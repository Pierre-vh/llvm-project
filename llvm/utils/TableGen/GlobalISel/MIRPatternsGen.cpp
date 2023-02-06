//===- MIRPatternsGen.cpp -------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// @file TODO
//
//===----------------------------------------------------------------------===//

#include "MIRPatternsGen.h"
#include "../CodeGenInstruction.h"
#include "MIRPatterns.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"

using namespace llvm;

//===----------------------------------------------------------------------===//
// MIRPatternGICombinerGen
//
// C++ CodeGen for a Combine rule consisting of an apply/match MIR pattern pair
// goes as follows:
// - The "MatchData" type is always the same, and it simply consists of a vector
//   of `MachineInstr*`
// - Match code will check instructions then push them into the MatchData
// vector.
//    - The Match code returns true on complete match and false on failure.
//      It should be generated inside its own function or a one-use lambda.
//    - Match code is very stupid; it's a chain of if statements. Merging this
//    with MatchDag would have tons of benefits to improve code quality.
// - Apply code will fetch instructions from that vector as needed.
//===----------------------------------------------------------------------===//

void MIRPatternGICombinerGen::emitMatchInfoDecl(raw_ostream &OS,
                                                unsigned Indent) {
  // TODO: We could probably reuse the MIs vector if we integrate more with
  // MatchDag?
  OS.indent(Indent) << "std::vector<MachineInstr*> " << MatchInfoName << ";\n";
  OS.indent(Indent) << "(void)" << MatchInfoName << ";\n";
}

void MIRPatternGICombinerGen::emitIncludeDeps(raw_ostream &OS) {
  OS << "#include \"llvm/CodeGen/GlobalISel/Utils.h\"\n";
}

void MIRPatternGICombinerGen::emitInstMatchCode(raw_ostream &OS,
                                                const Instruction &I,
                                                StringRef IVarName,
                                                unsigned Indent) {
  if (I.isCommutable())
    PrintWarning(I.getLoc(),
                 "isCommutable is not supported in MIR Pattern Matching yet");

  // Check opcode first.
  OS.indent(Indent) << "if(";
  for (const auto &[Idx, Opc] : enumerate(I.opcodes())) {
    if (Idx != 0)
      OS << " && ";
    OS << IVarName << "->getOpcode() != " << OpcNamespace
       << "::" << Opc->TheDef->getName();
  }
  OS << ")\n";
  OS.indent(Indent + 2) << "return false;\n";

  // Check number of operands
  OS.indent(Indent) << "if(" << IVarName
                    << "->getNumOperands() != " << I.operands_size() << " || "
                    << IVarName << "->getNumDefs() != " << I.getNumDefs()
                    << ")\n";
  OS.indent(Indent + 2) << "return false;\n";

  // Check MIRPattern operands.
  const unsigned FirstOpIdx = I.getNumDefs();
  for (const auto &[Idx, InOp] : enumerate(I.uses())) {
    // FIXME: Handle commutable instructions!

    if (InOp.isWildcard())
      continue;

    const auto OpTmp = createTmpVarName();
    OS.indent(Indent) << "MachineOperand &" << OpTmp << " = " << IVarName
                      << "->getOperand(" << (FirstOpIdx + Idx) << ");\n";
    // TODO
    if (InOp.isFloat()) {
      llvm_unreachable("TODO: Match Float Imms");
    }

    // TODO: doesn't handle CImm
    if (InOp.isInt()) {
      OS.indent(Indent) << "if(!" << OpTmp << ".isImm() || " << OpTmp
                        << ".getImm() != " << InOp.getInt() << ")\n";
      OS.indent(Indent + 2) << "return false;\n";
      continue;
    }

    // Register: recursively check other insts if needed.
    if (InOp.isRegister()) {
      // TODO: IMPORTANT: Check register equality if Reg has been used earlier.

      OS.indent(Indent) << "if(!" << OpTmp << ".isReg())\n";
      OS.indent(Indent + 2) << "return false;\n";
      if (Instruction *RegDef = MatchPat.getDef(InOp.getRegister())) {
        OS.indent(Indent) << "else {\n";
        const auto OpTmpInst = OpTmp + "Inst";
        if (RegDef->hasCopy()) {
          OS.indent(Indent + 2)
              << "MachineInstr *" << OpTmpInst << " = " << MRIVarName
              << ".getVRegDef(" << OpTmp << ".getReg());\n";
        } else {
          OS.indent(Indent + 2)
              << "MachineInstr *" << OpTmpInst << " = getDefIgnoringCopies("
              << OpTmp << ".getReg(), " << MRIVarName << ");\n";
        }
        emitInstMatchCode(OS, *RegDef, OpTmpInst, Indent + 2);
        OS.indent(Indent) << "}\n";
      }
    }
  }

  // Instruction matches if the emitted code reaches here, so record it.
  OS.indent(Indent) << MatchInfoName << ".push_back(" << IVarName << ");\n";
  recordMatchInfoPush(&I);
}

std::string MIRPatternGICombinerGen::getAccessMatchInfoDef(const Instruction *I,
                                                           Register Reg) const {
  assert(MatchInfoIdx.count(I) != 0 && "Inst not seen!");

  unsigned DefIdx = -1;
  for (const auto &[Idx, R] : enumerate(I->defs())) {
    if (R.getRegister() == Reg) {
      DefIdx = Idx;
      break;
    }
  }

  assert(DefIdx != (unsigned)-1);
  const unsigned Idx = MatchInfoIdx.lookup(I);
  return std::string(MatchInfoName) + "[" + std::to_string(Idx) +
         "]->getOperand(" + std::to_string(DefIdx) + ").getReg()";
}

std::string
MIRPatternGICombinerGen::getAccessMatchPatLiveIn(Register Reg) const {
  // Iterate over instructions use operands until we find one that has the
  // register we want.
  for (Instruction &I : MatchPat.insts()) {
    for (const auto &[Idx, Op] : enumerate(I.operands())) {
      if (!Op.isDef() && Op.isRegister() && Op.getRegister() == Reg) {
        assert(MatchInfoIdx.count(&I) != 0 && "Inst not seen!");
        const unsigned Idx = MatchInfoIdx.lookup(&I);
        return std::string(MatchInfoName) + "[" + std::to_string(Idx) +
               "]->getOperand(" + std::to_string(Idx) + ").getReg()";
      }
    }
  }

  llvm_unreachable(
      "Couldn't find any use of the live-in in the match pattern?!");
}

static void emitLLTDecl(raw_ostream &OS, LLT Type) {
  // TODO: handle other types
  if (Type.isScalar()) {
    OS << "LLT::scalar(" << Type.getSizeInBits() << ")";
    return;
  }

  llvm_unreachable("Unhandled LLT");
}

// FIXME: duplicate from MIRPatterns.cpp
static std::string toString(LLT Ty) {
  std::string Str;
  raw_string_ostream OS(Str);
  OS << Ty;
  return Str;
}

void MIRPatternGICombinerGen::emitInstApplyCode(
    raw_ostream &OS, const Instruction &I, unsigned Indent,
    StringMap<std::string> &RegVarNames,
    DenseSet<Instruction *> &InstsToDelete) {
  // FIXME: We use fatal errors a lot. We should just use normal errors so we
  // can emit as many of them as possible before giving up.
  assert(I.opcodes_size() == 1);

  SmallVector<std::string, 4> BuilderCalls;

  const auto checkInOutRegTypes = [&](Register Reg) {
    const auto &MatchTy = MatchPat.getType(Reg);
    const auto &ApplyTy = ApplyPat.getType(Reg);
    if (MatchTy && ApplyTy && *MatchTy != *ApplyTy)
      PrintFatalError(ApplyPat.getLoc(),
                      Reg.Name + " has a different type in match(" +
                          ::toString(*MatchTy) + ") and apply(" +
                          ::toString(*ApplyTy) + ") patterns");
  };

  const auto OpcName = I.getSingleOpcode().TheDef->getName();

  for (auto &Def : I.defs()) {
    Register Reg = Def.getRegister();
    assert(RegVarNames[Reg.Name].empty() && "Multiple defs seen?!");

    // Check if was seen before in the match pattern.
    if (MatchPat.usesRegister(Reg)) {
      // Check if the type is consistent if both registers are typed.
      checkInOutRegTypes(Reg);

      if (MatchPat.isLiveIn(Reg)) {
        PrintFatalError(I.getLoc(),
                        "cannot define " + Reg.Name +
                            " which is a live-in of the match pattern");
        // TODO: remark 'match pattern is here'
      }

      Instruction *MatchDef = MatchPat.getDef(Reg);
      assert(MatchDef);

      const auto VarName = getAccessMatchInfoDef(MatchDef, Reg);
      RegVarNames[Reg.Name] = VarName;
      BuilderCalls.push_back("addDef(" + VarName + ")");
      InstsToDelete.insert(MatchDef);
    } else {
      // Register has not been seen in the match pattern, we need to create it.
      const auto &RegTy = ApplyPat.getType(Reg);
      if (!RegTy)
        PrintFatalError(I.getLoc(), "newly defined output register " +
                                        Reg.Name + " must have a fixed type");

      const auto TmpName = createTmpVarName();
      OS.indent(Indent) << "Register " << TmpName << " = " << MRIVarName
                        << ".createGenericVirtualRegister(";
      emitLLTDecl(OS, *RegTy);
      OS << ");\n";

      RegVarNames[Reg.Name] = TmpName;
      BuilderCalls.push_back("addDef(" + TmpName + ")");
    }
  }

  for (const auto &Op : I.uses()) {
    assert(!Op.isWildcard());

    if (Op.isFloat()) {
      llvm_unreachable("TODO: Create Float Imms");
    }

    if (Op.isInt()) {
      // FIXME: Doesn't handle CImm?
      BuilderCalls.push_back("addImm(" +
                             std::to_string(Op.getInt().getZExtValue()) + ")");
      continue;
    }

    assert(Op.isRegister());
    Register OpReg = Op.getRegister();

    std::string RegVarName;
    if (auto It = RegVarNames.find(OpReg.Name); It != RegVarNames.end())
      RegVarName = It->second;
    else {
      assert(ApplyPat.isLiveIn(OpReg));

      // This register must be in the match pattern.
      if (!MatchPat.usesRegister(OpReg)) {
        PrintFatalError(I.getLoc(), "cannot use " + OpReg.Name +
                                        " as an operand unless it has been "
                                        "defined in the match pattern");
      }

      checkInOutRegTypes(OpReg);

      if (Instruction *MatchDef = MatchPat.getDef(OpReg)) {
        // Defined by the match pattern
        RegVarName = getAccessMatchInfoDef(MatchDef, OpReg);
        RegVarNames[OpReg.Name] = RegVarName;
      } else {
        // Live-in of the match pattern (aka a matched instruction's operands)
        RegVarName = getAccessMatchPatLiveIn(OpReg);
        RegVarNames[OpReg.Name] = RegVarName;
      }
    }

    assert(!RegVarName.empty());
    BuilderCalls.push_back("addReg(" + RegVarName + ")");
  }

  const auto NewInstrName = createTmpVarName();

  // FIXME: Find a better way to deal with these. It's quite ugly and also
  // wasteful do collect BuilderCalls just to not use them.
  if (OpcName == "G_CONSTANT") {
    if (I.getNumUses() != 1 || !I.getOperand(1).isInt())
      PrintFatalError(
          I.getLoc(),
          "G_CONSTANT must haves a single integer immediate operand");

    assert(I.getNumDefs() == 1);
    uint64_t Val = I.getOperand(1).getInt().getZExtValue();
    Register CstReg = I.getOperand(0).getRegister();
    const auto RegVarName = RegVarNames[CstReg.Name];
    assert(!RegVarName.empty());
    OS.indent(Indent) << "MachineInstr *" << NewInstrName << " = "
                    << BuilderVarName << ".buildConstant(" << RegVarName << ", " << Val << ");\n";
  } else {
    OS.indent(Indent) << "MachineInstr *" << NewInstrName << " = "
                    << BuilderVarName << ".buildInstr(" << OpcNamespace
                    << "::" << I.getSingleOpcode().TheDef->getName() << ")";
    for (const auto &Call : BuilderCalls) {
      OS << "\n";
      OS.indent(Indent + 2) << "." << Call;
    }
    OS << ";\n";
  }

  OS.indent(Indent) << "(void)" << NewInstrName << ";\n";
}

void MIRPatternGICombinerGen::emitMatchCode(raw_ostream &OS,
                                            StringRef RootMIVarName,
                                            unsigned Indent) {
  emitInstMatchCode(OS, *MatchPat.getRoot(), RootMIVarName, Indent);
  OS.indent(Indent) << "return true;\n";
}

void MIRPatternGICombinerGen::emitApplyCode(raw_ostream &OS, unsigned Indent) {
  // "Apply" patterns are emitted in reverse order, instead of starting at the
  // root we start at the leaves.
  StringMap<std::string> RegVarNames;
  DenseSet<Instruction *> InstsToDelete;
  OS.indent(Indent) << BuilderVarName << ".setInstrAndDebugLoc(*"
                    << MatchInfoName << "["
                    << getMatchInfoIdx(MatchPat.getRoot()) << "]);\n";
  for (Instruction &I : ApplyPat.insts())
    emitInstApplyCode(OS, I, Indent, RegVarNames, InstsToDelete);

  for (Instruction *I : InstsToDelete)
    OS.indent(Indent) << MatchInfoName << "[" << getMatchInfoIdx(I)
                      << "]->eraseFromParent();\n";
  OS.indent(Indent) << MatchInfoName << ".clear();";
}

//===----------------------------------------------------------------------===//
