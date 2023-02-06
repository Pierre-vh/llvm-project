//===- MIRPatterns.cpp ----------------------------------------------------===//
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

#include "MIRPatterns.h"
#include "../CodeGenInstruction.h"
#include "../CodeGenTarget.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/LowLevelTypeImpl.h"
#include "llvm/Support/SMLoc.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"

using namespace llvm;

using Register = MIRPattern::Register;
using Instruction = MIRPattern::Instruction;
using Operand = MIRPattern::Operand;

namespace {

std::string toString(LLT Ty) {
  std::string Str;
  raw_string_ostream OS(Str);
  OS << Ty;
  return Str;
}

enum class VariadicKind {
  None,         ///< Not a Variadic Instruction.
  VariadicIns,  ///< Variadic Ins
  VariadicOuts, ///< Variadic Outs
};

/// Condensate of a GenericInstruction's semantics that are
/// relevant to an Instruction pattern.
///
/// FIXME: This + typecheckInst need a good rewrite. This is currently very
/// messy.
struct InstructionSemantics {
  InstructionSemantics(const CodeGenInstruction &CGI);

  /// Instruction name. This isn't part of its semantics and is
  /// just here so we can emit pretty errors.
  StringRef Name;

  std::vector<std::string> InTypes;
  std::vector<std::string> OutTypes;
  bool IsCommutable = false;
  VariadicKind VK = VariadicKind::None;

  bool ApplyTo(Instruction &I, MIRPattern &Pat) {
    // Set flags
    I.setIsCommutable(IsCommutable);

    // Map of operand type name (e.g. OPERAND_GENERIC_0) to registers that
    // belong to that group.
    StringMap<SmallVector<Register, 4>> TypeToEqRegs;

    for (const auto &[Idx, Def] : enumerate(I.defs())) {
      if (Idx < OutTypes.size())
        TypeToEqRegs[OutTypes[Idx]].push_back(Def.getRegister());
      else {
        assert(VK == VariadicKind::VariadicOuts);
        TypeToEqRegs[OutTypes.back()].push_back(Def.getRegister());
      }
    }

    for (const auto &[Idx, Op] : enumerate(I.uses())) {
      if (Op.isRegister()) {
        if (Idx < InTypes.size())
          TypeToEqRegs[InTypes[Idx]].push_back(Op.getRegister());
        else {
          assert(VK == VariadicKind::VariadicIns);
          TypeToEqRegs[InTypes.back()].push_back(Op.getRegister());
        }
      }
    }

    // Now that we know which registers must be equal, check if that's doable
    // given the register types.
    for (const auto &[GroupName, Regs] : TypeToEqRegs) {

      // Check if any of the Regs have a type. If a reg is typed, we
      // can infer that all other registers have the same type.
      std::optional<LLT> PreciseType;
      for (Register R : Regs) {
        const auto &RegType = Pat.getType(R);
        if (!RegType)
          continue;

        if (!PreciseType) {
          PreciseType = *RegType;
          continue;
        }

        if (*PreciseType != *RegType) {
          // TODO: Can we emit a better error here?
          PrintError(I.getLoc(), R.Name + " should have type " +
                                     toString(*PreciseType) + ", not " +
                                     toString(*RegType));
          return false;
        }
      }

      if (!PreciseType)
        continue;

      for (Register R : Regs) {
        // The loop earlier should have caught type mismatches.
        if (!Pat.setType(R, *PreciseType))
          llvm_unreachable("Uncaught type issue!");
      }
    }

    return true;
  }
};

InstructionSemantics::InstructionSemantics(const CodeGenInstruction &CGI) {
  Name = CGI.TheDef->getName();

  auto &Ops = CGI.Operands;
  unsigned NumDefs = Ops.NumDefs;

  for (const auto &[Idx, Op] : enumerate(Ops)) {
    if (Idx < NumDefs)
      OutTypes.push_back(Op.OperandType);
    else
      InTypes.push_back(Op.OperandType);
  }

  IsCommutable = CGI.isCommutable;
  if (Ops.isVariadic)
    VK = Ops.hasVariadicOuts ? VariadicKind::VariadicOuts
                             : VariadicKind::VariadicIns;
}

/// Checks that @p I is well-formed according to its Opcodes.
/// That is, all opcodes play nice together and there is the right amount of
/// defs/operands.
bool typecheckInst(Instruction &I, MIRPattern &Pat) {
  std::vector<InstructionSemantics> ISemantics;
  DenseSet<StringRef> NamesSeen;

  const auto fail = [&](Twine Msg) {
    PrintError(I.getLoc(), "invalid pattern: " + Msg);
    return false;
  };

  // First, check all opcodes individually: Check that the Instruction pattern
  // can satisfy it.
  for (CodeGenInstruction *CGI : I.opcodes()) {
    auto &ISema = ISemantics.emplace_back(*CGI);

    if (NamesSeen.contains(ISema.Name))
      return fail("multiple occurences of " + ISema.Name);
    NamesSeen.insert(ISema.Name);

    unsigned NumIns = ISema.InTypes.size();
    if (I.getNumUses() != NumIns) {
      // Check if this has variadic "ins" and if it does, ensure we have more
      // than the minimum amount of "ins".
      if (ISema.VK != VariadicKind::VariadicIns)
        return fail(ISema.Name + " has exactly " + Twine(NumIns) +
                    " in-operands but got " + Twine(I.getNumUses()));
      if (I.getNumUses() < NumIns)
        return fail(ISema.Name + " needs at least " + Twine(NumIns) +
                    " in-operands but got " + Twine(I.getNumUses()));
    }

    unsigned NumOuts = ISema.OutTypes.size();
    if (I.getNumDefs() != NumOuts) {
      if (ISema.VK != VariadicKind::VariadicOuts)
        return fail(ISema.Name + " has exactly " + Twine(NumOuts) +
                    " defs but got " + Twine(I.getNumDefs()));
      if (I.getNumDefs() < NumOuts)
        return fail(ISema.Name + " needs at least " + Twine(NumOuts) +
                    " defs but got " + Twine(I.getNumDefs()));
    }

    // TODO: Check that the operands are indeed imms?
  }

  auto &MainSema = ISemantics.front();

  if (I.opcodes_size() == 1)
    return MainSema.ApplyTo(I, Pat);

  // Multi-opcode instructions: Check compatibility between opcodes.
  // We take the first opcode as the main one and compare the other opcodes
  // against it.
  for (auto &OtherSema : drop_begin(ISemantics)) {
    if (MainSema.IsCommutable != OtherSema.IsCommutable)
      return fail(MainSema.Name + " and " + OtherSema.Name +
                  " have different values for 'isCommutable'");

    // FIXME: This could supported I think, but the question is 'Is it needed'?
    // How often would we want to have things like, say, "= (G_ADD |
    // G_BUILD_VECTOR)"?
    if (MainSema.VK != OtherSema.VK)
      return fail(MainSema.Name + " and " + OtherSema.Name +
                  " has different 'variadic' properties");

    // FIXME: Needs more thought if the above changes.
    if (MainSema.InTypes.size() != OtherSema.InTypes.size() ||
        MainSema.OutTypes.size() != OtherSema.OutTypes.size())
      return fail(MainSema.Name + " and " + OtherSema.Name +
                  " have incompatible number of in/out operands");

    // FIXME: Fragile, should they be "canonicalized" somehow? Also what if all
    // types are the same? Then the InTypes/OutTypes can be different and it
    // doesn't matter.
    // Note that if we become "looser" here we need to merge constraints better
    if (MainSema.InTypes != OtherSema.InTypes ||
        MainSema.OutTypes != OtherSema.OutTypes) {
      return fail(
          MainSema.Name + " and " + OtherSema.Name +
          " have incompatible type constraints on their in/out operands");
    }
  }

  // FIXME: If we want to do inference, we probably need to merge the semantics
  // somehow.
  return MainSema.ApplyTo(I, Pat);
}

bool isInteger(StringRef Str) {
  if (Str[0] == '+' || Str[0] == '-')
    Str = Str.drop_front();
  return !Str.empty() && all_of(Str, isdigit);
}

bool isFloatingPoint(StringRef Str) {
  if (Str[0] == '+' || Str[0] == '-')
    Str = Str.drop_front();
  // Only allow basic numbers like 0.0, 3.14, etc so far.
  // No scientific notation, or shorthands like ".3".
  auto [LHS, RHS] = Str.split('.');
  return isInteger(LHS) && isInteger(RHS);
}

bool isIntegerTypeName(StringRef Str, unsigned &Width) {
  if (Str.size() <= 1 || !Str.consume_front("i"))
    return false;
  if (!isInteger(Str))
    return false;
  Width = APInt(64, Str, 10).getZExtValue();
  return true;
}

bool isFloatingPointTypeName(StringRef Str, APFloat::Semantics &Semantics) {
  if (Str == "f32") {
    Semantics = APFloat::S_IEEEsingle;
    return true;
  }

  if (Str == "f64") {
    Semantics = APFloat::S_IEEEdouble;
    return true;
  }

  return false;
}

bool isIdentifier(StringRef Str) {
  // Identifiers are made up of a-z, A-Z, 0-9 and _ characters.
  // First character cannot be a digit.
  // _ alone is not an identifier, but it can be used in, e.g. _a.
  if (Str.empty() || Str == "_")
    return false;

  for (auto I = Str.begin(); I != Str.end(); ++I) {
    if (isalpha(*I) || *I == '_')
      continue;

    if (isdigit(*I)) {
      if (I == Str.begin())
        return false;
      continue;
    }

    return false;
  }

  return true;
}

} // namespace

class MIRPattern::InstructionParser {
  const StringRef Src;
  StringRef::iterator It;

  StringRef Tok;

  bool HadError = false;
  RecordKeeper &RK;
  const CodeGenTarget &CGT;
  MIRPattern &Pat;

  SMLoc getTokLoc() const {
    if (Tok.empty())
      return SMLoc();
    return SMLoc::getFromPointer(Tok.begin());
  }

public:
  InstructionParser(RecordKeeper &RK, const CodeGenTarget &CGT, MIRPattern &Pat,
                    StringRef Src)
      : Src(Src), It(Src.begin()), RK(RK), CGT(CGT), Pat(Pat) {
    assert(SrcMgr.FindBufferContainingLoc(SMLoc::getFromPointer(It)) &&
           "Cannot create SMLocs from StringRef Iterators!");
    // Get the first token ready to go.
    consumeToken();
  }

  std::unique_ptr<Instruction> parseInstruction();
  std::optional<Register> parseRegister(Instruction *DefInst);
  std::optional<Operand> parseOperand();
  std::optional<LLT> parseLLT();
  CodeGenInstruction *parseOpcode();

  // Implements a very trivial lexer. It just splits the input up into
  // identifiers and known separators. For simplicity, Tokens are not even
  // tagged. Tok will be empty if no token could be parsed due to reaching EOF,
  // or encountering an error.
  void consumeToken();

  bool tryConsumeToken(StringRef Str) {
    if (Tok == Str) {
      consumeToken();
      return true;
    }

    return false;
  }

  bool hadError() const { return HadError; }
  bool isEOF() const { return Tok.empty() && It == Src.end(); }

  void PrintParsingError(Twine Msg) {
    // Don't report errors coming from empty tokens. They act as "invalid"
    // tokens.
    if (Tok.empty())
      return;
    PrintParsingError(Tok.begin(), Msg);
  }

  void PrintParsingError(StringRef::iterator Loc, Twine Msg) {
    // FIXME: Errors are currently reported as-if the pattern was its own file.
    //
    // This makes for terrible UX because this can't be parsed like other
    // diagnostics so the IDE can put squiggles on the error location.
    // For now this is the best we can do simply because StringInit doesn't
    // keep track of the original StringRef extracted from the SourceMgr's
    // buffer. It doesn't even keep track of the SMLoc where the String begins.
    //
    // If it did, we could just increment that SMLoc by distance(begin, loc) to
    // get the actual location of the error within the buffer owned the SrcMgr
    // in by TableGen/Error.h.
    //
    // Though this may not be doable if we do "instantiations" of StringInits.
    // e.g. if we clone a StringInt multiple times for a for loop & substitute
    // text each time for instance.
    HadError = true;
    PrintError(Loc, Msg);
  }
};

void MIRPattern::InstructionParser::consumeToken() {
  StringRef::iterator TokBegin = It;
  Tok = "";

  // Makes a token from [TokBegin, It).
  const auto makeToken = [&]() {
    const unsigned TokLen = std::distance(TokBegin, It);
    assert(TokLen != 0 && "Empty Token!");
    Tok = StringRef(TokBegin, TokLen);

    // Skip trailing spaces.
    while (isspace(*It) && It != Src.end())
      ++It;
  };

  for (; It != Src.end(); ++It) {
    switch (*It) {
    case '(':
    case ')':
    case '|':
    case ',':
    case '=':
    case ':':
      // If the current Token is empty, then the separator itself is a token.
      if (It == TokBegin) {
        ++It;
        return makeToken();
      }

      return makeToken();
    case '.':
      // . only makes sense if it's preceded by a digit.
      if (It == TokBegin || !isdigit(*(It - 1))) {
        PrintError(It, "unexpected '.' character");
        Tok = "";
        return;
      }
      continue;
    case '%':
    case '+':
    case '-':
      // %, + and - only makes sense as the first character of a Token.
      if (It != TokBegin) {
        PrintError(It, "unexpected '" + Twine(*It) + "' character");
        Tok = "";
        return;
      }
      continue;
    default:
      // Spaces are separators, but can't form Tokens of their own so
      // skip leading spaces.
      if (isspace(*It)) {
        if (It == TokBegin) {
          ++TokBegin;
          continue;
        }

        return makeToken();
      }

      // we only understand alphanumeric characters and '_' from here.
      if (!isalnum(*It) && *It != '_') {
        PrintError(It, "unexpected '" + Twine(*It) + "' character");
        Tok = "";
        return;
      }

      continue;
    }
  }

  // Reached EOF, make a token if needed.
  if (It != TokBegin)
    makeToken();
}

CodeGenInstruction *MIRPattern::InstructionParser::parseOpcode() {
  Record *R = RK.getDef(Tok);
  if (!R) {
    PrintParsingError("Cannot find a definition for '" + Tok + "'");
    return nullptr;
  }

  if (!R->isSubClassOf("GenericInstruction")) {
    PrintParsingError("'" + Tok + "' is not a GenericInstruction");
    return nullptr;
  }

  consumeToken();
  return &CGT.getInstruction(R);
}

std::optional<LLT> MIRPattern::InstructionParser::parseLLT() {
  // TODO: Support point types, but that requires more information about the
  // target's address spaces.
  // TODO: Support vectors.

  if (!Tok.starts_with("s")) {
    PrintParsingError("expected a type");
    return std::nullopt;
  }

  // Looking for a scalar type. Eat all digits.
  StringRef Val = Tok.drop_front(1);
  if (!isInteger(Val)) {
    PrintParsingError(Val.begin(), "expected a number after 's'");
    return std::nullopt;
  }

  consumeToken();
  return LLT::scalar(APSInt(Val).getZExtValue());
}

std::optional<Register>
MIRPattern::InstructionParser::parseRegister(Instruction *DefInst) {
  assert(Tok.starts_with("%"));

  const SMLoc TokLoc = getTokLoc();
  const StringRef RegName = Tok;
  // Identifier or integral number must follow the '%'
  if (!isIdentifier(RegName.drop_front()) && !isInteger(RegName.drop_front())) {
    PrintParsingError(RegName.begin(),
                      "'" + RegName + "' is not a valid register name");
    return std::nullopt;
  }

  consumeToken();

  // Parse optional ':'
  std::optional<LLT> RegType;
  if (tryConsumeToken(":")) {

    // '(' LLT ')'
    if (!tryConsumeToken("(")) {
      PrintParsingError("expected '('");
      return std::nullopt;
    }

    RegType = parseLLT();

    if (!tryConsumeToken(")")) {
      PrintParsingError("expected ')'");
      return std::nullopt;
    }
  }

  // If DefInst is provided, this is being parsed for a definition.
  // Else, it's parsed for a use.
  return DefInst ? Pat.recordRegisterDef(TokLoc, *DefInst, RegName, RegType)
                 : Pat.recordRegisterUse(TokLoc, RegName, RegType);
}

std::optional<Operand> MIRPattern::InstructionParser::parseOperand() {
  // Assume the error was reported while tokenizing;
  if (Tok.empty())
    return std::nullopt;

  SMLoc TokLoc = getTokLoc();

  // wilcard
  if (Tok == "_") {
    consumeToken();
    return Operand::getWildcard(TokLoc);
  }

  // register
  if (Tok.starts_with("%")) {
    std::optional<Register> Reg = parseRegister(nullptr);
    if (!Reg)
      return std::nullopt;
    return Operand(TokLoc, *Reg, /*Def*/ false);
  }

  // int immediates
  unsigned IntWidth = 0;
  if (isIntegerTypeName(Tok, IntWidth)) {
    consumeToken();
    if (!isInteger(Tok)) {
      PrintParsingError("expected an integer immediate");
      return std::nullopt;
    }
    Operand Result(TokLoc, APInt(IntWidth, Tok, 10));
    consumeToken();
    return Result;
  }

  // float immediates
  APFloat::Semantics FltSemEnum;
  if (isFloatingPointTypeName(Tok, FltSemEnum)) {
    consumeToken();
    if (!isFloatingPoint(Tok)) {
      PrintParsingError("expected a floating-point immediate");
      return std::nullopt;
    }
    auto &FltSem = APFloat::EnumToSemantics(FltSemEnum);
    auto Value = APFloat(FltSem);
    // FIXME: no idea what to use for this.
    auto ParseResult =
        Value.convertFromString(Tok, APFloat::rmNearestTiesToEven);
    if (auto Err = ParseResult.takeError()) {
      PrintParsingError("cannot parse floating-point immediate (" +
                        toString(std::move(Err)) + ")");
      return std::nullopt;
    }

    consumeToken();
    return Operand(TokLoc, std::move(Value));
  }

  PrintParsingError("expected an immediate, a register or '_'");
  return std::nullopt;
}

std::unique_ptr<Instruction> MIRPattern::InstructionParser::parseInstruction() {
  auto Inst = std::make_unique<Instruction>(getTokLoc());

  // (reg (',' reg)[0+])?
  do {
    if (!Tok.starts_with("%")) {
      if (!Inst->hasDefs())
        break;
      PrintParsingError("expected a register after ','");
      return nullptr;
    }

    SMLoc Loc = getTokLoc();
    std::optional<Register> Reg = parseRegister(Inst.get());
    if (!Reg)
      return nullptr;
    Inst->addOperand(Operand(Loc, *Reg, /*Def*/ true));
  } while (tryConsumeToken(","));

  // '=' is mandatory if we just parsed defs.
  if (Inst->hasDefs()) {
    if (!tryConsumeToken("=")) {
      PrintParsingError("expected '=' after register list");
      return nullptr;
    }
  }

  // opcode-list := '(' opcode ('|' opcode)[0+] ')'
  // opcode | opcode-list
  auto &Opcodes = Inst->Opcodes;
  if (tryConsumeToken("(")) {
    do {
      if (!isIdentifier(Tok)) {
        PrintParsingError("expected an opcode");
        return nullptr;
      }

      CodeGenInstruction *OpcInst = parseOpcode();
      if (!OpcInst)
        return nullptr;
      Opcodes.push_back(OpcInst);
    } while (tryConsumeToken("|"));

    if (!tryConsumeToken(")")) {
      PrintParsingError("expected ')' after opcodes list");
      return nullptr;
    }
  } else {
    if (!isIdentifier(Tok)) {
      PrintParsingError("expected an opcode");
      return nullptr;
    }

    CodeGenInstruction *OpcInst = parseOpcode();
    if (!OpcInst)
      return nullptr;
    Opcodes.push_back(OpcInst);
  }

  // Optional operand list.
  if (!isEOF()) {
    do {
      std::optional<Operand> Op = parseOperand();
      if (!Op)
        return nullptr;
      Inst->addOperand(std::move(*Op));
    } while (tryConsumeToken(","));
  }

  if (!isEOF()) {
    PrintParsingError("unexpected token at end of instruction");
    return nullptr;
  }

  return Inst;
}

MIRPattern::~MIRPattern() = default;

std::unique_ptr<MIRPattern> MIRPattern::parse(RecordKeeper &Records,
                                              const CodeGenTarget &CGT,
                                              StringRef Src, Kind K,
                                              Twine PatName, bool MakeCopy) {
  // Get the Src inside a SourceManager for error reporting.
  const unsigned BufID = SrcMgr.AddNewSourceBuffer(
      MakeCopy ? MemoryBuffer::getMemBufferCopy(Src, PatName.str())
               : MemoryBuffer::getMemBuffer(Src, PatName.str(), false),
      SMLoc());
  Src = SrcMgr.getBufferInfo(BufID).Buffer->getBuffer();

  SMLoc PatLoc = SMLoc::getFromPointer(Src.begin());
  auto Pat =
      std::unique_ptr<MIRPattern>(new MIRPattern(PatName.str(), K, PatLoc));

  /// MIR Patterns are just a list of instruction patterns. We can split using
  /// '\n' and parse each line as an instruction.
  bool HadError = false;
  while (!Src.empty()) {
    // Remove leading whitespace.
    Src = Src.ltrim();

    // Split at the next '\n'. If there is no '\n' remaining in the string
    // then Src will be empty and the parsing loop ends.
    StringRef CurrentLine;
    std::tie(CurrentLine, Src) = Src.split('\n');

    // Trim spaces at the end of the line.
    CurrentLine = CurrentLine.rtrim();
    if (CurrentLine.empty()) {
      continue;
    }

    // 'Cur' likely contains an instruction, parse it.
    InstructionParser IP(Records, CGT, *Pat, CurrentLine);
    auto Inst = IP.parseInstruction();
    if (!Inst || IP.hadError()) {
      HadError = true;
      continue;
    }
    Pat->addInst(std::move(Inst));
  }

  if (HadError)
    return nullptr;

  if (Pat->insts_empty()) {
    PrintError(PatLoc, "pattern is empty");
    return nullptr;
  }

  if (!Pat->typecheck() || !Pat->checkSemantics())
    return nullptr;

  assert(Pat->verify());
  return Pat;
}

MIRPattern::RegisterInfo &MIRPattern::getRegInfo(Register Reg) {
  if (auto It = RegInfos.find(Reg.Name); It != RegInfos.end())
    return It->second;

  report_fatal_error("Pattern does not know about this Register - Did you call "
                     "usesRegister first?");
}

bool MIRPattern::typecheck() {
  for (auto &I : PatInsts) {
    if (!typecheckInst(*I, *this))
      return false;
  }
  return true;
}

bool MIRPattern::checkSemantics() {
  bool Result = true;
  if (isApplyPattern()) {
    for (auto &I : PatInsts) {
      if (I->opcodes_size() != 1) {
        PrintError(I->getLoc(), "'apply' patterns must have a single opcode");
        Result = false;
      }

      for (auto &Op : I->operands()) {
        if (Op.isWildcard()) {
          PrintError(I->getLoc(),
                     "'apply' patterns may not use wildcard ('_') operands");
          Result = false;
        }
      }
    }
  }

  return Result;
}

bool MIRPattern::verifyReachabilityFromRoot() const {
  assert(PatRoot && "No Pattern Root Set!");
  DenseSet<const Instruction *> SeenInsts;
  visitRecursively(*PatRoot, [&](auto &I) {
    SeenInsts.insert(&I);
    return true;
  });

  if (SeenInsts.size() == PatInsts.size())
    return true;

  for (auto &I : PatInsts) {
    if (SeenInsts.contains(I.get()))
      continue;

    PrintError(I->getLoc(),
               "instruction is not reachable from the root of the pattern");
    PrintNote(PatRoot->getLoc(), "root of the pattern is here");
  }

  return false;
}

void MIRPattern::setRoot(Instruction *Inst) {
  assert(
      find_if(PatInsts, [&](auto &PatInst) { return PatInst.get() == Inst; }) !=
          PatInsts.end() &&
      "Inst does not belong to this pattern!");
  PatRoot = Inst;
}

bool MIRPattern::usesRegister(Register Reg) const {
  return RegInfos.count(Reg.Name) != 0;
}

bool MIRPattern::setType(Register Reg, LLT Ty) {
  auto &ExistingTy = getRegInfo(Reg).Type;
  if (!ExistingTy) {
    ExistingTy = Ty;
    return true;
  }

  return *ExistingTy == Ty;
}

bool MIRPattern::visitRecursively(
    const Instruction &I,
    const std::function<bool(const Instruction &I)> &Visitor) const {
  if (!Visitor(I))
    return false;

  for (auto &Op : I.uses()) {
    if (Op.isRegister()) {
      if (Instruction *Def = getDef(Op.getRegister())) {
        if (!visitRecursively(*Def, Visitor))
          return false;
      }
    }
  }

  return true;
}

bool MIRPattern::verify() const {
  for (const auto &[RegName, Info] : RegInfos) {
    if (Info.Def) {
      const bool HasDef =
          find_if(Info.Def->defs(), [RegName = RegName](auto &DefOp) {
            return DefOp.getRegister() == Register(RegName);
          }) != Info.Def->defs().end();

      if (!HasDef) {
        dbgs() << "MIRPattern Verification Error: Register -> Defs Map is "
                  "Inconsistent!";
        dbgs() << RegName << " is not actually defined by " << Info.Def << "\n";
        Info.Def->print(dbgs(), this);
        return false;
      }
    }
  }

  for (auto &I : PatInsts)
    if (!I->verify())
      return false;

  return true;
}

std::optional<Register> MIRPattern::recordRegisterDef(SMLoc At,
                                                      Instruction &Inst,
                                                      StringRef Name,
                                                      std::optional<LLT> Type) {
  const auto It = RegInfos.find(Name);
  if (It != RegInfos.end()) {
    RegisterInfo &RI = It->getValue();
    // Register already exists. If we thought it was a live-in before, it's a
    // use-before-def, else it's a redefinition.
    if (!RI.Def) {
      PrintError(RI.FirstSeenAt,
                 Name + " cannot be used before its definition");
      PrintNote(At, Name + " is defined here");
    } else {
      PrintError(At, "illegal redefinition of " + Name);
      PrintNote(RI.FirstSeenAt, Name + " is first defined here");
    }
    return std::nullopt;
  }

  // Register does not exist, create an entry for it.
  // Ensure we return a StringRef for the copy that StringMap allocated.
  return RegInfos.insert({Name, RegisterInfo(Type, &Inst, At)}).first->getKey();
}

std::optional<Register> MIRPattern::recordRegisterUse(SMLoc At, StringRef Name,
                                                      std::optional<LLT> Type) {
  const auto It = RegInfos.find(Name);
  if (It == RegInfos.end()) {
    // Register does not exist, record it as a live-in.
    // Ensure we return a StringRef for the copy that StringMap allocated.
    return RegInfos.insert({Name, RegisterInfo(Type, nullptr, At)})
        .first->getKey();
  }

  // Check the types are consistent, or if now know the type of this
  // register.
  if (!Type)
    return It->getKey();

  RegisterInfo &RI = It->getValue();
  if (!RI.Type) {
    // Untyped register, set its type.
    RI.Type = *Type;
  } else if (*RI.Type != *Type) {
    PrintError(At, "invalid type for " + Name + ": " + ::toString(*Type) +
                       " but register has type " + ::toString(*RI.Type));
    return std::nullopt;
  }

  return It->getKey();
}

void MIRPattern::print(raw_ostream &OS, unsigned Indent) const {
  OS.indent(Indent) << "MIRPattern(" << Name << "):\n";
  for (auto &[Index, I] : enumerate(PatInsts))
    I->print(OS, this, Indent + 1);
}

void MIRPattern::Register::print(raw_ostream &OS, const MIRPattern *Pat,
                                 bool DumpDefInst) const {
  OS << Name;
  if (!Pat || !Pat->usesRegister(*this)) {
    OS << "(?)";
    return;
  }

  OS << "(";
  if (DumpDefInst) {
    if (Instruction *Def = Pat->getDef(*this))
      OS << Def << " ";
    else
      OS << "live-in ";
  }
  if (auto Type = Pat->getType(*this))
    OS << ::toString(*Type);
  else
    OS << "untyped";
  OS << ")";
}

void MIRPattern::Operand::print(raw_ostream &OS, const MIRPattern *Pat,
                                bool PrintRegDef) const {
  if (isWildcard())
    OS << "<Wildcard>";
  else if (isRegister()) {
    if (isDef())
      OS << "def ";
    getRegister().print(OS, Pat, PrintRegDef);
  } else if (isFloat()) {
    SmallString<32> Str;
    getFloat().toString(Str);
    OS << "<fpimm: " << Str << ">";
  } else if (isInt())
    OS << "<intimm: " << getInt() << ">";
  else
    llvm_unreachable("Unknown Operand Kind!");
}

bool MIRPattern::Instruction::verify() const {
  if (NumDefs > Operands.size()) {
    dbgs() << "MIRPattern Instruction Verification Error: Instruction has "
           << NumDefs << " defs but only " << Operands.size() << " operands\n";
    print(dbgs(), nullptr);
    return false;
  }

  for (auto &Op : defs()) {
    if (!Op.isRegister()) {
      dbgs() << "MIRPattern Instruction Verification Error: Instruction has a "
                "def that is not a register\n";
      print(dbgs(), nullptr);
      return false;
    }

    if (!Op.isDef()) {
      dbgs() << "MIRPattern Instruction Verification Error: Def operand does "
                "not have 'isDef'\n";
      print(dbgs(), nullptr);
      return false;
    }
  }

  for (auto &Op : uses()) {
    if (Op.isDef()) {
      dbgs() << "MIRPattern Instruction Verification Error: Use operand has "
                "'isDef'\n";
      print(dbgs(), nullptr);
      return false;
    }
  }

  return true;
}

void MIRPattern::Instruction::addOperand(Operand Op) {
  assert((!Op.isDef() || (NumDefs == Operands.size())) &&
         "Adding a def after a use operand!");
  Operands.emplace_back(std::move(Op));
  if (Op.isDef())
    ++NumDefs;
}

bool MIRPattern::Instruction::hasCopy() const {
  return any_of(Opcodes, [&](CodeGenInstruction *CGI) {
    return CGI->TheDef->getName() == "COPY";
  });
}

void MIRPattern::Instruction::print(raw_ostream &OS, const MIRPattern *Pat,
                                    unsigned Indent) const {
  OS.indent(Indent) << "Instruction(" << this << "):\n";

  if (Commutable)
    OS.indent(Indent + 1) << "flags:  \tcommutable\n";

  OS.indent(Indent + 1) << "opcodes:\t";
  for (auto &[Index, Opc] : enumerate(Opcodes)) {
    if (Index != 0)
      OS << ", ";
    OS << Opc->TheDef->getName();
  }
  OS << "\n";

  OS.indent(Indent + 1) << "operands:\t";
  if (operands_size() != 0) {
    for (auto &[Index, Op] : enumerate(operands())) {
      if (Index != 0)
        OS << ", ";
      Op.print(OS, Pat, /* DumpDefInst */ !Op.isDef());
    }
    OS << "\n";
  } else
    OS << "<empty>\n";
}
