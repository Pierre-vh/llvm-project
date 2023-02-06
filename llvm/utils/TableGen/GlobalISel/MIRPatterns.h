//===- MIRPatterns.h ------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_UTILS_TABLEGEN_MIRPATTERNS_H
#define LLVM_UTILS_TABLEGEN_MIRPATTERNS_H

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/LowLevelTypeImpl.h"
#include "llvm/Support/SMLoc.h"
#include <functional>
#include <variant>

namespace llvm {
class RecordKeeper;
class Record;
class StringInit;
class CodeGenTarget;
class CodeGenInstruction;

/// Represents a full gMIR pattern, which is made up of a list
/// of Instructions.
class MIRPattern {
  class InstructionParser;

public:
  class Operand;
  class Instruction;

  /// Represents a register in this Pattern.
  /// This is simply a thin wrapper around a StringRef which contains the name
  /// of the register. '%' is part of the name.
  ///
  /// Representing registers by name only is a choice to make things simpler
  /// w.r.t. the handling of patterns. When we just use a name, we can easily do
  /// cross-pattern queries; for instance if an "out" pattern wants to check if
  /// an "in" pattern knows about a given register, it can just ask without any
  /// complicated translation/lookups.
  struct Register {
    StringRef Name;

    Register() = default;
    Register(StringRef Name) : Name(Name) {}

    /// Pretty-print the register & the data @p Pat has about it.
    void print(raw_ostream &OS, const MIRPattern *Pat = nullptr,
               bool DumpDefInst = true) const;

    explicit operator bool() const { return !Name.empty(); }
    bool operator==(Register Other) const { return Name == Other.Name; }
  };

  using inst_iterator_range = iterator_range<pointee_iterator<
      typename std::vector<std::unique_ptr<Instruction>>::iterator>>;
  using const_inst_iterator_range = iterator_range<pointee_iterator<
      typename std::vector<std::unique_ptr<Instruction>>::const_iterator>>;

  /// Kind of patterns.
  enum class Kind {
    /// This pattern is used to match a piece of code. It may have multiple
    /// opcodes in one instructions and use wildcard operands.
    Match,
    /// This pattern is used to generate MIR code. It may not use wildcard
    /// operands and can only have one opcode per instruction.
    Apply,
  };

  ~MIRPattern();

  /// Parses a MIR Pattern from a source string.
  /// If @p MakeCopy is true, a copy of @p Src will be created in TableGen's
  /// SourceMgr. Else, only a reference to @p Src will be
  /// added to TableGen's SourceMgr.
  ///
  /// If @p Src can be deallocated before the end of the program, creating a
  /// Copy is prefferable to avoid dangling pointers in the SourceMgr.
  static std::unique_ptr<MIRPattern>
  parse(RecordKeeper &Records, const CodeGenTarget &CGT, StringRef Src, Kind K,
        Twine PatName = "MIRPattern", bool MakeCopy = false);

  /// Checks that all instructions in this pattern are reachable from
  /// its root instruction. A root must have been set earlier.
  bool verifyReachabilityFromRoot() const;

  bool isMatchPattern() const { return K == Kind::Match; }
  bool isApplyPattern() const { return K == Kind::Apply; }

  void setRoot(Instruction *Inst);
  Instruction *getRoot() { return PatRoot; }
  const Instruction *getRoot() const { return PatRoot; }

  Instruction *insts_back() { return PatInsts.back().get(); }
  const Instruction *insts_back() const { return PatInsts.back().get(); }

  inst_iterator_range insts() { return PatInsts; }
  const_inst_iterator_range insts() const { return PatInsts; }
  bool insts_empty() const { return PatInsts.empty(); }

  SMLoc getLoc() const { return Loc; }

  Instruction *getDef(Register Reg) const { return getRegInfo(Reg).Def; }
  bool isLiveIn(Register Reg) const { return getDef(Reg) == nullptr; }
  std::optional<LLT> getType(Register Reg) const { return getRegInfo(Reg).Type; }
  bool usesRegister(Register Reg) const;

  /// Attempts to set the type of @p Reg to @p Ty. If @p Reg already has a type
  /// != @p Ty, returns false.
  bool setType(Register Reg, LLT Ty);

  /// Calls @p Visitor on an instruction then recursively looks at its operands
  /// for registers, and visits their definitions too. Stops when @p Visitor
  /// returns false. Returns false if @p Visitor returned false once.
  bool visitRecursively(
      const Instruction &I,
      const std::function<bool(const Instruction &I)> &Visitor) const;

  bool verify() const;
  void print(raw_ostream &OS, unsigned Indent = 0) const;

private:
  struct RegisterInfo {
    RegisterInfo() = default;
    RegisterInfo(std::optional<LLT> Type, Instruction *Def, SMLoc FirstSeenAt)
        : Type(std::move(Type)), FirstSeenAt(FirstSeenAt), Def(Def) {}

    std::optional<LLT> Type;
    SMLoc FirstSeenAt;

    // The instruction that defines this register. `nullptr` for live-ins.
    Instruction *Def = nullptr;
  };

  MIRPattern(StringRef Name, Kind K, SMLoc Loc) : Name(Name), K(K), Loc(Loc) {}

  const RegisterInfo &getRegInfo(Register Reg) const {
    return const_cast<MIRPattern *>(this)->getRegInfo(Reg);
  }
  RegisterInfo &getRegInfo(Register Reg);

  /// Loosely type-checks the pattern, inferring as many types as
  /// possible and verifying that existing types make sense given an instruction
  /// opcode. Prints errors as needed and returns false on failure.
  bool typecheck();

  /// Checks that the pattern makes sense with relation to its Kind.
  /// Print errors as needed and returns false on failure.
  bool checkSemantics();

  /// Record a use of a register @p RegName with optional type @p Type.
  ///
  /// If the register has never been seen been seen before, it records it.
  ///
  /// If the register has been seen before this emits relevant diagnostics.
  ///
  /// If this definition is legal, returns the Register object, else returns
  /// nullopt.
  ///
  /// Note: This function is expected to only be called during parsing of the
  /// pattern.
  std::optional<Register> recordRegisterDef(SMLoc At, Instruction &Inst,
                                            StringRef RegName,
                                            std::optional<LLT> Type);

  /// Records a definition of register @p RegName with optional type @p Type.
  ///
  /// If the register has never been seen been seen before, it's considered
  /// as a live-in.
  ///
  /// If the register has been seen before, checks this use is consistent
  /// with previous uses and emits a diagnostic if needed.
  ///
  /// If this use is legal, returns the Register object, else returns nullopt.
  ///
  /// Note: This function is expected to only be called during parsing of the
  /// pattern.
  std::optional<Register> recordRegisterUse(SMLoc At, StringRef RegName,
                                            std::optional<LLT> Type);

  void addInst(std::unique_ptr<Instruction> Inst) {
    PatInsts.emplace_back(std::move(Inst));
  }

  std::string Name;
  Kind K;
  SMLoc Loc;
  std::vector<std::unique_ptr<Instruction>> PatInsts;
  StringMap<RegisterInfo> RegInfos;
  Instruction *PatRoot = nullptr;
};

/// Represents an instruction's operand. This could be an identifier,
/// an immediate or a wildcard.
class MIRPattern::Operand {
  struct WildcardToken {};

  SMLoc Loc;
  bool IsDef = false;
  std::variant<APInt, APFloat, Register, WildcardToken> Data;

  Operand(SMLoc Loc, WildcardToken T) : Loc(Loc), Data(T) {}

public:
  explicit Operand(SMLoc Loc, APInt Value) : Loc(Loc), Data(std::move(Value)) {}
  explicit Operand(SMLoc Loc, APFloat Value)
      : Loc(Loc), Data(std::move(Value)) {}
  explicit Operand(SMLoc Loc, Register Ident, bool IsDef)
      : Loc(Loc), IsDef(IsDef), Data(Ident) {}

  static Operand getWildcard(SMLoc Loc) {
    return Operand(Loc, WildcardToken{});
  }

  SMLoc getLoc() const { return Loc; }
  bool isDef() const { return IsDef; }

  bool isInt() const { return std::holds_alternative<APInt>(Data); }
  const APInt &getInt() const {
    assert(isInt());
    return std::get<APInt>(Data);
  }

  bool isFloat() const { return std::holds_alternative<APFloat>(Data); }
  const APFloat &getFloat() const {
    assert(isFloat());
    return std::get<APFloat>(Data);
  }

  bool isRegister() const { return std::holds_alternative<Register>(Data); }
  Register getRegister() const { return std::get<Register>(Data); }

  bool isWildcard() const {
    return std::holds_alternative<WildcardToken>(Data);
  }

  void print(raw_ostream &OS, const MIRPattern *Pat = nullptr,
             bool PrintRegDef = true) const;
};

/// Represents an instruction in the pattern.
/// This pretty much maps to a normal gMIR instruction, e.g.:
/// `%0 = G_ADD %1, %2`
///
/// Instructions in matching pattern can also have multiple opcodes,
/// representing a "one-of" match type.
/// `%0 = (G_ADD | G_SUB) %1, %2`
class MIRPattern::Instruction {
  SMLoc Loc;
  std::vector<CodeGenInstruction *> Opcodes;
  std::vector<Operand> Operands;
  std::size_t NumDefs = 0;
  bool Commutable = false;

  friend class InstructionParser;

  void addOperand(Operand Op);

public:
  Instruction(SMLoc Loc) : Loc(Loc) {}

  using const_op_iterator = std::vector<Operand>::const_iterator;

  SMLoc getLoc() const { return Loc; }
  const std::vector<CodeGenInstruction *> &opcodes() const { return Opcodes; }

  iterator_range<const_op_iterator> operands() const {
    return make_range(Operands.begin(), Operands.end());
  }

  iterator_range<const_op_iterator> defs() const {
    return make_range(Operands.begin(), Operands.begin() + NumDefs);
  }

  iterator_range<const_op_iterator> uses() const {
    return make_range(Operands.begin() + NumDefs, Operands.end());
  }

  const CodeGenInstruction &getSingleOpcode() const {
    assert(opcodes_size() == 1);
    return *Opcodes.front();
  }

  std::size_t opcodes_size() const { return Opcodes.size(); }
  std::size_t operands_size() const { return Operands.size(); }

  const auto& getOperand(unsigned Idx) const { return Operands[Idx]; }

  bool hasUses() const { return getNumUses() != 0; }
  bool hasDefs() const { return NumDefs != 0; }
  std::size_t getNumDefs() const { return NumDefs; }
  std::size_t getNumUses() const { return Operands.size() - NumDefs; }

  bool hasCopy() const;

  void setIsCommutable(bool Value = true) { Commutable = Value; }
  bool isCommutable() const { return Commutable; }

  void print(raw_ostream &OS, const MIRPattern *Pat, unsigned Indent = 0) const;

  bool verify() const;
};

} // namespace llvm

#endif
