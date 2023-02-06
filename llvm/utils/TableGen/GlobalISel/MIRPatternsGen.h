//===- MIRPatternsGen.h ---------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_UTILS_TABLEGEN_MIRPATTERNSGEN_H
#define LLVM_UTILS_TABLEGEN_MIRPATTERNSGEN_H

#include "MIRPatterns.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"

namespace llvm {
class raw_ostream;
class StringRef;

/// Helper class to emit C++ code to match & rewrite MIR code using a "match"
/// and "apply" pattern.
///
/// TODO: A lot of this (if not everything) could probably be merged with
/// GIMatchTree.
class MIRPatternGICombinerGen {
public:
  using Instruction = MIRPattern::Instruction;
  using Register = MIRPattern::Register;

private:
  MIRPattern &MatchPat, &ApplyPat;

  unsigned TmpIdx = 0;

  std::string createTmpVarName() {
    return std::string("Tmp") + std::to_string(TmpIdx++);
  }

  DenseMap<const Instruction *, unsigned> MatchInfoIdx;
  unsigned NextMatchInfoIdx = 0;

  std::string getAccessMatchInfoDef(const Instruction *I, Register Reg) const;
  std::string getAccessMatchPatLiveIn(Register Reg) const;

  void recordMatchInfoPush(const Instruction *I) {
    MatchInfoIdx[I] = NextMatchInfoIdx++;
  }

  unsigned getMatchInfoIdx(const Instruction *I) {
    assert(MatchInfoIdx.count(I) != 0);
    return MatchInfoIdx[I];
  }

  void emitInstMatchCode(raw_ostream &OS, const Instruction &I,
                         StringRef IVarName, unsigned Indent);

  void emitInstApplyCode(raw_ostream &OS, const Instruction &I, unsigned Indent,
                         StringMap<std::string> &RegVarNames,
                         DenseSet<Instruction *> &InstsToDelete);

public:
  MIRPatternGICombinerGen(MIRPattern &MatchPat, MIRPattern &ApplyPat)
      : MatchPat(MatchPat), ApplyPat(ApplyPat) {
    assert(MatchPat.isMatchPattern() && ApplyPat.isApplyPattern());
  }

  static void emitMatchInfoDecl(raw_ostream &OS, unsigned Indent = 0);
  static void emitIncludeDeps(raw_ostream &OS);

  void emitMatchCode(raw_ostream &OS, StringRef RootMIVarName,
                     unsigned Indent = 0);
  void emitApplyCode(raw_ostream &OS, unsigned Indent = 0);

  static constexpr const char *MatchInfoName = "MIRPatternsMatchInfo";
  StringRef OpcNamespace = "TargetOpcode";
  StringRef MRIVarName = "MRI";
  StringRef BuilderVarName = "B";
};
} // namespace llvm

#endif
