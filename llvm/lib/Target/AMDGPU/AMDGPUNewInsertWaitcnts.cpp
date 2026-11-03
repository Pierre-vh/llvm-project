//===- AMDGPUNewInsertWaitcnts.cpp - Insert wait instructions -------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// TODO
//
//===----------------------------------------------------------------------===//

#include "AMDGPUNewInsertWaitcnts.h"
#include "AMDGPU.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

#define DEBUG_TYPE "amdgpu-new-insert-waitcnts"

namespace {

class AMDGPUNewInsertWaitcnts {
public:
  bool run(MachineFunction &MF);
};

bool AMDGPUNewInsertWaitcnts::run(MachineFunction &MF) {
  // TODO: Implement the pass.
  return false;
}

class AMDGPUNewInsertWaitcntsLegacy : public MachineFunctionPass {
public:
  static char ID;

  AMDGPUNewInsertWaitcntsLegacy() : MachineFunctionPass(ID) {}

  bool runOnMachineFunction(MachineFunction &MF) override {
    return AMDGPUNewInsertWaitcnts().run(MF);
  }

  StringRef getPassName() const override {
    return "AMDGPU New Insert Waitcnts";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    // TODO: Declare required/preserved analyses once the implementation needs
    // them.
    MachineFunctionPass::getAnalysisUsage(AU);
  }
};

} // end anonymous namespace

char AMDGPUNewInsertWaitcntsLegacy::ID = 0;

char &llvm::AMDGPUNewInsertWaitcntsLegacyID = AMDGPUNewInsertWaitcntsLegacy::ID;

INITIALIZE_PASS(AMDGPUNewInsertWaitcntsLegacy, DEBUG_TYPE,
                "AMDGPU New Insert Waitcnts", false, false)

PreservedAnalyses
AMDGPUNewInsertWaitcntsPass::run(MachineFunction &MF,
                                 MachineFunctionAnalysisManager &MFAM) {
  if (!AMDGPUNewInsertWaitcnts().run(MF))
    return PreservedAnalyses::all();

  return getMachineFunctionPassPreservedAnalyses().preserveSet<CFGAnalyses>();
}
