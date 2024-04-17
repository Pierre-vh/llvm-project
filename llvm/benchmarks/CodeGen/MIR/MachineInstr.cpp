//===- benchmark/CodeGen/MIR/MachineInstr.cpp -------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Benchmark of MachineInstr APIs.
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/MachineInstr.h"
#include "Utils.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"

namespace llvm {

static MCInstrDesc TrivialMCID = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

//===----------------------------------------------------------------------===//
// MachineInstr Creation
//===----------------------------------------------------------------------===//

// Test MachineInstr creation with X operands and Y implicit defs+uses.
BENCHMARK_DEFINE_F(OneFnMIRFixture, MachineInstrCtor)(benchmark::State &S) {
  // Create a InstrInfo-like struct with:
  //  - S.range(0) operands
  //  - S.range(1) implicit operands: half defs, half uses.
  static constexpr unsigned MaxImpRegs = 256;
  struct {
    MCInstrDesc MCID = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    MCPhysReg ImpRegs[MaxImpRegs];
  } II;
  II.MCID.NumOperands = S.range(0);
  assert(S.range(1) <= MaxImpRegs);
  assert((S.range(1) % 2) == 0);
  II.MCID.NumImplicitDefs = 0;
  II.MCID.NumImplicitDefs = 0;
  for (unsigned K = 0; K < S.range(1); ++K)
    II.ImpRegs[K] = K;

  for (auto _ : S)
    MF->CreateMachineInstr(II.MCID, DebugLoc());
}

BENCHMARK_REGISTER_F(OneFnMIRFixture, MachineInstrCtor)
  ->Ranges({{2, 64}, {2, 64}});

//===----------------------------------------------------------------------===//
// MachineInstr::addOperand
//===----------------------------------------------------------------------===//

// Add X immediate operands to an instruction.
BENCHMARK_DEFINE_F(OneFnMIRFixture, AddImmOp)(benchmark::State &S) {
  for (auto _ : S) {
    S.PauseTiming();
    // Don't measure the MachineInstr construction time.
    MachineInstr *MI = MF->CreateMachineInstr(TrivialMCID, DebugLoc());
    S.ResumeTiming();

    for (unsigned K = 0; K < S.range(0); ++K)
      MI->addOperand(*MF, MachineOperand::CreateImm(42));
  }
}

BENCHMARK_REGISTER_F(OneFnMIRFixture, AddImmOp)
  ->Range(8, 256)->RangeMultiplier(2);

// Add X immediate operands to an instruction that reserved memory of Y
// operands.
BENCHMARK_DEFINE_F(OneFnMIRFixture, AddReservedImmOp)(benchmark::State &S) {
  auto II = TrivialMCID;
  II.NumOperands = S.range(1);
  for (auto _ : S) {
    S.PauseTiming();
    // Don't measure the MachineInstr construction time.
    MachineInstr *MI = MF->CreateMachineInstr(II, DebugLoc());
    S.ResumeTiming();

    for (unsigned K = 0; K < S.range(0); ++K)
      MI->addOperand(*MF, MachineOperand::CreateImm(42));
  }
}

BENCHMARK_REGISTER_F(OneFnMIRFixture, AddReservedImmOp)
  ->ArgsProduct({{8, 64, 128}, {0, 8, 64}});

// Add X copies of one register to an instruction.
BENCHMARK_DEFINE_F(OneFnMIRFixture, AddRegOp)(benchmark::State &S) {
  for (auto _ : S) {
    S.PauseTiming();
    // Don't measure the MachineInstr construction time.
    MachineInstr *MI = MF->CreateMachineInstr(TrivialMCID, DebugLoc());
    Register R = MRI->createGenericVirtualRegister(LLT::scalar(32));
    S.ResumeTiming();

    for (unsigned K = 0; K < S.range(0); ++K)
      MI->addOperand(*MF, MachineOperand::CreateReg(R, /*Def*/ false));
  }
}

BENCHMARK_REGISTER_F(OneFnMIRFixture, AddRegOp)
  ->Range(8, 256)->RangeMultiplier(2);

// Add X implicit copies of one register to an instruction.
BENCHMARK_DEFINE_F(OneFnMIRFixture, AddImpRegOp)(benchmark::State &S) {
  for (auto _ : S) {
    S.PauseTiming();
    // Don't measure the MachineInstr construction time.
    MachineInstr *MI = MF->CreateMachineInstr(TrivialMCID, DebugLoc());
    Register R = MRI->createGenericVirtualRegister(LLT::scalar(32));
    S.ResumeTiming();

    for (unsigned K = 0; K < S.range(0); ++K)
      MI->addOperand(
          *MF, MachineOperand::CreateReg(R, /*Def*/ false, /*Implicit*/ true));
  }
}

BENCHMARK_REGISTER_F(OneFnMIRFixture, AddImpRegOp)
  ->RangeMultiplier(2)->Range(8, 256);

// Add X implicit registers, then Y explicit register operands to an
// instruction.
BENCHMARK_DEFINE_F(OneFnMIRFixture, AddImpRegOpThenRegOp)(benchmark::State &S) {
  for (auto _ : S) {
    S.PauseTiming();
    // Don't measure the MachineInstr construction time.
    MachineInstr *MI = MF->CreateMachineInstr(TrivialMCID, DebugLoc());
    Register R = MRI->createGenericVirtualRegister(LLT::scalar(32));

    // Add a bunch of implicit operands first. Don't time those.
    for (unsigned K = 0; K < S.range(0); ++K) {
      MI->addOperand(
          *MF, MachineOperand::CreateReg(R, /*Def*/ false, /*Implicit*/ true));
    }
    S.ResumeTiming();

    // Now time how long it takes to add the explicit ones.
    for (unsigned K = 0; K < S.range(1); ++K)
      MI->addOperand(*MF, MachineOperand::CreateReg(R, /*Def*/ false));
  }
}

// Check 8 and 64 implicit operands with 8 to 512 explicit ones.
BENCHMARK_REGISTER_F(OneFnMIRFixture, AddImpRegOpThenRegOp)
    ->Ranges({{8, 64}, {8, 512}});

} // namespace llvm
