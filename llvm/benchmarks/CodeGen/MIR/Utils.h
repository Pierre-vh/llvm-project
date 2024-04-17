//===- benchmark/CodeGen/MIR/Utils.h ----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Common helpers (set-up & tear-down) for MIR benchmarks.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_BENCHMARK_CODEGEN_MIR_UTILS_H
#define LLVM_BENCHMARK_CODEGEN_MIR_UTILS_H

#include "benchmark/benchmark.h"
#include <memory>

namespace llvm {
class LLVMContext;
class Module;
class MachineFunction;
class MachineRegisterInfo;

/// A trivial MIR benchmark fixture that sets-up the necessary boilerplate
/// for creating basic blocks & machine instructions inside a single
/// function.
class OneFnMIRFixture : public benchmark::Fixture {
public:
  OneFnMIRFixture();
  virtual ~OneFnMIRFixture();

  void SetUp(::benchmark::State &state) override;
  void TearDown(::benchmark::State &state) override;

  std::unique_ptr<LLVMContext> Ctx;
  std::unique_ptr<Module> M;
  std::unique_ptr<MachineFunction> MF;

  MachineRegisterInfo *MRI = nullptr;
};

} // namespace llvm

#endif
