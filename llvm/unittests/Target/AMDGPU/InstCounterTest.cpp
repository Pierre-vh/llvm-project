//===- llvm/unittests/Target/AMDGPU/InstCounterTest.cpp -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "AMDGPUUnitTests.h"
#include "AMDGPUWaitcntUtils.h"
#include "GCNSubtarget.h"
#include "llvm/TargetParser/Triple.h"
#include "gtest/gtest.h"

using namespace llvm;
using namespace llvm::AMDGPU;

namespace {

constexpr unsigned NoLimit = AMDGPUInstCounter::NoLimit;

constexpr HWEvents VMemReadEvents =
    HWEvents::VMEM_READ_ACCESS | HWEvents::VMEM_SAMPLER_READ_ACCESS |
    HWEvents::VMEM_BVH_READ_ACCESS | HWEvents::VMEM_INV_ACCESS;
constexpr HWEvents VMemWriteEvents =
    HWEvents::VMEM_WRITE_ACCESS | HWEvents::SCRATCH_WRITE_ACCESS;
constexpr HWEvents ExportEvents =
    HWEvents::EXP_GPR_LOCK | HWEvents::GDS_GPR_LOCK | HWEvents::VMW_GPR_LOCK |
    HWEvents::EXP_PARAM_ACCESS | HWEvents::EXP_POS_ACCESS |
    HWEvents::EXP_LDS_ACCESS;
constexpr HWEvents PreGFX12LgkmEvents =
    HWEvents::SMEM_ACCESS | HWEvents::LDS_ACCESS | HWEvents::GDS_ACCESS |
    HWEvents::SQ_MESSAGE;

void checkCounters(StringRef CPU,
                   ArrayRef<AMDGPUInstCounter> ExpectedCounters) {
  Triple TT("amdgcn-amd-amdhsa");
  auto TM = createAMDGPUTargetMachine(TT, CPU, "");
  ASSERT_TRUE(TM) << "No target machine";
  GCNSubtarget ST(TT, CPU, "", *TM);

  auto Counters = getCounters(ST, /*IsExpertMode=*/false);
  ASSERT_EQ(Counters.size(), ExpectedCounters.size()) << CPU.str();
  for (auto [Counter, Expected] : zip_equal(Counters, ExpectedCounters)) {
    EXPECT_EQ(Counter.getIndex(), Expected.getIndex()) << Expected.getName();
    EXPECT_EQ(Counter.getType(), Expected.getType()) << Expected.getName();
    EXPECT_EQ(Counter.getLimit(), Expected.getLimit()) << Expected.getName();
    EXPECT_EQ(Counter.getName(), Expected.getName());
    EXPECT_EQ(Counter.getEvents().value(), Expected.getEvents().value())
        << Expected.getName();
  }
}

class InstCounterTest : public AMDGPUTestBase {};

// No separate store counter: stores are tracked by the VM counter.
TEST_F(InstCounterTest, GFX7) {
  checkCounters("gfx700", {
                              {0, LOAD_CNT, 15, "VM_CNT",
                               VMemReadEvents | VMemWriteEvents},
                              {1, DS_CNT, 15, "LGKM_CNT", PreGFX12LgkmEvents},
                              {2, EXP_CNT, 7, "EXP_CNT", ExportEvents},
                          });
}

TEST_F(InstCounterTest, GFX10) {
  checkCounters("gfx1030", {
                               {0, LOAD_CNT, 63, "VM_CNT", VMemReadEvents},
                               {1, DS_CNT, 63, "LGKM_CNT", PreGFX12LgkmEvents},
                               {2, EXP_CNT, 7, "EXP_CNT", ExportEvents},
                               {3, STORE_CNT, 63, "VS_CNT", VMemWriteEvents},
                           });
}

TEST_F(InstCounterTest, GFX12) {
  checkCounters(
      "gfx1200",
      {
          {0, LOAD_CNT, 63, "LOAD_CNT",
           HWEvents::VMEM_READ_ACCESS | HWEvents::VMEM_INV_ACCESS},
          {1, DS_CNT, 63, "DS_CNT",
           HWEvents::LDS_ACCESS | HWEvents::GDS_ACCESS},
          {2, EXP_CNT, 7, "EXP_CNT", ExportEvents},
          {3, STORE_CNT, 63, "STORE_CNT", VMemWriteEvents},
          {4, SAMPLE_CNT, 63, "SAMPLE_CNT", HWEvents::VMEM_SAMPLER_READ_ACCESS},
          {5, BVH_CNT, 7, "BVH_CNT", HWEvents::VMEM_BVH_READ_ACCESS},
          {6, KM_CNT, 31, "KM_CNT",
           HWEvents::SMEM_ACCESS | HWEvents::SQ_MESSAGE | HWEvents::SCC_WRITE},
      });
}

TEST_F(InstCounterTest, GFX125) {
  checkCounters(
      "gfx1250",
      {
          {0, LOAD_CNT, 63, "LOAD_CNT",
           HWEvents::VMEM_READ_ACCESS | HWEvents::VMEM_INV_ACCESS},
          {1, DS_CNT, 63, "DS_CNT",
           HWEvents::LDS_ACCESS | HWEvents::GDS_ACCESS},
          {2, STORE_CNT, 63, "STORE_CNT", VMemWriteEvents},
          {3, KM_CNT, 31, "KM_CNT",
           HWEvents::SMEM_ACCESS | HWEvents::SQ_MESSAGE | HWEvents::SCC_WRITE},
          {4, X_CNT, 63, "X_CNT", HWEvents::VMEM_GROUP | HWEvents::SMEM_GROUP},
          {5, ASYNC_CNT, 63, "ASYNC_CNT", HWEvents::ASYNC_ACCESS},
          {6, TENSOR_CNT, NoLimit, "TENSOR_CNT", HWEvents::TENSOR_ACCESS},
      });
}

} // namespace
