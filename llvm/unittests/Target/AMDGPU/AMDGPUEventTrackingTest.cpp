//===- AMDGPUEventTrackingTest.cpp ------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "AMDGPUEventTracking.h"
#include "AMDGPUUnitTests.h"
#include "AMDGPUWaitcntUtils.h"
#include "MCTargetDesc/AMDGPUMCTargetDesc.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "gtest/gtest.h"

using namespace llvm;
using namespace llvm::AMDGPU;
using namespace llvm::AMDGPU::eventtracking;

namespace {

class AMDGPUGFX12EventTrackingTest : public AMDGPUCodeGenTestBase {
public:
  void SetUp() override {
    setUpImpl("amdgpu12.00-amd-amdhsa", "", "");

    TrackerGetter = [&](const MachineBasicBlock &MBB) -> EventTracker & {
      const GCNSubtarget &ST = MBB.getParent()->getSubtarget<GCNSubtarget>();
      // EventTracker stores pointers into the counter list, so it must outlive
      // the trackers.
      if (Counters.empty())
        Counters = getCounters(ST, /*IsExpertMode=*/false);
      auto &Entry = Trackers[&MBB];
      if (!Entry)
        Entry = std::make_unique<EventTracker>(MBB, Counters);
      return *Entry;
    };
  }

  EventTracker &
  visitAll(MachineBasicBlock &MBB,
           function_ref<void(EventTracker &ET)> AfterVisit = nullptr) {
    const GCNSubtarget &ST = MBB.getParent()->getSubtarget<GCNSubtarget>();

    EventTracker &ET = TrackerGetter(MBB);
    ET.enterBlock(TrackerGetter);
    for (MachineInstr &MI : MBB) {
      HWEvents Events =
          getEventsFor(MI, ST, /*IsExpertMode=*/false, /*TgSplit=*/false);
      for (HWEvents SingleEv : Events) {
        ET.record(MI, SingleHWEvent::encode(SingleEv));
      }
    }
    if (AfterVisit)
      AfterVisit(ET);
    return ET;
  }

  SmallVector<AMDGPUInstCounter, NUM_INST_CNTS> Counters;
  std::function<EventTracker &(const MachineBasicBlock &)> TrackerGetter;
  DenseMap<const MachineBasicBlock *, std::unique_ptr<EventTracker>> Trackers;
};

namespace {

/// Provides some helpers to declaratively check the state of the EventTracker
/// for one counter. This provides helpers to check the general counter state
/// (value, etc) but also allows iterating over the timeline from the oldest to
/// the youngest element.
///
/// This makes the actual test cases clearer.
struct TrackerRecordsChecker {
  TrackerRecordsChecker(EventTracker &ET, InstCounterType T)
      : ET(ET), T(T), Records(ET.getTimeline(T)) {}

  unsigned getCount() { return ET.count(T); }

  bool empty() { return Records.empty(); }

  // Has no records and count is zero
  bool unused() { return empty() && !getCount(); }

  const EventTrackerRecord &cur() { return Records[CurElt]; }

  /// Move to the next record.
  /// \returns true on success, false if the end has been reached.
  bool next() {
    ++CurElt;
    if (CurElt >= Records.size())
      return false;
    return true;
  }

  EventTracker &ET;
  InstCounterType T;
  ArrayRef<EventTrackerRecord> Records;
  unsigned CurElt = 0;
};

} // namespace

/// Check trivial straight line counting.
TEST_F(AMDGPUGFX12EventTrackingTest, BasicTimeline) {
  StringRef MIR = R"(
name:            BasicTimeline
body:             |
  bb.0:
    liveins: $vgpr0_vgpr1, $vgpr1_vgpr2, $vgpr3_vgpr4, $vgpr4_vgpr5

    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    $vgpr0 = DS_READ_B32_gfx9 $vgpr1, 0, 0, implicit $exec
    GLOBAL_STORE_DWORDX2 $vgpr1_vgpr2, $vgpr3_vgpr4, 0, 0, implicit $exec
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("BasicTimeline");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);

  auto &ET = visitAll(BB0);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_EQ(LoadCnt.getCount(), 1u);
  EXPECT_FALSE(LoadCnt.empty());
  EXPECT_EQ(LoadCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);
  EXPECT_EQ(LoadCnt.cur().getAge(), 0u);
  EXPECT_FALSE(LoadCnt.next());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_FALSE(DsCnt.empty());
  EXPECT_EQ(DsCnt.cur().getMI()->getOpcode(), AMDGPU::DS_READ_B32_gfx9);
  EXPECT_EQ(DsCnt.cur().getAge(), 0u);
  EXPECT_FALSE(DsCnt.next());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_FALSE(StoreCnt.empty());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getAge(), 1u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORDX2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Check partial and full drains of a counter.
TEST_F(AMDGPUGFX12EventTrackingTest, Drain) {
  StringRef MIR = R"(
name:            Drain
body:             |
  bb.0:
    liveins: $vgpr0_vgpr1, $vgpr1_vgpr2, $vgpr3_vgpr4, $vgpr4_vgpr5

    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    GLOBAL_STORE_DWORDX2 $vgpr1_vgpr2, $vgpr3_vgpr4, 0, 0, implicit $exec
    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("Drain");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);

  auto &ET = visitAll(BB0);

  EXPECT_EQ(ET.getPendingEvents(AMDGPU::STORE_CNT),
            HWEvents(HWEvents::VMEM_WRITE_ACCESS));
  EXPECT_EQ(ET.getPendingEvents(AMDGPU::LOAD_CNT),
            HWEvents(HWEvents::VMEM_READ_ACCESS));
  EXPECT_FALSE(ET.getPendingEvents(AMDGPU::DS_CNT));

  // Partial drain: only the two youngest stores remain.
  ET.drain(AMDGPU::STORE_CNT, 2);
  {
    auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
    EXPECT_EQ(StoreCnt.getCount(), 2u);
    EXPECT_FALSE(StoreCnt.empty());
    EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(),
              AMDGPU::GLOBAL_STORE_DWORDX2);
    EXPECT_EQ(StoreCnt.cur().getAge(),
              1u); // drain doesn't change record ages
    EXPECT_TRUE(StoreCnt.next());
    EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
    EXPECT_EQ(StoreCnt.cur().getAge(),
              0u); // drain doesn't change record ages
    EXPECT_FALSE(StoreCnt.next());
  }

  // Draining a counter does not affect other counters.
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), 1u);
  EXPECT_EQ(ET.getTimeline(AMDGPU::LOAD_CNT).size(), 1u);

  // Draining above the current count is a no-op.
  ET.drain(AMDGPU::STORE_CNT, 5);
  EXPECT_EQ(ET.count(AMDGPU::STORE_CNT), 2u);
  EXPECT_EQ(ET.getTimeline(AMDGPU::STORE_CNT).size(), 2u);

  // Full drain.
  ET.drain(AMDGPU::STORE_CNT);
  EXPECT_TRUE(TrackerRecordsChecker(ET, AMDGPU::STORE_CNT).unused());
  EXPECT_FALSE(ET.getPendingEvents(AMDGPU::STORE_CNT));
}

/// Check cases where a block loops back on itself.
TEST_F(AMDGPUGFX12EventTrackingTest, SelfPredecessor) {
  StringRef MIR = R"(
name:            BasicTimeline
body:             |
  bb.0:
    liveins: $vgpr1_vgpr2, $vgpr3_vgpr4, $vgpr4_vgpr5, $scc

    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    $vgpr0 = DS_READ_B32_gfx9 $vgpr1, 0, 0, implicit $exec
    GLOBAL_STORE_DWORDX2 $vgpr1_vgpr2, $vgpr3_vgpr4, 0, 0, implicit $exec
    S_CBRANCH_SCC1 %bb.0, implicit $scc
    S_BRANCH %bb.1

  bb.1:
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("BasicTimeline");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);

  // Iterate twice
  visitAll(BB0);
  auto &ET = visitAll(BB0);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_EQ(LoadCnt.getCount(), 2u);
  EXPECT_FALSE(LoadCnt.empty());
  EXPECT_EQ(LoadCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);
  EXPECT_EQ(LoadCnt.cur().getAge(), 1u);
  EXPECT_TRUE(LoadCnt.next());
  EXPECT_EQ(LoadCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);
  EXPECT_EQ(LoadCnt.cur().getAge(), 0u);
  EXPECT_FALSE(LoadCnt.next());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 2u);
  EXPECT_FALSE(DsCnt.empty());
  EXPECT_EQ(DsCnt.cur().getMI()->getOpcode(), AMDGPU::DS_READ_B32_gfx9);
  EXPECT_EQ(DsCnt.cur().getAge(), 1u);
  EXPECT_TRUE(DsCnt.next());
  EXPECT_EQ(DsCnt.cur().getMI()->getOpcode(), AMDGPU::DS_READ_B32_gfx9);
  EXPECT_EQ(DsCnt.cur().getAge(), 0u);
  EXPECT_FALSE(DsCnt.next());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_FALSE(StoreCnt.empty());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORDX2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 1u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORDX2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Check all events carry into the next incoming block.
TEST_F(AMDGPUGFX12EventTrackingTest, SingleIncomingBlock) {
  StringRef MIR = R"(
name:            SingleIncomingBlock
body:             |
  bb.0:
    successors: %bb.1
    liveins: $vgpr0_vgpr1, $vgpr1_vgpr2, $vgpr3_vgpr4, $vgpr4_vgpr5

    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    $vgpr0 = DS_READ_B32_gfx9 $vgpr1, 0, 0, implicit $exec
    GLOBAL_STORE_DWORDX2 $vgpr1_vgpr2, $vgpr3_vgpr4, 0, 0, implicit $exec

  bb.1:

    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("SingleIncomingBlock");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);

  visitAll(BB0);
  auto &ET = visitAll(BB1);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_EQ(LoadCnt.getCount(), 1u);
  EXPECT_FALSE(LoadCnt.empty());
  EXPECT_EQ(LoadCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);
  EXPECT_EQ(LoadCnt.cur().getAge(), 0u);
  EXPECT_FALSE(LoadCnt.next());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_FALSE(DsCnt.empty());
  EXPECT_EQ(DsCnt.cur().getMI()->getOpcode(), AMDGPU::DS_READ_B32_gfx9);
  EXPECT_EQ(DsCnt.cur().getAge(), 0u);
  EXPECT_FALSE(DsCnt.next());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_FALSE(StoreCnt.empty());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getAge(), 1u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORDX2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Check a simple merge where all events differ in each incoming block.
TEST_F(AMDGPUGFX12EventTrackingTest, SimpleDisjointMerge) {
  StringRef MIR = R"(
name:            SimpleDisjointMerge
body:             |
  bb.0:
    successors: %bb.2
    liveins: $vgpr1, $vgpr4_vgpr5

    $vgpr0 = DS_READ_B32_gfx9 $vgpr1, 0, 0, implicit $exec
    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    S_BRANCH %bb.2

  bb.1:
    successors: %bb.2
    liveins: $vgpr0_vgpr1, $vgpr1_vgpr2, $vgpr3_vgpr4
    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    GLOBAL_STORE_DWORDX2 $vgpr1_vgpr2, $vgpr3_vgpr4, 0, 0, implicit $exec
    S_BRANCH %bb.2

  bb.2:
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("SimpleDisjointMerge");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);
  MachineBasicBlock &BB2 = *MF.getBlockNumbered(2);

  visitAll(BB0);
  visitAll(BB1);
  auto &ET = visitAll(BB2);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_EQ(LoadCnt.getCount(), 1u);
  EXPECT_FALSE(LoadCnt.empty());
  EXPECT_EQ(LoadCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);
  EXPECT_EQ(LoadCnt.cur().getAge(), 0u);
  EXPECT_FALSE(LoadCnt.next());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_FALSE(DsCnt.empty());
  EXPECT_EQ(DsCnt.cur().getMI()->getOpcode(), AMDGPU::DS_READ_B32_gfx9);
  EXPECT_EQ(DsCnt.cur().getAge(), 0u);
  EXPECT_FALSE(DsCnt.next());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_FALSE(StoreCnt.empty());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getAge(), 1u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORDX2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Merge with divergent events in a counter.
TEST_F(AMDGPUGFX12EventTrackingTest, DivergenceMerge) {
  StringRef MIR = R"(
name:            DivergenceMerge
body:             |
  bb.0:
    successors: %bb.2
    liveins: $vgpr1, $vgpr2

    $vgpr0 = DS_READ_B32_gfx9 $vgpr1, 0, 0, implicit $exec
    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    S_BRANCH %bb.2

  bb.1:
    successors: %bb.2
    liveins: $vgpr1_vgpr2, $vgpr3_vgpr4, $vgpr4_vgpr5
    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    GLOBAL_STORE_DWORDX2 $vgpr1_vgpr2, $vgpr3_vgpr4, 0, 0, implicit $exec
    S_BRANCH %bb.2

  bb.2:
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("DivergenceMerge");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);
  MachineBasicBlock &BB2 = *MF.getBlockNumbered(2);

  visitAll(BB0);
  visitAll(BB1);
  auto &ET = visitAll(BB2);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_EQ(LoadCnt.getCount(), 1u);
  EXPECT_FALSE(LoadCnt.empty());
  EXPECT_EQ(LoadCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);
  EXPECT_EQ(LoadCnt.cur().getAge(), 0u);
  EXPECT_FALSE(LoadCnt.next());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_FALSE(DsCnt.empty());
  EXPECT_EQ(DsCnt.cur().getMI()->getOpcode(), AMDGPU::DS_READ_B32_gfx9);
  EXPECT_EQ(DsCnt.cur().getAge(), 0u);
  EXPECT_FALSE(DsCnt.next());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  // Count is 1 because we have 1 event max across all predecessors.
  EXPECT_EQ(StoreCnt.getCount(), 1u);
  EXPECT_FALSE(StoreCnt.empty());
  // First successor has GLOBAL_STORE_DWORD at age 0
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_TRUE(StoreCnt.next());
  // Second successor has GLOBAL_STORE_DWORDX2 at age 0 too
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORDX2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Basic diamond CFG, the store is carried all the way into bb3 and uniqued
/// again so only 1 instance of the record is present in bb3.
TEST_F(AMDGPUGFX12EventTrackingTest, BasicDiamond) {
  StringRef MIR = R"(
name:            BasicDiamond
body:             |
  bb.0:
    successors: %bb.1, %bb.2
    liveins: $vgpr0_vgpr1, $vgpr2, $vgpr4_vgpr5, $scc

    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    S_CBRANCH_SCC1 %bb.1, implicit $scc
    S_BRANCH %bb.2

  bb.1:
    successors: %bb.3
    liveins: $vgpr1
    $vgpr0 = DS_READ_B32_gfx9 $vgpr1, 0, 0, implicit $exec
    S_BRANCH %bb.3

  bb.2:
    successors: %bb.3
    liveins: $vgpr4_vgpr5
    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    S_BRANCH %bb.3

  bb.3:
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("BasicDiamond");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);
  MachineBasicBlock &BB2 = *MF.getBlockNumbered(2);
  MachineBasicBlock &BB3 = *MF.getBlockNumbered(3);

  visitAll(BB0);
  visitAll(BB1);
  visitAll(BB2);
  auto &ET = visitAll(BB3);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_EQ(LoadCnt.getCount(), 1u);
  EXPECT_FALSE(LoadCnt.empty());
  EXPECT_EQ(LoadCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);
  EXPECT_EQ(LoadCnt.cur().getAge(), 0u);
  EXPECT_FALSE(LoadCnt.next());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_FALSE(DsCnt.empty());
  EXPECT_EQ(DsCnt.cur().getMI()->getOpcode(), AMDGPU::DS_READ_B32_gfx9);
  EXPECT_EQ(DsCnt.cur().getAge(), 0u);
  EXPECT_FALSE(DsCnt.next());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 1u);
  EXPECT_FALSE(StoreCnt.empty());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Asymetrical diamond
///   - bb0 has two stores
///   - bb1 adds another store without any waits.
///   - bb2 adds a store and waits on the two stores from bb0 afterwards
///
/// The timeline will be:
///   - Stores from bb0 exist at 1/2
///   - The added store from bb1 exist at age 0
///   - The added store from bb2 exist at age 0
TEST_F(AMDGPUGFX12EventTrackingTest, AsymetricalDiamond) {
  StringRef MIR = R"(
name:            AsymetricalDiamond
body:             |
  bb.0:
    successors: %bb.1, %bb.2
    liveins: $vgpr0_vgpr1, $vgpr1_vgpr2, $vgpr3_vgpr4, $scc

    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    GLOBAL_STORE_DWORDX2 $vgpr1_vgpr2, $vgpr3_vgpr4, 0, 0, implicit $exec
    S_CBRANCH_SCC1 %bb.1, implicit $scc
    S_BRANCH %bb.2

  bb.1:
    successors: %bb.3
    liveins: $vgpr1_vgpr2, $vgpr3
    GLOBAL_STORE_DWORD $vgpr1_vgpr2, $vgpr3, 0, 0, implicit $exec
    S_BRANCH %bb.3

  bb.2:
    successors: %bb.3
    liveins: $vgpr0_vgpr1, $vgpr2
    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    S_BRANCH %bb.3

  bb.3:
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("AsymetricalDiamond");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);
  MachineBasicBlock &BB2 = *MF.getBlockNumbered(2);
  MachineBasicBlock &BB3 = *MF.getBlockNumbered(3);

  visitAll(BB0);
  visitAll(BB1);
  visitAll(BB2,
           /*AfterVisit=*/[&](EventTracker &ET) { ET.drain(STORE_CNT, 1); });
  auto &ET = visitAll(BB3);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_TRUE(LoadCnt.unused());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_TRUE(DsCnt.unused());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);

  EXPECT_EQ(StoreCnt.getCount(), 3u);
  EXPECT_FALSE(StoreCnt.empty());

  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getMI()->getParent(), &BB0);
  EXPECT_EQ(StoreCnt.cur().getAge(), 2u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORDX2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 1u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getMI()->getParent(), &BB1);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getMI()->getParent(), &BB2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Asymetrical diamond
///   - bb0 has one store
///   - bb1 just falls through
///   - bb2 adds 1 more store.
///
/// The timeline will showcase how the value of a counter can be different from
/// the content of the timeline.
///   - The timeline will have all records at an age of 0.
///   - The counter will still be at 2.
TEST_F(AMDGPUGFX12EventTrackingTest, AsymetricalDiamond2) {
  StringRef MIR = R"(
name:            AsymetricalDiamond2
body:             |
  bb.0:
    successors: %bb.1, %bb.2
    liveins: $vgpr0_vgpr1, $vgpr2, $scc

    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    S_CBRANCH_SCC1 %bb.1, implicit $scc
    S_BRANCH %bb.2

  bb.1:
    successors: %bb.3
    S_BRANCH %bb.3

  bb.2:
    successors: %bb.3
    liveins: $vgpr0_vgpr1, $vgpr2
    GLOBAL_STORE_DWORD $vgpr0_vgpr1, $vgpr2, 0, 0, implicit $exec
    S_BRANCH %bb.3

  bb.3:
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("AsymetricalDiamond2");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);
  MachineBasicBlock &BB2 = *MF.getBlockNumbered(2);
  MachineBasicBlock &BB3 = *MF.getBlockNumbered(3);

  visitAll(BB0);
  visitAll(BB1);
  visitAll(BB2);

  auto &ET = visitAll(BB3);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_TRUE(LoadCnt.unused());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_TRUE(DsCnt.unused());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);

  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_FALSE(StoreCnt.empty());

  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getMI()->getParent(), &BB0);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_TRUE(StoreCnt.next());
  EXPECT_EQ(StoreCnt.cur().getMI()->getOpcode(), AMDGPU::GLOBAL_STORE_DWORD);
  EXPECT_EQ(StoreCnt.cur().getMI()->getParent(), &BB2);
  EXPECT_EQ(StoreCnt.cur().getAge(), 0u);
  EXPECT_FALSE(StoreCnt.next());
}

/// Check that the count of a counter stops at its limit minus 1, while the
/// timeline keeps growing and record ages keep increasing.
TEST_F(AMDGPUGFX12EventTrackingTest, CountCappedAtLimit) {
  StringRef MIR = R"(
name:            CountCappedAtLimit
body:             |
  bb.0:
    liveins: $vgpr4_vgpr5

    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("CountCappedAtLimit");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineInstr &Load = BB0.front();
  ASSERT_EQ(Load.getOpcode(), AMDGPU::GLOBAL_LOAD_DWORD);

  const GCNSubtarget &ST = MF.getSubtarget<GCNSubtarget>();
  auto Counters = getCounters(ST, /*IsExpertMode=*/false);
  const AMDGPUInstCounter *LoadIC = nullptr;
  for (const AMDGPUInstCounter &IC : Counters) {
    if (IC.getType() == AMDGPU::LOAD_CNT)
      LoadIC = &IC;
  }
  ASSERT_TRUE(LoadIC && LoadIC->hasLimit());
  const unsigned Limit = LoadIC->getLimit();
  ASSERT_GT(Limit, 1u);

  EventTracker ET(BB0, Counters);
  ET.enterBlock(TrackerGetter);
  const SingleHWEvent Ev = SingleHWEvent::encode(HWEvents::VMEM_READ_ACCESS);

  // Fill the counter up to just before the cap.
  for (unsigned I = 0; I < Limit - 2; ++I)
    ET.record(Load, Ev);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Limit - 2);
  EXPECT_FALSE(ET.isCapped(AMDGPU::LOAD_CNT));

  // One more event reaches the cap.
  ET.record(Load, Ev);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Limit - 1);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));

  // Further events no longer increment the count, but are still recorded and
  // still age the existing records.
  constexpr unsigned Extra = 5;
  for (unsigned I = 0; I < Extra; ++I)
    ET.record(Load, Ev);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Limit - 1);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));

  const unsigned NumRecords = Limit - 1 + Extra;
  ArrayRef<EventTrackerRecord> TL = ET.getTimeline(AMDGPU::LOAD_CNT);
  ASSERT_EQ(TL.size(), NumRecords);
  EXPECT_EQ(TL.front().getAge(), NumRecords - 1);
  EXPECT_EQ(TL.back().getAge(), 0u);
  EXPECT_GT(TL.front().getAge(), ET.count(AMDGPU::LOAD_CNT));

  // Other counters are unaffected.
  EXPECT_TRUE(TrackerRecordsChecker(ET, AMDGPU::STORE_CNT).unused());
  EXPECT_FALSE(ET.isCapped(AMDGPU::STORE_CNT));

  // A partial drain uncaps the counter and removes all records at or above the
  // drained age.
  ET.drain(AMDGPU::LOAD_CNT, 3);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), 3u);
  EXPECT_FALSE(ET.isCapped(AMDGPU::LOAD_CNT));
  EXPECT_EQ(ET.getTimeline(AMDGPU::LOAD_CNT).size(), 3u);

  // The counter can be capped again afterwards.
  for (unsigned I = 0; I < Limit; ++I)
    ET.record(Load, Ev);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Limit - 1);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));
}

/// Check that drainCappedRecords only acts on capped counters, removes exactly
/// the records whose age is at or above the cap (Limit - 1), and leaves the
/// count and the younger records untouched.
TEST_F(AMDGPUGFX12EventTrackingTest, DrainCappedRecords) {
  StringRef MIR = R"(
name:            DrainCappedRecords
body:             |
  bb.0:
    liveins: $vgpr4_vgpr5

    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("DrainCappedRecords");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineInstr &Load = BB0.front();

  const GCNSubtarget &ST = MF.getSubtarget<GCNSubtarget>();
  auto Counters = getCounters(ST, /*IsExpertMode=*/false);
  const unsigned Limit = getCounter(AMDGPU::LOAD_CNT, Counters).getLimit();
  const unsigned Cap = Limit - 1;
  ASSERT_GT(Limit, 2u);

  EventTracker ET(BB0, Counters);
  ET.enterBlock(TrackerGetter);
  const SingleHWEvent Ev = SingleHWEvent::encode(HWEvents::VMEM_READ_ACCESS);

  // Not capped: nothing is removed.
  for (unsigned I = 0; I < 3; ++I)
    ET.record(Load, Ev);
  ASSERT_FALSE(ET.isCapped(AMDGPU::LOAD_CNT));
  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  EXPECT_EQ(ET.getTimeline(AMDGPU::LOAD_CNT).size(), 3u);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), 3u);

  // Capped, with Extra records at or above the cap.
  constexpr unsigned Extra = 4;
  for (unsigned I = 3; I < Cap + Extra; ++I)
    ET.record(Load, Ev);
  ASSERT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));
  ASSERT_EQ(ET.getTimeline(AMDGPU::LOAD_CNT).size(), Cap + Extra);

  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  ArrayRef<EventTrackerRecord> TL = ET.getTimeline(AMDGPU::LOAD_CNT);
  ASSERT_EQ(TL.size(), Cap);
  EXPECT_EQ(TL.front().getAge(), Cap - 1);
  EXPECT_EQ(TL.back().getAge(), 0u);
  // The hardware counter stays saturated: the count is not lowered.
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Cap);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));

  // Idempotent.
  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  EXPECT_EQ(ET.getTimeline(AMDGPU::LOAD_CNT).size(), Cap);

  // One more event ages the oldest record to the cap; it is removed again.
  ET.record(Load, Ev);
  EXPECT_EQ(ET.getTimeline(AMDGPU::LOAD_CNT).front().getAge(), Cap);
  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  TL = ET.getTimeline(AMDGPU::LOAD_CNT);
  EXPECT_EQ(TL.size(), Cap);
  EXPECT_EQ(TL.front().getAge(), Cap - 1);

  // Other counters are unaffected.
  ET.drainCappedRecords(AMDGPU::STORE_CNT);
  EXPECT_TRUE(TrackerRecordsChecker(ET, AMDGPU::STORE_CNT).unused());
}

/// Check that widenCount raises the count to the cap without touching the
/// timeline, that later events don't push the count further, and that it does
/// nothing on a counter the target lacks.
TEST_F(AMDGPUGFX12EventTrackingTest, WidenCount) {
  StringRef MIR = R"(
name:            WidenCount
body:             |
  bb.0:
    liveins: $vgpr4_vgpr5

    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    S_ENDPGM 0
...
)";
  ASSERT_TRUE(parseMIR(MIR));
  MachineFunction &MF = getMF("WidenCount");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineInstr &Load = BB0.front();

  const GCNSubtarget &ST = MF.getSubtarget<GCNSubtarget>();
  auto Counters = getCounters(ST, /*IsExpertMode=*/false);
  const unsigned Cap = getCounter(AMDGPU::LOAD_CNT, Counters).getLimit() - 1;

  EventTracker ET(BB0, Counters);
  ET.enterBlock(TrackerGetter);
  const SingleHWEvent Ev = SingleHWEvent::encode(HWEvents::VMEM_READ_ACCESS);
  ET.record(Load, Ev);
  ET.record(Load, Ev);
  ASSERT_EQ(ET.count(AMDGPU::LOAD_CNT), 2u);

  EXPECT_TRUE(ET.widenCount(AMDGPU::LOAD_CNT));
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Cap);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));
  ArrayRef<EventTrackerRecord> TL = ET.getTimeline(AMDGPU::LOAD_CNT);
  ASSERT_EQ(TL.size(), 2u);
  EXPECT_EQ(TL[0].getAge(), 1u);
  EXPECT_EQ(TL[1].getAge(), 0u);

  // Widening twice is a no-op; recording keeps the count at the cap.
  EXPECT_TRUE(ET.widenCount(AMDGPU::LOAD_CNT));
  ET.record(Load, Ev);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Cap);
  EXPECT_EQ(ET.getTimeline(AMDGPU::LOAD_CNT).size(), 3u);

  // A drain still lowers a widened count.
  ET.drain(AMDGPU::LOAD_CNT, 1);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), 1u);
  EXPECT_FALSE(ET.isCapped(AMDGPU::LOAD_CNT));

  // TENSOR_CNT does not exist on gfx12.00: nothing to widen.
  EXPECT_FALSE(ET.widenCount(AMDGPU::TENSOR_CNT));
  EXPECT_EQ(ET.count(AMDGPU::TENSOR_CNT), 0u);
}

} // namespace
