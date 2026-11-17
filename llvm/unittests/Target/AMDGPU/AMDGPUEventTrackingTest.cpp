//===- AMDGPUEventTrackingTest.cpp ------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// FIXME: Tests are extensively written by AI (at least all the new ones);
//        Carefully review them before publishing any of this upstream.
//        Do not send a slop grenade!

#include "AMDGPUEventTracking.h"
#include "AMDGPUUnitTests.h"
#include "AMDGPUWaitcntUtils.h"
#include "MCTargetDesc/AMDGPUMCTargetDesc.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "gtest/gtest.h"

using namespace llvm;
using namespace llvm::AMDGPU;

namespace {

class AMDGPUGFX12EventTrackingTest : public AMDGPUCodeGenTestBase {
public:
  void SetUp() override {
    setUpImpl("amdgpu12.00-amd-amdhsa", "", "");
  }

  /// \returns the tracker of \p MBB, creating it if needed.
  EventTracker &getTracker(const MachineBasicBlock &MBB) {
    const GCNSubtarget &ST = MBB.getParent()->getSubtarget<GCNSubtarget>();
    // EventTracker stores pointers into the counter list, so it must outlive
    // the trackers.
    if (Counters.empty())
      Counters = getCounters(ST, /*IsExpertMode=*/false);
    auto &Entry = Trackers[&MBB];
    if (!Entry)
      Entry = std::make_unique<EventTracker>(MBB, Counters);
    return *Entry;
  }

  /// \returns the tracker of \p MBB after entering it.
  EventTracker &enterBlock(const MachineBasicBlock &MBB) {
    EventTracker &ET = getTracker(MBB);
    SmallVector<const EventTracker *, 4> Preds;
    for (const MachineBasicBlock *P : MBB.predecessors())
      Preds.push_back(&getTracker(*P));
    ET.enterBlock(Preds);
    return ET;
  }

  EventTracker &
  visitAll(MachineBasicBlock &MBB,
           function_ref<void(EventTracker &ET)> AfterVisit = nullptr) {
    const GCNSubtarget &ST = MBB.getParent()->getSubtarget<GCNSubtarget>();

    EventTracker &ET = enterBlock(MBB);
    for (MachineInstr &MI : MBB) {
      HWEvents Events =
          getEventsFor(MI, ST, /*IsExpertMode=*/false, /*TgSplit=*/false);
      for (HWEvents SingleEv : Events) {
        ET.record(MI, SingleHWEvent::encode(SingleEv));
#if !defined(NDEBUG) || defined(EXPENSIVE_CHECKS)
        ET.verify();
#endif
      }
    }
    if (AfterVisit)
      AfterVisit(ET);
    return ET;
  }

  SmallVector<AMDGPUInstCounter, NUM_INST_CNTS> Counters;
  DenseMap<const MachineBasicBlock *, std::unique_ptr<EventTracker>> Trackers;
};

/// Copy of one timeline record. Unlike \ref EventTrackerRecord, it stays valid
/// when the tracker is modified.
struct RecordSnapshot {
  MachineInstr *MI;
  SingleHWEvent Kind;
  unsigned WaitValue;
};

/// Expected state of one timeline record, for
/// \ref TrackerRecordsChecker::hasRecords.
struct ExpectedRecord {
  unsigned Opcode;
  unsigned WaitValue;
  /// If set, the parent block of the record's MachineInstr.
  const MachineBasicBlock *Parent = nullptr;
};

/// Snapshot of the state of one counter of an \ref EventTracker, taken at
/// construction. Allows declaratively checking the counter state and the
/// timeline, from the oldest to the youngest record.
///
/// The snapshot does not reference the tracker, so it stays valid when the
/// tracker is modified afterwards.
class TrackerRecordsChecker {
public:
  TrackerRecordsChecker(const EventTracker &ET, InstCounterType T)
      : Count(ET.count(T)) {
    for (EventTrackerRecord R : ET.getTimeline(T))
      Records.push_back({R.getMI(), R.getKind(), R.getWaitValue()});
  }

  unsigned getCount() const { return Count; }

  size_t size() const { return Records.size(); }
  bool empty() const { return Records.empty(); }

  /// Has no records and count is zero.
  bool unused() const { return empty() && !getCount(); }

  /// \returns the oldest record.
  const RecordSnapshot &front() const { return Records.front(); }
  /// \returns the youngest record.
  const RecordSnapshot &back() const { return Records.back(); }

  /// Checks that the timeline matches \p Expected exactly, in order (oldest
  /// first). Use with EXPECT_TRUE/ASSERT_TRUE to get a readable diagnostic.
  testing::AssertionResult hasRecords(ArrayRef<ExpectedRecord> Expected) const {
    if (Records.size() != Expected.size()) {
      testing::AssertionResult Res = testing::AssertionFailure();
      Res << "expected " << Expected.size() << " records, got "
          << Records.size() << ':';
      for (const RecordSnapshot &R : Records)
        Res << ' '
            << describe(R.MI, R.MI->getOpcode(), R.WaitValue,
                        R.MI->getParent());
      return Res;
    }

    for (auto [Idx, R, E] : enumerate(Records, Expected)) {
      if (R.MI->getOpcode() == E.Opcode && R.WaitValue == E.WaitValue &&
          (!E.Parent || R.MI->getParent() == E.Parent))
        continue;
      return testing::AssertionFailure()
             << "record #" << Idx << ": expected "
             << describe(R.MI, E.Opcode, E.WaitValue, E.Parent) << ", got "
             << describe(R.MI, R.MI->getOpcode(), R.WaitValue,
                         R.MI->getParent());
    }
    return testing::AssertionSuccess();
  }

private:
  /// \returns "{OPCODE, wait N[, bb.M]}". \p MI is only used to fetch the
  /// opcode names.
  static std::string describe(const MachineInstr *MI, unsigned Opcode,
                              unsigned WaitValue,
                              const MachineBasicBlock *Parent) {
    const TargetInstrInfo *TII = MI->getMF()->getSubtarget().getInstrInfo();
    std::string Str;
    raw_string_ostream OS(Str);
    OS << '{' << TII->getName(Opcode) << ", wait " << WaitValue;
    if (Parent)
      OS << ", bb." << Parent->getNumber();
    OS << '}';
    return Str;
  }

  unsigned Count;
  SmallVector<RecordSnapshot> Records;
};

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
  EXPECT_TRUE(LoadCnt.hasRecords({{AMDGPU::GLOBAL_LOAD_DWORD, 0}}));

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_TRUE(DsCnt.hasRecords({{AMDGPU::DS_READ_B32_gfx9, 0}}));

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_TRUE(StoreCnt.hasRecords({
      {AMDGPU::GLOBAL_STORE_DWORD, 1},
      {AMDGPU::GLOBAL_STORE_DWORDX2, 0},
  }));
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
    // Drain doesn't change record wait values.
    EXPECT_TRUE(StoreCnt.hasRecords({
        {AMDGPU::GLOBAL_STORE_DWORDX2, 1},
        {AMDGPU::GLOBAL_STORE_DWORD, 0},
    }));
  }

  // Draining a counter does not affect other counters.
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    EXPECT_EQ(LoadCnt.getCount(), 1u);
    EXPECT_EQ(LoadCnt.size(), 1u);
  }

  // Draining above the current count is a no-op.
  ET.drain(AMDGPU::STORE_CNT, 5);
  {
    auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
    EXPECT_EQ(StoreCnt.getCount(), 2u);
    EXPECT_EQ(StoreCnt.size(), 2u);
  }

  // Full drain.
  ET.drain(AMDGPU::STORE_CNT);
  EXPECT_TRUE(TrackerRecordsChecker(ET, AMDGPU::STORE_CNT).unused());
  EXPECT_FALSE(ET.getPendingEvents(AMDGPU::STORE_CNT));
}

/// Check cases where a block loops back on itself.
TEST_F(AMDGPUGFX12EventTrackingTest, SelfPredecessor) {
  StringRef MIR = R"(
name:            SelfPredecessor
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
  MachineFunction &MF = getMF("SelfPredecessor");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);

  // Iterate twice
  visitAll(BB0);
  auto &ET = visitAll(BB0);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_EQ(LoadCnt.getCount(), 2u);
  EXPECT_TRUE(LoadCnt.hasRecords({
      {AMDGPU::GLOBAL_LOAD_DWORD, 1},
      {AMDGPU::GLOBAL_LOAD_DWORD, 0},
  }));

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 2u);
  EXPECT_TRUE(DsCnt.hasRecords({
      {AMDGPU::DS_READ_B32_gfx9, 1},
      {AMDGPU::DS_READ_B32_gfx9, 0},
  }));

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_TRUE(StoreCnt.hasRecords({
      {AMDGPU::GLOBAL_STORE_DWORDX2, 1},
      {AMDGPU::GLOBAL_STORE_DWORDX2, 0},
  }));
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
  EXPECT_TRUE(LoadCnt.hasRecords({{AMDGPU::GLOBAL_LOAD_DWORD, 0}}));

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_TRUE(DsCnt.hasRecords({{AMDGPU::DS_READ_B32_gfx9, 0}}));

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_TRUE(StoreCnt.hasRecords({
      {AMDGPU::GLOBAL_STORE_DWORD, 1},
      {AMDGPU::GLOBAL_STORE_DWORDX2, 0},
  }));
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
  EXPECT_TRUE(LoadCnt.hasRecords({{AMDGPU::GLOBAL_LOAD_DWORD, 0}}));

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_TRUE(DsCnt.hasRecords({{AMDGPU::DS_READ_B32_gfx9, 0}}));

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 2u);
  EXPECT_TRUE(StoreCnt.hasRecords({
      {AMDGPU::GLOBAL_STORE_DWORD, 1},
      {AMDGPU::GLOBAL_STORE_DWORDX2, 0},
  }));
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
  EXPECT_TRUE(LoadCnt.hasRecords({{AMDGPU::GLOBAL_LOAD_DWORD, 0}}));

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_TRUE(DsCnt.hasRecords({{AMDGPU::DS_READ_B32_gfx9, 0}}));

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  // Count is 1 because we have 1 event max across all predecessors.
  EXPECT_EQ(StoreCnt.getCount(), 1u);
  // Each predecessor contributes its store with a wait value of 0.
  EXPECT_TRUE(StoreCnt.hasRecords({
      {AMDGPU::GLOBAL_STORE_DWORD, 0},   // From bb.0.
      {AMDGPU::GLOBAL_STORE_DWORDX2, 0}, // From bb.1.
  }));
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
  EXPECT_TRUE(LoadCnt.hasRecords({{AMDGPU::GLOBAL_LOAD_DWORD, 0}}));

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_EQ(DsCnt.getCount(), 1u);
  EXPECT_TRUE(DsCnt.hasRecords({{AMDGPU::DS_READ_B32_gfx9, 0}}));

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);
  EXPECT_EQ(StoreCnt.getCount(), 1u);
  EXPECT_TRUE(StoreCnt.hasRecords({{AMDGPU::GLOBAL_STORE_DWORD, 0}}));
}

/// Asymetrical diamond
///   - bb0 has two stores
///   - bb1 adds another store without any waits.
///   - bb2 adds a store and waits on the two stores from bb0 afterwards
///
/// The timeline will be:
///   - Stores from bb0 exist with wait values of 1/2
///   - The added store from bb1 exists with a wait value of 0
///   - The added store from bb2 exists with a wait value of 0
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
  visitAll(
      BB2,
      /*AfterVisit=*/[&](EventTracker &ET) { ET.drain(AMDGPU::STORE_CNT, 1); });
  auto &ET = visitAll(BB3);

  auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
  EXPECT_TRUE(LoadCnt.unused());

  auto DsCnt = TrackerRecordsChecker(ET, AMDGPU::DS_CNT);
  EXPECT_TRUE(DsCnt.unused());

  auto ExpCnt = TrackerRecordsChecker(ET, AMDGPU::EXP_CNT);
  EXPECT_TRUE(ExpCnt.unused());

  auto StoreCnt = TrackerRecordsChecker(ET, AMDGPU::STORE_CNT);

  EXPECT_EQ(StoreCnt.getCount(), 3u);
  EXPECT_TRUE(StoreCnt.hasRecords({
      {AMDGPU::GLOBAL_STORE_DWORD, 2, &BB0},
      {AMDGPU::GLOBAL_STORE_DWORDX2, 1},
      {AMDGPU::GLOBAL_STORE_DWORD, 0, &BB1},
      {AMDGPU::GLOBAL_STORE_DWORD, 0, &BB2},
  }));
}

/// Asymetrical diamond
///   - bb0 has one store
///   - bb1 just falls through
///   - bb2 adds 1 more store.
///
/// The timeline will showcase how the value of a counter can be different from
/// the content of the timeline.
///   - The timeline will have all records with a wait value of 0.
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
  EXPECT_TRUE(StoreCnt.hasRecords({
      {AMDGPU::GLOBAL_STORE_DWORD, 0, &BB0},
      {AMDGPU::GLOBAL_STORE_DWORD, 0, &BB2},
  }));
}

/// Check that the count of a counter stops at its limit minus 1, while the
/// timeline keeps growing and record wait values keep increasing.
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

  EventTracker &ET = enterBlock(BB0);
  const AMDGPUInstCounter &LoadIC = getCounter(AMDGPU::LOAD_CNT, Counters);
  ASSERT_TRUE(LoadIC.hasLimit());
  const unsigned Limit = LoadIC.getLimit();
  ASSERT_GT(Limit, 1u);
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
  // still increment the wait value of existing records.
  constexpr unsigned Extra = 5;
  for (unsigned I = 0; I < Extra; ++I)
    ET.record(Load, Ev);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Limit - 1);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));

  const unsigned NumRecords = Limit - 1 + Extra;
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    ASSERT_EQ(LoadCnt.size(), NumRecords);
    EXPECT_EQ(LoadCnt.front().WaitValue, NumRecords - 1);
    EXPECT_EQ(LoadCnt.back().WaitValue, 0u);
    EXPECT_GT(LoadCnt.front().WaitValue, LoadCnt.getCount());
  }

  // Other counters are unaffected.
  EXPECT_TRUE(TrackerRecordsChecker(ET, AMDGPU::STORE_CNT).unused());
  EXPECT_FALSE(ET.isCapped(AMDGPU::STORE_CNT));

  // A partial drain uncaps the counter and removes all records at or above the
  // drained wait value.
  ET.drain(AMDGPU::LOAD_CNT, 3);
  EXPECT_FALSE(ET.isCapped(AMDGPU::LOAD_CNT));
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    EXPECT_EQ(LoadCnt.getCount(), 3u);
    EXPECT_EQ(LoadCnt.size(), 3u);
  }

  // The counter can be capped again afterwards.
  for (unsigned I = 0; I < Limit; ++I)
    ET.record(Load, Ev);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), Limit - 1);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));
}

/// Check that drainCappedRecords only acts on capped counters, removes exactly
/// the records whose wait value is at or above the cap (Limit - 1), and leaves
/// the count and the younger records untouched.
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

  EventTracker &ET = enterBlock(BB0);
  const unsigned Limit = getCounter(AMDGPU::LOAD_CNT, Counters).getLimit();
  const unsigned Cap = Limit - 1;
  ASSERT_GT(Limit, 2u);
  const SingleHWEvent Ev = SingleHWEvent::encode(HWEvents::VMEM_READ_ACCESS);

  // Not capped: nothing is removed.
  for (unsigned I = 0; I < 3; ++I)
    ET.record(Load, Ev);
  ASSERT_FALSE(ET.isCapped(AMDGPU::LOAD_CNT));
  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    EXPECT_EQ(LoadCnt.getCount(), 3u);
    EXPECT_EQ(LoadCnt.size(), 3u);
  }

  // Capped, with Extra records at or above the cap.
  constexpr unsigned Extra = 4;
  for (unsigned I = 3; I < Cap + Extra; ++I)
    ET.record(Load, Ev);
  ASSERT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));
  ASSERT_EQ(TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT).size(), Cap + Extra);

  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    // The hardware counter stays saturated: the count is not lowered.
    EXPECT_EQ(LoadCnt.getCount(), Cap);
    ASSERT_EQ(LoadCnt.size(), Cap);
    EXPECT_EQ(LoadCnt.front().WaitValue, Cap - 1);
    EXPECT_EQ(LoadCnt.back().WaitValue, 0u);
  }

  // Idempotent.
  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  EXPECT_EQ(TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT).size(), Cap);

  // One more event brings the oldest record's wait value to the cap; it is
  // removed again.
  ET.record(Load, Ev);
  EXPECT_EQ(TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT).front().WaitValue, Cap);
  ET.drainCappedRecords(AMDGPU::LOAD_CNT);
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    ASSERT_EQ(LoadCnt.size(), Cap);
    EXPECT_EQ(LoadCnt.front().WaitValue, Cap - 1);
  }

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

  EventTracker &ET = enterBlock(BB0);
  const unsigned Cap = getCounter(AMDGPU::LOAD_CNT, Counters).getLimit() - 1;
  const SingleHWEvent Ev = SingleHWEvent::encode(HWEvents::VMEM_READ_ACCESS);
  ET.record(Load, Ev);
  ET.record(Load, Ev);
  ASSERT_EQ(ET.count(AMDGPU::LOAD_CNT), 2u);

  EXPECT_TRUE(ET.widenCount(AMDGPU::LOAD_CNT));
  EXPECT_TRUE(ET.isCapped(AMDGPU::LOAD_CNT));
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    EXPECT_EQ(LoadCnt.getCount(), Cap);
    EXPECT_TRUE(LoadCnt.hasRecords({
        {AMDGPU::GLOBAL_LOAD_DWORD, 1},
        {AMDGPU::GLOBAL_LOAD_DWORD, 0},
    }));
  }

  // Widening twice is a no-op; recording keeps the count at the cap.
  EXPECT_TRUE(ET.widenCount(AMDGPU::LOAD_CNT));
  ET.record(Load, Ev);
  {
    auto LoadCnt = TrackerRecordsChecker(ET, AMDGPU::LOAD_CNT);
    EXPECT_EQ(LoadCnt.getCount(), Cap);
    EXPECT_EQ(LoadCnt.size(), 3u);
  }

  // A drain still lowers a widened count.
  ET.drain(AMDGPU::LOAD_CNT, 1);
  EXPECT_EQ(ET.count(AMDGPU::LOAD_CNT), 1u);
  EXPECT_FALSE(ET.isCapped(AMDGPU::LOAD_CNT));

  // TENSOR_CNT does not exist on gfx12.00: nothing to widen.
  EXPECT_FALSE(ET.widenCount(AMDGPU::TENSOR_CNT));
  EXPECT_EQ(ET.count(AMDGPU::TENSOR_CNT), 0u);
}

/// Two loads in bb.0, then a diamond: bb.0 -> {bb.1, bb.2} -> bb.3.
constexpr const char *DiamondMIR = R"(
name:            Diamond
body:             |
  bb.0:
    liveins: $vgpr4_vgpr5, $vgpr6_vgpr7, $scc
    $vgpr4 = GLOBAL_LOAD_DWORD $vgpr4_vgpr5, 0, 0, implicit $exec
    $vgpr6 = GLOBAL_LOAD_DWORD $vgpr6_vgpr7, 0, 0, implicit $exec
    S_CBRANCH_SCC1 %bb.2, implicit $scc
    S_BRANCH %bb.1

  bb.1:
    S_BRANCH %bb.3

  bb.2:
    S_BRANCH %bb.3

  bb.3:
    S_ENDPGM 0
...
)";

/// markIndeterminate widens the count. A partial drain keeps the flag; only a
/// drain to 0 clears it.
TEST_F(AMDGPUGFX12EventTrackingTest, IndeterminateAndDrain) {
  ASSERT_TRUE(parseMIR(DiamondMIR));
  MachineFunction &MF = getMF("Diamond");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineInstr &Load = BB0.front();

  EventTracker &ET = enterBlock(BB0);
  const unsigned Cap = getCounter(AMDGPU::STORE_CNT, Counters).getLimit() - 1;

  // Indeterminate with an empty timeline (e.g. unknown stores at entry).
  ET.markIndeterminate(AMDGPU::STORE_CNT);
  EXPECT_TRUE(ET.isIndeterminate(AMDGPU::STORE_CNT));
  EXPECT_EQ(ET.count(AMDGPU::STORE_CNT), Cap);
  EXPECT_TRUE(TrackerRecordsChecker(ET, AMDGPU::STORE_CNT).empty());

  ET.record(Load, SingleHWEvent::encode(HWEvents::VMEM_WRITE_ACCESS));
  EXPECT_EQ(ET.count(AMDGPU::STORE_CNT), Cap);

  ET.drain(AMDGPU::STORE_CNT, 1);
  EXPECT_TRUE(ET.isIndeterminate(AMDGPU::STORE_CNT));

  ET.drain(AMDGPU::STORE_CNT, 0);
  EXPECT_FALSE(ET.isIndeterminate(AMDGPU::STORE_CNT));
  EXPECT_TRUE(TrackerRecordsChecker(ET, AMDGPU::STORE_CNT).unused());
  EXPECT_EQ(ET.getPendingEvents(AMDGPU::STORE_CNT), HWEvents());
}

/// The cached pending events follow record, partial drain, capped-record
/// pruning and joins.
TEST_F(AMDGPUGFX12EventTrackingTest, PendingEventsCache) {
  ASSERT_TRUE(parseMIR(DiamondMIR));
  MachineFunction &MF = getMF("Diamond");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineInstr &Load = BB0.front();

  EventTracker &ET = enterBlock(BB0);
  // STORE_CNT tracks two kinds; the MI does not matter to the tracker.
  ET.record(Load, SingleHWEvent::encode(HWEvents::SCRATCH_WRITE_ACCESS));
  ET.record(Load, SingleHWEvent::encode(HWEvents::VMEM_WRITE_ACCESS));
  EXPECT_EQ(ET.getPendingEvents(AMDGPU::STORE_CNT),
            HWEvents::SCRATCH_WRITE_ACCESS | HWEvents::VMEM_WRITE_ACCESS);

  // Partial drain removes the older (scratch) record.
  ET.drain(AMDGPU::STORE_CNT, 1);
  EXPECT_EQ(ET.getPendingEvents(AMDGPU::STORE_CNT),
            HWEvents::VMEM_WRITE_ACCESS);

  // Join into bb.1 rebuilds the cache.
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);
  EventTracker &ET1 = enterBlock(BB1);
  EXPECT_EQ(ET1.getPendingEvents(AMDGPU::STORE_CNT),
            HWEvents::VMEM_WRITE_ACCESS);
#if !defined(NDEBUG) || defined(EXPENSIVE_CHECKS)
  ET.verify();
  ET1.verify();
#endif
}

/// The indeterminate flag is sticky across joins: one predecessor in the
/// state is enough. It takes part in operator==.
TEST_F(AMDGPUGFX12EventTrackingTest, IndeterminatePropagatesThroughJoin) {
  ASSERT_TRUE(parseMIR(DiamondMIR));
  MachineFunction &MF = getMF("Diamond");
  MachineBasicBlock &BB0 = *MF.getBlockNumbered(0);
  MachineBasicBlock &BB1 = *MF.getBlockNumbered(1);
  MachineBasicBlock &BB2 = *MF.getBlockNumbered(2);
  MachineBasicBlock &BB3 = *MF.getBlockNumbered(3);

  visitAll(BB0);
  visitAll(BB1,
           [](EventTracker &ET) { ET.markIndeterminate(AMDGPU::STORE_CNT); });
  visitAll(BB2);
  EventTracker &ET3 = visitAll(BB3);

  EXPECT_FALSE(getTracker(BB2).isIndeterminate(AMDGPU::STORE_CNT));
  EXPECT_TRUE(ET3.isIndeterminate(AMDGPU::STORE_CNT));
  EXPECT_FALSE(ET3.isIndeterminate(AMDGPU::LOAD_CNT));
  // Count is the max over predecessors: the widened one.
  EXPECT_EQ(ET3.count(AMDGPU::STORE_CNT),
            getTracker(BB1).count(AMDGPU::STORE_CNT));

  // Two states that differ only by the flag are not equal.
  EventTracker A(BB1, Counters), B(BB1, Counters);
  A.markIndeterminate(AMDGPU::STORE_CNT);
  B.widenCount(AMDGPU::STORE_CNT);
  ASSERT_EQ(A.count(AMDGPU::STORE_CNT), B.count(AMDGPU::STORE_CNT));
  EXPECT_FALSE(A == B);
}

} // namespace
