//===- AMDGPUEventTracking.cpp ----------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "AMDGPUEventTracking.h"
#include "AMDGPUHWEvents.h"
#include "AMDGPUWaitcntUtils.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include <algorithm>
#include <limits>

#define DEBUG_TYPE "amdgpu-event-tracking"

using namespace llvm::AMDGPU::et_detail;

namespace llvm {

#ifndef NDEBUG
static cl::opt<bool> EventTrackerPrintAll(
    "amdgpu-event-tracker-print-all", cl::init(false),
    cl::desc("When using -debug, print the updated timeline every time a "
             "record is added or removed"));
#endif

namespace AMDGPU {

namespace {
/// Orders records of the same timeline by descending wait value (i.e.
/// ascending stamp). Ties are broken by kind, then by parent MBB number, so
/// that the order is deterministic.
static bool compareRecords(const RecordImpl &A, const RecordImpl &B) {
  if (A.Stamp != B.Stamp)
    return A.Stamp < B.Stamp;

  // Same wait value but different kind.
  unsigned AKindV = A.Kind.rawValue();
  unsigned BKindV = B.Kind.rawValue();
  if (AKindV != BKindV)
    return AKindV > BKindV;

  const MachineInstr *AMI = A.MI;
  const MachineInstr *BMI = B.MI;
  if (AMI == BMI)
    return false;

  // Same wait value/kind but MIs are in different MBBs: the one in the MBB with
  // the lower number comes first.
  const MachineBasicBlock *Bbb = BMI->getParent();
  const MachineBasicBlock *Abb = AMI->getParent();
  if (Abb != Bbb)
    return Abb->getNumber() < Bbb->getNumber();

  llvm_unreachable("We cannot have two distinct instructions from the same "
                   "MBB, with the same wait value and the same event kind!");
}

static HWEvents calcPendingEvents(const CounterData &CD) {
  HWEvents Res;
  for (const RecordImpl &R : CD.Timeline)
    Res |= R.Kind;
  return Res;
}

/// \returns true if \p A and \p B have the same records (MI, kind and wait
/// value) in the same order. The clocks of the two timelines may differ and
/// that is fine as the clock is just an implementation detail.
static bool timelinesEqual(const CounterData &A, const CounterData &B) {
  return equal(A.Timeline, B.Timeline,
               [&](const RecordImpl &RA, const RecordImpl &RB) {
                 return RA.MI == RB.MI && RA.Kind == RB.Kind &&
                        A.waitOf(RA) == B.waitOf(RB);
               });
}

static void printCounterData(raw_ostream &OS, const CounterData &CD,
                             unsigned Indent = 0) {
  assert(CD.isTracked());
  OS.indent(Indent) << CD.IC->getName() << " (Count=" << CD.Count
                    << ", Timeline=" << CD.Timeline.size()
                    << ", Indeterminate=" << CD.IsIndeterminate << ")\n";
  for (const RecordImpl &CR : CD.Timeline) {
    OS.indent(Indent + 2);
    EventTrackerRecord(CR, CD).print(OS);
  }
}

} // namespace

void EventTrackerRecord::print(raw_ostream &OS, bool PrintMI,
                               unsigned Indent) const {
  OS.indent(Indent) << "Record Kind=" << getKind()
                    << " WaitValue=" << getWaitValue() << ": ";
  if (PrintMI && getMI())
    OS << *getMI();
  else
    OS << "MI@" << (void *)getMI() << '\n';
}

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
LLVM_DUMP_METHOD void EventTrackerRecord::dump() const {
  dbgs() << '\n';
  print(dbgs(), /*PrintMI=*/true);
  dbgs() << '\n';
}
#endif

EventTracker::EventTracker(const MachineBasicBlock &MBB,
                           ArrayRef<AMDGPUInstCounter> CounterInfos)
    : MBB(&MBB) {
  /// TODO: Should be more compact; use the size of CounterInfos instead.
  /// All addressing of the Counters array needs to change.
  Counters.resize(NUM_INST_CNTS);
  for (const AMDGPUInstCounter &IC : CounterInfos)
    Counters[IC.getType()].IC = &IC;
}

void EventTracker::enterBlock(ArrayRef<const EventTracker *> Preds) {
  LLVM_DEBUG(dbgs() << "\n[EventTracker] Entering ";
             MBB->printAsOperand(dbgs()); dbgs() << '\n');
  assert(Preds.size() == MBB->pred_size() &&
         "Expected one tracker per predecessor");
  recordIncomings(Preds);
}

void EventTracker::record(MachineInstr &MI, SingleHWEvent Event) {
  LLVM_DEBUG(dbgs() << "[EventTracker] Recording " << Event << ": " << MI);

  [[maybe_unused]] bool FoundMatch = false;
  for (CounterData &CD : Counters) {
    if (!CD.isTracked() || !CD.IC->getEvents().contains(Event))
      continue;

    FoundMatch = true;
    if (!isCapped(CD))
      ++CD.Count;

    // Ticking the clock ages every pre-existing record by one.
    assert(CD.Clock != std::numeric_limits<uint32_t>::max() &&
           "Clock overflow");
    ++CD.Clock;

    // NOTE: Unlike recordIncomings, we do not merge with a previous record that
    // has the same identity (MI+Kind). Having two such records is fine: one is
    // carried over from a backedge and the other is from a more recent
    // iteration.
    CD.Timeline.emplace_back(MI, Event, CD.Clock);

    CD.PendingEventsCache |= Event;

    LLVM_DEBUG(if (EventTrackerPrintAll) {
      dbgs().indent(2) << "Updated Timeline:\n";
      printCounterData(dbgs(), CD, /*Indent=*/4);
    });
  }

  assert(FoundMatch && "Event has no matching InstCounterType!");

#ifdef EXPENSIVE_CHECKS
  verify();
#endif
}

bool EventTracker::widenCount(InstCounterType T) {
  CounterData &CD = Counters[T];
  if (!CD.isTracked() || !CD.IC->hasLimit())
    return false;
  LLVM_DEBUG(dbgs() << "[EventTracker] Widening " << CD.IC->getName() << "\n");
  CD.Count = CD.IC->getLimit() - 1;
  assert(isCapped(T));
  return true;
}

void EventTracker::drain(InstCounterType T, unsigned N) {
  CounterData &CD = Counters[T];
  assert(CD.isTracked());
  LLVM_DEBUG(dbgs() << "[EventTracker] Drain " << getInstCounterName(T)
                    << " at " << N << '\n');

  // Fast path for clearing the counter.
  if (N == 0) {
    CD.Timeline.clear();
    CD.Count = 0;
    CD.Clock = 0;

    CD.IsIndeterminate = false;
  } else {
    CD.Count = std::min(CD.Count, N);

    // The timeline is sorted by descending wait value, so the records to
    // remove form a prefix.
    auto *RmEnd = find_if(
        CD.Timeline, [&](const RecordImpl &R) { return CD.waitOf(R) < N; });
    LLVM_DEBUG(
        for (const RecordImpl &R : make_range(CD.Timeline.begin(), RmEnd)) {
          dbgs() << "  | Removing ";
          EventTrackerRecord(R, CD).print(dbgs());
        });
    CD.Timeline.erase(CD.Timeline.begin(), RmEnd);

    LLVM_DEBUG(dbgs() << "  | => Updated Count:" << CD.Count << '\n');

    LLVM_DEBUG(if (EventTrackerPrintAll) {
      dbgs().indent(2) << "Updated Timeline:\n";
      printCounterData(dbgs(), CD, /*Indent=*/4);
    });
  }

  CD.PendingEventsCache = calcPendingEvents(CD);

#ifdef EXPENSIVE_CHECKS
  verify();
#endif
}

void EventTracker::markIndeterminate(InstCounterType T) {
  CounterData &CD = Counters[T];
  assert(CD.isTracked());

  LLVM_DEBUG(dbgs() << "[EventTracker] Marking as indeterminate: "
                    << CD.IC->getName() << "\n");
  CD.IsIndeterminate = true;
  widenCount(T);
}

bool EventTracker::isIndeterminate(InstCounterType T) const {
  return Counters[T].IsIndeterminate;
}

bool EventTracker::isTimelineIdentical(InstCounterType T,
                                       const EventTracker &Other) const {
  assert(Counters.size() == Other.Counters.size());
  assert(Counters[T].isTracked());
  assert(Counters[T].IC == Other.Counters[T].IC);
  return timelinesEqual(Counters[T], Other.Counters[T]);
}

bool EventTracker::operator==(const EventTracker &Other) const {
  assert(Counters.size() == Other.Counters.size());
  // Timelines are kept sorted by compareRecords, which is a strict total order
  // on the records of a timeline (verify() rejects duplicate identities with
  // the same wait value), so an element-wise compare is exact.
  for (const auto &[A, B] : zip_equal(Counters, Other.Counters)) {
    assert(A.IC == B.IC && "comparing trackers with different counters");
    if (A.Count != B.Count || !timelinesEqual(A, B) ||
        A.IsIndeterminate != B.IsIndeterminate)
      return false;
  }
  return true;
}

unsigned EventTracker::count(InstCounterType T) const {
  return Counters[T].Count;
}

HWEvents EventTracker::getPendingEvents(InstCounterType T) const {
  return Counters[T].PendingEventsCache;
}

void EventTracker::drainCappedRecords(InstCounterType T) {
  CounterData &CD = Counters[T];
  assert(CD.isTracked());

  if (!isCapped(CD))
    return;

  // TL is sorted, so iterate from the start to see oldest records, then bail
  // early.
  unsigned NumAboveCap = 0;
  unsigned Cap = CD.IC->getLimit() - 1;
  for (const RecordImpl &R : CD.Timeline) {
    if (CD.waitOf(R) >= Cap)
      ++NumAboveCap;
    else
      break;
  }

  if (NumAboveCap > 0) {
    CD.Timeline.erase(CD.Timeline.begin(), CD.Timeline.begin() + NumAboveCap);
    CD.PendingEventsCache = calcPendingEvents(CD);
  }
}

iterator_range<EventTracker::TimelineIt>
EventTracker::getTimeline(InstCounterType T) const {
  return map_range(Counters[T].Timeline,
                   EventTrackerRecordMapper{&Counters[T]});
}

#if !defined(NDEBUG) || defined(EXPENSIVE_CHECKS)
void EventTracker::verify() const {
  if (!MBB)
    llvm_unreachable("EventTracker has no MBB!");

  for (const CounterData &C : Counters) {
    if (!C.isTracked())
      continue;

    const auto OnError = [&]() {
      dbgs() << "EventTracker verification error\n";
      printCounterData(dbgs(), C);
    };

    // Check some basic invariants:
    //  - The stamp of a record cannot exceed the clock.
    //  - The wait value of a record cannot exceed the value of the counter.
    //  - We cannot have two records with the same identity and the same wait
    //    value, e.g. two VMEM_READ_ACCESS records for the same instruction
    //    with the same wait value. `recordIncomings` merges based on identity,
    //    and `record` increments the wait value of all pre-existing records
    //    before inserting a new one.
    DenseSet<std::pair<RecordIdentity, unsigned>> RecIdentityCheck;
    for (const RecordImpl &CR : C.Timeline) {
      EventTrackerRecord ETR(CR, C);
      if (CR.Stamp > C.Clock) {
        OnError();
        dbgs() << "Concerning Record: Stamp=" << CR.Stamp
               << " Clock=" << C.Clock << '\n';
        llvm_unreachable("record stamp is ahead of the clock");
      }

      if (C.waitOf(CR) > C.Count && !isCapped(C)) {
        OnError();
        dbgs() << "Concerning Record:";
        ETR.print(dbgs());
        llvm_unreachable("record wait value is out of range");
      }

      RecordIdentity CRIdent = {CR.MI, CR.Kind};
      auto [It, Inserted] = RecIdentityCheck.insert({CRIdent, CR.Stamp});
      if (!Inserted) {
        OnError();
        dbgs() << "Concerning Record:";
        ETR.print(dbgs());
        llvm_unreachable("The timeline cannot have two records with the same "
                         "MachineInstr, Kind and wait value at the same "
                         "time!");
      }
    }

    // A pending record implies a non-zero count.
    if (!C.Timeline.empty() && C.Count == 0) {
      OnError();
      llvm_unreachable("records are pending but the count is zero");
    }

    // Check that the timeline is sorted.
    if (!is_sorted(C.Timeline, compareRecords)) {
      OnError();
      llvm_unreachable("live records are not sorted!");
    }

    HWEvents PendingEvents = calcPendingEvents(C);
    if (PendingEvents != C.PendingEventsCache) {
      OnError();
      dbgs() << "Current Pending Events: " << PendingEvents << "\n";
      dbgs() << "Cached Pending Events: " << C.PendingEventsCache << "\n";
      llvm_unreachable("pending events cache is incorrect!");
    }
  }
}
#endif

void EventTracker::print(raw_ostream &OS, bool IgnoreEmpty,
                         unsigned Indent) const {
  OS.indent(Indent) << "EventTracker for ";
  MBB->printAsOperand(OS);
  OS << ':';
  if (IgnoreEmpty) {
    if (all_of(Counters, [](const CounterData &CD) { return CD.Count == 0; })) {
      OS << " (empty)\n";
      return;
    }
  }

  OS << '\n';
  for (const CounterData &C : Counters) {
    if (!C.isTracked() || (IgnoreEmpty && C.Count == 0))
      continue;
    printCounterData(OS, C, Indent + 2);
  }
}

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
LLVM_DUMP_METHOD void EventTracker::dump() const {
  dbgs() << '\n';
  print(dbgs());
  dbgs() << '\n';
}
#endif

bool EventTracker::isCapped(const CounterData &CD) const {
  assert(CD.isTracked());
  if (!CD.IC->hasLimit())
    return false;
  assert(CD.Count < CD.IC->getLimit() && "Counter already overflowed!");
  return (CD.Count + 1) >= CD.IC->getLimit();
}

void EventTracker::recordIncomings(ArrayRef<const EventTracker *> Preds) {
  LLVM_DEBUG(if (!Preds.empty()) {
    dbgs() << "[EventTracker] Recording incoming events (merge) from "
              "predecessors:\n";
    for (const EventTracker *Pred : Preds) {
      Pred->print(dbgs(), /*IgnoreEmpty=*/true, /*Indent=*/2);
    }
  });

  // Iterate over all counters that are available to us.
  for (CounterData &OldCData : Counters) {
    if (!OldCData.isTracked()) {
      // FIXME: We should assert that the Preds also don't track this counter.
      continue;
    }

    // Build the merged state separately, as `this` may be one of the Preds.
    CounterData CData;
    CData.IC = OldCData.IC;
    DenseMap<RecordIdentity, unsigned> Acc;
    // Upper bound of the merged wait values. Records are rebased on it below.
    uint32_t LargestWait = 0;

    for (const EventTracker *Pred : Preds) {
      const CounterData &PredCData = Pred->Counters[CData.IC->getType()];
      assert(PredCData.IC == OldCData.IC);

      // The merged count is the max across predecessors.
      CData.Count = std::max(CData.Count, PredCData.Count);

      CData.IsIndeterminate |= PredCData.IsIndeterminate;

      for (const RecordImpl &PredEntry : PredCData.Timeline) {
        // At a join, collapse records from all predecessors with the same
        // identity (MI+Kind) into a single record whose wait value is the
        // minimum across predecessors (i.e. the most conservative one).
        RecordIdentity Key = {PredEntry.MI, PredEntry.Kind};
        uint32_t Wait = PredCData.waitOf(PredEntry);
        LargestWait = std::max(LargestWait, Wait);
        auto [It, Inserted] = Acc.try_emplace(Key, Wait);
        if (!Inserted) {
          auto &AccVal = It->second;
          AccVal = std::min(AccVal, Wait);
        }
      }
    }

    // Rebase all records on a fresh clock. LargestWait is >= every merged
    // wait value, so no stamp underflows. The oldest stamp is not necessarily
    // 0 (the max is taken before the per-identity min), which is fine as
    // stamps are only meaningful relative to the clock.
    CData.Clock = LargestWait;
    for (const auto &[RecIdent, RecWait] : Acc)
      CData.Timeline.emplace_back(*RecIdent.first, RecIdent.second,
                                  CData.Clock - RecWait);

    CData.PendingEventsCache = calcPendingEvents(CData);

    // Sort records by descending wait value for consistent iteration.
    stable_sort(CData.Timeline, compareRecords);

    OldCData = std::move(CData);
  }

#ifdef EXPENSIVE_CHECKS
  verify();
#endif

  LLVM_DEBUG(if (!Preds.empty()) {
    dbgs() << "[EventTracker] Timeline after recording incomings:\n";
    print(dbgs(), /*IgnoreEmpty=*/true, /*Indent=*/2);
  });
}

} // namespace AMDGPU

} // namespace llvm
