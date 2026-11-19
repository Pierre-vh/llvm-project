//===- AMDGPUEventTracking.h ------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// Minimal API to track in-flight events that increment hardware instruction
/// counters (\ref InstCounterType, e.g. LOAD_CNT, DS_CNT). Intended as a
/// building block for waitcnt insertion: it tracks which events are
/// outstanding and how far back they are, but does not directly compute waits.
///
///   - \ref CounterInfo: constant per-counter description (events, limit).
///   - \ref EventTrackerRecord: a view of a (MachineInstr, SingleHWEvent) pair
///     with a wait value: the largest N such that waiting for the counter to
///     reach N or lower guarantees that the event has completed.
///   - \ref EventTracker: per-MBB state; for each counter, a count and a
///     timeline of records sorted by descending wait value.
///     Driven by the client during an RPO dataflow analysis:
///     \ref EventTracker::enterBlock merges predecessor state,
///     \ref EventTracker::record appends new events and increments the wait
///     value of all pre-existing events, and \ref EventTracker::drain removes
///     events that are guaranteed to have completed after a wait.
///
/// This is a low-level API. It can be used directly for trivial waitcnt
/// calculation (e.g. wait on a specific MI), but the typical usage is for
/// clients to build helpers on top of it that combine the timeline with
/// additional information (e.g. alias analysis, subtarget-specific behavior)
/// to compute more precise waits.
///
/// TODO For Long Term:
///   - Fix the `Counter` array, it's really not ideal. Find a cleaner way to
///     store the counters, handling holes in the AMDGPUCounterInfo map.
///     Possibilities are:
///       - Avoid holes entirely (not nice)
///       - Always reason with AMDGPUInstCounterInfo& instead of what we have
///         now (part one, part other)
///         Maybe in that case require the tracker to pass a MachineFunctionInfo
///         or some kind of context object to enforce we always pass the right
///         AMDGPUInstCounterInfo ptrs?
///       - Keep vector dense, linear scan to find T
///         - Tricky, handle differences in IC
///       - Use unique_ptr in vector so holes don't matter
///         - Need deep copy op which is ugly.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_AMDGPU_AMDGPUEVENTTRACKING_H
#define LLVM_LIB_TARGET_AMDGPU_AMDGPUEVENTTRACKING_H

#include "AMDGPUHWEvents.h"
#include "AMDGPUWaitcntUtils.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/iterator_range.h"

namespace llvm {
class raw_ostream;
class MachineBasicBlock;

namespace AMDGPU {
namespace et_detail {

/// Storage structure for individual records of events in the EventTracker.
struct RecordImpl {
  RecordImpl(MachineInstr &MI, SingleHWEvent Kind,
             unsigned MaxWaitToComplete = 0)
      : MI(&MI), Kind(Kind), MaxWaitToComplete(MaxWaitToComplete) {}

  bool operator==(const RecordImpl &Other) const {
    return MI == Other.MI && Kind == Other.Kind &&
           MaxWaitToComplete == Other.MaxWaitToComplete;
  }

  MachineInstr *MI = nullptr;
  SingleHWEvent Kind;

  /// Largest wait value N such that waiting for the counter to reach N or
  /// lower guarantees this event has completed. Equivalently, the number of
  /// younger events of the same counter that may still be in flight.
  /// Conservative across merged paths (the minimum is kept at joins).
  unsigned MaxWaitToComplete = 0;
};

/// Storage structure for all information pertaining to one InstCounterType in
/// EventTracker.
struct CounterData {
  using TimelineTy = SmallVector<RecordImpl, 16>;

  /// Info about the counter. If nullptr, then this CounterData is invalid and
  /// represents a counter not being tracked.
  const AMDGPUInstCounter *IC = nullptr;

  TimelineTy Timeline;

  /// The current value of the counter. This is a max (upper bound) across
  /// all possible execution paths at runtime. It cannot be inferred from the
  /// Timeline alone and is thus a separate tracking domain.
  uint32_t Count = 0;

  /// Cached pending events. Updated when recording new events, recomputed
  /// whenever events are removed.
  HWEvents PendingEventsCache;

  bool IsIndeterminate = false;

  bool isTracked() const { return IC != nullptr; }
};
} // namespace et_detail

/// A view into a record within the \ref EventTracker's timeline
/// for one \ref InstCounterType.
class EventTrackerRecord {
public:
  explicit EventTrackerRecord(const et_detail::RecordImpl &Record)
      : Record(&Record) {}

  /// \returns the MachineInstr that originated this record.
  MachineInstr *getMI() const { return Record->MI; }

  /// \returns the kind of record this is, as a \ref SingleHWEvent.
  SingleHWEvent getKind() const { return Record->Kind; }

  /// \returns the largest wait value N such that waiting for the counter to
  /// reach N or lower guarantees this record's event has completed.
  /// Conservative across merged paths.
  uint32_t getWaitValue() const { return Record->MaxWaitToComplete; }

  void print(raw_ostream &OS, bool PrintMI = true, unsigned Indent = 0) const;

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
  LLVM_DUMP_METHOD void dump() const;
#endif

  bool operator==(const EventTrackerRecord &Other) const {
    return *Record == *Other.Record;
  }

private:
  const et_detail::RecordImpl *Record = nullptr;
};

/// Per-MBB tracking context which tracks the current value (count) of each
/// instruction counter and the timeline of \ref EventTrackerRecord
/// for each instruction counter.
///
/// This class is only responsible for tracking records for every
/// \ref InstCounterType. It does not deal with calculating the waitcnts needed,
/// or doing more advanced reasoning over the timeline for specific queries
/// (e.g. finding an aliasing store). These responsibilities are left to
/// helpers built on top of this class (see the file header).
///
/// It is intended to be used during a reverse postorder dataflow analysis of a
/// function. The expected usage pattern is to call
/// \ref EventTracker::enterBlock, then visit the MBB in instruction order, call
/// \ref EventTracker::record whenever an interesting event occurs, and call
/// \ref EventTracker::drain whenever a wait on a counter is performed.
/// In between those operations, the user of the class can use all other methods
/// to query the current state of a counter, iterate its timeline, etc.
///
/// Allocation/storage/mapping of EventTrackers to MBBs is left to the user of
/// the class.
///
/// Whenever the dataflow analysis re-visits a block, the user of the class is
/// expected to re-use the same EventTracker (which is required in case the MBB
/// is its own predecessor) and call \ref EventTracker::enterBlock again, which
/// clears the state and re-imports all incoming state.
class EventTracker {
  using RecordImpl = et_detail::RecordImpl;
  using CounterData = et_detail::CounterData;
  using RecordIdentity = std::pair<MachineInstr *, SingleHWEvent>;

  struct EventTrackerRecordMapper {
    EventTrackerRecord operator()(const RecordImpl &RI) const {
      return EventTrackerRecord(RI);
    }
  };

public:
  using TimelineIt = mapped_iterator<CounterData::TimelineTy::const_iterator,
                                     EventTrackerRecordMapper>;

  /// \p MBB is the MachineBasicBlock for this tracker.
  /// \p CounterInfos describes the available \ref InstCounterType. Counters
  /// unavailable on the target can be omitted (the InstCounterType value does
  /// not have to match the index in \p CounterInfos)
  EventTracker(const MachineBasicBlock &MBB,
               ArrayRef<AMDGPUInstCounter> CounterInfos);

  /// Prepare this EventTracker for iteration through its basic block.
  ///
  /// Clears the current state and merges the state of the EventTrackers of
  /// predecessor MBBs. Records with the same identity (MachineInstr and
  /// SingleHWEvent) are merged and only the lowest wait value is kept.
  /// Counts are merged by taking the maximum.
  ///
  /// \param Preds the EventTrackers of the predecessors of the MBB, in any
  /// order. May contain this EventTracker if the MBB is its own predecessor.
  void enterBlock(ArrayRef<const EventTracker *> Preds);

  /// Record an event of type \p Event at a MachineInstr \p MI, which will
  /// affect all counters that have \p Event in their event set.
  /// \pre \p Event belongs to at least one \ref InstCounterType.
  void record(MachineInstr &MI, SingleHWEvent Event);

  /// Set the \ref count of \p T to its limit ( \ref isCapped returns true).
  /// The timeline is unaffected. If the counter isn't tracked or has no limit,
  /// does nothing.
  /// \returns true if the count was widened, false otherwise.
  bool widenCount(InstCounterType T);

  /// \returns true if the \ref count of \p T is at its max (Limit of the
  /// counter minus 1), and new events do not increment the counter value
  /// anymore.
  bool isCapped(InstCounterType T) const { return isCapped(Counters[T]); }

  /// Drains the timeline of \p T such that:
  /// - The \ref count of \p T is no higher than \p N.
  /// - There are no records in the timeline with a wait value >= \p N.
  /// If \p N = 0, then \p T is no longer in the indeterminate state.
  void drain(InstCounterType T, unsigned N = 0);

  /// Mark \p T as being indeterminate, which means that we only track a subset
  /// of events.
  /// Implies \ref widenCount, only cleared by a \ref drain 0, and persists
  /// across joins.
  /// FIXME: I feel like this is a bit of a breach of the separation of
  /// concerns. We don't store OoO bit here but we store indeterminate because
  /// it's arbitrary/easier. Reevaluate that split. Either trim this and
  /// generalize it to just a system of abstract flags, or don't store it here?
  void markIndeterminate(InstCounterType T);

  /// \returns true if the counter \p T is in the indeterminate state.
  bool isIndeterminate(InstCounterType T) const;

  /// \returns a conservative estimate of the current value of the counter \p T
  /// (a maximum value across all possible CFG paths).
  unsigned count(InstCounterType T) const;

  /// \returns the set of pending HWEvents for \p T.
  HWEvents getPendingEvents(InstCounterType T) const;

  /// Drain all records of \p T that have a wait value >= the cap of \p T.
  void drainCappedRecords(InstCounterType T);

  /// \returns the current timeline for \p T, which contains all known in-flight
  /// (not drained) records. The timeline is always sorted by descending
  /// wait value (oldest first).
  /// The returned iterators are invalidated whenever the timeline changes (e.g.
  /// \ref record, \ref drain, \ref enterBlock).
  iterator_range<TimelineIt> getTimeline(InstCounterType T) const;

  /// \returns true if the timeline of \p T is identical (same records, same
  /// order) in this tracker and in \p Other.
  bool isTimelineIdentical(InstCounterType T, const EventTracker &Other) const;

  /// \returns true if \p Other tracks the same state: for every counter, the
  /// same count and the same timeline (records compared by MI, kind and wait
  /// value).
  /// The tracked MBB is not compared.
  bool operator==(const EventTracker &Other) const;

  /// Prints a dump of all internal tracking state of this class to the stream
  /// \p OS. If \p IgnoreEmpty is true, do not print counters with a count of 0.
  void print(raw_ostream &OS, bool IgnoreEmpty = false,
             unsigned Indent = 0) const;

#if !defined(NDEBUG) || defined(EXPENSIVE_CHECKS)
  /// Verifies that the invariants of this class hold.
  void verify() const;
#endif

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
  LLVM_DUMP_METHOD void dump() const;
#endif

private:
  bool isCapped(const CounterData &CD) const;

  /// Import all records from the predecessor trackers in \p Preds and
  /// reconcile divergence at joins.
  void recordIncomings(ArrayRef<const EventTracker *> Preds);

  const MachineBasicBlock *MBB;

  /// FIXME?: We can have CounterDatas in there with a nullptr IC, which means
  /// the counter is untracked. This wastes a bit of space but the added
  /// complexity of worrying about that space isn't worth it.
  SmallVector<CounterData, 0> Counters;
};

} // namespace AMDGPU

} // namespace llvm

#endif
