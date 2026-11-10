//===- AMDGPUNewInsertWaitcnts.cpp - Insert wait instructions -------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
///   Thoughts as I write this:
///     - I think there is even more opportunity to split things between files
///       here. e.g. all the stuff that computes Waitcnt values from State
///       could be in a separate class.
///       Consider putting everything into a separate folder so I can create
///       multiple files?
//
//===----------------------------------------------------------------------===//

#include "AMDGPUNewInsertWaitcnts.h"
#include "AMDGPU.h"
#include "AMDGPUEventTracking.h"
#include "AMDGPUHWEvents.h"
#include "AMDGPUMachineFunctionInfo.h"
#include "AMDGPUNewInsertWaitcntsUtils.h"
#include "AMDGPUWaitcntRewriter.h"
#include "GCNSubtarget.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachinePostDominators.h"
#include "llvm/InitializePasses.h"
#include "llvm/Target/TargetMachine.h"

using namespace llvm;
using namespace llvm::AMDGPU;
using namespace llvm::AMDGPU::eventtracking;

#define DEBUG_TYPE "amdgpu-new-insert-waitcnts"
#define PASS_NAME "AMDGPU New Insert Waitcnts"

STATISTIC(NumCounterWidened, "Number of counters widened in retreating MBBs");

namespace {

struct PassOptions {
  /// For each "retreating" MBB, set an iteration limit:
  /// When the limit is reached, we force-drain the MBB before its terminator.
  /// Using a limit of 0 forces the pass to do a conservative "one-shot"
  /// approach of waitcnt insertion.
  ///
  /// FIXME: Number demands an investigation.
  unsigned IterationLimitForRetreatingBlocks = 16;
  /// Global limit. This is multiplied by the number of blocks to visit.
  /// When the limit is reached, we force drain every future retreating MBB so
  /// their out state is empty.
  ///
  /// FIXME: Number demands an investigation.
  unsigned GlobalLimit = 32;
  /// Whether to run verify after apply.
  ///
  /// TODO: use CL opt for this?
  bool Verify = false;
};

struct State {
  State(const MachineBasicBlock &MBB, ArrayRef<AMDGPUInstCounter> Counters)
      : ET(MBB, Counters) {}

  EventTracker ET;

  // TODO: ASYNCMARK state goes here. It must take part in operator==
  // and the join.
  //  - Join is currently handled by the EventTracker. Does it mean this State
  //    will need to handle join in the future ? Can we find another way?
  //    Can EventTracker do it?

  bool operator==(const State &Other) const { return ET == Other.ET; }
};

class AMDGPUNewInsertWaitcnts {
public:
  AMDGPUNewInsertWaitcnts(MachineFunction &MF, MachineLoopInfo &MLI,
                          MachinePostDominatorTree &PDT, AAResults *AA)
      : MF(MF), AA(AA), ST(MF.getSubtarget<GCNSubtarget>()),
        MFI(*MF.getInfo<AMDGPUMachineFunctionInfo>()), TII(*ST.getInstrInfo()),
        TRI(*ST.getRegisterInfo()), MRI(MF.getRegInfo()),
        InstCounters(MFI.getInstCounters()), IV(getIsaVersion(ST.getCPU())),
        RPO(MF), LoopPreInfo(MF, MLI) {
    SmemCounter = getCounterForEvent(HWEvents::SMEM_ACCESS, InstCounters);

    EntryBlocksNeedWaits = !MFI.isEntryFunction() &&
                           !MF.getFunction().hasFnAttribute(Attribute::Naked);

    // SIW:172-173
    OptNone = MF.getFunction().hasOptNone() ||
              MF.getTarget().getOptLevel() == CodeGenOptLevel::None;

    IsTgSplit =
        ST.hasTgSplitSupport() && AMDGPU::isTgSplitEnabled(MF.getFunction());
    if (ST.hasExtendedWaitCounts()) {
      IsExpertMode = AMDGPU::isExpertSchedulingMode(ST, MF.getFunction());
    }
  }

  /// Runs the pass on the function. \returns true if the MIR changed.
  bool run();

private:
  /// Releases the VGPRs before the S_ENDPGM recorded in \p Sol, if the
  /// function wants it (see \ref getVGPRDeallocMode).
  /// \returns true if the MIR changed.
  bool insertVGPRDeallocs(const Solution &Sol);

  /// Computes the waits of every block into \p Sol without modifying the MIR.
  void solve(Solution &Sol);

  /// Emits the waits in \p Sol into the MIR, rewriting the preceding waits of
  /// each decision point.
  /// \returns true if the MIR changed.
  bool apply(const Solution &Sol);

  /// Checks that the emitted MIR satisfies every dependency (debug aid).
  void verify();

  /// Walks \p MBB from its in-state (rebuilt from the predecessors'
  /// \p OutStates) and leaves its out-state in \p OutStates. Blocks in
  /// \p ForceDrain are fully drained before their terminator. Decisions are
  /// recorded in \p Sol if non-null.
  void walkBlock(MachineBasicBlock &MBB,
                 DenseMap<const MachineBasicBlock *, State> &OutStates,
                 const DenseSet<const MachineBasicBlock *> &ForceDrain,
                 Solution *Sol);

  /// \param S the state of \p MBB before its terminator
  /// \param MBB a basic block which may be a loop preheader.
  /// \returns true if \p MBB is a loop preheader, and we must wait for all
  /// loads (LOADCNT/vmcnt) at the end of \p MBB.
  bool shouldFlushPreheader(const State &S, const MachineBasicBlock &MBB);

  /// \returns true if \p MI is S_ENDPGM or S_ENDPGM_SAVED.
  static bool isEndPgm(const MachineInstr &MI) {
    return MI.getOpcode() == AMDGPU::S_ENDPGM ||
           MI.getOpcode() == AMDGPU::S_ENDPGM_SAVED;
  }

  /// \returns true if sending the dealloc VGPRs message before an S_ENDPGM
  /// reached with state \p S is safe and useful: some store is in flight (the
  /// message lets the wave release its VGPRs while waiting for it) and none is
  /// a scratch store (it still needs its VGPRs). \p PendingForcedWait is the
  /// forced-after wait of the previous instruction, not applied to \p S yet.
  bool isSafeToDeallocVGPRs(const State &S, const Waitcnt &PendingForcedWait);

  /// \returns true if \p S has an outstanding SMEM_ACCESS event.
  bool hasPendingSMEM(const State &S) const;

  /// \returns the waits needed at the end of \p MBB, taking into account
  /// pre-header flushing (see \ref shouldFlushPreheader) if necessary. If \p
  /// MBB is in \p ForceDrain, all InstCounters will be drained.
  Waitcnt getWaitsAtEnd(const State &S, const MachineBasicBlock &MBB,
                        const DenseSet<const MachineBasicBlock *> &ForceDrain);

  /// Computes waits necessary before a certain point in a MBB.
  /// \param S the current State of a MBB.
  /// \param MI a MachineInstr, or nullptr to indicate the end of the MBB.
  /// \param Preceding Waits that precede \p MI
  /// \param ExtraWait Extra wait to take into account.
  /// \returns everything to wait for before \p MI; this also includes
  /// \ref getWaitsRequiredBy
  Waitcnt getWaitsBefore(const State &S, const MachineInstr *MI,
                         const PrecedingWaits &Preceding, Waitcnt ExtraWait);

  /// \param S the current State of a MBB.
  /// \param MI a MachineInstr
  /// \returns the waits necessary to satisfy any dependency of \p MI on
  /// in-flight events.
  Waitcnt getWaitsRequiredBy(const State &S, const MachineInstr &MI);

  /// \returns a wait of 0 on every counter that must be empty before \p MI
  /// These are state-independent waits which are required by the ISA.
  Waitcnt getAlwaysRequiredWaitsBefore(const MachineInstr &MI) const;

  /// \returns true if \p MI must wait for record \p R of counter \p T, through
  /// a register (RAW, WAW, WAR) or a memory dependency.
  bool hasDependencyOn(const State &S, const MachineInstr &MI,
                       const EventTrackerRecord &R, InstCounterType T) const;

  /// \returns true if a register operand of \p MI has a dependency on an
  /// operand of \p P via the counter \p T.
  /// (see \ref getOperandsTrackedByCounter).
  bool hasRegDependencyOn(const State &S, const MachineInstr &MI,
                          const MachineInstr &P, InstCounterType T) const;

  /// \returns true if \p MI has a memory dependency on \p P via the counter \p
  /// T. (e.g. LDS access after aliasing DMAs)
  bool hasMemDependencyOn(const MachineInstr &MI, const MachineInstr &P,
                          InstCounterType T) const;

  /// \returns true if operand \p Op of \p MI can depend on a pending event of
  /// counter \p T, based on its register class, use/def role and, for WAW and
  /// EXP_CNT uses, the pending events in \p S.
  bool isOperandCheckedOn(const State &S, const MachineInstr &MI,
                          const MachineOperand &Op, InstCounterType T) const;

  /// \returns true if the VMEM instruction \p MI writing VGPR \p Reg needs no
  /// WAW wait: the target writes VGPRs in order and every pending write to
  /// \p Reg has the same VMEM event kind as \p MI.
  bool isInOrderVGPRWrite(const State &S, const MachineInstr &MI,
                          MCRegister Reg) const;

  /// \returns the VGPR write events (see getVGPRWriteEvents) of the pending
  /// VM_CNT-only producers that write \p Reg.
  HWEvents getPendingVGPRWriteEvents(const State &S, MCRegister Reg) const;

  /// \returns the register to check on \p T for operand register \p Reg of
  /// \p MI: the enclosing 32-bit VGPR if a 16-bit write may clobber the other
  /// half (D16Writes32BitVgpr), else \p Reg.
  MCRegister getRegToCheck(const State &S, const MachineInstr &MI,
                           MCRegister Reg, InstCounterType T) const;

  /// \returns true if there is a pending write to \p Ref tracked via \p T.
  bool hasPendingWriteTo(const State &S, MCRegister Reg,
                         InstCounterType T) const;

  /// \returns true if events pending on \p T may complete out of order, in
  /// which case only a wait for 0 guarantees anything.
  bool isOutOfOrder(const State &S, InstCounterType T) const;

  /// \returns \p W without the waits that can never block given \p S.
  Waitcnt removeNoOpWaits(const State &S, Waitcnt W) const;

  /// Simplifies the soft wait \p W in \p S. No-op at -O0.
  Waitcnt simplifySoftWait(const State &S, Waitcnt W) const;

  /// \returns \p W without its LOAD_CNT wait if only cache invalidates are
  /// pending on LOAD_CNT.
  Waitcnt removeVmemInvOnlyWait(const State &S, Waitcnt W) const;

  /// \returns true if \p P writes the callee address of \p Call or, for a
  /// register callee, its saved return address.
  bool writesCallAddrOrDst(const MachineInstr &P,
                           const MachineInstr &Call) const;

  /// Applies the wait \p W to \p S. Non-zero waits on out-of-order counters
  /// are ignored. The only caller of EventTracker::drain.
  void applyWait(State &S, const Waitcnt &W);

  /// Records the events of \p MI into \p S.
  void recordEvents(State &S, MachineInstr &MI);

  /// Models unknown stores left in flight by a caller or callee (T6).
  void setStateOnFunctionEntryOrReturn(State &S);

  /// \returns the waits forced right after \p MI (precise memory mode).
  Waitcnt getWaitsForcedAfter(const MachineInstr &MI) const;

  /// \returns a wait of 0 on every counter, STORE_CNT only if
  /// \p IncludeStores.
  Waitcnt getAllZeroWaitcnt(bool IncludeStores) const;

#ifndef NDEBUG
  /// Asserts that the rewritten preceding waits of \p It wait for exactly \p W.
  void checkRewrite(const WaitcntRewriter &Rewriter, MachineBasicBlock &MBB,
                    MachineBasicBlock::instr_iterator It,
                    const Waitcnt &W) const;
#endif

  /// \returns the wait at the start of a non-entry function, for the
  /// operations its caller left in flight (stores excluded).
  Waitcnt getEntryWait() const;

  /// Sets \p W[T] to 0 if anything is pending on \p T.
  void waitForAll(Waitcnt &W, const State &S, InstCounterType T);

  /// Adds to \p W the wait on \p T for the youngest record matching \p Pred,
  /// or a wait for 0 if \p DrainAll.
  void waitForMatchingRecords(
      Waitcnt &W, const State &S, InstCounterType T, bool DrainAll,
      function_ref<bool(const EventTrackerRecord &)> Pred) const;

  /// \returns the wait on \p T that guarantees completion of a record of age
  /// \p Age: 0 if \p T is out of order or a flat access is pending, else
  /// \p Age capped at the counter limit - 1.
  unsigned waitFor(const State &S, InstCounterType T, unsigned Age) const;

  /// \returns true if waits on \p T (LOAD_CNT or DS_CNT) must be 0 because a
  /// flat access that may hit both VMEM and LDS is pending, and the target
  /// does not decrement both counters in order.
  bool flatForcesZero(const State &S, InstCounterType T) const;

  MachineFunction &MF;
  AAResults *AA = nullptr;
  const GCNSubtarget &ST;
  const AMDGPUMachineFunctionInfo &MFI;
  const SIInstrInfo &TII;
  const SIRegisterInfo &TRI;
  const MachineRegisterInfo &MRI;
  ArrayRef<AMDGPUInstCounter> InstCounters;
  const IsaVersion IV;

  /// Counter that tracks SMEM_ACCESS (DS_CNT pre-gfx12, KM_CNT after).
  const AMDGPUInstCounter *SmemCounter = nullptr;

  WaitcntRPOInfo RPO;
  PassOptions Opts;
  WaitcntLoopPreheaderInfo LoopPreInfo;

  bool EntryBlocksNeedWaits = false;
  bool OptNone = false;
  bool IsExpertMode = false;
  bool IsTgSplit = false;
};

void AMDGPUNewInsertWaitcnts::solve(Solution &Sol) {
  // Out state of a given MBB.
  DenseMap<const MachineBasicBlock *, State> OutStates;
  for (const MachineBasicBlock &MBB : MF)
    OutStates.try_emplace(&MBB, MBB, InstCounters);

  // MBBs marked for force draining. This means we'll ensure the output state of
  // the block is empty before moving on. This should ideally not be invoked
  // often, and provides an escape hatch to generate correct code no matter
  // what.
  //
  // TODO: Unsure of how this works with AsyncMarks? Is it valid to just empty
  // the asyncmarks?
  DenseSet<const MachineBasicBlock *> ForceDrain;

  // Only for retreating MBBs: Count how many times we changed the MBB so we can
  // put a hard cap on iteration.
  DenseMap<const MachineBasicBlock *, unsigned> RetreatingMBBChangeCount;

  unsigned Visits = 0;
  const unsigned TotalVisitBudget = Opts.GlobalLimit * RPO.getNumBlocks();
  bool WillForceDrain = false;

  // Short-circuit if we are doing a single RPO pass.
  if (Opts.IterationLimitForRetreatingBlocks == 0) {
    auto Retreating = RPO.getRetreatingBlocks();
    ForceDrain.insert(Retreating.begin(),
                      Retreating.end()); // one RPO pass (A.4)
  }

  RPOWorklist WL(RPO);
  while (MachineBasicBlock *MBB = WL.pop()) {
    const bool IsRetreating = RPO.getRetreatingBlocks().contains(MBB);
    State Old = OutStates.at(MBB);
    // The last visit always wins, so preemptively clear the solution.
    Sol.forget(*MBB);

    walkBlock(*MBB, OutStates, ForceDrain, &Sol);
    State &New = OutStates.at(MBB);

    if (IsRetreating) {
      for (const AMDGPUInstCounter &IC : InstCounters) {
        InstCounterType T = IC.getType();
        // If the timeline is unchanged and only the counter grew, widen the
        // count to the cap.
        if ((Old.ET.getTimeline(T) == New.ET.getTimeline(T)) &&
            (Old.ET.count(T) < New.ET.count(T))) {
          if (New.ET.widenCount(IC.getType()))
            ++NumCounterWidened;
        }
      }
    }

    if (++Visits > TotalVisitBudget && !WillForceDrain) {
      /// TODO: Move to a helper function? Maybe the entire solver should move
      /// to a separate class?

      // We exhausted our budget on this function, do the conservatively correct
      // thing. This should really not fire often and it may be worth emitting a
      // diagnostic when it happens.
      for (MachineBasicBlock *RetreatingMBB : RPO.getRetreatingBlocks()) {
        // Visit all retreating MBBs we haven't force-drained yet.
        if (!ForceDrain.contains(RetreatingMBB)) {
          ForceDrain.insert(RetreatingMBB);
          WL.push(RetreatingMBB);
        }
      }
      WillForceDrain = true;
    }

    // Out state is equal to old state; we are getting closer to a fixpoint.
    if (New == Old)
      continue;

    for (MachineBasicBlock *Succ : MBB->successors()) {
      WL.push(Succ);

      /// TODO: Implement this ?
      // Nested reset (A.7): a forward edge into a loop header restarts the
      // counters of that loop's retreating sources.
      //
      // if (RPOIdx.at(MBB) < RPOIdx.at(Succ)) {
      //   for (MachineBasicBlock *Src : RetreatingInto.lookup(Succ)) {
      //     Changes[Src] = 0;
      //   }
      // }
    }

    // If this is a retreating block that isn't marked for force-draining, keep
    // track of how many times we passed over it. Once our budget runs out, mark
    // it for force draining and revisit it.
    if (IsRetreating && !ForceDrain.contains(MBB) &&
        ++RetreatingMBBChangeCount[MBB] >
            Opts.IterationLimitForRetreatingBlocks) {
      /// TODO: This should be rare as well, diagnose it.
      ForceDrain.insert(MBB);
      WL.push(MBB);
    }
  }

  /// TODO: Add correctness assertion for debug builds/EXPENSIVE_CHECKS.
}

struct PendingWaitAfter {
  Waitcnt W;
  bool AlwaysGDS = false; // came from an always-GDS instruction
};

bool AMDGPUNewInsertWaitcnts::shouldFlushPreheader(
    const State &S, const MachineBasicBlock &MBB) {
  const WaitcntLoopPreheaderInfo::Entry *L = LoopPreInfo.getPreheaderInfo(MBB);
  if (!L || L->LoadedValueUsedInLoop)
    return false;

  bool StoreOnlyLoop = !ST.hasVscnt() && L->HasVMemStore && !L->HasVMemLoad;
  bool LoadsUnused = L->HasVMemLoad && ST.hasVmemWriteVgprInOrder();
  if (!StoreOnlyLoop && !LoadsUnused)
    return false;

  return any_of(S.ET.getTimeline(LOAD_CNT), [&](const EventTrackerRecord &R) {
    return definesAnyRUs(TRI, *R.getMI(), L->UsedVectorUnits);
  });
}

Waitcnt AMDGPUNewInsertWaitcnts::getWaitsAtEnd(
    const State &S, const MachineBasicBlock &MBB,
    const DenseSet<const MachineBasicBlock *> &ForceDrain) {
  Waitcnt W;

  if (ForceDrain.contains(&MBB)) {
    // Do not use getAllZeroWaitcnt - this has to be more thorough: drain every
    // single counter that has even just one event. This is necessary as
    // ForceDrain is one of the guards that ensure we reach a fixpoint.
    // An indeterminate counter can have an empty timeline (events we don't
    // track), and a count without records must be drained too, or the
    // out-state of this block would still depend on its in-state.
    for (const AMDGPUInstCounter &IC : InstCounters) {
      InstCounterType T = IC.getType();
      if (!S.ET.getTimeline(T).empty() || S.ET.count(T) > 0 ||
          S.ET.isIndeterminate(T))
        W.set(T, 0);
    }
  }

  if (shouldFlushPreheader(S, MBB)) { // recomputed every visit (W7)
    waitForAll(W, S, LOAD_CNT); // vmcnt(0) at the preheader end (SIW:2616-2620)
  }

  return W;
}

Waitcnt AMDGPUNewInsertWaitcnts::getWaitsBefore(const State &S,
                                                const MachineInstr *MI,
                                                const PrecedingWaits &Preceding,
                                                Waitcnt ExtraWait) {
  Waitcnt W = Preceding.CombinedWaits;

  for (const Waitcnt &Soft : Preceding.SoftWaits) {
    W = W.combined(simplifySoftWait(S, Soft));
  }

  if (Preceding.SeenLDSDirectWait) {
    waitForMatchingRecords(
        W, S, LOAD_CNT, /*DrainAll=*/false,
        [&](const auto &R) { return TII.isNonAsyncLdsDmaWrite(*R.getMI()); });
  }

  // TODO: WAIT_ASYNCMARK in the preceding waits (App. B).

  W = W.combined(ExtraWait);
  if (MI)
    W = W.combined(getWaitsRequiredBy(S, *MI));

  return W;
}

Waitcnt AMDGPUNewInsertWaitcnts::getWaitsRequiredBy(const State &S,
                                                    const MachineInstr &MI) {
  Waitcnt W;

  // Calls: the callee's entry waits for everything, so only the callee address
  // and the saved return address wait, and only on SMEM (SIW:2414-2428).
  if (MI.isCall()) {
    assert(SmemCounter && "no counter tracks SMEM");
    waitForMatchingRecords(
        W, S, SmemCounter->getType(), /*DrainAll=*/false, [&](const auto &R) {
          return HWEvents(R.getKind()) == HWEvents::SMEM_ACCESS &&
                 writesCallAddrOrDst(*R.getMI(), MI);
        });
    return W;
  }

  for (const AMDGPUInstCounter &IC : InstCounters) {
    waitForMatchingRecords(W, S, IC.getType(), /*DrainAll=*/false,
                           [&](const EventTrackerRecord &R) {
                             return hasDependencyOn(S, MI, R, IC.getType());
                           });
  }

  // Counters that must be empty before MI. The old pass simplifies these like
  // any other wait (SIW:2567), and also drops a return's INV-only LOAD wait
  // (SIW:2340), even at -O0.
  Waitcnt Empty = removeNoOpWaits(S, getAlwaysRequiredWaitsBefore(MI));
  if (MI.isReturn() && !MI.isCall())
    Empty = removeVmemInvOnlyWait(S, Empty);
  W = W.combined(Empty);

  // EXEC write: drain exports and GDS source locks (SIW:2395-2404).
  if (MI.modifiesRegister(AMDGPU::EXEC, &TRI)) {
    static constexpr HWEvents ExpCntDrainEvents =
        HWEvents::EXP_GPR_LOCK | HWEvents::EXP_PARAM_ACCESS |
        HWEvents::EXP_POS_ACCESS | HWEvents::GDS_GPR_LOCK;
    waitForMatchingRecords(W, S, EXP_CNT, /*DrainAll=*/true, [](const auto &R) {
      return (HWEvents(R.getKind()) & ExpCntDrainEvents).any();
    });
  }

  // Always-GDS: wait for a pending GDS operation (SIW:2408-2409, LastGDS is
  // set for DS producers that are always-GDS or have the gds bit, SIW:2722).
  if (TII.isAlwaysGDS(MI.getOpcode())) {
    waitForMatchingRecords(
        W, S, DS_CNT, /*DrainAll=*/false, [&](const auto &R) {
          const MachineInstr &P = *R.getMI();
          return SIInstrInfo::isDS(P) &&
                 (TII.isAlwaysGDS(P.getOpcode()) ||
                  TII.hasModifiersSet(P, AMDGPU::OpName::gds));
        });
  }

  // VCCZ bug: a VCCZ-reading branch waits for pending SMEM (SIW:2578-2581).
  if (SIInstrInfo::isCBranchVCCZRead(MI) && ST.hasReadVCCZBug()) {
    assert(SmemCounter && "no counter tracks SMEM");
    waitForMatchingRecords(
        W, S, SmemCounter->getType(), /*DrainAll=*/false, [](const auto &R) {
          return HWEvents(R.getKind()) == HWEvents::SMEM_ACCESS;
        });
  }

  return W;
}

Waitcnt AMDGPUNewInsertWaitcnts::getAlwaysRequiredWaitsBefore(
    const MachineInstr &MI) const {
  // Port of the forced waits in generateWaitcntInstBefore (SIW:2318-2366,
  // 2553-2556). Returns a 0 for every counter that must be drained before MI.
  Waitcnt W;

  switch (MI.getOpcode()) {
  case AMDGPU::BUFFER_WBINVL1:
  case AMDGPU::BUFFER_WBINVL1_SC:
  case AMDGPU::BUFFER_WBINVL1_VOL:
  case AMDGPU::BUFFER_GL0_INV:
  case AMDGPU::BUFFER_GL1_INV:
    // FIXME (from the old pass): should already be handled by the memory
    // legalizer.
    W.set(LOAD_CNT, 0);
    break;
  case AMDGPU::SI_RETURN_TO_EPILOG:
  case AMDGPU::SI_RETURN:
  case AMDGPU::SI_WHOLE_WAVE_FUNC_RETURN:
  case AMDGPU::S_SETPC_B64_return:
    // Everything but stores must be resolved at return: the caller assumes so
    // after the call (see recordEvents).
    W = getAllZeroWaitcnt(/*IncludeStores=*/false);
    break;
  case AMDGPU::S_SENDMSG:
  case AMDGPU::S_SENDMSGHALT:
    // Resolve vm waits before gs-done.
    if (ST.hasLegacyGeometry() &&
        (MI.getOperand(0).getImm() & SendMsg::ID_MASK_PreGFX11_) ==
            SendMsg::ID_GS_DONE_PreGFX11)
      W.set(LOAD_CNT, 0);
    break;
  case AMDGPU::S_BARRIER:
    // Without auto-waitcnt or back-off, the barrier must not have any memory
    // operation outstanding.
    if (!ST.hasAutoWaitcntBeforeBarrier() && !ST.hasBackOffBarrier())
      W = getAllZeroWaitcnt(/*IncludeStores=*/true);
    break;
  default:
    break;
  }

  return W;
}

bool AMDGPUNewInsertWaitcnts::writesCallAddrOrDst(
    const MachineInstr &P, const MachineInstr &Call) const {
  // SIW:2400-2410: the callee address and, only if the callee is a register,
  // the saved return address (WAW).
  const MachineOperand &CallAddrOp = TII.getCalleeOperand(Call);
  if (!CallAddrOp.isReg())
    return false;

  // Only explicit defs carry scores in the old pass (SIW:1020-1027).
  const MachineOperand *RtnAddrOp =
      TII.getNamedOperand(Call, AMDGPU::OpName::dst);
  return any_of(P.defs(), [&](const MachineOperand &Def) {
    return Def.isReg() &&
           (TRI.regsOverlap(Def.getReg(), CallAddrOp.getReg()) ||
            (RtnAddrOp && TRI.regsOverlap(Def.getReg(), RtnAddrOp->getReg())));
  });
}

bool AMDGPUNewInsertWaitcnts::hasDependencyOn(const State &S,
                                              const MachineInstr &MI,
                                              const EventTrackerRecord &R,
                                              InstCounterType T) const {
  // TODO(T6): UNKNOWN_STORE records have no producer MI and must never match:
  //   if (R.getKind() == UNKNOWN_STORE)
  //     return false;
  const MachineInstr &P = *R.getMI();

  // TODO(perf, R7): this is called for every (MI, record) pair, and the
  // register checks below scan the timelines again (WAW exemption, D16).
  // Precompute per-MI data if it shows up in profiles.
  return hasRegDependencyOn(S, MI, P, T) || hasMemDependencyOn(MI, P, T);
}

bool AMDGPUNewInsertWaitcnts::hasRegDependencyOn(const State &S,
                                                 const MachineInstr &MI,
                                                 const MachineInstr &P,
                                                 InstCounterType T) const {
  // Registers of P that MI must wait on T for (defs, or EXP_CNT locks).
  SmallVector<const MachineOperand *, 4> Tracked;
  getOperandsTrackedByCounter(TII, TRI, MRI, P, T, Tracked);
  if (Tracked.empty())
    return false;

  // RAW, WAW and WAR (EXP_CNT) via MI's operands (SIW:2468-2537).
  for (const MachineOperand &Op : MI.operands()) {
    if (!Op.isReg() || !Op.getReg() || !isOperandCheckedOn(S, MI, Op, T))
      continue;

    MCRegister Reg = getRegToCheck(S, MI, Op.getReg().asMCReg(), T);
    if (any_of(Tracked, [&](const MachineOperand *TrackedOp) {
          return trackedRegsOverlap(TRI, Reg, TrackedOp->getReg().asMCReg());
        }))
      return true;
  }
  return false;
}

bool AMDGPUNewInsertWaitcnts::isOperandCheckedOn(const State &S,
                                                 const MachineInstr &MI,
                                                 const MachineOperand &Op,
                                                 InstCounterType T) const {
  // MI does not read its tied source.
  if (Op.isTied() && Op.isUse() && TII.doesNotReadTiedSource(MI))
    return false;

  // TODO(gfx12+): X_CNT on defs, VA_VDST_*, VM_VSRC (SIW:2490-2496, 2534).
  const Register Reg = Op.getReg();
  if (TRI.isVectorRegister(MRI, Reg)) {
    // Implicit VGPR operands of memory instructions only model
    // super-register liveness.
    if (Op.isImplicit() && MI.mayLoadOrStore())
      return false;

    switch (T) {
    case LOAD_CNT:
    case SAMPLE_CNT:
    case BVH_CNT:
      // RAW always waits. WAW waits unless both writes are guaranteed to land
      // in order.
      return Op.isUse() || !isInOrderVGPRWrite(S, MI, Reg.asMCReg());
    case EXP_CNT:
      // WAR on a locked register. Uses only conflict with LDS parameter
      // loads, whose destination is written asynchronously.
      return Op.isDef() ||
             S.ET.getPendingEvents(EXP_CNT).contains(HWEvents::EXP_LDS_ACCESS);
    case DS_CNT:
      return true;
    default:
      return false;
    }
  }

  if (Reg == AMDGPU::SCC)
    return T == KM_CNT;

  // Other (scalar) registers are only written asynchronously by SMEM.
  return T == SmemCounter->getType();
}

bool AMDGPUNewInsertWaitcnts::isInOrderVGPRWrite(const State &S,
                                                 const MachineInstr &MI,
                                                 MCRegister Reg) const {
  // The negation of SIW:2511-2515. Without per-register pending events in the
  // state, they are recomputed from the timelines.
  if (!updatesVMCntOnly(MI) || !ST.hasVmemWriteVgprInOrder())
    return false;

  HWEvents Pending = getPendingVGPRWriteEvents(S, Reg);
  if ((Pending - getSimplifiedVMEMEventsFor(MI, TII)).any())
    return false;

  // Point sample acceleration may turn MI into a plain read, which is not
  // in order with other kinds of pending writes.
  return !mayUsePointSampleAccel(ST, MI) ||
         !(Pending - HWEvents::VMEM_READ_ACCESS).any();
}

HWEvents
AMDGPUNewInsertWaitcnts::getPendingVGPRWriteEvents(const State &S,
                                                   MCRegister Reg) const {
  // Old pass: VGPRPendingEvents, only set by producers that update VM_CNT
  // only (SIW:1012-1027).
  HWEvents Pending;
  for (InstCounterType T : {LOAD_CNT, SAMPLE_CNT, BVH_CNT}) {
    for (const EventTrackerRecord &R : S.ET.getTimeline(T)) {
      const MachineInstr &P = *R.getMI();
      if (!updatesVMCntOnly(P))
        continue;
      if (any_of(P.defs(), [&](const MachineOperand &Def) {
            return trackedRegsOverlap(TRI, Reg, Def.getReg().asMCReg());
          }))
        Pending |= getVGPRWriteEvents(ST, TII, P);
    }
  }
  return Pending;
}

MCRegister AMDGPUNewInsertWaitcnts::getRegToCheck(const State &S,
                                                  const MachineInstr &MI,
                                                  MCRegister Reg,
                                                  InstCounterType T) const {
  // Port of determineVGPR16Dependency (SIW:1418-1457). With
  // D16Writes32BitVgpr, a 16-bit write may clobber the whole 32-bit VGPR, so
  // the other half is checked too if it has a pending write on T and either
  // MI is a VALU or MI's events on T may complete out of order.
  if (!ST.hasD16Writes32BitVgpr() || !TRI.isVectorRegister(MRI, Reg))
    return Reg;

  MCRegister OtherHalf = getOther16BitHalf(TRI, Reg);
  if (!OtherHalf || !hasPendingWriteTo(S, OtherHalf, T))
    return Reg;

  MCRegister Reg32 = TRI.get32BitRegister(Reg);
  if (TII.isVALU(MI, /*AllowLDSDMA=*/false))
    return Reg32;

  HWEvents Events = getEventsFor(MI, ST, IsExpertMode, IsTgSplit) &
                    getCounter(T, InstCounters).getEvents();
  return Events.size() > 1 ? Reg32 : Reg;
}

bool AMDGPUNewInsertWaitcnts::hasPendingWriteTo(const State &S, MCRegister Reg,
                                                InstCounterType T) const {
  return any_of(S.ET.getTimeline(T), [&](const EventTrackerRecord &R) {
    SmallVector<const MachineOperand *, 4> Tracked;
    getOperandsTrackedByCounter(TII, TRI, MRI, *R.getMI(), T, Tracked);
    return any_of(Tracked, [&](const MachineOperand *Op) {
      return trackedRegsOverlap(TRI, Reg, Op->getReg().asMCReg());
    });
  });
}

bool AMDGPUNewInsertWaitcnts::hasMemDependencyOn(const MachineInstr &MI,
                                                 const MachineInstr &P,
                                                 InstCounterType T) const {
  // LDS DMA → LDS access (SIW:2437-2463). Back-to-back LDS DMAs don't wait
  // for each other.
  //
  // Deviations from the old pass:
  //  - The old pass only tracks LDS DMA stores that have alias scope info in
  //    LDSDMAStores. When MI has alias info, an unscoped LDS DMA is never
  //    checked, which looks like a missed wait [code, not reproduced]. Here
  //    every pending LDS DMA is checked with AA.
  //  - The old pass also waits on EXP_CNT for LDS DMA before an LDS store,
  //    but no LDS DMA slot ever gets an EXP_CNT score (the slot bookkeeping
  //    is only in the non-EXP branch of updateByEvent), so it is dead code
  //    and not ported.
  if (T == LOAD_CNT && TII.isNonAsyncLdsDmaWrite(P) &&
      !SIInstrInfo::mayWriteLDSThroughDMA(MI) &&
      mayAccessLDSWrittenByDMA(AA, MI, P))
    return true;

  // SMEM load → store to the same address: WAR (SIW:2428-2435).
  //
  // Deviation from the old pass: it keeps a function-wide, visit-order
  // dependent map of loaded addresses (SLoadAddresses) and forces a wait
  // whenever the address matches, even if the load has completed. Here only
  // pending loads match. The wait still goes to 0, since SMEM is out of order.
  if (T == SmemCounter->getType() && TII.isSMRD(P) &&
      mayStoreToLoadedAddress(MI, P))
    return true;

  return false;
}

bool AMDGPUNewInsertWaitcnts::isOutOfOrder(const State &S,
                                           InstCounterType T) const {
  // Port of counterOutOfOrder (SIW:1568-1605). The pending events of T are the
  // kinds of the records in T's timeline.
  HWEvents Events = S.ET.getPendingEvents(T);

  // Scalar memory reads can always complete out of order. ET only records
  // SMEM_ACCESS on the SMEM counter (DS_CNT pre-gfx12, KM_CNT after), which
  // replaces the old `T == SmemAccessCounter` check.
  if (Events.contains(HWEvents::SMEM_ACCESS) ||
      (T == X_CNT && Events.contains(HWEvents::SMEM_GROUP)))
    return true;

  if (T == LOAD_CNT) {
    // Without vscnt, LOAD_CNT also counts stores, and all of these events
    // complete in order with respect to each other.
    if (!ST.hasVscnt())
      return false;

    // Without extended counters, sampler/BVH reads are equivalent to
    // VMEM_READ_ACCESS.
    constexpr HWEvents ExtendedImageEvents =
        HWEvents::VMEM_SAMPLER_READ_ACCESS | HWEvents::VMEM_BVH_READ_ACCESS;
    if (!ST.hasExtendedWaitCounts() && (Events & ExtendedImageEvents).any()) {
      Events -= ExtendedImageEvents;
      Events |= HWEvents::VMEM_READ_ACCESS;
    }

    // GLOBAL_INV/BUFFER_INV complete in order with VMEM_READ_ACCESS.
    Events -= HWEvents::VMEM_INV_ACCESS;
  }

  // TODO(T6): an UNKNOWN_STORE record must count as mixed. Being a distinct
  // kind, it should already do so here once it exists.
  return Events.size() > 1;
}

Waitcnt AMDGPUNewInsertWaitcnts::removeNoOpWaits(const State &S,
                                                 Waitcnt W) const {
  // At most count(T) events are in flight on every path, so a wait for
  // N >= count(T) can never block.
  //
  // TODO(gfx12+): XCNT and VM_VSRC have extra rules (simplifyXcnt,
  // simplifyVmVsrc). The plain count test is still sound for them.
  for (const AMDGPUInstCounter &IC : InstCounters) {
    InstCounterType T = IC.getType();
    unsigned Val = W.get(T);
    // An indeterminate counter has events we don't track, so its count is
    // not an upper bound (e.g. NoLimit counters can't be widened).
    if (Val != ~0u && Val >= S.ET.count(T) && !S.ET.isIndeterminate(T))
      W.set(T, ~0u);
  }

  return W;
}

Waitcnt AMDGPUNewInsertWaitcnts::simplifySoftWait(const State &S,
                                                  Waitcnt W) const {
  // Soft waits are kept as-is at -O0 (SIW:1677).
  if (OptNone)
    return W;

  W = removeNoOpWaits(S, W);
  // On GFX12+, we must preserve the waits after cache inv/wbs for correctness.
  if (!ST.hasExtendedWaitCounts())
    W = removeVmemInvOnlyWait(S, W);
  return W;
}

Waitcnt AMDGPUNewInsertWaitcnts::removeVmemInvOnlyWait(const State &S,
                                                       Waitcnt W) const {
  // FIXME: Potential bug inherited from the old pass. On targets without
  // vscnt, stores are counted on LOAD_CNT, but they are masked out below, so a
  // soft vmcnt wait is dropped even when stores are still in flight, e.g.
  // `buffer_inv; global_store; <soft vmcnt(0) from a release fence>`.
  // [unproven]: no repro yet. Dropping the store mask would be the
  // conservative fix.
  //
  // GLOBAL_INV/BUFFER_INV increment LOAD_CNT but write no VGPRs: a wait that
  // only drains them can be dropped (simplifyVmemInvOnlyWait, SIW:566-573).
  const HWEvents StoreEvents =
      HWEvents::VMEM_WRITE_ACCESS | HWEvents::SCRATCH_WRITE_ACCESS;
  if ((S.ET.getPendingEvents(LOAD_CNT) - StoreEvents) ==
      HWEvents::VMEM_INV_ACCESS)
    W.set(LOAD_CNT, ~0u);

  return W;
}

void AMDGPUNewInsertWaitcnts::applyWait(State &S, const Waitcnt &W) {
  for (const AMDGPUInstCounter &IC : InstCounters) {
    InstCounterType T = IC.getType();
    unsigned Val = W.get(T);
    if (Val == ~0u)
      continue;
    if (Val != 0 && isOutOfOrder(S, T))
      continue;
    S.ET.drain(T, Val);
  }

  // TODO: ASYNCMARK state update (App. B).
}

void AMDGPUNewInsertWaitcnts::recordEvents(State &S, MachineInstr &MI) {
  if (MI.isCall()) {
    // State-only drain, no wait emitted: the callee's entry S_WAITCNT 0 covers
    // every counter except STORE. The callee may leave stores in flight
    // (SIW:2758-2761).
    applyWait(S, getAllZeroWaitcnt(/*IncludeStores=*/false));
    setStateOnFunctionEntryOrReturn(S); // T6
    return;
  }

  for (HWEvents E : getEventsFor(MI, ST, IsExpertMode, IsTgSplit))
    S.ET.record(MI, SingleHWEvent::encode(E));

  // For in-order counters, drain any records above the cap.
  for (const AMDGPUInstCounter &IC : InstCounters) {
    InstCounterType T = IC.getType();
    if (!isOutOfOrder(S, T))
      S.ET.drainCappedRecords(T);
  }

  // The waitexp operand of VINTERP is an implicit EXP_CNT wait (SIW:2744-2746).
  // WaitcntRewriter may lower it to fold the wait decided before MI, which
  // applyWait has already modelled.
  if (TII.isVINTERP(MI)) {
    Waitcnt WaitExp;
    WaitExp.set(EXP_CNT,
                TII.getNamedOperand(MI, AMDGPU::OpName::waitexp)->getImm());
    applyWait(S, WaitExp);
  }

  // TODO: ASYNCMARK push (App. B).
}

void AMDGPUNewInsertWaitcnts::setStateOnFunctionEntryOrReturn(State &S) {
  // A caller (at function entry) or a callee (after a call) may leave stores in
  // flight that we don't track.
  S.ET.markIndeterminate(STORE_CNT);
}

Waitcnt
AMDGPUNewInsertWaitcnts::getWaitsForcedAfter(const MachineInstr &MI) const {
  // SIW:2692-2700.
  Waitcnt W;
  if (ST.isPreciseMemoryEnabled() && MI.mayLoadOrStore())
    W = getAllZeroWaitcnt(MI.mayStore() && !SIInstrInfo::isAtomicRet(MI));
  if (TII.isAlwaysGDS(MI.getOpcode()))
    W.set(DS_CNT, 0);
  return W;
}

Waitcnt AMDGPUNewInsertWaitcnts::getEntryWait() const {
  // Pre-gfx12, the old pass emits `S_WAITCNT 0`, i.e. vm/exp/lgkm (SIW:3524).
  // TODO(gfx12+): the old pass emits S_WAIT_LOADCNT_DSCNT 0 plus one wait per
  // extended counter, skipping STORE/X/ASYNC/TENSOR and counters the target
  // lacks, plus S_WAITCNT_DEPCTR in expert mode (SIW:3496-3522).
  return getAllZeroWaitcnt(/*IncludeStores=*/false);
}

Waitcnt AMDGPUNewInsertWaitcnts::getAllZeroWaitcnt(bool IncludeStores) const {
  // Mirrors WaitcntGeneratorPreGFX12/GFX12Plus::getAllZeroWaitcnt in
  // SIInsertWaitcnts.cpp. Counters not mentioned stay at ~0u (no wait).
  if (!ST.hasExtendedWaitCounts())
    return Waitcnt(0, 0, 0, IncludeStores && ST.hasVscnt() ? 0 : ~0u);

  unsigned ExpertVal = IsExpertMode ? 0 : ~0u;
  return Waitcnt(0, 0, 0, IncludeStores ? 0 : ~0u, 0, 0, 0, ~0u /* XCNT */,
                 ~0u /* ASYNC_CNT */, ~0u /* TENSOR_CNT */, ExpertVal,
                 ExpertVal, ExpertVal);
}

void AMDGPUNewInsertWaitcnts::waitForAll(Waitcnt &W, const State &S,
                                         InstCounterType T) {
  if (S.ET.count(T) > 0)
    W.set(T, 0);
}

void AMDGPUNewInsertWaitcnts::waitForMatchingRecords(
    Waitcnt &W, const State &S, InstCounterType T, bool DrainAll,
    function_ref<bool(const EventTrackerRecord &)> Pred) const {
  // The timeline is sorted by descending age, so walking it in reverse visits
  // the youngest records first. The first match has the minimum age, i.e. the
  // strongest wait any match would need: stop there.
  for (const EventTrackerRecord &R : reverse(S.ET.getTimeline(T))) {
    if (Pred(R)) {
      if (DrainAll)
        W.add(T, 0);
      else
        W.add(T, waitFor(S, T, R.getAge()));
      return;
    }
  }
}

bool AMDGPUNewInsertWaitcnts::flatForcesZero(const State &S,
                                             InstCounterType T) const {
  // A pending FLAT that may access both VMEM and LDS can decrement either
  // counter early, so waits on LOAD_CNT and DS_CNT must go to 0 (SIW:1370).
  if ((T != LOAD_CNT && T != DS_CNT) || ST.hasFlatLgkmVMemCountInOrder())
    return false;

  // Deviation from the old pass, which records the LOAD/DS upper bounds at the
  // time of the FLAT (setPendingFlat, SIW:615-617). With vscnt, a FLAT store
  // has no LOAD_CNT event, so the old pass forces vmcnt(0) while an older,
  // unrelated load is pending. Here only the FLAT's own records count. The
  // FLAT always has a DS record (LDS_ACCESS), so it is still seen.
  // [argument]: sound because the store's VMEM half does not touch vmcnt.
  //
  // TODO: Perf: scans up to two timelines per waitFor call. Compute once per
  // instruction if it shows up in profiles (see roadmap R7).
  const auto IsPendingFlat = [&](const EventTrackerRecord &R) {
    return TII.mayAccessVMEMAndLDSThroughFlat(*R.getMI(), IsTgSplit);
  };
  return any_of(S.ET.getTimeline(DS_CNT), IsPendingFlat) ||
         any_of(S.ET.getTimeline(LOAD_CNT), IsPendingFlat);
}

unsigned AMDGPUNewInsertWaitcnts::waitFor(const State &S, InstCounterType T,
                                          unsigned Age) const {
  // Port of determineWaitForScore (SIW:1362-1388).
  if (flatForcesZero(S, T) || isOutOfOrder(S, T))
    return 0;

  // If the counter has been maxed out, avoid overflow by waiting for
  // Limit - 1 instead.
  const AMDGPUInstCounter &IC = getCounter(T, InstCounters);
  return IC.hasLimit() ? std::min(Age, IC.getLimit() - 1) : Age;
}

void AMDGPUNewInsertWaitcnts::walkBlock(
    MachineBasicBlock &MBB,
    DenseMap<const MachineBasicBlock *, State> &OutStates,
    const DenseSet<const MachineBasicBlock *> &ForceDrain, Solution *Sol) {
  State &S = OutStates.at(&MBB);

  S.ET.enterBlock(/*Getter=*/[&](auto &P) -> EventTracker & {
    return OutStates.at(&P).ET;
  });
  // TODO: AsyncMark state join too

  bool IsEntryWithWaits = MBB.isEntryBlock() && EntryBlocksNeedWaits;
  if (IsEntryWithWaits)
    setStateOnFunctionEntryOrReturn(S);

  // Per-walk, intra-block state: starts "vccz may be stale" at every block
  // entry, like the old pass (see VCCZRecomputeTracker).
  VCCZRecomputeTracker VCCZ(ST, TII);

  PrecedingWaits Preceding;
  PendingWaitAfter PWA;

  // The entry wait is folded into the first decision point: the first
  // instruction that is neither a wait nor a meta instruction, or the end of
  // the block if there is none. This matches the old pass, which inserts
  // S_WAITCNT 0 before the first non-meta instruction (SIW:3492-3494): any wait
  // already there joins the same preceding waits. It is not simplified: it
  // waits for the caller's unknown operations.
  bool NeedsEntryWait = IsEntryWithWaits;

  for (MachineInstr &MI : MBB.instrs()) {
    if (isWaitInstr(MI)) {
      Preceding.add(MI, IV);
      continue;
    }

    if (isNonWaitcntMetaInst(MI)) {
      continue;
    }

    Waitcnt Extra = PWA.W; // D10: forced-after wait of the previous MI
    if (NeedsEntryWait) {
      Extra = Extra.combined(getEntryWait());
      NeedsEntryWait = false;
    }

    if (MI.getIterator() == MBB.getFirstTerminator()) {
      Extra = Extra.combined(getWaitsAtEnd(S, MBB, ForceDrain));
    }

    if (Sol && isEndPgm(MI))
      (*Sol)[MBB].EndPgmSafeToMessage[&MI] = isSafeToDeallocVGPRs(S, PWA.W);

    Waitcnt W = getWaitsBefore(S, &MI, Preceding, Extra);
    applyWait(S, W);
    if (Sol) {
      (*Sol)[MBB].Before[&MI] = W;
      // SIW:2702-2710: S_NOP between the forced wait after an always-GDS
      // instruction and S_ENDPGM.
      if (PWA.AlwaysGDS && PWA.W.hasWait() &&
          isNextNonMetaEndpgm(MBB, MI.getIterator()))
        (*Sol)[MBB].NopAfterWait.insert(&MI);
    }

    recordEvents(S, MI);

    // Must come after recordEvents and applyWait: the old pass looks at the
    // state after MI was processed (and after its wait, which for a
    // vccz-reading branch drains the pending SMEM on bugged targets). Tracked
    // on every visit, but only recorded (like the waits) when building the
    // solution.
    if (VCCZ.visit(MI, hasPendingSMEM(S)) && Sol)
      (*Sol)[MBB].RecomputeVCCZBefore.insert(&MI);

    Preceding = {};
    PWA = {removeNoOpWaits(S, getWaitsForcedAfter(MI)),
           TII.isAlwaysGDS(MI.getOpcode())};

    // TODO: May want to verify less often once the pass is stable?
#if !defined(NDEBUG) || defined(EXPENSIVE_CHECKS)
    S.ET.verify();
#endif
  }

  if (MBB.getFirstTerminator() == MBB.end()) { // fallthrough block
    Waitcnt Extra = PWA.W.combined(getWaitsAtEnd(S, MBB, ForceDrain));
    if (NeedsEntryWait) // entry block with only waits and meta instructions
      Extra = Extra.combined(getEntryWait());
    Waitcnt W = getWaitsBefore(S, /*MI=*/nullptr, Preceding, Extra);
    applyWait(S, W);
    if (Sol) {
      (*Sol)[MBB].AtEnd = W;
      (*Sol)[MBB].NopAfterAtEnd = PWA.AlwaysGDS && PWA.W.hasWait() &&
                                  isNextNonMetaEndpgm(MBB, MBB.instr_end());
    }
  }

  // assert(C.W == Waitcnt() && "forced-after wait on a terminator");
}

bool AMDGPUNewInsertWaitcnts::isSafeToDeallocVGPRs(
    const State &S, const Waitcnt &PendingForcedWait) {
  // Safe iff some store is in flight and none of them is a scratch store.
  //
  // S does not include PendingForcedWait yet. Forced waits are always
  // all-zero (see \ref getWaitsForcedAfter), so one on STORE_CNT leaves no
  // store in flight and there is nothing to overlap with.
  //
  // The message only exists on gfx11+, where STORE_CNT is always present.
  if (!ST.hasVscnt())
    return false;

  // NB: This avoids having to copy the state just to apply the waitcnt.
  // If we somehow add forced waits that don't waitcnt zero, this is no longer
  // valid (hence the assert).
  assert((!PendingForcedWait.hasWaitStoreCnt() ||
          PendingForcedWait.get(STORE_CNT) == 0) &&
         "forced waits are expected to be all-zero waits");
  if (PendingForcedWait.hasWaitStoreCnt())
    return false;

  // An indeterminate STORE_CNT (stores from the caller / a callee) stands for
  // the old pass's "unknown stores", which set SCRATCH_WRITE_ACCESS too.
  if (S.ET.isIndeterminate(STORE_CNT))
    return false;

  const auto &Timeline = S.ET.getTimeline(STORE_CNT);
  bool HasStores = S.ET.count(STORE_CNT) > 0 || !Timeline.empty();
  bool HasScratchStore = any_of(Timeline, [](const EventTrackerRecord &R) {
    return HWEvents(R.getKind()) == HWEvents::SCRATCH_WRITE_ACCESS;
  });
  return HasStores && !HasScratchStore;
}

bool AMDGPUNewInsertWaitcnts::hasPendingSMEM(const State &S) const {
  // Port of ScoreBrackets.hasPendingEvent(SMEM_ACCESS). The SMEM counter also
  // tracks other events (LDS on gfx9, for instance), so look at the kind of
  // the records. A record disappears from the timeline when a wait drains it,
  // so this is "has an SMEM that was not waited for".
  // [unverified] Records pruned from in-order counters by drainCappedRecords
  // (T3) are treated as completed; SMEM is out-of-order, so none are pruned.
  assert(SmemCounter && "no counter tracks SMEM");
  return any_of(S.ET.getTimeline(SmemCounter->getType()),
                [](const EventTrackerRecord &R) {
                  return HWEvents(R.getKind()) == HWEvents::SMEM_ACCESS;
                });
}

bool AMDGPUNewInsertWaitcnts::apply(const Solution &Sol) {
  WaitcntRewriter Rewriter(ST, InstCounters);
  bool Modified = false;

  const auto Rewrite = [&](MachineBasicBlock &MBB,
                           MachineBasicBlock::instr_iterator It, Waitcnt W,
                           bool NopAfter) {
    Modified |= Rewriter.rewrite(MBB, It, W, NopAfter);
#ifndef NDEBUG
    checkRewrite(Rewriter, MBB, It, W);
#endif
  };

  // Program order, for deterministic MIR mutation and debug output. Blocks
  // without a solution are unreachable and left alone, like the old pass.
  for (MachineBasicBlock &MBB : MF) {
    const Solution::BasicBlockSolution *BS = Sol.lookup(MBB);
    if (!BS)
      continue;

    // Rewriting only touches the preceding waits of MI and inserts before MI,
    // so the iteration is not invalidated.
    for (MachineInstr &MI : make_early_inc_range(MBB.instrs())) {
      auto It = BS->Before.find(&MI);
      if (It != BS->Before.end())
        Rewrite(MBB, MI.getIterator(), It->second,
                BS->NopAfterWait.contains(&MI));

      // After the rewrite, so the recompute lands between the waits and MI
      // like in the old pass (waits are inserted first, vccz recompute second).
      if (BS->RecomputeVCCZBefore.contains(&MI)) {
        emitVCCZRecompute(MBB, MI.getIterator(), ST, TII, TRI);
        Modified = true;
      }
    }
    if (BS->AtEnd)
      Rewrite(MBB, MBB.instr_end(), *BS->AtEnd, BS->NopAfterAtEnd);
  }
  return Modified;
}

#ifndef NDEBUG
void AMDGPUNewInsertWaitcnts::checkRewrite(const WaitcntRewriter &Rewriter,
                                           MachineBasicBlock &MBB,
                                           MachineBasicBlock::instr_iterator It,
                                           const Waitcnt &W) const {
  // The rewritten preceding waits must wait for exactly W. A VINTERP's original
  // waitexp may be stronger than W on EXP_CNT. Encodings have no "no wait"
  // value: a field left alone decodes to the counter limit, which never blocks,
  // so values at or above the limit compare equal to ~0u.
  Waitcnt Got = Rewriter.decodePrecedingWaits(MBB, It);
  bool IsVINTERP = It != MBB.instr_end() && SIInstrInfo::isVINTERP(*It);
  for (const AMDGPUInstCounter &IC : InstCounters) {
    InstCounterType T = IC.getType();
    const auto Normalize = [&](unsigned V) {
      return IC.hasLimit() && V >= IC.getLimit() ? ~0u : V;
    };
    unsigned GotV = Normalize(Got.get(T));
    unsigned WantV = Normalize(W.get(T));
    bool OK = (IsVINTERP && T == EXP_CNT) ? GotV <= WantV : GotV == WantV;
    if (!OK) {
      dbgs() << "Expected " << W << "Got " << Got << "in " << MBB.getName()
             << '\n';
      llvm_unreachable("emitted waits differ from the solution");
    }
  }
}
#endif

void AMDGPUNewInsertWaitcnts::verify() {
  // TODO in a future batch of work; not critical for now.
}

bool AMDGPUNewInsertWaitcnts::insertVGPRDeallocs(const Solution &Sol) {
  VGPRDeallocMode Mode = getVGPRDeallocMode(MF, ST, TRI, OptNone);
  if (Mode == VGPRDeallocMode::None)
    return false;

  bool Modified = false;
  for (MachineBasicBlock &MBB : MF) {
    const Solution::BasicBlockSolution *BS = Sol.lookup(MBB);
    if (!BS)
      continue; // unreachable, like the old pass
    for (MachineInstr &MI : make_early_inc_range(MBB.instrs())) {
      auto It = BS->EndPgmSafeToMessage.find(&MI);
      if (It != BS->EndPgmSafeToMessage.end())
        Modified |= emitVGPRDealloc(MI, Mode, It->second, ST, TII);
    }
  }
  return Modified;
}

bool AMDGPUNewInsertWaitcnts::run() {
  Solution Sol;

  solve(Sol);
  bool Modified = apply(Sol);

  // TODO: move to apply
  Modified |= insertScalarStoreCacheFlushes(MF, ST, TII);
  Modified |= insertVGPRDeallocs(Sol);

  if (Opts.Verify)
    verify();

  return Modified;
}

class AMDGPUNewInsertWaitcntsLegacy : public MachineFunctionPass {
public:
  static char ID;

  AMDGPUNewInsertWaitcntsLegacy() : MachineFunctionPass(ID) {}

  bool runOnMachineFunction(MachineFunction &MF) override {
    auto &MLI = getAnalysis<MachineLoopInfoWrapperPass>().getLI();
    auto &PDT =
        getAnalysis<MachinePostDominatorTreeWrapperPass>().getPostDomTree();
    AAResults *AA = nullptr;
    if (auto *AAR = getAnalysisIfAvailable<AAResultsWrapperPass>())
      AA = &AAR->getAAResults();
    return AMDGPUNewInsertWaitcnts(MF, MLI, PDT, AA).run();
  }

  StringRef getPassName() const override {
    return "AMDGPU New Insert Waitcnts";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<MachineLoopInfoWrapperPass>();
    AU.addRequired<MachinePostDominatorTreeWrapperPass>();
    AU.addUsedIfAvailable<AAResultsWrapperPass>();
    AU.addPreserved<AAResultsWrapperPass>();
    MachineFunctionPass::getAnalysisUsage(AU);
  }
};

} // end anonymous namespace

char AMDGPUNewInsertWaitcntsLegacy::ID = 0;

char &llvm::AMDGPUNewInsertWaitcntsLegacyID = AMDGPUNewInsertWaitcntsLegacy::ID;

INITIALIZE_PASS_BEGIN(AMDGPUNewInsertWaitcntsLegacy, DEBUG_TYPE, PASS_NAME,
                      false, false)
INITIALIZE_PASS_DEPENDENCY(MachineLoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(MachinePostDominatorTreeWrapperPass)
INITIALIZE_PASS_END(AMDGPUNewInsertWaitcntsLegacy, DEBUG_TYPE, PASS_NAME, false,
                    false)

PreservedAnalyses
AMDGPUNewInsertWaitcntsPass::run(MachineFunction &MF,
                                 MachineFunctionAnalysisManager &MFAM) {
  auto &MLI = MFAM.getResult<MachineLoopAnalysis>(MF);
  auto &PDT = MFAM.getResult<MachinePostDominatorTreeAnalysis>(MF);
  auto *AA = MFAM.getResult<FunctionAnalysisManagerMachineFunctionProxy>(MF)
                 .getManager()
                 .getCachedResult<AAManager>(MF.getFunction());
  if (!AMDGPUNewInsertWaitcnts(MF, MLI, PDT, AA).run())
    return PreservedAnalyses::all();

  return getMachineFunctionPassPreservedAnalyses()
      .preserveSet<CFGAnalyses>()
      .preserve<AAManager>();
}
