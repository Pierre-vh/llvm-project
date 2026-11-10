//===- AMDGPUNewInsertWaitcntsUtils.h ---------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file Private utilities for the AMDGPUNewInsertWaitcnts pass.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_AMDGPU_AMDGPUNEWINSERTWAITCNTSUTILS_H
#define LLVM_LIB_TARGET_AMDGPU_AMDGPUNEWINSERTWAITCNTSUTILS_H

#include "AMDGPUWaitcntUtils.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/MC/MCRegister.h"
#include <optional>

namespace llvm {

class AAResults;
class GCNSubtarget;
class MachineFunction;
class MachineLoopInfo;
class MachineLoop;
class MachineOperand;
class MachineRegisterInfo;
class SIInstrInfo;
class SIRegisterInfo;

namespace AMDGPU {

//===----------------------------------------------------------------------===//
// Instruction Helpers
//===----------------------------------------------------------------------===//

bool isWaitInstr(MachineInstr &MI);

// ASYNCMARK and WAIT_ASYNCMARK are meta instructions that emit no hardware
// code but still need to be processed by this pass for async vmcnt tracking.
/// TODO docs
bool isNonWaitcntMetaInst(const MachineInstr &MI);

/// \returns the waits performed by the wait instruction \p MI (soft or hard)
/// on a target with ISA version \p IV.
/// \pre isWaitInstr(MI) and \p MI is not S_WAITCNT_lds_direct, whose wait
/// depends on the pending LDS DMAs.
/// WAIT_ASYNCMARK is decoded conservatively as a full drain of the counters
/// that track asynchronous operations. Legacy S_WAITCNT on gfx12+ decodes to
/// no wait.
Waitcnt decode(const MachineInstr &MI, const IsaVersion &IV);

/// \returns the start of the preceding waits of \p It: the maximal sequence of
/// wait instructions (isWaitInstr) and non-wait meta instructions
/// (isNonWaitcntMetaInst) right before \p It, within \p MBB. \returns \p It
/// if there are none.
MachineBasicBlock::instr_iterator
getPrecedingWaitsBegin(MachineBasicBlock &MBB,
                       MachineBasicBlock::instr_iterator It);

/// \returns true if the first non-meta instruction at or after \p It is
/// S_ENDPGM, continuing into the next blocks in layout order when the end of
/// \p MBB is reached.
bool isNextNonMetaEndpgm(MachineBasicBlock &MBB,
                         MachineBasicBlock::instr_iterator It);

/// \returns true if \p MI defines any registers covered by \p RUs.
bool definesAnyRUs(const SIRegisterInfo &TRI, const MachineInstr &MI,
                   const DenseSet<MCRegUnit> &RUs);

//===----------------------------------------------------------------------===//
// Register and memory dependency helpers
//===----------------------------------------------------------------------===//

/// \returns true if registers \p A and \p B overlap and can carry a
/// dependency. Registers outside of allocatable classes (e.g. EXEC, M0) never
/// do. SCC is the only exception: it only overlaps with itself.
bool trackedRegsOverlap(const SIRegisterInfo &TRI, MCRegister A, MCRegister B);

/// \returns true if \p MI is a memory access that only increments the vector
/// memory counter. Generic FLAT instructions may also access LDS and are
/// excluded.
bool updatesVMCntOnly(const MachineInstr &MI);

/// \returns true if \p ST supports point sample acceleration and \p MI is an
/// image instruction it may be applied to. Whether it is actually applied is
/// decided by the hardware, so this is conservative.
bool mayUsePointSampleAccel(const GCNSubtarget &ST, const MachineInstr &MI);

/// \returns the events that a VGPR written by the VMEM instruction \p MI is
/// pending on.
HWEvents getVGPRWriteEvents(const GCNSubtarget &ST, const SIInstrInfo &TII,
                            const MachineInstr &MI);

/// \returns the other 16-bit half of \p Reg if \p Reg is a 16-bit register,
/// or an invalid register otherwise.
MCRegister getOther16BitHalf(const SIRegisterInfo &TRI, MCRegister Reg);

/// Collects in \p Ops the operands of \p MI whose registers stay in use by
/// the hardware after \p MI issues, until EXP_CNT is decremented for \p MI:
/// the sources of stores, exports and GDS operations, and the destination of
/// LDS direct loads. Writing one of those registers before the counter
/// decrements is a write-after-read hazard.
void getEXPCntLockedOperands(const SIInstrInfo &TII, const SIRegisterInfo &TRI,
                             const MachineRegisterInfo &MRI,
                             const MachineInstr &MI,
                             SmallVectorImpl<const MachineOperand *> &Ops);

/// Collects in \p Ops the operands of \p MI whose registers depend on the
/// completion of \p MI on counter \p T, i.e. the registers a later
/// instruction must wait on \p T for before accessing them:
///  - EXP_CNT: see \ref getEXPCntLockedOperands.
///  - LOAD_CNT, SAMPLE_CNT, BVH_CNT: the explicit vector register defs.
///  - Other counters: all explicit defs.
/// Implicit operands are excluded because on memory instructions they only
/// model super-register liveness.
void getOperandsTrackedByCounter(const SIInstrInfo &TII,
                                 const SIRegisterInfo &TRI,
                                 const MachineRegisterInfo &MRI,
                                 const MachineInstr &MI, InstCounterType T,
                                 SmallVectorImpl<const MachineOperand *> &Ops);

/// \returns true if \p MI may access LDS memory written by the LDS DMA
/// instruction \p DMA. Only LDS and flat memory operands of \p MI are
/// considered. A memory operand without an IR value or alias info is assumed
/// to alias. Instructions without memory operands are assumed not to access
/// LDS.
bool mayAccessLDSWrittenByDMA(AAResults *AA, const MachineInstr &MI,
                              const MachineInstr &DMA);

/// \returns true if a store memory operand of \p MI refers to the same IR
/// value as a non-invariant load memory operand of \p Load. Two operands
/// without an IR value are considered the same.
bool mayStoreToLoadedAddress(const MachineInstr &MI, const MachineInstr &Load);

/// Decides where the "vccz recompute" workaround is needed.
///
/// There are two reasons why vccz (the hardware "vcc == 0" bit read by
/// S_CBRANCH_VCCZ/VCCNZ) might be stale; see
/// \ref GCNSubtarget::hasReadVCCZBug() and
/// \ref GCNSubtarget::partialVCCWritesUpdateVCCZ():
///  i.  CI/SI hardware bug: an SMEM load may complete and corrupt vccz at any
///      time. Before a vccz read, all pending SMEM must be waited for (handled
///      by the solver) and vccz recomputed.
///  ii. On targets before GFX10, a partial write to vcc (VCC_LO or VCC_HI) does
///      not update vccz. No wait is needed, only the recompute.
/// Recomputing is done by writing vcc back to itself (see \ref
/// emitVCCZRecompute).
///
/// Usage: create one tracker per basic block walk and call visit() on every
/// instruction of the block, in order, that is neither a wait nor a meta
/// instruction. The tracker only carries intra-block state.
/// It starts every block assuming vccz may be stale (a predecessor may have
/// written vcc and then issued an SMEM load), so there is nothing to join
/// across blocks and no fixpoint concern: the result is a pure function of the
/// block's instructions plus, for the bug (i) half, "is an SMEM pending".
class VCCZRecomputeTracker {
public:
  VCCZRecomputeTracker(const GCNSubtarget &ST, const SIInstrInfo &TII);

  /// Updates the tracked state for \p MI.
  /// \param MI the MachineInstr
  /// \param HasPendingSMEM True if there is an outstanding SMEM_ACCESS event.
  /// \pre this assumes \p MI has already been analyzed, so if \p MI is the one
  /// to cause the SMEM_ACCESS event, it should set \p HasPendingSMEM.
  /// \returns true if a vccz recompute must be emitted right before \p MI,
  bool visit(const MachineInstr &MI, bool HasPendingSMEM);

private:
  const SIInstrInfo &TII;
  bool VCCZCorruptionBug;
  bool VCCZNotUpdatedByPartialWrites;
  bool MustRecomputeVCCZ = true;
};

/// Emits the vccz recompute (`vcc = S_MOV vcc`, with the wave-size appropriate
/// opcode) right before \p InsertBefore. Any write to vcc updates vccz, so
/// writing back the value just read restores it.
void emitVCCZRecompute(MachineBasicBlock &MBB,
                       MachineBasicBlock::instr_iterator InsertBefore,
                       const GCNSubtarget &ST, const SIInstrInfo &TII,
                       const SIRegisterInfo &TRI);

/// Inserts S_DCACHE_WB before every S_ENDPGM / SI_RETURN_TO_EPILOG of \p MF
/// that is not already preceded (in its block) by one, if \p MF contains
/// scalar stores. Scalar stores are written to the scalar cache, which must be
/// flushed before the wave terminates, or the next wave reusing the same
/// scratch memory can be clobbered.
/// \returns true if the MIR was modified.
bool insertScalarStoreCacheFlushes(MachineFunction &MF, const GCNSubtarget &ST,
                                   const SIInstrInfo &TII);

/// How VGPRs are released before the wave ends (see \ref getVGPRDeallocMode).
enum class VGPRDeallocMode {
  /// Nothing is emitted.
  None,
  /// Dynamic VGPR mode: `S_ALLOC_VGPR 0` before every S_ENDPGM(_SAVED).
  Dynamic,
  /// `S_SENDMSG dealloc_vgprs` (preceded by `S_NOP 0` if the target requires
  /// it) before the S_ENDPGM(_SAVED) that are safe.
  Message,
};

/// \returns How \p MF releases its VGPRs before S_ENDPGM.
VGPRDeallocMode getVGPRDeallocMode(const MachineFunction &MF,
                                   const GCNSubtarget &ST,
                                   const SIRegisterInfo &TRI, bool OptNone);

/// Emits the VGPR release for the S_ENDPGM(_SAVED) \p EndPgm, right before it.
/// \param EndPgm The S_ENDPGM instruction.
/// \param Mode The dealloc mode provided by \ref getVGPRDeallocMode
/// \param SafeToMessage Whether sending the dealloc message is safe at \p
///                      EndPgm (no scratch stores outstanding, but some stores
///                      in flight). Only consulted in message mode.
/// \returns true if something was emitted.
bool emitVGPRDealloc(MachineInstr &EndPgm, VGPRDeallocMode Mode,
                     bool SafeToMessage, const GCNSubtarget &ST,
                     const SIInstrInfo &TII);

/// Represents a solution found by the solver for a MachineFunction.
/// The solver does not mutate the code at all, it creates these objects which
/// are then applied to the code.
class Solution {
public:
  struct BasicBlockSolution {
    // Map of MachineInstr to the Waitcnts that must be inserted before them.
    DenseMap<const MachineInstr *, Waitcnt> Before;

    // Waitcnt to insert at the end of this MBB.
    // Only necessary if this MBB has no terminator to which we can attach the
    // waitcnt.
    std::optional<Waitcnt> AtEnd;

    // S_ENDPGM instructions that need an `S_NOP 0` between the wait before
    // them and themselves (forced wait after an always-GDS instruction).
    DenseSet<const MachineInstr *> NopAfterWait;

    // Same as NopAfterWait, for AtEnd (S_ENDPGM in a later block).
    bool NopAfterAtEnd = false;

    // Instructions (S_CBRANCH_VCCZ/VCCNZ) before which vccz must be recomputed
    // (see VCCZRecomputeTracker). Emitted after the waits of the instruction,
    // so that it ends up between the wait and the branch.
    DenseSet<const MachineInstr *> RecomputeVCCZBefore;

    // Every S_ENDPGM / S_ENDPGM_SAVED of the block, with whether sending the
    // dealloc VGPRs message is safe at that point: stores are in flight (so
    // there is something to overlap with) and none is a scratch store (the
    // message releases the VGPRs the scratch store still reads).
    DenseMap<const MachineInstr *, bool> EndPgmSafeToMessage;

    bool operator==(const BasicBlockSolution &Other) const {
      return Before == Other.Before && AtEnd == Other.AtEnd &&
             NopAfterWait == Other.NopAfterWait &&
             NopAfterAtEnd == Other.NopAfterAtEnd &&
             RecomputeVCCZBefore == Other.RecomputeVCCZBefore &&
             EndPgmSafeToMessage == Other.EndPgmSafeToMessage;
    }
  };

  /// \returns the solution of \p MBB, or nullptr if \p MBB was never
  /// visited (unreachable).
  const BasicBlockSolution *lookup(const MachineBasicBlock &MBB) const {
    auto It = Solutions.find(&MBB);
    return It == Solutions.end() ? nullptr : &It->second;
  }

  const BasicBlockSolution &operator[](const MachineBasicBlock &MBB) const {
    return Solutions.at(&MBB);
  }

  BasicBlockSolution &operator[](const MachineBasicBlock &MBB) {
    return Solutions[&MBB];
  }

  auto begin() { return Solutions.begin(); }
  auto begin() const { return Solutions.begin(); }

  auto end() { return Solutions.end(); }
  auto end() const { return Solutions.end(); }

  /// Forget all about \p MBB: erase all entries that mention MBB.
  void forget(const MachineBasicBlock &MBB) { Solutions.erase(&MBB); }

private:
  DenseMap<const MachineBasicBlock *, BasicBlockSolution> Solutions;
};

/// Utility to visit a MachineFunction in reverse post order, with some extras.
class WaitcntRPOInfo {
public:
  WaitcntRPOInfo(MachineFunction &MF);

  auto begin() { return RPO.begin(); }
  auto begin() const { return RPO.begin(); }

  auto end() { return RPO.end(); }
  auto end() const { return RPO.end(); }

  /// \returns blocks where at least one successor is lower in the RPO order.
  const DenseSet<MachineBasicBlock *> &getRetreatingBlocks() const {
    return RetreatingBlocks;
  }

  unsigned getRPOIndex(const MachineBasicBlock &MBB) const {
    unsigned Res = RPOIndexes.at(&MBB);
    assert(getFromRPOIndex(Res) == &MBB);
    return Res;
  }

  unsigned getNumBlocks() const { return RPO.size(); }

  MachineBasicBlock *getFromRPOIndex(unsigned K) const { return RPO[K]; }

private:
  /// MBBs in RPO order, mapped to their RPO index.
  SmallVector<MachineBasicBlock *> RPO;
  DenseMap<const MachineBasicBlock *, unsigned> RPOIndexes;
  DenseSet<MachineBasicBlock *> RetreatingBlocks;
};

/// Using the information provided by WaitcntRPOInfo, this class implements a
/// smart reverse post order worklist.
///
/// The worklist works using an underlying BitVector so the next item in the
/// worklist is always the one with the lowest RPO index.
/// This is an efficiency improvement over classic worklists that just append
/// new elements at the back, and can help save some iterations.
class RPOWorklist {
public:
  RPOWorklist(const WaitcntRPOInfo &RPO);

  MachineBasicBlock *pop();
  void push(const MachineBasicBlock *MBB);

private:
  const WaitcntRPOInfo &RPO;
  BitVector Worklist;
};

/// This class wraps around MachineLoopInfo and exposes all the information that
/// may be needed by the solver when dealing with loop pre-headers.
class WaitcntLoopPreheaderInfo {
public:
  WaitcntLoopPreheaderInfo(const MachineFunction &MF,
                           const MachineLoopInfo &MLI)
      : MF(MF), MLI(MLI) {
    init();
  }

  struct Entry {
    bool HasVMemLoad;
    bool HasVMemStore;
    bool LoadedValueUsedInLoop = false;
    DenseSet<MCRegUnit> UsedVectorUnits;
  };

  /// \returns Iff \p MBB is a loop pre-header, return information about that
  /// pre-header.
  const WaitcntLoopPreheaderInfo::Entry *
  getPreheaderInfo(const MachineBasicBlock &MBB) const;

private:
  void init();

  const MachineFunction &MF;
  const MachineLoopInfo &MLI;

  DenseMap<const MachineLoop *, Entry> Entries;
};

/// The decoded preceding waits of an instruction (see getPrecedingWaitsBegin),
/// accumulated while walking a block.
struct PrecedingWaits {
  Waitcnt CombinedWaits;
  SmallVector<Waitcnt> SoftWaits;
  bool SeenLDSDirectWait = false;

  /// Add a wait instr \p MI, decoded for ISA version \p IV.
  void add(MachineInstr &MI, const IsaVersion &IV);
};

} // namespace AMDGPU
} // namespace llvm

#endif // LLVM_LIB_TARGET_AMDGPU_AMDGPUNEWINSERTWAITCNTS_H
