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
/// that track asynchronous operations.
Waitcnt decode(const MachineInstr &MI, const IsaVersion &IV);

//===----------------------------------------------------------------------===//
// Register and memory dependency helpers
//===----------------------------------------------------------------------===//

/// \returns true if registers \p A and \p B overlap and can carry a
/// dependency. Registers outside of allocatable classes (e.g. EXEC, M0) never
/// do. SCC is the only exception: it only overlaps with itself.
bool trackedRegsOverlap(const SIRegisterInfo &TRI, MCRegister A, MCRegister B);

/// \returns true if \p MI is a memory access that only increments the vector
/// memory counter (LOAD_CNT and its split variants SAMPLE_CNT/BVH_CNT, or
/// STORE_CNT): non-FLAT VMEM instructions, and FLAT global/scratch
/// instructions. Generic FLAT instructions may also access LDS and are
/// excluded.
bool updatesVMCntOnly(const MachineInstr &MI);

/// \returns true if \p ST supports point sample acceleration and \p MI is an
/// image instruction it may be applied to. Whether it is actually applied is
/// decided by the hardware, so this is conservative.
bool mayUsePointSampleAccel(const GCNSubtarget &ST, const MachineInstr &MI);

/// \returns the events that a VGPR written by the VMEM instruction \p MI is
/// pending on, for the purpose of in-order write checks. This is the
/// simplified VMEM event of \p MI, plus VMEM_READ_ACCESS if point sample
/// acceleration may turn \p MI into a plain read.
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
/// Implicit operands are excluded: on memory instructions they only model
/// super-register liveness.
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

    bool operator==(const BasicBlockSolution &Other) const {
      return Before == Other.Before && AtEnd == Other.AtEnd;
    }
  };

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

  // isIdenticalTo -> just use ==

private:
  DenseMap<const MachineBasicBlock *, BasicBlockSolution> Solutions;
};

/// Utility to visit a MachineFunction in reverse post order, with some extras.
/// This is an info class, its
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

/// Information about all waitcnts encountered until a certain point when
/// iterating a function.
struct AggregatedWaitcnts {
  Waitcnt CombinedWaits;
  SmallVector<Waitcnt> SoftWaits;
  bool SeenLDSDirectWait = false;

  /// Add a wait instr \p MI, decoded for ISA version \p IV.
  void add(MachineInstr &MI, const IsaVersion &IV);
};

} // namespace AMDGPU
} // namespace llvm

#endif // LLVM_LIB_TARGET_AMDGPU_AMDGPUNEWINSERTWAITCNTS_H
