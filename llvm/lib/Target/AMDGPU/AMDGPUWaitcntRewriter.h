//===- AMDGPUWaitcntRewriter.h ----------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// Materializes a wait (\ref AMDGPU::Waitcnt) in front of an instruction by
/// rewriting the wait instructions already there. This is purely syntactic:
/// it knows nothing about pending events, and emits exactly the wait it is
/// given.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_AMDGPU_AMDGPUWAITCNTREWRITER_H
#define LLVM_LIB_TARGET_AMDGPU_AMDGPUWAITCNTREWRITER_H

#include "AMDGPUWaitcntUtils.h"
#include "llvm/CodeGen/MachineBasicBlock.h"

namespace llvm {

class GCNSubtarget;
class SIInstrInfo;

namespace AMDGPU {

/// Rewrites the preceding waits of a position: the maximal sequence of wait
/// instructions and non-wait meta instructions that ends at that position
/// (see getPrecedingWaitsBegin).
///
/// Existing wait instructions are reused in place, like SIInsertWaitcnts does:
/// the first instruction of each kind is updated (and promoted from soft to
/// hard), the others are erased, and new instructions are only created for
/// the remaining counters, right before the position. WAIT_ASYNCMARK is kept,
/// S_WAITCNT_lds_direct is erased, and legacy S_WAITCNT on targets with
/// extended wait counts is left untouched.
class WaitcntRewriter {
public:
  /// \p Counters are the counters available on \p ST. Waits on other counters
  /// are ignored.
  WaitcntRewriter(const GCNSubtarget &ST, ArrayRef<AMDGPUInstCounter> Counters);

  /// Rewrites the wait instructions that precede \p It in \p MBB so that they
  /// wait for exactly \p W, restricted to the available counters. Existing
  /// wait instructions are reused, and new ones are inserted right before
  /// \p It for the counters they cannot encode, including when there are none.
  /// If \p It is a VINTERP instruction, its `waitexp` operand may absorb the
  /// EXP_CNT wait instead.
  /// If \p NopAfter, an `S_NOP 0` is inserted right before \p It.
  /// \returns true if the MIR changed.
  bool rewrite(MachineBasicBlock &MBB, MachineBasicBlock::instr_iterator It,
               Waitcnt W, bool NopAfter);

  /// \returns the wait performed by the wait instructions that precede \p It in
  /// \p MBB, restricted to the available counters.
  /// If \p It is a VINTERP instruction, this also includes the wait from the
  /// `waitexp` operand.
  Waitcnt decodePrecedingWaits(MachineBasicBlock &MBB,
                               MachineBasicBlock::instr_iterator It) const;

private:
  /// \returns \p W without the waits on counters that are not available.
  Waitcnt restrictToCounters(Waitcnt W) const;

  /// Reuses the existing wait instructions in [\p Begin, \p It) for the
  /// counters they can encode, clearing those counters from \p W.
  bool reusePreGFX12(MachineBasicBlock::instr_iterator Begin,
                     MachineBasicBlock::instr_iterator It, Waitcnt &W);
  bool reuseGFX12Plus(MachineBasicBlock::instr_iterator Begin,
                      MachineBasicBlock::instr_iterator It, Waitcnt &W);

  /// Folds the EXP_CNT wait of \p W into the VINTERP at \p It, if any.
  bool foldIntoVINTERP(MachineBasicBlock &MBB,
                       MachineBasicBlock::instr_iterator It, Waitcnt &W);

  /// Creates new wait instructions before \p It for all of \p W.
  bool emitPreGFX12(MachineBasicBlock &MBB,
                    MachineBasicBlock::instr_iterator It, const Waitcnt &W);
  bool emitGFX12Plus(MachineBasicBlock &MBB,
                     MachineBasicBlock::instr_iterator It, Waitcnt W);

  const GCNSubtarget &ST;
  const SIInstrInfo &TII;
  const IsaVersion IV;
  ArrayRef<AMDGPUInstCounter> Counters;
};

} // namespace AMDGPU
} // namespace llvm

#endif // LLVM_LIB_TARGET_AMDGPU_AMDGPUWAITCNTREWRITER_H
