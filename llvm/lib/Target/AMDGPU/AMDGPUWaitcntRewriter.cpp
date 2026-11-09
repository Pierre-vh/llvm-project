//===- AMDGPUWaitcntRewriter.cpp --------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Port of the MIR-rewriting half of SIInsertWaitcnts
// (applyPreexistingWaitcnt, createNewWaitcnt and the VINTERP part of
// generateWaitcnt), without the state-dependent simplification, which the
// solver has already done.
//
//===----------------------------------------------------------------------===//

#include "AMDGPUWaitcntRewriter.h"
#include "AMDGPUNewInsertWaitcntsUtils.h"
#include "GCNSubtarget.h"
#include "SIInstrInfo.h"
#include "Utils/AMDGPUBaseInfo.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"

using namespace llvm;
using namespace llvm::AMDGPU;

/// Sets the simm16 operand of \p MI to \p Imm. \returns true if it changed.
static bool setSImm16(MachineInstr &MI, unsigned Imm) {
  int Idx = getNamedOperandIdx(MI.getOpcode(), AMDGPU::OpName::simm16);
  assert(Idx >= 0 && "wait instruction without simm16");
  MachineOperand &MO = MI.getOperand(Idx);
  if (MO.getImm() == static_cast<int64_t>(Imm))
    return false;
  MO.setImm(Imm);
  return true;
}

/// Turns a soft wait into the equivalent hard wait. \returns true if it
/// changed.
static bool promoteSoftWait(const SIInstrInfo &TII, MachineInstr &MI) {
  unsigned Opcode = SIInstrInfo::getNonSoftWaitcntOpcode(MI.getOpcode());
  if (Opcode == MI.getOpcode())
    return false;
  MI.setDesc(TII.get(Opcode));
  return true;
}

/// Updates the reused wait \p MI to \p Imm and promotes it. \returns true if
/// \p MI changed.
static bool updateWait(const SIInstrInfo &TII, MachineInstr &MI,
                       unsigned Imm) {
  bool Changed = setSImm16(MI, Imm);
  return promoteSoftWait(TII, MI) || Changed;
}

/// \returns the gfx12+ single-counter wait opcode (S_WAIT_*CNT) for \p T, the
/// inverse of counterTypeForInstr.
/// \pre The target has extended wait counts and counter \p T.
static unsigned getGFX12WaitInstr(InstCounterType T) {
  switch (T) {
  case LOAD_CNT:
    return AMDGPU::S_WAIT_LOADCNT;
  case DS_CNT:
    return AMDGPU::S_WAIT_DSCNT;
  case EXP_CNT:
    return AMDGPU::S_WAIT_EXPCNT;
  case STORE_CNT:
    return AMDGPU::S_WAIT_STORECNT;
  case SAMPLE_CNT:
    return AMDGPU::S_WAIT_SAMPLECNT;
  case BVH_CNT:
    return AMDGPU::S_WAIT_BVHCNT;
  case KM_CNT:
    return AMDGPU::S_WAIT_KMCNT;
  case X_CNT:
    return AMDGPU::S_WAIT_XCNT;
  case ASYNC_CNT:
    return AMDGPU::S_WAIT_ASYNCCNT;
  case TENSOR_CNT:
    return AMDGPU::S_WAIT_TENSORCNT;
  default:
    llvm_unreachable("counter has no single-counter wait instruction");
  }
}

WaitcntRewriter::WaitcntRewriter(const GCNSubtarget &ST,
                                 ArrayRef<AMDGPUInstCounter> Counters)
    : ST(ST), TII(*ST.getInstrInfo()), IV(getIsaVersion(ST.getCPU())),
      Counters(Counters) {}

Waitcnt WaitcntRewriter::restrictToCounters(Waitcnt W) const {
  Waitcnt Res;
  for (const AMDGPUInstCounter &C : Counters)
    Res.set(C.getType(), W.get(C.getType()));
  return Res;
}

bool WaitcntRewriter::rewrite(MachineBasicBlock &MBB,
                              MachineBasicBlock::instr_iterator It, Waitcnt W,
                              bool NopAfter) {
  W = restrictToCounters(W);
  MachineBasicBlock::instr_iterator Begin = getPrecedingWaitsBegin(MBB, It);

  // Bundles: like the old pass, the walk visits instructions inside bundles
  // and waits are inserted with instr_iterators, right before the bundled
  // instruction.
  bool Modified = ST.hasExtendedWaitCounts() ? reuseGFX12Plus(Begin, It, W)
                                             : reusePreGFX12(Begin, It, W);
  Modified |= foldIntoVINTERP(MBB, It, W);
  Modified |= ST.hasExtendedWaitCounts() ? emitGFX12Plus(MBB, It, W)
                                         : emitPreGFX12(MBB, It, W);

  if (NopAfter) {
    BuildMI(MBB, It, MBB.findDebugLoc(It), TII.get(AMDGPU::S_NOP)).addImm(0);
    Modified = true;
  }
  return Modified;
}

bool WaitcntRewriter::reusePreGFX12(MachineBasicBlock::instr_iterator Begin,
                                    MachineBasicBlock::instr_iterator It,
                                    Waitcnt &W) {
  // SIW:1633-1772.
  bool Modified = false;
  MachineInstr *WaitcntMI = nullptr;
  MachineInstr *VsCntMI = nullptr;

  for (MachineInstr &II : make_early_inc_range(make_range(Begin, It))) {
    if (isNonWaitcntMetaInst(II))
      continue;

    switch (SIInstrInfo::getNonSoftWaitcntOpcode(II.getOpcode())) {
    case AMDGPU::WAIT_ASYNCMARK:
      break; // Shows up in the assembly as a comment: keep it.
    case AMDGPU::S_WAITCNT:
    case AMDGPU::S_WAITCNT_VSCNT: {
      bool IsVsCnt = SIInstrInfo::getNonSoftWaitcntOpcode(II.getOpcode()) ==
                     AMDGPU::S_WAITCNT_VSCNT;
      MachineInstr *&Kept = IsVsCnt ? VsCntMI : WaitcntMI;
      if (!Kept) {
        Kept = &II;
        break;
      }
      II.eraseFromParent();
      Modified = true;
      break;
    }
    case AMDGPU::S_WAITCNT_lds_direct:
      II.eraseFromParent();
      Modified = true;
      break;
    default:
      llvm_unreachable("unexpected instruction in pre-gfx12 preceding waits");
    }
  }

  // A kept wait with nothing left to wait for is erased if soft. The old pass
  // keeps hard ones (updated to "no wait").
  const auto Finish = [&](MachineInstr *MI, bool HasWait, unsigned Imm) {
    if (!MI)
      return;
    if (!HasWait && SIInstrInfo::getNonSoftWaitcntOpcode(MI->getOpcode()) !=
                        MI->getOpcode()) {
      MI->eraseFromParent();
      Modified = true;
      return;
    }
    Modified |= updateWait(TII, *MI, Imm);
  };

  if (WaitcntMI) {
    Finish(WaitcntMI, W.hasWaitExceptStoreCnt(), encodeWaitcnt(IV, W));
    W.clear(LOAD_CNT);
    W.clear(EXP_CNT);
    W.clear(DS_CNT);
  }
  if (VsCntMI) {
    Finish(VsCntMI, W.hasWaitStoreCnt(), W.get(STORE_CNT));
    W.clear(STORE_CNT);
  }
  return Modified;
}

bool WaitcntRewriter::reuseGFX12Plus(MachineBasicBlock::instr_iterator Begin,
                                     MachineBasicBlock::instr_iterator It,
                                     Waitcnt &W) {
  // SIW:1884-2185, minus S_WAITCNT_DEPCTR, which is not part of the preceding waits
  // here (TODO(gfx12+, expert mode)).
  bool Modified = false;
  MachineInstr *LoadDsMI = nullptr;
  MachineInstr *StoreDsMI = nullptr;
  MachineInstr *SingleMIs[NUM_INST_CNTS] = {};

  const auto KeepFirst = [&](MachineInstr *&Kept, MachineInstr &II) {
    if (!Kept) {
      Kept = &II;
      return;
    }
    II.eraseFromParent();
    Modified = true;
  };

  for (MachineInstr &II : make_early_inc_range(make_range(Begin, It))) {
    if (isNonWaitcntMetaInst(II))
      continue;

    unsigned Opcode = SIInstrInfo::getNonSoftWaitcntOpcode(II.getOpcode());
    switch (Opcode) {
    case AMDGPU::S_WAITCNT:      // Legacy: left alone (SIW:1922).
    case AMDGPU::WAIT_ASYNCMARK: // Kept as an assembly comment.
      break;
    case AMDGPU::S_WAITCNT_lds_direct:
      II.eraseFromParent();
      Modified = true;
      break;
    case AMDGPU::S_WAIT_LOADCNT_DSCNT:
      KeepFirst(LoadDsMI, II);
      break;
    case AMDGPU::S_WAIT_STORECNT_DSCNT:
      KeepFirst(StoreDsMI, II);
      break;
    default: {
      std::optional<InstCounterType> T = counterTypeForInstr(Opcode);
      assert(T && "unexpected instruction in gfx12+ preceding waits");
      KeepFirst(SingleMIs[*T], II);
      break;
    }
    }
  }

  const auto EraseMI = [&](MachineInstr *&MI) {
    if (!MI)
      return;
    MI->eraseFromParent();
    MI = nullptr;
    Modified = true;
  };

  // A combined wait is only kept if both of its counters need a wait.
  // Otherwise it is erased and single-counter waits are created instead.
  const auto ReuseCombined = [&](MachineInstr *&MI, InstCounterType T,
                                 unsigned Enc) {
    if (!MI)
      return;
    if (W.get(T) == ~0u || W.get(DS_CNT) == ~0u) {
      EraseMI(MI);
      return;
    }
    Modified |= updateWait(TII, *MI, Enc);
    W.clear(T);
    W.clear(DS_CNT);
  };
  ReuseCombined(LoadDsMI, LOAD_CNT, encodeLoadcntDscnt(IV, W));
  ReuseCombined(StoreDsMI, STORE_CNT, encodeStorecntDscnt(IV, W));

  // If DS and exactly one of LOAD/STORE remain, erase their single waits so
  // that emitGFX12Plus creates a combined wait instead.
  if (W.get(DS_CNT) != ~0u) {
    if (W.get(LOAD_CNT) != ~0u) {
      EraseMI(SingleMIs[LOAD_CNT]);
      EraseMI(SingleMIs[DS_CNT]);
    } else if (W.get(STORE_CNT) != ~0u) {
      EraseMI(SingleMIs[STORE_CNT]);
      EraseMI(SingleMIs[DS_CNT]);
    }
  }

  for (InstCounterType T : inst_counter_types(NUM_EXTENDED_INST_CNTS)) {
    if (!SingleMIs[T])
      continue;
    if (W.get(T) == ~0u) {
      EraseMI(SingleMIs[T]);
      continue;
    }
    Modified |= updateWait(TII, *SingleMIs[T], W.get(T));
    W.clear(T);
  }
  return Modified;
}

bool WaitcntRewriter::foldIntoVINTERP(MachineBasicBlock &MBB,
                                      MachineBasicBlock::instr_iterator It,
                                      Waitcnt &W) {
  // SIW:2627-2640: the EXP_CNT wait goes into the VINTERP's waitexp operand.
  if (It == MBB.instr_end() || !SIInstrInfo::isVINTERP(*It) ||
      W.get(EXP_CNT) == ~0u)
    return false;

  MachineOperand *WaitExp = TII.getNamedOperand(*It, AMDGPU::OpName::waitexp);
  bool Modified = false;
  if (W.get(EXP_CNT) < WaitExp->getImm()) {
    WaitExp->setImm(W.get(EXP_CNT));
    Modified = true;
  }
  W.clear(EXP_CNT);
  return Modified;
}

bool WaitcntRewriter::emitPreGFX12(MachineBasicBlock &MBB,
                                   MachineBasicBlock::instr_iterator It,
                                   const Waitcnt &W) {
  // SIW:1774-1882, without the profiling expansion.
  const DebugLoc &DL = MBB.findDebugLoc(It);
  bool Modified = false;

  if (W.hasWaitExceptStoreCnt()) {
    BuildMI(MBB, It, DL, TII.get(AMDGPU::S_WAITCNT))
        .addImm(encodeWaitcnt(IV, W));
    Modified = true;
  }
  if (W.hasWaitStoreCnt()) {
    assert(ST.hasVscnt());
    BuildMI(MBB, It, DL, TII.get(AMDGPU::S_WAITCNT_VSCNT))
        .addReg(AMDGPU::SGPR_NULL, RegState::Undef)
        .addImm(W.get(STORE_CNT));
    Modified = true;
  }
  return Modified;
}

bool WaitcntRewriter::emitGFX12Plus(MachineBasicBlock &MBB,
                                    MachineBasicBlock::instr_iterator It,
                                    Waitcnt W) {
  // SIW:2187-2275, without the profiling expansion.
  const DebugLoc &DL = MBB.findDebugLoc(It);
  bool Modified = false;

  // Prefer the combined waits when DS_CNT is involved.
  if (W.get(DS_CNT) != ~0u && W.get(LOAD_CNT) != ~0u) {
    BuildMI(MBB, It, DL, TII.get(AMDGPU::S_WAIT_LOADCNT_DSCNT))
        .addImm(encodeLoadcntDscnt(IV, W));
    W.clear(LOAD_CNT);
    W.clear(DS_CNT);
    Modified = true;
  } else if (W.get(DS_CNT) != ~0u && W.get(STORE_CNT) != ~0u) {
    BuildMI(MBB, It, DL, TII.get(AMDGPU::S_WAIT_STORECNT_DSCNT))
        .addImm(encodeStorecntDscnt(IV, W));
    W.clear(STORE_CNT);
    W.clear(DS_CNT);
    Modified = true;
  }

  for (InstCounterType T : inst_counter_types(NUM_EXTENDED_INST_CNTS)) {
    if (W.get(T) == ~0u)
      continue;
    BuildMI(MBB, It, DL, TII.get(getGFX12WaitInstr(T))).addImm(W.get(T));
    Modified = true;
  }

  // Expert scheduling mode counters share S_WAITCNT_DEPCTR. VA_VDST_RD and
  // VA_VDST_WR map to a single hardware field.
  if (W.hasWaitDepctr()) {
    unsigned Enc = DepCtr::encodeFieldVmVsrc(W.get(VM_VSRC), ST);
    Enc = DepCtr::encodeFieldVaVdst(
        Enc, std::min(W.get(VA_VDST_RD), W.get(VA_VDST_WR)));
    BuildMI(MBB, It, DL, TII.get(AMDGPU::S_WAITCNT_DEPCTR)).addImm(Enc);
    Modified = true;
  }
  return Modified;
}

Waitcnt WaitcntRewriter::decodePrecedingWaits(
    MachineBasicBlock &MBB, MachineBasicBlock::instr_iterator It) const {
  Waitcnt W;
  for (MachineInstr &II : make_range(getPrecedingWaitsBegin(MBB, It), It)) {
    if (!isWaitInstr(II))
      continue;
    // Only reachable before the rewrite (the rewrite erases it).
    if (SIInstrInfo::getNonSoftWaitcntOpcode(II.getOpcode()) ==
        AMDGPU::S_WAITCNT_lds_direct)
      continue;
    W = W.combined(decode(II, IV));
  }

  if (It != MBB.instr_end() && SIInstrInfo::isVINTERP(*It)) {
    W.add(EXP_CNT,
          TII.getNamedOperand(*It, AMDGPU::OpName::waitexp)->getImm());
  }
  return restrictToCounters(W);
}
