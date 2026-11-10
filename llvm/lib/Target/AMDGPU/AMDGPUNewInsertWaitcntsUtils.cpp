//===- AMDGPUNewInsertWaitcntsUtils.cpp -------------------------*- C++ -*-===//
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

#include "AMDGPUNewInsertWaitcntsUtils.h"
#include "GCNSubtarget.h"
#include "SIInstrInfo.h"
#include "SIRegisterInfo.h"
#include "Utils/AMDGPUBaseInfo.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/MachineLoopInfo.h"

namespace llvm {
namespace AMDGPU {

bool isWaitInstr(MachineInstr &MI) {
  unsigned Opcode = SIInstrInfo::getNonSoftWaitcntOpcode(MI.getOpcode());
  switch (Opcode) {
  case AMDGPU::S_WAITCNT:
  case AMDGPU::S_WAIT_LOADCNT_DSCNT:
  case AMDGPU::S_WAIT_STORECNT_DSCNT:
  case AMDGPU::S_WAITCNT_lds_direct:
  case AMDGPU::WAIT_ASYNCMARK:
    return true;
  case AMDGPU::S_WAITCNT_VSCNT:
    return MI.getOperand(0).isReg() &&
           MI.getOperand(0).getReg() == AMDGPU::SGPR_NULL;
  default:
    return AMDGPU::counterTypeForInstr(Opcode).has_value();
  }
}

bool isNonWaitcntMetaInst(const MachineInstr &MI) {
  switch (MI.getOpcode()) {
  case AMDGPU::ASYNCMARK:
  case AMDGPU::WAIT_ASYNCMARK:
    return false;
  default:
    return MI.isMetaInstruction();
  }
}

Waitcnt decode(const MachineInstr &MI, const IsaVersion &IV) {
  const unsigned Opcode = SIInstrInfo::getNonSoftWaitcntOpcode(MI.getOpcode());
  const auto GetImm = [&]() {
    int Idx = getNamedOperandIdx(MI.getOpcode(), AMDGPU::OpName::simm16);
    assert(Idx >= 0 && "wait instruction without simm16");
    return static_cast<unsigned>(MI.getOperand(Idx).getImm());
  };

  Waitcnt W;
  switch (Opcode) {
  case AMDGPU::S_WAITCNT:
    // Ignore S_WAITCNT on targets with extended counters.
    if (IV.Major >= 12)
      return W;
    return decodeWaitcnt(IV, GetImm());
  case AMDGPU::S_WAITCNT_VSCNT:
    assert(MI.getOperand(0).getReg() == AMDGPU::SGPR_NULL);
    W.set(STORE_CNT, GetImm());
    return W;
  case AMDGPU::S_WAIT_LOADCNT_DSCNT:
    return decodeLoadcntDscnt(IV, GetImm());
  case AMDGPU::S_WAIT_STORECNT_DSCNT:
    return decodeStorecntDscnt(IV, GetImm());
  case AMDGPU::WAIT_ASYNCMARK:
    // FIXME: ASYNCMARKs are not implemented so this is a safe approximation.
    W.set(LOAD_CNT, 0);
    W.set(ASYNC_CNT, 0);
    W.set(TENSOR_CNT, 0);
    return W;
  case AMDGPU::S_WAITCNT_lds_direct:
    llvm_unreachable("S_WAITCNT_lds_direct does not fit here");
  default:
    break;
  }

  // gfx12+ single-counter waits (S_WAIT_LOADCNT, S_WAIT_KMCNT, ...).
  std::optional<InstCounterType> T = counterTypeForInstr(Opcode);
  assert(T && "not a wait instruction");
  W.set(*T, GetImm());
  return W;
}

MachineBasicBlock::instr_iterator
getPrecedingWaitsBegin(MachineBasicBlock &MBB,
                       MachineBasicBlock::instr_iterator It) {
  MachineBasicBlock::instr_iterator Begin = It;
  while (Begin != MBB.instr_begin()) {
    MachineBasicBlock::instr_iterator Prev = std::prev(Begin);
    if (!isWaitInstr(*Prev) && !isNonWaitcntMetaInst(*Prev))
      break;
    Begin = Prev;
  }
  return Begin;
}

bool isNextNonMetaEndpgm(MachineBasicBlock &MBB,
                         MachineBasicBlock::instr_iterator It) {
  MachineFunction::iterator BlockIt = MBB.getIterator();
  MachineFunction::iterator BlockEnd = MBB.getParent()->end();
  while (true) {
    if (It == BlockIt->instr_end()) {
      if (++BlockIt == BlockEnd)
        return false;
      It = BlockIt->instr_begin();
      continue;
    }
    if (!It->isMetaInstruction())
      return It->getOpcode() == AMDGPU::S_ENDPGM;
    ++It;
  }
}

bool definesAnyRUs(const SIRegisterInfo &TRI, const MachineInstr &MI,
                   const DenseSet<MCRegUnit> &RUs) {
  for (const MachineOperand &Def : MI.defs()) {
    for (MCRegUnit RU : TRI.regunits(Def.getReg())) {
      if (RUs.contains(RU))
        return true;
    }
  }
  return false;
}

bool trackedRegsOverlap(const SIRegisterInfo &TRI, MCRegister A, MCRegister B) {
  if (!A.isValid() || !B.isValid())
    return false;
  if (A == AMDGPU::SCC || B == AMDGPU::SCC)
    return A == B;
  if (!TRI.isInAllocatableClass(A) || !TRI.isInAllocatableClass(B))
    return false;
  return TRI.regsOverlap(A, B);
}

bool updatesVMCntOnly(const MachineInstr &MI) {
  return (SIInstrInfo::isVMEM(MI) && !SIInstrInfo::isFLAT(MI)) ||
         SIInstrInfo::isFLATGlobal(MI) || SIInstrInfo::isFLATScratch(MI);
}

bool mayUsePointSampleAccel(const GCNSubtarget &ST, const MachineInstr &MI) {
  if (!ST.hasPointSampleAccel() || !SIInstrInfo::isMIMG(MI))
    return false;

  const MIMGInfo *Info = getMIMGInfo(MI.getOpcode());
  const MIMGBaseOpcodeInfo *BaseInfo = getMIMGBaseOpcodeInfo(Info->BaseOpcode);
  return BaseInfo->PointSampleAccel;
}

HWEvents getVGPRWriteEvents(const GCNSubtarget &ST, const SIInstrInfo &TII,
                            const MachineInstr &MI) {
  HWEvents Events = getSimplifiedVMEMEventsFor(MI, TII);
  if (mayUsePointSampleAccel(ST, MI))
    Events |= HWEvents::VMEM_READ_ACCESS;
  return Events;
}

MCRegister getOther16BitHalf(const SIRegisterInfo &TRI, MCRegister Reg) {
  const TargetRegisterClass *RC = TRI.getPhysRegBaseClass(Reg);
  if (!RC || TRI.getRegSizeInBits(*RC) != 16)
    return MCRegister();

  MCRegister Reg32 = TRI.get32BitRegister(Reg);
  return TRI.getSubReg(Reg32,
                       isHi16Reg(Reg, TRI) ? AMDGPU::lo16 : AMDGPU::hi16);
}

void getEXPCntLockedOperands(const SIInstrInfo &TII, const SIRegisterInfo &TRI,
                             const MachineRegisterInfo &MRI,
                             const MachineInstr &MI,
                             SmallVectorImpl<const MachineOperand *> &Ops) {
  const auto AddNamed = [&](AMDGPU::OpName Name) {
    if (const MachineOperand *Op = TII.getNamedOperand(MI, Name))
      Ops.push_back(Op);
  };
  const auto AddVectorUses = [&]() {
    for (const MachineOperand &Op : MI.all_uses())
      if (TRI.isVectorRegister(MRI, Op.getReg()))
        Ops.push_back(&Op);
  };

  if (SIInstrInfo::isDS(MI) && MI.mayLoadOrStore()) {
    // GDS operations protect their address, like exports.
    AddNamed(AMDGPU::OpName::addr);
    if (MI.mayStore()) {
      AddNamed(AMDGPU::OpName::data0);
      AddNamed(AMDGPU::OpName::data1);
    } else if (SIInstrInfo::isAtomicRet(MI) && !SIInstrInfo::isGWS(MI) &&
               MI.getOpcode() != AMDGPU::DS_APPEND &&
               MI.getOpcode() != AMDGPU::DS_CONSUME &&
               MI.getOpcode() != AMDGPU::DS_ORDERED_COUNT) {
      AddVectorUses();
    }
    return;
  }

  if (SIInstrInfo::isFLAT(MI)) {
    if (MI.mayStore() || SIInstrInfo::isAtomicRet(MI))
      AddNamed(AMDGPU::OpName::data);
    return;
  }

  if (SIInstrInfo::isMIMG(MI) || SIInstrInfo::isMUBUF(MI)) {
    if (MI.mayStore())
      Ops.push_back(&MI.getOperand(0));
    else if (SIInstrInfo::isAtomicRet(MI))
      AddNamed(AMDGPU::OpName::data);
    return;
  }

  if (SIInstrInfo::isMTBUF(MI)) {
    if (MI.mayStore())
      Ops.push_back(&MI.getOperand(0));
    return;
  }

  if (SIInstrInfo::isLDSDIR(MI)) {
    AddNamed(AMDGPU::OpName::vdst);
    return;
  }

  // Exports: the destination registers are temporaries that may be used as
  // sources after export patching, so they are locked too.
  if (SIInstrInfo::isEXP(MI)) {
    for (const MachineOperand &Def : MI.all_defs())
      if (TRI.isVGPR(MRI, Def.getReg()))
        Ops.push_back(&Def);
  }
  AddVectorUses();
}

void getOperandsTrackedByCounter(const SIInstrInfo &TII,
                                 const SIRegisterInfo &TRI,
                                 const MachineRegisterInfo &MRI,
                                 const MachineInstr &MI, InstCounterType T,
                                 SmallVectorImpl<const MachineOperand *> &Ops) {
  if (T == EXP_CNT) {
    getEXPCntLockedOperands(TII, TRI, MRI, MI, Ops);
    return;
  }

  // Track implicit SCC operand from S_BARRIER instructions.
  if (T == KM_CNT && SIInstrInfo::isSBarrierSCCWrite(MI.getOpcode())) {
    if (const MachineOperand *SCCDef =
            MI.findRegisterDefOperand(AMDGPU::SCC, /*TRI=*/nullptr))
      Ops.push_back(SCCDef);
    return;
  }

  const bool VectorOnly = T == LOAD_CNT || T == SAMPLE_CNT || T == BVH_CNT;
  for (const MachineOperand &Def : MI.defs()) {
    if (!VectorOnly || TRI.isVectorRegister(MRI, Def.getReg()))
      Ops.push_back(&Def);
  }
}

bool mayAccessLDSWrittenByDMA(AAResults *AA, const MachineInstr &MI,
                              const MachineInstr &DMA) {
  bool AccessesLDS = false;
  for (const MachineMemOperand *MMO : MI.memoperands()) {
    unsigned AS = MMO->getAddrSpace();
    if (AS != AMDGPUAS::LOCAL_ADDRESS && AS != AMDGPUAS::FLAT_ADDRESS)
      continue;
    if (!MMO->getValue() || !MMO->getAAInfo())
      return true;
    AccessesLDS = true;
  }

  return AccessesLDS && MI.mayAlias(AA, DMA, /*UseTBAA=*/true);
}

bool mayStoreToLoadedAddress(const MachineInstr &MI, const MachineInstr &Load) {
  for (const MachineMemOperand *StoreMMO : MI.memoperands()) {
    if (!StoreMMO->isStore())
      continue;
    for (const MachineMemOperand *LoadMMO : Load.memoperands()) {
      if (LoadMMO->isLoad() && !LoadMMO->isInvariant() &&
          LoadMMO->getValue() == StoreMMO->getValue())
        return true;
    }
  }
  return false;
}

WaitcntRPOInfo::WaitcntRPOInfo(MachineFunction &MF) {
  DenseSet<MachineBasicBlock *> Seen;
  unsigned RPOIdx = 0;
  for (MachineBasicBlock *MBB :
       ReversePostOrderTraversal<MachineFunction *>(&MF)) {
    Seen.insert(MBB);
    for (MachineBasicBlock *Succ : MBB->successors()) {
      if (Seen.contains(Succ)) {
        RetreatingBlocks.insert(MBB);
        break;
      }
    }
    RPOIndexes[MBB] = RPOIdx++;
    RPO.push_back(MBB);
  }

  assert(RPOIndexes.size() == RPO.size());
}

RPOWorklist::RPOWorklist(const WaitcntRPOInfo &RPO) : RPO(RPO) {
  Worklist.resize(RPO.getNumBlocks(), 1);
}

MachineBasicBlock *RPOWorklist::pop() {
  int Next = Worklist.find_first();
  if (Next == -1)
    return nullptr;

  Worklist[Next] = false;
  return RPO.getFromRPOIndex(Next);
}

void RPOWorklist::push(const MachineBasicBlock *MBB) {
  Worklist[RPO.getRPOIndex(*MBB)] = true;
}

const WaitcntLoopPreheaderInfo::Entry *
WaitcntLoopPreheaderInfo::getPreheaderInfo(const MachineBasicBlock &MBB) const {
  // MBB is outside the loop it preheads: look the loop up via its successor.
  // MBB may itself be inside an outer loop (preheader of an inner loop).
  const MachineBasicBlock *Succ = MBB.getSingleSuccessor();
  if (!Succ)
    return nullptr;

  const MachineLoop *ML = MLI.getLoopFor(Succ);
  if (!ML || ML->getLoopPreheader() != &MBB)
    return nullptr;

  auto It = Entries.find(ML);
  if (It == Entries.end())
    return nullptr;
  return &It->second;
}

static bool isVMEMOrFlatVMEM(const SIInstrInfo &TII, const MachineInstr &MI) {
  if (SIInstrInfo::isFLAT(MI))
    return TII.mayAccessVMEMThroughFlat(MI);
  return SIInstrInfo::isVMEM(MI);
}

void WaitcntLoopPreheaderInfo::init() {
  const GCNSubtarget &ST = MF.getSubtarget<GCNSubtarget>();
  const SIInstrInfo &TII = *ST.getInstrInfo();
  const SIRegisterInfo &TRI = *ST.getRegisterInfo();
  const MachineRegisterInfo &MRI = MF.getRegInfo();

  // TODO: Spin up new agent with previous context to implement this.
}

void PrecedingWaits::add(MachineInstr &MI, const IsaVersion &IV) {
  assert(isWaitInstr(MI));

  unsigned Opcode = SIInstrInfo::getNonSoftWaitcntOpcode(MI.getOpcode());
  bool IsSoft = (Opcode != MI.getOpcode());

  if (Opcode == AMDGPU::S_WAITCNT_lds_direct) {
    SeenLDSDirectWait = true;
    return;
  }

  Waitcnt W = decode(MI, IV);
  if (IsSoft)
    SoftWaits.push_back(W);
  else
    CombinedWaits = CombinedWaits.combined(W);
}

} // namespace AMDGPU
} // namespace llvm
