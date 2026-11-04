//===- AMDGPUWaitcntUtils.cpp ---------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "AMDGPUWaitcntUtils.h"
#include "GCNSubtarget.h"
#include "MCTargetDesc/AMDGPUMCTargetDesc.h"
#include "Utils/AMDGPUBaseInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

namespace llvm::AMDGPU {

static cl::opt<bool> ExpertSchedulingModeFlag(
    "amdgpu-expert-scheduling-mode",
    cl::desc("Enable expert scheduling mode 2 for all functions (GFX12+ only)"),
    cl::init(false), cl::Hidden);

bool isExpertSchedulingMode(const GCNSubtarget &ST, const Function &F) {
  return ST.hasExpertSchedulingMode() &&
         (ExpertSchedulingModeFlag.getNumOccurrences()
              ? ExpertSchedulingModeFlag
              : F.getFnAttribute("amdgpu-expert-scheduling-mode")
                    .getValueAsBool());
}

iota_range<InstCounterType> inst_counter_types(InstCounterType MaxCounter) {
  return enum_seq(LOAD_CNT, MaxCounter);
}

StringLiteral getInstCounterName(InstCounterType T) {
  switch (T) {
  case LOAD_CNT:
    return "LOAD_CNT";
  case DS_CNT:
    return "DS_CNT";
  case EXP_CNT:
    return "EXP_CNT";
  case STORE_CNT:
    return "STORE_CNT";
  case SAMPLE_CNT:
    return "SAMPLE_CNT";
  case BVH_CNT:
    return "BVH_CNT";
  case KM_CNT:
    return "KM_CNT";
  case X_CNT:
    return "X_CNT";
  case ASYNC_CNT:
    return "ASYNC_CNT";
  case TENSOR_CNT:
    return "TENSOR_CNT";
  case VA_VDST_RD:
    return "VA_VDST_RD";
  case VA_VDST_WR:
    return "VA_VDST_WR";
  case VM_VSRC:
    return "VM_VSRC";
  case NUM_INST_CNTS:
    return "NUM_INST_CNTS";
  }
  llvm_unreachable("Unhandled InstCounterType");
}

HardwareLimits::HardwareLimits(const IsaVersion &IV) {
  bool HasExtendedWaitCounts = IV.Major >= 12;
  if (HasExtendedWaitCounts) {
    LoadcntMax = getLoadcntBitMask(IV);
    DscntMax = getDscntBitMask(IV);
  } else {
    LoadcntMax = getVmcntBitMask(IV);
    DscntMax = getLgkmcntBitMask(IV);
  }
  ExpcntMax = getExpcntBitMask(IV);
  StorecntMax = getStorecntBitMask(IV);
  SamplecntMax = getSamplecntBitMask(IV);
  BvhcntMax = getBvhcntBitMask(IV);
  KmcntMax = getKmcntBitMask(IV);
  XcntMax = getXcntBitMask(IV);
  AsyncMax = getAsynccntBitMask(IV);
  VaVdstMax = DepCtr::getVaVdstBitMask();
  VmVsrcMax = DepCtr::getVmVsrcBitMask();
}

unsigned HardwareLimits::get(InstCounterType T) const {
  switch (T) {
  case AMDGPU::LOAD_CNT:
    return LoadcntMax;
  case AMDGPU::DS_CNT:
    return DscntMax;
  case AMDGPU::EXP_CNT:
    return ExpcntMax;
  case AMDGPU::STORE_CNT:
    return StorecntMax;
  case AMDGPU::SAMPLE_CNT:
    return SamplecntMax;
  case AMDGPU::BVH_CNT:
    return BvhcntMax;
  case AMDGPU::KM_CNT:
    return KmcntMax;
  case AMDGPU::X_CNT:
    return XcntMax;
  case AMDGPU::VA_VDST_RD:
  case AMDGPU::VA_VDST_WR:
    return VaVdstMax;
  case AMDGPU::VM_VSRC:
    return VmVsrcMax;
  default:
    return 0;
  }
}

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
void Waitcnt::dump() const { dbgs() << *this << '\n'; }
#endif

Waitcnt decodeWaitcnt(const IsaVersion &Version, unsigned Encoded) {
  Waitcnt Decoded;
  Decoded.set(LOAD_CNT, decodeVmcnt(Version, Encoded));
  Decoded.set(EXP_CNT, decodeExpcnt(Version, Encoded));
  Decoded.set(DS_CNT, decodeLgkmcnt(Version, Encoded));
  return Decoded;
}

unsigned encodeWaitcnt(const IsaVersion &Version, const Waitcnt &Decoded) {
  return encodeWaitcnt(Version, Decoded.get(LOAD_CNT), Decoded.get(EXP_CNT),
                       Decoded.get(DS_CNT));
}

Waitcnt decodeLoadcntDscnt(const IsaVersion &Version, unsigned LoadcntDscnt) {
  Waitcnt Decoded;
  Decoded.set(LOAD_CNT, decodeLoadcnt(Version, LoadcntDscnt));
  Decoded.set(DS_CNT, decodeDscnt(Version, LoadcntDscnt));
  return Decoded;
}

Waitcnt decodeStorecntDscnt(const IsaVersion &Version, unsigned StorecntDscnt) {
  Waitcnt Decoded;
  Decoded.set(STORE_CNT, decodeStorecnt(Version, StorecntDscnt));
  Decoded.set(DS_CNT, decodeDscnt(Version, StorecntDscnt));
  return Decoded;
}

unsigned encodeLoadcntDscnt(const IsaVersion &Version, const Waitcnt &Decoded) {
  return encodeLoadcntDscnt(Version, Decoded.get(LOAD_CNT),
                            Decoded.get(DS_CNT));
}

unsigned encodeStorecntDscnt(const IsaVersion &Version,
                             const Waitcnt &Decoded) {
  return encodeStorecntDscnt(Version, Decoded.get(STORE_CNT),
                             Decoded.get(DS_CNT));
}

std::optional<AMDGPU::InstCounterType> counterTypeForInstr(unsigned Opcode) {
  switch (Opcode) {
  case AMDGPU::S_WAIT_LOADCNT:
    return AMDGPU::LOAD_CNT;
  case AMDGPU::S_WAIT_EXPCNT:
    return AMDGPU::EXP_CNT;
  case AMDGPU::S_WAIT_STORECNT:
    return AMDGPU::STORE_CNT;
  case AMDGPU::S_WAIT_SAMPLECNT:
    return AMDGPU::SAMPLE_CNT;
  case AMDGPU::S_WAIT_BVHCNT:
    return AMDGPU::BVH_CNT;
  case AMDGPU::S_WAIT_DSCNT:
    return AMDGPU::DS_CNT;
  case AMDGPU::S_WAIT_KMCNT:
    return AMDGPU::KM_CNT;
  case AMDGPU::S_WAIT_XCNT:
    return AMDGPU::X_CNT;
  case AMDGPU::S_WAIT_ASYNCCNT:
    return AMDGPU::ASYNC_CNT;
  case AMDGPU::S_WAIT_TENSORCNT:
    return AMDGPU::TENSOR_CNT;
  default:
    return {};
  }
}

/// \return the name of \p T as printed by SIInsertWaitcnts, which uses the
/// legacy names (VM/LGKM/VS) before gfx12.
static StringRef getCounterName(const GCNSubtarget &ST, InstCounterType T) {
  if (!ST.hasExtendedWaitCounts()) {
    switch (T) {
    case LOAD_CNT:
      return "VM_CNT";
    case DS_CNT:
      return "LGKM_CNT";
    case STORE_CNT:
      return "VS_CNT";
    default:
      break;
    }
  }
  return getInstCounterName(T);
}

/// \return true if counter \p T exists on \p ST. Counters that are only
/// present on some subtargets are omitted from getCounters() on the others.
static bool hasCounter(const GCNSubtarget &ST, InstCounterType T) {
  switch (T) {
  case EXP_CNT:
    // Exports and LDSDIR also use EXP_CNT, so keep it when exports exist even
    // if image instructions were disabled.
    // FIXME: This is still incomplete on gfx13 with image instructions
    // disabled: GCNSubtarget::hasExportInsts() returns false there because
    // gfx13 has GFX1250Insts, even though the HasExportInsts assembler
    // predicate and LDSDIR (isGFX12PlusNot12_50) both include gfx13, so
    // EXP_CNT is wrongly dropped. Disabling image instructions on a target
    // that has them is an unlikely configuration, so we should reevaluate
    // whether to forbid it entirely (e.g. assert) instead of handling it here.
    return !ST.hasExtendedWaitCounts() || ST.hasImageInsts() ||
           ST.hasExportInsts();
  case SAMPLE_CNT:
  case BVH_CNT:
    // On gfx12+ these are only used by image instructions.
    return !ST.hasExtendedWaitCounts() || ST.hasImageInsts();
  case STORE_CNT:
    // Before gfx12, the store counter is a separate counter on gfx10/gfx11
    // only.
    return ST.hasExtendedWaitCounts() || ST.hasVscnt();
  case X_CNT:
    return ST.hasWaitXcnt();
  case ASYNC_CNT:
    // TODO: GFX13 has async LDS DMA instructions that use ASYNC_CNT but lacks
    // FeatureAsynccnt (and has a zero asynccnt bit width), so ASYNC_CNT is
    // omitted there. Fix the target definition.
    return ST.hasAsynccnt();
  case TENSOR_CNT:
    return ST.hasGFX1250Insts();
  default:
    return true;
  }
}

/// \return the set of events that \p T tracks on \p ST.
static HWEvents getCounterEvents(const GCNSubtarget &ST, InstCounterType T) {
  constexpr HWEvents ExportEvents =
      HWEvents::EXP_GPR_LOCK | HWEvents::GDS_GPR_LOCK | HWEvents::VMW_GPR_LOCK |
      HWEvents::EXP_PARAM_ACCESS | HWEvents::EXP_POS_ACCESS |
      HWEvents::EXP_LDS_ACCESS;
  constexpr HWEvents StoreEvents =
      HWEvents::VMEM_WRITE_ACCESS | HWEvents::SCRATCH_WRITE_ACCESS;

  if (!ST.hasExtendedWaitCounts()) {
    switch (T) {
    case LOAD_CNT: {
      HWEvents EVs = HWEvents::VMEM_READ_ACCESS |
                     HWEvents::VMEM_SAMPLER_READ_ACCESS |
                     HWEvents::VMEM_BVH_READ_ACCESS | HWEvents::VMEM_INV_ACCESS;
      // Without a separate store counter, stores are tracked by LOAD_CNT.
      if (!ST.hasVscnt())
        EVs |= StoreEvents;
      return EVs;
    }
    case DS_CNT:
      return HWEvents::SMEM_ACCESS | HWEvents::LDS_ACCESS |
             HWEvents::GDS_ACCESS | HWEvents::SQ_MESSAGE;
    case EXP_CNT:
      return ExportEvents;
    case STORE_CNT:
      return StoreEvents;
    default:
      return HWEvents::NONE;
    }
  }

  switch (T) {
  case LOAD_CNT:
    return HWEvents::VMEM_READ_ACCESS | HWEvents::VMEM_INV_ACCESS;
  case DS_CNT:
    return HWEvents::LDS_ACCESS | HWEvents::GDS_ACCESS;
  case EXP_CNT:
    return ExportEvents;
  case STORE_CNT:
    return StoreEvents;
  case SAMPLE_CNT:
    return HWEvents::VMEM_SAMPLER_READ_ACCESS;
  case BVH_CNT:
    return HWEvents::VMEM_BVH_READ_ACCESS;
  case KM_CNT:
    return HWEvents::SMEM_ACCESS | HWEvents::SQ_MESSAGE | HWEvents::SCC_WRITE;
  case X_CNT:
    return HWEvents::VMEM_GROUP | HWEvents::SMEM_GROUP;
  case ASYNC_CNT:
    return HWEvents::ASYNC_ACCESS;
  case TENSOR_CNT:
    return HWEvents::TENSOR_ACCESS;
  case VA_VDST_RD:
    return HWEvents::VGPR_CSMACC_READ | HWEvents::VGPR_DPMACC_READ |
           HWEvents::VGPR_TRANS_READ | HWEvents::VGPR_XDL_READ;
  case VA_VDST_WR:
    return HWEvents::VGPR_CSMACC_WRITE | HWEvents::VGPR_DPMACC_WRITE |
           HWEvents::VGPR_TRANS_WRITE | HWEvents::VGPR_XDL_WRITE;
  case VM_VSRC:
    return HWEvents::VGPR_LDS_READ | HWEvents::VGPR_FLAT_READ |
           HWEvents::VGPR_VMEM_READ;
  case NUM_INST_CNTS:
    break;
  }
  llvm_unreachable("Unhandled InstCounterType");
}

static unsigned getCounterLimit(const HardwareLimits &Limits,
                                InstCounterType T) {
  switch (T) {
  case ASYNC_CNT:
    // TODO: HardwareLimits::get() should handle ASYNC_CNT so this special case
    // can be removed. Note that SIInsertWaitcnts currently uses
    // HardwareLimits::get(), which returns 0 for ASYNC_CNT, so it effectively
    // treats ASYNC_CNT as unlimited (getLimit() - 1 wraps around).
    return Limits.AsyncMax;
  case TENSOR_CNT:
    // TODO: HardwareLimits has no limit for TENSOR_CNT; report it as unlimited
    // until the actual hardware limit is known and added there.
    return AMDGPUInstCounter::NoLimit;
  default:
    return Limits.get(T);
  }
}

SmallVector<AMDGPUInstCounter, NUM_INST_CNTS>
getCounters(const GCNSubtarget &ST, bool IsExpertMode) {
  InstCounterType MaxCounter = NUM_NORMAL_INST_CNTS;
  if (ST.hasExtendedWaitCounts())
    MaxCounter = IsExpertMode ? NUM_EXPERT_INST_CNTS : NUM_EXTENDED_INST_CNTS;

  HardwareLimits Limits(getIsaVersion(ST.getCPU()));
  SmallVector<AMDGPUInstCounter, NUM_INST_CNTS> Counters;
  for (InstCounterType T : inst_counter_types(MaxCounter)) {
    if (!hasCounter(ST, T))
      continue;
    // The index is the position in the result, not the InstCounterType, as
    // counters missing on this subtarget are skipped.
    Counters.emplace_back(Counters.size(), T, getCounterLimit(Limits, T),
                          getCounterName(ST, T), getCounterEvents(ST, T));
  }
  return Counters;
}

SmallVector<AMDGPUInstCounter, NUM_INST_CNTS>
getCounters(const MachineFunction &MF) {
  const auto &ST = MF.getSubtarget<GCNSubtarget>();
  return getCounters(ST, isExpertSchedulingMode(ST, MF.getFunction()));
}

} // namespace llvm::AMDGPU
