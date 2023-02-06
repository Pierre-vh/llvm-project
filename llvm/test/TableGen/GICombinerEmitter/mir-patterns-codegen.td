// RUN: llvm-tblgen -I %p/../../../include -gen-global-isel-combiner \
// RUN:     -combiners=MyCombiner %s \
// RUN:     -o - 2>&1 | FileCheck %s
// REQUIRES: asserts

include "llvm/Target/Target.td"
include "llvm/Target/GlobalISel/Combine.td"

def MyTargetISA : InstrInfo;
def MyTarget : Target { let InstructionSet = MyTargetISA; }

def dummy;

// Basic patterns.
def mirpat_undef_to_int_zero: GIMIRCombineRule<
  [{
    %imp = G_IMPLICIT_DEF
    %root = (G_AND | G_MUL) _, %imp
  }],
  [{
    %root = G_CONSTANT i32 0
  }]>;


def MyCombiner: GICombinerHelper<"GenMyCombiner", [
  mirpat_undef_to_int_zero
]>;
