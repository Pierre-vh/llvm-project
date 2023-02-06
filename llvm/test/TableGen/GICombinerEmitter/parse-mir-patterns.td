// RUN: not llvm-tblgen -I %p/../../../include -gen-global-isel-combiner \
// RUN:     -combiners=MyCombiner -gicombiner-mir-patterns-dump-parse %s \
// RUN:     -o - 2>&1 | FileCheck %s
// REQUIRES: asserts

include "llvm/Target/Target.td"
include "llvm/Target/GlobalISel/Combine.td"

def MyTargetISA : InstrInfo;
def MyTarget : Target { let InstructionSet = MyTargetISA; }

def dummy;

// CHECK: empty_patterns.match:1:1: error: pattern is empty
def empty_patterns: GIMIRCombineRule<
  [{

  }],
  "">;

// CHECK: use_before_def.match:2:32: error: %imp cannot be used before its definition
// CHECK: use_before_def.match:3:5: note: %imp is defined here
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def use_before_def: GIMIRCombineRule<
  [{
    %root = (G_AND | G_MUL) _, %imp
    %imp = G_IMPLICIT_DEF
  }],
  [{
    %root = G_CONSTANT i19 0
  }]>;

// CHECK: invalid_redef.match:3:5: error: illegal redefinition of %imp
// CHECK: invalid_redef.match:2:5: note: %imp is first defined here
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def invalid_redef: GIMIRCombineRule<
  [{
    %imp = G_IMPLICIT_DEF
    %imp = G_IMPLICIT_DEF
  }],
  [{
    %root = G_CONSTANT i16 0
  }]>;

// CHECK: inconsistent_types.match:3:19: error: invalid type for %foo: s32 but register has type s64
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def inconsistent_types: GIMIRCombineRule<
  [{
    %foo:(s64) = G_CONSTANT i74 0
    %root = G_AND %foo:(s32), %livein
  }],
  [{
    %root = G_AND %bar:(s64), _
    %root = G_AND %bar:(s32), _
  }]>;

// CHECK: inconsistent_commutable.match:2:5: error: invalid pattern: G_FDIV and G_MUL have different values for 'isCommutable'
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def inconsistent_commutable: GIMIRCombineRule<
  [{
    %root = (G_FDIV | G_MUL) _, _
  }],
  [{
    %root = G_CONSTANT i16 1
  }]>;

// CHECK: inconsistent_types_liveins.match:3:16: error: invalid type for %bar: s32 but register has type s64
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def inconsistent_types_liveins: GIMIRCombineRule<
  [{
    %1 = G_AND %bar:(s64), _
    %0 = G_AND %bar:(s32), _
  }],
  [{
    %root = G_CONSTANT i42 0
  }]>;

// CHECK: redundant_opcodes.match:2:5: error: invalid pattern: multiple occurences of G_AND
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def redundant_opcodes: GIMIRCombineRule<
  [{
    %0 = (G_AND | G_AND) %live1:(s32), _
  }],
  [{
    %root = G_CONSTANT i42 0
  }]>;

// CHECK: outpat_sema.apply:2:5: error: 'apply' patterns may not use wildcard ('_') operand
// CHECK: outpat_sema.apply:3:5: error: 'apply' patterns must have a single opcode
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def outpat_sema: GIMIRCombineRule<
  [{
    %0 = G_AND %live1:(s32), _
  }],
  [{
    %foo = G_AND _, %0
    %root = (G_ABS | G_FABS) %foo
  }]>;

// CHECK: unreachable_inst.match:2:5: error: instruction is not reachable from the root of the pattern
// CHECK: unreachable_inst.match:3:5: note: root of the pattern is here
// CHECK: :[[@LINE+1]]:{{[0-9]+}}: error: Failed to parse rule
def unreachable_inst: GIMIRCombineRule<
  [{
    %1 = G_AND %live0:(s64), _
    %0 = G_AND %live1:(s32), _
  }],
  [{
    %root = G_CONSTANT i42 0
  }]>;

// CHECK:      MIRPattern(valid0.match):
// CHECK-NEXT:  Instruction([[VALID0_INST0:.*]]):
// CHECK-NEXT:   opcodes:      G_IMPLICIT_DEF
// CHECK-NEXT:   operands:     def %imp(untyped)
// CHECK-NEXT:  Instruction({{.*}}):
// CHECK-NEXT:   flags:        commutable
// CHECK-NEXT:   opcodes:      G_AND, G_MUL
// CHECK-NEXT:   operands:     def %root(untyped), <Wildcard>, %imp([[VALID0_INST0]] untyped)
// CHECK-NEXT: MIRPattern(valid0.apply):
// CHECK-NEXT:  Instruction({{.*}}):
// CHECK-NEXT:   opcodes:      G_CONSTANT
// CHECK-NEXT:   operands:     def %root(untyped), <intimm: -99>
def valid0: GIMIRCombineRule<
  [{
    %imp = G_IMPLICIT_DEF
    %root = (G_AND | G_MUL) _, %imp
  }],
  [{
    %root = G_CONSTANT i42 -99
  }]>;

// CHECK:      MIRPattern(valid1.match):
// CHECK-NEXT:  Instruction([[VALID1_INST0:.*]]):
// CHECK-NEXT:   opcodes:      G_FCONSTANT
// CHECK-NEXT:   operands:     def %const(untyped), <fpimm: 3.1400001>
// CHECK-NEXT:  Instruction({{.*}}):
// CHECK-NEXT:   opcodes:      G_BUILD_VECTOR
// CHECK-NEXT:   operands:     def %0(untyped), <Wildcard>, %const([[VALID1_INST0]] untyped), %livein(live-in untyped)
// CHECK-NEXT: MIRPattern(valid1.apply):
// CHECK-NEXT:  Instruction({{.*}}):
// CHECK-NEXT:   opcodes:      G_UNMERGE_VALUES
// CHECK-NEXT:   operands:     def %a(untyped), def %b(untyped), def %c(untyped), %const(live-in untyped)
def valid1: GIMIRCombineRule<
  [{
    %const = G_FCONSTANT f32 3.14
    %0 = G_BUILD_VECTOR _, %const, %livein
  }],
  [{
    %a, %b, %c = G_UNMERGE_VALUES %const
  }]>;

// CHECK:       MIRPattern(infer_valid.match):
// CHECK-NEXT:   Instruction([[INFER_VALID_INST0:.*]]):
// CHECK-NEXT:    flags:        commutable
// CHECK-NEXT:    opcodes:      G_ADD
// CHECK-NEXT:    operands:     def %const(s32), <Wildcard>, <Wildcard>
// CHECK-NEXT:   Instruction([[INFER_VALID_INST1:.*]]):
// CHECK-NEXT:    opcodes:      G_BUILD_VECTOR
// CHECK-NEXT:    operands:     def %bv(untyped), <Wildcard>, %const([[INFER_VALID_INST0]] s32), %livein(live-in s32)
// CHECK-NEXT:   Instruction({{.*}}):
// CHECK-NEXT:    opcodes:      G_EXTRACT_VECTOR_ELT
// CHECK-NEXT:    operands:     def %root(untyped), %bv([[INFER_VALID_INST1]] untyped), %const([[INFER_VALID_INST0]] s32)
def infer_valid: GIMIRCombineRule<
  [{
    %const:(s32) = G_ADD _, _
    %bv = G_BUILD_VECTOR _, %const, %livein
    %root = G_EXTRACT_VECTOR_ELT %bv, %const
  }],
  [{
    %a, %b, %c = G_UNMERGE_VALUES %const
  }]>;


def MyCombiner: GICombinerHelper<"GenMyCombiner", [
  empty_patterns, use_before_def, invalid_redef, inconsistent_types,
  inconsistent_commutable, inconsistent_types_liveins, redundant_opcodes,
  outpat_sema, unreachable_inst, valid0, valid1, infer_valid
]>;
