set(LLVM_LINK_COMPONENTS
  Core
  CodeGen
  MC
  SelectionDAG
  Support
  Target
  TargetParser)

add_benchmark(MIRBenchmark
    MachineInstr.cpp
    MIRBenchmark.cpp
    Utils.cpp)
