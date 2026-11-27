(*
  Forge Milestone 1: In-Logic Verified ARM64 Compilation of counter_prog.
  Emits counter_arm8.S and proves the compiler evaluation theorem linking
  counter_prog to its exact ARM64 machine-code bytes and bitmaps.
*)
Theory forge_counterCompile
Ancestors
  forge_counterProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem counter_compiled =
  eval_cake_compile_arm8 "" counter_prog_def "counter_arm8.S";
