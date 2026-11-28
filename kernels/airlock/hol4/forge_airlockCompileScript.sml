(*
  Forge Milestone 3: In-Logic Verified ARM64 Compilation of airlock_prog.
  Emits airlock_arm8.S and proves the compiler evaluation theorem linking
  airlock_prog to its exact ARM64 machine-code bytes and bitmaps.
*)
Theory forge_airlockCompile
Ancestors
  forge_airlockProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem airlock_compiled =
  eval_cake_compile_arm8 "" airlock_prog_def "airlock_arm8.S";
