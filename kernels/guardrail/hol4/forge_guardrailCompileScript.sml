(*
  Forge Milestone 2: In-Logic Verified ARM64 Compilation of guardrail_prog.
  Emits guardrail_arm8.S and proves the compiler evaluation theorem linking
  guardrail_prog to its exact ARM64 machine-code bytes and bitmaps.
*)
Theory forge_guardrailCompile
Ancestors
  forge_guardrailProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem guardrail_compiled =
  eval_cake_compile_arm8 "" guardrail_prog_def "guardrail_arm8.S";
