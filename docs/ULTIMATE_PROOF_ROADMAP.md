# The Vertical Verification Ladder (Intent to Transistors)

This document records the 5-level verification roadmap from Milestone 1 (`forge-iron` M1) to a full intent-to-transistors proof stack.

## Level 1 — Standalone Verified ARM64 Binary (Milestone 1: `counter`)

- **Proof:** A standalone static Linux ARM64 ELF binary with zero `libc` and zero C compiler, proved bit-for-bit from `_start` through `cake_main` to `SVC #0` (`read`, `write`, `exit_group`), under real Linux EL0 processor bits (`TBI0 = T`, `TBI1 = F`, `SA0 = T`, 16-byte aligned `SP_EL0`).
- **Remaining TCB:** The Linux kernel (30M+ lines of unverified C handling `SVC #0`), the ARM64 CPU silicon, and HOL4's proof checker (Poly/ML + HOL4 kernel).

## Level 2 — Real-World Critical Kernel & AI Safety Governor (Milestone 2: `guardrail`)

- Swap `counter_prog` for a reusable high-stakes kernel over fixed-width binary frames:
  - Financial settlement / refund kernel proved to conserve value across every possible byte stream (mathematically impossible to double-spend or double-refund).
  - Deterministic AI guardrail kernel enforcing hard spending caps, destination allowlists, monotonic nonces, and signing policies that no prompt injection, parser bug, or buffer overflow can violate.
- Target deployment: AWS Graviton Nitro Enclave (native ARM64 hardware isolation).

## Level 3 — Removing the Linux Kernel (`_start` -> Verified Microkernel)

- Replace Linux `SVC #0` with a formally verified microkernel (`seL4`) and verified device drivers (Pancake / Microkit).
- Removes the ~30M-line unverified OS C kernel between the verified binary and the hardware.

## Level 4 — Closing the Proof-Checker Trust Loop (Self-Certifying Replay)

- Replay the proof audit inside **Candle** (CakeML's formally verified HOL proof checker, itself compiled to a verified machine-code binary).
- Removes unverified Poly/ML + HOL4 kernel trust from the audit step.

## Level 5 — The Ultimate Proof (Human Intent to Transistors)

- **Top:** ~100 lines of human-readable math (e.g., conservation of funds and multi-signature authorization laws).
- **Middle:** AI-generated CakeML/Pancake implementation + verified compiler + verified bare-metal boot and microkernel (zero C, zero `libc`, zero Linux).
- **Bottom:** Verified open-source CPU ISA and RTL Verilog hardware (e.g., CakeML on Silver or a formally verified RISC-V core) down to the netlist on an FPGA or ASIC.
- **Boundary:** Anyone can download the bitstream + ELF binary + proof bundle and run an independent clean-room Iron-Law Gate replay with zero trust in the AI, developer, compiler, OS, or chip.
