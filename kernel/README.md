# kernel/ — Ring 0 (PROVED for Milestone 1)

This directory holds the Milestone 1 end-to-end verified ARM64 counter kernel. It compiles a Zero-Basis CakeML binary-frame loop directly to a static non-PIE Linux AArch64 ELF binary with zero `libc`, zero C compiler, and zero unverified executable gap bytes.

## Layout

- [`GATE.manifest`](GATE.manifest): Fixed key/value manifest read by [`scripts/iron_law.py`](../scripts/iron_law.py).
- `hol4/`: Six HOL4 theories built via `Holmake --qof --no_prereqs`:
  1. `forge_counterSpecScript.sml` — 16-byte little-endian framing, overflow-safe `u64` spend cap (`cap_val = 10000`), replay/gap rejection, and total 2-FFI oracle (`recv16`, `send16`).
  2. `forge_arm8ErasureScript.sml` — Real ARMv8 processor-bit erasure lift (`TBI0`, `TBI1`, `SA0`) over L3 ARMv8, plus proved negative/positive controls.
  3. `forge_counterProgScript.sml` — Zero-Basis CakeML program extending `Word8ArrayProg` only, with CF correctness (`counter_semantics`).
  4. `forge_counterCompileScript.sml` — In-logic ARM64 CakeML compilation producing `code` (74,396 bytes) and `data` (484 bitmap words = 3,872 bytes).
  5. `forge_shimProofScript.sml` — Real L3 ARMv8 proofs for the 44 veneer words (176 bytes) and 80 raw shim words (320 bytes): 43-step `_start -> cml_main -> cake_main`, partial-read/write + `EINTR` loops on Linux `read(63)` / `write(64)` / `exit_group(94)`, and `targetSem` discharge.
  6. `forge_m1KernelScript.sml` — Top-level theorem `forge_m1_kernel_correct` and concrete non-vacuity witness `forge_m1_nonvacuous`.
- `shim/`: Raw AArch64 assembly (`shim.S`), fixed low-address strict-W^X linker script (`forge.ld`), and static ELF builder (`build_elf.sh`).
- `build/`: Linked static non-PIE ARM64 ELF binary (`forge-kernel`, 275,400 bytes) and SHA-256 file (`machine_bytes_hash.txt`).

## Verify locally

1. Replay all HOL4 proofs cleanly:
   ```sh
   cd kernel/hol4 && Holmake cleanAll && Holmake --qof -j 1 --no_prereqs
   ```
2. Run the Iron Law gate (proof replay, HOL4 kernel tag/axiom audit, and zero-gap ELF byte equality):
   ```sh
   python3 scripts/iron_law.py
   ```
3. Run the 25 gate negative controls and 6 ARM64 black-box smoke tests:
   ```sh
   python3 scripts/tests/test_iron_law.py
   python3 scripts/smoke_m1.py --docker-image forge-arm64-tools:bookworm kernel/build/forge-kernel
   ```
