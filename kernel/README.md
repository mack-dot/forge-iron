# kernel/ — Ring 0 (PROVED for Milestone 1)

This directory holds the Milestone 1 end-to-end verified ARM64 counter kernel. It compiles a Zero-Basis CakeML binary-frame loop directly to a static non-PIE Linux AArch64 ELF binary with zero `libc`, zero C compiler, and zero unverified executable gap bytes.

## Layout

- [`GATE.manifest`](GATE.manifest): Fixed key/value manifest read by [`scripts/iron_law.py`](../scripts/iron_law.py).
- [`SPEC_HASHES.sha256`](SPEC_HASHES.sha256): SHA-256 pins for the two trusted specification files (`forge_counterSpecScript.sml` and `forge_contractSpecScript.sml`).
- `hol4/`: Seven HOL4 theories built via `Holmake --qof -j 1 --no_prereqs`:
  1. `forge_counterSpecScript.sml` — SHA-256 pinned 16-byte little-endian framing, overflow-safe `u64` spend cap (`cap_val = 10000`), replay/gap rejection, and total 2-FFI oracle (`recv16`, `send16`).
  2. `forge_contractSpecScript.sml` — SHA-256 pinned initial Linux EL0 ARM64 CPU/ELF memory contract (`forge_elf_loaded`), whole-binary transition relation (`whole_step`), and Linux `read(63)` / `write(64)` / `exit_group(94)` `svc #0` contracts.
  3. `forge_counterProgScript.sml` — Zero-Basis CakeML program extending `Word8ArrayProg` only, with CF correctness (`counter_semantics`).
  4. `forge_counterCompileScript.sml` — In-logic ARM64 CakeML compilation producing `code` (74,396 bytes) and `data` (484 bitmap words = 3,872 bytes).
  5. `forge_arm8ErasureScript.sml` — Real Linux EL0 ARMv8 processor-bit erasure (`TBI0`, `TBI1`, `SA0`), exact `arm8$Next` encoder correctness, no-rogue-`svc #0` proof (`encoded_bytes_in_mem_not_svc0`), and unconditional `machine_sem_real_eq_exact` with zero `b ≠ Fail` escape hatch.
  6. `forge_shimProofScript.sml` — Real L3 ARMv8 proofs for the 44 veneer words (176 bytes) and 80 raw shim words (320 bytes): 43-step `_start -> cml_main -> cake_main`, universal (`∀`) safety and forward liveness over partial reads/writes, `EINTR` retries, truncated `<16B` EOF, and fatal read/write errors on Linux `read(63)` / `write(64)` / `exit_group(94)`.
  7. `forge_m1KernelScript.sml` — Top-level `Term.aconv`-pinned whole-binary theorem `forge_m1_kernel_correct` and concrete non-vacuity witness `forge_m1_nonvacuous`.
- `shim/`: Raw AArch64 assembly (`shim.S`), fixed low-address strict-W^X linker script (`forge.ld`), and static ELF builder (`build_elf.sh`).
- `build/`: Linked static non-PIE ARM64 ELF binary (`forge-kernel`, 275,400 bytes) and SHA-256 file (`machine_bytes_hash.txt`).

## Verify locally

1. Check pinned specification hashes:
   ```sh
   shasum -a 256 -c kernel/SPEC_HASHES.sha256
   ```
2. Replay all 7 HOL4 proofs cleanly and run the Iron Law gate (fresh `Holmake --qof -j 1 --no_prereqs`, HOL4 kernel `Term.aconv` + tag/axiom audit, byte-for-byte `docs/THEOREM_CATALOG.md` check, and zero-gap ELF byte equality):
   ```sh
   (cd kernel/hol4 && Holmake cleanAll) && python3 scripts/iron_law.py
   ```
3. Run the 41 gate unit/sabotage tests, 7 real HOL4 `Term.aconv` negative controls, and 6 ARM64 black-box smoke tests:
   ```sh
   python3 scripts/tests/test_iron_law.py
   python3 scripts/tests/test_hol_audit_real.py
   python3 scripts/smoke_m1.py --docker-image forge-arm64-tools:bookworm kernel/build/forge-kernel
   ```
