# Status

Measured locally on branch `feat/m1-counter-e2e` (not merged to `main`):

```text
end_to_end=true sha256=ef18c49c11319578fa6facd2f5887f5d514ce8f9c4b819ab06afdc335f3808df exec_bytes=135488 code_bytes=74396 shim_bytes=320 gap_bytes=0
```

| Item | State |
| --- | --- |
| Current milestone | Milestone 1 (`feat/m1-counter-e2e` — local proof, gate, smoke, and 6-vector red-team audit passed; awaiting owner review) |
| Kernel theorem | `forge_m1Kernel.forge_m1_kernel_correct` + `forge_m1Kernel.forge_m1_nonvacuous` (0 hypotheses, `DISK_THM`-only oracle tag, 4 `bool` axioms across 434 theories, 257 `forge_*` theorems/defs clean) |
| Clean `Holmake --qof` replay | Passed locally (`Holmake cleanAll && Holmake --qof -j 1 --no_prereqs`, exit `0`, 6/6 theories built in ~3 min) |
| Iron Law gate (`scripts/iron_law.py`) | Passed locally (exit `0`, `end_to_end=true`, zero unverified gap bytes across 135,488B `PF_X`) |
| Gate self-test (`scripts/tests/test_iron_law.py`) | Passed locally (`25 of 25 cases passed`, exit `0`) |
| ARM64 black-box smoke (`scripts/smoke_m1.py`) | Passed locally in Linux/ARM64 Docker (`ALL 6 M1 BLACK-BOX SMOKE CASES PASSED`, exit `0`) |
| Independent `/tmp` sabotage controls | Passed locally (1-bit `.text` flip -> `HASH_MISMATCH` exit `1`; 1-bit `.text` flip + forged hash -> `CODE_BYTE_MISMATCH` exit `1`; injected `cheat` -> `CHEAT_FOUND` exit `1`) |
| Hosted GitHub Actions CI (`.github/workflows/iron-law.yml`) | Updated for pinned `HOL4 9783a4997` + `CakeML cd9155694` + `qemu-user-static`; **not executed on GitHub Actions yet** |
| Merge blocking | Needs branch protection + required status checks on `main` (owner action) |

## Commands run locally (actual exit codes)

- `Holmake cleanAll && Holmake --qof -j 1 --no_prereqs` in `kernel/hol4`: **exit 0**
  - `forge_arm8Erasure`: `20.8s`
  - `forge_counterSpec`: `4.3s`
  - `forge_counterProg`: `1m10s`
  - `forge_counterCompile`: `27.7s`
  - `forge_shimProof`: `48.7s`
  - `forge_m1Kernel`: `16.3s`
- `python3 scripts/iron_law.py`: **exit 0** (`end_to_end=true sha256=ef18c49c11319578fa6facd2f5887f5d514ce8f9c4b819ab06afdc335f3808df exec_bytes=135488 code_bytes=74396 shim_bytes=320 gap_bytes=0`)
- `python3 scripts/tests/test_iron_law.py`: **exit 0** (`25 of 25 cases passed`)
- `python3 scripts/smoke_m1.py --docker-image forge-arm64-tools:bookworm kernel/build/forge-kernel`: **exit 0** (`6/6` passed)
- `readelf -h -l -d -sW kernel/build/forge-kernel` (in `forge-arm64-tools:bookworm`): **exit 0** (`ET_EXEC`, `AArch64`, `e_entry=0x421000`, 2 `PT_LOAD` segments `R E` and `RW`, no dynamic section)
- Raw `hol` kernel inspection on `forge_m1KernelTheory`: **exit 0** (`HYP_COUNT: 0`, `ORACLES: [DISK_THM]`, `BAD_FORGE_ITEMS: 0`, 4 `bool` axioms)

## Commands not run yet

- Hosted GitHub Actions workflow `.github/workflows/iron-law.yml` on `ubuntu-24.04` (runs after push / PR open).

## Explicit trust boundary (Level 1 of `docs/ULTIMATE_PROOF_ROADMAP.md`)

- **Proved in HOL4:** Pure counter conservation/overflow/replay spec (`forge_counterSpec`), Zero-Basis CakeML implementation (`forge_counterProg`), in-logic ARM64 compilation (`forge_counterCompile`), real Linux EL0 processor-bit erasure lift for `TBI0`/`TBI1`/`SA0` (`forge_arm8Erasure`), 43-step ELF startup + `read(63)`/`write(64)`/`exit_group(94)` shim (`forge_shimProof`), top-level real-bits machine theorem + non-vacuity witness (`forge_m1Kernel`), and zero-gap byte equality against `kernel/build/forge-kernel` (`scripts/iron_law.py`).
- **Remaining trusted computing base (TCB):** Linux kernel syscall implementation behind `svc #0` (modeled explicitly as `svc_read_rel`, `svc_write_rel`, `svc_exit_group_rel`), ARM64 CPU silicon, HOL4/Poly/ML proof checker, and `scripts/iron_law.py` + `scripts/hol_audit.sml` + `scripts/elf64_check.py`.
- **Note on Silver/FPGA:** CakeML's Silver targets a separate ISA, not ARM64. The roadmap tracks hardware and microkernel TCB elimination separately in `docs/ULTIMATE_PROOF_ROADMAP.md`.
