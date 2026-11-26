# Status

Measured locally on branch `feat/m1-counter-e2e` (not merged to `main`).

Mid-milestone hardening checkpoint (Pass 2A complete; Pass 2B `forge_shimProof` compiling; Pass 2C `forge_m1Kernel` pending). Final `end_to_end=true` awaits the upgraded `Term.aconv` + pinned-spec + theorem-catalog replay of `scripts/iron_law.py`.

## Compiled Theories (Checkpoint #1 — from `docs/THEOREM_CATALOG.md`)

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_counterSpec` | Pure Spec | `verified` | 31 | 52 | 0 | `[DISK_THM]` | `[]` |
| `forge_contractSpec` | Hardware & OS Contract | `verified` | 56 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterProg` | Zero-Basis CakeML | `verified` | 8 | 26 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Boot & Syscall Shim | `pending` | — | — | — | — | — |
| `forge_m1Kernel` | Unified End-to-End | `pending` | — | — | — | — | — |

Global kernel summary across the 5 compiled `forge_*` theories (336 transitive theories): `105` definitions, `133` theorems (`238` verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, `AXIOMS=4` (`bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX`).

## Commands run locally (actual exit codes)

- `Holmake --qof -j 1 --no_prereqs forge_counterProgTheory.uo forge_counterCompileTheory.uo` in `kernel/hol4`: **exit 0**
- `Holmake --qof -j 1 --no_prereqs forge_arm8ErasureTheory.uo` in `kernel/hol4`: **exit 0** (`9m18s`, proved `encoded_bytes_in_mem_not_svc0`, `arm8_target_exact_ok`, `arm8_target_exact_encoder_correct`, `real_mc_evaluate_exact_eq`, and `machine_sem_real_eq_exact`)
- `FORGE_CATALOG_CHECKPOINT=1 ... hol ... < ../../scripts/export_theorem_catalog.sml`: **exit 0** (`CATALOG_EXPORT_CHECKPOINT_OK theories=5 pending=2 defs=105 thms=133 axioms=4`)
- `python3 scripts/tests/test_iron_law.py`: **exit 0** (`41 of 41 cases passed`)
- `python3 scripts/tests/test_hol_audit_real.py`: **exit 0** (`7 of 7 real HOL4 Term.aconv negative controls passed`)

## Commands not run yet on hardened Pass 2 build

- `Holmake --qof -j 1 --no_prereqs forge_shimProofTheory.uo` (currently building)
- `Holmake --qof -j 1 --no_prereqs forge_m1KernelTheory.uo` (pending Pass 2C proof)
- Full clean `Holmake cleanAll && python3 scripts/iron_law.py` (requires 100% built theories and zero `pending` in `docs/THEOREM_CATALOG.md`)
- `python3 scripts/smoke_m1.py --docker-image forge-arm64-tools:bookworm kernel/build/forge-kernel` (re-run at final gate)
- Hosted GitHub Actions workflow `.github/workflows/iron-law.yml` on `ubuntu-24.04` (runs after PR open)

## Explicit trust boundary (Level 1 of `docs/ULTIMATE_PROOF_ROADMAP.md`)

- **Proved in HOL4 (compiled so far):** Pure counter conservation/overflow/replay spec (`forge_counterSpec`), SHA-256 pinned hardware/ELF/syscall contract (`forge_contractSpec`), Zero-Basis CakeML implementation (`forge_counterProg`), in-logic ARM64 compilation (`forge_counterCompile`), real Linux EL0 processor-bit erasure + exact `arm8$Next` encoder correctness + no-rogue-`svc #0` + unconditional `machine_sem_real_eq_exact` (`forge_arm8Erasure`).
- **Pending in Pass 2B/2C:** Universal syscall shim proof (`forge_shimProof`) and unified `Term.aconv`-pinned whole-binary theorem + non-vacuity witness (`forge_m1Kernel`).
- **Remaining trusted computing base (TCB):** Linux kernel syscall implementation behind `svc #0` (`svc_read_rel`, `svc_write_rel`, `svc_exit_group_rel`), ARM64 CPU silicon, HOL4/Poly/ML proof checker, and `scripts/iron_law.py` + `scripts/hol_audit.sml` + `scripts/elf64_check.py`.
