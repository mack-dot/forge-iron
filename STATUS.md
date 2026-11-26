# Status

Measured locally on branch `feat/m1-counter-e2e` (not merged to `main`).

Milestone 1 local verification is complete (`end_to_end=true` on a clean `Holmake cleanAll` replay, `7/7` theories verified, `pending=0`). Hosted GitHub Actions CI replay awaits opening the Milestone 1 PR into `main`.

## Compiled Theories (Final M1 Export — from `docs/THEOREM_CATALOG.md`)

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_counterSpec` | Pure Spec | `verified` | 31 | 52 | 0 | `[DISK_THM]` | `[]` |
| `forge_contractSpec` | Hardware & OS Contract | `verified` | 56 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterProg` | Zero-Basis CakeML | `verified` | 8 | 26 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Boot & Syscall Shim | `verified` | 5 | 43 | 0 | `[DISK_THM]` | `[]` |
| `forge_m1Kernel` | Unified End-to-End | `verified` | 2 | 6 | 0 | `[DISK_THM]` | `[]` |

Global kernel summary across all 7 compiled `forge_*` theories (`435` transitive theories): `112` definitions, `182` theorems (`294` total verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, `AXIOMS=4` (`bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX`).

## Iron Law Gate Result (Clean Replay)

- `Holmake cleanAll && python3 scripts/iron_law.py`: **exit 0**
  - Output: `end_to_end=true sha256=ef18c49c11319578fa6facd2f5887f5d514ce8f9c4b819ab06afdc335f3808df exec_bytes=135488 code_bytes=74396 shim_bytes=320 gap_bytes=0`
  - `scripts/hol_audit.sml`: `AUDIT_OK aconv=exact closure_nodes=435 forge_theories=7 axioms=4 code_bytes=74396 data_bytes=3872 veneers_bytes=176 shim_bytes=320`
  - `scripts/export_theorem_catalog.sml`: `CATALOG_EXPORT_OK theories=7 pending=0 defs=112 thms=182 axioms=4` (byte-for-byte match verified against `docs/THEOREM_CATALOG.md`)

## Commands run locally (actual exit codes)

- `cd kernel/hol4 && Holmake cleanAll`: **exit 0**
- `python3 scripts/iron_law.py` (clean replay of all 7 theories via `Holmake --qof -j 1 --no_prereqs`, `Term.aconv` audit, `SPEC_HASHES.sha256`, `elf64_check.py`, and byte-for-byte `docs/THEOREM_CATALOG.md` check): **exit 0**
- `python3 scripts/tests/test_iron_law.py`: **exit 0** (`41 of 41 cases passed`)
- `python3 scripts/tests/test_hol_audit_real.py`: **exit 0** (`7 of 7 real HOL4 audit negative controls passed`)
- `shasum -a 256 -c kernel/SPEC_HASHES.sha256`: **exit 0** (`forge_counterSpecScript.sml: OK`, `forge_contractSpecScript.sml: OK`)
- `python3 scripts/smoke_m1.py --docker-image forge-arm64-tools:bookworm kernel/build/forge-kernel`: **exit 0** (`ALL 6 M1 BLACK-BOX SMOKE CASES PASSED`)

## Commands not run yet

- Hosted GitHub Actions workflow `.github/workflows/iron-law.yml` on `ubuntu-24.04` (runs after opening the Milestone 1 PR against `main`)
- `docker build -f Dockerfile.toolchain .` (upstream toolchain image build on clean container host)

## Explicit trust boundary (Level 1 of `docs/ULTIMATE_PROOF_ROADMAP.md`)

- **Proved in HOL4 (`7/7` theories compiled and audited):** Pure counter conservation/overflow/replay spec (`forge_counterSpec`), SHA-256 pinned hardware/ELF/syscall contract (`forge_contractSpec`), Zero-Basis CakeML implementation (`forge_counterProg`), in-logic ARM64 compilation (`forge_counterCompile`), real Linux EL0 processor-bit erasure + exact `arm8$Next` encoder correctness + no-rogue-`svc #0` + unconditional `machine_sem_real_eq_exact` (`forge_arm8Erasure`), 43-step ELF startup + universal Linux `read(63)`/`write(64)`/`exit_group(94)` syscall shim safety and liveness (`forge_shimProof`), and unified `Term.aconv`-pinned whole-binary theorem + non-vacuity witness (`forge_m1Kernel`).
- **Remaining trusted computing base (TCB):** Linux kernel syscall implementation behind `svc #0` (`svc_read_rel`, `svc_write_rel`, `svc_exit_group_rel`), ARM64 CPU silicon, HOL4/Poly/ML proof checker, and `scripts/iron_law.py` + `scripts/hol_audit.sml` + `scripts/elf64_check.py`.
