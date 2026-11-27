# Status

Measured locally on branch `feat/m2-guardrail-factory` (branched off `main` / tag `v0.1-m1`; not pushed to `main`, not merged).

Milestone 2 local verification is complete. Both the M2 Guardrail kernel (`11/11` `forge_*` theories, `pending=0`) and the M1 Counter kernel on the frozen 256 KB runtime (`7/7` `forge_*` theories, `pending=0`) pass `scripts/iron_law.py` with `end_to_end=true` and `gap_bytes=0`. Hosted GitHub Actions CI replay awaits opening the Milestone 2 PR against `main`.

## M2 Guardrail Kernel — Compiled Theories (from `docs/THEOREM_CATALOG.md`)

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_guardrailSpec` | Pure Spec (M2) | `verified` | 32 | 26 | 0 | `[DISK_THM]` | `[]` |
| `forge_runtimeSpec` | Frozen Runtime Contract | `verified` | 65 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_frame64Spec` | Generic 64B Frame ABI | `verified` | 36 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_frameRunner` | Generic 64B ML Runner | `verified` | 22 | 24 | 0 | `[DISK_THM]` | `[]` |
| `forge_guardrailProg` | Zero-SL CakeML (M2) | `verified` | 4 | 56 | 0 | `[DISK_THM]` | `[]` |
| `forge_guardrailCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Frozen 256KB Shim Proof | `verified` | 6 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_slotUtil` | Frozen 256KB Slot Util | `verified` | 0 | 21 | 0 | `[DISK_THM]` | `[]` |
| `forge_frame64Compose` | Generic 64B E2E Compose | `verified` | 2 | 1 | 0 | `[DISK_THM]` | `[]` |
| `forge_m2Kernel` | Unified End-to-End (M2) | `verified` | 0 | 2 | 0 | `[DISK_THM]` | `[]` |

Global M2 kernel summary across all 11 compiled `forge_*` theories (`439` transitive theories): `177` definitions, `285` theorems (`462` total verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, `AXIOMS=4` (`bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX`).

Frozen M2 spec digest (`kernels/guardrail/hol4/forge_guardrailSpecScript.sml`, 91 lines): `sha256=02bb89dd3432e9438f62341a38e79f98fbad1588c5cd8c3e7cf12d9b8b638356`.

## M1 Counter Kernel on Frozen Runtime — Compiled Theories (from `docs/THEOREM_CATALOG_M1.md`)

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_counterSpec` | Pure Spec (M1) | `verified` | 31 | 52 | 0 | `[DISK_THM]` | `[]` |
| `forge_runtimeSpec` | Frozen Runtime Contract | `verified` | 65 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterProg` | Zero-Basis CakeML (M1) | `verified` | 8 | 26 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Frozen 256KB Shim Proof | `verified` | 6 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_m1Kernel` | Unified End-to-End (M1) | `verified` | 2 | 6 | 0 | `[DISK_THM]` | `[]` |

Global M1 kernel summary across all 7 compiled `forge_*` theories (`435` transitive theories): `122` definitions, `189` theorems (`311` total verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, `AXIOMS=4`.

## Iron Law Gate Results

- **M2 Guardrail (`python3 scripts/iron_law.py --manifest kernels/guardrail/GATE.manifest`):** **exit 0** (clean kernel rebuild `249s` with built `runtime/hol4`; post-hardening replay **exit 0**)
  - Output: `end_to_end=true sha256=4ead3ad34246f5a5440395fbf95727475e2abe20ed70958caaaed8db00e788ae exec_bytes=328000 code_bytes=101240 shim_bytes=320 gap_bytes=0`
  - `runtime/export_theorem_catalog.sml`: `theories=11 pending=0 defs=177 thms=285 axioms=4` (byte-for-byte match verified against `docs/THEOREM_CATALOG.md`)
- **M1 Counter (`python3 scripts/iron_law.py --manifest kernels/counter/GATE.manifest`):** **exit 0** (clean full cold rebuild of `runtime/hol4` + `kernels/counter/hol4` `1148s`; post-hardening replay **exit 0**)
  - Output: `end_to_end=true sha256=a98ed8a5cd6c23e5e7bb482fed545dac0cd1c51cac079766f1782865f3137def exec_bytes=328000 code_bytes=74396 shim_bytes=320 gap_bytes=0`
  - `runtime/export_theorem_catalog.sml`: `CATALOG_EXPORT_OK theories=7 pending=0 defs=122 thms=189 axioms=4` (byte-for-byte match verified against `docs/THEOREM_CATALOG_M1.md`)

## Commands run locally (actual exit codes)

- `python3 scripts/iron_law.py --manifest kernels/guardrail/GATE.manifest`: **exit 0** (`end_to_end=true ... gap_bytes=0`)
- `python3 scripts/iron_law.py --manifest kernels/counter/GATE.manifest`: **exit 0** (`end_to_end=true ... gap_bytes=0`)
- `shasum -a 256 -c kernels/counter/SPEC_HASHES.sha256 && shasum -a 256 -c kernels/guardrail/SPEC_HASHES.sha256`: **exit 0** (`5/5 OK`)
- `python3 scripts/tests/test_iron_law.py`: **exit 0** (`53 of 53 cases passed`)
- `python3 scripts/tests/test_hol_audit_real.py`: **exit 0** (`15 of 15 real HOL4 audit negative controls passed`)
- `python3 sdk/guardrail/test_golden_vectors.py`: **exit 0** (`5/5` Python/TypeScript/HOL4 `EVAL` byte-identical vectors + `u64` bounds checks)
- `python3 scripts/smoke_m1.py --docker-image forge-arm64-tools:bookworm kernels/counter/build/forge-kernel`: **exit 0** (`ALL 6 M1 BLACK-BOX SMOKE CASES PASSED`)
- `python3 scripts/smoke_m2.py --docker-image forge-arm64-tools:bookworm kernels/guardrail/build/forge-kernel`: **exit 0** (`ALL 6 M2 GUARDRAIL BLACK-BOX SMOKE SUITES PASSED (28 frames verified)`, including 1-byte chunked pipe reads and real Linux `-EPIPE`)
- `python3 scripts/tests/test_hol_repl.py`: **exit 0** (`ALL 6 HOLCTL WARM DAEMON TESTS PASSED`: `fast_step` `78.4ms` wall / `27.23ms` HOL, `5.09s` `WORD_ADD_COMM` timeout recovery, `76.2ms` `back` undo)
- `make factory-heap`: **exit 0** (dumped local untracked `forge_factory.heap` preloading `ml_translatorLib`, `blastLib`, `cfLib`, and frozen `runtime/` theories)

## Commands not run yet

- Hosted GitHub Actions workflow `.github/workflows/iron-law.yml` on `ubuntu-24.04` (runs after opening the Milestone 2 PR against `main`)
- `docker build -f Dockerfile.toolchain .` (upstream toolchain image build on clean container host)

## Explicit trust boundary (Level 1 of `docs/ULTIMATE_PROOF_ROADMAP.md`)

- **Proved in HOL4 (`11/11` M2 theories and `7/7` M1 theories compiled and audited):** Frozen pure specs (`forge_guardrailSpec`, `forge_counterSpec`), frozen 256 KB RX slot + `_start=0x450000` + 16B/64B syscall contract (`forge_runtimeSpec`), generic 64B binary frame bijection (`forge_frame64Spec`), polymorphic Zero-Basis CakeML 64B runner (`forge_frameRunner`), `ml_translator`-synthesized guardrail program (`forge_guardrailProg`), in-logic ARM64 compilation (`forge_guardrailCompile`, `forge_counterCompile`), real Linux EL0 bit erasure + no-`svc #0` + unconditional `machine_sem_real_eq_exact` (`forge_arm8Erasure`), parameterized 43-step startup + universal Linux `read(63)`/`write(64)`/`exit_group(94)` shim proofs (`forge_shimProof`), slot layout utility + non-vacuity (`forge_slotUtil`), generic 64B E2E composition (`forge_frame64Compose`), and exact `Term.aconv`-pinned whole-binary theorems (`forge_m2Kernel`, `forge_m1Kernel`).
- **Untrusted Ring 2 host tooling (outside Ring 0/1 TCB):** `sdk/guardrail/` (`sdk.py`, `sdk.ts`, `schema.json`, `test_golden_vectors.py`) and `scripts/forge_vibe.py`.
- **Remaining trusted computing base (TCB):** Linux kernel syscall implementation behind `svc #0` (`svc_read_rel`, `svc_write_rel`, `svc_exit_group_rel`), ARM64 CPU silicon, HOL4/Poly/ML proof checker, and `runtime/iron_law.py` + `runtime/hol_audit.sml` + `runtime/elf64_check.py`.
