# Status

Measured locally on branch `feat/m3-crypto-crashsafe-airlock` (branched off `main` / tag `v0.2-m2`; not pushed to `main`, not merged).

Milestone 3 local verification is complete. The M3 Crypto-Airlock kernel (`19/19` `forge_*` theories, `pending=0`), the M2 Guardrail kernel (`11/11` `forge_*` theories, `pending=0`), and the M1 Counter kernel (`7/7` `forge_*` theories, `pending=0`) all pass `scripts/iron_law.py` with `end_to_end=true` and `gap_bytes=0`. Hosted GitHub Actions CI replay awaits opening the Milestone 3 PR against `main`.

## M3 Crypto-Airlock Kernel — Compiled Theories (from `docs/THEOREM_CATALOG_M3.md`)

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_runtimeSpec` | Frozen Runtime Contract | `verified` | 65 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_frame64Spec` | Generic 64B Frame ABI | `verified` | 36 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_frameRunner` | Generic 64B ML Runner | `verified` | 22 | 24 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Frozen 256KB Shim Proof | `verified` | 6 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_slotUtil` | Frozen 256KB Slot Util | `verified` | 0 | 21 | 0 | `[DISK_THM]` | `[]` |
| `forge_sha256Spec` | Verified Crypto (M3) | `verified` | 19 | 15 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockFfi` | M3 4-FFI Airlock ABI | `verified` | 44 | 45 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockContract` | M3 6-Syscall Contract | `verified` | 53 | 21 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockSpec` | Pure Spec (M3) | `verified` | 64 | 35 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockRunner` | M3 4-FFI ML Runner | `verified` | 20 | 23 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockProg` | Zero-SL CakeML (M3) | `verified` | 7 | 185 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimBase` | M3 256KB Shim Base | `verified` | 2 | 36 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimStart` | M3 Startup & Exit Proof | `verified` | 0 | 6 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimIo` | M3 I/O Syscall Proofs | `verified` | 0 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimProof` | M3 Disk/Boot Proofs | `verified` | 0 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockCompose` | M3 4-FFI E2E Compose | `verified` | 2 | 1 | 0 | `[DISK_THM]` | `[]` |
| `forge_m3Kernel` | Unified End-to-End (M3) | `verified` | 0 | 2 | 0 | `[DISK_THM]` | `[]` |

Global M3 kernel summary across all 19 compiled `forge_*` theories (`447` transitive theories): `350` definitions, `577` theorems (`927` total verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, `AXIOMS=4` (`bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX`).

Pinned M3 spec digests (`kernels/airlock/SPEC_HASHES.sha256`, 6 files):

- `kernels/airlock/hol4/forge_airlockSpecScript.sml` (539 lines): `sha256=04324a6c7428e8d6806dcbbf76372e78ecaeafc413004d3f371662d966d81e51`
- `runtime/hol4/forge_sha256SpecScript.sml` (247 lines): `sha256=fedd53a5ab65c7b33e71809793ce5595e554db1f8d0e6b55100821e1e6e2566b`
- `runtime/hol4/forge_airlockFfiScript.sml`: `sha256=2e6388f5cca25c5cbd7bc443a0af2519affa22c09ea83c9a1ff7ba6009aab2e7`
- `runtime/hol4/forge_airlockContractScript.sml`: `sha256=537c3f08fa8ded59da4d57eca4acb45ec043325cf385dc746f2ae84b86115a53`
- `runtime/hol4/forge_frame64SpecScript.sml`: `sha256=b1e549f101805432eb8d7bdca89cfd006492d28e67567550d05f9ef8872e39bb`
- `runtime/hol4/forge_runtimeSpecScript.sml`: `sha256=8cc4e8ea2ad3576d9d75ee48c3792882abc8e0a1285f1a8d7965f4578fd78947`

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

Global M2 kernel summary across all 11 compiled `forge_*` theories (`439` transitive theories): `177` definitions, `285` theorems (`462` total verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, `AXIOMS=4`.

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

- **M3 Crypto-Airlock (`python3 scripts/iron_law.py --manifest kernels/airlock/GATE.manifest`):** **exit 0** (clean kernel rebuild via `Holmake cleanAll && Holmake --qof -j 1 --no_prereqs`: `forge_airlockSpec` `9.4s`, `forge_airlockProg` `2m26s`, `forge_airlockCompile` `1m10s`, `forge_m3Kernel` `3.1s`; full gate replay **exit 0**)
  - Output: `end_to_end=true sha256=05a868c6827b5196472ec8e9c0b4f933b3bde7676ea5ac2b544188ac6639fa1f exec_bytes=328352 code_bytes=178044 shim_bytes=672 gap_bytes=0`
  - `runtime/export_theorem_catalog.sml`: `CATALOG_EXPORT_OK theories=19 pending=0 defs=350 thms=577 axioms=4` (byte-for-byte match verified against `docs/THEOREM_CATALOG_M3.md`)
- **M2 Guardrail (`python3 scripts/iron_law.py --manifest kernels/guardrail/GATE.manifest`):** **exit 0**
  - Output: `end_to_end=true sha256=4ead3ad34246f5a5440395fbf95727475e2abe20ed70958caaaed8db00e788ae exec_bytes=328000 code_bytes=101240 shim_bytes=320 gap_bytes=0`
  - `docs/THEOREM_CATALOG.md`: byte-for-byte match (`theories=11 pending=0 defs=177 thms=285 axioms=4`)
- **M1 Counter (`python3 scripts/iron_law.py --manifest kernels/counter/GATE.manifest`):** **exit 0**
  - Output: `end_to_end=true sha256=a98ed8a5cd6c23e5e7bb482fed545dac0cd1c51cac079766f1782865f3137def exec_bytes=328000 code_bytes=74396 shim_bytes=320 gap_bytes=0`
  - `docs/THEOREM_CATALOG_M1.md`: byte-for-byte match (`theories=7 pending=0 defs=122 thms=189 axioms=4`)

## Commands run locally (actual exit codes)

- `cd kernels/airlock/hol4 && Holmake cleanAll && gtimeout 1200 Holmake --qof -j 1 --no_prereqs && cd ../../.. && python3 scripts/iron_law.py --manifest kernels/airlock/GATE.manifest`: **exit 0** (`end_to_end=true sha256=05a868c6827b5196472ec8e9c0b4f933b3bde7676ea5ac2b544188ac6639fa1f exec_bytes=328352 code_bytes=178044 shim_bytes=672 gap_bytes=0`)
- `python3 scripts/iron_law.py --manifest kernels/guardrail/GATE.manifest`: **exit 0** (`end_to_end=true sha256=4ead3ad34246f5a5440395fbf95727475e2abe20ed70958caaaed8db00e788ae ... gap_bytes=0`)
- `python3 scripts/iron_law.py --manifest kernels/counter/GATE.manifest`: **exit 0** (`end_to_end=true sha256=a98ed8a5cd6c23e5e7bb482fed545dac0cd1c51cac079766f1782865f3137def ... gap_bytes=0`)
- `shasum -a 256 -c kernels/airlock/SPEC_HASHES.sha256 kernels/guardrail/SPEC_HASHES.sha256 kernels/counter/SPEC_HASHES.sha256`: **exit 0** (`11/11 OK`)
- `python3 scripts/tests/test_iron_law.py`: **exit 0** (`65 of 65 cases passed`)
- `python3 scripts/tests/test_hol_audit_real.py`: **exit 0** (`21 of 21 real HOL4 audit negative controls passed`)
- `cargo test --manifest-path relay/Cargo.toml`: **exit 0** (`1 passed`: NIST FIPS 180-4 SHA-256 and RFC 4231 HMAC-SHA256 vectors)
- `cargo test --manifest-path sdk/guardrail/Cargo.toml`: **exit 0** (`3 passed`: golden vectors, partial I/O + EINTR, live ARM64 `GuardrailAdmin`/`GuardrailAgent` capability separation)
- `python3 sdk/guardrail/test_golden_vectors.py`: **exit 0** (Python, TypeScript, Rust, and HOL4 `EVAL` byte-identical vectors + `u64` bounds checks)
- `make demo-airlock`: **exit 0** (live Rogue-Agent Airlock demo against ARM64 `kernels/airlock/build/forge-kernel` + Rust `relay/`)
- `forge-fuzz --mode both --duration 10 --cycles 100`: **exit 0** (adversarial frame + crash-recovery fuzzing against ARM64 `kernels/airlock/build/forge-kernel`)
- `python3 scripts/smoke_m1.py --docker-image forge-arm64-tools:bookworm kernels/counter/build/forge-kernel`: **exit 0** (`ALL 6 M1 BLACK-BOX SMOKE CASES PASSED`)
- `python3 scripts/smoke_m2.py --docker-image forge-arm64-tools:bookworm kernels/guardrail/build/forge-kernel`: **exit 0** (`ALL 6 M2 GUARDRAIL BLACK-BOX SMOKE SUITES PASSED`)
- `python3 scripts/tests/test_hol_repl.py`: **exit 0** (`ALL 6 HOLCTL WARM DAEMON TESTS PASSED`)

## Commands not run yet

- Hosted GitHub Actions workflow `.github/workflows/iron-law.yml` on `ubuntu-24.04` (runs after opening the Milestone 3 PR against `main`)
- `docker build -f Dockerfile.toolchain .` (upstream toolchain image build on clean container host)

## Explicit trust boundary (Level 1 of `docs/ULTIMATE_PROOF_ROADMAP.md`)

- **Proved in HOL4 (`19/19` M3 theories, `11/11` M2 theories, and `7/7` M1 theories compiled and audited):** Pure FIPS 180-4 `SHA-256` and RFC 2104 `HMAC-SHA256` (`forge_sha256Spec`), keyed-HMAC dual-slot crash recovery + conservation + capability tokens + idempotent retry (`forge_airlockSpec`), 6-syscall Linux AArch64 OS contract (`read(63)`, `write(64)`, `pread64(67)`, `pwrite64(68)`, `fdatasync(83)`, `exit_group(94)` in `forge_airlockContract`), 4-FFI CakeML runner (`forge_airlockRunner`), `ml_translator`-synthesized program (`forge_airlockProg`), in-logic ARM64 compilation (`forge_airlockCompile`), real Linux EL0 bit erasure + no-`svc #0` + unconditional `machine_sem_real_eq_exact` (`forge_arm8Erasure`), 43-step startup + universal 6-syscall ARM64 shim proofs (`forge_airlockShimBase`, `forge_airlockShimStart`, `forge_airlockShimIo`, `forge_airlockShimProof`), polymorphic 4-FFI whole-binary composition (`forge_airlockCompose`), and exact `Term.aconv`-pinned whole-binary theorems (`forge_m3Kernel`, `forge_m2Kernel`, `forge_m1Kernel`).
- **Ring 1 stateless keyless boundary (outside Ring 0 ELF proof):** `relay/src/main.rs` (251 lines, zero external crates) holds external API credentials in a separate OS process and forwards calls only after constant-time `HMAC-SHA256` verification of the kernel's capability token.
- **Untrusted Ring 2 host tooling (outside Ring 0/1 TCB):** `examples/rogue_agent_airlock/demo_airlock.py`, `tools/forge-fuzz/`, `sdk/guardrail/`, and `scripts/forge_vibe.py`.
- **Remaining trusted computing base (TCB):** Linux kernel syscall implementation behind `svc #0` (`read`, `write`, `pread64`, `pwrite64`, `fdatasync`, `exit_group`), ARM64 CPU silicon, HOL4/Poly/ML proof checker, and `runtime/iron_law.py` + `runtime/hol_audit.sml` + `runtime/elf64_check.py`.
