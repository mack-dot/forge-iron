# forge-iron

Proof-gated ARM64 execution engine built in HOL4 and Zero-Basis CakeML with zero `libc` and zero C compiler.

- Master plan: [MASTER_PLAN.md](MASTER_PLAN.md)
- Verified M2 theorem catalog: [docs/THEOREM_CATALOG.md](docs/THEOREM_CATALOG.md)
- Verified M1 theorem catalog: [docs/THEOREM_CATALOG_M1.md](docs/THEOREM_CATALOG_M1.md)
- Live status & measured logs: [STATUS.md](STATUS.md)
- Issue tracker: [ISSUES.md](ISSUES.md)
- Ultimate proof roadmap: [docs/ULTIMATE_PROOF_ROADMAP.md](docs/ULTIMATE_PROOF_ROADMAP.md)
- Future `hol2pan` architecture note: [docs/HOL2PAN_DESIGN.md](docs/HOL2PAN_DESIGN.md)

## Current State

Work is active on branch `feat/m2-guardrail-factory` (branched off `main` / tag `v0.1-m1`; not merged to `main`).

- **Milestone 0 (merged):** Skeleton, Iron Law gate (`scripts/iron_law.py`), and self-test harness (`scripts/tests/test_iron_law.py`).
- **Milestone 1 (merged to `main` as `v0.1-m1`, re-verified on frozen `runtime/`):** End-to-end verified ARM64 counter kernel (`kernels/counter/`, `7/7` theories, `end_to_end=true`, `gap_bytes=0`).
- **Milestone 2 (locally verified `end_to_end=true`; hosted CI awaits PR open):**
  - **Phase A — Proving-Speed Infrastructure & Frozen `runtime/`:** Added warm HOL4 Unix-socket goal server (`scripts/hol_repl.py` + `scripts/holctl`, `<80ms` tactic step, `5s` timeout recovery, `6/6` tests passing), `make factory-heap`, frozen 256 KB RX code slot `[0x400000..0x440000)` with fixed `_start=0x450000` (`runtime/hol4/`), and polymorphic zero-SL 64-byte `ml_translator` frame runner (`forge_frameRunner`) + E2E composition (`forge_frame64Compose`).
  - **Phase B — Verified Vibe-Coding CLI (`scripts/forge_vibe.py`):** Generates `<100`-line HOL4 specs, 64-byte binary schemas, and Ring 2 zero-dependency Python/TypeScript SDKs (`sdk/<app>/`) with cross-language golden-vector byte tests against HOL4 `EVAL`.
  - **Phase C — Flagship M2 Guardrail Kernel (`kernels/guardrail/`):** Frozen 91-line pure HOL4 AI spending guardrail spec (`forge_guardrailSpec`) supporting `BUDGET_SET/DEPOSIT`, `SPEND_REQUEST`, `REFUND`, and `QUERY` with exact fund conservation, rolling net cap, allowlist enforcement, strict monotonic nonces, and zero double-refunds or `u64` overflow. Synthesized via `ml_translator` with zero manual Separation Logic and zero new assembly proofs (`forge_m2Kernel`: 73 lines, `2.5s` compile).
  - **Hardened Iron Law Gate:** Exact HOL4 kernel `Term.aconv` verification + `dest_thy_const`/LHS pinning on `code_def`/`data_def`/`ffis_def`/`shim_def`/layout defs (`runtime/hol_audit.sml`), mandatory spec-hash checks (`runtime/iron_law.py`), zero-gap ELF64 layout checks (`runtime/elf64_check.py`), `53/53` gate self-tests (`scripts/tests/test_iron_law.py`), `15/15` real HOL4 negative controls (`scripts/tests/test_hol_audit_real.py`), and `6/6` black-box ARM64 smoke suites each for M1 (`scripts/smoke_m1.py`) and M2 (`scripts/smoke_m2.py`).

Only `scripts/iron_law.py` decides `end_to_end=true`. See [STATUS.md](STATUS.md) for measured command exit codes and [ISSUES.md](ISSUES.md) for active items.

## Verified Theorem Summary (M2 Guardrail)

Every theorem below exports directly from compiled HOL4 `.dat` files into [docs/THEOREM_CATALOG.md](docs/THEOREM_CATALOG.md) and is checked byte-for-byte by `scripts/iron_law.py`.

**Global M2 kernel tags:** `11` compiled `forge_*` theories (`439` transitive theories), `177` definitions, `285` theorems (`462` total verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, and `AXIOMS=4` (`bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX`).

| Layer | Theory | Key Theorem / Definition | Plain-English Guarantee |
| --- | --- | --- | --- |
| Pure Spec (M2) | `forge_guardrailSpec` | `frame_bijection`, `gr_run_preserves_inv`, `gr_safety_denials` | Lossless 64B framing, exact fund conservation (`deposits = balance + spent - refunds`), rolling net cap, allowlist, strict nonces, zero double-refunds, and zero `u64` overflow across any stream. |
| Frozen Runtime Contract | `forge_runtimeSpec` | `forge_slot_loaded_def`, `whole_step_def` | SHA-256 pinned 256 KB RX code slot `[0x400000..0x440000)`, fixed `_start=0x450000`, and raw `arm8$Next` + Linux `svc #0` transition relation. |
| Generic 64B Frame ABI | `forge_frame64Spec` | `frame64_roundtrip`, `frame64_run_def` | Lossless 8×`u64` little-endian 64-byte binary framing and total `recv64`/`send64` FFI oracle. |
| Generic 64B ML Runner | `forge_frameRunner` | `run_frame64_kernel_spec` | Polymorphic Zero-Basis CakeML `recv64 -> step -> send64` loop proved once for all future `ml_translator` kernels. |
| Zero-SL CakeML (M2) | `forge_guardrailProg` | `guardrail_semantics` | Automatically `ml_translator`-synthesized `guardrail_prog` terminates cleanly and emits exact `frame64_run gr_step` frames. |
| Verified Compilation | `forge_guardrailCompile` | `guardrail_compiled` | In-logic CakeML `arm8` backend compilation binding `guardrail_prog` to exact code bytes (`101,240` B) and bitmaps (`6,984` B). |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `encoded_bytes_in_mem_not_svc0`, `machine_sem_real_eq_exact` | Compiled code contains zero `svc #0`, preserves `SP_EL0` with zero CPU exceptions, and matches real EL0 bits (`TBI0`/`TBI1`/`SA0`) unconditionally. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `startup_to_cake_main_slot`, `ffirecv64_universal_slot`, `ffisend64_universal_slot` | Parameterized 43-step `_start -> cake_main` boot proof for any `<=256 KB` kernel plus universal (`∀`) safety over partial reads/writes, `EINTR`, truncated EOF, and `-EPIPE`. |
| Slot Util & E2E Compose | `forge_slotUtil`, `forge_frame64Compose` | `forge_slot_nonvacuous`, `forge_frame64_kernel_compose` | Reusable slot layout witness and polymorphic whole-binary lift from `_start` to `exit_group(94)`. |
| Unified End-to-End (M2) | `forge_m2Kernel` | `forge_m2_nonvacuous`, `forge_m2_kernel_correct` | Exact `Term.aconv`-pinned whole-binary theorem from `_start` (`0x450000`) across `RTC whole_step` to `svc #0 exit_group(94)` (`0w`/`1w`/`2w`) and exact `frame64_run gr_step` output on `exit_code = 0w`. |

Full verbatim `⊢ ...` statements and per-theorem kernel tags: [docs/THEOREM_CATALOG.md](docs/THEOREM_CATALOG.md) (M2) and [docs/THEOREM_CATALOG_M1.md](docs/THEOREM_CATALOG_M1.md) (M1).

## Repository Layout

```text
forge-iron/
├── runtime/             # Ring 0 frozen 256 KB ARM64 runtime, generic 64B runner, Iron Law gate, HOL4 auditor, ELF64 checker
├── kernels/
│   ├── counter/         # Ring 0 M1 verified 16-byte spend counter kernel (re-verified on frozen runtime/)
│   └── guardrail/       # Ring 0 M2 verified 64-byte AI spending guardrail kernel (zero-SL ml_translator)
├── sdk/                 # Ring 2 untrusted host SDKs (Python/TypeScript wrappers, schemas, golden-vector byte tests)
├── spec-compiler/       # Ring 1 verified canonical spec compiler (planned)
├── relay/               # Stateless edge gateway (planned)
├── scripts/             # CLI wrappers (iron_law.py, holctl, forge_vibe.py), smoke suites, and negative-control test harnesses
├── docs/                # Auto-generated theorem catalogs, HOL2PAN design note, and TCB elimination roadmap
└── Dockerfile.toolchain # Upstream-only Poly/ML 5.9.1 + HOL4 + CakeML ARM8 toolchain image
```

The earlier research history remains in `mack-dot/forge-lab`.
