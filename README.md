# forge-iron

Proof-gated ARM64 execution engine built in HOL4 and Zero-Basis CakeML with zero `libc` and zero C compiler.

- Master plan: [MASTER_PLAN.md](MASTER_PLAN.md)
- Verified theorem catalog: [docs/THEOREM_CATALOG.md](docs/THEOREM_CATALOG.md)
- Live status & measured logs: [STATUS.md](STATUS.md)
- Issue tracker: [ISSUES.md](ISSUES.md)
- Ultimate proof roadmap: [docs/ULTIMATE_PROOF_ROADMAP.md](docs/ULTIMATE_PROOF_ROADMAP.md)
- Kernel architecture: [kernel/README.md](kernel/README.md)

## Current State

Work is active on branch `feat/m1-counter-e2e` (not merged to `main`).

- **Milestone 0:** Skeleton, Iron Law gate (`scripts/iron_law.py`), and self-test harness (`scripts/tests/test_iron_law.py`).
- **Milestone 1 (locally verified `end_to_end=true`; hosted CI awaits PR open):**
  - **Pass 1 (complete and measured):** Exact HOL4 kernel `Term.aconv` verification (`scripts/hol_audit.sml`), SHA-256-pinned trusted specification files (`kernel/SPEC_HASHES.sha256`), exact ELF64 layout and zero-gap byte checks (`scripts/elf64_check.py`), byte-for-byte theorem catalog check (`scripts/export_theorem_catalog.sml`), `41/41` unit/sabotage tests (`scripts/tests/test_iron_law.py`), and `7/7` real HOL4 `Term.aconv` negative controls (`scripts/tests/test_hol_audit_real.py`).
  - **Pass 2 (complete and measured):** Closed `ISS-004` (`forge_arm8Erasure`), `ISS-005` (`forge_shimProof`), and `ISS-006` (`forge_m1Kernel`). Clean replay (`Holmake cleanAll && python3 scripts/iron_law.py`) emitted `end_to_end=true` with `7` compiled `forge_*` theories, `0` pending theories, and `6/6` passing ARM64 black-box smoke tests (`scripts/smoke_m1.py`).
  - **Pass 3 (committed locally; hosted replay pending PR open):** Added upstream-only `Dockerfile.toolchain` and hardened `.github/workflows/iron-law.yml` (Poly/ML 5.9.1, HOL4 `9783a4997`, CakeML `cd9155694`, zero prebuilt `forge_*` theories). Hosted GitHub Actions replay runs once the Milestone 1 PR opens against `main`.

Only `scripts/iron_law.py` decides `end_to_end=true`. See [STATUS.md](STATUS.md) for measured command exit codes and [ISSUES.md](ISSUES.md) for active items.

## Verified Theorem Summary

Every theorem below is exported directly from compiled HOL4 `.dat` files into [docs/THEOREM_CATALOG.md](docs/THEOREM_CATALOG.md) and checked byte-for-byte by `scripts/iron_law.py`.

**Global kernel tags:** `7` compiled `forge_*` theories (`435` transitive theories), `112` definitions, `182` theorems (`294` total verified items), `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`, and `AXIOMS=4` (`bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX`).

| Layer | Theory | Key Theorem / Definition | Plain-English Guarantee |
| --- | --- | --- | --- |
| Pure Spec | `forge_counterSpec` | `counter_run_preserves_cap`, `counter_step_no_overflow`, `counter_step_replay_rejected` | Multi-frame spend counter never exceeds `cap_val` (`10000`), never overflows `u64`, and rejects replays and sequence gaps. |
| Hardware & OS Contract | `forge_contractSpec` | `forge_elf_loaded_def`, `whole_step_def` | SHA-256 pinned initial Linux EL0 ARM64 CPU/ELF contract at `_start` (`0x421000`) and raw `arm8$Next` + `svc #0` transition relation. |
| Zero-Basis CakeML | `forge_counterProg` | `counter_semantics` | Zero-Basis CakeML `counter_prog` terminates cleanly and emits exact `counter_run` frames under all write limits. |
| Verified Compilation | `forge_counterCompile` | `counter_compiled` | In-logic CakeML `arm8` compilation binding `counter_prog` to exact code bytes (`74,396` B) and bitmap data (`3,872` B). |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `encoded_bytes_in_mem_not_svc0`, `arm8_target_exact_encoder_correct`, `machine_sem_real_eq_exact` | Compiled code contains zero `svc #0` (`0xD4000001`), preserves `SP_EL0` with zero CPU exceptions, and matches real EL0 bits (`TBI0`/`TBI1`/`SA0`) unconditionally with zero `b ≠ Fail` escape hatch. |
| Boot & Syscall Shim | `forge_shimProof` | `startup_to_cake_main`, `ffirecv16_universal`, `ffisend16_universal`, `cake_exit_universal` | Exact 43-step `_start -> cake_main` boot proof and universal (`∀`) safety over partial reads/writes, `EINTR` retries, truncated EOF, and `EPIPE`/fatal errors on Linux `read(63)`, `write(64)`, and `exit_group(94)`. |
| Non-Vacuity Witness | `forge_m1Kernel` | `forge_m1_nonvacuous` | Constructive witness exhibiting a concrete Linux EL0 ARM64 state (`TBI0=T`, `TBI1=F`, `SA0=T`, 16B-aligned `SP_EL0`) satisfying `forge_elf_loaded`. |
| Unified End-to-End | `forge_m1Kernel` | `forge_m1_kernel_correct` | Exact `Term.aconv`-pinned whole-binary theorem from `_start` (`0x421000`) across `RTC whole_step` to `svc #0 exit_group(94)` (`0w`/`1w`/`2w`), prefix safety under arbitrary OS errors, and exact `counter_run` output on `exit_code = 0w`. |

Full verbatim `⊢ ...` statements and per-theorem kernel tags: [docs/THEOREM_CATALOG.md](docs/THEOREM_CATALOG.md).

## Repository Layout

```text
forge-iron/
├── kernel/              # Ring 0: HOL4 specs/proofs, Zero-Basis CakeML counter, raw ARM64 syscall shim
├── spec-compiler/       # Ring 1: Verified canonical spec compiler (future milestones)
├── relay/               # Stateless edge gateway (future milestones)
├── sdk/                 # Ring 2 untrusted host tooling (future milestones)
├── scripts/             # Iron Law gate, HOL4 kernel Term.aconv auditor, ELF64 verifier, catalog exporter, tests
├── docs/                # Auto-generated theorem catalog and TCB elimination roadmap
└── Dockerfile.toolchain # Upstream-only Poly/ML 5.9.1 + HOL4 + CakeML ARM8 toolchain image
```

The earlier research history remains in `mack-dot/forge-lab`.
