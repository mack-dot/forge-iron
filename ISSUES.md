# Issues Tracker

This file tracks open and resolved proof, gate, CI, and architecture issues in `forge-iron`.

## Active Milestone 1 Hardening (Hostile Audit v1 Remediation)

| ID | Severity | Area | Status | Summary |
| --- | --- | --- | --- | --- |
| `ISS-001` | Critical | Gate / Auditor | Closed (Pass 1) | Replaced heuristic constant checks in `scripts/hol_audit.sml` with exact HOL4 kernel `Term.aconv` checks against pinned spec theories loaded first (`kernel/SPEC_HASHES.sha256`, `forge_counterSpecScript.sml`, `forge_contractSpecScript.sml`). Verified with 7 real HOL4 negative controls (`scripts/tests/test_hol_audit_real.py`, 7/7 passed). |
| `ISS-002` | Critical | ELF / Layout | Closed (Pass 1) | Exported all 24 `FORGE_*` addresses and `FORGE_CBSPACE` into `theorem_layout.txt` and enforced exact `e_entry`, `PT_LOAD` RX/RW vaddrs, `p_memsz`, and byte offsets in `scripts/elf64_check.py`. Verified with 41/41 cases in `scripts/tests/test_iron_law.py`. |
| `ISS-003` | High | Build / Portability | Closed (Pass 1) | Removed hardcoded local paths from `kernel/hol4/Holmakefile` and enforced `Holmake --qof -j 1 --no_prereqs` in `scripts/iron_law.py`. |
| `ISS-004` | Critical | Proof (B1) | Closed (Pass 2A) | Removed the `b ≠ Fail` escape hatch by proving `encoded_bytes_in_mem_not_svc0`, `arm8_target_exact_ok`, `arm8_target_exact_encoder_correct`, `real_mc_evaluate_exact_eq`, and `machine_sem_real_eq_exact` in `kernel/hol4/forge_arm8ErasureScript.sml`. Verified cleanly via `Holmake --qof -j 1 --no_prereqs forge_arm8ErasureTheory.uo` (`exit 0`, `4` defs / `51` theorems, `HYP_COUNT=0`, `ORACLES=[DISK_THM]`). |
| `ISS-005` | Critical | Proof (B2) | Closed (Pass 2B) | Upgraded `ffirecv16`, `ffisend16`, `cml_exit`, and `cml_install` in `kernel/hol4/forge_shimProofScript.sml` to universal (`∀`) safety over arbitrary OS partial reads/writes, `EINTR` retries, truncated `<16B` EOF, and fatal read/write errors, plus forward error-free liveness and `real_interfer_ok_imp_erase_ok`. Verified cleanly via `Holmake --qof -j 1 --no_prereqs forge_shimProofTheory.uo` (`exit 0`, `1m03s`, `5` defs / `43` theorems, `HYP_COUNT=0`, `ORACLES=[DISK_THM]`). |
| `ISS-006` | Critical | Proof (B3) | Closed (Pass 2C) | Proved `forge_m1_kernel_correct` and `forge_m1_nonvacuous` in `kernel/hol4/forge_m1KernelScript.sml`, matching the exact `Term.aconv`-pinned expected theorems in `scripts/hol_audit.sml`. Verified via clean `Holmake cleanAll && python3 scripts/iron_law.py` (`exit 0`, `end_to_end=true`, `7` theories, `112` defs, `182` thms, `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `4` `bool` axioms). |
| `ISS-007` | Critical | CI / Reproducibility | Open (PR pending) | Committed upstream-only `Dockerfile.toolchain` (Poly/ML 5.9.1, HOL4 `9783a4997`, CakeML `cd9155694`, zero `forge-iron` theories) and updated `.github/workflows/iron-law.yml` to run `Holmake cleanAll`, `scripts/iron_law.py`, `scripts/tests/test_hol_audit_real.py`, and `scripts/smoke_m1.py`. Remains open until hosted GitHub Actions replay passes green on the Milestone 1 PR. |

## Milestone 2 Hardening (Hostile Audit v3 Remediation)

| ID | Severity | Area | Status | Summary |
| --- | --- | --- | --- | --- |
| `ISS-011` | Critical | Gate / Auditor | Closed | Hardened `runtime/hol_audit.sml` to enforce exact `Term.aconv` LHS checks on `code_def`/`data_def`/`ffis_def`/`shim_def`/layout defs, pinned `contract_thy`/`shim_thy`, and `dest_thy_const` checks on `cv$Pair`/`cv$Num`/`cv_type$to_list`/`cv_type$to_word`/`cv$c2n` BEFORE loading the prover's final theory. Verified with 15/15 real HOL4 negative controls (`scripts/tests/test_hol_audit_real.py`). |
| `ISS-012` | High | TCB Boundary | Closed | Moved Ring 2 `json`/TypeScript/Python SDK wrappers and `schema.json` out of `kernels/guardrail/` into `sdk/guardrail/`, updated `scripts/forge_vibe.py`, added `u64` bounds checks in `sdk.ts`, and removed stale `kernel/` directory. |
| `ISS-013` | High | Gate / ELF / Catalog | Closed | Enforced required pinned spec/contract/frame64 entries in `runtime/iron_law.py`, required `frame_bytes` and `rx_tmp + frame_bytes <= forge_heap` in `runtime/elf64_check.py`, removed `extra_rt` pollution from `runtime/export_theorem_catalog.sml` (M1 catalog now exact 7 theories), and upgraded `scripts/smoke_m2.py` to 1-byte chunks + real Linux `-EPIPE`. Verified with 53/53 cases in `scripts/tests/test_iron_law.py` and 6/6 suites in `scripts/smoke_m2.py`. |

## Repository & Future Milestone Issues

| ID | Severity | Area | Status | Summary |
| --- | --- | --- | --- | --- |
| `ISS-008` | Medium | Governance | Open (Owner action) | Configure GitHub branch protection and required `iron-law` status checks on `main` once Milestone 1 passes hosted CI and merges. |
| `ISS-009` | Medium | Milestone 2 | Planned | Extend the syscall shim with `pwrite64` and `fdatasync`, and add verified allocation-free SHA-256, HMAC-SHA256, and dual-slot (`Slot A` / `Slot B`) crash recovery. |
| `ISS-010` | Long-term | TCB Elimination | Planned | Replace the Linux `svc #0` syscall boundary with a verified microkernel (`seL4` / Microkit) and pursue verified hardware execution per `docs/ULTIMATE_PROOF_ROADMAP.md`. |

## Verification Rule for Closing Issues

An issue moves to `Closed` only after its fix and planted negative control (for gate changes) or clean `Holmake --qof -j 1 --no_prereqs` replay (for proof changes) exit with code `0`.
