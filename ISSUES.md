# Issues Tracker

This file tracks open and resolved proof, gate, CI, and architecture issues in `forge-iron`.

## Active Milestone 1 Hardening (Hostile Audit v1 Remediation)

| ID | Severity | Area | Status | Summary |
| --- | --- | --- | --- | --- |
| `ISS-001` | Critical | Gate / Auditor | Closed (Pass 1) | Replaced heuristic constant checks in `scripts/hol_audit.sml` with exact HOL4 kernel `Term.aconv` checks against pinned spec theories loaded first (`kernel/SPEC_HASHES.sha256`, `forge_counterSpecScript.sml`, `forge_contractSpecScript.sml`). Verified with 7 real HOL4 negative controls (`scripts/tests/test_hol_audit_real.py`, 7/7 passed). |
| `ISS-002` | Critical | ELF / Layout | Closed (Pass 1) | Exported all 24 `FORGE_*` addresses and `FORGE_CBSPACE` into `theorem_layout.txt` and enforced exact `e_entry`, `PT_LOAD` RX/RW vaddrs, `p_memsz`, and byte offsets in `scripts/elf64_check.py`. Verified with 38/38 cases in `scripts/tests/test_iron_law.py`. |
| `ISS-003` | High | Build / Portability | Closed (Pass 1) | Removed hardcoded local paths from `kernel/hol4/Holmakefile` and enforced `Holmake --qof -j 1 --no_prereqs` in `scripts/iron_law.py`. |
| `ISS-004` | Critical | Proof (B1) | In progress (Pass 2A) | Remove `b ≠ Fail` premise from `forge_m1_kernel_correct` by proving `arm8_target_exact_encoder_correct`, `encoded_bytes_in_mem_not_svc0`, and `machine_sem_real_eq_exact` in `kernel/hol4/forge_arm8ErasureScript.sml`. |
| `ISS-005` | Critical | Proof (B2) | In progress (Pass 2B) | Upgrade `ffirecv16` and `ffisend16` in `kernel/hol4/forge_shimProofScript.sml` from existential happy-path lemmas to universal (`∀`) safety over arbitrary OS partial reads/writes, `EINTR` retries, truncated `<16B` EOF, and fatal read/write errors. |
| `ISS-006` | Critical | Proof (B3) | Open (Pass 2C) | Unify startup, real-bits CakeML execution, and verified syscall shim in `kernel/hol4/forge_m1KernelScript.sml` to match the exact `Term.aconv`-pinned statement in `scripts/hol_audit.sml`. |
| `ISS-007` | Critical | CI / Reproducibility | Open (Pass 3) | Add upstream-only `Dockerfile.toolchain` (Poly/ML 5.9.1, HOL4 `9783a4997`, CakeML `cd9155694`, zero `forge-iron` theories), fix `.github/workflows/iron-law.yml`, and verify hosted GitHub Actions replay on `mack-dot/forge-iron`. |

## Repository & Future Milestone Issues

| ID | Severity | Area | Status | Summary |
| --- | --- | --- | --- | --- |
| `ISS-008` | Medium | Governance | Open (Owner action) | Configure GitHub branch protection and required `iron-law` status checks on `main` once Milestone 1 earns `end_to_end=true` under the hardened gate. |
| `ISS-009` | Medium | Milestone 2 | Planned | Extend the syscall shim with `pwrite64` and `fdatasync`, and add verified allocation-free SHA-256, HMAC-SHA256, and dual-slot (`Slot A` / `Slot B`) crash recovery. |
| `ISS-010` | Long-term | TCB Elimination | Planned | Replace the Linux `svc #0` syscall boundary with a verified microkernel (`seL4` / Microkit) and pursue verified hardware execution per `docs/ULTIMATE_PROOF_ROADMAP.md`. |

## Verification Rule for Closing Issues

An issue moves to `Closed` only after its fix and planted negative control (for gate changes) or clean `Holmake --qof -j 1 --no_prereqs` replay (for proof changes) exit with code `0`.
