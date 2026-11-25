# forge-iron

Proof-gated ARM64 execution engine built in HOL4 and Zero-Basis CakeML with zero `libc` and zero C compiler.

- Master plan: [MASTER_PLAN.md](MASTER_PLAN.md)
- Live status & measured logs: [STATUS.md](STATUS.md)
- Issue tracker: [ISSUES.md](ISSUES.md)
- Ultimate proof roadmap: [docs/ULTIMATE_PROOF_ROADMAP.md](docs/ULTIMATE_PROOF_ROADMAP.md)
- Kernel architecture: [kernel/README.md](kernel/README.md)

## Current State

Work is active on branch `feat/m1-counter-e2e` (not merged to `main`).

- **Milestone 0:** Skeleton, Iron Law gate (`scripts/iron_law.py`), and self-test harness (`scripts/tests/test_iron_law.py`).
- **Milestone 1 (hardening in progress):**
  - **Pass 1 (complete and measured):** Locked the gate with exact HOL4 kernel `Term.aconv` statement verification (`scripts/hol_audit.sml`), SHA-256-pinned trusted specification files (`kernel/SPEC_HASHES.sha256`), exact ELF64 layout and zero-gap byte checks (`scripts/elf64_check.py`), 38/38 passing unit/sabotage tests (`scripts/tests/test_iron_law.py`), and 7/7 passing real HOL4 `Term.aconv` negative controls (`scripts/tests/test_hol_audit_real.py`).
  - **Pass 2 (in progress):** Closing proof gaps `ISS-004` (`forge_arm8ErasureScript.sml`), `ISS-005` (`forge_shimProofScript.sml`), and `ISS-006` (`forge_m1KernelScript.sml`) against the upgraded `Term.aconv`-pinned theorem.
  - **Pass 3 (pending):** Upstream-only `Dockerfile.toolchain`, hosted GitHub Actions CI replay (`.github/workflows/iron-law.yml`), and independent read-only re-audit before opening the Milestone 1 PR into `main`.

Only `scripts/iron_law.py` decides `end_to_end=true`. See [STATUS.md](STATUS.md) for measured command exit codes and [ISSUES.md](ISSUES.md) for active blockers.

## Repository Layout

```text
forge-iron/
├── kernel/              # Ring 0: HOL4 specs/proofs, Zero-Basis CakeML counter, raw ARM64 syscall shim
├── spec-compiler/       # Ring 1: Verified canonical spec compiler (future milestones)
├── relay/               # Stateless edge gateway (future milestones)
├── sdk/                 # Ring 2 untrusted host tooling (future milestones)
├── scripts/             # Iron Law gate, HOL4 kernel Term.aconv auditor, ELF64 verifier, smoke & sabotage tests
└── docs/                # Long-term TCB elimination roadmap
```

The earlier research history remains in `mack-dot/forge-lab`.
