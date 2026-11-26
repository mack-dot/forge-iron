# Milestone 2 Plan: Reusable Verified ARM64 Factory & Guardrail Kernel

**Precondition:** Start on a new branch only AFTER Milestone 1 (`counter`) passes the independent 6-vector red-team audit (`docs/RED_TEAM_AUDIT.md`) and owner review.

## Goal

Turn `forge-iron` into an open-source, reusable verified ARM64 binary factory (zero `libc`, zero C compiler, `_start` to `SVC #0`) and ship Milestone 2: a mathematically unbypassable **Guardrail & Conservation Kernel** enforcing hard spending caps, fund conservation (no double-refunds), destination allowlists, and monotonic nonces over fixed binary frames, ready for live AWS Graviton Nitro Enclave deployment.

## Non-Negotiable Safety & Workflow Rules

1. **Interactive debug, `Holmake --qof` certifies:** Use `--holstate` dumped heaps for fast tactic debugging, kill any hung word-arithmetic tactic within 60s, and certify every milestone with a clean `Holmake --qof` build (zero `.dumpedheap` files committed).
2. **Two-tier resource caps:** Use `--maxheap 6G` and `gtimeout 600` for interactive runs and standard `*Script.sml` files; use a higher safe `--maxheap` (below physical RAM so macOS never swap-freezes) and longer timeout strictly for `*CompileScript.sml`.
3. **Zero oracles + mandatory non-vacuity:** Zero `cheat`, `mk_thm`, `mk_oracle_thm`, or `new_axiom`. Every top-level binary theorem MUST include a proved non-vacuity witness lemma (`|- ?s0. <initial_premise> s0`).
4. **Prover vs. Spec/Gate Separation:** Once the M2 pure spec and Iron-Law Gate are approved and frozen, do NOT modify or weaken them—only fix implementations and proofs to satisfy them.

## Phase A — Refactor into Reusable Verified ARM64 Factory

1. Separate the repository cleanly into:
   - `runtime/`: Frozen verified ARM64 shim (`_start` -> `cake_main`, `cml_hdr0`–`4`, framed `ffirecv`/`ffisend`, `exit_group`, `forge_shimProofTheory`, `hol_audit.sml`, ELF byte-equivalence checker, and negative-control suite).
   - `kernels/counter/`: Existing M1 spec, CakeML program, compile script, and M1 top-level composition.
2. Generalize the shim and composition theorem so any kernel using the fixed-width binary frame FFI ABI plugs straight into `runtime/` without re-proving `_start` or `exit_group` assembly.
3. Prove M1 (`kernels/counter/`) still passes a clean `Holmake --qof` + full Iron-Law Gate after refactoring.

## Phase B — Propose & Freeze M2 Spec (STOP FOR APPROVAL BEFORE PROVING)

1. Design a fixed-width binary frame protocol (32-byte or 64-byte frames; zero variable-length string or JSON parsing) for `kernels/guardrail/` supporting:
   - `DEPOSIT / BUDGET_SET`
   - `SPEND_REQUEST` (`agent_id`, `dest_id`, `amount_u64`, `nonce_u64`)
   - `REFUND` (`tx_id`, `amount_u64`)
   - `QUERY`
2. Draft `kernels/guardrail/forge_guardrailSpecScript.sml` (<100 lines of crystal-clear pure HOL4 math) stating the exact top-level safety theorems:
   - Hard spending cap is never exceeded across any input stream.
   - Non-allowlisted destinations are always denied.
   - Replayed or out-of-order nonces are always denied.
   - Strict fund conservation (`deposits == balances + refunds + spent`), zero double-refunds, and zero 64-bit integer overflow or underflow.
3. **Mandatory Stop Gate:** STOP after Phase A passes and Phase B's pure spec draft is written. Present the <100-line M2 spec and binary frame layout for human review and freezing before writing `forge_guardrailProgScript.sml` or running proofs.
