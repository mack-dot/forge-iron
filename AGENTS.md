# Agent rules

Read `MASTER_PLAN.md` and `STATUS.md` first. Work only on the current milestone.

- Never set `end_to_end=true` by hand. Only `scripts/iron_law.py` (delegating to `runtime/iron_law.py`) decides it.
- Never weaken the gate, its self-test, `hol_audit.sml` (`Term.aconv`), `SPEC_HASHES.sha256`, or `.github/workflows/iron-law.yml` without the owner's exact approval.
- Every new gate check needs a planted failure (negative control).
- Nothing from the banned TCB list in `MASTER_PLAN.md` goes into `runtime/`, `kernels/`, `kernel/`, or `spec-compiler/`.
- One branch and one pull request per milestone. Never push to `main`. Never merge.
- Record measured results only. Keep commands that did not run apart from actual exit codes.
- Use ASD-STE100 as an approximately 80% guide: short sentences, active voice.

## Checkpoint Theorem Upload

Whenever a `forge_*` theory finishes compiling cleanly via `Holmake --qof`:

1. Run `scripts/export_theorem_catalog.sml` (use `FORGE_CATALOG_CHECKPOINT=1` mid-milestone; omit it once the top-level theory compiles) to regenerate `docs/THEOREM_CATALOG.md` directly from compiled `*Theory.dat` files. Downstream unbuilt theories are marked `pending` mid-milestone; `scripts/iron_law.py` requires 100% built theories and zero `pending` at the final gate.
2. Update `STATUS.md` with the newly certified theory and its measured definition/theorem counts.
3. Stage ONLY clean source and doc files (never stage `*.dumpedheap`, `*.heap`, `*.uo`, `*.ui`, `*Theory.dat`, or scratch `dbg_*.sml` / `test_*.sml` files), commit, and `git push` to the active milestone branch (`feat/...`; never push directly to `main`).

## Permanent Proving-Speed & Workflow Rules

- **Use `scripts/holctl` for interactive tactic search:** Keep one warm HOL4 session alive in RAM via `scripts/holctl start` (`scripts/hol_repl.py`). Test candidate tactics with `holctl goal` / `holctl step` (auto-canceling loops at 5.0s via SML `TimeLimit.timeLimit`) and undo with `holctl back`. Never replay 1,000+ lines of `.sml` via `sed | hol` per tactic guess.
- **Run `Holmake --qof` in the foreground with `gtimeout`:** Always wrap `Holmake --qof -j 1 --no_prereqs` with `gtimeout` (e.g. `gtimeout 600` for normal theories, `gtimeout 1200` for erasure/compile theories) instead of idling or yielding mid-pipeline.
- **Use `ml_translator` + frozen `runtime/` for all kernel logic:** Write application logic as pure HOL4 functions over `frame64` and synthesize CakeML code and proofs automatically via `ml_translatorLib.translate` + `runtime/hol4/forge_frameRunnerTheory`. Never write manual Separation Logic (`W8ARRAY`) or re-prove ARM64 startup/syscall assembly for new kernels.
- **Keep new `*Script.sml` files concise:** Aim for a `<= 350`-line soft cap per new `*Script.sml` file; split helper lemmas cleanly rather than growing monolithic proof scripts.
- **3-way parallel tactic race on stalls:** If any single lemma stalls past 3 interactive tries, spawn 3 read-only subagents in parallel to test distinct proof strategies (e.g., `BBLAST_TAC`, algebraic induction/simplification, or intermediate lemma decomposition) and adopt the first clean proof.
- **Pre-build `forge_factory.heap`:** Run `make factory-heap` to dump a single local `forge_factory.heap` preloading `ml_translatorLib`, `blastLib`, `cfLib`, `forge_arm8ErasureTheory`, `forge_shimProofTheory`, and `forge_frameRunnerTheory`. Never commit `*.dumpedheap` or `*.heap` files.

## HOL4 Fast-Path Rules

- Never pass `WORD_ADD_COMM` directly to `simp []` or `REWRITE_TAC` (causes an infinite loop; use `AC`, `WORD_ARITH_ss`, or `blastLib.BBLAST_TAC`).
- Use `blastLib.BBLAST_TAC` for fixed-width word bounds and bitfield identities; never run `WORD_DECIDE_TAC` on symbolic `n2w k` terms (prove `:num` bounds first with `gvs []`).
- Avoid variable names `addr`, `rem`, `cnt`, and `target` that collide with `asm$`, `integer$`, or `targetSem$` constants.
- Use `MATCH_MP_TAC` instead of `irule` when a rule's conclusion is a conjunction matching a conjunctive goal.
- Parenthesize `(t1 \\ t2 >- t3)` when `>-` follows a tactic that produces multiple subgoals.
