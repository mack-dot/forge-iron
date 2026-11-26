# Agent rules

Read `MASTER_PLAN.md` and `STATUS.md` first. Work only on the current milestone.

- Never set `end_to_end=true` by hand. Only `scripts/iron_law.py` decides it.
- Never weaken the gate, its self-test, or `.github/workflows/iron-law.yml`
  without the owner's exact approval.
- Every new gate check needs a planted failure (negative control).
- Nothing from the banned TCB list in `MASTER_PLAN.md` goes into `kernel/` or `spec-compiler/`.
- One branch and one pull request per milestone. Never push to `main`. Never merge.
- Record measured results only. Keep commands that did not run apart from actual exit codes.
- Use ASD-STE100 as an approximately 80% guide: short sentences, active voice.

## Checkpoint Theorem Upload

Whenever a `forge_*` theory finishes compiling cleanly via `Holmake --qof`:

1. Run `scripts/export_theorem_catalog.sml` (use `FORGE_CATALOG_CHECKPOINT=1` mid-milestone; omit it once the top-level theory compiles) to regenerate `docs/THEOREM_CATALOG.md` directly from compiled `*Theory.dat` files. Downstream unbuilt theories are marked `pending` mid-milestone; `scripts/iron_law.py` requires 100% built theories and zero `pending` at the final gate.
2. Update `STATUS.md` with the newly certified theory and its measured definition/theorem counts.
3. Stage ONLY clean source and doc files (never stage `*.dumpedheap`, `*.uo`, `*.ui`, `*Theory.dat`, or scratch `dbg_*.sml` / `test_*.sml` files), commit, and `git push` to the active milestone branch (`feat/...`; never push directly to `main`).

## HOL4 Fast-Path Rules

- Never pass `WORD_ADD_COMM` directly to `simp []` (causes an infinite loop; use `AC` or `WORD_ARITH_ss`).
- Never run `WORD_DECIDE_TAC` on symbolic `n2w k` terms (use `blastLib.BBLAST_TAC` on fixed-width words without `n2w`, or prove `:num` bounds first with `gvs []`).
- Avoid variable names `addr`, `rem`, and `cnt` that collide with `asm$` or `integer$` constants.
- Use `MATCH_MP_TAC` instead of `irule` when a rule's conclusion is a conjunction matching a conjunctive goal.
- Parenthesize `(t1 \\ t2 >- t3)` when `>-` follows a tactic that produces multiple subgoals.
- In M2+, pre-build a single `forge_factory.heap` with `ml_translator`, `cfLib`, `forge_arm8Erasure`, and `forge_shimProof` loaded, and never commit `*.dumpedheap` or `*.heap` files.
