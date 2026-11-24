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
