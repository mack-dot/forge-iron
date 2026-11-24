# Status

end_to_end=false

| Item | State |
| --- | --- |
| Current milestone | Milestone 1 (not started) |
| Kernel theorem | none |
| HOL4 replay in CI | not installed in CI yet |
| Gate self-test | 12 negative-control cases (`scripts/tests/test_iron_law.py`) |
| Merge blocking | needs a required status check on `main` (owner action) |

## Known limits of the gate

- The `cheat` check is textual. HOL oracle tags are not read yet.
- The gate does not yet prove that the hash file comes from the theorem
  statement. Milestone 1 must bind them.
- The fake `Holmake` in the self-test proves only the gate logic.

## Open questions from the plan (to record, not to assume)

- Linux syscall behavior cannot be proved inside HOL4. It can only be an
  explicit, tested premise. "Premises proved" in Theorem 4 needs a precise meaning.
- CakeML's Silver is a separate verified CPU (its own ISA), not ARM64. The
  FPGA path proves a different binary for a different machine. ECP5 support is unverified.
- A full CakeML build is large. Hosted runners may not fit it; a cached
  build or a self-hosted runner may be necessary.
