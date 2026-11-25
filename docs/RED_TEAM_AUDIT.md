# Hostile Read-Only Red-Team Audit Protocol

Never let the prover grade its own homework. Before tagging any milestone or trusting `end_to_end=true`, an independent reviewer (human or clean read-only agent) must attempt to falsify the claim across all 6 attack vectors. Run any sabotage tests inside `/tmp` only; never modify the repository during an audit.

## Attack Vector 1 — Spec & Gate Integrity (`git diff`)

- Inspect all changes to the pure spec (`counter_run` or milestone equivalent), `sem_satisfies`, `scripts/hol_audit.sml`, linker scripts (`kernel/shim/forge.ld`), and `scripts/iron_law.py`.
- Confirm `sem_satisfies` quantifies universally over behaviors (excluding `Fail` and empty sets).
- Confirm no constants are shadowed, weakened, or replaced with trivial definitions.

## Attack Vector 2 — Raw HOL4 Kernel Audit (Inspect Compiled `*Theory.dat` Directly)

- Do not trust build logs. After a fresh `Holmake --qof` with zero `.dumpedheap` files, open a fresh `hol` session (with `--maxheap 6G` and timeout), load the top-level theorem, and print:
  - `Thm.tag` — verify `axioms = []` and oracle tags contain only `DISK_THM` (zero `cheat`, `mk_thm`, `mk_oracle_thm`, `new_axiom` anywhere in the transitive closure, and `DB.axioms` closure contains only the 4 standard `bool` axioms).
  - `Thm.hyp` — verify `[]` (zero unproved assumptions).
  - `Thm.concl` — print the full term with `show_types := true` and explicit theory prefixes (e.g., `forge_counterSpec$counter_run`), and audit every premise line by line.

## Attack Vector 3 — Vacuous Premise Hunt (`False ==> Anything`)

- Audit every hypothesis of the top-level theorem against real Linux ARM64 ELF loader behavior (`_start`, `SP_EL0`, alignment, `forge_regions_disjoint`, memory permissions, processor bits `TBI0`/`TBI1`/`SA0`).
- Require a proved **non-vacuity witness lemma** inside HOL4:
  ```text
  |- ?ms0. <initial_premise> ms0 /\ ms0.TCR_EL1.TBI0 /\ ~ms0.TCR_EL1.TBI1 /\
           ms0.SCTLR_EL1.SA0 /\ aligned 4 ms0.SP_EL0
  ```
- Exhibiting a concrete CPU and memory state inside HOL4 makes it mathematically impossible for the theorem hypotheses to be `False`. Flag a missing witness lemma as a mandatory blocker before tagging.

## Attack Vector 4 — Real ELF Binary & Byte-Equivalence Audit

- Run `readelf -h -l -d` on the ARM64 ELF binary on disk.
- Confirm:
  - Static `ET_EXEC` `AArch64` binary with zero `PT_INTERP`, zero `PT_DYNAMIC`, zero `libc`, zero `ld-linux`.
  - Strict `W^X` and all virtual addresses `< 2^55` (P-LO55).
  - `e_entry` equals `_start` (`FORGE_SHIM_BASE`) in `startup_to_cake_main`.
  - Zero unverified executable gap bytes in `PF_X`.
  - The byte-equivalence gate compares the actual ELF file bytes on disk byte-for-byte against the concrete byte lists extracted directly from the proved HOL4 theorems.

## Attack Vector 5 — Independent Negative Controls (`/tmp` Copy Only)

- Copy the repository/artifacts into `/tmp/forge-iron-sabotage`.
- Flip 1 byte in the `.text` section of the ELF binary and run `scripts/iron_law.py` -> must exit non-zero.
- Inject 1 `cheat` into a proof script and run `scripts/iron_law.py` / `scripts/hol_audit.sml` -> must exit non-zero.

## Attack Vector 6 — Clean-Replay Readiness

- Confirm `git status` tracks zero `.dumpedheap` files, scratch logs, or stale build artifacts.
- Confirm a clean `Holmake --qof --no_prereqs` replay succeeds from scratch with exit `0`.

## Verdict Format

End every audit report with a strict verdict (**PASS** or **FAIL**) and list every gap or weakness found with exact command outputs and file/line evidence.
