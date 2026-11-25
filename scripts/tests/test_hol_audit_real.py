#!/usr/bin/env python3
"""Real HOL4 negative controls for scripts/hol_audit.sml (Exact Term.aconv Edition).

Builds actual forged HOL4 theories in a temporary directory and runs the real
`scripts/hol_audit.sml` against each one to prove that the HOL4 kernel auditor
enforces EXACT `Term.aconv` against the pinned expected theorem statements
(constructed BEFORE loading the prover's theory) and rejects every attack:
  1. Missing `forge_m1_nonvacuous` theorem
  2. Shadowed local constant with bare name `counter_run` (parser/overload hijack)
  3. `F ==>` vacuous antecedent
  4. `b <> ffi$Fail` premise escape hatch
  5. Tacked-on top-level biconditional conjunct (`shim_step <=> ...`)
  6. Dropped liveness conjunct / partial theorem
  7. Subtle 1-symbol weakening on `forge_m1_nonvacuous` (dropping `aligned 4 SP_EL0`)
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
AUDIT_SML = ROOT / "scripts" / "hol_audit.sml"
HOL_DIR = ROOT / "kernel" / "hol4"


def run_forged_theory(
    hol_bin: str,
    holmake_bin: str,
    cakeml_dir: str,
    name: str,
    script_body: str,
    want_err_substr: str,
) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory(prefix=f"forge-audit-neg-{name}-") as td:
        tmp = Path(td)
        (tmp / "Holmakefile").write_text(
            f"INCLUDES = {HOL_DIR} \\\n"
            f"           $(CAKEMLDIR)/misc $(CAKEMLDIR)/semantics $(CAKEMLDIR)/semantics/ffi \\\n"
            f"           $(CAKEMLDIR)/semantics/proofs $(CAKEMLDIR)/translator $(CAKEMLDIR)/characteristic \\\n"
            f"           $(CAKEMLDIR)/basis $(CAKEMLDIR)/compiler/backend $(CAKEMLDIR)/compiler/backend/semantics \\\n"
            f"           $(CAKEMLDIR)/compiler/backend/proofs $(CAKEMLDIR)/compiler/backend/arm8 \\\n"
            f"           $(CAKEMLDIR)/compiler/backend/arm8/proofs $(CAKEMLDIR)/compiler/encoders/arm8 \\\n"
            f"           $(CAKEMLDIR)/compiler/encoders/arm8/proofs $(CAKEMLDIR)/compiler/encoders/asm \\\n"
            f"           $(CAKEMLDIR)/cv_translator \\\n"
            f"           $(HOLDIR)/examples/l3-machine-code/arm8/model $(HOLDIR)/examples/l3-machine-code/arm8/step\n"
            f"HOLHEAP = $(CAKEMLDIR)/cv_translator/cake_compile_heap\n"
        )
        thy = f"forge_neg_{name}"
        (tmp / f"{thy}Script.sml").write_text(script_body)

        env = dict(os.environ)
        env["CAKEMLDIR"] = cakeml_dir
        bm = subprocess.run(
            [holmake_bin, "--qof", "-j", "1", "--no_prereqs", f"{thy}Theory.uo"],
            cwd=tmp,
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if bm.returncode != 0:
            return False, f"forged theory failed to build: {(bm.stderr or bm.stdout)[-400:]}"

        out_dir = tmp / "audit_out"
        out_dir.mkdir()
        heap = str(Path(cakeml_dir) / "cv_translator" / "cake_compile_heap")
        env.update(
            {
                "FORGE_AUDIT_THEORY": thy,
                "FORGE_AUDIT_THEOREM": "forge_m1_kernel_correct",
                "FORGE_AUDIT_NONVAC_THEOREM": "forge_m1_nonvacuous",
                "FORGE_AUDIT_SPEC_THY": "forge_counterSpec",
                "FORGE_AUDIT_CONTRACT_THY": "forge_contractSpec",
                "FORGE_AUDIT_COMPILE_THY": "forge_counterCompile",
                "FORGE_AUDIT_SHIM_THY": "forge_shimProof",
                "FORGE_AUDIT_OUT_DIR": str(out_dir),
            }
        )
        ar = subprocess.run(
            [hol_bin, "--zero", f"--holstate={heap}"],
            cwd=tmp,
            env=env,
            stdin=AUDIT_SML.open("rb"),
            capture_output=True,
            text=True,
            timeout=60,
        )
        combined = (ar.stderr + "\n" + ar.stdout).strip()
        ok = ar.returncode != 0 and "AUDIT_OK" not in ar.stdout and want_err_substr in combined
        last_line = [ln for ln in combined.splitlines() if "HOL_AUDIT_FAIL" in ln]
        msg = last_line[-1] if last_line else combined[-200:]
        return ok, f"exit {ar.returncode}; {msg}"


COMMON_HEADER = """Theory forge_neg_{name}
Ancestors
  forge_counterSpec forge_contractSpec forge_counterCompile targetSem relation alignment arm8
Libs
  preamble
"""

VALID_NONVAC_STUB = r"""
Theorem forge_m1_nonvacuous:
  ∃ms0:arm8_state.
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
Proof
  qexists_tac `(ARB:arm8_state) with <|
    SCTLR_EL1 := ((ARB:SCTLRType) with SA0 := T);
    TCR_EL1 := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
    SP_EL0 := 0x490000w |>`
  \\ simp [] \\ EVAL_TAC
QED
"""

CASES = [
    (
        "missing_nonvac",
        COMMON_HEADER.format(name="missing_nonvac")
        + r"""
Theorem forge_m1_kernel_correct:
  T
Proof
  simp []
QED
""",
        "missing non-vacuity theorem",
    ),
    (
        "shadow_const",
        COMMON_HEADER.format(name="shadow_const")
        + r"""
Definition counter_run_def:
  counter_run (x:num) = x
End

Definition forge_elf_loaded_def:
  forge_elf_loaded (b:word8 list) (d:num list) (m:arm8_state) = T
End

Theorem forge_m1_nonvacuous:
  ∃ms0.
    forge_elf_loaded code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
Proof
  qexists_tac `(ARB:arm8_state) with <|
    SCTLR_EL1 := ((ARB:SCTLRType) with SA0 := T);
    TCR_EL1 := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
    SP_EL0 := 0x490000w |>`
  \\ simp [forge_elf_loaded_def] \\ EVAL_TAC
QED

Theorem forge_m1_kernel_correct:
  ∀ms0. forge_elf_loaded code data ms0 ⇒ counter_run 0 = 0
Proof
  simp [counter_run_def]
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_shadow_const.forge_m1_kernel_correct",
    ),
    (
        "false_ant",
        COMMON_HEADER.format(name="false_ant")
        + VALID_NONVAC_STUB
        + r"""
Theorem forge_m1_kernel_correct:
  ∀ms0:arm8_state.
    F ∧ forge_elf_loaded code data ms0 ⇒
      let ms1 = FUNPOW arm8$Next 43 ms0 in
      (∀(io:counter_io) ffi_if inst_if.
         io.outputs = [] ∧ real_interfer_ok (bits_of ms0) ffi_if inst_if ⇒
           let rmc = real_mc (bits_of ms0) (forge_mc_with ffi_if inst_if) in
             rmc.target = arm8_target_real (bits_of ms0) ∧
             ¬machine_sem rmc (counter_ffi io) ms1 Fail)
Proof
  simp []
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_false_ant.forge_m1_kernel_correct",
    ),
    (
        "b_neq_fail",
        COMMON_HEADER.format(name="b_neq_fail")
        + VALID_NONVAC_STUB
        + r"""
Theorem forge_m1_kernel_correct:
  ∀ms0:arm8_state.
    forge_elf_loaded code data ms0 ⇒
      ∀io ffi_if inst_if b.
        b ≠ Fail ∧ machine_sem (real_mc (bits_of ms0) (forge_mc_with ffi_if inst_if)) (counter_ffi io) ms0 b ⇒
        (real_mc (bits_of ms0) (forge_mc_with ffi_if inst_if)).target = arm8_target_real (bits_of ms0)
Proof
  simp [real_mc_def]
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_b_neq_fail.forge_m1_kernel_correct",
    ),
    (
        "pasted_def_iff",
        COMMON_HEADER.format(name="pasted_def_iff")
        + VALID_NONVAC_STUB
        + r"""
Theorem forge_m1_kernel_correct:
  ∀ms0:arm8_state.
    forge_elf_loaded code data ms0 ⇒
      (∀inp out s inp' out' s'.
         shim_step (inp, out, s) (inp', out', s') ⇔
         whole_step svc_read_rel svc_write_rel (inp, out, s) (inp', out', s'))
Proof
  simp [shim_step_def]
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_pasted_def_iff.forge_m1_kernel_correct",
    ),
    (
        "weakened_nonvac",
        COMMON_HEADER.format(name="weakened_nonvac")
        + r"""
Theorem forge_m1_nonvacuous:
  ∃ms0:arm8_state.
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0
Proof
  qexists_tac `(ARB:arm8_state) with <|
    SCTLR_EL1 := ((ARB:SCTLRType) with SA0 := T);
    TCR_EL1 := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>) |>`
  \\ simp []
QED

Theorem forge_m1_kernel_correct:
  ∀ms0:arm8_state.
    forge_elf_loaded code data ms0 ⇒
      (real_mc (bits_of ms0) (forge_mc_with ARB ARB)).target = arm8_target_real (bits_of ms0)
Proof
  simp [real_mc_def]
QED
""",
        "EXACT_TERM_MISMATCH",
    ),
    (
        "weakened_exit_code",
        COMMON_HEADER.format(name="weakened_exit_code")
        + VALID_NONVAC_STUB
        + r"""
Theorem forge_m1_kernel_correct:
  ∀ms0:arm8_state.
    forge_elf_loaded code data ms0 ⇒
      let ms1 = FUNPOW arm8$Next 43 ms0 in
      (∀(inp:word8 list) inp_f out_f ms_f exit_code.
         RTC (whole_step svc_read_rel svc_write_rel) (inp, [], ms0) (inp_f, out_f, ms_f) ∧
         svc_exit_group_rel exit_code ms_f ⇒ T)
Proof
  simp []
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_weakened_exit_code.forge_m1_kernel_correct",
    ),
]


def main() -> int:
    hol_bin = shutil.which("hol")
    holmake_bin = shutil.which("Holmake")
    cakeml_dir = os.environ.get("CAKEMLDIR")
    if not hol_bin or not holmake_bin or not cakeml_dir:
        print("FAIL: set PATH (with hol/Holmake) and CAKEMLDIR to run real HOL4 audit negative controls")
        return 1
    bad = 0
    for name, body, want in CASES:
        ok, info = run_forged_theory(hol_bin, holmake_bin, cakeml_dir, name, body, want)
        bad += not ok
        print(f"{'PASS' if ok else 'FAIL'} hol_audit reject {name}: {info}")
    print(f"{len(CASES) - bad} of {len(CASES)} real HOL4 audit negative controls passed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
