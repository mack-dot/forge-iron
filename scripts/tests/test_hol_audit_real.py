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
AUDIT_SML = ROOT / "runtime" / "hol_audit.sml"
HOL_DIR_M1 = ROOT / "kernels" / "counter" / "hol4"
HOL_DIR_M2 = ROOT / "kernels" / "guardrail" / "hol4"
HOL_DIR_M3 = ROOT / "kernels" / "airlock" / "hol4"
RT_DIR = ROOT / "runtime" / "hol4"


def run_forged_theory(
    hol_bin: str,
    holmake_bin: str,
    cakeml_dir: str,
    name: str,
    script_body: str,
    want_err_substr: str,
    *,
    hol_dir: Path = HOL_DIR_M1,
    audit_thm: str = "forge_m1_kernel_correct",
    nonvac_thm: str = "forge_m1_nonvacuous",
    spec_thy: str = "forge_counterSpec",
    contract_thy: str = "forge_runtimeSpec",
    compile_thy: str = "forge_counterCompile",
    shim_thy: str = "forge_shimProof",
    extra_scripts: dict[str, str] | None = None,
    include_hol_dir: bool = True,
) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory(prefix=f"forge-audit-neg-{name}-") as td:
        tmp = Path(td)
        inc_prefix = f"{hol_dir} {RT_DIR}" if include_hol_dir else f"{RT_DIR}"
        (tmp / "Holmakefile").write_text(
            f"INCLUDES = {inc_prefix} \\\n"
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
        env = dict(os.environ)
        env["CAKEMLDIR"] = cakeml_dir
        if extra_scripts:
            for ename, ebody in extra_scripts.items():
                (tmp / f"{ename}Script.sml").write_text(ebody)
                ebm = subprocess.run(
                    [holmake_bin, "--qof", "-j", "1", "--no_prereqs", f"{ename}Theory.uo"],
                    cwd=tmp,
                    env=env,
                    capture_output=True,
                    text=True,
                    timeout=120,
                )
                if ebm.returncode != 0:
                    return False, f"extra forged theory {ename} failed to build: {(ebm.stderr or ebm.stdout)[-400:]}"

        thy = f"forge_neg_{name}"
        (tmp / f"{thy}Script.sml").write_text(script_body)

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
                "FORGE_AUDIT_THEOREM": audit_thm,
                "FORGE_AUDIT_NONVAC_THEOREM": nonvac_thm,
                "FORGE_AUDIT_SPEC_THY": spec_thy,
                "FORGE_AUDIT_CONTRACT_THY": contract_thy,
                "FORGE_AUDIT_COMPILE_THY": compile_thy,
                "FORGE_AUDIT_SHIM_THY": shim_thy,
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
  forge_counterSpec forge_runtimeSpec forge_counterCompile targetSem relation alignment arm8
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
    SP_EL0 := 0x500000w |>`
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

Definition forge_slot_loaded_def:
  forge_slot_loaded (s:word32 list) (b:word8 list) (d:num list) (m:arm8_state) = T
End

Theorem forge_m1_nonvacuous:
  ∃ms0.
    forge_slot_loaded forge_shim16_words code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
Proof
  qexists_tac `(ARB:arm8_state) with <|
    SCTLR_EL1 := ((ARB:SCTLRType) with SA0 := T);
    TCR_EL1 := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
    SP_EL0 := 0x500000w |>`
  \\ simp [forge_slot_loaded_def] \\ EVAL_TAC
QED

Theorem forge_m1_kernel_correct:
  ∀ms0. forge_slot_loaded forge_shim16_words code data ms0 ⇒ counter_run 0 = 0
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
    F ∧ forge_slot_loaded forge_shim16_words code data ms0 ⇒
      let ms1 = FUNPOW arm8$Next 43 ms0 in
      let cb_end = slot_cb_end (LENGTH code) in
      let bm_end = slot_bm_buf_end (LENGTH data) in
      let cbsp = slot_cbspace (LENGTH code) in
      (∀(io:counter_io) ffi_if inst_if.
         io.outputs = [] ∧ real_interfer_ok_slot cb_end bm_end cbsp [ExtCall «send16»; ExtCall «recv16»] (bits_of ms0) ffi_if inst_if ⇒
           let rmc = real_mc (bits_of ms0) (forge_mc_slot cb_end bm_end [ExtCall «send16»; ExtCall «recv16»] ffi_if inst_if) in
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
    forge_slot_loaded forge_shim16_words code data ms0 ⇒
      ∀io ffi_if inst_if b.
        b ≠ Fail ∧ machine_sem (real_mc (bits_of ms0) (forge_mc_slot (slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data)) [ExtCall «send16»; ExtCall «recv16»] ffi_if inst_if)) (counter_ffi io) ms0 b ⇒
        (real_mc (bits_of ms0) (forge_mc_slot (slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data)) [ExtCall «send16»; ExtCall «recv16»] ffi_if inst_if)).target = arm8_target_real (bits_of ms0)
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
    forge_slot_loaded forge_shim16_words code data ms0 ⇒
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
        r"""Theory forge_neg_weakened_nonvac
Ancestors
  forge_m1Kernel forge_counterSpec forge_runtimeSpec forge_counterCompile targetSem relation alignment arm8
Libs
  preamble

Theorem forge_m1_nonvacuous:
  ∃ms0:arm8_state.
    forge_slot_loaded forge_shim16_words code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0
Proof
  mp_tac forge_m1KernelTheory.forge_m1_nonvacuous \\ metis_tac []
QED

Theorem forge_m1_kernel_correct = forge_m1KernelTheory.forge_m1_kernel_correct;
""",
        "EXACT_TERM_MISMATCH on forge_neg_weakened_nonvac.forge_m1_nonvacuous",
    ),
    (
        "weakened_exit_code",
        COMMON_HEADER.format(name="weakened_exit_code")
        + VALID_NONVAC_STUB
        + r"""
Theorem forge_m1_kernel_correct:
  ∀ms0:arm8_state.
    forge_slot_loaded forge_shim16_words code data ms0 ⇒
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


M2_CASES = [
    (
        "m2_wrong_shim16",
        r"""Theory forge_neg_m2_wrong_shim16
Ancestors
  forge_m2Kernel forge_guardrailSpec forge_frame64Spec forge_runtimeSpec forge_guardrailCompile
  forge_slotUtil targetSem relation alignment arm8
Libs
  preamble

Theorem forge_m2_nonvacuous:
  ∃ms0:arm8_state.
    forge_slot_loaded forge_shim16_words code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
Proof
  mp_tac guardrail_compiled \\ strip_tac
  \\ irule forge_slot_nonvacuous
  \\ simp [forge_shim16_words_def, FORGE_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
QED

Theorem forge_m2_kernel_correct = forge_m2KernelTheory.forge_m2_kernel_correct;
""",
        "EXACT_TERM_MISMATCH on forge_neg_m2_wrong_shim16.forge_m2_nonvacuous",
        {"hol_dir": HOL_DIR_M2, "audit_thm": "forge_m2_kernel_correct", "nonvac_thm": "forge_m2_nonvacuous",
         "spec_thy": "forge_guardrailSpec", "compile_thy": "forge_guardrailCompile"},
    ),
    (
        "m2_shadow_const",
        r"""Theory forge_neg_m2_shadow_const
Ancestors
  forge_guardrailSpec forge_frame64Spec forge_runtimeSpec forge_guardrailCompile targetSem relation alignment arm8
Libs
  preamble

Definition gr_step_def:
  gr_step (x:num) = x
End

Definition forge_slot_loaded_def:
  forge_slot_loaded (s:word32 list) (b:word8 list) (d:num list) (m:arm8_state) = T
End

Theorem forge_m2_nonvacuous:
  ∃ms0.
    forge_slot_loaded forge_shim64_words code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
Proof
  qexists_tac `(ARB:arm8_state) with <|
    SCTLR_EL1 := ((ARB:SCTLRType) with SA0 := T);
    TCR_EL1 := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
    SP_EL0 := 0x500000w |>`
  \\ simp [forge_slot_loaded_def] \\ EVAL_TAC
QED

Theorem forge_m2_kernel_correct:
  ∀ms0. forge_slot_loaded forge_shim64_words code data ms0 ⇒ gr_step 0 = 0
Proof
  simp [gr_step_def]
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_m2_shadow_const.forge_m2_kernel_correct",
        {"hol_dir": HOL_DIR_M2, "audit_thm": "forge_m2_kernel_correct", "nonvac_thm": "forge_m2_nonvacuous",
         "spec_thy": "forge_guardrailSpec", "compile_thy": "forge_guardrailCompile"},
    ),
    (
        "m2_weakened_concl",
        r"""Theory forge_neg_m2_weakened_concl
Ancestors
  forge_m2Kernel forge_guardrailSpec forge_frame64Spec forge_runtimeSpec forge_guardrailCompile targetSem relation alignment arm8
Libs
  preamble

Theorem forge_m2_nonvacuous = forge_m2KernelTheory.forge_m2_nonvacuous;

Theorem forge_m2_kernel_correct:
  ∀ms0:arm8_state.
    forge_slot_loaded forge_shim64_words code data ms0 ⇒
      (∀inp:word8 list.
         ∃inp_f out_f ms_f exit_code.
           RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
             (inp, [], ms0) (inp_f, out_f, ms_f) ∧
           svc_exit_group_rel exit_code ms_f)
Proof
  rpt strip_tac
  \\ mp_tac forge_m2KernelTheory.forge_m2_kernel_correct
  \\ disch_then drule \\ simp [LET_THM]
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_m2_weakened_concl.forge_m2_kernel_correct",
        {"hol_dir": HOL_DIR_M2, "audit_thm": "forge_m2_kernel_correct", "nonvac_thm": "forge_m2_nonvacuous",
         "spec_thy": "forge_guardrailSpec", "compile_thy": "forge_guardrailCompile"},
    ),
    (
        "m2_unsupported_spec",
        r"""Theory forge_neg_m2_unsupported_spec
Ancestors
  forge_runtimeSpec
Libs
  preamble

Theorem forge_m2_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m2_nonvacuous:
  T
Proof
  simp []
QED
""",
        "UNSUPPORTED_SPEC_THEORY: forge_bogusSpec",
        {"hol_dir": HOL_DIR_M2, "audit_thm": "forge_m2_kernel_correct", "nonvac_thm": "forge_m2_nonvacuous",
         "spec_thy": "forge_bogusSpec", "compile_thy": "forge_guardrailCompile"},
    ),
    (
        "m2_wrong_contract_thy",
        r"""Theory forge_neg_m2_wrong_contract_thy
Ancestors
  forge_runtimeSpec
Libs
  preamble

Theorem forge_m2_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m2_nonvacuous:
  T
Proof
  simp []
QED
""",
        "UNSUPPORTED_CONTRACT_THEORY: forge_evilContract",
        {"hol_dir": HOL_DIR_M2, "audit_thm": "forge_m2_kernel_correct", "nonvac_thm": "forge_m2_nonvacuous",
         "spec_thy": "forge_guardrailSpec", "contract_thy": "forge_evilContract",
         "compile_thy": "forge_guardrailCompile"},
    ),
    (
        "m2_wrong_shim_thy",
        r"""Theory forge_neg_m2_wrong_shim_thy
Ancestors
  forge_runtimeSpec
Libs
  preamble

Theorem forge_m2_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m2_nonvacuous:
  T
Proof
  simp []
QED
""",
        "UNSUPPORTED_SHIM_THEORY: forge_evilShim",
        {"hol_dir": HOL_DIR_M2, "audit_thm": "forge_m2_kernel_correct", "nonvac_thm": "forge_m2_nonvacuous",
         "spec_thy": "forge_guardrailSpec", "compile_thy": "forge_guardrailCompile",
         "shim_thy": "forge_evilShim"},
    ),
    (
        "m2_code_def_lhs_decoy",
        r"""Theory forge_neg_m2_code_def_lhs_decoy
Ancestors
  forge_guardrailCompile
Libs
  preamble

Theorem forge_m2_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m2_nonvacuous:
  T
Proof
  simp []
QED
""",
        "CODE_DEF_LHS_MISMATCH",
        {
            "hol_dir": HOL_DIR_M2,
            "include_hol_dir": False,
            "audit_thm": "forge_m2_kernel_correct",
            "nonvac_thm": "forge_m2_nonvacuous",
            "spec_thy": "forge_guardrailSpec",
            "compile_thy": "forge_guardrailCompile",
            "extra_scripts": {
                "forge_guardrailSpec": (HOL_DIR_M2 / "forge_guardrailSpecScript.sml").read_text(),
                "forge_guardrailCompile": r"""Theory forge_guardrailCompile
Ancestors
  words list cv cv_type mlstring
Libs
  preamble

Definition code_real_def:
  code = [0w:word8]
End

Definition decoy_def:
  decoy = [1w:word8]
End

Theorem code_def = decoy_def;

Definition data_def:
  data = [0:num]
End

Definition ffis_def:
  ffis = [«»]
End
""",
            },
        },
    ),
    (
        "m2_shadow_cv_to_word",
        r"""Theory forge_neg_m2_shadow_cv_to_word
Ancestors
  forge_guardrailCompile
Libs
  preamble

Theorem forge_m2_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m2_nonvacuous:
  T
Proof
  simp []
QED
""",
        "CODE_BYTES_MALFORMED",
        {
            "hol_dir": HOL_DIR_M2,
            "include_hol_dir": False,
            "audit_thm": "forge_m2_kernel_correct",
            "nonvac_thm": "forge_m2_nonvacuous",
            "spec_thy": "forge_guardrailSpec",
            "compile_thy": "forge_guardrailCompile",
            "extra_scripts": {
                "forge_guardrailSpec": (HOL_DIR_M2 / "forge_guardrailSpecScript.sml").read_text(),
                "forge_guardrailCompile": r"""Theory forge_guardrailCompile
Ancestors
  words list cv cv_type mlstring
Libs
  preamble

Definition to_list_def:
  to_list (f:cv -> word8) (x:cv) = [0w:word8]
End

Definition to_word_def:
  to_word (x:cv) = (0w:word8)
End

Definition code_def:
  code = to_list to_word (cv$Pair (cv$Num 42) (cv$Num 0))
End

Definition data_def:
  data = [0:num]
End

Definition ffis_def:
  ffis = [«»]
End
""",
            },
        },
    ),
]


M3_CASES = [
    (
        "m3_cross_mix_contract",
        r"""Theory forge_neg_m3_cross_mix_contract
Ancestors
  forge_airlockContract
Libs
  preamble

Theorem forge_m3_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m3_nonvacuous:
  T
Proof
  simp []
QED
""",
        "UNSUPPORTED_CONTRACT_THEORY: forge_runtimeSpec",
        {"hol_dir": HOL_DIR_M3, "audit_thm": "forge_m3_kernel_correct", "nonvac_thm": "forge_m3_nonvacuous",
         "spec_thy": "forge_airlockSpec", "contract_thy": "forge_runtimeSpec",
         "compile_thy": "forge_airlockCompile", "shim_thy": "forge_airlockShimProof"},
    ),
    (
        "m3_cross_mix_shim",
        r"""Theory forge_neg_m3_cross_mix_shim
Ancestors
  forge_airlockContract
Libs
  preamble

Theorem forge_m3_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m3_nonvacuous:
  T
Proof
  simp []
QED
""",
        "UNSUPPORTED_SHIM_THEORY: forge_shimProof",
        {"hol_dir": HOL_DIR_M3, "audit_thm": "forge_m3_kernel_correct", "nonvac_thm": "forge_m3_nonvacuous",
         "spec_thy": "forge_airlockSpec", "contract_thy": "forge_airlockContract",
         "compile_thy": "forge_airlockCompile", "shim_thy": "forge_shimProof"},
    ),
    (
        "m3_cross_mix_m2_contract",
        r"""Theory forge_neg_m3_cross_mix_m2_contract
Ancestors
  forge_airlockContract
Libs
  preamble

Theorem forge_m2_kernel_correct:
  T
Proof
  simp []
QED

Theorem forge_m2_nonvacuous:
  T
Proof
  simp []
QED
""",
        "UNSUPPORTED_CONTRACT_THEORY: forge_airlockContract",
        {"hol_dir": HOL_DIR_M2, "audit_thm": "forge_m2_kernel_correct", "nonvac_thm": "forge_m2_nonvacuous",
         "spec_thy": "forge_guardrailSpec", "contract_thy": "forge_airlockContract",
         "compile_thy": "forge_guardrailCompile", "shim_thy": "forge_shimProof"},
    ),
    (
        "m3_shadow_const",
        r"""Theory forge_neg_m3_shadow_const
Ancestors
  forge_airlockSpec forge_airlockContract forge_airlockCompile targetSem relation alignment arm8
Libs
  preamble

Definition airlock_run_def:
  airlock_run (x:num) = x
End

Definition forge_m3_slot_loaded_def:
  forge_m3_slot_loaded (b:word8 list) (d:num list) (m:arm8_state) = T
End

Theorem forge_m3_nonvacuous:
  ∃ms0.
    forge_m3_slot_loaded code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
Proof
  qexists_tac `(ARB:arm8_state) with <|
    SCTLR_EL1 := ((ARB:SCTLRType) with SA0 := T);
    TCR_EL1 := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
    SP_EL0 := 0x500000w |>`
  \\ simp [forge_m3_slot_loaded_def] \\ EVAL_TAC
QED

Theorem forge_m3_kernel_correct:
  ∀ms0. forge_m3_slot_loaded code data ms0 ⇒ airlock_run 0 = 0
Proof
  simp [airlock_run_def]
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_m3_shadow_const.forge_m3_kernel_correct",
        {"hol_dir": HOL_DIR_M3, "audit_thm": "forge_m3_kernel_correct", "nonvac_thm": "forge_m3_nonvacuous",
         "spec_thy": "forge_airlockSpec", "contract_thy": "forge_airlockContract",
         "compile_thy": "forge_airlockCompile", "shim_thy": "forge_airlockShimProof"},
    ),
    (
        "m3_weakened_nonvac",
        r"""Theory forge_neg_m3_weakened_nonvac
Ancestors
  forge_m3Kernel forge_airlockSpec forge_airlockContract forge_airlockCompile targetSem relation alignment arm8
Libs
  preamble

Theorem forge_m3_nonvacuous:
  ∃ms0:arm8_state.
    forge_m3_slot_loaded code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0
Proof
  mp_tac forge_m3KernelTheory.forge_m3_nonvacuous \\ metis_tac []
QED

Theorem forge_m3_kernel_correct = forge_m3KernelTheory.forge_m3_kernel_correct;
""",
        "EXACT_TERM_MISMATCH on forge_neg_m3_weakened_nonvac.forge_m3_nonvacuous",
        {"hol_dir": HOL_DIR_M3, "audit_thm": "forge_m3_kernel_correct", "nonvac_thm": "forge_m3_nonvacuous",
         "spec_thy": "forge_airlockSpec", "contract_thy": "forge_airlockContract",
         "compile_thy": "forge_airlockCompile", "shim_thy": "forge_airlockShimProof"},
    ),
    (
        "m3_weakened_concl",
        r"""Theory forge_neg_m3_weakened_concl
Ancestors
  forge_m3Kernel forge_airlockSpec forge_airlockContract forge_airlockCompile targetSem relation alignment arm8
Libs
  preamble

Theorem forge_m3_nonvacuous = forge_m3KernelTheory.forge_m3_nonvacuous;

Theorem forge_m3_kernel_correct:
  ∀ms0:arm8_state.
    forge_m3_slot_loaded code data ms0 ⇒
      (∀os0:m3_os.
         os0.out = [] ⇒
         ∃os_f ms_f exit_code.
           RTC (m3_whole_step F) (os0, ms0) (os_f, ms_f) ∧
           svc_exit_group_rel exit_code ms_f)
Proof
  rpt strip_tac
  \\ mp_tac forge_m3KernelTheory.forge_m3_kernel_correct
  \\ disch_then drule \\ simp [LET_THM]
QED
""",
        "EXACT_TERM_MISMATCH on forge_neg_m3_weakened_concl.forge_m3_kernel_correct",
        {"hol_dir": HOL_DIR_M3, "audit_thm": "forge_m3_kernel_correct", "nonvac_thm": "forge_m3_nonvacuous",
         "spec_thy": "forge_airlockSpec", "contract_thy": "forge_airlockContract",
         "compile_thy": "forge_airlockCompile", "shim_thy": "forge_airlockShimProof"},
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
    total = len(CASES) + len(M2_CASES) + len(M3_CASES)
    for name, body, want in CASES:
        ok, info = run_forged_theory(hol_bin, holmake_bin, cakeml_dir, name, body, want)
        bad += not ok
        print(f"{'PASS' if ok else 'FAIL'} hol_audit reject {name}: {info}")
    for name, body, want, kw in M2_CASES:
        ok, info = run_forged_theory(hol_bin, holmake_bin, cakeml_dir, name, body, want, **kw)
        bad += not ok
        print(f"{'PASS' if ok else 'FAIL'} hol_audit reject {name}: {info}")
    for name, body, want, kw in M3_CASES:
        ok, info = run_forged_theory(hol_bin, holmake_bin, cakeml_dir, name, body, want, **kw)
        bad += not ok
        print(f"{'PASS' if ok else 'FAIL'} hol_audit reject {name}: {info}")
    print(f"{total - bad} of {total} real HOL4 audit negative controls passed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
