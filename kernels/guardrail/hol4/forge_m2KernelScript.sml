(*
  Forge Milestone 2: Unified End-to-End Verified ARM64 Guardrail Kernel Theorem.

  Instantiates the frozen reusable 64-byte whole-binary kernel composition theorem
  (`forge_frame64ComposeTheory.forge_frame64_kernel_compose`) with the frozen
  91-line guardrail spec (`forge_guardrailSpec`), zero-SL synthesized CakeML
  program (`forge_guardrailProg`), and in-logic ARM64 compiled bytes
  (`forge_guardrailCompile`).
*)
Theory forge_m2Kernel
Ancestors
  forge_guardrailSpec forge_frame64Spec forge_runtimeSpec
  forge_guardrailProg forge_guardrailCompile
  forge_arm8Erasure forge_shimProof forge_slotUtil forge_frame64Compose
  targetSem ffi relation arm8 alignment list
Libs
  preamble

Theorem forge_m2_ffis_eval[local] =
  forge_guardrailCompileTheory.ffis_def |> CONV_RULE (RAND_CONV EVAL);

Theorem forge_m2_bundle[local]:
  (∀ms0:arm8_state.
     forge_slot_loaded forge_shim64_words code data ms0 ⇒
       let ms1 = FUNPOW arm8$Next 43 ms0 in
       let cb_end = slot_cb_end (LENGTH code) in
       let bm_end = slot_bm_buf_end (LENGTH data) in
       let cbsp = slot_cbspace (LENGTH code) in
       (∀(io:frame64_io) ffi_if inst_if.
          io.outputs = [] ∧
          real_interfer_ok_slot cb_end bm_end cbsp
            [ExtCall «send64»; ExtCall «recv64»] (bits_of ms0) ffi_if inst_if ⇒
            let rmc = real_mc (bits_of ms0)
                        (forge_mc_slot cb_end bm_end
                           [ExtCall «send64»; ExtCall «recv64»] ffi_if inst_if) in
              rmc.target = arm8_target_real (bits_of ms0) ∧
              ¬machine_sem rmc (frame64_ffi io) ms1 Fail) ∧
       (∀inp:word8 list.
          ∃inp_f out_f ms_f exit_code.
            RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
              (inp, [], ms0) (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel exit_code ms_f) ∧
       (∀(inp:word8 list) inp_f out_f ms_f exit_code.
          RTC (whole_step svc_read_rel svc_write_rel)
            (inp, [], ms0) (inp_f, out_f, ms_f) ∧
          svc_exit_group_rel exit_code ms_f ⇒
            (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
            list$isPREFIX out_f
              (FLAT (SND (frame64_run gr_step gr_init (chunks64 inp))))) ∧
       (∀(inp:word8 list) inp_f out_f ms_f exit_code.
          RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
            (inp, [], ms0) (inp_f, out_f, ms_f) ∧
          svc_exit_group_rel exit_code ms_f ∧
          exit_code = 0w ⇒
            out_f = FLAT (SND (frame64_run gr_step gr_init (chunks64 inp))))) ∧
  (∃ms0:arm8_state.
     forge_slot_loaded forge_shim64_words code data ms0 ∧
     ms0.TCR_EL1.TBI0 ∧
     ¬ms0.TCR_EL1.TBI1 ∧
     ms0.SCTLR_EL1.SA0 ∧
     aligned 4 ms0.SP_EL0)
Proof
  mp_tac guardrail_compiled \\ strip_tac
  \\ qspecl_then [`gr_step`, `gr_init`, `guardrail_prog`, `code`, `data`, `info`, `oracle`]
       mp_tac forge_frame64_kernel_compose
  \\ impl_tac
  >- (simp [guardrail_semantics, FORGE_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
      \\ metis_tac [forge_m2_ffis_eval])
  \\ simp []
QED

Theorem forge_m2_kernel_correct = cj 1 forge_m2_bundle;
Theorem forge_m2_nonvacuous = cj 2 forge_m2_bundle;
