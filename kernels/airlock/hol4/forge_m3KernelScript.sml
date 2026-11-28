(*
  Forge Milestone 3: Unified End-to-End Verified ARM64 Crypto-Airlock Kernel Theorem.

  Instantiates the reusable 4-FFI whole-binary airlock composition theorem
  (`forge_airlockComposeTheory.forge_airlock_kernel_compose`) with the SHA-256
  pinned pure crypto-airlock spec (`forge_airlockSpec` + `forge_sha256Spec`),
  zero-SL synthesized CakeML program (`forge_airlockProg`), and in-logic ARM64
  compiled bytes (`forge_airlockCompile`).
*)
Theory forge_m3Kernel
Ancestors
  forge_sha256Spec forge_airlockFfi forge_airlockContract forge_airlockSpec
  forge_frame64Spec forge_runtimeSpec
  forge_airlockRunner forge_airlockProg forge_airlockCompile
  forge_arm8Erasure forge_shimProof forge_slotUtil
  forge_airlockShimBase forge_airlockShimStart forge_airlockShimIo
  forge_airlockShimProof forge_airlockCompose
  targetSem ffi relation arm8 alignment list
Libs
  preamble

Theorem forge_m3_ffis_eval[local] =
  forge_airlockCompileTheory.ffis_def |> CONV_RULE (RAND_CONV EVAL);

Theorem forge_m3_bundle[local]:
  (∀ms0:arm8_state.
     forge_m3_slot_loaded code data ms0 ⇒
       let ms1 = FUNPOW arm8$Next 43 ms0 in
       let cb_end = m3_slot_cb_end (LENGTH code) in
       let bm_end = slot_bm_buf_end (LENGTH data) in
       let cbsp = m3_slot_cbspace (LENGTH code) in
       (∀(io:airlock_io) ffi_if inst_if.
          io.outputs = [] ∧
          m3_real_interfer_ok_slot cb_end bm_end cbsp
            [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
            (bits_of ms0) ffi_if inst_if ⇒
            let rmc = real_mc (bits_of ms0)
                        (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           ffi_if inst_if) in
              rmc.target = arm8_target_real (bits_of ms0) ∧
              ¬machine_sem rmc (airlock_ffi io) ms1 Fail) ∧
       (∀os0:m3_os.
          os0.out = [] ⇒
          ∃os_f ms_f exit_code.
            RTC (m3_whole_step F) (os0, ms0) (os_f, ms_f) ∧
            svc_exit_group_rel exit_code ms_f) ∧
       (∀(os0:m3_os) os_f ms_f exit_code.
          os0.out = [] ∧
          RTC (m3_whole_step T) (os0, ms0) (os_f, ms_f) ∧
          svc_exit_group_rel exit_code ms_f ⇒
            (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
            list$isPREFIX os_f.out
              (if 32 ≤ LENGTH os0.key_in then
                 let key = TAKE 32 os0.key_in in
                 let p512 = pad512 os0.disk in
                   FLAT (SND (airlock_run key
                     (recover_dual_slot key (TAKE 256 p512) (DROP 256 p512))
                     (chunks64 os0.inp)))
               else [])) ∧
       (∀(os0:m3_os) os_f ms_f exit_code.
          os0.out = [] ∧
          RTC (m3_whole_step F) (os0, ms0) (os_f, ms_f) ∧
          svc_exit_group_rel exit_code ms_f ∧
          exit_code = 0w ⇒
            os_f.out =
              (if 32 ≤ LENGTH os0.key_in then
                 let key = TAKE 32 os0.key_in in
                 let p512 = pad512 os0.disk in
                   FLAT (SND (airlock_run key
                     (recover_dual_slot key (TAKE 256 p512) (DROP 256 p512))
                     (chunks64 os0.inp)))
               else []))) ∧
  (∃ms0:arm8_state.
     forge_m3_slot_loaded code data ms0 ∧
     ms0.TCR_EL1.TBI0 ∧
     ¬ms0.TCR_EL1.TBI1 ∧
     ms0.SCTLR_EL1.SA0 ∧
     aligned 4 ms0.SP_EL0)
Proof
  mp_tac airlock_compiled \\ strip_tac
  \\ qspecl_then [`recover_dual_slot`, `airlock_step`, `airlock_prog`, `code`, `data`, `info`, `oracle`]
       mp_tac forge_airlock_kernel_compose
  \\ impl_tac
  >- (simp [airlock_semantics, FORGE_M3_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
      \\ metis_tac [forge_m3_ffis_eval])
  \\ simp [airlock_exec_eq_run]
QED

Theorem forge_m3_kernel_correct = cj 1 forge_m3_bundle;
Theorem forge_m3_nonvacuous = cj 2 forge_m3_bundle;
