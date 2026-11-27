(*
  Forge Reusable Runtime: Generic 64-Byte Whole-Binary Kernel Composition Theory.

  Proves ONE polymorphic end-to-end theorem (`forge_frame64_kernel_compose`) for
  ANY pure 64-byte frame step function `step : 'st -> frame64 -> 'st # frame64`
  and initial state `init : 'st`, linking:
    1. In-logic CakeML arm8 compilation (`compile ... = SOME (code, data, info)`)
    2. Whole-program CakeML source semantics (`sem_satisfies ... frame64_run`)
    3. Frozen 256 KB RX slot + fixed `_start = 0x450000` + `forge_shim64_words`
    4. Exact arm8$Next erasure (`forge_arm8Erasure`) & universal 64B Linux
       `read(63)` / `write(64)` / `exit_group(94)` syscall safety & liveness (`forge_shimProof`)
  into the exact whole-binary execution theorem + non-vacuity witness.
*)
Theory forge_frame64Compose
Ancestors
  forge_frame64Spec forge_frameRunner forge_runtimeSpec
  forge_arm8Erasure forge_shimProof forge_slotUtil
  arm8_target arm8_configProof lab_to_targetProof backendProof ml_prog
  targetProps semanticsProps alignment set_sep byte
Libs
  preamble blastLib wordsLib

(* ---- 1. Generic 64-Byte Stream, Prefix & Trace Helpers ---- *)

Theorem limit_frames64_prefix[local]:
  ∀wlim xs. limit_frames64 wlim xs ≼ xs
Proof
  Cases \\ simp [limit_frames64_def]
  \\ metis_tac [IS_PREFIX_APPEND, listTheory.TAKE_DROP]
QED

Theorem stop_after_err64_prefix[local]:
  ∀xs ys. xs ≼ ys ∧ stop_after_err64 ys ⇒ stop_after_err64 xs
Proof
  Induct \\ simp [stop_after_err64_def]
  \\ rpt strip_tac
  \\ Cases_on `ys` \\ fs [stop_after_err64_def]
  \\ rveq
  \\ Cases_on `event_is_err64 h` \\ fs [stop_after_err64_def]
  \\ metis_tac []
QED

Theorem stop_after_err64_prefix_eq[local]:
  ∀es1 es2.
    es1 ≼ es2 ∧ stop_after_err64 es2 ∧ (∃e. MEM e es1 ∧ event_is_err64 e) ⇒
    es2 = es1
Proof
  Induct \\ simp []
  \\ rpt strip_tac
  \\ Cases_on `es2` \\ fs [stop_after_err64_def]
  \\ rveq
  \\ Cases_on `event_is_err64 h` \\ fs []
  \\ first_x_assum irule \\ simp [] \\ metis_tac []
QED

Theorem sent_frames64_of_prefix[local]:
  ∀xs ys. xs ≼ ys ⇒ sent_frames64_of xs ≼ sent_frames64_of ys
Proof
  rw [IS_PREFIX_APPEND] \\ simp [sent_frames64_of_append]
QED

Theorem FLAT_prefix[local]:
  ∀xs ys. xs ≼ ys ⇒ FLAT xs ≼ FLAT ys
Proof
  rw [IS_PREFIX_APPEND] \\ simp [listTheory.FLAT_APPEND]
QED

Theorem FLAT_snoc_prefix[local]:
  ∀xs f chunk. chunk ≼ f ⇒ FLAT xs ++ chunk ≼ FLAT (xs ++ [f])
Proof
  simp [listTheory.FLAT_APPEND]
QED

Theorem frame64_run_append[local]:
  ∀stepf inps1 inps2 st.
    EVERY (λf. LENGTH f = 64) inps1 ⇒
    SND (frame64_run stepf st (inps1 ++ inps2)) =
      SND (frame64_run stepf st inps1) ++
      SND (frame64_run stepf (FST (frame64_run stepf st inps1)) inps2)
Proof
  gen_tac \\ Induct_on `inps1`
  >- simp [frame64_run_def]
  \\ rpt strip_tac \\ fs []
  \\ simp [frame64_run_def]
  \\ Cases_on `stepf st (frame64_decode h)` \\ simp []
  \\ Cases_on `frame64_run stepf q inps1` \\ simp []
  \\ Cases_on `frame64_run stepf q (inps1 ++ inps2)` \\ simp []
  \\ first_x_assum (qspecl_then [`inps2`, `q`] mp_tac) \\ simp []
QED

Theorem frame64_run_take_prefix[local]:
  ∀stepf r inps st.
    EVERY (λf. LENGTH f = 64) inps ⇒
    SND (frame64_run stepf st (TAKE r inps)) ≼ SND (frame64_run stepf st inps)
Proof
  rpt strip_tac
  \\ `inps = TAKE r inps ++ DROP r inps` by simp [listTheory.TAKE_DROP]
  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [th])))))
  \\ `EVERY (λf. LENGTH f = 64) (TAKE r inps)` by simp [rich_listTheory.EVERY_TAKE]
  \\ drule frame64_run_append \\ simp [IS_PREFIX_APPEND]
QED

Theorem chunks64_split_tail[local]:
  ∀inp. ∃tail_bs. inp = FLAT (chunks64 inp) ++ tail_bs ∧ LENGTH tail_bs < 64
Proof
  ho_match_mp_tac chunks64_ind \\ rpt strip_tac
  \\ Cases_on `LENGTH inp < 64`
  >- (qexists_tac `inp` \\ simp [Once chunks64_def])
  \\ fs []
  \\ qexists_tac `tail_bs`
  \\ simp [Once chunks64_def]
  \\ `TAKE 64 inp ++ FLAT (chunks64 (DROP 64 inp)) ++ tail_bs = TAKE 64 inp ++ DROP 64 inp` by simp []
  \\ pop_assum SUBST1_TAC
  \\ simp [listTheory.TAKE_DROP]
QED

Theorem chunks64_drop_eq[local]:
  ∀r inp inp_cur.
    r ≤ LENGTH (chunks64 inp) ∧
    inp = FLAT (TAKE r (chunks64 inp)) ++ inp_cur ⇒
    chunks64 inp = TAKE r (chunks64 inp) ++ chunks64 inp_cur ∧
    DROP r (chunks64 inp) = chunks64 inp_cur
Proof
  Induct_on `r`
  >- (rpt strip_tac \\ gvs [])
  \\ rpt gen_tac \\ strip_tac
  \\ `¬(LENGTH inp < 64)` by
       (strip_tac \\ drule chunks64_lt64 \\ strip_tac \\ fs [])
  \\ `chunks64 inp = TAKE 64 inp :: chunks64 (DROP 64 inp)` by
       simp [Once chunks64_def]
  \\ `TAKE (SUC r) (chunks64 inp) = TAKE 64 inp :: TAKE r (chunks64 (DROP 64 inp))` by
       (pop_assum (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) \\ simp [])
  \\ `DROP 64 inp = FLAT (TAKE r (chunks64 (DROP 64 inp))) ++ inp_cur` by (
       `TAKE 64 inp ++ DROP 64 inp =
        TAKE 64 inp ++ (FLAT (TAKE r (chunks64 (DROP 64 inp))) ++ inp_cur)` by (
         REWRITE_TAC [listTheory.TAKE_DROP]
         \\ qpat_x_assum `inp = FLAT (TAKE (SUC r) _) ++ _`
              (fn th => CONV_TAC (LHS_CONV (REWR_CONV th)))
         \\ qpat_x_assum `TAKE (SUC r) _ = _`
              (fn th => CONV_TAC (LHS_CONV (LAND_CONV (RAND_CONV (REWR_CONV th)))))
         \\ simp [])
       \\ fs [])
  \\ `r ≤ LENGTH (chunks64 (DROP 64 inp))` by
       (qpat_x_assum `SUC r ≤ _` mp_tac
        \\ qpat_x_assum `chunks64 inp = _` (fn th => ONCE_REWRITE_TAC [th])
        \\ simp [])
  \\ first_x_assum (qspecl_then [`DROP 64 inp`, `inp_cur`] mp_tac)
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ conj_tac
  >- (qpat_x_assum `chunks64 inp = _` (fn th => CONV_TAC (LHS_CONV (REWR_CONV th)))
      \\ qpat_x_assum `TAKE (SUC r) _ = _` (fn th => CONV_TAC (RHS_CONV (LAND_CONV (REWR_CONV th))))
      \\ simp [])
  \\ qpat_x_assum `chunks64 inp = _` (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th))))
  \\ simp []
QED

Theorem chunks64_take_step[local]:
  ∀r inp inp_cur frame inp_after.
    r ≤ LENGTH (chunks64 inp) ∧
    inp = FLAT (TAKE r (chunks64 inp)) ++ inp_cur ∧
    LENGTH frame = 64 ∧ inp_cur = frame ++ inp_after ⇒
    r + 1 ≤ LENGTH (chunks64 inp) ∧
    TAKE (r + 1) (chunks64 inp) = TAKE r (chunks64 inp) ++ [frame] ∧
    inp = FLAT (TAKE (r + 1) (chunks64 inp)) ++ inp_after
Proof
  rpt gen_tac \\ strip_tac
  \\ drule_all chunks64_drop_eq \\ strip_tac
  \\ `chunks64 inp_cur = frame :: chunks64 inp_after` by simp [chunks64_cons]
  \\ `chunks64 inp = TAKE r (chunks64 inp) ++ (frame :: chunks64 inp_after)` by
       (qpat_x_assum `chunks64 inp = _` (fn th => CONV_TAC (LHS_CONV (REWR_CONV th)))
        \\ simp [])
  \\ `LENGTH (TAKE r (chunks64 inp)) = r` by simp []
  \\ `r < LENGTH (chunks64 inp)` by
       (qpat_assum `chunks64 inp = TAKE r _ ++ _` (fn th => CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV th))))
        \\ simp [])
  \\ `TAKE (r + 1) (chunks64 inp) = TAKE r (chunks64 inp) ++ [frame]` by
       (qpat_assum `chunks64 inp = TAKE r _ ++ _` (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th))))
        \\ `r + 1 = LENGTH (TAKE r (chunks64 inp)) + 1` by simp []
        \\ pop_assum SUBST1_TAC
        \\ simp [rich_listTheory.TAKE_APPEND2])
  \\ rpt conj_tac
  >- decide_tac
  >- first_assum ACCEPT_TAC
  \\ qpat_x_assum `TAKE (r + 1) _ = _`
       (fn th => CONV_TAC (RHS_CONV (LAND_CONV (RAND_CONV (REWR_CONV th)))))
  \\ REWRITE_TAC [listTheory.FLAT_APPEND, listTheory.FLAT, listTheory.APPEND_NIL,
                  GSYM listTheory.APPEND_ASSOC]
  \\ qpat_x_assum `inp_cur = _` (fn th => REWRITE_TAC [GSYM th])
  \\ first_assum ACCEPT_TAC
QED

Theorem chunks64_take_all_of_lt64[local]:
  ∀r inp inp_cur.
    r ≤ LENGTH (chunks64 inp) ∧
    inp = FLAT (TAKE r (chunks64 inp)) ++ inp_cur ∧
    LENGTH inp_cur < 64 ⇒
    TAKE r (chunks64 inp) = chunks64 inp
Proof
  rpt strip_tac
  \\ drule_all chunks64_drop_eq \\ strip_tac
  \\ `chunks64 inp_cur = []` by simp [chunks64_lt64]
  \\ qpat_x_assum `chunks64 inp = _` (fn th => CONV_TAC (RHS_CONV (REWR_CONV th)))
  \\ simp []
QED

(* ---- 2. Generic Compilation Lift for 64-Byte Kernels ---- *)

Theorem shim64_len[local]:
  LENGTH forge_shim64_words = 80
Proof
  simp [forge_shim64_words_def]
QED

Theorem frame64_compile_exact[local]:
  ∀(stepf:'st -> frame64 -> 'st # frame64) (init:'st) prog code data info oracle ms0 io ffi_if inst_if.
    backend$compile arm8_config (set_oracle arm8_backend_config oracle) prog = SOME (code, data, info) ∧
    prog_syntax_ok prog ∧
    info.lab_conf.shmem_extra = [] ∧
    ffinames_to_string_list (the [] info.lab_conf.ffi_names) = [«send64»; «recv64»] ∧
    (∀io0:frame64_io.
       io0.outputs = [] ⇒
       sem_satisfies
         (semantics_dec_list (init_state (frame64_ffi io0)) init_env prog)
         (λb. ∃io_events.
                b = Terminate Success io_events ∧
                stop_after_err64 io_events ∧
                sent_frames64_of io_events =
                  limit_frames64 io0.write_limit (SND (frame64_run stepf init io0.inputs)))) ∧
    forge_slot_loaded forge_shim64_words code data ms0 ∧ io.outputs = [] ∧
    real_interfer_ok_slot (slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data))
      (slot_cbspace (LENGTH code)) [ExtCall «send64»; ExtCall «recv64»] (bits_of ms0) ffi_if inst_if ⇒
    let ms1 = FUNPOW arm8$Next 43 ms0 in
    let cb_end = slot_cb_end (LENGTH code) in
    let bm_end = slot_bm_buf_end (LENGTH data) in
    let rmc = real_mc (bits_of ms0)
                (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] ffi_if inst_if) in
      rmc.target = arm8_target_real (bits_of ms0) ∧
      ¬machine_sem rmc (frame64_ffi io) ms1 Fail ∧
      (∀j. FST (evaluate rmc (frame64_ffi io) j ms1) ≠ Error) ∧
      (∃ck t ms_end st_end.
         evaluate rmc (frame64_ffi io) ck ms1 = (Halt t, ms_end, st_end) ∧
         stop_after_err64 st_end.io_events ∧
         ((t = Success ∧
           sent_frames64_of st_end.io_events =
             limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs))) ∨
          (t = Resource_limit_hit ∧
           sent_frames64_of st_end.io_events ≼
             limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs))))) ∧
      (∀ck t ms_end st_end.
         evaluate rmc (frame64_ffi io) ck ms1 = (Halt t, ms_end, st_end) ⇒
         stop_after_err64 st_end.io_events ∧
         ((t = Success ∧
           sent_frames64_of st_end.io_events =
             limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs))) ∨
          (t = Resource_limit_hit ∧
           sent_frames64_of st_end.io_events ≼
             limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs)))))
Proof
  rpt strip_tac
  \\ simp [LET_THM]
  \\ qabbrev_tac `cb_begin = slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ qabbrev_tac `cbsp = slot_cbspace (LENGTH code)`
  \\ `info.lab_conf.ffi_names = SOME [ExtCall «send64»; ExtCall «recv64»]` by (
       drule (REWRITE_RULE [GSYM AND_IMP_INTRO] compile_imp_ffi_names)
       \\ disch_then (qspec_then `[«send64»; «recv64»]` mp_tac)
       \\ simp [backendTheory.set_oracle_def, arm8_configTheory.arm8_backend_config_def])
  \\ `slot_layout_ok cb_begin cb_end bm_end` by (
       fs [forge_slot_loaded_def, LET_THM]
       \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac slot_params_props
       \\ simp [LET_THM])
  \\ qspecl_then [`forge_shim64_words`, `«send64»`, `«recv64»`, `code`, `data`,
                  `info.lab_conf.ffi_names`, `ms0`, `ffi_if`, `inst_if`]
       mp_tac forge_slot_installed_exact
  \\ impl_tac >- simp [shim64_common_words_ok]
  \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ qabbrev_tac `mc0 = forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] ffi_if inst_if`
  \\ qabbrev_tac `emc = erase_mc (bits_of ms0) mc0`
  \\ qabbrev_tac `rmc = real_mc (bits_of ms0) mc0`
  \\ qpat_x_assum `∀io0. io0.outputs = [] ⇒ sem_satisfies _ _` (qspec_then `io` mp_tac)
  \\ impl_tac >- simp [] \\ strip_tac
  \\ `∀b. semantics_prog (init_state (frame64_ffi io)) init_env prog b ⇒
          ∃io_events. b = Terminate Success io_events ∧
                      stop_after_err64 io_events ∧
                      sent_frames64_of io_events =
                        limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs))` by
       fs [semanticsPropsTheory.sem_satisfies_def, ml_progTheory.semantics_dec_list_eq, IN_DEF]
  \\ `¬semantics_prog (init_state (frame64_ffi io)) init_env prog Fail` by
       (strip_tac \\ first_x_assum drule \\ simp [])
  \\ `heap_regs arm8_backend_config.stack_conf.reg_names = (1, 3)` by EVAL_TAC
  \\ `mc_conf_ok emc ∧ mc_init_ok arm8_config arm8_backend_config emc` by
       simp [Abbr `emc`, Abbr `mc0`, erase_mc_conf_ok_slot, erase_mc_init_ok_slot]
  \\ `machine_sem emc (frame64_ffi io) (erase ms1) ⊆
      extend_with_resource_limit (semantics_prog (init_state (frame64_ffi io)) init_env prog)` by (
       qpat_x_assum `backend$compile _ _ _ = _` (fn th =>
         irule (MATCH_MP backendProofTheory.compile_correct th
                |> SIMP_RULE (srw_ss()) [LET_THM, ml_progTheory.init_state_env_thm,
                                         backendProofTheory.set_oracle_simp,
                                         arm8_configProofTheory.arm8_backend_config_ok]))
       \\ simp [] \\ metis_tac [])
  \\ `¬machine_sem emc (frame64_ffi io) (erase ms1) Fail` by (
       strip_tac
       \\ `Fail ∈ extend_with_resource_limit (semantics_prog (init_state (frame64_ffi io)) init_env prog)` by
            fs [SUBSET_DEF, IN_DEF]
       \\ drule semanticsPropsTheory.extend_with_resource_limit_not_fail
       \\ simp [IN_DEF])
  \\ `machine_sem rmc (frame64_ffi io) ms1 = machine_sem emc (frame64_ffi io) (erase ms1)` by (
       fs [Abbr `rmc`, Abbr `emc`]
       \\ irule machine_sem_real_eq_exact
       \\ simp [Abbr `mc0`, MATCH_MP forge_mc_slot_lo55 (ASSUME ``slot_layout_ok cb_begin cb_end bm_end``)]
       \\ rpt conj_tac
       >- fs [real_interfer_ok_slot_def, LET_THM, forge_mc_slot_def]
       >- fs [real_interfer_ok_slot_def, LET_THM, forge_mc_slot_def]
       >- simp [forge_mc_slot_def]
       >- simp [forge_mc_slot_def]
       \\ fs [sp_ok_def, bits_of_def, forge_slot_loaded_def, LET_THM])
  \\ `¬machine_sem rmc (frame64_ffi io) ms1 Fail` by simp []
  \\ `∀b. machine_sem rmc (frame64_ffi io) ms1 b ⇒
          ∃t io_events.
            b = Terminate t io_events ∧
            stop_after_err64 io_events ∧
            ((t = Success ∧
              sent_frames64_of io_events =
                limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs))) ∨
             (t = Resource_limit_hit ∧
              sent_frames64_of io_events ≼
                limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs))))` by (
       rpt strip_tac
       \\ `b ∈ extend_with_resource_limit (semantics_prog (init_state (frame64_ffi io)) init_env prog)` by
            metis_tac [SUBSET_DEF, IN_DEF]
       \\ qpat_x_assum `b ∈ extend_with_resource_limit _` mp_tac
       \\ simp [semanticsPropsTheory.extend_with_resource_limit_def]
       \\ rpt strip_tac \\ fs [IN_DEF]
       \\ qpat_x_assum `∀b. semantics_prog _ _ _ b ⇒ _`
            (fn ih => qpat_x_assum `semantics_prog _ _ _ _` (strip_assume_tac o MATCH_MP ih))
       \\ rveq \\ fs []
       \\ metis_tac [stop_after_err64_prefix, sent_frames64_of_prefix])
  \\ rpt conj_tac
  >- simp [Abbr `rmc`, real_mc_def]
  >- simp []
  >- (qpat_x_assum `¬machine_sem rmc _ _ Fail` mp_tac \\ simp [targetSemTheory.machine_sem_def])
  >- (
    qspecl_then [`rmc`, `frame64_ffi io`, `ms1`] strip_assume_tac
      (Q.GENL [`mc`, `st`, `ms`] targetPropsTheory.machine_sem_total)
    \\ first_x_assum drule \\ strip_tac \\ rveq
    \\ qpat_x_assum `machine_sem rmc _ _ (Terminate _ _)` mp_tac
    \\ simp [targetSemTheory.machine_sem_def] \\ strip_tac
    \\ metis_tac [])
  \\ rpt gen_tac \\ strip_tac
  \\ `machine_sem rmc (frame64_ffi io) ms1 (Terminate t st_end.io_events)` by
       (simp [targetSemTheory.machine_sem_def] \\ metis_tac [])
  \\ first_x_assum drule \\ strip_tac \\ fs []
QED

(* ---- 3. Single-Step Real-Bits Evaluation & 64B FFI Oracle Helpers ---- *)

Theorem shift_mk_real_ffi64_if[local]:
  ∀cb_begin cb_end bm_end P.
    shift_seq 1 (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P) =
    mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + 1))
Proof
  rpt gen_tac \\ simp [FUN_EQ_THM, pairTheory.FORALL_PROD, miscTheory.shift_seq_def, mk_real_ffi_if_slot_def]
QED

Theorem mk_real_ffi64_if_pc[local]:
  ∀cb_begin cb_end bm_end P k idx new_bs s.
    (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P k (idx, new_bs, s)).PC = s.REG 30w
Proof
  rpt gen_tac \\ simp [mk_real_ffi_if_slot_def]
  \\ IF_CASES_TAC
  >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [ffi_return_ok_slot_def])
  \\ simp [forge_canonical_ffi_post_def]
QED

Theorem mk_real_ffi64_if_select[local]:
  ∀cb_begin cb_end bm_end P k idx new_bs s s_tgt.
    (∀s'. P k idx new_bs s s' ⇔ s' = s_tgt) ∧
    ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s_tgt ⇒
    mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P k (idx, new_bs, s) = s_tgt
Proof
  rpt strip_tac \\ simp [mk_real_ffi_if_slot_def]
  \\ SELECT_ELIM_TAC \\ simp []
QED

Theorem frame64_ffi_call_send64[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = frame64_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «send64») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = frame64_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «send64») bytes (ZIP (bytes2, new_bs))] ∧
      (LENGTH bytes2 < 65 ⇒
         new_bs = bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state ∧
         sent_frames64_of ffi'.io_events = sent_frames64_of ffi.io_events) ∧
      (65 ≤ LENGTH bytes2 ⇒
         let frame = TAKE 64 (DROP 1 bytes2) in
         sent_frames64_of ffi'.io_events = sent_frames64_of ffi.io_events ++ [frame] ∧
         (ffi.ffi_state.write_limit = NONE ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with outputs := ffi.ffi_state.outputs ++ [frame]) ∧
         (ffi.ffi_state.write_limit = SOME 0 ⇒
            new_bs = 1w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with outputs := ffi.ffi_state.outputs ++ [frame] ∧
            event_is_err64 (IO_event (ExtCall «send64») bytes (ZIP (bytes2, new_bs)))) ∧
         (∀d. ffi.ffi_state.write_limit = SOME (SUC d) ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with <| outputs := ffi.ffi_state.outputs ++ [frame];
                                                   write_limit := SOME d |>))
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [frame64_ffi_oracle_def, ffi_send64_def]
  \\ (Cases_on `LENGTH bytes2 < 65` \\ simp [])
  >- simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.LENGTH_ZIP]
  \\ (Cases_on `ffi.ffi_state.write_limit` \\ simp [])
  >- (
    `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.MAP_ZIP, listTheory.LENGTH_ZIP])
  \\ (Cases_on `x` \\ simp [])
  >- (
    `LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.MAP_ZIP, listTheory.LENGTH_ZIP,
             event_is_err64_def]
    \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
  \\ simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.MAP_ZIP, listTheory.LENGTH_ZIP]
QED

Theorem frame64_ffi_call_recv64[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = frame64_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «recv64») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = frame64_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs))] ∧
      sent_frames64_of ffi'.io_events = sent_frames64_of ffi.io_events ∧
      (LENGTH bytes2 < 65 ⇒
         new_bs = bytes2 ∧ ffi'.ffi_state = ffi.ffi_state) ∧
      (65 ≤ LENGTH bytes2 ∧ ffi.ffi_state.inputs = [] ⇒
         new_bs = 1w :: DROP 1 bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state ∧
         event_is_err64 (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs)))) ∧
      (∀f fs. 65 ≤ LENGTH bytes2 ∧ ffi.ffi_state.inputs = f :: fs ∧ LENGTH f = 64 ⇒
         new_bs = 0w :: f ++ DROP 65 bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state with inputs := fs)
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [frame64_ffi_oracle_def, ffi_recv64_def]
  \\ (Cases_on `LENGTH bytes2 < 65` \\ simp [])
  >- simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.LENGTH_ZIP]
  \\ (Cases_on `ffi.ffi_state.inputs` \\ simp [])
  >- (
    `LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.LENGTH_ZIP, event_is_err64_def]
    \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ (Cases_on `LENGTH h = 64` \\ simp [])
  >- (
    `LENGTH (0w :: h ++ DROP 65 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.LENGTH_ZIP])
  \\ `LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
  \\ simp [sent_frames64_of_append, sent_frames64_of_def, listTheory.LENGTH_ZIP]
QED

Theorem frame64_eval_step_cases[local]:
  ∀cb_begin cb_end bm_end B P ffi s.
    let rmc = real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                           (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      shim_loaded_slot forge_shim64_words cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = frame64_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ⇒
      (s.PC ∈ forge_prog_addresses_slot cb_end bm_end ∧ s.PC ≠ FORGE_FFISEND_VENEER ∧ s.PC ≠ FORGE_FFIRECV_VENEER ⇒
         ¬is_svc0_at s ∧
         NextStateARM8 s = SOME (arm8$Next s) ∧
         arm8_ok (erase (arm8$Next s)) ∧ sp_ok (arm8$Next s) ∧
         bits_of (arm8$Next s) = B ∧
         shim_loaded_slot forge_shim64_words cb_begin cb_end bm_end (arm8$Next s).MEM ∧
         (∀k. evaluate rmc ffi (SUC k) s = evaluate rmc ffi k (arm8$Next s))) ∧
      (s.PC = FORGE_EXIT_VENEER ⇒
         ∀k. evaluate rmc ffi (SUC k) s =
             (if s.REG 0w = 0w then Halt Success else Halt Resource_limit_hit, s, ffi)) ∧
      (s.PC = FORGE_FFISEND_VENEER ∨ s.PC = FORGE_FFIRECV_VENEER ⇒
         ∃bytes bytes2.
           read_bytearray (s.REG 0w) (w2n (s.REG 1w))
             (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes ∧
           read_bytearray (s.REG 2w) (w2n (s.REG 3w))
             (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
           aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w)) ∧
      ((s.PC ∈ forge_prog_addresses_slot cb_end bm_end ∧ s.PC ≠ FORGE_FFISEND_VENEER ∧ s.PC ≠ FORGE_FFIRECV_VENEER) ∨
       s.PC = FORGE_EXIT_VENEER ∨ s.PC = FORGE_INSTALL_VENEER ∨
       s.PC = FORGE_FFISEND_VENEER ∨ s.PC = FORGE_FFIRECV_VENEER)
Proof
  rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                           (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P)
                           forge_real_install_if)`
  \\ strip_tac
  \\ drule forge_veneer_facts_slot \\ strip_tac
  \\ drule forge_regions_disjoint_slot \\ strip_tac
  \\ rpt conj_tac
  >- (
    strip_tac
    \\ `s.PC ≠ FORGE_EXIT_VENEER ∧ s.PC ≠ FORGE_INSTALL_VENEER` by metis_tac []
    \\ `SND (SND B) ⇒ aligned 4 s.SP_EL0` by
         (qpat_x_assum `bits_of s = B` (SUBST1_TAC o SYM) \\ fs [sp_ok_def, bits_of_def])
    \\ `encoded_bytes_in_mem arm8_config s.PC s.MEM (forge_prog_addresses_slot cb_end bm_end) ∧
        arm8_ok (erase (arm8$Next s)) ∧ bits_of (arm8$Next s) = B ∧
        (SND (SND B) ⇒ aligned 4 (arm8$Next s).SP_EL0) ∧
        (∀x. x ∉ forge_prog_addresses_slot cb_end bm_end ⇒ (arm8$Next s).MEM x = s.MEM x)` by (
         qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
         \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def]
         \\ Cases_on `encoded_bytes_in_mem arm8_config s.PC s.MEM (forge_prog_addresses_slot cb_end bm_end)` \\ simp []
         \\ Cases_on `((¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧ arm8_ok (erase (arm8$Next s)) ∧
                       bits_of (arm8$Next s) = B ∧ (¬SND (SND B) ∨ aligned 4 (arm8$Next s).SP_EL0)) ∧
                      (∀x. x ∉ forge_prog_addresses_slot cb_end bm_end ⇒ (arm8$Next s).MEM x = s.MEM x)` \\ simp []
         \\ strip_tac \\ metis_tac [])
    \\ rpt conj_tac
    >- (irule encoded_bytes_in_mem_not_svc0 \\ qexists_tac `forge_prog_addresses_slot cb_end bm_end` \\ simp [])
    >- (simp [arm8_stepTheory.NextStateARM8_def] \\ fs [arm8_ok_erase])
    >- simp []
    >- (fs [sp_ok_def, arm8_ok_erase] \\ Cases_on `(arm8$Next s).SCTLR_EL1.SA0` \\ simp []
        \\ qpat_x_assum `SND (SND B) ⇒ aligned 4 (arm8$Next s).SP_EL0` irule
        \\ qpat_x_assum `bits_of (arm8$Next s) = B` (SUBST1_TAC o SYM) \\ simp [bits_of_def])
    >- simp []
    >- (mp_tac (Q.SPECL [`forge_shim64_words`, `cb_begin`, `cb_end`, `bm_end`, `(arm8$Next s).MEM`, `s.MEM`] shim_loaded_slot_cong)
        \\ impl_tac
        >- (conj_tac >- simp [shim64_len]
            \\ rpt strip_tac \\ first_x_assum irule
            \\ strip_tac \\ qpat_x_assum `∀a. a ∈ forge_prog_addresses_slot _ _ ⇒ a ∉ forge_shim_code_region` (mp_tac o Q.SPEC `a`) \\ simp [])
        \\ simp [])
    \\ gen_tac
    \\ `shift_seq 1 (K I) = (K I : num -> arm8_state -> arm8_state)` by
         simp [miscTheory.shift_seq_def, FUN_EQ_THM]
    \\ `(¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧ (¬SND (SND B) ∨ aligned 4 (arm8$Next s).SP_EL0)` by metis_tac []
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_slot_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def])
  >- (
    strip_tac \\ gen_tac
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_slot_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def])
  >- (
    disch_tac
    \\ `s.PC ∉ forge_prog_addresses_slot cb_end bm_end ∧ s.PC ≠ FORGE_EXIT_VENEER ∧ s.PC ≠ FORGE_INSTALL_VENEER` by metis_tac []
    \\ `find_index s.PC [FORGE_FFISEND_VENEER; FORGE_FFIRECV_VENEER] 0 =
        SOME (if s.PC = FORGE_FFISEND_VENEER then 0 else 1)` by
         (Cases_on `s.PC = FORGE_FFISEND_VENEER` \\ fs [miscTheory.find_index_def])
    \\ qabbrev_tac `idx = if s.PC = FORGE_FFISEND_VENEER then 0 else 1`
    \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `2` mp_tac)
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_slot_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def,
             targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def]
    \\ `EL idx [ExtCall «send64»; ExtCall «recv64»] =
        ExtCall (if idx = 0 then «send64» else «recv64»)` by (simp [Abbr `idx`] \\ rw [])
    \\ pop_assum SUBST1_TAC
    \\ Cases_on `read_bytearray (s.REG 0w) (w2n (s.REG 1w))
                   (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE)` \\ simp []
    \\ rename1 `read_bytearray (s.REG 0w) _ _ = SOME bytes`
    \\ Cases_on `read_bytearray (s.REG 2w) (w2n (s.REG 3w))
                   (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE)` \\ simp []
    \\ rename1 `read_bytearray (s.REG 2w) _ _ = SOME bytes2`
    \\ `∃ffi1 new_bs. call_FFI ffi (ExtCall (if idx = 0 then «send64» else «recv64»)) bytes bytes2 =
                      FFI_return ffi1 new_bs` by
         ((Cases_on `idx = 0` \\ simp [])
          >- (drule frame64_ffi_call_send64 \\ metis_tac [])
          \\ drule frame64_ffi_call_recv64 \\ metis_tac [])
    \\ pop_assum strip_assume_tac \\ simp []
    \\ qabbrev_tac `ms1 = mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P 0 (idx, new_bs, s)`
    \\ `ms1.PC = s.REG 30w` by simp [Abbr `ms1`, mk_real_ffi64_if_pc]
    \\ simp [Once targetSemTheory.evaluate_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def]
    \\ (Cases_on `s.REG 30w = FORGE_EXIT_VENEER` \\ simp [])
    >- (simp [FORGE_EXIT_VENEER_def, untagged_def] \\ EVAL_TAC)
    \\ (Cases_on `s.REG 30w = FORGE_INSTALL_VENEER` \\ simp [])
    >- (simp [FORGE_INSTALL_VENEER_def, untagged_def] \\ EVAL_TAC)
    \\ (Cases_on `s.REG 30w ∈ forge_prog_addresses_slot cb_end bm_end` \\ simp [])
    >- (
      `s.REG 30w ≠ FORGE_FFISEND_VENEER ∧ s.REG 30w ≠ FORGE_FFIRECV_VENEER` by metis_tac []
      \\ simp []
      \\ Cases_on `encoded_bytes_in_mem arm8_config (s.REG 30w) ms1.MEM (forge_prog_addresses_slot cb_end bm_end)` \\ simp []
      \\ Cases_on `arm8_ok (erase ms1)` \\ simp []
      \\ disch_tac
      \\ qpat_x_assum `arm8_ok (erase ms1)` mp_tac \\ simp [arm8_ok_erase])
    \\ (Cases_on `s.REG 30w = FORGE_FFISEND_VENEER` \\ simp [miscTheory.find_index_def])
    >- (simp [FORGE_FFISEND_VENEER_def, untagged_def] \\ EVAL_TAC)
    \\ (Cases_on `s.REG 30w = FORGE_FFIRECV_VENEER` \\ simp [miscTheory.find_index_def])
    \\ simp [FORGE_FFIRECV_VENEER_def, untagged_def] \\ EVAL_TAC)
  \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
  \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_slot_def,
           arm8_target_real_def, arm8_targetTheory.arm8_target_def]
  \\ Cases_on `s.PC ∈ forge_prog_addresses_slot cb_end bm_end ∧ s.PC ≠ FORGE_FFISEND_VENEER ∧ s.PC ≠ FORGE_FFIRECV_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_EXIT_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_INSTALL_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_FFISEND_VENEER` \\ simp [miscTheory.find_index_def]
  \\ Cases_on `s.PC = FORGE_FFIRECV_VENEER` \\ simp [miscTheory.find_index_def]
QED

(* ---- 4. Forward Liveness under Error-Free Linux Syscalls ---- *)

Definition noerr_ffi64_P_def:
  noerr_ffi64_P (cb_end:word64) (bm_end:word64) (tail_bs:word8 list)
                (k:num) (idx:num) (new_bs:word8 list)
                (s:arm8_state) (s':arm8_state) ⇔
    (idx = 0 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 65 ⇒
          ∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
       (65 ≤ w2n (s.REG 3w) ⇒
          ∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                      (inp, out, s) (inp, out ++ TAKE 64 (DROP 1 bytes2), s'))) ∨
    (idx = 1 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 65 ⇒
          ∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
       (65 ≤ w2n (s.REG 3w) ∧ HD new_bs = 0w ⇒
          ∀rest out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                       (TAKE 64 (DROP 1 new_bs) ++ rest, out, s) (rest, out, s')) ∧
       (65 ≤ w2n (s.REG 3w) ∧ HD new_bs ≠ 0w ⇒
          ∀out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (tail_bs, out, s) ([], out, s')))
End

Theorem noerr_ffi64_P_shift[local]:
  ∀cb_end bm_end tail_bs.
    (λk. noerr_ffi64_P cb_end bm_end tail_bs (k + 1)) = noerr_ffi64_P cb_end bm_end tail_bs
Proof
  rpt gen_tac \\ simp [FUN_EQ_THM, noerr_ffi64_P_def]
QED

Theorem frame64_liveness_eval_rtc[local]:
  ∀ck cb_begin cb_end bm_end B tail_bs ffi s inp_cur out_cur t ms_end st_end.
    let rmc = real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                           (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end
                              (noerr_ffi64_P cb_end bm_end tail_bs))
                           forge_real_install_if) in
      slot_layout_ok cb_begin cb_end bm_end ∧
      LENGTH tail_bs < 64 ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      shim_loaded_slot forge_shim64_words cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = frame64_ffi_oracle ∧
      ffi.ffi_state.write_limit = NONE ∧
      EVERY (λf. LENGTH f = 64) ffi.ffi_state.inputs ∧
      inp_cur = FLAT ffi.ffi_state.inputs ++ tail_bs ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ∧
      evaluate rmc ffi ck s = (Halt t, ms_end, st_end) ∧
      stop_after_err64 st_end.io_events ∧
      EVERY ($~ o event_is_err64) ffi.io_events ⇒
      ∃inp_f out_f ms_f ec.
        RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
          (inp_cur, out_cur, s) (inp_f, out_f, ms_f) ∧
        svc_exit_group_rel ec ms_f
Proof
  Induct_on `ck`
  >- (rpt gen_tac \\ simp [LET_THM] \\ strip_tac
      \\ qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
  \\ rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                           (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end
                              (noerr_ffi64_P cb_end bm_end tail_bs))
                           forge_real_install_if)`
  \\ strip_tac
  \\ drule forge_veneer_facts_slot \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `noerr_ffi64_P cb_end bm_end tail_bs`, `ffi`, `s`]
       mp_tac frame64_eval_step_cases
  \\ simp [LET_THM] \\ strip_tac
  >- (
    (* Prog address stepf *)
    first_x_assum drule \\ strip_tac
    \\ `evaluate rmc ffi ck (arm8$Next s) = (Halt t, ms_end, st_end)` by fs []
    \\ `∀j. FST (evaluate rmc ffi j (arm8$Next s)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
    \\ qpat_x_assum `∀cb_begin cb_end bm_end B tail_bs ffi s. _`
         (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `tail_bs`, `ffi`, `arm8$Next s`,
                       `inp_cur`, `out_cur`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp []
    \\ ONCE_REWRITE_TAC [relationTheory.RTC_CASES1] \\ disj2_tac
    \\ qexists_tac `(inp_cur, out_cur, arm8$Next s)`
    \\ simp [whole_step_def])
  >- (
    (* Exit veneer *)
    qspecl_then [`forge_shim64_words`, `cb_begin`, `cb_end`, `bm_end`, `s`]
      mp_tac cake_exit_to_svc_exit_group_slot
    \\ simp [shim64_common_words_ok, LET_THM] \\ strip_tac
    \\ qexists_tac `inp_cur` \\ qexists_tac `out_cur`
    \\ qexists_tac `FUNPOW arm8$Next k s`
    \\ qexists_tac `if s.REG 0w = 0w then 0w else 1w`
    \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `k` \\ simp [])
  >- (
    (* Install veneer *)
    qspecl_then [`forge_shim64_words`, `cb_begin`, `cb_end`, `bm_end`, `s`]
      mp_tac cake_install_to_svc_exit_group_slot
    \\ simp [shim64_common_words_ok, LET_THM] \\ strip_tac
    \\ qexists_tac `inp_cur` \\ qexists_tac `out_cur`
    \\ qexists_tac `FUNPOW arm8$Next 3 s` \\ qexists_tac `2w`
    \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
  >- (
    (* send64 veneer *)
    `∃bytes bytes2.
       read_bytearray (s.REG 0w) (w2n (s.REG 1w))
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes ∧
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w)` by simp []
    \\ drule_all (SIMP_RULE (srw_ss()) [LET_THM] frame64_ffi_call_send64)
    \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
    \\ imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `s1 = mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (noerr_ffi64_P cb_end bm_end tail_bs) 0 (0, new_bs, s)`
    \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
        (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
         `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
           gen_tac
           \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi64_if, noerr_ffi64_P_shift, Abbr `s1`])
         \\ conj_tac >- fs []
         \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
         \\ simp [])
    \\ `∃s_ex. noerr_ffi64_P cb_end bm_end tail_bs 0 0 new_bs s s_ex ∧
               ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s_ex` by (
         qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac ffisend64_noerr_exists_slot
         \\ impl_tac >- simp [] \\ strip_tac
         \\ Cases_on `w2n (s.REG 3w) < 65`
         >- (fs [] \\ qexists_tac `s'` \\ simp [noerr_ffi64_P_def] \\ qexists_tac `bytes2` \\ simp [])
         \\ `65 ≤ w2n (s.REG 3w)` by decide_tac
         \\ fs [] \\ qexists_tac `s'` \\ simp [noerr_ffi64_P_def] \\ qexists_tac `bytes2` \\ simp [])
    \\ `noerr_ffi64_P cb_end bm_end tail_bs 0 0 new_bs s s1 ∧
        ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s1` by (
         simp [Abbr `s1`, mk_real_ffi_if_slot_def]
         \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
         \\ metis_tac [])
    \\ `ffi'.ffi_state.inputs = ffi.ffi_state.inputs ∧ ffi'.ffi_state.write_limit = NONE ∧
        EVERY ($~ o event_is_err64) ffi'.io_events ∧
        (∃out_next.
           RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp_cur, out_cur, s) (inp_cur, out_next, s1))` by (
         Cases_on `w2n (s.REG 3w) < 65`
         >- (fs [noerr_ffi64_P_def, event_is_err64_def, listTheory.LENGTH_ZIP] \\ metis_tac [])
         \\ `65 ≤ LENGTH bytes2` by decide_tac
         \\ fs [noerr_ffi64_P_def, event_is_err64_def, listTheory.LENGTH_ZIP]
         \\ `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
         \\ conj_tac >- (Cases_on `bytes2` \\ fs [listTheory.ZIP])
         \\ metis_tac [])
    \\ qpat_x_assum `∀cb_begin cb_end bm_end B tail_bs ffi s. _`
         (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `tail_bs`, `ffi'`, `s1`,
                       `inp_cur`, `out_next`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac >- fs [ffi_return_ok_slot_def]
    \\ strip_tac
    \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  \\ (* recv64 veneer *)
     `∃bytes bytes2.
        read_bytearray (s.REG 0w) (w2n (s.REG 1w))
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes ∧
        read_bytearray (s.REG 2w) (w2n (s.REG 3w))
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w)` by simp []
  \\ drule_all frame64_ffi_call_recv64
  \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `s1 = mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (noerr_ffi64_P cb_end bm_end tail_bs) 0 (1, new_bs, s)`
  \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
      (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
       `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
         gen_tac
         \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi64_if, noerr_ffi64_P_shift, Abbr `s1`])
       \\ conj_tac >- fs []
       \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
       \\ simp [])
  \\ Cases_on `w2n (s.REG 3w) < 65`
  >- (
    `∃s_ex. noerr_ffi64_P cb_end bm_end tail_bs 0 1 new_bs s s_ex ∧
            ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s_ex` by (
       qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac ffirecv64_noerr_exists_slot
       \\ impl_tac >- simp [] \\ strip_tac
       \\ gvs [] \\ qexists_tac `s'` \\ simp [noerr_ffi64_P_def] \\ qexists_tac `bytes2` \\ simp [])
    \\ `noerr_ffi64_P cb_end bm_end tail_bs 0 1 new_bs s s1 ∧
        ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s1` by (
         simp [Abbr `s1`, mk_real_ffi_if_slot_def]
         \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
         \\ metis_tac [])
    \\ `RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp_cur, out_cur, s) (inp_cur, out_cur, s1)` by
         (qpat_x_assum `noerr_ffi64_P _ _ _ _ _ _ _ _` mp_tac \\ simp [noerr_ffi64_P_def])
    \\ `EVERY ($~ o event_is_err64) ffi'.io_events` by gvs [event_is_err64_def, listTheory.LENGTH_ZIP]
    \\ qpat_x_assum `∀cb_begin cb_end bm_end B tail_bs ffi s. _`
         (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `tail_bs`, `ffi'`, `s1`,
                       `inp_cur`, `out_cur`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac >- gvs [ffi_return_ok_slot_def]
    \\ strip_tac
    \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  \\ `65 ≤ LENGTH bytes2` by decide_tac
  \\ Cases_on `ffi.ffi_state.inputs`
  >- (
    `new_bs = 1w :: DROP 1 bytes2 ∧ ffi'.ffi_state = ffi.ffi_state ∧
     event_is_err64 (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs)))` by gvs []
    \\ `∃s_ex. noerr_ffi64_P cb_end bm_end tail_bs 0 1 new_bs s s_ex ∧
               ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s_ex` by (
         qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac ffirecv64_noerr_exists_slot
         \\ impl_tac >- simp [] \\ strip_tac
         \\ qpat_x_assum `∀tail_bs. 65 ≤ _ ∧ LENGTH tail_bs < 64 ⇒ _` (qspec_then `tail_bs` mp_tac)
         \\ simp [] \\ strip_tac
         \\ qexists_tac `s'` \\ simp [noerr_ffi64_P_def] \\ qexists_tac `bytes2` \\ simp [])
    \\ `noerr_ffi64_P cb_end bm_end tail_bs 0 1 new_bs s s1 ∧
        ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s1` by (
         simp [Abbr `s1`, mk_real_ffi_if_slot_def]
         \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
         \\ metis_tac [])
    \\ `RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (tail_bs, out_cur, s) ([], out_cur, s1)` by
         (qpat_x_assum `noerr_ffi64_P _ _ _ _ _ _ _ _` mp_tac \\ simp [noerr_ffi64_P_def])
    \\ `∀ck' s' ffi_s.
          arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = B ∧
          shim_loaded_slot forge_shim64_words cb_begin cb_end bm_end s'.MEM ∧
          ffi_s.oracle = frame64_ffi_oracle ∧
          (∀j. FST (evaluate rmc ffi_s j s') ≠ Error) ∧
          evaluate rmc ffi_s ck' s' = (Halt t, ms_end, st_end) ∧
          (∃e. MEM e ffi_s.io_events ∧ event_is_err64 e) ⇒
          ∃inp_f out_f ms_f ec.
            RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) ([], out_cur, s') (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel ec ms_f` suffices_by (
          strip_tac \\ first_x_assum (qspecl_then [`ck`, `s1`, `ffi'`] mp_tac)
          \\ impl_tac >- (fs [ffi_return_ok_slot_def] \\ metis_tac [])
          \\ strip_tac
          \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
          \\ simp [] \\ fs [] \\ metis_tac [relationTheory.RTC_RTC])
    \\ Induct_on `ck'`
    >- (rpt strip_tac \\ qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rpt strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `noerr_ffi64_P cb_end bm_end tail_bs`, `ffi_s`, `s'`]
         mp_tac frame64_eval_step_cases
    \\ simp [LET_THM] \\ strip_tac
    >- (
      qpat_x_assum `s'.PC ∈ forge_prog_addresses_slot cb_end bm_end ∧ _ ⇒ _` (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac)
      \\ `evaluate rmc ffi_s ck' (arm8$Next s') = (Halt t, ms_end, st_end)` by fs []
      \\ `∀j. FST (evaluate rmc ffi_s j (arm8$Next s')) ≠ Error` by
           (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi_s j s') ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
      \\ qpat_x_assum `∀s' ffi_s. _` (qspecl_then [`arm8$Next s'`, `ffi_s`] mp_tac)
      \\ impl_tac >- (simp [] \\ metis_tac [])
      \\ strip_tac
      \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp []
      \\ ONCE_REWRITE_TAC [relationTheory.RTC_CASES1] \\ disj2_tac
      \\ qexists_tac `([], out_cur, arm8$Next s')`
      \\ simp [whole_step_def])
    >- (
      qspecl_then [`forge_shim64_words`, `cb_begin`, `cb_end`, `bm_end`, `s'`]
        mp_tac cake_exit_to_svc_exit_group_slot
      \\ simp [shim64_common_words_ok, LET_THM] \\ strip_tac
      \\ qexists_tac `[]` \\ qexists_tac `out_cur` \\ qexists_tac `FUNPOW arm8$Next k s'`
      \\ qexists_tac `if s'.REG 0w = 0w then 0w else 1w`
      \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `k` \\ simp [])
    >- (
      qspecl_then [`forge_shim64_words`, `cb_begin`, `cb_end`, `bm_end`, `s'`]
        mp_tac cake_install_to_svc_exit_group_slot
      \\ simp [shim64_common_words_ok, LET_THM] \\ strip_tac
      \\ qexists_tac `[]` \\ qexists_tac `out_cur` \\ qexists_tac `FUNPOW arm8$Next 3 s'`
      \\ qexists_tac `2w`
      \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
    >- (
      `∃bytes' bytes2'.
         read_bytearray (s'.REG 0w) (w2n (s'.REG 1w))
           (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s'.MEM a) else NONE) = SOME bytes' ∧
         read_bytearray (s'.REG 2w) (w2n (s'.REG 3w))
           (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s'.MEM a) else NONE) = SOME bytes2'` by metis_tac []
      \\ qspecl_then [`ffi_s`, `bytes'`, `bytes2'`] mp_tac
           (SIMP_RULE (srw_ss()) [LET_THM] frame64_ffi_call_send64)
      \\ simp [] \\ strip_tac
      \\ rename1 `call_FFI ffi_s _ _ _ = FFI_return ffi_next new_bs_next`
      \\ `evaluate rmc ffi_s (SUC ck') s' =
          evaluate rmc ffi_next ck' (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (noerr_ffi64_P cb_end bm_end tail_bs) 0 (0, new_bs_next, s'))` by (
           CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
           \\ simp [Abbr `rmc`, real_mc_def, forge_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi64_if, noerr_ffi64_P_shift])
      \\ `ffi_next.io_events ≼ st_end.io_events` by (
           qspecl_then [`rmc`, `ffi_next`, `ck'`, `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (noerr_ffi64_P cb_end bm_end tail_bs) 0 (0, new_bs_next, s')`]
             mp_tac targetPropsTheory.evaluate_io_events_mono
           \\ gvs [])
      \\ `ffi_s.io_events ≼ st_end.io_events` by
           (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi_next.io_events` \\ simp [IS_PREFIX_APPEND])
      \\ `st_end.io_events = ffi_s.io_events` by (irule stop_after_err64_prefix_eq \\ metis_tac [])
      \\ qpat_x_assum `ffi_next.io_events ≼ st_end.io_events` mp_tac
      \\ simp [IS_PREFIX_APPEND] \\ strip_tac
      \\ `LENGTH st_end.io_events = LENGTH (ffi_next.io_events ++ l)` by simp []
      \\ fs [])
    \\ `∃bytes' bytes2'.
          read_bytearray (s'.REG 0w) (w2n (s'.REG 1w))
            (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s'.MEM a) else NONE) = SOME bytes' ∧
          read_bytearray (s'.REG 2w) (w2n (s'.REG 3w))
            (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s'.MEM a) else NONE) = SOME bytes2'` by metis_tac []
    \\ qspecl_then [`ffi_s`, `bytes'`, `bytes2'`] mp_tac frame64_ffi_call_recv64
    \\ simp [] \\ strip_tac
    \\ rename1 `call_FFI ffi_s _ _ _ = FFI_return ffi_next new_bs_next`
    \\ `evaluate rmc ffi_s (SUC ck') s' =
        evaluate rmc ffi_next ck' (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (noerr_ffi64_P cb_end bm_end tail_bs) 0 (1, new_bs_next, s'))` by (
         CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc`, real_mc_def, forge_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi64_if, noerr_ffi64_P_shift])
    \\ `ffi_next.io_events ≼ st_end.io_events` by (
         qspecl_then [`rmc`, `ffi_next`, `ck'`, `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (noerr_ffi64_P cb_end bm_end tail_bs) 0 (1, new_bs_next, s')`]
           mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ gvs [])
    \\ `ffi_s.io_events ≼ st_end.io_events` by
         (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi_next.io_events` \\ simp [IS_PREFIX_APPEND])
    \\ `st_end.io_events = ffi_s.io_events` by (irule stop_after_err64_prefix_eq \\ metis_tac [])
    \\ qpat_x_assum `ffi_next.io_events ≼ st_end.io_events` mp_tac
    \\ simp [IS_PREFIX_APPEND] \\ strip_tac
    \\ `LENGTH st_end.io_events = LENGTH (ffi_next.io_events ++ l)` by simp []
    \\ fs [])
  \\ (* Non-empty inputs h :: rest_inps: read full 64B frame h *)
     rename1 `ffi.ffi_state.inputs = h :: rest_inps`
  \\ `LENGTH h = 64 ∧ EVERY (λf. LENGTH f = 64) rest_inps` by gvs []
  \\ `new_bs = 0w :: h ++ DROP 65 bytes2 ∧ ffi'.ffi_state = ffi.ffi_state with inputs := rest_inps` by (
       qpat_x_assum `∀f fs. _` (qspecl_then [`h`, `rest_inps`] mp_tac) \\ simp [])
  \\ `TAKE 64 h = h` by metis_tac [listTheory.TAKE_LENGTH_ID]
  \\ `TAKE 64 (DROP 1 new_bs) = h` by simp [listTheory.TAKE_APPEND1]
  \\ `∃s_ex. noerr_ffi64_P cb_end bm_end tail_bs 0 1 new_bs s s_ex ∧
             ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s_ex` by (
       qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac ffirecv64_noerr_exists_slot
       \\ impl_tac >- simp [] \\ strip_tac
       \\ qpat_x_assum `∀f. 65 ≤ _ ∧ LENGTH f = 64 ⇒ _` (qspec_then `h` mp_tac) \\ simp [] \\ strip_tac
       \\ qexists_tac `s'` \\ simp [noerr_ffi64_P_def, listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt])
  \\ `noerr_ffi64_P cb_end bm_end tail_bs 0 1 new_bs s s1 ∧
      ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end new_bs s s1` by (
       simp [Abbr `s1`, mk_real_ffi_if_slot_def]
       \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
       \\ fs [] \\ metis_tac [])
  \\ `RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
        (h ++ (FLAT rest_inps ++ tail_bs), out_cur, s) (FLAT rest_inps ++ tail_bs, out_cur, s1)` by (
       qpat_x_assum `noerr_ffi64_P _ _ _ _ _ _ _ _` mp_tac
       \\ simp [noerr_ffi64_P_def, listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt])
  \\ `EVERY ($~ o event_is_err64) ffi'.io_events` by (
       fs [event_is_err64_def, listTheory.LENGTH_ZIP]
       \\ `LENGTH (0w :: h ++ DROP 65 bytes2) = LENGTH bytes2` by simp []
       \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ qpat_x_assum `∀cb_begin cb_end bm_end B tail_bs ffi s. _`
       (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `tail_bs`, `ffi'`, `s1`,
                     `FLAT rest_inps ++ tail_bs`, `out_cur`, `t`, `ms_end`, `st_end`] mp_tac)
  \\ simp [LET_THM]
  \\ impl_tac >- gvs [ffi_return_ok_slot_def]
  \\ strip_tac
  \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
  \\ simp [] \\ fs [] \\ metis_tac [relationTheory.RTC_RTC]
QED

(* ---- 5. Universal Safety & Exactness over All OS Syscall Behaviors ---- *)

Definition mk_prefix64_P_def:
  mk_prefix64_P (posts:arm8_state list) (k:num) (idx:num) (bs:word8 list)
                (s:arm8_state) (s':arm8_state) ⇔
    k < LENGTH posts ∧ s' = EL k posts
End

Theorem frame64_post_err_nrc_safety[local]:
  ∀n cb_begin cb_end bm_end allow_err B P ffi_cur s_cur inp_cur out_cur inp_f out_f ms_f ec ck t ms_end st_end.
    let rmc = real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                           (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s_cur) ∧ sp_ok s_cur ∧ bits_of s_cur = B ∧
      shim_loaded_slot forge_shim64_words cb_begin cb_end bm_end s_cur.MEM ∧
      ffi_cur.oracle = frame64_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi_cur j s_cur) ≠ Error) ∧
      evaluate rmc ffi_cur ck s_cur = (Halt t, ms_end, st_end) ∧
      stop_after_err64 st_end.io_events ∧
      (∃e. MEM e ffi_cur.io_events ∧ event_is_err64 e) ∧
      NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel)
                      (if allow_err then svc_write_rel else svc_write_noerr_rel))
          n (inp_cur, out_cur, s_cur) (inp_f, out_f, ms_f) ∧
      svc_exit_group_rel ec ms_f ⇒
      out_f = out_cur ∧
      (ec = 0w ∨ ec = 1w ∨ ec = 2w) ∧
      (ec = 0w ⇒ t = Success ∧ st_end.io_events = ffi_cur.io_events)
Proof
  completeInduct_on `n` \\ rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                           (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P)
                           forge_real_install_if)`
  \\ strip_tac
  \\ drule forge_veneer_facts_slot \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi_cur`, `s_cur`]
       mp_tac frame64_eval_step_cases
  \\ simp [LET_THM] \\ strip_tac
  >- (
    qpat_x_assum `s_cur.PC ∈ forge_prog_addresses_slot cb_end bm_end ∧ _ ⇒ _` (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac)
    \\ Cases_on `n`
    >- (gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_def, is_svc0_at_def]
    \\ strip_tac
    \\ Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ `evaluate rmc ffi_cur ck' (arm8$Next s_cur) = (Halt t, ms_end, st_end)` by fs []
    \\ `∀j. FST (evaluate rmc ffi_cur j (arm8$Next s_cur)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi_cur j s_cur) ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
    \\ qpat_x_assum `∀m. m < SUC _ ⇒ _` (qspec_then `n'` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `allow_err`, `B`, `P`, `ffi_cur`, `arm8$Next s_cur`,
                                `inp_cur`, `out_cur`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `ck'`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ impl_tac >- (simp [] \\ metis_tac []) \\ simp [])
  >- (
    mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] cake_exit_universal_slot) shim64_common_words_ok)
    \\ disch_then drule_all \\ strip_tac
    \\ Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ qpat_x_assum `s_cur.PC = FORGE_EXIT_VENEER ⇒ _` mp_tac
    \\ impl_tac >- simp []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ Cases_on `s_cur.REG 0w = 0w` \\ fs [])
  >- (
    mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] cake_install_universal_slot) shim64_common_words_ok)
    \\ disch_then drule_all \\ strip_tac \\ simp [])
  >- (
    Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ `∃bytes bytes2.
          read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
            (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
          read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
            (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes2` by metis_tac []
    \\ drule_all (SIMP_RULE (srw_ss()) [LET_THM] frame64_ffi_call_send64)
    \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
    \\ `evaluate rmc ffi_cur (SUC ck') s_cur =
        evaluate (real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                   (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + 1))) forge_real_install_if))
          ffi' ck' (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P 0 (0, new_bs, s_cur))` by (
         CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc`, real_mc_def, forge_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi64_if])
    \\ `ffi'.io_events ≼ st_end.io_events` by (
         qspecl_then [`real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                        (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + 1))) forge_real_install_if)`,
                      `ffi'`, `ck'`, `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P 0 (0, new_bs, s_cur)`]
           mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ gvs [])
    \\ `ffi_cur.io_events ≼ st_end.io_events` by
         (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi'.io_events` \\ simp [IS_PREFIX_APPEND])
    \\ `st_end.io_events = ffi_cur.io_events` by (irule stop_after_err64_prefix_eq \\ metis_tac [])
    \\ qpat_x_assum `ffi'.io_events ≼ st_end.io_events` mp_tac
    \\ simp [IS_PREFIX_APPEND] \\ strip_tac
    \\ `LENGTH st_end.io_events = LENGTH (ffi'.io_events ++ l)` by simp []
    \\ fs [])
  \\ Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
  \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
  \\ `∃bytes bytes2.
        read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
        read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes2` by metis_tac []
  \\ drule_all frame64_ffi_call_recv64
  \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
  \\ `evaluate rmc ffi_cur (SUC ck') s_cur =
      evaluate (real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                 (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + 1))) forge_real_install_if))
        ffi' ck' (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P 0 (1, new_bs, s_cur))` by (
       CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
       \\ simp [Abbr `rmc`, real_mc_def, forge_mc_slot_def,
                arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                shift_mk_real_ffi64_if])
  \\ `ffi'.io_events ≼ st_end.io_events` by (
       qspecl_then [`real_mc B (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                      (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + 1))) forge_real_install_if)`,
                    `ffi'`, `ck'`, `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P 0 (1, new_bs, s_cur)`]
         mp_tac targetPropsTheory.evaluate_io_events_mono
       \\ gvs [])
  \\ `ffi_cur.io_events ≼ st_end.io_events` by
       (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi'.io_events` \\ simp [IS_PREFIX_APPEND])
  \\ `st_end.io_events = ffi_cur.io_events` by (irule stop_after_err64_prefix_eq \\ metis_tac [])
  \\ qpat_x_assum `ffi'.io_events ≼ st_end.io_events` mp_tac
  \\ simp [IS_PREFIX_APPEND] \\ strip_tac
  \\ `LENGTH st_end.io_events = LENGTH (ffi'.io_events ++ l)` by simp []
  \\ fs []
QED

Theorem frame64_pre_err_nrc_safety[local]:
  ∀n (stepf:'st -> frame64 -> 'st # frame64) (init:'st) prog code data info oracle
     allow_err ms0 inp r w inp_cur out_cur s_cur inp_f out_f ms_f ec posts sent_so_far step_cnt.
    let cb_begin = slot_cb_begin (LENGTH code) in
    let cb_end = slot_cb_end (LENGTH code) in
    let bm_end = slot_bm_buf_end (LENGTH data) in
    backend$compile arm8_config (set_oracle arm8_backend_config oracle) prog = SOME (code, data, info) ∧
    prog_syntax_ok prog ∧
    info.lab_conf.shmem_extra = [] ∧
    ffinames_to_string_list (the [] info.lab_conf.ffi_names) = [«send64»; «recv64»] ∧
    (∀io0:frame64_io.
       io0.outputs = [] ⇒
       sem_satisfies
         (semantics_dec_list (init_state (frame64_ffi io0)) init_env prog)
         (λb. ∃io_events.
                b = Terminate Success io_events ∧
                stop_after_err64 io_events ∧
                sent_frames64_of io_events =
                  limit_frames64 io0.write_limit (SND (frame64_run stepf init io0.inputs)))) ∧
    forge_slot_loaded forge_shim64_words code data ms0 ∧
    inp = FLAT (TAKE r (chunks64 inp)) ++ inp_cur ∧
    r ≤ LENGTH (chunks64 inp) ∧
    LENGTH sent_so_far = w ∧
    FLAT sent_so_far = out_cur ∧
    arm8_ok (erase s_cur) ∧ sp_ok s_cur ∧ bits_of s_cur = bits_of ms0 ∧
    shim_loaded_slot forge_shim64_words cb_begin cb_end bm_end s_cur.MEM ∧
    (∀extra_in wlim_rem P.
       (∀j. j < LENGTH posts ⇒ ∀idx bs s s'. P j idx bs s s' ⇔ s' = EL j posts) ⇒
       let io = <| inputs := TAKE r (chunks64 inp) ++ extra_in;
                   outputs := [];
                   write_limit := OPTION_MAP (λd. w + d) wlim_rem |> in
       let rmc0 = real_mc (bits_of ms0)
                    (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                       (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P)
                       forge_real_install_if) in
       let rmc_cur = real_mc (bits_of ms0)
                       (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                          (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                          forge_real_install_if) in
       ∃ffi_cur.
         ffi_cur.oracle = frame64_ffi_oracle ∧
         ffi_cur.ffi_state = <| inputs := extra_in; outputs := sent_so_far; write_limit := wlim_rem |> ∧
         sent_frames64_of ffi_cur.io_events = sent_so_far ∧
         (∀k. evaluate rmc0 (frame64_ffi io) (step_cnt + k) (FUNPOW arm8$Next 43 ms0) =
              evaluate rmc_cur ffi_cur k s_cur)) ∧
    NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel)
                    (if allow_err then svc_write_rel else svc_write_noerr_rel))
        n (inp_cur, out_cur, s_cur) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (ec = 0w ∨ ec = 1w ∨ ec = 2w) ∧
    out_f ≼ FLAT (SND (frame64_run stepf init (chunks64 inp))) ∧
    (¬allow_err ∧ ec = 0w ⇒ out_f = FLAT (SND (frame64_run stepf init (chunks64 inp))))
Proof
  completeInduct_on `n` \\ rpt gen_tac \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `cb_begin = slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ `slot_layout_ok cb_begin cb_end bm_end` by (
       qpat_x_assum `forge_slot_loaded _ _ _ _` mp_tac
       \\ simp [forge_slot_loaded_def, LET_THM] \\ strip_tac
       \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac slot_params_props
       \\ simp [LET_THM])
  \\ drule forge_veneer_facts_slot \\ strip_tac
  \\ qabbrev_tac `P0 = mk_prefix64_P posts`
  \\ `∀j. j < LENGTH posts ⇒ ∀idx bs s s'. P0 j idx bs s s' ⇔ s' = EL j posts` by
       simp [Abbr `P0`, mk_prefix64_P_def]
  \\ `∃ffi0.
        let io0 = <| inputs := chunks64 inp; outputs := []; write_limit := NONE |> in
        let rmc0 = real_mc (bits_of ms0)
                     (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                        (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P0)
                        forge_real_install_if) in
        let rmc_c = real_mc (bits_of ms0)
                      (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                         (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
                         forge_real_install_if) in
        ffi0.oracle = frame64_ffi_oracle ∧
        ffi0.ffi_state = <| inputs := chunks64 inp_cur; outputs := sent_so_far; write_limit := NONE |> ∧
        sent_frames64_of ffi0.io_events = sent_so_far ∧
        (∀k. evaluate rmc0 (frame64_ffi io0) (step_cnt + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate rmc_c ffi0 k s_cur) ∧
        (∀j. FST (evaluate rmc_c ffi0 j s_cur) ≠ Error)` by (
       drule_all chunks64_drop_eq \\ strip_tac
       \\ qpat_x_assum `chunks64 inp = _` (assume_tac o SYM)
       \\ qpat_assum `∀extra_in wlim_rem P. _`
            (qspecl_then [`chunks64 inp_cur`, `NONE`, `P0`] mp_tac)
       \\ impl_tac >- simp []
       \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
       \\ qexists_tac `ffi_cur` \\ gvs [LET_THM]
       \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                       `ms0`, `<| inputs := chunks64 inp; outputs := []; write_limit := NONE |>`,
                       `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P0`,
                       `forge_real_install_if`] mp_tac frame64_compile_exact
       \\ simp [LET_THM, mk_real_ffi_if_slot_ok] \\ strip_tac
       \\ gen_tac
       \\ qpat_x_assum `∀j. FST (evaluate _ _ j _) ≠ Error` (qspec_then `step_cnt + j` mp_tac) \\ simp [])
  \\ pop_assum (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`, `λk. P0 (k + LENGTH posts)`, `ffi0`, `s_cur`]
       mp_tac frame64_eval_step_cases
  \\ simp [LET_THM] \\ strip_tac
  >- (
    (* Case 1: Normal instruction *)
    first_x_assum drule \\ strip_tac
    \\ Cases_on `n`
    >- (gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_def, is_svc0_at_def]
    \\ strip_tac
    \\ qpat_x_assum `∀m. m < SUC n' ⇒ _` (qspec_then `n'` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                                `allow_err`, `ms0`, `inp`, `r`, `w`, `inp_cur`, `out_cur`,
                                `arm8$Next s_cur`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `posts`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      simp [] \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- simp []
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ qexists_tac `ffi_cur` \\ simp []
      \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                      `ms0`, `<| inputs := TAKE r (chunks64 inp) ++ extra_in; outputs := [];
                                 write_limit := OPTION_MAP (λd. w + d) wlim_rem |>`,
                      `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P`,
                      `forge_real_install_if`] mp_tac frame64_compile_exact
      \\ simp [LET_THM, mk_real_ffi_if_slot_ok]
      \\ disch_then (assume_tac o cj 3)
      \\ `∀j. FST (evaluate (real_mc (bits_of ms0)
                      (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                         (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                         forge_real_install_if))
                    ffi_cur j s_cur) ≠ Error` by
           (gen_tac \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + j` mp_tac) \\ simp [])
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`, `λk. P (k + LENGTH posts)`, `ffi_cur`, `s_cur`]
           mp_tac frame64_eval_step_cases
      \\ `s_cur.PC ≠ FORGE_EXIT_VENEER ∧ s_cur.PC ≠ FORGE_INSTALL_VENEER ∧
          s_cur.PC ≠ FORGE_FFISEND_VENEER ∧ s_cur.PC ≠ FORGE_FFIRECV_VENEER` by metis_tac []
      \\ simp [LET_THM] \\ strip_tac
      \\ gen_tac
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp [])
  >- (
    (* Case 2: Exit veneer *)
    mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] cake_exit_universal_slot) shim64_common_words_ok)
    \\ disch_then drule_all \\ strip_tac
    \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `<| inputs := chunks64 inp; outputs := []; write_limit := NONE |>`,
                    `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P0`,
                    `forge_real_install_if`] mp_tac frame64_compile_exact
    \\ simp [LET_THM, mk_real_ffi_if_slot_ok]
    \\ disch_then (assume_tac o cj 5)
    \\ `evaluate (real_mc (bits_of ms0) (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                   (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P0) forge_real_install_if))
          (frame64_ffi <| inputs := chunks64 inp; outputs := []; write_limit := NONE |>)
          (step_cnt + 1) (FUNPOW arm8$Next 43 ms0) =
        (if s_cur.REG 0w = 0w then Halt Success else Halt Resource_limit_hit, s_cur, ffi0)` by
         (qpat_x_assum `s_cur.PC = FORGE_EXIT_VENEER ⇒ _` mp_tac
          \\ impl_tac >- simp []
          \\ disch_then (qspec_then `0` assume_tac)
          \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = _` (qspec_then `SUC 0` mp_tac)
          \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ qpat_x_assum `∀ck t ms_end st_end. _`
         (qspecl_then [`step_cnt + 1`,
                       `if s_cur.REG 0w = 0w then Success else Resource_limit_hit`,
                       `s_cur`, `ffi0`] mp_tac)
    \\ simp [limit_frames64_def]
    \\ (Cases_on `s_cur.REG 0w = 0w` \\ simp [])
    >- (strip_tac \\ rveq \\ simp [])
    \\ strip_tac \\ rveq \\ irule FLAT_prefix \\ simp [])
  >- (
    (* Case 3: Install veneer *)
    mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] cake_install_universal_slot) shim64_common_words_ok)
    \\ disch_then drule_all \\ strip_tac
    \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `<| inputs := chunks64 inp; outputs := []; write_limit := NONE |>`,
                    `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P0`,
                    `forge_real_install_if`] mp_tac frame64_compile_exact
    \\ simp [LET_THM, mk_real_ffi_if_slot_ok] \\ strip_tac
    \\ `evaluate (real_mc (bits_of ms0) (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                   (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P0) forge_real_install_if))
          (frame64_ffi <| inputs := chunks64 inp; outputs := []; write_limit := NONE |>)
          (step_cnt + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by
         (`step_cnt + ck = ck + step_cnt` by decide_tac \\ pop_assum SUBST1_TAC
          \\ irule targetPropsTheory.evaluate_add_clock \\ simp [])
    \\ `ffi0.io_events ≼ st_end.io_events` by (
         qspecl_then [`real_mc (bits_of ms0)
                        (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                           (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
                           forge_real_install_if)`,
                      `ffi0`, `ck`, `s_cur`] mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ gvs [])
    \\ `sent_frames64_of ffi0.io_events ≼ sent_frames64_of st_end.io_events` by simp [sent_frames64_of_prefix]
    \\ `sent_frames64_of st_end.io_events ≼ SND (frame64_run stepf init (chunks64 inp))` by
         fs [limit_frames64_def]
    \\ `sent_so_far ≼ SND (frame64_run stepf init (chunks64 inp))` by
         (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `sent_frames64_of st_end.io_events`
          \\ qpat_x_assum `sent_frames64_of ffi0.io_events ≼ _` mp_tac \\ simp [])
    \\ rveq \\ simp [FLAT_prefix])
  >- (
    (* Case 4: send64 veneer *)
    `∃bytes bytes2.
       read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
       read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes2 ∧
       aligned 2 (s_cur.REG 30w) ∧ untagged (s_cur.REG 30w)` by simp []
    \\ imp_res_tac read_bytearray_mem_eq
    \\ mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] ffisend64_universal_slot)
                 (ASSUME ``slot_layout_ok cb_begin cb_end bm_end``))
    \\ disch_then drule_all \\ strip_tac
    \\ Cases_on `w2n (s_cur.REG 3w) < 65`
    >- (
      first_x_assum drule \\ strip_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `inp`, `r`, `w`, `inp_cur`, `out_cur`,
                                  `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                  `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [] \\ rpt conj_tac >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
        >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_rem`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] frame64_ffi_call_send64)
        \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (0, bytes2, s_cur) = s'` by (
             irule mk_real_ffi64_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                     (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts))) forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                     (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_ffi64_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ fs [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [])
    \\ `65 ≤ w2n (s_cur.REG 3w)` by decide_tac
    \\ first_x_assum drule \\ strip_tac
    >- (
      qabbrev_tac `frame = TAKE 64 (DROP 1 bytes2)`
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `inp`, `r`, `w + 1`, `inp_cur`,
                                  `out_cur ++ frame`, `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                  `posts ++ [s']`, `sent_so_far ++ [frame]`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [listTheory.FLAT_APPEND] \\ rpt conj_tac >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
        >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qabbrev_tac `wlim_prev = OPTION_MAP SUC wlim_rem`
        \\ `OPTION_MAP (λd. d + w) wlim_prev = OPTION_MAP (λd. d + (w + 1)) wlim_rem` by
             (Cases_on `wlim_rem` \\ simp [Abbr `wlim_prev`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
        \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_prev`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] frame64_ffi_call_send64)
        \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
        \\ `new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = <| inputs := extra_in; outputs := sent_so_far ++ [frame];
                                write_limit := wlim_rem |>` by (
             Cases_on `wlim_rem` \\ fs [Abbr `wlim_prev`, Abbr `frame`, frame64_io_component_equality])
        \\ qexists_tac `ffi'` \\ simp [Abbr `frame`]
        \\ `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (0, 0w :: DROP 1 bytes2, s_cur) = s'` by (
             irule mk_real_ffi64_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                     (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts))) forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                     (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_ffi64_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ fs [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [])
    \\ (* Subcase 4c: partial/error write *)
       qabbrev_tac `frame = TAKE 64 (DROP 1 bytes2)`
    \\ qabbrev_tac `P1 = mk_prefix64_P (posts ++ [s'])`
    \\ drule_all chunks64_drop_eq \\ strip_tac
    \\ qpat_x_assum `chunks64 inp = _` (assume_tac o SYM)
    \\ qpat_assum `∀extra_in wlim_rem P. _`
         (qspecl_then [`chunks64 inp_cur`, `SOME 0`, `P1`] mp_tac)
    \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix64_P_def, rich_listTheory.EL_APPEND1])
    \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
    \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
         (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] frame64_ffi_call_send64)
    \\ simp [] \\ strip_tac
    \\ `sent_frames64_of ffi'.io_events = sent_so_far ++ [frame]` by simp [Abbr `frame`]
    \\ `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)) 0 (0, 1w :: DROP 1 bytes2, s_cur) = s'` by (
         irule mk_real_ffi64_if_select \\ simp [Abbr `P1`, mk_prefix64_P_def, rich_listTheory.EL_LENGTH_APPEND])
    \\ qabbrev_tac `io_err = <| inputs := chunks64 inp; outputs := []; write_limit := SOME w |>`
    \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0) (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P1) forge_real_install_if)`
    \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                     (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P1 (k + (LENGTH posts + 1)))) forge_real_install_if)`
    \\ `∀k. evaluate rmc1 (frame64_ffi io_err) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
            evaluate rmc_post ffi' k s'` by (
         gen_tac
         \\ `evaluate rmc1 (frame64_ffi io_err) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate (real_mc (bits_of ms0)
               (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts))) forge_real_install_if))
               ffi_cur (SUC k) s_cur` by (
              qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
              \\ simp [Abbr `io_err`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
         \\ pop_assum SUBST1_TAC
         \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc_post`, real_mc_def, forge_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi64_if]
         \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
              (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
         \\ simp [])
    \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `<| inputs := chunks64 inp; outputs := []; write_limit := SOME w |>`,
                    `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P1`,
                    `forge_real_install_if`] mp_tac frame64_compile_exact
    \\ simp [LET_THM, mk_real_ffi_if_slot_ok]
    \\ disch_then (fn th => assume_tac (cj 3 th) \\ strip_assume_tac (cj 4 th))
    \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
         `evaluate rmc1 (frame64_ffi <|inputs := chunks64 inp; outputs := []; write_limit := SOME w|>)
            (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
              `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
              \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
         \\ pop_assum mp_tac
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
         \\ simp [Abbr `io_err`])
    \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
         gen_tac
         \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
         \\ simp [Abbr `rmc1`, Abbr `io_err`])
    \\ qspecl_then [`n'`, `cb_begin`, `cb_end`, `bm_end`, `allow_err`, `bits_of ms0`, `λk. P1 (k + (LENGTH posts + 1))`,
                    `ffi'`, `s'`, `inp_cur`, `out_cur ++ chunk`, `inp_f`, `out_f`, `ms_f`, `ec`,
                    `ck`, `t`, `ms_end`, `st_end`] mp_tac frame64_post_err_nrc_safety
    \\ simp [LET_THM]
    \\ (impl_tac >- (
         qpat_x_assum `ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end _ _ _` (strip_assume_tac o REWRITE_RULE [ffi_return_ok_slot_def])
         \\ qpat_x_assum `event_is_err64 _` mp_tac
         \\ qpat_x_assum `NRC _ n' _ _` mp_tac
         \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
         \\ qpat_x_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
         \\ simp [Abbr `rmc_post`, boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]))
    \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
    \\ simp []
    \\ `ffi'.io_events ≼ st_end.io_events` by (
         qspecl_then [`rmc_post`, `ffi'`, `ck`, `s'`] mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ simp [])
    \\ `sent_so_far ++ [frame] ≼ SND (frame64_run stepf init (chunks64 inp))` by (
         `sent_frames64_of ffi'.io_events ≼ sent_frames64_of st_end.io_events` by simp [sent_frames64_of_prefix]
         \\ `sent_frames64_of st_end.io_events ≼ limit_frames64 (SOME w) (SND (frame64_run stepf init (chunks64 inp)))` by simp []
         \\ `limit_frames64 (SOME w) (SND (frame64_run stepf init (chunks64 inp))) ≼
             SND (frame64_run stepf init (chunks64 inp))` by simp [limit_frames64_prefix]
         \\ irule rich_listTheory.IS_PREFIX_TRANS
         \\ qexists_tac `sent_frames64_of st_end.io_events`
         \\ (conj_tac
             >- (irule rich_listTheory.IS_PREFIX_TRANS
                 \\ qexists_tac `limit_frames64 (SOME w) (SND (frame64_run stepf init (chunks64 inp)))`
                 \\ simp []))
         \\ qpat_x_assum `sent_frames64_of ffi'.io_events ≼ _` mp_tac \\ simp [Abbr `frame`])
    \\ `out_cur ++ chunk ≼ FLAT (sent_so_far ++ [frame])` by
         (qpat_x_assum `FLAT sent_so_far = out_cur` (SUBST1_TAC o SYM) \\ simp [FLAT_snoc_prefix])
    \\ `FLAT (sent_so_far ++ [frame]) ≼ FLAT (SND (frame64_run stepf init (chunks64 inp)))` by
         simp [FLAT_prefix]
    \\ irule rich_listTheory.IS_PREFIX_TRANS
    \\ qexists_tac `FLAT (sent_so_far ++ [frame])` \\ simp [])
  \\ (* Case 5: recv64 veneer *)
     `∃bytes bytes2.
        read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
        read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s_cur.MEM a) else NONE) = SOME bytes2 ∧
        aligned 2 (s_cur.REG 30w) ∧ untagged (s_cur.REG 30w)` by simp []
  \\ imp_res_tac read_bytearray_mem_eq
  \\ mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] ffirecv64_universal_slot)
               (ASSUME ``slot_layout_ok cb_begin cb_end bm_end``))
  \\ disch_then drule_all \\ strip_tac
  \\ Cases_on `w2n (s_cur.REG 3w) < 65`
  >- (
    first_x_assum drule \\ strip_tac
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
    \\ disch_then (qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                                `allow_err`, `ms0`, `inp`, `r`, `w`, `inp_cur`, `out_cur`,
                                `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      simp [] \\ rpt conj_tac >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
      >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
      \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ drule_all frame64_ffi_call_recv64
      \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
      \\ qexists_tac `ffi'` \\ simp []
      \\ `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (1, bytes2, s_cur) = s'` by (
           irule mk_real_ffi64_if_select \\ simp []
           \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
           \\ simp [rich_listTheory.EL_LENGTH_APPEND])
      \\ `∀k. evaluate (real_mc (bits_of ms0)
                (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                   (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts))) forge_real_install_if))
              ffi_cur (SUC k) s_cur =
              evaluate (real_mc (bits_of ms0)
                (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                   (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
              ffi' k s'` by (
           gen_tac
           \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi64_if]
           \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
           \\ fs [])
      \\ gen_tac
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp [])
  \\ `65 ≤ w2n (s_cur.REG 3w)` by decide_tac
  \\ first_x_assum drule
  \\ disch_then (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS)))
  >- (
    (* Subcase 5b: read full 64B frame *)
    drule_all chunks64_take_step \\ strip_tac
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
    \\ disch_then (qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                                `allow_err`, `ms0`, `inp`, `r + 1`, `w`, `inp_after`, `out_cur`,
                                `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      simp [] \\ rpt conj_tac >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
      >- fs [ffi_return_ok_slot_def] >- fs [ffi_return_ok_slot_def]
      \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`frame :: extra_in`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac frame64_ffi_call_recv64
      \\ simp [] \\ strip_tac
      \\ `ffi'.ffi_state = <| inputs := extra_in; outputs := sent_so_far; write_limit := wlim_rem |>` by
           simp [frame64_io_component_equality]
      \\ qexists_tac `ffi'` \\ simp []
      \\ `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (1, 0w :: frame ++ DROP 65 bytes2, s_cur) = s'` by (
           irule mk_real_ffi64_if_select \\ simp []
           \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
           \\ simp [rich_listTheory.EL_LENGTH_APPEND])
      \\ `∀k. evaluate (real_mc (bits_of ms0)
                (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                   (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + LENGTH posts))) forge_real_install_if))
              ffi_cur (SUC k) s_cur =
              evaluate (real_mc (bits_of ms0)
                (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»]
                   (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
              ffi' k s'` by (
           gen_tac
           \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi64_if]
           \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
           \\ fs [])
      \\ gen_tac
      \\ `TAKE r (chunks64 inp) ++ [frame] ++ extra_in = TAKE r (chunks64 inp) ++ frame :: extra_in` by
           REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp [])
  \\ (* Subcase 5c: EOF / truncated <64B / read error *)
     qabbrev_tac `P1 = mk_prefix64_P (posts ++ [s'])`
  \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`[]`, `NONE`, `P1`] mp_tac)
  \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix64_P_def, rich_listTheory.EL_APPEND1])
  \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
  \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac frame64_ffi_call_recv64
  \\ simp [] \\ strip_tac
  \\ `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)) 0 (1, 1w :: DROP 1 bytes2, s_cur) = s'` by (
       irule mk_real_ffi64_if_select \\ simp [Abbr `P1`, mk_prefix64_P_def, rich_listTheory.EL_LENGTH_APPEND])
  \\ qabbrev_tac `io_eof = <| inputs := TAKE r (chunks64 inp); outputs := []; write_limit := NONE |>`
  \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0) (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P1) forge_real_install_if)`
  \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                   (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P1 (k + (LENGTH posts + 1)))) forge_real_install_if)`
  \\ `∀k. evaluate rmc1 (frame64_ffi io_eof) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
          evaluate rmc_post ffi' k s'` by (
       gen_tac
       \\ `evaluate rmc1 (frame64_ffi io_eof) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
           evaluate (real_mc (bits_of ms0)
             (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] (mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts))) forge_real_install_if))
             ffi_cur (SUC k) s_cur` by (
            qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
            \\ simp [Abbr `io_eof`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
       \\ pop_assum SUBST1_TAC
       \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc_post`, real_mc_def, forge_mc_slot_def,
                arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                shift_mk_real_ffi64_if]
       \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
            (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
       \\ simp [])
  \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                  `ms0`, `<| inputs := TAKE r (chunks64 inp); outputs := []; write_limit := NONE |>`,
                  `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end P1`,
                  `forge_real_install_if`] mp_tac frame64_compile_exact
  \\ simp [LET_THM, mk_real_ffi_if_slot_ok, limit_frames64_def]
  \\ disch_then (fn th => assume_tac (cj 3 th) \\ strip_assume_tac (cj 4 th))
  \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
       `evaluate rmc1 (frame64_ffi <|inputs := TAKE r (chunks64 inp); outputs := []; write_limit := NONE|>)
          (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
            `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
            \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
       \\ pop_assum mp_tac
       \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
       \\ simp [Abbr `io_eof`])
  \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
       gen_tac
       \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
       \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
       \\ simp [Abbr `rmc1`, Abbr `io_eof`])
  \\ qspecl_then [`n'`, `cb_begin`, `cb_end`, `bm_end`, `allow_err`, `bits_of ms0`, `λk. P1 (k + (LENGTH posts + 1))`,
                  `ffi'`, `s'`, `inp_after`, `out_cur`, `inp_f`, `out_f`, `ms_f`, `ec`,
                  `ck`, `t`, `ms_end`, `st_end`] mp_tac frame64_post_err_nrc_safety
  \\ simp [LET_THM]
  \\ (impl_tac >- (
       qpat_x_assum `ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_end _ _ _` (strip_assume_tac o REWRITE_RULE [ffi_return_ok_slot_def])
       \\ qpat_x_assum `event_is_err64 _` mp_tac
       \\ qpat_x_assum `NRC _ n' _ _` mp_tac
       \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
       \\ qpat_x_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
       \\ simp [Abbr `rmc_post`, boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]))
  \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
  \\ simp []
  \\ `ffi'.io_events ≼ st_end.io_events` by (
       qspecl_then [`rmc_post`, `ffi'`, `ck`, `s'`] mp_tac targetPropsTheory.evaluate_io_events_mono
       \\ simp [])
  \\ `out_cur ≼ FLAT (SND (frame64_run stepf init (chunks64 inp)))` by (
       `sent_so_far ≼ SND (frame64_run stepf init (TAKE r (chunks64 inp)))` by (
         `sent_frames64_of ffi'.io_events ≼ sent_frames64_of st_end.io_events` by simp [sent_frames64_of_prefix]
         \\ `sent_frames64_of st_end.io_events ≼ SND (frame64_run stepf init (TAKE r (chunks64 inp)))` by simp []
         \\ irule rich_listTheory.IS_PREFIX_TRANS
         \\ qexists_tac `sent_frames64_of st_end.io_events`
         \\ qpat_x_assum `sent_frames64_of ffi'.io_events ≼ _` mp_tac \\ simp [])
       \\ `SND (frame64_run stepf init (TAKE r (chunks64 inp))) ≼
           SND (frame64_run stepf init (chunks64 inp))` by
            (irule frame64_run_take_prefix \\ simp [chunks64_every_len64])
       \\ `sent_so_far ≼ SND (frame64_run stepf init (chunks64 inp))` by
            (irule rich_listTheory.IS_PREFIX_TRANS
             \\ qexists_tac `SND (frame64_run stepf init (TAKE r (chunks64 inp)))` \\ simp [])
       \\ qpat_x_assum `FLAT sent_so_far = out_cur` (SUBST1_TAC o SYM)
       \\ simp [FLAT_prefix])
  \\ simp []
  \\ rpt strip_tac
  \\ `LENGTH inp_cur < 64` by (qpat_x_assum `allow_err ∨ _` mp_tac \\ simp [])
  \\ `TAKE r (chunks64 inp) = chunks64 inp` by (
       qspecl_then [`r`, `inp`, `inp_cur`] mp_tac chunks64_take_all_of_lt64
       \\ impl_tac >- (rpt conj_tac \\ TRY (first_assum ACCEPT_TAC) \\ simp [])
       \\ simp [])
  \\ `t = Success ∧ st_end.io_events = ffi'.io_events` by simp []
  \\ `sent_so_far = SND (frame64_run stepf init (chunks64 inp))` by (
       qpat_x_assum `sent_frames64_of st_end.io_events = _` mp_tac
       \\ qpat_x_assum `st_end.io_events = ffi'.io_events` SUBST1_TAC
       \\ qpat_x_assum `TAKE r (chunks64 inp) = chunks64 inp` SUBST1_TAC
       \\ simp [])
  \\ qpat_x_assum `FLAT sent_so_far = out_cur` (SUBST1_TAC o SYM)
  \\ simp []
QED

(* ---- 6. Polymorphic Top-Level Whole-Binary 64-Byte Kernel Composition Theorem ---- *)

Theorem forge_frame64_kernel_compose:
  ∀(stepf:'st -> frame64 -> 'st # frame64) (init:'st) prog code data info oracle.
    backend$compile arm8_config (set_oracle arm8_backend_config oracle) prog = SOME (code, data, info) ∧
    prog_syntax_ok prog ∧
    info.lab_conf.shmem_extra = [] ∧
    ffinames_to_string_list (the [] info.lab_conf.ffi_names) = [«send64»; «recv64»] ∧
    0 < LENGTH code ∧ LENGTH code ≤ FORGE_MAX_CODE_BYTES ∧
    LENGTH data ≤ FORGE_MAX_BITMAP_WORDS ∧
    (∀io:frame64_io.
       io.outputs = [] ⇒
       sem_satisfies
         (semantics_dec_list (init_state (frame64_ffi io)) init_env prog)
         (λb. ∃io_events.
                b = Terminate Success io_events ∧
                stop_after_err64 io_events ∧
                sent_frames64_of io_events =
                  limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs)))) ⇒
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
                (FLAT (SND (frame64_run stepf init (chunks64 inp))))) ∧
         (∀(inp:word8 list) inp_f out_f ms_f exit_code.
            RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
              (inp, [], ms0) (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel exit_code ms_f ∧
            exit_code = 0w ⇒
              out_f = FLAT (SND (frame64_run stepf init (chunks64 inp))))) ∧
    (∃ms0:arm8_state.
       forge_slot_loaded forge_shim64_words code data ms0 ∧
       ms0.TCR_EL1.TBI0 ∧
       ¬ms0.TCR_EL1.TBI1 ∧
       ms0.SCTLR_EL1.SA0 ∧
       aligned 4 ms0.SP_EL0)
Proof
  rpt strip_tac
  >- (
    simp [LET_THM]
    \\ qabbrev_tac `cb_begin = slot_cb_begin (LENGTH code)`
    \\ qabbrev_tac `cb_end = slot_cb_end (LENGTH code)`
    \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
    \\ qabbrev_tac `cbsp = slot_cbspace (LENGTH code)`
    \\ `slot_layout_ok cb_begin cb_end bm_end` by (
         qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac slot_params_props
         \\ simp [LET_THM])
    \\ `det_run 43 ms0 (FUNPOW arm8$Next 43 ms0) ∧
        arm8_ok (erase (FUNPOW arm8$Next 43 ms0)) ∧
        sp_ok (FUNPOW arm8$Next 43 ms0) ∧
        bits_of (FUNPOW arm8$Next 43 ms0) = bits_of ms0 ∧
        shim_loaded_slot forge_shim64_words cb_begin cb_end bm_end (FUNPOW arm8$Next 43 ms0).MEM` by (
         fs [forge_slot_loaded_def, LET_THM]
         \\ qspecl_then [`forge_shim64_words`, `cb_begin`, `cb_end`, `bm_end`, `ms0`]
              mp_tac startup_to_cake_main_slot
         \\ simp [shim64_common_words_ok, LET_THM])
    \\ rpt conj_tac
    >- (
      rpt strip_tac \\ simp [LET_THM]
      \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                      `ms0`, `io`, `ffi_if`, `inst_if`] mp_tac frame64_compile_exact
      \\ simp [LET_THM])
    >- (
      gen_tac
      \\ qspec_then `inp` strip_assume_tac chunks64_split_tail
      \\ qspecl_then [`stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                      `ms0`, `<| inputs := chunks64 inp; outputs := []; write_limit := NONE |>`,
                      `mk_real_ffi_if_slot forge_shim64_words cb_begin cb_end bm_end
                         (noerr_ffi64_P cb_end bm_end tail_bs)`,
                      `forge_real_install_if`] mp_tac frame64_compile_exact
      \\ simp [LET_THM, mk_real_ffi_if_slot_ok]
      \\ disch_then (fn th => assume_tac (cj 3 th) \\ mp_tac (cj 4 th))
      \\ disch_then (qx_choosel_then [`ck`, `t`, `ms_end`, `st_end`] (EVERY o map assume_tac o CONJUNCTS))
      \\ qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`, `tail_bs`,
                      `frame64_ffi <| inputs := chunks64 inp; outputs := []; write_limit := NONE |>`,
                      `FUNPOW arm8$Next 43 ms0`, `inp`, `[]`, `t`, `ms_end`, `st_end`]
           mp_tac frame64_liveness_eval_rtc
      \\ simp [LET_THM]
      \\ impl_tac >- (
           rpt conj_tac
           \\ TRY (first_assum ACCEPT_TAC)
           \\ simp [frame64_ffi_def, ffiTheory.initial_ffi_state_def, chunks64_every_len64])
      \\ strip_tac
      \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp []
      \\ irule relationTheory.RTC_RTC
      \\ qexists_tac `(inp, [], FUNPOW arm8$Next 43 ms0)`
      \\ simp []
      \\ irule det_run_imp_rtc \\ qexists_tac `43` \\ simp [])
    >- (
      rpt gen_tac \\ strip_tac
      \\ qpat_x_assum `RTC _ _ _` (strip_assume_tac o REWRITE_RULE [arithmeticTheory.RTC_eq_NRC])
      \\ drule_all det_run_peel_nrc \\ strip_tac
      \\ qspecl_then [`n - 43`, `stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                      `T`, `ms0`, `inp`, `0`, `0`, `inp`, `[]`,
                      `FUNPOW arm8$Next 43 ms0`, `inp_f`, `out_f`, `ms_f`, `exit_code`,
                      `[]`, `[]`, `0`] mp_tac frame64_pre_err_nrc_safety
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [] \\ rpt gen_tac
        \\ qexists_tac `frame64_ffi <| inputs := extra_in; outputs := []; write_limit := wlim_rem |>`
        \\ `OPTION_MAP (λd:num. d) wlim_rem = wlim_rem` by (Cases_on `wlim_rem` \\ simp [])
        \\ simp [frame64_ffi_def, ffiTheory.initial_ffi_state_def, sent_frames64_of_def, ETA_THM])
      \\ simp [])
    \\ rpt gen_tac \\ strip_tac
    \\ qpat_x_assum `RTC _ _ _` (strip_assume_tac o REWRITE_RULE [arithmeticTheory.RTC_eq_NRC])
    \\ drule_all det_run_peel_nrc \\ strip_tac
    \\ qspecl_then [`n - 43`, `stepf`, `init`, `prog`, `code`, `data`, `info`, `oracle`,
                    `F`, `ms0`, `inp`, `0`, `0`, `inp`, `[]`,
                    `FUNPOW arm8$Next 43 ms0`, `inp_f`, `out_f`, `ms_f`, `0w`,
                    `[]`, `[]`, `0`] mp_tac frame64_pre_err_nrc_safety
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      simp [] \\ rpt gen_tac
      \\ qexists_tac `frame64_ffi <| inputs := extra_in; outputs := []; write_limit := wlim_rem |>`
      \\ `OPTION_MAP (λd:num. d) wlim_rem = wlim_rem` by (Cases_on `wlim_rem` \\ simp [])
      \\ simp [frame64_ffi_def, ffiTheory.initial_ffi_state_def, sent_frames64_of_def, ETA_THM])
    \\ simp [])
  \\ irule forge_slot_nonvacuous
  \\ simp [shim64_len]
QED
