(*
  Forge Milestone 3 Reusable Runtime: Generic 4-FFI Crash-Atomic Whole-Binary
  Kernel Composition Theory (`bootload`, `send128`, `recv64`, `commit`).

  Proves ONE polymorphic end-to-end theorem (`forge_airlock_kernel_compose`) for
  ANY pure dual-slot recovery + 64B->128B airlock step function, linking:
    1. In-logic CakeML arm8 compilation (`compile ... = SOME (code, data, info)`)
    2. Whole-program CakeML source semantics (`sem_satisfies ... airlock_exec`)
    3. Fixed 256 KB RX slot + 52-word veneers + 168-word 6-syscall shim
    4. Exact arm8$Next erasure (`forge_arm8Erasure`) & universal 6-syscall Linux
       `read(63)` / `write(64)` / `pread64(67)` / `pwrite64(68)` / `fdatasync(83)` /
       `exit_group(94)` safety & forward liveness (`forge_airlockShimStart/Io/Proof`)
  into the exact whole-binary execution theorem + non-vacuity witness.
*)
Theory forge_airlockCompose
Ancestors
  forge_frame64Spec forge_airlockFfi forge_airlockContract forge_runtimeSpec
  forge_airlockRunner forge_arm8Erasure forge_shimProof forge_slotUtil
  forge_airlockShimBase forge_airlockShimStart forge_airlockShimIo
  forge_airlockShimProof
  arm8_target arm8_configProof lab_to_targetProof backendProof ml_prog
  targetProps semanticsProps alignment set_sep byte
Libs
  preamble blastLib wordsLib

(* ---- 1. Generic Stream, Prefix & Boot/Error Trace Helpers ---- *)

Theorem stop_after_err_al_prefix[local]:
  ∀xs ys. xs ≼ ys ∧ stop_after_err_al ys ⇒ stop_after_err_al xs
Proof
  Induct \\ simp [stop_after_err_al_def]
  \\ rpt strip_tac
  \\ Cases_on `ys` \\ fs [stop_after_err_al_def]
  \\ rveq
  \\ Cases_on `event_is_err_al h` \\ fs [stop_after_err_al_def]
  \\ metis_tac []
QED

Theorem stop_after_err_al_prefix_eq[local]:
  ∀es1 es2.
    es1 ≼ es2 ∧ stop_after_err_al es2 ∧ (∃e. MEM e es1 ∧ event_is_err_al e) ⇒
    es2 = es1
Proof
  Induct \\ simp []
  \\ rpt strip_tac
  \\ Cases_on `es2` \\ fs [stop_after_err_al_def]
  \\ rveq
  \\ Cases_on `event_is_err_al h` \\ fs []
  \\ first_x_assum irule \\ simp [] \\ metis_tac []
QED

Theorem boot_first_once_al_prefix[local]:
  ∀xs ys. xs ≼ ys ∧ boot_first_once_al ys ⇒ boot_first_once_al xs
Proof
  Cases \\ simp [boot_first_once_al_def]
  \\ rpt strip_tac
  \\ Cases_on `ys` \\ fs [boot_first_once_al_def]
  \\ rveq \\ fs [IS_PREFIX_APPEND] \\ rveq \\ fs []
QED

Theorem boot_first_once_al_first_must_be_boot[local]:
  ∀e es. [e] ≼ es ∧ boot_first_once_al es ⇒ is_bootload_ev e
Proof
  rpt gen_tac \\ Cases_on `es` \\ simp [boot_first_once_al_def]
QED

Theorem boot_first_once_al_no_second_boot[local]:
  ∀es1 e es2. es1 ≠ [] ∧ (es1 ++ [e]) ≼ es2 ∧ boot_first_once_al es2 ⇒ ¬is_bootload_ev e
Proof
  rpt gen_tac \\ Cases_on `es1` \\ simp []
  \\ Cases_on `es2` \\ simp [boot_first_once_al_def, IS_PREFIX_APPEND]
  \\ rpt strip_tac \\ rveq \\ fs []
QED

Theorem sent_frames128_of_prefix[local]:
  ∀xs ys. xs ≼ ys ⇒ sent_frames128_of xs ≼ sent_frames128_of ys
Proof
  rw [IS_PREFIX_APPEND] \\ simp [sent_frames128_of_append]
QED

Theorem m3_FLAT_prefix[local]:
  ∀xs ys. xs ≼ ys ⇒ FLAT xs ≼ FLAT ys
Proof
  rw [IS_PREFIX_APPEND] \\ simp [listTheory.FLAT_APPEND]
QED

Theorem m3_FLAT_snoc_prefix[local]:
  ∀xs f chunk. chunk ≼ f ⇒ FLAT xs ++ chunk ≼ FLAT (xs ++ [f])
Proof
  simp [listTheory.FLAT_APPEND]
QED

Theorem airlock_exec_append_none[local]:
  ∀stepf inps1 inps2 key st.
    EVERY (λf. LENGTH f = 64) inps1 ⇒
    SND (airlock_exec stepf key st (inps1 ++ inps2) NONE NONE) =
      SND (airlock_exec stepf key st inps1 NONE NONE) ++
      SND (airlock_exec stepf key (FST (airlock_exec stepf key st inps1 NONE NONE)) inps2 NONE NONE)
Proof
  gen_tac \\ Induct_on `inps1`
  >- simp [airlock_exec_def]
  \\ rpt strip_tac \\ fs []
  \\ simp [airlock_exec_def]
  \\ Cases_on `stepf key st (frame64_decode h)` \\ Cases_on `r` \\ simp []
  \\ Cases_on `r'` \\ simp []
  \\ Cases_on `airlock_exec stepf key q inps1 NONE NONE` \\ simp []
  \\ Cases_on `airlock_exec stepf key q (inps1 ++ inps2) NONE NONE` \\ simp []
  \\ first_x_assum (qspecl_then [`inps2`, `key`, `q`] mp_tac) \\ simp []
QED

Theorem airlock_exec_take_prefix_none[local]:
  ∀stepf r inps key st.
    EVERY (λf. LENGTH f = 64) inps ⇒
    SND (airlock_exec stepf key st (TAKE r inps) NONE NONE) ≼
      SND (airlock_exec stepf key st inps NONE NONE)
Proof
  rpt strip_tac
  \\ `inps = TAKE r inps ++ DROP r inps` by simp [listTheory.TAKE_DROP]
  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [th])))))))
  \\ `EVERY (λf. LENGTH f = 64) (TAKE r inps)` by simp [rich_listTheory.EVERY_TAKE]
  \\ drule airlock_exec_append_none \\ simp [IS_PREFIX_APPEND]
QED

Theorem m3_chunks64_split_tail[local]:
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

Theorem m3_chunks64_drop_eq[local]:
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

Theorem m3_chunks64_take_step[local]:
  ∀r inp inp_cur frame inp_after.
    r ≤ LENGTH (chunks64 inp) ∧
    inp = FLAT (TAKE r (chunks64 inp)) ++ inp_cur ∧
    LENGTH frame = 64 ∧ inp_cur = frame ++ inp_after ⇒
    r + 1 ≤ LENGTH (chunks64 inp) ∧
    TAKE (r + 1) (chunks64 inp) = TAKE r (chunks64 inp) ++ [frame] ∧
    inp = FLAT (TAKE (r + 1) (chunks64 inp)) ++ inp_after
Proof
  rpt gen_tac \\ strip_tac
  \\ drule_all m3_chunks64_drop_eq \\ strip_tac
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

Theorem m3_chunks64_take_all_of_lt64[local]:
  ∀r inp inp_cur.
    r ≤ LENGTH (chunks64 inp) ∧
    inp = FLAT (TAKE r (chunks64 inp)) ++ inp_cur ∧
    LENGTH inp_cur < 64 ⇒
    TAKE r (chunks64 inp) = chunks64 inp
Proof
  rpt strip_tac
  \\ drule_all m3_chunks64_drop_eq \\ strip_tac
  \\ `chunks64 inp_cur = []` by simp [chunks64_lt64]
  \\ qpat_x_assum `chunks64 inp = _` (fn th => CONV_TAC (RHS_CONV (REWR_CONV th)))
  \\ simp []
QED

(* ---- 2. Generic Compilation Lift for 4-FFI Airlock Kernels ---- *)

Theorem m3_compile_exact[local]:
  ∀(recf:word8 list -> word8 list -> word8 list -> 'st)
   (stepf:word8 list -> 'st -> frame64 -> 'st # frame128 # bool)
   prog code data info oracle ms0 io ffi_if inst_if.
    backend$compile arm8_config (set_oracle arm8_backend_config oracle) prog = SOME (code, data, info) ∧
    prog_syntax_ok prog ∧
    info.lab_conf.shmem_extra = [] ∧
    ffinames_to_string_list (the [] info.lab_conf.ffi_names) =
      [«bootload»; «send128»; «recv64»; «commit»] ∧
    (∀io0:airlock_io.
       io0.outputs = [] ⇒
       sem_satisfies
         (semantics_dec_list (init_state (airlock_ffi io0)) init_env prog)
         (λb. ∃io_events.
                b = Terminate Success io_events ∧
                stop_after_err_al io_events ∧
                boot_first_once_al io_events ∧
                sent_frames128_of io_events =
                  if ¬io0.boot_fail ∧ LENGTH io0.boot_key = 32 ∧
                     LENGTH io0.slotA = 256 ∧ LENGTH io0.slotB = 256 then
                    SND (airlock_exec stepf io0.boot_key
                           (recf io0.boot_key io0.slotA io0.slotB)
                           io0.inputs io0.commit_limit io0.write_limit)
                  else [])) ∧
    forge_m3_slot_loaded code data ms0 ∧ io.outputs = [] ∧
    m3_real_interfer_ok_slot (m3_slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data))
      (m3_slot_cbspace (LENGTH code))
      [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
      (bits_of ms0) ffi_if inst_if ⇒
    let ms1 = FUNPOW arm8$Next 43 ms0 in
    let cb_end = m3_slot_cb_end (LENGTH code) in
    let bm_end = slot_bm_buf_end (LENGTH data) in
    let rmc = real_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                   ffi_if inst_if) in
    let exp = if ¬io.boot_fail ∧ LENGTH io.boot_key = 32 ∧
                 LENGTH io.slotA = 256 ∧ LENGTH io.slotB = 256 then
                SND (airlock_exec stepf io.boot_key
                       (recf io.boot_key io.slotA io.slotB)
                       io.inputs io.commit_limit io.write_limit)
              else [] in
      rmc.target = arm8_target_real (bits_of ms0) ∧
      ¬machine_sem rmc (airlock_ffi io) ms1 Fail ∧
      (∀j. FST (evaluate rmc (airlock_ffi io) j ms1) ≠ Error) ∧
      (∃ck t ms_end st_end.
         evaluate rmc (airlock_ffi io) ck ms1 = (Halt t, ms_end, st_end) ∧
         stop_after_err_al st_end.io_events ∧
         boot_first_once_al st_end.io_events ∧
         ((t = Success ∧ sent_frames128_of st_end.io_events = exp) ∨
          (t = Resource_limit_hit ∧ sent_frames128_of st_end.io_events ≼ exp))) ∧
      (∀ck t ms_end st_end.
         evaluate rmc (airlock_ffi io) ck ms1 = (Halt t, ms_end, st_end) ⇒
         stop_after_err_al st_end.io_events ∧
         boot_first_once_al st_end.io_events ∧
         ((t = Success ∧ sent_frames128_of st_end.io_events = exp) ∨
          (t = Resource_limit_hit ∧ sent_frames128_of st_end.io_events ≼ exp)))
Proof
  rpt strip_tac
  \\ simp [LET_THM]
  \\ qabbrev_tac `cb_begin = m3_slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = m3_slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ qabbrev_tac `cbsp = m3_slot_cbspace (LENGTH code)`
  \\ `info.lab_conf.ffi_names =
        SOME [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]` by (
       drule (REWRITE_RULE [GSYM AND_IMP_INTRO] compile_imp_ffi_names)
       \\ disch_then (qspec_then `[«bootload»; «send128»; «recv64»; «commit»]` mp_tac)
       \\ simp [backendTheory.set_oracle_def, arm8_configTheory.arm8_backend_config_def])
  \\ `m3_slot_layout_ok cb_begin cb_end bm_end` by (
       fs [forge_m3_slot_loaded_def, LET_THM]
       \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac m3_slot_params_props
       \\ simp [LET_THM])
  \\ qspecl_then [`«bootload»`, `«send128»`, `«recv64»`, `«commit»`, `code`, `data`,
                  `info.lab_conf.ffi_names`, `ms0`, `ffi_if`, `inst_if`]
       mp_tac forge_m3_slot_installed_exact
  \\ impl_tac >- simp []
  \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ qabbrev_tac `mc0 = forge_m3_mc_slot cb_end bm_end
                          [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                          ffi_if inst_if`
  \\ qabbrev_tac `emc = erase_mc (bits_of ms0) mc0`
  \\ qabbrev_tac `rmc = real_mc (bits_of ms0) mc0`
  \\ qpat_x_assum `∀io0. io0.outputs = [] ⇒ sem_satisfies _ _` (qspec_then `io` mp_tac)
  \\ impl_tac >- simp [] \\ strip_tac
  \\ qabbrev_tac `exp = if ¬io.boot_fail ∧ LENGTH io.boot_key = 32 ∧
                           LENGTH io.slotA = 256 ∧ LENGTH io.slotB = 256 then
                          SND (airlock_exec stepf io.boot_key
                                 (recf io.boot_key io.slotA io.slotB)
                                 io.inputs io.commit_limit io.write_limit)
                        else []`
  \\ `∀b. semantics_prog (init_state (airlock_ffi io)) init_env prog b ⇒
          ∃io_events. b = Terminate Success io_events ∧
                      stop_after_err_al io_events ∧
                      boot_first_once_al io_events ∧
                      sent_frames128_of io_events = exp` by
       fs [semanticsPropsTheory.sem_satisfies_def, ml_progTheory.semantics_dec_list_eq, IN_DEF, Abbr `exp`]
  \\ `¬semantics_prog (init_state (airlock_ffi io)) init_env prog Fail` by
       (strip_tac \\ first_x_assum drule \\ simp [])
  \\ `heap_regs arm8_backend_config.stack_conf.reg_names = (1, 3)` by EVAL_TAC
  \\ `mc_conf_ok emc ∧ mc_init_ok arm8_config arm8_backend_config emc` by
       simp [Abbr `emc`, Abbr `mc0`, m3_erase_mc_conf_ok_slot, m3_erase_mc_init_ok_slot]
  \\ `machine_sem emc (airlock_ffi io) (erase ms1) ⊆
      extend_with_resource_limit (semantics_prog (init_state (airlock_ffi io)) init_env prog)` by (
       qpat_x_assum `backend$compile _ _ _ = _` (fn th =>
         irule (MATCH_MP backendProofTheory.compile_correct th
                |> SIMP_RULE (srw_ss()) [LET_THM, ml_progTheory.init_state_env_thm,
                                         backendProofTheory.set_oracle_simp,
                                         arm8_configProofTheory.arm8_backend_config_ok]))
       \\ simp [] \\ metis_tac [])
  \\ `¬machine_sem emc (airlock_ffi io) (erase ms1) Fail` by (
       strip_tac
       \\ `Fail ∈ extend_with_resource_limit (semantics_prog (init_state (airlock_ffi io)) init_env prog)` by
            fs [SUBSET_DEF, IN_DEF]
       \\ drule semanticsPropsTheory.extend_with_resource_limit_not_fail
       \\ simp [IN_DEF])
  \\ `machine_sem rmc (airlock_ffi io) ms1 = machine_sem emc (airlock_ffi io) (erase ms1)` by (
       fs [Abbr `rmc`, Abbr `emc`]
       \\ irule machine_sem_real_eq_exact
       \\ simp [Abbr `mc0`, MATCH_MP forge_m3_mc_slot_lo55 (ASSUME ``m3_slot_layout_ok cb_begin cb_end bm_end``)]
       \\ rpt conj_tac
       >- fs [m3_real_interfer_ok_slot_def, LET_THM, forge_m3_mc_slot_def]
       >- fs [m3_real_interfer_ok_slot_def, LET_THM, forge_m3_mc_slot_def]
       >- simp [forge_m3_mc_slot_def]
       >- simp [forge_m3_mc_slot_def]
       \\ fs [sp_ok_def, bits_of_def, forge_m3_slot_loaded_def, LET_THM])
  \\ `¬machine_sem rmc (airlock_ffi io) ms1 Fail` by simp []
  \\ `∀b. machine_sem rmc (airlock_ffi io) ms1 b ⇒
          ∃t io_events.
            b = Terminate t io_events ∧
            stop_after_err_al io_events ∧
            boot_first_once_al io_events ∧
            ((t = Success ∧ sent_frames128_of io_events = exp) ∨
             (t = Resource_limit_hit ∧ sent_frames128_of io_events ≼ exp))` by (
       rpt strip_tac
       \\ `b ∈ extend_with_resource_limit (semantics_prog (init_state (airlock_ffi io)) init_env prog)` by
            metis_tac [SUBSET_DEF, IN_DEF]
       \\ qpat_x_assum `b ∈ extend_with_resource_limit _` mp_tac
       \\ simp [semanticsPropsTheory.extend_with_resource_limit_def]
       \\ rpt strip_tac \\ fs [IN_DEF]
       \\ qpat_x_assum `∀b. semantics_prog _ _ _ b ⇒ _`
            (fn ih => qpat_x_assum `semantics_prog _ _ _ _` (strip_assume_tac o MATCH_MP ih))
       \\ rveq \\ fs []
       \\ metis_tac [stop_after_err_al_prefix, boot_first_once_al_prefix, sent_frames128_of_prefix])
  \\ rpt conj_tac
  >- simp [Abbr `rmc`, real_mc_def]
  >- simp []
  >- (qpat_x_assum `¬machine_sem rmc _ _ Fail` mp_tac \\ simp [targetSemTheory.machine_sem_def])
  >- (
    qspecl_then [`rmc`, `airlock_ffi io`, `ms1`] strip_assume_tac
      (Q.GENL [`mc`, `st`, `ms`] targetPropsTheory.machine_sem_total)
    \\ first_x_assum drule \\ strip_tac \\ rveq
    \\ qpat_x_assum `machine_sem rmc _ _ (Terminate _ _)` mp_tac
    \\ simp [targetSemTheory.machine_sem_def] \\ strip_tac
    \\ metis_tac [])
  \\ rpt gen_tac \\ strip_tac
  \\ `machine_sem rmc (airlock_ffi io) ms1 (Terminate t st_end.io_events)` by
       (simp [targetSemTheory.machine_sem_def] \\ metis_tac [])
  \\ first_x_assum drule \\ strip_tac \\ fs []
QED

(* ---- 3. Single-Step Real-Bits Evaluation & 4-FFI Oracle Helpers ---- *)

Theorem shift_mk_real_m3_ffi_if[local]:
  ∀cb_begin cb_end bm_end P.
    shift_seq 1 (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P) =
    mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + 1))
Proof
  rpt gen_tac
  \\ simp [FUN_EQ_THM, pairTheory.FORALL_PROD, miscTheory.shift_seq_def, mk_real_m3_ffi_if_slot_def]
QED

Theorem mk_real_m3_ffi_if_pc[local]:
  ∀cb_begin cb_end bm_end P k idx new_bs s.
    (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P k (idx, new_bs, s)).PC = s.REG 30w
Proof
  rpt gen_tac \\ simp [mk_real_m3_ffi_if_slot_def]
  \\ IF_CASES_TAC
  >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [m3_ffi_return_ok_slot_def])
  \\ simp [forge_canonical_ffi_post_def]
QED

Theorem mk_real_m3_ffi_if_select[local]:
  ∀cb_begin cb_end bm_end P k idx new_bs s s_tgt.
    (∀s'. P k idx new_bs s s' ⇔ s' = s_tgt) ∧
    m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_tgt ⇒
    mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P k (idx, new_bs, s) = s_tgt
Proof
  rpt strip_tac \\ simp [mk_real_m3_ffi_if_slot_def]
  \\ SELECT_ELIM_TAC \\ simp []
QED

Theorem airlock_ffi_call_bootload[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = airlock_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «bootload») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = airlock_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs))] ∧
      is_bootload_ev (IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs))) ∧
      sent_frames128_of ffi'.io_events = sent_frames128_of ffi.io_events ∧
      ffi'.ffi_state = ffi.ffi_state ∧
      (LENGTH bytes2 < 545 ⇒ new_bs = bytes2) ∧
      (545 ≤ LENGTH bytes2 ∧
       (ffi.ffi_state.boot_fail ∨ LENGTH ffi.ffi_state.boot_key ≠ 32 ∨
        LENGTH ffi.ffi_state.slotA ≠ 256 ∨ LENGTH ffi.ffi_state.slotB ≠ 256) ⇒
         new_bs = 1w :: DROP 1 bytes2 ∧
         event_is_err_al (IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs)))) ∧
      (545 ≤ LENGTH bytes2 ∧ ¬ffi.ffi_state.boot_fail ∧
       LENGTH ffi.ffi_state.boot_key = 32 ∧ LENGTH ffi.ffi_state.slotA = 256 ∧
       LENGTH ffi.ffi_state.slotB = 256 ⇒
         new_bs = 0w :: ffi.ffi_state.boot_key ++ ffi.ffi_state.slotA ++ ffi.ffi_state.slotB ++ DROP 545 bytes2 ∧
         ¬event_is_err_al (IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs))))
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [airlock_ffi_oracle_def, ffi_bootload_def, is_bootload_ev_def]
  \\ (Cases_on `LENGTH bytes2 < 545` \\ simp [])
  >- simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP]
  \\ Cases_on `¬ffi.ffi_state.boot_fail ∧ LENGTH ffi.ffi_state.boot_key = 32 ∧
               LENGTH ffi.ffi_state.slotA = 256 ∧ LENGTH ffi.ffi_state.slotB = 256`
  >- (fs []
      \\ `LENGTH (0w :: ffi.ffi_state.boot_key ++ ffi.ffi_state.slotA ++ ffi.ffi_state.slotB ++ DROP 545 bytes2) =
          LENGTH bytes2` by simp []
      \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP, event_is_err_al_def]
      \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ Cases_on `bytes2` >- fs []
  \\ `LENGTH (1w :: t) = SUC (LENGTH t)` by simp []
  \\ `LENGTH ffi.ffi_state.boot_key = 32 ⇒ LENGTH ffi.ffi_state.slotA = 256 ⇒
      LENGTH ffi.ffi_state.slotB = 256 ⇒ ffi.ffi_state.boot_fail` by metis_tac []
  \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP,
           event_is_err_al_def, listTheory.ZIP]
  \\ rpt strip_tac \\ fs []
QED

Theorem airlock_ffi_call_send128[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = airlock_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «send128») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = airlock_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «send128») bytes (ZIP (bytes2, new_bs))] ∧
      ¬is_bootload_ev (IO_event (ExtCall «send128») bytes (ZIP (bytes2, new_bs))) ∧
      (LENGTH bytes2 < 129 ⇒
         new_bs = bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state ∧
         sent_frames128_of ffi'.io_events = sent_frames128_of ffi.io_events) ∧
      (129 ≤ LENGTH bytes2 ⇒
         let frame = TAKE 128 (DROP 1 bytes2) in
         sent_frames128_of ffi'.io_events = sent_frames128_of ffi.io_events ++ [frame] ∧
         (ffi.ffi_state.write_limit = NONE ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with outputs := ffi.ffi_state.outputs ++ [frame] ∧
            ¬event_is_err_al (IO_event (ExtCall «send128») bytes (ZIP (bytes2, new_bs)))) ∧
         (ffi.ffi_state.write_limit = SOME 0 ⇒
            new_bs = 1w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with outputs := ffi.ffi_state.outputs ++ [frame] ∧
            event_is_err_al (IO_event (ExtCall «send128») bytes (ZIP (bytes2, new_bs)))) ∧
         (∀d. ffi.ffi_state.write_limit = SOME (SUC d) ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with <| outputs := ffi.ffi_state.outputs ++ [frame];
                                                   write_limit := SOME d |>))
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [airlock_ffi_oracle_def, ffi_al_send128_def, is_bootload_ev_def]
  \\ (Cases_on `LENGTH bytes2 < 129` \\ simp [])
  >- simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP]
  \\ (Cases_on `ffi.ffi_state.write_limit` \\ simp [])
  >- (`LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
      \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.MAP_ZIP,
               listTheory.LENGTH_ZIP, event_is_err_al_def]
      \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ (Cases_on `x` \\ simp [])
  >- (`LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
      \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.MAP_ZIP,
               listTheory.LENGTH_ZIP, event_is_err_al_def]
      \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
  \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.MAP_ZIP, listTheory.LENGTH_ZIP]
QED

Theorem airlock_ffi_call_recv64[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = airlock_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «recv64») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = airlock_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs))] ∧
      ¬is_bootload_ev (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs))) ∧
      sent_frames128_of ffi'.io_events = sent_frames128_of ffi.io_events ∧
      (LENGTH bytes2 < 65 ⇒
         new_bs = bytes2 ∧ ffi'.ffi_state = ffi.ffi_state) ∧
      (65 ≤ LENGTH bytes2 ∧ ffi.ffi_state.inputs = [] ⇒
         new_bs = 1w :: DROP 1 bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state ∧
         event_is_err_al (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs)))) ∧
      (∀f fs. 65 ≤ LENGTH bytes2 ∧ ffi.ffi_state.inputs = f :: fs ∧ LENGTH f = 64 ⇒
         new_bs = 0w :: f ++ DROP 65 bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state with inputs := fs ∧
         ¬event_is_err_al (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs))))
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [airlock_ffi_oracle_def, ffi_al_recv64_def, is_bootload_ev_def]
  \\ (Cases_on `LENGTH bytes2 < 65` \\ simp [])
  >- simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP]
  \\ (Cases_on `ffi.ffi_state.inputs` \\ simp [])
  >- (`LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
      \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP, event_is_err_al_def]
      \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ (Cases_on `LENGTH h = 64` \\ simp [])
  >- (`LENGTH (0w :: h ++ DROP 65 bytes2) = LENGTH bytes2` by simp []
      \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP, event_is_err_al_def]
      \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ `LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
  \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP]
QED

Theorem airlock_ffi_call_commit[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = airlock_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «commit») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = airlock_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «commit») bytes (ZIP (bytes2, new_bs))] ∧
      ¬is_bootload_ev (IO_event (ExtCall «commit») bytes (ZIP (bytes2, new_bs))) ∧
      sent_frames128_of ffi'.io_events = sent_frames128_of ffi.io_events ∧
      (LENGTH bytes2 < 258 ⇒
         new_bs = bytes2 ∧ ffi'.ffi_state = ffi.ffi_state) ∧
      (258 ≤ LENGTH bytes2 ⇒
         let sel = EL 1 bytes2 in
         let rec = TAKE 256 (DROP 2 bytes2) in
         let io_upd = if (sel && 1w) = 0w then ffi.ffi_state with slotA := rec
                      else ffi.ffi_state with slotB := rec in
         (ffi.ffi_state.commit_limit = NONE ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = io_upd ∧
            ¬event_is_err_al (IO_event (ExtCall «commit») bytes (ZIP (bytes2, new_bs)))) ∧
         (ffi.ffi_state.commit_limit = SOME 0 ⇒
            new_bs = 1w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state ∧
            event_is_err_al (IO_event (ExtCall «commit») bytes (ZIP (bytes2, new_bs)))) ∧
         (∀d. ffi.ffi_state.commit_limit = SOME (SUC d) ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = io_upd with commit_limit := SOME d))
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [airlock_ffi_oracle_def, ffi_commit_def, is_bootload_ev_def]
  \\ (Cases_on `LENGTH bytes2 < 258` \\ simp [])
  >- simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP]
  \\ (Cases_on `ffi.ffi_state.commit_limit` \\ simp [])
  >- (`LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
      \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP, event_is_err_al_def]
      \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ (Cases_on `x` \\ simp [])
  >- (`LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
      \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP, event_is_err_al_def]
      \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
  \\ simp [sent_frames128_of_append, sent_frames128_of_def, listTheory.LENGTH_ZIP]
QED

Theorem m3_veneers_aligned_untagged[local]:
  aligned 2 FORGE_M3_EXIT_VENEER ∧ untagged FORGE_M3_EXIT_VENEER ∧
  aligned 2 FORGE_M3_INSTALL_VENEER ∧ untagged FORGE_M3_INSTALL_VENEER ∧
  aligned 2 FORGE_M3_FFIBOOT_VENEER ∧ untagged FORGE_M3_FFIBOOT_VENEER ∧
  aligned 2 FORGE_M3_FFISEND_VENEER ∧ untagged FORGE_M3_FFISEND_VENEER ∧
  aligned 2 FORGE_M3_FFIRECV_VENEER ∧ untagged FORGE_M3_FFIRECV_VENEER ∧
  aligned 2 FORGE_M3_FFICOMMIT_VENEER ∧ untagged FORGE_M3_FFICOMMIT_VENEER
Proof
  simp [FORGE_M3_EXIT_VENEER_def, FORGE_M3_INSTALL_VENEER_def,
        FORGE_M3_FFIBOOT_VENEER_def, FORGE_M3_FFISEND_VENEER_def,
        FORGE_M3_FFIRECV_VENEER_def, FORGE_M3_FFICOMMIT_VENEER_def, untagged_def]
  \\ EVAL_TAC
QED

Theorem m3_eval_step_cases[local]:
  ∀cb_begin cb_end bm_end B P ffi s.
    let rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = airlock_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ⇒
      (s.PC ∈ forge_m3_prog_addresses cb_end bm_end ⇒
         ¬is_svc0_at s ∧
         NextStateARM8 s = SOME (arm8$Next s) ∧
         arm8_ok (erase (arm8$Next s)) ∧ sp_ok (arm8$Next s) ∧
         bits_of (arm8$Next s) = B ∧
         m3_shim_loaded_slot cb_begin cb_end bm_end (arm8$Next s).MEM ∧
         (∀k. evaluate rmc ffi (SUC k) s = evaluate rmc ffi k (arm8$Next s))) ∧
      (s.PC = FORGE_M3_EXIT_VENEER ⇒
         ∀k. evaluate rmc ffi (SUC k) s =
             (if s.REG 0w = 0w then Halt Success else Halt Resource_limit_hit, s, ffi)) ∧
      (s.PC = FORGE_M3_FFIBOOT_VENEER ∨ s.PC = FORGE_M3_FFISEND_VENEER ∨
       s.PC = FORGE_M3_FFIRECV_VENEER ∨ s.PC = FORGE_M3_FFICOMMIT_VENEER ⇒
         ∃bytes bytes2.
           read_bytearray (s.REG 0w) (w2n (s.REG 1w))
             (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes ∧
           read_bytearray (s.REG 2w) (w2n (s.REG 3w))
             (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
           aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w)) ∧
      (s.PC ∈ forge_m3_prog_addresses cb_end bm_end ∨
       s.PC = FORGE_M3_EXIT_VENEER ∨ s.PC = FORGE_M3_INSTALL_VENEER ∨
       s.PC = FORGE_M3_FFIBOOT_VENEER ∨ s.PC = FORGE_M3_FFISEND_VENEER ∨
       s.PC = FORGE_M3_FFIRECV_VENEER ∨ s.PC = FORGE_M3_FFICOMMIT_VENEER)
Proof
  rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                          [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                          (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                          forge_real_install_if)`
  \\ strip_tac
  \\ drule m3_veneer_facts_slot \\ simp [] \\ strip_tac
  \\ drule m3_regions_disjoint_slot \\ strip_tac
  \\ rpt conj_tac
  >- (
    strip_tac
    \\ `s.PC ≠ FORGE_M3_EXIT_VENEER ∧ s.PC ≠ FORGE_M3_INSTALL_VENEER ∧
        s.PC ≠ FORGE_M3_FFIBOOT_VENEER ∧ s.PC ≠ FORGE_M3_FFISEND_VENEER ∧
        s.PC ≠ FORGE_M3_FFIRECV_VENEER ∧ s.PC ≠ FORGE_M3_FFICOMMIT_VENEER` by (rpt conj_tac \\ strip_tac \\ gvs [])
    \\ `SND (SND B) ⇒ aligned 4 s.SP_EL0` by
         (qpat_x_assum `bits_of s = B` (SUBST1_TAC o SYM) \\ fs [sp_ok_def, bits_of_def])
    \\ `encoded_bytes_in_mem arm8_config s.PC s.MEM (forge_m3_prog_addresses cb_end bm_end) ∧
        arm8_ok (erase (arm8$Next s)) ∧ bits_of (arm8$Next s) = B ∧
        (SND (SND B) ⇒ aligned 4 (arm8$Next s).SP_EL0) ∧
        (∀x. x ∉ forge_m3_prog_addresses cb_end bm_end ⇒ (arm8$Next s).MEM x = s.MEM x)` by (
         qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
         \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def]
         \\ Cases_on `encoded_bytes_in_mem arm8_config s.PC s.MEM (forge_m3_prog_addresses cb_end bm_end)` \\ simp []
         \\ Cases_on `((¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧ arm8_ok (erase (arm8$Next s)) ∧
                       bits_of (arm8$Next s) = B ∧ (¬SND (SND B) ∨ aligned 4 (arm8$Next s).SP_EL0)) ∧
                      (∀x. x ∉ forge_m3_prog_addresses cb_end bm_end ⇒ (arm8$Next s).MEM x = s.MEM x)` \\ simp []
         \\ Cases_on `SND (SND B)` \\ fs [])
    \\ rpt conj_tac
    >- (irule encoded_bytes_in_mem_not_svc0 \\ qexists_tac `forge_m3_prog_addresses cb_end bm_end` \\ simp [])
    >- (simp [arm8_stepTheory.NextStateARM8_def] \\ fs [arm8_ok_erase])
    >- simp []
    >- (fs [sp_ok_def, arm8_ok_erase] \\ Cases_on `(arm8$Next s).SCTLR_EL1.SA0` \\ simp []
        \\ qpat_x_assum `SND (SND B) ⇒ aligned 4 (arm8$Next s).SP_EL0` irule
        \\ qpat_x_assum `bits_of (arm8$Next s) = B` (SUBST1_TAC o SYM) \\ simp [bits_of_def])
    >- simp []
    >- (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM` \\ simp []
        \\ rpt strip_tac \\ first_x_assum irule
        \\ strip_tac \\ qpat_x_assum `∀a. a ∈ forge_m3_prog_addresses _ _ ⇒ a ∉ forge_m3_shim_code_region` (mp_tac o Q.SPEC `a`) \\ simp [])
    \\ gen_tac
    \\ `shift_seq 1 (K I) = (K I : num -> arm8_state -> arm8_state)` by
         simp [miscTheory.shift_seq_def, FUN_EQ_THM]
    \\ `(¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧ (¬SND (SND B) ∨ aligned 4 (arm8$Next s).SP_EL0)` by
         (Cases_on `SND (SND B)` \\ fs [])
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def, miscTheory.find_index_def])
  >- (
    strip_tac \\ gen_tac
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def])
  >- (
    disch_tac
    \\ `s.PC ∉ forge_m3_prog_addresses cb_end bm_end ∧
        s.PC ≠ FORGE_M3_EXIT_VENEER ∧ s.PC ≠ FORGE_M3_INSTALL_VENEER` by
         (qpat_assum `s.PC = FORGE_M3_FFIBOOT_VENEER ∨ _` (REPEAT_TCL DISJ_CASES_THEN (fn th => fs [th])))
    \\ `∃idx nm.
          find_index s.PC [FORGE_M3_FFIBOOT_VENEER; FORGE_M3_FFISEND_VENEER;
                           FORGE_M3_FFIRECV_VENEER; FORGE_M3_FFICOMMIT_VENEER] 0 = SOME idx ∧
          EL idx [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»] = ExtCall nm ∧
          (nm = «bootload» ∨ nm = «send128» ∨ nm = «recv64» ∨ nm = «commit»)` by
         (qpat_assum `s.PC = FORGE_M3_FFIBOOT_VENEER ∨ _` (REPEAT_TCL DISJ_CASES_THEN (fn th => simp [th, miscTheory.find_index_def])))
    \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `2` mp_tac)
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def,
             targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def]
    \\ Cases_on `read_bytearray (s.REG 0w) (w2n (s.REG 1w))
                   (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE)` \\ simp []
    \\ rename1 `read_bytearray (s.REG 0w) _ _ = SOME bytes`
    \\ Cases_on `read_bytearray (s.REG 2w) (w2n (s.REG 3w))
                   (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE)` \\ simp []
    \\ rename1 `read_bytearray (s.REG 2w) _ _ = SOME bytes2`
    \\ `∃ffi1 new_bs. call_FFI ffi (ExtCall nm) bytes bytes2 = FFI_return ffi1 new_bs` by (
         rveq
         \\ TRY (drule airlock_ffi_call_bootload \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac) \\ simp [] \\ NO_TAC)
         \\ TRY (drule airlock_ffi_call_send128 \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac) \\ simp [] \\ NO_TAC)
         \\ TRY (drule airlock_ffi_call_recv64 \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac) \\ simp [] \\ NO_TAC)
         \\ drule airlock_ffi_call_commit \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac) \\ simp [])
    \\ pop_assum strip_assume_tac \\ rveq \\ simp []
    \\ qabbrev_tac `ms1 = mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P 0 (idx, new_bs, s)`
    \\ `ms1.PC = s.REG 30w` by simp [Abbr `ms1`, mk_real_m3_ffi_if_pc]
    \\ simp [Once targetSemTheory.evaluate_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def]
    \\ (Cases_on `s.REG 30w = FORGE_M3_EXIT_VENEER` \\ simp [m3_veneers_aligned_untagged])
    \\ (Cases_on `s.REG 30w = FORGE_M3_INSTALL_VENEER` \\ simp [m3_veneers_aligned_untagged])
    \\ ((Cases_on `s.REG 30w ∈ forge_m3_prog_addresses cb_end bm_end` \\ simp [])
        >- (`s.REG 30w ≠ FORGE_M3_FFIBOOT_VENEER ∧ s.REG 30w ≠ FORGE_M3_FFISEND_VENEER ∧
             s.REG 30w ≠ FORGE_M3_FFIRECV_VENEER ∧ s.REG 30w ≠ FORGE_M3_FFICOMMIT_VENEER` by (rpt conj_tac \\ strip_tac \\ gvs [])
            \\ simp [miscTheory.find_index_def]
            \\ Cases_on `encoded_bytes_in_mem arm8_config (s.REG 30w) ms1.MEM (forge_m3_prog_addresses cb_end bm_end)` \\ simp []
            \\ Cases_on `arm8_ok (erase ms1)` \\ simp []
            \\ disch_tac
            \\ qpat_x_assum `arm8_ok (erase ms1)` mp_tac \\ simp [arm8_ok_erase]))
    \\ (Cases_on `s.REG 30w = FORGE_M3_FFIBOOT_VENEER` \\ simp [miscTheory.find_index_def, m3_veneers_aligned_untagged])
    \\ (Cases_on `s.REG 30w = FORGE_M3_FFISEND_VENEER` \\ simp [miscTheory.find_index_def, m3_veneers_aligned_untagged])
    \\ (Cases_on `s.REG 30w = FORGE_M3_FFIRECV_VENEER` \\ simp [miscTheory.find_index_def, m3_veneers_aligned_untagged])
    \\ (Cases_on `s.REG 30w = FORGE_M3_FFICOMMIT_VENEER` \\ simp [miscTheory.find_index_def, m3_veneers_aligned_untagged]))
  \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
  \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
           arm8_target_real_def, arm8_targetTheory.arm8_target_def]
  \\ Cases_on `s.PC ∈ forge_m3_prog_addresses cb_end bm_end` \\ simp []
  \\ Cases_on `s.PC = FORGE_M3_EXIT_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_M3_INSTALL_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_M3_FFIBOOT_VENEER` \\ simp [miscTheory.find_index_def]
  \\ Cases_on `s.PC = FORGE_M3_FFISEND_VENEER` \\ simp [miscTheory.find_index_def]
  \\ Cases_on `s.PC = FORGE_M3_FFIRECV_VENEER` \\ simp [miscTheory.find_index_def]
  \\ Cases_on `s.PC = FORGE_M3_FFICOMMIT_VENEER` \\ simp [miscTheory.find_index_def]
QED

(* Helper: stepping evaluate at any of the 4 FFI veneers yields an event extending io_events *)
Theorem m3_eval_ffi_event_mono[local]:
  ∀cb_begin cb_end bm_end B P ffi s ck t ms_end st_end.
    let rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = airlock_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ∧
      evaluate rmc ffi ck s = (Halt t, ms_end, st_end) ∧
      (s.PC = FORGE_M3_FFIBOOT_VENEER ∨ s.PC = FORGE_M3_FFISEND_VENEER ∨
       s.PC = FORGE_M3_FFIRECV_VENEER ∨ s.PC = FORGE_M3_FFICOMMIT_VENEER) ⇒
      ∃ev. (ffi.io_events ++ [ev]) ≼ st_end.io_events ∧
           (is_bootload_ev ev ⇔ s.PC = FORGE_M3_FFIBOOT_VENEER)
Proof
  rpt gen_tac \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                          [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                          (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                          forge_real_install_if)`
  \\ (Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def]))
  \\ rename1 `SUC ck'`
  \\ drule m3_veneer_facts_slot \\ simp [] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi`, `s`] mp_tac m3_eval_step_cases
  \\ simp [LET_THM]
  \\ strip_tac
  \\ `∃idx nm.
        find_index s.PC [FORGE_M3_FFIBOOT_VENEER; FORGE_M3_FFISEND_VENEER;
                         FORGE_M3_FFIRECV_VENEER; FORGE_M3_FFICOMMIT_VENEER] 0 = SOME idx ∧
        EL idx [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»] = ExtCall nm ∧
        (nm = «bootload» ⇔ s.PC = FORGE_M3_FFIBOOT_VENEER) ∧
        (nm = «bootload» ∨ nm = «send128» ∨ nm = «recv64» ∨ nm = «commit»)` by
       (simp [miscTheory.find_index_def] \\ fs [miscTheory.find_index_def])
  \\ `∃ffi' new_bs.
        call_FFI ffi (ExtCall nm) bytes bytes2 = FFI_return ffi' new_bs ∧
        ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall nm) bytes (ZIP (bytes2, new_bs))]` by (
       Cases_on `nm = «bootload»`
       >- (fs [] \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_bootload
           \\ (impl_tac >- simp []) \\ disch_then (qx_choosel_then [`ffi1`, `bs1`] strip_assume_tac)
           \\ qexists_tac `ffi1` \\ qexists_tac `bs1` \\ simp [])
       \\ Cases_on `nm = «send128»`
       >- (fs [] \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_send128
           \\ (impl_tac >- simp []) \\ disch_then (qx_choosel_then [`ffi1`, `bs1`] strip_assume_tac)
           \\ qexists_tac `ffi1` \\ qexists_tac `bs1` \\ simp [])
       \\ Cases_on `nm = «recv64»`
       >- (fs [] \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_recv64
           \\ (impl_tac >- simp []) \\ disch_then (qx_choosel_then [`ffi1`, `bs1`] strip_assume_tac)
           \\ qexists_tac `ffi1` \\ qexists_tac `bs1` \\ simp [])
       \\ `nm = «commit»` by fs [] \\ fs []
       \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_commit
       \\ (impl_tac >- simp []) \\ disch_then (qx_choosel_then [`ffi1`, `bs1`] strip_assume_tac)
       \\ qexists_tac `ffi1` \\ qexists_tac `bs1` \\ simp [])
  \\ `s.PC ∉ forge_m3_prog_addresses cb_end bm_end ∧
      s.PC ≠ FORGE_M3_EXIT_VENEER ∧ s.PC ≠ FORGE_M3_INSTALL_VENEER` by fs []
  \\ qabbrev_tac `rmc_next = real_mc B (forge_m3_mc_slot cb_end bm_end
                               [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                               (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + 1)))
                               forge_real_install_if)`
  \\ qabbrev_tac `s_next = mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P 0 (idx, new_bs, s)`
  \\ `evaluate rmc ffi (SUC ck') s = evaluate rmc_next ffi' ck' s_next` by (
       rveq
       \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
       \\ gvs [Abbr `rmc`, Abbr `rmc_next`, Abbr `s_next`, real_mc_def, forge_m3_mc_slot_def,
               arm8_target_real_def, arm8_targetTheory.arm8_target_def,
               targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
               targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
               shift_mk_real_m3_ffi_if])
  \\ `ffi'.io_events ≼ st_end.io_events` by (
       qspecl_then [`rmc_next`, `ffi'`, `ck'`, `s_next`] mp_tac targetPropsTheory.evaluate_io_events_mono
       \\ gvs [])
  \\ qexists_tac `IO_event (ExtCall nm) bytes (ZIP (bytes2, new_bs))`
  \\ gvs [is_bootload_ev_def]
QED

Theorem m3_post_err_ffi_contra[local]:
  ∀cb_begin cb_end bm_end B P ffi s ck t ms_end st_end.
    let rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = airlock_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ∧
      evaluate rmc ffi ck s = (Halt t, ms_end, st_end) ∧
      stop_after_err_al st_end.io_events ∧
      (∃e. MEM e ffi.io_events ∧ event_is_err_al e) ∧
      (s.PC = FORGE_M3_FFIBOOT_VENEER ∨ s.PC = FORGE_M3_FFISEND_VENEER ∨
       s.PC = FORGE_M3_FFIRECV_VENEER ∨ s.PC = FORGE_M3_FFICOMMIT_VENEER) ⇒
      F
Proof
  rpt gen_tac \\ ONCE_REWRITE_TAC [LET_THM] \\ BETA_TAC \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi`, `s`, `ck`, `t`, `ms_end`, `st_end`]
       (mp_tac o REWRITE_RULE [LET_THM]) m3_eval_ffi_event_mono
  \\ BETA_TAC \\ (impl_tac >- simp []) \\ strip_tac
  \\ qpat_x_assum `_ ≼ st_end.io_events` (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND])
  \\ rename1 `st_end.io_events = (ffi.io_events ++ [ev]) ++ rest`
  \\ `ffi.io_events ≼ st_end.io_events` by
       (simp [IS_PREFIX_APPEND] \\ qexists_tac `[ev] ++ rest` \\ simp [])
  \\ `st_end.io_events = ffi.io_events` by (irule stop_after_err_al_prefix_eq \\ metis_tac [])
  \\ qpat_x_assum `st_end.io_events = (ffi.io_events ++ [ev]) ++ rest` mp_tac
  \\ simp []
QED

Theorem m3_boot_order_ffi_contra[local]:
  ∀cb_begin cb_end bm_end B P ffi s ck t ms_end st_end.
    let rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = airlock_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ∧
      evaluate rmc ffi ck s = (Halt t, ms_end, st_end) ∧
      boot_first_once_al st_end.io_events ∧
      ((ffi.io_events = [] ∧
        (s.PC = FORGE_M3_FFISEND_VENEER ∨ s.PC = FORGE_M3_FFIRECV_VENEER ∨
         s.PC = FORGE_M3_FFICOMMIT_VENEER)) ∨
       (ffi.io_events ≠ [] ∧ s.PC = FORGE_M3_FFIBOOT_VENEER)) ⇒
      F
Proof
  rpt gen_tac \\ ONCE_REWRITE_TAC [LET_THM] \\ BETA_TAC
  \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ drule m3_veneer_facts_slot
  \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])
  \\ qpat_x_assum `_ ∨ _` (DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))
  >- (qpat_x_assum `s.PC = _ ∨ _` (REPEAT_TCL DISJ_CASES_THEN assume_tac)
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi`, `s`, `ck`, `t`, `ms_end`, `st_end`]
           (mp_tac o REWRITE_RULE [LET_THM]) m3_eval_ffi_event_mono
      \\ BETA_TAC \\ (impl_tac >- simp []) \\ strip_tac
      \\ `¬is_bootload_ev ev` by fs []
      \\ Cases_on `st_end.io_events` \\ gvs [boot_first_once_al_def])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi`, `s`, `ck`, `t`, `ms_end`, `st_end`]
       (mp_tac o REWRITE_RULE [LET_THM]) m3_eval_ffi_event_mono
  \\ BETA_TAC \\ (impl_tac >- simp []) \\ strip_tac
  \\ qspecl_then [`ffi.io_events`, `ev`, `st_end.io_events`] mp_tac boot_first_once_al_no_second_boot
  \\ fs []
QED

(* ---- 4. Forward Liveness under Error-Free 6-Syscall Linux Execution ---- *)

Definition noerr_m3_P_def:
  noerr_m3_P (cb_end:word64) (bm_end:word64)
             (key_in0:word8 list) (disk0:word8 list) (tail_bs:word8 list)
             (k:num) (idx:num) (new_bs:word8 list)
             (s:arm8_state) (s':arm8_state) ⇔
    (idx = 0 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 545 ⇒
          ∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
       (545 ≤ w2n (s.REG 3w) ∧ HD new_bs = 0w ⇒
          ∀os krest. os.key_in = TAKE 32 (DROP 1 new_bs) ++ krest ∧ os.disk = disk0 ⇒
            RTC (m3_whole_step F) (os, s) (os with key_in := krest, s')) ∧
       (545 ≤ w2n (s.REG 3w) ∧ HD new_bs ≠ 0w ⇒
          ∀os. os.key_in = key_in0 ⇒
            RTC (m3_whole_step F) (os, s) (os with key_in := [], s'))) ∨
    (idx = 1 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 129 ⇒
          ∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
       (129 ≤ w2n (s.REG 3w) ⇒
          ∀os. RTC (m3_whole_step F) (os, s) (os with out := os.out ++ TAKE 128 (DROP 1 bytes2), s'))) ∨
    (idx = 2 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 65 ⇒
          ∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
       (65 ≤ w2n (s.REG 3w) ∧ HD new_bs = 0w ⇒
          ∀os rest. os.inp = TAKE 64 (DROP 1 new_bs) ++ rest ⇒
            RTC (m3_whole_step F) (os, s) (os with inp := rest, s')) ∧
       (65 ≤ w2n (s.REG 3w) ∧ HD new_bs ≠ 0w ⇒
          ∀os. os.inp = tail_bs ⇒
            RTC (m3_whole_step F) (os, s) (os with inp := [], s'))) ∨
    (idx = 3 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 258 ⇒
          ∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
       (258 ≤ w2n (s.REG 3w) ⇒
          let sel = EL 1 bytes2 in
          let boff = if (sel && 1w) = 0w then 0 else 256 in
          let rec = TAKE 256 (DROP 2 bytes2) in
            ∀os. let d' = patch_bytes boff rec os.disk in
                   RTC (m3_whole_step F) (os, s) (os with <| disk := d'; durable := d' |>, s')))
End

Theorem noerr_m3_P_shift[local]:
  ∀cb_end bm_end key_in0 disk0 tail_bs.
    (λk. noerr_m3_P cb_end bm_end key_in0 disk0 tail_bs (k + 1)) =
    noerr_m3_P cb_end bm_end key_in0 disk0 tail_bs
Proof
  rpt gen_tac \\ simp [FUN_EQ_THM, noerr_m3_P_def]
QED

Theorem m3_liveness_post_err[local]:
  ∀ck cb_begin cb_end bm_end B P ffi s os t ms_end st_end.
    let rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = airlock_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ∧
      evaluate rmc ffi ck s = (Halt t, ms_end, st_end) ∧
      stop_after_err_al st_end.io_events ∧
      (∃e. MEM e ffi.io_events ∧ event_is_err_al e) ⇒
      ∃os_f ms_f ec.
        RTC (m3_whole_step F) (os, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f
Proof
  Induct_on `ck`
  >- (rpt gen_tac \\ simp [LET_THM] \\ strip_tac
      \\ qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
  \\ rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                          [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                          (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                          forge_real_install_if)`
  \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi`, `s`] mp_tac m3_eval_step_cases
  \\ simp [LET_THM]
  \\ strip_tac
  >- (
    qpat_x_assum `s.PC ∈ forge_m3_prog_addresses _ _ ⇒ _` mp_tac \\ impl_tac >- simp [] \\ strip_tac
    \\ `evaluate rmc ffi ck (arm8$Next s) = (Halt t, ms_end, st_end)` by fs []
    \\ `∀j. FST (evaluate rmc ffi j (arm8$Next s)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
    \\ qpat_x_assum `∀cb_begin cb_end bm_end B P ffi s. _`
         (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi`, `arm8$Next s`, `os`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ TRY (impl_tac >- (simp [Abbr `rmc`] \\ metis_tac [])) \\ strip_tac
    \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec` \\ simp []
    \\ ONCE_REWRITE_TAC [relationTheory.RTC_CASES1] \\ disj2_tac
    \\ qexists_tac `(os, arm8$Next s)` \\ simp [m3_whole_step_def])
  >- (
    qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`] mp_tac m3_cake_exit_to_svc_exit_group_slot
    \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `os` \\ qexists_tac `FUNPOW arm8$Next k s`
    \\ qexists_tac `if s.REG 0w = 0w then 0w else 1w`
    \\ simp [] \\ irule m3_det_run_imp_rtc \\ qexists_tac `k` \\ simp [])
  >- (
    qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`] mp_tac m3_cake_install_to_svc_exit_group_slot
    \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `os` \\ qexists_tac `FUNPOW arm8$Next 3 s` \\ qexists_tac `2w`
    \\ simp [] \\ irule m3_det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
  \\ (* All 4 FFI veneers contradict stop_after_err_al *)
     qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi`, `s`, `SUC ck`, `t`, `ms_end`, `st_end`]
       mp_tac m3_post_err_ffi_contra
  \\ simp [LET_THM, Abbr `rmc`] \\ metis_tac []
QED

Theorem mk_real_m3_ffi_if_exists[local]:
  ∀cb_begin cb_end bm_end P k idx new_bs s.
    (∃s_ex. P k idx new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex) ⇒
    P k idx new_bs s (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P k (idx, new_bs, s)) ∧
    m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s
      (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P k (idx, new_bs, s))
Proof
  rpt strip_tac \\ simp [mk_real_m3_ffi_if_slot_def]
  \\ (IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp []))
  \\ metis_tac []
QED

Theorem m3_liveness_eval_rtc[local]:
  ∀ck cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s os_cur t ms_end st_end.
    let rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end
                              (noerr_m3_P cb_end bm_end key_in0 disk0 tail_bs))
                           forge_real_install_if) in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      LENGTH tail_bs < 64 ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end s.MEM ∧
      ffi.oracle = airlock_ffi_oracle ∧
      ffi.ffi_state.commit_limit = NONE ∧
      ffi.ffi_state.write_limit = NONE ∧
      (ffi.io_events = [] ⇒
         os_cur.key_in = key_in0 ∧ os_cur.disk = disk0 ∧
         ¬ffi.ffi_state.boot_fail ∧
         ffi.ffi_state.boot_key = (if 32 ≤ LENGTH key_in0 then TAKE 32 key_in0 else []) ∧
         ffi.ffi_state.slotA = TAKE 256 (pad512 disk0) ∧
         ffi.ffi_state.slotB = DROP 256 (pad512 disk0)) ∧
      EVERY (λf. LENGTH f = 64) ffi.ffi_state.inputs ∧
      os_cur.inp = FLAT ffi.ffi_state.inputs ++ tail_bs ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ∧
      evaluate rmc ffi ck s = (Halt t, ms_end, st_end) ∧
      stop_after_err_al st_end.io_events ∧
      boot_first_once_al st_end.io_events ∧
      EVERY ($~ o event_is_err_al) ffi.io_events ⇒
      ∃os_f ms_f ec.
        RTC (m3_whole_step F) (os_cur, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f
Proof
  Induct_on `ck`
  >- (rpt gen_tac \\ simp [LET_THM] \\ strip_tac
      \\ qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
  \\ rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `P_ne = noerr_m3_P cb_end bm_end key_in0 disk0 tail_bs`
  \\ qabbrev_tac `rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                          [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                          (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P_ne)
                          forge_real_install_if)`
  \\ strip_tac
  \\ drule m3_veneer_facts_slot \\ simp [] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi`, `s`] mp_tac m3_eval_step_cases
  \\ simp [LET_THM]
  \\ strip_tac
  >- (
    (* Normal instruction *)
    qpat_x_assum `s.PC ∈ forge_m3_prog_addresses _ _ ⇒ _` mp_tac \\ impl_tac >- simp [] \\ strip_tac
    \\ `evaluate rmc ffi ck (arm8$Next s) = (Halt t, ms_end, st_end)` by fs []
    \\ `∀j. FST (evaluate rmc ffi j (arm8$Next s)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
    \\ qpat_x_assum `∀cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s. _`
         (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `key_in0`, `disk0`, `tail_bs`,
                       `ffi`, `arm8$Next s`, `os_cur`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ TRY (impl_tac >- simp [Abbr `rmc`, Abbr `P_ne`]) \\ strip_tac
    \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec` \\ simp []
    \\ ONCE_REWRITE_TAC [relationTheory.RTC_CASES1] \\ disj2_tac
    \\ qexists_tac `(os_cur, arm8$Next s)` \\ simp [m3_whole_step_def])
  >- (
    (* Exit veneer *)
    qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`] mp_tac m3_cake_exit_to_svc_exit_group_slot
    \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `os_cur` \\ qexists_tac `FUNPOW arm8$Next k s`
    \\ qexists_tac `if s.REG 0w = 0w then 0w else 1w`
    \\ simp [] \\ irule m3_det_run_imp_rtc \\ qexists_tac `k` \\ simp [])
  >- (
    (* Install veneer *)
    qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`] mp_tac m3_cake_install_to_svc_exit_group_slot
    \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `os_cur` \\ qexists_tac `FUNPOW arm8$Next 3 s` \\ qexists_tac `2w`
    \\ simp [] \\ irule m3_det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
  >- (
    (* bootload veneer: idx = 0 *)
    Cases_on `ffi.io_events ≠ []`
    >- (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi`, `s`, `SUC ck`, `t`, `ms_end`, `st_end`]
          mp_tac m3_boot_order_ffi_contra \\ simp [LET_THM, Abbr `rmc`])
    \\ `ffi.io_events = []` by fs []
    \\ `os_cur.key_in = key_in0 ∧ os_cur.disk = disk0 ∧ ¬ffi.ffi_state.boot_fail ∧
        ffi.ffi_state.boot_key = (if 32 ≤ LENGTH key_in0 then TAKE 32 key_in0 else []) ∧
        ffi.ffi_state.slotA = TAKE 256 (pad512 disk0) ∧
        ffi.ffi_state.slotB = DROP 256 (pad512 disk0)` by simp []
    \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
    \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
    \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_bootload
    \\ impl_tac >- simp [] \\ strip_tac
    \\ imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `s1 = mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P_ne 0 (0, new_bs, s)`
    \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
        (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
         `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
           gen_tac
           \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
           \\ simp [Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_m3_ffi_if, Abbr `P_ne`, noerr_m3_P_shift, Abbr `s1`])
         \\ conj_tac >- fs []
         \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
         \\ simp [])
    \\ Cases_on `w2n (s.REG 3w) < 545`
    >- (
      `∃s_ex. P_ne 0 0 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
         qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac m3_ffibootload_noerr_exists_slot
         \\ impl_tac >- simp [] \\ strip_tac
         \\ gvs [] \\ qexists_tac `s'` \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ qexists_tac `bytes2` \\ simp [])
      \\ `P_ne 0 0 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
           qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
           \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
      \\ `RTC (m3_whole_step F) (os_cur, s) (os_cur, s1)` by
           (qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def])
      \\ Cases_on `event_is_err_al (IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs)))`
      >- (qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi'`, `s1`, `os_cur`, `t`, `ms_end`, `st_end`]
            mp_tac m3_liveness_post_err \\ simp [LET_THM]
          \\ impl_tac >- (gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`] \\ metis_tac [])
          \\ strip_tac \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
          \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
      \\ qpat_x_assum `∀cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s. _`
           (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `key_in0`, `disk0`, `tail_bs`,
                         `ffi'`, `s1`, `os_cur`, `t`, `ms_end`, `st_end`] mp_tac)
      \\ simp [LET_THM] \\ impl_tac >- gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`, Abbr `P_ne`] \\ strip_tac
      \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
    \\ `545 ≤ LENGTH bytes2` by decide_tac
    \\ Cases_on `32 ≤ LENGTH key_in0`
    >- (
      qabbrev_tac `k32 = TAKE 32 key_in0`
      \\ `LENGTH k32 = 32 ∧ LENGTH (TAKE 256 (pad512 disk0)) = 256 ∧ LENGTH (DROP 256 (pad512 disk0)) = 256` by
           simp [Abbr `k32`, LENGTH_pad512]
      \\ `TAKE 256 (pad512 disk0) ++ DROP 256 (pad512 disk0) = pad512 disk0` by simp [listTheory.TAKE_DROP]
      \\ `new_bs = 0w :: k32 ++ pad512 disk0 ++ DROP 545 bytes2 ∧
          ¬event_is_err_al (IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs)))` by (
           fs [Abbr `k32`]
           \\ `k32 ++ TAKE 256 (pad512 disk0) ++ DROP 256 (pad512 disk0) ++ DROP 545 bytes2 =
               k32 ++ pad512 disk0 ++ DROP 545 bytes2` by
                simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC]
           \\ fs [Abbr `k32`])
      \\ `TAKE 32 (DROP 1 new_bs) = k32` by simp [listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt]
      \\ `∃s_ex. P_ne 0 0 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
           qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac m3_ffibootload_noerr_exists_slot
           \\ impl_tac >- simp [] \\ strip_tac
           \\ qpat_x_assum `∀key disk. 545 ≤ _ ∧ LENGTH key = 32 ⇒ _` (qspecl_then [`k32`, `disk0`] mp_tac)
           \\ impl_tac >- simp [] \\ strip_tac
           \\ qexists_tac `s'`
           \\ conj_tac >- simp [Abbr `P_ne`, noerr_m3_P_def, listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt]
           \\ qpat_x_assum `new_bs = _` SUBST1_TAC \\ first_assum ACCEPT_TAC)
      \\ `P_ne 0 0 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
           qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
           \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
      \\ `os_cur.key_in = k32 ++ DROP 32 key_in0` by simp [Abbr `k32`, listTheory.TAKE_DROP]
      \\ `RTC (m3_whole_step F) (os_cur, s) (os_cur with key_in := DROP 32 key_in0, s1)` by (
           qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ strip_tac
           \\ first_x_assum irule \\ simp [])
      \\ qpat_x_assum `∀cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s. _`
           (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `key_in0`, `disk0`, `tail_bs`,
                         `ffi'`, `s1`, `os_cur with key_in := DROP 32 key_in0`, `t`, `ms_end`, `st_end`] mp_tac)
      \\ simp [LET_THM] \\ impl_tac >- gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`, Abbr `P_ne`] \\ strip_tac
      \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
    \\ (* Short key_in0 -> bootload error -> halt via m3_liveness_post_err *)
       `LENGTH key_in0 < 32` by decide_tac
    \\ `new_bs = 1w :: DROP 1 bytes2 ∧
        event_is_err_al (IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs)))` by gvs []
    \\ `∃s_ex. P_ne 0 0 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
         qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac m3_ffibootload_noerr_exists_slot
         \\ impl_tac >- simp [] \\ strip_tac
         \\ qpat_x_assum `∀kshort. 545 ≤ _ ∧ LENGTH kshort < 32 ⇒ _` (qspec_then `key_in0` mp_tac)
         \\ impl_tac >- simp [] \\ strip_tac
         \\ qexists_tac `s'` \\ fs [Abbr `P_ne`, noerr_m3_P_def])
    \\ `P_ne 0 0 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
         qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
         \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
    \\ `RTC (m3_whole_step F) (os_cur, s) (os_cur with key_in := [], s1)` by
         (qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def])
    \\ qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi'`, `s1`,
                    `os_cur with key_in := []`, `t`, `ms_end`, `st_end`] mp_tac m3_liveness_post_err
    \\ simp [LET_THM] \\ impl_tac >- (gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`] \\ metis_tac [])
    \\ strip_tac \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  >- (
    (* send128 veneer: idx = 1 *)
    Cases_on `ffi.io_events = []`
    >- (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi`, `s`, `SUC ck`, `t`, `ms_end`, `st_end`]
          mp_tac m3_boot_order_ffi_contra \\ simp [LET_THM, Abbr `rmc`])
    \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
    \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
    \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac
         (SIMP_RULE (srw_ss()) [LET_THM] airlock_ffi_call_send128)
    \\ impl_tac >- simp [] \\ strip_tac
    \\ imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `s1 = mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P_ne 0 (1, new_bs, s)`
    \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
        (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
         `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
           gen_tac
           \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
           \\ simp [Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_m3_ffi_if, Abbr `P_ne`, noerr_m3_P_shift, Abbr `s1`])
         \\ conj_tac >- fs []
         \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
         \\ simp [])
    \\ `∃s_ex. P_ne 0 1 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
         qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac m3_ffisend128_noerr_exists_slot
         \\ impl_tac >- simp [] \\ strip_tac
         \\ Cases_on `w2n (s.REG 3w) < 129`
         >- (gvs [] \\ qexists_tac `s'` \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ qexists_tac `bytes2` \\ simp [])
         \\ `129 ≤ w2n (s.REG 3w)` by decide_tac
         \\ gvs [] \\ qexists_tac `s'` \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ qexists_tac `bytes2` \\ simp [])
    \\ `P_ne 0 1 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
         qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
         \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
    \\ `∃os_next. RTC (m3_whole_step F) (os_cur, s) (os_next, s1) ∧
                  os_next.inp = os_cur.inp ∧
                  ffi'.ffi_state.inputs = ffi.ffi_state.inputs ∧
                  ffi'.ffi_state.commit_limit = NONE ∧ ffi'.ffi_state.write_limit = NONE` by (
         Cases_on `w2n (s.REG 3w) < 129`
         >- (qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def]
             \\ strip_tac \\ qexists_tac `os_cur` \\ fs [])
         \\ `129 ≤ LENGTH bytes2` by decide_tac
         \\ qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def]
         \\ strip_tac \\ qexists_tac `os_cur with out := os_cur.out ++ TAKE 128 (DROP 1 bytes2)`
         \\ fs [])
    \\ Cases_on `event_is_err_al (IO_event (ExtCall «send128») bytes (ZIP (bytes2, new_bs)))`
    >- (qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi'`, `s1`, `os_next`, `t`, `ms_end`, `st_end`]
          mp_tac m3_liveness_post_err \\ simp [LET_THM]
        \\ impl_tac >- (gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`] \\ metis_tac [])
        \\ strip_tac \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
        \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
    \\ qpat_x_assum `∀cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s. _`
         (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `key_in0`, `disk0`, `tail_bs`,
                       `ffi'`, `s1`, `os_next`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ impl_tac >- gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`, Abbr `P_ne`] \\ strip_tac
    \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  >- (
    (* recv64 veneer: idx = 2 *)
    Cases_on `ffi.io_events = []`
    >- (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi`, `s`, `SUC ck`, `t`, `ms_end`, `st_end`]
          mp_tac m3_boot_order_ffi_contra \\ simp [LET_THM, Abbr `rmc`])
    \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
    \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
    \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_recv64
    \\ impl_tac >- simp [] \\ strip_tac
    \\ imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `s1 = mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P_ne 0 (2, new_bs, s)`
    \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
        (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
         `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
           gen_tac
           \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
           \\ simp [Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_m3_ffi_if, Abbr `P_ne`, noerr_m3_P_shift, Abbr `s1`])
         \\ conj_tac >- fs []
         \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
         \\ simp [])
    \\ Cases_on `w2n (s.REG 3w) < 65`
    >- (
      `∃s_ex. P_ne 0 2 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
         qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac m3_ffirecv64_noerr_exists_slot
         \\ impl_tac >- simp [] \\ strip_tac
         \\ gvs [] \\ qexists_tac `s'` \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ qexists_tac `bytes2` \\ simp [])
      \\ `P_ne 0 2 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
           qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
           \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
      \\ `RTC (m3_whole_step F) (os_cur, s) (os_cur, s1)` by
           (qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def])
      \\ Cases_on `event_is_err_al (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs)))`
      >- (qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi'`, `s1`, `os_cur`, `t`, `ms_end`, `st_end`]
            mp_tac m3_liveness_post_err \\ simp [LET_THM]
          \\ impl_tac >- (gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`] \\ metis_tac [])
          \\ strip_tac \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
          \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
      \\ qpat_x_assum `∀cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s. _`
           (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `key_in0`, `disk0`, `tail_bs`,
                         `ffi'`, `s1`, `os_cur`, `t`, `ms_end`, `st_end`] mp_tac)
      \\ simp [LET_THM] \\ impl_tac >- gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`, Abbr `P_ne`] \\ strip_tac
      \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
    \\ `65 ≤ LENGTH bytes2` by decide_tac
    \\ Cases_on `ffi.ffi_state.inputs`
    >- (
      `new_bs = 1w :: DROP 1 bytes2 ∧ ffi'.ffi_state = ffi.ffi_state ∧
       event_is_err_al (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs)))` by gvs []
      \\ `∃s_ex. P_ne 0 2 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
           qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac m3_ffirecv64_noerr_exists_slot
           \\ impl_tac >- simp [] \\ strip_tac
           \\ qpat_x_assum `∀tail_bs. 65 ≤ _ ∧ LENGTH tail_bs < 64 ⇒ _` (qspec_then `tail_bs` mp_tac)
           \\ impl_tac >- simp [] \\ strip_tac
           \\ qexists_tac `s'` \\ fs [Abbr `P_ne`, noerr_m3_P_def])
      \\ `P_ne 0 2 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
           qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
           \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
      \\ `RTC (m3_whole_step F) (os_cur, s) (os_cur with inp := [], s1)` by
           (qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ fs [])
      \\ qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi'`, `s1`,
                      `os_cur with inp := []`, `t`, `ms_end`, `st_end`] mp_tac m3_liveness_post_err
      \\ simp [LET_THM] \\ impl_tac >- (gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`] \\ metis_tac [])
      \\ strip_tac \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
    \\ rename1 `ffi.ffi_state.inputs = h :: rest_inps`
    \\ `LENGTH h = 64 ∧ EVERY (λf. LENGTH f = 64) rest_inps` by gvs []
    \\ `new_bs = 0w :: h ++ DROP 65 bytes2 ∧ ffi'.ffi_state = ffi.ffi_state with inputs := rest_inps ∧
        ¬event_is_err_al (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs)))` by (
         qpat_x_assum `∀f fs. _` (qspecl_then [`h`, `rest_inps`] mp_tac) \\ simp [])
    \\ `TAKE 64 (DROP 1 new_bs) = h` by simp [listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt]
    \\ `∃s_ex. P_ne 0 2 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
         qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac m3_ffirecv64_noerr_exists_slot
         \\ impl_tac >- simp [] \\ strip_tac
         \\ qpat_x_assum `∀f. 65 ≤ _ ∧ LENGTH f = 64 ⇒ _` (qspec_then `h` mp_tac)
         \\ impl_tac >- simp [] \\ strip_tac
         \\ qexists_tac `s'`
         \\ conj_tac >- simp [Abbr `P_ne`, noerr_m3_P_def, listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt]
         \\ qpat_x_assum `new_bs = _` SUBST1_TAC \\ first_assum ACCEPT_TAC)
    \\ `P_ne 0 2 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
         qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
         \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
    \\ `RTC (m3_whole_step F) (os_cur, s) (os_cur with inp := FLAT rest_inps ++ tail_bs, s1)` by (
         qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ strip_tac
         \\ first_x_assum irule \\ fs [])
    \\ qpat_x_assum `∀cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s. _`
         (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `key_in0`, `disk0`, `tail_bs`,
                       `ffi'`, `s1`, `os_cur with inp := FLAT rest_inps ++ tail_bs`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ impl_tac >- gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`, Abbr `P_ne`] \\ strip_tac
    \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  \\ (* commit veneer: idx = 3 *)
     Cases_on `ffi.io_events = []`
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi`, `s`, `SUC ck`, `t`, `ms_end`, `st_end`]
        mp_tac m3_boot_order_ffi_contra \\ simp [LET_THM, Abbr `rmc`])
  \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
  \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
  \\ qspecl_then [`ffi`, `bytes`, `bytes2`] mp_tac
       (SIMP_RULE (srw_ss()) [LET_THM] airlock_ffi_call_commit)
  \\ impl_tac >- simp [] \\ strip_tac
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `s1 = mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P_ne 0 (3, new_bs, s)`
  \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
      (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
       `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
         gen_tac
         \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc`, real_mc_def, forge_m3_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_m3_ffi_if, Abbr `P_ne`, noerr_m3_P_shift, Abbr `s1`])
       \\ conj_tac >- fs []
       \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
       \\ simp [])
  \\ `∃s_ex. P_ne 0 3 new_bs s s_ex ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s_ex` by (
       qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `s`, `bytes2`] mp_tac
         (SIMP_RULE (srw_ss()) [LET_THM] m3_fficommit_noerr_exists_slot)
       \\ impl_tac >- simp [] \\ strip_tac
       \\ Cases_on `w2n (s.REG 3w) < 258`
       >- (gvs [] \\ qexists_tac `s'` \\ simp [Abbr `P_ne`, noerr_m3_P_def] \\ qexists_tac `bytes2` \\ simp [])
       \\ `258 ≤ w2n (s.REG 3w)` by decide_tac
       \\ gvs [] \\ qexists_tac `s'` \\ simp [Abbr `P_ne`, noerr_m3_P_def, LET_THM] \\ qexists_tac `bytes2` \\ simp [])
  \\ `P_ne 0 3 new_bs s s1 ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_end new_bs s s1` by (
       qpat_x_assum `Abbrev (s1 = _)` (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
       \\ irule mk_real_m3_ffi_if_exists \\ qexists_tac `s_ex` \\ simp [])
  \\ `∃os_next. RTC (m3_whole_step F) (os_cur, s) (os_next, s1) ∧
                os_next.inp = os_cur.inp ∧
                ffi'.ffi_state.inputs = ffi.ffi_state.inputs ∧
                ffi'.ffi_state.commit_limit = NONE ∧ ffi'.ffi_state.write_limit = NONE` by (
       Cases_on `w2n (s.REG 3w) < 258`
       >- (qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def]
           \\ strip_tac \\ qexists_tac `os_cur` \\ fs [])
       \\ `258 ≤ LENGTH bytes2` by decide_tac
       \\ qpat_x_assum `P_ne _ _ _ _ _` mp_tac \\ simp [Abbr `P_ne`, noerr_m3_P_def, LET_THM]
       \\ strip_tac
       \\ qabbrev_tac `d' = patch_bytes (if (EL 1 bytes2 && 1w) = 0w then 0 else 256)
                                        (TAKE 256 (DROP 2 bytes2)) os_cur.disk`
       \\ qexists_tac `os_cur with <| disk := d'; durable := d' |>`
       \\ fs [Abbr `d'`] \\ Cases_on `(EL 1 bytes2 && 1w) = 0w` \\ fs [])
  \\ Cases_on `event_is_err_al (IO_event (ExtCall «commit») bytes (ZIP (bytes2, new_bs)))`
  >- (qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `B`, `P_ne`, `ffi'`, `s1`, `os_next`, `t`, `ms_end`, `st_end`]
        mp_tac m3_liveness_post_err \\ simp [LET_THM]
      \\ impl_tac >- (gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`] \\ metis_tac [])
      \\ strip_tac \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  \\ qpat_x_assum `∀cb_begin cb_end bm_end B key_in0 disk0 tail_bs ffi s. _`
       (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `key_in0`, `disk0`, `tail_bs`,
                     `ffi'`, `s1`, `os_next`, `t`, `ms_end`, `st_end`] mp_tac)
  \\ simp [LET_THM] \\ impl_tac >- gvs [m3_ffi_return_ok_slot_def, Abbr `rmc`, Abbr `P_ne`] \\ strip_tac
  \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
  \\ simp [] \\ metis_tac [relationTheory.RTC_RTC]
QED

(* ---- 5. Universal Safety & Exactness over All 6-Syscall OS Behaviors ---- *)

Definition mk_prefix_m3_P_def:
  mk_prefix_m3_P (posts:arm8_state list) (k:num) (idx:num) (bs:word8 list)
                 (s:arm8_state) (s':arm8_state) ⇔
    k < LENGTH posts ∧ s' = EL k posts
End

Theorem m3_post_err_nrc_safety[local]:
  ∀n cb_begin cb_end bm_end allow_err B P ffi_cur s_cur os_cur os_f ms_f ec ck t ms_end st_end.
    let rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                           forge_real_install_if) in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      arm8_ok (erase s_cur) ∧ sp_ok s_cur ∧ bits_of s_cur = B ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end s_cur.MEM ∧
      ffi_cur.oracle = airlock_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi_cur j s_cur) ≠ Error) ∧
      evaluate rmc ffi_cur ck s_cur = (Halt t, ms_end, st_end) ∧
      stop_after_err_al st_end.io_events ∧
      (∃e. MEM e ffi_cur.io_events ∧ event_is_err_al e) ∧
      NRC (m3_whole_step allow_err) n (os_cur, s_cur) (os_f, ms_f) ∧
      svc_exit_group_rel ec ms_f ⇒
      os_f.out = os_cur.out ∧
      (ec = 0w ∨ ec = 1w ∨ ec = 2w) ∧
      (ec = 0w ⇒ t = Success ∧ st_end.io_events = ffi_cur.io_events)
Proof
  completeInduct_on `n` \\ rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_m3_mc_slot cb_end bm_end
                          [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                          (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                          forge_real_install_if)`
  \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi_cur`, `s_cur`] mp_tac m3_eval_step_cases
  \\ simp [LET_THM]
  \\ strip_tac
  >- (
    qpat_x_assum `s_cur.PC ∈ forge_m3_prog_addresses _ _ ⇒ _` mp_tac \\ impl_tac >- simp [] \\ strip_tac
    \\ Cases_on `n` >- gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def]
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, m3_whole_step_def, is_svc0_at_def]
    \\ strip_tac
    \\ Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ `evaluate rmc ffi_cur ck' (arm8$Next s_cur) = (Halt t, ms_end, st_end)` by fs []
    \\ `∀j. FST (evaluate rmc ffi_cur j (arm8$Next s_cur)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi_cur j s_cur) ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
    \\ qpat_x_assum `∀m. m < SUC _ ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `allow_err`, `B`, `P`, `ffi_cur`, `arm8$Next s_cur`,
                                `os_cur`, `os_f`, `ms_f`, `ec`, `ck'`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ TRY (impl_tac >- (simp [Abbr `rmc`] \\ metis_tac [])) \\ simp [])
  >- (
    drule_all m3_cake_exit_universal_slot \\ strip_tac
    \\ Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ qpat_x_assum `s_cur.PC = FORGE_M3_EXIT_VENEER ⇒ _` mp_tac
    \\ impl_tac >- simp [] \\ disch_then (qspec_then `ck'` assume_tac)
    \\ Cases_on `s_cur.REG 0w = 0w` \\ fs [])
  >- (drule_all m3_cake_install_universal_slot \\ strip_tac \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `B`, `P`, `ffi_cur`, `s_cur`, `ck`, `t`, `ms_end`, `st_end`]
       mp_tac m3_post_err_ffi_contra
  \\ simp [LET_THM, Abbr `rmc`] \\ metis_tac []
QED

Theorem m3_pre_err_nrc_safety[local]:
  ∀n (recf:word8 list -> word8 list -> word8 list -> 'st)
     (stepf:word8 list -> 'st -> frame64 -> 'st # frame128 # bool)
     prog code data info oracle allow_err ms0 os0
     boot_done r w c sA_cur sB_cur os_cur s_cur os_f ms_f ec posts sent_so_far step_cnt.
    let cb_begin = m3_slot_cb_begin (LENGTH code) in
    let cb_end = m3_slot_cb_end (LENGTH code) in
    let bm_end = slot_bm_buf_end (LENGTH data) in
    let bk0 = if 32 ≤ LENGTH os0.key_in then TAKE 32 os0.key_in else [] in
    let sA0 = TAKE 256 (pad512 os0.disk) in
    let sB0 = DROP 256 (pad512 os0.disk) in
    let exp_all = if 32 ≤ LENGTH os0.key_in then
                    SND (airlock_exec stepf bk0 (recf bk0 sA0 sB0) (chunks64 os0.inp) NONE NONE)
                  else [] in
    backend$compile arm8_config (set_oracle arm8_backend_config oracle) prog = SOME (code, data, info) ∧
    prog_syntax_ok prog ∧
    info.lab_conf.shmem_extra = [] ∧
    ffinames_to_string_list (the [] info.lab_conf.ffi_names) =
      [«bootload»; «send128»; «recv64»; «commit»] ∧
    (∀io0:airlock_io.
       io0.outputs = [] ⇒
       sem_satisfies
         (semantics_dec_list (init_state (airlock_ffi io0)) init_env prog)
         (λb. ∃io_events.
                b = Terminate Success io_events ∧
                stop_after_err_al io_events ∧
                boot_first_once_al io_events ∧
                sent_frames128_of io_events =
                  if ¬io0.boot_fail ∧ LENGTH io0.boot_key = 32 ∧
                     LENGTH io0.slotA = 256 ∧ LENGTH io0.slotB = 256 then
                    SND (airlock_exec stepf io0.boot_key
                           (recf io0.boot_key io0.slotA io0.slotB)
                           io0.inputs io0.commit_limit io0.write_limit)
                  else [])) ∧
    forge_m3_slot_loaded code data ms0 ∧
    os0.inp = FLAT (TAKE r (chunks64 os0.inp)) ++ os_cur.inp ∧
    r ≤ LENGTH (chunks64 os0.inp) ∧
    LENGTH sent_so_far = w ∧
    FLAT sent_so_far = os_cur.out ∧
    (¬boot_done ⇒
       os_cur.key_in = os0.key_in ∧ os_cur.disk = os0.disk ∧
       sA_cur = sA0 ∧ sB_cur = sB0 ∧ sent_so_far = []) ∧
    arm8_ok (erase s_cur) ∧ sp_ok s_cur ∧ bits_of s_cur = bits_of ms0 ∧
    m3_shim_loaded_slot cb_begin cb_end bm_end s_cur.MEM ∧
    (∀bfail extra_in clim_rem wlim_rem P.
       (boot_done ⇒ ¬bfail) ∧
       (∀j. j < LENGTH posts ⇒ ∀idx bs s s'. P j idx bs s s' ⇔ s' = EL j posts) ⇒
       let io = <| boot_key := bk0; boot_fail := bfail; slotA := sA0; slotB := sB0;
                   inputs := TAKE r (chunks64 os0.inp) ++ extra_in;
                   outputs := [];
                   commit_limit := OPTION_MAP (λd. c + d) clim_rem;
                   write_limit := OPTION_MAP (λd. w + d) wlim_rem |> in
       let rmc0 = real_mc (bits_of ms0)
                    (forge_m3_mc_slot cb_end bm_end
                       [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                       (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P)
                       forge_real_install_if) in
       let rmc_cur = real_mc (bits_of ms0)
                       (forge_m3_mc_slot cb_end bm_end
                          [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                          (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                          forge_real_install_if) in
       ∃ffi_cur.
         ffi_cur.oracle = airlock_ffi_oracle ∧
         ffi_cur.ffi_state = <| boot_key := bk0; boot_fail := bfail;
                                slotA := sA_cur; slotB := sB_cur;
                                inputs := extra_in; outputs := sent_so_far;
                                commit_limit := clim_rem; write_limit := wlim_rem |> ∧
         (ffi_cur.io_events = [] ⇔ ¬boot_done) ∧
         sent_frames128_of ffi_cur.io_events = sent_so_far ∧
         (∀k. evaluate rmc0 (airlock_ffi io) (step_cnt + k) (FUNPOW arm8$Next 43 ms0) =
              evaluate rmc_cur ffi_cur k s_cur)) ∧
    NRC (m3_whole_step allow_err) n (os_cur, s_cur) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (ec = 0w ∨ ec = 1w ∨ ec = 2w) ∧
    os_f.out ≼ FLAT exp_all ∧
    (¬allow_err ∧ ec = 0w ⇒ os_f.out = FLAT exp_all)
Proof
  completeInduct_on `n` \\ rpt gen_tac \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `cb_begin = m3_slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = m3_slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ qabbrev_tac `bk0 = if 32 ≤ LENGTH os0.key_in then TAKE 32 os0.key_in else []`
  \\ qabbrev_tac `sA0 = TAKE 256 (pad512 os0.disk)`
  \\ qabbrev_tac `sB0 = DROP 256 (pad512 os0.disk)`
  \\ qabbrev_tac `exp_all = if 32 ≤ LENGTH os0.key_in then
                              SND (airlock_exec stepf bk0 (recf bk0 sA0 sB0) (chunks64 os0.inp) NONE NONE)
                            else []`
  \\ `(if 32 ≤ LENGTH os0.key_in then
         SND (airlock_exec stepf (TAKE 32 os0.key_in) (recf (TAKE 32 os0.key_in) sA0 sB0) (chunks64 os0.inp) NONE NONE)
       else []) = exp_all` by (Cases_on `32 ≤ LENGTH os0.key_in` \\ simp [Abbr `exp_all`, Abbr `bk0`])
  \\ pop_assum SUBST1_TAC
  \\ `LENGTH sA0 = 256 ∧ LENGTH sB0 = 256 ∧ (LENGTH bk0 = 32 ⇔ 32 ≤ LENGTH os0.key_in)` by
       (simp [Abbr `sA0`, Abbr `sB0`, Abbr `bk0`, LENGTH_pad512] \\ rw [])
  \\ `m3_slot_layout_ok cb_begin cb_end bm_end` by (
       qpat_x_assum `forge_m3_slot_loaded _ _ _` mp_tac
       \\ simp [forge_m3_slot_loaded_def, LET_THM] \\ strip_tac
       \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac m3_slot_params_props
       \\ simp [LET_THM])
  \\ drule m3_veneer_facts_slot \\ simp [] \\ strip_tac
  \\ qabbrev_tac `P0 = mk_prefix_m3_P posts`
  \\ `∀j. j < LENGTH posts ⇒ ∀idx bs s s'. P0 j idx bs s s' ⇔ s' = EL j posts` by
       simp [Abbr `P0`, mk_prefix_m3_P_def]
  \\ `∃ffi0.
        let io0 = <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                     inputs := chunks64 os0.inp; outputs := [];
                     commit_limit := NONE; write_limit := NONE |> in
        let rmc0 = real_mc (bits_of ms0)
                     (forge_m3_mc_slot cb_end bm_end
                        [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                        (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0)
                        forge_real_install_if) in
        let rmc_c = real_mc (bits_of ms0)
                      (forge_m3_mc_slot cb_end bm_end
                         [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                         (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
                         forge_real_install_if) in
        ffi0.oracle = airlock_ffi_oracle ∧
        ffi0.ffi_state = <| boot_key := bk0; boot_fail := F; slotA := sA_cur; slotB := sB_cur;
                            inputs := chunks64 os_cur.inp; outputs := sent_so_far;
                            commit_limit := NONE; write_limit := NONE |> ∧
        (ffi0.io_events = [] ⇔ ¬boot_done) ∧
        sent_frames128_of ffi0.io_events = sent_so_far ∧
        (∀k. evaluate rmc0 (airlock_ffi io0) (step_cnt + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate rmc_c ffi0 k s_cur) ∧
        (∀j. FST (evaluate rmc_c ffi0 j s_cur) ≠ Error)` by (
       drule_all m3_chunks64_drop_eq \\ strip_tac
       \\ qpat_x_assum `chunks64 os0.inp = _` (assume_tac o SYM)
       \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
            (qspecl_then [`F`, `chunks64 os_cur.inp`, `NONE`, `NONE`, `P0`] mp_tac)
       \\ impl_tac >- simp []
       \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
       \\ qexists_tac `ffi_cur`
       \\ `∀k. evaluate (real_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                   (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0) forge_real_install_if))
              (airlock_ffi <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                              inputs := chunks64 os0.inp; outputs := [];
                              commit_limit := NONE; write_limit := NONE |>)
              (step_cnt + k) (FUNPOW arm8$Next 43 ms0) =
              evaluate (real_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                   (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
                   forge_real_install_if))
              ffi_cur k s_cur` by (
            qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = _` mp_tac \\ simp [])
       \\ simp [LET_THM]
       \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                       `ms0`, `<| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                                  inputs := chunks64 os0.inp; outputs := [];
                                  commit_limit := NONE; write_limit := NONE |>`,
                       `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0`,
                       `forge_real_install_if`] mp_tac m3_compile_exact
       \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok] \\ strip_tac
       \\ gen_tac
       \\ qpat_x_assum `∀j. FST (evaluate _ _ j _) ≠ Error` (qspec_then `step_cnt + j` mp_tac) \\ simp [])
  \\ pop_assum (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`, `λk. P0 (k + LENGTH posts)`, `ffi0`, `s_cur`]
       mp_tac m3_eval_step_cases
  \\ simp [LET_THM] \\ strip_tac
  >- (
    (* Case 1: Normal instruction *)
    qpat_x_assum `s_cur.PC ∈ forge_m3_prog_addresses _ _ ⇒ _` mp_tac \\ impl_tac >- simp [] \\ strip_tac
    \\ Cases_on `n` >- gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def]
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, m3_whole_step_def, is_svc0_at_def]
    \\ strip_tac
    \\ qpat_x_assum `∀m. m < SUC n' ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                `allow_err`, `ms0`, `os0`, `boot_done`, `r`, `w`, `c`,
                                `sA_cur`, `sB_cur`, `os_cur`, `arm8$Next s_cur`,
                                `os_f`, `ms_f`, `ec`, `posts`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      simp [] \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
           (qspecl_then [`bfail`, `extra_in`, `clim_rem`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- simp []
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ qexists_tac `ffi_cur` \\ simp []
      \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                      `ms0`, `<| boot_key := bk0; boot_fail := bfail; slotA := sA0; slotB := sB0;
                                 inputs := TAKE r (chunks64 os0.inp) ++ extra_in; outputs := [];
                                 commit_limit := OPTION_MAP (λd. c + d) clim_rem;
                                 write_limit := OPTION_MAP (λd. w + d) wlim_rem |>`,
                      `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P`,
                      `forge_real_install_if`] mp_tac m3_compile_exact
      \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok]
      \\ disch_then (assume_tac o cj 3)
      \\ `∀j. FST (evaluate (real_mc (bits_of ms0)
                      (forge_m3_mc_slot cb_end bm_end
                         [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                         (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                         forge_real_install_if))
                    ffi_cur j s_cur) ≠ Error` by
           (gen_tac \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + j` mp_tac) \\ simp [])
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`, `λk. P (k + LENGTH posts)`, `ffi_cur`, `s_cur`]
           mp_tac m3_eval_step_cases
      \\ simp [LET_THM] \\ strip_tac
      \\ gen_tac
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp [Abbr `exp_all`, Abbr `bk0`])
  >- (
    (* Case 2: Exit veneer *)
    drule_all m3_cake_exit_universal_slot \\ strip_tac
    \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `<| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                               inputs := chunks64 os0.inp; outputs := [];
                               commit_limit := NONE; write_limit := NONE |>`,
                    `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0`,
                    `forge_real_install_if`] mp_tac m3_compile_exact
    \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok]
    \\ disch_then (assume_tac o cj 5)
    \\ `evaluate (real_mc (bits_of ms0)
          (forge_m3_mc_slot cb_end bm_end
             [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
             (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0) forge_real_install_if))
          (airlock_ffi <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                          inputs := chunks64 os0.inp; outputs := [];
                          commit_limit := NONE; write_limit := NONE |>)
          (step_cnt + 1) (FUNPOW arm8$Next 43 ms0) =
        (if s_cur.REG 0w = 0w then Halt Success else Halt Resource_limit_hit, s_cur, ffi0)` by
         (qpat_x_assum `s_cur.PC = FORGE_M3_EXIT_VENEER ⇒ _` mp_tac
          \\ impl_tac >- simp [] \\ disch_then (qspec_then `0` assume_tac)
          \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = _` (qspec_then `SUC 0` mp_tac)
          \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ qpat_x_assum `∀ck t ms_end st_end. _`
         (qspecl_then [`step_cnt + 1`,
                       `if s_cur.REG 0w = 0w then Success else Resource_limit_hit`,
                       `s_cur`, `ffi0`] mp_tac)
    \\ simp []
    \\ (Cases_on `s_cur.REG 0w = 0w` \\ simp [])
    >- (strip_tac \\ fs [Abbr `exp_all`, Abbr `bk0`])
    \\ strip_tac \\ qpat_x_assum `FLAT sent_so_far = os_cur.out` (SUBST1_TAC o SYM)
    \\ simp [] \\ irule m3_FLAT_prefix \\ fs [Abbr `exp_all`, Abbr `bk0`])
  >- (
    (* Case 3: Install veneer *)
    drule_all m3_cake_install_universal_slot \\ strip_tac
    \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `<| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                               inputs := chunks64 os0.inp; outputs := [];
                               commit_limit := NONE; write_limit := NONE |>`,
                    `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0`,
                    `forge_real_install_if`] mp_tac m3_compile_exact
    \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok] \\ strip_tac
    \\ `evaluate (real_mc (bits_of ms0)
          (forge_m3_mc_slot cb_end bm_end
             [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
             (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0) forge_real_install_if))
          (airlock_ffi <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                          inputs := chunks64 os0.inp; outputs := [];
                          commit_limit := NONE; write_limit := NONE |>)
          (step_cnt + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by
         (`step_cnt + ck = ck + step_cnt` by decide_tac \\ pop_assum SUBST1_TAC
          \\ irule targetPropsTheory.evaluate_add_clock \\ simp [])
    \\ `evaluate (real_mc (bits_of ms0)
          (forge_m3_mc_slot cb_end bm_end
             [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
             (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
             forge_real_install_if))
          ffi0 ck s_cur = (Halt t, ms_end, st_end)` by (
         pop_assum mp_tac
         \\ qpat_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi0 _ _` (qspec_then `ck` mp_tac)
         \\ simp [])
    \\ `ffi0.io_events ≼ st_end.io_events` by (
         qspecl_then [`real_mc (bits_of ms0)
                        (forge_m3_mc_slot cb_end bm_end
                           [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                           (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
                           forge_real_install_if)`,
                      `ffi0`, `ck`, `s_cur`] mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ simp [])
    \\ `sent_frames128_of ffi0.io_events ≼ sent_frames128_of st_end.io_events` by simp [sent_frames128_of_prefix]
    \\ `sent_frames128_of st_end.io_events ≼ exp_all` by fs [Abbr `exp_all`]
    \\ `sent_so_far ≼ exp_all` by
         (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `sent_frames128_of st_end.io_events`
          \\ qpat_x_assum `sent_frames128_of ffi0.io_events ≼ _` mp_tac \\ simp [])
    \\ qpat_x_assum `FLAT sent_so_far = os_cur.out` (SUBST1_TAC o SYM)
    \\ rveq \\ simp [m3_FLAT_prefix])
  >- (
    (* Case 4: bootload veneer (idx = 0) *)
    Cases_on `boot_done`
    >- (
      (* 2nd bootload contradicts boot_first_once_al *)
      qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                   `ms0`, `<| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                              inputs := chunks64 os0.inp; outputs := [];
                              commit_limit := NONE; write_limit := NONE |>`,
                   `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0`,
                   `forge_real_install_if`] mp_tac m3_compile_exact
      \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok] \\ strip_tac
      \\ `evaluate (real_mc (bits_of ms0)
            (forge_m3_mc_slot cb_end bm_end
               [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
               (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
               forge_real_install_if))
            ffi0 ck s_cur = (Halt t, ms_end, st_end)` by (
           `evaluate (real_mc (bits_of ms0)
              (forge_m3_mc_slot cb_end bm_end
                 [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                 (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0) forge_real_install_if))
              (airlock_ffi <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                              inputs := chunks64 os0.inp; outputs := [];
                              commit_limit := NONE; write_limit := NONE |>)
              (step_cnt + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by
                (`step_cnt + ck = ck + step_cnt` by decide_tac \\ pop_assum SUBST1_TAC
                 \\ irule targetPropsTheory.evaluate_add_clock \\ simp [])
           \\ pop_assum mp_tac
           \\ qpat_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi0 _ _` (qspec_then `ck` mp_tac)
           \\ simp [])
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`,
                      `λk. P0 (k + LENGTH posts)`, `ffi0`, `s_cur`, `ck`, `t`, `ms_end`, `st_end`]
           mp_tac m3_boot_order_ffi_contra
      \\ simp [LET_THM]
      \\ qpat_x_assum `ffi0.io_events = [] ⇔ _` mp_tac \\ simp [])
    \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
    \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
    \\ imp_res_tac read_bytearray_mem_eq
    \\ mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] m3_ffibootload_universal_slot)
                 (ASSUME ``m3_slot_layout_ok cb_begin cb_end bm_end``))
    \\ disch_then drule_all \\ strip_tac
    \\ Cases_on `w2n (s_cur.REG 3w) < 545`
    >- (
      (* Subcase 4a: short buffer < 545 *)
      first_x_assum drule \\ strip_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `os0`, `T`, `r`, `w`, `c`,
                                  `sA_cur`, `sB_cur`, `os_cur`, `s'`,
                                  `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [] \\ rpt conj_tac >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
             (qspecl_then [`F`, `extra_in`, `clim_rem`, `wlim_rem`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_bootload
        \\ impl_tac >- simp [] \\ strip_tac
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (0, bytes2, s_cur) = s'` by (
             irule mk_real_m3_ffi_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                     forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                     forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
             \\ simp [real_mc_def, forge_m3_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_m3_ffi_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ pop_assum SUBST1_TAC \\ simp [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [Abbr `exp_all`, Abbr `bk0`])
    \\ `545 ≤ w2n (s_cur.REG 3w)` by decide_tac
    \\ first_x_assum drule
    \\ disch_then (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS)))
    >- (
      (* Subcase 4b: bootload succeeded with 32B key + 512B disk *)
      `32 ≤ LENGTH os0.key_in ∧ key = bk0` by (
        `os0.key_in = key ++ krest` by fs []
        \\ `LENGTH os0.key_in = 32 + LENGTH krest` by simp []
        \\ simp [Abbr `bk0`, listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt])
      \\ `sA0 ++ sB0 = pad512 os0.disk` by simp [Abbr `sA0`, Abbr `sB0`, listTheory.TAKE_DROP]
      \\ `os_cur.disk = os0.disk ∧ sA_cur = sA0 ∧ sB_cur = sB0` by fs []
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `os0`, `T`, `r`, `w`, `c`,
                                  `sA_cur`, `sB_cur`, `os_cur with key_in := krest`, `s'`,
                                  `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [] \\ rpt conj_tac >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
             (qspecl_then [`F`, `extra_in`, `clim_rem`, `wlim_rem`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_bootload
        \\ impl_tac >- simp [] \\ strip_tac
        \\ `new_bs = 0w :: key ++ pad512 os_cur.disk ++ DROP 545 bytes2` by (
             `new_bs = 0w :: bk0 ++ sA0 ++ sB0 ++ DROP 545 bytes2` by fs []
             \\ pop_assum SUBST1_TAC
             \\ `bk0 ++ sA0 ++ sB0 ++ DROP 545 bytes2 = key ++ (sA0 ++ sB0) ++ DROP 545 bytes2` by
                  simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC]
             \\ simp [])
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (0, new_bs, s_cur) = s'` by (
             irule mk_real_m3_ffi_if_select
             \\ conj_tac
             >- (gen_tac \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
                 \\ simp [rich_listTheory.EL_LENGTH_APPEND])
             \\ qpat_x_assum `new_bs = _` SUBST1_TAC
             \\ first_assum ACCEPT_TAC)
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                     forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                     forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
             \\ simp [real_mc_def, forge_m3_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_m3_ffi_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ pop_assum SUBST1_TAC
             \\ qpat_x_assum `mk_real_m3_ffi_if_slot _ _ _ _ 0 (0, new_bs, s_cur) = s'` mp_tac
             \\ simp [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [Abbr `exp_all`, Abbr `bk0`])
    \\ (* Subcase 4c: bootload failed (short key_in or OS error) *)
       qabbrev_tac `P1 = mk_prefix_m3_P (posts ++ [s'])`
    \\ qabbrev_tac `bf = (32 ≤ LENGTH os0.key_in)`
    \\ drule_all m3_chunks64_drop_eq \\ strip_tac
    \\ qpat_x_assum `chunks64 os0.inp = _` (assume_tac o SYM)
    \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
         (qspecl_then [`bf`, `chunks64 os_cur.inp`, `NONE`, `NONE`, `P1`] mp_tac)
    \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_APPEND1])
    \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
    \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_bootload
    \\ impl_tac >- simp [] \\ strip_tac
    \\ `new_bs = 1w :: DROP 1 bytes2 ∧
        event_is_err_al (IO_event (ExtCall «bootload») bytes (ZIP (bytes2, new_bs)))` by (
         qpat_x_assum `545 ≤ LENGTH bytes2 ∧ _ ⇒ _` mp_tac
         \\ simp [Abbr `bf`, Abbr `bk0`]
         \\ Cases_on `32 ≤ LENGTH os0.key_in` \\ simp [])
    \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)) 0 (0, 1w :: DROP 1 bytes2, s_cur) = s'` by (
         irule mk_real_m3_ffi_if_select \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_LENGTH_APPEND])
    \\ qabbrev_tac `io_bf = <| boot_key := bk0; boot_fail := bf; slotA := sA0; slotB := sB0;
                               inputs := chunks64 os0.inp; outputs := [];
                               commit_limit := NONE; write_limit := NONE |>`
    \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0)
                             (forge_m3_mc_slot cb_end bm_end
                                [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                                (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1) forge_real_install_if)`
    \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                                 (forge_m3_mc_slot cb_end bm_end
                                    [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                                    (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + (LENGTH posts + 1))))
                                    forge_real_install_if)`
    \\ `∀k. evaluate rmc1 (airlock_ffi io_bf) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
            evaluate rmc_post ffi' k s'` by (
         gen_tac
         \\ `evaluate rmc1 (airlock_ffi io_bf) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate (real_mc (bits_of ms0)
               (forge_m3_mc_slot cb_end bm_end
                  [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                  (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)))
                  forge_real_install_if))
               ffi_cur (SUC k) s_cur` by (
              qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
              \\ simp [Abbr `io_bf`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
         \\ pop_assum SUBST1_TAC
         \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc_post`, real_mc_def, forge_m3_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_m3_ffi_if]
         \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
              (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
         \\ simp [])
    \\ `io_bf.outputs = []` by simp [Abbr `io_bf`]
    \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `io_bf`, `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1`,
                    `forge_real_install_if`] mp_tac m3_compile_exact
    \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok]
    \\ disch_then (fn th => assume_tac (cj 3 th) \\
         REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS) (cj 4 th))
    \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
         `evaluate rmc1 (airlock_ffi io_bf)
            (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
              `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
              \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
         \\ pop_assum mp_tac
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
         \\ simp [])
    \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
         gen_tac
         \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
         \\ simp [Abbr `rmc1`])
    \\ qspecl_then [`n'`, `cb_begin`, `cb_end`, `bm_end`, `allow_err`, `bits_of ms0`,
                    `λk. P1 (k + (LENGTH posts + 1))`, `ffi'`, `s'`,
                    `os_cur with key_in := krest`, `os_f`, `ms_f`, `ec`,
                    `ck`, `t`, `ms_end`, `st_end`] mp_tac m3_post_err_nrc_safety
    \\ simp [LET_THM]
    \\ (impl_tac >- (
         qpat_assum `m3_ffi_return_ok_slot _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [m3_ffi_return_ok_slot_def])
         \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
         \\ qpat_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
         \\ simp [Abbr `rmc_post`,
                  boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]
         \\ Cases_on `bytes2`
         >- (qpat_x_assum `LENGTH [] = _` mp_tac \\ simp [])
         \\ simp [event_is_err_al_def]))
    \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
    \\ `os_cur.out = []` by (
         qpat_x_assum `¬boot_done ⇒ _` mp_tac \\ simp [] \\ strip_tac
         \\ qpat_x_assum `FLAT sent_so_far = os_cur.out` mp_tac
         \\ simp [])
    \\ simp [Abbr `exp_all`]
    \\ rpt strip_tac
    \\ `LENGTH os0.key_in < 32` by (
         qpat_x_assum `¬boot_done ⇒ _` mp_tac \\ simp [] \\ strip_tac
         \\ qpat_x_assum `allow_err ∨ LENGTH os_cur.key_in < 32` mp_tac
         \\ simp [])
    \\ simp [Abbr `bf`])
  >- (
    (* Case 5: send128 veneer (idx = 1) *)
    Cases_on `¬boot_done`
    >- (
      qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                   `ms0`, `<| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                              inputs := chunks64 os0.inp; outputs := [];
                              commit_limit := NONE; write_limit := NONE |>`,
                   `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0`,
                   `forge_real_install_if`] mp_tac m3_compile_exact
      \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok] \\ strip_tac
      \\ `evaluate (real_mc (bits_of ms0)
            (forge_m3_mc_slot cb_end bm_end
               [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
               (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
               forge_real_install_if))
            ffi0 ck s_cur = (Halt t, ms_end, st_end)` by (
           `evaluate (real_mc (bits_of ms0)
              (forge_m3_mc_slot cb_end bm_end
                 [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                 (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0) forge_real_install_if))
              (airlock_ffi <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                              inputs := chunks64 os0.inp; outputs := [];
                              commit_limit := NONE; write_limit := NONE |>)
              (step_cnt + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by
                (`step_cnt + ck = ck + step_cnt` by decide_tac \\ pop_assum SUBST1_TAC
                 \\ irule targetPropsTheory.evaluate_add_clock \\ simp [])
           \\ pop_assum mp_tac
           \\ qpat_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi0 _ _` (qspec_then `ck` mp_tac)
           \\ simp [])
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`,
                      `λk. P0 (k + LENGTH posts)`, `ffi0`, `s_cur`, `ck`, `t`, `ms_end`, `st_end`]
           mp_tac m3_boot_order_ffi_contra
      \\ simp [LET_THM]
      \\ qpat_x_assum `ffi0.io_events = [] ⇔ _` mp_tac \\ simp [])
    \\ qpat_x_assum `¬¬boot_done` (assume_tac o REWRITE_RULE [])
    \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
    \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
    \\ imp_res_tac read_bytearray_mem_eq
    \\ mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] m3_ffisend128_universal_slot)
                 (ASSUME ``m3_slot_layout_ok cb_begin cb_end bm_end``))
    \\ disch_then drule_all \\ strip_tac
    \\ Cases_on `w2n (s_cur.REG 3w) < 129`
    >- (
      first_x_assum drule \\ strip_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `os0`, `T`, `r`, `w`, `c`,
                                  `sA_cur`, `sB_cur`, `os_cur`, `s'`,
                                  `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [] \\ rpt conj_tac >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
             (qspecl_then [`F`, `extra_in`, `clim_rem`, `wlim_rem`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
             (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] airlock_ffi_call_send128)
        \\ impl_tac >- simp [] \\ strip_tac
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (1, bytes2, s_cur) = s'` by (
             irule mk_real_m3_ffi_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                     forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                     forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
             \\ simp [real_mc_def, forge_m3_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_m3_ffi_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ pop_assum SUBST1_TAC \\ simp [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [Abbr `exp_all`, Abbr `bk0`])
    \\ `129 ≤ w2n (s_cur.REG 3w)` by decide_tac
    \\ first_x_assum drule \\ strip_tac
    >- (
      qabbrev_tac `frame = TAKE 128 (DROP 1 bytes2)`
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `os0`, `T`, `r`, `w + 1`, `c`,
                                  `sA_cur`, `sB_cur`, `os_cur with out := os_cur.out ++ frame`, `s'`,
                                  `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far ++ [frame]`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [listTheory.FLAT_APPEND] \\ rpt conj_tac >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qabbrev_tac `wlim_prev = OPTION_MAP SUC wlim_rem`
        \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
             (qspecl_then [`F`, `extra_in`, `clim_rem`, `wlim_prev`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])
        \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
             (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] airlock_ffi_call_send128)
        \\ impl_tac >- simp [] \\ strip_tac
        \\ `new_bs = 0w :: DROP 1 bytes2 ∧
            sent_frames128_of ffi'.io_events = sent_so_far ++ [frame] ∧
            ffi'.ffi_state = <| boot_key := bk0; boot_fail := F; slotA := sA_cur; slotB := sB_cur;
                                inputs := extra_in; outputs := sent_so_far ++ [frame];
                                commit_limit := clim_rem; write_limit := wlim_rem |>` by (
             qpat_x_assum `ffi'.io_events = _` (K ALL_TAC)
             \\ qpat_x_assum `129 ≤ LENGTH bytes2 ⇒ _` mp_tac
             \\ qpat_x_assum `ffi_cur.ffi_state = _` mp_tac
             \\ Cases_on `wlim_rem`
             \\ simp [Abbr `wlim_prev`, Abbr `frame`] \\ rpt strip_tac
             \\ simp [airlock_io_component_equality])
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (1, 0w :: DROP 1 bytes2, s_cur) = s'` by (
             irule mk_real_m3_ffi_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                     forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                     forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
             \\ simp [real_mc_def, forge_m3_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_m3_ffi_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ pop_assum SUBST1_TAC \\ simp [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ Cases_on `wlim_rem`
        \\ simp [Abbr `wlim_prev`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [Abbr `exp_all`, Abbr `bk0`])
    \\ (* Subcase 5c: partial/error write *)
       qabbrev_tac `frame = TAKE 128 (DROP 1 bytes2)`
    \\ qabbrev_tac `P1 = mk_prefix_m3_P (posts ++ [s'])`
    \\ drule_all m3_chunks64_drop_eq \\ strip_tac
    \\ qpat_x_assum `chunks64 os0.inp = _` (assume_tac o SYM)
    \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
         (qspecl_then [`F`, `chunks64 os_cur.inp`, `NONE`, `SOME 0`, `P1`] mp_tac)
    \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_APPEND1])
    \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
    \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
         (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] airlock_ffi_call_send128)
    \\ impl_tac >- simp [] \\ strip_tac
    \\ `new_bs = 1w :: DROP 1 bytes2 ∧
        sent_frames128_of ffi'.io_events = sent_so_far ++ [frame] ∧
        event_is_err_al (IO_event (ExtCall «send128») bytes (ZIP (bytes2, new_bs)))` by (
         qpat_x_assum `ffi'.io_events = _` (K ALL_TAC)
         \\ qpat_x_assum `129 ≤ LENGTH bytes2 ⇒ _` mp_tac
         \\ simp [Abbr `frame`] \\ strip_tac \\ simp [])
    \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)) 0 (1, 1w :: DROP 1 bytes2, s_cur) = s'` by (
         irule mk_real_m3_ffi_if_select \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_LENGTH_APPEND])
    \\ qabbrev_tac `io_err = <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                                inputs := chunks64 os0.inp; outputs := [];
                                commit_limit := NONE; write_limit := SOME w |>`
    \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0)
                             (forge_m3_mc_slot cb_end bm_end
                                [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                                (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1) forge_real_install_if)`
    \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                                 (forge_m3_mc_slot cb_end bm_end
                                    [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                                    (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + (LENGTH posts + 1))))
                                    forge_real_install_if)`
    \\ `∀k. evaluate rmc1 (airlock_ffi io_err) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
            evaluate rmc_post ffi' k s'` by (
         gen_tac
         \\ `evaluate rmc1 (airlock_ffi io_err) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate (real_mc (bits_of ms0)
               (forge_m3_mc_slot cb_end bm_end
                  [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                  (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)))
                  forge_real_install_if))
               ffi_cur (SUC k) s_cur` by (
              qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
              \\ simp [Abbr `io_err`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
         \\ pop_assum SUBST1_TAC
         \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc_post`, real_mc_def, forge_m3_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_m3_ffi_if]
         \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
              (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
         \\ simp [])
    \\ `io_err.outputs = []` by simp [Abbr `io_err`]
    \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `io_err`, `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1`,
                    `forge_real_install_if`] mp_tac m3_compile_exact
    \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok]
    \\ disch_then (fn th => assume_tac (cj 3 th) \\
         REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS) (cj 4 th))
    \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
         `evaluate rmc1 (airlock_ffi io_err)
            (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
              `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
              \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
         \\ pop_assum mp_tac
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
         \\ simp [])
    \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
         gen_tac
         \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
         \\ simp [Abbr `rmc1`])
    \\ qspecl_then [`n'`, `cb_begin`, `cb_end`, `bm_end`, `allow_err`, `bits_of ms0`,
                    `λk. P1 (k + (LENGTH posts + 1))`, `ffi'`, `s'`,
                    `os_cur with out := os_cur.out ++ chunk`, `os_f`, `ms_f`, `ec`,
                    `ck`, `t`, `ms_end`, `st_end`] mp_tac m3_post_err_nrc_safety
    \\ simp [LET_THM]
    \\ (impl_tac >- (
         qpat_assum `m3_ffi_return_ok_slot _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [m3_ffi_return_ok_slot_def])
         \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
         \\ qpat_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
         \\ simp [Abbr `rmc_post`,
                  boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]
         \\ Cases_on `bytes2`
         >- (qpat_x_assum `LENGTH [] = _` mp_tac \\ simp [])
         \\ simp [event_is_err_al_def]))
    \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
    \\ simp []
    \\ `ffi'.io_events ≼ st_end.io_events` by (
         qspecl_then [`rmc_post`, `ffi'`, `ck`, `s'`] mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ simp [])
    \\ `sent_so_far ++ [frame] ≼ exp_all` by (
         `sent_frames128_of ffi'.io_events ≼ sent_frames128_of st_end.io_events` by
           (irule sent_frames128_of_prefix \\ qpat_x_assum `ffi'.io_events ≼ st_end.io_events` ACCEPT_TAC)
         \\ `sent_frames128_of st_end.io_events ≼ exp_all` by (
              qpat_x_assum `t = Success ∧ _ ∨ _` mp_tac
              \\ Cases_on `32 ≤ LENGTH os0.key_in`
              \\ simp [Abbr `exp_all`, Abbr `io_err`]
              \\ strip_tac \\ simp []
              \\ irule rich_listTheory.IS_PREFIX_TRANS
              \\ qexists_tac `SND (airlock_exec stepf bk0 (recf bk0 sA0 sB0) (chunks64 os0.inp) NONE (SOME w))`
              \\ simp [airlock_exec_prefix_none])
         \\ irule rich_listTheory.IS_PREFIX_TRANS
         \\ qexists_tac `sent_frames128_of st_end.io_events`
         \\ qpat_x_assum `ffi'.io_events = _` (K ALL_TAC)
         \\ qpat_x_assum `sent_frames128_of ffi'.io_events ≼ _` mp_tac \\ simp [])
    \\ `os_cur.out ++ chunk ≼ FLAT (sent_so_far ++ [frame])` by
         (qpat_x_assum `FLAT sent_so_far = os_cur.out` (SUBST1_TAC o SYM) \\ simp [m3_FLAT_snoc_prefix, Abbr `frame`])
    \\ `FLAT (sent_so_far ++ [frame]) ≼ FLAT exp_all` by simp [m3_FLAT_prefix]
    \\ irule rich_listTheory.IS_PREFIX_TRANS
    \\ qexists_tac `FLAT (sent_so_far ++ [frame])` \\ simp [])
  >- (
    (* Case 6: recv64 veneer (idx = 2) *)
    Cases_on `¬boot_done`
    >- (
      qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                   `ms0`, `<| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                              inputs := chunks64 os0.inp; outputs := [];
                              commit_limit := NONE; write_limit := NONE |>`,
                   `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0`,
                   `forge_real_install_if`] mp_tac m3_compile_exact
      \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok] \\ strip_tac
      \\ `evaluate (real_mc (bits_of ms0)
            (forge_m3_mc_slot cb_end bm_end
               [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
               (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
               forge_real_install_if))
            ffi0 ck s_cur = (Halt t, ms_end, st_end)` by (
           `evaluate (real_mc (bits_of ms0)
              (forge_m3_mc_slot cb_end bm_end
                 [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                 (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0) forge_real_install_if))
              (airlock_ffi <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                              inputs := chunks64 os0.inp; outputs := [];
                              commit_limit := NONE; write_limit := NONE |>)
              (step_cnt + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by
                (`step_cnt + ck = ck + step_cnt` by decide_tac \\ pop_assum SUBST1_TAC
                 \\ irule targetPropsTheory.evaluate_add_clock \\ simp [])
           \\ pop_assum mp_tac
           \\ qpat_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi0 _ _` (qspec_then `ck` mp_tac)
           \\ simp [])
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`,
                      `λk. P0 (k + LENGTH posts)`, `ffi0`, `s_cur`, `ck`, `t`, `ms_end`, `st_end`]
           mp_tac m3_boot_order_ffi_contra
      \\ simp [LET_THM]
      \\ qpat_x_assum `ffi0.io_events = [] ⇔ _` mp_tac \\ simp [])
    \\ qpat_x_assum `¬¬boot_done` (assume_tac o REWRITE_RULE [])
    \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
    \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
    \\ imp_res_tac read_bytearray_mem_eq
    \\ mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] m3_ffirecv64_universal_slot)
                 (ASSUME ``m3_slot_layout_ok cb_begin cb_end bm_end``))
    \\ disch_then drule_all \\ strip_tac
    \\ Cases_on `w2n (s_cur.REG 3w) < 65`
    >- (
      first_x_assum drule \\ strip_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `os0`, `T`, `r`, `w`, `c`,
                                  `sA_cur`, `sB_cur`, `os_cur`, `s'`,
                                  `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [] \\ rpt conj_tac >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
             (qspecl_then [`F`, `extra_in`, `clim_rem`, `wlim_rem`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_recv64
        \\ impl_tac >- simp [] \\ strip_tac
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (2, bytes2, s_cur) = s'` by (
             irule mk_real_m3_ffi_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                     forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                     forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
             \\ simp [real_mc_def, forge_m3_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_m3_ffi_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ pop_assum SUBST1_TAC \\ simp [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [Abbr `exp_all`, Abbr `bk0`])
    \\ `65 ≤ w2n (s_cur.REG 3w)` by decide_tac
    \\ first_x_assum drule
    \\ disch_then (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS)))
    >- (
      qspecl_then [`r`, `os0.inp`, `os_cur.inp`, `frame`, `inp_after`] mp_tac m3_chunks64_take_step
      \\ impl_tac >- simp [] \\ strip_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                  `allow_err`, `ms0`, `os0`, `T`, `r + 1`, `w`, `c`,
                                  `sA_cur`, `sB_cur`, `os_cur with inp := inp_after`, `s'`,
                                  `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        qpat_assum `m3_ffi_return_ok_slot _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [m3_ffi_return_ok_slot_def])
        \\ simp [listTheory.FLAT_APPEND]
        \\ rpt (conj_tac >- fs [listTheory.FLAT_APPEND])
        \\ rpt gen_tac \\ strip_tac
        \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
             (qspecl_then [`F`, `frame :: extra_in`, `clim_rem`, `wlim_rem`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_recv64
        \\ impl_tac >- simp [] \\ strip_tac
        \\ `new_bs = 0w :: frame ++ DROP 65 bytes2 ∧
            ffi'.ffi_state = <| boot_key := bk0; boot_fail := F; slotA := sA_cur; slotB := sB_cur;
                                inputs := extra_in; outputs := sent_so_far;
                                commit_limit := clim_rem; write_limit := wlim_rem |>` by (
             qpat_x_assum `∀f fs. 65 ≤ LENGTH bytes2 ∧ _ ⇒ _` (qspecl_then [`frame`, `extra_in`] mp_tac)
             \\ simp [] \\ strip_tac \\ simp [airlock_io_component_equality])
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (2, 0w :: frame ++ DROP 65 bytes2, s_cur) = s'` by (
             irule mk_real_m3_ffi_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                     forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_m3_mc_slot cb_end bm_end
                     [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                     (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                     forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
             \\ simp [real_mc_def, forge_m3_mc_slot_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_m3_ffi_if]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ pop_assum SUBST1_TAC
             \\ qpat_x_assum `mk_real_m3_ffi_if_slot _ _ _ _ 0 (2, _, s_cur) = s'` mp_tac
             \\ simp [])
        \\ gen_tac
        \\ `TAKE r (chunks64 os0.inp) ++ [frame] ++ extra_in = TAKE r (chunks64 os0.inp) ++ frame :: extra_in` by
             REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp [Abbr `exp_all`, Abbr `bk0`])
    \\ (* Subcase 6c: EOF / truncated <64B / read error *)
       qabbrev_tac `P1 = mk_prefix_m3_P (posts ++ [s'])`
    \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
         (qspecl_then [`F`, `[]`, `NONE`, `NONE`, `P1`] mp_tac)
    \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_APPEND1])
    \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
    \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac airlock_ffi_call_recv64
    \\ impl_tac >- simp [] \\ strip_tac
    \\ `new_bs = 1w :: DROP 1 bytes2 ∧
        event_is_err_al (IO_event (ExtCall «recv64») bytes (ZIP (bytes2, new_bs)))` by (
         qpat_x_assum `65 ≤ LENGTH bytes2 ∧ ffi_cur.ffi_state.inputs = [] ⇒ _` mp_tac
         \\ simp [] \\ strip_tac \\ simp [])
    \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)) 0 (2, 1w :: DROP 1 bytes2, s_cur) = s'` by (
         irule mk_real_m3_ffi_if_select \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_LENGTH_APPEND])
    \\ qabbrev_tac `io_eof = <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                                inputs := TAKE r (chunks64 os0.inp); outputs := [];
                                commit_limit := NONE; write_limit := NONE |>`
    \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0)
                             (forge_m3_mc_slot cb_end bm_end
                                [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                                (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1) forge_real_install_if)`
    \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                                 (forge_m3_mc_slot cb_end bm_end
                                    [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                                    (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + (LENGTH posts + 1))))
                                    forge_real_install_if)`
    \\ `∀k. evaluate rmc1 (airlock_ffi io_eof) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
            evaluate rmc_post ffi' k s'` by (
         gen_tac
         \\ `evaluate rmc1 (airlock_ffi io_eof) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate (real_mc (bits_of ms0)
               (forge_m3_mc_slot cb_end bm_end
                  [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                  (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)))
                  forge_real_install_if))
               ffi_cur (SUC k) s_cur` by (
              qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
              \\ simp [Abbr `io_eof`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
         \\ pop_assum SUBST1_TAC
         \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc_post`, real_mc_def, forge_m3_mc_slot_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_m3_ffi_if]
         \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
              (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
         \\ simp [])
    \\ `io_eof.outputs = []` by simp [Abbr `io_eof`]
    \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                    `ms0`, `io_eof`, `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1`,
                    `forge_real_install_if`] mp_tac m3_compile_exact
    \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok]
    \\ disch_then (fn th => assume_tac (cj 3 th) \\
         REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS) (cj 4 th))
    \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
         `evaluate rmc1 (airlock_ffi io_eof)
            (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
              `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
              \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
         \\ pop_assum mp_tac
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
         \\ simp [])
    \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
         gen_tac
         \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
         \\ simp [Abbr `rmc1`])
    \\ qspecl_then [`n'`, `cb_begin`, `cb_end`, `bm_end`, `allow_err`, `bits_of ms0`,
                    `λk. P1 (k + (LENGTH posts + 1))`, `ffi'`, `s'`,
                    `os_cur with inp := inp_after`, `os_f`, `ms_f`, `ec`,
                    `ck`, `t`, `ms_end`, `st_end`] mp_tac m3_post_err_nrc_safety
    \\ simp [LET_THM]
    \\ (impl_tac >- (
         qpat_assum `m3_ffi_return_ok_slot _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [m3_ffi_return_ok_slot_def])
         \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
         \\ qpat_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
         \\ simp [Abbr `rmc_post`,
                  boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]
         \\ Cases_on `bytes2`
         >- (qpat_x_assum `LENGTH [] = _` mp_tac \\ simp [])
         \\ simp [event_is_err_al_def]))
    \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
    \\ simp []
    \\ `ffi'.io_events ≼ st_end.io_events` by (
         qspecl_then [`rmc_post`, `ffi'`, `ck`, `s'`] mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ simp [])
    \\ `os_cur.out ≼ FLAT exp_all` by (
         `sent_so_far ≼ exp_all` by (
           `sent_frames128_of ffi'.io_events ≼ sent_frames128_of st_end.io_events` by
             (irule sent_frames128_of_prefix \\ qpat_x_assum `ffi'.io_events ≼ st_end.io_events` ACCEPT_TAC)
           \\ `sent_frames128_of st_end.io_events ≼ exp_all` by (
                qpat_x_assum `t = Success ∧ _ ∨ _` mp_tac
                \\ Cases_on `32 ≤ LENGTH os0.key_in`
                \\ simp [Abbr `exp_all`, Abbr `io_eof`]
                \\ strip_tac \\ simp []
                \\ irule rich_listTheory.IS_PREFIX_TRANS
                \\ qexists_tac `SND (airlock_exec stepf bk0 (recf bk0 sA0 sB0) (TAKE r (chunks64 os0.inp)) NONE NONE)`
                \\ simp [airlock_exec_take_prefix_none, chunks64_every_len64])
           \\ irule rich_listTheory.IS_PREFIX_TRANS
           \\ qexists_tac `sent_frames128_of st_end.io_events`
           \\ qpat_x_assum `ffi'.io_events = _` (K ALL_TAC)
           \\ qpat_x_assum `sent_frames128_of ffi'.io_events ≼ _` mp_tac \\ simp [])
         \\ qpat_x_assum `FLAT sent_so_far = os_cur.out` (SUBST1_TAC o SYM)
         \\ simp [m3_FLAT_prefix])
    \\ simp []
    \\ rpt strip_tac
    \\ `LENGTH os_cur.inp < 64` by (qpat_x_assum `allow_err ∨ _` mp_tac \\ simp [])
    \\ `TAKE r (chunks64 os0.inp) = chunks64 os0.inp` by (
         qspecl_then [`r`, `os0.inp`, `os_cur.inp`] mp_tac m3_chunks64_take_all_of_lt64
         \\ impl_tac >- (rpt conj_tac \\ TRY (first_assum ACCEPT_TAC) \\ simp [])
         \\ simp [])
    \\ `t = Success ∧ st_end.io_events = ffi'.io_events` by simp []
    \\ `sent_so_far = exp_all` by (
         qpat_x_assum `ffi'.io_events = _` (K ALL_TAC)
         \\ qpat_x_assum `t = Success ∧ _ ∨ _` mp_tac
         \\ Cases_on `32 ≤ LENGTH os0.key_in`
         \\ simp [Abbr `exp_all`, Abbr `io_eof`])
    \\ qpat_x_assum `FLAT sent_so_far = os_cur.out` (SUBST1_TAC o SYM)
    \\ simp [])
  \\ (* Case 7: commit veneer (idx = 3) *)
     Cases_on `¬boot_done`
  >- (
    qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                 `ms0`, `<| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                            inputs := chunks64 os0.inp; outputs := [];
                            commit_limit := NONE; write_limit := NONE |>`,
                 `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0`,
                 `forge_real_install_if`] mp_tac m3_compile_exact
    \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok] \\ strip_tac
    \\ `evaluate (real_mc (bits_of ms0)
          (forge_m3_mc_slot cb_end bm_end
             [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
             (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P0 (k + LENGTH posts)))
             forge_real_install_if))
          ffi0 ck s_cur = (Halt t, ms_end, st_end)` by (
         `evaluate (real_mc (bits_of ms0)
            (forge_m3_mc_slot cb_end bm_end
               [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
               (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P0) forge_real_install_if))
            (airlock_ffi <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                            inputs := chunks64 os0.inp; outputs := [];
                            commit_limit := NONE; write_limit := NONE |>)
            (step_cnt + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by
              (`step_cnt + ck = ck + step_cnt` by decide_tac \\ pop_assum SUBST1_TAC
               \\ irule targetPropsTheory.evaluate_add_clock \\ simp [])
         \\ pop_assum mp_tac
         \\ qpat_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi0 _ _` (qspec_then `ck` mp_tac)
         \\ simp [])
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`,
                    `λk. P0 (k + LENGTH posts)`, `ffi0`, `s_cur`, `ck`, `t`, `ms_end`, `st_end`]
         mp_tac m3_boot_order_ffi_contra
    \\ simp [LET_THM]
    \\ qpat_x_assum `ffi0.io_events = [] ⇔ _` mp_tac \\ simp [])
  \\ qpat_x_assum `¬¬boot_done` (assume_tac o REWRITE_RULE [])
  \\ TRY (qpat_x_assum `_ ⇒ ∃bytes bytes2. _` mp_tac \\ impl_tac >- simp [] \\ strip_tac)
  \\ TRY (qpat_x_assum `∃bytes bytes2. _` strip_assume_tac)
  \\ imp_res_tac read_bytearray_mem_eq
  \\ mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] m3_fficommit_universal_slot)
               (ASSUME ``m3_slot_layout_ok cb_begin cb_end bm_end``))
  \\ disch_then drule_all \\ simp [LET_THM] \\ strip_tac
  \\ Cases_on `w2n (s_cur.REG 3w) < 258`
  >- (
    first_x_assum drule \\ strip_tac
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
    \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                `allow_err`, `ms0`, `os0`, `T`, `r`, `w`, `c`,
                                `sA_cur`, `sB_cur`, `os_cur`, `s'`,
                                `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      simp [] \\ rpt conj_tac >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
      >- fs [m3_ffi_return_ok_slot_def] >- fs [m3_ffi_return_ok_slot_def]
      \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
           (qspecl_then [`F`, `extra_in`, `clim_rem`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
           (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] airlock_ffi_call_commit)
      \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `ffi'` \\ simp []
      \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (3, bytes2, s_cur) = s'` by (
           irule mk_real_m3_ffi_if_select \\ simp []
           \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
           \\ simp [rich_listTheory.EL_LENGTH_APPEND])
      \\ `∀k. evaluate (real_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                   (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                   forge_real_install_if))
              ffi_cur (SUC k) s_cur =
              evaluate (real_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                   (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                   forge_real_install_if))
              ffi' k s'` by (
           gen_tac
           \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
           \\ simp [real_mc_def, forge_m3_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_m3_ffi_if]
           \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
           \\ pop_assum SUBST1_TAC \\ simp [])
      \\ gen_tac
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp [Abbr `exp_all`, Abbr `bk0`])
  \\ `258 ≤ w2n (s_cur.REG 3w)` by decide_tac
  \\ first_x_assum drule \\ strip_tac
  >- (
    (* Subcase 7b: full commit succeeded *)
    qabbrev_tac `sel = EL 1 bytes2`
    \\ qabbrev_tac `rec = TAKE 256 (DROP 2 bytes2)`
    \\ qabbrev_tac `sA_next = if (1w && sel) = 0w then rec else sA_cur`
    \\ qabbrev_tac `sB_next = if (1w && sel) = 0w then sB_cur else rec`
    \\ qabbrev_tac `d' = patch_bytes (if (1w && sel) = 0w then 0 else 256) rec os_cur.disk`
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
    \\ disch_then (qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                                `allow_err`, `ms0`, `os0`, `T`, `r`, `w`, `c + 1`,
                                `sA_next`, `sB_next`, `os_cur with <| disk := d'; durable := d' |>`, `s'`,
                                `os_f`, `ms_f`, `ec`, `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      qpat_assum `m3_ffi_return_ok_slot _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [m3_ffi_return_ok_slot_def])
      \\ simp []
      \\ rpt gen_tac \\ strip_tac
      \\ qabbrev_tac `clim_prev = OPTION_MAP SUC clim_rem`
      \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
           (qspecl_then [`F`, `extra_in`, `clim_prev`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])
      \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
           (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] airlock_ffi_call_commit)
      \\ impl_tac >- simp [] \\ strip_tac
      \\ `new_bs = 0w :: DROP 1 bytes2 ∧
          ffi'.ffi_state = <| boot_key := bk0; boot_fail := F; slotA := sA_next; slotB := sB_next;
                              inputs := extra_in; outputs := sent_so_far;
                              commit_limit := clim_rem; write_limit := wlim_rem |>` by (
           qpat_x_assum `258 ≤ LENGTH bytes2 ⇒ _` mp_tac
           \\ qpat_x_assum `ffi_cur.ffi_state = _` mp_tac
           \\ Cases_on `clim_rem` \\ Cases_on `(1w && sel) = 0w`
           \\ simp [Abbr `clim_prev`, Abbr `sA_next`, Abbr `sB_next`, Abbr `sel`, Abbr `rec`]
           \\ rpt strip_tac \\ simp [airlock_io_component_equality])
      \\ qexists_tac `ffi'` \\ simp []
      \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)) 0 (3, 0w :: DROP 1 bytes2, s_cur) = s'` by (
           irule mk_real_m3_ffi_if_select \\ simp []
           \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
           \\ simp [rich_listTheory.EL_LENGTH_APPEND])
      \\ `∀k. evaluate (real_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                   (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + LENGTH posts)))
                   forge_real_install_if))
              ffi_cur (SUC k) s_cur =
              evaluate (real_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                   (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P (k + (LENGTH posts + 1))))
                   forge_real_install_if))
              ffi' k s'` by (
           gen_tac
           \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
           \\ simp [real_mc_def, forge_m3_mc_slot_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_m3_ffi_if]
           \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
           \\ pop_assum SUBST1_TAC \\ simp [])
      \\ gen_tac
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ Cases_on `clim_rem`
      \\ simp [Abbr `clim_prev`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp [Abbr `exp_all`, Abbr `bk0`])
  \\ (* Subcase 7c: commit failed (pwrite64/fdatasync error) *)
     qabbrev_tac `P1 = mk_prefix_m3_P (posts ++ [s'])`
  \\ drule_all m3_chunks64_drop_eq \\ strip_tac
  \\ qpat_x_assum `chunks64 os0.inp = _` (assume_tac o SYM)
  \\ qpat_assum `∀bfail extra_in clim_rem wlim_rem P. _`
       (qspecl_then [`F`, `chunks64 os_cur.inp`, `SOME 0`, `NONE`, `P1`] mp_tac)
  \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_APPEND1])
  \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
  \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
       (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] airlock_ffi_call_commit)
  \\ impl_tac >- simp [] \\ strip_tac
  \\ `new_bs = 1w :: DROP 1 bytes2 ∧
      event_is_err_al (IO_event (ExtCall «commit») bytes (ZIP (bytes2, new_bs)))` by (
       qpat_x_assum `258 ≤ LENGTH bytes2 ⇒ _` mp_tac
       \\ simp [] \\ strip_tac \\ simp [])
  \\ `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)) 0 (3, 1w :: DROP 1 bytes2, s_cur) = s'` by (
       irule mk_real_m3_ffi_if_select \\ simp [Abbr `P1`, mk_prefix_m3_P_def, rich_listTheory.EL_LENGTH_APPEND])
  \\ qabbrev_tac `io_ce = <| boot_key := bk0; boot_fail := F; slotA := sA0; slotB := sB0;
                             inputs := chunks64 os0.inp; outputs := [];
                             commit_limit := SOME c; write_limit := NONE |>`
  \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0)
                           (forge_m3_mc_slot cb_end bm_end
                              [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                              (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1) forge_real_install_if)`
  \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                               (forge_m3_mc_slot cb_end bm_end
                                  [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                                  (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + (LENGTH posts + 1))))
                                  forge_real_install_if)`
  \\ `∀k. evaluate rmc1 (airlock_ffi io_ce) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
          evaluate rmc_post ffi' k s'` by (
       gen_tac
       \\ `evaluate rmc1 (airlock_ffi io_ce) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
           evaluate (real_mc (bits_of ms0)
             (forge_m3_mc_slot cb_end bm_end
                [ExtCall «bootload»; ExtCall «send128»; ExtCall «recv64»; ExtCall «commit»]
                (mk_real_m3_ffi_if_slot cb_begin cb_end bm_end (λk. P1 (k + LENGTH posts)))
                forge_real_install_if))
             ffi_cur (SUC k) s_cur` by (
            qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
            \\ simp [Abbr `io_ce`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
       \\ pop_assum SUBST1_TAC
       \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
       \\ simp [Abbr `rmc_post`, real_mc_def, forge_m3_mc_slot_def,
                arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                shift_mk_real_m3_ffi_if]
       \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
            (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
       \\ simp [])
  \\ `io_ce.outputs = []` by simp [Abbr `io_ce`]
  \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                  `ms0`, `io_ce`, `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end P1`,
                  `forge_real_install_if`] mp_tac m3_compile_exact
  \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok]
  \\ disch_then (fn th => assume_tac (cj 3 th) \\
       REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS) (cj 4 th))
  \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
       `evaluate rmc1 (airlock_ffi io_ce)
          (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
            `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
            \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
       \\ pop_assum mp_tac
       \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
       \\ simp [])
  \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
       gen_tac
       \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
       \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
       \\ simp [Abbr `rmc1`])
  \\ qspecl_then [`n'`, `cb_begin`, `cb_end`, `bm_end`, `allow_err`, `bits_of ms0`,
                  `λk. P1 (k + (LENGTH posts + 1))`, `ffi'`, `s'`,
                  `os_cur with disk := d_tmp`, `os_f`, `ms_f`, `ec`,
                  `ck`, `t`, `ms_end`, `st_end`] mp_tac m3_post_err_nrc_safety
  \\ simp [LET_THM]
  \\ (impl_tac >- (
       qpat_assum `m3_ffi_return_ok_slot _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [m3_ffi_return_ok_slot_def])
       \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
       \\ qpat_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
       \\ simp [Abbr `rmc_post`,
                boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]
       \\ Cases_on `bytes2`
       >- (qpat_x_assum `LENGTH [] = _` mp_tac \\ simp [])
       \\ simp [event_is_err_al_def]))
  \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
  \\ simp []
  \\ `ffi'.io_events ≼ st_end.io_events` by (
       qspecl_then [`rmc_post`, `ffi'`, `ck`, `s'`] mp_tac targetPropsTheory.evaluate_io_events_mono
       \\ simp [])
  \\ `sent_so_far ≼ exp_all` by (
       `sent_frames128_of ffi'.io_events ≼ sent_frames128_of st_end.io_events` by
         (irule sent_frames128_of_prefix \\ qpat_x_assum `ffi'.io_events ≼ st_end.io_events` ACCEPT_TAC)
       \\ `sent_frames128_of st_end.io_events ≼ exp_all` by (
            qpat_x_assum `t = Success ∧ _ ∨ _` mp_tac
            \\ Cases_on `32 ≤ LENGTH os0.key_in`
            \\ simp [Abbr `exp_all`, Abbr `io_ce`]
            \\ strip_tac \\ simp []
            \\ irule rich_listTheory.IS_PREFIX_TRANS
            \\ qexists_tac `SND (airlock_exec stepf bk0 (recf bk0 sA0 sB0) (chunks64 os0.inp) (SOME c) NONE)`
            \\ simp [airlock_exec_prefix_none])
       \\ irule rich_listTheory.IS_PREFIX_TRANS
       \\ qexists_tac `sent_frames128_of st_end.io_events`
       \\ qpat_x_assum `ffi'.io_events = _` (K ALL_TAC)
       \\ qpat_x_assum `sent_frames128_of ffi'.io_events ≼ _` mp_tac \\ simp [])
  \\ qpat_x_assum `FLAT sent_so_far = os_cur.out` (SUBST1_TAC o SYM)
  \\ simp [m3_FLAT_prefix]
QED

(* ---- 6. Polymorphic Top-Level Whole-Binary 4-FFI Airlock Composition Theorem ---- *)

Theorem forge_airlock_kernel_compose:
  ∀(recf:word8 list -> word8 list -> word8 list -> 'st)
   (stepf:word8 list -> 'st -> frame64 -> 'st # frame128 # bool)
   prog code data info oracle.
    backend$compile arm8_config (set_oracle arm8_backend_config oracle) prog = SOME (code, data, info) ∧
    prog_syntax_ok prog ∧
    info.lab_conf.shmem_extra = [] ∧
    ffinames_to_string_list (the [] info.lab_conf.ffi_names) =
      [«bootload»; «send128»; «recv64»; «commit»] ∧
    0 < LENGTH code ∧ LENGTH code ≤ FORGE_M3_MAX_CODE_BYTES ∧
    LENGTH data ≤ FORGE_MAX_BITMAP_WORDS ∧
    (∀io:airlock_io.
       io.outputs = [] ⇒
       sem_satisfies
         (semantics_dec_list (init_state (airlock_ffi io)) init_env prog)
         (λb. ∃io_events.
                b = Terminate Success io_events ∧
                stop_after_err_al io_events ∧
                boot_first_once_al io_events ∧
                sent_frames128_of io_events =
                  if ¬io.boot_fail ∧ LENGTH io.boot_key = 32 ∧
                     LENGTH io.slotA = 256 ∧ LENGTH io.slotB = 256 then
                    SND (airlock_exec stepf io.boot_key
                           (recf io.boot_key io.slotA io.slotB)
                           io.inputs io.commit_limit io.write_limit)
                  else [])) ⇒
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
                     FLAT (SND (airlock_exec stepf key
                       (recf key (TAKE 256 p512) (DROP 256 p512))
                       (chunks64 os0.inp) NONE NONE))
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
                     FLAT (SND (airlock_exec stepf key
                       (recf key (TAKE 256 p512) (DROP 256 p512))
                       (chunks64 os0.inp) NONE NONE))
                 else []))) ∧
    (∃ms0:arm8_state.
       forge_m3_slot_loaded code data ms0 ∧
       ms0.TCR_EL1.TBI0 ∧
       ¬ms0.TCR_EL1.TBI1 ∧
       ms0.SCTLR_EL1.SA0 ∧
       aligned 4 ms0.SP_EL0)
Proof
  rpt strip_tac
  >- (
    simp [LET_THM]
    \\ qabbrev_tac `cb_begin = m3_slot_cb_begin (LENGTH code)`
    \\ qabbrev_tac `cb_end = m3_slot_cb_end (LENGTH code)`
    \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
    \\ qabbrev_tac `cbsp = m3_slot_cbspace (LENGTH code)`
    \\ `m3_slot_layout_ok cb_begin cb_end bm_end` by (
         qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac m3_slot_params_props
         \\ simp [LET_THM])
    \\ `det_run 43 ms0 (FUNPOW arm8$Next 43 ms0) ∧
        arm8_ok (erase (FUNPOW arm8$Next 43 ms0)) ∧
        sp_ok (FUNPOW arm8$Next 43 ms0) ∧
        bits_of (FUNPOW arm8$Next 43 ms0) = bits_of ms0 ∧
        m3_shim_loaded_slot cb_begin cb_end bm_end (FUNPOW arm8$Next 43 ms0).MEM` by (
         fs [forge_m3_slot_loaded_def, LET_THM]
         \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `ms0`] mp_tac m3_startup_to_cake_main_slot
         \\ simp [LET_THM])
    \\ rpt conj_tac
    >- (
      rpt strip_tac \\ simp [LET_THM]
      \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                      `ms0`, `io`, `ffi_if`, `inst_if`] mp_tac m3_compile_exact
      \\ simp [LET_THM])
    >- (
      rpt strip_tac
      \\ qspec_then `os0.inp` strip_assume_tac m3_chunks64_split_tail
      \\ qabbrev_tac `bk0 = if 32 ≤ LENGTH os0.key_in then TAKE 32 os0.key_in else []`
      \\ qabbrev_tac `io0 = <| boot_key := bk0; boot_fail := F;
                               slotA := TAKE 256 (pad512 os0.disk);
                               slotB := DROP 256 (pad512 os0.disk);
                               inputs := chunks64 os0.inp; outputs := [];
                               commit_limit := NONE; write_limit := NONE |>`
      \\ qspecl_then [`recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                      `ms0`, `io0`,
                      `mk_real_m3_ffi_if_slot cb_begin cb_end bm_end
                         (noerr_m3_P cb_end bm_end os0.key_in os0.disk tail_bs)`,
                      `forge_real_install_if`] mp_tac m3_compile_exact
      \\ simp [LET_THM, mk_real_m3_ffi_if_slot_ok, Abbr `io0`]
      \\ disch_then (fn th => assume_tac (cj 3 th) \\ mp_tac (cj 4 th))
      \\ disch_then (qx_choosel_then [`ck`, `t`, `ms_end`, `st_end`] (EVERY o map assume_tac o CONJUNCTS))
      \\ qspecl_then [`ck`, `cb_begin`, `cb_end`, `bm_end`, `bits_of ms0`,
                      `os0.key_in`, `os0.disk`, `tail_bs`,
                      `airlock_ffi <| boot_key := bk0; boot_fail := F;
                                      slotA := TAKE 256 (pad512 os0.disk);
                                      slotB := DROP 256 (pad512 os0.disk);
                                      inputs := chunks64 os0.inp; outputs := [];
                                      commit_limit := NONE; write_limit := NONE |>`,
                      `FUNPOW arm8$Next 43 ms0`, `os0`, `t`, `ms_end`, `st_end`]
           mp_tac m3_liveness_eval_rtc
      \\ simp [LET_THM]
      \\ impl_tac >- (
           rpt conj_tac
           \\ TRY (first_assum ACCEPT_TAC)
           \\ simp [airlock_ffi_def, ffiTheory.initial_ffi_state_def, chunks64_every_len64, Abbr `bk0`])
      \\ strip_tac
      \\ qexists_tac `os_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp []
      \\ irule relationTheory.RTC_RTC
      \\ qexists_tac `(os0, FUNPOW arm8$Next 43 ms0)`
      \\ simp []
      \\ irule m3_det_run_imp_rtc \\ qexists_tac `43` \\ simp [])
    >- (
      rpt gen_tac \\ strip_tac
      \\ qpat_x_assum `RTC _ _ _` (strip_assume_tac o REWRITE_RULE [arithmeticTheory.RTC_eq_NRC])
      \\ drule_all m3_det_run_peel_nrc \\ strip_tac
      \\ qspecl_then [`n - 43`, `recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                      `T`, `ms0`, `os0`, `F`, `0`, `0`, `0`,
                      `TAKE 256 (pad512 os0.disk)`, `DROP 256 (pad512 os0.disk)`,
                      `os0`, `FUNPOW arm8$Next 43 ms0`, `os_f`, `ms_f`, `exit_code`,
                      `[]`, `[]`, `0`] mp_tac m3_pre_err_nrc_safety
      \\ simp [LET_THM]
      \\ impl_tac
      >- (
        simp [] \\ rpt gen_tac
        \\ qexists_tac `airlock_ffi <| boot_key := if 32 ≤ LENGTH os0.key_in then TAKE 32 os0.key_in else [];
                                       boot_fail := bfail;
                                       slotA := TAKE 256 (pad512 os0.disk);
                                       slotB := DROP 256 (pad512 os0.disk);
                                       inputs := extra_in; outputs := [];
                                       commit_limit := clim_rem; write_limit := wlim_rem |>`
        \\ `OPTION_MAP (λd:num. d) clim_rem = clim_rem ∧ OPTION_MAP (λd:num. d) wlim_rem = wlim_rem` by
             (Cases_on `clim_rem` \\ Cases_on `wlim_rem` \\ simp [])
        \\ simp [airlock_ffi_def, ffiTheory.initial_ffi_state_def, sent_frames128_of_def, ETA_THM])
      \\ Cases_on `32 ≤ LENGTH os0.key_in` \\ simp [LET_THM])
    \\ rpt gen_tac \\ strip_tac
    \\ qpat_x_assum `RTC _ _ _` (strip_assume_tac o REWRITE_RULE [arithmeticTheory.RTC_eq_NRC])
    \\ drule_all m3_det_run_peel_nrc \\ strip_tac
    \\ qspecl_then [`n - 43`, `recf`, `stepf`, `prog`, `code`, `data`, `info`, `oracle`,
                    `F`, `ms0`, `os0`, `F`, `0`, `0`, `0`,
                    `TAKE 256 (pad512 os0.disk)`, `DROP 256 (pad512 os0.disk)`,
                    `os0`, `FUNPOW arm8$Next 43 ms0`, `os_f`, `ms_f`, `0w`,
                    `[]`, `[]`, `0`] mp_tac m3_pre_err_nrc_safety
    \\ simp [LET_THM]
    \\ impl_tac
    >- (
      simp [] \\ rpt gen_tac
      \\ qexists_tac `airlock_ffi <| boot_key := if 32 ≤ LENGTH os0.key_in then TAKE 32 os0.key_in else [];
                                     boot_fail := bfail;
                                     slotA := TAKE 256 (pad512 os0.disk);
                                     slotB := DROP 256 (pad512 os0.disk);
                                     inputs := extra_in; outputs := [];
                                     commit_limit := clim_rem; write_limit := wlim_rem |>`
      \\ `OPTION_MAP (λd:num. d) clim_rem = clim_rem ∧ OPTION_MAP (λd:num. d) wlim_rem = wlim_rem` by
           (Cases_on `clim_rem` \\ Cases_on `wlim_rem` \\ simp [])
      \\ simp [airlock_ffi_def, ffiTheory.initial_ffi_state_def, sent_frames128_of_def, ETA_THM])
    \\ Cases_on `32 ≤ LENGTH os0.key_in` \\ simp [LET_THM])
  \\ irule forge_m3_slot_nonvacuous
  \\ simp []
QED
