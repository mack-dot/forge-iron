(*
  Forge Milestone 3 Reusable Runtime: Core M3 256 KB Slot Disjointness,
  6-Syscall Whole-Step Helpers, Machine Config, Interference & Non-Vacuity.
*)
Theory forge_airlockShimBase
Ancestors
  words arithmetic list rich_list combin pred_set relation
  arm8 arm8_step arm8_target arm8_config arm8_configProof
  asmProps targetSem lab_to_targetProof backendProof misc alignment
  forge_runtimeSpec forge_airlockFfi forge_airlockContract
  forge_arm8Erasure forge_shimProof forge_slotUtil
Libs
  preamble blastLib wordsLib

(* ---- 1. Memory Congruence, Slot Parameters & Disjointness ---- *)

Theorem m3_shim_words_len:
  LENGTH forge_shim_airlock_words = 168
Proof
  simp [forge_shim_airlock_words_def]
QED

Theorem m3_veneers_len:
  ∀cb_begin cb_end bm_buf_end.
    LENGTH (forge_m3_slot_veneers cb_begin cb_end bm_buf_end) = 52
Proof
  rpt gen_tac \\ simp [forge_m3_slot_veneers_def]
QED

Theorem m3_shim_loaded_slot_cong:
  ∀cb_begin cb_end bm_buf_end m1 m2.
    (∀a. a ∈ forge_m3_shim_code_region ⇒ m1 a = m2 a) ⇒
    (m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1 ⇔
     m3_shim_loaded_slot cb_begin cb_end bm_buf_end m2)
Proof
  rpt strip_tac
  \\ simp [m3_shim_loaded_slot_def]
  \\ `words32_in_mem FORGE_M3_VENEERS_BASE (forge_m3_slot_veneers cb_begin cb_end bm_buf_end) m1 ⇔
      words32_in_mem FORGE_M3_VENEERS_BASE (forge_m3_slot_veneers cb_begin cb_end bm_buf_end) m2` by
     (irule words32_in_mem_cong
      \\ simp [m3_veneers_len, FORGE_M3_VENEERS_BASE_def, dimword_64]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs [forge_m3_shim_code_region_def, FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def])
  \\ `words32_in_mem FORGE_M3_SHIM_BASE forge_shim_airlock_words m1 ⇔
      words32_in_mem FORGE_M3_SHIM_BASE forge_shim_airlock_words m2` by
     (irule words32_in_mem_cong
      \\ simp [m3_shim_words_len, FORGE_M3_SHIM_BASE_def, dimword_64]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs [forge_m3_shim_code_region_def, FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def])
  \\ simp []
QED

Theorem m3_shim_loaded_slot_update:
  ∀cb_begin cb_end bm_buf_end m a b.
    a ∉ forge_m3_shim_code_region ⇒
    (m3_shim_loaded_slot cb_begin cb_end bm_buf_end (m⦇a ↦ b⦈) ⇔
     m3_shim_loaded_slot cb_begin cb_end bm_buf_end m)
Proof
  rpt strip_tac \\ irule m3_shim_loaded_slot_cong
  \\ simp [combinTheory.APPLY_UPDATE_THM] \\ rpt strip_tac \\ rw [] \\ fs []
QED

Theorem m3_untagged_lt_8m[local]:
  ∀a:word64. a <₊ 0x00800000w ⇒ untagged a
Proof
  simp [untagged_def] \\ blastLib.BBLAST_TAC
QED

Theorem m3_regions_disjoint_slot:
  ∀cb_begin cb_end bm_buf_end.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_m3_rx_tmp_region ⇒
         a ∉ forge_m3_prog_addresses cb_end bm_buf_end ∧ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_cml_ptrs_region ⇒
         a ∉ forge_m3_prog_addresses cb_end bm_buf_end ∧ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_heap_hdr_region ⇒
         a ∉ forge_cml_ptrs_region ∧ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒ untagged a) ∧
    (∀a. a ∈ forge_m3_shim_code_region ⇒ untagged a)
Proof
  rpt gen_tac \\ strip_tac
  \\ fs [m3_slot_layout_ok_def, forge_m3_prog_addresses_def, forge_m3_code_region_def,
         forge_bitmaps_region_slot_def, forge_heap_stack_region_def,
         forge_m3_shim_code_region_def, forge_m3_rx_tmp_region_def,
         forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
         FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def,
         FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def, FORGE_CML_HEAP_def,
         FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, FORGE_RX_TMP_def,
         FORGE_HEAP_def, FORGE_STACKEND_def]
  \\ rpt conj_tac \\ rpt strip_tac
  \\ TRY (irule m3_untagged_lt_8m)
  \\ fs [wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac
QED

Theorem m3_align_up_64k_bounds[local]:
  ∀a:word64. 0x004000D0w <₊ a ∧ a ≤₊ 0x00440000w ⇒
    a ≤₊ align_up_64k a ∧ align_up_64k a ≤₊ 0x00440000w
Proof
  simp [align_up_64k_def] \\ blastLib.BBLAST_TAC
QED

Theorem m3_slot_params_props:
  ∀code_len data_len.
    0 < code_len ∧ code_len ≤ FORGE_M3_MAX_CODE_BYTES ∧ data_len ≤ FORGE_MAX_BITMAP_WORDS ⇒
    let cb_begin = m3_slot_cb_begin code_len in
    let cb_end = m3_slot_cb_end code_len in
    let cbsp = m3_slot_cbspace code_len in
    let bm_end = slot_bm_buf_end data_len in
      m3_slot_layout_ok cb_begin cb_end bm_end ∧
      FORGE_M3_CAKE_MAIN + n2w code_len = cb_begin ∧
      cb_begin + n2w cbsp = cb_end ∧
      FORGE_M3_CAKE_MAIN + n2w code_len + n2w cbsp = cb_end ∧
      w2n FORGE_M3_CAKE_MAIN + code_len = w2n cb_begin ∧
      w2n FORGE_M3_CAKE_MAIN + code_len + cbsp = w2n cb_end ∧
      w2n cb_end ≤ 0x00440000 ∧
      FORGE_CAKE_BITMAPS + n2w (8 * data_len) = bm_end ∧
      FORGE_CAKE_BITMAPS + n2w data_len * (bytes_in_word:word64) = bm_end ∧
      w2n FORGE_CAKE_BITMAPS + 8 * data_len = w2n bm_end ∧
      w2n bm_end ≤ 0x00470000
Proof
  rpt strip_tac
  \\ PURE_REWRITE_TAC [LET_THM] \\ BETA_TAC
  \\ fs [FORGE_M3_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
  \\ qabbrev_tac `cb_begin = m3_slot_cb_begin code_len`
  \\ qabbrev_tac `cb_end = m3_slot_cb_end code_len`
  \\ qabbrev_tac `cbsp = m3_slot_cbspace code_len`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end data_len`
  \\ `cb_begin = FORGE_M3_CAKE_MAIN + n2w code_len` by simp [Abbr `cb_begin`, m3_slot_cb_begin_def]
  \\ `w2n cb_begin = 0x004000D0 + code_len` by
       simp [FORGE_M3_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64]
  \\ `0x004000D0w <₊ cb_begin ∧ cb_begin ≤₊ 0x00440000w` by
       simp [wordsTheory.WORD_LO, wordsTheory.WORD_LS]
  \\ `cb_end = align_up_64k cb_begin` by
       simp [Abbr `cb_end`, Abbr `cb_begin`, m3_slot_cb_end_def]
  \\ `cb_begin ≤₊ cb_end ∧ cb_end ≤₊ 0x00440000w` by
       (qpat_assum `cb_end = align_up_64k cb_begin` SUBST1_TAC
        \\ MATCH_MP_TAC m3_align_up_64k_bounds \\ simp [])
  \\ `w2n cb_end ≤ 0x00440000` by fs [wordsTheory.WORD_LS]
  \\ `cbsp = w2n (cb_end - cb_begin)` by
       (mp_tac (Q.SPEC `code_len` m3_slot_cbspace_def)
        \\ qpat_assum `Abbrev (cbsp = _)` (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])
        \\ qpat_assum `Abbrev (cb_end = _)` (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])
        \\ qpat_assum `Abbrev (cb_begin = _)` (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])
        \\ simp [])
  \\ `w2n cb_begin + cbsp = w2n cb_end` by
       (qpat_assum `cbsp = _` SUBST1_TAC
        \\ qspecl_then [`cb_end`, `cb_begin`] mp_tac wordsTheory.word_sub_w2n
        \\ impl_tac >- first_assum ACCEPT_TAC
        \\ disch_then SUBST1_TAC
        \\ qpat_assum `cb_begin ≤₊ cb_end` mp_tac
        \\ REWRITE_TAC [wordsTheory.WORD_LS] \\ decide_tac)
  \\ `cb_begin + n2w cbsp = cb_end` by
       (qpat_assum `cbsp = _` SUBST1_TAC \\ REWRITE_TAC [wordsTheory.n2w_w2n] \\ blastLib.BBLAST_TAC)
  \\ `FORGE_M3_CAKE_MAIN + n2w code_len + n2w cbsp = cb_end` by
       (qpat_assum `cb_begin = _` (SUBST1_TAC o SYM) \\ first_assum ACCEPT_TAC)
  \\ `w2n FORGE_M3_CAKE_MAIN + code_len = w2n cb_begin` by simp [FORGE_M3_CAKE_MAIN_def]
  \\ `w2n FORGE_M3_CAKE_MAIN + code_len + cbsp = w2n cb_end` by decide_tac
  \\ `bm_end = FORGE_CAKE_BITMAPS + n2w (8 * data_len)` by simp [Abbr `bm_end`, slot_bm_buf_end_def]
  \\ `w2n bm_end = 0x00460018 + 8 * data_len` by
       simp [FORGE_CAKE_BITMAPS_def, wordsTheory.word_add_n2w, w2n_n2w_64]
  \\ `w2n bm_end ≤ 0x00470000` by decide_tac
  \\ `FORGE_CAKE_BITMAPS ≤₊ bm_end ∧ bm_end ≤₊ FORGE_DATA_SLOT_END` by
       simp [FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, wordsTheory.WORD_LS]
  \\ `m3_slot_layout_ok cb_begin cb_end bm_end` by
       (REWRITE_TAC [m3_slot_layout_ok_def, FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def]
        \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ `FORGE_CAKE_BITMAPS + n2w data_len * (bytes_in_word:word64) = bm_end` by
       (qpat_assum `bm_end = _` SUBST1_TAC
        \\ AP_TERM_TAC \\ simp [bytes_in_word_64, wordsTheory.word_mul_n2w])
  \\ `w2n FORGE_CAKE_BITMAPS + 8 * data_len = w2n bm_end` by simp [FORGE_CAKE_BITMAPS_def]
  \\ `FORGE_M3_CAKE_MAIN + n2w code_len = cb_begin` by (irule EQ_SYM \\ first_assum ACCEPT_TAC)
  \\ `FORGE_CAKE_BITMAPS + n2w (8 * data_len) = bm_end` by (irule EQ_SYM \\ first_assum ACCEPT_TAC)
  \\ rpt conj_tac
  \\ TRY (first_assum ACCEPT_TAC)
  \\ TRY decide_tac
  \\ TRY (qpat_assum `cb_begin + n2w cbsp = cb_end` (SUBST1_TAC o SYM) \\ blastLib.BBLAST_TAC)
  \\ qpat_assum `FORGE_CAKE_BITMAPS + n2w data_len * _ = bm_end` (SUBST1_TAC o SYM)
  \\ blastLib.BBLAST_TAC
QED

Theorem m3_veneer_facts_slot:
  ∀cb_begin cb_end bm_end.
    m3_slot_layout_ok cb_begin cb_end bm_end ⇒
    FORGE_M3_EXIT_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_INSTALL_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFIBOOT_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFISEND_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFIRECV_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFICOMMIT_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    ALL_DISTINCT [FORGE_M3_EXIT_VENEER; FORGE_M3_INSTALL_VENEER;
                  FORGE_M3_FFIBOOT_VENEER; FORGE_M3_FFISEND_VENEER;
                  FORGE_M3_FFIRECV_VENEER; FORGE_M3_FFICOMMIT_VENEER]
Proof
  rpt strip_tac
  \\ fs [m3_slot_layout_ok_def, forge_m3_prog_addresses_def, forge_m3_code_region_def,
         forge_bitmaps_region_slot_def, forge_heap_stack_region_def,
         FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
         FORGE_HEAP_def, FORGE_STACKEND_def,
         FORGE_M3_EXIT_VENEER_def, FORGE_M3_INSTALL_VENEER_def,
         FORGE_M3_FFIBOOT_VENEER_def, FORGE_M3_FFISEND_VENEER_def,
         FORGE_M3_FFIRECV_VENEER_def, FORGE_M3_FFICOMMIT_VENEER_def]
  \\ blastLib.BBLAST_TAC
QED

(* ---- 2. Whole-Step Determinism, Peeling & Patch-Bytes Laws ---- *)

Theorem m3_whole_step_exit_stuck:
  ∀allow_err ec os s y.
    svc_exit_group_rel ec s ⇒ ¬m3_whole_step allow_err (os, s) y
Proof
  rpt strip_tac \\ PairCases_on `y`
  \\ gvs [svc_exit_group_rel_def, m3_whole_step_def, is_svc0_at_def]
QED

Theorem m3_whole_step_nrc_exit_stuck:
  ∀allow_err n ec os s y.
    svc_exit_group_rel ec s ∧ NRC (m3_whole_step allow_err) n (os, s) y ⇒
    n = 0 ∧ y = (os, s)
Proof
  rpt gen_tac \\ Cases_on `n` \\ simp [arithmeticTheory.NRC]
  \\ rpt strip_tac \\ metis_tac [m3_whole_step_exit_stuck]
QED

Theorem m3_det_run_imp_nrc:
  ∀k s s' allow_err os.
    det_run k s s' ⇒ NRC (m3_whole_step allow_err) k (os, s) (os, s')
Proof
  Induct_on `k` \\ simp [det_run_def, arithmeticTheory.NRC]
  \\ rpt strip_tac \\ qexists_tac `(os, s1)` \\ simp [m3_whole_step_def]
QED

Theorem m3_det_run_imp_rtc:
  ∀k s s' allow_err os.
    det_run k s s' ⇒ RTC (m3_whole_step allow_err) (os, s) (os, s')
Proof
  rpt strip_tac \\ drule m3_det_run_imp_nrc \\ metis_tac [arithmeticTheory.RTC_eq_NRC]
QED

Theorem m3_det_run_peel_nrc:
  ∀k s s' allow_err n ec os os_f ms_f.
    det_run k s s' ∧
    NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    k ≤ n ∧ NRC (m3_whole_step allow_err) (n - k) (os, s') (os_f, ms_f)
Proof
  Induct_on `k` \\ simp [det_run_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `n`
  >- (gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def])
  \\ gvs [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, m3_whole_step_def]
  \\ last_x_assum (qspecl_then [`s1`, `s'`, `allow_err`, `n'`, `ec`, `os`, `os_f`, `ms_f`] mp_tac)
  \\ simp []
QED

Theorem m3_whole_step_svc_det:
  (∀allow_err os s os' s'. is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 0w ⇒
     (m3_whole_step allow_err (os, s) (os', s') ⇔
      ∃rest. svc_read_fd_rel 0w allow_err os.inp s s' rest ∧ os' = os with inp := rest)) ∧
  (∀allow_err os s os' s'. is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 4w ⇒
     (m3_whole_step allow_err (os, s) (os', s') ⇔
      ∃rest. svc_read_fd_rel 4w allow_err os.key_in s s' rest ∧ os' = os with key_in := rest)) ∧
  (∀allow_err os s os' s'. is_svc0_at s ∧ s.REG 8w = 64w ∧ s.REG 0w = 1w ⇒
     (m3_whole_step allow_err (os, s) (os', s') ⇔
      ∃chunk. (if allow_err then svc_write_rel else svc_write_noerr_rel) s s' chunk ∧
              os' = os with out := os.out ++ chunk)) ∧
  (∀allow_err os s os' s'. is_svc0_at s ∧ s.REG 8w = 67w ⇒
     (m3_whole_step allow_err (os, s) (os', s') ⇔
      svc_pread64_rel allow_err os.disk s s' ∧ os' = os)) ∧
  (∀allow_err os s os' s'. is_svc0_at s ∧ s.REG 8w = 68w ⇒
     (m3_whole_step allow_err (os, s) (os', s') ⇔
      ∃disk'. svc_pwrite64_rel allow_err os.disk s s' disk' ∧ os' = os with disk := disk')) ∧
  (∀allow_err os s os' s'. is_svc0_at s ∧ s.REG 8w = 83w ⇒
     (m3_whole_step allow_err (os, s) (os', s') ⇔
      ∃dur'. svc_fdatasync_rel allow_err os.disk os.durable s s' dur' ∧ os' = os with durable := dur'))
Proof
  rpt conj_tac \\ rpt strip_tac \\ simp [m3_whole_step_def]
QED

Theorem patch_bytes_nil:
  ∀off buf. off ≤ LENGTH buf ⇒ patch_bytes off [] buf = buf
Proof
  rpt strip_tac \\ simp [patch_bytes_def, listTheory.TAKE_DROP]
QED

Theorem patch_bytes_append:
  ∀off c1 c2 buf.
    patch_bytes (off + LENGTH c1) c2 (patch_bytes off c1 buf) =
    patch_bytes off (c1 ++ c2) buf
Proof
  rpt gen_tac \\ simp [patch_bytes_def]
  \\ qabbrev_tac `p1 = if LENGTH buf < off then buf ++ REPLICATE (off - LENGTH buf) 0w else buf`
  \\ `off ≤ LENGTH p1` by (simp [Abbr `p1`] \\ rw [])
  \\ qabbrev_tac `d1 = TAKE off p1 ++ c1 ++ DROP (off + LENGTH c1) p1`
  \\ `off + LENGTH c1 ≤ LENGTH d1` by simp [Abbr `d1`, LENGTH_TAKE]
  \\ `¬(LENGTH d1 < off + LENGTH c1)` by decide_tac \\ simp []
  \\ `TAKE (off + LENGTH c1) d1 = TAKE off p1 ++ c1` by
       (simp [Abbr `d1`, TAKE_APPEND1, TAKE_APPEND2, LENGTH_TAKE, TAKE_LENGTH_ID_rwt])
  \\ `DROP (off + (LENGTH c1 + LENGTH c2)) d1 = DROP (off + (LENGTH c1 + LENGTH c2)) p1` by
       (irule listTheory.LIST_EQ \\ simp [Abbr `d1`, LENGTH_TAKE]
        \\ rpt strip_tac
        \\ `x + (off + (LENGTH c1 + LENGTH c2)) < LENGTH p1` by decide_tac
        \\ simp [EL_DROP, EL_APPEND2, LENGTH_TAKE]
        \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac)
  \\ simp []
QED

Theorem pad512_patch_bytes_slotA:
  ∀rec buf.
    LENGTH rec = 256 ⇒
    TAKE 256 (pad512 (patch_bytes 0 rec buf)) = rec ∧
    DROP 256 (pad512 (patch_bytes 0 rec buf)) = DROP 256 (pad512 buf)
Proof
  rpt strip_tac
  >- (irule listTheory.LIST_EQ \\ simp [pad512_def, patch_bytes_def, EL_TAKE, EL_APPEND1])
  \\ irule listTheory.LIST_EQ \\ simp [pad512_def, patch_bytes_def]
  \\ rpt strip_tac \\ simp [EL_DROP, EL_TAKE]
  \\ Cases_on `x + 256 < LENGTH buf`
  >- (simp [EL_APPEND1, EL_APPEND2, EL_DROP] \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac)
  \\ Cases_on `LENGTH buf < 256`
  >- (`DROP 256 buf = []` by simp [DROP_LENGTH_TOO_LONG]
      \\ simp [EL_APPEND2, EL_REPLICATE])
  \\ simp [EL_APPEND2, EL_REPLICATE]
QED

Theorem pad512_patch_bytes_slotB:
  ∀rec buf.
    LENGTH rec = 256 ⇒
    TAKE 256 (pad512 (patch_bytes 256 rec buf)) = TAKE 256 (pad512 buf) ∧
    DROP 256 (pad512 (patch_bytes 256 rec buf)) = rec
Proof
  rpt strip_tac
  \\ qabbrev_tac `p1 = if LENGTH buf < 256 then buf ++ REPLICATE (256 - LENGTH buf) 0w else buf`
  \\ `256 ≤ LENGTH p1` by (simp [Abbr `p1`] \\ rw [])
  >- (
    irule listTheory.LIST_EQ \\ simp [pad512_def, patch_bytes_def]
    \\ rpt strip_tac \\ simp [EL_TAKE, EL_APPEND1, LENGTH_TAKE]
    \\ simp [Abbr `p1`] \\ Cases_on `x < LENGTH buf` \\ rw [EL_APPEND1, EL_APPEND2, EL_REPLICATE])
  \\ irule listTheory.LIST_EQ \\ simp [pad512_def, patch_bytes_def]
  \\ rpt strip_tac \\ simp [EL_DROP, EL_TAKE, EL_APPEND1, EL_APPEND2, LENGTH_TAKE]
QED

(* ---- 3. Arithmetic & Register Lifting Helpers for forge_m3StepLib ---- *)

Theorem m3_restore_erase_record_upds:
  (∀s. restore (bits_of s) (erase s) = s) ∧
  (∀b s pc. restore b (s with PC := pc) = restore b s with PC := pc) ∧
  (∀b s r. restore b (s with REG := r) = restore b s with REG := r) ∧
  (∀b s m. restore b (s with MEM := m) = restore b s with MEM := m) ∧
  (∀b s ps. restore b (s with PSTATE := ps) = restore b s with PSTATE := ps) ∧
  (∀b s bh. restore b (s with branch_hint := bh) = restore b s with branch_hint := bh)
Proof
  rpt conj_tac \\ rpt gen_tac \\ TRY (PairCases_on `b`)
  \\ simp [restore_def, erase_def, bits_of_def, arm8Theory.arm8_state_component_equality,
           arm8Theory.TCR_EL1_component_equality, arm8Theory.SCTLRType_component_equality]
QED

Theorem m3_mem_dword_write8:
  ∀m (a:word64) (v:word64).
    mem_dword
      (m⦇a + 7w ↦ (63 >< 56) v; a + 6w ↦ (55 >< 48) v;
         a + 5w ↦ (47 >< 40) v; a + 4w ↦ (39 >< 32) v;
         a + 3w ↦ (31 >< 24) v; a + 2w ↦ (23 >< 16) v;
         a + 1w ↦ (15 >< 8) v;  a ↦ (7 >< 0) v⦈)
      a = v
Proof
  rpt strip_tac \\ simp [arm8_stepTheory.mem_dword_def, combinTheory.APPLY_UPDATE_THM]
  \\ blastLib.BBLAST_TAC
QED

Theorem m3_mem_dword_cong:
  ∀m1 m2 (a:word64).
    (∀i:word64. i <₊ 8w ⇒ m1 (a + i) = m2 (a + i)) ⇒
    mem_dword m1 a = mem_dword m2 a
Proof
  rpt strip_tac \\ simp [arm8_stepTheory.mem_dword_def]
  \\ `m1 a = m2 a ∧ m1 (a + 1w) = m2 (a + 1w) ∧ m1 (a + 2w) = m2 (a + 2w) ∧
      m1 (a + 3w) = m2 (a + 3w) ∧ m1 (a + 4w) = m2 (a + 4w) ∧
      m1 (a + 5w) = m2 (a + 5w) ∧ m1 (a + 6w) = m2 (a + 6w) ∧
      m1 (a + 7w) = m2 (a + 7w)` by
     (rpt conj_tac >- (first_x_assum (qspec_then `0w` mp_tac) \\ simp [])
      \\ first_x_assum irule \\ EVAL_TAC)
  \\ simp []
QED

Theorem m3_cmp_carry_k:
  ∀k (w:word64).
    1 ≤ k ∧ k < 18446744073709551616 ⇒
    (((if w2n w + (18446744073709551615 - k) + 1 < 18446744073709551616
       then w2n w + (18446744073709551615 - k) + 1
       else (w2n w + (18446744073709551615 - k) + 1) MOD 18446744073709551616) ≠
      w2n w + (18446744073709551615 - k) + 1) ⇔ k ≤ w2n w)
Proof
  rpt strip_tac
  \\ assume_tac (Q.ISPEC `w:word64` wordsTheory.w2n_lt) \\ fs [dimword_64]
  \\ Cases_on `k ≤ w2n w` \\ simp []
  \\ `w2n w + (18446744073709551615 - k) + 1 = 18446744073709551616 + (w2n w - k)` by decide_tac
  \\ simp [arithmeticTheory.ADD_MODULUS_LEFT]
QED

Theorem m3_cmp_zero_gt_cond:
  ∀w:word64.
    (BIT 63 (w2n w + 18446744073709551615 + 1) ⇔ word_msb w) ∧
    (BIT 63 (w2n w + 18446744073709551616) ⇔ word_msb w)
Proof
  gen_tac
  \\ `w2n w + 18446744073709551615 + 1 = w2n w + 18446744073709551616` by decide_tac
  \\ `BIT 63 (w2n w + 18446744073709551616) = BIT 63 (w2n w)` by
     (simp [bitTheory.BIT_def, bitTheory.BITS_THM2]
      \\ `w2n w + 18446744073709551616 = w2n w + 2 * 9223372036854775808` by decide_tac
      \\ pop_assum SUBST1_TAC
      \\ `2 ** 63 = 9223372036854775808` by EVAL_TAC
      \\ simp [arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.ADD_MODULUS_LEFT])
  \\ `BIT 63 (w2n w) ⇔ word_msb w` by
     (Cases_on `w` \\ simp [wordsTheory.word_msb_def, wordsTheory.word_index,
                            wordsTheory.w2n_n2w, dimword_64])
  \\ simp []
QED

Theorem m3_cmn_4_zero:
  ∀w:word64. (w + 4w = 0w) ⇔ (w = -4w)
Proof
  blastLib.BBLAST_TAC
QED

Theorem m3_extend_uxtx_0:
  ∀w:word64. ExtendValue (w, ExtendType_UXTX, 0) = w
Proof
  gen_tac
  \\ simp [arm8Theory.ExtendValue_def, arm8Theory.Extend_def, bitstringTheory.shiftl_def,
           bitstringTheory.shiftr_def, bitstringTheory.field_def,
           bitstringTheory.zero_extend_def, bitstringTheory.fixwidth_id_imp,
           listTheory.PAD_RIGHT, listTheory.TAKE_LENGTH_ID_rwt,
           bitstringTheory.length_w2v, bitstringTheory.v2w_w2v]
QED

Theorem m3_w2w_w2w_word8_word64:
  ∀b:word8. (w2w ((w2w b):word32):word64) = w2w b ∧ (w2w ((w2w b):word64):word8) = b
Proof
  blastLib.BBLAST_TAC
QED

Theorem m3_word_add_n2w_right:
  (∀(p:word64) a b. p + n2w a + n2w b = p + n2w (a + b)) ∧
  (∀(p:word64) n. p + 1w + n2w n = p + n2w (n + 1)) ∧
  (∀(p:word64) n. p + n2w n + 1w = p + n2w (n + 1))
Proof
  rpt strip_tac
  >- (REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w])
  >- (REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w] \\ simp [])
  \\ REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w]
QED

Theorem m3_word64_arith_step_helpers:
  (∀a b:word64. -1w * a + b = b - a) ∧
  (∀a b c:word64. a + (b + c) = b + (c + a))
Proof
  conj_tac \\ rpt gen_tac \\ blastLib.BBLAST_TAC
QED

Theorem m3_asm_write_bytearray_pointwise:
  ∀xs (p:word64) m1 m2 a.
    m1 a = m2 a ⇒
    asm_write_bytearray p xs m1 a = asm_write_bytearray p xs m2 a
Proof
  Induct \\ simp [miscTheory.asm_write_bytearray_def, combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac \\ IF_CASES_TAC \\ simp []
QED

(* ---- 4. M3 Leaf FFI Return Contract, Machine Config & Interference ---- *)

Definition m3_ffi_return_ok_slot_def:
  m3_ffi_return_ok_slot (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64)
                        (new_bytes:word8 list) (s:arm8_state) (s':arm8_state) ⇔
    arm8_ok (erase s') ∧
    sp_ok s' ∧
    bits_of s' = bits_of s ∧
    s'.SP_EL0 = s.SP_EL0 ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
    s'.PC = s.REG 30w ∧
    (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒
         s'.MEM a = asm_write_bytearray (s.REG 2w) new_bytes s.MEM a) ∧
    (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))
End

Definition mk_real_m3_ffi_if_slot_def:
  mk_real_m3_ffi_if_slot (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64)
                         (P : num -> num -> word8 list -> arm8_state -> arm8_state -> bool)
                         (k:num) (index:num, new_bytes:word8 list, s:arm8_state) : arm8_state =
    if ∃s'. P k index new_bytes s s' ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end new_bytes s s' then
      @s'. P k index new_bytes s s' ∧
           m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end new_bytes s s'
    else
      forge_canonical_ffi_post new_bytes s
End

Theorem forge_m3_mc_slot_mmio_min:
  ∀cb_end bm_buf_end n0 n1 n2 n3 ffi_if inst_if.
    mmio_pcs_min_index
      (forge_m3_mc_slot cb_end bm_buf_end
         [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if).ffi_names = SOME 4
Proof
  rpt gen_tac
  \\ simp [forge_m3_mc_slot_def, targetSemTheory.mmio_pcs_min_index_def]
  \\ DEEP_INTRO_TAC optionTheory.some_intro
  \\ conj_tac
  >- (rpt strip_tac \\ `x = 4` suffices_by simp []
      \\ CCONTR_TAC \\ `x < 4` by decide_tac
      \\ first_x_assum (qspec_then `x` mp_tac) \\ simp []
      \\ `x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3` by decide_tac \\ rveq \\ simp [])
  \\ simp [] \\ qexists_tac `4` \\ simp []
  \\ gen_tac \\ Cases_on `j` \\ simp []
  \\ Cases_on `n` \\ simp [] \\ Cases_on `n'` \\ simp [] \\ Cases_on `n` \\ simp []
QED

Theorem forge_m3_mc_slot_lo55:
  ∀cb_begin cb_end bm_buf_end ffi_names_l ffi_if inst_if.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    lo55 (forge_m3_mc_slot cb_end bm_buf_end ffi_names_l ffi_if inst_if)
Proof
  rpt strip_tac
  \\ drule m3_regions_disjoint_slot \\ strip_tac
  \\ simp [lo55_def, forge_m3_mc_slot_def,
           FORGE_M3_EXIT_VENEER_def, FORGE_M3_INSTALL_VENEER_def,
           FORGE_M3_FFIBOOT_VENEER_def, FORGE_M3_FFISEND_VENEER_def,
           FORGE_M3_FFIRECV_VENEER_def, FORGE_M3_FFICOMMIT_VENEER_def, untagged_def]
  \\ rpt strip_tac
  >- (first_x_assum drule \\ simp [untagged_def])
  \\ rveq \\ EVAL_TAC
QED

Theorem forge_m3_mc_slot_start_pc_ok:
  ∀cb_begin cb_end bm_buf_end n0 n1 n2 n3 ffi_if inst_if.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    start_pc_ok
      (forge_m3_mc_slot cb_end bm_buf_end
         [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if)
      FORGE_M3_CAKE_MAIN
Proof
  rpt strip_tac
  \\ fs [m3_slot_layout_ok_def]
  \\ simp [targetSemTheory.start_pc_ok_def, forge_m3_mc_slot_def,
           FORGE_M3_CAKE_MAIN_def, FORGE_M3_EXIT_VENEER_def, FORGE_M3_INSTALL_VENEER_def,
           FORGE_M3_FFIBOOT_VENEER_def, FORGE_M3_FFISEND_VENEER_def,
           FORGE_M3_FFIRECV_VENEER_def, FORGE_M3_FFICOMMIT_VENEER_def,
           lab_to_targetTheory.ffi_offset_def]
  \\ rpt conj_tac
  >- (simp [forge_m3_prog_addresses_def, forge_m3_code_region_def, forge_bitmaps_region_slot_def,
            forge_heap_stack_region_def, FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def,
            FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ fs [FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
             wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
  >- (simp [forge_m3_prog_addresses_def, forge_m3_code_region_def, forge_bitmaps_region_slot_def,
            forge_heap_stack_region_def, FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def,
            FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ fs [FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
             wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
  \\ qexists_tac `4`
  \\ rpt conj_tac
  >- (mp_tac (Q.SPECL [`cb_end`, `bm_buf_end`, `n0`, `n1`, `n2`, `n3`, `ffi_if`, `inst_if`]
                      forge_m3_mc_slot_mmio_min)
      \\ simp [forge_m3_mc_slot_def])
  >- (gen_tac \\ strip_tac
      \\ `index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3` by decide_tac \\ rveq
      \\ simp [miscTheory.find_index_def, forge_m3_prog_addresses_def, forge_m3_code_region_def,
               forge_bitmaps_region_slot_def, forge_heap_stack_region_def, FORGE_M3_CAKE_MAIN_def,
               FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
               FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ fs [FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
             wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
  \\ rpt strip_tac \\ decide_tac
QED

Theorem mk_real_m3_ffi_if_slot_ok:
  ∀cb_begin cb_end bm_buf_end cbspace n0 n1 n2 n3 B P.
    m3_real_interfer_ok_slot cb_end bm_buf_end cbspace
      [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] B
      (mk_real_m3_ffi_if_slot cb_begin cb_end bm_buf_end P) forge_real_install_if
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ simp [m3_real_interfer_ok_slot_def, LET_THM]
  \\ rpt conj_tac
  >- (
    simp [targetSemTheory.ffi_interfer_ok_def, forge_m3_mc_slot_def, arm8_target_def,
          arm8_config_def, mk_real_m3_ffi_if_slot_def]
    \\ rpt gen_tac \\ strip_tac
    \\ `i = 4` by
       (qpat_x_assum `mmio_pcs_min_index _ = SOME i` mp_tac
        \\ mp_tac (Q.SPECL [`cb_end`, `bm_buf_end`, `n0`, `n1`, `n2`, `n3`, `ARB`, `ARB`]
                           forge_m3_mc_slot_mmio_min)
        \\ simp [forge_m3_mc_slot_def])
    \\ rveq \\ simp []
    \\ disch_then strip_assume_tac
    \\ `t1.regs 30 = ms2.REG 30w ∧ t1.regs 2 = ms2.REG 2w ∧
        (∀a. a ∈ t1.mem_domain ⇒ t1.mem a = ms2.MEM a) ∧
        (∀r. r < 32 ∧ ¬MEM r [18;26;31] ⇒ t1.regs r = ms2.REG (n2w r)) ∧
        arm8_ok ms2` by
       fs [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
    \\ IF_CASES_TAC
    >- (
      SELECT_ELIM_TAC \\ conj_tac >- metis_tac []
      \\ rpt strip_tac
      \\ fs [m3_ffi_return_ok_slot_def, erase_fields, restore_def]
      \\ rpt strip_tac \\ simp [] \\ irule m3_asm_write_bytearray_pointwise \\ simp [])
    \\ simp [forge_canonical_ffi_post_def, erase_fields, arm8_ok_erase, restore_def]
    \\ fs [arm8_ok_def]
    \\ rpt strip_tac \\ irule m3_asm_write_bytearray_pointwise \\ simp [])
  >- (
    simp [targetSemTheory.install_interfer_ok_def, forge_m3_mc_slot_def, arm8_target_def,
          arm8_config_def, forge_real_install_if_def, erase_fields, arm8_ok_erase, restore_def]
    \\ rpt strip_tac
    \\ `t1.regs 30 = ms2.REG 30w ∧ t1.regs 2 = ms2.REG 2w ∧
        (∀a. a ∈ t1.mem_domain ⇒ t1.mem a = ms2.MEM a) ∧
        (∀r. r < 32 ∧ ¬MEM r [18;26;31] ⇒ t1.regs r = ms2.REG (n2w r)) ∧
        arm8_ok ms2` by
       fs [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
    \\ simp [arm8_ok_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_def]
    \\ rpt conj_tac
    >- (rpt strip_tac \\ irule m3_asm_write_bytearray_pointwise \\ simp [])
    \\ rpt strip_tac \\ rveq \\ simp [combinTheory.APPLY_UPDATE_THM])
  >- (
    rpt gen_tac \\ strip_tac \\ simp [mk_real_m3_ffi_if_slot_def]
    \\ IF_CASES_TAC
    >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac []
        \\ rpt strip_tac \\ fs [m3_ffi_return_ok_slot_def])
    \\ simp [forge_canonical_ffi_post_def, bits_of_def] \\ fs [bits_of_def])
  \\ rpt strip_tac \\ simp [forge_real_install_if_def, bits_of_def] \\ fs [bits_of_def]
QED

Theorem m3_real_interfer_ok_slot_imp_erase_ok:
  ∀cb_end bm_buf_end cbspace n0 n1 n2 n3 B ffi_if inst_if.
    m3_real_interfer_ok_slot cb_end bm_buf_end cbspace
      [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] B ffi_if inst_if ⇒
    ffi_interfer_ok FORGE_M3_CAKE_MAIN
      (erase_mc B (forge_m3_mc_slot cb_end bm_buf_end
                     [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if)) ∧
    install_interfer_ok FORGE_M3_CAKE_MAIN cbspace
      (erase_mc B (forge_m3_mc_slot cb_end bm_buf_end
                     [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if)) ∧
    interference_ok
      (erase_mc B (forge_m3_mc_slot cb_end bm_buf_end
                     [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if)).next_interfer
      ((erase_mc B (forge_m3_mc_slot cb_end bm_buf_end
                      [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if)).target.proj
         (forge_m3_prog_addresses cb_end bm_buf_end))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ simp [m3_real_interfer_ok_slot_def, LET_THM] \\ strip_tac
  \\ rpt conj_tac
  >- (
    simp [targetSemTheory.ffi_interfer_ok_def, erase_mc_def, forge_m3_mc_slot_def,
          arm8_target_exact_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ rpt gen_tac \\ strip_tac
    \\ `mmio_pcs_min_index [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] = SOME 4` by
         (mp_tac (Q.SPECL [`cb_end`, `bm_buf_end`, `n0`, `n1`, `n2`, `n3`, `ARB`, `ARB`]
                          forge_m3_mc_slot_mmio_min)
          \\ simp [forge_m3_mc_slot_def])
    \\ `i = 4` by fs [] \\ rveq \\ simp []
    \\ strip_tac
    \\ qpat_x_assum `ffi_interfer_ok _ _`
         (mp_tac o Q.SPECL [`ms2`, `k`, `index`, `new_bytes`, `t1`, `bytes`, `bytes2`, `4`] o
          REWRITE_RULE [targetSemTheory.ffi_interfer_ok_def])
    \\ simp [forge_m3_mc_slot_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ impl_tac
    >- fs [targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
           asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def,
           arm8_config_def, forge_m3_mc_slot_def]
    \\ strip_tac \\ fs [erase_fields]
    \\ `(ffi_if k (index, new_bytes, restore (B0,B1,B2) ms2)).SP_EL0 = ms2.SP_EL0` by
         (qpat_x_assum `∀k i bs s. bits_of s = _ ⇒ _`
            (qspecl_then [`k`, `index`, `new_bytes`, `restore (B0,B1,B2) ms2`] mp_tac)
          \\ simp [bits_of_restore, restore_def])
    \\ qpat_x_assum `target_state_rel _ _ _` mp_tac
    \\ simp [asmPropsTheory.target_state_rel_def]
    \\ rpt strip_tac \\ qpat_x_assum `∀r. _ ⇒ (ffi_if _ _).REG _ = _` irule \\ simp [])
  >- (
    simp [targetSemTheory.install_interfer_ok_def, erase_mc_def, forge_m3_mc_slot_def,
          arm8_target_exact_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ rpt gen_tac \\ strip_tac
    \\ qpat_x_assum `install_interfer_ok _ _ _`
         (mp_tac o Q.SPECL [`ms2`, `t1`, `k`, `bytes`] o
          REWRITE_RULE [targetSemTheory.install_interfer_ok_def])
    \\ simp [forge_m3_mc_slot_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ impl_tac
    >- gvs [targetSemTheory.read_ffi_bytearray_def, asmPropsTheory.target_state_rel_def,
            arm8_target_exact_def, arm8_target_def, arm8_config_def, forge_m3_mc_slot_def]
    \\ strip_tac \\ fs [erase_fields]
    \\ `(inst_if k (bytes, restore (B0,B1,B2) ms2)).SP_EL0 = ms2.SP_EL0` by
         (qpat_x_assum `∀k bs s. bits_of s = _ ⇒ _`
            (qspecl_then [`k`, `bytes`, `restore (B0,B1,B2) ms2`] mp_tac)
          \\ simp [bits_of_restore, restore_def])
    \\ qpat_x_assum `target_state_rel _ _ _` mp_tac
    \\ simp [asmPropsTheory.target_state_rel_def]
    \\ rpt strip_tac \\ qpat_x_assum `∀r. _ ⇒ (inst_if _ _).REG _ = _` irule \\ simp [])
  \\ simp [asmPropsTheory.interference_ok_def, erase_mc_def, forge_m3_mc_slot_def]
QED

Theorem m3_erase_mc_conf_ok_slot:
  ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_conf_ok (erase_mc B (forge_m3_mc_slot cb_end bm_end fnames ffi_if inst_if))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ `mc_conf_ok (forge_m3_mc_slot cb_end bm_end fnames ffi_if inst_if)` by (
       irule arm8_configProofTheory.arm8_machine_config_ok
       \\ simp [arm8_configProofTheory.is_arm8_machine_config_def, forge_m3_mc_slot_def])
  \\ pop_assum mp_tac
  \\ simp [lab_to_targetProofTheory.mc_conf_ok_def, erase_mc_def, forge_m3_mc_slot_def,
           arm8_target_exact_encoder_correct]
  \\ simp [arm8_target_exact_def]
QED

Theorem m3_erase_mc_init_ok_slot:
  ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_init_ok arm8_config arm8_backend_config
      (erase_mc B (forge_m3_mc_slot cb_end bm_end fnames ffi_if inst_if))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ `mc_init_ok arm8_config arm8_backend_config (forge_m3_mc_slot cb_end bm_end fnames ffi_if inst_if)` by (
       irule arm8_configProofTheory.arm8_init_ok
       \\ simp [arm8_configProofTheory.is_arm8_machine_config_def, forge_m3_mc_slot_def])
  \\ pop_assum mp_tac
  \\ simp [backendProofTheory.mc_init_ok_def, erase_mc_def, forge_m3_mc_slot_def,
           arm8_target_exact_def]
QED

(* ---- 5. Constructive M3 Non-Vacuity Witness ---- *)

Theorem m3_words32_in_mem_pointwise[local]:
  ∀ws (base:word64) (m:word64 -> word8).
    (∀i. i < LENGTH ws ⇒
      m (base + n2w (4 * i))     = (7 >< 0)   (EL i ws) ∧
      m (base + n2w (4 * i + 1)) = (15 >< 8)  (EL i ws) ∧
      m (base + n2w (4 * i + 2)) = (23 >< 16) (EL i ws) ∧
      m (base + n2w (4 * i + 3)) = (31 >< 24) (EL i ws)) ⇒
    words32_in_mem base ws m
Proof
  Induct \\ simp [words32_in_mem_def]
  \\ rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ first_x_assum irule \\ gen_tac \\ strip_tac
  \\ first_x_assum (qspec_then `SUC i` mp_tac)
  \\ simp [word_add_n2w_n2w, arithmeticTheory.MULT_SUC, arithmeticTheory.ADD_CLAUSES]
QED

Theorem m3_read_bytearray_pointwise[local]:
  ∀(bs:word8 list) (a:word64) (dm:word64 set) (m:word64 -> word8).
    (∀i. i < LENGTH bs ⇒ a + n2w i ∈ dm ∧ m (a + n2w i) = EL i bs) ⇒
    read_bytearray a (LENGTH bs) (λx. if x ∈ dm then SOME (m x) else NONE) = SOME bs
Proof
  Induct \\ simp [miscTheory.read_bytearray_def]
  \\ rpt strip_tac
  \\ `a ∈ dm ∧ m a = h` by (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ simp []
  \\ `read_bytearray (a + 1w) (LENGTH bs) (λx. if x ∈ dm then SOME (m x) else NONE) = SOME bs` by (
       first_x_assum irule \\ gen_tac \\ strip_tac
       \\ first_x_assum (qspec_then `SUC i` mp_tac) \\ simp [word_add_1w_n2w])
  \\ simp []
QED

Theorem m3_dword_bytes_reassemble[local]:
  ∀m (a:word64) (w:word64).
    m a = (7 >< 0) w ∧ m (a + 1w) = (15 >< 8) w ∧ m (a + 2w) = (23 >< 16) w ∧
    m (a + 3w) = (31 >< 24) w ∧ m (a + 4w) = (39 >< 32) w ∧ m (a + 5w) = (47 >< 40) w ∧
    m (a + 6w) = (55 >< 48) w ∧ m (a + 7w) = (63 >< 56) w ⇒
    mem_dword m a = w
Proof
  rpt strip_tac \\ simp [arm8_stepTheory.mem_dword_def] \\ blastLib.BBLAST_TAC
QED

Theorem forge_m3_slot_nonvacuous:
  ∀(code:word8 list) (data:num list).
    0 < LENGTH code ∧ LENGTH code ≤ FORGE_M3_MAX_CODE_BYTES ∧
    LENGTH data ≤ FORGE_MAX_BITMAP_WORDS ⇒
    ∃ms0:arm8_state.
      forge_m3_slot_loaded code data ms0 ∧
      ms0.TCR_EL1.TBI0 ∧
      ¬ms0.TCR_EL1.TBI1 ∧
      ms0.SCTLR_EL1.SA0 ∧
      aligned 4 ms0.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `cb_begin = m3_slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = m3_slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac m3_slot_params_props
  \\ impl_tac >- simp []
  \\ simp [LET_THM] \\ strip_tac
  \\ `LENGTH code ≤ 261936 ∧ LENGTH data ≤ 8189` by
       fs [FORGE_M3_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
  \\ qabbrev_tac `m0 = λa:word64.
       if FORGE_M3_CAKE_MAIN ≤₊ a ∧ a <₊ cb_begin then
         EL (w2n (a - FORGE_M3_CAKE_MAIN)) code
       else if FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ bm_end then
         let off = w2n (a - FORGE_CAKE_BITMAPS) in
         let w : word64 = n2w (EL (off DIV 8) data) in
           if off MOD 8 = 0 then (7 >< 0) w
           else if off MOD 8 = 1 then (15 >< 8) w
           else if off MOD 8 = 2 then (23 >< 16) w
           else if off MOD 8 = 3 then (31 >< 24) w
           else if off MOD 8 = 4 then (39 >< 32) w
           else if off MOD 8 = 5 then (47 >< 40) w
           else if off MOD 8 = 6 then (55 >< 48) w
           else (63 >< 56) w
       else if FORGE_M3_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_M3_CAKE_MAIN then
         let off = w2n (a - FORGE_M3_VENEERS_BASE) in
         let w = EL (off DIV 4) (forge_m3_slot_veneers cb_begin cb_end bm_end) in
           if off MOD 4 = 0 then (7 >< 0) w
           else if off MOD 4 = 1 then (15 >< 8) w
           else if off MOD 4 = 2 then (23 >< 16) w
           else (31 >< 24) w
       else if FORGE_M3_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_M3_SHIM_END then
         let off = w2n (a - FORGE_M3_SHIM_BASE) in
         let w = EL (off DIV 4) forge_shim_airlock_words in
           if off MOD 4 = 0 then (7 >< 0) w
           else if off MOD 4 = 1 then (15 >< 8) w
           else if off MOD 4 = 2 then (23 >< 16) w
           else (31 >< 24) w
       else 0w`
  \\ qexists_tac `(ARB:arm8_state) with
       <| PSTATE    := ((ARB:ProcState) with EL := 0w);
          SCTLR_EL1 := ((ARB:SCTLRType) with <| SA0 := T; E0E := F |>);
          TCR_EL1   := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
          SP_EL0    := FORGE_STACKEND;
          exception := NoException;
          PC        := FORGE_M3_SHIM_BASE;
          MEM       := m0 |>`
  \\ simp [forge_m3_slot_loaded_def, LET_THM, arm8_ok_erase, sp_ok_def]
  \\ rpt conj_tac
  >- (simp [FORGE_M3_SHIM_BASE_def] \\ EVAL_TAC)
  >- (simp [FORGE_STACKEND_def] \\ EVAL_TAC)
  >- (
    simp [m3_shim_loaded_slot_def]
    \\ conj_tac
    >- (
      irule m3_words32_in_mem_pointwise \\ rpt strip_tac \\ fs [m3_veneers_len]
      \\ `∀j. j < 4 ⇒
            (FORGE_M3_VENEERS_BASE + n2w (4 * i + j)) <₊ FORGE_M3_CAKE_MAIN ∧
            FORGE_M3_VENEERS_BASE ≤₊ (FORGE_M3_VENEERS_BASE + n2w (4 * i + j)) ∧
            ¬(FORGE_M3_CAKE_MAIN ≤₊ (FORGE_M3_VENEERS_BASE + n2w (4 * i + j))) ∧
            ¬(FORGE_CAKE_BITMAPS ≤₊ (FORGE_M3_VENEERS_BASE + n2w (4 * i + j))) ∧
            w2n ((FORGE_M3_VENEERS_BASE + n2w (4 * i + j)) - FORGE_M3_VENEERS_BASE) = 4 * i + j` by (
           rpt strip_tac
           \\ `0x00400000 + (4 * i + j) < 18446744073709551616 ∧ 4 * i + j < 18446744073709551616` by decide_tac
           \\ fs [wordsTheory.WORD_ADD_SUB2, w2n_n2w_64]
           \\ fs [FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def, FORGE_CAKE_BITMAPS_def, word64_add_lo_ls]
           \\ decide_tac)
      \\ rpt conj_tac
      \\ (simp [Abbr `m0`]
          \\ first_x_assum (fn th =>
               mp_tac (Q.SPEC `0` th) \\ mp_tac (Q.SPEC `1` th) \\
               mp_tac (Q.SPEC `2` th) \\ mp_tac (Q.SPEC `3` th))
          \\ simp [div_mod_4]))
    \\ irule m3_words32_in_mem_pointwise \\ rpt strip_tac \\ fs [m3_shim_words_len]
    \\ `∀j. j < 4 ⇒
          FORGE_M3_SHIM_BASE ≤₊ (FORGE_M3_SHIM_BASE + n2w (4 * i + j)) ∧
          (FORGE_M3_SHIM_BASE + n2w (4 * i + j)) <₊ FORGE_M3_SHIM_END ∧
          ¬((FORGE_M3_SHIM_BASE + n2w (4 * i + j)) <₊ cb_begin) ∧
          ¬(FORGE_CAKE_BITMAPS ≤₊ (FORGE_M3_SHIM_BASE + n2w (4 * i + j))) ∧
          ¬((FORGE_M3_SHIM_BASE + n2w (4 * i + j)) <₊ FORGE_M3_CAKE_MAIN) ∧
          w2n ((FORGE_M3_SHIM_BASE + n2w (4 * i + j)) - FORGE_M3_SHIM_BASE) = 4 * i + j` by (
         rpt strip_tac
         \\ `0x00450000 + (4 * i + j) < 18446744073709551616 ∧ 4 * i + j < 18446744073709551616` by decide_tac
         \\ `w2n (FORGE_M3_SHIM_BASE + n2w (4 * i + j)) = 0x00450000 + (4 * i + j)` by
              simp [FORGE_M3_SHIM_BASE_def, wordsTheory.word_add_n2w, w2n_n2w_64]
         \\ fs [wordsTheory.WORD_ADD_SUB2, w2n_n2w_64, wordsTheory.WORD_LO, wordsTheory.WORD_LS,
                FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def, FORGE_M3_CAKE_MAIN_def, FORGE_CAKE_BITMAPS_def]
         \\ decide_tac)
    \\ rpt conj_tac
    \\ (simp [Abbr `m0`]
        \\ first_x_assum (fn th =>
             mp_tac (Q.SPEC `0` th) \\ mp_tac (Q.SPEC `1` th) \\
             mp_tac (Q.SPEC `2` th) \\ mp_tac (Q.SPEC `3` th))
        \\ simp [div_mod_4]))
  >- (
    irule m3_read_bytearray_pointwise \\ gen_tac \\ strip_tac \\ fs []
    \\ `0x004000D0 + i < 18446744073709551616 ∧ i < 18446744073709551616` by decide_tac
    \\ `w2n (FORGE_M3_CAKE_MAIN + n2w i) = 0x004000D0 + i` by
         simp [FORGE_M3_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64]
    \\ conj_tac
    >- (
      fs [forge_m3_prog_addresses_def, forge_m3_code_region_def, FORGE_M3_CAKE_MAIN_def,
          wordsTheory.WORD_LO, wordsTheory.WORD_LS]
      \\ decide_tac)
    \\ fs [Abbr `m0`, wordsTheory.WORD_ADD_SUB2, w2n_n2w_64, wordsTheory.WORD_LO, wordsTheory.WORD_LS,
           FORGE_M3_CAKE_MAIN_def]
    \\ decide_tac)
  >- (
    rpt strip_tac \\ fs []
    \\ irule m3_dword_bytes_reassemble
    \\ `∀j. j < 8 ⇒
          FORGE_CAKE_BITMAPS ≤₊ (FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) ∧
          (FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) <₊ bm_end ∧
          ¬((FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) <₊ cb_begin) ∧
          w2n ((FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) - FORGE_CAKE_BITMAPS) = 8 * i + j` by (
         gen_tac \\ strip_tac
         \\ `0x00460018 + (8 * i + j) < 18446744073709551616 ∧ 8 * i + j < 18446744073709551616` by decide_tac
         \\ qabbrev_tac `ad = FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j`
         \\ `w2n ad = 0x00460018 + (8 * i + j)` by
              simp [Abbr `ad`, word_add_n2w_n2w, FORGE_CAKE_BITMAPS_def, wordsTheory.word_add_n2w, w2n_n2w_64]
         \\ `w2n (ad - FORGE_CAKE_BITMAPS) = 8 * i + j` by
              simp [Abbr `ad`, word_add_n2w_n2w, wordsTheory.WORD_ADD_SUB2, w2n_n2w_64]
         \\ `8 * LENGTH data + 0x00460018 = w2n bm_end` by (
              qpat_x_assum `8 * LENGTH data + w2n FORGE_CAKE_BITMAPS = w2n bm_end` mp_tac
              \\ PURE_REWRITE_TAC [FORGE_CAKE_BITMAPS_def]
              \\ CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV wordsLib.WORD_EVAL_CONV)) \\ simp [])
         \\ `LENGTH code + 0x004000D0 = w2n cb_begin` by (
              qpat_x_assum `LENGTH code + w2n FORGE_M3_CAKE_MAIN = w2n cb_begin` mp_tac
              \\ PURE_REWRITE_TAC [FORGE_M3_CAKE_MAIN_def]
              \\ CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV wordsLib.WORD_EVAL_CONV)) \\ simp [])
         \\ simp [wordsTheory.WORD_LO, wordsTheory.WORD_LS, FORGE_CAKE_BITMAPS_def, dimword_64]
         \\ decide_tac)
    \\ `FORGE_CAKE_BITMAPS ≤₊ (FORGE_CAKE_BITMAPS + n2w (8 * i)) ∧
        (FORGE_CAKE_BITMAPS + n2w (8 * i)) <₊ bm_end ∧
        ¬((FORGE_CAKE_BITMAPS + n2w (8 * i)) <₊ cb_begin) ∧
        w2n ((FORGE_CAKE_BITMAPS + n2w (8 * i)) - FORGE_CAKE_BITMAPS) = 8 * i` by (
         first_x_assum (qspec_then `0` mp_tac) \\ simp [])
    \\ rpt conj_tac
    \\ (simp [Abbr `m0`]
        \\ first_x_assum (fn th =>
             EVERY (map (fn k => mp_tac (Q.SPEC k th)) [`1`, `2`, `3`, `4`, `5`, `6`, `7`]))
        \\ simp [div_mod_8]))
  \\ simp [FORGE_STACKEND_def] \\ EVAL_TAC
QED
