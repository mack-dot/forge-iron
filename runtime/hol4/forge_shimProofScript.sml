(*
  Forge Reusable Runtime: Parameterized 256 KB Slot ARM64 Veneers & Raw Linux
  Syscall Shim Proof (Frozen, Kernel-Agnostic; Supports Both 16B & 64B Frames).

  Proves real L3 ARMv8 instruction semantics (via arm8_stepLib + forge_arm8Erasure)
  for ANY compiled CakeML kernel fitting inside the 256 KB RX code slot
  [0x4000B0..0x440000) with bitmaps inside [0x460018..0x470000) and fixed
  _start = 0x450000:
    1. Symbolic ADRP x2 + ADD x2 + STR x2 header proofs (real_step_adrp_x2,
       real_step_add_x2) covering arbitrary (cb_begin, cb_end, bm_buf_end).
    2. 43-step ELF startup proof (_start -> cml_main -> cake_main) for both
       forge_shim16_words and forge_shim64_words.
    3. Exit (0w/1w) and Install (2w) universal whole-step proofs.
    4. Parameterized universal + forward-liveness Linux svc #0 proofs for BOTH:
         - 16-byte frames (ffirecv16_* / ffisend16_*, used by M1 counter)
         - 64-byte frames (ffirecv64_* / ffisend64_*, used by M2+ kernels)
       covering arbitrary partial reads/writes, EINTR retries, EOF, truncated
       frames, and buffer-length totality.
    5. Parameterized targetSem$ffi_interfer_ok, install_interfer_ok, start_pc_ok,
       lo55, and real_interfer_ok_slot_imp_erase_ok for forge_mc_slot.
*)
Theory forge_shimProof
Ancestors
  words arithmetic list combin pred_set relation
  arm8 arm8_step arm8_target arm8_config arm8_configProof
  asmProps targetSem misc
  forge_runtimeSpec forge_arm8Erasure
Libs
  preamble blastLib wordsLib arm8_stepLib

(* ---- 1. Memory Congruence & Parameterized Slot Disjointness ---- *)

Definition shim_common_words_ok_def:
  shim_common_words_ok (shim_ws:word32 list) ⇔
    LENGTH shim_ws = 80 ∧
    TAKE 16 shim_ws = TAKE 16 forge_shim16_words ∧
    DROP 71 shim_ws = DROP 71 forge_shim16_words
End

Theorem shim16_common_words_ok:
  shim_common_words_ok forge_shim16_words
Proof
  simp [shim_common_words_ok_def, forge_shim16_words_def]
QED

Theorem shim64_common_words_ok:
  shim_common_words_ok forge_shim64_words
Proof
  simp [shim_common_words_ok_def, forge_shim16_words_def, forge_shim64_words_def]
QED

Theorem words32_in_mem_cong:
  ∀ws base m1 m2.
    (∀a. base ≤₊ a ∧ a <₊ base + n2w (4 * LENGTH ws) ⇒ m1 a = m2 a) ∧
    w2n base + 4 * LENGTH ws < dimword (:64) ⇒
    (words32_in_mem base ws m1 ⇔ words32_in_mem base ws m2)
Proof
  Induct \\ simp [words32_in_mem_def] \\ rpt strip_tac
  \\ qabbrev_tac `b = w2n base`
  \\ `base = n2w b` by simp [Abbr `b`]
  \\ pop_assum SUBST_ALL_TAC
  \\ `b < 18446744073709551616` by fs [dimword_64]
  \\ `m1 (n2w b) = m2 (n2w b) ∧ m1 (n2w b + 1w) = m2 (n2w b + 1w) ∧
      m1 (n2w b + 2w) = m2 (n2w b + 2w) ∧ m1 (n2w b + 3w) = m2 (n2w b + 3w)` by
     (rpt conj_tac \\ first_x_assum irule
      \\ simp [WORD_LS, WORD_LO, word_add_n2w, w2n_n2w, dimword_64] \\ fs [dimword_64])
  \\ `words32_in_mem (n2w b + 4w) ws m1 ⇔ words32_in_mem (n2w b + 4w) ws m2` by
     (first_x_assum irule \\ conj_tac
      >- (rpt strip_tac \\ first_x_assum irule
          \\ qpat_x_assum `_ ≤₊ a` mp_tac \\ qpat_x_assum `a <₊ _` mp_tac
          \\ simp [WORD_LS, WORD_LO, word_add_n2w, w2n_n2w, dimword_64, arithmeticTheory.MULT_SUC])
      \\ simp [word_add_n2w, w2n_n2w, dimword_64] \\ fs [dimword_64])
  \\ simp []
QED

Theorem words32_in_mem_append[local]:
  ∀xs ys base m.
    words32_in_mem base (xs ++ ys) m ⇔
    words32_in_mem base xs m ∧ words32_in_mem (base + n2w (4 * LENGTH xs)) ys m
Proof
  Induct \\ simp [words32_in_mem_def]
  \\ rpt gen_tac
  \\ `base + 4w + n2w (4 * LENGTH xs) = base + n2w (4 * SUC (LENGTH xs))` by
       (REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w, arithmeticTheory.MULT_SUC]
        \\ simp [])
  \\ pop_assum (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ simp [CONJ_ASSOC]
QED

Theorem shim_loaded_slot_common_bytes[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end m.
    shim_common_words_ok shim_ws ∧ shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end m ⇒
    words32_in_mem FORGE_SHIM_BASE (TAKE 16 forge_shim16_words) m ∧
    words32_in_mem 0x0045011Cw (DROP 71 forge_shim16_words) m
Proof
  rpt gen_tac \\ strip_tac
  \\ fs [shim_common_words_ok_def, shim_loaded_slot_def]
  \\ conj_tac
  >- (
    `shim_ws = TAKE 16 shim_ws ++ DROP 16 shim_ws` by simp [listTheory.TAKE_DROP]
    \\ qpat_x_assum `words32_in_mem FORGE_SHIM_BASE shim_ws m` mp_tac
    \\ pop_assum (fn th => ONCE_REWRITE_TAC [th])
    \\ simp [words32_in_mem_append])
  \\ `shim_ws = TAKE 71 shim_ws ++ DROP 71 shim_ws` by simp [listTheory.TAKE_DROP]
  \\ `LENGTH (TAKE 71 shim_ws) = 71` by simp []
  \\ `FORGE_SHIM_BASE + 284w = 0x0045011Cw` by (simp [FORGE_SHIM_BASE_def] \\ EVAL_TAC)
  \\ qpat_x_assum `words32_in_mem FORGE_SHIM_BASE shim_ws m` mp_tac
  \\ pop_assum (fn ath => pop_assum (fn lth => pop_assum (fn sth =>
       ONCE_REWRITE_TAC [sth] \\ simp [words32_in_mem_append, lth, ath])))
QED

Theorem shim_loaded_slot_cong:
  ∀shim_ws cb_begin cb_end bm_buf_end m1 m2.
    LENGTH shim_ws = 80 ∧
    (∀a. a ∈ forge_shim_code_region ⇒ m1 a = m2 a) ⇒
    (shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end m1 ⇔
     shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end m2)
Proof
  rpt strip_tac
  \\ simp [shim_loaded_slot_def]
  \\ `LENGTH (forge_slot_veneers cb_begin cb_end bm_buf_end) = 44` by simp [forge_slot_veneers_def]
  \\ `words32_in_mem FORGE_VENEERS_BASE (forge_slot_veneers cb_begin cb_end bm_buf_end) m1 ⇔
      words32_in_mem FORGE_VENEERS_BASE (forge_slot_veneers cb_begin cb_end bm_buf_end) m2` by
     (irule words32_in_mem_cong
      \\ simp [FORGE_VENEERS_BASE_def, dimword_64]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def])
  \\ `words32_in_mem FORGE_SHIM_BASE shim_ws m1 ⇔
      words32_in_mem FORGE_SHIM_BASE shim_ws m2` by
     (irule words32_in_mem_cong
      \\ simp [FORGE_SHIM_BASE_def, dimword_64]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs [forge_shim_code_region_def, FORGE_SHIM_BASE_def, FORGE_SHIM_END_def])
  \\ simp []
QED

Theorem shim_loaded_slot_update[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end m a b.
    LENGTH shim_ws = 80 ∧ a ∉ forge_shim_code_region ⇒
    (shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end (m⦇a ↦ b⦈) ⇔
     shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end m)
Proof
  rpt strip_tac \\ irule shim_loaded_slot_cong
  \\ simp [combinTheory.APPLY_UPDATE_THM] \\ rpt strip_tac \\ rw [] \\ fs []
QED

Theorem untagged_lt_8m[local]:
  ∀a:word64. a <₊ 0x00800000w ⇒ untagged a
Proof
  simp [untagged_def] \\ blastLib.BBLAST_TAC
QED

Theorem forge_regions_disjoint_slot:
  ∀cb_begin cb_end bm_buf_end.
    slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    (∀a. a ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_rx_tmp_region ⇒
         a ∉ forge_prog_addresses_slot cb_end bm_buf_end ∧ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_cml_ptrs_region ⇒
         a ∉ forge_prog_addresses_slot cb_end bm_buf_end ∧ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_heap_hdr_region ⇒
         a ∉ forge_cml_ptrs_region ∧ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒ untagged a) ∧
    (∀a. a ∈ forge_shim_code_region ⇒ untagged a)
Proof
  rpt gen_tac \\ strip_tac
  \\ fs [slot_layout_ok_def, forge_prog_addresses_slot_def, forge_code_region_slot_def,
         forge_bitmaps_region_slot_def, forge_heap_stack_region_def,
         forge_shim_code_region_def, forge_rx_tmp_region_def,
         forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
         FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def,
         FORGE_SHIM_BASE_def, FORGE_SHIM_END_def, FORGE_CML_HEAP_def,
         FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, FORGE_RX_TMP_def,
         FORGE_HEAP_def, FORGE_STACKEND_def]
  \\ rpt conj_tac \\ rpt strip_tac
  \\ TRY (irule untagged_lt_8m)
  \\ fs [wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac
QED

(* ---- 2. Whole-Binary Step Determinism & Deterministic Multi-Step Helper ---- *)

Overload shim_steps = ``shim_step^*``

Definition det_run_def:
  (det_run 0 (s:arm8_state) (s':arm8_state) ⇔ s' = s) ∧
  (det_run (SUC k) s s' ⇔
     ∃s1. ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ∧ det_run k s1 s')
End

Theorem det_run_add:
  ∀k1 k2 s s1 s2. det_run k1 s s1 ∧ det_run k2 s1 s2 ⇒ det_run (k1 + k2) s s2
Proof
  Induct_on `k1` \\ simp [det_run_def, arithmeticTheory.ADD_CLAUSES]
  \\ metis_tac []
QED

Theorem det_run_funpow:
  ∀k s s'. det_run k s s' ⇒ s' = FUNPOW arm8$Next k s
Proof
  Induct_on `k` \\ simp [det_run_def, arithmeticTheory.FUNPOW]
  \\ rpt strip_tac \\ gvs [NextStateARM8_def]
QED

Theorem whole_step_arm8_det:
  ∀rrel wrel inp out s inp' out' s' s1.
    ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ⇒
    (whole_step rrel wrel (inp, out, s) (inp', out', s') ⇔
     inp' = inp ∧ out' = out ∧ s' = s1)
Proof
  simp [whole_step_def] \\ metis_tac []
QED

Theorem whole_step_svc_read_det:
  ∀rrel wrel inp out s inp' out' s'.
    is_svc0_at s ∧ s.REG 8w = 63w ⇒
    (whole_step rrel wrel (inp, out, s) (inp', out', s') ⇔
     rrel inp s s' inp' ∧ out' = out)
Proof
  simp [whole_step_def] \\ metis_tac []
QED

Theorem whole_step_svc_write_det:
  ∀rrel wrel inp out s inp' out' s'.
    is_svc0_at s ∧ s.REG 8w = 64w ⇒
    (whole_step rrel wrel (inp, out, s) (inp', out', s') ⇔
     ∃chunk. wrel s s' chunk ∧ inp' = inp ∧ out' = out ++ chunk)
Proof
  simp [whole_step_def] \\ metis_tac []
QED

Theorem whole_step_exit_stuck:
  ∀rrel wrel ec inp out s y.
    svc_exit_group_rel ec s ⇒ ¬whole_step rrel wrel (inp, out, s) y
Proof
  rpt strip_tac \\ PairCases_on `y`
  \\ gvs [svc_exit_group_rel_def, whole_step_def, is_svc0_at_def]
QED

Theorem whole_step_nrc_exit_stuck:
  ∀rrel wrel n ec inp out s y.
    svc_exit_group_rel ec s ∧ NRC (whole_step rrel wrel) n (inp, out, s) y ⇒
    n = 0 ∧ y = (inp, out, s)
Proof
  rpt gen_tac \\ Cases_on `n` \\ simp [arithmeticTheory.NRC]
  \\ rpt strip_tac \\ metis_tac [whole_step_exit_stuck]
QED

Theorem det_run_imp_nrc:
  ∀k s s' rrel wrel inp out.
    det_run k s s' ⇒
    NRC (whole_step rrel wrel) k (inp, out, s) (inp, out, s')
Proof
  Induct_on `k` \\ simp [det_run_def, arithmeticTheory.NRC]
  \\ rpt strip_tac
  \\ qexists_tac `(inp, out, s1)`
  \\ simp [whole_step_def]
QED

Theorem det_run_imp_rtc:
  ∀k s s' rrel wrel inp out.
    det_run k s s' ⇒
    RTC (whole_step rrel wrel) (inp, out, s) (inp, out, s')
Proof
  rpt strip_tac \\ drule det_run_imp_nrc \\ metis_tac [arithmeticTheory.RTC_eq_NRC]
QED

Theorem det_run_peel_nrc:
  ∀k s s' rrel wrel n ec inp out inp_f out_f ms_f.
    det_run k s s' ∧
    NRC (whole_step rrel wrel) n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    k ≤ n ∧ NRC (whole_step rrel wrel) (n - k) (inp, out, s') (inp_f, out_f, ms_f)
Proof
  Induct_on `k` \\ simp [det_run_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `n`
  >- (gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def])
  \\ gvs [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_def]
  \\ last_x_assum (qspecl_then [`s1`, `s'`, `rrel`, `wrel`, `n'`, `ec`, `inp`, `out`, `inp_f`, `out_f`, `ms_f`] mp_tac)
  \\ simp []
QED

Theorem svc_read_noerr_imp_rel:
  ∀inp s s' rest. svc_read_noerr_rel inp s s' rest ⇒ svc_read_rel inp s s' rest
Proof
  simp [svc_read_noerr_rel_def, svc_read_rel_def] \\ metis_tac []
QED

Theorem svc_write_noerr_imp_rel:
  ∀s s' out. svc_write_noerr_rel s s' out ⇒ svc_write_rel s s' out
Proof
  simp [svc_write_noerr_rel_def, svc_write_rel_def] \\ metis_tac []
QED

(* ---- 3. Core Real-ARM64 Lifting, Arithmetic & Bytearray Helpers ---- *)

Theorem restore_erase_record_upds[local]:
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

Theorem mem_dword_write8[local]:
  ∀m (a:word64) (v:word64).
    mem_dword
      (m⦇a + 7w ↦ (63 >< 56) v; a + 6w ↦ (55 >< 48) v;
         a + 5w ↦ (47 >< 40) v; a + 4w ↦ (39 >< 32) v;
         a + 3w ↦ (31 >< 24) v; a + 2w ↦ (23 >< 16) v;
         a + 1w ↦ (15 >< 8) v;  a ↦ (7 >< 0) v⦈)
      a = v
Proof
  rpt strip_tac
  \\ simp [arm8_stepTheory.mem_dword_def, combinTheory.APPLY_UPDATE_THM]
  \\ blastLib.BBLAST_TAC
QED

Theorem mem_dword_cong[local]:
  ∀m1 m2 (a:word64).
    (∀i:word64. i <₊ 8w ⇒ m1 (a + i) = m2 (a + i)) ⇒
    mem_dword m1 a = mem_dword m2 a
Proof
  rpt strip_tac
  \\ simp [arm8_stepTheory.mem_dword_def]
  \\ `m1 a = m2 a ∧ m1 (a + 1w) = m2 (a + 1w) ∧ m1 (a + 2w) = m2 (a + 2w) ∧
      m1 (a + 3w) = m2 (a + 3w) ∧ m1 (a + 4w) = m2 (a + 4w) ∧
      m1 (a + 5w) = m2 (a + 5w) ∧ m1 (a + 6w) = m2 (a + 6w) ∧
      m1 (a + 7w) = m2 (a + 7w)` by
     (rpt conj_tac
      >- (first_x_assum (qspec_then `0w` mp_tac) \\ simp [])
      \\ first_x_assum irule \\ EVAL_TAC)
  \\ simp []
QED

Theorem cmp_carry_k[local]:
  ∀k (w:word64).
    1 ≤ k ∧ k < 18446744073709551616 ⇒
    (((if w2n w + (18446744073709551615 - k) + 1 < 18446744073709551616
       then w2n w + (18446744073709551615 - k) + 1
       else (w2n w + (18446744073709551615 - k) + 1) MOD 18446744073709551616) ≠
      w2n w + (18446744073709551615 - k) + 1) ⇔ k ≤ w2n w)
Proof
  rpt strip_tac
  \\ assume_tac (Q.ISPEC `w:word64` wordsTheory.w2n_lt)
  \\ fs [dimword_64]
  \\ Cases_on `k ≤ w2n w` \\ simp []
  \\ `w2n w + (18446744073709551615 - k) + 1 = 18446744073709551616 + (w2n w - k)` by decide_tac
  \\ simp [arithmeticTheory.ADD_MODULUS_LEFT]
QED

fun mk_cmp_carry k =
  let val kt = numSyntax.term_of_int k in
    REWRITE_RULE [EVAL ``18446744073709551615 - ^kt``]
      (MATCH_MP cmp_carry_k
        (EQT_ELIM (EVAL ``1 ≤ ^kt ∧ ^kt < 18446744073709551616``)))
  end;
val cmp_carry_17 = mk_cmp_carry 17;
val cmp_carry_16 = mk_cmp_carry 16;
val cmp_carry_65 = mk_cmp_carry 65;
val cmp_carry_64 = mk_cmp_carry 64;

Theorem cmp_zero_gt_cond[local]:
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

Theorem cmn_4_zero[local]:
  ∀w:word64. (w + 4w = 0w) ⇔ (w = -4w)
Proof
  blastLib.BBLAST_TAC
QED

Theorem extend_uxtx_0[local]:
  ∀w:word64. ExtendValue (w, ExtendType_UXTX, 0) = w
Proof
  gen_tac
  \\ simp [arm8Theory.ExtendValue_def, arm8Theory.Extend_def, bitstringTheory.shiftl_def,
           bitstringTheory.shiftr_def, bitstringTheory.field_def,
           bitstringTheory.zero_extend_def, bitstringTheory.fixwidth_id_imp,
           listTheory.PAD_RIGHT, listTheory.TAKE_LENGTH_ID_rwt,
           bitstringTheory.length_w2v, bitstringTheory.v2w_w2v]
QED

Theorem w2w_w2w_word8_word64[local]:
  ∀b:word8. (w2w ((w2w b):word32):word64) = w2w b ∧ (w2w ((w2w b):word64):word8) = b
Proof
  blastLib.BBLAST_TAC
QED

Theorem word_add_n2w_right[local]:
  (∀(p:word64) a b. p + n2w a + n2w b = p + n2w (a + b)) ∧
  (∀(p:word64) n. p + 1w + n2w n = p + n2w (n + 1)) ∧
  (∀(p:word64) n. p + n2w n + 1w = p + n2w (n + 1))
Proof
  rpt strip_tac
  >- (REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w])
  >- (REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w] \\ simp [])
  \\ REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w]
QED

Theorem word64_arith_step_helpers[local]:
  (∀a b:word64. -1w * a + b = b - a) ∧
  (∀a b c:word64. a + (b + c) = b + (c + a))
Proof
  conj_tac \\ rpt gen_tac \\ blastLib.BBLAST_TAC
QED

Theorem read_bytearray_mem_eq:
  ∀n (p:word64) dm m bs.
    read_bytearray p n (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    LENGTH bs = n ∧
    (∀i. i < n ⇒ p + n2w i ∈ dm ∧ m (p + n2w i) = EL i bs)
Proof
  Induct
  >- simp [miscTheory.read_bytearray_def]
  \\ rpt gen_tac \\ simp [miscTheory.read_bytearray_def, AllCaseEqs()]
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum drule \\ strip_tac \\ simp []
  \\ Cases_on `i` \\ simp []
  \\ first_x_assum (qspec_then `n'` mp_tac)
  \\ simp [word_add_n2w_right, wordsTheory.word_add_n2w, ADD1]
QED

Theorem asm_write_bytearray_id:
  ∀n (p:word64) dm m bs.
    read_bytearray p n (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p bs m = m
Proof
  Induct
  >- simp [miscTheory.read_bytearray_def, miscTheory.asm_write_bytearray_def]
  \\ rpt gen_tac \\ simp [miscTheory.read_bytearray_def, AllCaseEqs()]
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum drule \\ strip_tac
  \\ simp [miscTheory.asm_write_bytearray_def, combinTheory.UPDATE_EQ, FUN_EQ_THM,
           combinTheory.APPLY_UPDATE_THM]
  \\ rw []
QED

Theorem asm_write_bytearray_append:
  ∀xs ys (p:word64) m.
    asm_write_bytearray p (xs ++ ys) m =
    asm_write_bytearray p xs (asm_write_bytearray (p + n2w (LENGTH xs)) ys m)
Proof
  Induct \\ simp [miscTheory.asm_write_bytearray_def]
  \\ rpt gen_tac
  \\ simp [word_add_n2w_right, wordsTheory.word_add_n2w, ADD1]
QED

Theorem asm_write_bytearray_unchanged_lt:
  ∀xs (p:word64) (a:word64) m.
    (∀i. i < LENGTH xs ⇒ a ≠ p + n2w i) ⇒
    asm_write_bytearray p xs m a = m a
Proof
  Induct \\ simp [miscTheory.asm_write_bytearray_def, combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac
  \\ `a ≠ p` by (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ simp []
  \\ first_x_assum irule
  \\ rpt strip_tac
  \\ first_x_assum (qspec_then `SUC i` mp_tac)
  \\ simp [word_add_n2w_right, wordsTheory.word_add_n2w, ADD1]
QED

Theorem asm_write_bytearray_read_el:
  ∀xs (p:word64) m i.
    LENGTH xs < dimword (:64) ∧ i < LENGTH xs ⇒
    asm_write_bytearray p xs m (p + n2w i) = EL i xs
Proof
  Induct \\ simp [miscTheory.asm_write_bytearray_def, combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac
  \\ Cases_on `i` \\ simp []
  \\ `p + n2w (SUC n) ≠ p` by
     (spose_not_then (mp_tac o Q.AP_TERM `λx:word64. x - p`)
      \\ simp []
      \\ disch_then (mp_tac o Q.AP_TERM `w2n`)
      \\ simp [dimword_64])
  \\ simp []
  \\ `p + n2w (SUC n) = (p + 1w) + n2w n` by
       simp [word_add_n2w_right, wordsTheory.word_add_n2w, ADD1]
  \\ pop_assum SUBST1_TAC
  \\ first_x_assum irule \\ simp []
QED

Theorem asm_write_bytearray_drop1:
  ∀(p:word64) dm m bs b0.
    1 ≤ LENGTH bs ∧
    read_bytearray p (LENGTH bs) (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p (b0 :: DROP 1 bs) m = (p =+ b0) m
Proof
  rpt strip_tac
  \\ Cases_on `bs` \\ fs [miscTheory.read_bytearray_def, AllCaseEqs()]
  \\ rveq
  \\ `asm_write_bytearray (p + 1w) t m = m` by (irule asm_write_bytearray_id \\ metis_tac [])
  \\ simp [miscTheory.asm_write_bytearray_def]
QED

Theorem asm_write_bytearray_eq_mem[local]:
  ∀ys (q:word64) m.
    (∀i. i < LENGTH ys ⇒ m (q + n2w i) = EL i ys) ⇒
    asm_write_bytearray q ys m = m
Proof
  Induct \\ simp [miscTheory.asm_write_bytearray_def] \\ rpt strip_tac
  \\ `asm_write_bytearray (q + 1w) ys m = m` by
       (first_x_assum irule \\ rpt strip_tac
        \\ first_x_assum (qspec_then `SUC i` mp_tac)
        \\ simp [word_add_n2w_right, arithmeticTheory.ADD1])
  \\ `m q = h` by (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ simp [FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] \\ gen_tac \\ rw []
QED

Theorem asm_write_bytearray_drop_np1:
  ∀N (p:word64) dm m bs f.
    N + 1 ≤ LENGTH bs ∧ LENGTH f = N ∧
    read_bytearray p (LENGTH bs) (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p (0w :: f ++ DROP (N + 1) bs) m =
    (p =+ 0w) (asm_write_bytearray (p + 1w) f m)
Proof
  rpt strip_tac
  \\ imp_res_tac read_bytearray_mem_eq
  \\ simp [miscTheory.asm_write_bytearray_def, asm_write_bytearray_append, word_add_n2w_right]
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ irule asm_write_bytearray_eq_mem \\ simp [] \\ rpt strip_tac
  \\ `N + 1 + i < LENGTH bs` by decide_tac
  \\ simp [rich_listTheory.EL_DROP, word_add_n2w_right]
  \\ `i + SUC N = N + (i + 1)` by decide_tac \\ simp []
QED

Theorem asm_write_bytearray_pointwise[local]:
  ∀xs (p:word64) m1 m2 a.
    m1 a = m2 a ⇒
    asm_write_bytearray p xs m1 a = asm_write_bytearray p xs m2 a
Proof
  Induct \\ simp [miscTheory.asm_write_bytearray_def, combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac \\ IF_CASES_TAC \\ simp []
QED

(* ---- 4. Symbolic ADRP x2 & ADD x2 Step Theorems (Any 256 KB Slot Target) ---- *)

local
  fun mk_pat_idx s =
    let
      fun go _ [] = []
        | go i (#"T"::cs) = T :: go (i+1) cs
        | go i (#"F"::cs) = F :: go (i+1) cs
        | go i (_::cs) = mk_var ("b" ^ Int.toString i, bool) :: go (i+1) cs
    in listSyntax.mk_list (go 0 (String.explode s), bool) end

  val raw_adrp_th = hd (arm8_stepLib.arm8_step (mk_pat_idx "T__TFFFF___________________FFFTF"))
  val raw_add_th  = hd (arm8_stepLib.arm8_step (mk_pat_idx "TFFTFFFTFF____________FFFTFFFFTF"))

  val delta_tm = ``(((tgt:word64) && 0xFFFFFFFFFFFFF000w) - ((s:arm8_state).PC && 0xFFFFFFFFFFFFF000w)) ≫ 12``
  val adrp_inst =
    [mk_var ("b1", bool) |-> ``word_bit 1 ^delta_tm``,
     mk_var ("b2", bool) |-> ``word_bit 0 ^delta_tm``] @
    List.tabulate (19, fn j =>
      mk_var ("b" ^ Int.toString (8 + j), bool) |->
      ``word_bit ^(numSyntax.term_of_int (20 - j)) ^delta_tm``)
  val add_inst =
    List.tabulate (12, fn j =>
      mk_var ("b" ^ Int.toString (10 + j), bool) |->
      ``word_bit ^(numSyntax.term_of_int (11 - j)) (tgt:word64)``)

  val adrp_erased_th =
    raw_adrp_th
    |> Thm.INST ((``s:arm8_state`` |-> ``erase (s:arm8_state)``) :: adrp_inst)
    |> DISCH_ALL
    |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val add_erased_th =
    raw_add_th
    |> Thm.INST ((``s:arm8_state`` |-> ``erase (s:arm8_state)``) :: add_inst)
    |> DISCH_ALL
    |> PURE_REWRITE_RULE [AND_IMP_INTRO]
in

Theorem real_step_adrp_x2:
  ∀s (tgt:word64).
    arm8_ok (erase s) ∧ sp_ok s ∧
    s.PC && 0xFFFFFFFFFFFFF000w = 0x00400000w ∧ aligned 2 s.PC ∧
    0x00400000w ≤₊ tgt ∧ tgt ≤₊ 0x00480000w ∧
    words32_in_mem s.PC [arm8_enc_adrp_x2 s.PC tgt] s.MEM ⇒
    NextStateARM8 s = SOME (s with <| PC := s.PC + 4w;
                                      REG := s.REG⦇2w ↦ tgt && 0xFFFFFFFFFFFFF000w⦈;
                                      branch_hint := NONE |>) ∧
    ¬is_svc0_at s
Proof
  rpt strip_tac
  >- (
    qabbrev_tac `s_er = erase s with <|
      PC := s.PC + 4w;
      REG := s.REG⦇2w ↦ tgt && 0xFFFFFFFFFFFFF000w⦈;
      branch_hint := NONE |>`
    \\ `NextStateARM8 (erase s) = SOME s_er` by (
      mp_tac adrp_erased_th
      \\ simp [arm8_ok_erase, erase_fields, words32_in_mem_def, arm8_enc_adrp_x2_def, LET_THM]
      \\ fs [arm8_ok_erase, erase_fields, words32_in_mem_def, arm8_enc_adrp_x2_def, LET_THM]
      \\ impl_tac
      >- (rpt conj_tac \\ TRY (EVAL_TAC \\ NO_TAC) \\ blastLib.FULL_BBLAST_TAC)
      \\ disch_then SUBST1_TAC
      \\ `v2w [F;F;F;T;F] = (2w:word5)` by EVAL_TAC
      \\ simp [Abbr `s_er`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM, erase_fields]
      \\ gen_tac \\ rw [] \\ blastLib.FULL_BBLAST_TAC)
    \\ mp_tac (Q.SPECL [`s`, `s_er`] NextStateARM8_restore)
    \\ impl_tac
    >- (simp [Abbr `s_er`, untagged_def, erase_fields] \\ blastLib.FULL_BBLAST_TAC)
    \\ simp [Abbr `s_er`, restore_erase_record_upds, erase_fields])
  \\ fs [words32_in_mem_def, arm8_enc_adrp_x2_def, LET_THM, is_svc0_at_def]
  \\ blastLib.FULL_BBLAST_TAC
QED

Theorem real_step_add_x2:
  ∀s (tgt:word64).
    arm8_ok (erase s) ∧ sp_ok s ∧
    s.PC && 0xFFFFFFFFFFFFF000w = 0x00400000w ∧ aligned 2 s.PC ∧
    s.REG 2w = tgt && 0xFFFFFFFFFFFFF000w ∧
    words32_in_mem s.PC [arm8_enc_add_x2 tgt] s.MEM ⇒
    NextStateARM8 s = SOME (s with <| PC := s.PC + 4w;
                                      REG := s.REG⦇2w ↦ tgt⦈;
                                      branch_hint := NONE |>) ∧
    ¬is_svc0_at s
Proof
  rpt strip_tac
  >- (
    qabbrev_tac `s_er = erase s with <|
      PC := s.PC + 4w;
      REG := s.REG⦇2w ↦ tgt⦈;
      branch_hint := NONE |>`
    \\ `NextStateARM8 (erase s) = SOME s_er` by (
      mp_tac add_erased_th
      \\ simp [arm8_ok_erase, erase_fields, words32_in_mem_def, arm8_enc_add_x2_def, LET_THM]
      \\ fs [arm8_ok_erase, erase_fields, words32_in_mem_def, arm8_enc_add_x2_def, LET_THM]
      \\ impl_tac
      >- (rpt conj_tac \\ TRY (EVAL_TAC \\ NO_TAC) \\ blastLib.FULL_BBLAST_TAC)
      \\ disch_then SUBST1_TAC
      \\ `v2w [F;F;F;T;F] = (2w:word5)` by EVAL_TAC
      \\ simp [Abbr `s_er`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM, erase_fields]
      \\ gen_tac \\ rw [] \\ blastLib.FULL_BBLAST_TAC)
    \\ mp_tac (Q.SPECL [`s`, `s_er`] NextStateARM8_restore)
    \\ impl_tac
    >- (simp [Abbr `s_er`, untagged_def, erase_fields] \\ blastLib.FULL_BBLAST_TAC)
    \\ simp [Abbr `s_er`, restore_erase_record_upds, erase_fields])
  \\ fs [words32_in_mem_def, arm8_enc_add_x2_def, LET_THM, is_svc0_at_def]
  \\ blastLib.FULL_BBLAST_TAC
QED

end;

(* ---- 5. Automated Step Generator for Fixed Veneer & 16B/64B Shim Words ---- *)

local
  val v_list =
    forge_slot_veneers_def |> SPEC_ALL |> concl |> rhs |> listSyntax.dest_list |> fst
  val s16_list = forge_shim16_words_def |> concl |> rhs |> listSyntax.dest_list |> fst
  val s64_list = forge_shim64_words_def |> concl |> rhs |> listSyntax.dest_list |> fst

  fun word32_hex t =
    let
      val n = wordsSyntax.dest_word_literal t
      val s = Arbnum.toHexString n
    in
      if size s < 8 then String.implode (List.tabulate (8 - size s, K #"0")) ^ s else s
    end

  val v_bytes_th =
    SIMP_RULE (srw_ss() ++ wordsLib.WORD_ss)
      [words32_in_mem_def, forge_slot_veneers_def, FORGE_VENEERS_BASE_def]
      (ASSUME ``words32_in_mem FORGE_VENEERS_BASE (forge_slot_veneers cb_begin cb_end bm_buf_end) (m:word64 -> word8)``)
  val s16_bytes_th =
    SIMP_RULE (srw_ss() ++ wordsLib.WORD_ss)
      [words32_in_mem_def, forge_shim16_words_def, FORGE_SHIM_BASE_def]
      (ASSUME ``words32_in_mem FORGE_SHIM_BASE forge_shim16_words (m:word64 -> word8)``)
  val s64_bytes_th =
    SIMP_RULE (srw_ss() ++ wordsLib.WORD_ss)
      [words32_in_mem_def, forge_shim64_words_def, FORGE_SHIM_BASE_def]
      (ASSUME ``words32_in_mem FORGE_SHIM_BASE forge_shim64_words (m:word64 -> word8)``)
  val sc_start_bytes_th =
    SIMP_RULE (srw_ss() ++ wordsLib.WORD_ss)
      [words32_in_mem_def, forge_shim16_words_def, FORGE_SHIM_BASE_def, listTheory.TAKE_def]
      (ASSUME ``words32_in_mem FORGE_SHIM_BASE (TAKE 16 forge_shim16_words) (m:word64 -> word8)``)
  val sc_end_bytes_th =
    SIMP_RULE (srw_ss() ++ wordsLib.WORD_ss)
      [words32_in_mem_def, forge_shim16_words_def, listTheory.DROP_def]
      (ASSUME ``words32_in_mem 0x0045011Cw (DROP 71 forge_shim16_words) (m:word64 -> word8)``)

  val v_arr = Vector.fromList (CONJUNCTS v_bytes_th)
  val s16_arr = Vector.fromList (CONJUNCTS s16_bytes_th)
  val s64_arr = Vector.fromList (CONJUNCTS s64_bytes_th)
  val sc_start_arr = Vector.fromList (CONJUNCTS sc_start_bytes_th)
  val sc_end_arr = Vector.fromList (CONJUNCTS sc_end_bytes_th)
  val v_warr = Vector.fromList v_list
  val s16_warr = Vector.fromList s16_list
  val s64_warr = Vector.fromList s64_list

  val step_cache : (string * thm list) list ref = ref []
  fun cached_step h =
    case List.find (fn (k, _) => k = h) (!step_cache) of
      SOME (_, ths) => ths
    | NONE =>
        let val ths = arm8_stepLib.arm8_step_hex h
        in step_cache := (h, ths) :: !step_cache; ths end

  fun is_std_hyp t =
    let val s = term_to_string t in
      String.isSubstring "SCTLR_EL1" s orelse
      String.isSubstring "TCR_EL1" s orelse
      String.isSubstring ".EL =" s orelse
      String.isSubstring ".exception =" s orelse
      String.isSubstring ".MEM " s orelse
      String.isSubstring "aligned 2 " s
    end

  fun get_word_info kind idx =
    case kind of
      "veneer" =>
        (0x00400000 + 4 * idx,
         word32_hex (Vector.sub (v_warr, idx)),
         List.tabulate (4, fn j => Vector.sub (v_arr, 4 * idx + j)),
         ``shim_loaded_slot (shim_ws:word32 list) cb_begin cb_end bm_buf_end (s:arm8_state).MEM``,
         [shim_loaded_slot_def])
    | "common_start" =>
        (0x00450000 + 4 * idx,
         word32_hex (Vector.sub (s16_warr, idx)),
         List.tabulate (4, fn j => Vector.sub (sc_start_arr, 4 * idx + j)),
         ``shim_common_words_ok (shim_ws:word32 list) ∧ shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end (s:arm8_state).MEM``,
         [shim_loaded_slot_common_bytes])
    | "common_end" =>
        (0x00450000 + 4 * idx,
         word32_hex (Vector.sub (s16_warr, idx)),
         List.tabulate (4, fn j => Vector.sub (sc_end_arr, 4 * (idx - 71) + j)),
         ``shim_common_words_ok (shim_ws:word32 list) ∧ shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end (s:arm8_state).MEM``,
         [shim_loaded_slot_common_bytes])
    | "shim16" =>
        (0x00450000 + 4 * idx,
         word32_hex (Vector.sub (s16_warr, idx)),
         List.tabulate (4, fn j => Vector.sub (s16_arr, 4 * idx + j)),
         ``shim_loaded_slot forge_shim16_words cb_begin cb_end bm_buf_end (s:arm8_state).MEM``,
         [shim_loaded_slot_def])
    | "shim64" =>
        (0x00450000 + 4 * idx,
         word32_hex (Vector.sub (s64_warr, idx)),
         List.tabulate (4, fn j => Vector.sub (s64_arr, 4 * idx + j)),
         ``shim_loaded_slot forge_shim64_words cb_begin cb_end bm_buf_end (s:arm8_state).MEM``,
         [shim_loaded_slot_def])
    | _ => failwith ("unknown kind: " ^ kind)

  fun prove_real_step kind idx branch_idx =
    let
      val (addr_n, hex, bths, load_hyp, load_rews) = get_word_info kind idx
      val addr_tm = wordsSyntax.mk_wordii (addr_n, 64)
      val raw_th = List.nth (cached_step hex, branch_idx)
      val erased_th = Thm.INST [``s:arm8_state`` |-> ``erase (s:arm8_state)``] raw_th
      val pc_eq = ``(s:arm8_state).PC = ^addr_tm``
      val inst_bths = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) bths
      val raw_hyps = Thm.hyp erased_th
      val extra_hyps =
        raw_hyps
        |> List.filter (not o is_std_hyp)
        |> map (fn h => rhs (concl (SIMP_CONV (srw_ss() ++ wordsLib.WORD_ss)
                             [erase_fields, ASSUME pc_eq] h)))
      val rhs_erased = erased_th |> concl |> rand |> rand
      val goal_rhs_th =
        SIMP_CONV (srw_ss() ++ wordsLib.WORD_ss)
          [restore_erase_record_upds, erase_fields, ASSUME pc_eq]
          ``restore (bits_of (s:arm8_state)) ^rhs_erased``
      val goal_rhs = rhs (concl goal_rhs_th)
      val need_untagged_lr = (hex = "D65F03C0")
      val extra_hyps' = if need_untagged_lr then ``untagged ((s:arm8_state).REG 30w)`` :: extra_hyps
                        else extra_hyps
      val all_hyps = [``arm8_ok (erase (s:arm8_state))``, ``sp_ok (s:arm8_state)``,
                      load_hyp, pc_eq] @ extra_hyps'
      val goal = mk_imp (list_mk_conj all_hyps,
                   ``NextStateARM8 (s:arm8_state) = SOME ^goal_rhs ∧ ¬is_svc0_at (s:arm8_state)``)
    in
      prove (goal,
        rpt strip_tac
        >- (
          TRY (drule_all shim_loaded_slot_common_bytes \\ strip_tac)
          \\ fs ([shim_loaded_slot_def] @ load_rews)
          \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) inst_bths)
          \\ `NextStateARM8 (erase s) = SOME ^rhs_erased` by
            (mp_tac (DISCH_ALL erased_th)
             \\ simp [arm8_ok_erase, erase_fields]
             \\ fs [arm8_ok_erase, erase_fields]
             \\ TRY (EVAL_TAC \\ NO_TAC))
          \\ (mp_tac (SPECL [``s:arm8_state``, rhs_erased] NextStateARM8_restore)
              \\ impl_tac
              >- (simp [untagged_def] \\ fs [erase_fields, untagged_def] \\ TRY (EVAL_TAC \\ NO_TAC)))
          \\ disch_then SUBST1_TAC
          \\ simp [restore_erase_record_upds, erase_fields])
        \\ TRY (drule_all shim_loaded_slot_common_bytes \\ strip_tac)
        \\ gvs ([shim_loaded_slot_def, is_svc0_at_def] @ load_rews)
        \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) inst_bths)
        \\ gvs [])
    end

  fun prove_svc0_at kind idx =
    let
      val (addr_n, _, bths, load_hyp, load_rews) = get_word_info kind idx
      val addr_tm = wordsSyntax.mk_wordii (addr_n, 64)
      val inst_bths = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) bths
    in
      GEN_ALL (prove (``^load_hyp ∧ (s:arm8_state).PC = ^addr_tm ⇒ is_svc0_at s``,
        rpt strip_tac
        \\ TRY (drule_all shim_loaded_slot_common_bytes \\ strip_tac)
        \\ gvs ([shim_loaded_slot_def, is_svc0_at_def] @ load_rews)
        \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) inst_bths)
        \\ simp []))
    end

  fun fast_eval (g as (_, w)) =
    if can (find_term (fn t => is_const t andalso fst (dest_const t) = "shim_loaded_slot")) w
    then NO_TAC g else (EVAL_TAC \\ NO_TAC) g

  fun step_det th (g as (asl, w)) =
    let
      val (_, args) = strip_comb w
      val s_tm = el 2 args
      val th_s = Thm.INST [``s:arm8_state`` |-> s_tm] th
    in
      (CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV numLib.num_CONV)))
       \\ ONCE_REWRITE_TAC [det_run_def]
       \\ mp_tac th_s
       \\ impl_tac
       >- (TRY (qpat_assum `arm8_ok (erase _)` (mp_tac o REWRITE_RULE [arm8_ok_erase]))
           \\ TRY (qpat_assum `sp_ok _` (mp_tac o REWRITE_RULE [sp_ok_def]))
           \\ simp [arm8_ok_erase, sp_ok_def, combinTheory.APPLY_UPDATE_THM,
                    shim_loaded_slot_update, forge_shim_code_region_def,
                    FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                    FORGE_SHIM_BASE_def, FORGE_SHIM_END_def,
                    wordsTheory.word_lo_n2w, wordsTheory.word_ls_n2w, dimword_64,
                    word_add_n2w_right, wordsTheory.word_add_n2w,
                    cmp_carry_17, cmp_carry_16, cmp_carry_65, cmp_carry_64,
                    cmp_zero_gt_cond, cmn_4_zero,
                    extend_uxtx_0, w2w_w2w_word8_word64]
           \\ TRY fast_eval)
       \\ disch_then (fn th' =>
            qexists_tac `^(th' |> concl |> dest_conj |> fst |> rand |> rand)`
            \\ conj_tac >- ACCEPT_TAC (CONJUNCT2 th')
            \\ conj_tac >- ACCEPT_TAC (CONJUNCT1 th'))
       \\ SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
            [combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ,
             extend_uxtx_0, w2w_w2w_word8_word64, cmp_zero_gt_cond]) g
    end
in
  val prove_real_step = prove_real_step
  val prove_svc0_at = prove_svc0_at
  val step_det = step_det
  val v_arr = v_arr
end;

(* ---- 6. Startup Proof (43 Steps): _start (0x450000) -> cml_main (0x400000) -> cake_main (0x4000B0) ---- *)

local
  val start_ths = List.tabulate (16, fn i => prove_real_step "common_start" i 0)
  val cml_head_ths = List.tabulate (5, fn i => prove_real_step "veneer" i 0)
  val cml_hdr0_ths = List.tabulate (3, fn i => prove_real_step "veneer" (5 + i) 0)
  val cml_str_ths = [prove_real_step "veneer" 10 0,
                     prove_real_step "veneer" 13 0,
                     prove_real_step "veneer" 16 0,
                     prove_real_step "veneer" 19 0]
  val cml_tail_ths = List.tabulate (7, fn i => prove_real_step "veneer" (20 + i) 0)
in
  val start_ths = start_ths
  val cml_head_ths = cml_head_ths
  val cml_hdr0_ths = cml_hdr0_ths
  val cml_str_ths = cml_str_ths
  val cml_tail_ths = cml_tail_ths
end;

Theorem start_block1_slot[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x450000w ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧
      s1.PC = 0x450014w ∧
      mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. 0x460008w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `LENGTH shim_ws = 80` by fs [shim_common_words_ok_def]
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 5 s`
  \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇0x460007w ↦ (63 >< 56) (0x480000w:word64);
                                                0x460006w ↦ (55 >< 48) (0x480000w:word64);
                                                0x460005w ↦ (47 >< 40) (0x480000w:word64);
                                                0x460004w ↦ (39 >< 32) (0x480000w:word64);
                                                0x460003w ↦ (31 >< 24) (0x480000w:word64);
                                                0x460002w ↦ (23 >< 16) (0x480000w:word64);
                                                0x460001w ↦ (15 >< 8) (0x480000w:word64);
                                                0x460000w ↦ (7 >< 0) (0x480000w:word64)⦈;
                                   PC := 0x450014w;
                                   REG := s.REG⦇0w ↦ 0x480000w; 1w ↦ 0x460000w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 5 s s_tgt` by
     (EVERY (map step_det (List.take (start_ths, 5)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_HEAP_def, FORGE_HEAP_def, arm8_stepTheory.mem_dword_def,
            combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC))
      \\ simp [])
  >- (irule (iffRL shim_loaded_slot_cong) \\ conj_tac >- simp [] \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                           FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem start_block2_slot[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x450014w ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧
      s1.PC = 0x450028w ∧
      mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a <₊ 0x460008w ∨ 0x460010w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `LENGTH shim_ws = 80` by fs [shim_common_words_ok_def]
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 5 s`
  \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇0x46000Fw ↦ (63 >< 56) (0x4C0000w:word64);
                                                0x46000Ew ↦ (55 >< 48) (0x4C0000w:word64);
                                                0x46000Dw ↦ (47 >< 40) (0x4C0000w:word64);
                                                0x46000Cw ↦ (39 >< 32) (0x4C0000w:word64);
                                                0x46000Bw ↦ (31 >< 24) (0x4C0000w:word64);
                                                0x46000Aw ↦ (23 >< 16) (0x4C0000w:word64);
                                                0x460009w ↦ (15 >< 8) (0x4C0000w:word64);
                                                0x460008w ↦ (7 >< 0) (0x4C0000w:word64)⦈;
                                   PC := 0x450028w;
                                   REG := s.REG⦇0w ↦ 0x4C0000w; 1w ↦ 0x460008w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 5 s s_tgt` by
     (EVERY (map step_det (List.take (List.drop (start_ths, 5), 5)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_STACK_def, FORGE_STACK_def, arm8_stepTheory.mem_dword_def,
            combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC))
      \\ simp [])
  >- (irule (iffRL shim_loaded_slot_cong) \\ conj_tac >- simp [] \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                           FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem start_block3_slot[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x450028w ⇒
    let s1 = FUNPOW arm8$Next 6 s in
      det_run 6 s s1 ∧
      s1.PC = FORGE_VENEERS_BASE ∧
      mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a <₊ 0x460010w ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `LENGTH shim_ws = 80` by fs [shim_common_words_ok_def]
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 6 s`
  \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇0x460017w ↦ (63 >< 56) (0x500000w:word64);
                                                0x460016w ↦ (55 >< 48) (0x500000w:word64);
                                                0x460015w ↦ (47 >< 40) (0x500000w:word64);
                                                0x460014w ↦ (39 >< 32) (0x500000w:word64);
                                                0x460013w ↦ (31 >< 24) (0x500000w:word64);
                                                0x460012w ↦ (23 >< 16) (0x500000w:word64);
                                                0x460011w ↦ (15 >< 8) (0x500000w:word64);
                                                0x460010w ↦ (7 >< 0) (0x500000w:word64)⦈;
                                   PC := 0x400000w;
                                   REG := s.REG⦇0w ↦ 0x500000w; 1w ↦ 0x460010w⦈;
                                   branch_hint := SOME BranchType_JMP|>`
  \\ `det_run 6 s s_tgt` by
     (EVERY (map step_det (List.drop (start_ths, 10)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_VENEERS_BASE_def]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_STACKEND_def, FORGE_STACKEND_def, arm8_stepTheory.mem_dword_def,
            combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC))
      \\ simp [])
  >- (irule (iffRL shim_loaded_slot_cong) \\ conj_tac >- simp [] \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                           FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem start_16_steps_slot:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_SHIM_BASE ⇒
    let s1 = FUNPOW arm8$Next 16 s in
      det_run 16 s s1 ∧
      s1.PC = FORGE_VENEERS_BASE ∧
      mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
      mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
      mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `16 = 6 + (5 + 5)` by decide_tac \\ pop_assum SUBST1_TAC
  \\ rewrite_tac [arithmeticTheory.FUNPOW_ADD]
  \\ fs [FORGE_SHIM_BASE_def]
  \\ drule_all start_block1_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sA = FUNPOW arm8$Next 5 s`
  \\ drule_all start_block2_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sB = FUNPOW arm8$Next 5 sA`
  \\ drule_all start_block3_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sC = FUNPOW arm8$Next 6 sB`
  \\ simp []
  \\ rpt conj_tac
  >- (`16 = (5 + 5) + 6` by decide_tac \\ pop_assum SUBST1_TAC
      \\ irule det_run_add \\ qexists_tac `sB` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sA` \\ simp [])
  >- (`mem_dword sC.MEM FORGE_CML_HEAP = mem_dword sA.MEM FORGE_CML_HEAP` by
        (irule mem_dword_cong \\ simp [FORGE_CML_HEAP_def] \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sC.MEM ad`
         \\ `ad <₊ 0x460010w ∧ ad <₊ 0x460008w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  \\ `mem_dword sC.MEM FORGE_CML_STACK = mem_dword sB.MEM FORGE_CML_STACK` by
       (irule mem_dword_cong \\ simp [FORGE_CML_STACK_def] \\ rpt strip_tac
        \\ qmatch_goalsub_abbrev_tac `sC.MEM ad`
        \\ `ad <₊ 0x460010w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
        \\ simp [])
  \\ simp []
QED

Theorem cml_main_head_slot[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_VENEERS_BASE ∧ mem_dword s.MEM FORGE_CML_HEAP = FORGE_HEAP ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧
      s1.PC = 0x400014w ∧
      s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
      s1.MEM = s.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 5 s`
  \\ `s.PC = 0x400000w` by fs [FORGE_VENEERS_BASE_def]
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x400014w;
                                   REG := s.REG⦇0w ↦ 0x4000B0w; 1w ↦ 0x480000w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 5 s s_tgt` by
     (EVERY (map step_det cml_head_ths)
      \\ fs [det_run_def, Abbr `s_tgt`, FORGE_CML_HEAP_def, FORGE_HEAP_def,
             arm8Theory.arm8_state_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_CAKE_MAIN_def, FORGE_HEAP_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem cml_hdr0_slot[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    LENGTH shim_ws = 80 ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x400014w ∧ s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
    let s1 = FUNPOW arm8$Next 3 s in
      det_run 3 s s1 ∧
      s1.PC = 0x400020w ∧
      s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
      mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
      (∀a. a <₊ 0x480000w ∨ 0x480008w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 3 s`
  \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇0x480007w ↦ (63 >< 56) (0x460018w:word64);
                                                0x480006w ↦ (55 >< 48) (0x460018w:word64);
                                                0x480005w ↦ (47 >< 40) (0x460018w:word64);
                                                0x480004w ↦ (39 >< 32) (0x460018w:word64);
                                                0x480003w ↦ (31 >< 24) (0x460018w:word64);
                                                0x480002w ↦ (23 >< 16) (0x460018w:word64);
                                                0x480001w ↦ (15 >< 8) (0x460018w:word64);
                                                0x480000w ↦ (7 >< 0) (0x460018w:word64)⦈;
                                   PC := 0x400020w;
                                   REG := s.REG⦇2w ↦ 0x460018w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 3 s s_tgt` by
     (`s.REG 1w = 0x480000w` by fs [FORGE_HEAP_def]
      \\ EVERY (map step_det cml_hdr0_ths)
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, combinTheory.APPLY_UPDATE_THM, FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def]
  \\ rpt conj_tac
  >- (simp [arm8_stepTheory.mem_dword_def, combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC)) \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_heap_hdr_region_def, FORGE_HEAP_def] \\ EVAL_TAC)) \\ simp [])
  >- (irule (iffRL shim_loaded_slot_cong) \\ conj_tac >- simp [] \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                           FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

local
  fun mk_sym_hdr_thm name idx pc_in pc_out dst_val val_tm str_th =
    let
      val adrp_bths = List.tabulate (4, fn j => Vector.sub (v_arr, 4 * idx + j))
      val add_bths  = List.tabulate (4, fn j => Vector.sub (v_arr, 4 * (idx + 1) + j))
      val pc_mid = rhs (concl (EVAL ``^pc_in + 4w``))
      val pc_str = rhs (concl (EVAL ``^pc_in + 8w``))
      val dst_hi = rhs (concl (EVAL ``^dst_val + 8w``))
      val goal =
        ``∀shim_ws cb_begin cb_end bm_buf_end s.
            LENGTH shim_ws = 80 ∧ slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = ^pc_in ∧ s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
            let s1 = FUNPOW arm8$Next 3 s in
              det_run 3 s s1 ∧
              s1.PC = ^pc_out ∧
              s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
              mem_dword s1.MEM ^dst_val = ^val_tm ∧
              (∀a. a <₊ ^dst_val ∨ ^dst_hi ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
              (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
              shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧
              arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0``
      val inst_adrp = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) adrp_bths
      val inst_add  = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) add_bths
    in
      store_thm (name, goal,
        rpt strip_tac
        \\ qabbrev_tac `s1 = FUNPOW arm8$Next 3 s`
        \\ `0x00400000w ≤₊ ^val_tm ∧ ^val_tm ≤₊ 0x00480000w` by
             (fs [slot_layout_ok_def, FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def,
                  FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
                  wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
        \\ `words32_in_mem ^pc_in [arm8_enc_adrp_x2 ^pc_in ^val_tm] s.MEM ∧
            words32_in_mem ^pc_mid [arm8_enc_add_x2 ^val_tm] s.MEM` by
             (fs [shim_loaded_slot_def, words32_in_mem_def]
              \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) (inst_adrp @ inst_add))
              \\ simp [])
        \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇^dst_val + 7w ↦ (63 >< 56) (^val_tm:word64);
                                                      ^dst_val + 6w ↦ (55 >< 48) (^val_tm:word64);
                                                      ^dst_val + 5w ↦ (47 >< 40) (^val_tm:word64);
                                                      ^dst_val + 4w ↦ (39 >< 32) (^val_tm:word64);
                                                      ^dst_val + 3w ↦ (31 >< 24) (^val_tm:word64);
                                                      ^dst_val + 2w ↦ (23 >< 16) (^val_tm:word64);
                                                      ^dst_val + 1w ↦ (15 >< 8) (^val_tm:word64);
                                                      ^dst_val ↦ (7 >< 0) (^val_tm:word64)⦈;
                                         PC := ^pc_out;
                                         REG := s.REG⦇2w ↦ ^val_tm⦈;
                                         branch_hint := NONE|>`
        \\ `det_run 3 s s_tgt` by (
             fs [FORGE_HEAP_def]
             \\ mp_tac (SPECL [``s:arm8_state``, val_tm] real_step_adrp_x2)
             \\ impl_tac >- (simp [] \\ EVAL_TAC)
             \\ strip_tac
             \\ CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV numLib.num_CONV)))
             \\ ONCE_REWRITE_TAC [det_run_def]
             \\ qexists_tac `s with <|PC := ^pc_mid; REG := s.REG⦇2w ↦ 0xFFFFFFFFFFFFF000w && ^val_tm⦈; branch_hint := NONE|>`
             \\ simp []
             \\ qabbrev_tac `s_m = s with <|PC := ^pc_mid; REG := s.REG⦇2w ↦ 0xFFFFFFFFFFFFF000w && ^val_tm⦈; branch_hint := NONE|>`
             \\ mp_tac (SPECL [``s_m:arm8_state``, val_tm] real_step_add_x2)
             \\ impl_tac
             >- (simp [Abbr `s_m`, arm8_ok_erase, sp_ok_def, combinTheory.APPLY_UPDATE_THM]
                 \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)
             \\ strip_tac
             \\ CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV numLib.num_CONV)))
             \\ ONCE_REWRITE_TAC [det_run_def]
             \\ qexists_tac `s_m with <|PC := ^pc_str; REG := s_m.REG⦇2w ↦ ^val_tm⦈; branch_hint := NONE|>`
             \\ fs [Abbr `s_m`, combinTheory.APPLY_UPDATE_THM]
             \\ step_det str_th
             \\ simp [det_run_def, Abbr `s_tgt`])
        \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
        \\ simp [] \\ simp [Abbr `s_tgt`, combinTheory.APPLY_UPDATE_THM]
        \\ rpt conj_tac
        >- (mp_tac (SPECL [``(s:arm8_state).MEM``, dst_val, val_tm] mem_dword_write8) \\ simp [])
        >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC)) \\ simp [])
        >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_heap_hdr_region_def, FORGE_HEAP_def] \\ EVAL_TAC)) \\ simp [])
        >- (irule (iffRL shim_loaded_slot_cong) \\ conj_tac >- simp [] \\ qexists_tac `s.MEM` \\ simp []
            \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                                 FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
            \\ simp [])
        \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC)
    end
in
  val cml_hdr1_slot = mk_sym_hdr_thm "cml_hdr1_slot"  8 ``0x400020w:word64`` ``0x40002Cw:word64`` ``0x480008w:word64`` ``bm_buf_end:word64`` (el 1 cml_str_ths)
  val cml_hdr2_slot = mk_sym_hdr_thm "cml_hdr2_slot" 11 ``0x40002Cw:word64`` ``0x400038w:word64`` ``0x480010w:word64`` ``bm_buf_end:word64`` (el 2 cml_str_ths)
  val cml_hdr3_slot = mk_sym_hdr_thm "cml_hdr3_slot" 14 ``0x400038w:word64`` ``0x400044w:word64`` ``0x480018w:word64`` ``cb_begin:word64``   (el 3 cml_str_ths)
  val cml_hdr4_slot = mk_sym_hdr_thm "cml_hdr4_slot" 17 ``0x400044w:word64`` ``0x400050w:word64`` ``0x480020w:word64`` ``cb_end:word64``     (el 4 cml_str_ths)
end;

Theorem cml_main_tail_slot[local]:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x400050w ∧ s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ∧
    mem_dword s.MEM FORGE_CML_STACK = FORGE_STACK ∧
    mem_dword s.MEM FORGE_CML_STACKEND = FORGE_STACKEND ⇒
    let s1 = FUNPOW arm8$Next 7 s in
      det_run 7 s s1 ∧
      s1.PC = FORGE_CAKE_MAIN ∧
      s1.REG 0w = FORGE_CAKE_MAIN ∧
      s1.REG 1w = FORGE_HEAP ∧
      s1.REG 2w = FORGE_STACK ∧
      s1.REG 3w = FORGE_STACKEND ∧
      s1.MEM = s.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 7 s`
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x4000B0w;
                                   REG := s.REG⦇2w ↦ 0x4C0000w; 3w ↦ 0x500000w⦈;
                                   branch_hint := SOME BranchType_JMP|>`
  \\ `det_run 7 s s_tgt` by
     (EVERY (map step_det cml_tail_ths)
      \\ fs [det_run_def, Abbr `s_tgt`, FORGE_CML_STACK_def, FORGE_CML_STACKEND_def,
             FORGE_STACK_def, FORGE_STACKEND_def,
             arm8Theory.arm8_state_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_CAKE_MAIN_def, FORGE_HEAP_def, FORGE_STACK_def, FORGE_STACKEND_def,
           combinTheory.APPLY_UPDATE_THM]
  \\ fs [FORGE_CAKE_MAIN_def, FORGE_HEAP_def, arm8_ok_erase, sp_ok_def, bits_of_def]
  \\ EVAL_TAC
QED

Theorem startup_to_cake_main_slot:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧ slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_SHIM_BASE ⇒
    let s1 = FUNPOW arm8$Next 43 s in
      det_run 43 s s1 ∧
      s1.PC = FORGE_CAKE_MAIN ∧
      s1.REG 0w = FORGE_CAKE_MAIN ∧
      s1.REG 1w = FORGE_HEAP ∧
      s1.REG 2w = FORGE_STACK ∧
      s1.REG 3w = FORGE_STACKEND ∧
      mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
      mem_dword s1.MEM (FORGE_HEAP + 8w) = bm_buf_end ∧
      mem_dword s1.MEM (FORGE_HEAP + 16w) = bm_buf_end ∧
      mem_dword s1.MEM (FORGE_HEAP + 24w) = cb_begin ∧
      mem_dword s1.MEM (FORGE_HEAP + 32w) = cb_end ∧
      (∀a. a ∉ forge_cml_ptrs_region ∧ a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `LENGTH shim_ws = 80` by fs [shim_common_words_ok_def]
  \\ `43 = 7 + (3 + (3 + (3 + (3 + (3 + (5 + 16))))))` by decide_tac
  \\ pop_assum SUBST1_TAC
  \\ rewrite_tac [arithmeticTheory.FUNPOW_ADD]
  \\ drule_all start_16_steps_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `s0 = FUNPOW arm8$Next 16 s`
  \\ drule_all cml_main_head_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sA = FUNPOW arm8$Next 5 s0`
  \\ qspecl_then [`shim_ws`, `cb_begin`, `cb_end`, `bm_buf_end`, `sA`] mp_tac cml_hdr0_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sB = FUNPOW arm8$Next 3 sA`
  \\ qspecl_then [`shim_ws`, `cb_begin`, `cb_end`, `bm_buf_end`, `sB`] mp_tac cml_hdr1_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sC = FUNPOW arm8$Next 3 sB`
  \\ qspecl_then [`shim_ws`, `cb_begin`, `cb_end`, `bm_buf_end`, `sC`] mp_tac cml_hdr2_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sD = FUNPOW arm8$Next 3 sC`
  \\ qspecl_then [`shim_ws`, `cb_begin`, `cb_end`, `bm_buf_end`, `sD`] mp_tac cml_hdr3_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sE = FUNPOW arm8$Next 3 sD`
  \\ qspecl_then [`shim_ws`, `cb_begin`, `cb_end`, `bm_buf_end`, `sE`] mp_tac cml_hdr4_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sF = FUNPOW arm8$Next 3 sE`
  \\ `mem_dword sF.MEM FORGE_CML_STACK = FORGE_STACK ∧
      mem_dword sF.MEM FORGE_CML_STACKEND = FORGE_STACKEND` by
     (conj_tac
      >- (`mem_dword sF.MEM FORGE_CML_STACK = mem_dword s0.MEM FORGE_CML_STACK` by
            (irule mem_dword_cong \\ simp [FORGE_CML_STACK_def] \\ rpt strip_tac
             \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
             \\ `ad ∉ forge_heap_hdr_region` by
                  (simp [Abbr `ad`, forge_heap_hdr_region_def, FORGE_HEAP_def] \\ blastLib.FULL_BBLAST_TAC)
             \\ simp [])
          \\ simp [])
      \\ `mem_dword sF.MEM FORGE_CML_STACKEND = mem_dword s0.MEM FORGE_CML_STACKEND` by
           (irule mem_dword_cong \\ simp [FORGE_CML_STACKEND_def] \\ rpt strip_tac
            \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
            \\ `ad ∉ forge_heap_hdr_region` by
                 (simp [Abbr `ad`, forge_heap_hdr_region_def, FORGE_HEAP_def] \\ blastLib.FULL_BBLAST_TAC)
            \\ simp [])
      \\ simp [])
  \\ qspecl_then [`shim_ws`, `cb_begin`, `cb_end`, `bm_buf_end`, `sF`] mp_tac cml_main_tail_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ simp [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def]
  \\ rpt conj_tac
  >- (`43 = (((((((16 + 5) + 3) + 3) + 3) + 3) + 3) + 7)` by decide_tac
      \\ pop_assum SUBST1_TAC
      \\ irule det_run_add \\ qexists_tac `sF` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sE` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sD` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sC` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sB` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sA` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `s0` \\ simp [])
  >- (`mem_dword sF.MEM 0x480000w = mem_dword sB.MEM 0x480000w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480008w ∧ ad <₊ 0x480010w ∧ ad <₊ 0x480018w ∧ ad <₊ 0x480020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ fs [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def])
  >- (`mem_dword sF.MEM 0x480008w = mem_dword sC.MEM 0x480008w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480010w ∧ ad <₊ 0x480018w ∧ ad <₊ 0x480020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  >- (`mem_dword sF.MEM 0x480010w = mem_dword sD.MEM 0x480010w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480018w ∧ ad <₊ 0x480020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  >- (`mem_dword sF.MEM 0x480018w = mem_dword sE.MEM 0x480018w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480020w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
QED

(* ---- 7. Exit & Install Veneer + Stub Proofs (Both 16B & 64B Shims) ---- *)

local
  val veneer_exit_th    = prove_real_step "veneer" 40 0
  val veneer_install_th = prove_real_step "veneer" 36 0
  val exit_cbz_nz_th    = prove_real_step "common_end" 71 0
  val exit_cbz_z_th     = prove_real_step "common_end" 71 1
  val exit_mov1_th      = prove_real_step "common_end" 72 0
  val exit_mov8_th      = prove_real_step "common_end" 73 0
  val exit_svc_th       = prove_svc0_at   "common_end" 74
  val inst_mov2_th      = prove_real_step "common_end" 76 0
  val inst_mov8_th      = prove_real_step "common_end" 77 0
  val inst_svc_th       = prove_svc0_at   "common_end" 78
in

Theorem cake_exit_to_svc_exit_group_slot:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_EXIT_VENEER ⇒
    ∃k.
      let s1 = FUNPOW arm8$Next k s in
        det_run k s s1 ∧
        s1.PC = 0x450128w ∧
        svc_exit_group_rel (if s.REG 0w = 0w then 0w else 1w) s1 ∧
        s1.MEM = s.MEM ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `s.PC = 0x4000A0w` by fs [FORGE_EXIT_VENEER_def]
  \\ Cases_on `s.REG 0w = 0w`
  >- (
    qexists_tac `3`
    \\ qabbrev_tac `s_tgt = s with <|PC := 0x450128w; REG := s.REG⦇8w ↦ 94w⦈; branch_hint := NONE|>`
    \\ `det_run 3 s s_tgt` by
       (step_det veneer_exit_th \\ step_det exit_cbz_z_th \\ step_det exit_mov8_th
        \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `FUNPOW arm8$Next 3 s = s_tgt` by (drule det_run_funpow \\ simp [])
    \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
    \\ `is_svc0_at (s with <|PC := 0x450128w; REG := s.REG⦇8w ↦ 94w⦈; branch_hint := NONE|>)` by
         (irule exit_svc_th \\ simp [] \\ metis_tac [])
    \\ fs [is_svc0_at_def])
  \\ qexists_tac `4`
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x450128w; REG := s.REG⦇0w ↦ 1w; 8w ↦ 94w⦈; branch_hint := NONE|>`
  \\ `det_run 4 s s_tgt` by
     (step_det veneer_exit_th \\ step_det exit_cbz_nz_th \\ step_det exit_mov1_th \\ step_det exit_mov8_th
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `FUNPOW arm8$Next 4 s = s_tgt` by (drule det_run_funpow \\ simp [])
  \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
  \\ `is_svc0_at (s with <|PC := 0x450128w; REG := s.REG⦇0w ↦ 1w; 8w ↦ 94w⦈; branch_hint := NONE|>)` by
       (irule exit_svc_th \\ simp [] \\ metis_tac [])
  \\ fs [is_svc0_at_def]
QED

Theorem cake_exit_universal_slot:
  ∀shim_ws cb_begin cb_end bm_buf_end rrel wrel n s inp out inp_f out_f ms_f ec.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_EXIT_VENEER ∧
    NRC (whole_step rrel wrel) n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = (if s.REG 0w = 0w then 0w else 1w)
Proof
  rpt strip_tac
  \\ drule_all cake_exit_to_svc_exit_group_slot \\ simp [LET_THM] \\ strip_tac
  \\ drule_all det_run_peel_nrc \\ strip_tac
  \\ drule_all whole_step_nrc_exit_stuck \\ strip_tac
  \\ rveq \\ fs [svc_exit_group_rel_def]
QED

Theorem cake_install_to_svc_exit_group_slot:
  ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_INSTALL_VENEER ⇒
    let s1 = FUNPOW arm8$Next 3 s in
      det_run 3 s s1 ∧
      s1.PC = 0x450138w ∧
      svc_exit_group_rel 2w s1 ∧
      s1.MEM = s.MEM ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `s.PC = 0x400090w` by fs [FORGE_INSTALL_VENEER_def]
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x450138w; REG := s.REG⦇0w ↦ 2w; 8w ↦ 94w⦈; branch_hint := NONE|>`
  \\ `det_run 3 s s_tgt` by
     (step_det veneer_install_th \\ step_det inst_mov2_th \\ step_det inst_mov8_th
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `FUNPOW arm8$Next 3 s = s_tgt` by (drule det_run_funpow \\ simp [])
  \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
  \\ `is_svc0_at (s with <|PC := 0x450138w; REG := s.REG⦇0w ↦ 2w; 8w ↦ 94w⦈; branch_hint := NONE|>)` by
       (irule inst_svc_th \\ simp [] \\ metis_tac [])
  \\ fs [is_svc0_at_def]
QED

Theorem cake_install_universal_slot:
  ∀shim_ws cb_begin cb_end bm_buf_end rrel wrel n s inp out inp_f out_f ms_f ec.
    shim_common_words_ok shim_ws ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_INSTALL_VENEER ∧
    NRC (whole_step rrel wrel) n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = 2w
Proof
  rpt strip_tac
  \\ drule_all cake_install_to_svc_exit_group_slot \\ simp [LET_THM] \\ strip_tac
  \\ drule_all det_run_peel_nrc \\ strip_tac
  \\ drule_all whole_step_nrc_exit_stuck \\ strip_tac
  \\ rveq \\ fs [svc_exit_group_rel_def]
QED

end;

(* ---- 8. Parameterized Leaf FFI Postcondition & Frame-Width Proof Generator (16B & 64B) ---- *)

Definition ffi_return_ok_slot_def:
  ffi_return_ok_slot (shim_ws:word32 list) (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64)
                     (new_bytes:word8 list) (s:arm8_state) (s':arm8_state) ⇔
    arm8_ok (erase s') ∧
    sp_ok s' ∧
    bits_of s' = bits_of s ∧
    s'.SP_EL0 = s.SP_EL0 ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s'.MEM ∧
    s'.PC = s.REG 30w ∧
    (∀a. a ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒
         s'.MEM a = asm_write_bytearray (s.REG 2w) new_bytes s.MEM a) ∧
    (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))
End

val peel_nrc_tac =
  qpat_x_assum `det_run _ _ _` (fn dth =>
    qpat_x_assum `NRC _ _ _ _` (fn nth =>
      mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] det_run_peel_nrc) dth)
      \\ disch_then (fn th => mp_tac (MATCH_MP th nth))
      \\ disch_then (fn th => first_assum (mp_tac o MATCH_MP th))
      \\ strip_tac));

Theorem svc_read_noerr_not_fatal[local]:
  ∀inp s s' rest cnt.
    cnt ≤ 64 ∧ s.REG 2w = n2w cnt ∧ svc_read_noerr_rel inp s s' rest ⇒
    ¬(word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w)
Proof
  rpt strip_tac
  \\ qpat_x_assum `svc_read_noerr_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [svc_read_noerr_rel_def])
  >- (qpat_x_assum `word_msb _` mp_tac \\ simp [] \\ EVAL_TAC)
  \\ `n ≤ cnt` by (qpat_x_assum `_ ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
  \\ `¬word_msb (n2w n : word64)` by
       (simp [wordsTheory.word_msb_n2w, dimword_64] \\ irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
  \\ qpat_x_assum `word_msb _` mp_tac \\ simp []
QED

Theorem svc_write_noerr_not_err[local]:
  ∀s s' chunk cnt.
    cnt ≤ 64 ∧ s.REG 2w = n2w cnt ∧ svc_write_noerr_rel s s' chunk ⇒
    ¬(s'.REG 0w = 0w ∨ (word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w))
Proof
  rpt strip_tac
  \\ qpat_x_assum `svc_write_noerr_rel _ _ _`
       (strip_assume_tac o REWRITE_RULE [svc_write_noerr_rel_def])
  >- (qpat_x_assum `s'.REG 0w = 0w` mp_tac \\ simp [] \\ EVAL_TAC)
  >- (`n ≤ cnt` by (qpat_x_assum `_ ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
      \\ `(n2w n : word64) ≠ 0w` by simp [wordsTheory.n2w_11, dimword_64]
      \\ qpat_x_assum `s'.REG 0w = 0w` mp_tac \\ simp [])
  \\ `n ≤ cnt` by (qpat_x_assum `_ ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
  \\ `¬word_msb (n2w n : word64)` by
       (simp [wordsTheory.word_msb_n2w, dimword_64] \\ irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
  \\ qpat_x_assum `word_msb _` mp_tac \\ simp []
QED

local
  val v_recv_gen = prove_real_step "veneer" 28 0
  val v_send_gen = prove_real_step "veneer" 32 0

  fun mk_frame_ffi_suite {n : int, kind : string, shim_ws_tm : term, shim_len_th : thm} =
    let
      val ns = Int.toString n
      val n_tm   = numSyntax.term_of_int n
      val np1_tm = numSyntax.term_of_int (n + 1)
      val nm1_tm = numSyntax.term_of_int (n - 1)
      val n_w64  = wordsSyntax.mk_wordii (n, 64)
      val max_u64 = Arbnum.fromString "18446744073709551615"
      val c_np1_tm = numSyntax.mk_numeral (Arbnum.- (max_u64, Arbnum.fromInt (n + 1)))
      val c_n_tm   = numSyntax.mk_numeral (Arbnum.- (max_u64, Arbnum.fromInt n))
      val neg_np1_w64 = wordsSyntax.mk_word (Arbnum.- (Arbnum.fromString "18446744073709551616", Arbnum.fromInt (n + 1)), Arbnum.fromInt 64)
      val neg_n_w64   = wordsSyntax.mk_word (Arbnum.- (Arbnum.fromString "18446744073709551616", Arbnum.fromInt n), Arbnum.fromInt 64)

      val v_recv = Thm.INST [``shim_ws:word32 list`` |-> shim_ws_tm] v_recv_gen
      val v_send = Thm.INST [``shim_ws:word32 list`` |-> shim_ws_tm] v_send_gen

      val r_cmp_np1  = prove_real_step kind 16 0
      val r_blo_ge   = prove_real_step kind 17 0
      val r_blo_lt   = prove_real_step kind 17 1
      val r_mov9     = prove_real_step kind 18 0
      val r_adrp10   = prove_real_step kind 19 0
      val r_add10    = prove_real_step kind 20 0
      val r_mov11_n  = prove_real_step kind 21 0
      val r_cbz_nz   = prove_real_step kind 22 0
      val r_cbz_z    = prove_real_step kind 22 1
      val r_mov0     = prove_real_step kind 23 0
      val r_mov1     = prove_real_step kind 24 0
      val r_mov2     = prove_real_step kind 25 0
      val r_mov8     = prove_real_step kind 26 0
      val r_svc      = prove_svc0_at   kind 27
      val r_cmn4     = prove_real_step kind 28 0
      val r_beq_ne   = prove_real_step kind 29 0
      val r_beq_eq   = prove_real_step kind 29 1
      val r_cmp0     = prove_real_step kind 30 0
      val r_ble_gt   = prove_real_step kind 31 0
      val r_ble_le   = prove_real_step kind 31 1
      val r_add10_x0 = prove_real_step kind 32 0
      val r_sub11_x0 = prove_real_step kind 33 0
      val r_b_loop   = prove_real_step kind 34 0
      val r_adrp12   = prove_real_step kind 35 0
      val r_add12    = prove_real_step kind 36 0
      val r_mov11_0  = prove_real_step kind 37 0
      val r_ldrb     = prove_real_step kind 38 0
      val r_add11_1  = prove_real_step kind 39 0
      val r_strb_reg = prove_real_step kind 40 0
      val r_cmp_n    = prove_real_step kind 41 0
      val r_blo_done = prove_real_step kind 42 0
      val r_blo_more = prove_real_step kind 42 1
      val r_strb_0   = prove_real_step kind 43 0
      val r_ret_ok   = prove_real_step kind 44 0
      val r_mov12_1  = prove_real_step kind 45 0
      val r_strb_1   = prove_real_step kind 46 0
      val r_ret_err  = prove_real_step kind 47 0

      val s_cmp_np1  = prove_real_step kind 48 0
      val s_blo_ge   = prove_real_step kind 49 0
      val s_blo_lt   = prove_real_step kind 49 1
      val s_mov9     = prove_real_step kind 50 0
      val s_add10    = prove_real_step kind 51 0
      val s_mov11_n  = prove_real_step kind 52 0
      val s_cbz_nz   = prove_real_step kind 53 0
      val s_cbz_z    = prove_real_step kind 53 1
      val s_mov0     = prove_real_step kind 54 0
      val s_mov1     = prove_real_step kind 55 0
      val s_mov2     = prove_real_step kind 56 0
      val s_mov8     = prove_real_step kind 57 0
      val s_svc      = prove_svc0_at   kind 58
      val s_cmn4     = prove_real_step kind 59 0
      val s_beq_ne   = prove_real_step kind 60 0
      val s_beq_eq   = prove_real_step kind 60 1
      val s_cmp0     = prove_real_step kind 61 0
      val s_ble_gt   = prove_real_step kind 62 0
      val s_ble_le   = prove_real_step kind 62 1
      val s_add10_x0 = prove_real_step kind 63 0
      val s_sub11_x0 = prove_real_step kind 64 0
      val s_b_loop   = prove_real_step kind 65 0
      val s_strb_0   = prove_real_step kind 66 0
      val s_ret_ok   = prove_real_step kind 67 0
      val s_mov12_1  = prove_real_step kind 68 0
      val s_strb_1   = prove_real_step kind 69 0
      val s_ret_err  = prove_real_step kind 70 0

      val recv_short_det = prove(
        ``∀cb_begin cb_end bm_buf_end s bytes2.
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFIRECV_VENEER ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            read_bytearray (s.REG 2w) (w2n (s.REG 3w))
              (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
            w2n (s.REG 3w) < ^np1_tm ⇒
            ∃s'. det_run 4 s s' ∧ ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end bytes2 s s'``,
        rpt strip_tac
        \\ `s.PC = 0x400070w` by fs [FORGE_FFIRECV_VENEER_def]
        \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by
             (irule asm_write_bytearray_id \\ metis_tac [])
        \\ qexists_tac `s with <|PC := s.REG 30w;
                                 PSTATE := s.PSTATE with
                                   <|V := (word_msb (s.REG 3w) ∧
                                           (word_msb (s.REG 3w) ⇎
                                            BIT 63 (w2n (s.REG 3w) + ^c_np1_tm + 1)));
                                     C := F;
                                     Z := (s.REG 3w + ^neg_np1_w64 = 0w);
                                     N := word_msb (s.REG 3w + ^neg_np1_w64)|>;
                                 branch_hint := SOME BranchType_RET|>`
        \\ conj_tac
        >- (step_det v_recv \\ step_det r_cmp_np1 \\ step_det r_blo_lt \\ step_det r_ret_err
            \\ simp [det_run_def, cmp_carry_17, cmp_carry_65, arm8Theory.arm8_state_component_equality])
        \\ simp [ffi_return_ok_slot_def, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ fs [arm8_ok_erase, sp_ok_def])

      val recv_entry_det = prove(
        ``∀cb_begin cb_end bm_buf_end s.
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFIRECV_VENEER ∧ ^np1_tm ≤ w2n (s.REG 3w) ⇒
            ∃s_loop.
              det_run 7 s s_loop ∧
              arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s_loop.MEM ∧
              bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
              s_loop.PC = 0x450058w ∧ s_loop.MEM = s.MEM ∧
              s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = FORGE_RX_TMP ∧ s_loop.REG 11w = ^n_w64 ∧
              s_loop.REG 30w = s.REG 30w ∧
              (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))``,
        rpt strip_tac
        \\ `s.PC = 0x400070w` by fs [FORGE_FFIRECV_VENEER_def]
        \\ qabbrev_tac `p = s.REG 2w`
        \\ qexists_tac `s with <|PC := 0x450058w;
                                 REG := s.REG⦇9w ↦ p; 10w ↦ FORGE_RX_TMP; 11w ↦ ^n_w64⦈;
                                 PSTATE := s.PSTATE with
                                   <|V := (word_msb (s.REG 3w) ∧
                                           (word_msb (s.REG 3w) ⇎
                                            BIT 63 (w2n (s.REG 3w) + ^c_np1_tm + 1)));
                                     C := T;
                                     Z := (s.REG 3w + ^neg_np1_w64 = 0w);
                                     N := word_msb (s.REG 3w + ^neg_np1_w64)|>;
                                 branch_hint := NONE|>`
        \\ conj_tac
        >- (step_det v_recv \\ step_det r_cmp_np1 \\ step_det r_blo_ge \\ step_det r_mov9
            \\ step_det r_adrp10 \\ step_det r_add10 \\ step_det r_mov11_n
            \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
                 [det_run_def, Abbr `p`, FORGE_RX_TMP_def, cmp_carry_17, cmp_carry_65,
                  arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                  combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
        \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

      val recv_copy_loop_det = prove(
        ``∀c k cb_begin cb_end bm_buf_end s (f:word8 list) (p:word64).
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            1 ≤ c ∧ c + k = ^n_tm ∧ LENGTH f = ^n_tm ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x450098w ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            s.REG 9w = p ∧ s.REG 12w = FORGE_RX_TMP ∧ s.REG 11w = n2w k ∧
            (∀i. i < ^np1_tm ⇒ p + n2w i ∈ forge_prog_addresses_slot cb_end bm_buf_end) ∧
            (∀i. i < ^n_tm ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i f) ⇒
            ∃d s'.
              1 ≤ d ∧ det_run d s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧
              s'.SP_EL0 = s.SP_EL0 ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              s'.PC = s.REG 30w ∧
              s'.MEM = (p =+ 0w) (asm_write_bytearray (p + n2w (k + 1)) (DROP k f) s.MEM) ∧
              (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)``,
        Induct_on `c`
        >- (rpt strip_tac \\ `F` by decide_tac)
        \\ rpt strip_tac
        \\ drule forge_regions_disjoint_slot \\ strip_tac
        \\ Cases_on `c = 0`
        >- (
          `k = ^nm1_tm` by decide_tac \\ pop_assum SUBST_ALL_TAC
          \\ qabbrev_tac `blast = EL ^nm1_tm f`
          \\ qpat_assum `∀i. i < ^n_tm ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `^nm1_tm`)
          \\ qpat_assum `∀i. i < ^np1_tm ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `^n_tm`)
          \\ qpat_assum `∀i. i < ^np1_tm ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `0`)
          \\ `p + ^n_w64 ∉ forge_shim_code_region ∧ p ∉ forge_shim_code_region` by simp []
          \\ qabbrev_tac `m1 = s.MEM⦇p + ^n_w64 ↦ blast⦈`
          \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end m1` by
               simp [Abbr `m1`, shim_loaded_slot_update, shim_len_th]
          \\ qabbrev_tac `m2 = m1⦇p ↦ 0w⦈`
          \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end m2` by
               simp [Abbr `m2`, shim_loaded_slot_update, shim_len_th]
          \\ `DROP ^nm1_tm f = [blast]` by
               (simp [Abbr `blast`] \\ `^nm1_tm < LENGTH f` by decide_tac
                \\ simp [DROP_EL_CONS, listTheory.DROP_LENGTH_NIL])
          \\ qexists_tac `7`
          \\ qexists_tac `s with <|MEM := m2; PC := s.REG 30w;
                                   REG := s.REG⦇10w ↦ w2w blast; 11w ↦ ^n_w64⦈;
                                   PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                                   branch_hint := SOME BranchType_RET|>`
          \\ conj_tac >- decide_tac
          \\ conj_tac
          >- (step_det r_ldrb \\ step_det r_add11_1 \\ step_det r_strb_reg
              \\ step_det r_cmp_n \\ step_det r_blo_done \\ step_det r_strb_0 \\ step_det r_ret_ok
              \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
                   [det_run_def, Abbr `m2`, Abbr `m1`, Abbr `blast`, FORGE_RX_TMP_def,
                    cmp_carry_16, cmp_carry_64,
                    arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                    combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
              \\ rw [] \\ fs [] \\ TRY (EVAL_TAC \\ NO_TAC))
          \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM,
                   Abbr `m2`, Abbr `m1`, miscTheory.asm_write_bytearray_def]
          \\ fs [arm8_ok_erase, sp_ok_def])
        \\ `k < ^nm1_tm ∧ k + 1 < ^n_tm` by decide_tac
        \\ qabbrev_tac `bk = EL k f`
        \\ qpat_assum `∀i. i < ^n_tm ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k`)
        \\ qpat_assum `∀i. i < ^np1_tm ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k + 1`)
        \\ `s.MEM (FORGE_RX_TMP + n2w k) = bk` by simp [Abbr `bk`]
        \\ `p + n2w (k + 1) ∈ forge_prog_addresses_slot cb_end bm_buf_end` by simp []
        \\ `p + n2w (k + 1) ∉ forge_shim_code_region` by simp []
        \\ `∀i. i < ^n_tm ⇒ p + n2w (k + 1) ≠ FORGE_RX_TMP + n2w i` by
           (rpt strip_tac
            \\ `FORGE_RX_TMP + n2w i ∈ forge_rx_tmp_region` by
                 (simp [forge_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
                        word_add_n2w, w2n_n2w, dimword_64])
            \\ metis_tac [])
        \\ qabbrev_tac `m1 = s.MEM⦇p + n2w (k + 1) ↦ bk⦈`
        \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end m1` by
             simp [Abbr `m1`, shim_loaded_slot_update, shim_len_th]
        \\ qabbrev_tac `s_next = s with <|MEM := m1; PC := 0x450098w;
                                          REG := s.REG⦇10w ↦ w2w bk; 11w ↦ n2w (k + 1)⦈;
                                          PSTATE := s.PSTATE with
                                            <|V := (word_msb (n2w (k + 1):word64) ∧
                                                    (word_msb (n2w (k + 1):word64) ⇎
                                                     BIT 63 (w2n (n2w (k + 1):word64) + ^c_n_tm + 1)));
                                              C := F;
                                              Z := ((n2w (k + 1):word64) + ^neg_n_w64 = 0w);
                                              N := word_msb ((n2w (k + 1):word64) + ^neg_n_w64)|>;
                                          branch_hint := SOME BranchType_JMP|>`
        \\ `det_run 5 s s_next` by
           (step_det r_ldrb \\ step_det r_add11_1 \\ step_det r_strb_reg
            \\ step_det r_cmp_n \\ step_det r_blo_more
            \\ simp [det_run_def, Abbr `s_next`, Abbr `m1`, Abbr `bk`,
                     cmp_carry_16, cmp_carry_64,
                     word_add_n2w_right, wordsTheory.word_add_n2w,
                     arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                     combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ qpat_x_assum `∀k cb_begin cb_end bm_buf_end s f p. _`
             (qspecl_then [`k + 1`, `cb_begin`, `cb_end`, `bm_buf_end`, `s_next`, `f`, `p`] mp_tac)
        \\ impl_tac
        >- (simp [Abbr `s_next`, combinTheory.APPLY_UPDATE_THM, arm8_ok_erase, sp_ok_def]
            \\ rpt conj_tac
            \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
            \\ TRY (fs [sp_ok_def] \\ NO_TAC)
            \\ TRY decide_tac
            \\ rpt strip_tac \\ simp [Abbr `m1`, combinTheory.APPLY_UPDATE_THM]
            \\ `FORGE_RX_TMP + n2w i ≠ p + n2w (k + 1)` by metis_tac []
            \\ simp [])
        \\ strip_tac
        \\ `s_next.MEM = m1 ∧ s_next.SP_EL0 = s.SP_EL0 ∧ bits_of s_next = bits_of s ∧
            s_next.REG 30w = s.REG 30w ∧ (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s_next.REG r = s.REG r)` by
             simp [Abbr `s_next`, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ qexists_tac `5 + d` \\ qexists_tac `s'`
        \\ conj_tac >- decide_tac
        \\ conj_tac >- (irule det_run_add \\ qexists_tac `s_next` \\ simp [])
        \\ simp []
        \\ `DROP k f = bk :: DROP (k + 1) f` by (simp [Abbr `bk`, DROP_EL_CONS, ADD1])
        \\ simp [miscTheory.asm_write_bytearray_def]
        \\ `p + n2w (k + 1) + 1w = p + n2w (k + 2)` by simp [word_add_n2w_right, wordsTheory.word_add_n2w]
        \\ simp [FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
        \\ gen_tac
        \\ Cases_on `x = p` \\ simp []
        \\ Cases_on `x = p + n2w (k + 1)` \\ simp [Abbr `m1`]
        >- (
          `asm_write_bytearray (p + n2w (k + 2)) (DROP (k + 1) f) (s.MEM⦇p + n2w (k + 1) ↦ bk⦈) (p + n2w (k + 1)) =
           (s.MEM⦇p + n2w (k + 1) ↦ bk⦈) (p + n2w (k + 1))` by
            (irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
             \\ `i < ^n_tm` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
             \\ qpat_x_assum `p + n2w (k + 1) = _` mp_tac
             \\ simp [word_add_n2w_right, wordsTheory.word_add_n2w,
                      wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
          \\ simp [combinTheory.APPLY_UPDATE_THM])
        \\ irule asm_write_bytearray_pointwise \\ simp [combinTheory.APPLY_UPDATE_THM])

      val recv_loop_done_det = prove(
        ``∀cb_begin cb_end bm_buf_end s.
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x450058w ∧ s.REG 11w = 0w ⇒
            ∃s_cp0.
              det_run 4 s s_cp0 ∧
              arm8_ok (erase s_cp0) ∧ sp_ok s_cp0 ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s_cp0.MEM ∧
              bits_of s_cp0 = bits_of s ∧ s_cp0.SP_EL0 = s.SP_EL0 ∧
              s_cp0.PC = 0x450098w ∧ s_cp0.MEM = s.MEM ∧
              s_cp0.REG 12w = FORGE_RX_TMP ∧ s_cp0.REG 11w = 0w ∧
              (∀r. r ≠ 11w ∧ r ≠ 12w ⇒ s_cp0.REG r = s.REG r)``,
        rpt strip_tac
        \\ qexists_tac `s with <|PC := 0x450098w;
                                 REG := s.REG⦇12w ↦ FORGE_RX_TMP; 11w ↦ 0w⦈;
                                 branch_hint := NONE|>`
        \\ conj_tac
        >- (step_det r_cbz_z \\ step_det r_adrp12 \\ step_det r_add12 \\ step_det r_mov11_0
            \\ simp [det_run_def, FORGE_RX_TMP_def, arm8Theory.arm8_state_component_equality,
                     combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

      val recv_loop_to_svc_det = prove(
        ``∀cb_begin cb_end bm_buf_end s k c.
            1 ≤ c ∧ c + k = ^n_tm ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x450058w ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ⇒
            ∃s_svc.
              det_run 5 s s_svc ∧
              arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s_svc.MEM ∧
              bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
              s_svc.PC = 0x45006Cw ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
              s_svc.REG 0w = 0w ∧ s_svc.REG 1w = FORGE_RX_TMP + n2w k ∧
              s_svc.REG 2w = n2w c ∧ s_svc.REG 8w = 63w ∧
              (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
        rpt strip_tac
        \\ qabbrev_tac `s_svc = s with <|PC := 0x45006Cw;
                                         REG := s.REG⦇0w ↦ 0w; 1w ↦ FORGE_RX_TMP + n2w k;
                                                      2w ↦ n2w c; 8w ↦ 63w⦈;
                                         branch_hint := NONE|>`
        \\ qexists_tac `s_svc`
        \\ conj_tac
        >- (step_det r_cbz_nz \\ step_det r_mov0 \\ step_det r_mov1 \\ step_det r_mov2 \\ step_det r_mov8
            \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                     combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ `is_svc0_at s_svc` by (irule r_svc \\ simp [Abbr `s_svc`] \\ metis_tac [])
        \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

      val recv_post_eintr_det = prove(
        ``∀cb_begin cb_end bm_buf_end s.
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x450070w ∧ s.REG 0w = -4w ⇒
            ∃s'.
              det_run 2 s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
              s'.PC = 0x450058w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
        rpt strip_tac
        \\ qexists_tac `s with <|PC := 0x450058w;
                                 PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                                 branch_hint := SOME BranchType_JMP|>`
        \\ conj_tac
        >- (step_det r_cmn4 \\ step_det r_beq_eq
            \\ simp [det_run_def, arm8Theory.arm8_state_component_equality,
                     arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

      val recv_post_err_det = prove(
        ``∀cb_begin cb_end bm_buf_end s (p:word64).
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x450070w ∧ s.REG 9w = p ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            p ∈ forge_prog_addresses_slot cb_end bm_buf_end ∧
            (s.REG 0w = 0w ∨ (word_msb (s.REG 0w) ∧ s.REG 0w ≠ -4w)) ⇒
            ∃s'.
              det_run 7 s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
              s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
              (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)``,
        rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
        \\ drule forge_regions_disjoint_slot \\ strip_tac
        \\ `p ∉ forge_shim_code_region` by simp []
        \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 1w⦈)` by
             simp [shim_loaded_slot_update, shim_len_th]
        \\ `s.REG 0w ≠ -4w ∧ (¬word_msb (s.REG 0w) ⇒ s.REG 0w = 0w)` by
             (Cases_on `s.REG 0w = 0w` \\ fs [] \\ EVAL_TAC)
        \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 1w⦈; PC := s.REG 30w;
                                 REG := s.REG⦇12w ↦ 1w⦈;
                                 PSTATE := s.PSTATE with
                                   <|V := (word_msb (s.REG 0w) ∧
                                           (word_msb (s.REG 0w) ⇎
                                            BIT 63 (w2n (s.REG 0w) + 18446744073709551615 + 1)));
                                     C := ((if w2n (s.REG 0w) + 18446744073709551615 + 1 < 18446744073709551616
                                            then w2n (s.REG 0w) + 18446744073709551615 + 1
                                            else (w2n (s.REG 0w) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                           w2n (s.REG 0w) + 18446744073709551615 + 1);
                                     Z := (s.REG 0w + 0w = 0w);
                                     N := word_msb (s.REG 0w + 0w)|>;
                                 branch_hint := SOME BranchType_RET|>`
        \\ conj_tac
        >- (step_det r_cmn4 \\ step_det r_beq_ne \\ step_det r_cmp0 \\ step_det r_ble_le
            \\ step_det r_mov12_1 \\ step_det r_strb_1 \\ step_det r_ret_err
            \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
                 [det_run_def, cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
                  arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ fs [arm8_ok_erase, sp_ok_def])

      val recv_post_ok_det = prove(
        ``∀cb_begin cb_end bm_buf_end s k c m.
            1 ≤ m ∧ m ≤ c ∧ c + k = ^n_tm ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x450070w ∧ s.REG 0w = n2w m ∧
            s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ⇒
            ∃s'.
              det_run 7 s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
              s'.PC = 0x450058w ∧ s'.MEM = s.MEM ∧
              s'.REG 10w = FORGE_RX_TMP + n2w (k + m) ∧ s'.REG 11w = n2w (c - m) ∧
              (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)``,
        rpt strip_tac
        \\ `¬word_msb (n2w m : word64) ∧ (n2w m : word64) ≠ 0w ∧ (n2w m : word64) ≠ -4w` by
           (simp [wordsTheory.word_msb_n2w, wordsTheory.n2w_11, dimword_64]
            \\ `¬BIT 63 m` by (irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
            \\ `(-4w:word64) = n2w 18446744073709551612` by EVAL_TAC
            \\ simp [wordsTheory.n2w_11, dimword_64])
        \\ `-1w * (n2w m : word64) + n2w c = n2w (c - m)` by
           (ONCE_REWRITE_TAC [cj 1 word64_arith_step_helpers]
            \\ mp_tac (Q.SPECL [`c`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub)) \\ simp [])
        \\ `(n2w m : word64) + (FORGE_RX_TMP + n2w k) = FORGE_RX_TMP + n2w (k + m)` by
           (ONCE_REWRITE_TAC [cj 2 word64_arith_step_helpers] \\ simp [wordsTheory.word_add_n2w])
        \\ qexists_tac `s with <|PC := 0x450058w;
                                 REG := s.REG⦇10w ↦ FORGE_RX_TMP + n2w (k + m); 11w ↦ n2w (c - m)⦈;
                                 PSTATE := s.PSTATE with
                                   <|V := F;
                                     C := ((if w2n (n2w m:word64) + 18446744073709551615 + 1 < 18446744073709551616
                                            then w2n (n2w m:word64) + 18446744073709551615 + 1
                                            else (w2n (n2w m:word64) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                           w2n (n2w m:word64) + 18446744073709551615 + 1);
                                     Z := F; N := F|>;
                                 branch_hint := SOME BranchType_JMP|>`
        \\ conj_tac
        >- (step_det r_cmn4 \\ step_det r_beq_ne \\ step_det r_cmp0 \\ step_det r_ble_gt
            \\ step_det r_add10_x0 \\ step_det r_sub11_x0 \\ step_det r_b_loop
            \\ simp [det_run_def, cmp_zero_gt_cond,
                     arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                     combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ `aligned 2 (0x450058w:word64)` by EVAL_TAC
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ fs [arm8_ok_erase, sp_ok_def])

      val recv_read_loop_universal = prove(
        ``∀n allow_err wrel cb_begin cb_end bm_buf_end k c acc s inp out inp_f out_f ms_f ec (p:word64).
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            c + k = ^n_tm ∧ LENGTH acc = k ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x450058w ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            s.REG 9w = p ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ∧
            p ∈ forge_prog_addresses_slot cb_end bm_buf_end ∧
            (∀i. i < k ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i acc) ∧
            NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
                n (inp, out, s) (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel ec ms_f ⇒
            (∃n' s' frame inp_after.
               n' < n ∧ LENGTH frame = ^n_tm ∧ acc ++ inp = frame ++ inp_after ∧
               NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
                   n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
               arm8_ok (erase s') ∧ sp_ok s' ∧
               shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
               bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
               s'.PC = 0x450098w ∧ s'.REG 9w = p ∧ s'.REG 12w = FORGE_RX_TMP ∧ s'.REG 11w = 0w ∧
               s'.REG 30w = s.REG 30w ∧
               (∀i. i < ^n_tm ⇒ s'.MEM (FORGE_RX_TMP + n2w i) = EL i frame) ∧
               (∀a. a ∉ forge_rx_tmp_region ⇒ s'.MEM a = s.MEM a) ∧
               (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
            (∃n' s' inp_after.
               n' < n ∧ (allow_err ∨ LENGTH (acc ++ inp) < ^n_tm) ∧
               NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
                   n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
               arm8_ok (erase s') ∧ sp_ok s' ∧
               shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
               bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
               s'.PC = s.REG 30w ∧
               (∀a. a ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒ s'.MEM a = (p =+ 1w) s.MEM a) ∧
               (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
        completeInduct_on `n` \\ rpt strip_tac
        \\ Cases_on `c = 0`
        >- (
          `k = ^n_tm` by decide_tac \\ rveq
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_loop_done_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ disj1_tac
          \\ qexists_tac `n - 4` \\ qexists_tac `s_cp0` \\ qexists_tac `acc` \\ qexists_tac `inp`
          \\ simp [] \\ rpt strip_tac \\ rveq \\ simp [])
        \\ `1 ≤ c` by decide_tac
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `k`, `c`] mp_tac recv_loop_to_svc_det
        \\ impl_tac >- simp [] \\ strip_tac
        \\ peel_nrc_tac
        \\ Cases_on `n - 5`
        >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
        \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
        \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_svc_read_det]
        \\ rpt strip_tac
        \\ rename1 `NRC _ _ (z0, out, z2) _`
        \\ `s_svc.REG 8w = 63w ∧ s_svc.REG 0w = 0w ∧ s_svc.REG 1w = FORGE_RX_TMP + n2w k ∧
            s_svc.REG 2w = n2w c ∧ s_svc.REG 9w = p ∧ s_svc.REG 10w = FORGE_RX_TMP + n2w k ∧
            s_svc.REG 11w = n2w c ∧ s_svc.REG 30w = s.REG 30w` by simp []
        \\ `svc_read_rel inp s_svc z2 z0 ∧ (¬allow_err ⇒ svc_read_noerr_rel inp s_svc z2 z0)` by
             (Cases_on `allow_err` \\ fs [svc_read_noerr_imp_rel])
        \\ qpat_x_assum `svc_read_rel _ _ _ _`
             (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_read_rel_def, svc_frame_rel_def])
        \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
            z2.PC = 0x450070w ∧ z2.REG 9w = p ∧ z2.REG 10w = FORGE_RX_TMP + n2w k ∧
            z2.REG 11w = n2w c ∧ z2.REG 30w = s.REG 30w ∧
            (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
             (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
              \\ rpt conj_tac
              \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
              \\ TRY (fs [sp_ok_def] \\ NO_TAC)
              \\ TRY (fs [bits_of_def] \\ NO_TAC)
              \\ rpt strip_tac \\ rveq \\ simp [])
        \\ qpat_x_assum `_ ∨ _ ∨ _ ∨ _` (REPEAT_TCL DISJ_CASES_THEN strip_assume_tac)
        >- (
          qpat_x_assum `z0 = inp` SUBST_ALL_TAC
          \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end z2.MEM` by simp []
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac recv_post_eintr_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac)
          \\ impl_tac >- decide_tac
          \\ disch_then (qspecl_then [`allow_err`, `wrel`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                      `k`, `c`, `acc`, `s'`, `inp`, `out`, `inp_f`, `out_f`, `ms_f`, `ec`, `p`] mp_tac)
          \\ impl_tac >- simp []
          \\ strip_tac
          >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
              \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
          \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `inp_after`
          \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
        >- (
          qpat_x_assum `z0 = []` SUBST_ALL_TAC
          \\ qpat_x_assum `inp = []` SUBST_ALL_TAC
          \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end z2.MEM ∧ k < ^n_tm` by simp []
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac recv_post_err_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ disj2_tac
          \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `[]`
          \\ simp [combinTheory.APPLY_UPDATE_THM]
          \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
        >- (
          `allow_err` by
            (CCONTR_TAC
             \\ `svc_read_noerr_rel inp s_svc z2 z0 ∧ c ≤ 64` by
                  (conj_tac >- (qpat_x_assum `¬allow_err ⇒ _` irule \\ simp []) \\ decide_tac)
             \\ mp_tac (Q.SPECL [`inp`, `s_svc`, `z2`, `z0`, `c`] svc_read_noerr_not_fatal) \\ simp [])
          \\ qpat_x_assum `z0 = inp` SUBST_ALL_TAC
          \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end z2.MEM` by simp []
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac recv_post_err_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ disj2_tac
          \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `inp`
          \\ simp [combinTheory.APPLY_UPDATE_THM]
          \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
        \\ rename1 `z2.REG 0w = n2w m`
        \\ qpat_x_assum `z0 = DROP m inp` SUBST_ALL_TAC
        \\ `m ≤ c` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
        \\ `∀a. a ∉ forge_rx_tmp_region ⇒ z2.MEM a = s.MEM a` by
             (rpt strip_tac \\ simp []
              \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
              \\ `i < m` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
              \\ `FORGE_RX_TMP + n2w k + n2w i ∈ forge_rx_tmp_region` by
                   (simp [forge_rx_tmp_region_def, FORGE_RX_TMP_def, word_add_n2w_right,
                          wordsTheory.word_add_n2w, WORD_LS, WORD_LO, w2n_n2w, dimword_64])
              \\ rveq \\ fs [])
        \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end z2.MEM` by
             (mp_tac (SPECL [shim_ws_tm, ``cb_begin:word64``, ``cb_end:word64``, ``bm_buf_end:word64``,
                             ``(z2:arm8_state).MEM``, ``(s:arm8_state).MEM``] shim_loaded_slot_cong)
              \\ impl_tac
              >- (conj_tac >- simp [shim_len_th]
                  \\ rpt strip_tac \\ first_x_assum irule \\ strip_tac
                  \\ drule forge_regions_disjoint_slot \\ strip_tac
                  \\ qpat_assum `∀a. a ∈ forge_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
              \\ simp [])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `k`, `c`, `m`] mp_tac recv_post_ok_det
        \\ impl_tac >- simp [] \\ strip_tac
        \\ peel_nrc_tac
        \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 7` mp_tac)
        \\ impl_tac >- decide_tac
        \\ disch_then (qspecl_then [`allow_err`, `wrel`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                    `k + m`, `c - m`, `acc ++ TAKE m inp`,
                                    `s'`, `DROP m inp`, `out`, `inp_f`, `out_f`, `ms_f`, `ec`, `p`] mp_tac)
        \\ impl_tac
        >- (
          simp [] \\ rpt strip_tac
          \\ Cases_on `i < k`
          >- (simp [EL_APPEND1]
              \\ `asm_write_bytearray (FORGE_RX_TMP + n2w k) (TAKE m inp) s.MEM (FORGE_RX_TMP + n2w i) =
                  s.MEM (FORGE_RX_TMP + n2w i)` by
                 (irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
                  \\ `i' < m` by (qpat_x_assum `i' < LENGTH _` mp_tac \\ simp [])
                  \\ qpat_x_assum `FORGE_RX_TMP + n2w i = _` mp_tac
                  \\ simp [word_add_n2w_right, wordsTheory.word_add_n2w,
                           wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
              \\ simp [])
          \\ simp [EL_APPEND2]
          \\ `i - k < m` by decide_tac
          \\ `FORGE_RX_TMP + n2w i = (FORGE_RX_TMP + n2w k) + n2w (i - k)` by
               simp [word_add_n2w_right, wordsTheory.word_add_n2w]
          \\ pop_assum SUBST1_TAC
          \\ `asm_write_bytearray (FORGE_RX_TMP + n2w k) (TAKE m inp) s.MEM
                ((FORGE_RX_TMP + n2w k) + n2w (i - k)) = EL (i - k) (TAKE m inp)` by
               (irule asm_write_bytearray_read_el \\ simp [dimword_64])
          \\ simp [])
        \\ strip_tac
        >- (
          `(acc ++ TAKE m inp) ++ DROP m inp = acc ++ inp` by simp [listTheory.TAKE_DROP]
          \\ pop_assum SUBST_ALL_TAC
          \\ disj1_tac
          \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
          \\ fs [] \\ rpt conj_tac \\ TRY decide_tac
          >- (rpt strip_tac
              \\ qpat_x_assum `∀a. a ∉ forge_rx_tmp_region ⇒ z2.MEM a = s.MEM a` (mp_tac o Q.SPEC `a`)
              \\ simp [])
          \\ rpt strip_tac \\ rveq \\ simp [])
        \\ (`(acc ++ TAKE m inp) ++ DROP m inp = acc ++ inp` by simp [listTheory.TAKE_DROP]
            \\ pop_assum SUBST_ALL_TAC
            \\ disj2_tac
            \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `inp_after`
            \\ fs [] \\ rpt conj_tac \\ TRY decide_tac
            >- (rpt strip_tac
                \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ drule forge_regions_disjoint_slot \\ strip_tac \\ qpat_assum `∀a. a ∈ forge_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
                \\ qpat_x_assum `∀a. a ∉ forge_rx_tmp_region ⇒ z2.MEM a = s.MEM a` (mp_tac o Q.SPEC `a`)
                \\ simp [combinTheory.APPLY_UPDATE_THM])
            \\ rpt strip_tac \\ rveq \\ simp []))

      val recv_universal = store_thm("ffirecv" ^ ns ^ "_universal_slot",
        ``∀cb_begin cb_end bm_buf_end allow_err wrel n s inp out inp_f out_f ms_f ec bytes2.
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFIRECV_VENEER ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            read_bytearray (s.REG 2w) (w2n (s.REG 3w))
              (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
            NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
                n (inp, out, s) (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel ec ms_f ⇒
            (w2n (s.REG 3w) < ^np1_tm ⇒
               ∃n' s'. n' < n ∧
                 NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
                     n' (inp, out, s') (inp_f, out_f, ms_f) ∧
                 ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end bytes2 s s') ∧
            (^np1_tm ≤ w2n (s.REG 3w) ⇒
               (∃n' s' frame inp_after.
                  n' < n ∧ LENGTH frame = ^n_tm ∧ inp = frame ++ inp_after ∧
                  NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
                      n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
                  ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (0w :: frame ++ DROP ^np1_tm bytes2) s s') ∨
               (∃n' s' inp_after.
                  n' < n ∧ (allow_err ∨ LENGTH inp < ^n_tm) ∧
                  NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
                      n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
                  ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s'))``,
        rpt strip_tac
        >- (
          qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac recv_short_det \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
        \\ drule forge_regions_disjoint_slot \\ strip_tac
        \\ imp_res_tac read_bytearray_mem_eq
        \\ qabbrev_tac `p = s.REG 2w`
        \\ `∀i. i < ^np1_tm ⇒ p + n2w i ∈ forge_prog_addresses_slot cb_end bm_buf_end` by
             (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses_slot _ _` (qspec_then `i` mp_tac) \\ simp [])
        \\ `p ∈ forge_prog_addresses_slot cb_end bm_buf_end` by
             (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses_slot _ _` (mp_tac o Q.SPEC `0`)
              \\ impl_tac >- decide_tac
              \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_entry_det \\ impl_tac >- simp [] \\ strip_tac
        \\ peel_nrc_tac
        \\ qspecl_then [`n - 7`, `allow_err`, `wrel`, `cb_begin`, `cb_end`, `bm_buf_end`,
                        `0`, `^n_tm`, `[]`, `s_loop`, `inp`, `out`,
                        `inp_f`, `out_f`, `ms_f`, `ec`, `p`] mp_tac recv_read_loop_universal
        \\ impl_tac >- simp []
        \\ strip_tac
        >- (
          qspecl_then [`^n_tm`, `0`, `cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `frame`, `p`] mp_tac recv_copy_loop_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ disj1_tac
          \\ qexists_tac `n' - d` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
          \\ `asm_write_bytearray (s.REG 2w) (0w :: frame ++ DROP ^np1_tm bytes2) s.MEM =
              (p =+ 0w) (asm_write_bytearray (p + 1w) frame s.MEM)` by
               (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
                \\ qspecl_then [`^n_tm`, `p`, `forge_prog_addresses_slot cb_end bm_buf_end`, `s.MEM`, `bytes2`, `frame`]
                     mp_tac asm_write_bytearray_drop_np1 \\ simp [])
          \\ REWRITE_TAC [ffi_return_ok_slot_def]
          \\ pop_assum SUBST1_TAC
          \\ fs [] \\ rpt conj_tac \\ TRY decide_tac
          \\ rpt strip_tac
          \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
          \\ irule asm_write_bytearray_pointwise
          \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
          \\ simp [])
        \\ disj2_tac
        \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `inp_after`
        \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
             (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
              \\ qspecl_then [`p`, `forge_prog_addresses_slot cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
                   asm_write_bytearray_drop1 \\ simp [])
        \\ REWRITE_TAC [ffi_return_ok_slot_def]
        \\ pop_assum SUBST1_TAC
        \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])

      val recv_noerr_exists = store_thm("ffirecv" ^ ns ^ "_noerr_exists_slot",
        ``∀cb_begin cb_end bm_buf_end s bytes2.
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFIRECV_VENEER ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            read_bytearray (s.REG 2w) (w2n (s.REG 3w))
              (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
            (w2n (s.REG 3w) < ^np1_tm ⇒
               ∃s'. (∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
                    ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end bytes2 s s') ∧
            (∀f. ^np1_tm ≤ w2n (s.REG 3w) ∧ LENGTH f = ^n_tm ⇒
               ∃s'. (∀rest out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                                    (f ++ rest, out, s) (rest, out, s')) ∧
                    ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (0w :: f ++ DROP ^np1_tm bytes2) s s') ∧
            (∀tail_bs. ^np1_tm ≤ w2n (s.REG 3w) ∧ LENGTH tail_bs < ^n_tm ⇒
               ∃s'. (∀out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (tail_bs, out, s) ([], out, s')) ∧
                    ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s')``,
        rpt strip_tac
        >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac recv_short_det \\ impl_tac >- simp [] \\ strip_tac
            \\ qexists_tac `s'` \\ simp []
            \\ metis_tac [det_run_imp_nrc, arithmeticTheory.RTC_eq_NRC])
        >- (
          drule forge_regions_disjoint_slot \\ strip_tac
          \\ imp_res_tac read_bytearray_mem_eq
          \\ qabbrev_tac `p = s.REG 2w`
          \\ `∀i. i < ^np1_tm ⇒ p + n2w i ∈ forge_prog_addresses_slot cb_end bm_buf_end` by
               (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses_slot _ _` (qspec_then `i` mp_tac) \\ simp [])
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_entry_det \\ impl_tac >- simp [] \\ strip_tac
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `^n_tm`] mp_tac recv_loop_to_svc_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP f s.MEM`
          \\ qabbrev_tac `s_post = s_svc with <|PC := 0x450070w; REG := s_svc.REG⦇0w ↦ ^n_w64⦈; MEM := m1|>`
          \\ `∀rest out. whole_step svc_read_noerr_rel svc_write_noerr_rel (f ++ rest, out, s_svc) (rest, out, s_post)` by
               (rpt strip_tac
                \\ simp [whole_step_def, Abbr `s_post`, svc_read_noerr_rel_def, svc_frame_rel_def,
                         combinTheory.APPLY_UPDATE_THM]
                \\ conj_tac >- fs [arm8_ok_erase]
                \\ qexists_tac `^n_tm` \\ simp [Abbr `m1`, TAKE_APPEND1, DROP_APPEND2, listTheory.TAKE_LENGTH_ID_rwt])
          \\ `∀a. a ∉ forge_rx_tmp_region ⇒ m1 a = s.MEM a` by
               (rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt
                \\ rpt strip_tac
                \\ `FORGE_RX_TMP + n2w i ∈ forge_rx_tmp_region` by
                     simp [forge_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
                           word_add_n2w, w2n_n2w, dimword_64]
                \\ rveq \\ fs [])
          \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end m1` by
               (mp_tac (SPECL [shim_ws_tm, ``cb_begin:word64``, ``cb_end:word64``, ``bm_buf_end:word64``,
                               ``m1:word64 -> word8``, ``(s:arm8_state).MEM``] shim_loaded_slot_cong)
                \\ impl_tac
                >- (conj_tac >- simp [shim_len_th]
                    \\ rpt strip_tac \\ first_x_assum irule \\ strip_tac \\ qpat_assum `∀a. a ∈ forge_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
                \\ simp [])
          \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
               (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
                \\ rpt conj_tac
                \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
                \\ gvs [sp_ok_def, bits_of_def])
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `0`, `^n_tm`, `^n_tm`] mp_tac recv_post_ok_det
          \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`] mp_tac recv_loop_done_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ qspecl_then [`^n_tm`, `0`, `cb_begin`, `cb_end`, `bm_buf_end`, `s_cp0`, `f`, `p`] mp_tac recv_copy_loop_det
          \\ impl_tac
          >- (simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM, Abbr `m1`]
              \\ rpt strip_tac \\ irule asm_write_bytearray_read_el \\ simp [dimword_64])
          \\ strip_tac
          \\ qexists_tac `s''`
          \\ conj_tac
          >- (rpt strip_tac
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `(f ++ rest, out, s_loop)`
              \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `(f ++ rest, out, s_svc)`
              \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `(rest, out, s_post)`
              \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `(rest, out, s')`
              \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `(rest, out, s_cp0)`
              \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `4` \\ simp [])
              \\ irule det_run_imp_rtc \\ qexists_tac `d` \\ simp [])
          \\ `asm_write_bytearray (s.REG 2w) (0w :: f ++ DROP ^np1_tm bytes2) s.MEM =
              (p =+ 0w) (asm_write_bytearray (p + 1w) f s.MEM)` by
               (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
                \\ qspecl_then [`^n_tm`, `p`, `forge_prog_addresses_slot cb_end bm_buf_end`, `s.MEM`, `bytes2`, `f`]
                     mp_tac asm_write_bytearray_drop_np1 \\ simp [])
          \\ REWRITE_TAC [ffi_return_ok_slot_def]
          \\ pop_assum SUBST1_TAC
          \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
          \\ rpt conj_tac
          >- (rpt strip_tac
              \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
              \\ irule asm_write_bytearray_pointwise
              \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
              \\ simp [])
          \\ rpt strip_tac \\ rveq \\ simp [])
        \\ drule forge_regions_disjoint_slot \\ strip_tac
        \\ imp_res_tac read_bytearray_mem_eq
        \\ qabbrev_tac `p = s.REG 2w`
        \\ `p ∈ forge_prog_addresses_slot cb_end bm_buf_end` by
             (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses_slot _ _` (mp_tac o Q.SPEC `0`)
              \\ impl_tac >- decide_tac
              \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
        \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
             (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
              \\ qspecl_then [`p`, `forge_prog_addresses_slot cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
                   asm_write_bytearray_drop1 \\ simp [])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_entry_det \\ impl_tac >- simp [] \\ strip_tac
        \\ Cases_on `tail_bs = []`
        >- (
          rveq
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `^n_tm`] mp_tac recv_loop_to_svc_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ qabbrev_tac `s_post = s_svc with <|PC := 0x450070w; REG := s_svc.REG⦇0w ↦ 0w⦈|>`
          \\ `∀out. whole_step svc_read_noerr_rel svc_write_noerr_rel ([], out, s_svc) ([], out, s_post)` by
               (gen_tac \\ simp [whole_step_def, Abbr `s_post`, svc_read_noerr_rel_def, svc_frame_rel_def,
                                 combinTheory.APPLY_UPDATE_THM] \\ fs [arm8_ok_erase])
          \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
               (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
                \\ rpt conj_tac
                \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
                \\ gvs [sp_ok_def, bits_of_def])
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `p`] mp_tac recv_post_err_det
          \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
          \\ qexists_tac `s'`
          \\ conj_tac
          >- (gen_tac
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `([], out, s_loop)`
              \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `([], out, s_svc)`
              \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
              \\ irule relationTheory.RTC_RTC \\ qexists_tac `([], out, s_post)`
              \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
              \\ irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
          \\ REWRITE_TAC [ffi_return_ok_slot_def]
          \\ qpat_x_assum `asm_write_bytearray (s.REG 2w) _ _ = _` SUBST1_TAC
          \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
          \\ rpt strip_tac \\ rveq \\ simp [])
        \\ `1 ≤ LENGTH tail_bs` by (Cases_on `tail_bs` \\ fs [])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `^n_tm`] mp_tac recv_loop_to_svc_det
        \\ impl_tac >- simp [] \\ strip_tac
        \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP tail_bs s.MEM`
        \\ qabbrev_tac `s_post1 = s_svc with <|PC := 0x450070w; REG := s_svc.REG⦇0w ↦ n2w (LENGTH tail_bs)⦈; MEM := m1|>`
        \\ `∀out. whole_step svc_read_noerr_rel svc_write_noerr_rel (tail_bs, out, s_svc) ([], out, s_post1)` by
             (gen_tac \\ simp [whole_step_def, Abbr `s_post1`, svc_read_noerr_rel_def, svc_frame_rel_def,
                               combinTheory.APPLY_UPDATE_THM]
              \\ conj_tac >- fs [arm8_ok_erase]
              \\ qexists_tac `LENGTH tail_bs`
              \\ simp [Abbr `m1`, listTheory.TAKE_LENGTH_ID_rwt, listTheory.DROP_LENGTH_NIL])
        \\ `∀a. a ∉ forge_rx_tmp_region ⇒ m1 a = s.MEM a` by
             (rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt
              \\ rpt strip_tac
              \\ `FORGE_RX_TMP + n2w i ∈ forge_rx_tmp_region` by
                   simp [forge_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
                         word_add_n2w, w2n_n2w, dimword_64]
              \\ rveq \\ fs [])
        \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end m1` by
             (mp_tac (SPECL [shim_ws_tm, ``cb_begin:word64``, ``cb_end:word64``, ``bm_buf_end:word64``,
                             ``m1:word64 -> word8``, ``(s:arm8_state).MEM``] shim_loaded_slot_cong)
              \\ impl_tac
              >- (conj_tac >- simp [shim_len_th]
                  \\ rpt strip_tac \\ first_x_assum irule \\ strip_tac \\ qpat_assum `∀a. a ∈ forge_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
              \\ simp [])
        \\ `arm8_ok (erase s_post1) ∧ sp_ok s_post1 ∧ bits_of s_post1 = bits_of s ∧ s_post1.SP_EL0 = s.SP_EL0` by
             (simp [Abbr `s_post1`, arm8_ok_erase, sp_ok_def, bits_of_def]
              \\ rpt conj_tac
              \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
              \\ gvs [sp_ok_def, bits_of_def])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post1`, `0`, `^n_tm`, `LENGTH tail_bs`]
             mp_tac recv_post_ok_det
        \\ impl_tac >- simp [Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `LENGTH tail_bs`, `^n_tm - LENGTH tail_bs`]
             mp_tac recv_loop_to_svc_det
        \\ impl_tac >- simp [] \\ strip_tac
        \\ qabbrev_tac `s_post2 = s_svc' with <|PC := 0x450070w; REG := s_svc'.REG⦇0w ↦ 0w⦈|>`
        \\ `∀out. whole_step svc_read_noerr_rel svc_write_noerr_rel ([], out, s_svc') ([], out, s_post2)` by
             (gen_tac \\ simp [whole_step_def, Abbr `s_post2`, svc_read_noerr_rel_def, svc_frame_rel_def,
                               combinTheory.APPLY_UPDATE_THM] \\ fs [arm8_ok_erase])
        \\ `arm8_ok (erase s_post2) ∧ sp_ok s_post2 ∧ bits_of s_post2 = bits_of s ∧ s_post2.SP_EL0 = s.SP_EL0` by
             (simp [Abbr `s_post2`, arm8_ok_erase, sp_ok_def, bits_of_def]
              \\ rpt conj_tac
              \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
              \\ gvs [sp_ok_def, bits_of_def])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post2`, `p`] mp_tac recv_post_err_det
        \\ impl_tac >- simp [Abbr `s_post2`, Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
        \\ qexists_tac `s''`
        \\ conj_tac
        >- (gen_tac
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `(tail_bs, out, s_loop)`
            \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `(tail_bs, out, s_svc)`
            \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `([], out, s_post1)`
            \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `([], out, s')`
            \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `([], out, s_svc')`
            \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `([], out, s_post2)`
            \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
            \\ irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
        \\ REWRITE_TAC [ffi_return_ok_slot_def]
        \\ qpat_x_assum `asm_write_bytearray (s.REG 2w) _ _ = _` SUBST1_TAC
        \\ simp [Abbr `s_post2`, Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM]
        \\ rpt conj_tac
        >- (rpt strip_tac \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp []) \\ simp [combinTheory.APPLY_UPDATE_THM])
        \\ rpt strip_tac \\ rveq \\ simp [])

      val send_short_det = prove(
        ``∀cb_begin cb_end bm_buf_end s bytes2.
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFISEND_VENEER ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            read_bytearray (s.REG 2w) (w2n (s.REG 3w))
              (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
            w2n (s.REG 3w) < ^np1_tm ⇒
            ∃s'. det_run 4 s s' ∧ ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end bytes2 s s'``,
        rpt strip_tac
        \\ `s.PC = 0x400080w` by fs [FORGE_FFISEND_VENEER_def]
        \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by
             (irule asm_write_bytearray_id \\ metis_tac [])
        \\ qexists_tac `s with <|PC := s.REG 30w;
                                 PSTATE := s.PSTATE with
                                   <|V := (word_msb (s.REG 3w) ∧
                                           (word_msb (s.REG 3w) ⇎
                                            BIT 63 (w2n (s.REG 3w) + ^c_np1_tm + 1)));
                                     C := F;
                                     Z := (s.REG 3w + ^neg_np1_w64 = 0w);
                                     N := word_msb (s.REG 3w + ^neg_np1_w64)|>;
                                 branch_hint := SOME BranchType_RET|>`
        \\ conj_tac
        >- (step_det v_send \\ step_det s_cmp_np1 \\ step_det s_blo_lt \\ step_det s_ret_err
            \\ simp [det_run_def, cmp_carry_17, cmp_carry_65, arm8Theory.arm8_state_component_equality])
        \\ simp [ffi_return_ok_slot_def, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ fs [arm8_ok_erase, sp_ok_def])

      val send_entry_det = prove(
        ``∀cb_begin cb_end bm_buf_end s.
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFISEND_VENEER ∧ ^np1_tm ≤ w2n (s.REG 3w) ⇒
            ∃s_loop.
              det_run 6 s s_loop ∧
              arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s_loop.MEM ∧
              bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
              s_loop.PC = 0x4500D4w ∧ s_loop.MEM = s.MEM ∧
              s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = s.REG 2w + 1w ∧ s_loop.REG 11w = ^n_w64 ∧
              s_loop.REG 30w = s.REG 30w ∧
              (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))``,
        rpt strip_tac
        \\ `s.PC = 0x400080w` by fs [FORGE_FFISEND_VENEER_def]
        \\ qabbrev_tac `p = s.REG 2w`
        \\ qexists_tac `s with <|PC := 0x4500D4w;
                                 REG := s.REG⦇9w ↦ p; 10w ↦ p + 1w; 11w ↦ ^n_w64⦈;
                                 PSTATE := s.PSTATE with
                                   <|V := (word_msb (s.REG 3w) ∧
                                           (word_msb (s.REG 3w) ⇎
                                            BIT 63 (w2n (s.REG 3w) + ^c_np1_tm + 1)));
                                     C := T;
                                     Z := (s.REG 3w + ^neg_np1_w64 = 0w);
                                     N := word_msb (s.REG 3w + ^neg_np1_w64)|>;
                                 branch_hint := NONE|>`
        \\ conj_tac
        >- (step_det v_send \\ step_det s_cmp_np1 \\ step_det s_blo_ge \\ step_det s_mov9
            \\ step_det s_add10 \\ step_det s_mov11_n
            \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
                 [det_run_def, Abbr `p`, cmp_carry_17, cmp_carry_65,
                  arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                  combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
        \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

      val send_loop_done_det = prove(
        ``∀cb_begin cb_end bm_buf_end s (p:word64).
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x4500D4w ∧ s.REG 9w = p ∧ s.REG 11w = 0w ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            p ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒
            ∃s'.
              det_run 3 s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
              s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧ s'.REG = s.REG``,
        rpt strip_tac
        \\ drule forge_regions_disjoint_slot \\ strip_tac
        \\ `p ∉ forge_shim_code_region` by simp []
        \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 0w⦈)` by
             simp [shim_loaded_slot_update, shim_len_th]
        \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 0w⦈; PC := s.REG 30w; branch_hint := SOME BranchType_RET|>`
        \\ conj_tac
        >- (step_det s_cbz_z \\ step_det s_strb_0 \\ step_det s_ret_ok
            \\ simp [det_run_def, arm8Theory.arm8_state_component_equality])
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ fs [arm8_ok_erase, sp_ok_def])

      val send_loop_to_svc_det = prove(
        ``∀cb_begin cb_end bm_buf_end s (p:word64) k c.
            1 ≤ c ∧ c + k = ^n_tm ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x4500D4w ∧ s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w c ⇒
            ∃s_svc.
              det_run 5 s s_svc ∧
              arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s_svc.MEM ∧
              bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
              s_svc.PC = 0x4500E8w ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
              s_svc.REG 0w = 1w ∧ s_svc.REG 1w = p + n2w (k + 1) ∧
              s_svc.REG 2w = n2w c ∧ s_svc.REG 8w = 64w ∧
              (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
        rpt strip_tac
        \\ qabbrev_tac `s_svc = s with <|PC := 0x4500E8w;
                                         REG := s.REG⦇0w ↦ 1w; 1w ↦ p + n2w (k + 1);
                                                      2w ↦ n2w c; 8w ↦ 64w⦈;
                                         branch_hint := NONE|>`
        \\ qexists_tac `s_svc`
        \\ conj_tac
        >- (step_det s_cbz_nz \\ step_det s_mov0 \\ step_det s_mov1 \\ step_det s_mov2 \\ step_det s_mov8
            \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                     combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ `is_svc0_at s_svc` by (irule s_svc \\ simp [Abbr `s_svc`] \\ metis_tac [])
        \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

      val send_post_eintr_det = prove(
        ``∀cb_begin cb_end bm_buf_end s.
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x4500ECw ∧ s.REG 0w = -4w ⇒
            ∃s'.
              det_run 2 s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
              s'.PC = 0x4500D4w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
        rpt strip_tac
        \\ qexists_tac `s with <|PC := 0x4500D4w;
                                 PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                                 branch_hint := SOME BranchType_JMP|>`
        \\ conj_tac
        >- (step_det s_cmn4 \\ step_det s_beq_eq
            \\ simp [det_run_def, arm8Theory.arm8_state_component_equality,
                     arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

      val send_post_err_det = prove(
        ``∀cb_begin cb_end bm_buf_end s (p:word64).
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x4500ECw ∧ s.REG 9w = p ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            p ∈ forge_prog_addresses_slot cb_end bm_buf_end ∧
            (s.REG 0w = 0w ∨ (word_msb (s.REG 0w) ∧ s.REG 0w ≠ -4w)) ⇒
            ∃s'.
              det_run 7 s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
              s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
              (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)``,
        rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
        \\ drule forge_regions_disjoint_slot \\ strip_tac
        \\ `p ∉ forge_shim_code_region` by simp []
        \\ `shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 1w⦈)` by
             simp [shim_loaded_slot_update, shim_len_th]
        \\ `s.REG 0w ≠ -4w ∧ (¬word_msb (s.REG 0w) ⇒ s.REG 0w = 0w)` by
             (Cases_on `s.REG 0w = 0w` \\ fs [] \\ EVAL_TAC)
        \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 1w⦈; PC := s.REG 30w;
                                 REG := s.REG⦇12w ↦ 1w⦈;
                                 PSTATE := s.PSTATE with
                                   <|V := (word_msb (s.REG 0w) ∧
                                           (word_msb (s.REG 0w) ⇎
                                            BIT 63 (w2n (s.REG 0w) + 18446744073709551615 + 1)));
                                     C := ((if w2n (s.REG 0w) + 18446744073709551615 + 1 < 18446744073709551616
                                            then w2n (s.REG 0w) + 18446744073709551615 + 1
                                            else (w2n (s.REG 0w) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                           w2n (s.REG 0w) + 18446744073709551615 + 1);
                                     Z := (s.REG 0w + 0w = 0w);
                                     N := word_msb (s.REG 0w + 0w)|>;
                                 branch_hint := SOME BranchType_RET|>`
        \\ conj_tac
        >- (step_det s_cmn4 \\ step_det s_beq_ne \\ step_det s_cmp0 \\ step_det s_ble_le
            \\ step_det s_mov12_1 \\ step_det s_strb_1 \\ step_det s_ret_err
            \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
                 [det_run_def, cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
                  arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ fs [arm8_ok_erase, sp_ok_def])

      val send_post_ok_det = prove(
        ``∀cb_begin cb_end bm_buf_end s (p:word64) k c m.
            1 ≤ m ∧ m ≤ c ∧ c + k = ^n_tm ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x4500ECw ∧ s.REG 0w = n2w m ∧
            s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w c ⇒
            ∃s'.
              det_run 7 s s' ∧
              arm8_ok (erase s') ∧ sp_ok s' ∧
              shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
              bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
              s'.PC = 0x4500D4w ∧ s'.MEM = s.MEM ∧
              s'.REG 10w = p + n2w (k + m + 1) ∧ s'.REG 11w = n2w (c - m) ∧
              (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)``,
        rpt strip_tac
        \\ `¬word_msb (n2w m : word64) ∧ (n2w m : word64) ≠ 0w ∧ (n2w m : word64) ≠ -4w` by
           (simp [wordsTheory.word_msb_n2w, wordsTheory.n2w_11, dimword_64]
            \\ `¬BIT 63 m` by (irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
            \\ `(-4w:word64) = n2w 18446744073709551612` by EVAL_TAC
            \\ simp [wordsTheory.n2w_11, dimword_64])
        \\ `-1w * (n2w m : word64) + n2w c = n2w (c - m)` by
           (ONCE_REWRITE_TAC [cj 1 word64_arith_step_helpers]
            \\ mp_tac (Q.SPECL [`c`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub)) \\ simp [])
        \\ `(n2w m : word64) + (p + n2w (k + 1)) = p + n2w (k + m + 1)` by
           (ONCE_REWRITE_TAC [cj 2 word64_arith_step_helpers]
            \\ simp [wordsTheory.word_add_n2w] \\ `k + 1 + m = k + m + 1` by decide_tac \\ simp [])
        \\ qexists_tac `s with <|PC := 0x4500D4w;
                                 REG := s.REG⦇10w ↦ p + n2w (k + m + 1); 11w ↦ n2w (c - m)⦈;
                                 PSTATE := s.PSTATE with
                                   <|V := F;
                                     C := ((if w2n (n2w m:word64) + 18446744073709551615 + 1 < 18446744073709551616
                                            then w2n (n2w m:word64) + 18446744073709551615 + 1
                                            else (w2n (n2w m:word64) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                           w2n (n2w m:word64) + 18446744073709551615 + 1);
                                     Z := F; N := F|>;
                                 branch_hint := SOME BranchType_JMP|>`
        \\ conj_tac
        >- (step_det s_cmn4 \\ step_det s_beq_ne \\ step_det s_cmp0 \\ step_det s_ble_gt
            \\ step_det s_add10_x0 \\ step_det s_sub11_x0 \\ step_det s_b_loop
            \\ simp [det_run_def, cmp_zero_gt_cond,
                     arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                     combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ `aligned 2 (0x4500D4w:word64)` by EVAL_TAC
        \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
        \\ fs [arm8_ok_erase, sp_ok_def])

      val send_write_loop_universal = prove(
        ``∀n allow_err rrel cb_begin cb_end bm_buf_end k c s inp out inp_f out_f ms_f ec (p:word64) (frame:word8 list).
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            c + k = ^n_tm ∧ LENGTH frame = ^n_tm ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = 0x4500D4w ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            s.REG 9w = p ∧ s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w c ∧
            p ∈ forge_prog_addresses_slot cb_end bm_buf_end ∧
            (∀i. i < ^n_tm ⇒ s.MEM (p + n2w (i + 1)) = EL i frame) ∧
            NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
                n (inp, out, s) (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel ec ms_f ⇒
            (∃n' s'.
               n' < n ∧
               NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
                   n' (inp, out ++ DROP k frame, s') (inp_f, out_f, ms_f) ∧
               arm8_ok (erase s') ∧ sp_ok s' ∧
               shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
               bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
               s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧
               (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
            (allow_err ∧
             ∃n' s' chunk.
               n' < n ∧ chunk ≼ DROP k frame ∧
               NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
                   n' (inp, out ++ chunk, s') (inp_f, out_f, ms_f) ∧
               arm8_ok (erase s') ∧ sp_ok s' ∧
               shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s'.MEM ∧
               bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
               s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
               (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
        completeInduct_on `n` \\ rpt strip_tac
        \\ Cases_on `c = 0`
        >- (
          `k = ^n_tm` by decide_tac \\ rveq
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `s.REG 9w`] mp_tac send_loop_done_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ disj1_tac
          \\ qexists_tac `n - 3` \\ qexists_tac `s'`
          \\ simp [listTheory.DROP_LENGTH_TOO_LONG])
        \\ `1 ≤ c` by decide_tac
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `p`, `k`, `c`] mp_tac send_loop_to_svc_det
        \\ impl_tac >- simp [] \\ strip_tac
        \\ peel_nrc_tac
        \\ Cases_on `n - 5`
        >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
        \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
        \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_svc_write_det]
        \\ rpt strip_tac
        \\ TRY (qpat_x_assum `_ = inp` SUBST_ALL_TAC)
        \\ TRY (qpat_x_assum `_ = out ++ _` SUBST_ALL_TAC)
        \\ rename1 `NRC _ _ (inp, out ++ chunk, z2) _`
        \\ `s_svc.REG 8w = 64w ∧ s_svc.REG 0w = 1w ∧ s_svc.REG 1w = p + n2w (k + 1) ∧
            s_svc.REG 2w = n2w c ∧ s_svc.REG 9w = p ∧ s_svc.REG 10w = p + n2w (k + 1) ∧
            s_svc.REG 11w = n2w c ∧ s_svc.REG 30w = s.REG 30w` by simp []
        \\ `svc_write_rel s_svc z2 chunk ∧ (¬allow_err ⇒ svc_write_noerr_rel s_svc z2 chunk)` by
             (Cases_on `allow_err` \\ fs [svc_write_noerr_imp_rel])
        \\ qpat_x_assum `svc_write_rel _ _ _`
             (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_write_rel_def, svc_frame_rel_def])
        \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
            z2.PC = 0x4500ECw ∧ z2.REG 9w = p ∧ z2.REG 10w = p + n2w (k + 1) ∧
            z2.REG 11w = n2w c ∧ z2.REG 30w = s.REG 30w ∧ z2.MEM = s.MEM ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end z2.MEM ∧
            (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
             (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
              \\ rpt conj_tac
              \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
              \\ TRY (fs [sp_ok_def] \\ NO_TAC)
              \\ TRY (fs [bits_of_def] \\ NO_TAC)
              \\ rpt strip_tac \\ rveq \\ simp [])
        \\ qpat_x_assum `_ ∨ _ ∨ _`
             (DISJ_CASES_THEN2 (REPEAT_TCL CONJUNCTS_THEN assume_tac)
                (DISJ_CASES_THEN2 strip_assume_tac (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
        >- (
          qpat_x_assum `chunk = []` SUBST_ALL_TAC
          \\ qpat_x_assum `NRC _ _ (inp, out ++ [], z2) _`
               (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac send_post_eintr_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac)
          \\ impl_tac >- decide_tac
          \\ disch_then (qspecl_then [`allow_err`, `rrel`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                      `k`, `c`, `s'`, `inp`, `out`, `inp_f`, `out_f`, `ms_f`, `ec`, `p`, `frame`] mp_tac)
          \\ impl_tac >- simp []
          \\ strip_tac
          >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''`
              \\ simp [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
          \\ disj2_tac \\ simp [] \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `chunk`
          \\ qpat_x_assum `NRC _ n'' _ _` mp_tac
          \\ simp [] \\ strip_tac \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
        >- (
          rename1 `z2.REG 0w = n2w m`
          \\ `m ≤ c` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
          \\ `chunk = TAKE m (DROP k frame)` by
               (simp [] \\ irule listTheory.LIST_EQ \\ simp [] \\ rpt strip_tac
                \\ simp [EL_TAKE, EL_DROP, word_add_n2w_right, wordsTheory.word_add_n2w]
                \\ `k + x < ^n_tm ∧ k + 1 + x = k + x + 1` by decide_tac
                \\ qpat_x_assum `∀i. i < ^n_tm ⇒ s.MEM _ = EL i frame` (qspec_then `k + x` mp_tac) \\ simp [])
          \\ qpat_x_assum `chunk = TAKE m (DROP k frame)` SUBST_ALL_TAC
          \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`, `k`, `c`, `m`] mp_tac send_post_ok_det
          \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 7` mp_tac)
          \\ impl_tac >- decide_tac
          \\ disch_then (qspecl_then [`allow_err`, `rrel`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                      `k + m`, `c - m`, `s'`, `inp`,
                                      `out ++ TAKE m (DROP k frame)`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                      `p`, `frame`] mp_tac)
          \\ impl_tac >- simp []
          \\ strip_tac
          >- (
            disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''`
            \\ `(out ++ TAKE m (DROP k frame)) ++ DROP (k + m) frame = out ++ DROP k frame` by
                 (`TAKE m (DROP k frame) ++ DROP (k + m) frame = DROP k frame` by
                    (`k + m = m + k` by decide_tac \\ pop_assum SUBST1_TAC
                     \\ PURE_ONCE_REWRITE_TAC [GSYM rich_listTheory.DROP_DROP_T]
                     \\ REWRITE_TAC [listTheory.TAKE_DROP])
                  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (SYM th)))) \\ simp []))
            \\ pop_assum SUBST_ALL_TAC
            \\ simp [] \\ rpt conj_tac \\ TRY decide_tac
            \\ rpt strip_tac \\ rveq \\ simp [])
          \\ disj2_tac \\ simp []
          \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `TAKE m (DROP k frame) ++ chunk`
          \\ `TAKE m (DROP k frame) ++ chunk ≼ DROP k frame` by
               (`TAKE m (DROP k frame) ++ DROP (k + m) frame = DROP k frame` by
                  (`k + m = m + k` by decide_tac \\ pop_assum SUBST1_TAC
                   \\ PURE_ONCE_REWRITE_TAC [GSYM rich_listTheory.DROP_DROP_T]
                   \\ REWRITE_TAC [listTheory.TAKE_DROP])
                \\ pop_assum (fn th => CONV_TAC (RAND_CONV (REWR_CONV (SYM th))) \\ simp []))
          \\ `(out ++ TAKE m (DROP k frame)) ++ chunk = out ++ (TAKE m (DROP k frame) ++ chunk)` by simp []
          \\ pop_assum SUBST_ALL_TAC
          \\ qpat_x_assum `NRC _ n'' _ _` mp_tac
          \\ simp [] \\ strip_tac \\ rpt conj_tac \\ TRY decide_tac
          \\ rpt strip_tac \\ rveq \\ simp [])
        \\ `allow_err` by
             (CCONTR_TAC
              \\ `svc_write_noerr_rel s_svc z2 chunk ∧ c ≤ 64` by
                   (conj_tac >- (qpat_x_assum `¬allow_err ⇒ _` irule \\ simp []) \\ decide_tac)
              \\ mp_tac (Q.SPECL [`s_svc`, `z2`, `chunk`, `c`] svc_write_noerr_not_err) \\ simp [])
        \\ qpat_x_assum `chunk = []` SUBST_ALL_TAC
        \\ qpat_x_assum `NRC _ _ (inp, out ++ [], z2) _`
             (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac send_post_err_det
        \\ impl_tac >- simp [] \\ strip_tac
        \\ peel_nrc_tac
        \\ disj2_tac \\ simp []
        \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `[]`
        \\ qpat_x_assum `NRC _ (n' - 7) _ _` mp_tac
        \\ simp [] \\ strip_tac \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])

      val send_universal = store_thm("ffisend" ^ ns ^ "_universal_slot",
        ``∀cb_begin cb_end bm_buf_end allow_err rrel n s inp out inp_f out_f ms_f ec bytes2.
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFISEND_VENEER ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            read_bytearray (s.REG 2w) (w2n (s.REG 3w))
              (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
            NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
                n (inp, out, s) (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel ec ms_f ⇒
            (w2n (s.REG 3w) < ^np1_tm ⇒
               ∃n' s'. n' < n ∧
                 NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
                     n' (inp, out, s') (inp_f, out_f, ms_f) ∧
                 ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end bytes2 s s') ∧
            (^np1_tm ≤ w2n (s.REG 3w) ⇒
               (∃n' s'.
                  n' < n ∧
                  NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
                      n' (inp, out ++ TAKE ^n_tm (DROP 1 bytes2), s') (inp_f, out_f, ms_f) ∧
                  ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (0w :: DROP 1 bytes2) s s') ∨
               (allow_err ∧
                ∃n' s' chunk.
                  n' < n ∧ chunk ≼ TAKE ^n_tm (DROP 1 bytes2) ∧
                  NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
                      n' (inp, out ++ chunk, s') (inp_f, out_f, ms_f) ∧
                  ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s'))``,
        rpt strip_tac
        >- (
          qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac send_short_det \\ impl_tac >- simp [] \\ strip_tac
          \\ peel_nrc_tac
          \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
        \\ imp_res_tac read_bytearray_mem_eq
        \\ qabbrev_tac `p = s.REG 2w`
        \\ `s.REG 2w = p` by simp [Abbr `p`]
        \\ `p ∈ forge_prog_addresses_slot cb_end bm_buf_end` by
             (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses_slot _ _` (mp_tac o Q.SPEC `0`)
              \\ impl_tac >- decide_tac
              \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac send_entry_det \\ impl_tac >- simp [] \\ strip_tac
        \\ peel_nrc_tac
        \\ qspecl_then [`n - 6`, `allow_err`, `rrel`, `cb_begin`, `cb_end`, `bm_buf_end`,
                        `0`, `^n_tm`, `s_loop`, `inp`, `out`,
                        `inp_f`, `out_f`, `ms_f`, `ec`, `p`, `TAKE ^n_tm (DROP 1 bytes2)`]
             mp_tac send_write_loop_universal
        \\ impl_tac
        >- (simp [] \\ rpt strip_tac
            \\ simp [EL_TAKE, EL_DROP]
            \\ `1 + i = i + 1` by decide_tac
            \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `i + 1` mp_tac) \\ simp [])
        \\ strip_tac
        >- (
          disj1_tac \\ qexists_tac `n'` \\ qexists_tac `s'`
          \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
               (qspecl_then [`p`, `forge_prog_addresses_slot cb_end bm_buf_end`, `s.MEM`, `bytes2`, `0w`]
                  mp_tac asm_write_bytearray_drop1 \\ simp [])
          \\ REWRITE_TAC [ffi_return_ok_slot_def]
          \\ pop_assum SUBST1_TAC
          \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
        \\ disj2_tac \\ simp []
        \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `chunk`
        \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
             (qspecl_then [`p`, `forge_prog_addresses_slot cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`]
                mp_tac asm_write_bytearray_drop1 \\ simp [])
        \\ REWRITE_TAC [ffi_return_ok_slot_def]
        \\ pop_assum SUBST1_TAC
        \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])

      val send_noerr_exists = store_thm("ffisend" ^ ns ^ "_noerr_exists_slot",
        ``∀cb_begin cb_end bm_buf_end s bytes2.
            slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            shim_loaded_slot ^shim_ws_tm cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = FORGE_FFISEND_VENEER ∧
            aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
            read_bytearray (s.REG 2w) (w2n (s.REG 3w))
              (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
            (w2n (s.REG 3w) < ^np1_tm ⇒
               ∃s'. (∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
                    ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end bytes2 s s') ∧
            (^np1_tm ≤ w2n (s.REG 3w) ⇒
               ∃s'. (∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                                   (inp, out, s) (inp, out ++ TAKE ^n_tm (DROP 1 bytes2), s')) ∧
                    ffi_return_ok_slot ^shim_ws_tm cb_begin cb_end bm_buf_end (0w :: DROP 1 bytes2) s s')``,
        rpt strip_tac
        >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac send_short_det \\ impl_tac >- simp [] \\ strip_tac
            \\ qexists_tac `s'` \\ simp []
            \\ metis_tac [det_run_imp_nrc, arithmeticTheory.RTC_eq_NRC])
        \\ imp_res_tac read_bytearray_mem_eq
        \\ qabbrev_tac `p = s.REG 2w`
        \\ `s.REG 2w = p` by simp [Abbr `p`]
        \\ `p ∈ forge_prog_addresses_slot cb_end bm_buf_end` by
             (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses_slot _ _` (mp_tac o Q.SPEC `0`)
              \\ impl_tac >- decide_tac
              \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac send_entry_det \\ impl_tac >- simp [] \\ strip_tac
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `p`, `0`, `^n_tm`] mp_tac send_loop_to_svc_det
        \\ impl_tac >- simp [] \\ strip_tac
        \\ `GENLIST (λi. s.MEM (p + n2w i + 1w)) ^n_tm = TAKE ^n_tm (DROP 1 bytes2)` by
             (irule listTheory.LIST_EQ \\ simp [] \\ rpt strip_tac
              \\ simp [EL_TAKE, EL_DROP, word_add_n2w_right, wordsTheory.word_add_n2w]
              \\ `1 + x = x + 1` by decide_tac
              \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `x + 1` mp_tac) \\ simp [])
        \\ qabbrev_tac `s_post = s_svc with <|PC := 0x4500ECw; REG := s_svc.REG⦇0w ↦ ^n_w64⦈|>`
        \\ `∀inp out. whole_step svc_read_noerr_rel svc_write_noerr_rel
                        (inp, out, s_svc) (inp, out ++ TAKE ^n_tm (DROP 1 bytes2), s_post)` by
             (rpt gen_tac \\ simp [whole_step_def, Abbr `s_post`, svc_write_noerr_rel_def, svc_frame_rel_def,
                                   combinTheory.APPLY_UPDATE_THM]
              \\ conj_tac >- fs [arm8_ok_erase]
              \\ qexists_tac `^n_tm` \\ simp [])
        \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
             (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
              \\ rpt conj_tac
              \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
              \\ gvs [sp_ok_def, bits_of_def])
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `p`, `0`, `^n_tm`, `^n_tm`] mp_tac send_post_ok_det
        \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
        \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `p`] mp_tac send_loop_done_det
        \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
        \\ qexists_tac `s''`
        \\ conj_tac
        >- (rpt gen_tac
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out, s_loop)`
            \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out, s_svc)`
            \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out ++ TAKE ^n_tm (DROP 1 bytes2), s_post)`
            \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
            \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out ++ TAKE ^n_tm (DROP 1 bytes2), s')`
            \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
            \\ irule det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
        \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
             (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
              \\ qspecl_then [`p`, `forge_prog_addresses_slot cb_end bm_buf_end`, `s.MEM`, `bytes2`, `0w`]
                   mp_tac asm_write_bytearray_drop1 \\ simp [])
        \\ REWRITE_TAC [ffi_return_ok_slot_def]
        \\ pop_assum SUBST1_TAC
        \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
        \\ rpt strip_tac \\ rveq \\ simp [])
    in
      (recv_universal, recv_noerr_exists, send_universal, send_noerr_exists)
    end

  val shim16_len = prove (``LENGTH forge_shim16_words = 80``, simp [forge_shim16_words_def])
  val shim64_len = prove (``LENGTH forge_shim64_words = 80``, simp [forge_shim64_words_def])
in
  val (ffirecv16_universal_slot, ffirecv16_noerr_exists_slot,
       ffisend16_universal_slot, ffisend16_noerr_exists_slot) =
    mk_frame_ffi_suite {n = 16, kind = "shim16", shim_ws_tm = ``forge_shim16_words``, shim_len_th = shim16_len}

  val (ffirecv64_universal_slot, ffirecv64_noerr_exists_slot,
       ffisend64_universal_slot, ffisend64_noerr_exists_slot) =
    mk_frame_ffi_suite {n = 64, kind = "shim64", shim_ws_tm = ``forge_shim64_words``, shim_len_th = shim64_len}
end;

(* ---- 9. Parameterized Machine Configuration & Interference Proofs ---- *)

Definition forge_canonical_ffi_post_def:
  forge_canonical_ffi_post (new_bytes:word8 list) (s:arm8_state) : arm8_state =
    s with <| PC := s.REG 30w;
              MEM := asm_write_bytearray (s.REG 2w) new_bytes s.MEM |>
End

Definition mk_real_ffi_if_slot_def:
  mk_real_ffi_if_slot (shim_ws:word32 list) (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64)
                      (P : num -> num -> word8 list -> arm8_state -> arm8_state -> bool)
                      (k:num) (index:num, new_bytes:word8 list, s:arm8_state) : arm8_state =
    if ∃s'. P k index new_bytes s s' ∧
            ffi_return_ok_slot shim_ws cb_begin cb_end bm_buf_end new_bytes s s' then
      @s'. P k index new_bytes s s' ∧
           ffi_return_ok_slot shim_ws cb_begin cb_end bm_buf_end new_bytes s s'
    else
      forge_canonical_ffi_post new_bytes s
End

Definition forge_real_install_if_def:
  forge_real_install_if (k:num) (bytes:word8 list, s:arm8_state) : arm8_state =
    s with <| PC := s.REG 30w;
              REG := (0w =+ s.REG 2w) s.REG;
              MEM := asm_write_bytearray (s.REG 2w) bytes s.MEM |>
End

Theorem forge_mc_slot_mmio_min:
  ∀cb_end bm_buf_end sn rn ffi_if inst_if.
    mmio_pcs_min_index
      (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if).ffi_names = SOME 2
Proof
  rpt gen_tac
  \\ simp [forge_mc_slot_def, targetSemTheory.mmio_pcs_min_index_def]
  \\ DEEP_INTRO_TAC optionTheory.some_intro
  \\ conj_tac
  >- (rpt strip_tac \\ `x = 2` suffices_by simp []
      \\ CCONTR_TAC \\ `x < 2` by decide_tac
      \\ first_x_assum (qspec_then `x` mp_tac) \\ simp []
      \\ `x = 0 ∨ x = 1` by decide_tac \\ rveq \\ simp [])
  \\ simp [] \\ qexists_tac `2` \\ simp []
  \\ gen_tac \\ Cases_on `j` \\ simp [] \\ Cases_on `n` \\ simp []
QED

Theorem forge_mc_slot_lo55:
  ∀cb_begin cb_end bm_buf_end ffi_names_l ffi_if inst_if.
    slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    lo55 (forge_mc_slot cb_end bm_buf_end ffi_names_l ffi_if inst_if)
Proof
  rpt strip_tac
  \\ drule forge_regions_disjoint_slot \\ strip_tac
  \\ simp [lo55_def, forge_mc_slot_def, FORGE_EXIT_VENEER_def, FORGE_INSTALL_VENEER_def,
           FORGE_FFISEND_VENEER_def, FORGE_FFIRECV_VENEER_def, untagged_def]
  \\ rpt strip_tac
  >- (first_x_assum drule \\ simp [untagged_def])
  \\ rveq \\ EVAL_TAC
QED

Theorem forge_mc_slot_start_pc_ok:
  ∀cb_begin cb_end bm_buf_end sn rn ffi_if inst_if.
    slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    start_pc_ok (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if) FORGE_CAKE_MAIN
Proof
  rpt strip_tac
  \\ fs [slot_layout_ok_def]
  \\ simp [targetSemTheory.start_pc_ok_def, forge_mc_slot_def,
           FORGE_CAKE_MAIN_def, FORGE_EXIT_VENEER_def, FORGE_INSTALL_VENEER_def,
           FORGE_FFISEND_VENEER_def, FORGE_FFIRECV_VENEER_def,
           lab_to_targetTheory.ffi_offset_def]
  \\ rpt conj_tac
  >- (simp [forge_prog_addresses_slot_def, forge_code_region_slot_def, forge_bitmaps_region_slot_def,
            forge_heap_stack_region_def, FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def,
            FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ fs [FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
             wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
  >- (simp [forge_prog_addresses_slot_def, forge_code_region_slot_def, forge_bitmaps_region_slot_def,
            forge_heap_stack_region_def, FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def,
            FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ fs [FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
             wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
  \\ qexists_tac `2`
  \\ rpt conj_tac
  >- (mp_tac (Q.SPECL [`cb_end`, `bm_buf_end`, `sn`, `rn`, `ffi_if`, `inst_if`] forge_mc_slot_mmio_min)
      \\ simp [forge_mc_slot_def])
  >- (gen_tac \\ strip_tac
      \\ `index = 0 ∨ index = 1` by decide_tac \\ rveq
      \\ simp [miscTheory.find_index_def, forge_prog_addresses_slot_def, forge_code_region_slot_def,
               forge_bitmaps_region_slot_def, forge_heap_stack_region_def, FORGE_CAKE_MAIN_def,
               FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
               FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ fs [FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
             wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
  \\ rpt strip_tac \\ decide_tac
QED

Theorem mk_real_ffi_if_slot_ok:
  ∀shim_ws cb_begin cb_end bm_buf_end cbspace sn rn B P.
    real_interfer_ok_slot cb_end bm_buf_end cbspace [ExtCall sn; ExtCall rn] B
      (mk_real_ffi_if_slot shim_ws cb_begin cb_end bm_buf_end P) forge_real_install_if
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ simp [real_interfer_ok_slot_def, LET_THM]
  \\ rpt conj_tac
  >- (
    simp [targetSemTheory.ffi_interfer_ok_def, forge_mc_slot_def, arm8_target_def,
          arm8_config_def, mk_real_ffi_if_slot_def]
    \\ rpt gen_tac \\ strip_tac
    \\ `i = 2` by
       (qpat_x_assum `mmio_pcs_min_index _ = SOME i` mp_tac
        \\ mp_tac (Q.SPECL [`cb_end`, `bm_buf_end`, `sn`, `rn`, `ARB`, `ARB`] forge_mc_slot_mmio_min)
        \\ simp [forge_mc_slot_def])
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
      \\ fs [ffi_return_ok_slot_def, erase_fields, restore_def]
      \\ rpt strip_tac \\ simp [] \\ irule asm_write_bytearray_pointwise \\ simp [])
    \\ simp [forge_canonical_ffi_post_def, erase_fields, arm8_ok_erase, restore_def]
    \\ fs [arm8_ok_def]
    \\ rpt strip_tac \\ irule asm_write_bytearray_pointwise \\ simp [])
  >- (
    simp [targetSemTheory.install_interfer_ok_def, forge_mc_slot_def, arm8_target_def,
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
    >- (rpt strip_tac \\ irule asm_write_bytearray_pointwise \\ simp [])
    \\ rpt strip_tac \\ rveq \\ simp [combinTheory.APPLY_UPDATE_THM])
  >- (
    rpt gen_tac \\ strip_tac \\ simp [mk_real_ffi_if_slot_def]
    \\ IF_CASES_TAC
    >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac []
        \\ rpt strip_tac \\ fs [ffi_return_ok_slot_def])
    \\ simp [forge_canonical_ffi_post_def, bits_of_def] \\ fs [bits_of_def])
  \\ rpt strip_tac \\ simp [forge_real_install_if_def, bits_of_def] \\ fs [bits_of_def]
QED

Theorem real_interfer_ok_slot_imp_erase_ok:
  ∀cb_end bm_buf_end cbspace sn rn B ffi_if inst_if.
    real_interfer_ok_slot cb_end bm_buf_end cbspace [ExtCall sn; ExtCall rn] B ffi_if inst_if ⇒
    ffi_interfer_ok FORGE_CAKE_MAIN
      (erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)) ∧
    install_interfer_ok FORGE_CAKE_MAIN cbspace
      (erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)) ∧
    interference_ok
      (erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)).next_interfer
      ((erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)).target.proj
         (forge_prog_addresses_slot cb_end bm_buf_end))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ simp [real_interfer_ok_slot_def, LET_THM] \\ strip_tac
  \\ rpt conj_tac
  >- (
    simp [targetSemTheory.ffi_interfer_ok_def, erase_mc_def, forge_mc_slot_def,
          arm8_target_exact_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ rpt gen_tac \\ strip_tac
    \\ `mmio_pcs_min_index [ExtCall sn; ExtCall rn] = SOME 2` by
         (mp_tac (Q.SPECL [`cb_end`, `bm_buf_end`, `sn`, `rn`, `ARB`, `ARB`] forge_mc_slot_mmio_min)
          \\ simp [forge_mc_slot_def])
    \\ `i = 2` by fs [] \\ rveq \\ simp []
    \\ strip_tac
    \\ qpat_x_assum `ffi_interfer_ok _ _`
         (mp_tac o Q.SPECL [`ms2`, `k`, `index`, `new_bytes`, `t1`, `bytes`, `bytes2`, `2`] o
          REWRITE_RULE [targetSemTheory.ffi_interfer_ok_def])
    \\ simp [forge_mc_slot_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ impl_tac
    >- fs [targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
           asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def,
           arm8_config_def, forge_mc_slot_def]
    \\ strip_tac \\ fs [erase_fields]
    \\ `(ffi_if k (index, new_bytes, restore (B0,B1,B2) ms2)).SP_EL0 = ms2.SP_EL0` by
         (qpat_x_assum `∀k i bs s. bits_of s = _ ⇒ _`
            (qspecl_then [`k`, `index`, `new_bytes`, `restore (B0,B1,B2) ms2`] mp_tac)
          \\ simp [bits_of_restore, restore_def])
    \\ qpat_x_assum `target_state_rel _ _ _` mp_tac
    \\ simp [asmPropsTheory.target_state_rel_def]
    \\ rpt strip_tac \\ qpat_x_assum `∀r. _ ⇒ (ffi_if _ _).REG _ = _` irule \\ simp [])
  >- (
    simp [targetSemTheory.install_interfer_ok_def, erase_mc_def, forge_mc_slot_def,
          arm8_target_exact_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ rpt gen_tac \\ strip_tac
    \\ qpat_x_assum `install_interfer_ok _ _ _`
         (mp_tac o Q.SPECL [`ms2`, `t1`, `k`, `bytes`] o
          REWRITE_RULE [targetSemTheory.install_interfer_ok_def])
    \\ simp [forge_mc_slot_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ impl_tac
    >- gvs [targetSemTheory.read_ffi_bytearray_def, asmPropsTheory.target_state_rel_def,
            arm8_target_exact_def, arm8_target_def, arm8_config_def, forge_mc_slot_def]
    \\ strip_tac \\ fs [erase_fields]
    \\ `(inst_if k (bytes, restore (B0,B1,B2) ms2)).SP_EL0 = ms2.SP_EL0` by
         (qpat_x_assum `∀k bs s. bits_of s = _ ⇒ _`
            (qspecl_then [`k`, `bytes`, `restore (B0,B1,B2) ms2`] mp_tac)
          \\ simp [bits_of_restore, restore_def])
    \\ qpat_x_assum `target_state_rel _ _ _` mp_tac
    \\ simp [asmPropsTheory.target_state_rel_def]
    \\ rpt strip_tac \\ qpat_x_assum `∀r. _ ⇒ (inst_if _ _).REG _ = _` irule \\ simp [])
  \\ simp [asmPropsTheory.interference_ok_def, erase_mc_def, forge_mc_slot_def]
QED
