(*
  Forge Milestone 3 Reusable Runtime: Universal & Liveness ARM64 Syscall Proofs
  for `ffirecv64` (fd 0, 64B request) and `ffisend128` (fd 1, 128B response + HMAC).
*)
Theory forge_airlockShimIo
Ancestors
  words arithmetic list rich_list combin pred_set relation
  arm8 arm8_step arm8_target targetSem misc alignment
  forge_runtimeSpec forge_airlockFfi forge_airlockContract
  forge_arm8Erasure forge_shimProof forge_airlockShimBase
Libs
  preamble blastLib wordsLib forge_m3StepLib

Theorem m3_append_take_drop[local]:
  ∀a n l. a ++ TAKE n l ++ DROP n l = a ++ l
Proof
  rpt gen_tac \\ REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.TAKE_DROP]
QED

Theorem m3_take_drop_add[local]:
  ∀k m l. TAKE m (DROP k l) ++ DROP (k + m) l = DROP k l
Proof
  Induct \\ simp [listTheory.TAKE_DROP, arithmeticTheory.ADD_CLAUSES]
  \\ rpt gen_tac \\ Cases_on `l` \\ simp []
QED

Theorem m3_append_take_drop_add[local]:
  ∀a k m l. a ++ TAKE m (DROP k l) ++ DROP (k + m) l = a ++ DROP k l
Proof
  rpt gen_tac \\ REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, m3_take_drop_add]
QED

Theorem m3_svc_write_noerr_not_err[local]:
  ∀s s' chunk cnt.
    cnt ≤ 128 ∧ s.REG 2w = n2w cnt ∧ svc_write_noerr_rel s s' chunk ⇒
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

(* ---- 1. ffirecv64 (0x400080 -> 0x450040..0x4500BC, fd 0, 64B frames) ---- *)

local
  val v_recv     = prove_m3_step "veneer" 32 0
  val r_cmp_65   = prove_m3_step "shim" 16 0
  val r_blo_ge   = prove_m3_step "shim" 17 0
  val r_blo_lt   = prove_m3_step "shim" 17 1
  val r_mov9     = prove_m3_step "shim" 18 0
  val r_adrp10   = prove_m3_step "shim" 19 0
  val r_add10    = prove_m3_step "shim" 20 0
  val r_mov11_64 = prove_m3_step "shim" 21 0
  val r_cbz_nz   = prove_m3_step "shim" 22 0
  val r_cbz_z    = prove_m3_step "shim" 22 1
  val r_mov0     = prove_m3_step "shim" 23 0
  val r_mov1     = prove_m3_step "shim" 24 0
  val r_mov2     = prove_m3_step "shim" 25 0
  val r_mov8     = prove_m3_step "shim" 26 0
  val r_svc      = prove_m3_svc0_at "shim" 27
  val r_cmn4     = prove_m3_step "shim" 28 0
  val r_beq_ne   = prove_m3_step "shim" 29 0
  val r_beq_eq   = prove_m3_step "shim" 29 1
  val r_cmp0     = prove_m3_step "shim" 30 0
  val r_ble_gt   = prove_m3_step "shim" 31 0
  val r_ble_le   = prove_m3_step "shim" 31 1
  val r_add10_x0 = prove_m3_step "shim" 32 0
  val r_sub11_x0 = prove_m3_step "shim" 33 0
  val r_b_loop   = prove_m3_step "shim" 34 0
  val r_adrp12   = prove_m3_step "shim" 35 0
  val r_add12    = prove_m3_step "shim" 36 0
  val r_mov11_0  = prove_m3_step "shim" 37 0
  val r_ldrb     = prove_m3_step "shim" 38 0
  val r_add11_1  = prove_m3_step "shim" 39 0
  val r_strb_reg = prove_m3_step "shim" 40 0
  val r_cmp_64   = prove_m3_step "shim" 41 0
  val r_blo_done = prove_m3_step "shim" 42 0
  val r_blo_more = prove_m3_step "shim" 42 1
  val r_strb_0   = prove_m3_step "shim" 43 0
  val r_ret_ok   = prove_m3_step "shim" 44 0
  val r_mov12_1  = prove_m3_step "shim" 45 0
  val r_strb_1   = prove_m3_step "shim" 46 0
  val r_ret_err  = prove_m3_step "shim" 47 0

  val recv_short_det = prove(
    ``∀cb_begin cb_end bm_buf_end s bytes2.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFIRECV_VENEER ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        read_bytearray (s.REG 2w) (w2n (s.REG 3w))
          (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
        w2n (s.REG 3w) < 65 ⇒
        ∃s'. det_run 4 s s' ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s'``,
    rpt strip_tac
    \\ `s.PC = 0x400080w` by fs [FORGE_M3_FFIRECV_VENEER_def]
    \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by (irule asm_write_bytearray_id \\ metis_tac [])
    \\ qexists_tac `s with <|PC := s.REG 30w;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551550 + 1)));
                                 C := F;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFFBFw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFFBFw)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det v_recv \\ step_m3_det r_cmp_65 \\ step_m3_det r_blo_lt \\ step_m3_det r_ret_err
        \\ simp [det_run_def, cmp_carry_65, arm8Theory.arm8_state_component_equality])
    \\ simp [m3_ffi_return_ok_slot_def, arm8_ok_erase, sp_ok_def, bits_of_def]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val recv_entry_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFIRECV_VENEER ∧ 65 ≤ w2n (s.REG 3w) ⇒
        ∃s_loop.
          det_run 7 s s_loop ∧ arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_loop.MEM ∧
          bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
          s_loop.PC = 0x450058w ∧ s_loop.MEM = s.MEM ∧
          s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = FORGE_RX_TMP ∧ s_loop.REG 11w = 64w ∧
          s_loop.REG 30w = s.REG 30w ∧
          (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))``,
    rpt strip_tac
    \\ `s.PC = 0x400080w` by fs [FORGE_M3_FFIRECV_VENEER_def]
    \\ qabbrev_tac `p = s.REG 2w`
    \\ qexists_tac `s with <|PC := 0x450058w;
                             REG := s.REG⦇9w ↦ p; 10w ↦ FORGE_RX_TMP; 11w ↦ 64w⦈;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551550 + 1)));
                                 C := T;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFFBFw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFFBFw)|>;
                             branch_hint := NONE|>`
    \\ conj_tac
    >- (step_m3_det v_recv \\ step_m3_det r_cmp_65 \\ step_m3_det r_blo_ge \\ step_m3_det r_mov9
        \\ step_m3_det r_adrp10 \\ step_m3_det r_add10 \\ step_m3_det r_mov11_64
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, Abbr `p`, FORGE_RX_TMP_def, cmp_carry_65,
              arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
              combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val recv_copy_loop_det = prove(
    ``∀c k cb_begin cb_end bm_buf_end s (f:word8 list) (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        1 ≤ c ∧ c + k = 64 ∧ LENGTH f = 64 ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450098w ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ s.REG 12w = FORGE_RX_TMP ∧ s.REG 11w = n2w k ∧
        (∀i. i < 65 ⇒ p + n2w i ∈ forge_m3_prog_addresses cb_end bm_buf_end) ∧
        (∀i. i < 64 ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i f) ⇒
        ∃d s'.
          1 ≤ d ∧ det_run d s s' ∧
          arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
          s'.PC = s.REG 30w ∧
          s'.MEM = (p =+ 0w) (asm_write_bytearray (p + n2w (k + 1)) (DROP k f) s.MEM) ∧
          (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)``,
    Induct_on `c` >- (rpt strip_tac \\ `F` by decide_tac)
    \\ rpt strip_tac \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ Cases_on `c = 0`
    >- (
      `k = 63` by decide_tac \\ pop_assum SUBST_ALL_TAC
      \\ qabbrev_tac `blast = EL 63 f`
      \\ qpat_assum `∀i. i < 64 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `63`)
      \\ qpat_assum `∀i. i < 65 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `64`)
      \\ qpat_assum `∀i. i < 65 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `0`)
      \\ `p + 64w ∉ forge_m3_shim_code_region ∧ p ∉ forge_m3_shim_code_region` by simp []
      \\ qabbrev_tac `m1 = s.MEM⦇p + 64w ↦ blast⦈`
      \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by simp [Abbr `m1`, m3_shim_loaded_slot_update]
      \\ qabbrev_tac `m2 = m1⦇p ↦ 0w⦈`
      \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m2` by simp [Abbr `m2`, m3_shim_loaded_slot_update]
      \\ `DROP 63 f = [blast]` by (simp [Abbr `blast`] \\ `63 < LENGTH f` by decide_tac \\ simp [DROP_EL_CONS, listTheory.DROP_LENGTH_NIL])
      \\ qexists_tac `7`
      \\ qexists_tac `s with <|MEM := m2; PC := s.REG 30w;
                               REG := s.REG⦇10w ↦ w2w blast; 11w ↦ 64w⦈;
                               PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                               branch_hint := SOME BranchType_RET|>`
      \\ conj_tac >- decide_tac
      \\ conj_tac
      >- (step_m3_det r_ldrb \\ step_m3_det r_add11_1 \\ step_m3_det r_strb_reg
          \\ step_m3_det r_cmp_64 \\ step_m3_det r_blo_done \\ step_m3_det r_strb_0 \\ step_m3_det r_ret_ok
          \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
               [det_run_def, Abbr `m2`, Abbr `m1`, Abbr `blast`, FORGE_RX_TMP_def, cmp_carry_64,
                arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
          \\ rw [] \\ fs [] \\ TRY (EVAL_TAC \\ NO_TAC))
      \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM,
               Abbr `m2`, Abbr `m1`, miscTheory.asm_write_bytearray_def]
      \\ fs [arm8_ok_erase, sp_ok_def])
    \\ `k < 63 ∧ k + 1 < 64` by decide_tac
    \\ qabbrev_tac `bk = EL k f`
    \\ qpat_assum `∀i. i < 64 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k`)
    \\ qpat_assum `∀i. i < 65 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k + 1`)
    \\ `p + n2w (k + 1) ∈ forge_m3_prog_addresses cb_end bm_buf_end` by simp []
    \\ `p + n2w (k + 1) ∉ forge_m3_shim_code_region` by simp []
    \\ `∀i. i < 64 ⇒ p + n2w (k + 1) ≠ FORGE_RX_TMP + n2w i` by
       (rpt strip_tac
        \\ `FORGE_RX_TMP + n2w i ∈ forge_m3_rx_tmp_region` by
             simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
                   word_add_n2w, w2n_n2w, dimword_64]
        \\ `p + n2w (k + 1) ∈ forge_m3_rx_tmp_region` by fs []
        \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `p + n2w (k + 1)`)
        \\ simp [])
    \\ qabbrev_tac `m1 = s.MEM⦇p + n2w (k + 1) ↦ bk⦈`
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by simp [Abbr `m1`, m3_shim_loaded_slot_update]
    \\ qabbrev_tac `s_next = s with <|MEM := m1; PC := 0x450098w;
                                      REG := s.REG⦇10w ↦ w2w bk; 11w ↦ n2w (k + 1)⦈;
                                      PSTATE := s.PSTATE with
                                        <|V := (word_msb (n2w (k + 1):word64) ∧
                                                (word_msb (n2w (k + 1):word64) ⇎
                                                 BIT 63 (w2n (n2w (k + 1):word64) + 18446744073709551551 + 1)));
                                          C := F;
                                          Z := ((n2w (k + 1):word64) + 0xFFFFFFFFFFFFFFC0w = 0w);
                                          N := word_msb ((n2w (k + 1):word64) + 0xFFFFFFFFFFFFFFC0w)|>;
                                      branch_hint := SOME BranchType_JMP|>`
    \\ `det_run 5 s s_next` by
       (step_m3_det r_ldrb \\ step_m3_det r_add11_1 \\ step_m3_det r_strb_reg
        \\ step_m3_det r_cmp_64 \\ step_m3_det r_blo_more
        \\ simp [det_run_def, Abbr `s_next`, Abbr `m1`, Abbr `bk`, cmp_carry_64,
                 m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                 arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ qpat_x_assum `∀k cb_begin cb_end bm_buf_end s f p. _`
         (qspecl_then [`k + 1`, `cb_begin`, `cb_end`, `bm_buf_end`, `s_next`, `f`, `p`] mp_tac)
    \\ impl_tac
    >- (simp [Abbr `s_next`, combinTheory.APPLY_UPDATE_THM, arm8_ok_erase, sp_ok_def]
        \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
        \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY decide_tac
        \\ rpt strip_tac \\ simp [Abbr `m1`, combinTheory.APPLY_UPDATE_THM]
        \\ `FORGE_RX_TMP + n2w i ≠ p + n2w (k + 1)` by
             (strip_tac \\ qpat_assum `∀i. i < 64 ⇒ p + n2w (k + 1) ≠ _` (mp_tac o Q.SPEC `i`) \\ simp [])
        \\ simp [])
    \\ strip_tac
    \\ `s_next.MEM = m1 ∧ s_next.SP_EL0 = s.SP_EL0 ∧ bits_of s_next = bits_of s ∧
        s_next.REG 30w = s.REG 30w ∧ (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s_next.REG r = s.REG r)` by
         simp [Abbr `s_next`, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ qexists_tac `5 + d` \\ qexists_tac `s'`
    \\ conj_tac >- decide_tac
    \\ conj_tac >- (irule det_run_add \\ qexists_tac `s_next` \\ simp [])
    \\ simp []
    \\ `DROP k f = bk :: DROP (k + 1) f` by simp [Abbr `bk`, DROP_EL_CONS, ADD1]
    \\ simp [miscTheory.asm_write_bytearray_def]
    \\ `p + n2w (k + 1) + 1w = p + n2w (k + 2)` by simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w]
    \\ simp [FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] \\ gen_tac
    \\ Cases_on `x = p` \\ simp []
    \\ Cases_on `x = p + n2w (k + 1)` \\ simp [Abbr `m1`]
    >- (`asm_write_bytearray (p + n2w (k + 2)) (DROP (k + 1) f) (s.MEM⦇p + n2w (k + 1) ↦ bk⦈) (p + n2w (k + 1)) =
         (s.MEM⦇p + n2w (k + 1) ↦ bk⦈) (p + n2w (k + 1))` by
          (irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
           \\ `i < 64` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
           \\ qpat_x_assum `p + n2w (k + 1) = _` mp_tac
           \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                    wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
        \\ simp [combinTheory.APPLY_UPDATE_THM])
    \\ irule m3_asm_write_bytearray_pointwise \\ simp [combinTheory.APPLY_UPDATE_THM])

  val recv_loop_done_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450058w ∧ s.REG 11w = 0w ⇒
        ∃s_cp0.
          det_run 4 s s_cp0 ∧ arm8_ok (erase s_cp0) ∧ sp_ok s_cp0 ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_cp0.MEM ∧
          bits_of s_cp0 = bits_of s ∧ s_cp0.SP_EL0 = s.SP_EL0 ∧
          s_cp0.PC = 0x450098w ∧ s_cp0.MEM = s.MEM ∧
          s_cp0.REG 12w = FORGE_RX_TMP ∧ s_cp0.REG 11w = 0w ∧
          (∀r. r ≠ 11w ∧ r ≠ 12w ⇒ s_cp0.REG r = s.REG r)``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x450098w; REG := s.REG⦇12w ↦ FORGE_RX_TMP; 11w ↦ 0w⦈; branch_hint := NONE|>`
    \\ conj_tac
    >- (step_m3_det r_cbz_z \\ step_m3_det r_adrp12 \\ step_m3_det r_add12 \\ step_m3_det r_mov11_0
        \\ simp [det_run_def, FORGE_RX_TMP_def, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val recv_loop_to_svc_det = prove(
    ``∀cb_begin cb_end bm_buf_end s k c.
        1 ≤ c ∧ c + k = 64 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450058w ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ⇒
        ∃s_svc.
          det_run 5 s s_svc ∧ arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_svc.MEM ∧
          bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
          s_svc.PC = 0x45006Cw ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
          s_svc.REG 0w = 0w ∧ s_svc.REG 1w = FORGE_RX_TMP + n2w k ∧
          s_svc.REG 2w = n2w c ∧ s_svc.REG 8w = 63w ∧
          (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
    rpt strip_tac
    \\ qabbrev_tac `s_svc = s with <|PC := 0x45006Cw;
                                     REG := s.REG⦇0w ↦ 0w; 1w ↦ FORGE_RX_TMP + n2w k; 2w ↦ n2w c; 8w ↦ 63w⦈;
                                     branch_hint := NONE|>`
    \\ qexists_tac `s_svc`
    \\ conj_tac
    >- (step_m3_det r_cbz_nz \\ step_m3_det r_mov0 \\ step_m3_det r_mov1 \\ step_m3_det r_mov2 \\ step_m3_det r_mov8
        \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `is_svc0_at s_svc` by (irule r_svc \\ simp [Abbr `s_svc`] \\ metis_tac [])
    \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val recv_post_eintr_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450070w ∧ s.REG 0w = -4w ⇒
        ∃s'. det_run 2 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x450058w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x450058w; PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det r_cmn4 \\ step_m3_det r_beq_eq
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val recv_post_err_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450070w ∧ s.REG 9w = p ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        (s.REG 0w = 0w ∨ (word_msb (s.REG 0w) ∧ s.REG 0w ≠ -4w)) ⇒
        ∃s'. det_run 7 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
             (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)``,
    rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
    \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ `p ∉ forge_m3_shim_code_region` by simp []
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 1w⦈)` by simp [m3_shim_loaded_slot_update]
    \\ `s.REG 0w ≠ -4w ∧ (¬word_msb (s.REG 0w) ⇒ s.REG 0w = 0w)` by (Cases_on `s.REG 0w = 0w` \\ fs [] \\ EVAL_TAC)
    \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 1w⦈; PC := s.REG 30w; REG := s.REG⦇12w ↦ 1w⦈;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 0w) ∧
                                       (word_msb (s.REG 0w) ⇎
                                        BIT 63 (w2n (s.REG 0w) + 18446744073709551615 + 1)));
                                 C := ((if w2n (s.REG 0w) + 18446744073709551615 + 1 < 18446744073709551616
                                        then w2n (s.REG 0w) + 18446744073709551615 + 1
                                        else (w2n (s.REG 0w) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                       w2n (s.REG 0w) + 18446744073709551615 + 1);
                                 Z := (s.REG 0w + 0w = 0w); N := word_msb (s.REG 0w + 0w)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det r_cmn4 \\ step_m3_det r_beq_ne \\ step_m3_det r_cmp0 \\ step_m3_det r_ble_le
        \\ step_m3_det r_mov12_1 \\ step_m3_det r_strb_1 \\ step_m3_det r_ret_err
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
              arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val recv_post_ok_det = prove(
    ``∀cb_begin cb_end bm_buf_end s k c m.
        1 ≤ m ∧ m ≤ c ∧ c + k = 64 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450070w ∧ s.REG 0w = n2w m ∧
        s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ⇒
        ∃s'. det_run 7 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
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
       (ONCE_REWRITE_TAC [cj 1 m3_word64_arith_step_helpers]
        \\ mp_tac (Q.SPECL [`c`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub)) \\ simp [])
    \\ `(n2w m : word64) + (FORGE_RX_TMP + n2w k) = FORGE_RX_TMP + n2w (k + m)` by
       (ONCE_REWRITE_TAC [cj 2 m3_word64_arith_step_helpers] \\ simp [wordsTheory.word_add_n2w])
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
    >- (step_m3_det r_cmn4 \\ step_m3_det r_beq_ne \\ step_m3_det r_cmp0 \\ step_m3_det r_ble_gt
        \\ step_m3_det r_add10_x0 \\ step_m3_det r_sub11_x0 \\ step_m3_det r_b_loop
        \\ simp [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
                 arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ `aligned 2 (0x450058w:word64)` by EVAL_TAC
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val recv_read_loop_universal = prove(
    ``∀n allow_err cb_begin cb_end bm_buf_end k c acc s os os_f ms_f ec (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        c + k = 64 ∧ LENGTH acc = k ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450058w ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        (∀i. i < k ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i acc) ∧
        NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f ⇒
        (∃n' s' frame inp_after.
           n' < n ∧ LENGTH frame = 64 ∧ acc ++ os.inp = frame ++ inp_after ∧
           NRC (m3_whole_step allow_err) n' (os with inp := inp_after, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = 0x450098w ∧ s'.REG 9w = p ∧ s'.REG 12w = FORGE_RX_TMP ∧ s'.REG 11w = 0w ∧
           s'.REG 30w = s.REG 30w ∧
           (∀i. i < 64 ⇒ s'.MEM (FORGE_RX_TMP + n2w i) = EL i frame) ∧
           (∀a. a ∉ forge_m3_rx_tmp_region ⇒ s'.MEM a = s.MEM a) ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
        (∃n' s' inp_after.
           n' < n ∧ (allow_err ∨ LENGTH (acc ++ os.inp) < 64) ∧
           NRC (m3_whole_step allow_err) n' (os with inp := inp_after, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧
           (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒ s'.MEM a = (p =+ 1w) s.MEM a) ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
    completeInduct_on `n` \\ rpt strip_tac
    \\ Cases_on `c = 0`
    >- (
      `k = 64` by decide_tac \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_loop_done_det
      \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj1_tac
      \\ qexists_tac `n - 4` \\ qexists_tac `s_cp0` \\ qexists_tac `acc` \\ qexists_tac `os.inp`
      \\ `os with inp := os.inp = os` by simp [m3_os_component_equality]
      \\ simp [] \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `1 ≤ c` by decide_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `k`, `c`] mp_tac recv_loop_to_svc_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ Cases_on `n - 5`
    >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, cj 1 m3_whole_step_svc_det]
    \\ rpt strip_tac \\ qpat_x_assum `_ = os with inp := _` SUBST_ALL_TAC
    \\ rename1 `NRC _ _ (os with inp := rest, z2) _`
    \\ qpat_x_assum `svc_read_fd_rel _ _ _ _ _ _`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_read_fd_rel_def, svc_frame_rel_def])
    \\ `s_svc.REG 9w = p ∧ s_svc.REG 10w = FORGE_RX_TMP + n2w k ∧
        s_svc.REG 11w = n2w c ∧ s_svc.REG 30w = s.REG 30w` by simp []
    \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
        z2.PC = 0x450070w ∧ z2.REG 9w = p ∧ z2.REG 10w = FORGE_RX_TMP + n2w k ∧
        z2.REG 11w = n2w c ∧ z2.REG 30w = s.REG 30w ∧
        (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
         (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY (fs [bits_of_def] \\ NO_TAC)
          \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ qpat_x_assum `_ ∨ _ ∨ _ ∨ _` (REPEAT_TCL DISJ_CASES_THEN strip_assume_tac)
    >- (
      `os with inp := rest = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac recv_post_eintr_det
      \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac)
      \\ impl_tac >- decide_tac
      \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                  `k`, `c`, `acc`, `s'`, `os`, `os_f`, `ms_f`, `ec`, `p`] mp_tac)
      \\ impl_tac >- simp [] \\ strip_tac
      >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
          \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `inp_after`
      \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      qpat_x_assum `rest = []` SUBST_ALL_TAC
      \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end z2.MEM ∧ k < 64` by simp []
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac recv_post_err_det
      \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj2_tac \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `[]`
      \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      `os with inp := rest = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac recv_post_err_det
      \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj2_tac \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `os.inp`
      \\ qpat_x_assum `NRC _ _ _ _` mp_tac
      \\ simp [combinTheory.APPLY_UPDATE_THM] \\ disch_then (K ALL_TAC)
      \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ rename1 `z2.REG 0w = n2w m`
    \\ qpat_x_assum `rest = DROP _ _` SUBST_ALL_TAC
    \\ `m ≤ c` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
    \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ z2.MEM a = s.MEM a` by
         (rpt strip_tac \\ simp [] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
          \\ `i < m` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
          \\ `FORGE_RX_TMP + n2w k + n2w i ∈ forge_m3_rx_tmp_region` by
               simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, m3_word_add_n2w_right,
                     wordsTheory.word_add_n2w, WORD_LS, WORD_LO, w2n_n2w, dimword_64]
          \\ rveq \\ fs [])
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end z2.MEM` by
         (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
          \\ conj_tac
          >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
              \\ qpat_assum `m3_slot_layout_ok _ _ _` (strip_assume_tac o MATCH_MP m3_regions_disjoint_slot)
              \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
          \\ first_assum ACCEPT_TAC)
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `k`, `c`, `m`] mp_tac recv_post_ok_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 7` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                `k + m`, `c - m`, `acc ++ TAKE m os.inp`,
                                `s'`, `os with inp := DROP m os.inp`, `os_f`, `ms_f`, `ec`, `p`] mp_tac)
    \\ impl_tac
    >- (
      simp [] \\ rpt strip_tac
      \\ Cases_on `i < k`
      >- (simp [EL_APPEND1]
          \\ `asm_write_bytearray (FORGE_RX_TMP + n2w k) (TAKE m os.inp) s.MEM (FORGE_RX_TMP + n2w i) =
              s.MEM (FORGE_RX_TMP + n2w i)` by
             (irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
              \\ `i' < m` by (qpat_x_assum `i' < LENGTH _` mp_tac \\ simp [])
              \\ qpat_x_assum `FORGE_RX_TMP + n2w i = _` mp_tac
              \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                       wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
          \\ simp [])
      \\ simp [EL_APPEND2] \\ `i - k < m` by decide_tac
      \\ `FORGE_RX_TMP + n2w i = (FORGE_RX_TMP + n2w k) + n2w (i - k)` by
           simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w]
      \\ pop_assum SUBST1_TAC
      \\ `asm_write_bytearray (FORGE_RX_TMP + n2w k) (TAKE m os.inp) s.MEM
            ((FORGE_RX_TMP + n2w k) + n2w (i - k)) = EL (i - k) (TAKE m os.inp)` by
           (irule asm_write_bytearray_read_el \\ simp [dimword_64])
      \\ simp [])
    \\ strip_tac
    >- (
      disj1_tac
      \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
      \\ fs [m3_append_take_drop] \\ rfs []
      \\ rpt conj_tac \\ TRY decide_tac
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `inp_after`
    \\ fs [m3_append_take_drop] \\ rfs []
    \\ rpt conj_tac \\ TRY decide_tac
    \\ rpt strip_tac
    \\ TRY (pop_assum SUBST1_TAC \\ simp [] \\ NO_TAC)
    \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `m3_slot_layout_ok _ _ _` (strip_assume_tac o MATCH_MP m3_regions_disjoint_slot) \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
    \\ simp [combinTheory.APPLY_UPDATE_THM])
in

Theorem m3_ffirecv64_universal_slot:
  ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFIRECV_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 65 ⇒
       ∃n' s'. n' < n ∧
         NRC (m3_whole_step allow_err) n' (os, s') (os_f, ms_f) ∧
         m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (65 ≤ w2n (s.REG 3w) ⇒
       (∃n' s' frame inp_after.
          n' < n ∧ LENGTH frame = 64 ∧ os.inp = frame ++ inp_after ∧
          NRC (m3_whole_step allow_err) n' (os with inp := inp_after, s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w :: frame ++ DROP 65 bytes2) s s') ∨
       (∃n' s' inp_after.
          n' < n ∧ (allow_err ∨ LENGTH os.inp < 64) ∧
          NRC (m3_whole_step allow_err) n' (os with inp := inp_after, s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s'))
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac recv_short_det
      \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
  \\ drule m3_regions_disjoint_slot \\ strip_tac
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `∀i. i < 65 ⇒ p + n2w i ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (qspec_then `i` mp_tac) \\ simp [])
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ m3_peel_nrc_tac
  \\ qspecl_then [`n - 7`, `allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                  `0`, `64`, `[]`, `s_loop`, `os`, `os_f`, `ms_f`, `ec`, `p`] mp_tac recv_read_loop_universal
  \\ impl_tac >- simp [] \\ strip_tac
  >- (
    qspecl_then [`64`, `0`, `cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `frame`, `p`] mp_tac recv_copy_loop_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ disj1_tac
    \\ qexists_tac `n' - d` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
    \\ `asm_write_bytearray (s.REG 2w) (0w :: frame ++ DROP 65 bytes2) s.MEM =
        (p =+ 0w) (asm_write_bytearray (p + 1w) frame s.MEM)` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
          \\ qspecl_then [`64`, `p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `frame`]
               mp_tac asm_write_bytearray_drop_np1 \\ simp [])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
    \\ fs [] \\ rpt conj_tac \\ TRY decide_tac
    >- (rpt strip_tac \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
        \\ irule m3_asm_write_bytearray_pointwise
        \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
        \\ simp [])
    \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ disj2_tac \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `inp_after`
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
        \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
             asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
  \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

Theorem m3_ffirecv64_noerr_exists_slot:
  ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFIRECV_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 65 ⇒
       ∃s'. (∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (∀f. 65 ≤ w2n (s.REG 3w) ∧ LENGTH f = 64 ⇒
       ∃s'. (∀os rest. os.inp = f ++ rest ⇒ RTC (m3_whole_step F) (os, s) (os with inp := rest, s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w :: f ++ DROP 65 bytes2) s s') ∧
    (∀tail_bs. 65 ≤ w2n (s.REG 3w) ∧ LENGTH tail_bs < 64 ⇒
       ∃s'. (∀os. os.inp = tail_bs ⇒ RTC (m3_whole_step F) (os, s) (os with inp := [], s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s')
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac recv_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `s'` \\ simp [] \\ metis_tac [m3_det_run_imp_rtc])
  >- (
    drule m3_regions_disjoint_slot \\ strip_tac
    \\ imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `p = s.REG 2w` \\ `s.REG 2w = p` by simp [Abbr `p`]
    \\ `∀i. i < 65 ⇒ p + n2w i ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
         (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (qspec_then `i` mp_tac) \\ simp [])
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_entry_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `64`] mp_tac recv_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP f s.MEM`
    \\ qabbrev_tac `s_post = s_svc with <|PC := 0x450070w; REG := s_svc.REG⦇0w ↦ 64w⦈; MEM := m1|>`
    \\ `∀os rest. os.inp = f ++ rest ⇒ m3_whole_step F (os, s_svc) (os with inp := rest, s_post)` by
         (rpt strip_tac \\ `s_svc.exception = NoException` by fs [arm8_ok_erase]
          \\ simp [m3_whole_step_def, Abbr `s_post`, svc_read_fd_rel_def, svc_frame_rel_def,
                   combinTheory.APPLY_UPDATE_THM]
          \\ qexists_tac `rest` \\ simp []
          \\ qexists_tac `64` \\ simp [Abbr `m1`, TAKE_APPEND1, DROP_APPEND2, listTheory.TAKE_LENGTH_ID_rwt])
    \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ m1 a = s.MEM a` by
         (rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
          \\ `FORGE_RX_TMP + n2w i ∈ forge_m3_rx_tmp_region` by
               simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO, word_add_n2w, w2n_n2w, dimword_64]
          \\ rveq \\ fs [])
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by
         (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
          \\ conj_tac
          >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
              \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
          \\ first_assum ACCEPT_TAC)
    \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
         (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC) \\ gvs [sp_ok_def, bits_of_def])
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `0`, `64`, `64`] mp_tac recv_post_ok_det
    \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`] mp_tac recv_loop_done_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qspecl_then [`64`, `0`, `cb_begin`, `cb_end`, `bm_buf_end`, `s_cp0`, `f`, `p`] mp_tac recv_copy_loop_det
    \\ impl_tac >- (simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM, Abbr `m1`]
                    \\ rpt strip_tac \\ irule asm_write_bytearray_read_el \\ simp [dimword_64])
    \\ strip_tac \\ qexists_tac `s''`
    \\ conj_tac
    >- (rpt strip_tac
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := rest, s_post)`
        \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := rest, s')`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := rest, s_cp0)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `4` \\ simp [])
        \\ irule m3_det_run_imp_rtc \\ qexists_tac `d` \\ simp [])
    \\ `asm_write_bytearray (s.REG 2w) (0w :: f ++ DROP 65 bytes2) s.MEM =
        (p =+ 0w) (asm_write_bytearray (p + 1w) f s.MEM)` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
          \\ qspecl_then [`64`, `p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `f`]
               mp_tac asm_write_bytearray_drop_np1 \\ simp [])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
    \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
    \\ rpt conj_tac
    >- (rpt strip_tac \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
        \\ irule m3_asm_write_bytearray_pointwise
        \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
        \\ simp [])
    \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ drule m3_regions_disjoint_slot \\ strip_tac
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w` \\ `s.REG 2w = p` by simp [Abbr `p`]
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
        \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
             asm_write_bytearray_drop1 \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac recv_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ Cases_on `tail_bs = []`
  >- (
    pop_assum SUBST_ALL_TAC
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `64`] mp_tac recv_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qabbrev_tac `s_post = s_svc with <|PC := 0x450070w; REG := s_svc.REG⦇0w ↦ 0w⦈|>`
    \\ `∀os. os.inp = [] ⇒ m3_whole_step F (os, s_svc) (os with inp := [], s_post)` by
         (rpt strip_tac \\ `s_svc.exception = NoException` by fs [arm8_ok_erase]
          \\ simp [m3_whole_step_def, Abbr `s_post`, svc_read_fd_rel_def, svc_frame_rel_def,
                   combinTheory.APPLY_UPDATE_THM]
          \\ qexists_tac `[]` \\ simp [])
    \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
         (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC) \\ gvs [sp_ok_def, bits_of_def])
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `p`] mp_tac recv_post_err_det
    \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
    \\ qexists_tac `s'`
    \\ conj_tac
    >- (rpt strip_tac
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := [], s_post)`
        \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
        \\ irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def]
    \\ qpat_x_assum `asm_write_bytearray (s.REG 2w) _ _ = _` SUBST1_TAC
    \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ `1 ≤ LENGTH tail_bs` by (Cases_on `tail_bs` \\ fs [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `64`] mp_tac recv_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
  \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP tail_bs s.MEM`
  \\ qabbrev_tac `s_post1 = s_svc with <|PC := 0x450070w; REG := s_svc.REG⦇0w ↦ n2w (LENGTH tail_bs)⦈; MEM := m1|>`
  \\ `∀os. os.inp = tail_bs ⇒ m3_whole_step F (os, s_svc) (os with inp := [], s_post1)` by
       (rpt strip_tac \\ `s_svc.exception = NoException` by fs [arm8_ok_erase]
        \\ simp [m3_whole_step_def, Abbr `s_post1`, svc_read_fd_rel_def, svc_frame_rel_def,
                 combinTheory.APPLY_UPDATE_THM]
        \\ qexists_tac `[]` \\ simp []
        \\ TRY disj2_tac \\ TRY disj2_tac
        \\ qexists_tac `LENGTH tail_bs` \\ simp [Abbr `m1`, listTheory.TAKE_LENGTH_ID_rwt, listTheory.DROP_LENGTH_NIL])
  \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ m1 a = s.MEM a` by
       (rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
        \\ `FORGE_RX_TMP + n2w i ∈ forge_m3_rx_tmp_region` by
             simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO, word_add_n2w, w2n_n2w, dimword_64]
        \\ rveq \\ fs [])
  \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by
       (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
        \\ conj_tac
        >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
            \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
        \\ first_assum ACCEPT_TAC)
  \\ `arm8_ok (erase s_post1) ∧ sp_ok s_post1 ∧ bits_of s_post1 = bits_of s ∧ s_post1.SP_EL0 = s.SP_EL0` by
       (simp [Abbr `s_post1`, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ rpt conj_tac \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC) \\ gvs [sp_ok_def, bits_of_def])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post1`, `0`, `64`, `LENGTH tail_bs`] mp_tac recv_post_ok_det
  \\ impl_tac >- simp [Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `LENGTH tail_bs`, `64 - LENGTH tail_bs`] mp_tac recv_loop_to_svc_det
  \\ impl_tac >- simp [] \\ strip_tac
  \\ qabbrev_tac `s_post2 = s_svc' with <|PC := 0x450070w; REG := s_svc'.REG⦇0w ↦ 0w⦈|>`
  \\ `∀os. m3_whole_step F (os with inp := [], s_svc') (os with inp := [], s_post2)` by
       (gen_tac \\ `s_svc'.exception = NoException` by fs [arm8_ok_erase]
        \\ simp [m3_whole_step_def, Abbr `s_post2`, svc_read_fd_rel_def, svc_frame_rel_def,
                 combinTheory.APPLY_UPDATE_THM]
        \\ qexists_tac `[]` \\ simp [])
  \\ `arm8_ok (erase s_post2) ∧ sp_ok s_post2 ∧ bits_of s_post2 = bits_of s ∧ s_post2.SP_EL0 = s.SP_EL0` by
       (simp [Abbr `s_post2`, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ rpt conj_tac \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC) \\ gvs [sp_ok_def, bits_of_def])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post2`, `p`] mp_tac recv_post_err_det
  \\ impl_tac >- simp [Abbr `s_post2`, Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qexists_tac `s''`
  \\ conj_tac
  >- (rpt strip_tac
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := [], s_post1)`
      \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := [], s')`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := [], s_svc')`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with inp := [], s_post2)`
      \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
      \\ irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def]
  \\ qpat_x_assum `asm_write_bytearray (s.REG 2w) _ _ = _` SUBST1_TAC
  \\ simp [Abbr `s_post2`, Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM]
  \\ rpt conj_tac
  >- (rpt strip_tac \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
      \\ simp [combinTheory.APPLY_UPDATE_THM])
  \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

end;

(* ---- 2. ffisend128 (0x400090 -> 0x4500C0..0x450118, fd 1, 128B frames) ---- *)

local
  val v_send      = prove_m3_step "veneer" 36 0
  val s_cmp_129   = prove_m3_step "shim" 48 0
  val s_blo_ge    = prove_m3_step "shim" 49 0
  val s_blo_lt    = prove_m3_step "shim" 49 1
  val s_mov9      = prove_m3_step "shim" 50 0
  val s_add10     = prove_m3_step "shim" 51 0
  val s_mov11_128 = prove_m3_step "shim" 52 0
  val s_cbz_nz    = prove_m3_step "shim" 53 0
  val s_cbz_z     = prove_m3_step "shim" 53 1
  val s_mov0      = prove_m3_step "shim" 54 0
  val s_mov1      = prove_m3_step "shim" 55 0
  val s_mov2      = prove_m3_step "shim" 56 0
  val s_mov8      = prove_m3_step "shim" 57 0
  val s_svc       = prove_m3_svc0_at "shim" 58
  val s_cmn4      = prove_m3_step "shim" 59 0
  val s_beq_ne    = prove_m3_step "shim" 60 0
  val s_beq_eq    = prove_m3_step "shim" 60 1
  val s_cmp0      = prove_m3_step "shim" 61 0
  val s_ble_gt    = prove_m3_step "shim" 62 0
  val s_ble_le    = prove_m3_step "shim" 62 1
  val s_add10_x0  = prove_m3_step "shim" 63 0
  val s_sub11_x0  = prove_m3_step "shim" 64 0
  val s_b_loop    = prove_m3_step "shim" 65 0
  val s_strb_0    = prove_m3_step "shim" 66 0
  val s_ret_ok    = prove_m3_step "shim" 67 0
  val s_mov12_1   = prove_m3_step "shim" 68 0
  val s_strb_1    = prove_m3_step "shim" 69 0
  val s_ret_err   = prove_m3_step "shim" 70 0

  val send_short_det = prove(
    ``∀cb_begin cb_end bm_buf_end s bytes2.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFISEND_VENEER ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        read_bytearray (s.REG 2w) (w2n (s.REG 3w))
          (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
        w2n (s.REG 3w) < 129 ⇒
        ∃s'. det_run 4 s s' ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s'``,
    rpt strip_tac
    \\ `s.PC = 0x400090w` by fs [FORGE_M3_FFISEND_VENEER_def]
    \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by (irule asm_write_bytearray_id \\ metis_tac [])
    \\ qexists_tac `s with <|PC := s.REG 30w;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551486 + 1)));
                                 C := F;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFF7Fw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFF7Fw)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det v_send \\ step_m3_det s_cmp_129 \\ step_m3_det s_blo_lt \\ step_m3_det s_ret_err
        \\ simp [det_run_def, cmp_carry_129, arm8Theory.arm8_state_component_equality])
    \\ simp [m3_ffi_return_ok_slot_def, arm8_ok_erase, sp_ok_def, bits_of_def]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val send_entry_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFISEND_VENEER ∧ 129 ≤ w2n (s.REG 3w) ⇒
        ∃s_loop.
          det_run 6 s s_loop ∧ arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_loop.MEM ∧
          bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
          s_loop.PC = 0x4500D4w ∧ s_loop.MEM = s.MEM ∧
          s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = s.REG 2w + 1w ∧ s_loop.REG 11w = 128w ∧
          s_loop.REG 30w = s.REG 30w ∧
          (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))``,
    rpt strip_tac
    \\ `s.PC = 0x400090w` by fs [FORGE_M3_FFISEND_VENEER_def]
    \\ qabbrev_tac `p = s.REG 2w`
    \\ qexists_tac `s with <|PC := 0x4500D4w;
                             REG := s.REG⦇9w ↦ p; 10w ↦ p + 1w; 11w ↦ 128w⦈;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551486 + 1)));
                                 C := T;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFF7Fw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFF7Fw)|>;
                             branch_hint := NONE|>`
    \\ conj_tac
    >- (step_m3_det v_send \\ step_m3_det s_cmp_129 \\ step_m3_det s_blo_ge \\ step_m3_det s_mov9
        \\ step_m3_det s_add10 \\ step_m3_det s_mov11_128
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, Abbr `p`, cmp_carry_129,
              arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
              combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val send_loop_done_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4500D4w ∧ s.REG 9w = p ∧ s.REG 11w = 0w ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒
        ∃s'. det_run 3 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ `p ∉ forge_m3_shim_code_region` by simp []
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 0w⦈)` by simp [m3_shim_loaded_slot_update]
    \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 0w⦈; PC := s.REG 30w; branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det s_cbz_z \\ step_m3_det s_strb_0 \\ step_m3_det s_ret_ok
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def])

  val send_loop_to_svc_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64) k c.
        1 ≤ c ∧ c + k = 128 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4500D4w ∧ s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w c ⇒
        ∃s_svc.
          det_run 5 s s_svc ∧ arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_svc.MEM ∧
          bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
          s_svc.PC = 0x4500E8w ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
          s_svc.REG 0w = 1w ∧ s_svc.REG 1w = p + n2w (k + 1) ∧
          s_svc.REG 2w = n2w c ∧ s_svc.REG 8w = 64w ∧
          (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
    rpt strip_tac
    \\ qabbrev_tac `s_svc = s with <|PC := 0x4500E8w;
                                     REG := s.REG⦇0w ↦ 1w; 1w ↦ p + n2w (k + 1); 2w ↦ n2w c; 8w ↦ 64w⦈;
                                     branch_hint := NONE|>`
    \\ qexists_tac `s_svc`
    \\ conj_tac
    >- (step_m3_det s_cbz_nz \\ step_m3_det s_mov0 \\ step_m3_det s_mov1 \\ step_m3_det s_mov2 \\ step_m3_det s_mov8
        \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `is_svc0_at s_svc` by (irule s_svc \\ simp [Abbr `s_svc`] \\ metis_tac [])
    \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val send_post_eintr_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4500ECw ∧ s.REG 0w = -4w ⇒
        ∃s'. det_run 2 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x4500D4w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x4500D4w; PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det s_cmn4 \\ step_m3_det s_beq_eq
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val send_post_err_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4500ECw ∧ s.REG 9w = p ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        (s.REG 0w = 0w ∨ (word_msb (s.REG 0w) ∧ s.REG 0w ≠ -4w)) ⇒
        ∃s'. det_run 7 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
             (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)``,
    rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
    \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ `p ∉ forge_m3_shim_code_region` by simp []
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 1w⦈)` by simp [m3_shim_loaded_slot_update]
    \\ `s.REG 0w ≠ -4w ∧ (¬word_msb (s.REG 0w) ⇒ s.REG 0w = 0w)` by (Cases_on `s.REG 0w = 0w` \\ fs [] \\ EVAL_TAC)
    \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 1w⦈; PC := s.REG 30w; REG := s.REG⦇12w ↦ 1w⦈;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 0w) ∧
                                       (word_msb (s.REG 0w) ⇎
                                        BIT 63 (w2n (s.REG 0w) + 18446744073709551615 + 1)));
                                 C := ((if w2n (s.REG 0w) + 18446744073709551615 + 1 < 18446744073709551616
                                        then w2n (s.REG 0w) + 18446744073709551615 + 1
                                        else (w2n (s.REG 0w) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                       w2n (s.REG 0w) + 18446744073709551615 + 1);
                                 Z := (s.REG 0w + 0w = 0w); N := word_msb (s.REG 0w + 0w)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det s_cmn4 \\ step_m3_det s_beq_ne \\ step_m3_det s_cmp0 \\ step_m3_det s_ble_le
        \\ step_m3_det s_mov12_1 \\ step_m3_det s_strb_1 \\ step_m3_det s_ret_err
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
              arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val send_post_ok_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64) k c m.
        1 ≤ m ∧ m ≤ c ∧ c + k = 128 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4500ECw ∧ s.REG 0w = n2w m ∧
        s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w c ⇒
        ∃s'. det_run 7 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
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
       (ONCE_REWRITE_TAC [cj 1 m3_word64_arith_step_helpers]
        \\ mp_tac (Q.SPECL [`c`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub)) \\ simp [])
    \\ `(n2w m : word64) + (p + n2w (k + 1)) = p + n2w (k + m + 1)` by
       (ONCE_REWRITE_TAC [cj 2 m3_word64_arith_step_helpers] \\ simp [wordsTheory.word_add_n2w])
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
    >- (step_m3_det s_cmn4 \\ step_m3_det s_beq_ne \\ step_m3_det s_cmp0 \\ step_m3_det s_ble_gt
        \\ step_m3_det s_add10_x0 \\ step_m3_det s_sub11_x0 \\ step_m3_det s_b_loop
        \\ simp [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
                 arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ `aligned 2 (0x4500D4w:word64)` by EVAL_TAC
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val send_write_loop_universal = prove(
    ``∀n allow_err cb_begin cb_end bm_buf_end k c s os os_f ms_f ec (p:word64) (frame:word8 list).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        c + k = 128 ∧ LENGTH frame = 128 ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4500D4w ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w c ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        (∀i. i < 128 ⇒ s.MEM (p + n2w (i + 1)) = EL i frame) ∧
        NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f ⇒
        (∃n' s'.
           n' < n ∧
           NRC (m3_whole_step allow_err) n' (os with out := os.out ++ DROP k frame, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
        (allow_err ∧
         ∃n' s' chunk.
           n' < n ∧ chunk ≼ DROP k frame ∧
           NRC (m3_whole_step allow_err) n' (os with out := os.out ++ chunk, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
    completeInduct_on `n` \\ rpt strip_tac
    \\ Cases_on `c = 0`
    >- (
      `k = 128` by decide_tac \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `p`] mp_tac send_loop_done_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj1_tac \\ qexists_tac `n - 3` \\ qexists_tac `s'`
      \\ `os with out := os.out = os` by simp [m3_os_component_equality]
      \\ simp [listTheory.DROP_LENGTH_TOO_LONG] \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `1 ≤ c` by decide_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `p`, `k`, `c`] mp_tac send_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ Cases_on `n - 5`
    >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, cj 3 m3_whole_step_svc_det]
    \\ rpt strip_tac \\ qpat_x_assum `_ = os with out := _` SUBST_ALL_TAC
    \\ rename1 `NRC _ _ (os with out := os.out ++ ch, z2) _`
    \\ `svc_write_rel s_svc z2 ch ∧ (¬allow_err ⇒ svc_write_noerr_rel s_svc z2 ch)` by
         (qpat_x_assum `(if allow_err then svc_write_rel else svc_write_noerr_rel) _ _ _` mp_tac
          \\ Cases_on `allow_err` \\ simp [] \\ metis_tac [svc_write_noerr_imp_rel])
    \\ qpat_x_assum `svc_write_rel _ _ _`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_write_rel_def, svc_frame_rel_def])
    \\ `s_svc.REG 9w = p ∧ s_svc.REG 10w = p + n2w (k + 1) ∧
        s_svc.REG 11w = n2w c ∧ s_svc.REG 30w = s.REG 30w` by simp []
    \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
        z2.PC = 0x4500ECw ∧ z2.REG 9w = p ∧ z2.REG 10w = p + n2w (k + 1) ∧
        z2.REG 11w = n2w c ∧ z2.REG 30w = s.REG 30w ∧
        (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
         (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY (fs [bits_of_def] \\ NO_TAC)
          \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ qpat_x_assum `_ ∨ _ ∨ _`
         (DISJ_CASES_THEN2 strip_assume_tac
           (DISJ_CASES_THEN2 strip_assume_tac (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
    >- (
      `os with out := os.out ++ ch = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac send_post_eintr_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac) \\ impl_tac >- decide_tac
      \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                  `k`, `c`, `s'`, `os`, `os_f`, `ms_f`, `ec`, `p`, `frame`] mp_tac)
      \\ impl_tac >- simp [] \\ strip_tac
      >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ simp [] \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `chunk`
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      rename1 `z2.REG 0w = n2w m`
      \\ `m ≤ c` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
      \\ `ch = TAKE m (DROP k frame)` by (
           simp [] \\ irule listTheory.LIST_EQ \\ simp [] \\ rpt strip_tac
           \\ simp [EL_TAKE, EL_DROP, m3_word_add_n2w_right, wordsTheory.word_add_n2w]
           \\ `k + 1 + x = (k + x) + 1` by decide_tac \\ pop_assum SUBST1_TAC
           \\ qpat_x_assum `∀i. i < 128 ⇒ s.MEM _ = _` (qspec_then `k + x` mp_tac) \\ simp [])
      \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`, `k`, `c`, `m`] mp_tac send_post_ok_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 7` mp_tac) \\ impl_tac >- decide_tac
      \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                  `k + m`, `c - m`, `s'`, `os with out := os.out ++ TAKE m (DROP k frame)`,
                                  `os_f`, `ms_f`, `ec`, `p`, `frame`] mp_tac)
      \\ impl_tac >- simp [] \\ strip_tac
      >- (
        disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''`
        \\ fs [m3_append_take_drop_add] \\ rfs [m3_append_take_drop_add]
        \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ simp []
      \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `TAKE m (DROP k frame) ++ chunk`
      \\ `TAKE m (DROP k frame) ++ chunk ≼ DROP k frame` by (
           CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM (Q.SPECL [`k`, `m`, `frame`] m3_take_drop_add)]))
           \\ simp [])
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `allow_err` by
         (CCONTR_TAC \\ `svc_write_noerr_rel s_svc z2 ch ∧ c ≤ 128` by
            (conj_tac >- (qpat_x_assum `¬allow_err ⇒ _` irule \\ simp []) \\ decide_tac)
          \\ mp_tac (Q.SPECL [`s_svc`, `z2`, `ch`, `c`] m3_svc_write_noerr_not_err) \\ simp [])
    \\ `os with out := os.out ++ ch = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac send_post_err_det \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ disj2_tac \\ simp [] \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `[]`
    \\ `os with out := os.out = os` by simp [m3_os_component_equality]
    \\ qpat_x_assum `NRC _ _ _ _` mp_tac
    \\ simp [] \\ disch_then (K ALL_TAC) \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
in

Theorem m3_ffisend128_universal_slot:
  ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFISEND_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 129 ⇒
       ∃n' s'. n' < n ∧
         NRC (m3_whole_step allow_err) n' (os, s') (os_f, ms_f) ∧
         m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (129 ≤ w2n (s.REG 3w) ⇒
       (∃n' s'.
          n' < n ∧
          NRC (m3_whole_step allow_err) n' (os with out := os.out ++ TAKE 128 (DROP 1 bytes2), s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w :: DROP 1 bytes2) s s') ∨
       (allow_err ∧
        ∃n' s' chunk.
          n' < n ∧ chunk ≼ TAKE 128 (DROP 1 bytes2) ∧
          NRC (m3_whole_step allow_err) n' (os with out := os.out ++ chunk, s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s'))
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac send_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w` \\ `s.REG 2w = p` by simp [Abbr `p`]
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac send_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ m3_peel_nrc_tac
  \\ qspecl_then [`n - 6`, `allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                  `0`, `128`, `s_loop`, `os`, `os_f`, `ms_f`, `ec`, `p`, `TAKE 128 (DROP 1 bytes2)`]
       mp_tac send_write_loop_universal
  \\ impl_tac
  >- (simp [] \\ rpt strip_tac \\ simp [EL_TAKE, EL_DROP] \\ `1 + i = i + 1` by decide_tac
      \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `i + 1` mp_tac) \\ simp [])
  \\ strip_tac
  >- (
    disj1_tac \\ qexists_tac `n'` \\ qexists_tac `s'`
    \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
         (qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `0w`]
            mp_tac asm_write_bytearray_drop1 \\ simp [])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
    \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ disj2_tac \\ simp [] \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `chunk`
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`]
          mp_tac asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
  \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

Theorem m3_ffisend128_noerr_exists_slot:
  ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFISEND_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 129 ⇒
       ∃s'. (∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (129 ≤ w2n (s.REG 3w) ⇒
       ∃s'. (∀os. RTC (m3_whole_step F) (os, s) (os with out := os.out ++ TAKE 128 (DROP 1 bytes2), s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w :: DROP 1 bytes2) s s')
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac send_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `s'` \\ simp [] \\ metis_tac [m3_det_run_imp_rtc])
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w` \\ `s.REG 2w = p` by simp [Abbr `p`]
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac send_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `p`, `0`, `128`] mp_tac send_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
  \\ `GENLIST (λi. s.MEM (p + n2w i + 1w)) 128 = TAKE 128 (DROP 1 bytes2)` by
       (irule listTheory.LIST_EQ \\ simp [] \\ rpt strip_tac
        \\ simp [EL_TAKE, EL_DROP, m3_word_add_n2w_right, wordsTheory.word_add_n2w]
        \\ `1 + x = x + 1` by decide_tac
        \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `x + 1` mp_tac) \\ simp [])
  \\ qabbrev_tac `s_post = s_svc with <|PC := 0x4500ECw; REG := s_svc.REG⦇0w ↦ 128w⦈|>`
  \\ `∀os. m3_whole_step F (os, s_svc) (os with out := os.out ++ TAKE 128 (DROP 1 bytes2), s_post)` by
       (gen_tac \\ `s_svc.exception = NoException` by fs [arm8_ok_erase]
        \\ simp [m3_whole_step_def, Abbr `s_post`, svc_write_noerr_rel_def, svc_frame_rel_def,
                 combinTheory.APPLY_UPDATE_THM]
        \\ qexists_tac `TAKE 128 (DROP 1 bytes2)` \\ simp []
        \\ qexists_tac `128` \\ simp [])
  \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
       (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ rpt conj_tac \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC) \\ gvs [sp_ok_def, bits_of_def])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `p`, `0`, `128`, `128`] mp_tac send_post_ok_det
  \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `p`] mp_tac send_loop_done_det
  \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qexists_tac `s''`
  \\ conj_tac
  >- (gen_tac
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with out := os.out ++ TAKE 128 (DROP 1 bytes2), s_post)`
      \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with out := os.out ++ TAKE 128 (DROP 1 bytes2), s')`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
      \\ irule m3_det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
  \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
        \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `0w`]
             mp_tac asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
  \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

end;
