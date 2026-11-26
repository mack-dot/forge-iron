(*
  Forge Milestone 1: Verified ARM64 Veneers & Raw Linux Syscall Shim Proof.

  Proves real L3 ARMv8 instruction semantics (via arm8_stepLib + forge_arm8Erasure)
  directly over the exact linked 44 veneer words [0x400000..0x4000B0) and 80 shim
  words [0x421000..0x421140) extracted from kernel/build/forge-kernel:
    1. _start -> cml_main -> cake_main (43 exact real-ARM64 steps).
    2. cake_ffirecv16 -> ffirecv16 with explicit Linux svc_read_rel (handles
       arbitrary partial reads, EINTR retries, clean EOF, truncated <16B EOF,
       and x3 < 17 totality, preserving x19..x28, x30, SP_EL0, and processor bits).
    3. cake_ffisend16 -> ffisend16 with explicit Linux svc_write_rel (handles
       arbitrary partial writes, EINTR retries, and x3 < 17 totality).
    4. cake_exit -> cml_exit (full 64-bit x0 check -> svc_exit_group_rel 0w / 1w)
       and cake_install -> cml_install (-> svc_exit_group_rel 2w).
    5. Discharges targetSem$ffi_interfer_ok, install_interfer_ok, start_pc_ok,
       lo55, interfer_sp_bits_ok, and is_arm8_machine_config for forge_mc.
*)
Theory forge_shimProof
Ancestors
  words arithmetic list combin pred_set relation
  arm8 arm8_step arm8_target arm8_config arm8_configProof
  asmProps targetSem misc
  forge_counterSpec forge_contractSpec forge_arm8Erasure
Libs
  preamble blastLib wordsLib arm8_stepLib

(* ---- 1. Memory Congruence & Region Disjointness (addresses & shim words pinned in forge_contractSpec) ---- *)

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

Theorem shim_loaded_cong:
  ∀m1 m2.
    (∀a. a ∈ forge_shim_code_region ⇒ m1 a = m2 a) ⇒
    (shim_loaded m1 ⇔ shim_loaded m2)
Proof
  rpt strip_tac
  \\ simp [shim_loaded_def]
  \\ `LENGTH forge_veneers_words = 44 ∧ LENGTH forge_shim_words = 80` by
       simp [forge_veneers_words_def, forge_shim_words_def]
  \\ `words32_in_mem FORGE_VENEERS_BASE forge_veneers_words m1 ⇔
      words32_in_mem FORGE_VENEERS_BASE forge_veneers_words m2` by
     (irule words32_in_mem_cong
      \\ simp [FORGE_VENEERS_BASE_def, dimword_64]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def])
  \\ `words32_in_mem FORGE_SHIM_BASE forge_shim_words m1 ⇔
      words32_in_mem FORGE_SHIM_BASE forge_shim_words m2` by
     (irule words32_in_mem_cong
      \\ simp [FORGE_SHIM_BASE_def, dimword_64]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs [forge_shim_code_region_def, FORGE_SHIM_BASE_def, FORGE_SHIM_END_def])
  \\ simp []
QED

Theorem shim_loaded_update[local]:
  ∀m a b. a ∉ forge_shim_code_region ⇒ (shim_loaded (m⦇a ↦ b⦈) ⇔ shim_loaded m)
Proof
  rpt strip_tac \\ irule shim_loaded_cong
  \\ simp [combinTheory.APPLY_UPDATE_THM] \\ rpt strip_tac \\ rw [] \\ fs []
QED

Theorem forge_regions_disjoint:
  (∀a. a ∈ forge_prog_addresses ⇒ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_rx_tmp_region ⇒ a ∉ forge_prog_addresses ∧ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_cml_ptrs_region ⇒ a ∉ forge_prog_addresses ∧ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_heap_hdr_region ⇒ a ∉ forge_cml_ptrs_region ∧ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_prog_addresses ⇒ untagged a) ∧
  (∀a. a ∈ forge_shim_code_region ⇒ untagged a)
Proof
  simp [forge_prog_addresses_def, forge_code_region_def, forge_bitmaps_region_def,
        forge_heap_stack_region_def, forge_shim_code_region_def,
        forge_rx_tmp_region_def, forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
        FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def, FORGE_CB_END_def,
        FORGE_SHIM_BASE_def, FORGE_SHIM_END_def, FORGE_CML_HEAP_def,
        FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def, FORGE_RX_TMP_def,
        FORGE_HEAP_def, FORGE_STACKEND_def, untagged_def]
  \\ rpt conj_tac \\ gen_tac \\ blastLib.BBLAST_TAC
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

(* ---- 4. Core Real-ARM64 Lifting, Arithmetic & Bytearray Helpers ---- *)

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

Theorem Next_of_NextStateARM8[local]:
  ∀s s'. NextStateARM8 s = SOME s' ⇒ arm8$Next s = s'
Proof
  rw [NextStateARM8_def]
QED

Theorem FUNPOW_Next_SUC[local]:
  ∀n s s1. NextStateARM8 s = SOME s1 ⇒ FUNPOW arm8$Next (SUC n) s = FUNPOW arm8$Next n s1
Proof
  rpt strip_tac \\ drule Next_of_NextStateARM8 \\ simp [arithmeticTheory.FUNPOW]
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

Theorem cmp_carry_17[local]:
  ∀w:word64.
    ((if w2n w + 18446744073709551598 + 1 < 18446744073709551616
      then w2n w + 18446744073709551598 + 1
      else (w2n w + 18446744073709551598 + 1) MOD 18446744073709551616) ≠
     w2n w + 18446744073709551598 + 1) ⇔ 17 ≤ w2n w
Proof
  gen_tac
  \\ assume_tac (Q.ISPEC `w:word64` wordsTheory.w2n_lt)
  \\ fs [dimword_64]
  \\ Cases_on `17 ≤ w2n w` \\ simp []
  \\ `w2n w + 18446744073709551599 = 18446744073709551616 + (w2n w - 17)` by decide_tac
  \\ simp [arithmeticTheory.ADD_MODULUS_LEFT]
QED

Theorem cmp_carry_16[local]:
  ∀w:word64.
    ((if w2n w + 18446744073709551599 + 1 < 18446744073709551616
      then w2n w + 18446744073709551599 + 1
      else (w2n w + 18446744073709551599 + 1) MOD 18446744073709551616) ≠
     w2n w + 18446744073709551599 + 1) ⇔ 16 ≤ w2n w
Proof
  gen_tac
  \\ assume_tac (Q.ISPEC `w:word64` wordsTheory.w2n_lt)
  \\ fs [dimword_64]
  \\ Cases_on `16 ≤ w2n w` \\ simp []
  \\ `w2n w + 18446744073709551600 = 18446744073709551616 + (w2n w - 16)` by decide_tac
  \\ simp [arithmeticTheory.ADD_MODULUS_LEFT]
QED

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

Theorem asm_write_bytearray_drop17:
  ∀(p:word64) dm m bs f.
    17 ≤ LENGTH bs ∧ LENGTH f = 16 ∧
    read_bytearray p (LENGTH bs) (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p (0w :: f ++ DROP 17 bs) m =
    (p =+ 0w) (asm_write_bytearray (p + 1w) f m)
Proof
  rpt strip_tac
  \\ `∃b0 hd16 tl17. bs = b0 :: (hd16 ++ tl17) ∧ LENGTH hd16 = 16` by
     (Cases_on `bs` \\ fs []
      \\ `16 ≤ LENGTH t` by decide_tac
      \\ qexists_tac `TAKE 16 t` \\ qexists_tac `DROP 16 t`
      \\ simp [listTheory.TAKE_DROP])
  \\ rveq
  \\ `DROP 17 (b0 :: (hd16 ++ tl17)) = tl17` by
     (`17 = SUC 16` by decide_tac \\ pop_assum SUBST1_TAC
      \\ simp [listTheory.DROP_def, DROP_APPEND2])
  \\ simp []
  \\ `read_bytearray (p + 17w) (LENGTH tl17) (λa. if a ∈ dm then SOME (m a) else NONE) = SOME tl17` by
     (qpat_x_assum `read_bytearray _ _ _ = SOME _` mp_tac
      \\ simp [listTheory.LENGTH_APPEND] \\ strip_tac
      \\ imp_res_tac read_bytearray_mem_eq
      \\ `∀k (q:word64) ys.
            (∀i. i < k ⇒ q + n2w i ∈ dm ∧ m (q + n2w i) = EL i ys) ∧ LENGTH ys = k ⇒
            read_bytearray q k (λa. if a ∈ dm then SOME (m a) else NONE) = SOME ys` by
         (Induct_on `k` >- (Cases_on `ys` \\ simp [miscTheory.read_bytearray_def])
          \\ rpt gen_tac \\ Cases_on `ys` \\ simp [miscTheory.read_bytearray_def]
          \\ strip_tac
          \\ `q ∈ dm ∧ m q = h` by (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
          \\ simp []
          \\ first_x_assum (qspecl_then [`q + 1w`, `t`] mp_tac)
          \\ impl_tac
          >- (simp [] \\ rpt strip_tac
              \\ first_x_assum (qspec_then `SUC i` mp_tac)
              \\ simp [word_add_n2w_right, wordsTheory.word_add_n2w, ADD1])
          \\ simp [])
      \\ first_x_assum irule \\ simp [] \\ rpt strip_tac
      \\ qpat_x_assum `∀i. i < _ ⇒ _` (qspec_then `17 + i` mp_tac)
      \\ `p + n2w i + 17w = p + n2w (17 + i)` by
           (REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w] \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ `17 + i = SUC (16 + i)` by decide_tac \\ pop_assum SUBST1_TAC
      \\ simp [EL_APPEND2])
  \\ `asm_write_bytearray (p + 17w) tl17 m = m` by (irule asm_write_bytearray_id \\ metis_tac [])
  \\ simp [miscTheory.asm_write_bytearray_def, asm_write_bytearray_append,
           word_add_n2w_right]
QED

Theorem asm_write_bytearray_pointwise[local]:
  ∀xs (p:word64) m1 m2 a.
    m1 a = m2 a ⇒
    asm_write_bytearray p xs m1 a = asm_write_bytearray p xs m2 a
Proof
  Induct \\ simp [miscTheory.asm_write_bytearray_def, combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac \\ IF_CASES_TAC \\ simp []
QED

Theorem shim_step_arm8[local]:
  ∀inp out s s'.
    ¬is_svc0_at s ∧ NextStateARM8 s = SOME s' ⇒
    shim_step (inp, out, s) (inp, out, s')
Proof
  simp [shim_step_def, whole_step_def]
QED

Theorem shim_steps_arm8[local]:
  ∀inp out s s1 inp' out' s'.
    ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ∧
    shim_steps (inp, out, s1) (inp', out', s') ⇒
    shim_steps (inp, out, s) (inp', out', s')
Proof
  rpt strip_tac
  \\ irule (cj 2 relationTheory.RTC_RULES)
  \\ qexists_tac `(inp, out, s1)`
  \\ simp [shim_step_arm8]
QED

Theorem shim_steps_eq[local]:
  ∀x y. x = y ⇒ shim_steps x y
Proof
  rw [relationTheory.RTC_REFL]
QED

(* ---- 5. Automated O(1) Real-ARM64 Step Generator for All 124 Linked Words ---- *)

local
  val v_list = forge_veneers_words_def |> concl |> rhs |> listSyntax.dest_list |> fst
  val s_list = forge_shim_words_def |> concl |> rhs |> listSyntax.dest_list |> fst

  fun word32_hex t =
    let
      val n = wordsSyntax.dest_word_literal t
      val s = Arbnum.toHexString n
    in
      if size s < 8 then String.implode (List.tabulate (8 - size s, K #"0")) ^ s else s
    end

  val v_bytes_th =
    SIMP_RULE (srw_ss() ++ wordsLib.WORD_ss)
      [words32_in_mem_def, forge_veneers_words_def, FORGE_VENEERS_BASE_def]
      (ASSUME ``words32_in_mem FORGE_VENEERS_BASE forge_veneers_words (m:word64 -> word8)``)
  val s_bytes_th =
    SIMP_RULE (srw_ss() ++ wordsLib.WORD_ss)
      [words32_in_mem_def, forge_shim_words_def, FORGE_SHIM_BASE_def]
      (ASSUME ``words32_in_mem FORGE_SHIM_BASE forge_shim_words (m:word64 -> word8)``)

  val v_arr = Vector.fromList (CONJUNCTS v_bytes_th)
  val s_arr = Vector.fromList (CONJUNCTS s_bytes_th)
  val v_warr = Vector.fromList v_list
  val s_warr = Vector.fromList s_list

  val step_cache : (string * thm list) list ref = ref []
  fun cached_step h =
    case List.find (fn (k, _) => k = h) (!step_cache) of
      SOME (_, ths) => ths
    | NONE =>
        let val ths = arm8_stepLib.arm8_step_hex h
        in step_cache := (h, ths) :: !step_cache; ths end

  fun get_word_info region idx =
    if region = "veneer" then
      let
        val base_n = 0x00400000 + 4 * idx
        val wtm = Vector.sub (v_warr, idx)
        val bths = List.tabulate (4, fn j => Vector.sub (v_arr, 4 * idx + j))
      in (base_n, word32_hex wtm, bths) end
    else
      let
        val base_n = 0x00421000 + 4 * idx
        val wtm = Vector.sub (s_warr, idx)
        val bths = List.tabulate (4, fn j => Vector.sub (s_arr, 4 * idx + j))
      in (base_n, word32_hex wtm, bths) end

  (* Classify which hypotheses of arm8_step_hex are auto-discharged by arm8_ok + shim_loaded *)
  fun is_std_hyp t =
    let val s = term_to_string t in
      String.isSubstring "SCTLR_EL1" s orelse
      String.isSubstring "TCR_EL1" s orelse
      String.isSubstring ".EL =" s orelse
      String.isSubstring ".exception =" s orelse
      String.isSubstring ".MEM " s orelse
      String.isSubstring "aligned 2 " s
    end

  fun prove_real_step region idx branch_idx =
    let
      val (addr_n, hex, bths) = get_word_info region idx
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
      val goal_rhs =
        rhs (concl (SIMP_CONV (srw_ss() ++ wordsLib.WORD_ss)
          [restore_erase_record_upds, erase_fields, ASSUME pc_eq]
          ``restore (bits_of (s:arm8_state)) ^rhs_erased``))
      val need_untagged_lr = (hex = "D65F03C0")
      val extra_hyps' = if need_untagged_lr then ``untagged ((s:arm8_state).REG 30w)`` :: extra_hyps
                        else extra_hyps
      val all_hyps = [``arm8_ok (erase (s:arm8_state))``, ``sp_ok (s:arm8_state)``,
                      ``shim_loaded (s:arm8_state).MEM``, pc_eq] @ extra_hyps'
      val goal = mk_imp (list_mk_conj all_hyps,
                   ``NextStateARM8 (s:arm8_state) = SOME ^goal_rhs ∧ ¬is_svc0_at (s:arm8_state)``)
    in
      prove (goal,
        rpt strip_tac
        >- (
          `NextStateARM8 (erase s) = SOME ^rhs_erased` by
            (mp_tac (DISCH_ALL erased_th)
             \\ simp ([arm8_ok_erase, erase_fields, shim_loaded_def] @ inst_bths)
             \\ fs ([arm8_ok_erase, erase_fields, shim_loaded_def] @ inst_bths)
             \\ TRY (EVAL_TAC \\ NO_TAC))
          \\ mp_tac (SPECL [``s:arm8_state``, rhs_erased] NextStateARM8_restore)
          \\ impl_tac
          >- (simp [untagged_def] \\ fs [erase_fields, untagged_def] \\ TRY (EVAL_TAC \\ NO_TAC))
          \\ asm_simp_tac (srw_ss() ++ wordsLib.WORD_ss) [restore_erase_record_upds, erase_fields])
        \\ gvs [shim_loaded_def, is_svc0_at_def]
        \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) inst_bths)
        \\ gvs [])
    end

  fun prove_svc0_at region idx =
    let
      val (addr_n, _, bths) = get_word_info region idx
      val addr_tm = wordsSyntax.mk_wordii (addr_n, 64)
      val inst_bths = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) bths
    in
      GEN_ALL (prove (``shim_loaded (s:arm8_state).MEM ∧ s.PC = ^addr_tm ⇒ is_svc0_at s``,
        rpt strip_tac
        \\ gvs [shim_loaded_def, is_svc0_at_def]
        \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) inst_bths)
        \\ simp []))
    end
in
  val prove_real_step = prove_real_step
  val prove_svc0_at = prove_svc0_at
end;

(* ---- 6. Startup Proof: _start (16 steps) + cml_main (27 steps) -> cake_main ---- *)

local
  val start_ths = List.tabulate (16, fn i => prove_real_step "shim" i 0)
  val cml_ths   = List.tabulate (27, fn i => prove_real_step "veneer" i 0)

  fun fast_eval (g as (_, w)) =
    if can (find_term (fn t => is_const t andalso fst (dest_const t) = "shim_loaded")) w
    then NO_TAC g else (EVAL_TAC \\ NO_TAC) g

  (* Advance a det_run (SUC k) s target goal by one real ARMv8 step *)
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
                    shim_loaded_update, forge_shim_code_region_def,
                    FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                    FORGE_SHIM_BASE_def, FORGE_SHIM_END_def,
                    wordsTheory.word_lo_n2w, wordsTheory.word_ls_n2w, dimword_64,
                    word_add_n2w_right, wordsTheory.word_add_n2w,
                    cmp_carry_17, cmp_carry_16, cmp_zero_gt_cond, cmn_4_zero,
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
  val start_ths = start_ths
  val cml_ths = cml_ths
  val step_det = step_det
end;

(* Micro-block 1..3 of _start: 5 instructions each storing one pointer in cml_ptrs *)
Theorem start_block1[local]:
  ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x421000w ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧
      s1.PC = 0x421014w ∧
      mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. 0x430008w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 5 s`
  \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇0x430007w ↦ (63 >< 56) (0x450000w:word64);
                                                0x430006w ↦ (55 >< 48) (0x450000w:word64);
                                                0x430005w ↦ (47 >< 40) (0x450000w:word64);
                                                0x430004w ↦ (39 >< 32) (0x450000w:word64);
                                                0x430003w ↦ (31 >< 24) (0x450000w:word64);
                                                0x430002w ↦ (23 >< 16) (0x450000w:word64);
                                                0x430001w ↦ (15 >< 8) (0x450000w:word64);
                                                0x430000w ↦ (7 >< 0) (0x450000w:word64)⦈;
                                   PC := 0x421014w;
                                   REG := s.REG⦇0w ↦ 0x450000w; 1w ↦ 0x430000w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 5 s s_tgt` by
     (EVERY (map step_det (List.take (start_ths, 5)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_HEAP_def, FORGE_HEAP_def]
      \\ mp_tac (Q.SPECL [`s.MEM`, `0x430000w`, `0x450000w`] mem_dword_write8)
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC))
      \\ simp [])
  >- (irule (iffRL shim_loaded_cong) \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                           FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem start_block2[local]:
  ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x421014w ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧
      s1.PC = 0x421028w ∧
      mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a <₊ 0x430008w ∨ 0x430010w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 5 s`
  \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇0x43000Fw ↦ (63 >< 56) (0x470000w:word64);
                                                0x43000Ew ↦ (55 >< 48) (0x470000w:word64);
                                                0x43000Dw ↦ (47 >< 40) (0x470000w:word64);
                                                0x43000Cw ↦ (39 >< 32) (0x470000w:word64);
                                                0x43000Bw ↦ (31 >< 24) (0x470000w:word64);
                                                0x43000Aw ↦ (23 >< 16) (0x470000w:word64);
                                                0x430009w ↦ (15 >< 8) (0x470000w:word64);
                                                0x430008w ↦ (7 >< 0) (0x470000w:word64)⦈;
                                   PC := 0x421028w;
                                   REG := s.REG⦇0w ↦ 0x470000w; 1w ↦ 0x430008w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 5 s s_tgt` by
     (EVERY (map step_det (List.take (List.drop (start_ths, 5), 5)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_STACK_def, FORGE_STACK_def]
      \\ mp_tac (Q.SPECL [`s.MEM`, `0x430008w`, `0x470000w`] mem_dword_write8)
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC))
      \\ simp [])
  >- (irule (iffRL shim_loaded_cong) \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                           FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem start_block3[local]:
  ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x421028w ⇒
    let s1 = FUNPOW arm8$Next 6 s in
      det_run 6 s s1 ∧
      s1.PC = FORGE_VENEERS_BASE ∧
      mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a <₊ 0x430010w ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 6 s`
  \\ qabbrev_tac `s_tgt = s with <|MEM := s.MEM⦇0x430017w ↦ (63 >< 56) (0x490000w:word64);
                                                0x430016w ↦ (55 >< 48) (0x490000w:word64);
                                                0x430015w ↦ (47 >< 40) (0x490000w:word64);
                                                0x430014w ↦ (39 >< 32) (0x490000w:word64);
                                                0x430013w ↦ (31 >< 24) (0x490000w:word64);
                                                0x430012w ↦ (23 >< 16) (0x490000w:word64);
                                                0x430011w ↦ (15 >< 8) (0x490000w:word64);
                                                0x430010w ↦ (7 >< 0) (0x490000w:word64)⦈;
                                   PC := 0x400000w;
                                   REG := s.REG⦇0w ↦ 0x490000w; 1w ↦ 0x430010w⦈;
                                   branch_hint := SOME BranchType_JMP|>`
  \\ `det_run 6 s s_tgt` by
     (EVERY (map step_det (List.drop (start_ths, 10)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_VENEERS_BASE_def]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_STACKEND_def, FORGE_STACKEND_def]
      \\ mp_tac (Q.SPECL [`s.MEM`, `0x430010w`, `0x490000w`] mem_dword_write8)
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC))
      \\ simp [])
  >- (irule (iffRL shim_loaded_cong) \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                           FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem start_16_steps:
  ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_SHIM_BASE ⇒
    let s1 = FUNPOW arm8$Next 16 s in
      det_run 16 s s1 ∧
      s1.PC = FORGE_VENEERS_BASE ∧
      mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
      mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
      mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `16 = 6 + (5 + 5)` by decide_tac \\ pop_assum SUBST1_TAC
  \\ rewrite_tac [arithmeticTheory.FUNPOW_ADD]
  \\ fs [FORGE_SHIM_BASE_def]
  \\ drule_all start_block1 \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sA = FUNPOW arm8$Next 5 s`
  \\ drule_all start_block2 \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sB = FUNPOW arm8$Next 5 sA`
  \\ drule_all start_block3 \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sC = FUNPOW arm8$Next 6 sB`
  \\ simp []
  \\ rpt conj_tac
  >- (`16 = (5 + 5) + 6` by decide_tac \\ pop_assum SUBST1_TAC
      \\ irule det_run_add \\ qexists_tac `sB` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sA` \\ simp [])
  >- (`mem_dword sC.MEM FORGE_CML_HEAP = mem_dword sA.MEM FORGE_CML_HEAP` by
        (irule mem_dword_cong \\ simp [FORGE_CML_HEAP_def] \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sC.MEM ad`
         \\ `ad <₊ 0x430010w ∧ ad <₊ 0x430008w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  \\ `mem_dword sC.MEM FORGE_CML_STACK = mem_dword sB.MEM FORGE_CML_STACK` by
       (irule mem_dword_cong \\ simp [FORGE_CML_STACK_def] \\ rpt strip_tac
        \\ qmatch_goalsub_abbrev_tac `sC.MEM ad`
        \\ `ad <₊ 0x430010w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
        \\ simp [])
  \\ simp []
QED

(* Micro-blocks of cml_main (27 steps) *)

Theorem cml_main_head[local]:
  ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
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
                                   REG := s.REG⦇0w ↦ 0x4000B0w; 1w ↦ 0x450000w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 5 s s_tgt` by
     (EVERY (map step_det (List.take (cml_ths, 5)))
      \\ fs [det_run_def, Abbr `s_tgt`, FORGE_CML_HEAP_def, FORGE_HEAP_def,
             arm8Theory.arm8_state_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_CAKE_MAIN_def, FORGE_HEAP_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

local
  fun mk_hdr_store_thm name start_idx pc_in pc_out off_tm val_tm =
    let
      val blk = List.take (List.drop (cml_ths, start_idx), 3)
      val dst_tm = ``(0x450000w:word64) + ^off_tm``
      val dst_val = rhs (concl (EVAL dst_tm))
      val goal =
        ``∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
              s.PC = ^pc_in ∧ s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
            let s1 = FUNPOW arm8$Next 3 s in
              det_run 3 s s1 ∧
              s1.PC = ^pc_out ∧
              s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
              mem_dword s1.MEM ^dst_val = ^val_tm ∧
              (∀a. a <₊ ^dst_val ∨ ^dst_val + 8w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
              (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
              shim_loaded s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
              bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0``
    in
      store_thm (name, goal,
        rpt strip_tac
        \\ qabbrev_tac `s1 = FUNPOW arm8$Next 3 s`
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
        \\ `det_run 3 s s_tgt` by
           (`s.REG 1w = 0x450000w` by fs [FORGE_HEAP_def]
            \\ EVERY (map step_det blk)
            \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
                     combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
            \\ rw [] \\ fs [])
        \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
        \\ simp [] \\ simp [Abbr `s_tgt`, combinTheory.APPLY_UPDATE_THM]
        \\ rpt conj_tac
        >- (mp_tac (SPECL [``(s:arm8_state).MEM``, dst_val, val_tm] mem_dword_write8) \\ simp [])
        >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC))
            \\ simp [])
        >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_heap_hdr_region_def, FORGE_HEAP_def] \\ EVAL_TAC))
            \\ simp [])
        >- (irule (iffRL shim_loaded_cong) \\ qexists_tac `s.MEM` \\ simp []
            \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_shim_code_region_def, FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def,
                                                 FORGE_SHIM_BASE_def, FORGE_SHIM_END_def] \\ EVAL_TAC))
            \\ simp [])
        \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC)
    end
in
  val cml_hdr0 = mk_hdr_store_thm "cml_hdr0"  5 ``0x400014w:word64`` ``0x400020w:word64`` ``0w:word64``  ``0x430018w:word64``
  val cml_hdr1 = mk_hdr_store_thm "cml_hdr1"  8 ``0x400020w:word64`` ``0x40002Cw:word64`` ``8w:word64``  ``0x430F38w:word64``
  val cml_hdr2 = mk_hdr_store_thm "cml_hdr2" 11 ``0x40002Cw:word64`` ``0x400038w:word64`` ``16w:word64`` ``0x430F38w:word64``
  val cml_hdr3 = mk_hdr_store_thm "cml_hdr3" 14 ``0x400038w:word64`` ``0x400044w:word64`` ``24w:word64`` ``0x41234Cw:word64``
  val cml_hdr4 = mk_hdr_store_thm "cml_hdr4" 17 ``0x400044w:word64`` ``0x400050w:word64`` ``32w:word64`` ``0x420000w:word64``
end;

Theorem cml_main_tail[local]:
  ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
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
                                   REG := s.REG⦇2w ↦ 0x470000w; 3w ↦ 0x490000w⦈;
                                   branch_hint := SOME BranchType_JMP|>`
  \\ `det_run 7 s s_tgt` by
     (EVERY (map step_det (List.drop (cml_ths, 20)))
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

Theorem startup_to_cake_main:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_SHIM_BASE ⇒
    let s1 = FUNPOW arm8$Next 43 s in
      det_run 43 s s1 ∧
      s1.PC = FORGE_CAKE_MAIN ∧
      s1.REG 0w = FORGE_CAKE_MAIN ∧
      s1.REG 1w = FORGE_HEAP ∧
      s1.REG 2w = FORGE_STACK ∧
      s1.REG 3w = FORGE_STACKEND ∧
      mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
      mem_dword s1.MEM (FORGE_HEAP + 8w) = FORGE_BM_BUF_END ∧
      mem_dword s1.MEM (FORGE_HEAP + 16w) = FORGE_BM_BUF_END ∧
      mem_dword s1.MEM (FORGE_HEAP + 24w) = FORGE_CB_BEGIN ∧
      mem_dword s1.MEM (FORGE_HEAP + 32w) = FORGE_CB_END ∧
      (∀a. a ∉ forge_cml_ptrs_region ∧ a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
      shim_loaded s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `43 = 7 + (3 + (3 + (3 + (3 + (3 + (5 + 16))))))` by decide_tac
  \\ pop_assum SUBST1_TAC
  \\ rewrite_tac [arithmeticTheory.FUNPOW_ADD]
  \\ qspec_then `s` mp_tac start_16_steps \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `s0 = FUNPOW arm8$Next 16 s`
  \\ qspec_then `s0` mp_tac cml_main_head \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sA = FUNPOW arm8$Next 5 s0`
  \\ qspec_then `sA` mp_tac cml_hdr0 \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sB = FUNPOW arm8$Next 3 sA`
  \\ qspec_then `sB` mp_tac cml_hdr1 \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sC = FUNPOW arm8$Next 3 sB`
  \\ qspec_then `sC` mp_tac cml_hdr2 \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sD = FUNPOW arm8$Next 3 sC`
  \\ qspec_then `sD` mp_tac cml_hdr3 \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sE = FUNPOW arm8$Next 3 sD`
  \\ qspec_then `sE` mp_tac cml_hdr4 \\ simp [LET_THM] \\ strip_tac
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
  \\ qspec_then `sF` mp_tac cml_main_tail \\ simp [LET_THM] \\ strip_tac
  \\ simp [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def,
           FORGE_CB_BEGIN_def, FORGE_CB_END_def]
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
  >- (`mem_dword sF.MEM 0x450000w = mem_dword sB.MEM 0x450000w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x450008w ∧ ad <₊ 0x450010w ∧ ad <₊ 0x450018w ∧ ad <₊ 0x450020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  >- (`mem_dword sF.MEM 0x450008w = mem_dword sC.MEM 0x450008w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x450010w ∧ ad <₊ 0x450018w ∧ ad <₊ 0x450020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  >- (`mem_dword sF.MEM 0x450010w = mem_dword sD.MEM 0x450010w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x450018w ∧ ad <₊ 0x450020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  >- (`mem_dword sF.MEM 0x450018w = mem_dword sE.MEM 0x450018w` by
        (irule mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x450020w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
QED

(* ---- 7. Exit & Install Veneer + Stub Proofs (Forward + Universal Whole-Step) ---- *)

local
  val veneer_exit_th    = prove_real_step "veneer" 40 0
  val veneer_install_th = prove_real_step "veneer" 36 0
  val exit_cbz_nz_th    = prove_real_step "shim" 71 0
  val exit_cbz_z_th     = prove_real_step "shim" 71 1
  val exit_mov1_th      = prove_real_step "shim" 72 0
  val exit_mov8_th      = prove_real_step "shim" 73 0
  val exit_svc_th       = prove_svc0_at   "shim" 74
  val inst_mov2_th      = prove_real_step "shim" 76 0
  val inst_mov8_th      = prove_real_step "shim" 77 0
  val inst_svc_th       = prove_svc0_at   "shim" 78
in
  val veneer_exit_th = veneer_exit_th
  val veneer_install_th = veneer_install_th
  val exit_cbz_nz_th = exit_cbz_nz_th
  val exit_cbz_z_th = exit_cbz_z_th
  val exit_mov1_th = exit_mov1_th
  val exit_mov8_th = exit_mov8_th
  val exit_svc_th = exit_svc_th
  val inst_mov2_th = inst_mov2_th
  val inst_mov8_th = inst_mov8_th
  val inst_svc_th = inst_svc_th
end;

Theorem cake_exit_to_svc_exit_group:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_EXIT_VENEER ⇒
    ∃k.
      let s1 = FUNPOW arm8$Next k s in
        det_run k s s1 ∧
        s1.PC = 0x421128w ∧
        svc_exit_group_rel (if s.REG 0w = 0w then 0w else 1w) s1 ∧
        s1.MEM = s.MEM ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `s.PC = 0x4000A0w` by fs [FORGE_EXIT_VENEER_def]
  \\ Cases_on `s.REG 0w = 0w`
  >- (
    qexists_tac `3`
    \\ qabbrev_tac `s_tgt = s with <|PC := 0x421128w; REG := s.REG⦇8w ↦ 94w⦈; branch_hint := NONE|>`
    \\ `det_run 3 s s_tgt` by
       (step_det veneer_exit_th
        \\ step_det exit_cbz_z_th
        \\ step_det exit_mov8_th
        \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `FUNPOW arm8$Next 3 s = s_tgt` by (drule det_run_funpow \\ simp [])
    \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
    \\ mp_tac (Q.SPEC `s with <|PC := 0x421128w; REG := s.REG⦇8w ↦ 94w⦈; branch_hint := NONE|>` exit_svc_th)
    \\ simp [is_svc0_at_def])
  \\ qexists_tac `4`
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x421128w; REG := s.REG⦇0w ↦ 1w; 8w ↦ 94w⦈; branch_hint := NONE|>`
  \\ `det_run 4 s s_tgt` by
     (step_det veneer_exit_th
      \\ step_det exit_cbz_nz_th
      \\ step_det exit_mov1_th
      \\ step_det exit_mov8_th
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `FUNPOW arm8$Next 4 s = s_tgt` by (drule det_run_funpow \\ simp [])
  \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
  \\ mp_tac (Q.SPEC `s with <|PC := 0x421128w; REG := s.REG⦇0w ↦ 1w; 8w ↦ 94w⦈; branch_hint := NONE|>` exit_svc_th)
  \\ simp [is_svc0_at_def]
QED

Theorem cake_exit_universal:
  ∀rrel wrel n s inp out inp_f out_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_EXIT_VENEER ∧
    NRC (whole_step rrel wrel) n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = (if s.REG 0w = 0w then 0w else 1w)
Proof
  rpt strip_tac
  \\ drule_all cake_exit_to_svc_exit_group \\ simp [LET_THM] \\ strip_tac
  \\ drule_all det_run_peel_nrc \\ strip_tac
  \\ drule_all whole_step_nrc_exit_stuck \\ strip_tac
  \\ rveq \\ fs [svc_exit_group_rel_def]
QED

Theorem cake_install_to_svc_exit_group:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_INSTALL_VENEER ⇒
    let s1 = FUNPOW arm8$Next 3 s in
      det_run 3 s s1 ∧
      s1.PC = 0x421138w ∧
      svc_exit_group_rel 2w s1 ∧
      s1.MEM = s.MEM ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `s.PC = 0x400090w` by fs [FORGE_INSTALL_VENEER_def]
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x421138w; REG := s.REG⦇0w ↦ 2w; 8w ↦ 94w⦈; branch_hint := NONE|>`
  \\ `det_run 3 s s_tgt` by
     (step_det veneer_install_th
      \\ step_det inst_mov2_th
      \\ step_det inst_mov8_th
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `FUNPOW arm8$Next 3 s = s_tgt` by (drule det_run_funpow \\ simp [])
  \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
  \\ mp_tac (Q.SPEC `s with <|PC := 0x421138w; REG := s.REG⦇0w ↦ 2w; 8w ↦ 94w⦈; branch_hint := NONE|>` inst_svc_th)
  \\ simp [is_svc0_at_def]
QED

Theorem cake_install_universal:
  ∀rrel wrel n s inp out inp_f out_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_INSTALL_VENEER ∧
    NRC (whole_step rrel wrel) n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = 2w
Proof
  rpt strip_tac
  \\ drule_all cake_install_to_svc_exit_group \\ simp [LET_THM] \\ strip_tac
  \\ drule_all det_run_peel_nrc \\ strip_tac
  \\ drule_all whole_step_nrc_exit_stuck \\ strip_tac
  \\ rveq \\ fs [svc_exit_group_rel_def]
QED


(* ---- 8. Universal & Forward Leaf FFI Proofs: ffirecv16 & ffisend16 ---- *)

(* Extract all step theorems for ffirecv16 (veneer 28, shim 16..47) *)
local
  val v_recv       = prove_real_step "veneer" 28 0
  val r_cmp17      = prove_real_step "shim" 16 0
  val r_blo_ge     = prove_real_step "shim" 17 0
  val r_blo_lt     = prove_real_step "shim" 17 1
  val r_mov9       = prove_real_step "shim" 18 0
  val r_adrp10     = prove_real_step "shim" 19 0
  val r_add10      = prove_real_step "shim" 20 0
  val r_mov11_16   = prove_real_step "shim" 21 0
  val r_cbz_nz     = prove_real_step "shim" 22 0
  val r_cbz_z      = prove_real_step "shim" 22 1
  val r_mov0       = prove_real_step "shim" 23 0
  val r_mov1       = prove_real_step "shim" 24 0
  val r_mov2       = prove_real_step "shim" 25 0
  val r_mov8       = prove_real_step "shim" 26 0
  val r_svc        = prove_svc0_at   "shim" 27
  val r_cmn4       = prove_real_step "shim" 28 0
  val r_beq_ne     = prove_real_step "shim" 29 0
  val r_beq_eq     = prove_real_step "shim" 29 1
  val r_cmp0       = prove_real_step "shim" 30 0
  val r_ble_gt     = prove_real_step "shim" 31 0
  val r_ble_le     = prove_real_step "shim" 31 1
  val r_add10_x0   = prove_real_step "shim" 32 0
  val r_sub11_x0   = prove_real_step "shim" 33 0
  val r_b_loop     = prove_real_step "shim" 34 0
  val r_adrp12     = prove_real_step "shim" 35 0
  val r_add12      = prove_real_step "shim" 36 0
  val r_mov11_0    = prove_real_step "shim" 37 0
  val r_ldrb       = prove_real_step "shim" 38 0
  val r_add11_1    = prove_real_step "shim" 39 0
  val r_strb_reg   = prove_real_step "shim" 40 0
  val r_cmp16      = prove_real_step "shim" 41 0
  val r_blo_done   = prove_real_step "shim" 42 0
  val r_blo_more   = prove_real_step "shim" 42 1
  val r_strb_0     = prove_real_step "shim" 43 0
  val r_ret_ok     = prove_real_step "shim" 44 0
  val r_mov12_1    = prove_real_step "shim" 45 0
  val r_strb_1     = prove_real_step "shim" 46 0
  val r_ret_err    = prove_real_step "shim" 47 0
in
  val v_recv = v_recv and r_cmp17 = r_cmp17 and r_blo_ge = r_blo_ge and r_blo_lt = r_blo_lt
  val r_mov9 = r_mov9 and r_adrp10 = r_adrp10 and r_add10 = r_add10 and r_mov11_16 = r_mov11_16
  val r_cbz_nz = r_cbz_nz and r_cbz_z = r_cbz_z and r_mov0 = r_mov0 and r_mov1 = r_mov1
  val r_mov2 = r_mov2 and r_mov8 = r_mov8 and r_svc = r_svc and r_cmn4 = r_cmn4
  val r_beq_ne = r_beq_ne and r_beq_eq = r_beq_eq and r_cmp0 = r_cmp0 and r_ble_gt = r_ble_gt
  val r_ble_le = r_ble_le and r_add10_x0 = r_add10_x0 and r_sub11_x0 = r_sub11_x0
  val r_b_loop = r_b_loop and r_adrp12 = r_adrp12 and r_add12 = r_add12 and r_mov11_0 = r_mov11_0
  val r_ldrb = r_ldrb and r_add11_1 = r_add11_1 and r_strb_reg = r_strb_reg
  val r_cmp16 = r_cmp16 and r_blo_done = r_blo_done and r_blo_more = r_blo_more
  val r_strb_0 = r_strb_0 and r_ret_ok = r_ret_ok and r_mov12_1 = r_mov12_1
  val r_strb_1 = r_strb_1 and r_ret_err = r_ret_err
end;

(* Shared postcondition predicate for FFI leaf return *)
Definition ffi_return_ok_def:
  ffi_return_ok (new_bytes:word8 list) (s:arm8_state) (s':arm8_state) ⇔
    arm8_ok (erase s') ∧
    sp_ok s' ∧
    bits_of s' = bits_of s ∧
    s'.SP_EL0 = s.SP_EL0 ∧
    shim_loaded s'.MEM ∧
    s'.PC = s.REG 30w ∧
    (∀a. a ∈ forge_prog_addresses ⇒
         s'.MEM a = asm_write_bytearray (s.REG 2w) new_bytes s.MEM a) ∧
    (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))
End

(* ffirecv16 straight-line deterministic blocks *)

Theorem ffirecv16_short_det[local]:
  ∀s bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFIRECV16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    w2n (s.REG 3w) < 17 ⇒
    ∃s'. det_run 4 s s' ∧ ffi_return_ok bytes2 s s'
Proof
  rpt strip_tac
  \\ `s.PC = 0x400070w` by fs [FORGE_FFIRECV16_VENEER_def]
  \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by
       (irule asm_write_bytearray_id \\ metis_tac [])
  \\ qexists_tac `s with <|PC := s.REG 30w;
                           PSTATE := s.PSTATE with
                             <|V := (word_msb (s.REG 3w) ∧
                                     (word_msb (s.REG 3w) ⇎
                                      BIT 63 (w2n (s.REG 3w) + 18446744073709551598 + 1)));
                               C := F;
                               Z := (s.REG 3w + 0xFFFFFFFFFFFFFFEFw = 0w);
                               N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFFEFw)|>;
                           branch_hint := SOME BranchType_RET|>`
  \\ conj_tac
  >- (step_det v_recv \\ step_det r_cmp17 \\ step_det r_blo_lt \\ step_det r_ret_err
      \\ simp [det_run_def, cmp_carry_17, arm8Theory.arm8_state_component_equality])
  \\ simp [ffi_return_ok_def, arm8_ok_erase, sp_ok_def, bits_of_def]
  \\ fs [arm8_ok_erase, sp_ok_def]
QED

Theorem ffirecv16_entry_det[local]:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFIRECV16_VENEER ∧ 17 ≤ w2n (s.REG 3w) ⇒
    ∃s_loop.
      det_run 7 s s_loop ∧
      arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧ shim_loaded s_loop.MEM ∧
      bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
      s_loop.PC = 0x421058w ∧ s_loop.MEM = s.MEM ∧
      s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = FORGE_RX_TMP ∧ s_loop.REG 11w = 16w ∧
      s_loop.REG 30w = s.REG 30w ∧
      (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))
Proof
  rpt strip_tac
  \\ `s.PC = 0x400070w` by fs [FORGE_FFIRECV16_VENEER_def]
  \\ qabbrev_tac `p = s.REG 2w`
  \\ qexists_tac `s with <|PC := 0x421058w;
                           REG := s.REG⦇9w ↦ p; 10w ↦ FORGE_RX_TMP; 11w ↦ 16w⦈;
                           PSTATE := s.PSTATE with
                             <|V := (word_msb (s.REG 3w) ∧
                                     (word_msb (s.REG 3w) ⇎
                                      BIT 63 (w2n (s.REG 3w) + 18446744073709551598 + 1)));
                               C := T;
                               Z := (s.REG 3w + 0xFFFFFFFFFFFFFFEFw = 0w);
                               N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFFEFw)|>;
                           branch_hint := NONE|>`
  \\ conj_tac
  >- (step_det v_recv \\ step_det r_cmp17 \\ step_det r_blo_ge \\ step_det r_mov9
      \\ step_det r_adrp10 \\ step_det r_add10 \\ step_det r_mov11_16
      \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
           [det_run_def, Abbr `p`, FORGE_RX_TMP_def, cmp_carry_17,
            arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
            combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
  \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC
QED

Theorem ffirecv16_copy_loop_det[local]:
  ∀cnt k s (f:word8 list) (p:word64).
    1 ≤ cnt ∧ cnt + k = 16 ∧ LENGTH f = 16 ∧
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x421098w ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    s.REG 9w = p ∧ s.REG 12w = FORGE_RX_TMP ∧ s.REG 11w = n2w k ∧
    (∀i. i < 17 ⇒ p + n2w i ∈ forge_prog_addresses) ∧
    (∀i. i < 16 ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i f) ⇒
    ∃d s'.
      1 ≤ d ∧ det_run d s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧
      s'.SP_EL0 = s.SP_EL0 ∧ shim_loaded s'.MEM ∧ s'.PC = s.REG 30w ∧
      s'.MEM = (p =+ 0w) (asm_write_bytearray (p + n2w (k + 1)) (DROP k f) s.MEM) ∧
      (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)
Proof
  Induct_on `cnt`
  >- (rpt strip_tac \\ `F` by decide_tac)
  \\ rpt strip_tac
  \\ Cases_on `cnt = 0`
  >- (
    `k = 15` by decide_tac \\ pop_assum SUBST_ALL_TAC
    \\ qabbrev_tac `b15 = EL 15 f`
    \\ qpat_assum `∀i. i < 16 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `15`)
    \\ qpat_assum `∀i. i < 17 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `16`)
    \\ qpat_assum `∀i. i < 17 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `0`)
    \\ `p + 16w ∉ forge_shim_code_region ∧ p ∉ forge_shim_code_region` by
         simp [cj 1 forge_regions_disjoint]
    \\ qabbrev_tac `m1 = s.MEM⦇p + 16w ↦ b15⦈`
    \\ `shim_loaded m1` by simp [Abbr `m1`, shim_loaded_update]
    \\ qabbrev_tac `m2 = m1⦇p ↦ 0w⦈`
    \\ `shim_loaded m2` by simp [Abbr `m2`, shim_loaded_update]
    \\ `DROP 15 f = [b15]` by
         (simp [Abbr `b15`] \\ `15 < LENGTH f` by decide_tac
          \\ simp [DROP_EL_CONS, listTheory.DROP_LENGTH_NIL])
    \\ qexists_tac `7`
    \\ qexists_tac `s with <|MEM := m2; PC := s.REG 30w;
                             REG := s.REG⦇10w ↦ w2w b15; 11w ↦ 16w⦈;
                             PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac >- decide_tac
    \\ conj_tac
    >- (step_det r_ldrb \\ step_det r_add11_1 \\ step_det r_strb_reg
        \\ step_det r_cmp16 \\ step_det r_blo_done \\ step_det r_strb_0 \\ step_det r_ret_ok
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, Abbr `m2`, Abbr `m1`, Abbr `b15`, FORGE_RX_TMP_def, cmp_carry_16,
              arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
              combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [] \\ TRY (EVAL_TAC \\ NO_TAC))
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM,
             Abbr `m2`, Abbr `m1`, miscTheory.asm_write_bytearray_def]
    \\ fs [arm8_ok_erase, sp_ok_def])
  \\ `k < 15 ∧ k + 1 < 16` by decide_tac
  \\ qabbrev_tac `bk = EL k f`
  \\ qpat_assum `∀i. i < 16 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k`)
  \\ qpat_assum `∀i. i < 17 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k + 1`)
  \\ `s.MEM (FORGE_RX_TMP + n2w k) = bk` by simp [Abbr `bk`]
  \\ `p + n2w (k + 1) ∈ forge_prog_addresses` by simp []
  \\ `p + n2w (k + 1) ∉ forge_shim_code_region` by simp [cj 1 forge_regions_disjoint]
  \\ `∀i. i < 16 ⇒ p + n2w (k + 1) ≠ FORGE_RX_TMP + n2w i` by
     (rpt strip_tac
      \\ `FORGE_RX_TMP + n2w i ∈ forge_rx_tmp_region` by
           (simp [forge_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
                  word_add_n2w, w2n_n2w, dimword_64])
      \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
  \\ qabbrev_tac `m1 = s.MEM⦇p + n2w (k + 1) ↦ bk⦈`
  \\ `shim_loaded m1` by simp [Abbr `m1`, shim_loaded_update]
  \\ qabbrev_tac `s_next = s with <|MEM := m1; PC := 0x421098w;
                                    REG := s.REG⦇10w ↦ w2w bk; 11w ↦ n2w (k + 1)⦈;
                                    PSTATE := s.PSTATE with
                                      <|V := (word_msb (n2w (k + 1):word64) ∧
                                              (word_msb (n2w (k + 1):word64) ⇎
                                               BIT 63 (w2n (n2w (k + 1):word64) + 18446744073709551599 + 1)));
                                        C := F;
                                        Z := ((n2w (k + 1):word64) + 0xFFFFFFFFFFFFFFF0w = 0w);
                                        N := word_msb ((n2w (k + 1):word64) + 0xFFFFFFFFFFFFFFF0w)|>;
                                    branch_hint := SOME BranchType_JMP|>`
  \\ `det_run 5 s s_next` by
     (step_det r_ldrb \\ step_det r_add11_1 \\ step_det r_strb_reg
      \\ step_det r_cmp16 \\ step_det r_blo_more
      \\ simp [det_run_def, Abbr `s_next`, Abbr `m1`, Abbr `bk`, cmp_carry_16,
               word_add_n2w_right, wordsTheory.word_add_n2w,
               arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ qpat_x_assum `∀k s f p. _` (qspecl_then [`k + 1`, `s_next`, `f`, `p`] mp_tac)
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
       \\ `i < 16` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
       \\ qpat_x_assum `p + n2w (k + 1) = _` mp_tac
       \\ simp [word_add_n2w_right, wordsTheory.word_add_n2w,
                wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
    \\ simp [combinTheory.APPLY_UPDATE_THM])
  \\ irule asm_write_bytearray_pointwise \\ simp [combinTheory.APPLY_UPDATE_THM]
QED

Theorem ffirecv16_loop_done_det[local]:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x421058w ∧ s.REG 11w = 0w ⇒
    ∃s_cp0.
      det_run 4 s s_cp0 ∧
      arm8_ok (erase s_cp0) ∧ sp_ok s_cp0 ∧ shim_loaded s_cp0.MEM ∧
      bits_of s_cp0 = bits_of s ∧ s_cp0.SP_EL0 = s.SP_EL0 ∧
      s_cp0.PC = 0x421098w ∧ s_cp0.MEM = s.MEM ∧
      s_cp0.REG 12w = FORGE_RX_TMP ∧ s_cp0.REG 11w = 0w ∧
      (∀r. r ≠ 11w ∧ r ≠ 12w ⇒ s_cp0.REG r = s.REG r)
Proof
  rpt strip_tac
  \\ qexists_tac `s with <|PC := 0x421098w;
                           REG := s.REG⦇12w ↦ FORGE_RX_TMP; 11w ↦ 0w⦈;
                           branch_hint := NONE|>`
  \\ conj_tac
  >- (step_det r_cbz_z \\ step_det r_adrp12 \\ step_det r_add12 \\ step_det r_mov11_0
      \\ simp [det_run_def, FORGE_RX_TMP_def, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC
QED

Theorem ffirecv16_loop_to_svc_det[local]:
  ∀s k cnt.
    1 ≤ cnt ∧ cnt + k = 16 ∧
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x421058w ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w cnt ⇒
    ∃s_svc.
      det_run 5 s s_svc ∧
      arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧ shim_loaded s_svc.MEM ∧
      bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
      s_svc.PC = 0x42106Cw ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
      s_svc.REG 0w = 0w ∧ s_svc.REG 1w = FORGE_RX_TMP + n2w k ∧
      s_svc.REG 2w = n2w cnt ∧ s_svc.REG 8w = 63w ∧
      (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)
Proof
  rpt strip_tac
  \\ qabbrev_tac `s_svc = s with <|PC := 0x42106Cw;
                                   REG := s.REG⦇0w ↦ 0w; 1w ↦ FORGE_RX_TMP + n2w k;
                                                2w ↦ n2w cnt; 8w ↦ 63w⦈;
                                   branch_hint := NONE|>`
  \\ qexists_tac `s_svc`
  \\ conj_tac
  >- (step_det r_cbz_nz \\ step_det r_mov0 \\ step_det r_mov1 \\ step_det r_mov2 \\ step_det r_mov8
      \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `is_svc0_at s_svc` by (irule r_svc \\ simp [Abbr `s_svc`])
  \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC
QED

Theorem ffirecv16_post_eintr_det[local]:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x421070w ∧ s.REG 0w = -4w ⇒
    ∃s'.
      det_run 2 s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
      bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
      s'.PC = 0x421058w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG
Proof
  rpt strip_tac
  \\ qexists_tac `s with <|PC := 0x421058w;
                           PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                           branch_hint := SOME BranchType_JMP|>`
  \\ conj_tac
  >- (step_det r_cmn4 \\ step_det r_beq_eq
      \\ simp [det_run_def, arm8Theory.arm8_state_component_equality,
               arm8Theory.ProcState_component_equality]
      \\ EVAL_TAC)
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def]
  \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC
QED

Theorem ffirecv16_post_err_det[local]:
  ∀s (p:word64).
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x421070w ∧ s.REG 9w = p ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    p ∈ forge_prog_addresses ∧
    (s.REG 0w = 0w ∨ (word_msb (s.REG 0w) ∧ s.REG 0w ≠ -4w)) ⇒
    ∃s'.
      det_run 7 s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
      bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
      s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
      (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)
Proof
  rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ `p ∉ forge_shim_code_region` by simp [cj 1 forge_regions_disjoint]
  \\ `shim_loaded (s.MEM⦇p ↦ 1w⦈)` by simp [shim_loaded_update]
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
  \\ fs [arm8_ok_erase, sp_ok_def]
QED

Theorem ffirecv16_post_ok_det[local]:
  ∀s k cnt m.
    1 ≤ m ∧ m ≤ cnt ∧ cnt + k = 16 ∧
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x421070w ∧ s.REG 0w = n2w m ∧
    s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w cnt ⇒
    ∃s'.
      det_run 7 s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
      bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
      s'.PC = 0x421058w ∧ s'.MEM = s.MEM ∧
      s'.REG 10w = FORGE_RX_TMP + n2w (k + m) ∧ s'.REG 11w = n2w (cnt - m) ∧
      (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)
Proof
  rpt strip_tac
  \\ `¬word_msb (n2w m : word64) ∧ (n2w m : word64) ≠ 0w ∧ (n2w m : word64) ≠ -4w` by
     (simp [wordsTheory.word_msb_n2w, wordsTheory.n2w_11, dimword_64]
      \\ `¬BIT 63 m` by (irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
      \\ `(-4w:word64) = n2w 18446744073709551612` by EVAL_TAC
      \\ simp [wordsTheory.n2w_11, dimword_64])
  \\ `-1w * (n2w m : word64) + n2w cnt = n2w (cnt - m)` by
     (ONCE_REWRITE_TAC [cj 1 word64_arith_step_helpers]
      \\ mp_tac (Q.SPECL [`cnt`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub))
      \\ simp [])
  \\ `(n2w m : word64) + (FORGE_RX_TMP + n2w k) = FORGE_RX_TMP + n2w (k + m)` by
     (ONCE_REWRITE_TAC [cj 2 word64_arith_step_helpers]
      \\ simp [wordsTheory.word_add_n2w])
  \\ qexists_tac `s with <|PC := 0x421058w;
                           REG := s.REG⦇10w ↦ FORGE_RX_TMP + n2w (k + m); 11w ↦ n2w (cnt - m)⦈;
                           PSTATE := s.PSTATE with
                             <|V := F;
                               C := ((if w2n (n2w m:word64) + 18446744073709551615 + 1 < 18446744073709551616
                                      then w2n (n2w m:word64) + 18446744073709551615 + 1
                                      else (w2n (n2w m:word64) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                     w2n (n2w m:word64) + 18446744073709551615 + 1);
                               Z := F;
                               N := F|>;
                           branch_hint := SOME BranchType_JMP|>`
  \\ conj_tac
  >- (step_det r_cmn4 \\ step_det r_beq_ne \\ step_det r_cmp0 \\ step_det r_ble_gt
      \\ step_det r_add10_x0 \\ step_det r_sub11_x0 \\ step_det r_b_loop
      \\ simp [det_run_def, cmp_zero_gt_cond,
               arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `aligned 2 (0x421058w:word64)` by EVAL_TAC
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def]
QED

(* Helper tactic: deterministically peel the active det_run off the active NRC *)
val peel_nrc_tac =
  qpat_x_assum `det_run _ _ _` (fn dth =>
    qpat_x_assum `NRC _ _ _ _` (fn nth =>
      mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] det_run_peel_nrc) dth)
      \\ disch_then (fn th => mp_tac (MATCH_MP th nth))
      \\ disch_then (fn th => first_assum (mp_tac o MATCH_MP th))
      \\ strip_tac));

Theorem svc_read_noerr_not_fatal[local]:
  ∀inp s s' rest cnt.
    cnt ≤ 16 ∧ s.REG 2w = n2w cnt ∧ svc_read_noerr_rel inp s s' rest ⇒
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
    cnt ≤ 16 ∧ s.REG 2w = n2w cnt ∧ svc_write_noerr_rel s s' chunk ⇒
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

(* UNIVERSAL ffirecv16 read loop: covers ALL partial reads, EINTR retries, EOF, truncated <16B, and fatal errors *)
Theorem ffirecv16_read_loop_universal[local]:
  ∀n allow_err wrel k cnt acc s inp out inp_f out_f ms_f ec (p:word64).
    cnt + k = 16 ∧ LENGTH acc = k ∧
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x421058w ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    s.REG 9w = p ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w cnt ∧
    p ∈ forge_prog_addresses ∧
    (∀i. i < k ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i acc) ∧
    NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
        n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (∃n' s' frame inp_after.
       n' < n ∧ LENGTH frame = 16 ∧ acc ++ inp = frame ++ inp_after ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
           n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
       arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
       bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
       s'.PC = 0x421098w ∧ s'.REG 9w = p ∧ s'.REG 12w = FORGE_RX_TMP ∧ s'.REG 11w = 0w ∧
       s'.REG 30w = s.REG 30w ∧
       (∀i. i < 16 ⇒ s'.MEM (FORGE_RX_TMP + n2w i) = EL i frame) ∧
       (∀a. a ∉ forge_rx_tmp_region ⇒ s'.MEM a = s.MEM a) ∧
       (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
    (∃n' s' inp_after.
       n' < n ∧ (allow_err ∨ LENGTH (acc ++ inp) < 16) ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
           n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
       arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
       bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
       s'.PC = s.REG 30w ∧
       (∀a. a ∈ forge_prog_addresses ⇒ s'.MEM a = (p =+ 1w) s.MEM a) ∧
       (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))
Proof
  completeInduct_on `n` \\ rpt strip_tac
  \\ Cases_on `cnt = 0`
  >- (
    `k = 16` by decide_tac \\ rveq
    \\ qspec_then `s` mp_tac ffirecv16_loop_done_det \\ impl_tac >- simp [] \\ strip_tac
    \\ peel_nrc_tac
    \\ disj1_tac
    \\ qexists_tac `n - 4` \\ qexists_tac `s_cp0` \\ qexists_tac `acc` \\ qexists_tac `inp`
    \\ simp [] \\ rpt strip_tac \\ rveq \\ simp [])
  \\ `1 ≤ cnt` by decide_tac
  \\ qspecl_then [`s`, `k`, `cnt`] mp_tac ffirecv16_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
  \\ peel_nrc_tac
  \\ Cases_on `n - 5`
  >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
  \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
  \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_svc_read_det]
  \\ rpt strip_tac
  \\ rename1 `NRC _ _ (z0, out, z2) _`
  \\ `s_svc.REG 8w = 63w ∧ s_svc.REG 0w = 0w ∧ s_svc.REG 1w = FORGE_RX_TMP + n2w k ∧
      s_svc.REG 2w = n2w cnt ∧ s_svc.REG 9w = p ∧ s_svc.REG 10w = FORGE_RX_TMP + n2w k ∧
      s_svc.REG 11w = n2w cnt ∧ s_svc.REG 30w = s.REG 30w` by simp []
  \\ `svc_read_rel inp s_svc z2 z0 ∧
      (¬allow_err ⇒ svc_read_noerr_rel inp s_svc z2 z0)` by
       (Cases_on `allow_err` \\ fs [svc_read_noerr_imp_rel])
  \\ qpat_x_assum `svc_read_rel _ _ _ _`
       (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_read_rel_def, svc_frame_rel_def])
  \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
      z2.PC = 0x421070w ∧ z2.REG 9w = p ∧ z2.REG 10w = FORGE_RX_TMP + n2w k ∧
      z2.REG 11w = n2w cnt ∧ z2.REG 30w = s.REG 30w ∧
      (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
       (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ rpt conj_tac
        \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
        \\ TRY (fs [sp_ok_def] \\ NO_TAC)
        \\ TRY (fs [bits_of_def] \\ NO_TAC)
        \\ rpt strip_tac \\ rveq \\ simp [])
  \\ qpat_x_assum `_ ∨ _ ∨ _ ∨ _` (REPEAT_TCL DISJ_CASES_THEN strip_assume_tac)
  >- (
    (* Case 1: EINTR (-4w) -> retry at 0x421058 with n' < n *)
    qpat_x_assum `z0 = inp` SUBST_ALL_TAC
    \\ `shim_loaded z2.MEM` by simp []
    \\ qspec_then `z2` mp_tac ffirecv16_post_eintr_det \\ impl_tac >- simp [] \\ strip_tac
    \\ peel_nrc_tac
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `wrel`, `k`, `cnt`, `acc`, `s'`, `inp`, `out`, `inp_f`, `out_f`, `ms_f`, `ec`, `p`] mp_tac)
    \\ impl_tac >- simp []
    \\ strip_tac
    >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
        \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
    \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `inp_after`
    \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
  >- (
    (* Case 2: EOF (0w, inp = []) -> error return; LENGTH (acc ++ []) = k < 16 *)
    qpat_x_assum `z0 = []` SUBST_ALL_TAC
    \\ qpat_x_assum `inp = []` SUBST_ALL_TAC
    \\ `shim_loaded z2.MEM ∧ k < 16` by simp []
    \\ qspecl_then [`z2`, `p`] mp_tac ffirecv16_post_err_det
    \\ impl_tac >- simp []
    \\ strip_tac
    \\ peel_nrc_tac
    \\ disj2_tac
    \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `[]`
    \\ simp [combinTheory.APPLY_UPDATE_THM]
    \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
  >- (
    (* Case 3: Fatal read error (only possible when allow_err = T!) *)
    `allow_err` by
      (CCONTR_TAC
       \\ `svc_read_noerr_rel inp s_svc z2 z0 ∧ cnt ≤ 16` by (conj_tac >- metis_tac [] \\ decide_tac)
       \\ mp_tac (Q.SPECL [`inp`, `s_svc`, `z2`, `z0`, `cnt`] svc_read_noerr_not_fatal)
       \\ simp [])
    \\ qpat_x_assum `z0 = inp` SUBST_ALL_TAC
    \\ `shim_loaded z2.MEM` by simp []
    \\ qspecl_then [`z2`, `p`] mp_tac ffirecv16_post_err_det
    \\ impl_tac >- simp []
    \\ strip_tac
    \\ peel_nrc_tac
    \\ disj2_tac
    \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `inp`
    \\ simp [combinTheory.APPLY_UPDATE_THM]
    \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
  \\ (* Case 4: Partial/full read of m bytes (1 ≤ m ≤ cnt) *)
     rename1 `z2.REG 0w = n2w m`
  \\ qpat_x_assum `z0 = DROP m inp` SUBST_ALL_TAC
  \\ `m ≤ cnt` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
  \\ `∀a. a ∉ forge_rx_tmp_region ⇒ z2.MEM a = s.MEM a` by
       (rpt strip_tac \\ simp []
        \\ irule asm_write_bytearray_unchanged_lt
        \\ rpt strip_tac
        \\ `i < m` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
        \\ `FORGE_RX_TMP + n2w k + n2w i ∈ forge_rx_tmp_region` by
             (simp [forge_rx_tmp_region_def, FORGE_RX_TMP_def, word_add_n2w_right,
                    wordsTheory.word_add_n2w, WORD_LS, WORD_LO, w2n_n2w, dimword_64])
        \\ metis_tac [])
  \\ `shim_loaded z2.MEM` by
       (mp_tac (Q.SPECL [`z2.MEM`, `s.MEM`] shim_loaded_cong)
        \\ impl_tac
        >- (rpt strip_tac \\ first_x_assum irule
            \\ strip_tac \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
        \\ simp [])
  \\ qspecl_then [`z2`, `k`, `cnt`, `m`] mp_tac ffirecv16_post_ok_det
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ peel_nrc_tac
  \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 7` mp_tac)
  \\ impl_tac >- decide_tac
  \\ disch_then (qspecl_then [`allow_err`, `wrel`, `k + m`, `cnt - m`, `acc ++ TAKE m inp`,
                              `s'`, `DROP m inp`, `out`, `inp_f`, `out_f`, `ms_f`, `ec`, `p`] mp_tac)
  \\ impl_tac
  >- (
    simp []
    \\ rpt strip_tac
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
          \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
          \\ qpat_x_assum `∀a. a ∉ forge_rx_tmp_region ⇒ z2.MEM a = s.MEM a` (mp_tac o Q.SPEC `a`)
          \\ simp [combinTheory.APPLY_UPDATE_THM])
      \\ rpt strip_tac \\ rveq \\ simp [])
QED

Theorem ffirecv16_universal:
  ∀allow_err wrel n s inp out inp_f out_f ms_f ec bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFIRECV16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
        n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 17 ⇒
       ∃n' s'. n' < n ∧
         NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
             n' (inp, out, s') (inp_f, out_f, ms_f) ∧
         ffi_return_ok bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
       (∃n' s' frame inp_after.
          n' < n ∧ LENGTH frame = 16 ∧ inp = frame ++ inp_after ∧
          NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
              n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
          ffi_return_ok (0w :: frame ++ DROP 17 bytes2) s s') ∨
       (∃n' s' inp_after.
          n' < n ∧ (allow_err ∨ LENGTH inp < 16) ∧
          NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel)
              n' (inp_after, out, s') (inp_f, out_f, ms_f) ∧
          ffi_return_ok (1w :: DROP 1 bytes2) s s'))
Proof
  rpt strip_tac
  >- (
    qspecl_then [`s`, `bytes2`] mp_tac ffirecv16_short_det \\ impl_tac >- simp [] \\ strip_tac
    \\ peel_nrc_tac
    \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `∀i. i < 17 ⇒ p + n2w i ∈ forge_prog_addresses` by
       (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses` (qspec_then `i` mp_tac) \\ simp [])
  \\ `p ∈ forge_prog_addresses` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac
        \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspec_then `s` mp_tac ffirecv16_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ peel_nrc_tac
  \\ qspecl_then [`n - 7`, `allow_err`, `wrel`, `0`, `16`, `[]`, `s_loop`, `inp`, `out`,
                  `inp_f`, `out_f`, `ms_f`, `ec`, `p`] mp_tac ffirecv16_read_loop_universal
  \\ impl_tac >- simp []
  \\ strip_tac
  >- (
    qspecl_then [`16`, `0`, `s'`, `frame`, `p`] mp_tac ffirecv16_copy_loop_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ peel_nrc_tac
    \\ disj1_tac
    \\ qexists_tac `n' - d` \\ qexists_tac `s''` \\ qexists_tac `frame` \\ qexists_tac `inp_after`
    \\ `asm_write_bytearray (s.REG 2w) (0w :: frame ++ DROP 17 bytes2) s.MEM =
        (p =+ 0w) (asm_write_bytearray (p + 1w) frame s.MEM)` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
          \\ qspecl_then [`p`, `forge_prog_addresses`, `s.MEM`, `bytes2`, `frame`] mp_tac
               asm_write_bytearray_drop17 \\ simp [])
    \\ REWRITE_TAC [ffi_return_ok_def]
    \\ pop_assum SUBST1_TAC
    \\ fs [] \\ rpt conj_tac \\ TRY decide_tac
    \\ rpt strip_tac
    \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
    \\ irule asm_write_bytearray_pointwise
    \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
    \\ simp [])
  \\ disj2_tac
  \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `inp_after`
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
        \\ qspecl_then [`p`, `forge_prog_addresses`, `s.MEM`, `bytes2`, `1w`] mp_tac
             asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [ffi_return_ok_def]
  \\ pop_assum SUBST1_TAC
  \\ fs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp []
QED

(* Forward ffirecv16 existence under error-free Linux read(0) (for Conjunct 2 liveness) *)
Theorem ffirecv16_noerr_exists:
  ∀s bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFIRECV16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 17 ⇒
       ∃s'. (∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
            ffi_return_ok bytes2 s s') ∧
    (∀f. 17 ≤ w2n (s.REG 3w) ∧ LENGTH f = 16 ⇒
       ∃s'. (∀rest out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                            (f ++ rest, out, s) (rest, out, s')) ∧
            ffi_return_ok (0w :: f ++ DROP 17 bytes2) s s') ∧
    (∀tail_bs. 17 ≤ w2n (s.REG 3w) ∧ LENGTH tail_bs < 16 ⇒
       ∃s'. (∀out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (tail_bs, out, s) ([], out, s')) ∧
            ffi_return_ok (1w :: DROP 1 bytes2) s s')
Proof
  rpt strip_tac
  >- (qspecl_then [`s`, `bytes2`] mp_tac ffirecv16_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `s'` \\ simp []
      \\ metis_tac [det_run_imp_nrc, arithmeticTheory.RTC_eq_NRC])
  >- (
    imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `p = s.REG 2w`
    \\ `∀i. i < 17 ⇒ p + n2w i ∈ forge_prog_addresses` by
         (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses` (qspec_then `i` mp_tac) \\ simp [])
    \\ qspec_then `s` mp_tac ffirecv16_entry_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qspecl_then [`s_loop`, `0`, `16`] mp_tac ffirecv16_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP f s.MEM`
    \\ qabbrev_tac `s_post = s_svc with <|PC := 0x421070w; REG := s_svc.REG⦇0w ↦ 16w⦈; MEM := m1|>`
    \\ `∀rest out. whole_step svc_read_noerr_rel svc_write_noerr_rel (f ++ rest, out, s_svc) (rest, out, s_post)` by
         (rpt strip_tac
          \\ simp [whole_step_def, Abbr `s_post`, svc_read_noerr_rel_def, svc_frame_rel_def,
                   combinTheory.APPLY_UPDATE_THM]
          \\ conj_tac >- fs [arm8_ok_erase]
          \\ qexists_tac `16` \\ simp [Abbr `m1`, TAKE_APPEND1, DROP_APPEND2, listTheory.TAKE_LENGTH_ID_rwt])
    \\ `∀a. a ∉ forge_rx_tmp_region ⇒ m1 a = s.MEM a` by
         (rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt
          \\ rpt strip_tac
          \\ `FORGE_RX_TMP + n2w i ∈ forge_rx_tmp_region` by
               simp [forge_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
                     word_add_n2w, w2n_n2w, dimword_64]
          \\ rveq \\ fs [])
    \\ `shim_loaded m1` by
         (mp_tac (Q.SPECL [`m1`, `s.MEM`] shim_loaded_cong)
          \\ impl_tac
          >- (rpt strip_tac \\ first_x_assum irule
              \\ strip_tac \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
          \\ simp [])
    \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
         (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac
          \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ gvs [sp_ok_def, bits_of_def])
    \\ qspecl_then [`s_post`, `0`, `16`, `16`] mp_tac ffirecv16_post_ok_det
    \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
    \\ strip_tac
    \\ qspec_then `s'` mp_tac ffirecv16_loop_done_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qspecl_then [`16`, `0`, `s_cp0`, `f`, `p`] mp_tac ffirecv16_copy_loop_det
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
    \\ `asm_write_bytearray (s.REG 2w) (0w :: f ++ DROP 17 bytes2) s.MEM =
        (p =+ 0w) (asm_write_bytearray (p + 1w) f s.MEM)` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
          \\ qspecl_then [`p`, `forge_prog_addresses`, `s.MEM`, `bytes2`, `f`] mp_tac
               asm_write_bytearray_drop17 \\ simp [])
    \\ REWRITE_TAC [ffi_return_ok_def]
    \\ pop_assum SUBST1_TAC
    \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
    \\ rpt conj_tac
    >- (rpt strip_tac
        \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
        \\ irule asm_write_bytearray_pointwise
        \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
        \\ simp [])
    \\ rpt strip_tac \\ rveq \\ simp [])
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `p ∈ forge_prog_addresses` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac
        \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
        \\ qspecl_then [`p`, `forge_prog_addresses`, `s.MEM`, `bytes2`, `1w`] mp_tac
             asm_write_bytearray_drop1 \\ simp [])
  \\ qspec_then `s` mp_tac ffirecv16_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ Cases_on `tail_bs = []`
  >- (
    rveq
    \\ qspecl_then [`s_loop`, `0`, `16`] mp_tac ffirecv16_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qabbrev_tac `s_post = s_svc with <|PC := 0x421070w; REG := s_svc.REG⦇0w ↦ 0w⦈|>`
    \\ `∀out. whole_step svc_read_noerr_rel svc_write_noerr_rel ([], out, s_svc) ([], out, s_post)` by
         (gen_tac \\ simp [whole_step_def, Abbr `s_post`, svc_read_noerr_rel_def, svc_frame_rel_def,
                           combinTheory.APPLY_UPDATE_THM] \\ fs [arm8_ok_erase])
    \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
         (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac
          \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ gvs [sp_ok_def, bits_of_def])
    \\ qspecl_then [`s_post`, `p`] mp_tac ffirecv16_post_err_det
    \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
    \\ strip_tac
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
    \\ REWRITE_TAC [ffi_return_ok_def]
    \\ qpat_x_assum `asm_write_bytearray (s.REG 2w) _ _ = _` SUBST1_TAC
    \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
    \\ rpt strip_tac \\ rveq \\ simp [])
  \\ `1 ≤ LENGTH tail_bs` by (Cases_on `tail_bs` \\ fs [])
  \\ qspecl_then [`s_loop`, `0`, `16`] mp_tac ffirecv16_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
  \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP tail_bs s.MEM`
  \\ qabbrev_tac `s_post1 = s_svc with <|PC := 0x421070w; REG := s_svc.REG⦇0w ↦ n2w (LENGTH tail_bs)⦈; MEM := m1|>`
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
  \\ `shim_loaded m1` by
       (mp_tac (Q.SPECL [`m1`, `s.MEM`] shim_loaded_cong)
        \\ impl_tac
        >- (rpt strip_tac \\ first_x_assum irule
            \\ strip_tac \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
        \\ simp [])
  \\ `arm8_ok (erase s_post1) ∧ sp_ok s_post1 ∧ bits_of s_post1 = bits_of s ∧ s_post1.SP_EL0 = s.SP_EL0` by
       (simp [Abbr `s_post1`, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ rpt conj_tac
        \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
        \\ gvs [sp_ok_def, bits_of_def])
  \\ qspecl_then [`s_post1`, `0`, `16`, `LENGTH tail_bs`] mp_tac ffirecv16_post_ok_det
  \\ impl_tac >- simp [Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM]
  \\ strip_tac
  \\ qspecl_then [`s'`, `LENGTH tail_bs`, `16 - LENGTH tail_bs`] mp_tac ffirecv16_loop_to_svc_det
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ qabbrev_tac `s_post2 = s_svc' with <|PC := 0x421070w; REG := s_svc'.REG⦇0w ↦ 0w⦈|>`
  \\ `∀out. whole_step svc_read_noerr_rel svc_write_noerr_rel ([], out, s_svc') ([], out, s_post2)` by
       (gen_tac \\ simp [whole_step_def, Abbr `s_post2`, svc_read_noerr_rel_def, svc_frame_rel_def,
                         combinTheory.APPLY_UPDATE_THM] \\ fs [arm8_ok_erase])
  \\ `arm8_ok (erase s_post2) ∧ sp_ok s_post2 ∧ bits_of s_post2 = bits_of s ∧ s_post2.SP_EL0 = s.SP_EL0` by
       (simp [Abbr `s_post2`, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ rpt conj_tac
        \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
        \\ gvs [sp_ok_def, bits_of_def])
  \\ qspecl_then [`s_post2`, `p`] mp_tac ffirecv16_post_err_det
  \\ impl_tac >- simp [Abbr `s_post2`, Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM]
  \\ strip_tac
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
  \\ REWRITE_TAC [ffi_return_ok_def]
  \\ qpat_x_assum `asm_write_bytearray (s.REG 2w) _ _ = _` SUBST1_TAC
  \\ simp [Abbr `s_post2`, Abbr `s_post1`, combinTheory.APPLY_UPDATE_THM]
  \\ rpt conj_tac
  >- (rpt strip_tac
      \\ `a ∉ forge_rx_tmp_region` by (strip_tac \\ drule (cj 2 forge_regions_disjoint) \\ gvs [])
      \\ simp [combinTheory.APPLY_UPDATE_THM])
  \\ rpt strip_tac \\ rveq \\ simp []
QED

(* Extract all step theorems for ffisend16 (veneer 32, shim 48..70) *)
local
  val v_send       = prove_real_step "veneer" 32 0
  val s_cmp17      = prove_real_step "shim" 48 0
  val s_blo_ge     = prove_real_step "shim" 49 0
  val s_blo_lt     = prove_real_step "shim" 49 1
  val s_mov9       = prove_real_step "shim" 50 0
  val s_add10      = prove_real_step "shim" 51 0
  val s_mov11_16   = prove_real_step "shim" 52 0
  val s_cbz_nz     = prove_real_step "shim" 53 0
  val s_cbz_z      = prove_real_step "shim" 53 1
  val s_mov0       = prove_real_step "shim" 54 0
  val s_mov1       = prove_real_step "shim" 55 0
  val s_mov2       = prove_real_step "shim" 56 0
  val s_mov8       = prove_real_step "shim" 57 0
  val s_svc        = prove_svc0_at   "shim" 58
  val s_cmn4       = prove_real_step "shim" 59 0
  val s_beq_ne     = prove_real_step "shim" 60 0
  val s_beq_eq     = prove_real_step "shim" 60 1
  val s_cmp0       = prove_real_step "shim" 61 0
  val s_ble_gt     = prove_real_step "shim" 62 0
  val s_ble_le     = prove_real_step "shim" 62 1
  val s_add10_x0   = prove_real_step "shim" 63 0
  val s_sub11_x0   = prove_real_step "shim" 64 0
  val s_b_loop     = prove_real_step "shim" 65 0
  val s_strb_0     = prove_real_step "shim" 66 0
  val s_ret_ok     = prove_real_step "shim" 67 0
  val s_mov12_1    = prove_real_step "shim" 68 0
  val s_strb_1     = prove_real_step "shim" 69 0
  val s_ret_err    = prove_real_step "shim" 70 0
in
  val v_send = v_send and s_cmp17 = s_cmp17 and s_blo_ge = s_blo_ge and s_blo_lt = s_blo_lt
  val s_mov9 = s_mov9 and s_add10 = s_add10 and s_mov11_16 = s_mov11_16
  val s_cbz_nz = s_cbz_nz and s_cbz_z = s_cbz_z and s_mov0 = s_mov0 and s_mov1 = s_mov1
  val s_mov2 = s_mov2 and s_mov8 = s_mov8 and s_svc = s_svc and s_cmn4 = s_cmn4
  val s_beq_ne = s_beq_ne and s_beq_eq = s_beq_eq and s_cmp0 = s_cmp0 and s_ble_gt = s_ble_gt
  val s_ble_le = s_ble_le and s_add10_x0 = s_add10_x0 and s_sub11_x0 = s_sub11_x0
  val s_b_loop = s_b_loop and s_strb_0 = s_strb_0 and s_ret_ok = s_ret_ok
  val s_mov12_1 = s_mov12_1 and s_strb_1 = s_strb_1 and s_ret_err = s_ret_err
end;

(* ffisend16 straight-line deterministic blocks *)

Theorem ffisend16_short_det[local]:
  ∀s bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFISEND16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    w2n (s.REG 3w) < 17 ⇒
    ∃s'. det_run 4 s s' ∧ ffi_return_ok bytes2 s s'
Proof
  rpt strip_tac
  \\ `s.PC = 0x400080w` by fs [FORGE_FFISEND16_VENEER_def]
  \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by
       (irule asm_write_bytearray_id \\ metis_tac [])
  \\ qexists_tac `s with <|PC := s.REG 30w;
                           PSTATE := s.PSTATE with
                             <|V := (word_msb (s.REG 3w) ∧
                                     (word_msb (s.REG 3w) ⇎
                                      BIT 63 (w2n (s.REG 3w) + 18446744073709551598 + 1)));
                               C := F;
                               Z := (s.REG 3w + 0xFFFFFFFFFFFFFFEFw = 0w);
                               N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFFEFw)|>;
                           branch_hint := SOME BranchType_RET|>`
  \\ conj_tac
  >- (step_det v_send \\ step_det s_cmp17 \\ step_det s_blo_lt \\ step_det s_ret_err
      \\ simp [det_run_def, cmp_carry_17, arm8Theory.arm8_state_component_equality])
  \\ simp [ffi_return_ok_def, arm8_ok_erase, sp_ok_def, bits_of_def]
  \\ fs [arm8_ok_erase, sp_ok_def]
QED

Theorem ffisend16_entry_det[local]:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFISEND16_VENEER ∧ 17 ≤ w2n (s.REG 3w) ⇒
    ∃s_loop.
      det_run 6 s s_loop ∧
      arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧ shim_loaded s_loop.MEM ∧
      bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
      s_loop.PC = 0x4210D4w ∧ s_loop.MEM = s.MEM ∧
      s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = s.REG 2w + 1w ∧ s_loop.REG 11w = 16w ∧
      s_loop.REG 30w = s.REG 30w ∧
      (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))
Proof
  rpt strip_tac
  \\ `s.PC = 0x400080w` by fs [FORGE_FFISEND16_VENEER_def]
  \\ qabbrev_tac `p = s.REG 2w`
  \\ qexists_tac `s with <|PC := 0x4210D4w;
                           REG := s.REG⦇9w ↦ p; 10w ↦ p + 1w; 11w ↦ 16w⦈;
                           PSTATE := s.PSTATE with
                             <|V := (word_msb (s.REG 3w) ∧
                                     (word_msb (s.REG 3w) ⇎
                                      BIT 63 (w2n (s.REG 3w) + 18446744073709551598 + 1)));
                               C := T;
                               Z := (s.REG 3w + 0xFFFFFFFFFFFFFFEFw = 0w);
                               N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFFEFw)|>;
                           branch_hint := NONE|>`
  \\ conj_tac
  >- (step_det v_send \\ step_det s_cmp17 \\ step_det s_blo_ge \\ step_det s_mov9
      \\ step_det s_add10 \\ step_det s_mov11_16
      \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
           [det_run_def, Abbr `p`, cmp_carry_17,
            arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
            combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
  \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC
QED

Theorem ffisend16_loop_done_det[local]:
  ∀s (p:word64).
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x4210D4w ∧ s.REG 9w = p ∧ s.REG 11w = 0w ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    p ∈ forge_prog_addresses ⇒
    ∃s'.
      det_run 3 s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
      bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
      s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧ s'.REG = s.REG
Proof
  rpt strip_tac
  \\ `p ∉ forge_shim_code_region` by simp [cj 1 forge_regions_disjoint]
  \\ `shim_loaded (s.MEM⦇p ↦ 0w⦈)` by simp [shim_loaded_update]
  \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 0w⦈; PC := s.REG 30w;
                           branch_hint := SOME BranchType_RET|>`
  \\ conj_tac
  >- (step_det s_cbz_z \\ step_det s_strb_0 \\ step_det s_ret_ok
      \\ simp [det_run_def, arm8Theory.arm8_state_component_equality])
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def]
  \\ fs [arm8_ok_erase, sp_ok_def]
QED

Theorem ffisend16_loop_to_svc_det[local]:
  ∀s (p:word64) k cnt.
    1 ≤ cnt ∧ cnt + k = 16 ∧
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x4210D4w ∧ s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w cnt ⇒
    ∃s_svc.
      det_run 5 s s_svc ∧
      arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧ shim_loaded s_svc.MEM ∧
      bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
      s_svc.PC = 0x4210E8w ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
      s_svc.REG 0w = 1w ∧ s_svc.REG 1w = p + n2w (k + 1) ∧
      s_svc.REG 2w = n2w cnt ∧ s_svc.REG 8w = 64w ∧
      (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)
Proof
  rpt strip_tac
  \\ qabbrev_tac `s_svc = s with <|PC := 0x4210E8w;
                                   REG := s.REG⦇0w ↦ 1w; 1w ↦ p + n2w (k + 1);
                                                2w ↦ n2w cnt; 8w ↦ 64w⦈;
                                   branch_hint := NONE|>`
  \\ qexists_tac `s_svc`
  \\ conj_tac
  >- (step_det s_cbz_nz \\ step_det s_mov0 \\ step_det s_mov1 \\ step_det s_mov2 \\ step_det s_mov8
      \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `is_svc0_at s_svc` by (irule s_svc \\ simp [Abbr `s_svc`])
  \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC
QED

Theorem ffisend16_post_eintr_det[local]:
  ∀s.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x4210ECw ∧ s.REG 0w = -4w ⇒
    ∃s'.
      det_run 2 s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
      bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
      s'.PC = 0x4210D4w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG
Proof
  rpt strip_tac
  \\ qexists_tac `s with <|PC := 0x4210D4w;
                           PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                           branch_hint := SOME BranchType_JMP|>`
  \\ conj_tac
  >- (step_det s_cmn4 \\ step_det s_beq_eq
      \\ simp [det_run_def, arm8Theory.arm8_state_component_equality,
               arm8Theory.ProcState_component_equality]
      \\ EVAL_TAC)
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def]
  \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC
QED

Theorem ffisend16_post_err_det[local]:
  ∀s (p:word64).
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x4210ECw ∧ s.REG 9w = p ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    p ∈ forge_prog_addresses ∧
    (s.REG 0w = 0w ∨ (word_msb (s.REG 0w) ∧ s.REG 0w ≠ -4w)) ⇒
    ∃s'.
      det_run 7 s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
      bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
      s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
      (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)
Proof
  rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ `p ∉ forge_shim_code_region` by simp [cj 1 forge_regions_disjoint]
  \\ `shim_loaded (s.MEM⦇p ↦ 1w⦈)` by simp [shim_loaded_update]
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
  \\ fs [arm8_ok_erase, sp_ok_def]
QED

Theorem ffisend16_post_ok_det[local]:
  ∀s (p:word64) k cnt m.
    1 ≤ m ∧ m ≤ cnt ∧ cnt + k = 16 ∧
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x4210ECw ∧ s.REG 0w = n2w m ∧
    s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w cnt ⇒
    ∃s'.
      det_run 7 s s' ∧
      arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
      bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
      s'.PC = 0x4210D4w ∧ s'.MEM = s.MEM ∧
      s'.REG 10w = p + n2w (k + m + 1) ∧ s'.REG 11w = n2w (cnt - m) ∧
      (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)
Proof
  rpt strip_tac
  \\ `¬word_msb (n2w m : word64) ∧ (n2w m : word64) ≠ 0w ∧ (n2w m : word64) ≠ -4w` by
     (simp [wordsTheory.word_msb_n2w, wordsTheory.n2w_11, dimword_64]
      \\ `¬BIT 63 m` by (irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
      \\ `(-4w:word64) = n2w 18446744073709551612` by EVAL_TAC
      \\ simp [wordsTheory.n2w_11, dimword_64])
  \\ `-1w * (n2w m : word64) + n2w cnt = n2w (cnt - m)` by
     (ONCE_REWRITE_TAC [cj 1 word64_arith_step_helpers]
      \\ mp_tac (Q.SPECL [`cnt`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub))
      \\ simp [])
  \\ `(n2w m : word64) + (p + n2w (k + 1)) = p + n2w (k + m + 1)` by
     (ONCE_REWRITE_TAC [cj 2 word64_arith_step_helpers]
      \\ simp [wordsTheory.word_add_n2w]
      \\ `k + 1 + m = k + m + 1` by decide_tac \\ simp [])
  \\ qexists_tac `s with <|PC := 0x4210D4w;
                           REG := s.REG⦇10w ↦ p + n2w (k + m + 1); 11w ↦ n2w (cnt - m)⦈;
                           PSTATE := s.PSTATE with
                             <|V := F;
                               C := ((if w2n (n2w m:word64) + 18446744073709551615 + 1 < 18446744073709551616
                                      then w2n (n2w m:word64) + 18446744073709551615 + 1
                                      else (w2n (n2w m:word64) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                     w2n (n2w m:word64) + 18446744073709551615 + 1);
                               Z := F;
                               N := F|>;
                           branch_hint := SOME BranchType_JMP|>`
  \\ conj_tac
  >- (step_det s_cmn4 \\ step_det s_beq_ne \\ step_det s_cmp0 \\ step_det s_ble_gt
      \\ step_det s_add10_x0 \\ step_det s_sub11_x0 \\ step_det s_b_loop
      \\ simp [det_run_def, cmp_zero_gt_cond,
               arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `aligned 2 (0x4210D4w:word64)` by EVAL_TAC
  \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def]
QED

(* UNIVERSAL ffisend16 write loop: covers ALL partial writes, EINTR retries, and write errors *)
Theorem ffisend16_write_loop_universal[local]:
  ∀n allow_err rrel k cnt s inp out inp_f out_f ms_f ec (p:word64) (frame:word8 list).
    cnt + k = 16 ∧ LENGTH frame = 16 ∧
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = 0x4210D4w ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    s.REG 9w = p ∧ s.REG 10w = p + n2w (k + 1) ∧ s.REG 11w = n2w cnt ∧
    p ∈ forge_prog_addresses ∧
    (∀i. i < 16 ⇒ s.MEM (p + n2w (i + 1)) = EL i frame) ∧
    NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
        n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (∃n' s'.
       n' < n ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
           n' (inp, out ++ DROP k frame, s') (inp_f, out_f, ms_f) ∧
       arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
       bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
       s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧
       (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
    (allow_err ∧
     ∃n' s' chunk.
       n' < n ∧ chunk ≼ DROP k frame ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
           n' (inp, out ++ chunk, s') (inp_f, out_f, ms_f) ∧
       arm8_ok (erase s') ∧ sp_ok s' ∧ shim_loaded s'.MEM ∧
       bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
       s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
       (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))
Proof
  completeInduct_on `n` \\ rpt strip_tac
  \\ Cases_on `cnt = 0`
  >- (
    `k = 16` by decide_tac \\ rveq
    \\ qspecl_then [`s`, `s.REG 9w`] mp_tac ffisend16_loop_done_det \\ impl_tac >- simp [] \\ strip_tac
    \\ peel_nrc_tac
    \\ disj1_tac
    \\ qexists_tac `n - 3` \\ qexists_tac `s'`
    \\ simp [listTheory.DROP_LENGTH_TOO_LONG])
  \\ `1 ≤ cnt` by decide_tac
  \\ qspecl_then [`s`, `p`, `k`, `cnt`] mp_tac ffisend16_loop_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
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
      s_svc.REG 2w = n2w cnt ∧ s_svc.REG 9w = p ∧ s_svc.REG 10w = p + n2w (k + 1) ∧
      s_svc.REG 11w = n2w cnt ∧ s_svc.REG 30w = s.REG 30w` by simp []
  \\ `svc_write_rel s_svc z2 chunk ∧
      (¬allow_err ⇒ svc_write_noerr_rel s_svc z2 chunk)` by
       (Cases_on `allow_err` \\ fs [svc_write_noerr_imp_rel])
  \\ qpat_x_assum `svc_write_rel _ _ _`
       (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_write_rel_def, svc_frame_rel_def])
  \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
      z2.PC = 0x4210ECw ∧ z2.REG 9w = p ∧ z2.REG 10w = p + n2w (k + 1) ∧
      z2.REG 11w = n2w cnt ∧ z2.REG 30w = s.REG 30w ∧ z2.MEM = s.MEM ∧
      shim_loaded z2.MEM ∧
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
    (* Case 1: EINTR (-4w) -> retry at 0x4210D4 with n' < n *)
    qpat_x_assum `chunk = []` SUBST_ALL_TAC
    \\ qpat_x_assum `NRC _ _ (inp, out ++ [], z2) _`
         (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])
    \\ qspec_then `z2` mp_tac ffisend16_post_eintr_det \\ impl_tac >- simp [] \\ strip_tac
    \\ peel_nrc_tac
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `rrel`, `k`, `cnt`, `s'`, `inp`, `out`,
                                `inp_f`, `out_f`, `ms_f`, `ec`, `p`, `frame`] mp_tac)
    \\ impl_tac >- simp []
    \\ strip_tac
    >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''`
        \\ simp [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
    \\ disj2_tac \\ simp [] \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `chunk`
    \\ qpat_x_assum `NRC _ n'' _ _` mp_tac
    \\ simp [] \\ strip_tac \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
  >- (
    (* Case 2: Partial/full write of m bytes (1 ≤ m ≤ cnt) *)
    rename1 `z2.REG 0w = n2w m`
    \\ `m ≤ cnt` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
    \\ `chunk = TAKE m (DROP k frame)` by
         (simp [] \\ irule listTheory.LIST_EQ \\ simp [] \\ rpt strip_tac
          \\ simp [EL_TAKE, EL_DROP, word_add_n2w_right, wordsTheory.word_add_n2w]
          \\ `k + x < 16 ∧ k + 1 + x = k + x + 1` by decide_tac
          \\ qpat_x_assum `∀i. i < 16 ⇒ s.MEM _ = EL i frame` (qspec_then `k + x` mp_tac) \\ simp [])
    \\ qpat_x_assum `chunk = TAKE m (DROP k frame)` SUBST_ALL_TAC
    \\ qspecl_then [`z2`, `p`, `k`, `cnt`, `m`] mp_tac ffisend16_post_ok_det
    \\ impl_tac >- simp []
    \\ strip_tac
    \\ peel_nrc_tac
    \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 7` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `rrel`, `k + m`, `cnt - m`, `s'`, `inp`,
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
  \\ (* Case 3: Write 0 or fatal write error (only possible when allow_err = T!) *)
     `allow_err` by
       (CCONTR_TAC
        \\ `svc_write_noerr_rel s_svc z2 chunk ∧ cnt ≤ 16` by
             (conj_tac >- (qpat_x_assum `¬allow_err ⇒ _` irule \\ simp []) \\ decide_tac)
        \\ mp_tac (Q.SPECL [`s_svc`, `z2`, `chunk`, `cnt`] svc_write_noerr_not_err)
        \\ simp [])
  \\ qpat_x_assum `chunk = []` SUBST_ALL_TAC
  \\ qpat_x_assum `NRC _ _ (inp, out ++ [], z2) _`
       (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])
  \\ qspecl_then [`z2`, `p`] mp_tac ffisend16_post_err_det
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ peel_nrc_tac
  \\ disj2_tac \\ simp []
  \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `[]`
  \\ qpat_x_assum `NRC _ (n' - 7) _ _` mp_tac
  \\ simp [] \\ strip_tac \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp []
QED

Theorem ffisend16_universal:
  ∀allow_err rrel n s inp out inp_f out_f ms_f ec bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFISEND16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
        n (inp, out, s) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 17 ⇒
       ∃n' s'. n' < n ∧
         NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
             n' (inp, out, s') (inp_f, out_f, ms_f) ∧
         ffi_return_ok bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
       (∃n' s'.
          n' < n ∧
          NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
              n' (inp, out ++ TAKE 16 (DROP 1 bytes2), s') (inp_f, out_f, ms_f) ∧
          ffi_return_ok (0w :: DROP 1 bytes2) s s') ∨
       (allow_err ∧
        ∃n' s' chunk.
          n' < n ∧ chunk ≼ TAKE 16 (DROP 1 bytes2) ∧
          NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel))
              n' (inp, out ++ chunk, s') (inp_f, out_f, ms_f) ∧
          ffi_return_ok (1w :: DROP 1 bytes2) s s'))
Proof
  rpt strip_tac
  >- (
    qspecl_then [`s`, `bytes2`] mp_tac ffisend16_short_det \\ impl_tac >- simp [] \\ strip_tac
    \\ peel_nrc_tac
    \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `s.REG 2w = p` by simp [Abbr `p`]
  \\ `p ∈ forge_prog_addresses` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac
        \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspec_then `s` mp_tac ffisend16_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ peel_nrc_tac
  \\ qspecl_then [`n - 6`, `allow_err`, `rrel`, `0`, `16`, `s_loop`, `inp`, `out`,
                  `inp_f`, `out_f`, `ms_f`, `ec`, `p`, `TAKE 16 (DROP 1 bytes2)`] mp_tac
       ffisend16_write_loop_universal
  \\ impl_tac
  >- (simp [] \\ rpt strip_tac
      \\ simp [EL_TAKE, EL_DROP]
      \\ `1 + i = i + 1` by decide_tac
      \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `i + 1` mp_tac) \\ simp [])
  \\ strip_tac
  >- (
    disj1_tac \\ qexists_tac `n'` \\ qexists_tac `s'`
    \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
         (qspecl_then [`p`, `forge_prog_addresses`, `s.MEM`, `bytes2`, `0w`] mp_tac
            asm_write_bytearray_drop1 \\ simp [])
    \\ REWRITE_TAC [ffi_return_ok_def]
    \\ pop_assum SUBST1_TAC
    \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp [])
  \\ disj2_tac \\ simp []
  \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `chunk`
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (qspecl_then [`p`, `forge_prog_addresses`, `s.MEM`, `bytes2`, `1w`] mp_tac
          asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [ffi_return_ok_def]
  \\ pop_assum SUBST1_TAC
  \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ rveq \\ simp []
QED

(* Forward ffisend16 existence under error-free Linux write(1) (for Conjunct 2 liveness) *)
Theorem ffisend16_noerr_exists:
  ∀s bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
    s.PC = FORGE_FFISEND16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 17 ⇒
       ∃s'. (∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
            ffi_return_ok bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
       ∃s'. (∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                           (inp, out, s) (inp, out ++ TAKE 16 (DROP 1 bytes2), s')) ∧
            ffi_return_ok (0w :: DROP 1 bytes2) s s')
Proof
  rpt strip_tac
  >- (qspecl_then [`s`, `bytes2`] mp_tac ffisend16_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `s'` \\ simp []
      \\ metis_tac [det_run_imp_nrc, arithmeticTheory.RTC_eq_NRC])
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `s.REG 2w = p` by simp [Abbr `p`]
  \\ `p ∈ forge_prog_addresses` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_prog_addresses` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac
        \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspec_then `s` mp_tac ffisend16_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ qspecl_then [`s_loop`, `p`, `0`, `16`] mp_tac ffisend16_loop_to_svc_det
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ `GENLIST (λi. s.MEM (p + n2w i + 1w)) 16 = TAKE 16 (DROP 1 bytes2)` by
       (irule listTheory.LIST_EQ \\ simp [] \\ rpt strip_tac
        \\ simp [EL_TAKE, EL_DROP, word_add_n2w_right, wordsTheory.word_add_n2w]
        \\ `1 + x = x + 1` by decide_tac
        \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `x + 1` mp_tac) \\ simp [])
  \\ qabbrev_tac `s_post = s_svc with <|PC := 0x4210ECw; REG := s_svc.REG⦇0w ↦ 16w⦈|>`
  \\ `∀inp out. whole_step svc_read_noerr_rel svc_write_noerr_rel
                  (inp, out, s_svc) (inp, out ++ TAKE 16 (DROP 1 bytes2), s_post)` by
       (rpt gen_tac \\ simp [whole_step_def, Abbr `s_post`, svc_write_noerr_rel_def, svc_frame_rel_def,
                             combinTheory.APPLY_UPDATE_THM]
        \\ conj_tac >- fs [arm8_ok_erase]
        \\ qexists_tac `16` \\ simp [])
  \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by
       (simp [Abbr `s_post`, arm8_ok_erase, sp_ok_def, bits_of_def]
        \\ rpt conj_tac
        \\ TRY (gvs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
        \\ gvs [sp_ok_def, bits_of_def])
  \\ qspecl_then [`s_post`, `p`, `0`, `16`, `16`] mp_tac ffisend16_post_ok_det
  \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
  \\ strip_tac
  \\ qspecl_then [`s'`, `p`] mp_tac ffisend16_loop_done_det
  \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
  \\ strip_tac
  \\ qexists_tac `s''`
  \\ conj_tac
  >- (rpt gen_tac
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out, s_loop)`
      \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out, s_svc)`
      \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out ++ TAKE 16 (DROP 1 bytes2), s_post)`
      \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(inp, out ++ TAKE 16 (DROP 1 bytes2), s')`
      \\ conj_tac >- (irule det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
      \\ irule det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
  \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ pop_assum SUBST1_TAC
        \\ qspecl_then [`p`, `forge_prog_addresses`, `s.MEM`, `bytes2`, `0w`] mp_tac
             asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [ffi_return_ok_def]
  \\ pop_assum SUBST1_TAC
  \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac \\ rveq \\ simp []
QED

(* ---- 9. Parameterized Machine Configuration & Interference Proofs ---- *)

Definition forge_canonical_ffi_post_def:
  forge_canonical_ffi_post (new_bytes:word8 list) (s:arm8_state) : arm8_state =
    s with <| PC := s.REG 30w;
              MEM := asm_write_bytearray (s.REG 2w) new_bytes s.MEM |>
End

Definition mk_real_ffi_if_def:
  mk_real_ffi_if (P : num -> num -> word8 list -> arm8_state -> arm8_state -> bool)
                 (k:num) (index:num, new_bytes:word8 list, s:arm8_state) : arm8_state =
    if ∃s'. P k index new_bytes s s' ∧ ffi_return_ok new_bytes s s' then
      @s'. P k index new_bytes s s' ∧ ffi_return_ok new_bytes s s'
    else
      forge_canonical_ffi_post new_bytes s
End

Definition forge_real_install_if_def:
  forge_real_install_if (k:num) (bytes:word8 list, s:arm8_state) : arm8_state =
    s with <| PC := s.REG 30w;
              REG := (0w =+ s.REG 2w) s.REG;
              MEM := asm_write_bytearray (s.REG 2w) bytes s.MEM |>
End

Theorem forge_mc_with_mmio_min:
  ∀ffi_if inst_if. mmio_pcs_min_index (forge_mc_with ffi_if inst_if).ffi_names = SOME 2
Proof
  rpt gen_tac
  \\ simp [forge_mc_with_def, targetSemTheory.mmio_pcs_min_index_def]
  \\ DEEP_INTRO_TAC optionTheory.some_intro
  \\ conj_tac
  >- (rpt strip_tac \\ `x = 2` suffices_by simp []
      \\ CCONTR_TAC \\ `x < 2` by decide_tac
      \\ first_x_assum (qspec_then `x` mp_tac) \\ simp []
      \\ `x = 0 ∨ x = 1` by decide_tac \\ rveq \\ simp [])
  \\ simp [] \\ qexists_tac `2` \\ simp []
  \\ gen_tac \\ Cases_on `j` \\ simp [] \\ Cases_on `n` \\ simp []
QED

Theorem forge_mc_with_lo55:
  ∀ffi_if inst_if. lo55 (forge_mc_with ffi_if inst_if)
Proof
  rpt gen_tac
  \\ simp [lo55_def, forge_mc_with_def, FORGE_EXIT_VENEER_def, FORGE_INSTALL_VENEER_def,
           FORGE_FFISEND16_VENEER_def, FORGE_FFIRECV16_VENEER_def, untagged_def]
  \\ rpt strip_tac
  >- (drule (cj 5 forge_regions_disjoint) \\ simp [untagged_def])
  \\ rveq \\ EVAL_TAC
QED

Theorem forge_mc_with_start_pc_ok:
  ∀ffi_if inst_if. start_pc_ok (forge_mc_with ffi_if inst_if) FORGE_CAKE_MAIN
Proof
  rpt gen_tac
  \\ simp [targetSemTheory.start_pc_ok_def, forge_mc_with_def,
           FORGE_CAKE_MAIN_def, FORGE_EXIT_VENEER_def, FORGE_INSTALL_VENEER_def,
           FORGE_FFISEND16_VENEER_def, FORGE_FFIRECV16_VENEER_def,
           lab_to_targetTheory.ffi_offset_def]
  \\ rpt conj_tac
  >- (simp [forge_prog_addresses_def, forge_code_region_def, forge_bitmaps_region_def,
            forge_heap_stack_region_def, FORGE_CAKE_MAIN_def, FORGE_CB_END_def,
            FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def, FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ EVAL_TAC)
  >- (simp [forge_prog_addresses_def, forge_code_region_def, forge_bitmaps_region_def,
            forge_heap_stack_region_def, FORGE_CAKE_MAIN_def, FORGE_CB_END_def,
            FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def, FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ EVAL_TAC)
  \\ qexists_tac `2`
  \\ rpt conj_tac
  >- (mp_tac (Q.SPECL [`ffi_if`, `inst_if`] forge_mc_with_mmio_min) \\ simp [forge_mc_with_def])
  >- (gen_tac \\ strip_tac
      \\ `index = 0 ∨ index = 1` by decide_tac \\ rveq
      \\ simp [miscTheory.find_index_def, forge_prog_addresses_def, forge_code_region_def,
               forge_bitmaps_region_def, forge_heap_stack_region_def, FORGE_CAKE_MAIN_def,
               FORGE_CB_END_def, FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def,
               FORGE_HEAP_def, FORGE_STACKEND_def]
      \\ EVAL_TAC)
  \\ rpt strip_tac \\ decide_tac
QED

Theorem mk_real_ffi_if_ok:
  ∀B P. real_interfer_ok B (mk_real_ffi_if P) forge_real_install_if
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ simp [real_interfer_ok_def, LET_THM]
  \\ rpt conj_tac
  >- (
    simp [targetSemTheory.ffi_interfer_ok_def, forge_mc_with_def, arm8_target_def,
          arm8_config_def, mk_real_ffi_if_def]
    \\ rpt gen_tac \\ strip_tac
    \\ `i = 2` by
       (qpat_x_assum `mmio_pcs_min_index _ = SOME i` mp_tac
        \\ mp_tac (Q.SPECL [`ARB`, `ARB`] forge_mc_with_mmio_min)
        \\ simp [forge_mc_with_def])
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
      \\ fs [ffi_return_ok_def, erase_fields, restore_def]
      \\ rpt strip_tac \\ simp [] \\ irule asm_write_bytearray_pointwise \\ simp [])
    \\ simp [forge_canonical_ffi_post_def, erase_fields, arm8_ok_erase, restore_def]
    \\ fs [arm8_ok_def]
    \\ rpt strip_tac \\ irule asm_write_bytearray_pointwise \\ simp [])
  >- (
    simp [targetSemTheory.install_interfer_ok_def, forge_mc_with_def, arm8_target_def,
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
    rpt gen_tac \\ strip_tac \\ simp [mk_real_ffi_if_def]
    \\ IF_CASES_TAC
    >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac []
        \\ rpt strip_tac \\ fs [ffi_return_ok_def])
    \\ simp [forge_canonical_ffi_post_def, bits_of_def] \\ fs [bits_of_def])
  \\ rpt strip_tac \\ simp [forge_real_install_if_def, bits_of_def] \\ fs [bits_of_def]
QED

Theorem real_interfer_ok_imp_erase_ok:
  ∀B ffi_if inst_if.
    real_interfer_ok B ffi_if inst_if ⇒
    ffi_interfer_ok FORGE_CAKE_MAIN (erase_mc B (forge_mc_with ffi_if inst_if)) ∧
    install_interfer_ok FORGE_CAKE_MAIN FORGE_CBSPACE (erase_mc B (forge_mc_with ffi_if inst_if)) ∧
    interference_ok (erase_mc B (forge_mc_with ffi_if inst_if)).next_interfer
      ((erase_mc B (forge_mc_with ffi_if inst_if)).target.proj forge_prog_addresses)
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ simp [real_interfer_ok_def, LET_THM] \\ strip_tac
  \\ rpt conj_tac
  >- (
    simp [targetSemTheory.ffi_interfer_ok_def, erase_mc_def, forge_mc_with_def,
          arm8_target_exact_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ rpt gen_tac \\ strip_tac
    \\ `mmio_pcs_min_index [ExtCall «send16»; ExtCall «recv16»] = SOME 2` by
         (mp_tac (Q.SPECL [`ARB`, `ARB`] forge_mc_with_mmio_min) \\ simp [forge_mc_with_def])
    \\ `i = 2` by fs [] \\ rveq \\ simp []
    \\ strip_tac
    \\ qpat_x_assum `ffi_interfer_ok _ _`
         (mp_tac o Q.SPECL [`ms2`, `k`, `index`, `new_bytes`, `t1`, `bytes`, `bytes2`, `2`] o
          REWRITE_RULE [targetSemTheory.ffi_interfer_ok_def])
    \\ simp [forge_mc_with_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ impl_tac
    >- fs [targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
           asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def,
           arm8_config_def, forge_mc_with_def]
    \\ strip_tac \\ fs [erase_fields]
    \\ `(ffi_if k (index, new_bytes, restore (B0,B1,B2) ms2)).SP_EL0 = ms2.SP_EL0` by
         (qpat_x_assum `∀k i bs s. bits_of s = _ ⇒ _`
            (qspecl_then [`k`, `index`, `new_bytes`, `restore (B0,B1,B2) ms2`] mp_tac)
          \\ simp [bits_of_restore, restore_def])
    \\ qpat_x_assum `target_state_rel _ _ _` mp_tac
    \\ simp [asmPropsTheory.target_state_rel_def]
    \\ rpt strip_tac \\ qpat_x_assum `∀r. _ ⇒ (ffi_if _ _).REG _ = _` irule \\ simp [])
  >- (
    simp [targetSemTheory.install_interfer_ok_def, erase_mc_def, forge_mc_with_def,
          arm8_target_exact_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ rpt gen_tac \\ strip_tac
    \\ qpat_x_assum `install_interfer_ok _ _ _`
         (mp_tac o Q.SPECL [`ms2`, `t1`, `k`, `bytes`] o
          REWRITE_RULE [targetSemTheory.install_interfer_ok_def])
    \\ simp [forge_mc_with_def, arm8_target_def, arm8_config_def, LET_THM]
    \\ impl_tac
    >- gvs [targetSemTheory.read_ffi_bytearray_def, asmPropsTheory.target_state_rel_def,
            arm8_target_exact_def, arm8_target_def, arm8_config_def, forge_mc_with_def]
    \\ strip_tac \\ fs [erase_fields]
    \\ `(inst_if k (bytes, restore (B0,B1,B2) ms2)).SP_EL0 = ms2.SP_EL0` by
         (qpat_x_assum `∀k bs s. bits_of s = _ ⇒ _`
            (qspecl_then [`k`, `bytes`, `restore (B0,B1,B2) ms2`] mp_tac)
          \\ simp [bits_of_restore, restore_def])
    \\ qpat_x_assum `target_state_rel _ _ _` mp_tac
    \\ simp [asmPropsTheory.target_state_rel_def]
    \\ rpt strip_tac \\ qpat_x_assum `∀r. _ ⇒ (inst_if _ _).REG _ = _` irule \\ simp [])
  \\ simp [asmPropsTheory.interference_ok_def, erase_mc_def, forge_mc_with_def]
QED
