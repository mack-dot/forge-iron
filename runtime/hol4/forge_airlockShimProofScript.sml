(*
  Forge Milestone 3 Reusable Runtime: Universal & Liveness ARM64 Syscall Proofs
  for `fficommit` (fd 3, pwrite64(68) + fdatasync(83) crash-atomic durability)
  and `ffibootload` (fd 4 32B key + fd 3 512B dual-slot pread64(67) + zero-fill).
*)
Theory forge_airlockShimProof
Ancestors
  words arithmetic list rich_list combin pred_set relation
  arm8 arm8_step arm8_target targetSem misc alignment
  forge_runtimeSpec forge_airlockFfi forge_airlockContract
  forge_arm8Erasure forge_shimProof forge_airlockShimBase
  forge_airlockShimStart forge_airlockShimIo
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

Theorem m3_slot_off_calc[local]:
  ∀b:word8.
    256w && (w2w b : word64) ⇄ 56 = if (1w && b) = 0w then 0w else 256w
Proof
  gen_tac \\ Cases_on `(1w && b) = 0w` \\ simp [] \\ pop_assum mp_tac \\ blastLib.BBLAST_TAC
QED

Theorem m3_word_bit_63_msb[local]:
  ∀w:word64. word_bit 63 w ⇔ word_msb w
Proof
  blastLib.BBLAST_TAC
QED

Theorem m3_n2w_sub1[local]:
  ∀c. 1 ≤ c ∧ c < 18446744073709551616 ⇒
    (n2w c : word64) + 0xFFFFFFFFFFFFFFFFw = n2w (c - 1)
Proof
  rpt strip_tac
  \\ `0xFFFFFFFFFFFFFFFFw = (-1w:word64)` by EVAL_TAC
  \\ pop_assum SUBST1_TAC
  \\ `n2w c + (-1w:word64) = (n2w c : word64) - n2w 1` by blastLib.BBLAST_TAC
  \\ pop_assum SUBST1_TAC
  \\ mp_tac (Q.SPECL [`c`, `1`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub))
  \\ simp []
QED

Theorem m3_take_pad512_zero_fill[local]:
  ∀disk k c.
    c + k = 512 ∧ k = LENGTH disk ⇒
    TAKE k disk ++ REPLICATE c 0w = pad512 disk
Proof
  rpt strip_tac \\ irule listTheory.LIST_EQ \\ simp [pad512_def]
  \\ rpt strip_tac \\ Cases_on `x < LENGTH disk`
  \\ simp [EL_TAKE, EL_APPEND1, EL_APPEND2, EL_REPLICATE]
QED

Theorem m3_take_512_eq_pad512[local]:
  ∀disk. 512 ≤ LENGTH disk ⇒ TAKE 512 disk = pad512 disk
Proof
  rpt strip_tac \\ simp [pad512_def, TAKE_APPEND1]
QED

Theorem m3_LENGTH_patch_bytes_ge[local]:
  ∀off chunk buf. off + LENGTH chunk ≤ LENGTH (patch_bytes off chunk buf)
Proof
  rpt gen_tac \\ simp [patch_bytes_def] \\ rw []
QED

Theorem m3_bits_of_upds[local]:
  (∀s pc r. bits_of (s with <|PC := pc; REG := r|>) = bits_of s) ∧
  (∀s pc r m. bits_of (s with <|PC := pc; REG := r; MEM := m|>) = bits_of s) ∧
  (∀s m. bits_of (s with MEM := m) = bits_of s)
Proof
  simp [bits_of_def]
QED

Theorem m3_arm8_ok_sp_ok_upds[local]:
  (∀s pc r. arm8_ok (erase s) ∧ aligned 2 pc ⇒ arm8_ok (erase (s with <|PC := pc; REG := r|>))) ∧
  (∀s pc r m. arm8_ok (erase s) ∧ aligned 2 pc ⇒ arm8_ok (erase (s with <|PC := pc; REG := r; MEM := m|>))) ∧
  (∀s pc r. sp_ok s ⇒ sp_ok (s with <|PC := pc; REG := r|>)) ∧
  (∀s pc r m. sp_ok s ⇒ sp_ok (s with <|PC := pc; REG := r; MEM := m|>)) ∧
  (∀s. arm8_ok (erase s) ⇒ s.exception = NoException) ∧
  (∀s m. sp_ok (s with MEM := m) ⇔ sp_ok s) ∧
  (∀s m. arm8_ok (erase (s with MEM := m)) ⇔ arm8_ok (erase s))
Proof
  simp [arm8_ok_erase, sp_ok_def]
QED

(* ---- 1. fficommit (0x400070 -> 0x45011C..0x4501A0, pwrite64(68) + fdatasync(83)) ---- *)

local
  val v_commit    = prove_m3_step "veneer" 28 0
  val c_cmp_258   = prove_m3_step "shim" 71 0
  val c_blo_ge    = prove_m3_step "shim" 72 0
  val c_blo_lt    = prove_m3_step "shim" 72 1
  val c_mov9      = prove_m3_step "shim" 73 0
  val c_ldrb13    = prove_m3_step "shim" 74 0
  val c_and13     = prove_m3_step "shim" 75 0
  val c_lsl13     = prove_m3_step "shim" 76 0
  val c_add10     = prove_m3_step "shim" 77 0
  val c_mov11_256 = prove_m3_step "shim" 78 0
  val c_cbz_nz    = prove_m3_step "shim" 79 0
  val c_cbz_z     = prove_m3_step "shim" 79 1
  val c_mov0      = prove_m3_step "shim" 80 0
  val c_mov1      = prove_m3_step "shim" 81 0
  val c_mov2      = prove_m3_step "shim" 82 0
  val c_mov3      = prove_m3_step "shim" 83 0
  val c_mov8      = prove_m3_step "shim" 84 0
  val c_svc_pw    = prove_m3_svc0_at "shim" 85
  val c_cmn4      = prove_m3_step "shim" 86 0
  val c_beq_ne    = prove_m3_step "shim" 87 0
  val c_beq_eq    = prove_m3_step "shim" 87 1
  val c_cmp0      = prove_m3_step "shim" 88 0
  val c_ble_gt    = prove_m3_step "shim" 89 0
  val c_ble_le    = prove_m3_step "shim" 89 1
  val c_add10_x0  = prove_m3_step "shim" 90 0
  val c_sub11_x0  = prove_m3_step "shim" 91 0
  val c_add13_x0  = prove_m3_step "shim" 92 0
  val c_b_loop    = prove_m3_step "shim" 93 0
  val c_sync_mov0 = prove_m3_step "shim" 94 0
  val c_sync_mov8 = prove_m3_step "shim" 95 0
  val c_svc_fs    = prove_m3_svc0_at "shim" 96
  val c_s_cmn4    = prove_m3_step "shim" 97 0
  val c_s_beq_ne  = prove_m3_step "shim" 98 0
  val c_s_beq_eq  = prove_m3_step "shim" 98 1
  val c_s_cbnz_nz = prove_m3_step "shim" 99 0
  val c_s_cbnz_z  = prove_m3_step "shim" 99 1
  val c_strb_0    = prove_m3_step "shim" 100 0
  val c_ret_ok    = prove_m3_step "shim" 101 0
  val c_mov12_1   = prove_m3_step "shim" 102 0
  val c_strb_1    = prove_m3_step "shim" 103 0
  val c_ret_err   = prove_m3_step "shim" 104 0

  val commit_short_det = prove(
    ``∀cb_begin cb_end bm_buf_end s bytes2.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFICOMMIT_VENEER ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        read_bytearray (s.REG 2w) (w2n (s.REG 3w))
          (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
        w2n (s.REG 3w) < 258 ⇒
        ∃s'. det_run 4 s s' ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s'``,
    rpt strip_tac
    \\ `s.PC = 0x400070w` by fs [FORGE_M3_FFICOMMIT_VENEER_def]
    \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by (irule asm_write_bytearray_id \\ metis_tac [])
    \\ qexists_tac `s with <|PC := s.REG 30w;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551357 + 1)));
                                 C := F;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFEFEw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFEFEw)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det v_commit \\ step_m3_det c_cmp_258 \\ step_m3_det c_blo_lt \\ step_m3_det c_ret_err
        \\ simp [det_run_def, cmp_carry_258, arm8Theory.arm8_state_component_equality])
    \\ simp [m3_ffi_return_ok_slot_def, arm8_ok_erase, sp_ok_def, bits_of_def]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val commit_entry_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (sel:word8).
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFICOMMIT_VENEER ∧ 258 ≤ w2n (s.REG 3w) ∧
        s.MEM (s.REG 2w + 1w) = sel ⇒
        ∃s_loop.
          det_run 9 s s_loop ∧ arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_loop.MEM ∧
          bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
          s_loop.PC = 0x45013Cw ∧ s_loop.MEM = s.MEM ∧
          s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = s.REG 2w + 2w ∧
          s_loop.REG 11w = 256w ∧
          s_loop.REG 13w = (if (sel && 1w) = 0w then 0w else 256w) ∧
          s_loop.REG 30w = s.REG 30w ∧
          (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))``,
    rpt strip_tac
    \\ `s.PC = 0x400070w` by fs [FORGE_M3_FFICOMMIT_VENEER_def]
    \\ qabbrev_tac `p = s.REG 2w`
    \\ qexists_tac `s with <|PC := 0x45013Cw;
                             REG := s.REG⦇9w ↦ p; 10w ↦ p + 2w; 11w ↦ 256w;
                                          13w ↦ if (sel && 1w) = 0w then 0w else 256w⦈;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551357 + 1)));
                                 C := T;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFEFEw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFEFEw)|>;
                             branch_hint := NONE|>`
    \\ conj_tac
    >- (step_m3_det v_commit \\ step_m3_det c_cmp_258 \\ step_m3_det c_blo_ge \\ step_m3_det c_mov9
        \\ step_m3_det c_ldrb13 \\ step_m3_det c_and13 \\ step_m3_det c_lsl13
        \\ step_m3_det c_add10 \\ step_m3_det c_mov11_256
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, Abbr `p`, cmp_carry_258, m3_slot_off_calc,
              arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
              combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [] \\ blastLib.BBLAST_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val commit_loop_to_sync_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x45013Cw ∧ s.REG 11w = 0w ⇒
        ∃s_sync. det_run 1 s s_sync ∧ arm8_ok (erase s_sync) ∧ sp_ok s_sync ∧
                 m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_sync.MEM ∧
                 bits_of s_sync = bits_of s ∧ s_sync.SP_EL0 = s.SP_EL0 ∧
                 s_sync.PC = 0x450178w ∧ s_sync.MEM = s.MEM ∧ s_sync.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x450178w; branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det c_cbz_z \\ simp [det_run_def, arm8Theory.arm8_state_component_equality])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val commit_loop_to_svc_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64) boff k c.
        1 ≤ c ∧ c + k = 256 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x45013Cw ∧ s.REG 10w = p + n2w (k + 2) ∧
        s.REG 11w = n2w c ∧ s.REG 13w = n2w (boff + k) ⇒
        ∃s_svc.
          det_run 6 s s_svc ∧ arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_svc.MEM ∧
          bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
          s_svc.PC = 0x450154w ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
          s_svc.REG 0w = 3w ∧ s_svc.REG 1w = p + n2w (k + 2) ∧
          s_svc.REG 2w = n2w c ∧ s_svc.REG 3w = n2w (boff + k) ∧ s_svc.REG 8w = 68w ∧
          (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 3w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
    rpt strip_tac
    \\ qabbrev_tac `s_svc = s with <|PC := 0x450154w;
                                     REG := s.REG⦇0w ↦ 3w; 1w ↦ p + n2w (k + 2);
                                                  2w ↦ n2w c; 3w ↦ n2w (boff + k); 8w ↦ 68w⦈;
                                     branch_hint := NONE|>`
    \\ qexists_tac `s_svc`
    \\ conj_tac
    >- (step_m3_det c_cbz_nz \\ step_m3_det c_mov0 \\ step_m3_det c_mov1
        \\ step_m3_det c_mov2 \\ step_m3_det c_mov3 \\ step_m3_det c_mov8
        \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `is_svc0_at s_svc` by (irule c_svc_pw \\ simp [Abbr `s_svc`] \\ metis_tac [])
    \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val commit_pw_eintr_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450158w ∧ s.REG 0w = -4w ⇒
        ∃s'. det_run 2 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x45013Cw ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x45013Cw; PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det c_cmn4 \\ step_m3_det c_beq_eq
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val commit_pw_err_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450158w ∧ s.REG 9w = p ∧
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
    >- (step_m3_det c_cmn4 \\ step_m3_det c_beq_ne \\ step_m3_det c_cmp0 \\ step_m3_det c_ble_le
        \\ step_m3_det c_mov12_1 \\ step_m3_det c_strb_1 \\ step_m3_det c_ret_err
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
              arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val commit_pw_ok_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64) boff k c m.
        1 ≤ m ∧ m ≤ c ∧ c + k = 256 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450158w ∧ s.REG 0w = n2w m ∧
        s.REG 10w = p + n2w (k + 2) ∧ s.REG 11w = n2w c ∧ s.REG 13w = n2w (boff + k) ⇒
        ∃s'. det_run 8 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x45013Cw ∧ s'.MEM = s.MEM ∧
             s'.REG 10w = p + n2w (k + m + 2) ∧ s'.REG 11w = n2w (c - m) ∧
             s'.REG 13w = n2w (boff + (k + m)) ∧
             (∀r. r ≠ 10w ∧ r ≠ 11w ∧ r ≠ 13w ⇒ s'.REG r = s.REG r)``,
    rpt strip_tac
    \\ `¬word_msb (n2w m : word64) ∧ (n2w m : word64) ≠ 0w ∧ (n2w m : word64) ≠ -4w` by
       (simp [wordsTheory.word_msb_n2w, wordsTheory.n2w_11, dimword_64]
        \\ `¬BIT 63 m` by (irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
        \\ `(-4w:word64) = n2w 18446744073709551612` by EVAL_TAC
        \\ simp [wordsTheory.n2w_11, dimword_64])
    \\ `-1w * (n2w m : word64) + n2w c = n2w (c - m)` by
       (ONCE_REWRITE_TAC [cj 1 m3_word64_arith_step_helpers]
        \\ mp_tac (Q.SPECL [`c`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub)) \\ simp [])
    \\ `(n2w m : word64) + (p + n2w (k + 2)) = p + n2w (k + m + 2)` by
       (ONCE_REWRITE_TAC [cj 2 m3_word64_arith_step_helpers] \\ simp [wordsTheory.word_add_n2w])
    \\ `(n2w m : word64) + n2w (boff + k) = n2w (boff + (k + m))` by
       (simp [wordsTheory.word_add_n2w] \\ AP_TERM_TAC \\ decide_tac)
    \\ qexists_tac `s with <|PC := 0x45013Cw;
                             REG := s.REG⦇10w ↦ p + n2w (k + m + 2); 11w ↦ n2w (c - m);
                                          13w ↦ n2w (boff + (k + m))⦈;
                             PSTATE := s.PSTATE with
                               <|V := F;
                                 C := ((if w2n (n2w m:word64) + 18446744073709551615 + 1 < 18446744073709551616
                                        then w2n (n2w m:word64) + 18446744073709551615 + 1
                                        else (w2n (n2w m:word64) + 18446744073709551615 + 1) MOD 18446744073709551616) ≠
                                       w2n (n2w m:word64) + 18446744073709551615 + 1);
                                 Z := F; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det c_cmn4 \\ step_m3_det c_beq_ne \\ step_m3_det c_cmp0 \\ step_m3_det c_ble_gt
        \\ step_m3_det c_add10_x0 \\ step_m3_det c_sub11_x0 \\ step_m3_det c_add13_x0 \\ step_m3_det c_b_loop
        \\ simp [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
                 arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ `aligned 2 (0x45013Cw:word64)` by EVAL_TAC
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val commit_sync_to_svc_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450178w ⇒
        ∃s_svc.
          det_run 2 s s_svc ∧ arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_svc.MEM ∧
          bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
          s_svc.PC = 0x450180w ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
          s_svc.REG 0w = 3w ∧ s_svc.REG 8w = 83w ∧
          (∀r. r ≠ 0w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
    rpt strip_tac
    \\ qabbrev_tac `s_svc = s with <|PC := 0x450180w; REG := s.REG⦇0w ↦ 3w; 8w ↦ 83w⦈; branch_hint := NONE|>`
    \\ qexists_tac `s_svc`
    \\ conj_tac
    >- (step_m3_det c_sync_mov0 \\ step_m3_det c_sync_mov8
        \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `is_svc0_at s_svc` by (irule c_svc_fs \\ simp [Abbr `s_svc`] \\ metis_tac [])
    \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val commit_sync_eintr_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450184w ∧ s.REG 0w = -4w ⇒
        ∃s'. det_run 2 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x450178w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x450178w; PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det c_s_cmn4 \\ step_m3_det c_s_beq_eq
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val commit_sync_ok_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450184w ∧ s.REG 0w = 0w ∧ s.REG 9w = p ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒
        ∃s'. det_run 5 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ `p ∉ forge_m3_shim_code_region` by simp []
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 0w⦈)` by simp [m3_shim_loaded_slot_update]
    \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 0w⦈; PC := s.REG 30w;
                             PSTATE := s.PSTATE with <|V := F; C := F; Z := F; N := F|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det c_s_cmn4 \\ step_m3_det c_s_beq_ne \\ step_m3_det c_s_cbnz_z
        \\ step_m3_det c_strb_0 \\ step_m3_det c_ret_ok
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def])

  val commit_sync_err_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450184w ∧ s.REG 0w ≠ 0w ∧ s.REG 0w ≠ -4w ∧ s.REG 9w = p ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒
        ∃s'. det_run 6 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
             (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)``,
    rpt strip_tac
    \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ `p ∉ forge_m3_shim_code_region` by simp []
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 1w⦈)` by simp [m3_shim_loaded_slot_update]
    \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 1w⦈; PC := s.REG 30w; REG := s.REG⦇12w ↦ 1w⦈;
                             PSTATE := s.PSTATE with
                               <|V := ((word_msb (s.REG 0w) ⇔ F) ∧
                                       (word_msb (s.REG 0w) ⇎ BIT 63 (w2n (s.REG 0w) + 4)));
                                 C := ((if w2n (s.REG 0w) + 4 < 18446744073709551616
                                        then w2n (s.REG 0w) + 4
                                        else (w2n (s.REG 0w) + 4) MOD 18446744073709551616) ≠
                                       w2n (s.REG 0w) + 4);
                                 Z := (s.REG 0w + 4w = 0w); N := word_msb (s.REG 0w + 4w)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det c_s_cmn4 \\ step_m3_det c_s_beq_ne \\ step_m3_det c_s_cbnz_nz
        \\ step_m3_det c_mov12_1 \\ step_m3_det c_strb_1 \\ step_m3_det c_ret_err
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
              combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val commit_sync_universal = prove(
    ``∀n allow_err cb_begin cb_end bm_buf_end s os os_f ms_f ec (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450178w ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f ⇒
        (∃n' s'.
           n' < n ∧
           NRC (m3_whole_step allow_err) n' (os with durable := os.disk, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
        (allow_err ∧
         ∃n' s'.
           n' < n ∧
           NRC (m3_whole_step allow_err) n' (os, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
    completeInduct_on `n` \\ rpt strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac commit_sync_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ Cases_on `n - 2` >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, cj 6 m3_whole_step_svc_det]
    \\ rpt strip_tac \\ qpat_x_assum `_ = os with durable := _` SUBST_ALL_TAC
    \\ rename1 `NRC _ _ (os with durable := dur', z2) _`
    \\ qpat_x_assum `svc_fdatasync_rel _ _ _ _ _ _`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_fdatasync_rel_def, svc_frame_rel_def])
    \\ `s_svc.REG 9w = p ∧ s_svc.REG 30w = s.REG 30w` by simp []
    \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
        z2.PC = 0x450184w ∧ z2.REG 9w = p ∧ z2.REG 30w = s.REG 30w ∧
        (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
         (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY (fs [bits_of_def] \\ NO_TAC)
          \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ qpat_x_assum `_ ∨ _ ∨ _`
         (DISJ_CASES_THEN2 strip_assume_tac
           (DISJ_CASES_THEN2 (REPEAT_TCL CONJUNCTS_THEN assume_tac) strip_assume_tac))
    >- (
      `os with durable := dur' = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac commit_sync_eintr_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac) \\ impl_tac >- decide_tac
      \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `os`, `os_f`, `ms_f`, `ec`, `p`] mp_tac)
      \\ impl_tac >- simp [] \\ strip_tac
      >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ conj_tac >- simp [] \\ qexists_tac `n''` \\ qexists_tac `s''`
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      qpat_x_assum `dur' = os.disk` SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac commit_sync_ok_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj1_tac \\ qexists_tac `n' - 5` \\ qexists_tac `s'`
      \\ simp [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `os with durable := dur' = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac commit_sync_err_det \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ disj2_tac \\ simp [] \\ qexists_tac `n' - 6` \\ qexists_tac `s'`
    \\ qpat_x_assum `NRC _ _ _ _` mp_tac
    \\ simp [] \\ disch_then (K ALL_TAC) \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])

  val commit_pw_loop_universal = prove(
    ``∀n allow_err cb_begin cb_end bm_buf_end boff k c s os os_f ms_f ec (p:word64) (rec:word8 list).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        (boff = 0 ∨ boff = 256) ∧ c + k = 256 ∧ LENGTH rec = 256 ∧
        (k = 0 ∨ boff + k ≤ LENGTH os.disk) ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x45013Cw ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ s.REG 10w = p + n2w (k + 2) ∧ s.REG 11w = n2w c ∧ s.REG 13w = n2w (boff + k) ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        (∀i. i < 256 ⇒ s.MEM (p + n2w (i + 2)) = EL i rec) ∧
        NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f ⇒
        (∃n' s'.
           n' < n ∧
           let d' = patch_bytes (boff + k) (DROP k rec) os.disk in
             NRC (m3_whole_step allow_err) n' (os with <| disk := d'; durable := d' |>, s') (os_f, ms_f) ∧
             arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 0w⦈ ∧
             (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
        (allow_err ∧
         ∃n' s' d'.
           n' < n ∧
           NRC (m3_whole_step allow_err) n' (os with disk := d', s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
    completeInduct_on `n` \\ rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
    \\ `boff ≤ 256` by (qpat_assum `boff = 0 ∨ boff = 256` strip_assume_tac \\ decide_tac)
    \\ Cases_on `c = 0`
    >- (
      `k = 256` by decide_tac \\ pop_assum SUBST_ALL_TAC
      \\ `boff + 256 ≤ LENGTH os.disk` by (qpat_assum `256 = 0 ∨ _` mp_tac \\ simp [])
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac commit_loop_to_sync_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qspecl_then [`n - 1`, `allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`, `s_sync`, `os`, `os_f`, `ms_f`, `ec`, `p`]
           mp_tac commit_sync_universal
      \\ impl_tac >- simp [] \\ strip_tac
      >- (
        disj1_tac \\ qexists_tac `n'` \\ qexists_tac `s'` \\ simp [LET_THM, listTheory.DROP_LENGTH_TOO_LONG, patch_bytes_nil]
        \\ `os with <|disk := os.disk; durable := os.disk|> = os with durable := os.disk` by simp [m3_os_component_equality]
        \\ simp [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ conj_tac >- simp [] \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `os.disk`
      \\ `os with disk := os.disk = os` by simp [m3_os_component_equality]
      \\ qpat_x_assum `NRC _ n' _ _` mp_tac
      \\ simp [] \\ disch_then (K ALL_TAC) \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `1 ≤ c` by decide_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `p`, `boff`, `k`, `c`] mp_tac commit_loop_to_svc_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ Cases_on `n - 6` >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, cj 5 m3_whole_step_svc_det]
    \\ rpt strip_tac \\ qpat_x_assum `_ = os with disk := _` SUBST_ALL_TAC
    \\ rename1 `NRC _ _ (os with disk := disk', z2) _`
    \\ qpat_x_assum `svc_pwrite64_rel _ _ _ _ _`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_pwrite64_rel_def, svc_frame_rel_def, LET_THM])
    \\ `s_svc.REG 9w = p ∧ s_svc.REG 10w = p + n2w (k + 2) ∧
        s_svc.REG 11w = n2w c ∧ s_svc.REG 13w = n2w (boff + k) ∧ s_svc.REG 30w = s.REG 30w` by simp []
    \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
        z2.PC = 0x450158w ∧ z2.REG 9w = p ∧ z2.REG 10w = p + n2w (k + 2) ∧
        z2.REG 11w = n2w c ∧ z2.REG 13w = n2w (boff + k) ∧ z2.REG 30w = s.REG 30w ∧
        (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
         (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY (fs [bits_of_def] \\ NO_TAC)
          \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ qpat_x_assum `_ ∨ _ ∨ _`
         (DISJ_CASES_THEN2 strip_assume_tac
           (DISJ_CASES_THEN2 (REPEAT_TCL CONJUNCTS_THEN assume_tac) strip_assume_tac))
    >- (
      `os with disk := disk' = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac commit_pw_eintr_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac) \\ impl_tac >- decide_tac
      \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`, `boff`, `k`, `c`,
                                  `s'`, `os`, `os_f`, `ms_f`, `ec`, `p`, `rec`] mp_tac)
      \\ impl_tac >- simp [] \\ strip_tac
      >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ fs [LET_THM] \\ rfs []
          \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ simp [] \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `d'`
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      `os with disk := disk' = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac commit_pw_err_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj2_tac \\ simp [] \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `os.disk`
      \\ `os with disk := os.disk = os` by simp [m3_os_component_equality]
      \\ qpat_x_assum `NRC _ _ _ _` mp_tac
      \\ simp [] \\ disch_then (K ALL_TAC) \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ rename1 `z2.REG 0w = n2w m`
    \\ `m ≤ c` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
    \\ `w2n (s_svc.REG 3w) = boff + k` by simp [wordsTheory.w2n_n2w, dimword_64]
    \\ `GENLIST (λi. s_svc.MEM (n2w i + s_svc.REG 1w)) m = TAKE m (DROP k rec)` by (
         irule listTheory.LIST_EQ \\ simp [] \\ rpt strip_tac
         \\ simp [EL_TAKE, EL_DROP, m3_word_add_n2w_right]
         \\ `x + (k + 2) = k + (x + 2)` by decide_tac \\ pop_assum SUBST1_TAC
         \\ qpat_x_assum `∀i. i < 256 ⇒ s.MEM _ = _` (qspec_then `k + x` mp_tac) \\ simp [])
    \\ `disk' = patch_bytes (boff + k) (TAKE m (DROP k rec)) os.disk` by
         (qpat_assum `disk' = patch_bytes _ _ _` SUBST1_TAC \\ simp [])
    \\ `boff + (k + m) ≤ LENGTH (patch_bytes (boff + k) (TAKE m (DROP k rec)) os.disk)` by (
         mp_tac (Q.SPECL [`boff + k`, `TAKE m (DROP k rec)`, `os.disk`] m3_LENGTH_patch_bytes_ge)
         \\ simp [])
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`, `boff`, `k`, `c`, `m`] mp_tac commit_pw_ok_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 8` mp_tac) \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`, `boff`, `k + m`, `c - m`,
                                `s'`, `os with disk := disk'`, `os_f`, `ms_f`, `ec`, `p`, `rec`] mp_tac)
    \\ impl_tac >- simp [] \\ strip_tac
    >- (
      qpat_x_assum `let d' = _ in _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])
      \\ qpat_x_assum `NRC _ n'' _ _` mp_tac
      \\ simp []
      \\ `patch_bytes (boff + (k + m)) (DROP (k + m) rec) (patch_bytes (boff + k) (TAKE m (DROP k rec)) os.disk) =
          patch_bytes (boff + k) (DROP k rec) os.disk` by (
            `boff + (k + m) = (boff + k) + LENGTH (TAKE m (DROP k rec))` by simp []
            \\ pop_assum SUBST1_TAC
            \\ REWRITE_TAC [patch_bytes_append, m3_take_drop_add]
            \\ simp [])
      \\ pop_assum SUBST1_TAC \\ strip_tac
      \\ disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''`
      \\ simp [LET_THM]
      \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ qpat_x_assum `NRC _ n'' _ _` mp_tac \\ simp [] \\ strip_tac
    \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `d'`
    \\ qpat_x_assum `NRC _ n'' _ _` mp_tac \\ simp [] \\ disch_then (K ALL_TAC)
    \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
in

Theorem m3_fficommit_universal_slot:
  ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFICOMMIT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 258 ⇒
       ∃n' s'. n' < n ∧
         NRC (m3_whole_step allow_err) n' (os, s') (os_f, ms_f) ∧
         m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (258 ≤ w2n (s.REG 3w) ⇒
       let sel = EL 1 bytes2 in
       let boff = if (sel && 1w) = 0w then 0 else 256 in
       let rec = TAKE 256 (DROP 2 bytes2) in
       let d' = patch_bytes boff rec os.disk in
       (∃n' s'.
          n' < n ∧
          NRC (m3_whole_step allow_err) n' (os with <| disk := d'; durable := d' |>, s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w :: DROP 1 bytes2) s s') ∨
       (allow_err ∧
        ∃n' s' d_tmp.
          n' < n ∧
          NRC (m3_whole_step allow_err) n' (os with disk := d_tmp, s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s'))
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac commit_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
  \\ simp [LET_THM]
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ `s.MEM (p + 1w) = EL 1 bytes2` by
       (qpat_assum `∀i. i < _ ⇒ s.MEM _ = _` (mp_tac o Q.SPEC `1`)
        \\ impl_tac >- decide_tac \\ simp [])
  \\ qabbrev_tac `sel = EL 1 bytes2`
  \\ qabbrev_tac `boff = if (1w && sel) = 0w then 0 else 256`
  \\ qabbrev_tac `rec = TAKE 256 (DROP 2 bytes2)`
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `sel`] mp_tac commit_entry_det
  \\ impl_tac >- simp [Abbr `p`] \\ strip_tac
  \\ m3_peel_nrc_tac
  \\ `s_loop.REG 9w = p ∧ s_loop.REG 10w = p + 2w` by simp [Abbr `p`]
  \\ `s_loop.REG 13w = n2w (boff + 0)` by (Cases_on `1w && sel = 0w` \\ simp [Abbr `boff`])
  \\ qspecl_then [`n - 9`, `allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                  `boff`, `0`, `256`, `s_loop`, `os`, `os_f`, `ms_f`, `ec`, `p`, `rec`]
       mp_tac commit_pw_loop_universal
  \\ impl_tac
  >- (simp [Abbr `rec`]
      \\ conj_tac >- (Cases_on `1w && sel = 0w` \\ simp [Abbr `boff`])
      \\ rpt strip_tac \\ simp [EL_TAKE, EL_DROP] \\ `2 + i = i + 2` by decide_tac
      \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `i + 2` mp_tac) \\ simp [])
  \\ strip_tac
  >- (
    qpat_x_assum `let d' = _ in _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])
    \\ disj1_tac \\ qexists_tac `n'` \\ qexists_tac `s'`
    \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
          \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `0w`]
               mp_tac asm_write_bytearray_drop1 \\ simp [])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
    \\ simp [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ disj2_tac \\ conj_tac >- simp [] \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `d'`
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
        \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`]
             mp_tac asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
  \\ qpat_x_assum `NRC _ n' _ _` mp_tac \\ simp [] \\ disch_then (K ALL_TAC)
  \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

Theorem m3_fficommit_noerr_exists_slot:
  ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFICOMMIT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 258 ⇒
       ∃s'. (∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (258 ≤ w2n (s.REG 3w) ⇒
       let sel = EL 1 bytes2 in
       let boff = if (sel && 1w) = 0w then 0 else 256 in
       let rec = TAKE 256 (DROP 2 bytes2) in
       ∃s'.
         (∀os. let d' = patch_bytes boff rec os.disk in
                 RTC (m3_whole_step F) (os, s) (os with <| disk := d'; durable := d' |>, s')) ∧
         m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w :: DROP 1 bytes2) s s')
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac commit_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `s'` \\ simp [] \\ metis_tac [m3_det_run_imp_rtc])
  \\ simp [LET_THM]
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ `s.MEM (p + 1w) = EL 1 bytes2` by
       (qpat_assum `∀i. i < _ ⇒ s.MEM _ = _` (mp_tac o Q.SPEC `1`) \\ impl_tac >- decide_tac \\ simp [])
  \\ qabbrev_tac `sel = EL 1 bytes2`
  \\ qabbrev_tac `boff = if (1w && sel) = 0w then 0 else 256`
  \\ qabbrev_tac `rec = TAKE 256 (DROP 2 bytes2)`
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `sel`] mp_tac commit_entry_det
  \\ impl_tac >- simp [Abbr `p`] \\ strip_tac
  \\ `s_loop.REG 9w = p ∧ s_loop.REG 10w = p + 2w` by simp [Abbr `p`]
  \\ `s_loop.REG 13w = n2w (boff + 0)` by (Cases_on `1w && sel = 0w` \\ simp [Abbr `boff`])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `p`, `boff`, `0`, `256`] mp_tac commit_loop_to_svc_det
  \\ impl_tac >- simp [] \\ strip_tac
  \\ `GENLIST (λi. s.MEM (p + n2w i + 2w)) 256 = rec` by (
       irule listTheory.LIST_EQ \\ simp [Abbr `rec`] \\ rpt strip_tac
       \\ simp [EL_TAKE, EL_DROP, m3_word_add_n2w_right, wordsTheory.word_add_n2w]
       \\ `2 + x = x + 2` by decide_tac
       \\ qpat_x_assum `∀i. i < _ ⇒ s.MEM _ = _` (qspec_then `x + 2` mp_tac) \\ simp [])
  \\ `w2n (s_svc.REG 3w) = boff` by (Cases_on `1w && sel = 0w` \\ simp [Abbr `boff`, wordsTheory.w2n_n2w, dimword_64])
  \\ qabbrev_tac `s_post = s_svc with <|PC := 0x450158w; REG := s_svc.REG⦇0w ↦ 256w⦈|>`
  \\ `∀os. m3_whole_step F (os, s_svc) (os with disk := patch_bytes boff rec os.disk, s_post)` by (
       gen_tac \\ `s_svc.exception = NoException` by (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
       \\ simp [m3_whole_step_def, Abbr `s_post`, svc_pwrite64_rel_def, svc_frame_rel_def,
                combinTheory.APPLY_UPDATE_THM, LET_THM]
       \\ qexists_tac `patch_bytes boff rec os.disk` \\ simp []
       \\ qexists_tac `256` \\ simp [])
  \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by (
       simp [Abbr `s_post`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
       \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `p`, `boff`, `0`, `256`, `256`] mp_tac commit_pw_ok_det
  \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`] mp_tac commit_loop_to_sync_det
  \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_sync`] mp_tac commit_sync_to_svc_det
  \\ impl_tac >- simp [] \\ strip_tac
  \\ qabbrev_tac `s_fs = s_svc' with <|PC := 0x450184w; REG := s_svc'.REG⦇0w ↦ 0w⦈|>`
  \\ `∀os. m3_whole_step F (os, s_svc') (os with durable := os.disk, s_fs)` by (
       gen_tac \\ `s_svc'.exception = NoException` by (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
       \\ simp [m3_whole_step_def, Abbr `s_fs`, svc_fdatasync_rel_def, svc_frame_rel_def,
                combinTheory.APPLY_UPDATE_THM]
       \\ qexists_tac `os.disk` \\ simp [])
  \\ `arm8_ok (erase s_fs) ∧ sp_ok s_fs ∧ bits_of s_fs = bits_of s ∧ s_fs.SP_EL0 = s.SP_EL0` by (
       simp [Abbr `s_fs`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
       \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_fs`, `p`] mp_tac commit_sync_ok_det
  \\ impl_tac >- simp [Abbr `s_fs`, Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qexists_tac `s''`
  \\ conj_tac
  >- (gen_tac
      \\ qabbrev_tac `os1 = os with disk := patch_bytes boff rec os.disk`
      \\ `os1 with durable := os1.disk = os with <|disk := patch_bytes boff rec os.disk; durable := patch_bytes boff rec os.disk|>`
           by simp [Abbr `os1`, m3_os_component_equality]
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `9` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os1, s_post)`
      \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [Abbr `os1`])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os1, s')`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `8` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os1, s_sync)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `1` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os1, s_svc')`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `2` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os1 with durable := os1.disk, s_fs)`
      \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
      \\ pop_assum (fn th => REWRITE_TAC [GSYM th])
      \\ irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
  \\ `asm_write_bytearray (s.REG 2w) (0w :: DROP 1 bytes2) s.MEM = (p =+ 0w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
        \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `0w`]
             mp_tac asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
  \\ simp [Abbr `s_fs`, Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
  \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

end;

(* ---- 2. ffibootload (0x4000A0 -> 0x4501A4..0x450278, fd 4 32B key + fd 3 512B pread64) ---- *)

local
  val v_boot       = prove_m3_step "veneer" 40 0
  val b_cmp_545    = prove_m3_step "shim" 105 0
  val b_blo_ge     = prove_m3_step "shim" 106 0
  val b_blo_lt     = prove_m3_step "shim" 106 1
  val b_mov9       = prove_m3_step "shim" 107 0
  val b_adrp10     = prove_m3_step "shim" 108 0
  val b_add10      = prove_m3_step "shim" 109 0
  val b_mov11_32   = prove_m3_step "shim" 110 0
  val b_k_cbz_nz   = prove_m3_step "shim" 111 0
  val b_k_cbz_z    = prove_m3_step "shim" 111 1
  val b_k_mov0     = prove_m3_step "shim" 112 0
  val b_k_mov1     = prove_m3_step "shim" 113 0
  val b_k_mov2     = prove_m3_step "shim" 114 0
  val b_k_mov8     = prove_m3_step "shim" 115 0
  val b_k_svc      = prove_m3_svc0_at "shim" 116
  val b_k_cmn4     = prove_m3_step "shim" 117 0
  val b_k_beq_ne   = prove_m3_step "shim" 118 0
  val b_k_beq_eq   = prove_m3_step "shim" 118 1
  val b_k_cmp0     = prove_m3_step "shim" 119 0
  val b_k_ble_gt   = prove_m3_step "shim" 120 0
  val b_k_ble_le   = prove_m3_step "shim" 120 1
  val b_k_add10    = prove_m3_step "shim" 121 0
  val b_k_sub11    = prove_m3_step "shim" 122 0
  val b_k_bloop    = prove_m3_step "shim" 123 0
  val b_d_mov11    = prove_m3_step "shim" 124 0
  val b_d_mov13    = prove_m3_step "shim" 125 0
  val b_d_cbz_nz   = prove_m3_step "shim" 126 0
  val b_d_cbz_z    = prove_m3_step "shim" 126 1
  val b_d_mov0     = prove_m3_step "shim" 127 0
  val b_d_mov1     = prove_m3_step "shim" 128 0
  val b_d_mov2     = prove_m3_step "shim" 129 0
  val b_d_mov3     = prove_m3_step "shim" 130 0
  val b_d_mov8     = prove_m3_step "shim" 131 0
  val b_d_svc      = prove_m3_svc0_at "shim" 132
  val b_d_cmn4     = prove_m3_step "shim" 133 0
  val b_d_beq_ne   = prove_m3_step "shim" 134 0
  val b_d_beq_eq   = prove_m3_step "shim" 134 1
  val b_d_cbz0_nz  = prove_m3_step "shim" 135 0
  val b_d_cbz0_z   = prove_m3_step "shim" 135 1
  val b_d_tbnz_ok  = prove_m3_step "shim" 136 0
  val b_d_tbnz_err = prove_m3_step "shim" 136 1
  val b_d_add10    = prove_m3_step "shim" 137 0
  val b_d_sub11    = prove_m3_step "shim" 138 0
  val b_d_add13    = prove_m3_step "shim" 139 0
  val b_d_bloop    = prove_m3_step "shim" 140 0
  val b_z_cbz_nz   = prove_m3_step "shim" 141 0
  val b_z_cbz_z    = prove_m3_step "shim" 141 1
  val b_z_strb0    = prove_m3_step "shim" 142 0
  val b_z_add10    = prove_m3_step "shim" 143 0
  val b_z_sub11    = prove_m3_step "shim" 144 0
  val b_z_bloop    = prove_m3_step "shim" 145 0
  val b_c_adrp12   = prove_m3_step "shim" 146 0
  val b_c_add12    = prove_m3_step "shim" 147 0
  val b_c_mov11_0  = prove_m3_step "shim" 148 0
  val b_c_ldrb     = prove_m3_step "shim" 149 0
  val b_c_add11    = prove_m3_step "shim" 150 0
  val b_c_strb     = prove_m3_step "shim" 151 0
  val b_c_cmp_544  = prove_m3_step "shim" 152 0
  val b_c_blo_done = prove_m3_step "shim" 153 0
  val b_c_blo_more = prove_m3_step "shim" 153 1
  val b_c_strb_0   = prove_m3_step "shim" 154 0
  val b_c_ret_ok   = prove_m3_step "shim" 155 0
  val b_mov12_1    = prove_m3_step "shim" 156 0
  val b_strb_1     = prove_m3_step "shim" 157 0
  val b_ret_err    = prove_m3_step "shim" 158 0

  val boot_short_det = prove(
    ``∀cb_begin cb_end bm_buf_end s bytes2.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFIBOOT_VENEER ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        read_bytearray (s.REG 2w) (w2n (s.REG 3w))
          (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
        w2n (s.REG 3w) < 545 ⇒
        ∃s'. det_run 4 s s' ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s'``,
    rpt strip_tac
    \\ `s.PC = 0x4000A0w` by fs [FORGE_M3_FFIBOOT_VENEER_def]
    \\ `asm_write_bytearray (s.REG 2w) bytes2 s.MEM = s.MEM` by (irule asm_write_bytearray_id \\ metis_tac [])
    \\ qexists_tac `s with <|PC := s.REG 30w;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551070 + 1)));
                                 C := F;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFDDFw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFDDFw)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det v_boot \\ step_m3_det b_cmp_545 \\ step_m3_det b_blo_lt \\ step_m3_det b_ret_err
        \\ simp [det_run_def, cmp_carry_545, arm8Theory.arm8_state_component_equality])
    \\ simp [m3_ffi_return_ok_slot_def, arm8_ok_erase, sp_ok_def, bits_of_def]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val boot_entry_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = FORGE_M3_FFIBOOT_VENEER ∧ 545 ≤ w2n (s.REG 3w) ⇒
        ∃s_loop.
          det_run 7 s s_loop ∧ arm8_ok (erase s_loop) ∧ sp_ok s_loop ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_loop.MEM ∧
          bits_of s_loop = bits_of s ∧ s_loop.SP_EL0 = s.SP_EL0 ∧
          s_loop.PC = 0x4501BCw ∧ s_loop.MEM = s.MEM ∧
          s_loop.REG 9w = s.REG 2w ∧ s_loop.REG 10w = FORGE_RX_TMP ∧ s_loop.REG 11w = 32w ∧
          s_loop.REG 30w = s.REG 30w ∧
          (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s_loop.REG (n2w r) = s.REG (n2w r))``,
    rpt strip_tac
    \\ `s.PC = 0x4000A0w` by fs [FORGE_M3_FFIBOOT_VENEER_def]
    \\ qabbrev_tac `p = s.REG 2w`
    \\ qexists_tac `s with <|PC := 0x4501BCw;
                             REG := s.REG⦇9w ↦ p; 10w ↦ FORGE_RX_TMP; 11w ↦ 32w⦈;
                             PSTATE := s.PSTATE with
                               <|V := (word_msb (s.REG 3w) ∧
                                       (word_msb (s.REG 3w) ⇎
                                        BIT 63 (w2n (s.REG 3w) + 18446744073709551070 + 1)));
                                 C := T;
                                 Z := (s.REG 3w + 0xFFFFFFFFFFFFFDDFw = 0w);
                                 N := word_msb (s.REG 3w + 0xFFFFFFFFFFFFFDDFw)|>;
                             branch_hint := NONE|>`
    \\ conj_tac
    >- (step_m3_det v_boot \\ step_m3_det b_cmp_545 \\ step_m3_det b_blo_ge \\ step_m3_det b_mov9
        \\ step_m3_det b_adrp10 \\ step_m3_det b_add10 \\ step_m3_det b_mov11_32
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, Abbr `p`, FORGE_RX_TMP_def, cmp_carry_545,
              arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
              combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM, Abbr `p`]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_key_done_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501BCw ∧ s.REG 11w = 0w ⇒
        ∃s_d. det_run 3 s s_d ∧ arm8_ok (erase s_d) ∧ sp_ok s_d ∧
              m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_d.MEM ∧
              bits_of s_d = bits_of s ∧ s_d.SP_EL0 = s.SP_EL0 ∧
              s_d.PC = 0x4501F8w ∧ s_d.MEM = s.MEM ∧
              s_d.REG 11w = 512w ∧ s_d.REG 13w = 0w ∧
              (∀r. r ≠ 11w ∧ r ≠ 13w ⇒ s_d.REG r = s.REG r)``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x4501F8w; REG := s.REG⦇11w ↦ 512w; 13w ↦ 0w⦈; branch_hint := NONE|>`
    \\ conj_tac
    >- (step_m3_det b_k_cbz_z \\ step_m3_det b_d_mov11 \\ step_m3_det b_d_mov13
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_key_to_svc_det = prove(
    ``∀cb_begin cb_end bm_buf_end s k c.
        1 ≤ c ∧ c + k = 32 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501BCw ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ⇒
        ∃s_svc.
          det_run 5 s s_svc ∧ arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_svc.MEM ∧
          bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
          s_svc.PC = 0x4501D0w ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
          s_svc.REG 0w = 4w ∧ s_svc.REG 1w = FORGE_RX_TMP + n2w k ∧
          s_svc.REG 2w = n2w c ∧ s_svc.REG 8w = 63w ∧
          (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
    rpt strip_tac
    \\ qabbrev_tac `s_svc = s with <|PC := 0x4501D0w;
                                     REG := s.REG⦇0w ↦ 4w; 1w ↦ FORGE_RX_TMP + n2w k; 2w ↦ n2w c; 8w ↦ 63w⦈;
                                     branch_hint := NONE|>`
    \\ qexists_tac `s_svc`
    \\ conj_tac
    >- (step_m3_det b_k_cbz_nz \\ step_m3_det b_k_mov0 \\ step_m3_det b_k_mov1
        \\ step_m3_det b_k_mov2 \\ step_m3_det b_k_mov8
        \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `is_svc0_at s_svc` by (irule b_k_svc \\ simp [Abbr `s_svc`] \\ metis_tac [])
    \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_key_eintr_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501D4w ∧ s.REG 0w = -4w ⇒
        ∃s'. det_run 2 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x4501BCw ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x4501BCw; PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det b_k_cmn4 \\ step_m3_det b_k_beq_eq
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_key_err_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501D4w ∧ s.REG 9w = p ∧
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
    >- (step_m3_det b_k_cmn4 \\ step_m3_det b_k_beq_ne \\ step_m3_det b_k_cmp0 \\ step_m3_det b_k_ble_le
        \\ step_m3_det b_mov12_1 \\ step_m3_det b_strb_1 \\ step_m3_det b_ret_err
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
              arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val boot_key_ok_det = prove(
    ``∀cb_begin cb_end bm_buf_end s k c m.
        1 ≤ m ∧ m ≤ c ∧ c + k = 32 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501D4w ∧ s.REG 0w = n2w m ∧
        s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ⇒
        ∃s'. det_run 7 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x4501BCw ∧ s'.MEM = s.MEM ∧
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
    \\ qexists_tac `s with <|PC := 0x4501BCw;
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
    >- (step_m3_det b_k_cmn4 \\ step_m3_det b_k_beq_ne \\ step_m3_det b_k_cmp0 \\ step_m3_det b_k_ble_gt
        \\ step_m3_det b_k_add10 \\ step_m3_det b_k_sub11 \\ step_m3_det b_k_bloop
        \\ simp [det_run_def, m3_cmp_zero_gt_cond, arm8Theory.arm8_state_component_equality,
                 arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ `aligned 2 (0x4501BCw:word64)` by EVAL_TAC
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val boot_disk_done_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501F8w ∧ s.REG 11w = 0w ⇒
        ∃s_cp. det_run 4 s s_cp ∧ arm8_ok (erase s_cp) ∧ sp_ok s_cp ∧
               m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_cp.MEM ∧
               bits_of s_cp = bits_of s ∧ s_cp.SP_EL0 = s.SP_EL0 ∧
               s_cp.PC = 0x450254w ∧ s_cp.MEM = s.MEM ∧
               s_cp.REG 12w = FORGE_RX_TMP ∧ s_cp.REG 11w = 0w ∧
               (∀r. r ≠ 11w ∧ r ≠ 12w ⇒ s_cp.REG r = s.REG r)``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x450254w; REG := s.REG⦇12w ↦ FORGE_RX_TMP; 11w ↦ 0w⦈; branch_hint := NONE|>`
    \\ conj_tac
    >- (step_m3_det b_d_cbz_z \\ step_m3_det b_c_adrp12 \\ step_m3_det b_c_add12 \\ step_m3_det b_c_mov11_0
        \\ simp [det_run_def, FORGE_RX_TMP_def, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_disk_to_svc_det = prove(
    ``∀cb_begin cb_end bm_buf_end s k c.
        1 ≤ c ∧ c + k = 512 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501F8w ∧ s.REG 10w = FORGE_RX_TMP + n2w (32 + k) ∧
        s.REG 11w = n2w c ∧ s.REG 13w = n2w k ⇒
        ∃s_svc.
          det_run 6 s s_svc ∧ arm8_ok (erase s_svc) ∧ sp_ok s_svc ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s_svc.MEM ∧
          bits_of s_svc = bits_of s ∧ s_svc.SP_EL0 = s.SP_EL0 ∧
          s_svc.PC = 0x450210w ∧ is_svc0_at s_svc ∧ s_svc.MEM = s.MEM ∧
          s_svc.REG 0w = 3w ∧ s_svc.REG 1w = FORGE_RX_TMP + n2w (32 + k) ∧
          s_svc.REG 2w = n2w c ∧ s_svc.REG 3w = n2w k ∧ s_svc.REG 8w = 67w ∧
          (∀r. r ≠ 0w ∧ r ≠ 1w ∧ r ≠ 2w ∧ r ≠ 3w ∧ r ≠ 8w ⇒ s_svc.REG r = s.REG r)``,
    rpt strip_tac
    \\ qabbrev_tac `s_svc = s with <|PC := 0x450210w;
                                     REG := s.REG⦇0w ↦ 3w; 1w ↦ FORGE_RX_TMP + n2w (32 + k);
                                                  2w ↦ n2w c; 3w ↦ n2w k; 8w ↦ 67w⦈;
                                     branch_hint := NONE|>`
    \\ qexists_tac `s_svc`
    \\ conj_tac
    >- (step_m3_det b_d_cbz_nz \\ step_m3_det b_d_mov0 \\ step_m3_det b_d_mov1
        \\ step_m3_det b_d_mov2 \\ step_m3_det b_d_mov3 \\ step_m3_det b_d_mov8
        \\ simp [det_run_def, Abbr `s_svc`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `is_svc0_at s_svc` by (irule b_d_svc \\ simp [Abbr `s_svc`] \\ metis_tac [])
    \\ simp [Abbr `s_svc`, arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_disk_eintr_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450214w ∧ s.REG 0w = -4w ⇒
        ∃s'. det_run 2 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x4501F8w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x4501F8w; PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det b_d_cmn4 \\ step_m3_det b_d_beq_eq
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_disk_eof_det = prove(
    ``∀cb_begin cb_end bm_buf_end s.
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450214w ∧ s.REG 0w = 0w ⇒
        ∃s'. det_run 3 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x450234w ∧ s'.MEM = s.MEM ∧ s'.REG = s.REG``,
    rpt strip_tac
    \\ qexists_tac `s with <|PC := 0x450234w; PSTATE := s.PSTATE with <|V := F; C := F; Z := F; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det b_d_cmn4 \\ step_m3_det b_d_beq_ne \\ step_m3_det b_d_cbz0_z
        \\ simp [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality] \\ EVAL_TAC)
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def] \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)

  val boot_disk_err_det = prove(
    ``∀cb_begin cb_end bm_buf_end s (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450214w ∧ s.REG 9w = p ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        word_msb (s.REG 0w) ∧ s.REG 0w ≠ -4w ⇒
        ∃s'. det_run 7 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = s.REG 30w ∧ s'.MEM = s.MEM⦇p ↦ 1w⦈ ∧
             (∀r. r ≠ 12w ⇒ s'.REG r = s.REG r)``,
    rpt strip_tac
    \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ `p ∉ forge_m3_shim_code_region` by simp []
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end (s.MEM⦇p ↦ 1w⦈)` by simp [m3_shim_loaded_slot_update]
    \\ `s.REG 0w ≠ 0w ∧ word_bit 63 (s.REG 0w)` by (simp [m3_word_bit_63_msb] \\ strip_tac \\ gvs [])
    \\ qexists_tac `s with <|MEM := s.MEM⦇p ↦ 1w⦈; PC := s.REG 30w; REG := s.REG⦇12w ↦ 1w⦈;
                             PSTATE := s.PSTATE with
                               <|V := ((word_msb (s.REG 0w) ⇔ F) ∧
                                       (word_msb (s.REG 0w) ⇎ BIT 63 (w2n (s.REG 0w) + 4)));
                                 C := ((if w2n (s.REG 0w) + 4 < 18446744073709551616
                                        then w2n (s.REG 0w) + 4
                                        else (w2n (s.REG 0w) + 4) MOD 18446744073709551616) ≠
                                       w2n (s.REG 0w) + 4);
                                 Z := (s.REG 0w + 4w = 0w); N := word_msb (s.REG 0w + 4w)|>;
                             branch_hint := SOME BranchType_RET|>`
    \\ conj_tac
    >- (step_m3_det b_d_cmn4 \\ step_m3_det b_d_beq_ne \\ step_m3_det b_d_cbz0_nz \\ step_m3_det b_d_tbnz_err
        \\ step_m3_det b_mov12_1 \\ step_m3_det b_strb_1 \\ step_m3_det b_ret_err
        \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
             [det_run_def, arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
              combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val boot_disk_ok_det = prove(
    ``∀cb_begin cb_end bm_buf_end s k c m.
        1 ≤ m ∧ m ≤ c ∧ c + k = 512 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450214w ∧ s.REG 0w = n2w m ∧
        s.REG 10w = FORGE_RX_TMP + n2w (32 + k) ∧ s.REG 11w = n2w c ∧ s.REG 13w = n2w k ⇒
        ∃s'. det_run 8 s s' ∧ arm8_ok (erase s') ∧ sp_ok s' ∧
             m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
             bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
             s'.PC = 0x4501F8w ∧ s'.MEM = s.MEM ∧
             s'.REG 10w = FORGE_RX_TMP + n2w (32 + (k + m)) ∧
             s'.REG 11w = n2w (c - m) ∧ s'.REG 13w = n2w (k + m) ∧
             (∀r. r ≠ 10w ∧ r ≠ 11w ∧ r ≠ 13w ⇒ s'.REG r = s.REG r)``,
    rpt strip_tac
    \\ `¬word_msb (n2w m : word64) ∧ ¬word_bit 63 (n2w m : word64) ∧
        (n2w m : word64) ≠ 0w ∧ (n2w m : word64) ≠ -4w ∧
        ¬word_msb ((n2w m : word64) + 4w) ∧ w2n (n2w m : word64) = m ∧
        ¬BIT 63 (m + 4)` by
       (simp [m3_word_bit_63_msb, wordsTheory.word_msb_n2w, wordsTheory.word_add_n2w,
              wordsTheory.n2w_11, wordsTheory.w2n_n2w, dimword_64]
        \\ `¬BIT 63 m ∧ ¬BIT 63 (m + 4)` by (conj_tac \\ irule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
        \\ `(-4w:word64) = n2w 18446744073709551612` by EVAL_TAC
        \\ simp [wordsTheory.n2w_11, dimword_64])
    \\ `-1w * (n2w m : word64) + n2w c = n2w (c - m)` by
       (ONCE_REWRITE_TAC [cj 1 m3_word64_arith_step_helpers]
        \\ mp_tac (Q.SPECL [`c`, `m`] (INST_TYPE [alpha |-> ``:64``] wordsTheory.n2w_sub)) \\ simp [])
    \\ `(n2w m : word64) + (FORGE_RX_TMP + n2w (32 + k)) = FORGE_RX_TMP + n2w (32 + (k + m))` by
       (ONCE_REWRITE_TAC [cj 2 m3_word64_arith_step_helpers] \\ simp [wordsTheory.word_add_n2w]
        \\ AP_TERM_TAC \\ AP_TERM_TAC \\ decide_tac)
    \\ `(n2w m : word64) + n2w k = n2w (k + m)` by (simp [wordsTheory.word_add_n2w] \\ AP_TERM_TAC \\ decide_tac)
    \\ qexists_tac `s with <|PC := 0x4501F8w;
                             REG := s.REG⦇10w ↦ FORGE_RX_TMP + n2w (32 + (k + m));
                                          11w ↦ n2w (c - m); 13w ↦ n2w (k + m)⦈;
                             PSTATE := s.PSTATE with <|V := F; C := F; Z := F; N := F|>;
                             branch_hint := SOME BranchType_JMP|>`
    \\ conj_tac
    >- (step_m3_det b_d_cmn4 \\ step_m3_det b_d_beq_ne \\ step_m3_det b_d_cbz0_nz \\ step_m3_det b_d_tbnz_ok
        \\ step_m3_det b_d_add10 \\ step_m3_det b_d_sub11 \\ step_m3_det b_d_add13 \\ step_m3_det b_d_bloop
        \\ simp [det_run_def, m3_cmn_4_zero, arm8Theory.arm8_state_component_equality,
                 arm8Theory.ProcState_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
        \\ rw [] \\ fs [])
    \\ `aligned 2 (0x4501F8w:word64)` by EVAL_TAC
    \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ fs [arm8_ok_erase, sp_ok_def])

  val boot_zero_loop_det = prove(
    ``∀c k cb_begin cb_end bm_buf_end s (key:word8 list) (disk:word8 list).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        c + k = 512 ∧ LENGTH key = 32 ∧ k ≤ LENGTH disk ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450234w ∧ s.REG 10w = FORGE_RX_TMP + n2w (32 + k) ∧ s.REG 11w = n2w c ∧
        (∀i. i < 32 ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i key) ∧
        (∀i. i < k ⇒ s.MEM (FORGE_RX_TMP + n2w (32 + i)) = EL i disk) ⇒
        ∃d s'.
          1 ≤ d ∧ det_run d s s' ∧
          arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
          s'.PC = 0x450254w ∧ s'.REG 12w = FORGE_RX_TMP ∧ s'.REG 11w = 0w ∧
          (∀i. i < 32 ⇒ s'.MEM (FORGE_RX_TMP + n2w i) = EL i key) ∧
          (∀i. i < 512 ⇒ s'.MEM (FORGE_RX_TMP + n2w (32 + i)) = EL i (TAKE k disk ++ REPLICATE c 0w)) ∧
          (∀a. a ∉ forge_m3_rx_tmp_region ⇒ s'.MEM a = s.MEM a) ∧
          (∀r. r ≠ 10w ∧ r ≠ 11w ∧ r ≠ 12w ⇒ s'.REG r = s.REG r)``,
    Induct_on `c`
    >- (
      rpt strip_tac \\ `k = 512` by decide_tac \\ rveq
      \\ qexists_tac `4`
      \\ qexists_tac `s with <|PC := 0x450254w; REG := s.REG⦇12w ↦ FORGE_RX_TMP; 11w ↦ 0w⦈; branch_hint := NONE|>`
      \\ conj_tac >- decide_tac
      \\ conj_tac
      >- (step_m3_det b_z_cbz_z \\ step_m3_det b_c_adrp12 \\ step_m3_det b_c_add12 \\ step_m3_det b_c_mov11_0
          \\ simp [det_run_def, FORGE_RX_TMP_def, arm8Theory.arm8_state_component_equality,
                   combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
      \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM,
               rich_listTheory.REPLICATE, EL_TAKE]
      \\ fs [arm8_ok_erase, sp_ok_def] \\ EVAL_TAC)
    \\ rpt strip_tac \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ `FORGE_RX_TMP + n2w (32 + k) ∈ forge_m3_rx_tmp_region` by
         simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
               wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, dimword_64]
    \\ `FORGE_RX_TMP + n2w (32 + k) ∉ forge_m3_shim_code_region` by simp []
    \\ `FORGE_RX_TMP + n2w (k + 32) ∉ forge_m3_shim_code_region` by
         (`k + 32 = 32 + k` by decide_tac \\ pop_assum SUBST1_TAC \\ first_assum ACCEPT_TAC)
    \\ qabbrev_tac `m1 = s.MEM⦇FORGE_RX_TMP + n2w (32 + k) ↦ 0w⦈`
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by simp [Abbr `m1`, m3_shim_loaded_slot_update]
    \\ `(n2w (SUC c) : word64) ≠ 0w` by simp [wordsTheory.n2w_11, dimword_64]
    \\ `(n2w (SUC c) : word64) + 0xFFFFFFFFFFFFFFFFw = n2w c` by (mp_tac (Q.SPEC `SUC c` m3_n2w_sub1) \\ simp [])
    \\ `FORGE_RX_TMP + n2w (k + 32) + 1w = FORGE_RX_TMP + n2w (k + 33)` by
         (simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w] \\ AP_TERM_TAC \\ AP_TERM_TAC \\ decide_tac)
    \\ qabbrev_tac `s_next = s with <|MEM := m1; PC := 0x450234w;
                                      REG := s.REG⦇10w ↦ FORGE_RX_TMP + n2w (32 + (k + 1)); 11w ↦ n2w c⦈;
                                      branch_hint := SOME BranchType_JMP|>`
    \\ `det_run 5 s s_next` by (
         step_m3_det b_z_cbz_nz \\ step_m3_det b_z_strb0 \\ step_m3_det b_z_add10
         \\ step_m3_det b_z_sub11 \\ step_m3_det b_z_bloop
         \\ simp [det_run_def, Abbr `s_next`, Abbr `m1`,
                  arm8Theory.arm8_state_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
         \\ rw [] \\ fs [])
    \\ qpat_x_assum `∀k cb_begin cb_end bm_buf_end s key disk. _`
         (qspecl_then [`k + 1`, `cb_begin`, `cb_end`, `bm_buf_end`, `s_next`, `key`, `TAKE k disk ++ [0w]`] mp_tac)
    \\ impl_tac
    >- (
      simp [Abbr `s_next`, combinTheory.APPLY_UPDATE_THM, arm8_ok_erase, sp_ok_def]
      \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
      \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY decide_tac
      >- (rpt strip_tac \\ simp [Abbr `m1`, combinTheory.APPLY_UPDATE_THM]
          \\ `FORGE_RX_TMP + n2w i ≠ FORGE_RX_TMP + n2w (32 + k)` by
               simp [wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64]
          \\ simp [])
      \\ rpt strip_tac \\ simp [Abbr `m1`, combinTheory.APPLY_UPDATE_THM]
      \\ Cases_on `i = k`
      >- (rveq \\ simp [EL_APPEND2])
      \\ `i < k` by decide_tac
      \\ `FORGE_RX_TMP + n2w (32 + i) ≠ FORGE_RX_TMP + n2w (32 + k)` by
           simp [wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64]
      \\ qpat_x_assum `∀i. i < k ⇒ _` (qspec_then `i` mp_tac)
      \\ simp [EL_APPEND1, EL_TAKE])
    \\ strip_tac
    \\ qexists_tac `5 + d` \\ qexists_tac `s'`
    \\ conj_tac >- decide_tac
    \\ conj_tac >- (irule det_run_add \\ qexists_tac `s_next` \\ simp [])
    \\ `TAKE (k + 1) (TAKE k disk ++ [0w]) ++ REPLICATE c 0w = TAKE k disk ++ REPLICATE (SUC c) 0w` by (
         `LENGTH (TAKE k disk ++ [0w]) = k + 1` by simp []
         \\ `TAKE (k + 1) (TAKE k disk ++ [0w]) = TAKE k disk ++ [0w]` by metis_tac [listTheory.TAKE_LENGTH_ID_rwt]
         \\ pop_assum SUBST1_TAC
         \\ simp [rich_listTheory.REPLICATE])
    \\ `s_next.SP_EL0 = s.SP_EL0 ∧ bits_of s_next = bits_of s ∧
        (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s_next.REG r = s.REG r)` by
         simp [Abbr `s_next`, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ qpat_x_assum `TAKE (k + 1) _ ++ _ = _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th])
    \\ rpt conj_tac \\ TRY (first_assum ACCEPT_TAC) \\ TRY (simp [] \\ NO_TAC)
    >- (rpt strip_tac \\ `s_next.MEM a = s.MEM a` by (simp [Abbr `s_next`, Abbr `m1`, combinTheory.APPLY_UPDATE_THM] \\ IF_CASES_TAC \\ fs []) \\ simp [])
    \\ rpt strip_tac \\ simp [])

  val boot_copy_loop_det = prove(
    ``∀c k cb_begin cb_end bm_buf_end s (payload:word8 list) (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        1 ≤ c ∧ c + k = 544 ∧ LENGTH payload = 544 ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x450254w ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ s.REG 12w = FORGE_RX_TMP ∧ s.REG 11w = n2w k ∧
        (∀i. i < 545 ⇒ p + n2w i ∈ forge_m3_prog_addresses cb_end bm_buf_end) ∧
        (∀i. i < 544 ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i payload) ⇒
        ∃d s'.
          1 ≤ d ∧ det_run d s s' ∧
          arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
          s'.PC = s.REG 30w ∧
          s'.MEM = (p =+ 0w) (asm_write_bytearray (p + n2w (k + 1)) (DROP k payload) s.MEM) ∧
          (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s'.REG r = s.REG r)``,
    Induct_on `c` >- (rpt strip_tac \\ `F` by decide_tac)
    \\ rpt strip_tac \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ Cases_on `c = 0`
    >- (
      `k = 543` by decide_tac \\ pop_assum SUBST_ALL_TAC
      \\ qabbrev_tac `blast = EL 543 payload`
      \\ qpat_assum `∀i. i < 544 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `543`)
      \\ qpat_assum `∀i. i < 545 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `544`)
      \\ qpat_assum `∀i. i < 545 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `0`)
      \\ `p + 544w ∉ forge_m3_shim_code_region ∧ p ∉ forge_m3_shim_code_region` by simp []
      \\ qabbrev_tac `m1 = s.MEM⦇p + 544w ↦ blast⦈`
      \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by simp [Abbr `m1`, m3_shim_loaded_slot_update]
      \\ qabbrev_tac `m2 = m1⦇p ↦ 0w⦈`
      \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m2` by simp [Abbr `m2`, m3_shim_loaded_slot_update]
      \\ `DROP 543 payload = [blast]` by (simp [Abbr `blast`] \\ `543 < LENGTH payload` by decide_tac \\ simp [DROP_EL_CONS, listTheory.DROP_LENGTH_TOO_LONG])
      \\ qexists_tac `7`
      \\ qexists_tac `s with <|MEM := m2; PC := s.REG 30w;
                               REG := s.REG⦇10w ↦ w2w blast; 11w ↦ 544w⦈;
                               PSTATE := s.PSTATE with <|V := F; C := T; Z := T; N := F|>;
                               branch_hint := SOME BranchType_RET|>`
      \\ conj_tac >- decide_tac
      \\ conj_tac
      >- (step_m3_det b_c_ldrb \\ step_m3_det b_c_add11 \\ step_m3_det b_c_strb
          \\ step_m3_det b_c_cmp_544 \\ step_m3_det b_c_blo_done \\ step_m3_det b_c_strb_0 \\ step_m3_det b_c_ret_ok
          \\ FULL_SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
               [det_run_def, Abbr `m2`, Abbr `m1`, Abbr `blast`, FORGE_RX_TMP_def, cmp_carry_544,
                arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
          \\ rw [] \\ fs [] \\ TRY (EVAL_TAC \\ NO_TAC))
      \\ simp [arm8_ok_erase, sp_ok_def, bits_of_def, combinTheory.APPLY_UPDATE_THM,
               Abbr `m2`, Abbr `m1`, miscTheory.asm_write_bytearray_def]
      \\ fs [arm8_ok_erase, sp_ok_def])
    \\ `k < 543 ∧ k + 1 < 544` by decide_tac
    \\ qabbrev_tac `bk = EL k payload`
    \\ qpat_assum `∀i. i < 544 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k`)
    \\ qpat_assum `∀i. i < 545 ⇒ _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `k + 1`)
    \\ `p + n2w (k + 1) ∈ forge_m3_prog_addresses cb_end bm_buf_end` by simp []
    \\ `p + n2w (k + 1) ∉ forge_m3_shim_code_region` by simp []
    \\ `∀i. i < 544 ⇒ p + n2w (k + 1) ≠ FORGE_RX_TMP + n2w i` by
       (rpt strip_tac
        \\ `FORGE_RX_TMP + n2w i ∈ forge_m3_rx_tmp_region` by
             simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO,
                   word_add_n2w, w2n_n2w, dimword_64]
        \\ `p + n2w (k + 1) ∈ forge_m3_rx_tmp_region` by fs []
        \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `p + n2w (k + 1)`)
        \\ simp [])
    \\ qabbrev_tac `m1 = s.MEM⦇p + n2w (k + 1) ↦ bk⦈`
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by simp [Abbr `m1`, m3_shim_loaded_slot_update]
    \\ qabbrev_tac `s_next = s with <|MEM := m1; PC := 0x450254w;
                                      REG := s.REG⦇10w ↦ w2w bk; 11w ↦ n2w (k + 1)⦈;
                                      PSTATE := s.PSTATE with
                                        <|V := (word_msb (n2w (k + 1):word64) ∧
                                                (word_msb (n2w (k + 1):word64) ⇎
                                                 BIT 63 (w2n (n2w (k + 1):word64) + 18446744073709551071 + 1)));
                                          C := F;
                                          Z := ((n2w (k + 1):word64) + 0xFFFFFFFFFFFFFDE0w = 0w);
                                          N := word_msb ((n2w (k + 1):word64) + 0xFFFFFFFFFFFFFDE0w)|>;
                                      branch_hint := SOME BranchType_JMP|>`
    \\ `det_run 5 s s_next` by
       (step_m3_det b_c_ldrb \\ step_m3_det b_c_add11 \\ step_m3_det b_c_strb
        \\ step_m3_det b_c_cmp_544 \\ step_m3_det b_c_blo_more
        \\ simp [det_run_def, Abbr `s_next`, Abbr `m1`, Abbr `bk`, cmp_carry_544,
                 m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                 arm8Theory.arm8_state_component_equality, arm8Theory.ProcState_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ qpat_x_assum `∀k cb_begin cb_end bm_buf_end s payload p. _`
         (qspecl_then [`k + 1`, `cb_begin`, `cb_end`, `bm_buf_end`, `s_next`, `payload`, `p`] mp_tac)
    \\ impl_tac
    >- (simp [Abbr `s_next`, combinTheory.APPLY_UPDATE_THM, arm8_ok_erase, sp_ok_def]
        \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
        \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY decide_tac
        \\ rpt strip_tac \\ simp [Abbr `m1`, combinTheory.APPLY_UPDATE_THM]
        \\ `FORGE_RX_TMP + n2w i ≠ p + n2w (k + 1)` by
             (strip_tac \\ qpat_assum `∀i. i < 544 ⇒ p + n2w (k + 1) ≠ _` (mp_tac o Q.SPEC `i`) \\ simp [])
        \\ simp [])
    \\ strip_tac
    \\ `s_next.MEM = m1 ∧ s_next.SP_EL0 = s.SP_EL0 ∧ bits_of s_next = bits_of s ∧
        s_next.REG 30w = s.REG 30w ∧ (∀r. r ≠ 10w ∧ r ≠ 11w ⇒ s_next.REG r = s.REG r)` by
         simp [Abbr `s_next`, bits_of_def, combinTheory.APPLY_UPDATE_THM]
    \\ qexists_tac `5 + d` \\ qexists_tac `s'`
    \\ conj_tac >- decide_tac
    \\ conj_tac >- (irule det_run_add \\ qexists_tac `s_next` \\ simp [])
    \\ simp []
    \\ `DROP k payload = bk :: DROP (k + 1) payload` by simp [Abbr `bk`, DROP_EL_CONS, ADD1]
    \\ simp [miscTheory.asm_write_bytearray_def]
    \\ `p + n2w (k + 1) + 1w = p + n2w (k + 2)` by simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w]
    \\ simp [FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] \\ gen_tac
    \\ Cases_on `x = p` \\ simp []
    \\ Cases_on `x = p + n2w (k + 1)` \\ simp [Abbr `m1`]
    >- (`asm_write_bytearray (p + n2w (k + 2)) (DROP (k + 1) payload) (s.MEM⦇p + n2w (k + 1) ↦ bk⦈) (p + n2w (k + 1)) =
         (s.MEM⦇p + n2w (k + 1) ↦ bk⦈) (p + n2w (k + 1))` by
          (irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
           \\ `i < 544` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
           \\ qpat_x_assum `p + n2w (k + 1) = _` mp_tac
           \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                    wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
        \\ simp [combinTheory.APPLY_UPDATE_THM])
    \\ irule m3_asm_write_bytearray_pointwise \\ simp [combinTheory.APPLY_UPDATE_THM])

  val boot_disk_loop_universal = prove(
    ``∀n allow_err cb_begin cb_end bm_buf_end k c s os os_f ms_f ec (p:word64) (key:word8 list).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        c + k = 512 ∧ LENGTH key = 32 ∧ k ≤ LENGTH os.disk ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501F8w ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ s.REG 10w = FORGE_RX_TMP + n2w (32 + k) ∧ s.REG 11w = n2w c ∧ s.REG 13w = n2w k ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        (∀i. i < 32 ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i key) ∧
        (∀i. i < k ⇒ s.MEM (FORGE_RX_TMP + n2w (32 + i)) = EL i os.disk) ∧
        NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f ⇒
        (∃n' s'.
           n' < n ∧
           NRC (m3_whole_step allow_err) n' (os, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = 0x450254w ∧ s'.REG 9w = p ∧ s'.REG 12w = FORGE_RX_TMP ∧ s'.REG 11w = 0w ∧
           s'.REG 30w = s.REG 30w ∧
           (∀i. i < 544 ⇒ s'.MEM (FORGE_RX_TMP + n2w i) = EL i (key ++ pad512 os.disk)) ∧
           (∀a. a ∉ forge_m3_rx_tmp_region ⇒ s'.MEM a = s.MEM a) ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
        (allow_err ∧
         ∃n' s'.
           n' < n ∧
           NRC (m3_whole_step allow_err) n' (os, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧
           (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒ s'.MEM a = (p =+ 1w) s.MEM a) ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
    completeInduct_on `n` \\ rpt strip_tac
    \\ Cases_on `c = 0`
    >- (
      `k = 512` by decide_tac \\ pop_assum SUBST_ALL_TAC
      \\ `512 ≤ LENGTH os.disk` by decide_tac
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac boot_disk_done_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj1_tac \\ qexists_tac `n - 4` \\ qexists_tac `s_cp`
      \\ simp [] \\ rpt conj_tac
      >- (rpt strip_tac \\ Cases_on `i < 32`
          >- simp [EL_APPEND1]
          \\ simp [EL_APPEND2, GSYM m3_take_512_eq_pad512, EL_TAKE]
          \\ `32 + (i - 32) = i` by decide_tac
          \\ qpat_x_assum `∀i. i < 512 ⇒ _` (qspec_then `i - 32` mp_tac) \\ simp [])
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `1 ≤ c` by decide_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `k`, `c`] mp_tac boot_disk_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ Cases_on `n - 6` >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, cj 4 m3_whole_step_svc_det]
    \\ rpt strip_tac
    \\ rename1 `NRC _ _ (os, z2) _`
    \\ qpat_x_assum `svc_pread64_rel _ _ _ _`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_pread64_rel_def, svc_frame_rel_def, LET_THM])
    \\ `s_svc.REG 9w = p ∧ s_svc.REG 10w = FORGE_RX_TMP + n2w (32 + k) ∧
        s_svc.REG 11w = n2w c ∧ s_svc.REG 13w = n2w k ∧ s_svc.REG 30w = s.REG 30w` by simp []
    \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
        z2.PC = 0x450214w ∧ z2.REG 9w = p ∧ z2.REG 10w = FORGE_RX_TMP + n2w (32 + k) ∧
        z2.REG 11w = n2w c ∧ z2.REG 13w = n2w k ∧ z2.REG 30w = s.REG 30w ∧
        (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
         (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY (fs [bits_of_def] \\ NO_TAC)
          \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `w2n (s_svc.REG 3w) = k ∧ w2n (s_svc.REG 2w) = c` by simp [wordsTheory.w2n_n2w, dimword_64]
    \\ qpat_x_assum `_ ∨ _ ∨ _ ∨ _` (REPEAT_TCL DISJ_CASES_THEN strip_assume_tac)
    >- (
      qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac boot_disk_eintr_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac) \\ impl_tac >- decide_tac
      \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`, `k`, `c`,
                                  `s'`, `os`, `os_f`, `ms_f`, `ec`, `p`, `key`] mp_tac)
      \\ impl_tac >- (simp [] \\ rpt strip_tac \\ qpat_x_assum `∀i. i < k ⇒ _` (qspec_then `i` mp_tac) \\ simp []) \\ strip_tac
      >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ conj_tac >- simp [] \\ qexists_tac `n''` \\ qexists_tac `s''`
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      `k = LENGTH os.disk` by decide_tac
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac boot_disk_eof_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qspecl_then [`c`, `k`, `cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `key`, `os.disk`] mp_tac boot_zero_loop_det
      \\ impl_tac >- (simp [] \\ rpt strip_tac \\ qpat_x_assum `∀i. i < k ⇒ _` (qspec_then `i` mp_tac) \\ simp []) \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj1_tac \\ qexists_tac `n' - 3 - d` \\ qexists_tac `s''`
      \\ `TAKE k os.disk ++ REPLICATE c 0w = pad512 os.disk` by (irule m3_take_pad512_zero_fill \\ simp [])
      \\ simp [] \\ rpt conj_tac \\ TRY decide_tac
      >- (rpt strip_tac \\ Cases_on `i < 32`
          >- simp [EL_APPEND1]
          \\ simp [EL_APPEND2]
          \\ `32 + (i - 32) = i` by decide_tac
          \\ qpat_x_assum `∀i. i < 512 ⇒ _` (qspec_then `i - 32` mp_tac) \\ simp [])
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac boot_disk_err_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj2_tac \\ conj_tac >- simp [] \\ qexists_tac `n' - 7` \\ qexists_tac `s'`
      \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ rename1 `z2.REG 0w = n2w m`
    \\ `m ≤ c` by decide_tac
    \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ z2.MEM a = s.MEM a` by (
         rpt strip_tac \\ simp [] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
         \\ `i < m` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
         \\ `FORGE_RX_TMP + n2w (32 + k) + n2w i ∈ forge_m3_rx_tmp_region` by
              simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, m3_word_add_n2w_right,
                    wordsTheory.word_add_n2w, WORD_LS, WORD_LO, w2n_n2w, dimword_64]
         \\ rveq \\ fs [])
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end z2.MEM` by (
         irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
         \\ conj_tac
         >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
             \\ qpat_assum `m3_slot_layout_ok _ _ _` (strip_assume_tac o MATCH_MP m3_regions_disjoint_slot)
             \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
         \\ first_assum ACCEPT_TAC)
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `k`, `c`, `m`] mp_tac boot_disk_ok_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 8` mp_tac) \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                `k + m`, `c - m`, `s'`, `os`, `os_f`, `ms_f`, `ec`, `p`, `key`] mp_tac)
    \\ impl_tac
    >- (
      simp [] \\ rpt conj_tac
      >- (rpt strip_tac
          \\ `asm_write_bytearray (FORGE_RX_TMP + n2w (k + 32)) (TAKE m (DROP k os.disk)) s.MEM (FORGE_RX_TMP + n2w i) =
              s.MEM (FORGE_RX_TMP + n2w i)` by (
                irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
                \\ `i' < m` by (qpat_x_assum `i' < LENGTH _` mp_tac \\ simp [])
                \\ qpat_x_assum `FORGE_RX_TMP + n2w i = _` mp_tac
                \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                         wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
          \\ simp [])
      \\ rpt strip_tac \\ Cases_on `i < k`
      >- (`asm_write_bytearray (FORGE_RX_TMP + n2w (k + 32)) (TAKE m (DROP k os.disk)) s.MEM (FORGE_RX_TMP + n2w (i + 32)) =
           s.MEM (FORGE_RX_TMP + n2w (i + 32))` by (
             irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
             \\ `i' < m` by (qpat_x_assum `i' < LENGTH _` mp_tac \\ simp [])
             \\ qpat_x_assum `FORGE_RX_TMP + n2w (i + 32) = _` mp_tac
             \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                      wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
          \\ pop_assum SUBST1_TAC
          \\ qpat_x_assum `∀i. i < k ⇒ _` (qspec_then `i` mp_tac) \\ simp [])
      \\ `i - k < m` by decide_tac
      \\ `FORGE_RX_TMP + n2w (i + 32) = (FORGE_RX_TMP + n2w (k + 32)) + n2w (i - k)` by
           (simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w] \\ AP_TERM_TAC \\ AP_TERM_TAC \\ decide_tac)
      \\ pop_assum SUBST1_TAC
      \\ `asm_write_bytearray (FORGE_RX_TMP + n2w (k + 32)) (TAKE m (DROP k os.disk)) s.MEM
            ((FORGE_RX_TMP + n2w (k + 32)) + n2w (i - k)) = EL (i - k) (TAKE m (DROP k os.disk))` by
           (irule asm_write_bytearray_read_el \\ simp [dimword_64])
      \\ simp [EL_TAKE, EL_DROP])
    \\ strip_tac
    >- (
      disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''`
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ disj2_tac \\ conj_tac >- simp [] \\ qexists_tac `n''` \\ qexists_tac `s''`
    \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac
    \\ rpt strip_tac
    \\ TRY (pop_assum SUBST1_TAC \\ simp [] \\ NO_TAC)
    \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `m3_slot_layout_ok _ _ _` (strip_assume_tac o MATCH_MP m3_regions_disjoint_slot) \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
    \\ simp [combinTheory.APPLY_UPDATE_THM])

  val boot_key_loop_universal = prove(
    ``∀n allow_err cb_begin cb_end bm_buf_end k c acc s os os_f ms_f ec (p:word64).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        c + k = 32 ∧ LENGTH acc = k ∧
        arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501BCw ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        s.REG 9w = p ∧ s.REG 10w = FORGE_RX_TMP + n2w k ∧ s.REG 11w = n2w c ∧
        p ∈ forge_m3_prog_addresses cb_end bm_buf_end ∧
        (∀i. i < k ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i acc) ∧
        NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
        svc_exit_group_rel ec ms_f ⇒
        (∃n' s' key krest.
           n' < n ∧ LENGTH key = 32 ∧ acc ++ os.key_in = key ++ krest ∧
           NRC (m3_whole_step allow_err) n' (os with key_in := krest, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = 0x4501F8w ∧ s'.REG 9w = p ∧ s'.REG 10w = FORGE_RX_TMP + 32w ∧
           s'.REG 11w = 512w ∧ s'.REG 13w = 0w ∧ s'.REG 30w = s.REG 30w ∧
           (∀i. i < 32 ⇒ s'.MEM (FORGE_RX_TMP + n2w i) = EL i key) ∧
           (∀a. a ∉ forge_m3_rx_tmp_region ⇒ s'.MEM a = s.MEM a) ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))) ∨
        (∃n' s' krest.
           n' < n ∧ (allow_err ∨ LENGTH (acc ++ os.key_in) < 32) ∧
           NRC (m3_whole_step allow_err) n' (os with key_in := krest, s') (os_f, ms_f) ∧
           arm8_ok (erase s') ∧ sp_ok s' ∧
           m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
           bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
           s'.PC = s.REG 30w ∧
           (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒ s'.MEM a = (p =+ 1w) s.MEM a) ∧
           (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r)))``,
    completeInduct_on `n` \\ rpt strip_tac
    \\ Cases_on `c = 0`
    >- (
      `k = 32` by decide_tac \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac boot_key_done_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj1_tac \\ qexists_tac `n - 3` \\ qexists_tac `s_d` \\ qexists_tac `acc` \\ qexists_tac `os.key_in`
      \\ `os with key_in := os.key_in = os` by simp [m3_os_component_equality]
      \\ simp [] \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ `1 ≤ c` by decide_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `k`, `c`] mp_tac boot_key_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ Cases_on `n - 5` >- (fs [arithmeticTheory.NRC] \\ rveq \\ gvs [svc_exit_group_rel_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, cj 2 m3_whole_step_svc_det]
    \\ rpt strip_tac \\ qpat_x_assum `_ = os with key_in := _` SUBST_ALL_TAC
    \\ rename1 `NRC _ _ (os with key_in := rest, z2) _`
    \\ qpat_x_assum `svc_read_fd_rel _ _ _ _ _ _`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac o SIMP_RULE (srw_ss()) [svc_read_fd_rel_def, svc_frame_rel_def])
    \\ `s_svc.REG 9w = p ∧ s_svc.REG 10w = FORGE_RX_TMP + n2w k ∧
        s_svc.REG 11w = n2w c ∧ s_svc.REG 30w = s.REG 30w` by simp []
    \\ `arm8_ok (erase z2) ∧ sp_ok z2 ∧ bits_of z2 = bits_of s ∧ z2.SP_EL0 = s.SP_EL0 ∧
        z2.PC = 0x4501D4w ∧ z2.REG 9w = p ∧ z2.REG 10w = FORGE_RX_TMP + n2w k ∧
        z2.REG 11w = n2w c ∧ z2.REG 30w = s.REG 30w ∧
        (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ z2.REG (n2w r) = s.REG (n2w r))` by
         (simp [arm8_ok_erase, sp_ok_def, bits_of_def]
          \\ rpt conj_tac \\ TRY (fs [arm8_ok_erase] \\ EVAL_TAC \\ NO_TAC)
          \\ TRY (fs [sp_ok_def] \\ NO_TAC) \\ TRY (fs [bits_of_def] \\ NO_TAC)
          \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ qpat_x_assum `_ ∨ _ ∨ _ ∨ _` (REPEAT_TCL DISJ_CASES_THEN strip_assume_tac)
    >- (
      `os with key_in := rest = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`] mp_tac boot_key_eintr_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n' - 2` mp_tac) \\ impl_tac >- decide_tac
      \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                  `k`, `c`, `acc`, `s'`, `os`, `os_f`, `ms_f`, `ec`, `p`] mp_tac)
      \\ impl_tac >- simp [] \\ strip_tac
      >- (disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `key` \\ qexists_tac `krest`
          \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
      \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `krest`
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      qpat_x_assum `rest = []` SUBST_ALL_TAC
      \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end z2.MEM ∧ k < 32` by simp []
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac boot_key_err_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj2_tac \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `[]`
      \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    >- (
      `os with key_in := rest = os` by simp [m3_os_component_equality] \\ pop_assum SUBST_ALL_TAC
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `p`] mp_tac boot_key_err_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj2_tac \\ qexists_tac `n' - 7` \\ qexists_tac `s'` \\ qexists_tac `os.key_in`
      \\ qpat_x_assum `NRC _ _ _ _` mp_tac
      \\ simp [combinTheory.APPLY_UPDATE_THM] \\ disch_then (K ALL_TAC)
      \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ rename1 `z2.REG 0w = n2w m`
    \\ qpat_x_assum `rest = DROP _ _` SUBST_ALL_TAC
    \\ `m ≤ c` by (qpat_x_assum `m ≤ w2n _` mp_tac \\ simp [wordsTheory.w2n_n2w, dimword_64])
    \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ z2.MEM a = s.MEM a` by (
         rpt strip_tac \\ simp [] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
         \\ `i < m` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
         \\ `FORGE_RX_TMP + n2w k + n2w i ∈ forge_m3_rx_tmp_region` by
              simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, m3_word_add_n2w_right,
                    wordsTheory.word_add_n2w, WORD_LS, WORD_LO, w2n_n2w, dimword_64]
         \\ rveq \\ fs [])
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end z2.MEM` by (
         irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
         \\ conj_tac
         >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
             \\ qpat_assum `m3_slot_layout_ok _ _ _` (strip_assume_tac o MATCH_MP m3_regions_disjoint_slot)
             \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
         \\ first_assum ACCEPT_TAC)
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `z2`, `k`, `c`, `m`] mp_tac boot_key_ok_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ m3_peel_nrc_tac
    \\ qpat_x_assum `∀m'. m' < n ⇒ _` (qspec_then `n' - 7` mp_tac) \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                                `k + m`, `c - m`, `acc ++ TAKE m os.key_in`,
                                `s'`, `os with key_in := DROP m os.key_in`, `os_f`, `ms_f`, `ec`, `p`] mp_tac)
    \\ impl_tac
    >- (
      simp [] \\ rpt strip_tac \\ Cases_on `i < k`
      >- (simp [EL_APPEND1]
          \\ `asm_write_bytearray (FORGE_RX_TMP + n2w k) (TAKE m os.key_in) s.MEM (FORGE_RX_TMP + n2w i) =
              s.MEM (FORGE_RX_TMP + n2w i)` by (
                irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
                \\ `i' < m` by (qpat_x_assum `i' < LENGTH _` mp_tac \\ simp [])
                \\ qpat_x_assum `FORGE_RX_TMP + n2w i = _` mp_tac
                \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                         wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
          \\ simp [])
      \\ simp [EL_APPEND2] \\ `i - k < m` by decide_tac
      \\ `FORGE_RX_TMP + n2w i = (FORGE_RX_TMP + n2w k) + n2w (i - k)` by
           simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w]
      \\ pop_assum SUBST1_TAC
      \\ `asm_write_bytearray (FORGE_RX_TMP + n2w k) (TAKE m os.key_in) s.MEM
            ((FORGE_RX_TMP + n2w k) + n2w (i - k)) = EL (i - k) (TAKE m os.key_in)` by
           (irule asm_write_bytearray_read_el \\ simp [dimword_64])
      \\ simp [])
    \\ strip_tac
    >- (
      disj1_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `key` \\ qexists_tac `krest`
      \\ fs [m3_append_take_drop] \\ rfs []
      \\ rpt conj_tac \\ TRY decide_tac
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `krest`
    \\ fs [m3_append_take_drop] \\ rfs []
    \\ rpt conj_tac \\ TRY decide_tac
    \\ rpt strip_tac
    \\ TRY (pop_assum SUBST1_TAC \\ simp [] \\ NO_TAC)
    \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `m3_slot_layout_ok _ _ _` (strip_assume_tac o MATCH_MP m3_regions_disjoint_slot) \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
    \\ simp [combinTheory.APPLY_UPDATE_THM])

  val boot_disk_noerr_exists = prove(
    ``∀cb_begin cb_end bm_buf_end s (key:word8 list) (disk:word8 list).
        m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
        LENGTH key = 32 ∧ arm8_ok (erase s) ∧ sp_ok s ∧
        m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
        s.PC = 0x4501F8w ∧ s.REG 10w = FORGE_RX_TMP + 32w ∧ s.REG 11w = 512w ∧ s.REG 13w = 0w ∧
        (∀i. i < 32 ⇒ s.MEM (FORGE_RX_TMP + n2w i) = EL i key) ⇒
        ∃s'.
          (∀os. os.disk = disk ⇒ RTC (m3_whole_step F) (os, s) (os, s')) ∧
          arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
          m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧
          s'.PC = 0x450254w ∧ s'.REG 9w = s.REG 9w ∧ s'.REG 12w = FORGE_RX_TMP ∧ s'.REG 11w = 0w ∧
          s'.REG 30w = s.REG 30w ∧
          (∀i. i < 544 ⇒ s'.MEM (FORGE_RX_TMP + n2w i) = EL i (key ++ pad512 disk)) ∧
          (∀a. a ∉ forge_m3_rx_tmp_region ⇒ s'.MEM a = s.MEM a) ∧
          (∀r. MEM r [19;20;21;22;23;24;25;26;27;28] ⇒ s'.REG (n2w r) = s.REG (n2w r))``,
    rpt strip_tac \\ drule m3_regions_disjoint_slot \\ strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `0`, `512`] mp_tac boot_disk_to_svc_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ Cases_on `512 ≤ LENGTH disk`
    >- (
      qabbrev_tac `m1 = asm_write_bytearray (FORGE_RX_TMP + 32w) (TAKE 512 disk) s.MEM`
      \\ qabbrev_tac `s_post = s_svc with <|PC := 0x450214w; REG := s_svc.REG⦇0w ↦ 512w⦈; MEM := m1|>`
      \\ `∀os. os.disk = disk ⇒ m3_whole_step F (os, s_svc) (os, s_post)` by (
           rpt strip_tac \\ simp [m3_whole_step_def, Abbr `s_post`, svc_pread64_rel_def, svc_frame_rel_def,
                                  combinTheory.APPLY_UPDATE_THM, LET_THM]
           \\ conj_tac >- (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp []) \\ qexists_tac `512` \\ simp [Abbr `m1`])
      \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ m1 a = s.MEM a` by (
           rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
           \\ `i < 512` by (qpat_x_assum `i < LENGTH _` mp_tac \\ simp [])
           \\ `FORGE_RX_TMP + 32w + n2w i ∈ forge_m3_rx_tmp_region` by
                simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, m3_word_add_n2w_right,
                      wordsTheory.word_add_n2w, WORD_LS, WORD_LO, w2n_n2w, dimword_64]
           \\ rveq \\ fs [])
      \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by (
           irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
           \\ conj_tac
           >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
               \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
           \\ first_assum ACCEPT_TAC)
      \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by (
           simp [Abbr `s_post`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
           \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `0`, `512`, `512`] mp_tac boot_disk_ok_det
      \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`] mp_tac boot_disk_done_det \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `s_cp`
      \\ conj_tac
      >- (rpt strip_tac
          \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
          \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
          \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_post)`
          \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
          \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s')`
          \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `8` \\ simp [])
          \\ irule m3_det_run_imp_rtc \\ qexists_tac `4` \\ simp [])
      \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
      \\ rpt conj_tac
      >- (rpt strip_tac \\ Cases_on `i < 32`
          >- (simp [EL_APPEND1, Abbr `m1`]
              \\ `asm_write_bytearray (FORGE_RX_TMP + 32w) (TAKE 512 disk) s.MEM (FORGE_RX_TMP + n2w i) = s.MEM (FORGE_RX_TMP + n2w i)` by (
                    irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
                    \\ `i' < 512` by (qpat_x_assum `i' < LENGTH _` mp_tac \\ simp [])
                    \\ qpat_x_assum `FORGE_RX_TMP + n2w i = _` mp_tac
                    \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                             wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
              \\ simp [])
          \\ simp [EL_APPEND2, GSYM m3_take_512_eq_pad512, Abbr `m1`]
          \\ `FORGE_RX_TMP + n2w i = (FORGE_RX_TMP + 32w) + n2w (i - 32)` by
               (simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w] \\ AP_TERM_TAC \\ AP_TERM_TAC \\ decide_tac)
          \\ pop_assum SUBST1_TAC
          \\ irule asm_write_bytearray_read_el \\ simp [dimword_64])
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ Cases_on `LENGTH disk = 0`
    >- (
      qabbrev_tac `s_eof = s_svc with <|PC := 0x450214w; REG := s_svc.REG⦇0w ↦ 0w⦈|>`
      \\ `∀os. os.disk = disk ⇒ m3_whole_step F (os, s_svc) (os, s_eof)` by (
           rpt strip_tac \\ simp [m3_whole_step_def, Abbr `s_eof`, svc_pread64_rel_def, svc_frame_rel_def,
                                  combinTheory.APPLY_UPDATE_THM, LET_THM]
           \\ irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
      \\ `arm8_ok (erase s_eof) ∧ sp_ok s_eof ∧ bits_of s_eof = bits_of s ∧ s_eof.SP_EL0 = s.SP_EL0` by (
           simp [Abbr `s_eof`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
           \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
      \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_eof`] mp_tac boot_disk_eof_det
      \\ impl_tac >- simp [Abbr `s_eof`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
      \\ qspecl_then [`512`, `0`, `cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `key`, `disk`] mp_tac boot_zero_loop_det
      \\ impl_tac >- simp [Abbr `s_eof`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
      \\ qexists_tac `s''`
      \\ conj_tac
      >- (rpt strip_tac
          \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
          \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
          \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_eof)`
          \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
          \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s')`
          \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
          \\ irule m3_det_run_imp_rtc \\ qexists_tac `d` \\ simp [])
      \\ `TAKE 0 disk ++ REPLICATE 512 0w = pad512 disk` by
           (qpat_assum `LENGTH disk = 0` mp_tac \\ qspecl_then [`disk`, `0`, `512`] mp_tac m3_take_pad512_zero_fill \\ simp [])
      \\ simp [Abbr `s_eof`, combinTheory.APPLY_UPDATE_THM]
      \\ rpt conj_tac
      >- (rpt strip_tac \\ Cases_on `i < 32` >- simp [EL_APPEND1]
          \\ simp [EL_APPEND2] \\ `32 + (i - 32) = i` by decide_tac
          \\ qpat_x_assum `∀i. i < 512 ⇒ _` (qspec_then `i - 32` mp_tac) \\ simp [])
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ qabbrev_tac `L = LENGTH disk` \\ `1 ≤ L ∧ L < 512` by decide_tac
    \\ qabbrev_tac `m1 = asm_write_bytearray (FORGE_RX_TMP + 32w) disk s.MEM`
    \\ qabbrev_tac `s_post = s_svc with <|PC := 0x450214w; REG := s_svc.REG⦇0w ↦ n2w L⦈; MEM := m1|>`
    \\ `∀os. os.disk = disk ⇒ m3_whole_step F (os, s_svc) (os, s_post)` by (
         rpt strip_tac \\ simp [m3_whole_step_def, Abbr `s_post`, svc_pread64_rel_def, svc_frame_rel_def,
                                combinTheory.APPLY_UPDATE_THM, LET_THM]
         \\ conj_tac >- (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
         \\ TRY disj2_tac \\ TRY disj2_tac
         \\ qexists_tac `L` \\ simp [Abbr `m1`, Abbr `L`, TAKE_LENGTH_ID_rwt])
    \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ m1 a = s.MEM a` by (
         rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
         \\ `i < L` by (qpat_x_assum `i < LENGTH disk` mp_tac \\ simp [Abbr `L`])
         \\ `FORGE_RX_TMP + 32w + n2w i ∈ forge_m3_rx_tmp_region` by
              simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, m3_word_add_n2w_right,
                    wordsTheory.word_add_n2w, WORD_LS, WORD_LO, w2n_n2w, dimword_64]
         \\ rveq \\ fs [])
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by (
         irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
         \\ conj_tac
         >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
             \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
         \\ first_assum ACCEPT_TAC)
    \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by (
         simp [Abbr `s_post`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
         \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `0`, `512`, `L`] mp_tac boot_disk_ok_det
    \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `L`, `512 - L`] mp_tac boot_disk_to_svc_det
    \\ impl_tac >- simp [] \\ strip_tac
    \\ qabbrev_tac `s_eof = s_svc' with <|PC := 0x450214w; REG := s_svc'.REG⦇0w ↦ 0w⦈|>`
    \\ `∀os. os.disk = disk ⇒ m3_whole_step F (os, s_svc') (os, s_eof)` by (
         rpt strip_tac \\ simp [m3_whole_step_def, Abbr `s_eof`, svc_pread64_rel_def, svc_frame_rel_def,
                                combinTheory.APPLY_UPDATE_THM, LET_THM, wordsTheory.w2n_n2w, dimword_64]
         \\ simp [Abbr `L`] \\ irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
    \\ `arm8_ok (erase s_eof) ∧ sp_ok s_eof ∧ bits_of s_eof = bits_of s ∧ s_eof.SP_EL0 = s.SP_EL0` by (
         simp [Abbr `s_eof`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
         \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_eof`] mp_tac boot_disk_eof_det
    \\ impl_tac >- simp [Abbr `s_eof`, Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
    \\ qspecl_then [`512 - L`, `L`, `cb_begin`, `cb_end`, `bm_buf_end`, `s''`, `key`, `disk`] mp_tac boot_zero_loop_det
    \\ impl_tac
    >- (
      simp [Abbr `s_eof`, Abbr `s_post`, combinTheory.APPLY_UPDATE_THM, Abbr `m1`]
      \\ conj_tac
      >- (rpt strip_tac
          \\ `asm_write_bytearray (FORGE_RX_TMP + 32w) disk s.MEM (FORGE_RX_TMP + n2w i) = s.MEM (FORGE_RX_TMP + n2w i)` by (
                irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
                \\ `i' < L` by (qpat_x_assum `i' < LENGTH disk` mp_tac \\ simp [Abbr `L`])
                \\ qpat_x_assum `FORGE_RX_TMP + n2w i = _` mp_tac
                \\ simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                         wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.n2w_11, dimword_64])
          \\ simp [])
      \\ rpt strip_tac
      \\ `FORGE_RX_TMP + n2w (i + 32) = (FORGE_RX_TMP + 32w) + n2w i` by simp [m3_word_add_n2w_right, wordsTheory.word_add_n2w]
      \\ pop_assum SUBST1_TAC
      \\ irule asm_write_bytearray_read_el \\ simp [dimword_64, Abbr `L`])
    \\ strip_tac \\ qexists_tac `s'''`
    \\ conj_tac
    >- (rpt strip_tac
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_post)`
        \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s')`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `8` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc')`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `6` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_eof)`
        \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s'')`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
        \\ irule m3_det_run_imp_rtc \\ qexists_tac `d` \\ simp [])
    \\ `TAKE L disk ++ REPLICATE (512 - L) 0w = pad512 disk` by
         (qspecl_then [`disk`, `L`, `512 - L`] mp_tac m3_take_pad512_zero_fill \\ simp [Abbr `L`])
    \\ simp [Abbr `s_eof`, Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
    \\ rpt conj_tac
    >- (rpt strip_tac \\ Cases_on `i < 32` >- simp [EL_APPEND1]
        \\ simp [EL_APPEND2] \\ `32 + (i - 32) = i` by decide_tac
        \\ qpat_x_assum `∀i. i < 512 ⇒ _` (qspec_then `i - 32` mp_tac) \\ simp [])
    \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
in

Theorem m3_ffibootload_universal_slot:
  ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFIBOOT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 545 ⇒
       ∃n' s'. n' < n ∧
         NRC (m3_whole_step allow_err) n' (os, s') (os_f, ms_f) ∧
         m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (545 ≤ w2n (s.REG 3w) ⇒
       (∃n' s' key krest.
          n' < n ∧ LENGTH key = 32 ∧ os.key_in = key ++ krest ∧
          NRC (m3_whole_step allow_err) n' (os with key_in := krest, s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end
            (0w :: key ++ pad512 os.disk ++ DROP 545 bytes2) s s') ∨
       (∃n' s' krest.
          n' < n ∧ (allow_err ∨ LENGTH os.key_in < 32) ∧
          NRC (m3_whole_step allow_err) n' (os with key_in := krest, s') (os_f, ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s'))
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac boot_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ m3_peel_nrc_tac \\ qexists_tac `n - 4` \\ qexists_tac `s'` \\ simp [])
  \\ drule m3_regions_disjoint_slot \\ strip_tac
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `∀i. i < 545 ⇒ p + n2w i ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (qspec_then `i` mp_tac) \\ simp [])
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac boot_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ m3_peel_nrc_tac
  \\ qspecl_then [`n - 7`, `allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                  `0`, `32`, `[]`, `s_loop`, `os`, `os_f`, `ms_f`, `ec`, `p`] mp_tac boot_key_loop_universal
  \\ impl_tac >- simp [] \\ strip_tac
  >- (
    qspecl_then [`n'`, `allow_err`, `cb_begin`, `cb_end`, `bm_buf_end`,
                 `0`, `512`, `s'`, `os with key_in := krest`, `os_f`, `ms_f`, `ec`, `p`, `key`]
         mp_tac boot_disk_loop_universal
    \\ impl_tac >- simp [] \\ strip_tac
    >- (
      qspecl_then [`544`, `0`, `cb_begin`, `cb_end`, `bm_buf_end`, `s''`, `key ++ pad512 os.disk`, `p`]
           mp_tac boot_copy_loop_det
      \\ impl_tac >- simp [LENGTH_pad512] \\ strip_tac
      \\ m3_peel_nrc_tac
      \\ disj1_tac \\ qexists_tac `n'' - d` \\ qexists_tac `s'''` \\ qexists_tac `key` \\ qexists_tac `krest`
      \\ `asm_write_bytearray (s.REG 2w) (0w :: key ++ pad512 os.disk ++ DROP 545 bytes2) s.MEM =
          (p =+ 0w) (asm_write_bytearray (p + 1w) (key ++ pad512 os.disk) s.MEM)` by
           (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
            \\ `0w :: key ++ pad512 os.disk ++ DROP 545 bytes2 = 0w :: ((key ++ pad512 os.disk) ++ DROP 545 bytes2)` by simp []
            \\ pop_assum SUBST1_TAC
            \\ qspecl_then [`544`, `p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `key ++ pad512 os.disk`]
                 mp_tac asm_write_bytearray_drop_np1 \\ simp [LENGTH_pad512])
      \\ REWRITE_TAC [m3_ffi_return_ok_slot_def]
      \\ pop_assum SUBST1_TAC
      \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac
      >- (rpt strip_tac \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
          \\ irule m3_asm_write_bytearray_pointwise
          \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
          \\ simp [])
      \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
    \\ disj2_tac \\ qexists_tac `n''` \\ qexists_tac `s''` \\ qexists_tac `krest`
    \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
          \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
               asm_write_bytearray_drop1 \\ simp [])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
    \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac
    >- (rpt strip_tac \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
        \\ simp [combinTheory.APPLY_UPDATE_THM])
    \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ disj2_tac \\ qexists_tac `n'` \\ qexists_tac `s'` \\ qexists_tac `krest`
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
        \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
             asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
  \\ fs [] \\ rfs [] \\ rpt conj_tac \\ TRY decide_tac \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

Theorem m3_ffibootload_noerr_exists_slot:
  ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_FFIBOOT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 545 ⇒
       ∃s'. (∀os. RTC (m3_whole_step F) (os, s) (os, s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (∀key disk. 545 ≤ w2n (s.REG 3w) ∧ LENGTH key = 32 ⇒
       ∃s'. (∀os krest. os.key_in = key ++ krest ∧ os.disk = disk ⇒
               RTC (m3_whole_step F) (os, s) (os with key_in := krest, s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end
              (0w :: key ++ pad512 disk ++ DROP 545 bytes2) s s') ∧
    (∀kshort. 545 ≤ w2n (s.REG 3w) ∧ LENGTH kshort < 32 ⇒
       ∃s'. (∀os. os.key_in = kshort ⇒
               RTC (m3_whole_step F) (os, s) (os with key_in := [], s')) ∧
            m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w :: DROP 1 bytes2) s s')
Proof
  rpt strip_tac
  >- (qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`, `bytes2`] mp_tac boot_short_det \\ impl_tac >- simp [] \\ strip_tac
      \\ qexists_tac `s'` \\ simp [] \\ metis_tac [m3_det_run_imp_rtc])
  >- (
    drule m3_regions_disjoint_slot \\ strip_tac
    \\ imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `p = s.REG 2w`
    \\ `∀i. i < 545 ⇒ p + n2w i ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
         (rpt strip_tac \\ qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (qspec_then `i` mp_tac) \\ simp [])
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac boot_entry_det \\ impl_tac >- simp [] \\ strip_tac
    \\ `s_loop.REG 9w = p` by simp [Abbr `p`]
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `32`] mp_tac boot_key_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP key s.MEM`
    \\ qabbrev_tac `s_post = s_svc with <|PC := 0x4501D4w; REG := s_svc.REG⦇0w ↦ 32w⦈; MEM := m1|>`
    \\ `∀os krest. os.key_in = key ++ krest ⇒ m3_whole_step F (os, s_svc) (os with key_in := krest, s_post)` by (
         rpt strip_tac \\ `s_svc.exception = NoException` by (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
         \\ simp [m3_whole_step_def, Abbr `s_post`, svc_read_fd_rel_def, svc_frame_rel_def,
                  combinTheory.APPLY_UPDATE_THM]
         \\ qexists_tac `krest` \\ simp []
         \\ qexists_tac `32` \\ simp [Abbr `m1`, TAKE_APPEND1, DROP_APPEND2, listTheory.TAKE_LENGTH_ID_rwt])
    \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ m1 a = s.MEM a` by (
         rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
         \\ `FORGE_RX_TMP + n2w i ∈ forge_m3_rx_tmp_region` by
              simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO, word_add_n2w, w2n_n2w, dimword_64]
         \\ rveq \\ fs [])
    \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by (
         irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
         \\ conj_tac
         >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
             \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
         \\ first_assum ACCEPT_TAC)
    \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by (
         simp [Abbr `s_post`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
         \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `0`, `32`, `32`] mp_tac boot_key_ok_det
    \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`] mp_tac boot_key_done_det \\ impl_tac >- simp [] \\ strip_tac
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_d`, `key`, `disk`] mp_tac boot_disk_noerr_exists
    \\ impl_tac >- (simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM, Abbr `m1`]
                    \\ rpt strip_tac \\ irule asm_write_bytearray_read_el \\ simp [dimword_64])
    \\ strip_tac
    \\ qspecl_then [`544`, `0`, `cb_begin`, `cb_end`, `bm_buf_end`, `s''`, `key ++ pad512 disk`, `p`]
         mp_tac boot_copy_loop_det
    \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM, LENGTH_pad512] \\ strip_tac
    \\ qexists_tac `s'''`
    \\ conj_tac
    >- (rpt strip_tac
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := krest, s_post)`
        \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := krest, s')`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := krest, s_d)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := krest, s'')`
        \\ conj_tac >- (qpat_assum `∀os. os.disk = disk ⇒ RTC _ _ _` irule \\ simp [])
        \\ irule m3_det_run_imp_rtc \\ qexists_tac `d` \\ simp [])
    \\ `asm_write_bytearray (s.REG 2w) (0w :: key ++ pad512 disk ++ DROP 545 bytes2) s.MEM =
        (p =+ 0w) (asm_write_bytearray (p + 1w) (key ++ pad512 disk) s.MEM)` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
          \\ `0w :: key ++ pad512 disk ++ DROP 545 bytes2 = 0w :: ((key ++ pad512 disk) ++ DROP 545 bytes2)` by simp []
          \\ pop_assum SUBST1_TAC
          \\ qspecl_then [`544`, `p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `key ++ pad512 disk`]
               mp_tac asm_write_bytearray_drop_np1 \\ simp [LENGTH_pad512])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def]
    \\ pop_assum SUBST1_TAC
    \\ simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
    \\ rpt conj_tac
    >- (rpt strip_tac \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
        \\ irule m3_asm_write_bytearray_pointwise
        \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
        \\ simp [])
    \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ drule m3_regions_disjoint_slot \\ strip_tac
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `p = s.REG 2w`
  \\ `p ∈ forge_m3_prog_addresses cb_end bm_buf_end` by
       (qpat_x_assum `∀i. i < _ ⇒ _ ∈ forge_m3_prog_addresses _ _` (mp_tac o Q.SPEC `0`)
        \\ impl_tac >- decide_tac \\ disch_then (mp_tac o SIMP_RULE (srw_ss()) []) \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s`] mp_tac boot_entry_det \\ impl_tac >- simp [] \\ strip_tac
  \\ `s_loop.REG 9w = p` by simp [Abbr `p`]
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_loop`, `0`, `32`] mp_tac boot_key_to_svc_det \\ impl_tac >- simp [] \\ strip_tac
  \\ Cases_on `kshort = []`
  >- (
    pop_assum SUBST_ALL_TAC
    \\ qabbrev_tac `s_eof = s_svc with <|PC := 0x4501D4w; REG := s_svc.REG⦇0w ↦ 0w⦈|>`
    \\ `∀os. os.key_in = [] ⇒ m3_whole_step F (os, s_svc) (os with key_in := [], s_eof)` by (
         rpt strip_tac \\ `s_svc.exception = NoException` by (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
         \\ simp [m3_whole_step_def, Abbr `s_eof`, svc_read_fd_rel_def, svc_frame_rel_def,
                  combinTheory.APPLY_UPDATE_THM]
         \\ qexists_tac `[]` \\ simp [])
    \\ `arm8_ok (erase s_eof) ∧ sp_ok s_eof ∧ bits_of s_eof = bits_of s ∧ s_eof.SP_EL0 = s.SP_EL0` by (
         simp [Abbr `s_eof`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
         \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
    \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_eof`, `p`] mp_tac boot_key_err_det
    \\ impl_tac >- simp [Abbr `s_eof`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
    \\ qexists_tac `s'`
    \\ conj_tac
    >- (rpt strip_tac
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
        \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
        \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := [], s_eof)`
        \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
        \\ irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
    \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
         (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
          \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
               asm_write_bytearray_drop1 \\ simp [])
    \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
    \\ simp [Abbr `s_eof`, combinTheory.APPLY_UPDATE_THM] \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp [])
  \\ qabbrev_tac `L = LENGTH kshort`
  \\ `1 ≤ L` by (qpat_x_assum `kshort ≠ []` mp_tac \\ simp [Abbr `L`] \\ Cases_on `kshort` \\ simp [])
  \\ qabbrev_tac `m1 = asm_write_bytearray FORGE_RX_TMP kshort s.MEM`
  \\ qabbrev_tac `s_post = s_svc with <|PC := 0x4501D4w; REG := s_svc.REG⦇0w ↦ n2w L⦈; MEM := m1|>`
  \\ `∀os. os.key_in = kshort ⇒ m3_whole_step F (os, s_svc) (os with key_in := [], s_post)` by (
       rpt strip_tac \\ `s_svc.exception = NoException` by (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
       \\ simp [m3_whole_step_def, Abbr `s_post`, svc_read_fd_rel_def, svc_frame_rel_def,
                combinTheory.APPLY_UPDATE_THM]
       \\ qexists_tac `[]` \\ simp []
       \\ TRY disj2_tac \\ TRY disj2_tac
       \\ qexists_tac `L` \\ simp [Abbr `m1`, Abbr `L`, TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL])
  \\ `∀a. a ∉ forge_m3_rx_tmp_region ⇒ m1 a = s.MEM a` by (
       rpt strip_tac \\ simp [Abbr `m1`] \\ irule asm_write_bytearray_unchanged_lt \\ rpt strip_tac
       \\ `i < L` by (qpat_x_assum `i < LENGTH kshort` mp_tac \\ simp [Abbr `L`])
       \\ `FORGE_RX_TMP + n2w i ∈ forge_m3_rx_tmp_region` by
            simp [forge_m3_rx_tmp_region_def, FORGE_RX_TMP_def, WORD_LS, WORD_LO, word_add_n2w, w2n_n2w, dimword_64]
       \\ rveq \\ fs [])
  \\ `m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1` by (
       irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM`
       \\ conj_tac
       >- (rpt strip_tac \\ qpat_assum `∀a. a ∉ forge_m3_rx_tmp_region ⇒ _ a = s.MEM a` irule \\ strip_tac
           \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
       \\ first_assum ACCEPT_TAC)
  \\ `arm8_ok (erase s_post) ∧ sp_ok s_post ∧ bits_of s_post = bits_of s ∧ s_post.SP_EL0 = s.SP_EL0` by (
       simp [Abbr `s_post`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
       \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_post`, `0`, `32`, `L`] mp_tac boot_key_ok_det
  \\ impl_tac >- simp [Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s'`, `L`, `32 - L`] mp_tac boot_key_to_svc_det
  \\ impl_tac >- simp [] \\ strip_tac
  \\ qabbrev_tac `s_eof = s_svc' with <|PC := 0x4501D4w; REG := s_svc'.REG⦇0w ↦ 0w⦈|>`
  \\ `∀os0. os0.key_in = [] ⇒ m3_whole_step F (os0, s_svc') (os0, s_eof)` by (
       rpt strip_tac \\ `s_svc'.exception = NoException` by (irule (cj 5 m3_arm8_ok_sp_ok_upds) \\ simp [])
       \\ `os0 with key_in := [] = os0` by simp [m3_os_component_equality]
       \\ pop_assum (fn th => CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (GSYM th)))))
       \\ simp [m3_whole_step_def, Abbr `s_eof`, svc_read_fd_rel_def, svc_frame_rel_def,
                combinTheory.APPLY_UPDATE_THM]
       \\ qexists_tac `[]` \\ simp [])
  \\ `arm8_ok (erase s_eof) ∧ sp_ok s_eof ∧ bits_of s_eof = bits_of s ∧ s_eof.SP_EL0 = s.SP_EL0` by (
       simp [Abbr `s_eof`, m3_bits_of_upds, m3_arm8_ok_sp_ok_upds]
       \\ irule (cj 1 m3_arm8_ok_sp_ok_upds) \\ simp [] \\ EVAL_TAC)
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `s_eof`, `p`] mp_tac boot_key_err_det
  \\ impl_tac >- simp [Abbr `s_eof`, Abbr `s_post`, combinTheory.APPLY_UPDATE_THM] \\ strip_tac
  \\ qexists_tac `s''`
  \\ conj_tac
  >- (rpt strip_tac
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_loop)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os, s_svc)`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := [], s_post)`
      \\ conj_tac >- (irule relationTheory.RTC_SUBSET \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := [], s')`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := [], s_svc')`
      \\ conj_tac >- (irule m3_det_run_imp_rtc \\ qexists_tac `5` \\ simp [])
      \\ irule relationTheory.RTC_RTC \\ qexists_tac `(os with key_in := [], s_eof)`
      \\ conj_tac >- (
           irule relationTheory.RTC_SUBSET
           \\ qpat_assum `∀os0. os0.key_in = [] ⇒ m3_whole_step _ _ _` irule
           \\ simp [])
      \\ irule m3_det_run_imp_rtc \\ qexists_tac `7` \\ simp [])
  \\ `asm_write_bytearray (s.REG 2w) (1w :: DROP 1 bytes2) s.MEM = (p =+ 1w) s.MEM` by
       (`s.REG 2w = p` by simp [Abbr `p`] \\ qpat_assum `s.REG 2w = p` SUBST1_TAC
        \\ qspecl_then [`p`, `forge_m3_prog_addresses cb_end bm_buf_end`, `s.MEM`, `bytes2`, `1w`] mp_tac
             asm_write_bytearray_drop1 \\ simp [])
  \\ REWRITE_TAC [m3_ffi_return_ok_slot_def] \\ pop_assum SUBST1_TAC
  \\ simp [Abbr `s_eof`, Abbr `s_post`, combinTheory.APPLY_UPDATE_THM]
  \\ rpt conj_tac
  >- (rpt strip_tac \\ Cases_on `a = p` \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ `a ∉ forge_m3_rx_tmp_region` by (strip_tac \\ qpat_assum `∀a. a ∈ forge_m3_rx_tmp_region ⇒ _` (mp_tac o Q.SPEC `a`) \\ simp [])
      \\ simp [])
  \\ rpt strip_tac \\ TRY (pop_assum SUBST1_TAC) \\ simp []
QED

end;
