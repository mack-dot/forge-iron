(*
  Forge Milestone 3 Reusable Runtime: 43-Step Startup Proof (_start=0x450000 ->
  cake_main=0x4000D0), Exact Installed Proof & Universal Exit/Install Stub Proofs.
*)
Theory forge_airlockShimStart
Ancestors
  words arithmetic list combin pred_set relation
  arm8 arm8_step arm8_target arm8_config arm8_configProof
  asmProps targetSem lab_to_targetProof backendProof misc alignment set_sep byte
  forge_runtimeSpec forge_airlockFfi forge_airlockContract
  forge_arm8Erasure forge_shimProof forge_slotUtil forge_airlockShimBase
Libs
  preamble blastLib wordsLib forge_m3StepLib

(* ---- 1. Startup Proof (43 Steps): _start (0x450000) -> cml_main (0x400000) -> cake_main (0x4000D0) ---- *)

local
  val start_ths    = List.tabulate (16, fn i => prove_m3_step "shim" i 0)
  val cml_head_ths = List.tabulate (5, fn i => prove_m3_step "veneer" i 0)
  val cml_hdr0_ths = List.tabulate (3, fn i => prove_m3_step "veneer" (5 + i) 0)
  val cml_str_ths  = [prove_m3_step "veneer" 10 0,
                      prove_m3_step "veneer" 13 0,
                      prove_m3_step "veneer" 16 0,
                      prove_m3_step "veneer" 19 0]
  val cml_tail_ths = List.tabulate (7, fn i => prove_m3_step "veneer" (20 + i) 0)
in
  val start_ths = start_ths
  val cml_head_ths = cml_head_ths
  val cml_hdr0_ths = cml_hdr0_ths
  val cml_str_ths = cml_str_ths
  val cml_tail_ths = cml_tail_ths
end;

Theorem m3_start_block1_slot[local]:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x450000w ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧ s1.PC = 0x450014w ∧
      mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. 0x460008w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
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
     (EVERY (map step_m3_det (List.take (start_ths, 5)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_HEAP_def, FORGE_HEAP_def, arm8_stepTheory.mem_dword_def,
            combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC)) \\ simp [])
  >- (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_m3_shim_code_region_def, FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def,
                                           FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem m3_start_block2_slot[local]:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x450014w ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧ s1.PC = 0x450028w ∧
      mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a <₊ 0x460008w ∨ 0x460010w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
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
     (EVERY (map step_m3_det (List.take (List.drop (start_ths, 5), 5)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_STACK_def, FORGE_STACK_def, arm8_stepTheory.mem_dword_def,
            combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC)) \\ simp [])
  >- (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_m3_shim_code_region_def, FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def,
                                           FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem m3_start_block3_slot[local]:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x450028w ⇒
    let s1 = FUNPOW arm8$Next 6 s in
      det_run 6 s s1 ∧ s1.PC = FORGE_M3_VENEERS_BASE ∧
      mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a <₊ 0x460010w ⇒ s1.MEM a = s.MEM a) ∧
      m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
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
     (EVERY (map step_m3_det (List.drop (start_ths, 10)))
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_M3_VENEERS_BASE_def]
  \\ rpt conj_tac
  >- (simp [FORGE_CML_STACKEND_def, FORGE_STACKEND_def, arm8_stepTheory.mem_dword_def,
            combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_cml_ptrs_region_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ EVAL_TAC))
      \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC)) \\ simp [])
  >- (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_m3_shim_code_region_def, FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def,
                                           FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem m3_start_16_steps_slot[local]:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_SHIM_BASE ⇒
    let s1 = FUNPOW arm8$Next 16 s in
      det_run 16 s s1 ∧ s1.PC = FORGE_M3_VENEERS_BASE ∧
      mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
      mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
      mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
      (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
      m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `16 = 6 + (5 + 5)` by decide_tac \\ pop_assum SUBST1_TAC
  \\ rewrite_tac [arithmeticTheory.FUNPOW_ADD]
  \\ fs [FORGE_M3_SHIM_BASE_def]
  \\ drule_all m3_start_block1_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sA = FUNPOW arm8$Next 5 s`
  \\ drule_all m3_start_block2_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sB = FUNPOW arm8$Next 5 sA`
  \\ drule_all m3_start_block3_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sC = FUNPOW arm8$Next 6 sB`
  \\ simp []
  \\ rpt conj_tac
  >- (`16 = (5 + 5) + 6` by decide_tac \\ pop_assum SUBST1_TAC
      \\ irule det_run_add \\ qexists_tac `sB` \\ reverse conj_tac >- simp []
      \\ irule det_run_add \\ qexists_tac `sA` \\ simp [])
  >- (`mem_dword sC.MEM FORGE_CML_HEAP = mem_dword sA.MEM FORGE_CML_HEAP` by
        (irule m3_mem_dword_cong \\ simp [FORGE_CML_HEAP_def] \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sC.MEM ad`
         \\ `ad <₊ 0x460010w ∧ ad <₊ 0x460008w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  \\ `mem_dword sC.MEM FORGE_CML_STACK = mem_dword sB.MEM FORGE_CML_STACK` by
       (irule m3_mem_dword_cong \\ simp [FORGE_CML_STACK_def] \\ rpt strip_tac
        \\ qmatch_goalsub_abbrev_tac `sC.MEM ad`
        \\ `ad <₊ 0x460010w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
        \\ simp [])
  \\ simp []
QED

Theorem m3_cml_main_head_slot[local]:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_VENEERS_BASE ∧ mem_dword s.MEM FORGE_CML_HEAP = FORGE_HEAP ⇒
    let s1 = FUNPOW arm8$Next 5 s in
      det_run 5 s s1 ∧ s1.PC = 0x400014w ∧
      s1.REG 0w = FORGE_M3_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
      s1.MEM = s.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 5 s`
  \\ `s.PC = 0x400000w` by fs [FORGE_M3_VENEERS_BASE_def]
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x400014w;
                                   REG := s.REG⦇0w ↦ 0x4000D0w; 1w ↦ 0x480000w⦈;
                                   branch_hint := NONE|>`
  \\ `det_run 5 s s_tgt` by
     (EVERY (map step_m3_det cml_head_ths)
      \\ fs [det_run_def, Abbr `s_tgt`, FORGE_CML_HEAP_def, FORGE_HEAP_def,
             arm8Theory.arm8_state_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_M3_CAKE_MAIN_def, FORGE_HEAP_def, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

Theorem m3_cml_hdr0_slot[local]:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x400014w ∧ s.REG 0w = FORGE_M3_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
    let s1 = FUNPOW arm8$Next 3 s in
      det_run 3 s s1 ∧ s1.PC = 0x400020w ∧
      s1.REG 0w = FORGE_M3_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
      mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
      (∀a. a <₊ 0x480000w ∨ 0x480008w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
      (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
      m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧
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
      \\ EVERY (map step_m3_det cml_hdr0_ths)
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, combinTheory.APPLY_UPDATE_THM, FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def]
  \\ rpt conj_tac
  >- (simp [arm8_stepTheory.mem_dword_def, combinTheory.APPLY_UPDATE_THM] \\ EVAL_TAC)
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC)) \\ simp [])
  >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_heap_hdr_region_def, FORGE_HEAP_def] \\ EVAL_TAC)) \\ simp [])
  >- (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM` \\ simp []
      \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
      \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_m3_shim_code_region_def, FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def,
                                           FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def] \\ EVAL_TAC))
      \\ simp [])
  \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC
QED

local
  fun mk_m3_sym_hdr_thm name idx pc_in pc_out dst_val val_tm str_th =
    let
      val adrp_bths = List.tabulate (4, fn j => Vector.sub (m3_v_arr, 4 * idx + j))
      val add_bths  = List.tabulate (4, fn j => Vector.sub (m3_v_arr, 4 * (idx + 1) + j))
      val pc_mid = rhs (concl (EVAL ``^pc_in + 4w``))
      val pc_str = rhs (concl (EVAL ``^pc_in + 8w``))
      val dst_hi = rhs (concl (EVAL ``^dst_val + 8w``))
      val goal =
        ``∀cb_begin cb_end bm_buf_end s.
            m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
            arm8_ok (erase s) ∧ sp_ok s ∧
            m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
            s.PC = ^pc_in ∧ s.REG 0w = FORGE_M3_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
            let s1 = FUNPOW arm8$Next 3 s in
              det_run 3 s s1 ∧ s1.PC = ^pc_out ∧
              s1.REG 0w = FORGE_M3_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
              mem_dword s1.MEM ^dst_val = ^val_tm ∧
              (∀a. a <₊ ^dst_val ∨ ^dst_hi ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
              (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
              m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧
              arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0``
      val inst_adrp = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) adrp_bths
      val inst_add  = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) add_bths
    in
      prove (goal,
        rpt strip_tac
        \\ qabbrev_tac `s1 = FUNPOW arm8$Next 3 s`
        \\ `0x00400000w ≤₊ ^val_tm ∧ ^val_tm ≤₊ 0x00480000w` by
             (fs [m3_slot_layout_ok_def, FORGE_M3_CAKE_MAIN_def, FORGE_SLOT_END_def,
                  FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
                  wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
        \\ `words32_in_mem ^pc_in [arm8_enc_adrp_x2 ^pc_in ^val_tm] s.MEM ∧
            words32_in_mem ^pc_mid [arm8_enc_add_x2 ^val_tm] s.MEM` by
             (fs [m3_shim_loaded_slot_def, words32_in_mem_def]
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
             \\ step_m3_det str_th
             \\ simp [det_run_def, Abbr `s_tgt`])
        \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
        \\ simp [] \\ simp [Abbr `s_tgt`, combinTheory.APPLY_UPDATE_THM]
        \\ rpt conj_tac
        >- (mp_tac (SPECL [``(s:arm8_state).MEM``, dst_val, val_tm] m3_mem_dword_write8) \\ simp [])
        >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [] \\ EVAL_TAC)) \\ simp [])
        >- (rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_heap_hdr_region_def, FORGE_HEAP_def] \\ EVAL_TAC)) \\ simp [])
        >- (irule (iffRL m3_shim_loaded_slot_cong) \\ qexists_tac `s.MEM` \\ simp []
            \\ rpt strip_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
            \\ rpt (IF_CASES_TAC >- (rveq \\ fs [forge_m3_shim_code_region_def, FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def,
                                                 FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def] \\ EVAL_TAC))
            \\ simp [])
        \\ fs [arm8_ok_erase, sp_ok_def, bits_of_def] \\ EVAL_TAC)
    end
in
  val m3_cml_hdr1_slot = mk_m3_sym_hdr_thm "m3_cml_hdr1_slot"  8 ``0x400020w:word64`` ``0x40002Cw:word64`` ``0x480008w:word64`` ``bm_buf_end:word64`` (el 1 cml_str_ths)
  val m3_cml_hdr2_slot = mk_m3_sym_hdr_thm "m3_cml_hdr2_slot" 11 ``0x40002Cw:word64`` ``0x400038w:word64`` ``0x480010w:word64`` ``bm_buf_end:word64`` (el 2 cml_str_ths)
  val m3_cml_hdr3_slot = mk_m3_sym_hdr_thm "m3_cml_hdr3_slot" 14 ``0x400038w:word64`` ``0x400044w:word64`` ``0x480018w:word64`` ``cb_begin:word64``   (el 3 cml_str_ths)
  val m3_cml_hdr4_slot = mk_m3_sym_hdr_thm "m3_cml_hdr4_slot" 17 ``0x400044w:word64`` ``0x400050w:word64`` ``0x480020w:word64`` ``cb_end:word64``     (el 4 cml_str_ths)
end;

Theorem m3_cml_main_tail_slot[local]:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = 0x400050w ∧ s.REG 0w = FORGE_M3_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ∧
    mem_dword s.MEM FORGE_CML_STACK = FORGE_STACK ∧
    mem_dword s.MEM FORGE_CML_STACKEND = FORGE_STACKEND ⇒
    let s1 = FUNPOW arm8$Next 7 s in
      det_run 7 s s1 ∧ s1.PC = FORGE_M3_CAKE_MAIN ∧
      s1.REG 0w = FORGE_M3_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
      s1.REG 2w = FORGE_STACK ∧ s1.REG 3w = FORGE_STACKEND ∧
      s1.MEM = s.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
      bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `s1 = FUNPOW arm8$Next 7 s`
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x4000D0w;
                                   REG := s.REG⦇2w ↦ 0x4C0000w; 3w ↦ 0x500000w⦈;
                                   branch_hint := SOME BranchType_JMP|>`
  \\ `det_run 7 s s_tgt` by
     (EVERY (map step_m3_det cml_tail_ths)
      \\ fs [det_run_def, Abbr `s_tgt`, FORGE_CML_STACK_def, FORGE_CML_STACKEND_def,
             FORGE_STACK_def, FORGE_STACKEND_def,
             arm8Theory.arm8_state_component_equality, combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
      \\ rw [] \\ fs [])
  \\ `s1 = s_tgt` by (drule det_run_funpow \\ simp [Abbr `s1`])
  \\ simp [] \\ simp [Abbr `s_tgt`, FORGE_M3_CAKE_MAIN_def, FORGE_HEAP_def, FORGE_STACK_def, FORGE_STACKEND_def,
           combinTheory.APPLY_UPDATE_THM]
  \\ fs [FORGE_M3_CAKE_MAIN_def, FORGE_HEAP_def, arm8_ok_erase, sp_ok_def, bits_of_def]
  \\ EVAL_TAC
QED

Theorem m3_startup_to_cake_main_slot:
  ∀cb_begin cb_end bm_buf_end s.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_SHIM_BASE ⇒
    let s1 = FUNPOW arm8$Next 43 s in
      det_run 43 s s1 ∧
      s1.PC = FORGE_M3_CAKE_MAIN ∧
      s1.REG 0w = FORGE_M3_CAKE_MAIN ∧
      s1.REG 1w = FORGE_HEAP ∧
      s1.REG 2w = FORGE_STACK ∧
      s1.REG 3w = FORGE_STACKEND ∧
      mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
      mem_dword s1.MEM (FORGE_HEAP + 8w) = bm_buf_end ∧
      mem_dword s1.MEM (FORGE_HEAP + 16w) = bm_buf_end ∧
      mem_dword s1.MEM (FORGE_HEAP + 24w) = cb_begin ∧
      mem_dword s1.MEM (FORGE_HEAP + 32w) = cb_end ∧
      (∀a. a ∉ forge_cml_ptrs_region ∧ a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
      m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧
      arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `43 = 7 + (3 + (3 + (3 + (3 + (3 + (5 + 16))))))` by decide_tac
  \\ pop_assum SUBST1_TAC
  \\ rewrite_tac [arithmeticTheory.FUNPOW_ADD]
  \\ drule_all m3_start_16_steps_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `s0 = FUNPOW arm8$Next 16 s`
  \\ drule_all m3_cml_main_head_slot \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sA = FUNPOW arm8$Next 5 s0`
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `sA`] mp_tac m3_cml_hdr0_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sB = FUNPOW arm8$Next 3 sA`
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `sB`] mp_tac m3_cml_hdr1_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sC = FUNPOW arm8$Next 3 sB`
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `sC`] mp_tac m3_cml_hdr2_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sD = FUNPOW arm8$Next 3 sC`
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `sD`] mp_tac m3_cml_hdr3_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sE = FUNPOW arm8$Next 3 sD`
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `sE`] mp_tac m3_cml_hdr4_slot
  \\ impl_tac >- simp [] \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `sF = FUNPOW arm8$Next 3 sE`
  \\ `mem_dword sF.MEM FORGE_CML_STACK = FORGE_STACK ∧
      mem_dword sF.MEM FORGE_CML_STACKEND = FORGE_STACKEND` by
     (conj_tac
      >- (`mem_dword sF.MEM FORGE_CML_STACK = mem_dword s0.MEM FORGE_CML_STACK` by
            (irule m3_mem_dword_cong \\ simp [FORGE_CML_STACK_def] \\ rpt strip_tac
             \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
             \\ `ad ∉ forge_heap_hdr_region` by
                  (simp [Abbr `ad`, forge_heap_hdr_region_def, FORGE_HEAP_def] \\ blastLib.FULL_BBLAST_TAC)
             \\ simp [])
          \\ simp [])
      \\ `mem_dword sF.MEM FORGE_CML_STACKEND = mem_dword s0.MEM FORGE_CML_STACKEND` by
           (irule m3_mem_dword_cong \\ simp [FORGE_CML_STACKEND_def] \\ rpt strip_tac
            \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
            \\ `ad ∉ forge_heap_hdr_region` by
                 (simp [Abbr `ad`, forge_heap_hdr_region_def, FORGE_HEAP_def] \\ blastLib.FULL_BBLAST_TAC)
            \\ simp [])
      \\ simp [])
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_buf_end`, `sF`] mp_tac m3_cml_main_tail_slot
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
        (irule m3_mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480008w ∧ ad <₊ 0x480010w ∧ ad <₊ 0x480018w ∧ ad <₊ 0x480020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def] \\ fs [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def])
  >- (`mem_dword sF.MEM 0x480008w = mem_dword sC.MEM 0x480008w` by
        (irule m3_mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480010w ∧ ad <₊ 0x480018w ∧ ad <₊ 0x480020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  >- (`mem_dword sF.MEM 0x480010w = mem_dword sD.MEM 0x480010w` by
        (irule m3_mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480018w ∧ ad <₊ 0x480020w` by
              (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
  >- (`mem_dword sF.MEM 0x480018w = mem_dword sE.MEM 0x480018w` by
        (irule m3_mem_dword_cong \\ rpt strip_tac
         \\ qmatch_goalsub_abbrev_tac `sF.MEM ad`
         \\ `ad <₊ 0x480020w` by (simp [Abbr `ad`] \\ blastLib.FULL_BBLAST_TAC)
         \\ simp [])
      \\ simp [])
QED

(* ---- 2. Exact M3 Installed Proof ---- *)

Theorem m3_word_list_exists_0[local]:
  ∀a:word64. word_list_exists a 0 = emp
Proof
  gen_tac \\ simp [FUN_EQ_THM, miscTheory.word_list_exists_def, miscTheory.word_list_def,
                   set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
QED

Theorem m3_byte_align_in_region[local]:
  ∀(bm_end:word64) (a:word64).
    bm_end && 7w = 0w ∧
    ((0x00480000w ≤₊ (a && 0xFFFFFFFFFFFFFFF8w) ∧ (a && 0xFFFFFFFFFFFFFFF8w) <₊ 0x00500000w) ∨
     (0x00460018w ≤₊ (a && 0xFFFFFFFFFFFFFFF8w) ∧ (a && 0xFFFFFFFFFFFFFFF8w) <₊ bm_end)) ⇒
    (0x00480000w ≤₊ a ∧ a <₊ 0x00500000w) ∨
    (0x00460018w ≤₊ a ∧ a <₊ bm_end)
Proof
  blastLib.BBLAST_TAC
QED

Theorem m3_heap_bitmaps_disjoint[local]:
  ∀(bm_end:word64).
    bm_end ≤₊ 0x00470000w ⇒
    DISJOINT forge_heap_stack_region (forge_bitmaps_region_slot bm_end)
Proof
  simp [DISJOINT_DEF, EXTENSION, forge_heap_stack_region_def, forge_bitmaps_region_slot_def,
        FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def,
        wordsTheory.WORD_LO, wordsTheory.WORD_LS]
  \\ rpt strip_tac \\ decide_tac
QED

Theorem forge_m3_slot_installed_exact:
  ∀n0 n1 n2 n3 (code:word8 list) (data:num list) ffi_names ms0 ffi_if inst_if.
    ffi_names = SOME [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ∧
    forge_m3_slot_loaded code data ms0 ∧
    m3_real_interfer_ok_slot (m3_slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data))
      (m3_slot_cbspace (LENGTH code)) [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3]
      (bits_of ms0) ffi_if inst_if ⇒
    let cb_begin = m3_slot_cb_begin (LENGTH code) in
    let cb_end = m3_slot_cb_end (LENGTH code) in
    let bm_end = slot_bm_buf_end (LENGTH data) in
    let cbsp = m3_slot_cbspace (LENGTH code) in
    let ms1 = FUNPOW arm8$Next 43 ms0 in
    let emc = erase_mc (bits_of ms0)
                (forge_m3_mc_slot cb_end bm_end
                   [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if) in
      det_run 43 ms0 ms1 ∧
      ms1.PC = FORGE_M3_CAKE_MAIN ∧
      bits_of ms1 = bits_of ms0 ∧
      ms1.SP_EL0 = ms0.SP_EL0 ∧
      sp_ok ms1 ∧
      arm8_ok (erase ms1) ∧
      m3_shim_loaded_slot cb_begin cb_end bm_end ms1.MEM ∧
      installed code cbsp data 0 ffi_names (1, 3) emc [] (erase ms1)
Proof
  rpt strip_tac
  \\ simp [LET_THM]
  \\ qabbrev_tac `cb_begin = m3_slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = m3_slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ qabbrev_tac `cbsp = m3_slot_cbspace (LENGTH code)`
  \\ fs [forge_m3_slot_loaded_def, LET_THM]
  \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac m3_slot_params_props
  \\ impl_tac >- simp []
  \\ simp [LET_THM] \\ strip_tac
  \\ qspecl_then [`cb_begin`, `cb_end`, `bm_end`, `ms0`] mp_tac m3_startup_to_cake_main_slot
  \\ impl_tac >- simp []
  \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ qabbrev_tac `B = bits_of ms0`
  \\ qabbrev_tac `emc = erase_mc B (forge_m3_mc_slot cb_end bm_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if inst_if)`
  \\ simp [targetSemTheory.installed_def]
  \\ qexists_tac `<| regs := λr. ms1.REG (n2w r);
                     fp_regs := K 0w;
                     mem := ms1.MEM;
                     mem_domain := forge_m3_prog_addresses cb_end bm_end;
                     pc := FORGE_M3_CAKE_MAIN;
                     lr := 30;
                     align := 2;
                     be := F;
                     failed := F |>`
  \\ qexists_tac `λa. Word (mem_dword ms1.MEM (byte_align a))`
  \\ qexists_tac `FORGE_CAKE_BITMAPS`
  \\ qexists_tac `forge_bitmaps_region_slot bm_end`
  \\ qexists_tac `∅`
  \\ simp [LET_THM]
  \\ `{w | FORGE_HEAP ≤₊ w ∧ w <₊ FORGE_STACKEND} = forge_heap_stack_region` by
       simp [forge_heap_stack_region_def]
  \\ pop_assum SUBST1_TAC
  \\ `LENGTH code ≤ 261936 ∧ LENGTH data ≤ 8189` by
       fs [FORGE_M3_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
  \\ `read_bytearray FORGE_M3_CAKE_MAIN (LENGTH code)
        (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (ms1.MEM a) else NONE) = SOME code` by (
       `read_bytearray FORGE_M3_CAKE_MAIN (LENGTH code)
          (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (ms1.MEM a) else NONE) =
        read_bytearray FORGE_M3_CAKE_MAIN (LENGTH code)
          (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (ms0.MEM a) else NONE)` by (
         irule read_bytearray_cong \\ rpt strip_tac \\ fs []
         \\ qmatch_goalsub_abbrev_tac `ms1.MEM ad`
         \\ `ad ∉ forge_cml_ptrs_region ∧ ad ∉ forge_heap_hdr_region` by (
              `0x004000D0 + i < 18446744073709551616` by decide_tac
              \\ fs [Abbr `ad`, forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
                     FORGE_M3_CAKE_MAIN_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def, FORGE_HEAP_def,
                     word64_add_lo_ls] \\ decide_tac)
         \\ simp [])
       \\ simp [])
  \\ drule m3_real_interfer_ok_slot_imp_erase_ok \\ strip_tac
  \\ rpt conj_tac
  >- (
    simp [targetSemTheory.good_init_state_def, targetSemTheory.target_configured_def,
          targetSemTheory.code_loaded_def, asmPropsTheory.target_state_rel_def,
          Abbr `emc`, erase_mc_def, forge_m3_mc_slot_def,
          arm8_target_exact_def, arm8_targetTheory.arm8_target_def,
          arm8_targetTheory.arm8_config_def, erase_fields]
    \\ rpt conj_tac
    >- fs [sp_ok_def, bits_of_def, Abbr `B`]
    >- (mp_tac (Q.SPECL [`cb_begin`, `cb_end`, `bm_end`, `n0`, `n1`, `n2`, `n3`, `ffi_if`, `inst_if`]
                        forge_m3_mc_slot_start_pc_ok)
        \\ simp [targetSemTheory.start_pc_ok_def, forge_m3_mc_slot_def])
    >- (simp [FORGE_M3_CAKE_MAIN_def] \\ EVAL_TAC)
    >- (qpat_x_assum `interference_ok _ _` mp_tac
        \\ simp [erase_mc_def, forge_m3_mc_slot_def, arm8_target_exact_def, arm8_targetTheory.arm8_target_def])
    >- (qpat_x_assum `ffi_interfer_ok _ _` mp_tac
        \\ simp [erase_mc_def, forge_m3_mc_slot_def, arm8_target_exact_def,
                 arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- (qpat_x_assum `install_interfer_ok _ _ _` mp_tac
        \\ simp [erase_mc_def, forge_m3_mc_slot_def, arm8_target_exact_def,
                 arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- (
      qpat_x_assum `read_bytearray _ _ (λa. if a ∈ _ then SOME (ms1.MEM a) else NONE) = SOME code`
        (mp_tac o MATCH_MP read_bytearray_mem_eq) \\ strip_tac
      \\ irule read_bytearray_imp_bytes_in_mem \\ rpt strip_tac \\ fs []
      \\ first_x_assum drule \\ strip_tac \\ simp []
      \\ `w2n (FORGE_M3_CAKE_MAIN + n2w i) = 0x004000D0 + i` by
           (`0x004000D0 + i < 18446744073709551616` by decide_tac
            \\ simp [FORGE_M3_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64])
      \\ fs [forge_heap_stack_region_def, forge_bitmaps_region_slot_def,
             FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def,
             wordsTheory.WORD_LO, wordsTheory.WORD_LS] \\ decide_tac)
    >- simp [forge_m3_prog_addresses_def, SUBSET_DEF]
    >- simp [forge_m3_prog_addresses_def, SUBSET_DEF]
    >- (
      `bm_end && 7w = 0w` by (
        qpat_assum `FORGE_CAKE_BITMAPS + n2w (8 * LENGTH data) = bm_end` (SUBST1_TAC o SYM)
        \\ REWRITE_TAC [FORGE_CAKE_BITMAPS_def, GSYM wordsTheory.word_mul_n2w]
        \\ blastLib.BBLAST_TAC)
      \\ rpt strip_tac
      \\ fs [forge_heap_stack_region_def, forge_bitmaps_region_slot_def,
             FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def, byte_align_64]
      \\ irule m3_byte_align_in_region \\ simp [])
    >- (
      gen_tac
      \\ `byte_align (byte_align a) = byte_align a` by (simp [byte_align_64] \\ blastLib.BBLAST_TAC)
      \\ simp [GSYM mem_dword_get_byte])
    \\ gen_tac \\ strip_tac
    \\ qabbrev_tac `ad = FORGE_M3_CAKE_MAIN + n2w (n + LENGTH code)`
    \\ `cbsp + (LENGTH code + 0x004000D0) = w2n cb_end` by (
         qpat_x_assum `cbsp + (LENGTH code + w2n FORGE_M3_CAKE_MAIN) = w2n cb_end` mp_tac
         \\ PURE_REWRITE_TAC [FORGE_M3_CAKE_MAIN_def]
         \\ CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV wordsLib.WORD_EVAL_CONV))
         \\ simp [])
    \\ `w2n ad = 0x004000D0 + (n + LENGTH code)` by (
         `0x004000D0 + (n + LENGTH code) < 18446744073709551616` by decide_tac
         \\ simp [Abbr `ad`, FORGE_M3_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64])
    \\ simp [forge_m3_prog_addresses_def, forge_m3_code_region_def, forge_heap_stack_region_def,
             forge_bitmaps_region_slot_def, FORGE_M3_CAKE_MAIN_def, FORGE_HEAP_def, FORGE_STACKEND_def,
             FORGE_CAKE_BITMAPS_def, wordsTheory.WORD_LO, wordsTheory.WORD_LS, dimword_64]
    \\ decide_tac)
  >- simp [FORGE_HEAP_def, byte_aligned_mod8]
  >- simp [FORGE_STACKEND_def, byte_aligned_mod8]
  >- simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8]
  >- (simp [FORGE_HEAP_def, FORGE_STACKEND_def] \\ EVAL_TAC)
  >- (simp [FORGE_HEAP_def, FORGE_STACKEND_def, bytes_in_word_64] \\ EVAL_TAC)
  >- (irule m3_heap_bitmaps_disjoint \\ qpat_x_assum `m3_slot_layout_ok _ _ _` mp_tac
      \\ simp [m3_slot_layout_ok_def, FORGE_DATA_SLOT_END_def])
  >- (`byte_align FORGE_HEAP = FORGE_HEAP` by (simp [FORGE_HEAP_def, byte_align_64] \\ EVAL_TAC) \\ simp [])
  >- (`byte_align (FORGE_HEAP + bytes_in_word) = FORGE_HEAP + 8w` by
        (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC) \\ simp [])
  >- (`byte_align (FORGE_HEAP + 2w * bytes_in_word) = FORGE_HEAP + 16w` by
        (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC) \\ simp [])
  >- (simp [Abbr `emc`, erase_mc_def, forge_m3_mc_slot_def, arm8_target_exact_def,
            arm8_targetTheory.arm8_target_def, erase_fields]
      \\ `byte_align (FORGE_HEAP + 3w * bytes_in_word) = FORGE_HEAP + 24w` by
           (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC) \\ simp [])
  >- (simp [Abbr `emc`, erase_mc_def, forge_m3_mc_slot_def, arm8_target_exact_def,
            arm8_targetTheory.arm8_target_def, erase_fields]
      \\ `byte_align (FORGE_HEAP + 4w * bytes_in_word) = FORGE_HEAP + 32w` by
           (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC) \\ simp [])
  >- (
    simp [m3_word_list_exists_0, set_sepTheory.SEP_CLAUSES]
    \\ `forge_bitmaps_region_slot bm_end =
          {a | FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ FORGE_CAKE_BITMAPS + n2w (8 * LENGTH (MAP ((Word : word64 -> 64 word_loc) o n2w) data))}` by
         simp [forge_bitmaps_region_slot_def]
    \\ pop_assum SUBST1_TAC
    \\ irule word_list_slice
    \\ rpt conj_tac
    >- (
      rpt strip_tac \\ fs [] \\ simp [EL_MAP]
      \\ `byte_align (FORGE_CAKE_BITMAPS + n2w (8 * i)) = FORGE_CAKE_BITMAPS + n2w (8 * i)` by (
           `byte_aligned (FORGE_CAKE_BITMAPS + n2w (8 * i))` by (
             `0x00460018 + 8 * i < 18446744073709551616` by decide_tac
             \\ simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8, wordsTheory.word_add_n2w, w2n_n2w_64]
             \\ `0x00460018 + 8 * i = (573443 + i) * 8` by decide_tac
             \\ pop_assum SUBST1_TAC \\ simp [])
           \\ fs [alignmentTheory.byte_aligned_def, alignmentTheory.aligned_def,
                  alignmentTheory.byte_align_def])
      \\ simp []
      \\ `mem_dword ms1.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) =
          mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i))` by (
           irule mem_dword_cong_util \\ rpt strip_tac \\ first_x_assum irule
           \\ `0x00460018 + (8 * i + j) < 18446744073709551616` by decide_tac
           \\ fs [forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
                  FORGE_CAKE_BITMAPS_def, FORGE_CML_HEAP_def, FORGE_HEAP_def,
                  word_add_n2w_n2w, word64_add_lo_ls] \\ decide_tac)
      \\ simp [])
    >- simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8]
    \\ simp [FORGE_CAKE_BITMAPS_def, dimword_64] \\ decide_tac)
  >- simp [Abbr `emc`, erase_mc_def, forge_m3_mc_slot_def]
  \\ gen_tac \\ strip_tac
  \\ `i = 4` by (
       qpat_x_assum `mmio_pcs_min_index _ = SOME i` mp_tac
       \\ mp_tac (Q.SPECL [`cb_end`, `bm_end`, `n0`, `n1`, `n2`, `n3`, `ffi_if`, `inst_if`]
                          forge_m3_mc_slot_mmio_min)
       \\ simp [Abbr `emc`, erase_mc_def])
  \\ rveq
  \\ simp [Abbr `emc`, erase_mc_def, forge_m3_mc_slot_def, FORGE_M3_CAKE_MAIN_def,
           lab_to_targetTheory.ffi_offset_def, dimword_64]
QED

(* ---- 3. M3 Exit & Install Veneer + Stub Proofs ---- *)

local
  val veneer_exit_th    = prove_m3_step "veneer" 48 0
  val veneer_install_th = prove_m3_step "veneer" 44 0
  val exit_cbz_nz_th    = prove_m3_step "shim" 159 0
  val exit_cbz_z_th     = prove_m3_step "shim" 159 1
  val exit_mov1_th      = prove_m3_step "shim" 160 0
  val exit_mov8_th      = prove_m3_step "shim" 161 0
  val exit_svc_th       = prove_m3_svc0_at "shim" 162
  val inst_mov2_th      = prove_m3_step "shim" 164 0
  val inst_mov8_th      = prove_m3_step "shim" 165 0
  val inst_svc_th       = prove_m3_svc0_at "shim" 166
in

Theorem m3_cake_exit_to_svc_exit_group_slot:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_EXIT_VENEER ⇒
    ∃k.
      let s1 = FUNPOW arm8$Next k s in
        det_run k s s1 ∧
        s1.PC = 0x450288w ∧
        svc_exit_group_rel (if s.REG 0w = 0w then 0w else 1w) s1 ∧
        s1.MEM = s.MEM ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `s.PC = 0x4000C0w` by fs [FORGE_M3_EXIT_VENEER_def]
  \\ Cases_on `s.REG 0w = 0w`
  >- (
    qexists_tac `3`
    \\ qabbrev_tac `s_tgt = s with <|PC := 0x450288w; REG := s.REG⦇8w ↦ 94w⦈; branch_hint := NONE|>`
    \\ `det_run 3 s s_tgt` by
       (step_m3_det veneer_exit_th \\ step_m3_det exit_cbz_z_th \\ step_m3_det exit_mov8_th
        \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
                 combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
    \\ `FUNPOW arm8$Next 3 s = s_tgt` by (drule det_run_funpow \\ simp [])
    \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
    \\ `is_svc0_at (s with <|PC := 0x450288w; REG := s.REG⦇8w ↦ 94w⦈; branch_hint := NONE|>)` by
         (irule exit_svc_th \\ simp [] \\ metis_tac [])
    \\ fs [is_svc0_at_def])
  \\ qexists_tac `4`
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x450288w; REG := s.REG⦇0w ↦ 1w; 8w ↦ 94w⦈; branch_hint := NONE|>`
  \\ `det_run 4 s s_tgt` by
     (step_m3_det veneer_exit_th \\ step_m3_det exit_cbz_nz_th \\ step_m3_det exit_mov1_th \\ step_m3_det exit_mov8_th
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `FUNPOW arm8$Next 4 s = s_tgt` by (drule det_run_funpow \\ simp [])
  \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
  \\ `is_svc0_at (s with <|PC := 0x450288w; REG := s.REG⦇0w ↦ 1w; 8w ↦ 94w⦈; branch_hint := NONE|>)` by
       (irule exit_svc_th \\ simp [] \\ metis_tac [])
  \\ fs [is_svc0_at_def]
QED

Theorem m3_cake_exit_universal_slot:
  ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_EXIT_VENEER ∧
    NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    os_f = os ∧ ec = (if s.REG 0w = 0w then 0w else 1w)
Proof
  rpt strip_tac
  \\ drule_all m3_cake_exit_to_svc_exit_group_slot \\ simp [LET_THM] \\ strip_tac
  \\ drule_all m3_det_run_peel_nrc \\ strip_tac
  \\ drule_all m3_whole_step_nrc_exit_stuck \\ strip_tac
  \\ rveq \\ fs [svc_exit_group_rel_def]
QED

Theorem m3_cake_install_to_svc_exit_group_slot:
  ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_INSTALL_VENEER ⇒
    let s1 = FUNPOW arm8$Next 3 s in
      det_run 3 s s1 ∧
      s1.PC = 0x450298w ∧
      svc_exit_group_rel 2w s1 ∧
      s1.MEM = s.MEM ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac
  \\ `s.PC = 0x4000B0w` by fs [FORGE_M3_INSTALL_VENEER_def]
  \\ qabbrev_tac `s_tgt = s with <|PC := 0x450298w; REG := s.REG⦇0w ↦ 2w; 8w ↦ 94w⦈; branch_hint := NONE|>`
  \\ `det_run 3 s s_tgt` by
     (step_m3_det veneer_install_th \\ step_m3_det inst_mov2_th \\ step_m3_det inst_mov8_th
      \\ simp [det_run_def, Abbr `s_tgt`, arm8Theory.arm8_state_component_equality,
               combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] \\ rw [] \\ fs [])
  \\ `FUNPOW arm8$Next 3 s = s_tgt` by (drule det_run_funpow \\ simp [])
  \\ simp [] \\ simp [Abbr `s_tgt`, svc_exit_group_rel_def, combinTheory.APPLY_UPDATE_THM, bits_of_def]
  \\ `is_svc0_at (s with <|PC := 0x450298w; REG := s.REG⦇0w ↦ 2w; 8w ↦ 94w⦈; branch_hint := NONE|>)` by
       (irule inst_svc_th \\ simp [] \\ metis_tac [])
  \\ fs [is_svc0_at_def]
QED

Theorem m3_cake_install_universal_slot:
  ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_INSTALL_VENEER ∧
    NRC (m3_whole_step allow_err) n (os, s) (os_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    os_f = os ∧ ec = 2w
Proof
  rpt strip_tac
  \\ drule_all m3_cake_install_to_svc_exit_group_slot \\ simp [LET_THM] \\ strip_tac
  \\ drule_all m3_det_run_peel_nrc \\ strip_tac
  \\ drule_all m3_whole_step_nrc_exit_stuck \\ strip_tac
  \\ rveq \\ fs [svc_exit_group_rel_def]
QED

end;
