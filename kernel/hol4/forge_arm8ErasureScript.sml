(*
  Forge Milestone 1: ARMv8 Processor-Bit Erasure & Real-Bits Lift
  Closes M1-B False Premise #1 (arm8_ok requires TBI0 = F, TBI1 = F, SA0 = F,
  whereas real Linux/macOS ARM64 kernels set TBI0 = T and SA0 = T).

  Proves:
    1. BranchTo_erase_untagged, CheckSPAlignment_erase (+ negative controls N1a..N4, P1)
    2. Next_frame, NextStateARM8_frame (L3 never modifies TCR_EL1, SCTLR_EL1, PSTATE.EL)
    3. Next_erase, NextStateARM8_erase, NextStateARM8_restore (full L3 step erasure)
    4. real_mc_evaluate_eq and machine_sem_real_eq lifting CakeML arm8_target
       machine_sem to real Linux EL0 processor bits (TBI0=T, TBI1=F, SA0=T)
       under untagged addresses (lo55) and 16-byte aligned SP_EL0.
*)
Theory forge_arm8Erasure
Ancestors
  words arm8 arm8_step targetSem arm8_target alignment state_transformer
Libs
  preamble wordsLib blastLib

(* ---- Definitions ---- *)

Definition erase_def:
  erase (s:arm8_state) =
    s with <| TCR_EL1   := s.TCR_EL1 with <| TBI0 := F; TBI1 := F |>;
              SCTLR_EL1 := s.SCTLR_EL1 with SA0 := F |>
End

Definition bits_of_def:
  bits_of (s:arm8_state) = (s.TCR_EL1.TBI0, s.TCR_EL1.TBI1, s.SCTLR_EL1.SA0)
End

Definition restore_def:
  restore (B:bool # bool # bool) (s:arm8_state) =
    s with <| TCR_EL1   := s.TCR_EL1 with <| TBI0 := FST B; TBI1 := FST (SND B) |>;
              SCTLR_EL1 := s.SCTLR_EL1 with SA0 := SND (SND B) |>
End

Definition untagged_def:
  untagged (a:word64) ⇔ ((63 >< 55) a = (0w:word9))
End

Definition sp_ok_def:
  sp_ok (s:arm8_state) ⇔
    s.PSTATE.EL = 0w ∧ (¬s.SCTLR_EL1.SA0 ∨ aligned 4 s.SP_EL0)
End

Definition tbi_pc_def:
  tbi_pc (tcr:TCR_EL1) (t:word64) =
    let s0 = if word_bit 55 t ∧ tcr.TBI1 then bit_field_insert 63 56 (255w:word8) t else t in
      if ¬word_bit 55 s0 ∧ tcr.TBI0 then bit_field_insert 63 56 (0w:word8) s0 else s0
End

Definition erase_e0e_def:
  erase_e0e (s:arm8_state) = (erase s) with SCTLR_EL1 := (erase s).SCTLR_EL1 with E0E := F
End

Definition lo55_def:
  lo55 (mc : (64, 'b, 'c) machine_config) ⇔
    ∀a. a ∈ mc.prog_addresses ∨ a = mc.halt_pc ∨ a = mc.install_pc ∨ MEM a mc.ffi_entry_pcs ⇒
        untagged a
End

Definition arm8_target_real_def:
  arm8_target_real (B : bool # bool # bool) =
    arm8_target with <|
      next := arm8$Next;
      state_ok := λms. arm8_ok (erase ms) ∧ bits_of ms = B ∧
                       (¬SND (SND B) ∨ aligned 4 ms.SP_EL0)
    |>
End

Definition real_mc_def:
  real_mc (B : bool # bool # bool) (mc : (64, arm8_state, 'c) machine_config) =
    mc with <|
      target := arm8_target_real B;
      next_interfer := λk ms. restore B (mc.next_interfer k (erase ms));
      ffi_interfer := λk (i, bs, ms). restore B (mc.ffi_interfer k (i, bs, erase ms));
      install_interfer := λk (bs, ms). restore B (mc.install_interfer k (bs, erase ms))
    |>
End

Definition interfer_sp_bits_ok_def:
  interfer_sp_bits_ok (mc : (64, arm8_state, 'c) machine_config) ⇔
    (∀k s. aligned 4 s.SP_EL0 ⇒ aligned 4 (mc.next_interfer k s).SP_EL0) ∧
    (∀k s. erase s = s ⇒ erase (mc.next_interfer k s) = mc.next_interfer k s) ∧
    (∀k i bs s. aligned 4 s.SP_EL0 ⇒ aligned 4 (mc.ffi_interfer k (i, bs, s)).SP_EL0) ∧
    (∀k i bs s. erase s = s ⇒ erase (mc.ffi_interfer k (i, bs, s)) = mc.ffi_interfer k (i, bs, s)) ∧
    (∀k bs s. aligned 4 s.SP_EL0 ⇒ aligned 4 (mc.install_interfer k (bs, s)).SP_EL0) ∧
    (∀k bs s. erase s = s ⇒ erase (mc.install_interfer k (bs, s)) = mc.install_interfer k (bs, s))
End

(* ---- 1. Field & round-trip lemmas ---- *)

Theorem erase_fields:
  ∀s.
    (erase s).PC = s.PC ∧ (erase s).REG = s.REG ∧ (erase s).MEM = s.MEM ∧
    (erase s).SP_EL0 = s.SP_EL0 ∧ (erase s).PSTATE = s.PSTATE ∧
    (erase s).exception = s.exception ∧ (erase s).branch_hint = s.branch_hint ∧
    (erase s).SCTLR_EL1.A = s.SCTLR_EL1.A ∧ (erase s).SCTLR_EL1.E0E = s.SCTLR_EL1.E0E ∧
    (erase s).SCTLR_EL1.EE = s.SCTLR_EL1.EE ∧ (erase s).SCTLR_EL1.SA = s.SCTLR_EL1.SA ∧
    ¬(erase s).TCR_EL1.TBI0 ∧ ¬(erase s).TCR_EL1.TBI1 ∧ ¬(erase s).SCTLR_EL1.SA0
Proof
  simp [erase_def]
QED

Theorem restore_erase:
  ∀B s. bits_of s = B ⇒ restore B (erase s) = s
Proof
  rw [bits_of_def, restore_def, erase_def]
  \\ simp [arm8_state_component_equality, TCR_EL1_component_equality, SCTLRType_component_equality]
QED

Theorem erase_restore:
  ∀B s. erase (restore B s) = erase s
Proof
  simp [restore_def, erase_def]
QED

Theorem bits_of_restore:
  ∀B s. bits_of (restore B s) = B
Proof
  PairCases \\ simp [bits_of_def, restore_def]
QED

Theorem arm8_ok_erase:
  ∀s. arm8_ok (erase s) ⇔
      s.PSTATE.EL = 0w ∧ ¬s.SCTLR_EL1.E0E ∧ s.exception = NoException ∧ aligned 2 s.PC
Proof
  simp [arm8_ok_def, erase_def]
QED

Theorem untagged_bits:
  ∀t:word64. untagged t ⇒ ¬word_bit 55 t ∧ bit_field_insert 63 56 (0w:word8) t = t
Proof
  rw [untagged_def] \\ blastLib.FULL_BBLAST_TAC
QED

Theorem BranchTo_EL0_pc:
  ∀s t bt. s.PSTATE.EL = 0w ⇒
    BranchTo (t, bt) s = s with <| branch_hint := SOME bt; PC := tbi_pc s.TCR_EL1 t |>
Proof
  rpt strip_tac
  \\ simp [BranchTo_def, Hint_Branch_def, tbi_pc_def, LET_THM, literal_case_THM]
QED

Theorem tbi_pc_erased:
  ∀tcr t. tbi_pc (tcr with <| TBI0 := F; TBI1 := F |>) t = t
Proof
  simp [tbi_pc_def]
QED

Theorem tbi_pc_erase_state:
  ∀s t. tbi_pc (erase s).TCR_EL1 t = t
Proof
  simp [erase_def, tbi_pc_def]
QED

Theorem tbi_pc_untagged:
  ∀tcr t. untagged t ⇒ tbi_pc tcr t = t
Proof
  rpt strip_tac \\ imp_res_tac untagged_bits \\ simp [tbi_pc_def]
QED

Theorem BranchTo_erase_untagged:
  ∀s t bt. s.PSTATE.EL = 0w ∧ untagged t ⇒
    BranchTo (t, bt) (erase s) = erase (BranchTo (t, bt) s)
Proof
  rpt strip_tac
  \\ `(erase s).PSTATE.EL = 0w` by simp [erase_def]
  \\ asm_simp_tac (srw_ss()) [BranchTo_EL0_pc, tbi_pc_untagged]
  \\ simp [erase_def, tbi_pc_erased]
QED

Theorem CheckSPAlignment_erase:
  ∀s. sp_ok s ⇒ CheckSPAlignment (erase s) = erase (CheckSPAlignment s)
Proof
  rw [sp_ok_def, CheckSPAlignment_def, SP_def, erase_def, Aligned] \\ fs []
QED

Theorem CheckSPAlignment_erase_fault:
  ∀s. s.PSTATE.EL = 0w ∧ s.exception = NoException ⇒
    CheckSPAlignment (erase s) = erase s ∧
    (CheckSPAlignment s = s ∨
     (s.SCTLR_EL1.SA0 ∧ ¬aligned 4 s.SP_EL0 ∧
      CheckSPAlignment s = s with exception := ALIGNMENT_FAULT))
Proof
  rw [CheckSPAlignment_def, SP_def, erase_def, Aligned, raise'exception_def] \\ fs []
QED

(* ---- 2. Proved negative & positive controls (E1-0003) ---- *)

Theorem N1a_tagged_branch_breaks:
  ∀s. s.PSTATE.EL = 0w ∧ s.TCR_EL1.TBI0 ⇒
    BranchTo (0x0100000000001000w, BranchType_JMP) (erase s) ≠
    erase (BranchTo (0x0100000000001000w, BranchType_JMP) s)
Proof
  rpt strip_tac
  \\ `(erase s).PSTATE.EL = 0w` by simp [erase_def]
  \\ qpat_x_assum `BranchTo _ _ = _` mp_tac
  \\ asm_simp_tac (srw_ss()) [BranchTo_EL0_pc]
  \\ simp [erase_def, tbi_pc_erased, arm8_state_component_equality, tbi_pc_def]
  \\ Cases_on `s.TCR_EL1.TBI1` \\ EVAL_TAC
QED

Theorem N1b_bit55_branch_breaks:
  ∀s. s.PSTATE.EL = 0w ∧ s.TCR_EL1.TBI1 ⇒
    BranchTo (0x0080000000001000w, BranchType_JMP) (erase s) ≠
    erase (BranchTo (0x0080000000001000w, BranchType_JMP) s)
Proof
  rpt strip_tac
  \\ `(erase s).PSTATE.EL = 0w` by simp [erase_def]
  \\ qpat_x_assum `BranchTo _ _ = _` mp_tac
  \\ asm_simp_tac (srw_ss()) [BranchTo_EL0_pc]
  \\ simp [erase_def, tbi_pc_erased, arm8_state_component_equality, tbi_pc_def]
  \\ Cases_on `s.TCR_EL1.TBI0` \\ EVAL_TAC
QED

Theorem N2_misaligned_sp_breaks:
  ∀s. s.PSTATE.EL = 0w ∧ s.exception = NoException ∧ s.SCTLR_EL1.SA0 ∧ s.SP_EL0 = 8w ⇒
    (CheckSPAlignment (erase s)).exception = NoException ∧
    (CheckSPAlignment s).exception = ALIGNMENT_FAULT
Proof
  rpt strip_tac \\ Cases_on `s.PSTATE.SPS`
  \\ fs [CheckSPAlignment_def, SP_def, erase_def, raise'exception_def, Aligned, literal_case_THM, w2w_id]
  \\ EVAL_TAC
QED

Theorem N3_e0e_not_erasable:
  ∀s. s.PSTATE.EL = 0w ∧ s.SCTLR_EL1.E0E ⇒ BigEndian (erase_e0e s) ≠ BigEndian s
Proof
  rw [BigEndian_def, erase_e0e_def, erase_def]
QED

Theorem P1_bit55_without_TBI1_is_fine:
  ∀s bt. s.PSTATE.EL = 0w ∧ ¬s.TCR_EL1.TBI1 ⇒
    BranchTo (0x0080000000001000w, bt) (erase s) = erase (BranchTo (0x0080000000001000w, bt) s)
Proof
  rpt strip_tac
  \\ `(erase s).PSTATE.EL = 0w` by simp [erase_def]
  \\ asm_simp_tac (srw_ss()) [BranchTo_EL0_pc]
  \\ simp [erase_def, tbi_pc_erased, arm8_state_component_equality, tbi_pc_def]
  \\ Cases_on `s.TCR_EL1.TBI0` \\ EVAL_TAC
QED

Theorem W_linux_bits_nonvacuous:
  ∃s t. arm8_ok (erase s) ∧ s.TCR_EL1.TBI0 ∧ ¬s.TCR_EL1.TBI1 ∧
        s.SCTLR_EL1.SA0 ∧ aligned 4 s.SP_EL0 ∧ untagged t ∧ s.PSTATE.EL = 0w
Proof
  qexists_tac `(ARB:arm8_state) with <| PSTATE := ((ARB:ProcState) with EL := 0w);
                  SCTLR_EL1 := ((ARB:SCTLRType) with <| SA0 := T; E0E := F |>);
                  TCR_EL1 := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
                  SP_EL0 := 0x420000w;
                  exception := NoException; PC := 0x400000w |>`
  \\ qexists_tac `0x400000w`
  \\ simp [arm8_ok_erase, untagged_def] \\ EVAL_TAC
QED

(* ---- 3. Frame lemmas across all L3 ARMv8 definitions (EF-0001) ---- *)

Theorem FOR_proj:
  ∀(p:'s -> 'b) i j (a:num -> 's -> unit # 's).
    (∀k s. p (SND (a k s)) = p s) ⇒ ∀s. p (SND (FOR (i,j,a) s)) = p s
Proof
  gen_tac \\ recInduct FOR_ind \\ rpt strip_tac
  \\ once_rewrite_tac [FOR_def] \\ Cases_on `i = j`
  \\ asm_simp_tac (srw_ss()) [BIND_DEF, UNCURRY, o_THM]
QED

Theorem FOR_snd_const:
  ∀i j (a:num -> 'x # 's -> unit # ('x # 's)).
    (∀k x. SND (SND (a k x)) = SND x) ⇒ ∀x. SND (SND (FOR (i,j,a) x)) = SND x
Proof
  recInduct FOR_ind \\ rpt strip_tac
  \\ once_rewrite_tac [FOR_def] \\ Cases_on `i = j`
  \\ asm_simp_tac (srw_ss()) [BIND_DEF, UNCURRY, o_THM]
QED

Theorem Mem_state:
  ∀a n acc s. SND (arm8$Mem (a, n, acc) s : 'N word # arm8_state) = CheckAlignment (a, n, acc, F) s
Proof
  rpt gen_tac \\ simp [Mem_def, LET_THM, UNCURRY, FOR_snd_const]
QED

Theorem word2_cases:
  ∀w:2 word. w = 0w ∨ w = 1w ∨ w = 2w ∨ w = 3w
Proof
  wordsLib.Cases_word_value \\ simp []
QED

(* Helper: FOR commutes with erase on arm8_state *)
Theorem FOR_erase:
  ∀i j (a:num -> arm8_state -> unit # arm8_state).
    (∀k s. SND (a k (erase s)) = erase (SND (a k s))) ⇒
    ∀s. SND (FOR (i,j,a) (erase s)) = erase (SND (FOR (i,j,a) s))
Proof
  recInduct FOR_ind \\ rpt strip_tac
  \\ once_rewrite_tac [FOR_def] \\ Cases_on `i = j`
  \\ asm_simp_tac (srw_ss()) [BIND_DEF, UNCURRY, o_THM]
QED

Theorem FOR_erase_pair:
  ∀i j (a:num -> 'x # arm8_state -> unit # ('x # arm8_state)).
    (∀k x s. FST (SND (a k (x, erase s))) = FST (SND (a k (x, s))) ∧
             SND (SND (a k (x, erase s))) = erase (SND (SND (a k (x, s))))) ⇒
    ∀x s. FST (SND (FOR (i,j,a) (x, erase s))) = FST (SND (FOR (i,j,a) (x, s))) ∧
          SND (SND (FOR (i,j,a) (x, erase s))) = erase (SND (SND (FOR (i,j,a) (x, s))))
Proof
  recInduct FOR_ind \\ rpt strip_tac
  \\ once_rewrite_tac [FOR_def] \\ Cases_on `i = j`
  \\ asm_simp_tac (srw_ss()) [BIND_DEF, UNCURRY, o_THM]
  \\ `SND (a i (x, erase s)) = (FST (SND (a i (x, s))), erase (SND (SND (a i (x, s)))))` by
       (Cases_on `SND (a i (x, erase s))` \\ first_x_assum (qspecl_then [`i`, `x`, `s`] mp_tac) \\ simp [])
  \\ `SND (a i (x, s)) = (FST (SND (a i (x, s))), SND (SND (a i (x, s))))` by simp []
  \\ simp []
QED

Theorem erase_reads_all:
  ∀s.
    (erase s).MEM = s.MEM ∧ (erase s).PC = s.PC ∧ (erase s).PSTATE = s.PSTATE ∧
    (erase s).REG = s.REG ∧ (erase s).SCTLR_EL2 = s.SCTLR_EL2 ∧
    (erase s).SCTLR_EL3 = s.SCTLR_EL3 ∧ (erase s).SP_EL0 = s.SP_EL0 ∧
    (erase s).SP_EL1 = s.SP_EL1 ∧ (erase s).SP_EL2 = s.SP_EL2 ∧
    (erase s).SP_EL3 = s.SP_EL3 ∧ (erase s).TCR_EL2 = s.TCR_EL2 ∧
    (erase s).TCR_EL3 = s.TCR_EL3 ∧ (erase s).branch_hint = s.branch_hint ∧
    (erase s).exception = s.exception
Proof
  simp [erase_def]
QED

Theorem erase_upds:
  (∀g s. (erase s) with MEM updated_by g = erase (s with MEM updated_by g)) ∧
  (∀g s. (erase s) with PC updated_by g = erase (s with PC updated_by g)) ∧
  (∀g s. (erase s) with PSTATE updated_by g = erase (s with PSTATE updated_by g)) ∧
  (∀g s. (erase s) with REG updated_by g = erase (s with REG updated_by g)) ∧
  (∀g s. (erase s) with SCTLR_EL2 updated_by g = erase (s with SCTLR_EL2 updated_by g)) ∧
  (∀g s. (erase s) with SCTLR_EL3 updated_by g = erase (s with SCTLR_EL3 updated_by g)) ∧
  (∀g s. (erase s) with SP_EL0 updated_by g = erase (s with SP_EL0 updated_by g)) ∧
  (∀g s. (erase s) with SP_EL1 updated_by g = erase (s with SP_EL1 updated_by g)) ∧
  (∀g s. (erase s) with SP_EL2 updated_by g = erase (s with SP_EL2 updated_by g)) ∧
  (∀g s. (erase s) with SP_EL3 updated_by g = erase (s with SP_EL3 updated_by g)) ∧
  (∀g s. (erase s) with TCR_EL2 updated_by g = erase (s with TCR_EL2 updated_by g)) ∧
  (∀g s. (erase s) with TCR_EL3 updated_by g = erase (s with TCR_EL3 updated_by g)) ∧
  (∀g s. (erase s) with branch_hint updated_by g = erase (s with branch_hint updated_by g)) ∧
  (∀g s. (erase s) with exception updated_by g = erase (s with exception updated_by g))
Proof
  rpt conj_tac \\ rpt gen_tac \\ simp [erase_def]
QED

Theorem SCTLR_erase:
  ∀s.
    (SCTLR (erase s)).A = (SCTLR s).A ∧ (SCTLR (erase s)).SA = (SCTLR s).SA ∧
    (SCTLR (erase s)).EE = (SCTLR s).EE ∧ (SCTLR (erase s)).E0E = (SCTLR s).E0E
Proof
  gen_tac \\ simp [SCTLR_def, TranslationRegime_def, erase_def, literal_case_THM]
  \\ BasicProvers.every_case_tac \\ simp []
QED

Theorem CheckAlignment_frame_EL:
  ∀x s. (CheckAlignment x s).PSTATE.EL = s.PSTATE.EL
Proof
  rpt gen_tac \\ PairCases_on `x`
  \\ rw [CheckAlignment_def, Aligned, raise'exception_def]
QED

Theorem CheckAlignment_erase:
  ∀x s. CheckAlignment x (erase s) = erase (CheckAlignment x s)
Proof
  rpt gen_tac \\ PairCases_on `x`
  \\ simp [CheckAlignment_def, Aligned, raise'exception_def, SCTLR_erase, erase_reads_all]
  \\ BasicProvers.every_case_tac \\ simp [erase_def]
QED

Theorem BigEndian_erase:
  ∀s. BigEndian (erase s) = BigEndian s
Proof
  gen_tac \\ simp [BigEndian_def, SCTLR_erase, erase_fields, erase_reads_all]
QED

Theorem Mem_erase:
  ∀x s.
    FST (arm8$Mem x (erase s) : 'N word # arm8_state) = FST (arm8$Mem x s) ∧
    SND (arm8$Mem x (erase s) : 'N word # arm8_state) = erase (SND (arm8$Mem x s))
Proof
  rpt gen_tac \\ PairCases_on `x`
  \\ simp [Mem_def, LET_THM, UNCURRY, CheckAlignment_erase]
  \\ qabbrev_tac `s1 = CheckAlignment (x0, x1, x2, F) s`
  \\ qmatch_goalsub_abbrev_tac `FOR (0, x1 − 1, body)`
  \\ `∀k (acc:bool list) st.
        FST (SND (body k (acc, erase st))) = FST (SND (body k (acc, st))) ∧
        SND (SND (body k (acc, erase st))) = erase (SND (SND (body k (acc, st))))` by
       simp [Abbr `body`, erase_fields]
  \\ `∀i j acc st.
        FST (SND (FOR (i, j, body) (acc, erase st))) = FST (SND (FOR (i, j, body) (acc, st))) ∧
        SND (SND (FOR (i, j, body) (acc, erase st))) = erase (SND (SND (FOR (i, j, body) (acc, st))))` by
       (rpt gen_tac \\ irule FOR_erase_pair \\ simp [])
  \\ `SND (SND (FOR (0, x1 − 1, body) ([], s1))) = s1` by
       (qspecl_then [`0`, `x1 − 1`, `body`] mp_tac FOR_snd_const
        \\ impl_tac >- simp [Abbr `body`]
        \\ disch_then (qspec_then `([], s1)` mp_tac) \\ simp [])
  \\ simp [BigEndian_erase]
QED

Theorem write_Mem_erase:
  ∀x s. arm8$write'Mem x (erase s) = erase (arm8$write'Mem x s)
Proof
  rpt gen_tac \\ PairCases_on `x`
  \\ simp [write'Mem_def, LET_THM, UNCURRY, CheckAlignment_erase]
  \\ simp [BigEndian_erase]
  \\ qmatch_goalsub_abbrev_tac `FOR (0, x2 − 1, body)`
  \\ `∀k st. SND (body k (erase st)) = erase (SND (body k st))` by
       simp [Abbr `body`, erase_def]
  \\ `∀i j st. SND (FOR (i, j, body) (erase st)) = erase (SND (FOR (i, j, body) st))` by
       (rpt gen_tac \\ irule FOR_erase \\ simp [])
  \\ simp []
QED

local
  val st_ty = ``:arm8_state``
  val s_v = mk_var ("s", st_ty)
  val TCRsel = rator ``(s:arm8_state).TCR_EL1``
  val SCsel  = rator ``(s:arm8_state).SCTLR_EL1``
  val PSsel  = rator ``(s:arm8_state).PSTATE``
  val ELsel  = rator ``(p:ProcState).EL``
  val SNDsel = ``SND : 'p # 'q -> 'q``
  val FSTsel = ``FST : 'p # 'q -> 'p``
  val ERsel  = ``erase``
  fun inst_rand sel th =
    let val th0 = SPEC_ALL th
        val f = rator (lhs (concl th0))
    in INST_TY_TERM (match_term f sel) th0 end
  val arm8_tys =
    List.mapPartial (fn (n, a) => if a = 0 then SOME (mk_thy_type {Thy = "arm8", Tyop = n, Args = []}) else NONE)
      (Theory.types "arm8")
  val case_rands = List.mapPartial (fn ty => total TypeBase.case_rand_of ty) (``:'a option`` :: arm8_tys)
  fun rand_rules sel = List.mapPartial (fn th => total (inst_rand sel) th) (boolTheory.COND_RAND :: case_rands)
  val FR_RAND = List.concat (map rand_rules [TCRsel, SCsel, PSsel, ELsel, SNDsel])
  val ER_OUT  = List.mapPartial (fn th => total (fn t => GSYM (inst_rand ERsel t)) th)
                  (boolTheory.COND_RAND :: case_rands)
  val ER_PAIR = rand_rules FSTsel @ rand_rules SNDsel
  val FOR_proj_inst = List.mapPartial (fn sel => total (ISPEC sel) FOR_proj) [TCRsel, SCsel, PSsel]

  val def_names =
   ["raise'exception_def", "X_def", "write'X_def", "SP_def", "write'SP_def",
    "TranslationRegime_def", "SCTLR_def", "Hint_Branch_def", "BranchTo_def",
    "Align_def", "Aligned_def", "CheckSPAlignment_def", "CheckAlignment_def",
    "BigEndian_def", "ByteList_def", "BigEndianReverse_def", "Mem_def", "write'Mem_def",
    "ConditionTest_def", "ConditionHolds_def", "Ones_def", "Zeros_def", "Replicate_def",
    "HighestSetBit_def", "CountLeadingZeroBits_def", "CountLeadingSignBits_def",
    "Poly32Mod2_loop_def", "Poly32Mod2_def", "AddWithCarry_def", "SetTheFlags_def",
    "DecodeShift_def", "ShiftValue_def", "ShiftReg_def", "ExtendWord_def", "Extend_def",
    "DecodeRegExtend_def", "ExtendValue_def", "ExtendReg_def", "DecodeBitMasks_def",
    "dfn'Address_def", "dfn'AddSubCarry_def", "dfn'AddSubExtendRegister_def",
    "dfn'AddSubImmediate_def", "dfn'AddSubShiftedRegister_def", "dfn'LogicalImmediate_def",
    "dfn'LogicalShiftedRegister_def", "dfn'Shift_def", "dfn'MoveWide_def", "dfn'BitfieldMove_def",
    "dfn'ConditionalCompareImmediate_def", "dfn'ConditionalCompareRegister_def",
    "dfn'ConditionalSelect_def", "dfn'CountLeading_def", "dfn'ExtractRegister_def",
    "dfn'Division_def", "dfn'MultiplyAddSub_def", "dfn'MultiplyAddSubLong_def",
    "dfn'MultiplyHigh_def", "dfn'Reverse_def", "dfn'CRC_def",
    "dfn'BranchConditional_def", "dfn'BranchImmediate_def", "dfn'BranchRegister_def",
    "dfn'CompareAndBranch_def", "dfn'TestBitAndBranch_def",
    "LoadStoreSingle_def", "dfn'LoadStoreImmediate_def", "dfn'LoadStoreRegister_def",
    "dfn'LoadStorePair_def", "ExclusiveMonitorPass_def", "SetExclusiveMonitors_def",
    "ExclusiveMonitorStatus_def", "dfn'LoadStoreAcquire_def", "dfn'LoadStoreAcquirePair_def",
    "dfn'LoadLiteral_def", "dfn'MemoryBarrier_def", "dfn'ClearExclusive_def", "dfn'Hint_def",
    "dfn'Breakpoint_def", "dfn'DebugSwitch_def", "dfn'DebugRestore_def", "dfn'Halt_def",
    "dfn'SystemInstruction_def", "dfn'MoveSystemRegister_def", "dfn'MoveImmediateProcState_def",
    "dfn'SupervisorCall_def", "dfn'HypervisorCall_def", "dfn'SecureMonitorCall_def",
    "dfn'ExceptionReturn_def", "dfn'Unallocated_def", "dfn'Reserved_def",
    "Run_def", "Fetch_def"]

  datatype kind = ST | PR | RD
  fun occ ty = ty = st_ty orelse (not (is_vartype ty) andalso List.exists occ (snd (dest_type ty)))
  fun is_pair_st ty = not (is_vartype ty) andalso
    (case dest_type ty of ("prod", [a, b]) => b = st_ty andalso not (occ a) | _ => false)
  fun res_kind r = if r = st_ty then SOME ST else if is_pair_st r then SOME PR else if occ r then NONE else SOME RD
  fun classify c =
    case total dom_rng (type_of c) of
      NONE => NONE
    | SOME (d, r) =>
        if d = st_ty then Option.map (fn k => (false, k)) (res_kind r)
        else if occ d then NONE
        else (case total dom_rng r of
                SOME (d2, r2) => if d2 = st_ty then Option.map (fn k => (true, k)) (res_kind r2) else NONE
              | NONE => NONE)
  fun cname_of dname = String.substring (dname, 0, size dname - 4)
  fun lookup dname =
    let val cn = cname_of dname
    in case (total prim_mk_const {Thy = "arm8", Name = cn}, total (DB.fetch "arm8") dname) of
         (SOME c, SOME d) => SOME (cn, c, d)
       | _ => NONE
    end
  fun app_of c hasArg = if hasArg then mk_comb (c, mk_var ("x", fst (dom_rng (type_of c)))) else c
  fun vars_of f hasArg = (if hasArg then [rand f] else []) @ [s_v]
  fun out_of k t = if k = PR then pairSyntax.mk_snd t else t
  fun frame_body t =
    list_mk_conj [mk_eq (mk_comb (TCRsel, t), mk_comb (TCRsel, s_v)),
                  mk_eq (mk_comb (SCsel, t), mk_comb (SCsel, s_v)),
                  mk_eq (mk_comb (ELsel, mk_comb (PSsel, t)), mk_comb (ELsel, mk_comb (PSsel, s_v)))]
  fun frame_goal c hasArg k =
    let val f = app_of c hasArg in list_mk_forall (vars_of f hasArg, frame_body (out_of k (mk_comb (f, s_v)))) end

  val frames = ref ([] : thm list)
  fun FRset () = [boolTheory.LET_THM, pairTheory.UNCURRY, pairTheory.pair_CASE_def,
                  boolTheory.literal_case_THM, FOR_proj, FOR_snd_const, Mem_state] @
                 FOR_proj_inst @ FR_RAND @ !frames
  val PC_x = TRY (PairCases_on `x`)
  fun try_tacs goal [] = raise Fail ("tactic failed: " ^ term_to_string goal)
    | try_tacs goal (t::ts) = Tactical.TAC_PROOF (([], goal), t) handle _ => try_tacs goal ts

  fun generic_fr d =
    [rpt gen_tac >> PC_x >> simp (d :: FRset ()),
     rpt gen_tac >> PC_x >> simp (d :: FRset ()) >> BasicProvers.every_case_tac >> simp (FRset ())]
  fun el_fr d =
    [rpt gen_tac >> PC_x >> qspec_then `s.PSTATE.EL` strip_assume_tac word2_cases >>
       simp (d :: Hint_Branch_def :: FRset ())]
  fun run_fr d =
    [rpt gen_tac >> simp [d] >> BasicProvers.every_case_tac >> simp (FRset ())]
  fun frame_tacs cn d =
    if cn = "write'SP" orelse cn = "BranchTo" then el_fr d
    else if cn = "Run" then run_fr d
    else generic_fr d

  val _ = List.app (fn dname =>
    case lookup dname of
      NONE => ()
    | SOME (cn, c, d) =>
        (case classify c of
           SOME (hasArg, ST) =>
             let val th = try_tacs (frame_goal c hasArg ST) (frame_tacs cn d)
             in frames := th :: !frames end
         | SOME (hasArg, PR) =>
             let val th = try_tacs (frame_goal c hasArg PR) (frame_tacs cn d)
             in frames := th :: !frames end
         | _ => ())) def_names

  val next_frame_th =
    try_tacs
      ``∀s. (arm8$Next s).TCR_EL1 = s.TCR_EL1 ∧
            (arm8$Next s).SCTLR_EL1 = s.SCTLR_EL1 ∧
            (arm8$Next s).PSTATE.EL = s.PSTATE.EL``
      [gen_tac >> simp (Next_def :: FRset ())]

  (* ---- Now prove erase-commutation for all non-branch definitions + 5 branch definitions ---- *)
  val branch_fns = ["BranchTo", "dfn'BranchConditional", "dfn'BranchImmediate",
                    "dfn'BranchRegister", "dfn'CompareAndBranch", "dfn'TestBitAndBranch",
                    "Run", "Fetch"]
  val is_branch = fn cn => List.exists (fn b => b = cn) branch_fns

  val erases = ref ([erase_fields, erase_reads_all, erase_upds, CheckSPAlignment_erase] : thm list)
  val sp_ok_EL = try_tacs
    ``∀s. sp_ok s ⇒ s.PSTATE.EL = 0w``
    [simp [sp_ok_def]]
  val PSTATE_EL_COND = try_tacs
    ``∀c a b. (if c then a else b).PSTATE.EL = if c then a.PSTATE.EL else b.PSTATE.EL``
    [rw []]
  val Mem_erase_pair = try_tacs
    ``∀x s.
        (arm8$Mem x (erase s) : 'N word # arm8_state) =
        (FST (arm8$Mem x s), erase (SND (arm8$Mem x s)))``
    [rpt gen_tac >>
     CONV_TAC (LAND_CONV (REWR_CONV (GSYM pairTheory.PAIR))) >>
     simp [Mem_erase]]

  fun ERset () = [boolTheory.LET_THM, pairTheory.UNCURRY, pairTheory.pair_CASE_def,
                  boolTheory.literal_case_THM, sp_ok_EL, PSTATE_EL_COND,
                  FOR_erase, FOR_erase_pair, Mem_state, Mem_erase_pair] @
                 ER_OUT @ ER_PAIR @ !frames @ !erases

  val sp_needed = ["LoadStoreSingle", "dfn'LoadStoreImmediate", "dfn'LoadStoreRegister",
                   "dfn'LoadStorePair", "dfn'LoadStoreAcquire", "dfn'LoadStoreAcquirePair"]
  val needs_sp = fn cn => List.exists (fn x => x = cn) sp_needed

  fun erase_goal cn c hasArg k =
    let val f = app_of c hasArg
        val lhs_tm = mk_comb (f, mk_comb (ERsel, s_v))
        val rhs_tm = mk_comb (f, s_v)
        val body =
          case k of
            RD => mk_eq (lhs_tm, rhs_tm)
          | ST => mk_eq (lhs_tm, mk_comb (ERsel, rhs_tm))
          | PR => mk_conj (mk_eq (pairSyntax.mk_fst lhs_tm, pairSyntax.mk_fst rhs_tm),
                           mk_eq (pairSyntax.mk_snd lhs_tm, mk_comb (ERsel, pairSyntax.mk_snd rhs_tm)))
        val full = if needs_sp cn then mk_imp (``sp_ok ^s_v``, body) else body
    in list_mk_forall (vars_of f hasArg, full) end

  val skip_er = ["CheckSPAlignment", "SCTLR", "CheckAlignment", "BigEndian", "Mem", "write'Mem"]

  val sp_ok_frame = try_tacs
    ``∀s. sp_ok s ⇒ sp_ok (CheckSPAlignment s)``
    [rw [sp_ok_def, CheckSPAlignment_def, SP_def, Aligned, raise'exception_def] >> fs []]
  val _ = erases := [SCTLR_erase, sp_ok_frame, CheckAlignment_erase, BigEndian_erase,
                     Mem_erase, write_Mem_erase] @ !erases

  val _ = List.app (fn dname =>
    case lookup dname of
      NONE => ()
    | SOME (cn, c, d) =>
        if is_branch cn orelse List.exists (fn x => x = cn) skip_er then ()
        else
          (case classify c of
             SOME (hasArg, k) =>
               let val g = erase_goal cn c hasArg k
                   val pre = rpt gen_tac >> PC_x >> (if needs_sp cn then DISCH_TAC else ALL_TAC)
                   val th = try_tacs g
                     [pre >> simp (d :: ERset ()) >> TRY (simp [erase_def]),
                      pre >> simp (d :: ERset ()) >> BasicProvers.every_case_tac >>
                        simp (ERset ()) >> TRY (simp [erase_def]),
                      pre >> qspec_then `s.PSTATE.EL` strip_assume_tac word2_cases >>
                        simp (d :: ERset ()) >>
                        TRY (BasicProvers.every_case_tac >> simp (ERset ())) >>
                        TRY (simp [erase_def, arm8_state_component_equality])]
               in erases := th :: !erases end
           | NONE => ())) def_names

  val fetch_er = try_tacs
    ``∀s.
        FST (Fetch (erase s)) = FST (Fetch s) ∧
        SND (Fetch (erase s)) = erase (SND (Fetch s))``
    [gen_tac >> simp (Fetch_def :: ERset ())]
  val _ = erases := fetch_er :: !erases

  (* Branch instructions: erase commutes whenever the erased post-PC is untagged! *)
  fun branch_goal c =
    let val xv = mk_var ("x", fst (dom_rng (type_of c)))
        val f = mk_comb (c, xv)
        val lhs_tm = mk_comb (f, mk_comb (ERsel, s_v))
        val rhs_tm = mk_comb (f, s_v)
    in list_mk_forall ([xv, s_v],
         mk_imp (mk_conj (``sp_ok ^s_v``, ``untagged (^lhs_tm).PC``),
                 mk_eq (lhs_tm, mk_comb (ERsel, rhs_tm)))) end

  fun branch_exc_goal c =
    let val xv = mk_var ("x", fst (dom_rng (type_of c)))
        val f = mk_comb (c, xv)
        val lhs_tm = mk_comb (f, mk_comb (ERsel, s_v))
        val rhs_tm = mk_comb (f, s_v)
    in list_mk_forall ([xv, s_v],
         mk_imp (``sp_ok ^s_v``,
                 mk_eq (``(^lhs_tm).exception``, ``(^rhs_tm).exception``))) end

  fun branch_nohint_goal c =
    let val xv = mk_var ("x", fst (dom_rng (type_of c)))
        val f = mk_comb (c, xv)
        val lhs_tm = mk_comb (f, mk_comb (ERsel, s_v))
        val rhs_tm = mk_comb (f, s_v)
    in list_mk_forall ([xv, s_v],
         mk_imp (mk_conj (``sp_ok ^s_v``, ``¬IS_SOME (^lhs_tm).branch_hint``),
                 mk_eq (lhs_tm, mk_comb (ERsel, rhs_tm)))) end

  val br_erases = ref ([] : thm list)
  val br_excs = ref ([] : thm list)
  val br_nohints = ref ([] : thm list)
  val _ = List.app (fn dname =>
    case lookup dname of
      NONE => ()
    | SOME (cn, c, d) =>
        let val g = branch_goal c
            val th = try_tacs g
              [rpt gen_tac >> strip_tac >> PC_x >>
               qpat_x_assum `untagged _` mp_tac >>
               simp (d :: BranchTo_EL0_pc :: tbi_pc_erase_state :: tbi_pc_erased :: ERset ()) >>
               TRY (BasicProvers.every_case_tac >>
                    simp (BranchTo_EL0_pc :: tbi_pc_erase_state :: tbi_pc_erased :: tbi_pc_untagged :: ERset ())) >>
               rpt strip_tac >>
               simp (BranchTo_EL0_pc :: tbi_pc_erase_state :: tbi_pc_erased :: tbi_pc_untagged :: ERset ()) >>
               TRY (simp [erase_def])]
            val ge = branch_exc_goal c
            val the = try_tacs ge
              [rpt gen_tac >> strip_tac >> PC_x >>
               simp (d :: BranchTo_EL0_pc :: tbi_pc_erase_state :: ERset ()) >>
               TRY (BasicProvers.every_case_tac >> simp (BranchTo_EL0_pc :: tbi_pc_erase_state :: ERset ()))]
            val gh = branch_nohint_goal c
            val thh = try_tacs gh
              [rpt gen_tac >> strip_tac >> PC_x >>
               qpat_x_assum `¬IS_SOME _` mp_tac >>
               simp (d :: BranchTo_EL0_pc :: tbi_pc_erase_state :: ERset ()) >>
               TRY (BasicProvers.every_case_tac >> simp (BranchTo_EL0_pc :: tbi_pc_erase_state :: ERset ()))]
        in br_erases := th :: !br_erases;
           br_excs := the :: !br_excs;
           br_nohints := thh :: !br_nohints end)
    ["dfn'BranchConditional_def", "dfn'BranchImmediate_def", "dfn'BranchRegister_def",
     "dfn'CompareAndBranch_def", "dfn'TestBitAndBranch_def"]

  (* Prove Run_erase, Run_exception_erase, Next_erase, Next_exception_erase *)
  val run_erase_th = try_tacs
    ``∀ins s. sp_ok s ∧ untagged (Run ins (erase s)).PC ⇒
        Run ins (erase s) = erase (Run ins s)``
    [rpt strip_tac >> Cases_on `ins` >>
     fs (Run_def :: !br_erases @ !erases) >>
     BasicProvers.every_case_tac >>
     fs (Run_def :: !br_erases @ !erases)]

  val run_exc_th = try_tacs
    ``∀ins s. sp_ok s ⇒
        (Run ins (erase s)).exception = (Run ins s).exception``
    [rpt strip_tac >> Cases_on `ins` >>
     fs (Run_def :: !br_excs @ !erases) >>
     BasicProvers.every_case_tac >>
     fs (Run_def :: !br_excs @ !erases)]

  val run_nonbranch_hint = try_tacs
    ``∀ins s. sp_ok s ∧ ¬IS_SOME (Run ins (erase s)).branch_hint ⇒
        Run ins (erase s) = erase (Run ins s)``
    [rpt strip_tac >> Cases_on `ins` >>
     fs (Run_def :: !br_nohints @ !erases) >>
     BasicProvers.every_case_tac >>
     fs (Run_def :: !br_nohints @ !erases)]

  val sp_ok_CheckAlignment = try_tacs
    ``∀x s. sp_ok (CheckAlignment x s) ⇔ sp_ok s``
    [rpt gen_tac >> PairCases_on `x` >>
     rw [sp_ok_def, CheckAlignment_def, Aligned, raise'exception_def]]

  val sp_ok_Fetch = try_tacs
    ``∀s. sp_ok (SND (Fetch s)) ⇔ sp_ok s``
    [gen_tac >> simp [Fetch_def, LET_THM, UNCURRY, Mem_state, sp_ok_CheckAlignment]]

in
  val Next_frame = save_thm ("Next_frame", next_frame_th)
  val Fetch_erase = save_thm ("Fetch_erase", fetch_er)
  val sp_ok_Fetch = save_thm ("sp_ok_Fetch", sp_ok_Fetch)
  val Run_erase = save_thm ("Run_erase", run_erase_th)
  val Run_exception_erase = save_thm ("Run_exception_erase", run_exc_th)
  val Run_nonbranch_hint = save_thm ("Run_nonbranch_hint", run_nonbranch_hint)
end;

Theorem Next_erase:
  ∀s. sp_ok s ∧ untagged (arm8$Next (erase s)).PC ⇒
      arm8$Next (erase s) = erase (arm8$Next s)
Proof
  rpt strip_tac
  \\ qpat_x_assum `untagged _` mp_tac
  \\ simp [Next_def, LET_THM]
  \\ `(erase s) with branch_hint := NONE = erase (s with branch_hint := NONE)` by simp [erase_def]
  \\ `sp_ok (s with branch_hint := NONE)` by fs [sp_ok_def]
  \\ Cases_on `Fetch (s with branch_hint := NONE)`
  \\ rename1 `Fetch (s with branch_hint := NONE) = (v, s1)`
  \\ `Fetch (erase (s with branch_hint := NONE)) = (v, erase s1)` by
       (qspec_then `s with branch_hint := NONE` assume_tac Fetch_erase
        \\ Cases_on `Fetch (erase (s with branch_hint := NONE))` \\ fs [])
  \\ `sp_ok s1` by
       (mp_tac (Q.SPEC `s with branch_hint := NONE` sp_ok_Fetch) \\ simp [])
  \\ simp [UNCURRY]
  \\ Cases_on `(Run (Decode v) (erase s1)).branch_hint = NONE` \\ simp []
  >- (
    strip_tac
    \\ `¬IS_SOME (Run (Decode v) (erase s1)).branch_hint` by simp []
    \\ drule_all Run_nonbranch_hint \\ strip_tac
    \\ `(Run (Decode v) s1).branch_hint = NONE` by metis_tac [erase_fields]
    \\ simp [erase_def])
  \\ strip_tac
  \\ drule_all Run_erase \\ strip_tac
  \\ `(Run (Decode v) s1).branch_hint ≠ NONE` by metis_tac [erase_fields]
  \\ simp []
QED

Theorem Next_exception_erase:
  ∀s. sp_ok s ⇒
      (arm8$Next (erase s)).exception = (arm8$Next s).exception
Proof
  rpt strip_tac
  \\ simp [Next_def, LET_THM]
  \\ `(erase s) with branch_hint := NONE = erase (s with branch_hint := NONE)` by simp [erase_def]
  \\ `sp_ok (s with branch_hint := NONE)` by fs [sp_ok_def]
  \\ Cases_on `Fetch (s with branch_hint := NONE)`
  \\ rename1 `Fetch (s with branch_hint := NONE) = (v, s1)`
  \\ `Fetch (erase (s with branch_hint := NONE)) = (v, erase s1)` by
       (qspec_then `s with branch_hint := NONE` assume_tac Fetch_erase
        \\ Cases_on `Fetch (erase (s with branch_hint := NONE))` \\ fs [])
  \\ `sp_ok s1` by
       (mp_tac (Q.SPEC `s with branch_hint := NONE` sp_ok_Fetch) \\ simp [])
  \\ simp [UNCURRY]
  \\ drule_all Run_exception_erase \\ strip_tac
  \\ Cases_on `(Run (Decode v) (erase s1)).branch_hint = NONE`
  \\ Cases_on `(Run (Decode v) s1).branch_hint = NONE` \\ simp []
QED

Theorem NextStateARM8_frame:
  ∀s t. NextStateARM8 s = SOME t ⇒
    t.TCR_EL1 = s.TCR_EL1 ∧ t.SCTLR_EL1 = s.SCTLR_EL1 ∧ t.PSTATE.EL = s.PSTATE.EL
Proof
  rpt strip_tac \\ gvs [NextStateARM8_def, Next_frame]
QED

Theorem NextStateARM8_erase:
  ∀s. sp_ok s ∧ (∀t. NextStateARM8 (erase s) = SOME t ⇒ untagged t.PC) ⇒
    OPTION_MAP erase (NextStateARM8 s) = NextStateARM8 (erase s)
Proof
  rpt strip_tac \\ simp [NextStateARM8_def]
  \\ drule Next_exception_erase \\ strip_tac
  \\ Cases_on `(Next (erase s)).exception = NoException` \\ fs []
  >- (
    `untagged (Next (erase s)).PC` by (first_x_assum irule \\ simp [NextStateARM8_def])
    \\ drule_all Next_erase \\ simp [])
  \\ metis_tac []
QED

Theorem NextStateARM8_restore:
  ∀s t.
    sp_ok s ∧ NextStateARM8 (erase s) = SOME t ∧ untagged t.PC ⇒
    NextStateARM8 s = SOME (restore (bits_of s) t)
Proof
  rpt strip_tac
  \\ gvs [NextStateARM8_def]
  \\ drule_all Next_erase \\ strip_tac
  \\ `(Next s).exception = NoException` by metis_tac [erase_fields]
  \\ simp []
  \\ `bits_of (Next s) = bits_of s` by simp [bits_of_def, Next_frame]
  \\ metis_tac [restore_erase]
QED

(* ---- 4. Whole-run lift from erased machine_sem to real Linux EL0 processor bits ---- *)

Theorem evaluate_non_error_pc_valid:
  ∀mc ffi ms.
    mc.target = arm8_target ∧
    FST (evaluate mc ffi 1 ms) ≠ Error ⇒
    ms.PC ∈ mc.prog_addresses ∨ ms.PC = mc.halt_pc ∨
    ms.PC = mc.install_pc ∨ MEM ms.PC mc.ffi_entry_pcs
Proof
  rpt strip_tac
  \\ qpat_x_assum `FST _ ≠ Error` mp_tac
  \\ simp [Once evaluate_def, arm8_target_def]
  \\ Cases_on `ms.PC ∈ mc.prog_addresses DIFF set mc.ffi_entry_pcs` \\ fs []
  \\ Cases_on `ms.PC = mc.halt_pc` \\ fs []
  \\ Cases_on `ms.PC = mc.install_pc` \\ fs []
  \\ Cases_on `find_index ms.PC mc.ffi_entry_pcs 0` \\ fs []
  \\ imp_res_tac miscTheory.find_index_is_MEM \\ fs []
QED

Theorem interference_ok_arm8_pc:
  ∀f dm ms.
    interference_ok f (arm8_target.proj dm) ⇒
    (f 0 ms).PC = ms.PC
Proof
  rw [asmPropsTheory.interference_ok_def, arm8_target_def, arm8_proj_def]
  \\ first_x_assum (qspecl_then [`0`, `ms`] mp_tac)
  \\ simp []
QED

Theorem interference_ok_shift:
  ∀f p.
    interference_ok f p ⇒
    interference_ok (λk. f (k + 1)) p
Proof
  rw [asmPropsTheory.interference_ok_def]
QED

Theorem interfer_sp_bits_ok_shifts:
  ∀mc. interfer_sp_bits_ok mc ⇒
    interfer_sp_bits_ok (mc with next_interfer := (λk. mc.next_interfer (k + 1))) ∧
    interfer_sp_bits_ok (mc with ffi_interfer := (λk. mc.ffi_interfer (k + 1))) ∧
    interfer_sp_bits_ok (mc with install_interfer := (λk. mc.install_interfer (k + 1)))
Proof
  rw [interfer_sp_bits_ok_def]
QED

Theorem erase_idem:
  ∀s. erase (erase s) = erase s
Proof
  simp [erase_def]
QED

Theorem shift_seq_1[local]:
  ∀f. misc$shift_seq 1 f = (λk. f (k + 1))
Proof
  simp [FUN_EQ_THM, miscTheory.shift_seq_def]
QED

(* Unconditional safety transfer: zero extra NextStateARM8 / SP_EL0 step premises *)
Theorem real_mc_evaluate_nonerror_eq:
  ∀k mc B ffi ms.
    mc.target = arm8_target ∧
    mc.mmio_info = [] ∧
    lo55 mc ∧
    interference_ok mc.next_interfer (arm8_target.proj mc.prog_addresses) ∧
    interfer_sp_bits_ok mc ∧
    bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    (∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error) ∧
    FST (evaluate (real_mc B mc) ffi k ms) ≠ Error ⇒
    let (res, rms', ffi') = evaluate (real_mc B mc) ffi k ms in
      evaluate mc ffi k (erase ms) = (res, erase rms', ffi') ∧
      bits_of rms' = B ∧ (¬SND (SND B) ∨ aligned 4 rms'.SP_EL0)
Proof
  Induct_on `k`
  >- (rpt gen_tac \\ strip_tac \\ simp [Once evaluate_def] \\ once_rewrite_tac [evaluate_def] \\ simp [])
  \\ rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ PairCases_on `B`
  \\ qpat_x_assum `¬SND (SND _) ∨ _` (assume_tac o SIMP_RULE (srw_ss()) [])
  \\ qpat_x_assum `FST (evaluate (real_mc _ mc) _ _ _) ≠ Error` mp_tac
  \\ once_rewrite_tac [evaluate_def]
  \\ simp [real_mc_def, arm8_target_real_def, erase_fields, arm8_target_def]
  \\ Cases_on `ms.PC ∈ mc.prog_addresses ∧ ¬MEM ms.PC mc.ffi_entry_pcs` \\ simp []
  >- (
    Cases_on `encoded_bytes_in_mem arm8_config ms.PC ms.MEM mc.prog_addresses` \\ simp []
    \\ simp [apply_oracle_def]
    \\ qabbrev_tac `rms2 = restore (B0,B1,B2) (mc.next_interfer 0 (erase (Next ms)))`
    \\ qabbrev_tac `mc1 = mc with next_interfer := (λk'. mc.next_interfer (k' + 1))`
    \\ IF_CASES_TAC \\ simp []
    \\ strip_tac
    \\ qpat_x_assum `(arm8_ok _ ∧ _) ∧ _` (REPEAT_TCL CONJUNCTS_THEN assume_tac)
    \\ `sp_ok ms` by fs [sp_ok_def, arm8_ok_erase, bits_of_def]
    \\ `(Next ms).exception = NoException` by fs [arm8_ok_erase]
    \\ `(Next (erase ms)).exception = NoException` by (drule Next_exception_erase \\ simp [])
    \\ `NextStateARM8 (erase ms) = SOME (Next (erase ms))` by simp [NextStateARM8_def, LET_THM]
    \\ `arm8_next (erase ms) = Next (erase ms)` by simp [arm8_next_def]
    \\ qabbrev_tac `ms2 = mc.next_interfer 0 (Next (erase ms))`
    \\ `arm8_ok (Next (erase ms)) ∧ arm8_ok ms2 ∧
        (∀x. x ∉ mc.prog_addresses ⇒ (Next (erase ms)).MEM x = ms.MEM x) ∧
        ∀j. FST (evaluate mc1 ffi j ms2) ≠ Error` by
      (rpt conj_tac
       >- (qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `1` mp_tac)
           \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def, Abbr `ms2`]
           \\ IF_CASES_TAC \\ fs [])
       >- (qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `1` mp_tac)
           \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def, Abbr `ms2`]
           \\ IF_CASES_TAC \\ fs [])
       >- (qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `1` mp_tac)
           \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def, Abbr `ms2`]
           \\ IF_CASES_TAC \\ fs [])
       \\ gen_tac
       \\ qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `SUC j` mp_tac)
       \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def,
                Abbr `mc1`, Abbr `ms2`, shift_seq_1]
       \\ IF_CASES_TAC \\ fs [])
    \\ `ms2.PC = (Next (erase ms)).PC` by (unabbrev_all_tac \\ drule interference_ok_arm8_pc \\ simp [])
    \\ `untagged (Next (erase ms)).PC` by
      (qspecl_then [`mc1`, `ffi`, `ms2`] mp_tac evaluate_non_error_pc_valid
       \\ simp [Abbr `mc1`] \\ strip_tac \\ fs [lo55_def])
    \\ `Next (erase ms) = erase (Next ms)` by (drule_all Next_erase \\ simp [])
    \\ `erase rms2 = ms2` by
      (simp [Abbr `rms2`, Abbr `ms2`, erase_restore]
       \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
       \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
       \\ qpat_x_assum `∀k s. erase s = s ⇒ _` (qspecl_then [`0`, `erase (Next ms)`] mp_tac)
       \\ simp [erase_idem])
    \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi`, `rms2`] mp_tac)
    \\ (impl_tac
        >- (simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                  interfer_sp_bits_ok_shifts, ETA_THM]
            \\ rpt conj_tac
            >- (qpat_x_assum `lo55 mc` mp_tac \\ simp [lo55_def])
            >- (irule interference_ok_shift \\ qpat_x_assum `interference_ok _ _` mp_tac \\ simp [arm8_target_def])
            >- (qpat_x_assum `FST (evaluate _ _ _ _) ≠ Error` mp_tac \\ simp [shift_seq_1, ETA_THM]))
        \\ simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                 shift_seq_1, ETA_THM]
        \\ `arm8_ok (mc.next_interfer 0 (erase (Next ms))) ∧
            ∀x. x ∉ mc.prog_addresses ⇒ (erase (Next ms)).MEM x = ms.MEM x` by fs [Abbr `ms2`]
        \\ simp [Abbr `ms2`]))
  \\ Cases_on `ms.PC = mc.halt_pc` \\ simp []
  \\ Cases_on `ms.PC = mc.install_pc` \\ simp []
  >- (
    qmatch_goalsub_abbrev_tac `read_ffi_bytearray rmc_tmp`
    \\ `read_ffi_bytearray rmc_tmp mc.ptr_reg mc.len_reg ms =
        read_ffi_bytearray mc mc.ptr_reg mc.len_reg (erase ms)` by
         simp [Abbr `rmc_tmp`, read_ffi_bytearray_def, erase_fields, arm8_target_def]
    \\ Cases_on `read_ffi_bytearray mc mc.ptr_reg mc.len_reg (erase ms)` \\ simp []
    \\ simp [apply_oracle_def]
    \\ strip_tac
    \\ qabbrev_tac `mc1 = mc with install_interfer := (λk'. mc.install_interfer (k' + 1))`
    \\ qabbrev_tac `ms1 = mc.install_interfer 0 (x, erase ms)`
    \\ qabbrev_tac `rms1 = restore (B0,B1,B2) ms1`
    \\ `∀j. FST (evaluate mc1 ffi j ms1) ≠ Error` by
      (gen_tac
       \\ qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `SUC j` mp_tac)
       \\ qpat_x_assum `¬(_ ∧ _)` mp_tac \\ qpat_x_assum `ms.PC ≠ mc.halt_pc` mp_tac
       \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def,
                Abbr `mc1`, Abbr `ms1`, shift_seq_1]
       \\ rw [])
    \\ `erase rms1 = ms1` by
      (simp [Abbr `rms1`, Abbr `ms1`, erase_restore]
       \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
       \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
       \\ qpat_x_assum `∀k bs s. erase s = s ⇒ _` (qspecl_then [`0`, `x`, `erase ms`] mp_tac)
       \\ simp [erase_idem])
    \\ `bits_of rms1 = (B0,B1,B2)` by simp [Abbr `rms1`, bits_of_restore]
    \\ `¬B2 ∨ aligned 4 rms1.SP_EL0` by
      (Cases_on `B2` \\ simp [Abbr `rms1`, restore_def, Abbr `ms1`]
       \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
       \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
       \\ qpat_x_assum `∀k bs s. aligned 4 s.SP_EL0 ⇒ _` irule \\ fs [erase_fields])
    \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi`, `rms1`] mp_tac)
    \\ (impl_tac
        >- (simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                  interfer_sp_bits_ok_shifts, ETA_THM]
            \\ rpt conj_tac
            >- (qpat_x_assum `lo55 mc` mp_tac \\ simp [lo55_def])
            >- (qpat_x_assum `interference_ok _ _` mp_tac \\ simp [arm8_target_def])
            >- (qpat_x_assum `FST (evaluate _ _ _ _) ≠ Error` mp_tac \\ simp [shift_seq_1, ETA_THM]))
        \\ simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                 shift_seq_1, ETA_THM, Abbr `ms1`]))
  \\ Cases_on `find_index ms.PC mc.ffi_entry_pcs 0` \\ simp []
  \\ Cases_on `EL x mc.ffi_names` \\ simp []
  \\ rename1 `EL x mc.ffi_names = ExtCall fnm`
  \\ qmatch_goalsub_abbrev_tac `read_ffi_bytearrays rmc_tmp`
  \\ `read_ffi_bytearrays rmc_tmp ms = read_ffi_bytearrays mc (erase ms)` by
       simp [Abbr `rmc_tmp`, read_ffi_bytearrays_def, read_ffi_bytearray_def,
             erase_fields, arm8_target_def]
  \\ Cases_on `read_ffi_bytearrays mc (erase ms)` \\ simp []
  \\ Cases_on `q` \\ Cases_on `r` \\ simp []
  \\ Cases_on `call_FFI ffi (ExtCall fnm) x' x''` \\ simp []
  \\ rename1 `call_FFI ffi (ExtCall fnm) x' x'' = FFI_return ffi1 new_bs`
  \\ simp [apply_oracle_def]
  \\ strip_tac
  \\ qabbrev_tac `mc1 = mc with ffi_interfer := (λk'. mc.ffi_interfer (k' + 1))`
  \\ qabbrev_tac `ms1 = mc.ffi_interfer 0 (x, new_bs, erase ms)`
  \\ qabbrev_tac `rms1 = restore (B0,B1,B2) ms1`
  \\ `∀j. FST (evaluate mc1 ffi1 j ms1) ≠ Error` by
    (gen_tac
     \\ qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `SUC j` mp_tac)
     \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def,
              Abbr `mc1`, Abbr `ms1`, shift_seq_1]
     \\ rw [])
  \\ `erase rms1 = ms1` by
    (simp [Abbr `rms1`, Abbr `ms1`, erase_restore]
     \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
     \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
     \\ qpat_x_assum `∀k i bs s. erase s = s ⇒ _` (qspecl_then [`0`, `x`, `new_bs`, `erase ms`] mp_tac)
     \\ simp [erase_idem])
  \\ `bits_of rms1 = (B0,B1,B2)` by simp [Abbr `rms1`, bits_of_restore]
  \\ `¬B2 ∨ aligned 4 rms1.SP_EL0` by
    (Cases_on `B2` \\ simp [Abbr `rms1`, restore_def, Abbr `ms1`]
     \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
     \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
     \\ qpat_x_assum `∀k i bs s. aligned 4 s.SP_EL0 ⇒ _` irule \\ fs [erase_fields])
  \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi1`, `rms1`] mp_tac)
  \\ (impl_tac
      >- (simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                interfer_sp_bits_ok_shifts, ETA_THM]
          \\ rpt conj_tac
          >- (qpat_x_assum `lo55 mc` mp_tac \\ simp [lo55_def])
          >- (qpat_x_assum `interference_ok _ _` mp_tac \\ simp [arm8_target_def])
          >- (qpat_x_assum `FST (evaluate _ _ _ _) ≠ Error` mp_tac \\ simp [shift_seq_1, ETA_THM]))
      \\ simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
               shift_seq_1, ETA_THM, Abbr `ms1`])
QED

Theorem machine_sem_real_safety:
  ∀mc B ffi ms b.
    mc.target = arm8_target ∧
    mc.mmio_info = [] ∧
    lo55 mc ∧
    interference_ok mc.next_interfer (arm8_target.proj mc.prog_addresses) ∧
    interfer_sp_bits_ok mc ∧
    bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    ¬machine_sem mc ffi (erase ms) Fail ∧
    b ≠ Fail ∧
    machine_sem (real_mc B mc) ffi ms b ⇒
    machine_sem mc ffi (erase ms) b
Proof
  rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` by
       (qpat_x_assum `¬machine_sem _ _ _ _` mp_tac \\ simp [machine_sem_def])
  \\ qpat_x_assum `b ≠ Fail` mp_tac
  \\ qpat_x_assum `machine_sem (real_mc _ _) _ _ _` mp_tac
  \\ Cases_on `b` \\ simp [machine_sem_def]
  >- (
    disch_then strip_assume_tac \\ conj_tac
    >- (
      gen_tac
      \\ qpat_x_assum `∀k. ∃ms' st'. evaluate (real_mc _ _) _ _ _ = _` (qspec_then `k` strip_assume_tac)
      \\ qspecl_then [`k`, `mc`, `B`, `ffi`, `ms`] mp_tac real_mc_evaluate_nonerror_eq
      \\ simp [] \\ strip_tac
      \\ qexists_tac `erase ms'` \\ qexists_tac `st'` \\ simp [])
    \\ `∀k. (SND (SND (evaluate mc ffi k (erase ms)))).io_events =
            (SND (SND (evaluate (real_mc B mc) ffi k ms))).io_events` by
      (gen_tac
       \\ qpat_x_assum `∀k. ∃ms' st'. evaluate (real_mc _ _) _ _ _ = _` (qspec_then `k` strip_assume_tac)
       \\ qspecl_then [`k`, `mc`, `B`, `ffi`, `ms`] mp_tac real_mc_evaluate_nonerror_eq
       \\ simp [] \\ strip_tac \\ simp [])
    \\ simp [])
  \\ disch_then strip_assume_tac
  \\ qspecl_then [`k`, `mc`, `B`, `ffi`, `ms`] mp_tac real_mc_evaluate_nonerror_eq
  \\ simp [] \\ strip_tac
  \\ qexists_tac `k` \\ qexists_tac `erase ms'` \\ qexists_tac `st'` \\ simp []
QED

(* Full equivalence including ¬Fail when every stepped instruction is fault-free and SP-preserving *)
Theorem real_mc_evaluate_eq:
  ∀k mc B ffi ms.
    mc.target = arm8_target ∧
    mc.mmio_info = [] ∧
    lo55 mc ∧
    interference_ok mc.next_interfer (arm8_target.proj mc.prog_addresses) ∧
    interfer_sp_bits_ok mc ∧
    bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    (∀s. arm8_ok (erase s) ∧ bits_of s = B ∧ (¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧
         s.PC ∈ mc.prog_addresses DIFF set mc.ffi_entry_pcs ∧
         encoded_bytes_in_mem arm8_config s.PC s.MEM mc.prog_addresses ∧
         arm8_ok (arm8_next (erase s)) ⇒
         (Next (erase s)).exception = NoException ∧ aligned 4 (Next s).SP_EL0) ∧
    (∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error) ⇒
    let (res, ms', ffi') = evaluate mc ffi k (erase ms) in
    ∃rms'.
      evaluate (real_mc B mc) ffi k ms = (res, rms', ffi') ∧
      erase rms' = ms' ∧ bits_of rms' = B ∧ (¬SND (SND B) ∨ aligned 4 rms'.SP_EL0)
Proof
  Induct_on `k`
  >- (rpt gen_tac \\ strip_tac \\ once_rewrite_tac [evaluate_def] \\ simp [] \\ qexists_tac `ms` \\ simp [])
  \\ rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ PairCases_on `B`
  \\ qpat_x_assum `¬SND (SND _) ∨ _` (assume_tac o SIMP_RULE (srw_ss()) [])
  \\ `FST (evaluate mc ffi (SUC k) (erase ms)) ≠ Error` by fs []
  \\ once_rewrite_tac [evaluate_def]
  \\ simp [real_mc_def, arm8_target_real_def, erase_fields, arm8_target_def]
  \\ Cases_on `ms.PC ∈ mc.prog_addresses ∧ ¬MEM ms.PC mc.ffi_entry_pcs` \\ simp []
  >- (
    Cases_on `encoded_bytes_in_mem arm8_config ms.PC ms.MEM mc.prog_addresses`
    >- (
      simp [apply_oracle_def]
      \\ `arm8_ok (erase ms) ∧ arm8_ok (arm8_next (erase ms)) ∧
          arm8_ok (mc.next_interfer 0 (arm8_next (erase ms))) ∧
          ∀x. x ∉ mc.prog_addresses ⇒ (arm8_next (erase ms)).MEM x = ms.MEM x` by
        (rpt conj_tac
         \\ qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `1` mp_tac)
         \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def]
         \\ IF_CASES_TAC \\ fs [])
      \\ `(Next (erase ms)).exception = NoException ∧ aligned 4 (Next ms).SP_EL0` by
           (qpat_x_assum `∀s. _ ⇒ _` (qspec_then `ms` mp_tac) \\ simp [IN_DIFF])
      \\ `NextStateARM8 (erase ms) = SOME (Next (erase ms))` by simp [NextStateARM8_def, LET_THM]
      \\ `arm8_next (erase ms) = Next (erase ms)` by simp [arm8_next_def]
      \\ `sp_ok ms` by fs [sp_ok_def, arm8_ok_erase, bits_of_def]
      \\ qabbrev_tac `mc1 = mc with next_interfer := (λk'. mc.next_interfer (k' + 1))`
      \\ qabbrev_tac `ms2 = mc.next_interfer 0 (Next (erase ms))`
      \\ `∀j. FST (evaluate mc1 ffi j ms2) ≠ Error` by
        (gen_tac
         \\ qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `SUC j` mp_tac)
         \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def,
                  Abbr `mc1`, Abbr `ms2`, shift_seq_1]
         \\ IF_CASES_TAC \\ fs [])
      \\ `ms2.PC = (Next (erase ms)).PC` by (unabbrev_all_tac \\ drule interference_ok_arm8_pc \\ simp [])
      \\ `untagged (Next (erase ms)).PC` by
        (qspecl_then [`mc1`, `ffi`, `ms2`] mp_tac evaluate_non_error_pc_valid
         \\ simp [Abbr `mc1`] \\ strip_tac \\ fs [lo55_def])
      \\ `Next (erase ms) = erase (Next ms)` by (drule_all Next_erase \\ simp [])
      \\ `bits_of (Next ms) = (B0,B1,B2)` by fs [bits_of_def, Next_frame]
      \\ qabbrev_tac `rms2 = restore (B0,B1,B2) ms2`
      \\ `erase rms2 = ms2` by
           (simp [Abbr `rms2`, Abbr `ms2`, erase_restore]
            \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
            \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
            \\ qpat_x_assum `∀k s. erase s = s ⇒ _` (qspecl_then [`0`, `erase (Next ms)`] mp_tac)
            \\ simp [erase_idem])
      \\ `bits_of rms2 = (B0,B1,B2)` by simp [Abbr `rms2`, bits_of_restore]
      \\ `aligned 4 ms2.SP_EL0` by
           (simp [Abbr `ms2`] \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
            \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
            \\ qpat_x_assum `∀k s. aligned 4 s.SP_EL0 ⇒ _` (qspecl_then [`0`, `erase (Next ms)`] mp_tac)
            \\ simp [erase_fields])
      \\ `aligned 4 rms2.SP_EL0` by simp [Abbr `rms2`, restore_def]
      \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi`, `rms2`] mp_tac)
      \\ (impl_tac
          >- (simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                    interfer_sp_bits_ok_shifts, ETA_THM]
              \\ rpt conj_tac
              >- (qpat_x_assum `lo55 mc` mp_tac \\ simp [lo55_def])
              >- (irule interference_ok_shift \\ qpat_x_assum `interference_ok _ _` mp_tac \\ simp [arm8_target_def])
              >- (rpt strip_tac \\ qpat_x_assum `∀s. _ ⇒ _` (qspec_then `s` mp_tac) \\ simp [IN_DIFF]))
          \\ `∀x. x ∉ mc.prog_addresses ⇒ (Next ms).MEM x = ms.MEM x` by
               (rpt strip_tac
                \\ `(Next ms).MEM x = (erase (Next ms)).MEM x` by simp [erase_fields]
                \\ pop_assum SUBST1_TAC
                \\ qpat_x_assum `Next (erase ms) = erase (Next ms)` (fn th => SUBST1_TAC (SYM th))
                \\ qpat_x_assum `∀x. x ∉ mc.prog_addresses ⇒ _` (qspec_then `x` mp_tac)
                \\ simp [])
          \\ `arm8_ok (erase (Next ms)) ∧
              arm8_ok (erase (restore (B0,B1,B2) (mc.next_interfer 0 (erase (Next ms))))) ∧
              bits_of (restore (B0,B1,B2) (mc.next_interfer 0 (erase (Next ms)))) = (B0,B1,B2) ∧
              aligned 4 (restore (B0,B1,B2) (mc.next_interfer 0 (erase (Next ms)))).SP_EL0` by
                (rpt conj_tac
                 >- (qpat_x_assum `Next (erase ms) = erase (Next ms)` (fn th => SUBST1_TAC (SYM th)) \\ fs [])
                 >- (qpat_x_assum `Next (erase ms) = erase (Next ms)` (fn th => SUBST1_TAC (SYM th)) \\ fs [Abbr `rms2`, Abbr `ms2`])
                 >- simp [bits_of_restore]
                 >- (qpat_x_assum `Next (erase ms) = erase (Next ms)` (fn th => SUBST1_TAC (SYM th)) \\ fs [Abbr `rms2`, Abbr `ms2`]))
          \\ simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                   shift_seq_1, ETA_THM, erase_fields, Abbr `rms2`, Abbr `ms2`]))
    \\ qpat_x_assum `FST (evaluate mc ffi (SUC k) _) ≠ Error` mp_tac
    \\ simp [Once evaluate_def, arm8_target_def, erase_fields])
  \\ Cases_on `ms.PC = mc.halt_pc` \\ simp [erase_fields]
  \\ Cases_on `ms.PC = mc.install_pc` \\ simp []
  >- (
    qmatch_goalsub_abbrev_tac `read_ffi_bytearray rmc_tmp`
    \\ `read_ffi_bytearray rmc_tmp mc.ptr_reg mc.len_reg ms =
        read_ffi_bytearray mc mc.ptr_reg mc.len_reg (erase ms)` by
         simp [Abbr `rmc_tmp`, read_ffi_bytearray_def, erase_fields, arm8_target_def]
    \\ Cases_on `read_ffi_bytearray mc mc.ptr_reg mc.len_reg (erase ms)`
    >- (qpat_x_assum `FST (evaluate mc ffi (SUC k) _) ≠ Error` mp_tac
        \\ qpat_x_assum `¬(_ ∧ _)` mp_tac \\ qpat_x_assum `ms.PC ≠ mc.halt_pc` mp_tac
        \\ simp [Once evaluate_def, arm8_target_def, erase_fields] \\ rw [])
    \\ simp [apply_oracle_def]
    \\ qabbrev_tac `mc1 = mc with install_interfer := (λk'. mc.install_interfer (k' + 1))`
    \\ qabbrev_tac `ms1 = mc.install_interfer 0 (x, erase ms)`
    \\ qabbrev_tac `rms1 = restore (B0,B1,B2) ms1`
    \\ `∀j. FST (evaluate mc1 ffi j ms1) ≠ Error` by
      (gen_tac \\ qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `SUC j` mp_tac)
       \\ qpat_x_assum `¬(_ ∧ _)` mp_tac \\ qpat_x_assum `ms.PC ≠ mc.halt_pc` mp_tac
       \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def,
                Abbr `mc1`, Abbr `ms1`, shift_seq_1] \\ rw [])
    \\ `erase rms1 = ms1` by
      (simp [Abbr `rms1`, Abbr `ms1`, erase_restore]
       \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
       \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
       \\ qpat_x_assum `∀k bs s. erase s = s ⇒ _` (qspecl_then [`0`, `x`, `erase ms`] mp_tac)
       \\ simp [erase_idem])
    \\ `bits_of rms1 = (B0,B1,B2)` by simp [Abbr `rms1`, bits_of_restore]
    \\ `¬B2 ∨ aligned 4 rms1.SP_EL0` by
      (Cases_on `B2` \\ simp [Abbr `rms1`, restore_def, Abbr `ms1`]
       \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
       \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
       \\ qpat_x_assum `∀k bs s. aligned 4 s.SP_EL0 ⇒ _` irule \\ fs [erase_fields])
    \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi`, `rms1`] mp_tac)
    \\ (impl_tac
        >- (simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                  interfer_sp_bits_ok_shifts, ETA_THM]
            \\ rpt conj_tac
            \\ TRY (qpat_x_assum `lo55 mc` mp_tac \\ simp [lo55_def])
            \\ TRY (qpat_x_assum `interference_ok _ _` mp_tac \\ simp [arm8_target_def])
            \\ TRY (rpt strip_tac \\ qpat_x_assum `∀s. _ ⇒ _` (qspec_then `s` mp_tac) \\ simp [IN_DIFF]))
        \\ simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                 shift_seq_1, ETA_THM, Abbr `rms1`, Abbr `ms1`]))
  \\ Cases_on `find_index ms.PC mc.ffi_entry_pcs 0`
  >- (qpat_x_assum `FST (evaluate mc ffi (SUC k) _) ≠ Error` mp_tac
      \\ simp [Once evaluate_def, arm8_target_def, erase_fields] \\ rw [])
  \\ simp []
  \\ Cases_on `EL x mc.ffi_names` \\ simp []
  >- (
    rename1 `EL x mc.ffi_names = ExtCall fnm`
    \\ qmatch_goalsub_abbrev_tac `read_ffi_bytearrays rmc_tmp`
    \\ `read_ffi_bytearrays rmc_tmp ms = read_ffi_bytearrays mc (erase ms)` by
         simp [Abbr `rmc_tmp`, read_ffi_bytearrays_def, read_ffi_bytearray_def,
               erase_fields, arm8_target_def]
    \\ Cases_on `read_ffi_bytearrays mc (erase ms)`
    \\ Cases_on `q` \\ Cases_on `r`
    >- (qpat_x_assum `FST (evaluate mc ffi (SUC k) _) ≠ Error` mp_tac
        \\ simp [Once evaluate_def, arm8_target_def, erase_fields] \\ rw [])
    >- (qpat_x_assum `FST (evaluate mc ffi (SUC k) _) ≠ Error` mp_tac
        \\ simp [Once evaluate_def, arm8_target_def, erase_fields] \\ rw [])
    >- (qpat_x_assum `FST (evaluate mc ffi (SUC k) _) ≠ Error` mp_tac
        \\ simp [Once evaluate_def, arm8_target_def, erase_fields] \\ rw [])
    \\ simp []
    \\ Cases_on `call_FFI ffi (ExtCall fnm) x' x''` \\ simp []
    \\ rename1 `call_FFI ffi (ExtCall fnm) x' x'' = FFI_return ffi1 new_bs`
    \\ simp [apply_oracle_def]
    \\ qabbrev_tac `mc1 = mc with ffi_interfer := (λk'. mc.ffi_interfer (k' + 1))`
    \\ qabbrev_tac `ms1 = mc.ffi_interfer 0 (x, new_bs, erase ms)`
    \\ qabbrev_tac `rms1 = restore (B0,B1,B2) ms1`
    \\ `∀j. FST (evaluate mc1 ffi1 j ms1) ≠ Error` by
      (gen_tac \\ qpat_x_assum `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` (qspec_then `SUC j` mp_tac)
       \\ simp [Once evaluate_def, arm8_target_def, erase_fields, apply_oracle_def,
                Abbr `mc1`, Abbr `ms1`, shift_seq_1] \\ rw [])
    \\ `erase rms1 = ms1` by
      (simp [Abbr `rms1`, Abbr `ms1`, erase_restore]
       \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
       \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
       \\ qpat_x_assum `∀k i bs s. erase s = s ⇒ _` (qspecl_then [`0`, `x`, `new_bs`, `erase ms`] mp_tac)
       \\ simp [erase_idem])
    \\ `bits_of rms1 = (B0,B1,B2)` by simp [Abbr `rms1`, bits_of_restore]
    \\ `¬B2 ∨ aligned 4 rms1.SP_EL0` by
      (Cases_on `B2` \\ simp [Abbr `rms1`, restore_def, Abbr `ms1`]
       \\ qpat_x_assum `interfer_sp_bits_ok mc` mp_tac
       \\ simp [interfer_sp_bits_ok_def] \\ strip_tac
       \\ qpat_x_assum `∀k i bs s. aligned 4 s.SP_EL0 ⇒ _` irule \\ fs [erase_fields])
    \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi1`, `rms1`] mp_tac)
    \\ (impl_tac
        >- (simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                  interfer_sp_bits_ok_shifts, ETA_THM]
            \\ rpt conj_tac
            \\ TRY (qpat_x_assum `lo55 mc` mp_tac \\ simp [lo55_def])
            \\ TRY (qpat_x_assum `interference_ok _ _` mp_tac \\ simp [arm8_target_def])
            \\ TRY (rpt strip_tac \\ qpat_x_assum `∀s. _ ⇒ _` (qspec_then `s` mp_tac) \\ simp [IN_DIFF]))
        \\ simp [Abbr `mc1`, real_mc_def, arm8_target_real_def, arm8_target_def,
                 shift_seq_1, ETA_THM, Abbr `rms1`, Abbr `ms1`]))
  \\ qpat_x_assum `FST (evaluate mc ffi (SUC k) _) ≠ Error` mp_tac
  \\ simp [Once evaluate_def, arm8_target_def, erase_fields] \\ rw []
QED

Theorem machine_sem_real_eq:
  ∀mc B ffi ms.
    mc.target = arm8_target ∧
    mc.mmio_info = [] ∧
    lo55 mc ∧
    interference_ok mc.next_interfer (arm8_target.proj mc.prog_addresses) ∧
    interfer_sp_bits_ok mc ∧
    bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    (∀s. arm8_ok (erase s) ∧ bits_of s = B ∧ (¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧
         s.PC ∈ mc.prog_addresses DIFF set mc.ffi_entry_pcs ∧
         encoded_bytes_in_mem arm8_config s.PC s.MEM mc.prog_addresses ∧
         arm8_ok (arm8_next (erase s)) ⇒
         (Next (erase s)).exception = NoException ∧ aligned 4 (Next s).SP_EL0) ∧
    ¬machine_sem mc ffi (erase ms) Fail ⇒
    machine_sem (real_mc B mc) ffi ms = machine_sem mc ffi (erase ms)
Proof
  rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ `∀j. FST (evaluate mc ffi j (erase ms)) ≠ Error` by
       (qpat_x_assum `¬machine_sem _ _ _ _` mp_tac \\ simp [machine_sem_def])
  \\ `∀k. ∃rms'.
        evaluate (real_mc B mc) ffi k ms =
          (FST (evaluate mc ffi k (erase ms)), rms', SND (SND (evaluate mc ffi k (erase ms))))` by
       (gen_tac
        \\ qspecl_then [`k`, `mc`, `B`, `ffi`, `ms`] mp_tac real_mc_evaluate_eq
        \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
        \\ Cases_on `evaluate mc ffi k (erase ms)` \\ Cases_on `r`
        \\ simp [] \\ disch_then strip_assume_tac
        \\ qexists_tac `rms'` \\ simp [])
  \\ simp [FUN_EQ_THM] \\ gen_tac
  \\ Cases_on `x` \\ simp [machine_sem_def]
  >- (
    `∀k. (∃ms' st'. evaluate (real_mc B mc) ffi k ms = (TimeOut, ms', st')) ⇔
         (∃ms' st'. evaluate mc ffi k (erase ms) = (TimeOut, ms', st'))` by
      (gen_tac \\ qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac)
       \\ Cases_on `evaluate mc ffi k (erase ms)` \\ Cases_on `r` \\ fs []
       \\ eq_tac \\ disch_then strip_assume_tac \\ fs [])
    \\ `∀k. (SND (SND (evaluate (real_mc B mc) ffi k ms))).io_events =
            (SND (SND (evaluate mc ffi k (erase ms)))).io_events` by
      (gen_tac \\ qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac) \\ simp [])
    \\ simp [])
  >- (
    eq_tac \\ disch_then strip_assume_tac
    >- (
      qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac)
      \\ Cases_on `evaluate mc ffi k (erase ms)` \\ Cases_on `r`
      \\ qpat_x_assum `evaluate (real_mc _ _) _ _ _ = (Halt _, _, _)` mp_tac
      \\ simp [] \\ strip_tac
      \\ qexists_tac `k` \\ qexists_tac `q'` \\ qexists_tac `r'` \\ simp [])
    >- (
      qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac)
      \\ qpat_x_assum `evaluate (real_mc _ _) _ _ _ = _` mp_tac
      \\ simp [] \\ strip_tac
      \\ qexists_tac `k` \\ qexists_tac `rms'` \\ qexists_tac `st'` \\ simp []))
  \\ gen_tac
  \\ qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac)
  \\ qpat_x_assum `∀j. FST (evaluate mc _ _ _) ≠ Error` (qspec_then `k` mp_tac)
  \\ simp []
QED
