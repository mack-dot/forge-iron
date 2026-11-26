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
  words arm8 arm8_step targetSem arm8_target arm8_targetProof asmProps alignment
  state_transformer bitstring forge_contractSpec
Libs
  preamble wordsLib blastLib bitstringLib arm8_targetProofLib

(* ---- Definitions (core erase/bits_of/restore/untagged/sp_ok/lo55/arm8_target_real/real_mc are pinned in forge_contractSpec) ---- *)

Definition tbi_pc_def:
  tbi_pc (tcr:TCR_EL1) (t:word64) =
    let s0 = if word_bit 55 t ∧ tcr.TBI1 then bit_field_insert 63 56 (255w:word8) t else t in
      if ¬word_bit 55 s0 ∧ tcr.TBI0 then bit_field_insert 63 56 (0w:word8) s0 else s0
End

Definition erase_e0e_def:
  erase_e0e (s:arm8_state) = (erase s) with SCTLR_EL1 := (erase s).SCTLR_EL1 with E0E := F
End

Definition arm8_target_exact_def:
  arm8_target_exact (check_sp : bool) =
    arm8_target with <|
      next := arm8$Next;
      state_ok := λms. arm8_ok ms ∧ (¬check_sp ∨ aligned 4 ms.SP_EL0);
      proj := λd ms. (arm8_proj d ms, ms.SP_EL0)
    |>
End

Definition erase_mc_def:
  erase_mc (B : bool # bool # bool) (mc : (64, arm8_state, 'c) machine_config) =
    mc with <|
      target := arm8_target_exact (SND (SND B));
      ffi_interfer := λk (i, bs, s). erase (mc.ffi_interfer k (i, bs, restore B s));
      install_interfer := λk (bs, s). erase (mc.install_interfer k (bs, restore B s))
    |>
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


(* ---- 4. Exact ARMv8 Target (arm8_target_exact) & No-svc0 in Encoded CakeML Code ---- *)

Theorem EXN_COND[local]:
  ∀c (a:arm8_state) b. (if c then a else b).exception = if c then a.exception else b.exception
Proof
  rw []
QED

Theorem SP_COND[local]:
  ∀c (a:arm8_state) b. (if c then a else b).SP_EL0 = if c then a.SP_EL0 else b.SP_EL0
Proof
  rw []
QED

Theorem PC_COND[local]:
  ∀c (a:arm8_state) b. (if c then a else b).PC = if c then a.PC else b.PC
Proof
  rw []
QED

Theorem BH_COND[local]:
  ∀c (a:arm8_state) b. (if c then a else b).branch_hint = if c then a.branch_hint else b.branch_hint
Proof
  rw []
QED

Theorem BranchTo_exn_sp[local]:
  ∀t bt s. (BranchTo (t, bt) s).exception = s.exception ∧ (BranchTo (t, bt) s).SP_EL0 = s.SP_EL0
Proof
  rpt gen_tac \\ qspec_then `s.PSTATE.EL` strip_assume_tac word2_cases
  \\ simp [BranchTo_def, Hint_Branch_def, LET_THM, EXN_COND, SP_COND]
QED

Theorem SetTheFlags_exn_sp[local]:
  ∀x s. (SetTheFlags x s).exception = s.exception ∧ (SetTheFlags x s).SP_EL0 = s.SP_EL0
Proof
  gen_tac \\ PairCases_on `x` \\ simp [SetTheFlags_def, LET_THM, EXN_COND, SP_COND]
QED

Theorem writeX_exn_sp_pc_bh[local]:
  ∀(v:'a word) n s.
    (write'X (v, n) s).exception = s.exception ∧
    (write'X (v, n) s).SP_EL0 = s.SP_EL0 ∧
    (write'X (v, n) s).PC = s.PC ∧
    (write'X (v, n) s).branch_hint = s.branch_hint
Proof
  rpt gen_tac \\ simp [write'X_def, EXN_COND, SP_COND, PC_COND, BH_COND]
QED

Theorem Fetch_arm8_ok:
  ∀s (w:word32).
    arm8_ok s ∧
    s.MEM s.PC = (7 >< 0) w ∧
    s.MEM (s.PC + 1w) = (15 >< 8) w ∧
    s.MEM (s.PC + 2w) = (23 >< 16) w ∧
    s.MEM (s.PC + 3w) = (31 >< 24) w ⇒
    Fetch (s with branch_hint := NONE) = (w, s with branch_hint := NONE)
Proof
  rpt strip_tac
  \\ simp [Fetch_def]
  \\ mp_tac (arm8_stepTheory.mem4 |> DISCH_ALL
             |> Q.INST [`s` |-> `s with branch_hint := NONE`,
                        `address` |-> `s.PC`,
                        `acctype` |-> `AccType_IFETCH`])
  \\ simp [arm8_ok_def, arm8_stepTheory.mem_word_def]
  \\ fs [arm8_ok_def]
  \\ strip_tac \\ simp [] \\ blastLib.BBLAST_TAC
QED

local
  val fast_simps =
    [Run_def, NoOperation_def, dfn'Hint_def, dfn'Address_def,
     dfn'BranchConditional_def, dfn'BranchImmediate_def, dfn'BranchRegister_def,
     dfn'MoveWide_def, dfn'AddSubShiftedRegister_def, dfn'LogicalShiftedRegister_def,
     dfn'BitfieldMove_def, dfn'ExtractRegister_def, dfn'Shift_def, dfn'Division_def,
     dfn'MultiplyHigh_def, dfn'MultiplyAddSub_def, dfn'ConditionalSelect_def,
     dfn'ConditionalCompareImmediate_def, dfn'AddSubCarry_def,
     dfn'AddSubImmediate_def, dfn'LogicalImmediate_def,
     BranchTo_exn_sp, SetTheFlags_exn_sp, writeX_exn_sp_pc_bh,
     EXN_COND, SP_COND, LET_THM, UNCURRY]
in
Theorem safe_nonmem_Run_ok[local]:
  ∀ins s.
    (ins = Hint SystemHintOp_NOP ∨
     (∃a. ins = Address a) ∨
     (∃b. ins = Branch b ∧
          ((∃x. b = BranchConditional x) ∨ (∃x. b = BranchImmediate x) ∨ (∃x. b = BranchRegister x))) ∨
     (∃d. ins = Data d ∧
          ((∃x. d = MoveWide@64 x) ∨
           (∃x. d = AddSubShiftedRegister@64 x) ∨
           (∃x. d = LogicalShiftedRegister@64 x) ∨
           (∃x. d = BitfieldMove@64 x) ∨
           (∃x. d = ExtractRegister@64 x) ∨
           (∃x. d = Shift@64 x) ∨
           (∃x. d = Division@64 x) ∨
           (∃x. d = MultiplyHigh x) ∨
           (∃x. d = MultiplyAddSub@64 x) ∨
           (∃x. d = ConditionalSelect@64 x) ∨
           (∃x. d = ConditionalCompareImmediate@64 x) ∨
           (∃x. d = AddSubCarry@64 x) ∨
           (∃sf subop setflags imm rn rd.
              d = AddSubImmediate@64 (sf, subop, setflags, imm, rn, rd) ∧ (setflags ∨ rd ≠ 31w)) ∨
           (∃sf lop setflags imm rn rd.
              d = LogicalImmediate@64 (sf, lop, setflags, imm, rn, rd) ∧ (setflags ∨ rd ≠ 31w))))) ⇒
    (Run ins s).exception = s.exception ∧ (Run ins s).SP_EL0 = s.SP_EL0
Proof
  rpt strip_tac \\ rveq
  \\ TRY (PairCases_on `a`) \\ TRY (PairCases_on `x`)
  \\ simp fast_simps
  \\ TRY (Cases_on `setflags` \\ simp fast_simps)
  \\ TRY (BasicProvers.every_case_tac \\ simp fast_simps)
QED
end;

local
  val FOR_proj_exn = BETA_RULE (Q.ISPEC `λs:arm8_state. s.exception` FOR_proj)
  val FOR_proj_sp  = BETA_RULE (Q.ISPEC `λs:arm8_state. s.SP_EL0` FOR_proj)
  val FOR_proj_pc  = BETA_RULE (Q.ISPEC `λs:arm8_state. s.PC` FOR_proj)
  val FOR_proj_bh  = BETA_RULE (Q.ISPEC `λs:arm8_state. s.branch_hint` FOR_proj)
in
Theorem lsi_Run_ok[local]:
  ∀s rsw mo sg wbu rtu uo off n t.
    arm8_ok s ∧ n ≠ 31w ⇒
    ((∀sz. aligned 3 (s.REG n + off) ⇒
       let r = Run (LoadStore (LoadStoreImmediate@64 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, n, t))) s in
         r.exception = NoException ∧ r.SP_EL0 = s.SP_EL0 ∧ r.PC = s.PC ∧ r.branch_hint = s.branch_hint) ∧
     (∀sz. aligned 2 (s.REG n + off) ⇒
       let r = Run (LoadStore (LoadStoreImmediate@32 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, n, t))) s in
         r.exception = NoException ∧ r.SP_EL0 = s.SP_EL0 ∧ r.PC = s.PC ∧ r.branch_hint = s.branch_hint) ∧
     (∀sz. aligned 1 (s.REG n + off) ⇒
       let r = Run (LoadStore (LoadStoreImmediate@16 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, n, t))) s in
         r.exception = NoException ∧ r.SP_EL0 = s.SP_EL0 ∧ r.PC = s.PC ∧ r.branch_hint = s.branch_hint) ∧
     (∀sz.
       let r = Run (LoadStore (LoadStoreImmediate@8 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, n, t))) s in
         r.exception = NoException ∧ r.SP_EL0 = s.SP_EL0 ∧ r.PC = s.PC ∧ r.branch_hint = s.branch_hint))
Proof
  rpt strip_tac
  \\ simp [Run_def, dfn'LoadStoreImmediate_def, LoadStoreSingle_def, LET_THM, UNCURRY,
           X_def, EXN_COND, SP_COND, PC_COND, BH_COND, Mem_state]
  \\ Cases_on `mo`
  \\ simp [write'Mem_def, CheckAlignment_def, Aligned, LET_THM, UNCURRY,
           arm8_ok_def, alignmentTheory.aligned_0, EXN_COND, SP_COND, PC_COND, BH_COND, writeX_exn_sp_pc_bh]
  \\ fs [arm8_ok_def, alignmentTheory.aligned_0]
  \\ simp [FOR_proj_exn, FOR_proj_sp, FOR_proj_pc, FOR_proj_bh]
QED
end;

Theorem addsub_imm_Run_ok[local]:
  ∀subop (b:word64) (rn:word5) s.
    arm8_ok s ∧ rn ≠ 31w ⇒
    let r = Run (Data (AddSubImmediate@64 (1w, subop, F, b, rn, 26w))) (s with branch_hint := NONE) in
      r.exception = NoException ∧ r.SP_EL0 = s.SP_EL0 ∧
      r.PC = s.PC ∧ r.branch_hint = NONE ∧
      r.REG 26w = (if subop then s.REG rn - b else s.REG rn + b)
Proof
  rpt strip_tac
  \\ Cases_on `subop`
  \\ simp [Run_def, dfn'AddSubImmediate_def, X_def, write'X_def, AddWithCarry_def,
           SetTheFlags_def, wordsTheory.add_with_carry_def, wordsTheory.WORD_NOT,
           GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
           LET_THM, UNCURRY, combinTheory.APPLY_UPDATE_THM]
  \\ fs [arm8_ok_def]
QED

(* Decode-of-Encode round-trip lemmas for all 20 arm8_ast instruction shapes *)
local
  fun boolify_conv tm =
    if is_comb tm andalso same_const (rator tm) ``boolify32`` then
      (REWR_CONV boolify32_def THENC
       DEPTH_CONV (fn t => if wordsSyntax.is_word_bit t then blastLib.BBLAST_CONV t else NO_CONV t)) tm
    else NO_CONV tm

  val v2w_simps = map bitstringLib.v2w_n2w_CONV
    [``v2w [T] : word1``, ``v2w [F] : word1``,
     ``v2w [F; F] : word2``, ``v2w [F; T] : word2``, ``v2w [T; F] : word2``, ``v2w [T; T] : word2``,
     ``v2w [F; F; F] : word3``, ``v2w [F; F; T] : word3``, ``v2w [F; T; F] : word3``, ``v2w [F; T; T] : word3``,
     ``v2w [T; F; F] : word3``, ``v2w [T; F; T] : word3``, ``v2w [T; T; F] : word3``, ``v2w [T; T; T] : word3``,
     ``v2w [T; T; F; T; F] : word5``]

  val decode_enc_tac =
    simp ([Encode_def, e_data_def, e_branch_def, e_load_store_def, e_sf_def,
           e_LoadStoreImmediate_def, EncodeLogicalOp_def, NoOperation_def,
           ShiftType2num_thm, SystemHintOp2num_thm, LET_THM] @ v2w_simps)
    \\ simp [Decode_def]
    \\ CONV_TAC (DEPTH_CONV boolify_conv)
    \\ simp (v2w_simps @ [arm8_stepTheory.DecodeLogicalOp, arm8Theory.LoadStoreImmediate_def,
                          arm8Theory.LoadStoreImmediateN_def, pairTheory.UNCURRY])
in

Theorem dec_NoOp[local]:
  ∃w. Encode NoOperation = ARM8 w ∧ Decode w = Hint SystemHintOp_NOP
Proof
  decode_enc_tac \\ EVAL_TAC
QED

Theorem dec_MoveWide[local]:
  ∀op hw (imm16:word16) (d:word5).
    ∃w a. Encode (Data (MoveWide@64 (1w, op, hw, imm16, d))) = ARM8 w ∧
          Decode w = Data (MoveWide@64 a)
Proof
  rpt gen_tac \\ Cases_on `op` \\ decode_enc_tac
QED

Theorem dec_LogicalImm[local]:
  ∀lop setflags (imm:word64) (rn:word5) (rd:word5).
    IS_SOME (EncodeBitMask imm) ∧ (setflags ∨ rd ≠ 31w) ∧
    (lop = LogicalOp_AND ∨ lop = LogicalOp_ORR ∨ lop = LogicalOp_EOR) ∧
    (setflags ⇒ lop = LogicalOp_AND) ⇒
    ∃w sf' lop' sf_f imm' rn' rd'.
      Encode (Data (LogicalImmediate@64 (1w, lop, setflags, imm, rn, rd))) = ARM8 w ∧
      Decode w = Data (LogicalImmediate@64 (sf', lop', sf_f, imm', rn', rd')) ∧
      (sf_f ∨ rd' ≠ 31w)
Proof
  rpt strip_tac
  \\ `∃n s r. EncodeBitMask imm = SOME (n, s, r)` by
       (Cases_on `EncodeBitMask imm` \\ fs [] \\ PairCases_on `x` \\ metis_tac [])
  \\ drule (cj 2 arm8_targetProofTheory.Decode_EncodeBitMask) \\ strip_tac
  \\ Cases_on `lop` \\ Cases_on `setflags` \\ fs []
  \\ decode_enc_tac
  \\ simp [arm8_targetProofLib.lem2]
  \\ `v2w [rd ' 4; rd ' 3; rd ' 2; rd ' 1; rd ' 0] = rd` by blastLib.BBLAST_TAC
  \\ simp []
QED

Theorem dec_AddSubShift[local]:
  ∀subop setflags sh (rm:word5) (shamt:word6) (rn:word5) (rd:word5).
    (sh = ShiftType_LSL ∨ sh = ShiftType_ASR) ⇒
    ∃w a. Encode (Data (AddSubShiftedRegister@64 (1w, subop, setflags, sh, rm, shamt, rn, rd))) = ARM8 w ∧
          Decode w = Data (AddSubShiftedRegister@64 a)
Proof
  rpt strip_tac \\ rveq \\ decode_enc_tac
QED

Theorem dec_LogShift[local]:
  ∀lop inv setflags (rm:word5) (rn:word5) (rd:word5).
    (lop = LogicalOp_AND ∨ lop = LogicalOp_ORR ∨ lop = LogicalOp_EOR) ∧
    (setflags ⇒ lop = LogicalOp_AND) ⇒
    ∃w a. Encode (Data (LogicalShiftedRegister@64 (1w, lop, inv, setflags, ShiftType_LSL, 0, rm, rn, rd))) = ARM8 w ∧
          Decode w = Data (LogicalShiftedRegister@64 a)
Proof
  rpt strip_tac \\ Cases_on `lop` \\ Cases_on `setflags` \\ fs [] \\ decode_enc_tac
QED

Theorem dec_AddSubImm[local]:
  ∀subop setflags (imm:word64) (rn:word5) (rd:word5).
    ((~0xFFFw && imm = 0w) ∨ (~0xFFF000w && imm = 0w)) ∧ (setflags ∨ rd ≠ 31w) ⇒
    ∃w sf' sub' sf_f imm' rn' rd'.
      Encode (Data (AddSubImmediate@64 (1w, subop, setflags, imm, rn, rd))) = ARM8 w ∧
      Decode w = Data (AddSubImmediate@64 (sf', sub', sf_f, imm', rn', rd')) ∧
      (sf_f ∨ rd' ≠ 31w)
Proof
  rpt strip_tac
  \\ Cases_on `~0xFFFw && imm = 0w` \\ Cases_on `setflags` \\ fs []
  \\ decode_enc_tac
  \\ `v2w [rd ' 4; rd ' 3; rd ' 2; rd ' 1; rd ' 0] = rd` by blastLib.BBLAST_TAC
  \\ simp []
QED

Theorem dec_AddSubImm_exact[local]:
  ∀subop (b:word64) (rn:word5).
    (~0xFFFw && b = 0w) ⇒
    ∃w. Encode (Data (AddSubImmediate@64 (1w, subop, F, b, rn, 26w))) = ARM8 w ∧
        Decode w = Data (AddSubImmediate@64 (1w, subop, F, b, rn, 26w))
Proof
  rpt strip_tac \\ Cases_on `subop` \\ fs [] \\ decode_enc_tac
  \\ `v2w [rn ' 4; rn ' 3; rn ' 2; rn ' 1; rn ' 0] = rn` by blastLib.BBLAST_TAC
  \\ `w2w (v2w [b ' 11; b ' 10; b ' 9; b ' 8; b ' 7; b ' 6; b ' 5; b ' 4; b ' 3; b ' 2; b ' 1; b ' 0] : word12) = b` by
       (irule arm8_targetProofLib.lem25 \\ fs [])
  \\ simp []
QED

Theorem dec_Bitfield[local]:
  ∀asr_f (wmask:word64) (tmask:word64) r s (rn:word5) (rd:word5).
    r < 64 ∧ s < 64 ∧
    DecodeBitMasks (1w, n2w s, n2w r, F) = SOME (wmask, tmask) ⇒
    ∃w a. Encode (Data (BitfieldMove@64 (1w, T, asr_f, wmask, tmask, r, s, rn, rd))) = ARM8 w ∧
          Decode w = Data (BitfieldMove@64 a)
Proof
  rpt strip_tac
  \\ `∀n:num. v2w [BIT 5 n; BIT 4 n; BIT 3 n; BIT 2 n; BIT 1 n; BIT 0 n] = (n2w n : word6)` by
       (gen_tac
        \\ qspec_then `n2w n : word6` mp_tac (cj 2 arm8_targetProofLib.lem2)
        \\ simp [wordsTheory.word_index])
  \\ `w2n (n2w r : word6) = r ∧ w2n (n2w s : word6) = s` by simp [wordsTheory.w2n_n2w, dimword_6]
  \\ Cases_on `asr_f`
  \\ decode_enc_tac
QED

Theorem dec_Extract[local]:
  ∀(immr:word6) (rm:word5) (rn:word5) (rd:word5).
    ∃w a. Encode (Data (ExtractRegister@64 (1w, immr, rm, rn, rd))) = ARM8 w ∧
          Decode w = Data (ExtractRegister@64 a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_Shift[local]:
  ∀sh (rm:word5) (rn:word5) (rd:word5).
    ∃w a. Encode (Data (Shift@64 (1w, sh, rm, rn, rd))) = ARM8 w ∧
          Decode w = Data (Shift@64 a)
Proof
  rpt gen_tac \\ Cases_on `sh` \\ decode_enc_tac
QED

Theorem dec_Div[local]:
  ∀(rm:word5) (rn:word5) (rd:word5).
    ∃w a. Encode (Data (Division@64 (1w, F, rm, rn, rd))) = ARM8 w ∧
          Decode w = Data (Division@64 a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_MulHi[local]:
  ∀sg (rm:word5) (rn:word5) (rd:word5).
    ∃w a. Encode (Data (MultiplyHigh (sg, rm, rn, rd))) = ARM8 w ∧
          Decode w = Data (MultiplyHigh a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_MulAS[local]:
  ∀subop (rm:word5) (ra:word5) (rn:word5) (rd:word5).
    ∃w a. Encode (Data (MultiplyAddSub@64 (1w, subop, rm, ra, rn, rd))) = ARM8 w ∧
          Decode w = Data (MultiplyAddSub@64 a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_CSel[local]:
  ∀(cond:word4) (rm:word5) (rn:word5) (rd:word5).
    ∃w a. Encode (Data (ConditionalSelect@64 (1w, F, T, cond, rm, rn, rd))) = ARM8 w ∧
          Decode w = Data (ConditionalSelect@64 a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_CCmpI[local]:
  ∀(rn:word5).
    ∃w a. Encode (Data (ConditionalCompareImmediate@64 (1w, F, 0w, 0w, (F, F, T, F), rn))) = ARM8 w ∧
          Decode w = Data (ConditionalCompareImmediate@64 a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_AddC[local]:
  ∀setflags (rm:word5) (rn:word5) (rd:word5).
    ∃w a. Encode (Data (AddSubCarry@64 (1w, F, setflags, rm, rn, rd))) = ARM8 w ∧
          Decode w = Data (AddSubCarry@64 a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_BranchImm[local]:
  ∀(off:word64) bt.
    0xFFFFFFFFF8000000w ≤ off ∧ off ≤ 0x7FFFFFFw ∧ aligned 2 off ∧
    (bt = BranchType_JMP ∨ bt = BranchType_CALL) ⇒
    ∃w a. Encode (Branch (BranchImmediate (off, bt))) = ARM8 w ∧
          Decode w = Branch (BranchImmediate a)
Proof
  rpt strip_tac \\ rveq
  \\ `off = sw2sw ((((27 >< 2) off : 26 word) @@ (0w : word2)) : word28)` by
       (irule arm8_targetProofLib.lem9 \\ simp [])
  \\ decode_enc_tac
QED

Theorem dec_BranchCond[local]:
  ∀(off:word64) (cond:word4).
    0xFFFFFFFFFFF00000w ≤ off ∧ off ≤ 0xFFFFFw ∧ aligned 2 off ⇒
    ∃w a. Encode (Branch (BranchConditional (off, cond))) = ARM8 w ∧
          Decode w = Branch (BranchConditional a)
Proof
  rpt strip_tac
  \\ `off = sw2sw ((((20 >< 2) off : 19 word) @@ (0w : word2)) : 21 word)` by
       (fs [alignmentTheory.aligned_extract] \\ blastLib.FULL_BBLAST_TAC)
  \\ decode_enc_tac
QED

Theorem dec_BranchReg[local]:
  ∀(rn:word5).
    ∃w a. Encode (Branch (BranchRegister (rn, BranchType_JMP))) = ARM8 w ∧
          Decode w = Branch (BranchRegister a)
Proof
  rpt gen_tac \\ decode_enc_tac
QED

Theorem dec_Address[local]:
  ∀(off:word64) (rd:word5).
    sw2sw (INT_MINw:word20) ≤ off ∧ off ≤ sw2sw (INT_MAXw:word20) ⇒
    ∃w a. Encode (Address (F, off, rd)) = ARM8 w ∧
          Decode w = Address a
Proof
  rpt strip_tac
  \\ `sw2sw ((((20 >< 2) off : 19 word) @@ ((1 >< 0) off : word2)) : 21 word) = off` by
       (fs [wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def] \\ blastLib.FULL_BBLAST_TAC)
  \\ simp [Encode_def, LET_THM]
  \\ simp [Decode_def]
  \\ CONV_TAC (DEPTH_CONV boolify_conv)
  \\ simp v2w_simps
QED

Theorem dec_LSI64[local]:
  ∀ls unsigned (off:word64) (rn:word5) (rt:word5).
    (ls = MemOp_LOAD ∨ ls = MemOp_STORE) ∧
    ((unsigned ∧ off = w2w ((11 >< 0) (off >>> 3) : word12) << 3) ∨
     off = sw2sw ((8 >< 0) off : word9)) ⇒
    ∃w sz rsw mo sg wbu rtu uo.
      Encode (LoadStore (LoadStoreImmediate@64 (3w, F, ls, AccType_NORMAL, F, F, F, F, F, unsigned, off, rn, rt))) = ARM8 w ∧
      Decode w = LoadStore (LoadStoreImmediate@64 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, rn, rt))
Proof
  rpt strip_tac
  \\ Cases_on `ls` \\ fs []
  \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ decode_enc_tac
  \\ `v2w [rn ' 4; rn ' 3; rn ' 2; rn ' 1; rn ' 0] = rn ∧
      v2w [rt ' 4; rt ' 3; rt ' 2; rt ' 1; rt ' 0] = rt` by blastLib.BBLAST_TAC
  \\ simp []
  \\ TRY (`w2w (v2w [off ' 14; off ' 13; off ' 12; off ' 11; off ' 10; off ' 9;
                     off ' 8; off ' 7; off ' 6; off ' 5; off ' 4; off ' 3] : word12) << 3 = off` by blastLib.FULL_BBLAST_TAC)
  \\ TRY (`sw2sw (v2w [off ' 8; off ' 7; off ' 6; off ' 5; off ' 4; off ' 3; off ' 2; off ' 1; off ' 0] : word9) = off` by blastLib.FULL_BBLAST_TAC)
  \\ simp []
QED

Theorem dec_LSI32[local]:
  ∀ls unsigned (off:word64) (rn:word5) (rt:word5).
    (ls = MemOp_LOAD ∨ ls = MemOp_STORE) ∧
    ((unsigned ∧ off = w2w ((11 >< 0) (off >>> 2) : word12) << 2) ∨
     off = sw2sw ((8 >< 0) off : word9)) ⇒
    ∃w sz rsw mo sg wbu rtu uo.
      Encode (LoadStore (LoadStoreImmediate@32 (2w, T, ls, AccType_NORMAL, F, F, F, F, F, unsigned, off, rn, rt))) = ARM8 w ∧
      Decode w = LoadStore (LoadStoreImmediate@32 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, rn, rt))
Proof
  rpt strip_tac
  \\ Cases_on `ls` \\ fs []
  \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ decode_enc_tac
  \\ `v2w [rn ' 4; rn ' 3; rn ' 2; rn ' 1; rn ' 0] = rn ∧
      v2w [rt ' 4; rt ' 3; rt ' 2; rt ' 1; rt ' 0] = rt` by blastLib.BBLAST_TAC
  \\ simp []
  \\ TRY (`w2w (v2w [off ' 13; off ' 12; off ' 11; off ' 10; off ' 9; off ' 8;
                     off ' 7; off ' 6; off ' 5; off ' 4; off ' 3; off ' 2] : word12) << 2 = off` by blastLib.FULL_BBLAST_TAC)
  \\ TRY (`sw2sw (v2w [off ' 8; off ' 7; off ' 6; off ' 5; off ' 4; off ' 3; off ' 2; off ' 1; off ' 0] : word9) = off` by blastLib.FULL_BBLAST_TAC)
  \\ simp []
QED

Theorem dec_LSI16[local]:
  ∀ls unsigned (off:word64) (rn:word5) (rt:word5).
    (ls = MemOp_LOAD ∨ ls = MemOp_STORE) ∧
    ((unsigned ∧ off = w2w ((11 >< 0) (off >>> 1) : word12) << 1) ∨
     off = sw2sw ((8 >< 0) off : word9)) ⇒
    ∃w sz rsw mo sg wbu rtu uo.
      Encode (LoadStore (LoadStoreImmediate@16 (1w, T, ls, AccType_NORMAL, F, F, F, F, F, unsigned, off, rn, rt))) = ARM8 w ∧
      Decode w = LoadStore (LoadStoreImmediate@16 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, rn, rt))
Proof
  rpt strip_tac
  \\ Cases_on `ls` \\ fs []
  \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ decode_enc_tac
  \\ `v2w [rn ' 4; rn ' 3; rn ' 2; rn ' 1; rn ' 0] = rn ∧
      v2w [rt ' 4; rt ' 3; rt ' 2; rt ' 1; rt ' 0] = rt` by blastLib.BBLAST_TAC
  \\ simp []
  \\ TRY (`w2w (v2w [off ' 12; off ' 11; off ' 10; off ' 9; off ' 8; off ' 7;
                     off ' 6; off ' 5; off ' 4; off ' 3; off ' 2; off ' 1] : word12) << 1 = off` by blastLib.FULL_BBLAST_TAC)
  \\ TRY (`sw2sw (v2w [off ' 8; off ' 7; off ' 6; off ' 5; off ' 4; off ' 3; off ' 2; off ' 1; off ' 0] : word9) = off` by blastLib.FULL_BBLAST_TAC)
  \\ simp []
QED

Theorem dec_LSI8[local]:
  ∀ls unsigned (off:word64) (rn:word5) (rt:word5).
    (ls = MemOp_LOAD ∨ ls = MemOp_STORE) ∧
    ((unsigned ∧ off = w2w ((11 >< 0) off : word12)) ∨
     off = sw2sw ((8 >< 0) off : word9)) ⇒
    ∃w sz rsw mo sg wbu rtu uo.
      Encode (LoadStore (LoadStoreImmediate@8 (0w, F, ls, AccType_NORMAL, F, F, F, F, F, unsigned, off, rn, rt))) = ARM8 w ∧
      Decode w = LoadStore (LoadStoreImmediate@8 (sz, rsw, mo, AccType_NORMAL, sg, wbu, rtu, F, F, uo, off, rn, rt))
Proof
  rpt strip_tac
  \\ Cases_on `ls` \\ fs []
  \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ decode_enc_tac
  \\ `v2w [rn ' 4; rn ' 3; rn ' 2; rn ' 1; rn ' 0] = rn ∧
      v2w [rt ' 4; rt ' 3; rt ' 2; rt ' 1; rt ' 0] = rt` by blastLib.BBLAST_TAC
  \\ simp []
  \\ TRY (`w2w (v2w [off ' 11; off ' 10; off ' 9; off ' 8; off ' 7; off ' 6;
                     off ' 5; off ' 4; off ' 3; off ' 2; off ' 1; off ' 0] : word12) = off` by blastLib.FULL_BBLAST_TAC)
  \\ TRY (`sw2sw (v2w [off ' 8; off ' 7; off ' 6; off ' 5; off ' 4; off ' 3; off ' 2; off ' 1; off ' 0] : word9) = off` by blastLib.FULL_BBLAST_TAC)
  \\ simp []
QED

end;

(* No-svc #0 for every arm8_ast instruction -> encoded_bytes_in_mem_not_svc0 *)

Theorem top_byte_neq_D4[local]:
  ∀ins. (∀w. Encode ins = ARM8 w ⇒ (31 >< 24) w ≠ (0xD4w:word8)) ⇒
        arm8_encode ins ≠ [1w; 0w; 0w; 0xD4w]
Proof
  rpt strip_tac \\ fs [arm8_encode_def]
  \\ Cases_on `Encode ins` \\ fs []
QED

Theorem no_svc0_all_shapes[local]:
  (arm8_encode NoOperation ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀f imm d. arm8_encode (Address (f, imm, d)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀b. arm8_encode (Branch b) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (LoadStore (LoadStoreImmediate@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (LoadStore (LoadStoreImmediate@32 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (LoadStore (LoadStoreImmediate@16 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (LoadStore (LoadStoreImmediate@8 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (MoveWide@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (LogicalImmediate@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (AddSubShiftedRegister@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (LogicalShiftedRegister@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (AddSubImmediate@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (BitfieldMove@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (ExtractRegister@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (Shift@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (Division@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (MultiplyHigh a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (MultiplyAddSub@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (ConditionalSelect@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (ConditionalCompareImmediate@64 a)) ≠ [1w; 0w; 0w; 0xD4w]) ∧
  (∀a. arm8_encode (Data (AddSubCarry@64 a)) ≠ [1w; 0w; 0w; 0xD4w])
Proof
  rpt conj_tac
  >- (simp [arm8_encode_def, Encode_def, NoOperation_def, SystemHintOp2num_thm] \\ EVAL_TAC)
  >- (rpt gen_tac \\ irule top_byte_neq_D4 \\ gen_tac
      \\ simp [Encode_def, LET_THM] \\ rw [] \\ rpt (pop_assum kall_tac) \\ blastLib.BBLAST_TAC)
  >- (gen_tac \\ irule top_byte_neq_D4 \\ gen_tac
      \\ Cases_on `b` \\ simp [Encode_def, e_branch_def, LET_THM, UNCURRY]
      \\ TRY (PairCases_on `p`) \\ simp [LET_THM]
      \\ TRY (Cases_on `p1`) \\ simp [LET_THM]
      \\ rw [] \\ rpt (pop_assum kall_tac) \\ blastLib.BBLAST_TAC)
  >- (gen_tac \\ irule top_byte_neq_D4 \\ gen_tac \\ PairCases_on `a`
      \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
      \\ rw [] \\ rpt (pop_assum kall_tac) \\ blastLib.BBLAST_TAC)
  >- (gen_tac \\ irule top_byte_neq_D4 \\ gen_tac \\ PairCases_on `a`
      \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
      \\ rw [] \\ rpt (pop_assum kall_tac) \\ blastLib.BBLAST_TAC)
  >- (gen_tac \\ irule top_byte_neq_D4 \\ gen_tac \\ PairCases_on `a`
      \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
      \\ rw [] \\ rpt (pop_assum kall_tac) \\ blastLib.BBLAST_TAC)
  >- (gen_tac \\ irule top_byte_neq_D4 \\ gen_tac \\ PairCases_on `a`
      \\ simp [Encode_def, e_load_store_def, e_LoadStoreImmediate_def, LET_THM]
      \\ rw [] \\ rpt (pop_assum kall_tac) \\ blastLib.BBLAST_TAC)
  \\ (gen_tac \\ irule top_byte_neq_D4 \\ gen_tac \\ PairCases_on `a`
      \\ simp [Encode_def, e_data_def, e_sf_def, EncodeLogicalOp_def, ShiftType2num_thm, LET_THM]
      \\ TRY (IF_CASES_TAC \\ rw [] \\ rpt (pop_assum kall_tac)
              \\ qmatch_goalsub_abbrev_tac `466w @@ lo20` \\ blastLib.BBLAST_TAC \\ NO_TAC)
      \\ BasicProvers.EVERY_CASE_TAC \\ rw []
      \\ rpt (pop_assum kall_tac) \\ blastLib.BBLAST_TAC)
QED

Theorem arm8_encode_LENGTH4[local]:
  ∀ins. LENGTH (arm8_encode ins) = 4
Proof
  gen_tac \\ simp [arm8_encode_def] \\ Cases_on `Encode ins` \\ simp []
QED

Theorem LIST_BIND_arm8_encode_LENGTH[local]:
  ∀l. LENGTH (LIST_BIND l arm8_encode) = 4 * LENGTH l
Proof
  Induct \\ simp [arm8_encode_LENGTH4]
QED

Theorem DROP_LIST_BIND_arm8_encode[local]:
  ∀l k. k < LENGTH l ⇒
    ∃tl. DROP (4 * k) (LIST_BIND l arm8_encode) = arm8_encode (EL k l) ++ tl
Proof
  Induct \\ simp [listTheory.LIST_BIND_def] \\ rpt strip_tac
  \\ Cases_on `k` \\ simp []
  \\ `4 * SUC n = 4 + 4 * n` by decide_tac \\ pop_assum SUBST1_TAC
  \\ simp [GSYM listTheory.LIST_BIND_def, rich_listTheory.DROP_APPEND2, arm8_encode_LENGTH4]
QED

Theorem arm8_ast_no_svc0[local]:
  ∀i ins. MEM ins (arm8_ast i) ⇒ arm8_encode ins ≠ [1w; 0w; 0w; 0xD4w]
Proof
  gen_tac
  \\ asmLib.asm_cases_tac `i`
  \\ rpt strip_tac
  \\ qpat_x_assum `MEM _ _` mp_tac
  \\ simp [arm8_ast_def, arm8_encode_fail_def, arm8_load_store_ast_def,
           arm8_load_store_ast32_def, arm8_load_store_ast16_def, LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ rpt strip_tac \\ gvs [no_svc0_all_shapes]
QED

Theorem encoded_bytes_in_mem_not_svc0:
  ∀s dm. encoded_bytes_in_mem arm8_config s.PC s.MEM dm ⇒ ¬is_svc0_at s
Proof
  rpt strip_tac
  \\ fs [targetSemTheory.encoded_bytes_in_mem_def, arm8_targetTheory.arm8_config_def,
         arm8_targetTheory.arm8_enc_def, LIST_BIND_arm8_encode_LENGTH]
  \\ `k < LENGTH (arm8_ast i)` by decide_tac
  \\ `k * 4 = 4 * k` by decide_tac
  \\ drule DROP_LIST_BIND_arm8_encode \\ strip_tac
  \\ qpat_x_assum `bytes_in_memory _ _ _ _` mp_tac
  \\ simp []
  \\ `arm8_encode (EL k (arm8_ast i)) ≠ [1w; 0w; 0w; 0xD4w]` by
       metis_tac [arm8_ast_no_svc0, listTheory.EL_MEM]
  \\ `LENGTH (arm8_encode (EL k (arm8_ast i))) = 4` by simp [arm8_encode_LENGTH4]
  \\ fs [listTheory.LENGTH_EQ_NUM_compute]
  \\ rpt strip_tac
  \\ gvs [miscTheory.bytes_in_memory_def, is_svc0_at_def, GSYM wordsTheory.WORD_ADD_ASSOC]
QED

(* Step-safety of all non-Mem arm8_ast instructions *)

Theorem bytes_in_mem_encode_fetch[local]:
  ∀ins w s dm.
    arm8_ok s ∧ Encode ins = ARM8 w ∧ bytes_in_memory s.PC (arm8_encode ins) s.MEM dm ⇒
    Fetch (s with branch_hint := NONE) = (w, s with branch_hint := NONE)
Proof
  rpt strip_tac
  \\ irule Fetch_arm8_ok
  \\ gvs [arm8_encode_def, miscTheory.bytes_in_memory_def, GSYM wordsTheory.WORD_ADD_ASSOC]
QED

Theorem Next_of_safe_nonmem[local]:
  ∀ins w s dm.
    arm8_ok s ∧ Encode ins = ARM8 w ∧ bytes_in_memory s.PC (arm8_encode ins) s.MEM dm ∧
    (Decode w = Hint SystemHintOp_NOP ∨
     (∃a. Decode w = Address a) ∨
     (∃b. Decode w = Branch b ∧
          ((∃x. b = BranchConditional x) ∨ (∃x. b = BranchImmediate x) ∨ (∃x. b = BranchRegister x))) ∨
     (∃d. Decode w = Data d ∧
          ((∃x. d = MoveWide@64 x) ∨
           (∃x. d = AddSubShiftedRegister@64 x) ∨
           (∃x. d = LogicalShiftedRegister@64 x) ∨
           (∃x. d = BitfieldMove@64 x) ∨
           (∃x. d = ExtractRegister@64 x) ∨
           (∃x. d = Shift@64 x) ∨
           (∃x. d = Division@64 x) ∨
           (∃x. d = MultiplyHigh x) ∨
           (∃x. d = MultiplyAddSub@64 x) ∨
           (∃x. d = ConditionalSelect@64 x) ∨
           (∃x. d = ConditionalCompareImmediate@64 x) ∨
           (∃x. d = AddSubCarry@64 x) ∨
           (∃sf subop setflags imm rn rd.
              d = AddSubImmediate@64 (sf, subop, setflags, imm, rn, rd) ∧ (setflags ∨ rd ≠ 31w)) ∨
           (∃sf lop setflags imm rn rd.
              d = LogicalImmediate@64 (sf, lop, setflags, imm, rn, rd) ∧ (setflags ∨ rd ≠ 31w))))) ⇒
    (arm8$Next s).exception = NoException ∧ (arm8$Next s).SP_EL0 = s.SP_EL0
Proof
  rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ drule_all bytes_in_mem_encode_fetch \\ strip_tac
  \\ qspecl_then [`Decode w`, `s with branch_hint := NONE`] mp_tac safe_nonmem_Run_ok
  \\ impl_tac >- metis_tac []
  \\ strip_tac
  \\ simp [Next_def, LET_THM]
  \\ IF_CASES_TAC \\ fs [arm8_ok_def]
QED

Theorem reg_lt31_neq_31w[local]:
  (∀r:num. r < 32 ∧ r ≠ 31 ⇒ (n2w r : word5) ≠ 31w) ∧
  (∀r:num. r < 31 ⇒ (n2w r : word5) ≠ 31w)
Proof
  conj_tac \\ rpt strip_tac
  \\ qpat_x_assum `n2w r = 31w` (mp_tac o AP_TERM ``w2n : word5 -> num``)
  \\ simp [wordsTheory.w2n_n2w, EVAL ``dimword (:5)``, EVAL ``w2n (31w : word5)``]
QED

Theorem int_divides_4_i2w[local]:
  ∀i:int. 4 int_divides i ⇒ (i2w i : word64) && 3w = 0w
Proof
  rpt strip_tac
  \\ `∀w:word64. -(w * 4w) && 3w = 0w ∧ (w * 4w) && 3w = 0w` by blastLib.BBLAST_TAC
  \\ qpat_x_assum `4 int_divides i` (strip_assume_tac o REWRITE_RULE [integerTheory.INT_DIVIDES])
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ rename1 `k * 4`
  \\ simp [integer_wordTheory.i2w_def]
  \\ IF_CASES_TAC
  >- (`∃n. -(k * 4) = &(n * 4)` by
        (Cases_on `k` \\ TRY (qexists_tac `n` \\ intLib.ARITH_TAC) \\ intLib.ARITH_TAC)
      \\ simp [integerTheory.NUM_OF_INT]
      \\ first_x_assum (qspec_then `n2w n` (mp_tac o REWRITE_RULE [wordsTheory.word_mul_n2w]))
      \\ simp [])
  \\ `∃n. k * 4 = &(n * 4)` by
       (Cases_on `k` \\ TRY (qexists_tac `n` \\ intLib.ARITH_TAC) \\ qexists_tac `0` \\ intLib.ARITH_TAC)
  \\ simp [integerTheory.NUM_OF_INT]
  \\ first_x_assum (qspec_then `n2w n` (mp_tac o REWRITE_RULE [wordsTheory.word_mul_n2w]))
  \\ simp []
QED

Theorem branch_offset_i2w_local[local]:
  (∀i. -134217728 ≤ i ∧ i ≤ 134217727 ∧ 4 int_divides i ⇒
       0xFFFFFFFFF8000000w ≤ (i2w i : word64) ∧ (i2w i : word64) ≤ 0x7FFFFFFw ∧ aligned 2 (i2w i : word64)) ∧
  (∀i. -1048572 ≤ i ∧ i ≤ 1048579 ∧ 4 int_divides i ⇒
       0xFFFFFFFFFFF00000w ≤ (i2w i : word64) - 4w ∧ (i2w i : word64) - 4w ≤ 0xFFFFFw ∧
       aligned 2 ((i2w i : word64) - 4w))
Proof
  conj_tac \\ gen_tac \\ disch_then strip_assume_tac
  \\ `(i2w i : word64) && 3w = 0w` by imp_res_tac int_divides_4_i2w
  \\ `w2i (i2w i : word64) = i` by
       (irule integer_wordTheory.w2i_i2w
        \\ simp [integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
                 EVAL ``words$INT_MIN (:64)``, EVAL ``words$INT_MAX (:64)``]
        \\ intLib.ARITH_TAC)
  >- (
    `w2i (0xFFFFFFFFF8000000w : word64) = -134217728 ∧ w2i (0x7FFFFFFw : word64) = 134217727` by EVAL_TAC
    \\ simp [integer_wordTheory.WORD_LEi, alignmentTheory.aligned_bitwise_and]
    \\ intLib.ARITH_TAC)
  \\ `0xFFFFFFFFFFF00004w ≤ (i2w i : word64) ∧ (i2w i : word64) ≤ 0x100003w` by
       (`w2i (0xFFFFFFFFFFF00004w : word64) = -1048572 ∧ w2i (0x100003w : word64) = 1048579` by EVAL_TAC
        \\ simp [integer_wordTheory.WORD_LEi] \\ intLib.ARITH_TAC)
  \\ simp [alignmentTheory.aligned_bitwise_and]
  \\ rpt (qpat_x_assum `w2i _ = _` kall_tac)
  \\ qpat_x_assum `0xFFFFFFFFFFF00004w ≤ _` mp_tac
  \\ qpat_x_assum `_ ≤ 0x100003w` mp_tac
  \\ qpat_x_assum `_ && 3w = 0w` mp_tac
  \\ blastLib.BBLAST_TAC
QED

Theorem arm8_ast_nonmem_step_ok[local]:
  ∀i ins s dm.
    asm_ok i arm8_config ∧ (∀op r ad. i ≠ Inst (Mem op r ad)) ∧
    MEM ins (arm8_ast i) ∧ arm8_ok s ∧ bytes_in_memory s.PC (arm8_encode ins) s.MEM dm ⇒
    (arm8$Next s).exception = NoException ∧ (arm8$Next s).SP_EL0 = s.SP_EL0
Proof
  let
    fun find_enc_ins asl =
      let
        fun get_ins tm =
          let val (f, args) = strip_comb tm in
            if is_const f andalso fst (dest_const f) = "bytes_in_memory" andalso length args = 4 then
              let val (ef, eargs) = strip_comb (el 2 args) in
                if is_const ef andalso fst (dest_const ef) = "arm8_encode" andalso length eargs = 1 then
                  SOME (hd eargs)
                else NONE
              end
            else NONE
          end
      in
        case List.mapPartial get_ins asl of
          ins :: _ => ins
        | [] => raise mk_HOL_ERR "forge_arm8Erasure" "find_enc_ins" "not found"
      end
    val branch_cond_thm =
      REWRITE_RULE [wordsTheory.word_sub_def, EVAL ``-(4w:word64)``] (cj 2 branch_offset_i2w_local)
    val w2n_word6_lt =
      SIMP_RULE (srw_ss()) [dimword_6] (Q.ISPEC `w:word6` wordsTheory.w2n_lt |> GEN_ALL)
    fun dispatch_tac (asl, g) =
      let
        val ins = find_enc_ins asl
        val (hd_c, args) = strip_comb ins
        val cname = fst (dest_const hd_c)
        val dec_tac =
          if cname = "NoOperation" then
            mp_tac dec_NoOp
          else if cname = "Address" then
            let val [_, off, rd] = pairSyntax.strip_pair (hd args) in
              mp_tac (SPECL [off, rd] dec_Address)
              \\ impl_tac >- (simp [] \\ TRY EVAL_TAC)
            end
          else if cname = "Branch" then
            let val (bc, bargs) = strip_comb (hd args)
                val bname = fst (dest_const bc) in
              if bname = "BranchImmediate" then
                let val [off, bt] = pairSyntax.strip_pair (hd bargs) in
                  mp_tac (SPECL [off, bt] dec_BranchImm)
                  \\ impl_tac >- (simp [] \\ irule (cj 1 branch_offset_i2w_local) \\ simp [])
                end
              else if bname = "BranchConditional" then
                let val [off, cnd] = pairSyntax.strip_pair (hd bargs) in
                  mp_tac (SPECL [off, cnd] dec_BranchCond)
                  \\ impl_tac >- (simp [] \\ (irule (cj 2 branch_offset_i2w_local) ORELSE irule branch_cond_thm) \\ simp [])
                end
              else
                let val [rn, _] = pairSyntax.strip_pair (hd bargs) in
                  mp_tac (SPEC rn dec_BranchReg)
                end
            end
          else (* Data *)
            let val (dc, dargs) = strip_comb (hd args)
                val dname = fst (dest_const dc)
                val ps = pairSyntax.strip_pair (hd dargs) in
              if dname = "MoveWide@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 5 ps] dec_MoveWide)
              else if dname = "AddSubShiftedRegister@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 5 ps, el 6 ps, el 7 ps, el 8 ps] dec_AddSubShift)
                \\ impl_tac >- simp []
              else if dname = "LogicalShiftedRegister@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 7 ps, el 8 ps, el 9 ps] dec_LogShift)
                \\ impl_tac >- simp []
              else if dname = "AddSubImmediate@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 5 ps, el 6 ps] dec_AddSubImm)
                \\ impl_tac >- (simp [reg_lt31_neq_31w] \\ TRY EVAL_TAC)
              else if dname = "LogicalImmediate@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 5 ps, el 6 ps] dec_LogicalImm)
                \\ impl_tac >- simp [reg_lt31_neq_31w]
              else if dname = "BitfieldMove@64" then
                mp_tac (SPECL [el 3 ps, el 4 ps, el 5 ps, el 6 ps, el 7 ps, el 8 ps, el 9 ps] dec_Bitfield)
                \\ impl_tac >- (simp [wordsTheory.n2w_w2n, w2n_word6_lt]
                                \\ fs [EVAL ``asm$arch_width_bits (asm$arch_wordsize asm$ARMv8)``]
                                \\ TRY (`Num i < 64` by (Cases_on `i` \\ fs []) \\ simp []))
              else if dname = "ExtractRegister@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 5 ps] dec_Extract)
              else if dname = "Shift@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 5 ps] dec_Shift)
              else if dname = "Division@64" then
                mp_tac (SPECL [el 3 ps, el 4 ps, el 5 ps] dec_Div)
              else if dname = "MultiplyHigh" then
                mp_tac (SPECL [el 1 ps, el 2 ps, el 3 ps, el 4 ps] dec_MulHi)
              else if dname = "MultiplyAddSub@64" then
                mp_tac (SPECL [el 2 ps, el 3 ps, el 4 ps, el 5 ps, el 6 ps] dec_MulAS)
              else if dname = "ConditionalSelect@64" then
                mp_tac (SPECL [el 4 ps, el 5 ps, el 6 ps, el 7 ps] dec_CSel)
              else if dname = "ConditionalCompareImmediate@64" then
                mp_tac (SPEC (last ps) dec_CCmpI)
              else if dname = "AddSubCarry@64" then
                mp_tac (SPECL [el 3 ps, el 4 ps, el 5 ps, el 6 ps] dec_AddC)
              else raise mk_HOL_ERR "forge_arm8Erasure" "dispatch_tac" ("unhandled: " ^ dname)
            end
      in
        (dec_tac \\ strip_tac
         \\ qpat_x_assum `Encode _ = ARM8 _` (fn eth =>
              mp_tac (SPECL [ins, rand (rhs (concl eth)), ``s:arm8_state``, ``dm:word64 set``] Next_of_safe_nonmem)
              \\ assume_tac eth)
         \\ simp [reg_lt31_neq_31w]) (asl, g)
      end
  in
  gen_tac
  \\ asmLib.asm_cases_tac `i`
  \\ rpt gen_tac \\ disch_then strip_assume_tac
  \\ gvs [arm8_ast_def, arm8_asm_ok, arm8_valid_imm_def, valid_immediate_def,
          arm8_encode_fail_def, asmSemTheory.is_test_def, bop_enc_def, LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ gvs [arm8_encode_fail_def]
  \\ dispatch_tac
  end
QED

Theorem bytes_in_memory_all_pcs_elem[local]:
  ∀l pc m dm k.
    k < LENGTH l ∧ bytes_in_memory pc (LIST_BIND l arm8_encode) m dm ⇒
    bytes_in_memory (pc + n2w (4 * k)) (arm8_encode (EL k l)) m dm
Proof
  Induct \\ simp [listTheory.LIST_BIND_def] \\ rpt strip_tac
  \\ Cases_on `k` \\ simp []
  >- (fs [miscTheory.bytes_in_memory_APPEND])
  \\ fs [miscTheory.bytes_in_memory_APPEND, arm8_encode_LENGTH4, GSYM listTheory.LIST_BIND_def]
  \\ first_x_assum (qspecl_then [`pc + 4w`, `m`, `dm`, `n`] mp_tac)
  \\ simp []
  \\ `pc + n2w (4 * SUC n) = pc + 4w + n2w (4 * n)` by
       (REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w, arithmeticTheory.MULT_SUC] \\ simp [])
  \\ simp []
QED

Theorem bytes_in_memory_cong_pcs0[local]:
  ∀bs pc m1 m2 dm.
    bytes_in_memory pc bs m1 dm ∧
    (∀a. a ∈ all_pcs (LENGTH bs) pc 0 ⇒ m2 a = m1 a) ⇒
    bytes_in_memory pc bs m2 dm
Proof
  Induct \\ simp [miscTheory.bytes_in_memory_def]
  \\ rpt strip_tac
  >- (first_x_assum (qspec_then `pc` mp_tac)
      \\ simp [asmPropsTheory.all_pcs_thm]
      \\ impl_tac >- (qexists_tac `0` \\ simp []) \\ simp [])
  \\ first_x_assum irule
  \\ qexists_tac `m1` \\ simp []
  \\ rpt strip_tac
  \\ first_x_assum irule
  \\ fs [asmPropsTheory.all_pcs_thm]
  \\ qexists_tac `SUC i`
  \\ REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w, arithmeticTheory.ADD1]
  \\ simp []
QED

Theorem asserts_cong[local]:
  ∀m f1 f2 s P R.
    (∀k. k ≤ m ⇒ f1 k = f2 k) ⇒ (asserts m f1 s P R ⇔ asserts m f2 s P R)
Proof
  Induct_on `m` >- simp [asmPropsTheory.asserts_def]
  \\ rpt strip_tac \\ simp [asmPropsTheory.asserts_def, LET_THM]
  \\ `f1 (SUC m) = f2 (SUC m)` by simp []
  \\ simp [] \\ AP_TERM_TAC \\ first_x_assum irule \\ rpt strip_tac \\ simp []
QED

Theorem asserts2_0_SUC[local]:
  (∀fi fc ms P. asserts2 0 fi fc ms P ⇔ T) ∧
  (∀n fi fc ms P. asserts2 (SUC n) fi fc ms P ⇔ P ms (fc ms) ∧ asserts2 n fi fc (fi (SUC n) (fc ms)) P) ∧
  (∀n fi fc ms P. asserts2 (n + 1) fi fc ms P ⇔ P ms (fc ms) ∧ asserts2 n fi fc (fi (n + 1) (fc ms)) P)
Proof
  rpt conj_tac \\ rpt gen_tac \\ simp [Once asmPropsTheory.asserts2_def]
QED

Theorem asserts2_cong[local]:
  ∀m f1 f2 fc s R.
    (∀k. 1 ≤ k ∧ k ≤ m ⇒ f1 k = f2 k) ⇒ (asserts2 m f1 fc s R ⇔ asserts2 m f2 fc s R)
Proof
  Induct_on `m` >- simp [asserts2_0_SUC]
  \\ rpt strip_tac \\ simp [asserts2_0_SUC]
  \\ `f1 (SUC m) = f2 (SUC m)` by simp []
  \\ simp [] \\ AP_TERM_TAC \\ first_x_assum irule \\ rpt strip_tac \\ simp []
QED

Theorem asserts_arm8_exact_lift[local]:
  ∀n env ms P_next Q dm check_sp.
    interference_ok env ((arm8_target_exact check_sp).proj dm) ∧
    arm8_ok ms ∧ (¬check_sp ∨ aligned 4 ms.SP_EL0) ∧ P_next ms ∧
    (∀s. arm8_ok s ∧ P_next s ⇒
         (arm8$Next s).exception = NoException ∧ (arm8$Next s).SP_EL0 = s.SP_EL0) ∧
    asserts n (λk s. env (n - k) (arm8_next s)) ms
      (λms'. arm8_ok ms' ∧ P_next ms') Q ∧
    asserts2 (n + 1) (λk. env (n + 1 - k)) arm8_next ms
      (λms1 ms2. ∀x. x ∉ dm ⇒ ms1.MEM x = ms2.MEM x) ⇒
    asserts n (λk s. env (n - k) (arm8$Next s)) ms
      (λms'. (arm8_target_exact check_sp).state_ok ms' ∧ P_next ms')
      (λms'. Q ms' ∧ (¬check_sp ∨ aligned 4 ms'.SP_EL0)) ∧
    asserts2 (n + 1) (λk. env (n + 1 - k)) arm8$Next ms
      (λms1 ms2. ∀x. x ∉ dm ⇒ ms1.MEM x = ms2.MEM x)
Proof
  Induct_on `n`
  >- (
    rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
    \\ `(arm8$Next ms).exception = NoException ∧ (arm8$Next ms).SP_EL0 = ms.SP_EL0` by metis_tac []
    \\ `arm8_next ms = arm8$Next ms` by simp [arm8_next_def, NextStateARM8_def]
    \\ `(env 0 (arm8$Next ms)).SP_EL0 = (arm8$Next ms).SP_EL0` by
         (fs [asmPropsTheory.interference_ok_def, arm8_target_exact_def]
          \\ first_x_assum (qspecl_then [`0`, `arm8$Next ms`] mp_tac) \\ simp [])
    \\ fs [asmPropsTheory.asserts_def, asserts2_0_SUC, arithmeticTheory.ONE])
  \\ rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ `(arm8$Next ms).exception = NoException ∧ (arm8$Next ms).SP_EL0 = ms.SP_EL0` by metis_tac []
  \\ `arm8_next ms = arm8$Next ms` by simp [arm8_next_def, NextStateARM8_def]
  \\ qabbrev_tac `ms1 = env 0 (arm8$Next ms)`
  \\ `ms1.SP_EL0 = ms.SP_EL0` by
       (fs [Abbr `ms1`, asmPropsTheory.interference_ok_def, arm8_target_exact_def]
        \\ first_x_assum (qspecl_then [`0`, `arm8$Next ms`] mp_tac) \\ simp [])
  \\ qpat_x_assum `asserts (SUC n) _ _ _ _` mp_tac
  \\ simp [Once asmPropsTheory.asserts_def, LET_THM]
  \\ strip_tac
  \\ qpat_x_assum `asserts2 (SUC n + 1) _ _ _ _` mp_tac
  \\ simp [Once (cj 3 asserts2_0_SUC)]
  \\ strip_tac
  \\ `interference_ok (λk. env (k + 1)) ((arm8_target_exact check_sp).proj dm)` by
       (fs [asmPropsTheory.interference_ok_def])
  \\ first_x_assum (qspecl_then [`λk. env (k + 1)`, `ms1`, `P_next`, `Q`, `dm`, `check_sp`] mp_tac)
  \\ impl_tac
  >- (
    simp [Abbr `ms1`]
    \\ conj_tac
    >- (
      qpat_x_assum `asserts n _ _ _ _` mp_tac
      \\ `asserts n (λk s. env (SUC n - k) (arm8_next s)) (env 0 (arm8$Next ms))
            (λms'. arm8_ok ms' ∧ P_next ms') Q ⇔
          asserts n (λk s. env (n - k + 1) (arm8_next s)) (env 0 (arm8$Next ms))
            (λms'. arm8_ok ms' ∧ P_next ms') Q` by
           (irule asserts_cong \\ rpt strip_tac \\ simp [FUN_EQ_THM] \\ gen_tac
            \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac)
      \\ simp [])
    \\ qpat_x_assum `asserts2 (SUC n) _ _ _ _` mp_tac
    \\ `SUC n = n + 1` by decide_tac \\ pop_assum SUBST1_TAC
    \\ `asserts2 (n + 1) (λk. env (n + 1 + 1 - k)) arm8_next (env 0 (arm8$Next ms))
          (λms1 ms2. ∀x. x ∉ dm ⇒ ms1.MEM x = ms2.MEM x) ⇔
        asserts2 (n + 1) (λk. env (n + 1 - k + 1)) arm8_next (env 0 (arm8$Next ms))
          (λms1 ms2. ∀x. x ∉ dm ⇒ ms1.MEM x = ms2.MEM x)` by
         (irule asserts2_cong \\ rpt strip_tac \\ simp [] \\ AP_TERM_TAC \\ decide_tac)
    \\ simp [])
  \\ disch_then (strip_assume_tac o BETA_RULE)
  \\ qunabbrev_tac `ms1`
  \\ conj_tac
  >- (
    simp [Once asmPropsTheory.asserts_def, LET_THM]
    \\ conj_tac
    >- simp [arm8_target_exact_def]
    \\ qpat_x_assum `asserts n (λk s. env (n - k + 1) _) _ _ _` mp_tac
    \\ `asserts n (λk s. env (n - k + 1) (arm8$Next s)) (env 0 (arm8$Next ms))
          (λms'. (arm8_target_exact check_sp).state_ok ms' ∧ P_next ms')
          (λms'. Q ms' ∧ (¬check_sp ∨ aligned 4 ms'.SP_EL0)) ⇔
        asserts n (λk s. env (SUC n - k) (arm8$Next s)) (env 0 (arm8$Next ms))
          (λms'. (arm8_target_exact check_sp).state_ok ms' ∧ P_next ms')
          (λms'. Q ms' ∧ (¬check_sp ∨ aligned 4 ms'.SP_EL0))` by
         (irule asserts_cong \\ rpt strip_tac \\ simp [FUN_EQ_THM] \\ gen_tac
          \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac)
    \\ simp [])
  \\ simp [Once (cj 3 asserts2_0_SUC)]
  \\ `SUC n = n + 1` by decide_tac \\ pop_assum SUBST1_TAC
  \\ qpat_x_assum `asserts2 (n + 1) (λk. env (n + 1 - k + 1)) _ _ _` mp_tac
  \\ `asserts2 (n + 1) (λk. env (n + 1 - k + 1)) arm8$Next (env 0 (arm8$Next ms))
        (λms1 ms2. ∀x. x ∉ dm ⇒ ms1.MEM x = ms2.MEM x) ⇔
      asserts2 (n + 1) (λk. env (n + 1 + 1 - k)) arm8$Next (env 0 (arm8$Next ms))
        (λms1 ms2. ∀x. x ∉ dm ⇒ ms1.MEM x = ms2.MEM x)` by
       (irule asserts2_cong \\ rpt strip_tac \\ simp [] \\ AP_TERM_TAC \\ decide_tac)
  \\ simp []
QED

Theorem all_pcs_4_8[local]:
  (∀pc:word64. pc + 4w ∉ all_pcs 4 pc 2) ∧
  (∀pc:word64. pc + 8w ∉ all_pcs 8 pc 2)
Proof
  conj_tac \\ gen_tac
  \\ simp [asmPropsTheory.all_pcs_thm, wordsTheory.WORD_EQ_ADD_LCANCEL,
           wordsTheory.n2w_11, dimword_64]
  \\ gen_tac \\ CCONTR_TAC \\ fs []
  \\ `4 * i < 18446744073709551616` by decide_tac
  \\ fs [arithmeticTheory.LESS_MOD]
QED

Theorem mem_offset_bounds[local]:
  (∀i:int. -4351 ≤ i ∧ i ≤ 4350 ⇒
           0xFFFFFFFFFFFFEF01w ≤ (i2w i : word64) ∧ (i2w i : word64) ≤ 0x10FEw) ∧
  (∀i:int. -256 ≤ i ∧ i ≤ 4095 ⇒
           0xFFFFFFFFFFFFFF00w ≤ (i2w i : word64) ∧ (i2w i : word64) ≤ 0xFFFw)
Proof
  conj_tac \\ gen_tac \\ disch_then strip_assume_tac
  \\ `w2i (i2w i : word64) = i` by
       (irule integer_wordTheory.w2i_i2w
        \\ simp [integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
                 EVAL ``words$INT_MIN (:64)``, EVAL ``words$INT_MAX (:64)``]
        \\ intLib.ARITH_TAC)
  >- (`w2i (0xFFFFFFFFFFFFEF01w : word64) = -4351 ∧ w2i (0x10FEw : word64) = 4350` by EVAL_TAC
      \\ simp [integer_wordTheory.WORD_LEi] \\ intLib.ARITH_TAC)
  \\ `w2i (0xFFFFFFFFFFFFFF00w : word64) = -256 ∧ w2i (0xFFFw : word64) = 4095` by EVAL_TAC
  \\ simp [integer_wordTheory.WORD_LEi] \\ intLib.ARITH_TAC
QED

Theorem mem_2inst_arith[local]:
  (∀c:word64.
     0xFFFFFFFFFFFFEF01w ≤ c ∧ c ≤ 0x10FEw ∧ c ≠ sw2sw ((8 >< 0) c : word9) ⇒
     (~0xFFFw && (if ~word_msb c then c - 0xFFw else -c - 0x100w) = 0w) ∧
     (((if ~word_msb c then 0xFFw else -0x100w) : word64) =
        sw2sw ((8 >< 0) ((if ~word_msb c then 0xFFw else -0x100w) : word64) : word9)) ∧
     ∀x:word64.
       (if word_msb c then x - (-c - 0x100w) else x + (c - 0xFFw)) +
       (if ~word_msb c then 0xFFw else -0x100w) = x + c)
Proof
  rpt strip_tac
  \\ Cases_on `word_msb c`
  \\ simp [EVAL ``sw2sw ((8 >< 0) (255w : word64) : word9) : word64``,
           EVAL ``sw2sw ((8 >< 0) (-256w : word64) : word9) : word64``]
  \\ blastLib.FULL_BBLAST_TAC
QED

Theorem arm8_target_exact_ok:
  ∀check_sp. target_ok (arm8_target_exact check_sp)
Proof
  gen_tac
  \\ mp_tac arm8_targetProofTheory.arm8_encoder_correct
  \\ simp [asmPropsTheory.encoder_correct_def, asmPropsTheory.target_ok_def,
           asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def]
  \\ strip_tac \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [`ms1`, `ms2`, `s`] mp_tac)
  \\ simp [] \\ metis_tac []
QED

Theorem arm8_target_exact_encoder_correct:
  ∀check_sp. encoder_correct (arm8_target_exact check_sp)
Proof
  gen_tac
  \\ simp [asmPropsTheory.encoder_correct_def, arm8_target_exact_ok]
  \\ rpt strip_tac
  \\ `target_state_rel arm8_target s1 ms` by
       fs [asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def]
  \\ SUBGOAL_THEN ``check_sp ⇒ aligned 4 ms.SP_EL0`` assume_tac
  >- fs [asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def]
  \\ mp_tac arm8_targetProofTheory.arm8_encoder_correct
  \\ simp [asmPropsTheory.encoder_correct_def]
  \\ strip_tac
  \\ first_x_assum (qspecl_then [`s1`, `i`, `s2`, `ms`] mp_tac)
  \\ impl_tac >- fs [arm8_target_exact_def, arm8_target_def]
  \\ strip_tac
  \\ qexists_tac `n`
  \\ gen_tac \\ strip_tac
  \\ `interference_ok env (arm8_target.proj s1.mem_domain)` by
       (fs [asmPropsTheory.interference_ok_def, arm8_target_exact_def, arm8_target_def]
        \\ metis_tac [pairTheory.PAIR_EQ])
  \\ `∀k s. (env k s).SP_EL0 = s.SP_EL0 ∧ (env k s).PC = s.PC ∧ (env k s).REG = s.REG` by
       (rpt strip_tac \\ fs [asmPropsTheory.interference_ok_def, arm8_target_exact_def, arm8_proj_def]
        \\ first_x_assum (qspecl_then [`k`, `s`] mp_tac) \\ simp [])
  \\ first_x_assum drule \\ simp [LET_THM] \\ strip_tac
  \\ Cases_on `∃op r ad. i = Inst (Mem op r ad)`
  >- (
    (* Mem cases: either 1 instruction (n = 0) or 2 instructions (n ≤ 1) *)
    pop_assum strip_assume_tac \\ rveq
    \\ Cases_on `ad`
    \\ rename1 `Inst (Mem op r1 (Addr r2 off_i))`
    \\ `asm_ok (Inst (Mem op r1 (Addr r2 off_i))) arm8_config ∧
        bytes_in_memory s1.pc (arm8_enc (Inst (Mem op r1 (Addr r2 off_i)))) s1.mem s1.mem_domain ∧
        ¬s2.failed ∧ asm (Inst (Mem op r1 (Addr r2 off_i))) (s1.pc + n2w (LENGTH (arm8_enc (Inst (Mem op r1 (Addr r2 off_i)))))) s1 = s2` by
         fs [asmSemTheory.asm_step_def, arm8_target_exact_def, arm8_target_def, arm8_config_def]
    \\ `arm8_ok ms ∧ ms.PC = s1.pc ∧ ms.REG (n2w r2) = s1.regs r2 ∧
        bytes_in_memory s1.pc (arm8_enc (Inst (Mem op r1 (Addr r2 off_i)))) ms.MEM s1.mem_domain` by
         (Cases_on `op` \\ fs [arm8_asm_ok]
          \\ fs [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
          \\ irule bytes_in_memory_cong_pcs0
          \\ qexists_tac `s1.mem` \\ simp [] \\ rpt strip_tac
          \\ qpat_x_assum `∀a. a ∈ s1.mem_domain ⇒ ms.MEM a = s1.mem a` irule
          \\ drule asmPropsTheory.bytes_in_memory_all_pcs
          \\ disch_then (qspec_then `0` mp_tac)
          \\ simp [SUBSET_DEF])
    \\ qabbrev_tac `c : word64 = i2w off_i`
    \\ `r2 < 32 ∧ r2 ≠ 31` by (Cases_on `op` \\ fs [arm8_asm_ok])
    \\ `n2w r2 ≠ (31w : word5)` by simp [reg_lt31_neq_31w]
    (* Helper tactic: discharge 1-instruction LSI case *)
    \\ `∀ins. arm8_ast (Inst (Mem op r1 (Addr r2 off_i))) = [ins] ∧
              ((arm8$Next ms).exception = NoException ∧ (arm8$Next ms).SP_EL0 = ms.SP_EL0 ∧
               (arm8$Next ms).PC = s1.pc + 4w) ⇒
              asserts n (λk s. env (n - k) (arm8$Next s)) ms
                (λms'. (arm8_target_exact check_sp).state_ok ms' ∧
                       (∀pc. pc ∈ all_pcs (LENGTH (arm8_enc (Inst (Mem op r1 (Addr r2 off_i))))) s1.pc 0 ⇒
                             ms'.MEM pc = ms.MEM pc) ∧
                       ms'.PC ∈ all_pcs (LENGTH (arm8_enc (Inst (Mem op r1 (Addr r2 off_i))))) s1.pc 2)
                (λms'. target_state_rel (arm8_target_exact check_sp) s2 ms') ∧
              asserts2 (n + 1) (λk. env (n + 1 - k)) arm8$Next ms
                (λms1 ms2. ∀x. x ∉ s1.mem_domain ⇒ ms1.MEM x = ms2.MEM x)` by
         (gen_tac \\ strip_tac
          \\ `arm8_next ms = arm8$Next ms` by simp [arm8_next_def, NextStateARM8_def]
          \\ `LENGTH (arm8_enc (Inst (Mem op r1 (Addr r2 off_i)))) = 4` by
               simp [arm8_enc_def, arm8_encode_LENGTH4]
          \\ Cases_on `n`
          >- (fs [asmPropsTheory.asserts_def, asserts2_0_SUC, arithmeticTheory.ONE,
                  asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def]
              \\ Cases_on `check_sp` \\ gvs [])
          \\ qpat_x_assum `asserts (SUC _) _ _ _ _` mp_tac
          \\ simp [Once asmPropsTheory.asserts_def, LET_THM, arm8_target_def, arm8_config_def]
          \\ strip_tac
          \\ `s1.pc + 4w ∈ all_pcs 4 s1.pc 2` by gvs []
          \\ fs [all_pcs_4_8])
    (* Helper tactic: discharge 2-instruction AddSubImm + LSI case *)
    \\ `∀ins0 ins1.
          arm8_ast (Inst (Mem op r1 (Addr r2 off_i))) = [ins0; ins1] ∧
          ((arm8$Next ms).exception = NoException ∧ (arm8$Next ms).SP_EL0 = ms.SP_EL0 ∧
           (arm8$Next ms).PC = s1.pc + 4w) ∧
          (∀ms1. arm8_ok ms1 ∧ ms1.PC = s1.pc + 4w ∧ ms1.REG = (arm8$Next ms).REG ∧
                 bytes_in_memory (s1.pc + 4w) (arm8_encode ins1) ms1.MEM s1.mem_domain ⇒
                 (arm8$Next ms1).exception = NoException ∧ (arm8$Next ms1).SP_EL0 = ms1.SP_EL0 ∧
                 (arm8$Next ms1).PC = s1.pc + 8w) ⇒
          asserts n (λk s. env (n - k) (arm8$Next s)) ms
            (λms'. (arm8_target_exact check_sp).state_ok ms' ∧
                   (∀pc. pc ∈ all_pcs (LENGTH (arm8_enc (Inst (Mem op r1 (Addr r2 off_i))))) s1.pc 0 ⇒
                         ms'.MEM pc = ms.MEM pc) ∧
                   ms'.PC ∈ all_pcs (LENGTH (arm8_enc (Inst (Mem op r1 (Addr r2 off_i))))) s1.pc 2)
            (λms'. target_state_rel (arm8_target_exact check_sp) s2 ms') ∧
          asserts2 (n + 1) (λk. env (n + 1 - k)) arm8$Next ms
            (λms1 ms2. ∀x. x ∉ s1.mem_domain ⇒ ms1.MEM x = ms2.MEM x)` by
         (rpt gen_tac \\ strip_tac
          \\ `arm8_next ms = arm8$Next ms` by simp [arm8_next_def, NextStateARM8_def]
          \\ `LENGTH (arm8_enc (Inst (Mem op r1 (Addr r2 off_i)))) = 8` by
               simp [arm8_enc_def, arm8_encode_LENGTH4]
          \\ Cases_on `n`
          >- (fs [asmPropsTheory.asserts_def, asserts2_0_SUC, arithmeticTheory.ONE,
                  asmPropsTheory.target_state_rel_def, arm8_target_exact_def, arm8_target_def]
              \\ Cases_on `check_sp` \\ gvs [])
          \\ qpat_x_assum `asserts (SUC _) _ _ _ _` mp_tac
          \\ simp [Once asmPropsTheory.asserts_def, LET_THM, arm8_target_def, arm8_config_def]
          \\ strip_tac
          \\ qabbrev_tac `ms1 = env 0 (arm8$Next ms)`
          \\ `bytes_in_memory (s1.pc + 4w) (arm8_encode ins1) ms1.MEM s1.mem_domain` by
               (`bytes_in_memory s1.pc (arm8_enc (Inst (Mem op r1 (Addr r2 off_i)))) ms1.MEM s1.mem_domain` by
                  (irule bytes_in_memory_cong_pcs0 \\ qexists_tac `ms.MEM` \\ simp [Abbr `ms1`])
                \\ pop_assum mp_tac
                \\ simp [arm8_enc_def, listTheory.LIST_BIND_def, miscTheory.bytes_in_memory_APPEND,
                         arm8_encode_LENGTH4])
          \\ `(arm8$Next ms1).exception = NoException ∧ (arm8$Next ms1).SP_EL0 = ms1.SP_EL0 ∧
              (arm8$Next ms1).PC = s1.pc + 8w` by
               (qpat_x_assum `∀ms1. _ ⇒ _` irule \\ simp [Abbr `ms1`])
          \\ `arm8_next ms1 = arm8$Next ms1` by simp [arm8_next_def, NextStateARM8_def]
          \\ Cases_on `n'`
          >- (
            qpat_x_assum `asserts2 (SUC 0 + 1) _ _ _ _` mp_tac
            \\ qpat_x_assum `asserts 0 _ _ _ _` mp_tac
            \\ ONCE_REWRITE_TAC [cj 3 asserts2_0_SUC]
            \\ ONCE_REWRITE_TAC [cj 2 asserts2_0_SUC]
            \\ REWRITE_TAC [cj 1 asserts2_0_SUC]
            \\ `SUC 0 + 1 - (SUC 0 + 1) = 0 ∧ SUC 0 + 1 - SUC 0 = 1 ∧
                SUC 0 - SUC 0 = 0 ∧ SUC 0 - 0 = 1` by decide_tac
            \\ simp [asmPropsTheory.asserts_def, LET_THM,
                     asmPropsTheory.target_state_rel_def, arm8_target_exact_def,
                     arm8_target_def, arm8_config_def]
            \\ `ms1.SP_EL0 = ms.SP_EL0 ∧ ms1.PC = s1.pc + 4w` by simp [Abbr `ms1`]
            \\ rpt strip_tac \\ Cases_on `check_sp` \\ fs [])
          \\ qpat_x_assum `asserts (SUC _) _ _ _ _` mp_tac
          \\ simp [Once asmPropsTheory.asserts_def, LET_THM, arm8_target_def, arm8_config_def]
          \\ strip_tac
          \\ `s1.pc + 8w ∈ all_pcs 8 s1.pc 2` by gvs [Abbr `ms1`]
          \\ fs [all_pcs_4_8])
    (* Rewrite only target projections on goal to match H1 / H2 *)
    \\ `(arm8_target_exact check_sp).next = arm8$Next ∧
        (arm8_target_exact check_sp).config.encode = arm8_enc ∧
        (arm8_target_exact check_sp).config.code_alignment = 2 ∧
        (arm8_target_exact check_sp).get_byte = arm8_state_MEM ∧
        (arm8_target_exact check_sp).get_pc = arm8_state_PC` by
         simp [arm8_target_exact_def, arm8_target_def, arm8_config_def]
    \\ pop_assum (fn th => REWRITE_TAC [th])
    (* Now split on the 8 MemOp constructors *)
    \\ Cases_on `op`
    \\ fs [arm8_ast_def, arm8_load_store_ast_def, arm8_load_store_ast32_def, arm8_load_store_ast16_def,
           arm8_asm_ok, asmSemTheory.asm_def, asmSemTheory.inst_def, asmSemTheory.upd_pc_def,
           asmSemTheory.mem_op_def, asmSemTheory.addr_def, asmSemTheory.mem_load_def,
           asmSemTheory.mem_store_def, asmSemTheory.assert_def, asmSemTheory.read_reg_def, LET_THM]
    \\ rpt (pairarg_tac \\ fs [])
    \\ qpat_x_assum `Abbrev (c = i2w off_i)` (fn th =>
         FULL_SIMP_TAC pure_ss [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] \\ assume_tac th)
    \\ TRY (
      (* Load8 / Store8: always 1 instruction *)
      `0xFFFFFFFFFFFFFF00w ≤ c ∧ c ≤ 0xFFFw` by
        (mp_tac (Q.SPEC `off_i` (cj 2 mem_offset_bounds)) \\ simp [Abbr `c`])
      \\ `((¬word_msb c ∧ c = w2w ((11 >< 0) c : word12)) ∨ c = sw2sw ((8 >< 0) c : word9))` by
           blastLib.FULL_BBLAST_TAC
      \\ qpat_x_assum `(arm8$Next ms).exception = NoException ∧ _ ⇒ _` MATCH_MP_TAC
      \\ qpat_x_assum `bytes_in_memory s1.pc (arm8_enc _) ms.MEM _` mp_tac
      \\ simp [arm8_enc_def, listTheory.LIST_BIND_def, arm8_ast_def]
      \\ qpat_x_assum `Abbrev (c = i2w off_i)` (fn th =>
           REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] \\ assume_tac th)
      \\ strip_tac
      \\ qpat_x_assum `ms.PC = s1.pc` (fn th =>
           qpat_x_assum `bytes_in_memory s1.pc (arm8_encode _) ms.MEM _`
             (assume_tac o REWRITE_RULE [GSYM th]) \\ assume_tac th)
      \\ ((qspecl_then [`MemOp_LOAD`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI8
           \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
           \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
           \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
           \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
          ORELSE
          (qspecl_then [`MemOp_STORE`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI8
           \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
           \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
           \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
           \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC)))
      \\ simp [Next_def, LET_THM]
      \\ (mp_tac (Q.SPECL [`ms with branch_hint := NONE`, `rsw`, `mo`, `sg`, `wbu`, `rtu`, `uo`, `c`, `n2w r2`, `n2w r1`] lsi_Run_ok)
          \\ impl_tac >- fs [arm8_ok_def, reg_lt31_neq_31w]
          \\ disch_then (fn th => qspec_then `sz` mp_tac (cj 4 th))
          \\ simp [LET_THM]) \\ NO_TAC)
    \\ (* Load / Load32 / Load16 / Store / Store32 / Store16: 1 or 2 instructions *)
       (`0xFFFFFFFFFFFFEF01w ≤ c ∧ c ≤ 0x10FEw` by
          (mp_tac (Q.SPEC `off_i` (cj 1 mem_offset_bounds)) \\ simp [Abbr `c`])
        \\ qpat_x_assum `¬s2.failed` (fn nf =>
             qpat_x_assum `_ = s2` (fn eq =>
               mp_tac (REWRITE_RULE [SYM eq] nf) \\ assume_tac eq))
        \\ simp [EVAL ``LOG2 8``, EVAL ``LOG2 4``, EVAL ``LOG2 2``]
        \\ strip_tac
        \\ qpat_x_assum `∀ins. _ ⇒ _` mp_tac
        \\ IF_CASES_TAC
        >- (
          (* 2-instruction Mem *)
          disch_then assume_tac
          \\ qabbrev_tac `b0 : word64 = if ¬word_msb c then c - 0xFFw else -c - 0x100w`
          \\ qabbrev_tac `c0 : word64 = if ¬word_msb c then 0xFFw else -0x100w`
         \\ `b = b0 ∧ c' = c0` by
              (Cases_on `word_msb c` \\ gvs [Abbr `b0`, Abbr `c0`])
         \\ pop_assum (fn th => FULL_SIMP_TAC pure_ss [th])
         \\ fs []
         \\ qpat_x_assum `_ ⇒ asserts n _ ms _ _ ∧ asserts2 _ _ arm8$Next ms _` MATCH_MP_TAC
         \\ `(~0xFFFw && b0 = 0w) ∧ c0 = sw2sw ((8 >< 0) c0 : word9) ∧
             (if word_msb c then ms.REG (n2w r2) - b0 else ms.REG (n2w r2) + b0) + c0 = ms.REG (n2w r2) + c` by
              (simp [Abbr `b0`, Abbr `c0`] \\ mp_tac (Q.SPEC `c` mem_2inst_arith) \\ simp [])
         \\ `bytes_in_memory ms.PC (arm8_encode (Data (AddSubImmediate@64 (1w, word_msb c, F, b0, n2w r2, 26w)))) ms.MEM s1.mem_domain` by
              (qpat_x_assum `bytes_in_memory s1.pc (arm8_enc _) ms.MEM _` mp_tac
               \\ simp [arm8_enc_def, listTheory.LIST_BIND_def, arm8_ast_def, arm8_load_store_ast_def,
                        arm8_load_store_ast32_def, arm8_load_store_ast16_def, LET_THM,
                        miscTheory.bytes_in_memory_APPEND]
               \\ qpat_x_assum `Abbrev (c = i2w off_i)` (fn th =>
                    REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] \\ assume_tac th)
               \\ Cases_on `word_msb c` \\ fs [Abbr `b0`, Abbr `c0`])
         \\ (qspecl_then [`word_msb c`, `b0`, `n2w r2`] mp_tac dec_AddSubImm_exact
             \\ impl_tac >- simp []
             \\ strip_tac)
         \\ qpat_x_assum `Encode _ = ARM8 _` assume_tac
         \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
         \\ strip_tac
         \\ `(arm8$Next ms).exception = NoException ∧ (arm8$Next ms).SP_EL0 = ms.SP_EL0 ∧
             (arm8$Next ms).PC = s1.pc + 4w ∧
             (arm8$Next ms).REG 26w = (if word_msb c then ms.REG (n2w r2) - b0 else ms.REG (n2w r2) + b0)` by
              (simp [Next_def, LET_THM]
               \\ qspecl_then [`word_msb c`, `b0`, `n2w r2`, `ms`] mp_tac addsub_imm_Run_ok
               \\ simp [LET_THM, reg_lt31_neq_31w])
         \\ simp []
         \\ rpt strip_tac
         \\ `26w ≠ (31w : word5)` by EVAL_TAC
         \\ `((¬word_msb c ∧ c0 = w2w ((11 >< 0) (c0 >>> 3) : word12) << 3) ∨ c0 = sw2sw ((8 >< 0) c0 : word9)) ∧
             ((¬word_msb c ∧ c0 = w2w ((11 >< 0) (c0 >>> 2) : word12) << 2) ∨ c0 = sw2sw ((8 >< 0) c0 : word9)) ∧
             ((¬word_msb c ∧ c0 = w2w ((11 >< 0) (c0 >>> 1) : word12) << 1) ∨ c0 = sw2sw ((8 >< 0) c0 : word9))` by simp []
         \\ qpat_x_assum `bytes_in_memory (s1.pc + 4w) _ ms1.MEM _` mp_tac
         \\ simp [] \\ strip_tac
         \\ qpat_x_assum `ms1.PC = s1.pc + 4w` (fn th =>
              qpat_x_assum `bytes_in_memory (s1.pc + 4w) _ ms1.MEM _`
                (assume_tac o REWRITE_RULE [GSYM th]) \\ assume_tac th)
         \\ ((qspecl_then [`MemOp_LOAD`, `¬word_msb c`, `c0`, `26w`, `n2w r1`] mp_tac dec_LSI64
              \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
              \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` (fn eth =>
                   drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                     (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)) eth))
              \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
             ORELSE
             (qspecl_then [`MemOp_STORE`, `¬word_msb c`, `c0`, `26w`, `n2w r1`] mp_tac dec_LSI64
              \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
              \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` (fn eth =>
                   drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                     (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)) eth))
              \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
             ORELSE
             (qspecl_then [`MemOp_LOAD`, `¬word_msb c`, `c0`, `26w`, `n2w r1`] mp_tac dec_LSI32
              \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
              \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` (fn eth =>
                   drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                     (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)) eth))
              \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
             ORELSE
             (qspecl_then [`MemOp_STORE`, `¬word_msb c`, `c0`, `26w`, `n2w r1`] mp_tac dec_LSI32
              \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
              \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` (fn eth =>
                   drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                     (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)) eth))
              \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
             ORELSE
             (qspecl_then [`MemOp_LOAD`, `¬word_msb c`, `c0`, `26w`, `n2w r1`] mp_tac dec_LSI16
              \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
              \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` (fn eth =>
                   drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                     (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)) eth))
              \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
             ORELSE
             (qspecl_then [`MemOp_STORE`, `¬word_msb c`, `c0`, `26w`, `n2w r1`] mp_tac dec_LSI16
              \\ impl_tac >- simp [] \\ simp [] \\ strip_tac
              \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` (fn eth =>
                   drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                     (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)) eth))
              \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC)))
         \\ simp [Next_def, LET_THM]
         \\ (mp_tac (Q.SPECL [`ms1 with branch_hint := NONE`, `rsw`, `mo`, `sg`, `wbu`, `rtu`, `uo`, `c0`, `26w`, `n2w r1`] lsi_Run_ok)
             \\ impl_tac >- fs [arm8_ok_def]
             \\ strip_tac)
         \\ `s1.pc + 4w + 4w = s1.pc + 8w` by blastLib.BBLAST_TAC
         \\ `(ms1 with branch_hint := NONE).REG 26w + c0 = c + s1.regs r2` by
              (simp [] \\ Cases_on `word_msb c` \\ fs [Abbr `b0`, Abbr `c0`] \\ blastLib.BBLAST_TAC)
         \\ pop_assum (fn th => rpt (qpat_x_assum `∀sz. _` (assume_tac o REWRITE_RULE [th] o Q.SPEC `sz`)))
         \\ rfs [LET_THM])
       \\ (* 1-instruction Mem *)
          disch_then assume_tac
          \\ fs []
          \\ qpat_x_assum `_ ⇒ asserts n _ ms _ _ ∧ asserts2 _ _ arm8$Next ms _` MATCH_MP_TAC
          \\ qpat_x_assum `bytes_in_memory s1.pc (arm8_enc _) ms.MEM _` mp_tac
          \\ simp [arm8_enc_def, listTheory.LIST_BIND_def, arm8_ast_def, arm8_load_store_ast_def,
                   arm8_load_store_ast32_def, arm8_load_store_ast16_def, LET_THM]
          \\ qpat_x_assum `Abbrev (c = i2w off_i)` (fn th =>
               REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] \\ assume_tac th)
          \\ simp [listTheory.LIST_BIND_def]
          \\ strip_tac
          \\ qpat_x_assum `ms.PC = s1.pc` (fn th =>
               qpat_x_assum `bytes_in_memory s1.pc (arm8_encode _) ms.MEM _`
                 (assume_tac o REWRITE_RULE [GSYM th]) \\ assume_tac th)
          \\ ((qspecl_then [`MemOp_LOAD`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI64
               \\ impl_tac >- (Cases_on `word_msb c` \\ fs [] \\ Cases_on `c = sw2sw ((8 >< 0) c : word9)` \\ fs []) \\ simp [] \\ strip_tac \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
               \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
               \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
              ORELSE
              (qspecl_then [`MemOp_STORE`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI64
               \\ impl_tac >- (Cases_on `word_msb c` \\ fs [] \\ Cases_on `c = sw2sw ((8 >< 0) c : word9)` \\ fs []) \\ simp [] \\ strip_tac \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
               \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
               \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
              ORELSE
              (qspecl_then [`MemOp_LOAD`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI32
               \\ impl_tac >- (Cases_on `word_msb c` \\ fs [] \\ Cases_on `c = sw2sw ((8 >< 0) c : word9)` \\ fs []) \\ simp [] \\ strip_tac \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
               \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
               \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
              ORELSE
              (qspecl_then [`MemOp_STORE`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI32
               \\ impl_tac >- (Cases_on `word_msb c` \\ fs [] \\ Cases_on `c = sw2sw ((8 >< 0) c : word9)` \\ fs []) \\ simp [] \\ strip_tac \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
               \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
               \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
              ORELSE
              (qspecl_then [`MemOp_LOAD`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI16
               \\ impl_tac >- (Cases_on `word_msb c` \\ fs [] \\ Cases_on `c = sw2sw ((8 >< 0) c : word9)` \\ fs []) \\ simp [] \\ strip_tac \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
               \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
               \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC))
              ORELSE
              (qspecl_then [`MemOp_STORE`, `¬word_msb c`, `c`, `n2w r2`, `n2w r1`] mp_tac dec_LSI16
               \\ impl_tac >- (Cases_on `word_msb c` \\ fs [] \\ Cases_on `c = sw2sw ((8 >< 0) c : word9)` \\ fs []) \\ simp [] \\ strip_tac \\ qpat_x_assum `Encode (LoadStore _) = ARM8 _` assume_tac
               \\ drule_all (ONCE_REWRITE_RULE [DECIDE ``(a ∧ b ∧ c ⇒ d) ⇔ (b ∧ a ∧ c ⇒ d)``] bytes_in_mem_encode_fetch)
               \\ disch_then (fn th => if is_eq (concl th) then assume_tac th else NO_TAC)))
          \\ simp [Next_def, LET_THM]
          \\ (mp_tac (Q.SPECL [`ms with branch_hint := NONE`, `rsw`, `mo`, `sg`, `wbu`, `rtu`, `uo`, `c`, `n2w r2`, `n2w r1`] lsi_Run_ok)
              \\ impl_tac >- fs [arm8_ok_def, reg_lt31_neq_31w]
              \\ strip_tac)
          \\ `(ms with branch_hint := NONE).REG (n2w r2) + c = c + s1.regs r2` by
               (simp [] \\ blastLib.BBLAST_TAC)
          \\ pop_assum (fn th => rpt (qpat_x_assum `∀sz. _` (assume_tac o REWRITE_RULE [th] o Q.SPEC `sz`)))
          \\ rfs [LET_THM]))
  \\ (* All non-Mem instructions: single uniform lift via asserts_arm8_exact_lift! *)
     `asm_ok i arm8_config ∧ bytes_in_memory s1.pc (arm8_enc i) ms.MEM s1.mem_domain` by
       (fs [asmSemTheory.asm_step_def, asmPropsTheory.target_state_rel_def,
            arm8_target_exact_def, arm8_target_def, arm8_config_def]
        \\ irule bytes_in_memory_cong_pcs0
        \\ qexists_tac `s1.mem` \\ simp [] \\ rpt strip_tac
        \\ `a ∈ s1.mem_domain` by
             (drule asmPropsTheory.bytes_in_memory_all_pcs
              \\ disch_then (qspec_then `0` mp_tac) \\ simp [SUBSET_DEF])
        \\ simp [])
  \\ qabbrev_tac `P_next = λms':arm8_state.
       (∀pc. pc ∈ all_pcs (LENGTH (arm8_enc i)) s1.pc 0 ⇒ ms'.MEM pc = ms.MEM pc) ∧
       ms'.PC ∈ all_pcs (LENGTH (arm8_enc i)) s1.pc 2`
  \\ SUBGOAL_THEN ``¬check_sp ∨ aligned 4 ms.SP_EL0`` assume_tac
  >- (Cases_on `check_sp` \\ fs [])
  \\ qspecl_then [`n`, `env`, `ms`, `P_next`, `λms'. target_state_rel arm8_target s2 ms'`,
                  `s1.mem_domain`, `check_sp`] mp_tac asserts_arm8_exact_lift
  \\ impl_tac
  >- (
    simp [Abbr `P_next`]
    \\ rpt conj_tac
    >- fs [asmPropsTheory.target_state_rel_def, arm8_target_def]
    >- (simp [asmPropsTheory.all_pcs_thm] \\ qexists_tac `0`
        \\ `ms.PC = s1.pc` by fs [asmPropsTheory.target_state_rel_def, arm8_target_def]
        \\ simp [arm8_enc_def, LIST_BIND_arm8_encode_LENGTH]
        \\ mp_tac (Q.SPEC `i` arm8_targetProofTheory.arm8_encoding)
        \\ simp [arm8_enc_def]
        \\ Cases_on `arm8_ast i` \\ simp [])
    >- (
      rpt strip_tac
      \\ `bytes_in_memory s1.pc (arm8_enc i) s.MEM s1.mem_domain` by
           (irule bytes_in_memory_cong_pcs0 \\ qexists_tac `ms.MEM` \\ simp [])
      \\ fs [asmPropsTheory.all_pcs_thm, arm8_enc_def, LIST_BIND_arm8_encode_LENGTH]
      \\ `i' < LENGTH (arm8_ast i)` by decide_tac
      \\ `bytes_in_memory s.PC (arm8_encode (EL i' (arm8_ast i))) s.MEM s1.mem_domain` by
           (`s.PC = s1.pc + n2w (4 * i')` by (`i' * 4 = 4 * i'` by decide_tac \\ simp [])
            \\ pop_assum SUBST1_TAC
            \\ irule bytes_in_memory_all_pcs_elem \\ simp [])
      \\ qspecl_then [`i`, `EL i' (arm8_ast i)`, `s`, `s1.mem_domain`] mp_tac arm8_ast_nonmem_step_ok
      \\ simp [listTheory.EL_MEM] \\ metis_tac [])
    >- fs [arm8_target_def, arm8_config_def]
    \\ fs [arm8_target_def])
  \\ simp [Abbr `P_next`, arm8_target_exact_def, arm8_target_def, arm8_config_def, CONJ_ASSOC]
  \\ disch_then (fn th => simp [cj 2 th] \\ assume_tac (cj 1 th))
  \\ `∀m f (s:arm8_state) P1 Q1.
        asserts m f s P1 Q1 ⇒
        ∀P2 Q2. (∀x. P1 x ⇔ P2 x) ∧ (∀x. Q1 x ⇒ Q2 x) ⇒ asserts m f s P2 Q2` by
       (Induct_on `m` >- simp [asmPropsTheory.asserts_def]
        \\ rpt strip_tac \\ fs [asmPropsTheory.asserts_def, LET_THM] \\ metis_tac [])
  \\ pop_assum (fn mth => pop_assum (fn th1 => HO_MATCH_MP_TAC (MATCH_MP mth th1)))
  \\ simp [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def, CONJ_ASSOC]
QED

(* ---- 5. Unconditional Real-Bits Machine-Semantics Equivalence (Zero b ≠ Fail Premise) ---- *)

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

Theorem erase_mc_next_interfer_K_I[local]:
  ∀B mc. mc.next_interfer = K I ⇒
    (erase_mc B mc with next_interfer := shift_seq 1 (K I)) = erase_mc B mc ∧
    (erase_mc B mc with next_interfer := shift_seq 1 (erase_mc B mc).next_interfer) =
    erase_mc B mc
Proof
  rpt strip_tac
  \\ simp [erase_mc_def, shift_seq_1, FUN_EQ_THM, targetSemTheory.machine_config_component_equality]
QED

Theorem real_mc_next_interfer_K_I[local]:
  ∀B mc. mc.next_interfer = K I ⇒
    (real_mc B mc with next_interfer := shift_seq 1 (K I)) = real_mc B mc ∧
    (real_mc B mc with next_interfer := shift_seq 1 (real_mc B mc).next_interfer) =
    real_mc B mc
Proof
  rpt strip_tac
  \\ simp [real_mc_def, shift_seq_1, FUN_EQ_THM, targetSemTheory.machine_config_component_equality]
QED

Theorem real_erase_mc_fields[local]:
  ∀B mc.
    (real_mc B mc).prog_addresses = mc.prog_addresses ∧
    (real_mc B mc).ffi_entry_pcs = mc.ffi_entry_pcs ∧
    (real_mc B mc).ffi_names = mc.ffi_names ∧
    (real_mc B mc).halt_pc = mc.halt_pc ∧
    (real_mc B mc).install_pc = mc.install_pc ∧
    (real_mc B mc).ptr_reg = mc.ptr_reg ∧
    (real_mc B mc).len_reg = mc.len_reg ∧
    (real_mc B mc).ptr2_reg = mc.ptr2_reg ∧
    (real_mc B mc).len2_reg = mc.len2_reg ∧
    (real_mc B mc).mmio_info = mc.mmio_info ∧
    (real_mc B mc).next_interfer = mc.next_interfer ∧
    (real_mc B mc).ffi_interfer = mc.ffi_interfer ∧
    (real_mc B mc).install_interfer = mc.install_interfer ∧
    (real_mc B mc).target = arm8_target_real B ∧
    (erase_mc B mc).prog_addresses = mc.prog_addresses ∧
    (erase_mc B mc).ffi_entry_pcs = mc.ffi_entry_pcs ∧
    (erase_mc B mc).ffi_names = mc.ffi_names ∧
    (erase_mc B mc).halt_pc = mc.halt_pc ∧
    (erase_mc B mc).install_pc = mc.install_pc ∧
    (erase_mc B mc).ptr_reg = mc.ptr_reg ∧
    (erase_mc B mc).len_reg = mc.len_reg ∧
    (erase_mc B mc).ptr2_reg = mc.ptr2_reg ∧
    (erase_mc B mc).len2_reg = mc.len2_reg ∧
    (erase_mc B mc).mmio_info = mc.mmio_info ∧
    (erase_mc B mc).next_interfer = mc.next_interfer ∧
    (erase_mc B mc).ffi_interfer = (λk (i,bs,s). erase (mc.ffi_interfer k (i,bs,restore B s))) ∧
    (erase_mc B mc).install_interfer = (λk (bs,s). erase (mc.install_interfer k (bs,restore B s))) ∧
    (erase_mc B mc).target = arm8_target_exact (SND (SND B))
Proof
  simp [real_mc_def, erase_mc_def]
QED

Theorem real_erase_mc_shift_install[local]:
  ∀B mc.
    (real_mc B mc with install_interfer := shift_seq 1 mc.install_interfer) =
    real_mc B (mc with install_interfer := shift_seq 1 mc.install_interfer) ∧
    (erase_mc B mc with install_interfer :=
       shift_seq 1 (λk (bs,s). erase (mc.install_interfer k (bs,restore B s)))) =
    erase_mc B (mc with install_interfer := shift_seq 1 mc.install_interfer) ∧
    (erase_mc B mc with install_interfer := shift_seq 1 (erase_mc B mc).install_interfer) =
    erase_mc B (mc with install_interfer := shift_seq 1 mc.install_interfer)
Proof
  simp [real_mc_def, erase_mc_def, shift_seq_1, FUN_EQ_THM,
        targetSemTheory.machine_config_component_equality]
QED

Theorem real_erase_mc_shift_ffi[local]:
  ∀B mc.
    (real_mc B mc with ffi_interfer := shift_seq 1 mc.ffi_interfer) =
    real_mc B (mc with ffi_interfer := shift_seq 1 mc.ffi_interfer) ∧
    (erase_mc B mc with ffi_interfer :=
       shift_seq 1 (λk (i,bs,s). erase (mc.ffi_interfer k (i,bs,restore B s)))) =
    erase_mc B (mc with ffi_interfer := shift_seq 1 mc.ffi_interfer) ∧
    (erase_mc B mc with ffi_interfer := shift_seq 1 (erase_mc B mc).ffi_interfer) =
    erase_mc B (mc with ffi_interfer := shift_seq 1 mc.ffi_interfer)
Proof
  simp [real_mc_def, erase_mc_def, shift_seq_1, FUN_EQ_THM,
        targetSemTheory.machine_config_component_equality]
QED

Theorem evaluate_exact_non_error_pc_valid[local]:
  ∀mc B ffi ms.
    FST (evaluate (erase_mc B mc) ffi 1 ms) ≠ Error ⇒
    ms.PC ∈ mc.prog_addresses ∨ ms.PC = mc.halt_pc ∨
    ms.PC = mc.install_pc ∨ MEM ms.PC mc.ffi_entry_pcs
Proof
  rpt strip_tac
  \\ qpat_x_assum `FST _ ≠ Error` mp_tac
  \\ simp [Once evaluate_def, erase_mc_def, arm8_target_exact_def, arm8_target_def]
  \\ Cases_on `ms.PC ∈ mc.prog_addresses DIFF set mc.ffi_entry_pcs` \\ fs []
  \\ Cases_on `ms.PC = mc.halt_pc` \\ fs []
  \\ Cases_on `ms.PC = mc.install_pc` \\ fs []
  \\ Cases_on `find_index ms.PC mc.ffi_entry_pcs 0` \\ fs []
  \\ imp_res_tac miscTheory.find_index_is_MEM \\ fs []
QED

Theorem uncurry3_eq[local]:
  (∀P x. (let (a, b, c) = x in P a b c) ⇔ P (FST x) (FST (SND x)) (SND (SND x))) ∧
  (∀P x. UNCURRY (λa. UNCURRY (P a)) x ⇔ P (FST x) (FST (SND x)) (SND (SND x)))
Proof
  conj_tac \\ gen_tac \\ PairCases \\ simp []
QED

Theorem real_mc_evaluate_exact_eq:
  ∀k mc B ffi ms.
    mc.mmio_info = [] ∧
    mc.next_interfer = K I ∧
    lo55 mc ∧
    bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    (∀k i bs s. bits_of s = B ⇒
                bits_of (mc.ffi_interfer k (i, bs, s)) = B ∧
                (mc.ffi_interfer k (i, bs, s)).SP_EL0 = s.SP_EL0) ∧
    (∀k bs s. bits_of s = B ⇒
              bits_of (mc.install_interfer k (bs, s)) = B ∧
              (mc.install_interfer k (bs, s)).SP_EL0 = s.SP_EL0) ∧
    (∀j. FST (evaluate (erase_mc B mc) ffi j (erase ms)) ≠ Error) ⇒
    let (res, ms', ffi') = evaluate (erase_mc B mc) ffi k (erase ms) in
    ∃rms'.
      evaluate (real_mc B mc) ffi k ms = (res, rms', ffi') ∧
      erase rms' = ms' ∧ bits_of rms' = B ∧ (¬SND (SND B) ∨ aligned 4 rms'.SP_EL0)
Proof
  Induct_on `k`
  >- (rpt gen_tac \\ strip_tac \\ once_rewrite_tac [evaluate_def] \\ simp [] \\ qexists_tac `ms` \\ simp [])
  \\ rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ PairCases_on `B`
  \\ qpat_x_assum `¬SND (SND _) ∨ _` (assume_tac o SIMP_RULE (srw_ss()) [])
  \\ `FST (evaluate (erase_mc (B0,B1,B2) mc) ffi (SUC k) (erase ms)) ≠ Error` by fs []
  \\ once_rewrite_tac [evaluate_def]
  \\ simp [apply_oracle_def, real_mc_next_interfer_K_I, erase_mc_next_interfer_K_I,
           real_erase_mc_shift_install, real_erase_mc_shift_ffi, real_erase_mc_fields,
           arm8_target_real_def, arm8_target_exact_def, arm8_target_def, erase_fields]
  \\ Cases_on `ms.PC ∈ mc.prog_addresses ∧ ¬MEM ms.PC mc.ffi_entry_pcs` \\ simp []
  >- (
    Cases_on `encoded_bytes_in_mem arm8_config ms.PC ms.MEM mc.prog_addresses`
    >- (
      `arm8_ok (erase ms) ∧
       arm8_ok (arm8$Next (erase ms)) ∧
       (¬B2 ∨ aligned 4 (arm8$Next (erase ms)).SP_EL0) ∧
       (∀x. x ∉ mc.prog_addresses ⇒ (arm8$Next (erase ms)).MEM x = ms.MEM x) ∧
       (∀j. FST (evaluate (erase_mc (B0,B1,B2) mc) ffi j (arm8$Next (erase ms))) ≠ Error)` by
        (rpt conj_tac
         >- (qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
             \\ simp [Once evaluate_def, apply_oracle_def, erase_mc_next_interfer_K_I,
                      real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields]
             \\ IF_CASES_TAC \\ fs [])
         >- (qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
             \\ simp [Once evaluate_def, apply_oracle_def, erase_mc_next_interfer_K_I,
                      real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields]
             \\ IF_CASES_TAC \\ fs [])
         >- (qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
             \\ simp [Once evaluate_def, apply_oracle_def, erase_mc_next_interfer_K_I,
                      real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields]
             \\ IF_CASES_TAC \\ fs [])
         >- (qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
             \\ simp [Once evaluate_def, apply_oracle_def, erase_mc_next_interfer_K_I,
                      real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields]
             \\ IF_CASES_TAC \\ fs [])
         \\ gen_tac \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `SUC j` mp_tac)
         \\ simp [Once evaluate_def, apply_oracle_def, erase_mc_next_interfer_K_I,
                  real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields]
         \\ IF_CASES_TAC \\ fs [])
      \\ `sp_ok ms` by fs [sp_ok_def, arm8_ok_erase, bits_of_def]
      \\ `untagged (arm8$Next (erase ms)).PC` by
           (qspecl_then [`mc`, `(B0,B1,B2)`, `ffi`, `arm8$Next (erase ms)`] mp_tac
              evaluate_exact_non_error_pc_valid
            \\ simp [] \\ strip_tac \\ fs [lo55_def])
      \\ `arm8$Next (erase ms) = erase (arm8$Next ms)` by (drule_all Next_erase \\ simp [])
      \\ `bits_of (arm8$Next ms) = (B0,B1,B2)` by fs [bits_of_def, Next_frame]
      \\ `¬B2 ∨ aligned 4 (arm8$Next ms).SP_EL0` by
           (`(arm8$Next ms).SP_EL0 = (erase (arm8$Next ms)).SP_EL0` by simp [erase_fields] \\ fs [])
      \\ `∀x. x ∉ mc.prog_addresses ⇒ (arm8$Next ms).MEM x = ms.MEM x` by
           (rpt strip_tac
            \\ `(arm8$Next ms).MEM x = (erase (arm8$Next ms)).MEM x` by simp [erase_fields]
            \\ pop_assum SUBST1_TAC
            \\ qpat_x_assum `Next (erase ms) = erase (Next ms)` (fn th => SUBST1_TAC (SYM th))
            \\ simp [])
      \\ `arm8_ok (erase (arm8$Next ms))` by
           (qpat_x_assum `Next (erase ms) = erase (Next ms)` (fn th => SUBST1_TAC (SYM th)) \\ simp [])
      \\ first_x_assum (qspecl_then [`mc`, `(B0,B1,B2)`, `ffi`, `arm8$Next ms`] mp_tac)
      \\ impl_tac >- gvs []
      \\ simp [uncurry3_eq] \\ gvs [])
    \\ qpat_x_assum `FST (evaluate _ _ (SUC k) _) ≠ Error` mp_tac
    \\ simp [Once evaluate_def, real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields])
  \\ Cases_on `ms.PC = mc.halt_pc` \\ simp [erase_fields]
  \\ Cases_on `ms.PC = mc.install_pc` \\ simp []
  >- (
    `read_ffi_bytearray (real_mc (B0,B1,B2) mc) mc.ptr_reg mc.len_reg ms =
     read_ffi_bytearray (erase_mc (B0,B1,B2) mc) mc.ptr_reg mc.len_reg (erase ms)` by
      simp [read_ffi_bytearray_def, real_erase_mc_fields, arm8_target_real_def,
            arm8_target_exact_def, arm8_target_def, erase_fields]
    \\ Cases_on `read_ffi_bytearray (erase_mc (B0,B1,B2) mc) mc.ptr_reg mc.len_reg (erase ms)`
    >- (qpat_x_assum `FST (evaluate _ _ (SUC k) _) ≠ Error` mp_tac
        \\ qpat_x_assum `¬(_ ∧ _)` mp_tac \\ qpat_x_assum `ms.PC ≠ mc.halt_pc` mp_tac
        \\ simp [Once evaluate_def, real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields]
        \\ rw [])
    \\ simp []
    \\ `restore (B0,B1,B2) (erase ms) = ms` by (irule restore_erase \\ simp [])
    \\ qabbrev_tac `mc1 = mc with install_interfer := shift_seq 1 mc.install_interfer`
    \\ qabbrev_tac `rms1 = mc.install_interfer 0 (x, ms)`
    \\ `bits_of rms1 = (B0,B1,B2) ∧ rms1.SP_EL0 = ms.SP_EL0` by (simp [Abbr `rms1`] \\ metis_tac [])
    \\ `∀j. FST (evaluate (erase_mc (B0,B1,B2) mc1) ffi j (erase rms1)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `SUC j` mp_tac)
          \\ qpat_x_assum `¬(_ ∧ _)` mp_tac \\ qpat_x_assum `ms.PC ≠ mc.halt_pc` mp_tac
          \\ simp [Once evaluate_def, apply_oracle_def, real_erase_mc_shift_install,
                   real_erase_mc_fields, arm8_target_exact_def, arm8_target_def,
                   erase_fields, Abbr `mc1`, Abbr `rms1`]
          \\ rw [])
    \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi`, `rms1`] mp_tac)
    \\ impl_tac >- (gvs [Abbr `mc1`, shift_seq_1, lo55_def] \\ metis_tac [])
    \\ simp [uncurry3_eq, Abbr `rms1`] \\ gvs [])
  \\ Cases_on `find_index ms.PC mc.ffi_entry_pcs 0`
  >- (qpat_x_assum `FST (evaluate _ _ (SUC k) _) ≠ Error` mp_tac
      \\ simp [Once evaluate_def, real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields]
      \\ rw [])
  \\ simp []
  \\ Cases_on `EL x mc.ffi_names` \\ simp []
  >- (
    rename1 `EL x mc.ffi_names = ExtCall fnm`
    \\ `read_ffi_bytearrays (real_mc (B0,B1,B2) mc) ms =
        read_ffi_bytearrays (erase_mc (B0,B1,B2) mc) (erase ms)` by
         simp [read_ffi_bytearrays_def, read_ffi_bytearray_def, real_erase_mc_fields,
               arm8_target_real_def, arm8_target_exact_def, arm8_target_def, erase_fields]
    \\ Cases_on `read_ffi_bytearrays (erase_mc (B0,B1,B2) mc) (erase ms)`
    \\ Cases_on `q` \\ Cases_on `r`
    >- (qpat_x_assum `FST (evaluate _ _ (SUC k) _) ≠ Error` mp_tac
        \\ simp [Once evaluate_def, real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields] \\ rw [])
    >- (qpat_x_assum `FST (evaluate _ _ (SUC k) _) ≠ Error` mp_tac
        \\ simp [Once evaluate_def, real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields] \\ rw [])
    >- (qpat_x_assum `FST (evaluate _ _ (SUC k) _) ≠ Error` mp_tac
        \\ simp [Once evaluate_def, real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields] \\ rw [])
    \\ simp []
    \\ Cases_on `call_FFI ffi (ExtCall fnm) x' x''` \\ simp []
    \\ rename1 `call_FFI ffi (ExtCall fnm) x' x'' = FFI_return ffi1 new_bs`
    \\ `restore (B0,B1,B2) (erase ms) = ms` by (irule restore_erase \\ simp [])
    \\ qabbrev_tac `mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer`
    \\ qabbrev_tac `rms1 = mc.ffi_interfer 0 (x, new_bs, ms)`
    \\ `bits_of rms1 = (B0,B1,B2) ∧ rms1.SP_EL0 = ms.SP_EL0` by (simp [Abbr `rms1`] \\ metis_tac [])
    \\ `∀j. FST (evaluate (erase_mc (B0,B1,B2) mc1) ffi1 j (erase rms1)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `SUC j` mp_tac)
          \\ simp [Once evaluate_def, apply_oracle_def, real_erase_mc_shift_ffi,
                   real_erase_mc_fields, arm8_target_exact_def, arm8_target_def,
                   erase_fields, Abbr `mc1`, Abbr `rms1`]
          \\ rw [])
    \\ first_x_assum (qspecl_then [`mc1`, `(B0,B1,B2)`, `ffi1`, `rms1`] mp_tac)
    \\ impl_tac >- (gvs [Abbr `mc1`, shift_seq_1, lo55_def] \\ metis_tac [])
    \\ simp [uncurry3_eq, Abbr `rms1`] \\ gvs [])
  \\ qpat_x_assum `FST (evaluate _ _ (SUC k) _) ≠ Error` mp_tac
  \\ simp [Once evaluate_def, real_erase_mc_fields, arm8_target_exact_def, arm8_target_def, erase_fields] \\ rw []
QED

Theorem machine_sem_real_eq_exact:
  ∀mc B ffi ms.
    mc.mmio_info = [] ∧
    mc.next_interfer = K I ∧
    lo55 mc ∧
    bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    (∀k i bs s. bits_of s = B ⇒
                bits_of (mc.ffi_interfer k (i, bs, s)) = B ∧
                (mc.ffi_interfer k (i, bs, s)).SP_EL0 = s.SP_EL0) ∧
    (∀k bs s. bits_of s = B ⇒
              bits_of (mc.install_interfer k (bs, s)) = B ∧
              (mc.install_interfer k (bs, s)).SP_EL0 = s.SP_EL0) ∧
    ¬machine_sem (erase_mc B mc) ffi (erase ms) Fail ⇒
    machine_sem (real_mc B mc) ffi ms = machine_sem (erase_mc B mc) ffi (erase ms)
Proof
  rpt gen_tac \\ disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  \\ `∀j. FST (evaluate (erase_mc B mc) ffi j (erase ms)) ≠ Error` by
       (qpat_x_assum `¬machine_sem _ _ _ _` mp_tac \\ simp [machine_sem_def])
  \\ `∀k. ∃rms'.
        evaluate (real_mc B mc) ffi k ms =
          (FST (evaluate (erase_mc B mc) ffi k (erase ms)), rms',
           SND (SND (evaluate (erase_mc B mc) ffi k (erase ms))))` by
       (gen_tac
        \\ qspecl_then [`k`, `mc`, `B`, `ffi`, `ms`] mp_tac real_mc_evaluate_exact_eq
        \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
        \\ Cases_on `evaluate (erase_mc B mc) ffi k (erase ms)` \\ Cases_on `r`
        \\ simp [] \\ disch_then strip_assume_tac
        \\ qexists_tac `rms'` \\ simp [])
  \\ simp [FUN_EQ_THM] \\ gen_tac
  \\ Cases_on `x` \\ simp [machine_sem_def]
  >- (
    `∀k. (∃ms' st'. evaluate (real_mc B mc) ffi k ms = (TimeOut, ms', st')) ⇔
         (∃ms' st'. evaluate (erase_mc B mc) ffi k (erase ms) = (TimeOut, ms', st'))` by
      (gen_tac \\ qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac)
       \\ Cases_on `evaluate (erase_mc B mc) ffi k (erase ms)` \\ Cases_on `r` \\ fs []
       \\ eq_tac \\ disch_then strip_assume_tac \\ fs [])
    \\ `∀k. (SND (SND (evaluate (real_mc B mc) ffi k ms))).io_events =
            (SND (SND (evaluate (erase_mc B mc) ffi k (erase ms)))).io_events` by
      (gen_tac \\ qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac) \\ simp [])
    \\ simp [])
  >- (
    eq_tac \\ disch_then strip_assume_tac
    >- (
      qpat_x_assum `∀k. ∃rms'. _` (qspec_then `k` strip_assume_tac)
      \\ Cases_on `evaluate (erase_mc B mc) ffi k (erase ms)` \\ Cases_on `r`
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
  \\ qpat_x_assum `∀j. FST (evaluate _ _ _ _) ≠ Error` (qspec_then `k` mp_tac)
  \\ simp []
QED
