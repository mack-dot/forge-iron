structure forge_m3StepLib =
struct

open HolKernel Parse boolLib bossLib preamble wordsLib arm8_stepLib;
open forge_runtimeSpecTheory forge_airlockContractTheory forge_arm8ErasureTheory
     forge_shimProofTheory forge_airlockShimBaseTheory;

fun mk_cmp_carry k =
  let val kt = numSyntax.term_of_int k in
    REWRITE_RULE [EVAL ``18446744073709551615 - ^kt``]
      (MATCH_MP m3_cmp_carry_k
        (EQT_ELIM (EVAL ``1 ≤ ^kt ∧ ^kt < 18446744073709551616``)))
  end;

val cmp_carry_65  = mk_cmp_carry 65;
val cmp_carry_64  = mk_cmp_carry 64;
val cmp_carry_129 = mk_cmp_carry 129;
val cmp_carry_258 = mk_cmp_carry 258;
val cmp_carry_545 = mk_cmp_carry 545;
val cmp_carry_544 = mk_cmp_carry 544;

val m3_v_list =
  forge_m3_slot_veneers_def |> SPEC_ALL |> concl |> rhs |> listSyntax.dest_list |> fst;
val m3_s_list =
  forge_shim_airlock_words_def |> concl |> rhs |> listSyntax.dest_list |> fst;

fun word32_hex t =
  let
    val n = wordsSyntax.dest_word_literal t
    val s = Arbnum.toHexString n
  in
    if size s < 8 then String.implode (List.tabulate (8 - size s, K #"0")) ^ s else s
  end;

local
  val w32_cons = CONJUNCT2 words32_in_mem_def
  val addr_conv = LAND_CONV (RAND_CONV (fn t => if null (free_vars t) then wordsLib.WORD_EVAL_CONV t else ALL_CONV t))
  val byte_conv = RAND_CONV (fn t => if null (free_vars t) then wordsLib.WORD_EVAL_CONV t else ALL_CONV t)
  val eq_conv = addr_conv THENC byte_conv
  val next_addr_conv = RATOR_CONV (RATOR_CONV (RAND_CONV wordsLib.WORD_EVAL_CONV))
  fun peel acc th =
    let
      val ws = el 2 (snd (strip_comb (concl th)))
    in
      if listSyntax.is_nil ws then List.rev acc
      else
        let
          val th1 = CONV_RULE (REWR_CONV w32_cons) th
          val c0 = CONV_RULE eq_conv (CONJUNCT1 th1)
          val t1 = CONJUNCT2 th1
          val c1 = CONV_RULE eq_conv (CONJUNCT1 t1)
          val t2 = CONJUNCT2 t1
          val c2 = CONV_RULE eq_conv (CONJUNCT1 t2)
          val t3 = CONJUNCT2 t2
          val c3 = CONV_RULE eq_conv (CONJUNCT1 t3)
          val rest = CONV_RULE next_addr_conv (CONJUNCT2 t3)
        in
          peel (c3 :: c2 :: c1 :: c0 :: acc) rest
        end
    end
in
  val m3_v_arr =
    Vector.fromList (peel [] (
      PURE_ONCE_REWRITE_RULE [forge_m3_slot_veneers_def, FORGE_M3_VENEERS_BASE_def]
        (ASSUME ``words32_in_mem FORGE_M3_VENEERS_BASE (forge_m3_slot_veneers cb_begin cb_end bm_buf_end) (m:word64 -> word8)``)))
  val m3_s_arr =
    Vector.fromList (peel [] (
      PURE_ONCE_REWRITE_RULE [forge_shim_airlock_words_def, FORGE_M3_SHIM_BASE_def]
        (ASSUME ``words32_in_mem FORGE_M3_SHIM_BASE forge_shim_airlock_words (m:word64 -> word8)``)))
end;
val m3_v_warr = Vector.fromList m3_v_list;
val m3_s_warr = Vector.fromList m3_s_list;

val step_cache : (string * thm list) list ref = ref [];
fun cached_step h =
  case List.find (fn (k, _) => k = h) (!step_cache) of
    SOME (_, ths) => ths
  | NONE =>
      let val ths = arm8_stepLib.arm8_step_hex h
      in step_cache := (h, ths) :: !step_cache; ths end;

fun is_std_hyp t =
  let val s = term_to_string t in
    String.isSubstring "SCTLR_EL1" s orelse
    String.isSubstring "TCR_EL1" s orelse
    String.isSubstring ".EL =" s orelse
    String.isSubstring ".exception =" s orelse
    String.isSubstring ".MEM " s orelse
    String.isSubstring "aligned 2 " s
  end;

fun get_m3_word_info kind idx =
  case kind of
    "veneer" =>
      (0x00400000 + 4 * idx,
       word32_hex (Vector.sub (m3_v_warr, idx)),
       List.tabulate (4, fn j => Vector.sub (m3_v_arr, 4 * idx + j)))
  | "shim" =>
      (0x00450000 + 4 * idx,
       word32_hex (Vector.sub (m3_s_warr, idx)),
       List.tabulate (4, fn j => Vector.sub (m3_s_arr, 4 * idx + j)))
  | _ => failwith ("unknown kind: " ^ kind);

val load_hyp = ``m3_shim_loaded_slot cb_begin cb_end bm_buf_end (s:arm8_state).MEM``;

fun inst_some_hyps th =
  let
    fun match_eq h =
      if is_eq h then
        let val (l, r) = dest_eq h in
          if optionSyntax.is_some l andalso optionSyntax.is_some r then
            let val (l', r') = (optionSyntax.dest_some l, optionSyntax.dest_some r) in
              if pairSyntax.is_pair l' andalso pairSyntax.is_pair r' then
                let val (l1, l2) = pairSyntax.dest_pair l'
                    val (r1, r2) = pairSyntax.dest_pair r' in
                  if is_var r1 andalso is_var r2 then [(r1 |-> l1), (r2 |-> l2)]
                  else if is_var l1 andalso is_var l2 then [(l1 |-> r1), (l2 |-> r2)]
                  else []
                end
              else if is_var r' then [r' |-> l']
              else if is_var l' then [l' |-> r']
              else []
            end
          else []
        end
      else []
    val subst = List.concat (map match_eq (Thm.hyp th))
    val th1 = if null subst then th else Thm.INST subst th
    fun drop_refl h acc =
      if is_eq h andalso aconv (lhs h) (rhs h) then PROVE_HYP (REFL (lhs h)) acc else acc
  in
    List.foldl (fn (h, acc) => drop_refl h acc) th1 (Thm.hyp th1)
  end;

fun prove_m3_step kind idx branch_idx =
  let
    val (addr_n, hex, bths) = get_m3_word_info kind idx
    val addr_tm = wordsSyntax.mk_wordii (addr_n, 64)
    val raw_th = inst_some_hyps (List.nth (cached_step hex, branch_idx))
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
        [m3_restore_erase_record_upds, erase_fields, ASSUME pc_eq]
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
        fs [m3_shim_loaded_slot_def]
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
        \\ simp [m3_restore_erase_record_upds, erase_fields])
      \\ gvs [m3_shim_loaded_slot_def, is_svc0_at_def]
      \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) inst_bths)
      \\ gvs [])
  end;

fun prove_m3_svc0_at kind idx =
  let
    val (addr_n, _, bths) = get_m3_word_info kind idx
    val addr_tm = wordsSyntax.mk_wordii (addr_n, 64)
    val inst_bths = map (DISCH_ALL o Thm.INST [``m:word64 -> word8`` |-> ``(s:arm8_state).MEM``]) bths
  in
    GEN_ALL (prove (``^load_hyp ∧ (s:arm8_state).PC = ^addr_tm ⇒ is_svc0_at s``,
      rpt strip_tac
      \\ gvs [m3_shim_loaded_slot_def, is_svc0_at_def]
      \\ EVERY (map (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac) inst_bths)
      \\ simp []))
  end;

fun fast_eval (g as (_, w)) =
  if can (find_term (fn t => is_const t andalso fst (dest_const t) = "m3_shim_loaded_slot")) w
  then NO_TAC g else (EVAL_TAC \\ NO_TAC) g;

fun step_m3_det th (g as (asl, w)) =
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
                  m3_shim_loaded_slot_update, forge_m3_shim_code_region_def,
                  FORGE_M3_VENEERS_BASE_def, FORGE_M3_CAKE_MAIN_def,
                  FORGE_M3_SHIM_BASE_def, FORGE_M3_SHIM_END_def,
                  wordsTheory.word_lo_n2w, wordsTheory.word_ls_n2w, dimword_64,
                  m3_word_add_n2w_right, wordsTheory.word_add_n2w,
                  cmp_carry_65, cmp_carry_64, cmp_carry_129, cmp_carry_258,
                  cmp_carry_545, cmp_carry_544,
                  m3_cmp_zero_gt_cond, m3_cmn_4_zero,
                  m3_extend_uxtx_0, m3_w2w_w2w_word8_word64]
         \\ TRY fast_eval)
     \\ disch_then (fn th' =>
          qexists_tac `^(th' |> concl |> dest_conj |> fst |> rand |> rand)`
          \\ conj_tac >- ACCEPT_TAC (CONJUNCT2 th')
          \\ conj_tac >- ACCEPT_TAC (CONJUNCT1 th'))
     \\ SIMP_TAC (srw_ss() ++ wordsLib.WORD_ss)
          [combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ,
           m3_extend_uxtx_0, m3_w2w_w2w_word8_word64, m3_cmp_zero_gt_cond]) g
  end;

val m3_peel_nrc_tac =
  qpat_x_assum `det_run _ _ _` (fn dth =>
    qpat_x_assum `NRC _ _ _ _` (fn nth =>
      mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] m3_det_run_peel_nrc) dth)
      \\ disch_then (fn th => mp_tac (MATCH_MP th nth))
      \\ disch_then (fn th => first_assum (mp_tac o MATCH_MP th))
      \\ strip_tac));

end;
