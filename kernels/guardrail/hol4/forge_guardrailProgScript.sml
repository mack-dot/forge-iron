(*
  Forge Milestone 2: Zero-SL CakeML Guardrail Kernel Program & Whole-Program Semantics.

  Synthesizes CakeML code and refinement theorems automatically from the frozen
  91-line pure HOL4 spec (`forge_guardrailSpec`) via `ml_translatorLib.translate`,
  and composes with the frozen generic 64-byte frame runner (`forge_frameRunner`).
  Zero manual Separation Logic (`W8ARRAY`) and zero manual assembly proofs.
*)
Theory forge_guardrailProg
Ancestors
  forge_guardrailSpec forge_frame64Spec forge_frameRunner cfMain
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib cfLib cfTacticsLib

val _ = translation_extends "forge_frameRunner";

Theorem dest_allowed_ml_eq[local]:
  ∀(mask:word64) (d:word64). dest_allowed mask d ⇔ d <₊ 64w ∧ ((mask ⋙ w2n d) && 1w ≠ 0w)
Proof
  rpt gen_tac \\ simp [dest_allowed_def]
  \\ Cases_on `d <₊ 64w` \\ simp []
  \\ `w2n d < 64` by fs [wordsTheory.WORD_LO]
  \\ `∀x:word64. (1w && x ≠ 0w) ⇔ x ' 0` by blastLib.BBLAST_TAC
  \\ simp [wordsTheory.word_bit_def, wordsTheory.word_lsr_def, fcpTheory.FCP_BETA]
QED

(* Automatically translate frozen pure HOL4 guardrail spec into CakeML + refinement thms *)
val gr_init_thm      = translate gr_init_def;
val dest_allowed_thm = translate dest_allowed_ml_eq;
val gr_resp_thm      = translate gr_resp_def;
val gr_step_thm      = translate gr_step_def;

val GR_STATE_TYPE_tm = ml_translatorLib.get_type_inv ``:gr_state``;

Quote add_cakeml:
  fun guardrail_main u = run_frame64_kernel gr_step gr_init
End

val st = get_ml_prog_state ();

(* Build whole program AST: declarations ++ [guardrail_main ()] *)

val Decls_raw =
  st
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def];

val prog_decs = Decls_raw |> concl |> rator |> rator |> rand;

val main_call_tm =
  ``Dlet NoLocs (Pcon NONE []) (App Opapp [Var (Short «guardrail_main»); Con NONE []])``;

val snoc_eq_thm =
  (PURE_REWRITE_CONV [listTheory.SNOC_APPEND] THENC
   PURE_REWRITE_CONV [GSYM listTheory.APPEND_ASSOC] THENC
   PURE_REWRITE_CONV [listTheory.APPEND]) ``SNOC ^main_call_tm ^prog_decs``;

Definition guardrail_prog_def[compute]:
  guardrail_prog = ^(rhs (concl snoc_eq_thm))
End

Theorem guardrail_prog_eq_snoc:
  guardrail_prog = SNOC ^main_call_tm ^prog_decs
Proof
  rewrite_tac [guardrail_prog_def, GSYM snoc_eq_thm]
QED

Theorem stop_after_err64_prefix_eq:
  ∀es1 es2.
    es1 ≼ es2 ∧ stop_after_err64 es2 ∧ (∃e. MEM e es1 ∧ event_is_err64 e) ⇒
    es2 = es1
Proof
  Induct \\ simp []
  \\ rpt strip_tac
  \\ Cases_on `es2` \\ fs [stop_after_err64_def]
  \\ rveq
  \\ Cases_on `event_is_err64 h` \\ fs []
  \\ first_x_assum irule \\ simp [] \\ metis_tac []
QED

(* CF specification of guardrail_main — zero manual W8ARRAY reasoning *)

Theorem guardrail_main_spec:
  ∀inps wlim uv.
    UNIT_TYPE () uv ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "guardrail_main" st) [uv]
      (FRAME64_IO_EV <| inputs := inps; outputs := []; write_limit := wlim |> [])
      (POSTv rv.
        &(UNIT_TYPE () rv) *
        (SEP_EXISTS rest_inps wlim' evs'.
          &(stop_after_err64 evs') *
          FRAME64_IO_EV <| inputs := rest_inps;
                           outputs := limit_frames64 wlim (SND (frame64_run gr_step gr_init inps));
                           write_limit := wlim' |> evs'))
Proof
  rpt strip_tac
  \\ xcf "guardrail_main" st
  \\ xapp_spec (ISPEC GR_STATE_TYPE_tm run_frame64_kernel_spec)
  \\ xsimpl \\ simp [gr_init_thm, gr_step_thm]
QED

(* Whole-program CakeML source semantics theorem *)

local
  val lem_vs = Decls_raw |> concl |> free_vars
  val ffi_var = lem_vs |> filter (fn v => fst (dest_var v) = "ffi") |> hd
  val po_var  = lem_vs |> filter (fn v => fst (dest_var v) = "po") |> hd
  val eq_init_st = Q.prove (
    `init_state (frame64_ffi io) with ptr_eq_oracle := K (K F) = init_state (frame64_ffi io)`,
    simp [ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality])
  val decls_inst =
    Decls_raw
    |> GEN ffi_var |> ISPEC ``frame64_ffi (io:frame64_io)``
    |> GEN po_var  |> ISPEC ``(K (K F) : num -> num -> bool)``
    |> CONV_RULE (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV eq_init_st)))))
  val res_env = decls_inst |> concl |> rator |> rand
  val res_st  = decls_inst |> concl |> rand
  val lookup_tm = ``nsLookup (^res_env).v (Short «guardrail_main»)``
  val lookup_thm =
    prove (mk_eq (lookup_tm, optionSyntax.mk_some (fetch_v "guardrail_main" st)),
           REWRITE_TAC [ml_progLib.nsLookup_conv lookup_tm])
  val ffi_eq_thm =
    prove (``(^res_st).ffi = frame64_ffi io``, EVAL_TAC)
in
  val guardrail_Decls_thm  = decls_inst
  val guardrail_lookup_thm = lookup_thm
  val guardrail_ffi_eq_thm = ffi_eq_thm
end;

val call_main_gen =
  Q.GENL [`env1`, `st1`, `prog`, `env2`, `st2`, `fname`, `fv`, `proj1`, `proj2`, `P`, `Q`, `h1`, `h2`]
    cfMainTheory.call_main_thm2;

Theorem guardrail_semantics:
  ∀io.
    io.outputs = [] ⇒
    semanticsProps$sem_satisfies
      (semantics_dec_list (init_state (frame64_ffi io)) init_env guardrail_prog)
      (λb. ∃io_events.
             b = Terminate Success io_events ∧
             stop_after_err64 io_events ∧
             sent_frames64_of io_events =
               limit_frames64 io.write_limit (SND (frame64_run gr_step gr_init io.inputs)))
Proof
  rpt strip_tac
  \\ qabbrev_tac `inps = io.inputs`
  \\ qabbrev_tac `wlim = io.write_limit`
  \\ `io = <| inputs := inps; outputs := []; write_limit := wlim |>` by
       simp [frame64_io_component_equality, Abbr `inps`, Abbr `wlim`]
  \\ pop_assum SUBST_ALL_TAC \\ simp []
  \\ rewrite_tac [guardrail_prog_eq_snoc]
  \\ qspecl_then [`inps`, `wlim`, `Conv NONE []`] mp_tac
       (INST_TYPE [mk_vartype "'ffi" |-> ``:frame64_io``] guardrail_main_spec
        |> Q.GEN `p` |> Q.SPEC `frame64_proj`)
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac
  \\ qspec_then `<| inputs := inps; outputs := []; write_limit := wlim |>` assume_tac
       (GEN ``io:frame64_io`` guardrail_Decls_thm)
  \\ qspec_then `<| inputs := inps; outputs := []; write_limit := wlim |>` assume_tac
       (GEN ``io:frame64_io`` guardrail_ffi_eq_thm)
  \\ drule frame64_io_split \\ strip_tac
  \\ qpat_x_assum `Decls _ _ _ _ _` (mp_tac o MATCH_MP call_main_gen)
  \\ disch_then (qspecl_then [`«guardrail_main»`, `^(fetch_v "guardrail_main" st)`,
                              `FST frame64_proj`, `SND frame64_proj`,
                              `FRAME64_IO_EV <| inputs := inps; outputs := []; write_limit := wlim |> []`,
                              `SEP_EXISTS rest_inps wlim' evs'.
                                 &(stop_after_err64 evs') *
                                 FRAME64_IO_EV <| inputs := rest_inps;
                                                  outputs := limit_frames64 wlim (SND (frame64_run gr_step gr_init inps));
                                                  write_limit := wlim' |> evs'`,
                              `h1`, `h2`] mp_tac)
  \\ simp [ml_progTheory.lookup_var_def, guardrail_lookup_thm, frame64_io_ffi_part_hprop]
  \\ simp [semanticsPropsTheory.sem_satisfies_def]
  \\ rpt strip_tac
  \\ qpat_x_assum `∀behavior. _ ⇒ _` (qspec_then `b` mp_tac)
  \\ impl_tac >- first_assum ACCEPT_TAC
  \\ strip_tac
  \\ rveq \\ qexists_tac `st3.ffi.io_events` \\ simp []
  \\ qpat_x_assum `$SEP_EXISTS _ _` mp_tac
  \\ simp [set_sepTheory.SEP_EXISTS_THM, FRAME64_IO_EV_def, set_sepTheory.one_def,
           set_sepTheory.STAR_def, set_sepTheory.cond_def,
           set_sepTheory.SPLIT_def, set_sepTheory.emp_def]
  \\ strip_tac \\ rveq
  \\ qmatch_asmsub_abbrev_tac `SPLIT3 _ ({ffip}, _, _)`
  \\ `ffip ∈ st2heap frame64_proj st3` by
       (qpat_x_assum `SPLIT3 _ _` mp_tac \\ simp [cfHeapsBaseTheory.SPLIT3_def, EXTENSION] \\ metis_tac [])
  \\ qpat_x_assum `ffip ∈ st2heap _ _` mp_tac
  \\ simp [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           frame64_proj_def, cfStoreTheory.ffi2heap_def, Abbr `ffip`]
  \\ simp [GSYM frame64_proj_def]
  \\ Cases_on `cfStore$parts_ok st3.ffi frame64_proj` \\ simp []
  \\ strip_tac
  \\ conj_tac
  >- (
    `FILTER (cfStore$ffi_has_index_in [«recv64»; «send64»]) st3.ffi.io_events = st3.ffi.io_events` by
      (qpat_x_assum `cfStore$parts_ok _ _` mp_tac
       \\ simp [listTheory.FILTER_EQ_ID, cfStoreTheory.parts_ok_def, frame64_proj_def])
    \\ fs [])
  \\ qpat_x_assum `∀n. _ ⇒ _` (qspec_then `«recv64»` mp_tac)
  \\ simp [FUPDATE_LIST_THM, FLOOKUP_UPDATE, encode_frame64_io_11]
  \\ strip_tac
  \\ qpat_x_assum `call_FFI_rel꙳ _ _` mp_tac
  \\ simp [ml_progTheory.init_state_def]
  \\ strip_tac
  \\ qspecl_then [`<| inputs := inps; outputs := []; write_limit := wlim |>`, `st3.ffi`] mp_tac
       frame64_ffi_outputs_eq_sent_frames
  \\ simp []
QED
