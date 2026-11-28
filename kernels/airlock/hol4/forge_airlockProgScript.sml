(*
  Forge Milestone 3: Zero-SL CakeML Crypto-Airlock Kernel Program & Whole-Program Semantics.

  Synthesizes CakeML code and refinement theorems automatically from the SHA-256 pinned
  pure HOL4 specs (`forge_sha256Spec` + `forge_airlockSpec`) via `ml_translatorLib.translate`,
  and composes with the generic 4-FFI airlock runner (`forge_airlockRunner`).
  Zero manual Separation Logic (`W8ARRAY`) and zero manual assembly proofs.
*)
Theory forge_airlockProg
Ancestors
  forge_sha256Spec forge_airlockSpec forge_frame64Spec forge_airlockFfi forge_airlockRunner cfMain
Libs
  preamble blastLib ml_translatorLib ml_progLib basisFunctionsLib cfLib cfTacticsLib

val _ = translation_extends "forge_airlockRunner";

(* List helpers needed by SHA-256 & slot encoding/validation *)
val _ = translate listTheory.LENGTH;
val _ = translate listTheory.APPEND;
val _ = translate rich_listTheory.REPLICATE;
val _ = translate listTheory.TAKE_def;
val _ = translate listTheory.DROP_def;

(* Translate SHA-256 & HMAC-SHA256 (forge_sha256Spec) *)
val _ = translate be32_of_bytes_def;
val _ = translate be32_to_bytes_def;
val _ = translate be64_to_bytes_def;
val _ = translate bytes_to_be32s_def;
val _ = translate sha256_iv_def;
val _ = translate sha256_k_def;
Theorem sha256_ch_ml_eq[local]:
  ∀x y z:word32. sha256_ch x y z = (x && y) ⊕ ((x ⊕ 0xFFFFFFFFw) && z)
Proof
  simp [sha256_ch_def] \\ blastLib.BBLAST_TAC
QED

Theorem sha256_bsig0_ml_eq[local]:
  ∀x:word32. sha256_bsig0 x = ((x ⋙ 2) ‖ (x ≪ 30)) ⊕ ((x ⋙ 13) ‖ (x ≪ 19)) ⊕ ((x ⋙ 22) ‖ (x ≪ 10))
Proof
  simp [sha256_bsig0_def] \\ blastLib.BBLAST_TAC
QED

Theorem sha256_bsig1_ml_eq[local]:
  ∀x:word32. sha256_bsig1 x = ((x ⋙ 6) ‖ (x ≪ 26)) ⊕ ((x ⋙ 11) ‖ (x ≪ 21)) ⊕ ((x ⋙ 25) ‖ (x ≪ 7))
Proof
  simp [sha256_bsig1_def] \\ blastLib.BBLAST_TAC
QED

Theorem sha256_ssig0_ml_eq[local]:
  ∀x:word32. sha256_ssig0 x = ((x ⋙ 7) ‖ (x ≪ 25)) ⊕ ((x ⋙ 18) ‖ (x ≪ 14)) ⊕ (x ⋙ 3)
Proof
  simp [sha256_ssig0_def] \\ blastLib.BBLAST_TAC
QED

Theorem sha256_ssig1_ml_eq[local]:
  ∀x:word32. sha256_ssig1 x = ((x ⋙ 17) ‖ (x ≪ 15)) ⊕ ((x ⋙ 19) ‖ (x ≪ 13)) ⊕ (x ⋙ 10)
Proof
  simp [sha256_ssig1_def] \\ blastLib.BBLAST_TAC
QED

val _ = translate sha256_ch_ml_eq;
val _ = translate sha256_maj_def;
val _ = translate sha256_bsig0_ml_eq;
val _ = translate sha256_bsig1_ml_eq;
val _ = translate sha256_ssig0_ml_eq;
val _ = translate sha256_ssig1_ml_eq;
val _ = translate sha256_round_def;
val _ = translate sha256_rounds_def;
val _ = translate sha256_compress_def;
val _ = translate sha256_word_blocks_def;

val sha256_pad_thm = translate sha256_pad_def;
Theorem sha256_pad_side_thm[local]:
  ∀msg. sha256_pad_side msg
Proof
  gen_tac \\ simp [fetch "-" "sha256_pad_side_def"]
  \\ `LENGTH msg MOD 64 < 64` by simp [] \\ decide_tac
QED
val _ = update_precondition sha256_pad_side_thm;

val _ = translate sha256_finalize_def;
val _ = translate sha256_def;
val _ = translate hmac_xor_bytes_def;
val hmac_sha256_thm = translate hmac_sha256_def;
Theorem hmac_sha256_side_thm[local]:
  ∀key msg. hmac_sha256_side key msg
Proof
  rpt gen_tac \\ simp [fetch "-" "hmac_sha256_side_def", LENGTH_sha256]
  \\ IF_CASES_TAC \\ simp [LENGTH_sha256]
QED
val _ = update_precondition hmac_sha256_side_thm;

Theorem le64_encode_ml_eq[local]:
  ∀w:word64.
    le64_encode w =
      [w2w w; w2w (w ⋙ 8); w2w (w ⋙ 16); w2w (w ⋙ 24);
       w2w (w ⋙ 32); w2w (w ⋙ 40); w2w (w ⋙ 48); w2w (w ⋙ 56)]
Proof
  simp [le64_encode_def, le64_byte_def]
QED

(* Translate Airlock Spec (forge_airlockSpec) *)
val _ = translate le64_encode_ml_eq;
val _ = translate le64_decode_def;
val _ = translate le64_take_def;
val _ = translate bytes32_to_w64x4_def;
val _ = translate cap_domain_def;
val _ = translate cap_token_msg_def;
val _ = translate mint_cap_tag_def;
val _ = translate airlock_init_def;
val _ = translate al_dest_allowed_def;
val _ = translate al_resp_plain_def;
val _ = translate al_resp_tok_def;
val airlock_step_thm      = translate airlock_step_def;
val _                     = translate airlock_inv_def;
val _                     = translate SLOT_MAGIC_def;
val _                     = translate encode_slot_body_def;
val encode_slot_thm       = translate encode_slot_def;
val _                     = translate decode_slot_raw_def;
val _                     = translate slot_valid_def;
val recover_dual_slot_thm = translate recover_dual_slot_def;
val _                     = translate commit_slot_byte_def;

Definition commit_slot_of_state_def:
  commit_slot_of_state (st:airlock_state) : word8 = commit_slot_byte st.gen
End
val commit_slot_of_state_thm = translate commit_slot_of_state_def;

val AIRLOCK_STATE_TYPE_tm = ml_translatorLib.get_type_inv ``:airlock_state``;

Quote add_cakeml:
  fun airlock_main u =
    run_airlock_kernel recover_dual_slot airlock_step encode_slot commit_slot_of_state
End

val st = get_ml_prog_state ();

(* Build whole program AST: declarations ++ [airlock_main ()] *)

val Decls_raw =
  st
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def];

val prog_decs = Decls_raw |> concl |> rator |> rator |> rand;

val main_call_tm =
  ``Dlet NoLocs (Pcon NONE []) (App Opapp [Var (Short «airlock_main»); Con NONE []])``;

val snoc_eq_thm =
  (PURE_REWRITE_CONV [listTheory.SNOC_APPEND] THENC
   PURE_REWRITE_CONV [GSYM listTheory.APPEND_ASSOC] THENC
   PURE_REWRITE_CONV [listTheory.APPEND]) ``SNOC ^main_call_tm ^prog_decs``;

Definition airlock_prog_def[compute]:
  airlock_prog = ^(rhs (concl snoc_eq_thm))
End

Theorem airlock_prog_eq_snoc:
  airlock_prog = SNOC ^main_call_tm ^prog_decs
Proof
  rewrite_tac [airlock_prog_def, GSYM snoc_eq_thm]
QED

(* CF specification of airlock_main — zero manual W8ARRAY reasoning *)

Theorem airlock_main_spec:
  ∀bk bf sA sB inps clim wlim uv.
    UNIT_TYPE () uv ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "airlock_main" st) [uv]
      (AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                        inputs := inps; outputs := [];
                        commit_limit := clim; write_limit := wlim |> [])
      (POSTv rv.
        &(UNIT_TYPE () rv) *
        (SEP_EXISTS sA' sB' rest_inps clim' wlim' evs'.
          &(stop_after_err_al evs' ∧ boot_first_once_al evs') *
          AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB';
                           inputs := rest_inps;
                           outputs :=
                             if ¬bf ∧ LENGTH bk = 32 ∧ LENGTH sA = 256 ∧ LENGTH sB = 256 then
                               SND (airlock_exec airlock_step bk (recover_dual_slot bk sA sB) inps clim wlim)
                             else [];
                           commit_limit := clim'; write_limit := wlim' |> evs'))
Proof
  rpt strip_tac
  \\ xcf "airlock_main" st
  \\ xapp_spec (ISPEC AIRLOCK_STATE_TYPE_tm run_airlock_kernel_spec)
  \\ xsimpl
  \\ simp [recover_dual_slot_thm, airlock_step_thm]
  \\ conj_tac
  >- (qexists_tac `commit_slot_of_state` \\ simp [commit_slot_of_state_thm])
  \\ qexists_tac `encode_slot` \\ simp [encode_slot_thm, LENGTH_encode_slot]
QED

(* Whole-program CakeML source semantics theorem *)

local
  val lem_vs = Decls_raw |> concl |> free_vars
  val ffi_var = lem_vs |> filter (fn v => fst (dest_var v) = "ffi") |> hd
  val po_var  = lem_vs |> filter (fn v => fst (dest_var v) = "po") |> hd
  val eq_init_st = Q.prove (
    `init_state (airlock_ffi io) with ptr_eq_oracle := K (K F) = init_state (airlock_ffi io)`,
    simp [ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality])
  val decls_inst =
    Decls_raw
    |> GEN ffi_var |> ISPEC ``airlock_ffi (io:airlock_io)``
    |> GEN po_var  |> ISPEC ``(K (K F) : num -> num -> bool)``
    |> CONV_RULE (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV eq_init_st)))))
  val res_env = decls_inst |> concl |> rator |> rand
  val res_st  = decls_inst |> concl |> rand
  val lookup_tm = ``nsLookup (^res_env).v (Short «airlock_main»)``
  val lookup_thm =
    prove (mk_eq (lookup_tm, optionSyntax.mk_some (fetch_v "airlock_main" st)),
           REWRITE_TAC [ml_progLib.nsLookup_conv lookup_tm])
  val ffi_eq_thm =
    prove (``(^res_st).ffi = airlock_ffi io``, EVAL_TAC)
in
  val airlock_Decls_thm  = decls_inst
  val airlock_lookup_thm = lookup_thm
  val airlock_ffi_eq_thm = ffi_eq_thm
end;

val call_main_gen =
  Q.GENL [`env1`, `st1`, `prog`, `env2`, `st2`, `fname`, `fv`, `proj1`, `proj2`, `P`, `Q`, `h1`, `h2`]
    cfMainTheory.call_main_thm2;

Theorem airlock_semantics:
  ∀io.
    io.outputs = [] ⇒
    semanticsProps$sem_satisfies
      (semantics_dec_list (init_state (airlock_ffi io)) init_env airlock_prog)
      (λb. ∃io_events.
             b = Terminate Success io_events ∧
             stop_after_err_al io_events ∧
             boot_first_once_al io_events ∧
             sent_frames128_of io_events =
               if ¬io.boot_fail ∧ LENGTH io.boot_key = 32 ∧
                  LENGTH io.slotA = 256 ∧ LENGTH io.slotB = 256 then
                 SND (airlock_exec airlock_step io.boot_key
                        (recover_dual_slot io.boot_key io.slotA io.slotB)
                        io.inputs io.commit_limit io.write_limit)
               else [])
Proof
  rpt strip_tac
  \\ qabbrev_tac `bk = io.boot_key`
  \\ qabbrev_tac `bf = io.boot_fail`
  \\ qabbrev_tac `sA = io.slotA`
  \\ qabbrev_tac `sB = io.slotB`
  \\ qabbrev_tac `inps = io.inputs`
  \\ qabbrev_tac `clim = io.commit_limit`
  \\ qabbrev_tac `wlim = io.write_limit`
  \\ `io = <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
              inputs := inps; outputs := []; commit_limit := clim; write_limit := wlim |>` by
       simp [airlock_io_component_equality, Abbr `bk`, Abbr `bf`, Abbr `sA`, Abbr `sB`,
             Abbr `inps`, Abbr `clim`, Abbr `wlim`]
  \\ pop_assum SUBST_ALL_TAC \\ simp []
  \\ rewrite_tac [airlock_prog_eq_snoc]
  \\ qspecl_then [`bk`, `bf`, `sA`, `sB`, `inps`, `clim`, `wlim`, `Conv NONE []`] mp_tac
       (INST_TYPE [mk_vartype "'ffi" |-> ``:airlock_io``] airlock_main_spec
        |> Q.GEN `p` |> Q.SPEC `airlock_proj`)
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac
  \\ qspec_then `<| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                    inputs := inps; outputs := []; commit_limit := clim; write_limit := wlim |>`
       assume_tac (GEN ``io:airlock_io`` airlock_Decls_thm)
  \\ qspec_then `<| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                    inputs := inps; outputs := []; commit_limit := clim; write_limit := wlim |>`
       assume_tac (GEN ``io:airlock_io`` airlock_ffi_eq_thm)
  \\ drule airlock_io_split \\ strip_tac
  \\ qpat_x_assum `Decls _ _ _ _ _` (mp_tac o MATCH_MP call_main_gen)
  \\ disch_then (qspecl_then
       [`«airlock_main»`, `^(fetch_v "airlock_main" st)`,
        `FST airlock_proj`, `SND airlock_proj`,
        `AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                          inputs := inps; outputs := []; commit_limit := clim; write_limit := wlim |> []`,
        `SEP_EXISTS sA' sB' rest_inps clim' wlim' evs'.
           &(stop_after_err_al evs' ∧ boot_first_once_al evs') *
           AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB';
                            inputs := rest_inps;
                            outputs :=
                              if ¬bf ∧ LENGTH bk = 32 ∧ LENGTH sA = 256 ∧ LENGTH sB = 256 then
                                SND (airlock_exec airlock_step bk (recover_dual_slot bk sA sB) inps clim wlim)
                              else [];
                            commit_limit := clim'; write_limit := wlim' |> evs'`,
        `h1`, `h2`] mp_tac)
  \\ simp [ml_progTheory.lookup_var_def, airlock_lookup_thm, airlock_io_ffi_part_hprop]
  \\ simp [semanticsPropsTheory.sem_satisfies_def]
  \\ rpt strip_tac
  \\ qpat_x_assum `∀behavior. _ ⇒ _` (qspec_then `b` mp_tac)
  \\ impl_tac >- first_assum ACCEPT_TAC
  \\ strip_tac
  \\ rveq \\ qexists_tac `st3.ffi.io_events` \\ simp []
  \\ qpat_x_assum `$SEP_EXISTS _ _` mp_tac
  \\ simp [set_sepTheory.SEP_EXISTS_THM, AIRLOCK_IO_EV_def, set_sepTheory.one_def,
           set_sepTheory.STAR_def, set_sepTheory.cond_def,
           set_sepTheory.SPLIT_def, set_sepTheory.emp_def]
  \\ strip_tac \\ rveq
  \\ qmatch_asmsub_abbrev_tac `SPLIT3 _ ({ffip}, _, _)`
  \\ `ffip ∈ st2heap airlock_proj st3` by
       (qpat_x_assum `SPLIT3 _ _` mp_tac \\ simp [cfHeapsBaseTheory.SPLIT3_def, EXTENSION] \\ metis_tac [])
  \\ qpat_x_assum `ffip ∈ st2heap _ _` mp_tac
  \\ simp [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           airlock_proj_def, cfStoreTheory.ffi2heap_def, Abbr `ffip`]
  \\ simp [GSYM airlock_proj_def]
  \\ Cases_on `cfStore$parts_ok st3.ffi airlock_proj` \\ simp []
  \\ strip_tac
  \\ `FILTER (cfStore$ffi_has_index_in airlock_ffi_names) st3.ffi.io_events = st3.ffi.io_events` by
       (qpat_x_assum `cfStore$parts_ok _ _` mp_tac
        \\ simp [listTheory.FILTER_EQ_ID, cfStoreTheory.parts_ok_def, airlock_proj_def])
  \\ conj_tac >- fs []
  \\ conj_tac >- fs []
  \\ qpat_x_assum `∀n. _ ⇒ _` (qspec_then `«bootload»` mp_tac)
  \\ simp [airlock_ffi_names_def, FUPDATE_LIST_THM, FLOOKUP_UPDATE, encode_airlock_io_11]
  \\ strip_tac
  \\ qpat_x_assum `call_FFI_rel꙳ _ _` mp_tac
  \\ simp [ml_progTheory.init_state_def]
  \\ strip_tac
  \\ qspecl_then
       [`<| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
            inputs := inps; outputs := []; commit_limit := clim; write_limit := wlim |>`, `st3.ffi`]
       mp_tac airlock_ffi_outputs_eq_sent_frames
  \\ simp []
QED
