(*
  Forge Milestone 1: Zero-Basis CakeML Counter Program & CF Correctness Proof.
  Extends Word8ArrayProg only (zero TextIO, fsFFI, CommandLine, Runtime, basis_ffi.c).
  Allocates one 17-byte Word8Array outside the loop and calls only FFI "recv16" and "send16".
*)
Theory forge_counterProg
Ancestors
  forge_counterSpec Word8ArrayProof cfMain
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib cfLib cfTacticsLib

val _ = translation_extends "Word8ArrayProg";

(* Translate pure counter logic from forge_counterSpec *)

val _ = translate le64_decode_def;
val _ = translate le64_byte_def;
val _ = translate cap_val_def;
val _ = translate counter_step_def;

(* ~30-line CakeML binary-frame counter loop *)

Quote add_cakeml:
  fun read_u64 a off =
    le64_decode
      (Word8Array.sub a off)
      (Word8Array.sub a (off + 1))
      (Word8Array.sub a (off + 2))
      (Word8Array.sub a (off + 3))
      (Word8Array.sub a (off + 4))
      (Word8Array.sub a (off + 5))
      (Word8Array.sub a (off + 6))
      (Word8Array.sub a (off + 7))

  fun write_u64 a off w =
    (Word8Array.update a off (le64_byte w 0);
     Word8Array.update a (off + 1) (le64_byte w 1);
     Word8Array.update a (off + 2) (le64_byte w 2);
     Word8Array.update a (off + 3) (le64_byte w 3);
     Word8Array.update a (off + 4) (le64_byte w 4);
     Word8Array.update a (off + 5) (le64_byte w 5);
     Word8Array.update a (off + 6) (le64_byte w 6);
     Word8Array.update a (off + 7) (le64_byte w 7))

  fun counter_loop buf seq spent =
    let
      val u = #(recv16) "" buf
      val st = Word8Array.sub buf 0
    in
      if st = Word8.fromInt 0 then
        let
          val req_seq = read_u64 buf 1
          val amount = read_u64 buf 9
          val res = counter_step seq spent req_seq amount
        in
          case res of
            (seq', (spent', (ok, out_seq))) =>
              let
                val u1 = write_u64 buf 1 ok
                val u2 = write_u64 buf 9 out_seq
                val u3 = #(send16) "" buf
                val wst = Word8Array.sub buf 0
              in
                if wst = Word8.fromInt 0 then
                  counter_loop buf seq' spent'
                else
                  ()
              end
        end
      else
        ()
    end

  fun counter_main u =
    let
      val buf = Word8Array.array 17 (Word8.fromInt 0)
    in
      counter_loop buf (Word64.fromInt 0) (Word64.fromInt 0)
    end
End

val st = get_ml_prog_state ();

(* Build whole program AST: declarations ++ [counter_main ()] *)

val Decls_raw =
  st
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def];

val prog_decs = Decls_raw |> concl |> rator |> rator |> rand;

val main_call_tm =
  ``Dlet NoLocs (Pcon NONE []) (App Opapp [Var (Short «counter_main»); Con NONE []])``;

val snoc_eq_thm =
  (PURE_REWRITE_CONV [listTheory.SNOC_APPEND] THENC
   PURE_REWRITE_CONV [GSYM listTheory.APPEND_ASSOC] THENC
   PURE_REWRITE_CONV [listTheory.APPEND]) ``SNOC ^main_call_tm ^prog_decs``;

Definition counter_prog_def[compute]:
  counter_prog = ^(rhs (concl snoc_eq_thm))
End

Theorem counter_prog_eq_snoc:
  counter_prog = SNOC ^main_call_tm ^prog_decs
Proof
  rewrite_tac [counter_prog_def, GSYM snoc_eq_thm]
QED

(* Heap predicate and event-termination predicate for the 2-FFI counter oracle *)

Definition event_is_err_def:
  (event_is_err (IO_event (ExtCall n) conf bs) ⇔ 17 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w) ∧
  (event_is_err _ ⇔ F)
End

Definition stop_after_err_def:
  (stop_after_err [] ⇔ T) ∧
  (stop_after_err (e::es) ⇔ if event_is_err e then es = [] else stop_after_err es)
End

Theorem stop_after_err_snoc:
  ∀es e. EVERY ($~ o event_is_err) es ⇒ stop_after_err (es ++ [e])
Proof
  Induct \\ simp [stop_after_err_def]
QED

Theorem stop_after_err_prefix_eq:
  ∀es1 es2.
    es1 ≼ es2 ∧ stop_after_err es2 ∧ (∃e. MEM e es1 ∧ event_is_err e) ⇒
    es2 = es1
Proof
  Induct \\ simp []
  \\ rpt strip_tac
  \\ Cases_on `es2` \\ fs [stop_after_err_def]
  \\ rveq
  \\ Cases_on `event_is_err h` \\ fs []
  \\ first_x_assum irule \\ simp [] \\ metis_tac []
QED

Definition COUNTER_IO_def:
  COUNTER_IO (io:counter_io) = IOx counter_ffi_part io
End

Definition COUNTER_IO_EV_def:
  COUNTER_IO_EV (io:counter_io) (evs:io_event list) =
    one (FFI_part (encode_counter_io io) (mk_ffi_next counter_ffi_part)
                  [«recv16»; «send16»] evs)
End

Theorem read_u64_spec:
  ∀av bs off offv.
    NUM off offv ∧ off + 8 ≤ LENGTH bs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "read_u64" st) [av; offv]
      (W8ARRAY av bs)
      (POSTv wv.
        &(WORD (le64_decode (EL off bs) (EL (off + 1) bs) (EL (off + 2) bs) (EL (off + 3) bs)
                            (EL (off + 4) bs) (EL (off + 5) bs) (EL (off + 6) bs) (EL (off + 7) bs)) wv) *
        W8ARRAY av bs)
Proof
  rpt strip_tac
  \\ xcf "read_u64" st
  \\ rpt (xlet_auto >- xsimpl)
  \\ xapp \\ xsimpl
  \\ qexists_tac `EL (off + 7) bs` \\ qexists_tac `EL (off + 6) bs`
  \\ qexists_tac `EL (off + 5) bs` \\ qexists_tac `EL (off + 4) bs`
  \\ qexists_tac `EL (off + 3) bs` \\ qexists_tac `EL (off + 2) bs`
  \\ qexists_tac `EL (off + 1) bs` \\ qexists_tac `EL off bs`
  \\ simp []
QED

Theorem write_u64_spec:
  ∀av bs off offv w wv.
    NUM off offv ∧ WORD w wv ∧ off + 8 ≤ LENGTH bs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "write_u64" st) [av; offv; wv]
      (W8ARRAY av bs)
      (POSTv uv.
        &(UNIT_TYPE () uv) *
        W8ARRAY av (TAKE off bs ++ le64_encode w ++ DROP (off + 8) bs))
Proof
  rpt strip_tac
  \\ xcf "write_u64" st
  \\ rpt (xlet_auto >- xsimpl)
  \\ xapp \\ xsimpl
  \\ qexists_tac `le64_byte w 7` \\ qexists_tac `off + 7` \\ simp []
  \\ rw [le64_encode_def]
  \\ `∀i. i < LENGTH (LUPDATE (le64_byte w 7) (off + 7)
                       (LUPDATE (le64_byte w 6) (off + 6)
                        (LUPDATE (le64_byte w 5) (off + 5)
                         (LUPDATE (le64_byte w 4) (off + 4)
                          (LUPDATE (le64_byte w 3) (off + 3)
                           (LUPDATE (le64_byte w 2) (off + 2)
                            (LUPDATE (le64_byte w 1) (off + 1)
                             (LUPDATE (le64_byte w 0) off bs)))))))) ⇒
       EL i (LUPDATE (le64_byte w 7) (off + 7)
              (LUPDATE (le64_byte w 6) (off + 6)
               (LUPDATE (le64_byte w 5) (off + 5)
                (LUPDATE (le64_byte w 4) (off + 4)
                 (LUPDATE (le64_byte w 3) (off + 3)
                  (LUPDATE (le64_byte w 2) (off + 2)
                   (LUPDATE (le64_byte w 1) (off + 1)
                    (LUPDATE (le64_byte w 0) off bs)))))))) =
       EL i (TAKE off bs ++
             [le64_byte w 0; le64_byte w 1; le64_byte w 2; le64_byte w 3;
              le64_byte w 4; le64_byte w 5; le64_byte w 6; le64_byte w 7] ++
             DROP (off + 8) bs)` by
    (rpt strip_tac \\ fs [LENGTH_LUPDATE]
     \\ Cases_on `i < off`
     >- simp [EL_LUPDATE, EL_APPEND1, EL_TAKE]
     \\ Cases_on `i < off + 8`
     >- (`i = off ∨ i = off + 1 ∨ i = off + 2 ∨ i = off + 3 ∨
          i = off + 4 ∨ i = off + 5 ∨ i = off + 6 ∨ i = off + 7` by decide_tac
         \\ rveq \\ simp [EL_LUPDATE, EL_APPEND1, EL_APPEND2, LENGTH_TAKE])
     \\ simp [EL_LUPDATE, EL_APPEND2, LENGTH_TAKE, EL_DROP])
  \\ irule LIST_EQ \\ simp [LENGTH_LUPDATE, LENGTH_TAKE, LENGTH_DROP]
QED

Definition limit_frames_def:
  (limit_frames NONE xs = xs) ∧
  (limit_frames (SOME n) xs = TAKE (SUC n) xs)
End

Theorem counter_loop_spec:
  ∀inps outs wlim evs bufv bs seq seqv spent spentv.
    LENGTH bs = 17 ∧ WORD seq seqv ∧ WORD spent spentv ∧
    EVERY ($~ o event_is_err) evs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "counter_loop" st) [bufv; seqv; spentv]
      (W8ARRAY bufv bs * COUNTER_IO_EV <| inputs := inps; outputs := outs; write_limit := wlim |> evs)
      (POSTv uv.
        &(UNIT_TYPE () uv) *
        (SEP_EXISTS bs'. SEP_EXISTS rest_inps. SEP_EXISTS wlim'. SEP_EXISTS evs'.
          W8ARRAY bufv bs' * &(LENGTH bs' = 17 ∧ stop_after_err evs') *
          COUNTER_IO_EV <| inputs := rest_inps;
                           outputs := outs ++ limit_frames wlim (SND (SND (counter_run seq spent inps)));
                           write_limit := wlim' |> evs'))
Proof
  Induct_on `inps`
  >- (
    rpt strip_tac
    \\ xcf "counter_loop" st
    \\ xlet `POSTv uv.
         W8ARRAY bufv (1w :: DROP 1 bs) *
         COUNTER_IO_EV <| inputs := []; outputs := outs; write_limit := wlim |>
           (evs ++ [IO_event (ExtCall «recv16») [] (ZIP (bs, 1w :: DROP 1 bs))])`
    >- (
      simp [COUNTER_IO_EV_def]
      \\ xffi
      \\ simp [counter_ffi_part_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`bs`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_counter_io,
               ffi_recv16_def, counter_ffi_part_def]
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xcon \\ xsimpl
    \\ qexists_tac `[]` \\ qexists_tac `wlim`
    \\ qexists_tac `evs ++ [IO_event (ExtCall «recv16») [] (ZIP (bs, 1w :: DROP 1 bs))]`
    \\ simp [stop_after_err_snoc]
    \\ Cases_on `wlim` \\ simp [counter_run_def, limit_frames_def] \\ xsimpl)
  \\ rpt strip_tac
  \\ xcf "counter_loop" st
  \\ Cases_on `LENGTH h = 16`
  >- (
    qabbrev_tac `ev_r = IO_event (ExtCall «recv16») [] (ZIP (bs, 0w :: h))`
    \\ `¬event_is_err ev_r` by
         (simp [Abbr `ev_r`, event_is_err_def]
          \\ Cases_on `bs` \\ fs [listTheory.ZIP])
    \\ xlet `POSTv uv.
         W8ARRAY bufv (0w :: h) *
         COUNTER_IO_EV <| inputs := inps; outputs := outs; write_limit := wlim |>
           (evs ++ [ev_r])`
    >- (
      simp [COUNTER_IO_EV_def, Abbr `ev_r`]
      \\ xffi
      \\ simp [counter_ffi_part_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`bs`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_counter_io,
               ffi_recv16_def, counter_ffi_part_def, DROP_LENGTH_TOO_LONG]
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xlet_auto_spec (SOME read_u64_spec) >- (xsimpl \\ simp [])
    \\ xlet_auto_spec (SOME read_u64_spec) >- (xsimpl \\ simp [])
    \\ xlet_auto >- xsimpl
    \\ qmatch_asmsub_abbrev_tac `counter_step seq spent req_seq amount`
    \\ `req_seq = FST (frame16_decode h) ∧ amount = SND (frame16_decode h)` by
         (unabbrev_all_tac \\ simp [frame16_decode_def, listTheory.EL])
    \\ Cases_on `counter_step seq spent req_seq amount`
    \\ rename1 `counter_step _ _ _ _ = (seq', rest1)`
    \\ Cases_on `rest1`
    \\ rename1 `counter_step _ _ _ _ = (seq', spent', rest2)`
    \\ Cases_on `rest2`
    \\ rename1 `counter_step _ _ _ _ = (seq', spent', ok, out_seq)`
    \\ qpat_x_assum `PAIR_TYPE _ _ _ _` mp_tac
    \\ simp [ml_translatorTheory.PAIR_TYPE_def]
    \\ rpt strip_tac \\ rveq
    \\ xmatch
    \\ xlet_auto_spec (SOME write_u64_spec) >- (xsimpl \\ simp [])
    \\ xlet_auto_spec (SOME write_u64_spec) >- (xsimpl \\ simp [le64_encode_length])
    \\ qmatch_goalsub_abbrev_tac `W8ARRAY bufv out_buf`
    \\ `out_buf = 0w :: frame16_encode ok out_seq` by
         (unabbrev_all_tac
          \\ simp [frame16_encode_def, le64_encode_length, TAKE_APPEND1, DROP_APPEND2,
                   TAKE_LENGTH_ID_rwt, DROP_LENGTH_TOO_LONG])
    \\ `LENGTH out_buf = 17` by simp [frame16_encode_length]
    \\ Cases_on `wlim`
    >- (
      qabbrev_tac `ev_s = IO_event (ExtCall «send16») [] (ZIP (out_buf, out_buf))`
      \\ `¬event_is_err ev_s` by
           (simp [Abbr `ev_s`, event_is_err_def]
            \\ qpat_x_assum `out_buf = 0w :: _` SUBST1_TAC
            \\ simp [listTheory.ZIP])
      \\ xlet `POSTv uv.
           W8ARRAY bufv out_buf *
           COUNTER_IO_EV <| inputs := inps;
                            outputs := outs ++ [frame16_encode ok out_seq];
                            write_limit := NONE |>
             (evs ++ [ev_r] ++ [ev_s])`
      >- (
        simp [COUNTER_IO_EV_def, Abbr `ev_s`]
        \\ xffi
        \\ simp [counter_ffi_part_def]
        \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
        \\ map_every qexists_tac [`out_buf`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs ++ [ev_r]`]
        \\ unabbrev_all_tac
        \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_counter_io,
                 ffi_send16_def, counter_ffi_part_def,
                 frame16_encode_length, TAKE_LENGTH_ID_rwt]
        \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
      \\ xif \\ asm_exists_tac \\ fs []
      \\ xapp \\ xsimpl
      \\ map_every qexists_tac [`emp`, `NONE`, `spent'`, `seq'`,
                                `outs ++ [frame16_encode ok out_seq]`, `evs ++ [ev_r] ++ [ev_s]`]
      \\ simp [frame16_encode_length]
      \\ xsimpl
      \\ rpt strip_tac
      \\ qpat_x_assum `LENGTH x = 17`
           (strip_assume_tac o SIMP_RULE (srw_ss()) [listTheory.LENGTH_EQ_NUM_compute])
      \\ rveq
      \\ qexists_tac `x'` \\ qexists_tac `x''` \\ qexists_tac `x'''`
      \\ Cases_on `frame16_decode h` \\ fs []
      \\ Cases_on `counter_run seq' spent' inps` \\ rename1 `_ = (s1, s2)`
      \\ Cases_on `s2` \\ simp [counter_run_def, limit_frames_def]
      \\ `outs ++ [frame16_encode ok out_seq] ++ r' = outs ++ frame16_encode ok out_seq :: r'` by
           metis_tac [listTheory.APPEND_ASSOC, listTheory.APPEND]
      \\ pop_assum SUBST1_TAC \\ xsimpl)
    \\ Cases_on `x`
    >- (
      qabbrev_tac `ev_s = IO_event (ExtCall «send16») [] (ZIP (out_buf, 1w :: frame16_encode ok out_seq))`
      \\ xlet `POSTv uv.
           W8ARRAY bufv (1w :: frame16_encode ok out_seq) *
           COUNTER_IO_EV <| inputs := inps;
                            outputs := outs ++ [frame16_encode ok out_seq];
                            write_limit := SOME 0 |>
             (evs ++ [ev_r] ++ [ev_s])`
      >- (
        simp [COUNTER_IO_EV_def, Abbr `ev_s`]
        \\ xffi
        \\ simp [counter_ffi_part_def]
        \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
        \\ map_every qexists_tac [`out_buf`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs ++ [ev_r]`]
        \\ unabbrev_all_tac
        \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_counter_io,
                 ffi_send16_def, counter_ffi_part_def,
                 frame16_encode_length, TAKE_LENGTH_ID_rwt]
        \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
      \\ xif \\ asm_exists_tac \\ fs []
      \\ xcon \\ xsimpl
      \\ qexists_tac `inps` \\ qexists_tac `SOME 0` \\ qexists_tac `evs ++ [ev_r] ++ [ev_s]`
      \\ `stop_after_err (evs ++ [ev_r] ++ [ev_s])` by
           (`evs ++ [ev_r] ++ [ev_s] = (evs ++ [ev_r]) ++ [ev_s]` by simp []
            \\ pop_assum SUBST1_TAC \\ irule stop_after_err_snoc \\ simp [])
      \\ simp []
      \\ Cases_on `frame16_decode h` \\ fs []
      \\ Cases_on `counter_run seq' spent' inps` \\ rename1 `_ = (s1, s2)`
      \\ Cases_on `s2` \\ simp [counter_run_def, limit_frames_def]
      \\ xsimpl
      \\ `LENGTH (frame16_encode ok out_seq) = 16` by simp [frame16_encode_length]
      \\ fs [listTheory.LENGTH_EQ_NUM_compute])
    \\ qabbrev_tac `ev_s = IO_event (ExtCall «send16») [] (ZIP (out_buf, out_buf))`
    \\ `¬event_is_err ev_s` by
         (simp [Abbr `ev_s`, event_is_err_def]
          \\ qpat_x_assum `out_buf = 0w :: _` SUBST1_TAC
          \\ simp [listTheory.ZIP])
    \\ xlet `POSTv uv.
         W8ARRAY bufv out_buf *
         COUNTER_IO_EV <| inputs := inps;
                          outputs := outs ++ [frame16_encode ok out_seq];
                          write_limit := SOME n |>
           (evs ++ [ev_r] ++ [ev_s])`
    >- (
      simp [COUNTER_IO_EV_def, Abbr `ev_s`]
      \\ xffi
      \\ simp [counter_ffi_part_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`out_buf`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs ++ [ev_r]`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_counter_io,
               ffi_send16_def, counter_ffi_part_def,
               frame16_encode_length, TAKE_LENGTH_ID_rwt]
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xapp \\ xsimpl
    \\ map_every qexists_tac [`emp`, `SOME n`, `spent'`, `seq'`,
                              `outs ++ [frame16_encode ok out_seq]`, `evs ++ [ev_r] ++ [ev_s]`]
    \\ simp [frame16_encode_length]
    \\ xsimpl
    \\ rpt strip_tac
    \\ qpat_x_assum `LENGTH x = 17`
         (strip_assume_tac o SIMP_RULE (srw_ss()) [listTheory.LENGTH_EQ_NUM_compute])
    \\ rveq
    \\ qexists_tac `x'` \\ qexists_tac `x''` \\ qexists_tac `x'''`
    \\ Cases_on `frame16_decode h` \\ fs []
    \\ Cases_on `counter_run seq' spent' inps` \\ rename1 `_ = (s1, s2)`
    \\ Cases_on `s2` \\ simp [counter_run_def, limit_frames_def]
    \\ `outs ++ [frame16_encode ok out_seq] ++ TAKE (SUC n) r' =
        outs ++ frame16_encode ok out_seq :: TAKE (SUC n) r'` by
         metis_tac [listTheory.APPEND_ASSOC, listTheory.APPEND]
    \\ pop_assum SUBST1_TAC \\ xsimpl)
  \\ xlet `POSTv uv.
       W8ARRAY bufv (1w :: DROP 1 bs) *
       COUNTER_IO_EV <| inputs := h::inps; outputs := outs; write_limit := wlim |>
         (evs ++ [IO_event (ExtCall «recv16») [] (ZIP (bs, 1w :: DROP 1 bs))])`
  >- (
    simp [COUNTER_IO_EV_def]
    \\ xffi
    \\ simp [counter_ffi_part_def]
    \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
    \\ map_every qexists_tac [`bs`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
    \\ unabbrev_all_tac
    \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_counter_io,
             ffi_recv16_def, counter_ffi_part_def]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif \\ asm_exists_tac \\ fs []
  \\ xcon \\ xsimpl
  \\ qexists_tac `h::inps` \\ qexists_tac `wlim`
  \\ qexists_tac `evs ++ [IO_event (ExtCall «recv16») [] (ZIP (bs, 1w :: DROP 1 bs))]`
  \\ simp [stop_after_err_snoc]
  \\ Cases_on `wlim` \\ simp [counter_run_def, limit_frames_def] \\ xsimpl
QED

Theorem counter_main_spec:
  ∀inps wlim uv.
    UNIT_TYPE () uv ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "counter_main" st) [uv]
      (COUNTER_IO_EV <| inputs := inps; outputs := []; write_limit := wlim |> [])
      (POSTv rv.
        &(UNIT_TYPE () rv) *
        (SEP_EXISTS rest_inps. SEP_EXISTS wlim'. SEP_EXISTS evs'.
          &(stop_after_err evs') *
          COUNTER_IO_EV <| inputs := rest_inps;
                           outputs := limit_frames wlim (SND (SND (counter_run 0w 0w inps)));
                           write_limit := wlim' |> evs'))
Proof
  rpt strip_tac
  \\ xcf "counter_main" st
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp_spec counter_loop_spec \\ xsimpl
  \\ map_every qexists_tac [`emp`, `wlim`, `0w`, `0w`, `[]`, `inps`, `[]`]
  \\ xsimpl \\ rpt strip_tac \\ qexists_tac `x'` \\ qexists_tac `x''` \\ qexists_tac `x'''` \\ xsimpl
QED

(* Whole-program CakeML source semantics theorem *)

Theorem counter_parts_ok:
  ∀io. cfStore$parts_ok (counter_ffi io) counter_proj
Proof
  gen_tac
  \\ simp [cfStoreTheory.parts_ok_def, counter_proj_def, counter_ffi_def,
           ffiTheory.initial_ffi_state_def, counter_ffi_part_def]
  \\ rpt conj_tac
  >- (qexists_tac `encode_counter_io io` \\ rw [FUPDATE_LIST_THM, FLOOKUP_UPDATE])
  >- (rpt strip_tac \\ gvs [FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM, cfHeapsBaseTheory.mk_ffi_next_def,
                            decode_encode_counter_io, AllCaseEqs(), ffi_recv16_def, ffi_send16_def])
  >- (
    rpt gen_tac \\ strip_tac
    \\ gvs [FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM, cfHeapsBaseTheory.mk_ffi_next_def,
            decode_encode_counter_io, AllCaseEqs()]
    \\ (conj_tac >- (imp_res_tac ffi_recv16_length \\ imp_res_tac ffi_send16_length \\ simp [])
        \\ qexists_tac `s`
        \\ simp [counter_ffi_oracle_def, FUPDATE_LIST_THM, fmap_eq_flookup, FLOOKUP_UPDATE] \\ rw []))
QED

Theorem counter_io_split:
  ∀st2 io.
    st2.ffi = counter_ffi io ⇒
    ∃h1 h2. SPLIT (st2heap counter_proj st2) (h1, h2) ∧ COUNTER_IO_EV io [] h1
Proof
  rpt strip_tac
  \\ qabbrev_tac `ffip = FFI_part (encode_counter_io io) (mk_ffi_next counter_ffi_part)
                                  [«recv16»; «send16»] []`
  \\ qexists_tac `{ffip}`
  \\ qexists_tac `st2heap counter_proj st2 DIFF {ffip}`
  \\ conj_tac
  >- (
    `ffip ∈ st2heap counter_proj st2` by
      (simp [cfStoreTheory.st2heap_def] \\ disj2_tac
       \\ simp [counter_proj_def, cfStoreTheory.ffi2heap_def]
       \\ simp [GSYM counter_proj_def, counter_parts_ok]
       \\ rw [Abbr `ffip`, counter_proj_def, counter_ffi_def, ffiTheory.initial_ffi_state_def,
              FUPDATE_LIST_THM, FLOOKUP_UPDATE])
    \\ fs [set_sepTheory.SPLIT_def, IN_DISJOINT, EXTENSION] \\ metis_tac [])
  \\ simp [COUNTER_IO_EV_def, set_sepTheory.one_def, Abbr `ffip`]
QED

Theorem counter_io_ffi_part_hprop:
  ∀out.
    FFI_part_hprop
      (SEP_EXISTS rest_inps. SEP_EXISTS wlim'. SEP_EXISTS evs'.
        &(stop_after_err evs') *
        COUNTER_IO_EV <| inputs := rest_inps; outputs := out; write_limit := wlim' |> evs')
Proof
  gen_tac
  \\ ho_match_mp_tac cfMainTheory.FFI_part_hprop_SEP_EXISTS \\ gen_tac
  \\ ho_match_mp_tac cfMainTheory.FFI_part_hprop_SEP_EXISTS \\ gen_tac
  \\ ho_match_mp_tac cfMainTheory.FFI_part_hprop_SEP_EXISTS \\ gen_tac
  \\ simp [cfMainTheory.FFI_part_hprop_def, COUNTER_IO_EV_def, set_sepTheory.one_def,
           set_sepTheory.STAR_def, set_sepTheory.cond_def,
           set_sepTheory.SPLIT_def, set_sepTheory.emp_def]
  \\ rpt strip_tac \\ rveq \\ simp [] \\ metis_tac []
QED

local
  val lem_vs = Decls_raw |> concl |> free_vars
  val ffi_var = lem_vs |> filter (fn v => fst (dest_var v) = "ffi") |> hd
  val po_var  = lem_vs |> filter (fn v => fst (dest_var v) = "po") |> hd
  val eq_init_st = Q.prove (
    `init_state (counter_ffi io) with ptr_eq_oracle := K (K F) = init_state (counter_ffi io)`,
    simp [ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality])
  val decls_inst =
    Decls_raw
    |> GEN ffi_var |> ISPEC ``counter_ffi (io:counter_io)``
    |> GEN po_var  |> ISPEC ``(K (K F) : num -> num -> bool)``
    |> CONV_RULE (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV eq_init_st)))))
  val res_env = decls_inst |> concl |> rator |> rand
  val res_st  = decls_inst |> concl |> rand
  val lookup_tm = ``nsLookup (^res_env).v (Short «counter_main»)``
  val lookup_thm =
    prove (mk_eq (lookup_tm, optionSyntax.mk_some (fetch_v "counter_main" st)),
           REWRITE_TAC [ml_progLib.nsLookup_conv lookup_tm])
  val ffi_eq_thm =
    prove (``(^res_st).ffi = counter_ffi io``, EVAL_TAC)
in
  val counter_Decls_thm = decls_inst
  val counter_lookup_thm = lookup_thm
  val counter_ffi_eq_thm = ffi_eq_thm
end;

val call_main_gen =
  Q.GENL [`env1`, `st1`, `prog`, `env2`, `st2`, `fname`, `fv`, `proj1`, `proj2`, `P`, `Q`, `h1`, `h2`]
    cfMainTheory.call_main_thm2;

Theorem counter_semantics:
  ∀io.
    io.outputs = [] ⇒
    semanticsProps$sem_satisfies
      (semantics_dec_list (init_state (counter_ffi io)) init_env counter_prog)
      (λb. ∃io_events.
             b = Terminate Success io_events ∧
             stop_after_err io_events ∧
             sent_frames_of io_events =
               limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs))))
Proof
  rpt strip_tac
  \\ qabbrev_tac `inps = io.inputs`
  \\ qabbrev_tac `wlim = io.write_limit`
  \\ `io = <| inputs := inps; outputs := []; write_limit := wlim |>` by
       simp [counter_io_component_equality, Abbr `inps`, Abbr `wlim`]
  \\ pop_assum SUBST_ALL_TAC \\ simp []
  \\ rewrite_tac [counter_prog_eq_snoc]
  \\ qspecl_then [`inps`, `wlim`, `Conv NONE []`] mp_tac
       (INST_TYPE [mk_vartype "'ffi" |-> ``:counter_io``] counter_main_spec
        |> Q.GEN `p` |> Q.SPEC `counter_proj`)
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac
  \\ qspec_then `<| inputs := inps; outputs := []; write_limit := wlim |>` assume_tac
       (GEN ``io:counter_io`` counter_Decls_thm)
  \\ qspec_then `<| inputs := inps; outputs := []; write_limit := wlim |>` assume_tac
       (GEN ``io:counter_io`` counter_ffi_eq_thm)
  \\ drule counter_io_split \\ strip_tac
  \\ qpat_x_assum `Decls _ _ _ _ _` (mp_tac o MATCH_MP call_main_gen)
  \\ disch_then (qspecl_then [`«counter_main»`, `^(fetch_v "counter_main" st)`,
                              `FST counter_proj`, `SND counter_proj`,
                              `COUNTER_IO_EV <| inputs := inps; outputs := []; write_limit := wlim |> []`,
                              `SEP_EXISTS rest_inps. SEP_EXISTS wlim'. SEP_EXISTS evs'.
                                 &(stop_after_err evs') *
                                 COUNTER_IO_EV <| inputs := rest_inps;
                                                  outputs := limit_frames wlim (SND (SND (counter_run 0w 0w inps)));
                                                  write_limit := wlim' |> evs'`,
                              `h1`, `h2`] mp_tac)
  \\ simp [ml_progTheory.lookup_var_def, counter_lookup_thm, counter_io_ffi_part_hprop]
  \\ simp [semanticsPropsTheory.sem_satisfies_def]
  \\ rpt strip_tac
  \\ qpat_x_assum `∀behavior. _ ⇒ _` (qspec_then `b` mp_tac)
  \\ impl_tac >- first_assum ACCEPT_TAC
  \\ strip_tac
  \\ rveq \\ qexists_tac `st3.ffi.io_events` \\ simp []
  \\ qpat_x_assum `$SEP_EXISTS _ _` mp_tac
  \\ simp [set_sepTheory.SEP_EXISTS_THM, COUNTER_IO_EV_def, set_sepTheory.one_def,
           set_sepTheory.STAR_def, set_sepTheory.cond_def,
           set_sepTheory.SPLIT_def, set_sepTheory.emp_def]
  \\ strip_tac \\ rveq
  \\ qmatch_asmsub_abbrev_tac `SPLIT3 _ ({ffip}, _, _)`
  \\ `ffip ∈ st2heap counter_proj st3` by
       (qpat_x_assum `SPLIT3 _ _` mp_tac \\ simp [cfHeapsBaseTheory.SPLIT3_def, EXTENSION] \\ metis_tac [])
  \\ qpat_x_assum `ffip ∈ st2heap _ _` mp_tac
  \\ simp [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           counter_proj_def, cfStoreTheory.ffi2heap_def, Abbr `ffip`]
  \\ simp [GSYM counter_proj_def]
  \\ Cases_on `cfStore$parts_ok st3.ffi counter_proj` \\ simp []
  \\ strip_tac
  \\ conj_tac
  >- (
    `FILTER (cfStore$ffi_has_index_in [«recv16»; «send16»]) st3.ffi.io_events = st3.ffi.io_events` by
      (qpat_x_assum `cfStore$parts_ok _ _` mp_tac
       \\ simp [listTheory.FILTER_EQ_ID, cfStoreTheory.parts_ok_def, counter_proj_def])
    \\ fs [])
  \\ qpat_x_assum `∀n. _ ⇒ _` (qspec_then `«recv16»` mp_tac)
  \\ simp [FUPDATE_LIST_THM, FLOOKUP_UPDATE, encode_counter_io_11]
  \\ strip_tac
  \\ qpat_x_assum `call_FFI_rel꙳ _ _` mp_tac
  \\ simp [ml_progTheory.init_state_def]
  \\ strip_tac
  \\ qspecl_then [`<| inputs := inps; outputs := []; write_limit := wlim |>`, `st3.ffi`] mp_tac
       counter_ffi_outputs_eq_sent_frames
  \\ simp []
QED
