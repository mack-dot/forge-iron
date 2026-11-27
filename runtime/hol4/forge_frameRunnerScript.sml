(*
  Forge Reusable Runtime: Generic 64-Byte CakeML Frame-Runner Wrapper (Zero-Basis).

  Extends Word8ArrayProg ONLY and proves ONE polymorphic higher-order runner:
      run_frame64_kernel : ('st -> frame64 -> 'st # frame64) -> 'st -> unit

  Future kernels (M2 guardrail, M3 escrow/crypto, etc.) simply call:
      val _ = translation_extends "forge_frameRunner";
      val _ = translate my_init_def;
      val _ = translate my_step_def;
  and invoke `run_frame64_kernel my_step my_init` to inherit the entire verified
  65-byte W8ARRAY loop, recv64/send64 FFI Separation Logic proof, and whole-program
  semantics theorem with ZERO manual Separation Logic or assembly proofs.
*)
Theory forge_frameRunner
Ancestors
  forge_frame64Spec Word8ArrayProof cfMain
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib cfLib cfTacticsLib

val _ = translation_extends "Word8ArrayProg";

val _ = translate le64_decode_def;
val _ = translate le64_byte_def;
val _ = register_type ``:frame64``;

val FRAME64_TYPE_tm = ml_translatorLib.get_type_inv ``:frame64``;

(* Generic 64-byte frame loop (single 65-byte Word8Array allocated once outside loop) *)

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

  fun read_frame64 a =
    Frame64
      (read_u64 a 1)  (read_u64 a 9)  (read_u64 a 17) (read_u64 a 25)
      (read_u64 a 33) (read_u64 a 41) (read_u64 a 49) (read_u64 a 57)

  fun write_frame64 a fr =
    case fr of
      Frame64 w0 w1 w2 w3 w4 w5 w6 w7 =>
        (write_u64 a 1 w0;  write_u64 a 9 w1;  write_u64 a 17 w2; write_u64 a 25 w3;
         write_u64 a 33 w4; write_u64 a 41 w5; write_u64 a 49 w6; write_u64 a 57 w7)

  fun frame64_loop step buf state =
    let
      val u = #(recv64) "" buf
      val st = Word8Array.sub buf 0
    in
      if st = Word8.fromInt 0 then
        let
          val req = read_frame64 buf
          val step_st = step state
          val res = step_st req
        in
          case res of
            (state', resp) =>
              let
                val u1 = write_frame64 buf resp
                val u2 = #(send64) "" buf
                val wst = Word8Array.sub buf 0
              in
                if wst = Word8.fromInt 0 then
                  frame64_loop step buf state'
                else
                  ()
              end
        end
      else
        ()
    end

  fun run_frame64_kernel step init_state =
    let
      val buf = Word8Array.array 65 (Word8.fromInt 0)
    in
      frame64_loop step buf init_state
    end
End

val st = get_ml_prog_state ();

(* Event termination & FFI heap predicates *)

Definition event_is_err64_def:
  (event_is_err64 (IO_event (ExtCall n) conf bs) ⇔ 65 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w) ∧
  (event_is_err64 _ ⇔ F)
End

Definition stop_after_err64_def:
  (stop_after_err64 [] ⇔ T) ∧
  (stop_after_err64 (e::es) ⇔ if event_is_err64 e then es = [] else stop_after_err64 es)
End

Theorem stop_after_err64_snoc:
  ∀es e. EVERY ($~ o event_is_err64) es ⇒ stop_after_err64 (es ++ [e])
Proof
  Induct \\ simp [stop_after_err64_def]
QED

Definition FRAME64_IO_EV_def:
  FRAME64_IO_EV (io:frame64_io) (evs:io_event list) =
    one (FFI_part (encode_frame64_io io) (mk_ffi_next frame64_ffi_part)
                  [«recv64»; «send64»] evs)
End

Theorem read_u64_spec:
  ∀av bs off offv.
    NUM off offv ∧ off + 8 ≤ LENGTH bs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "read_u64" st) [av; offv]
      (W8ARRAY av bs)
      (POSTv wv. &(WORD (le64_at bs off) wv) * W8ARRAY av bs)
Proof
  rpt strip_tac
  \\ xcf "read_u64" st
  \\ rpt (xlet_auto >- xsimpl)
  \\ xapp \\ xsimpl \\ simp [le64_at_def]
  \\ map_every qexists_tac
       [`EL (off + 7) bs`, `EL (off + 6) bs`, `EL (off + 5) bs`, `EL (off + 4) bs`,
        `EL (off + 3) bs`, `EL (off + 2) bs`, `EL (off + 1) bs`, `EL off bs`]
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
  \\ irule LIST_EQ \\ simp [LENGTH_LUPDATE, LENGTH_TAKE, LENGTH_DROP]
  \\ rpt strip_tac
  \\ Cases_on `x < off` >- simp [EL_LUPDATE, EL_APPEND1, EL_TAKE]
  \\ Cases_on `x < off + 8`
  >- (`x = off ∨ x = off + 1 ∨ x = off + 2 ∨ x = off + 3 ∨
       x = off + 4 ∨ x = off + 5 ∨ x = off + 6 ∨ x = off + 7` by decide_tac
      \\ rveq \\ simp [EL_LUPDATE, EL_APPEND1, EL_APPEND2, LENGTH_TAKE])
  \\ simp [EL_LUPDATE, EL_APPEND2, LENGTH_TAKE, EL_DROP]
QED

Theorem read_frame64_spec:
  ∀av b0 h.
    LENGTH h = 64 ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "read_frame64" st) [av]
      (W8ARRAY av (b0 :: h))
      (POSTv frv. &(^(FRAME64_TYPE_tm) (frame64_decode h) frv) * W8ARRAY av (b0 :: h))
Proof
  rpt strip_tac
  \\ xcf "read_frame64" st
  \\ rpt (xlet_auto_spec (SOME read_u64_spec) >- (xsimpl \\ simp []))
  \\ xcon \\ xsimpl
  \\ fs [frame64_decode_def, le64_at_def, fetch "-" "FORGE_FRAME64SPEC_FRAME64_TYPE_def"]
QED

Theorem write_frame64_spec:
  ∀av bs fr frv.
    LENGTH bs = 65 ∧ ^(FRAME64_TYPE_tm) fr frv ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "write_frame64" st) [av; frv]
      (W8ARRAY av bs)
      (POSTv uv.
        &(UNIT_TYPE () uv) *
        W8ARRAY av (HD bs :: frame64_encode fr))
Proof
  rpt strip_tac
  \\ Cases_on `fr` \\ rename1 `Frame64 w0 w1 w2 w3 w4 w5 w6 w7`
  \\ Cases_on `bs` \\ rename1 `W8ARRAY av (b0 :: rest)`
  \\ fs [fetch "-" "FORGE_FRAME64SPEC_FRAME64_TYPE_def"] \\ rveq
  \\ xcf "write_frame64" st
  \\ xmatch
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ DROP 8 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w0` \\ simp [])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ DROP 16 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w1`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) *
             W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ DROP 24 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w2`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) *
             W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++
                         le64_encode w3 ++ DROP 32 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w3`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) *
             W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++
                         le64_encode w3 ++ le64_encode w4 ++ DROP 40 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w4`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) *
             W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++
                         le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ DROP 48 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w5`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) *
             W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++
                         le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++
                         le64_encode w6 ++ DROP 56 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w6`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w7`
  \\ simp [frame64_encode_def, le64_encode_length, TAKE_APPEND, DROP_APPEND,
           TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T]
QED

Theorem Arrow_app_1_frame[local]:
  ∀p a b f fv x xv H.
    (a --> b) f fv ∧ a x xv ⇒
    app p fv [xv] H (POSTv rv. &b (f x) rv * H)
Proof
  rpt strip_tac
  \\ `app p fv [xv] emp (POSTv rv. &b (f x) rv)` by
       (simp [cfAppTheory.app_def] \\ metis_tac [cfAppTheory.Arrow_IMP_app_basic])
  \\ drule cfAppTheory.app_wgframe
  \\ disch_then (qspecl_then [`H`, `H`, `POSTv rv. &b (f x) rv * H`] mp_tac)
  \\ impl_tac >- (conj_tac >- xsimpl
                  \\ simp [cfHeapsBaseTheory.SEP_IMPPOST_def, cfHeapsBaseTheory.STARPOST_def,
                           cfHeapsBaseTheory.POSTv_def] \\ Cases \\ simp [] \\ xsimpl)
  \\ simp []
QED

Theorem frame64_loop_spec:
  ∀(ST:'st -> v -> bool) step stepv inps outs wlim evs bufv bs state statev.
    (ST --> ^(FRAME64_TYPE_tm) --> PAIR_TYPE ST ^(FRAME64_TYPE_tm)) step stepv ∧
    ST state statev ∧ LENGTH bs = 65 ∧ EVERY ($~ o event_is_err64) evs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "frame64_loop" st) [stepv; bufv; statev]
      (W8ARRAY bufv bs * FRAME64_IO_EV <| inputs := inps; outputs := outs; write_limit := wlim |> evs)
      (POSTv uv.
        &(UNIT_TYPE () uv) *
        (SEP_EXISTS bs' rest_inps wlim' evs'.
          W8ARRAY bufv bs' * &(stop_after_err64 evs') *
          FRAME64_IO_EV <| inputs := rest_inps;
                           outputs := outs ++ limit_frames64 wlim (SND (frame64_run step state inps));
                           write_limit := wlim' |> evs'))
Proof
  ntac 3 gen_tac
  \\ Induct_on `inps`
  >- (
    rpt strip_tac
    \\ xcf "frame64_loop" st
    \\ xlet `POSTv uv.
         W8ARRAY bufv (1w :: DROP 1 bs) *
         FRAME64_IO_EV <| inputs := []; outputs := outs; write_limit := wlim |>
           (evs ++ [IO_event (ExtCall «recv64») [] (ZIP (bs, 1w :: DROP 1 bs))])`
    >- (
      simp [FRAME64_IO_EV_def] \\ xffi \\ simp [frame64_ffi_part_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`bs`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_frame64_io,
               ffi_recv64_def, frame64_ffi_part_def] \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xcon \\ xsimpl
    \\ map_every qexists_tac [`[]`, `wlim`, `evs ++ [IO_event (ExtCall «recv64») [] (ZIP (bs, 1w :: DROP 1 bs))]`]
    \\ simp [stop_after_err64_snoc]
    \\ Cases_on `wlim` \\ simp [frame64_run_def, limit_frames64_def] \\ xsimpl)
  \\ rpt strip_tac
  \\ rename1 `ST cur_st statev`
  \\ xcf "frame64_loop" st
  \\ Cases_on `LENGTH h = 64`
  >- (
    qabbrev_tac `ev_r = IO_event (ExtCall «recv64») [] (ZIP (bs, 0w :: h))`
    \\ `¬event_is_err64 ev_r` by
         (simp [Abbr `ev_r`, event_is_err64_def] \\ Cases_on `bs` \\ fs [listTheory.ZIP])
    \\ xlet `POSTv uv.
         W8ARRAY bufv (0w :: h) *
         FRAME64_IO_EV <| inputs := inps; outputs := outs; write_limit := wlim |>
           (evs ++ [ev_r])`
    >- (
      simp [FRAME64_IO_EV_def, Abbr `ev_r`] \\ xffi \\ simp [frame64_ffi_part_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`bs`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_frame64_io,
               ffi_recv64_def, frame64_ffi_part_def, DROP_LENGTH_TOO_LONG] \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xlet_auto_spec (SOME read_frame64_spec) >- (xsimpl \\ simp [])
    \\ xlet `POSTv sfv. &((^(FRAME64_TYPE_tm) --> PAIR_TYPE ST ^(FRAME64_TYPE_tm)) (step cur_st) sfv) *
                          (W8ARRAY bufv (0w :: h) *
                           FRAME64_IO_EV <| inputs := inps; outputs := outs; write_limit := wlim |> (evs ++ [ev_r]))`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame \\ metis_tac [])
    \\ xlet `POSTv resv. &(PAIR_TYPE ST ^(FRAME64_TYPE_tm) (step cur_st (frame64_decode h)) resv) *
                          (W8ARRAY bufv (0w :: h) *
                           FRAME64_IO_EV <| inputs := inps; outputs := outs; write_limit := wlim |> (evs ++ [ev_r]))`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame \\ metis_tac [])
    \\ Cases_on `step cur_st (frame64_decode h)`
    \\ rename1 `step _ _ = (next_st, resp)`
    \\ fs [ml_translatorTheory.PAIR_TYPE_def] \\ rveq
    \\ xmatch
    \\ xlet_auto_spec (SOME write_frame64_spec) >- (xsimpl \\ simp [])
    \\ qabbrev_tac `out_buf = 0w :: frame64_encode resp`
    \\ `LENGTH out_buf = 65` by simp [Abbr `out_buf`, frame64_encode_length]
    \\ Cases_on `wlim`
    >- (
      qabbrev_tac `ev_s = IO_event (ExtCall «send64») [] (ZIP (out_buf, out_buf))`
      \\ `¬event_is_err64 ev_s` by simp [Abbr `ev_s`, Abbr `out_buf`, event_is_err64_def]
      \\ xlet `POSTv uv.
           W8ARRAY bufv out_buf *
           FRAME64_IO_EV <| inputs := inps; outputs := outs ++ [frame64_encode resp]; write_limit := NONE |>
             (evs ++ [ev_r] ++ [ev_s])`
      >- (
        simp [FRAME64_IO_EV_def, Abbr `ev_s`] \\ xffi \\ simp [frame64_ffi_part_def]
        \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
        \\ map_every qexists_tac [`out_buf`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs ++ [ev_r]`]
        \\ unabbrev_all_tac
        \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_frame64_io,
                 ffi_send64_def, frame64_ffi_part_def, frame64_encode_length, TAKE_LENGTH_ID_rwt]
        \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def, Abbr `out_buf`])
      \\ xif \\ asm_exists_tac \\ fs [Abbr `out_buf`]
      \\ xapp \\ xsimpl
      \\ map_every qexists_tac [`emp`, `NONE`, `next_st`, `outs ++ [frame64_encode resp]`, `evs ++ [ev_r] ++ [ev_s]`]
      \\ simp [frame64_encode_length] \\ xsimpl
      \\ rpt strip_tac
      \\ map_every qexists_tac [`x'`, `x''`, `x'''`]
      \\ Cases_on `frame64_run step next_st inps`
      \\ simp [frame64_run_def, limit_frames64_def]
      \\ `outs ++ [frame64_encode resp] ++ r = outs ++ frame64_encode resp :: r` by simp []
      \\ pop_assum SUBST1_TAC \\ xsimpl)
    \\ Cases_on `x`
    >- (
      qabbrev_tac `ev_s = IO_event (ExtCall «send64») [] (ZIP (out_buf, 1w :: frame64_encode resp))`
      \\ xlet `POSTv uv.
           W8ARRAY bufv (1w :: frame64_encode resp) *
           FRAME64_IO_EV <| inputs := inps; outputs := outs ++ [frame64_encode resp]; write_limit := SOME 0 |>
             (evs ++ [ev_r] ++ [ev_s])`
      >- (
        simp [FRAME64_IO_EV_def, Abbr `ev_s`] \\ xffi \\ simp [frame64_ffi_part_def]
        \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
        \\ map_every qexists_tac [`out_buf`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs ++ [ev_r]`]
        \\ unabbrev_all_tac
        \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_frame64_io,
                 ffi_send64_def, frame64_ffi_part_def, frame64_encode_length, TAKE_LENGTH_ID_rwt]
        \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
      \\ xif \\ asm_exists_tac \\ fs []
      \\ xcon \\ xsimpl
      \\ map_every qexists_tac [`inps`, `SOME 0`, `evs ++ [ev_r] ++ [ev_s]`]
      \\ `stop_after_err64 (evs ++ [ev_r] ++ [ev_s])` by
           (`evs ++ [ev_r] ++ [ev_s] = (evs ++ [ev_r]) ++ [ev_s]` by simp []
            \\ pop_assum SUBST1_TAC \\ irule stop_after_err64_snoc \\ simp [])
      \\ Cases_on `frame64_run step next_st inps`
      \\ simp [frame64_run_def, limit_frames64_def, frame64_encode_length] \\ xsimpl)
    \\ qabbrev_tac `ev_s = IO_event (ExtCall «send64») [] (ZIP (out_buf, out_buf))`
    \\ `¬event_is_err64 ev_s` by simp [Abbr `ev_s`, Abbr `out_buf`, event_is_err64_def]
    \\ xlet `POSTv uv.
         W8ARRAY bufv out_buf *
         FRAME64_IO_EV <| inputs := inps; outputs := outs ++ [frame64_encode resp]; write_limit := SOME n |>
           (evs ++ [ev_r] ++ [ev_s])`
    >- (
      simp [FRAME64_IO_EV_def, Abbr `ev_s`] \\ xffi \\ simp [frame64_ffi_part_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`out_buf`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs ++ [ev_r]`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_frame64_io,
               ffi_send64_def, frame64_ffi_part_def, frame64_encode_length, TAKE_LENGTH_ID_rwt]
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def, Abbr `out_buf`])
    \\ xif \\ asm_exists_tac \\ fs [Abbr `out_buf`]
    \\ xapp \\ xsimpl
    \\ map_every qexists_tac [`emp`, `SOME n`, `next_st`, `outs ++ [frame64_encode resp]`, `evs ++ [ev_r] ++ [ev_s]`]
    \\ simp [frame64_encode_length] \\ xsimpl
    \\ rpt strip_tac
    \\ map_every qexists_tac [`x'`, `x''`, `x'''`]
    \\ Cases_on `frame64_run step next_st inps`
    \\ simp [frame64_run_def, limit_frames64_def]
    \\ `outs ++ [frame64_encode resp] ++ TAKE (SUC n) r = outs ++ frame64_encode resp :: TAKE (SUC n) r` by simp []
    \\ pop_assum SUBST1_TAC \\ xsimpl)
  \\ xlet `POSTv uv.
       W8ARRAY bufv (1w :: DROP 1 bs) *
       FRAME64_IO_EV <| inputs := h::inps; outputs := outs; write_limit := wlim |>
         (evs ++ [IO_event (ExtCall «recv64») [] (ZIP (bs, 1w :: DROP 1 bs))])`
  >- (
    simp [FRAME64_IO_EV_def] \\ xffi \\ simp [frame64_ffi_part_def]
    \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
    \\ map_every qexists_tac [`bs`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
    \\ unabbrev_all_tac
    \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_frame64_io,
             ffi_recv64_def, frame64_ffi_part_def] \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif \\ asm_exists_tac \\ fs []
  \\ xcon \\ xsimpl
  \\ map_every qexists_tac [`h::inps`, `wlim`, `evs ++ [IO_event (ExtCall «recv64») [] (ZIP (bs, 1w :: DROP 1 bs))]`]
  \\ simp [stop_after_err64_snoc]
  \\ Cases_on `wlim` \\ simp [frame64_run_def, limit_frames64_def] \\ xsimpl
QED

Theorem run_frame64_kernel_spec:
  ∀(ST:'st -> v -> bool) step stepv init_state init_statev inps wlim.
    (ST --> ^(FRAME64_TYPE_tm) --> PAIR_TYPE ST ^(FRAME64_TYPE_tm)) step stepv ∧
    ST init_state init_statev ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "run_frame64_kernel" st) [stepv; init_statev]
      (FRAME64_IO_EV <| inputs := inps; outputs := []; write_limit := wlim |> [])
      (POSTv rv.
        &(UNIT_TYPE () rv) *
        (SEP_EXISTS rest_inps wlim' evs'.
          &(stop_after_err64 evs') *
          FRAME64_IO_EV <| inputs := rest_inps;
                           outputs := limit_frames64 wlim (SND (frame64_run step init_state inps));
                           write_limit := wlim' |> evs'))
Proof
  rpt strip_tac
  \\ rename1 `ST st0 init_statev`
  \\ xcf "run_frame64_kernel" st
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp_spec frame64_loop_spec \\ xsimpl
  \\ map_every qexists_tac [`emp`, `wlim`, `step`, `st0`, `[]`, `inps`, `[]`, `ST`]
  \\ xsimpl \\ rpt strip_tac
  \\ map_every qexists_tac [`x'`, `x''`, `x'''`] \\ xsimpl
QED

Theorem frame64_parts_ok:
  ∀io. cfStore$parts_ok (frame64_ffi io) frame64_proj
Proof
  gen_tac
  \\ simp [cfStoreTheory.parts_ok_def, frame64_proj_def, frame64_ffi_def,
           ffiTheory.initial_ffi_state_def, frame64_ffi_part_def]
  \\ rpt conj_tac
  >- (qexists_tac `encode_frame64_io io` \\ rw [FUPDATE_LIST_THM, FLOOKUP_UPDATE])
  >- (rpt strip_tac \\ gvs [FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM, cfHeapsBaseTheory.mk_ffi_next_def,
                            decode_encode_frame64_io, AllCaseEqs(), ffi_recv64_def, ffi_send64_def])
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM, cfHeapsBaseTheory.mk_ffi_next_def,
          decode_encode_frame64_io, AllCaseEqs()]
  \\ (conj_tac >- (imp_res_tac ffi_recv64_length \\ imp_res_tac ffi_send64_length \\ simp [])
      \\ qexists_tac `s`
      \\ simp [frame64_ffi_oracle_def, FUPDATE_LIST_THM, fmap_eq_flookup, FLOOKUP_UPDATE] \\ rw [])
QED

Theorem frame64_io_split:
  ∀st2 io.
    st2.ffi = frame64_ffi io ⇒
    ∃h1 h2. SPLIT (st2heap frame64_proj st2) (h1, h2) ∧ FRAME64_IO_EV io [] h1
Proof
  rpt strip_tac
  \\ qabbrev_tac `ffip = FFI_part (encode_frame64_io io) (mk_ffi_next frame64_ffi_part)
                                  [«recv64»; «send64»] []`
  \\ qexists_tac `{ffip}` \\ qexists_tac `st2heap frame64_proj st2 DIFF {ffip}`
  \\ conj_tac
  >- (`ffip ∈ st2heap frame64_proj st2` by
        (simp [cfStoreTheory.st2heap_def] \\ disj2_tac
         \\ simp [frame64_proj_def, cfStoreTheory.ffi2heap_def]
         \\ simp [GSYM frame64_proj_def, frame64_parts_ok]
         \\ rw [Abbr `ffip`, frame64_proj_def, frame64_ffi_def, ffiTheory.initial_ffi_state_def,
                FUPDATE_LIST_THM, FLOOKUP_UPDATE])
      \\ fs [set_sepTheory.SPLIT_def, IN_DISJOINT, EXTENSION] \\ metis_tac [])
  \\ simp [FRAME64_IO_EV_def, set_sepTheory.one_def, Abbr `ffip`]
QED

Theorem frame64_io_ffi_part_hprop:
  ∀out.
    FFI_part_hprop
      (SEP_EXISTS rest_inps wlim' evs'.
        &(stop_after_err64 evs') *
        FRAME64_IO_EV <| inputs := rest_inps; outputs := out; write_limit := wlim' |> evs')
Proof
  gen_tac
  \\ ho_match_mp_tac cfMainTheory.FFI_part_hprop_SEP_EXISTS \\ gen_tac
  \\ ho_match_mp_tac cfMainTheory.FFI_part_hprop_SEP_EXISTS \\ gen_tac
  \\ ho_match_mp_tac cfMainTheory.FFI_part_hprop_SEP_EXISTS \\ gen_tac
  \\ simp [cfMainTheory.FFI_part_hprop_def, FRAME64_IO_EV_def, set_sepTheory.one_def,
           set_sepTheory.STAR_def, set_sepTheory.cond_def,
           set_sepTheory.SPLIT_def, set_sepTheory.emp_def]
  \\ rpt strip_tac \\ rveq \\ simp [] \\ metis_tac []
QED
