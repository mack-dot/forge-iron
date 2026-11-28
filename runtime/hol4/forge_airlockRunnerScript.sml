(*
  Forge Milestone 3 Reusable Runtime: Generic 4-FFI Crash-Atomic Airlock Runner (Zero-Basis).

  Extends `forge_frameRunner` and proves ONE polymorphic higher-order runner:
      run_airlock_kernel
        : (word8 list -> word8 list -> word8 list -> 'st)   (* recover_dual_slot *)
       -> (word8 list -> 'st -> frame64 -> 'st # frame128 # bool)  (* step *)
       -> ('st -> word8 list)                               (* encode_slot (256B) *)
       -> ('st -> word8)                                    (* commit_slot_byte *)
       -> unit

  Any M3+ crypto/crash-safe kernel simply calls `translation_extends "forge_airlockRunner"`,
  translates its pure HOL4 spec functions via `ml_translatorLib.translate`, and invokes
  `run_airlock_kernel` to inherit the entire verified bootload / dual-slot commit /
  recv64 / send128 Separation Logic proof with ZERO manual W8ARRAY reasoning.
*)
Theory forge_airlockRunner
Ancestors
  forge_frame64Spec forge_airlockFfi forge_frameRunner Word8ArrayProof cfMain
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib cfLib cfTacticsLib

val _ = translation_extends "forge_frameRunner";

val _ = register_type ``:frame128``;

val FRAME64_TYPE_tm  = ml_translatorLib.get_type_inv ``:frame64``;
val FRAME128_TYPE_tm = ml_translatorLib.get_type_inv ``:frame128``;

Quote add_cakeml:
  fun al_read_bytes a off n =
    if n = 0 then []
    else
      let
        val b = Word8Array.sub a off
        val rest = al_read_bytes a (off + 1) (n - 1)
      in
        b :: rest
      end

  fun al_write_bytes a off bs =
    case bs of
      [] => ()
    | b::rest => (Word8Array.update a off b; al_write_bytes a (off + 1) rest)

  fun al_write_frame128 a fr =
    case fr of
      Frame128 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
        (write_u64 a 1 w0;    write_u64 a 9 w1;    write_u64 a 17 w2;   write_u64 a 25 w3;
         write_u64 a 33 w4;   write_u64 a 41 w5;   write_u64 a 49 w6;   write_u64 a 57 w7;
         write_u64 a 65 w8;   write_u64 a 73 w9;   write_u64 a 81 w10;  write_u64 a 89 w11;
         write_u64 a 97 w12;  write_u64 a 105 w13; write_u64 a 113 w14; write_u64 a 121 w15)

  fun al_do_commit enc_slot slot_sel key cbuf state' =
    let
      val sel = slot_sel state'
      val enc1 = enc_slot key
      val rec_bs = enc1 state'
      val u1 = Word8Array.update cbuf 1 sel
      val u2 = al_write_bytes cbuf 2 rec_bs
      val u3 = #(commit) "" cbuf
      val cst = Word8Array.sub cbuf 0
    in
      cst = Word8.fromInt 0
    end

  fun airlock_loop step enc_slot slot_sel key rbuf cbuf sbuf state =
    let
      val u = #(recv64) "" rbuf
      val st = Word8Array.sub rbuf 0
    in
      if st = Word8.fromInt 0 then
        let
          val req = read_frame64 rbuf
          val step1 = step key
          val step2 = step1 state
          val res = step2 req
        in
          case res of
            (state', rest_p) =>
              case rest_p of
                (resp, dc) =>
                  let
                    val ok_c = if dc then al_do_commit enc_slot slot_sel key cbuf state' else True
                  in
                    if ok_c then
                      let
                        val u1 = al_write_frame128 sbuf resp
                        val u2 = #(send128) "" sbuf
                        val wst = Word8Array.sub sbuf 0
                      in
                        if wst = Word8.fromInt 0 then
                          airlock_loop step enc_slot slot_sel key rbuf cbuf sbuf state'
                        else
                          ()
                      end
                    else
                      ()
                  end
        end
      else
        ()
    end

  fun run_airlock_kernel recover step enc_slot slot_sel =
    let
      val bbuf = Word8Array.array 545 (Word8.fromInt 0)
      val u0 = #(bootload) "" bbuf
      val bst = Word8Array.sub bbuf 0
    in
      if bst = Word8.fromInt 0 then
        let
          val key = al_read_bytes bbuf 1 32
          val slotA = al_read_bytes bbuf 33 256
          val slotB = al_read_bytes bbuf 289 256
          val rec1 = recover key
          val rec2 = rec1 slotA
          val st0 = rec2 slotB
          val rbuf = Word8Array.array 65 (Word8.fromInt 0)
          val cbuf = Word8Array.array 258 (Word8.fromInt 0)
          val sbuf = Word8Array.array 129 (Word8.fromInt 0)
        in
          airlock_loop step enc_slot slot_sel key rbuf cbuf sbuf st0
        end
      else
        ()
    end
End

val st = get_ml_prog_state ();

(* ---- 1. Error-Termination Event Predicate & FFI Heap Predicate ---- *)

Definition event_is_err_al_def:
  (event_is_err_al (IO_event (ExtCall n) conf bs) ⇔ 1 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w) ∧
  (event_is_err_al _ ⇔ F)
End

Definition stop_after_err_al_def:
  (stop_after_err_al [] ⇔ T) ∧
  (stop_after_err_al (e::es) ⇔ if event_is_err_al e then es = [] else stop_after_err_al es)
End

Theorem stop_after_err_al_snoc:
  ∀es e. EVERY ($~ o event_is_err_al) es ⇒ stop_after_err_al (es ++ [e])
Proof
  Induct \\ simp [stop_after_err_al_def]
QED

Definition is_bootload_ev_def:
  (is_bootload_ev (IO_event (ExtCall n) _ _) ⇔ n = «bootload») ∧
  (is_bootload_ev _ ⇔ F)
End

Definition boot_first_once_al_def:
  (boot_first_once_al [] ⇔ T) ∧
  (boot_first_once_al (e::es) ⇔ is_bootload_ev e ∧ EVERY ($~ o is_bootload_ev) es)
End

Theorem boot_first_once_al_snoc:
  ∀es e. boot_first_once_al es ∧ es ≠ [] ∧ ¬is_bootload_ev e ⇒ boot_first_once_al (es ++ [e])
Proof
  Cases \\ simp [boot_first_once_al_def]
QED

Definition AIRLOCK_IO_EV_def:
  AIRLOCK_IO_EV (io:airlock_io) (evs:io_event list) =
    one (FFI_part (encode_airlock_io io) (mk_ffi_next airlock_ffi_part)
                  airlock_ffi_names evs)
End

(* ---- 2. Helper Array Specs ---- *)

Theorem al_read_bytes_spec:
  ∀n av bs off offv nv.
    NUM off offv ∧ NUM n nv ∧ off + n ≤ LENGTH bs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "al_read_bytes" st) [av; offv; nv]
      (W8ARRAY av bs)
      (POSTv bsv. &(LIST_TYPE WORD (TAKE n (DROP off bs)) bsv) * W8ARRAY av bs)
Proof
  Induct_on `n`
  >- (
    rpt strip_tac \\ xcf "al_read_bytes" st
    \\ xlet_auto >- xsimpl
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xcon \\ xsimpl \\ simp [ml_translatorTheory.LIST_TYPE_def])
  \\ rpt strip_tac \\ xcf "al_read_bytes" st
  \\ xlet_auto >- xsimpl
  \\ xif \\ asm_exists_tac \\ fs []
  \\ xlet_auto >- (xsimpl \\ decide_tac)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xsimpl \\ decide_tac)
  \\ xcon \\ xsimpl
  \\ `TAKE (SUC n) (DROP off bs) = EL off bs :: TAKE n (DROP (off + 1) bs)` by (
       `off < LENGTH bs` by decide_tac
       \\ simp [rich_listTheory.DROP_EL_CONS, ADD1])
  \\ simp [ml_translatorTheory.LIST_TYPE_def]
QED

Theorem al_write_bytes_spec:
  ∀ws wsv av bs off offv.
    NUM off offv ∧ LIST_TYPE WORD ws wsv ∧ off + LENGTH ws ≤ LENGTH bs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "al_write_bytes" st) [av; offv; wsv]
      (W8ARRAY av bs)
      (POSTv uv.
        &(UNIT_TYPE () uv) *
        W8ARRAY av (TAKE off bs ++ ws ++ DROP (off + LENGTH ws) bs))
Proof
  Induct_on `ws`
  >- (
    rpt strip_tac \\ fs [ml_translatorTheory.LIST_TYPE_def] \\ rveq
    \\ xcf "al_write_bytes" st \\ xmatch \\ xcon \\ xsimpl)
  \\ rpt strip_tac \\ fs [ml_translatorTheory.LIST_TYPE_def] \\ rveq
  \\ xcf "al_write_bytes" st \\ xmatch
  \\ xlet_auto >- (xsimpl \\ decide_tac)
  \\ xlet_auto >- xsimpl
  \\ xapp \\ xsimpl
  \\ qexists_tac `off + 1` \\ simp []
  \\ `TAKE (off + 1) (LUPDATE h off bs) = TAKE off bs ++ [h]` by (
       irule LIST_EQ \\ simp [LENGTH_TAKE, LENGTH_LUPDATE]
       \\ rpt strip_tac
       \\ Cases_on `x < off`
       >- simp [EL_TAKE, EL_LUPDATE, EL_APPEND1]
       \\ `x = off` by decide_tac \\ rveq
       \\ simp [EL_TAKE, EL_LUPDATE, EL_APPEND2, LENGTH_TAKE])
  \\ `DROP (off + (LENGTH ws + 1)) (LUPDATE h off bs) = DROP (off + SUC (LENGTH ws)) bs` by (
       irule LIST_EQ \\ simp [LENGTH_DROP, LENGTH_LUPDATE]
       \\ rpt strip_tac \\ simp [EL_DROP, EL_LUPDATE, ADD1])
  \\ simp []
QED

Theorem al_write_frame128_spec:
  ∀av bs fr frv.
    LENGTH bs = 129 ∧ ^(FRAME128_TYPE_tm) fr frv ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "al_write_frame128" st) [av; frv]
      (W8ARRAY av bs)
      (POSTv uv.
        &(UNIT_TYPE () uv) *
        W8ARRAY av (HD bs :: frame128_encode fr))
Proof
  rpt strip_tac
  \\ Cases_on `fr` \\ rename1 `Frame128 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15`
  \\ Cases_on `bs` \\ rename1 `W8ARRAY av (b0 :: rest)`
  \\ fs [fetch "-" "FORGE_AIRLOCKFFI_FRAME128_TYPE_def"] \\ rveq
  \\ xcf "al_write_frame128" st \\ xmatch
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ DROP 8 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w0` \\ simp [])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ DROP 16 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w1`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ DROP 24 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w2`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ DROP 32 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w3`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ DROP 40 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w4`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ DROP 48 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w5`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ DROP 56 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w6`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ DROP 64 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w7`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ DROP 72 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w8`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ le64_encode w9 ++ DROP 80 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w9`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ le64_encode w9 ++ le64_encode w10 ++ DROP 88 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w10`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ le64_encode w9 ++ le64_encode w10 ++ le64_encode w11 ++ DROP 96 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w11`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ le64_encode w9 ++ le64_encode w10 ++ le64_encode w11 ++ le64_encode w12 ++ DROP 104 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w12`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ le64_encode w9 ++ le64_encode w10 ++ le64_encode w11 ++ le64_encode w12 ++ le64_encode w13 ++ DROP 112 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w13`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xlet `POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY av (b0 :: le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ le64_encode w9 ++ le64_encode w10 ++ le64_encode w11 ++ le64_encode w12 ++ le64_encode w13 ++ le64_encode w14 ++ DROP 120 rest)`
  >- (xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w14`
      \\ simp [le64_encode_length, TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T])
  \\ xapp_spec write_u64_spec \\ xsimpl \\ qexists_tac `w15`
  \\ simp [frame128_encode_def, le64_encode_length, TAKE_APPEND, DROP_APPEND,
           TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T]
QED

Theorem Arrow_app_1_frame_al[local]:
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

(* ---- 3. Dual-Slot Commit, Main Loop & Kernel Entry CF Specs ---- *)

Theorem al_do_commit_spec:
  ∀(ST:'st -> v -> bool) (enc_slot:word8 list -> 'st -> word8 list) encv (slot_sel:'st -> word8) selv
    key keyv cbufv cbs state' stv io evs.
    (LIST_TYPE WORD --> ST --> LIST_TYPE WORD) enc_slot encv ∧
    (ST --> WORD) slot_sel selv ∧
    LIST_TYPE WORD key keyv ∧
    ST state' stv ∧
    LENGTH (enc_slot key state') = 256 ∧
    LENGTH cbs = 258 ∧
    EVERY ($~ o event_is_err_al) evs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "al_do_commit" st) [encv; selv; keyv; cbufv; stv]
      (W8ARRAY cbufv cbs * AIRLOCK_IO_EV io evs)
      (POSTv bv.
        let sel = slot_sel state' in
        let rec = enc_slot key state' in
        let io_upd = if (sel && 1w) = 0w then io with slotA := rec else io with slotB := rec in
        case io.commit_limit of
          NONE =>
            &(BOOL T bv) *
            (SEP_EXISTS cbs' ev.
              &(¬event_is_err_al ev ∧ ¬is_bootload_ev ev) *
              W8ARRAY cbufv cbs' * &(LENGTH cbs' = 258) *
              AIRLOCK_IO_EV io_upd (evs ++ [ev]))
        | SOME 0 =>
            &(BOOL F bv) *
            (SEP_EXISTS cbs' ev.
              &(event_is_err_al ev ∧ ¬is_bootload_ev ev) *
              W8ARRAY cbufv cbs' * &(LENGTH cbs' = 258) *
              AIRLOCK_IO_EV io (evs ++ [ev]))
        | SOME (SUC c) =>
            &(BOOL T bv) *
            (SEP_EXISTS cbs' ev.
              &(¬event_is_err_al ev ∧ ¬is_bootload_ev ev) *
              W8ARRAY cbufv cbs' * &(LENGTH cbs' = 258) *
              AIRLOCK_IO_EV (io_upd with commit_limit := SOME c) (evs ++ [ev])))
Proof
  rpt strip_tac
  \\ xcf "al_do_commit" st
  \\ xlet `POSTv sel_v. &(WORD (slot_sel state') sel_v) * (W8ARRAY cbufv cbs * AIRLOCK_IO_EV io evs)`
  >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
  \\ xlet `POSTv enc1_v. &((ST --> LIST_TYPE (WORD:word8 -> v -> bool)) (enc_slot key) enc1_v) * (W8ARRAY cbufv cbs * AIRLOCK_IO_EV io evs)`
  >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
  \\ xlet `POSTv rec_v. &(LIST_TYPE WORD (enc_slot key state') rec_v) * (W8ARRAY cbufv cbs * AIRLOCK_IO_EV io evs)`
  >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto_spec (SOME al_write_bytes_spec) >- (xsimpl \\ simp [])
  \\ qabbrev_tac `sel = slot_sel state'`
  \\ qabbrev_tac `rec = enc_slot key state'`
  \\ qabbrev_tac `buf_in = HD cbs :: sel :: rec`
  \\ `TAKE 2 (LUPDATE sel 1 cbs) ++ rec = buf_in` by (
       Cases_on `cbs` \\ fs [] \\ Cases_on `t` \\ fs []
       \\ `LUPDATE sel 1 (h::h'::t') = h::sel::t'` by
            (irule LIST_EQ \\ simp [LENGTH_LUPDATE] \\ rpt strip_tac
             \\ Cases_on `x = 0` \\ Cases_on `x = 1` \\ simp [EL_LUPDATE]
             \\ Cases_on `x` \\ fs [] \\ Cases_on `n` \\ fs [])
       \\ simp [Abbr `buf_in`])
  \\ pop_assum SUBST_ALL_TAC
  \\ `LENGTH buf_in = 258` by simp [Abbr `buf_in`]
  \\ `EL 1 buf_in = sel ∧ TAKE 256 (DROP 2 buf_in) = rec ∧ DROP 1 buf_in = sel :: rec` by
       simp [Abbr `buf_in`, TAKE_LENGTH_ID_rwt]
  \\ Cases_on `io.commit_limit`
  >- (
    qabbrev_tac `io_upd = if (sel && 1w) = 0w then io with slotA := rec else io with slotB := rec`
    \\ qabbrev_tac `ev_c = IO_event (ExtCall «commit») [] (ZIP (buf_in, 0w :: sel :: rec))`
    \\ `¬event_is_err_al ev_c` by simp [Abbr `ev_c`, Abbr `buf_in`, event_is_err_al_def]
    \\ xlet `POSTv uv.
         W8ARRAY cbufv (0w :: sel :: rec) *
         AIRLOCK_IO_EV io_upd (evs ++ [ev_c])`
    >- (
      simp [AIRLOCK_IO_EV_def, Abbr `ev_c`, Abbr `io_upd`] \\ xffi
      \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`buf_in`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
               ffi_commit_def, airlock_ffi_part_def] \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xapp_spec (INST_TYPE [alpha |-> ``:word8``] mlbasicsProgTheory.eq_v_thm)
    \\ xsimpl
    \\ map_every qexists_tac [`0w:word8`, `0w:word8`, `WORD:word8 -> v -> bool`]
    \\ simp [ml_translatorTheory.EqualityType_NUM_BOOL]
    \\ rpt strip_tac \\ qexists_tac `ev_c`
    \\ simp [Abbr `io_upd`, Abbr `ev_c`, is_bootload_ev_def] \\ xsimpl)
  \\ Cases_on `x`
  >- (
    qabbrev_tac `ev_c = IO_event (ExtCall «commit») [] (ZIP (buf_in, 1w :: sel :: rec))`
    \\ `event_is_err_al ev_c` by simp [Abbr `ev_c`, Abbr `buf_in`, event_is_err_al_def]
    \\ xlet `POSTv uv.
         W8ARRAY cbufv (1w :: sel :: rec) *
         AIRLOCK_IO_EV io (evs ++ [ev_c])`
    >- (
      simp [AIRLOCK_IO_EV_def, Abbr `ev_c`] \\ xffi
      \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`buf_in`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
               ffi_commit_def, airlock_ffi_part_def] \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xapp_spec (INST_TYPE [alpha |-> ``:word8``] mlbasicsProgTheory.eq_v_thm)
    \\ xsimpl
    \\ map_every qexists_tac [`0w:word8`, `1w:word8`, `WORD:word8 -> v -> bool`]
    \\ simp [ml_translatorTheory.EqualityType_NUM_BOOL]
    \\ rpt strip_tac \\ qexists_tac `ev_c` \\ simp [Abbr `ev_c`, is_bootload_ev_def] \\ xsimpl)
  \\ qabbrev_tac `io_upd = if (sel && 1w) = 0w then io with slotA := rec else io with slotB := rec`
  \\ qabbrev_tac `ev_c = IO_event (ExtCall «commit») [] (ZIP (buf_in, 0w :: sel :: rec))`
  \\ `¬event_is_err_al ev_c` by simp [Abbr `ev_c`, Abbr `buf_in`, event_is_err_al_def]
  \\ xlet `POSTv uv.
       W8ARRAY cbufv (0w :: sel :: rec) *
       AIRLOCK_IO_EV (io_upd with commit_limit := SOME n) (evs ++ [ev_c])`
  >- (
    simp [AIRLOCK_IO_EV_def, Abbr `ev_c`, Abbr `io_upd`] \\ xffi
    \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
    \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
    \\ map_every qexists_tac [`buf_in`, `emp`, `st_e`, `u_fn`, `ns_l`, `evs`]
    \\ unabbrev_all_tac
    \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
             ffi_commit_def, airlock_ffi_part_def] \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (INST_TYPE [alpha |-> ``:word8``] mlbasicsProgTheory.eq_v_thm)
  \\ xsimpl
  \\ map_every qexists_tac [`0w:word8`, `0w:word8`, `WORD:word8 -> v -> bool`]
  \\ simp [ml_translatorTheory.EqualityType_NUM_BOOL]
  \\ rpt strip_tac \\ qexists_tac `ev_c`
  \\ simp [Abbr `io_upd`, Abbr `ev_c`, is_bootload_ev_def] \\ xsimpl
QED

Theorem airlock_loop_spec:
  ∀(ST:'st -> v -> bool) step stepv (enc_slot:word8 list -> 'st -> word8 list) encv (slot_sel:'st -> word8) selv
    inps bk bf sA sB outs clim wlim evs keyv rbufv rbs cbufv cbs sbufv sbs state statev.
    (LIST_TYPE WORD --> ST --> ^(FRAME64_TYPE_tm) -->
      PAIR_TYPE ST (PAIR_TYPE ^(FRAME128_TYPE_tm) BOOL)) step stepv ∧
    (LIST_TYPE WORD --> ST --> LIST_TYPE WORD) enc_slot encv ∧
    (ST --> WORD) slot_sel selv ∧
    (∀k s. LENGTH (enc_slot k s) = 256) ∧
    LIST_TYPE WORD bk keyv ∧
    ST state statev ∧
    LENGTH rbs = 65 ∧ LENGTH cbs = 258 ∧ LENGTH sbs = 129 ∧
    EVERY ($~ o event_is_err_al) evs ∧
    evs ≠ [] ∧ boot_first_once_al evs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "airlock_loop" st)
      [stepv; encv; selv; keyv; rbufv; cbufv; sbufv; statev]
      (W8ARRAY rbufv rbs * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
       AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                        inputs := inps; outputs := outs;
                        commit_limit := clim; write_limit := wlim |> evs)
      (POSTv uv.
        &(UNIT_TYPE () uv) *
        (SEP_EXISTS rbs' cbs' sbs' sA' sB' rest_inps clim' wlim' evs'.
          W8ARRAY rbufv rbs' * W8ARRAY cbufv cbs' * W8ARRAY sbufv sbs' *
          &(stop_after_err_al evs') *
          &(boot_first_once_al evs') *
          AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB';
                           inputs := rest_inps;
                           outputs := outs ++ SND (airlock_exec step bk state inps clim wlim);
                           commit_limit := clim'; write_limit := wlim' |> evs'))
Proof
  ntac 7 gen_tac
  \\ Induct_on `inps`
  >- (
    rpt strip_tac
    \\ xcf "airlock_loop" st
    \\ qabbrev_tac `ev_r = IO_event (ExtCall «recv64») [] (ZIP (rbs, 1w :: DROP 1 rbs))`
    \\ xlet `POSTv uv.
         W8ARRAY rbufv (1w :: DROP 1 rbs) * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
         AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                          inputs := []; outputs := outs;
                          commit_limit := clim; write_limit := wlim |> (evs ++ [ev_r])`
    >- (
      simp [AIRLOCK_IO_EV_def, Abbr `ev_r`] \\ xffi
      \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`rbs`, `W8ARRAY cbufv cbs * W8ARRAY sbufv sbs`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
               ffi_al_recv64_def, airlock_ffi_part_def] \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xcon \\ xsimpl
    \\ map_every qexists_tac [`sA`, `sB`, `[]`, `clim`, `wlim`, `evs ++ [ev_r]`]
    \\ `boot_first_once_al (evs ++ [ev_r])` by (irule boot_first_once_al_snoc \\ simp [Abbr `ev_r`, is_bootload_ev_def])
    \\ simp [stop_after_err_al_snoc, airlock_exec_def] \\ xsimpl)
  \\ rpt strip_tac
  \\ rename1 `ST cur_st statev`
  \\ xcf "airlock_loop" st
  \\ Cases_on `LENGTH h = 64`
  >- (
    qabbrev_tac `ev_r = IO_event (ExtCall «recv64») [] (ZIP (rbs, 0w :: h))`
    \\ `¬event_is_err_al ev_r` by
         (simp [Abbr `ev_r`, event_is_err_al_def] \\ Cases_on `rbs` \\ fs [listTheory.ZIP])
    \\ xlet `POSTv uv.
         W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
         AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                          inputs := inps; outputs := outs;
                          commit_limit := clim; write_limit := wlim |> (evs ++ [ev_r])`
    >- (
      simp [AIRLOCK_IO_EV_def, Abbr `ev_r`] \\ xffi
      \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`rbs`, `W8ARRAY cbufv cbs * W8ARRAY sbufv sbs`, `st_e`, `u_fn`, `ns_l`, `evs`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
               ffi_al_recv64_def, airlock_ffi_part_def, DROP_LENGTH_TOO_LONG] \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xlet_auto_spec (SOME read_frame64_spec) >- (xsimpl \\ simp [])
    \\ qabbrev_tac `io1 = <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                             inputs := inps; outputs := outs;
                             commit_limit := clim; write_limit := wlim |>`
    \\ xlet `POSTv step1v. &((ST --> ^(FRAME64_TYPE_tm) --> PAIR_TYPE ST (PAIR_TYPE ^(FRAME128_TYPE_tm) BOOL)) (step bk) step1v) *
                          (W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
                           AIRLOCK_IO_EV io1 (evs ++ [ev_r]))`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
    \\ xlet `POSTv step2v. &((^(FRAME64_TYPE_tm) --> PAIR_TYPE ST (PAIR_TYPE ^(FRAME128_TYPE_tm) BOOL)) (step bk cur_st) step2v) *
                          (W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
                           AIRLOCK_IO_EV io1 (evs ++ [ev_r]))`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
    \\ xlet `POSTv resv. &(PAIR_TYPE ST (PAIR_TYPE ^(FRAME128_TYPE_tm) BOOL) (step bk cur_st (frame64_decode h)) resv) *
                          (W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
                           AIRLOCK_IO_EV io1 (evs ++ [ev_r]))`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
    \\ Cases_on `step bk cur_st (frame64_decode h)` \\ Cases_on `r`
    \\ rename1 `step _ _ _ = (next_st, resp, dc)`
    \\ fs [ml_translatorTheory.PAIR_TYPE_def] \\ rveq
    \\ xmatch \\ xmatch
    \\ (* Handle commit branch cleanly via unified intermediate postcondition *)
    qabbrev_tac `sel = slot_sel next_st`
    \\ qabbrev_tac `rec_b = enc_slot bk next_st`
    \\ qabbrev_tac `sA_c = if dc ∧ (sel && 1w) = 0w then rec_b else sA`
    \\ qabbrev_tac `sB_c = if dc ∧ (sel && 1w) ≠ 0w then rec_b else sB`
    \\ qabbrev_tac `ok_commit = (¬dc ∨ clim ≠ SOME 0)`
    \\ qabbrev_tac `clim_next = if dc then (case clim of NONE => NONE | SOME 0 => SOME 0 | SOME (SUC c) => SOME c) else clim`
    \\ xlet `POSTv okv.
         &(BOOL ok_commit okv) *
         (SEP_EXISTS cbs1 evs1.
           W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs1 * W8ARRAY sbufv sbs *
           &(LENGTH cbs1 = 258) *
           &(evs1 ≠ [] ∧ boot_first_once_al evs1) *
           &(if ok_commit then EVERY ($~ o event_is_err_al) evs1 else stop_after_err_al evs1) *
           AIRLOCK_IO_EV (if ok_commit then
                            io1 with <| slotA := sA_c; slotB := sB_c; commit_limit := clim_next |>
                          else io1) evs1)`
    >- (
      `boot_first_once_al (evs ++ [ev_r])` by (irule boot_first_once_al_snoc \\ simp [Abbr `ev_r`, is_bootload_ev_def])
      \\ xif
      >- (
        (* dc = T *)
        xapp_spec al_do_commit_spec
        \\ map_every qexists_tac [`W8ARRAY rbufv (0w :: h) * W8ARRAY sbufv sbs`,
                                  `next_st`, `slot_sel`, `bk`, `io1`, `evs ++ [ev_r]`, `enc_slot`, `cbs`]
        \\ conj_tac >- (simp [] \\ qexists_tac `ST` \\ simp [])
        \\ conj_tac >- xsimpl
        \\ Cases_on `clim`
        \\ simp [Abbr `io1`, Abbr `ok_commit`, Abbr `clim_next`, Abbr `sA_c`, Abbr `sB_c`, Abbr `sel`, Abbr `rec_b`, LET_THM]
        >- (xsimpl \\ rpt strip_tac \\ rename1 `¬event_is_err_al ev_c`
            \\ qexists_tac `evs ++ [ev_r] ++ [ev_c]`
            \\ `boot_first_once_al ((evs ++ [ev_r]) ++ [ev_c])` by (irule boot_first_once_al_snoc \\ simp [])
            \\ IF_CASES_TAC \\ fs [] \\ xsimpl)
        \\ Cases_on `x` \\ simp []
        >- (xsimpl \\ rpt strip_tac \\ rename1 `event_is_err_al ev_c`
            \\ qexists_tac `evs ++ [ev_r] ++ [ev_c]`
            \\ `stop_after_err_al ((evs ++ [ev_r]) ++ [ev_c])` by (irule stop_after_err_al_snoc \\ simp [])
            \\ `boot_first_once_al ((evs ++ [ev_r]) ++ [ev_c])` by (irule boot_first_once_al_snoc \\ simp [])
            \\ fs [] \\ xsimpl)
        \\ xsimpl \\ rpt strip_tac \\ rename1 `¬event_is_err_al ev_c`
        \\ qexists_tac `evs ++ [ev_r] ++ [ev_c]`
        \\ `boot_first_once_al ((evs ++ [ev_r]) ++ [ev_c])` by (irule boot_first_once_al_snoc \\ simp [])
        \\ IF_CASES_TAC \\ fs [] \\ xsimpl)
      \\ (* dc = F *)
      xcon \\ xsimpl
      \\ qexists_tac `evs ++ [ev_r]`
      \\ simp [Abbr `ok_commit`, Abbr `clim_next`, Abbr `sA_c`, Abbr `sB_c`, Abbr `io1`] \\ xsimpl)
    \\ xif
    >- (
      (* ok_commit = T *)
      xlet_auto_spec (SOME al_write_frame128_spec) >- (xsimpl \\ simp [])
      \\ qabbrev_tac `out_buf = HD sbs :: frame128_encode resp`
      \\ `LENGTH out_buf = 129` by simp [Abbr `out_buf`, frame128_encode_length]
      \\ `TAKE 128 (DROP 1 out_buf) = frame128_encode resp ∧ DROP 1 out_buf = frame128_encode resp` by
           simp [Abbr `out_buf`, frame128_encode_length, TAKE_LENGTH_ID_rwt]
      \\ Cases_on `wlim`
      >- (
        qabbrev_tac `ev_s = IO_event (ExtCall «send128») [] (ZIP (out_buf, 0w :: frame128_encode resp))`
        \\ `¬event_is_err_al ev_s` by simp [Abbr `ev_s`, Abbr `out_buf`, event_is_err_al_def]
        \\ xlet `POSTv uv.
             W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs1 * W8ARRAY sbufv (0w :: frame128_encode resp) *
             AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA_c; slotB := sB_c;
                              inputs := inps; outputs := outs ++ [frame128_encode resp];
                              commit_limit := clim_next; write_limit := NONE |> (evs1 ++ [ev_s])`
        >- (
          simp [AIRLOCK_IO_EV_def, Abbr `ev_s`, Abbr `io1`] \\ xffi
          \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
          \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
          \\ map_every qexists_tac [`out_buf`, `W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs1`, `st_e`, `u_fn`, `ns_l`, `evs1`]
          \\ unabbrev_all_tac
          \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
                   ffi_al_send128_def, airlock_ffi_part_def] \\ xsimpl)
        \\ xlet_auto >- xsimpl
        \\ xlet_auto >- xsimpl
        \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
        \\ xif \\ asm_exists_tac \\ fs []
        \\ xapp \\ xsimpl
        \\ map_every qexists_tac [`emp`, `NONE`, `next_st`, `sB_c`, `sA_c`,
                                  `outs ++ [frame128_encode resp]`, `evs1 ++ [ev_s]`, `clim_next`, `bk`, `bf`]
        \\ `boot_first_once_al (evs1 ++ [ev_s])` by (irule boot_first_once_al_snoc \\ simp [Abbr `ev_s`, is_bootload_ev_def])
        \\ simp [frame128_encode_length] \\ xsimpl
        \\ qx_genl_tac [`uv_e`, `sA_e`, `sB_e`, `inps_e`, `clim_e`, `wlim_e`, `evs_e`]
        \\ rpt strip_tac
        \\ map_every qexists_tac [`sA_e`, `sB_e`, `inps_e`, `clim_e`, `wlim_e`, `evs_e`]
        \\ Cases_on `dc`
        >- (Cases_on `clim` \\ fs [Abbr `ok_commit`, Abbr `clim_next`]
            >- (Cases_on `airlock_exec step bk next_st inps NONE NONE`
                \\ simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC, airlock_exec_def] \\ xsimpl)
            \\ Cases_on `x` \\ fs []
            \\ qmatch_goalsub_abbrev_tac `airlock_exec step bk next_st inps clim_r NONE`
            \\ Cases_on `airlock_exec step bk next_st inps clim_r NONE`
            \\ simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC, airlock_exec_def, Abbr `clim_r`] \\ xsimpl)
        \\ fs [Abbr `ok_commit`, Abbr `clim_next`]
        \\ Cases_on `airlock_exec step bk next_st inps clim NONE`
        \\ simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC, airlock_exec_def] \\ xsimpl)
      \\ Cases_on `x`
      >- (
        qabbrev_tac `ev_s = IO_event (ExtCall «send128») [] (ZIP (out_buf, 1w :: frame128_encode resp))`
        \\ xlet `POSTv uv.
             W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs1 * W8ARRAY sbufv (1w :: frame128_encode resp) *
             AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA_c; slotB := sB_c;
                              inputs := inps; outputs := outs ++ [frame128_encode resp];
                              commit_limit := clim_next; write_limit := SOME 0 |> (evs1 ++ [ev_s])`
        >- (
          simp [AIRLOCK_IO_EV_def, Abbr `ev_s`, Abbr `io1`] \\ xffi
          \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
          \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
          \\ map_every qexists_tac [`out_buf`, `W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs1`, `st_e`, `u_fn`, `ns_l`, `evs1`]
          \\ unabbrev_all_tac
          \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
                   ffi_al_send128_def, airlock_ffi_part_def] \\ xsimpl)
        \\ xlet_auto >- xsimpl
        \\ xlet_auto >- xsimpl
        \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
        \\ xif \\ asm_exists_tac \\ fs []
        \\ xcon \\ xsimpl
        \\ map_every qexists_tac [`sA_c`, `sB_c`, `inps`, `clim_next`, `SOME 0`, `evs1 ++ [ev_s]`]
        \\ `boot_first_once_al (evs1 ++ [ev_s])` by (irule boot_first_once_al_snoc \\ simp [Abbr `ev_s`, is_bootload_ev_def])
        \\ simp [stop_after_err_al_snoc]
        \\ Cases_on `dc`
        >- (Cases_on `clim` \\ fs [Abbr `ok_commit`, Abbr `clim_next`]
            >- (simp [airlock_exec_def] \\ xsimpl)
            \\ Cases_on `x` \\ fs [] \\ simp [airlock_exec_def] \\ xsimpl)
        \\ fs [Abbr `ok_commit`, Abbr `clim_next`] \\ simp [airlock_exec_def] \\ xsimpl)
      \\ qabbrev_tac `ev_s = IO_event (ExtCall «send128») [] (ZIP (out_buf, 0w :: frame128_encode resp))`
      \\ `¬event_is_err_al ev_s` by simp [Abbr `ev_s`, Abbr `out_buf`, event_is_err_al_def]
      \\ xlet `POSTv uv.
           W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs1 * W8ARRAY sbufv (0w :: frame128_encode resp) *
           AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA_c; slotB := sB_c;
                            inputs := inps; outputs := outs ++ [frame128_encode resp];
                            commit_limit := clim_next; write_limit := SOME n |> (evs1 ++ [ev_s])`
      >- (
        simp [AIRLOCK_IO_EV_def, Abbr `ev_s`, Abbr `io1`] \\ xffi
        \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
        \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
        \\ map_every qexists_tac [`out_buf`, `W8ARRAY rbufv (0w :: h) * W8ARRAY cbufv cbs1`, `st_e`, `u_fn`, `ns_l`, `evs1`]
        \\ unabbrev_all_tac
        \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
                 ffi_al_send128_def, airlock_ffi_part_def] \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
      \\ xif \\ asm_exists_tac \\ fs []
      \\ xapp \\ xsimpl
      \\ map_every qexists_tac [`emp`, `SOME n`, `next_st`, `sB_c`, `sA_c`,
                                `outs ++ [frame128_encode resp]`, `evs1 ++ [ev_s]`, `clim_next`, `bk`, `bf`]
      \\ `boot_first_once_al (evs1 ++ [ev_s])` by (irule boot_first_once_al_snoc \\ simp [Abbr `ev_s`, is_bootload_ev_def])
      \\ simp [frame128_encode_length] \\ xsimpl
      \\ qx_genl_tac [`uv_e`, `sA_e`, `sB_e`, `inps_e`, `clim_e`, `wlim_e`, `evs_e`]
      \\ rpt strip_tac
      \\ map_every qexists_tac [`sA_e`, `sB_e`, `inps_e`, `clim_e`, `wlim_e`, `evs_e`]
      \\ Cases_on `dc`
      >- (Cases_on `clim` \\ fs [Abbr `ok_commit`, Abbr `clim_next`]
          >- (Cases_on `airlock_exec step bk next_st inps NONE (SOME n)`
              \\ simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC, airlock_exec_def] \\ xsimpl)
          \\ Cases_on `x` \\ fs []
          \\ qmatch_goalsub_abbrev_tac `airlock_exec step bk next_st inps clim_r (SOME n)`
          \\ Cases_on `airlock_exec step bk next_st inps clim_r (SOME n)`
          \\ simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC, airlock_exec_def, Abbr `clim_r`] \\ xsimpl)
      \\ fs [Abbr `ok_commit`, Abbr `clim_next`]
      \\ Cases_on `airlock_exec step bk next_st inps clim (SOME n)`
      \\ simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC, airlock_exec_def] \\ xsimpl)
    \\ (* ok_commit = F => dc = T ∧ clim = SOME 0 *)
    `dc ∧ clim = SOME 0` by fs [Abbr `ok_commit`]
    \\ `stop_after_err_al evs1` by fs []
    \\ xcon \\ xsimpl
    \\ map_every qexists_tac [`sA`, `sB`, `inps`, `SOME 0`, `wlim`, `evs1`]
    \\ simp [airlock_exec_def, Abbr `io1`] \\ xsimpl)
  \\ (* LENGTH h ≠ 64 *)
  qabbrev_tac `ev_r = IO_event (ExtCall «recv64») [] (ZIP (rbs, 1w :: DROP 1 rbs))`
  \\ xlet `POSTv uv.
       W8ARRAY rbufv (1w :: DROP 1 rbs) * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
       AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                        inputs := h::inps; outputs := outs;
                        commit_limit := clim; write_limit := wlim |> (evs ++ [ev_r])`
  >- (
    simp [AIRLOCK_IO_EV_def, Abbr `ev_r`] \\ xffi
    \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
    \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
    \\ map_every qexists_tac [`rbs`, `W8ARRAY cbufv cbs * W8ARRAY sbufv sbs`, `st_e`, `u_fn`, `ns_l`, `evs`]
    \\ unabbrev_all_tac
    \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
             ffi_al_recv64_def, airlock_ffi_part_def] \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
  \\ xif \\ asm_exists_tac \\ fs []
  \\ xcon \\ xsimpl
  \\ map_every qexists_tac [`sA`, `sB`, `h::inps`, `clim`, `wlim`, `evs ++ [ev_r]`]
  \\ `boot_first_once_al (evs ++ [ev_r])` by (irule boot_first_once_al_snoc \\ simp [Abbr `ev_r`, is_bootload_ev_def])
  \\ simp [stop_after_err_al_snoc, airlock_exec_def] \\ xsimpl
QED

Theorem run_airlock_kernel_spec:
  ∀(ST:'st -> v -> bool) recover recv step stepv (enc_slot:word8 list -> 'st -> word8 list) encv (slot_sel:'st -> word8) selv
    bk bf sA sB inps clim wlim.
    (LIST_TYPE WORD --> LIST_TYPE WORD --> LIST_TYPE WORD --> ST) recover recv ∧
    (LIST_TYPE WORD --> ST --> ^(FRAME64_TYPE_tm) -->
      PAIR_TYPE ST (PAIR_TYPE ^(FRAME128_TYPE_tm) BOOL)) step stepv ∧
    (LIST_TYPE WORD --> ST --> LIST_TYPE WORD) enc_slot encv ∧
    (ST --> WORD) slot_sel selv ∧
    (∀k s. LENGTH (enc_slot k s) = 256) ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "run_airlock_kernel" st) [recv; stepv; encv; selv]
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
                               SND (airlock_exec step bk (recover bk sA sB) inps clim wlim)
                             else [];
                           commit_limit := clim'; write_limit := wlim' |> evs'))
Proof
  rpt strip_tac
  \\ xcf "run_airlock_kernel" st
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 `W8ARRAY bbuf (REPLICATE 545 0w)`
  \\ qabbrev_tac `io0 = <| boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB;
                           inputs := inps; outputs := [];
                           commit_limit := clim; write_limit := wlim |>`
  \\ Cases_on `¬bf ∧ LENGTH bk = 32 ∧ LENGTH sA = 256 ∧ LENGTH sB = 256`
  >- (
    qabbrev_tac `boot_bs = 0w :: (bk ++ sA ++ sB)`
    \\ `LENGTH boot_bs = 545` by simp [Abbr `boot_bs`]
    \\ qabbrev_tac `ev_b = IO_event (ExtCall «bootload») [] (ZIP (REPLICATE 545 0w, boot_bs))`
    \\ `¬event_is_err_al ev_b` by
         (simp [Abbr `ev_b`, Abbr `boot_bs`, event_is_err_al_def]
          \\ `REPLICATE 545 (0w:word8) = 0w :: REPLICATE 544 0w` by EVAL_TAC
          \\ pop_assum SUBST1_TAC \\ simp [listTheory.ZIP])
    \\ xlet `POSTv uv. W8ARRAY bbuf boot_bs * AIRLOCK_IO_EV io0 [ev_b]`
    >- (
      simp [AIRLOCK_IO_EV_def, Abbr `ev_b`, Abbr `boot_bs`, Abbr `io0`] \\ xffi
      \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
      \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
      \\ map_every qexists_tac [`REPLICATE 545 0w`, `emp`, `st_e`, `u_fn`, `ns_l`, `[]`]
      \\ unabbrev_all_tac
      \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
               ffi_bootload_def, airlock_ffi_part_def, DROP_LENGTH_TOO_LONG] \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def, Abbr `boot_bs`])
    \\ xif \\ asm_exists_tac \\ fs [Abbr `boot_bs`]
    \\ xlet_auto_spec (SOME al_read_bytes_spec) >- (xsimpl \\ simp [])
    \\ `TAKE 32 (bk ++ sA ++ sB) = bk` by
         simp [TAKE_APPEND1, TAKE_LENGTH_ID_rwt]
    \\ pop_assum SUBST_ALL_TAC
    \\ xlet_auto_spec (SOME al_read_bytes_spec) >- (xsimpl \\ simp [])
    \\ `TAKE 256 (DROP 32 (bk ++ sA ++ sB)) = sA` by
         simp [Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC, DROP_APPEND2, TAKE_APPEND1, TAKE_LENGTH_ID_rwt]
    \\ pop_assum SUBST_ALL_TAC
    \\ xlet_auto_spec (SOME al_read_bytes_spec) >- (xsimpl \\ simp [])
    \\ `TAKE 256 (DROP 288 (bk ++ sA ++ sB)) = sB` by
         (`LENGTH (bk ++ sA) = 288` by simp []
          \\ simp [DROP_APPEND2, TAKE_LENGTH_ID_rwt])
    \\ pop_assum SUBST_ALL_TAC
    \\ xlet `POSTv r1v. &((LIST_TYPE WORD --> LIST_TYPE WORD --> ST) (recover bk) r1v) *
                          (W8ARRAY bbuf (0w :: (bk ++ sA ++ sB)) * AIRLOCK_IO_EV io0 [ev_b])`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
    \\ xlet `POSTv r2v. &((LIST_TYPE WORD --> ST) (recover bk sA) r2v) *
                          (W8ARRAY bbuf (0w :: (bk ++ sA ++ sB)) * AIRLOCK_IO_EV io0 [ev_b])`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
    \\ xlet `POSTv st0v. &(ST (recover bk sA sB) st0v) *
                          (W8ARRAY bbuf (0w :: (bk ++ sA ++ sB)) * AIRLOCK_IO_EV io0 [ev_b])`
    >- (xapp_prepare_goal \\ irule Arrow_app_1_frame_al \\ metis_tac [])
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xapp_spec airlock_loop_spec \\ xsimpl
    \\ map_every qexists_tac [`W8ARRAY bbuf (0w :: (bk ++ sA ++ sB))`, `wlim`, `step`,
                              `recover bk sA sB`, `sB`, `sA`, `[]`, `inps`, `[ev_b]`,
                              `clim`, `bk`, `F`, `ST`, `enc_slot`, `slot_sel`]
    \\ simp [Abbr `io0`, boot_first_once_al_def, is_bootload_ev_def, Abbr `ev_b`] \\ xsimpl
    \\ qx_genl_tac [`rv_e`, `rbs_e`, `cbs_e`, `sbs_e`, `sA_e`, `sB_e`, `inps_e`, `clim_e`, `wlim_e`, `evs_e`]
    \\ rpt strip_tac
    \\ map_every qexists_tac [`sA_e`, `sB_e`, `inps_e`, `clim_e`, `wlim_e`, `evs_e`]
    \\ simp [] \\ xsimpl)
  \\ (* Boot failure branch *)
  qabbrev_tac `ev_b = IO_event (ExtCall «bootload») [] (ZIP (REPLICATE 545 0w, 1w :: DROP 1 (REPLICATE 545 0w)))`
  \\ xlet `POSTv uv. W8ARRAY bbuf (1w :: DROP 1 (REPLICATE 545 0w)) * AIRLOCK_IO_EV io0 [ev_b]`
  >- (
    simp [AIRLOCK_IO_EV_def, Abbr `ev_b`, Abbr `io0`] \\ xffi
    \\ simp [airlock_ffi_part_def, airlock_ffi_names_def]
    \\ qmatch_goalsub_abbrev_tac `FFI_part st_e u_fn ns_l`
    \\ map_every qexists_tac [`REPLICATE 545 0w`, `emp`, `st_e`, `u_fn`, `ns_l`, `[]`]
    \\ unabbrev_all_tac
    \\ fs [boolTheory.DE_MORGAN_THM]
    \\ simp [cfHeapsBaseTheory.mk_ffi_next_def, decode_encode_airlock_io,
             ffi_bootload_def, airlock_ffi_part_def] \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xsimpl \\ fs [ml_translatorTheory.WORD_def])
  \\ xif \\ asm_exists_tac \\ fs []
  \\ xcon \\ xsimpl
  \\ map_every qexists_tac [`sA`, `sB`, `inps`, `clim`, `wlim`, `[ev_b]`]
  \\ simp [stop_after_err_al_def, event_is_err_al_def, boot_first_once_al_def, is_bootload_ev_def, Abbr `ev_b`, Abbr `io0`]
  \\ `REPLICATE 545 (0w:word8) = 0w :: REPLICATE 544 0w` by EVAL_TAC
  \\ pop_assum SUBST1_TAC \\ simp [listTheory.ZIP] \\ IF_CASES_TAC >- fs [] \\ xsimpl
QED

(* ---- 4. FFI Projection / Heap Split Theorems for cfMain ---- *)

Theorem airlock_parts_ok:
  ∀io. cfStore$parts_ok (airlock_ffi io) airlock_proj
Proof
  gen_tac
  \\ simp [cfStoreTheory.parts_ok_def, airlock_proj_def, airlock_ffi_def,
           ffiTheory.initial_ffi_state_def, airlock_ffi_part_def, airlock_ffi_names_def]
  \\ rpt conj_tac
  >- (qexists_tac `encode_airlock_io io` \\ rw [FUPDATE_LIST_THM, FLOOKUP_UPDATE])
  >- (rpt strip_tac \\ gvs [FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM, cfHeapsBaseTheory.mk_ffi_next_def,
                            decode_encode_airlock_io, AllCaseEqs(),
                            ffi_bootload_def, ffi_commit_def, ffi_al_recv64_def, ffi_al_send128_def])
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM, cfHeapsBaseTheory.mk_ffi_next_def,
          decode_encode_airlock_io, AllCaseEqs()]
  \\ (conj_tac >- (imp_res_tac ffi_airlock_lengths \\ simp [])
      \\ qexists_tac `s`
      \\ simp [airlock_ffi_oracle_def, FUPDATE_LIST_THM, fmap_eq_flookup, FLOOKUP_UPDATE] \\ rw [])
QED

Theorem airlock_io_split:
  ∀st2 io.
    st2.ffi = airlock_ffi io ⇒
    ∃h1 h2. SPLIT (st2heap airlock_proj st2) (h1, h2) ∧ AIRLOCK_IO_EV io [] h1
Proof
  rpt strip_tac
  \\ qabbrev_tac `ffip = FFI_part (encode_airlock_io io) (mk_ffi_next airlock_ffi_part)
                                  airlock_ffi_names []`
  \\ qexists_tac `{ffip}` \\ qexists_tac `st2heap airlock_proj st2 DIFF {ffip}`
  \\ conj_tac
  >- (`ffip ∈ st2heap airlock_proj st2` by
        (simp [cfStoreTheory.st2heap_def] \\ disj2_tac
         \\ simp [airlock_proj_def, cfStoreTheory.ffi2heap_def]
         \\ simp [GSYM airlock_proj_def, airlock_parts_ok]
         \\ rw [Abbr `ffip`, airlock_proj_def, airlock_ffi_def, airlock_ffi_names_def,
                ffiTheory.initial_ffi_state_def, FUPDATE_LIST_THM, FLOOKUP_UPDATE])
      \\ fs [set_sepTheory.SPLIT_def, IN_DISJOINT, EXTENSION] \\ metis_tac [])
  \\ simp [AIRLOCK_IO_EV_def, set_sepTheory.one_def, Abbr `ffip`]
QED

Theorem airlock_io_ffi_part_hprop:
  ∀bk bf out.
    FFI_part_hprop
      (SEP_EXISTS sA' sB' rest_inps clim' wlim' evs'.
        &(stop_after_err_al evs' ∧ boot_first_once_al evs') *
        AIRLOCK_IO_EV <| boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB';
                         inputs := rest_inps; outputs := out;
                         commit_limit := clim'; write_limit := wlim' |> evs')
Proof
  rpt gen_tac
  \\ ntac 6 (ho_match_mp_tac cfMainTheory.FFI_part_hprop_SEP_EXISTS \\ gen_tac)
  \\ simp [cfMainTheory.FFI_part_hprop_def, AIRLOCK_IO_EV_def, set_sepTheory.one_def,
           set_sepTheory.STAR_def, set_sepTheory.cond_def,
           set_sepTheory.SPLIT_def, set_sepTheory.emp_def]
  \\ rpt strip_tac \\ rveq \\ simp [] \\ metis_tac []
QED
