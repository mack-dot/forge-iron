(*
  Forge Reusable Runtime: Generic 64-Byte Binary Frame Specification & Total 2-FFI Oracle.

  Provides the fixed 64-byte wire framing (8 little-endian u64 lanes), round-trip
  bijection theorems, 64-byte chunking, polymorphic trace runner `frame64_run`,
  and total 2-FFI oracle (`recv64` / `send64`) shared by all M2+ kernels.
*)
Theory forge_frame64Spec
Ancestors
  words arithmetic list ffi cfHeapsBase semanticsProps evaluateProps
Libs
  preamble blastLib wordsLib

(* ---- 1. Fixed-Width LE64 & 64-Byte Frame Bijection ---- *)

Definition le64_decode_def:
  le64_decode (b0:word8) (b1:word8) (b2:word8) (b3:word8)
              (b4:word8) (b5:word8) (b6:word8) (b7:word8) : word64 =
    (w2w b0 : word64) ‖
    ((w2w b1 : word64) ≪ 8) ‖
    ((w2w b2 : word64) ≪ 16) ‖
    ((w2w b3 : word64) ≪ 24) ‖
    ((w2w b4 : word64) ≪ 32) ‖
    ((w2w b5 : word64) ≪ 40) ‖
    ((w2w b6 : word64) ≪ 48) ‖
    ((w2w b7 : word64) ≪ 56)
End

Definition le64_byte_def:
  le64_byte (w:word64) (i:num) : word8 = w2w (w ⋙ (8 * i))
End

Definition le64_encode_def:
  le64_encode (w:word64) : word8 list =
    [le64_byte w 0; le64_byte w 1; le64_byte w 2; le64_byte w 3;
     le64_byte w 4; le64_byte w 5; le64_byte w 6; le64_byte w 7]
End

Theorem le64_encode_length:
  ∀w. LENGTH (le64_encode w) = 8
Proof
  simp [le64_encode_def]
QED

Theorem le64_roundtrip:
  ∀w:word64.
    le64_decode (le64_byte w 0) (le64_byte w 1) (le64_byte w 2) (le64_byte w 3)
                (le64_byte w 4) (le64_byte w 5) (le64_byte w 6) (le64_byte w 7) = w
Proof
  simp [le64_decode_def, le64_byte_def] \\ blastLib.BBLAST_TAC
QED

Theorem le64_decode_encode_bytes:
  ∀b0 b1 b2 b3 b4 b5 b6 b7:word8.
    le64_encode (le64_decode b0 b1 b2 b3 b4 b5 b6 b7) =
    [b0; b1; b2; b3; b4; b5; b6; b7]
Proof
  simp [le64_encode_def, le64_decode_def, le64_byte_def]
  \\ rpt strip_tac \\ blastLib.BBLAST_TAC
QED

Datatype:
  frame64 = Frame64 word64 word64 word64 word64 word64 word64 word64 word64
End

Definition le64_at_def:
  le64_at (bs:word8 list) (off:num) : word64 =
    le64_decode (EL off bs) (EL (off + 1) bs) (EL (off + 2) bs) (EL (off + 3) bs)
                (EL (off + 4) bs) (EL (off + 5) bs) (EL (off + 6) bs) (EL (off + 7) bs)
End

Definition frame64_decode_def:
  frame64_decode (bs:word8 list) : frame64 =
    Frame64 (le64_at bs 0)  (le64_at bs 8)  (le64_at bs 16) (le64_at bs 24)
            (le64_at bs 32) (le64_at bs 40) (le64_at bs 48) (le64_at bs 56)
End

Definition frame64_encode_def:
  frame64_encode (Frame64 w0 w1 w2 w3 w4 w5 w6 w7) : word8 list =
    le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++
    le64_encode w4 ++ le64_encode w5 ++ le64_encode w6 ++ le64_encode w7
End

Theorem frame64_encode_length:
  ∀fr. LENGTH (frame64_encode fr) = 64
Proof
  Cases \\ simp [frame64_encode_def, le64_encode_length]
QED

Theorem frame64_roundtrip:
  ∀fr. frame64_decode (frame64_encode fr) = fr
Proof
  Cases
  \\ simp [frame64_decode_def, frame64_encode_def, le64_at_def, le64_encode_def,
           le64_roundtrip]
QED

Theorem frame64_decode_encode_bytes:
  ∀bs. LENGTH bs = 64 ⇒ frame64_encode (frame64_decode bs) = bs
Proof
  rpt strip_tac
  \\ `∀k. k + 8 ≤ LENGTH bs ⇒ le64_encode (le64_at bs k) = TAKE 8 (DROP k bs)` by (
       rpt strip_tac
       \\ simp [le64_at_def, le64_decode_encode_bytes]
       \\ irule LIST_EQ \\ simp [LENGTH_TAKE, LENGTH_DROP]
       \\ rpt strip_tac
       \\ `x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7` by decide_tac
       \\ rveq \\ simp [EL_TAKE, EL_DROP])
  \\ simp [frame64_decode_def, frame64_encode_def]
  \\ `TAKE 8 bs ++ TAKE 8 (DROP 8 bs) ++ TAKE 8 (DROP 16 bs) ++
      TAKE 8 (DROP 24 bs) ++ TAKE 8 (DROP 32 bs) ++ TAKE 8 (DROP 40 bs) ++
      TAKE 8 (DROP 48 bs) ++ TAKE 8 (DROP 56 bs) = bs` by (
       irule LIST_EQ \\ simp [LENGTH_TAKE, LENGTH_DROP]
       \\ rpt strip_tac
       \\ Cases_on `x < 8`  >- simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP]
       \\ Cases_on `x < 16` >- simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP]
       \\ Cases_on `x < 24` >- simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP]
       \\ Cases_on `x < 32` >- simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP]
       \\ Cases_on `x < 40` >- simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP]
       \\ Cases_on `x < 48` >- simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP]
       \\ Cases_on `x < 56` >- simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP]
       \\ simp [EL_APPEND1, EL_APPEND2, EL_TAKE, EL_DROP])
  \\ simp []
QED

(* ---- 2. 64-Byte Stream Chunking & Generic Trace Runner ---- *)

Definition chunks64_def:
  chunks64 (bs:word8 list) : (word8 list) list =
    if LENGTH bs < 64 then []
    else TAKE 64 bs :: chunks64 (DROP 64 bs)
Termination
  WF_REL_TAC `measure LENGTH` \\ simp []
End

Theorem chunks64_lt64:
  ∀bs. LENGTH bs < 64 ⇒ chunks64 bs = []
Proof
  rpt strip_tac \\ simp [Once chunks64_def]
QED

Theorem chunks64_cons:
  ∀f rest. LENGTH f = 64 ⇒ chunks64 (f ++ rest) = f :: chunks64 rest
Proof
  rpt strip_tac \\ simp [Once chunks64_def, TAKE_APPEND1, DROP_APPEND2]
QED

Theorem chunks64_every_len64:
  ∀bs. EVERY (λf. LENGTH f = 64) (chunks64 bs)
Proof
  ho_match_mp_tac chunks64_ind \\ rpt strip_tac
  \\ simp [Once chunks64_def] \\ IF_CASES_TAC \\ simp []
QED

Definition frame64_run_def:
  (frame64_run (step:'st -> frame64 -> 'st # frame64) (st:'st) [] = (st, [])) ∧
  (frame64_run step st (f::fs) =
    if LENGTH f = 64 then
      let (st', resp) = step st (frame64_decode f) in
      let (stf, outs) = frame64_run step st' fs in
        (stf, frame64_encode resp :: outs)
    else
      (st, []))
End

Definition limit_frames64_def:
  (limit_frames64 NONE xs = xs) ∧
  (limit_frames64 (SOME n) xs = TAKE (SUC n) xs)
End

(* ---- 3. Total 64-Byte 2-FFI Oracle (`recv64` / `send64`) ---- *)

Datatype:
  frame64_io = <|
    inputs      : (word8 list) list;
    outputs     : (word8 list) list;
    write_limit : num option
  |>
End

Definition ffi_recv64_def:
  ffi_recv64 (conf:word8 list) (bytes:word8 list) (io:frame64_io) =
    if LENGTH bytes < 65 then
      SOME (FFIreturn bytes io)
    else
      case io.inputs of
        [] => SOME (FFIreturn (1w :: DROP 1 bytes) io)
      | f::fs =>
          if LENGTH f = 64 then
            SOME (FFIreturn (0w :: f ++ DROP 65 bytes) (io with inputs := fs))
          else
            SOME (FFIreturn (1w :: DROP 1 bytes) io)
End

Definition ffi_send64_def:
  ffi_send64 (conf:word8 list) (bytes:word8 list) (io:frame64_io) =
    if LENGTH bytes < 65 then
      SOME (FFIreturn bytes io)
    else
      let frame = TAKE 64 (DROP 1 bytes) in
      case io.write_limit of
        NONE =>
          SOME (FFIreturn (0w :: DROP 1 bytes)
                          (io with outputs := io.outputs ++ [frame]))
      | SOME 0 =>
          SOME (FFIreturn (1w :: DROP 1 bytes)
                          (io with outputs := io.outputs ++ [frame]))
      | SOME (SUC n) =>
          SOME (FFIreturn (0w :: DROP 1 bytes)
                          (io with <| outputs := io.outputs ++ [frame];
                                      write_limit := SOME n |>))
End

Theorem ffi_recv64_length:
  ∀conf bytes io bytes' io'.
    ffi_recv64 conf bytes io = SOME (FFIreturn bytes' io') ⇒
    LENGTH bytes' = LENGTH bytes
Proof
  rpt strip_tac \\ gvs [ffi_recv64_def, AllCaseEqs()]
QED

Theorem ffi_send64_length:
  ∀conf bytes io bytes' io'.
    ffi_send64 conf bytes io = SOME (FFIreturn bytes' io') ⇒
    LENGTH bytes' = LENGTH bytes
Proof
  rpt strip_tac \\ gvs [ffi_send64_def, AllCaseEqs()]
QED

Definition encode_byte_list64_def:
  encode_byte_list64 (bs:word8 list) : ffi = List (MAP (Num o w2n) bs)
End

Theorem encode_byte_list64_11:
  ∀x y. encode_byte_list64 x = encode_byte_list64 y ⇔ x = y
Proof
  simp [encode_byte_list64_def]
  \\ Induct >- (Cases \\ simp [])
  \\ gen_tac \\ Cases \\ simp [w2n_11]
QED

Definition encode_opt_num64_def:
  (encode_opt_num64 NONE = Num 0) ∧
  (encode_opt_num64 (SOME n) = Cons (Num 1) (Num n))
End

Theorem encode_opt_num64_11:
  ∀x y. encode_opt_num64 x = encode_opt_num64 y ⇔ x = y
Proof
  Cases \\ Cases \\ simp [encode_opt_num64_def]
QED

Definition encode_frame64_io_def:
  encode_frame64_io (io:frame64_io) : ffi =
    Cons (List (MAP encode_byte_list64 io.inputs))
         (Cons (List (MAP encode_byte_list64 io.outputs))
               (encode_opt_num64 io.write_limit))
End

Theorem encode_frame64_io_11:
  ∀x y. encode_frame64_io x = encode_frame64_io y ⇔ x = y
Proof
  Cases \\ Cases \\ simp [encode_frame64_io_def, encode_opt_num64_11]
  \\ `∀a b. MAP encode_byte_list64 a = MAP encode_byte_list64 b ⇔ a = b` by
       (Induct >- (Cases \\ simp []) \\ gen_tac \\ Cases \\ simp [encode_byte_list64_11])
  \\ simp []
QED

Definition decode_frame64_io_def:
  decode_frame64_io f =
    if ∃io. encode_frame64_io io = f then SOME (@io. encode_frame64_io io = f)
    else NONE
End

Theorem decode_encode_frame64_io:
  ∀io. decode_frame64_io (encode_frame64_io io) = SOME io
Proof
  rw [decode_frame64_io_def, encode_frame64_io_11] \\ metis_tac []
QED

Definition frame64_ffi_part_def:
  frame64_ffi_part =
    (encode_frame64_io, decode_frame64_io,
     [(«recv64», ffi_recv64); («send64», ffi_send64)])
End

Definition frame64_ffi_oracle_def:
  frame64_ffi_oracle : frame64_io oracle =
    λname io conf bytes.
      if name = ExtCall «recv64» then
        case ffi_recv64 conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else if name = ExtCall «send64» then
        case ffi_send64 conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else
        Oracle_final FFI_failed
End

Definition frame64_ffi_def:
  frame64_ffi (io:frame64_io) : frame64_io ffi_state =
    initial_ffi_state frame64_ffi_oracle io
End

Definition frame64_proj_def:
  frame64_proj : frame64_io ffi_proj =
    ((λio. FEMPTY |++ [(«recv64», encode_frame64_io io); («send64», encode_frame64_io io)]),
     [([«recv64»; «send64»], mk_ffi_next frame64_ffi_part)])
End

Definition sent_frames64_of_def:
  (sent_frames64_of [] = []) ∧
  (sent_frames64_of (IO_event (ExtCall n) conf bs :: rest) =
    (if n = «send64» ∧ 65 ≤ LENGTH bs then [TAKE 64 (DROP 1 (MAP FST bs))] else [])
    ++ sent_frames64_of rest) ∧
  (sent_frames64_of (_ :: rest) = sent_frames64_of rest)
End

Theorem sent_frames64_of_append:
  ∀xs ys. sent_frames64_of (xs ++ ys) = sent_frames64_of xs ++ sent_frames64_of ys
Proof
  Induct \\ simp [sent_frames64_of_def]
  \\ Cases \\ simp [sent_frames64_of_def]
  \\ Cases_on `f` \\ simp [sent_frames64_of_def]
QED

Theorem call_FFI_frame64_outputs:
  ∀st st'.
    call_FFI_rel st st' ∧ st.oracle = frame64_ffi_oracle ⇒
    st'.oracle = frame64_ffi_oracle ∧
    st'.ffi_state.outputs = st.ffi_state.outputs ++
      sent_frames64_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
Proof
  rw [evaluatePropsTheory.call_FFI_rel_def]
  \\ qpat_x_assum `call_FFI _ _ _ _ = _` mp_tac
  \\ simp [ffiTheory.call_FFI_def, AllCaseEqs()]
  \\ strip_tac \\ gvs [sent_frames64_of_def, DROP_LENGTH_APPEND]
  \\ Cases_on `n`
  \\ gvs [frame64_ffi_oracle_def, AllCaseEqs(), ffi_recv64_def, ffi_send64_def,
          sent_frames64_of_def, MAP_ZIP]
QED

Theorem frame64_ffi_outputs_eq_sent_frames:
  ∀io st'.
    io.outputs = [] ∧
    call_FFI_rel^* (frame64_ffi io) st' ⇒
    st'.ffi_state.outputs = sent_frames64_of st'.io_events
Proof
  `∀a b c.
     sent_frames64_of (DROP (LENGTH a) (a ++ b)) ++
     sent_frames64_of (DROP (LENGTH (a ++ b)) ((a ++ b) ++ c)) =
     sent_frames64_of (DROP (LENGTH a) ((a ++ b) ++ c))` by (
       Induct_on `a` >- simp [DROP_LENGTH_APPEND, sent_frames64_of_append] \\ fs [])
  \\ `∀st st'. call_FFI_rel^* st st' ⇒ st.oracle = frame64_ffi_oracle ⇒
     st'.oracle = frame64_ffi_oracle ∧
     st'.ffi_state.outputs = st.ffi_state.outputs ++
       sent_frames64_of (DROP (LENGTH st.io_events) st'.io_events) ∧
     st.io_events ≼ st'.io_events` by (
       ho_match_mp_tac relationTheory.RTC_INDUCT \\ rw []
       >- simp [sent_frames64_of_def]
       \\ drule_all call_FFI_frame64_outputs \\ strip_tac \\ fs []
       \\ `st.io_events ≼ st''.io_events` by metis_tac [IS_PREFIX_TRANS]
       \\ simp []
       \\ qpat_x_assum `st.io_events ≼ st'.io_events` mp_tac
       \\ qpat_x_assum `st'.io_events ≼ st''.io_events` mp_tac
       \\ simp [IS_PREFIX_APPEND] \\ rpt strip_tac \\ rveq
       \\ first_x_assum (qspecl_then [`st.io_events`, `l'`, `l`] mp_tac) \\ simp [])
  \\ rw [frame64_ffi_def, ffiTheory.initial_ffi_state_def]
  \\ first_x_assum drule \\ simp []
QED
