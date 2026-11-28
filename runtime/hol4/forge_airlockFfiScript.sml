(*
  Forge Milestone 3 Reusable Runtime: 128-Byte Response Frames & Total 4-FFI
  Crypto-Airlock Oracle (`bootload`, `commit`, `recv64`, `send128`).

  Provides:
    1. Fixed 128-byte LE64 response frame (`frame128`) & round-trip bijections.
    2. Generic crash-atomic execution trace (`airlock_exec` / `airlock_full_run`).
    3. Total 4-FFI CakeML oracle (`bootload` 545B, `commit` 258B, `recv64` 65B,
       `send128` 129B) with injective encoding and event-stream output extraction.
*)
Theory forge_airlockFfi
Ancestors
  words arithmetic list rich_list ffi cfHeapsBase semanticsProps evaluateProps
  forge_frame64Spec
Libs
  preamble blastLib wordsLib

(* ---- 1. 128-Byte Response Frame & Byte/Word64 Bijections ---- *)

Datatype:
  frame128 = Frame128
    word64 word64 word64 word64 word64 word64 word64 word64
    word64 word64 word64 word64 word64 word64 word64 word64
End

Definition le64_take_def:
  (le64_take (b0::b1::b2::b3::b4::b5::b6::b7::rest) =
     (le64_decode b0 b1 b2 b3 b4 b5 b6 b7, rest)) ∧
  (le64_take _ = (0w, []))
End

Definition frame128_encode_def:
  frame128_encode (Frame128 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) : word8 list =
    le64_encode w0  ++ le64_encode w1  ++ le64_encode w2  ++ le64_encode w3  ++
    le64_encode w4  ++ le64_encode w5  ++ le64_encode w6  ++ le64_encode w7  ++
    le64_encode w8  ++ le64_encode w9  ++ le64_encode w10 ++ le64_encode w11 ++
    le64_encode w12 ++ le64_encode w13 ++ le64_encode w14 ++ le64_encode w15
End

Definition frame128_decode_def:
  frame128_decode (bs:word8 list) : frame128 =
    let (w0,  r0)  = le64_take bs  in let (w1,  r1)  = le64_take r0  in
    let (w2,  r2)  = le64_take r1  in let (w3,  r3)  = le64_take r2  in
    let (w4,  r4)  = le64_take r3  in let (w5,  r5)  = le64_take r4  in
    let (w6,  r6)  = le64_take r5  in let (w7,  r7)  = le64_take r6  in
    let (w8,  r8)  = le64_take r7  in let (w9,  r9)  = le64_take r8  in
    let (w10, r10) = le64_take r9  in let (w11, r11) = le64_take r10 in
    let (w12, r12) = le64_take r11 in let (w13, r13) = le64_take r12 in
    let (w14, r14) = le64_take r13 in let (w15, _ )  = le64_take r14 in
      Frame128 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
End

Theorem le64_take_encode:
  ∀w rest. le64_take (le64_encode w ++ rest) = (w, rest)
Proof
  rpt gen_tac
  \\ simp [le64_encode_def, le64_take_def, le64_decode_def, le64_byte_def]
  \\ blastLib.BBLAST_TAC
QED

Theorem le64_take_encode_nil:
  ∀w. le64_take (le64_encode w) = (w, [])
Proof
  gen_tac \\ mp_tac (Q.SPECL [`w`, `[]`] le64_take_encode) \\ simp []
QED

Theorem le64_take_length8[local]:
  ∀bs. LENGTH bs ≥ 8 ⇒
    ∃w r. le64_take bs = (w, r) ∧ bs = le64_encode w ++ r ∧ LENGTH r = LENGTH bs − 8
Proof
  rpt strip_tac
  \\ Cases_on `bs` \\ fs [] \\ Cases_on `t` \\ fs [] \\ Cases_on `t'` \\ fs []
  \\ Cases_on `t` \\ fs [] \\ Cases_on `t'` \\ fs [] \\ Cases_on `t` \\ fs []
  \\ Cases_on `t'` \\ fs [] \\ Cases_on `t` \\ fs []
  \\ simp [le64_take_def, le64_encode_def]
  \\ qabbrev_tac `w = le64_decode h h' h'' h''' h'''' h''''' h'''''' h'''''''`
  \\ `le64_byte w 0 = h ∧ le64_byte w 1 = h' ∧ le64_byte w 2 = h'' ∧ le64_byte w 3 = h''' ∧
      le64_byte w 4 = h'''' ∧ le64_byte w 5 = h''''' ∧ le64_byte w 6 = h'''''' ∧ le64_byte w 7 = h'''''''`
     by (simp [Abbr `w`, le64_decode_def, le64_byte_def] \\ rpt conj_tac \\ blastLib.BBLAST_TAC)
  \\ simp []
QED

Theorem frame128_encode_length:
  ∀fr. LENGTH (frame128_encode fr) = 128
Proof
  Cases \\ simp [frame128_encode_def, le64_encode_def]
QED

Theorem frame128_roundtrip:
  ∀fr. frame128_decode (frame128_encode fr) = fr
Proof
  Cases
  \\ simp [Excl "APPEND_ASSOC", frame128_encode_def, frame128_decode_def,
           GSYM APPEND_ASSOC, le64_take_encode, le64_take_encode_nil]
QED

Theorem le64_split8[local]:
  ∀n bs. LENGTH bs = n + 8 ⇒ ∃w r. bs = le64_encode w ++ r ∧ LENGTH r = n
Proof
  rpt strip_tac \\ `LENGTH bs ≥ 8` by decide_tac
  \\ drule le64_take_length8 \\ strip_tac \\ qexistsl_tac [`w`, `r`] \\ simp []
QED

Theorem le64_split32[local]:
  ∀n bs. LENGTH bs = n + 32 ⇒
    ∃w0 w1 w2 w3 r.
      bs = le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ r ∧
      LENGTH r = n
Proof
  rpt strip_tac
  \\ qspecl_then [`n + 24`, `bs`] mp_tac le64_split8 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `bs = le64_encode a0 ++ s0`
  \\ qspecl_then [`n + 16`, `s0`] mp_tac le64_split8 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `s0 = le64_encode a1 ++ s1`
  \\ qspecl_then [`n + 8`,  `s1`] mp_tac le64_split8 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `s1 = le64_encode a2 ++ s2`
  \\ qspecl_then [`n`,      `s2`] mp_tac le64_split8 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `s2 = le64_encode a3 ++ s3`
  \\ qexistsl_tac [`a0`, `a1`, `a2`, `a3`, `s3`]
  \\ rveq \\ simp [Excl "APPEND_ASSOC", GSYM APPEND_ASSOC]
QED

Theorem frame128_decode_encode_bytes:
  ∀bs. LENGTH bs = 128 ⇒ frame128_encode (frame128_decode bs) = bs
Proof
  rpt strip_tac
  \\ qspecl_then [`96`, `bs`] mp_tac le64_split32 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `bs = le64_encode a0 ++ le64_encode a1 ++ le64_encode a2 ++ le64_encode a3 ++ s0`
  \\ qspecl_then [`64`, `s0`] mp_tac le64_split32 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `s0 = le64_encode b0 ++ le64_encode b1 ++ le64_encode b2 ++ le64_encode b3 ++ s1`
  \\ qspecl_then [`32`, `s1`] mp_tac le64_split32 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `s1 = le64_encode c0 ++ le64_encode c1 ++ le64_encode c2 ++ le64_encode c3 ++ s2`
  \\ qspecl_then [`0`,  `s2`] mp_tac le64_split32 \\ impl_tac >- decide_tac
  \\ strip_tac \\ rename1 `s2 = le64_encode d0 ++ le64_encode d1 ++ le64_encode d2 ++ le64_encode d3 ++ s3`
  \\ `s3 = []` by fs [LENGTH_NIL] \\ rveq
  \\ qabbrev_tac `fr = Frame128 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3`
  \\ `le64_encode a0 ++ le64_encode a1 ++ le64_encode a2 ++ le64_encode a3 ++
      (le64_encode b0 ++ le64_encode b1 ++ le64_encode b2 ++ le64_encode b3 ++
      (le64_encode c0 ++ le64_encode c1 ++ le64_encode c2 ++ le64_encode c3 ++
      (le64_encode d0 ++ le64_encode d1 ++ le64_encode d2 ++ le64_encode d3 ++ []))) =
      frame128_encode fr`
     by simp [Abbr `fr`, Excl "APPEND_ASSOC", frame128_encode_def, GSYM APPEND_ASSOC]
  \\ pop_assum SUBST1_TAC \\ simp [frame128_roundtrip]
QED

(* ---- 2. Generic Crash-Atomic Execution Trace ---- *)

Definition pad512_def:
  pad512 (bs:word8 list) : word8 list =
    TAKE 512 (bs ++ REPLICATE 512 0w)
End

Theorem LENGTH_pad512:
  ∀bs. LENGTH (pad512 bs) = 512
Proof
  gen_tac \\ simp [pad512_def]
QED

Definition airlock_exec_def:
  (airlock_exec (stepf:word8 list -> 'st -> frame64 -> 'st # frame128 # bool)
                (key:word8 list) (st:'st) [] (clim:num option) (wlim:num option) = (st, [])) ∧
  (airlock_exec stepf key st (f::fs) clim wlim =
     if LENGTH f = 64 then
       let (st', resp, dc) = stepf key st (frame64_decode f) in
       if dc then
         case clim of
           SOME 0 => (st, [])
         | SOME (SUC c) =>
             (case wlim of
                NONE =>
                  let (stf, outs) = airlock_exec stepf key st' fs (SOME c) NONE in
                    (stf, frame128_encode resp :: outs)
              | SOME 0 => (st', [frame128_encode resp])
              | SOME (SUC w) =>
                  let (stf, outs) = airlock_exec stepf key st' fs (SOME c) (SOME w) in
                    (stf, frame128_encode resp :: outs))
         | NONE =>
             (case wlim of
                NONE =>
                  let (stf, outs) = airlock_exec stepf key st' fs NONE NONE in
                    (stf, frame128_encode resp :: outs)
              | SOME 0 => (st', [frame128_encode resp])
              | SOME (SUC w) =>
                  let (stf, outs) = airlock_exec stepf key st' fs NONE (SOME w) in
                    (stf, frame128_encode resp :: outs))
       else
         case wlim of
           NONE =>
             let (stf, outs) = airlock_exec stepf key st' fs clim NONE in
               (stf, frame128_encode resp :: outs)
         | SOME 0 => (st', [frame128_encode resp])
         | SOME (SUC w) =>
             let (stf, outs) = airlock_exec stepf key st' fs clim (SOME w) in
               (stf, frame128_encode resp :: outs)
     else (st, []))
End

Theorem airlock_exec_prefix_none:
  ∀stepf inps key st clim wlim.
    SND (airlock_exec stepf key st inps clim wlim) ≼
      SND (airlock_exec stepf key st inps NONE NONE)
Proof
  gen_tac \\ Induct_on `inps`
  >- simp [airlock_exec_def]
  \\ rpt strip_tac \\ simp [airlock_exec_def]
  \\ Cases_on `LENGTH h = 64` \\ simp []
  \\ Cases_on `stepf key st (frame64_decode h)` \\ Cases_on `r` \\ simp []
  \\ Cases_on `airlock_exec stepf key q inps NONE NONE` \\ simp []
  \\ Cases_on `r'` \\ simp []
  >- (Cases_on `clim` \\ simp []
      >- (Cases_on `wlim` \\ simp [] \\ Cases_on `x` \\ simp []
          \\ Cases_on `airlock_exec stepf key q inps NONE (SOME n)` \\ simp []
          \\ first_x_assum (qspecl_then [`key`, `q`, `NONE`, `SOME n`] mp_tac) \\ simp [])
      \\ Cases_on `x` \\ simp []
      \\ Cases_on `wlim` \\ simp []
      >- (Cases_on `airlock_exec stepf key q inps (SOME n) NONE` \\ simp []
          \\ first_x_assum (qspecl_then [`key`, `q`, `SOME n`, `NONE`] mp_tac) \\ simp [])
      \\ Cases_on `x` \\ simp []
      \\ Cases_on `airlock_exec stepf key q inps (SOME n) (SOME n')` \\ simp []
      \\ first_x_assum (qspecl_then [`key`, `q`, `SOME n`, `SOME n'`] mp_tac) \\ simp [])
  \\ Cases_on `wlim` \\ simp []
  >- (Cases_on `airlock_exec stepf key q inps clim NONE` \\ simp []
      \\ first_x_assum (qspecl_then [`key`, `q`, `clim`, `NONE`] mp_tac) \\ simp [])
  \\ Cases_on `x` \\ simp []
  \\ Cases_on `airlock_exec stepf key q inps clim (SOME n)` \\ simp []
  \\ first_x_assum (qspecl_then [`key`, `q`, `clim`, `SOME n`] mp_tac) \\ simp []
QED

(* ---- 3. Total 4-FFI Oracle (`bootload`, `commit`, `recv64`, `send128`) ---- *)

Datatype:
  airlock_io = <|
    boot_key     : word8 list;
    boot_fail    : bool;
    slotA        : word8 list;
    slotB        : word8 list;
    inputs       : (word8 list) list;
    outputs      : (word8 list) list;
    commit_limit : num option;
    write_limit  : num option
  |>
End

Definition ffi_bootload_def:
  ffi_bootload (conf:word8 list) (bytes:word8 list) (io:airlock_io) =
    if LENGTH bytes < 545 then
      SOME (FFIreturn bytes io)
    else if io.boot_fail ∨ LENGTH io.boot_key ≠ 32 ∨ LENGTH io.slotA ≠ 256 ∨ LENGTH io.slotB ≠ 256 then
      SOME (FFIreturn (1w :: DROP 1 bytes) io)
    else
      SOME (FFIreturn (0w :: io.boot_key ++ io.slotA ++ io.slotB ++ DROP 545 bytes) io)
End

Definition ffi_commit_def:
  ffi_commit (conf:word8 list) (bytes:word8 list) (io:airlock_io) =
    if LENGTH bytes < 258 then
      SOME (FFIreturn bytes io)
    else
      let sel = EL 1 bytes in
      let rec = TAKE 256 (DROP 2 bytes) in
      let io_upd = if (sel && 1w) = 0w then io with slotA := rec else io with slotB := rec in
      case io.commit_limit of
        NONE => SOME (FFIreturn (0w :: DROP 1 bytes) io_upd)
      | SOME 0 => SOME (FFIreturn (1w :: DROP 1 bytes) io)
      | SOME (SUC c) => SOME (FFIreturn (0w :: DROP 1 bytes) (io_upd with commit_limit := SOME c))
End

Definition ffi_al_recv64_def:
  ffi_al_recv64 (conf:word8 list) (bytes:word8 list) (io:airlock_io) =
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

Definition ffi_al_send128_def:
  ffi_al_send128 (conf:word8 list) (bytes:word8 list) (io:airlock_io) =
    if LENGTH bytes < 129 then
      SOME (FFIreturn bytes io)
    else
      let frame = TAKE 128 (DROP 1 bytes) in
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

Theorem ffi_airlock_lengths:
  (∀conf bytes io bytes' io'.
     ffi_bootload conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (∀conf bytes io bytes' io'.
     ffi_commit conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (∀conf bytes io bytes' io'.
     ffi_al_recv64 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (∀conf bytes io bytes' io'.
     ffi_al_send128 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes)
Proof
  rpt conj_tac \\ rpt strip_tac
  \\ gvs [ffi_bootload_def, ffi_commit_def, ffi_al_recv64_def, ffi_al_send128_def, AllCaseEqs()]
QED

Definition encode_bool_ffi_def:
  encode_bool_ffi (b:bool) : ffi = Num (if b then 1 else 0)
End

Definition encode_airlock_io_def:
  encode_airlock_io (io:airlock_io) : ffi =
    Cons (encode_byte_list64 io.boot_key)
      (Cons (encode_bool_ffi io.boot_fail)
        (Cons (encode_byte_list64 io.slotA)
          (Cons (encode_byte_list64 io.slotB)
            (Cons (List (MAP encode_byte_list64 io.inputs))
              (Cons (List (MAP encode_byte_list64 io.outputs))
                (Cons (encode_opt_num64 io.commit_limit)
                      (encode_opt_num64 io.write_limit)))))))
End

Theorem encode_airlock_io_11:
  ∀x y. encode_airlock_io x = encode_airlock_io y ⇔ x = y
Proof
  Cases \\ Cases
  \\ simp [encode_airlock_io_def, encode_byte_list64_11, encode_opt_num64_11, encode_bool_ffi_def]
  \\ `∀a b. MAP encode_byte_list64 a = MAP encode_byte_list64 b ⇔ a = b` by
       (Induct >- (Cases \\ simp []) \\ gen_tac \\ Cases \\ simp [encode_byte_list64_11])
  \\ Cases_on `b` \\ Cases_on `b'` \\ simp []
QED

Definition decode_airlock_io_def:
  decode_airlock_io f =
    if ∃io. encode_airlock_io io = f then SOME (@io. encode_airlock_io io = f)
    else NONE
End

Theorem decode_encode_airlock_io:
  ∀io. decode_airlock_io (encode_airlock_io io) = SOME io
Proof
  rw [decode_airlock_io_def, encode_airlock_io_11] \\ metis_tac []
QED

Definition airlock_ffi_names_def:
  airlock_ffi_names : mlstring list = [«bootload»; «commit»; «recv64»; «send128»]
End

Definition airlock_ffi_part_def:
  airlock_ffi_part =
    (encode_airlock_io, decode_airlock_io,
     [(«bootload», ffi_bootload);
      («commit»,   ffi_commit);
      («recv64»,   ffi_al_recv64);
      («send128»,  ffi_al_send128)])
End

Definition airlock_ffi_oracle_def:
  airlock_ffi_oracle : airlock_io oracle =
    λname io conf bytes.
      if name = ExtCall «bootload» then
        case ffi_bootload conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else if name = ExtCall «commit» then
        case ffi_commit conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else if name = ExtCall «recv64» then
        case ffi_al_recv64 conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else if name = ExtCall «send128» then
        case ffi_al_send128 conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else
        Oracle_final FFI_failed
End

Definition airlock_ffi_def:
  airlock_ffi (io:airlock_io) : airlock_io ffi_state =
    initial_ffi_state airlock_ffi_oracle io
End

Definition airlock_proj_def:
  airlock_proj : airlock_io ffi_proj =
    ((λio. FEMPTY |++ [(«bootload», encode_airlock_io io);
                       («commit»,   encode_airlock_io io);
                       («recv64»,   encode_airlock_io io);
                       («send128»,  encode_airlock_io io)]),
     [(airlock_ffi_names, mk_ffi_next airlock_ffi_part)])
End

(* ---- 4. Event-Stream Extraction (Sent 128B Frames & Error Termination) ---- *)

Definition sent_frames128_of_def:
  (sent_frames128_of [] = []) ∧
  (sent_frames128_of (IO_event (ExtCall n) conf bs :: rest) =
    (if n = «send128» ∧ 129 ≤ LENGTH bs then [TAKE 128 (DROP 1 (MAP FST bs))] else [])
    ++ sent_frames128_of rest) ∧
  (sent_frames128_of (_ :: rest) = sent_frames128_of rest)
End

Theorem sent_frames128_of_append:
  ∀xs ys. sent_frames128_of (xs ++ ys) = sent_frames128_of xs ++ sent_frames128_of ys
Proof
  Induct \\ simp [sent_frames128_of_def]
  \\ Cases \\ simp [sent_frames128_of_def]
  \\ Cases_on `f` \\ simp [sent_frames128_of_def]
QED

Theorem call_FFI_airlock_outputs:
  ∀st st'.
    call_FFI_rel st st' ∧ st.oracle = airlock_ffi_oracle ⇒
    st'.oracle = airlock_ffi_oracle ∧
    st'.ffi_state.outputs = st.ffi_state.outputs ++
      sent_frames128_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
Proof
  rw [evaluatePropsTheory.call_FFI_rel_def]
  \\ qpat_x_assum `call_FFI _ _ _ _ = _` mp_tac
  \\ simp [ffiTheory.call_FFI_def, AllCaseEqs()]
  \\ strip_tac \\ gvs [sent_frames128_of_def, DROP_LENGTH_APPEND]
  \\ Cases_on `n`
  \\ gvs [airlock_ffi_oracle_def, AllCaseEqs(),
          ffi_bootload_def, ffi_commit_def, ffi_al_recv64_def, ffi_al_send128_def,
          sent_frames128_of_def, MAP_ZIP]
  \\ rw []
QED

Theorem airlock_ffi_outputs_eq_sent_frames:
  ∀io st'.
    io.outputs = [] ∧
    call_FFI_rel^* (airlock_ffi io) st' ⇒
    st'.ffi_state.outputs = sent_frames128_of st'.io_events
Proof
  `∀a b c.
     sent_frames128_of (DROP (LENGTH a) (a ++ b)) ++
     sent_frames128_of (DROP (LENGTH (a ++ b)) ((a ++ b) ++ c)) =
     sent_frames128_of (DROP (LENGTH a) ((a ++ b) ++ c))` by (
       Induct_on `a` >- simp [DROP_LENGTH_APPEND, sent_frames128_of_append] \\ fs [])
  \\ `∀st st'. call_FFI_rel^* st st' ⇒ st.oracle = airlock_ffi_oracle ⇒
     st'.oracle = airlock_ffi_oracle ∧
     st'.ffi_state.outputs = st.ffi_state.outputs ++
       sent_frames128_of (DROP (LENGTH st.io_events) st'.io_events) ∧
     st.io_events ≼ st'.io_events` by (
       ho_match_mp_tac relationTheory.RTC_INDUCT \\ rw []
       >- simp [sent_frames128_of_def]
       \\ drule_all call_FFI_airlock_outputs \\ strip_tac \\ fs []
       \\ `st.io_events ≼ st''.io_events` by metis_tac [IS_PREFIX_TRANS]
       \\ simp []
       \\ qpat_x_assum `st.io_events ≼ st'.io_events` mp_tac
       \\ qpat_x_assum `st'.io_events ≼ st''.io_events` mp_tac
       \\ simp [IS_PREFIX_APPEND] \\ rpt strip_tac \\ rveq
       \\ first_x_assum (qspecl_then [`st.io_events`, `l'`, `l`] mp_tac) \\ simp [])
  \\ rw [airlock_ffi_def, ffiTheory.initial_ffi_state_def]
  \\ first_x_assum drule \\ simp []
QED
