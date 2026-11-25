(*
  Forge Milestone 1: Trusted Pure Counter Specification (SHA-256 Pinned by Gate).

  Contains:
    - Fixed-width little-endian u64 framing (le64_decode, le64_encode, frame16_decode, frame16_encode)
    - Byte-stream 16-byte chunking (chunks16)
    - Pure counter transition & conservation theorems (cap_val, counter_step, counter_run)
    - Total 2-FFI oracle (recv16 / send16) modeling arbitrary partial/EOF/write-error schedules
*)
Theory forge_counterSpec
Ancestors
  words arithmetic list ffi cfHeapsBase semanticsProps evaluateProps
Libs
  preamble blastLib wordsLib

(* ---- Fixed-width little-endian u64 framing ---- *)

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

Definition frame16_decode_def:
  frame16_decode (f:word8 list) : word64 # word64 =
    (le64_decode (EL 0 f) (EL 1 f) (EL 2 f) (EL 3 f)
                 (EL 4 f) (EL 5 f) (EL 6 f) (EL 7 f),
     le64_decode (EL 8 f) (EL 9 f) (EL 10 f) (EL 11 f)
                 (EL 12 f) (EL 13 f) (EL 14 f) (EL 15 f))
End

Definition frame16_encode_def:
  frame16_encode (tag:word64) (seq:word64) : word8 list =
    le64_encode tag ++ le64_encode seq
End

Theorem frame16_encode_length:
  ∀tag seq. LENGTH (frame16_encode tag seq) = 16
Proof
  simp [frame16_encode_def, le64_encode_length]
QED

(* ---- Byte-stream 16-byte chunking ---- *)

Definition chunks16_def:
  chunks16 (bs:word8 list) : (word8 list) list =
    if LENGTH bs < 16 then []
    else TAKE 16 bs :: chunks16 (DROP 16 bs)
Termination
  WF_REL_TAC `measure LENGTH` \\ simp []
End

Theorem chunks16_lt16:
  ∀bs. LENGTH bs < 16 ⇒ chunks16 bs = []
Proof
  rpt strip_tac \\ simp [Once chunks16_def]
QED

Theorem chunks16_cons:
  ∀f rest. LENGTH f = 16 ⇒ chunks16 (f ++ rest) = f :: chunks16 rest
Proof
  rpt strip_tac \\ simp [Once chunks16_def, TAKE_APPEND1, DROP_APPEND2]
QED

Theorem chunks16_every_len16:
  ∀bs. EVERY (λf. LENGTH f = 16) (chunks16 bs)
Proof
  ho_match_mp_tac chunks16_ind \\ rpt strip_tac
  \\ simp [Once chunks16_def]
  \\ IF_CASES_TAC \\ simp []
QED

(* ---- Pure counter transition & conservation invariants ---- *)

Definition cap_val_def:
  cap_val : word64 = 10000w
End

Definition counter_step_def:
  counter_step (seq:word64) (spent:word64) (req_seq:word64) (amount:word64) =
    if seq ≠ 0xFFFFFFFFFFFFFFFFw ∧ req_seq = seq + 1w ∧ amount ≤₊ cap_val − spent then
      (seq + 1w, spent + amount, 1w:word64, seq + 1w)
    else
      (seq, spent, 0w:word64, seq)
End

Theorem counter_step_preserves_cap:
  ∀seq spent req_seq amount seq' spent' ok out_seq.
    spent ≤₊ cap_val ∧
    counter_step seq spent req_seq amount = (seq', spent', ok, out_seq) ⇒
    spent' ≤₊ cap_val
Proof
  rw [counter_step_def, cap_val_def] \\ blastLib.FULL_BBLAST_TAC
QED

Theorem counter_step_no_overflow:
  ∀seq spent req_seq amount seq' spent' out_seq.
    spent ≤₊ cap_val ∧
    counter_step seq spent req_seq amount = (seq', spent', 1w, out_seq) ⇒
    w2n spent' = w2n spent + w2n amount ∧
    w2n spent' ≤ w2n cap_val ∧
    w2n seq' = w2n seq + 1 ∧
    out_seq = seq'
Proof
  rpt gen_tac \\ disch_then strip_assume_tac
  \\ qpat_x_assum `counter_step _ _ _ _ = _` mp_tac
  \\ simp [counter_step_def, cap_val_def]
  \\ IF_CASES_TAC \\ simp []
  \\ rpt strip_tac \\ rveq
  \\ `spent ≤₊ (10000w:word64)` by fs [cap_val_def]
  \\ `w2n spent ≤ 10000` by fs [WORD_LS]
  \\ `w2n ((10000w:word64) - spent) = 10000 - w2n spent` by simp [word_sub_w2n]
  \\ `w2n amount ≤ 10000 - w2n spent` by fs [WORD_LS]
  \\ `w2n seq < 18446744073709551616` by
       (assume_tac (Q.ISPEC `seq:word64` w2n_lt) \\ fs [dimword_64])
  \\ `w2n seq ≠ 18446744073709551615` by
       (strip_tac \\ `seq = 0xFFFFFFFFFFFFFFFFw` by (Cases_on `seq` \\ fs [dimword_64]) \\ fs [])
  \\ simp [cap_val_def, word_add_def, w2n_n2w, dimword_64]
QED

Theorem counter_step_reject_unchanged:
  ∀seq spent req_seq amount seq' spent' out_seq.
    counter_step seq spent req_seq amount = (seq', spent', 0w, out_seq) ⇒
    seq' = seq ∧ spent' = spent ∧ out_seq = seq
Proof
  rw [counter_step_def]
QED

Theorem counter_step_overflow_attack_rejected:
  ∀seq spent.
    spent ≤₊ cap_val ⇒
    counter_step seq spent (seq + 1w) 0xFFFFFFFFFFFFFFFFw = (seq, spent, 0w, seq)
Proof
  rw [counter_step_def, cap_val_def] \\ blastLib.FULL_BBLAST_TAC
QED

Theorem counter_step_replay_rejected:
  ∀seq spent amount.
    counter_step seq spent seq amount = (seq, spent, 0w, seq)
Proof
  rw [counter_step_def] \\ blastLib.FULL_BBLAST_TAC
QED

Theorem counter_step_gap_rejected:
  ∀seq spent amount.
    counter_step seq spent (seq + 2w) amount = (seq, spent, 0w, seq)
Proof
  rw [counter_step_def] \\ blastLib.FULL_BBLAST_TAC
QED

(* ---- Multi-frame trace specification ---- *)

Definition counter_run_def:
  (counter_run (seq:word64) (spent:word64) [] = (seq, spent, [])) ∧
  (counter_run seq spent (f::fs) =
    if LENGTH f = 16 then
      let (req_seq, amount) = frame16_decode f in
      let (seq', spent', ok, out_seq) = counter_step seq spent req_seq amount in
      let (seqf, spentf, outs) = counter_run seq' spent' fs in
        (seqf, spentf, frame16_encode ok out_seq :: outs)
    else
      (seq, spent, []))
End

Theorem counter_run_preserves_cap:
  ∀fs seq spent seqf spentf outs.
    spent ≤₊ cap_val ∧
    counter_run seq spent fs = (seqf, spentf, outs) ⇒
    spentf ≤₊ cap_val ∧ w2n spentf ≤ 10000
Proof
  Induct_on `fs`
  >- (rpt strip_tac \\ gvs [counter_run_def, cap_val_def, WORD_LS])
  \\ rpt gen_tac \\ disch_then strip_assume_tac
  \\ qpat_x_assum `counter_run _ _ _ = _` mp_tac
  \\ simp [counter_run_def]
  \\ Cases_on `LENGTH h = 16` \\ simp []
  >- (
    pairarg_tac \\ simp []
    \\ pairarg_tac \\ simp []
    \\ pairarg_tac \\ simp []
    \\ strip_tac \\ rveq
    \\ drule_all counter_step_preserves_cap \\ strip_tac
    \\ first_x_assum drule_all \\ simp [])
  \\ strip_tac \\ rveq \\ fs [cap_val_def, WORD_LS]
QED

Theorem counter_run_take_prefix:
  ∀fs n seq spent.
    SND (SND (counter_run seq spent (TAKE n fs))) ≼ SND (SND (counter_run seq spent fs))
Proof
  Induct_on `fs` \\ simp [counter_run_def]
  \\ rpt strip_tac
  \\ Cases_on `n` \\ simp [counter_run_def]
  \\ Cases_on `LENGTH h = 16` \\ simp []
  \\ rpt (pairarg_tac \\ simp [])
  \\ first_x_assum (qspecl_then [`n'`, `seq'`, `spent'`] mp_tac) \\ simp []
QED

Theorem FLAT_prefix:
  ∀xs ys. xs ≼ ys ⇒ FLAT xs ≼ FLAT ys
Proof
  rw [IS_PREFIX_APPEND] \\ simp [FLAT_APPEND, IS_PREFIX_APPEND]
QED

(* ---- Total 2-FFI oracle for recv16 and send16 ---- *)

Datatype:
  counter_io = <|
    inputs      : (word8 list) list;
    outputs     : (word8 list) list;
    write_limit : num option
  |>
End

Definition ffi_recv16_def:
  ffi_recv16 (conf:word8 list) (bytes:word8 list) (io:counter_io) =
    if LENGTH bytes < 17 then
      SOME (FFIreturn bytes io)
    else
      case io.inputs of
        [] => SOME (FFIreturn (1w :: DROP 1 bytes) io)
      | f::fs =>
          if LENGTH f = 16 then
            SOME (FFIreturn (0w :: f ++ DROP 17 bytes) (io with inputs := fs))
          else
            SOME (FFIreturn (1w :: DROP 1 bytes) io)
End

Definition ffi_send16_def:
  ffi_send16 (conf:word8 list) (bytes:word8 list) (io:counter_io) =
    if LENGTH bytes < 17 then
      SOME (FFIreturn bytes io)
    else
      let frame = TAKE 16 (DROP 1 bytes) in
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

Theorem ffi_recv16_length:
  ∀conf bytes io bytes' io'.
    ffi_recv16 conf bytes io = SOME (FFIreturn bytes' io') ⇒
    LENGTH bytes' = LENGTH bytes
Proof
  rpt strip_tac \\ gvs [ffi_recv16_def, AllCaseEqs()]
QED

Theorem ffi_send16_length:
  ∀conf bytes io bytes' io'.
    ffi_send16 conf bytes io = SOME (FFIreturn bytes' io') ⇒
    LENGTH bytes' = LENGTH bytes
Proof
  rpt strip_tac \\ gvs [ffi_send16_def, AllCaseEqs()]
QED

(* Bijective encoding of counter_io into cfHeapsBase$ffi *)

Definition encode_byte_list_def:
  encode_byte_list (bs:word8 list) : ffi = List (MAP (Num o w2n) bs)
End

Theorem encode_byte_list_11:
  ∀x y. encode_byte_list x = encode_byte_list y ⇔ x = y
Proof
  simp [encode_byte_list_def]
  \\ Induct
  >- (Cases \\ simp [])
  \\ gen_tac \\ Cases \\ simp [w2n_11]
QED

Definition encode_opt_num_def:
  (encode_opt_num NONE = Num 0) ∧
  (encode_opt_num (SOME n) = Cons (Num 1) (Num n))
End

Theorem encode_opt_num_11:
  ∀x y. encode_opt_num x = encode_opt_num y ⇔ x = y
Proof
  Cases \\ Cases \\ simp [encode_opt_num_def]
QED

Definition encode_counter_io_def:
  encode_counter_io (io:counter_io) : ffi =
    Cons (List (MAP encode_byte_list io.inputs))
         (Cons (List (MAP encode_byte_list io.outputs))
               (encode_opt_num io.write_limit))
End

Theorem encode_counter_io_11:
  ∀x y. encode_counter_io x = encode_counter_io y ⇔ x = y
Proof
  Cases \\ Cases \\ simp [encode_counter_io_def, encode_opt_num_11]
  \\ `∀a b. MAP encode_byte_list a = MAP encode_byte_list b ⇔ a = b` by
       (Induct >- (Cases \\ simp []) \\ gen_tac \\ Cases \\ simp [encode_byte_list_11])
  \\ simp []
QED

Definition decode_counter_io_def:
  decode_counter_io f =
    if ∃io. encode_counter_io io = f then SOME (@io. encode_counter_io io = f)
    else NONE
End

Theorem decode_encode_counter_io:
  ∀io. decode_counter_io (encode_counter_io io) = SOME io
Proof
  rw [decode_counter_io_def, encode_counter_io_11]
  \\ metis_tac []
QED

Definition counter_ffi_part_def:
  counter_ffi_part =
    (encode_counter_io, decode_counter_io,
     [(«recv16», ffi_recv16); («send16», ffi_send16)])
End

Definition counter_ffi_oracle_def:
  counter_ffi_oracle : counter_io oracle =
    λname io conf bytes.
      if name = ExtCall «recv16» then
        case ffi_recv16 conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else if name = ExtCall «send16» then
        case ffi_send16 conf bytes io of
          SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
        | _ => Oracle_final FFI_failed
      else
        Oracle_final FFI_failed
End

Definition counter_ffi_def:
  counter_ffi (io:counter_io) : counter_io ffi_state =
    initial_ffi_state counter_ffi_oracle io
End

Definition counter_proj_def:
  counter_proj : counter_io ffi_proj =
    ((λio. FEMPTY |++ [(«recv16», encode_counter_io io); («send16», encode_counter_io io)]),
     [([«recv16»; «send16»], mk_ffi_next counter_ffi_part)])
End

(* Direct extraction of sent 16-byte frames from machine io_events *)

Definition sent_frames_of_def:
  (sent_frames_of [] = []) ∧
  (sent_frames_of (IO_event (ExtCall n) conf bs :: rest) =
    (if n = «send16» ∧ 17 ≤ LENGTH bs then [TAKE 16 (DROP 1 (MAP FST bs))] else [])
    ++ sent_frames_of rest) ∧
  (sent_frames_of (_ :: rest) = sent_frames_of rest)
End

Theorem sent_frames_of_append:
  ∀xs ys. sent_frames_of (xs ++ ys) = sent_frames_of xs ++ sent_frames_of ys
Proof
  Induct \\ simp [sent_frames_of_def]
  \\ Cases \\ simp [sent_frames_of_def]
  \\ Cases_on `f` \\ simp [sent_frames_of_def]
QED

Theorem sent_frames_of_prefix:
  ∀xs ys. xs ≼ ys ⇒ sent_frames_of xs ≼ sent_frames_of ys
Proof
  rw [IS_PREFIX_APPEND] \\ simp [sent_frames_of_append]
QED

(* Relating call_FFI_rel^* on counter_ffi to sent_frames_of io_events *)

Theorem call_FFI_counter_outputs:
  ∀st st'.
    call_FFI_rel st st' ∧ st.oracle = counter_ffi_oracle ⇒
    st'.oracle = counter_ffi_oracle ∧
    st'.ffi_state.outputs = st.ffi_state.outputs ++
      sent_frames_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
Proof
  rw [evaluatePropsTheory.call_FFI_rel_def]
  \\ qpat_x_assum `call_FFI _ _ _ _ = _` mp_tac
  \\ simp [ffiTheory.call_FFI_def, AllCaseEqs()]
  \\ strip_tac \\ gvs [sent_frames_of_def, DROP_LENGTH_APPEND]
  \\ Cases_on `n`
  \\ gvs [counter_ffi_oracle_def, AllCaseEqs(), ffi_recv16_def, ffi_send16_def,
          sent_frames_of_def, MAP_ZIP]
QED

Theorem drop_append_sent_frames[local]:
  ∀a b c.
    sent_frames_of (DROP (LENGTH a) (a ++ b)) ++
    sent_frames_of (DROP (LENGTH (a ++ b)) ((a ++ b) ++ c)) =
    sent_frames_of (DROP (LENGTH a) ((a ++ b) ++ c))
Proof
  Induct_on `a`
  >- simp [DROP_LENGTH_APPEND, sent_frames_of_append]
  \\ fs []
QED

Theorem call_FFI_star_counter_outputs:
  ∀st st'.
    call_FFI_rel^* st st' ⇒
    st.oracle = counter_ffi_oracle ⇒
    st'.oracle = counter_ffi_oracle ∧
    st'.ffi_state.outputs = st.ffi_state.outputs ++
      sent_frames_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
Proof
  ho_match_mp_tac relationTheory.RTC_INDUCT \\ rw []
  >- simp [sent_frames_of_def]
  \\ drule_all call_FFI_counter_outputs \\ strip_tac
  \\ fs []
  \\ `st.io_events ≼ st''.io_events` by metis_tac [IS_PREFIX_TRANS]
  \\ simp []
  \\ qpat_x_assum `st.io_events ≼ st'.io_events` mp_tac
  \\ qpat_x_assum `st'.io_events ≼ st''.io_events` mp_tac
  \\ simp [IS_PREFIX_APPEND] \\ rpt strip_tac
  \\ qspecl_then [`st.io_events`, `l'`, `l`] mp_tac drop_append_sent_frames
  \\ simp []
QED

Theorem counter_ffi_outputs_eq_sent_frames:
  ∀io st'.
    io.outputs = [] ∧
    call_FFI_rel^* (counter_ffi io) st' ⇒
    st'.ffi_state.outputs = sent_frames_of st'.io_events
Proof
  rw [counter_ffi_def, ffiTheory.initial_ffi_state_def]
  \\ drule call_FFI_star_counter_outputs \\ simp []
QED
