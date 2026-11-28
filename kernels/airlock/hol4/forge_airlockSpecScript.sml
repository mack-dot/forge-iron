(*
  Forge Milestone 3: Pure HOL4 Crypto-Authenticated, Crash-Atomic Airlock Specification.

  SHA-256 pinned specification defining:
    - Fixed 64B LE64 request frames (`frame64`) and 128B LE64 response frames (`frame128`)
      carrying both guardrail accounting state and unforgeable HMAC-SHA256 capability tokens
      over `(seq, op, dest, amt, balance)` with domain tag `"FORGE-CAP-V1"`.
    - Dual-slot 256-byte crash-atomic persistent disk records (`Slot A` / `Slot B`) with
      monotonic generation counter, SHA-256 integrity checksum, and `last_token` retry cache.
    - Pure proofs of exact natural-number fund conservation, rolling net cap, allowlist,
      strict monotonic nonces, universal dual-slot crash recovery, retry idempotency,
      safety denials, and cryptographic token authenticity.
*)
Theory forge_airlockSpec
Ancestors
  words arithmetic list rich_list forge_frame64Spec forge_sha256Spec forge_airlockFfi
Libs
  preamble blastLib wordsLib

(* ---- 1. Airlock Persistent State & 32B/Word64x4 Conversion ---- *)

Datatype:
  airlock_state = <|
    gen       : word64;
    deposits  : word64;
    balance   : word64;
    spent     : word64;
    refunds   : word64;
    cap       : word64;
    allowmask : word64;
    nonce     : word64;
    last_tx   : word64;
    last_amt  : word64;
    tx_open   : bool;
    tok_seq   : word64;
    tok_op    : word64;
    tok_dest  : word64;
    tok_amt   : word64;
    tok_bal   : word64;
    tok_tag0  : word64;
    tok_tag1  : word64;
    tok_tag2  : word64;
    tok_tag3  : word64
  |>
End

Definition bytes32_to_w64x4_def:
  bytes32_to_w64x4 (bs:word8 list) : word64 # word64 # word64 # word64 =
    let (w0, r0) = le64_take bs in
    let (w1, r1) = le64_take r0 in
    let (w2, r2) = le64_take r1 in
    let (w3, _ ) = le64_take r2 in
      (w0, w1, w2, w3)
End

Definition w64x4_to_bytes32_def:
  w64x4_to_bytes32 ((w0,w1,w2,w3):word64#word64#word64#word64) : word8 list =
    le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3
End

(* ---- 2. Capability Token Construction (Domain "FORGE-CAP-V1") ---- *)

Definition cap_domain_def:
  cap_domain : word8 list =
    [0x46w; 0x4fw; 0x52w; 0x47w; 0x45w; 0x2dw;
     0x43w; 0x41w; 0x50w; 0x2dw; 0x56w; 0x31w]
End

Definition cap_token_msg_def:
  cap_token_msg (seq:word64) (op:word64) (dest:word64) (amt:word64) (bal:word64) : word8 list =
    cap_domain ++
    le64_encode seq ++ le64_encode op ++ le64_encode dest ++
    le64_encode amt ++ le64_encode bal
End

Definition mint_cap_tag_def:
  mint_cap_tag (key:word8 list) (seq:word64) (op:word64)
               (dest:word64) (amt:word64) (bal:word64) =
    bytes32_to_w64x4 (hmac_sha256 key (cap_token_msg seq op dest amt bal))
End

(* ---- 3. Airlock Initial State, Step Function & Invariant ---- *)

Definition airlock_init_def:
  airlock_init : airlock_state = <|
    gen := 0w; deposits := 0w; balance := 0w; spent := 0w; refunds := 0w;
    cap := 100000w; allowmask := 7w; nonce := 0w; last_tx := 0w; last_amt := 0w;
    tx_open := F; tok_seq := 0w; tok_op := 0w; tok_dest := 0w; tok_amt := 0w;
    tok_bal := 0w; tok_tag0 := 0w; tok_tag1 := 0w; tok_tag2 := 0w; tok_tag3 := 0w
  |>
End

Definition al_dest_allowed_def:
  al_dest_allowed (mask:word64) (d:word64) ⇔ d <₊ 64w ∧ ((mask ⋙ w2n d) && 1w ≠ 0w)
End

Definition al_resp_plain_def:
  al_resp_plain (ok:word64) (code:word64) (st:airlock_state) : frame128 =
    Frame128 ok code st.deposits st.balance (st.spent − st.refunds)
             st.refunds st.nonce st.last_tx
             0w 0w 0w 0w 0w 0w 0w 0w
End

Definition al_resp_tok_def:
  al_resp_tok (ok:word64) (code:word64) (st:airlock_state) : frame128 =
    Frame128 ok code st.deposits st.balance (st.spent − st.refunds)
             st.refunds st.nonce st.last_tx
             st.tok_seq st.tok_op st.tok_dest st.tok_amt
             st.tok_tag0 st.tok_tag1 st.tok_tag2 st.tok_tag3
End

Definition airlock_step_def:
  airlock_step (key:word8 list) (st:airlock_state) (Frame64 op agent arg2 amt arg4 _ _ _)
    : airlock_state # frame128 # bool =
    if op = 1w then (* BUDGET_SET / DEPOSIT (admin) *)
      if st.gen ≠ 0xFFFFFFFFFFFFFFFFw ∧
         amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.deposits ∧
         (st.spent − st.refunds) ≤₊ arg4 then
        let st' = st with <|
          gen := st.gen + 1w;
          deposits := st.deposits + amt;
          balance := st.balance + amt;
          cap := arg4;
          allowmask := arg2;
          tok_op := 0w
        |> in (st', al_resp_plain 1w 0w st', T)
      else (st, al_resp_plain 0w 1w st, F)
    else if op = 2w then (* SPEND_REQUEST: arg2=dest_id, amt=amount, arg4=nonce *)
      if st.tok_op = 2w ∧ arg4 = st.nonce ∧ arg2 = st.tok_dest ∧ amt = st.tok_amt then
        (st, al_resp_tok 1w 5w st, F) (* idempotent retry cache hit *)
      else if st.gen ≠ 0xFFFFFFFFFFFFFFFFw ∧
              amt ≠ 0w ∧ al_dest_allowed st.allowmask arg2 ∧
              st.nonce ≠ 0xFFFFFFFFFFFFFFFFw ∧ arg4 = st.nonce + 1w ∧
              st.last_tx ≠ 0xFFFFFFFFFFFFFFFFw ∧
              amt ≤₊ st.balance ∧
              amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.spent ∧
              amt ≤₊ st.cap − (st.spent − st.refunds) then
        let gen' = st.gen + 1w in
        let bal' = st.balance − amt in
        let (t0, t1, t2, t3) = mint_cap_tag key gen' 2w arg2 amt bal' in
        let st' = st with <|
          gen := gen'; balance := bal'; spent := st.spent + amt;
          nonce := arg4; last_tx := st.last_tx + 1w; last_amt := amt; tx_open := T;
          tok_seq := gen'; tok_op := 2w; tok_dest := arg2; tok_amt := amt; tok_bal := bal';
          tok_tag0 := t0; tok_tag1 := t1; tok_tag2 := t2; tok_tag3 := t3
        |> in (st', al_resp_tok 1w 0w st', T)
      else (st, al_resp_plain 0w 2w st, F)
    else if op = 3w then (* REFUND: arg4=tx_id, amt=refund_amount *)
      if st.tok_op = 3w ∧ ¬st.tx_open ∧ arg4 = st.last_tx ∧ amt = st.tok_amt then
        (st, al_resp_tok 1w 5w st, F) (* idempotent retry cache hit *)
      else if st.gen ≠ 0xFFFFFFFFFFFFFFFFw ∧
              amt ≠ 0w ∧ st.tx_open ∧ arg4 = st.last_tx ∧
              amt ≤₊ st.last_amt ∧
              amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.refunds ∧
              amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.balance then
        let gen' = st.gen + 1w in
        let bal' = st.balance + amt in
        let (t0, t1, t2, t3) = mint_cap_tag key gen' 3w arg4 amt bal' in
        let st' = st with <|
          gen := gen'; balance := bal'; refunds := st.refunds + amt; tx_open := F;
          tok_seq := gen'; tok_op := 3w; tok_dest := arg4; tok_amt := amt; tok_bal := bal';
          tok_tag0 := t0; tok_tag1 := t1; tok_tag2 := t2; tok_tag3 := t3
        |> in (st', al_resp_tok 1w 0w st', T)
      else (st, al_resp_plain 0w 3w st, F)
    else if op = 4w then (st, al_resp_plain 1w 0w st, F)
    else (st, al_resp_plain 0w 4w st, F)
End

Definition airlock_inv_def:
  airlock_inv (key:word8 list) (st:airlock_state) ⇔
    st.refunds ≤₊ st.spent ∧
    (st.tx_open ⇒ st.last_amt ≤₊ st.spent − st.refunds) ∧
    st.balance ≤₊ st.deposits ∧
    st.deposits = st.balance + (st.spent − st.refunds) ∧
    (st.spent − st.refunds) ≤₊ st.cap ∧
    (st.tok_op ≠ 0w ⇒
       st.balance = st.tok_bal ∧
       (st.tok_tag0, st.tok_tag1, st.tok_tag2, st.tok_tag3) =
         mint_cap_tag key st.tok_seq st.tok_op st.tok_dest st.tok_amt st.tok_bal)
End

(* ---- 4. Dual-Slot 256-Byte Crash-Atomic Disk Format ---- *)

Definition SLOT_MAGIC_def:
  SLOT_MAGIC : word64 = 0x464F524745534C33w
End

Definition encode_slot_body_def:
  encode_slot_body (st:airlock_state) : word8 list =
    le64_encode SLOT_MAGIC ++
    le64_encode st.gen ++
    le64_encode st.deposits ++
    le64_encode st.balance ++
    le64_encode st.spent ++
    le64_encode st.refunds ++
    le64_encode st.cap ++
    le64_encode st.allowmask ++
    le64_encode st.nonce ++
    le64_encode st.last_tx ++
    le64_encode st.last_amt ++
    le64_encode (if st.tx_open then 1w else 0w) ++
    le64_encode st.tok_seq ++
    le64_encode st.tok_op ++
    le64_encode st.tok_dest ++
    le64_encode st.tok_amt ++
    le64_encode st.tok_bal ++
    le64_encode st.tok_tag0 ++
    le64_encode st.tok_tag1 ++
    le64_encode st.tok_tag2 ++
    le64_encode st.tok_tag3 ++
    REPLICATE 56 0w
End

Definition encode_slot_def:
  encode_slot (key:word8 list) (st:airlock_state) : word8 list =
    let body = encode_slot_body st in body ++ hmac_sha256 key body
End

Definition decode_slot_raw_def:
  decode_slot_raw (bs:word8 list) : word64 # airlock_state =
    let (magic, r0)  = le64_take bs  in let (gen,   r1)  = le64_take r0  in
    let (dep,   r2)  = le64_take r1  in let (bal,   r3)  = le64_take r2  in
    let (sp,    r4)  = le64_take r3  in let (rf,    r5)  = le64_take r4  in
    let (cp,    r6)  = le64_take r5  in let (mask,  r7)  = le64_take r6  in
    let (nc,    r8)  = le64_take r7  in let (ltx,   r9)  = le64_take r8  in
    let (lamt,  r10) = le64_take r9  in let (txop,  r11) = le64_take r10 in
    let (tseq,  r12) = le64_take r11 in let (top,   r13) = le64_take r12 in
    let (tdest, r14) = le64_take r13 in let (tamt,  r15) = le64_take r14 in
    let (tbal,  r16) = le64_take r15 in let (tt0,   r17) = le64_take r16 in
    let (tt1,   r18) = le64_take r17 in let (tt2,   r19) = le64_take r18 in
    let (tt3,   _ )  = le64_take r19 in
      (magic, <|
        gen := gen; deposits := dep; balance := bal; spent := sp; refunds := rf;
        cap := cp; allowmask := mask; nonce := nc; last_tx := ltx; last_amt := lamt;
        tx_open := (txop ≠ 0w);
        tok_seq := tseq; tok_op := top; tok_dest := tdest; tok_amt := tamt; tok_bal := tbal;
        tok_tag0 := tt0; tok_tag1 := tt1; tok_tag2 := tt2; tok_tag3 := tt3
      |>)
End

Definition slot_valid_def:
  slot_valid (key:word8 list) (bs:word8 list) ⇔
    LENGTH bs = 256 ∧
    let (magic, st) = decode_slot_raw bs in
      magic = SLOT_MAGIC ∧
      st.gen ≠ 0w ∧
      DROP 224 bs = hmac_sha256 key (TAKE 224 bs) ∧
      airlock_inv key st
End

Definition recover_dual_slot_def:
  recover_dual_slot (key:word8 list) (slotA:word8 list) (slotB:word8 list) : airlock_state =
    let va = slot_valid key slotA in
    let vb = slot_valid key slotB in
      if va ∧ vb then
        let sa = SND (decode_slot_raw slotA) in
        let sb = SND (decode_slot_raw slotB) in
          if sa.gen <₊ sb.gen then sb else sa
      else if va then SND (decode_slot_raw slotA)
      else if vb then SND (decode_slot_raw slotB)
      else airlock_init
End

(* Odd generation -> Slot A (0w, offset 0); Even generation -> Slot B (1w, offset 256) *)
Definition commit_slot_byte_def:
  commit_slot_byte (gen:word64) : word8 = if (gen && 1w) = 0w then 1w else 0w
End

Definition airlock_run_def:
  (airlock_run key st [] = (st, [])) ∧
  (airlock_run key st (fr_bs::rest) =
     if LENGTH fr_bs = 64 then
       let (st', resp, _) = airlock_step key st (frame64_decode fr_bs) in
       let (st_f, outs) = airlock_run key st' rest in
         (st_f, frame128_encode resp :: outs)
     else (st, []))
End

(* ---- 5. Core Correctness, Conservation, Crash-Recovery & Security Proofs ---- *)

Theorem LENGTH_encode_slot_body:
  ∀st. LENGTH (encode_slot_body st) = 224
Proof
  gen_tac \\ simp [encode_slot_body_def, le64_encode_def]
QED

Theorem LENGTH_encode_slot:
  ∀key st. LENGTH (encode_slot key st) = 256
Proof
  rpt gen_tac \\ simp [encode_slot_def, LENGTH_encode_slot_body, LENGTH_hmac_sha256]
QED

Theorem decode_encode_slot:
  ∀key st. decode_slot_raw (encode_slot key st) = (SLOT_MAGIC, st)
Proof
  rpt gen_tac
  \\ simp [Excl "APPEND_ASSOC", encode_slot_def, encode_slot_body_def,
           decode_slot_raw_def, GSYM APPEND_ASSOC, le64_take_encode]
  \\ Cases_on `st.tx_open`
  \\ simp [theorem "airlock_state_component_equality"]
QED

Theorem slot_valid_encode_slot:
  ∀key st. st.gen ≠ 0w ∧ airlock_inv key st ⇒ slot_valid key (encode_slot key st)
Proof
  rpt strip_tac
  \\ simp [slot_valid_def, LENGTH_encode_slot, decode_encode_slot, LET_THM]
  \\ simp [encode_slot_def, LET_THM, TAKE_APPEND1, DROP_APPEND2,
           LENGTH_encode_slot_body, TAKE_LENGTH_ID_rwt]
QED

Theorem w64_al_arith[local]:
  (∀x y:word64. y ≤₊ 0xFFFFFFFFFFFFFFFFw − x ⇒ w2n (x + y) = w2n x + w2n y ∧ x ≤₊ x + y) ∧
  (∀x y:word64. y ≤₊ -1w * x + 0xFFFFFFFFFFFFFFFFw ⇒ w2n (y + x) = w2n y + w2n x ∧ w2n (x + y) = w2n x + w2n y) ∧
  (∀x y:word64. y ≤₊ x ⇒ w2n (x − y) = w2n x − w2n y ∧ w2n (-1w * y + x) = w2n x − w2n y ∧ w2n (x + -1w * y) = w2n x − w2n y)
Proof
  rpt conj_tac \\ rpt strip_tac
  >- (`w2n x < 18446744073709551616` by (assume_tac (Q.ISPEC `x:word64` w2n_lt) \\ fs [dimword_64])
      \\ `w2n (0xFFFFFFFFFFFFFFFFw − x) = 18446744073709551615 − w2n x` by
           (qspecl_then [`0xFFFFFFFFFFFFFFFFw:word64`, `x`] mp_tac word_sub_w2n
            \\ `x ≤₊ 0xFFFFFFFFFFFFFFFFw` by simp [WORD_LS] \\ simp [])
      \\ `w2n x + w2n y < 18446744073709551616` by fs [WORD_LS]
      \\ simp [word_add_def, w2n_n2w, dimword_64])
  >- (qpat_x_assum `y ≤₊ _` mp_tac \\ blastLib.BBLAST_TAC)
  >- (`y + x = x + y` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC
      \\ `w2n x < 18446744073709551616` by (assume_tac (Q.ISPEC `x:word64` w2n_lt) \\ fs [dimword_64])
      \\ `y ≤₊ 0xFFFFFFFFFFFFFFFFw − x` by (qpat_x_assum `y ≤₊ _` mp_tac \\ blastLib.BBLAST_TAC)
      \\ `w2n (0xFFFFFFFFFFFFFFFFw − x) = 18446744073709551615 − w2n x` by
           (qspecl_then [`0xFFFFFFFFFFFFFFFFw:word64`, `x`] mp_tac word_sub_w2n
            \\ `x ≤₊ 0xFFFFFFFFFFFFFFFFw` by simp [WORD_LS] \\ simp [])
      \\ `w2n x + w2n y < 18446744073709551616` by fs [WORD_LS]
      \\ simp [word_add_def, w2n_n2w, dimword_64])
  >- (`w2n x < 18446744073709551616` by (assume_tac (Q.ISPEC `x:word64` w2n_lt) \\ fs [dimword_64])
      \\ `y ≤₊ 0xFFFFFFFFFFFFFFFFw − x` by (qpat_x_assum `y ≤₊ _` mp_tac \\ blastLib.BBLAST_TAC)
      \\ `w2n (0xFFFFFFFFFFFFFFFFw − x) = 18446744073709551615 − w2n x` by
           (qspecl_then [`0xFFFFFFFFFFFFFFFFw:word64`, `x`] mp_tac word_sub_w2n
            \\ `x ≤₊ 0xFFFFFFFFFFFFFFFFw` by simp [WORD_LS] \\ simp [])
      \\ `w2n x + w2n y < 18446744073709551616` by fs [WORD_LS]
      \\ simp [word_add_def, w2n_n2w, dimword_64])
  >- simp [word_sub_w2n]
  >- (`-1w * y + x = x − y` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC \\ simp [word_sub_w2n])
  \\ `x + -1w * y = x − y` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC \\ simp [word_sub_w2n]
QED

Theorem w64_add_no_wrap[local]:
  ∀a b:word64. a ≤₊ a + b ⇒ w2n (a + b) = w2n a + w2n b
Proof
  rpt strip_tac
  \\ `b ≤₊ 0xFFFFFFFFFFFFFFFFw − a` by (qpat_x_assum `a ≤₊ a + b` mp_tac \\ blastLib.BBLAST_TAC)
  \\ simp [cj 1 w64_al_arith]
QED

Theorem airlock_base_inv_nat_conservation:
  ∀key st. airlock_inv key st ⇒
    w2n st.deposits = w2n st.balance + (w2n st.spent − w2n st.refunds)
Proof
  rpt strip_tac \\ fs [airlock_inv_def]
  \\ qspecl_then [`st.balance`, `st.spent − st.refunds`] mp_tac w64_add_no_wrap
  \\ fs [word_sub_w2n]
QED

Theorem airlock_inv_init:
  ∀key. airlock_inv key airlock_init
Proof
  gen_tac \\ simp [airlock_inv_def, airlock_init_def] \\ EVAL_TAC
QED

Theorem airlock_inv_recover_dual_slot:
  ∀key slotA slotB. airlock_inv key (recover_dual_slot key slotA slotB)
Proof
  rpt gen_tac \\ simp [recover_dual_slot_def, LET_THM]
  \\ rpt IF_CASES_TAC \\ fs [slot_valid_def, LET_THM, airlock_inv_init]
  \\ pairarg_tac \\ fs [] \\ pairarg_tac \\ fs []
QED

(* Universal Dual-Slot Crash Recovery Theorem (Closes E1/E2 storage atomicity) *)
Theorem dual_slot_crash_recovery:
  ∀key st st' bad.
    st.gen ≠ 0w ∧ airlock_inv key st ∧
    st'.gen = st.gen + 1w ∧ st.gen ≠ 0xFFFFFFFFFFFFFFFFw ∧ airlock_inv key st' ∧
    ¬slot_valid key bad ⇒
    (* Torn/power-loss write to inactive slot recovers exact prior committed st *)
    (recover_dual_slot key (encode_slot key st) bad = st ∧
     recover_dual_slot key bad (encode_slot key st) = st) ∧
    (* Completed commit to inactive slot recovers exact new st' *)
    (recover_dual_slot key (encode_slot key st) (encode_slot key st') = st' ∧
     recover_dual_slot key (encode_slot key st') (encode_slot key st) = st')
Proof
  rpt strip_tac
  \\ `slot_valid key (encode_slot key st)` by metis_tac [slot_valid_encode_slot]
  \\ `st.gen + 1w ≠ 0w ∧ st.gen <₊ st.gen + 1w ∧ ¬(st.gen + 1w <₊ st.gen)` by
       (qpat_x_assum `st.gen ≠ 0xFFFFFFFFFFFFFFFFw` mp_tac \\ blastLib.BBLAST_TAC)
  \\ `slot_valid key (encode_slot key st')` by metis_tac [slot_valid_encode_slot]
  \\ simp [recover_dual_slot_def, decode_encode_slot, LET_THM]
QED

Theorem airlock_step_preserves_inv:
  ∀key st fr st' resp dc.
    airlock_inv key st ∧ airlock_step key st fr = (st', resp, dc) ⇒
    airlock_inv key st'
Proof
  Cases_on `fr` \\ rename1 `Frame64 op ag a2 amt a4 r5 r6 r7`
  \\ rpt strip_tac
  \\ imp_res_tac airlock_base_inv_nat_conservation
  \\ qpat_x_assum `airlock_step _ _ _ = _` mp_tac
  \\ simp [airlock_step_def]
  \\ IF_CASES_TAC
  >- (
    IF_CASES_TAC >- (
      strip_tac \\ fs [] \\ rveq \\ fs [airlock_inv_def]
      \\ qspecl_then [`st.deposits`, `amt`] mp_tac (cj 2 w64_al_arith)
      \\ fs [] \\ strip_tac
      \\ `w2n amt + w2n st.balance < dimword (:64)` by
           (assume_tac (Q.ISPEC `amt + st.balance + -1w * st.refunds + st.spent` w2n_lt) \\ decide_tac)
      \\ `w2n (amt + st.balance) = w2n amt + w2n st.balance` by simp [word_add_def, w2n_n2w]
      \\ simp [WORD_LS] \\ decide_tac)
    \\ strip_tac \\ gvs [])
  \\ IF_CASES_TAC
  >- (
    IF_CASES_TAC >- (strip_tac \\ gvs [])
    \\ IF_CASES_TAC >- (
      strip_tac \\ pairarg_tac \\ fs [] \\ rveq \\ fs [airlock_inv_def]
      \\ qspecl_then [`st.spent`, `amt`] mp_tac (cj 2 w64_al_arith)
      \\ qspecl_then [`st.balance`, `amt`] mp_tac (cj 3 w64_al_arith)
      \\ qspecl_then [`st.spent`, `st.refunds`] mp_tac (cj 3 w64_al_arith)
      \\ qspecl_then [`st.cap`, `-1w * st.refunds + st.spent`] mp_tac (cj 3 w64_al_arith)
      \\ fs [] \\ rpt strip_tac
      \\ `st.refunds ≤₊ amt + st.spent` by fs [WORD_LS]
      \\ `w2n (amt + -1w * st.refunds + st.spent) = w2n amt + w2n st.spent − w2n st.refunds` by
           (`amt + -1w * st.refunds + st.spent = (amt + st.spent) − st.refunds` by blastLib.BBLAST_TAC
            \\ pop_assum SUBST1_TAC \\ simp [word_sub_w2n])
      \\ rpt conj_tac \\ gvs [WORD_LS] \\ decide_tac)
    \\ strip_tac \\ gvs [])
  \\ IF_CASES_TAC
  >- (
    IF_CASES_TAC >- (strip_tac \\ gvs [])
    \\ IF_CASES_TAC >- (
      strip_tac \\ pairarg_tac \\ fs [] \\ rveq \\ fs [airlock_inv_def]
      \\ qspecl_then [`st.refunds`, `amt`] mp_tac (cj 2 w64_al_arith)
      \\ qspecl_then [`st.balance`, `amt`] mp_tac (cj 2 w64_al_arith)
      \\ qspecl_then [`st.spent`, `st.refunds`] mp_tac (cj 3 w64_al_arith)
      \\ fs [] \\ rpt strip_tac
      \\ `amt + st.refunds ≤₊ st.spent` by fs [WORD_LS]
      \\ `w2n (st.spent + -1w * (amt + st.refunds)) = w2n st.spent − (w2n amt + w2n st.refunds)` by
           (`st.spent + -1w * (amt + st.refunds) = st.spent − (amt + st.refunds)` by blastLib.BBLAST_TAC
            \\ pop_assum SUBST1_TAC \\ simp [word_sub_w2n])
      \\ rpt conj_tac
      >- (gvs [WORD_LS] \\ decide_tac)
      >- blastLib.BBLAST_TAC
      \\ gvs [WORD_LS] \\ decide_tac)
    \\ strip_tac \\ gvs [])
  \\ IF_CASES_TAC \\ strip_tac \\ gvs []
QED

Theorem airlock_run_preserves_inv:
  ∀inps key st. airlock_inv key st ⇒ airlock_inv key (FST (airlock_run key st inps))
Proof
  Induct \\ simp [airlock_run_def] \\ rpt strip_tac
  \\ Cases_on `LENGTH h = 64` \\ simp []
  \\ Cases_on `airlock_step key st (frame64_decode h)` \\ Cases_on `r` \\ simp []
  \\ `airlock_inv key q` by metis_tac [airlock_step_preserves_inv]
  \\ pairarg_tac \\ fs [] \\ first_x_assum (qspecl_then [`key`, `q`] mp_tac) \\ simp []
QED

(* Idempotent retry returns exact cached signed token with state unchanged and no disk commit *)
Theorem airlock_retry_idempotent:
  (∀key st ag r5 r6 r7.
     st.tok_op = 2w ⇒
     airlock_step key st (Frame64 2w ag st.tok_dest st.tok_amt st.nonce r5 r6 r7) =
       (st, al_resp_tok 1w 5w st, F)) ∧
  (∀key st ag a2 r5 r6 r7.
     st.tok_op = 3w ∧ ¬st.tx_open ⇒
     airlock_step key st (Frame64 3w ag a2 st.tok_amt st.last_tx r5 r6 r7) =
       (st, al_resp_tok 1w 5w st, F))
Proof
  rw [airlock_step_def]
QED

(* Safety denials: unallowlisted dest, tampered replay, and non-matching double-refund *)
Theorem airlock_safety_denials:
  (∀key st ag d amt nc r5 r6 r7.
     ¬al_dest_allowed st.allowmask d ∧ ¬(st.tok_op = 2w ∧ nc = st.nonce ∧ d = st.tok_dest ∧ amt = st.tok_amt) ⇒
     airlock_step key st (Frame64 2w ag d amt nc r5 r6 r7) = (st, al_resp_plain 0w 2w st, F)) ∧
  (∀key st ag d amt r5 r6 r7.
     ¬(st.tok_op = 2w ∧ d = st.tok_dest ∧ amt = st.tok_amt) ⇒
     airlock_step key st (Frame64 2w ag d amt st.nonce r5 r6 r7) = (st, al_resp_plain 0w 2w st, F)) ∧
  (∀key st ag a2 amt tx r5 r6 r7.
     ¬st.tx_open ∧ ¬(st.tok_op = 3w ∧ tx = st.last_tx ∧ amt = st.tok_amt) ⇒
     airlock_step key st (Frame64 3w ag a2 amt tx r5 r6 r7) = (st, al_resp_plain 0w 3w st, F))
Proof
  rw [airlock_step_def]
  \\ `∀w:word64. w ≠ w + 1w` by blastLib.BBLAST_TAC \\ metis_tac []
QED

Theorem airlock_step_resp_shape[local]:
  ∀key st fr st' resp dc.
    airlock_step key st fr = (st', resp, dc) ⇒
    (∃ok code. resp = al_resp_plain ok code st') ∨
    (∃ok code. resp = al_resp_tok ok code st')
Proof
  Cases_on `fr`
  \\ PURE_REWRITE_TAC [airlock_step_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC >- (IF_CASES_TAC >- (BasicProvers.LET_ELIM_TAC \\ rpt strip_tac \\ fs [] \\ metis_tac []) \\ strip_tac \\ fs [] \\ metis_tac [])
  \\ IF_CASES_TAC >- (
       IF_CASES_TAC >- (strip_tac \\ fs [] \\ metis_tac [])
       \\ IF_CASES_TAC >- (BasicProvers.LET_ELIM_TAC \\ rpt strip_tac \\ fs [] \\ metis_tac [])
       \\ strip_tac \\ fs [] \\ metis_tac [])
  \\ IF_CASES_TAC >- (
       IF_CASES_TAC >- (strip_tac \\ fs [] \\ metis_tac [])
       \\ IF_CASES_TAC >- (BasicProvers.LET_ELIM_TAC \\ rpt strip_tac \\ fs [] \\ metis_tac [])
       \\ strip_tac \\ fs [] \\ metis_tac [])
  \\ IF_CASES_TAC \\ strip_tac \\ fs [] \\ metis_tac []
QED

(* Token authenticity: every emitted non-zero capability token matches HMAC-SHA256(key, msg) *)
Theorem airlock_emitted_token_authentic:
  ∀key st fr st' w0 w1 w2 w3 w4 w5 w6 w7 tseq top tdest tamt t0 t1 t2 t3 dc.
    airlock_inv key st ∧
    airlock_step key st fr = (st', Frame128 w0 w1 w2 w3 w4 w5 w6 w7 tseq top tdest tamt t0 t1 t2 t3, dc) ∧
    top ≠ 0w ⇒
    w3 = st'.balance ∧
    (t0, t1, t2, t3) = mint_cap_tag key tseq top tdest tamt w3
Proof
  rpt gen_tac \\ strip_tac
  \\ `airlock_inv key st'` by metis_tac [airlock_step_preserves_inv]
  \\ drule airlock_step_resp_shape \\ strip_tac
  >- gvs [al_resp_plain_def]
  \\ gvs [al_resp_tok_def, airlock_inv_def]
QED

Theorem airlock_exec_eq_run:
  ∀inps key st. airlock_exec airlock_step key st inps NONE NONE = airlock_run key st inps
Proof
  Induct \\ simp [airlock_exec_def, airlock_run_def]
  \\ rpt strip_tac \\ Cases_on `LENGTH h = 64` \\ simp []
  \\ Cases_on `airlock_step key st (frame64_decode h)` \\ Cases_on `r` \\ simp []
  \\ Cases_on `r'` \\ simp []
QED
