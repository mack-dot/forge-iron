(* Forge M2 Guardrail Pure HOL4 Spec (<100 lines; 64B LE64 frame = 8 x word64) *)
Theory forge_guardrailSpec
Ancestors words arithmetic list forge_frame64Spec
Libs preamble blastLib wordsLib
Datatype:
  gr_state = <| deposits:word64; balance:word64; spent:word64; refunds:word64; cap:word64;
                allowmask:word64; nonce:word64; last_tx:word64; last_amt:word64; tx_open:bool |>
End
Definition gr_init_def:
  gr_init = <| deposits:=0w; balance:=0w; spent:=0w; refunds:=0w; cap:=100000w; allowmask:=7w; nonce:=0w; last_tx:=0w; last_amt:=0w; tx_open:=F |>
End
Definition dest_allowed_def:
  dest_allowed (mask:word64) (d:word64) ⇔ d <₊ 64w ∧ word_bit (w2n d) mask
End
Definition gr_resp_def:
  gr_resp ok code st = Frame64 ok code st.deposits st.balance (st.spent − st.refunds) st.refunds st.nonce st.last_tx
End
Definition encode_frame_def:
  encode_frame fr = frame64_encode fr
End
Definition decode_frame_def:
  decode_frame bs = frame64_decode bs
End
Definition gr_step_def:
  gr_step st (Frame64 op agent arg2 amt arg4 _ _ _) =
    if op = 1w then (* BUDGET_SET/DEPOSIT: arg2=allowmask, amt=deposit, arg4=cap *)
      if amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.deposits ∧ (st.spent − st.refunds) ≤₊ arg4 then
        let st' = st with <| deposits := st.deposits + amt; balance := st.balance + amt; cap := arg4; allowmask := arg2 |> in (st', gr_resp 1w 0w st')
      else (st, gr_resp 0w 1w st)
    else if op = 2w then (* SPEND_REQUEST: arg2=dest_id, amt=amount, arg4=nonce *)
      if amt ≠ 0w ∧ dest_allowed st.allowmask arg2 ∧ st.nonce ≠ 0xFFFFFFFFFFFFFFFFw ∧ arg4 = st.nonce + 1w ∧
         st.last_tx ≠ 0xFFFFFFFFFFFFFFFFw ∧ amt ≤₊ st.balance ∧ amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.spent ∧ amt ≤₊ st.cap − (st.spent − st.refunds) then
        let st' = st with <| balance := st.balance − amt; spent := st.spent + amt; nonce := arg4; last_tx := st.last_tx + 1w; last_amt := amt; tx_open := T |> in (st', gr_resp 1w 0w st')
      else (st, gr_resp 0w 2w st)
    else if op = 3w then (* REFUND: arg4=tx_id, amt=refund_amount *)
      if amt ≠ 0w ∧ st.tx_open ∧ arg4 = st.last_tx ∧ amt ≤₊ st.last_amt ∧
         amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.refunds ∧ amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.balance then
        let st' = st with <| balance := st.balance + amt; refunds := st.refunds + amt; tx_open := F |> in (st', gr_resp 1w 0w st')
      else (st, gr_resp 0w 3w st)
    else if op = 4w then (st, gr_resp 1w 0w st) else (st, gr_resp 0w 4w st) (* QUERY / unknown *)
End
Definition gr_inv_def:
  gr_inv st ⇔
    st.refunds ≤₊ st.spent ∧ (st.tx_open ⇒ st.last_amt ≤₊ st.spent − st.refunds) ∧
    w2n st.deposits = w2n st.balance + (w2n st.spent − w2n st.refunds) ∧ (st.spent − st.refunds) ≤₊ st.cap
End
Theorem w64_arith[local]:
  (∀x y:word64. y ≤₊ -1w * x + 0xFFFFFFFFFFFFFFFFw ⇒ w2n (y + x) = w2n y + w2n x) ∧
  (∀x y:word64. y ≤₊ x ⇒ w2n (-1w * y + x) = w2n x − w2n y ∧ w2n (x + -1w * y) = w2n x − w2n y) ∧
  (∀x y z:word64. y ≤₊ x + z ⇒ w2n (x + -1w * y + z) = w2n (x + z) − w2n y)
Proof
  rpt conj_tac \\ rpt strip_tac
  >- (`y + x = x + y` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC \\ `w2n x < 18446744073709551616` by (assume_tac (Q.ISPEC `x:word64` w2n_lt) \\ fs [dimword_64])
    \\ `w2n (-1w * x + 0xFFFFFFFFFFFFFFFFw) = 18446744073709551615 − w2n x` by (`-1w * x + 0xFFFFFFFFFFFFFFFFw = 0xFFFFFFFFFFFFFFFFw − x` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC \\ `x ≤₊ 0xFFFFFFFFFFFFFFFFw` by simp [WORD_LS] \\ simp [word_sub_w2n])
    \\ `w2n x + w2n y < 18446744073709551616` by fs [WORD_LS] \\ simp [word_add_def, w2n_n2w, dimword_64])
  >- (`-1w * y + x = x − y` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC \\ simp [word_sub_w2n])
  >- (`x + -1w * y = x − y` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC \\ simp [word_sub_w2n])
  \\ `x + -1w * y + z = (x + z) − y` by blastLib.BBLAST_TAC \\ pop_assum SUBST1_TAC \\ simp [word_sub_w2n]
QED
(* 1-Line Global Sanity Laws *)
Theorem frame_bijection:
  (∀fr. decode_frame (encode_frame fr) = fr) ∧ (∀bs. LENGTH bs = 64 ⇒ encode_frame (decode_frame bs) = bs)
Proof
  simp [encode_frame_def, decode_frame_def, frame64_roundtrip, frame64_decode_encode_bytes]
QED
Theorem gr_inv_init:
  gr_inv gr_init
Proof
  simp [gr_inv_def, gr_init_def] \\ EVAL_TAC
QED
Theorem gr_step_preserves_inv:
  ∀st fr st' resp. gr_inv st ∧ gr_step st fr = (st', resp) ⇒ gr_inv st'
Proof
  Cases_on `fr` \\ rename1 `Frame64 op ag a2 amt a4 r5 r6 r7`
  \\ Cases_on `op = 1w` >- (rw [gr_step_def, gr_inv_def, LET_THM] \\ TRY (fs [] \\ NO_TAC) \\ qspecl_then [`st.deposits`, `amt`] mp_tac (cj 1 w64_arith) \\ simp [] \\ strip_tac \\ assume_tac (Q.ISPEC `amt + st.deposits` w2n_lt) \\ `w2n amt + w2n st.balance < 18446744073709551616` by fs [dimword_64] \\ `w2n (amt + st.balance) = w2n amt + w2n st.balance` by simp [word_add_def, w2n_n2w, dimword_64] \\ decide_tac)
  \\ Cases_on `op = 2w` >- (rw [gr_step_def, gr_inv_def, LET_THM] \\ qspecl_then [`st.spent`, `amt`] mp_tac (cj 1 w64_arith) \\ qspecl_then [`st.spent`, `st.refunds`] mp_tac (cj 2 w64_arith) \\ qspecl_then [`st.balance`, `amt`] mp_tac (cj 2 w64_arith) \\ qspecl_then [`st.cap`, `-1w * st.refunds + st.spent`] mp_tac (cj 2 w64_arith) \\ simp [] \\ rpt strip_tac \\ `st.refunds ≤₊ amt + st.spent` by fs [WORD_LS] \\ qspecl_then [`amt`, `st.refunds`, `st.spent`] mp_tac (cj 3 w64_arith) \\ fs [WORD_LS] \\ decide_tac)
  \\ Cases_on `op = 3w` >- (rw [gr_step_def, gr_inv_def, LET_THM] \\ qspecl_then [`st.refunds`, `amt`] mp_tac (cj 1 w64_arith) \\ qspecl_then [`st.balance`, `amt`] mp_tac (cj 1 w64_arith) \\ qspecl_then [`st.spent`, `st.refunds`] mp_tac (cj 2 w64_arith) \\ simp [] \\ rpt strip_tac \\ `amt + st.refunds ≤₊ st.spent` by fs [WORD_LS] \\ qspecl_then [`st.spent`, `amt + st.refunds`] mp_tac (cj 2 w64_arith) \\ fs [WORD_LS] \\ decide_tac)
  \\ rw [gr_step_def] \\ gvs []
QED
Theorem gr_run_preserves_inv:
  ∀inps st. gr_inv st ⇒ gr_inv (FST (frame64_run gr_step st inps))
Proof
  Induct \\ simp [frame64_run_def] \\ rpt strip_tac \\ Cases_on `LENGTH h = 64` \\ simp [] \\ Cases_on `gr_step st (frame64_decode h)` \\ simp [] \\ pairarg_tac \\ fs [] \\ `gr_inv q` by metis_tac [gr_step_preserves_inv] \\ first_x_assum (qspec_then `q` mp_tac) \\ simp []
QED
Theorem gr_safety_denials:
  (∀st ag d amt nc r5 r6 r7. ¬dest_allowed st.allowmask d ⇒ FST (gr_step st (Frame64 2w ag d amt nc r5 r6 r7)) = st) ∧
  (∀st ag d amt r5 r6 r7. FST (gr_step st (Frame64 2w ag d amt st.nonce r5 r6 r7)) = st) ∧
  (∀st ag a2 amt tx r5 r6 r7. ¬st.tx_open ⇒ FST (gr_step st (Frame64 3w ag a2 amt tx r5 r6 r7)) = st)
Proof
  rw [gr_step_def] \\ `∀w:word64. w ≠ w + 1w` by blastLib.BBLAST_TAC \\ metis_tac []
QED
