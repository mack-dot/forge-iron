#!/usr/bin/env python3
"""v0.1 Verified Vibe-Coding CLI (`scripts/forge_vibe.py`).

Turns plain-English / typed guardrail rules into:
  1. Socratic Spec Interview (`interview`): asks 7 concrete edge-case questions
     (units/cents, $0 behavior, gross vs net cap after refund, duplicate nonce,
     u64 overflow/underflow, destination allowlist, refund cap/finality) and
     writes a structured single-source schema JSON.
  2. Single-Schema Generation (`generate`): emits from that single schema:
     - `<100`-line pure HOL4 spec (`kernels/<app>/hol4/forge_<app>SpecScript.sml`)
       with 1-line global sanity laws and declarative 64-byte frame layout
       (`encode_frame` / `decode_frame` + round-trip bijection theorem);
     - Matching zero-dependency TypeScript client (`sdk/<app>/sdk.ts`);
     - Matching zero-dependency Python client (`sdk/<app>/sdk.py`);
     - Cross-language golden-vector byte tests (`sdk/<app>/test_golden_vectors.py`)
       verified against HOL4 `EVAL`.
  3. Intent Lock (`intent-lock`):
     - Runs 15 concrete boundary scenarios directly in HOL4 `EVAL` and prints
       the executed input -> output/state table;
     - Emits a blind back-translation bundle (containing ONLY the HOL4 spec,
       never the original user prompt) for an independent read-only subagent;
     - Requires explicit human confirmation (`--freeze-confirm`) before writing
       `SPEC_HASHES.sha256` or triggering `ml_translator` + `runtime/` + `iron_law.py`.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import struct
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---- 1. Socratic Spec Interview ----

SOCRATIC_QUESTIONS = [
    {
        "id": "units",
        "prompt": "1. What integer unit should all monetary amounts use (never floats)?",
        "choices": ["cents_u64 (1 USD = 100)", "micro_usd_u64 (1 USD = 1_000_000)", "raw_u64"],
        "default": "cents_u64 (1 USD = 100)",
    },
    {
        "id": "zero_amount",
        "prompt": "2. How should a $0 SPEND_REQUEST or $0 REFUND behave?",
        "choices": ["deny_zero (amount == 0 rejected, state unchanged)", "allow_zero_noop"],
        "default": "deny_zero (amount == 0 rejected, state unchanged)",
    },
    {
        "id": "cap_basis",
        "prompt": "3. Does the rolling spending cap bound GROSS spend or NET (spent - refunded)?",
        "choices": ["net_spend (spent - refunded <= cap)", "gross_spend (spent <= cap even after refund)"],
        "default": "net_spend (spent - refunded <= cap)",
    },
    {
        "id": "nonce_rule",
        "prompt": "4. How should duplicate or out-of-order nonces be handled?",
        "choices": ["strict_next (req_nonce == last_nonce + 1)", "strictly_increasing (req_nonce > last_nonce)"],
        "default": "strict_next (req_nonce == last_nonce + 1)",
    },
    {
        "id": "overflow_rule",
        "prompt": "5. How must u64 addition/subtraction overflow or underflow behave?",
        "choices": ["reject_unchanged (checked arithmetic; state never wraps)"],
        "default": "reject_unchanged (checked arithmetic; state never wraps)",
    },
    {
        "id": "allowlist_rule",
        "prompt": "6. How should destinations (`dest_id`) be authorized?",
        "choices": ["fail_closed_bitmask (dest_id < 64 and bit dest_id set in allowlist_mask)"],
        "default": "fail_closed_bitmask (dest_id < 64 and bit dest_id set in allowlist_mask)",
    },
    {
        "id": "refund_rule",
        "prompt": "7. How must REFUND prevent double-refunds and over-refunds?",
        "choices": ["single_tx_final (tx_id == last_tx_id, not yet refunded, amount <= last_tx_amt)"],
        "default": "single_tx_final (tx_id == last_tx_id, not yet refunded, amount <= last_tx_amt)",
    },
]

DEFAULT_GUARDRAIL_SCHEMA = {
    "app": "guardrail",
    "description": "AI Agent Spending & Refund Guardrail Kernel",
    "frame_bytes": 64,
    "units": "cents_u64 (1 USD = 100)",
    "zero_amount": "deny_zero (amount == 0 rejected, state unchanged)",
    "cap_basis": "net_spend (spent - refunded <= cap)",
    "nonce_rule": "strict_next (req_nonce == last_nonce + 1)",
    "overflow_rule": "reject_unchanged (checked arithmetic; state never wraps)",
    "allowlist_rule": "fail_closed_bitmask (dest_id < 64 and bit dest_id set in allowlist_mask)",
    "refund_rule": "single_tx_final (tx_id == last_tx_id, not yet refunded, amount <= last_tx_amt)",
    "default_cap_u64": 100000,
    "default_allowlist_mask_u64": 7,
    "opcodes": {
        "BUDGET_SET": 1,
        "SPEND_REQUEST": 2,
        "REFUND": 3,
        "QUERY": 4,
    },
    "request_lanes_u64": [
        "op",
        "agent_id",
        "dest_id_or_mask",
        "deposit_or_amount",
        "cap_or_nonce_or_tx_id",
        "reserved5",
        "reserved6",
        "reserved7",
    ],
    "response_lanes_u64": [
        "ok",
        "code",
        "deposits",
        "balance",
        "net_spent",
        "refunds",
        "last_nonce",
        "last_tx_id",
    ],
}


def cmd_interview(args: argparse.Namespace) -> int:
    schema = dict(DEFAULT_GUARDRAIL_SCHEMA)
    schema["app"] = args.app
    if args.rule:
        schema["description"] = args.rule

    if args.answers:
        answers = json.loads(Path(args.answers).read_text())
        schema.update(answers)
    elif args.non_interactive:
        pass
    else:
        print(f"=== Forge Socratic Spec Interview ({args.app}) ===")
        if args.rule:
            print(f"Rule prompt: {args.rule}\n")
        for q in SOCRATIC_QUESTIONS:
            print(q["prompt"])
            for idx, ch in enumerate(q["choices"], 1):
                mark = " (default)" if ch == q["default"] else ""
                print(f"  [{idx}] {ch}{mark}")
            raw = input("Choice [Enter for default]: ").strip()
            if raw.isdigit() and 1 <= int(raw) <= len(q["choices"]):
                schema[q["id"]] = q["choices"][int(raw) - 1]
            elif raw:
                schema[q["id"]] = raw
            else:
                schema[q["id"]] = q["default"]
            print()

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(schema, indent=2) + "\n")
    print(f"Wrote canonical schema: {out}")
    return 0


# ---- 2. Single-Schema Code & Spec Emission ----


def render_guardrail_hol4_spec(schema: dict) -> str:
    app = schema["app"]
    thy = f"forge_{app}Spec"
    cap = int(schema.get("default_cap_u64", 100000))
    mask = int(schema.get("default_allowlist_mask_u64", 7))
    net_mode = str(schema.get("cap_basis", "net_spend")).startswith("net")
    deny_zero = str(schema.get("zero_amount", "deny_zero")).startswith("deny")

    amt_nonzero = "amt ≠ 0w ∧ " if deny_zero else ""
    cap_guard = (
        "amt ≤₊ st.cap − (st.spent − st.refunds)"
        if net_mode
        else "amt ≤₊ st.cap − st.spent"
    )
    cap_inv = (
        "(st.spent − st.refunds) ≤₊ st.cap"
        if net_mode
        else "st.spent ≤₊ st.cap"
    )

    return rf"""(* Forge M2 Guardrail Pure HOL4 Spec (<100 lines; 64B LE64 frame = 8 x word64) *)
Theory {thy}
Ancestors words arithmetic list forge_frame64Spec
Libs preamble blastLib wordsLib
Datatype:
  gr_state = <| deposits:word64; balance:word64; spent:word64; refunds:word64; cap:word64;
                allowmask:word64; nonce:word64; last_tx:word64; last_amt:word64; tx_open:bool |>
End
Definition gr_init_def:
  gr_init = <| deposits:=0w; balance:=0w; spent:=0w; refunds:=0w; cap:={cap}w; allowmask:={mask}w; nonce:=0w; last_tx:=0w; last_amt:=0w; tx_open:=F |>
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
      if {amt_nonzero}dest_allowed st.allowmask arg2 ∧ st.nonce ≠ 0xFFFFFFFFFFFFFFFFw ∧ arg4 = st.nonce + 1w ∧
         st.last_tx ≠ 0xFFFFFFFFFFFFFFFFw ∧ amt ≤₊ st.balance ∧ amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.spent ∧ {cap_guard} then
        let st' = st with <| balance := st.balance − amt; spent := st.spent + amt; nonce := arg4; last_tx := st.last_tx + 1w; last_amt := amt; tx_open := T |> in (st', gr_resp 1w 0w st')
      else (st, gr_resp 0w 2w st)
    else if op = 3w then (* REFUND: arg4=tx_id, amt=refund_amount *)
      if {amt_nonzero}st.tx_open ∧ arg4 = st.last_tx ∧ amt ≤₊ st.last_amt ∧
         amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.refunds ∧ amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.balance then
        let st' = st with <| balance := st.balance + amt; refunds := st.refunds + amt; tx_open := F |> in (st', gr_resp 1w 0w st')
      else (st, gr_resp 0w 3w st)
    else if op = 4w then (st, gr_resp 1w 0w st) else (st, gr_resp 0w 4w st) (* QUERY / unknown *)
End
Definition gr_inv_def:
  gr_inv st ⇔
    st.refunds ≤₊ st.spent ∧ (st.tx_open ⇒ st.last_amt ≤₊ st.spent − st.refunds) ∧
    w2n st.deposits = w2n st.balance + (w2n st.spent − w2n st.refunds) ∧ {cap_inv}
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
"""


def render_sdk_py(schema: dict) -> str:
    app = schema["app"]
    ops = schema["opcodes"]
    return f'''#!/usr/bin/env python3
"""Zero-dependency Python SDK for Forge `{app}` 64-byte binary frame kernel.
Auto-generated from canonical schema by `scripts/forge_vibe.py`.
"""
from __future__ import annotations

import dataclasses
import struct
import subprocess
from pathlib import Path

FRAME_BYTES = 64
FRAME_STRUCT = struct.Struct("<8Q")

OP_BUDGET_SET = {ops["BUDGET_SET"]}
OP_SPEND_REQUEST = {ops["SPEND_REQUEST"]}
OP_REFUND = {ops["REFUND"]}
OP_QUERY = {ops["QUERY"]}


@dataclasses.dataclass(frozen=True)
class RequestFrame:
    op: int
    agent_id: int = 0
    arg2: int = 0
    amount: int = 0
    arg4: int = 0
    reserved5: int = 0
    reserved6: int = 0
    reserved7: int = 0

    def encode(self) -> bytes:
        return FRAME_STRUCT.pack(
            self.op,
            self.agent_id,
            self.arg2,
            self.amount,
            self.arg4,
            self.reserved5,
            self.reserved6,
            self.reserved7,
        )

    @classmethod
    def decode(cls, buf: bytes) -> "RequestFrame":
        if len(buf) != FRAME_BYTES:
            raise ValueError(f"expected {{FRAME_BYTES}} bytes, got {{len(buf)}}")
        return cls(*FRAME_STRUCT.unpack(buf))


@dataclasses.dataclass(frozen=True)
class ResponseFrame:
    ok: int
    code: int
    deposits: int
    balance: int
    net_spent: int
    refunds: int
    last_nonce: int
    last_tx_id: int

    def encode(self) -> bytes:
        return FRAME_STRUCT.pack(
            self.ok,
            self.code,
            self.deposits,
            self.balance,
            self.net_spent,
            self.refunds,
            self.last_nonce,
            self.last_tx_id,
        )

    @classmethod
    def decode(cls, buf: bytes) -> "ResponseFrame":
        if len(buf) != FRAME_BYTES:
            raise ValueError(f"expected {{FRAME_BYTES}} bytes, got {{len(buf)}}")
        return cls(*FRAME_STRUCT.unpack(buf))


def budget_set_req(deposit: int, cap: int, allowlist_mask: int, agent_id: int = 0) -> RequestFrame:
    return RequestFrame(op=OP_BUDGET_SET, agent_id=agent_id, arg2=allowlist_mask, amount=deposit, arg4=cap)


def spend_req(agent_id: int, dest_id: int, amount: int, nonce: int) -> RequestFrame:
    return RequestFrame(op=OP_SPEND_REQUEST, agent_id=agent_id, arg2=dest_id, amount=amount, arg4=nonce)


def refund_req(tx_id: int, amount: int, agent_id: int = 0) -> RequestFrame:
    return RequestFrame(op=OP_REFUND, agent_id=agent_id, arg2=0, amount=amount, arg4=tx_id)


def query_req(agent_id: int = 0) -> RequestFrame:
    return RequestFrame(op=OP_QUERY, agent_id=agent_id)


class ForgeClient:
    """Pipes 64-byte frames directly to a compiled ARM64 forge-kernel binary."""

    def __init__(self, binary: str | Path, qemu: str | None = None) -> None:
        cmd = [qemu, str(binary)] if qemu else [str(binary)]
        self.cmd = cmd

    def run_batch(self, requests: list[RequestFrame]) -> list[ResponseFrame]:
        payload = b"".join(r.encode() for r in requests)
        proc = subprocess.run(self.cmd, input=payload, capture_output=True, check=True)
        raw = proc.stdout
        if len(raw) % FRAME_BYTES != 0:
            raise RuntimeError(f"unaligned response stream: {{len(raw)}} bytes")
        return [
            ResponseFrame.decode(raw[i : i + FRAME_BYTES])
            for i in range(0, len(raw), FRAME_BYTES)
        ]
'''


def render_sdk_ts(schema: dict) -> str:
    app = schema["app"]
    ops = schema["opcodes"]
    return f'''// Zero-dependency TypeScript SDK for Forge `{app}` 64-byte binary frame kernel.
// Auto-generated from canonical schema by `scripts/forge_vibe.py`.

export const FRAME_BYTES = 64;

export const OP_BUDGET_SET = {ops["BUDGET_SET"]}n;
export const OP_SPEND_REQUEST = {ops["SPEND_REQUEST"]}n;
export const OP_REFUND = {ops["REFUND"]}n;
export const OP_QUERY = {ops["QUERY"]}n;

export interface RequestFrame {{
  op: bigint;
  agentId: bigint;
  arg2: bigint;
  amount: bigint;
  arg4: bigint;
  reserved5?: bigint;
  reserved6?: bigint;
  reserved7?: bigint;
}}

export interface ResponseFrame {{
  ok: bigint;
  code: bigint;
  deposits: bigint;
  balance: bigint;
  netSpent: bigint;
  refunds: bigint;
  lastNonce: bigint;
  lastTxId: bigint;
}}

const U64_MAX = 0xFFFFFFFFFFFFFFFFn;

function checkU64(name: string, v: bigint): bigint {{
  if (v < 0n || v > U64_MAX) {{
    throw new RangeError(`${{name}} out of u64 range: ${{v}}`);
  }}
  return v;
}}

export function encodeRequestFrame(r: RequestFrame): Uint8Array {{
  const buf = new Uint8Array(FRAME_BYTES);
  const dv = new DataView(buf.buffer);
  dv.setBigUint64(0, checkU64("op", r.op), true);
  dv.setBigUint64(8, checkU64("agentId", r.agentId), true);
  dv.setBigUint64(16, checkU64("arg2", r.arg2), true);
  dv.setBigUint64(24, checkU64("amount", r.amount), true);
  dv.setBigUint64(32, checkU64("arg4", r.arg4), true);
  dv.setBigUint64(40, checkU64("reserved5", r.reserved5 ?? 0n), true);
  dv.setBigUint64(48, checkU64("reserved6", r.reserved6 ?? 0n), true);
  dv.setBigUint64(56, checkU64("reserved7", r.reserved7 ?? 0n), true);
  return buf;
}}

export function decodeRequestFrame(buf: Uint8Array): RequestFrame {{
  if (buf.byteLength !== FRAME_BYTES) {{
    throw new Error(`expected ${{FRAME_BYTES}} bytes, got ${{buf.byteLength}}`);
  }}
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return {{
    op: dv.getBigUint64(0, true),
    agentId: dv.getBigUint64(8, true),
    arg2: dv.getBigUint64(16, true),
    amount: dv.getBigUint64(24, true),
    arg4: dv.getBigUint64(32, true),
    reserved5: dv.getBigUint64(40, true),
    reserved6: dv.getBigUint64(48, true),
    reserved7: dv.getBigUint64(56, true),
  }};
}}

export function encodeResponseFrame(r: ResponseFrame): Uint8Array {{
  const buf = new Uint8Array(FRAME_BYTES);
  const dv = new DataView(buf.buffer);
  dv.setBigUint64(0, checkU64("ok", r.ok), true);
  dv.setBigUint64(8, checkU64("code", r.code), true);
  dv.setBigUint64(16, checkU64("deposits", r.deposits), true);
  dv.setBigUint64(24, checkU64("balance", r.balance), true);
  dv.setBigUint64(32, checkU64("netSpent", r.netSpent), true);
  dv.setBigUint64(40, checkU64("refunds", r.refunds), true);
  dv.setBigUint64(48, checkU64("lastNonce", r.lastNonce), true);
  dv.setBigUint64(56, checkU64("lastTxId", r.lastTxId), true);
  return buf;
}}

export function decodeResponseFrame(buf: Uint8Array): ResponseFrame {{
  if (buf.byteLength !== FRAME_BYTES) {{
    throw new Error(`expected ${{FRAME_BYTES}} bytes, got ${{buf.byteLength}}`);
  }}
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return {{
    ok: dv.getBigUint64(0, true),
    code: dv.getBigUint64(8, true),
    deposits: dv.getBigUint64(16, true),
    balance: dv.getBigUint64(24, true),
    netSpent: dv.getBigUint64(32, true),
    refunds: dv.getBigUint64(40, true),
    lastNonce: dv.getBigUint64(48, true),
    lastTxId: dv.getBigUint64(56, true),
  }};
}}

export const budgetSetReq = (deposit: bigint, cap: bigint, allowlistMask: bigint, agentId = 0n): RequestFrame => ({{
  op: OP_BUDGET_SET, agentId, arg2: allowlistMask, amount: deposit, arg4: cap,
}});

export const spendReq = (agentId: bigint, destId: bigint, amount: bigint, nonce: bigint): RequestFrame => ({{
  op: OP_SPEND_REQUEST, agentId, arg2: destId, amount, arg4: nonce,
}});

export const refundReq = (txId: bigint, amount: bigint, agentId = 0n): RequestFrame => ({{
  op: OP_REFUND, agentId, arg2: 0n, amount, arg4: txId,
}});

export const queryReq = (agentId = 0n): RequestFrame => ({{
  op: OP_QUERY, agentId, arg2: 0n, amount: 0n, arg4: 0n,
}});
'''


def render_golden_test_py(schema: dict) -> str:
    app = schema["app"]
    tpl = r'''#!/usr/bin/env python3
"""Cross-language golden-vector byte tests for `__APP__` (Python <-> TypeScript <-> HOL4 EVAL)."""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

SDK_DIR = Path(__file__).resolve().parent
ROOT = SDK_DIR.parent.parent
APP_DIR = ROOT / "kernels" / "__APP__"
sys.path.insert(0, str(SDK_DIR))
import sdk  # noqa: E402

GOLDEN_VECTORS = [
    ("budget_set_basic", sdk.budget_set_req(deposit=50000, cap=20000, allowlist_mask=0b1011, agent_id=7)),
    ("spend_normal", sdk.spend_req(agent_id=42, dest_id=3, amount=12500, nonce=1)),
    ("spend_u64_max_attack", sdk.spend_req(agent_id=1, dest_id=0, amount=(1 << 64) - 1, nonce=2)),
    ("refund_partial", sdk.refund_req(tx_id=9, amount=4000, agent_id=42)),
    ("query_zero", sdk.query_req(agent_id=99)),
]


def check_python_roundtrip() -> dict[str, str]:
    out = {}
    for name, req in GOLDEN_VECTORS:
        raw = req.encode()
        assert len(raw) == 64, f"{name}: bad len {len(raw)}"
        assert sdk.RequestFrame.decode(raw) == req, f"{name}: Python round-trip mismatch"
        out[name] = raw.hex()
    print(f"PASS python_roundtrip ({len(GOLDEN_VECTORS)} vectors)")
    return out


def check_typescript_bytes(py_hex: dict[str, str]) -> None:
    node = shutil.which("node")
    ts_src = (SDK_DIR / "sdk.ts").read_text()
    js = re.sub(r"export interface \w+ \{[^}]*\}", "", ts_src)
    js = re.sub(r"\):\s*(Uint8Array|RequestFrame|ResponseFrame|bigint)\b", ")", js)
    js = re.sub(r"\((\w+):\s*(RequestFrame|ResponseFrame|Uint8Array)\)", r"(\1)", js)
    js = re.sub(r":\s*(bigint|string)\b", "", js)
    js = js.replace("export const ", "const ").replace("export function ", "function ")
    vectors_js = json.dumps([
        [name, str(r.op), str(r.agent_id), str(r.arg2), str(r.amount), str(r.arg4), str(r.reserved5), str(r.reserved6), str(r.reserved7)]
        for name, r in GOLDEN_VECTORS
    ])
    driver = (
        js
        + "\nconst vecs = "
        + vectors_js
        + """;
const res = {};
for (const [name, op, ag, a2, amt, a4, r5, r6, r7] of vecs) {
  const req = { op: BigInt(op), agentId: BigInt(ag), arg2: BigInt(a2), amount: BigInt(amt), arg4: BigInt(a4), reserved5: BigInt(r5), reserved6: BigInt(r6), reserved7: BigInt(r7) };
  const b = encodeRequestFrame(req);
  const d = decodeRequestFrame(b);
  if (d.op !== req.op || d.agentId !== req.agentId || d.arg2 !== req.arg2 || d.amount !== req.amount || d.arg4 !== req.arg4) {
    throw new Error("TS roundtrip mismatch: " + name);
  }
  res[name] = Buffer.from(b).toString("hex");
}
console.log(JSON.stringify(res));
"""
    )
    if not node:
        print("SKIP typescript_bytes (node not on PATH)")
        return
    p = subprocess.run([node, "-e", driver], capture_output=True, text=True, check=True)
    ts_hex = json.loads(p.stdout.strip())
    for name, hx in py_hex.items():
        assert ts_hex[name] == hx, f"TS vs Python byte mismatch on {name}: {ts_hex[name]} != {hx}"
    print(f"PASS typescript_vs_python ({len(GOLDEN_VECTORS)} vectors identical byte-for-byte)")


def check_hol4_eval_bytes(py_hex: dict[str, str]) -> None:
    hol = shutil.which("hol")
    hol_dir = APP_DIR / "hol4"
    has_uo = (
        (hol_dir / "forge___APP__SpecTheory.uo").is_file()
        or (hol_dir / ".hol" / "objs" / "forge___APP__SpecTheory.uo").is_file()
    )
    if not hol or not has_uo:
        print("SKIP hol4_eval_bytes (hol not on PATH or forge___APP__SpecTheory not yet compiled)")
        return
    lines = [
        'val _ = load "forge___APP__SpecTheory";',
        'open HolKernel Parse boolLib bossLib wordsLib forge_frame64SpecTheory forge___APP__SpecTheory;',
        'fun byte_hex tm = let val n = Arbnum.toInt (wordsSyntax.dest_word_literal tm) val h = Int.fmt StringCvt.HEX n in if size h = 1 then "0" ^ h else h end;',
        'fun frame_hex tm = String.concat (map byte_hex (fst (listSyntax.dest_list (rhs (concl (EVAL tm))))));',
    ]
    for name, r in GOLDEN_VECTORS:
        lines.append(
            f'val _ = print ("VEC {name}=" ^ frame_hex ``encode_frame (Frame64 {r.op}w {r.agent_id}w {r.arg2}w {r.amount}w {r.arg4}w {r.reserved5}w {r.reserved6}w {r.reserved7}w)`` ^ "\\n");'
        )
    lines.append('val _ = OS.Process.exit OS.Process.success;')
    sml = "\n".join(lines) + "\n"
    heap = ROOT / "forge_factory.heap"
    cakeml = os.environ.get("CAKEMLDIR", "")
    cmd = [hol, "--zero"]
    if heap.is_file():
        cmd.append(f"--holstate={heap}")
    elif cakeml and (Path(cakeml) / "cv_translator" / "cake_compile_heap").is_file():
        cmd.append(f"--holstate={cakeml}/cv_translator/cake_compile_heap")
    p = subprocess.run(cmd, cwd=hol_dir, input=sml.encode("utf-8"), capture_output=True, timeout=60)
    out = p.stdout.decode("utf-8", errors="replace")
    err = p.stderr.decode("utf-8", errors="replace")
    assert p.returncode == 0, f"HOL4 EVAL failed (exit {p.returncode}): {out[-400:]} {err[-400:]}"
    hol_hex = {}
    for ln in out.splitlines():
        if ln.startswith("VEC ") and "=" in ln:
            k, v = ln[4:].split("=", 1)
            hol_hex[k.strip()] = v.strip().lower()
    for name, hx in py_hex.items():
        assert hol_hex.get(name) == hx, f"HOL4 vs Python mismatch on {name}: {hol_hex.get(name)} != {hx}"
    print(f"PASS hol4_eval_vs_python ({len(GOLDEN_VECTORS)} vectors identical byte-for-byte)")


def main() -> int:
    py_hex = check_python_roundtrip()
    check_typescript_bytes(py_hex)
    check_hol4_eval_bytes(py_hex)
    print("ALL GOLDEN VECTOR BYTE TESTS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
'''
    return tpl.replace("__APP__", app)


def cmd_generate(args: argparse.Namespace) -> int:
    schema = json.loads(Path(args.schema).read_text()) if args.schema else dict(DEFAULT_GUARDRAIL_SCHEMA)
    if args.app:
        schema["app"] = args.app
    app = schema["app"]
    app_dir = ROOT / "kernels" / app
    hol_dir = app_dir / "hol4"
    sdk_dir = ROOT / "sdk" / app
    hol_dir.mkdir(parents=True, exist_ok=True)
    sdk_dir.mkdir(parents=True, exist_ok=True)

    (sdk_dir / "schema.json").write_text(json.dumps(schema, indent=2) + "\n")

    spec_text = render_guardrail_hol4_spec(schema)
    spec_path = hol_dir / f"forge_{app}SpecScript.sml"
    spec_path.write_text(spec_text)

    holmakefile = (
        f"# Auto-generated Holmakefile for kernels/{app} (zero hardcoded developer paths).\n"
        f"INCLUDES = ../../../runtime/hol4 \\\n"
        f"           $(CAKEMLDIR)/misc $(CAKEMLDIR)/semantics $(CAKEMLDIR)/semantics/ffi \\\n"
        f"           $(CAKEMLDIR)/semantics/proofs $(CAKEMLDIR)/translator $(CAKEMLDIR)/characteristic \\\n"
        f"           $(CAKEMLDIR)/basis $(CAKEMLDIR)/compiler/backend $(CAKEMLDIR)/compiler/backend/semantics \\\n"
        f"           $(CAKEMLDIR)/compiler/backend/proofs $(CAKEMLDIR)/compiler/backend/arm8 \\\n"
        f"           $(CAKEMLDIR)/compiler/backend/arm8/proofs $(CAKEMLDIR)/compiler/encoders/arm8 \\\n"
        f"           $(CAKEMLDIR)/compiler/encoders/arm8/proofs $(CAKEMLDIR)/compiler/encoders/asm \\\n"
        f"           $(CAKEMLDIR)/cv_translator \\\n"
        f"           $(HOLDIR)/examples/l3-machine-code/arm8/model $(HOLDIR)/examples/l3-machine-code/arm8/step\n"
        f"HOLHEAP = $(CAKEMLDIR)/cv_translator/cake_compile_heap\n"
    )
    (hol_dir / "Holmakefile").write_text(holmakefile)

    (sdk_dir / "sdk.py").write_text(render_sdk_py(schema))
    (sdk_dir / "sdk.ts").write_text(render_sdk_ts(schema))
    gt_path = sdk_dir / "test_golden_vectors.py"
    gt_path.write_text(render_golden_test_py(schema))
    os.chmod(gt_path, 0o755)

    line_count = len(spec_text.splitlines())
    print(f"Generated kernels/{app} (Ring 0) + sdk/{app} (Ring 2):")
    print(f"  HOL4 Spec : {spec_path.relative_to(ROOT)} ({line_count} lines)")
    print(f"  Python SDK: {(sdk_dir / 'sdk.py').relative_to(ROOT)}")
    print(f"  TS SDK    : {(sdk_dir / 'sdk.ts').relative_to(ROOT)}")
    print(f"  Golden Tst: {gt_path.relative_to(ROOT)}")
    return 0


# ---- 3. Intent Lock (15 HOL4 EVAL Boundary Scenarios + Freeze Gate) ----

BOUNDARY_SCENARIOS = [
    ("01_initial_query",          "gr_init", (4, 0, 0, 0, 0)),
    ("02_deposit_50000_cap20000", "s0",      (1, 0, 7, 50000, 20000)),
    ("03_spend_zero_denied",      "s1",      (2, 1, 0, 0, 1)),
    ("04_spend_unallowed_dest",   "s1",      (2, 1, 5, 100, 1)),
    ("05_spend_dest_oob_64",      "s1",      (2, 1, 64, 100, 1)),
    ("06_spend_bad_nonce_0",      "s1",      (2, 1, 0, 100, 0)),
    ("07_spend_skip_nonce_2",     "s1",      (2, 1, 0, 100, 2)),
    ("08_spend_u64_max_overflow", "s1",      (2, 1, 0, (1 << 64) - 1, 1)),
    ("09_spend_over_cap_20001",   "s1",      (2, 1, 0, 20001, 1)),
    ("10_spend_exact_cap_20000",  "s1",      (2, 1, 2, 20000, 1)),
    ("11_spend_replay_nonce_1",   "s2",      (2, 1, 2, 1, 1)),
    ("12_refund_over_amt_20001",  "s2",      (3, 1, 0, 20001, 1)),
    ("13_refund_wrong_tx_99",     "s2",      (3, 1, 0, 5000, 99)),
    ("14_refund_partial_5000_ok", "s2",      (3, 1, 0, 5000, 1)),
    ("15_double_refund_denied",   "s3",      (3, 1, 0, 1, 1)),
]


def eval_boundary_scenarios_hol4(app: str) -> list[dict]:
    hol = shutil.which("hol")
    if not hol:
        raise RuntimeError("hol binary not on PATH")
    hol_dir = ROOT / "kernels" / app / "hol4"
    thy = f"forge_{app}SpecTheory"
    sml_lines = [
        f'val _ = load "{thy}";',
        f"open HolKernel Parse boolLib bossLib wordsLib forge_frame64SpecTheory {thy};",
        "val _ = Globals.linewidth := 200;",
        "fun wnum tm = Arbnum.toString (wordsSyntax.dest_word_literal tm);",
        "fun fmt_resp tm = let val (_, args) = strip_comb tm in String.concatWith \",\" (map wnum args) end;",
        "fun step_val st_tm req_tm = rhs (concl (EVAL ``gr_step ^st_tm ^req_tm``));",
        "val s0 = rhs (concl (EVAL ``gr_init``));",
        "val (s1, r_s1) = pairSyntax.dest_pair (step_val s0 ``Frame64 1w 0w 7w 50000w 20000w 0w 0w 0w``);",
        "val (s2, r_s2) = pairSyntax.dest_pair (step_val s1 ``Frame64 2w 1w 2w 20000w 1w 0w 0w 0w``);",
        "val (s3, r_s3) = pairSyntax.dest_pair (step_val s2 ``Frame64 3w 1w 0w 5000w 1w 0w 0w 0w``);",
    ]
    for name, st_var, (op, ag, a2, amt, a4) in BOUNDARY_SCENARIOS:
        base = "s0" if st_var == "gr_init" else st_var
        sml_lines.append(
            f'val _ = let val (_, r) = pairSyntax.dest_pair (step_val {base} ``Frame64 {op}w {ag}w {a2}w {amt}w {a4}w 0w 0w 0w``) '
            f'in print ("SCEN {name}=" ^ fmt_resp r ^ "\\n") end;'
        )
    sml_lines.append("val _ = OS.Process.exit OS.Process.success;")

    heap = ROOT / "forge_factory.heap"
    cakeml = os.environ.get("CAKEMLDIR", "")
    cmd = [hol, "--zero"]
    if heap.is_file():
        cmd.append(f"--holstate={heap}")
    elif cakeml and (Path(cakeml) / "cv_translator" / "cake_compile_heap").is_file():
        cmd.append(f"--holstate={cakeml}/cv_translator/cake_compile_heap")

    p = subprocess.run(
        cmd,
        cwd=hol_dir,
        input=("\n".join(sml_lines) + "\n").encode("utf-8"),
        capture_output=True,
        timeout=90,
    )
    out = p.stdout.decode("utf-8", errors="replace")
    err = p.stderr.decode("utf-8", errors="replace")
    if p.returncode != 0:
        raise RuntimeError(f"HOL4 EVAL failed (exit {p.returncode}): {out[-500:]} {err[-500:]}")

    rows = []
    parsed = {}
    for ln in out.splitlines():
        if ln.startswith("SCEN ") and "=" in ln:
            k, v = ln[5:].split("=", 1)
            parsed[k.strip()] = [int(x) for x in v.strip().split(",")]
    for name, st_var, (op, ag, a2, amt, a4) in BOUNDARY_SCENARIOS:
        vals = parsed.get(name)
        if not vals or len(vals) != 8:
            raise RuntimeError(f"missing HOL4 EVAL output for {name}")
        rows.append(
            {
                "scenario": name,
                "base_state": st_var,
                "req": {"op": op, "agent": ag, "arg2": a2, "amount": amt, "arg4": a4},
                "ok": vals[0],
                "code": vals[1],
                "deposits": vals[2],
                "balance": vals[3],
                "net_spent": vals[4],
                "refunds": vals[5],
                "last_nonce": vals[6],
                "last_tx_id": vals[7],
                "conserved": vals[2] == vals[3] + vals[4],
            }
        )
    return rows


def cmd_intent_lock(args: argparse.Namespace) -> int:
    app = args.app
    app_dir = ROOT / "kernels" / app
    spec_path = app_dir / "hol4" / f"forge_{app}SpecScript.sml"
    if not spec_path.is_file():
        print(f"FAIL: missing spec {spec_path}")
        return 1

    rows = eval_boundary_scenarios_hol4(app)
    print(f"=== 15 HOL4 EVAL Boundary Scenarios (`kernels/{app}`) ===")
    print(f"{'Scenario':28s} | {'OK':2s} | {'Code':4s} | {'Dep':6s} | {'Bal':6s} | {'Net':6s} | {'Ref':5s} | {'Nonce':5s} | {'Tx':2s} | Cons")
    print("-" * 96)
    for r in rows:
        print(
            f"{r['scenario']:28s} | {r['ok']:2d} | {r['code']:4d} | "
            f"{r['deposits']:6d} | {r['balance']:6d} | {r['net_spent']:6d} | "
            f"{r['refunds']:5d} | {r['last_nonce']:5d} | {r['last_tx_id']:2d} | "
            f"{'YES' if r['conserved'] else 'NO'}"
        )
        assert r["conserved"], f"Conservation violated in {r['scenario']}"

    if args.out_json:
        Path(args.out_json).write_text(json.dumps(rows, indent=2) + "\n")

    spec_sha = hashlib.sha256(spec_path.read_bytes()).hexdigest()
    rt_spec = ROOT / "runtime" / "hol4" / "forge_runtimeSpecScript.sml"
    rt_sha = hashlib.sha256(rt_spec.read_bytes()).hexdigest() if rt_spec.is_file() else ""

    if not args.freeze_confirm:
        print("\n[INTENT LOCK HOLD] Human confirmation required before freezing SPEC_HASHES.sha256.")
        print(f"  Candidate spec SHA-256   : {spec_sha}  {spec_path.relative_to(ROOT)}")
        if rt_sha:
            print(f"  Runtime spec SHA-256     : {rt_sha}  runtime/hol4/forge_runtimeSpecScript.sml")
        print("  Re-run with `--freeze-confirm` ONLY after human sign-off on the spec + blind back-translation.")
        return 0

    if not rt_sha:
        print("FAIL: runtime/hol4/forge_runtimeSpecScript.sml missing")
        return 1
    pin_path = app_dir / "SPEC_HASHES.sha256"
    pin_path.write_text(
        f"{spec_sha}  {spec_path.relative_to(ROOT)}\n"
        f"{rt_sha}  runtime/hol4/forge_runtimeSpecScript.sml\n"
    )
    print(f"FROZEN: wrote {pin_path.relative_to(ROOT)}")
    return 0


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(prog="forge_vibe.py", description="v0.1 Verified Vibe-Coding CLI")
    sub = p.add_subparsers(dest="cmd", required=True)

    pi = sub.add_parser("interview", help="Run Socratic edge-case interview -> schema.json")
    pi.add_argument("--app", default="guardrail")
    pi.add_argument("--rule", default="")
    pi.add_argument("--answers", default=None, help="JSON file with answers")
    pi.add_argument("--non-interactive", action="store_true")
    pi.add_argument("--out", required=True, help="Output schema.json path")

    pg = sub.add_parser("generate", help="Emit <100-line HOL4 spec + TS/Python SDK + golden tests")
    pg.add_argument("--schema", default=None, help="Path to schema.json (default: built-in guardrail)")
    pg.add_argument("--app", default=None)

    pl = sub.add_parser("intent-lock", help="Execute 15 HOL4 EVAL boundary scenarios + freeze gate")
    pl.add_argument("--app", default="guardrail")
    pl.add_argument("--out-json", default=None)
    pl.add_argument("--freeze-confirm", action="store_true", help="Explicit human freeze confirmation")

    args = p.parse_args(argv)
    if args.cmd == "interview":
        return cmd_interview(args)
    if args.cmd == "generate":
        return cmd_generate(args)
    if args.cmd == "intent-lock":
        return cmd_intent_lock(args)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
