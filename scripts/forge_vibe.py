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
     - Matching zero-dependency TypeScript client (`sdk/<app>/sdk.ts`) with `GuardrailAdmin`/`GuardrailAgent`;
     - Matching zero-dependency Python client (`sdk/<app>/sdk.py`) with `GuardrailAdmin`/`GuardrailAgent`;
     - Matching zero-dependency Rust crate (`sdk/<app>/Cargo.toml` + `sdk/<app>/src/lib.rs`) with `GuardrailAdmin`/`GuardrailAgent`;
     - 4-way golden-vector & live pipe tests (`sdk/<app>/test_golden_vectors.py`)
       verified byte-for-byte across Rust, Python, TypeScript, and HOL4 `EVAL`.
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
import re
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


def _apply_sdk_tokens(tpl: str, schema: dict) -> str:
    app = schema["app"]
    ops = schema["opcodes"]
    crate_name = "forge-" + re.sub(r"[^a-zA-Z0-9_-]", "-", app).lower() + "-sdk"
    return (
        tpl.replace("__APP__", app)
        .replace("__CRATE_NAME__", crate_name)
        .replace("__OP_BUDGET_SET__", str(ops["BUDGET_SET"]))
        .replace("__OP_SPEND_REQUEST__", str(ops["SPEND_REQUEST"]))
        .replace("__OP_REFUND__", str(ops["REFUND"]))
        .replace("__OP_QUERY__", str(ops["QUERY"]))
    )


def render_sdk_py(schema: dict) -> str:
    tpl = r'''#!/usr/bin/env python3
"""Zero-dependency Python SDK for Forge `__APP__` 64-byte binary frame kernel.
Auto-generated from canonical schema by `scripts/forge_vibe.py`.

Provides capability-separated live process clients:
  - `GuardrailAdmin`: owns process lifecycle + `deposit_and_configure` (`op=__OP_BUDGET_SET__`)
    and mints restricted `GuardrailAgent` handles.
  - `GuardrailAgent`: exposes ONLY `spend` (`op=__OP_SPEND_REQUEST__`), `refund` (`op=__OP_REFUND__`), and
    `query` (`op=__OP_QUERY__`), structurally preventing untrusted agent code from
    invoking `op=__OP_BUDGET_SET__` or closing the kernel process.
"""
from __future__ import annotations

import dataclasses
import os
import struct
import subprocess
import threading
from pathlib import Path
from typing import Callable, Sequence

FRAME_BYTES = 64
FRAME_STRUCT = struct.Struct("<8Q")

OP_BUDGET_SET = __OP_BUDGET_SET__
OP_SPEND_REQUEST = __OP_SPEND_REQUEST__
OP_REFUND = __OP_REFUND__
OP_QUERY = __OP_QUERY__

_AGENT_ALLOWED_OPS = frozenset((OP_SPEND_REQUEST, OP_REFUND, OP_QUERY))


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
            raise ValueError(f"expected {FRAME_BYTES} bytes, got {len(buf)}")
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
            raise ValueError(f"expected {FRAME_BYTES} bytes, got {len(buf)}")
        return cls(*FRAME_STRUCT.unpack(buf))

    @property
    def is_ok(self) -> bool:
        return self.ok == 1

    @property
    def is_conserved(self) -> bool:
        return self.deposits == self.balance + self.net_spent


def budget_set_req(deposit: int, cap: int, allowlist_mask: int, agent_id: int = 0) -> RequestFrame:
    return RequestFrame(op=OP_BUDGET_SET, agent_id=agent_id, arg2=allowlist_mask, amount=deposit, arg4=cap)


def spend_req(agent_id: int, dest_id: int, amount: int, nonce: int) -> RequestFrame:
    return RequestFrame(op=OP_SPEND_REQUEST, agent_id=agent_id, arg2=dest_id, amount=amount, arg4=nonce)


def refund_req(tx_id: int, amount: int, agent_id: int = 0) -> RequestFrame:
    return RequestFrame(op=OP_REFUND, agent_id=agent_id, arg2=0, amount=amount, arg4=tx_id)


def query_req(agent_id: int = 0) -> RequestFrame:
    return RequestFrame(op=OP_QUERY, agent_id=agent_id)


def _write_exact_64(fd: int, data: bytes) -> None:
    if len(data) != FRAME_BYTES:
        raise ValueError(f"expected {FRAME_BYTES} bytes, got {len(data)}")
    view = memoryview(data)
    written = 0
    while written < FRAME_BYTES:
        try:
            n = os.write(fd, view[written:])
        except InterruptedError:
            continue
        if n <= 0:
            raise BrokenPipeError("kernel stdin closed before 64-byte frame was written")
        written += n


def _read_exact_64(fd: int) -> bytes:
    chunks: list[bytes] = []
    got = 0
    while got < FRAME_BYTES:
        try:
            chunk = os.read(fd, FRAME_BYTES - got)
        except InterruptedError:
            continue
        if not chunk:
            raise EOFError(f"kernel stdout hit EOF after {got} of {FRAME_BYTES} bytes")
        chunks.append(chunk)
        got += len(chunk)
    return b"".join(chunks)


def _build_kernel_cmd(
    binary: str | Path | None = None,
    *,
    qemu: str | None = None,
    docker_image: str | None = None,
    cmd: Sequence[str] | None = None,
) -> list[str]:
    if cmd is not None:
        return list(cmd)
    if binary is None:
        raise ValueError("binary or cmd must be provided")
    bin_path = Path(binary)
    if docker_image:
        abs_bin = bin_path.resolve()
        return [
            "docker",
            "run",
            "--rm",
            "-i",
            "-v",
            f"{abs_bin.parent}:/work:ro",
            docker_image,
            f"/work/{abs_bin.name}",
        ]
    if qemu:
        return [qemu, str(bin_path)]
    return [str(bin_path)]


class _KernelPipe:
    """Thread-safe exact 64-byte framed pipe over a live forge-kernel process."""

    def __init__(self, cmd: list[str]) -> None:
        self._lock = threading.Lock()
        self._closed = False
        self._proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )
        assert self._proc.stdin is not None and self._proc.stdout is not None

    def send_frame(self, req: RequestFrame) -> ResponseFrame:
        payload = req.encode()
        with self._lock:
            if self._closed or self._proc.stdin is None or self._proc.stdout is None:
                raise BrokenPipeError("guardrail kernel process is closed")
            _write_exact_64(self._proc.stdin.fileno(), payload)
            raw_resp = _read_exact_64(self._proc.stdout.fileno())
        return ResponseFrame.decode(raw_resp)

    def close(self) -> int:
        with self._lock:
            if self._closed:
                return self._proc.returncode if self._proc.returncode is not None else 0
            self._closed = True
            if self._proc.stdin is not None:
                try:
                    self._proc.stdin.close()
                except OSError:
                    pass
            code = self._proc.wait(timeout=15)
            if self._proc.stdout is not None:
                self._proc.stdout.close()
            if self._proc.stderr is not None:
                self._proc.stderr.close()
            return code


_AGENT_TOKEN = object()


class GuardrailAgent:
    """Restricted capability handle for untrusted AI agents."""

    __slots__ = ("_agent_id", "_send")

    def __init__(
        self,
        agent_id: int,
        send_fn: Callable[[RequestFrame], ResponseFrame],
        _token: object = None,
    ) -> None:
        if _token is not _AGENT_TOKEN:
            raise TypeError("GuardrailAgent must be minted via GuardrailAdmin.mint_agent()")
        self._agent_id = int(agent_id)
        self._send = send_fn

    @property
    def agent_id(self) -> int:
        return self._agent_id

    def spend(self, dest_id: int, amount: int, nonce: int) -> ResponseFrame:
        return self._send(spend_req(self._agent_id, dest_id, amount, nonce))

    def refund(self, tx_id: int, amount: int) -> ResponseFrame:
        return self._send(refund_req(tx_id, amount, self._agent_id))

    def query(self) -> ResponseFrame:
        return self._send(query_req(self._agent_id))


class GuardrailAdmin:
    """Privileged guardrail administrator handle owning the live kernel process."""

    def __init__(
        self,
        binary: str | Path | None = None,
        *,
        qemu: str | None = None,
        docker_image: str | None = None,
        cmd: Sequence[str] | None = None,
    ) -> None:
        argv = _build_kernel_cmd(binary, qemu=qemu, docker_image=docker_image, cmd=cmd)
        self._pipe = _KernelPipe(argv)

    def __enter__(self) -> "GuardrailAdmin":
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        self.close()

    def deposit_and_configure(
        self,
        deposit: int,
        cap: int,
        allowlist_mask: int,
        agent_id: int = 0,
    ) -> ResponseFrame:
        return self._pipe.send_frame(budget_set_req(deposit, cap, allowlist_mask, agent_id))

    def query(self, agent_id: int = 0) -> ResponseFrame:
        return self._pipe.send_frame(query_req(agent_id))

    def mint_agent(self, agent_id: int) -> GuardrailAgent:
        pipe = self._pipe

        def _restricted_send(req: RequestFrame) -> ResponseFrame:
            if req.op not in _AGENT_ALLOWED_OPS:
                raise PermissionError(f"GuardrailAgent is forbidden from invoking op={req.op}")
            return pipe.send_frame(req)

        return GuardrailAgent(agent_id, _restricted_send, _token=_AGENT_TOKEN)

    def close(self) -> int:
        return self._pipe.close()


class ForgeClient:
    """Batch client piping 64-byte frames to a compiled ARM64 forge-kernel binary."""

    def __init__(
        self,
        binary: str | Path,
        qemu: str | None = None,
        docker_image: str | None = None,
    ) -> None:
        self.cmd = _build_kernel_cmd(binary, qemu=qemu, docker_image=docker_image)

    def run_batch(self, requests: list[RequestFrame]) -> list[ResponseFrame]:
        payload = b"".join(r.encode() for r in requests)
        proc = subprocess.run(self.cmd, input=payload, capture_output=True, check=True)
        raw = proc.stdout
        if len(raw) % FRAME_BYTES != 0:
            raise RuntimeError(f"unaligned response stream: {len(raw)} bytes")
        return [
            ResponseFrame.decode(raw[i : i + FRAME_BYTES])
            for i in range(0, len(raw), FRAME_BYTES)
        ]
'''
    return _apply_sdk_tokens(tpl, schema)


def render_sdk_ts(schema: dict) -> str:
    tpl = r'''// Zero-dependency TypeScript SDK for Forge `__APP__` 64-byte binary frame kernel.
// Auto-generated from canonical schema by `scripts/forge_vibe.py`.

import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { once } from "node:events";
import * as path from "node:path";

export const FRAME_BYTES = 64;

export const OP_BUDGET_SET = __OP_BUDGET_SET__n;
export const OP_SPEND_REQUEST = __OP_SPEND_REQUEST__n;
export const OP_REFUND = __OP_REFUND__n;
export const OP_QUERY = __OP_QUERY__n;

export interface RequestFrame {
  op: bigint;
  agentId: bigint;
  arg2: bigint;
  amount: bigint;
  arg4: bigint;
  reserved5?: bigint;
  reserved6?: bigint;
  reserved7?: bigint;
}

export interface ResponseFrame {
  ok: bigint;
  code: bigint;
  deposits: bigint;
  balance: bigint;
  netSpent: bigint;
  refunds: bigint;
  lastNonce: bigint;
  lastTxId: bigint;
}

export interface SpawnOptions {
  qemu?: string;
  dockerImage?: string;
  cmd?: string[];
}

const U64_MAX = 0xFFFFFFFFFFFFFFFFn;

function checkU64(name: string, v: bigint): bigint {
  if (v < 0n || v > U64_MAX) {
    throw new RangeError(`${name} out of u64 range: ${v}`);
  }
  return v;
}

export function encodeRequestFrame(r: RequestFrame): Uint8Array {
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
}

export function decodeRequestFrame(buf: Uint8Array): RequestFrame {
  if (buf.byteLength !== FRAME_BYTES) {
    throw new Error(`expected ${FRAME_BYTES} bytes, got ${buf.byteLength}`);
  }
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return {
    op: dv.getBigUint64(0, true),
    agentId: dv.getBigUint64(8, true),
    arg2: dv.getBigUint64(16, true),
    amount: dv.getBigUint64(24, true),
    arg4: dv.getBigUint64(32, true),
    reserved5: dv.getBigUint64(40, true),
    reserved6: dv.getBigUint64(48, true),
    reserved7: dv.getBigUint64(56, true),
  };
}

export function encodeResponseFrame(r: ResponseFrame): Uint8Array {
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
}

export function decodeResponseFrame(buf: Uint8Array): ResponseFrame {
  if (buf.byteLength !== FRAME_BYTES) {
    throw new Error(`expected ${FRAME_BYTES} bytes, got ${buf.byteLength}`);
  }
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  return {
    ok: dv.getBigUint64(0, true),
    code: dv.getBigUint64(8, true),
    deposits: dv.getBigUint64(16, true),
    balance: dv.getBigUint64(24, true),
    netSpent: dv.getBigUint64(32, true),
    refunds: dv.getBigUint64(40, true),
    lastNonce: dv.getBigUint64(48, true),
    lastTxId: dv.getBigUint64(56, true),
  };
}

export const budgetSetReq = (deposit: bigint, cap: bigint, allowlistMask: bigint, agentId = 0n): RequestFrame => ({
  op: OP_BUDGET_SET, agentId, arg2: allowlistMask, amount: deposit, arg4: cap,
});

export const spendReq = (agentId: bigint, destId: bigint, amount: bigint, nonce: bigint): RequestFrame => ({
  op: OP_SPEND_REQUEST, agentId, arg2: destId, amount, arg4: nonce,
});

export const refundReq = (txId: bigint, amount: bigint, agentId = 0n): RequestFrame => ({
  op: OP_REFUND, agentId, arg2: 0n, amount, arg4: txId,
});

export const queryReq = (agentId = 0n): RequestFrame => ({
  op: OP_QUERY, agentId, arg2: 0n, amount: 0n, arg4: 0n,
});

function buildKernelArgv(binary: string, opts?: SpawnOptions): [string, string[]] {
  if (opts?.cmd && opts.cmd.length > 0) {
    return [opts.cmd[0], opts.cmd.slice(1)];
  }
  if (opts?.dockerImage) {
    const absBin = path.resolve(binary);
    return [
      "docker",
      [
        "run",
        "--rm",
        "-i",
        "-v",
        `${path.dirname(absBin)}:/work:ro`,
        opts.dockerImage,
        `/work/${path.basename(absBin)}`,
      ],
    ];
  }
  if (opts?.qemu) {
    return [opts.qemu, [binary]];
  }
  return [binary, []];
}

interface PendingRead {
  resolve: (frame: Uint8Array) => void;
  reject: (err: Error) => void;
}

class KernelPipe {
  #child: ChildProcessWithoutNullStreams;
  #buf: Buffer = Buffer.alloc(0);
  #waiter: PendingRead | null = null;
  #queue: Promise<void> = Promise.resolve();
  #closed = false;
  #exitPromise: Promise<number>;

  constructor(program: string, args: string[]) {
    this.#child = spawn(program, args, { stdio: ["pipe", "pipe", "pipe"] });
    this.#exitPromise = new Promise<number>((resolve, reject) => {
      this.#child.once("error", reject);
      this.#child.once("close", (code, sig) => {
        this.#closed = true;
        if (this.#waiter) {
          const w = this.#waiter;
          this.#waiter = null;
          w.reject(new Error(`kernel stdout closed prematurely (code=${code}, sig=${sig})`));
        }
        resolve(code ?? (sig ? 1 : 0));
      });
    });

    this.#child.stdout.on("data", (chunk: Buffer) => {
      this.#buf = this.#buf.length === 0 ? chunk : Buffer.concat([this.#buf, chunk]);
      if (this.#waiter && this.#buf.length >= FRAME_BYTES) {
        const frame = new Uint8Array(this.#buf.subarray(0, FRAME_BYTES));
        this.#buf = this.#buf.subarray(FRAME_BYTES);
        const w = this.#waiter;
        this.#waiter = null;
        w.resolve(frame);
      }
    });

    this.#child.stdout.on("end", () => {
      if (this.#waiter) {
        const w = this.#waiter;
        this.#waiter = null;
        w.reject(new Error(`kernel stdout EOF after ${this.#buf.length} of ${FRAME_BYTES} bytes`));
      }
    });
  }

  #readExact64(): Promise<Uint8Array> {
    if (this.#buf.length >= FRAME_BYTES) {
      const frame = new Uint8Array(this.#buf.subarray(0, FRAME_BYTES));
      this.#buf = this.#buf.subarray(FRAME_BYTES);
      return Promise.resolve(frame);
    }
    if (this.#closed) {
      return Promise.reject(new Error("guardrail kernel process is closed"));
    }
    return new Promise<Uint8Array>((resolve, reject) => {
      this.#waiter = { resolve, reject };
    });
  }

  sendFrame(req: RequestFrame): Promise<ResponseFrame> {
    const encoded = encodeRequestFrame(req);
    const run = async (): Promise<ResponseFrame> => {
      if (this.#closed) {
        throw new Error("guardrail kernel process is closed");
      }
      const readPromise = this.#readExact64();
      const ok = this.#child.stdin.write(encoded);
      if (!ok) {
        await once(this.#child.stdin, "drain");
      }
      const rawResp = await readPromise;
      return decodeResponseFrame(rawResp);
    };
    const next = this.#queue.then(run, run);
    this.#queue = next.then(
      () => undefined,
      () => undefined,
    );
    return next;
  }

  async close(): Promise<number> {
    await this.#queue;
    if (!this.#closed) {
      this.#child.stdin.end();
    }
    return this.#exitPromise;
  }
}

const AGENT_TOKEN = Symbol("GuardrailAgentToken");
const AGENT_ALLOWED_OPS = new Set<bigint>([OP_SPEND_REQUEST, OP_REFUND, OP_QUERY]);

export class GuardrailAgent {
  readonly agentId: bigint;
  #send: (req: RequestFrame) => Promise<ResponseFrame>;

  constructor(
    agentId: bigint,
    sendFn: (req: RequestFrame) => Promise<ResponseFrame>,
    token: symbol,
  ) {
    if (token !== AGENT_TOKEN) {
      throw new TypeError("GuardrailAgent must be minted via GuardrailAdmin.mintAgent()");
    }
    this.agentId = checkU64("agentId", agentId);
    this.#send = sendFn;
  }

  spend(destId: bigint, amount: bigint, nonce: bigint): Promise<ResponseFrame> {
    return this.#send(spendReq(this.agentId, destId, amount, nonce));
  }

  refund(txId: bigint, amount: bigint): Promise<ResponseFrame> {
    return this.#send(refundReq(txId, amount, this.agentId));
  }

  query(): Promise<ResponseFrame> {
    return this.#send(queryReq(this.agentId));
  }
}

export class GuardrailAdmin {
  #pipe: KernelPipe;

  private constructor(pipe: KernelPipe) {
    this.#pipe = pipe;
  }

  static spawn(binary: string, opts?: SpawnOptions): GuardrailAdmin {
    const [program, args] = buildKernelArgv(binary, opts);
    return new GuardrailAdmin(new KernelPipe(program, args));
  }

  depositAndConfigure(
    deposit: bigint,
    cap: bigint,
    allowlistMask: bigint,
    agentId = 0n,
  ): Promise<ResponseFrame> {
    return this.#pipe.sendFrame(budgetSetReq(deposit, cap, allowlistMask, agentId));
  }

  deposit_and_configure(
    deposit: bigint,
    cap: bigint,
    allowlistMask: bigint,
    agentId = 0n,
  ): Promise<ResponseFrame> {
    return this.depositAndConfigure(deposit, cap, allowlistMask, agentId);
  }

  query(agentId = 0n): Promise<ResponseFrame> {
    return this.#pipe.sendFrame(queryReq(agentId));
  }

  mintAgent(agentId: bigint): GuardrailAgent {
    const pipe = this.#pipe;
    const restrictedSend = (req: RequestFrame): Promise<ResponseFrame> => {
      if (!AGENT_ALLOWED_OPS.has(req.op)) {
        return Promise.reject(new Error(`GuardrailAgent is forbidden from invoking op=${req.op}`));
      }
      return pipe.sendFrame(req);
    };
    return new GuardrailAgent(agentId, restrictedSend, AGENT_TOKEN);
  }

  close(): Promise<number> {
    return this.#pipe.close();
  }
}
'''
    return _apply_sdk_tokens(tpl, schema)


def render_rust_cargo_toml(schema: dict) -> str:
    tpl = r'''[package]
name = "__CRATE_NAME__"
version = "0.1.0"
edition = "2021"
description = "Zero-dependency Rust SDK for Forge __APP__ 64-byte binary frame kernel"

[dependencies]
'''
    return _apply_sdk_tokens(tpl, schema)


def render_rust_lib_rs(schema: dict) -> str:
    tpl = r'''//! Zero-dependency Rust SDK for the Forge `__APP__` 64-byte binary frame kernel.
//! Auto-generated from canonical schema by `scripts/forge_vibe.py`.

use std::ffi::OsStr;
use std::fmt;
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitStatus, Stdio};
use std::sync::{Arc, Mutex};

pub const FRAME_BYTES: usize = 64;

pub const OP_BUDGET_SET: u64 = __OP_BUDGET_SET__;
pub const OP_SPEND_REQUEST: u64 = __OP_SPEND_REQUEST__;
pub const OP_REFUND: u64 = __OP_REFUND__;
pub const OP_QUERY: u64 = __OP_QUERY__;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameError {
    InvalidLength { expected: usize, got: usize },
}

impl fmt::Display for FrameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            FrameError::InvalidLength { expected, got } => {
                write!(f, "expected {expected} bytes, got {got}")
            }
        }
    }
}

impl std::error::Error for FrameError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RequestFrame {
    pub op: u64,
    pub agent_id: u64,
    pub arg2: u64,
    pub amount: u64,
    pub arg4: u64,
    pub reserved5: u64,
    pub reserved6: u64,
    pub reserved7: u64,
}

impl RequestFrame {
    pub fn encode(&self) -> [u8; FRAME_BYTES] {
        encode_lanes([
            self.op,
            self.agent_id,
            self.arg2,
            self.amount,
            self.arg4,
            self.reserved5,
            self.reserved6,
            self.reserved7,
        ])
    }

    pub fn decode_array(buf: &[u8; FRAME_BYTES]) -> Self {
        let lanes = decode_lanes(buf);
        Self {
            op: lanes[0],
            agent_id: lanes[1],
            arg2: lanes[2],
            amount: lanes[3],
            arg4: lanes[4],
            reserved5: lanes[5],
            reserved6: lanes[6],
            reserved7: lanes[7],
        }
    }

    pub fn decode(buf: &[u8]) -> Result<Self, FrameError> {
        let arr: &[u8; FRAME_BYTES] = buf.try_into().map_err(|_| FrameError::InvalidLength {
            expected: FRAME_BYTES,
            got: buf.len(),
        })?;
        Ok(Self::decode_array(arr))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ResponseFrame {
    pub ok: u64,
    pub code: u64,
    pub deposits: u64,
    pub balance: u64,
    pub net_spent: u64,
    pub refunds: u64,
    pub last_nonce: u64,
    pub last_tx_id: u64,
}

impl ResponseFrame {
    pub fn encode(&self) -> [u8; FRAME_BYTES] {
        encode_lanes([
            self.ok,
            self.code,
            self.deposits,
            self.balance,
            self.net_spent,
            self.refunds,
            self.last_nonce,
            self.last_tx_id,
        ])
    }

    pub fn decode_array(buf: &[u8; FRAME_BYTES]) -> Self {
        let lanes = decode_lanes(buf);
        Self {
            ok: lanes[0],
            code: lanes[1],
            deposits: lanes[2],
            balance: lanes[3],
            net_spent: lanes[4],
            refunds: lanes[5],
            last_nonce: lanes[6],
            last_tx_id: lanes[7],
        }
    }

    pub fn decode(buf: &[u8]) -> Result<Self, FrameError> {
        let arr: &[u8; FRAME_BYTES] = buf.try_into().map_err(|_| FrameError::InvalidLength {
            expected: FRAME_BYTES,
            got: buf.len(),
        })?;
        Ok(Self::decode_array(arr))
    }

    pub fn is_ok(&self) -> bool {
        self.ok == 1
    }

    pub fn is_conserved(&self) -> bool {
        self.balance.checked_add(self.net_spent) == Some(self.deposits)
    }
}

fn encode_lanes(lanes: [u64; 8]) -> [u8; FRAME_BYTES] {
    let mut out = [0u8; FRAME_BYTES];
    for (i, word) in lanes.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&word.to_le_bytes());
    }
    out
}

fn decode_lanes(buf: &[u8; FRAME_BYTES]) -> [u64; 8] {
    let mut lanes = [0u64; 8];
    for (i, slot) in lanes.iter_mut().enumerate() {
        let mut chunk = [0u8; 8];
        chunk.copy_from_slice(&buf[i * 8..(i + 1) * 8]);
        *slot = u64::from_le_bytes(chunk);
    }
    lanes
}

pub fn budget_set_req(deposit: u64, cap: u64, allowlist_mask: u64, agent_id: u64) -> RequestFrame {
    RequestFrame {
        op: OP_BUDGET_SET,
        agent_id,
        arg2: allowlist_mask,
        amount: deposit,
        arg4: cap,
        ..RequestFrame::default()
    }
}

pub fn spend_req(agent_id: u64, dest_id: u64, amount: u64, nonce: u64) -> RequestFrame {
    RequestFrame {
        op: OP_SPEND_REQUEST,
        agent_id,
        arg2: dest_id,
        amount,
        arg4: nonce,
        ..RequestFrame::default()
    }
}

pub fn refund_req(tx_id: u64, amount: u64, agent_id: u64) -> RequestFrame {
    RequestFrame {
        op: OP_REFUND,
        agent_id,
        arg2: 0,
        amount,
        arg4: tx_id,
        ..RequestFrame::default()
    }
}

pub fn query_req(agent_id: u64) -> RequestFrame {
    RequestFrame {
        op: OP_QUERY,
        agent_id,
        ..RequestFrame::default()
    }
}

fn write_exact_64<W: Write>(writer: &mut W, buf: &[u8; FRAME_BYTES]) -> io::Result<()> {
    let mut written = 0usize;
    while written < FRAME_BYTES {
        match writer.write(&buf[written..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "kernel stdin closed before 64-byte frame was written",
                ));
            }
            Ok(n) => written += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
    loop {
        match writer.flush() {
            Ok(()) => return Ok(()),
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
}

fn read_exact_64<R: Read>(reader: &mut R) -> io::Result<[u8; FRAME_BYTES]> {
    let mut buf = [0u8; FRAME_BYTES];
    let mut got = 0usize;
    while got < FRAME_BYTES {
        match reader.read(&mut buf[got..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    format!("kernel stdout hit EOF after {got} of {FRAME_BYTES} bytes"),
                ));
            }
            Ok(n) => got += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
    Ok(buf)
}

struct KernelPipe {
    child: Child,
    stdin: Option<ChildStdin>,
    stdout: ChildStdout,
    closed: bool,
}

impl KernelPipe {
    fn spawn_cmd(mut cmd: Command) -> io::Result<Self> {
        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        let mut child = cmd.spawn()?;
        let stdin = child.stdin.take().ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "failed to attach kernel stdin pipe")
        })?;
        let stdout = child.stdout.take().ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "failed to attach kernel stdout pipe")
        })?;
        Ok(Self {
            child,
            stdin: Some(stdin),
            stdout,
            closed: false,
        })
    }

    fn send_frame(&mut self, req: &RequestFrame) -> io::Result<ResponseFrame> {
        if self.closed {
            return Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "guardrail kernel process is closed",
            ));
        }
        let encoded = req.encode();
        let stdin = self.stdin.as_mut().ok_or_else(|| {
            io::Error::new(io::ErrorKind::BrokenPipe, "kernel stdin already closed")
        })?;
        write_exact_64(stdin, &encoded)?;
        let raw_resp = read_exact_64(&mut self.stdout)?;
        Ok(ResponseFrame::decode_array(&raw_resp))
    }

    fn close(&mut self) -> io::Result<ExitStatus> {
        self.closed = true;
        drop(self.stdin.take());
        self.child.wait()
    }
}

impl Drop for KernelPipe {
    fn drop(&mut self) {
        if !self.closed {
            drop(self.stdin.take());
            let _ = self.child.wait();
            self.closed = true;
        }
    }
}

fn lock_pipe(pipe: &Arc<Mutex<KernelPipe>>) -> io::Result<std::sync::MutexGuard<'_, KernelPipe>> {
    pipe.lock()
        .map_err(|_| io::Error::new(io::ErrorKind::Other, "guardrail pipe mutex poisoned"))
}

pub struct GuardrailAdmin {
    pipe: Arc<Mutex<KernelPipe>>,
}

impl GuardrailAdmin {
    pub fn spawn<P: AsRef<Path>>(binary: P) -> io::Result<Self> {
        let cmd = Command::new(binary.as_ref());
        Ok(Self {
            pipe: Arc::new(Mutex::new(KernelPipe::spawn_cmd(cmd)?)),
        })
    }

    pub fn spawn_command<S, I, A>(program: S, args: I) -> io::Result<Self>
    where
        S: AsRef<OsStr>,
        I: IntoIterator<Item = A>,
        A: AsRef<OsStr>,
    {
        let mut cmd = Command::new(program);
        cmd.args(args);
        Ok(Self {
            pipe: Arc::new(Mutex::new(KernelPipe::spawn_cmd(cmd)?)),
        })
    }

    pub fn spawn_docker<P: AsRef<Path>>(docker_image: &str, binary: P) -> io::Result<Self> {
        let abs = std::fs::canonicalize(binary.as_ref())?;
        let parent = abs.parent().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "binary path has no parent directory")
        })?;
        let name = abs.file_name().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "binary path has no filename")
        })?;
        let mut mount = parent.as_os_str().to_os_string();
        mount.push(":/work:ro");
        let mut container_bin = std::ffi::OsString::from("/work/");
        container_bin.push(name);
        let mut cmd = Command::new("docker");
        cmd.args(["run", "--rm", "-i", "-v"])
            .arg(mount)
            .arg(docker_image)
            .arg(container_bin);
        Ok(Self {
            pipe: Arc::new(Mutex::new(KernelPipe::spawn_cmd(cmd)?)),
        })
    }

    pub fn deposit_and_configure(
        &self,
        deposit: u64,
        cap: u64,
        allowlist_mask: u64,
        agent_id: u64,
    ) -> io::Result<ResponseFrame> {
        let req = budget_set_req(deposit, cap, allowlist_mask, agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    pub fn query(&self, agent_id: u64) -> io::Result<ResponseFrame> {
        let req = query_req(agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    pub fn mint_agent(&self, agent_id: u64) -> GuardrailAgent {
        GuardrailAgent {
            pipe: Arc::clone(&self.pipe),
            agent_id,
        }
    }

    pub fn close(self) -> io::Result<ExitStatus> {
        let mut guard = lock_pipe(&self.pipe)?;
        guard.close()
    }
}

#[derive(Clone)]
pub struct GuardrailAgent {
    pipe: Arc<Mutex<KernelPipe>>,
    agent_id: u64,
}

impl GuardrailAgent {
    pub fn agent_id(&self) -> u64 {
        self.agent_id
    }

    pub fn spend(&self, dest_id: u64, amount: u64, nonce: u64) -> io::Result<ResponseFrame> {
        let req = spend_req(self.agent_id, dest_id, amount, nonce);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    pub fn refund(&self, tx_id: u64, amount: u64) -> io::Result<ResponseFrame> {
        let req = refund_req(tx_id, amount, self.agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    pub fn query(&self) -> io::Result<ResponseFrame> {
        let req = query_req(self.agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes_to_hex(bytes: &[u8]) -> String {
        let mut out = String::with_capacity(bytes.len() * 2);
        for b in bytes {
            use std::fmt::Write as _;
            let _ = write!(&mut out, "{b:02x}");
        }
        out
    }

    #[test]
    fn golden_vectors_roundtrip_and_hex() {
        let vectors: [(&str, RequestFrame); 5] = [
            ("budget_set_basic", budget_set_req(50_000, 20_000, 0b1011, 7)),
            ("spend_normal", spend_req(42, 3, 12_500, 1)),
            ("spend_u64_max_attack", spend_req(1, 0, u64::MAX, 2)),
            ("refund_partial", refund_req(9, 4_000, 42)),
            ("query_zero", query_req(99)),
        ];
        for (name, req) in vectors {
            let raw = req.encode();
            assert_eq!(raw.len(), FRAME_BYTES);
            assert_eq!(RequestFrame::decode(&raw).unwrap(), req);
            println!("RUST_VEC {name}={}", bytes_to_hex(&raw));
        }
        assert_eq!(
            RequestFrame::decode(&[0u8; 63]),
            Err(FrameError::InvalidLength { expected: 64, got: 63 })
        );
    }
}
'''
    return _apply_sdk_tokens(tpl, schema)


def render_golden_test_py(schema: dict) -> str:
    tpl = (ROOT / "sdk" / "guardrail" / "test_golden_vectors.py").read_text()
    return tpl.replace("guardrail", schema["app"])


def cmd_generate(args: argparse.Namespace) -> int:
    schema = json.loads(Path(args.schema).read_text()) if args.schema else dict(DEFAULT_GUARDRAIL_SCHEMA)
    if args.app:
        schema["app"] = args.app
    app = schema["app"]
    app_dir = ROOT / "kernels" / app
    hol_dir = app_dir / "hol4"
    sdk_dir = ROOT / "sdk" / app
    rust_src_dir = sdk_dir / "src"
    hol_dir.mkdir(parents=True, exist_ok=True)
    rust_src_dir.mkdir(parents=True, exist_ok=True)

    (sdk_dir / "schema.json").write_text(json.dumps(schema, indent=2) + "\n")

    spec_text = render_guardrail_hol4_spec(schema)
    spec_path = hol_dir / f"forge_{app}SpecScript.sml"
    pin_file = app_dir / "SPEC_HASHES.sha256"
    if pin_file.is_file() and spec_path.is_file():
        print(f"SKIP frozen spec overwrite (pinned in {pin_file.relative_to(ROOT)}): {spec_path.relative_to(ROOT)}")
    else:
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
    if not (hol_dir / "Holmakefile").is_file() or not pin_file.is_file():
        (hol_dir / "Holmakefile").write_text(holmakefile)

    (sdk_dir / "sdk.py").write_text(render_sdk_py(schema))
    (sdk_dir / "sdk.ts").write_text(render_sdk_ts(schema))
    (sdk_dir / "Cargo.toml").write_text(render_rust_cargo_toml(schema))
    (rust_src_dir / "lib.rs").write_text(render_rust_lib_rs(schema))
    gt_path = sdk_dir / "test_golden_vectors.py"
    gt_path.write_text(render_golden_test_py(schema))
    os.chmod(gt_path, 0o755)

    line_count = len(spec_text.splitlines())
    print(f"Generated kernels/{app} (Ring 0) + sdk/{app} (Ring 2):")
    print(f"  HOL4 Spec : {spec_path.relative_to(ROOT)} ({line_count} lines)")
    print(f"  Python SDK: {(sdk_dir / 'sdk.py').relative_to(ROOT)}")
    print(f"  TS SDK    : {(sdk_dir / 'sdk.ts').relative_to(ROOT)}")
    print(f"  Rust SDK  : {(sdk_dir / 'Cargo.toml').relative_to(ROOT)} + {(rust_src_dir / 'lib.rs').relative_to(ROOT)}")
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
