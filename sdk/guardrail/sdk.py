#!/usr/bin/env python3
"""Zero-dependency Python SDK for Forge `guardrail` 64-byte binary frame kernel.
Auto-generated from canonical schema by `scripts/forge_vibe.py`.
"""
from __future__ import annotations

import dataclasses
import struct
import subprocess
from pathlib import Path

FRAME_BYTES = 64
FRAME_STRUCT = struct.Struct("<8Q")

OP_BUDGET_SET = 1
OP_SPEND_REQUEST = 2
OP_REFUND = 3
OP_QUERY = 4


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
            raise RuntimeError(f"unaligned response stream: {len(raw)} bytes")
        return [
            ResponseFrame.decode(raw[i : i + FRAME_BYTES])
            for i in range(0, len(raw), FRAME_BYTES)
        ]
