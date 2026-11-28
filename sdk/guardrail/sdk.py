#!/usr/bin/env python3
"""Zero-dependency Python SDK for Forge `guardrail` 64-byte binary frame kernel.
Auto-generated from canonical schema by `scripts/forge_vibe.py`.

Provides capability-separated live process clients:
  - `GuardrailAdmin`: owns process lifecycle + `deposit_and_configure` (`op=1`)
    and mints restricted `GuardrailAgent` handles.
  - `GuardrailAgent`: exposes ONLY `spend` (`op=2`), `refund` (`op=3`), and
    `query` (`op=4`), structurally preventing untrusted agent code from
    invoking `op=1` or closing the kernel process.
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

OP_BUDGET_SET = 1
OP_SPEND_REQUEST = 2
OP_REFUND = 3
OP_QUERY = 4

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
    """Restricted capability handle for untrusted AI agents.

    Exposes ONLY `spend` (`op=2`), `refund` (`op=3`), and `query` (`op=4`).
    Structurally holds no reference to `GuardrailAdmin`, `op=1`, or process lifecycle.
    """

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
