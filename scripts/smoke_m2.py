#!/usr/bin/env python3
"""Black-box smoke suite for the M2 static Linux ARM64 guardrail kernel.

Tests all 15 frozen boundary scenarios (bit-for-bit against the pure Python/HOL4
guardrail spec), truncated trailing EOF, 1-byte-at-a-time chunked pipe reads
(exercising the ffirecv64 partial-read loop), and clean SIGPIPE / early close.
"""
from __future__ import annotations

import argparse
import struct
import subprocess
import sys
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "sdk" / "guardrail"))
import sdk  # noqa: E402

U64_MAX = (1 << 64) - 1
FRAME_BYTES = 64


def make_cmd(binary: Path, docker_image: str | None, qemu: str | None) -> list[str]:
    if docker_image:
        bin_abs = binary.resolve()
        return [
            "docker",
            "run",
            "--rm",
            "-i",
            "-v",
            f"{bin_abs.parent}:/work:ro",
            docker_image,
            f"/work/{bin_abs.name}",
        ]
    if qemu:
        return [qemu, str(binary)]
    return [str(binary)]


def run_raw(cmd: list[str], payload: bytes) -> tuple[int, bytes, bytes]:
    r = subprocess.run(cmd, input=payload, capture_output=True, timeout=30)
    return r.returncode, r.stdout, r.stderr


def run_chunked_1byte(cmd: list[str], payload: bytes) -> tuple[int, bytes, bytes]:
    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        bufsize=0,
    )
    assert proc.stdin is not None and proc.stdout is not None and proc.stderr is not None

    def feeder() -> None:
        try:
            for i in range(len(payload)):
                proc.stdin.write(payload[i : i + 1])
                proc.stdin.flush()
                time.sleep(0.0005)
        finally:
            proc.stdin.close()

    t = threading.Thread(target=feeder, daemon=True)
    t.start()
    out = proc.stdout.read()
    err = proc.stderr.read()
    t.join(timeout=15)
    code = proc.wait(timeout=15)
    return code, out, err


def unpack_resps(raw: bytes) -> list[sdk.ResponseFrame]:
    if len(raw) % FRAME_BYTES != 0:
        raise AssertionError(f"stdout length {len(raw)} is not a multiple of {FRAME_BYTES}")
    return [
        sdk.ResponseFrame.decode(raw[i : i + FRAME_BYTES])
        for i in range(0, len(raw), FRAME_BYTES)
    ]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("binary", type=Path)
    ap.add_argument("--docker-image", default=None)
    ap.add_argument("--qemu", default=None)
    args = ap.parse_args()

    cmd = make_cmd(args.binary, args.docker_image, args.qemu)

    # All 15 canonical boundary scenarios from intent-lock
    stream_15 = [
        ("01_initial_query", sdk.query_req(), sdk.ResponseFrame(1, 0, 0, 0, 0, 0, 0, 0)),
        ("02_budget_deposit_5000", sdk.budget_set_req(5000, 3000, 0b101), sdk.ResponseFrame(1, 0, 5000, 5000, 0, 0, 0, 0)),
        ("03_spend_zero_denied", sdk.spend_req(1, 0, 0, 1), sdk.ResponseFrame(0, 2, 5000, 5000, 0, 0, 0, 0)),
        ("04_spend_dest1_not_allowlisted", sdk.spend_req(1, 1, 100, 1), sdk.ResponseFrame(0, 2, 5000, 5000, 0, 0, 0, 0)),
        ("05_spend_dest64_oob_denied", sdk.spend_req(1, 64, 100, 1), sdk.ResponseFrame(0, 2, 5000, 5000, 0, 0, 0, 0)),
        ("06_spend_nonce_gap_denied", sdk.spend_req(1, 0, 100, 2), sdk.ResponseFrame(0, 2, 5000, 5000, 0, 0, 0, 0)),
        ("07_spend_1200_ok", sdk.spend_req(1, 0, 1200, 1), sdk.ResponseFrame(1, 0, 5000, 3800, 1200, 0, 1, 1)),
        ("08_spend_replay_nonce1_denied", sdk.spend_req(1, 0, 100, 1), sdk.ResponseFrame(0, 2, 5000, 3800, 1200, 0, 1, 1)),
        ("09_spend_over_cap_denied", sdk.spend_req(1, 2, 1801, 2), sdk.ResponseFrame(0, 2, 5000, 3800, 1200, 0, 1, 1)),
        ("10_spend_exact_cap_1800_ok", sdk.spend_req(1, 2, 1800, 2), sdk.ResponseFrame(1, 0, 5000, 2000, 3000, 0, 2, 2)),
        ("11_spend_at_cap_denied", sdk.spend_req(1, 0, 1, 3), sdk.ResponseFrame(0, 2, 5000, 2000, 3000, 0, 2, 2)),
        ("12_refund_wrong_tx1_denied", sdk.refund_req(1, 500), sdk.ResponseFrame(0, 3, 5000, 2000, 3000, 0, 2, 2)),
        ("13_refund_over_amt_denied", sdk.refund_req(2, 1801), sdk.ResponseFrame(0, 3, 5000, 2000, 3000, 0, 2, 2)),
        ("14_refund_tx2_800_ok", sdk.refund_req(2, 800), sdk.ResponseFrame(1, 0, 5000, 2800, 2200, 800, 2, 2)),
        ("15_double_refund_denied", sdk.refund_req(2, 100), sdk.ResponseFrame(0, 3, 5000, 2800, 2200, 800, 2, 2)),
    ]

    payload_15 = b"".join(req.encode() for _, req, _ in stream_15)
    code, out, err = run_raw(cmd, payload_15)
    if code != 0 or err:
        print(f"FAIL 15_boundary_scenarios: exit={code} stderr={err!r}")
        return 1
    got_15 = unpack_resps(out)
    if len(got_15) != len(stream_15):
        print(f"FAIL 15_boundary_scenarios: got {len(got_15)} frames != 15")
        return 1
    for (name, _, want), got in zip(stream_15, got_15):
        if got != want:
            print(f"FAIL {name}: got={got} want={want}")
            return 1
        assert got.deposits == got.balance + got.net_spent, f"conservation violated on {name}"
    print("PASS 15_boundary_scenarios: all 15 frames bit-identical & conserved, exit 0")

    # Overflow attacks, unknown opcode, net-cap re-spend after refund, cap-below-net-spent rejection
    extra_stream = [
        sdk.budget_set_req(1000, 1000, 1),
        sdk.budget_set_req(U64_MAX, 1000, 1),  # u64 deposit overflow denied
        sdk.spend_req(7, 0, U64_MAX, 1),       # u64 spend overflow denied
        sdk.spend_req(7, 0, 600, 1),           # valid spend 600
        sdk.budget_set_req(0, 599, 1),         # lowering cap below net_spent (600) denied
        sdk.refund_req(1, 400),                # partial refund 400 -> net_spent=200, bal=800
        sdk.spend_req(7, 0, 800, 2),           # net_spent 200+800=1000 <= cap 1000 -> ok!
        sdk.RequestFrame(op=99),               # unknown opcode -> code 4 denied
    ]
    extra_want = [
        sdk.ResponseFrame(1, 0, 1000, 1000, 0, 0, 0, 0),
        sdk.ResponseFrame(0, 1, 1000, 1000, 0, 0, 0, 0),
        sdk.ResponseFrame(0, 2, 1000, 1000, 0, 0, 0, 0),
        sdk.ResponseFrame(1, 0, 1000, 400, 600, 0, 1, 1),
        sdk.ResponseFrame(0, 1, 1000, 400, 600, 0, 1, 1),
        sdk.ResponseFrame(1, 0, 1000, 800, 200, 400, 1, 1),
        sdk.ResponseFrame(1, 0, 1000, 0, 1000, 400, 2, 2),
        sdk.ResponseFrame(0, 4, 1000, 0, 1000, 400, 2, 2),
    ]
    code, out, err = run_raw(cmd, b"".join(r.encode() for r in extra_stream))
    if code != 0 or err or unpack_resps(out) != extra_want:
        print(f"FAIL overflow_and_net_cap: exit={code} err={err!r} got={unpack_resps(out)}")
        return 1
    print("PASS overflow_and_net_cap: 8 adversarial frames ok, exit 0")

    # Truncated trailing EOF (63 trailing bytes ignored cleanly, exit 0)
    trunc_payload = sdk.budget_set_req(777, 1000, 1).encode() + b"\xAB" * 63
    code, out, err = run_raw(cmd, trunc_payload)
    if code != 0 or err or unpack_resps(out) != [sdk.ResponseFrame(1, 0, 777, 777, 0, 0, 0, 0)]:
        print(f"FAIL truncated_63b_eof: exit={code} err={err!r}")
        return 1
    print("PASS truncated_63b_eof: 63 trailing bytes cleanly ignored, exit 0")

    # Chunked 1-byte pipe writes exercising partial read loop in ffirecv64
    chunk_reqs = [sdk.budget_set_req(500, 500, 1), sdk.spend_req(1, 0, 250, 1), sdk.refund_req(1, 50)]
    chunk_want = [
        sdk.ResponseFrame(1, 0, 500, 500, 0, 0, 0, 0),
        sdk.ResponseFrame(1, 0, 500, 250, 250, 0, 1, 1),
        sdk.ResponseFrame(1, 0, 500, 300, 200, 50, 1, 1),
    ]
    code, out, err = run_chunked_1byte(cmd, b"".join(r.encode() for r in chunk_reqs))
    if code != 0 or err or unpack_resps(out) != chunk_want:
        print(f"FAIL chunked_1byte_pipe: exit={code} err={err!r}")
        return 1
    print("PASS chunked_1byte_pipe: 192 bytes fed 1B/write, 3 frames ok, exit 0")

    # Early stdout close / EPIPE: ignore SIGPIPE and pipe into `head -c 64` with >64KB of frames
    # so write(64) deterministically hits -EPIPE from the Linux kernel; ffisend64 sets buf[0]=1,
    # frame64_loop halts cleanly with exact 64B prefix and exits via exit_group(0).
    epipe_reqs = [sdk.budget_set_req(500, 500, 1)] + [sdk.query_req() for _ in range(2048)]
    epipe_payload = b"".join(r.encode() for r in epipe_reqs)
    epipe_sh = (
        'exec 4>&1; trap "" PIPE; '
        'rc=$( { ( "$1" 3>&- 4>&-; printf "%s" "$?" >&3 ) | head -c 64 3>&- >&4; } 3>&1 ); '
        'exit "${rc:-99}"'
    )
    if args.docker_image:
        bin_abs = args.binary.resolve()
        epipe_cmd = [
            "docker", "run", "--rm", "-i",
            "-v", f"{bin_abs.parent}:/work:ro",
            args.docker_image,
            "sh", "-c", epipe_sh, "_", f"/work/{bin_abs.name}",
        ]
    elif args.qemu:
        epipe_cmd = ["sh", "-c", epipe_sh.replace('"$1"', '"$1" "$2"'), "_", args.qemu, str(args.binary)]
    else:
        epipe_cmd = ["sh", "-c", epipe_sh, "_", str(args.binary)]
    epipe_code, first_raw, epipe_err = run_raw(epipe_cmd, epipe_payload)
    want_first = sdk.ResponseFrame(1, 0, 500, 500, 0, 0, 0, 0)
    if len(first_raw) != FRAME_BYTES or sdk.ResponseFrame.decode(first_raw) != want_first or epipe_code != 0 or epipe_err:
        print(f"FAIL early_close_epipe: exit={epipe_code} first_len={len(first_raw)} err={epipe_err!r}")
        return 1
    print("PASS early_close_epipe: 1st 64B prefix matched, -EPIPE handled cleanly with exit 0")

    # Empty stdin -> empty stdout, exit 0
    code, out, err = run_raw(cmd, b"")
    if code != 0 or err or out != b"":
        print(f"FAIL empty_eof: exit={code} len={len(out)} err={err!r}")
        return 1
    print("PASS empty_eof: 0 bytes -> 0 bytes, exit 0")

    print("ALL 6 M2 GUARDRAIL BLACK-BOX SMOKE SUITES PASSED (28 frames verified)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
