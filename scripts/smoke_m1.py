#!/usr/bin/env python3
"""Black-box smoke suite for the M1 static Linux ARM64 counter kernel.

Runs the compiled ELF binary directly (on Linux/ARM64), via qemu-aarch64-static,
or inside a Linux/ARM64 Docker container when invoked with --docker-image.
"""
import argparse
import os
import struct
import subprocess
import sys
import threading
import time
from pathlib import Path

U64_MAX = (1 << 64) - 1


def pack_frame(a: int, b: int) -> bytes:
    return struct.pack("<QQ", a, b)


def unpack_frames(data: bytes) -> list[tuple[int, int]]:
    if len(data) % 16 != 0:
        raise AssertionError(f"stdout length {len(data)} is not a multiple of 16")
    return [struct.unpack("<QQ", data[i : i + 16]) for i in range(0, len(data), 16)]


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


def run_frames(cmd: list[str], payload: bytes) -> tuple[int, bytes, bytes]:
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
    assert proc.stdin is not None
    assert proc.stdout is not None
    assert proc.stderr is not None

    def feeder() -> None:
        try:
            for b in payload:
                proc.stdin.write(bytes([b]))
                proc.stdin.flush()
                time.sleep(0.002)
        finally:
            proc.stdin.close()

    t = threading.Thread(target=feeder, daemon=True)
    t.start()
    out = proc.stdout.read()
    err = proc.stderr.read()
    t.join(timeout=10)
    code = proc.wait(timeout=10)
    return code, out, err


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("binary", type=Path)
    ap.add_argument("--docker-image", default=None)
    ap.add_argument("--qemu", default=None)
    args = ap.parse_args()

    cmd = make_cmd(args.binary, args.docker_image, args.qemu)

    cases: list[tuple[str, bytes, list[tuple[int, int]]]] = [
        (
            "valid_cap_boundary_and_overcap",
            b"".join(
                [
                    pack_frame(1, 2500),
                    pack_frame(2, 7500),
                    pack_frame(3, 0),
                    pack_frame(4, 1),
                ]
            ),
            [(1, 1), (1, 2), (1, 3), (0, 3)],
        ),
        (
            "replay_and_stale_seq",
            b"".join(
                [
                    pack_frame(1, 100),
                    pack_frame(1, 100),
                    pack_frame(0, 100),
                ]
            ),
            [(1, 1), (0, 1), (0, 1)],
        ),
        (
            "gap_skip_then_valid",
            b"".join(
                [
                    pack_frame(2, 100),
                    pack_frame(1, 100),
                ]
            ),
            [(0, 0), (1, 1)],
        ),
        (
            "u64_wraparound_overflow_attacks",
            b"".join(
                [
                    pack_frame(1, 100),
                    pack_frame(2, U64_MAX),
                    pack_frame(2, U64_MAX - 99),
                    pack_frame(2, 9900),
                ]
            ),
            [(1, 1), (0, 1), (0, 1), (1, 2)],
        ),
        (
            "truncated_trailing_eof",
            pack_frame(1, 42) + b"\x02\x00\x00\x00\x00\x00\x00",
            [(1, 1)],
        ),
    ]

    for name, payload, expected in cases:
        code, out, err = run_frames(cmd, payload)
        if code != 0 or err:
            print(f"FAIL {name}: exit={code} stderr={err!r}")
            return 1
        got = unpack_frames(out)
        if got != expected:
            print(f"FAIL {name}: got={got} expected={expected}")
            return 1
        print(f"PASS {name}: {len(got)} frames ok, exit 0")

    # 1-byte-at-a-time chunked pipe test (exercises partial read loop in ffirecv16)
    chunk_payload = b"".join(
        [
            pack_frame(1, 4000),
            pack_frame(1, 1),
            pack_frame(2, 6000),
        ]
    )
    chunk_expected = [(1, 1), (0, 1), (1, 2)]
    code, out, err = run_chunked_1byte(cmd, chunk_payload)
    if code != 0 or err:
        print(f"FAIL chunked_1byte_pipe: exit={code} stderr={err!r}")
        return 1
    got = unpack_frames(out)
    if got != chunk_expected:
        print(f"FAIL chunked_1byte_pipe: got={got} expected={chunk_expected}")
        return 1
    print(f"PASS chunked_1byte_pipe: 48 bytes fed 1 byte/write, {len(got)} frames ok, exit 0")

    print("ALL 6 M1 BLACK-BOX SMOKE CASES PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
