#!/usr/bin/env python3
"""Negative controls for the Iron Law gate.

Each case builds a scratch repository and checks the gate exit code. A fake
`Holmake` stands in for HOL4, so these cases test the gate logic only. They
prove nothing about the kernel.
"""
import hashlib
import os
import stat
import subprocess
import sys
import tempfile
from pathlib import Path

GATE = Path(__file__).resolve().parent.parent / "iron_law.py"
BIN = b"\x7fELF fake kernel bytes"
GOOD = hashlib.sha256(BIN).hexdigest()
MANIFEST = "holmake_dir=kernel/proof\nbinary=kernel/build/kernel.elf\nhash_file=kernel/build/machine_bytes_hash.txt\n"


def make_repo(d: Path, *, manifest=MANIFEST, holmake_exit=0, hash_text=GOOD,
              binary=BIN, script_text="Theorem t: T\nProof simp[]\nQED\n",
              write_hash=True):
    (d / "kernel/proof").mkdir(parents=True)
    (d / "kernel/build").mkdir(parents=True)
    if manifest is not None:
        (d / "kernel/GATE.manifest").write_text(manifest)
    (d / "kernel/proof/counterScript.sml").write_text(script_text)
    if binary is not None:
        (d / "kernel/build/kernel.elf").write_bytes(binary)
    tools = d / "_tools"
    tools.mkdir()
    hm = tools / "Holmake"
    body = f"#!/bin/sh\n"
    if write_hash:
        body += f"printf '%s\\n' '{hash_text}' > ../build/machine_bytes_hash.txt\n"
    body += f"exit {holmake_exit}\n"
    hm.write_text(body)
    hm.chmod(hm.stat().st_mode | stat.S_IEXEC)
    return tools


def run(d: Path, tools, with_holmake=True):
    env = dict(os.environ)
    path = "/usr/bin:/bin"
    if with_holmake:
        path = f"{tools}:{path}"
    env["PATH"] = path
    r = subprocess.run([sys.executable, str(GATE), str(d)], env=env,
                       capture_output=True, text=True)
    return r.returncode, r.stdout.strip()


CASES = [
    # name, make_repo kwargs, with_holmake, expected exit, expected text
    ("accept: proofs replay and hash matches", {}, True, 0, "end_to_end=true"),
    ("reject: no manifest", {"manifest": None}, True, 1, "NO_KERNEL_THEOREM"),
    ("reject: manifest missing a key", {"manifest": "holmake_dir=kernel/proof\n"}, True, 1, "BAD_MANIFEST"),
    ("reject: manifest path escapes repo", {"manifest": MANIFEST.replace("kernel/build/kernel.elf", "../x")}, True, 1, "BAD_MANIFEST"),
    ("reject: HOL4 not installed", {}, False, 1, "HOL4_NOT_INSTALLED"),
    ("reject: Holmake fails", {"holmake_exit": 2}, True, 1, "HOLMAKE_FAILED"),
    ("reject: cheat in a proof script", {"script_text": "Theorem t: F\nProof cheat\nQED\n"}, True, 1, "CHEAT_FOUND"),
    ("reject: binary one byte changed", {"binary": BIN[:-1] + b"X"}, True, 1, "HASH_MISMATCH"),
    ("reject: binary missing", {"binary": None}, True, 1, "BINARY_MISSING"),
    ("reject: hash file malformed", {"hash_text": "abc"}, True, 1, "HASH_FILE_MALFORMED"),
    ("reject: hash upper case", {"hash_text": GOOD.upper()}, True, 1, "HASH_FILE_MALFORMED"),
    ("reject: proof build writes no hash", {"write_hash": False}, True, 1, "HASH_FILE_MISSING"),
]


def main() -> int:
    bad = 0
    for name, kw, with_hm, want_exit, want_text in CASES:
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            tools = make_repo(d, **kw)
            code, out = run(d, tools, with_hm)
        ok = code == want_exit and want_text in out
        bad += not ok
        print(f"{'PASS' if ok else 'FAIL'} {name}: exit {code}; {out}")
    print(f"{len(CASES) - bad} of {len(CASES)} cases passed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
