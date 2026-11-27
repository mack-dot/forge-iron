#!/usr/bin/env python3
"""Automated tests for the persistent warm HOL4 goal server (`hol_repl.py` + `holctl`).

Verifies:
  1. Warm daemon startup & health check (`start`, `status`)
  2. Fast tactic step latency (< 0.5s) on `goal` + `step`
  3. Clean ~5.0s timeout recovery on looping tactic `simp [WORD_ADD_COMM]`
     without killing the daemon or corrupting the proof state
  4. Clean undo (`back`), recovery proof step (`blastLib.BBLAST_TAC`), `show`,
     `reset`, and graceful `stop`
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
HOLCTL = ROOT / "scripts" / "holctl"


def run_ctl(sock: str, *args: str) -> tuple[int, dict]:
    p = subprocess.run(
        [sys.executable, str(HOLCTL), "--sock", sock, "--json", *args],
        capture_output=True,
        text=True,
        timeout=90,
    )
    data = json.loads(p.stdout.strip()) if p.stdout.strip() else {"status": "error", "output": p.stderr}
    return p.returncode, data


def main() -> int:
    if not shutil.which("hol"):
        print("FAIL: hol not on PATH")
        return 1

    with tempfile.TemporaryDirectory(prefix="forge-holctl-test-") as td:
        sock = str(Path(td) / "hol.sock")
        try:
            # 1. Start daemon (use forge_factory.heap if present, else empty/default)
            heap = str(ROOT / "forge_factory.heap") if (ROOT / "forge_factory.heap").is_file() else ""
            rc, r = run_ctl(sock, "start", "--heap", heap, "--cwd", str(ROOT))
            assert rc == 0 and r["status"] == "ok", f"start failed: {r}"
            hol_pid = r["hol_pid"]
            print(f"PASS start: hol_pid={hol_pid} heap={r.get('heap')} startup_ms={r.get('startup_ms')}")

            # 2. Fast tactic step (< 0.5s)
            rc, r = run_ctl(sock, "goal", "1 + 1 = 2")
            assert rc == 0 and r["status"] == "ok", f"goal failed: {r}"
            t0 = time.monotonic()
            rc, r = run_ctl(sock, "step", "simp []")
            dt = time.monotonic() - t0
            assert rc == 0 and r["status"] == "ok", f"fast step failed: {r}"
            assert "goal proved" in r["output"].lower(), f"expected goal proved, got: {r['output']}"
            assert dt < 0.5, f"step latency {dt:.3f}s >= 0.5s"
            print(f"PASS fast_step: wall={dt*1000:.1f}ms hol_ms={r['elapsed_ms']}ms")

            # 3. Reset & looping tactic timeout recovery (~5.0s)
            rc, r = run_ctl(sock, "reset")
            assert rc == 0, f"reset failed: {r}"
            rc, r = run_ctl(sock, "goal", "(a:word64) + b + c = c + b + a")
            assert rc == 0 and r["status"] == "ok", f"word goal failed: {r}"
            t0 = time.monotonic()
            rc, r = run_ctl(
                sock,
                "step",
                "REWRITE_TAC [wordsTheory.WORD_ADD_COMM]",
                "--timeout",
                "5.0",
            )
            dt = time.monotonic() - t0
            assert rc == 124 and r["status"] == "timeout", f"expected timeout (124), got rc={rc} r={r}"
            assert 4.5 <= dt <= 7.5, f"expected ~5.0s timeout, got {dt:.2f}s"
            print(f"PASS timeout_recovery: wall={dt:.2f}s hol_ms={r['elapsed_ms']}ms")

            # 4. Verify daemon survived with exact same HOL PID and intact goal
            rc, st = run_ctl(sock, "status")
            assert rc == 0 and st["alive"] and st["hol_pid"] == hol_pid, f"daemon died or restarted: {st}"
            rc, sh = run_ctl(sock, "show")
            assert rc == 0 and "a + b + c = c + b + a" in sh["output"], f"goal corrupted after timeout: {sh}"
            print(f"PASS alive_after_timeout: same hol_pid={hol_pid}")

            # 5. Clean undo (`back`) + follow-up proof step
            rc, r = run_ctl(sock, "step", "Cases_on `a`")
            assert rc == 0 and r["status"] == "ok", f"Cases_on failed: {r}"
            t0 = time.monotonic()
            rc, r = run_ctl(sock, "back")
            dt_back = time.monotonic() - t0
            assert rc == 0 and r["status"] == "ok" and "a + b + c = c + b + a" in r["output"], f"back failed: {r}"
            assert dt_back < 0.5, f"back latency {dt_back:.3f}s >= 0.5s"
            print(f"PASS back_undo: wall={dt_back*1000:.1f}ms hol_ms={r['elapsed_ms']}ms")

            t0 = time.monotonic()
            rc, r = run_ctl(sock, "step", "blastLib.BBLAST_TAC")
            dt_blast = time.monotonic() - t0
            assert rc == 0 and r["status"] == "ok" and "goal proved" in r["output"].lower(), f"BBLAST failed: {r}"
            assert dt_blast < 0.5, f"BBLAST latency {dt_blast:.3f}s >= 0.5s"
            print(f"PASS post_recovery_proof: wall={dt_blast*1000:.1f}ms hol_ms={r['elapsed_ms']}ms")

            rc, r = run_ctl(sock, "reset")
            assert rc == 0, f"final reset failed: {r}"
            print("ALL 6 HOLCTL WARM DAEMON TESTS PASSED")
            return 0
        finally:
            try:
                run_ctl(sock, "stop")
            except Exception:
                pass


if __name__ == "__main__":
    sys.exit(main())
