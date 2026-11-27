#!/usr/bin/env python3
"""Persistent Warm HOL4 Goal Server (Unix-socket daemon).

Keeps one warm `hol` (optionally `--holstate=forge_factory.heap`) process alive
in RAM and accepts JSON-line commands over a Unix domain socket:
  - ping / status / stop
  - eval  : run arbitrary SML declarations (with timeout)
  - goal  : set a new proof goal (`g`)
  - step  : apply a tactic (`e`) inside `TimeLimit.timeLimit` (default 5.0s)
  - back  : undo last tactic step (`b()`)
  - show  : print current goal state (`p()`)
  - reset : drop current goal (`drop()`)

Every tactic step is wrapped in SML `TimeLimit.timeLimit` (Poly/ML watchdog
thread interrupting the worker cleanly) so looping tactics like
`simp [WORD_ADD_COMM]` abort in ~5.0s without killing the warm HOL4 process.
"""
from __future__ import annotations

import argparse
import json
import os
import select
import signal
import socket
import subprocess
import sys
import threading
import time
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SOCK = os.environ.get("FORGE_HOL_SOCK", f"/tmp/forge-hol-repl-{os.getuid()}.sock")
DEFAULT_TIMEOUT = 5.0

HOL_PRELUDE_SML = r"""
open HolKernel Parse boolLib bossLib proofManagerLib;
val _ = (load "wordsLib"; load "blastLib");
open wordsLib blastLib;
val _ = Globals.linewidth := 100;
val _ = Parse.current_backend := PPBackEnd.raw_terminal;
val _ = Thread.setAttributes [Thread.InterruptState Thread.InterruptAsynch];

structure TimeLimit =
struct
  exception TimeOut
  fun timeLimit (t : Time.time) (f : 'a -> 'b) (x : 'a) : 'b =
    let
      val me = Thread.self ()
      val m = Mutex.mutex ()
      val cv = ConditionVar.conditionVar ()
      val done = ref false
      val timed_out = ref false
      val deadline = Time.+ (Time.now (), t)
      val _ = Thread.fork (fn () => (
        Mutex.lock m;
        let
          fun loop () =
            if !done then ()
            else
              let val ok = ConditionVar.waitUntil (cv, m, deadline)
              in if !done then ()
                 else if not ok then (
                   timed_out := true;
                   (Thread.interrupt me) handle _ => ()
                 ) else loop ()
              end
        in loop () end;
        Mutex.unlock m
      ), [])
      fun finish () = (
        Mutex.lock m;
        done := true;
        ConditionVar.signal cv;
        Mutex.unlock m
      )
      datatype 'r outcome = Ok of 'r | Raised of exn
      val res =
        (let val v = f x in finish (); Ok v end)
        handle e => (finish (); Raised e)
    in
      case res of
        Ok v => v
      | Raised e =>
          if !timed_out then raise TimeOut else PolyML.Exception.reraise e
    end
end;

fun forge_fmt_goal () =
  HOLPP.pp_to_string 100 proofManagerLib.pp_proof (proofManagerLib.p ())
  handle HOL_ERR _ => "<no active goal>";

fun forge_safe_drop () =
  ((ignore (proofManagerLib.drop ()); "dropped")
   handle HOL_ERR _ => "no active goal");
"""


def sml_escape(s: str) -> str:
    return (
        s.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )


def find_default_heap(root: Path) -> str | None:
    env_heap = os.environ.get("FORGE_HOL_HEAP")
    if env_heap and Path(env_heap).is_file():
        return str(Path(env_heap).resolve())
    factory = root / "forge_factory.heap"
    if factory.is_file():
        return str(factory)
    cakeml = os.environ.get("CAKEMLDIR")
    if cakeml:
        cand = Path(cakeml) / "cv_translator" / "cake_compile_heap"
        if cand.is_file():
            return str(cand)
    return None


class HolSession:
    def __init__(self, hol_bin: str, heap: str | None, cwd: str) -> None:
        self.hol_bin = hol_bin
        self.heap = heap
        self.cwd = cwd
        self.lock = threading.Lock()
        self.started_at = time.monotonic()
        self.startup_ms = 0.0
        self._rx_buf = bytearray()
        self.proc = self._spawn()

    def _read_until_nul(self, hard_timeout: float) -> tuple[str, str]:
        if not self.is_alive():
            return "dead", ""
        assert self.proc.stdout is not None
        fd = self.proc.stdout.fileno()
        deadline = time.monotonic() + hard_timeout
        sent_sigint = False

        while True:
            nul = self._rx_buf.find(b"\x00")
            if nul != -1:
                msg = bytes(self._rx_buf[:nul]).decode("utf-8", errors="replace").strip()
                del self._rx_buf[: nul + 1]
                return "ok", msg

            rem = deadline - time.monotonic()
            if rem <= 0:
                if not sent_sigint:
                    sent_sigint = True
                    try:
                        self.proc.send_signal(signal.SIGINT)
                    except OSError:
                        pass
                    deadline = time.monotonic() + 3.0
                    continue
                return "hard_timeout", bytes(self._rx_buf).decode("utf-8", errors="replace")

            r, _, _ = select.select([fd], [], [], min(rem, 0.25))
            if not r:
                if self.proc.poll() is not None:
                    return "dead", bytes(self._rx_buf).decode("utf-8", errors="replace")
                continue
            chunk = os.read(fd, 65536)
            if not chunk:
                return "dead", bytes(self._rx_buf).decode("utf-8", errors="replace")
            self._rx_buf.extend(chunk)

    def _spawn(self) -> subprocess.Popen[bytes]:
        t0 = time.monotonic()
        cmd = [self.hol_bin, "--zero"]
        if self.heap:
            cmd.append(f"--holstate={self.heap}")
        proc = subprocess.Popen(
            cmd,
            cwd=self.cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=0,
        )
        self.proc = proc
        # Wait for hol --zero initial banner NUL terminator
        st0, out0 = self._read_until_nul(hard_timeout=60.0)
        if st0 != "ok":
            raise RuntimeError(f"HOL4 startup banner failed ({st0}): {out0}")
        status, out = self._exec_raw(HOL_PRELUDE_SML, hard_timeout=60.0)
        if status != "ok" or "Static Errors" in out or "Exception-" in out:
            raise RuntimeError(f"HOL4 prelude failed ({status}): {out}")
        self.startup_ms = (time.monotonic() - t0) * 1000.0
        return proc

    def is_alive(self) -> bool:
        return self.proc is not None and self.proc.poll() is None

    def close(self) -> None:
        if self.proc and self.proc.poll() is None:
            try:
                if self.proc.stdin:
                    self.proc.stdin.close()
                self.proc.wait(timeout=3.0)
            except Exception:
                self.proc.kill()
                self.proc.wait()

    def _exec_raw(self, sml_body: str, hard_timeout: float) -> tuple[str, str]:
        if not self.is_alive():
            raise RuntimeError("HOL4 child process is not running")
        assert self.proc.stdin is not None
        payload = (sml_body.rstrip() + "\n\x00").encode("utf-8")
        self.proc.stdin.write(payload)
        self.proc.stdin.flush()
        return self._read_until_nul(hard_timeout=hard_timeout)

    def handle(self, req: dict) -> dict:
        cmd = req.get("cmd", "")
        with self.lock:
            if cmd == "ping":
                return {
                    "status": "ok",
                    "alive": self.is_alive(),
                    "pid": os.getpid(),
                    "hol_pid": self.proc.pid if self.proc else None,
                    "heap": self.heap,
                    "cwd": self.cwd,
                    "startup_ms": round(self.startup_ms, 1),
                    "uptime_s": round(time.monotonic() - self.started_at, 2),
                }

            if cmd == "status":
                t0 = time.monotonic()
                st, out = self._exec_raw(
                    'val _ = (TextIO.output (TextIO.stdOut, forge_fmt_goal () ^ "\\n"); '
                    'TextIO.flushOut TextIO.stdOut);',
                    hard_timeout=10.0,
                )
                return {
                    "status": "ok" if st == "ok" else "error",
                    "alive": self.is_alive(),
                    "pid": os.getpid(),
                    "hol_pid": self.proc.pid if self.proc else None,
                    "heap": self.heap,
                    "cwd": self.cwd,
                    "startup_ms": round(self.startup_ms, 1),
                    "uptime_s": round(time.monotonic() - self.started_at, 2),
                    "goal": self._clean_hol_output(out),
                    "elapsed_ms": round((time.monotonic() - t0) * 1000.0, 2),
                }

            if cmd == "show":
                t0 = time.monotonic()
                st, out = self._exec_raw(
                    'val _ = (TextIO.output (TextIO.stdOut, forge_fmt_goal () ^ "\\n"); '
                    'TextIO.flushOut TextIO.stdOut);',
                    hard_timeout=10.0,
                )
                return {
                    "status": "ok" if st == "ok" else "error",
                    "output": self._clean_hol_output(out),
                    "elapsed_ms": round((time.monotonic() - t0) * 1000.0, 2),
                }

            if cmd == "reset":
                t0 = time.monotonic()
                st, out = self._exec_raw(
                    'val _ = (TextIO.output (TextIO.stdOut, forge_safe_drop () ^ "\\n"); '
                    'TextIO.flushOut TextIO.stdOut);',
                    hard_timeout=10.0,
                )
                return {
                    "status": "ok" if st == "ok" else "error",
                    "output": self._clean_hol_output(out),
                    "elapsed_ms": round((time.monotonic() - t0) * 1000.0, 2),
                }

            if cmd == "back":
                t0 = time.monotonic()
                body = (
                    'val _ = (\n'
                    '  (ignore (proofManagerLib.b ());\n'
                    '   TextIO.output (TextIO.stdOut, "__FORGE_RES=OK__\\n" ^ forge_fmt_goal () ^ "\\n"))\n'
                    '  handle e => TextIO.output (TextIO.stdOut, "__FORGE_RES=ERR__\\n" ^ General.exnMessage e ^ "\\n");\n'
                    '  TextIO.flushOut TextIO.stdOut\n'
                    ');'
                )
                st, out = self._exec_raw(body, hard_timeout=10.0)
                return self._parse_tagged_result(st, out, t0)

            if cmd == "goal":
                term = req.get("term", "")
                if not term.strip():
                    return {"status": "error", "output": "missing goal term"}
                t0 = time.monotonic()
                esc = sml_escape(term)
                body = (
                    'val _ = (\n'
                    f'  (ignore (proofManagerLib.set_goal ([], Parse.Term [HOLPP.QUOTE "{esc}"]));\n'
                    '   TextIO.output (TextIO.stdOut, "__FORGE_RES=OK__\\n" ^ forge_fmt_goal () ^ "\\n"))\n'
                    '  handle e => TextIO.output (TextIO.stdOut, "__FORGE_RES=ERR__\\n" ^ General.exnMessage e ^ "\\n");\n'
                    '  TextIO.flushOut TextIO.stdOut\n'
                    ');'
                )
                st, out = self._exec_raw(body, hard_timeout=20.0)
                return self._parse_tagged_result(st, out, t0)

            if cmd == "step":
                tactic = req.get("tactic", "")
                if not tactic.strip():
                    return {"status": "error", "output": "missing tactic"}
                timeout_s = float(req.get("timeout", DEFAULT_TIMEOUT))
                if timeout_s <= 0.0:
                    timeout_s = DEFAULT_TIMEOUT
                t0 = time.monotonic()
                body = (
                    'val _ = (\n'
                    f'  (let val _ = TimeLimit.timeLimit (Time.fromReal {timeout_s:.3f}) '
                    f'(fn () => proofManagerLib.e ({tactic})) ()\n'
                    '   in TextIO.output (TextIO.stdOut, "__FORGE_RES=OK__\\n" ^ forge_fmt_goal () ^ "\\n") end)\n'
                    '  handle TimeLimit.TimeOut =>\n'
                    '      TextIO.output (TextIO.stdOut, "__FORGE_RES=TIMEOUT__\\nTactic timed out after '
                    f'{timeout_s:.2f}s\\n" ^ forge_fmt_goal () ^ "\\n")\n'
                    '    | e =>\n'
                    '      TextIO.output (TextIO.stdOut, "__FORGE_RES=ERR__\\n" ^ General.exnMessage e ^ "\\n");\n'
                    '  TextIO.flushOut TextIO.stdOut\n'
                    ');'
                )
                st, out = self._exec_raw(body, hard_timeout=timeout_s + 5.0)
                return self._parse_tagged_result(st, out, t0)

            if cmd == "eval":
                sml = req.get("sml", "")
                if not sml.strip():
                    return {"status": "error", "output": "missing sml code"}
                timeout_s = float(req.get("timeout", 30.0))
                t0 = time.monotonic()
                st, out = self._exec_raw(sml, hard_timeout=timeout_s)
                cleaned = self._clean_hol_output(out)
                is_err = st != "ok" or "Static Errors" in cleaned or "Exception-" in cleaned
                return {
                    "status": "error" if is_err else "ok",
                    "output": cleaned,
                    "elapsed_ms": round((time.monotonic() - t0) * 1000.0, 2),
                }

            return {"status": "error", "output": f"unknown command: {cmd}"}

    @staticmethod
    def _clean_hol_output(out: str) -> str:
        lines = []
        for ln in out.splitlines():
            s = ln.strip()
            if s in ("val it = (): unit", ">", "> >", "val _ = (): unit"):
                continue
            if ln.startswith("> "):
                ln = ln[2:]
            lines.append(ln)
        return "\n".join(lines).strip()

    def _parse_tagged_result(self, st: str, out: str, t0: float) -> dict:
        elapsed_ms = round((time.monotonic() - t0) * 1000.0, 2)
        if st != "ok":
            return {"status": "error", "output": f"{st}: {out}", "elapsed_ms": elapsed_ms}
        for tag, status in (
            ("__FORGE_RES=OK__", "ok"),
            ("__FORGE_RES=TIMEOUT__", "timeout"),
            ("__FORGE_RES=ERR__", "error"),
        ):
            idx = out.find(tag)
            if idx != -1:
                body = self._clean_hol_output(out[idx + len(tag) :])
                return {"status": status, "output": body, "elapsed_ms": elapsed_ms}
        return {
            "status": "error",
            "output": self._clean_hol_output(out),
            "elapsed_ms": elapsed_ms,
        }


def serve(sock_path: Path, hol_bin: str, heap: str | None, cwd: str) -> int:
    if sock_path.exists():
        sock_path.unlink()
    sock_path.parent.mkdir(parents=True, exist_ok=True)
    pid_path = Path(str(sock_path) + ".pid")

    session = HolSession(hol_bin=hol_bin, heap=heap, cwd=cwd)
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(str(sock_path))
    os.chmod(sock_path, 0o600)
    srv.listen(8)
    pid_path.write_text(f"{os.getpid()}\n")

    stop_flag = False

    def handle_sig(_signum: int, _frame: object) -> None:
        nonlocal stop_flag
        stop_flag = True

    signal.signal(signal.SIGTERM, handle_sig)
    signal.signal(signal.SIGINT, handle_sig)
    srv.settimeout(0.5)

    try:
        while not stop_flag:
            try:
                conn, _ = srv.accept()
            except socket.timeout:
                if not session.is_alive():
                    break
                continue
            except OSError:
                break
            with conn:
                conn.settimeout(120.0)
                data = bytearray()
                while True:
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    data.extend(chunk)
                    if b"\n" in chunk:
                        break
                if not data:
                    continue
                try:
                    req = json.loads(data.decode("utf-8").splitlines()[0])
                except Exception as exc:
                    resp = {"status": "error", "output": f"bad json: {exc}"}
                else:
                    if req.get("cmd") == "stop":
                        resp = {"status": "ok", "output": "stopping"}
                        stop_flag = True
                    else:
                        resp = session.handle(req)
                conn.sendall((json.dumps(resp) + "\n").encode("utf-8"))
    finally:
        srv.close()
        session.close()
        for p in (sock_path, pid_path):
            try:
                p.unlink()
            except OSError:
                pass
    return 0


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description="Persistent warm HOL4 goal server daemon")
    p.add_argument("--sock", default=DEFAULT_SOCK, help="Unix socket path")
    p.add_argument("--hol", default=os.environ.get("FORGE_HOL_BIN", "hol"), help="hol binary")
    p.add_argument("--heap", default=None, help="HOL4 heap path (--holstate=...)")
    p.add_argument("--cwd", default=str(ROOT), help="Working directory for HOL4 process")
    args = p.parse_args(argv)

    heap = args.heap if args.heap is not None else find_default_heap(ROOT)
    if heap == "":
        heap = None
    return serve(Path(args.sock), args.hol, heap, args.cwd)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
