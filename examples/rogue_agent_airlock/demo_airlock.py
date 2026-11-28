#!/usr/bin/env python3
"""Forge Milestone 3: 1-Command Runnable Rogue-Agent Airlock Adversarial Demo.

Launches:
  1. Mock Stripe API server (enforcing Bearer secret + Idempotency-Key deduplication),
  2. Stateless keyless Rust `relay/` (`forge-relay`) holding STRIPE_SECRET_KEY + HMAC key,
  3. Real verified ARM64 `kernels/airlock/build/forge-kernel` (native on Linux aarch64 or
     seamlessly via `docker run --platform linux/arm64` on macOS Apple Silicon),
  4. Simulated prompt-injected rogue agent firing 6 live attacks + legitimate idempotent calls.

Verifies 100% of attacks fail ($0 leaked even across `kill -9` + torn disk slot corruption)
and legitimate spend/refund calls settle idempotently.
"""
from __future__ import annotations

import http.client
import http.server
import json
import os
import platform
import secrets
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
KERNEL_BIN = ROOT / "kernels" / "airlock" / "build" / "forge-kernel"
RELAY_BIN = ROOT / "relay" / "target" / "release" / "forge-relay"
DOCKER_IMG = os.environ.get("FORGE_ARM64_DOCKER_IMAGE", "forge-arm64-tools:bookworm")
STRIPE_SECRET = "sk_live_forge_airlock_secret_never_given_to_agent"


def free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class MockStripeState:
    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.idemp_cache: dict[str, dict] = {}
        self.charges_cents = 0
        self.refunds_cents = 0
        self.unauthorized_attempts = 0


def start_mock_stripe(port: int, state: MockStripeState) -> http.server.ThreadingHTTPServer:
    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, fmt: str, *args) -> None:
            return

        def do_POST(self) -> None:
            auth = self.headers.get("Authorization", "")
            if auth != f"Bearer {STRIPE_SECRET}":
                with state.lock:
                    state.unauthorized_attempts += 1
                body = json.dumps({"error": "unauthorized"}).encode()
                self.send_response(401)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return

            length = int(self.headers.get("Content-Length", "0"))
            payload = json.loads(self.rfile.read(length).decode())
            ikey = self.headers.get("Idempotency-Key", "")
            with state.lock:
                if ikey and ikey in state.idemp_cache:
                    resp = dict(state.idemp_cache[ikey])
                    resp["idempotent_replay"] = True
                else:
                    amt = int(payload["amount"])
                    if self.path == "/v1/charges":
                        state.charges_cents += amt
                        resp = {"id": f"ch_{ikey}", "status": "succeeded", "amount": amt, "idempotent_replay": False}
                    elif self.path == "/v1/refunds":
                        state.refunds_cents += amt
                        resp = {"id": f"re_{ikey}", "status": "succeeded", "amount": amt, "idempotent_replay": False}
                    else:
                        self.send_response(404)
                        self.end_headers()
                        return
                    if ikey:
                        state.idemp_cache[ikey] = resp

            body = json.dumps(resp).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

    srv = http.server.ThreadingHTTPServer(("127.0.0.1", port), Handler)
    t = threading.Thread(target=srv.serve_forever, daemon=True)
    t.start()
    return srv


def enc_req(op: int, agent: int, arg2: int, amt: int, arg4: int) -> bytes:
    return struct.pack("<8Q", op, agent, arg2, amt, arg4, 0, 0, 0)


def dec_resp(raw: bytes) -> dict:
    assert len(raw) == 128, f"expected 128B response, got {len(raw)}"
    w = struct.unpack("<16Q", raw)
    tag_bytes = struct.pack("<4Q", w[12], w[13], w[14], w[15])
    return {
        "ok": w[0], "code": w[1], "deposits": w[2], "balance": w[3],
        "net_spent": w[4], "refunds": w[5], "nonce": w[6], "last_tx": w[7],
        "tok_seq": w[8], "tok_op": w[9], "tok_dest": w[10], "tok_amt": w[11],
        "tok_hex": tag_bytes.hex(),
    }


def format_token_header(r: dict) -> str:
    return f"{r['tok_seq']}:{r['tok_op']}:{r['tok_dest']}:{r['tok_amt']}:{r['balance']}:{r['tok_hex']}"


class AirlockKernelProc:
    def __init__(self, state_dir: Path) -> None:
        self.state_dir = state_dir
        self.native = platform.system() == "Linux" and platform.machine() in ("aarch64", "arm64")
        if self.native:
            import fcntl
            fd3 = os.open(state_dir / "airlock.state", os.O_RDWR | os.O_CREAT, 0o600)
            fd4 = os.open(state_dir / "boot.key", os.O_RDONLY)

            def setup() -> None:
                t3 = fcntl.fcntl(fd3, fcntl.F_DUPFD, 10)
                t4 = fcntl.fcntl(fd4, fcntl.F_DUPFD, 10)
                os.dup2(t3, 3)
                os.dup2(t4, 4)
                os.set_inheritable(3, True)
                os.set_inheritable(4, True)
                os.close(t3)
                os.close(t4)
                if fd3 > 4:
                    os.close(fd3)
                if fd4 > 4:
                    os.close(fd4)

            self.proc = subprocess.Popen(
                [str(KERNEL_BIN)],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                preexec_fn=setup,
                close_fds=False,
            )
            os.close(fd3)
            os.close(fd4)
        else:
            self.proc = subprocess.Popen(
                [
                    "docker", "run", "--rm", "-i", "--platform", "linux/arm64",
                    "-v", f"{KERNEL_BIN.parent}:/work:ro",
                    "-v", f"{state_dir}:/state",
                    DOCKER_IMG,
                    "sh", "-eu", "-c",
                    "exec /work/forge-kernel 3<>/state/airlock.state 4</state/boot.key",
                ],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
            )

    def call(self, frame: bytes) -> dict:
        assert self.proc.stdin and self.proc.stdout
        self.proc.stdin.write(frame)
        self.proc.stdin.flush()
        buf = bytearray()
        while len(buf) < 128:
            ch = self.proc.stdout.read(128 - len(buf))
            if not ch:
                raise RuntimeError(f"kernel EOF after {len(buf)} bytes")
            buf.extend(ch)
        return dec_resp(bytes(buf))

    def kill9(self) -> None:
        self.proc.kill()
        self.proc.wait()

    def close(self) -> int:
        if self.proc.stdin:
            self.proc.stdin.close()
        return self.proc.wait()


def call_relay(relay_port: int, token_hdr: str | None) -> tuple[int, dict]:
    conn = http.client.HTTPConnection("127.0.0.1", relay_port, timeout=5)
    headers = {"Content-Type": "application/json"}
    if token_hdr is not None:
        headers["X-Forge-Token"] = token_hdr
    conn.request("POST", "/v1/execute", body="{}", headers=headers)
    resp = conn.getresponse()
    body = json.loads(resp.read().decode())
    conn.close()
    return resp.status, body


def main() -> int:
    if not KERNEL_BIN.is_file():
        print(f"error: missing compiled ARM64 kernel {KERNEL_BIN}", file=sys.stderr)
        return 1
    if not RELAY_BIN.is_file():
        print("Building Rust forge-relay (--release)...")
        subprocess.run(
            ["cargo", "build", "--release", "--manifest-path", str(ROOT / "relay" / "Cargo.toml")],
            check=True,
        )

    stripe_port = free_port()
    relay_port = free_port()
    stripe_state = MockStripeState()
    stripe_srv = start_mock_stripe(stripe_port, stripe_state)

    with tempfile.TemporaryDirectory(prefix="forge-airlock-demo-") as tmp_s:
        tmp = Path(tmp_s)
        key_path = tmp / "boot.key"
        state_path = tmp / "airlock.state"
        key_bytes = secrets.token_bytes(32)
        key_path.write_bytes(key_bytes)
        state_path.write_bytes(b"")

        relay_env = dict(os.environ)
        relay_env.update({
            "RELAY_LISTEN": f"127.0.0.1:{relay_port}",
            "UPSTREAM_ADDR": f"127.0.0.1:{stripe_port}",
            "STRIPE_SECRET_KEY": STRIPE_SECRET,
            "FORGE_HMAC_KEY_FILE": str(key_path),
        })
        relay_proc = subprocess.Popen(
            [str(RELAY_BIN)],
            env=relay_env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        # Wait briefly for relay TCP listener
        for _ in range(50):
            try:
                with socket.create_connection(("127.0.0.1", relay_port), timeout=0.1):
                    break
            except OSError:
                time.sleep(0.05)

        try:
            print("=== Forge M3 Rogue-Agent Airlock Demo ===")
            print(f"[1] Mock Stripe API listening on 127.0.0.1:{stripe_port}")
            print(f"[2] Rust Keyless Relay listening on 127.0.0.1:{relay_port} (owns STRIPE_SECRET_KEY)")
            print(f"[3] Spawning verified ARM64 Airlock Kernel: {KERNEL_BIN.relative_to(ROOT)}")

            k = AirlockKernelProc(tmp)
            # Admin configures budget: $500.00 deposit, $300.00 cap, allowlist={dest 0, dest 1}
            r_adm = k.call(enc_req(1, 0, 0b11, 50_000, 30_000))
            assert r_adm["ok"] == 1 and r_adm["balance"] == 50_000, f"admin setup failed: {r_adm}"
            print("    Admin configured: deposit=$500.00, rolling_cap=$300.00, allowlist={0,1}")

            # Legitimate Spend #1 ($120.00 to dest 0, nonce=1)
            r_sp1 = k.call(enc_req(2, 7, 0, 12_000, 1))
            assert r_sp1["ok"] == 1 and r_sp1["code"] == 0 and r_sp1["tok_op"] == 2
            st_code, st_body = call_relay(relay_port, format_token_header(r_sp1))
            assert st_code == 200 and st_body["amount"] == 12_000 and not st_body["idempotent_replay"]
            print(f"    Legit spend $120.00 -> kernel minted HMAC cap token (seq={r_sp1['tok_seq']}) -> Stripe 200 OK ({st_body['id']})")

            # Attack 1: Over-cap spend ($180.01 would push net_spent to $300.01 > $300.00 cap)
            a1 = k.call(enc_req(2, 7, 0, 18_001, 2))
            assert a1["ok"] == 0 and a1["code"] == 2 and a1["tok_op"] == 0
            print("    [ATTACK 1 BLOCKED] Over-cap spend ($180.01 > $180.00 remaining) -> DENIED (code=2, no token)")

            # Attack 2: Non-allowlisted destination (attacker wallet dest=9)
            a2 = k.call(enc_req(2, 7, 9, 1_000, 2))
            assert a2["ok"] == 0 and a2["code"] == 2 and a2["tok_op"] == 0
            print("    [ATTACK 2 BLOCKED] Non-allowlisted destination (dest=9) -> DENIED (code=2, no token)")

            # Attack 3: Replayed / tampered nonce (nonce=1 with altered amount $120.01)
            a3 = k.call(enc_req(2, 7, 0, 12_001, 1))
            assert a3["ok"] == 0 and a3["code"] == 2 and a3["tok_op"] == 0
            print("    [ATTACK 3 BLOCKED] Replayed & tampered nonce=1 ($120.01) -> DENIED (code=2, no token)")

            # Attack 4: Forged HMAC capability token sent directly to keyless Rust relay
            bad_hex = "00" * 32
            st_forged, body_forged = call_relay(relay_port, f"99:2:0:50000:0:{bad_hex}")
            assert st_forged == 403, f"expected 403 on forged HMAC, got {st_forged}"
            tampered_hdr = f"{r_sp1['tok_seq']}:2:0:12001:{r_sp1['balance']}:{r_sp1['tok_hex']}"
            st_tamp, _ = call_relay(relay_port, tampered_hdr)
            assert st_tamp == 403, f"expected 403 on tampered token amount, got {st_tamp}"
            print(f"    [ATTACK 4 BLOCKED] Forged & tampered HMAC tokens -> Rust relay 403 Forbidden ({body_forged['error']})")

            # Attack 5: Mid-run `kill -9` + torn-slot corruption + reboot cap-reset attack!
            k.kill9()
            raw = bytearray(state_path.read_bytes())
            # Corrupt inactive Slot B (or Slot A if B is active) to simulate power-loss torn write!
            if len(raw) < 512:
                raw.extend(b"\x00" * (512 - len(raw)))
            # Latest gen is 2 (even -> Slot B at 256..512), so corrupt Slot A (0..256)!
            for j in range(16, 128):
                raw[j] ^= 0xAA
            state_path.write_bytes(raw)
            k = AirlockKernelProc(tmp)
            # Rebooted kernel MUST still remember $120 spent and deny $200 (> $180 cap left)!
            a5 = k.call(enc_req(2, 7, 0, 20_000, 2))
            assert a5["ok"] == 0 and a5["code"] == 2 and a5["net_spent"] == 12_000
            # Idempotent retry of spend #1 after reboot returns exact cached token (code=5) & Stripe dedups!
            r_retry = k.call(enc_req(2, 7, 0, 12_000, 1))
            assert r_retry["ok"] == 1 and r_retry["code"] == 5 and r_retry["tok_hex"] == r_sp1["tok_hex"]
            st_rep, body_rep = call_relay(relay_port, format_token_header(r_retry))
            assert st_rep == 200 and body_rep["idempotent_replay"] is True
            assert stripe_state.charges_cents == 12_000, "DOUBLE CHARGE DETECTED!"
            print("    [ATTACK 5 BLOCKED] kill -9 + torn-slot reboot cap-reset -> recovered exact state ($120 spent), denied $200, retry idempotent!")

            # Legitimate partial refund ($40.00 on tx=1) + Attack 6 (double-refund attack)
            r_ref = k.call(enc_req(3, 7, 0, 4_000, 1))
            assert r_ref["ok"] == 1 and r_ref["code"] == 0 and r_ref["tok_op"] == 3
            st_ref, body_ref = call_relay(relay_port, format_token_header(r_ref))
            assert st_ref == 200 and body_ref["amount"] == 4_000
            a6 = k.call(enc_req(3, 7, 0, 1_000, 1))
            assert a6["ok"] == 0 and a6["code"] == 3 and a6["tok_op"] == 0
            print("    [ATTACK 6 BLOCKED] Double-refund ($10.00 after $40.00 refund) -> DENIED (code=3, no token)")

            q_final = k.call(enc_req(4, 7, 0, 0, 0))
            rc = k.close()
            assert rc == 0, f"expected kernel exit 0, got {rc}"

            net_stripe = stripe_state.charges_cents - stripe_state.refunds_cents
            assert net_stripe == 8_000
            assert q_final["deposits"] == 50_000
            assert q_final["balance"] == 42_000
            assert q_final["net_spent"] == 8_000
            assert q_final["deposits"] == q_final["balance"] + q_final["net_spent"]
            assert stripe_state.unauthorized_attempts == 0

            print(
                f"DEMO_AIRLOCK_PASS attacks_blocked=6/6 leaked_cents=0 "
                f"settled_net_cents={net_stripe} kernel_balance_cents={q_final['balance']} "
                f"conservation={q_final['deposits']}=={q_final['balance']}+{q_final['net_spent']}"
            )
            return 0
        finally:
            relay_proc.terminate()
            relay_proc.wait(timeout=5)
            stripe_srv.shutdown()


if __name__ == "__main__":
    sys.exit(main())
