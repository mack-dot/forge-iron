#!/usr/bin/env python3
"""4-way golden-vector byte tests & live ARM64 kernel pipe verification for `guardrail`.

Verifies byte-for-byte identity across:
  1. Python (`sdk/guardrail/sdk.py`)
  2. TypeScript (`sdk/guardrail/sdk.ts`, native Node execution)
  3. Rust (`sdk/guardrail/src/lib.rs` via `cargo test`)
  4. HOL4 `EVAL` (`kernels/guardrail/hol4/forge_guardrailSpecTheory`)

Also verifies structural capability separation (`GuardrailAdmin` vs `GuardrailAgent`)
and runs live `GuardrailAdmin` + `GuardrailAgent` sessions against the real compiled
ARM64 `kernels/guardrail/build/forge-kernel` binary in Rust, Python, and TypeScript.
"""
from __future__ import annotations

import json
import os
import platform
import shutil
import subprocess
import sys
import threading
from pathlib import Path

SDK_DIR = Path(__file__).resolve().parent
ROOT = SDK_DIR.parent.parent
APP_DIR = ROOT / "kernels" / "guardrail"
KERNEL_BIN = APP_DIR / "build" / "forge-kernel"
DEFAULT_DOCKER_IMAGE = "forge-arm64-tools:bookworm"

sys.path.insert(0, str(SDK_DIR))
import sdk  # noqa: E402

GOLDEN_VECTORS = [
    ("budget_set_basic", sdk.budget_set_req(deposit=50000, cap=20000, allowlist_mask=0b1011, agent_id=7)),
    ("spend_normal", sdk.spend_req(agent_id=42, dest_id=3, amount=12500, nonce=1)),
    ("spend_u64_max_attack", sdk.spend_req(agent_id=1, dest_id=0, amount=(1 << 64) - 1, nonce=2)),
    ("refund_partial", sdk.refund_req(tx_id=9, amount=4000, agent_id=42)),
    ("query_zero", sdk.query_req(agent_id=99)),
]


def detect_live_runner() -> dict[str, str | None] | None:
    if not KERNEL_BIN.is_file():
        return None
    qemu = os.environ.get("FORGE_GUARDRAIL_QEMU")
    if qemu:
        return {"mode": "qemu", "qemu": qemu, "docker_image": None}
    if platform.system() == "Linux" and platform.machine() in ("aarch64", "arm64"):
        return {"mode": "native", "qemu": None, "docker_image": None}
    docker = shutil.which("docker")
    docker_image = os.environ.get("FORGE_GUARDRAIL_DOCKER", DEFAULT_DOCKER_IMAGE)
    if docker:
        chk = subprocess.run(
            [docker, "images", "-q", docker_image],
            capture_output=True,
            text=True,
        )
        if chk.returncode == 0 and chk.stdout.strip():
            return {"mode": "docker", "qemu": None, "docker_image": docker_image}
    return None


def check_python_roundtrip() -> dict[str, str]:
    out = {}
    for name, req in GOLDEN_VECTORS:
        raw = req.encode()
        assert len(raw) == 64, f"{name}: bad len {len(raw)}"
        assert sdk.RequestFrame.decode(raw) == req, f"{name}: Python round-trip mismatch"
        out[name] = raw.hex()
    for bad_val in (-1, 1 << 64):
        try:
            sdk.spend_req(agent_id=1, dest_id=0, amount=bad_val, nonce=1).encode()
        except Exception:
            pass
        else:
            raise AssertionError(f"Python encode failed to reject out-of-range u64: {bad_val}")
    for bad_len in (63, 65):
        try:
            sdk.RequestFrame.decode(b"\x00" * bad_len)
        except ValueError:
            pass
        else:
            raise AssertionError(f"Python decode failed to reject bad length: {bad_len}")

    # Direct instantiation of GuardrailAgent without admin token must fail
    try:
        sdk.GuardrailAgent(1, lambda r: sdk.ResponseFrame(0, 0, 0, 0, 0, 0, 0, 0))
    except TypeError:
        pass
    else:
        raise AssertionError("Python GuardrailAgent allowed direct construction without token")

    print(f"PASS python_roundtrip ({len(GOLDEN_VECTORS)} vectors + u64 bounds + capability guard)")
    return out


def check_typescript_bytes_and_live(py_hex: dict[str, str], runner: dict[str, str | None] | None) -> None:
    node = shutil.which("node")
    if not node:
        print("SKIP typescript_bytes (node not on PATH)")
        return
    sdk_ts_url = (SDK_DIR / "sdk.ts").resolve().as_uri()
    vectors_json = json.dumps([
        [name, str(r.op), str(r.agent_id), str(r.arg2), str(r.amount), str(r.arg4), str(r.reserved5), str(r.reserved6), str(r.reserved7)]
        for name, r in GOLDEN_VECTORS
    ])
    live_cfg = json.dumps({
        "enabled": runner is not None,
        "binary": str(KERNEL_BIN.resolve()),
        "qemu": runner["qemu"] if runner else None,
        "dockerImage": runner["docker_image"] if runner else None,
    })
    driver = f"""
import * as sdk from {json.dumps(sdk_ts_url)};

const vecs = {vectors_json};
const liveCfg = {live_cfg};
const res = {{}};

for (const [name, op, ag, a2, amt, a4, r5, r6, r7] of vecs) {{
  const req = {{
    op: BigInt(op), agentId: BigInt(ag), arg2: BigInt(a2), amount: BigInt(amt),
    arg4: BigInt(a4), reserved5: BigInt(r5), reserved6: BigInt(r6), reserved7: BigInt(r7),
  }};
  const b = sdk.encodeRequestFrame(req);
  const d = sdk.decodeRequestFrame(b);
  if (d.op !== req.op || d.agentId !== req.agentId || d.arg2 !== req.arg2 || d.amount !== req.amount || d.arg4 !== req.arg4) {{
    throw new Error("TS roundtrip mismatch: " + name);
  }}
  res[name] = Buffer.from(b).toString("hex");
}}

for (const badVal of [-1n, 1n << 64n]) {{
  let threw = false;
  try {{
    sdk.encodeRequestFrame({{ op: 2n, agentId: 1n, arg2: 0n, amount: badVal, arg4: 1n }});
  }} catch (e) {{
    threw = e instanceof RangeError;
  }}
  if (!threw) throw new Error("TS failed to throw RangeError for out-of-range u64: " + badVal);
}}

// Capability guard: direct GuardrailAgent construction without secret symbol fails
let forgedThrew = false;
try {{
  new sdk.GuardrailAgent(1n, async () => ({{ ok: 0n, code: 0n, deposits: 0n, balance: 0n, netSpent: 0n, refunds: 0n, lastNonce: 0n, lastTxId: 0n }}), Symbol("fake"));
}} catch (e) {{
  forgedThrew = e instanceof TypeError;
}}
if (!forgedThrew) throw new Error("TS GuardrailAgent allowed forged construction");

let liveChecked = false;
if (liveCfg.enabled) {{
  const opts = {{}};
  if (liveCfg.qemu) opts.qemu = liveCfg.qemu;
  if (liveCfg.dockerImage) opts.dockerImage = liveCfg.dockerImage;
  const admin = sdk.GuardrailAdmin.spawn(liveCfg.binary, opts);
  try {{
    const r0 = await admin.query(0n);
    if (r0.ok !== 1n || r0.deposits !== 0n) throw new Error("TS initial query failed");

    const r1 = await admin.depositAndConfigure(5000n, 3000n, 5n, 0n);
    if (r1.ok !== 1n || r1.deposits !== 5000n || r1.balance !== 5000n) {{
      throw new Error("TS depositAndConfigure failed");
    }}

    const agent = admin.mintAgent(7n);
    // Structural capability separation checks on agent
    if ("depositAndConfigure" in agent || "deposit_and_configure" in agent || "close" in agent || "sendFrame" in agent) {{
      throw new Error("TS GuardrailAgent exposed privileged admin method");
    }}
    const ownKeys = Reflect.ownKeys(agent);
    if (ownKeys.length !== 1 || ownKeys[0] !== "agentId") {{
      throw new Error("TS GuardrailAgent leaked private state: " + JSON.stringify(ownKeys));
    }}

    const rz = await agent.spend(0n, 0n, 1n);
    if (rz.ok !== 0n || rz.code !== 2n) throw new Error("TS zero spend not denied");

    const rd = await agent.spend(1n, 100n, 1n);
    if (rd.ok !== 0n || rd.code !== 2n) throw new Error("TS non-allowlisted dest not denied");

    const rov = await agent.spend(0n, 0xFFFFFFFFFFFFFFFFn, 1n);
    if (rov.ok !== 0n || rov.code !== 2n) throw new Error("TS u64 max spend not denied");

    const rs1 = await agent.spend(0n, 1200n, 1n);
    if (rs1.ok !== 1n || rs1.balance !== 3800n || rs1.netSpent !== 1200n || rs1.lastNonce !== 1n) {{
      throw new Error("TS spend 1200 failed");
    }}

    const rrep = await agent.spend(0n, 100n, 1n);
    if (rrep.ok !== 0n || rrep.code !== 2n) throw new Error("TS replay nonce not denied");

    const rover = await agent.spend(2n, 1801n, 2n);
    if (rover.ok !== 0n) throw new Error("TS over-cap spend not denied");

    const rexact = await agent.spend(2n, 1800n, 2n);
    if (rexact.ok !== 1n || rexact.netSpent !== 3000n || rexact.balance !== 2000n) {{
      throw new Error("TS exact-cap spend failed");
    }}

    const rref = await agent.refund(2n, 800n);
    if (rref.ok !== 1n || rref.balance !== 2800n || rref.netSpent !== 2200n || rref.refunds !== 800n) {{
      throw new Error("TS partial refund failed");
    }}

    const rdbl = await agent.refund(2n, 100n);
    if (rdbl.ok !== 0n || rdbl.code !== 3n) throw new Error("TS double refund not denied");

    // Concurrent queued queries through GuardrailAgent
    const [q1, q2] = await Promise.all([agent.query(), agent.query()]);
    if (q1.balance !== 2800n || q2.balance !== 2800n) throw new Error("TS concurrent queries failed");

    liveChecked = true;
  }} finally {{
    const exitCode = await admin.close();
    if (exitCode !== 0) throw new Error("TS admin.close() expected exit 0, got " + exitCode);
  }}
}}

console.log(JSON.stringify({{ hex: res, liveChecked }}));
"""
    p = subprocess.run([node, "--input-type=module", "-e", driver], capture_output=True, text=True)
    assert p.returncode == 0, f"TypeScript driver failed (exit {p.returncode}):\nSTDOUT: {p.stdout}\nSTDERR: {p.stderr}"
    parsed = json.loads(p.stdout.strip().splitlines()[-1])
    ts_hex = parsed["hex"]
    for name, hx in py_hex.items():
        assert ts_hex[name] == hx, f"TS vs Python byte mismatch on {name}: {ts_hex[name]} != {hx}"
    live_msg = " + live ARM64 GuardrailAdmin/Agent" if parsed["liveChecked"] else ""
    print(f"PASS typescript_vs_python ({len(GOLDEN_VECTORS)} vectors identical byte-for-byte + u64 bounds{live_msg})")


def check_rust_bytes_and_live(py_hex: dict[str, str], runner: dict[str, str | None] | None) -> None:
    cargo = shutil.which("cargo")
    if not cargo or not (SDK_DIR / "Cargo.toml").is_file():
        print("SKIP rust_bytes (cargo not on PATH or Cargo.toml missing)")
        return
    env = dict(os.environ)
    env["FORGE_GUARDRAIL_BIN"] = str(KERNEL_BIN.resolve())
    if runner is not None:
        env["FORGE_REQUIRE_LIVE_KERNEL"] = "1"
        if runner["qemu"]:
            env["FORGE_GUARDRAIL_QEMU"] = runner["qemu"]
        if runner["docker_image"]:
            env["FORGE_GUARDRAIL_DOCKER"] = runner["docker_image"]
    p = subprocess.run(
        [cargo, "test", "--", "--nocapture"],
        cwd=SDK_DIR,
        env=env,
        capture_output=True,
        text=True,
        timeout=180,
    )
    assert p.returncode == 0, f"Rust cargo test failed (exit {p.returncode}):\nSTDOUT:\n{p.stdout}\nSTDERR:\n{p.stderr}"
    rust_hex = {}
    for ln in p.stdout.splitlines():
        if ln.startswith("RUST_VEC ") and "=" in ln:
            k, v = ln[9:].split("=", 1)
            rust_hex[k.strip()] = v.strip().lower()
    for name, hx in py_hex.items():
        assert rust_hex.get(name) == hx, f"Rust vs Python byte mismatch on {name}: {rust_hex.get(name)} != {hx}"
    live_msg = " + live ARM64 GuardrailAdmin/Agent" if runner is not None else ""
    print(f"PASS rust_vs_python ({len(GOLDEN_VECTORS)} vectors identical byte-for-byte + partial I/O + u64 bounds{live_msg})")


def check_python_live_kernel(runner: dict[str, str | None] | None) -> None:
    if runner is None:
        print("SKIP python_live_kernel (no native ARM64 / docker / qemu runner)")
        return
    with sdk.GuardrailAdmin(
        KERNEL_BIN,
        qemu=runner["qemu"],
        docker_image=runner["docker_image"],
    ) as admin:
        r0 = admin.query()
        assert r0 == sdk.ResponseFrame(1, 0, 0, 0, 0, 0, 0, 0) and r0.is_conserved

        r1 = admin.deposit_and_configure(deposit=5000, cap=3000, allowlist_mask=0b101)
        assert r1 == sdk.ResponseFrame(1, 0, 5000, 5000, 0, 0, 0, 0)

        agent = admin.mint_agent(agent_id=7)
        assert agent.agent_id == 7
        assert not hasattr(agent, "deposit_and_configure")
        assert not hasattr(agent, "close")
        assert not hasattr(agent, "_pipe")
        try:
            agent._send(sdk.budget_set_req(1, 1, 1))
        except PermissionError:
            pass
        else:
            raise AssertionError("Python GuardrailAgent allowed op=1 through _send")

        assert agent.spend(dest_id=0, amount=0, nonce=1).code == 2
        assert agent.spend(dest_id=1, amount=100, nonce=1).code == 2
        assert agent.spend(dest_id=0, amount=(1 << 64) - 1, nonce=1).code == 2

        sp1 = agent.spend(dest_id=0, amount=1200, nonce=1)
        assert sp1 == sdk.ResponseFrame(1, 0, 5000, 3800, 1200, 0, 1, 1) and sp1.is_conserved
        assert agent.spend(dest_id=0, amount=100, nonce=1).code == 2
        assert agent.spend(dest_id=2, amount=1801, nonce=2).ok == 0

        sp2 = agent.spend(dest_id=2, amount=1800, nonce=2)
        assert sp2 == sdk.ResponseFrame(1, 0, 5000, 2000, 3000, 0, 2, 2)

        rf1 = agent.refund(tx_id=2, amount=800)
        assert rf1 == sdk.ResponseFrame(1, 0, 5000, 2800, 2200, 800, 2, 2)
        assert agent.refund(tx_id=2, amount=100).code == 3

        # Thread-safe concurrent queries from multiple threads
        results: list[sdk.ResponseFrame] = []
        lock = threading.Lock()

        def worker() -> None:
            q = agent.query()
            with lock:
                results.append(q)

        threads = [threading.Thread(target=worker) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=15)
        assert len(results) == 4 and all(q == rf1 for q in results)

        exit_code = admin.close()
        assert exit_code == 0, f"expected clean exit 0, got {exit_code}"
    print(f"PASS python_live_kernel (GuardrailAdmin + restricted GuardrailAgent via {runner['mode']}, exit 0)")


def check_hol4_eval_bytes(py_hex: dict[str, str]) -> None:
    hol = shutil.which("hol")
    hol_dir = APP_DIR / "hol4"
    has_uo = (
        (hol_dir / "forge_guardrailSpecTheory.uo").is_file()
        or (hol_dir / ".hol" / "objs" / "forge_guardrailSpecTheory.uo").is_file()
    )
    if not hol or not has_uo:
        print("SKIP hol4_eval_bytes (hol not on PATH or forge_guardrailSpecTheory not yet compiled)")
        return
    lines = [
        'val _ = load "forge_guardrailSpecTheory";',
        'open HolKernel Parse boolLib bossLib wordsLib forge_frame64SpecTheory forge_guardrailSpecTheory;',
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
    runner = detect_live_runner()
    py_hex = check_python_roundtrip()
    check_typescript_bytes_and_live(py_hex, runner)
    check_rust_bytes_and_live(py_hex, runner)
    check_python_live_kernel(runner)
    check_hol4_eval_bytes(py_hex)
    print("ALL 4-WAY GOLDEN VECTOR & LIVE KERNEL TESTS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
