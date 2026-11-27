#!/usr/bin/env python3
"""Cross-language golden-vector byte tests for `guardrail` (Python <-> TypeScript <-> HOL4 EVAL)."""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

SDK_DIR = Path(__file__).resolve().parent
ROOT = SDK_DIR.parent.parent
APP_DIR = ROOT / "kernels" / "guardrail"
sys.path.insert(0, str(SDK_DIR))
import sdk  # noqa: E402

GOLDEN_VECTORS = [
    ("budget_set_basic", sdk.budget_set_req(deposit=50000, cap=20000, allowlist_mask=0b1011, agent_id=7)),
    ("spend_normal", sdk.spend_req(agent_id=42, dest_id=3, amount=12500, nonce=1)),
    ("spend_u64_max_attack", sdk.spend_req(agent_id=1, dest_id=0, amount=(1 << 64) - 1, nonce=2)),
    ("refund_partial", sdk.refund_req(tx_id=9, amount=4000, agent_id=42)),
    ("query_zero", sdk.query_req(agent_id=99)),
]


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
    print(f"PASS python_roundtrip ({len(GOLDEN_VECTORS)} vectors + u64 bounds)")
    return out


def check_typescript_bytes(py_hex: dict[str, str]) -> None:
    node = shutil.which("node")
    ts_src = (SDK_DIR / "sdk.ts").read_text()
    js = re.sub(r"export interface \w+ \{[^}]*\}", "", ts_src)
    js = re.sub(r"\):\s*(Uint8Array|RequestFrame|ResponseFrame|bigint)\b", ")", js)
    js = re.sub(r"\((\w+):\s*(RequestFrame|ResponseFrame|Uint8Array)\)", r"(\1)", js)
    js = re.sub(r":\s*(bigint|string)\b", "", js)
    js = js.replace("export const ", "const ").replace("export function ", "function ")
    vectors_js = json.dumps([
        [name, str(r.op), str(r.agent_id), str(r.arg2), str(r.amount), str(r.arg4), str(r.reserved5), str(r.reserved6), str(r.reserved7)]
        for name, r in GOLDEN_VECTORS
    ])
    driver = (
        js
        + "\nconst vecs = "
        + vectors_js
        + """;
const res = {};
for (const [name, op, ag, a2, amt, a4, r5, r6, r7] of vecs) {
  const req = { op: BigInt(op), agentId: BigInt(ag), arg2: BigInt(a2), amount: BigInt(amt), arg4: BigInt(a4), reserved5: BigInt(r5), reserved6: BigInt(r6), reserved7: BigInt(r7) };
  const b = encodeRequestFrame(req);
  const d = decodeRequestFrame(b);
  if (d.op !== req.op || d.agentId !== req.agentId || d.arg2 !== req.arg2 || d.amount !== req.amount || d.arg4 !== req.arg4) {
    throw new Error("TS roundtrip mismatch: " + name);
  }
  res[name] = Buffer.from(b).toString("hex");
}
for (const badVal of [-1n, 1n << 64n]) {
  let threw = false;
  try {
    encodeRequestFrame({ op: 1n, agentId: 1n, arg2: 0n, amount: badVal, arg4: 1n, reserved5: 0n, reserved6: 0n, reserved7: 0n });
  } catch (e) {
    threw = e instanceof RangeError;
  }
  if (!threw) throw new Error("TS failed to throw RangeError for out-of-range u64: " + badVal);
}
console.log(JSON.stringify(res));
"""
    )
    if not node:
        print("SKIP typescript_bytes (node not on PATH)")
        return
    p = subprocess.run([node, "-e", driver], capture_output=True, text=True, check=True)
    ts_hex = json.loads(p.stdout.strip())
    for name, hx in py_hex.items():
        assert ts_hex[name] == hx, f"TS vs Python byte mismatch on {name}: {ts_hex[name]} != {hx}"
    print(f"PASS typescript_vs_python ({len(GOLDEN_VECTORS)} vectors identical byte-for-byte)")


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
    py_hex = check_python_roundtrip()
    check_typescript_bytes(py_hex)
    check_hol4_eval_bytes(py_hex)
    print("ALL GOLDEN VECTOR BYTE TESTS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
