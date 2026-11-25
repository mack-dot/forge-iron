#!/usr/bin/env python3
"""The Iron Law gate.

end_to_end=true only if ALL of these hold:
  1. kernel/GATE.manifest exists and names holmake_dir, binary, hash_file,
     audit_theory, audit_theorem, compile_theory, and shim_theory (fixed
     key=value lines; no JSON or YAML).
  2. No `cheat`, `mk_thm`, `new_axiom`, `disk_thm`, `add_tag`, or
     `mk_oracle_thm` appears in any *.sml under kernel/ or spec-compiler/.
  3. `Holmake --no_prereqs` replays all proofs in holmake_dir with exit 0.
  4. Gate-owned HOL4 kernel audit (`scripts/hol_audit.sml`) passes with exit 0:
     - 0 hypotheses and DISK_THM-only oracle tags on all forge_* theories;
     - transitive DB.axioms closure equals ONLY the 4 standard bool axioms;
     - extracts raw verified bytes directly from the proved HOL4 theorems
       (code, data/bitmaps, export_arm8 veneers, and raw ARM64 shim).
  5. hash_file holds exactly 64 lowercase hex characters and matches
     SHA256(binary).
  6. Pure-Python ELF64 AArch64 check confirms static non-PIE ET_EXEC,
     zero PT_INTERP / PT_DYNAMIC, strict W^X, all vaddrs < 2^55 (P-LO55),
     zero unverified gap bytes across 100% of PF_X, and byte-for-byte
     equality against all HOL4-extracted theorem byte blobs.

Any other case prints end_to_end=false with a reason and exits 1.
"""
from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import elf64_check

REQUIRED = (
    "holmake_dir",
    "binary",
    "hash_file",
    "audit_theory",
    "audit_theorem",
    "compile_theory",
    "shim_theory",
)
HEX64 = re.compile(r"\A[0-9a-f]{64}\Z")
CHEAT_RE = re.compile(r"\bcheat\b")
FORBIDDEN_RE = re.compile(r"\b(mk_thm|new_axiom|disk_thm|add_tag|mk_oracle_thm)\b")


def fail(reason: str) -> int:
    print(f"end_to_end=false reason={reason}")
    return 1


def read_manifest(path: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    for n, line in enumerate(path.read_text().splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "=" not in line:
            raise ValueError(f"line {n}: no '='")
        k, v = line.split("=", 1)
        k, v = k.strip(), v.strip()
        if k in out:
            raise ValueError(f"line {n}: duplicate key {k}")
        out[k] = v
    missing = [k for k in REQUIRED if not out.get(k)]
    if missing:
        raise ValueError("missing keys: " + ",".join(missing))
    return out


def inside(root: Path, rel: str) -> Path:
    p = (root / rel).resolve()
    if root not in p.parents and p != root:
        raise ValueError(f"path leaves the repository: {rel}")
    return p


def scan_forbidden_sml(root: Path, hol_dir: Path) -> str | None:
    dirs = [hol_dir]
    for sub in ("kernel", "spec-compiler"):
        p = root / sub
        if p.is_dir() and p not in dirs:
            dirs.append(p)
    seen: set[Path] = set()
    for base in dirs:
        for script in sorted(base.rglob("*.sml")):
            if ".hol" in script.parts or script in seen:
                continue
            seen.add(script)
            txt = script.read_text(errors="replace")
            if CHEAT_RE.search(txt):
                return f"CHEAT_FOUND ({script.relative_to(root)})"
            m = FORBIDDEN_RE.search(txt)
            if m:
                return f"FORBIDDEN_PRIMITIVE ({m.group(1)} in {script.relative_to(root)})"
    return None


def find_hol_heap(hol_dir: Path) -> str | None:
    if os.environ.get("FORGE_HOL_HEAP"):
        return os.environ["FORGE_HOL_HEAP"]
    hm = hol_dir / "Holmakefile"
    if not hm.is_file():
        return None
    cakeml = os.environ.get("CAKEMLDIR")
    heap_tpl = None
    for line in hm.read_text(errors="replace").splitlines():
        s = line.strip()
        if s.startswith("CAKEMLDIR") and "=" in s and not cakeml:
            cakeml = s.split("=", 1)[1].strip()
        elif s.startswith("HOLHEAP") and "=" in s:
            heap_tpl = s.split("=", 1)[1].strip()
    if heap_tpl and cakeml:
        cand = Path(heap_tpl.replace("$(CAKEMLDIR)", cakeml))
        if cand.is_file():
            return str(cand)
    return None


def main(argv: list[str]) -> int:
    root = (Path(argv[1]) if len(argv) > 1 else Path(__file__).parent.parent).resolve()
    manifest = root / "kernel" / "GATE.manifest"
    if not manifest.is_file():
        return fail("NO_KERNEL_THEOREM (kernel/GATE.manifest absent; Milestone 1 not done)")
    try:
        m = read_manifest(manifest)
        hol_dir = inside(root, m["holmake_dir"])
        binary = inside(root, m["binary"])
        hash_file = inside(root, m["hash_file"])
    except ValueError as e:
        return fail(f"BAD_MANIFEST ({e})")
    if not hol_dir.is_dir():
        return fail("HOLMAKE_DIR_MISSING")

    bad_sml = scan_forbidden_sml(root, hol_dir)
    if bad_sml:
        return fail(bad_sml)

    holmake = shutil.which("Holmake")
    if holmake is None:
        return fail("HOL4_NOT_INSTALLED (Holmake not on PATH)")
    r = subprocess.run([holmake, "--no_prereqs"], cwd=hol_dir)
    if r.returncode != 0:
        return fail(f"HOLMAKE_FAILED (exit {r.returncode})")

    hol_bin = shutil.which("hol")
    if hol_bin is None:
        return fail("HOL4_NOT_INSTALLED (hol not on PATH)")

    audit_script = Path(__file__).resolve().parent / "hol_audit.sml"
    if not audit_script.is_file():
        return fail("AUDIT_SCRIPT_MISSING (scripts/hol_audit.sml)")

    with tempfile.TemporaryDirectory(prefix="forge-iron-audit-") as tmp:
        out_dir = Path(tmp)
        env = dict(os.environ)
        env.update(
            {
                "FORGE_AUDIT_THEORY": m["audit_theory"],
                "FORGE_AUDIT_THEOREM": m["audit_theorem"],
                "FORGE_AUDIT_COMPILE_THY": m["compile_theory"],
                "FORGE_AUDIT_SHIM_THY": m["shim_theory"],
                "FORGE_AUDIT_OUT_DIR": str(out_dir),
            }
        )
        hol_cmd = [hol_bin, "--zero"]
        heap = find_hol_heap(hol_dir)
        if heap:
            hol_cmd.append(f"--holstate={heap}")
        ar = subprocess.run(
            hol_cmd,
            cwd=hol_dir,
            env=env,
            stdin=audit_script.open("rb"),
            capture_output=True,
            text=True,
        )
        if ar.returncode != 0 or "AUDIT_OK" not in ar.stdout:
            detail = (ar.stderr or ar.stdout).strip().splitlines()
            msg = detail[-1] if detail else f"exit {ar.returncode}"
            return fail(f"HOL_AUDIT_FAILED ({msg})")

        needed_bins = [
            "theorem_veneers.bin",
            "theorem_code.bin",
            "theorem_shim.bin",
            "theorem_data.bin",
        ]
        for bn in needed_bins:
            p = out_dir / bn
            if not p.is_file() or p.stat().st_size == 0:
                return fail(f"HOL_AUDIT_MISSING_BYTES ({bn})")

        t_veneers = (out_dir / "theorem_veneers.bin").read_bytes()
        t_code = (out_dir / "theorem_code.bin").read_bytes()
        t_shim = (out_dir / "theorem_shim.bin").read_bytes()
        t_data = (out_dir / "theorem_data.bin").read_bytes()

    if not hash_file.is_file():
        return fail("HASH_FILE_MISSING (the proof build did not write it)")
    want = hash_file.read_text().strip()
    if not HEX64.match(want):
        return fail("HASH_FILE_MALFORMED")
    if not binary.is_file():
        return fail("BINARY_MISSING")
    got = hashlib.sha256(binary.read_bytes()).hexdigest()
    if got != want:
        return fail(f"HASH_MISMATCH (binary {got} != theorem {want})")

    try:
        info = elf64_check.verify_kernel_elf(binary, t_veneers, t_code, t_shim, t_data)
    except elf64_check.ElfError as e:
        return fail(f"ELF_CHECK_FAILED ({e})")

    print(
        f"end_to_end=true sha256={got} "
        f"exec_bytes={info['exec_bytes_total']} "
        f"code_bytes={info['code_bytes']} "
        f"shim_bytes={info['shim_bytes']} "
        f"gap_bytes={info['unverified_exec_gap_bytes']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
