#!/usr/bin/env python3
"""The Iron Law gate (Frozen Runtime + Exact Term.aconv + Pinned Spec SHA-256 Edition).

Canonical gate implementation living in `runtime/iron_law.py` (delegated from
`scripts/iron_law.py`). Supports both refactored `runtime/` + `kernels/<app>/GATE.manifest`
and legacy `kernel/GATE.manifest` layouts.
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

RUNTIME_DIR = Path(__file__).resolve().parent
if str(RUNTIME_DIR) not in sys.path:
    sys.path.insert(0, str(RUNTIME_DIR))
import elf64_check  # noqa: E402

REQUIRED = (
    "holmake_dir",
    "binary",
    "hash_file",
    "spec_hashes",
    "theorem_catalog",
    "audit_theory",
    "audit_theorem",
    "nonvacuous_theorem",
    "spec_theory",
    "contract_theory",
    "compile_theory",
    "shim_theory",
)
HEX64 = re.compile(r"\A[0-9a-f]{64}\Z")
CHEAT_RE = re.compile(r"\bcheat\b")
FORBIDDEN_RE = re.compile(r"\b(mk_thm|new_axiom|mk_axiom_thm|disk_thm|add_tag|mk_oracle_thm)\b")
HARDCODED_DEV_PATH_RE = re.compile(r"(/Users/|/home/|C:\\Users\\)")
SOURCE_SUFFIXES = (".sml", ".sig", ".ML")


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


def verify_pinned_specs(
    root: Path,
    spec_hashes_path: Path,
    m: dict[str, str],
    hol_dir: Path,
    rt_hol_dir: Path | None,
) -> str | None:
    if not spec_hashes_path.is_file():
        return f"SPEC_HASH_FILE_MISSING ({spec_hashes_path.name})"
    entries: list[tuple[str, Path, str]] = []
    seen: set[Path] = set()
    for n, raw in enumerate(spec_hashes_path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(None, 1)
        if len(parts) != 2:
            return f"SPEC_HASH_FILE_MALFORMED (line {n})"
        digest, rel = parts[0].strip(), parts[1].strip()
        if not HEX64.match(digest):
            return f"SPEC_HASH_FILE_MALFORMED (line {n}: invalid sha256)"
        try:
            target = inside(root, rel)
        except ValueError as e:
            return f"SPEC_HASH_FILE_MALFORMED ({e})"
        if target in seen:
            return f"SPEC_HASH_FILE_MALFORMED (duplicate path {rel})"
        seen.add(target)
        entries.append((digest, target, rel))
    if len(entries) < 2:
        return f"SPEC_HASH_FILE_MALFORMED (expected >= 2 pinned spec files, got {len(entries)})"
    contract_base = rt_hol_dir if rt_hol_dir is not None else hol_dir
    required_targets: list[Path] = [
        (hol_dir / f"{m['spec_theory']}Script.sml").resolve(),
        (contract_base / f"{m['contract_theory']}Script.sml").resolve(),
    ]
    if m["spec_theory"] == "forge_guardrailSpec":
        required_targets.append((contract_base / "forge_frame64SpecScript.sml").resolve())
    for req in required_targets:
        if req not in seen:
            rel_req = req.relative_to(root) if root in req.parents else req
            return f"SPEC_HASH_MISSING_REQUIRED ({rel_req})"
    for want, target, rel in entries:
        if not target.is_file():
            return f"SPEC_FILE_MISSING ({rel})"
        got = hashlib.sha256(target.read_bytes()).hexdigest()
        if got != want:
            return f"SPEC_HASH_MISMATCH ({rel}: got {got} != pinned {want})"
    return None


def scan_forbidden_sources(root: Path, hol_dirs: list[Path]) -> str | None:
    dirs = list(hol_dirs)
    for sub in ("runtime", "kernels", "kernel", "spec-compiler"):
        p = root / sub
        if p.is_dir() and p not in dirs:
            dirs.append(p)
    seen: set[Path] = set()
    for base in dirs:
        for f in sorted(base.rglob("*")):
            if not f.is_file() or ".hol" in f.parts or f in seen:
                continue
            # Skip gate SML scripts themselves (which are audited by tests, not prover theories)
            if f.parent == (root / "runtime") and f.name in ("hol_audit.sml", "export_theorem_catalog.sml"):
                continue
            if f.name == "Holmakefile":
                seen.add(f)
                txt = f.read_text(errors="replace")
                if HARDCODED_DEV_PATH_RE.search(txt):
                    return f"HARDCODED_DEV_PATH ({f.relative_to(root)})"
                if CHEAT_RE.search(txt):
                    return f"CHEAT_FOUND ({f.relative_to(root)})"
                m = FORBIDDEN_RE.search(txt)
                if m:
                    return f"FORBIDDEN_PRIMITIVE ({m.group(1)} in {f.relative_to(root)})"
                continue
            if f.suffix not in SOURCE_SUFFIXES:
                continue
            seen.add(f)
            txt = f.read_text(errors="replace")
            if CHEAT_RE.search(txt):
                return f"CHEAT_FOUND ({f.relative_to(root)})"
            m = FORBIDDEN_RE.search(txt)
            if m:
                return f"FORBIDDEN_PRIMITIVE ({m.group(1)} in {f.relative_to(root)})"
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


def resolve_manifest(root: Path, manifest_arg: str | None) -> Path | None:
    if manifest_arg:
        p = Path(manifest_arg)
        return p if p.is_absolute() else (root / p)
    for rel in ("kernels/counter/GATE.manifest", "kernel/GATE.manifest"):
        cand = root / rel
        if cand.is_file():
            return cand
    return None


def main(argv: list[str]) -> int:
    manifest_arg: str | None = None
    positional: list[str] = []
    i = 1
    while i < len(argv):
        if argv[i] == "--manifest" and i + 1 < len(argv):
            manifest_arg = argv[i + 1]
            i += 2
        else:
            positional.append(argv[i])
            i += 1

    root = (Path(positional[0]) if positional else RUNTIME_DIR.parent).resolve()
    manifest = resolve_manifest(root, manifest_arg)
    if manifest is None or not manifest.is_file():
        return fail("NO_KERNEL_THEOREM (kernel/GATE.manifest absent; Milestone 1 not done)")
    try:
        m = read_manifest(manifest)
        hol_dir = inside(root, m["holmake_dir"])
        rt_hol_dir = inside(root, m["runtime_holmake_dir"]) if m.get("runtime_holmake_dir") else None
        binary = inside(root, m["binary"])
        hash_file = inside(root, m["hash_file"])
        spec_hashes_file = inside(root, m["spec_hashes"])
        catalog_file = inside(root, m["theorem_catalog"])
    except ValueError as e:
        return fail(f"BAD_MANIFEST ({e})")
    if not hol_dir.is_dir():
        return fail("HOLMAKE_DIR_MISSING")
    if rt_hol_dir is not None and not rt_hol_dir.is_dir():
        return fail("RUNTIME_HOLMAKE_DIR_MISSING")

    bad_spec = verify_pinned_specs(root, spec_hashes_file, m, hol_dir, rt_hol_dir)
    if bad_spec:
        return fail(bad_spec)

    hol_dirs = ([rt_hol_dir] if rt_hol_dir else []) + [hol_dir]
    bad_src = scan_forbidden_sources(root, hol_dirs)
    if bad_src:
        return fail(bad_src)

    holmake = shutil.which("Holmake")
    if holmake is None:
        return fail("HOL4_NOT_INSTALLED (Holmake not on PATH)")

    if rt_hol_dir is not None:
        rr = subprocess.run([holmake, "--qof", "-j", "1", "--no_prereqs"], cwd=rt_hol_dir)
        if rr.returncode != 0:
            return fail(f"RUNTIME_HOLMAKE_FAILED (exit {rr.returncode})")

    r = subprocess.run([holmake, "--qof", "-j", "1", "--no_prereqs"], cwd=hol_dir)
    if r.returncode != 0:
        return fail(f"HOLMAKE_FAILED (exit {r.returncode})")

    bad_spec_after = verify_pinned_specs(root, spec_hashes_file, m, hol_dir, rt_hol_dir)
    if bad_spec_after:
        return fail(bad_spec_after)

    hol_bin = shutil.which("hol")
    if hol_bin is None:
        return fail("HOL4_NOT_INSTALLED (hol not on PATH)")

    audit_script = RUNTIME_DIR / "hol_audit.sml"
    if not audit_script.is_file():
        audit_script = root / "scripts" / "hol_audit.sml"
    if not audit_script.is_file():
        return fail("AUDIT_SCRIPT_MISSING (runtime/hol_audit.sml)")

    with tempfile.TemporaryDirectory(prefix="forge-iron-audit-") as tmp:
        out_dir = Path(tmp)
        env = dict(os.environ)
        env.update(
            {
                "FORGE_AUDIT_THEORY": m["audit_theory"],
                "FORGE_AUDIT_THEOREM": m["audit_theorem"],
                "FORGE_AUDIT_NONVAC_THEOREM": m["nonvacuous_theorem"],
                "FORGE_AUDIT_SPEC_THY": m["spec_theory"],
                "FORGE_AUDIT_CONTRACT_THY": m["contract_theory"],
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

        layout_file = out_dir / "theorem_layout.txt"
        if not layout_file.is_file() or layout_file.stat().st_size == 0:
            return fail("HOL_AUDIT_MISSING_LAYOUT (theorem_layout.txt)")

        t_veneers = (out_dir / "theorem_veneers.bin").read_bytes()
        t_code = (out_dir / "theorem_code.bin").read_bytes()
        t_shim = (out_dir / "theorem_shim.bin").read_bytes()
        t_data = (out_dir / "theorem_data.bin").read_bytes()
        layout_text = layout_file.read_text()

        catalog_script = RUNTIME_DIR / "export_theorem_catalog.sml"
        if not catalog_script.is_file():
            catalog_script = root / "scripts" / "export_theorem_catalog.sml"
        if not catalog_script.is_file():
            return fail("CATALOG_SCRIPT_MISSING (runtime/export_theorem_catalog.sml)")
        if not catalog_file.is_file():
            return fail(f"THEOREM_CATALOG_MISSING ({m['theorem_catalog']})")
        gen_catalog = out_dir / "THEOREM_CATALOG.md"
        cat_env = dict(os.environ)
        cat_env.pop("FORGE_CATALOG_CHECKPOINT", None)
        cat_env.update(
            {
                "FORGE_AUDIT_THEORY": m["audit_theory"],
                "FORGE_CATALOG_OUT": str(gen_catalog),
            }
        )
        cr = subprocess.run(
            hol_cmd,
            cwd=hol_dir,
            env=cat_env,
            stdin=catalog_script.open("rb"),
            capture_output=True,
            text=True,
        )
        if cr.returncode != 0 or "CATALOG_EXPORT_OK" not in cr.stdout or not gen_catalog.is_file():
            detail = (cr.stderr or cr.stdout).strip().splitlines()
            msg = detail[-1] if detail else f"exit {cr.returncode}"
            return fail(f"CATALOG_EXPORT_FAILED ({msg})")
        want_cat_bytes = gen_catalog.read_bytes()
        got_cat_bytes = catalog_file.read_bytes()
        if got_cat_bytes != want_cat_bytes:
            got_h = hashlib.sha256(got_cat_bytes).hexdigest()[:16]
            want_h = hashlib.sha256(want_cat_bytes).hexdigest()[:16]
            return fail(
                f"THEOREM_CATALOG_MISMATCH ({m['theorem_catalog']} sha256:{got_h} != generated:{want_h})"
            )

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
        layout = elf64_check.parse_layout(layout_text)
        info = elf64_check.verify_kernel_elf(binary, t_veneers, t_code, t_shim, t_data, layout)
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
