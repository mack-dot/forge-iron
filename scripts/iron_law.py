#!/usr/bin/env python3
"""The Iron Law gate (Exact Term.aconv + Pinned Spec SHA-256 Edition).

end_to_end=true only if ALL of these hold:
  1. kernel/GATE.manifest exists and names holmake_dir, binary, hash_file,
     spec_hashes, audit_theory, audit_theorem, nonvacuous_theorem, spec_theory,
     contract_theory, compile_theory, and shim_theory (fixed key=value lines).
  2. Every pinned specification file listed in spec_hashes exists inside the
     repository and matches its pinned lowercase 64-hex SHA-256 digest BEFORE
     AND AFTER Holmake (preventing any prover edit to counter_run, chunks16,
     forge_elf_loaded, arm8_target_real, real_mc, svc_read_rel, svc_write_rel,
     svc_exit_group_rel, whole_step, shim_step, or ELF layout constants).
  3. No `cheat`, `mk_thm`, `new_axiom`, `mk_axiom_thm`, `disk_thm`, `add_tag`,
     or `mk_oracle_thm` appears in any *.sml, *.sig, or *.ML under kernel/ or
     spec-compiler/, and Holmakefile contains no hardcoded developer paths.
  4. `Holmake --qof -j 1 --no_prereqs` replays all proofs in holmake_dir with
     exit 0.
  5. Gate-owned HOL4 kernel audit (`scripts/hol_audit.sml`) passes with exit 0:
     - parses the EXACT expected conclusions for audit_theorem and
       nonvacuous_theorem BEFORE loading audit_theory (immune to grammar/overload
       hijacking) and enforces exact kernel `Term.aconv`;
     - 0 hypotheses, 0 direct axioms, DISK_THM-only oracle tags on all forge_*
       theories, including audit_theorem and nonvacuous_theorem;
     - spec_theory, contract_theory, compile_theory, and shim_theory in
       transitive closure;
     - transitive DB.axioms closure equals ONLY the 4 standard bool axioms;
     - extracts raw verified bytes AND all 24 exact HOL4 layout constants
       (theorem_layout.txt) directly from proved HOL4 definitions.
  6. hash_file holds exactly 64 lowercase hex characters and matches
     SHA256(binary).
  7. Pure-Python ELF64 AArch64 check confirms static non-PIE ET_EXEC,
     zero PT_INTERP / PT_DYNAMIC, strict W^X, disjoint PT_LOAD segments,
     all vaddrs < 2^55 (P-LO55), exact e_entry and RX/RW PT_LOAD vaddr/memsz
     binding against theorem_layout.txt, zero unverified gap bytes across 100%
     of PF_X, and byte-for-byte equality against all HOL4-extracted blobs.
  8. Automated kernel-verified theorem catalog (`scripts/export_theorem_catalog.sml`)
     re-exports all compiled `forge_*` theories into a temporary file and
     matches `docs/THEOREM_CATALOG.md` byte-for-byte (preventing stale or
     hand-edited theorem claims).

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


def verify_pinned_specs(root: Path, spec_hashes_path: Path) -> str | None:
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
    for want, target, rel in entries:
        if not target.is_file():
            return f"SPEC_FILE_MISSING ({rel})"
        got = hashlib.sha256(target.read_bytes()).hexdigest()
        if got != want:
            return f"SPEC_HASH_MISMATCH ({rel}: got {got} != pinned {want})"
    return None


def scan_forbidden_sources(root: Path, hol_dir: Path) -> str | None:
    dirs = [hol_dir]
    for sub in ("kernel", "spec-compiler"):
        p = root / sub
        if p.is_dir() and p not in dirs:
            dirs.append(p)
    seen: set[Path] = set()
    for base in dirs:
        for f in sorted(base.rglob("*")):
            if not f.is_file() or ".hol" in f.parts or f in seen:
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
        spec_hashes_file = inside(root, m["spec_hashes"])
        catalog_file = inside(root, m["theorem_catalog"])
    except ValueError as e:
        return fail(f"BAD_MANIFEST ({e})")
    if not hol_dir.is_dir():
        return fail("HOLMAKE_DIR_MISSING")

    bad_spec = verify_pinned_specs(root, spec_hashes_file)
    if bad_spec:
        return fail(bad_spec)

    bad_src = scan_forbidden_sources(root, hol_dir)
    if bad_src:
        return fail(bad_src)

    holmake = shutil.which("Holmake")
    if holmake is None:
        return fail("HOL4_NOT_INSTALLED (Holmake not on PATH)")
    r = subprocess.run([holmake, "--qof", "-j", "1", "--no_prereqs"], cwd=hol_dir)
    if r.returncode != 0:
        return fail(f"HOLMAKE_FAILED (exit {r.returncode})")

    # Re-verify pinned spec files after Holmake in case build modified sources
    bad_spec_after = verify_pinned_specs(root, spec_hashes_file)
    if bad_spec_after:
        return fail(bad_spec_after)

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

        # Verify docs/THEOREM_CATALOG.md is byte-for-byte up-to-date with compiled theories
        catalog_script = Path(__file__).resolve().parent / "export_theorem_catalog.sml"
        if not catalog_script.is_file():
            return fail("CATALOG_SCRIPT_MISSING (scripts/export_theorem_catalog.sml)")
        if not catalog_file.is_file():
            return fail(f"THEOREM_CATALOG_MISSING ({m['theorem_catalog']})")
        gen_catalog = out_dir / "THEOREM_CATALOG.md"
        cat_env = dict(os.environ)
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
