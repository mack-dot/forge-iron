#!/usr/bin/env python3
"""The Iron Law gate.

end_to_end=true only if ALL of these hold:
  1. kernel/GATE.manifest exists and names a Holmake directory, a binary and a
     hash file (fixed key=value lines; no JSON or YAML).
  2. No `cheat` appears in any *Script.sml under the Holmake directory.
  3. `Holmake` replays the proofs in that directory with exit 0.
  4. The hash file (written by the proof build from the theorem) holds exactly
     64 lowercase hex characters.
  5. SHA256(binary) equals that hash.

Any other case prints end_to_end=false with a reason and exits 1.

Known limits (see STATUS.md): check 2 is textual only; HOL oracle tags are not
read yet. The gate does not yet prove that the hash file came from the
theorem statement; Milestone 1 must close this.
"""
import hashlib
import re
import shutil
import subprocess
import sys
from pathlib import Path

REQUIRED = ("holmake_dir", "binary", "hash_file")
HEX64 = re.compile(r"\A[0-9a-f]{64}\Z")


def fail(reason: str) -> int:
    print(f"end_to_end=false reason={reason}")
    return 1


def read_manifest(path: Path) -> dict:
    out = {}
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


def main(argv: list) -> int:
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

    for script in sorted(hol_dir.rglob("*Script.sml")):
        if re.search(r"\bcheat\b", script.read_text(errors="replace")):
            return fail(f"CHEAT_FOUND ({script.relative_to(root)})")

    holmake = shutil.which("Holmake")
    if holmake is None:
        return fail("HOL4_NOT_INSTALLED (Holmake not on PATH)")
    r = subprocess.run([holmake], cwd=hol_dir)
    if r.returncode != 0:
        return fail(f"HOLMAKE_FAILED (exit {r.returncode})")

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

    print(f"end_to_end=true sha256={got}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
