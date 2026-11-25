#!/usr/bin/env python3
"""Negative controls for the Iron Law gate (24 cases: 12 original + 12 M1 controls).

Each case builds a scratch repository with a synthetic valid static AArch64 ELF64
and fake Holmake/hol tools to test the gate logic deterministically. These cases
test the gate logic only; real proof replay happens when scripts/iron_law.py runs
against the real HOL4 toolchain and kernel/.
"""
from __future__ import annotations

import hashlib
import os
import stat
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

GATE = Path(__file__).resolve().parent.parent / "iron_law.py"

ARM64_NOP = b"\x1f\x20\x03\xd5"
ARM64_RET = b"\xc0\x03\x5f\xd6"
ARM64_BRK = b"\x00\x00\x20\xd4"

SYN_VENEERS = ARM64_NOP * 4
SYN_CODE = ARM64_NOP * 8
SYN_PAD = b"\x00" * 16
SYN_SHIM = ARM64_RET * 4
SYN_DATA = struct.pack("<QQ", 0x1122334455667788, 0xAABBCCDDEEFF0011)

MANIFEST = (
    "holmake_dir=kernel/proof\n"
    "binary=kernel/build/forge-kernel\n"
    "hash_file=kernel/build/machine_bytes_hash.txt\n"
    "audit_theory=forge_m1Kernel\n"
    "audit_theorem=forge_m1_kernel_correct\n"
    "compile_theory=forge_counterCompile\n"
    "shim_theory=forge_shimProof\n"
)


def make_synthetic_elf(
    *,
    veneers: bytes = SYN_VENEERS,
    code: bytes = SYN_CODE,
    pad: bytes = SYN_PAD,
    shim: bytes = SYN_SHIM,
    data_words: bytes = SYN_DATA,
    add_pt_dynamic: bool = False,
    wx_segment: bool = False,
    high_vaddr: bool = False,
    high_entry: bool = False,
) -> bytes:
    x_vaddr = (1 << 55) if high_entry else 0x00400000
    d_vaddr = (1 << 55) if high_vaddr else (x_vaddr + 0x10000)
    exec_blob = veneers + code + pad + shim
    data_blob = data_words

    phnum = 3 if add_pt_dynamic else 2
    ehdr_size = 64
    phentsize = 56
    phoff = ehdr_size

    x_off = 0x1000
    d_off = 0x2000

    # Symbols
    t_begin = x_vaddr
    c_main = x_vaddr + len(veneers)
    cb_begin = c_main + len(code)
    cb_end = cb_begin + len(pad)
    s_start = cb_end
    s_end = s_start + len(shim)
    heap = d_vaddr + 0x10000
    stk = heap + 0x10000
    stk_end = stk + 0x10000

    sym_list = [
        ("", 0),
        ("cake_text_begin", t_begin),
        ("cml_main", t_begin),
        ("cake_main", c_main),
        ("cake_codebuffer_begin", cb_begin),
        ("cake_codebuffer_end", cb_end),
        ("_start", s_start),
        ("ffirecv16", s_start + 4),
        ("ffisend16", s_start + 8),
        ("cml_exit", s_start + 12),
        ("cml_install", s_start + 12),
        ("forge_shim_end", s_end),
        ("cake_bitmaps", d_vaddr),
        ("forge_heap", heap),
        ("forge_stack", stk),
        ("forge_stackend", stk_end),
    ]

    strtab = bytearray(b"\x00")
    symtab = bytearray()
    for name, val in sym_list:
        if name:
            name_off = len(strtab)
            strtab.extend(name.encode("ascii") + b"\x00")
        else:
            name_off = 0
        symtab.extend(struct.pack("<IBBHQQ", name_off, 0, 0, 1, val, 0))

    strtab_off = 0x3000
    symtab_off = 0x3400
    shoff = 0x3800

    # Build 3 section headers: NULL, .strtab (idx 1), .symtab (idx 2)
    shdrs = bytearray()
    shdrs.extend(struct.pack("<IIQQQQIIQQ", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
    shdrs.extend(struct.pack("<IIQQQQIIQQ", 0, 3, 0, 0, strtab_off, len(strtab), 0, 0, 1, 0))
    shdrs.extend(struct.pack("<IIQQQQIIQQ", 0, 2, 0, 0, symtab_off, len(symtab), 1, 0, 8, 24))

    ehdr = struct.pack(
        "<4sBBBBB7sHHIQQQIHHHHHH",
        b"\x7fELF",
        2,  # ELFCLASS64
        1,  # ELFDATA2LSB
        1,  # EV_CURRENT
        0,
        0,
        b"\x00" * 7,
        2,  # ET_EXEC
        183,  # EM_AARCH64
        1,
        s_start,  # e_entry
        phoff,
        shoff,
        0,
        ehdr_size,
        phentsize,
        phnum,
        64,  # e_shentsize
        3,  # e_shnum
        0,
    )

    x_flags = (4 | 2 | 1) if wx_segment else (4 | 1)
    phdrs = bytearray()
    phdrs.extend(
        struct.pack(
            "<IIQQQQQQ", 1, x_flags, x_off, x_vaddr, x_vaddr, len(exec_blob), len(exec_blob), 0x10000
        )
    )
    phdrs.extend(
        struct.pack(
            "<IIQQQQQQ", 1, 4 | 2, d_off, d_vaddr, d_vaddr, len(data_blob), 0x30000, 0x10000
        )
    )
    if add_pt_dynamic:
        phdrs.extend(struct.pack("<IIQQQQQQ", 2, 4 | 2, d_off, d_vaddr, d_vaddr, 0, 0, 8))

    out = bytearray(shoff + len(shdrs))
    out[0 : len(ehdr)] = ehdr
    out[phoff : phoff + len(phdrs)] = phdrs
    out[x_off : x_off + len(exec_blob)] = exec_blob
    out[d_off : d_off + len(data_blob)] = data_blob
    out[strtab_off : strtab_off + len(strtab)] = strtab
    out[symtab_off : symtab_off + len(symtab)] = symtab
    out[shoff : shoff + len(shdrs)] = shdrs
    return bytes(out)


GOOD_BIN = make_synthetic_elf()
GOOD_HASH = hashlib.sha256(GOOD_BIN).hexdigest()


def flip_bit(buf: bytes, offset: int) -> bytes:
    b = bytearray(buf)
    b[offset] ^= 0x01
    return bytes(b)


def make_repo(
    d: Path,
    *,
    manifest: str | None = MANIFEST,
    holmake_exit: int = 0,
    hol_audit_exit: int = 0,
    hol_audit_stdout: str = "AUDIT_OK\n",
    hash_text: str | None = None,
    binary: bytes | None = GOOD_BIN,
    script_text: str = "Theorem t: T\nProof simp[]\nQED\n",
    spec_compiler_sml: str | None = None,
    write_hash: bool = True,
    with_hol: bool = True,
) -> Path:
    (d / "kernel/proof").mkdir(parents=True)
    (d / "kernel/build").mkdir(parents=True)
    (d / "spec-compiler").mkdir(parents=True)
    if manifest is not None:
        (d / "kernel/GATE.manifest").write_text(manifest)
    (d / "kernel/proof/counterScript.sml").write_text(script_text)
    if spec_compiler_sml is not None:
        (d / "spec-compiler/badHelper.sml").write_text(spec_compiler_sml)
    if binary is not None:
        (d / "kernel/build/forge-kernel").write_bytes(binary)
        h_val = hash_text if hash_text is not None else hashlib.sha256(binary).hexdigest()
    else:
        h_val = hash_text if hash_text is not None else GOOD_HASH

    tools = d / "_tools"
    tools.mkdir()
    hm = tools / "Holmake"
    body = "#!/bin/sh\n"
    if write_hash:
        body += f"printf '%s\\n' '{h_val}' > ../build/machine_bytes_hash.txt\n"
    body += f"exit {holmake_exit}\n"
    hm.write_text(body)
    hm.chmod(hm.stat().st_mode | stat.S_IEXEC)

    if with_hol:
        hol = tools / "hol"
        hol_body = f"""#!{sys.executable}
import os, sys
from pathlib import Path
out = Path(os.environ["FORGE_AUDIT_OUT_DIR"])
(out / "theorem_veneers.bin").write_bytes({SYN_VENEERS!r})
(out / "theorem_code.bin").write_bytes({SYN_CODE!r})
(out / "theorem_shim.bin").write_bytes({SYN_SHIM!r})
(out / "theorem_data.bin").write_bytes({SYN_DATA!r})
sys.stdout.write({hol_audit_stdout!r})
sys.exit({hol_audit_exit})
"""
        hol.write_text(hol_body)
        hol.chmod(hol.stat().st_mode | stat.S_IEXEC)

    return tools


def run(d: Path, tools: Path, with_holmake: bool = True) -> tuple[int, str]:
    env = dict(os.environ)
    path = "/usr/bin:/bin"
    if with_holmake:
        path = f"{tools}:{path}"
    env["PATH"] = path
    r = subprocess.run(
        [sys.executable, str(GATE), str(d)],
        env=env,
        capture_output=True,
        text=True,
    )
    return r.returncode, r.stdout.strip()


CASES = [
    # Original 12 cases (never weakened)
    ("accept: proofs replay, audit passes, and zero-gap ELF matches", {}, True, 0, "end_to_end=true"),
    ("reject: no manifest", {"manifest": None}, True, 1, "NO_KERNEL_THEOREM"),
    ("reject: manifest missing a key", {"manifest": "holmake_dir=kernel/proof\n"}, True, 1, "BAD_MANIFEST"),
    ("reject: manifest path escapes repo", {"manifest": MANIFEST.replace("kernel/build/forge-kernel", "../x")}, True, 1, "BAD_MANIFEST"),
    ("reject: HOL4 not installed", {}, False, 1, "HOL4_NOT_INSTALLED"),
    ("reject: Holmake fails", {"holmake_exit": 2}, True, 1, "HOLMAKE_FAILED"),
    ("reject: cheat in a proof script", {"script_text": "Theorem t: F\nProof cheat\nQED\n"}, True, 1, "CHEAT_FOUND"),
    ("reject: binary one byte changed (hash mismatch)", {"binary": GOOD_BIN[:-1] + b"X", "hash_text": GOOD_HASH}, True, 1, "HASH_MISMATCH"),
    ("reject: binary missing", {"binary": None}, True, 1, "BINARY_MISSING"),
    ("reject: hash file malformed", {"hash_text": "abc"}, True, 1, "HASH_FILE_MALFORMED"),
    ("reject: hash upper case", {"hash_text": GOOD_HASH.upper()}, True, 1, "HASH_FILE_MALFORMED"),
    ("reject: proof build writes no hash", {"write_hash": False}, True, 1, "HASH_FILE_MISSING"),
    # 12 new M1 security controls (planted failures)
    ("reject: mk_thm in a proof script", {"script_text": "val bad = mk_thm ([], ``F``);\n"}, True, 1, "FORBIDDEN_PRIMITIVE"),
    ("reject: new_axiom in a proof script", {"script_text": "val bad = new_axiom (\"x\", ``F``);\n"}, True, 1, "FORBIDDEN_PRIMITIVE"),
    ("reject: forbidden primitive in spec-compiler/", {"spec_compiler_sml": "val x = new_axiom (\"y\", ``F``);\n"}, True, 1, "FORBIDDEN_PRIMITIVE"),
    ("reject: HOL auditor detects extra axiom/oracle", {"hol_audit_exit": 1, "hol_audit_stdout": "HOL_AUDIT_FAIL: unexpected axioms\n"}, True, 1, "HOL_AUDIT_FAILED"),
    ("reject: 1-bit flip in cake_main code bytes", {"binary": make_synthetic_elf(code=flip_bit(SYN_CODE, 3))}, True, 1, "CODE_BYTE_MISMATCH"),
    ("reject: 1-bit flip in shim bytes", {"binary": make_synthetic_elf(shim=flip_bit(SYN_SHIM, 2))}, True, 1, "SHIM_BYTE_MISMATCH"),
    ("reject: 1-bit flip in veneers bytes", {"binary": make_synthetic_elf(veneers=flip_bit(SYN_VENEERS, 1))}, True, 1, "VENEERS_BYTE_MISMATCH"),
    ("reject: 1-bit flip in cake_bitmaps data bytes", {"binary": make_synthetic_elf(data_words=flip_bit(SYN_DATA, 0))}, True, 1, "BITMAPS_BYTE_MISMATCH"),
    ("reject: unverified instruction in codebuffer gap", {"binary": make_synthetic_elf(pad=ARM64_BRK + b"\x00" * 12)}, True, 1, "ELF_UNVERIFIED_CODEBUFFER_INSTRUCTION"),
    ("reject: PT_DYNAMIC segment in ELF", {"binary": make_synthetic_elf(add_pt_dynamic=True)}, True, 1, "ELF_FORBIDDEN_PT_DYNAMIC"),
    ("reject: PF_W|PF_X segment (W^X violation)", {"binary": make_synthetic_elf(wx_segment=True)}, True, 1, "ELF_WX_VIOLATION"),
    ("reject: segment vaddr >= 2^55 (P-LO55 violation)", {"binary": make_synthetic_elf(high_vaddr=True)}, True, 1, "ELF_VADDR_ABOVE_LO55"),
    ("reject: entry vaddr >= 2^55 (P-LO55 violation)", {"binary": make_synthetic_elf(high_entry=True)}, True, 1, "ELF_ENTRY_ABOVE_LO55"),
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
