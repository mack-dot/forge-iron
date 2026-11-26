#!/usr/bin/env python3
"""Negative controls for the Iron Law gate (41 cases: 12 original + 29 M1/Pass-1/Catalog controls).

Each case builds a scratch repository with a synthetic valid static AArch64 ELF64,
pinned spec SHA-256 files, verified theorem catalog, and fake Holmake/hol tools
to test the gate logic deterministically without requiring HOL4. Real HOL4 kernel
auditor exact Term.aconv negative controls run in `scripts/tests/test_hol_audit_real.py`.
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
    "spec_hashes=kernel/SPEC_HASHES.sha256\n"
    "theorem_catalog=docs/THEOREM_CATALOG.md\n"
    "audit_theory=forge_m1Kernel\n"
    "audit_theorem=forge_m1_kernel_correct\n"
    "nonvacuous_theorem=forge_m1_nonvacuous\n"
    "spec_theory=forge_counterSpec\n"
    "contract_theory=forge_contractSpec\n"
    "compile_theory=forge_counterCompile\n"
    "shim_theory=forge_shimProof\n"
)

SPEC_COUNTER_TEXT = "Theory forge_counterSpec\nDefinition counter_run_def: counter_run x = x End\n"
SPEC_CONTRACT_TEXT = "Theory forge_contractSpec\nDefinition forge_elf_loaded_def: forge_elf_loaded x = T End\n"
GOOD_CATALOG_TEXT = "# Verified Theorem Catalog\n\nSynthetic catalog for gate self-test.\n"


def default_layout(
    *,
    x_vaddr: int = 0x00400000,
    d_vaddr: int = 0x00410000,
    veneers_len: int = len(SYN_VENEERS),
    code_len: int = len(SYN_CODE),
    pad_len: int = len(SYN_PAD),
    shim_len: int = len(SYN_SHIM),
    data_len: int = len(SYN_DATA),
) -> dict[str, int]:
    c_main = x_vaddr + veneers_len
    cb_begin = c_main + code_len
    cb_end = cb_begin + pad_len
    s_start = cb_end
    s_end = s_start + shim_len
    bm_begin = d_vaddr + 0x18
    bm_end = bm_begin + data_len
    rx_tmp = d_vaddr + 0x1000
    heap = d_vaddr + 0x10000
    stk = heap + 0x10000
    stk_end = stk + 0x10000
    return {
        "veneers_base": x_vaddr,
        "ffirecv16_veneer": x_vaddr + 4,
        "ffisend16_veneer": x_vaddr + 8,
        "install_veneer": x_vaddr + 12,
        "exit_veneer": x_vaddr + 12,
        "cake_main": c_main,
        "cb_begin": cb_begin,
        "cb_end": cb_end,
        "cbspace": pad_len,
        "shim_base": s_start,
        "ffirecv16": s_start + 4,
        "ffisend16": s_start + 8,
        "cml_exit": s_start + 12,
        "cml_install": s_start + 12,
        "shim_end": s_end,
        "cml_heap": d_vaddr,
        "cml_stack": d_vaddr + 8,
        "cml_stackend": d_vaddr + 16,
        "cake_bitmaps": bm_begin,
        "bm_buf_end": bm_end,
        "rx_tmp": rx_tmp,
        "forge_heap": heap,
        "forge_stack": stk,
        "forge_stackend": stk_end,
    }


def format_layout(layout: dict[str, int]) -> str:
    return "".join(f"{k}={v}\n" for k, v in layout.items())


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
    x_vaddr_override: int | None = None,
    rw_memsz_override: int | None = None,
) -> bytes:
    x_vaddr = x_vaddr_override if x_vaddr_override is not None else ((1 << 55) if high_entry else 0x00400000)
    d_vaddr = (1 << 55) if high_vaddr else (x_vaddr + 0x10000)
    lay = default_layout(
        x_vaddr=x_vaddr,
        d_vaddr=d_vaddr,
        veneers_len=len(veneers),
        code_len=len(code),
        pad_len=len(pad),
        shim_len=len(shim),
        data_len=len(data_words),
    )

    exec_blob = veneers + code + pad + shim
    data_blob = (b"\x00" * 0x18) + data_words

    phnum = 3 if add_pt_dynamic else 2
    ehdr_size = 64
    phentsize = 56
    phoff = ehdr_size

    x_off = 0x1000
    d_off = 0x2000

    sym_list = [
        ("", 0),
        ("cake_text_begin", lay["veneers_base"]),
        ("cml_main", lay["veneers_base"]),
        ("cake_main", lay["cake_main"]),
        ("cake_codebuffer_begin", lay["cb_begin"]),
        ("cake_codebuffer_end", lay["cb_end"]),
        ("_start", lay["shim_base"]),
        ("ffirecv16", lay["ffirecv16"]),
        ("ffisend16", lay["ffisend16"]),
        ("cml_exit", lay["cml_exit"]),
        ("cml_install", lay["cml_install"]),
        ("forge_shim_end", lay["shim_end"]),
        ("cake_bitmaps", lay["cake_bitmaps"]),
        ("forge_heap", lay["forge_heap"]),
        ("forge_stack", lay["forge_stack"]),
        ("forge_stackend", lay["forge_stackend"]),
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

    shdrs = bytearray()
    shdrs.extend(struct.pack("<IIQQQQIIQQ", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
    shdrs.extend(struct.pack("<IIQQQQIIQQ", 0, 3, 0, 0, strtab_off, len(strtab), 0, 0, 1, 0))
    shdrs.extend(struct.pack("<IIQQQQIIQQ", 0, 2, 0, 0, symtab_off, len(symtab), 1, 0, 8, 24))

    ehdr = struct.pack(
        "<4sBBBBB7sHHIQQQIHHHHHH",
        b"\x7fELF",
        2,
        1,
        1,
        0,
        0,
        b"\x00" * 7,
        2,
        183,
        1,
        lay["shim_base"],
        phoff,
        shoff,
        0,
        ehdr_size,
        phentsize,
        phnum,
        64,
        3,
        0,
    )

    x_flags = (4 | 2 | 1) if wx_segment else (4 | 1)
    rw_memsz = rw_memsz_override if rw_memsz_override is not None else 0x30000
    phdrs = bytearray()
    phdrs.extend(
        struct.pack(
            "<IIQQQQQQ", 1, x_flags, x_off, x_vaddr, x_vaddr, len(exec_blob), len(exec_blob), 0x10000
        )
    )
    phdrs.extend(
        struct.pack(
            "<IIQQQQQQ", 1, 4 | 2, d_off, d_vaddr, d_vaddr, len(data_blob), rw_memsz, 0x10000
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
GOOD_LAYOUT = format_layout(default_layout())


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
    holmakefile_text: str | None = "INCLUDES = $(CAKEMLDIR)/misc\n",
    spec_compiler_sml: str | None = None,
    write_hash: bool = True,
    write_layout: bool = True,
    layout_text: str = GOOD_LAYOUT,
    with_hol: bool = True,
    check_holmake_flags: bool = True,
    write_spec_hashes: bool = True,
    spec_hashes_override: str | None = None,
    spec_counter_text: str = SPEC_COUNTER_TEXT,
    spec_contract_text: str = SPEC_CONTRACT_TEXT,
    write_catalog: bool = True,
    catalog_text: str = GOOD_CATALOG_TEXT,
    catalog_export_exit: int = 0,
    catalog_export_stdout: str = "CATALOG_EXPORT_OK\n",
) -> Path:
    (d / "kernel/proof").mkdir(parents=True)
    (d / "kernel/build").mkdir(parents=True)
    (d / "spec-compiler").mkdir(parents=True)
    (d / "docs").mkdir(parents=True)
    if manifest is not None:
        (d / "kernel/GATE.manifest").write_text(manifest)
    if write_catalog:
        (d / "docs/THEOREM_CATALOG.md").write_text(catalog_text)
    (d / "kernel/proof/counterScript.sml").write_text(script_text)
    (d / "kernel/proof/forge_counterSpecScript.sml").write_text(spec_counter_text)
    (d / "kernel/proof/forge_contractSpecScript.sml").write_text(spec_contract_text)
    if write_spec_hashes:
        if spec_hashes_override is not None:
            (d / "kernel/SPEC_HASHES.sha256").write_text(spec_hashes_override)
        else:
            h1 = hashlib.sha256(SPEC_COUNTER_TEXT.encode()).hexdigest()
            h2 = hashlib.sha256(SPEC_CONTRACT_TEXT.encode()).hexdigest()
            (d / "kernel/SPEC_HASHES.sha256").write_text(
                f"{h1}  kernel/proof/forge_counterSpecScript.sml\n"
                f"{h2}  kernel/proof/forge_contractSpecScript.sml\n"
            )
    if holmakefile_text is not None:
        (d / "kernel/proof/Holmakefile").write_text(holmakefile_text)
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
    if check_holmake_flags:
        body += 'if [ "$*" != "--qof -j 1 --no_prereqs" ]; then echo "BAD_FLAGS:$*" >&2; exit 99; fi\n'
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
if "FORGE_CATALOG_OUT" in os.environ:
    Path(os.environ["FORGE_CATALOG_OUT"]).write_text({GOOD_CATALOG_TEXT!r})
    sys.stdout.write({catalog_export_stdout!r})
    sys.exit({catalog_export_exit})
out = Path(os.environ["FORGE_AUDIT_OUT_DIR"])
(out / "theorem_veneers.bin").write_bytes({SYN_VENEERS!r})
(out / "theorem_code.bin").write_bytes({SYN_CODE!r})
(out / "theorem_shim.bin").write_bytes({SYN_SHIM!r})
(out / "theorem_data.bin").write_bytes({SYN_DATA!r})
if {write_layout!r}:
    (out / "theorem_layout.txt").write_text({layout_text!r})
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
    # M1 byte-equivalence & primitive controls (13 cases)
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
    # Pass 1 hardened controls (8 new planted failures from hostile audit)
    ("reject: shifted link base (0x800000 vs HOL4 0x400000)", {"binary": make_synthetic_elf(x_vaddr_override=0x00800000)}, True, 1, "ELF_ENTRY_MISMATCH"),
    ("reject: unmapped .bss heap/stackend in RW PT_LOAD", {"binary": make_synthetic_elf(rw_memsz_override=0x2000)}, True, 1, "ELF_RW_HEAP_UNMAPPED"),
    ("reject: missing theorem_layout.txt from HOL auditor", {"write_layout": False}, True, 1, "HOL_AUDIT_MISSING_LAYOUT"),
    ("reject: hardcoded developer path in Holmakefile", {"holmakefile_text": "CAKEMLDIR = /Users/dev/cakeml\n"}, True, 1, "HARDCODED_DEV_PATH"),
    ("reject: HOL auditor flags shadowed constant", {"hol_audit_exit": 1, "hol_audit_stdout": "HOL_AUDIT_FAIL: missing required constant: forge_counterSpec$counter_run\n"}, True, 1, "HOL_AUDIT_FAILED"),
    ("reject: HOL auditor flags missing forge_m1_nonvacuous", {"hol_audit_exit": 1, "hol_audit_stdout": "HOL_AUDIT_FAIL: missing non-vacuity theorem\n"}, True, 1, "HOL_AUDIT_FAILED"),
    ("reject: HOL auditor flags b <> Fail premise escape hatch", {"hol_audit_exit": 1, "hol_audit_stdout": "HOL_AUDIT_FAIL: EXACT_TERM_MISMATCH on forge_m1Kernel.forge_m1_kernel_correct\n"}, True, 1, "HOL_AUDIT_FAILED"),
    ("reject: HOL auditor flags tacked-on biconditional conjunct", {"hol_audit_exit": 1, "hol_audit_stdout": "HOL_AUDIT_FAIL: EXACT_TERM_MISMATCH on forge_m1Kernel.forge_m1_kernel_correct\n"}, True, 1, "HOL_AUDIT_FAILED"),
    # Spec-hash pinning & exact Term.aconv negative controls (5 new planted failures)
    ("reject: missing kernel/SPEC_HASHES.sha256", {"write_spec_hashes": False}, True, 1, "SPEC_HASH_FILE_MISSING"),
    ("reject: malformed kernel/SPEC_HASHES.sha256", {"spec_hashes_override": "not-a-hash  kernel/proof/x.sml\n"}, True, 1, "SPEC_HASH_FILE_MALFORMED"),
    ("reject: 1-byte mutation in pinned forge_counterSpecScript.sml", {"spec_counter_text": SPEC_COUNTER_TEXT + " "}, True, 1, "SPEC_HASH_MISMATCH"),
    ("reject: 1-byte mutation in pinned forge_contractSpecScript.sml", {"spec_contract_text": SPEC_CONTRACT_TEXT + " "}, True, 1, "SPEC_HASH_MISMATCH"),
    ("reject: HOL auditor flags exact Term.aconv mismatch on nonvacuous", {"hol_audit_exit": 1, "hol_audit_stdout": "HOL_AUDIT_FAIL: EXACT_TERM_MISMATCH on forge_m1Kernel.forge_m1_nonvacuous\n"}, True, 1, "HOL_AUDIT_FAILED"),
    # Theorem catalog byte-for-byte freshness controls (3 new planted failures)
    ("reject: missing docs/THEOREM_CATALOG.md", {"write_catalog": False}, True, 1, "THEOREM_CATALOG_MISSING"),
    ("reject: stale or hand-edited docs/THEOREM_CATALOG.md", {"catalog_text": GOOD_CATALOG_TEXT + "hand-edited claim\n"}, True, 1, "THEOREM_CATALOG_MISMATCH"),
    ("reject: theorem catalog exporter fails", {"catalog_export_exit": 1, "catalog_export_stdout": "CATALOG_EXPORT_FAIL: bad tag\n"}, True, 1, "CATALOG_EXPORT_FAILED"),
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
