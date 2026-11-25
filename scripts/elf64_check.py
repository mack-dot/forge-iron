#!/usr/bin/env python3
"""Pure-Python ELF64 AArch64 structural and zero-gap byte-equivalence verifier.

Used by scripts/iron_law.py to bind HOL4-extracted machine bytes directly
to the compiled static non-PIE Linux ARM64 ELF binary.
"""
from __future__ import annotations

import struct
from pathlib import Path

ELF_MAGIC = b"\x7fELF"
ELFCLASS64 = 2
ELFDATA2LSB = 1
ET_EXEC = 2
EM_AARCH64 = 183

PT_LOAD = 1
PT_DYNAMIC = 2
PT_INTERP = 3

PF_X = 1
PF_W = 2
PF_R = 4

SHT_SYMTAB = 2
SHT_STRTAB = 3

LO55_LIMIT = 1 << 55
ARM64_NOP = b"\x1f\x20\x03\xd5"
ARM64_UDF0 = b"\x00\x00\x00\x00"


class ElfError(ValueError):
    """Raised when an ELF violates structural or byte-equivalence invariants."""


def parse_elf64(data: bytes) -> dict:
    if len(data) < 64 or data[:4] != ELF_MAGIC:
        raise ElfError("ELF_BAD_MAGIC")
    ei_class, ei_data = data[4], data[5]
    if ei_class != ELFCLASS64 or ei_data != ELFDATA2LSB:
        raise ElfError(f"ELF_BAD_CLASS_OR_ENDIAN (class={ei_class}, data={ei_data})")

    (
        e_type,
        e_machine,
        _e_version,
        e_entry,
        e_phoff,
        e_shoff,
        _e_flags,
        _e_ehsize,
        e_phentsize,
        e_phnum,
        e_shentsize,
        e_shnum,
        _e_shstrndx,
    ) = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)

    if e_type != ET_EXEC:
        raise ElfError(f"ELF_NOT_ET_EXEC (e_type={e_type})")
    if e_machine != EM_AARCH64:
        raise ElfError(f"ELF_NOT_AARCH64 (e_machine={e_machine})")
    if e_entry >= LO55_LIMIT:
        raise ElfError(f"ELF_ENTRY_ABOVE_LO55 (0x{e_entry:x})")

    phdrs = []
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        if off + 56 > len(data):
            raise ElfError("ELF_TRUNCATED_PHDR")
        p_type, p_flags, p_offset, p_vaddr, _p_paddr, p_filesz, p_memsz, p_align = (
            struct.unpack_from("<IIQQQQQQ", data, off)
        )
        if p_type == PT_INTERP:
            raise ElfError("ELF_FORBIDDEN_PT_INTERP")
        if p_type == PT_DYNAMIC:
            raise ElfError("ELF_FORBIDDEN_PT_DYNAMIC")
        if p_type == PT_LOAD:
            if (p_flags & PF_W) and (p_flags & PF_X):
                raise ElfError(f"ELF_WX_VIOLATION (vaddr=0x{p_vaddr:x})")
            if p_vaddr + p_memsz >= LO55_LIMIT:
                raise ElfError(f"ELF_VADDR_ABOVE_LO55 (end=0x{p_vaddr + p_memsz:x})")
            if p_offset + p_filesz > len(data):
                raise ElfError("ELF_SEGMENT_OUT_OF_FILE")
            phdrs.append(
                {
                    "flags": p_flags,
                    "offset": p_offset,
                    "vaddr": p_vaddr,
                    "filesz": p_filesz,
                    "memsz": p_memsz,
                    "align": p_align,
                }
            )

    if not phdrs:
        raise ElfError("ELF_NO_PT_LOAD")

    # Parse sections + .symtab
    shdrs = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        if off + 64 > len(data):
            raise ElfError("ELF_TRUNCATED_SHDR")
        sh = struct.unpack_from("<IIQQQQIIQQ", data, off)
        shdrs.append(
            {
                "name": sh[0],
                "type": sh[1],
                "flags": sh[2],
                "addr": sh[3],
                "offset": sh[4],
                "size": sh[5],
                "link": sh[6],
                "entsize": sh[9],
            }
        )

    syms: dict[str, int] = {}
    for sh in shdrs:
        if sh["type"] == SHT_SYMTAB and sh["entsize"] >= 24:
            strtab = shdrs[sh["link"]]
            str_bytes = data[strtab["offset"] : strtab["offset"] + strtab["size"]]
            count = sh["size"] // sh["entsize"]
            for j in range(count):
                soff = sh["offset"] + j * sh["entsize"]
                st_name, _st_info, _st_other, _st_shndx, st_value, _st_size = (
                    struct.unpack_from("<IBBHQQ", data, soff)
                )
                if st_name < len(str_bytes):
                    end = str_bytes.find(b"\x00", st_name)
                    name = str_bytes[st_name : end if end != -1 else len(str_bytes)].decode(
                        "utf-8", errors="replace"
                    )
                    if name:
                        syms[name] = st_value

    return {"entry": e_entry, "loads": phdrs, "syms": syms}


def read_vaddr(data: bytes, loads: list[dict], vaddr: int, length: int) -> bytes:
    for seg in loads:
        if seg["vaddr"] <= vaddr and vaddr + length <= seg["vaddr"] + seg["filesz"]:
            foff = seg["offset"] + (vaddr - seg["vaddr"])
            return data[foff : foff + length]
    raise ElfError(f"ELF_VADDR_UNMAPPED (0x{vaddr:x}+{length})")


def check_padding_only(buf: bytes) -> None:
    if len(buf) % 4 != 0:
        raise ElfError(f"ELF_PADDING_NOT_WORD_ALIGNED (len={len(buf)})")
    for i in range(0, len(buf), 4):
        w = buf[i : i + 4]
        if w != ARM64_UDF0 and w != ARM64_NOP:
            raise ElfError(
                f"ELF_UNVERIFIED_CODEBUFFER_INSTRUCTION (off=0x{i:x} word={w.hex()})"
            )


def verify_kernel_elf(
    elf_path: Path,
    theorem_veneers: bytes,
    theorem_code: bytes,
    theorem_shim: bytes,
    theorem_data: bytes,
) -> dict:
    data = elf_path.read_bytes()
    elf = parse_elf64(data)
    loads = elf["loads"]
    syms = elf["syms"]

    req_syms = [
        "_start",
        "cake_text_begin",
        "cml_main",
        "cake_main",
        "cake_codebuffer_begin",
        "cake_codebuffer_end",
        "ffirecv16",
        "ffisend16",
        "cml_exit",
        "cml_install",
        "forge_shim_end",
        "cake_bitmaps",
        "forge_heap",
        "forge_stack",
        "forge_stackend",
    ]
    missing = [s for s in req_syms if s not in syms]
    if missing:
        raise ElfError("ELF_MISSING_SYMBOLS (" + ",".join(missing) + ")")

    if elf["entry"] != syms["_start"]:
        raise ElfError(f"ELF_ENTRY_MISMATCH (0x{elf['entry']:x} != 0x{syms['_start']:x})")

    exec_segs = [seg for seg in loads if seg["flags"] & PF_X]
    if len(exec_segs) != 1:
        raise ElfError(f"ELF_EXPECTED_ONE_EXEC_SEGMENT (got {len(exec_segs)})")
    xseg = exec_segs[0]
    x_start = xseg["vaddr"]
    x_end = xseg["vaddr"] + xseg["filesz"]

    # Zero-gap PF_X coverage check:
    # [x_start == cake_text_begin .. cake_main)       == theorem_veneers
    # [cake_main .. cake_codebuffer_begin)            == theorem_code
    # [cake_codebuffer_begin .. _start)               == pure UDF#0 / NOP padding only
    # [_start .. forge_shim_end == x_end)             == theorem_shim
    t_begin = syms["cake_text_begin"]
    c_main = syms["cake_main"]
    cb_begin = syms["cake_codebuffer_begin"]
    s_start = syms["_start"]
    s_end = syms["forge_shim_end"]

    if t_begin != x_start:
        raise ElfError(f"ELF_EXEC_LEADING_GAP (x_start=0x{x_start:x} cake_text_begin=0x{t_begin:x})")
    if s_end != x_end:
        raise ElfError(f"ELF_EXEC_TRAILING_GAP (forge_shim_end=0x{s_end:x} x_end=0x{x_end:x})")
    if not (t_begin < c_main < cb_begin <= s_start < s_end):
        raise ElfError("ELF_EXEC_REGION_ORDER_INVALID")

    elf_veneers = read_vaddr(data, loads, t_begin, c_main - t_begin)
    if elf_veneers != theorem_veneers:
        raise ElfError(
            f"VENEERS_BYTE_MISMATCH (elf={len(elf_veneers)}B theorem={len(theorem_veneers)}B)"
        )

    elf_code = read_vaddr(data, loads, c_main, cb_begin - c_main)
    if elf_code != theorem_code:
        raise ElfError(
            f"CODE_BYTE_MISMATCH (elf={len(elf_code)}B theorem={len(theorem_code)}B)"
        )

    elf_pad = read_vaddr(data, loads, cb_begin, s_start - cb_begin)
    check_padding_only(elf_pad)

    elf_shim = read_vaddr(data, loads, s_start, s_end - s_start)
    if elf_shim != theorem_shim:
        raise ElfError(
            f"SHIM_BYTE_MISMATCH (elf={len(elf_shim)}B theorem={len(theorem_shim)}B)"
        )

    # Verify cake_bitmaps in RW data segment
    elf_data = read_vaddr(data, loads, syms["cake_bitmaps"], len(theorem_data))
    if elf_data != theorem_data:
        raise ElfError(
            f"BITMAPS_BYTE_MISMATCH (elf={len(elf_data)}B theorem={len(theorem_data)}B)"
        )

    # Verify heap/stack layout invariants (aligned 3, e - h >= 8192, < 2^55, disjoint from exec)
    h, stk, e = syms["forge_heap"], syms["forge_stack"], syms["forge_stackend"]
    if (h & 7) != 0 or (stk & 7) != 0 or (e & 7) != 0:
        raise ElfError("ELF_HEAP_UNALIGNED")
    if not (x_end <= h < stk < e < LO55_LIMIT) or (e - h) < 8192:
        raise ElfError("ELF_HEAP_BOUNDS_INVALID")

    return {
        "exec_bytes_total": x_end - x_start,
        "veneers_bytes": len(elf_veneers),
        "code_bytes": len(elf_code),
        "padding_bytes": len(elf_pad),
        "shim_bytes": len(elf_shim),
        "data_bytes": len(elf_data),
        "unverified_exec_gap_bytes": 0,
    }
