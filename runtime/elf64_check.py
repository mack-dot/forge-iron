#!/usr/bin/env python3
"""Pure-Python ELF64 AArch64 structural and zero-gap byte-equivalence verifier.

Binds HOL4-extracted machine bytes AND exact HOL4 layout virtual addresses
(`theorem_layout.txt`) directly to the compiled static non-PIE Linux ARM64 ELF
PT_LOAD segments (not trusting .symtab alone).

Supports both 16-byte (`ffirecv16`/`ffisend16`) and 64-byte (`ffirecv64`/`ffisend64`)
frozen runtime shims inside the 256 KB RX code slot `[0x400000..0x440000)`.
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

REQUIRED_LAYOUT_KEYS = (
    "veneers_base",
    "ffirecv16_veneer",
    "ffisend16_veneer",
    "install_veneer",
    "exit_veneer",
    "cake_main",
    "cb_begin",
    "cb_end",
    "cbspace",
    "shim_base",
    "ffirecv16",
    "ffisend16",
    "cml_exit",
    "cml_install",
    "shim_end",
    "cml_heap",
    "cml_stack",
    "cml_stackend",
    "cake_bitmaps",
    "bm_buf_end",
    "rx_tmp",
    "forge_heap",
    "forge_stack",
    "forge_stackend",
    "frame_bytes",
)


class ElfError(ValueError):
    """Raised when an ELF violates structural, layout, or byte-equivalence invariants."""


def parse_layout(text: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for line in text.splitlines():
        s = line.strip()
        if not s or "=" not in s:
            continue
        k, v = s.split("=", 1)
        k, v = k.strip(), v.strip()
        if k in out:
            raise ElfError(f"LAYOUT_DUPLICATE_KEY ({k})")
        try:
            out[k] = int(v, 0)
        except ValueError as exc:
            raise ElfError(f"LAYOUT_BAD_INT ({k}={v})") from exc
    missing = [k for k in REQUIRED_LAYOUT_KEYS if k not in out]
    if missing:
        raise ElfError("LAYOUT_MISSING_KEYS (" + ",".join(missing) + ")")
    return out


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
            if p_memsz < p_filesz:
                raise ElfError(f"ELF_MEMSZ_LT_FILESZ (vaddr=0x{p_vaddr:x})")
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

    sorted_loads = sorted(phdrs, key=lambda s: s["vaddr"])
    for a, b in zip(sorted_loads, sorted_loads[1:]):
        if a["vaddr"] + a["memsz"] > b["vaddr"]:
            raise ElfError(
                f"ELF_OVERLAPPING_PT_LOAD (0x{a['vaddr']:x}..0x{a['vaddr']+a['memsz']:x} vs 0x{b['vaddr']:x})"
            )

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
            if sh["link"] >= len(shdrs):
                raise ElfError(f"ELF_BAD_SYMTAB_LINK (link={sh['link']})")
            strtab = shdrs[sh["link"]]
            if strtab["offset"] + strtab["size"] > len(data):
                raise ElfError("ELF_TRUNCATED_STRTAB")
            if sh["offset"] + sh["size"] > len(data):
                raise ElfError("ELF_TRUNCATED_SYMTAB")
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
                        if name in syms and syms[name] != st_value and not name.startswith("$"):
                            raise ElfError(
                                f"ELF_DUPLICATE_SYMBOL ({name}: 0x{syms[name]:x} vs 0x{st_value:x})"
                            )
                        syms[name] = st_value

    return {"entry": e_entry, "loads": phdrs, "syms": syms}


def read_seg_vaddr(data: bytes, seg: dict, vaddr: int, length: int) -> bytes:
    if seg["vaddr"] <= vaddr and vaddr + length <= seg["vaddr"] + seg["filesz"]:
        foff = seg["offset"] + (vaddr - seg["vaddr"])
        return data[foff : foff + length]
    raise ElfError(f"ELF_VADDR_UNMAPPED_IN_SEG (0x{vaddr:x}+{length})")


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
    layout: dict[str, int],
) -> dict:
    for k in REQUIRED_LAYOUT_KEYS:
        if k not in layout:
            raise ElfError(f"LAYOUT_MISSING_KEY ({k})")

    data = elf_path.read_bytes()
    elf = parse_elf64(data)
    loads = elf["loads"]
    syms = elf["syms"]

    t_begin = layout["veneers_base"]
    c_main = layout["cake_main"]
    cb_begin = layout["cb_begin"]
    cb_end = layout["cb_end"]
    cbspace = layout["cbspace"]
    s_start = layout["shim_base"]
    s_end = layout["shim_end"]
    cml_heap = layout["cml_heap"]
    bm_begin = layout["cake_bitmaps"]
    bm_end = layout["bm_buf_end"]
    rx_tmp = layout["rx_tmp"]
    heap = layout["forge_heap"]
    stk = layout["forge_stack"]
    stk_end = layout["forge_stackend"]
    frame_bytes = layout["frame_bytes"]
    if frame_bytes not in (16, 64, 128):
        raise ElfError(f"LAYOUT_BAD_FRAME_BYTES ({frame_bytes})")
    if frame_bytes == 128:
        m3_req = ("rx_tmp_bytes", "fficommit_veneer", "ffibootload_veneer", "fficommit", "ffibootload")
        m3_missing = [k for k in m3_req if k not in layout]
        if m3_missing:
            raise ElfError("LAYOUT_MISSING_KEYS (" + ",".join(m3_missing) + ")")
        rx_tmp_span = layout["rx_tmp_bytes"]
        if rx_tmp_span != 544:
            raise ElfError(f"LAYOUT_BAD_RX_TMP_BYTES ({rx_tmp_span})")
    else:
        rx_tmp_span = frame_bytes

    if not (t_begin < c_main < cb_begin <= cb_end <= s_start < s_end < LO55_LIMIT):
        raise ElfError("LAYOUT_EXEC_ORDER_INVALID")
    if "slot_end" in layout and cb_end > layout["slot_end"]:
        raise ElfError(f"LAYOUT_CODE_EXCEEDS_SLOT (cb_end=0x{cb_end:x} > slot_end=0x{layout['slot_end']:x})")
    if cb_end - cb_begin != cbspace:
        raise ElfError(f"LAYOUT_CBSPACE_MISMATCH (cb_end-cb_begin={cb_end-cb_begin} != {cbspace})")
    if c_main - t_begin != len(theorem_veneers):
        raise ElfError(f"LAYOUT_VENEERS_LEN_MISMATCH ({c_main-t_begin} != {len(theorem_veneers)})")
    if cb_begin - c_main != len(theorem_code):
        raise ElfError(f"LAYOUT_CODE_LEN_MISMATCH ({cb_begin-c_main} != {len(theorem_code)})")
    if s_end - s_start != len(theorem_shim):
        raise ElfError(f"LAYOUT_SHIM_LEN_MISMATCH ({s_end-s_start} != {len(theorem_shim)})")
    if bm_end - bm_begin != len(theorem_data):
        raise ElfError(f"LAYOUT_DATA_LEN_MISMATCH ({bm_end-bm_begin} != {len(theorem_data)})")

    if elf["entry"] != s_start:
        raise ElfError(f"ELF_ENTRY_MISMATCH (elf=0x{elf['entry']:x} hol4=0x{s_start:x})")

    exec_segs = [seg for seg in loads if seg["flags"] & PF_X]
    if len(exec_segs) != 1:
        raise ElfError(f"ELF_EXPECTED_ONE_EXEC_SEGMENT (got {len(exec_segs)})")
    xseg = exec_segs[0]
    if (xseg["flags"] & (PF_R | PF_X)) != (PF_R | PF_X):
        raise ElfError(f"ELF_EXEC_FLAGS_INVALID (flags=0x{xseg['flags']:x})")
    if xseg["vaddr"] != t_begin:
        raise ElfError(f"ELF_EXEC_VADDR_MISMATCH (elf=0x{xseg['vaddr']:x} hol4=0x{t_begin:x})")
    if xseg["memsz"] != xseg["filesz"]:
        raise ElfError(f"ELF_EXEC_MEMSZ_NE_FILESZ (memsz=0x{xseg['memsz']:x} filesz=0x{xseg['filesz']:x})")
    x_end = xseg["vaddr"] + xseg["filesz"]
    if x_end != s_end:
        raise ElfError(f"ELF_EXEC_END_MISMATCH (elf=0x{x_end:x} hol4=0x{s_end:x})")

    elf_veneers = read_seg_vaddr(data, xseg, t_begin, len(theorem_veneers))
    if elf_veneers != theorem_veneers:
        raise ElfError(
            f"VENEERS_BYTE_MISMATCH (elf={len(elf_veneers)}B theorem={len(theorem_veneers)}B)"
        )

    elf_code = read_seg_vaddr(data, xseg, c_main, len(theorem_code))
    if elf_code != theorem_code:
        raise ElfError(
            f"CODE_BYTE_MISMATCH (elf={len(elf_code)}B theorem={len(theorem_code)}B)"
        )

    elf_pad = read_seg_vaddr(data, xseg, cb_begin, s_start - cb_begin)
    check_padding_only(elf_pad)

    elf_shim = read_seg_vaddr(data, xseg, s_start, len(theorem_shim))
    if elf_shim != theorem_shim:
        raise ElfError(
            f"SHIM_BYTE_MISMATCH (elf={len(elf_shim)}B theorem={len(theorem_shim)}B)"
        )

    rw_segs = [seg for seg in loads if (seg["flags"] & PF_W) and not (seg["flags"] & PF_X)]
    if len(rw_segs) != 1:
        raise ElfError(f"ELF_EXPECTED_ONE_RW_SEGMENT (got {len(rw_segs)})")
    dseg = rw_segs[0]
    if (dseg["flags"] & (PF_R | PF_W)) != (PF_R | PF_W):
        raise ElfError(f"ELF_RW_FLAGS_INVALID (flags=0x{dseg['flags']:x})")
    if dseg["vaddr"] > cml_heap or dseg["vaddr"] + dseg["filesz"] < bm_end:
        raise ElfError(
            f"ELF_RW_DATA_UNMAPPED (seg=0x{dseg['vaddr']:x}..0x{dseg['vaddr']+dseg['filesz']:x} "
            f"need=0x{cml_heap:x}..0x{bm_end:x})"
        )
    if dseg["vaddr"] + dseg["memsz"] < stk_end:
        raise ElfError(
            f"ELF_RW_HEAP_UNMAPPED (seg_end=0x{dseg['vaddr']+dseg['memsz']:x} "
            f"need_stackend=0x{stk_end:x})"
        )
    if dseg["vaddr"] > rx_tmp or dseg["vaddr"] + dseg["memsz"] < rx_tmp + rx_tmp_span:
        raise ElfError(f"ELF_RW_RX_TMP_UNMAPPED (rx_tmp=0x{rx_tmp:x})")

    elf_data = read_seg_vaddr(data, dseg, bm_begin, len(theorem_data))
    if elf_data != theorem_data:
        raise ElfError(
            f"BITMAPS_BYTE_MISMATCH (elf={len(elf_data)}B theorem={len(theorem_data)}B)"
        )

    if (heap & 7) != 0 or (stk & 7) != 0 or (stk_end & 15) != 0:
        raise ElfError("ELF_HEAP_UNALIGNED")
    if not (
        s_end <= cml_heap < bm_begin < bm_end <= rx_tmp
        and rx_tmp + rx_tmp_span <= heap < stk < stk_end < LO55_LIMIT
    ):
        raise ElfError("ELF_HEAP_BOUNDS_INVALID")
    if (stk_end - heap) < 8192:
        raise ElfError("ELF_HEAP_TOO_SMALL")

    if frame_bytes == 128:
        sym_bindings = {
            "cake_text_begin": t_begin,
            "cml_main": t_begin,
            "cake_main": c_main,
            "cake_codebuffer_begin": cb_begin,
            "cake_codebuffer_end": cb_end,
            "_start": s_start,
            "ffirecv64": layout["ffirecv16"],
            "ffisend128": layout["ffisend16"],
            "fficommit": layout["fficommit"],
            "ffibootload": layout["ffibootload"],
            "cml_exit": layout["cml_exit"],
            "cml_install": layout["cml_install"],
            "forge_shim_end": s_end,
            "cake_bitmaps": bm_begin,
            "forge_heap": heap,
            "forge_stack": stk,
            "forge_stackend": stk_end,
        }
    else:
        recv_sym = f"ffirecv{frame_bytes}"
        send_sym = f"ffisend{frame_bytes}"
        sym_bindings = {
            "cake_text_begin": t_begin,
            "cml_main": t_begin,
            "cake_main": c_main,
            "cake_codebuffer_begin": cb_begin,
            "cake_codebuffer_end": cb_end,
            "_start": s_start,
            recv_sym: layout["ffirecv16"],
            send_sym: layout["ffisend16"],
            "cml_exit": layout["cml_exit"],
            "cml_install": layout["cml_install"],
            "forge_shim_end": s_end,
            "cake_bitmaps": bm_begin,
            "forge_heap": heap,
            "forge_stack": stk,
            "forge_stackend": stk_end,
        }
    missing = [s for s in sym_bindings if s not in syms]
    if missing:
        raise ElfError("ELF_MISSING_SYMBOLS (" + ",".join(missing) + ")")
    for name, want in sym_bindings.items():
        if syms[name] != want:
            raise ElfError(f"ELF_SYMBOL_VADDR_MISMATCH ({name}: elf=0x{syms[name]:x} hol4=0x{want:x})")

    return {
        "exec_bytes_total": x_end - t_begin,
        "veneers_bytes": len(elf_veneers),
        "code_bytes": len(elf_code),
        "padding_bytes": len(elf_pad),
        "shim_bytes": len(elf_shim),
        "data_bytes": len(elf_data),
        "unverified_exec_gap_bytes": 0,
    }
