/*
 * Forge Reusable Runtime: Static Non-PIE Linux AArch64 256 KB Slot Linker Script
 *
 * Fixed low addresses (base 0x00400000, slide = 0, all vaddrs << 2^55 for P-LO55).
 * Strict W^X: separate RX (.text) and RW (.data + .bss) PT_LOAD segments on 64 KiB pages.
 * Zero PT_INTERP, zero PT_DYNAMIC, zero libc.
 *
 * Layout:
 *   0x00400000 .. 0x004000B0  CakeML veneers (cml_main + 2 FFI + install + exit)
 *   0x004000B0 .. 0x00440000  256 KB fixed CakeML code slot (any kernel <= 261,968 B)
 *   0x00440000 .. 0x00450000  Verified zero-gap padding (ARM64 UDF#0 / NOP only)
 *   0x00450000 .. 0x00450140  Fixed raw ARM64 syscall shim (_start = 0x450000, 320 B)
 *   0x00460000 .. 0x00470000  cml_{heap,stack,stackend} + CakeML bitmaps (<= 64 KB)
 *   0x00470000 .. 0x00470040  forge_rx_tmp (64 B scratch receive buffer)
 *   0x00480000 .. 0x004C0000  forge_heap (256 KiB)
 *   0x004C0000 .. 0x00500000  forge_stack .. forge_stackend (256 KiB)
 */

OUTPUT_FORMAT("elf64-littleaarch64")
OUTPUT_ARCH(aarch64)
ENTRY(_start)

PHDRS
{
    text PT_LOAD FLAGS(5); /* PF_R | PF_X */
    data PT_LOAD FLAGS(6); /* PF_R | PF_W */
}

SECTIONS
{
    . = 0x00400000;

    .text : ALIGN(0x10000)
    {
        PROVIDE(forge_text_start = .);
        *(.text)
        ASSERT(. <= 0x50000, "CakeML code slot exceeded 256 KB boundary before _start=0x450000");
        . = 0x50000;
        *(.text.shim)
        PROVIDE(forge_text_end = .);
    } :text =0x00000000

    . = 0x00460000;

    .data : ALIGN(0x10000)
    {
        PROVIDE(forge_data_start = .);
        *(.data)
        *(.rodata*)
        ASSERT(. <= 0x10000, "CakeML bitmaps exceeded 64 KB data slot before 0x470000");
        PROVIDE(forge_data_end = .);
    } :data

    . = 0x00470000;

    .bss : ALIGN(0x10000)
    {
        PROVIDE(forge_bss_start = .);
        *(.bss)
        *(COMMON)
        PROVIDE(forge_bss_end = .);
    } :data

    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
    }
}
