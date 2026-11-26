/*
 * Forge Milestone 1: Static Non-PIE Linux AArch64 ELF Linker Script
 *
 * Fixed low addresses (base 0x00400000, slide = 0, all vaddrs << 2^55 for P-LO55).
 * Strict W^X: separate RX (.text) and RW (.data + .bss) PT_LOAD segments.
 * Zero PT_INTERP, zero PT_DYNAMIC, zero libc.
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
        *(.text.shim)
        PROVIDE(forge_text_end = .);
    } :text

    . = ALIGN(0x10000);

    .data : ALIGN(0x10000)
    {
        PROVIDE(forge_data_start = .);
        *(.data)
        *(.rodata*)
        PROVIDE(forge_data_end = .);
    } :data

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
