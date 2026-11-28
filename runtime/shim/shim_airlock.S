/*
 * Forge Milestone 3 Runtime: Raw Linux AArch64 Crypto-Airlock & Dual-Slot Disk Shim
 * (Zero libc, Zero C stack, Fixed _start = 0x00450000)
 *
 * Strictly 6 Linux AArch64 syscalls:
 *   __NR_read       = 63 (fd 0 stdin 64B frames, fd 4 boot key 32B)
 *   __NR_write      = 64 (fd 1 stdout 128B response + HMAC capability frames)
 *   __NR_pread64    = 67 (fd 3 dual-slot disk state 512B at offset 0)
 *   __NR_pwrite64   = 68 (fd 3 inactive slot 256B at offset 0 or 256)
 *   __NR_fdatasync  = 83 (fd 3 crash-atomic durability barrier before token emit)
 *   __NR_exit_group = 94
 *
 * Fixed _start = 0x00450000 inside runtime/shim/forge_slot.ld.
 * Callee-saved registers x19..x28 and SP are strictly preserved.
 */

.section .text.shim, "ax", @progbits
.p2align 2

.globl _start
.type _start, @function
_start:
    adrp    x0, forge_heap
    add     x0, x0, :lo12:forge_heap
    adrp    x1, cml_heap
    add     x1, x1, :lo12:cml_heap
    str     x0, [x1]

    adrp    x0, forge_stack
    add     x0, x0, :lo12:forge_stack
    adrp    x1, cml_stack
    add     x1, x1, :lo12:cml_stack
    str     x0, [x1]

    adrp    x0, forge_stackend
    add     x0, x0, :lo12:forge_stackend
    adrp    x1, cml_stackend
    add     x1, x1, :lo12:cml_stackend
    str     x0, [x1]

    b       cml_main
.size _start, . - _start

/* ffirecv64: 65B buffer (buf[0]=status, buf[1..64]=64B request from fd 0) */
.globl ffirecv64
.type ffirecv64, @function
ffirecv64:
    cmp     x3, #65
    b.lo    .Lrecv_ret
    mov     x9, x2
    adrp    x10, forge_rx_tmp
    add     x10, x10, :lo12:forge_rx_tmp
    mov     x11, #64
.Lrecv_loop:
    cbz     x11, .Lrecv_ok
    mov     x0, #0
    mov     x1, x10
    mov     x2, x11
    mov     x8, #63
    svc     #0
    cmn     x0, #4
    b.eq    .Lrecv_loop
    cmp     x0, #0
    b.le    .Lrecv_err
    add     x10, x10, x0
    sub     x11, x11, x0
    b       .Lrecv_loop
.Lrecv_ok:
    adrp    x12, forge_rx_tmp
    add     x12, x12, :lo12:forge_rx_tmp
    mov     x11, #0
.Lrecv_copy:
    ldrb    w10, [x12, x11]
    add     x11, x11, #1
    strb    w10, [x9, x11]
    cmp     x11, #64
    b.lo    .Lrecv_copy
    strb    wzr, [x9]
    ret
.Lrecv_err:
    mov     w12, #1
    strb    w12, [x9]
.Lrecv_ret:
    ret
.size ffirecv64, . - ffirecv64

/* ffisend128: 129B buffer (buf[0]=status, buf[1..128]=128B response to fd 1) */
.globl ffisend128
.type ffisend128, @function
ffisend128:
    cmp     x3, #129
    b.lo    .Lsend_ret
    mov     x9, x2
    add     x10, x2, #1
    mov     x11, #128
.Lsend_loop:
    cbz     x11, .Lsend_ok
    mov     x0, #1
    mov     x1, x10
    mov     x2, x11
    mov     x8, #64
    svc     #0
    cmn     x0, #4
    b.eq    .Lsend_loop
    cmp     x0, #0
    b.le    .Lsend_err
    add     x10, x10, x0
    sub     x11, x11, x0
    b       .Lsend_loop
.Lsend_ok:
    strb    wzr, [x9]
    ret
.Lsend_err:
    mov     w12, #1
    strb    w12, [x9]
.Lsend_ret:
    ret
.size ffisend128, . - ffisend128

/* fficommit: 258B buffer (buf[0]=status, buf[1]=slot 0/1, buf[2..257]=256B slot -> fd 3 + fdatasync) */
.globl fficommit
.type fficommit, @function
fficommit:
    cmp     x3, #258
    b.lo    .Lcommit_ret
    mov     x9, x2
    ldrb    w13, [x9, #1]
    and     x13, x13, #1
    lsl     x13, x13, #8
    add     x10, x9, #2
    mov     x11, #256
.Lcommit_loop:
    cbz     x11, .Lcommit_sync
    mov     x0, #3
    mov     x1, x10
    mov     x2, x11
    mov     x3, x13
    mov     x8, #68
    svc     #0
    cmn     x0, #4
    b.eq    .Lcommit_loop
    cmp     x0, #0
    b.le    .Lcommit_err
    add     x10, x10, x0
    sub     x11, x11, x0
    add     x13, x13, x0
    b       .Lcommit_loop
.Lcommit_sync:
    mov     x0, #3
    mov     x8, #83
    svc     #0
    cmn     x0, #4
    b.eq    .Lcommit_sync
    cbnz    x0, .Lcommit_err
    strb    wzr, [x9]
    ret
.Lcommit_err:
    mov     w12, #1
    strb    w12, [x9]
.Lcommit_ret:
    ret
.size fficommit, . - fficommit

/* ffibootload: 545B buffer (buf[0]=status, buf[1..32]=fd 4 key, buf[33..544]=fd 3 slots A||B) */
.globl ffibootload
.type ffibootload, @function
ffibootload:
    cmp     x3, #545
    b.lo    .Lboot_ret
    mov     x9, x2
    adrp    x10, forge_rx_tmp
    add     x10, x10, :lo12:forge_rx_tmp
    mov     x11, #32
.Lboot_key:
    cbz     x11, .Lboot_disk_init
    mov     x0, #4
    mov     x1, x10
    mov     x2, x11
    mov     x8, #63
    svc     #0
    cmn     x0, #4
    b.eq    .Lboot_key
    cmp     x0, #0
    b.le    .Lboot_err
    add     x10, x10, x0
    sub     x11, x11, x0
    b       .Lboot_key
.Lboot_disk_init:
    mov     x11, #512
    mov     x13, #0
.Lboot_disk:
    cbz     x11, .Lboot_copy_init
    mov     x0, #3
    mov     x1, x10
    mov     x2, x11
    mov     x3, x13
    mov     x8, #67
    svc     #0
    cmn     x0, #4
    b.eq    .Lboot_disk
    cbz     x0, .Lboot_zero
    tbnz    x0, #63, .Lboot_err
    add     x10, x10, x0
    sub     x11, x11, x0
    add     x13, x13, x0
    b       .Lboot_disk
.Lboot_zero:
    cbz     x11, .Lboot_copy_init
    strb    wzr, [x10]
    add     x10, x10, #1
    sub     x11, x11, #1
    b       .Lboot_zero
.Lboot_copy_init:
    adrp    x12, forge_rx_tmp
    add     x12, x12, :lo12:forge_rx_tmp
    mov     x11, #0
.Lboot_copy:
    ldrb    w10, [x12, x11]
    add     x11, x11, #1
    strb    w10, [x9, x11]
    cmp     x11, #544
    b.lo    .Lboot_copy
    strb    wzr, [x9]
    ret
.Lboot_err:
    mov     w12, #1
    strb    w12, [x9]
.Lboot_ret:
    ret
.size ffibootload, . - ffibootload

.globl cml_exit
.type cml_exit, @function
cml_exit:
    cbz     x0, .Lexit_go
    mov     x0, #1
.Lexit_go:
    mov     x8, #94
    svc     #0
.Lexit_trap:
    b       .Lexit_trap
.size cml_exit, . - cml_exit

.globl cml_install
.type cml_install, @function
cml_install:
    mov     x0, #2
    mov     x8, #94
    svc     #0
.Linst_trap:
    b       .Linst_trap
.size cml_install, . - cml_install

.globl forge_shim_end
forge_shim_end:

.section .bss
.p2align 4
.globl forge_rx_tmp
forge_rx_tmp:
    .space  544

.p2align 16
.globl forge_heap
forge_heap:
    .space  262144
.globl forge_stack
forge_stack:
    .space  262144
.globl forge_stackend
forge_stackend:
