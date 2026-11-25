/*
 * Forge Milestone 1: Raw Linux AArch64 Syscall & Startup Shim (Zero libc, Zero C stack)
 *
 * Strictly 3 Linux AArch64 syscalls:
 *   __NR_read       = 63 (fd 0, stdin)
 *   __NR_write      = 64 (fd 1, stdout)
 *   __NR_exit_group = 94
 *
 * Register discipline (verified in HOL4 forge_shimProofTheory):
 *   - Leaf stubs use only caller-saved registers x0..x3, x8..x12.
 *   - Callee-saved x19..x28, x29, x30, and SP_EL0 are NEVER modified.
 *   - Total FFI contract: if x3 (alen) < 17, return immediately without touching memory.
 *   - 64-bit exit check: cml_exit tests full 64-bit x0 (cbz x0), mapping 0 -> 0 and nonzero -> 1.
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

.globl ffirecv16
.type ffirecv16, @function
ffirecv16:
    cmp     x3, #17
    b.lo    .Lrecv_ret
    mov     x9, x2
    adrp    x10, forge_rx_tmp
    add     x10, x10, :lo12:forge_rx_tmp
    mov     x11, #16
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
    cmp     x11, #16
    b.lo    .Lrecv_copy
    strb    wzr, [x9]
    ret
.Lrecv_err:
    mov     w12, #1
    strb    w12, [x9]
.Lrecv_ret:
    ret
.size ffirecv16, . - ffirecv16

.globl ffisend16
.type ffisend16, @function
ffisend16:
    cmp     x3, #17
    b.lo    .Lsend_ret
    mov     x9, x2
    add     x10, x2, #1
    mov     x11, #16
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
.size ffisend16, . - ffisend16

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
    .space  16

.p2align 16
.globl forge_heap
forge_heap:
    .space  131072
.globl forge_stack
forge_stack:
    .space  131072
.globl forge_stackend
forge_stackend:
