# `hol2pan` Design — Certifying Pure-HOL4 to Pancake Zero-GC Translator (Planned M5)

**Status:** Planned post-M2/M3 architecture (target: Milestone 5). Milestones 1–3 use CakeML's verified `ml_translator` + `runtime/` 256 KB slot to deliver end-to-end verified ARM64 binaries rapidly; `hol2pan` eliminates the CakeML garbage collector and heap runtime in Ring 0 once the Guardrail (M2), Crypto/Crash-Recovery (M3), and Spec-Compiler (M4) layers stabilize.

## Motivation

CakeML's `ml_translator` gives us an immediate 20x proving speedup (`pure HOL4 -> CakeML AST -> ARM64 ELF` in seconds with zero manual Separation Logic). However, CakeML still carries a copying garbage collector and dynamic heap (`forge_heap`, 256 KiB) inside Ring 0. `MASTER_PLAN.md` sets the long-term Ring-0 goal: **zero garbage collection and zero dynamic heap allocation**, compiling directly through CakeML's **Pancake** systems-language backend (`pancake -> crep -> loop -> word -> stack -> lab -> arm8`).

## Architecture: Certifying Translation (`hol2pan`)

`hol2pan` is a proof-producing SML library in HOL4 (analogous to `ml_translatorLib`, targeting Pancake's `panLang` AST instead of CakeML's `ast$dec`). Because it is **certifying** (proof-producing inside HOL4's kernel), bugs in `hol2pan` itself can never break soundness—every translated function emits a kernel-checked simulation theorem.

```text
Pure HOL4 Spec (fixed-width word64 + bounded static state record)
        │
        ▼  hol2panLib.translate_pan (certifying SML translator, untrusted)
Pancake AST (`panLang$prog`)  +  Kernel-Checked Simulation Theorem:
        ⊢ panSem$evaluate (s0, pan_prog) = (res, s1)  ∧  state_rel (step st0 req) s1
        │
        ▼  CakeML verified Pancake backend (`pan_to_targetProof`)
Static Zero-GC ARM64 Machine Code (fits in frozen `runtime/` 256 KB RX slot)
        │
        ▼  Frozen `runtime/` (`forge_arm8Erasure` + `forge_shimProof` at `_start = 0x450000`)
Standalone Zero-GC, Zero-libc, Zero-C-Compiler ARM64 ELF (`gap_bytes = 0`)
```

## Supported Source Fragment (Ring-0 Pure Subset)

To keep translation deterministic, allocation-free, and WCET-bounded, `hol2pan` accepts a strict pure HOL4 subset:

1. **Types:** Fixed-width words (`word8`, `word32`, `word64`), booleans, fixed-size product/record types (`State`), and fixed-length static arrays (mapped to constant offsets inside `.bss`).
2. **Control Flow:** Non-recursive `let` bindings, `if/then/else`, pattern matching on finite enumerations/opcodes, and bounded loops with explicit constant fuel (compiled to Pancake `While` with statically proved termination).
3. **Operations:** Bitwise/arithmetic word ops (`+`, `-`, `*`, `&&`, `‖`, `⊕`, shifts, unsigned comparisons `<₊`, `≤₊`), pure field reads/writes, and fixed-offset static buffer loads/stores.
4. **Prohibited:** General recursion, dynamic allocation (`Cons`/`Ref`/`Word8Array.array` inside the step loop), closures, exceptions, and unbounded lists.

## Memory & Calling Convention (Drop-In Compatibility with `runtime/`)

- **Static `.bss` State Layout:** A single flat record layout (`STATE_BASE = 0x480000`, `RX_BUF = 0x470000`, `TX_BUF = 0x470040`) replaces CakeML's GC heap and bitmaps completely.
- **FFI Boundary:** Pancake's `@ffi` calls (`@recv64`, `@send64`, `@pwrite64`, `@fdatasync`) target the exact same verified ARM64 shim stubs at `_start = 0x450000` in `runtime/shim/`.
- **Erasure & No-`svc #0` Reuse:** Because Pancake shares CakeML's `lab_to_target` and `arm8_config` encoder backend, `runtime/hol4/forge_arm8ErasureTheory` (`encoded_bytes_in_mem_not_svc0` + `machine_sem_real_eq_exact`) transfers directly with zero re-proving.

## Phased Delivery Plan

1. **M2–M3 (Current):** Ship Guardrail + SHA-256/HMAC + Dual-Slot Crash Recovery on `runtime/` + `ml_translator` + `forge_frameRunner` (`end_to_end=true`).
2. **M4:** Build bijective Canonical English ↔ `ForgeSpec` compiler targeting the same pure HOL4 fragment.
3. **M5 (`hol2pan`):** Implement `hol2panLib` for the fixed-width pure HOL4 fragment, compose with upstream `pan_to_targetProof`, drop the CakeML GC heap from Ring 0, and prepare for Level 3 (`seL4` / Microkit) and Level 5 (Silver Verilog FPGA).
