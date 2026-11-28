# Verified Theorem Catalog

> **Auto-generated directly from compiled HOL4 `.dat` theory files** by `runtime/export_theorem_catalog.sml`.
> Verified byte-for-byte on every run of `scripts/iron_law.py`. Do not hand-edit this file.

## Global HOL4 Kernel Tag Summary

| Metric | Measured Kernel Value |
| --- | --- |
| Top-level theory | `forge_m3Kernel` |
| `forge_*` theories compiled | `19` |
| Transitive ancestry closure size | `447` theories |
| Exported `forge_*` definitions | `350` |
| Exported `forge_*` theorems | `577` |
| Total verified `forge_*` items | `927` |
| `HYP_COUNT` (max hypotheses across all items) | `0` |
| `ORACLES` (union of all theorem/definition oracle tags) | `[DISK_THM]` |
| `DIRECT_AXIOMS` (union of all direct axiom tags) | `[]` |
| `AXIOMS` (transitive `DB.axioms` closure) | `4`: `bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX` |

## Crown-Jewel Specifications & Theorems

| Layer | Theory | Theorem / Definition | Status | Plain-English Guarantee |
| --- | --- | --- | --- | --- |
| Frozen Runtime Contract | `forge_runtimeSpec` | `forge_slot_loaded_def` | `verified` | SHA-256 pinned 256 KB RX code slot [0x400000..0x440000) and fixed _start (0x450000) contract for any kernel. |
| Frozen Runtime Contract | `forge_runtimeSpec` | `whole_step_def` | `verified` | SHA-256 pinned whole-binary transition relation combining raw arm8$Next with Linux read(63)/write(64) svc #0 contracts. |
| Generic 64B Frame ABI | `forge_frame64Spec` | `frame64_roundtrip` | `verified` | Round-trip bijection proving 64-byte LE64 binary framing is lossless for all 8-word frames. |
| Generic 64B ML Runner | `forge_frameRunner` | `run_frame64_kernel_spec` | `verified` | Polymorphic CF specification of generic CakeML recv64 -> translated step -> send64 runner for zero-SL kernels. |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `encoded_bytes_in_mem_not_svc0` | `verified` | No compiled CakeML arm8_config instruction ever encodes the AArch64 svc #0 opcode (0xD4000001). |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `arm8_target_exact_encoder_correct` | `verified` | Exact arm8$Next encoder correctness proving zero CPU exceptions and strict SP_EL0 preservation on every compiled instruction. |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `machine_sem_real_eq_exact` | `verified` | Unconditional equivalence between real-bits arm8_target_real (TBI0/TBI1/SA0) and erased targetSem with zero b ≠ Fail escape hatch. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `startup_to_cake_main_slot` | `verified` | Parameterized 43-step ARM64 proof from fixed _start (0x450000) through cml_main to cake_main (0x4000B0) for any <=256 KB code blob. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffirecv16_universal_slot` | `verified` | Universal safety of raw ARM64 ffirecv16 at 0x450040 over partial reads, EINTR, truncated EOF, and fatal errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffisend16_universal_slot` | `verified` | Universal safety of raw ARM64 ffisend16 at 0x4500C0 over partial writes, EINTR, and fatal/EPIPE errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffirecv64_universal_slot` | `verified` | Universal safety of raw ARM64 ffirecv64 at 0x450040 over partial reads (1..64B), EINTR, truncated EOF, and fatal errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffisend64_universal_slot` | `verified` | Universal safety of raw ARM64 ffisend64 at 0x4500C0 over partial writes (1..64B), EINTR, and fatal/EPIPE errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `cake_exit_universal_slot` | `verified` | Universal termination proof of exit veneer + cml_exit to Linux svc #0 exit_group(94) with code 0 or 1. |
| Verified Crypto (M3) | `forge_sha256Spec` | `hmac_sha256_rfc4231_tc1` | `verified` | In-logic HOL4 proof verifying pure RFC 2104 HMAC-SHA256 matches official RFC 4231 Test Case 1 byte-for-byte. |
| Pure Spec (M3) | `forge_airlockSpec` | `dual_slot_crash_recovery` | `verified` | Universal dual-slot crash recovery: keyed-HMAC slots recover exact prior state on torn write and exact new state on completed commit. |
| Pure Spec (M3) | `forge_airlockSpec` | `airlock_run_preserves_inv` | `verified` | Exact natural-number fund conservation, rolling cap, and HMAC token invariant across every request stream. |
| Pure Spec (M3) | `forge_airlockSpec` | `airlock_retry_idempotent` | `verified` | Idempotent retry returns the exact cached signed capability token with state unchanged and zero disk commit. |
| Pure Spec (M3) | `forge_airlockSpec` | `airlock_emitted_token_authentic` | `verified` | Every non-zero emitted capability token matches HMAC-SHA256(key, FORGE-CAP-V1 || seq || op || dest || amt || bal). |
| M3 4-FFI ML Runner | `forge_airlockRunner` | `run_airlock_kernel_spec` | `verified` | Polymorphic CF specification of 4-FFI CakeML airlock runner with boot-once and crash-atomic commit ordering. |
| Zero-SL CakeML (M3) | `forge_airlockProg` | `airlock_semantics` | `verified` | Automatically ml_translator-synthesized CakeML airlock_prog terminates cleanly and emits exact airlock_exec frames. |
| Verified Compilation | `forge_airlockCompile` | `airlock_compiled` | `verified` | In-logic CakeML arm8 backend evaluation theorem binding airlock_prog to exact machine-code bytes (code) and bitmaps (data). |
| M3 Startup & Exit Proof | `forge_airlockShimStart` | `m3_startup_to_cake_main_slot` | `verified` | 43-step ARM64 proof from fixed _start (0x450000) through 52-word veneers to cake_main (0x4000D0). |
| M3 I/O Syscall Proofs | `forge_airlockShimIo` | `m3_ffirecv64_universal_slot` | `verified` | Universal safety of raw ARM64 ffirecv64 (fd 0) over partial reads, EINTR, truncated EOF, and errors. |
| M3 I/O Syscall Proofs | `forge_airlockShimIo` | `m3_ffisend128_universal_slot` | `verified` | Universal safety of raw ARM64 ffisend128 (fd 1) over partial writes (1..128B), EINTR, and errors. |
| M3 Disk/Boot Proofs | `forge_airlockShimProof` | `m3_fficommit_universal_slot` | `verified` | Universal crash-atomic durability proof of raw ARM64 fficommit (pwrite64(68) + fdatasync(83)) on fd 3. |
| M3 Disk/Boot Proofs | `forge_airlockShimProof` | `m3_ffibootload_universal_slot` | `verified` | Universal boot proof of raw ARM64 ffibootload (fd 4 32B key + fd 3 512B pread64(67) + zero-fill). |
| M3 4-FFI E2E Compose | `forge_airlockCompose` | `forge_airlock_kernel_compose` | `verified` | Polymorphic whole-binary composition theorem lifting any 4-FFI crypto-airlock kernel from _start to exit_group(94). |
| Non-Vacuity Witness | `forge_m3Kernel` | `forge_m3_nonvacuous` | `verified` | Constructive witness exhibiting a concrete Linux EL0 ARM64 state (TBI0=T, TBI1=F, SA0=T, 16B-aligned SP_EL0) satisfying M3 forge_m3_slot_loaded. |
| Unified End-to-End (M3) | `forge_m3Kernel` | `forge_m3_kernel_correct` | `verified` | Single whole-binary theorem (exact Term.aconv-pinned) connecting fixed _start (0x450000) across 6-syscall m3_whole_step to exit_group(94) and keyed airlock_run. |

## Theory-by-Theory Counts

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_runtimeSpec` | Frozen Runtime Contract | `verified` | 65 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_frame64Spec` | Generic 64B Frame ABI | `verified` | 36 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_frameRunner` | Generic 64B ML Runner | `verified` | 22 | 24 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Frozen 256KB Shim Proof | `verified` | 6 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_slotUtil` | Frozen 256KB Slot Util | `verified` | 0 | 21 | 0 | `[DISK_THM]` | `[]` |
| `forge_sha256Spec` | Verified Crypto (M3) | `verified` | 19 | 15 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockFfi` | M3 4-FFI Airlock ABI | `verified` | 44 | 45 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockContract` | M3 6-Syscall Contract | `verified` | 53 | 21 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockSpec` | Pure Spec (M3) | `verified` | 64 | 35 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockRunner` | M3 4-FFI ML Runner | `verified` | 20 | 23 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockProg` | Zero-SL CakeML (M3) | `verified` | 7 | 185 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimBase` | M3 256KB Shim Base | `verified` | 2 | 36 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimStart` | M3 Startup & Exit Proof | `verified` | 0 | 6 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimIo` | M3 I/O Syscall Proofs | `verified` | 0 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockShimProof` | M3 Disk/Boot Proofs | `verified` | 0 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_airlockCompose` | M3 4-FFI E2E Compose | `verified` | 2 | 1 | 0 | `[DISK_THM]` | `[]` |
| `forge_m3Kernel` | Unified End-to-End (M3) | `verified` | 0 | 2 | 0 | `[DISK_THM]` | `[]` |

## Verbatim Exported Statements (`DB.definitions` & `DB.theorems`)

Each section below dumps every exported definition and theorem directly from the compiled HOL4 `.dat` file using `Hol_pp.thm_to_string`.

<details>
<summary><strong><code>forge_runtimeSpec</code></strong> — Frozen Runtime Contract (65 definitions, 0 theorems)</summary>

SHA-256 pinned 256 KB RX slot [0x400000..0x440000), fixed _start=0x450000, parameterized veneers, 16B/64B shims, and Linux svc #0 contracts.

### Definitions

#### `forge_runtimeSpec.FORGE_CAKE_BITMAPS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CAKE_BITMAPS = 0x460018w
```

#### `forge_runtimeSpec.FORGE_CAKE_MAIN_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CAKE_MAIN = 0x4000B0w
```

#### `forge_runtimeSpec.FORGE_CML_EXIT_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_EXIT = 0x45011Cw
```

#### `forge_runtimeSpec.FORGE_CML_HEAP_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_HEAP = 0x460000w
```

#### `forge_runtimeSpec.FORGE_CML_INSTALL_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_INSTALL = 0x450130w
```

#### `forge_runtimeSpec.FORGE_CML_STACKEND_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_STACKEND = 0x460010w
```

#### `forge_runtimeSpec.FORGE_CML_STACK_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_STACK = 0x460008w
```

#### `forge_runtimeSpec.FORGE_DATA_SLOT_END_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_DATA_SLOT_END = 0x470000w
```

#### `forge_runtimeSpec.FORGE_EXIT_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_EXIT_VENEER = 0x4000A0w
```

#### `forge_runtimeSpec.FORGE_FFIRECV_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFIRECV_VENEER = 0x400070w
```

#### `forge_runtimeSpec.FORGE_FFIRECV_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFIRECV = 0x450040w
```

#### `forge_runtimeSpec.FORGE_FFISEND_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFISEND_VENEER = 0x400080w
```

#### `forge_runtimeSpec.FORGE_FFISEND_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFISEND = 0x4500C0w
```

#### `forge_runtimeSpec.FORGE_HEAP_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_HEAP = 0x480000w
```

#### `forge_runtimeSpec.FORGE_INSTALL_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_INSTALL_VENEER = 0x400090w
```

#### `forge_runtimeSpec.FORGE_MAX_BITMAP_WORDS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_MAX_BITMAP_WORDS = 8189
```

#### `forge_runtimeSpec.FORGE_MAX_CODE_BYTES_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_MAX_CODE_BYTES = 261968
```

#### `forge_runtimeSpec.FORGE_RX_TMP_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_RX_TMP = 0x470000w
```

#### `forge_runtimeSpec.FORGE_SHIM_BASE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_SHIM_BASE = 0x450000w
```

#### `forge_runtimeSpec.FORGE_SHIM_END_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_SHIM_END = 0x450140w
```

#### `forge_runtimeSpec.FORGE_SLOT_END_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_SLOT_END = 0x440000w
```

#### `forge_runtimeSpec.FORGE_STACKEND_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_STACKEND = 0x500000w
```

#### `forge_runtimeSpec.FORGE_STACK_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_STACK = 0x4C0000w
```

#### `forge_runtimeSpec.FORGE_VENEERS_BASE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_VENEERS_BASE = 0x400000w
```

#### `forge_runtimeSpec.align_up_64k_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a. align_up_64k a = a + 65535w && 0xFFFFFFFFFFFF0000w
```

#### `forge_runtimeSpec.arm8_enc_add_x2_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀tgt. arm8_enc_add_x2 tgt = (let imm12 = w2w ((11 >< 0) tgt) in 0x91000042w ‖ imm12 ≪ 10)
```

#### `forge_runtimeSpec.arm8_enc_adrp_x2_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀pc tgt.
    arm8_enc_adrp_x2 pc tgt =
    (let
       delta = ((tgt && 0xFFFFFFFFFFFFF000w) − (pc && 0xFFFFFFFFFFFFF000w)) ≫ 12;
       immlo = w2w ((1 >< 0) delta);
       immhi = w2w ((20 >< 2) delta)
     in
       0x90000002w ‖ immlo ≪ 29 ‖ immhi ≪ 5)
```

#### `forge_runtimeSpec.arm8_target_real_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B. arm8_target_real B =
      arm8_target with
      <|next := Next;
        state_ok :=
          (λms. arm8_ok (erase ms) ∧ bits_of ms = B ∧ (¬SND (SND B) ∨ aligned 4 ms.SP_EL0))|>
```

#### `forge_runtimeSpec.bits_of_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. bits_of s = (s.TCR_EL1.TBI0,s.TCR_EL1.TBI1,s.SCTLR_EL1.SA0)
```

#### `forge_runtimeSpec.erase_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. erase s =
      s with
      <|TCR_EL1 := s.TCR_EL1 with <|TBI0 := F; TBI1 := F|>; SCTLR_EL1 := s.SCTLR_EL1 with SA0 := F|>
```

#### `forge_runtimeSpec.forge_bitmaps_region_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bm_buf_end.
    forge_bitmaps_region_slot bm_buf_end = {a | FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ bm_buf_end}
```

#### `forge_runtimeSpec.forge_cml_ptrs_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_cml_ptrs_region = {a | FORGE_CML_HEAP ≤₊ a ∧ a <₊ FORGE_CAKE_BITMAPS}
```

#### `forge_runtimeSpec.forge_code_region_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end. forge_code_region_slot cb_end = {a | FORGE_CAKE_MAIN ≤₊ a ∧ a <₊ cb_end}
```

#### `forge_runtimeSpec.forge_heap_hdr_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_heap_hdr_region = {a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_HEAP + 40w}
```

#### `forge_runtimeSpec.forge_heap_stack_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_heap_stack_region = {a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_STACKEND}
```

#### `forge_runtimeSpec.forge_mc_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end ffi_names_l ffi_if inst_if.
    forge_mc_slot cb_end bm_buf_end ffi_names_l ffi_if inst_if =
    <|prog_addresses := forge_prog_addresses_slot cb_end bm_buf_end; shared_addresses := ∅;
      ffi_entry_pcs := [FORGE_FFISEND_VENEER; FORGE_FFIRECV_VENEER]; ffi_names := ffi_names_l;
      ptr_reg := 0; len_reg := 1; ptr2_reg := 2; len2_reg := 3; ffi_interfer := ffi_if;
      callee_saved_regs := [19; 20; 21; 22; 23; 24; 25; 26; 27; 28]; next_interfer := K I;
      halt_pc := FORGE_EXIT_VENEER; install_pc := FORGE_INSTALL_VENEER; install_interfer := inst_if;
      target := arm8_target; mmio_info := []|>
```

#### `forge_runtimeSpec.forge_prog_addresses_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end.
    forge_prog_addresses_slot cb_end bm_buf_end =
    forge_code_region_slot cb_end ∪ forge_bitmaps_region_slot bm_buf_end ∪ forge_heap_stack_region
```

#### `forge_runtimeSpec.forge_rx_tmp_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_rx_tmp_region = {a | FORGE_RX_TMP ≤₊ a ∧ a <₊ FORGE_RX_TMP + 64w}
```

#### `forge_runtimeSpec.forge_shim16_words_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_shim16_words = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_runtimeSpec.forge_shim64_words_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_shim64_words = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_runtimeSpec.forge_shim_code_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_shim_code_region =
  {a | FORGE_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_CAKE_MAIN} ∪
  {a | FORGE_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_SHIM_END}
```

#### `forge_runtimeSpec.forge_slot_loaded_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws bytes bitmaps ms0.
    forge_slot_loaded shim_ws bytes bitmaps ms0 ⇔
    (let
       cb_begin = slot_cb_begin (LENGTH bytes);
       cb_end = slot_cb_end (LENGTH bytes);
       bm_buf_end = slot_bm_buf_end (LENGTH bitmaps)
     in
       0 < LENGTH bytes ∧ LENGTH bytes ≤ FORGE_MAX_CODE_BYTES ∧
       LENGTH bitmaps ≤ FORGE_MAX_BITMAP_WORDS ∧ arm8_ok (erase ms0) ∧ sp_ok ms0 ∧
       ms0.PC = FORGE_SHIM_BASE ∧ shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end ms0.MEM ∧
       read_bytearray FORGE_CAKE_MAIN (LENGTH bytes)
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (ms0.MEM a) else NONE) =
       SOME bytes ∧
       ∀i. i < LENGTH bitmaps ⇒
           mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) = n2w bitmaps❲i❳)
```

#### `forge_runtimeSpec.forge_slot_veneers_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_runtimeSpec.is_svc0_at_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. is_svc0_at s ⇔
      s.MEM s.PC = 1w ∧ s.MEM (s.PC + 1w) = 0w ∧ s.MEM (s.PC + 2w) = 0w ∧ s.MEM (s.PC + 3w) = 212w
```

#### `forge_runtimeSpec.lo55_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀mc.
    lo55 mc ⇔
    ∀a. a ∈ mc.prog_addresses ∨ a = mc.halt_pc ∨ a = mc.install_pc ∨ MEM a mc.ffi_entry_pcs ⇒
        untagged a
```

#### `forge_runtimeSpec.real_interfer_ok_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end cbspace ffi_names_l B ffi_if inst_if.
    real_interfer_ok_slot cb_end bm_buf_end cbspace ffi_names_l B ffi_if inst_if ⇔
    (let
       mc =
         forge_mc_slot cb_end bm_buf_end ffi_names_l
           (λk (i,bs,s). erase (ffi_if k (i,bs,restore B s)))
           (λk (bs,s). erase (inst_if k (bs,restore B s)))
     in
       ffi_interfer_ok FORGE_CAKE_MAIN mc ∧ install_interfer_ok FORGE_CAKE_MAIN cbspace mc ∧
       (∀k i bs s.
          bits_of s = B ⇒ bits_of (ffi_if k (i,bs,s)) = B ∧ (ffi_if k (i,bs,s)).SP_EL0 = s.SP_EL0) ∧
       ∀k bs s.
         bits_of s = B ⇒ bits_of (inst_if k (bs,s)) = B ∧ (inst_if k (bs,s)).SP_EL0 = s.SP_EL0)
```

#### `forge_runtimeSpec.real_mc_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B mc. real_mc B mc = mc with target := arm8_target_real B
```

#### `forge_runtimeSpec.restore_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B s.
    restore B s =
    s with
    <|TCR_EL1 := s.TCR_EL1 with <|TBI0 := FST B; TBI1 := FST (SND B)|>;
      SCTLR_EL1 := s.SCTLR_EL1 with SA0 := SND (SND B)|>
```

#### `forge_runtimeSpec.shim_loaded_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end mem.
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end mem ⇔
    words32_in_mem FORGE_VENEERS_BASE (forge_slot_veneers cb_begin cb_end bm_buf_end) mem ∧
    words32_in_mem FORGE_SHIM_BASE shim_ws mem
```

#### `forge_runtimeSpec.shim_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ shim_step = whole_step svc_read_rel svc_write_rel
```

#### `forge_runtimeSpec.slot_bm_buf_end_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀data_len. slot_bm_buf_end data_len = FORGE_CAKE_BITMAPS + n2w (8 * data_len)
```

#### `forge_runtimeSpec.slot_cb_begin_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len. slot_cb_begin code_len = FORGE_CAKE_MAIN + n2w code_len
```

#### `forge_runtimeSpec.slot_cb_end_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len. slot_cb_end code_len = align_up_64k (slot_cb_begin code_len)
```

#### `forge_runtimeSpec.slot_cbspace_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len. slot_cbspace code_len = w2n (slot_cb_end code_len − slot_cb_begin code_len)
```

#### `forge_runtimeSpec.slot_layout_ok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end.
    slot_layout_ok cb_begin cb_end bm_buf_end ⇔
    FORGE_CAKE_MAIN <₊ cb_begin ∧ cb_begin ≤₊ cb_end ∧ cb_end ≤₊ FORGE_SLOT_END ∧
    FORGE_CAKE_BITMAPS ≤₊ bm_buf_end ∧ bm_buf_end ≤₊ FORGE_DATA_SLOT_END
```

#### `forge_runtimeSpec.sp_ok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. sp_ok s ⇔ s.PSTATE.EL = 0w ∧ (¬s.SCTLR_EL1.SA0 ∨ aligned 4 s.SP_EL0)
```

#### `forge_runtimeSpec.svc_exit_group_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀exit_code s.
    svc_exit_group_rel exit_code s ⇔
    s.REG 8w = 94w ∧ s.REG 0w = exit_code ∧ s.MEM s.PC = 1w ∧ s.MEM (s.PC + 1w) = 0w ∧
    s.MEM (s.PC + 2w) = 0w ∧ s.MEM (s.PC + 3w) = 212w
```

#### `forge_runtimeSpec.svc_frame_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s s'.
    svc_frame_rel s s' ⇔
    s'.PC = s.PC + 4w ∧ s'.exception = NoException ∧ s'.PSTATE.EL = s.PSTATE.EL ∧
    s'.SCTLR_EL1 = s.SCTLR_EL1 ∧ s'.TCR_EL1 = s.TCR_EL1 ∧ s'.SP_EL0 = s.SP_EL0 ∧
    ∀r. r ≠ 0w ⇒ s'.REG r = s.REG r
```

#### `forge_runtimeSpec.svc_read_noerr_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inp s s' rest.
    svc_read_noerr_rel inp s s' rest ⇔
    s.REG 8w = 63w ∧ s.REG 0w = 0w ∧ svc_frame_rel s s' ∧
    (s'.REG 0w = -4w ∧ s'.MEM = s.MEM ∧ rest = inp ∨
     s'.REG 0w = 0w ∧ inp = [] ∧ s'.MEM = s.MEM ∧ rest = [] ∨
     ∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ n ≤ LENGTH inp ∧ s'.REG 0w = n2w n ∧
         s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n inp) s.MEM ∧ rest = DROP n inp)
```

#### `forge_runtimeSpec.svc_read_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inp s s' rest.
    svc_read_rel inp s s' rest ⇔
    s.REG 8w = 63w ∧ s.REG 0w = 0w ∧ svc_frame_rel s s' ∧
    (s'.REG 0w = -4w ∧ s'.MEM = s.MEM ∧ rest = inp ∨
     s'.REG 0w = 0w ∧ inp = [] ∧ s'.MEM = s.MEM ∧ rest = [] ∨
     word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w ∧ s'.MEM = s.MEM ∧ rest = inp ∨
     ∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ n ≤ LENGTH inp ∧ s'.REG 0w = n2w n ∧
         s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n inp) s.MEM ∧ rest = DROP n inp)
```

#### `forge_runtimeSpec.svc_write_noerr_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s s' out.
    svc_write_noerr_rel s s' out ⇔
    s.REG 8w = 64w ∧ s.REG 0w = 1w ∧ svc_frame_rel s s' ∧ s'.MEM = s.MEM ∧
    (s'.REG 0w = -4w ∧ out = [] ∨
     ∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ s'.REG 0w = n2w n ∧
         out = GENLIST (λi. s.MEM (s.REG 1w + n2w i)) n)
```

#### `forge_runtimeSpec.svc_write_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s s' out.
    svc_write_rel s s' out ⇔
    s.REG 8w = 64w ∧ s.REG 0w = 1w ∧ svc_frame_rel s s' ∧ s'.MEM = s.MEM ∧
    (s'.REG 0w = -4w ∧ out = [] ∨
     (∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ s'.REG 0w = n2w n ∧
          out = GENLIST (λi. s.MEM (s.REG 1w + n2w i)) n) ∨
     (s'.REG 0w = 0w ∨ word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w) ∧ out = [])
```

#### `forge_runtimeSpec.untagged_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a. untagged a ⇔ (63 >< 55) a = 0w
```

#### `forge_runtimeSpec.whole_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel inp out s inp' out' s'.
    whole_step rrel wrel (inp,out,s) (inp',out',s') ⇔
    ¬is_svc0_at s ∧ NextStateARM8 s = SOME s' ∧ inp' = inp ∧ out' = out ∨
    is_svc0_at s ∧ s.REG 8w = 63w ∧ rrel inp s s' inp' ∧ out' = out ∨
    is_svc0_at s ∧ s.REG 8w = 64w ∧ ∃chunk. wrel s s' chunk ∧ inp' = inp ∧ out' = out ++ chunk
```

#### `forge_runtimeSpec.words32_in_mem_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀base mem. words32_in_mem base [] mem ⇔ T) ∧
  ∀base w ws mem.
    words32_in_mem base (w::ws) mem ⇔
    mem base = (7 >< 0) w ∧ mem (base + 1w) = (15 >< 8) w ∧ mem (base + 2w) = (23 >< 16) w ∧
    mem (base + 3w) = (31 >< 24) w ∧ words32_in_mem (base + 4w) ws mem
```

</details>

<details>
<summary><strong><code>forge_frame64Spec</code></strong> — Generic 64B Frame ABI (36 definitions, 50 theorems)</summary>

Fixed 64-byte LE64 binary frame bijection, 64-byte chunking, polymorphic trace runner, and total recv64/send64 FFI oracle.

### Definitions

#### `forge_frame64Spec.chunks64_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ chunks64 =
  WFREC (@R. WF R ∧ ∀bs. ¬(LENGTH bs < 64) ⇒ R (DROP 64 bs) bs)
    (λchunks64 a. I (if LENGTH a < 64 then [] else TAKE 64 a::chunks64 (DROP 64 a)))
```

#### `forge_frame64Spec.decode_frame64_io_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f. decode_frame64_io f =
      if ∃io. encode_frame64_io io = f then SOME (@io. encode_frame64_io io = f) else NONE
```

#### `forge_frame64Spec.encode_byte_list64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. encode_byte_list64 bs = List (MAP (Num ∘ w2n) bs)
```

#### `forge_frame64Spec.encode_frame64_io_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io.
    encode_frame64_io io =
    Cons (List (MAP encode_byte_list64 io.inputs))
      (Cons (List (MAP encode_byte_list64 io.outputs)) (encode_opt_num64 io.write_limit))
```

#### `forge_frame64Spec.encode_opt_num64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ encode_opt_num64 NONE = Num 0 ∧ ∀n. encode_opt_num64 (SOME n) = Cons (Num 1) (Num n)
```

#### `forge_frame64Spec.ffi_recv64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_recv64 conf bytes io =
    if LENGTH bytes < 65 then SOME (FFIreturn bytes io)
    else
      case io.inputs of
        [] => SOME (FFIreturn (1w::DROP 1 bytes) io)
      | f::fs =>
        if LENGTH f = 64 then SOME (FFIreturn (0w::f ++ DROP 65 bytes) (io with inputs := fs))
        else SOME (FFIreturn (1w::DROP 1 bytes) io)
```

#### `forge_frame64Spec.ffi_send64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_send64 conf bytes io =
    if LENGTH bytes < 65 then SOME (FFIreturn bytes io)
    else
      (let
         frame = TAKE 64 (DROP 1 bytes)
       in
         case io.write_limit of
           NONE => SOME (FFIreturn (0w::DROP 1 bytes) (io with outputs := io.outputs ++ [frame]))
         | SOME 0 => SOME (FFIreturn (1w::DROP 1 bytes) (io with outputs := io.outputs ++ [frame]))
         | SOME (SUC n) =>
           SOME
             (FFIreturn (0w::DROP 1 bytes)
                (io with <|outputs := io.outputs ++ [frame]; write_limit := SOME n|>)))
```

#### `forge_frame64Spec.frame64_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. frame64_ABS (frame64_REP a) = a) ∧ ∀r. (λx. T) r ⇔ frame64_REP (frame64_ABS r) = r
```

#### `forge_frame64Spec.frame64_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_CONS = frame64_ABS
```

#### `forge_frame64Spec.frame64_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_frame64Spec.frame64_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 f.
    frame64_CASE (Frame64 a0 a1 a2 a3 a4 a5 a6 a7) f = f a0 a1 a2 a3 a4 a5 a6 a7
```

#### `forge_frame64Spec.frame64_decode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs.
    frame64_decode bs =
    Frame64 (le64_at bs 0) (le64_at bs 8) (le64_at bs 16) (le64_at bs 24) (le64_at bs 32)
      (le64_at bs 40) (le64_at bs 48) (le64_at bs 56)
```

#### `forge_frame64Spec.frame64_encode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w0 w1 w2 w3 w4 w5 w6 w7.
    frame64_encode (Frame64 w0 w1 w2 w3 w4 w5 w6 w7) =
    le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++
    le64_encode w5 ++ le64_encode w6 ++ le64_encode w7
```

#### `forge_frame64Spec.frame64_ffi_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. frame64_ffi io = initial_ffi_state frame64_ffi_oracle io
```

#### `forge_frame64Spec.frame64_ffi_oracle_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_ffi_oracle =
  (λname io conf bytes.
     if name = ExtCall «recv64» then
       case ffi_recv64 conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else if name = ExtCall «send64» then
       case ffi_send64 conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else Oracle_final FFI_failed)
```

#### `forge_frame64Spec.frame64_ffi_part_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_ffi_part =
  (encode_frame64_io,decode_frame64_io,[(«recv64»,ffi_recv64); («send64»,ffi_send64)])
```

#### `forge_frame64Spec.frame64_io_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. frame64_io_ABS (frame64_io_REP a) = a) ∧
  ∀r. (λx. T) r ⇔ frame64_io_REP (frame64_io_ABS r) = r
```

#### `forge_frame64Spec.frame64_io_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_io_CONS = frame64_io_ABS
```

#### `forge_frame64Spec.frame64_io_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_frame64Spec.frame64_io_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 f. frame64_io_CASE (frame64_io a0 a1 a2) f = f a0 a1 a2
```

#### `forge_frame64Spec.frame64_io_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2.
    frame64_io_size (frame64_io a0 a1 a2) =
    1 + (list_size (list_size w2n) a0 + (list_size (list_size w2n) a1 + option_size (λx. x) a2))
```

#### `forge_frame64Spec.frame64_proj_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_proj =
  ((λio. FEMPTY |++ [(«recv64»,encode_frame64_io io); («send64»,encode_frame64_io io)]),
   [([«recv64»; «send64»],mk_ffi_next frame64_ffi_part)])
```

#### `forge_frame64Spec.frame64_run_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀ $step st. frame64_run $step st [] = (st,[])) ∧
  ∀ $step st f fs.
    frame64_run $step st (f::fs) =
    if LENGTH f = 64 then
      (let
         (st',resp) = (st step frame64_decode f);
         (stf,outs) = frame64_run $step st' fs
       in
         (stf,frame64_encode resp::outs))
    else (st,[])
```

#### `forge_frame64Spec.frame64_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7.
    frame64_size (Frame64 a0 a1 a2 a3 a4 a5 a6 a7) =
    1 + (w2n a0 + (w2n a1 + (w2n a2 + (w2n a3 + (w2n a4 + (w2n a5 + (w2n a6 + w2n a7)))))))
```

#### `forge_frame64Spec.le64_at_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs off.
    le64_at bs off =
    le64_decode bs❲off❳ bs❲off + 1❳ bs❲off + 2❳ bs❲off + 3❳ bs❲off + 4❳ bs❲off + 5❳ bs❲off + 6❳
      bs❲off + 7❳
```

#### `forge_frame64Spec.le64_byte_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w i. le64_byte w i = w2w (w ⋙ (8 * i))
```

#### `forge_frame64Spec.le64_decode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀b0 b1 b2 b3 b4 b5 b6 b7.
    le64_decode b0 b1 b2 b3 b4 b5 b6 b7 =
    w2w b0 ‖ w2w b1 ≪ 8 ‖ w2w b2 ≪ 16 ‖ w2w b3 ≪ 24 ‖ w2w b4 ≪ 32 ‖ w2w b5 ≪ 40 ‖ w2w b6 ≪ 48 ‖
    w2w b7 ≪ 56
```

#### `forge_frame64Spec.le64_encode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. le64_encode w =
      [le64_byte w 0; le64_byte w 1; le64_byte w 2; le64_byte w 3; le64_byte w 4; le64_byte w 5;
       le64_byte w 6; le64_byte w 7]
```

#### `forge_frame64Spec.limit_frames64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀xs. limit_frames64 NONE xs = xs) ∧ ∀n xs. limit_frames64 (SOME n) xs = TAKE (SUC n) xs
```

#### `forge_frame64Spec.recordtype_frame64_io_seldef_inputs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 $o. (frame64_io l l0 $o).inputs = l
```

#### `forge_frame64Spec.recordtype_frame64_io_seldef_inputs_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 $o. frame64_io l l0 $o with inputs updated_by f = frame64_io (f l) l0 $o
```

#### `forge_frame64Spec.recordtype_frame64_io_seldef_outputs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 $o. (frame64_io l l0 $o).outputs = l0
```

#### `forge_frame64Spec.recordtype_frame64_io_seldef_outputs_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 $o. frame64_io l l0 $o with outputs updated_by f = frame64_io l (f l0) $o
```

#### `forge_frame64Spec.recordtype_frame64_io_seldef_write_limit_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 $o. (frame64_io l l0 $o).write_limit = $o
```

#### `forge_frame64Spec.recordtype_frame64_io_seldef_write_limit_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 $o. frame64_io l l0 $o with write_limit updated_by f = frame64_io l l0 (f $o)
```

#### `forge_frame64Spec.sent_frames64_of_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sent_frames64_of =
  WFREC
    (@R. WF R ∧ (∀bs conf n rest. R rest (IO_event (ExtCall n) conf bs::rest)) ∧
         ∀v4 v3 v9 rest. R rest (IO_event (SharedMem v9) v3 v4::rest))
    (λsent_frames64_of a.
       case a of
         [] => I []
       | IO_event (ExtCall n) conf bs::rest =>
         I
           ((if n = «send64» ∧ 65 ≤ LENGTH bs then [TAKE 64 (DROP 1 (MAP FST bs))] else []) ++
            sent_frames64_of rest)
       | IO_event (SharedMem v11) conf bs::rest => I (sent_frames64_of rest))
```

### Theorems

#### `forge_frame64Spec.EXISTS_frame64_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∃f. P f) ⇔ ∃l0 l $o. P <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_frame64Spec.FORALL_frame64_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀f. P f) ⇔ ∀l0 l $o. P <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_frame64Spec.call_FFI_frame64_outputs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st st'.
    call_FFI_rel st st' ∧ st.oracle = frame64_ffi_oracle ⇒
    st'.oracle = frame64_ffi_oracle ∧
    st'.ffi_state.outputs =
    st.ffi_state.outputs ++ sent_frames64_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
```

#### `forge_frame64Spec.chunks64_cons`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f rest. LENGTH f = 64 ⇒ chunks64 (f ++ rest) = f::chunks64 rest
```

#### `forge_frame64Spec.chunks64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. chunks64 bs = if LENGTH bs < 64 then [] else TAKE 64 bs::chunks64 (DROP 64 bs)
```

#### `forge_frame64Spec.chunks64_every_len64`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. EVERY (λf. LENGTH f = 64) (chunks64 bs)
```

#### `forge_frame64Spec.chunks64_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀bs. (¬(LENGTH bs < 64) ⇒ P (DROP 64 bs)) ⇒ P bs) ⇒ ∀v. P v
```

#### `forge_frame64Spec.chunks64_lt64`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. LENGTH bs < 64 ⇒ chunks64 bs = []
```

#### `forge_frame64Spec.datatype_frame64`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE (frame64 Frame64)
```

#### `forge_frame64Spec.datatype_frame64_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE (record frame64_io inputs outputs write_limit)
```

#### `forge_frame64Spec.decode_encode_frame64_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. decode_frame64_io (encode_frame64_io io) = SOME io
```

#### `forge_frame64Spec.encode_byte_list64_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y. encode_byte_list64 x = encode_byte_list64 y ⇔ x = y
```

#### `forge_frame64Spec.encode_frame64_io_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y. encode_frame64_io x = encode_frame64_io y ⇔ x = y
```

#### `forge_frame64Spec.encode_opt_num64_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y. encode_opt_num64 x = encode_opt_num64 y ⇔ x = y
```

#### `forge_frame64Spec.ffi_recv64_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io bytes' io'.
    ffi_recv64 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes
```

#### `forge_frame64Spec.ffi_send64_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io bytes' io'.
    ffi_send64 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes
```

#### `forge_frame64Spec.frame64_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a0' a1' a2' a3' a4' a5' a6' a7'.
    Frame64 a0 a1 a2 a3 a4 a5 a6 a7 = Frame64 a0' a1' a2' a3' a4' a5' a6' a7' ⇔
    a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3' ∧ a4 = a4' ∧ a5 = a5' ∧ a6 = a6' ∧ a7 = a7'
```

#### `forge_frame64Spec.frame64_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2 a3 a4 a5 a6 a7.
    h (Frame64 a0 a1 a2 a3 a4 a5 a6 a7) = f0 a0 a1 a2 a3 a4 a5 a6 a7
```

#### `forge_frame64Spec.frame64_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧
    (∀a0 a1 a2 a3 a4 a5 a6 a7.
       M' = Frame64 a0 a1 a2 a3 a4 a5 a6 a7 ⇒ f a0 a1 a2 a3 a4 a5 a6 a7 = f' a0 a1 a2 a3 a4 a5 a6 a7) ⇒
    frame64_CASE M f = frame64_CASE M' f'
```

#### `forge_frame64Spec.frame64_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_CASE x f = v ⇔
  ∃c c0 c1 c2 c3 c4 c5 c6. x = Frame64 c c0 c1 c2 c3 c4 c5 c6 ∧ f c c0 c1 c2 c3 c4 c5 c6 = v
```

#### `forge_frame64Spec.frame64_decode_encode_bytes`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. LENGTH bs = 64 ⇒ frame64_encode (frame64_decode bs) = bs
```

#### `forge_frame64Spec.frame64_encode_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fr. LENGTH (frame64_encode fr) = 64
```

#### `forge_frame64Spec.frame64_ffi_outputs_eq_sent_frames`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io st'.
    io.outputs = [] ∧ call_FFI_rel꙳ (frame64_ffi io) st' ⇒
    st'.ffi_state.outputs = sent_frames64_of st'.io_events
```

#### `forge_frame64Spec.frame64_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀c c0 c1 c2 c3 c4 c5 c6. P (Frame64 c c0 c1 c2 c3 c4 c5 c6)) ⇒ ∀f. P f
```

#### `forge_frame64Spec.frame64_io_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a0' a1' a2'.
    frame64_io a0 a1 a2 = frame64_io a0' a1' a2' ⇔ a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
```

#### `forge_frame64Spec.frame64_io_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2. h (frame64_io a0 a1 a2) = f0 a0 a1 a2
```

#### `forge_frame64Spec.frame64_io_accessors`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀l l0 $o. (frame64_io l l0 $o).inputs = l) ∧ (∀l l0 $o. (frame64_io l l0 $o).outputs = l0) ∧
  ∀l l0 $o. (frame64_io l l0 $o).write_limit = $o
```

#### `forge_frame64Spec.frame64_io_accfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f0 f. (f with outputs updated_by f0).inputs = f.inputs) ∧
  (∀f0 f. (f with write_limit updated_by f0).inputs = f.inputs) ∧
  (∀f0 f. (f with inputs updated_by f0).outputs = f.outputs) ∧
  (∀f0 f. (f with write_limit updated_by f0).outputs = f.outputs) ∧
  (∀f0 f. (f with inputs updated_by f0).write_limit = f.write_limit) ∧
  (∀f0 f. (f with outputs updated_by f0).write_limit = f.write_limit) ∧
  (∀f0 f. (f with inputs updated_by f0).inputs = f0 f.inputs) ∧
  (∀f0 f. (f with outputs updated_by f0).outputs = f0 f.outputs) ∧
  ∀f0 f. (f with write_limit updated_by f0).write_limit = f0 f.write_limit
```

#### `forge_frame64Spec.frame64_io_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧ (∀a0 a1 a2. M' = frame64_io a0 a1 a2 ⇒ f a0 a1 a2 = f' a0 a1 a2) ⇒
    frame64_io_CASE M f = frame64_io_CASE M' f'
```

#### `forge_frame64Spec.frame64_io_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_io_CASE x f = v ⇔ ∃l l0 o'. x = frame64_io l l0 o' ∧ f l l0 o' = v
```

#### `forge_frame64Spec.frame64_io_component_equality`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f1 f2.
    f1 = f2 ⇔ f1.inputs = f2.inputs ∧ f1.outputs = f2.outputs ∧ f1.write_limit = f2.write_limit
```

#### `forge_frame64Spec.frame64_io_fn_updates`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f l l0 $o. frame64_io l l0 $o with inputs updated_by f = frame64_io (f l) l0 $o) ∧
  (∀f l l0 $o. frame64_io l l0 $o with outputs updated_by f = frame64_io l (f l0) $o) ∧
  ∀f l l0 $o. frame64_io l l0 $o with write_limit updated_by f = frame64_io l l0 (f $o)
```

#### `forge_frame64Spec.frame64_io_fupdcanon`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g f0 f.
     f with <|outputs updated_by f0; inputs updated_by g|> =
     f with <|inputs updated_by g; outputs updated_by f0|>) ∧
  (∀g f0 f.
     f with <|write_limit updated_by f0; inputs updated_by g|> =
     f with <|inputs updated_by g; write_limit updated_by f0|>) ∧
  ∀g f0 f.
    f with <|write_limit updated_by f0; outputs updated_by g|> =
    f with <|outputs updated_by g; write_limit updated_by f0|>
```

#### `forge_frame64Spec.frame64_io_fupdcanon_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f0. outputs_fupd f0 ∘ inputs_fupd g = inputs_fupd g ∘ outputs_fupd f0) ∧
   ∀h g f0. outputs_fupd f0 ∘ inputs_fupd g ∘ h = inputs_fupd g ∘ outputs_fupd f0 ∘ h) ∧
  ((∀g f0. write_limit_fupd f0 ∘ inputs_fupd g = inputs_fupd g ∘ write_limit_fupd f0) ∧
   ∀h g f0. write_limit_fupd f0 ∘ inputs_fupd g ∘ h = inputs_fupd g ∘ write_limit_fupd f0 ∘ h) ∧
  (∀g f0. write_limit_fupd f0 ∘ outputs_fupd g = outputs_fupd g ∘ write_limit_fupd f0) ∧
  ∀h g f0. write_limit_fupd f0 ∘ outputs_fupd g ∘ h = outputs_fupd g ∘ write_limit_fupd f0 ∘ h
```

#### `forge_frame64Spec.frame64_io_fupdfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g f0 f. f with <|inputs updated_by f0; inputs updated_by g|> = f with inputs updated_by f0 ∘ g) ∧
  (∀g f0 f.
     f with <|outputs updated_by f0; outputs updated_by g|> = f with outputs updated_by f0 ∘ g) ∧
  ∀g f0 f.
    f with <|write_limit updated_by f0; write_limit updated_by g|> =
    f with write_limit updated_by f0 ∘ g
```

#### `forge_frame64Spec.frame64_io_fupdfupds_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f0. inputs_fupd f0 ∘ inputs_fupd g = inputs_fupd (f0 ∘ g)) ∧
   ∀h g f0. inputs_fupd f0 ∘ inputs_fupd g ∘ h = inputs_fupd (f0 ∘ g) ∘ h) ∧
  ((∀g f0. outputs_fupd f0 ∘ outputs_fupd g = outputs_fupd (f0 ∘ g)) ∧
   ∀h g f0. outputs_fupd f0 ∘ outputs_fupd g ∘ h = outputs_fupd (f0 ∘ g) ∘ h) ∧
  (∀g f0. write_limit_fupd f0 ∘ write_limit_fupd g = write_limit_fupd (f0 ∘ g)) ∧
  ∀h g f0. write_limit_fupd f0 ∘ write_limit_fupd g ∘ h = write_limit_fupd (f0 ∘ g) ∘ h
```

#### `forge_frame64Spec.frame64_io_fupdselfid`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f. f with inputs := f.inputs = f) ∧ (∀f. f with outputs := f.outputs = f) ∧
  ∀f. f with write_limit := f.write_limit = f
```

#### `forge_frame64Spec.frame64_io_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀l l0 $o. P (frame64_io l l0 $o)) ⇒ ∀f. P f
```

#### `forge_frame64Spec.frame64_io_literal_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l01 l1 o1 l02 l2 o2.
    <|inputs := l01; outputs := l1; write_limit := o1|> =
    <|inputs := l02; outputs := l2; write_limit := o2|> ⇔ l01 = l02 ∧ l1 = l2 ∧ o1 = o2
```

#### `forge_frame64Spec.frame64_io_literal_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f. ∃l0 l $o. f = <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_frame64Spec.frame64_io_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ff. ∃l l0 $o. ff = frame64_io l l0 $o
```

#### `forge_frame64Spec.frame64_io_updates_eq_literal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l0 l $o.
    f with <|inputs := l0; outputs := l; write_limit := $o|> =
    <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_frame64Spec.frame64_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ff. ∃c c0 c1 c2 c3 c4 c5 c6. ff = Frame64 c c0 c1 c2 c3 c4 c5 c6
```

#### `forge_frame64Spec.frame64_roundtrip`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fr. frame64_decode (frame64_encode fr) = fr
```

#### `forge_frame64Spec.le64_decode_encode_bytes`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀b0 b1 b2 b3 b4 b5 b6 b7.
    le64_encode (le64_decode b0 b1 b2 b3 b4 b5 b6 b7) = [b0; b1; b2; b3; b4; b5; b6; b7]
```

#### `forge_frame64Spec.le64_encode_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. LENGTH (le64_encode w) = 8
```

#### `forge_frame64Spec.le64_roundtrip`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. le64_decode (le64_byte w 0) (le64_byte w 1) (le64_byte w 2) (le64_byte w 3) (le64_byte w 4)
        (le64_byte w 5) (le64_byte w 6) (le64_byte w 7) = w
```

#### `forge_frame64Spec.sent_frames64_of_append`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs ys. sent_frames64_of (xs ++ ys) = sent_frames64_of xs ++ sent_frames64_of ys
```

#### `forge_frame64Spec.sent_frames64_of_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sent_frames64_of [] = [] ∧
  (∀rest n conf bs.
     sent_frames64_of (IO_event (ExtCall n) conf bs::rest) =
     (if n = «send64» ∧ 65 ≤ LENGTH bs then [TAKE 64 (DROP 1 (MAP FST bs))] else []) ++
     sent_frames64_of rest) ∧
  ∀v9 v4 v3 rest. sent_frames64_of (IO_event (SharedMem v9) v3 v4::rest) = sent_frames64_of rest
```

#### `forge_frame64Spec.sent_frames64_of_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. P [] ∧ (∀n conf bs rest. P rest ⇒ P (IO_event (ExtCall n) conf bs::rest)) ∧
      (∀v9 v3 v4 rest. P rest ⇒ P (IO_event (SharedMem v9) v3 v4::rest)) ⇒
      ∀v. P v
```

</details>

<details>
<summary><strong><code>forge_frameRunner</code></strong> — Generic 64B ML Runner (22 definitions, 24 theorems)</summary>

Polymorphic Zero-Basis CakeML 64-byte frame runner (recv64 -> translated step -> send64) for zero-SL kernel synthesis.

### Definitions

#### `forge_frameRunner.FORGE_FRAME64SPEC_FRAME64_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6.
    FORGE_FRAME64SPEC_FRAME64_v (Frame64 c c0 c1 c2 c3 c4 c5 c6) =
    Conv (SOME (TypeStamp «Frame64» 9))
      [WORD_v c; WORD_v c0; WORD_v c1; WORD_v c2; WORD_v c3; WORD_v c4; WORD_v c5; WORD_v c6]
```

#### `forge_frameRunner.FRAME64_IO_EV_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io evs.
    FRAME64_IO_EV io evs =
    one (FFI_part (encode_frame64_io io) (mk_ffi_next frame64_ffi_part) [«recv64»; «send64»] evs)
```

#### `forge_frameRunner.event_is_err64_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ event_is_err64 =
  WFREC (@R. WF R)
    (λevent_is_err64 a.
       case a of
         IO_event (ExtCall n) conf bs => I (65 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w)
       | IO_event (SharedMem v9) conf bs => I F)
```

#### `forge_frameRunner.forge_frameRunner_env_0_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_0 = write «le64_byte» le64_byte_v forge_frameRunner_env
```

#### `forge_frameRunner.forge_frameRunner_env_1_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_1 = write_cons «Frame64» (8,TypeStamp «Frame64» 9) forge_frameRunner_env_0
```

#### `forge_frameRunner.forge_frameRunner_env_2_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_2 = write «read_u64» read_u64_v forge_frameRunner_env_1
```

#### `forge_frameRunner.forge_frameRunner_env_3_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_3 = write «write_u64» write_u64_v forge_frameRunner_env_2
```

#### `forge_frameRunner.forge_frameRunner_env_4_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_4 = write «read_frame64» read_frame64_v forge_frameRunner_env_3
```

#### `forge_frameRunner.forge_frameRunner_env_5_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_5 = write «write_frame64» write_frame64_v forge_frameRunner_env_4
```

#### `forge_frameRunner.forge_frameRunner_env_6_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_6 = write «frame64_loop» frame64_loop_v forge_frameRunner_env_5
```

#### `forge_frameRunner.forge_frameRunner_env_7_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env_7 = write «run_frame64_kernel» run_frame64_kernel_v forge_frameRunner_env_6
```

#### `forge_frameRunner.forge_frameRunner_env_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_frameRunner_env = write «le64_decode» le64_decode_v Word8ArrayProg_env_13
```

#### `forge_frameRunner.forge_frameRunner_st_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi po.
    forge_frameRunner_st (ffi,po) =
    <|clock := 0; refs := []; ffi := ffi; next_type_stamp := 10; next_exn_stamp := 5;
      eval_state := NONE; ptr_eq_oracle := some_chars_vector_po po|>
```

#### `forge_frameRunner.frame64_loop_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame64_loop_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_frameRunner.le64_byte_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ le64_byte_v =
  Closure (merge_env forge_frameRunner_env init_env) «v2»
    (Fun «v1»
       (App (Arith (Shift Lsl) (WordT W8))
          [App (FromTo IntT (WordT W8))
             [App (FromTo (WordT W64) IntT)
                [App (Arith (Shift Lsr) (WordT W64))
                   [App (Arith (Shift Lsr) (WordT W64))
                      [Var (Short «v2»);
                       App (FromTo IntT (WordT W64))
                         [If
                            (App (Test (Compare Lt) IntT)
                               [App (Arith Mul IntT) [Lit (IntLit 8); Var (Short «v1»)];
                                Lit (IntLit 64)])
                            (App (Arith Mul IntT) [Lit (IntLit 8); Var (Short «v1»)])
                            (Lit (IntLit 64))]]; Lit (Word64 0w)]]]; Lit (Word8 0w)]))
```

#### `forge_frameRunner.le64_decode_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ le64_decode_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_frameRunner.read_frame64_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ read_frame64_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_frameRunner.read_u64_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ read_u64_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_frameRunner.run_frame64_kernel_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ run_frame64_kernel_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_frameRunner.stop_after_err64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (stop_after_err64 [] ⇔ T) ∧
  ∀e es. stop_after_err64 (e::es) ⇔ if event_is_err64 e then es = [] else stop_after_err64 es
```

#### `forge_frameRunner.write_frame64_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ write_frame64_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_frameRunner.write_u64_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ write_u64_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

### Theorems

#### `forge_frameRunner.FORGE_FRAME64SPEC_FRAME64_TYPE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x_8_x1_1_ x_7_x1_2_ x_6_x1_3_ x_5_x1_4_ x_4_x1_5_ x_3_x1_6_ x_2_x1_7_ x_1_x1_8_ v.
    FORGE_FRAME64SPEC_FRAME64_TYPE
      (Frame64 x_8_x1_1_ x_7_x1_2_ x_6_x1_3_ x_5_x1_4_ x_4_x1_5_ x_3_x1_6_ x_2_x1_7_ x_1_x1_8_) v ⇔
    ∃v1_1 v1_2 v1_3 v1_4 v1_5 v1_6 v1_7 v1_8.
      v = Conv (SOME (TypeStamp «Frame64» 9)) [v1_1; v1_2; v1_3; v1_4; v1_5; v1_6; v1_7; v1_8] ∧
      WORD x_8_x1_1_ v1_1 ∧ WORD x_7_x1_2_ v1_2 ∧ WORD x_6_x1_3_ v1_3 ∧ WORD x_5_x1_4_ v1_4 ∧
      WORD x_4_x1_5_ v1_5 ∧ WORD x_3_x1_6_ v1_6 ∧ WORD x_2_x1_7_ v1_7 ∧ WORD x_1_x1_8_ v1_8
```

#### `forge_frameRunner.event_is_err64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (event_is_err64 (IO_event (ExtCall n) conf bs) ⇔ 65 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w) ∧
  (event_is_err64 (IO_event (SharedMem v7) v1 v2) ⇔ F)
```

#### `forge_frameRunner.event_is_err64_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀n conf bs. P (IO_event (ExtCall n) conf bs)) ∧
      (∀v7 v1 v2. P (IO_event (SharedMem v7) v1 v2)) ⇒
      ∀v. P v
```

#### `forge_frameRunner.frame64_io_ffi_part_hprop`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀out.
    FFI_part_hprop
      (SEP_EXISTS rest_inps wlim' evs'.
         &stop_after_err64 evs' *
         FRAME64_IO_EV <|inputs := rest_inps; outputs := out; write_limit := wlim'|> evs')
```

#### `forge_frameRunner.frame64_io_split`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st2 io.
    st2.ffi = frame64_ffi io ⇒
    ∃h1 h2. SPLIT (st2heap frame64_proj st2) (h1,h2) ∧ FRAME64_IO_EV io [] h1
```

#### `forge_frameRunner.frame64_loop_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ST $step stepv inps outs wlim evs bufv bs state statev.
    (ST --> FORGE_FRAME64SPEC_FRAME64_TYPE --> PAIR_TYPE ST FORGE_FRAME64SPEC_FRAME64_TYPE) $step
      stepv ∧ ST state statev ∧ LENGTH bs = 65 ∧ EVERY ($¬ ∘ event_is_err64) evs ⇒
    app p frame64_loop_v [stepv; bufv; statev]
      (W8ARRAY bufv bs * FRAME64_IO_EV <|inputs := inps; outputs := outs; write_limit := wlim|> evs)
      (POSTv uv.
         &UNIT_TYPE () uv *
         SEP_EXISTS bs' rest_inps wlim' evs'.
           W8ARRAY bufv bs' * &stop_after_err64 evs' *
           FRAME64_IO_EV
             <|inputs := rest_inps;
               outputs := outs ++ limit_frames64 wlim (SND (frame64_run $step state inps));
               write_limit := wlim'|> evs')
```

#### `forge_frameRunner.frame64_parts_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. parts_ok (frame64_ffi io) frame64_proj
```

#### `forge_frameRunner.le64_byte_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> NUM --> WORD8) le64_byte le64_byte_v
```

#### `forge_frameRunner.le64_decode_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD) le64_decode
    le64_decode_v
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_0_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_0.c = nsLookup_Mod1 forge_frameRunner_env.c ∧
  nsLookup_Mod1 forge_frameRunner_env_0.v = nsLookup_Mod1 forge_frameRunner_env.v ∧
  nsLookup_Short forge_frameRunner_env_0.c = nsLookup_Short forge_frameRunner_env.c ∧
  nsLookup_Short forge_frameRunner_env_0.v =
  option_choice_f (ALOOKUP [(«le64_byte»,le64_byte_v)]) (nsLookup_Short forge_frameRunner_env.v)
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_1_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_1.c = nsLookup_Mod1 forge_frameRunner_env_0.c ∧
  nsLookup_Mod1 forge_frameRunner_env_1.v = nsLookup_Mod1 forge_frameRunner_env_0.v ∧
  nsLookup_Short forge_frameRunner_env_1.c =
  option_choice_f (ALOOKUP [(«Frame64»,8,TypeStamp «Frame64» 9)])
    (nsLookup_Short forge_frameRunner_env_0.c) ∧
  nsLookup_Short forge_frameRunner_env_1.v = nsLookup_Short forge_frameRunner_env_0.v
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_2_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_2.c = nsLookup_Mod1 forge_frameRunner_env_1.c ∧
  nsLookup_Mod1 forge_frameRunner_env_2.v = nsLookup_Mod1 forge_frameRunner_env_1.v ∧
  nsLookup_Short forge_frameRunner_env_2.c = nsLookup_Short forge_frameRunner_env_1.c ∧
  nsLookup_Short forge_frameRunner_env_2.v =
  option_choice_f (ALOOKUP [(«read_u64»,read_u64_v)]) (nsLookup_Short forge_frameRunner_env_1.v)
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_3_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_3.c = nsLookup_Mod1 forge_frameRunner_env_2.c ∧
  nsLookup_Mod1 forge_frameRunner_env_3.v = nsLookup_Mod1 forge_frameRunner_env_2.v ∧
  nsLookup_Short forge_frameRunner_env_3.c = nsLookup_Short forge_frameRunner_env_2.c ∧
  nsLookup_Short forge_frameRunner_env_3.v =
  option_choice_f (ALOOKUP [(«write_u64»,write_u64_v)]) (nsLookup_Short forge_frameRunner_env_2.v)
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_4_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_4.c = nsLookup_Mod1 forge_frameRunner_env_3.c ∧
  nsLookup_Mod1 forge_frameRunner_env_4.v = nsLookup_Mod1 forge_frameRunner_env_3.v ∧
  nsLookup_Short forge_frameRunner_env_4.c = nsLookup_Short forge_frameRunner_env_3.c ∧
  nsLookup_Short forge_frameRunner_env_4.v =
  option_choice_f (ALOOKUP [(«read_frame64»,read_frame64_v)])
    (nsLookup_Short forge_frameRunner_env_3.v)
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_5_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_5.c = nsLookup_Mod1 forge_frameRunner_env_4.c ∧
  nsLookup_Mod1 forge_frameRunner_env_5.v = nsLookup_Mod1 forge_frameRunner_env_4.v ∧
  nsLookup_Short forge_frameRunner_env_5.c = nsLookup_Short forge_frameRunner_env_4.c ∧
  nsLookup_Short forge_frameRunner_env_5.v =
  option_choice_f (ALOOKUP [(«write_frame64»,write_frame64_v)])
    (nsLookup_Short forge_frameRunner_env_4.v)
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_6_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_6.c = nsLookup_Mod1 forge_frameRunner_env_5.c ∧
  nsLookup_Mod1 forge_frameRunner_env_6.v = nsLookup_Mod1 forge_frameRunner_env_5.v ∧
  nsLookup_Short forge_frameRunner_env_6.c = nsLookup_Short forge_frameRunner_env_5.c ∧
  nsLookup_Short forge_frameRunner_env_6.v =
  option_choice_f (ALOOKUP [(«frame64_loop»,frame64_loop_v)])
    (nsLookup_Short forge_frameRunner_env_5.v)
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_7_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env_7.c = nsLookup_Mod1 forge_frameRunner_env_6.c ∧
  nsLookup_Mod1 forge_frameRunner_env_7.v = nsLookup_Mod1 forge_frameRunner_env_6.v ∧
  nsLookup_Short forge_frameRunner_env_7.c = nsLookup_Short forge_frameRunner_env_6.c ∧
  nsLookup_Short forge_frameRunner_env_7.v =
  option_choice_f (ALOOKUP [(«run_frame64_kernel»,run_frame64_kernel_v)])
    (nsLookup_Short forge_frameRunner_env_6.v)
```

#### `forge_frameRunner.nsLookup_forge_frameRunner_env_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_frameRunner_env.c = nsLookup_Mod1 Word8ArrayProg_env_13.c ∧
  nsLookup_Mod1 forge_frameRunner_env.v = nsLookup_Mod1 Word8ArrayProg_env_13.v ∧
  nsLookup_Short forge_frameRunner_env.c = nsLookup_Short Word8ArrayProg_env_13.c ∧
  nsLookup_Short forge_frameRunner_env.v =
  option_choice_f (ALOOKUP [(«le64_decode»,le64_decode_v)]) (nsLookup_Short Word8ArrayProg_env_13.v)
```

#### `forge_frameRunner.read_frame64_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀av b0 h.
    LENGTH h = 64 ⇒
    app p read_frame64_v [av] (W8ARRAY av (b0::h))
      (POSTv frv. &FORGE_FRAME64SPEC_FRAME64_TYPE (frame64_decode h) frv * W8ARRAY av (b0::h))
```

#### `forge_frameRunner.read_u64_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀av bs off offv.
    NUM off offv ∧ off + 8 ≤ LENGTH bs ⇒
    app p read_u64_v [av; offv] (W8ARRAY av bs)
      (POSTv wv. &WORD (le64_at bs off) wv * W8ARRAY av bs)
```

#### `forge_frameRunner.run_frame64_kernel_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ST $step stepv init_state init_statev inps wlim.
    (ST --> FORGE_FRAME64SPEC_FRAME64_TYPE --> PAIR_TYPE ST FORGE_FRAME64SPEC_FRAME64_TYPE) $step
      stepv ∧ ST init_state init_statev ⇒
    app p run_frame64_kernel_v [stepv; init_statev]
      (FRAME64_IO_EV <|inputs := inps; outputs := []; write_limit := wlim|> [])
      (POSTv rv.
         &UNIT_TYPE () rv *
         SEP_EXISTS rest_inps wlim' evs'.
           &stop_after_err64 evs' *
           FRAME64_IO_EV
             <|inputs := rest_inps;
               outputs := limit_frames64 wlim (SND (frame64_run $step init_state inps));
               write_limit := wlim'|> evs')
```

#### `forge_frameRunner.stop_after_err64_snoc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀es e. EVERY ($¬ ∘ event_is_err64) es ⇒ stop_after_err64 (es ++ [e])
```

#### `forge_frameRunner.write_frame64_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀av bs fr frv.
    LENGTH bs = 65 ∧ FORGE_FRAME64SPEC_FRAME64_TYPE fr frv ⇒
    app p write_frame64_v [av; frv] (W8ARRAY av bs)
      (POSTv uv. &UNIT_TYPE () uv * W8ARRAY av (HD bs::frame64_encode fr))
```

#### `forge_frameRunner.write_u64_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀av bs off offv w wv.
    NUM off offv ∧ WORD w wv ∧ off + 8 ≤ LENGTH bs ⇒
    app p write_u64_v [av; offv; wv] (W8ARRAY av bs)
      (POSTv uv. &UNIT_TYPE () uv * W8ARRAY av (TAKE off bs ++ le64_encode w ++ DROP (off + 8) bs))
```

</details>

<details>
<summary><strong><code>forge_arm8Erasure</code></strong> — ARMv8 Erasure & No-SVC0 (4 definitions, 51 theorems)</summary>

Exact ARMv8 step equivalence under real EL0 bits (TBI0/TBI1/SA0) and proof that compiled code never emits svc #0.

### Definitions

#### `forge_arm8Erasure.arm8_target_exact_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀check_sp.
    arm8_target_exact check_sp =
    arm8_target with
    <|next := Next; state_ok := (λms. arm8_ok ms ∧ (¬check_sp ∨ aligned 4 ms.SP_EL0));
      proj := (λd ms. (arm8_proj d ms,ms.SP_EL0))|>
```

#### `forge_arm8Erasure.erase_e0e_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. erase_e0e s = erase s with SCTLR_EL1 := (erase s).SCTLR_EL1 with E0E := F
```

#### `forge_arm8Erasure.erase_mc_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B mc.
    erase_mc B mc =
    mc with
    <|target := arm8_target_exact (SND (SND B));
      ffi_interfer := (λk (i,bs,s). erase (mc.ffi_interfer k (i,bs,restore B s)));
      install_interfer := (λk (bs,s). erase (mc.install_interfer k (bs,restore B s)))|>
```

#### `forge_arm8Erasure.tbi_pc_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀tcr t.
    tbi_pc tcr t =
    (let
       s0 = if word_bit 55 t ∧ tcr.TBI1 then bit_field_insert 63 56 255w t else t
     in
       if ¬word_bit 55 s0 ∧ tcr.TBI0 then bit_field_insert 63 56 0w s0 else s0)
```

### Theorems

#### `forge_arm8Erasure.BigEndian_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. BigEndian (erase s) ⇔ BigEndian s
```

#### `forge_arm8Erasure.BranchTo_EL0_pc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s t bt.
    s.PSTATE.EL = 0w ⇒
    BranchTo (t,bt) s = s with <|branch_hint := SOME bt; PC := tbi_pc s.TCR_EL1 t|>
```

#### `forge_arm8Erasure.BranchTo_erase_untagged`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s t bt. s.PSTATE.EL = 0w ∧ untagged t ⇒ BranchTo (t,bt) (erase s) = erase (BranchTo (t,bt) s)
```

#### `forge_arm8Erasure.CheckAlignment_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x s. CheckAlignment x (erase s) = erase (CheckAlignment x s)
```

#### `forge_arm8Erasure.CheckAlignment_frame_EL`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x s. (CheckAlignment x s).PSTATE.EL = s.PSTATE.EL
```

#### `forge_arm8Erasure.CheckSPAlignment_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. sp_ok s ⇒ CheckSPAlignment (erase s) = erase (CheckSPAlignment s)
```

#### `forge_arm8Erasure.CheckSPAlignment_erase_fault`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. s.PSTATE.EL = 0w ∧ s.exception = NoException ⇒
      CheckSPAlignment (erase s) = erase s ∧
      (CheckSPAlignment s = s ∨
       s.SCTLR_EL1.SA0 ∧ ¬aligned 4 s.SP_EL0 ∧
       CheckSPAlignment s = s with exception := ALIGNMENT_FAULT)
```

#### `forge_arm8Erasure.FOR_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀i j a.
    (∀k s. SND (a k (erase s)) = erase (SND (a k s))) ⇒
    ∀s. SND (FOR (i,j,a) (erase s)) = erase (SND (FOR (i,j,a) s))
```

#### `forge_arm8Erasure.FOR_erase_pair`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀i j a.
    (∀k x s.
       FST (SND (a k (x,erase s))) = FST (SND (a k (x,s))) ∧
       SND (SND (a k (x,erase s))) = erase (SND (SND (a k (x,s))))) ⇒
    ∀x s.
      FST (SND (FOR (i,j,a) (x,erase s))) = FST (SND (FOR (i,j,a) (x,s))) ∧
      SND (SND (FOR (i,j,a) (x,erase s))) = erase (SND (SND (FOR (i,j,a) (x,s))))
```

#### `forge_arm8Erasure.FOR_proj`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀p i j a. (∀k s. p (SND (a k s)) = p s) ⇒ ∀s. p (SND (FOR (i,j,a) s)) = p s
```

#### `forge_arm8Erasure.FOR_snd_const`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀i j a. (∀k x. SND (SND (a k x)) = SND x) ⇒ ∀x. SND (SND (FOR (i,j,a) x)) = SND x
```

#### `forge_arm8Erasure.Fetch_arm8_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s w.
    arm8_ok s ∧ s.MEM s.PC = (7 >< 0) w ∧ s.MEM (s.PC + 1w) = (15 >< 8) w ∧
    s.MEM (s.PC + 2w) = (23 >< 16) w ∧ s.MEM (s.PC + 3w) = (31 >< 24) w ⇒
    Fetch (s with branch_hint := NONE) = (w,s with branch_hint := NONE)
```

#### `forge_arm8Erasure.Fetch_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. FST (Fetch (erase s)) = FST (Fetch s) ∧ SND (Fetch (erase s)) = erase (SND (Fetch s))
```

#### `forge_arm8Erasure.Mem_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x s. FST (Mem x (erase s)) = FST (Mem x s) ∧ SND (Mem x (erase s)) = erase (SND (Mem x s))
```

#### `forge_arm8Erasure.Mem_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a n acc s. SND (Mem (a,n,acc) s) = CheckAlignment (a,n,acc,F) s
```

#### `forge_arm8Erasure.N1a_tagged_branch_breaks`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. s.PSTATE.EL = 0w ∧ s.TCR_EL1.TBI0 ⇒
      BranchTo (0x100000000001000w,BranchType_JMP) (erase s) ≠
      erase (BranchTo (0x100000000001000w,BranchType_JMP) s)
```

#### `forge_arm8Erasure.N1b_bit55_branch_breaks`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. s.PSTATE.EL = 0w ∧ s.TCR_EL1.TBI1 ⇒
      BranchTo (0x80000000001000w,BranchType_JMP) (erase s) ≠
      erase (BranchTo (0x80000000001000w,BranchType_JMP) s)
```

#### `forge_arm8Erasure.N2_misaligned_sp_breaks`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. s.PSTATE.EL = 0w ∧ s.exception = NoException ∧ s.SCTLR_EL1.SA0 ∧ s.SP_EL0 = 8w ⇒
      (CheckSPAlignment (erase s)).exception = NoException ∧
      (CheckSPAlignment s).exception = ALIGNMENT_FAULT
```

#### `forge_arm8Erasure.N3_e0e_not_erasable`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. s.PSTATE.EL = 0w ∧ s.SCTLR_EL1.E0E ⇒ (BigEndian (erase_e0e s) ⇎ BigEndian s)
```

#### `forge_arm8Erasure.NextStateARM8_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. sp_ok s ∧ (∀t. NextStateARM8 (erase s) = SOME t ⇒ untagged t.PC) ⇒
      OPTION_MAP erase (NextStateARM8 s) = NextStateARM8 (erase s)
```

#### `forge_arm8Erasure.NextStateARM8_frame`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s t.
    NextStateARM8 s = SOME t ⇒
    t.TCR_EL1 = s.TCR_EL1 ∧ t.SCTLR_EL1 = s.SCTLR_EL1 ∧ t.PSTATE.EL = s.PSTATE.EL
```

#### `forge_arm8Erasure.NextStateARM8_restore`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s t.
    sp_ok s ∧ NextStateARM8 (erase s) = SOME t ∧ untagged t.PC ⇒
    NextStateARM8 s = SOME (restore (bits_of s) t)
```

#### `forge_arm8Erasure.Next_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. sp_ok s ∧ untagged (Next (erase s)).PC ⇒ Next (erase s) = erase (Next s)
```

#### `forge_arm8Erasure.Next_exception_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. sp_ok s ⇒ (Next (erase s)).exception = (Next s).exception
```

#### `forge_arm8Erasure.Next_frame`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. (Next s).TCR_EL1 = s.TCR_EL1 ∧ (Next s).SCTLR_EL1 = s.SCTLR_EL1 ∧
      (Next s).PSTATE.EL = s.PSTATE.EL
```

#### `forge_arm8Erasure.P1_bit55_without_TBI1_is_fine`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s bt.
    s.PSTATE.EL = 0w ∧ ¬s.TCR_EL1.TBI1 ⇒
    BranchTo (0x80000000001000w,bt) (erase s) = erase (BranchTo (0x80000000001000w,bt) s)
```

#### `forge_arm8Erasure.Run_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ins s. sp_ok s ∧ untagged (Run ins (erase s)).PC ⇒ Run ins (erase s) = erase (Run ins s)
```

#### `forge_arm8Erasure.Run_exception_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ins s. sp_ok s ⇒ (Run ins (erase s)).exception = (Run ins s).exception
```

#### `forge_arm8Erasure.Run_nonbranch_hint`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ins s. sp_ok s ∧ ¬IS_SOME (Run ins (erase s)).branch_hint ⇒ Run ins (erase s) = erase (Run ins s)
```

#### `forge_arm8Erasure.SCTLR_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. ((SCTLR (erase s)).A ⇔ (SCTLR s).A) ∧ ((SCTLR (erase s)).SA ⇔ (SCTLR s).SA) ∧
      ((SCTLR (erase s)).EE ⇔ (SCTLR s).EE) ∧ ((SCTLR (erase s)).E0E ⇔ (SCTLR s).E0E)
```

#### `forge_arm8Erasure.W_linux_bits_nonvacuous`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃s t.
    arm8_ok (erase s) ∧ s.TCR_EL1.TBI0 ∧ ¬s.TCR_EL1.TBI1 ∧ s.SCTLR_EL1.SA0 ∧ aligned 4 s.SP_EL0 ∧
    untagged t ∧ s.PSTATE.EL = 0w
```

#### `forge_arm8Erasure.arm8_ok_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ⇔
      s.PSTATE.EL = 0w ∧ ¬s.SCTLR_EL1.E0E ∧ s.exception = NoException ∧ aligned 2 s.PC
```

#### `forge_arm8Erasure.arm8_target_exact_encoder_correct`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀check_sp. encoder_correct (arm8_target_exact check_sp)
```

#### `forge_arm8Erasure.arm8_target_exact_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀check_sp. target_ok (arm8_target_exact check_sp)
```

#### `forge_arm8Erasure.bits_of_restore`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B s. bits_of (restore B s) = B
```

#### `forge_arm8Erasure.encoded_bytes_in_mem_not_svc0`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s dm. encoded_bytes_in_mem arm8_config s.PC s.MEM dm ⇒ ¬is_svc0_at s
```

#### `forge_arm8Erasure.erase_fields`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. (erase s).PC = s.PC ∧ (erase s).REG = s.REG ∧ (erase s).MEM = s.MEM ∧
      (erase s).SP_EL0 = s.SP_EL0 ∧ (erase s).PSTATE = s.PSTATE ∧
      (erase s).exception = s.exception ∧ (erase s).branch_hint = s.branch_hint ∧
      ((erase s).SCTLR_EL1.A ⇔ s.SCTLR_EL1.A) ∧ ((erase s).SCTLR_EL1.E0E ⇔ s.SCTLR_EL1.E0E) ∧
      ((erase s).SCTLR_EL1.EE ⇔ s.SCTLR_EL1.EE) ∧ ((erase s).SCTLR_EL1.SA ⇔ s.SCTLR_EL1.SA) ∧
      ¬(erase s).TCR_EL1.TBI0 ∧ ¬(erase s).TCR_EL1.TBI1 ∧ ¬(erase s).SCTLR_EL1.SA0
```

#### `forge_arm8Erasure.erase_idem`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. erase (erase s) = erase s
```

#### `forge_arm8Erasure.erase_reads_all`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. (erase s).MEM = s.MEM ∧ (erase s).PC = s.PC ∧ (erase s).PSTATE = s.PSTATE ∧
      (erase s).REG = s.REG ∧ (erase s).SCTLR_EL2 = s.SCTLR_EL2 ∧
      (erase s).SCTLR_EL3 = s.SCTLR_EL3 ∧ (erase s).SP_EL0 = s.SP_EL0 ∧
      (erase s).SP_EL1 = s.SP_EL1 ∧ (erase s).SP_EL2 = s.SP_EL2 ∧ (erase s).SP_EL3 = s.SP_EL3 ∧
      (erase s).TCR_EL2 = s.TCR_EL2 ∧ (erase s).TCR_EL3 = s.TCR_EL3 ∧
      (erase s).branch_hint = s.branch_hint ∧ (erase s).exception = s.exception
```

#### `forge_arm8Erasure.erase_restore`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B s. erase (restore B s) = erase s
```

#### `forge_arm8Erasure.erase_upds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g s. erase s with MEM updated_by g = erase (s with MEM updated_by g)) ∧
  (∀g s. erase s with PC updated_by g = erase (s with PC updated_by g)) ∧
  (∀g s. erase s with PSTATE updated_by g = erase (s with PSTATE updated_by g)) ∧
  (∀g s. erase s with REG updated_by g = erase (s with REG updated_by g)) ∧
  (∀g s. erase s with SCTLR_EL2 updated_by g = erase (s with SCTLR_EL2 updated_by g)) ∧
  (∀g s. erase s with SCTLR_EL3 updated_by g = erase (s with SCTLR_EL3 updated_by g)) ∧
  (∀g s. erase s with SP_EL0 updated_by g = erase (s with SP_EL0 updated_by g)) ∧
  (∀g s. erase s with SP_EL1 updated_by g = erase (s with SP_EL1 updated_by g)) ∧
  (∀g s. erase s with SP_EL2 updated_by g = erase (s with SP_EL2 updated_by g)) ∧
  (∀g s. erase s with SP_EL3 updated_by g = erase (s with SP_EL3 updated_by g)) ∧
  (∀g s. erase s with TCR_EL2 updated_by g = erase (s with TCR_EL2 updated_by g)) ∧
  (∀g s. erase s with TCR_EL3 updated_by g = erase (s with TCR_EL3 updated_by g)) ∧
  (∀g s. erase s with branch_hint updated_by g = erase (s with branch_hint updated_by g)) ∧
  ∀g s. erase s with exception updated_by g = erase (s with exception updated_by g)
```

#### `forge_arm8Erasure.machine_sem_real_eq_exact`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀mc B ffi ms.
    mc.mmio_info = [] ∧ mc.next_interfer = K I ∧ lo55 mc ∧ bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    (∀k i bs s.
       bits_of s = B ⇒
       bits_of (mc.ffi_interfer k (i,bs,s)) = B ∧ (mc.ffi_interfer k (i,bs,s)).SP_EL0 = s.SP_EL0) ∧
    (∀k bs s.
       bits_of s = B ⇒
       bits_of (mc.install_interfer k (bs,s)) = B ∧ (mc.install_interfer k (bs,s)).SP_EL0 = s.SP_EL0) ∧
    ¬machine_sem (erase_mc B mc) ffi (erase ms) Fail ⇒
    machine_sem (real_mc B mc) ffi ms = machine_sem (erase_mc B mc) ffi (erase ms)
```

#### `forge_arm8Erasure.real_mc_evaluate_exact_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k mc B ffi ms.
    mc.mmio_info = [] ∧ mc.next_interfer = K I ∧ lo55 mc ∧ bits_of ms = B ∧
    (¬SND (SND B) ∨ aligned 4 ms.SP_EL0) ∧
    (∀k i bs s.
       bits_of s = B ⇒
       bits_of (mc.ffi_interfer k (i,bs,s)) = B ∧ (mc.ffi_interfer k (i,bs,s)).SP_EL0 = s.SP_EL0) ∧
    (∀k bs s.
       bits_of s = B ⇒
       bits_of (mc.install_interfer k (bs,s)) = B ∧ (mc.install_interfer k (bs,s)).SP_EL0 = s.SP_EL0) ∧
    (∀j. FST (evaluate (erase_mc B mc) ffi j (erase ms)) ≠ Error) ⇒
    (let
       (res,ms',ffi') = evaluate (erase_mc B mc) ffi k (erase ms)
     in
       ∃rms'.
         evaluate (real_mc B mc) ffi k ms = (res,rms',ffi') ∧ erase rms' = ms' ∧ bits_of rms' = B ∧
         (¬SND (SND B) ∨ aligned 4 rms'.SP_EL0))
```

#### `forge_arm8Erasure.restore_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B s. bits_of s = B ⇒ restore B (erase s) = s
```

#### `forge_arm8Erasure.sp_ok_Fetch`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. sp_ok (SND (Fetch s)) ⇔ sp_ok s
```

#### `forge_arm8Erasure.tbi_pc_erase_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s t. tbi_pc (erase s).TCR_EL1 t = t
```

#### `forge_arm8Erasure.tbi_pc_erased`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀tcr t. tbi_pc (tcr with <|TBI0 := F; TBI1 := F|>) t = t
```

#### `forge_arm8Erasure.tbi_pc_untagged`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀tcr t. untagged t ⇒ tbi_pc tcr t = t
```

#### `forge_arm8Erasure.untagged_bits`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀t. untagged t ⇒ ¬word_bit 55 t ∧ bit_field_insert 63 56 0w t = t
```

#### `forge_arm8Erasure.word2_cases`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. w = 0w ∨ w = 1w ∨ w = 2w ∨ w = 3w
```

#### `forge_arm8Erasure.write_Mem_erase`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x s. write'Mem x (erase s) = erase (write'Mem x s)
```

</details>

<details>
<summary><strong><code>forge_shimProof</code></strong> — Frozen 256KB Shim Proof (6 definitions, 50 theorems)</summary>

Parameterized 43-step ELF startup proof (_start=0x450000) for any <=256KB code blob plus universal 16B & 64B Linux syscall safety and liveness.

### Definitions

#### `forge_shimProof.det_run_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀s s'. det_run 0 s s' ⇔ s' = s) ∧
  ∀k s s'. det_run (SUC k) s s' ⇔ ∃s1. ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ∧ det_run k s1 s'
```

#### `forge_shimProof.ffi_return_ok_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end new_bytes s s'.
    ffi_return_ok_slot shim_ws cb_begin cb_end bm_buf_end new_bytes s s' ⇔
    arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s'.MEM ∧ s'.PC = s.REG 30w ∧
    (∀a. a ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒
         s'.MEM a = asm_write_bytearray (s.REG 2w) new_bytes s.MEM a) ∧
    ∀r. MEM r [19; 20; 21; 22; 23; 24; 25; 26; 27; 28] ⇒ s'.REG (n2w r) = s.REG (n2w r)
```

#### `forge_shimProof.forge_canonical_ffi_post_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀new_bytes s.
    forge_canonical_ffi_post new_bytes s =
    s with <|PC := s.REG 30w; MEM := asm_write_bytearray (s.REG 2w) new_bytes s.MEM|>
```

#### `forge_shimProof.forge_real_install_if_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k bytes s.
    forge_real_install_if k (bytes,s) =
    s with
    <|PC := s.REG 30w; REG := s.REG⦇0w ↦ s.REG 2w⦈;
      MEM := asm_write_bytearray (s.REG 2w) bytes s.MEM|>
```

#### `forge_shimProof.mk_real_ffi_if_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end P k index new_bytes s.
    mk_real_ffi_if_slot shim_ws cb_begin cb_end bm_buf_end P k (index,new_bytes,s) =
    if
      ∃s'.
        P k index new_bytes s s' ∧
        ffi_return_ok_slot shim_ws cb_begin cb_end bm_buf_end new_bytes s s'
    then
      @s'.
        P k index new_bytes s s' ∧
        ffi_return_ok_slot shim_ws cb_begin cb_end bm_buf_end new_bytes s s'
    else forge_canonical_ffi_post new_bytes s
```

#### `forge_shimProof.shim_common_words_ok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws.
    shim_common_words_ok shim_ws ⇔
    LENGTH shim_ws = 80 ∧ TAKE 16 shim_ws = TAKE 16 forge_shim16_words ∧
    DROP 71 shim_ws = DROP 71 forge_shim16_words
```

### Theorems

#### `forge_shimProof.asm_write_bytearray_append`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs ys p m.
    asm_write_bytearray p (xs ++ ys) m =
    asm_write_bytearray p xs (asm_write_bytearray (p + n2w (LENGTH xs)) ys m)
```

#### `forge_shimProof.asm_write_bytearray_drop1`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀p dm m bs b0.
    1 ≤ LENGTH bs ∧ read_bytearray p (LENGTH bs) (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p (b0::DROP 1 bs) m = m⦇p ↦ b0⦈
```

#### `forge_shimProof.asm_write_bytearray_drop_np1`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀N p dm m bs f.
    N + 1 ≤ LENGTH bs ∧ LENGTH f = N ∧
    read_bytearray p (LENGTH bs) (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p (0w::f ++ DROP (N + 1) bs) m = (asm_write_bytearray (p + 1w) f m)⦇p ↦ 0w⦈
```

#### `forge_shimProof.asm_write_bytearray_id`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀n p dm m bs.
    read_bytearray p n (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p bs m = m
```

#### `forge_shimProof.asm_write_bytearray_read_el`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs p m i.
    LENGTH xs < dimword (:64) ∧ i < LENGTH xs ⇒ asm_write_bytearray p xs m (p + n2w i) = xs❲i❳
```

#### `forge_shimProof.asm_write_bytearray_unchanged_lt`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs p a m. (∀i. i < LENGTH xs ⇒ a ≠ p + n2w i) ⇒ asm_write_bytearray p xs m a = m a
```

#### `forge_shimProof.cake_exit_to_svc_exit_group_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_EXIT_VENEER ⇒
    ∃k. (let
           s1 = FUNPOW Next k s
         in
           det_run k s s1 ∧ s1.PC = 0x450128w ∧
           svc_exit_group_rel (if s.REG 0w = 0w then 0w else 1w) s1 ∧ s1.MEM = s.MEM ∧
           bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cake_exit_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end rrel wrel n s inp out inp_f out_f ms_f ec.
    shim_common_words_ok shim_ws ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_EXIT_VENEER ∧
    NRC (whole_step rrel wrel) n (inp,out,s) (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = if s.REG 0w = 0w then 0w else 1w
```

#### `forge_shimProof.cake_install_to_svc_exit_group_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_INSTALL_VENEER ⇒
    (let
       s1 = FUNPOW Next 3 s
     in
       det_run 3 s s1 ∧ s1.PC = 0x450138w ∧ svc_exit_group_rel 2w s1 ∧ s1.MEM = s.MEM ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cake_install_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end rrel wrel n s inp out inp_f out_f ms_f ec.
    shim_common_words_ok shim_ws ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_INSTALL_VENEER ∧
    NRC (whole_step rrel wrel) n (inp,out,s) (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = 2w
```

#### `forge_shimProof.cml_hdr1_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    LENGTH shim_ws = 80 ∧ slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = 0x400020w ∧
    s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
    (let
       s1 = FUNPOW Next 3 s
     in
       det_run 3 s s1 ∧ s1.PC = 0x40002Cw ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
       mem_dword s1.MEM 0x480008w = bm_buf_end ∧
       (∀a. a <₊ 0x480008w ∨ 0x480010w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
       (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
       shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cml_hdr2_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    LENGTH shim_ws = 80 ∧ slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = 0x40002Cw ∧
    s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
    (let
       s1 = FUNPOW Next 3 s
     in
       det_run 3 s s1 ∧ s1.PC = 0x400038w ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
       mem_dword s1.MEM 0x480010w = bm_buf_end ∧
       (∀a. a <₊ 0x480010w ∨ 0x480018w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
       (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
       shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cml_hdr3_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    LENGTH shim_ws = 80 ∧ slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = 0x400038w ∧
    s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
    (let
       s1 = FUNPOW Next 3 s
     in
       det_run 3 s s1 ∧ s1.PC = 0x400044w ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
       mem_dword s1.MEM 0x480018w = cb_begin ∧
       (∀a. a <₊ 0x480018w ∨ 0x480020w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
       (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
       shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cml_hdr4_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    LENGTH shim_ws = 80 ∧ slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = 0x400044w ∧
    s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
    (let
       s1 = FUNPOW Next 3 s
     in
       det_run 3 s s1 ∧ s1.PC = 0x400050w ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
       mem_dword s1.MEM 0x480020w = cb_end ∧
       (∀a. a <₊ 0x480020w ∨ 0x480028w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
       (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
       shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.det_run_add`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k1 k2 s s1 s2. det_run k1 s s1 ∧ det_run k2 s1 s2 ⇒ det_run (k1 + k2) s s2
```

#### `forge_shimProof.det_run_compute`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀s s'. det_run 0 s s' ⇔ s' = s) ∧
  (∀k s s'.
     det_run <..num comp'n..> s s' ⇔
     ∃s1. ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ∧ det_run (<..num comp'n..> − 1) s1 s') ∧
  ∀k s s'.
    det_run <..num comp'n..> s s' ⇔
    ∃s1. ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ∧ det_run <..num comp'n..> s1 s'
```

#### `forge_shimProof.det_run_funpow`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k s s'. det_run k s s' ⇒ s' = FUNPOW Next k s
```

#### `forge_shimProof.det_run_imp_nrc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k s s' rrel wrel inp out. det_run k s s' ⇒ NRC (whole_step rrel wrel) k (inp,out,s) (inp,out,s')
```

#### `forge_shimProof.det_run_imp_rtc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k s s' rrel wrel inp out. det_run k s s' ⇒ (whole_step rrel wrel)꙳ (inp,out,s) (inp,out,s')
```

#### `forge_shimProof.det_run_peel_nrc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k s s' rrel wrel n ec inp out inp_f out_f ms_f.
    det_run k s s' ∧ NRC (whole_step rrel wrel) n (inp,out,s) (inp_f,out_f,ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    k ≤ n ∧ NRC (whole_step rrel wrel) (n − k) (inp,out,s') (inp_f,out_f,ms_f)
```

#### `forge_shimProof.ffirecv16_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim16_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFIRECV_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃s'.
       (∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
       ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (∀f. 17 ≤ w2n (s.REG 3w) ∧ LENGTH f = 16 ⇒
         ∃s'.
           (∀rest out.
              (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (f ++ rest,out,s) (rest,out,s')) ∧
           ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end
             (0w::f ++ DROP 17 bytes2) s s') ∧
    ∀tail_bs.
      17 ≤ w2n (s.REG 3w) ∧ LENGTH tail_bs < 16 ⇒
      ∃s'.
        (∀out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (tail_bs,out,s) ([],out,s')) ∧
        ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s'
```

#### `forge_shimProof.ffirecv16_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err wrel n s inp out inp_f out_f ms_f ec bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim16_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFIRECV_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧
    NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n (inp,out,s)
      (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃n' s'.
       n' < n ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
         (inp,out,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
     (∃n' s' frame inp_after.
        n' < n ∧ LENGTH frame = 16 ∧ inp = frame ++ inp_after ∧
        NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
          (inp_after,out,s') (inp_f,out_f,ms_f) ∧
        ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end
          (0w::frame ++ DROP 17 bytes2) s s') ∨
     ∃n' s' inp_after.
       n' < n ∧ (allow_err ∨ LENGTH inp < 16) ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
         (inp_after,out,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.ffirecv64_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim64_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFIRECV_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 65 ⇒
     ∃s'.
       (∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
       ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (∀f. 65 ≤ w2n (s.REG 3w) ∧ LENGTH f = 64 ⇒
         ∃s'.
           (∀rest out.
              (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (f ++ rest,out,s) (rest,out,s')) ∧
           ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end
             (0w::f ++ DROP 65 bytes2) s s') ∧
    ∀tail_bs.
      65 ≤ w2n (s.REG 3w) ∧ LENGTH tail_bs < 64 ⇒
      ∃s'.
        (∀out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (tail_bs,out,s) ([],out,s')) ∧
        ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s'
```

#### `forge_shimProof.ffirecv64_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err wrel n s inp out inp_f out_f ms_f ec bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim64_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFIRECV_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧
    NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n (inp,out,s)
      (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 65 ⇒
     ∃n' s'.
       n' < n ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
         (inp,out,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (65 ≤ w2n (s.REG 3w) ⇒
     (∃n' s' frame inp_after.
        n' < n ∧ LENGTH frame = 64 ∧ inp = frame ++ inp_after ∧
        NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
          (inp_after,out,s') (inp_f,out_f,ms_f) ∧
        ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end
          (0w::frame ++ DROP 65 bytes2) s s') ∨
     ∃n' s' inp_after.
       n' < n ∧ (allow_err ∨ LENGTH inp < 64) ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
         (inp_after,out,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.ffisend16_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim16_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFISEND_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃s'.
       (∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
       ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
     ∃s'.
       (∀inp out.
          (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s)
            (inp,out ++ TAKE 16 (DROP 1 bytes2),s')) ∧
       ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.ffisend16_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err rrel n s inp out inp_f out_f ms_f ec bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim16_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFISEND_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧
    NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n (inp,out,s)
      (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃n' s'.
       n' < n ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
         (inp,out,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
     (∃n' s'.
        n' < n ∧
        NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
          (inp,out ++ TAKE 16 (DROP 1 bytes2),s') (inp_f,out_f,ms_f) ∧
        ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s') ∨
     allow_err ∧
     ∃n' s' chunk.
       n' < n ∧ chunk ≼ TAKE 16 (DROP 1 bytes2) ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
         (inp,out ++ chunk,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim16_words cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.ffisend64_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim64_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFISEND_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 65 ⇒
     ∃s'.
       (∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
       ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (65 ≤ w2n (s.REG 3w) ⇒
     ∃s'.
       (∀inp out.
          (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s)
            (inp,out ++ TAKE 64 (DROP 1 bytes2),s')) ∧
       ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.ffisend64_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err rrel n s inp out inp_f out_f ms_f ec bytes2.
    slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot forge_shim64_words cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_FFISEND_VENEER ∧ aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧
    NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n (inp,out,s)
      (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 65 ⇒
     ∃n' s'.
       n' < n ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
         (inp,out,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (65 ≤ w2n (s.REG 3w) ⇒
     (∃n' s'.
        n' < n ∧
        NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
          (inp,out ++ TAKE 64 (DROP 1 bytes2),s') (inp_f,out_f,ms_f) ∧
        ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s') ∨
     allow_err ∧
     ∃n' s' chunk.
       n' < n ∧ chunk ≼ TAKE 64 (DROP 1 bytes2) ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
         (inp,out ++ chunk,s') (inp_f,out_f,ms_f) ∧
       ffi_return_ok_slot forge_shim64_words cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.forge_mc_slot_lo55`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end ffi_names_l ffi_if inst_if.
    slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    lo55 (forge_mc_slot cb_end bm_buf_end ffi_names_l ffi_if inst_if)
```

#### `forge_shimProof.forge_mc_slot_mmio_min`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end sn rn ffi_if inst_if.
    mmio_pcs_min_index
      (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if).ffi_names = SOME 2
```

#### `forge_shimProof.forge_mc_slot_start_pc_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end sn rn ffi_if inst_if.
    slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    start_pc_ok (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)
      FORGE_CAKE_MAIN
```

#### `forge_shimProof.forge_regions_disjoint_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end.
    slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    (∀a. a ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_rx_tmp_region ⇒
         a ∉ forge_prog_addresses_slot cb_end bm_buf_end ∧ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_cml_ptrs_region ⇒
         a ∉ forge_prog_addresses_slot cb_end bm_buf_end ∧ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_heap_hdr_region ⇒ a ∉ forge_cml_ptrs_region ∧ a ∉ forge_shim_code_region) ∧
    (∀a. a ∈ forge_prog_addresses_slot cb_end bm_buf_end ⇒ untagged a) ∧
    ∀a. a ∈ forge_shim_code_region ⇒ untagged a
```

#### `forge_shimProof.mk_real_ffi_if_slot_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end cbspace sn rn B P.
    real_interfer_ok_slot cb_end bm_buf_end cbspace [ExtCall sn; ExtCall rn] B
      (mk_real_ffi_if_slot shim_ws cb_begin cb_end bm_buf_end P) forge_real_install_if
```

#### `forge_shimProof.read_bytearray_mem_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀n p dm m bs.
    read_bytearray p n (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    LENGTH bs = n ∧ ∀i. i < n ⇒ p + n2w i ∈ dm ∧ m (p + n2w i) = bs❲i❳
```

#### `forge_shimProof.real_interfer_ok_slot_imp_erase_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end cbspace sn rn B ffi_if inst_if.
    real_interfer_ok_slot cb_end bm_buf_end cbspace [ExtCall sn; ExtCall rn] B ffi_if inst_if ⇒
    ffi_interfer_ok FORGE_CAKE_MAIN
      (erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)) ∧
    install_interfer_ok FORGE_CAKE_MAIN cbspace
      (erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)) ∧
    interference_ok
      (erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)).
      next_interfer
      ((erase_mc B (forge_mc_slot cb_end bm_buf_end [ExtCall sn; ExtCall rn] ffi_if inst_if)).target.
       proj (forge_prog_addresses_slot cb_end bm_buf_end))
```

#### `forge_shimProof.real_step_add_x2`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s tgt.
    arm8_ok (erase s) ∧ sp_ok s ∧ s.PC && 0xFFFFFFFFFFFFF000w = 0x400000w ∧ aligned 2 s.PC ∧
    s.REG 2w = tgt && 0xFFFFFFFFFFFFF000w ∧ words32_in_mem s.PC [arm8_enc_add_x2 tgt] s.MEM ⇒
    NextStateARM8 s = SOME (s with <|PC := s.PC + 4w; REG := s.REG⦇2w ↦ tgt⦈; branch_hint := NONE|>) ∧
    ¬is_svc0_at s
```

#### `forge_shimProof.real_step_adrp_x2`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s tgt.
    arm8_ok (erase s) ∧ sp_ok s ∧ s.PC && 0xFFFFFFFFFFFFF000w = 0x400000w ∧ aligned 2 s.PC ∧
    0x400000w ≤₊ tgt ∧ tgt ≤₊ 0x480000w ∧ words32_in_mem s.PC [arm8_enc_adrp_x2 s.PC tgt] s.MEM ⇒
    NextStateARM8 s =
    SOME
      (s with
       <|PC := s.PC + 4w; REG := s.REG⦇2w ↦ tgt && 0xFFFFFFFFFFFFF000w⦈; branch_hint := NONE|>) ∧
    ¬is_svc0_at s
```

#### `forge_shimProof.shim16_common_words_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ shim_common_words_ok forge_shim16_words
```

#### `forge_shimProof.shim64_common_words_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ shim_common_words_ok forge_shim64_words
```

#### `forge_shimProof.shim_loaded_slot_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end m1 m2.
    LENGTH shim_ws = 80 ∧ (∀a. a ∈ forge_shim_code_region ⇒ m1 a = m2 a) ⇒
    (shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end m1 ⇔
     shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end m2)
```

#### `forge_shimProof.start_16_steps_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_SHIM_BASE ⇒
    (let
       s1 = FUNPOW Next 16 s
     in
       det_run 16 s s1 ∧ s1.PC = FORGE_VENEERS_BASE ∧ mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
       mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
       mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
       (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧
       shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.startup_to_cake_main_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws cb_begin cb_end bm_buf_end s.
    shim_common_words_ok shim_ws ∧ slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧
    sp_ok s ∧ shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_SHIM_BASE ⇒
    (let
       s1 = FUNPOW Next 43 s
     in
       det_run 43 s s1 ∧ s1.PC = FORGE_CAKE_MAIN ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧
       s1.REG 1w = FORGE_HEAP ∧ s1.REG 2w = FORGE_STACK ∧ s1.REG 3w = FORGE_STACKEND ∧
       mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
       mem_dword s1.MEM (FORGE_HEAP + 8w) = bm_buf_end ∧
       mem_dword s1.MEM (FORGE_HEAP + 16w) = bm_buf_end ∧
       mem_dword s1.MEM (FORGE_HEAP + 24w) = cb_begin ∧
       mem_dword s1.MEM (FORGE_HEAP + 32w) = cb_end ∧
       (∀a. a ∉ forge_cml_ptrs_region ∧ a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
       shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.svc_read_noerr_imp_rel`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inp s s' rest. svc_read_noerr_rel inp s s' rest ⇒ svc_read_rel inp s s' rest
```

#### `forge_shimProof.svc_write_noerr_imp_rel`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s s' out. svc_write_noerr_rel s s' out ⇒ svc_write_rel s s' out
```

#### `forge_shimProof.whole_step_arm8_det`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel inp out s inp' out' s' s1.
    ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ⇒
    (whole_step rrel wrel (inp,out,s) (inp',out',s') ⇔ inp' = inp ∧ out' = out ∧ s' = s1)
```

#### `forge_shimProof.whole_step_exit_stuck`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel ec inp out s y. svc_exit_group_rel ec s ⇒ ¬whole_step rrel wrel (inp,out,s) y
```

#### `forge_shimProof.whole_step_nrc_exit_stuck`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel n ec inp out s y.
    svc_exit_group_rel ec s ∧ NRC (whole_step rrel wrel) n (inp,out,s) y ⇒ n = 0 ∧ y = (inp,out,s)
```

#### `forge_shimProof.whole_step_svc_read_det`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel inp out s inp' out' s'.
    is_svc0_at s ∧ s.REG 8w = 63w ⇒
    (whole_step rrel wrel (inp,out,s) (inp',out',s') ⇔ rrel inp s s' inp' ∧ out' = out)
```

#### `forge_shimProof.whole_step_svc_write_det`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel inp out s inp' out' s'.
    is_svc0_at s ∧ s.REG 8w = 64w ⇒
    (whole_step rrel wrel (inp,out,s) (inp',out',s') ⇔
     ∃chunk. wrel s s' chunk ∧ inp' = inp ∧ out' = out ++ chunk)
```

#### `forge_shimProof.words32_in_mem_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ws base m1 m2.
    (∀a. base ≤₊ a ∧ a <₊ base + n2w (4 * LENGTH ws) ⇒ m1 a = m2 a) ∧
    w2n base + 4 * LENGTH ws < dimword (:64) ⇒
    (words32_in_mem base ws m1 ⇔ words32_in_mem base ws m2)
```

</details>

<details>
<summary><strong><code>forge_slotUtil</code></strong> — Frozen 256KB Slot Util (0 definitions, 21 theorems)</summary>

Parameterized slot layout arithmetic, installed proof, and constructive non-vacuity witness for any <=256KB kernel.

### Theorems

#### `forge_slotUtil.byte_align_64`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a. byte_align a = a && 0xFFFFFFFFFFFFFFF8w
```

#### `forge_slotUtil.byte_aligned_mod8`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a. byte_aligned a ⇔ w2n a MOD 8 = 0
```

#### `forge_slotUtil.bytes_in_word_64`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ bytes_in_word = 8w
```

#### `forge_slotUtil.compile_imp_ffi_names`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀asm_conf c p b d c1 f.
    compile asm_conf c p = SOME (b,d,c1) ∧ c1.lab_conf.shmem_extra = [] ∧ f ≠ [] ∧
    c.lab_conf.ffi_names = NONE ∧ ffinames_to_string_list (the [] c1.lab_conf.ffi_names) = f ⇒
    c1.lab_conf.ffi_names = SOME (MAP ExtCall f)
```

#### `forge_slotUtil.div_mod_4`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀i j. j < 4 ⇒ (4 * i + j) DIV 4 = i ∧ (4 * i + j) MOD 4 = j
```

#### `forge_slotUtil.div_mod_8`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀i j. j < 8 ⇒ (8 * i + j) DIV 8 = i ∧ (8 * i + j) MOD 8 = j
```

#### `forge_slotUtil.erase_mc_conf_ok_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_conf_ok (erase_mc B (forge_mc_slot cb_end bm_end fnames ffi_if inst_if))
```

#### `forge_slotUtil.erase_mc_init_ok_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_init_ok arm8_config arm8_backend_config
      (erase_mc B (forge_mc_slot cb_end bm_end fnames ffi_if inst_if))
```

#### `forge_slotUtil.forge_slot_installed_exact`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws sn rn code data ffi_names ms0 ffi_if inst_if.
    shim_common_words_ok shim_ws ∧ ffi_names = SOME [ExtCall sn; ExtCall rn] ∧
    forge_slot_loaded shim_ws code data ms0 ∧
    real_interfer_ok_slot (slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data))
      (slot_cbspace (LENGTH code)) [ExtCall sn; ExtCall rn] (bits_of ms0) ffi_if inst_if ⇒
    (let
       cb_begin = slot_cb_begin (LENGTH code);
       cb_end = slot_cb_end (LENGTH code);
       bm_end = slot_bm_buf_end (LENGTH data);
       cbsp = slot_cbspace (LENGTH code);
       ms1 = FUNPOW Next 43 ms0;
       emc =
         erase_mc (bits_of ms0)
           (forge_mc_slot cb_end bm_end [ExtCall sn; ExtCall rn] ffi_if inst_if)
     in
       det_run 43 ms0 ms1 ∧ ms1.PC = FORGE_CAKE_MAIN ∧ bits_of ms1 = bits_of ms0 ∧
       ms1.SP_EL0 = ms0.SP_EL0 ∧ sp_ok ms1 ∧ arm8_ok (erase ms1) ∧
       shim_loaded_slot shim_ws cb_begin cb_end bm_end ms1.MEM ∧
       installed code cbsp data 0 ffi_names (1,3) emc [] (erase ms1))
```

#### `forge_slotUtil.forge_slot_nonvacuous`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀shim_ws code data.
    LENGTH shim_ws = 80 ∧ 0 < LENGTH code ∧ LENGTH code ≤ FORGE_MAX_CODE_BYTES ∧
    LENGTH data ≤ FORGE_MAX_BITMAP_WORDS ⇒
    ∃ms0.
      forge_slot_loaded shim_ws code data ms0 ∧ ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
      ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
```

#### `forge_slotUtil.forge_veneer_facts_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_end.
    slot_layout_ok cb_begin cb_end bm_end ⇒
    FORGE_EXIT_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_INSTALL_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_FFISEND_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_FFIRECV_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_EXIT_VENEER ≠ FORGE_INSTALL_VENEER ∧ FORGE_EXIT_VENEER ≠ FORGE_FFISEND_VENEER ∧
    FORGE_EXIT_VENEER ≠ FORGE_FFIRECV_VENEER ∧ FORGE_INSTALL_VENEER ≠ FORGE_FFISEND_VENEER ∧
    FORGE_INSTALL_VENEER ≠ FORGE_FFIRECV_VENEER ∧ FORGE_FFISEND_VENEER ≠ FORGE_FFIRECV_VENEER ∧
    FORGE_INSTALL_VENEER ≠ FORGE_EXIT_VENEER ∧ FORGE_FFISEND_VENEER ≠ FORGE_EXIT_VENEER ∧
    FORGE_FFISEND_VENEER ≠ FORGE_INSTALL_VENEER ∧ FORGE_FFIRECV_VENEER ≠ FORGE_EXIT_VENEER ∧
    FORGE_FFIRECV_VENEER ≠ FORGE_INSTALL_VENEER ∧ FORGE_FFIRECV_VENEER ≠ FORGE_FFISEND_VENEER
```

#### `forge_slotUtil.mem_dword_cong_util`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m1 m2 a. (∀j. j < 8 ⇒ m1 (a + n2w j) = m2 (a + n2w j)) ⇒ mem_dword m1 a = mem_dword m2 a
```

#### `forge_slotUtil.mem_dword_get_byte`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m a. m a = get_byte a (mem_dword m (byte_align a)) F
```

#### `forge_slotUtil.read_bytearray_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀n a f g.
    (∀i. i < n ⇒ f (a + n2w i) = g (a + n2w i)) ⇒ read_bytearray a n f = read_bytearray a n g
```

#### `forge_slotUtil.read_bytearray_imp_bytes_in_mem`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs a m md k.
    (∀i. i < LENGTH bs ⇒ a + n2w i ∈ md ∧ a + n2w i ∉ k ∧ m (a + n2w i) = bs❲i❳) ⇒
    bytes_in_mem a bs m md k
```

#### `forge_slotUtil.slot_params_props`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len data_len.
    0 < code_len ∧ code_len ≤ FORGE_MAX_CODE_BYTES ∧ data_len ≤ FORGE_MAX_BITMAP_WORDS ⇒
    (let
       cb_begin = slot_cb_begin code_len;
       cb_end = slot_cb_end code_len;
       cbsp = slot_cbspace code_len;
       bm_end = slot_bm_buf_end data_len
     in
       slot_layout_ok cb_begin cb_end bm_end ∧ FORGE_CAKE_MAIN + n2w code_len = cb_begin ∧
       cb_begin + n2w cbsp = cb_end ∧ FORGE_CAKE_MAIN + n2w code_len + n2w cbsp = cb_end ∧
       w2n FORGE_CAKE_MAIN + code_len = w2n cb_begin ∧
       w2n FORGE_CAKE_MAIN + code_len + cbsp = w2n cb_end ∧ w2n cb_end ≤ 4456448 ∧
       FORGE_CAKE_BITMAPS + n2w (8 * data_len) = bm_end ∧
       FORGE_CAKE_BITMAPS + n2w data_len * bytes_in_word = bm_end ∧
       w2n FORGE_CAKE_BITMAPS + 8 * data_len = w2n bm_end ∧ w2n bm_end ≤ 4653056)
```

#### `forge_slotUtil.w2n_n2w_64`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀n. n < 18446744073709551616 ⇒ w2n (n2w n) = n
```

#### `forge_slotUtil.word64_add_lo_ls`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a b c.
    a + b < 18446744073709551616 ∧ c < 18446744073709551616 ⇒
    (n2w a + n2w b <₊ n2w c ⇔ a + b < c) ∧ (n2w a + n2w b ≤₊ n2w c ⇔ a + b ≤ c) ∧
    (n2w c ≤₊ n2w a + n2w b ⇔ c ≤ a + b) ∧ (n2w c <₊ n2w a + n2w b ⇔ c < a + b)
```

#### `forge_slotUtil.word_add_1w_n2w`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a i. a + 1w + n2w i = a + n2w (SUC i)
```

#### `forge_slotUtil.word_add_n2w_n2w`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a m n. a + n2w m + n2w n = a + n2w (m + n)
```

#### `forge_slotUtil.word_list_slice`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs base m.
    (∀i. i < LENGTH xs ⇒ m (base + n2w (8 * i)) = xs❲i❳) ∧ byte_aligned base ∧
    w2n base + 8 * LENGTH xs < dimword (:64) ⇒
    word_list base xs (fun2set (m,byte_aligned ∩ {a | base ≤₊ a ∧ a <₊ base + n2w (8 * LENGTH xs)}))
```

</details>

<details>
<summary><strong><code>forge_sha256Spec</code></strong> — Verified Crypto (M3) (19 definitions, 15 theorems)</summary>

SHA-256 pinned pure FIPS 180-4 SHA-256 and RFC 2104 HMAC-SHA256 specifications verified against official NIST/RFC test vectors.

### Definitions

#### `forge_sha256Spec.be32_of_bytes_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀b0 b1 b2 b3. be32_of_bytes b0 b1 b2 b3 = w2w b0 ≪ 24 ‖ w2w b1 ≪ 16 ‖ w2w b2 ≪ 8 ‖ w2w b3
```

#### `forge_sha256Spec.be32_to_bytes_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. be32_to_bytes w = [w2w (w ⋙ 24); w2w (w ⋙ 16); w2w (w ⋙ 8); w2w w]
```

#### `forge_sha256Spec.be64_to_bytes_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. be64_to_bytes w =
      [w2w (w ⋙ 56); w2w (w ⋙ 48); w2w (w ⋙ 40); w2w (w ⋙ 32); w2w (w ⋙ 24); w2w (w ⋙ 16);
       w2w (w ⋙ 8); w2w w]
```

#### `forge_sha256Spec.bytes_to_be32s_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ bytes_to_be32s =
  WFREC (@R. WF R ∧ ∀b3 b2 b1 b0 rest. R rest (b0::b1::b2::b3::rest))
    (λbytes_to_be32s a.
       case a of
         [] => I []
       | [b0] => I []
       | [b0; b1] => I []
       | [b0; b1; b2] => I []
       | b0::b1::b2::b3::rest => I (be32_of_bytes b0 b1 b2 b3::bytes_to_be32s rest))
```

#### `forge_sha256Spec.hmac_sha256_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key msg.
    hmac_sha256 key msg =
    (let
       k1 = if 64 < LENGTH key then sha256 key else key;
       k64 = k1 ++ REPLICATE (64 − LENGTH k1) 0w;
       ipad = hmac_xor_bytes 54w k64;
       opad = hmac_xor_bytes 92w k64
     in
       sha256 (opad ++ sha256 (ipad ++ msg)))
```

#### `forge_sha256Spec.hmac_xor_bytes_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀c. hmac_xor_bytes c [] = []) ∧ ∀c b bs. hmac_xor_bytes c (b::bs) = (b ⊕ c)::hmac_xor_bytes c bs
```

#### `forge_sha256Spec.sha256_bsig0_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x. sha256_bsig0 x = x ⇄ 2 ⊕ x ⇄ 13 ⊕ x ⇄ 22
```

#### `forge_sha256Spec.sha256_bsig1_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x. sha256_bsig1 x = x ⇄ 6 ⊕ x ⇄ 11 ⊕ x ⇄ 25
```

#### `forge_sha256Spec.sha256_ch_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y z. sha256_ch x y z = x && y ⊕ ¬x && z
```

#### `forge_sha256Spec.sha256_compress_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀h0 h1 h2 h3 h4 h5 h6 h7 win.
    sha256_compress (h0,h1,h2,h3,h4,h5,h6,h7) win =
    (let
       (a,b,c,d,e,f,g,h) = sha256_rounds sha256_k (h0,h1,h2,h3,h4,h5,h6,h7) win
     in
       (h0 + a,h1 + b,h2 + c,h3 + d,h4 + e,h5 + f,h6 + g,h7 + h))
```

#### `forge_sha256Spec.sha256_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀msg.
    sha256 msg = sha256_finalize (sha256_word_blocks sha256_iv (bytes_to_be32s (sha256_pad msg)))
```

#### `forge_sha256Spec.sha256_finalize_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀h0 h1 h2 h3 h4 h5 h6 h7.
    sha256_finalize (h0,h1,h2,h3,h4,h5,h6,h7) =
    be32_to_bytes h0 ++ be32_to_bytes h1 ++ be32_to_bytes h2 ++ be32_to_bytes h3 ++
    be32_to_bytes h4 ++ be32_to_bytes h5 ++ be32_to_bytes h6 ++ be32_to_bytes h7
```

#### `forge_sha256Spec.sha256_iv_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sha256_iv =
  (0x6A09E667w,0xBB67AE85w,0x3C6EF372w,0xA54FF53Aw,0x510E527Fw,0x9B05688Cw,0x1F83D9ABw,0x5BE0CD19w)
```

#### `forge_sha256Spec.sha256_k_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sha256_k = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_sha256Spec.sha256_maj_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y z. sha256_maj x y z = x && y ⊕ x && z ⊕ y && z
```

#### `forge_sha256Spec.sha256_pad_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀msg.
    sha256_pad msg =
    (let
       n = LENGTH msg;
       z = (119 − n MOD 64) MOD 64
     in
       msg ++ [128w] ++ REPLICATE z 0w ++ be64_to_bytes (n2w (8 * n)))
```

#### `forge_sha256Spec.sha256_round_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k w a b c d e f g h.
    sha256_round k w (a,b,c,d,e,f,g,h) =
    (let
       t1 = h + sha256_bsig1 e + sha256_ch e f g + k + w;
       t2 = sha256_bsig0 a + sha256_maj a b c
     in
       (t1 + t2,a,b,c,d + t1,e,f,g))
```

#### `forge_sha256Spec.sha256_ssig0_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x. sha256_ssig0 x = x ⇄ 7 ⊕ x ⇄ 18 ⊕ x ⋙ 3
```

#### `forge_sha256Spec.sha256_ssig1_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x. sha256_ssig1 x = x ⇄ 17 ⊕ x ⇄ 19 ⊕ x ⋙ 10
```

### Theorems

#### `forge_sha256Spec.LENGTH_hmac_sha256`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key msg. LENGTH (hmac_sha256 key msg) = 32
```

#### `forge_sha256Spec.LENGTH_sha256`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀msg. LENGTH (sha256 msg) = 32
```

#### `forge_sha256Spec.LENGTH_sha256_finalize`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st. LENGTH (sha256_finalize st) = 32
```

#### `forge_sha256Spec.bytes_to_be32s_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀rest b3 b2 b1 b0.
     bytes_to_be32s (b0::b1::b2::b3::rest) = be32_of_bytes b0 b1 b2 b3::bytes_to_be32s rest) ∧
  bytes_to_be32s [] = [] ∧ (∀v. bytes_to_be32s [v] = []) ∧ (∀v4 v. bytes_to_be32s [v; v4] = []) ∧
  ∀v8 v4 v. bytes_to_be32s [v; v4; v8] = []
```

#### `forge_sha256Spec.bytes_to_be32s_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀b0 b1 b2 b3 rest. P rest ⇒ P (b0::b1::b2::b3::rest)) ∧ P [] ∧ (∀v. P [v]) ∧
      (∀v v4. P [v; v4]) ∧ (∀v v4 v8. P [v; v4; v8]) ⇒
      ∀v. P v
```

#### `forge_sha256Spec.hmac_sha256_rfc4231_tc1`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ hmac_sha256 (REPLICATE 20 11w) (MAP (n2w ∘ ORD) "Hi There") =
  [176w; 52w; 76w; 97w; 216w; 219w; 56w; 83w; 92w; 168w; 175w; 206w; 175w; 11w; 241w; 43w; 136w;
   29w; 194w; 0w; 201w; 131w; 61w; 167w; 38w; 233w; 55w; 108w; 46w; 50w; 207w; 247w]
```

#### `forge_sha256Spec.hmac_sha256_rfc4231_tc2`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ hmac_sha256 (MAP (n2w ∘ ORD) "Jefe") (MAP (n2w ∘ ORD) "what do ya want for nothing?") =
  [91w; 220w; 193w; 70w; 191w; 96w; 117w; 78w; 106w; 4w; 36w; 38w; 8w; 149w; 117w; 199w; 90w; 0w;
   63w; 8w; 157w; 39w; 57w; 131w; 157w; 236w; 88w; 185w; 100w; 236w; 56w; 67w]
```

#### `forge_sha256Spec.hmac_sha256_rfc4231_tc6`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large term> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_sha256Spec.sha256_nist_448bit`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large term> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_sha256Spec.sha256_nist_abc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sha256 [97w; 98w; 99w] =
  [186w; 120w; 22w; 191w; 143w; 1w; 207w; 234w; 65w; 65w; 64w; 222w; 93w; 174w; 34w; 35w; 176w; 3w;
   97w; 163w; 150w; 23w; 122w; 156w; 180w; 16w; 255w; 97w; 242w; 0w; 21w; 173w]
```

#### `forge_sha256Spec.sha256_nist_empty`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sha256 [] =
  [227w; 176w; 196w; 66w; 152w; 252w; 28w; 20w; 154w; 251w; 244w; 200w; 153w; 111w; 185w; 36w; 39w;
   174w; 65w; 228w; 100w; 155w; 147w; 76w; 164w; 149w; 153w; 27w; 120w; 82w; 184w; 85w]
```

#### `forge_sha256Spec.sha256_rounds_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀win st. sha256_rounds [] st win = st) ∧
  ∀w9 w8 w7 w6 w5 w4 w3 w2 w15 w14 w13 w12 w11 w10 w1 w0 st ks k.
    sha256_rounds (k::ks) st (w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15) =
    (let
       st' = sha256_round k w0 st;
       wn = sha256_ssig1 w14 + w9 + sha256_ssig0 w1 + w0
     in
       sha256_rounds ks st' (w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,wn))
```

#### `forge_sha256Spec.sha256_rounds_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀st win. P [] st win) ∧
      (∀k ks st w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15.
         (∀st' wn.
            st' = sha256_round k w0 st ∧ wn = sha256_ssig1 w14 + w9 + sha256_ssig0 w1 + w0 ⇒
            P ks st' (w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,wn)) ⇒
         P (k::ks) st (w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15)) ⇒
      ∀v v1 v2. P v v1 v2
```

#### `forge_sha256Spec.sha256_word_blocks_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀w9 w8 w7 w6 w5 w4 w3 w2 w15 w14 w13 w12 w11 w10 w1 w0 st rest.
     sha256_word_blocks st
       (w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest) =
     sha256_word_blocks (sha256_compress st (w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15))
       rest) ∧ (∀st. sha256_word_blocks st [] = st) ∧ (∀v2 st. sha256_word_blocks st [v2] = st) ∧
  (∀v6 v2 st. sha256_word_blocks st [v2; v6] = st) ∧
  (∀v6 v2 v10 st. sha256_word_blocks st [v2; v6; v10] = st) ∧
  (∀v6 v2 v14 v10 st. sha256_word_blocks st [v2; v6; v10; v14] = st) ∧
  (∀v6 v2 v18 v14 v10 st. sha256_word_blocks st [v2; v6; v10; v14; v18] = st) ∧
  (∀v6 v22 v2 v18 v14 v10 st. sha256_word_blocks st [v2; v6; v10; v14; v18; v22] = st) ∧
  (∀v6 v26 v22 v2 v18 v14 v10 st. sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26] = st) ∧
  (∀v6 v30 v26 v22 v2 v18 v14 v10 st.
     sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30] = st) ∧
  (∀v6 v34 v30 v26 v22 v2 v18 v14 v10 st.
     sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30; v34] = st) ∧
  (∀v6 v38 v34 v30 v26 v22 v2 v18 v14 v10 st.
     sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38] = st) ∧
  (∀v6 v42 v38 v34 v30 v26 v22 v2 v18 v14 v10 st.
     sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42] = st) ∧
  (∀v6 v46 v42 v38 v34 v30 v26 v22 v2 v18 v14 v10 st.
     sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46] = st) ∧
  (∀v6 v50 v46 v42 v38 v34 v30 v26 v22 v2 v18 v14 v10 st.
     sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46; v50] = st) ∧
  (∀v6 v54 v50 v46 v42 v38 v34 v30 v26 v22 v2 v18 v14 v10 st.
     sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46; v50; v54] = st) ∧
  ∀v6 v58 v54 v50 v46 v42 v38 v34 v30 v26 v22 v2 v18 v14 v10 st.
    sha256_word_blocks st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46; v50; v54; v58] =
    st
```

#### `forge_sha256Spec.sha256_word_blocks_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀st w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest.
         P (sha256_compress st (w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15)) rest ⇒
         P st (w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest)) ∧
      (∀st. P st []) ∧ (∀st v2. P st [v2]) ∧ (∀st v2 v6. P st [v2; v6]) ∧
      (∀st v2 v6 v10. P st [v2; v6; v10]) ∧ (∀st v2 v6 v10 v14. P st [v2; v6; v10; v14]) ∧
      (∀st v2 v6 v10 v14 v18. P st [v2; v6; v10; v14; v18]) ∧
      (∀st v2 v6 v10 v14 v18 v22. P st [v2; v6; v10; v14; v18; v22]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26. P st [v2; v6; v10; v14; v18; v22; v26]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30. P st [v2; v6; v10; v14; v18; v22; v26; v30]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30 v34. P st [v2; v6; v10; v14; v18; v22; v26; v30; v34]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30 v34 v38.
         P st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30 v34 v38 v42.
         P st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30 v34 v38 v42 v46.
         P st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30 v34 v38 v42 v46 v50.
         P st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46; v50]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30 v34 v38 v42 v46 v50 v54.
         P st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46; v50; v54]) ∧
      (∀st v2 v6 v10 v14 v18 v22 v26 v30 v34 v38 v42 v46 v50 v54 v58.
         P st [v2; v6; v10; v14; v18; v22; v26; v30; v34; v38; v42; v46; v50; v54; v58]) ⇒
      ∀v v1. P v v1
```

</details>

<details>
<summary><strong><code>forge_airlockFfi</code></strong> — M3 4-FFI Airlock ABI (44 definitions, 45 theorems)</summary>

SHA-256 pinned 128-byte response frame bijection, dual-slot airlock_exec trace, and total 4-FFI oracle (bootload/commit/recv64/send128).

### Definitions

#### `forge_airlockFfi.airlock_exec_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀stepf key st clim wlim. airlock_exec stepf key st [] clim wlim = (st,[])) ∧
  ∀stepf key st f fs clim wlim.
    airlock_exec stepf key st (f::fs) clim wlim =
    if LENGTH f = 64 then
      (let
         (st',resp,dc) = stepf key st (frame64_decode f)
       in
         if dc then
           case clim of
             NONE =>
               (case wlim of
                  NONE =>
                    (let
                       (stf,outs) = airlock_exec stepf key st' fs NONE NONE
                     in
                       (stf,frame128_encode resp::outs))
                | SOME 0 => (st',[frame128_encode resp])
                | SOME (SUC w) =>
                  (let
                     (stf,outs) = airlock_exec stepf key st' fs NONE (SOME w)
                   in
                     (stf,frame128_encode resp::outs)))
           | SOME 0 => (st,[])
           | SOME (SUC c) =>
             case wlim of
               NONE =>
                 (let
                    (stf,outs) = airlock_exec stepf key st' fs (SOME c) NONE
                  in
                    (stf,frame128_encode resp::outs))
             | SOME 0 => (st',[frame128_encode resp])
             | SOME (SUC w) =>
               (let
                  (stf,outs) = airlock_exec stepf key st' fs (SOME c) (SOME w)
                in
                  (stf,frame128_encode resp::outs))
         else
           case wlim of
             NONE =>
               (let
                  (stf,outs) = airlock_exec stepf key st' fs clim NONE
                in
                  (stf,frame128_encode resp::outs))
           | SOME 0 => (st',[frame128_encode resp])
           | SOME (SUC w) =>
             (let
                (stf,outs) = airlock_exec stepf key st' fs clim (SOME w)
              in
                (stf,frame128_encode resp::outs)))
    else (st,[])
```

#### `forge_airlockFfi.airlock_ffi_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. airlock_ffi io = initial_ffi_state airlock_ffi_oracle io
```

#### `forge_airlockFfi.airlock_ffi_names_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_ffi_names = [«bootload»; «commit»; «recv64»; «send128»]
```

#### `forge_airlockFfi.airlock_ffi_oracle_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_ffi_oracle =
  (λname io conf bytes.
     if name = ExtCall «bootload» then
       case ffi_bootload conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else if name = ExtCall «commit» then
       case ffi_commit conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else if name = ExtCall «recv64» then
       case ffi_al_recv64 conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else if name = ExtCall «send128» then
       case ffi_al_send128 conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else Oracle_final FFI_failed)
```

#### `forge_airlockFfi.airlock_ffi_part_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_ffi_part =
  (encode_airlock_io,decode_airlock_io,
   [(«bootload»,ffi_bootload); («commit»,ffi_commit); («recv64»,ffi_al_recv64);
    («send128»,ffi_al_send128)])
```

#### `forge_airlockFfi.airlock_io_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. airlock_io_ABS (airlock_io_REP a) = a) ∧
  ∀r. (λx. T) r ⇔ airlock_io_REP (airlock_io_ABS r) = r
```

#### `forge_airlockFfi.airlock_io_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_io_CONS = airlock_io_ABS
```

#### `forge_airlockFfi.airlock_io_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_airlockFfi.airlock_io_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 f.
    airlock_io_CASE (airlock_io a0 a1 a2 a3 a4 a5 a6 a7) f = f a0 a1 a2 a3 a4 a5 a6 a7
```

#### `forge_airlockFfi.airlock_io_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7.
    airlock_io_size (airlock_io a0 a1 a2 a3 a4 a5 a6 a7) =
    1 +
    (list_size w2n a0 +
     (bool_size a1 +
      (list_size w2n a2 +
       (list_size w2n a3 +
        (list_size (list_size w2n) a4 +
         (list_size (list_size w2n) a5 + (option_size (λx. x) a6 + option_size (λx. x) a7)))))))
```

#### `forge_airlockFfi.airlock_proj_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_proj =
  ((λio.
      FEMPTY |++
      [(«bootload»,encode_airlock_io io); («commit»,encode_airlock_io io);
       («recv64»,encode_airlock_io io); («send128»,encode_airlock_io io)]),
   [(airlock_ffi_names,mk_ffi_next airlock_ffi_part)])
```

#### `forge_airlockFfi.decode_airlock_io_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f. decode_airlock_io f =
      if ∃io. encode_airlock_io io = f then SOME (@io. encode_airlock_io io = f) else NONE
```

#### `forge_airlockFfi.encode_airlock_io_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io.
    encode_airlock_io io =
    Cons (encode_byte_list64 io.boot_key)
      (Cons (encode_bool_ffi io.boot_fail)
         (Cons (encode_byte_list64 io.slotA)
            (Cons (encode_byte_list64 io.slotB)
               (Cons (List (MAP encode_byte_list64 io.inputs))
                  (Cons (List (MAP encode_byte_list64 io.outputs))
                     (Cons (encode_opt_num64 io.commit_limit) (encode_opt_num64 io.write_limit)))))))
```

#### `forge_airlockFfi.encode_bool_ffi_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀b. encode_bool_ffi b = Num (if b then 1 else 0)
```

#### `forge_airlockFfi.ffi_al_recv64_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_al_recv64 conf bytes io =
    if LENGTH bytes < 65 then SOME (FFIreturn bytes io)
    else
      case io.inputs of
        [] => SOME (FFIreturn (1w::DROP 1 bytes) io)
      | f::fs =>
        if LENGTH f = 64 then SOME (FFIreturn (0w::f ++ DROP 65 bytes) (io with inputs := fs))
        else SOME (FFIreturn (1w::DROP 1 bytes) io)
```

#### `forge_airlockFfi.ffi_al_send128_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_al_send128 conf bytes io =
    if LENGTH bytes < 129 then SOME (FFIreturn bytes io)
    else
      (let
         frame = TAKE 128 (DROP 1 bytes)
       in
         case io.write_limit of
           NONE => SOME (FFIreturn (0w::DROP 1 bytes) (io with outputs := io.outputs ++ [frame]))
         | SOME 0 => SOME (FFIreturn (1w::DROP 1 bytes) (io with outputs := io.outputs ++ [frame]))
         | SOME (SUC n) =>
           SOME
             (FFIreturn (0w::DROP 1 bytes)
                (io with <|outputs := io.outputs ++ [frame]; write_limit := SOME n|>)))
```

#### `forge_airlockFfi.ffi_bootload_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_bootload conf bytes io =
    if LENGTH bytes < 545 then SOME (FFIreturn bytes io)
    else if
      io.boot_fail ∨ LENGTH io.boot_key ≠ 32 ∨ LENGTH io.slotA ≠ 256 ∨ LENGTH io.slotB ≠ 256
    then
      SOME (FFIreturn (1w::DROP 1 bytes) io)
    else SOME (FFIreturn (0w::io.boot_key ++ io.slotA ++ io.slotB ++ DROP 545 bytes) io)
```

#### `forge_airlockFfi.ffi_commit_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_commit conf bytes io =
    if LENGTH bytes < 258 then SOME (FFIreturn bytes io)
    else
      (let
         sel = bytes❲1❳;
         rec = TAKE 256 (DROP 2 bytes);
         io_upd = if sel && 1w = 0w then io with slotA := rec else io with slotB := rec
       in
         case io.commit_limit of
           NONE => SOME (FFIreturn (0w::DROP 1 bytes) io_upd)
         | SOME 0 => SOME (FFIreturn (1w::DROP 1 bytes) io)
         | SOME (SUC c) => SOME (FFIreturn (0w::DROP 1 bytes) (io_upd with commit_limit := SOME c)))
```

#### `forge_airlockFfi.frame128_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. frame128_ABS (frame128_REP a) = a) ∧ ∀r. (λx. T) r ⇔ frame128_REP (frame128_ABS r) = r
```

#### `forge_airlockFfi.frame128_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame128_CONS = frame128_ABS
```

#### `forge_airlockFfi.frame128_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_airlockFfi.frame128_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 f.
    frame128_CASE (Frame128 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) f =
    f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
```

#### `forge_airlockFfi.frame128_decode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs.
    frame128_decode bs =
    (let
       (w0,r0) = le64_take bs;
       (w1,r1) = le64_take r0;
       (w2,r2) = le64_take r1;
       (w3,r3) = le64_take r2;
       (w4,r4) = le64_take r3;
       (w5,r5) = le64_take r4;
       (w6,r6) = le64_take r5;
       (w7,r7) = le64_take r6;
       (w8,r8) = le64_take r7;
       (w9,r9) = le64_take r8;
       (w10,r10) = le64_take r9;
       (w11,r11) = le64_take r10;
       (w12,r12) = le64_take r11;
       (w13,r13) = le64_take r12;
       (w14,r14) = le64_take r13;
       (w15,_0) = le64_take r14
     in
       Frame128 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
```

#### `forge_airlockFfi.frame128_encode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15.
    frame128_encode (Frame128 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) =
    le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3 ++ le64_encode w4 ++
    le64_encode w5 ++ le64_encode w6 ++ le64_encode w7 ++ le64_encode w8 ++ le64_encode w9 ++
    le64_encode w10 ++ le64_encode w11 ++ le64_encode w12 ++ le64_encode w13 ++ le64_encode w14 ++
    le64_encode w15
```

#### `forge_airlockFfi.frame128_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15.
    frame128_size (Frame128 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) =
    1 +
    (w2n a0 +
     (w2n a1 +
      (w2n a2 +
       (w2n a3 +
        (w2n a4 +
         (w2n a5 +
          (w2n a6 +
           (w2n a7 +
            (w2n a8 +
             (w2n a9 + (w2n a10 + (w2n a11 + (w2n a12 + (w2n a13 + (w2n a14 + w2n a15)))))))))))))))
```

#### `forge_airlockFfi.le64_take_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ le64_take =
  WFREC (@R. WF R)
    (λle64_take a.
       case a of
         [] => I (0w,[])
       | [b0] => I (0w,[])
       | [b0; b1] => I (0w,[])
       | [b0; b1; b2] => I (0w,[])
       | [b0; b1; b2; b3] => I (0w,[])
       | [b0; b1; b2; b3; b4] => I (0w,[])
       | [b0; b1; b2; b3; b4; b5] => I (0w,[])
       | [b0; b1; b2; b3; b4; b5; b6] => I (0w,[])
       | b0::b1::b2::b3::b4::b5::b6::b7::rest => I (le64_decode b0 b1 b2 b3 b4 b5 b6 b7,rest))
```

#### `forge_airlockFfi.pad512_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. pad512 bs = TAKE 512 (bs ++ REPLICATE 512 0w)
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_boot_fail_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).boot_fail ⇔ b
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_boot_fail_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with boot_fail updated_by f =
    airlock_io l (f b) l0 l1 l2 l3 $o o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_boot_key_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).boot_key = l
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_boot_key_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with boot_key updated_by f =
    airlock_io (f l) b l0 l1 l2 l3 $o o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_commit_limit_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).commit_limit = $o
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_commit_limit_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with commit_limit updated_by f =
    airlock_io l b l0 l1 l2 l3 (f $o) o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_inputs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).inputs = l2
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_inputs_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with inputs updated_by f = airlock_io l b l0 l1 (f l2) l3 $o o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_outputs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).outputs = l3
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_outputs_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with outputs updated_by f =
    airlock_io l b l0 l1 l2 (f l3) $o o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_slotA_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).slotA = l0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_slotA_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with slotA updated_by f = airlock_io l b (f l0) l1 l2 l3 $o o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_slotB_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).slotB = l1
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_slotB_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with slotB updated_by f = airlock_io l b l0 (f l1) l2 l3 $o o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_write_limit_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).write_limit = o0
```

#### `forge_airlockFfi.recordtype_airlock_io_seldef_write_limit_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with write_limit updated_by f =
    airlock_io l b l0 l1 l2 l3 $o (f o0)
```

#### `forge_airlockFfi.sent_frames128_of_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sent_frames128_of =
  WFREC
    (@R. WF R ∧ (∀bs conf n rest. R rest (IO_event (ExtCall n) conf bs::rest)) ∧
         ∀v4 v3 v9 rest. R rest (IO_event (SharedMem v9) v3 v4::rest))
    (λsent_frames128_of a.
       case a of
         [] => I []
       | IO_event (ExtCall n) conf bs::rest =>
         I
           ((if n = «send128» ∧ 129 ≤ LENGTH bs then [TAKE 128 (DROP 1 (MAP FST bs))] else []) ++
            sent_frames128_of rest)
       | IO_event (SharedMem v11) conf bs::rest => I (sent_frames128_of rest))
```

### Theorems

#### `forge_airlockFfi.EXISTS_airlock_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∃a. P a) ⇔
      ∃l3 b l2 l1 l0 l o0 $o.
        P
          <|boot_key := l3; boot_fail := b; slotA := l2; slotB := l1; inputs := l0; outputs := l;
            commit_limit := o0; write_limit := $o|>
```

#### `forge_airlockFfi.FORALL_airlock_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀a. P a) ⇔
      ∀l3 b l2 l1 l0 l o0 $o.
        P
          <|boot_key := l3; boot_fail := b; slotA := l2; slotB := l1; inputs := l0; outputs := l;
            commit_limit := o0; write_limit := $o|>
```

#### `forge_airlockFfi.LENGTH_pad512`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. LENGTH (pad512 bs) = 512
```

#### `forge_airlockFfi.airlock_exec_prefix_none`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀stepf inps key st clim wlim.
    SND (airlock_exec stepf key st inps clim wlim) ≼ SND (airlock_exec stepf key st inps NONE NONE)
```

#### `forge_airlockFfi.airlock_ffi_outputs_eq_sent_frames`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io st'.
    io.outputs = [] ∧ call_FFI_rel꙳ (airlock_ffi io) st' ⇒
    st'.ffi_state.outputs = sent_frames128_of st'.io_events
```

#### `forge_airlockFfi.airlock_io_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a0' a1' a2' a3' a4' a5' a6' a7'.
    airlock_io a0 a1 a2 a3 a4 a5 a6 a7 = airlock_io a0' a1' a2' a3' a4' a5' a6' a7' ⇔
    a0 = a0' ∧ (a1 ⇔ a1') ∧ a2 = a2' ∧ a3 = a3' ∧ a4 = a4' ∧ a5 = a5' ∧ a6 = a6' ∧ a7 = a7'
```

#### `forge_airlockFfi.airlock_io_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2 a3 a4 a5 a6 a7.
    h (airlock_io a0 a1 a2 a3 a4 a5 a6 a7) = f0 a0 a1 a2 a3 a4 a5 a6 a7
```

#### `forge_airlockFfi.airlock_io_accessors`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).boot_key = l) ∧
  (∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).boot_fail ⇔ b) ∧
  (∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).slotA = l0) ∧
  (∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).slotB = l1) ∧
  (∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).inputs = l2) ∧
  (∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).outputs = l3) ∧
  (∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).commit_limit = $o) ∧
  ∀l b l0 l1 l2 l3 $o o0. (airlock_io l b l0 l1 l2 l3 $o o0).write_limit = o0
```

#### `forge_airlockFfi.airlock_io_accfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f a. (a with boot_fail updated_by f).boot_key = a.boot_key) ∧
  (∀f a. (a with slotA updated_by f).boot_key = a.boot_key) ∧
  (∀f a. (a with slotB updated_by f).boot_key = a.boot_key) ∧
  (∀f a. (a with inputs updated_by f).boot_key = a.boot_key) ∧
  (∀f a. (a with outputs updated_by f).boot_key = a.boot_key) ∧
  (∀f a. (a with commit_limit updated_by f).boot_key = a.boot_key) ∧
  (∀f a. (a with write_limit updated_by f).boot_key = a.boot_key) ∧
  (∀f a. (a with boot_key updated_by f).boot_fail ⇔ a.boot_fail) ∧
  (∀f a. (a with slotA updated_by f).boot_fail ⇔ a.boot_fail) ∧
  (∀f a. (a with slotB updated_by f).boot_fail ⇔ a.boot_fail) ∧
  (∀f a. (a with inputs updated_by f).boot_fail ⇔ a.boot_fail) ∧
  (∀f a. (a with outputs updated_by f).boot_fail ⇔ a.boot_fail) ∧
  (∀f a. (a with commit_limit updated_by f).boot_fail ⇔ a.boot_fail) ∧
  (∀f a. (a with write_limit updated_by f).boot_fail ⇔ a.boot_fail) ∧
  (∀f a. (a with boot_key updated_by f).slotA = a.slotA) ∧
  (∀f a. (a with boot_fail updated_by f).slotA = a.slotA) ∧
  (∀f a. (a with slotB updated_by f).slotA = a.slotA) ∧
  (∀f a. (a with inputs updated_by f).slotA = a.slotA) ∧
  (∀f a. (a with outputs updated_by f).slotA = a.slotA) ∧
  (∀f a. (a with commit_limit updated_by f).slotA = a.slotA) ∧
  (∀f a. (a with write_limit updated_by f).slotA = a.slotA) ∧
  (∀f a. (a with boot_key updated_by f).slotB = a.slotB) ∧
  (∀f a. (a with boot_fail updated_by f).slotB = a.slotB) ∧
  (∀f a. (a with slotA updated_by f).slotB = a.slotB) ∧
  (∀f a. (a with inputs updated_by f).slotB = a.slotB) ∧
  (∀f a. (a with outputs updated_by f).slotB = a.slotB) ∧
  (∀f a. (a with commit_limit updated_by f).slotB = a.slotB) ∧
  (∀f a. (a with write_limit updated_by f).slotB = a.slotB) ∧
  (∀f a. (a with boot_key updated_by f).inputs = a.inputs) ∧
  (∀f a. (a with boot_fail updated_by f).inputs = a.inputs) ∧
  (∀f a. (a with slotA updated_by f).inputs = a.inputs) ∧
  (∀f a. (a with slotB updated_by f).inputs = a.inputs) ∧
  (∀f a. (a with outputs updated_by f).inputs = a.inputs) ∧
  (∀f a. (a with commit_limit updated_by f).inputs = a.inputs) ∧
  (∀f a. (a with write_limit updated_by f).inputs = a.inputs) ∧
  (∀f a. (a with boot_key updated_by f).outputs = a.outputs) ∧
  (∀f a. (a with boot_fail updated_by f).outputs = a.outputs) ∧
  (∀f a. (a with slotA updated_by f).outputs = a.outputs) ∧
  (∀f a. (a with slotB updated_by f).outputs = a.outputs) ∧
  (∀f a. (a with inputs updated_by f).outputs = a.outputs) ∧
  (∀f a. (a with commit_limit updated_by f).outputs = a.outputs) ∧
  (∀f a. (a with write_limit updated_by f).outputs = a.outputs) ∧
  (∀f a. (a with boot_key updated_by f).commit_limit = a.commit_limit) ∧
  (∀f a. (a with boot_fail updated_by f).commit_limit = a.commit_limit) ∧
  (∀f a. (a with slotA updated_by f).commit_limit = a.commit_limit) ∧
  (∀f a. (a with slotB updated_by f).commit_limit = a.commit_limit) ∧
  (∀f a. (a with inputs updated_by f).commit_limit = a.commit_limit) ∧
  (∀f a. (a with outputs updated_by f).commit_limit = a.commit_limit) ∧
  (∀f a. (a with write_limit updated_by f).commit_limit = a.commit_limit) ∧
  (∀f a. (a with boot_key updated_by f).write_limit = a.write_limit) ∧
  (∀f a. (a with boot_fail updated_by f).write_limit = a.write_limit) ∧
  (∀f a. (a with slotA updated_by f).write_limit = a.write_limit) ∧
  (∀f a. (a with slotB updated_by f).write_limit = a.write_limit) ∧
  (∀f a. (a with inputs updated_by f).write_limit = a.write_limit) ∧
  (∀f a. (a with outputs updated_by f).write_limit = a.write_limit) ∧
  (∀f a. (a with commit_limit updated_by f).write_limit = a.write_limit) ∧
  (∀f a. (a with boot_key updated_by f).boot_key = f a.boot_key) ∧
  (∀f a. (a with boot_fail updated_by f).boot_fail ⇔ f a.boot_fail) ∧
  (∀f a. (a with slotA updated_by f).slotA = f a.slotA) ∧
  (∀f a. (a with slotB updated_by f).slotB = f a.slotB) ∧
  (∀f a. (a with inputs updated_by f).inputs = f a.inputs) ∧
  (∀f a. (a with outputs updated_by f).outputs = f a.outputs) ∧
  (∀f a. (a with commit_limit updated_by f).commit_limit = f a.commit_limit) ∧
  ∀f a. (a with write_limit updated_by f).write_limit = f a.write_limit
```

#### `forge_airlockFfi.airlock_io_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧
    (∀a0 a1 a2 a3 a4 a5 a6 a7.
       M' = airlock_io a0 a1 a2 a3 a4 a5 a6 a7 ⇒
       f a0 a1 a2 a3 a4 a5 a6 a7 = f' a0 a1 a2 a3 a4 a5 a6 a7) ⇒
    airlock_io_CASE M f = airlock_io_CASE M' f'
```

#### `forge_airlockFfi.airlock_io_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_io_CASE x f = v ⇔
  ∃l b l0 l1 l2 l3 o' o0. x = airlock_io l b l0 l1 l2 l3 o' o0 ∧ f l b l0 l1 l2 l3 o' o0 = v
```

#### `forge_airlockFfi.airlock_io_component_equality`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a1 a2.
    a1 = a2 ⇔
    a1.boot_key = a2.boot_key ∧ (a1.boot_fail ⇔ a2.boot_fail) ∧ a1.slotA = a2.slotA ∧
    a1.slotB = a2.slotB ∧ a1.inputs = a2.inputs ∧ a1.outputs = a2.outputs ∧
    a1.commit_limit = a2.commit_limit ∧ a1.write_limit = a2.write_limit
```

#### `forge_airlockFfi.airlock_io_fn_updates`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f l b l0 l1 l2 l3 $o o0.
     airlock_io l b l0 l1 l2 l3 $o o0 with boot_key updated_by f =
     airlock_io (f l) b l0 l1 l2 l3 $o o0) ∧
  (∀f l b l0 l1 l2 l3 $o o0.
     airlock_io l b l0 l1 l2 l3 $o o0 with boot_fail updated_by f =
     airlock_io l (f b) l0 l1 l2 l3 $o o0) ∧
  (∀f l b l0 l1 l2 l3 $o o0.
     airlock_io l b l0 l1 l2 l3 $o o0 with slotA updated_by f = airlock_io l b (f l0) l1 l2 l3 $o o0) ∧
  (∀f l b l0 l1 l2 l3 $o o0.
     airlock_io l b l0 l1 l2 l3 $o o0 with slotB updated_by f = airlock_io l b l0 (f l1) l2 l3 $o o0) ∧
  (∀f l b l0 l1 l2 l3 $o o0.
     airlock_io l b l0 l1 l2 l3 $o o0 with inputs updated_by f =
     airlock_io l b l0 l1 (f l2) l3 $o o0) ∧
  (∀f l b l0 l1 l2 l3 $o o0.
     airlock_io l b l0 l1 l2 l3 $o o0 with outputs updated_by f =
     airlock_io l b l0 l1 l2 (f l3) $o o0) ∧
  (∀f l b l0 l1 l2 l3 $o o0.
     airlock_io l b l0 l1 l2 l3 $o o0 with commit_limit updated_by f =
     airlock_io l b l0 l1 l2 l3 (f $o) o0) ∧
  ∀f l b l0 l1 l2 l3 $o o0.
    airlock_io l b l0 l1 l2 l3 $o o0 with write_limit updated_by f =
    airlock_io l b l0 l1 l2 l3 $o (f o0)
```

#### `forge_airlockFfi.airlock_io_fupdcanon`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g f a.
     a with <|boot_fail updated_by f; boot_key updated_by g|> =
     a with <|boot_key updated_by g; boot_fail updated_by f|>) ∧
  (∀g f a.
     a with <|slotA updated_by f; boot_key updated_by g|> =
     a with <|boot_key updated_by g; slotA updated_by f|>) ∧
  (∀g f a.
     a with <|slotA updated_by f; boot_fail updated_by g|> =
     a with <|boot_fail updated_by g; slotA updated_by f|>) ∧
  (∀g f a.
     a with <|slotB updated_by f; boot_key updated_by g|> =
     a with <|boot_key updated_by g; slotB updated_by f|>) ∧
  (∀g f a.
     a with <|slotB updated_by f; boot_fail updated_by g|> =
     a with <|boot_fail updated_by g; slotB updated_by f|>) ∧
  (∀g f a.
     a with <|slotB updated_by f; slotA updated_by g|> =
     a with <|slotA updated_by g; slotB updated_by f|>) ∧
  (∀g f a.
     a with <|inputs updated_by f; boot_key updated_by g|> =
     a with <|boot_key updated_by g; inputs updated_by f|>) ∧
  (∀g f a.
     a with <|inputs updated_by f; boot_fail updated_by g|> =
     a with <|boot_fail updated_by g; inputs updated_by f|>) ∧
  (∀g f a.
     a with <|inputs updated_by f; slotA updated_by g|> =
     a with <|slotA updated_by g; inputs updated_by f|>) ∧
  (∀g f a.
     a with <|inputs updated_by f; slotB updated_by g|> =
     a with <|slotB updated_by g; inputs updated_by f|>) ∧
  (∀g f a.
     a with <|outputs updated_by f; boot_key updated_by g|> =
     a with <|boot_key updated_by g; outputs updated_by f|>) ∧
  (∀g f a.
     a with <|outputs updated_by f; boot_fail updated_by g|> =
     a with <|boot_fail updated_by g; outputs updated_by f|>) ∧
  (∀g f a.
     a with <|outputs updated_by f; slotA updated_by g|> =
     a with <|slotA updated_by g; outputs updated_by f|>) ∧
  (∀g f a.
     a with <|outputs updated_by f; slotB updated_by g|> =
     a with <|slotB updated_by g; outputs updated_by f|>) ∧
  (∀g f a.
     a with <|outputs updated_by f; inputs updated_by g|> =
     a with <|inputs updated_by g; outputs updated_by f|>) ∧
  (∀g f a.
     a with <|commit_limit updated_by f; boot_key updated_by g|> =
     a with <|boot_key updated_by g; commit_limit updated_by f|>) ∧
  (∀g f a.
     a with <|commit_limit updated_by f; boot_fail updated_by g|> =
     a with <|boot_fail updated_by g; commit_limit updated_by f|>) ∧
  (∀g f a.
     a with <|commit_limit updated_by f; slotA updated_by g|> =
     a with <|slotA updated_by g; commit_limit updated_by f|>) ∧
  (∀g f a.
     a with <|commit_limit updated_by f; slotB updated_by g|> =
     a with <|slotB updated_by g; commit_limit updated_by f|>) ∧
  (∀g f a.
     a with <|commit_limit updated_by f; inputs updated_by g|> =
     a with <|inputs updated_by g; commit_limit updated_by f|>) ∧
  (∀g f a.
     a with <|commit_limit updated_by f; outputs updated_by g|> =
     a with <|outputs updated_by g; commit_limit updated_by f|>) ∧
  (∀g f a.
     a with <|write_limit updated_by f; boot_key updated_by g|> =
     a with <|boot_key updated_by g; write_limit updated_by f|>) ∧
  (∀g f a.
     a with <|write_limit updated_by f; boot_fail updated_by g|> =
     a with <|boot_fail updated_by g; write_limit updated_by f|>) ∧
  (∀g f a.
     a with <|write_limit updated_by f; slotA updated_by g|> =
     a with <|slotA updated_by g; write_limit updated_by f|>) ∧
  (∀g f a.
     a with <|write_limit updated_by f; slotB updated_by g|> =
     a with <|slotB updated_by g; write_limit updated_by f|>) ∧
  (∀g f a.
     a with <|write_limit updated_by f; inputs updated_by g|> =
     a with <|inputs updated_by g; write_limit updated_by f|>) ∧
  (∀g f a.
     a with <|write_limit updated_by f; outputs updated_by g|> =
     a with <|outputs updated_by g; write_limit updated_by f|>) ∧
  ∀g f a.
    a with <|write_limit updated_by f; commit_limit updated_by g|> =
    a with <|commit_limit updated_by g; write_limit updated_by f|>
```

#### `forge_airlockFfi.airlock_io_fupdcanon_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockFfi.airlock_io_fupdfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g f a.
     a with <|boot_key updated_by f; boot_key updated_by g|> = a with boot_key updated_by f ∘ g) ∧
  (∀g f a.
     a with <|boot_fail updated_by f; boot_fail updated_by g|> = a with boot_fail updated_by f ∘ g) ∧
  (∀g f a. a with <|slotA updated_by f; slotA updated_by g|> = a with slotA updated_by f ∘ g) ∧
  (∀g f a. a with <|slotB updated_by f; slotB updated_by g|> = a with slotB updated_by f ∘ g) ∧
  (∀g f a. a with <|inputs updated_by f; inputs updated_by g|> = a with inputs updated_by f ∘ g) ∧
  (∀g f a. a with <|outputs updated_by f; outputs updated_by g|> = a with outputs updated_by f ∘ g) ∧
  (∀g f a.
     a with <|commit_limit updated_by f; commit_limit updated_by g|> =
     a with commit_limit updated_by f ∘ g) ∧
  ∀g f a.
    a with <|write_limit updated_by f; write_limit updated_by g|> =
    a with write_limit updated_by f ∘ g
```

#### `forge_airlockFfi.airlock_io_fupdfupds_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f. boot_key_fupd f ∘ boot_key_fupd g = boot_key_fupd (f ∘ g)) ∧
   ∀h g f. boot_key_fupd f ∘ boot_key_fupd g ∘ h = boot_key_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. boot_fail_fupd f ∘ boot_fail_fupd g = boot_fail_fupd (f ∘ g)) ∧
   ∀h g f. boot_fail_fupd f ∘ boot_fail_fupd g ∘ h = boot_fail_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. slotA_fupd f ∘ slotA_fupd g = slotA_fupd (f ∘ g)) ∧
   ∀h g f. slotA_fupd f ∘ slotA_fupd g ∘ h = slotA_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. slotB_fupd f ∘ slotB_fupd g = slotB_fupd (f ∘ g)) ∧
   ∀h g f. slotB_fupd f ∘ slotB_fupd g ∘ h = slotB_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. inputs_fupd f ∘ inputs_fupd g = inputs_fupd (f ∘ g)) ∧
   ∀h g f. inputs_fupd f ∘ inputs_fupd g ∘ h = inputs_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. outputs_fupd f ∘ outputs_fupd g = outputs_fupd (f ∘ g)) ∧
   ∀h g f. outputs_fupd f ∘ outputs_fupd g ∘ h = outputs_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. commit_limit_fupd f ∘ commit_limit_fupd g = commit_limit_fupd (f ∘ g)) ∧
   ∀h g f. commit_limit_fupd f ∘ commit_limit_fupd g ∘ h = commit_limit_fupd (f ∘ g) ∘ h) ∧
  (∀g f. write_limit_fupd f ∘ write_limit_fupd g = write_limit_fupd (f ∘ g)) ∧
  ∀h g f. write_limit_fupd f ∘ write_limit_fupd g ∘ h = write_limit_fupd (f ∘ g) ∘ h
```

#### `forge_airlockFfi.airlock_io_fupdselfid`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. a with boot_key := a.boot_key = a) ∧ (∀a. a with boot_fail := a.boot_fail = a) ∧
  (∀a. a with slotA := a.slotA = a) ∧ (∀a. a with slotB := a.slotB = a) ∧
  (∀a. a with inputs := a.inputs = a) ∧ (∀a. a with outputs := a.outputs = a) ∧
  (∀a. a with commit_limit := a.commit_limit = a) ∧ ∀a. a with write_limit := a.write_limit = a
```

#### `forge_airlockFfi.airlock_io_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀l b l0 l1 l2 l3 $o o0. P (airlock_io l b l0 l1 l2 l3 $o o0)) ⇒ ∀a. P a
```

#### `forge_airlockFfi.airlock_io_literal_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l31 b1 l21 l11 l01 l1 o01 o1 l32 b2 l22 l12 l02 l2 o02 o2.
    <|boot_key := l31; boot_fail := b1; slotA := l21; slotB := l11; inputs := l01; outputs := l1;
      commit_limit := o01; write_limit := o1|> =
    <|boot_key := l32; boot_fail := b2; slotA := l22; slotB := l12; inputs := l02; outputs := l2;
      commit_limit := o02; write_limit := o2|> ⇔
    l31 = l32 ∧ (b1 ⇔ b2) ∧ l21 = l22 ∧ l11 = l12 ∧ l01 = l02 ∧ l1 = l2 ∧ o01 = o02 ∧ o1 = o2
```

#### `forge_airlockFfi.airlock_io_literal_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a. ∃l3 b l2 l1 l0 l o0 $o.
    a =
    <|boot_key := l3; boot_fail := b; slotA := l2; slotB := l1; inputs := l0; outputs := l;
      commit_limit := o0; write_limit := $o|>
```

#### `forge_airlockFfi.airlock_io_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀aa. ∃l b l0 l1 l2 l3 $o o0. aa = airlock_io l b l0 l1 l2 l3 $o o0
```

#### `forge_airlockFfi.airlock_io_updates_eq_literal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a l3 b l2 l1 l0 l o0 $o.
    a with
    <|boot_key := l3; boot_fail := b; slotA := l2; slotB := l1; inputs := l0; outputs := l;
      commit_limit := o0; write_limit := $o|> =
    <|boot_key := l3; boot_fail := b; slotA := l2; slotB := l1; inputs := l0; outputs := l;
      commit_limit := o0; write_limit := $o|>
```

#### `forge_airlockFfi.call_FFI_airlock_outputs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st st'.
    call_FFI_rel st st' ∧ st.oracle = airlock_ffi_oracle ⇒
    st'.oracle = airlock_ffi_oracle ∧
    st'.ffi_state.outputs =
    st.ffi_state.outputs ++ sent_frames128_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
```

#### `forge_airlockFfi.datatype_airlock_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE
    (record airlock_io boot_key boot_fail slotA slotB inputs outputs commit_limit write_limit)
```

#### `forge_airlockFfi.datatype_frame128`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE (frame128 Frame128)
```

#### `forge_airlockFfi.decode_encode_airlock_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. decode_airlock_io (encode_airlock_io io) = SOME io
```

#### `forge_airlockFfi.encode_airlock_io_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y. encode_airlock_io x = encode_airlock_io y ⇔ x = y
```

#### `forge_airlockFfi.ffi_airlock_lengths`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀conf bytes io bytes' io'.
     ffi_bootload conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (∀conf bytes io bytes' io'.
     ffi_commit conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (∀conf bytes io bytes' io'.
     ffi_al_recv64 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  ∀conf bytes io bytes' io'.
    ffi_al_send128 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes
```

#### `forge_airlockFfi.frame128_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a0' a1' a2' a3' a4' a5' a6' a7' a8' a9'
      a10' a11' a12' a13' a14' a15'.
    Frame128 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =
    Frame128 a0' a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' ⇔
    a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3' ∧ a4 = a4' ∧ a5 = a5' ∧ a6 = a6' ∧ a7 = a7' ∧
    a8 = a8' ∧ a9 = a9' ∧ a10 = a10' ∧ a11 = a11' ∧ a12 = a12' ∧ a13 = a13' ∧ a14 = a14' ∧
    a15 = a15'
```

#### `forge_airlockFfi.frame128_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15.
    h (Frame128 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) =
    f0 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
```

#### `forge_airlockFfi.frame128_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧
    (∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15.
       M' = Frame128 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 ⇒
       f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =
       f' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) ⇒
    frame128_CASE M f = frame128_CASE M' f'
```

#### `forge_airlockFfi.frame128_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ frame128_CASE x f = v ⇔
  ∃c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14.
    x = Frame128 c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 ∧
    f c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 = v
```

#### `forge_airlockFfi.frame128_decode_encode_bytes`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. LENGTH bs = 128 ⇒ frame128_encode (frame128_decode bs) = bs
```

#### `forge_airlockFfi.frame128_encode_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fr. LENGTH (frame128_encode fr) = 128
```

#### `forge_airlockFfi.frame128_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14.
         P (Frame128 c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)) ⇒
      ∀f. P f
```

#### `forge_airlockFfi.frame128_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ff. ∃c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14.
    ff = Frame128 c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14
```

#### `forge_airlockFfi.frame128_roundtrip`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fr. frame128_decode (frame128_encode fr) = fr
```

#### `forge_airlockFfi.le64_take_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ le64_take (b0::b1::b2::b3::b4::b5::b6::b7::rest) = (le64_decode b0 b1 b2 b3 b4 b5 b6 b7,rest) ∧
  le64_take [] = (0w,[]) ∧ le64_take [v] = (0w,[]) ∧ le64_take [v; v4] = (0w,[]) ∧
  le64_take [v; v4; v8] = (0w,[]) ∧ le64_take [v; v4; v8; v12] = (0w,[]) ∧
  le64_take [v; v4; v8; v12; v16] = (0w,[]) ∧ le64_take [v; v4; v8; v12; v16; v20] = (0w,[]) ∧
  le64_take [v; v4; v8; v12; v16; v20; v24] = (0w,[])
```

#### `forge_airlockFfi.le64_take_encode`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w rest. le64_take (le64_encode w ++ rest) = (w,rest)
```

#### `forge_airlockFfi.le64_take_encode_nil`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. le64_take (le64_encode w) = (w,[])
```

#### `forge_airlockFfi.le64_take_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀b0 b1 b2 b3 b4 b5 b6 b7 rest. P (b0::b1::b2::b3::b4::b5::b6::b7::rest)) ∧ P [] ∧
      (∀v. P [v]) ∧ (∀v v4. P [v; v4]) ∧ (∀v v4 v8. P [v; v4; v8]) ∧
      (∀v v4 v8 v12. P [v; v4; v8; v12]) ∧ (∀v v4 v8 v12 v16. P [v; v4; v8; v12; v16]) ∧
      (∀v v4 v8 v12 v16 v20. P [v; v4; v8; v12; v16; v20]) ∧
      (∀v v4 v8 v12 v16 v20 v24. P [v; v4; v8; v12; v16; v20; v24]) ⇒
      ∀v. P v
```

#### `forge_airlockFfi.sent_frames128_of_append`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs ys. sent_frames128_of (xs ++ ys) = sent_frames128_of xs ++ sent_frames128_of ys
```

#### `forge_airlockFfi.sent_frames128_of_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sent_frames128_of [] = [] ∧
  (∀rest n conf bs.
     sent_frames128_of (IO_event (ExtCall n) conf bs::rest) =
     (if n = «send128» ∧ 129 ≤ LENGTH bs then [TAKE 128 (DROP 1 (MAP FST bs))] else []) ++
     sent_frames128_of rest) ∧
  ∀v9 v4 v3 rest. sent_frames128_of (IO_event (SharedMem v9) v3 v4::rest) = sent_frames128_of rest
```

#### `forge_airlockFfi.sent_frames128_of_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. P [] ∧ (∀n conf bs rest. P rest ⇒ P (IO_event (ExtCall n) conf bs::rest)) ∧
      (∀v9 v3 v4 rest. P rest ⇒ P (IO_event (SharedMem v9) v3 v4::rest)) ⇒
      ∀v. P v
```

</details>

<details>
<summary><strong><code>forge_airlockContract</code></strong> — M3 6-Syscall Contract (53 definitions, 21 theorems)</summary>

SHA-256 pinned M3 256 KB RX slot, 52-word veneers, 168-word airlock shim, and 6-syscall Linux AArch64 dual-slot OS contract.

### Definitions

#### `forge_airlockContract.FORGE_M3_CAKE_MAIN_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_CAKE_MAIN = 0x4000D0w
```

#### `forge_airlockContract.FORGE_M3_CML_EXIT_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_CML_EXIT = 0x45027Cw
```

#### `forge_airlockContract.FORGE_M3_CML_INSTALL_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_CML_INSTALL = 0x450290w
```

#### `forge_airlockContract.FORGE_M3_EXIT_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_EXIT_VENEER = 0x4000C0w
```

#### `forge_airlockContract.FORGE_M3_FFIBOOT_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFIBOOT_VENEER = 0x4000A0w
```

#### `forge_airlockContract.FORGE_M3_FFIBOOT_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFIBOOT = 0x4501A4w
```

#### `forge_airlockContract.FORGE_M3_FFICOMMIT_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFICOMMIT_VENEER = 0x400070w
```

#### `forge_airlockContract.FORGE_M3_FFICOMMIT_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFICOMMIT = 0x45011Cw
```

#### `forge_airlockContract.FORGE_M3_FFIRECV_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFIRECV_VENEER = 0x400080w
```

#### `forge_airlockContract.FORGE_M3_FFIRECV_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFIRECV = 0x450040w
```

#### `forge_airlockContract.FORGE_M3_FFISEND_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFISEND_VENEER = 0x400090w
```

#### `forge_airlockContract.FORGE_M3_FFISEND_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_FFISEND = 0x4500C0w
```

#### `forge_airlockContract.FORGE_M3_INSTALL_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_INSTALL_VENEER = 0x4000B0w
```

#### `forge_airlockContract.FORGE_M3_MAX_CODE_BYTES_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_MAX_CODE_BYTES = 261936
```

#### `forge_airlockContract.FORGE_M3_RX_TMP_BYTES_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_RX_TMP_BYTES = 544
```

#### `forge_airlockContract.FORGE_M3_SHIM_BASE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_SHIM_BASE = 0x450000w
```

#### `forge_airlockContract.FORGE_M3_SHIM_END_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_SHIM_END = 0x4502A0w
```

#### `forge_airlockContract.FORGE_M3_VENEERS_BASE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_M3_VENEERS_BASE = 0x400000w
```

#### `forge_airlockContract.forge_m3_code_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end. forge_m3_code_region cb_end = {a | FORGE_M3_CAKE_MAIN ≤₊ a ∧ a <₊ cb_end}
```

#### `forge_airlockContract.forge_m3_mc_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end ffi_names_l ffi_if inst_if.
    forge_m3_mc_slot cb_end bm_buf_end ffi_names_l ffi_if inst_if =
    <|prog_addresses := forge_m3_prog_addresses cb_end bm_buf_end; shared_addresses := ∅;
      ffi_entry_pcs :=
        [FORGE_M3_FFIBOOT_VENEER; FORGE_M3_FFISEND_VENEER; FORGE_M3_FFIRECV_VENEER;
         FORGE_M3_FFICOMMIT_VENEER]; ffi_names := ffi_names_l; ptr_reg := 0; len_reg := 1;
      ptr2_reg := 2; len2_reg := 3; ffi_interfer := ffi_if;
      callee_saved_regs := [19; 20; 21; 22; 23; 24; 25; 26; 27; 28]; next_interfer := K I;
      halt_pc := FORGE_M3_EXIT_VENEER; install_pc := FORGE_M3_INSTALL_VENEER;
      install_interfer := inst_if; target := arm8_target; mmio_info := []|>
```

#### `forge_airlockContract.forge_m3_prog_addresses_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end.
    forge_m3_prog_addresses cb_end bm_buf_end =
    forge_m3_code_region cb_end ∪ forge_bitmaps_region_slot bm_buf_end ∪ forge_heap_stack_region
```

#### `forge_airlockContract.forge_m3_rx_tmp_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_m3_rx_tmp_region = {a | FORGE_RX_TMP ≤₊ a ∧ a <₊ FORGE_RX_TMP + 544w}
```

#### `forge_airlockContract.forge_m3_shim_code_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_m3_shim_code_region =
  {a | FORGE_M3_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_M3_CAKE_MAIN} ∪
  {a | FORGE_M3_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_M3_SHIM_END}
```

#### `forge_airlockContract.forge_m3_slot_loaded_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bytes bitmaps ms0.
    forge_m3_slot_loaded bytes bitmaps ms0 ⇔
    (let
       cb_begin = m3_slot_cb_begin (LENGTH bytes);
       cb_end = m3_slot_cb_end (LENGTH bytes);
       bm_buf_end = slot_bm_buf_end (LENGTH bitmaps)
     in
       0 < LENGTH bytes ∧ LENGTH bytes ≤ FORGE_M3_MAX_CODE_BYTES ∧
       LENGTH bitmaps ≤ FORGE_MAX_BITMAP_WORDS ∧ arm8_ok (erase ms0) ∧ sp_ok ms0 ∧
       ms0.PC = FORGE_M3_SHIM_BASE ∧ m3_shim_loaded_slot cb_begin cb_end bm_buf_end ms0.MEM ∧
       read_bytearray FORGE_M3_CAKE_MAIN (LENGTH bytes)
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (ms0.MEM a) else NONE) =
       SOME bytes ∧
       ∀i. i < LENGTH bitmaps ⇒
           mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) = n2w bitmaps❲i❳)
```

#### `forge_airlockContract.forge_m3_slot_veneers_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockContract.forge_shim_airlock_words_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_shim_airlock_words = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockContract.m3_os_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. m3_os_ABS (m3_os_REP a) = a) ∧ ∀r. (λx. T) r ⇔ m3_os_REP (m3_os_ABS r) = r
```

#### `forge_airlockContract.m3_os_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ m3_os_CONS = m3_os_ABS
```

#### `forge_airlockContract.m3_os_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_airlockContract.m3_os_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 f. m3_os_CASE (m3_os a0 a1 a2 a3 a4) f = f a0 a1 a2 a3 a4
```

#### `forge_airlockContract.m3_os_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4.
    m3_os_size (m3_os a0 a1 a2 a3 a4) =
    1 +
    (list_size w2n a0 +
     (list_size w2n a1 + (list_size w2n a2 + (list_size w2n a3 + list_size w2n a4))))
```

#### `forge_airlockContract.m3_real_interfer_ok_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end cbspace ffi_names_l B ffi_if inst_if.
    m3_real_interfer_ok_slot cb_end bm_buf_end cbspace ffi_names_l B ffi_if inst_if ⇔
    (let
       mc =
         forge_m3_mc_slot cb_end bm_buf_end ffi_names_l
           (λk (i,bs,s). erase (ffi_if k (i,bs,restore B s)))
           (λk (bs,s). erase (inst_if k (bs,restore B s)))
     in
       ffi_interfer_ok FORGE_M3_CAKE_MAIN mc ∧ install_interfer_ok FORGE_M3_CAKE_MAIN cbspace mc ∧
       (∀k i bs s.
          bits_of s = B ⇒ bits_of (ffi_if k (i,bs,s)) = B ∧ (ffi_if k (i,bs,s)).SP_EL0 = s.SP_EL0) ∧
       ∀k bs s.
         bits_of s = B ⇒ bits_of (inst_if k (bs,s)) = B ∧ (inst_if k (bs,s)).SP_EL0 = s.SP_EL0)
```

#### `forge_airlockContract.m3_shim_loaded_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end mem.
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end mem ⇔
    words32_in_mem FORGE_M3_VENEERS_BASE (forge_m3_slot_veneers cb_begin cb_end bm_buf_end) mem ∧
    words32_in_mem FORGE_M3_SHIM_BASE forge_shim_airlock_words mem
```

#### `forge_airlockContract.m3_slot_cb_begin_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len. m3_slot_cb_begin code_len = FORGE_M3_CAKE_MAIN + n2w code_len
```

#### `forge_airlockContract.m3_slot_cb_end_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len. m3_slot_cb_end code_len = align_up_64k (m3_slot_cb_begin code_len)
```

#### `forge_airlockContract.m3_slot_cbspace_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len. m3_slot_cbspace code_len = w2n (m3_slot_cb_end code_len − m3_slot_cb_begin code_len)
```

#### `forge_airlockContract.m3_slot_layout_ok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ⇔
    FORGE_M3_CAKE_MAIN <₊ cb_begin ∧ cb_begin ≤₊ cb_end ∧ cb_end ≤₊ FORGE_SLOT_END ∧
    FORGE_CAKE_BITMAPS ≤₊ bm_buf_end ∧ bm_buf_end ≤₊ FORGE_DATA_SLOT_END
```

#### `forge_airlockContract.m3_whole_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err os s os' s'.
    m3_whole_step allow_err (os,s) (os',s') ⇔
    ¬is_svc0_at s ∧ NextStateARM8 s = SOME s' ∧ os' = os ∨
    is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 0w ∧
    (∃rest. svc_read_fd_rel 0w allow_err os.inp s s' rest ∧ os' = os with inp := rest) ∨
    is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 4w ∧
    (∃rest. svc_read_fd_rel 4w allow_err os.key_in s s' rest ∧ os' = os with key_in := rest) ∨
    is_svc0_at s ∧ s.REG 8w = 64w ∧ s.REG 0w = 1w ∧
    (∃chunk.
       (if allow_err then svc_write_rel else svc_write_noerr_rel) s s' chunk ∧
       os' = os with out := os.out ++ chunk) ∨
    is_svc0_at s ∧ s.REG 8w = 67w ∧ svc_pread64_rel allow_err os.disk s s' ∧ os' = os ∨
    is_svc0_at s ∧ s.REG 8w = 68w ∧
    (∃disk'. svc_pwrite64_rel allow_err os.disk s s' disk' ∧ os' = os with disk := disk') ∨
    is_svc0_at s ∧ s.REG 8w = 83w ∧
    ∃dur'. svc_fdatasync_rel allow_err os.disk os.durable s s' dur' ∧ os' = os with durable := dur'
```

#### `forge_airlockContract.patch_bytes_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀off chunk buf.
    patch_bytes off chunk buf =
    (let
       padded = if LENGTH buf < off then buf ++ REPLICATE (off − LENGTH buf) 0w else buf
     in
       TAKE off padded ++ chunk ++ DROP (off + LENGTH chunk) padded)
```

#### `forge_airlockContract.recordtype_m3_os_seldef_disk_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).disk = l0
```

#### `forge_airlockContract.recordtype_m3_os_seldef_disk_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with disk updated_by f = m3_os l (f l0) l1 l2 l3
```

#### `forge_airlockContract.recordtype_m3_os_seldef_durable_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).durable = l1
```

#### `forge_airlockContract.recordtype_m3_os_seldef_durable_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with durable updated_by f = m3_os l l0 (f l1) l2 l3
```

#### `forge_airlockContract.recordtype_m3_os_seldef_inp_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).inp = l2
```

#### `forge_airlockContract.recordtype_m3_os_seldef_inp_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with inp updated_by f = m3_os l l0 l1 (f l2) l3
```

#### `forge_airlockContract.recordtype_m3_os_seldef_key_in_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).key_in = l
```

#### `forge_airlockContract.recordtype_m3_os_seldef_key_in_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with key_in updated_by f = m3_os (f l) l0 l1 l2 l3
```

#### `forge_airlockContract.recordtype_m3_os_seldef_out_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).out = l3
```

#### `forge_airlockContract.recordtype_m3_os_seldef_out_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with out updated_by f = m3_os l l0 l1 l2 (f l3)
```

#### `forge_airlockContract.svc_fdatasync_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err disk dur s s' dur'.
    svc_fdatasync_rel allow_err disk dur s s' dur' ⇔
    s.REG 8w = 83w ∧ s.REG 0w = 3w ∧ svc_frame_rel s s' ∧ s'.MEM = s.MEM ∧
    (s'.REG 0w = -4w ∧ dur' = dur ∨ s'.REG 0w = 0w ∧ dur' = disk ∨
     allow_err ∧ s'.REG 0w ≠ 0w ∧ s'.REG 0w ≠ -4w ∧ dur' = dur)
```

#### `forge_airlockContract.svc_pread64_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err disk s s'.
    svc_pread64_rel allow_err disk s s' ⇔
    s.REG 8w = 67w ∧ s.REG 0w = 3w ∧ svc_frame_rel s s' ∧
    (let
       off = w2n (s.REG 3w);
       cnt = w2n (s.REG 2w)
     in
       s'.REG 0w = -4w ∧ s'.MEM = s.MEM ∨ s'.REG 0w = 0w ∧ LENGTH disk ≤ off ∧ s'.MEM = s.MEM ∨
       allow_err ∧ word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w ∧ s'.MEM = s.MEM ∨
       ∃n. 1 ≤ n ∧ n ≤ cnt ∧ off + n ≤ LENGTH disk ∧ s'.REG 0w = n2w n ∧
           s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n (DROP off disk)) s.MEM)
```

#### `forge_airlockContract.svc_pwrite64_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err disk s s' disk'.
    svc_pwrite64_rel allow_err disk s s' disk' ⇔
    s.REG 8w = 68w ∧ s.REG 0w = 3w ∧ svc_frame_rel s s' ∧ s'.MEM = s.MEM ∧
    (let
       off = w2n (s.REG 3w);
       cnt = w2n (s.REG 2w)
     in
       s'.REG 0w = -4w ∧ disk' = disk ∨
       allow_err ∧ (s'.REG 0w = 0w ∨ word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w) ∧ disk' = disk ∨
       ∃n. 1 ≤ n ∧ n ≤ cnt ∧ s'.REG 0w = n2w n ∧
           disk' = patch_bytes off (GENLIST (λi. s.MEM (s.REG 1w + n2w i)) n) disk)
```

#### `forge_airlockContract.svc_read_fd_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fd allow_err src s s' rest.
    svc_read_fd_rel fd allow_err src s s' rest ⇔
    s.REG 8w = 63w ∧ s.REG 0w = fd ∧ svc_frame_rel s s' ∧
    (s'.REG 0w = -4w ∧ s'.MEM = s.MEM ∧ rest = src ∨
     s'.REG 0w = 0w ∧ src = [] ∧ s'.MEM = s.MEM ∧ rest = [] ∨
     allow_err ∧ word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w ∧ s'.MEM = s.MEM ∧ rest = src ∨
     ∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ n ≤ LENGTH src ∧ s'.REG 0w = n2w n ∧
         s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n src) s.MEM ∧ rest = DROP n src)
```

### Theorems

#### `forge_airlockContract.EXISTS_m3_os`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∃m. P m) ⇔ ∃l3 l2 l1 l0 l. P <|key_in := l3; disk := l2; durable := l1; inp := l0; out := l|>
```

#### `forge_airlockContract.FORALL_m3_os`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀m. P m) ⇔ ∀l3 l2 l1 l0 l. P <|key_in := l3; disk := l2; durable := l1; inp := l0; out := l|>
```

#### `forge_airlockContract.datatype_m3_os`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE (record m3_os key_in disk durable inp out)
```

#### `forge_airlockContract.m3_os_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a0' a1' a2' a3' a4'.
    m3_os a0 a1 a2 a3 a4 = m3_os a0' a1' a2' a3' a4' ⇔
    a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3' ∧ a4 = a4'
```

#### `forge_airlockContract.m3_os_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2 a3 a4. h (m3_os a0 a1 a2 a3 a4) = f0 a0 a1 a2 a3 a4
```

#### `forge_airlockContract.m3_os_accessors`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).key_in = l) ∧
  (∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).disk = l0) ∧
  (∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).durable = l1) ∧
  (∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).inp = l2) ∧ ∀l l0 l1 l2 l3. (m3_os l l0 l1 l2 l3).out = l3
```

#### `forge_airlockContract.m3_os_accfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀m f. (m with disk updated_by f).key_in = m.key_in) ∧
  (∀m f. (m with durable updated_by f).key_in = m.key_in) ∧
  (∀m f. (m with inp updated_by f).key_in = m.key_in) ∧
  (∀m f. (m with out updated_by f).key_in = m.key_in) ∧
  (∀m f. (m with key_in updated_by f).disk = m.disk) ∧
  (∀m f. (m with durable updated_by f).disk = m.disk) ∧
  (∀m f. (m with inp updated_by f).disk = m.disk) ∧
  (∀m f. (m with out updated_by f).disk = m.disk) ∧
  (∀m f. (m with key_in updated_by f).durable = m.durable) ∧
  (∀m f. (m with disk updated_by f).durable = m.durable) ∧
  (∀m f. (m with inp updated_by f).durable = m.durable) ∧
  (∀m f. (m with out updated_by f).durable = m.durable) ∧
  (∀m f. (m with key_in updated_by f).inp = m.inp) ∧
  (∀m f. (m with disk updated_by f).inp = m.inp) ∧
  (∀m f. (m with durable updated_by f).inp = m.inp) ∧
  (∀m f. (m with out updated_by f).inp = m.inp) ∧ (∀m f. (m with key_in updated_by f).out = m.out) ∧
  (∀m f. (m with disk updated_by f).out = m.out) ∧
  (∀m f. (m with durable updated_by f).out = m.out) ∧
  (∀m f. (m with inp updated_by f).out = m.out) ∧
  (∀m f. (m with key_in updated_by f).key_in = f m.key_in) ∧
  (∀m f. (m with disk updated_by f).disk = f m.disk) ∧
  (∀m f. (m with durable updated_by f).durable = f m.durable) ∧
  (∀m f. (m with inp updated_by f).inp = f m.inp) ∧ ∀m f. (m with out updated_by f).out = f m.out
```

#### `forge_airlockContract.m3_os_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧ (∀a0 a1 a2 a3 a4. M' = m3_os a0 a1 a2 a3 a4 ⇒ f a0 a1 a2 a3 a4 = f' a0 a1 a2 a3 a4) ⇒
    m3_os_CASE M f = m3_os_CASE M' f'
```

#### `forge_airlockContract.m3_os_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ m3_os_CASE x f = v ⇔ ∃l l0 l1 l2 l3. x = m3_os l l0 l1 l2 l3 ∧ f l l0 l1 l2 l3 = v
```

#### `forge_airlockContract.m3_os_component_equality`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m1 m2.
    m1 = m2 ⇔
    m1.key_in = m2.key_in ∧ m1.disk = m2.disk ∧ m1.durable = m2.durable ∧ m1.inp = m2.inp ∧
    m1.out = m2.out
```

#### `forge_airlockContract.m3_os_fn_updates`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with key_in updated_by f = m3_os (f l) l0 l1 l2 l3) ∧
  (∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with disk updated_by f = m3_os l (f l0) l1 l2 l3) ∧
  (∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with durable updated_by f = m3_os l l0 (f l1) l2 l3) ∧
  (∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with inp updated_by f = m3_os l l0 l1 (f l2) l3) ∧
  ∀f l l0 l1 l2 l3. m3_os l l0 l1 l2 l3 with out updated_by f = m3_os l l0 l1 l2 (f l3)
```

#### `forge_airlockContract.m3_os_fupdcanon`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀m g f.
     m with <|disk updated_by f; key_in updated_by g|> =
     m with <|key_in updated_by g; disk updated_by f|>) ∧
  (∀m g f.
     m with <|durable updated_by f; key_in updated_by g|> =
     m with <|key_in updated_by g; durable updated_by f|>) ∧
  (∀m g f.
     m with <|durable updated_by f; disk updated_by g|> =
     m with <|disk updated_by g; durable updated_by f|>) ∧
  (∀m g f.
     m with <|inp updated_by f; key_in updated_by g|> =
     m with <|key_in updated_by g; inp updated_by f|>) ∧
  (∀m g f.
     m with <|inp updated_by f; disk updated_by g|> = m with <|disk updated_by g; inp updated_by f|>) ∧
  (∀m g f.
     m with <|inp updated_by f; durable updated_by g|> =
     m with <|durable updated_by g; inp updated_by f|>) ∧
  (∀m g f.
     m with <|out updated_by f; key_in updated_by g|> =
     m with <|key_in updated_by g; out updated_by f|>) ∧
  (∀m g f.
     m with <|out updated_by f; disk updated_by g|> = m with <|disk updated_by g; out updated_by f|>) ∧
  (∀m g f.
     m with <|out updated_by f; durable updated_by g|> =
     m with <|durable updated_by g; out updated_by f|>) ∧
  ∀m g f.
    m with <|out updated_by f; inp updated_by g|> = m with <|inp updated_by g; out updated_by f|>
```

#### `forge_airlockContract.m3_os_fupdcanon_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f. disk_fupd f ∘ key_in_fupd g = key_in_fupd g ∘ disk_fupd f) ∧
   ∀h g f. disk_fupd f ∘ key_in_fupd g ∘ h = key_in_fupd g ∘ disk_fupd f ∘ h) ∧
  ((∀g f. durable_fupd f ∘ key_in_fupd g = key_in_fupd g ∘ durable_fupd f) ∧
   ∀h g f. durable_fupd f ∘ key_in_fupd g ∘ h = key_in_fupd g ∘ durable_fupd f ∘ h) ∧
  ((∀g f. durable_fupd f ∘ disk_fupd g = disk_fupd g ∘ durable_fupd f) ∧
   ∀h g f. durable_fupd f ∘ disk_fupd g ∘ h = disk_fupd g ∘ durable_fupd f ∘ h) ∧
  ((∀g f. inp_fupd f ∘ key_in_fupd g = key_in_fupd g ∘ inp_fupd f) ∧
   ∀h g f. inp_fupd f ∘ key_in_fupd g ∘ h = key_in_fupd g ∘ inp_fupd f ∘ h) ∧
  ((∀g f. inp_fupd f ∘ disk_fupd g = disk_fupd g ∘ inp_fupd f) ∧
   ∀h g f. inp_fupd f ∘ disk_fupd g ∘ h = disk_fupd g ∘ inp_fupd f ∘ h) ∧
  ((∀g f. inp_fupd f ∘ durable_fupd g = durable_fupd g ∘ inp_fupd f) ∧
   ∀h g f. inp_fupd f ∘ durable_fupd g ∘ h = durable_fupd g ∘ inp_fupd f ∘ h) ∧
  ((∀g f. out_fupd f ∘ key_in_fupd g = key_in_fupd g ∘ out_fupd f) ∧
   ∀h g f. out_fupd f ∘ key_in_fupd g ∘ h = key_in_fupd g ∘ out_fupd f ∘ h) ∧
  ((∀g f. out_fupd f ∘ disk_fupd g = disk_fupd g ∘ out_fupd f) ∧
   ∀h g f. out_fupd f ∘ disk_fupd g ∘ h = disk_fupd g ∘ out_fupd f ∘ h) ∧
  ((∀g f. out_fupd f ∘ durable_fupd g = durable_fupd g ∘ out_fupd f) ∧
   ∀h g f. out_fupd f ∘ durable_fupd g ∘ h = durable_fupd g ∘ out_fupd f ∘ h) ∧
  (∀g f. out_fupd f ∘ inp_fupd g = inp_fupd g ∘ out_fupd f) ∧
  ∀h g f. out_fupd f ∘ inp_fupd g ∘ h = inp_fupd g ∘ out_fupd f ∘ h
```

#### `forge_airlockContract.m3_os_fupdfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀m g f. m with <|key_in updated_by f; key_in updated_by g|> = m with key_in updated_by f ∘ g) ∧
  (∀m g f. m with <|disk updated_by f; disk updated_by g|> = m with disk updated_by f ∘ g) ∧
  (∀m g f. m with <|durable updated_by f; durable updated_by g|> = m with durable updated_by f ∘ g) ∧
  (∀m g f. m with <|inp updated_by f; inp updated_by g|> = m with inp updated_by f ∘ g) ∧
  ∀m g f. m with <|out updated_by f; out updated_by g|> = m with out updated_by f ∘ g
```

#### `forge_airlockContract.m3_os_fupdfupds_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f. key_in_fupd f ∘ key_in_fupd g = key_in_fupd (f ∘ g)) ∧
   ∀h g f. key_in_fupd f ∘ key_in_fupd g ∘ h = key_in_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. disk_fupd f ∘ disk_fupd g = disk_fupd (f ∘ g)) ∧
   ∀h g f. disk_fupd f ∘ disk_fupd g ∘ h = disk_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. durable_fupd f ∘ durable_fupd g = durable_fupd (f ∘ g)) ∧
   ∀h g f. durable_fupd f ∘ durable_fupd g ∘ h = durable_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. inp_fupd f ∘ inp_fupd g = inp_fupd (f ∘ g)) ∧
   ∀h g f. inp_fupd f ∘ inp_fupd g ∘ h = inp_fupd (f ∘ g) ∘ h) ∧
  (∀g f. out_fupd f ∘ out_fupd g = out_fupd (f ∘ g)) ∧
  ∀h g f. out_fupd f ∘ out_fupd g ∘ h = out_fupd (f ∘ g) ∘ h
```

#### `forge_airlockContract.m3_os_fupdselfid`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀m. m with key_in := m.key_in = m) ∧ (∀m. m with disk := m.disk = m) ∧
  (∀m. m with durable := m.durable = m) ∧ (∀m. m with inp := m.inp = m) ∧
  ∀m. m with out := m.out = m
```

#### `forge_airlockContract.m3_os_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀l l0 l1 l2 l3. P (m3_os l l0 l1 l2 l3)) ⇒ ∀m. P m
```

#### `forge_airlockContract.m3_os_literal_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l31 l21 l11 l01 l1 l32 l22 l12 l02 l2.
    <|key_in := l31; disk := l21; durable := l11; inp := l01; out := l1|> =
    <|key_in := l32; disk := l22; durable := l12; inp := l02; out := l2|> ⇔
    l31 = l32 ∧ l21 = l22 ∧ l11 = l12 ∧ l01 = l02 ∧ l1 = l2
```

#### `forge_airlockContract.m3_os_literal_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m. ∃l3 l2 l1 l0 l. m = <|key_in := l3; disk := l2; durable := l1; inp := l0; out := l|>
```

#### `forge_airlockContract.m3_os_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀mm. ∃l l0 l1 l2 l3. mm = m3_os l l0 l1 l2 l3
```

#### `forge_airlockContract.m3_os_updates_eq_literal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m l3 l2 l1 l0 l.
    m with <|key_in := l3; disk := l2; durable := l1; inp := l0; out := l|> =
    <|key_in := l3; disk := l2; durable := l1; inp := l0; out := l|>
```

</details>

<details>
<summary><strong><code>forge_airlockSpec</code></strong> — Pure Spec (M3) (64 definitions, 35 theorems)</summary>

SHA-256 pinned crypto-authenticated crash-atomic airlock spec (keyed-HMAC dual slots, conservation, capability tokens, idempotent retry).

### Definitions

#### `forge_airlockSpec.SLOT_MAGIC_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ SLOT_MAGIC = 0x464F524745534C33w
```

#### `forge_airlockSpec.airlock_init_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_init =
  <|gen := 0w; deposits := 0w; balance := 0w; spent := 0w; refunds := 0w; cap := 0x186A0w;
    allowmask := 7w; nonce := 0w; last_tx := 0w; last_amt := 0w; tx_open := F; tok_seq := 0w;
    tok_op := 0w; tok_dest := 0w; tok_amt := 0w; tok_bal := 0w; tok_tag0 := 0w; tok_tag1 := 0w;
    tok_tag2 := 0w; tok_tag3 := 0w|>
```

#### `forge_airlockSpec.airlock_inv_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st.
    airlock_inv key st ⇔
    st.refunds ≤₊ st.spent ∧ (st.tx_open ⇒ st.last_amt ≤₊ st.spent − st.refunds) ∧
    st.balance ≤₊ st.deposits ∧ st.deposits = st.balance + (st.spent − st.refunds) ∧
    st.spent − st.refunds ≤₊ st.cap ∧
    (st.tok_op ≠ 0w ⇒
     st.balance = st.tok_bal ∧
     (st.tok_tag0,st.tok_tag1,st.tok_tag2,st.tok_tag3) =
     mint_cap_tag key st.tok_seq st.tok_op st.tok_dest st.tok_amt st.tok_bal)
```

#### `forge_airlockSpec.airlock_run_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀key st. airlock_run key st [] = (st,[])) ∧
  ∀key st fr_bs rest.
    airlock_run key st (fr_bs::rest) =
    if LENGTH fr_bs = 64 then
      (let
         (st',resp,_0) = airlock_step key st (frame64_decode fr_bs);
         (st_f,outs) = airlock_run key st' rest
       in
         (st_f,frame128_encode resp::outs))
    else (st,[])
```

#### `forge_airlockSpec.airlock_state_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. airlock_state_ABS (airlock_state_REP a) = a) ∧
  ∀r. (λx. T) r ⇔ airlock_state_REP (airlock_state_ABS r) = r
```

#### `forge_airlockSpec.airlock_state_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_state_CONS = airlock_state_ABS
```

#### `forge_airlockSpec.airlock_state_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_airlockSpec.airlock_state_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 f.
    airlock_state_CASE
      (airlock_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19) f =
    f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
```

#### `forge_airlockSpec.airlock_state_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19.
    airlock_state_size
      (airlock_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19) =
    1 +
    (w2n a0 +
     (w2n a1 +
      (w2n a2 +
       (w2n a3 +
        (w2n a4 +
         (w2n a5 +
          (w2n a6 +
           (w2n a7 +
            (w2n a8 +
             (w2n a9 +
              (bool_size a10 +
               (w2n a11 +
                (w2n a12 +
                 (w2n a13 + (w2n a14 + (w2n a15 + (w2n a16 + (w2n a17 + (w2n a18 + w2n a19)))))))))))))))))))
```

#### `forge_airlockSpec.airlock_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockSpec.al_dest_allowed_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀mask d. al_dest_allowed mask d ⇔ d <₊ 64w ∧ mask ⋙ w2n d && 1w ≠ 0w
```

#### `forge_airlockSpec.al_resp_plain_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ok code st.
    al_resp_plain ok code st =
    Frame128 ok code st.deposits st.balance (st.spent − st.refunds) st.refunds st.nonce st.last_tx
      0w 0w 0w 0w 0w 0w 0w 0w
```

#### `forge_airlockSpec.al_resp_tok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ok code st.
    al_resp_tok ok code st =
    Frame128 ok code st.deposits st.balance (st.spent − st.refunds) st.refunds st.nonce st.last_tx
      st.tok_seq st.tok_op st.tok_dest st.tok_amt st.tok_tag0 st.tok_tag1 st.tok_tag2 st.tok_tag3
```

#### `forge_airlockSpec.bytes32_to_w64x4_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs.
    bytes32_to_w64x4 bs =
    (let
       (w0,r0) = le64_take bs;
       (w1,r1) = le64_take r0;
       (w2,r2) = le64_take r1;
       (w3,_0) = le64_take r2
     in
       (w0,w1,w2,w3))
```

#### `forge_airlockSpec.cap_domain_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ cap_domain = [70w; 79w; 82w; 71w; 69w; 45w; 67w; 65w; 80w; 45w; 86w; 49w]
```

#### `forge_airlockSpec.cap_token_msg_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq op dest amt bal.
    cap_token_msg seq op dest amt bal =
    cap_domain ++ le64_encode seq ++ le64_encode op ++ le64_encode dest ++ le64_encode amt ++
    le64_encode bal
```

#### `forge_airlockSpec.commit_slot_byte_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀gen. commit_slot_byte gen = if gen && 1w = 0w then 1w else 0w
```

#### `forge_airlockSpec.decode_slot_raw_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs.
    decode_slot_raw bs =
    (let
       (magic,r0) = le64_take bs;
       (gen,r1) = le64_take r0;
       (dep,r2) = le64_take r1;
       (bal,r3) = le64_take r2;
       (sp,r4) = le64_take r3;
       (rf,r5) = le64_take r4;
       (cp,r6) = le64_take r5;
       (mask,r7) = le64_take r6;
       (nc,r8) = le64_take r7;
       (ltx,r9) = le64_take r8;
       (lamt,r10) = le64_take r9;
       (txop,r11) = le64_take r10;
       (tseq,r12) = le64_take r11;
       (top,r13) = le64_take r12;
       (tdest,r14) = le64_take r13;
       (tamt,r15) = le64_take r14;
       (tbal,r16) = le64_take r15;
       (tt0,r17) = le64_take r16;
       (tt1,r18) = le64_take r17;
       (tt2,r19) = le64_take r18;
       (tt3,_0) = le64_take r19
     in
       (magic,
        <|gen := gen; deposits := dep; balance := bal; spent := sp; refunds := rf; cap := cp;
          allowmask := mask; nonce := nc; last_tx := ltx; last_amt := lamt; tx_open := (txop ≠ 0w);
          tok_seq := tseq; tok_op := top; tok_dest := tdest; tok_amt := tamt; tok_bal := tbal;
          tok_tag0 := tt0; tok_tag1 := tt1; tok_tag2 := tt2; tok_tag3 := tt3|>))
```

#### `forge_airlockSpec.encode_slot_body_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st.
    encode_slot_body st =
    le64_encode SLOT_MAGIC ++ le64_encode st.gen ++ le64_encode st.deposits ++
    le64_encode st.balance ++ le64_encode st.spent ++ le64_encode st.refunds ++
    le64_encode st.cap ++ le64_encode st.allowmask ++ le64_encode st.nonce ++
    le64_encode st.last_tx ++ le64_encode st.last_amt ++
    le64_encode (if st.tx_open then 1w else 0w) ++ le64_encode st.tok_seq ++
    le64_encode st.tok_op ++ le64_encode st.tok_dest ++ le64_encode st.tok_amt ++
    le64_encode st.tok_bal ++ le64_encode st.tok_tag0 ++ le64_encode st.tok_tag1 ++
    le64_encode st.tok_tag2 ++ le64_encode st.tok_tag3 ++ REPLICATE 56 0w
```

#### `forge_airlockSpec.encode_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st. encode_slot key st = (let body = encode_slot_body st in body ++ hmac_sha256 key body)
```

#### `forge_airlockSpec.mint_cap_tag_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key seq op dest amt bal.
    mint_cap_tag key seq op dest amt bal =
    bytes32_to_w64x4 (hmac_sha256 key (cap_token_msg seq op dest amt bal))
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_allowmask_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).allowmask = c5
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_allowmask_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    allowmask updated_by f =
    airlock_state c c0 c1 c2 c3 c4 (f c5) c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_balance_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).balance = c1
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_balance_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    balance updated_by f =
    airlock_state c c0 (f c1) c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_cap_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).cap = c4
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_cap_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    cap updated_by f =
    airlock_state c c0 c1 c2 c3 (f c4) c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_deposits_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).deposits = c0
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_deposits_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    deposits updated_by f =
    airlock_state c (f c0) c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_gen_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).gen = c
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_gen_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    gen updated_by f =
    airlock_state (f c) c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_last_amt_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).last_amt = c8
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_last_amt_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    last_amt updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 (f c8) b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_last_tx_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).last_tx = c7
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_last_tx_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    last_tx updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 (f c7) c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_nonce_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).nonce = c6
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_nonce_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    nonce updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 (f c6) c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_refunds_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).refunds = c3
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_refunds_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    refunds updated_by f =
    airlock_state c c0 c1 c2 (f c3) c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_spent_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).spent = c2
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_spent_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    spent updated_by f =
    airlock_state c c0 c1 (f c2) c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_amt_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_amt = c12
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_amt_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_amt updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 (f c12) c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_bal_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_bal = c13
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_bal_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_bal updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 (f c13) c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_dest_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_dest = c11
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_dest_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_dest updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 (f c11) c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_op_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_op = c10
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_op_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_op updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 (f c10) c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_seq_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_seq = c9
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_seq_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_seq updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b (f c9) c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag0_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_tag0 = c14
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag0_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_tag0 updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 (f c14) c15 c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag1_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_tag1 = c15
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag1_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_tag1 updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 (f c15) c16 c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag2_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_tag2 = c16
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag2_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_tag2 updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 (f c16) c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag3_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tok_tag3 = c17
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tok_tag3_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tok_tag3 updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 (f c17)
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tx_open_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17).tx_open ⇔ b
```

#### `forge_airlockSpec.recordtype_airlock_state_seldef_tx_open_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 with
    tx_open updated_by f =
    airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 (f b) c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.recover_dual_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key slotA slotB.
    recover_dual_slot key slotA slotB =
    (let
       va = slot_valid key slotA;
       vb = slot_valid key slotB
     in
       if va ∧ vb then
         (let
            sa = SND (decode_slot_raw slotA);
            sb = SND (decode_slot_raw slotB)
          in
            if sa.gen <₊ sb.gen then sb else sa)
       else if va then SND (decode_slot_raw slotA)
       else if vb then SND (decode_slot_raw slotB)
       else airlock_init)
```

#### `forge_airlockSpec.slot_valid_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key bs.
    slot_valid key bs ⇔
    LENGTH bs = 256 ∧
    (let
       (magic,st) = decode_slot_raw bs
     in
       magic = SLOT_MAGIC ∧ st.gen ≠ 0w ∧ DROP 224 bs = hmac_sha256 key (TAKE 224 bs) ∧
       airlock_inv key st)
```

#### `forge_airlockSpec.w64x4_to_bytes32_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w0 w1 w2 w3.
    w64x4_to_bytes32 (w0,w1,w2,w3) =
    le64_encode w0 ++ le64_encode w1 ++ le64_encode w2 ++ le64_encode w3
```

### Theorems

#### `forge_airlockSpec.EXISTS_airlock_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∃a. P a) ⇔
      ∃c17 c16 c15 c14 c13 c12 c11 c10 c9 c8 b c7 c6 c5 c4 c3 c2 c1 c0 c.
        P
          <|gen := c17; deposits := c16; balance := c15; spent := c14; refunds := c13; cap := c12;
            allowmask := c11; nonce := c10; last_tx := c9; last_amt := c8; tx_open := b;
            tok_seq := c7; tok_op := c6; tok_dest := c5; tok_amt := c4; tok_bal := c3;
            tok_tag0 := c2; tok_tag1 := c1; tok_tag2 := c0; tok_tag3 := c|>
```

#### `forge_airlockSpec.FORALL_airlock_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀a. P a) ⇔
      ∀c17 c16 c15 c14 c13 c12 c11 c10 c9 c8 b c7 c6 c5 c4 c3 c2 c1 c0 c.
        P
          <|gen := c17; deposits := c16; balance := c15; spent := c14; refunds := c13; cap := c12;
            allowmask := c11; nonce := c10; last_tx := c9; last_amt := c8; tx_open := b;
            tok_seq := c7; tok_op := c6; tok_dest := c5; tok_amt := c4; tok_bal := c3;
            tok_tag0 := c2; tok_tag1 := c1; tok_tag2 := c0; tok_tag3 := c|>
```

#### `forge_airlockSpec.LENGTH_encode_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st. LENGTH (encode_slot key st) = 256
```

#### `forge_airlockSpec.LENGTH_encode_slot_body`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st. LENGTH (encode_slot_body st) = 224
```

#### `forge_airlockSpec.airlock_base_inv_nat_conservation`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st. airlock_inv key st ⇒ w2n st.deposits = w2n st.balance + (w2n st.spent − w2n st.refunds)
```

#### `forge_airlockSpec.airlock_emitted_token_authentic`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st fr st' w0 w1 w2 w3 w4 w5 w6 w7 tseq top tdest tamt t0 t1 t2 t3 dc.
    airlock_inv key st ∧
    airlock_step key st fr =
    (st',Frame128 w0 w1 w2 w3 w4 w5 w6 w7 tseq top tdest tamt t0 t1 t2 t3,dc) ∧ top ≠ 0w ⇒
    w3 = st'.balance ∧ (t0,t1,t2,t3) = mint_cap_tag key tseq top tdest tamt w3
```

#### `forge_airlockSpec.airlock_exec_eq_run`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inps key st. airlock_exec airlock_step key st inps NONE NONE = airlock_run key st inps
```

#### `forge_airlockSpec.airlock_inv_init`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key. airlock_inv key airlock_init
```

#### `forge_airlockSpec.airlock_inv_recover_dual_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key slotA slotB. airlock_inv key (recover_dual_slot key slotA slotB)
```

#### `forge_airlockSpec.airlock_retry_idempotent`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀key st ag r5 r6 r7.
     st.tok_op = 2w ⇒
     airlock_step key st (Frame64 2w ag st.tok_dest st.tok_amt st.nonce r5 r6 r7) =
     (st,al_resp_tok 1w 5w st,F)) ∧
  ∀key st ag a2 r5 r6 r7.
    st.tok_op = 3w ∧ ¬st.tx_open ⇒
    airlock_step key st (Frame64 3w ag a2 st.tok_amt st.last_tx r5 r6 r7) =
    (st,al_resp_tok 1w 5w st,F)
```

#### `forge_airlockSpec.airlock_run_preserves_inv`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inps key st. airlock_inv key st ⇒ airlock_inv key (FST (airlock_run key st inps))
```

#### `forge_airlockSpec.airlock_safety_denials`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀key st ag d amt nc r5 r6 r7.
     ¬al_dest_allowed st.allowmask d ∧
     ¬(st.tok_op = 2w ∧ nc = st.nonce ∧ d = st.tok_dest ∧ amt = st.tok_amt) ⇒
     airlock_step key st (Frame64 2w ag d amt nc r5 r6 r7) = (st,al_resp_plain 0w 2w st,F)) ∧
  (∀key st ag d amt r5 r6 r7.
     ¬(st.tok_op = 2w ∧ d = st.tok_dest ∧ amt = st.tok_amt) ⇒
     airlock_step key st (Frame64 2w ag d amt st.nonce r5 r6 r7) = (st,al_resp_plain 0w 2w st,F)) ∧
  ∀key st ag a2 amt tx r5 r6 r7.
    ¬st.tx_open ∧ ¬(st.tok_op = 3w ∧ tx = st.last_tx ∧ amt = st.tok_amt) ⇒
    airlock_step key st (Frame64 3w ag a2 amt tx r5 r6 r7) = (st,al_resp_plain 0w 3w st,F)
```

#### `forge_airlockSpec.airlock_state_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a0' a1' a2' a3' a4' a5' a6'
      a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17' a18' a19'.
    airlock_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 =
    airlock_state a0' a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17'
      a18' a19' ⇔
    a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3' ∧ a4 = a4' ∧ a5 = a5' ∧ a6 = a6' ∧ a7 = a7' ∧
    a8 = a8' ∧ a9 = a9' ∧ (a10 ⇔ a10') ∧ a11 = a11' ∧ a12 = a12' ∧ a13 = a13' ∧ a14 = a14' ∧
    a15 = a15' ∧ a16 = a16' ∧ a17 = a17' ∧ a18 = a18' ∧ a19 = a19'
```

#### `forge_airlockSpec.airlock_state_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19.
    h (airlock_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19) =
    f0 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
```

#### `forge_airlockSpec.airlock_state_accessors`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockSpec.airlock_state_accfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockSpec.airlock_state_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧
    (∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19.
       M' = airlock_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 ⇒
       f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 =
       f' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19) ⇒
    airlock_state_CASE M f = airlock_state_CASE M' f'
```

#### `forge_airlockSpec.airlock_state_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_state_CASE x f = v ⇔
  ∃c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    x = airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 ∧
    f c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17 = v
```

#### `forge_airlockSpec.airlock_state_component_equality`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a1 a2.
    a1 = a2 ⇔
    a1.gen = a2.gen ∧ a1.deposits = a2.deposits ∧ a1.balance = a2.balance ∧ a1.spent = a2.spent ∧
    a1.refunds = a2.refunds ∧ a1.cap = a2.cap ∧ a1.allowmask = a2.allowmask ∧ a1.nonce = a2.nonce ∧
    a1.last_tx = a2.last_tx ∧ a1.last_amt = a2.last_amt ∧ (a1.tx_open ⇔ a2.tx_open) ∧
    a1.tok_seq = a2.tok_seq ∧ a1.tok_op = a2.tok_op ∧ a1.tok_dest = a2.tok_dest ∧
    a1.tok_amt = a2.tok_amt ∧ a1.tok_bal = a2.tok_bal ∧ a1.tok_tag0 = a2.tok_tag0 ∧
    a1.tok_tag1 = a2.tok_tag1 ∧ a1.tok_tag2 = a2.tok_tag2 ∧ a1.tok_tag3 = a2.tok_tag3
```

#### `forge_airlockSpec.airlock_state_fn_updates`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockSpec.airlock_state_fupdcanon`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockSpec.airlock_state_fupdcanon_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockSpec.airlock_state_fupdfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g f a. a with <|gen updated_by f; gen updated_by g|> = a with gen updated_by f ∘ g) ∧
  (∀g f a.
     a with <|deposits updated_by f; deposits updated_by g|> = a with deposits updated_by f ∘ g) ∧
  (∀g f a. a with <|balance updated_by f; balance updated_by g|> = a with balance updated_by f ∘ g) ∧
  (∀g f a. a with <|spent updated_by f; spent updated_by g|> = a with spent updated_by f ∘ g) ∧
  (∀g f a. a with <|refunds updated_by f; refunds updated_by g|> = a with refunds updated_by f ∘ g) ∧
  (∀g f a. a with <|cap updated_by f; cap updated_by g|> = a with cap updated_by f ∘ g) ∧
  (∀g f a.
     a with <|allowmask updated_by f; allowmask updated_by g|> = a with allowmask updated_by f ∘ g) ∧
  (∀g f a. a with <|nonce updated_by f; nonce updated_by g|> = a with nonce updated_by f ∘ g) ∧
  (∀g f a. a with <|last_tx updated_by f; last_tx updated_by g|> = a with last_tx updated_by f ∘ g) ∧
  (∀g f a.
     a with <|last_amt updated_by f; last_amt updated_by g|> = a with last_amt updated_by f ∘ g) ∧
  (∀g f a. a with <|tx_open updated_by f; tx_open updated_by g|> = a with tx_open updated_by f ∘ g) ∧
  (∀g f a. a with <|tok_seq updated_by f; tok_seq updated_by g|> = a with tok_seq updated_by f ∘ g) ∧
  (∀g f a. a with <|tok_op updated_by f; tok_op updated_by g|> = a with tok_op updated_by f ∘ g) ∧
  (∀g f a.
     a with <|tok_dest updated_by f; tok_dest updated_by g|> = a with tok_dest updated_by f ∘ g) ∧
  (∀g f a. a with <|tok_amt updated_by f; tok_amt updated_by g|> = a with tok_amt updated_by f ∘ g) ∧
  (∀g f a. a with <|tok_bal updated_by f; tok_bal updated_by g|> = a with tok_bal updated_by f ∘ g) ∧
  (∀g f a.
     a with <|tok_tag0 updated_by f; tok_tag0 updated_by g|> = a with tok_tag0 updated_by f ∘ g) ∧
  (∀g f a.
     a with <|tok_tag1 updated_by f; tok_tag1 updated_by g|> = a with tok_tag1 updated_by f ∘ g) ∧
  (∀g f a.
     a with <|tok_tag2 updated_by f; tok_tag2 updated_by g|> = a with tok_tag2 updated_by f ∘ g) ∧
  ∀g f a. a with <|tok_tag3 updated_by f; tok_tag3 updated_by g|> = a with tok_tag3 updated_by f ∘ g
```

#### `forge_airlockSpec.airlock_state_fupdfupds_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f. gen_fupd f ∘ gen_fupd g = gen_fupd (f ∘ g)) ∧
   ∀h g f. gen_fupd f ∘ gen_fupd g ∘ h = gen_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. deposits_fupd f ∘ deposits_fupd g = deposits_fupd (f ∘ g)) ∧
   ∀h g f. deposits_fupd f ∘ deposits_fupd g ∘ h = deposits_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. balance_fupd f ∘ balance_fupd g = balance_fupd (f ∘ g)) ∧
   ∀h g f. balance_fupd f ∘ balance_fupd g ∘ h = balance_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. spent_fupd f ∘ spent_fupd g = spent_fupd (f ∘ g)) ∧
   ∀h g f. spent_fupd f ∘ spent_fupd g ∘ h = spent_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. refunds_fupd f ∘ refunds_fupd g = refunds_fupd (f ∘ g)) ∧
   ∀h g f. refunds_fupd f ∘ refunds_fupd g ∘ h = refunds_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. cap_fupd f ∘ cap_fupd g = cap_fupd (f ∘ g)) ∧
   ∀h g f. cap_fupd f ∘ cap_fupd g ∘ h = cap_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. allowmask_fupd f ∘ allowmask_fupd g = allowmask_fupd (f ∘ g)) ∧
   ∀h g f. allowmask_fupd f ∘ allowmask_fupd g ∘ h = allowmask_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. nonce_fupd f ∘ nonce_fupd g = nonce_fupd (f ∘ g)) ∧
   ∀h g f. nonce_fupd f ∘ nonce_fupd g ∘ h = nonce_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. last_tx_fupd f ∘ last_tx_fupd g = last_tx_fupd (f ∘ g)) ∧
   ∀h g f. last_tx_fupd f ∘ last_tx_fupd g ∘ h = last_tx_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. last_amt_fupd f ∘ last_amt_fupd g = last_amt_fupd (f ∘ g)) ∧
   ∀h g f. last_amt_fupd f ∘ last_amt_fupd g ∘ h = last_amt_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tx_open_fupd f ∘ tx_open_fupd g = tx_open_fupd (f ∘ g)) ∧
   ∀h g f. tx_open_fupd f ∘ tx_open_fupd g ∘ h = tx_open_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_seq_fupd f ∘ tok_seq_fupd g = tok_seq_fupd (f ∘ g)) ∧
   ∀h g f. tok_seq_fupd f ∘ tok_seq_fupd g ∘ h = tok_seq_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_op_fupd f ∘ tok_op_fupd g = tok_op_fupd (f ∘ g)) ∧
   ∀h g f. tok_op_fupd f ∘ tok_op_fupd g ∘ h = tok_op_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_dest_fupd f ∘ tok_dest_fupd g = tok_dest_fupd (f ∘ g)) ∧
   ∀h g f. tok_dest_fupd f ∘ tok_dest_fupd g ∘ h = tok_dest_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_amt_fupd f ∘ tok_amt_fupd g = tok_amt_fupd (f ∘ g)) ∧
   ∀h g f. tok_amt_fupd f ∘ tok_amt_fupd g ∘ h = tok_amt_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_bal_fupd f ∘ tok_bal_fupd g = tok_bal_fupd (f ∘ g)) ∧
   ∀h g f. tok_bal_fupd f ∘ tok_bal_fupd g ∘ h = tok_bal_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_tag0_fupd f ∘ tok_tag0_fupd g = tok_tag0_fupd (f ∘ g)) ∧
   ∀h g f. tok_tag0_fupd f ∘ tok_tag0_fupd g ∘ h = tok_tag0_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_tag1_fupd f ∘ tok_tag1_fupd g = tok_tag1_fupd (f ∘ g)) ∧
   ∀h g f. tok_tag1_fupd f ∘ tok_tag1_fupd g ∘ h = tok_tag1_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. tok_tag2_fupd f ∘ tok_tag2_fupd g = tok_tag2_fupd (f ∘ g)) ∧
   ∀h g f. tok_tag2_fupd f ∘ tok_tag2_fupd g ∘ h = tok_tag2_fupd (f ∘ g) ∘ h) ∧
  (∀g f. tok_tag3_fupd f ∘ tok_tag3_fupd g = tok_tag3_fupd (f ∘ g)) ∧
  ∀h g f. tok_tag3_fupd f ∘ tok_tag3_fupd g ∘ h = tok_tag3_fupd (f ∘ g) ∘ h
```

#### `forge_airlockSpec.airlock_state_fupdselfid`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. a with gen := a.gen = a) ∧ (∀a. a with deposits := a.deposits = a) ∧
  (∀a. a with balance := a.balance = a) ∧ (∀a. a with spent := a.spent = a) ∧
  (∀a. a with refunds := a.refunds = a) ∧ (∀a. a with cap := a.cap = a) ∧
  (∀a. a with allowmask := a.allowmask = a) ∧ (∀a. a with nonce := a.nonce = a) ∧
  (∀a. a with last_tx := a.last_tx = a) ∧ (∀a. a with last_amt := a.last_amt = a) ∧
  (∀a. a with tx_open := a.tx_open = a) ∧ (∀a. a with tok_seq := a.tok_seq = a) ∧
  (∀a. a with tok_op := a.tok_op = a) ∧ (∀a. a with tok_dest := a.tok_dest = a) ∧
  (∀a. a with tok_amt := a.tok_amt = a) ∧ (∀a. a with tok_bal := a.tok_bal = a) ∧
  (∀a. a with tok_tag0 := a.tok_tag0 = a) ∧ (∀a. a with tok_tag1 := a.tok_tag1 = a) ∧
  (∀a. a with tok_tag2 := a.tok_tag2 = a) ∧ ∀a. a with tok_tag3 := a.tok_tag3 = a
```

#### `forge_airlockSpec.airlock_state_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
         P (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17)) ⇒
      ∀a. P a
```

#### `forge_airlockSpec.airlock_state_literal_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c171 c161 c151 c141 c131 c121 c111 c101 c91 c81 b1 c71 c61 c51 c41 c31 c21 c11 c01 c1 c172 c162
      c152 c142 c132 c122 c112 c102 c92 c82 b2 c72 c62 c52 c42 c32 c22 c12 c02 c2.
    <|gen := c171; deposits := c161; balance := c151; spent := c141; refunds := c131; cap := c121;
      allowmask := c111; nonce := c101; last_tx := c91; last_amt := c81; tx_open := b1;
      tok_seq := c71; tok_op := c61; tok_dest := c51; tok_amt := c41; tok_bal := c31;
      tok_tag0 := c21; tok_tag1 := c11; tok_tag2 := c01; tok_tag3 := c1|> =
    <|gen := c172; deposits := c162; balance := c152; spent := c142; refunds := c132; cap := c122;
      allowmask := c112; nonce := c102; last_tx := c92; last_amt := c82; tx_open := b2;
      tok_seq := c72; tok_op := c62; tok_dest := c52; tok_amt := c42; tok_bal := c32;
      tok_tag0 := c22; tok_tag1 := c12; tok_tag2 := c02; tok_tag3 := c2|> ⇔
    c171 = c172 ∧ c161 = c162 ∧ c151 = c152 ∧ c141 = c142 ∧ c131 = c132 ∧ c121 = c122 ∧
    c111 = c112 ∧ c101 = c102 ∧ c91 = c92 ∧ c81 = c82 ∧ (b1 ⇔ b2) ∧ c71 = c72 ∧ c61 = c62 ∧
    c51 = c52 ∧ c41 = c42 ∧ c31 = c32 ∧ c21 = c22 ∧ c11 = c12 ∧ c01 = c02 ∧ c1 = c2
```

#### `forge_airlockSpec.airlock_state_literal_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a. ∃c17 c16 c15 c14 c13 c12 c11 c10 c9 c8 b c7 c6 c5 c4 c3 c2 c1 c0 c.
    a =
    <|gen := c17; deposits := c16; balance := c15; spent := c14; refunds := c13; cap := c12;
      allowmask := c11; nonce := c10; last_tx := c9; last_amt := c8; tx_open := b; tok_seq := c7;
      tok_op := c6; tok_dest := c5; tok_amt := c4; tok_bal := c3; tok_tag0 := c2; tok_tag1 := c1;
      tok_tag2 := c0; tok_tag3 := c|>
```

#### `forge_airlockSpec.airlock_state_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀aa. ∃c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    aa = airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17
```

#### `forge_airlockSpec.airlock_state_updates_eq_literal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a c17 c16 c15 c14 c13 c12 c11 c10 c9 c8 b c7 c6 c5 c4 c3 c2 c1 c0 c.
    a with
    <|gen := c17; deposits := c16; balance := c15; spent := c14; refunds := c13; cap := c12;
      allowmask := c11; nonce := c10; last_tx := c9; last_amt := c8; tx_open := b; tok_seq := c7;
      tok_op := c6; tok_dest := c5; tok_amt := c4; tok_bal := c3; tok_tag0 := c2; tok_tag1 := c1;
      tok_tag2 := c0; tok_tag3 := c|> =
    <|gen := c17; deposits := c16; balance := c15; spent := c14; refunds := c13; cap := c12;
      allowmask := c11; nonce := c10; last_tx := c9; last_amt := c8; tx_open := b; tok_seq := c7;
      tok_op := c6; tok_dest := c5; tok_amt := c4; tok_bal := c3; tok_tag0 := c2; tok_tag1 := c1;
      tok_tag2 := c0; tok_tag3 := c|>
```

#### `forge_airlockSpec.airlock_step_preserves_inv`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st fr st' resp dc.
    airlock_inv key st ∧ airlock_step key st fr = (st',resp,dc) ⇒ airlock_inv key st'
```

#### `forge_airlockSpec.datatype_airlock_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE
    (record airlock_state gen deposits balance spent refunds cap allowmask nonce last_tx last_amt
       tx_open tok_seq tok_op tok_dest tok_amt tok_bal tok_tag0 tok_tag1 tok_tag2 tok_tag3)
```

#### `forge_airlockSpec.decode_encode_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st. decode_slot_raw (encode_slot key st) = (SLOT_MAGIC,st)
```

#### `forge_airlockSpec.dual_slot_crash_recovery`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st st' bad.
    st.gen ≠ 0w ∧ airlock_inv key st ∧ st'.gen = st.gen + 1w ∧ st.gen ≠ 0xFFFFFFFFFFFFFFFFw ∧
    airlock_inv key st' ∧ ¬slot_valid key bad ⇒
    (recover_dual_slot key (encode_slot key st) bad = st ∧
     recover_dual_slot key bad (encode_slot key st) = st) ∧
    recover_dual_slot key (encode_slot key st) (encode_slot key st') = st' ∧
    recover_dual_slot key (encode_slot key st') (encode_slot key st) = st'
```

#### `forge_airlockSpec.slot_valid_encode_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀key st. st.gen ≠ 0w ∧ airlock_inv key st ⇒ slot_valid key (encode_slot key st)
```

</details>

<details>
<summary><strong><code>forge_airlockRunner</code></strong> — M3 4-FFI ML Runner (20 definitions, 23 theorems)</summary>

Polymorphic Zero-Basis CakeML 4-FFI crash-atomic airlock runner (bootload -> recv64 -> step -> commit -> send128) with boot-once invariant.

### Definitions

#### `forge_airlockRunner.AIRLOCK_IO_EV_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io evs.
    AIRLOCK_IO_EV io evs =
    one (FFI_part (encode_airlock_io io) (mk_ffi_next airlock_ffi_part) airlock_ffi_names evs)
```

#### `forge_airlockRunner.FORGE_AIRLOCKFFI_FRAME128_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14.
    FORGE_AIRLOCKFFI_FRAME128_v (Frame128 c c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14) =
    Conv (SOME (TypeStamp «Frame128» 10))
      [WORD_v c; WORD_v c0; WORD_v c1; WORD_v c2; WORD_v c3; WORD_v c4; WORD_v c5; WORD_v c6;
       WORD_v c7; WORD_v c8; WORD_v c9; WORD_v c10; WORD_v c11; WORD_v c12; WORD_v c13; WORD_v c14]
```

#### `forge_airlockRunner.airlock_loop_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_loop_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockRunner.al_do_commit_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ al_do_commit_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockRunner.al_read_bytes_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ al_read_bytes_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockRunner.al_write_bytes_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ al_write_bytes_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockRunner.al_write_frame128_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ al_write_frame128_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockRunner.boot_first_once_al_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (boot_first_once_al [] ⇔ T) ∧
  ∀e es. boot_first_once_al (e::es) ⇔ is_bootload_ev e ∧ EVERY ($¬ ∘ is_bootload_ev) es
```

#### `forge_airlockRunner.event_is_err_al_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ event_is_err_al =
  WFREC (@R. WF R)
    (λevent_is_err_al a.
       case a of
         IO_event (ExtCall n) conf bs => I (1 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w)
       | IO_event (SharedMem v9) conf bs => I F)
```

#### `forge_airlockRunner.forge_airlockRunner_env_0_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockRunner_env_0 = write «al_read_bytes» al_read_bytes_v forge_airlockRunner_env
```

#### `forge_airlockRunner.forge_airlockRunner_env_1_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockRunner_env_1 = write «al_write_bytes» al_write_bytes_v forge_airlockRunner_env_0
```

#### `forge_airlockRunner.forge_airlockRunner_env_2_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockRunner_env_2 =
  write «al_write_frame128» al_write_frame128_v forge_airlockRunner_env_1
```

#### `forge_airlockRunner.forge_airlockRunner_env_3_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockRunner_env_3 = write «al_do_commit» al_do_commit_v forge_airlockRunner_env_2
```

#### `forge_airlockRunner.forge_airlockRunner_env_4_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockRunner_env_4 = write «airlock_loop» airlock_loop_v forge_airlockRunner_env_3
```

#### `forge_airlockRunner.forge_airlockRunner_env_5_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockRunner_env_5 =
  write «run_airlock_kernel» run_airlock_kernel_v forge_airlockRunner_env_4
```

#### `forge_airlockRunner.forge_airlockRunner_env_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockRunner_env =
  write_cons «Frame128» (16,TypeStamp «Frame128» 10) forge_frameRunner_env_7
```

#### `forge_airlockRunner.forge_airlockRunner_st_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi po.
    forge_airlockRunner_st (ffi,po) =
    <|clock := 0; refs := []; ffi := ffi; next_type_stamp := 11; next_exn_stamp := 5;
      eval_state := NONE; ptr_eq_oracle := some_chars_vector_po po|>
```

#### `forge_airlockRunner.is_bootload_ev_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ is_bootload_ev =
  WFREC (@R. WF R)
    (λis_bootload_ev a.
       case a of
         IO_event (ExtCall n) v0 v1 => I (n = «bootload»)
       | IO_event (SharedMem v11) v0 v1 => I F)
```

#### `forge_airlockRunner.run_airlock_kernel_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ run_airlock_kernel_v = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockRunner.stop_after_err_al_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (stop_after_err_al [] ⇔ T) ∧
  ∀e es. stop_after_err_al (e::es) ⇔ if event_is_err_al e then es = [] else stop_after_err_al es
```

### Theorems

#### `forge_airlockRunner.FORGE_AIRLOCKFFI_FRAME128_TYPE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x_16_x1_1_ x_15_x1_2_ x_14_x1_3_ x_13_x1_4_ x_12_x1_5_ x_11_x1_6_ x_10_x1_7_ x_9_x1_8_ x_8_x1_9_
      x_7_x1_10_ x_6_x1_11_ x_5_x1_12_ x_4_x1_13_ x_3_x1_14_ x_2_x1_15_ x_1_x1_16_ v.
    FORGE_AIRLOCKFFI_FRAME128_TYPE
      (Frame128 x_16_x1_1_ x_15_x1_2_ x_14_x1_3_ x_13_x1_4_ x_12_x1_5_ x_11_x1_6_ x_10_x1_7_
         x_9_x1_8_ x_8_x1_9_ x_7_x1_10_ x_6_x1_11_ x_5_x1_12_ x_4_x1_13_ x_3_x1_14_ x_2_x1_15_
         x_1_x1_16_) v ⇔
    ∃v1_1 v1_2 v1_3 v1_4 v1_5 v1_6 v1_7 v1_8 v1_9 v1_10 v1_11 v1_12 v1_13 v1_14 v1_15 v1_16.
      v =
      Conv (SOME (TypeStamp «Frame128» 10))
        [v1_1; v1_2; v1_3; v1_4; v1_5; v1_6; v1_7; v1_8; v1_9; v1_10; v1_11; v1_12; v1_13; v1_14;
         v1_15; v1_16] ∧ WORD x_16_x1_1_ v1_1 ∧ WORD x_15_x1_2_ v1_2 ∧ WORD x_14_x1_3_ v1_3 ∧
      WORD x_13_x1_4_ v1_4 ∧ WORD x_12_x1_5_ v1_5 ∧ WORD x_11_x1_6_ v1_6 ∧ WORD x_10_x1_7_ v1_7 ∧
      WORD x_9_x1_8_ v1_8 ∧ WORD x_8_x1_9_ v1_9 ∧ WORD x_7_x1_10_ v1_10 ∧ WORD x_6_x1_11_ v1_11 ∧
      WORD x_5_x1_12_ v1_12 ∧ WORD x_4_x1_13_ v1_13 ∧ WORD x_3_x1_14_ v1_14 ∧
      WORD x_2_x1_15_ v1_15 ∧ WORD x_1_x1_16_ v1_16
```

#### `forge_airlockRunner.airlock_io_ffi_part_hprop`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bk bf out.
    FFI_part_hprop
      (SEP_EXISTS sA' sB' rest_inps clim' wlim' evs'.
         &(stop_after_err_al evs' ∧ boot_first_once_al evs') *
         AIRLOCK_IO_EV
           <|boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB'; inputs := rest_inps;
             outputs := out; commit_limit := clim'; write_limit := wlim'|> evs')
```

#### `forge_airlockRunner.airlock_io_split`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st2 io.
    st2.ffi = airlock_ffi io ⇒
    ∃h1 h2. SPLIT (st2heap airlock_proj st2) (h1,h2) ∧ AIRLOCK_IO_EV io [] h1
```

#### `forge_airlockRunner.airlock_loop_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ST $step stepv enc_slot encv slot_sel selv inps bk bf sA sB outs clim wlim evs keyv rbufv rbs
      cbufv cbs sbufv sbs state statev.
    (LIST_TYPE WORD8 --> ST --> FORGE_FRAME64SPEC_FRAME64_TYPE -->
     PAIR_TYPE ST (PAIR_TYPE FORGE_AIRLOCKFFI_FRAME128_TYPE BOOL)) $step stepv ∧
    (LIST_TYPE WORD8 --> ST --> LIST_TYPE WORD8) enc_slot encv ∧ (ST --> WORD8) slot_sel selv ∧
    (∀k s. LENGTH (enc_slot k s) = 256) ∧ LIST_TYPE WORD8 bk keyv ∧ ST state statev ∧
    LENGTH rbs = 65 ∧ LENGTH cbs = 258 ∧ LENGTH sbs = 129 ∧ EVERY ($¬ ∘ event_is_err_al) evs ∧
    evs ≠ [] ∧ boot_first_once_al evs ⇒
    app p airlock_loop_v [stepv; encv; selv; keyv; rbufv; cbufv; sbufv; statev]
      (W8ARRAY rbufv rbs * W8ARRAY cbufv cbs * W8ARRAY sbufv sbs *
       AIRLOCK_IO_EV
         <|boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB; inputs := inps;
           outputs := outs; commit_limit := clim; write_limit := wlim|> evs)
      (POSTv uv.
         &UNIT_TYPE () uv *
         SEP_EXISTS rbs' cbs' sbs' sA' sB' rest_inps clim' wlim' evs'.
           W8ARRAY rbufv rbs' * W8ARRAY cbufv cbs' * W8ARRAY sbufv sbs' * &stop_after_err_al evs' *
           &boot_first_once_al evs' *
           AIRLOCK_IO_EV
             <|boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB'; inputs := rest_inps;
               outputs := outs ++ SND (airlock_exec $step bk state inps clim wlim);
               commit_limit := clim'; write_limit := wlim'|> evs')
```

#### `forge_airlockRunner.airlock_parts_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. parts_ok (airlock_ffi io) airlock_proj
```

#### `forge_airlockRunner.al_do_commit_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ST enc_slot encv slot_sel selv key keyv cbufv cbs state' stv io evs.
    (LIST_TYPE WORD8 --> ST --> LIST_TYPE WORD8) enc_slot encv ∧ (ST --> WORD8) slot_sel selv ∧
    LIST_TYPE WORD8 key keyv ∧ ST state' stv ∧ LENGTH (enc_slot key state') = 256 ∧
    LENGTH cbs = 258 ∧ EVERY ($¬ ∘ event_is_err_al) evs ⇒
    app p al_do_commit_v [encv; selv; keyv; cbufv; stv] (W8ARRAY cbufv cbs * AIRLOCK_IO_EV io evs)
      (POSTv bv.
         (let
            sel = slot_sel state';
            rec = enc_slot key state';
            io_upd = if sel && 1w = 0w then io with slotA := rec else io with slotB := rec
          in
            case io.commit_limit of
              NONE =>
                &BOOL T bv *
                SEP_EXISTS cbs' ev.
                  &(¬event_is_err_al ev ∧ ¬is_bootload_ev ev) * W8ARRAY cbufv cbs' *
                  &(LENGTH cbs' = 258) * AIRLOCK_IO_EV io_upd (evs ++ [ev])
            | SOME 0 =>
              &BOOL F bv *
              SEP_EXISTS cbs' ev.
                &(event_is_err_al ev ∧ ¬is_bootload_ev ev) * W8ARRAY cbufv cbs' *
                &(LENGTH cbs' = 258) * AIRLOCK_IO_EV io (evs ++ [ev])
            | SOME (SUC c) =>
              &BOOL T bv *
              SEP_EXISTS cbs' ev.
                &(¬event_is_err_al ev ∧ ¬is_bootload_ev ev) * W8ARRAY cbufv cbs' *
                &(LENGTH cbs' = 258) *
                AIRLOCK_IO_EV (io_upd with commit_limit := SOME c) (evs ++ [ev])))
```

#### `forge_airlockRunner.al_read_bytes_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀n av bs off offv nv.
    NUM off offv ∧ NUM n nv ∧ off + n ≤ LENGTH bs ⇒
    app p al_read_bytes_v [av; offv; nv] (W8ARRAY av bs)
      (POSTv bsv. &LIST_TYPE WORD8 (TAKE n (DROP off bs)) bsv * W8ARRAY av bs)
```

#### `forge_airlockRunner.al_write_bytes_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ws wsv av bs off offv.
    NUM off offv ∧ LIST_TYPE WORD8 ws wsv ∧ off + LENGTH ws ≤ LENGTH bs ⇒
    app p al_write_bytes_v [av; offv; wsv] (W8ARRAY av bs)
      (POSTv uv. &UNIT_TYPE () uv * W8ARRAY av (TAKE off bs ++ ws ++ DROP (off + LENGTH ws) bs))
```

#### `forge_airlockRunner.al_write_frame128_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀av bs fr frv.
    LENGTH bs = 129 ∧ FORGE_AIRLOCKFFI_FRAME128_TYPE fr frv ⇒
    app p al_write_frame128_v [av; frv] (W8ARRAY av bs)
      (POSTv uv. &UNIT_TYPE () uv * W8ARRAY av (HD bs::frame128_encode fr))
```

#### `forge_airlockRunner.boot_first_once_al_snoc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀es e. boot_first_once_al es ∧ es ≠ [] ∧ ¬is_bootload_ev e ⇒ boot_first_once_al (es ++ [e])
```

#### `forge_airlockRunner.event_is_err_al_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (event_is_err_al (IO_event (ExtCall n) conf bs) ⇔ 1 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w) ∧
  (event_is_err_al (IO_event (SharedMem v7) v1 v2) ⇔ F)
```

#### `forge_airlockRunner.event_is_err_al_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀n conf bs. P (IO_event (ExtCall n) conf bs)) ∧
      (∀v7 v1 v2. P (IO_event (SharedMem v7) v1 v2)) ⇒
      ∀v. P v
```

#### `forge_airlockRunner.is_bootload_ev_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (is_bootload_ev (IO_event (ExtCall n) v0 v1) ⇔ n = «bootload») ∧
  (is_bootload_ev (IO_event (SharedMem v9) v3 v4) ⇔ F)
```

#### `forge_airlockRunner.is_bootload_ev_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀n v0 v1. P (IO_event (ExtCall n) v0 v1)) ∧ (∀v9 v3 v4. P (IO_event (SharedMem v9) v3 v4)) ⇒
      ∀v. P v
```

#### `forge_airlockRunner.nsLookup_forge_airlockRunner_env_0_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockRunner_env_0.c = nsLookup_Mod1 forge_airlockRunner_env.c ∧
  nsLookup_Mod1 forge_airlockRunner_env_0.v = nsLookup_Mod1 forge_airlockRunner_env.v ∧
  nsLookup_Short forge_airlockRunner_env_0.c = nsLookup_Short forge_airlockRunner_env.c ∧
  nsLookup_Short forge_airlockRunner_env_0.v =
  option_choice_f (ALOOKUP [(«al_read_bytes»,al_read_bytes_v)])
    (nsLookup_Short forge_airlockRunner_env.v)
```

#### `forge_airlockRunner.nsLookup_forge_airlockRunner_env_1_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockRunner_env_1.c = nsLookup_Mod1 forge_airlockRunner_env_0.c ∧
  nsLookup_Mod1 forge_airlockRunner_env_1.v = nsLookup_Mod1 forge_airlockRunner_env_0.v ∧
  nsLookup_Short forge_airlockRunner_env_1.c = nsLookup_Short forge_airlockRunner_env_0.c ∧
  nsLookup_Short forge_airlockRunner_env_1.v =
  option_choice_f (ALOOKUP [(«al_write_bytes»,al_write_bytes_v)])
    (nsLookup_Short forge_airlockRunner_env_0.v)
```

#### `forge_airlockRunner.nsLookup_forge_airlockRunner_env_2_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockRunner_env_2.c = nsLookup_Mod1 forge_airlockRunner_env_1.c ∧
  nsLookup_Mod1 forge_airlockRunner_env_2.v = nsLookup_Mod1 forge_airlockRunner_env_1.v ∧
  nsLookup_Short forge_airlockRunner_env_2.c = nsLookup_Short forge_airlockRunner_env_1.c ∧
  nsLookup_Short forge_airlockRunner_env_2.v =
  option_choice_f (ALOOKUP [(«al_write_frame128»,al_write_frame128_v)])
    (nsLookup_Short forge_airlockRunner_env_1.v)
```

#### `forge_airlockRunner.nsLookup_forge_airlockRunner_env_3_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockRunner_env_3.c = nsLookup_Mod1 forge_airlockRunner_env_2.c ∧
  nsLookup_Mod1 forge_airlockRunner_env_3.v = nsLookup_Mod1 forge_airlockRunner_env_2.v ∧
  nsLookup_Short forge_airlockRunner_env_3.c = nsLookup_Short forge_airlockRunner_env_2.c ∧
  nsLookup_Short forge_airlockRunner_env_3.v =
  option_choice_f (ALOOKUP [(«al_do_commit»,al_do_commit_v)])
    (nsLookup_Short forge_airlockRunner_env_2.v)
```

#### `forge_airlockRunner.nsLookup_forge_airlockRunner_env_4_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockRunner_env_4.c = nsLookup_Mod1 forge_airlockRunner_env_3.c ∧
  nsLookup_Mod1 forge_airlockRunner_env_4.v = nsLookup_Mod1 forge_airlockRunner_env_3.v ∧
  nsLookup_Short forge_airlockRunner_env_4.c = nsLookup_Short forge_airlockRunner_env_3.c ∧
  nsLookup_Short forge_airlockRunner_env_4.v =
  option_choice_f (ALOOKUP [(«airlock_loop»,airlock_loop_v)])
    (nsLookup_Short forge_airlockRunner_env_3.v)
```

#### `forge_airlockRunner.nsLookup_forge_airlockRunner_env_5_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockRunner_env_5.c = nsLookup_Mod1 forge_airlockRunner_env_4.c ∧
  nsLookup_Mod1 forge_airlockRunner_env_5.v = nsLookup_Mod1 forge_airlockRunner_env_4.v ∧
  nsLookup_Short forge_airlockRunner_env_5.c = nsLookup_Short forge_airlockRunner_env_4.c ∧
  nsLookup_Short forge_airlockRunner_env_5.v =
  option_choice_f (ALOOKUP [(«run_airlock_kernel»,run_airlock_kernel_v)])
    (nsLookup_Short forge_airlockRunner_env_4.v)
```

#### `forge_airlockRunner.nsLookup_forge_airlockRunner_env_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockRunner_env.c = nsLookup_Mod1 forge_frameRunner_env_7.c ∧
  nsLookup_Mod1 forge_airlockRunner_env.v = nsLookup_Mod1 forge_frameRunner_env_7.v ∧
  nsLookup_Short forge_airlockRunner_env.c =
  option_choice_f (ALOOKUP [(«Frame128»,16,TypeStamp «Frame128» 10)])
    (nsLookup_Short forge_frameRunner_env_7.c) ∧
  nsLookup_Short forge_airlockRunner_env.v = nsLookup_Short forge_frameRunner_env_7.v
```

#### `forge_airlockRunner.run_airlock_kernel_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ST recover recv $step stepv enc_slot encv slot_sel selv bk bf sA sB inps clim wlim.
    (LIST_TYPE WORD8 --> LIST_TYPE WORD8 --> LIST_TYPE WORD8 --> ST) recover recv ∧
    (LIST_TYPE WORD8 --> ST --> FORGE_FRAME64SPEC_FRAME64_TYPE -->
     PAIR_TYPE ST (PAIR_TYPE FORGE_AIRLOCKFFI_FRAME128_TYPE BOOL)) $step stepv ∧
    (LIST_TYPE WORD8 --> ST --> LIST_TYPE WORD8) enc_slot encv ∧ (ST --> WORD8) slot_sel selv ∧
    (∀k s. LENGTH (enc_slot k s) = 256) ⇒
    app p run_airlock_kernel_v [recv; stepv; encv; selv]
      (AIRLOCK_IO_EV
         <|boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB; inputs := inps; outputs := [];
           commit_limit := clim; write_limit := wlim|> [])
      (POSTv rv.
         &UNIT_TYPE () rv *
         SEP_EXISTS sA' sB' rest_inps clim' wlim' evs'.
           &(stop_after_err_al evs' ∧ boot_first_once_al evs') *
           AIRLOCK_IO_EV
             <|boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB'; inputs := rest_inps;
               outputs :=
                 if ¬bf ∧ LENGTH bk = 32 ∧ LENGTH sA = 256 ∧ LENGTH sB = 256 then
                   SND (airlock_exec $step bk (recover bk sA sB) inps clim wlim)
                 else []; commit_limit := clim'; write_limit := wlim'|> evs')
```

#### `forge_airlockRunner.stop_after_err_al_snoc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀es e. EVERY ($¬ ∘ event_is_err_al) es ⇒ stop_after_err_al (es ++ [e])
```

</details>

<details>
<summary><strong><code>forge_airlockProg</code></strong> — Zero-SL CakeML (M3) (7 definitions, 185 theorems)</summary>

Automatically ml_translator-synthesized CakeML crypto-airlock program (SHA-256, HMAC-SHA256, dual-slot recovery, guardrail step).

### Definitions

#### `forge_airlockProg.FORGE_AIRLOCKSPEC_AIRLOCK_STATE_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17.
    FORGE_AIRLOCKSPEC_AIRLOCK_STATE_v
      (airlock_state c c0 c1 c2 c3 c4 c5 c6 c7 c8 b c9 c10 c11 c12 c13 c14 c15 c16 c17) =
    Conv (SOME (TypeStamp «Recordtypeairlock_state» 11))
      [WORD_v c; WORD_v c0; WORD_v c1; WORD_v c2; WORD_v c3; WORD_v c4; WORD_v c5; WORD_v c6;
       WORD_v c7; WORD_v c8; BOOL_v b; WORD_v c9; WORD_v c10; WORD_v c11; WORD_v c12; WORD_v c13;
       WORD_v c14; WORD_v c15; WORD_v c16; WORD_v c17]
```

#### `forge_airlockProg.airlock_prog_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_prog = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockProg.commit_slot_of_state_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st. commit_slot_of_state st = commit_slot_byte st.gen
```

#### `forge_airlockProg.forge_airlockProg_env_87_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_airlockProg_env_87 = write «airlock_main» airlock_main_v forge_airlockProg_env_86
```

#### `forge_airlockProg.forge_airlockProg_st_4_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi po.
    forge_airlockProg_st_4 (ffi,po) =
    <|clock := 0; refs := []; ffi := ffi; next_type_stamp := 12; next_exn_stamp := 5;
      eval_state := NONE; ptr_eq_oracle := slot_magic_po po|>
```

#### `forge_airlockProg.hmac_sha256_side_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀v5 v6. hmac_sha256_side v5 v6 ⇔ LENGTH (if 64 < LENGTH v5 then sha256 v5 else v5) ≤ 64
```

#### `forge_airlockProg.sha256_pad_side_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀v3. sha256_pad_side v3 ⇔ LENGTH v3 MOD 64 ≤ 119
```

### Theorems

#### `forge_airlockProg.FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x_20_x1_1_ x_19_x1_2_ x_18_x1_3_ x_17_x1_4_ x_16_x1_5_ x_15_x1_6_ x_14_x1_7_ x_13_x1_8_
      x_12_x1_9_ x_11_x1_10_ x_10_x1_11_ x_9_x1_12_ x_8_x1_13_ x_7_x1_14_ x_6_x1_15_ x_5_x1_16_
      x_4_x1_17_ x_3_x1_18_ x_2_x1_19_ x_1_x1_20_ v.
    FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE
      (airlock_state x_20_x1_1_ x_19_x1_2_ x_18_x1_3_ x_17_x1_4_ x_16_x1_5_ x_15_x1_6_ x_14_x1_7_
         x_13_x1_8_ x_12_x1_9_ x_11_x1_10_ x_10_x1_11_ x_9_x1_12_ x_8_x1_13_ x_7_x1_14_ x_6_x1_15_
         x_5_x1_16_ x_4_x1_17_ x_3_x1_18_ x_2_x1_19_ x_1_x1_20_) v ⇔
    ∃v1_1 v1_2 v1_3 v1_4 v1_5 v1_6 v1_7 v1_8 v1_9 v1_10 v1_11 v1_12 v1_13 v1_14 v1_15 v1_16 v1_17
        v1_18 v1_19 v1_20.
      v =
      Conv (SOME (TypeStamp «Recordtypeairlock_state» 11))
        [v1_1; v1_2; v1_3; v1_4; v1_5; v1_6; v1_7; v1_8; v1_9; v1_10; v1_11; v1_12; v1_13; v1_14;
         v1_15; v1_16; v1_17; v1_18; v1_19; v1_20] ∧ WORD x_20_x1_1_ v1_1 ∧ WORD x_19_x1_2_ v1_2 ∧
      WORD x_18_x1_3_ v1_3 ∧ WORD x_17_x1_4_ v1_4 ∧ WORD x_16_x1_5_ v1_5 ∧ WORD x_15_x1_6_ v1_6 ∧
      WORD x_14_x1_7_ v1_7 ∧ WORD x_13_x1_8_ v1_8 ∧ WORD x_12_x1_9_ v1_9 ∧ WORD x_11_x1_10_ v1_10 ∧
      BOOL x_10_x1_11_ v1_11 ∧ WORD x_9_x1_12_ v1_12 ∧ WORD x_8_x1_13_ v1_13 ∧
      WORD x_7_x1_14_ v1_14 ∧ WORD x_6_x1_15_ v1_15 ∧ WORD x_5_x1_16_ v1_16 ∧
      WORD x_4_x1_17_ v1_17 ∧ WORD x_3_x1_18_ v1_18 ∧ WORD x_2_x1_19_ v1_19 ∧ WORD x_1_x1_20_ v1_20
```

#### `forge_airlockProg.airlock_init_refs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀po. airlock_init_refs po = []
```

#### `forge_airlockProg.airlock_init_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE airlock_init airlock_init_v
```

#### `forge_airlockProg.airlock_inv_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> BOOL) airlock_inv airlock_inv_v
```

#### `forge_airlockProg.airlock_main_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bk bf sA sB inps clim wlim uv.
    UNIT_TYPE () uv ⇒
    app p airlock_main_v [uv]
      (AIRLOCK_IO_EV
         <|boot_key := bk; boot_fail := bf; slotA := sA; slotB := sB; inputs := inps; outputs := [];
           commit_limit := clim; write_limit := wlim|> [])
      (POSTv rv.
         &UNIT_TYPE () rv *
         SEP_EXISTS sA' sB' rest_inps clim' wlim' evs'.
           &(stop_after_err_al evs' ∧ boot_first_once_al evs') *
           AIRLOCK_IO_EV
             <|boot_key := bk; boot_fail := bf; slotA := sA'; slotB := sB'; inputs := rest_inps;
               outputs :=
                 if ¬bf ∧ LENGTH bk = 32 ∧ LENGTH sA = 256 ∧ LENGTH sB = 256 then
                   SND (airlock_exec airlock_step bk (recover_dual_slot bk sA sB) inps clim wlim)
                 else []; commit_limit := clim'; write_limit := wlim'|> evs')
```

#### `forge_airlockProg.airlock_prog_eq_snoc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_prog = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockProg.airlock_semantics`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io.
    io.outputs = [] ⇒
    sem_satisfies (semantics_dec_list (init_state (airlock_ffi io)) init_env airlock_prog)
      (λb.
         ∃io_events.
           b = Terminate Success io_events ∧ stop_after_err_al io_events ∧
           boot_first_once_al io_events ∧
           sent_frames128_of io_events =
           if
             ¬io.boot_fail ∧ LENGTH io.boot_key = 32 ∧ LENGTH io.slotA = 256 ∧ LENGTH io.slotB = 256
           then
             SND
               (airlock_exec airlock_step io.boot_key
                  (recover_dual_slot io.boot_key io.slotA io.slotB) io.inputs io.commit_limit
                  io.write_limit)
           else [])
```

#### `forge_airlockProg.airlock_step_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_FRAME64SPEC_FRAME64_TYPE -->
   PAIR_TYPE FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE (PAIR_TYPE FORGE_AIRLOCKFFI_FRAME128_TYPE BOOL))
    airlock_step airlock_step_v
```

#### `forge_airlockProg.al_dest_allowed_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> BOOL) al_dest_allowed al_dest_allowed_v
```

#### `forge_airlockProg.al_resp_plain_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKFFI_FRAME128_TYPE)
    al_resp_plain al_resp_plain_v
```

#### `forge_airlockProg.al_resp_tok_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKFFI_FRAME128_TYPE)
    al_resp_tok al_resp_tok_v
```

#### `forge_airlockProg.append_1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE a --> LIST_TYPE a --> LIST_TYPE a) $++ append_1_v
```

#### `forge_airlockProg.be32_of_bytes_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD) be32_of_bytes be32_of_bytes_v
```

#### `forge_airlockProg.be32_to_bytes_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> LIST_TYPE WORD8) be32_to_bytes be32_to_bytes_v
```

#### `forge_airlockProg.be64_to_bytes_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> LIST_TYPE WORD8) be64_to_bytes be64_to_bytes_v
```

#### `forge_airlockProg.bytes32_to_w64x4_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD))) bytes32_to_w64x4
    bytes32_to_w64x4_v
```

#### `forge_airlockProg.bytes_to_be32s_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> LIST_TYPE WORD) bytes_to_be32s bytes_to_be32s_v
```

#### `forge_airlockProg.cap_domain_refs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀po. cap_domain_refs po = []
```

#### `forge_airlockProg.cap_domain_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ LIST_TYPE WORD8 cap_domain cap_domain_v
```

#### `forge_airlockProg.cap_token_msg_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> WORD --> WORD --> WORD --> LIST_TYPE WORD8) cap_token_msg cap_token_msg_v
```

#### `forge_airlockProg.commit_slot_byte_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD8) commit_slot_byte commit_slot_byte_v
```

#### `forge_airlockProg.commit_slot_of_state_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD8) commit_slot_of_state commit_slot_of_state_v
```

#### `forge_airlockProg.decode_slot_raw_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> PAIR_TYPE WORD FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE) decode_slot_raw
    decode_slot_raw_v
```

#### `forge_airlockProg.drop_1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (NUM --> LIST_TYPE a --> LIST_TYPE a) DROP drop_1_v
```

#### `forge_airlockProg.encode_slot_body_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> LIST_TYPE WORD8) encode_slot_body encode_slot_body_v
```

#### `forge_airlockProg.encode_slot_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> LIST_TYPE WORD8) encode_slot
    encode_slot_v
```

#### `forge_airlockProg.hmac_sha256_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> LIST_TYPE WORD8 --> LIST_TYPE WORD8) hmac_sha256 hmac_sha256_v
```

#### `forge_airlockProg.hmac_xor_bytes_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD8 --> LIST_TYPE WORD8 --> LIST_TYPE WORD8) hmac_xor_bytes hmac_xor_bytes_v
```

#### `forge_airlockProg.le64_decode_1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD) le64_decode
    le64_decode_1_v
```

#### `forge_airlockProg.le64_encode_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> LIST_TYPE WORD8) le64_encode le64_encode_v
```

#### `forge_airlockProg.le64_take_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> PAIR_TYPE WORD (LIST_TYPE WORD8)) le64_take le64_take_v
```

#### `forge_airlockProg.length_1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE a --> NUM) LENGTH length_1_v
```

#### `forge_airlockProg.mint_cap_tag_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> WORD --> WORD --> WORD --> WORD --> WORD -->
   PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD))) mint_cap_tag mint_cap_tag_v
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_0_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_0.c = nsLookup_Mod1 forge_airlockProg_env.c ∧
  nsLookup_Mod1 forge_airlockProg_env_0.v = nsLookup_Mod1 forge_airlockProg_env.v ∧
  nsLookup_Short forge_airlockProg_env_0.c = nsLookup_Short forge_airlockProg_env.c ∧
  nsLookup_Short forge_airlockProg_env_0.v =
  option_choice_f (ALOOKUP [(«append_1»,append_1_v)]) (nsLookup_Short forge_airlockProg_env.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_10_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_10.c = nsLookup_Mod1 forge_airlockProg_env_9.c ∧
  nsLookup_Mod1 forge_airlockProg_env_10.v = nsLookup_Mod1 forge_airlockProg_env_9.v ∧
  nsLookup_Short forge_airlockProg_env_10.c = nsLookup_Short forge_airlockProg_env_9.c ∧
  nsLookup_Short forge_airlockProg_env_10.v =
  option_choice_f (ALOOKUP [(«sha256_ch»,sha256_ch_v)]) (nsLookup_Short forge_airlockProg_env_9.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_11_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_11.c = nsLookup_Mod1 forge_airlockProg_env_10.c ∧
  nsLookup_Mod1 forge_airlockProg_env_11.v = nsLookup_Mod1 forge_airlockProg_env_10.v ∧
  nsLookup_Short forge_airlockProg_env_11.c = nsLookup_Short forge_airlockProg_env_10.c ∧
  nsLookup_Short forge_airlockProg_env_11.v =
  option_choice_f (ALOOKUP [(«sha256_maj»,sha256_maj_v)])
    (nsLookup_Short forge_airlockProg_env_10.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_12_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_12.c = nsLookup_Mod1 forge_airlockProg_env_11.c ∧
  nsLookup_Mod1 forge_airlockProg_env_12.v = nsLookup_Mod1 forge_airlockProg_env_11.v ∧
  nsLookup_Short forge_airlockProg_env_12.c = nsLookup_Short forge_airlockProg_env_11.c ∧
  nsLookup_Short forge_airlockProg_env_12.v =
  option_choice_f (ALOOKUP [(«sha256_bsig0»,sha256_bsig0_v)])
    (nsLookup_Short forge_airlockProg_env_11.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_13_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_13.c = nsLookup_Mod1 forge_airlockProg_env_12.c ∧
  nsLookup_Mod1 forge_airlockProg_env_13.v = nsLookup_Mod1 forge_airlockProg_env_12.v ∧
  nsLookup_Short forge_airlockProg_env_13.c = nsLookup_Short forge_airlockProg_env_12.c ∧
  nsLookup_Short forge_airlockProg_env_13.v =
  option_choice_f (ALOOKUP [(«sha256_bsig1»,sha256_bsig1_v)])
    (nsLookup_Short forge_airlockProg_env_12.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_14_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_14.c = nsLookup_Mod1 forge_airlockProg_env_13.c ∧
  nsLookup_Mod1 forge_airlockProg_env_14.v = nsLookup_Mod1 forge_airlockProg_env_13.v ∧
  nsLookup_Short forge_airlockProg_env_14.c = nsLookup_Short forge_airlockProg_env_13.c ∧
  nsLookup_Short forge_airlockProg_env_14.v =
  option_choice_f (ALOOKUP [(«sha256_ssig0»,sha256_ssig0_v)])
    (nsLookup_Short forge_airlockProg_env_13.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_15_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_15.c = nsLookup_Mod1 forge_airlockProg_env_14.c ∧
  nsLookup_Mod1 forge_airlockProg_env_15.v = nsLookup_Mod1 forge_airlockProg_env_14.v ∧
  nsLookup_Short forge_airlockProg_env_15.c = nsLookup_Short forge_airlockProg_env_14.c ∧
  nsLookup_Short forge_airlockProg_env_15.v =
  option_choice_f (ALOOKUP [(«sha256_ssig1»,sha256_ssig1_v)])
    (nsLookup_Short forge_airlockProg_env_14.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_16_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_16.c = nsLookup_Mod1 forge_airlockProg_env_15.c ∧
  nsLookup_Mod1 forge_airlockProg_env_16.v = nsLookup_Mod1 forge_airlockProg_env_15.v ∧
  nsLookup_Short forge_airlockProg_env_16.c = nsLookup_Short forge_airlockProg_env_15.c ∧
  nsLookup_Short forge_airlockProg_env_16.v =
  option_choice_f (ALOOKUP [(«sha256_round»,sha256_round_v)])
    (nsLookup_Short forge_airlockProg_env_15.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_17_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_17.c = nsLookup_Mod1 forge_airlockProg_env_16.c ∧
  nsLookup_Mod1 forge_airlockProg_env_17.v = nsLookup_Mod1 forge_airlockProg_env_16.v ∧
  nsLookup_Short forge_airlockProg_env_17.c = nsLookup_Short forge_airlockProg_env_16.c ∧
  nsLookup_Short forge_airlockProg_env_17.v =
  option_choice_f (ALOOKUP [(«sha256_rounds»,sha256_rounds_v)])
    (nsLookup_Short forge_airlockProg_env_16.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_18_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_18.c = nsLookup_Mod1 forge_airlockProg_env_17.c ∧
  nsLookup_Mod1 forge_airlockProg_env_18.v = nsLookup_Mod1 forge_airlockProg_env_17.v ∧
  nsLookup_Short forge_airlockProg_env_18.c = nsLookup_Short forge_airlockProg_env_17.c ∧
  nsLookup_Short forge_airlockProg_env_18.v =
  option_choice_f (ALOOKUP [(«sha256_compress»,sha256_compress_v)])
    (nsLookup_Short forge_airlockProg_env_17.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_19_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_19.c = nsLookup_Mod1 forge_airlockProg_env_18.c ∧
  nsLookup_Mod1 forge_airlockProg_env_19.v = nsLookup_Mod1 forge_airlockProg_env_18.v ∧
  nsLookup_Short forge_airlockProg_env_19.c = nsLookup_Short forge_airlockProg_env_18.c ∧
  nsLookup_Short forge_airlockProg_env_19.v =
  option_choice_f (ALOOKUP [(«sha256_word_blocks»,sha256_word_blocks_v)])
    (nsLookup_Short forge_airlockProg_env_18.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_1_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_1.c = nsLookup_Mod1 forge_airlockProg_env_0.c ∧
  nsLookup_Mod1 forge_airlockProg_env_1.v = nsLookup_Mod1 forge_airlockProg_env_0.v ∧
  nsLookup_Short forge_airlockProg_env_1.c = nsLookup_Short forge_airlockProg_env_0.c ∧
  nsLookup_Short forge_airlockProg_env_1.v =
  option_choice_f (ALOOKUP [(«replicate»,replicate_v)]) (nsLookup_Short forge_airlockProg_env_0.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_20_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_20.c = nsLookup_Mod1 forge_airlockProg_env_19.c ∧
  nsLookup_Mod1 forge_airlockProg_env_20.v = nsLookup_Mod1 forge_airlockProg_env_19.v ∧
  nsLookup_Short forge_airlockProg_env_20.c = nsLookup_Short forge_airlockProg_env_19.c ∧
  nsLookup_Short forge_airlockProg_env_20.v =
  option_choice_f (ALOOKUP [(«sha256_pad»,sha256_pad_v)])
    (nsLookup_Short forge_airlockProg_env_19.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_21_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_21.c = nsLookup_Mod1 forge_airlockProg_env_20.c ∧
  nsLookup_Mod1 forge_airlockProg_env_21.v = nsLookup_Mod1 forge_airlockProg_env_20.v ∧
  nsLookup_Short forge_airlockProg_env_21.c = nsLookup_Short forge_airlockProg_env_20.c ∧
  nsLookup_Short forge_airlockProg_env_21.v =
  option_choice_f (ALOOKUP [(«sha256_finalize»,sha256_finalize_v)])
    (nsLookup_Short forge_airlockProg_env_20.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_22_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_22.c = nsLookup_Mod1 forge_airlockProg_env_21.c ∧
  nsLookup_Mod1 forge_airlockProg_env_22.v = nsLookup_Mod1 forge_airlockProg_env_21.v ∧
  nsLookup_Short forge_airlockProg_env_22.c = nsLookup_Short forge_airlockProg_env_21.c ∧
  nsLookup_Short forge_airlockProg_env_22.v =
  option_choice_f (ALOOKUP [(«sha256»,sha256_v)]) (nsLookup_Short forge_airlockProg_env_21.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_23_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_23.c = nsLookup_Mod1 forge_airlockProg_env_22.c ∧
  nsLookup_Mod1 forge_airlockProg_env_23.v = nsLookup_Mod1 forge_airlockProg_env_22.v ∧
  nsLookup_Short forge_airlockProg_env_23.c = nsLookup_Short forge_airlockProg_env_22.c ∧
  nsLookup_Short forge_airlockProg_env_23.v =
  option_choice_f (ALOOKUP [(«hmac_xor_bytes»,hmac_xor_bytes_v)])
    (nsLookup_Short forge_airlockProg_env_22.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_24_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_24.c = nsLookup_Mod1 forge_airlockProg_env_23.c ∧
  nsLookup_Mod1 forge_airlockProg_env_24.v = nsLookup_Mod1 forge_airlockProg_env_23.v ∧
  nsLookup_Short forge_airlockProg_env_24.c = nsLookup_Short forge_airlockProg_env_23.c ∧
  nsLookup_Short forge_airlockProg_env_24.v =
  option_choice_f (ALOOKUP [(«hmac_sha256»,hmac_sha256_v)])
    (nsLookup_Short forge_airlockProg_env_23.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_25_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_25.c = nsLookup_Mod1 forge_airlockProg_env_24.c ∧
  nsLookup_Mod1 forge_airlockProg_env_25.v = nsLookup_Mod1 forge_airlockProg_env_24.v ∧
  nsLookup_Short forge_airlockProg_env_25.c = nsLookup_Short forge_airlockProg_env_24.c ∧
  nsLookup_Short forge_airlockProg_env_25.v =
  option_choice_f (ALOOKUP [(«le64_encode»,le64_encode_v)])
    (nsLookup_Short forge_airlockProg_env_24.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_26_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_26.c = nsLookup_Mod1 forge_airlockProg_env_25.c ∧
  nsLookup_Mod1 forge_airlockProg_env_26.v = nsLookup_Mod1 forge_airlockProg_env_25.v ∧
  nsLookup_Short forge_airlockProg_env_26.c = nsLookup_Short forge_airlockProg_env_25.c ∧
  nsLookup_Short forge_airlockProg_env_26.v =
  option_choice_f (ALOOKUP [(«le64_decode_1»,le64_decode_1_v)])
    (nsLookup_Short forge_airlockProg_env_25.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_27_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_27.c = nsLookup_Mod1 forge_airlockProg_env_26.c ∧
  nsLookup_Mod1 forge_airlockProg_env_27.v = nsLookup_Mod1 forge_airlockProg_env_26.v ∧
  nsLookup_Short forge_airlockProg_env_27.c = nsLookup_Short forge_airlockProg_env_26.c ∧
  nsLookup_Short forge_airlockProg_env_27.v =
  option_choice_f (ALOOKUP [(«le64_take»,le64_take_v)]) (nsLookup_Short forge_airlockProg_env_26.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_28_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_28.c = nsLookup_Mod1 forge_airlockProg_env_27.c ∧
  nsLookup_Mod1 forge_airlockProg_env_28.v = nsLookup_Mod1 forge_airlockProg_env_27.v ∧
  nsLookup_Short forge_airlockProg_env_28.c = nsLookup_Short forge_airlockProg_env_27.c ∧
  nsLookup_Short forge_airlockProg_env_28.v =
  option_choice_f (ALOOKUP [(«bytes32_to_w64x4»,bytes32_to_w64x4_v)])
    (nsLookup_Short forge_airlockProg_env_27.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_29_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_29.c = nsLookup_Mod1 forge_airlockProg_env_28.c ∧
  nsLookup_Mod1 forge_airlockProg_env_29.v = nsLookup_Mod1 forge_airlockProg_env_28.v ∧
  nsLookup_Short forge_airlockProg_env_29.c = nsLookup_Short forge_airlockProg_env_28.c ∧
  nsLookup_Short forge_airlockProg_env_29.v =
  option_choice_f (ALOOKUP [(«cap_domain»,cap_domain_v)])
    (nsLookup_Short forge_airlockProg_env_28.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_2_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_2.c = nsLookup_Mod1 forge_airlockProg_env_1.c ∧
  nsLookup_Mod1 forge_airlockProg_env_2.v = nsLookup_Mod1 forge_airlockProg_env_1.v ∧
  nsLookup_Short forge_airlockProg_env_2.c = nsLookup_Short forge_airlockProg_env_1.c ∧
  nsLookup_Short forge_airlockProg_env_2.v =
  option_choice_f (ALOOKUP [(«take_1»,take_1_v)]) (nsLookup_Short forge_airlockProg_env_1.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_30_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_30.c = nsLookup_Mod1 forge_airlockProg_env_29.c ∧
  nsLookup_Mod1 forge_airlockProg_env_30.v = nsLookup_Mod1 forge_airlockProg_env_29.v ∧
  nsLookup_Short forge_airlockProg_env_30.c = nsLookup_Short forge_airlockProg_env_29.c ∧
  nsLookup_Short forge_airlockProg_env_30.v =
  option_choice_f (ALOOKUP [(«cap_token_msg»,cap_token_msg_v)])
    (nsLookup_Short forge_airlockProg_env_29.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_31_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_31.c = nsLookup_Mod1 forge_airlockProg_env_30.c ∧
  nsLookup_Mod1 forge_airlockProg_env_31.v = nsLookup_Mod1 forge_airlockProg_env_30.v ∧
  nsLookup_Short forge_airlockProg_env_31.c = nsLookup_Short forge_airlockProg_env_30.c ∧
  nsLookup_Short forge_airlockProg_env_31.v =
  option_choice_f (ALOOKUP [(«mint_cap_tag»,mint_cap_tag_v)])
    (nsLookup_Short forge_airlockProg_env_30.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_32_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_32.c = nsLookup_Mod1 forge_airlockProg_env_31.c ∧
  nsLookup_Mod1 forge_airlockProg_env_32.v = nsLookup_Mod1 forge_airlockProg_env_31.v ∧
  nsLookup_Short forge_airlockProg_env_32.c =
  option_choice_f (ALOOKUP [(«Recordtypeairlock_state»,20,TypeStamp «Recordtypeairlock_state» 11)])
    (nsLookup_Short forge_airlockProg_env_31.c) ∧
  nsLookup_Short forge_airlockProg_env_32.v = nsLookup_Short forge_airlockProg_env_31.v
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_33_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_33.c = nsLookup_Mod1 forge_airlockProg_env_32.c ∧
  nsLookup_Mod1 forge_airlockProg_env_33.v = nsLookup_Mod1 forge_airlockProg_env_32.v ∧
  nsLookup_Short forge_airlockProg_env_33.c = nsLookup_Short forge_airlockProg_env_32.c ∧
  nsLookup_Short forge_airlockProg_env_33.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefgen»,recordtypeairlock_stateseldefgen_v)])
    (nsLookup_Short forge_airlockProg_env_32.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_34_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_34.c = nsLookup_Mod1 forge_airlockProg_env_33.c ∧
  nsLookup_Mod1 forge_airlockProg_env_34.v = nsLookup_Mod1 forge_airlockProg_env_33.v ∧
  nsLookup_Short forge_airlockProg_env_34.c = nsLookup_Short forge_airlockProg_env_33.c ∧
  nsLookup_Short forge_airlockProg_env_34.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefdeposits»,recordtypeairlock_stateseldefdeposits_v)])
    (nsLookup_Short forge_airlockProg_env_33.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_35_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_35.c = nsLookup_Mod1 forge_airlockProg_env_34.c ∧
  nsLookup_Mod1 forge_airlockProg_env_35.v = nsLookup_Mod1 forge_airlockProg_env_34.v ∧
  nsLookup_Short forge_airlockProg_env_35.c = nsLookup_Short forge_airlockProg_env_34.c ∧
  nsLookup_Short forge_airlockProg_env_35.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefbalance»,recordtypeairlock_stateseldefbalance_v)])
    (nsLookup_Short forge_airlockProg_env_34.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_36_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_36.c = nsLookup_Mod1 forge_airlockProg_env_35.c ∧
  nsLookup_Mod1 forge_airlockProg_env_36.v = nsLookup_Mod1 forge_airlockProg_env_35.v ∧
  nsLookup_Short forge_airlockProg_env_36.c = nsLookup_Short forge_airlockProg_env_35.c ∧
  nsLookup_Short forge_airlockProg_env_36.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefspent»,recordtypeairlock_stateseldefspent_v)])
    (nsLookup_Short forge_airlockProg_env_35.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_37_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_37.c = nsLookup_Mod1 forge_airlockProg_env_36.c ∧
  nsLookup_Mod1 forge_airlockProg_env_37.v = nsLookup_Mod1 forge_airlockProg_env_36.v ∧
  nsLookup_Short forge_airlockProg_env_37.c = nsLookup_Short forge_airlockProg_env_36.c ∧
  nsLookup_Short forge_airlockProg_env_37.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefrefunds»,recordtypeairlock_stateseldefrefunds_v)])
    (nsLookup_Short forge_airlockProg_env_36.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_38_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_38.c = nsLookup_Mod1 forge_airlockProg_env_37.c ∧
  nsLookup_Mod1 forge_airlockProg_env_38.v = nsLookup_Mod1 forge_airlockProg_env_37.v ∧
  nsLookup_Short forge_airlockProg_env_38.c = nsLookup_Short forge_airlockProg_env_37.c ∧
  nsLookup_Short forge_airlockProg_env_38.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefcap»,recordtypeairlock_stateseldefcap_v)])
    (nsLookup_Short forge_airlockProg_env_37.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_39_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_39.c = nsLookup_Mod1 forge_airlockProg_env_38.c ∧
  nsLookup_Mod1 forge_airlockProg_env_39.v = nsLookup_Mod1 forge_airlockProg_env_38.v ∧
  nsLookup_Short forge_airlockProg_env_39.c = nsLookup_Short forge_airlockProg_env_38.c ∧
  nsLookup_Short forge_airlockProg_env_39.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefallowmask»,recordtypeairlock_stateseldefallowmask_v)])
    (nsLookup_Short forge_airlockProg_env_38.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_3_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_3.c = nsLookup_Mod1 forge_airlockProg_env_2.c ∧
  nsLookup_Mod1 forge_airlockProg_env_3.v = nsLookup_Mod1 forge_airlockProg_env_2.v ∧
  nsLookup_Short forge_airlockProg_env_3.c = nsLookup_Short forge_airlockProg_env_2.c ∧
  nsLookup_Short forge_airlockProg_env_3.v =
  option_choice_f (ALOOKUP [(«drop_1»,drop_1_v)]) (nsLookup_Short forge_airlockProg_env_2.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_40_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_40.c = nsLookup_Mod1 forge_airlockProg_env_39.c ∧
  nsLookup_Mod1 forge_airlockProg_env_40.v = nsLookup_Mod1 forge_airlockProg_env_39.v ∧
  nsLookup_Short forge_airlockProg_env_40.c = nsLookup_Short forge_airlockProg_env_39.c ∧
  nsLookup_Short forge_airlockProg_env_40.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefnonce»,recordtypeairlock_stateseldefnonce_v)])
    (nsLookup_Short forge_airlockProg_env_39.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_41_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_41.c = nsLookup_Mod1 forge_airlockProg_env_40.c ∧
  nsLookup_Mod1 forge_airlockProg_env_41.v = nsLookup_Mod1 forge_airlockProg_env_40.v ∧
  nsLookup_Short forge_airlockProg_env_41.c = nsLookup_Short forge_airlockProg_env_40.c ∧
  nsLookup_Short forge_airlockProg_env_41.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeflast_tx»,recordtypeairlock_stateseldeflast_tx_v)])
    (nsLookup_Short forge_airlockProg_env_40.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_42_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_42.c = nsLookup_Mod1 forge_airlockProg_env_41.c ∧
  nsLookup_Mod1 forge_airlockProg_env_42.v = nsLookup_Mod1 forge_airlockProg_env_41.v ∧
  nsLookup_Short forge_airlockProg_env_42.c = nsLookup_Short forge_airlockProg_env_41.c ∧
  nsLookup_Short forge_airlockProg_env_42.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeflast_amt»,recordtypeairlock_stateseldeflast_amt_v)])
    (nsLookup_Short forge_airlockProg_env_41.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_43_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_43.c = nsLookup_Mod1 forge_airlockProg_env_42.c ∧
  nsLookup_Mod1 forge_airlockProg_env_43.v = nsLookup_Mod1 forge_airlockProg_env_42.v ∧
  nsLookup_Short forge_airlockProg_env_43.c = nsLookup_Short forge_airlockProg_env_42.c ∧
  nsLookup_Short forge_airlockProg_env_43.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftx_open»,recordtypeairlock_stateseldeftx_open_v)])
    (nsLookup_Short forge_airlockProg_env_42.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_44_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_44.c = nsLookup_Mod1 forge_airlockProg_env_43.c ∧
  nsLookup_Mod1 forge_airlockProg_env_44.v = nsLookup_Mod1 forge_airlockProg_env_43.v ∧
  nsLookup_Short forge_airlockProg_env_44.c = nsLookup_Short forge_airlockProg_env_43.c ∧
  nsLookup_Short forge_airlockProg_env_44.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_seq»,recordtypeairlock_stateseldeftok_seq_v)])
    (nsLookup_Short forge_airlockProg_env_43.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_45_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_45.c = nsLookup_Mod1 forge_airlockProg_env_44.c ∧
  nsLookup_Mod1 forge_airlockProg_env_45.v = nsLookup_Mod1 forge_airlockProg_env_44.v ∧
  nsLookup_Short forge_airlockProg_env_45.c = nsLookup_Short forge_airlockProg_env_44.c ∧
  nsLookup_Short forge_airlockProg_env_45.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_op»,recordtypeairlock_stateseldeftok_op_v)])
    (nsLookup_Short forge_airlockProg_env_44.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_46_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_46.c = nsLookup_Mod1 forge_airlockProg_env_45.c ∧
  nsLookup_Mod1 forge_airlockProg_env_46.v = nsLookup_Mod1 forge_airlockProg_env_45.v ∧
  nsLookup_Short forge_airlockProg_env_46.c = nsLookup_Short forge_airlockProg_env_45.c ∧
  nsLookup_Short forge_airlockProg_env_46.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_dest»,recordtypeairlock_stateseldeftok_dest_v)])
    (nsLookup_Short forge_airlockProg_env_45.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_47_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_47.c = nsLookup_Mod1 forge_airlockProg_env_46.c ∧
  nsLookup_Mod1 forge_airlockProg_env_47.v = nsLookup_Mod1 forge_airlockProg_env_46.v ∧
  nsLookup_Short forge_airlockProg_env_47.c = nsLookup_Short forge_airlockProg_env_46.c ∧
  nsLookup_Short forge_airlockProg_env_47.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_amt»,recordtypeairlock_stateseldeftok_amt_v)])
    (nsLookup_Short forge_airlockProg_env_46.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_48_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_48.c = nsLookup_Mod1 forge_airlockProg_env_47.c ∧
  nsLookup_Mod1 forge_airlockProg_env_48.v = nsLookup_Mod1 forge_airlockProg_env_47.v ∧
  nsLookup_Short forge_airlockProg_env_48.c = nsLookup_Short forge_airlockProg_env_47.c ∧
  nsLookup_Short forge_airlockProg_env_48.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_bal»,recordtypeairlock_stateseldeftok_bal_v)])
    (nsLookup_Short forge_airlockProg_env_47.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_49_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_49.c = nsLookup_Mod1 forge_airlockProg_env_48.c ∧
  nsLookup_Mod1 forge_airlockProg_env_49.v = nsLookup_Mod1 forge_airlockProg_env_48.v ∧
  nsLookup_Short forge_airlockProg_env_49.c = nsLookup_Short forge_airlockProg_env_48.c ∧
  nsLookup_Short forge_airlockProg_env_49.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_tag0»,recordtypeairlock_stateseldeftok_tag0_v)])
    (nsLookup_Short forge_airlockProg_env_48.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_4_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_4.c = nsLookup_Mod1 forge_airlockProg_env_3.c ∧
  nsLookup_Mod1 forge_airlockProg_env_4.v = nsLookup_Mod1 forge_airlockProg_env_3.v ∧
  nsLookup_Short forge_airlockProg_env_4.c = nsLookup_Short forge_airlockProg_env_3.c ∧
  nsLookup_Short forge_airlockProg_env_4.v =
  option_choice_f (ALOOKUP [(«be32_of_bytes»,be32_of_bytes_v)])
    (nsLookup_Short forge_airlockProg_env_3.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_50_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_50.c = nsLookup_Mod1 forge_airlockProg_env_49.c ∧
  nsLookup_Mod1 forge_airlockProg_env_50.v = nsLookup_Mod1 forge_airlockProg_env_49.v ∧
  nsLookup_Short forge_airlockProg_env_50.c = nsLookup_Short forge_airlockProg_env_49.c ∧
  nsLookup_Short forge_airlockProg_env_50.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_tag1»,recordtypeairlock_stateseldeftok_tag1_v)])
    (nsLookup_Short forge_airlockProg_env_49.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_51_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_51.c = nsLookup_Mod1 forge_airlockProg_env_50.c ∧
  nsLookup_Mod1 forge_airlockProg_env_51.v = nsLookup_Mod1 forge_airlockProg_env_50.v ∧
  nsLookup_Short forge_airlockProg_env_51.c = nsLookup_Short forge_airlockProg_env_50.c ∧
  nsLookup_Short forge_airlockProg_env_51.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_tag2»,recordtypeairlock_stateseldeftok_tag2_v)])
    (nsLookup_Short forge_airlockProg_env_50.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_52_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_52.c = nsLookup_Mod1 forge_airlockProg_env_51.c ∧
  nsLookup_Mod1 forge_airlockProg_env_52.v = nsLookup_Mod1 forge_airlockProg_env_51.v ∧
  nsLookup_Short forge_airlockProg_env_52.c = nsLookup_Short forge_airlockProg_env_51.c ∧
  nsLookup_Short forge_airlockProg_env_52.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldeftok_tag3»,recordtypeairlock_stateseldeftok_tag3_v)])
    (nsLookup_Short forge_airlockProg_env_51.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_53_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_53.c = nsLookup_Mod1 forge_airlockProg_env_52.c ∧
  nsLookup_Mod1 forge_airlockProg_env_53.v = nsLookup_Mod1 forge_airlockProg_env_52.v ∧
  nsLookup_Short forge_airlockProg_env_53.c = nsLookup_Short forge_airlockProg_env_52.c ∧
  nsLookup_Short forge_airlockProg_env_53.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefgen_fupd»,recordtypeairlock_stateseldefgen_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_52.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_54_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_54.c = nsLookup_Mod1 forge_airlockProg_env_53.c ∧
  nsLookup_Mod1 forge_airlockProg_env_54.v = nsLookup_Mod1 forge_airlockProg_env_53.v ∧
  nsLookup_Short forge_airlockProg_env_54.c = nsLookup_Short forge_airlockProg_env_53.c ∧
  nsLookup_Short forge_airlockProg_env_54.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldefdeposits_fupd»,recordtypeairlock_stateseldefdeposits_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_53.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_55_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_55.c = nsLookup_Mod1 forge_airlockProg_env_54.c ∧
  nsLookup_Mod1 forge_airlockProg_env_55.v = nsLookup_Mod1 forge_airlockProg_env_54.v ∧
  nsLookup_Short forge_airlockProg_env_55.c = nsLookup_Short forge_airlockProg_env_54.c ∧
  nsLookup_Short forge_airlockProg_env_55.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldefbalance_fupd»,recordtypeairlock_stateseldefbalance_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_54.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_56_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_56.c = nsLookup_Mod1 forge_airlockProg_env_55.c ∧
  nsLookup_Mod1 forge_airlockProg_env_56.v = nsLookup_Mod1 forge_airlockProg_env_55.v ∧
  nsLookup_Short forge_airlockProg_env_56.c = nsLookup_Short forge_airlockProg_env_55.c ∧
  nsLookup_Short forge_airlockProg_env_56.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefspent_fupd»,recordtypeairlock_stateseldefspent_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_55.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_57_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_57.c = nsLookup_Mod1 forge_airlockProg_env_56.c ∧
  nsLookup_Mod1 forge_airlockProg_env_57.v = nsLookup_Mod1 forge_airlockProg_env_56.v ∧
  nsLookup_Short forge_airlockProg_env_57.c = nsLookup_Short forge_airlockProg_env_56.c ∧
  nsLookup_Short forge_airlockProg_env_57.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldefrefunds_fupd»,recordtypeairlock_stateseldefrefunds_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_56.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_58_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_58.c = nsLookup_Mod1 forge_airlockProg_env_57.c ∧
  nsLookup_Mod1 forge_airlockProg_env_58.v = nsLookup_Mod1 forge_airlockProg_env_57.v ∧
  nsLookup_Short forge_airlockProg_env_58.c = nsLookup_Short forge_airlockProg_env_57.c ∧
  nsLookup_Short forge_airlockProg_env_58.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefcap_fupd»,recordtypeairlock_stateseldefcap_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_57.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_59_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_59.c = nsLookup_Mod1 forge_airlockProg_env_58.c ∧
  nsLookup_Mod1 forge_airlockProg_env_59.v = nsLookup_Mod1 forge_airlockProg_env_58.v ∧
  nsLookup_Short forge_airlockProg_env_59.c = nsLookup_Short forge_airlockProg_env_58.c ∧
  nsLookup_Short forge_airlockProg_env_59.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldefallowmask_fupd»,recordtypeairlock_stateseldefallowmask_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_58.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_5_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_5.c = nsLookup_Mod1 forge_airlockProg_env_4.c ∧
  nsLookup_Mod1 forge_airlockProg_env_5.v = nsLookup_Mod1 forge_airlockProg_env_4.v ∧
  nsLookup_Short forge_airlockProg_env_5.c = nsLookup_Short forge_airlockProg_env_4.c ∧
  nsLookup_Short forge_airlockProg_env_5.v =
  option_choice_f (ALOOKUP [(«be32_to_bytes»,be32_to_bytes_v)])
    (nsLookup_Short forge_airlockProg_env_4.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_60_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_60.c = nsLookup_Mod1 forge_airlockProg_env_59.c ∧
  nsLookup_Mod1 forge_airlockProg_env_60.v = nsLookup_Mod1 forge_airlockProg_env_59.v ∧
  nsLookup_Short forge_airlockProg_env_60.c = nsLookup_Short forge_airlockProg_env_59.c ∧
  nsLookup_Short forge_airlockProg_env_60.v =
  option_choice_f
    (ALOOKUP [(«recordtypeairlock_stateseldefnonce_fupd»,recordtypeairlock_stateseldefnonce_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_59.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_61_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_61.c = nsLookup_Mod1 forge_airlockProg_env_60.c ∧
  nsLookup_Mod1 forge_airlockProg_env_61.v = nsLookup_Mod1 forge_airlockProg_env_60.v ∧
  nsLookup_Short forge_airlockProg_env_61.c = nsLookup_Short forge_airlockProg_env_60.c ∧
  nsLookup_Short forge_airlockProg_env_61.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeflast_tx_fupd»,recordtypeairlock_stateseldeflast_tx_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_60.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_62_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_62.c = nsLookup_Mod1 forge_airlockProg_env_61.c ∧
  nsLookup_Mod1 forge_airlockProg_env_62.v = nsLookup_Mod1 forge_airlockProg_env_61.v ∧
  nsLookup_Short forge_airlockProg_env_62.c = nsLookup_Short forge_airlockProg_env_61.c ∧
  nsLookup_Short forge_airlockProg_env_62.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeflast_amt_fupd»,recordtypeairlock_stateseldeflast_amt_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_61.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_63_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_63.c = nsLookup_Mod1 forge_airlockProg_env_62.c ∧
  nsLookup_Mod1 forge_airlockProg_env_63.v = nsLookup_Mod1 forge_airlockProg_env_62.v ∧
  nsLookup_Short forge_airlockProg_env_63.c = nsLookup_Short forge_airlockProg_env_62.c ∧
  nsLookup_Short forge_airlockProg_env_63.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftx_open_fupd»,recordtypeairlock_stateseldeftx_open_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_62.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_64_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_64.c = nsLookup_Mod1 forge_airlockProg_env_63.c ∧
  nsLookup_Mod1 forge_airlockProg_env_64.v = nsLookup_Mod1 forge_airlockProg_env_63.v ∧
  nsLookup_Short forge_airlockProg_env_64.c = nsLookup_Short forge_airlockProg_env_63.c ∧
  nsLookup_Short forge_airlockProg_env_64.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_seq_fupd»,recordtypeairlock_stateseldeftok_seq_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_63.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_65_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_65.c = nsLookup_Mod1 forge_airlockProg_env_64.c ∧
  nsLookup_Mod1 forge_airlockProg_env_65.v = nsLookup_Mod1 forge_airlockProg_env_64.v ∧
  nsLookup_Short forge_airlockProg_env_65.c = nsLookup_Short forge_airlockProg_env_64.c ∧
  nsLookup_Short forge_airlockProg_env_65.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_op_fupd»,recordtypeairlock_stateseldeftok_op_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_64.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_66_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_66.c = nsLookup_Mod1 forge_airlockProg_env_65.c ∧
  nsLookup_Mod1 forge_airlockProg_env_66.v = nsLookup_Mod1 forge_airlockProg_env_65.v ∧
  nsLookup_Short forge_airlockProg_env_66.c = nsLookup_Short forge_airlockProg_env_65.c ∧
  nsLookup_Short forge_airlockProg_env_66.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_dest_fupd»,recordtypeairlock_stateseldeftok_dest_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_65.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_67_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_67.c = nsLookup_Mod1 forge_airlockProg_env_66.c ∧
  nsLookup_Mod1 forge_airlockProg_env_67.v = nsLookup_Mod1 forge_airlockProg_env_66.v ∧
  nsLookup_Short forge_airlockProg_env_67.c = nsLookup_Short forge_airlockProg_env_66.c ∧
  nsLookup_Short forge_airlockProg_env_67.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_amt_fupd»,recordtypeairlock_stateseldeftok_amt_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_66.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_68_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_68.c = nsLookup_Mod1 forge_airlockProg_env_67.c ∧
  nsLookup_Mod1 forge_airlockProg_env_68.v = nsLookup_Mod1 forge_airlockProg_env_67.v ∧
  nsLookup_Short forge_airlockProg_env_68.c = nsLookup_Short forge_airlockProg_env_67.c ∧
  nsLookup_Short forge_airlockProg_env_68.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_bal_fupd»,recordtypeairlock_stateseldeftok_bal_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_67.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_69_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_69.c = nsLookup_Mod1 forge_airlockProg_env_68.c ∧
  nsLookup_Mod1 forge_airlockProg_env_69.v = nsLookup_Mod1 forge_airlockProg_env_68.v ∧
  nsLookup_Short forge_airlockProg_env_69.c = nsLookup_Short forge_airlockProg_env_68.c ∧
  nsLookup_Short forge_airlockProg_env_69.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_tag0_fupd»,recordtypeairlock_stateseldeftok_tag0_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_68.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_6_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_6.c = nsLookup_Mod1 forge_airlockProg_env_5.c ∧
  nsLookup_Mod1 forge_airlockProg_env_6.v = nsLookup_Mod1 forge_airlockProg_env_5.v ∧
  nsLookup_Short forge_airlockProg_env_6.c = nsLookup_Short forge_airlockProg_env_5.c ∧
  nsLookup_Short forge_airlockProg_env_6.v =
  option_choice_f (ALOOKUP [(«be64_to_bytes»,be64_to_bytes_v)])
    (nsLookup_Short forge_airlockProg_env_5.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_70_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_70.c = nsLookup_Mod1 forge_airlockProg_env_69.c ∧
  nsLookup_Mod1 forge_airlockProg_env_70.v = nsLookup_Mod1 forge_airlockProg_env_69.v ∧
  nsLookup_Short forge_airlockProg_env_70.c = nsLookup_Short forge_airlockProg_env_69.c ∧
  nsLookup_Short forge_airlockProg_env_70.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_tag1_fupd»,recordtypeairlock_stateseldeftok_tag1_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_69.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_71_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_71.c = nsLookup_Mod1 forge_airlockProg_env_70.c ∧
  nsLookup_Mod1 forge_airlockProg_env_71.v = nsLookup_Mod1 forge_airlockProg_env_70.v ∧
  nsLookup_Short forge_airlockProg_env_71.c = nsLookup_Short forge_airlockProg_env_70.c ∧
  nsLookup_Short forge_airlockProg_env_71.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_tag2_fupd»,recordtypeairlock_stateseldeftok_tag2_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_70.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_72_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_72.c = nsLookup_Mod1 forge_airlockProg_env_71.c ∧
  nsLookup_Mod1 forge_airlockProg_env_72.v = nsLookup_Mod1 forge_airlockProg_env_71.v ∧
  nsLookup_Short forge_airlockProg_env_72.c = nsLookup_Short forge_airlockProg_env_71.c ∧
  nsLookup_Short forge_airlockProg_env_72.v =
  option_choice_f
    (ALOOKUP
       [(«recordtypeairlock_stateseldeftok_tag3_fupd»,recordtypeairlock_stateseldeftok_tag3_fupd_v)])
    (nsLookup_Short forge_airlockProg_env_71.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_73_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_73.c = nsLookup_Mod1 forge_airlockProg_env_72.c ∧
  nsLookup_Mod1 forge_airlockProg_env_73.v = nsLookup_Mod1 forge_airlockProg_env_72.v ∧
  nsLookup_Short forge_airlockProg_env_73.c = nsLookup_Short forge_airlockProg_env_72.c ∧
  nsLookup_Short forge_airlockProg_env_73.v =
  option_choice_f (ALOOKUP [(«airlock_init»,airlock_init_v)])
    (nsLookup_Short forge_airlockProg_env_72.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_74_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_74.c = nsLookup_Mod1 forge_airlockProg_env_73.c ∧
  nsLookup_Mod1 forge_airlockProg_env_74.v = nsLookup_Mod1 forge_airlockProg_env_73.v ∧
  nsLookup_Short forge_airlockProg_env_74.c = nsLookup_Short forge_airlockProg_env_73.c ∧
  nsLookup_Short forge_airlockProg_env_74.v =
  option_choice_f (ALOOKUP [(«al_dest_allowed»,al_dest_allowed_v)])
    (nsLookup_Short forge_airlockProg_env_73.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_75_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_75.c = nsLookup_Mod1 forge_airlockProg_env_74.c ∧
  nsLookup_Mod1 forge_airlockProg_env_75.v = nsLookup_Mod1 forge_airlockProg_env_74.v ∧
  nsLookup_Short forge_airlockProg_env_75.c = nsLookup_Short forge_airlockProg_env_74.c ∧
  nsLookup_Short forge_airlockProg_env_75.v =
  option_choice_f (ALOOKUP [(«al_resp_plain»,al_resp_plain_v)])
    (nsLookup_Short forge_airlockProg_env_74.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_76_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_76.c = nsLookup_Mod1 forge_airlockProg_env_75.c ∧
  nsLookup_Mod1 forge_airlockProg_env_76.v = nsLookup_Mod1 forge_airlockProg_env_75.v ∧
  nsLookup_Short forge_airlockProg_env_76.c = nsLookup_Short forge_airlockProg_env_75.c ∧
  nsLookup_Short forge_airlockProg_env_76.v =
  option_choice_f (ALOOKUP [(«al_resp_tok»,al_resp_tok_v)])
    (nsLookup_Short forge_airlockProg_env_75.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_77_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_77.c = nsLookup_Mod1 forge_airlockProg_env_76.c ∧
  nsLookup_Mod1 forge_airlockProg_env_77.v = nsLookup_Mod1 forge_airlockProg_env_76.v ∧
  nsLookup_Short forge_airlockProg_env_77.c = nsLookup_Short forge_airlockProg_env_76.c ∧
  nsLookup_Short forge_airlockProg_env_77.v =
  option_choice_f (ALOOKUP [(«airlock_step»,airlock_step_v)])
    (nsLookup_Short forge_airlockProg_env_76.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_78_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_78.c = nsLookup_Mod1 forge_airlockProg_env_77.c ∧
  nsLookup_Mod1 forge_airlockProg_env_78.v = nsLookup_Mod1 forge_airlockProg_env_77.v ∧
  nsLookup_Short forge_airlockProg_env_78.c = nsLookup_Short forge_airlockProg_env_77.c ∧
  nsLookup_Short forge_airlockProg_env_78.v =
  option_choice_f (ALOOKUP [(«airlock_inv»,airlock_inv_v)])
    (nsLookup_Short forge_airlockProg_env_77.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_79_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_79.c = nsLookup_Mod1 forge_airlockProg_env_78.c ∧
  nsLookup_Mod1 forge_airlockProg_env_79.v = nsLookup_Mod1 forge_airlockProg_env_78.v ∧
  nsLookup_Short forge_airlockProg_env_79.c = nsLookup_Short forge_airlockProg_env_78.c ∧
  nsLookup_Short forge_airlockProg_env_79.v =
  option_choice_f (ALOOKUP [(«slot_magic»,slot_magic_v)])
    (nsLookup_Short forge_airlockProg_env_78.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_7_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_7.c = nsLookup_Mod1 forge_airlockProg_env_6.c ∧
  nsLookup_Mod1 forge_airlockProg_env_7.v = nsLookup_Mod1 forge_airlockProg_env_6.v ∧
  nsLookup_Short forge_airlockProg_env_7.c = nsLookup_Short forge_airlockProg_env_6.c ∧
  nsLookup_Short forge_airlockProg_env_7.v =
  option_choice_f (ALOOKUP [(«bytes_to_be32s»,bytes_to_be32s_v)])
    (nsLookup_Short forge_airlockProg_env_6.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_80_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_80.c = nsLookup_Mod1 forge_airlockProg_env_79.c ∧
  nsLookup_Mod1 forge_airlockProg_env_80.v = nsLookup_Mod1 forge_airlockProg_env_79.v ∧
  nsLookup_Short forge_airlockProg_env_80.c = nsLookup_Short forge_airlockProg_env_79.c ∧
  nsLookup_Short forge_airlockProg_env_80.v =
  option_choice_f (ALOOKUP [(«encode_slot_body»,encode_slot_body_v)])
    (nsLookup_Short forge_airlockProg_env_79.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_81_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_81.c = nsLookup_Mod1 forge_airlockProg_env_80.c ∧
  nsLookup_Mod1 forge_airlockProg_env_81.v = nsLookup_Mod1 forge_airlockProg_env_80.v ∧
  nsLookup_Short forge_airlockProg_env_81.c = nsLookup_Short forge_airlockProg_env_80.c ∧
  nsLookup_Short forge_airlockProg_env_81.v =
  option_choice_f (ALOOKUP [(«encode_slot»,encode_slot_v)])
    (nsLookup_Short forge_airlockProg_env_80.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_82_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_82.c = nsLookup_Mod1 forge_airlockProg_env_81.c ∧
  nsLookup_Mod1 forge_airlockProg_env_82.v = nsLookup_Mod1 forge_airlockProg_env_81.v ∧
  nsLookup_Short forge_airlockProg_env_82.c = nsLookup_Short forge_airlockProg_env_81.c ∧
  nsLookup_Short forge_airlockProg_env_82.v =
  option_choice_f (ALOOKUP [(«decode_slot_raw»,decode_slot_raw_v)])
    (nsLookup_Short forge_airlockProg_env_81.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_83_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_83.c = nsLookup_Mod1 forge_airlockProg_env_82.c ∧
  nsLookup_Mod1 forge_airlockProg_env_83.v = nsLookup_Mod1 forge_airlockProg_env_82.v ∧
  nsLookup_Short forge_airlockProg_env_83.c = nsLookup_Short forge_airlockProg_env_82.c ∧
  nsLookup_Short forge_airlockProg_env_83.v =
  option_choice_f (ALOOKUP [(«slot_valid»,slot_valid_v)])
    (nsLookup_Short forge_airlockProg_env_82.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_84_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_84.c = nsLookup_Mod1 forge_airlockProg_env_83.c ∧
  nsLookup_Mod1 forge_airlockProg_env_84.v = nsLookup_Mod1 forge_airlockProg_env_83.v ∧
  nsLookup_Short forge_airlockProg_env_84.c = nsLookup_Short forge_airlockProg_env_83.c ∧
  nsLookup_Short forge_airlockProg_env_84.v =
  option_choice_f (ALOOKUP [(«recover_dual_slot»,recover_dual_slot_v)])
    (nsLookup_Short forge_airlockProg_env_83.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_85_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_85.c = nsLookup_Mod1 forge_airlockProg_env_84.c ∧
  nsLookup_Mod1 forge_airlockProg_env_85.v = nsLookup_Mod1 forge_airlockProg_env_84.v ∧
  nsLookup_Short forge_airlockProg_env_85.c = nsLookup_Short forge_airlockProg_env_84.c ∧
  nsLookup_Short forge_airlockProg_env_85.v =
  option_choice_f (ALOOKUP [(«commit_slot_byte»,commit_slot_byte_v)])
    (nsLookup_Short forge_airlockProg_env_84.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_86_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_86.c = nsLookup_Mod1 forge_airlockProg_env_85.c ∧
  nsLookup_Mod1 forge_airlockProg_env_86.v = nsLookup_Mod1 forge_airlockProg_env_85.v ∧
  nsLookup_Short forge_airlockProg_env_86.c = nsLookup_Short forge_airlockProg_env_85.c ∧
  nsLookup_Short forge_airlockProg_env_86.v =
  option_choice_f (ALOOKUP [(«commit_slot_of_state»,commit_slot_of_state_v)])
    (nsLookup_Short forge_airlockProg_env_85.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_87_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_87.c = nsLookup_Mod1 forge_airlockProg_env_86.c ∧
  nsLookup_Mod1 forge_airlockProg_env_87.v = nsLookup_Mod1 forge_airlockProg_env_86.v ∧
  nsLookup_Short forge_airlockProg_env_87.c = nsLookup_Short forge_airlockProg_env_86.c ∧
  nsLookup_Short forge_airlockProg_env_87.v =
  option_choice_f (ALOOKUP [(«airlock_main»,airlock_main_v)])
    (nsLookup_Short forge_airlockProg_env_86.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_8_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_8.c = nsLookup_Mod1 forge_airlockProg_env_7.c ∧
  nsLookup_Mod1 forge_airlockProg_env_8.v = nsLookup_Mod1 forge_airlockProg_env_7.v ∧
  nsLookup_Short forge_airlockProg_env_8.c = nsLookup_Short forge_airlockProg_env_7.c ∧
  nsLookup_Short forge_airlockProg_env_8.v =
  option_choice_f (ALOOKUP [(«sha256_iv»,sha256_iv_v)]) (nsLookup_Short forge_airlockProg_env_7.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_9_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env_9.c = nsLookup_Mod1 forge_airlockProg_env_8.c ∧
  nsLookup_Mod1 forge_airlockProg_env_9.v = nsLookup_Mod1 forge_airlockProg_env_8.v ∧
  nsLookup_Short forge_airlockProg_env_9.c = nsLookup_Short forge_airlockProg_env_8.c ∧
  nsLookup_Short forge_airlockProg_env_9.v =
  option_choice_f (ALOOKUP [(«sha256_k»,sha256_k_v)]) (nsLookup_Short forge_airlockProg_env_8.v)
```

#### `forge_airlockProg.nsLookup_forge_airlockProg_env_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_airlockProg_env.c = nsLookup_Mod1 forge_airlockRunner_env_5.c ∧
  nsLookup_Mod1 forge_airlockProg_env.v = nsLookup_Mod1 forge_airlockRunner_env_5.v ∧
  nsLookup_Short forge_airlockProg_env.c = nsLookup_Short forge_airlockRunner_env_5.c ∧
  nsLookup_Short forge_airlockProg_env.v =
  option_choice_f (ALOOKUP [(«length_1»,length_1_v)]) (nsLookup_Short forge_airlockRunner_env_5.v)
```

#### `forge_airlockProg.recordtypeairlock_stateseldefallowmask_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    allowmask_fupd recordtypeairlock_stateseldefallowmask_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefallowmask_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_allowmask
    recordtypeairlock_stateseldefallowmask_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefbalance_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    balance_fupd recordtypeairlock_stateseldefbalance_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefbalance_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_balance
    recordtypeairlock_stateseldefbalance_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefcap_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    cap_fupd recordtypeairlock_stateseldefcap_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefcap_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_cap
    recordtypeairlock_stateseldefcap_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefdeposits_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    deposits_fupd recordtypeairlock_stateseldefdeposits_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefdeposits_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_deposits
    recordtypeairlock_stateseldefdeposits_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefgen_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    gen_fupd recordtypeairlock_stateseldefgen_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefgen_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_gen
    recordtypeairlock_stateseldefgen_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeflast_amt_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    last_amt_fupd recordtypeairlock_stateseldeflast_amt_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeflast_amt_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_last_amt
    recordtypeairlock_stateseldeflast_amt_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeflast_tx_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    last_tx_fupd recordtypeairlock_stateseldeflast_tx_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeflast_tx_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_last_tx
    recordtypeairlock_stateseldeflast_tx_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefnonce_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    nonce_fupd recordtypeairlock_stateseldefnonce_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefnonce_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_nonce
    recordtypeairlock_stateseldefnonce_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefrefunds_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    refunds_fupd recordtypeairlock_stateseldefrefunds_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefrefunds_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_refunds
    recordtypeairlock_stateseldefrefunds_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefspent_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    spent_fupd recordtypeairlock_stateseldefspent_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldefspent_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_spent
    recordtypeairlock_stateseldefspent_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_amt_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_amt_fupd recordtypeairlock_stateseldeftok_amt_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_amt_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_amt
    recordtypeairlock_stateseldeftok_amt_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_bal_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_bal_fupd recordtypeairlock_stateseldeftok_bal_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_bal_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_bal
    recordtypeairlock_stateseldeftok_bal_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_dest_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_dest_fupd recordtypeairlock_stateseldeftok_dest_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_dest_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_dest
    recordtypeairlock_stateseldeftok_dest_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_op_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_op_fupd recordtypeairlock_stateseldeftok_op_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_op_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_op
    recordtypeairlock_stateseldeftok_op_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_seq_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_seq_fupd recordtypeairlock_stateseldeftok_seq_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_seq_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_seq
    recordtypeairlock_stateseldeftok_seq_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag0_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_tag0_fupd recordtypeairlock_stateseldeftok_tag0_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag0_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_tag0
    recordtypeairlock_stateseldeftok_tag0_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag1_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_tag1_fupd recordtypeairlock_stateseldeftok_tag1_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_tag1
    recordtypeairlock_stateseldeftok_tag1_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag2_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_tag2_fupd recordtypeairlock_stateseldeftok_tag2_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag2_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_tag2
    recordtypeairlock_stateseldeftok_tag2_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag3_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tok_tag3_fupd recordtypeairlock_stateseldeftok_tag3_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftok_tag3_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> WORD) airlock_state_tok_tag3
    recordtypeairlock_stateseldeftok_tag3_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftx_open_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((BOOL --> BOOL) --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    tx_open_fupd recordtypeairlock_stateseldeftx_open_fupd_v
```

#### `forge_airlockProg.recordtypeairlock_stateseldeftx_open_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE --> BOOL) airlock_state_tx_open
    recordtypeairlock_stateseldeftx_open_v
```

#### `forge_airlockProg.recover_dual_slot_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> LIST_TYPE WORD8 --> LIST_TYPE WORD8 --> FORGE_AIRLOCKSPEC_AIRLOCK_STATE_TYPE)
    recover_dual_slot recover_dual_slot_v
```

#### `forge_airlockProg.replicate_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (NUM --> a --> LIST_TYPE a) REPLICATE replicate_v
```

#### `forge_airlockProg.sha256_bsig0_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD) sha256_bsig0 sha256_bsig0_v
```

#### `forge_airlockProg.sha256_bsig1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD) sha256_bsig1 sha256_bsig1_v
```

#### `forge_airlockProg.sha256_ch_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> WORD --> WORD) sha256_ch sha256_ch_v
```

#### `forge_airlockProg.sha256_compress_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))) -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD
           (PAIR_TYPE WORD
              (PAIR_TYPE WORD
                 (PAIR_TYPE WORD
                    (PAIR_TYPE WORD
                       (PAIR_TYPE WORD
                          (PAIR_TYPE WORD
                             (PAIR_TYPE WORD
                                (PAIR_TYPE WORD
                                   (PAIR_TYPE WORD
                                      (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))))))))))) -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))))
    sha256_compress sha256_compress_v
```

#### `forge_airlockProg.sha256_finalize_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))) -->
   LIST_TYPE WORD8) sha256_finalize sha256_finalize_v
```

#### `forge_airlockProg.sha256_iv_refs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀po. sha256_iv_refs po = []
```

#### `forge_airlockProg.sha256_iv_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ PAIR_TYPE WORD
    (PAIR_TYPE WORD
       (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD))))))
    sha256_iv sha256_iv_v
```

#### `forge_airlockProg.sha256_k_refs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀po. sha256_k_refs po = []
```

#### `forge_airlockProg.sha256_k_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ LIST_TYPE WORD sha256_k sha256_k_v
```

#### `forge_airlockProg.sha256_maj_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> WORD --> WORD) sha256_maj sha256_maj_v
```

#### `forge_airlockProg.sha256_pad_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> LIST_TYPE WORD8) sha256_pad sha256_pad_v
```

#### `forge_airlockProg.sha256_round_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))) -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))))
    sha256_round sha256_round_v
```

#### `forge_airlockProg.sha256_rounds_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))) -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD
           (PAIR_TYPE WORD
              (PAIR_TYPE WORD
                 (PAIR_TYPE WORD
                    (PAIR_TYPE WORD
                       (PAIR_TYPE WORD
                          (PAIR_TYPE WORD
                             (PAIR_TYPE WORD
                                (PAIR_TYPE WORD
                                   (PAIR_TYPE WORD
                                      (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))))))))))) -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))))
    sha256_rounds sha256_rounds_v
```

#### `forge_airlockProg.sha256_ssig0_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD) sha256_ssig0 sha256_ssig0_v
```

#### `forge_airlockProg.sha256_ssig1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD) sha256_ssig1 sha256_ssig1_v
```

#### `forge_airlockProg.sha256_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> LIST_TYPE WORD8) sha256 sha256_v
```

#### `forge_airlockProg.sha256_word_blocks_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))) -->
   LIST_TYPE WORD -->
   PAIR_TYPE WORD
     (PAIR_TYPE WORD
        (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))))))
    sha256_word_blocks sha256_word_blocks_v
```

#### `forge_airlockProg.slot_magic_refs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀po. slot_magic_refs po = []
```

#### `forge_airlockProg.slot_magic_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ WORD SLOT_MAGIC slot_magic_v
```

#### `forge_airlockProg.slot_valid_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (LIST_TYPE WORD8 --> LIST_TYPE WORD8 --> BOOL) slot_valid slot_valid_v
```

#### `forge_airlockProg.take_1_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (NUM --> LIST_TYPE a --> LIST_TYPE a) TAKE take_1_v
```

</details>

<details>
<summary><strong><code>forge_airlockCompile</code></strong> — Verified Compilation (6 definitions, 4 theorems)</summary>

In-logic ARM64 backend compilation theorem linking airlock_prog to exact machine-code bytes and bitmaps.

### Definitions

#### `forge_airlockCompile.airlock_prog_cv_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x. airlock_prog_cv x = from_list from_ast_ast_dec airlock_prog
```

#### `forge_airlockCompile.code_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ code = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockCompile.compiled`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ compile arm8_config (set_oracle arm8_backend_config oracle) airlock_prog = SOME (code,data,info) ∧
  ffis = ffinames_to_string_list (the [] info.lab_conf.ffi_names) ∧ syms = info.symbols ∧
  LENGTH code = 178044 ∧ LENGTH data = 2062 ∧ info.lab_conf.shmem_extra = [] ∧
  prog_syntax_ok airlock_prog ∧ conf = encode_backend_config info
```

#### `forge_airlockCompile.conf_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ conf = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockCompile.data_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ data = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockCompile.ffis_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ffis =
  to_list to_mlstring_mlstring
    (cv$Pair
       (cv$Pair (cv$Num 0)
          (cv$Pair (cv$Num 98)
             (cv$Pair (cv$Num 111)
                (cv$Pair (cv$Num 111)
                   (cv$Pair (cv$Num 116)
                      (cv$Pair (cv$Num 108)
                         (cv$Pair (cv$Num 111)
                            (cv$Pair (cv$Num 97) (cv$Pair (cv$Num 100) (cv$Num 0))))))))))
       (cv$Pair
          (cv$Pair (cv$Num 0)
             (cv$Pair (cv$Num 115)
                (cv$Pair (cv$Num 101)
                   (cv$Pair (cv$Num 110)
                      (cv$Pair (cv$Num 100)
                         (cv$Pair (cv$Num 49) (cv$Pair (cv$Num 50) (cv$Pair (cv$Num 56) (cv$Num 0)))))))))
          (cv$Pair
             (cv$Pair (cv$Num 0)
                (cv$Pair (cv$Num 114)
                   (cv$Pair (cv$Num 101)
                      (cv$Pair (cv$Num 99)
                         (cv$Pair (cv$Num 118)
                            (cv$Pair (cv$Num 54) (cv$Pair (cv$Num 52) (cv$Num 0))))))))
             (cv$Pair
                (cv$Pair (cv$Num 0)
                   (cv$Pair (cv$Num 99)
                      (cv$Pair (cv$Num 111)
                         (cv$Pair (cv$Num 109)
                            (cv$Pair (cv$Num 109)
                               (cv$Pair (cv$Num 105) (cv$Pair (cv$Num 116) (cv$Num 0))))))))
                (cv$Num 0)))))
```

### Theorems

#### `forge_airlockCompile.airlock_compiled`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ compile arm8_config (set_oracle arm8_backend_config oracle) airlock_prog = SOME (code,data,info) ∧
  ffis = ffinames_to_string_list (the [] info.lab_conf.ffi_names) ∧ syms = info.symbols ∧
  LENGTH code = 178044 ∧ LENGTH data = 2062 ∧ info.lab_conf.shmem_extra = [] ∧
  prog_syntax_ok airlock_prog ∧ conf = encode_backend_config info
```

#### `forge_airlockCompile.airlock_prog_cv_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ airlock_prog_cv x = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_airlockCompile.airlock_prog_cv_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ from_list from_ast_ast_dec airlock_prog = airlock_prog_cv (cv$Num 0)
```

#### `forge_airlockCompile.temp_oracle_cv_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ from_list (from_option (from_sptree_sptree_spt cv$Num)) temp_oracle = temp_oracle_cv (cv$Num 0)
```

</details>

<details>
<summary><strong><code>forge_airlockShimBase</code></strong> — M3 256KB Shim Base (2 definitions, 36 theorems)</summary>

M3 256 KB slot disjointness, patch_bytes/pad512 laws, 4-FFI machine config, interference lifting, and constructive non-vacuity.

### Definitions

#### `forge_airlockShimBase.m3_ffi_return_ok_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end new_bytes s s'.
    m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end new_bytes s s' ⇔
    arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s'.MEM ∧ s'.PC = s.REG 30w ∧
    (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒
         s'.MEM a = asm_write_bytearray (s.REG 2w) new_bytes s.MEM a) ∧
    ∀r. MEM r [19; 20; 21; 22; 23; 24; 25; 26; 27; 28] ⇒ s'.REG (n2w r) = s.REG (n2w r)
```

#### `forge_airlockShimBase.mk_real_m3_ffi_if_slot_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end P k index new_bytes s.
    mk_real_m3_ffi_if_slot cb_begin cb_end bm_buf_end P k (index,new_bytes,s) =
    if
      ∃s'.
        P k index new_bytes s s' ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end new_bytes s s'
    then
      @s'.
        P k index new_bytes s s' ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end new_bytes s s'
    else forge_canonical_ffi_post new_bytes s
```

### Theorems

#### `forge_airlockShimBase.forge_m3_mc_slot_lo55`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end ffi_names_l ffi_if inst_if.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    lo55 (forge_m3_mc_slot cb_end bm_buf_end ffi_names_l ffi_if inst_if)
```

#### `forge_airlockShimBase.forge_m3_mc_slot_mmio_min`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end n0 n1 n2 n3 ffi_if inst_if.
    mmio_pcs_min_index
      (forge_m3_mc_slot cb_end bm_buf_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if
         inst_if).ffi_names = SOME 4
```

#### `forge_airlockShimBase.forge_m3_mc_slot_start_pc_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end n0 n1 n2 n3 ffi_if inst_if.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    start_pc_ok
      (forge_m3_mc_slot cb_end bm_buf_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if
         inst_if) FORGE_M3_CAKE_MAIN
```

#### `forge_airlockShimBase.forge_m3_slot_nonvacuous`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code data.
    0 < LENGTH code ∧ LENGTH code ≤ FORGE_M3_MAX_CODE_BYTES ∧ LENGTH data ≤ FORGE_MAX_BITMAP_WORDS ⇒
    ∃ms0.
      forge_m3_slot_loaded code data ms0 ∧ ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
      ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
```

#### `forge_airlockShimBase.m3_asm_write_bytearray_pointwise`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs p m1 m2 a. m1 a = m2 a ⇒ asm_write_bytearray p xs m1 a = asm_write_bytearray p xs m2 a
```

#### `forge_airlockShimBase.m3_cmn_4_zero`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. w + 4w = 0w ⇔ w = -4w
```

#### `forge_airlockShimBase.m3_cmp_carry_k`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k w.
    1 ≤ k ∧ k < 18446744073709551616 ⇒
    ((if w2n w + (18446744073709551615 − k) + 1 < 18446744073709551616 then
        w2n w + (18446744073709551615 − k) + 1
      else (w2n w + (18446744073709551615 − k) + 1) MOD 18446744073709551616) ≠
     w2n w + (18446744073709551615 − k) + 1 ⇔ k ≤ w2n w)
```

#### `forge_airlockShimBase.m3_cmp_zero_gt_cond`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. (BIT 63 (w2n w + 18446744073709551615 + 1) ⇔ word_msb w) ∧
      (BIT 63 (w2n w + 18446744073709551616) ⇔ word_msb w)
```

#### `forge_airlockShimBase.m3_det_run_imp_nrc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k s s' allow_err os. det_run k s s' ⇒ NRC (m3_whole_step allow_err) k (os,s) (os,s')
```

#### `forge_airlockShimBase.m3_det_run_imp_rtc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k s s' allow_err os. det_run k s s' ⇒ (m3_whole_step allow_err)꙳ (os,s) (os,s')
```

#### `forge_airlockShimBase.m3_det_run_peel_nrc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀k s s' allow_err n ec os os_f ms_f.
    det_run k s s' ∧ NRC (m3_whole_step allow_err) n (os,s) (os_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    k ≤ n ∧ NRC (m3_whole_step allow_err) (n − k) (os,s') (os_f,ms_f)
```

#### `forge_airlockShimBase.m3_erase_mc_conf_ok_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_conf_ok (erase_mc B (forge_m3_mc_slot cb_end bm_end fnames ffi_if inst_if))
```

#### `forge_airlockShimBase.m3_erase_mc_init_ok_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_init_ok arm8_config arm8_backend_config
      (erase_mc B (forge_m3_mc_slot cb_end bm_end fnames ffi_if inst_if))
```

#### `forge_airlockShimBase.m3_extend_uxtx_0`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. ExtendValue (w,ExtendType_UXTX,0) = w
```

#### `forge_airlockShimBase.m3_mem_dword_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m1 m2 a. (∀i. i <₊ 8w ⇒ m1 (a + i) = m2 (a + i)) ⇒ mem_dword m1 a = mem_dword m2 a
```

#### `forge_airlockShimBase.m3_mem_dword_write8`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m a v.
    mem_dword
      m⦇
        a + 7w ↦ (63 >< 56) v; a + 6w ↦ (55 >< 48) v; a + 5w ↦ (47 >< 40) v; a + 4w ↦ (39 >< 32) v;
        a + 3w ↦ (31 >< 24) v; a + 2w ↦ (23 >< 16) v; a + 1w ↦ (15 >< 8) v; a ↦ (7 >< 0) v
      ⦈ a = v
```

#### `forge_airlockShimBase.m3_real_interfer_ok_slot_imp_erase_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_buf_end cbspace n0 n1 n2 n3 B ffi_if inst_if.
    m3_real_interfer_ok_slot cb_end bm_buf_end cbspace
      [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] B ffi_if inst_if ⇒
    ffi_interfer_ok FORGE_M3_CAKE_MAIN
      (erase_mc B
         (forge_m3_mc_slot cb_end bm_buf_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if
            inst_if)) ∧
    install_interfer_ok FORGE_M3_CAKE_MAIN cbspace
      (erase_mc B
         (forge_m3_mc_slot cb_end bm_buf_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if
            inst_if)) ∧
    interference_ok
      (erase_mc B
         (forge_m3_mc_slot cb_end bm_buf_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if
            inst_if)).next_interfer
      ((erase_mc B
          (forge_m3_mc_slot cb_end bm_buf_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3]
             ffi_if inst_if)).target.proj (forge_m3_prog_addresses cb_end bm_buf_end))
```

#### `forge_airlockShimBase.m3_regions_disjoint_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ⇒
    (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_m3_rx_tmp_region ⇒
         a ∉ forge_m3_prog_addresses cb_end bm_buf_end ∧ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_cml_ptrs_region ⇒
         a ∉ forge_m3_prog_addresses cb_end bm_buf_end ∧ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_heap_hdr_region ⇒ a ∉ forge_cml_ptrs_region ∧ a ∉ forge_m3_shim_code_region) ∧
    (∀a. a ∈ forge_m3_prog_addresses cb_end bm_buf_end ⇒ untagged a) ∧
    ∀a. a ∈ forge_m3_shim_code_region ⇒ untagged a
```

#### `forge_airlockShimBase.m3_restore_erase_record_upds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀s. restore (bits_of s) (erase s) = s) ∧
  (∀b s pc. restore b (s with PC := pc) = restore b s with PC := pc) ∧
  (∀b s r. restore b (s with REG := r) = restore b s with REG := r) ∧
  (∀b s m. restore b (s with MEM := m) = restore b s with MEM := m) ∧
  (∀b s ps. restore b (s with PSTATE := ps) = restore b s with PSTATE := ps) ∧
  ∀b s bh. restore b (s with branch_hint := bh) = restore b s with branch_hint := bh
```

#### `forge_airlockShimBase.m3_shim_loaded_slot_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end m1 m2.
    (∀a. a ∈ forge_m3_shim_code_region ⇒ m1 a = m2 a) ⇒
    (m3_shim_loaded_slot cb_begin cb_end bm_buf_end m1 ⇔
     m3_shim_loaded_slot cb_begin cb_end bm_buf_end m2)
```

#### `forge_airlockShimBase.m3_shim_loaded_slot_update`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end m a b.
    a ∉ forge_m3_shim_code_region ⇒
    (m3_shim_loaded_slot cb_begin cb_end bm_buf_end m⦇a ↦ b⦈ ⇔
     m3_shim_loaded_slot cb_begin cb_end bm_buf_end m)
```

#### `forge_airlockShimBase.m3_shim_words_len`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ LENGTH forge_shim_airlock_words = 168
```

#### `forge_airlockShimBase.m3_slot_params_props`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀code_len data_len.
    0 < code_len ∧ code_len ≤ FORGE_M3_MAX_CODE_BYTES ∧ data_len ≤ FORGE_MAX_BITMAP_WORDS ⇒
    (let
       cb_begin = m3_slot_cb_begin code_len;
       cb_end = m3_slot_cb_end code_len;
       cbsp = m3_slot_cbspace code_len;
       bm_end = slot_bm_buf_end data_len
     in
       m3_slot_layout_ok cb_begin cb_end bm_end ∧ FORGE_M3_CAKE_MAIN + n2w code_len = cb_begin ∧
       cb_begin + n2w cbsp = cb_end ∧ FORGE_M3_CAKE_MAIN + n2w code_len + n2w cbsp = cb_end ∧
       w2n FORGE_M3_CAKE_MAIN + code_len = w2n cb_begin ∧
       w2n FORGE_M3_CAKE_MAIN + code_len + cbsp = w2n cb_end ∧ w2n cb_end ≤ 4456448 ∧
       FORGE_CAKE_BITMAPS + n2w (8 * data_len) = bm_end ∧
       FORGE_CAKE_BITMAPS + n2w data_len * bytes_in_word = bm_end ∧
       w2n FORGE_CAKE_BITMAPS + 8 * data_len = w2n bm_end ∧ w2n bm_end ≤ 4653056)
```

#### `forge_airlockShimBase.m3_veneer_facts_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_end.
    m3_slot_layout_ok cb_begin cb_end bm_end ⇒
    FORGE_M3_EXIT_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_INSTALL_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFIBOOT_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFISEND_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFIRECV_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    FORGE_M3_FFICOMMIT_VENEER ∉ forge_m3_prog_addresses cb_end bm_end ∧
    ALL_DISTINCT
      [FORGE_M3_EXIT_VENEER; FORGE_M3_INSTALL_VENEER; FORGE_M3_FFIBOOT_VENEER;
       FORGE_M3_FFISEND_VENEER; FORGE_M3_FFIRECV_VENEER; FORGE_M3_FFICOMMIT_VENEER]
```

#### `forge_airlockShimBase.m3_veneers_len`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end. LENGTH (forge_m3_slot_veneers cb_begin cb_end bm_buf_end) = 52
```

#### `forge_airlockShimBase.m3_w2w_w2w_word8_word64`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀b. w2w (w2w b) = w2w b ∧ w2w (w2w b) = b
```

#### `forge_airlockShimBase.m3_whole_step_exit_stuck`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err ec os s y. svc_exit_group_rel ec s ⇒ ¬m3_whole_step allow_err (os,s) y
```

#### `forge_airlockShimBase.m3_whole_step_nrc_exit_stuck`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err n ec os s y.
    svc_exit_group_rel ec s ∧ NRC (m3_whole_step allow_err) n (os,s) y ⇒ n = 0 ∧ y = (os,s)
```

#### `forge_airlockShimBase.m3_whole_step_svc_det`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀allow_err os s os' s'.
     is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 0w ⇒
     (m3_whole_step allow_err (os,s) (os',s') ⇔
      ∃rest. svc_read_fd_rel 0w allow_err os.inp s s' rest ∧ os' = os with inp := rest)) ∧
  (∀allow_err os s os' s'.
     is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 4w ⇒
     (m3_whole_step allow_err (os,s) (os',s') ⇔
      ∃rest. svc_read_fd_rel 4w allow_err os.key_in s s' rest ∧ os' = os with key_in := rest)) ∧
  (∀allow_err os s os' s'.
     is_svc0_at s ∧ s.REG 8w = 64w ∧ s.REG 0w = 1w ⇒
     (m3_whole_step allow_err (os,s) (os',s') ⇔
      ∃chunk.
        (if allow_err then svc_write_rel else svc_write_noerr_rel) s s' chunk ∧
        os' = os with out := os.out ++ chunk)) ∧
  (∀allow_err os s os' s'.
     is_svc0_at s ∧ s.REG 8w = 67w ⇒
     (m3_whole_step allow_err (os,s) (os',s') ⇔ svc_pread64_rel allow_err os.disk s s' ∧ os' = os)) ∧
  (∀allow_err os s os' s'.
     is_svc0_at s ∧ s.REG 8w = 68w ⇒
     (m3_whole_step allow_err (os,s) (os',s') ⇔
      ∃disk'. svc_pwrite64_rel allow_err os.disk s s' disk' ∧ os' = os with disk := disk')) ∧
  ∀allow_err os s os' s'.
    is_svc0_at s ∧ s.REG 8w = 83w ⇒
    (m3_whole_step allow_err (os,s) (os',s') ⇔
     ∃dur'. svc_fdatasync_rel allow_err os.disk os.durable s s' dur' ∧ os' = os with durable := dur')
```

#### `forge_airlockShimBase.m3_word64_arith_step_helpers`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a b. -1w * a + b = b − a) ∧ ∀a b c. a + (b + c) = b + (c + a)
```

#### `forge_airlockShimBase.m3_word_add_n2w_right`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀p a b. p + n2w a + n2w b = p + n2w (a + b)) ∧ (∀p n. p + 1w + n2w n = p + n2w (n + 1)) ∧
  ∀p n. p + n2w n + 1w = p + n2w (n + 1)
```

#### `forge_airlockShimBase.mk_real_m3_ffi_if_slot_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end cbspace n0 n1 n2 n3 B P.
    m3_real_interfer_ok_slot cb_end bm_buf_end cbspace
      [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] B
      (mk_real_m3_ffi_if_slot cb_begin cb_end bm_buf_end P) forge_real_install_if
```

#### `forge_airlockShimBase.pad512_patch_bytes_slotA`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rec buf.
    LENGTH rec = 256 ⇒
    TAKE 256 (pad512 (patch_bytes 0 rec buf)) = rec ∧
    DROP 256 (pad512 (patch_bytes 0 rec buf)) = DROP 256 (pad512 buf)
```

#### `forge_airlockShimBase.pad512_patch_bytes_slotB`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rec buf.
    LENGTH rec = 256 ⇒
    TAKE 256 (pad512 (patch_bytes 256 rec buf)) = TAKE 256 (pad512 buf) ∧
    DROP 256 (pad512 (patch_bytes 256 rec buf)) = rec
```

#### `forge_airlockShimBase.patch_bytes_append`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀off c1 c2 buf.
    patch_bytes (off + LENGTH c1) c2 (patch_bytes off c1 buf) = patch_bytes off (c1 ++ c2) buf
```

#### `forge_airlockShimBase.patch_bytes_nil`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀off buf. off ≤ LENGTH buf ⇒ patch_bytes off [] buf = buf
```

</details>

<details>
<summary><strong><code>forge_airlockShimStart</code></strong> — M3 Startup & Exit Proof (0 definitions, 6 theorems)</summary>

43-step ARM64 startup proof (_start=0x450000 -> cake_main=0x4000D0), exact installed proof, and universal exit/install stubs.

### Theorems

#### `forge_airlockShimStart.forge_m3_slot_installed_exact`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀n0 n1 n2 n3 code data ffi_names ms0 ffi_if inst_if.
    ffi_names = SOME [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ∧
    forge_m3_slot_loaded code data ms0 ∧
    m3_real_interfer_ok_slot (m3_slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data))
      (m3_slot_cbspace (LENGTH code)) [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] (bits_of ms0)
      ffi_if inst_if ⇒
    (let
       cb_begin = m3_slot_cb_begin (LENGTH code);
       cb_end = m3_slot_cb_end (LENGTH code);
       bm_end = slot_bm_buf_end (LENGTH data);
       cbsp = m3_slot_cbspace (LENGTH code);
       ms1 = FUNPOW Next 43 ms0;
       emc =
         erase_mc (bits_of ms0)
           (forge_m3_mc_slot cb_end bm_end [ExtCall n0; ExtCall n1; ExtCall n2; ExtCall n3] ffi_if
              inst_if)
     in
       det_run 43 ms0 ms1 ∧ ms1.PC = FORGE_M3_CAKE_MAIN ∧ bits_of ms1 = bits_of ms0 ∧
       ms1.SP_EL0 = ms0.SP_EL0 ∧ sp_ok ms1 ∧ arm8_ok (erase ms1) ∧
       m3_shim_loaded_slot cb_begin cb_end bm_end ms1.MEM ∧
       installed code cbsp data 0 ffi_names (1,3) emc [] (erase ms1))
```

#### `forge_airlockShimStart.m3_cake_exit_to_svc_exit_group_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧ m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_EXIT_VENEER ⇒
    ∃k. (let
           s1 = FUNPOW Next k s
         in
           det_run k s s1 ∧ s1.PC = 0x450288w ∧
           svc_exit_group_rel (if s.REG 0w = 0w then 0w else 1w) s1 ∧ s1.MEM = s.MEM ∧
           bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_airlockShimStart.m3_cake_exit_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧ m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_EXIT_VENEER ∧ NRC (m3_whole_step allow_err) n (os,s) (os_f,ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    os_f = os ∧ ec = if s.REG 0w = 0w then 0w else 1w
```

#### `forge_airlockShimStart.m3_cake_install_to_svc_exit_group_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s.
    arm8_ok (erase s) ∧ sp_ok s ∧ m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_INSTALL_VENEER ⇒
    (let
       s1 = FUNPOW Next 3 s
     in
       det_run 3 s s1 ∧ s1.PC = 0x450298w ∧ svc_exit_group_rel 2w s1 ∧ s1.MEM = s.MEM ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_airlockShimStart.m3_cake_install_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧ m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧
    s.PC = FORGE_M3_INSTALL_VENEER ∧ NRC (m3_whole_step allow_err) n (os,s) (os_f,ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    os_f = os ∧ ec = 2w
```

#### `forge_airlockShimStart.m3_startup_to_cake_main_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_SHIM_BASE ⇒
    (let
       s1 = FUNPOW Next 43 s
     in
       det_run 43 s s1 ∧ s1.PC = FORGE_M3_CAKE_MAIN ∧ s1.REG 0w = FORGE_M3_CAKE_MAIN ∧
       s1.REG 1w = FORGE_HEAP ∧ s1.REG 2w = FORGE_STACK ∧ s1.REG 3w = FORGE_STACKEND ∧
       mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
       mem_dword s1.MEM (FORGE_HEAP + 8w) = bm_buf_end ∧
       mem_dword s1.MEM (FORGE_HEAP + 16w) = bm_buf_end ∧
       mem_dword s1.MEM (FORGE_HEAP + 24w) = cb_begin ∧
       mem_dword s1.MEM (FORGE_HEAP + 32w) = cb_end ∧
       (∀a. a ∉ forge_cml_ptrs_region ∧ a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
       m3_shim_loaded_slot cb_begin cb_end bm_buf_end s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧
       bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

</details>

<details>
<summary><strong><code>forge_airlockShimIo</code></strong> — M3 I/O Syscall Proofs (0 definitions, 4 theorems)</summary>

Universal safety and error-free liveness proofs for raw ARM64 ffirecv64 (fd 0) and ffisend128 (fd 1).

### Theorems

#### `forge_airlockShimIo.m3_ffirecv64_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFIRECV_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 65 ⇒
     ∃s'.
       (∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (∀f. 65 ≤ w2n (s.REG 3w) ∧ LENGTH f = 64 ⇒
         ∃s'.
           (∀os rest. os.inp = f ++ rest ⇒ (m3_whole_step F)꙳ (os,s) (os with inp := rest,s')) ∧
           m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w::f ++ DROP 65 bytes2) s s') ∧
    ∀tail_bs.
      65 ≤ w2n (s.REG 3w) ∧ LENGTH tail_bs < 64 ⇒
      ∃s'.
        (∀os. os.inp = tail_bs ⇒ (m3_whole_step F)꙳ (os,s) (os with inp := [],s')) ∧
        m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s'
```

#### `forge_airlockShimIo.m3_ffirecv64_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFIRECV_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧ NRC (m3_whole_step allow_err) n (os,s) (os_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 65 ⇒
     ∃n' s'.
       n' < n ∧ NRC (m3_whole_step allow_err) n' (os,s') (os_f,ms_f) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (65 ≤ w2n (s.REG 3w) ⇒
     (∃n' s' frame inp_after.
        n' < n ∧ LENGTH frame = 64 ∧ os.inp = frame ++ inp_after ∧
        NRC (m3_whole_step allow_err) n' (os with inp := inp_after,s') (os_f,ms_f) ∧
        m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w::frame ++ DROP 65 bytes2) s s') ∨
     ∃n' s' inp_after.
       n' < n ∧ (allow_err ∨ LENGTH os.inp < 64) ∧
       NRC (m3_whole_step allow_err) n' (os with inp := inp_after,s') (os_f,ms_f) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s')
```

#### `forge_airlockShimIo.m3_ffisend128_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFISEND_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 129 ⇒
     ∃s'.
       (∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (129 ≤ w2n (s.REG 3w) ⇒
     ∃s'.
       (∀os. (m3_whole_step F)꙳ (os,s) (os with out := os.out ++ TAKE 128 (DROP 1 bytes2),s')) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s')
```

#### `forge_airlockShimIo.m3_ffisend128_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFISEND_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧ NRC (m3_whole_step allow_err) n (os,s) (os_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 129 ⇒
     ∃n' s'.
       n' < n ∧ NRC (m3_whole_step allow_err) n' (os,s') (os_f,ms_f) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (129 ≤ w2n (s.REG 3w) ⇒
     (∃n' s'.
        n' < n ∧
        NRC (m3_whole_step allow_err) n' (os with out := os.out ++ TAKE 128 (DROP 1 bytes2),s')
          (os_f,ms_f) ∧ m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s') ∨
     allow_err ∧
     ∃n' s' chunk.
       n' < n ∧ chunk ≼ TAKE 128 (DROP 1 bytes2) ∧
       NRC (m3_whole_step allow_err) n' (os with out := os.out ++ chunk,s') (os_f,ms_f) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s')
```

</details>

<details>
<summary><strong><code>forge_airlockShimProof</code></strong> — M3 Disk/Boot Proofs (0 definitions, 4 theorems)</summary>

Universal safety and liveness proofs for raw ARM64 fficommit (pwrite64 + fdatasync durability) and ffibootload (fd 4 key + fd 3 pread64).

### Theorems

#### `forge_airlockShimProof.m3_ffibootload_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFIBOOT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 545 ⇒
     ∃s'.
       (∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (∀key disk.
       545 ≤ w2n (s.REG 3w) ∧ LENGTH key = 32 ⇒
       ∃s'.
         (∀os krest.
            os.key_in = key ++ krest ∧ os.disk = disk ⇒
            (m3_whole_step F)꙳ (os,s) (os with key_in := krest,s')) ∧
         m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end
           (0w::key ++ pad512 disk ++ DROP 545 bytes2) s s') ∧
    ∀kshort.
      545 ≤ w2n (s.REG 3w) ∧ LENGTH kshort < 32 ⇒
      ∃s'.
        (∀os. os.key_in = kshort ⇒ (m3_whole_step F)꙳ (os,s) (os with key_in := [],s')) ∧
        m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s'
```

#### `forge_airlockShimProof.m3_ffibootload_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFIBOOT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧ NRC (m3_whole_step allow_err) n (os,s) (os_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 545 ⇒
     ∃n' s'.
       n' < n ∧ NRC (m3_whole_step allow_err) n' (os,s') (os_f,ms_f) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (545 ≤ w2n (s.REG 3w) ⇒
     (∃n' s' key krest.
        n' < n ∧ LENGTH key = 32 ∧ os.key_in = key ++ krest ∧
        NRC (m3_whole_step allow_err) n' (os with key_in := krest,s') (os_f,ms_f) ∧
        m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end
          (0w::key ++ pad512 os.disk ++ DROP 545 bytes2) s s') ∨
     ∃n' s' krest.
       n' < n ∧ (allow_err ∨ LENGTH os.key_in < 32) ∧
       NRC (m3_whole_step allow_err) n' (os with key_in := krest,s') (os_f,ms_f) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s')
```

#### `forge_airlockShimProof.m3_fficommit_noerr_exists_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end s bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFICOMMIT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ⇒
    (w2n (s.REG 3w) < 258 ⇒
     ∃s'.
       (∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (258 ≤ w2n (s.REG 3w) ⇒
     (let
        sel = bytes2❲1❳;
        boff = if sel && 1w = 0w then 0 else 256;
        rec = TAKE 256 (DROP 2 bytes2)
      in
        ∃s'.
          (∀os.
             (let
                d' = patch_bytes boff rec os.disk
              in
                (m3_whole_step F)꙳ (os,s) (os with <|disk := d'; durable := d'|>,s'))) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s'))
```

#### `forge_airlockShimProof.m3_fficommit_universal_slot`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_begin cb_end bm_buf_end allow_err n s os os_f ms_f ec bytes2.
    m3_slot_layout_ok cb_begin cb_end bm_buf_end ∧ arm8_ok (erase s) ∧ sp_ok s ∧
    m3_shim_loaded_slot cb_begin cb_end bm_buf_end s.MEM ∧ s.PC = FORGE_M3_FFICOMMIT_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (s.MEM a) else NONE) =
    SOME bytes2 ∧ NRC (m3_whole_step allow_err) n (os,s) (os_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 258 ⇒
     ∃n' s'.
       n' < n ∧ NRC (m3_whole_step allow_err) n' (os,s') (os_f,ms_f) ∧
       m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end bytes2 s s') ∧
    (258 ≤ w2n (s.REG 3w) ⇒
     (let
        sel = bytes2❲1❳;
        boff = if sel && 1w = 0w then 0 else 256;
        rec = TAKE 256 (DROP 2 bytes2);
        d' = patch_bytes boff rec os.disk
      in
        (∃n' s'.
           n' < n ∧
           NRC (m3_whole_step allow_err) n' (os with <|disk := d'; durable := d'|>,s') (os_f,ms_f) ∧
           m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (0w::DROP 1 bytes2) s s') ∨
        allow_err ∧
        ∃n' s' d_tmp.
          n' < n ∧ NRC (m3_whole_step allow_err) n' (os with disk := d_tmp,s') (os_f,ms_f) ∧
          m3_ffi_return_ok_slot cb_begin cb_end bm_buf_end (1w::DROP 1 bytes2) s s'))
```

</details>

<details>
<summary><strong><code>forge_airlockCompose</code></strong> — M3 4-FFI E2E Compose (2 definitions, 1 theorems)</summary>

Polymorphic whole-binary ARM64 composition theorem lifting any 4-FFI crypto-airlock kernel from _start to exit_group(94).

### Definitions

#### `forge_airlockCompose.mk_prefix_m3_P_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀posts k idx bs s s'. mk_prefix_m3_P posts k idx bs s s' ⇔ k < LENGTH posts ∧ s' = posts❲k❳
```

#### `forge_airlockCompose.noerr_m3_P_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_end key_in0 disk0 tail_bs k idx new_bs s s'.
    noerr_m3_P cb_end bm_end key_in0 disk0 tail_bs k idx new_bs s s' ⇔
    idx = 0 ∧
    (∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) =
       SOME bytes2 ∧ (w2n (s.REG 3w) < 545 ⇒ ∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
       (545 ≤ w2n (s.REG 3w) ∧ HD new_bs = 0w ⇒
        ∀os krest.
          os.key_in = TAKE 32 (DROP 1 new_bs) ++ krest ∧ os.disk = disk0 ⇒
          (m3_whole_step F)꙳ (os,s) (os with key_in := krest,s')) ∧
       (545 ≤ w2n (s.REG 3w) ∧ HD new_bs ≠ 0w ⇒
        ∀os. os.key_in = key_in0 ⇒ (m3_whole_step F)꙳ (os,s) (os with key_in := [],s'))) ∨
    idx = 1 ∧
    (∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) =
       SOME bytes2 ∧ (w2n (s.REG 3w) < 129 ⇒ ∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
       (129 ≤ w2n (s.REG 3w) ⇒
        ∀os. (m3_whole_step F)꙳ (os,s) (os with out := os.out ++ TAKE 128 (DROP 1 bytes2),s'))) ∨
    idx = 2 ∧
    (∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) =
       SOME bytes2 ∧ (w2n (s.REG 3w) < 65 ⇒ ∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
       (65 ≤ w2n (s.REG 3w) ∧ HD new_bs = 0w ⇒
        ∀os rest.
          os.inp = TAKE 64 (DROP 1 new_bs) ++ rest ⇒
          (m3_whole_step F)꙳ (os,s) (os with inp := rest,s')) ∧
       (65 ≤ w2n (s.REG 3w) ∧ HD new_bs ≠ 0w ⇒
        ∀os. os.inp = tail_bs ⇒ (m3_whole_step F)꙳ (os,s) (os with inp := [],s'))) ∨
    idx = 3 ∧
    ∃bytes2.
      read_bytearray (s.REG 2w) (w2n (s.REG 3w))
        (λa. if a ∈ forge_m3_prog_addresses cb_end bm_end then SOME (s.MEM a) else NONE) =
      SOME bytes2 ∧ (w2n (s.REG 3w) < 258 ⇒ ∀os. (m3_whole_step F)꙳ (os,s) (os,s')) ∧
      (258 ≤ w2n (s.REG 3w) ⇒
       (let
          sel = bytes2❲1❳;
          boff = if sel && 1w = 0w then 0 else 256;
          rec = TAKE 256 (DROP 2 bytes2)
        in
          ∀os.
            (let
               d' = patch_bytes boff rec os.disk
             in
               (m3_whole_step F)꙳ (os,s) (os with <|disk := d'; durable := d'|>,s'))))
```

### Theorems

#### `forge_airlockCompose.forge_airlock_kernel_compose`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

</details>

<details>
<summary><strong><code>forge_m3Kernel</code></strong> — Unified End-to-End (M3) (0 definitions, 2 theorems)</summary>

Whole-binary ARM64 crypto-airlock execution theorem from _start (0x450000) across 6 Linux syscalls to exit_group(94) and non-vacuity witness.

### Theorems

#### `forge_m3Kernel.forge_m3_kernel_correct`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_m3Kernel.forge_m3_nonvacuous`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃ms0.
    forge_m3_slot_loaded code data ms0 ∧ ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧ ms0.SCTLR_EL1.SA0 ∧
    aligned 4 ms0.SP_EL0
```

</details>

