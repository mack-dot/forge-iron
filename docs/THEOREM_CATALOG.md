# Verified Theorem Catalog

> **Auto-generated directly from compiled HOL4 `.dat` theory files** by `scripts/export_theorem_catalog.sml`.
> **Mid-milestone checkpoint snapshot** (`pending` downstream theories remain; final `scripts/iron_law.py` requires 100% compiled and zero `pending`).

## Global HOL4 Kernel Tag Summary

| Metric | Measured Kernel Value |
| --- | --- |
| Top-level theory | `forge_m1Kernel` (checkpoint — pending) |
| `forge_*` theories compiled | `6` (`1` pending) |
| Transitive ancestry closure size | `434` theories |
| Exported `forge_*` definitions | `110` |
| Exported `forge_*` theorems | `176` |
| Total verified `forge_*` items | `286` |
| `HYP_COUNT` (max hypotheses across all items) | `0` |
| `ORACLES` (union of all theorem/definition oracle tags) | `[DISK_THM]` |
| `DIRECT_AXIOMS` (union of all direct axiom tags) | `[]` |
| `AXIOMS` (transitive `DB.axioms` closure) | `4`: `bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX` |

## Crown-Jewel Specifications & Theorems

| Layer | Theory | Theorem / Definition | Status | Plain-English Guarantee |
| --- | --- | --- | --- | --- |
| Pure Spec | `forge_counterSpec` | `counter_run_preserves_cap` | `verified` | Multi-frame counter trace never exceeds cap_val (10,000) without wraparound. |
| Pure Spec | `forge_counterSpec` | `counter_step_no_overflow` | `verified` | Every accepted frame increments spent and seq exactly in natural arithmetic with zero 64-bit overflow. |
| Pure Spec | `forge_counterSpec` | `counter_step_overflow_attack_rejected` | `verified` | Adversarial max-u64 (0xFFFFFFFFFFFFFFFF) spend requests are rejected with state unchanged. |
| Pure Spec | `forge_counterSpec` | `counter_step_replay_rejected` | `verified` | Replayed sequence numbers are rejected with state unchanged. |
| Pure Spec | `forge_counterSpec` | `counter_step_gap_rejected` | `verified` | Skipped sequence numbers (seq + 2) are rejected with state unchanged. |
| Hardware & OS Contract | `forge_contractSpec` | `forge_elf_loaded_def` | `verified` | SHA-256 pinned initial EL0 ARM64 CPU and ELF memory contract at _start (0x421000). |
| Hardware & OS Contract | `forge_contractSpec` | `whole_step_def` | `verified` | SHA-256 pinned whole-binary transition relation combining raw arm8$Next with Linux read(63)/write(64) svc #0 contracts. |
| Zero-Basis CakeML | `forge_counterProg` | `counter_semantics` | `verified` | Zero-Basis CakeML counter_prog terminates cleanly and emits exact counter_run frames under all write limits. |
| Verified Compilation | `forge_counterCompile` | `counter_compiled` | `verified` | In-logic CakeML arm8 backend evaluation theorem binding counter_prog to exact machine-code bytes (code) and bitmaps (data). |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `encoded_bytes_in_mem_not_svc0` | `verified` | No compiled CakeML arm8_config instruction ever encodes the AArch64 svc #0 opcode (0xD4000001). |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `arm8_target_exact_encoder_correct` | `verified` | Exact arm8$Next encoder correctness proving zero CPU exceptions and strict SP_EL0 preservation on every compiled instruction. |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `machine_sem_real_eq_exact` | `verified` | Unconditional equivalence between real-bits arm8_target_real (TBI0/TBI1/SA0) and erased targetSem with zero b ≠ Fail escape hatch. |
| Boot & Syscall Shim | `forge_shimProof` | `startup_to_cake_main` | `verified` | Exact 43-step ARM64 proof from _start (0x421000) through cml_main to cake_main (0x4000B0) setting heap/stack/codebuffer headers. |
| Boot & Syscall Shim | `forge_shimProof` | `ffirecv16_universal` | `verified` | Universal safety of raw ARM64 ffirecv16 over arbitrary partial reads (1..16B), EINTR retries, truncated <16B EOF, and fatal read errors. |
| Boot & Syscall Shim | `forge_shimProof` | `ffisend16_universal` | `verified` | Universal safety of raw ARM64 ffisend16 over arbitrary partial writes (1..16B), EINTR retries, and fatal write/EPIPE errors. |
| Boot & Syscall Shim | `forge_shimProof` | `cake_exit_universal` | `verified` | Universal termination proof of exit veneer + cml_exit to Linux svc #0 exit_group(94) with code 0 or 1. |
| Non-Vacuity Witness | `forge_m1Kernel` | `forge_m1_nonvacuous` | `pending` | Constructive witness exhibiting a concrete Linux EL0 ARM64 state (TBI0=T, TBI1=F, SA0=T, 16B-aligned SP_EL0) satisfying forge_elf_loaded. |
| Unified End-to-End | `forge_m1Kernel` | `forge_m1_kernel_correct` | `pending` | Single whole-binary theorem (exact Term.aconv-pinned) connecting _start (0x421000) across RTC whole_step to svc #0 exit_group(94) and counter_run. |

## Theory-by-Theory Counts

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_counterSpec` | Pure Spec | `verified` | 31 | 52 | 0 | `[DISK_THM]` | `[]` |
| `forge_contractSpec` | Hardware & OS Contract | `verified` | 56 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterProg` | Zero-Basis CakeML | `verified` | 8 | 26 | 0 | `[DISK_THM]` | `[]` |
| `forge_counterCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Boot & Syscall Shim | `verified` | 5 | 43 | 0 | `[DISK_THM]` | `[]` |
| `forge_m1Kernel` | Unified End-to-End | `pending` | — | — | — | — | — |

## Verbatim Exported Statements (`DB.definitions` & `DB.theorems`)

Each section below dumps every exported definition and theorem directly from the compiled HOL4 `.dat` file using `Hol_pp.thm_to_string`.

<details>
<summary><strong><code>forge_counterSpec</code></strong> — Pure Spec (31 definitions, 52 theorems)</summary>

Fixed-width LE64 framing, 16-byte chunking, conservation invariants, and total 2-FFI oracle.

### Definitions

#### `forge_counterSpec.cap_val_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ cap_val = 10000w
```

#### `forge_counterSpec.chunks16_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ chunks16 =
  WFREC (@R. WF R ∧ ∀bs. ¬(LENGTH bs < 16) ⇒ R (DROP 16 bs) bs)
    (λchunks16 a. I (if LENGTH a < 16 then [] else TAKE 16 a::chunks16 (DROP 16 a)))
```

#### `forge_counterSpec.counter_ffi_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. counter_ffi io = initial_ffi_state counter_ffi_oracle io
```

#### `forge_counterSpec.counter_ffi_oracle_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_ffi_oracle =
  (λname io conf bytes.
     if name = ExtCall «recv16» then
       case ffi_recv16 conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else if name = ExtCall «send16» then
       case ffi_send16 conf bytes io of
         NONE => Oracle_final FFI_failed
       | SOME (FFIreturn bytes' io') => Oracle_return io' bytes'
       | SOME FFIdiverge => Oracle_final FFI_failed
     else Oracle_final FFI_failed)
```

#### `forge_counterSpec.counter_ffi_part_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_ffi_part =
  (encode_counter_io,decode_counter_io,[(«recv16»,ffi_recv16); («send16»,ffi_send16)])
```

#### `forge_counterSpec.counter_io_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. counter_io_ABS (counter_io_REP a) = a) ∧
  ∀r. (λx. T) r ⇔ counter_io_REP (counter_io_ABS r) = r
```

#### `forge_counterSpec.counter_io_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_io_CONS = counter_io_ABS
```

#### `forge_counterSpec.counter_io_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_counterSpec.counter_io_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 f. counter_io_CASE (counter_io a0 a1 a2) f = f a0 a1 a2
```

#### `forge_counterSpec.counter_io_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2.
    counter_io_size (counter_io a0 a1 a2) =
    1 + (list_size (list_size w2n) a0 + (list_size (list_size w2n) a1 + option_size (λx. x) a2))
```

#### `forge_counterSpec.counter_proj_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_proj =
  ((λio. FEMPTY |++ [(«recv16»,encode_counter_io io); («send16»,encode_counter_io io)]),
   [([«recv16»; «send16»],mk_ffi_next counter_ffi_part)])
```

#### `forge_counterSpec.counter_run_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀seq spent. counter_run seq spent [] = (seq,spent,[])) ∧
  ∀seq spent f fs.
    counter_run seq spent (f::fs) =
    if LENGTH f = 16 then
      (let
         (req_seq,amount) = frame16_decode f;
         (seq',spent',ok,out_seq) = counter_step seq spent req_seq amount;
         (seqf,spentf,outs) = counter_run seq' spent' fs
       in
         (seqf,spentf,frame16_encode ok out_seq::outs))
    else (seq,spent,[])
```

#### `forge_counterSpec.counter_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq spent req_seq amount.
    counter_step seq spent req_seq amount =
    if seq ≠ 0xFFFFFFFFFFFFFFFFw ∧ req_seq = seq + 1w ∧ amount ≤₊ cap_val − spent then
      (seq + 1w,spent + amount,1w,seq + 1w)
    else (seq,spent,0w,seq)
```

#### `forge_counterSpec.decode_counter_io_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f. decode_counter_io f =
      if ∃io. encode_counter_io io = f then SOME (@io. encode_counter_io io = f) else NONE
```

#### `forge_counterSpec.encode_byte_list_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. encode_byte_list bs = List (MAP (Num ∘ w2n) bs)
```

#### `forge_counterSpec.encode_counter_io_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io.
    encode_counter_io io =
    Cons (List (MAP encode_byte_list io.inputs))
      (Cons (List (MAP encode_byte_list io.outputs)) (encode_opt_num io.write_limit))
```

#### `forge_counterSpec.encode_opt_num_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ encode_opt_num NONE = Num 0 ∧ ∀n. encode_opt_num (SOME n) = Cons (Num 1) (Num n)
```

#### `forge_counterSpec.ffi_recv16_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_recv16 conf bytes io =
    if LENGTH bytes < 17 then SOME (FFIreturn bytes io)
    else
      case io.inputs of
        [] => SOME (FFIreturn (1w::DROP 1 bytes) io)
      | f::fs =>
        if LENGTH f = 16 then SOME (FFIreturn (0w::f ++ DROP 17 bytes) (io with inputs := fs))
        else SOME (FFIreturn (1w::DROP 1 bytes) io)
```

#### `forge_counterSpec.ffi_send16_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io.
    ffi_send16 conf bytes io =
    if LENGTH bytes < 17 then SOME (FFIreturn bytes io)
    else
      (let
         frame = TAKE 16 (DROP 1 bytes)
       in
         case io.write_limit of
           NONE => SOME (FFIreturn (0w::DROP 1 bytes) (io with outputs := io.outputs ++ [frame]))
         | SOME 0 => SOME (FFIreturn (1w::DROP 1 bytes) (io with outputs := io.outputs ++ [frame]))
         | SOME (SUC n) =>
           SOME
             (FFIreturn (0w::DROP 1 bytes)
                (io with <|outputs := io.outputs ++ [frame]; write_limit := SOME n|>)))
```

#### `forge_counterSpec.frame16_decode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f. frame16_decode f =
      (le64_decode f❲0❳ f❲1❳ f❲2❳ f❲3❳ f❲4❳ f❲5❳ f❲6❳ f❲7❳,
       le64_decode f❲8❳ f❲9❳ f❲10❳ f❲11❳ f❲12❳ f❲13❳ f❲14❳ f❲15❳)
```

#### `forge_counterSpec.frame16_encode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀tag seq. frame16_encode tag seq = le64_encode tag ++ le64_encode seq
```

#### `forge_counterSpec.le64_byte_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w i. le64_byte w i = w2w (w ⋙ (8 * i))
```

#### `forge_counterSpec.le64_decode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀b0 b1 b2 b3 b4 b5 b6 b7.
    le64_decode b0 b1 b2 b3 b4 b5 b6 b7 =
    w2w b0 ‖ w2w b1 ≪ 8 ‖ w2w b2 ≪ 16 ‖ w2w b3 ≪ 24 ‖ w2w b4 ≪ 32 ‖ w2w b5 ≪ 40 ‖ w2w b6 ≪ 48 ‖
    w2w b7 ≪ 56
```

#### `forge_counterSpec.le64_encode_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. le64_encode w =
      [le64_byte w 0; le64_byte w 1; le64_byte w 2; le64_byte w 3; le64_byte w 4; le64_byte w 5;
       le64_byte w 6; le64_byte w 7]
```

#### `forge_counterSpec.recordtype_counter_io_seldef_inputs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 $o. (counter_io l l0 $o).inputs = l
```

#### `forge_counterSpec.recordtype_counter_io_seldef_inputs_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 $o. counter_io l l0 $o with inputs updated_by f = counter_io (f l) l0 $o
```

#### `forge_counterSpec.recordtype_counter_io_seldef_outputs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 $o. (counter_io l l0 $o).outputs = l0
```

#### `forge_counterSpec.recordtype_counter_io_seldef_outputs_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 $o. counter_io l l0 $o with outputs updated_by f = counter_io l (f l0) $o
```

#### `forge_counterSpec.recordtype_counter_io_seldef_write_limit_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l l0 $o. (counter_io l l0 $o).write_limit = $o
```

#### `forge_counterSpec.recordtype_counter_io_seldef_write_limit_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f l l0 $o. counter_io l l0 $o with write_limit updated_by f = counter_io l l0 (f $o)
```

#### `forge_counterSpec.sent_frames_of_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sent_frames_of =
  WFREC
    (@R. WF R ∧ (∀bs conf n rest. R rest (IO_event (ExtCall n) conf bs::rest)) ∧
         ∀v4 v3 v9 rest. R rest (IO_event (SharedMem v9) v3 v4::rest))
    (λsent_frames_of a.
       case a of
         [] => I []
       | IO_event (ExtCall n) conf bs::rest =>
         I
           ((if n = «send16» ∧ 17 ≤ LENGTH bs then [TAKE 16 (DROP 1 (MAP FST bs))] else []) ++
            sent_frames_of rest)
       | IO_event (SharedMem v11) conf bs::rest => I (sent_frames_of rest))
```

### Theorems

#### `forge_counterSpec.EXISTS_counter_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∃c. P c) ⇔ ∃l0 l $o. P <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_counterSpec.FLAT_prefix`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs ys. xs ≼ ys ⇒ FLAT xs ≼ FLAT ys
```

#### `forge_counterSpec.FORALL_counter_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀c. P c) ⇔ ∀l0 l $o. P <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_counterSpec.call_FFI_counter_outputs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st st'.
    call_FFI_rel st st' ∧ st.oracle = counter_ffi_oracle ⇒
    st'.oracle = counter_ffi_oracle ∧
    st'.ffi_state.outputs =
    st.ffi_state.outputs ++ sent_frames_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
```

#### `forge_counterSpec.call_FFI_star_counter_outputs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st st'.
    call_FFI_rel꙳ st st' ⇒
    st.oracle = counter_ffi_oracle ⇒
    st'.oracle = counter_ffi_oracle ∧
    st'.ffi_state.outputs =
    st.ffi_state.outputs ++ sent_frames_of (DROP (LENGTH st.io_events) st'.io_events) ∧
    st.io_events ≼ st'.io_events
```

#### `forge_counterSpec.chunks16_cons`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f rest. LENGTH f = 16 ⇒ chunks16 (f ++ rest) = f::chunks16 rest
```

#### `forge_counterSpec.chunks16_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. chunks16 bs = if LENGTH bs < 16 then [] else TAKE 16 bs::chunks16 (DROP 16 bs)
```

#### `forge_counterSpec.chunks16_every_len16`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. EVERY (λf. LENGTH f = 16) (chunks16 bs)
```

#### `forge_counterSpec.chunks16_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀bs. (¬(LENGTH bs < 16) ⇒ P (DROP 16 bs)) ⇒ P bs) ⇒ ∀v. P v
```

#### `forge_counterSpec.chunks16_lt16`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. LENGTH bs < 16 ⇒ chunks16 bs = []
```

#### `forge_counterSpec.counter_ffi_outputs_eq_sent_frames`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io st'.
    io.outputs = [] ∧ call_FFI_rel꙳ (counter_ffi io) st' ⇒
    st'.ffi_state.outputs = sent_frames_of st'.io_events
```

#### `forge_counterSpec.counter_io_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a0' a1' a2'.
    counter_io a0 a1 a2 = counter_io a0' a1' a2' ⇔ a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
```

#### `forge_counterSpec.counter_io_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2. h (counter_io a0 a1 a2) = f0 a0 a1 a2
```

#### `forge_counterSpec.counter_io_accessors`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀l l0 $o. (counter_io l l0 $o).inputs = l) ∧ (∀l l0 $o. (counter_io l l0 $o).outputs = l0) ∧
  ∀l l0 $o. (counter_io l l0 $o).write_limit = $o
```

#### `forge_counterSpec.counter_io_accfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f c. (c with outputs updated_by f).inputs = c.inputs) ∧
  (∀f c. (c with write_limit updated_by f).inputs = c.inputs) ∧
  (∀f c. (c with inputs updated_by f).outputs = c.outputs) ∧
  (∀f c. (c with write_limit updated_by f).outputs = c.outputs) ∧
  (∀f c. (c with inputs updated_by f).write_limit = c.write_limit) ∧
  (∀f c. (c with outputs updated_by f).write_limit = c.write_limit) ∧
  (∀f c. (c with inputs updated_by f).inputs = f c.inputs) ∧
  (∀f c. (c with outputs updated_by f).outputs = f c.outputs) ∧
  ∀f c. (c with write_limit updated_by f).write_limit = f c.write_limit
```

#### `forge_counterSpec.counter_io_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧ (∀a0 a1 a2. M' = counter_io a0 a1 a2 ⇒ f a0 a1 a2 = f' a0 a1 a2) ⇒
    counter_io_CASE M f = counter_io_CASE M' f'
```

#### `forge_counterSpec.counter_io_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_io_CASE x f = v ⇔ ∃l l0 o'. x = counter_io l l0 o' ∧ f l l0 o' = v
```

#### `forge_counterSpec.counter_io_component_equality`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c1 c2.
    c1 = c2 ⇔ c1.inputs = c2.inputs ∧ c1.outputs = c2.outputs ∧ c1.write_limit = c2.write_limit
```

#### `forge_counterSpec.counter_io_fn_updates`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f l l0 $o. counter_io l l0 $o with inputs updated_by f = counter_io (f l) l0 $o) ∧
  (∀f l l0 $o. counter_io l l0 $o with outputs updated_by f = counter_io l (f l0) $o) ∧
  ∀f l l0 $o. counter_io l l0 $o with write_limit updated_by f = counter_io l l0 (f $o)
```

#### `forge_counterSpec.counter_io_fupdcanon`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g f c.
     c with <|outputs updated_by f; inputs updated_by g|> =
     c with <|inputs updated_by g; outputs updated_by f|>) ∧
  (∀g f c.
     c with <|write_limit updated_by f; inputs updated_by g|> =
     c with <|inputs updated_by g; write_limit updated_by f|>) ∧
  ∀g f c.
    c with <|write_limit updated_by f; outputs updated_by g|> =
    c with <|outputs updated_by g; write_limit updated_by f|>
```

#### `forge_counterSpec.counter_io_fupdcanon_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f. outputs_fupd f ∘ inputs_fupd g = inputs_fupd g ∘ outputs_fupd f) ∧
   ∀h g f. outputs_fupd f ∘ inputs_fupd g ∘ h = inputs_fupd g ∘ outputs_fupd f ∘ h) ∧
  ((∀g f. write_limit_fupd f ∘ inputs_fupd g = inputs_fupd g ∘ write_limit_fupd f) ∧
   ∀h g f. write_limit_fupd f ∘ inputs_fupd g ∘ h = inputs_fupd g ∘ write_limit_fupd f ∘ h) ∧
  (∀g f. write_limit_fupd f ∘ outputs_fupd g = outputs_fupd g ∘ write_limit_fupd f) ∧
  ∀h g f. write_limit_fupd f ∘ outputs_fupd g ∘ h = outputs_fupd g ∘ write_limit_fupd f ∘ h
```

#### `forge_counterSpec.counter_io_fupdfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g f c. c with <|inputs updated_by f; inputs updated_by g|> = c with inputs updated_by f ∘ g) ∧
  (∀g f c. c with <|outputs updated_by f; outputs updated_by g|> = c with outputs updated_by f ∘ g) ∧
  ∀g f c.
    c with <|write_limit updated_by f; write_limit updated_by g|> =
    c with write_limit updated_by f ∘ g
```

#### `forge_counterSpec.counter_io_fupdfupds_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g f. inputs_fupd f ∘ inputs_fupd g = inputs_fupd (f ∘ g)) ∧
   ∀h g f. inputs_fupd f ∘ inputs_fupd g ∘ h = inputs_fupd (f ∘ g) ∘ h) ∧
  ((∀g f. outputs_fupd f ∘ outputs_fupd g = outputs_fupd (f ∘ g)) ∧
   ∀h g f. outputs_fupd f ∘ outputs_fupd g ∘ h = outputs_fupd (f ∘ g) ∘ h) ∧
  (∀g f. write_limit_fupd f ∘ write_limit_fupd g = write_limit_fupd (f ∘ g)) ∧
  ∀h g f. write_limit_fupd f ∘ write_limit_fupd g ∘ h = write_limit_fupd (f ∘ g) ∘ h
```

#### `forge_counterSpec.counter_io_fupdselfid`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀c. c with inputs := c.inputs = c) ∧ (∀c. c with outputs := c.outputs = c) ∧
  ∀c. c with write_limit := c.write_limit = c
```

#### `forge_counterSpec.counter_io_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀l l0 $o. P (counter_io l l0 $o)) ⇒ ∀c. P c
```

#### `forge_counterSpec.counter_io_literal_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀l01 l1 o1 l02 l2 o2.
    <|inputs := l01; outputs := l1; write_limit := o1|> =
    <|inputs := l02; outputs := l2; write_limit := o2|> ⇔ l01 = l02 ∧ l1 = l2 ∧ o1 = o2
```

#### `forge_counterSpec.counter_io_literal_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c. ∃l0 l $o. c = <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_counterSpec.counter_io_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cc. ∃l l0 $o. cc = counter_io l l0 $o
```

#### `forge_counterSpec.counter_io_updates_eq_literal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c l0 l $o.
    c with <|inputs := l0; outputs := l; write_limit := $o|> =
    <|inputs := l0; outputs := l; write_limit := $o|>
```

#### `forge_counterSpec.counter_run_preserves_cap`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fs seq spent seqf spentf outs.
    spent ≤₊ cap_val ∧ counter_run seq spent fs = (seqf,spentf,outs) ⇒
    spentf ≤₊ cap_val ∧ w2n spentf ≤ 10000
```

#### `forge_counterSpec.counter_run_take_prefix`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fs n seq spent.
    SND (SND (counter_run seq spent (TAKE n fs))) ≼ SND (SND (counter_run seq spent fs))
```

#### `forge_counterSpec.counter_step_gap_rejected`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq spent amount. counter_step seq spent (seq + 2w) amount = (seq,spent,0w,seq)
```

#### `forge_counterSpec.counter_step_no_overflow`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq spent req_seq amount seq' spent' out_seq.
    spent ≤₊ cap_val ∧ counter_step seq spent req_seq amount = (seq',spent',1w,out_seq) ⇒
    w2n spent' = w2n spent + w2n amount ∧ w2n spent' ≤ w2n cap_val ∧ w2n seq' = w2n seq + 1 ∧
    out_seq = seq'
```

#### `forge_counterSpec.counter_step_overflow_attack_rejected`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq spent.
    spent ≤₊ cap_val ⇒ counter_step seq spent (seq + 1w) 0xFFFFFFFFFFFFFFFFw = (seq,spent,0w,seq)
```

#### `forge_counterSpec.counter_step_preserves_cap`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq spent req_seq amount seq' spent' ok out_seq.
    spent ≤₊ cap_val ∧ counter_step seq spent req_seq amount = (seq',spent',ok,out_seq) ⇒
    spent' ≤₊ cap_val
```

#### `forge_counterSpec.counter_step_reject_unchanged`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq spent req_seq amount seq' spent' out_seq.
    counter_step seq spent req_seq amount = (seq',spent',0w,out_seq) ⇒
    seq' = seq ∧ spent' = spent ∧ out_seq = seq
```

#### `forge_counterSpec.counter_step_replay_rejected`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀seq spent amount. counter_step seq spent seq amount = (seq,spent,0w,seq)
```

#### `forge_counterSpec.datatype_counter_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE (record counter_io inputs outputs write_limit)
```

#### `forge_counterSpec.decode_encode_counter_io`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. decode_counter_io (encode_counter_io io) = SOME io
```

#### `forge_counterSpec.encode_byte_list_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y. encode_byte_list x = encode_byte_list y ⇔ x = y
```

#### `forge_counterSpec.encode_counter_io_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y. encode_counter_io x = encode_counter_io y ⇔ x = y
```

#### `forge_counterSpec.encode_opt_num_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x y. encode_opt_num x = encode_opt_num y ⇔ x = y
```

#### `forge_counterSpec.ffi_recv16_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io bytes' io'.
    ffi_recv16 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes
```

#### `forge_counterSpec.ffi_send16_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀conf bytes io bytes' io'.
    ffi_send16 conf bytes io = SOME (FFIreturn bytes' io') ⇒ LENGTH bytes' = LENGTH bytes
```

#### `forge_counterSpec.frame16_encode_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀tag seq. LENGTH (frame16_encode tag seq) = 16
```

#### `forge_counterSpec.le64_decode_encode_bytes`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀b0 b1 b2 b3 b4 b5 b6 b7.
    le64_encode (le64_decode b0 b1 b2 b3 b4 b5 b6 b7) = [b0; b1; b2; b3; b4; b5; b6; b7]
```

#### `forge_counterSpec.le64_encode_length`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. LENGTH (le64_encode w) = 8
```

#### `forge_counterSpec.le64_roundtrip`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀w. le64_decode (le64_byte w 0) (le64_byte w 1) (le64_byte w 2) (le64_byte w 3) (le64_byte w 4)
        (le64_byte w 5) (le64_byte w 6) (le64_byte w 7) = w
```

#### `forge_counterSpec.sent_frames_of_append`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs ys. sent_frames_of (xs ++ ys) = sent_frames_of xs ++ sent_frames_of ys
```

#### `forge_counterSpec.sent_frames_of_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ sent_frames_of [] = [] ∧
  (∀rest n conf bs.
     sent_frames_of (IO_event (ExtCall n) conf bs::rest) =
     (if n = «send16» ∧ 17 ≤ LENGTH bs then [TAKE 16 (DROP 1 (MAP FST bs))] else []) ++
     sent_frames_of rest) ∧
  ∀v9 v4 v3 rest. sent_frames_of (IO_event (SharedMem v9) v3 v4::rest) = sent_frames_of rest
```

#### `forge_counterSpec.sent_frames_of_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. P [] ∧ (∀n conf bs rest. P rest ⇒ P (IO_event (ExtCall n) conf bs::rest)) ∧
      (∀v9 v3 v4 rest. P rest ⇒ P (IO_event (SharedMem v9) v3 v4::rest)) ⇒
      ∀v. P v
```

#### `forge_counterSpec.sent_frames_of_prefix`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀xs ys. xs ≼ ys ⇒ sent_frames_of xs ≼ sent_frames_of ys
```

</details>

<details>
<summary><strong><code>forge_contractSpec</code></strong> — Hardware & OS Contract (56 definitions, 0 theorems)</summary>

SHA-256 pinned ELF virtual addresses, linked veneer/shim words, ARMv8 real-bits target, and Linux svc #0 contracts.

### Definitions

#### `forge_contractSpec.FORGE_BM_BUF_END_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_BM_BUF_END = 0x430F38w
```

#### `forge_contractSpec.FORGE_CAKE_BITMAPS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CAKE_BITMAPS = 0x430018w
```

#### `forge_contractSpec.FORGE_CAKE_MAIN_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CAKE_MAIN = 0x4000B0w
```

#### `forge_contractSpec.FORGE_CBSPACE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CBSPACE = 56500
```

#### `forge_contractSpec.FORGE_CB_BEGIN_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CB_BEGIN = 0x41234Cw
```

#### `forge_contractSpec.FORGE_CB_END_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CB_END = 0x420000w
```

#### `forge_contractSpec.FORGE_CML_EXIT_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_EXIT = 0x42111Cw
```

#### `forge_contractSpec.FORGE_CML_HEAP_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_HEAP = 0x430000w
```

#### `forge_contractSpec.FORGE_CML_INSTALL_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_INSTALL = 0x421130w
```

#### `forge_contractSpec.FORGE_CML_STACKEND_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_STACKEND = 0x430010w
```

#### `forge_contractSpec.FORGE_CML_STACK_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_CML_STACK = 0x430008w
```

#### `forge_contractSpec.FORGE_EXIT_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_EXIT_VENEER = 0x4000A0w
```

#### `forge_contractSpec.FORGE_FFIRECV16_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFIRECV16_VENEER = 0x400070w
```

#### `forge_contractSpec.FORGE_FFIRECV16_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFIRECV16 = 0x421040w
```

#### `forge_contractSpec.FORGE_FFISEND16_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFISEND16_VENEER = 0x400080w
```

#### `forge_contractSpec.FORGE_FFISEND16_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_FFISEND16 = 0x4210C0w
```

#### `forge_contractSpec.FORGE_HEAP_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_HEAP = 0x450000w
```

#### `forge_contractSpec.FORGE_INSTALL_VENEER_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_INSTALL_VENEER = 0x400090w
```

#### `forge_contractSpec.FORGE_RX_TMP_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_RX_TMP = 0x440000w
```

#### `forge_contractSpec.FORGE_SHIM_BASE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_SHIM_BASE = 0x421000w
```

#### `forge_contractSpec.FORGE_SHIM_END_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_SHIM_END = 0x421140w
```

#### `forge_contractSpec.FORGE_STACKEND_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_STACKEND = 0x490000w
```

#### `forge_contractSpec.FORGE_STACK_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_STACK = 0x470000w
```

#### `forge_contractSpec.FORGE_VENEERS_BASE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_VENEERS_BASE = 0x400000w
```

#### `forge_contractSpec.arm8_target_real_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B. arm8_target_real B =
      arm8_target with
      <|next := Next;
        state_ok :=
          (λms. arm8_ok (erase ms) ∧ bits_of ms = B ∧ (¬SND (SND B) ∨ aligned 4 ms.SP_EL0))|>
```

#### `forge_contractSpec.bits_of_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. bits_of s = (s.TCR_EL1.TBI0,s.TCR_EL1.TBI1,s.SCTLR_EL1.SA0)
```

#### `forge_contractSpec.erase_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. erase s =
      s with
      <|TCR_EL1 := s.TCR_EL1 with <|TBI0 := F; TBI1 := F|>; SCTLR_EL1 := s.SCTLR_EL1 with SA0 := F|>
```

#### `forge_contractSpec.forge_bitmaps_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_bitmaps_region = {a | FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ FORGE_BM_BUF_END}
```

#### `forge_contractSpec.forge_cml_ptrs_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_cml_ptrs_region = {a | FORGE_CML_HEAP ≤₊ a ∧ a <₊ FORGE_CAKE_BITMAPS}
```

#### `forge_contractSpec.forge_code_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_code_region = {a | FORGE_CAKE_MAIN ≤₊ a ∧ a <₊ FORGE_CB_END}
```

#### `forge_contractSpec.forge_elf_loaded_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bytes bitmaps ms0.
    forge_elf_loaded bytes bitmaps ms0 ⇔
    arm8_ok (erase ms0) ∧ sp_ok ms0 ∧ ms0.PC = FORGE_SHIM_BASE ∧ shim_loaded ms0.MEM ∧
    read_bytearray FORGE_CAKE_MAIN (LENGTH bytes)
      (λa. if a ∈ forge_prog_addresses then SOME (ms0.MEM a) else NONE) = SOME bytes ∧
    ∀i. i < LENGTH bitmaps ⇒ mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) = n2w bitmaps❲i❳
```

#### `forge_contractSpec.forge_heap_hdr_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_heap_hdr_region = {a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_HEAP + 40w}
```

#### `forge_contractSpec.forge_heap_stack_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_heap_stack_region = {a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_STACKEND}
```

#### `forge_contractSpec.forge_mc_with_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi_if inst_if.
    forge_mc_with ffi_if inst_if =
    <|prog_addresses := forge_prog_addresses; shared_addresses := ∅;
      ffi_entry_pcs := [FORGE_FFISEND16_VENEER; FORGE_FFIRECV16_VENEER];
      ffi_names := [ExtCall «send16»; ExtCall «recv16»]; ptr_reg := 0; len_reg := 1; ptr2_reg := 2;
      len2_reg := 3; ffi_interfer := ffi_if;
      callee_saved_regs := [19; 20; 21; 22; 23; 24; 25; 26; 27; 28]; next_interfer := K I;
      halt_pc := FORGE_EXIT_VENEER; install_pc := FORGE_INSTALL_VENEER; install_interfer := inst_if;
      target := arm8_target; mmio_info := []|>
```

#### `forge_contractSpec.forge_prog_addresses_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_prog_addresses = forge_code_region ∪ forge_bitmaps_region ∪ forge_heap_stack_region
```

#### `forge_contractSpec.forge_rx_tmp_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_rx_tmp_region = {a | FORGE_RX_TMP ≤₊ a ∧ a <₊ FORGE_RX_TMP + 16w}
```

#### `forge_contractSpec.forge_shim_code_region_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_shim_code_region =
  {a | FORGE_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_CAKE_MAIN} ∪
  {a | FORGE_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_SHIM_END}
```

#### `forge_contractSpec.forge_shim_words_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_shim_words = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_contractSpec.forge_veneers_words_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_veneers_words = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_contractSpec.is_svc0_at_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. is_svc0_at s ⇔
      s.MEM s.PC = 1w ∧ s.MEM (s.PC + 1w) = 0w ∧ s.MEM (s.PC + 2w) = 0w ∧ s.MEM (s.PC + 3w) = 212w
```

#### `forge_contractSpec.lo55_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀mc.
    lo55 mc ⇔
    ∀a. a ∈ mc.prog_addresses ∨ a = mc.halt_pc ∨ a = mc.install_pc ∨ MEM a mc.ffi_entry_pcs ⇒
        untagged a
```

#### `forge_contractSpec.real_interfer_ok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B ffi_if inst_if.
    real_interfer_ok B ffi_if inst_if ⇔
    (let
       mc =
         forge_mc_with (λk (i,bs,s). erase (ffi_if k (i,bs,restore B s)))
           (λk (bs,s). erase (inst_if k (bs,restore B s)))
     in
       ffi_interfer_ok FORGE_CAKE_MAIN mc ∧ install_interfer_ok FORGE_CAKE_MAIN FORGE_CBSPACE mc ∧
       (∀k i bs s.
          bits_of s = B ⇒ bits_of (ffi_if k (i,bs,s)) = B ∧ (ffi_if k (i,bs,s)).SP_EL0 = s.SP_EL0) ∧
       ∀k bs s.
         bits_of s = B ⇒ bits_of (inst_if k (bs,s)) = B ∧ (inst_if k (bs,s)).SP_EL0 = s.SP_EL0)
```

#### `forge_contractSpec.real_mc_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B mc. real_mc B mc = mc with target := arm8_target_real B
```

#### `forge_contractSpec.restore_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B s.
    restore B s =
    s with
    <|TCR_EL1 := s.TCR_EL1 with <|TBI0 := FST B; TBI1 := FST (SND B)|>;
      SCTLR_EL1 := s.SCTLR_EL1 with SA0 := SND (SND B)|>
```

#### `forge_contractSpec.shim_loaded_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀mem.
    shim_loaded mem ⇔
    words32_in_mem FORGE_VENEERS_BASE forge_veneers_words mem ∧
    words32_in_mem FORGE_SHIM_BASE forge_shim_words mem
```

#### `forge_contractSpec.shim_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ shim_step = whole_step svc_read_rel svc_write_rel
```

#### `forge_contractSpec.sp_ok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. sp_ok s ⇔ s.PSTATE.EL = 0w ∧ (¬s.SCTLR_EL1.SA0 ∨ aligned 4 s.SP_EL0)
```

#### `forge_contractSpec.svc_exit_group_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀exit_code s.
    svc_exit_group_rel exit_code s ⇔
    s.REG 8w = 94w ∧ s.REG 0w = exit_code ∧ s.MEM s.PC = 1w ∧ s.MEM (s.PC + 1w) = 0w ∧
    s.MEM (s.PC + 2w) = 0w ∧ s.MEM (s.PC + 3w) = 212w
```

#### `forge_contractSpec.svc_frame_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s s'.
    svc_frame_rel s s' ⇔
    s'.PC = s.PC + 4w ∧ s'.exception = NoException ∧ s'.PSTATE.EL = s.PSTATE.EL ∧
    s'.SCTLR_EL1 = s.SCTLR_EL1 ∧ s'.TCR_EL1 = s.TCR_EL1 ∧ s'.SP_EL0 = s.SP_EL0 ∧
    ∀r. r ≠ 0w ⇒ s'.REG r = s.REG r
```

#### `forge_contractSpec.svc_read_noerr_rel_def`
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

#### `forge_contractSpec.svc_read_rel_def`
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

#### `forge_contractSpec.svc_write_noerr_rel_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s s' out.
    svc_write_noerr_rel s s' out ⇔
    s.REG 8w = 64w ∧ s.REG 0w = 1w ∧ svc_frame_rel s s' ∧ s'.MEM = s.MEM ∧
    (s'.REG 0w = -4w ∧ out = [] ∨
     ∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ s'.REG 0w = n2w n ∧
         out = GENLIST (λi. s.MEM (s.REG 1w + n2w i)) n)
```

#### `forge_contractSpec.svc_write_rel_def`
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

#### `forge_contractSpec.untagged_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a. untagged a ⇔ (63 >< 55) a = 0w
```

#### `forge_contractSpec.whole_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel inp out s inp' out' s'.
    whole_step rrel wrel (inp,out,s) (inp',out',s') ⇔
    ¬is_svc0_at s ∧ NextStateARM8 s = SOME s' ∧ inp' = inp ∧ out' = out ∨
    is_svc0_at s ∧ s.REG 8w = 63w ∧ rrel inp s s' inp' ∧ out' = out ∨
    is_svc0_at s ∧ s.REG 8w = 64w ∧ ∃chunk. wrel s s' chunk ∧ inp' = inp ∧ out' = out ++ chunk
```

#### `forge_contractSpec.words32_in_mem_def`
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
<summary><strong><code>forge_counterProg</code></strong> — Zero-Basis CakeML (8 definitions, 26 theorems)</summary>

Allocation-free 17-byte-buffer CakeML counter loop and CF total correctness proof.

### Definitions

#### `forge_counterProg.COUNTER_IO_EV_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io evs.
    COUNTER_IO_EV io evs =
    one (FFI_part (encode_counter_io io) (mk_ffi_next counter_ffi_part) [«recv16»; «send16»] evs)
```

#### `forge_counterProg.COUNTER_IO_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. COUNTER_IO io = IOx counter_ffi_part io
```

#### `forge_counterProg.counter_prog_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_prog = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_counterProg.event_is_err_def_primitive`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ event_is_err =
  WFREC (@R. WF R)
    (λevent_is_err a.
       case a of
         IO_event (ExtCall n) conf bs => I (17 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w)
       | IO_event (SharedMem v9) conf bs => I F)
```

#### `forge_counterProg.forge_counterProg_env_6_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_counterProg_env_6 = write «counter_main» counter_main_v forge_counterProg_env_5
```

#### `forge_counterProg.forge_counterProg_st_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi po.
    forge_counterProg_st (ffi,po) =
    <|clock := 0; refs := []; ffi := ffi; next_type_stamp := 9; next_exn_stamp := 5;
      eval_state := NONE; ptr_eq_oracle := cap_val_po po|>
```

#### `forge_counterProg.limit_frames_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀xs. limit_frames NONE xs = xs) ∧ ∀n xs. limit_frames (SOME n) xs = TAKE (SUC n) xs
```

#### `forge_counterProg.stop_after_err_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (stop_after_err [] ⇔ T) ∧
  ∀e es. stop_after_err (e::es) ⇔ if event_is_err e then es = [] else stop_after_err es
```

### Theorems

#### `forge_counterProg.cap_val_refs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀po. cap_val_refs po = []
```

#### `forge_counterProg.cap_val_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ WORD cap_val cap_val_v
```

#### `forge_counterProg.counter_io_ffi_part_hprop`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀out.
    FFI_part_hprop
      (SEP_EXISTS rest_inps wlim' evs'.
         &stop_after_err evs' *
         COUNTER_IO_EV <|inputs := rest_inps; outputs := out; write_limit := wlim'|> evs')
```

#### `forge_counterProg.counter_io_split`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st2 io.
    st2.ffi = counter_ffi io ⇒
    ∃h1 h2. SPLIT (st2heap counter_proj st2) (h1,h2) ∧ COUNTER_IO_EV io [] h1
```

#### `forge_counterProg.counter_loop_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inps outs wlim evs bufv bs seq seqv spent spentv.
    LENGTH bs = 17 ∧ WORD seq seqv ∧ WORD spent spentv ∧ EVERY ($¬ ∘ event_is_err) evs ⇒
    app p counter_loop_v [bufv; seqv; spentv]
      (W8ARRAY bufv bs * COUNTER_IO_EV <|inputs := inps; outputs := outs; write_limit := wlim|> evs)
      (POSTv uv.
         &UNIT_TYPE () uv *
         SEP_EXISTS bs' rest_inps wlim' evs'.
           W8ARRAY bufv bs' * &(LENGTH bs' = 17 ∧ stop_after_err evs') *
           COUNTER_IO_EV
             <|inputs := rest_inps;
               outputs := outs ++ limit_frames wlim (SND (SND (counter_run seq spent inps)));
               write_limit := wlim'|> evs')
```

#### `forge_counterProg.counter_main_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inps wlim uv.
    UNIT_TYPE () uv ⇒
    app p counter_main_v [uv]
      (COUNTER_IO_EV <|inputs := inps; outputs := []; write_limit := wlim|> [])
      (POSTv rv.
         &UNIT_TYPE () rv *
         SEP_EXISTS rest_inps wlim' evs'.
           &stop_after_err evs' *
           COUNTER_IO_EV
             <|inputs := rest_inps;
               outputs := limit_frames wlim (SND (SND (counter_run 0w 0w inps)));
               write_limit := wlim'|> evs')
```

#### `forge_counterProg.counter_parts_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io. parts_ok (counter_ffi io) counter_proj
```

#### `forge_counterProg.counter_prog_eq_snoc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_prog = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_counterProg.counter_semantics`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io.
    io.outputs = [] ⇒
    sem_satisfies (semantics_dec_list (init_state (counter_ffi io)) init_env counter_prog)
      (λb.
         ∃io_events.
           b = Terminate Success io_events ∧ stop_after_err io_events ∧
           sent_frames_of io_events =
           limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs))))
```

#### `forge_counterProg.counter_step_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> WORD --> WORD --> PAIR_TYPE WORD (PAIR_TYPE WORD (PAIR_TYPE WORD WORD)))
    counter_step counter_step_v
```

#### `forge_counterProg.event_is_err_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (event_is_err (IO_event (ExtCall n) conf bs) ⇔ 17 ≤ LENGTH bs ∧ SND (HD bs) ≠ 0w) ∧
  (event_is_err (IO_event (SharedMem v7) v1 v2) ⇔ F)
```

#### `forge_counterProg.event_is_err_ind`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀n conf bs. P (IO_event (ExtCall n) conf bs)) ∧
      (∀v7 v1 v2. P (IO_event (SharedMem v7) v1 v2)) ⇒
      ∀v. P v
```

#### `forge_counterProg.le64_byte_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> NUM --> WORD8) le64_byte le64_byte_v
```

#### `forge_counterProg.le64_decode_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD8 --> WORD) le64_decode
    le64_decode_v
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_0_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env_0.c = nsLookup_Mod1 forge_counterProg_env.c ∧
  nsLookup_Mod1 forge_counterProg_env_0.v = nsLookup_Mod1 forge_counterProg_env.v ∧
  nsLookup_Short forge_counterProg_env_0.c = nsLookup_Short forge_counterProg_env.c ∧
  nsLookup_Short forge_counterProg_env_0.v =
  option_choice_f (ALOOKUP [(«le64_byte»,le64_byte_v)]) (nsLookup_Short forge_counterProg_env.v)
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_1_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env_1.c = nsLookup_Mod1 forge_counterProg_env_0.c ∧
  nsLookup_Mod1 forge_counterProg_env_1.v = nsLookup_Mod1 forge_counterProg_env_0.v ∧
  nsLookup_Short forge_counterProg_env_1.c = nsLookup_Short forge_counterProg_env_0.c ∧
  nsLookup_Short forge_counterProg_env_1.v =
  option_choice_f (ALOOKUP [(«cap_val»,cap_val_v)]) (nsLookup_Short forge_counterProg_env_0.v)
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_2_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env_2.c = nsLookup_Mod1 forge_counterProg_env_1.c ∧
  nsLookup_Mod1 forge_counterProg_env_2.v = nsLookup_Mod1 forge_counterProg_env_1.v ∧
  nsLookup_Short forge_counterProg_env_2.c = nsLookup_Short forge_counterProg_env_1.c ∧
  nsLookup_Short forge_counterProg_env_2.v =
  option_choice_f (ALOOKUP [(«counter_step»,counter_step_v)])
    (nsLookup_Short forge_counterProg_env_1.v)
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_3_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env_3.c = nsLookup_Mod1 forge_counterProg_env_2.c ∧
  nsLookup_Mod1 forge_counterProg_env_3.v = nsLookup_Mod1 forge_counterProg_env_2.v ∧
  nsLookup_Short forge_counterProg_env_3.c = nsLookup_Short forge_counterProg_env_2.c ∧
  nsLookup_Short forge_counterProg_env_3.v =
  option_choice_f (ALOOKUP [(«read_u64»,read_u64_v)]) (nsLookup_Short forge_counterProg_env_2.v)
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_4_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env_4.c = nsLookup_Mod1 forge_counterProg_env_3.c ∧
  nsLookup_Mod1 forge_counterProg_env_4.v = nsLookup_Mod1 forge_counterProg_env_3.v ∧
  nsLookup_Short forge_counterProg_env_4.c = nsLookup_Short forge_counterProg_env_3.c ∧
  nsLookup_Short forge_counterProg_env_4.v =
  option_choice_f (ALOOKUP [(«write_u64»,write_u64_v)]) (nsLookup_Short forge_counterProg_env_3.v)
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_5_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env_5.c = nsLookup_Mod1 forge_counterProg_env_4.c ∧
  nsLookup_Mod1 forge_counterProg_env_5.v = nsLookup_Mod1 forge_counterProg_env_4.v ∧
  nsLookup_Short forge_counterProg_env_5.c = nsLookup_Short forge_counterProg_env_4.c ∧
  nsLookup_Short forge_counterProg_env_5.v =
  option_choice_f (ALOOKUP [(«counter_loop»,counter_loop_v)])
    (nsLookup_Short forge_counterProg_env_4.v)
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_6_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env_6.c = nsLookup_Mod1 forge_counterProg_env_5.c ∧
  nsLookup_Mod1 forge_counterProg_env_6.v = nsLookup_Mod1 forge_counterProg_env_5.v ∧
  nsLookup_Short forge_counterProg_env_6.c = nsLookup_Short forge_counterProg_env_5.c ∧
  nsLookup_Short forge_counterProg_env_6.v =
  option_choice_f (ALOOKUP [(«counter_main»,counter_main_v)])
    (nsLookup_Short forge_counterProg_env_5.v)
```

#### `forge_counterProg.nsLookup_forge_counterProg_env_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_counterProg_env.c = nsLookup_Mod1 Word8ArrayProg_env_13.c ∧
  nsLookup_Mod1 forge_counterProg_env.v = nsLookup_Mod1 Word8ArrayProg_env_13.v ∧
  nsLookup_Short forge_counterProg_env.c = nsLookup_Short Word8ArrayProg_env_13.c ∧
  nsLookup_Short forge_counterProg_env.v =
  option_choice_f (ALOOKUP [(«le64_decode»,le64_decode_v)]) (nsLookup_Short Word8ArrayProg_env_13.v)
```

#### `forge_counterProg.read_u64_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀av bs off offv.
    NUM off offv ∧ off + 8 ≤ LENGTH bs ⇒
    app p read_u64_v [av; offv] (W8ARRAY av bs)
      (POSTv wv.
         &WORD
           (le64_decode bs❲off❳ bs❲off + 1❳ bs❲off + 2❳ bs❲off + 3❳ bs❲off + 4❳ bs❲off + 5❳
              bs❲off + 6❳ bs❲off + 7❳) wv * W8ARRAY av bs)
```

#### `forge_counterProg.stop_after_err_prefix_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀es1 es2. es1 ≼ es2 ∧ stop_after_err es2 ∧ (∃e. MEM e es1 ∧ event_is_err e) ⇒ es2 = es1
```

#### `forge_counterProg.stop_after_err_snoc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀es e. EVERY ($¬ ∘ event_is_err) es ⇒ stop_after_err (es ++ [e])
```

#### `forge_counterProg.write_u64_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀av bs off offv w wv.
    NUM off offv ∧ WORD w wv ∧ off + 8 ≤ LENGTH bs ⇒
    app p write_u64_v [av; offv; wv] (W8ARRAY av bs)
      (POSTv uv. &UNIT_TYPE () uv * W8ARRAY av (TAKE off bs ++ le64_encode w ++ DROP (off + 8) bs))
```

</details>

<details>
<summary><strong><code>forge_counterCompile</code></strong> — Verified Compilation (6 definitions, 4 theorems)</summary>

In-logic ARM64 backend compilation theorem linking counter_prog to exact machine-code bytes and bitmaps.

### Definitions

#### `forge_counterCompile.code_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ code = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_counterCompile.compiled`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ compile arm8_config (set_oracle arm8_backend_config oracle) counter_prog = SOME (code,data,info) ∧
  ffis = ffinames_to_string_list (the [] info.lab_conf.ffi_names) ∧ syms = info.symbols ∧
  LENGTH code = 74396 ∧ LENGTH data = 484 ∧ info.lab_conf.shmem_extra = [] ∧
  prog_syntax_ok counter_prog ∧ conf = encode_backend_config info
```

#### `forge_counterCompile.conf_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ conf = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_counterCompile.counter_prog_cv_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x. counter_prog_cv x = from_list from_ast_ast_dec counter_prog
```

#### `forge_counterCompile.data_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ data = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_counterCompile.ffis_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ffis =
  to_list to_mlstring_mlstring
    (cv$Pair
       (cv$Pair (cv$Num 0)
          (cv$Pair (cv$Num 115)
             (cv$Pair (cv$Num 101)
                (cv$Pair (cv$Num 110)
                   (cv$Pair (cv$Num 100) (cv$Pair (cv$Num 49) (cv$Pair (cv$Num 54) (cv$Num 0))))))))
       (cv$Pair
          (cv$Pair (cv$Num 0)
             (cv$Pair (cv$Num 114)
                (cv$Pair (cv$Num 101)
                   (cv$Pair (cv$Num 99)
                      (cv$Pair (cv$Num 118) (cv$Pair (cv$Num 49) (cv$Pair (cv$Num 54) (cv$Num 0))))))))
          (cv$Num 0)))
```

### Theorems

#### `forge_counterCompile.counter_compiled`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ compile arm8_config (set_oracle arm8_backend_config oracle) counter_prog = SOME (code,data,info) ∧
  ffis = ffinames_to_string_list (the [] info.lab_conf.ffi_names) ∧ syms = info.symbols ∧
  LENGTH code = 74396 ∧ LENGTH data = 484 ∧ info.lab_conf.shmem_extra = [] ∧
  prog_syntax_ok counter_prog ∧ conf = encode_backend_config info
```

#### `forge_counterCompile.counter_prog_cv_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ counter_prog_cv x = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>
```

#### `forge_counterCompile.counter_prog_cv_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ from_list from_ast_ast_dec counter_prog = counter_prog_cv (cv$Num 0)
```

#### `forge_counterCompile.temp_oracle_cv_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ from_list (from_option (from_sptree_sptree_spt cv$Num)) temp_oracle = temp_oracle_cv (cv$Num 0)
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
<summary><strong><code>forge_shimProof</code></strong> — Boot & Syscall Shim (5 definitions, 43 theorems)</summary>

43-step ELF startup proof plus universal safety and liveness over Linux read(63)/write(64)/exit_group(94) syscalls.

### Definitions

#### `forge_shimProof.det_run_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀s s'. det_run 0 s s' ⇔ s' = s) ∧
  ∀k s s'. det_run (SUC k) s s' ⇔ ∃s1. ¬is_svc0_at s ∧ NextStateARM8 s = SOME s1 ∧ det_run k s1 s'
```

#### `forge_shimProof.ffi_return_ok_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀new_bytes s s'.
    ffi_return_ok new_bytes s s' ⇔
    arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = bits_of s ∧ s'.SP_EL0 = s.SP_EL0 ∧
    shim_loaded s'.MEM ∧ s'.PC = s.REG 30w ∧
    (∀a. a ∈ forge_prog_addresses ⇒ s'.MEM a = asm_write_bytearray (s.REG 2w) new_bytes s.MEM a) ∧
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

#### `forge_shimProof.mk_real_ffi_if_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P k index new_bytes s.
    mk_real_ffi_if P k (index,new_bytes,s) =
    if ∃s'. P k index new_bytes s s' ∧ ffi_return_ok new_bytes s s' then
      @s'. P k index new_bytes s s' ∧ ffi_return_ok new_bytes s s'
    else forge_canonical_ffi_post new_bytes s
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

#### `forge_shimProof.asm_write_bytearray_drop17`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀p dm m bs f.
    17 ≤ LENGTH bs ∧ LENGTH f = 16 ∧
    read_bytearray p (LENGTH bs) (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    asm_write_bytearray p (0w::f ++ DROP 17 bs) m = (asm_write_bytearray (p + 1w) f m)⦇p ↦ 0w⦈
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

#### `forge_shimProof.cake_exit_to_svc_exit_group`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_EXIT_VENEER ⇒
      ∃k. (let
             s1 = FUNPOW Next k s
           in
             det_run k s s1 ∧ s1.PC = 0x421128w ∧
             svc_exit_group_rel (if s.REG 0w = 0w then 0w else 1w) s1 ∧ s1.MEM = s.MEM ∧
             bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cake_exit_universal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel n s inp out inp_f out_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_EXIT_VENEER ∧
    NRC (whole_step rrel wrel) n (inp,out,s) (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = if s.REG 0w = 0w then 0w else 1w
```

#### `forge_shimProof.cake_install_to_svc_exit_group`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_INSTALL_VENEER ⇒
      (let
         s1 = FUNPOW Next 3 s
       in
         det_run 3 s s1 ∧ s1.PC = 0x421138w ∧ svc_exit_group_rel 2w s1 ∧ s1.MEM = s.MEM ∧
         bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cake_install_universal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀rrel wrel n s inp out inp_f out_f ms_f ec.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_INSTALL_VENEER ∧
    NRC (whole_step rrel wrel) n (inp,out,s) (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    inp_f = inp ∧ out_f = out ∧ ec = 2w
```

#### `forge_shimProof.cml_hdr0`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x400014w ∧
      s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
      (let
         s1 = FUNPOW Next 3 s
       in
         det_run 3 s s1 ∧ s1.PC = 0x400020w ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
         mem_dword s1.MEM 0x450000w = 0x430018w ∧
         (∀a. a <₊ 0x450000w ∨ 0x450000w + 8w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
         (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧ shim_loaded s1.MEM ∧
         arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cml_hdr1`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x400020w ∧
      s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
      (let
         s1 = FUNPOW Next 3 s
       in
         det_run 3 s s1 ∧ s1.PC = 0x40002Cw ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
         mem_dword s1.MEM 0x450008w = 0x430F38w ∧
         (∀a. a <₊ 0x450008w ∨ 0x450008w + 8w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
         (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧ shim_loaded s1.MEM ∧
         arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cml_hdr2`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x40002Cw ∧
      s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
      (let
         s1 = FUNPOW Next 3 s
       in
         det_run 3 s s1 ∧ s1.PC = 0x400038w ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
         mem_dword s1.MEM 0x450010w = 0x430F38w ∧
         (∀a. a <₊ 0x450010w ∨ 0x450010w + 8w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
         (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧ shim_loaded s1.MEM ∧
         arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cml_hdr3`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x400038w ∧
      s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
      (let
         s1 = FUNPOW Next 3 s
       in
         det_run 3 s s1 ∧ s1.PC = 0x400044w ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
         mem_dword s1.MEM 0x450018w = 0x41234Cw ∧
         (∀a. a <₊ 0x450018w ∨ 0x450018w + 8w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
         (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧ shim_loaded s1.MEM ∧
         arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.cml_hdr4`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = 0x400044w ∧
      s.REG 0w = FORGE_CAKE_MAIN ∧ s.REG 1w = FORGE_HEAP ⇒
      (let
         s1 = FUNPOW Next 3 s
       in
         det_run 3 s s1 ∧ s1.PC = 0x400050w ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧ s1.REG 1w = FORGE_HEAP ∧
         mem_dword s1.MEM 0x450020w = 0x420000w ∧
         (∀a. a <₊ 0x450020w ∨ 0x450020w + 8w ≤₊ a ⇒ s1.MEM a = s.MEM a) ∧
         (∀a. a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧ shim_loaded s1.MEM ∧
         arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
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

#### `forge_shimProof.ffirecv16_noerr_exists`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_FFIRECV16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃s'.
       (∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
       ffi_return_ok bytes2 s s') ∧
    (∀f. 17 ≤ w2n (s.REG 3w) ∧ LENGTH f = 16 ⇒
         ∃s'.
           (∀rest out.
              (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (f ++ rest,out,s) (rest,out,s')) ∧
           ffi_return_ok (0w::f ++ DROP 17 bytes2) s s') ∧
    ∀tail_bs.
      17 ≤ w2n (s.REG 3w) ∧ LENGTH tail_bs < 16 ⇒
      ∃s'.
        (∀out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (tail_bs,out,s) ([],out,s')) ∧
        ffi_return_ok (1w::DROP 1 bytes2) s s'
```

#### `forge_shimProof.ffirecv16_universal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err wrel n s inp out inp_f out_f ms_f ec bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_FFIRECV16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n (inp,out,s)
      (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃n' s'.
       n' < n ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
         (inp,out,s') (inp_f,out_f,ms_f) ∧ ffi_return_ok bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
     (∃n' s' frame inp_after.
        n' < n ∧ LENGTH frame = 16 ∧ inp = frame ++ inp_after ∧
        NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
          (inp_after,out,s') (inp_f,out_f,ms_f) ∧ ffi_return_ok (0w::frame ++ DROP 17 bytes2) s s') ∨
     ∃n' s' inp_after.
       n' < n ∧ (allow_err ∨ LENGTH inp < 16) ∧
       NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel) wrel) n'
         (inp_after,out,s') (inp_f,out_f,ms_f) ∧ ffi_return_ok (1w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.ffisend16_noerr_exists`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_FFISEND16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃s'.
       (∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
       ffi_return_ok bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
     ∃s'.
       (∀inp out.
          (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s)
            (inp,out ++ TAKE 16 (DROP 1 bytes2),s')) ∧ ffi_return_ok (0w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.ffisend16_universal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀allow_err rrel n s inp out inp_f out_f ms_f ec bytes2.
    arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_FFISEND16_VENEER ∧
    aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
    read_bytearray (s.REG 2w) (w2n (s.REG 3w))
      (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
    NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n (inp,out,s)
      (inp_f,out_f,ms_f) ∧ svc_exit_group_rel ec ms_f ⇒
    (w2n (s.REG 3w) < 17 ⇒
     ∃n' s'.
       n' < n ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
         (inp,out,s') (inp_f,out_f,ms_f) ∧ ffi_return_ok bytes2 s s') ∧
    (17 ≤ w2n (s.REG 3w) ⇒
     (∃n' s'.
        n' < n ∧
        NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
          (inp,out ++ TAKE 16 (DROP 1 bytes2),s') (inp_f,out_f,ms_f) ∧
        ffi_return_ok (0w::DROP 1 bytes2) s s') ∨
     allow_err ∧
     ∃n' s' chunk.
       n' < n ∧ chunk ≼ TAKE 16 (DROP 1 bytes2) ∧
       NRC (whole_step rrel (if allow_err then svc_write_rel else svc_write_noerr_rel)) n'
         (inp,out ++ chunk,s') (inp_f,out_f,ms_f) ∧ ffi_return_ok (1w::DROP 1 bytes2) s s')
```

#### `forge_shimProof.forge_mc_with_lo55`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi_if inst_if. lo55 (forge_mc_with ffi_if inst_if)
```

#### `forge_shimProof.forge_mc_with_mmio_min`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi_if inst_if. mmio_pcs_min_index (forge_mc_with ffi_if inst_if).ffi_names = SOME 2
```

#### `forge_shimProof.forge_mc_with_start_pc_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi_if inst_if. start_pc_ok (forge_mc_with ffi_if inst_if) FORGE_CAKE_MAIN
```

#### `forge_shimProof.forge_regions_disjoint`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. a ∈ forge_prog_addresses ⇒ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_rx_tmp_region ⇒ a ∉ forge_prog_addresses ∧ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_cml_ptrs_region ⇒ a ∉ forge_prog_addresses ∧ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_heap_hdr_region ⇒ a ∉ forge_cml_ptrs_region ∧ a ∉ forge_shim_code_region) ∧
  (∀a. a ∈ forge_prog_addresses ⇒ untagged a) ∧ ∀a. a ∈ forge_shim_code_region ⇒ untagged a
```

#### `forge_shimProof.mk_real_ffi_if_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B P. real_interfer_ok B (mk_real_ffi_if P) forge_real_install_if
```

#### `forge_shimProof.read_bytearray_mem_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀n p dm m bs.
    read_bytearray p n (λa. if a ∈ dm then SOME (m a) else NONE) = SOME bs ⇒
    LENGTH bs = n ∧ ∀i. i < n ⇒ p + n2w i ∈ dm ∧ m (p + n2w i) = bs❲i❳
```

#### `forge_shimProof.real_interfer_ok_imp_erase_ok`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀B ffi_if inst_if.
    real_interfer_ok B ffi_if inst_if ⇒
    ffi_interfer_ok FORGE_CAKE_MAIN (erase_mc B (forge_mc_with ffi_if inst_if)) ∧
    install_interfer_ok FORGE_CAKE_MAIN FORGE_CBSPACE (erase_mc B (forge_mc_with ffi_if inst_if)) ∧
    interference_ok (erase_mc B (forge_mc_with ffi_if inst_if)).next_interfer
      ((erase_mc B (forge_mc_with ffi_if inst_if)).target.proj forge_prog_addresses)
```

#### `forge_shimProof.shim_loaded_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀m1 m2. (∀a. a ∈ forge_shim_code_region ⇒ m1 a = m2 a) ⇒ (shim_loaded m1 ⇔ shim_loaded m2)
```

#### `forge_shimProof.start_16_steps`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_SHIM_BASE ⇒
      (let
         s1 = FUNPOW Next 16 s
       in
         det_run 16 s s1 ∧ s1.PC = FORGE_VENEERS_BASE ∧
         mem_dword s1.MEM FORGE_CML_HEAP = FORGE_HEAP ∧
         mem_dword s1.MEM FORGE_CML_STACK = FORGE_STACK ∧
         mem_dword s1.MEM FORGE_CML_STACKEND = FORGE_STACKEND ∧
         (∀a. a ∉ forge_cml_ptrs_region ⇒ s1.MEM a = s.MEM a) ∧ shim_loaded s1.MEM ∧
         arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0)
```

#### `forge_shimProof.startup_to_cake_main`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_SHIM_BASE ⇒
      (let
         s1 = FUNPOW Next 43 s
       in
         det_run 43 s s1 ∧ s1.PC = FORGE_CAKE_MAIN ∧ s1.REG 0w = FORGE_CAKE_MAIN ∧
         s1.REG 1w = FORGE_HEAP ∧ s1.REG 2w = FORGE_STACK ∧ s1.REG 3w = FORGE_STACKEND ∧
         mem_dword s1.MEM FORGE_HEAP = FORGE_CAKE_BITMAPS ∧
         mem_dword s1.MEM (FORGE_HEAP + 8w) = FORGE_BM_BUF_END ∧
         mem_dword s1.MEM (FORGE_HEAP + 16w) = FORGE_BM_BUF_END ∧
         mem_dword s1.MEM (FORGE_HEAP + 24w) = FORGE_CB_BEGIN ∧
         mem_dword s1.MEM (FORGE_HEAP + 32w) = FORGE_CB_END ∧
         (∀a. a ∉ forge_cml_ptrs_region ∧ a ∉ forge_heap_hdr_region ⇒ s1.MEM a = s.MEM a) ∧
         shim_loaded s1.MEM ∧ arm8_ok (erase s1) ∧ sp_ok s1 ∧ bits_of s1 = bits_of s ∧
         s1.SP_EL0 = s.SP_EL0)
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

