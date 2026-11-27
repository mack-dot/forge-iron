# Verified Theorem Catalog

> **Auto-generated directly from compiled HOL4 `.dat` theory files** by `runtime/export_theorem_catalog.sml`.
> Verified byte-for-byte on every run of `scripts/iron_law.py`. Do not hand-edit this file.

## Global HOL4 Kernel Tag Summary

| Metric | Measured Kernel Value |
| --- | --- |
| Top-level theory | `forge_m2Kernel` |
| `forge_*` theories compiled | `11` |
| Transitive ancestry closure size | `439` theories |
| Exported `forge_*` definitions | `177` |
| Exported `forge_*` theorems | `285` |
| Total verified `forge_*` items | `462` |
| `HYP_COUNT` (max hypotheses across all items) | `0` |
| `ORACLES` (union of all theorem/definition oracle tags) | `[DISK_THM]` |
| `DIRECT_AXIOMS` (union of all direct axiom tags) | `[]` |
| `AXIOMS` (transitive `DB.axioms` closure) | `4`: `bool.BOOL_CASES_AX`, `bool.ETA_AX`, `bool.INFINITY_AX`, `bool.SELECT_AX` |

## Crown-Jewel Specifications & Theorems

| Layer | Theory | Theorem / Definition | Status | Plain-English Guarantee |
| --- | --- | --- | --- | --- |
| Pure Spec (M2) | `forge_guardrailSpec` | `frame_bijection` | `verified` | Lossless 64-byte LE64 encode/decode bijection for guardrail frames. |
| Pure Spec (M2) | `forge_guardrailSpec` | `gr_run_preserves_inv` | `verified` | Exact fund conservation (deposits = balance + spent - refunds), rolling cap, and zero u64 wraparound across every request stream. |
| Pure Spec (M2) | `forge_guardrailSpec` | `gr_safety_denials` | `verified` | Non-allowlisted destinations, replayed nonces, and double refunds are unconditionally denied with state unchanged. |
| Frozen Runtime Contract | `forge_runtimeSpec` | `forge_slot_loaded_def` | `verified` | SHA-256 pinned 256 KB RX code slot [0x400000..0x440000) and fixed _start (0x450000) contract for any kernel. |
| Frozen Runtime Contract | `forge_runtimeSpec` | `whole_step_def` | `verified` | SHA-256 pinned whole-binary transition relation combining raw arm8$Next with Linux read(63)/write(64) svc #0 contracts. |
| Generic 64B Frame ABI | `forge_frame64Spec` | `frame64_roundtrip` | `verified` | Round-trip bijection proving 64-byte LE64 binary framing is lossless for all 8-word frames. |
| Generic 64B ML Runner | `forge_frameRunner` | `run_frame64_kernel_spec` | `verified` | Polymorphic CF specification of generic CakeML recv64 -> translated step -> send64 runner for zero-SL kernels. |
| Zero-SL CakeML (M2) | `forge_guardrailProg` | `guardrail_semantics` | `verified` | Automatically ml_translator-synthesized CakeML guardrail_prog terminates cleanly and emits exact frame64_run gr_step frames. |
| Verified Compilation | `forge_guardrailCompile` | `guardrail_compiled` | `verified` | In-logic CakeML arm8 backend evaluation theorem binding guardrail_prog to exact machine-code bytes (code) and bitmaps (data). |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `encoded_bytes_in_mem_not_svc0` | `verified` | No compiled CakeML arm8_config instruction ever encodes the AArch64 svc #0 opcode (0xD4000001). |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `arm8_target_exact_encoder_correct` | `verified` | Exact arm8$Next encoder correctness proving zero CPU exceptions and strict SP_EL0 preservation on every compiled instruction. |
| ARMv8 Erasure & No-SVC0 | `forge_arm8Erasure` | `machine_sem_real_eq_exact` | `verified` | Unconditional equivalence between real-bits arm8_target_real (TBI0/TBI1/SA0) and erased targetSem with zero b ≠ Fail escape hatch. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `startup_to_cake_main_slot` | `verified` | Parameterized 43-step ARM64 proof from fixed _start (0x450000) through cml_main to cake_main (0x4000B0) for any <=256 KB code blob. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffirecv16_universal_slot` | `verified` | Universal safety of raw ARM64 ffirecv16 at 0x450040 over partial reads, EINTR, truncated EOF, and fatal errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffisend16_universal_slot` | `verified` | Universal safety of raw ARM64 ffisend16 at 0x4500C0 over partial writes, EINTR, and fatal/EPIPE errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffirecv64_universal_slot` | `verified` | Universal safety of raw ARM64 ffirecv64 at 0x450040 over partial reads (1..64B), EINTR, truncated EOF, and fatal errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `ffisend64_universal_slot` | `verified` | Universal safety of raw ARM64 ffisend64 at 0x4500C0 over partial writes (1..64B), EINTR, and fatal/EPIPE errors. |
| Frozen 256KB Shim Proof | `forge_shimProof` | `cake_exit_universal_slot` | `verified` | Universal termination proof of exit veneer + cml_exit to Linux svc #0 exit_group(94) with code 0 or 1. |
| Generic 64B E2E Compose | `forge_frame64Compose` | `forge_frame64_kernel_compose` | `verified` | Polymorphic whole-binary composition theorem lifting any ml_translator 64-byte kernel from _start to exit_group(94). |
| Non-Vacuity Witness | `forge_m2Kernel` | `forge_m2_nonvacuous` | `verified` | Constructive witness exhibiting a concrete Linux EL0 ARM64 state (TBI0=T, TBI1=F, SA0=T, 16B-aligned SP_EL0) satisfying M2 forge_slot_loaded. |
| Unified End-to-End (M2) | `forge_m2Kernel` | `forge_m2_kernel_correct` | `verified` | Single whole-binary theorem (exact Term.aconv-pinned) connecting fixed _start (0x450000) across RTC whole_step to svc #0 exit_group(94) and frame64_run gr_step. |

## Theory-by-Theory Counts

| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |
| --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `forge_guardrailSpec` | Pure Spec (M2) | `verified` | 32 | 26 | 0 | `[DISK_THM]` | `[]` |
| `forge_runtimeSpec` | Frozen Runtime Contract | `verified` | 65 | 0 | 0 | `[DISK_THM]` | `[]` |
| `forge_frame64Spec` | Generic 64B Frame ABI | `verified` | 36 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_frameRunner` | Generic 64B ML Runner | `verified` | 22 | 24 | 0 | `[DISK_THM]` | `[]` |
| `forge_guardrailProg` | Zero-SL CakeML (M2) | `verified` | 4 | 56 | 0 | `[DISK_THM]` | `[]` |
| `forge_guardrailCompile` | Verified Compilation | `verified` | 6 | 4 | 0 | `[DISK_THM]` | `[]` |
| `forge_arm8Erasure` | ARMv8 Erasure & No-SVC0 | `verified` | 4 | 51 | 0 | `[DISK_THM]` | `[]` |
| `forge_shimProof` | Frozen 256KB Shim Proof | `verified` | 6 | 50 | 0 | `[DISK_THM]` | `[]` |
| `forge_slotUtil` | Frozen 256KB Slot Util | `verified` | 0 | 21 | 0 | `[DISK_THM]` | `[]` |
| `forge_frame64Compose` | Generic 64B E2E Compose | `verified` | 2 | 1 | 0 | `[DISK_THM]` | `[]` |
| `forge_m2Kernel` | Unified End-to-End (M2) | `verified` | 0 | 2 | 0 | `[DISK_THM]` | `[]` |

## Verbatim Exported Statements (`DB.definitions` & `DB.theorems`)

Each section below dumps every exported definition and theorem directly from the compiled HOL4 `.dat` file using `Hol_pp.thm_to_string`.

<details>
<summary><strong><code>forge_guardrailSpec</code></strong> — Pure Spec (M2) (32 definitions, 26 theorems)</summary>

Frozen 91-line pure HOL4 AI spending guardrail spec (deposit, spend, refund, query, conservation, cap, nonce, allowlist).

### Definitions

#### `forge_guardrailSpec.decode_frame_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀bs. decode_frame bs = frame64_decode bs
```

#### `forge_guardrailSpec.dest_allowed_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀mask d. dest_allowed mask d ⇔ d <₊ 64w ∧ word_bit (w2n d) mask
```

#### `forge_guardrailSpec.encode_frame_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀fr. encode_frame fr = frame64_encode fr
```

#### `forge_guardrailSpec.gr_init_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ gr_init =
  <|deposits := 0w; balance := 0w; spent := 0w; refunds := 0w; cap := 0x186A0w; allowmask := 7w;
    nonce := 0w; last_tx := 0w; last_amt := 0w; tx_open := F|>
```

#### `forge_guardrailSpec.gr_inv_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st.
    gr_inv st ⇔
    st.refunds ≤₊ st.spent ∧ (st.tx_open ⇒ st.last_amt ≤₊ st.spent − st.refunds) ∧
    w2n st.deposits = w2n st.balance + (w2n st.spent − w2n st.refunds) ∧
    st.spent − st.refunds ≤₊ st.cap
```

#### `forge_guardrailSpec.gr_resp_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ok code st.
    gr_resp ok code st =
    Frame64 ok code st.deposits st.balance (st.spent − st.refunds) st.refunds st.nonce st.last_tx
```

#### `forge_guardrailSpec.gr_state_ABSREP`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀a. gr_state_ABS (gr_state_REP a) = a) ∧ ∀r. (λx. T) r ⇔ gr_state_REP (gr_state_ABS r) = r
```

#### `forge_guardrailSpec.gr_state_CONS_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ gr_state_CONS = gr_state_ABS
```

#### `forge_guardrailSpec.gr_state_TY_DEF`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃rep. TYPE_DEFINITION (λx. T) rep
```

#### `forge_guardrailSpec.gr_state_case_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 f.
    gr_state_CASE (gr_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) f = f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
```

#### `forge_guardrailSpec.gr_state_size_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9.
    gr_state_size (gr_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) =
    1 +
    (w2n a0 +
     (w2n a1 +
      (w2n a2 + (w2n a3 + (w2n a4 + (w2n a5 + (w2n a6 + (w2n a7 + (w2n a8 + bool_size a9)))))))))
```

#### `forge_guardrailSpec.gr_step_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st op agent arg2 amt arg4 v0 v1 v2.
    gr_step st (Frame64 op agent arg2 amt arg4 v0 v1 v2) =
    if op = 1w then
      if amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.deposits ∧ st.spent − st.refunds ≤₊ arg4 then
        (let
           st' =
             st with
             <|deposits := st.deposits + amt; balance := st.balance + amt; cap := arg4;
               allowmask := arg2|>
         in
           (st',gr_resp 1w 0w st'))
      else (st,gr_resp 0w 1w st)
    else if op = 2w then
      if
        amt ≠ 0w ∧ dest_allowed st.allowmask arg2 ∧ st.nonce ≠ 0xFFFFFFFFFFFFFFFFw ∧
        arg4 = st.nonce + 1w ∧ st.last_tx ≠ 0xFFFFFFFFFFFFFFFFw ∧ amt ≤₊ st.balance ∧
        amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.spent ∧ amt ≤₊ st.cap − (st.spent − st.refunds)
      then
        (let
           st' =
             st with
             <|balance := st.balance − amt; spent := st.spent + amt; nonce := arg4;
               last_tx := st.last_tx + 1w; last_amt := amt; tx_open := T|>
         in
           (st',gr_resp 1w 0w st'))
      else (st,gr_resp 0w 2w st)
    else if op = 3w then
      if
        amt ≠ 0w ∧ st.tx_open ∧ arg4 = st.last_tx ∧ amt ≤₊ st.last_amt ∧
        amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.refunds ∧ amt ≤₊ 0xFFFFFFFFFFFFFFFFw − st.balance
      then
        (let
           st' = st with <|balance := st.balance + amt; refunds := st.refunds + amt; tx_open := F|>
         in
           (st',gr_resp 1w 0w st'))
      else (st,gr_resp 0w 3w st)
    else if op = 4w then (st,gr_resp 1w 0w st)
    else (st,gr_resp 0w 4w st)
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_allowmask_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).allowmask = c4
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_allowmask_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with allowmask updated_by f =
    gr_state c c0 c1 c2 c3 (f c4) c5 c6 c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_balance_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).balance = c0
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_balance_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with balance updated_by f =
    gr_state c (f c0) c1 c2 c3 c4 c5 c6 c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_cap_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).cap = c3
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_cap_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with cap updated_by f =
    gr_state c c0 c1 c2 (f c3) c4 c5 c6 c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_deposits_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).deposits = c
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_deposits_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with deposits updated_by f =
    gr_state (f c) c0 c1 c2 c3 c4 c5 c6 c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_last_amt_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).last_amt = c7
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_last_amt_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with last_amt updated_by f =
    gr_state c c0 c1 c2 c3 c4 c5 c6 (f c7) b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_last_tx_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).last_tx = c6
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_last_tx_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with last_tx updated_by f =
    gr_state c c0 c1 c2 c3 c4 c5 (f c6) c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_nonce_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).nonce = c5
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_nonce_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with nonce updated_by f =
    gr_state c c0 c1 c2 c3 c4 (f c5) c6 c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_refunds_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).refunds = c2
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_refunds_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with refunds updated_by f =
    gr_state c c0 c1 (f c2) c3 c4 c5 c6 c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_spent_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).spent = c1
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_spent_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with spent updated_by f =
    gr_state c c0 (f c1) c2 c3 c4 c5 c6 c7 b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_tx_open_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).tx_open ⇔ b
```

#### `forge_guardrailSpec.recordtype_gr_state_seldef_tx_open_fupd_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with tx_open updated_by f =
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 (f b)
```

### Theorems

#### `forge_guardrailSpec.EXISTS_gr_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∃g. P g) ⇔
      ∃c7 c6 c5 c4 c3 c2 c1 c0 c b.
        P
          <|deposits := c7; balance := c6; spent := c5; refunds := c4; cap := c3; allowmask := c2;
            nonce := c1; last_tx := c0; last_amt := c; tx_open := b|>
```

#### `forge_guardrailSpec.FORALL_gr_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀g. P g) ⇔
      ∀c7 c6 c5 c4 c3 c2 c1 c0 c b.
        P
          <|deposits := c7; balance := c6; spent := c5; refunds := c4; cap := c3; allowmask := c2;
            nonce := c1; last_tx := c0; last_amt := c; tx_open := b|>
```

#### `forge_guardrailSpec.datatype_gr_state`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ DATATYPE
    (record gr_state deposits balance spent refunds cap allowmask nonce last_tx last_amt tx_open)
```

#### `forge_guardrailSpec.frame_bijection`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀fr. decode_frame (encode_frame fr) = fr) ∧
  ∀bs. LENGTH bs = 64 ⇒ encode_frame (decode_frame bs) = bs
```

#### `forge_guardrailSpec.gr_inv_init`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ gr_inv gr_init
```

#### `forge_guardrailSpec.gr_run_preserves_inv`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inps st. gr_inv st ⇒ gr_inv (FST (frame64_run gr_step st inps))
```

#### `forge_guardrailSpec.gr_safety_denials`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀st ag d amt nc r5 r6 r7.
     ¬dest_allowed st.allowmask d ⇒ FST (gr_step st (Frame64 2w ag d amt nc r5 r6 r7)) = st) ∧
  (∀st ag d amt r5 r6 r7. FST (gr_step st (Frame64 2w ag d amt st.nonce r5 r6 r7)) = st) ∧
  ∀st ag a2 amt tx r5 r6 r7. ¬st.tx_open ⇒ FST (gr_step st (Frame64 3w ag a2 amt tx r5 r6 r7)) = st
```

#### `forge_guardrailSpec.gr_state_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a0' a1' a2' a3' a4' a5' a6' a7' a8' a9'.
    gr_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = gr_state a0' a1' a2' a3' a4' a5' a6' a7' a8' a9' ⇔
    a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3' ∧ a4 = a4' ∧ a5 = a5' ∧ a6 = a6' ∧ a7 = a7' ∧
    a8 = a8' ∧ (a9 ⇔ a9')
```

#### `forge_guardrailSpec.gr_state_Axiom`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀f0. ∃h. ∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9.
    h (gr_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) = f0 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
```

#### `forge_guardrailSpec.gr_state_accessors`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).deposits = c) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).balance = c0) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).spent = c1) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).refunds = c2) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).cap = c3) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).allowmask = c4) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).nonce = c5) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).last_tx = c6) ∧
  (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).last_amt = c7) ∧
  ∀c c0 c1 c2 c3 c4 c5 c6 c7 b. (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b).tx_open ⇔ b
```

#### `forge_guardrailSpec.gr_state_accfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_guardrailSpec.gr_state_case_cong`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀M M' f.
    M = M' ∧
    (∀a0 a1 a2 a3 a4 a5 a6 a7 a8 a9.
       M' = gr_state a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⇒
       f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = f' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ⇒
    gr_state_CASE M f = gr_state_CASE M' f'
```

#### `forge_guardrailSpec.gr_state_case_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ gr_state_CASE x f = v ⇔
  ∃c c0 c1 c2 c3 c4 c5 c6 c7 b.
    x = gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b ∧ f c c0 c1 c2 c3 c4 c5 c6 c7 b = v
```

#### `forge_guardrailSpec.gr_state_component_equality`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀g1 g2.
    g1 = g2 ⇔
    g1.deposits = g2.deposits ∧ g1.balance = g2.balance ∧ g1.spent = g2.spent ∧
    g1.refunds = g2.refunds ∧ g1.cap = g2.cap ∧ g1.allowmask = g2.allowmask ∧ g1.nonce = g2.nonce ∧
    g1.last_tx = g2.last_tx ∧ g1.last_amt = g2.last_amt ∧ (g1.tx_open ⇔ g2.tx_open)
```

#### `forge_guardrailSpec.gr_state_fn_updates`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with deposits updated_by f =
     gr_state (f c) c0 c1 c2 c3 c4 c5 c6 c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with balance updated_by f =
     gr_state c (f c0) c1 c2 c3 c4 c5 c6 c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with spent updated_by f =
     gr_state c c0 (f c1) c2 c3 c4 c5 c6 c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with refunds updated_by f =
     gr_state c c0 c1 (f c2) c3 c4 c5 c6 c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with cap updated_by f =
     gr_state c c0 c1 c2 (f c3) c4 c5 c6 c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with allowmask updated_by f =
     gr_state c c0 c1 c2 c3 (f c4) c5 c6 c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with nonce updated_by f =
     gr_state c c0 c1 c2 c3 c4 (f c5) c6 c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with last_tx updated_by f =
     gr_state c c0 c1 c2 c3 c4 c5 (f c6) c7 b) ∧
  (∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
     gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with last_amt updated_by f =
     gr_state c c0 c1 c2 c3 c4 c5 c6 (f c7) b) ∧
  ∀f c c0 c1 c2 c3 c4 c5 c6 c7 b.
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b with tx_open updated_by f =
    gr_state c c0 c1 c2 c3 c4 c5 c6 c7 (f b)
```

#### `forge_guardrailSpec.gr_state_fupdcanon`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g0 g f.
     g with <|balance updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; balance updated_by f|>) ∧
  (∀g0 g f.
     g with <|spent updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; spent updated_by f|>) ∧
  (∀g0 g f.
     g with <|spent updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; spent updated_by f|>) ∧
  (∀g0 g f.
     g with <|refunds updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; refunds updated_by f|>) ∧
  (∀g0 g f.
     g with <|refunds updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; refunds updated_by f|>) ∧
  (∀g0 g f.
     g with <|refunds updated_by f; spent updated_by g0|> =
     g with <|spent updated_by g0; refunds updated_by f|>) ∧
  (∀g0 g f.
     g with <|cap updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; cap updated_by f|>) ∧
  (∀g0 g f.
     g with <|cap updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; cap updated_by f|>) ∧
  (∀g0 g f.
     g with <|cap updated_by f; spent updated_by g0|> =
     g with <|spent updated_by g0; cap updated_by f|>) ∧
  (∀g0 g f.
     g with <|cap updated_by f; refunds updated_by g0|> =
     g with <|refunds updated_by g0; cap updated_by f|>) ∧
  (∀g0 g f.
     g with <|allowmask updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; allowmask updated_by f|>) ∧
  (∀g0 g f.
     g with <|allowmask updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; allowmask updated_by f|>) ∧
  (∀g0 g f.
     g with <|allowmask updated_by f; spent updated_by g0|> =
     g with <|spent updated_by g0; allowmask updated_by f|>) ∧
  (∀g0 g f.
     g with <|allowmask updated_by f; refunds updated_by g0|> =
     g with <|refunds updated_by g0; allowmask updated_by f|>) ∧
  (∀g0 g f.
     g with <|allowmask updated_by f; cap updated_by g0|> =
     g with <|cap updated_by g0; allowmask updated_by f|>) ∧
  (∀g0 g f.
     g with <|nonce updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; nonce updated_by f|>) ∧
  (∀g0 g f.
     g with <|nonce updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; nonce updated_by f|>) ∧
  (∀g0 g f.
     g with <|nonce updated_by f; spent updated_by g0|> =
     g with <|spent updated_by g0; nonce updated_by f|>) ∧
  (∀g0 g f.
     g with <|nonce updated_by f; refunds updated_by g0|> =
     g with <|refunds updated_by g0; nonce updated_by f|>) ∧
  (∀g0 g f.
     g with <|nonce updated_by f; cap updated_by g0|> =
     g with <|cap updated_by g0; nonce updated_by f|>) ∧
  (∀g0 g f.
     g with <|nonce updated_by f; allowmask updated_by g0|> =
     g with <|allowmask updated_by g0; nonce updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; last_tx updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; last_tx updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; spent updated_by g0|> =
     g with <|spent updated_by g0; last_tx updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; refunds updated_by g0|> =
     g with <|refunds updated_by g0; last_tx updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; cap updated_by g0|> =
     g with <|cap updated_by g0; last_tx updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; allowmask updated_by g0|> =
     g with <|allowmask updated_by g0; last_tx updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; nonce updated_by g0|> =
     g with <|nonce updated_by g0; last_tx updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; spent updated_by g0|> =
     g with <|spent updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; refunds updated_by g0|> =
     g with <|refunds updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; cap updated_by g0|> =
     g with <|cap updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; allowmask updated_by g0|> =
     g with <|allowmask updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; nonce updated_by g0|> =
     g with <|nonce updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; last_tx updated_by g0|> =
     g with <|last_tx updated_by g0; last_amt updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; deposits updated_by g0|> =
     g with <|deposits updated_by g0; tx_open updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; balance updated_by g0|> =
     g with <|balance updated_by g0; tx_open updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; spent updated_by g0|> =
     g with <|spent updated_by g0; tx_open updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; refunds updated_by g0|> =
     g with <|refunds updated_by g0; tx_open updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; cap updated_by g0|> =
     g with <|cap updated_by g0; tx_open updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; allowmask updated_by g0|> =
     g with <|allowmask updated_by g0; tx_open updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; nonce updated_by g0|> =
     g with <|nonce updated_by g0; tx_open updated_by f|>) ∧
  (∀g0 g f.
     g with <|tx_open updated_by f; last_tx updated_by g0|> =
     g with <|last_tx updated_by g0; tx_open updated_by f|>) ∧
  ∀g0 g f.
    g with <|tx_open updated_by f; last_amt updated_by g0|> =
    g with <|last_amt updated_by g0; tx_open updated_by f|>
```

#### `forge_guardrailSpec.gr_state_fupdcanon_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ <large theorem> = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_guardrailSpec.gr_state_fupdfupds`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g0 g f.
     g with <|deposits updated_by f; deposits updated_by g0|> = g with deposits updated_by f ∘ g0) ∧
  (∀g0 g f.
     g with <|balance updated_by f; balance updated_by g0|> = g with balance updated_by f ∘ g0) ∧
  (∀g0 g f. g with <|spent updated_by f; spent updated_by g0|> = g with spent updated_by f ∘ g0) ∧
  (∀g0 g f.
     g with <|refunds updated_by f; refunds updated_by g0|> = g with refunds updated_by f ∘ g0) ∧
  (∀g0 g f. g with <|cap updated_by f; cap updated_by g0|> = g with cap updated_by f ∘ g0) ∧
  (∀g0 g f.
     g with <|allowmask updated_by f; allowmask updated_by g0|> = g with allowmask updated_by f ∘ g0) ∧
  (∀g0 g f. g with <|nonce updated_by f; nonce updated_by g0|> = g with nonce updated_by f ∘ g0) ∧
  (∀g0 g f.
     g with <|last_tx updated_by f; last_tx updated_by g0|> = g with last_tx updated_by f ∘ g0) ∧
  (∀g0 g f.
     g with <|last_amt updated_by f; last_amt updated_by g0|> = g with last_amt updated_by f ∘ g0) ∧
  ∀g0 g f. g with <|tx_open updated_by f; tx_open updated_by g0|> = g with tx_open updated_by f ∘ g0
```

#### `forge_guardrailSpec.gr_state_fupdfupds_comp`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((∀g0 f. deposits_fupd f ∘ deposits_fupd g0 = deposits_fupd (f ∘ g0)) ∧
   ∀h g0 f. deposits_fupd f ∘ deposits_fupd g0 ∘ h = deposits_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. balance_fupd f ∘ balance_fupd g0 = balance_fupd (f ∘ g0)) ∧
   ∀h g0 f. balance_fupd f ∘ balance_fupd g0 ∘ h = balance_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. spent_fupd f ∘ spent_fupd g0 = spent_fupd (f ∘ g0)) ∧
   ∀h g0 f. spent_fupd f ∘ spent_fupd g0 ∘ h = spent_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. refunds_fupd f ∘ refunds_fupd g0 = refunds_fupd (f ∘ g0)) ∧
   ∀h g0 f. refunds_fupd f ∘ refunds_fupd g0 ∘ h = refunds_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. cap_fupd f ∘ cap_fupd g0 = cap_fupd (f ∘ g0)) ∧
   ∀h g0 f. cap_fupd f ∘ cap_fupd g0 ∘ h = cap_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. allowmask_fupd f ∘ allowmask_fupd g0 = allowmask_fupd (f ∘ g0)) ∧
   ∀h g0 f. allowmask_fupd f ∘ allowmask_fupd g0 ∘ h = allowmask_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. nonce_fupd f ∘ nonce_fupd g0 = nonce_fupd (f ∘ g0)) ∧
   ∀h g0 f. nonce_fupd f ∘ nonce_fupd g0 ∘ h = nonce_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. last_tx_fupd f ∘ last_tx_fupd g0 = last_tx_fupd (f ∘ g0)) ∧
   ∀h g0 f. last_tx_fupd f ∘ last_tx_fupd g0 ∘ h = last_tx_fupd (f ∘ g0) ∘ h) ∧
  ((∀g0 f. last_amt_fupd f ∘ last_amt_fupd g0 = last_amt_fupd (f ∘ g0)) ∧
   ∀h g0 f. last_amt_fupd f ∘ last_amt_fupd g0 ∘ h = last_amt_fupd (f ∘ g0) ∘ h) ∧
  (∀g0 f. tx_open_fupd f ∘ tx_open_fupd g0 = tx_open_fupd (f ∘ g0)) ∧
  ∀h g0 f. tx_open_fupd f ∘ tx_open_fupd g0 ∘ h = tx_open_fupd (f ∘ g0) ∘ h
```

#### `forge_guardrailSpec.gr_state_fupdselfid`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (∀g. g with deposits := g.deposits = g) ∧ (∀g. g with balance := g.balance = g) ∧
  (∀g. g with spent := g.spent = g) ∧ (∀g. g with refunds := g.refunds = g) ∧
  (∀g. g with cap := g.cap = g) ∧ (∀g. g with allowmask := g.allowmask = g) ∧
  (∀g. g with nonce := g.nonce = g) ∧ (∀g. g with last_tx := g.last_tx = g) ∧
  (∀g. g with last_amt := g.last_amt = g) ∧ ∀g. g with tx_open := g.tx_open = g
```

#### `forge_guardrailSpec.gr_state_induction`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀P. (∀c c0 c1 c2 c3 c4 c5 c6 c7 b. P (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b)) ⇒ ∀g. P g
```

#### `forge_guardrailSpec.gr_state_literal_11`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c71 c61 c51 c41 c31 c21 c11 c01 c1 b1 c72 c62 c52 c42 c32 c22 c12 c02 c2 b2.
    <|deposits := c71; balance := c61; spent := c51; refunds := c41; cap := c31; allowmask := c21;
      nonce := c11; last_tx := c01; last_amt := c1; tx_open := b1|> =
    <|deposits := c72; balance := c62; spent := c52; refunds := c42; cap := c32; allowmask := c22;
      nonce := c12; last_tx := c02; last_amt := c2; tx_open := b2|> ⇔
    c71 = c72 ∧ c61 = c62 ∧ c51 = c52 ∧ c41 = c42 ∧ c31 = c32 ∧ c21 = c22 ∧ c11 = c12 ∧ c01 = c02 ∧
    c1 = c2 ∧ (b1 ⇔ b2)
```

#### `forge_guardrailSpec.gr_state_literal_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀g. ∃c7 c6 c5 c4 c3 c2 c1 c0 c b.
    g =
    <|deposits := c7; balance := c6; spent := c5; refunds := c4; cap := c3; allowmask := c2;
      nonce := c1; last_tx := c0; last_amt := c; tx_open := b|>
```

#### `forge_guardrailSpec.gr_state_nchotomy`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀gg. ∃c c0 c1 c2 c3 c4 c5 c6 c7 b. gg = gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b
```

#### `forge_guardrailSpec.gr_state_updates_eq_literal`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀g c7 c6 c5 c4 c3 c2 c1 c0 c b.
    g with
    <|deposits := c7; balance := c6; spent := c5; refunds := c4; cap := c3; allowmask := c2;
      nonce := c1; last_tx := c0; last_amt := c; tx_open := b|> =
    <|deposits := c7; balance := c6; spent := c5; refunds := c4; cap := c3; allowmask := c2;
      nonce := c1; last_tx := c0; last_amt := c; tx_open := b|>
```

#### `forge_guardrailSpec.gr_step_preserves_inv`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀st fr st' resp. gr_inv st ∧ gr_step st fr = (st',resp) ⇒ gr_inv st'
```

</details>

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
<summary><strong><code>forge_guardrailProg</code></strong> — Zero-SL CakeML (M2) (4 definitions, 56 theorems)</summary>

Automatically ml_translator-synthesized CakeML guardrail program composed with frozen forge_frameRunner.

### Definitions

#### `forge_guardrailProg.FORGE_GUARDRAILSPEC_GR_STATE_v_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀c c0 c1 c2 c3 c4 c5 c6 c7 b.
    FORGE_GUARDRAILSPEC_GR_STATE_v (gr_state c c0 c1 c2 c3 c4 c5 c6 c7 b) =
    Conv (SOME (TypeStamp «Recordtypegr_state» 10))
      [WORD_v c; WORD_v c0; WORD_v c1; WORD_v c2; WORD_v c3; WORD_v c4; WORD_v c5; WORD_v c6;
       WORD_v c7; BOOL_v b]
```

#### `forge_guardrailProg.forge_guardrailProg_env_24_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ forge_guardrailProg_env_24 = write «guardrail_main» guardrail_main_v forge_guardrailProg_env_23
```

#### `forge_guardrailProg.forge_guardrailProg_st_0_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ffi po.
    forge_guardrailProg_st_0 (ffi,po) =
    <|clock := 0; refs := []; ffi := ffi; next_type_stamp := 11; next_exn_stamp := 5;
      eval_state := NONE; ptr_eq_oracle := gr_init_po po|>
```

#### `forge_guardrailProg.guardrail_prog_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ guardrail_prog = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

### Theorems

#### `forge_guardrailProg.FORGE_GUARDRAILSPEC_GR_STATE_TYPE_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x_10_x1_1_ x_9_x1_2_ x_8_x1_3_ x_7_x1_4_ x_6_x1_5_ x_5_x1_6_ x_4_x1_7_ x_3_x1_8_ x_2_x1_9_
      x_1_x1_10_ v.
    FORGE_GUARDRAILSPEC_GR_STATE_TYPE
      (gr_state x_10_x1_1_ x_9_x1_2_ x_8_x1_3_ x_7_x1_4_ x_6_x1_5_ x_5_x1_6_ x_4_x1_7_ x_3_x1_8_
         x_2_x1_9_ x_1_x1_10_) v ⇔
    ∃v1_1 v1_2 v1_3 v1_4 v1_5 v1_6 v1_7 v1_8 v1_9 v1_10.
      v =
      Conv (SOME (TypeStamp «Recordtypegr_state» 10))
        [v1_1; v1_2; v1_3; v1_4; v1_5; v1_6; v1_7; v1_8; v1_9; v1_10] ∧ WORD x_10_x1_1_ v1_1 ∧
      WORD x_9_x1_2_ v1_2 ∧ WORD x_8_x1_3_ v1_3 ∧ WORD x_7_x1_4_ v1_4 ∧ WORD x_6_x1_5_ v1_5 ∧
      WORD x_5_x1_6_ v1_6 ∧ WORD x_4_x1_7_ v1_7 ∧ WORD x_3_x1_8_ v1_8 ∧ WORD x_2_x1_9_ v1_9 ∧
      BOOL x_1_x1_10_ v1_10
```

#### `forge_guardrailProg.dest_allowed_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> BOOL) dest_allowed dest_allowed_v
```

#### `forge_guardrailProg.gr_init_refs_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀po. gr_init_refs po = []
```

#### `forge_guardrailProg.gr_init_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ FORGE_GUARDRAILSPEC_GR_STATE_TYPE gr_init gr_init_v
```

#### `forge_guardrailProg.gr_resp_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (WORD --> WORD --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_FRAME64SPEC_FRAME64_TYPE) gr_resp
    gr_resp_v
```

#### `forge_guardrailProg.gr_step_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_FRAME64SPEC_FRAME64_TYPE -->
   PAIR_TYPE FORGE_GUARDRAILSPEC_GR_STATE_TYPE FORGE_FRAME64SPEC_FRAME64_TYPE) gr_step gr_step_v
```

#### `forge_guardrailProg.guardrail_main_spec`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀inps wlim uv.
    UNIT_TYPE () uv ⇒
    app p guardrail_main_v [uv]
      (FRAME64_IO_EV <|inputs := inps; outputs := []; write_limit := wlim|> [])
      (POSTv rv.
         &UNIT_TYPE () rv *
         SEP_EXISTS rest_inps wlim' evs'.
           &stop_after_err64 evs' *
           FRAME64_IO_EV
             <|inputs := rest_inps;
               outputs := limit_frames64 wlim (SND (frame64_run gr_step gr_init inps));
               write_limit := wlim'|> evs')
```

#### `forge_guardrailProg.guardrail_prog_eq_snoc`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ guardrail_prog = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_guardrailProg.guardrail_semantics`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀io.
    io.outputs = [] ⇒
    sem_satisfies (semantics_dec_list (init_state (frame64_ffi io)) init_env guardrail_prog)
      (λb.
         ∃io_events.
           b = Terminate Success io_events ∧ stop_after_err64 io_events ∧
           sent_frames64_of io_events =
           limit_frames64 io.write_limit (SND (frame64_run gr_step gr_init io.inputs)))
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_0_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_0.c = nsLookup_Mod1 forge_guardrailProg_env.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_0.v = nsLookup_Mod1 forge_guardrailProg_env.v ∧
  nsLookup_Short forge_guardrailProg_env_0.c = nsLookup_Short forge_guardrailProg_env.c ∧
  nsLookup_Short forge_guardrailProg_env_0.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefdeposits»,recordtypegr_stateseldefdeposits_v)])
    (nsLookup_Short forge_guardrailProg_env.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_10_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_10.c = nsLookup_Mod1 forge_guardrailProg_env_9.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_10.v = nsLookup_Mod1 forge_guardrailProg_env_9.v ∧
  nsLookup_Short forge_guardrailProg_env_10.c = nsLookup_Short forge_guardrailProg_env_9.c ∧
  nsLookup_Short forge_guardrailProg_env_10.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefdeposits_fupd»,recordtypegr_stateseldefdeposits_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_9.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_11_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_11.c = nsLookup_Mod1 forge_guardrailProg_env_10.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_11.v = nsLookup_Mod1 forge_guardrailProg_env_10.v ∧
  nsLookup_Short forge_guardrailProg_env_11.c = nsLookup_Short forge_guardrailProg_env_10.c ∧
  nsLookup_Short forge_guardrailProg_env_11.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefbalance_fupd»,recordtypegr_stateseldefbalance_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_10.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_12_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_12.c = nsLookup_Mod1 forge_guardrailProg_env_11.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_12.v = nsLookup_Mod1 forge_guardrailProg_env_11.v ∧
  nsLookup_Short forge_guardrailProg_env_12.c = nsLookup_Short forge_guardrailProg_env_11.c ∧
  nsLookup_Short forge_guardrailProg_env_12.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefspent_fupd»,recordtypegr_stateseldefspent_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_11.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_13_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_13.c = nsLookup_Mod1 forge_guardrailProg_env_12.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_13.v = nsLookup_Mod1 forge_guardrailProg_env_12.v ∧
  nsLookup_Short forge_guardrailProg_env_13.c = nsLookup_Short forge_guardrailProg_env_12.c ∧
  nsLookup_Short forge_guardrailProg_env_13.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefrefunds_fupd»,recordtypegr_stateseldefrefunds_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_12.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_14_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_14.c = nsLookup_Mod1 forge_guardrailProg_env_13.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_14.v = nsLookup_Mod1 forge_guardrailProg_env_13.v ∧
  nsLookup_Short forge_guardrailProg_env_14.c = nsLookup_Short forge_guardrailProg_env_13.c ∧
  nsLookup_Short forge_guardrailProg_env_14.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefcap_fupd»,recordtypegr_stateseldefcap_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_13.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_15_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_15.c = nsLookup_Mod1 forge_guardrailProg_env_14.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_15.v = nsLookup_Mod1 forge_guardrailProg_env_14.v ∧
  nsLookup_Short forge_guardrailProg_env_15.c = nsLookup_Short forge_guardrailProg_env_14.c ∧
  nsLookup_Short forge_guardrailProg_env_15.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefallowmask_fupd»,recordtypegr_stateseldefallowmask_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_14.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_16_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_16.c = nsLookup_Mod1 forge_guardrailProg_env_15.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_16.v = nsLookup_Mod1 forge_guardrailProg_env_15.v ∧
  nsLookup_Short forge_guardrailProg_env_16.c = nsLookup_Short forge_guardrailProg_env_15.c ∧
  nsLookup_Short forge_guardrailProg_env_16.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefnonce_fupd»,recordtypegr_stateseldefnonce_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_15.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_17_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_17.c = nsLookup_Mod1 forge_guardrailProg_env_16.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_17.v = nsLookup_Mod1 forge_guardrailProg_env_16.v ∧
  nsLookup_Short forge_guardrailProg_env_17.c = nsLookup_Short forge_guardrailProg_env_16.c ∧
  nsLookup_Short forge_guardrailProg_env_17.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldeflast_tx_fupd»,recordtypegr_stateseldeflast_tx_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_16.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_18_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_18.c = nsLookup_Mod1 forge_guardrailProg_env_17.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_18.v = nsLookup_Mod1 forge_guardrailProg_env_17.v ∧
  nsLookup_Short forge_guardrailProg_env_18.c = nsLookup_Short forge_guardrailProg_env_17.c ∧
  nsLookup_Short forge_guardrailProg_env_18.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldeflast_amt_fupd»,recordtypegr_stateseldeflast_amt_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_17.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_19_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_19.c = nsLookup_Mod1 forge_guardrailProg_env_18.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_19.v = nsLookup_Mod1 forge_guardrailProg_env_18.v ∧
  nsLookup_Short forge_guardrailProg_env_19.c = nsLookup_Short forge_guardrailProg_env_18.c ∧
  nsLookup_Short forge_guardrailProg_env_19.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldeftx_open_fupd»,recordtypegr_stateseldeftx_open_fupd_v)])
    (nsLookup_Short forge_guardrailProg_env_18.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_1_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_1.c = nsLookup_Mod1 forge_guardrailProg_env_0.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_1.v = nsLookup_Mod1 forge_guardrailProg_env_0.v ∧
  nsLookup_Short forge_guardrailProg_env_1.c = nsLookup_Short forge_guardrailProg_env_0.c ∧
  nsLookup_Short forge_guardrailProg_env_1.v =
  option_choice_f (ALOOKUP [(«recordtypegr_stateseldefbalance»,recordtypegr_stateseldefbalance_v)])
    (nsLookup_Short forge_guardrailProg_env_0.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_20_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_20.c = nsLookup_Mod1 forge_guardrailProg_env_19.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_20.v = nsLookup_Mod1 forge_guardrailProg_env_19.v ∧
  nsLookup_Short forge_guardrailProg_env_20.c = nsLookup_Short forge_guardrailProg_env_19.c ∧
  nsLookup_Short forge_guardrailProg_env_20.v =
  option_choice_f (ALOOKUP [(«gr_init»,gr_init_v)]) (nsLookup_Short forge_guardrailProg_env_19.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_21_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_21.c = nsLookup_Mod1 forge_guardrailProg_env_20.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_21.v = nsLookup_Mod1 forge_guardrailProg_env_20.v ∧
  nsLookup_Short forge_guardrailProg_env_21.c = nsLookup_Short forge_guardrailProg_env_20.c ∧
  nsLookup_Short forge_guardrailProg_env_21.v =
  option_choice_f (ALOOKUP [(«dest_allowed»,dest_allowed_v)])
    (nsLookup_Short forge_guardrailProg_env_20.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_22_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_22.c = nsLookup_Mod1 forge_guardrailProg_env_21.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_22.v = nsLookup_Mod1 forge_guardrailProg_env_21.v ∧
  nsLookup_Short forge_guardrailProg_env_22.c = nsLookup_Short forge_guardrailProg_env_21.c ∧
  nsLookup_Short forge_guardrailProg_env_22.v =
  option_choice_f (ALOOKUP [(«gr_resp»,gr_resp_v)]) (nsLookup_Short forge_guardrailProg_env_21.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_23_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_23.c = nsLookup_Mod1 forge_guardrailProg_env_22.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_23.v = nsLookup_Mod1 forge_guardrailProg_env_22.v ∧
  nsLookup_Short forge_guardrailProg_env_23.c = nsLookup_Short forge_guardrailProg_env_22.c ∧
  nsLookup_Short forge_guardrailProg_env_23.v =
  option_choice_f (ALOOKUP [(«gr_step»,gr_step_v)]) (nsLookup_Short forge_guardrailProg_env_22.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_24_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_24.c = nsLookup_Mod1 forge_guardrailProg_env_23.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_24.v = nsLookup_Mod1 forge_guardrailProg_env_23.v ∧
  nsLookup_Short forge_guardrailProg_env_24.c = nsLookup_Short forge_guardrailProg_env_23.c ∧
  nsLookup_Short forge_guardrailProg_env_24.v =
  option_choice_f (ALOOKUP [(«guardrail_main»,guardrail_main_v)])
    (nsLookup_Short forge_guardrailProg_env_23.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_2_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_2.c = nsLookup_Mod1 forge_guardrailProg_env_1.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_2.v = nsLookup_Mod1 forge_guardrailProg_env_1.v ∧
  nsLookup_Short forge_guardrailProg_env_2.c = nsLookup_Short forge_guardrailProg_env_1.c ∧
  nsLookup_Short forge_guardrailProg_env_2.v =
  option_choice_f (ALOOKUP [(«recordtypegr_stateseldefspent»,recordtypegr_stateseldefspent_v)])
    (nsLookup_Short forge_guardrailProg_env_1.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_3_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_3.c = nsLookup_Mod1 forge_guardrailProg_env_2.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_3.v = nsLookup_Mod1 forge_guardrailProg_env_2.v ∧
  nsLookup_Short forge_guardrailProg_env_3.c = nsLookup_Short forge_guardrailProg_env_2.c ∧
  nsLookup_Short forge_guardrailProg_env_3.v =
  option_choice_f (ALOOKUP [(«recordtypegr_stateseldefrefunds»,recordtypegr_stateseldefrefunds_v)])
    (nsLookup_Short forge_guardrailProg_env_2.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_4_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_4.c = nsLookup_Mod1 forge_guardrailProg_env_3.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_4.v = nsLookup_Mod1 forge_guardrailProg_env_3.v ∧
  nsLookup_Short forge_guardrailProg_env_4.c = nsLookup_Short forge_guardrailProg_env_3.c ∧
  nsLookup_Short forge_guardrailProg_env_4.v =
  option_choice_f (ALOOKUP [(«recordtypegr_stateseldefcap»,recordtypegr_stateseldefcap_v)])
    (nsLookup_Short forge_guardrailProg_env_3.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_5_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_5.c = nsLookup_Mod1 forge_guardrailProg_env_4.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_5.v = nsLookup_Mod1 forge_guardrailProg_env_4.v ∧
  nsLookup_Short forge_guardrailProg_env_5.c = nsLookup_Short forge_guardrailProg_env_4.c ∧
  nsLookup_Short forge_guardrailProg_env_5.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldefallowmask»,recordtypegr_stateseldefallowmask_v)])
    (nsLookup_Short forge_guardrailProg_env_4.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_6_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_6.c = nsLookup_Mod1 forge_guardrailProg_env_5.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_6.v = nsLookup_Mod1 forge_guardrailProg_env_5.v ∧
  nsLookup_Short forge_guardrailProg_env_6.c = nsLookup_Short forge_guardrailProg_env_5.c ∧
  nsLookup_Short forge_guardrailProg_env_6.v =
  option_choice_f (ALOOKUP [(«recordtypegr_stateseldefnonce»,recordtypegr_stateseldefnonce_v)])
    (nsLookup_Short forge_guardrailProg_env_5.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_7_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_7.c = nsLookup_Mod1 forge_guardrailProg_env_6.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_7.v = nsLookup_Mod1 forge_guardrailProg_env_6.v ∧
  nsLookup_Short forge_guardrailProg_env_7.c = nsLookup_Short forge_guardrailProg_env_6.c ∧
  nsLookup_Short forge_guardrailProg_env_7.v =
  option_choice_f (ALOOKUP [(«recordtypegr_stateseldeflast_tx»,recordtypegr_stateseldeflast_tx_v)])
    (nsLookup_Short forge_guardrailProg_env_6.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_8_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_8.c = nsLookup_Mod1 forge_guardrailProg_env_7.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_8.v = nsLookup_Mod1 forge_guardrailProg_env_7.v ∧
  nsLookup_Short forge_guardrailProg_env_8.c = nsLookup_Short forge_guardrailProg_env_7.c ∧
  nsLookup_Short forge_guardrailProg_env_8.v =
  option_choice_f
    (ALOOKUP [(«recordtypegr_stateseldeflast_amt»,recordtypegr_stateseldeflast_amt_v)])
    (nsLookup_Short forge_guardrailProg_env_7.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_9_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env_9.c = nsLookup_Mod1 forge_guardrailProg_env_8.c ∧
  nsLookup_Mod1 forge_guardrailProg_env_9.v = nsLookup_Mod1 forge_guardrailProg_env_8.v ∧
  nsLookup_Short forge_guardrailProg_env_9.c = nsLookup_Short forge_guardrailProg_env_8.c ∧
  nsLookup_Short forge_guardrailProg_env_9.v =
  option_choice_f (ALOOKUP [(«recordtypegr_stateseldeftx_open»,recordtypegr_stateseldeftx_open_v)])
    (nsLookup_Short forge_guardrailProg_env_8.v)
```

#### `forge_guardrailProg.nsLookup_forge_guardrailProg_env_pfun_eqs`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ nsLookup_Mod1 forge_guardrailProg_env.c = nsLookup_Mod1 forge_frameRunner_env_7.c ∧
  nsLookup_Mod1 forge_guardrailProg_env.v = nsLookup_Mod1 forge_frameRunner_env_7.v ∧
  nsLookup_Short forge_guardrailProg_env.c =
  option_choice_f (ALOOKUP [(«Recordtypegr_state»,10,TypeStamp «Recordtypegr_state» 10)])
    (nsLookup_Short forge_frameRunner_env_7.c) ∧
  nsLookup_Short forge_guardrailProg_env.v = nsLookup_Short forge_frameRunner_env_7.v
```

#### `forge_guardrailProg.recordtypegr_stateseldefallowmask_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    allowmask_fupd recordtypegr_stateseldefallowmask_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefallowmask_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_allowmask
    recordtypegr_stateseldefallowmask_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefbalance_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    balance_fupd recordtypegr_stateseldefbalance_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefbalance_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_balance recordtypegr_stateseldefbalance_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefcap_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    cap_fupd recordtypegr_stateseldefcap_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefcap_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_cap recordtypegr_stateseldefcap_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefdeposits_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    deposits_fupd recordtypegr_stateseldefdeposits_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefdeposits_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_deposits recordtypegr_stateseldefdeposits_v
```

#### `forge_guardrailProg.recordtypegr_stateseldeflast_amt_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    last_amt_fupd recordtypegr_stateseldeflast_amt_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldeflast_amt_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_last_amt recordtypegr_stateseldeflast_amt_v
```

#### `forge_guardrailProg.recordtypegr_stateseldeflast_tx_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    last_tx_fupd recordtypegr_stateseldeflast_tx_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldeflast_tx_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_last_tx recordtypegr_stateseldeflast_tx_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefnonce_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    nonce_fupd recordtypegr_stateseldefnonce_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefnonce_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_nonce recordtypegr_stateseldefnonce_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefrefunds_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    refunds_fupd recordtypegr_stateseldefrefunds_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefrefunds_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_refunds recordtypegr_stateseldefrefunds_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefspent_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((WORD --> WORD) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    spent_fupd recordtypegr_stateseldefspent_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldefspent_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> WORD) gr_state_spent recordtypegr_stateseldefspent_v
```

#### `forge_guardrailProg.recordtypegr_stateseldeftx_open_fupd_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ((BOOL --> BOOL) --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> FORGE_GUARDRAILSPEC_GR_STATE_TYPE)
    tx_open_fupd recordtypegr_stateseldeftx_open_fupd_v
```

#### `forge_guardrailProg.recordtypegr_stateseldeftx_open_v_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ (FORGE_GUARDRAILSPEC_GR_STATE_TYPE --> BOOL) gr_state_tx_open recordtypegr_stateseldeftx_open_v
```

#### `forge_guardrailProg.stop_after_err64_prefix_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀es1 es2. es1 ≼ es2 ∧ stop_after_err64 es2 ∧ (∃e. MEM e es1 ∧ event_is_err64 e) ⇒ es2 = es1
```

</details>

<details>
<summary><strong><code>forge_guardrailCompile</code></strong> — Verified Compilation (6 definitions, 4 theorems)</summary>

In-logic ARM64 backend compilation theorem linking guardrail_prog to exact machine-code bytes and bitmaps.

### Definitions

#### `forge_guardrailCompile.code_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ code = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_guardrailCompile.compiled`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ compile arm8_config (set_oracle arm8_backend_config oracle) guardrail_prog = SOME (code,data,info) ∧
  ffis = ffinames_to_string_list (the [] info.lab_conf.ffi_names) ∧ syms = info.symbols ∧
  LENGTH code = 101240 ∧ LENGTH data = 873 ∧ info.lab_conf.shmem_extra = [] ∧
  prog_syntax_ok guardrail_prog ∧ conf = encode_backend_config info
```

#### `forge_guardrailCompile.conf_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ conf = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_guardrailCompile.data_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ data = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_guardrailCompile.ffis_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ffis =
  to_list to_mlstring_mlstring
    (cv$Pair
       (cv$Pair (cv$Num 0)
          (cv$Pair (cv$Num 115)
             (cv$Pair (cv$Num 101)
                (cv$Pair (cv$Num 110)
                   (cv$Pair (cv$Num 100) (cv$Pair (cv$Num 54) (cv$Pair (cv$Num 52) (cv$Num 0))))))))
       (cv$Pair
          (cv$Pair (cv$Num 0)
             (cv$Pair (cv$Num 114)
                (cv$Pair (cv$Num 101)
                   (cv$Pair (cv$Num 99)
                      (cv$Pair (cv$Num 118) (cv$Pair (cv$Num 54) (cv$Pair (cv$Num 52) (cv$Num 0))))))))
          (cv$Num 0)))
```

#### `forge_guardrailCompile.guardrail_prog_cv_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀x. guardrail_prog_cv x = from_list from_ast_ast_dec guardrail_prog
```

### Theorems

#### `forge_guardrailCompile.guardrail_compiled`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ compile arm8_config (set_oracle arm8_backend_config oracle) guardrail_prog = SOME (code,data,info) ∧
  ffis = ffinames_to_string_list (the [] info.lab_conf.ffi_names) ∧ syms = info.symbols ∧
  LENGTH code = 101240 ∧ LENGTH data = 873 ∧ info.lab_conf.shmem_extra = [] ∧
  prog_syntax_ok guardrail_prog ∧ conf = encode_backend_config info
```

#### `forge_guardrailCompile.guardrail_prog_cv_eq`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ guardrail_prog_cv x = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>
```

#### `forge_guardrailCompile.guardrail_prog_cv_thm`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ from_list from_ast_ast_dec guardrail_prog = guardrail_prog_cv (cv$Num 0)
```

#### `forge_guardrailCompile.temp_oracle_cv_thm`
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
<summary><strong><code>forge_frame64Compose</code></strong> — Generic 64B E2E Compose (2 definitions, 1 theorems)</summary>

Polymorphic whole-binary ARM64 composition theorem lifting any 64-byte ml_translator kernel from _start to exit_group(94).

### Definitions

#### `forge_frame64Compose.mk_prefix64_P_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀posts k idx bs s s'. mk_prefix64_P posts k idx bs s s' ⇔ k < LENGTH posts ∧ s' = posts❲k❳
```

#### `forge_frame64Compose.noerr_ffi64_P_def`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀cb_end bm_end tail_bs k idx new_bs s s'.
    noerr_ffi64_P cb_end bm_end tail_bs k idx new_bs s s' ⇔
    idx = 0 ∧
    (∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) =
       SOME bytes2 ∧
       (w2n (s.REG 3w) < 65 ⇒
        ∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
       (65 ≤ w2n (s.REG 3w) ⇒
        ∀inp out.
          (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s)
            (inp,out ++ TAKE 64 (DROP 1 bytes2),s'))) ∨
    idx = 1 ∧
    ∃bytes2.
      read_bytearray (s.REG 2w) (w2n (s.REG 3w))
        (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (s.MEM a) else NONE) =
      SOME bytes2 ∧
      (w2n (s.REG 3w) < 65 ⇒
       ∀inp out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,out,s) (inp,out,s')) ∧
      (65 ≤ w2n (s.REG 3w) ∧ HD new_bs = 0w ⇒
       ∀rest out.
         (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳
           (TAKE 64 (DROP 1 new_bs) ++ rest,out,s) (rest,out,s')) ∧
      (65 ≤ w2n (s.REG 3w) ∧ HD new_bs ≠ 0w ⇒
       ∀out. (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (tail_bs,out,s) ([],out,s'))
```

### Theorems

#### `forge_frame64Compose.forge_frame64_kernel_compose`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀stepf init prog code data info oracle.
    compile arm8_config (set_oracle arm8_backend_config oracle) prog = SOME (code,data,info) ∧
    prog_syntax_ok prog ∧ info.lab_conf.shmem_extra = [] ∧
    ffinames_to_string_list (the [] info.lab_conf.ffi_names) = [«send64»; «recv64»] ∧
    0 < LENGTH code ∧ LENGTH code ≤ FORGE_MAX_CODE_BYTES ∧ LENGTH data ≤ FORGE_MAX_BITMAP_WORDS ∧
    (∀io.
       io.outputs = [] ⇒
       sem_satisfies (semantics_dec_list (init_state (frame64_ffi io)) init_env prog)
         (λb.
            ∃io_events.
              b = Terminate Success io_events ∧ stop_after_err64 io_events ∧
              sent_frames64_of io_events =
              limit_frames64 io.write_limit (SND (frame64_run stepf init io.inputs)))) ⇒
    (∀ms0.
       forge_slot_loaded forge_shim64_words code data ms0 ⇒
       (let
          ms1 = FUNPOW Next 43 ms0;
          cb_end = slot_cb_end (LENGTH code);
          bm_end = slot_bm_buf_end (LENGTH data);
          cbsp = slot_cbspace (LENGTH code)
        in
          (∀io ffi_if inst_if.
             io.outputs = [] ∧
             real_interfer_ok_slot cb_end bm_end cbsp [ExtCall «send64»; ExtCall «recv64»]
               (bits_of ms0) ffi_if inst_if ⇒
             (let
                rmc =
                  real_mc (bits_of ms0)
                    (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] ffi_if inst_if)
              in
                rmc.target = arm8_target_real (bits_of ms0) ∧
                ¬machine_sem rmc (frame64_ffi io) ms1 Fail)) ∧
          (∀inp. ∃inp_f out_f ms_f exit_code.
             (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,[],ms0) (inp_f,out_f,ms_f) ∧
             svc_exit_group_rel exit_code ms_f) ∧
          (∀inp inp_f out_f ms_f exit_code.
             (whole_step svc_read_rel svc_write_rel)꙳ (inp,[],ms0) (inp_f,out_f,ms_f) ∧
             svc_exit_group_rel exit_code ms_f ⇒
             (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
             out_f ≼ FLAT (SND (frame64_run stepf init (chunks64 inp)))) ∧
          ∀inp inp_f out_f ms_f exit_code.
            (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,[],ms0) (inp_f,out_f,ms_f) ∧
            svc_exit_group_rel exit_code ms_f ∧ exit_code = 0w ⇒
            out_f = FLAT (SND (frame64_run stepf init (chunks64 inp))))) ∧
    ∃ms0.
      forge_slot_loaded forge_shim64_words code data ms0 ∧ ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
      ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
```

</details>

<details>
<summary><strong><code>forge_m2Kernel</code></strong> — Unified End-to-End (M2) (0 definitions, 2 theorems)</summary>

Whole-binary ARM64 guardrail execution theorem from _start (0x450000) to svc #0 exit_group(94) and non-vacuity witness.

### Theorems

#### `forge_m2Kernel.forge_m2_kernel_correct`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∀ms0.
    forge_slot_loaded forge_shim64_words code data ms0 ⇒
    (let
       ms1 = FUNPOW Next 43 ms0;
       cb_end = slot_cb_end (LENGTH code);
       bm_end = slot_bm_buf_end (LENGTH data);
       cbsp = slot_cbspace (LENGTH code)
     in
       (∀io ffi_if inst_if.
          io.outputs = [] ∧
          real_interfer_ok_slot cb_end bm_end cbsp [ExtCall «send64»; ExtCall «recv64»]
            (bits_of ms0) ffi_if inst_if ⇒
          (let
             rmc =
               real_mc (bits_of ms0)
                 (forge_mc_slot cb_end bm_end [ExtCall «send64»; ExtCall «recv64»] ffi_if inst_if)
           in
             rmc.target = arm8_target_real (bits_of ms0) ∧
             ¬machine_sem rmc (frame64_ffi io) ms1 Fail)) ∧
       (∀inp. ∃inp_f out_f ms_f exit_code.
          (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,[],ms0) (inp_f,out_f,ms_f) ∧
          svc_exit_group_rel exit_code ms_f) ∧
       (∀inp inp_f out_f ms_f exit_code.
          (whole_step svc_read_rel svc_write_rel)꙳ (inp,[],ms0) (inp_f,out_f,ms_f) ∧
          svc_exit_group_rel exit_code ms_f ⇒
          (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
          out_f ≼ FLAT (SND (frame64_run gr_step gr_init (chunks64 inp)))) ∧
       ∀inp inp_f out_f ms_f exit_code.
         (whole_step svc_read_noerr_rel svc_write_noerr_rel)꙳ (inp,[],ms0) (inp_f,out_f,ms_f) ∧
         svc_exit_group_rel exit_code ms_f ∧ exit_code = 0w ⇒
         out_f = FLAT (SND (frame64_run gr_step gr_init (chunks64 inp))))
```

#### `forge_m2Kernel.forge_m2_nonvacuous`
- Kernel tags: `HYP_COUNT=0`, `ORACLES=[DISK_THM]`, `DIRECT_AXIOMS=[]`

```text
⊢ ∃ms0.
    forge_slot_loaded forge_shim64_words code data ms0 ∧ ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
```

</details>

