(*
  Forge Milestone 1: Trusted Hardware, ELF Layout & Linux AArch64 Syscall Contract
  (SHA-256 Pinned by Gate).

  Contains ONLY the trusted boundary definitions referenced by the top-level
  correctness and non-vacuity theorems (zero proof tactics):
    1. Exact linked ELF virtual addresses, code buffer size, and linked veneer/shim words
    2. Memory region definitions & ELF initial-state predicate (forge_elf_loaded)
    3. Real ARMv8 EL0 processor-bit target & machine configuration (arm8_target_real, real_mc)
    4. Explicit Linux AArch64 svc #0 syscall contracts (read=63, write=64, exit_group=94)
       and whole-binary transition relation (whole_step / shim_step)
*)
Theory forge_contractSpec
Ancestors
  words arithmetic list pred_set alignment relation
  arm8 arm8_step arm8_target targetSem misc forge_counterSpec
Libs
  preamble

(* ---- 1. Exact Linked ELF Virtual Addresses & Machine-Code Words ---- *)

Definition FORGE_VENEERS_BASE_def:
  FORGE_VENEERS_BASE : word64 = 0x00400000w
End
Definition FORGE_FFIRECV16_VENEER_def:
  FORGE_FFIRECV16_VENEER : word64 = 0x00400070w
End
Definition FORGE_FFISEND16_VENEER_def:
  FORGE_FFISEND16_VENEER : word64 = 0x00400080w
End
Definition FORGE_INSTALL_VENEER_def:
  FORGE_INSTALL_VENEER : word64 = 0x00400090w
End
Definition FORGE_EXIT_VENEER_def:
  FORGE_EXIT_VENEER : word64 = 0x004000A0w
End
Definition FORGE_CAKE_MAIN_def:
  FORGE_CAKE_MAIN : word64 = 0x004000B0w
End
Definition FORGE_CB_BEGIN_def:
  FORGE_CB_BEGIN : word64 = 0x0041234Cw
End
Definition FORGE_CB_END_def:
  FORGE_CB_END : word64 = 0x00420000w
End
Definition FORGE_CBSPACE_def:
  FORGE_CBSPACE : num = 56500
End
Definition FORGE_SHIM_BASE_def:
  FORGE_SHIM_BASE : word64 = 0x00421000w
End
Definition FORGE_FFIRECV16_def:
  FORGE_FFIRECV16 : word64 = 0x00421040w
End
Definition FORGE_FFISEND16_def:
  FORGE_FFISEND16 : word64 = 0x004210C0w
End
Definition FORGE_CML_EXIT_def:
  FORGE_CML_EXIT : word64 = 0x0042111Cw
End
Definition FORGE_CML_INSTALL_def:
  FORGE_CML_INSTALL : word64 = 0x00421130w
End
Definition FORGE_SHIM_END_def:
  FORGE_SHIM_END : word64 = 0x00421140w
End
Definition FORGE_CML_HEAP_def:
  FORGE_CML_HEAP : word64 = 0x00430000w
End
Definition FORGE_CML_STACK_def:
  FORGE_CML_STACK : word64 = 0x00430008w
End
Definition FORGE_CML_STACKEND_def:
  FORGE_CML_STACKEND : word64 = 0x00430010w
End
Definition FORGE_CAKE_BITMAPS_def:
  FORGE_CAKE_BITMAPS : word64 = 0x00430018w
End
Definition FORGE_BM_BUF_END_def:
  FORGE_BM_BUF_END : word64 = 0x00430F38w
End
Definition FORGE_RX_TMP_def:
  FORGE_RX_TMP : word64 = 0x00440000w
End
Definition FORGE_HEAP_def:
  FORGE_HEAP : word64 = 0x00450000w
End
Definition FORGE_STACK_def:
  FORGE_STACK : word64 = 0x00470000w
End
Definition FORGE_STACKEND_def:
  FORGE_STACKEND : word64 = 0x00490000w
End

Definition forge_veneers_words_def:
  forge_veneers_words : word32 list = [
    0x90000000w; 0x9102C000w; 0x90000181w; 0x91000021w;
    0xF9400021w; 0x90000182w; 0x91006042w; 0xF9000022w;
    0x90000182w; 0x913CE042w; 0xF9000422w; 0x90000182w;
    0x913CE042w; 0xF9000822w; 0xD0000082w; 0x910D3042w;
    0xF9000C22w; 0x90000102w; 0x91000042w; 0xF9001022w;
    0x90000182w; 0x91002042w; 0xF9400042w; 0x90000183w;
    0x91004063w; 0xF9400063w; 0x14000012w; 0xD503201Fw;
    0x140083F4w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x14008410w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x14008428w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x1400841Fw; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw
  ]
End

Definition forge_shim_words_def:
  forge_shim_words : word32 list = [
    (* _start: 0x421000 .. 0x42103c (16 words) *)
    0xF0000160w; 0x91000000w; 0xF0000061w; 0x91000021w;
    0xF9000020w; 0xF0000260w; 0x91000000w; 0xF0000061w;
    0x91002021w; 0xF9000020w; 0xF0000360w; 0x91000000w;
    0xF0000061w; 0x91004021w; 0xF9000020w; 0x17FF7BF1w;
    (* ffirecv16: 0x421040 .. 0x4210bc (32 words) *)
    0xF100447Fw; 0x540003C3w; 0xAA0203E9w; 0xF00000EAw;
    0x9100014Aw; 0xD280020Bw; 0xB40001ABw; 0xD2800000w;
    0xAA0A03E1w; 0xAA0B03E2w; 0xD28007E8w; 0xD4000001w;
    0xB100101Fw; 0x54FFFF20w; 0xF100001Fw; 0x540001CDw;
    0x8B00014Aw; 0xCB00016Bw; 0x17FFFFF4w; 0xF00000ECw;
    0x9100018Cw; 0xD280000Bw; 0x386B698Aw; 0x9100056Bw;
    0x382B692Aw; 0xF100417Fw; 0x54FFFF83w; 0x3900013Fw;
    0xD65F03C0w; 0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* ffisend16: 0x4210c0 .. 0x421118 (23 words) *)
    0xF100447Fw; 0x540002A3w; 0xAA0203E9w; 0x9100044Aw;
    0xD280020Bw; 0xB40001ABw; 0xD2800020w; 0xAA0A03E1w;
    0xAA0B03E2w; 0xD2800808w; 0xD4000001w; 0xB100101Fw;
    0x54FFFF20w; 0xF100001Fw; 0x540000CDw; 0x8B00014Aw;
    0xCB00016Bw; 0x17FFFFF4w; 0x3900013Fw; 0xD65F03C0w;
    0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* cml_exit: 0x42111c .. 0x42112c (5 words) *)
    0xB4000040w; 0xD2800020w; 0xD2800BC8w; 0xD4000001w;
    0x14000000w;
    (* cml_install: 0x421130 .. 0x42113c (4 words) *)
    0xD2800040w; 0xD2800BC8w; 0xD4000001w; 0x14000000w
  ]
End

Definition words32_in_mem_def:
  (words32_in_mem (base:word64) [] (mem:word64 -> word8) ⇔ T) ∧
  (words32_in_mem base (w::ws) mem ⇔
    mem base        = (7 >< 0) w ∧
    mem (base + 1w) = (15 >< 8) w ∧
    mem (base + 2w) = (23 >< 16) w ∧
    mem (base + 3w) = (31 >< 24) w ∧
    words32_in_mem (base + 4w) ws mem)
End

Definition shim_loaded_def:
  shim_loaded (mem:word64 -> word8) ⇔
    words32_in_mem FORGE_VENEERS_BASE forge_veneers_words mem ∧
    words32_in_mem FORGE_SHIM_BASE forge_shim_words mem
End

(* ---- 2. Memory Regions ---- *)

Definition forge_code_region_def:
  forge_code_region : word64 set =
    { a | FORGE_CAKE_MAIN ≤₊ a ∧ a <₊ FORGE_CB_END }
End

Definition forge_bitmaps_region_def:
  forge_bitmaps_region : word64 set =
    { a | FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ FORGE_BM_BUF_END }
End

Definition forge_heap_stack_region_def:
  forge_heap_stack_region : word64 set =
    { a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_STACKEND }
End

Definition forge_prog_addresses_def:
  forge_prog_addresses : word64 set =
    forge_code_region ∪ forge_bitmaps_region ∪ forge_heap_stack_region
End

Definition forge_shim_code_region_def:
  forge_shim_code_region : word64 set =
    { a | FORGE_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_CAKE_MAIN } ∪
    { a | FORGE_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_SHIM_END }
End

Definition forge_rx_tmp_region_def:
  forge_rx_tmp_region : word64 set =
    { a | FORGE_RX_TMP ≤₊ a ∧ a <₊ FORGE_RX_TMP + 16w }
End

Definition forge_cml_ptrs_region_def:
  forge_cml_ptrs_region : word64 set =
    { a | FORGE_CML_HEAP ≤₊ a ∧ a <₊ FORGE_CAKE_BITMAPS }
End

Definition forge_heap_hdr_region_def:
  forge_heap_hdr_region : word64 set =
    { a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_HEAP + 40w }
End

(* ---- 3. Real ARMv8 EL0 Processor-Bit Target & Machine Configuration ---- *)

Definition erase_def:
  erase (s:arm8_state) =
    s with <| TCR_EL1   := s.TCR_EL1 with <| TBI0 := F; TBI1 := F |>;
              SCTLR_EL1 := s.SCTLR_EL1 with SA0 := F |>
End

Definition bits_of_def:
  bits_of (s:arm8_state) = (s.TCR_EL1.TBI0, s.TCR_EL1.TBI1, s.SCTLR_EL1.SA0)
End

Definition restore_def:
  restore (B:bool # bool # bool) (s:arm8_state) =
    s with <| TCR_EL1   := s.TCR_EL1 with <| TBI0 := FST B; TBI1 := FST (SND B) |>;
              SCTLR_EL1 := s.SCTLR_EL1 with SA0 := SND (SND B) |>
End

Definition untagged_def:
  untagged (a:word64) ⇔ ((63 >< 55) a = (0w:word9))
End

Definition sp_ok_def:
  sp_ok (s:arm8_state) ⇔
    s.PSTATE.EL = 0w ∧ (¬s.SCTLR_EL1.SA0 ∨ aligned 4 s.SP_EL0)
End

Definition lo55_def:
  lo55 (mc : (64, 'b, 'c) machine_config) ⇔
    ∀a. a ∈ mc.prog_addresses ∨ a = mc.halt_pc ∨ a = mc.install_pc ∨ MEM a mc.ffi_entry_pcs ⇒
        untagged a
End

Definition arm8_target_real_def:
  arm8_target_real (B : bool # bool # bool) =
    arm8_target with <|
      next := arm8$Next;
      state_ok := λms. arm8_ok (erase ms) ∧ bits_of ms = B ∧
                       (¬SND (SND B) ∨ aligned 4 ms.SP_EL0)
    |>
End

Definition real_mc_def:
  real_mc (B : bool # bool # bool) (mc : (64, arm8_state, 'c) machine_config) =
    mc with target := arm8_target_real B
End

Definition forge_mc_with_def:
  forge_mc_with ffi_if inst_if =
    <| prog_addresses    := forge_prog_addresses
     ; shared_addresses  := ∅
     ; ffi_entry_pcs     := [FORGE_FFISEND16_VENEER; FORGE_FFIRECV16_VENEER]
     ; ffi_names         := [ExtCall «send16»; ExtCall «recv16»]
     ; ptr_reg           := 0
     ; len_reg           := 1
     ; ptr2_reg          := 2
     ; len2_reg          := 3
     ; ffi_interfer      := ffi_if
     ; callee_saved_regs := [19;20;21;22;23;24;25;26;27;28]
     ; next_interfer     := K I
     ; halt_pc           := FORGE_EXIT_VENEER
     ; install_pc        := FORGE_INSTALL_VENEER
     ; install_interfer  := inst_if
     ; target            := arm8_target
     ; mmio_info         := []
     |>
End

Definition real_interfer_ok_def:
  real_interfer_ok B ffi_if inst_if ⇔
    let mc = forge_mc_with (λk (i, bs, s). erase (ffi_if k (i, bs, restore B s)))
                           (λk (bs, s). erase (inst_if k (bs, restore B s))) in
      ffi_interfer_ok FORGE_CAKE_MAIN mc ∧
      install_interfer_ok FORGE_CAKE_MAIN FORGE_CBSPACE mc ∧
      (∀k i bs s. bits_of s = B ⇒
                  bits_of (ffi_if k (i, bs, s)) = B ∧
                  (ffi_if k (i, bs, s)).SP_EL0 = s.SP_EL0) ∧
      (∀k bs s. bits_of s = B ⇒
                bits_of (inst_if k (bs, s)) = B ∧
                (inst_if k (bs, s)).SP_EL0 = s.SP_EL0)
End

(* ---- 4. Explicit Linux AArch64 svc #0 Syscall Contracts & Whole-Binary Step ---- *)

Definition svc_frame_rel_def:
  svc_frame_rel (s:arm8_state) (s':arm8_state) ⇔
    s'.PC = s.PC + 4w ∧
    s'.exception = NoException ∧
    s'.PSTATE.EL = s.PSTATE.EL ∧
    s'.SCTLR_EL1 = s.SCTLR_EL1 ∧
    s'.TCR_EL1 = s.TCR_EL1 ∧
    s'.SP_EL0 = s.SP_EL0 ∧
    (∀r. r ≠ 0w ⇒ s'.REG r = s.REG r)
End

(* Full Linux read(0) contract: EINTR, clean EOF, fatal read error, or 1..count partial/full read *)
Definition svc_read_rel_def:
  svc_read_rel (inp:word8 list) (s:arm8_state) (s':arm8_state) (rest:word8 list) ⇔
    s.REG 8w = 63w ∧
    s.REG 0w = 0w ∧
    svc_frame_rel s s' ∧
    ( (s'.REG 0w = -4w ∧ s'.MEM = s.MEM ∧ rest = inp) ∨
      (s'.REG 0w = 0w ∧ inp = [] ∧ s'.MEM = s.MEM ∧ rest = []) ∨
      (word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w ∧ s'.MEM = s.MEM ∧ rest = inp) ∨
      (∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ n ≤ LENGTH inp ∧
           s'.REG 0w = n2w n ∧
           s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n inp) s.MEM ∧
           rest = DROP n inp) )
End

(* Error-free Linux read(0) contract: arbitrary EINTR, arbitrary 1..count partial reads, clean/truncated EOF *)
Definition svc_read_noerr_rel_def:
  svc_read_noerr_rel (inp:word8 list) (s:arm8_state) (s':arm8_state) (rest:word8 list) ⇔
    s.REG 8w = 63w ∧
    s.REG 0w = 0w ∧
    svc_frame_rel s s' ∧
    ( (s'.REG 0w = -4w ∧ s'.MEM = s.MEM ∧ rest = inp) ∨
      (s'.REG 0w = 0w ∧ inp = [] ∧ s'.MEM = s.MEM ∧ rest = []) ∨
      (∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ n ≤ LENGTH inp ∧
           s'.REG 0w = n2w n ∧
           s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n inp) s.MEM ∧
           rest = DROP n inp) )
End

(* Full Linux write(1) contract: EINTR, 1..count partial/full write, or 0/fatal write error (EPIPE) *)
Definition svc_write_rel_def:
  svc_write_rel (s:arm8_state) (s':arm8_state) (out:word8 list) ⇔
    s.REG 8w = 64w ∧
    s.REG 0w = 1w ∧
    svc_frame_rel s s' ∧
    s'.MEM = s.MEM ∧
    ( (s'.REG 0w = -4w ∧ out = []) ∨
      (∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧
           s'.REG 0w = n2w n ∧
           out = GENLIST (λi. s.MEM (s.REG 1w + n2w i)) n) ∨
      ((s'.REG 0w = 0w ∨ (word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w)) ∧ out = []) )
End

(* Error-free Linux write(1) contract: arbitrary EINTR and arbitrary 1..count partial/full writes *)
Definition svc_write_noerr_rel_def:
  svc_write_noerr_rel (s:arm8_state) (s':arm8_state) (out:word8 list) ⇔
    s.REG 8w = 64w ∧
    s.REG 0w = 1w ∧
    svc_frame_rel s s' ∧
    s'.MEM = s.MEM ∧
    ( (s'.REG 0w = -4w ∧ out = []) ∨
      (∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧
           s'.REG 0w = n2w n ∧
           out = GENLIST (λi. s.MEM (s.REG 1w + n2w i)) n) )
End

Definition svc_exit_group_rel_def:
  svc_exit_group_rel (exit_code:word64) (s:arm8_state) ⇔
    s.REG 8w = 94w ∧
    s.REG 0w = exit_code ∧
    s.MEM s.PC = 0x01w ∧
    s.MEM (s.PC + 1w) = 0x00w ∧
    s.MEM (s.PC + 2w) = 0x00w ∧
    s.MEM (s.PC + 3w) = 0xD4w
End

Definition is_svc0_at_def:
  is_svc0_at (s:arm8_state) ⇔
    s.MEM s.PC = 0x01w ∧
    s.MEM (s.PC + 1w) = 0x00w ∧
    s.MEM (s.PC + 2w) = 0x00w ∧
    s.MEM (s.PC + 3w) = 0xD4w
End

Definition whole_step_def:
  whole_step rrel wrel
    (inp:word8 list, out:word8 list, s:arm8_state)
    (inp':word8 list, out':word8 list, s':arm8_state) ⇔
    (¬is_svc0_at s ∧ NextStateARM8 s = SOME s' ∧ inp' = inp ∧ out' = out) ∨
    (is_svc0_at s ∧ s.REG 8w = 63w ∧ rrel inp s s' inp' ∧ out' = out) ∨
    (is_svc0_at s ∧ s.REG 8w = 64w ∧ ∃chunk. wrel s s' chunk ∧ inp' = inp ∧ out' = out ++ chunk)
End

Definition shim_step_def:
  shim_step = whole_step svc_read_rel svc_write_rel
End

(* ---- 5. Initial ELF Memory & CPU State Predicate ---- *)

Definition forge_elf_loaded_def:
  forge_elf_loaded (bytes:word8 list) (bitmaps:num list) (ms0:arm8_state) ⇔
    arm8_ok (erase ms0) ∧
    sp_ok ms0 ∧
    ms0.PC = FORGE_SHIM_BASE ∧
    shim_loaded ms0.MEM ∧
    read_bytearray FORGE_CAKE_MAIN (LENGTH bytes)
      (λa. if a ∈ forge_prog_addresses then SOME (ms0.MEM a) else NONE) = SOME bytes ∧
    (∀i. i < LENGTH bitmaps ⇒
      mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) = n2w (EL i bitmaps))
End
