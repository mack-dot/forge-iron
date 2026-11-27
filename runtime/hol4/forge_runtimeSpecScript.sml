(*
  Forge Reusable Runtime: Trusted 256 KB Slot Hardware, ELF Layout & Linux AArch64
  Syscall Contract (SHA-256 Pinned by Gate).

  Contains ONLY trusted boundary definitions (zero proof tactics):
    1. Fixed 256 KB RX code slot [0x400000..0x440000) with fixed _start = 0x450000,
       fixed 64 KB bitmap slot [0x460018..0x470000), fixed rx_tmp/heap/stackend.
    2. Parameterized ARM64 veneer word generator (forge_slot_veneers) for ANY
       compiled CakeML code blob <= 261,968 B and bitmaps <= 8,189 u64 words.
    3. Exact 80-word raw Linux AArch64 syscall shims at _start = 0x450000 for both
       16-byte frames (forge_shim16_words) and 64-byte frames (forge_shim64_words).
    4. Real ARMv8 EL0 processor-bit erasure target & machine_config (erase, bits_of,
       restore, untagged, sp_ok, lo55, arm8_target_real, real_mc).
    5. Explicit Linux AArch64 svc #0 syscall contracts (read=63, write=64,
       exit_group=94) and whole-binary transition relation (whole_step / shim_step).
    6. Parameterized initial ELF loaded predicate (forge_slot_loaded).
*)
Theory forge_runtimeSpec
Ancestors
  words arithmetic list pred_set alignment relation
  arm8 arm8_step arm8_target targetSem ffi misc
Libs
  preamble

(* ---- 1. Fixed 256 KB Slot Virtual Addresses ---- *)

Definition FORGE_VENEERS_BASE_def:
  FORGE_VENEERS_BASE : word64 = 0x00400000w
End
Definition FORGE_FFIRECV_VENEER_def:
  FORGE_FFIRECV_VENEER : word64 = 0x00400070w
End
Definition FORGE_FFISEND_VENEER_def:
  FORGE_FFISEND_VENEER : word64 = 0x00400080w
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
Definition FORGE_SLOT_END_def:
  FORGE_SLOT_END : word64 = 0x00440000w
End
Definition FORGE_MAX_CODE_BYTES_def:
  FORGE_MAX_CODE_BYTES : num = 261968
End
Definition FORGE_SHIM_BASE_def:
  FORGE_SHIM_BASE : word64 = 0x00450000w
End
Definition FORGE_FFIRECV_def:
  FORGE_FFIRECV : word64 = 0x00450040w
End
Definition FORGE_FFISEND_def:
  FORGE_FFISEND : word64 = 0x004500C0w
End
Definition FORGE_CML_EXIT_def:
  FORGE_CML_EXIT : word64 = 0x0045011Cw
End
Definition FORGE_CML_INSTALL_def:
  FORGE_CML_INSTALL : word64 = 0x00450130w
End
Definition FORGE_SHIM_END_def:
  FORGE_SHIM_END : word64 = 0x00450140w
End
Definition FORGE_CML_HEAP_def:
  FORGE_CML_HEAP : word64 = 0x00460000w
End
Definition FORGE_CML_STACK_def:
  FORGE_CML_STACK : word64 = 0x00460008w
End
Definition FORGE_CML_STACKEND_def:
  FORGE_CML_STACKEND : word64 = 0x00460010w
End
Definition FORGE_CAKE_BITMAPS_def:
  FORGE_CAKE_BITMAPS : word64 = 0x00460018w
End
Definition FORGE_DATA_SLOT_END_def:
  FORGE_DATA_SLOT_END : word64 = 0x00470000w
End
Definition FORGE_MAX_BITMAP_WORDS_def:
  FORGE_MAX_BITMAP_WORDS : num = 8189
End
Definition FORGE_RX_TMP_def:
  FORGE_RX_TMP : word64 = 0x00470000w
End
Definition FORGE_HEAP_def:
  FORGE_HEAP : word64 = 0x00480000w
End
Definition FORGE_STACK_def:
  FORGE_STACK : word64 = 0x004C0000w
End
Definition FORGE_STACKEND_def:
  FORGE_STACKEND : word64 = 0x00500000w
End

Definition align_up_64k_def:
  align_up_64k (a:word64) : word64 = (a + 0xFFFFw) && 0xFFFFFFFFFFFF0000w
End

Definition slot_cb_begin_def:
  slot_cb_begin (code_len:num) : word64 = FORGE_CAKE_MAIN + n2w code_len
End

Definition slot_cb_end_def:
  slot_cb_end (code_len:num) : word64 = align_up_64k (slot_cb_begin code_len)
End

Definition slot_cbspace_def:
  slot_cbspace (code_len:num) : num = w2n (slot_cb_end code_len - slot_cb_begin code_len)
End

Definition slot_bm_buf_end_def:
  slot_bm_buf_end (data_len:num) : word64 = FORGE_CAKE_BITMAPS + n2w (8 * data_len)
End

Definition slot_layout_ok_def:
  slot_layout_ok (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64) ⇔
    FORGE_CAKE_MAIN <₊ cb_begin ∧ cb_begin ≤₊ cb_end ∧ cb_end ≤₊ FORGE_SLOT_END ∧
    FORGE_CAKE_BITMAPS ≤₊ bm_buf_end ∧ bm_buf_end ≤₊ FORGE_DATA_SLOT_END
End

(* ---- 2. Parameterized ARM64 Veneers & Fixed 80-Word Syscall Shims ---- *)

Definition arm8_enc_adrp_x2_def:
  arm8_enc_adrp_x2 (pc:word64) (tgt:word64) : word32 =
    let delta : word64 = ((tgt && 0xFFFFFFFFFFFFF000w) - (pc && 0xFFFFFFFFFFFFF000w)) ≫ 12 in
    let immlo : word32 = w2w ((1 >< 0) delta : 2 word) in
    let immhi : word32 = w2w ((20 >< 2) delta : 19 word) in
      0x90000002w ‖ (immlo ≪ 29) ‖ (immhi ≪ 5)
End

Definition arm8_enc_add_x2_def:
  arm8_enc_add_x2 (tgt:word64) : word32 =
    let imm12 : word32 = w2w ((11 >< 0) tgt : 12 word) in
      0x91000042w ‖ (imm12 ≪ 10)
End

Definition forge_slot_veneers_def:
  forge_slot_veneers (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64) : word32 list = [
    (* 0..7: x0 = cake_main (0x4000B0), x1 = [cml_heap (0x460000)], [x1] = cake_bitmaps (0x460018) *)
    0x90000000w; 0x9102C000w; 0x90000301w; 0x91000021w;
    0xF9400021w; 0x90000302w; 0x91006042w; 0xF9000022w;
    (* 8..10: [x1, #8] = cake_bitmaps_buffer_begin (bm_buf_end) *)
    arm8_enc_adrp_x2 0x00400020w bm_buf_end;
    arm8_enc_add_x2 bm_buf_end;
    0xF9000422w;
    (* 11..13: [x1, #16] = cake_bitmaps_buffer_end (bm_buf_end) *)
    arm8_enc_adrp_x2 0x0040002Cw bm_buf_end;
    arm8_enc_add_x2 bm_buf_end;
    0xF9000822w;
    (* 14..16: [x1, #24] = cake_codebuffer_begin (cb_begin) *)
    arm8_enc_adrp_x2 0x00400038w cb_begin;
    arm8_enc_add_x2 cb_begin;
    0xF9000C22w;
    (* 17..19: [x1, #32] = cake_codebuffer_end (cb_end) *)
    arm8_enc_adrp_x2 0x00400044w cb_end;
    arm8_enc_add_x2 cb_end;
    0xF9001022w;
    (* 20..27: x2 = [cml_stack (0x460008)], x3 = [cml_stackend (0x460010)], b cake_main, nop *)
    0x90000302w; 0x91002042w; 0xF9400042w; 0x90000303w;
    0x91004063w; 0xF9400063w; 0x14000012w; 0xD503201Fw;
    (* 28..43: b ffirecv (0x450040), b ffisend (0x4500C0), b cml_install (0x450130), b cml_exit (0x45011C) *)
    0x14013FF4w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x14014010w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x14014028w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x1401401Fw; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw
  ]
End

Definition forge_shim16_words_def:
  forge_shim16_words : word32 list = [
    (* _start: 0x450000 .. 0x45003C (16 words) *)
    0x90000180w; 0x91000000w; 0x90000081w; 0x91000021w;
    0xF9000020w; 0x90000380w; 0x91000000w; 0x90000081w;
    0x91002021w; 0xF9000020w; 0x90000580w; 0x91000000w;
    0x90000081w; 0x91004021w; 0xF9000020w; 0x17FEBFF1w;
    (* ffirecv16: 0x450040 .. 0x4500BC (32 words) *)
    0xF100447Fw; 0x540003C3w; 0xAA0203E9w; 0x9000010Aw;
    0x9100014Aw; 0xD280020Bw; 0xB40001ABw; 0xD2800000w;
    0xAA0A03E1w; 0xAA0B03E2w; 0xD28007E8w; 0xD4000001w;
    0xB100101Fw; 0x54FFFF20w; 0xF100001Fw; 0x540001CDw;
    0x8B00014Aw; 0xCB00016Bw; 0x17FFFFF4w; 0x9000010Cw;
    0x9100018Cw; 0xD280000Bw; 0x386B698Aw; 0x9100056Bw;
    0x382B692Aw; 0xF100417Fw; 0x54FFFF83w; 0x3900013Fw;
    0xD65F03C0w; 0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* ffisend16: 0x4500C0 .. 0x450118 (23 words) *)
    0xF100447Fw; 0x540002A3w; 0xAA0203E9w; 0x9100044Aw;
    0xD280020Bw; 0xB40001ABw; 0xD2800020w; 0xAA0A03E1w;
    0xAA0B03E2w; 0xD2800808w; 0xD4000001w; 0xB100101Fw;
    0x54FFFF20w; 0xF100001Fw; 0x540000CDw; 0x8B00014Aw;
    0xCB00016Bw; 0x17FFFFF4w; 0x3900013Fw; 0xD65F03C0w;
    0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* cml_exit: 0x45011C .. 0x45012C (5 words) *)
    0xB4000040w; 0xD2800020w; 0xD2800BC8w; 0xD4000001w;
    0x14000000w;
    (* cml_install: 0x450130 .. 0x45013C (4 words) *)
    0xD2800040w; 0xD2800BC8w; 0xD4000001w; 0x14000000w
  ]
End

Definition forge_shim64_words_def:
  forge_shim64_words : word32 list = [
    (* _start: 0x450000 .. 0x45003C (16 words) *)
    0x90000180w; 0x91000000w; 0x90000081w; 0x91000021w;
    0xF9000020w; 0x90000380w; 0x91000000w; 0x90000081w;
    0x91002021w; 0xF9000020w; 0x90000580w; 0x91000000w;
    0x90000081w; 0x91004021w; 0xF9000020w; 0x17FEBFF1w;
    (* ffirecv64: 0x450040 .. 0x4500BC (32 words; #65/#64) *)
    0xF101047Fw; 0x540003C3w; 0xAA0203E9w; 0x9000010Aw;
    0x9100014Aw; 0xD280080Bw; 0xB40001ABw; 0xD2800000w;
    0xAA0A03E1w; 0xAA0B03E2w; 0xD28007E8w; 0xD4000001w;
    0xB100101Fw; 0x54FFFF20w; 0xF100001Fw; 0x540001CDw;
    0x8B00014Aw; 0xCB00016Bw; 0x17FFFFF4w; 0x9000010Cw;
    0x9100018Cw; 0xD280000Bw; 0x386B698Aw; 0x9100056Bw;
    0x382B692Aw; 0xF101017Fw; 0x54FFFF83w; 0x3900013Fw;
    0xD65F03C0w; 0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* ffisend64: 0x4500C0 .. 0x450118 (23 words; #65/#64) *)
    0xF101047Fw; 0x540002A3w; 0xAA0203E9w; 0x9100044Aw;
    0xD280080Bw; 0xB40001ABw; 0xD2800020w; 0xAA0A03E1w;
    0xAA0B03E2w; 0xD2800808w; 0xD4000001w; 0xB100101Fw;
    0x54FFFF20w; 0xF100001Fw; 0x540000CDw; 0x8B00014Aw;
    0xCB00016Bw; 0x17FFFFF4w; 0x3900013Fw; 0xD65F03C0w;
    0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* cml_exit: 0x45011C .. 0x45012C (5 words) *)
    0xB4000040w; 0xD2800020w; 0xD2800BC8w; 0xD4000001w;
    0x14000000w;
    (* cml_install: 0x450130 .. 0x45013C (4 words) *)
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

Definition shim_loaded_slot_def:
  shim_loaded_slot (shim_ws:word32 list) (cb_begin:word64) (cb_end:word64)
                   (bm_buf_end:word64) (mem:word64 -> word8) ⇔
    words32_in_mem FORGE_VENEERS_BASE (forge_slot_veneers cb_begin cb_end bm_buf_end) mem ∧
    words32_in_mem FORGE_SHIM_BASE shim_ws mem
End

(* ---- 3. Parameterized Slot Memory Regions ---- *)

Definition forge_code_region_slot_def:
  forge_code_region_slot (cb_end:word64) : word64 set =
    { a | FORGE_CAKE_MAIN ≤₊ a ∧ a <₊ cb_end }
End

Definition forge_bitmaps_region_slot_def:
  forge_bitmaps_region_slot (bm_buf_end:word64) : word64 set =
    { a | FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ bm_buf_end }
End

Definition forge_heap_stack_region_def:
  forge_heap_stack_region : word64 set =
    { a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_STACKEND }
End

Definition forge_prog_addresses_slot_def:
  forge_prog_addresses_slot (cb_end:word64) (bm_buf_end:word64) : word64 set =
    forge_code_region_slot cb_end ∪
    forge_bitmaps_region_slot bm_buf_end ∪
    forge_heap_stack_region
End

Definition forge_shim_code_region_def:
  forge_shim_code_region : word64 set =
    { a | FORGE_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_CAKE_MAIN } ∪
    { a | FORGE_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_SHIM_END }
End

Definition forge_rx_tmp_region_def:
  forge_rx_tmp_region : word64 set =
    { a | FORGE_RX_TMP ≤₊ a ∧ a <₊ FORGE_RX_TMP + 64w }
End

Definition forge_cml_ptrs_region_def:
  forge_cml_ptrs_region : word64 set =
    { a | FORGE_CML_HEAP ≤₊ a ∧ a <₊ FORGE_CAKE_BITMAPS }
End

Definition forge_heap_hdr_region_def:
  forge_heap_hdr_region : word64 set =
    { a | FORGE_HEAP ≤₊ a ∧ a <₊ FORGE_HEAP + 40w }
End

(* ---- 4. Real ARMv8 EL0 Processor-Bit Target & Machine Configuration ---- *)

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

Definition forge_mc_slot_def:
  forge_mc_slot (cb_end:word64) (bm_buf_end:word64) ffi_names_l
                ffi_if inst_if =
    <| prog_addresses    := forge_prog_addresses_slot cb_end bm_buf_end
     ; shared_addresses  := ∅
     ; ffi_entry_pcs     := [FORGE_FFISEND_VENEER; FORGE_FFIRECV_VENEER]
     ; ffi_names         := ffi_names_l
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

Definition real_interfer_ok_slot_def:
  real_interfer_ok_slot (cb_end:word64) (bm_buf_end:word64) (cbspace:num)
                        ffi_names_l B ffi_if inst_if ⇔
    let mc = forge_mc_slot cb_end bm_buf_end ffi_names_l
               (λk (i, bs, s). erase (ffi_if k (i, bs, restore B s)))
               (λk (bs, s). erase (inst_if k (bs, restore B s))) in
      ffi_interfer_ok FORGE_CAKE_MAIN mc ∧
      install_interfer_ok FORGE_CAKE_MAIN cbspace mc ∧
      (∀k i bs s. bits_of s = B ⇒
                  bits_of (ffi_if k (i, bs, s)) = B ∧
                  (ffi_if k (i, bs, s)).SP_EL0 = s.SP_EL0) ∧
      (∀k bs s. bits_of s = B ⇒
                bits_of (inst_if k (bs, s)) = B ∧
                (inst_if k (bs, s)).SP_EL0 = s.SP_EL0)
End

(* ---- 5. Explicit Linux AArch64 svc #0 Syscall Contracts & Whole-Binary Step ---- *)

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

(* ---- 6. Parameterized Initial ELF Memory & CPU State Predicate ---- *)

Definition forge_slot_loaded_def:
  forge_slot_loaded (shim_ws:word32 list) (bytes:word8 list) (bitmaps:num list) (ms0:arm8_state) ⇔
    let cb_begin = slot_cb_begin (LENGTH bytes) in
    let cb_end = slot_cb_end (LENGTH bytes) in
    let bm_buf_end = slot_bm_buf_end (LENGTH bitmaps) in
      0 < LENGTH bytes ∧
      LENGTH bytes ≤ FORGE_MAX_CODE_BYTES ∧
      LENGTH bitmaps ≤ FORGE_MAX_BITMAP_WORDS ∧
      arm8_ok (erase ms0) ∧
      sp_ok ms0 ∧
      ms0.PC = FORGE_SHIM_BASE ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_buf_end ms0.MEM ∧
      read_bytearray FORGE_CAKE_MAIN (LENGTH bytes)
        (λa. if a ∈ forge_prog_addresses_slot cb_end bm_buf_end then SOME (ms0.MEM a) else NONE) = SOME bytes ∧
      (∀i. i < LENGTH bitmaps ⇒
        mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) = n2w (EL i bitmaps))
End
