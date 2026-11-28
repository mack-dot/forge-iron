(*
  Forge Milestone 3 Reusable Runtime: Trusted 256 KB Slot Hardware, ELF Layout &
  6-Syscall Linux AArch64 Dual-Slot Crypto-Airlock Contract (SHA-256 Pinned by Gate).

  Contains ONLY trusted boundary definitions (zero proof tactics):
    1. Fixed 256 KB RX code slot [0x400000..0x440000) with 52-word veneers
       (cml_main + 4 FFI veneers + install + exit), cake_main = 0x4000D0,
       fixed _start = 0x450000, and 544B forge_rx_tmp at 0x470000.
    2. Parameterized 52-word ARM64 veneer word generator (`forge_m3_slot_veneers`).
    3. Exact 168-word raw Linux AArch64 syscall shim (`forge_shim_airlock_words`)
       covering read(63) on fd 0 & fd 4, write(64) on fd 1, pread64(67) on fd 3,
       pwrite64(68) on fd 3, fdatasync(83) on fd 3, and exit_group(94).
    4. Explicit Linux AArch64 svc #0 syscall contracts + page-cache vs fdatasync-durable
       dual-slot OS state (`m3_os`) and whole-binary transition relation (`m3_whole_step`).
    5. Parameterized initial ELF loaded predicate (`forge_m3_slot_loaded`).
*)
Theory forge_airlockContract
Ancestors
  words arithmetic list pred_set alignment relation
  arm8 arm8_step arm8_target targetSem ffi misc
  forge_runtimeSpec forge_airlockFfi
Libs
  preamble

(* ---- 1. Fixed M3 256 KB Slot Virtual Addresses ---- *)

Definition FORGE_M3_VENEERS_BASE_def:
  FORGE_M3_VENEERS_BASE : word64 = 0x00400000w
End
Definition FORGE_M3_FFICOMMIT_VENEER_def:
  FORGE_M3_FFICOMMIT_VENEER : word64 = 0x00400070w
End
Definition FORGE_M3_FFIRECV_VENEER_def:
  FORGE_M3_FFIRECV_VENEER : word64 = 0x00400080w
End
Definition FORGE_M3_FFISEND_VENEER_def:
  FORGE_M3_FFISEND_VENEER : word64 = 0x00400090w
End
Definition FORGE_M3_FFIBOOT_VENEER_def:
  FORGE_M3_FFIBOOT_VENEER : word64 = 0x004000A0w
End
Definition FORGE_M3_INSTALL_VENEER_def:
  FORGE_M3_INSTALL_VENEER : word64 = 0x004000B0w
End
Definition FORGE_M3_EXIT_VENEER_def:
  FORGE_M3_EXIT_VENEER : word64 = 0x004000C0w
End
Definition FORGE_M3_CAKE_MAIN_def:
  FORGE_M3_CAKE_MAIN : word64 = 0x004000D0w
End
Definition FORGE_M3_MAX_CODE_BYTES_def:
  FORGE_M3_MAX_CODE_BYTES : num = 261936
End
Definition FORGE_M3_SHIM_BASE_def:
  FORGE_M3_SHIM_BASE : word64 = 0x00450000w
End
Definition FORGE_M3_FFIRECV_def:
  FORGE_M3_FFIRECV : word64 = 0x00450040w
End
Definition FORGE_M3_FFISEND_def:
  FORGE_M3_FFISEND : word64 = 0x004500C0w
End
Definition FORGE_M3_FFICOMMIT_def:
  FORGE_M3_FFICOMMIT : word64 = 0x0045011Cw
End
Definition FORGE_M3_FFIBOOT_def:
  FORGE_M3_FFIBOOT : word64 = 0x004501A4w
End
Definition FORGE_M3_CML_EXIT_def:
  FORGE_M3_CML_EXIT : word64 = 0x0045027Cw
End
Definition FORGE_M3_CML_INSTALL_def:
  FORGE_M3_CML_INSTALL : word64 = 0x00450290w
End
Definition FORGE_M3_SHIM_END_def:
  FORGE_M3_SHIM_END : word64 = 0x004502A0w
End
Definition FORGE_M3_RX_TMP_BYTES_def:
  FORGE_M3_RX_TMP_BYTES : num = 544
End

Definition m3_slot_cb_begin_def:
  m3_slot_cb_begin (code_len:num) : word64 = FORGE_M3_CAKE_MAIN + n2w code_len
End

Definition m3_slot_cb_end_def:
  m3_slot_cb_end (code_len:num) : word64 = align_up_64k (m3_slot_cb_begin code_len)
End

Definition m3_slot_cbspace_def:
  m3_slot_cbspace (code_len:num) : num = w2n (m3_slot_cb_end code_len - m3_slot_cb_begin code_len)
End

Definition m3_slot_layout_ok_def:
  m3_slot_layout_ok (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64) ⇔
    FORGE_M3_CAKE_MAIN <₊ cb_begin ∧ cb_begin ≤₊ cb_end ∧ cb_end ≤₊ FORGE_SLOT_END ∧
    FORGE_CAKE_BITMAPS ≤₊ bm_buf_end ∧ bm_buf_end ≤₊ FORGE_DATA_SLOT_END
End

(* ---- 2. Parameterized 52-Word ARM64 Veneers & Fixed 168-Word Airlock Shim ---- *)

Definition forge_m3_slot_veneers_def:
  forge_m3_slot_veneers (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64) : word32 list = [
    (* 0..7: x0 = cake_main (0x4000D0), x1 = [cml_heap (0x460000)], [x1] = cake_bitmaps (0x460018) *)
    0x90000000w; 0x91034000w; 0x90000301w; 0x91000021w;
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
    (* 20..27: x2 = [cml_stack], x3 = [cml_stackend], b cake_main (0x4000D0), nop *)
    0x90000302w; 0x91002042w; 0xF9400042w; 0x90000303w;
    0x91004063w; 0xF9400063w; 0x1400001Aw; 0xD503201Fw;
    (* 28..51: 4 FFI veneers (commit, recv64, send128, bootload) + install + exit *)
    0x1401402Bw; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x14013FF0w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x1401400Cw; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x14014041w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x14014078w; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw;
    0x1401406Fw; 0xD503201Fw; 0xD503201Fw; 0xD503201Fw
  ]
End

Definition forge_shim_airlock_words_def:
  forge_shim_airlock_words : word32 list = [
    (* _start: 0x450000 .. 0x45003C (16 words) *)
    0x90000180w; 0x91000000w; 0x90000081w; 0x91000021w;
    0xF9000020w; 0x90000380w; 0x91000000w; 0x90000081w;
    0x91002021w; 0xF9000020w; 0x90000580w; 0x91000000w;
    0x90000081w; 0x91004021w; 0xF9000020w; 0x17FEBFF1w;
    (* ffirecv64: 0x450040 .. 0x4500BC (32 words) *)
    0xF101047Fw; 0x540003C3w; 0xAA0203E9w; 0x9000010Aw;
    0x9100014Aw; 0xD280080Bw; 0xB40001ABw; 0xD2800000w;
    0xAA0A03E1w; 0xAA0B03E2w; 0xD28007E8w; 0xD4000001w;
    0xB100101Fw; 0x54FFFF20w; 0xF100001Fw; 0x540001CDw;
    0x8B00014Aw; 0xCB00016Bw; 0x17FFFFF4w; 0x9000010Cw;
    0x9100018Cw; 0xD280000Bw; 0x386B698Aw; 0x9100056Bw;
    0x382B692Aw; 0xF101017Fw; 0x54FFFF83w; 0x3900013Fw;
    0xD65F03C0w; 0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* ffisend128: 0x4500C0 .. 0x450118 (23 words) *)
    0xF102047Fw; 0x540002A3w; 0xAA0203E9w; 0x9100044Aw;
    0xD280100Bw; 0xB40001ABw; 0xD2800020w; 0xAA0A03E1w;
    0xAA0B03E2w; 0xD2800808w; 0xD4000001w; 0xB100101Fw;
    0x54FFFF20w; 0xF100001Fw; 0x540000CDw; 0x8B00014Aw;
    0xCB00016Bw; 0x17FFFFF4w; 0x3900013Fw; 0xD65F03C0w;
    0x5280002Cw; 0x3900012Cw; 0xD65F03C0w;
    (* fficommit: 0x45011C .. 0x4501A0 (34 words) *)
    0xF104087Fw; 0x54000403w; 0xAA0203E9w; 0x3940052Dw;
    0x924001ADw; 0xD378DDADw; 0x9100092Aw; 0xD280200Bw;
    0xB40001EBw; 0xD2800060w; 0xAA0A03E1w; 0xAA0B03E2w;
    0xAA0D03E3w; 0xD2800888w; 0xD4000001w; 0xB100101Fw;
    0x54FFFF00w; 0xF100001Fw; 0x540001ADw; 0x8B00014Aw;
    0xCB00016Bw; 0x8B0001ADw; 0x17FFFFF2w; 0xD2800060w;
    0xD2800A68w; 0xD4000001w; 0xB100101Fw; 0x54FFFF80w;
    0xB5000060w; 0x3900013Fw; 0xD65F03C0w; 0x5280002Cw;
    0x3900012Cw; 0xD65F03C0w;
    (* ffibootload: 0x4501A4 .. 0x450278 (54 words) *)
    0xF108847Fw; 0x54000683w; 0xAA0203E9w; 0x9000010Aw;
    0x9100014Aw; 0xD280040Bw; 0xB40001ABw; 0xD2800080w;
    0xAA0A03E1w; 0xAA0B03E2w; 0xD28007E8w; 0xD4000001w;
    0xB100101Fw; 0x54FFFF20w; 0xF100001Fw; 0x5400048Dw;
    0x8B00014Aw; 0xCB00016Bw; 0x17FFFFF4w; 0xD280400Bw;
    0xD280000Dw; 0xB400028Bw; 0xD2800060w; 0xAA0A03E1w;
    0xAA0B03E2w; 0xAA0D03E3w; 0xD2800868w; 0xD4000001w;
    0xB100101Fw; 0x54FFFF00w; 0xB40000C0w; 0xB7F80280w;
    0x8B00014Aw; 0xCB00016Bw; 0x8B0001ADw; 0x17FFFFF2w;
    0xB40000ABw; 0x3900015Fw; 0x9100054Aw; 0xD100056Bw;
    0x17FFFFFCw; 0x9000010Cw; 0x9100018Cw; 0xD280000Bw;
    0x386B698Aw; 0x9100056Bw; 0x382B692Aw; 0xF108817Fw;
    0x54FFFF83w; 0x3900013Fw; 0xD65F03C0w; 0x5280002Cw;
    0x3900012Cw; 0xD65F03C0w;
    (* cml_exit: 0x45027C .. 0x45028C (5 words) *)
    0xB4000040w; 0xD2800020w; 0xD2800BC8w; 0xD4000001w;
    0x14000000w;
    (* cml_install: 0x450290 .. 0x45029C (4 words) *)
    0xD2800040w; 0xD2800BC8w; 0xD4000001w; 0x14000000w
  ]
End

Definition m3_shim_loaded_slot_def:
  m3_shim_loaded_slot (cb_begin:word64) (cb_end:word64) (bm_buf_end:word64) (mem:word64 -> word8) ⇔
    words32_in_mem FORGE_M3_VENEERS_BASE (forge_m3_slot_veneers cb_begin cb_end bm_buf_end) mem ∧
    words32_in_mem FORGE_M3_SHIM_BASE forge_shim_airlock_words mem
End

(* ---- 3. Parameterized M3 Memory Regions & Machine Config ---- *)

Definition forge_m3_code_region_def:
  forge_m3_code_region (cb_end:word64) : word64 set =
    { a | FORGE_M3_CAKE_MAIN ≤₊ a ∧ a <₊ cb_end }
End

Definition forge_m3_prog_addresses_def:
  forge_m3_prog_addresses (cb_end:word64) (bm_buf_end:word64) : word64 set =
    forge_m3_code_region cb_end ∪
    forge_bitmaps_region_slot bm_buf_end ∪
    forge_heap_stack_region
End

Definition forge_m3_shim_code_region_def:
  forge_m3_shim_code_region : word64 set =
    { a | FORGE_M3_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_M3_CAKE_MAIN } ∪
    { a | FORGE_M3_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_M3_SHIM_END }
End

Definition forge_m3_rx_tmp_region_def:
  forge_m3_rx_tmp_region : word64 set =
    { a | FORGE_RX_TMP ≤₊ a ∧ a <₊ FORGE_RX_TMP + 544w }
End

Definition forge_m3_mc_slot_def:
  forge_m3_mc_slot (cb_end:word64) (bm_buf_end:word64) ffi_names_l ffi_if inst_if =
    <| prog_addresses    := forge_m3_prog_addresses cb_end bm_buf_end
     ; shared_addresses  := ∅
     ; ffi_entry_pcs     := [FORGE_M3_FFIBOOT_VENEER;
                             FORGE_M3_FFISEND_VENEER;
                             FORGE_M3_FFIRECV_VENEER;
                             FORGE_M3_FFICOMMIT_VENEER]
     ; ffi_names         := ffi_names_l
     ; ptr_reg           := 0
     ; len_reg           := 1
     ; ptr2_reg          := 2
     ; len2_reg          := 3
     ; ffi_interfer      := ffi_if
     ; callee_saved_regs := [19;20;21;22;23;24;25;26;27;28]
     ; next_interfer     := K I
     ; halt_pc           := FORGE_M3_EXIT_VENEER
     ; install_pc        := FORGE_M3_INSTALL_VENEER
     ; install_interfer  := inst_if
     ; target            := arm8_target
     ; mmio_info         := []
     |>
End

Definition m3_real_interfer_ok_slot_def:
  m3_real_interfer_ok_slot (cb_end:word64) (bm_buf_end:word64) (cbspace:num)
                           ffi_names_l B ffi_if inst_if ⇔
    let mc = forge_m3_mc_slot cb_end bm_buf_end ffi_names_l
               (λk (i, bs, s). erase (ffi_if k (i, bs, restore B s)))
               (λk (bs, s). erase (inst_if k (bs, restore B s))) in
      ffi_interfer_ok FORGE_M3_CAKE_MAIN mc ∧
      install_interfer_ok FORGE_M3_CAKE_MAIN cbspace mc ∧
      (∀k i bs s. bits_of s = B ⇒
                  bits_of (ffi_if k (i, bs, s)) = B ∧
                  (ffi_if k (i, bs, s)).SP_EL0 = s.SP_EL0) ∧
      (∀k bs s. bits_of s = B ⇒
                bits_of (inst_if k (bs, s)) = B ∧
                (inst_if k (bs, s)).SP_EL0 = s.SP_EL0)
End

(* ---- 4. Explicit 6-Syscall Linux AArch64 OS Contract (Page Cache vs Durable Disk) ---- *)

Datatype:
  m3_os = <|
    key_in  : word8 list;
    disk    : word8 list;
    durable : word8 list;
    inp     : word8 list;
    out     : word8 list
  |>
End

Definition patch_bytes_def:
  patch_bytes (off:num) (chunk:word8 list) (buf:word8 list) : word8 list =
    let padded = if LENGTH buf < off then buf ++ REPLICATE (off - LENGTH buf) 0w else buf in
      TAKE off padded ++ chunk ++ DROP (off + LENGTH chunk) padded
End

Definition svc_read_fd_rel_def:
  svc_read_fd_rel (fd:word64) (allow_err:bool)
                  (src:word8 list) (s:arm8_state) (s':arm8_state) (rest:word8 list) ⇔
    s.REG 8w = 63w ∧
    s.REG 0w = fd ∧
    svc_frame_rel s s' ∧
    ( (s'.REG 0w = -4w ∧ s'.MEM = s.MEM ∧ rest = src) ∨
      (s'.REG 0w = 0w ∧ src = [] ∧ s'.MEM = s.MEM ∧ rest = []) ∨
      (allow_err ∧ word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w ∧ s'.MEM = s.MEM ∧ rest = src) ∨
      (∃n. 1 ≤ n ∧ n ≤ w2n (s.REG 2w) ∧ n ≤ LENGTH src ∧
           s'.REG 0w = n2w n ∧
           s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n src) s.MEM ∧
           rest = DROP n src) )
End

Definition svc_pread64_rel_def:
  svc_pread64_rel (allow_err:bool) (disk:word8 list) (s:arm8_state) (s':arm8_state) ⇔
    s.REG 8w = 67w ∧
    s.REG 0w = 3w ∧
    svc_frame_rel s s' ∧
    let off = w2n (s.REG 3w) in
    let cnt = w2n (s.REG 2w) in
    ( (s'.REG 0w = -4w ∧ s'.MEM = s.MEM) ∨
      (s'.REG 0w = 0w ∧ LENGTH disk ≤ off ∧ s'.MEM = s.MEM) ∨
      (allow_err ∧ word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w ∧ s'.MEM = s.MEM) ∨
      (∃n. 1 ≤ n ∧ n ≤ cnt ∧ off + n ≤ LENGTH disk ∧
           s'.REG 0w = n2w n ∧
           s'.MEM = asm_write_bytearray (s.REG 1w) (TAKE n (DROP off disk)) s.MEM) )
End

Definition svc_pwrite64_rel_def:
  svc_pwrite64_rel (allow_err:bool) (disk:word8 list) (s:arm8_state) (s':arm8_state) (disk':word8 list) ⇔
    s.REG 8w = 68w ∧
    s.REG 0w = 3w ∧
    svc_frame_rel s s' ∧
    s'.MEM = s.MEM ∧
    let off = w2n (s.REG 3w) in
    let cnt = w2n (s.REG 2w) in
    ( (s'.REG 0w = -4w ∧ disk' = disk) ∨
      (allow_err ∧ (s'.REG 0w = 0w ∨ (word_msb (s'.REG 0w) ∧ s'.REG 0w ≠ -4w)) ∧ disk' = disk) ∨
      (∃n. 1 ≤ n ∧ n ≤ cnt ∧
           s'.REG 0w = n2w n ∧
           disk' = patch_bytes off (GENLIST (λi. s.MEM (s.REG 1w + n2w i)) n) disk) )
End

Definition svc_fdatasync_rel_def:
  svc_fdatasync_rel (allow_err:bool) (disk:word8 list) (dur:word8 list)
                    (s:arm8_state) (s':arm8_state) (dur':word8 list) ⇔
    s.REG 8w = 83w ∧
    s.REG 0w = 3w ∧
    svc_frame_rel s s' ∧
    s'.MEM = s.MEM ∧
    ( (s'.REG 0w = -4w ∧ dur' = dur) ∨
      (s'.REG 0w = 0w ∧ dur' = disk) ∨
      (allow_err ∧ s'.REG 0w ≠ 0w ∧ s'.REG 0w ≠ -4w ∧ dur' = dur) )
End

Definition m3_whole_step_def:
  m3_whole_step (allow_err:bool) (os:m3_os, s:arm8_state) (os':m3_os, s':arm8_state) ⇔
    (¬is_svc0_at s ∧ NextStateARM8 s = SOME s' ∧ os' = os) ∨
    (is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 0w ∧
       ∃rest. svc_read_fd_rel 0w allow_err os.inp s s' rest ∧ os' = os with inp := rest) ∨
    (is_svc0_at s ∧ s.REG 8w = 63w ∧ s.REG 0w = 4w ∧
       ∃rest. svc_read_fd_rel 4w allow_err os.key_in s s' rest ∧ os' = os with key_in := rest) ∨
    (is_svc0_at s ∧ s.REG 8w = 64w ∧ s.REG 0w = 1w ∧
       ∃chunk. (if allow_err then svc_write_rel else svc_write_noerr_rel) s s' chunk ∧
               os' = os with out := os.out ++ chunk) ∨
    (is_svc0_at s ∧ s.REG 8w = 67w ∧
       svc_pread64_rel allow_err os.disk s s' ∧ os' = os) ∨
    (is_svc0_at s ∧ s.REG 8w = 68w ∧
       ∃disk'. svc_pwrite64_rel allow_err os.disk s s' disk' ∧ os' = os with disk := disk') ∨
    (is_svc0_at s ∧ s.REG 8w = 83w ∧
       ∃dur'. svc_fdatasync_rel allow_err os.disk os.durable s s' dur' ∧ os' = os with durable := dur')
End

(* ---- 5. Parameterized Initial M3 ELF Loaded Predicate ---- *)

Definition forge_m3_slot_loaded_def:
  forge_m3_slot_loaded (bytes:word8 list) (bitmaps:num list) (ms0:arm8_state) ⇔
    let cb_begin = m3_slot_cb_begin (LENGTH bytes) in
    let cb_end = m3_slot_cb_end (LENGTH bytes) in
    let bm_buf_end = slot_bm_buf_end (LENGTH bitmaps) in
      0 < LENGTH bytes ∧
      LENGTH bytes ≤ FORGE_M3_MAX_CODE_BYTES ∧
      LENGTH bitmaps ≤ FORGE_MAX_BITMAP_WORDS ∧
      arm8_ok (erase ms0) ∧
      sp_ok ms0 ∧
      ms0.PC = FORGE_M3_SHIM_BASE ∧
      m3_shim_loaded_slot cb_begin cb_end bm_buf_end ms0.MEM ∧
      read_bytearray FORGE_M3_CAKE_MAIN (LENGTH bytes)
        (λa. if a ∈ forge_m3_prog_addresses cb_end bm_buf_end then SOME (ms0.MEM a) else NONE) = SOME bytes ∧
      (∀i. i < LENGTH bitmaps ⇒
        mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) = n2w (EL i bitmaps))
End
