(*
  Forge Reusable Runtime: Parameterized 256 KB Slot Utilities, Installed Proof & Non-Vacuity.

  Generic over ANY kernel (code <= 261,968 B, bitmaps <= 8,189 u64 words, 80-word shim).
  Eliminates all per-kernel boilerplate for M2+ kernels.
*)
Theory forge_slotUtil
Ancestors
  forge_runtimeSpec forge_arm8Erasure forge_shimProof
  arm8_target arm8_configProof lab_to_targetProof backendProof
  targetProps semanticsProps alignment set_sep byte
Libs
  preamble blastLib wordsLib

(* ---- 1. FFI Name Extraction from In-Logic Compilation Theorem ---- *)

Theorem get_shmem_info_LENGTH[local]:
  ∀xs c l1 l2.
    get_shmem_info xs c l1 l2 = (t1,t2) ∧ LENGTH l1 = LENGTH l2 ⇒
    LENGTH t1 = LENGTH t2
Proof
  ho_match_mp_tac lab_to_targetTheory.get_shmem_info_ind \\ rw []
  \\ gvs [lab_to_targetTheory.get_shmem_info_def]
  \\ pairarg_tac \\ gvs []
QED

Theorem IMP_EVERY_list_add_if_fresh[local]:
  ∀xs x p. p x ∧ EVERY p xs ⇒ EVERY p (list_add_if_fresh x xs)
Proof
  Induct \\ gvs [lab_to_targetTheory.list_add_if_fresh_def] \\ rw []
QED

Theorem find_ffi_names_ExtCall[local]:
  ∀xs. EVERY (λx. ∃i. ExtCall i = x) (find_ffi_names xs)
Proof
  ho_match_mp_tac lab_to_targetTheory.find_ffi_names_ind
  \\ rpt strip_tac
  \\ asm_rewrite_tac [lab_to_targetTheory.find_ffi_names_def, EVERY_DEF]
  \\ Cases_on `x` \\ gvs []
  \\ Cases_on `a` \\ gvs []
  \\ irule IMP_EVERY_list_add_if_fresh \\ gvs []
QED

Theorem MAP_ExtCall_ffinames[local]:
  ∀xs.
    EVERY (λx. ∃i. ExtCall i = x) xs ⇒
    xs = MAP ExtCall (ffinames_to_string_list xs)
Proof
  Induct \\ gvs [backendTheory.ffinames_to_string_list_def]
  \\ Cases \\ gvs [backendTheory.ffinames_to_string_list_def]
QED

Theorem compile_imp_ffi_names:
  ∀asm_conf c p b d c1 f.
    backend$compile asm_conf c p = SOME (b,d,c1) ∧
    c1.lab_conf.shmem_extra = [] ∧ f ≠ [] ∧
    c.lab_conf.ffi_names = NONE ∧
    ffinames_to_string_list (the [] c1.lab_conf.ffi_names) = f ⇒
    c1.lab_conf.ffi_names = SOME (MAP ExtCall f)
Proof
  rpt gen_tac
  \\ Cases_on `c1.lab_conf.ffi_names`
  \\ gvs [miscTheory.the_def, backendTheory.ffinames_to_string_list_def]
  \\ gvs [backendTheory.compile_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [oneline backendTheory.attach_bitmaps_def, AllCaseEqs()]
  \\ strip_tac \\ gvs []
  \\ gvs [lab_to_targetTheory.compile_def]
  \\ gvs [lab_to_targetTheory.compile_lab_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule get_shmem_info_LENGTH \\ gvs [] \\ rw []
  \\ irule MAP_ExtCall_ffinames
  \\ gvs [find_ffi_names_ExtCall]
QED

(* ---- 2. Word, Alignment, Memory & Slot Arithmetic Helpers ---- *)

Theorem log2_8[local]:
  LOG2 8 = 3
Proof
  EVAL_TAC
QED

Theorem bytes_in_word_64:
  (bytes_in_word : word64) = 8w
Proof
  EVAL_TAC
QED

Theorem w2n_n2w_64:
  ∀n. n < 18446744073709551616 ⇒ w2n (n2w n : word64) = n
Proof
  simp [wordsTheory.w2n_n2w, dimword_64]
QED

Theorem word_add_1w_n2w:
  ∀(a:word64) i. a + 1w + n2w i = a + n2w (SUC i)
Proof
  rpt gen_tac
  \\ REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w, arithmeticTheory.ADD1]
  \\ simp []
QED

Theorem word_add_n2w_n2w:
  ∀(a:word64) m n. a + n2w m + n2w n = a + n2w (m + n)
Proof
  rpt gen_tac
  \\ REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w]
QED

Theorem byte_align_64:
  ∀a:word64. byte_align a = a && 0xFFFFFFFFFFFFFFF8w
Proof
  gen_tac \\ simp [alignmentTheory.byte_align_def, alignmentTheory.align_def, log2_8]
  \\ blastLib.BBLAST_TAC
QED

Theorem byte_aligned_mod8:
  ∀a:word64. byte_aligned a ⇔ w2n a MOD 8 = 0
Proof
  gen_tac \\ simp [alignmentTheory.byte_aligned_def, log2_8, alignmentTheory.aligned_w2n]
QED

Theorem word64_add_lo_ls:
  ∀a b c:num. a + b < 18446744073709551616 ∧ c < 18446744073709551616 ⇒
    ((n2w a + n2w b : word64) <₊ n2w c ⇔ a + b < c) ∧
    ((n2w a + n2w b : word64) ≤₊ n2w c ⇔ a + b ≤ c) ∧
    (n2w c ≤₊ (n2w a + n2w b : word64) ⇔ c ≤ a + b) ∧
    (n2w c <₊ (n2w a + n2w b : word64) ⇔ c < a + b)
Proof
  rpt strip_tac \\ simp [wordsTheory.word_add_n2w, wordsTheory.WORD_LO, wordsTheory.WORD_LS, w2n_n2w_64]
QED

Theorem div_mod_4:
  ∀i j. j < 4 ⇒ (4 * i + j) DIV 4 = i ∧ (4 * i + j) MOD 4 = j
Proof
  rpt strip_tac
  \\ `4 * i = i * 4` by metis_tac [arithmeticTheory.MULT_COMM]
  \\ pop_assum SUBST1_TAC
  \\ simp [arithmeticTheory.DIV_MULT, arithmeticTheory.MOD_MULT]
QED

Theorem div_mod_8:
  ∀i j. j < 8 ⇒ (8 * i + j) DIV 8 = i ∧ (8 * i + j) MOD 8 = j
Proof
  rpt strip_tac
  \\ `8 * i = i * 8` by metis_tac [arithmeticTheory.MULT_COMM]
  \\ pop_assum SUBST1_TAC
  \\ simp [arithmeticTheory.DIV_MULT, arithmeticTheory.MOD_MULT]
QED

Theorem align_up_64k_bounds[local]:
  ∀a:word64. 0x004000B0w <₊ a ∧ a ≤₊ 0x00440000w ⇒
    a ≤₊ align_up_64k a ∧ align_up_64k a ≤₊ 0x00440000w
Proof
  simp [align_up_64k_def] \\ blastLib.BBLAST_TAC
QED

Theorem slot_params_props:
  ∀code_len data_len.
    0 < code_len ∧ code_len ≤ FORGE_MAX_CODE_BYTES ∧ data_len ≤ FORGE_MAX_BITMAP_WORDS ⇒
    let cb_begin = slot_cb_begin code_len in
    let cb_end = slot_cb_end code_len in
    let cbsp = slot_cbspace code_len in
    let bm_end = slot_bm_buf_end data_len in
      slot_layout_ok cb_begin cb_end bm_end ∧
      FORGE_CAKE_MAIN + n2w code_len = cb_begin ∧
      cb_begin + n2w cbsp = cb_end ∧
      FORGE_CAKE_MAIN + n2w code_len + n2w cbsp = cb_end ∧
      w2n FORGE_CAKE_MAIN + code_len = w2n cb_begin ∧
      w2n FORGE_CAKE_MAIN + code_len + cbsp = w2n cb_end ∧
      w2n cb_end ≤ 0x00440000 ∧
      FORGE_CAKE_BITMAPS + n2w (8 * data_len) = bm_end ∧
      FORGE_CAKE_BITMAPS + n2w data_len * (bytes_in_word:word64) = bm_end ∧
      w2n FORGE_CAKE_BITMAPS + 8 * data_len = w2n bm_end ∧
      w2n bm_end ≤ 0x00470000
Proof
  rpt strip_tac
  \\ PURE_REWRITE_TAC [LET_THM] \\ BETA_TAC
  \\ fs [FORGE_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
  \\ qabbrev_tac `cb_begin = slot_cb_begin code_len`
  \\ qabbrev_tac `cb_end = slot_cb_end code_len`
  \\ qabbrev_tac `cbsp = slot_cbspace code_len`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end data_len`
  \\ `cb_begin = FORGE_CAKE_MAIN + n2w code_len` by simp [Abbr `cb_begin`, slot_cb_begin_def]
  \\ `w2n cb_begin = 0x004000B0 + code_len` by
       simp [FORGE_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64]
  \\ `0x004000B0w <₊ cb_begin ∧ cb_begin ≤₊ 0x00440000w` by
       simp [wordsTheory.WORD_LO, wordsTheory.WORD_LS]
  \\ `cb_end = align_up_64k cb_begin` by
       simp [Abbr `cb_end`, Abbr `cb_begin`, slot_cb_end_def]
  \\ `cb_begin ≤₊ cb_end ∧ cb_end ≤₊ 0x00440000w` by
       (qpat_assum `cb_end = align_up_64k cb_begin` SUBST1_TAC
        \\ MATCH_MP_TAC align_up_64k_bounds \\ simp [])
  \\ `w2n cb_end ≤ 0x00440000` by fs [wordsTheory.WORD_LS]
  \\ `cbsp = w2n (cb_end - cb_begin)` by
       (mp_tac (Q.SPEC `code_len` slot_cbspace_def)
        \\ qpat_assum `Abbrev (cbsp = _)` (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])
        \\ qpat_assum `Abbrev (cb_end = _)` (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])
        \\ qpat_assum `Abbrev (cb_begin = _)` (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])
        \\ simp [])
  \\ `w2n cb_begin + cbsp = w2n cb_end` by
       (qpat_assum `cbsp = _` SUBST1_TAC
        \\ qspecl_then [`cb_end`, `cb_begin`] mp_tac wordsTheory.word_sub_w2n
        \\ impl_tac >- first_assum ACCEPT_TAC
        \\ disch_then SUBST1_TAC
        \\ qpat_assum `cb_begin ≤₊ cb_end` mp_tac
        \\ REWRITE_TAC [wordsTheory.WORD_LS] \\ decide_tac)
  \\ `cb_begin + n2w cbsp = cb_end` by
       (qpat_assum `cbsp = _` SUBST1_TAC \\ REWRITE_TAC [wordsTheory.n2w_w2n] \\ blastLib.BBLAST_TAC)
  \\ `FORGE_CAKE_MAIN + n2w code_len + n2w cbsp = cb_end` by
       (qpat_assum `cb_begin = _` (SUBST1_TAC o SYM) \\ first_assum ACCEPT_TAC)
  \\ `w2n FORGE_CAKE_MAIN + code_len = w2n cb_begin` by simp [FORGE_CAKE_MAIN_def]
  \\ `w2n FORGE_CAKE_MAIN + code_len + cbsp = w2n cb_end` by decide_tac
  \\ `bm_end = FORGE_CAKE_BITMAPS + n2w (8 * data_len)` by simp [Abbr `bm_end`, slot_bm_buf_end_def]
  \\ `w2n bm_end = 0x00460018 + 8 * data_len` by
       simp [FORGE_CAKE_BITMAPS_def, wordsTheory.word_add_n2w, w2n_n2w_64]
  \\ `w2n bm_end ≤ 0x00470000` by decide_tac
  \\ `FORGE_CAKE_BITMAPS ≤₊ bm_end ∧ bm_end ≤₊ FORGE_DATA_SLOT_END` by
       simp [FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def, wordsTheory.WORD_LS]
  \\ `slot_layout_ok cb_begin cb_end bm_end` by
       (REWRITE_TAC [slot_layout_ok_def, FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def]
        \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ `FORGE_CAKE_BITMAPS + n2w data_len * (bytes_in_word:word64) = bm_end` by
       (qpat_assum `bm_end = _` SUBST1_TAC
        \\ AP_TERM_TAC \\ simp [bytes_in_word_64, wordsTheory.word_mul_n2w])
  \\ `w2n FORGE_CAKE_BITMAPS + 8 * data_len = w2n bm_end` by simp [FORGE_CAKE_BITMAPS_def]
  \\ `FORGE_CAKE_MAIN + n2w code_len = cb_begin` by (irule EQ_SYM \\ first_assum ACCEPT_TAC)
  \\ `FORGE_CAKE_BITMAPS + n2w (8 * data_len) = bm_end` by (irule EQ_SYM \\ first_assum ACCEPT_TAC)
  \\ rpt conj_tac
  \\ TRY (first_assum ACCEPT_TAC)
  \\ TRY decide_tac
  \\ TRY (qpat_assum `cb_begin + n2w cbsp = cb_end` (SUBST1_TAC o SYM) \\ blastLib.BBLAST_TAC)
  \\ qpat_assum `FORGE_CAKE_BITMAPS + n2w data_len * _ = bm_end` (SUBST1_TAC o SYM)
  \\ blastLib.BBLAST_TAC
QED

Theorem forge_veneer_facts_slot:
  ∀cb_begin cb_end bm_end.
    slot_layout_ok cb_begin cb_end bm_end ⇒
    FORGE_EXIT_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_INSTALL_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_FFISEND_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_FFIRECV_VENEER ∉ forge_prog_addresses_slot cb_end bm_end ∧
    FORGE_EXIT_VENEER ≠ FORGE_INSTALL_VENEER ∧
    FORGE_EXIT_VENEER ≠ FORGE_FFISEND_VENEER ∧
    FORGE_EXIT_VENEER ≠ FORGE_FFIRECV_VENEER ∧
    FORGE_INSTALL_VENEER ≠ FORGE_FFISEND_VENEER ∧
    FORGE_INSTALL_VENEER ≠ FORGE_FFIRECV_VENEER ∧
    FORGE_FFISEND_VENEER ≠ FORGE_FFIRECV_VENEER ∧
    FORGE_INSTALL_VENEER ≠ FORGE_EXIT_VENEER ∧
    FORGE_FFISEND_VENEER ≠ FORGE_EXIT_VENEER ∧
    FORGE_FFISEND_VENEER ≠ FORGE_INSTALL_VENEER ∧
    FORGE_FFIRECV_VENEER ≠ FORGE_EXIT_VENEER ∧
    FORGE_FFIRECV_VENEER ≠ FORGE_INSTALL_VENEER ∧
    FORGE_FFIRECV_VENEER ≠ FORGE_FFISEND_VENEER
Proof
  rpt strip_tac
  \\ fs [slot_layout_ok_def, forge_prog_addresses_slot_def, forge_code_region_slot_def,
         forge_bitmaps_region_slot_def, forge_heap_stack_region_def,
         FORGE_CAKE_MAIN_def, FORGE_SLOT_END_def, FORGE_CAKE_BITMAPS_def, FORGE_DATA_SLOT_END_def,
         FORGE_HEAP_def, FORGE_STACKEND_def,
         FORGE_EXIT_VENEER_def, FORGE_INSTALL_VENEER_def,
         FORGE_FFISEND_VENEER_def, FORGE_FFIRECV_VENEER_def]
  \\ blastLib.BBLAST_TAC
QED

Theorem mem_dword_get_byte:
  ∀m (a:word64). m a = get_byte a (mem_dword m (byte_align a)) F
Proof
  rpt gen_tac
  \\ qabbrev_tac `lo : word3 = (2 >< 0) a`
  \\ `byte_index a F = 8 * w2n lo` by
       (simp [byteTheory.byte_index_def, Abbr `lo`]
        \\ `w2n ((2 >< 0) a : word3) = w2n a MOD 8` by
             (Cases_on `a`
              \\ simp [wordsTheory.word_extract_n2w, wordsTheory.w2n_n2w,
                       bitTheory.BITS_ZERO3, dimword_64])
        \\ simp [])
  \\ qspec_then `lo` strip_assume_tac
       (Q.prove (`∀w:word3. w = 0w ∨ w = 1w ∨ w = 2w ∨ w = 3w ∨ w = 4w ∨ w = 5w ∨ w = 6w ∨ w = 7w`,
                 wordsLib.Cases_word_value \\ simp []))
  \\ (
    `a = byte_align a + w2w lo` by
      (simp [byte_align_64] \\ qunabbrev_tac `lo` \\ pop_assum mp_tac \\ blastLib.BBLAST_TAC)
    \\ pop_assum (fn th => CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [th]))))
    \\ simp [byteTheory.get_byte_def, arm8_stepTheory.mem_dword_def]
    \\ blastLib.BBLAST_TAC)
QED

Theorem mem_dword_cong_util:
  ∀m1 m2 (a:word64).
    (∀j. j < 8 ⇒ m1 (a + n2w j) = m2 (a + n2w j)) ⇒
    mem_dword m1 a = mem_dword m2 a
Proof
  rpt strip_tac
  \\ first_x_assum (fn th =>
       EVERY (map (fn k => mp_tac (Q.SPEC k th)) [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`]))
  \\ simp [] \\ rpt strip_tac \\ simp [arm8_stepTheory.mem_dword_def]
QED

Theorem read_bytearray_cong:
  ∀n (a:word64) f g.
    (∀i. i < n ⇒ f (a + n2w i) = g (a + n2w i)) ⇒
    read_bytearray a n f = read_bytearray a n g
Proof
  Induct \\ simp [miscTheory.read_bytearray_def]
  \\ rpt strip_tac
  \\ `f a = g a` by (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ simp [] \\ Cases_on `g a` \\ simp []
  \\ `read_bytearray (a + 1w) n f = read_bytearray (a + 1w) n g` by
       (first_x_assum irule \\ rpt strip_tac
        \\ first_x_assum (qspec_then `SUC i` mp_tac)
        \\ simp [word_add_1w_n2w])
  \\ simp []
QED

Theorem read_bytearray_imp_bytes_in_mem:
  ∀bs (a:word64) m md k.
    (∀i. i < LENGTH bs ⇒ a + n2w i ∈ md ∧ a + n2w i ∉ k ∧ m (a + n2w i) = EL i bs) ⇒
    bytes_in_mem a bs m md k
Proof
  Induct \\ simp [miscTheory.bytes_in_mem_def]
  \\ rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ first_x_assum irule \\ gen_tac \\ strip_tac
  \\ first_x_assum (qspec_then `SUC i` mp_tac)
  \\ simp [word_add_1w_n2w]
QED

Theorem word_list_exists_0[local]:
  ∀a:word64. word_list_exists a 0 = emp
Proof
  gen_tac \\ simp [FUN_EQ_THM, miscTheory.word_list_exists_def, miscTheory.word_list_def,
                   set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
QED

Theorem mul8_step[local]:
  ∀p q:num. p * 8 < q * 8 ⇒ p * 8 + 8 ≤ q * 8
Proof
  rpt strip_tac
  \\ `p < q` by decide_tac
  \\ `p + 1 ≤ q` by decide_tac
  \\ `(p + 1) * 8 ≤ q * 8` by simp []
  \\ fs [arithmeticTheory.RIGHT_ADD_DISTRIB]
QED

Theorem word_list_slice:
  ∀xs (base:word64) (m:word64 -> 64 word_loc).
    (∀i. i < LENGTH xs ⇒ m (base + n2w (8 * i)) = EL i xs) ∧
    byte_aligned base ∧
    w2n base + 8 * LENGTH xs < dimword (:64) ⇒
    word_list base xs
      (fun2set (m, byte_aligned ∩ {a | base ≤₊ a ∧ a <₊ base + n2w (8 * LENGTH xs)}))
Proof
  Induct
  >- (
    rpt strip_tac
    \\ `byte_aligned ∩ {a | base ≤₊ a ∧ a <₊ base} = ∅` by
         (simp [EXTENSION, wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ gen_tac \\ strip_tac \\ decide_tac)
    \\ `fun2set (m, ∅) = ∅` by simp [set_sepTheory.fun2set_def, EXTENSION]
    \\ simp [miscTheory.word_list_def, set_sepTheory.emp_def])
  \\ rpt strip_tac
  \\ simp [miscTheory.word_list_def, bytes_in_word_64]
  \\ `w2n (base + 8w) = w2n base + 8` by
       (Cases_on `base`
        \\ fs [wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, dimword_64, arithmeticTheory.MULT_SUC])
  \\ `w2n (base + n2w (8 * SUC (LENGTH xs))) = w2n base + 8 * SUC (LENGTH xs)` by
       (Cases_on `base`
        \\ fs [wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, dimword_64, arithmeticTheory.MULT_SUC])
  \\ `base + 8w + n2w (8 * LENGTH xs) = base + n2w (8 * SUC (LENGTH xs))` by
       simp [word_add_n2w_n2w, arithmeticTheory.MULT_SUC]
  \\ qabbrev_tac `d1 : word64 set = {base}`
  \\ qabbrev_tac `d2 : word64 set =
        byte_aligned ∩ {a | base + 8w ≤₊ a ∧ a <₊ (base + 8w) + n2w (8 * LENGTH xs)}`
  \\ `byte_aligned ∩ {a | base ≤₊ a ∧ a <₊ base + n2w (8 * SUC (LENGTH xs))} = d1 ∪ d2` by (
       simp [Abbr `d1`, Abbr `d2`, EXTENSION] \\ gen_tac
       \\ `∀a:word64. a ∈ byte_aligned ⇔ byte_aligned a` by simp [SPECIFICATION]
       \\ simp []
       \\ eq_tac \\ strip_tac
       >- (
         Cases_on `x = base` \\ simp []
         \\ `w2n base < w2n x` by
              (`w2n base ≤ w2n x` by fs [wordsTheory.WORD_LS]
               \\ `w2n base ≠ w2n x` by (strip_tac \\ fs [wordsTheory.w2n_11])
               \\ decide_tac)
         \\ `w2n base = (w2n base DIV 8) * 8 ∧ w2n x = (w2n x DIV 8) * 8` by (
              qspec_then `w2n base` mp_tac (MATCH_MP arithmeticTheory.DIVISION (DECIDE ``0 < 8``))
              \\ qspec_then `w2n x` mp_tac (MATCH_MP arithmeticTheory.DIVISION (DECIDE ``0 < 8``))
              \\ fs [byte_aligned_mod8])
         \\ `w2n base + 8 ≤ w2n x` by metis_tac [mul8_step]
         \\ simp [wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ fs [wordsTheory.WORD_LO])
       >- (rveq \\ simp [wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ simp [arithmeticTheory.MULT_SUC])
       \\ simp [wordsTheory.WORD_LS, wordsTheory.WORD_LO]
       \\ fs [wordsTheory.WORD_LS, wordsTheory.WORD_LO] \\ decide_tac)
  \\ pop_assum SUBST1_TAC
  \\ irule miscTheory.fun2set_disjoint_union
  \\ rpt conj_tac
  >- (
    `m base = h` by (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
    \\ simp [Abbr `d1`, set_sepTheory.one_def, set_sepTheory.fun2set_def, EXTENSION,
             pairTheory.FORALL_PROD])
  >- (
    qunabbrev_tac `d2`
    \\ first_x_assum irule
    \\ rpt conj_tac
    >- (
      rpt strip_tac
      \\ `base + 8w + n2w (8 * i) = base + n2w (8 * SUC i)` by
           (simp [word_add_n2w_n2w, arithmeticTheory.MULT_SUC])
      \\ pop_assum SUBST1_TAC
      \\ first_x_assum (qspec_then `SUC i` mp_tac) \\ simp [])
    >- (fs [byte_aligned_mod8] \\ simp [arithmeticTheory.ADD_MODULUS_RIGHT])
    \\ fs [arithmeticTheory.MULT_SUC])
  \\ simp [Abbr `d1`, Abbr `d2`, DISJOINT_DEF, EXTENSION, wordsTheory.WORD_LS]
QED

Theorem words32_in_mem_pointwise[local]:
  ∀ws (base:word64) (m:word64 -> word8).
    (∀i. i < LENGTH ws ⇒
      m (base + n2w (4 * i))     = (7 >< 0)   (EL i ws) ∧
      m (base + n2w (4 * i + 1)) = (15 >< 8)  (EL i ws) ∧
      m (base + n2w (4 * i + 2)) = (23 >< 16) (EL i ws) ∧
      m (base + n2w (4 * i + 3)) = (31 >< 24) (EL i ws)) ⇒
    words32_in_mem base ws m
Proof
  Induct \\ simp [words32_in_mem_def]
  \\ rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ first_x_assum irule \\ gen_tac \\ strip_tac
  \\ first_x_assum (qspec_then `SUC i` mp_tac)
  \\ simp [word_add_n2w_n2w, arithmeticTheory.MULT_SUC, arithmeticTheory.ADD_CLAUSES]
QED

Theorem read_bytearray_pointwise[local]:
  ∀(bs:word8 list) (a:word64) (dm:word64 set) (m:word64 -> word8).
    (∀i. i < LENGTH bs ⇒ a + n2w i ∈ dm ∧ m (a + n2w i) = EL i bs) ⇒
    read_bytearray a (LENGTH bs) (λx. if x ∈ dm then SOME (m x) else NONE) = SOME bs
Proof
  Induct \\ simp [miscTheory.read_bytearray_def]
  \\ rpt strip_tac
  \\ `a ∈ dm ∧ m a = h` by (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
  \\ simp []
  \\ `read_bytearray (a + 1w) (LENGTH bs) (λx. if x ∈ dm then SOME (m x) else NONE) = SOME bs` by (
       first_x_assum irule \\ gen_tac \\ strip_tac
       \\ first_x_assum (qspec_then `SUC i` mp_tac) \\ simp [word_add_1w_n2w])
  \\ simp []
QED

Theorem dword_bytes_reassemble[local]:
  ∀m (a:word64) (w:word64).
    m a = (7 >< 0) w ∧ m (a + 1w) = (15 >< 8) w ∧ m (a + 2w) = (23 >< 16) w ∧
    m (a + 3w) = (31 >< 24) w ∧ m (a + 4w) = (39 >< 32) w ∧ m (a + 5w) = (47 >< 40) w ∧
    m (a + 6w) = (55 >< 48) w ∧ m (a + 7w) = (63 >< 56) w ⇒
    mem_dword m a = w
Proof
  rpt strip_tac \\ simp [arm8_stepTheory.mem_dword_def] \\ blastLib.BBLAST_TAC
QED

(* ---- 3. Generic Target Config, Installed & Non-Vacuity Theorems ---- *)

Theorem erase_mc_conf_ok_slot:
  ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_conf_ok (erase_mc B (forge_mc_slot cb_end bm_end fnames ffi_if inst_if))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ `mc_conf_ok (forge_mc_slot cb_end bm_end fnames ffi_if inst_if)` by (
       irule arm8_configProofTheory.arm8_machine_config_ok
       \\ simp [arm8_configProofTheory.is_arm8_machine_config_def, forge_mc_slot_def])
  \\ pop_assum mp_tac
  \\ simp [lab_to_targetProofTheory.mc_conf_ok_def, erase_mc_def, forge_mc_slot_def,
           arm8_target_exact_encoder_correct]
  \\ simp [arm8_target_exact_def]
QED

Theorem erase_mc_init_ok_slot:
  ∀cb_end bm_end fnames B ffi_if inst_if.
    mc_init_ok arm8_config arm8_backend_config
      (erase_mc B (forge_mc_slot cb_end bm_end fnames ffi_if inst_if))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ `mc_init_ok arm8_config arm8_backend_config (forge_mc_slot cb_end bm_end fnames ffi_if inst_if)` by (
       irule arm8_configProofTheory.arm8_init_ok
       \\ simp [arm8_configProofTheory.is_arm8_machine_config_def, forge_mc_slot_def])
  \\ pop_assum mp_tac
  \\ simp [backendProofTheory.mc_init_ok_def, erase_mc_def, forge_mc_slot_def,
           arm8_target_exact_def]
QED

Theorem byte_align_in_region[local]:
  ∀(bm_end:word64) (a:word64).
    bm_end && 7w = 0w ∧
    ((0x00480000w ≤₊ (a && 0xFFFFFFFFFFFFFFF8w) ∧ (a && 0xFFFFFFFFFFFFFFF8w) <₊ 0x00500000w) ∨
     (0x00460018w ≤₊ (a && 0xFFFFFFFFFFFFFFF8w) ∧ (a && 0xFFFFFFFFFFFFFFF8w) <₊ bm_end)) ⇒
    (0x00480000w ≤₊ a ∧ a <₊ 0x00500000w) ∨
    (0x00460018w ≤₊ a ∧ a <₊ bm_end)
Proof
  blastLib.BBLAST_TAC
QED

Theorem heap_bitmaps_disjoint[local]:
  ∀(bm_end:word64).
    bm_end ≤₊ 0x00470000w ⇒
    DISJOINT forge_heap_stack_region (forge_bitmaps_region_slot bm_end)
Proof
  simp [DISJOINT_DEF, EXTENSION, forge_heap_stack_region_def, forge_bitmaps_region_slot_def,
        FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def,
        wordsTheory.WORD_LO, wordsTheory.WORD_LS]
  \\ rpt strip_tac \\ decide_tac
QED

Theorem forge_slot_installed_exact:
  ∀shim_ws sn rn (code:word8 list) (data:num list) ffi_names ms0 ffi_if inst_if.
    shim_common_words_ok shim_ws ∧
    ffi_names = SOME [ExtCall sn; ExtCall rn] ∧
    forge_slot_loaded shim_ws code data ms0 ∧
    real_interfer_ok_slot (slot_cb_end (LENGTH code)) (slot_bm_buf_end (LENGTH data))
      (slot_cbspace (LENGTH code)) [ExtCall sn; ExtCall rn] (bits_of ms0) ffi_if inst_if ⇒
    let cb_begin = slot_cb_begin (LENGTH code) in
    let cb_end = slot_cb_end (LENGTH code) in
    let bm_end = slot_bm_buf_end (LENGTH data) in
    let cbsp = slot_cbspace (LENGTH code) in
    let ms1 = FUNPOW arm8$Next 43 ms0 in
    let emc = erase_mc (bits_of ms0)
                (forge_mc_slot cb_end bm_end [ExtCall sn; ExtCall rn] ffi_if inst_if) in
      det_run 43 ms0 ms1 ∧
      ms1.PC = FORGE_CAKE_MAIN ∧
      bits_of ms1 = bits_of ms0 ∧
      ms1.SP_EL0 = ms0.SP_EL0 ∧
      sp_ok ms1 ∧
      arm8_ok (erase ms1) ∧
      shim_loaded_slot shim_ws cb_begin cb_end bm_end ms1.MEM ∧
      installed code cbsp data 0 ffi_names (1, 3) emc [] (erase ms1)
Proof
  rpt strip_tac
  \\ simp [LET_THM]
  \\ qabbrev_tac `cb_begin = slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ qabbrev_tac `cbsp = slot_cbspace (LENGTH code)`
  \\ fs [forge_slot_loaded_def, LET_THM]
  \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac slot_params_props
  \\ impl_tac >- simp []
  \\ simp [LET_THM] \\ strip_tac
  \\ qspecl_then [`shim_ws`, `cb_begin`, `cb_end`, `bm_end`, `ms0`] mp_tac startup_to_cake_main_slot
  \\ impl_tac >- simp []
  \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ qabbrev_tac `B = bits_of ms0`
  \\ qabbrev_tac `emc = erase_mc B (forge_mc_slot cb_end bm_end [ExtCall sn; ExtCall rn] ffi_if inst_if)`
  \\ simp [targetSemTheory.installed_def]
  \\ qexists_tac `<| regs := λr. ms1.REG (n2w r);
                     fp_regs := K 0w;
                     mem := ms1.MEM;
                     mem_domain := forge_prog_addresses_slot cb_end bm_end;
                     pc := FORGE_CAKE_MAIN;
                     lr := 30;
                     align := 2;
                     be := F;
                     failed := F |>`
  \\ qexists_tac `λa. Word (mem_dword ms1.MEM (byte_align a))`
  \\ qexists_tac `FORGE_CAKE_BITMAPS`
  \\ qexists_tac `forge_bitmaps_region_slot bm_end`
  \\ qexists_tac `∅`
  \\ simp [LET_THM]
  \\ `{w | FORGE_HEAP ≤₊ w ∧ w <₊ FORGE_STACKEND} = forge_heap_stack_region` by
       simp [forge_heap_stack_region_def]
  \\ pop_assum SUBST1_TAC
  \\ `LENGTH code ≤ 261968 ∧ LENGTH data ≤ 8189` by
       fs [FORGE_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
  \\ `read_bytearray FORGE_CAKE_MAIN (LENGTH code)
        (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (ms1.MEM a) else NONE) = SOME code` by (
       `read_bytearray FORGE_CAKE_MAIN (LENGTH code)
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (ms1.MEM a) else NONE) =
        read_bytearray FORGE_CAKE_MAIN (LENGTH code)
          (λa. if a ∈ forge_prog_addresses_slot cb_end bm_end then SOME (ms0.MEM a) else NONE)` by (
         irule read_bytearray_cong \\ rpt strip_tac \\ fs []
         \\ qmatch_goalsub_abbrev_tac `ms1.MEM ad`
         \\ `ad ∉ forge_cml_ptrs_region ∧ ad ∉ forge_heap_hdr_region` by (
              `0x004000B0 + i < 18446744073709551616` by decide_tac
              \\ fs [Abbr `ad`, forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
                     FORGE_CAKE_MAIN_def, FORGE_CML_HEAP_def, FORGE_CAKE_BITMAPS_def, FORGE_HEAP_def,
                     word64_add_lo_ls]
              \\ decide_tac)
         \\ simp [])
       \\ simp [])
  \\ drule real_interfer_ok_slot_imp_erase_ok \\ strip_tac
  \\ rpt conj_tac
  >- (
    (* good_init_state *)
    simp [targetSemTheory.good_init_state_def, targetSemTheory.target_configured_def,
          targetSemTheory.code_loaded_def, asmPropsTheory.target_state_rel_def,
          Abbr `emc`, erase_mc_def, forge_mc_slot_def,
          arm8_target_exact_def, arm8_targetTheory.arm8_target_def,
          arm8_targetTheory.arm8_config_def, erase_fields]
    \\ rpt conj_tac
    >- (fs [sp_ok_def, bits_of_def, Abbr `B`])
    >- (mp_tac (Q.SPECL [`cb_begin`, `cb_end`, `bm_end`, `sn`, `rn`, `ffi_if`, `inst_if`] forge_mc_slot_start_pc_ok)
        \\ simp [targetSemTheory.start_pc_ok_def, forge_mc_slot_def])
    >- (simp [FORGE_CAKE_MAIN_def] \\ EVAL_TAC)
    >- (qpat_x_assum `interference_ok _ _` mp_tac
        \\ simp [erase_mc_def, forge_mc_slot_def, arm8_target_exact_def, arm8_targetTheory.arm8_target_def])
    >- (qpat_x_assum `ffi_interfer_ok _ _` mp_tac
        \\ simp [erase_mc_def, forge_mc_slot_def, arm8_target_exact_def,
                 arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- (qpat_x_assum `install_interfer_ok _ _ _` mp_tac
        \\ simp [erase_mc_def, forge_mc_slot_def, arm8_target_exact_def,
                 arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- (
      qpat_x_assum `read_bytearray _ _ (λa. if a ∈ _ then SOME (ms1.MEM a) else NONE) = SOME code`
        (mp_tac o MATCH_MP read_bytearray_mem_eq) \\ strip_tac
      \\ irule read_bytearray_imp_bytes_in_mem \\ rpt strip_tac \\ fs []
      \\ first_x_assum drule \\ strip_tac \\ simp []
      \\ `w2n (FORGE_CAKE_MAIN + n2w i) = 0x004000B0 + i` by
           (`0x004000B0 + i < 18446744073709551616` by decide_tac
            \\ simp [FORGE_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64])
      \\ fs [forge_heap_stack_region_def, forge_bitmaps_region_slot_def,
             FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def,
             wordsTheory.WORD_LO, wordsTheory.WORD_LS]
      \\ decide_tac)
    >- simp [forge_prog_addresses_slot_def, SUBSET_DEF]
    >- simp [forge_prog_addresses_slot_def, SUBSET_DEF]
    >- (
      `bm_end && 7w = 0w` by (
        qpat_assum `FORGE_CAKE_BITMAPS + n2w (8 * LENGTH data) = bm_end` (SUBST1_TAC o SYM)
        \\ REWRITE_TAC [FORGE_CAKE_BITMAPS_def, GSYM wordsTheory.word_mul_n2w]
        \\ blastLib.BBLAST_TAC)
      \\ rpt strip_tac
      \\ fs [forge_heap_stack_region_def, forge_bitmaps_region_slot_def,
             FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def, byte_align_64]
      \\ irule byte_align_in_region \\ simp [])
    >- (
      gen_tac
      \\ `byte_align (byte_align a) = byte_align a` by (simp [byte_align_64] \\ blastLib.BBLAST_TAC)
      \\ simp [GSYM mem_dword_get_byte])
    \\ gen_tac \\ strip_tac
    \\ qabbrev_tac `ad = FORGE_CAKE_MAIN + n2w (n + LENGTH code)`
    \\ `cbsp + (LENGTH code + 0x004000B0) = w2n cb_end` by (
         qpat_x_assum `cbsp + (LENGTH code + w2n FORGE_CAKE_MAIN) = w2n cb_end` mp_tac
         \\ PURE_REWRITE_TAC [FORGE_CAKE_MAIN_def]
         \\ CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV wordsLib.WORD_EVAL_CONV))
         \\ simp [])
    \\ `w2n ad = 0x004000B0 + (n + LENGTH code)` by (
         `0x004000B0 + (n + LENGTH code) < 18446744073709551616` by decide_tac
         \\ simp [Abbr `ad`, FORGE_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64])
    \\ simp [forge_prog_addresses_slot_def, forge_code_region_slot_def, forge_heap_stack_region_def,
             forge_bitmaps_region_slot_def, FORGE_CAKE_MAIN_def, FORGE_HEAP_def, FORGE_STACKEND_def,
             FORGE_CAKE_BITMAPS_def, wordsTheory.WORD_LO, wordsTheory.WORD_LS, dimword_64]
    \\ decide_tac)
  >- (simp [FORGE_HEAP_def, byte_aligned_mod8])
  >- (simp [FORGE_STACKEND_def, byte_aligned_mod8])
  >- (simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8])
  >- (simp [FORGE_HEAP_def, FORGE_STACKEND_def] \\ EVAL_TAC)
  >- (simp [FORGE_HEAP_def, FORGE_STACKEND_def, bytes_in_word_64] \\ EVAL_TAC)
  >- (
    irule heap_bitmaps_disjoint
    \\ qpat_x_assum `slot_layout_ok _ _ _` mp_tac
    \\ simp [slot_layout_ok_def, FORGE_DATA_SLOT_END_def])
  >- (
    `byte_align FORGE_HEAP = FORGE_HEAP` by (simp [FORGE_HEAP_def, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    `byte_align (FORGE_HEAP + bytes_in_word) = FORGE_HEAP + 8w` by
      (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    `byte_align (FORGE_HEAP + 2w * bytes_in_word) = FORGE_HEAP + 16w` by
      (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    simp [Abbr `emc`, erase_mc_def, forge_mc_slot_def, arm8_target_exact_def,
          arm8_targetTheory.arm8_target_def, erase_fields]
    \\ `byte_align (FORGE_HEAP + 3w * bytes_in_word) = FORGE_HEAP + 24w` by
      (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    simp [Abbr `emc`, erase_mc_def, forge_mc_slot_def, arm8_target_exact_def,
          arm8_targetTheory.arm8_target_def, erase_fields]
    \\ `byte_align (FORGE_HEAP + 4w * bytes_in_word) = FORGE_HEAP + 32w` by
         (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    (* word_list for bitmaps *)
    simp [word_list_exists_0, set_sepTheory.SEP_CLAUSES]
    \\ `forge_bitmaps_region_slot bm_end =
          {a | FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ FORGE_CAKE_BITMAPS + n2w (8 * LENGTH (MAP ((Word : word64 -> 64 word_loc) o n2w) data))}` by (
         simp [forge_bitmaps_region_slot_def])
    \\ pop_assum SUBST1_TAC
    \\ irule word_list_slice
    \\ rpt conj_tac
    >- (
      rpt strip_tac \\ fs []
      \\ simp [EL_MAP]
      \\ `byte_align (FORGE_CAKE_BITMAPS + n2w (8 * i)) = FORGE_CAKE_BITMAPS + n2w (8 * i)` by (
           `byte_aligned (FORGE_CAKE_BITMAPS + n2w (8 * i))` by (
             `0x00460018 + 8 * i < 18446744073709551616` by decide_tac
             \\ simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8, wordsTheory.word_add_n2w, w2n_n2w_64]
             \\ `0x00460018 + 8 * i = (573443 + i) * 8` by decide_tac
             \\ pop_assum SUBST1_TAC \\ simp [])
           \\ fs [alignmentTheory.byte_aligned_def, alignmentTheory.aligned_def,
                  alignmentTheory.byte_align_def])
      \\ simp []
      \\ `mem_dword ms1.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) =
          mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i))` by (
           irule mem_dword_cong_util \\ rpt strip_tac \\ first_x_assum irule
           \\ `0x00460018 + (8 * i + j) < 18446744073709551616` by decide_tac
           \\ fs [forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
                  FORGE_CAKE_BITMAPS_def, FORGE_CML_HEAP_def, FORGE_HEAP_def,
                  word_add_n2w_n2w, word64_add_lo_ls]
           \\ decide_tac)
      \\ simp [])
    >- simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8]
    \\ simp [FORGE_CAKE_BITMAPS_def, dimword_64] \\ decide_tac)
  >- simp [Abbr `emc`, erase_mc_def, forge_mc_slot_def]
  \\ gen_tac \\ strip_tac
  \\ `i = 2` by (
       qpat_x_assum `mmio_pcs_min_index _ = SOME i` mp_tac
       \\ mp_tac (Q.SPECL [`cb_end`, `bm_end`, `sn`, `rn`, `ffi_if`, `inst_if`] forge_mc_slot_mmio_min)
       \\ simp [Abbr `emc`, erase_mc_def])
  \\ rveq
  \\ simp [Abbr `emc`, erase_mc_def, forge_mc_slot_def, FORGE_CAKE_MAIN_def,
           lab_to_targetTheory.ffi_offset_def, dimword_64]
QED

Theorem forge_slot_nonvacuous:
  ∀shim_ws (code:word8 list) (data:num list).
    LENGTH shim_ws = 80 ∧
    0 < LENGTH code ∧ LENGTH code ≤ FORGE_MAX_CODE_BYTES ∧
    LENGTH data ≤ FORGE_MAX_BITMAP_WORDS ⇒
    ∃ms0:arm8_state.
      forge_slot_loaded shim_ws code data ms0 ∧
      ms0.TCR_EL1.TBI0 ∧
      ¬ms0.TCR_EL1.TBI1 ∧
      ms0.SCTLR_EL1.SA0 ∧
      aligned 4 ms0.SP_EL0
Proof
  rpt strip_tac
  \\ qabbrev_tac `cb_begin = slot_cb_begin (LENGTH code)`
  \\ qabbrev_tac `cb_end = slot_cb_end (LENGTH code)`
  \\ qabbrev_tac `bm_end = slot_bm_buf_end (LENGTH data)`
  \\ qspecl_then [`LENGTH code`, `LENGTH data`] mp_tac slot_params_props
  \\ impl_tac >- simp []
  \\ simp [LET_THM] \\ strip_tac
  \\ `LENGTH code ≤ 261968 ∧ LENGTH data ≤ 8189` by
       fs [FORGE_MAX_CODE_BYTES_def, FORGE_MAX_BITMAP_WORDS_def]
  \\ qabbrev_tac `m0 = λa:word64.
       if FORGE_CAKE_MAIN ≤₊ a ∧ a <₊ cb_begin then
         EL (w2n (a - FORGE_CAKE_MAIN)) code
       else if FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ bm_end then
         let off = w2n (a - FORGE_CAKE_BITMAPS) in
         let w : word64 = n2w (EL (off DIV 8) data) in
           if off MOD 8 = 0 then (7 >< 0) w
           else if off MOD 8 = 1 then (15 >< 8) w
           else if off MOD 8 = 2 then (23 >< 16) w
           else if off MOD 8 = 3 then (31 >< 24) w
           else if off MOD 8 = 4 then (39 >< 32) w
           else if off MOD 8 = 5 then (47 >< 40) w
           else if off MOD 8 = 6 then (55 >< 48) w
           else (63 >< 56) w
       else if FORGE_VENEERS_BASE ≤₊ a ∧ a <₊ FORGE_CAKE_MAIN then
         let off = w2n (a - FORGE_VENEERS_BASE) in
         let w = EL (off DIV 4) (forge_slot_veneers cb_begin cb_end bm_end) in
           if off MOD 4 = 0 then (7 >< 0) w
           else if off MOD 4 = 1 then (15 >< 8) w
           else if off MOD 4 = 2 then (23 >< 16) w
           else (31 >< 24) w
       else if FORGE_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_SHIM_END then
         let off = w2n (a - FORGE_SHIM_BASE) in
         let w = EL (off DIV 4) shim_ws in
           if off MOD 4 = 0 then (7 >< 0) w
           else if off MOD 4 = 1 then (15 >< 8) w
           else if off MOD 4 = 2 then (23 >< 16) w
           else (31 >< 24) w
       else 0w`
  \\ qexists_tac `(ARB:arm8_state) with
       <| PSTATE    := ((ARB:ProcState) with EL := 0w);
          SCTLR_EL1 := ((ARB:SCTLRType) with <| SA0 := T; E0E := F |>);
          TCR_EL1   := ((ARB:TCR_EL1) with <| TBI0 := T; TBI1 := F |>);
          SP_EL0    := FORGE_STACKEND;
          exception := NoException;
          PC        := FORGE_SHIM_BASE;
          MEM       := m0 |>`
  \\ simp [forge_slot_loaded_def, LET_THM, arm8_ok_erase, sp_ok_def]
  \\ rpt conj_tac
  >- (simp [FORGE_SHIM_BASE_def] \\ EVAL_TAC)
  >- (simp [FORGE_STACKEND_def] \\ EVAL_TAC)
  >- (
    simp [shim_loaded_slot_def]
    \\ `LENGTH (forge_slot_veneers cb_begin cb_end bm_end) = 44` by simp [forge_slot_veneers_def]
    \\ conj_tac
    >- (
      irule words32_in_mem_pointwise \\ rpt strip_tac \\ fs []
      \\ `∀j. j < 4 ⇒
            (FORGE_VENEERS_BASE + n2w (4 * i + j)) <₊ FORGE_CAKE_MAIN ∧
            FORGE_VENEERS_BASE ≤₊ (FORGE_VENEERS_BASE + n2w (4 * i + j)) ∧
            ¬(FORGE_CAKE_MAIN ≤₊ (FORGE_VENEERS_BASE + n2w (4 * i + j))) ∧
            ¬(FORGE_CAKE_BITMAPS ≤₊ (FORGE_VENEERS_BASE + n2w (4 * i + j))) ∧
            w2n ((FORGE_VENEERS_BASE + n2w (4 * i + j)) - FORGE_VENEERS_BASE) = 4 * i + j` by (
           rpt strip_tac
           \\ `0x00400000 + (4 * i + j) < 18446744073709551616 ∧ 4 * i + j < 18446744073709551616` by decide_tac
           \\ fs [wordsTheory.WORD_ADD_SUB2, w2n_n2w_64]
           \\ fs [FORGE_VENEERS_BASE_def, FORGE_CAKE_MAIN_def, FORGE_CAKE_BITMAPS_def, word64_add_lo_ls]
           \\ decide_tac)
      \\ rpt conj_tac
      \\ (simp [Abbr `m0`]
          \\ first_x_assum (fn th =>
               mp_tac (Q.SPEC `0` th) \\ mp_tac (Q.SPEC `1` th) \\
               mp_tac (Q.SPEC `2` th) \\ mp_tac (Q.SPEC `3` th))
          \\ simp [div_mod_4]))
    \\ irule words32_in_mem_pointwise \\ rpt strip_tac \\ fs []
    \\ `∀j. j < 4 ⇒
          FORGE_SHIM_BASE ≤₊ (FORGE_SHIM_BASE + n2w (4 * i + j)) ∧
          (FORGE_SHIM_BASE + n2w (4 * i + j)) <₊ FORGE_SHIM_END ∧
          ¬((FORGE_SHIM_BASE + n2w (4 * i + j)) <₊ cb_begin) ∧
          ¬(FORGE_CAKE_BITMAPS ≤₊ (FORGE_SHIM_BASE + n2w (4 * i + j))) ∧
          ¬((FORGE_SHIM_BASE + n2w (4 * i + j)) <₊ FORGE_CAKE_MAIN) ∧
          w2n ((FORGE_SHIM_BASE + n2w (4 * i + j)) - FORGE_SHIM_BASE) = 4 * i + j` by (
         rpt strip_tac
         \\ `0x00450000 + (4 * i + j) < 18446744073709551616 ∧ 4 * i + j < 18446744073709551616` by decide_tac
         \\ `w2n (FORGE_SHIM_BASE + n2w (4 * i + j)) = 0x00450000 + (4 * i + j)` by
              simp [FORGE_SHIM_BASE_def, wordsTheory.word_add_n2w, w2n_n2w_64]
         \\ fs [wordsTheory.WORD_ADD_SUB2, w2n_n2w_64, wordsTheory.WORD_LO, wordsTheory.WORD_LS,
                FORGE_SHIM_BASE_def, FORGE_SHIM_END_def, FORGE_CAKE_MAIN_def, FORGE_CAKE_BITMAPS_def]
         \\ decide_tac)
    \\ rpt conj_tac
    \\ (simp [Abbr `m0`]
        \\ first_x_assum (fn th =>
             mp_tac (Q.SPEC `0` th) \\ mp_tac (Q.SPEC `1` th) \\
             mp_tac (Q.SPEC `2` th) \\ mp_tac (Q.SPEC `3` th))
        \\ simp [div_mod_4]))
  >- (
    irule read_bytearray_pointwise \\ gen_tac \\ strip_tac \\ fs []
    \\ `0x004000B0 + i < 18446744073709551616 ∧ i < 18446744073709551616` by decide_tac
    \\ `w2n (FORGE_CAKE_MAIN + n2w i) = 0x004000B0 + i` by
         simp [FORGE_CAKE_MAIN_def, wordsTheory.word_add_n2w, w2n_n2w_64]
    \\ conj_tac
    >- (
      fs [forge_prog_addresses_slot_def, forge_code_region_slot_def, FORGE_CAKE_MAIN_def,
          wordsTheory.WORD_LO, wordsTheory.WORD_LS]
      \\ decide_tac)
    \\ fs [Abbr `m0`, wordsTheory.WORD_ADD_SUB2, w2n_n2w_64, wordsTheory.WORD_LO, wordsTheory.WORD_LS,
           FORGE_CAKE_MAIN_def]
    \\ decide_tac)
  >- (
    rpt strip_tac \\ fs []
    \\ irule dword_bytes_reassemble
    \\ `∀j. j < 8 ⇒
          FORGE_CAKE_BITMAPS ≤₊ (FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) ∧
          (FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) <₊ bm_end ∧
          ¬((FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) <₊ cb_begin) ∧
          w2n ((FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) - FORGE_CAKE_BITMAPS) = 8 * i + j` by (
         gen_tac \\ strip_tac
         \\ `0x00460018 + (8 * i + j) < 18446744073709551616 ∧ 8 * i + j < 18446744073709551616` by decide_tac
         \\ qabbrev_tac `ad = FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j`
         \\ `w2n ad = 0x00460018 + (8 * i + j)` by
              simp [Abbr `ad`, word_add_n2w_n2w, FORGE_CAKE_BITMAPS_def, wordsTheory.word_add_n2w, w2n_n2w_64]
         \\ `w2n (ad - FORGE_CAKE_BITMAPS) = 8 * i + j` by
              simp [Abbr `ad`, word_add_n2w_n2w, wordsTheory.WORD_ADD_SUB2, w2n_n2w_64]
         \\ `8 * LENGTH data + 0x00460018 = w2n bm_end` by (
              qpat_x_assum `8 * LENGTH data + w2n FORGE_CAKE_BITMAPS = w2n bm_end` mp_tac
              \\ PURE_REWRITE_TAC [FORGE_CAKE_BITMAPS_def]
              \\ CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV wordsLib.WORD_EVAL_CONV)) \\ simp [])
         \\ `LENGTH code + 0x004000B0 = w2n cb_begin` by (
              qpat_x_assum `LENGTH code + w2n FORGE_CAKE_MAIN = w2n cb_begin` mp_tac
              \\ PURE_REWRITE_TAC [FORGE_CAKE_MAIN_def]
              \\ CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV wordsLib.WORD_EVAL_CONV)) \\ simp [])
         \\ simp [wordsTheory.WORD_LO, wordsTheory.WORD_LS, FORGE_CAKE_BITMAPS_def, dimword_64]
         \\ decide_tac)
    \\ `FORGE_CAKE_BITMAPS ≤₊ (FORGE_CAKE_BITMAPS + n2w (8 * i)) ∧
        (FORGE_CAKE_BITMAPS + n2w (8 * i)) <₊ bm_end ∧
        ¬((FORGE_CAKE_BITMAPS + n2w (8 * i)) <₊ cb_begin) ∧
        w2n ((FORGE_CAKE_BITMAPS + n2w (8 * i)) - FORGE_CAKE_BITMAPS) = 8 * i` by (
         first_x_assum (qspec_then `0` mp_tac) \\ simp [])
    \\ rpt conj_tac
    \\ (simp [Abbr `m0`]
        \\ first_x_assum (fn th =>
             EVERY (map (fn k => mp_tac (Q.SPEC k th)) [`1`, `2`, `3`, `4`, `5`, `6`, `7`]))
        \\ simp [div_mod_8]))
  \\ simp [FORGE_STACKEND_def] \\ EVAL_TAC
QED
