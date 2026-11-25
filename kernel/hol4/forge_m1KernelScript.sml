(*
  Forge Milestone 1: Top-Level End-to-End Verified ARM64 Counter Kernel Theorem.

  Composes:
    1. Pure counter spec & conservation invariants (forge_counterSpec)
    2. Zero-Basis CakeML program & CF verification (forge_counterProg)
    3. In-logic ARM64 CakeML backend compilation (forge_counterCompile)
    4. Real ARMv8 processor-bit erasure lift for TBI0/TBI1/SA0 (forge_arm8Erasure)
    5. Verified 43-step ELF startup, Linux read(63)/write(64)/exit_group(94) shim,
       and full targetSem machine-config discharge (forge_shimProof)
    6. CakeML backendProof$compile_correct for arm8_config
    7. Non-vacuity witness lemma (forge_m1_nonvacuous) exhibiting a concrete
       Linux EL0 CPU and memory state satisfying forge_elf_loaded code data ms0.
*)
Theory forge_m1Kernel
Ancestors
  forge_counterSpec forge_counterProg forge_counterCompile
  forge_arm8Erasure forge_shimProof
  arm8_target arm8_configProof backendProof ml_prog targetProps semanticsProps
  alignment set_sep byte
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

Theorem compile_imp_ffi_names[local]:
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

Theorem forge_ffis_eval =
  forge_counterCompileTheory.ffis_def |> CONV_RULE (RAND_CONV EVAL);

Theorem forge_ffi_names_eq:
  info.lab_conf.ffi_names = SOME forge_mc.ffi_names
Proof
  mp_tac counter_compiled \\ strip_tac
  \\ drule (REWRITE_RULE [GSYM AND_IMP_INTRO] compile_imp_ffi_names)
  \\ disch_then (qspec_then `ffis` mp_tac)
  \\ simp [forge_mc_def, backendTheory.set_oracle_def, arm8_configTheory.arm8_backend_config_def]
  \\ `ffinames_to_string_list (the [] info.lab_conf.ffi_names) = [«send16»; «recv16»]` by
       metis_tac [forge_ffis_eval]
  \\ simp []
QED

(* ---- 2. Byte-Level Memory, Alignment & Bitmap Helpers ---- *)

Theorem log2_8[local]:
  LOG2 8 = 3
Proof
  EVAL_TAC
QED

Theorem bytes_in_word_64[local]:
  (bytes_in_word : word64) = 8w
Proof
  EVAL_TAC
QED

Theorem word_add_1w_n2w[local]:
  ∀(a:word64) i. a + 1w + n2w i = a + n2w (SUC i)
Proof
  rpt gen_tac
  \\ REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w, arithmeticTheory.ADD1]
  \\ simp []
QED

Theorem word_add_n2w_n2w[local]:
  ∀(a:word64) m n. a + n2w m + n2w n = a + n2w (m + n)
Proof
  rpt gen_tac
  \\ REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w]
QED

Theorem byte_align_64[local]:
  ∀a:word64. byte_align a = a && 0xFFFFFFFFFFFFFFF8w
Proof
  gen_tac \\ simp [alignmentTheory.byte_align_def, alignmentTheory.align_def, log2_8]
  \\ blastLib.BBLAST_TAC
QED

Theorem byte_aligned_mod8[local]:
  ∀a:word64. byte_aligned a ⇔ w2n a MOD 8 = 0
Proof
  gen_tac \\ simp [alignmentTheory.byte_aligned_def, log2_8, alignmentTheory.aligned_w2n]
QED

Theorem mem_dword_get_byte[local]:
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

Theorem read_bytearray_cong[local]:
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

Theorem read_bytearray_imp_bytes_in_mem[local]:
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

Theorem word_list_slice[local]:
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

Theorem w2n_n2w_64[local]:
  ∀n. n < 18446744073709551616 ⇒ w2n (n2w n : word64) = n
Proof
  simp [wordsTheory.w2n_n2w, dimword_64]
QED

Theorem mem_dword_cong[local]:
  ∀m1 m2 (a:word64).
    (∀j. j < 8 ⇒ m1 (a + n2w j) = m2 (a + n2w j)) ⇒
    mem_dword m1 a = mem_dword m2 a
Proof
  rpt strip_tac
  \\ first_x_assum (fn th =>
       EVERY (map (fn k => mp_tac (Q.SPEC k th)) [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`]))
  \\ simp [] \\ rpt strip_tac \\ simp [arm8_stepTheory.mem_dword_def]
QED

Theorem word64_add_lo_ls[local]:
  ∀a b c:num. a + b < 18446744073709551616 ∧ c < 18446744073709551616 ⇒
    ((n2w a + n2w b : word64) <₊ n2w c ⇔ a + b < c) ∧
    ((n2w a + n2w b : word64) ≤₊ n2w c ⇔ a + b ≤ c) ∧
    (n2w c ≤₊ (n2w a + n2w b : word64) ⇔ c ≤ a + b) ∧
    (n2w c <₊ (n2w a + n2w b : word64) ⇔ c < a + b)
Proof
  rpt strip_tac \\ simp [wordsTheory.word_add_n2w, wordsTheory.WORD_LO, wordsTheory.WORD_LS, w2n_n2w_64]
QED

Theorem div_mod_4[local]:
  ∀i j. j < 4 ⇒ (4 * i + j) DIV 4 = i ∧ (4 * i + j) MOD 4 = j
Proof
  rpt strip_tac
  \\ `4 * i = i * 4` by metis_tac [arithmeticTheory.MULT_COMM]
  \\ pop_assum SUBST1_TAC
  \\ simp [arithmeticTheory.DIV_MULT, arithmeticTheory.MOD_MULT]
QED

Theorem div_mod_8[local]:
  ∀i j. j < 8 ⇒ (8 * i + j) DIV 8 = i ∧ (8 * i + j) MOD 8 = j
Proof
  rpt strip_tac
  \\ `8 * i = i * 8` by metis_tac [arithmeticTheory.MULT_COMM]
  \\ pop_assum SUBST1_TAC
  \\ simp [arithmeticTheory.DIV_MULT, arithmeticTheory.MOD_MULT]
QED

(* ---- 3. ELF Initial State & Verified Installation into CakeML targetSem ---- *)

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

Theorem mmio_min_idx_forge[local]:
  mmio_pcs_min_index forge_mc.ffi_names = SOME 2
Proof
  simp [forge_mc_def, targetSemTheory.mmio_pcs_min_index_def]
  \\ DEEP_INTRO_TAC optionTheory.some_intro
  \\ conj_tac
  >- (rpt strip_tac \\ `x = 2` suffices_by simp []
      \\ CCONTR_TAC \\ `x < 2` by decide_tac
      \\ first_x_assum (qspec_then `x` mp_tac) \\ simp []
      \\ `x = 0 ∨ x = 1` by decide_tac \\ rveq \\ simp [])
  \\ simp [] \\ qexists_tac `2` \\ simp []
  \\ gen_tac \\ Cases_on `j` \\ simp [] \\ Cases_on `n` \\ simp []
QED

Theorem forge_installed:
  ∀ms0.
    forge_elf_loaded code data ms0 ⇒
    let ms1 = FUNPOW arm8$Next 43 ms0 in
      ms1.PC = FORGE_CAKE_MAIN ∧
      bits_of ms1 = bits_of ms0 ∧
      ms1.SP_EL0 = ms0.SP_EL0 ∧
      sp_ok ms1 ∧
      shim_loaded ms1.MEM ∧
      installed code FORGE_CBSPACE data 0 info.lab_conf.ffi_names
        (1, 3) forge_mc [] (erase ms1)
Proof
  rpt strip_tac
  \\ fs [forge_elf_loaded_def]
  \\ mp_tac counter_compiled \\ strip_tac
  \\ qspec_then `ms0` mp_tac startup_to_cake_main \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ simp [targetSemTheory.installed_def]
  \\ qexists_tac `<| regs := λr. ms1.REG (n2w r);
                     fp_regs := K 0w;
                     mem := ms1.MEM;
                     mem_domain := forge_prog_addresses;
                     pc := FORGE_CAKE_MAIN;
                     lr := 30;
                     align := 2;
                     be := F;
                     failed := F |>`
  \\ qexists_tac `λa. Word (mem_dword ms1.MEM (byte_align a))`
  \\ qexists_tac `FORGE_CAKE_BITMAPS`
  \\ qexists_tac `forge_bitmaps_region`
  \\ qexists_tac `∅`
  \\ simp [LET_THM]
  \\ `{w | FORGE_HEAP ≤₊ w ∧ w <₊ FORGE_STACKEND} = forge_heap_stack_region` by
       simp [forge_heap_stack_region_def]
  \\ pop_assum SUBST1_TAC
  \\ `read_bytearray FORGE_CAKE_MAIN (LENGTH code)
        (λa. if a ∈ forge_prog_addresses then SOME (ms1.MEM a) else NONE) = SOME code` by (
       `read_bytearray FORGE_CAKE_MAIN (LENGTH code)
          (λa. if a ∈ forge_prog_addresses then SOME (ms1.MEM a) else NONE) =
        read_bytearray FORGE_CAKE_MAIN (LENGTH code)
          (λa. if a ∈ forge_prog_addresses then SOME (ms0.MEM a) else NONE)` by (
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
  \\ rpt conj_tac
  >- (
    (* good_init_state *)
    simp [targetSemTheory.good_init_state_def, targetSemTheory.target_configured_def,
          targetSemTheory.code_loaded_def, asmPropsTheory.target_state_rel_def,
          forge_mc_def, arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def,
          erase_fields]
    \\ rpt conj_tac
    >- (mp_tac forge_mc_start_pc_ok
        \\ simp [forge_mc_def, arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- (simp [FORGE_CAKE_MAIN_def] \\ EVAL_TAC)
    >- (mp_tac forge_mc_interference_ok \\ simp [forge_mc_def, arm8_targetTheory.arm8_target_def])
    >- (mp_tac forge_mc_ffi_interfer_ok
        \\ simp [forge_mc_def, arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- (mp_tac forge_mc_install_interfer_ok
        \\ simp [forge_mc_def, arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- rfs []
    >- (
      qpat_x_assum `read_bytearray _ _ (λa. if a ∈ _ then SOME (ms1.MEM a) else NONE) = SOME code`
        (mp_tac o MATCH_MP read_bytearray_mem_eq) \\ strip_tac
      \\ irule read_bytearray_imp_bytes_in_mem \\ rpt strip_tac \\ fs []
      \\ first_x_assum drule \\ strip_tac \\ simp []
      \\ `0x004000B0 + i < 18446744073709551616` by decide_tac
      \\ fs [forge_heap_stack_region_def, forge_bitmaps_region_def,
             FORGE_CAKE_MAIN_def, FORGE_HEAP_def, FORGE_STACKEND_def,
             FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def, word64_add_lo_ls]
      \\ decide_tac)
    >- simp [forge_prog_addresses_def, SUBSET_DEF]
    >- simp [forge_prog_addresses_def, SUBSET_DEF]
    >- (
      rpt strip_tac
      \\ fs [forge_heap_stack_region_def, forge_bitmaps_region_def,
             FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def,
             byte_align_64]
      \\ blastLib.FULL_BBLAST_TAC)
    >- (
      gen_tac
      \\ `byte_align (byte_align a) = byte_align a` by (simp [byte_align_64] \\ blastLib.BBLAST_TAC)
      \\ simp [GSYM mem_dword_get_byte])
    >- (
      rpt strip_tac \\ fs [FORGE_CBSPACE_def]
      \\ `0x004000B0 + (n + 74396) < 18446744073709551616` by decide_tac
      \\ fs [forge_prog_addresses_def, forge_code_region_def, forge_heap_stack_region_def,
             forge_bitmaps_region_def, FORGE_CAKE_MAIN_def, FORGE_CB_END_def,
             FORGE_CBSPACE_def, FORGE_HEAP_def, FORGE_STACKEND_def,
             FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def, word64_add_lo_ls]
      \\ decide_tac)
    \\ simp [FORGE_CBSPACE_def, dimword_64])
  >- (simp [FORGE_HEAP_def, byte_aligned_mod8])
  >- (simp [FORGE_STACKEND_def, byte_aligned_mod8])
  >- (simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8])
  >- (simp [FORGE_HEAP_def, FORGE_STACKEND_def] \\ EVAL_TAC)
  >- (simp [FORGE_HEAP_def, FORGE_STACKEND_def, bytes_in_word_64] \\ EVAL_TAC)
  >- (
    simp [DISJOINT_DEF, EXTENSION, forge_heap_stack_region_def, forge_bitmaps_region_def,
          FORGE_HEAP_def, FORGE_STACKEND_def, FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def]
    \\ gen_tac \\ blastLib.BBLAST_TAC)
  >- (
    `byte_align FORGE_HEAP = FORGE_HEAP` by (simp [FORGE_HEAP_def, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    `byte_align (FORGE_HEAP + bytes_in_word) = FORGE_HEAP + 8w ∧
     FORGE_CAKE_BITMAPS + 484w * bytes_in_word = FORGE_BM_BUF_END` by
      (simp [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def,
             bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    `byte_align (FORGE_HEAP + 2w * bytes_in_word) = FORGE_HEAP + 16w ∧
     FORGE_CAKE_BITMAPS + 484w * bytes_in_word = FORGE_BM_BUF_END` by
      (simp [FORGE_HEAP_def, FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def,
             bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    simp [forge_mc_def, arm8_targetTheory.arm8_target_def, erase_fields]
    \\ `byte_align (FORGE_HEAP + 3w * bytes_in_word) = FORGE_HEAP + 24w ∧
        FORGE_CAKE_MAIN + 0x1229Cw = FORGE_CB_BEGIN` by
      (simp [FORGE_HEAP_def, FORGE_CAKE_MAIN_def, FORGE_CB_BEGIN_def,
             bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    simp [forge_mc_def, arm8_targetTheory.arm8_target_def, erase_fields]
    \\ `byte_align (FORGE_HEAP + 4w * bytes_in_word) = FORGE_HEAP + 32w ∧
        FORGE_CAKE_MAIN + n2w FORGE_CBSPACE + 0x1229Cw = FORGE_CB_END` by
      (simp [FORGE_HEAP_def, FORGE_CAKE_MAIN_def, FORGE_CBSPACE_def, FORGE_CB_END_def,
             bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    (* word_list for bitmaps *)
    simp [word_list_exists_0, set_sepTheory.SEP_CLAUSES]
    \\ `forge_bitmaps_region =
          {a | FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ FORGE_CAKE_BITMAPS + n2w (8 * LENGTH (MAP ((Word : word64 -> 64 word_loc) o n2w) data))}` by (
         simp [forge_bitmaps_region_def, FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def]
         \\ `0x430018w + n2w (8 * 484) = (0x430F38w:word64)` by EVAL_TAC
         \\ simp [])
    \\ pop_assum SUBST1_TAC
    \\ irule word_list_slice
    \\ rpt conj_tac
    >- (
      rpt strip_tac \\ fs []
      \\ simp [EL_MAP]
      \\ `byte_align (FORGE_CAKE_BITMAPS + n2w (8 * i)) = FORGE_CAKE_BITMAPS + n2w (8 * i)` by (
           `byte_aligned (FORGE_CAKE_BITMAPS + n2w (8 * i))` by (
             `0x00430018 + 8 * i < 18446744073709551616` by decide_tac
             \\ simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8, wordsTheory.word_add_n2w, w2n_n2w_64]
             \\ `0x00430018 + 8 * i = (548867 + i) * 8` by decide_tac
             \\ pop_assum SUBST1_TAC \\ simp [])
           \\ fs [alignmentTheory.byte_aligned_def, alignmentTheory.aligned_def,
                  alignmentTheory.byte_align_def])
      \\ simp []
      \\ `mem_dword ms1.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i)) =
          mem_dword ms0.MEM (FORGE_CAKE_BITMAPS + n2w (8 * i))` by (
           irule mem_dword_cong \\ rpt strip_tac \\ first_x_assum irule
           \\ `0x00430018 + (8 * i + j) < 18446744073709551616` by decide_tac
           \\ fs [forge_cml_ptrs_region_def, forge_heap_hdr_region_def,
                  FORGE_CAKE_BITMAPS_def, FORGE_CML_HEAP_def, FORGE_HEAP_def,
                  word_add_n2w_n2w, word64_add_lo_ls]
           \\ decide_tac)
      \\ simp [])
    >- simp [FORGE_CAKE_BITMAPS_def, byte_aligned_mod8]
    \\ simp [FORGE_CAKE_BITMAPS_def, dimword_64])
  >- simp [forge_ffi_names_eq]
  \\ rpt strip_tac \\ fs [mmio_min_idx_forge] \\ rveq
  \\ simp [forge_mc_def, FORGE_CBSPACE_def, lab_to_targetTheory.ffi_offset_def, dimword_64]
QED

(* ---- 4. Top-Level End-to-End Real-Bits ARM64 Kernel Correctness Theorem ---- *)

Theorem forge_m1_kernel_correct:
  ∀ms0 io.
    forge_elf_loaded code data ms0 ∧ io.outputs = [] ⇒
    let ms1 = FUNPOW arm8$Next 43 ms0 in
    let rmc = real_mc (bits_of ms0) forge_mc in
      rmc.target = arm8_target_real (bits_of ms0) ∧
      ms1.PC = FORGE_CAKE_MAIN ∧
      bits_of ms1 = bits_of ms0 ∧
      sp_ok ms1 ∧
      shim_loaded ms1.MEM ∧
      (∀b. b ≠ Fail ∧ machine_sem rmc (counter_ffi io) ms1 b ⇒
        (∃io_events.
           b = Terminate Success io_events ∧
           sent_frames_of io_events = SND (SND (counter_run 0w 0w io.inputs))) ∨
        (∃io_events.
           b = Terminate Resource_limit_hit io_events ∧
           sent_frames_of io_events ≼ SND (SND (counter_run 0w 0w io.inputs)))) ∧
      (∀s. arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧ s.PC = FORGE_EXIT_VENEER ⇒
        ∃k. let s1 = FUNPOW arm8$Next k s in
              s1.PC = 0x421128w ∧
              svc_exit_group_rel (if s.REG 0w = 0w then 0w else 1w) s1 ∧
              s1.MEM = s.MEM ∧ bits_of s1 = bits_of s ∧ s1.SP_EL0 = s.SP_EL0) ∧
      (∀s index bytes2 new_bytes io1 io2.
        arm8_ok (erase s) ∧ sp_ok s ∧ shim_loaded s.MEM ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w) ∧
        index < 2 ∧ s.PC = EL index forge_mc.ffi_entry_pcs ∧
        read_bytearray (s.REG 2w) (w2n (s.REG 3w))
          (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
        counter_ffi_oracle (EL index forge_mc.ffi_names) io1 [] bytes2 = Oracle_return io2 new_bytes ⇒
        ∃s'. shim_ffi_realized index new_bytes s s') ∧
      (∀inp out s inp' out' s'.
        shim_step (inp, out, s) (inp', out', s') ⇔
          (¬is_svc0_at s ∧ NextStateARM8 s = SOME s' ∧ inp' = inp ∧ out' = out) ∨
          (is_svc0_at s ∧ s.REG 8w = 63w ∧ svc_read_rel inp s s' inp' ∧ out' = out) ∨
          (is_svc0_at s ∧ s.REG 8w = 64w ∧ ∃chunk. svc_write_rel s s' chunk ∧ inp' = inp ∧ out' = out ++ chunk))
Proof
  rpt strip_tac
  \\ simp [LET_THM]
  \\ drule forge_installed \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ mp_tac counter_compiled \\ strip_tac
  \\ drule counter_semantics \\ strip_tac
  \\ `∀b. semantics_prog (init_state (counter_ffi io)) init_env counter_prog b ⇒
          ∃io_events. b = Terminate Success io_events ∧
                      sent_frames_of io_events = SND (SND (counter_run 0w 0w io.inputs))` by (
       fs [semanticsPropsTheory.sem_satisfies_def, ml_progTheory.semantics_dec_list_eq, IN_DEF])
  \\ `¬semantics_prog (init_state (counter_ffi io)) init_env counter_prog Fail` by (
       strip_tac \\ first_x_assum drule \\ simp [])
  \\ `heap_regs arm8_backend_config.stack_conf.reg_names = (1, 3)` by EVAL_TAC
  \\ `machine_sem forge_mc (counter_ffi io) (erase ms1) ⊆
      extend_with_resource_limit (semantics_prog (init_state (counter_ffi io)) init_env counter_prog)` by (
       mp_tac (MATCH_MP backendProofTheory.compile_correct (cj 1 counter_compiled)
               |> Q.GENL [`ffi`, `mc`, `cbspace`, `data_sp`, `ms`]
               |> Q.ISPECL [`counter_ffi io`, `forge_mc`, `FORGE_CBSPACE`, `0`, `erase ms1`])
       \\ simp [LET_THM, ml_progTheory.init_state_env_thm, backendProofTheory.set_oracle_simp,
                arm8_configProofTheory.arm8_backend_config_ok,
                arm8_configProofTheory.arm8_machine_config_ok,
                arm8_configProofTheory.arm8_init_ok,
                forge_mc_is_arm8])
  \\ `¬machine_sem forge_mc (counter_ffi io) (erase ms1) Fail` by (
       strip_tac
       \\ `Fail ∈ extend_with_resource_limit (semantics_prog (init_state (counter_ffi io)) init_env counter_prog)` by
            fs [SUBSET_DEF, IN_DEF]
       \\ drule semanticsPropsTheory.extend_with_resource_limit_not_fail
       \\ simp [IN_DEF])
  \\ rpt conj_tac
  >- simp [real_mc_def]
  >- (
    rpt strip_tac
    \\ `machine_sem forge_mc (counter_ffi io) (erase ms1) b` by (
         qspecl_then [`forge_mc`, `bits_of ms0`, `counter_ffi io`, `ms1`, `b`] mp_tac
           machine_sem_real_safety
         \\ impl_tac
         >- (
           `forge_mc.target = arm8_target ∧ forge_mc.mmio_info = []` by simp [forge_mc_def]
           \\ `interference_ok forge_mc.next_interfer (arm8_target.proj forge_mc.prog_addresses)` by
                (mp_tac forge_mc_interference_ok \\ simp [forge_mc_def])
           \\ `¬SND (SND (bits_of ms0)) ∨ aligned 4 ms1.SP_EL0` by (
                `bits_of ms0 = bits_of ms1` by simp []
                \\ pop_assum SUBST1_TAC
                \\ fs [sp_ok_def, bits_of_def])
           \\ simp [forge_mc_lo55, forge_mc_interfer_sp_bits_ok])
         \\ simp [])
    \\ `b ∈ extend_with_resource_limit (semantics_prog (init_state (counter_ffi io)) init_env counter_prog)` by
         fs [SUBSET_DEF, IN_DEF]
    \\ qpat_x_assum `b ∈ extend_with_resource_limit _` mp_tac
    \\ simp [semanticsPropsTheory.extend_with_resource_limit_def, IN_DEF]
    \\ rpt strip_tac
    >- (disj1_tac \\ first_x_assum drule \\ simp [])
    >- (
      disj2_tac
      \\ first_x_assum drule \\ strip_tac \\ fs []
      \\ qpat_x_assum `sent_frames_of _ = _` (SUBST1_TAC o SYM)
      \\ irule sent_frames_of_prefix \\ simp [IS_PREFIX_APPEND])
    \\ first_x_assum drule \\ simp [])
  >- (rpt strip_tac \\ drule_all cake_exit_to_svc_exit_group \\ simp [LET_THM])
  >- (rpt strip_tac \\ drule_all forge_ffi_always_realized \\ simp [])
  \\ simp [shim_step_def]
QED

(* ---- 5. Non-Vacuity Witness Lemma (Anti-False ==> P Proof Inside HOL4) ---- *)

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

Theorem forge_m1_nonvacuous:
  ∃ms0.
    forge_elf_loaded code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧ ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧ aligned 4 ms0.SP_EL0
Proof
  mp_tac counter_compiled \\ strip_tac
  \\ qabbrev_tac `m0 = λa:word64.
       if FORGE_CAKE_MAIN ≤₊ a ∧ a <₊ FORGE_CB_BEGIN then
         EL (w2n (a - FORGE_CAKE_MAIN)) code
       else if FORGE_CAKE_BITMAPS ≤₊ a ∧ a <₊ FORGE_BM_BUF_END then
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
         let w = EL (off DIV 4) forge_veneers_words in
           if off MOD 4 = 0 then (7 >< 0) w
           else if off MOD 4 = 1 then (15 >< 8) w
           else if off MOD 4 = 2 then (23 >< 16) w
           else (31 >< 24) w
       else if FORGE_SHIM_BASE ≤₊ a ∧ a <₊ FORGE_SHIM_END then
         let off = w2n (a - FORGE_SHIM_BASE) in
         let w = EL (off DIV 4) forge_shim_words in
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
  \\ simp [forge_elf_loaded_def, arm8_ok_erase, sp_ok_def]
  \\ rpt conj_tac
  >- (simp [FORGE_SHIM_BASE_def] \\ EVAL_TAC)
  >- (simp [FORGE_STACKEND_def] \\ EVAL_TAC)
  >- (
    simp [shim_loaded_def]
    \\ `LENGTH forge_veneers_words = 44 ∧ LENGTH forge_shim_words = 80` by
         simp [forge_veneers_words_def, forge_shim_words_def]
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
          ¬((FORGE_SHIM_BASE + n2w (4 * i + j)) <₊ FORGE_CB_BEGIN) ∧
          ¬(FORGE_CAKE_BITMAPS ≤₊ (FORGE_SHIM_BASE + n2w (4 * i + j))) ∧
          ¬((FORGE_SHIM_BASE + n2w (4 * i + j)) <₊ FORGE_CAKE_MAIN) ∧
          w2n ((FORGE_SHIM_BASE + n2w (4 * i + j)) - FORGE_SHIM_BASE) = 4 * i + j` by (
         rpt strip_tac
         \\ `0x00421000 + (4 * i + j) < 18446744073709551616 ∧ 4 * i + j < 18446744073709551616` by decide_tac
         \\ fs [wordsTheory.WORD_ADD_SUB2, w2n_n2w_64]
         \\ fs [FORGE_SHIM_BASE_def, FORGE_SHIM_END_def, FORGE_CB_BEGIN_def,
                FORGE_CAKE_BITMAPS_def, FORGE_CAKE_MAIN_def, word64_add_lo_ls]
         \\ decide_tac)
    \\ rpt conj_tac
    \\ (simp [Abbr `m0`]
        \\ first_x_assum (fn th =>
             mp_tac (Q.SPEC `0` th) \\ mp_tac (Q.SPEC `1` th) \\
             mp_tac (Q.SPEC `2` th) \\ mp_tac (Q.SPEC `3` th))
        \\ simp [div_mod_4]))
  >- (
    `74396 = LENGTH code` by simp [] \\ pop_assum SUBST1_TAC
    \\ irule read_bytearray_pointwise \\ gen_tac \\ strip_tac \\ fs []
    \\ `0x004000B0 + i < 18446744073709551616 ∧ i < 18446744073709551616` by decide_tac
    \\ conj_tac
    >- (
      fs [forge_prog_addresses_def, forge_code_region_def, FORGE_CAKE_MAIN_def, FORGE_CB_END_def,
          word64_add_lo_ls]
      \\ decide_tac)
    \\ fs [Abbr `m0`, wordsTheory.WORD_ADD_SUB2, w2n_n2w_64]
    \\ fs [FORGE_CAKE_MAIN_def, FORGE_CB_BEGIN_def, word64_add_lo_ls]
    \\ decide_tac)
  >- (
    rpt strip_tac \\ fs []
    \\ irule dword_bytes_reassemble
    \\ `∀j. j < 8 ⇒
          FORGE_CAKE_BITMAPS ≤₊ (FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) ∧
          (FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) <₊ FORGE_BM_BUF_END ∧
          ¬((FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) <₊ FORGE_CB_BEGIN) ∧
          w2n ((FORGE_CAKE_BITMAPS + n2w (8 * i) + n2w j) - FORGE_CAKE_BITMAPS) = 8 * i + j` by (
         rpt strip_tac
         \\ `0x00430018 + (8 * i + j) < 18446744073709551616 ∧ 8 * i + j < 18446744073709551616` by decide_tac
         \\ fs [word_add_n2w_n2w, wordsTheory.WORD_ADD_SUB2, w2n_n2w_64]
         \\ fs [FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def, FORGE_CB_BEGIN_def, word64_add_lo_ls]
         \\ decide_tac)
    \\ `FORGE_CAKE_BITMAPS ≤₊ (FORGE_CAKE_BITMAPS + n2w (8 * i)) ∧
        (FORGE_CAKE_BITMAPS + n2w (8 * i)) <₊ FORGE_BM_BUF_END ∧
        ¬((FORGE_CAKE_BITMAPS + n2w (8 * i)) <₊ FORGE_CB_BEGIN) ∧
        w2n ((FORGE_CAKE_BITMAPS + n2w (8 * i)) - FORGE_CAKE_BITMAPS) = 8 * i` by (
         first_x_assum (qspec_then `0` mp_tac) \\ simp [])
    \\ rpt conj_tac
    \\ (simp [Abbr `m0`]
        \\ first_x_assum (fn th =>
             EVERY (map (fn k => mp_tac (Q.SPEC k th)) [`1`, `2`, `3`, `4`, `5`, `6`, `7`]))
        \\ simp [div_mod_8]))
  \\ simp [FORGE_STACKEND_def] \\ EVAL_TAC
QED
