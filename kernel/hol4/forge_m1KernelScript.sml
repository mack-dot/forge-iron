(*
  Forge Milestone 1: Unified End-to-End Verified ARM64 Counter Kernel Theorem.

  Composes:
    1. Pure counter spec & conservation invariants (forge_counterSpec, SHA-256 pinned)
    2. Hardware/ELF/Linux svc #0 contract (forge_contractSpec, SHA-256 pinned)
    3. Zero-Basis CakeML program & CF total correctness (forge_counterProg)
    4. In-logic ARM64 CakeML backend compilation (forge_counterCompile)
    5. Exact arm8$Next encoder correctness, no-rogue-svc #0, and unconditional
       real-bits erasure equivalence (forge_arm8Erasure)
    6. 43-step ELF startup + universal Linux read(63)/write(64)/exit_group(94)
       syscall shim safety & liveness (forge_shimProof)
    7. CakeML backendProof$compile_correct for arm8_target_exact
    8. Non-vacuity witness lemma (forge_m1_nonvacuous) and exact Term.aconv-pinned
       unified whole-binary execution theorem (forge_m1_kernel_correct).
*)
Theory forge_m1Kernel
Ancestors
  forge_counterSpec forge_contractSpec forge_counterProg forge_counterCompile
  forge_arm8Erasure forge_shimProof
  arm8_target arm8_configProof lab_to_targetProof backendProof ml_prog
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
  ∀ffi_if inst_if.
    info.lab_conf.ffi_names = SOME (forge_mc_with ffi_if inst_if).ffi_names
Proof
  rpt gen_tac
  \\ mp_tac counter_compiled \\ strip_tac
  \\ drule (REWRITE_RULE [GSYM AND_IMP_INTRO] compile_imp_ffi_names)
  \\ disch_then (qspec_then `ffis` mp_tac)
  \\ simp [forge_mc_with_def, backendTheory.set_oracle_def, arm8_configTheory.arm8_backend_config_def]
  \\ `ffinames_to_string_list (the [] info.lab_conf.ffi_names) = [«send16»; «recv16»]` by
       metis_tac [forge_ffis_eval]
  \\ simp []
QED

(* ---- 2. Byte-Level Memory, Alignment, Bitmap & List Helpers ---- *)

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

Theorem limit_frames_prefix[local]:
  ∀wlim xs. limit_frames wlim xs ≼ xs
Proof
  Cases \\ simp [limit_frames_def]
  \\ metis_tac [IS_PREFIX_APPEND, listTheory.TAKE_DROP]
QED

Theorem stop_after_err_prefix[local]:
  ∀xs ys. xs ≼ ys ∧ stop_after_err ys ⇒ stop_after_err xs
Proof
  Induct \\ simp [stop_after_err_def]
  \\ rpt strip_tac
  \\ Cases_on `ys` \\ fs [stop_after_err_def]
  \\ rveq
  \\ Cases_on `event_is_err h` \\ fs [stop_after_err_def]
  \\ metis_tac []
QED

Theorem chunks16_split_tail[local]:
  ∀inp. ∃tail_bs. inp = FLAT (chunks16 inp) ++ tail_bs ∧ LENGTH tail_bs < 16
Proof
  ho_match_mp_tac chunks16_ind \\ rpt strip_tac
  \\ Cases_on `LENGTH inp < 16`
  >- (qexists_tac `inp` \\ simp [Once chunks16_def])
  \\ fs []
  \\ qexists_tac `tail_bs`
  \\ simp [Once chunks16_def]
  \\ `TAKE 16 inp ++ FLAT (chunks16 (DROP 16 inp)) ++ tail_bs = TAKE 16 inp ++ DROP 16 inp` by simp []
  \\ pop_assum SUBST1_TAC
  \\ simp [listTheory.TAKE_DROP]
QED

Theorem chunks16_drop_eq[local]:
  ∀r inp inp_cur.
    r ≤ LENGTH (chunks16 inp) ∧
    inp = FLAT (TAKE r (chunks16 inp)) ++ inp_cur ⇒
    chunks16 inp = TAKE r (chunks16 inp) ++ chunks16 inp_cur ∧
    DROP r (chunks16 inp) = chunks16 inp_cur
Proof
  Induct_on `r`
  >- (rpt strip_tac \\ gvs [])
  \\ rpt gen_tac \\ strip_tac
  \\ `¬(LENGTH inp < 16)` by
       (strip_tac \\ drule chunks16_lt16 \\ strip_tac \\ fs [])
  \\ `chunks16 inp = TAKE 16 inp :: chunks16 (DROP 16 inp)` by
       simp [Once chunks16_def]
  \\ `TAKE (SUC r) (chunks16 inp) = TAKE 16 inp :: TAKE r (chunks16 (DROP 16 inp))` by
       (pop_assum (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) \\ simp [])
  \\ `DROP 16 inp = FLAT (TAKE r (chunks16 (DROP 16 inp))) ++ inp_cur` by (
       `TAKE 16 inp ++ DROP 16 inp =
        TAKE 16 inp ++ (FLAT (TAKE r (chunks16 (DROP 16 inp))) ++ inp_cur)` by (
         REWRITE_TAC [listTheory.TAKE_DROP]
         \\ qpat_x_assum `inp = FLAT (TAKE (SUC r) _) ++ _`
              (fn th => CONV_TAC (LHS_CONV (REWR_CONV th)))
         \\ qpat_x_assum `TAKE (SUC r) _ = _`
              (fn th => CONV_TAC (LHS_CONV (LAND_CONV (RAND_CONV (REWR_CONV th)))))
         \\ simp [])
       \\ fs [])
  \\ `r ≤ LENGTH (chunks16 (DROP 16 inp))` by
       (qpat_x_assum `SUC r ≤ _` mp_tac
        \\ qpat_x_assum `chunks16 inp = _` (fn th => ONCE_REWRITE_TAC [th])
        \\ simp [])
  \\ first_x_assum (qspecl_then [`DROP 16 inp`, `inp_cur`] mp_tac)
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ conj_tac
  >- (qpat_x_assum `chunks16 inp = _` (fn th => CONV_TAC (LHS_CONV (REWR_CONV th)))
      \\ qpat_x_assum `TAKE (SUC r) _ = _` (fn th => CONV_TAC (RHS_CONV (LAND_CONV (REWR_CONV th))))
      \\ simp [])
  \\ qpat_x_assum `chunks16 inp = _` (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th))))
  \\ simp []
QED

Theorem chunks16_take_step[local]:
  ∀r inp inp_cur frame inp_after.
    r ≤ LENGTH (chunks16 inp) ∧
    inp = FLAT (TAKE r (chunks16 inp)) ++ inp_cur ∧
    LENGTH frame = 16 ∧ inp_cur = frame ++ inp_after ⇒
    r + 1 ≤ LENGTH (chunks16 inp) ∧
    TAKE (r + 1) (chunks16 inp) = TAKE r (chunks16 inp) ++ [frame] ∧
    inp = FLAT (TAKE (r + 1) (chunks16 inp)) ++ inp_after
Proof
  rpt gen_tac \\ strip_tac
  \\ drule_all chunks16_drop_eq \\ strip_tac
  \\ `chunks16 inp_cur = frame :: chunks16 inp_after` by simp [chunks16_cons]
  \\ `chunks16 inp = TAKE r (chunks16 inp) ++ (frame :: chunks16 inp_after)` by
       (qpat_x_assum `chunks16 inp = _` (fn th => CONV_TAC (LHS_CONV (REWR_CONV th)))
        \\ simp [])
  \\ `LENGTH (TAKE r (chunks16 inp)) = r` by simp []
  \\ `r < LENGTH (chunks16 inp)` by
       (qpat_assum `chunks16 inp = TAKE r _ ++ _` (fn th => CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV th))))
        \\ simp [])
  \\ `TAKE (r + 1) (chunks16 inp) = TAKE r (chunks16 inp) ++ [frame]` by
       (qpat_assum `chunks16 inp = TAKE r _ ++ _` (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th))))
        \\ `r + 1 = LENGTH (TAKE r (chunks16 inp)) + 1` by simp []
        \\ pop_assum SUBST1_TAC
        \\ simp [rich_listTheory.TAKE_APPEND2])
  \\ rpt conj_tac
  >- decide_tac
  >- first_assum ACCEPT_TAC
  \\ qpat_x_assum `TAKE (r + 1) _ = _`
       (fn th => CONV_TAC (RHS_CONV (LAND_CONV (RAND_CONV (REWR_CONV th)))))
  \\ REWRITE_TAC [listTheory.FLAT_APPEND, listTheory.FLAT, listTheory.APPEND_NIL,
                  GSYM listTheory.APPEND_ASSOC]
  \\ qpat_x_assum `inp_cur = _` (fn th => REWRITE_TAC [GSYM th])
  \\ first_assum ACCEPT_TAC
QED

Theorem chunks16_take_all_of_lt16[local]:
  ∀r inp inp_cur.
    r ≤ LENGTH (chunks16 inp) ∧
    inp = FLAT (TAKE r (chunks16 inp)) ++ inp_cur ∧
    LENGTH inp_cur < 16 ⇒
    TAKE r (chunks16 inp) = chunks16 inp
Proof
  rpt strip_tac
  \\ drule_all chunks16_drop_eq \\ strip_tac
  \\ `chunks16 inp_cur = []` by simp [chunks16_lt16]
  \\ qpat_x_assum `chunks16 inp = _` (fn th => CONV_TAC (RHS_CONV (REWR_CONV th)))
  \\ simp []
QED

Theorem FLAT_snoc_prefix[local]:
  ∀xs f chunk. chunk ≼ f ⇒ FLAT xs ++ chunk ≼ FLAT (xs ++ [f])
Proof
  simp [listTheory.FLAT_APPEND]
QED

(* ---- 3. Exact Target Machine Config, Installation & Compilation Lift ---- *)

Theorem erase_mc_conf_ok[local]:
  ∀B ffi_if inst_if. mc_conf_ok (erase_mc B (forge_mc_with ffi_if inst_if))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ `mc_conf_ok (forge_mc_with ffi_if inst_if)` by (
       irule arm8_configProofTheory.arm8_machine_config_ok
       \\ simp [arm8_configProofTheory.is_arm8_machine_config_def, forge_mc_with_def])
  \\ pop_assum mp_tac
  \\ simp [lab_to_targetProofTheory.mc_conf_ok_def, erase_mc_def, forge_mc_with_def,
           arm8_target_exact_encoder_correct]
  \\ simp [arm8_target_exact_def]
QED

Theorem erase_mc_init_ok[local]:
  ∀B ffi_if inst_if.
    mc_init_ok arm8_config arm8_backend_config (erase_mc B (forge_mc_with ffi_if inst_if))
Proof
  rpt gen_tac \\ PairCases_on `B`
  \\ `mc_init_ok arm8_config arm8_backend_config (forge_mc_with ffi_if inst_if)` by (
       irule arm8_configProofTheory.arm8_init_ok
       \\ simp [arm8_configProofTheory.is_arm8_machine_config_def, forge_mc_with_def])
  \\ pop_assum mp_tac
  \\ simp [backendProofTheory.mc_init_ok_def, erase_mc_def, forge_mc_with_def,
           arm8_target_exact_def]
QED

Theorem forge_installed_exact:
  ∀ms0 ffi_if inst_if.
    forge_elf_loaded code data ms0 ∧
    real_interfer_ok (bits_of ms0) ffi_if inst_if ⇒
    let ms1 = FUNPOW arm8$Next 43 ms0 in
    let emc = erase_mc (bits_of ms0) (forge_mc_with ffi_if inst_if) in
      det_run 43 ms0 ms1 ∧
      ms1.PC = FORGE_CAKE_MAIN ∧
      bits_of ms1 = bits_of ms0 ∧
      ms1.SP_EL0 = ms0.SP_EL0 ∧
      sp_ok ms1 ∧
      arm8_ok (erase ms1) ∧
      shim_loaded ms1.MEM ∧
      installed code FORGE_CBSPACE data 0 info.lab_conf.ffi_names
        (1, 3) emc [] (erase ms1)
Proof
  rpt strip_tac
  \\ fs [forge_elf_loaded_def]
  \\ mp_tac counter_compiled \\ strip_tac
  \\ qspec_then `ms0` mp_tac startup_to_cake_main \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ qabbrev_tac `B = bits_of ms0`
  \\ qabbrev_tac `emc = erase_mc B (forge_mc_with ffi_if inst_if)`
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
  \\ drule real_interfer_ok_imp_erase_ok \\ strip_tac
  \\ rpt conj_tac
  >- (
    (* good_init_state *)
    simp [targetSemTheory.good_init_state_def, targetSemTheory.target_configured_def,
          targetSemTheory.code_loaded_def, asmPropsTheory.target_state_rel_def,
          Abbr `emc`, erase_mc_def, forge_mc_with_def,
          arm8_target_exact_def, arm8_targetTheory.arm8_target_def,
          arm8_targetTheory.arm8_config_def, erase_fields]
    \\ rpt conj_tac
    >- (fs [sp_ok_def, bits_of_def, Abbr `B`])
    >- (mp_tac (Q.SPECL [`ffi_if`, `inst_if`] forge_mc_with_start_pc_ok)
        \\ simp [targetSemTheory.start_pc_ok_def, forge_mc_with_def])
    >- (simp [FORGE_CAKE_MAIN_def] \\ EVAL_TAC)
    >- (qpat_x_assum `interference_ok _ _` mp_tac
        \\ simp [erase_mc_def, forge_mc_with_def, arm8_target_exact_def, arm8_targetTheory.arm8_target_def])
    >- (qpat_x_assum `ffi_interfer_ok _ _` mp_tac
        \\ simp [erase_mc_def, forge_mc_with_def, arm8_target_exact_def,
                 arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
    >- (qpat_x_assum `install_interfer_ok _ _ _` mp_tac
        \\ simp [erase_mc_def, forge_mc_with_def, arm8_target_exact_def,
                 arm8_targetTheory.arm8_target_def, arm8_targetTheory.arm8_config_def])
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
    simp [Abbr `emc`, erase_mc_def, forge_mc_with_def, arm8_target_exact_def,
          arm8_targetTheory.arm8_target_def, erase_fields]
    \\ `byte_align (FORGE_HEAP + 3w * bytes_in_word) = FORGE_HEAP + 24w ∧
        FORGE_CAKE_MAIN + 0x1229Cw = FORGE_CB_BEGIN` by
      (simp [FORGE_HEAP_def, FORGE_CAKE_MAIN_def, FORGE_CB_BEGIN_def,
             bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ simp [])
  >- (
    simp [Abbr `emc`, erase_mc_def, forge_mc_with_def, arm8_target_exact_def,
          arm8_targetTheory.arm8_target_def, erase_fields]
    \\ `byte_align (FORGE_HEAP + 4w * bytes_in_word) = FORGE_HEAP + 32w` by
         (simp [FORGE_HEAP_def, bytes_in_word_64, byte_align_64] \\ EVAL_TAC)
    \\ pop_assum SUBST1_TAC \\ simp []
    \\ simp [FORGE_CAKE_MAIN_def, FORGE_CBSPACE_def, FORGE_CB_END_def] \\ EVAL_TAC)
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
  >- simp [Abbr `emc`, erase_mc_def, forge_ffi_names_eq]
  \\ gen_tac \\ strip_tac
  \\ `i = 2` by (
       qpat_x_assum `mmio_pcs_min_index _ = SOME i` mp_tac
       \\ mp_tac (Q.SPECL [`ffi_if`, `inst_if`] forge_mc_with_mmio_min)
       \\ simp [Abbr `emc`, erase_mc_def])
  \\ rveq
  \\ simp [Abbr `emc`, erase_mc_def, forge_mc_with_def, FORGE_CBSPACE_def,
           lab_to_targetTheory.ffi_offset_def, dimword_64]
QED

Theorem forge_compile_exact:
  ∀ms0 io ffi_if inst_if.
    forge_elf_loaded code data ms0 ∧ io.outputs = [] ∧
    real_interfer_ok (bits_of ms0) ffi_if inst_if ⇒
    let ms1 = FUNPOW arm8$Next 43 ms0 in
    let rmc = real_mc (bits_of ms0) (forge_mc_with ffi_if inst_if) in
      rmc.target = arm8_target_real (bits_of ms0) ∧
      ¬machine_sem rmc (counter_ffi io) ms1 Fail ∧
      (∀j. FST (evaluate rmc (counter_ffi io) j ms1) ≠ Error) ∧
      (∃ck t ms_end st_end.
         evaluate rmc (counter_ffi io) ck ms1 = (Halt t, ms_end, st_end) ∧
         stop_after_err st_end.io_events ∧
         ((t = Success ∧
           sent_frames_of st_end.io_events =
             limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs)))) ∨
          (t = Resource_limit_hit ∧
           sent_frames_of st_end.io_events ≼
             limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs)))))) ∧
      (∀ck t ms_end st_end.
         evaluate rmc (counter_ffi io) ck ms1 = (Halt t, ms_end, st_end) ⇒
         stop_after_err st_end.io_events ∧
         ((t = Success ∧
           sent_frames_of st_end.io_events =
             limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs)))) ∨
          (t = Resource_limit_hit ∧
           sent_frames_of st_end.io_events ≼
             limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs))))))
Proof
  rpt strip_tac
  \\ simp [LET_THM]
  \\ drule_all forge_installed_exact \\ simp [LET_THM] \\ strip_tac
  \\ qabbrev_tac `ms1 = FUNPOW arm8$Next 43 ms0`
  \\ qabbrev_tac `mc0 = forge_mc_with ffi_if inst_if`
  \\ qabbrev_tac `emc = erase_mc (bits_of ms0) mc0`
  \\ qabbrev_tac `rmc = real_mc (bits_of ms0) mc0`
  \\ mp_tac counter_compiled \\ strip_tac
  \\ drule counter_semantics \\ strip_tac
  \\ `∀b. semantics_prog (init_state (counter_ffi io)) init_env counter_prog b ⇒
          ∃io_events. b = Terminate Success io_events ∧
                      stop_after_err io_events ∧
                      sent_frames_of io_events =
                        limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs)))` by
       fs [semanticsPropsTheory.sem_satisfies_def, ml_progTheory.semantics_dec_list_eq, IN_DEF]
  \\ `¬semantics_prog (init_state (counter_ffi io)) init_env counter_prog Fail` by
       (strip_tac \\ first_x_assum drule \\ simp [])
  \\ `heap_regs arm8_backend_config.stack_conf.reg_names = (1, 3)` by EVAL_TAC
  \\ `mc_conf_ok emc ∧ mc_init_ok arm8_config arm8_backend_config emc` by
       simp [Abbr `emc`, Abbr `mc0`, erase_mc_conf_ok, erase_mc_init_ok]
  \\ `machine_sem emc (counter_ffi io) (erase ms1) ⊆
      extend_with_resource_limit (semantics_prog (init_state (counter_ffi io)) init_env counter_prog)` by (
       irule (MATCH_MP backendProofTheory.compile_correct (cj 1 counter_compiled)
              |> SIMP_RULE (srw_ss()) [LET_THM, ml_progTheory.init_state_env_thm,
                                       backendProofTheory.set_oracle_simp,
                                       arm8_configProofTheory.arm8_backend_config_ok])
       \\ simp [] \\ metis_tac [])
  \\ `¬machine_sem emc (counter_ffi io) (erase ms1) Fail` by (
       strip_tac
       \\ `Fail ∈ extend_with_resource_limit (semantics_prog (init_state (counter_ffi io)) init_env counter_prog)` by
            fs [SUBSET_DEF, IN_DEF]
       \\ drule semanticsPropsTheory.extend_with_resource_limit_not_fail
       \\ simp [IN_DEF])
  \\ `machine_sem rmc (counter_ffi io) ms1 = machine_sem emc (counter_ffi io) (erase ms1)` by (
       fs [Abbr `rmc`, Abbr `emc`]
       \\ irule machine_sem_real_eq_exact
       \\ simp [Abbr `mc0`, forge_mc_with_lo55]
       \\ rpt conj_tac
       >- fs [real_interfer_ok_def, LET_THM, forge_mc_with_def]
       >- fs [real_interfer_ok_def, LET_THM, forge_mc_with_def]
       >- simp [forge_mc_with_def]
       >- simp [forge_mc_with_def]
       \\ fs [sp_ok_def, bits_of_def, forge_elf_loaded_def])
  \\ `¬machine_sem rmc (counter_ffi io) ms1 Fail` by simp []
  \\ `∀b. machine_sem rmc (counter_ffi io) ms1 b ⇒
          ∃t io_events.
            b = Terminate t io_events ∧
            stop_after_err io_events ∧
            ((t = Success ∧
              sent_frames_of io_events =
                limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs)))) ∨
             (t = Resource_limit_hit ∧
              sent_frames_of io_events ≼
                limit_frames io.write_limit (SND (SND (counter_run 0w 0w io.inputs)))))` by (
       rpt strip_tac
       \\ `b ∈ extend_with_resource_limit (semantics_prog (init_state (counter_ffi io)) init_env counter_prog)` by
            metis_tac [SUBSET_DEF, IN_DEF]
       \\ qpat_x_assum `b ∈ extend_with_resource_limit _` mp_tac
       \\ simp [semanticsPropsTheory.extend_with_resource_limit_def]
       \\ rpt strip_tac \\ fs [IN_DEF]
       \\ qpat_x_assum `∀b. semantics_prog _ _ _ b ⇒ _`
            (fn ih => qpat_x_assum `semantics_prog _ _ _ _` (strip_assume_tac o MATCH_MP ih))
       \\ rveq \\ fs []
       \\ metis_tac [stop_after_err_prefix, sent_frames_of_prefix])
  \\ rpt conj_tac
  >- simp [Abbr `rmc`, real_mc_def]
  >- simp []
  >- (qpat_x_assum `¬machine_sem rmc _ _ Fail` mp_tac \\ simp [targetSemTheory.machine_sem_def])
  >- (
    qspecl_then [`rmc`, `counter_ffi io`, `ms1`] strip_assume_tac
      (Q.GENL [`mc`, `st`, `ms`] targetPropsTheory.machine_sem_total)
    \\ first_x_assum drule \\ strip_tac \\ rveq
    \\ qpat_x_assum `machine_sem rmc _ _ (Terminate _ _)` mp_tac
    \\ simp [targetSemTheory.machine_sem_def] \\ strip_tac
    \\ metis_tac [])
  \\ rpt gen_tac \\ strip_tac
  \\ `machine_sem rmc (counter_ffi io) ms1 (Terminate t st_end.io_events)` by
       (simp [targetSemTheory.machine_sem_def] \\ metis_tac [])
  \\ first_x_assum drule \\ strip_tac \\ fs []
QED

(* ---- 4. Single-Step Real-Bits Evaluation & Counter-FFI Oracle Helpers ---- *)

Theorem shift_rmc_next_interfer[local]:
  ∀B ffi_if inst_if.
    (real_mc B (forge_mc_with ffi_if inst_if) with next_interfer := shift_seq 1 (K I)) =
    real_mc B (forge_mc_with ffi_if inst_if)
Proof
  rpt gen_tac
  \\ simp [real_mc_def, forge_mc_with_def, miscTheory.shift_seq_def, FUN_EQ_THM,
           targetSemTheory.machine_config_component_equality]
QED

Theorem shift_mk_real_ffi_if[local]:
  ∀P. shift_seq 1 (mk_real_ffi_if P) = mk_real_ffi_if (λk. P (k + 1))
Proof
  gen_tac \\ simp [FUN_EQ_THM, pairTheory.FORALL_PROD, miscTheory.shift_seq_def, mk_real_ffi_if_def]
QED

Theorem real_mc_shift_ffi_P[local]:
  ∀B P.
    (real_mc B (forge_mc_with (mk_real_ffi_if P) forge_real_install_if) with
       ffi_interfer := shift_seq 1 (mk_real_ffi_if P)) =
    real_mc B (forge_mc_with (mk_real_ffi_if (λk. P (k + 1))) forge_real_install_if)
Proof
  rpt gen_tac
  \\ simp [real_mc_def, forge_mc_with_def, shift_mk_real_ffi_if,
           targetSemTheory.machine_config_component_equality]
QED

Theorem mk_real_ffi_if_pc[local]:
  ∀P k idx new_bs s. (mk_real_ffi_if P k (idx, new_bs, s)).PC = s.REG 30w
Proof
  rpt gen_tac \\ simp [mk_real_ffi_if_def]
  \\ IF_CASES_TAC
  >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [ffi_return_ok_def])
  \\ simp [forge_canonical_ffi_post_def]
QED

Theorem mk_real_ffi_if_select[local]:
  ∀P k idx new_bs s s_tgt.
    (∀s'. P k idx new_bs s s' ⇔ s' = s_tgt) ∧ ffi_return_ok new_bs s s_tgt ⇒
    mk_real_ffi_if P k (idx, new_bs, s) = s_tgt
Proof
  rpt strip_tac \\ simp [mk_real_ffi_if_def]
  \\ SELECT_ELIM_TAC \\ simp []
QED

Theorem counter_ffi_call_send16[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = counter_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «send16») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = counter_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «send16») bytes (ZIP (bytes2, new_bs))] ∧
      (LENGTH bytes2 < 17 ⇒
         new_bs = bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state ∧
         sent_frames_of ffi'.io_events = sent_frames_of ffi.io_events) ∧
      (17 ≤ LENGTH bytes2 ⇒
         let frame = TAKE 16 (DROP 1 bytes2) in
         sent_frames_of ffi'.io_events = sent_frames_of ffi.io_events ++ [frame] ∧
         (ffi.ffi_state.write_limit = NONE ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with outputs := ffi.ffi_state.outputs ++ [frame]) ∧
         (ffi.ffi_state.write_limit = SOME 0 ⇒
            new_bs = 1w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with outputs := ffi.ffi_state.outputs ++ [frame] ∧
            event_is_err (IO_event (ExtCall «send16») bytes (ZIP (bytes2, new_bs)))) ∧
         (∀d. ffi.ffi_state.write_limit = SOME (SUC d) ⇒
            new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = ffi.ffi_state with <| outputs := ffi.ffi_state.outputs ++ [frame];
                                                   write_limit := SOME d |>))
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [counter_ffi_oracle_def, ffi_send16_def]
  \\ (Cases_on `LENGTH bytes2 < 17` \\ simp [])
  >- simp [sent_frames_of_append, sent_frames_of_def, listTheory.LENGTH_ZIP]
  \\ (Cases_on `ffi.ffi_state.write_limit` \\ simp [])
  >- (
    `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames_of_append, sent_frames_of_def, listTheory.MAP_ZIP, listTheory.LENGTH_ZIP])
  \\ (Cases_on `x` \\ simp [])
  >- (
    `LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames_of_append, sent_frames_of_def, listTheory.MAP_ZIP, listTheory.LENGTH_ZIP,
             event_is_err_def]
    \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
  \\ simp [sent_frames_of_append, sent_frames_of_def, listTheory.MAP_ZIP, listTheory.LENGTH_ZIP]
QED

Theorem counter_ffi_call_recv16[local]:
  ∀ffi bytes bytes2.
    ffi.oracle = counter_ffi_oracle ⇒
    ∃ffi' new_bs.
      call_FFI ffi (ExtCall «recv16») bytes bytes2 = FFI_return ffi' new_bs ∧
      ffi'.oracle = counter_ffi_oracle ∧
      LENGTH new_bs = LENGTH bytes2 ∧
      ffi'.io_events = ffi.io_events ++ [IO_event (ExtCall «recv16») bytes (ZIP (bytes2, new_bs))] ∧
      sent_frames_of ffi'.io_events = sent_frames_of ffi.io_events ∧
      (LENGTH bytes2 < 17 ⇒
         new_bs = bytes2 ∧ ffi'.ffi_state = ffi.ffi_state) ∧
      (17 ≤ LENGTH bytes2 ∧ ffi.ffi_state.inputs = [] ⇒
         new_bs = 1w :: DROP 1 bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state ∧
         event_is_err (IO_event (ExtCall «recv16») bytes (ZIP (bytes2, new_bs)))) ∧
      (∀f fs. 17 ≤ LENGTH bytes2 ∧ ffi.ffi_state.inputs = f :: fs ∧ LENGTH f = 16 ⇒
         new_bs = 0w :: f ++ DROP 17 bytes2 ∧
         ffi'.ffi_state = ffi.ffi_state with inputs := fs)
Proof
  rpt strip_tac
  \\ simp [ffiTheory.call_FFI_def]
  \\ fs [counter_ffi_oracle_def, ffi_recv16_def]
  \\ (Cases_on `LENGTH bytes2 < 17` \\ simp [])
  >- simp [sent_frames_of_append, sent_frames_of_def, listTheory.LENGTH_ZIP]
  \\ (Cases_on `ffi.ffi_state.inputs` \\ simp [])
  >- (
    `LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames_of_append, sent_frames_of_def, listTheory.LENGTH_ZIP, event_is_err_def]
    \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ (Cases_on `LENGTH h = 16` \\ simp [])
  >- (
    `LENGTH (0w :: h ++ DROP 17 bytes2) = LENGTH bytes2` by simp []
    \\ simp [sent_frames_of_append, sent_frames_of_def, listTheory.LENGTH_ZIP])
  \\ `LENGTH (1w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
  \\ simp [sent_frames_of_append, sent_frames_of_def, listTheory.LENGTH_ZIP]
QED

Theorem forge_veneer_facts[local]:
  FORGE_EXIT_VENEER ∉ forge_prog_addresses ∧
  FORGE_INSTALL_VENEER ∉ forge_prog_addresses ∧
  FORGE_FFISEND16_VENEER ∉ forge_prog_addresses ∧
  FORGE_FFIRECV16_VENEER ∉ forge_prog_addresses ∧
  FORGE_EXIT_VENEER ≠ FORGE_INSTALL_VENEER ∧
  FORGE_EXIT_VENEER ≠ FORGE_FFISEND16_VENEER ∧
  FORGE_EXIT_VENEER ≠ FORGE_FFIRECV16_VENEER ∧
  FORGE_INSTALL_VENEER ≠ FORGE_FFISEND16_VENEER ∧
  FORGE_INSTALL_VENEER ≠ FORGE_FFIRECV16_VENEER ∧
  FORGE_FFISEND16_VENEER ≠ FORGE_FFIRECV16_VENEER ∧
  FORGE_INSTALL_VENEER ≠ FORGE_EXIT_VENEER ∧
  FORGE_FFISEND16_VENEER ≠ FORGE_EXIT_VENEER ∧
  FORGE_FFISEND16_VENEER ≠ FORGE_INSTALL_VENEER ∧
  FORGE_FFIRECV16_VENEER ≠ FORGE_EXIT_VENEER ∧
  FORGE_FFIRECV16_VENEER ≠ FORGE_INSTALL_VENEER ∧
  FORGE_FFIRECV16_VENEER ≠ FORGE_FFISEND16_VENEER
Proof
  simp [forge_prog_addresses_def, forge_code_region_def, forge_bitmaps_region_def,
        forge_heap_stack_region_def, FORGE_CAKE_MAIN_def, FORGE_CB_END_def,
        FORGE_CAKE_BITMAPS_def, FORGE_BM_BUF_END_def, FORGE_HEAP_def, FORGE_STACKEND_def,
        FORGE_EXIT_VENEER_def, FORGE_INSTALL_VENEER_def,
        FORGE_FFISEND16_VENEER_def, FORGE_FFIRECV16_VENEER_def] \\ EVAL_TAC
QED

Theorem real_mc_eval_step_cases[local]:
  ∀B P ffi s.
    let rmc = real_mc B (forge_mc_with (mk_real_ffi_if P) forge_real_install_if) in
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧ shim_loaded s.MEM ∧
      ffi.oracle = counter_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ⇒
      (s.PC ∈ forge_prog_addresses ∧ s.PC ≠ FORGE_FFISEND16_VENEER ∧ s.PC ≠ FORGE_FFIRECV16_VENEER ⇒
         ¬is_svc0_at s ∧
         NextStateARM8 s = SOME (arm8$Next s) ∧
         arm8_ok (erase (arm8$Next s)) ∧ sp_ok (arm8$Next s) ∧
         bits_of (arm8$Next s) = B ∧ shim_loaded (arm8$Next s).MEM ∧
         (∀k. evaluate rmc ffi (SUC k) s = evaluate rmc ffi k (arm8$Next s))) ∧
      (s.PC = FORGE_EXIT_VENEER ⇒
         ∀k. evaluate rmc ffi (SUC k) s =
             (if s.REG 0w = 0w then Halt Success else Halt Resource_limit_hit, s, ffi)) ∧
      (s.PC = FORGE_FFISEND16_VENEER ∨ s.PC = FORGE_FFIRECV16_VENEER ⇒
         ∃bytes bytes2.
           read_bytearray (s.REG 0w) (w2n (s.REG 1w))
             (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes ∧
           read_bytearray (s.REG 2w) (w2n (s.REG 3w))
             (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
           aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w)) ∧
      ((s.PC ∈ forge_prog_addresses ∧ s.PC ≠ FORGE_FFISEND16_VENEER ∧ s.PC ≠ FORGE_FFIRECV16_VENEER) ∨
       s.PC = FORGE_EXIT_VENEER ∨ s.PC = FORGE_INSTALL_VENEER ∨
       s.PC = FORGE_FFISEND16_VENEER ∨ s.PC = FORGE_FFIRECV16_VENEER)
Proof
  rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_mc_with (mk_real_ffi_if P) forge_real_install_if)`
  \\ strip_tac
  \\ strip_assume_tac forge_veneer_facts
  \\ rpt conj_tac
  >- (
    strip_tac
    \\ `s.PC ≠ FORGE_EXIT_VENEER ∧ s.PC ≠ FORGE_INSTALL_VENEER` by metis_tac []
    \\ `SND (SND B) ⇒ aligned 4 s.SP_EL0` by
         (qpat_x_assum `bits_of s = B` (SUBST1_TAC o SYM) \\ fs [sp_ok_def, bits_of_def])
    \\ `encoded_bytes_in_mem arm8_config s.PC s.MEM forge_prog_addresses ∧
        arm8_ok (erase (arm8$Next s)) ∧ bits_of (arm8$Next s) = B ∧
        (SND (SND B) ⇒ aligned 4 (arm8$Next s).SP_EL0) ∧
        (∀x. x ∉ forge_prog_addresses ⇒ (arm8$Next s).MEM x = s.MEM x)` by (
         qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
         \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_with_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def]
         \\ Cases_on `encoded_bytes_in_mem arm8_config s.PC s.MEM forge_prog_addresses` \\ simp []
         \\ Cases_on `((¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧ arm8_ok (erase (arm8$Next s)) ∧
                       bits_of (arm8$Next s) = B ∧ (¬SND (SND B) ∨ aligned 4 (arm8$Next s).SP_EL0)) ∧
                      (∀x. x ∉ forge_prog_addresses ⇒ (arm8$Next s).MEM x = s.MEM x)` \\ simp []
         \\ strip_tac \\ metis_tac [])
    \\ rpt conj_tac
    >- (irule encoded_bytes_in_mem_not_svc0 \\ qexists_tac `forge_prog_addresses` \\ simp [])
    >- (simp [arm8_stepTheory.NextStateARM8_def] \\ fs [arm8_ok_erase])
    >- simp []
    >- (fs [sp_ok_def, arm8_ok_erase] \\ Cases_on `(arm8$Next s).SCTLR_EL1.SA0` \\ simp []
        \\ qpat_x_assum `SND (SND B) ⇒ aligned 4 (arm8$Next s).SP_EL0` irule
        \\ qpat_x_assum `bits_of (arm8$Next s) = B` (SUBST1_TAC o SYM) \\ simp [bits_of_def])
    >- simp []
    >- (irule (iffRL shim_loaded_cong) \\ qexists_tac `s.MEM` \\ simp []
        \\ rpt strip_tac \\ first_x_assum irule
        \\ strip_tac \\ drule (cj 1 forge_regions_disjoint) \\ gvs [])
    \\ gen_tac
    \\ `shift_seq 1 (K I) = (K I : num -> arm8_state -> arm8_state)` by
         simp [miscTheory.shift_seq_def, FUN_EQ_THM]
    \\ `(¬SND (SND B) ∨ aligned 4 s.SP_EL0) ∧ (¬SND (SND B) ∨ aligned 4 (arm8$Next s).SP_EL0)` by metis_tac []
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_with_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def])
  >- (
    strip_tac \\ gen_tac
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_with_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def])
  >- (
    disch_tac
    \\ `s.PC ∉ forge_prog_addresses ∧ s.PC ≠ FORGE_EXIT_VENEER ∧ s.PC ≠ FORGE_INSTALL_VENEER` by metis_tac []
    \\ `find_index s.PC [FORGE_FFISEND16_VENEER; FORGE_FFIRECV16_VENEER] 0 =
        SOME (if s.PC = FORGE_FFISEND16_VENEER then 0 else 1)` by
         (Cases_on `s.PC = FORGE_FFISEND16_VENEER` \\ fs [miscTheory.find_index_def])
    \\ qabbrev_tac `idx = if s.PC = FORGE_FFISEND16_VENEER then 0 else 1`
    \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `2` mp_tac)
    \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_with_def,
             arm8_target_real_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def,
             targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def]
    \\ `EL idx [ExtCall «send16»; ExtCall «recv16»] =
        ExtCall (if idx = 0 then «send16» else «recv16»)` by (simp [Abbr `idx`] \\ rw [])
    \\ pop_assum SUBST1_TAC
    \\ Cases_on `read_bytearray (s.REG 0w) (w2n (s.REG 1w))
                   (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE)` \\ simp []
    \\ rename1 `read_bytearray (s.REG 0w) _ _ = SOME bytes`
    \\ Cases_on `read_bytearray (s.REG 2w) (w2n (s.REG 3w))
                   (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE)` \\ simp []
    \\ rename1 `read_bytearray (s.REG 2w) _ _ = SOME bytes2`
    \\ `∃ffi1 new_bs. call_FFI ffi (ExtCall (if idx = 0 then «send16» else «recv16»)) bytes bytes2 =
                      FFI_return ffi1 new_bs` by
         ((Cases_on `idx = 0` \\ simp [])
          >- (drule counter_ffi_call_send16 \\ metis_tac [])
          \\ drule counter_ffi_call_recv16 \\ metis_tac [])
    \\ pop_assum strip_assume_tac \\ simp []
    \\ qabbrev_tac `ms1 = mk_real_ffi_if P 0 (idx, new_bs, s)`
    \\ `ms1.PC = s.REG 30w` by simp [Abbr `ms1`, mk_real_ffi_if_pc]
    \\ simp [Once targetSemTheory.evaluate_def, arm8_targetTheory.arm8_target_def,
             targetSemTheory.apply_oracle_def]
    \\ (Cases_on `s.REG 30w = FORGE_EXIT_VENEER` \\ simp [])
    >- (simp [FORGE_EXIT_VENEER_def, untagged_def] \\ EVAL_TAC)
    \\ (Cases_on `s.REG 30w = FORGE_INSTALL_VENEER` \\ simp [])
    >- (simp [FORGE_INSTALL_VENEER_def, untagged_def] \\ EVAL_TAC)
    \\ (Cases_on `s.REG 30w ∈ forge_prog_addresses` \\ simp [])
    >- (
      `s.REG 30w ≠ FORGE_FFISEND16_VENEER ∧ s.REG 30w ≠ FORGE_FFIRECV16_VENEER` by metis_tac []
      \\ simp []
      \\ Cases_on `encoded_bytes_in_mem arm8_config (s.REG 30w) ms1.MEM forge_prog_addresses` \\ simp []
      \\ Cases_on `arm8_ok (erase ms1)` \\ simp []
      \\ disch_tac \\ conj_tac
      >- (qpat_x_assum `arm8_ok (erase ms1)` mp_tac \\ simp [arm8_ok_erase])
      \\ irule (cj 5 forge_regions_disjoint) \\ simp [])
    \\ (Cases_on `s.REG 30w = FORGE_FFISEND16_VENEER` \\ simp [miscTheory.find_index_def])
    >- (simp [FORGE_FFISEND16_VENEER_def, untagged_def] \\ EVAL_TAC)
    \\ (Cases_on `s.REG 30w = FORGE_FFIRECV16_VENEER` \\ simp [miscTheory.find_index_def])
    \\ simp [FORGE_FFIRECV16_VENEER_def, untagged_def] \\ EVAL_TAC)
  \\ qpat_x_assum `∀j. FST _ ≠ Error` (qspec_then `1` mp_tac)
  \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_with_def,
           arm8_target_real_def, arm8_targetTheory.arm8_target_def]
  \\ Cases_on `s.PC ∈ forge_prog_addresses ∧ s.PC ≠ FORGE_FFISEND16_VENEER ∧ s.PC ≠ FORGE_FFIRECV16_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_EXIT_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_INSTALL_VENEER` \\ simp []
  \\ Cases_on `s.PC = FORGE_FFISEND16_VENEER` \\ simp [miscTheory.find_index_def]
  \\ Cases_on `s.PC = FORGE_FFIRECV16_VENEER` \\ simp [miscTheory.find_index_def]
QED

(* ---- 5. Conjunct 2: Forward Liveness under Error-Free Linux Syscalls ---- *)

Definition noerr_ffi_P_def:
  noerr_ffi_P (tail_bs:word8 list) (k:num) (idx:num) (new_bs:word8 list)
              (s:arm8_state) (s':arm8_state) ⇔
    (idx = 0 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 17 ⇒
          ∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
       (17 ≤ w2n (s.REG 3w) ⇒
          ∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                      (inp, out, s) (inp, out ++ TAKE 16 (DROP 1 bytes2), s'))) ∨
    (idx = 1 ∧
     ∃bytes2.
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       (w2n (s.REG 3w) < 17 ⇒
          ∀inp out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp, out, s) (inp, out, s')) ∧
       (17 ≤ w2n (s.REG 3w) ∧ HD new_bs = 0w ⇒
          ∀rest out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
                       (TAKE 16 (DROP 1 new_bs) ++ rest, out, s) (rest, out, s')) ∧
       (17 ≤ w2n (s.REG 3w) ∧ HD new_bs ≠ 0w ⇒
          ∀out. RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (tail_bs, out, s) ([], out, s')))
End

Theorem noerr_ffi_P_shift[local]:
  ∀tail_bs. (λk. noerr_ffi_P tail_bs (k + 1)) = noerr_ffi_P tail_bs
Proof
  gen_tac \\ simp [FUN_EQ_THM, noerr_ffi_P_def]
QED

Theorem liveness_eval_rtc[local]:
  ∀ck B tail_bs ffi s inp_cur out_cur t ms_end st_end.
    let rmc = real_mc B (forge_mc_with (mk_real_ffi_if (noerr_ffi_P tail_bs)) forge_real_install_if) in
      LENGTH tail_bs < 16 ∧
      arm8_ok (erase s) ∧ sp_ok s ∧ bits_of s = B ∧ shim_loaded s.MEM ∧
      ffi.oracle = counter_ffi_oracle ∧
      ffi.ffi_state.write_limit = NONE ∧
      EVERY (λf. LENGTH f = 16) ffi.ffi_state.inputs ∧
      inp_cur = FLAT ffi.ffi_state.inputs ++ tail_bs ∧
      (∀j. FST (evaluate rmc ffi j s) ≠ Error) ∧
      evaluate rmc ffi ck s = (Halt t, ms_end, st_end) ∧
      stop_after_err st_end.io_events ∧
      EVERY ($~ o event_is_err) ffi.io_events ⇒
      ∃inp_f out_f ms_f ec.
        RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
          (inp_cur, out_cur, s) (inp_f, out_f, ms_f) ∧
        svc_exit_group_rel ec ms_f
Proof
  Induct_on `ck`
  >- (rpt gen_tac \\ simp [LET_THM] \\ strip_tac
      \\ qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
  \\ rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_mc_with (mk_real_ffi_if (noerr_ffi_P tail_bs)) forge_real_install_if)`
  \\ strip_tac
  \\ qspecl_then [`B`, `noerr_ffi_P tail_bs`, `ffi`, `s`] mp_tac real_mc_eval_step_cases
  \\ simp [LET_THM] \\ strip_tac
  >- (
    (* Prog address step *)
    first_x_assum drule \\ strip_tac
    \\ `evaluate rmc ffi ck (arm8$Next s) = (Halt t, ms_end, st_end)` by fs []
    \\ `∀j. FST (evaluate rmc ffi j (arm8$Next s)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
    \\ qpat_x_assum `∀B tail_bs ffi s. _`
         (qspecl_then [`B`, `tail_bs`, `ffi`, `arm8$Next s`, `inp_cur`, `out_cur`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp []
    \\ ONCE_REWRITE_TAC [relationTheory.RTC_CASES1] \\ disj2_tac
    \\ qexists_tac `(inp_cur, out_cur, arm8$Next s)`
    \\ simp [whole_step_def])
  >- (
    (* Exit veneer *)
    drule_all cake_exit_to_svc_exit_group \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `inp_cur` \\ qexists_tac `out_cur`
    \\ qexists_tac `FUNPOW arm8$Next k s`
    \\ qexists_tac `if s.REG 0w = 0w then 0w else 1w`
    \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `k` \\ simp [])
  >- (
    (* Install veneer *)
    drule_all cake_install_to_svc_exit_group \\ simp [LET_THM] \\ strip_tac
    \\ qexists_tac `inp_cur` \\ qexists_tac `out_cur`
    \\ qexists_tac `FUNPOW arm8$Next 3 s` \\ qexists_tac `2w`
    \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
  >- (
    (* send16 veneer *)
    `∃bytes bytes2.
       read_bytearray (s.REG 0w) (w2n (s.REG 1w))
         (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes ∧
       read_bytearray (s.REG 2w) (w2n (s.REG 3w))
         (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
       aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w)` by simp []
    \\ drule_all (SIMP_RULE (srw_ss()) [LET_THM] counter_ffi_call_send16)
    \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
    \\ imp_res_tac read_bytearray_mem_eq
    \\ qabbrev_tac `s1 = mk_real_ffi_if (noerr_ffi_P tail_bs) 0 (0, new_bs, s)`
    \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
        (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
         `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
           gen_tac
           \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_with_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi_if, noerr_ffi_P_shift, forge_veneer_facts, Abbr `s1`])
         \\ conj_tac >- fs []
         \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
         \\ simp [])
    \\ `∃s_ex. noerr_ffi_P tail_bs 0 0 new_bs s s_ex ∧ ffi_return_ok new_bs s s_ex` by (
         drule_all ffisend16_noerr_exists \\ strip_tac
         \\ Cases_on `w2n (s.REG 3w) < 17`
         >- (fs [] \\ qexists_tac `s'` \\ simp [noerr_ffi_P_def] \\ qexists_tac `bytes2` \\ simp [])
         \\ `17 ≤ w2n (s.REG 3w)` by decide_tac
         \\ fs [] \\ qexists_tac `s'` \\ simp [noerr_ffi_P_def] \\ qexists_tac `bytes2` \\ simp [])
    \\ `noerr_ffi_P tail_bs 0 0 new_bs s s1 ∧ ffi_return_ok new_bs s s1` by (
         simp [Abbr `s1`, mk_real_ffi_if_def]
         \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
         \\ metis_tac [])
    \\ `ffi'.ffi_state.inputs = ffi.ffi_state.inputs ∧ ffi'.ffi_state.write_limit = NONE ∧
        EVERY ($~ o event_is_err) ffi'.io_events ∧
        (∃out_next.
           RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp_cur, out_cur, s) (inp_cur, out_next, s1))` by (
         Cases_on `w2n (s.REG 3w) < 17`
         >- (fs [noerr_ffi_P_def, event_is_err_def, listTheory.LENGTH_ZIP] \\ metis_tac [])
         \\ `17 ≤ LENGTH bytes2` by decide_tac
         \\ fs [noerr_ffi_P_def, event_is_err_def, listTheory.LENGTH_ZIP]
         \\ `LENGTH (0w :: DROP 1 bytes2) = LENGTH bytes2` by simp []
         \\ conj_tac >- (Cases_on `bytes2` \\ fs [listTheory.ZIP])
         \\ metis_tac [])
    \\ qpat_x_assum `∀B tail_bs ffi s. _`
         (qspecl_then [`B`, `tail_bs`, `ffi'`, `s1`, `inp_cur`, `out_next`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac >- fs [ffi_return_ok_def]
    \\ strip_tac
    \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  \\ (* recv16 veneer *)
     `∃bytes bytes2.
        read_bytearray (s.REG 0w) (w2n (s.REG 1w))
          (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes ∧
        read_bytearray (s.REG 2w) (w2n (s.REG 3w))
          (λa. if a ∈ forge_prog_addresses then SOME (s.MEM a) else NONE) = SOME bytes2 ∧
        aligned 2 (s.REG 30w) ∧ untagged (s.REG 30w)` by simp []
  \\ drule_all counter_ffi_call_recv16
  \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
  \\ imp_res_tac read_bytearray_mem_eq
  \\ qabbrev_tac `s1 = mk_real_ffi_if (noerr_ffi_P tail_bs) 0 (1, new_bs, s)`
  \\ `evaluate rmc ffi (SUC ck) s = evaluate rmc ffi' ck s1 ∧
      (∀j. FST (evaluate rmc ffi' j s1) ≠ Error)` by (
       `∀m. evaluate rmc ffi (SUC m) s = evaluate rmc ffi' m s1` by (
         gen_tac
         \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc`, real_mc_def, forge_mc_with_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi_if, noerr_ffi_P_shift, forge_veneer_facts, Abbr `s1`])
       \\ conj_tac >- fs []
       \\ gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi j s) ≠ Error` (qspec_then `SUC j` mp_tac)
       \\ simp [])
  \\ Cases_on `w2n (s.REG 3w) < 17`
  >- (
    `∃s_ex. noerr_ffi_P tail_bs 0 1 new_bs s s_ex ∧ ffi_return_ok new_bs s s_ex` by (
       drule_all ffirecv16_noerr_exists \\ strip_tac
       \\ gvs [] \\ qexists_tac `s'` \\ simp [noerr_ffi_P_def] \\ qexists_tac `bytes2` \\ simp [])
    \\ `noerr_ffi_P tail_bs 0 1 new_bs s s1 ∧ ffi_return_ok new_bs s s1` by (
         simp [Abbr `s1`, mk_real_ffi_if_def]
         \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
         \\ metis_tac [])
    \\ `RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (inp_cur, out_cur, s) (inp_cur, out_cur, s1)` by
         (qpat_x_assum `noerr_ffi_P _ _ _ _ _ _` mp_tac \\ simp [noerr_ffi_P_def])
    \\ `EVERY ($~ o event_is_err) ffi'.io_events` by gvs [event_is_err_def, listTheory.LENGTH_ZIP]
    \\ qpat_x_assum `∀B tail_bs ffi s. _`
         (qspecl_then [`B`, `tail_bs`, `ffi'`, `s1`, `inp_cur`, `out_cur`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM]
    \\ impl_tac >- gvs [ffi_return_ok_def]
    \\ strip_tac
    \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp [] \\ metis_tac [relationTheory.RTC_RTC])
  \\ `17 ≤ LENGTH bytes2` by decide_tac
  \\ Cases_on `ffi.ffi_state.inputs`
  >- (
    (* EOF / truncated <16B: ffi'.io_events now contains event_is_err, so NO more FFI calls occur! *)
    `new_bs = 1w :: DROP 1 bytes2 ∧ ffi'.ffi_state = ffi.ffi_state ∧
     event_is_err (IO_event (ExtCall «recv16») bytes (ZIP (bytes2, new_bs)))` by gvs []
    \\ `∃s_ex. noerr_ffi_P tail_bs 0 1 new_bs s s_ex ∧ ffi_return_ok new_bs s s_ex` by (
         drule_all ffirecv16_noerr_exists \\ strip_tac
         \\ qpat_x_assum `∀tail_bs. 17 ≤ _ ∧ LENGTH tail_bs < 16 ⇒ _` (qspec_then `tail_bs` mp_tac)
         \\ simp [] \\ strip_tac
         \\ qexists_tac `s'` \\ simp [noerr_ffi_P_def] \\ qexists_tac `bytes2` \\ simp [])
    \\ `noerr_ffi_P tail_bs 0 1 new_bs s s1 ∧ ffi_return_ok new_bs s s1` by (
         simp [Abbr `s1`, mk_real_ffi_if_def]
         \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
         \\ metis_tac [])
    \\ `RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) (tail_bs, out_cur, s) ([], out_cur, s1)` by
         (qpat_x_assum `noerr_ffi_P _ _ _ _ _ _` mp_tac \\ simp [noerr_ffi_P_def])
    \\ (* Now step purely via non-FFI steps from s1 to Halt/Install! *)
       `∀ck' s' ffi_s.
          arm8_ok (erase s') ∧ sp_ok s' ∧ bits_of s' = B ∧ shim_loaded s'.MEM ∧
          ffi_s.oracle = counter_ffi_oracle ∧
          (∀j. FST (evaluate rmc ffi_s j s') ≠ Error) ∧
          evaluate rmc ffi_s ck' s' = (Halt t, ms_end, st_end) ∧
          (∃e. MEM e ffi_s.io_events ∧ event_is_err e) ⇒
          ∃inp_f out_f ms_f ec.
            RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel) ([], out_cur, s') (inp_f, out_f, ms_f) ∧
            svc_exit_group_rel ec ms_f` suffices_by (
          strip_tac \\ first_x_assum (qspecl_then [`ck`, `s1`, `ffi'`] mp_tac)
          \\ impl_tac >- (fs [ffi_return_ok_def] \\ metis_tac [])
          \\ strip_tac
          \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
          \\ simp [] \\ fs [] \\ metis_tac [relationTheory.RTC_RTC])
    \\ Induct_on `ck'`
    >- (rpt strip_tac \\ qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rpt strip_tac
    \\ qspecl_then [`B`, `noerr_ffi_P tail_bs`, `ffi_s`, `s'`] mp_tac real_mc_eval_step_cases
    \\ simp [LET_THM] \\ strip_tac
    >- (
      qpat_x_assum `s'.PC ∈ forge_prog_addresses ∧ _ ⇒ _` (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac)
      \\ `evaluate rmc ffi_s ck' (arm8$Next s') = (Halt t, ms_end, st_end)` by fs []
      \\ `∀j. FST (evaluate rmc ffi_s j (arm8$Next s')) ≠ Error` by
           (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi_s j s') ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
      \\ qpat_x_assum `∀s' ffi_s. _` (qspecl_then [`arm8$Next s'`, `ffi_s`] mp_tac)
      \\ impl_tac >- (simp [] \\ metis_tac [])
      \\ strip_tac
      \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
      \\ simp []
      \\ ONCE_REWRITE_TAC [relationTheory.RTC_CASES1] \\ disj2_tac
      \\ qexists_tac `([], out_cur, arm8$Next s')`
      \\ simp [whole_step_def])
    >- (
      qspec_then `s'` mp_tac cake_exit_to_svc_exit_group \\ simp [LET_THM] \\ strip_tac
      \\ qexists_tac `[]` \\ qexists_tac `out_cur` \\ qexists_tac `FUNPOW arm8$Next k s'`
      \\ qexists_tac `if s'.REG 0w = 0w then 0w else 1w`
      \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `k` \\ simp [])
    >- (
      qspec_then `s'` mp_tac cake_install_to_svc_exit_group \\ simp [LET_THM] \\ strip_tac
      \\ qexists_tac `[]` \\ qexists_tac `out_cur` \\ qexists_tac `FUNPOW arm8$Next 3 s'`
      \\ qexists_tac `2w`
      \\ simp [] \\ irule det_run_imp_rtc \\ qexists_tac `3` \\ simp [])
    >- (
      (* FFI impossible after event_is_err! *)
      `∃bytes' bytes2'.
         read_bytearray (s'.REG 0w) (w2n (s'.REG 1w))
           (λa. if a ∈ forge_prog_addresses then SOME (s'.MEM a) else NONE) = SOME bytes' ∧
         read_bytearray (s'.REG 2w) (w2n (s'.REG 3w))
           (λa. if a ∈ forge_prog_addresses then SOME (s'.MEM a) else NONE) = SOME bytes2'` by metis_tac []
      \\ qspecl_then [`ffi_s`, `bytes'`, `bytes2'`] mp_tac
           (SIMP_RULE (srw_ss()) [LET_THM] counter_ffi_call_send16)
      \\ simp [] \\ strip_tac
      \\ rename1 `call_FFI ffi_s _ _ _ = FFI_return ffi_next new_bs_next`
      \\ `evaluate rmc ffi_s (SUC ck') s' =
          evaluate rmc ffi_next ck' (mk_real_ffi_if (noerr_ffi_P tail_bs) 0 (0, new_bs_next, s'))` by (
           CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
           \\ simp [Abbr `rmc`, real_mc_def, forge_mc_with_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi_if, noerr_ffi_P_shift, forge_veneer_facts])
      \\ `ffi_next.io_events ≼ st_end.io_events` by (
           qspecl_then [`rmc`, `ffi_next`, `ck'`, `mk_real_ffi_if (noerr_ffi_P tail_bs) 0 (0, new_bs_next, s')`]
             mp_tac targetPropsTheory.evaluate_io_events_mono
           \\ gvs [])
      \\ `ffi_s.io_events ≼ st_end.io_events` by
           (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi_next.io_events` \\ simp [IS_PREFIX_APPEND])
      \\ `st_end.io_events = ffi_s.io_events` by (irule stop_after_err_prefix_eq \\ metis_tac [])
      \\ qpat_x_assum `ffi_next.io_events ≼ st_end.io_events` mp_tac
      \\ simp [IS_PREFIX_APPEND] \\ strip_tac
      \\ `LENGTH st_end.io_events = LENGTH (ffi_next.io_events ++ l)` by simp []
      \\ fs [])
    \\ `∃bytes' bytes2'.
          read_bytearray (s'.REG 0w) (w2n (s'.REG 1w))
            (λa. if a ∈ forge_prog_addresses then SOME (s'.MEM a) else NONE) = SOME bytes' ∧
          read_bytearray (s'.REG 2w) (w2n (s'.REG 3w))
            (λa. if a ∈ forge_prog_addresses then SOME (s'.MEM a) else NONE) = SOME bytes2'` by metis_tac []
    \\ qspecl_then [`ffi_s`, `bytes'`, `bytes2'`] mp_tac counter_ffi_call_recv16
    \\ simp [] \\ strip_tac
    \\ rename1 `call_FFI ffi_s _ _ _ = FFI_return ffi_next new_bs_next`
    \\ `evaluate rmc ffi_s (SUC ck') s' =
        evaluate rmc ffi_next ck' (mk_real_ffi_if (noerr_ffi_P tail_bs) 0 (1, new_bs_next, s'))` by (
         CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc`, real_mc_def, forge_mc_with_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi_if, noerr_ffi_P_shift, forge_veneer_facts])
    \\ `ffi_next.io_events ≼ st_end.io_events` by (
         qspecl_then [`rmc`, `ffi_next`, `ck'`, `mk_real_ffi_if (noerr_ffi_P tail_bs) 0 (1, new_bs_next, s')`]
           mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ gvs [])
    \\ `ffi_s.io_events ≼ st_end.io_events` by
         (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi_next.io_events` \\ simp [IS_PREFIX_APPEND])
    \\ `st_end.io_events = ffi_s.io_events` by (irule stop_after_err_prefix_eq \\ metis_tac [])
    \\ qpat_x_assum `ffi_next.io_events ≼ st_end.io_events` mp_tac
    \\ simp [IS_PREFIX_APPEND] \\ strip_tac
    \\ `LENGTH st_end.io_events = LENGTH (ffi_next.io_events ++ l)` by simp []
    \\ fs [])
  \\ (* Non-empty inputs h :: rest_inps: read full 16B frame h *)
     rename1 `ffi.ffi_state.inputs = h :: rest_inps`
  \\ `LENGTH h = 16 ∧ EVERY (λf. LENGTH f = 16) rest_inps` by gvs []
  \\ `new_bs = 0w :: h ++ DROP 17 bytes2 ∧ ffi'.ffi_state = ffi.ffi_state with inputs := rest_inps` by (
       qpat_x_assum `∀f fs. _` (qspecl_then [`h`, `rest_inps`] mp_tac) \\ simp [])
  \\ `TAKE 16 h = h` by metis_tac [listTheory.TAKE_LENGTH_ID]
  \\ `TAKE 16 (DROP 1 new_bs) = h` by simp [listTheory.TAKE_APPEND1]
  \\ `∃s_ex. noerr_ffi_P tail_bs 0 1 new_bs s s_ex ∧ ffi_return_ok new_bs s s_ex` by (
       drule_all ffirecv16_noerr_exists \\ strip_tac
       \\ qpat_x_assum `∀f. 17 ≤ _ ∧ LENGTH f = 16 ⇒ _` (qspec_then `h` mp_tac) \\ simp [] \\ strip_tac
       \\ qexists_tac `s'` \\ simp [noerr_ffi_P_def, listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt])
  \\ `noerr_ffi_P tail_bs 0 1 new_bs s s1 ∧ ffi_return_ok new_bs s s1` by (
       simp [Abbr `s1`, mk_real_ffi_if_def]
       \\ IF_CASES_TAC >- (SELECT_ELIM_TAC \\ conj_tac >- metis_tac [] \\ simp [])
       \\ fs [] \\ metis_tac [])
  \\ `RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
        (h ++ (FLAT rest_inps ++ tail_bs), out_cur, s) (FLAT rest_inps ++ tail_bs, out_cur, s1)` by (
       qpat_x_assum `noerr_ffi_P _ _ _ _ _ _` mp_tac
       \\ simp [noerr_ffi_P_def, listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt])
  \\ `EVERY ($~ o event_is_err) ffi'.io_events` by (
       fs [event_is_err_def, listTheory.LENGTH_ZIP]
       \\ `LENGTH (0w :: h ++ DROP 17 bytes2) = LENGTH bytes2` by simp []
       \\ Cases_on `bytes2` \\ fs [listTheory.ZIP])
  \\ qpat_x_assum `∀B tail_bs ffi s. _`
       (qspecl_then [`B`, `tail_bs`, `ffi'`, `s1`, `FLAT rest_inps ++ tail_bs`, `out_cur`, `t`, `ms_end`, `st_end`] mp_tac)
  \\ simp [LET_THM]
  \\ impl_tac >- gvs [ffi_return_ok_def]
  \\ strip_tac
  \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
  \\ simp [] \\ fs [] \\ metis_tac [relationTheory.RTC_RTC]
QED

(* ---- 6. Conjuncts 3 & 4: Unified Universal Safety & Exactness ---- *)

Definition mk_prefix_P_def:
  mk_prefix_P (posts:arm8_state list) (k:num) (idx:num) (bs:word8 list)
              (s:arm8_state) (s':arm8_state) ⇔
    k < LENGTH posts ∧ s' = EL k posts
End

Theorem post_err_nrc_safety[local]:
  ∀n allow_err B P ffi_cur s_cur inp_cur out_cur inp_f out_f ms_f ec ck t ms_end st_end.
    let rmc = real_mc B (forge_mc_with (mk_real_ffi_if P) forge_real_install_if) in
      arm8_ok (erase s_cur) ∧ sp_ok s_cur ∧ bits_of s_cur = B ∧ shim_loaded s_cur.MEM ∧
      ffi_cur.oracle = counter_ffi_oracle ∧
      (∀j. FST (evaluate rmc ffi_cur j s_cur) ≠ Error) ∧
      evaluate rmc ffi_cur ck s_cur = (Halt t, ms_end, st_end) ∧
      stop_after_err st_end.io_events ∧
      (∃e. MEM e ffi_cur.io_events ∧ event_is_err e) ∧
      NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel)
                      (if allow_err then svc_write_rel else svc_write_noerr_rel))
          n (inp_cur, out_cur, s_cur) (inp_f, out_f, ms_f) ∧
      svc_exit_group_rel ec ms_f ⇒
      out_f = out_cur ∧
      (ec = 0w ∨ ec = 1w ∨ ec = 2w) ∧
      (ec = 0w ⇒ t = Success ∧ st_end.io_events = ffi_cur.io_events)
Proof
  completeInduct_on `n` \\ rpt gen_tac \\ simp [LET_THM]
  \\ qabbrev_tac `rmc = real_mc B (forge_mc_with (mk_real_ffi_if P) forge_real_install_if)`
  \\ strip_tac
  \\ qspecl_then [`B`, `P`, `ffi_cur`, `s_cur`] mp_tac real_mc_eval_step_cases
  \\ simp [LET_THM] \\ strip_tac
  >- (
    (* Prog address *)
    qpat_x_assum `s_cur.PC ∈ forge_prog_addresses ∧ _ ⇒ _` (fn th => mp_tac th \\ impl_tac >- simp [] \\ strip_tac)
    \\ Cases_on `n`
    >- (gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_def, is_svc0_at_def]
    \\ strip_tac
    \\ Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ `evaluate rmc ffi_cur ck' (arm8$Next s_cur) = (Halt t, ms_end, st_end)` by fs []
    \\ `∀j. FST (evaluate rmc ffi_cur j (arm8$Next s_cur)) ≠ Error` by
         (gen_tac \\ qpat_x_assum `∀j. FST (evaluate rmc ffi_cur j s_cur) ≠ Error` (qspec_then `SUC j` mp_tac) \\ simp [])
    \\ qpat_x_assum `∀m. m < SUC _ ⇒ _` (qspec_then `n'` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `B`, `P`, `ffi_cur`, `arm8$Next s_cur`,
                                `inp_cur`, `out_cur`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `ck'`, `t`, `ms_end`, `st_end`] mp_tac)
    \\ simp [LET_THM] \\ impl_tac >- (simp [] \\ metis_tac []) \\ simp [])
  >- (
    (* Exit veneer *)
    drule_all cake_exit_universal \\ strip_tac
    \\ Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ qpat_x_assum `s_cur.PC = FORGE_EXIT_VENEER ⇒ _` mp_tac
    \\ impl_tac >- simp []
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ Cases_on `s_cur.REG 0w = 0w` \\ fs [])
  >- (
    (* Install veneer *)
    drule_all cake_install_universal \\ strip_tac \\ simp [])
  >- (
    (* send16 impossible after event_is_err *)
    Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
    \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
    \\ `∃bytes bytes2.
          read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
            (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
          read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
            (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes2` by metis_tac []
    \\ drule_all (SIMP_RULE (srw_ss()) [LET_THM] counter_ffi_call_send16)
    \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
    \\ `evaluate rmc ffi_cur (SUC ck') s_cur =
        evaluate (real_mc B (forge_mc_with (mk_real_ffi_if (λk. P (k + 1))) forge_real_install_if))
          ffi' ck' (mk_real_ffi_if P 0 (0, new_bs, s_cur))` by (
         CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
         \\ simp [Abbr `rmc`, real_mc_def, forge_mc_with_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi_if, forge_veneer_facts])
    \\ `ffi'.io_events ≼ st_end.io_events` by (
         qspecl_then [`real_mc B (forge_mc_with (mk_real_ffi_if (λk. P (k + 1))) forge_real_install_if)`,
                      `ffi'`, `ck'`, `mk_real_ffi_if P 0 (0, new_bs, s_cur)`]
           mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ gvs [])
    \\ `ffi_cur.io_events ≼ st_end.io_events` by
         (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi'.io_events` \\ simp [IS_PREFIX_APPEND])
    \\ `st_end.io_events = ffi_cur.io_events` by (irule stop_after_err_prefix_eq \\ metis_tac [])
    \\ qpat_x_assum `ffi'.io_events ≼ st_end.io_events` mp_tac
    \\ simp [IS_PREFIX_APPEND] \\ strip_tac
    \\ `LENGTH st_end.io_events = LENGTH (ffi'.io_events ++ l)` by simp []
    \\ fs [])
  \\ (* recv16 impossible after event_is_err *)
     Cases_on `ck` >- (qpat_x_assum `evaluate _ _ 0 _ = _` mp_tac \\ simp [Once targetSemTheory.evaluate_def])
  \\ rename1 `evaluate rmc ffi_cur (SUC ck') s_cur = _`
  \\ `∃bytes bytes2.
        read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
          (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
        read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
          (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes2` by metis_tac []
  \\ drule_all counter_ffi_call_recv16
  \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
  \\ `evaluate rmc ffi_cur (SUC ck') s_cur =
      evaluate (real_mc B (forge_mc_with (mk_real_ffi_if (λk. P (k + 1))) forge_real_install_if))
        ffi' ck' (mk_real_ffi_if P 0 (1, new_bs, s_cur))` by (
       CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [targetSemTheory.evaluate_def]))
       \\ simp [Abbr `rmc`, real_mc_def, forge_mc_with_def,
                arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                shift_mk_real_ffi_if, forge_veneer_facts])
  \\ `ffi'.io_events ≼ st_end.io_events` by (
       qspecl_then [`real_mc B (forge_mc_with (mk_real_ffi_if (λk. P (k + 1))) forge_real_install_if)`,
                    `ffi'`, `ck'`, `mk_real_ffi_if P 0 (1, new_bs, s_cur)`]
         mp_tac targetPropsTheory.evaluate_io_events_mono
       \\ gvs [])
  \\ `ffi_cur.io_events ≼ st_end.io_events` by
       (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `ffi'.io_events` \\ simp [IS_PREFIX_APPEND])
  \\ `st_end.io_events = ffi_cur.io_events` by (irule stop_after_err_prefix_eq \\ metis_tac [])
  \\ qpat_x_assum `ffi'.io_events ≼ st_end.io_events` mp_tac
  \\ simp [IS_PREFIX_APPEND] \\ strip_tac
  \\ `LENGTH st_end.io_events = LENGTH (ffi'.io_events ++ l)` by simp []
  \\ fs []
QED

Theorem pre_err_nrc_safety[local]:
  ∀n allow_err ms0 inp r w inp_cur out_cur s_cur inp_f out_f ms_f ec posts sent_so_far step_cnt.
    forge_elf_loaded code data ms0 ∧
    inp = FLAT (TAKE r (chunks16 inp)) ++ inp_cur ∧
    r ≤ LENGTH (chunks16 inp) ∧
    LENGTH sent_so_far = w ∧
    FLAT sent_so_far = out_cur ∧
    arm8_ok (erase s_cur) ∧ sp_ok s_cur ∧ bits_of s_cur = bits_of ms0 ∧ shim_loaded s_cur.MEM ∧
    (∀extra_in wlim_rem P.
       (∀j. j < LENGTH posts ⇒ ∀idx bs s s'. P j idx bs s s' ⇔ s' = EL j posts) ⇒
       let io = <| inputs := TAKE r (chunks16 inp) ++ extra_in;
                   outputs := [];
                   write_limit := OPTION_MAP (λd. w + d) wlim_rem |> in
       let rmc0 = real_mc (bits_of ms0) (forge_mc_with (mk_real_ffi_if P) forge_real_install_if) in
       let rmc_cur = real_mc (bits_of ms0)
                       (forge_mc_with (mk_real_ffi_if (λk. P (k + LENGTH posts))) forge_real_install_if) in
       ∃ffi_cur.
         ffi_cur.oracle = counter_ffi_oracle ∧
         ffi_cur.ffi_state = <| inputs := extra_in; outputs := sent_so_far; write_limit := wlim_rem |> ∧
         sent_frames_of ffi_cur.io_events = sent_so_far ∧
         (∀k. evaluate rmc0 (counter_ffi io) (step_cnt + k) (FUNPOW arm8$Next 43 ms0) =
              evaluate rmc_cur ffi_cur k s_cur)) ∧
    NRC (whole_step (if allow_err then svc_read_rel else svc_read_noerr_rel)
                    (if allow_err then svc_write_rel else svc_write_noerr_rel))
        n (inp_cur, out_cur, s_cur) (inp_f, out_f, ms_f) ∧
    svc_exit_group_rel ec ms_f ⇒
    (ec = 0w ∨ ec = 1w ∨ ec = 2w) ∧
    out_f ≼ FLAT (SND (SND (counter_run 0w 0w (chunks16 inp)))) ∧
    (¬allow_err ∧ ec = 0w ⇒ out_f = FLAT (SND (SND (counter_run 0w 0w (chunks16 inp)))))
Proof
  completeInduct_on `n` \\ rpt gen_tac \\ strip_tac
  \\ qabbrev_tac `P0 = mk_prefix_P posts`
  \\ `∀j. j < LENGTH posts ⇒ ∀idx bs s s'. P0 j idx bs s s' ⇔ s' = EL j posts` by
       simp [Abbr `P0`, mk_prefix_P_def]
  \\ `∃ffi0.
        let io0 = <| inputs := chunks16 inp; outputs := []; write_limit := NONE |> in
        let rmc0 = real_mc (bits_of ms0) (forge_mc_with (mk_real_ffi_if P0) forge_real_install_if) in
        let rmc_c = real_mc (bits_of ms0)
                      (forge_mc_with (mk_real_ffi_if (λk. P0 (k + LENGTH posts))) forge_real_install_if) in
        ffi0.oracle = counter_ffi_oracle ∧
        ffi0.ffi_state = <| inputs := chunks16 inp_cur; outputs := sent_so_far; write_limit := NONE |> ∧
        sent_frames_of ffi0.io_events = sent_so_far ∧
        (∀k. evaluate rmc0 (counter_ffi io0) (step_cnt + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate rmc_c ffi0 k s_cur) ∧
        (∀j. FST (evaluate rmc_c ffi0 j s_cur) ≠ Error)` by (
       drule_all chunks16_drop_eq \\ strip_tac
       \\ qpat_x_assum `chunks16 inp = _` (assume_tac o SYM)
       \\ qpat_assum `∀extra_in wlim_rem P. _`
            (qspecl_then [`chunks16 inp_cur`, `NONE`, `P0`] mp_tac)
       \\ impl_tac >- simp []
       \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
       \\ qexists_tac `ffi_cur` \\ gvs [LET_THM]
       \\ qspecl_then [`ms0`, `<| inputs := chunks16 inp; outputs := []; write_limit := NONE |>`,
                       `mk_real_ffi_if P0`, `forge_real_install_if`] mp_tac forge_compile_exact
       \\ simp [LET_THM, mk_real_ffi_if_ok] \\ strip_tac
       \\ gen_tac
       \\ qpat_x_assum `∀j. FST (evaluate _ _ j _) ≠ Error` (qspec_then `step_cnt + j` mp_tac) \\ simp [])
  \\ pop_assum (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
  \\ qspecl_then [`bits_of ms0`, `λk. P0 (k + LENGTH posts)`, `ffi0`, `s_cur`] mp_tac
       real_mc_eval_step_cases
  \\ simp [LET_THM] \\ strip_tac
  >- (
    (* Case 1: Normal instruction in forge_prog_addresses *)
    first_x_assum drule \\ strip_tac
    \\ Cases_on `n`
    >- (gvs [arithmeticTheory.NRC, svc_exit_group_rel_def, is_svc0_at_def])
    \\ qpat_x_assum `NRC _ (SUC _) _ _` mp_tac
    \\ simp [arithmeticTheory.NRC, pairTheory.EXISTS_PROD, whole_step_def, is_svc0_at_def]
    \\ strip_tac
    \\ qpat_x_assum `∀m. m < SUC n' ⇒ _` (qspec_then `n'` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_then (qspecl_then [`allow_err`, `ms0`, `inp`, `r`, `w`, `inp_cur`, `out_cur`,
                                `arm8$Next s_cur`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `posts`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ impl_tac
    >- (
      simp [] \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- simp []
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ qexists_tac `ffi_cur` \\ simp []
      \\ qspecl_then [`ms0`, `<| inputs := TAKE r (chunks16 inp) ++ extra_in; outputs := [];
                                 write_limit := OPTION_MAP (λd. w + d) wlim_rem |>`,
                      `mk_real_ffi_if P`, `forge_real_install_if`] mp_tac forge_compile_exact
      \\ simp [LET_THM, mk_real_ffi_if_ok]
      \\ disch_then (assume_tac o cj 3)
      \\ `∀j. FST (evaluate (real_mc (bits_of ms0)
                      (forge_mc_with (mk_real_ffi_if (λk. P (k + LENGTH posts))) forge_real_install_if))
                    ffi_cur j s_cur) ≠ Error` by
           (gen_tac \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + j` mp_tac) \\ simp [])
      \\ qspecl_then [`bits_of ms0`, `λk. P (k + LENGTH posts)`, `ffi_cur`, `s_cur`] mp_tac
           real_mc_eval_step_cases
      \\ `s_cur.PC ≠ FORGE_EXIT_VENEER ∧ s_cur.PC ≠ FORGE_INSTALL_VENEER ∧
          s_cur.PC ≠ FORGE_FFISEND16_VENEER ∧ s_cur.PC ≠ FORGE_FFIRECV16_VENEER` by
           metis_tac [forge_veneer_facts]
      \\ simp [LET_THM] \\ strip_tac
      \\ gen_tac
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp []
  )
  >- (
    (* Case 2: Exit veneer *)
    drule_all cake_exit_universal \\ strip_tac
    \\ qspecl_then [`ms0`, `<| inputs := chunks16 inp; outputs := []; write_limit := NONE |>`,
                    `mk_real_ffi_if P0`, `forge_real_install_if`] mp_tac forge_compile_exact
    \\ simp [LET_THM, mk_real_ffi_if_ok]
    \\ disch_then (assume_tac o cj 5)
    \\ `evaluate (real_mc (bits_of ms0) (forge_mc_with (mk_real_ffi_if P0) forge_real_install_if))
          (counter_ffi <| inputs := chunks16 inp; outputs := []; write_limit := NONE |>)
          (step_cnt + 1) (FUNPOW arm8$Next 43 ms0) =
        (if s_cur.REG 0w = 0w then Halt Success else Halt Resource_limit_hit, s_cur, ffi0)` by
         (qpat_x_assum `s_cur.PC = FORGE_EXIT_VENEER ⇒ _` mp_tac
          \\ impl_tac >- simp []
          \\ disch_then (qspec_then `0` assume_tac)
          \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = _` (qspec_then `SUC 0` mp_tac)
          \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ qpat_x_assum `∀ck t ms_end st_end. _`
         (qspecl_then [`step_cnt + 1`,
                       `if s_cur.REG 0w = 0w then Success else Resource_limit_hit`,
                       `s_cur`, `ffi0`] mp_tac)
    \\ simp [limit_frames_def]
    \\ (Cases_on `s_cur.REG 0w = 0w` \\ simp [])
    >- (strip_tac \\ rveq \\ simp [])
    \\ strip_tac \\ rveq \\ irule FLAT_prefix \\ simp []
  )
  >- (
    (* Case 3: Install veneer *)
    drule_all cake_install_universal \\ strip_tac
    \\ qspecl_then [`ms0`, `<| inputs := chunks16 inp; outputs := []; write_limit := NONE |>`,
                    `mk_real_ffi_if P0`, `forge_real_install_if`] mp_tac forge_compile_exact
    \\ simp [LET_THM, mk_real_ffi_if_ok] \\ strip_tac
    \\ `evaluate (real_mc (bits_of ms0) (forge_mc_with (mk_real_ffi_if P0) forge_real_install_if))
          (counter_ffi <| inputs := chunks16 inp; outputs := []; write_limit := NONE |>)
          (step_cnt + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by
         (`step_cnt + ck = ck + step_cnt` by decide_tac \\ pop_assum SUBST1_TAC
          \\ irule targetPropsTheory.evaluate_add_clock \\ simp [])
    \\ `ffi0.io_events ≼ st_end.io_events` by (
         qspecl_then [`real_mc (bits_of ms0)
                        (forge_mc_with (mk_real_ffi_if (λk. P0 (k + LENGTH posts))) forge_real_install_if)`,
                      `ffi0`, `ck`, `s_cur`] mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ gvs [])
    \\ `sent_frames_of ffi0.io_events ≼ sent_frames_of st_end.io_events` by simp [sent_frames_of_prefix]
    \\ `sent_frames_of st_end.io_events ≼ SND (SND (counter_run 0w 0w (chunks16 inp)))` by
         fs [limit_frames_def]
    \\ `sent_so_far ≼ SND (SND (counter_run 0w 0w (chunks16 inp)))` by
         (irule rich_listTheory.IS_PREFIX_TRANS \\ qexists_tac `sent_frames_of st_end.io_events`
          \\ qpat_x_assum `sent_frames_of ffi0.io_events ≼ _` mp_tac \\ simp [])
    \\ rveq \\ simp [FLAT_prefix]
  )
  >- (
    (* Case 4: send16 veneer *)
    `∃bytes bytes2.
       read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
         (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
       read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
         (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes2 ∧
       aligned 2 (s_cur.REG 30w) ∧ untagged (s_cur.REG 30w)` by simp []
    \\ imp_res_tac read_bytearray_mem_eq
    \\ drule_all ffisend16_universal \\ strip_tac
    \\ Cases_on `w2n (s_cur.REG 3w) < 17`
    >- (
      (* Subcase 4a: short send16 (<17B) *)
      first_x_assum drule \\ strip_tac
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`allow_err`, `ms0`, `inp`, `r`, `w`, `inp_cur`, `out_cur`,
                                  `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                  `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
      \\ impl_tac
      >- (
        simp [] \\ rpt conj_tac >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
        >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_rem`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] counter_ffi_call_send16)
        \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
        \\ qexists_tac `ffi'` \\ simp []
        \\ `mk_real_ffi_if (λk. P (k + LENGTH posts)) 0 (0, bytes2, s_cur) = s'` by (
             irule mk_real_ffi_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_mc_with (mk_real_ffi_if (λk. P (k + LENGTH posts))) forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_mc_with (mk_real_ffi_if (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_with_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_ffi_if]
             \\ `FORGE_FFISEND16_VENEER ∉ forge_prog_addresses ∧
                 FORGE_FFISEND16_VENEER ≠ FORGE_EXIT_VENEER ∧
                 FORGE_FFISEND16_VENEER ≠ FORGE_INSTALL_VENEER` by
                  simp [forge_veneer_facts]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ fs [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp []
    )
    \\ `17 ≤ w2n (s_cur.REG 3w)` by decide_tac
      \\ first_x_assum drule \\ strip_tac
    >- (
      (* Subcase 4b: full 16B write *)
      qabbrev_tac `frame = TAKE 16 (DROP 1 bytes2)`
      \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
      \\ disch_then (qspecl_then [`allow_err`, `ms0`, `inp`, `r`, `w + 1`, `inp_cur`,
                                  `out_cur ++ frame`, `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                  `posts ++ [s']`, `sent_so_far ++ [frame]`, `step_cnt + 1`] mp_tac)
      \\ impl_tac
      >- (
        simp [listTheory.FLAT_APPEND] \\ rpt conj_tac >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
        >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
        \\ rpt gen_tac \\ strip_tac
        \\ qabbrev_tac `wlim_prev = OPTION_MAP SUC wlim_rem`
        \\ `OPTION_MAP (λd. d + w) wlim_prev = OPTION_MAP (λd. d + (w + 1)) wlim_rem` by
             (Cases_on `wlim_rem` \\ simp [Abbr `wlim_prev`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
        \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_prev`, `P`] mp_tac)
        \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
        \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
        \\ drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] counter_ffi_call_send16)
        \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
        \\ `new_bs = 0w :: DROP 1 bytes2 ∧
            ffi'.ffi_state = <| inputs := extra_in; outputs := sent_so_far ++ [frame];
                                write_limit := wlim_rem |>` by (
             Cases_on `wlim_rem` \\ fs [Abbr `wlim_prev`, Abbr `frame`, counter_io_component_equality])
        \\ qexists_tac `ffi'` \\ simp [Abbr `frame`]
        \\ `mk_real_ffi_if (λk. P (k + LENGTH posts)) 0 (0, 0w :: DROP 1 bytes2, s_cur) = s'` by (
             irule mk_real_ffi_if_select \\ simp []
             \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
             \\ simp [rich_listTheory.EL_LENGTH_APPEND])
        \\ `∀k. evaluate (real_mc (bits_of ms0)
                  (forge_mc_with (mk_real_ffi_if (λk. P (k + LENGTH posts))) forge_real_install_if))
                ffi_cur (SUC k) s_cur =
                evaluate (real_mc (bits_of ms0)
                  (forge_mc_with (mk_real_ffi_if (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
                ffi' k s'` by (
             gen_tac
             \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_with_def,
                      arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                      targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                      targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                      shift_mk_real_ffi_if]
             \\ `FORGE_FFISEND16_VENEER ∉ forge_prog_addresses ∧
                 FORGE_FFISEND16_VENEER ≠ FORGE_EXIT_VENEER ∧
                 FORGE_FFISEND16_VENEER ≠ FORGE_INSTALL_VENEER` by
                  simp [forge_veneer_facts]
             \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                  (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
             \\ fs [])
        \\ gen_tac
        \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
        \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
      \\ simp []
    )
    \\ (* Subcase 4c: allow_err = T, partial/error write chunk ≼ frame *)
      qabbrev_tac `frame = TAKE 16 (DROP 1 bytes2)`
      \\ qabbrev_tac `P1 = mk_prefix_P (posts ++ [s'])`
      \\ drule_all chunks16_drop_eq \\ strip_tac
      \\ qpat_x_assum `chunks16 inp = _` (assume_tac o SYM)
      \\ qpat_assum `∀extra_in wlim_rem P. _`
           (qspecl_then [`chunks16 inp_cur`, `SOME 0`, `P1`] mp_tac)
      \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix_P_def, rich_listTheory.EL_APPEND1])
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac
           (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM] counter_ffi_call_send16)
      \\ simp [] \\ strip_tac
      \\ `sent_frames_of ffi'.io_events = sent_so_far ++ [frame]` by simp [Abbr `frame`]
      \\ `mk_real_ffi_if (λk. P1 (k + LENGTH posts)) 0 (0, 1w :: DROP 1 bytes2, s_cur) = s'` by (
           irule mk_real_ffi_if_select \\ simp [Abbr `P1`, mk_prefix_P_def, rich_listTheory.EL_LENGTH_APPEND])
      \\ qabbrev_tac `io_err = <| inputs := chunks16 inp; outputs := []; write_limit := SOME w |>`
      \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0) (forge_mc_with (mk_real_ffi_if P1) forge_real_install_if)`
      \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                       (forge_mc_with (mk_real_ffi_if (λk. P1 (k + (LENGTH posts + 1)))) forge_real_install_if)`
      \\ `∀k. evaluate rmc1 (counter_ffi io_err) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
              evaluate rmc_post ffi' k s'` by (
           gen_tac
           \\ `evaluate rmc1 (counter_ffi io_err) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
               evaluate (real_mc (bits_of ms0)
                 (forge_mc_with (mk_real_ffi_if (λk. P1 (k + LENGTH posts))) forge_real_install_if))
                 ffi_cur (SUC k) s_cur` by (
                qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
                \\ simp [Abbr `io_err`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
           \\ pop_assum SUBST1_TAC
           \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc_post`, real_mc_def, forge_mc_with_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi_if, forge_veneer_facts]
           \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
                (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
           \\ simp [])
      \\ qspecl_then [`ms0`, `<| inputs := chunks16 inp; outputs := []; write_limit := SOME w |>`,
                      `mk_real_ffi_if P1`, `forge_real_install_if`] mp_tac
           forge_compile_exact
      \\ simp [LET_THM, mk_real_ffi_if_ok]
      \\ disch_then (fn th => assume_tac (cj 3 th) \\ strip_assume_tac (cj 4 th))
      \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
           `evaluate rmc1 (counter_ffi <|inputs := chunks16 inp; outputs := []; write_limit := SOME w|>)
              (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
                `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
                \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
           \\ pop_assum mp_tac
           \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
           \\ simp [Abbr `io_err`])
      \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
           gen_tac
           \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
           \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
           \\ simp [Abbr `rmc1`, Abbr `io_err`])
      \\ qspecl_then [`n'`, `allow_err`, `bits_of ms0`, `λk. P1 (k + (LENGTH posts + 1))`,
                      `ffi'`, `s'`, `inp_cur`, `out_cur ++ chunk`, `inp_f`, `out_f`, `ms_f`, `ec`,
                      `ck`, `t`, `ms_end`, `st_end`] mp_tac post_err_nrc_safety
      \\ simp [LET_THM]
      \\ (impl_tac >- (
           qpat_x_assum `ffi_return_ok _ _ _` (strip_assume_tac o REWRITE_RULE [ffi_return_ok_def])
           \\ qpat_x_assum `event_is_err _` mp_tac
           \\ qpat_x_assum `NRC _ n' _ _` mp_tac
           \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
           \\ qpat_x_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
           \\ simp [Abbr `rmc_post`, boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]))
      \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
      \\ simp []
      \\ `ffi'.io_events ≼ st_end.io_events` by (
           qspecl_then [`rmc_post`, `ffi'`, `ck`, `s'`] mp_tac targetPropsTheory.evaluate_io_events_mono
           \\ simp [])
      \\ `sent_so_far ++ [frame] ≼ SND (SND (counter_run 0w 0w (chunks16 inp)))` by (
           `sent_frames_of ffi'.io_events ≼ sent_frames_of st_end.io_events` by simp [sent_frames_of_prefix]
           \\ `sent_frames_of st_end.io_events ≼ limit_frames (SOME w) (SND (SND (counter_run 0w 0w (chunks16 inp))))` by simp []
           \\ `limit_frames (SOME w) (SND (SND (counter_run 0w 0w (chunks16 inp)))) ≼
               SND (SND (counter_run 0w 0w (chunks16 inp)))` by simp [limit_frames_prefix]
           \\ irule rich_listTheory.IS_PREFIX_TRANS
           \\ qexists_tac `sent_frames_of st_end.io_events`
           \\ (conj_tac
               >- (irule rich_listTheory.IS_PREFIX_TRANS
                   \\ qexists_tac `limit_frames (SOME w) (SND (SND (counter_run 0w 0w (chunks16 inp))))`
                   \\ simp []))
           \\ qpat_x_assum `sent_frames_of ffi'.io_events ≼ _` mp_tac \\ simp [Abbr `frame`])
      \\ `out_cur ++ chunk ≼ FLAT (sent_so_far ++ [frame])` by
           (qpat_x_assum `FLAT sent_so_far = out_cur` (SUBST1_TAC o SYM) \\ simp [FLAT_snoc_prefix])
      \\ `FLAT (sent_so_far ++ [frame]) ≼ FLAT (SND (SND (counter_run 0w 0w (chunks16 inp))))` by
           simp [FLAT_prefix]
      \\ irule rich_listTheory.IS_PREFIX_TRANS
      \\ qexists_tac `FLAT (sent_so_far ++ [frame])` \\ simp []
  )
  \\ (* Case 5: recv16 veneer *)
    `∃bytes bytes2.
       read_bytearray (s_cur.REG 0w) (w2n (s_cur.REG 1w))
         (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes ∧
       read_bytearray (s_cur.REG 2w) (w2n (s_cur.REG 3w))
         (λa. if a ∈ forge_prog_addresses then SOME (s_cur.MEM a) else NONE) = SOME bytes2 ∧
       aligned 2 (s_cur.REG 30w) ∧ untagged (s_cur.REG 30w)` by simp []
    \\ imp_res_tac read_bytearray_mem_eq
    \\ drule_all ffirecv16_universal \\ strip_tac
    \\ Cases_on `w2n (s_cur.REG 3w) < 17`
  >- (
    (* Subcase 5a: short recv16 (<17B) *)
    first_x_assum drule \\ strip_tac
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
    \\ disch_then (qspecl_then [`allow_err`, `ms0`, `inp`, `r`, `w`, `inp_cur`, `out_cur`,
                                `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ impl_tac
    >- (
      simp [] \\ rpt conj_tac >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
      >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
      \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`extra_in`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ drule_all counter_ffi_call_recv16
      \\ disch_then (qspecl_then [`bytes`, `bytes2`] strip_assume_tac)
      \\ qexists_tac `ffi'` \\ simp []
      \\ `mk_real_ffi_if (λk. P (k + LENGTH posts)) 0 (1, bytes2, s_cur) = s'` by (
           irule mk_real_ffi_if_select \\ simp []
           \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
           \\ simp [rich_listTheory.EL_LENGTH_APPEND])
      \\ `∀k. evaluate (real_mc (bits_of ms0)
                (forge_mc_with (mk_real_ffi_if (λk. P (k + LENGTH posts))) forge_real_install_if))
              ffi_cur (SUC k) s_cur =
              evaluate (real_mc (bits_of ms0)
                (forge_mc_with (mk_real_ffi_if (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
              ffi' k s'` by (
           gen_tac
           \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_with_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi_if]
           \\ `FORGE_FFIRECV16_VENEER ∉ forge_prog_addresses ∧
               FORGE_FFIRECV16_VENEER ≠ FORGE_EXIT_VENEER ∧
               FORGE_FFIRECV16_VENEER ≠ FORGE_INSTALL_VENEER ∧
               FORGE_FFIRECV16_VENEER ≠ FORGE_FFISEND16_VENEER` by
                simp [forge_veneer_facts]
           \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
           \\ fs [])
      \\ gen_tac
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp []
  )
  \\ `17 ≤ w2n (s_cur.REG 3w)` by decide_tac
    \\ first_x_assum drule
    \\ disch_then (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (EVERY o map assume_tac o CONJUNCTS)))
  >- (
    (* Subcase 5b: read full 16B frame *)
    drule_all chunks16_take_step \\ strip_tac
    \\ qpat_x_assum `∀m. m < n ⇒ _` (qspec_then `n'` mp_tac) \\ impl_tac >- simp []
    \\ disch_then (qspecl_then [`allow_err`, `ms0`, `inp`, `r + 1`, `w`, `inp_after`, `out_cur`,
                                `s'`, `inp_f`, `out_f`, `ms_f`, `ec`,
                                `posts ++ [s']`, `sent_so_far`, `step_cnt + 1`] mp_tac)
    \\ impl_tac
    >- (
      simp [] \\ rpt conj_tac >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
      >- fs [ffi_return_ok_def] >- fs [ffi_return_ok_def]
      \\ rpt gen_tac \\ strip_tac
      \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`frame :: extra_in`, `wlim_rem`, `P`] mp_tac)
      \\ impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `j` mp_tac) \\ simp [rich_listTheory.EL_APPEND1])
      \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
      \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac counter_ffi_call_recv16
      \\ simp [] \\ strip_tac
      \\ `ffi'.ffi_state = <| inputs := extra_in; outputs := sent_so_far; write_limit := wlim_rem |>` by
           simp [counter_io_component_equality]
      \\ qexists_tac `ffi'` \\ simp []
      \\ `mk_real_ffi_if (λk. P (k + LENGTH posts)) 0 (1, 0w :: frame ++ DROP 17 bytes2, s_cur) = s'` by (
           irule mk_real_ffi_if_select \\ simp []
           \\ qpat_x_assum `∀j. j < LENGTH posts + 1 ⇒ _` (qspec_then `LENGTH posts` mp_tac)
           \\ simp [rich_listTheory.EL_LENGTH_APPEND])
      \\ `∀k. evaluate (real_mc (bits_of ms0)
                (forge_mc_with (mk_real_ffi_if (λk. P (k + LENGTH posts))) forge_real_install_if))
              ffi_cur (SUC k) s_cur =
              evaluate (real_mc (bits_of ms0)
                (forge_mc_with (mk_real_ffi_if (λk. P (k + (LENGTH posts + 1)))) forge_real_install_if))
              ffi' k s'` by (
           gen_tac
           \\ simp [Once targetSemTheory.evaluate_def, real_mc_def, forge_mc_with_def,
                    arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                    targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                    targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                    shift_mk_real_ffi_if]
           \\ `FORGE_FFIRECV16_VENEER ∉ forge_prog_addresses ∧
               FORGE_FFIRECV16_VENEER ≠ FORGE_EXIT_VENEER ∧
               FORGE_FFIRECV16_VENEER ≠ FORGE_INSTALL_VENEER ∧
               FORGE_FFIRECV16_VENEER ≠ FORGE_FFISEND16_VENEER` by
                simp [forge_veneer_facts]
           \\ `(λk. P (k + 1 + LENGTH posts)) = (λk. P (k + (LENGTH posts + 1)))` by
                (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
           \\ fs [])
      \\ gen_tac
      \\ `TAKE r (chunks16 inp) ++ [frame] ++ extra_in = TAKE r (chunks16 inp) ++ frame :: extra_in` by
           REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
      \\ qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
      \\ simp [arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
    \\ simp []
  )
  \\ (* Subcase 5c: EOF / truncated <16B / read error *)
    qabbrev_tac `P1 = mk_prefix_P (posts ++ [s'])`
    \\ qpat_assum `∀extra_in wlim_rem P. _` (qspecl_then [`[]`, `NONE`, `P1`] mp_tac)
    \\ impl_tac >- (rpt strip_tac \\ simp [Abbr `P1`, mk_prefix_P_def, rich_listTheory.EL_APPEND1])
    \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [LET_THM])
    \\ qspecl_then [`ffi_cur`, `bytes`, `bytes2`] mp_tac counter_ffi_call_recv16
    \\ simp [] \\ strip_tac
    \\ `mk_real_ffi_if (λk. P1 (k + LENGTH posts)) 0 (1, 1w :: DROP 1 bytes2, s_cur) = s'` by (
         irule mk_real_ffi_if_select \\ simp [Abbr `P1`, mk_prefix_P_def, rich_listTheory.EL_LENGTH_APPEND])
    \\ qabbrev_tac `io_eof = <| inputs := TAKE r (chunks16 inp); outputs := []; write_limit := NONE |>`
    \\ qabbrev_tac `rmc1 = real_mc (bits_of ms0) (forge_mc_with (mk_real_ffi_if P1) forge_real_install_if)`
    \\ qabbrev_tac `rmc_post = real_mc (bits_of ms0)
                     (forge_mc_with (mk_real_ffi_if (λk. P1 (k + (LENGTH posts + 1)))) forge_real_install_if)`
    \\ `∀k. evaluate rmc1 (counter_ffi io_eof) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
            evaluate rmc_post ffi' k s'` by (
         gen_tac
         \\ `evaluate rmc1 (counter_ffi io_eof) (step_cnt + 1 + k) (FUNPOW arm8$Next 43 ms0) =
             evaluate (real_mc (bits_of ms0)
               (forge_mc_with (mk_real_ffi_if (λk. P1 (k + LENGTH posts))) forge_real_install_if))
               ffi_cur (SUC k) s_cur` by (
              qpat_x_assum `∀k. evaluate _ _ _ (FUNPOW _ _ _) = evaluate _ ffi_cur _ _` (qspec_then `SUC k` mp_tac)
              \\ simp [Abbr `io_eof`, Abbr `rmc1`, arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES])
         \\ pop_assum SUBST1_TAC
         \\ simp [Once targetSemTheory.evaluate_def, Abbr `rmc_post`, real_mc_def, forge_mc_with_def,
                  arm8_target_real_def, arm8_targetTheory.arm8_target_def,
                  targetSemTheory.apply_oracle_def, miscTheory.find_index_def,
                  targetSemTheory.read_ffi_bytearrays_def, targetSemTheory.read_ffi_bytearray_def,
                  shift_mk_real_ffi_if, forge_veneer_facts]
         \\ `(λk. P1 (k + 1 + LENGTH posts)) = (λk. P1 (k + (LENGTH posts + 1)))` by
              (simp [FUN_EQ_THM] \\ gen_tac \\ AP_TERM_TAC \\ decide_tac)
         \\ simp [])
    \\ qspecl_then [`ms0`, `<| inputs := TAKE r (chunks16 inp); outputs := []; write_limit := NONE |>`,
                    `mk_real_ffi_if P1`, `forge_real_install_if`] mp_tac
         forge_compile_exact
    \\ simp [LET_THM, mk_real_ffi_if_ok, limit_frames_def]
    \\ disch_then (fn th => assume_tac (cj 3 th) \\ strip_assume_tac (cj 4 th))
    \\ `evaluate rmc_post ffi' ck s' = (Halt t, ms_end, st_end)` by (
         `evaluate rmc1 (counter_ffi <|inputs := TAKE r (chunks16 inp); outputs := []; write_limit := NONE|>)
            (step_cnt + 1 + ck) (FUNPOW arm8$Next 43 ms0) = (Halt t, ms_end, st_end)` by (
              `step_cnt + 1 + ck = ck + (step_cnt + 1)` by decide_tac \\ pop_assum SUBST1_TAC
              \\ irule targetPropsTheory.evaluate_add_clock \\ simp [Abbr `rmc1`])
         \\ pop_assum mp_tac
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `ck` mp_tac)
         \\ simp [Abbr `io_eof`])
    \\ `∀j. FST (evaluate rmc_post ffi' j s') ≠ Error` by (
         gen_tac
         \\ qpat_x_assum `∀j. FST (evaluate _ _ j (FUNPOW _ _ _)) ≠ Error` (qspec_then `step_cnt + 1 + j` mp_tac)
         \\ qpat_assum `∀k. evaluate rmc1 _ _ _ = _` (qspec_then `j` mp_tac)
         \\ simp [Abbr `rmc1`, Abbr `io_eof`])
    \\ qspecl_then [`n'`, `allow_err`, `bits_of ms0`, `λk. P1 (k + (LENGTH posts + 1))`,
                    `ffi'`, `s'`, `inp_after`, `out_cur`, `inp_f`, `out_f`, `ms_f`, `ec`,
                    `ck`, `t`, `ms_end`, `st_end`] mp_tac post_err_nrc_safety
    \\ simp [LET_THM]
    \\ (impl_tac >- (
         qpat_x_assum `ffi_return_ok _ _ _` (strip_assume_tac o REWRITE_RULE [ffi_return_ok_def])
         \\ qpat_x_assum `event_is_err _` mp_tac
         \\ qpat_x_assum `NRC _ n' _ _` mp_tac
         \\ qpat_assum `evaluate rmc_post _ _ _ = _` mp_tac
         \\ qpat_x_assum `∀j. FST (evaluate rmc_post _ _ _) ≠ Error` mp_tac
         \\ simp [Abbr `rmc_post`, boolTheory.RIGHT_AND_OVER_OR, boolTheory.EXISTS_OR_THM]))
    \\ disch_then (EVERY o map assume_tac o CONJUNCTS)
    \\ simp []
    \\ `ffi'.io_events ≼ st_end.io_events` by (
         qspecl_then [`rmc_post`, `ffi'`, `ck`, `s'`] mp_tac targetPropsTheory.evaluate_io_events_mono
         \\ simp [])
    \\ `out_cur ≼ FLAT (SND (SND (counter_run 0w 0w (chunks16 inp))))` by (
         `sent_so_far ≼ SND (SND (counter_run 0w 0w (TAKE r (chunks16 inp))))` by (
           `sent_frames_of ffi'.io_events ≼ sent_frames_of st_end.io_events` by simp [sent_frames_of_prefix]
           \\ `sent_frames_of st_end.io_events ≼ SND (SND (counter_run 0w 0w (TAKE r (chunks16 inp))))` by simp []
           \\ irule rich_listTheory.IS_PREFIX_TRANS
           \\ qexists_tac `sent_frames_of st_end.io_events`
           \\ qpat_x_assum `sent_frames_of ffi'.io_events ≼ _` mp_tac \\ simp [])
         \\ `SND (SND (counter_run 0w 0w (TAKE r (chunks16 inp)))) ≼
             SND (SND (counter_run 0w 0w (chunks16 inp)))` by simp [counter_run_take_prefix]
         \\ `sent_so_far ≼ SND (SND (counter_run 0w 0w (chunks16 inp)))` by
              (irule rich_listTheory.IS_PREFIX_TRANS
               \\ qexists_tac `SND (SND (counter_run 0w 0w (TAKE r (chunks16 inp))))` \\ simp [])
         \\ qpat_x_assum `FLAT sent_so_far = out_cur` (SUBST1_TAC o SYM)
         \\ simp [FLAT_prefix])
    \\ simp []
    \\ rpt strip_tac
    \\ `LENGTH inp_cur < 16` by (qpat_x_assum `allow_err ∨ _` mp_tac \\ simp [])
    \\ `TAKE r (chunks16 inp) = chunks16 inp` by (
         qspecl_then [`r`, `inp`, `inp_cur`] mp_tac chunks16_take_all_of_lt16
         \\ impl_tac >- (rpt conj_tac \\ TRY (first_assum ACCEPT_TAC) \\ simp [])
         \\ simp [])
    \\ `t = Success ∧ st_end.io_events = ffi'.io_events` by simp []
    \\ `sent_so_far = SND (SND (counter_run 0w 0w (chunks16 inp)))` by (
         qpat_x_assum `sent_frames_of st_end.io_events = _` mp_tac
         \\ qpat_x_assum `st_end.io_events = ffi'.io_events` SUBST1_TAC
         \\ qpat_x_assum `TAKE r (chunks16 inp) = chunks16 inp` SUBST1_TAC
         \\ simp [])
    \\ qpat_x_assum `FLAT sent_so_far = out_cur` (SUBST1_TAC o SYM)
    \\ simp []
QED

(* ---- 7. Top-Level Exact Term.aconv-Pinned Unified End-to-End Theorem ---- *)

Theorem forge_m1_kernel_correct:
  ∀ms0:arm8_state.
    forge_elf_loaded code data ms0 ⇒
      let ms1 = FUNPOW arm8$Next 43 ms0 in
      (∀(io:counter_io) ffi_if inst_if.
         io.outputs = [] ∧
         real_interfer_ok (bits_of ms0) ffi_if inst_if ⇒
           let rmc = real_mc (bits_of ms0) (forge_mc_with ffi_if inst_if) in
             rmc.target = arm8_target_real (bits_of ms0) ∧
             ¬machine_sem rmc (counter_ffi io) ms1 Fail) ∧
      (∀inp:word8 list.
         ∃inp_f out_f ms_f exit_code.
           RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
             (inp, [], ms0) (inp_f, out_f, ms_f) ∧
           svc_exit_group_rel exit_code ms_f) ∧
      (∀(inp:word8 list) inp_f out_f ms_f exit_code.
         RTC (whole_step svc_read_rel svc_write_rel)
           (inp, [], ms0) (inp_f, out_f, ms_f) ∧
         svc_exit_group_rel exit_code ms_f ⇒
           (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
           list$isPREFIX out_f
             (FLAT (SND (SND (counter_run 0w 0w (chunks16 inp)))))) ∧
      (∀(inp:word8 list) inp_f out_f ms_f exit_code.
         RTC (whole_step svc_read_noerr_rel svc_write_noerr_rel)
           (inp, [], ms0) (inp_f, out_f, ms_f) ∧
         svc_exit_group_rel exit_code ms_f ∧
         exit_code = 0w ⇒
           out_f = FLAT (SND (SND (counter_run 0w 0w (chunks16 inp)))))
Proof
  rpt strip_tac \\ simp [LET_THM]
  \\ `det_run 43 ms0 (FUNPOW arm8$Next 43 ms0) ∧
      arm8_ok (erase (FUNPOW arm8$Next 43 ms0)) ∧
      sp_ok (FUNPOW arm8$Next 43 ms0) ∧
      bits_of (FUNPOW arm8$Next 43 ms0) = bits_of ms0 ∧
      shim_loaded (FUNPOW arm8$Next 43 ms0).MEM` by (
       fs [forge_elf_loaded_def]
       \\ qspec_then `ms0` mp_tac startup_to_cake_main \\ simp [LET_THM])
  \\ rpt conj_tac
  >- (
    (* Conjunct 1: Unconditional real-bits target + ¬Fail for all valid FFI/install interferences *)
    rpt strip_tac \\ simp [LET_THM]
    \\ drule_all forge_compile_exact \\ simp [LET_THM])
  >- (
    (* Conjunct 2: Forward liveness under error-free Linux read(63)/write(64) *)
    gen_tac
    \\ qspec_then `inp` strip_assume_tac chunks16_split_tail
    \\ qspecl_then [`ms0`, `<| inputs := chunks16 inp; outputs := []; write_limit := NONE |>`,
                    `mk_real_ffi_if (noerr_ffi_P tail_bs)`, `forge_real_install_if`]
         mp_tac forge_compile_exact
    \\ simp [LET_THM, mk_real_ffi_if_ok]
    \\ disch_then (fn th => assume_tac (cj 3 th) \\ mp_tac (cj 4 th))
    \\ disch_then (qx_choosel_then [`ck`, `t`, `ms_end`, `st_end`] (EVERY o map assume_tac o CONJUNCTS))
    \\ qspecl_then [`ck`, `bits_of ms0`, `tail_bs`,
                    `counter_ffi <| inputs := chunks16 inp; outputs := []; write_limit := NONE |>`,
                    `FUNPOW arm8$Next 43 ms0`, `inp`, `[]`, `t`, `ms_end`, `st_end`]
         mp_tac liveness_eval_rtc
    \\ simp [LET_THM]
    \\ impl_tac >- (
         rpt conj_tac
         \\ TRY (first_assum ACCEPT_TAC)
         \\ simp [counter_ffi_def, ffiTheory.initial_ffi_state_def, chunks16_every_len16])
    \\ strip_tac
    \\ qexists_tac `inp_f` \\ qexists_tac `out_f` \\ qexists_tac `ms_f` \\ qexists_tac `ec`
    \\ simp []
    \\ irule relationTheory.RTC_RTC
    \\ qexists_tac `(inp, [], FUNPOW arm8$Next 43 ms0)`
    \\ simp []
    \\ irule det_run_imp_rtc \\ qexists_tac `43` \\ simp [])
  >- (
    (* Conjunct 3: Universal safety over arbitrary OS partial reads/writes, EINTR, EOF & fatal errors *)
    rpt gen_tac \\ strip_tac
    \\ qpat_x_assum `RTC _ _ _` (strip_assume_tac o REWRITE_RULE [arithmeticTheory.RTC_eq_NRC])
    \\ drule_all det_run_peel_nrc \\ strip_tac
    \\ qspecl_then [`n - 43`, `T`, `ms0`, `inp`, `0`, `0`, `inp`, `[]`,
                    `FUNPOW arm8$Next 43 ms0`, `inp_f`, `out_f`, `ms_f`, `exit_code`,
                    `[]`, `[]`, `0`] mp_tac pre_err_nrc_safety
    \\ impl_tac
    >- (
      simp [] \\ rpt gen_tac
      \\ qexists_tac `counter_ffi <| inputs := extra_in; outputs := []; write_limit := wlim_rem |>`
      \\ `OPTION_MAP (λd:num. d) wlim_rem = wlim_rem` by (Cases_on `wlim_rem` \\ simp [])
      \\ simp [counter_ffi_def, ffiTheory.initial_ffi_state_def, sent_frames_of_def,
               ETA_THM])
    \\ simp [])
  \\ (* Conjunct 4: Exactness when exit_code = 0w under error-free Linux syscalls *)
     rpt gen_tac \\ strip_tac
  \\ qpat_x_assum `RTC _ _ _` (strip_assume_tac o REWRITE_RULE [arithmeticTheory.RTC_eq_NRC])
  \\ drule_all det_run_peel_nrc \\ strip_tac
  \\ qspecl_then [`n - 43`, `F`, `ms0`, `inp`, `0`, `0`, `inp`, `[]`,
                  `FUNPOW arm8$Next 43 ms0`, `inp_f`, `out_f`, `ms_f`, `0w`,
                  `[]`, `[]`, `0`] mp_tac pre_err_nrc_safety
  \\ impl_tac
  >- (
    simp [] \\ rpt gen_tac
    \\ qexists_tac `counter_ffi <| inputs := extra_in; outputs := []; write_limit := wlim_rem |>`
    \\ `OPTION_MAP (λd:num. d) wlim_rem = wlim_rem` by (Cases_on `wlim_rem` \\ simp [])
    \\ simp [counter_ffi_def, ffiTheory.initial_ffi_state_def, sent_frames_of_def,
             ETA_THM])
  \\ simp []
QED

(* ---- 8. Non-Vacuity Witness Lemma (Exact Term.aconv-Pinned) ---- *)

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
  ∃ms0:arm8_state.
    forge_elf_loaded code data ms0 ∧
    ms0.TCR_EL1.TBI0 ∧
    ¬ms0.TCR_EL1.TBI1 ∧
    ms0.SCTLR_EL1.SA0 ∧
    aligned 4 ms0.SP_EL0
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
