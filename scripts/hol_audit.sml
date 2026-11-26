(*
  Forge Iron Law — Gate-Owned HOL4 Kernel Auditor (Exact Term.aconv Edition).
  Invoked by scripts/iron_law.py AFTER Holmake completes and AFTER pinned
  spec files (forge_counterSpecScript.sml, forge_contractSpecScript.sml) pass
  SHA-256 verification.

  Verifies directly against the HOL4 kernel:
    1. Loads ONLY pinned spec theories + compile theory FIRST (BEFORE loading
       the prover's final_theory, making expected-term parsing 100% immune to
       parser/overload hijacking).
    2. Parses the EXACT expected conclusion terms for `forge_m1_kernel_correct`
       and `forge_m1_nonvacuous` using fully qualified `Thy$Name` constants.
    3. Loads `final_theory` and enforces EXACT kernel alpha-equivalence:
         - `Term.aconv (Thm.concl final_th) expected_kernel_correct`
         - `Term.aconv (Thm.concl nonvac_th) expected_nonvacuous`
    4. Checks 0 hypotheses, 0 direct axiom tags, and DISK_THM-only oracle tags
       on `final_th`, `nonvac_th`, AND every theorem and definition in all
       `forge_*` theories in the transitive closure.
    5. Checks `spec_theory`, `contract_theory`, `compile_theory`, and
       `shim_theory` are in the transitive ancestry closure, and that transitive
       DB.axioms contains ONLY the 4 standard bool axioms:
         bool.BOOL_CASES_AX, bool.ETA_AX, bool.INFINITY_AX, bool.SELECT_AX.
    6. Extracts raw verified ARM64 bytes AND all 24 exact HOL4 layout constants
       (FORGE_* vaddrs and FORGE_CBSPACE) directly from proved definitions.
*)

open HolKernel Parse boolLib bossLib wordsLib;

fun die msg = (TextIO.output (TextIO.stdErr, "HOL_AUDIT_FAIL: " ^ msg ^ "\n");
               OS.Process.exit OS.Process.failure);

fun req_env k =
  case OS.Process.getEnv k of
    SOME v => if size v > 0 then v else die ("empty env " ^ k)
  | NONE => die ("missing env " ^ k);

val final_thy_name    = req_env "FORGE_AUDIT_THEORY";
val final_thm_name    = req_env "FORGE_AUDIT_THEOREM";
val nonvac_thm_name   = req_env "FORGE_AUDIT_NONVAC_THEOREM";
val spec_thy_name     = req_env "FORGE_AUDIT_SPEC_THY";
val contract_thy_name = req_env "FORGE_AUDIT_CONTRACT_THY";
val compile_thy_name  = req_env "FORGE_AUDIT_COMPILE_THY";
val shim_thy_name     = req_env "FORGE_AUDIT_SHIM_THY";
val out_dir           = req_env "FORGE_AUDIT_OUT_DIR";

(* 1. Load pinned spec & compile theories FIRST, BEFORE loading final_thy_name *)
val _ = List.app (fn t =>
  (load (t ^ "Theory"))
  handle e => die ("cannot load trusted dependency " ^ t ^ "Theory: " ^ General.exnMessage e)
) [spec_thy_name, contract_thy_name, compile_thy_name,
   "targetSem", "ffi", "relation", "arm8", "alignment", "list"];

(* 2. Construct EXACT expected conclusion terms BEFORE final_thy_name is loaded *)
val expected_nonvacuous : term =
  ``∃ms0:arm8$arm8_state.
      forge_contractSpec$forge_elf_loaded
        forge_counterCompile$code forge_counterCompile$data ms0 ∧
      ms0.TCR_EL1.TBI0 ∧
      ¬ms0.TCR_EL1.TBI1 ∧
      ms0.SCTLR_EL1.SA0 ∧
      alignment$aligned 4 ms0.SP_EL0``;

val expected_kernel_correct : term =
  ``∀ms0:arm8$arm8_state.
      forge_contractSpec$forge_elf_loaded
        forge_counterCompile$code forge_counterCompile$data ms0 ⇒
        let ms1 = arithmetic$FUNPOW arm8$Next 43 ms0 in
        (∀(io:forge_counterSpec$counter_io) ffi_if inst_if.
           io.outputs = [] ∧
           forge_contractSpec$real_interfer_ok (forge_contractSpec$bits_of ms0) ffi_if inst_if ⇒
             let rmc = forge_contractSpec$real_mc (forge_contractSpec$bits_of ms0)
                         (forge_contractSpec$forge_mc_with ffi_if inst_if) in
               rmc.target = forge_contractSpec$arm8_target_real (forge_contractSpec$bits_of ms0) ∧
               ¬targetSem$machine_sem rmc (forge_counterSpec$counter_ffi io) ms1 ffi$Fail) ∧
        (∀inp:word8 list.
           ∃inp_f out_f ms_f exit_code.
             relation$RTC
               (forge_contractSpec$whole_step
                  forge_contractSpec$svc_read_noerr_rel
                  forge_contractSpec$svc_write_noerr_rel)
               (inp, [], ms0) (inp_f, out_f, ms_f) ∧
             forge_contractSpec$svc_exit_group_rel exit_code ms_f) ∧
        (∀(inp:word8 list) inp_f out_f ms_f exit_code.
           relation$RTC
             (forge_contractSpec$whole_step
                forge_contractSpec$svc_read_rel
                forge_contractSpec$svc_write_rel)
             (inp, [], ms0) (inp_f, out_f, ms_f) ∧
           forge_contractSpec$svc_exit_group_rel exit_code ms_f ⇒
             (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
             list$isPREFIX out_f
               (list$FLAT (pair$SND (pair$SND (forge_counterSpec$counter_run 0w 0w (forge_counterSpec$chunks16 inp)))))) ∧
        (∀(inp:word8 list) inp_f out_f ms_f exit_code.
           relation$RTC
             (forge_contractSpec$whole_step
                forge_contractSpec$svc_read_noerr_rel
                forge_contractSpec$svc_write_noerr_rel)
             (inp, [], ms0) (inp_f, out_f, ms_f) ∧
           forge_contractSpec$svc_exit_group_rel exit_code ms_f ∧
           exit_code = 0w ⇒
             out_f = list$FLAT (pair$SND (pair$SND (forge_counterSpec$counter_run 0w 0w (forge_counterSpec$chunks16 inp)))))``;

(* 3. Now load the prover's final theory *)
val _ = (load (final_thy_name ^ "Theory"))
  handle e => die ("cannot load " ^ final_thy_name ^ "Theory: " ^ General.exnMessage e);

fun check_tag ctx th =
  let
    val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in
    if not (null (Thm.hyp th)) then
      die ("non-empty hypotheses in " ^ ctx)
    else if not (null axs) then
      die ("direct axiom tags in " ^ ctx ^ ": " ^ String.concatWith "," axs)
    else if not (List.all (fn x => x = "DISK_THM") ors) then
      die ("forbidden oracle tag in " ^ ctx ^ ": " ^ String.concatWith "," ors)
    else ()
  end;

(* 4. Fetch theorems and enforce EXACT kernel Term.aconv + clean tags *)
val final_th = DB.fetch final_thy_name final_thm_name
  handle e => die ("missing theorem " ^ final_thy_name ^ "." ^ final_thm_name ^ ": " ^ General.exnMessage e);
val _ = check_tag (final_thy_name ^ "." ^ final_thm_name) final_th;

val nonvac_th = DB.fetch final_thy_name nonvac_thm_name
  handle e => die ("missing non-vacuity theorem " ^ final_thy_name ^ "." ^ nonvac_thm_name ^ ": " ^ General.exnMessage e);
val _ = check_tag (final_thy_name ^ "." ^ nonvac_thm_name) nonvac_th;

val _ =
  if Term.aconv (Thm.concl final_th) expected_kernel_correct then ()
  else die ("EXACT_TERM_MISMATCH on " ^ final_thy_name ^ "." ^ final_thm_name ^
            " (Thm.concl is not alpha-equivalent to the pinned expected theorem)");

val _ =
  if Term.aconv (Thm.concl nonvac_th) expected_nonvacuous then ()
  else die ("EXACT_TERM_MISMATCH on " ^ final_thy_name ^ "." ^ nonvac_thm_name ^
            " (Thm.concl is not alpha-equivalent to the pinned expected non-vacuity theorem)");

(* 5. Audit transitive ancestry: required theories, axioms, and all forge_* items *)
val closure = final_thy_name :: Theory.ancestry final_thy_name;
fun mem s xs = List.exists (fn x => x = s) xs;

val _ = List.app (fn t =>
  if mem t closure then ()
  else die ("required theory not in closure: " ^ t)
) [spec_thy_name, contract_thy_name, compile_thy_name, shim_thy_name];

val all_axioms =
  List.concat (map (fn thy => map (fn (nm, _) => thy ^ "." ^ nm) (DB.axioms thy)) closure);

val allowed_axioms =
  ["bool.BOOL_CASES_AX", "bool.ETA_AX", "bool.INFINITY_AX", "bool.SELECT_AX"];

val extra_axioms = List.filter (fn a => not (mem a allowed_axioms)) all_axioms;
val _ = if null extra_axioms then ()
        else die ("unexpected axioms in closure: " ^ String.concatWith "," extra_axioms);
val _ = if length all_axioms = 4 then ()
        else die ("expected 4 bool axioms, got " ^ Int.toString (length all_axioms));

val forge_thys = List.filter (String.isPrefix "forge_") closure;
val _ = if length forge_thys >= 5 then ()
        else die ("unexpectedly few forge_* theories in closure: " ^ Int.toString (length forge_thys));

val _ = List.app (fn thy =>
  List.app (fn (nm, th) => check_tag (thy ^ "." ^ nm) th)
    (DB.theorems thy @ DB.definitions thy)
) forge_thys;

(* 6. Helper: extract word8 / word32 / word64 byte blobs & layout constants *)
fun eval_to_rhs th =
  let val th' = CONV_RULE (RAND_CONV EVAL) th
  in rhs (concl th') end;

fun eval_word64_def thy def_name =
  let
    val th = DB.fetch thy def_name
      handle e => die ("missing layout def " ^ thy ^ "." ^ def_name)
    val _ = check_tag (thy ^ "." ^ def_name) th
    val r = eval_to_rhs th
  in
    Arbnum.toString (wordsSyntax.dest_word_literal r)
      handle _ => die ("layout def " ^ def_name ^ " did not evaluate to word literal")
  end;

fun eval_num_def thy def_name =
  let
    val th = DB.fetch thy def_name
      handle e => die ("missing layout def " ^ thy ^ "." ^ def_name)
    val _ = check_tag (thy ^ "." ^ def_name) th
    val r = eval_to_rhs th
  in
    Arbnum.toString (numSyntax.dest_numeral r)
      handle _ => die ("layout def " ^ def_name ^ " did not evaluate to numeral")
  end;

fun cv_num_list tm acc =
  let val (f, args) = strip_comb tm in
    if is_const f andalso fst (dest_const f) = "Pair" andalso length args = 2 then
      let val (nf, nargs) = strip_comb (hd args) in
        if is_const nf andalso fst (dest_const nf) = "Num" andalso length nargs = 1 then
          cv_num_list (el 2 args) (numSyntax.dest_numeral (hd nargs) :: acc)
        else die "malformed cv$Pair element"
      end
    else if is_const f andalso fst (dest_const f) = "Num" andalso length args = 1
            andalso Arbnum.compare (numSyntax.dest_numeral (hd args), Arbnum.zero) = EQUAL then
      rev acc
    else die ("malformed cv list tail: " ^ term_to_string f)
  end;

fun word8_list_to_bytes tm =
  let
    val (f, args) = strip_comb tm
  in
    if is_const f andalso fst (dest_const f) = "to_list" andalso length args = 2
       andalso is_const (fst (strip_comb (hd args)))
       andalso fst (dest_const (fst (strip_comb (hd args)))) = "to_word" then
      let
        val nums = cv_num_list (el 2 args) []
        fun one_num n =
          let val i = Arbnum.toInt n in
            if i >= 0 andalso i < 256 then Word8.fromInt i
            else die ("cv byte out of range: " ^ Int.toString i)
          end
      in Word8Vector.fromList (map one_num nums) end
    else
      let
        val (elems, _) = listSyntax.dest_list tm
        fun one_byte t =
          let val n = Arbnum.toInt (wordsSyntax.dest_word_literal t)
          in if n >= 0 andalso n < 256 then Word8.fromInt n
             else die ("byte out of range: " ^ Int.toString n) end
      in Word8Vector.fromList (map one_byte elems) end
  end;

fun word32_list_to_le_bytes tm =
  let
    val (elems, _) = listSyntax.dest_list tm
    fun one_w32 t =
      let
        val n = wordsSyntax.dest_word_literal t
        val b0 = Arbnum.toInt (Arbnum.mod (n, Arbnum.fromInt 256))
        val n1 = Arbnum.div (n, Arbnum.fromInt 256)
        val b1 = Arbnum.toInt (Arbnum.mod (n1, Arbnum.fromInt 256))
        val n2 = Arbnum.div (n1, Arbnum.fromInt 256)
        val b2 = Arbnum.toInt (Arbnum.mod (n2, Arbnum.fromInt 256))
        val n3 = Arbnum.div (n2, Arbnum.fromInt 256)
        val b3 = Arbnum.toInt (Arbnum.mod (n3, Arbnum.fromInt 256))
      in map Word8.fromInt [b0, b1, b2, b3] end
  in Word8Vector.fromList (List.concat (map one_w32 elems)) end;

fun split_u64_le n =
  let
    fun split 0 _ acc = rev acc
      | split k m acc =
          let val b = Arbnum.toInt (Arbnum.mod (m, Arbnum.fromInt 256))
          in split (k - 1) (Arbnum.div (m, Arbnum.fromInt 256)) (Word8.fromInt b :: acc) end
  in split 8 n [] end;

fun word64_list_to_le_bytes tm =
  let
    val (f, args) = strip_comb tm
  in
    if is_const f andalso fst (dest_const f) = "to_list" andalso length args = 2
       andalso is_const (fst (strip_comb (hd args)))
       andalso fst (dest_const (fst (strip_comb (hd args)))) = "c2n" then
      let val nums = cv_num_list (el 2 args) []
      in Word8Vector.fromList (List.concat (map split_u64_le nums)) end
    else
      let
        val (elems, _) = listSyntax.dest_list tm
        fun one_w64 t = split_u64_le (numSyntax.dest_numeral t)
      in Word8Vector.fromList (List.concat (map one_w64 elems)) end
  end;

fun write_bin path vec =
  let val os = BinIO.openOut path
  in BinIO.output (os, vec); BinIO.closeOut os end;

(* 7. Extract verified code, bitmaps, veneers, shim words, and all FORGE_* layout constants *)
val _ = let
  val code_def = DB.fetch compile_thy_name "code_def"
    handle e => die ("missing " ^ compile_thy_name ^ ".code_def")
  val data_def = DB.fetch compile_thy_name "data_def"
    handle e => die ("missing " ^ compile_thy_name ^ ".data_def")
  val ffis_def = DB.fetch compile_thy_name "ffis_def"
    handle e => die ("missing " ^ compile_thy_name ^ ".ffis_def")
  val _ = (check_tag "code_def" code_def; check_tag "data_def" data_def; check_tag "ffis_def" ffis_def)

  val code_vec = word8_list_to_bytes (rhs (concl code_def))
  val data_vec = word64_list_to_le_bytes (rhs (concl data_def))
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_code.bin")) code_vec
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_data.bin")) data_vec

  val veneers_def = DB.fetch contract_thy_name "forge_veneers_words_def"
    handle e => die ("missing " ^ contract_thy_name ^ ".forge_veneers_words_def")
  val shim_def = DB.fetch contract_thy_name "forge_shim_words_def"
    handle e => die ("missing " ^ contract_thy_name ^ ".forge_shim_words_def")
  val _ = (check_tag "forge_veneers_words_def" veneers_def; check_tag "forge_shim_words_def" shim_def)

  val veneers_vec = word32_list_to_le_bytes (eval_to_rhs veneers_def)
  val shim_vec = word32_list_to_le_bytes (eval_to_rhs shim_def)
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_veneers.bin")) veneers_vec
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_shim.bin")) shim_vec

  val w64_fields = [
    ("veneers_base", "FORGE_VENEERS_BASE_def"),
    ("ffirecv16_veneer", "FORGE_FFIRECV16_VENEER_def"),
    ("ffisend16_veneer", "FORGE_FFISEND16_VENEER_def"),
    ("install_veneer", "FORGE_INSTALL_VENEER_def"),
    ("exit_veneer", "FORGE_EXIT_VENEER_def"),
    ("cake_main", "FORGE_CAKE_MAIN_def"),
    ("cb_begin", "FORGE_CB_BEGIN_def"),
    ("cb_end", "FORGE_CB_END_def"),
    ("shim_base", "FORGE_SHIM_BASE_def"),
    ("ffirecv16", "FORGE_FFIRECV16_def"),
    ("ffisend16", "FORGE_FFISEND16_def"),
    ("cml_exit", "FORGE_CML_EXIT_def"),
    ("cml_install", "FORGE_CML_INSTALL_def"),
    ("shim_end", "FORGE_SHIM_END_def"),
    ("cml_heap", "FORGE_CML_HEAP_def"),
    ("cml_stack", "FORGE_CML_STACK_def"),
    ("cml_stackend", "FORGE_CML_STACKEND_def"),
    ("cake_bitmaps", "FORGE_CAKE_BITMAPS_def"),
    ("bm_buf_end", "FORGE_BM_BUF_END_def"),
    ("rx_tmp", "FORGE_RX_TMP_def"),
    ("forge_heap", "FORGE_HEAP_def"),
    ("forge_stack", "FORGE_STACK_def"),
    ("forge_stackend", "FORGE_STACKEND_def")
  ]
  val layout_lines =
    map (fn (k, d) => k ^ "=" ^ eval_word64_def contract_thy_name d ^ "\n") w64_fields @
    ["cbspace=" ^ eval_num_def contract_thy_name "FORGE_CBSPACE_def" ^ "\n",
     "closure_nodes=" ^ Int.toString (length closure) ^ "\n",
     "forge_theories=" ^ Int.toString (length forge_thys) ^ "\n",
     "axioms=" ^ Int.toString (length all_axioms) ^ "\n",
     "code_bytes=" ^ Int.toString (Word8Vector.length code_vec) ^ "\n",
     "data_bytes=" ^ Int.toString (Word8Vector.length data_vec) ^ "\n",
     "veneers_bytes=" ^ Int.toString (Word8Vector.length veneers_vec) ^ "\n",
     "shim_bytes=" ^ Int.toString (Word8Vector.length shim_vec) ^ "\n"]

  val layout_os = TextIO.openOut (OS.Path.concat (out_dir, "theorem_layout.txt"))
  val _ = TextIO.output (layout_os, String.concat layout_lines)
  val _ = TextIO.closeOut layout_os
in
  print ("AUDIT_OK aconv=exact closure_nodes=" ^ Int.toString (length closure) ^
         " forge_theories=" ^ Int.toString (length forge_thys) ^
         " axioms=4 code_bytes=" ^ Int.toString (Word8Vector.length code_vec) ^
         " data_bytes=" ^ Int.toString (Word8Vector.length data_vec) ^
         " veneers_bytes=" ^ Int.toString (Word8Vector.length veneers_vec) ^
         " shim_bytes=" ^ Int.toString (Word8Vector.length shim_vec) ^ "\n")
end;
val _ = OS.Process.exit OS.Process.success;
