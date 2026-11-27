(*
  Forge Iron Law — Gate-Owned HOL4 Kernel Auditor (Frozen Runtime 256 KB Slot + Exact Term.aconv).

  Invoked by runtime/iron_law.py AFTER Holmake completes and AFTER pinned spec
  files pass SHA-256 verification.

  Supports exact Term.aconv verification for:
    - M1 Counter Kernel (`forge_counterSpec` / `forge_counterCompile`, 16B shim)
    - M2 Guardrail Kernel (`forge_guardrailSpec` / `forge_guardrailCompile`, 64B shim)
  Fails closed on any unrecognized spec or mismatched compile theory.

  Verifies directly against the HOL4 kernel:
    1. Loads ONLY pinned spec theories + compile theory FIRST (BEFORE loading
       the prover's final_theory, making expected-term parsing 100% immune to
       parser/overload hijacking).
    2. Parses the EXACT expected conclusion terms for `final_thm_name`
       and `nonvac_thm_name` using fully qualified `Thy$Name` constants.
    3. Loads `final_theory` and enforces EXACT kernel alpha-equivalence:
         - `Term.aconv (Thm.concl final_th) expected_kernel_correct`
         - `Term.aconv (Thm.concl nonvac_th) expected_nonvacuous`
    4. Checks 0 hypotheses, 0 direct axiom tags, and DISK_THM-only oracle tags
       on `final_th`, `nonvac_th`, AND every theorem and definition in all
       `forge_*` theories in the transitive closure.
    5. Checks required spec/contract/compile/shim theories are in the transitive
       ancestry closure, and that transitive DB.axioms contains ONLY the 4
       standard bool axioms.
    6. Extracts raw verified ARM64 bytes AND all 24+ exact HOL4 layout constants
       directly from proved HOL4 definitions.
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
val _ =
  if contract_thy_name <> "forge_runtimeSpec" then
    die ("UNSUPPORTED_CONTRACT_THEORY: " ^ contract_thy_name)
  else if shim_thy_name <> "forge_shimProof" then
    die ("UNSUPPORTED_SHIM_THEORY: " ^ shim_thy_name)
  else ();

val (extra_trusted_thys, shim_words_const_name, shim_words_def_name, frame_bytes_str) =
  if spec_thy_name = "forge_counterSpec" then (
    if compile_thy_name <> "forge_counterCompile" then
      die ("COMPILE_THY_MISMATCH for forge_counterSpec: " ^ compile_thy_name)
    else ();
    ([], "forge_shim16_words", "forge_shim16_words_def", "16")
  ) else if spec_thy_name = "forge_guardrailSpec" then (
    if compile_thy_name <> "forge_guardrailCompile" then
      die ("COMPILE_THY_MISMATCH for forge_guardrailSpec: " ^ compile_thy_name)
    else ();
    (["forge_frame64Spec"], "forge_shim64_words", "forge_shim64_words_def", "64")
  ) else
    die ("UNSUPPORTED_SPEC_THEORY: " ^ spec_thy_name);

val _ = List.app (fn t =>
  (load (t ^ "Theory"))
  handle e => die ("cannot load trusted dependency " ^ t ^ "Theory: " ^ General.exnMessage e)
) ([spec_thy_name] @ extra_trusted_thys @ [contract_thy_name, compile_thy_name,
   "targetSem", "ffi", "relation", "arm8", "alignment", "list", "cv", "cv_type"]);

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

fun is_thy_const thy nm tm =
  is_const tm andalso
  let val {Thy, Name, ...} = dest_thy_const tm
  in Thy = thy andalso Name = nm end;

fun check_def_lhs ctx thy cname th =
  let
    val c = Thm.concl th
    val _ = if is_eq c then () else die (ctx ^ "_NOT_EQ")
    val expected_lhs = prim_mk_const {Thy = thy, Name = cname}
      handle _ => die (ctx ^ "_MISSING_CONST (" ^ thy ^ "$" ^ cname ^ ")")
  in
    if Term.aconv (lhs c) expected_lhs then ()
    else die (ctx ^ "_LHS_MISMATCH (expected " ^ thy ^ "$" ^ cname ^ ")")
  end;

fun cv_num_list tm acc =
  let val (f, args) = strip_comb tm in
    if is_thy_const "cv" "Pair" f andalso length args = 2 then
      let val (nf, nargs) = strip_comb (hd args) in
        if is_thy_const "cv" "Num" nf andalso length nargs = 1 then
          cv_num_list (el 2 args) (numSyntax.dest_numeral (hd nargs) :: acc)
        else die "malformed cv$Pair element (expected cv$Num)"
      end
    else if is_thy_const "cv" "Num" f andalso length args = 1
            andalso Arbnum.compare (numSyntax.dest_numeral (hd args), Arbnum.zero) = EQUAL then
      rev acc
    else die ("malformed cv list tail (expected cv$Pair or cv$Num 0): " ^ term_to_string f)
  end;

fun word8_list_to_bytes tm =
  let
    val (f, args) = strip_comb tm
    val expected_to_word_ty = Type.mk_type ("fun", [Type.mk_thy_type {Thy="cv", Tyop="cv", Args=[]}, ``:word8``])
  in
    if is_thy_const "cv_type" "to_list" f andalso length args = 2
       andalso is_thy_const "cv_type" "to_word" (hd args)
       andalso type_of (hd args) = expected_to_word_ty then
      let
        val nums = cv_num_list (el 2 args) []
        fun one_num n =
          let val i = Arbnum.toInt n in
            if i >= 0 andalso i < 256 then Word8.fromInt i
            else die ("cv byte out of range: " ^ Int.toString i)
          end
      in Word8Vector.fromList (map one_num nums) end
    else
      ((let
          val (elems, _) = listSyntax.dest_list tm
          fun one_byte t =
            let val n = Arbnum.toInt (wordsSyntax.dest_word_literal t)
            in if n >= 0 andalso n < 256 then Word8.fromInt n
               else die ("byte out of range: " ^ Int.toString n) end
        in Word8Vector.fromList (map one_byte elems) end)
       handle HOL_ERR _ =>
         die "CODE_BYTES_MALFORMED (expected cv_type$to_list cv_type$to_word or word8 list literal)")
  end;

val u64_limit = Arbnum.pow (Arbnum.two, Arbnum.fromInt 64);

fun split_u64_le n =
  let
    val _ = if Arbnum.< (n, u64_limit) then ()
            else die ("u64 bitmap word out of range: " ^ Arbnum.toString n)
    fun split 0 _ acc = rev acc
      | split k m acc =
          let val b = Arbnum.toInt (Arbnum.mod (m, Arbnum.fromInt 256))
          in split (k - 1) (Arbnum.div (m, Arbnum.fromInt 256)) (Word8.fromInt b :: acc) end
  in split 8 n [] end;

fun word64_list_to_le_bytes tm =
  let
    val (f, args) = strip_comb tm
    val expected_c2n_ty = Type.mk_type ("fun", [Type.mk_thy_type {Thy="cv", Tyop="cv", Args=[]}, ``:num``])
  in
    if is_thy_const "cv_type" "to_list" f andalso length args = 2
       andalso is_thy_const "cv" "c2n" (hd args)
       andalso type_of (hd args) = expected_c2n_ty then
      let val nums = cv_num_list (el 2 args) []
      in Word8Vector.fromList (List.concat (map split_u64_le nums)) end
    else
      ((let
          val (elems, _) = listSyntax.dest_list tm
          fun one_w64 t = split_u64_le (numSyntax.dest_numeral t)
        in Word8Vector.fromList (List.concat (map one_w64 elems)) end)
       handle HOL_ERR _ =>
         die "DATA_WORDS_MALFORMED (expected cv_type$to_list cv$c2n or num list literal)")
  end;

(* 2. Construct EXACT expected conclusion terms BEFORE final_thy_name is loaded *)
val (expected_nonvacuous : term, expected_kernel_correct : term) =
  if spec_thy_name = "forge_counterSpec" then
    (
      ``∃ms0:arm8$arm8_state.
          forge_runtimeSpec$forge_slot_loaded
            forge_runtimeSpec$forge_shim16_words
            forge_counterCompile$code forge_counterCompile$data ms0 ∧
          ms0.TCR_EL1.TBI0 ∧
          ¬ms0.TCR_EL1.TBI1 ∧
          ms0.SCTLR_EL1.SA0 ∧
          alignment$aligned 4 ms0.SP_EL0``,
      ``∀ms0:arm8$arm8_state.
          forge_runtimeSpec$forge_slot_loaded
            forge_runtimeSpec$forge_shim16_words
            forge_counterCompile$code forge_counterCompile$data ms0 ⇒
            let ms1 = arithmetic$FUNPOW arm8$Next 43 ms0 in
            let cb_end = forge_runtimeSpec$slot_cb_end (list$LENGTH forge_counterCompile$code) in
            let bm_end = forge_runtimeSpec$slot_bm_buf_end (list$LENGTH forge_counterCompile$data) in
            let cbsp = forge_runtimeSpec$slot_cbspace (list$LENGTH forge_counterCompile$code) in
            (∀(io:forge_counterSpec$counter_io) ffi_if inst_if.
               io.outputs = [] ∧
               forge_runtimeSpec$real_interfer_ok_slot cb_end bm_end cbsp
                 [ffi$ExtCall «send16»; ffi$ExtCall «recv16»]
                 (forge_runtimeSpec$bits_of ms0) ffi_if inst_if ⇒
                 let rmc = forge_runtimeSpec$real_mc (forge_runtimeSpec$bits_of ms0)
                             (forge_runtimeSpec$forge_mc_slot cb_end bm_end
                                [ffi$ExtCall «send16»; ffi$ExtCall «recv16»] ffi_if inst_if) in
                   rmc.target = forge_runtimeSpec$arm8_target_real (forge_runtimeSpec$bits_of ms0) ∧
                   ¬targetSem$machine_sem rmc (forge_counterSpec$counter_ffi io) ms1 ffi$Fail) ∧
            (∀inp:word8 list.
               ∃inp_f out_f ms_f exit_code.
                 relation$RTC
                   (forge_runtimeSpec$whole_step
                      forge_runtimeSpec$svc_read_noerr_rel
                      forge_runtimeSpec$svc_write_noerr_rel)
                   (inp, [], ms0) (inp_f, out_f, ms_f) ∧
                 forge_runtimeSpec$svc_exit_group_rel exit_code ms_f) ∧
            (∀(inp:word8 list) inp_f out_f ms_f exit_code.
               relation$RTC
                 (forge_runtimeSpec$whole_step
                    forge_runtimeSpec$svc_read_rel
                    forge_runtimeSpec$svc_write_rel)
                 (inp, [], ms0) (inp_f, out_f, ms_f) ∧
               forge_runtimeSpec$svc_exit_group_rel exit_code ms_f ⇒
                 (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
                 list$isPREFIX out_f
                   (list$FLAT (pair$SND (pair$SND (forge_counterSpec$counter_run 0w 0w (forge_counterSpec$chunks16 inp)))))) ∧
            (∀(inp:word8 list) inp_f out_f ms_f exit_code.
               relation$RTC
                 (forge_runtimeSpec$whole_step
                    forge_runtimeSpec$svc_read_noerr_rel
                    forge_runtimeSpec$svc_write_noerr_rel)
                 (inp, [], ms0) (inp_f, out_f, ms_f) ∧
               forge_runtimeSpec$svc_exit_group_rel exit_code ms_f ∧
               exit_code = 0w ⇒
                 out_f = list$FLAT (pair$SND (pair$SND (forge_counterSpec$counter_run 0w 0w (forge_counterSpec$chunks16 inp)))))``
    )
  else
    (
      ``∃ms0:arm8$arm8_state.
          forge_runtimeSpec$forge_slot_loaded
            forge_runtimeSpec$forge_shim64_words
            forge_guardrailCompile$code forge_guardrailCompile$data ms0 ∧
          ms0.TCR_EL1.TBI0 ∧
          ¬ms0.TCR_EL1.TBI1 ∧
          ms0.SCTLR_EL1.SA0 ∧
          alignment$aligned 4 ms0.SP_EL0``,
      ``∀ms0:arm8$arm8_state.
          forge_runtimeSpec$forge_slot_loaded
            forge_runtimeSpec$forge_shim64_words
            forge_guardrailCompile$code forge_guardrailCompile$data ms0 ⇒
            let ms1 = arithmetic$FUNPOW arm8$Next 43 ms0 in
            let cb_end = forge_runtimeSpec$slot_cb_end (list$LENGTH forge_guardrailCompile$code) in
            let bm_end = forge_runtimeSpec$slot_bm_buf_end (list$LENGTH forge_guardrailCompile$data) in
            let cbsp = forge_runtimeSpec$slot_cbspace (list$LENGTH forge_guardrailCompile$code) in
            (∀(io:forge_frame64Spec$frame64_io) ffi_if inst_if.
               io.outputs = [] ∧
               forge_runtimeSpec$real_interfer_ok_slot cb_end bm_end cbsp
                 [ffi$ExtCall «send64»; ffi$ExtCall «recv64»]
                 (forge_runtimeSpec$bits_of ms0) ffi_if inst_if ⇒
                 let rmc = forge_runtimeSpec$real_mc (forge_runtimeSpec$bits_of ms0)
                             (forge_runtimeSpec$forge_mc_slot cb_end bm_end
                                [ffi$ExtCall «send64»; ffi$ExtCall «recv64»] ffi_if inst_if) in
                   rmc.target = forge_runtimeSpec$arm8_target_real (forge_runtimeSpec$bits_of ms0) ∧
                   ¬targetSem$machine_sem rmc (forge_frame64Spec$frame64_ffi io) ms1 ffi$Fail) ∧
            (∀inp:word8 list.
               ∃inp_f out_f ms_f exit_code.
                 relation$RTC
                   (forge_runtimeSpec$whole_step
                      forge_runtimeSpec$svc_read_noerr_rel
                      forge_runtimeSpec$svc_write_noerr_rel)
                   (inp, [], ms0) (inp_f, out_f, ms_f) ∧
                 forge_runtimeSpec$svc_exit_group_rel exit_code ms_f) ∧
            (∀(inp:word8 list) inp_f out_f ms_f exit_code.
               relation$RTC
                 (forge_runtimeSpec$whole_step
                    forge_runtimeSpec$svc_read_rel
                    forge_runtimeSpec$svc_write_rel)
                 (inp, [], ms0) (inp_f, out_f, ms_f) ∧
               forge_runtimeSpec$svc_exit_group_rel exit_code ms_f ⇒
                 (exit_code = 0w ∨ exit_code = 1w ∨ exit_code = 2w) ∧
                 list$isPREFIX out_f
                   (list$FLAT (pair$SND (forge_frame64Spec$frame64_run forge_guardrailSpec$gr_step forge_guardrailSpec$gr_init (forge_frame64Spec$chunks64 inp))))) ∧
            (∀(inp:word8 list) inp_f out_f ms_f exit_code.
               relation$RTC
                 (forge_runtimeSpec$whole_step
                    forge_runtimeSpec$svc_read_noerr_rel
                    forge_runtimeSpec$svc_write_noerr_rel)
                 (inp, [], ms0) (inp_f, out_f, ms_f) ∧
               forge_runtimeSpec$svc_exit_group_rel exit_code ms_f ∧
               exit_code = 0w ⇒
                 out_f = list$FLAT (pair$SND (forge_frame64Spec$frame64_run forge_guardrailSpec$gr_step forge_guardrailSpec$gr_init (forge_frame64Spec$chunks64 inp))))``
    );

(* 2b. Validate compile_thy_name defs & decode code/data BEFORE loading final_thy_name *)
val (code_vec, data_vec) = let
  val code_def = DB.fetch compile_thy_name "code_def"
    handle e => die ("missing " ^ compile_thy_name ^ ".code_def")
  val data_def = DB.fetch compile_thy_name "data_def"
    handle e => die ("missing " ^ compile_thy_name ^ ".data_def")
  val ffis_def = DB.fetch compile_thy_name "ffis_def"
    handle e => die ("missing " ^ compile_thy_name ^ ".ffis_def")
  val _ = (check_tag "code_def" code_def; check_tag "data_def" data_def; check_tag "ffis_def" ffis_def)
  val _ = check_def_lhs "CODE_DEF" compile_thy_name "code" code_def
  val _ = check_def_lhs "DATA_DEF" compile_thy_name "data" data_def
  val _ = check_def_lhs "FFIS_DEF" compile_thy_name "ffis" ffis_def
in
  (word8_list_to_bytes (rhs (concl code_def)),
   word64_list_to_le_bytes (rhs (concl data_def)))
end;

(* 3. Now load the prover's final theory *)
val _ = (load (final_thy_name ^ "Theory"))
  handle e => die ("cannot load " ^ final_thy_name ^ "Theory: " ^ General.exnMessage e);

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
) ([spec_thy_name, contract_thy_name, compile_thy_name, shim_thy_name] @ extra_trusted_thys);

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

(* 6. Helper: extract word32 / word64 blobs & layout constants *)
fun eval_tm tm = rhs (concl (EVAL tm));

fun eval_word64_tm tm =
  Arbnum.toString (wordsSyntax.dest_word_literal (eval_tm tm))
  handle _ => die ("word64 term did not evaluate to literal: " ^ term_to_string tm);

fun eval_num_tm tm =
  Arbnum.toString (numSyntax.dest_numeral (eval_tm tm))
  handle _ => die ("num term did not evaluate to numeral: " ^ term_to_string tm);

fun eval_word64_def thy cname def_name =
  let
    val th = DB.fetch thy def_name
      handle e => die ("missing layout def " ^ thy ^ "." ^ def_name)
    val _ = check_tag (thy ^ "." ^ def_name) th
    val _ = check_def_lhs ("LAYOUT_" ^ cname) thy cname th
  in
    eval_word64_tm (rhs (concl th))
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

fun write_bin path vec =
  let val os = BinIO.openOut path
  in BinIO.output (os, vec); BinIO.closeOut os end;

(* 7. Write verified code, bitmaps, slot veneers, shim words, and all FORGE_* layout constants *)
val _ = let
  val code_len_tm = numSyntax.term_of_int (Word8Vector.length code_vec)
  val data_words_tm = numSyntax.term_of_int (Word8Vector.length data_vec div 8)
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_code.bin")) code_vec
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_data.bin")) data_vec

  val cb_begin_tm = eval_tm ``forge_runtimeSpec$slot_cb_begin ^code_len_tm``
  val cb_end_tm   = eval_tm ``forge_runtimeSpec$slot_cb_end ^code_len_tm``
  val bm_end_tm   = eval_tm ``forge_runtimeSpec$slot_bm_buf_end ^data_words_tm``
  val cbspace_str = eval_num_tm ``forge_runtimeSpec$slot_cbspace ^code_len_tm``

  val veneers_tm = eval_tm ``forge_runtimeSpec$forge_slot_veneers ^cb_begin_tm ^cb_end_tm ^bm_end_tm``
  val shim_def = DB.fetch "forge_runtimeSpec" shim_words_def_name
    handle e => die ("missing forge_runtimeSpec." ^ shim_words_def_name)
  val _ = check_tag shim_words_def_name shim_def
  val _ = check_def_lhs "SHIM_DEF" "forge_runtimeSpec" shim_words_const_name shim_def

  val veneers_vec = word32_list_to_le_bytes veneers_tm
  val shim_vec = word32_list_to_le_bytes (eval_tm (rhs (concl shim_def)))
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_veneers.bin")) veneers_vec
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_shim.bin")) shim_vec

  val fixed_w64_fields = [
    ("veneers_base",     "FORGE_VENEERS_BASE",   "FORGE_VENEERS_BASE_def"),
    ("ffirecv16_veneer", "FORGE_FFIRECV_VENEER", "FORGE_FFIRECV_VENEER_def"),
    ("ffisend16_veneer", "FORGE_FFISEND_VENEER", "FORGE_FFISEND_VENEER_def"),
    ("install_veneer",   "FORGE_INSTALL_VENEER", "FORGE_INSTALL_VENEER_def"),
    ("exit_veneer",      "FORGE_EXIT_VENEER",    "FORGE_EXIT_VENEER_def"),
    ("cake_main",        "FORGE_CAKE_MAIN",      "FORGE_CAKE_MAIN_def"),
    ("slot_end",         "FORGE_SLOT_END",       "FORGE_SLOT_END_def"),
    ("shim_base",        "FORGE_SHIM_BASE",      "FORGE_SHIM_BASE_def"),
    ("ffirecv16",        "FORGE_FFIRECV",        "FORGE_FFIRECV_def"),
    ("ffisend16",        "FORGE_FFISEND",        "FORGE_FFISEND_def"),
    ("cml_exit",         "FORGE_CML_EXIT",       "FORGE_CML_EXIT_def"),
    ("cml_install",      "FORGE_CML_INSTALL",    "FORGE_CML_INSTALL_def"),
    ("shim_end",         "FORGE_SHIM_END",       "FORGE_SHIM_END_def"),
    ("cml_heap",         "FORGE_CML_HEAP",       "FORGE_CML_HEAP_def"),
    ("cml_stack",        "FORGE_CML_STACK",      "FORGE_CML_STACK_def"),
    ("cml_stackend",     "FORGE_CML_STACKEND",   "FORGE_CML_STACKEND_def"),
    ("cake_bitmaps",     "FORGE_CAKE_BITMAPS",   "FORGE_CAKE_BITMAPS_def"),
    ("rx_tmp",           "FORGE_RX_TMP",         "FORGE_RX_TMP_def"),
    ("forge_heap",       "FORGE_HEAP",           "FORGE_HEAP_def"),
    ("forge_stack",      "FORGE_STACK",          "FORGE_STACK_def"),
    ("forge_stackend",   "FORGE_STACKEND",       "FORGE_STACKEND_def")
  ]
  val layout_lines =
    map (fn (k, c, d) => k ^ "=" ^ eval_word64_def "forge_runtimeSpec" c d ^ "\n") fixed_w64_fields @
    ["cb_begin=" ^ eval_word64_tm cb_begin_tm ^ "\n",
     "cb_end=" ^ eval_word64_tm cb_end_tm ^ "\n",
     "bm_buf_end=" ^ eval_word64_tm bm_end_tm ^ "\n",
     "cbspace=" ^ cbspace_str ^ "\n",
     "frame_bytes=" ^ frame_bytes_str ^ "\n",
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
  print ("AUDIT_OK aconv=exact spec=" ^ spec_thy_name ^
         " frame_bytes=" ^ frame_bytes_str ^
         " closure_nodes=" ^ Int.toString (length closure) ^
         " forge_theories=" ^ Int.toString (length forge_thys) ^
         " axioms=4 code_bytes=" ^ Int.toString (Word8Vector.length code_vec) ^
         " data_bytes=" ^ Int.toString (Word8Vector.length data_vec) ^
         " veneers_bytes=" ^ Int.toString (Word8Vector.length veneers_vec) ^
         " shim_bytes=" ^ Int.toString (Word8Vector.length shim_vec) ^ "\n")
end;
val _ = OS.Process.exit OS.Process.success;
