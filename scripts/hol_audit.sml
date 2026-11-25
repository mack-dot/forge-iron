(*
  Forge Iron Law — Gate-Owned HOL4 Kernel Auditor.
  Invoked by scripts/iron_law.py AFTER Holmake completes.

  Verifies directly against the HOL4 kernel:
    1. Top-level theorem exists, has 0 hypotheses, and only DISK_THM oracle tag.
    2. Every theorem and definition in all forge_* theories in the ancestry has
       0 hypotheses and only DISK_THM oracle tags.
    3. Transitive DB.axioms closure contains ONLY the 4 standard bool axioms:
       bool.BOOL_CASES_AX, bool.ETA_AX, bool.INFINITY_AX, bool.SELECT_AX.
    4. Top-level theorem mentions the required verified constants (non-trivial).
    5. Extracts raw verified ARM64 bytes directly from proved theorem definitions:
         - theorem_code.bin     (CakeML compiled code bytes from code_def)
         - theorem_data.bin     (CakeML compiled bitmap words from data_def)
         - theorem_veneers.bin  (export_arm8 cml_main + FFI veneers from forge_shimProof)
         - theorem_shim.bin     (raw Linux AArch64 shim bytes from forge_shimProof)
         - theorem_layout.txt   (key=value constants: vaddrs, cbspace, lengths)
*)

open HolKernel Parse boolLib bossLib wordsLib;

fun die msg = (TextIO.output (TextIO.stdErr, "HOL_AUDIT_FAIL: " ^ msg ^ "\n");
               OS.Process.exit OS.Process.failure);

fun req_env k =
  case OS.Process.getEnv k of
    SOME v => if size v > 0 then v else die ("empty env " ^ k)
  | NONE => die ("missing env " ^ k);

val final_thy_name = req_env "FORGE_AUDIT_THEORY";
val final_thm_name = req_env "FORGE_AUDIT_THEOREM";
val compile_thy_name = req_env "FORGE_AUDIT_COMPILE_THY";
val shim_thy_name = req_env "FORGE_AUDIT_SHIM_THY";
val out_dir = req_env "FORGE_AUDIT_OUT_DIR";

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

(* 1. Audit top-level theorem *)
val final_th = DB.fetch final_thy_name final_thm_name
  handle e => die ("missing theorem " ^ final_thy_name ^ "." ^ final_thm_name ^ ": " ^ General.exnMessage e);
val _ = check_tag (final_thy_name ^ "." ^ final_thm_name) final_th;

(* 2. Audit transitive ancestry: axioms and all forge_* theorems/definitions *)
val closure = final_thy_name :: Theory.ancestry final_thy_name;
val all_axioms =
  List.concat (map (fn thy => map (fn (nm, _) => thy ^ "." ^ nm) (DB.axioms thy)) closure);

val allowed_axioms =
  ["bool.BOOL_CASES_AX", "bool.ETA_AX", "bool.INFINITY_AX", "bool.SELECT_AX"];

fun mem s xs = List.exists (fn x => x = s) xs;
val extra_axioms = List.filter (fn a => not (mem a allowed_axioms)) all_axioms;
val _ = if null extra_axioms then ()
        else die ("unexpected axioms in closure: " ^ String.concatWith "," extra_axioms);
val _ = if length all_axioms = 4 then ()
        else die ("expected 4 bool axioms, got " ^ Int.toString (length all_axioms));

val forge_thys = List.filter (String.isPrefix "forge_") closure;
val _ = if length forge_thys >= 4 then ()
        else die ("unexpectedly few forge_* theories in closure: " ^ Int.toString (length forge_thys));

val _ = List.app (fn thy =>
  List.app (fn (nm, th) => check_tag (thy ^ "." ^ nm) th)
    (DB.theorems thy @ DB.definitions thy)
) forge_thys;

(* 3. Verify top-level theorem is non-trivial and references required constants *)
fun has_const name tm =
  can (find_term (fn t => is_const t andalso fst (dest_const t) = name)) tm;

val req_consts =
  ["machine_sem", "real_mc", "arm8_target_real", "counter_run", "sent_frames_of",
   "svc_read_rel", "svc_write_rel", "svc_exit_group_rel", "code", "data"];

val _ = List.app (fn c =>
  if has_const c (concl final_th) then ()
  else die ("final theorem missing required constant: " ^ c)
) req_consts;

(* 4. Helper: extract word8 / word32 / word64 byte blobs from proved HOL4 defs *)
fun eval_to_rhs th =
  let val th' = CONV_RULE (RAND_CONV EVAL) th
  in rhs (concl th') end;

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

(* 5. Extract verified code bytes, bitmaps, veneers, and shim words without printing huge terms *)
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

  val veneers_def = DB.fetch shim_thy_name "forge_veneers_words_def"
    handle e => die ("missing " ^ shim_thy_name ^ ".forge_veneers_words_def")
  val shim_def = DB.fetch shim_thy_name "forge_shim_words_def"
    handle e => die ("missing " ^ shim_thy_name ^ ".forge_shim_words_def")
  val _ = (check_tag "forge_veneers_words_def" veneers_def; check_tag "forge_shim_words_def" shim_def)

  val veneers_vec = word32_list_to_le_bytes (eval_to_rhs veneers_def)
  val shim_vec = word32_list_to_le_bytes (eval_to_rhs shim_def)
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_veneers.bin")) veneers_vec
  val _ = write_bin (OS.Path.concat (out_dir, "theorem_shim.bin")) shim_vec

  val layout_os = TextIO.openOut (OS.Path.concat (out_dir, "theorem_layout.txt"))
  val _ = TextIO.output (layout_os,
    "closure_nodes=" ^ Int.toString (length closure) ^ "\n" ^
    "forge_theories=" ^ Int.toString (length forge_thys) ^ "\n" ^
    "axioms=" ^ Int.toString (length all_axioms) ^ "\n" ^
    "code_bytes=" ^ Int.toString (Word8Vector.length code_vec) ^ "\n" ^
    "data_bytes=" ^ Int.toString (Word8Vector.length data_vec) ^ "\n" ^
    "veneers_bytes=" ^ Int.toString (Word8Vector.length veneers_vec) ^ "\n" ^
    "shim_bytes=" ^ Int.toString (Word8Vector.length shim_vec) ^ "\n")
  val _ = TextIO.closeOut layout_os
in
  print ("AUDIT_OK closure_nodes=" ^ Int.toString (length closure) ^
         " forge_theories=" ^ Int.toString (length forge_thys) ^
         " axioms=4 code_bytes=" ^ Int.toString (Word8Vector.length code_vec) ^
         " data_bytes=" ^ Int.toString (Word8Vector.length data_vec) ^
         " veneers_bytes=" ^ Int.toString (Word8Vector.length veneers_vec) ^
         " shim_bytes=" ^ Int.toString (Word8Vector.length shim_vec) ^ "\n")
end;
val _ = OS.Process.exit OS.Process.success;
