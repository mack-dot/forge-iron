(*
  Forge Iron Law — Automated Kernel-Verified Theorem Catalog Exporter.

  Loads all compiled `forge_*` theories directly from HOL4 `.dat` theory files,
  audits every theorem and definition tag against the HOL4 kernel, and emits
  a deterministic Markdown catalog to `FORGE_CATALOG_OUT` (default:
  `../../docs/THEOREM_CATALOG.md`).

  Verified byte-for-byte by `scripts/iron_law.py` so stale or hand-edited
  theorem claims fail the gate.
*)

open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.raw_terminal;
val _ = Globals.linewidth := 100;
val _ = Globals.show_tags := false;
val _ = Globals.show_types := false;
val _ = Globals.show_assums := false;

fun die msg = (
  TextIO.output (TextIO.stdErr, "CATALOG_EXPORT_FAIL: " ^ msg ^ "\n");
  OS.Process.exit OS.Process.failure
);

val out_path =
  case OS.Process.getEnv "FORGE_CATALOG_OUT" of
    SOME p => if size p > 0 then p else "../../docs/THEOREM_CATALOG.md"
  | NONE => "../../docs/THEOREM_CATALOG.md";

val final_thy_name =
  case OS.Process.getEnv "FORGE_AUDIT_THEORY" of
    SOME t => if size t > 0 then t else "forge_m1Kernel"
  | NONE => "forge_m1Kernel";

val checkpoint_mode =
  case OS.Process.getEnv "FORGE_CATALOG_CHECKPOINT" of
    SOME "1" => true
  | _ => false;

(* Canonical ordered list of M1 theories, plus any extra forge_* theories in closure *)
val canonical_order = [
  ("forge_counterSpec",    "Pure Spec",               "Fixed-width LE64 framing, 16-byte chunking, conservation invariants, and total 2-FFI oracle"),
  ("forge_contractSpec",   "Hardware & OS Contract",  "SHA-256 pinned ELF virtual addresses, linked veneer/shim words, ARMv8 real-bits target, and Linux svc #0 contracts"),
  ("forge_counterProg",    "Zero-Basis CakeML",       "Allocation-free 17-byte-buffer CakeML counter loop and CF total correctness proof"),
  ("forge_counterCompile", "Verified Compilation",    "In-logic ARM64 backend compilation theorem linking counter_prog to exact machine-code bytes and bitmaps"),
  ("forge_arm8Erasure",    "ARMv8 Erasure & No-SVC0", "Exact ARMv8 step equivalence under real EL0 bits (TBI0/TBI1/SA0) and proof that compiled code never emits svc #0"),
  ("forge_shimProof",      "Boot & Syscall Shim",     "43-step ELF startup proof plus universal safety and liveness over Linux read(63)/write(64)/exit_group(94) syscalls"),
  ("forge_m1Kernel",       "Unified End-to-End",      "Whole-binary ARM64 execution theorem from _start (0x421000) to svc #0 exit_group(94) and non-vacuity witness")
];

fun mem s xs = List.exists (fn x => x = s) xs;
fun add_unique x xs = if mem x xs then xs else x :: xs;

(* In full mode (default & iron_law.py), load final_thy_name strictly.
   In checkpoint mode (FORGE_CATALOG_CHECKPOINT=1), load all built canonical theories. *)
val (loaded_roots, pending_theories) =
  if not checkpoint_mode then (
    (load (final_thy_name ^ "Theory"))
    handle e => die ("cannot load " ^ final_thy_name ^ "Theory: " ^ General.exnMessage e);
    ([final_thy_name], [] : (string * string * string) list)
  ) else (
    let
      val loaded = ref ([] : string list)
      val pending = ref ([] : (string * string * string) list)
      fun try_one (entry as (thy, _, _)) =
        if OS.FileSys.access (thy ^ "Theory.dat", [OS.FileSys.A_READ]) orelse
           OS.FileSys.access (".hol/objs/" ^ thy ^ "Theory.dat", [OS.FileSys.A_READ]) then (
          (load (thy ^ "Theory"); loaded := !loaded @ [thy])
          handle e => die ("cannot load built " ^ thy ^ "Theory: " ^ General.exnMessage e)
        ) else (
          pending := !pending @ [entry]
        )
    in
      List.app try_one canonical_order;
      if null (!loaded) then die "checkpoint mode found zero compiled forge_* theories"
      else (!loaded, !pending)
    end
  );

val closure =
  List.foldl (fn (root, acc) =>
    List.foldl (fn (t, a) => add_unique t a) acc (root :: Theory.ancestry root)
  ) [] loaded_roots;

val forge_in_closure = List.filter (String.isPrefix "forge_") closure;

fun sort_strings xs =
  let
    fun insert x [] = [x]
      | insert x (y::ys) = if String.compare (x, y) <> GREATER then x::y::ys else y::insert x ys
  in
    List.foldl (fn (x, acc) => insert x acc) [] xs
  end;

fun sort_named_thms xs =
  let
    fun insert (p as (k, _)) [] = [p]
      | insert (p as (k, _)) ((q as (k', _))::ys) =
          if String.compare (k, k') <> GREATER then p::q::ys else q::insert p ys
  in
    List.foldl (fn (p, acc) => insert p acc) [] xs
  end;

val ordered_theories =
  let
    val canonical_names = map #1 canonical_order
    val present_canonical = List.filter (fn (t, _, _) => mem t forge_in_closure) canonical_order
    val extra_names = sort_strings (List.filter (fn t => not (mem t canonical_names)) forge_in_closure)
    val extra_entries = map (fn t => (t, "Additional Theory", "Compiled forge_* theory in transitive closure")) extra_names
  in
    present_canonical @ extra_entries
  end;

val _ = if length ordered_theories = 0 then die "no forge_* theories in closure" else ();

(* Collect transitive axioms *)
val all_axioms =
  sort_strings (List.concat (map (fn thy => map (fn (nm, _) => thy ^ "." ^ nm) (DB.axioms thy)) closure));

val allowed_axioms =
  ["bool.BOOL_CASES_AX", "bool.ETA_AX", "bool.INFINITY_AX", "bool.SELECT_AX"];

val _ =
  if all_axioms = allowed_axioms then ()
  else die ("unexpected transitive axioms: " ^ String.concatWith ", " all_axioms);

(* Tag inspection helpers *)

val max_hyps = ref 0;
val all_oracles = ref ([] : string list);
val all_direct_axioms = ref ([] : string list);
val total_defs = ref 0;
val total_thms = ref 0;

fun inspect_thm ctx th =
  let
    val hcount = length (Thm.hyp th)
    val (ors, axs) = Tag.dest_tag (Thm.tag th)
    val ors_sorted = sort_strings ors
    val axs_sorted = sort_strings axs
  in
    if hcount > !max_hyps then max_hyps := hcount else ();
    List.app (fn o_nm => all_oracles := add_unique o_nm (!all_oracles)) ors_sorted;
    List.app (fn a_nm => all_direct_axioms := add_unique a_nm (!all_direct_axioms)) axs_sorted;
    if hcount <> 0 then die ("non-empty hypotheses in " ^ ctx)
    else if not (null axs_sorted) then die ("direct axiom tag in " ^ ctx ^ ": " ^ String.concatWith "," axs_sorted)
    else if not (List.all (fn x => x = "DISK_THM") ors_sorted) then
      die ("forbidden oracle tag in " ^ ctx ^ ": " ^ String.concatWith "," ors_sorted)
    else (hcount, ors_sorted, axs_sorted)
  end;

fun fmt_list [] = "[]"
  | fmt_list xs = "[" ^ String.concatWith ", " xs ^ "]";

fun term_size_exceeds limit tm =
  let
    exception Exceeded
    fun go n t =
      if n > limit then raise Exceeded
      else if is_comb t then
        let val (f, x) = dest_comb t
        in go (go (n + 1) f) x end
      else if is_abs t then
        go (n + 1) (body t)
      else n + 1
  in
    (ignore (go 0 tm); false) handle Exceeded => true
  end;

fun render_thm_stmt th =
  if term_size_exceeds 1500 (concl th) then
    let
      val lhs_s =
        let val l = lhs (concl th) in
          if term_size_exceeds 200 l then "<large term>" else term_to_string l
        end
        handle _ => "<large theorem>"
    in
      "⊢ " ^ lhs_s ^
      " = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>"
    end
  else
    let
      val s = Hol_pp.thm_to_string th
    in
      if size s <= 12000 then s
      else
        let
          val lhs_s =
            (term_to_string (lhs (concl th)))
            handle _ => "<large theorem>"
        in
          "⊢ " ^ lhs_s ^ " = <omitted " ^ Int.toString (size s) ^
          "-char compiled constant; raw bytes verified by scripts/hol_audit.sml and scripts/elf64_check.py>"
        end
    end;

(* Verify existence of crown-jewel theorems & definitions directly in the HOL4 kernel *)
val crown_jewels = [
  ("Pure Spec",               "forge_counterSpec",    "counter_run_preserves_cap",           "Multi-frame counter trace never exceeds cap_val (10,000) without wraparound."),
  ("Pure Spec",               "forge_counterSpec",    "counter_step_no_overflow",            "Every accepted frame increments spent and seq exactly in natural arithmetic with zero 64-bit overflow."),
  ("Pure Spec",               "forge_counterSpec",    "counter_step_overflow_attack_rejected","Adversarial max-u64 (0xFFFFFFFFFFFFFFFF) spend requests are rejected with state unchanged."),
  ("Pure Spec",               "forge_counterSpec",    "counter_step_replay_rejected",        "Replayed sequence numbers are rejected with state unchanged."),
  ("Pure Spec",               "forge_counterSpec",    "counter_step_gap_rejected",           "Skipped sequence numbers (seq + 2) are rejected with state unchanged."),
  ("Hardware & OS Contract",  "forge_contractSpec",   "forge_elf_loaded_def",                "SHA-256 pinned initial EL0 ARM64 CPU and ELF memory contract at _start (0x421000)."),
  ("Hardware & OS Contract",  "forge_contractSpec",   "whole_step_def",                      "SHA-256 pinned whole-binary transition relation combining raw arm8$Next with Linux read(63)/write(64) svc #0 contracts."),
  ("Zero-Basis CakeML",       "forge_counterProg",    "counter_semantics",                   "Zero-Basis CakeML counter_prog terminates cleanly and emits exact counter_run frames under all write limits."),
  ("Verified Compilation",    "forge_counterCompile", "counter_compiled",                    "In-logic CakeML arm8 backend evaluation theorem binding counter_prog to exact machine-code bytes (code) and bitmaps (data)."),
  ("ARMv8 Erasure & No-SVC0", "forge_arm8Erasure",    "encoded_bytes_in_mem_not_svc0",       "No compiled CakeML arm8_config instruction ever encodes the AArch64 svc #0 opcode (0xD4000001)."),
  ("ARMv8 Erasure & No-SVC0", "forge_arm8Erasure",    "arm8_target_exact_encoder_correct",   "Exact arm8$Next encoder correctness proving zero CPU exceptions and strict SP_EL0 preservation on every compiled instruction."),
  ("ARMv8 Erasure & No-SVC0", "forge_arm8Erasure",    "machine_sem_real_eq_exact",           "Unconditional equivalence between real-bits arm8_target_real (TBI0/TBI1/SA0) and erased targetSem with zero b ≠ Fail escape hatch."),
  ("Boot & Syscall Shim",     "forge_shimProof",      "startup_to_cake_main",                "Exact 43-step ARM64 proof from _start (0x421000) through cml_main to cake_main (0x4000B0) setting heap/stack/codebuffer headers."),
  ("Boot & Syscall Shim",     "forge_shimProof",      "ffirecv16_universal",                 "Universal safety of raw ARM64 ffirecv16 over arbitrary partial reads (1..16B), EINTR retries, truncated <16B EOF, and fatal read errors."),
  ("Boot & Syscall Shim",     "forge_shimProof",      "ffisend16_universal",                 "Universal safety of raw ARM64 ffisend16 over arbitrary partial writes (1..16B), EINTR retries, and fatal write/EPIPE errors."),
  ("Boot & Syscall Shim",     "forge_shimProof",      "cake_exit_universal",                 "Universal termination proof of exit veneer + cml_exit to Linux svc #0 exit_group(94) with code 0 or 1."),
  ("Non-Vacuity Witness",     "forge_m1Kernel",       "forge_m1_nonvacuous",                 "Constructive witness exhibiting a concrete Linux EL0 ARM64 state (TBI0=T, TBI1=F, SA0=T, 16B-aligned SP_EL0) satisfying forge_elf_loaded."),
  ("Unified End-to-End",      "forge_m1Kernel",       "forge_m1_kernel_correct",             "Single whole-binary theorem (exact Term.aconv-pinned) connecting _start (0x421000) across RTC whole_step to svc #0 exit_group(94) and counter_run.")
];

val pending_names = map #1 pending_theories;

val _ = List.app (fn (_, thy, nm, _) =>
  if checkpoint_mode andalso mem thy pending_names then ()
  else
    let
      val th = DB.fetch thy nm
        handle e => die ("missing crown-jewel item " ^ thy ^ "." ^ nm ^ ": " ^ General.exnMessage e)
      val _ = inspect_thm ("crown:" ^ thy ^ "." ^ nm) th
    in () end
) crown_jewels;

(* Gather per-theory data *)
val theory_data = map (fn (thy, layer, desc) =>
  let
    val defs = sort_named_thms (DB.definitions thy)
    val thms = sort_named_thms (DB.theorems thy)
    val def_rows = map (fn (nm, th) =>
      let val meta = inspect_thm (thy ^ "." ^ nm) th
      in (nm, meta, render_thm_stmt th) end
    ) defs
    val thm_rows = map (fn (nm, th) =>
      let val meta = inspect_thm (thy ^ "." ^ nm) th
      in (nm, meta, render_thm_stmt th) end
    ) thms
    val _ = total_defs := !total_defs + length def_rows
    val _ = total_thms := !total_thms + length thm_rows
  in
    (thy, layer, desc, def_rows, thm_rows)
  end
) ordered_theories;

val global_oracles_sorted = sort_strings (!all_oracles);
val global_direct_axs_sorted = sort_strings (!all_direct_axioms);

(* Emit deterministic Markdown *)
val os = TextIO.openOut out_path;
fun wl s = TextIO.output (os, s ^ "\n");

val _ = (
  wl "# Verified Theorem Catalog";
  wl "";
  wl "> **Auto-generated directly from compiled HOL4 `.dat` theory files** by `scripts/export_theorem_catalog.sml`.";
  if checkpoint_mode andalso not (null pending_theories) then
    wl "> **Mid-milestone checkpoint snapshot** (`pending` downstream theories remain; final `scripts/iron_law.py` requires 100% compiled and zero `pending`)."
  else
    wl "> Verified byte-for-byte on every run of `scripts/iron_law.py`. Do not hand-edit this file.";
  wl "";
  wl "## Global HOL4 Kernel Tag Summary";
  wl "";
  wl "| Metric | Measured Kernel Value |";
  wl "| --- | --- |";
  wl ("| Top-level theory | `" ^ final_thy_name ^ (if checkpoint_mode andalso not (null pending_theories) then "` (checkpoint — pending)" else "`") ^ " |");
  wl ("| `forge_*` theories compiled | `" ^ Int.toString (length theory_data) ^ "`" ^ (if null pending_theories then "" else " (`" ^ Int.toString (length pending_theories) ^ "` pending)") ^ " |");
  wl ("| Transitive ancestry closure size | `" ^ Int.toString (length closure) ^ "` theories |");
  wl ("| Exported `forge_*` definitions | `" ^ Int.toString (!total_defs) ^ "` |");
  wl ("| Exported `forge_*` theorems | `" ^ Int.toString (!total_thms) ^ "` |");
  wl ("| Total verified `forge_*` items | `" ^ Int.toString (!total_defs + !total_thms) ^ "` |");
  wl ("| `HYP_COUNT` (max hypotheses across all items) | `" ^ Int.toString (!max_hyps) ^ "` |");
  wl ("| `ORACLES` (union of all theorem/definition oracle tags) | `" ^ fmt_list global_oracles_sorted ^ "` |");
  wl ("| `DIRECT_AXIOMS` (union of all direct axiom tags) | `" ^ fmt_list global_direct_axs_sorted ^ "` |");
  wl ("| `AXIOMS` (transitive `DB.axioms` closure) | `" ^ Int.toString (length all_axioms) ^ "`: `" ^ String.concatWith "`, `" all_axioms ^ "` |");
  wl "";
  wl "## Crown-Jewel Specifications & Theorems";
  wl "";
  wl "| Layer | Theory | Theorem / Definition | Status | Plain-English Guarantee |";
  wl "| --- | --- | --- | --- | --- |";
  List.app (fn (layer, thy, nm, summary) =>
    let val st = if checkpoint_mode andalso mem thy pending_names then "`pending`" else "`verified`"
    in wl ("| " ^ layer ^ " | `" ^ thy ^ "` | `" ^ nm ^ "` | " ^ st ^ " | " ^ summary ^ " |") end
  ) crown_jewels;
  wl "";
  wl "## Theory-by-Theory Counts";
  wl "";
  wl "| Theory | Layer | Status | Definitions | Theorems | Max `HYP` | Oracles | Direct Axioms |";
  wl "| --- | --- | --- | ---: | ---: | ---: | --- | --- |";
  List.app (fn (thy, layer, _, def_rows, thm_rows) =>
    let
      val all_rows = def_rows @ thm_rows
      val thy_ors = sort_strings (List.foldl (fn ((_, (_, ors, _), _), acc) =>
        List.foldl (fn (o_nm, a) => add_unique o_nm a) acc ors) [] all_rows)
      val thy_axs = sort_strings (List.foldl (fn ((_, (_, _, axs), _), acc) =>
        List.foldl (fn (a_nm, a) => add_unique a_nm a) acc axs) [] all_rows)
    in
      wl ("| `" ^ thy ^ "` | " ^ layer ^ " | `verified` | " ^ Int.toString (length def_rows) ^
          " | " ^ Int.toString (length thm_rows) ^ " | 0 | `" ^ fmt_list thy_ors ^
          "` | `" ^ fmt_list thy_axs ^ "` |")
    end
  ) theory_data;
  List.app (fn (thy, layer, _) =>
    wl ("| `" ^ thy ^ "` | " ^ layer ^ " | `pending` | — | — | — | — | — |")
  ) pending_theories;
  wl "";
  wl "## Verbatim Exported Statements (`DB.definitions` & `DB.theorems`)";
  wl "";
  wl "Each section below dumps every exported definition and theorem directly from the compiled HOL4 `.dat` file using `Hol_pp.thm_to_string`.";
  wl "";
  List.app (fn (thy, layer, desc, def_rows, thm_rows) => (
    wl ("<details>");
    wl ("<summary><strong><code>" ^ thy ^ "</code></strong> — " ^ layer ^
        " (" ^ Int.toString (length def_rows) ^ " definitions, " ^
        Int.toString (length thm_rows) ^ " theorems)</summary>");
    wl "";
    wl (desc ^ ".");
    wl "";
    if not (null def_rows) then (
      wl "### Definitions";
      wl "";
      List.app (fn (nm, (hc, ors, axs), stmt) => (
        wl ("#### `" ^ thy ^ "." ^ nm ^ "`");
        wl ("- Kernel tags: `HYP_COUNT=" ^ Int.toString hc ^
            "`, `ORACLES=" ^ fmt_list ors ^ "`, `DIRECT_AXIOMS=" ^ fmt_list axs ^ "`");
        wl "";
        wl "```text";
        wl stmt;
        wl "```";
        wl ""
      )) def_rows
    ) else ();
    if not (null thm_rows) then (
      wl "### Theorems";
      wl "";
      List.app (fn (nm, (hc, ors, axs), stmt) => (
        wl ("#### `" ^ thy ^ "." ^ nm ^ "`");
        wl ("- Kernel tags: `HYP_COUNT=" ^ Int.toString hc ^
            "`, `ORACLES=" ^ fmt_list ors ^ "`, `DIRECT_AXIOMS=" ^ fmt_list axs ^ "`");
        wl "";
        wl "```text";
        wl stmt;
        wl "```";
        wl ""
      )) thm_rows
    ) else ();
    wl "</details>";
    wl ""
  )) theory_data
);

val _ = TextIO.closeOut os;
val status_tag =
  if checkpoint_mode andalso not (null pending_theories) then "CATALOG_EXPORT_CHECKPOINT_OK"
  else "CATALOG_EXPORT_OK";
val _ = print (status_tag ^ " theories=" ^ Int.toString (length theory_data) ^
               " pending=" ^ Int.toString (length pending_theories) ^
               " defs=" ^ Int.toString (!total_defs) ^
               " thms=" ^ Int.toString (!total_thms) ^
               " axioms=" ^ Int.toString (length all_axioms) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
