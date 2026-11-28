(*
  Forge Iron Law — Automated Kernel-Verified Theorem Catalog Exporter (Frozen Runtime Edition).

  Loads all compiled `forge_*` theories directly from HOL4 `.dat` theory files,
  audits every theorem and definition tag against the HOL4 kernel, and emits
  a deterministic Markdown catalog to `FORGE_CATALOG_OUT` (default:
  `../../../docs/THEOREM_CATALOG.md`).

  Verified byte-for-byte by `runtime/iron_law.py` (delegated from `scripts/iron_law.py`).
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
    SOME p => if size p > 0 then p else "../../../docs/THEOREM_CATALOG.md"
  | NONE => "../../../docs/THEOREM_CATALOG.md";

val final_thy_name =
  case OS.Process.getEnv "FORGE_AUDIT_THEORY" of
    SOME t => if size t > 0 then t else "forge_m1Kernel"
  | NONE => "forge_m1Kernel";

val checkpoint_mode =
  case OS.Process.getEnv "FORGE_CATALOG_CHECKPOINT" of
    SOME "1" => true
  | _ => false;

val canonical_order = [
  ("forge_counterSpec",      "Pure Spec (M1)",          "Fixed-width LE64 framing, 16-byte chunking, conservation invariants, and total 2-FFI oracle"),
  ("forge_guardrailSpec",    "Pure Spec (M2)",          "Frozen 91-line pure HOL4 AI spending guardrail spec (deposit, spend, refund, query, conservation, cap, nonce, allowlist)"),
  ("forge_runtimeSpec",      "Frozen Runtime Contract", "SHA-256 pinned 256 KB RX slot [0x400000..0x440000), fixed _start=0x450000, parameterized veneers, 16B/64B shims, and Linux svc #0 contracts"),
  ("forge_frame64Spec",      "Generic 64B Frame ABI",   "Fixed 64-byte LE64 binary frame bijection, 64-byte chunking, polymorphic trace runner, and total recv64/send64 FFI oracle"),
  ("forge_frameRunner",      "Generic 64B ML Runner",   "Polymorphic Zero-Basis CakeML 64-byte frame runner (recv64 -> translated step -> send64) for zero-SL kernel synthesis"),
  ("forge_counterProg",      "Zero-Basis CakeML (M1)",  "Allocation-free 17-byte-buffer CakeML counter loop and CF total correctness proof"),
  ("forge_counterCompile",   "Verified Compilation",    "In-logic ARM64 backend compilation theorem linking counter_prog to exact machine-code bytes and bitmaps"),
  ("forge_guardrailProg",    "Zero-SL CakeML (M2)",     "Automatically ml_translator-synthesized CakeML guardrail program composed with frozen forge_frameRunner"),
  ("forge_guardrailCompile", "Verified Compilation",    "In-logic ARM64 backend compilation theorem linking guardrail_prog to exact machine-code bytes and bitmaps"),
  ("forge_arm8Erasure",      "ARMv8 Erasure & No-SVC0", "Exact ARMv8 step equivalence under real EL0 bits (TBI0/TBI1/SA0) and proof that compiled code never emits svc #0"),
  ("forge_shimProof",        "Frozen 256KB Shim Proof", "Parameterized 43-step ELF startup proof (_start=0x450000) for any <=256KB code blob plus universal 16B & 64B Linux syscall safety and liveness"),
  ("forge_slotUtil",         "Frozen 256KB Slot Util",  "Parameterized slot layout arithmetic, installed proof, and constructive non-vacuity witness for any <=256KB kernel"),
  ("forge_frame64Compose",   "Generic 64B E2E Compose", "Polymorphic whole-binary ARM64 composition theorem lifting any 64-byte ml_translator kernel from _start to exit_group(94)"),
  ("forge_sha256Spec",       "Verified Crypto (M3)",    "SHA-256 pinned pure FIPS 180-4 SHA-256 and RFC 2104 HMAC-SHA256 specifications verified against official NIST/RFC test vectors"),
  ("forge_airlockFfi",       "M3 4-FFI Airlock ABI",    "SHA-256 pinned 128-byte response frame bijection, dual-slot airlock_exec trace, and total 4-FFI oracle (bootload/commit/recv64/send128)"),
  ("forge_airlockContract",  "M3 6-Syscall Contract",   "SHA-256 pinned M3 256 KB RX slot, 52-word veneers, 168-word airlock shim, and 6-syscall Linux AArch64 dual-slot OS contract"),
  ("forge_airlockSpec",      "Pure Spec (M3)",          "SHA-256 pinned crypto-authenticated crash-atomic airlock spec (keyed-HMAC dual slots, conservation, capability tokens, idempotent retry)"),
  ("forge_airlockRunner",    "M3 4-FFI ML Runner",      "Polymorphic Zero-Basis CakeML 4-FFI crash-atomic airlock runner (bootload -> recv64 -> step -> commit -> send128) with boot-once invariant"),
  ("forge_airlockProg",      "Zero-SL CakeML (M3)",     "Automatically ml_translator-synthesized CakeML crypto-airlock program (SHA-256, HMAC-SHA256, dual-slot recovery, guardrail step)"),
  ("forge_airlockCompile",   "Verified Compilation",    "In-logic ARM64 backend compilation theorem linking airlock_prog to exact machine-code bytes and bitmaps"),
  ("forge_airlockShimBase",  "M3 256KB Shim Base",      "M3 256 KB slot disjointness, patch_bytes/pad512 laws, 4-FFI machine config, interference lifting, and constructive non-vacuity"),
  ("forge_airlockShimStart", "M3 Startup & Exit Proof", "43-step ARM64 startup proof (_start=0x450000 -> cake_main=0x4000D0), exact installed proof, and universal exit/install stubs"),
  ("forge_airlockShimIo",    "M3 I/O Syscall Proofs",   "Universal safety and error-free liveness proofs for raw ARM64 ffirecv64 (fd 0) and ffisend128 (fd 1)"),
  ("forge_airlockShimProof", "M3 Disk/Boot Proofs",     "Universal safety and liveness proofs for raw ARM64 fficommit (pwrite64 + fdatasync durability) and ffibootload (fd 4 key + fd 3 pread64)"),
  ("forge_airlockCompose",   "M3 4-FFI E2E Compose",    "Polymorphic whole-binary ARM64 composition theorem lifting any 4-FFI crypto-airlock kernel from _start to exit_group(94)"),
  ("forge_m1Kernel",         "Unified End-to-End (M1)", "Whole-binary ARM64 counter execution theorem from _start (0x450000) to svc #0 exit_group(94) and non-vacuity witness"),
  ("forge_m2Kernel",         "Unified End-to-End (M2)", "Whole-binary ARM64 guardrail execution theorem from _start (0x450000) to svc #0 exit_group(94) and non-vacuity witness"),
  ("forge_m3Kernel",         "Unified End-to-End (M3)", "Whole-binary ARM64 crypto-airlock execution theorem from _start (0x450000) across 6 Linux syscalls to exit_group(94) and non-vacuity witness")
];

fun mem s xs = List.exists (fn x => x = s) xs;
fun add_unique x xs = if mem x xs then xs else x :: xs;

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
        (load (thy ^ "Theory"); loaded := !loaded @ [thy])
        handle _ => (pending := !pending @ [entry])
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

val all_axioms =
  sort_strings (List.concat (map (fn thy => map (fn (nm, _) => thy ^ "." ^ nm) (DB.axioms thy)) closure));

val allowed_axioms =
  ["bool.BOOL_CASES_AX", "bool.ETA_AX", "bool.INFINITY_AX", "bool.SELECT_AX"];

val _ =
  if all_axioms = allowed_axioms then ()
  else die ("unexpected transitive axioms: " ^ String.concatWith ", " all_axioms);

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
      " = <omitted large compiled/AST term (>1500 AST nodes); kernel tags audited and raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>"
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
          "-char compiled constant; raw bytes verified by runtime/hol_audit.sml and runtime/elf64_check.py>"
        end
    end;

val crown_jewels = [
  ("Pure Spec (M1)",          "forge_counterSpec",      "counter_run_preserves_cap",           "Multi-frame counter trace never exceeds cap_val (10,000) without wraparound."),
  ("Pure Spec (M1)",          "forge_counterSpec",      "counter_step_no_overflow",            "Every accepted frame increments spent and seq exactly in natural arithmetic with zero 64-bit overflow."),
  ("Pure Spec (M1)",          "forge_counterSpec",      "counter_step_overflow_attack_rejected","Adversarial max-u64 (0xFFFFFFFFFFFFFFFF) spend requests are rejected with state unchanged."),
  ("Pure Spec (M1)",          "forge_counterSpec",      "counter_step_replay_rejected",        "Replayed sequence numbers are rejected with state unchanged."),
  ("Pure Spec (M1)",          "forge_counterSpec",      "counter_step_gap_rejected",           "Skipped sequence numbers (seq + 2) are rejected with state unchanged."),
  ("Pure Spec (M2)",          "forge_guardrailSpec",    "frame_bijection",                     "Lossless 64-byte LE64 encode/decode bijection for guardrail frames."),
  ("Pure Spec (M2)",          "forge_guardrailSpec",    "gr_run_preserves_inv",                "Exact fund conservation (deposits = balance + spent - refunds), rolling cap, and zero u64 wraparound across every request stream."),
  ("Pure Spec (M2)",          "forge_guardrailSpec",    "gr_safety_denials",                   "Non-allowlisted destinations, replayed nonces, and double refunds are unconditionally denied with state unchanged."),
  ("Frozen Runtime Contract", "forge_runtimeSpec",      "forge_slot_loaded_def",               "SHA-256 pinned 256 KB RX code slot [0x400000..0x440000) and fixed _start (0x450000) contract for any kernel."),
  ("Frozen Runtime Contract", "forge_runtimeSpec",      "whole_step_def",                      "SHA-256 pinned whole-binary transition relation combining raw arm8$Next with Linux read(63)/write(64) svc #0 contracts."),
  ("Generic 64B Frame ABI",   "forge_frame64Spec",      "frame64_roundtrip",                   "Round-trip bijection proving 64-byte LE64 binary framing is lossless for all 8-word frames."),
  ("Generic 64B ML Runner",   "forge_frameRunner",      "run_frame64_kernel_spec",             "Polymorphic CF specification of generic CakeML recv64 -> translated step -> send64 runner for zero-SL kernels."),
  ("Zero-Basis CakeML (M1)",  "forge_counterProg",      "counter_semantics",                   "Zero-Basis CakeML counter_prog terminates cleanly and emits exact counter_run frames under all write limits."),
  ("Verified Compilation",    "forge_counterCompile",   "counter_compiled",                    "In-logic CakeML arm8 backend evaluation theorem binding counter_prog to exact machine-code bytes (code) and bitmaps (data)."),
  ("Zero-SL CakeML (M2)",     "forge_guardrailProg",    "guardrail_semantics",                 "Automatically ml_translator-synthesized CakeML guardrail_prog terminates cleanly and emits exact frame64_run gr_step frames."),
  ("Verified Compilation",    "forge_guardrailCompile", "guardrail_compiled",                  "In-logic CakeML arm8 backend evaluation theorem binding guardrail_prog to exact machine-code bytes (code) and bitmaps (data)."),
  ("ARMv8 Erasure & No-SVC0", "forge_arm8Erasure",      "encoded_bytes_in_mem_not_svc0",       "No compiled CakeML arm8_config instruction ever encodes the AArch64 svc #0 opcode (0xD4000001)."),
  ("ARMv8 Erasure & No-SVC0", "forge_arm8Erasure",      "arm8_target_exact_encoder_correct",   "Exact arm8$Next encoder correctness proving zero CPU exceptions and strict SP_EL0 preservation on every compiled instruction."),
  ("ARMv8 Erasure & No-SVC0", "forge_arm8Erasure",      "machine_sem_real_eq_exact",           "Unconditional equivalence between real-bits arm8_target_real (TBI0/TBI1/SA0) and erased targetSem with zero b ≠ Fail escape hatch."),
  ("Frozen 256KB Shim Proof", "forge_shimProof",        "startup_to_cake_main_slot",           "Parameterized 43-step ARM64 proof from fixed _start (0x450000) through cml_main to cake_main (0x4000B0) for any <=256 KB code blob."),
  ("Frozen 256KB Shim Proof", "forge_shimProof",        "ffirecv16_universal_slot",            "Universal safety of raw ARM64 ffirecv16 at 0x450040 over partial reads, EINTR, truncated EOF, and fatal errors."),
  ("Frozen 256KB Shim Proof", "forge_shimProof",        "ffisend16_universal_slot",            "Universal safety of raw ARM64 ffisend16 at 0x4500C0 over partial writes, EINTR, and fatal/EPIPE errors."),
  ("Frozen 256KB Shim Proof", "forge_shimProof",        "ffirecv64_universal_slot",            "Universal safety of raw ARM64 ffirecv64 at 0x450040 over partial reads (1..64B), EINTR, truncated EOF, and fatal errors."),
  ("Frozen 256KB Shim Proof", "forge_shimProof",        "ffisend64_universal_slot",            "Universal safety of raw ARM64 ffisend64 at 0x4500C0 over partial writes (1..64B), EINTR, and fatal/EPIPE errors."),
  ("Frozen 256KB Shim Proof", "forge_shimProof",        "cake_exit_universal_slot",            "Universal termination proof of exit veneer + cml_exit to Linux svc #0 exit_group(94) with code 0 or 1."),
  ("Generic 64B E2E Compose", "forge_frame64Compose",   "forge_frame64_kernel_compose",        "Polymorphic whole-binary composition theorem lifting any ml_translator 64-byte kernel from _start to exit_group(94)."),
  ("Non-Vacuity Witness",     "forge_m1Kernel",         "forge_m1_nonvacuous",                 "Constructive witness exhibiting a concrete Linux EL0 ARM64 state (TBI0=T, TBI1=F, SA0=T, 16B-aligned SP_EL0) satisfying M1 forge_slot_loaded."),
  ("Unified End-to-End (M1)", "forge_m1Kernel",         "forge_m1_kernel_correct",             "Single whole-binary theorem (exact Term.aconv-pinned) connecting fixed _start (0x450000) across RTC whole_step to svc #0 exit_group(94) and counter_run."),
  ("Non-Vacuity Witness",     "forge_m2Kernel",         "forge_m2_nonvacuous",                 "Constructive witness exhibiting a concrete Linux EL0 ARM64 state (TBI0=T, TBI1=F, SA0=T, 16B-aligned SP_EL0) satisfying M2 forge_slot_loaded."),
  ("Unified End-to-End (M2)", "forge_m2Kernel",         "forge_m2_kernel_correct",             "Single whole-binary theorem (exact Term.aconv-pinned) connecting fixed _start (0x450000) across RTC whole_step to svc #0 exit_group(94) and frame64_run gr_step."),
  ("Verified Crypto (M3)",    "forge_sha256Spec",       "hmac_sha256_rfc4231_tc1",             "In-logic HOL4 proof verifying pure RFC 2104 HMAC-SHA256 matches official RFC 4231 Test Case 1 byte-for-byte."),
  ("Pure Spec (M3)",          "forge_airlockSpec",      "dual_slot_crash_recovery",            "Universal dual-slot crash recovery: keyed-HMAC slots recover exact prior state on torn write and exact new state on completed commit."),
  ("Pure Spec (M3)",          "forge_airlockSpec",      "airlock_run_preserves_inv",           "Exact natural-number fund conservation, rolling cap, and HMAC token invariant across every request stream."),
  ("Pure Spec (M3)",          "forge_airlockSpec",      "airlock_retry_idempotent",            "Idempotent retry returns the exact cached signed capability token with state unchanged and zero disk commit."),
  ("Pure Spec (M3)",          "forge_airlockSpec",      "airlock_emitted_token_authentic",     "Every non-zero emitted capability token matches HMAC-SHA256(key, FORGE-CAP-V1 || seq || op || dest || amt || bal)."),
  ("M3 4-FFI ML Runner",      "forge_airlockRunner",    "run_airlock_kernel_spec",             "Polymorphic CF specification of 4-FFI CakeML airlock runner with boot-once and crash-atomic commit ordering."),
  ("Zero-SL CakeML (M3)",     "forge_airlockProg",      "airlock_semantics",                   "Automatically ml_translator-synthesized CakeML airlock_prog terminates cleanly and emits exact airlock_exec frames."),
  ("Verified Compilation",    "forge_airlockCompile",   "airlock_compiled",                    "In-logic CakeML arm8 backend evaluation theorem binding airlock_prog to exact machine-code bytes (code) and bitmaps (data)."),
  ("M3 Startup & Exit Proof", "forge_airlockShimStart", "m3_startup_to_cake_main_slot",        "43-step ARM64 proof from fixed _start (0x450000) through 52-word veneers to cake_main (0x4000D0)."),
  ("M3 I/O Syscall Proofs",   "forge_airlockShimIo",    "m3_ffirecv64_universal_slot",         "Universal safety of raw ARM64 ffirecv64 (fd 0) over partial reads, EINTR, truncated EOF, and errors."),
  ("M3 I/O Syscall Proofs",   "forge_airlockShimIo",    "m3_ffisend128_universal_slot",        "Universal safety of raw ARM64 ffisend128 (fd 1) over partial writes (1..128B), EINTR, and errors."),
  ("M3 Disk/Boot Proofs",     "forge_airlockShimProof", "m3_fficommit_universal_slot",         "Universal crash-atomic durability proof of raw ARM64 fficommit (pwrite64(68) + fdatasync(83)) on fd 3."),
  ("M3 Disk/Boot Proofs",     "forge_airlockShimProof", "m3_ffibootload_universal_slot",       "Universal boot proof of raw ARM64 ffibootload (fd 4 32B key + fd 3 512B pread64(67) + zero-fill)."),
  ("M3 4-FFI E2E Compose",    "forge_airlockCompose",   "forge_airlock_kernel_compose",        "Polymorphic whole-binary composition theorem lifting any 4-FFI crypto-airlock kernel from _start to exit_group(94)."),
  ("Non-Vacuity Witness",     "forge_m3Kernel",         "forge_m3_nonvacuous",                 "Constructive witness exhibiting a concrete Linux EL0 ARM64 state (TBI0=T, TBI1=F, SA0=T, 16B-aligned SP_EL0) satisfying M3 forge_m3_slot_loaded."),
  ("Unified End-to-End (M3)", "forge_m3Kernel",         "forge_m3_kernel_correct",             "Single whole-binary theorem (exact Term.aconv-pinned) connecting fixed _start (0x450000) across 6-syscall m3_whole_step to exit_group(94) and keyed airlock_run.")
];

val pending_names = map #1 pending_theories;

val _ = List.app (fn (_, thy, nm, _) =>
  if not (mem thy forge_in_closure) then ()
  else if checkpoint_mode andalso mem thy pending_names then ()
  else
    let
      val th = DB.fetch thy nm
        handle e => die ("missing crown-jewel item " ^ thy ^ "." ^ nm ^ ": " ^ General.exnMessage e)
      val _ = inspect_thm ("crown:" ^ thy ^ "." ^ nm) th
    in () end
) crown_jewels;

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

val os = TextIO.openOut out_path;
fun wl s = TextIO.output (os, s ^ "\n");

val _ = (
  wl "# Verified Theorem Catalog";
  wl "";
  wl "> **Auto-generated directly from compiled HOL4 `.dat` theory files** by `runtime/export_theorem_catalog.sml`.";
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
    if not (mem thy forge_in_closure) andalso not (mem thy pending_names) then ()
    else
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
