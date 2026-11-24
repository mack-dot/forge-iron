# FORGE: THE MASTER PLAN

> Source note (2026-11-24). This is the owner's plan text. The source paste
> was damaged in three places: part of the Ring diagram and the start of
> Theorem 1 are missing, and the last sentence is cut. These places are marked
> `[LOST IN PASTE]`. Copy artifacts (letters split one per line, doubled
> arrows) were repaired. No other words were changed.
>
> Status: `end_to_end=false`. See `STATUS.md`. Nothing in this plan is proved yet.

## One-Sentence Thesis

Forge is a machine-code-verified execution engine that lets humans lock business
laws in plain, unambiguous English, lets untrusted AI vibe-code or optimize 99.9%
of the application at full speed, and makes it mathematically impossible—down to
ARM64 machine bytes and FPGA hardware gates—for bugs, race conditions, crashes, or
rogue agents to violate those laws in the real world.

## 0. Day-Zero Repo Reset & The Iron Law

**Archive the Research Lab:** Rename your current `mack-dot/forge` → `mack-dot/forge-lab`.
Nothing is lost—keep all 113 commits, M1-B notes, FarkasCert, RefundSpec,
Clearing, and the `bugs/` planted-bug corpus as your reference quarry.

**Create a Pristine `mack-dot/forge`:** Start clean with four top-level
directories and zero legacy glue.

**The Iron Law of CI:** Commit #1 starts at `end_to_end=true`. Every PR touching
`kernel/` or `spec-compiler/` must replay all HOL4 proofs from the ~2.5k-line
logic kernel (zero Z3 trust) and verify
`SHA256(compiled_binary) == theorem.machine_bytes_hash`. If `end_to_end` ever
drops to false, CI blocks merge.

> Owner decision 2026-11-24: commit #1 carries the gate and reports
> `end_to_end=false` honestly. The gate turns green only when Milestone 1 is
> really proved.

### What Is Permanently Banned From the Trusted Computing Base (TCB)

"The best way to solve a problem is to not have it."

- NO JSON, YAML, HTTP, TLS, DNS, or MCP parsers inside the TCB (fixed binary frames only).
- NO SQLite, Postgres, B-trees, or growing log files inside the TCB (one 32-byte Sparse Merkle root + untrusted host storage).
- NO threads, async runtimes, or file locks inside the TCB (single-threaded sequential loop).
- NO garbage collection or dynamic heap allocation in Ring 0 (Pancake / static buffers only).
- NO Z3, rustc, Node.js, or `/usr/bin/ssh-keygen` in the TCB.
- NO reliance on GitHub branch rulesets (protect-main) for runtime security (cryptographic human spec-signing enforced at boot).

## 1. Repository Architecture ("The 3-Ring Forge")

```text
forge/
├── kernel/              # [RING 0 - PROVED] ~400 LOC Pancake/CakeML + HOL4 M1-B & Silver RTL proofs
├── spec-compiler/       # [RING 1 - PROVED] HOL4 Bijective EnglikeML compiler
├── relay/               # [STATELESS EDGE]  ~35 LOC auditable capability-token -> Stripe/LLM gateway
├── sdk/                 # [RING 2 - UNTRUSTED] `npx forge` CLI, TS/Python SDK, SQLite Merkle tree,
│                        #                      Z3 Spec-Clearing Quiz, TouchID/FIDO2 UI, Cursor MCP
└── examples/
    ├── 01-vibe-saas/    # Vibe-coded Next.js credits, tenant auth & Stripe refunds
    ├── 02-escrow/       # Marketplace multi-state escrow finality
    └── 03-clearing-lp/  # 50-agent combinatorial clearing + Farkas optimality certificates
```

```text
                   HUMAN FOUNDER / VIBE CODER
                   │
                   │ 1. Reads & signs Plain Canonical English (`spec.lock`)
                   │    via TouchID / FIDO2 Ed25519 / $25 OLED Hardware Stick
                   ▼
╔═══════════════════════════════════════════════════════════════════════════╗
║  [Ring 1: Verified Spec Compiler (HOL4)]                                  ║
║   • Verified `decode_english(spec.lock)` <-> `ForgeSpec AST` (Bijective)  ║
║   • Built-in checkers: Conservation + Merkle Finality + Farkas Optimality ║
║                                    │                                      ║
║                                    ▼ compiles pure `Guest::step`          ║
║  [Ring 0: Iron Kernel (~400 LOC Pancake/CakeML)]                          ║
║   • Verifies human `Ed25519` signature over `(english_spec_hash, code)`   ║
║   • Checks 32-level Sparse Merkle proofs against 32-byte `state_root`     ║
║   • Commits 160-byte state across dual raw ping-pong sectors (Slot A / B) ║
║   • Mints `HMAC-SHA256` / `WOTS+` capability token for monotonic `seq`    ║
╚══════════════════▲═════════════════════════════════════╤══════════════════╝
                   │                                     │
   2. Binary frame: (action,                             │ 3. Signed capability token
      merkle_siblings, farkas_dual)                      │    (`seq`, `effect_hash`, `mac`)
                   │                                     ▼
┌──────────────────┴──────────────────────┐   ┌─────────────────────────────┐
│ [Ring 2: Untrusted App / Vibe Code]     │   │ [Stateless API Relay]       │
│ • 50,000 LOC Next.js, Python, Claude    │   │ • Holds Stripe / OpenAI key │
│ • Local SQLite DB + LP Solver (HiGHS)   │   │ • Verifies token MAC        │
│ • Zero raw API secrets in `.env`!       │   │ • Sets `Idempotency: seq`   │
└─────────────────────────────────────────┘   └─────────────────────────────┘
```

`[LOST IN PASTE]`: the rest of section 1, the heading of section 2, and the
start of Theorem 1. The surviving end of Theorem 1 reads:

> …ambiguity and zero hidden clauses. Not a single boundary condition, overflow
> rule, or auth bypass can exist in the compiled spec unless it appears visibly
> in the plain-English text signed by the human.

**Theorem 2 — ForgeSpec & Certificate Soundness (Closes Domain Semantics):**

```text
Guest::step(root, req, witness) = Ok(root', eff)  ⟺  ⟦decode_en(E)⟧(root, req, root', eff)
```

Meaning: Every accepted step satisfies exact integer conservation, Sparse Merkle
state-transition legality, tenant authorization, and—when declared—zero linear
duality gap (FarkasCert proving mathematical optimality).

**Theorem 3 — Crash-Atomic & Idempotent State Machine (Closes E1/E2 & Storage):**
Across arbitrary power-loss crashes at any sector write and arbitrary
duplicate/reordered retries, the sequence of signed capability tokens ever
emitted is a strict valid trace of S, with at-most-once execution per `seq`.

**Theorem 4 — Machine-Code & RTL Refinement (Closes M1-B & Silicon):**
Via the Pancake/CakeML verified backend (with real ARM64 Linux microVM syscall
premises proved, plus CakeML's Silver Verilog processor backend), the exact
binary/bitstream bytes refine the HOL4 kernel transition function.

## 3. The Two-Sided Product Experience

### Experience A: For Vibe Coders ("Move Fast, Mathematically Can't Get Drained")

- **Prompt in Messy English:** User tells Cursor/Claude: "Add user credits, promo redemptions, and Stripe refunds, max $200/day."
- **Interactive Spec Clearing (`npx forge clear`):** Untrusted Claude + Z3 translates the prompt into Canonical English and asks 2–3 multiple-choice dollar questions to clear edge cases ("Can promo credits be refunded for cash? [No / Yes]").
- **Sign Plain English (`npx forge approve`):** User reads the 12-line Canonical English card and taps TouchID / YubiKey (Ed25519) to lock `spec.lock`.
- **Live MCP Bug-Slayer (`npx forge dev`):** While Cursor vibe-codes the app, Forge's MCP server n tests at it; when Cursor's async handler races, Forge hands the exact Merkle conflict back to Cursor so it fixes its own code automatically. *(Source text: "n tests"; one or more words may be missing.)*
- **Zero-Key Deployment:** `STRIPE_SECRET_KEY` goes into `relay/`, never into the vibe-coded app. Even if the vibe-coded app gets prompt-injected or rooted in production, the founder cannot lose more than the signed spec permits.

### Experience B: For High-Stakes AI Infrastructure ("More Than an Airlock")

- Untrusted LLMs + Python solvers (scipy/HiGHS) run complex multi-party clearing houses, autonomous treasuries, procurement auctions, and scheduling engines outside the box.
- Every proposed batch submits `(proposed_fills, merkle_proofs, farkas_dual_prices)` into Ring 0.
- In < 0.5 milliseconds, Forge verifies exact zero-sum balance conservation across all accounts and verifies 0% optimality gap—rejecting hallucinated, collusive, or sloppy deals before a cent moves.

## 4. The 12-Week Execution Roadmap (8 Commits, Always end_to_end=true)

### Phase I: The Iron Spine (Weeks 1–3)

**Milestone 1 (Days 1–5) — Commit #1 (end_to_end=true Spike):**
Set up the new repo + CI replaying HOL4. Write a 60-line Pancake/CakeML counter
binary, fix the two false ARM64 premises from forge-lab, prove the 3-syscall
Linux microVM wrapper (read, write, pwrite/fdatasync), and enforce binary SHA-256
hash matching in CI.

**Milestone 2 (Week 2) — Verified SHA-256 + Dual-Slot Crash Recovery:**
Implement and prove allocation-free SHA-256, HMAC-SHA256, and the 160-byte
Slot A / Slot B atomic state store with `last_token` idempotent retry cache.
Replay all E1/E2 crash tests from `forge-lab/bugs/`.

**Milestone 3 (Week 3) — 32-Byte Sparse Merkle Engine + Boot Pinning (S1):**
Add the 32-level Merkle verifier + Ed25519 boot signature check over
`spec.lock`. Build the 35-line stateless `relay/` holding Stripe/OpenAI keys.

### Phase II: Plain English & Universal Certificates (Weeks 4–7)

**Milestone 4 (Weeks 4–5) — Bijective Canonical English + ForgeSpec v1:**
Build `decode_en` / `encode_en` + ForgeSpec compiler in HOL4 (supporting u64
integer conservation, caps, booleans, tenant auth, and Merkle state
transitions). Prove Theorems 1 & 2.

**Milestone 5 (Weeks 6–7) — FarkasCert Optimality & Multi-Party Clearing:**
Port linear primal-dual optimality checking (FarkasCert) into ForgeSpec v2 in
HOL4. Prove `examples/02-escrow` and `examples/03-clearing-lp` end-to-end down
to ARM64 machine code.

### Phase III: Vibe-Coder Magic & Auditability (Weeks 8–10)

**Milestone 6 (Weeks 8–9) — Zero-Friction SDK + Spec Clearing + Cursor MCP:**
Build `npx forge` (clear, approve via FIDO2/TouchID, dev sidecar, mcp server for
Claude Code/Cursor), automatic SQLite Merkle witness tracking, and automatic
HiGHS dual-witness extraction (`@forge.transact`).

**Milestone 7 (Week 10) — `forge verify-from-axioms` & Spec-to-Silicon Explorer:**
Ship the one-command (<60s) axiom-to-ELF verifier and an interactive web
visualizer mapping each English sentence ↔ HOL4 theorem ↔ ARM64 assembly block.

### Phase IV: Silicon & The Public Bounty Launch (Weeks 11–12)

**Milestone 8 (Weeks 11–12) — $25 FPGA Dongle + The 3-Act Viral Launch:**
Synthesize the exact same HOL4 theorem via CakeML's Silver backend onto an
open-source ECP5 FPGA USB stick (Yosys + nextpnr) with a 2-line OLED display and
physical approve button.

Launch Live With Three Undeniable Demos:

1. **The $10,000 Rooted Rogue Agent Bounty:** Public prompt-injection box connected to a rooted Linux agent + live $10,000 Stripe/USDC account guarded by the $25 FPGA on live webcam (including yanking the USB power cord mid-transfer).
2. **Autonomous Optimal Clearing:** 50 adversarial/hallucinating agents trading live, proving Forge rejects even a $0.01 suboptimal or unfair deal in 0.4ms via FarkasCert.
3. **60-Second Vibe-Coder Challenge:** Vibe-code a SaaS billing backend in Cursor in 60 seconds, clear & sign the 10-line English spec, fire 500 concurrent exploit requests at it live, and watch $0.00 leak.

## 5. Your Immediate Next 3 Actions Today

1. Rename `mack-dot/forge` → `mack-dot/forge-lab`.
2. Initialize the new `mack-dot/forge` with `MASTER_PLAN.md` and the 4 folders (`kernel/`, `spec-compiler/`, `relay/`, `sdk/`).
3. Start Milestone 1 exclusively: get a 60-line Pancake/CakeML ARM64 binary building in CI with the two M1-B machine premises fixed and `end_to_end=true` green on Commit #1. Do not write a single line of SDK or wrapper code until that green light is locked i `[LOST IN PASTE]`
