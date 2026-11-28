//! Forge High-Speed Differential & Chaos Crash Fuzzer (Zero External Dependencies).
//!
//! Modes:
//!   --mode diff  --duration <secs> : Persistent pipe differential fuzzing against live
//!                                    ARM64 `forge-kernel` vs. clean Rust reference model
//!                                    (verifies all 128 response bytes including HMAC-SHA256).
//!   --mode chaos --cycles <N>      : Fires real `kill -9` mid-transaction, restarts
//!                                    `forge-kernel` against the dual-slot state file
//!                                    (plus torn-slot injection), and asserts fund
//!                                    conservation, cap bounds, and zero double-spends.
//!   --mode both  --duration <secs> --cycles <N> : Runs both modes sequentially.

use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const REQ_BYTES: usize = 64;
const RESP_BYTES: usize = 128;
const SLOT_BYTES: usize = 256;
const DOMAIN: &[u8; 12] = b"FORGE-CAP-V1";
const SLOT_MAGIC: u64 = 0x464F524745534C33;

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

fn sha256(msg: &[u8]) -> [u8; 32] {
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];
    let mut data = msg.to_vec();
    data.push(0x80);
    while (data.len() % 64) != 56 { data.push(0); }
    data.extend_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
    for blk in data.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([blk[4 * i], blk[4 * i + 1], blk[4 * i + 2], blk[4 * i + 3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g; g = f; f = e; e = d.wrapping_add(t1);
            d = c; c = b; b = a; a = t1.wrapping_add(t2);
        }
        for (dst, add) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *dst = dst.wrapping_add(add);
        }
    }
    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut k64 = [0u8; 64];
    if key.len() > 64 {
        k64[..32].copy_from_slice(&sha256(key));
    } else {
        k64[..key.len()].copy_from_slice(key);
    }
    let mut ipad = Vec::with_capacity(64 + msg.len());
    let mut opad = Vec::with_capacity(96);
    for b in k64 { ipad.push(b ^ 0x36); opad.push(b ^ 0x5c); }
    ipad.extend_from_slice(msg);
    opad.extend_from_slice(&sha256(&ipad));
    sha256(&opad)
}

fn mint_cap_tag(key: &[u8], seq: u64, op: u64, dest: u64, amt: u64, bal: u64) -> [u64; 4] {
    let mut msg = Vec::with_capacity(52);
    msg.extend_from_slice(DOMAIN);
    for w in [seq, op, dest, amt, bal] { msg.extend_from_slice(&w.to_le_bytes()); }
    let digest = hmac_sha256(key, &msg);
    [
        u64::from_le_bytes(digest[0..8].try_into().unwrap()),
        u64::from_le_bytes(digest[8..16].try_into().unwrap()),
        u64::from_le_bytes(digest[16..24].try_into().unwrap()),
        u64::from_le_bytes(digest[24..32].try_into().unwrap()),
    ]
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn range(&mut self, bound: u64) -> u64 {
        if bound == 0 { 0 } else { self.next() % bound }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RefState {
    gen: u64,
    deposits: u64,
    balance: u64,
    spent: u64,
    refunds: u64,
    cap: u64,
    allowmask: u64,
    nonce: u64,
    last_tx: u64,
    last_amt: u64,
    tx_open: bool,
    tok_seq: u64,
    tok_op: u64,
    tok_dest: u64,
    tok_amt: u64,
    tok_bal: u64,
    tok_tag: [u64; 4],
}

impl Default for RefState {
    fn default() -> Self {
        Self {
            gen: 0, deposits: 0, balance: 0, spent: 0, refunds: 0,
            cap: 100_000, allowmask: 7, nonce: 0, last_tx: 0, last_amt: 0,
            tx_open: false, tok_seq: 0, tok_op: 0, tok_dest: 0, tok_amt: 0,
            tok_bal: 0, tok_tag: [0; 4],
        }
    }
}

fn dest_allowed(mask: u64, d: u64) -> bool {
    d < 64 && ((mask >> (d as u32)) & 1) != 0
}

fn encode_req(w: [u64; 8]) -> [u8; REQ_BYTES] {
    let mut out = [0u8; REQ_BYTES];
    for (i, lane) in w.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&lane.to_le_bytes());
    }
    out
}

fn encode_resp(w: [u64; 16]) -> [u8; RESP_BYTES] {
    let mut out = [0u8; RESP_BYTES];
    for (i, lane) in w.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&lane.to_le_bytes());
    }
    out
}

fn decode_resp(buf: &[u8; RESP_BYTES]) -> [u64; 16] {
    let mut w = [0u64; 16];
    for i in 0..16 {
        w[i] = u64::from_le_bytes(buf[8 * i..8 * i + 8].try_into().unwrap());
    }
    w
}

impl RefState {
    fn plain(&self, ok: u64, code: u64) -> [u64; 16] {
        [
            ok, code, self.deposits, self.balance, self.spent - self.refunds,
            self.refunds, self.nonce, self.last_tx,
            0, 0, 0, 0, 0, 0, 0, 0,
        ]
    }
    fn tok(&self, ok: u64, code: u64) -> [u64; 16] {
        [
            ok, code, self.deposits, self.balance, self.spent - self.refunds,
            self.refunds, self.nonce, self.last_tx,
            self.tok_seq, self.tok_op, self.tok_dest, self.tok_amt,
            self.tok_tag[0], self.tok_tag[1], self.tok_tag[2], self.tok_tag[3],
        ]
    }
    fn step(&mut self, key: &[u8; 32], req: [u64; 8]) -> ([u64; 16], bool) {
        let [op, _agent, arg2, amt, arg4, _, _, _] = req;
        if op == 1 {
            if self.gen != u64::MAX
                && amt <= u64::MAX - self.deposits
                && (self.spent - self.refunds) <= arg4
            {
                self.gen += 1;
                self.deposits += amt;
                self.balance += amt;
                self.cap = arg4;
                self.allowmask = arg2;
                self.tok_op = 0;
                (self.plain(1, 0), true)
            } else {
                (self.plain(0, 1), false)
            }
        } else if op == 2 {
            if self.tok_op == 2 && arg4 == self.nonce && arg2 == self.tok_dest && amt == self.tok_amt {
                (self.tok(1, 5), false)
            } else if self.gen != u64::MAX
                && amt != 0
                && dest_allowed(self.allowmask, arg2)
                && self.nonce != u64::MAX
                && arg4 == self.nonce + 1
                && self.last_tx != u64::MAX
                && amt <= self.balance
                && amt <= u64::MAX - self.spent
                && amt <= self.cap - (self.spent - self.refunds)
            {
                let gen_n = self.gen + 1;
                let bal_n = self.balance - amt;
                let tag = mint_cap_tag(key, gen_n, 2, arg2, amt, bal_n);
                self.gen = gen_n;
                self.balance = bal_n;
                self.spent += amt;
                self.nonce = arg4;
                self.last_tx += 1;
                self.last_amt = amt;
                self.tx_open = true;
                self.tok_seq = gen_n;
                self.tok_op = 2;
                self.tok_dest = arg2;
                self.tok_amt = amt;
                self.tok_bal = bal_n;
                self.tok_tag = tag;
                (self.tok(1, 0), true)
            } else {
                (self.plain(0, 2), false)
            }
        } else if op == 3 {
            if self.tok_op == 3 && !self.tx_open && arg4 == self.last_tx && amt == self.tok_amt {
                (self.tok(1, 5), false)
            } else if self.gen != u64::MAX
                && amt != 0
                && self.tx_open
                && arg4 == self.last_tx
                && amt <= self.last_amt
                && amt <= u64::MAX - self.refunds
                && amt <= u64::MAX - self.balance
            {
                let gen_n = self.gen + 1;
                let bal_n = self.balance + amt;
                let tag = mint_cap_tag(key, gen_n, 3, arg4, amt, bal_n);
                self.gen = gen_n;
                self.balance = bal_n;
                self.refunds += amt;
                self.tx_open = false;
                self.tok_seq = gen_n;
                self.tok_op = 3;
                self.tok_dest = arg4;
                self.tok_amt = amt;
                self.tok_bal = bal_n;
                self.tok_tag = tag;
                (self.tok(1, 0), true)
            } else {
                (self.plain(0, 3), false)
            }
        } else if op == 4 {
            (self.plain(1, 0), false)
        } else {
            (self.plain(0, 4), false)
        }
    }
}

fn spawn_airlock(kernel: &Path, state_dir: &Path, docker_image: &str) -> io::Result<(Child, ChildStdin, ChildStdout)> {
    let abs_kernel = fs::canonicalize(kernel)?;
    let abs_state = fs::canonicalize(state_dir)?;
    let mut cmd = if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
        let mut c = Command::new("sh");
        c.args(["-eu", "-c", r#"exec "$1" 3<>"$2/airlock.state" 4<"$2/boot.key""#, "--"])
            .arg(&abs_kernel)
            .arg(&abs_state);
        c
    } else {
        let kdir = abs_kernel.parent().unwrap();
        let kname = abs_kernel.file_name().unwrap().to_string_lossy();
        let mut c = Command::new("docker");
        c.args(["run", "--rm", "-i", "--platform", "linux/arm64", "-v"])
            .arg(format!("{}:/work:ro", kdir.display()))
            .arg("-v")
            .arg(format!("{}:/state", abs_state.display()))
            .arg(docker_image)
            .args([
                "sh", "-eu", "-c",
                &format!("exec /work/{kname} 3<>/state/airlock.state 4</state/boot.key"),
            ]);
        c
    };
    cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit());
    let mut child = cmd.spawn()?;
    let stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    Ok((child, stdin, stdout))
}

fn gen_fuzz_req(rng: &mut Rng, st: &RefState) -> [u64; 8] {
    let r = rng.range(100);
    if r < 30 {
        // Query (no fsync, very fast)
        [4, rng.next(), 0, 0, 0, 0, 0, 0]
    } else if r < 55 {
        // Adversarial spend denials (wrong nonce, bad dest, 0, u64::MAX, over-cap)
        let bad_kind = rng.range(5);
        match bad_kind {
            0 => [2, 1, 0, u64::MAX, st.nonce.wrapping_add(1), 0, 0, 0],
            1 => [2, 1, 63, 10, st.nonce.wrapping_add(1), 0, 0, 0],
            2 => [2, 1, 0, 0, st.nonce.wrapping_add(1), 0, 0, 0],
            3 => [2, 1, 0, 10, st.nonce, 0, 0, 0],
            _ => [2, 1, 0, st.cap.saturating_add(1), st.nonce.wrapping_add(1), 0, 0, 0],
        }
    } else if r < 70 {
        // Valid or boundary spend / idempotent retry
        if st.tok_op == 2 && rng.range(2) == 0 {
            [2, 7, st.tok_dest, st.tok_amt, st.nonce, 0, 0, 0]
        } else {
            let max_ok = st.balance.min(st.cap.saturating_sub(st.spent - st.refunds));
            let amt = if max_ok > 0 { 1 + rng.range(max_ok.min(500)) } else { 10 };
            [2, 7, rng.range(3), amt, st.nonce.wrapping_add(1), 0, 0, 0]
        }
    } else if r < 85 {
        // Refund (valid, retry, or double-refund attack)
        if st.tx_open && st.last_amt > 0 && rng.range(3) != 0 {
            let amt = 1 + rng.range(st.last_amt);
            [3, 7, 0, amt, st.last_tx, 0, 0, 0]
        } else if st.tok_op == 3 && !st.tx_open && rng.range(2) == 0 {
            [3, 7, 0, st.tok_amt, st.last_tx, 0, 0, 0]
        } else {
            [3, 7, 0, 1 + rng.range(100), st.last_tx, 0, 0, 0]
        }
    } else if r < 95 {
        // Admin deposit / cap update (valid or overflow attack)
        if rng.range(4) == 0 {
            [1, 0, 7, u64::MAX, st.cap, 0, 0, 0]
        } else {
            let dep = rng.range(2000);
            let new_cap = (st.spent - st.refunds) + 10_000 + rng.range(50_000);
            [1, 0, 0b111, dep, new_cap, 0, 0, 0]
        }
    } else {
        // Unknown opcode
        [5 + rng.range(20), rng.next(), rng.next(), rng.next(), rng.next(), 0, 0, 0]
    }
}

fn run_diff_mode(kernel: &Path, duration_secs: u64, seed: u64, docker_image: &str) -> io::Result<()> {
    let ts = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let tmp = env::temp_dir().join(format!("forge-fuzz-diff-{ts}"));
    fs::create_dir_all(&tmp)?;
    let key: [u8; 32] = [
        0x10,0x21,0x32,0x43,0x54,0x65,0x76,0x87,0x98,0xa9,0xba,0xcb,0xdc,0xed,0xfe,0x0f,
        0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x01,
    ];
    fs::write(tmp.join("boot.key"), key)?;
    fs::write(tmp.join("airlock.state"), [])?;

    let (mut child, mut stdin, mut stdout) = spawn_airlock(kernel, &tmp, docker_image)?;
    let mut rng = Rng(seed | 1);
    let mut model = RefState::default();

    // Seed initial budget so spends/refunds exercise live HMAC + disk commits immediately
    let init_req = [1, 0, 0b111, 100_000, 50_000, 0, 0, 0];
    let (want0, _) = model.step(&key, init_req);
    stdin.write_all(&encode_req(init_req))?;
    stdin.flush()?;
    let mut got0 = [0u8; RESP_BYTES];
    stdout.read_exact(&mut got0)?;
    assert_eq!(got0, encode_resp(want0), "initial deposit frame mismatch!");

    const BATCH: usize = 128;
    let mut tx_buf = vec![0u8; BATCH * REQ_BYTES];
    let mut rx_buf = vec![0u8; BATCH * RESP_BYTES];
    let mut expected = vec![[0u8; RESP_BYTES]; BATCH];

    let start = Instant::now();
    let deadline = Duration::from_secs(duration_secs);
    let mut total_frames: u64 = 1;
    let mut total_commits: u64 = 1;
    let mut total_tokens: u64 = 0;

    while start.elapsed() < deadline {
        for i in 0..BATCH {
            let req = gen_fuzz_req(&mut rng, &model);
            let (want, committed) = model.step(&key, req);
            if committed { total_commits += 1; }
            if want[9] != 0 { total_tokens += 1; }
            tx_buf[i * REQ_BYTES..(i + 1) * REQ_BYTES].copy_from_slice(&encode_req(req));
            expected[i] = encode_resp(want);
        }
        stdin.write_all(&tx_buf)?;
        stdin.flush()?;
        stdout.read_exact(&mut rx_buf)?;
        for i in 0..BATCH {
            let got = &rx_buf[i * RESP_BYTES..(i + 1) * RESP_BYTES];
            if got != expected[i] {
                let g = decode_resp(got.try_into().unwrap());
                let w = decode_resp(&expected[i]);
                panic!("DIFF MISMATCH at frame {}:\n  got : {:?}\n  want: {:?}", total_frames + i as u64, g, w);
            }
        }
        total_frames += BATCH as u64;
    }

    drop(stdin);
    let status = child.wait()?;
    let _ = fs::remove_dir_all(&tmp);
    assert!(status.success(), "kernel exited non-zero after diff fuzz: {status}");
    let elapsed = start.elapsed().as_secs_f64();
    let fps = (total_frames as f64) / elapsed.max(0.001);
    println!(
        "DIFF_FUZZ_PASS frames={total_frames} commits={total_commits} hmac_tokens={total_tokens} \
         elapsed={elapsed:.2}s rate={fps:.0} frames/sec mismatches=0"
    );
    Ok(())
}

fn check_state_file_valid(state_path: &Path, key: &[u8; 32]) -> (u64, u64, u64, u64, u64, u64) {
    let raw = fs::read(state_path).unwrap_or_default();
    let mut padded = [0u8; 512];
    let n = raw.len().min(512);
    padded[..n].copy_from_slice(&raw[..n]);
    let parse_slot = |slot: &[u8]| -> Option<(u64, u64, u64, u64, u64, u64)> {
        if slot.len() != SLOT_BYTES { return None; }
        let magic = u64::from_le_bytes(slot[0..8].try_into().unwrap());
        let gen = u64::from_le_bytes(slot[8..16].try_into().unwrap());
        if magic != SLOT_MAGIC || gen == 0 { return None; }
        let digest = hmac_sha256(key, &slot[0..224]);
        if digest != slot[224..256] { return None; }
        let deposits = u64::from_le_bytes(slot[16..24].try_into().unwrap());
        let balance = u64::from_le_bytes(slot[24..32].try_into().unwrap());
        let spent = u64::from_le_bytes(slot[32..40].try_into().unwrap());
        let refunds = u64::from_le_bytes(slot[40..48].try_into().unwrap());
        let cap = u64::from_le_bytes(slot[48..56].try_into().unwrap());
        let tok_seq = u64::from_le_bytes(slot[96..104].try_into().unwrap());
        let tok_op = u64::from_le_bytes(slot[104..112].try_into().unwrap());
        let tok_dest = u64::from_le_bytes(slot[112..120].try_into().unwrap());
        let tok_amt = u64::from_le_bytes(slot[120..128].try_into().unwrap());
        let tok_bal = u64::from_le_bytes(slot[128..136].try_into().unwrap());
        let mut tag = [0u64; 4];
        for i in 0..4 {
            tag[i] = u64::from_le_bytes(slot[136 + 8 * i..144 + 8 * i].try_into().unwrap());
        }
        if refunds > spent || balance > deposits || deposits != balance + (spent - refunds) || (spent - refunds) > cap {
            return None;
        }
        if tok_op != 0 && (balance != tok_bal || tag != mint_cap_tag(key, tok_seq, tok_op, tok_dest, tok_amt, tok_bal)) {
            return None;
        }
        Some((gen, deposits, balance, spent - refunds, refunds, cap))
    };
    let a = parse_slot(&padded[0..256]);
    let b = parse_slot(&padded[256..512]);
    match (a, b) {
        (Some(sa), Some(sb)) => if sa.0 < sb.0 { sb } else { sa },
        (Some(sa), None) => sa,
        (None, Some(sb)) => sb,
        (None, None) => (0, 0, 0, 0, 0, 100_000),
    }
}

fn run_chaos_mode(kernel: &Path, cycles: u64, seed: u64, docker_image: &str) -> io::Result<()> {
    let ts = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let tmp = env::temp_dir().join(format!("forge-fuzz-chaos-{ts}"));
    fs::create_dir_all(&tmp)?;
    let key: [u8; 32] = [0xA5; 32];
    fs::write(tmp.join("boot.key"), key)?;
    fs::write(tmp.join("airlock.state"), [])?;

    let abs_kernel = fs::canonicalize(kernel)?;
    let abs_state = fs::canonicalize(&tmp)?;
    let start = Instant::now();

    // Run real Linux `kill -9` chaos supervisor natively on Linux ARM64 or inside ONE
    // persistent `--platform linux/arm64` container on macOS Apple Silicon (100+ cycles in ~3s!).
    let py_supervisor = r#"
import fcntl, hashlib, hmac, os, random, signal, struct, subprocess, sys, time

kernel, state_dir, cycles_s, seed_s = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
cycles = int(cycles_s)
rng = random.Random(int(seed_s))
state_path = os.path.join(state_dir, "airlock.state")
key_path = os.path.join(state_dir, "boot.key")
key = open(key_path, "rb").read()
assert len(key) == 32

def enc_req(op, ag, a2, amt, a4):
    return struct.pack("<8Q", op, ag, a2, amt, a4, 0, 0, 0)

def dec_resp(b):
    assert len(b) == 128, f"short resp {len(b)}"
    return struct.unpack("<16Q", b)

def verify_tag(r):
    # r: ok,code,dep,bal,net,ref,nonce,ltx,tseq,top,tdest,tamt,t0,t1,t2,t3
    if r[9] == 0:
        return
    msg = b"FORGE-CAP-V1" + struct.pack("<5Q", r[8], r[9], r[10], r[11], r[3])
    want = hmac.new(key, msg, hashlib.sha256).digest()
    got = struct.pack("<4Q", r[12], r[13], r[14], r[15])
    assert got == want, "HMAC verification failed after crash!"

def spawn_proc():
    fd3 = os.open(state_path, os.O_RDWR | os.O_CREAT, 0o600)
    fd4 = os.open(key_path, os.O_RDONLY)
    def setup():
        t3 = fcntl.fcntl(fd3, fcntl.F_DUPFD, 10)
        t4 = fcntl.fcntl(fd4, fcntl.F_DUPFD, 10)
        os.dup2(t3, 3)
        os.dup2(t4, 4)
        os.set_inheritable(3, True)
        os.set_inheritable(4, True)
        os.close(t3)
        os.close(t4)
        if fd3 > 4: os.close(fd3)
        if fd4 > 4: os.close(fd4)
    p = subprocess.Popen(
        [kernel],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        preexec_fn=setup,
        close_fds=False,
    )
    os.close(fd3)
    os.close(fd4)
    return p

def read_exact(stream, n):
    out = bytearray()
    while len(out) < n:
        ch = stream.read(n - len(out))
        if not ch:
            return None
        out.extend(ch)
    return bytes(out)

# Seed initial deposit=1_000_000, cap=500_000, allowmask=7
p = spawn_proc()
p.stdin.write(enc_req(1, 0, 7, 1_000_000, 500_000))
p.stdin.flush()
r0 = dec_resp(read_exact(p.stdout, 128))
assert r0[0] == 1 and r0[2] == 1_000_000 and r0[3] == 1_000_000
p.stdin.close()
assert p.wait() == 0

last_nonce = 0
last_net = 0
last_dep = 1_000_000
cap = 500_000
kills = 0
torn_injects = 0
idempotent_retries = 0
completed_spends = 0

for cyc in range(cycles):
    # Launch kernel, fire a burst of spends, then send SIGKILL mid-flight!
    p = spawn_proc()
    amt = rng.randint(1, 50)
    dest = rng.randint(0, 2)
    req_next = enc_req(2, 7, dest, amt, last_nonce + 1)
    req_extra = enc_req(2, 7, dest, amt, last_nonce + 2) + enc_req(2, 7, dest, amt, last_nonce + 3)
    try:
        p.stdin.write(req_next + req_extra)
        p.stdin.flush()
    except BrokenPipeError:
        pass
    # Random micro-delay (0..1.5ms) so kill -9 hits before/during/after pwrite64/fdatasync
    if cyc % 3 != 0:
        time.sleep(rng.uniform(0.0001, 0.0015))
    os.kill(p.pid, signal.SIGKILL)
    p.wait()
    kills += 1

    # On 25% of cycles, corrupt the older/inactive disk slot to simulate torn power-loss write!
    if cyc % 4 == 0 and os.path.exists(state_path):
        raw = bytearray(open(state_path, "rb").read())
        if len(raw) >= 512:
            gen_a = struct.unpack_from("<Q", raw, 8)[0] if struct.unpack_from("<Q", raw, 0)[0] == 0x464F524745534C33 else 0
            gen_b = struct.unpack_from("<Q", raw, 264)[0] if struct.unpack_from("<Q", raw, 256)[0] == 0x464F524745534C33 else 0
            victim_off = 256 if gen_a >= gen_b else 0
            for j in range(16, 80):
                raw[victim_off + j] ^= 0xFF
            open(state_path, "wb").write(raw)
            torn_injects += 1

    # Reboot kernel, query state, verify conservation + cap + monotonicity, then retry req_next!
    p2 = spawn_proc()
    p2.stdin.write(enc_req(4, 7, 0, 0, 0))
    p2.stdin.flush()
    rq = dec_resp(read_exact(p2.stdout, 128))
    assert rq[0] == 1 and rq[2] == last_dep, f"deposit mismatch {rq}"
    assert rq[2] == rq[3] + rq[4], f"CONSERVATION VIOLATION: {rq}"
    assert rq[4] <= cap, f"CAP VIOLATION: {rq}"
    assert rq[6] >= last_nonce, f"NONCE ROLLBACK: {rq[6]} < {last_nonce}"
    recovered_nonce = rq[6]

    # Retry req_next: must NEVER double-spend!
    p2.stdin.write(req_next)
    p2.stdin.flush()
    rr = dec_resp(read_exact(p2.stdout, 128))
    verify_tag(rr)
    assert rr[2] == rr[3] + rr[4], f"CONSERVATION VIOLATION post-retry: {rr}"
    assert rr[4] <= cap, f"CAP VIOLATION post-retry: {rr}"

    if recovered_nonce == last_nonce:
        # Crashed before commit: retry succeeds fresh with code=0
        assert rr[0] == 1 and rr[1] == 0 and rr[6] == last_nonce + 1, f"expected fresh spend {rr}"
        completed_spends += 1
    elif recovered_nonce == last_nonce + 1:
        # Crashed after commit of req_next: retry MUST hit idempotent cache (code=5, zero double-spend)!
        assert rr[0] == 1 and rr[1] == 5 and rr[4] == rq[4], f"DOUBLE-SPEND OR MISSING RETRY CACHE: {rr} vs {rq}"
        idempotent_retries += 1
    else:
        # Multiple burst frames committed before SIGKILL: stale nonce MUST be denied!
        assert rr[0] == 0 and rr[1] == 2 and rr[4] == rq[4], f"STALE REPLAY NOT DENIED: {rr} vs {rq}"

    last_nonce = rr[6]
    last_net = rr[4]
    p2.stdin.close()
    assert p2.wait() == 0

print(f"CHAOS_INNER_OK kills={kills} torn_injects={torn_injects} fresh_retries={completed_spends} idempotent_cache_hits={idempotent_retries} final_nonce={last_nonce} final_net_spent={last_net}")
"#;

    let script_path = abs_state.join("chaos_sup.py");
    fs::write(&script_path, py_supervisor)?;

    let out = if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
        Command::new("python3")
            .arg(&script_path)
            .arg(&abs_kernel)
            .arg(&abs_state)
            .arg(cycles.to_string())
            .arg(seed.to_string())
            .output()?
    } else {
        let kdir = abs_kernel.parent().unwrap();
        let kname = abs_kernel.file_name().unwrap().to_string_lossy();
        Command::new("docker")
            .args(["run", "--rm", "--platform", "linux/arm64", "-v"])
            .arg(format!("{}:/work:ro", kdir.display()))
            .arg("-v")
            .arg(format!("{}:/state", abs_state.display()))
            .arg(docker_image)
            .args([
                "python3", "/state/chaos_sup.py",
                &format!("/work/{kname}"), "/state",
                &cycles.to_string(), &seed.to_string(),
            ])
            .output()?
    };

    if !out.status.success() {
        let _ = fs::remove_dir_all(&tmp);
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!(
                "chaos supervisor failed ({}):\nstdout: {}\nstderr: {}",
                out.status,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr),
            ),
        ));
    }

    // Independent Rust-side verification of final dual-slot disk image
    let (gen, dep, bal, net, _ref, cap) = check_state_file_valid(&tmp.join("airlock.state"), &key);
    assert!(gen > 0 && dep == bal + net && net <= cap, "final dual-slot invariant failed!");

    let _ = fs::remove_dir_all(&tmp);
    let elapsed = start.elapsed().as_secs_f64();
    let inner = String::from_utf8_lossy(&out.stdout).trim().to_string();
    println!(
        "CHAOS_FUZZ_PASS cycles={cycles} elapsed={elapsed:.2}s final_gen={gen} \
         conservation={dep}=={bal}+{net} ({inner})"
    );
    Ok(())
}

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    let mut mode = String::from("both");
    let mut kernel = PathBuf::from("kernels/airlock/build/forge-kernel");
    let mut duration: u64 = 15;
    let mut cycles: u64 = 100;
    let mut seed: u64 = 0x5EED_F046_E003;
    let mut docker_image = env::var("FORGE_ARM64_DOCKER_IMAGE")
        .unwrap_or_else(|_| "forge-arm64-tools:bookworm".to_string());

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--mode" if i + 1 < args.len() => { mode = args[i + 1].clone(); i += 2; }
            "--kernel" if i + 1 < args.len() => { kernel = PathBuf::from(&args[i + 1]); i += 2; }
            "--duration" if i + 1 < args.len() => { duration = args[i + 1].parse().expect("bad --duration"); i += 2; }
            "--cycles" if i + 1 < args.len() => { cycles = args[i + 1].parse().expect("bad --cycles"); i += 2; }
            "--seed" if i + 1 < args.len() => { seed = args[i + 1].parse().expect("bad --seed"); i += 2; }
            "--docker-image" if i + 1 < args.len() => { docker_image = args[i + 1].clone(); i += 2; }
            other => {
                eprintln!("Usage: forge-fuzz [--mode diff|chaos|both] [--kernel PATH] [--duration SECS] [--cycles N] [--seed U64]");
                return Err(io::Error::new(io::ErrorKind::InvalidInput, format!("unknown arg: {other}")));
            }
        }
    }

    match mode.as_str() {
        "diff" => run_diff_mode(&kernel, duration, seed, &docker_image)?,
        "chaos" => run_chaos_mode(&kernel, cycles, seed, &docker_image)?,
        "both" => {
            run_diff_mode(&kernel, duration, seed, &docker_image)?;
            run_chaos_mode(&kernel, cycles, seed, &docker_image)?;
        }
        _ => return Err(io::Error::new(io::ErrorKind::InvalidInput, format!("invalid --mode {mode}"))),
    }
    Ok(())
}
