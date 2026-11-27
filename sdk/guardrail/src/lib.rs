//! Zero-dependency Rust SDK for the Forge `guardrail` 64-byte binary frame kernel.
//!
//! - Uses Rust `std` only (`0` external crates).
//! - Encodes and decodes exact 64-byte little-endian frames (`8 x u64`) matching
//!   `runtime/hol4/forge_frame64SpecScript.sml`.
//! - Enforces compile-time capability separation between [`GuardrailAdmin`] (lifecycle +
//!   `op=1` `BUDGET_SET`) and [`GuardrailAgent`] (restricted strictly to `op=2` `spend`,
//!   `op=3` `refund`, and `op=4` `query`).

use std::ffi::OsStr;
use std::fmt;
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitStatus, Stdio};
use std::sync::{Arc, Mutex};

/// Fixed binary frame length in bytes (`8 x u64` little-endian).
pub const FRAME_BYTES: usize = 64;

/// Opcode 1: Deposit funds, set rolling net cap, and set destination allowlist mask (admin-only).
pub const OP_BUDGET_SET: u64 = 1;
/// Opcode 2: Request spend against balance, net cap, allowlist, and strict monotonic nonce.
pub const OP_SPEND_REQUEST: u64 = 2;
/// Opcode 3: Request partial or full refund for the latest unrefunded spend transaction.
pub const OP_REFUND: u64 = 3;
/// Opcode 4: Read current guardrail accounting state without mutation.
pub const OP_QUERY: u64 = 4;

/// Error returned when decoding a binary frame with invalid byte length.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameError {
    InvalidLength { expected: usize, got: usize },
}

impl fmt::Display for FrameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            FrameError::InvalidLength { expected, got } => {
                write!(f, "expected {expected} bytes, got {got}")
            }
        }
    }
}

impl std::error::Error for FrameError {}

/// 64-byte binary request frame (`8 x u64` LE) matching `forge_frame64Spec`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RequestFrame {
    pub op: u64,
    pub agent_id: u64,
    pub arg2: u64,
    pub amount: u64,
    pub arg4: u64,
    pub reserved5: u64,
    pub reserved6: u64,
    pub reserved7: u64,
}

impl RequestFrame {
    /// Encodes all 8 lanes in little-endian order into a fixed 64-byte array.
    pub fn encode(&self) -> [u8; FRAME_BYTES] {
        let lanes = [
            self.op,
            self.agent_id,
            self.arg2,
            self.amount,
            self.arg4,
            self.reserved5,
            self.reserved6,
            self.reserved7,
        ];
        encode_lanes(lanes)
    }

    /// Decodes a fixed 64-byte array into a [`RequestFrame`].
    pub fn decode_array(buf: &[u8; FRAME_BYTES]) -> Self {
        let lanes = decode_lanes(buf);
        Self {
            op: lanes[0],
            agent_id: lanes[1],
            arg2: lanes[2],
            amount: lanes[3],
            arg4: lanes[4],
            reserved5: lanes[5],
            reserved6: lanes[6],
            reserved7: lanes[7],
        }
    }

    /// Decodes a byte slice into a [`RequestFrame`], rejecting lengths other than 64 bytes.
    pub fn decode(buf: &[u8]) -> Result<Self, FrameError> {
        let arr: &[u8; FRAME_BYTES] = buf.try_into().map_err(|_| FrameError::InvalidLength {
            expected: FRAME_BYTES,
            got: buf.len(),
        })?;
        Ok(Self::decode_array(arr))
    }
}

/// 64-byte binary response frame (`8 x u64` LE) matching `forge_guardrailSpec`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ResponseFrame {
    pub ok: u64,
    pub code: u64,
    pub deposits: u64,
    pub balance: u64,
    pub net_spent: u64,
    pub refunds: u64,
    pub last_nonce: u64,
    pub last_tx_id: u64,
}

impl ResponseFrame {
    /// Encodes all 8 lanes in little-endian order into a fixed 64-byte array.
    pub fn encode(&self) -> [u8; FRAME_BYTES] {
        let lanes = [
            self.ok,
            self.code,
            self.deposits,
            self.balance,
            self.net_spent,
            self.refunds,
            self.last_nonce,
            self.last_tx_id,
        ];
        encode_lanes(lanes)
    }

    /// Decodes a fixed 64-byte array into a [`ResponseFrame`].
    pub fn decode_array(buf: &[u8; FRAME_BYTES]) -> Self {
        let lanes = decode_lanes(buf);
        Self {
            ok: lanes[0],
            code: lanes[1],
            deposits: lanes[2],
            balance: lanes[3],
            net_spent: lanes[4],
            refunds: lanes[5],
            last_nonce: lanes[6],
            last_tx_id: lanes[7],
        }
    }

    /// Decodes a byte slice into a [`ResponseFrame`], rejecting lengths other than 64 bytes.
    pub fn decode(buf: &[u8]) -> Result<Self, FrameError> {
        let arr: &[u8; FRAME_BYTES] = buf.try_into().map_err(|_| FrameError::InvalidLength {
            expected: FRAME_BYTES,
            got: buf.len(),
        })?;
        Ok(Self::decode_array(arr))
    }

    /// Returns `true` when the kernel accepted the request (`ok == 1`).
    pub fn is_ok(&self) -> bool {
        self.ok == 1
    }

    /// Checks the conservation invariant `deposits == balance + net_spent` without overflow.
    pub fn is_conserved(&self) -> bool {
        self.balance.checked_add(self.net_spent) == Some(self.deposits)
    }
}

fn encode_lanes(lanes: [u64; 8]) -> [u8; FRAME_BYTES] {
    let mut out = [0u8; FRAME_BYTES];
    for (i, word) in lanes.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&word.to_le_bytes());
    }
    out
}

fn decode_lanes(buf: &[u8; FRAME_BYTES]) -> [u64; 8] {
    let mut lanes = [0u64; 8];
    for (i, slot) in lanes.iter_mut().enumerate() {
        let mut chunk = [0u8; 8];
        chunk.copy_from_slice(&buf[i * 8..(i + 1) * 8]);
        *slot = u64::from_le_bytes(chunk);
    }
    lanes
}

/// Builds a `BUDGET_SET` (`op=1`) request frame.
pub fn budget_set_req(deposit: u64, cap: u64, allowlist_mask: u64, agent_id: u64) -> RequestFrame {
    RequestFrame {
        op: OP_BUDGET_SET,
        agent_id,
        arg2: allowlist_mask,
        amount: deposit,
        arg4: cap,
        ..RequestFrame::default()
    }
}

/// Builds a `SPEND_REQUEST` (`op=2`) request frame.
pub fn spend_req(agent_id: u64, dest_id: u64, amount: u64, nonce: u64) -> RequestFrame {
    RequestFrame {
        op: OP_SPEND_REQUEST,
        agent_id,
        arg2: dest_id,
        amount,
        arg4: nonce,
        ..RequestFrame::default()
    }
}

/// Builds a `REFUND` (`op=3`) request frame.
pub fn refund_req(tx_id: u64, amount: u64, agent_id: u64) -> RequestFrame {
    RequestFrame {
        op: OP_REFUND,
        agent_id,
        arg2: 0,
        amount,
        arg4: tx_id,
        ..RequestFrame::default()
    }
}

/// Builds a `QUERY` (`op=4`) request frame.
pub fn query_req(agent_id: u64) -> RequestFrame {
    RequestFrame {
        op: OP_QUERY,
        agent_id,
        ..RequestFrame::default()
    }
}

fn write_exact_64<W: Write>(writer: &mut W, buf: &[u8; FRAME_BYTES]) -> io::Result<()> {
    let mut written = 0usize;
    while written < FRAME_BYTES {
        match writer.write(&buf[written..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "kernel stdin closed before 64-byte frame was written",
                ));
            }
            Ok(n) => written += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
    loop {
        match writer.flush() {
            Ok(()) => return Ok(()),
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
}

fn read_exact_64<R: Read>(reader: &mut R) -> io::Result<[u8; FRAME_BYTES]> {
    let mut buf = [0u8; FRAME_BYTES];
    let mut got = 0usize;
    while got < FRAME_BYTES {
        match reader.read(&mut buf[got..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    format!("kernel stdout hit EOF after {got} of {FRAME_BYTES} bytes"),
                ));
            }
            Ok(n) => got += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
    Ok(buf)
}

struct KernelPipe {
    child: Child,
    stdin: Option<ChildStdin>,
    stdout: ChildStdout,
    closed: bool,
}

impl KernelPipe {
    fn spawn_cmd(mut cmd: Command) -> io::Result<Self> {
        cmd.stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        let mut child = cmd.spawn()?;
        let stdin = child.stdin.take().ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "failed to attach kernel stdin pipe")
        })?;
        let stdout = child.stdout.take().ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "failed to attach kernel stdout pipe")
        })?;
        Ok(Self {
            child,
            stdin: Some(stdin),
            stdout,
            closed: false,
        })
    }

    fn send_frame(&mut self, req: &RequestFrame) -> io::Result<ResponseFrame> {
        if self.closed {
            return Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "guardrail kernel process is closed",
            ));
        }
        let encoded = req.encode();
        let stdin = self.stdin.as_mut().ok_or_else(|| {
            io::Error::new(io::ErrorKind::BrokenPipe, "kernel stdin already closed")
        })?;
        write_exact_64(stdin, &encoded)?;
        let raw_resp = read_exact_64(&mut self.stdout)?;
        Ok(ResponseFrame::decode_array(&raw_resp))
    }

    fn close(&mut self) -> io::Result<ExitStatus> {
        self.closed = true;
        drop(self.stdin.take());
        self.child.wait()
    }
}

impl Drop for KernelPipe {
    fn drop(&mut self) {
        if !self.closed {
            drop(self.stdin.take());
            let _ = self.child.wait();
            self.closed = true;
        }
    }
}

fn lock_pipe(pipe: &Arc<Mutex<KernelPipe>>) -> io::Result<std::sync::MutexGuard<'_, KernelPipe>> {
    pipe.lock()
        .map_err(|_| io::Error::new(io::ErrorKind::Other, "guardrail pipe mutex poisoned"))
}

/// Privileged guardrail administrator handle.
///
/// Owns the live `forge-kernel` child process lifecycle, exposes `deposit_and_configure`
/// (`op=1`), and mints restricted [`GuardrailAgent`] capabilities that structurally
/// cannot invoke `op=1` or shut down the kernel.
pub struct GuardrailAdmin {
    pipe: Arc<Mutex<KernelPipe>>,
}

impl GuardrailAdmin {
    /// Spawns a compiled ARM64 `forge-kernel` binary directly.
    pub fn spawn<P: AsRef<Path>>(binary: P) -> io::Result<Self> {
        let cmd = Command::new(binary.as_ref());
        Ok(Self {
            pipe: Arc::new(Mutex::new(KernelPipe::spawn_cmd(cmd)?)),
        })
    }

    /// Spawns a kernel via an explicit launcher command (for example `qemu-aarch64` or `docker`).
    pub fn spawn_command<S, I, A>(program: S, args: I) -> io::Result<Self>
    where
        S: AsRef<OsStr>,
        I: IntoIterator<Item = A>,
        A: AsRef<OsStr>,
    {
        let mut cmd = Command::new(program);
        cmd.args(args);
        Ok(Self {
            pipe: Arc::new(Mutex::new(KernelPipe::spawn_cmd(cmd)?)),
        })
    }

    /// Spawns the ARM64 binary inside an ARM64 Docker image with its parent directory mounted read-only.
    pub fn spawn_docker<P: AsRef<Path>>(docker_image: &str, binary: P) -> io::Result<Self> {
        let abs = std::fs::canonicalize(binary.as_ref())?;
        let parent = abs.parent().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "binary path has no parent directory")
        })?;
        let name = abs.file_name().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "binary path has no filename")
        })?;
        let mut mount = parent.as_os_str().to_os_string();
        mount.push(":/work:ro");
        let mut container_bin = std::ffi::OsString::from("/work/");
        container_bin.push(name);
        let mut cmd = Command::new("docker");
        cmd.args(["run", "--rm", "-i", "-v"])
            .arg(mount)
            .arg(docker_image)
            .arg(container_bin);
        Ok(Self {
            pipe: Arc::new(Mutex::new(KernelPipe::spawn_cmd(cmd)?)),
        })
    }

    /// Executes privileged `BUDGET_SET` (`op=1`): adds `deposit`, sets rolling `cap`, and sets `allowlist_mask`.
    pub fn deposit_and_configure(
        &self,
        deposit: u64,
        cap: u64,
        allowlist_mask: u64,
        agent_id: u64,
    ) -> io::Result<ResponseFrame> {
        let req = budget_set_req(deposit, cap, allowlist_mask, agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    /// Executes read-only `QUERY` (`op=4`) as admin.
    pub fn query(&self, agent_id: u64) -> io::Result<ResponseFrame> {
        let req = query_req(agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    /// Mints a restricted [`GuardrailAgent`] capability bound to `agent_id`.
    ///
    /// The returned handle shares the thread-safe serialized pipe and exposes ONLY
    /// `spend` (`op=2`), `refund` (`op=3`), and `query` (`op=4`).
    pub fn mint_agent(&self, agent_id: u64) -> GuardrailAgent {
        GuardrailAgent {
            pipe: Arc::clone(&self.pipe),
            agent_id,
        }
    }

    /// Closes stdin cleanly (signaling EOF) and waits for the kernel process to exit.
    pub fn close(self) -> io::Result<ExitStatus> {
        let mut guard = lock_pipe(&self.pipe)?;
        guard.close()
    }
}

/// Restricted capability handle for untrusted AI agents.
///
/// Structurally cannot invoke `op=1` (`BUDGET_SET`), send raw arbitrary frames, or
/// control the underlying `forge-kernel` process lifecycle. Thread-safe (`Send + Sync + Clone`).
#[derive(Clone)]
pub struct GuardrailAgent {
    pipe: Arc<Mutex<KernelPipe>>,
    agent_id: u64,
}

impl GuardrailAgent {
    /// Returns the `agent_id` bound to this capability handle.
    pub fn agent_id(&self) -> u64 {
        self.agent_id
    }

    /// Executes `SPEND_REQUEST` (`op=2`) under the bound `agent_id`.
    pub fn spend(&self, dest_id: u64, amount: u64, nonce: u64) -> io::Result<ResponseFrame> {
        let req = spend_req(self.agent_id, dest_id, amount, nonce);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    /// Executes `REFUND` (`op=3`) under the bound `agent_id`.
    pub fn refund(&self, tx_id: u64, amount: u64) -> io::Result<ResponseFrame> {
        let req = refund_req(tx_id, amount, self.agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }

    /// Executes read-only `QUERY` (`op=4`) under the bound `agent_id`.
    pub fn query(&self) -> io::Result<ResponseFrame> {
        let req = query_req(self.agent_id);
        let mut guard = lock_pipe(&self.pipe)?;
        guard.send_frame(&req)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use std::thread;

    fn bytes_to_hex(bytes: &[u8]) -> String {
        let mut out = String::with_capacity(bytes.len() * 2);
        for b in bytes {
            use std::fmt::Write as _;
            let _ = write!(&mut out, "{b:02x}");
        }
        out
    }

    #[test]
    fn golden_vectors_roundtrip_and_hex() {
        let vectors: [(&str, RequestFrame); 5] = [
            ("budget_set_basic", budget_set_req(50_000, 20_000, 0b1011, 7)),
            ("spend_normal", spend_req(42, 3, 12_500, 1)),
            ("spend_u64_max_attack", spend_req(1, 0, u64::MAX, 2)),
            ("refund_partial", refund_req(9, 4_000, 42)),
            ("query_zero", query_req(99)),
        ];
        for (name, req) in vectors {
            let raw = req.encode();
            assert_eq!(raw.len(), FRAME_BYTES);
            let dec = RequestFrame::decode(&raw).expect("valid 64B request decode");
            assert_eq!(dec, req, "round-trip mismatch on {name}");
            println!("RUST_VEC {name}={}", bytes_to_hex(&raw));
        }

        // Response frame round-trip including u64::MAX boundary
        let resp = ResponseFrame {
            ok: 1,
            code: 0,
            deposits: u64::MAX,
            balance: u64::MAX - 10,
            net_spent: 10,
            refunds: 0,
            last_nonce: 1,
            last_tx_id: 1,
        };
        assert!(resp.is_ok());
        assert!(resp.is_conserved());
        assert_eq!(ResponseFrame::decode(&resp.encode()).unwrap(), resp);

        // Reject invalid frame lengths
        assert_eq!(
            RequestFrame::decode(&[0u8; 63]),
            Err(FrameError::InvalidLength { expected: 64, got: 63 })
        );
        assert_eq!(
            ResponseFrame::decode(&[0u8; 65]),
            Err(FrameError::InvalidLength { expected: 64, got: 65 })
        );
    }

    #[test]
    fn partial_read_write_exact_64_with_eintr() {
        struct FlakyIo {
            data: Vec<u8>,
            pos: usize,
            step: usize,
        }

        impl Write for FlakyIo {
            fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
                self.step += 1;
                if self.step % 3 == 0 {
                    return Err(io::Error::new(io::ErrorKind::Interrupted, "simulated EINTR"));
                }
                let take = buf.len().min(3);
                self.data.extend_from_slice(&buf[..take]);
                Ok(take)
            }
            fn flush(&mut self) -> io::Result<()> {
                self.step += 1;
                if self.step % 5 == 0 {
                    return Err(io::Error::new(io::ErrorKind::Interrupted, "simulated flush EINTR"));
                }
                Ok(())
            }
        }

        impl Read for FlakyIo {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                self.step += 1;
                if self.step % 4 == 0 {
                    return Err(io::Error::new(io::ErrorKind::Interrupted, "simulated EINTR"));
                }
                let rem = self.data.len() - self.pos;
                if rem == 0 {
                    return Ok(0);
                }
                let take = rem.min(buf.len()).min(2);
                buf[..take].copy_from_slice(&self.data[self.pos..self.pos + take]);
                self.pos += take;
                Ok(take)
            }
        }

        let req = spend_req(42, 3, u64::MAX, 7);
        let raw = req.encode();
        let mut io_buf = FlakyIo {
            data: Vec::new(),
            pos: 0,
            step: 0,
        };
        write_exact_64(&mut io_buf, &raw).expect("flaky partial write succeeds");
        let got = read_exact_64(&mut io_buf).expect("flaky partial read succeeds");
        assert_eq!(got, raw);

        // Short EOF must return UnexpectedEof
        let mut short_io = FlakyIo {
            data: raw[..63].to_vec(),
            pos: 0,
            step: 0,
        };
        let err = read_exact_64(&mut short_io).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
    }

    fn spawn_live_guardrail_admin() -> Option<GuardrailAdmin> {
        let default_bin = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../kernels/guardrail/build/forge-kernel");
        let bin = std::env::var_os("FORGE_GUARDRAIL_BIN")
            .map(PathBuf::from)
            .unwrap_or(default_bin);
        if !bin.is_file() {
            return None;
        }
        if let Ok(qemu) = std::env::var("FORGE_GUARDRAIL_QEMU") {
            if !qemu.is_empty() {
                return Some(
                    GuardrailAdmin::spawn_command(&qemu, [&bin])
                        .expect("spawn guardrail via qemu"),
                );
            }
        }
        if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
            return Some(GuardrailAdmin::spawn(&bin).expect("spawn native ARM64 guardrail"));
        }
        let docker_img = std::env::var("FORGE_GUARDRAIL_DOCKER")
            .unwrap_or_else(|_| "forge-arm64-tools:bookworm".to_string());
        let docker_ok = Command::new("docker")
            .args(["images", "-q", &docker_img])
            .output()
            .map(|o| o.status.success() && !String::from_utf8_lossy(&o.stdout).trim().is_empty())
            .unwrap_or(false);
        if docker_ok {
            return Some(
                GuardrailAdmin::spawn_docker(&docker_img, &bin)
                    .expect("spawn guardrail via docker"),
            );
        }
        if std::env::var("FORGE_REQUIRE_LIVE_KERNEL").as_deref() == Ok("1") {
            panic!("FORGE_REQUIRE_LIVE_KERNEL=1 set, but no native aarch64/qemu/docker runner available");
        }
        None
    }

    #[test]
    fn live_guardrail_admin_and_agent_capability_separation() {
        // Static compile-time check: GuardrailAgent is Send + Sync + Clone
        fn assert_agent_traits<T: Send + Sync + Clone>() {}
        assert_agent_traits::<GuardrailAgent>();

        let Some(admin) = spawn_live_guardrail_admin() else {
            eprintln!("SKIP live_guardrail_admin_and_agent (no native ARM64 / docker / qemu runner)");
            return;
        };

        // 1. Initial query before deposit
        let r0 = admin.query(0).expect("initial query");
        assert_eq!(r0, ResponseFrame { ok: 1, code: 0, ..ResponseFrame::default() });
        assert!(r0.is_conserved());

        // 2. Admin-only op=1 configures deposit=5000, cap=3000, allowlist=0b101 (dest 0 and 2)
        let r1 = admin.deposit_and_configure(5000, 3000, 0b101, 0).expect("admin deposit");
        assert_eq!(
            r1,
            ResponseFrame {
                ok: 1,
                code: 0,
                deposits: 5000,
                balance: 5000,
                net_spent: 0,
                refunds: 0,
                last_nonce: 0,
                last_tx_id: 0,
            }
        );

        // 3. Mint restricted GuardrailAgent capability (cannot call op=1 or close)
        let agent = admin.mint_agent(7);
        assert_eq!(agent.agent_id(), 7);

        // Zero amount denied
        let r_zero = agent.spend(0, 0, 1).expect("spend zero");
        assert_eq!(r_zero.ok, 0);
        assert_eq!(r_zero.code, 2);

        // Non-allowlisted dest=1 denied
        let r_dest = agent.spend(1, 100, 1).expect("spend non-allowlisted");
        assert_eq!(r_dest.ok, 0);
        assert_eq!(r_dest.code, 2);

        // u64::MAX overflow attack denied
        let r_ovf = agent.spend(0, u64::MAX, 1).expect("spend overflow");
        assert_eq!(r_ovf.ok, 0);
        assert_eq!(r_ovf.code, 2);

        // Valid spend 1200 to dest 0 (nonce 1)
        let r_sp1 = agent.spend(0, 1200, 1).expect("spend 1200");
        assert_eq!(
            r_sp1,
            ResponseFrame {
                ok: 1,
                code: 0,
                deposits: 5000,
                balance: 3800,
                net_spent: 1200,
                refunds: 0,
                last_nonce: 1,
                last_tx_id: 1,
            }
        );
        assert!(r_sp1.is_conserved());

        // Replayed nonce 1 denied
        let r_rep = agent.spend(0, 100, 1).expect("replay nonce");
        assert_eq!(r_rep.ok, 0);
        assert_eq!(r_rep.code, 2);

        // Over-cap spend 1801 denied, exact cap 1800 accepted
        let r_over = agent.spend(2, 1801, 2).expect("over cap");
        assert_eq!(r_over.ok, 0);
        let r_exact = agent.spend(2, 1800, 2).expect("exact cap");
        assert_eq!(r_exact.ok, 1);
        assert_eq!(r_exact.net_spent, 3000);
        assert_eq!(r_exact.balance, 2000);

        // Partial refund 800 on tx 2 accepted, double refund denied
        let r_ref = agent.refund(2, 800).expect("refund 800");
        assert_eq!(
            r_ref,
            ResponseFrame {
                ok: 1,
                code: 0,
                deposits: 5000,
                balance: 2800,
                net_spent: 2200,
                refunds: 800,
                last_nonce: 2,
                last_tx_id: 2,
            }
        );
        let r_dbl = agent.refund(2, 100).expect("double refund");
        assert_eq!(r_dbl.ok, 0);
        assert_eq!(r_dbl.code, 3);

        // Multi-threaded concurrent queries through cloned GuardrailAgent handles
        let a1 = agent.clone();
        let a2 = agent.clone();
        let t1 = thread::spawn(move || a1.query().expect("t1 query"));
        let t2 = thread::spawn(move || a2.query().expect("t2 query"));
        let q1 = t1.join().unwrap();
        let q2 = t2.join().unwrap();
        assert_eq!(q1, r_ref);
        assert_eq!(q2, r_ref);

        // Admin shuts down process cleanly with exit 0
        let status = admin.close().expect("admin close");
        assert!(status.success(), "expected clean exit 0, got {status}");
    }
}
