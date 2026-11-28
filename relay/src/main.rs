//! Forge Ring 1: Stateless Keyless HMAC-SHA256 Capability Relay (Zero Dependencies).
//!
//! Holds external API secrets (`STRIPE_SECRET_KEY`) and the 32-byte kernel HMAC key
//! exclusively in its own OS process memory. The untrusted AI agent and application
//! never possess `STRIPE_SECRET_KEY`. Every inbound call MUST present a valid
//! kernel-minted HMAC-SHA256 capability token over `"FORGE-CAP-V1" || (seq,op,dest,amt,bal)`.
//! Verified calls are forwarded upstream with `Idempotency-Key: forge-<seq>`.

use std::env;
use std::fs;
use std::hint::black_box;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::Duration;

const IO_TIMEOUT: Duration = Duration::from_secs(5);
const MAX_REQ_BYTES: usize = 8192;

const DOMAIN: &[u8; 12] = b"FORGE-CAP-V1";
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
    while (data.len() % 64) != 56 {
        data.push(0);
    }
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

fn verify_cap_token(key: &[u8], seq: u64, op: u64, dest: u64, amt: u64, bal: u64, tag: &[u8; 32]) -> bool {
    if op != 2 && op != 3 { return false; }
    let mut msg = Vec::with_capacity(52);
    msg.extend_from_slice(DOMAIN);
    for w in [seq, op, dest, amt, bal] { msg.extend_from_slice(&w.to_le_bytes()); }
    let want = hmac_sha256(key, &msg);
    let mut diff = 0u8;
    for i in 0..32 {
        diff = black_box(diff | (want[i] ^ tag[i]));
    }
    black_box(diff) == 0
}

fn extract_token_header(raw: &[u8]) -> Option<String> {
    let hdr_end = raw.windows(4).position(|w| w == b"\r\n\r\n")?;
    let head = std::str::from_utf8(&raw[..hdr_end]).ok()?;
    let mut lines = head.split("\r\n");
    let _req_line = lines.next()?;
    let mut found: Option<String> = None;
    for line in lines {
        let (k, v) = line.split_once(':')?;
        if k.trim().eq_ignore_ascii_case("x-forge-token") {
            if found.is_some() {
                return None; // Reject duplicate X-Forge-Token headers (smuggling defense)
            }
            found = Some(v.trim().to_string());
        }
    }
    found
}

fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 { return None; }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(out)
}

fn reply(stream: &mut TcpStream, status: &str, body: &str) {
    let resp = format!(
        "HTTP/1.1 {status}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    let _ = stream.write_all(resp.as_bytes());
}

fn handle_client(mut client: TcpStream, hmac_key: &[u8; 32], api_secret: &str, upstream: &str) {
    let _ = client.set_read_timeout(Some(IO_TIMEOUT));
    let _ = client.set_write_timeout(Some(IO_TIMEOUT));
    let mut req_buf = Vec::with_capacity(1024);
    let mut chunk = [0u8; 1024];
    let mut found_end = false;
    while req_buf.len() < MAX_REQ_BYTES {
        match client.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => {
                req_buf.extend_from_slice(&chunk[..n]);
                if req_buf.windows(4).any(|w| w == b"\r\n\r\n") {
                    found_end = true;
                    break;
                }
            }
            Err(_) => return,
        }
    }
    if !found_end {
        return reply(&mut client, "400 Bad Request", r#"{"error":"incomplete_http_headers"}"#);
    }
    let Some(tok) = extract_token_header(&req_buf) else {
        return reply(&mut client, "403 Forbidden", r#"{"error":"missing_capability_token"}"#);
    };
    let parts: Vec<&str> = tok.split(':').collect();
    if parts.len() != 6 {
        return reply(&mut client, "403 Forbidden", r#"{"error":"malformed_capability_token"}"#);
    }
    let (Ok(seq), Ok(op), Ok(dest), Ok(amt), Ok(bal), Some(tag)) = (
        parts[0].parse::<u64>(), parts[1].parse::<u64>(), parts[2].parse::<u64>(),
        parts[3].parse::<u64>(), parts[4].parse::<u64>(), decode_hex32(parts[5]),
    ) else {
        return reply(&mut client, "403 Forbidden", r#"{"error":"invalid_token_fields"}"#);
    };
    if !verify_cap_token(hmac_key, seq, op, dest, amt, bal, &tag) {
        return reply(&mut client, "403 Forbidden", r#"{"error":"invalid_hmac_signature"}"#);
    }
    let path = if op == 2 { "/v1/charges" } else { "/v1/refunds" };
    let body = format!(r#"{{"seq":{seq},"op":{op},"dest":{dest},"amount":{amt},"balance":{bal}}}"#);
    let fwd = format!(
        "POST {path} HTTP/1.1\r\nHost: {upstream}\r\nAuthorization: Bearer {api_secret}\r\n\
         Idempotency-Key: forge-{seq}\r\nContent-Type: application/json\r\n\
         Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    match TcpStream::connect(upstream) {
        Ok(mut up) => {
            let _ = up.set_read_timeout(Some(IO_TIMEOUT));
            let _ = up.set_write_timeout(Some(IO_TIMEOUT));
            if up.write_all(fwd.as_bytes()).is_ok() {
                let mut up_resp = Vec::new();
                let _ = up.read_to_end(&mut up_resp);
                let _ = client.write_all(&up_resp);
            } else {
                reply(&mut client, "502 Bad Gateway", r#"{"error":"upstream_write_failed"}"#);
            }
        }
        Err(_) => reply(&mut client, "502 Bad Gateway", r#"{"error":"upstream_connect_failed"}"#),
    }
}

fn main() {
    let listen = env::var("RELAY_LISTEN").unwrap_or_else(|_| "127.0.0.1:18080".into());
    let upstream = env::var("UPSTREAM_ADDR").unwrap_or_else(|_| "127.0.0.1:18081".into());
    let api_secret = env::var("STRIPE_SECRET_KEY").expect("STRIPE_SECRET_KEY required");
    let key_bytes: [u8; 32] = if let Ok(path) = env::var("FORGE_HMAC_KEY_FILE") {
        let raw = fs::read(&path).expect("cannot read FORGE_HMAC_KEY_FILE");
        raw.try_into().expect("FORGE_HMAC_KEY_FILE must be exactly 32 bytes")
    } else {
        let hex = env::var("FORGE_HMAC_KEY_HEX").expect("FORGE_HMAC_KEY_FILE or FORGE_HMAC_KEY_HEX required");
        decode_hex32(&hex).expect("FORGE_HMAC_KEY_HEX must be 64 hex chars")
    };
    let listener = TcpListener::bind(&listen).expect("failed to bind RELAY_LISTEN");
    eprintln!("forge-relay listening on {listen} -> upstream {upstream}");
    for conn in listener.incoming().flatten() {
        handle_client(conn, &key_bytes, &api_secret, &upstream);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nist_and_rfc4231_vectors() {
        assert_eq!(
            sha256(b"abc"),
            [0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
             0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad]
        );
        assert_eq!(
            hmac_sha256(&[0x0b; 20], b"Hi There"),
            [0xb0,0x34,0x4c,0x61,0xd8,0xdb,0x38,0x53,0x5c,0xa8,0xaf,0xce,0xaf,0x0b,0xf1,0x2b,
             0x88,0x1d,0xc2,0x00,0xc9,0x83,0x3d,0xa7,0x26,0xe9,0x37,0x6c,0x2e,0x32,0xcf,0xf7]
        );
        let key = [0x42u8; 32];
        let mut msg = Vec::from(DOMAIN.as_slice());
        for w in [1u64, 2, 0, 500, 9500] { msg.extend_from_slice(&w.to_le_bytes()); }
        let tag = hmac_sha256(&key, &msg);
        assert!(verify_cap_token(&key, 1, 2, 0, 500, 9500, &tag));
        let mut bad = tag;
        bad[0] ^= 1;
        assert!(!verify_cap_token(&key, 1, 2, 0, 500, 9500, &bad));
        assert!(!verify_cap_token(&key, 1, 2, 0, 501, 9500, &tag));

        // Header boundary and smuggling defense
        let ok_req = b"POST /v1/execute HTTP/1.1\r\nHost: x\r\nX-Forge-Token: abc\r\n\r\nX-Forge-Token: forged";
        assert_eq!(extract_token_header(ok_req).as_deref(), Some("abc"));
        let no_delim = b"POST /v1/execute HTTP/1.1\r\nX-Forge-Token: abc\r\n";
        assert_eq!(extract_token_header(no_delim), None);
        let dup_hdr = b"POST /v1/execute HTTP/1.1\r\nX-Forge-Token: a\r\nX-Forge-Token: b\r\n\r\n";
        assert_eq!(extract_token_header(dup_hdr), None);
    }
}
