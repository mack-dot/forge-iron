(*
  Forge Milestone 3: Pure HOL4 FIPS 180-4 SHA-256 & RFC 2104 HMAC-SHA256 Specification.

  SHA-256 pinned specification theory (zero axioms, zero cheats, zero EL/array bounds
  side-conditions for direct `ml_translatorLib.translate` synthesis).

  Validated inside the HOL4 kernel against 6 official NIST FIPS 180-4 and
  IETF RFC 4231 test vectors (empty, "abc", 2-block 448-bit message, HMAC TC1,
  HMAC TC2, and HMAC TC6 with 131-byte key > 64-byte block size).
*)
Theory forge_sha256Spec
Ancestors
  words arithmetic list rich_list
Libs
  preamble wordsLib

(* ---- 1. Big-endian 32-bit / 64-bit byte helpers ---- *)

Definition be32_of_bytes_def:
  be32_of_bytes (b0:word8) (b1:word8) (b2:word8) (b3:word8) : word32 =
    ((w2w b0 : word32) ≪ 24) ‖ ((w2w b1 : word32) ≪ 16) ‖
    ((w2w b2 : word32) ≪ 8) ‖ (w2w b3 : word32)
End

Definition be32_to_bytes_def:
  be32_to_bytes (w:word32) : word8 list =
    [w2w (w ⋙ 24); w2w (w ⋙ 16); w2w (w ⋙ 8); w2w w]
End

Definition be64_to_bytes_def:
  be64_to_bytes (w:word64) : word8 list =
    [w2w (w ⋙ 56); w2w (w ⋙ 48); w2w (w ⋙ 40); w2w (w ⋙ 32);
     w2w (w ⋙ 24); w2w (w ⋙ 16); w2w (w ⋙ 8); w2w w]
End

Definition bytes_to_be32s_def:
  (bytes_to_be32s (b0::b1::b2::b3::rest) =
     be32_of_bytes b0 b1 b2 b3 :: bytes_to_be32s rest) ∧
  (bytes_to_be32s _ = [])
End

(* ---- 2. FIPS 180-4 Constants & Round Functions ---- *)

Definition sha256_iv_def:
  sha256_iv : word32 # word32 # word32 # word32 # word32 # word32 # word32 # word32 =
    (0x6a09e667w, 0xbb67ae85w, 0x3c6ef372w, 0xa54ff53aw,
     0x510e527fw, 0x9b05688cw, 0x1f83d9abw, 0x5be0cd19w)
End

Definition sha256_k_def:
  sha256_k : word32 list = [
    0x428a2f98w; 0x71374491w; 0xb5c0fbcfw; 0xe9b5dba5w;
    0x3956c25bw; 0x59f111f1w; 0x923f82a4w; 0xab1c5ed5w;
    0xd807aa98w; 0x12835b01w; 0x243185bew; 0x550c7dc3w;
    0x72be5d74w; 0x80deb1few; 0x9bdc06a7w; 0xc19bf174w;
    0xe49b69c1w; 0xefbe4786w; 0x0fc19dc6w; 0x240ca1ccw;
    0x2de92c6fw; 0x4a7484aaw; 0x5cb0a9dcw; 0x76f988daw;
    0x983e5152w; 0xa831c66dw; 0xb00327c8w; 0xbf597fc7w;
    0xc6e00bf3w; 0xd5a79147w; 0x06ca6351w; 0x14292967w;
    0x27b70a85w; 0x2e1b2138w; 0x4d2c6dfcw; 0x53380d13w;
    0x650a7354w; 0x766a0abbw; 0x81c2c92ew; 0x92722c85w;
    0xa2bfe8a1w; 0xa81a664bw; 0xc24b8b70w; 0xc76c51a3w;
    0xd192e819w; 0xd6990624w; 0xf40e3585w; 0x106aa070w;
    0x19a4c116w; 0x1e376c08w; 0x2748774cw; 0x34b0bcb5w;
    0x391c0cb3w; 0x4ed8aa4aw; 0x5b9cca4fw; 0x682e6ff3w;
    0x748f82eew; 0x78a5636fw; 0x84c87814w; 0x8cc70208w;
    0x90befffaw; 0xa4506cebw; 0xbef9a3f7w; 0xc67178f2w
  ]
End

Definition sha256_ch_def:
  sha256_ch (x:word32) (y:word32) (z:word32) = (x && y) ⊕ (¬x && z)
End

Definition sha256_maj_def:
  sha256_maj (x:word32) (y:word32) (z:word32) = (x && y) ⊕ (x && z) ⊕ (y && z)
End

Definition sha256_bsig0_def:
  sha256_bsig0 (x:word32) = (x ⇄ 2) ⊕ (x ⇄ 13) ⊕ (x ⇄ 22)
End

Definition sha256_bsig1_def:
  sha256_bsig1 (x:word32) = (x ⇄ 6) ⊕ (x ⇄ 11) ⊕ (x ⇄ 25)
End

Definition sha256_ssig0_def:
  sha256_ssig0 (x:word32) = (x ⇄ 7) ⊕ (x ⇄ 18) ⊕ (x ⋙ 3)
End

Definition sha256_ssig1_def:
  sha256_ssig1 (x:word32) = (x ⇄ 17) ⊕ (x ⇄ 19) ⊕ (x ⋙ 10)
End

Definition sha256_round_def:
  sha256_round (k:word32) (w:word32)
    ((a,b,c,d,e,f,g,h):word32#word32#word32#word32#word32#word32#word32#word32) =
    let t1 = h + sha256_bsig1 e + sha256_ch e f g + k + w in
    let t2 = sha256_bsig0 a + sha256_maj a b c in
      (t1 + t2, a, b, c, d + t1, e, f, g)
End

(* Sliding 16-word message schedule + 64-round loop: zero indexing/EL side conditions *)
Definition sha256_rounds_def:
  (sha256_rounds [] st win = st) ∧
  (sha256_rounds (k::ks) st
     (w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15) =
     let st' = sha256_round k w0 st in
     let wn  = sha256_ssig1 w14 + w9 + sha256_ssig0 w1 + w0 in
       sha256_rounds ks st'
         (w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,wn))
End

Definition sha256_compress_def:
  sha256_compress
    ((h0,h1,h2,h3,h4,h5,h6,h7):word32#word32#word32#word32#word32#word32#word32#word32)
    win =
    let (a,b,c,d,e,f,g,h) = sha256_rounds sha256_k (h0,h1,h2,h3,h4,h5,h6,h7) win in
      (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e, h5 + f, h6 + g, h7 + h)
End

Definition sha256_word_blocks_def:
  (sha256_word_blocks st
     (w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest) =
     sha256_word_blocks
       (sha256_compress st (w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15))
       rest) ∧
  (sha256_word_blocks st _ = st)
End

Definition sha256_pad_def:
  sha256_pad (msg:word8 list) : word8 list =
    let n = LENGTH msg in
    let z = (119 − (n MOD 64)) MOD 64 in
      msg ++ [0x80w] ++ REPLICATE z 0w ++ be64_to_bytes (n2w (8 * n))
End

Definition sha256_finalize_def:
  sha256_finalize
    ((h0,h1,h2,h3,h4,h5,h6,h7):word32#word32#word32#word32#word32#word32#word32#word32) : word8 list =
    be32_to_bytes h0 ++ be32_to_bytes h1 ++ be32_to_bytes h2 ++ be32_to_bytes h3 ++
    be32_to_bytes h4 ++ be32_to_bytes h5 ++ be32_to_bytes h6 ++ be32_to_bytes h7
End

Definition sha256_def:
  sha256 (msg:word8 list) : word8 list =
    sha256_finalize (sha256_word_blocks sha256_iv (bytes_to_be32s (sha256_pad msg)))
End

(* ---- 3. RFC 2104 HMAC-SHA256 ---- *)

Definition hmac_xor_bytes_def:
  (hmac_xor_bytes (c:word8) [] = []) ∧
  (hmac_xor_bytes c (b::bs) = (b ⊕ c) :: hmac_xor_bytes c bs)
End

Definition hmac_sha256_def:
  hmac_sha256 (key:word8 list) (msg:word8 list) : word8 list =
    let k1  = if 64 < LENGTH key then sha256 key else key in
    let k64 = k1 ++ REPLICATE (64 − LENGTH k1) 0w in
    let ipad = hmac_xor_bytes 0x36w k64 in
    let opad = hmac_xor_bytes 0x5cw k64 in
      sha256 (opad ++ sha256 (ipad ++ msg))
End

(* ---- 4. Core Length Laws ---- *)

Theorem LENGTH_sha256_finalize:
  ∀st. LENGTH (sha256_finalize st) = 32
Proof
  PairCases \\ simp [sha256_finalize_def, be32_to_bytes_def]
QED

Theorem LENGTH_sha256:
  ∀msg. LENGTH (sha256 msg) = 32
Proof
  simp [sha256_def, LENGTH_sha256_finalize]
QED

Theorem LENGTH_hmac_sha256:
  ∀key msg. LENGTH (hmac_sha256 key msg) = 32
Proof
  simp [hmac_sha256_def, LENGTH_sha256]
QED

(* ---- 5. Official NIST FIPS 180-4 & RFC 4231 Test Vectors (Kernel-Checked) ---- *)

Theorem sha256_nist_empty:
  sha256 [] =
    [0xe3w; 0xb0w; 0xc4w; 0x42w; 0x98w; 0xfcw; 0x1cw; 0x14w;
     0x9aw; 0xfbw; 0xf4w; 0xc8w; 0x99w; 0x6fw; 0xb9w; 0x24w;
     0x27w; 0xaew; 0x41w; 0xe4w; 0x64w; 0x9bw; 0x93w; 0x4cw;
     0xa4w; 0x95w; 0x99w; 0x1bw; 0x78w; 0x52w; 0xb8w; 0x55w]
Proof
  EVAL_TAC
QED

Theorem sha256_nist_abc:
  sha256 [0x61w; 0x62w; 0x63w] =
    [0xbaw; 0x78w; 0x16w; 0xbfw; 0x8fw; 0x01w; 0xcfw; 0xeaw;
     0x41w; 0x41w; 0x40w; 0xdew; 0x5dw; 0xaew; 0x22w; 0x23w;
     0xb0w; 0x03w; 0x61w; 0xa3w; 0x96w; 0x17w; 0x7aw; 0x9cw;
     0xb4w; 0x10w; 0xffw; 0x61w; 0xf2w; 0x00w; 0x15w; 0xadw]
Proof
  EVAL_TAC
QED

Theorem sha256_nist_448bit:
  sha256 (MAP (n2w o ORD) "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
    [0x24w; 0x8dw; 0x6aw; 0x61w; 0xd2w; 0x06w; 0x38w; 0xb8w;
     0xe5w; 0xc0w; 0x26w; 0x93w; 0x0cw; 0x3ew; 0x60w; 0x39w;
     0xa3w; 0x3cw; 0xe4w; 0x59w; 0x64w; 0xffw; 0x21w; 0x67w;
     0xf6w; 0xecw; 0xedw; 0xd4w; 0x19w; 0xdbw; 0x06w; 0xc1w]
Proof
  EVAL_TAC
QED

Theorem hmac_sha256_rfc4231_tc1:
  hmac_sha256 (REPLICATE 20 0x0bw) (MAP (n2w o ORD) "Hi There") =
    [0xb0w; 0x34w; 0x4cw; 0x61w; 0xd8w; 0xdbw; 0x38w; 0x53w;
     0x5cw; 0xa8w; 0xafw; 0xcew; 0xafw; 0x0bw; 0xf1w; 0x2bw;
     0x88w; 0x1dw; 0xc2w; 0x00w; 0xc9w; 0x83w; 0x3dw; 0xa7w;
     0x26w; 0xe9w; 0x37w; 0x6cw; 0x2ew; 0x32w; 0xcfw; 0xf7w]
Proof
  EVAL_TAC
QED

Theorem hmac_sha256_rfc4231_tc2:
  hmac_sha256 (MAP (n2w o ORD) "Jefe") (MAP (n2w o ORD) "what do ya want for nothing?") =
    [0x5bw; 0xdcw; 0xc1w; 0x46w; 0xbfw; 0x60w; 0x75w; 0x4ew;
     0x6aw; 0x04w; 0x24w; 0x26w; 0x08w; 0x95w; 0x75w; 0xc7w;
     0x5aw; 0x00w; 0x3fw; 0x08w; 0x9dw; 0x27w; 0x39w; 0x83w;
     0x9dw; 0xecw; 0x58w; 0xb9w; 0x64w; 0xecw; 0x38w; 0x43w]
Proof
  EVAL_TAC
QED

Theorem hmac_sha256_rfc4231_tc6:
  hmac_sha256 (REPLICATE 131 0xaaw)
    (MAP (n2w o ORD) "Test Using Larger Than Block-Size Key - Hash Key First") =
    [0x60w; 0xe4w; 0x31w; 0x59w; 0x1ew; 0xe0w; 0xb6w; 0x7fw;
     0x0dw; 0x8aw; 0x26w; 0xaaw; 0xcbw; 0xf5w; 0xb7w; 0x7fw;
     0x8ew; 0x0bw; 0xc6w; 0x21w; 0x37w; 0x28w; 0xc5w; 0x14w;
     0x05w; 0x46w; 0x04w; 0x0fw; 0x0ew; 0xe3w; 0x7fw; 0x54w]
Proof
  EVAL_TAC
QED
