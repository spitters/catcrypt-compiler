set_option maxRecDepth 200000

-- OPS: 7800

/-! SHA-256 (FIPS 180-4) as a kernel-reduction cost sample.

    Aggregate state is a packed `Nat`: 32-bit word `i` occupies bits `32*i`,
    read by a shift and a mask. The eight-word hash state, the 64-word message
    schedule and the 64-word constant table are each one packed `Nat`. The
    working variables are unpacked once per compression round, the round runs on
    local bindings, and the state is packed once at the end of the round.

    OPS: 7800

    Operation count, counting each `Nat` shift, mask, or, xor, add and
    subtraction the file performs. `rotr32` is five operations (the offset
    subtraction, two shifts, an or and a mask). Message schedule: 48 words,
    each four lane reads (8), four rotations (20), two right shifts (2), four
    xors (4), three adds and a mask (4), and a multiply, shift and or to append
    (3) — 41 each, 1968. Compression: 64 rounds, each eight lane reads of the
    state (16), two lane reads of the schedule and the constant table (4), `S1`
    (17), `ch` (4), `T1` (5), `S0` (17), `maj` (5), `T2` (2), the two state
    updates (4) and the repack (14) — 88 each, 5632. Building the constant
    table and the initial state costs 144, the feed-forward 62, and the digest
    assembly 30. -/

def w32 : Nat := 4294967295

def lane (s i : Nat) : Nat := (s >>> (32 * i)) &&& w32

def rotr32 (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (32 - n))) &&& w32

/-- Pack a list of 32-bit words so that the head sits at bit 0. -/
def packWords (ws : List Nat) : Nat :=
  ws.foldr (fun v acc => (acc <<< 32) ||| v) 0

def pack8 (a b c d e f g h : Nat) : Nat :=
  a ||| (b <<< 32) ||| (c <<< 64) ||| (d <<< 96)
    ||| (e <<< 128) ||| (f <<< 160) ||| (g <<< 192) ||| (h <<< 224)

/-- The 64 round constants, word `t` at bit `32*t`. -/
def kConst : Nat :=
  packWords
    [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5
    , 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
    , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3
    , 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
    , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc
    , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
    , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7
    , 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
    , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
    , 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
    , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3
    , 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
    , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
    , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
    , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208
    , 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-- The initial hash value, word `i` at bit `32*i`. -/
def initH : Nat :=
  packWords
    [ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a
    , 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-- Extend the 16 packed message words to 64 packed schedule words. -/
def shaSchedule : Nat → Nat → Nat → Nat
  | 0, _, w => w
  | n + 1, t, w =>
    let a := lane w (t - 15)
    let b := lane w (t - 2)
    let s0 := (rotr32 a 7) ^^^ (rotr32 a 18) ^^^ (a >>> 3)
    let s1 := (rotr32 b 17) ^^^ (rotr32 b 19) ^^^ (b >>> 10)
    let nw := (lane w (t - 16) + s0 + lane w (t - 7) + s1) &&& w32
    shaSchedule n (t + 1) (w ||| (nw <<< (32 * t)))

/-- The compression rounds over a packed eight-word working state. -/
def shaRounds : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, s => s
  | n + 1, t, w, s =>
    let a := lane s 0; let b := lane s 1; let c := lane s 2; let d := lane s 3
    let e := lane s 4; let f := lane s 5; let g := lane s 6; let h := lane s 7
    let s1 := (rotr32 e 6) ^^^ (rotr32 e 11) ^^^ (rotr32 e 25)
    let ch := (e &&& f) ^^^ ((e ^^^ w32) &&& g)
    let t1 := (h + s1 + ch + lane kConst t + lane w t) &&& w32
    let s0 := (rotr32 a 2) ^^^ (rotr32 a 13) ^^^ (rotr32 a 22)
    let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := (s0 + mj) &&& w32
    shaRounds n (t + 1) w
      (pack8 ((t1 + t2) &&& w32) a b c ((d + t1) &&& w32) e f g)

/-- The compression function on a packed hash state and a packed 16-word block. -/
def sha256Block (hs m : Nat) : Nat :=
  let r := shaRounds 64 0 (shaSchedule 48 16 m) hs
  pack8
    ((lane hs 0 + lane r 0) &&& w32) ((lane hs 1 + lane r 1) &&& w32)
    ((lane hs 2 + lane r 2) &&& w32) ((lane hs 3 + lane r 3) &&& w32)
    ((lane hs 4 + lane r 4) &&& w32) ((lane hs 5 + lane r 5) &&& w32)
    ((lane hs 6 + lane r 6) &&& w32) ((lane hs 7 + lane r 7) &&& w32)

/-- The digest of a packed hash state as one big-endian 256-bit natural. -/
def digestBE (hs : Nat) : Nat :=
  (lane hs 0 <<< 224) ||| (lane hs 1 <<< 192) ||| (lane hs 2 <<< 160)
    ||| (lane hs 3 <<< 128) ||| (lane hs 4 <<< 96) ||| (lane hs 5 <<< 64)
    ||| (lane hs 6 <<< 32) ||| lane hs 7

/-- The padded one-block message "abc": `0x61626380` in word 0 and the bit
    length 24 in word 15. -/
def msgAbc : Nat := 0x61626380 ||| (24 <<< (32 * 15))

/-- SHA-256("abc"), the one-block example of FIPS 180-4 Appendix B.1. -/
theorem sha256_abc :
    decide (digestBE (sha256Block initH msgAbc)
      = 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad) = true :=
  rfl
