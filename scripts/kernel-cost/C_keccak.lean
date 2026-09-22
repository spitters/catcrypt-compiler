set_option maxRecDepth 200000

-- OPS: 9100

/-! Keccak-f[1600] and SHA3-256 (FIPS 202) as a kernel-reduction cost sample.

    The 1600-bit state is one packed `Nat`: lane `i` occupies bits `64*i`, read
    by a shift and a mask, with lane `x + 5*y` holding `A[x, y]`. The 25 lanes
    are unpacked once per round; theta, rho, pi, chi and iota run on local
    bindings; the state is packed once at the end of the round. The 24 round
    constants are a single packed `Nat`.

    OPS: 9100

    Operation count, counting each `Nat` shift, mask, or, xor, and and
    subtraction the file performs. `rotl64` is five operations (the offset
    subtraction, two shifts, an or and a mask). Per round: 25 lane reads (50),
    the five column parities (20), the five theta terms (30), the 25 combined
    theta-rho-pi lanes, one of which is unrotated (145), chi on 25 lanes plus
    the iota lane read and xor (78), and the repack (48) — 371 each, 8904 over
    24 rounds. Building the constant table costs 48, the padded state 2, and
    the digest's four lane reads, four byte swaps and assembly 134. -/

def w64 : Nat := 18446744073709551615

def lane64 (s i : Nat) : Nat := (s >>> (64 * i)) &&& w64

def rotl64 (x n : Nat) : Nat := ((x <<< n) ||| (x >>> (64 - n))) &&& w64

/-- Pack a list of 64-bit lanes so that the head sits at bit 0. -/
def packLanes (ls : List Nat) : Nat :=
  ls.foldr (fun v acc => (acc <<< 64) ||| v) 0

/-- Reverse the eight bytes of a 64-bit value. -/
def bswap64 (x : Nat) : Nat :=
  ((x &&& 0xff) <<< 56) ||| (((x >>> 8) &&& 0xff) <<< 48)
    ||| (((x >>> 16) &&& 0xff) <<< 40) ||| (((x >>> 24) &&& 0xff) <<< 32)
    ||| (((x >>> 32) &&& 0xff) <<< 24) ||| (((x >>> 40) &&& 0xff) <<< 16)
    ||| (((x >>> 48) &&& 0xff) <<< 8) ||| ((x >>> 56) &&& 0xff)

/-- The 24 round constants, constant `t` at bit `64*t`. -/
def rcTable : Nat :=
  packLanes
    [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000
    , 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009
    , 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a
    , 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003
    , 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a
    , 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

/-- One round of Keccak-f[1600] with round index `t`. -/
def keccakRound (t s : Nat) : Nat :=
  let a0 := lane64 s 0; let a1 := lane64 s 1; let a2 := lane64 s 2
  let a3 := lane64 s 3; let a4 := lane64 s 4; let a5 := lane64 s 5
  let a6 := lane64 s 6; let a7 := lane64 s 7; let a8 := lane64 s 8
  let a9 := lane64 s 9; let a10 := lane64 s 10; let a11 := lane64 s 11
  let a12 := lane64 s 12; let a13 := lane64 s 13; let a14 := lane64 s 14
  let a15 := lane64 s 15; let a16 := lane64 s 16; let a17 := lane64 s 17
  let a18 := lane64 s 18; let a19 := lane64 s 19; let a20 := lane64 s 20
  let a21 := lane64 s 21; let a22 := lane64 s 22; let a23 := lane64 s 23
  let a24 := lane64 s 24
  let c0 := a0 ^^^ a5 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a1 ^^^ a6 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a2 ^^^ a7 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a3 ^^^ a8 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a4 ^^^ a9 ^^^ a14 ^^^ a19 ^^^ a24
  let d0 := c4 ^^^ rotl64 c1 1
  let d1 := c0 ^^^ rotl64 c2 1
  let d2 := c1 ^^^ rotl64 c3 1
  let d3 := c2 ^^^ rotl64 c4 1
  let d4 := c3 ^^^ rotl64 c0 1
  let b0 := a0 ^^^ d0
  let b1 := rotl64 (a6 ^^^ d1) 44
  let b2 := rotl64 (a12 ^^^ d2) 43
  let b3 := rotl64 (a18 ^^^ d3) 21
  let b4 := rotl64 (a24 ^^^ d4) 14
  let b5 := rotl64 (a3 ^^^ d3) 28
  let b6 := rotl64 (a9 ^^^ d4) 20
  let b7 := rotl64 (a10 ^^^ d0) 3
  let b8 := rotl64 (a16 ^^^ d1) 45
  let b9 := rotl64 (a22 ^^^ d2) 61
  let b10 := rotl64 (a1 ^^^ d1) 1
  let b11 := rotl64 (a7 ^^^ d2) 6
  let b12 := rotl64 (a13 ^^^ d3) 25
  let b13 := rotl64 (a19 ^^^ d4) 8
  let b14 := rotl64 (a20 ^^^ d0) 18
  let b15 := rotl64 (a4 ^^^ d4) 27
  let b16 := rotl64 (a5 ^^^ d0) 36
  let b17 := rotl64 (a11 ^^^ d1) 10
  let b18 := rotl64 (a17 ^^^ d2) 15
  let b19 := rotl64 (a23 ^^^ d3) 56
  let b20 := rotl64 (a2 ^^^ d2) 62
  let b21 := rotl64 (a8 ^^^ d3) 55
  let b22 := rotl64 (a14 ^^^ d4) 39
  let b23 := rotl64 (a15 ^^^ d0) 41
  let b24 := rotl64 (a21 ^^^ d1) 2
  let o0 := b0 ^^^ ((b1 ^^^ w64) &&& b2) ^^^ lane64 rcTable t
  let o1 := b1 ^^^ ((b2 ^^^ w64) &&& b3)
  let o2 := b2 ^^^ ((b3 ^^^ w64) &&& b4)
  let o3 := b3 ^^^ ((b4 ^^^ w64) &&& b0)
  let o4 := b4 ^^^ ((b0 ^^^ w64) &&& b1)
  let o5 := b5 ^^^ ((b6 ^^^ w64) &&& b7)
  let o6 := b6 ^^^ ((b7 ^^^ w64) &&& b8)
  let o7 := b7 ^^^ ((b8 ^^^ w64) &&& b9)
  let o8 := b8 ^^^ ((b9 ^^^ w64) &&& b5)
  let o9 := b9 ^^^ ((b5 ^^^ w64) &&& b6)
  let o10 := b10 ^^^ ((b11 ^^^ w64) &&& b12)
  let o11 := b11 ^^^ ((b12 ^^^ w64) &&& b13)
  let o12 := b12 ^^^ ((b13 ^^^ w64) &&& b14)
  let o13 := b13 ^^^ ((b14 ^^^ w64) &&& b10)
  let o14 := b14 ^^^ ((b10 ^^^ w64) &&& b11)
  let o15 := b15 ^^^ ((b16 ^^^ w64) &&& b17)
  let o16 := b16 ^^^ ((b17 ^^^ w64) &&& b18)
  let o17 := b17 ^^^ ((b18 ^^^ w64) &&& b19)
  let o18 := b18 ^^^ ((b19 ^^^ w64) &&& b15)
  let o19 := b19 ^^^ ((b15 ^^^ w64) &&& b16)
  let o20 := b20 ^^^ ((b21 ^^^ w64) &&& b22)
  let o21 := b21 ^^^ ((b22 ^^^ w64) &&& b23)
  let o22 := b22 ^^^ ((b23 ^^^ w64) &&& b24)
  let o23 := b23 ^^^ ((b24 ^^^ w64) &&& b20)
  let o24 := b24 ^^^ ((b20 ^^^ w64) &&& b21)
  o0 ||| (o1 <<< 64) ||| (o2 <<< 128) ||| (o3 <<< 192) ||| (o4 <<< 256)
    ||| (o5 <<< 320) ||| (o6 <<< 384) ||| (o7 <<< 448) ||| (o8 <<< 512)
    ||| (o9 <<< 576) ||| (o10 <<< 640) ||| (o11 <<< 704) ||| (o12 <<< 768)
    ||| (o13 <<< 832) ||| (o14 <<< 896) ||| (o15 <<< 960) ||| (o16 <<< 1024)
    ||| (o17 <<< 1088) ||| (o18 <<< 1152) ||| (o19 <<< 1216) ||| (o20 <<< 1280)
    ||| (o21 <<< 1344) ||| (o22 <<< 1408) ||| (o23 <<< 1472) ||| (o24 <<< 1536)

def keccakRounds : Nat → Nat → Nat → Nat
  | 0, _, s => s
  | n + 1, t, s => keccakRounds n (t + 1) (keccakRound t s)

/-- Keccak-f[1600]: the 24 rounds. -/
def keccakF (s : Nat) : Nat := keccakRounds 24 0 s

/-- The SHA3-256 absorbed state for the empty message: the domain-separated pad
    `0x06` in byte 0 and `0x80` in byte 135 of the 136-byte rate. -/
def sha3EmptyState : Nat := 0x06 ||| (0x8000000000000000 <<< (64 * 16))

/-- The 256-bit SHA3 digest of a squeezed state, as one big-endian natural: the
    first four lanes, each written out in little-endian byte order. -/
def sha3Digest (s : Nat) : Nat :=
  (bswap64 (lane64 s 0) <<< 192) ||| (bswap64 (lane64 s 1) <<< 128)
    ||| (bswap64 (lane64 s 2) <<< 64) ||| bswap64 (lane64 s 3)

/-- SHA3-256 of the empty message, the zero-length example of FIPS 202. -/
theorem sha3_256_empty :
    decide (sha3Digest (keccakF sha3EmptyState)
      = 0xa7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a) = true :=
  rfl
