set_option maxRecDepth 200000

-- OPS: 25820

/-! AES-128 block encryption (FIPS 197) over a packed `Nat` state.

    The sixteen state bytes live in the low 128 bits of one natural number,
    byte `i` at bit `8 * i`, in the column-major order FIPS 197 gives the
    input. The S-box is a second packed number, 256 bytes wide, so a
    substitution is a shift and a mask rather than a list traversal.
    AddRoundKey is a single exclusive-or of two packed numbers. Each round
    unpacks the sixteen bytes once, runs SubBytes, ShiftRows and MixColumns on
    local bindings, and repacks once.

    Operation count, over 8-bit operations; ShiftRows and the packing are
    re-indexing and count as zero. A column of MixColumns is four `xtime`
    doublings and fifteen exclusive-ors, 19, so a full round is
    16 + 4 * 19 + 16 = 108 with its key addition. Nine full rounds, a final
    round without MixColumns at 16 + 16 = 32, and the initial key addition of
    16 give 9 * 108 + 32 + 16 = 1020 per block. Key expansion is forty words
    of four substitutions and four exclusive-ors, 320. The timing theorem
    chains twenty-five encryptions under one schedule:
    25 * 1020 + 320 = 25820. -/

def m8 : Nat := 255

/-- Byte `i` of a packed number. -/
def byteAt (x i : Nat) : Nat := (x >>> (8 * i)) &&& m8

/-- Pack a list of bytes, the head at bit 0. -/
def packBytes (bs : List Nat) : Nat :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b) 0

/-- The AES S-box of FIPS 197 §5.1.1, packed with entry `x` at bit `8 * x`. -/
def sboxPacked : Nat :=
  packBytes
    [ 0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76
    , 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0
    , 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15
    , 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75
    , 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84
    , 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf
    , 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8
    , 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2
    , 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73
    , 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb
    , 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79
    , 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08
    , 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a
    , 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e
    , 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf
    , 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 ]

/-- S-box substitution on one byte. -/
def sb (x : Nat) : Nat := byteAt sboxPacked x

/-- Multiplication by `x` in `GF(2^8)` modulo the AES polynomial. -/
def xt (a : Nat) : Nat :=
  if a < 128 then a <<< 1 else ((a <<< 1) ^^^ 0x1b) &&& m8

/-- The round constants of FIPS 197 §5.2, `rcon j` for `1 ≤ j ≤ 10`. -/
def rcon (j : Nat) : Nat :=
  byteAt (packBytes [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]) j

/-- A key-schedule word holds byte `j` of the word at bit `8 * j`. -/
def subWord (w : Nat) : Nat :=
  packBytes [sb (byteAt w 0), sb (byteAt w 1), sb (byteAt w 2), sb (byteAt w 3)]

def rotWord (w : Nat) : Nat :=
  packBytes [byteAt w 1, byteAt w 2, byteAt w 3, byteAt w 0]

/-- Element `i` of a list of words, counting from the head. -/
def wordAt (ws : List Nat) (i : Nat) : Nat := (ws.drop i).headD 0

/-- One key-expansion step. `ws` holds the words produced so far in reverse,
    so its head is `w[i-1]`. -/
def expandStep (i : Nat) (ws : List Nat) : List Nat :=
  let prev := wordAt ws 0
  let back := wordAt ws 3
  let temp := if i % 4 = 0 then subWord (rotWord prev) ^^^ rcon (i / 4) else prev
  (back ^^^ temp) :: ws

def expandN : Nat → Nat → List Nat → List Nat
  | 0, _, ws => ws
  | n + 1, i, ws => expandN n (i + 1) (expandStep i ws)

/-- The eleven round keys of an AES-128 schedule, each a packed 128-bit
    number, in round order. -/
def roundKeys (key : List Nat) : List Nat :=
  let w0 := packBytes (key.take 4)
  let w1 := packBytes ((key.drop 4).take 4)
  let w2 := packBytes ((key.drop 8).take 4)
  let w3 := packBytes ((key.drop 12).take 4)
  let ws := (expandN 40 4 [w3, w2, w1, w0]).reverse
  (List.range 11).map (fun j =>
    wordAt ws (4 * j)
      ||| (wordAt ws (4 * j + 1) <<< 32)
      ||| (wordAt ws (4 * j + 2) <<< 64)
      ||| (wordAt ws (4 * j + 3) <<< 96))

/-- MixColumns on one column, returning the four output bytes packed into a
    32-bit word. -/
def mixCol (a0 a1 a2 a3 : Nat) : Nat :=
  let r0 := xt a0 ^^^ xt a1 ^^^ a1 ^^^ a2 ^^^ a3
  let r1 := a0 ^^^ xt a1 ^^^ xt a2 ^^^ a2 ^^^ a3
  let r2 := a0 ^^^ a1 ^^^ xt a2 ^^^ xt a3 ^^^ a3
  let r3 := xt a0 ^^^ a0 ^^^ a1 ^^^ a2 ^^^ xt a3
  r0 ||| (r1 <<< 8) ||| (r2 <<< 16) ||| (r3 <<< 24)

/-- A full round: SubBytes, ShiftRows, MixColumns, AddRoundKey. -/
def aesRound (s rk : Nat) : Nat :=
  let t0 := sb (byteAt s 0); let t1 := sb (byteAt s 1)
  let t2 := sb (byteAt s 2); let t3 := sb (byteAt s 3)
  let t4 := sb (byteAt s 4); let t5 := sb (byteAt s 5)
  let t6 := sb (byteAt s 6); let t7 := sb (byteAt s 7)
  let t8 := sb (byteAt s 8); let t9 := sb (byteAt s 9)
  let t10 := sb (byteAt s 10); let t11 := sb (byteAt s 11)
  let t12 := sb (byteAt s 12); let t13 := sb (byteAt s 13)
  let t14 := sb (byteAt s 14); let t15 := sb (byteAt s 15)
  let c0 := mixCol t0 t5 t10 t15
  let c1 := mixCol t4 t9 t14 t3
  let c2 := mixCol t8 t13 t2 t7
  let c3 := mixCol t12 t1 t6 t11
  (c0 ||| (c1 <<< 32) ||| (c2 <<< 64) ||| (c3 <<< 96)) ^^^ rk

/-- The final round: SubBytes, ShiftRows, AddRoundKey. -/
def aesFinalRound (s rk : Nat) : Nat :=
  let t0 := sb (byteAt s 0); let t1 := sb (byteAt s 1)
  let t2 := sb (byteAt s 2); let t3 := sb (byteAt s 3)
  let t4 := sb (byteAt s 4); let t5 := sb (byteAt s 5)
  let t6 := sb (byteAt s 6); let t7 := sb (byteAt s 7)
  let t8 := sb (byteAt s 8); let t9 := sb (byteAt s 9)
  let t10 := sb (byteAt s 10); let t11 := sb (byteAt s 11)
  let t12 := sb (byteAt s 12); let t13 := sb (byteAt s 13)
  let t14 := sb (byteAt s 14); let t15 := sb (byteAt s 15)
  packBytes [t0, t5, t10, t15, t4, t9, t14, t3, t8, t13, t2, t7, t12, t1, t6, t11] ^^^ rk

def roundLoop : Nat → Nat → List Nat → Nat
  | 0, s, _ => s
  | n + 1, s, rks => roundLoop n (aesRound s (wordAt rks 0)) (rks.drop 1)

/-- AES-128 encryption of a packed plaintext block under a packed schedule. -/
def aesEncryptWith (rks : List Nat) (pt : Nat) : Nat :=
  let s := pt ^^^ wordAt rks 0
  let s := roundLoop 9 s (rks.drop 1)
  aesFinalRound s (wordAt rks 10)

def aesEncrypt (key : List Nat) (pt : Nat) : Nat :=
  aesEncryptWith (roundKeys key) pt

/-- The FIPS 197 Appendix C.1 key `000102030405060708090a0b0c0d0e0f`. -/
def fipsKey : List Nat :=
  [ 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07
  , 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f ]

/-- The FIPS 197 Appendix C.1 plaintext `00112233445566778899aabbccddeeff`. -/
def fipsPlain : Nat :=
  packBytes
    [ 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77
    , 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff ]

/-- The FIPS 197 Appendix C.1 ciphertext `69c4e0d86a7b0430d8cdb78070b4c55a`. -/
def fipsCipher : Nat :=
  packBytes
    [ 0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30
    , 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a ]

/-- FIPS 197 Appendix C.1, "AES-128 (Nk=4, Nr=10)". -/
theorem aes128_fips197_c1 : aesEncrypt fipsKey fipsPlain = fipsCipher := rfl

/-- Feed each ciphertext back in as the next plaintext under a fixed key. -/
def chainEnc (rks : List Nat) : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => chainEnc rks n (aesEncryptWith rks s)

/-- Twenty-five chained encryptions, the reduction the operation count above
    refers to. -/
theorem aes128_chain :
    decide (chainEnc (roundKeys fipsKey) 25 fipsPlain = 0) = false := rfl
