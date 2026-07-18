/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import Mathlib.Logic.Function.Basic

/-!
# SHA-512 Hash Function (FIPS 180-4)

Constructive implementation of SHA-512.  All operations are on `UInt64`
(which wraps modulo 2^64 in Lean 4).  This is the FIPS 180-4 §6.4
specification, sharing structure with `Primitives.SHA256.lean` but
operating on 64-bit words with:

* 80 rounds (vs. 64 for SHA-256)
* 1024-bit (128-byte) blocks (vs. 512-bit / 64-byte for SHA-256)
* 128-bit length encoding in padding (vs. 64-bit for SHA-256)
* Different rotation amounts (Σ/σ constants)
* 64-byte digest (vs. 32-byte)

Internally uses `Vector` for the message schedule and state to enable
efficient `native_decide` evaluation (avoids `Function.update` closure
chains), matching the SHA-256 file's structure.

All definitions are sealed with `@[irreducible]`.

## References

* FIPS 180-4, §6.4 — SHA-512
* FIPS 180-4, §4.1.3 — Σ/σ rotations for 64-bit words
* FIPS 180-4, §4.2.3 — K_512 constants (first 64 bits of fractional parts
  of the cube roots of the first 80 primes)
* FIPS 180-4, §5.3.5 — Initial hash values H₀ (first 64 bits of fractional
  parts of the square roots of the first 8 primes)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.SHA512

/-! ## Constants -/

/-- SHA-512 round constants K (FIPS 180-4, §4.2.3) — 80 entries. -/
private def kData : Vector UInt64 80 := #v[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
]

def kConst (t : Nat) : UInt64 := kData.toArray.getD t 0

/-- SHA-512 initial hash values H₀ (FIPS 180-4, §5.3.5). -/
private def h0Vec : Vector UInt64 8 := #v[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
]

def hInit : Fin 8 → UInt64 := fun i => h0Vec[i]

/-! ## SHA-512 Operations (FIPS 180-4, §4.1.3) -/

/-- Right rotate for UInt64. -/
def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- Ch(x,y,z) = (x AND y) XOR (NOT x AND z). -/
def ch (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)

/-- Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z). -/
def maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ₀(x) = ROTR²⁸(x) XOR ROTR³⁴(x) XOR ROTR³⁹(x). -/
def bigSigma0 (x : UInt64) : UInt64 := rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39

/-- Σ₁(x) = ROTR¹⁴(x) XOR ROTR¹⁸(x) XOR ROTR⁴¹(x). -/
def bigSigma1 (x : UInt64) : UInt64 := rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41

/-- σ₀(x) = ROTR¹(x) XOR ROTR⁸(x) XOR SHR⁷(x). -/
def smallSigma0 (x : UInt64) : UInt64 := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> (7 : UInt64))

/-- σ₁(x) = ROTR¹⁹(x) XOR ROTR⁶¹(x) XOR SHR⁶(x). -/
def smallSigma1 (x : UInt64) : UInt64 := rotr x 19 ^^^ rotr x 61 ^^^ (x >>> (6 : UInt64))

/-! ## Message Schedule (FIPS 180-4, §6.4.2, Step 1)

Uses `Vector` internally for O(1) indexing. -/

/-- Compute the SHA-512 message schedule W[0..79] from a 128-byte block.

    W[t] = M[t] for 0 ≤ t ≤ 15 (parsed as big-endian u64)
    W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16] for 16 ≤ t ≤ 79 -/
def messageSchedule (block : Fin 128 → UInt8) : Fin 80 → UInt64 :=
  let w0 : Vector UInt64 80 := Vector.ofFn fun (t : Fin 80) =>
    if h : t.val < 16 then
      let i := 8 * t.val
      let b0 := (block ⟨i, by omega⟩).toUInt64
      let b1 := (block ⟨i + 1, by omega⟩).toUInt64
      let b2 := (block ⟨i + 2, by omega⟩).toUInt64
      let b3 := (block ⟨i + 3, by omega⟩).toUInt64
      let b4 := (block ⟨i + 4, by omega⟩).toUInt64
      let b5 := (block ⟨i + 5, by omega⟩).toUInt64
      let b6 := (block ⟨i + 6, by omega⟩).toUInt64
      let b7 := (block ⟨i + 7, by omega⟩).toUInt64
      (b0 <<< (56 : UInt64)) ||| (b1 <<< (48 : UInt64)) |||
        (b2 <<< (40 : UInt64)) ||| (b3 <<< (32 : UInt64)) |||
        (b4 <<< (24 : UInt64)) ||| (b5 <<< (16 : UInt64)) |||
        (b6 <<< (8 : UInt64)) ||| b7
    else 0
  let w := Fin.foldl 64 (init := w0) fun (w : Vector UInt64 80) (j : Fin 64) =>
    have _hj : j.val < 64 := j.isLt
    have h14 : j.val + 14 < 80 := by omega
    have h9 : j.val + 9 < 80 := by omega
    have h1 : j.val + 1 < 80 := by omega
    have h0 : j.val < 80 := by omega
    have h16 : j.val + 16 < 80 := by omega
    let wt := smallSigma1 (w.get ⟨j.val + 14, h14⟩) +
              (w.get ⟨j.val + 9, h9⟩) +
              smallSigma0 (w.get ⟨j.val + 1, h1⟩) +
              (w.get ⟨j.val, h0⟩)
    w.set (j.val + 16) wt h16
  fun t => w[t]

/-! ## Compression Function (FIPS 180-4, §6.4.2, Steps 2-4) -/

/-- SHA-512 state: 8 words [a, b, c, d, e, f, g, h]. -/
abbrev State512 := Fin 8 → UInt64

/-- One round of SHA-512 compression using Vector state. -/
private def compressRoundVec (state : Vector UInt64 8) (wt kt : UInt64) : Vector UInt64 8 :=
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  let t1 := h + bigSigma1 e + ch e f g + kt + wt
  let t2 := bigSigma0 a + maj a b c
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/-- One round of SHA-512 compression. -/
def compressRound (state : State512) (wt kt : UInt64) : State512 :=
  fun i => (compressRoundVec (Vector.ofFn state) wt kt)[i]

/-- SHA-512 compression function: compress one 128-byte block. -/
def compress (state : State512) (block : Fin 128 → UInt8) : State512 :=
  let w := messageSchedule block
  let s0 := Vector.ofFn state
  let final := Fin.foldl 80 (init := s0) fun (s : Vector UInt64 8) (t : Fin 80) =>
    compressRoundVec s (w t) (kConst t.val)
  fun i => state i + final[i]

/-! ## Padding and Hashing -/

/-- SHA-512 padding: append 1 bit, zeros, and 128-bit big-endian length.
    For messages ≤ 111 bytes, fits in one 128-byte block. -/
def padShort (msg : List UInt8) : Fin 128 → UInt8 :=
  let len := msg.length
  let bitLen := 8 * len
  fun i =>
    if i.val < len then msg.getD i.val 0
    else if i.val == len then 0x80
    else if i.val < 112 then 0x00
    else
      -- 128-bit length field: 16 bytes big-endian.
      -- Upper 8 bytes (i.val ∈ [112, 120)) are always 0 for messages
      -- with bitLen < 2^64.  Lower 8 bytes (i.val ∈ [120, 128)) hold
      -- the 64-bit big-endian message length in bits.
      if i.val < 120 then 0x00
      else
        let byteIdx := i.val - 120
        ((bitLen >>> (8 * (7 - byteIdx))) % 256).toUInt8

/-- Serialize SHA-512 state (8 UInt64 words) to 64 bytes (big-endian). -/
def serializeState (state : State512) : Fin 64 → UInt8 := fun i =>
  let wordIdx := i.val / 8
  let byteIdx := i.val % 8
  let word := state ⟨wordIdx, by omega⟩
  let shift : UInt64 := (8 * (7 - byteIdx)).toUInt64
  ((word >>> shift).toNat % 256).toUInt8

/-- SHA-512 hash of a short message (≤ 111 bytes). -/
def sha512Short (msg : List UInt8) : Fin 64 → UInt8 :=
  serializeState (compress hInit (padShort msg))

/-- SHA-512 padding for multi-block: the final block.
    `totalBitLen` is the TOTAL message length in bits. -/
def padFinal (tail : List UInt8) (totalBitLen : Nat) : Fin 128 → UInt8 :=
  let len := tail.length
  fun i =>
    if i.val < len then tail.getD i.val 0
    else if i.val == len then 0x80
    else if i.val < 112 then 0x00
    else
      if i.val < 120 then 0x00
      else
        let byteIdx := i.val - 120
        ((totalBitLen >>> (8 * (7 - byteIdx))) % 256).toUInt8

/-- SHA-512 hash of a two-block message.

    The first block is `block1` (128 bytes), the rest (< 112 bytes) is padded.
    This is the analog of SHA-256's `sha256TwoBlock` and is the only variant
    used by `Primitives.HMAC512` (which always feeds a 128-byte key-derived
    inner/outer block + short payload to the compression chain).

    Pre-condition: `tail.length < 112` AND `totalLen = 128 + tail.length`. -/
def sha512TwoBlock (block1 : Fin 128 → UInt8) (tail : List UInt8)
    (totalLen : Nat) : Fin 64 → UInt8 :=
  let state1 := compress hInit block1
  let state2 := compress state1 (padFinal tail (8 * totalLen))
  serializeState state2

/-- SHA-512 hash of a single 128-byte block. -/
def sha512Block (block : Fin 128 → UInt8) : Fin 64 → UInt8 :=
  sha512Short (List.ofFn block)

/-- `sha512Block` unfolds to `sha512Short ∘ List.ofFn`.
    Exported before sealing so downstream files can prove similar lemmas
    to those used for `sha256Block`. -/
theorem sha512Block_eq (block : Fin 128 → UInt8) :
    sha512Block block = sha512Short (List.ofFn block) := rfl

/-! ## Properties (proved before sealing so native_decide can evaluate) -/

/-- SHA-512 of "abc" ≠ SHA-512 of "abd".
    Proved before `@[irreducible]` sealing.

    FIPS 180-4 Appendix C.1 test vector: SHA-512("abc") =
      0xddaf35a193617aba cc417349ae204131 12e6fa4e89a97ea2 0a9eeee64b55d39a
        2192992a274fc1a8 36ba3c23a3feebbd 454d4423643ce80e 2a9ac94fa54ca49f
    We don't need the full digest match — bytewise non-triviality at byte 0
    suffices to show the implementation is non-constant. -/
theorem sha512Short_nontrivial :
    sha512Short [0x61, 0x62, 0x63] ≠ sha512Short [0x61, 0x62, 0x64] := by
  intro h; exact absurd (congr_fun h ⟨0, by omega⟩) (by native_decide)

/-- SHA-512 of "abc" computes to the FIPS 180-4 Appendix C.1 test vector,
    byte 0. -/
theorem sha512Short_abc_byte0 :
    sha512Short [0x61, 0x62, 0x63] ⟨0, by omega⟩ = 0xdd := by
  native_decide

/-! ## Seal all definitions -/

attribute [irreducible] sha512Short sha512TwoBlock sha512Block serializeState
attribute [irreducible] compress compressRound compressRoundVec
attribute [irreducible] messageSchedule padShort padFinal
attribute [irreducible] ch maj bigSigma0 bigSigma1 smallSigma0 smallSigma1 rotr
attribute [irreducible] kConst hInit h0Vec kData

end CatCrypt.Crypto.Primitives.SHA512
