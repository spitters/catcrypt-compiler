/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import Mathlib.Logic.Function.Basic

/-!
# SHA-256 Hash Function (FIPS 180-4)

Constructive implementation of SHA-256. All operations are on `UInt32`
(which wraps modulo 2^32 in Lean 4).

Internally uses `Vector` for the message schedule and state to enable
efficient `native_decide` evaluation (avoids `Function.update` closure chains).

All definitions are sealed with `@[irreducible]`.

## References

* FIPS 180-4, Section 6.2 — SHA-256
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.SHA256

/-! ## Constants -/

/-- SHA-256 round constants K (FIPS 180-4, Section 4.2.2). -/
def kData : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def kConst (t : Nat) : UInt32 := kData.toArray.getD t 0

/-- SHA-256 initial hash values H₀ (FIPS 180-4, Section 5.3.3). -/
def h0Vec : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

def hInit : Fin 8 → UInt32 := fun i => h0Vec[i]

/-! ## SHA-256 Operations (FIPS 180-4, Section 4.1.2) -/

/-- Right rotate for UInt32. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Ch(x,y,z) = (x AND y) XOR (NOT x AND z). -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

/-- Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z). -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ₀(x) = ROTR²(x) XOR ROTR¹³(x) XOR ROTR²²(x). -/
def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- Σ₁(x) = ROTR⁶(x) XOR ROTR¹¹(x) XOR ROTR²⁵(x). -/
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- σ₀(x) = ROTR⁷(x) XOR ROTR¹⁸(x) XOR SHR³(x). -/
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> (3 : UInt32))

/-- σ₁(x) = ROTR¹⁷(x) XOR ROTR¹⁹(x) XOR SHR¹⁰(x). -/
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> (10 : UInt32))

/-! ## Message Schedule (FIPS 180-4, Section 6.2.2, Step 1)

Uses `Vector` internally for O(1) indexing (avoids `Function.update` closure chains). -/

/-- Compute the SHA-256 message schedule W[0..63] from a 64-byte block.

    W[t] = M[t] for 0 ≤ t ≤ 15 (parsed as big-endian u32)
    W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16] for 16 ≤ t ≤ 63 -/
def messageSchedule (block : Fin 64 → UInt8) : Fin 64 → UInt32 :=
  let w0 : Vector UInt32 64 := Vector.ofFn fun (t : Fin 64) =>
    if h : t.val < 16 then
      let i := 4 * t.val
      let b0 := (block ⟨i, by omega⟩).toUInt32
      let b1 := (block ⟨i + 1, by omega⟩).toUInt32
      let b2 := (block ⟨i + 2, by omega⟩).toUInt32
      let b3 := (block ⟨i + 3, by omega⟩).toUInt32
      (b0 <<< (24 : UInt32)) ||| (b1 <<< (16 : UInt32)) |||
        (b2 <<< (8 : UInt32)) ||| b3
    else 0
  let w := Fin.foldl 48 (init := w0) fun (w : Vector UInt32 64) (j : Fin 48) =>
    have hj : j.val < 48 := j.isLt
    have h14 : j.val + 14 < 64 := by omega
    have h9 : j.val + 9 < 64 := by omega
    have h1 : j.val + 1 < 64 := by omega
    have h0 : j.val < 64 := by omega
    have h16 : j.val + 16 < 64 := by omega
    let wt := smallSigma1 (w.get ⟨j.val + 14, h14⟩) +
              (w.get ⟨j.val + 9, h9⟩) +
              smallSigma0 (w.get ⟨j.val + 1, h1⟩) +
              (w.get ⟨j.val, h0⟩)
    w.set (j.val + 16) wt h16
  fun t => w[t]

/-! ## Compression Function (FIPS 180-4, Section 6.2.2, Steps 2-4)

Uses `Vector UInt32 8` for the state to enable efficient evaluation. -/

/-- SHA-256 state: 8 words [a, b, c, d, e, f, g, h]. -/
abbrev State256 := Fin 8 → UInt32

/-- One round of SHA-256 compression using Vector state. -/
def compressRoundVec (state : Vector UInt32 8) (wt kt : UInt32) : Vector UInt32 8 :=
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  let t1 := h + bigSigma1 e + ch e f g + kt + wt
  let t2 := bigSigma0 a + maj a b c
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/-- One round of SHA-256 compression. -/
def compressRound (state : State256) (wt kt : UInt32) : State256 :=
  fun i => (compressRoundVec (Vector.ofFn state) wt kt)[i]

/-- SHA-256 compression function: compress one 64-byte block. -/
def compress (state : State256) (block : Fin 64 → UInt8) : State256 :=
  let w := messageSchedule block
  let s0 := Vector.ofFn state
  let final := Fin.foldl 64 (init := s0) fun (s : Vector UInt32 8) (t : Fin 64) =>
    compressRoundVec s (w t) (kConst t.val)
  fun i => state i + final[i]

/-! ## Padding and Hashing -/

/-- SHA-256 padding: append 1 bit, zeros, and 64-bit big-endian length.
    For messages ≤ 55 bytes, fits in one 64-byte block. -/
def padShort (msg : List UInt8) : Fin 64 → UInt8 :=
  let len := msg.length
  let bitLen := 8 * len
  fun i =>
    if i.val < len then msg.getD i.val 0
    else if i.val == len then 0x80
    else if i.val < 56 then 0x00
    else
      let byteIdx := i.val - 56
      ((bitLen >>> (8 * (7 - byteIdx))) % 256).toUInt8

/-- Serialize SHA-256 state (8 UInt32 words) to 32 bytes (big-endian). -/
def serializeState (state : State256) : Fin 32 → UInt8 := fun i =>
  let wordIdx := i.val / 4
  let byteIdx := i.val % 4
  let word := state ⟨wordIdx, by omega⟩
  let shift : UInt32 := (8 * (3 - byteIdx)).toUInt32
  ((word >>> shift).toNat % 256).toUInt8

/-- SHA-256 hash of a short message (≤ 55 bytes). -/
def sha256Short (msg : List UInt8) : Fin 32 → UInt8 :=
  serializeState (compress hInit (padShort msg))

/-- SHA-256 padding for multi-block: the final block.
    `totalBitLen` is the TOTAL message length in bits. -/
def padFinal (tail : List UInt8) (totalBitLen : Nat) : Fin 64 → UInt8 :=
  let len := tail.length
  fun i =>
    if i.val < len then tail.getD i.val 0
    else if i.val == len then 0x80
    else if i.val < 56 then 0x00
    else
      let byteIdx := i.val - 56
      ((totalBitLen >>> (8 * (7 - byteIdx))) % 256).toUInt8

/-- SHA-256 hash of a two-block message (57-119 bytes).
    The first block is `block1` (64 bytes), the rest (< 56 bytes) is padded. -/
def sha256TwoBlock (block1 : Fin 64 → UInt8) (tail : List UInt8)
    (totalLen : Nat) : Fin 32 → UInt8 :=
  let state1 := compress hInit block1
  let state2 := compress state1 (padFinal tail (8 * totalLen))
  serializeState state2

/-- SHA-256 hash of a single 64-byte block. -/
def sha256Block (block : Fin 64 → UInt8) : Fin 32 → UInt8 :=
  sha256Short (List.ofFn block)

/-- `sha256Block` unfolds to `sha256Short ∘ List.ofFn`.
    Exported before sealing so downstream files can prove `hashBlock_from_compress`. -/
theorem sha256Block_eq (block : Fin 64 → UInt8) :
    sha256Block block = sha256Short (List.ofFn block) := rfl

/-! ## Properties (proved before sealing so native_decide can evaluate) -/

/-- SHA-256 of "abc" ≠ SHA-256 of "abd".
    Proved before `@[irreducible]` sealing. Uses single-byte comparison
    to avoid needing `DecidableEq` on function types. -/
theorem sha256Short_nontrivial :
    sha256Short [0x61, 0x62, 0x63] ≠ sha256Short [0x61, 0x62, 0x64] := by
  intro h; exact absurd (congr_fun h ⟨0, by omega⟩) (by native_decide)

/-! ## Seal all definitions -/

attribute [irreducible] sha256Short sha256TwoBlock sha256Block serializeState
attribute [irreducible] compress compressRound compressRoundVec
attribute [irreducible] messageSchedule padShort padFinal
attribute [irreducible] ch maj bigSigma0 bigSigma1 smallSigma0 smallSigma1 rotr
attribute [irreducible] kConst hInit h0Vec kData

end CatCrypt.Crypto.Primitives.SHA256
