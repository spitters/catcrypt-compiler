/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# BLAKE2s Hash Function (RFC 7693)

Constructive implementation of BLAKE2s-256. All operations are on `UInt32`
(which wraps modulo 2^32 in Lean 4).

Internally uses `Vector` for the working state to enable efficient
`native_decide` evaluation (avoids `Function.update` closure chains).

All definitions are sealed with `@[irreducible]`.

## References

* RFC 7693 — The BLAKE2 Cryptographic Hash and Message Authentication Code (MAC)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.BLAKE2s

/-! ## Constants -/

/-- BLAKE2s initialization vector (IV): fractional parts of sqrt(2..9). -/
def ivVec : Vector UInt32 8 := #v[
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
  0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
]

def iv : Fin 8 → UInt32 := fun i => ivVec[i]

/-- BLAKE2s SIGMA permutation table (10 rounds × 16 entries). -/
def sigmaData : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]
]

def sigma (round : Fin 10) (idx : Fin 16) : Fin 16 := sigmaData[round][idx]

/-! ## Helper Operations -/

/-- Right rotate for UInt32. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Load a little-endian UInt32 from 4 bytes. -/
def loadLE32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< (8 : UInt32)) |||
  (b2.toUInt32 <<< (16 : UInt32)) ||| (b3.toUInt32 <<< (24 : UInt32))

/-! ## BLAKE2s Mixing Function G -/

/-- BLAKE2s mixing function G(v, a, b, c, d, x, y).
    Operates on working vector `v` at positions a, b, c, d with message words x, y. -/
def mixG (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let v := v.set a va
  let vd := rotr (v[d] ^^^ va) 16
  let v := v.set d vd
  let vc := v[c] + vd
  let v := v.set c vc
  let vb := rotr (v[b] ^^^ vc) 12
  let v := v.set b vb
  let va' := v[a] + vb + y
  let v := v.set a va'
  let vd' := rotr (v[d] ^^^ va') 8
  let v := v.set d vd'
  let vc' := v[c] + vd'
  let v := v.set c vc'
  let vb' := rotr (v[b] ^^^ vc') 7
  v.set b vb'

/-! ## BLAKE2s Round Function -/

/-- One round of BLAKE2s: 8 calls to G using the SIGMA permutation. -/
def blake2sRound (v : Vector UInt32 16) (m : Fin 16 → UInt32) (r : Fin 10) :
    Vector UInt32 16 :=
  let s := sigma r
  -- Column step
  let v := mixG v  0  4  8 12 (m (s  0)) (m (s  1))
  let v := mixG v  1  5  9 13 (m (s  2)) (m (s  3))
  let v := mixG v  2  6 10 14 (m (s  4)) (m (s  5))
  let v := mixG v  3  7 11 15 (m (s  6)) (m (s  7))
  -- Diagonal step
  let v := mixG v  0  5 10 15 (m (s  8)) (m (s  9))
  let v := mixG v  1  6 11 12 (m (s 10)) (m (s 11))
  let v := mixG v  2  7  8 13 (m (s 12)) (m (s 13))
  mixG v  3  4  9 14 (m (s 14)) (m (s 15))

/-! ## BLAKE2s Compression Function -/

/-- BLAKE2s state: 8 words. -/
abbrev State2s := Fin 8 → UInt32

/-- Parse a 64-byte block into 16 little-endian UInt32 words. -/
def parseBlock (block : Fin 64 → UInt8) : Fin 16 → UInt32 := fun i =>
  let off := 4 * i.val
  loadLE32 (block ⟨off, by omega⟩) (block ⟨off + 1, by omega⟩)
           (block ⟨off + 2, by omega⟩) (block ⟨off + 3, by omega⟩)

/-- BLAKE2s compression function F(h, m, t, f).
    - `h`: current state (8 words)
    - `m`: message block (16 words)
    - `t`: byte offset counter (UInt64, split into low/high UInt32)
    - `f`: finalization flag -/
def blake2sCompress (h : Fin 8 → UInt32) (m : Fin 16 → UInt32)
    (t : UInt64) (f : Bool) : Fin 8 → UInt32 :=
  let tLo : UInt32 := t.toUInt32
  let tHi : UInt32 := (t >>> (32 : UInt64)).toUInt32
  -- Initialize working vector v[0..15]
  let v0 : Vector UInt32 16 := Vector.ofFn fun (i : Fin 16) =>
    if h8 : i.val < 8 then h ⟨i.val, h8⟩
    else iv ⟨i.val - 8, by omega⟩
  -- XOR counter and finalization flag
  let v0 := v0.set 12 (v0[12] ^^^ tLo)
  let v0 := v0.set 13 (v0[13] ^^^ tHi)
  let v0 := if f then v0.set 14 (v0[14] ^^^ 0xFFFFFFFF) else v0
  -- 10 rounds of mixing
  let vFinal := Fin.foldl 10 (fun (v : Vector UInt32 16) (r : Fin 10) =>
    blake2sRound v m r) v0
  -- Finalize: h[i] ^= v[i] ^ v[i+8]
  fun (i : Fin 8) => h i ^^^ vFinal[i.val] ^^^ vFinal[i.val + 8]

/-! ## BLAKE2s Hashing -/

/-- Pad a partial block to 64 bytes (zero-padded). -/
def padBlock (data : List UInt8) : Fin 64 → UInt8 := fun i =>
  data.getD i.val 0

/-- Serialize state to bytes in little-endian order. -/
def serializeStateLE (state : Fin 8 → UInt32) : List UInt8 :=
  let words := List.ofFn state
  words.flatMap fun w =>
    [(w.toNat % 256).toUInt8,
     (w.toNat / 256 % 256).toUInt8,
     (w.toNat / 65536 % 256).toUInt8,
     (w.toNat / 16777216 % 256).toUInt8]

/-- Process non-final full blocks recursively. -/
def processBlocks (msg : List UInt8) (h : Fin 8 → UInt32)
    (blockIdx numBlocks : Nat) : Fin 8 → UInt32 :=
  if hz : numBlocks == 0 then h
  else
    let offset := 64 * blockIdx
    let block : Fin 64 → UInt8 := fun j => msg.getD (offset + j.val) 0
    let m := parseBlock block
    let bytesProcessed : UInt64 := (offset + 64).toUInt64
    let h' := blake2sCompress h m bytesProcessed false
    processBlocks msg h' (blockIdx + 1) (numBlocks - 1)
termination_by numBlocks
decreasing_by simp_all; omega

/-- BLAKE2s hash with no key and 32-byte output.
    Processes the input in 64-byte blocks. -/
def blake2s (msg : List UInt8) : List UInt8 :=
  -- Initialize state: h = IV, h[0] ^= 0x01010020 (fanout=1, depth=1, digestLen=32)
  let h : Fin 8 → UInt32 := fun i =>
    if i.val == 0 then iv i ^^^ 0x01010020 else iv i
  -- Process message in 64-byte blocks
  let len := msg.length
  if len == 0 then
    -- Empty message: compress one zero block as final
    let m := parseBlock (padBlock [])
    let h' := blake2sCompress h m 0 true
    serializeStateLE h'
  else
    let fullBlocks := (len - 1) / 64  -- number of non-final full blocks
    let h' := processBlocks msg h 0 fullBlocks
    -- Final block (possibly partial, zero-padded)
    let lastOffset := 64 * fullBlocks
    let lastData := msg.drop lastOffset
    let m := parseBlock (padBlock lastData)
    let h'' := blake2sCompress h' m len.toUInt64 true
    serializeStateLE h''

/-! ## Properties (proved before sealing so native_decide can evaluate) -/

/-- BLAKE2s of "abc" ≠ BLAKE2s of "abd". -/
theorem blake2s_nontrivial :
    blake2s [0x61, 0x62, 0x63] ≠ blake2s [0x61, 0x62, 0x64] := by
  native_decide

/-! ## Seal all definitions -/

attribute [irreducible] blake2s serializeStateLE
attribute [irreducible] blake2sCompress blake2sRound mixG
attribute [irreducible] parseBlock padBlock loadLE32 rotr
attribute [irreducible] sigma sigmaData iv ivVec

end CatCrypt.Crypto.Primitives.BLAKE2s
