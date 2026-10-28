/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec
public import CatCrypt.Crypto.MLKEM.Compress
public import CatCrypt.Crypto.MLDSA.Spec.Rounding

/-!
# The rounding and codec templates against the ML-KEM and ML-DSA specifications

The ML-KEM word templates of `VIR.RoundCodec` are proved against `compressSpec` and
`decompressSpec` on `ℕ`, restated in that module. This module identifies those
restatements with the specifications the ML-KEM development uses,
`MLKEM.Compress.compress_d` and `MLKEM.Compress.decompress_d`, and restates each
word-level theorem against them. The ML-DSA templates are proved against the functions of
`RoundCodec.Fips204`, which are the functions of `MLDSA.Spec`: both names denote the
definitions of `VIR.RoundCodecDefs`. The ML-DSA word-level theorems are restated here at
the two parameter sets, with the bounds checks discharged.

## Main results

* `compress_d_val`: `(compress_d d x).val = compressSpec 3329 d x.val`, for every `d`.
* `decompress_d_val`: `(decompress_d d y).val = decompressSpec 3329 d y.val`, for `d ≤ 12`.
* `isGamma2_iff`: the ML-DSA parameter predicate `Spec.IsGamma2` holds exactly at the
  `γ₂` of the two template instances `mldsa88`, `mldsa32`.
* `mlkemCompress_word`, `mlkemDecompress_word`: at `d ∈ {1, 4, 5, 10, 11}`, the ML-KEM
  blocks map the word of a coefficient to the word of its `compress_d` and
  `decompress_d`.
* `mldsaPower2Round_word`, `mldsaDecompose_word`, `mldsaMakeHint_word`,
  `mldsaUseHint_word`: the ML-DSA blocks compute `Spec.power2Round`,
  `(Spec.highBits, Spec.lowBits)`, `Spec.makeHint` (for `|z| ≤ γ₂`) and `Spec.useHint`
  at both parameter sets.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RoundCodecSpec

open CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.MLKEM.Compress (compress_d decompress_d)

namespace Spec
export CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec.Fips204 (q power2Round decompose
  highBits lowBits makeHint useHint)
export CatCrypt.Crypto.MLDSA.Spec (IsGamma2)
end Spec

/-! ## ML-KEM: `Compress_d` and `Decompress_d` -/

/-- The ML-KEM `Compress_d` is `compressSpec` at `q = 3329` on canonical representatives. -/
theorem compress_d_val (d : ℕ) (x : ZMod 3329) :
    (compress_d d x).val = compressSpec 3329 d x.val := by
  rw [compress_d, ZMod.val_natCast]
  rfl

/-- The ML-KEM `Decompress_d` is `decompressSpec` at `q = 3329` on canonical
    representatives, for `d ≤ 12`. -/
theorem decompress_d_val (d : ℕ) (hd : d ≤ 12) (y : ZMod (2 ^ d)) :
    (decompress_d d y).val = decompressSpec 3329 d y.val := by
  rw [decompress_d, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hy : y.val < 2 ^ d := ZMod.val_lt y
  have hN : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  rw [Nat.div_lt_iff_lt_mul hpos]
  show 3329 * y.val + 2 ^ d / 2 < 3329 * 2 ^ d
  omega

/-- On a word `v` holding the canonical representative of `x : ZMod 3329`, the ML-KEM
    compression template at `d ∈ {1, 4, 5, 10, 11}` returns the representative of
    `compress_d d x`. -/
theorem mlkemCompress_word (d : ℕ) (hd : d ∈ [1, 4, 5, 10, 11]) (x : ZMod 3329)
    (v : BitVec (mlkemCompressMagic d).w) (hv : v.toNat = x.val) :
    zvals false ((compressProg d (mlkemCompressMagic d)).denote (.cons v .nil))
      = .cons ((compress_d d x).val : ℤ) .nil := by
  have hb : boundsOkMR false (iv1 (0, ((3329 : ℕ) : ℤ) - 1)) (compressProg d (mlkemCompressMagic d))
      (iv1 (0, 2 ^ d - 1)) = true := mlkemCompressBlock_ok d hd
  rw [compress_d_val, ← hv]
  exact compress_denote 3329 d _ (mlkemCompress_ok d hd) hb v (hv ▸ ZMod.val_lt x)

/-- On a word `v` holding the representative of `y : ZMod (2^d)`, the ML-KEM decompression
    template at `d ∈ {1, 4, 5, 10, 11}` returns the canonical representative of
    `decompress_d d y`. -/
theorem mlkemDecompress_word (d : ℕ) (hd : d ∈ [1, 4, 5, 10, 11]) (y : ZMod (2 ^ d))
    (v : BitVec 32) (hv : v.toNat = y.val) :
    zvals false ((decompressProg 32 3329 d).denote (.cons v .nil))
      = .cons ((decompress_d d y).val : ℤ) .nil := by
  have hd12 : d ≤ 12 := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd; omega
  have hd32 : 2 ^ d / 2 < 2 ^ 32 := by
    have : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd12
    omega
  have hb : boundsOkMR false (iv1 (0, 2 ^ d - 1)) (decompressProg 32 3329 d)
      (iv1 (0, ((3329 : ℕ) : ℤ) - 1)) = true := mlkemDecompressBlock_ok d hd
  rw [decompress_d_val d hd12, ← hv]
  exact decompress_denote 32 3329 d (by norm_num) hd32 hb v (hv ▸ ZMod.val_lt y)

/-! ## ML-DSA: the FIPS 204 rounding functions -/

/-- `Spec.IsGamma2 γ₂` holds exactly when `γ₂` is the parameter of one of the two template
    instances `mldsa88`, `mldsa32`. -/
theorem isGamma2_iff (γ2 : ℤ) : Spec.IsGamma2 γ2 ↔ ∃ P, MldsaInst P γ2 := by
  constructor
  · rintro (h | h)
    · exact ⟨mldsa88, .inl ⟨rfl, h⟩⟩
    · exact ⟨mldsa32, .inr ⟨rfl, h⟩⟩
  · rintro ⟨P, ⟨_, h⟩ | ⟨_, h⟩⟩
    · exact .inl h
    · exact .inr h

/-- The ML-DSA `Power2Round` block computes `Spec.power2Round` on the signed reading of a
    32-bit word in `[0, q)`. -/
theorem mldsaPower2Round_word (x : BitVec 32) (h0 : 0 ≤ rd true x) (h1 : rd true x < Spec.q) :
    zvals true ((power2RoundProg 32 13).denote (.cons x .nil))
      = .cons (Spec.power2Round (rd true x)).1 (.cons (Spec.power2Round (rd true x)).2 .nil) :=
  power2Round_denote _ mldsaPower2RoundBlock_ok x h0 h1

/-- Bounds check of the `Decompose` block at an ML-DSA instance. -/
theorem mldsaDecompose_boundsOk {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2) :
    boundsOkMR true (iv1 (0, Fips204.q - 1)) (decomposeProg P) (iv2 mldsaOut mldsaOut)
      = true := by
  rcases hP with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact mldsaDecomposeBlock_ok.1
  · exact mldsaDecomposeBlock_ok.2

/-- The ML-DSA `Decompose` block computes `(Spec.highBits, Spec.lowBits)` on the signed
    reading of a word in `[0, q)`, at both parameter sets. -/
theorem mldsaDecompose_word {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (x : BitVec P.w) (h0 : 0 ≤ rd true x) (h1 : rd true x < Spec.q) :
    zvals true ((decomposeProg P).denote (.cons x .nil))
      = .cons (Spec.highBits γ2 (rd true x)) (.cons (Spec.lowBits γ2 (rd true x)) .nil) :=
  decompose_denote hP _ (mldsaDecompose_boundsOk hP) x h0 h1

/-- Bounds check of the `MakeHint` block at an ML-DSA instance, with `z ∈ [-γ₂, γ₂]`. -/
theorem mldsaMakeHint_boundsOk {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2) :
    boundsOkMR true (iv2 (0, Fips204.q - 1) (-γ2, γ2)) (makeHintProg P) (iv1 mldsaOut)
      = true := by
  rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact mldsaMakeHintBlock_mldsa88_ok
  · exact mldsaMakeHintBlock_mldsa32_ok

/-- The ML-DSA `MakeHint` block computes `Spec.makeHint` as a bit, for `r ∈ [0, q)` and
    `|z| ≤ γ₂`, at both parameter sets. -/
theorem mldsaMakeHint_word {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (r z : BitVec P.w) (h0 : 0 ≤ rd true r) (h1 : rd true r < Spec.q)
    (hz0 : -γ2 ≤ rd true z) (hz1 : rd true z ≤ γ2) :
    zvals true ((makeHintProg P).denote (.cons r (.cons z .nil)))
      = .cons (if Spec.makeHint γ2 (rd true z) (rd true r) then 1 else 0) .nil :=
  makeHint_denote hP _ (mldsaMakeHint_boundsOk hP) r z h0 h1 hz0 hz1

/-- Bounds check of the `UseHint` block at an ML-DSA instance. -/
theorem mldsaUseHint_boundsOk {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2) :
    boundsOkMR true (iv2 (0, Fips204.q - 1) (0, 1)) (useHintProg P) (iv1 mldsaOut) = true := by
  rcases hP with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact mldsaUseHintBlock_mldsa88_ok
  · exact mldsaUseHintBlock_mldsa32_ok

/-- The ML-DSA `UseHint` block computes `Spec.useHint` for `r ∈ [0, q)` and a hint word in
    `{0, 1}`, at both parameter sets. -/
theorem mldsaUseHint_word {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (r h : BitVec P.w) (h0 : 0 ≤ rd true r) (h1 : rd true r < Spec.q)
    (hh0 : 0 ≤ rd true h) (hh1 : rd true h ≤ 1) :
    zvals true ((useHintProg P).denote (.cons r (.cons h .nil)))
      = .cons (Spec.useHint γ2 (decide (rd true h = 1)) (rd true r)) .nil :=
  useHint_denote hP _ (mldsaUseHint_boundsOk hP) r h h0 h1 hh0 hh1

end CatCrypt.Crypto.SecureCompilation.Haxc.RoundCodecSpec
