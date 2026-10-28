/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.MLKEM.NttTemplate
public import CatCrypt.Crypto.MLDSA.NttTemplate
public import CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord

/-!
# The word-level NTT and base multiplication against FIPS 203 and FIPS 204

`MLKEM/NttTemplate.lean` and `MLDSA/NttTemplate.lean` identify the template transform
`nttSpec` with the FIPS 203 transform `Spec.Ntt.nttKem` (Algorithm 9, in the pair
layout `coeffsOfPairs`) and the FIPS 204 transform `Spec.Ntt.ntt` (Algorithm 41). This
module identifies the template base multiplication `RingDialect.basemulF` at the ML-KEM
parameters with FIPS 203 `MultiplyNTTs` (`Spec.Ntt.basemulKem`, Algorithms 11 and 12)
and restates the word-level theorems of the signed transform, its inverse, the base
multiplication and the pointwise product against the FIPS statements.

## Main results

* `basemulF_mlkem_eq_basemulKem` — `basemulF` at `ψ = 17`, seven layers and 256
  coefficients is `coeffsOfPairs ∘ basemulKem` on the pair layouts of its operands.
* `mlkemSigned_nttKem` — every output word of the signed 16-bit ML-KEM transform is
  the FIPS 203 transform of the input modulo `q`, in the pair layout.
* `mlkemSignedInv_nttKem` — on the words of `nttKem a`, every output word of the
  signed 16-bit ML-KEM inverse is `2 ^ 16 · a i` modulo `q`.
* `mlkemBasemul_basemulKem`, `mlkemBasemul_polyMulKem` — every output word of the
  16-bit base multiplication, times `2 ^ 16`, is `MultiplyNTTs` of the inputs, and on
  the transforms of `a` and `b` it is the transform of the product `a · b`.
* `mldsaSigned_ntt` — every output word of the signed 32-bit ML-DSA transform is the
  FIPS 204 transform of the input modulo `q`.
* `mldsaPointwise_polyMul` — on the transforms of `a` and `b`, every output word of the
  32-bit pointwise product, times `2 ^ 32`, is the transform of the product `a · b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NttFipsWord

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.RingDialect (Limbs basemulF rowLanes)
open CatCrypt.Crypto.MLKEM.Spec.Ntt (nttKem basemulKem basemulPair gammaKem bitRev7
  zetaKem polyMulKem negaMulKem_eq_polyMulKem nttKem_negaMulKem)
open CatCrypt.Crypto.MLKEM.Spec.Coeffs (Tq_kem coeffsOfPairs pairsOfCoeffs pairIndex
  pairs_roundtrip)

/-! ## ML-KEM -/

/-- The single row of a one-modulus limb family at `q = 3329`. -/
def row (x : Limbs [3329] 256) : Fin 256 → ZMod 3329 := x ⟨0, by simp⟩

/-- The one-modulus limb family at `q = 3329` whose row is `v`. -/
def toLimbs (v : Fin 256 → ZMod 3329) : Limbs [3329] 256
  | ⟨0, _⟩ => v
  | ⟨n + 1, h⟩ => absurd h (by simp)

theorem row_toLimbs (v : Fin 256 → ZMod 3329) : row (toLimbs v) = v := rfl

/-- **The ML-KEM base multiplication is FIPS 203 `MultiplyNTTs`.** At `ψ = 17`,
seven layers and 256 coefficients, `basemulF` is `basemulKem` on the pair layouts of its
operands, read back in the pair layout. -/
theorem basemulF_mlkem_eq_basemulKem (x y : Limbs [3329] 256) (i : Fin 256) :
    basemulF 8 7 [17] x y ⟨0, by simp⟩ i
      = coeffsOfPairs (basemulKem (pairsOfCoeffs (row x)) (pairsOfCoeffs (row y))) i := by
  unfold basemulF
  simp only [List.getD_cons_zero, show 8 - 7 = 1 from rfl, pow_one]
  rw [BasemulWord.blockMul_two]
  have hi := i.isLt
  unfold coeffsOfPairs basemulKem basemulPair gammaKem blockRoot
  split_ifs with h
  all_goals simp only [rowLanes, row, pairsOfCoeffs, pairIndex,
    CatCrypt.Crypto.MLKEM.Spec.Coeffs.pairFst, CatCrypt.Crypto.MLKEM.Spec.Coeffs.pairSnd,
    zetaKem]
  · have e : 2 * (i.val / 2) = i.val := by omega
    have hb : (bitRev7 ⟨i.val / 2, by omega⟩).val
        = CatCrypt.Crypto.Lattice.BitReversalGeneric.bitrev 7 (i.val / 2) := rfl
    simp only [e, hb, dite_eq_left (show i.val < 2 ^ 8 by omega),
      dite_eq_left (show i.val + 1 < 2 ^ 8 by omega), Nat.cast_ofNat]
    ring
  · have e : 2 * (i.val / 2) = i.val - 1 := by omega
    have e' : i.val - 1 + 1 = i.val := by omega
    simp only [e, e', dite_eq_left (show i.val < 2 ^ 8 by omega),
      dite_eq_left (show i.val - 1 < 2 ^ 8 by omega)]

/-- **The signed 16-bit ML-KEM transform against FIPS 203.** From integer
representatives `f` of `a` below `q` in absolute value, every output word of
`nttProgSW mlkemNtt mlkemSigned` is below `8 q` in absolute value and is, modulo `q`,
the FIPS 203 transform `nttKem a` in the pair layout. -/
theorem mlkemSigned_nttKem (a : Fin 256 → ZMod 3329) (f : ℕ → ℤ) (hf : ∀ j, |f j| < 3329)
    (hfa : ∀ j (hj : j < 256), ((f j : ℤ) : ZMod 3329) = a ⟨j, hj⟩) (i : Fin 256) :
    |(hvGetG (Rw 16) (0 : BitVec 16) ((nttProgSW mlkemNtt mlkemSigned).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt| < 8 * 3329 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((nttProgSW mlkemNtt mlkemSigned).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt : ℤ) : ZMod 3329)
      = coeffsOfPairs (nttKem a) i := by
  obtain ⟨hb, he⟩ := mlkemSigned_denote f hf i i.isLt
  refine ⟨hb, he.trans ?_⟩
  rw [nttSpec_congr _ 7 8 (by norm_num) _ (CatCrypt.Crypto.MLKEM.NttTemplate.lanes a)
    (fun j hj => by
      rw [CatCrypt.Crypto.MLKEM.NttTemplate.lanes, dite_eq_left (show j < 256 from hj)]
      exact hfa j hj)]
  exact congrFun (CatCrypt.Crypto.MLKEM.NttTemplate.nttSpec_mlkem_eq_nttKem a) i

/-- **The signed 16-bit ML-KEM inverse against FIPS 203.** From integer
representatives `f` of the pair layout of `nttKem a` below `q` in absolute value, every
output word of `inttProgSW mlkemNtt mlkemSignedInv 512` is below `q` in absolute value
and is `2 ^ 16 · a i` modulo `q`: the inverse of the FIPS 203 transform, scaled by the
Montgomery radix. -/
theorem mlkemSignedInv_nttKem (a : Fin 256 → ZMod 3329) (f : ℕ → ℤ) (hf : ∀ j, |f j| < 3329)
    (hfa : ∀ j (hj : j < 256), ((f j : ℤ) : ZMod 3329) = coeffsOfPairs (nttKem a) ⟨j, hj⟩)
    (i : Fin 256) :
    |(hvGetG (Rw 16) (0 : BitVec 16) ((inttProgSW mlkemNtt mlkemSignedInv 512).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt| < 3329 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((inttProgSW mlkemNtt mlkemSignedInv 512).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt : ℤ) : ZMod 3329)
      = (2 ^ 16 : ZMod 3329) * a i := by
  obtain ⟨hb, he⟩ := mlkemSignedInv_denote f hf i i.isLt
  refine ⟨hb, he.trans ?_⟩
  have h3 := congrFun (CatCrypt.Crypto.MLKEM.NttTemplate.inttSpec_mlkem_nttKem a) i
  simp only [inttSpec] at h3 ⊢
  rw [invRun_congr _ 7 8 7 (by norm_num) _
    (CatCrypt.Crypto.MLKEM.NttTemplate.lanes (coeffsOfPairs (nttKem a)))
    (fun j hj => by
      rw [CatCrypt.Crypto.MLKEM.NttTemplate.lanes, dite_eq_left (show j < 256 from hj)]
      exact hfa j hj) i i.isLt, ← h3, ← mul_assoc]
  congr 1

/-- **The 16-bit ML-KEM base multiplication against FIPS 203.** When the first and
second operand words are representatives of the pair layouts of `s` and `t`, every
output word of `basemulProgW mlkemBasemul 17 8` is at most `23310` in absolute value
and, times `2 ^ 16`, is `MultiplyNTTs s t` modulo `q`, in the pair layout. -/
theorem mlkemBasemul_basemulKem (g : ℕ → BitVec 16)
    (hg : ∀ j, j < 512 → |(g j).toInt| ≤ 26632) (s t : Tq_kem)
    (hs : ∀ j (hj : j < 256), coeffsOfPairs s ⟨j, hj⟩ = ((g j).toInt : ZMod 3329))
    (ht : ∀ j (hj : j < 256), coeffsOfPairs t ⟨j, hj⟩ = ((g (256 + j)).toInt : ZMod 3329))
    (i : Fin 256) :
    |(hvGetG (Rw 16) (0 : BitVec 16) ((basemulProgW mlkemBasemul 17 8).denote
        (lanesVal (Rw 16) g 512 0)) i).toInt| ≤ 23310 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((basemulProgW mlkemBasemul 17 8).denote
        (lanesVal (Rw 16) g 512 0)) i).toInt : ℤ) : ZMod 3329) * ((2 ^ 16 : ℕ) : ZMod 3329)
      = coeffsOfPairs (basemulKem s t) i := by
  obtain ⟨hb, he⟩ := mlkemBasemul_basemulF g hg (toLimbs (coeffsOfPairs s))
    (toLimbs (coeffsOfPairs t)) hs ht i i.isLt
  refine ⟨hb, he.trans ?_⟩
  exact (basemulF_mlkem_eq_basemulKem _ _ i).trans
    (by simp only [row_toLimbs, pairs_roundtrip])

/-- **The 16-bit ML-KEM base multiplication computes the product.** When the operand
words are representatives of the pair layouts of `nttKem a` and `nttKem b`, every
output word of `basemulProgW mlkemBasemul 17 8`, times `2 ^ 16`, is modulo `q` the
FIPS 203 transform of the product `a · b` in `Rq`, in the pair layout. -/
theorem mlkemBasemul_polyMulKem (g : ℕ → BitVec 16)
    (hg : ∀ j, j < 512 → |(g j).toInt| ≤ 26632) (a b : Fin 256 → ZMod 3329)
    (ha : ∀ j (hj : j < 256), coeffsOfPairs (nttKem a) ⟨j, hj⟩ = ((g j).toInt : ZMod 3329))
    (hb : ∀ j (hj : j < 256),
      coeffsOfPairs (nttKem b) ⟨j, hj⟩ = ((g (256 + j)).toInt : ZMod 3329))
    (i : Fin 256) :
    (((hvGetG (Rw 16) (0 : BitVec 16) ((basemulProgW mlkemBasemul 17 8).denote
        (lanesVal (Rw 16) g 512 0)) i).toInt : ℤ) : ZMod 3329) * ((2 ^ 16 : ℕ) : ZMod 3329)
      = coeffsOfPairs (nttKem (polyMulKem a b)) i := by
  rw [← negaMulKem_eq_polyMulKem, nttKem_negaMulKem]
  exact (mlkemBasemul_basemulKem g hg _ _ ha hb i).2

/-! ## ML-DSA -/

/-- **The signed 32-bit ML-DSA transform against FIPS 204.** From integer
representatives `f` of `w` below `q` in absolute value, every output word of
`nttProgSW mldsaNtt mldsaSigned` is below `9 q` in absolute value and is the FIPS 204
transform `ntt w` modulo `q`. -/
theorem mldsaSigned_ntt (w : Fin 256 → ZMod 8380417) (f : ℕ → ℤ)
    (hf : ∀ j, |f j| < 8380417)
    (hfw : ∀ j (hj : j < 256), ((f j : ℤ) : ZMod 8380417) = w ⟨j, hj⟩) (i : Fin 256) :
    |(hvGetG (Rw 32) (0 : BitVec 32) ((nttProgSW mldsaNtt mldsaSigned).denote
        (lanesVal (Rw 32) (fun j => BitVec.ofInt 32 (f j)) 256 0)) i).toInt| < 9 * 8380417 ∧
    (((hvGetG (Rw 32) (0 : BitVec 32) ((nttProgSW mldsaNtt mldsaSigned).denote
        (lanesVal (Rw 32) (fun j => BitVec.ofInt 32 (f j)) 256 0)) i).toInt : ℤ)
        : ZMod 8380417)
      = CatCrypt.Crypto.MLDSA.Spec.Ntt.ntt w i := by
  have hT : SSchedOk mldsaNtt mldsaSigned := mldsaSignedWord_ok.1
  obtain ⟨hb, he⟩ := nttProgSW_denote mldsaNtt mldsaSigned mldsaNtt_ok hT f
    (fun j => by simpa [mldsaSigned] using hf j) i i.isLt
  refine ⟨hb, he.trans ?_⟩
  rw [← CatCrypt.Crypto.MLDSA.NttTemplate.nttSpec_eq_ntt]
  exact nttSpec_congr _ 8 8 le_rfl _ _ (fun j hj => by
    rw [CatCrypt.Crypto.MLDSA.NttTemplate.lanes, dite_eq_left (show j < 256 from hj)]
    exact hfw j hj) i

/-- **The 32-bit ML-DSA pointwise product computes the product.** When the operand
words are representatives of `ntt a` and `ntt b`, every output word of
`pointwiseProgW mldsaPointwise 8` is at most `5514723` in absolute value and, times
`2 ^ 32`, is the FIPS 204 transform of the product `a · b` in `Rq` modulo `q`. -/
theorem mldsaPointwise_polyMul (g : ℕ → BitVec 32)
    (hg : ∀ j, j < 512 → |(g j).toInt| ≤ 75423753) (a b : Fin 256 → ZMod 8380417)
    (ha : ∀ j (hj : j < 256),
      CatCrypt.Crypto.MLDSA.Spec.Ntt.ntt a ⟨j, hj⟩ = ((g j).toInt : ZMod 8380417))
    (hb : ∀ j (hj : j < 256),
      CatCrypt.Crypto.MLDSA.Spec.Ntt.ntt b ⟨j, hj⟩ = ((g (256 + j)).toInt : ZMod 8380417))
    (i : Fin 256) :
    |(hvGetG (Rw 32) (0 : BitVec 32) ((pointwiseProgW mldsaPointwise 8).denote
        (lanesVal (Rw 32) g 512 0)) i).toInt| ≤ 5514723 ∧
    (((hvGetG (Rw 32) (0 : BitVec 32) ((pointwiseProgW mldsaPointwise 8).denote
        (lanesVal (Rw 32) g 512 0)) i).toInt : ℤ) : ZMod 8380417)
        * ((2 ^ 32 : ℕ) : ZMod 8380417)
      = CatCrypt.Crypto.MLDSA.Spec.Ntt.ntt (CatCrypt.Crypto.MLDSA.Spec.Ntt.polyMul a b) i := by
  obtain ⟨hbd, he⟩ := pointwiseProgW_denote mldsaPointwise mldsaPointwise_ok 8 g hg i i.isLt
  refine ⟨hbd, he.trans ?_⟩
  rw [CatCrypt.Crypto.MLDSA.Spec.Ntt.ntt_polyMul, ha i i.isLt, hb i i.isLt]
  rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.NttFipsWord
