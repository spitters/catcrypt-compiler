/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.MLKEM.Spec.Ntt
public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttInverse

/-!
# The ML-KEM NTT as an instance of the negacyclic NTT template

`VIR/NegacyclicNttTemplate.lean` lowers the merged-twiddle negacyclic NTT to a
`fieldDialect` program `nttProg P`, generic in the parameter record `P`, and
proves once that lane `i` of the program is `nttSpec` at `i`.  At
`P = mlkemNtt` (`q = 3329`, 256 coefficients, seven layers, `ψ = 17`) lanes
`2 j` and `2 j + 1` are the two components of pair `j` of the FIPS 203
transform `Spec.Ntt.nttKem` (Algorithm 9).  The tree states FIPS 203's inverse
transform (Algorithm 10) only as the inverse of `nttKem`; the scaled template
inverse `inttSpec` with scaling `128⁻¹ = 3303` is that inverse on both sides,
through the pair layout `coeffsOfPairs`.

## Main results

* `nttSpec_eq_nttHalf` — lane `2 j + r` of `nttSpec` at the ML-KEM parameters is
  the length-128 transform of the coefficients `2 s + r`, read at `BitRev7 j`.
* `nttProg_mlkem_eq_nttKem` — lanes `2 j` and `2 j + 1` of `nttProg mlkemNtt` on
  the coefficients of `a` are the components of `Spec.Ntt.nttKem a j`.
* `nttSpec_mlkem_eq_nttKem` — on the 256 coefficients, `nttSpec` at the ML-KEM
  parameters is `coeffsOfPairs ∘ Spec.Ntt.nttKem`.
* `inttSpec_mlkem_nttKem`, `nttKem_inttSpec_mlkem` — `inttSpec` at scaling
  `3303` is a left and a right inverse of `Spec.Ntt.nttKem`.
* `inttProg_mlkem_nttKem` — lane `i` of `inttProg mlkemNtt 3303` on the lanes of
  `nttKem a` is `a i`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.NttTemplate

open CatCrypt.Crypto.MLKEM.Spec.Ntt
open CatCrypt.Crypto.MLKEM.Spec.Coeffs (Tq_kem coeffsOfPairs pairsOfCoeffs pairIndex
  pairs_roundtrip)
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral (hvGetD)

/-- The coefficients of `a` as a lane function, zero past index `255`. -/
def lanes (a : Fin 256 → ZMod 3329) (k : ℕ) : ZMod 3329 :=
  if h : k < 256 then a ⟨k, h⟩ else 0

/-- Lane `2 j + r` of `nttSpec` at `ψ = 17`, seven layers and 256 coefficients is
the length-128 twisted transform of the coefficients `2 s + r`, read at
`BitRev7 j`. -/
theorem nttSpec_eq_nttHalf (a : Fin 256 → ZMod 3329) (j : Fin 128) (r : ℕ) (hr : r < 2) :
    nttSpec (17 : ZMod 3329) 7 8 (lanes a) (2 * j.val + r)
      = nttHalf (fun s : Fin 128 => a ⟨2 * s.val + r, by omega⟩) (bitRev7 j) := by
  have h2 : (2 : ℕ) ^ (8 - 7) = 2 := by norm_num
  have hdiv : (2 * j.val + r) / 2 = j.val := by omega
  have hmod : (2 * j.val + r) % 2 = r := by omega
  rw [nttSpec, h2, hdiv, hmod, show (2 : ℕ) ^ 7 = 128 from by norm_num, nttHalf_apply,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lanes, dite_eq_left (by omega)]
  congr 1
  · exact congrArg a (Fin.ext (by simp only; omega))
  · rw [mul_comm (s.val)]; rfl

/-- **The ML-KEM instance.** Lanes `2 j` and `2 j + 1` of the template program at
`mlkemNtt` are the two components of pair `j` of the FIPS 203 NTT. -/
theorem nttProg_mlkem_eq_nttKem (a : Fin 256 → ZMod 3329) (j : Fin 128) :
    hvGetD ((nttProg mlkemNtt).denote (fnVal 3329 (lanes a) 256 0)) (2 * j.val)
        = (nttKem a j).1 ∧
    hvGetD ((nttProg mlkemNtt).denote (fnVal 3329 (lanes a) 256 0)) (2 * j.val + 1)
        = (nttKem a j).2 := by
  constructor
  · rw [mlkemNtt_denote (lanes a) _ (by omega)]
    exact nttSpec_eq_nttHalf a j 0 (by omega)
  · rw [mlkemNtt_denote (lanes a) _ (by omega)]
    exact nttSpec_eq_nttHalf a j 1 (by omega)

/-- On the 256 coefficients, `nttSpec` at `ψ = 17`, seven layers and 256
coefficients is the FIPS 203 transform in the pair layout. -/
theorem nttSpec_mlkem_eq_nttKem (a : Fin 256 → ZMod 3329) :
    (fun i : Fin 256 => nttSpec (17 : ZMod 3329) 7 8 (lanes a) i)
      = coeffsOfPairs (nttKem a) := by
  funext i
  have hi : i.val = 2 * (pairIndex i).val + i.val % 2 := by simp only [pairIndex]; omega
  rw [hi, nttSpec_eq_nttHalf a (pairIndex i) (i.val % 2) (Nat.mod_lt _ (by norm_num))]
  unfold coeffsOfPairs nttKem
  split_ifs with h
  · congr 1
    funext s
    exact congrArg a (Fin.ext (by simp only [pairFst_val]; omega))
  · congr 1
    funext s
    exact congrArg a (Fin.ext (by simp only [pairSnd_val]; omega))

/-- **The inverse is a left inverse of the FIPS 203 transform.** `inttSpec` at
`ψ = 17`, seven layers and scaling `128⁻¹ = 3303`, applied to the lanes of
`nttKem a`, returns the coefficients of `a`. -/
theorem inttSpec_mlkem_nttKem (a : Fin 256 → ZMod 3329) :
    (fun i : Fin 256 =>
      inttSpec (17 : ZMod 3329) 7 8 (3303 : ZMod 3329) (lanes (coeffsOfPairs (nttKem a))) i)
      = a := by
  funext i
  have hfwd : ∀ j, j < 2 ^ 8 →
      lanes (coeffsOfPairs (nttKem a)) j = nttSpec (17 : ZMod 3329) 7 8 (lanes a) j := by
    intro j hj
    rw [lanes, dite_eq_left (show j < 256 from hj)]
    exact (congrFun (nttSpec_mlkem_eq_nttKem a) ⟨j, hj⟩).symm
  rw [inttSpec, invRun_congr _ 7 8 7 (by norm_num) _ _ hfwd i i.isLt, ← inttSpec,
    inttSpec_nttSpec (17 : ZMod 3329) 7 8 (mlkemNtt.psi_pow mlkemNtt_ok) (by norm_num)
      (by norm_num) (3303 : ZMod 3329) (ScaleOk.cast mlkemNtt 3303 mlkem_scaleOk) _ i i.isLt,
    lanes, dite_eq_left i.isLt]

/-- **The inverse is a right inverse of the FIPS 203 transform.** `nttKem` of the
coefficients `inttSpec` produces from the lanes of `t` is `t`. -/
theorem nttKem_inttSpec_mlkem (t : Tq_kem) :
    nttKem (fun i : Fin 256 =>
      inttSpec (17 : ZMod 3329) 7 8 (3303 : ZMod 3329) (lanes (coeffsOfPairs t)) i) = t := by
  set u : Fin 256 → ZMod 3329 := fun i =>
    inttSpec (17 : ZMod 3329) 7 8 (3303 : ZMod 3329) (lanes (coeffsOfPairs t)) i with hu
  have h : coeffsOfPairs (nttKem u) = coeffsOfPairs t := by
    rw [← nttSpec_mlkem_eq_nttKem u]
    funext i
    have hcongr : ∀ j, j < 2 ^ 8 → lanes u j
        = inttSpec (17 : ZMod 3329) 7 8 (3303 : ZMod 3329) (lanes (coeffsOfPairs t)) j := by
      intro j hj
      rw [lanes, dite_eq_left (show j < 256 from hj)]
    rw [nttSpec_congr _ 7 8 (by norm_num) _ _ hcongr,
      nttSpec_inttSpec (17 : ZMod 3329) 7 8 (mlkemNtt.psi_pow mlkemNtt_ok) (by norm_num)
        (by norm_num) (3303 : ZMod 3329) (ScaleOk.cast mlkemNtt 3303 mlkem_scaleOk) _ i i.isLt,
      lanes, dite_eq_left i.isLt]
  have h' := congrArg pairsOfCoeffs h
  rwa [pairs_roundtrip, pairs_roundtrip] at h'

/-- **The ML-KEM inverse instance.** Lane `i` of the template inverse program at
`mlkemNtt` with scaling `3303`, on the lanes of `nttKem a`, is `a i`. -/
theorem inttProg_mlkem_nttKem (a : Fin 256 → ZMod 3329) (i : Fin 256) :
    hvGetD ((inttProg mlkemNtt 3303).denote
      (fnVal 3329 (lanes (coeffsOfPairs (nttKem a))) 256 0)) i = a i :=
  (inttProg_denote mlkemNtt mlkemNtt_ok 3303 _ i i.isLt).trans
    (congrFun (inttSpec_mlkem_nttKem a) i)

end CatCrypt.Crypto.MLKEM.NttTemplate
