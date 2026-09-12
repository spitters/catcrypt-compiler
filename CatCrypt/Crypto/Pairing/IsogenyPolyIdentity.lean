/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.IsogenyCoeffs
public import Transfer.Examples.ZModPolyDecide

/-!
# The BLS12-381 11-isogeny polynomial identity (RFC 9380 Appendix E.2)

The degree-63 polynomial identity `(x³+A'x+B')·yₙ²·xₐ³ = xₙ³·yₐ² + b·xₐ³·yₐ²`
that clears the isogeny rational map's denominators (`iso_map_on_curve`). Proved
`∀ x' : FpBLS` by the bounded reflective route: each Horner polynomial is bridged
to `Transfer.ZModPolyDecide.evalC` over its integer coefficient residues, both
sides are assembled with the `% p`-reducing coefficient operations (`cMulMod` /
`cPowMod` / `cAddMod`, so intermediate coefficients stay below the 381-bit prime),
and the identity reduces to a per-coefficient divisibility check over ≈64 bounded
integers closed by kernel `decide`.

The check is axiom-clean (`[propext, Classical.choice, Quot.sound]` — kernel
`decide`, no `Lean.ofReduceBool`) and elaborates in a few seconds; the module is
split out from `HashToCurveBLS12381` so this proof is verified on its own light
import closure rather than inside the heavier hash-to-curve module.

## Main results

* `isogenyPolyIdentity`: the degree-63 RFC 9380 §E.2 polynomial identity, `∀ x'`.
* `hornerEval_eq_evalC`, `hornerEvalMonic_eq_evalC`: the Horner-to-`evalC` bridges
  the proof rewrites through.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.HashToCurveBLS12381

open CatCrypt.Util (FpBLS BLS12381)
open Transfer.ZModPolyDecide

/-- Horner evaluation over `FpBLS` coefficients equals `evalC` over the integer
    residues recovered by `ZMod.val`. -/
theorem hornerEval_eq_evalC (L : List FpBLS) (x : FpBLS) :
    hornerEval L x = evalC (L.map (fun c => (c.val : ℤ))) x := by
  induction L with
  | nil => simp [hornerEval]
  | cons c cs ih =>
    cases cs with
    | nil => simp [hornerEval, evalC]
    | cons d ds =>
      rw [show hornerEval (c :: d :: ds) x = c + x * hornerEval (d :: ds) x from rfl, ih]
      simp [List.map_cons, evalC_cons]

/-- The monic variant: the implicit leading `1` becomes a trailing `[1]` on the
    integer coefficient list. -/
theorem hornerEvalMonic_eq_evalC (cs : List FpBLS) (x : FpBLS) :
    hornerEvalMonic cs x = evalC ((cs.map (fun c => (c.val : ℤ))) ++ [1]) x := by
  have hone : ((1 : FpBLS).val : ℤ) = 1 := by decide +kernel
  rw [hornerEvalMonic, hornerEval_eq_evalC, List.map_append,
    List.map_cons, List.map_nil, hone]

/-- **The isogeny polynomial identity** (RFC 9380 Appendix E.2), proved by the
    bounded reflective coefficient check (kernel `decide`, axiom-clean). -/
theorem isogenyPolyIdentity (x' : FpBLS) :
    (x' ^ 3 + isoA * x' + isoB)
        * (hornerEval isoYnum x') ^ 2
        * (hornerEvalMonic isoXden x') ^ 3
      = (hornerEval isoXnum x') ^ 3 * (hornerEvalMonic isoYden x') ^ 2
        + bls12B * (hornerEvalMonic isoXden x') ^ 3
            * (hornerEvalMonic isoYden x') ^ 2 := by
  have hb : bls12B = ((4 : ℤ) : FpBLS) := by rw [bls12B]; push_cast; ring
  have hcurve : x' ^ 3 + isoA * x' + isoB
      = evalC [(isoB.val : ℤ), (isoA.val : ℤ), 0, 1] x' := by
    simp only [evalC_cons, evalC_nil]
    push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  rw [hornerEval_eq_evalC isoYnum x', hornerEval_eq_evalC isoXnum x',
      hornerEvalMonic_eq_evalC isoXden x', hornerEvalMonic_eq_evalC isoYden x',
      hcurve, hb]
  have key :
      evalC (cMulMod ((BLS12381 : ℕ) : ℤ)
              (cMulMod ((BLS12381 : ℕ) : ℤ) [(isoB.val : ℤ), (isoA.val : ℤ), 0, 1]
                (cPowMod ((BLS12381 : ℕ) : ℤ) (isoYnum.map (fun c => (c.val : ℤ))) 2))
              (cPowMod ((BLS12381 : ℕ) : ℤ) (isoXden.map (fun c => (c.val : ℤ)) ++ [1]) 3)) x'
    = evalC (cAddMod ((BLS12381 : ℕ) : ℤ)
              (cMulMod ((BLS12381 : ℕ) : ℤ)
                (cPowMod ((BLS12381 : ℕ) : ℤ) (isoXnum.map (fun c => (c.val : ℤ))) 3)
                (cPowMod ((BLS12381 : ℕ) : ℤ) (isoYden.map (fun c => (c.val : ℤ)) ++ [1]) 2))
              (cMulMod ((BLS12381 : ℕ) : ℤ) [(4 : ℤ)]
                (cMulMod ((BLS12381 : ℕ) : ℤ)
                  (cPowMod ((BLS12381 : ℕ) : ℤ) (isoXden.map (fun c => (c.val : ℤ)) ++ [1]) 3)
                  (cPowMod ((BLS12381 : ℕ) : ℤ) (isoYden.map (fun c => (c.val : ℤ)) ++ [1]) 2)))) x' :=
    evalC_congr_of_dvd _ _ (by decide +kernel) x'
  simp only [evalC_cMulMod, evalC_cPowMod, evalC_cAddMod] at key
  have h4 : evalC [(4 : ℤ)] x' = (4 : FpBLS) := by simp [evalC]
  rw [h4] at key
  linear_combination key

end CatCrypt.Crypto.Pairing.HashToCurveBLS12381
