/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonWidth3Compile
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4
public import CatCrypt.Crypto.Hash.Poseidon.BN254

/-!
# Poseidon over the BN254 scalar field, lowered to four 64-bit limbs per lane

`PoseidonWidth3.permComAt params3 i` is the width-3 circomlib Poseidon permutation
over `ZMod r`, `r` the BN254 scalar-field modulus, as a `fieldDialect` program. Its
bindings are `fAdd`, `fMul`, `fConst` and `fCopy` at `r`, so it is covered by the
Montgomery lowering `FieldToJasminLimbsMont4.loweringL bn254r`, and
`fieldToJasminLimbsMont4_denote` applies: `permJasminAt i` is a
`MultiReturnCom jasminDialect` over the twelve limb registers of the three input
lanes that returns the four limbs of the Montgomery form of output lane `i`.

## Main definitions

* `bn254r`: the `Mont4Prime` record of `r`, with `nInv = -r⁻¹ mod 2^64`.
* `permJasminAt i`: the lowered permutation program returning lane `i`.
* `limbVal x`: the twelve input limbs, the Montgomery forms of `x 0`, `x 1`, `x 2`.

## Main results

* `permComAt_params3_denote`: the field program computes `Hash.Poseidon.BN254.permute3`.
* `permJasminAt_denote`: **for every input `x`, the lowered program maps the limbs of
  the Montgomery forms of `x` to the limbs of the Montgomery form of lane `i` of
  `permute3 x`.**
* `permJasminAt_hash2`: lane `0` of the lowered program on `(0, a, b)` is the
  Montgomery form of `hash2 a b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonBN254

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldExprCompile (inputs)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4 (Mont4Prime enc)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4
open CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonWidth3
open CatCrypt.Crypto.Hash.Poseidon.BN254 (r params3 permute3 hash2)

/-- The BN254 scalar-field modulus `r` with `nInv = -r⁻¹ mod 2^64`. -/
def bn254r : Mont4Prime where
  p := r
  nInv := 0xc2e1f593efffffff
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The three input lanes. -/
abbrev inCtxt : Ctxt fieldDialect := FieldExprCompile.inCtxt r 3

/-- The lowering of the permutation program returning lane `i`, over four 64-bit
    limbs per lane in Montgomery form. -/
def permJasminAt (i : Fin 3) :
    MultiReturnCom jasminDialect ((loweringL bn254r).mapCtx inCtxt)
      ((loweringL bn254r).mapTys (.fp r)) :=
  (loweringL bn254r).lowerMulti (permComAt params3 i)

/-- The valuation of the three input lanes. -/
def inVal (x : Fin 3 → ZMod r) : Valuation inCtxt :=
  .cons (x 0) (.cons (x 1) (.cons (x 2) .nil))

/-- The twelve input limbs: the Montgomery forms of the three lanes, in lane order. -/
def limbVal (x : Fin 3 → ZMod r) : Valuation ((loweringL bn254r).mapCtx inCtxt) :=
  hvAppend (enc bn254r (x 0)) (hvAppend (enc bn254r (x 1))
    (hvAppend (enc bn254r (x 2)) .nil))

theorem inputs_inVal (x : Fin 3 → ZMod r) : inputs (inVal x) = x := by
  funext i
  fin_cases i <;> rfl

theorem flatVal_inVal (x : Fin 3 → ZMod r) :
    flatVal (fun {t} v => encL bn254r (t := t) v) (inVal x) = limbVal x := rfl

/-- **The field program computes the circomlib width-3 permutation.** -/
theorem permComAt_params3_denote (i : Fin 3) (x : Fin 3 → ZMod r) :
    (permComAt params3 i).denote (inVal x) = permute3 x i := by
  rw [permComAt_denote params3 rfl i, inputs_inVal]

/-- `GoodAMC r` coverage implies `GoodV` coverage at `bn254r`. -/
private theorem covered_goodV : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t), BlockLoweringCPS.CoveredCom (GoodAMC r) c →
      BlockLoweringCPS.CoveredCom (GoodV bn254r) c
  | _, _, .ret _, _ => trivial
  | _, _, .var _ body, hc =>
    ⟨by rcases hc.1 with h | h | h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h)),
      covered_goodV body hc.2⟩

/-- **Correctness of the lowered permutation for all inputs.** The lowered program,
    run on the limbs of the Montgomery forms of `x 0`, `x 1`, `x 2`, returns the limbs
    of the Montgomery form of lane `i` of `permute3 x`. -/
theorem permJasminAt_denote (i : Fin 3) (x : Fin 3 → ZMod r) :
    (permJasminAt i).denote (limbVal x) = enc bn254r (permute3 x i) := by
  have h := fieldToJasminLimbsMont4_denoteV bn254r (permComAt params3 i)
    (covered_goodV _ (permComAt_covered params3 i)) (inVal x)
  rw [flatVal_inVal, permComAt_params3_denote] at h
  exact h.trans (encL_fp bn254r _)

/-- Lane `0` of the lowered program on `(0, a, b)` is the Montgomery form of circomlib
    `poseidon([a, b])`. -/
theorem permJasminAt_hash2 (a b : ZMod r) :
    (permJasminAt 0).denote (limbVal ![0, a, b]) = enc bn254r (hash2 a b) :=
  permJasminAt_denote 0 ![0, a, b]

end CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonBN254
