/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

/-!
# Montgomery field blocks over four 64-bit limbs for an odd modulus below `2^256`

The four-limb instance of `FieldLimbs.Mont`. A modulus record is
`Mont4Prime := Mont.LimbParams 4`; an element `x` of `ZMod p` is represented by the four
little-endian 64-bit limbs of the canonical representative of its Montgomery form
`x · 2^256` (`enc`). Each block takes its operands as four limb variables and is the
generic block of `FieldLimbs.Mont` on the list of those variables; each value theorem
is the generic theorem at `n = 4`, with `Mont.limbsN 4` read as
`Curve25519.limbsOf` (`limbsN_four`).

## Main definitions

* `Mont4Prime`: the modulus record.
* `R`, `enc`: the Montgomery factor and the encoding.
* `addBlk`, `mulBlk`, `constBlk`, `subBlk`, `negBlk`, `invBlk`: the blocks; the copy
  block is `FieldLimbs.Curve25519.copyBlk`.

## Main results

* `limbsN_four`, `enc_eq`: the four-limb readings of the generic limbs and encoding.
* `addBlk_denote`, `mulBlk_denote`, `constBlk_denote`, `copyBlk_denote`: the value
  theorems of the blocks.
* `enc_injective`: the encoding is injective.
* `subBlk_denote`, `negBlk_denote`: the blocks on canonical representatives;
  `subBlk_denote_enc`, `negBlk_denote_enc` on Montgomery forms.
* `invBlk_denote_pow`: the inversion block gives `enc (x^(p-2))`;
  `invBlk_denote_inv` gives `enc x⁻¹` at a prime modulus (`pow_sub_two_eq_inv`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 MC lk eBin_denote Pres bindK_denote nv nv_cons nv_nil R4 limbsOf ret4_denote copyBlk)

/-! ## 1. The modulus and the encoding -/

/-- An odd modulus below `2^256` with the Montgomery constant `nInv = -p⁻¹ mod 2^64`. -/
abbrev Mont4Prime : Type := Mont.LimbParams 4

variable (P : Mont4Prime)

/-- The Montgomery factor `2^256` in `ZMod p`. -/
abbrev R : ZMod P.p := Mont.R P

theorem isUnit_R : IsUnit (R P) := Mont.isUnit_R P

/-- The encoding of `ZMod p`: the four limbs of the canonical representative of the
    Montgomery form `x · 2^256`. -/
def enc (x : ZMod P.p) : ListDenote R4 := limbsOf (x * R P).val

/-- The generic four limbs of `v` are `limbsOf v`. -/
theorem limbsN_four (v : Nat) : Mont.limbsN 4 v = limbsOf v := by
  simp only [Mont.limbsN, limbsOf, Nat.div_div_eq_div_mul]
  norm_num

theorem enc_eq (x : ZMod P.p) : enc P x = Mont.enc P x := (limbsN_four _).symm

theorem val_lt (x : ZMod P.p) : x.val < P.p := ZMod.val_lt x

theorem val_lt_two_pow (x : ZMod P.p) : x.val < 2 ^ 256 := Mont.val_lt_two_pow P x

theorem enc_injective : Function.Injective (enc P) := fun x y h => by
  rw [enc_eq, enc_eq] at h
  exact Mont.enc_injective P h

/-- Fermat inversion: at a prime modulus, `x^(p-2) = x⁻¹`, including at `x = 0`. -/
theorem pow_sub_two_eq_inv (hp : P.p.Prime) (x : ZMod P.p) : x ^ (P.p - 2) = x⁻¹ :=
  Mont.pow_sub_two_eq_inv P hp x

/-! ## 2. The blocks -/

section Blocks

variable {Γ : Ctxt jasminDialect}

/-- The addition block over the limbs `x₀ … x₃` and `y₀ … y₃`. -/
def addBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  Mont.addBlk P [x₀, x₁, x₂, x₃] [y₀, y₁, y₂, y₃]

/-- The Montgomery multiplication block. -/
def mulBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  Mont.mulBlk P [x₀, x₁, x₂, x₃] [y₀, y₁, y₂, y₃]

/-- The constant block: the four 64-bit digits of `n` as `regConst` bindings. -/
def constBlk (n : Nat) : MC Γ R4 := Mont.constBlk 4 n

/-- The subtraction block over the limbs `x₀ … x₃` and `y₀ … y₃`. -/
def subBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  Mont.subBlk P [x₀, x₁, x₂, x₃] [y₀, y₁, y₂, y₃]

/-- The negation block: the subtraction of `x₀ … x₃` from four zero limbs. -/
def negBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  Mont.negBlk P [x₀, x₁, x₂, x₃]

/-- The Montgomery inversion block: the Montgomery power of `x₀ … x₃` to the exponent
    `p - 2`, from the Montgomery form of `1`. -/
def invBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  Mont.invBlk P [x₀, x₁, x₂, x₃]

variable (W : Valuation Γ)

theorem addBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) (hy : nv W [y₀, y₁, y₂, y₃] = (y * R P).val) :
    (addBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc P (x + y) := by
  rw [enc_eq]
  exact Mont.addBlk_denote P W _ _ rfl rfl x y hx hy

theorem mulBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) (hy : nv W [y₀, y₁, y₂, y₃] = (y * R P).val) :
    (mulBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc P (x * y) := by
  rw [enc_eq]
  exact Mont.mulBlk_denote P W _ _ rfl rfl x y hx hy

theorem constBlk_denote (n : Nat) : (constBlk (Γ := Γ) n).denote W = limbsOf n := by
  rw [← limbsN_four]
  exact Mont.constBlk_denote W 4 n

theorem copyBlk_denote (x₀ x₁ x₂ x₃ : Var Γ w64) :
    (copyBlk x₀ x₁ x₂ x₃).denote W = limbsOf (nv W [x₀, x₁, x₂, x₃]) := by
  refine bindK_denote _ _ _ _ fun r₁ c₀ W₁ h₁ hc₀ => ?_
  refine bindK_denote _ _ _ _ fun r₂ c₁ W₂ h₂ hc₁ => ?_
  refine bindK_denote _ _ _ _ fun r₃ c₂ W₃ h₃ hc₂ => ?_
  refine bindK_denote _ _ _ _ fun r₄ c₃ W₄ h₄ hc₃ => ?_
  rw [ret4_denote _ _ W₄ rfl]
  congr 1
  simp only [nv_cons, nv_nil]
  have e0 : lk (r₄ (r₃ (r₂ c₀))) W₄ = lk x₀ W := by
    rw [show lk (r₄ (r₃ (r₂ c₀))) W₄ = lk c₀ W₁ from (h₄ _).trans ((h₃ _).trans (h₂ c₀)),
      show lk c₀ W₁ = _ from hc₀, eBin_denote]
    exact BitVec.or_self
  have e1 : lk (r₄ (r₃ c₁)) W₄ = lk x₁ W := by
    rw [show lk (r₄ (r₃ c₁)) W₄ = lk c₁ W₂ from (h₄ _).trans (h₃ c₁),
      show lk c₁ W₂ = _ from hc₁, eBin_denote,
      show lk (r₁ x₁) W₁ = lk x₁ W from h₁ x₁]
    exact BitVec.or_self
  have e2 : lk (r₄ c₂) W₄ = lk x₂ W := by
    rw [show lk (r₄ c₂) W₄ = lk c₂ W₃ from h₄ c₂, show lk c₂ W₃ = _ from hc₂, eBin_denote,
      show lk (r₂ (r₁ x₂)) W₂ = lk x₂ W from (h₂ _).trans (h₁ x₂)]
    exact BitVec.or_self
  have e3 : lk c₃ W₄ = lk x₃ W := by
    rw [show lk c₃ W₄ = _ from hc₃, eBin_denote,
      show lk (r₃ (r₂ (r₁ x₃))) W₃ = lk x₃ W from (h₃ _).trans ((h₂ _).trans (h₁ x₃))]
    exact BitVec.or_self
  rw [e0, e1, e2, e3]

theorem subBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (a b : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = a.val) (hy : nv W [y₀, y₁, y₂, y₃] = b.val) :
    (subBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = limbsOf (a - b).val := by
  rw [← limbsN_four]
  exact Mont.subBlk_denote P W _ _ rfl rfl a b hx hy

theorem negBlk_denote (x₀ x₁ x₂ x₃ : Var Γ w64) (a : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = a.val) :
    (negBlk P x₀ x₁ x₂ x₃).denote W = limbsOf (-a).val := by
  rw [← limbsN_four]
  exact Mont.negBlk_denote P W _ rfl a hx

/-- On the Montgomery forms of `x` and `y`, the subtraction block gives the Montgomery
    form of `x - y`. -/
theorem subBlk_denote_enc (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) (hy : nv W [y₀, y₁, y₂, y₃] = (y * R P).val) :
    (subBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc P (x - y) := by
  rw [enc, sub_mul]
  exact subBlk_denote P W _ _ _ _ _ _ _ _ _ _ hx hy

/-- On the Montgomery form of `x`, the negation block gives the Montgomery form of
    `-x`. -/
theorem negBlk_denote_enc (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) :
    (negBlk P x₀ x₁ x₂ x₃).denote W = enc P (-x) := by
  rw [enc, neg_mul]
  exact negBlk_denote P W _ _ _ _ _ hx

end Blocks

/-! ## 3. Inversion -/

section Inv

variable {Γ : Ctxt jasminDialect}

/-- On the Montgomery form of `x`, the inversion block gives the Montgomery form of
    `x^(p-2)`. -/
theorem invBlk_denote_pow (W : Valuation Γ) (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) :
    (invBlk P x₀ x₁ x₂ x₃).denote W = enc P (x ^ (P.p - 2)) := by
  rw [enc_eq]
  exact Mont.invBlk_denote_pow P W _ rfl x hx

/-- At a prime modulus, on the Montgomery form of `x`, the inversion block gives the
    Montgomery form of `x⁻¹`. -/
theorem invBlk_denote_inv (hp : P.p.Prime) (W : Valuation Γ) (x₀ x₁ x₂ x₃ : Var Γ w64)
    (x : ZMod P.p) (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) :
    (invBlk P x₀ x₁ x₂ x₃).denote W = enc P x⁻¹ := by
  rw [invBlk_denote_pow P W x₀ x₁ x₂ x₃ x hx, pow_sub_two_eq_inv P hp]

end Inv

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4
