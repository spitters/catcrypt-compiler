/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum

/-!
# The field specification of fiat-crypto's `curve25519` `carry_mul`

fiat-crypto's `UnsaturatedSolinas` pipeline proves, for `m = 2^255 - 19` over five
limbs in radix `2^51`, the predicate `mul_correct` of `COperationSpecifications.v` for
`carry_mul`: for every pair of inputs whose limbs lie within the loose bounds,

* `eval (carry_mul x y) mod m = (eval x * eval y) mod m`, and
* the output limbs lie within the tight bounds.

The output is not required to be below `m`. `CarryMulSpec` is the congruence; the input
bound `LimbsBelow54` (every limb below `2^54`) is the hypothesis under which the
correctness theorems of `CarryMulCorrect.lean` are stated. CryptOpt's
`fiat_curve25519_carry_mul` (`CarryMulBlock`) is an implementation of this function.

## Main results

* `eval5`, `carryMulP`: the radix-`2^51` value of five limbs and `2^255 - 19`.
* `CarryMulSpec a b out`: `eval5 out ≡ eval5 a * eval5 b (mod 2^255 - 19)`.
* `LimbsBelow54`: every limb is below `2^54`.
* `limbs51OfNat`, `eval5_limbs51OfNat`: the five radix-`2^51` digits of a number below
  `2^255`, and their value.
* `carryMulRef`, `carryMulRef_spec`: a reference product (the canonical residue split
  into limbs) meets the specification.
* `not_carryMulSpec_two_three_five`: the specification rejects `5` as the product of
  `2` and `3`.
* `carryMulSpec_noncanonical`: the specification accepts the output `6 + p` for the
  inputs `2` and `3`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CarryMul

/-- The value `l 0 + 2^51 l 1 + 2^102 l 2 + 2^153 l 3 + 2^204 l 4` of five 64-bit limbs
    in radix `2^51`. -/
def eval5 (l : Fin 5 → BitVec 64) : Nat :=
  (l 0).toNat + 2 ^ 51 * (l 1).toNat + 2 ^ 102 * (l 2).toNat + 2 ^ 153 * (l 3).toNat +
    2 ^ 204 * (l 4).toNat

/-- The Curve25519 field modulus `2^255 - 19`. -/
abbrev carryMulP : Nat := 2 ^ 255 - 19

/-- fiat-crypto's `mul_correct` congruence for `curve25519` `carry_mul` over 64-bit
    limbs: the output value is congruent to the product of the input values modulo
    `2^255 - 19`. -/
def CarryMulSpec (a b out : Fin 5 → BitVec 64) : Prop :=
  eval5 out % carryMulP = (eval5 a * eval5 b) % carryMulP

/-- Every limb is below `2^54`. -/
def LimbsBelow54 (l : Fin 5 → BitVec 64) : Prop :=
  ∀ i, (l i).toNat < 2 ^ 54

/-- The five radix-`2^51` digits of `v`, least significant first. -/
def limbs51OfNat (v : Nat) : Fin 5 → BitVec 64 :=
  fun i => BitVec.ofNat 64 (v / 2 ^ (51 * i.val) % 2 ^ 51)

/-- The digits of a number below `2^255` have that number as their value. -/
theorem eval5_limbs51OfNat (v : Nat) (hv : v < 2 ^ 255) : eval5 (limbs51OfNat v) = v := by
  simp only [eval5, limbs51OfNat, BitVec.toNat_ofNat]
  have h3 : ((3 : Fin 5) : Nat) = 3 := rfl
  have h4 : ((4 : Fin 5) : Nat) = 4 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h3, h4]
  omega

/-- The modulus is below `2^255`. -/
theorem carryMulP_lt : carryMulP < 2 ^ 255 := by
  simp only [carryMulP]; omega

/-- The modulus is positive. -/
theorem carryMulP_pos : 0 < carryMulP := by
  simp only [carryMulP]; omega

/-- The reference product: the canonical residue of `eval5 a * eval5 b` modulo
    `2^255 - 19`, split into five limbs. -/
def carryMulRef (a b : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 :=
  limbs51OfNat ((eval5 a * eval5 b) % carryMulP)

/-- The reference product meets the specification. -/
theorem carryMulRef_spec (a b : Fin 5 → BitVec 64) : CarryMulSpec a b (carryMulRef a b) := by
  unfold CarryMulSpec carryMulRef
  rw [eval5_limbs51OfNat _ (lt_trans (Nat.mod_lt _ carryMulP_pos) carryMulP_lt), Nat.mod_mod]

/-- The specification rejects `5` as the product of `2` and `3`. -/
theorem not_carryMulSpec_two_three_five :
    ¬ CarryMulSpec (limbs51OfNat 2) (limbs51OfNat 3) (limbs51OfNat 5) := by
  unfold CarryMulSpec
  rw [eval5_limbs51OfNat 2 (by omega), eval5_limbs51OfNat 3 (by omega),
    eval5_limbs51OfNat 5 (by omega)]
  simp only [carryMulP]
  omega

/-- The specification accepts the output `6 + (2^255 - 19)` for the inputs `2` and `3`:
    it constrains the output value modulo `2^255 - 19` only. -/
theorem carryMulSpec_noncanonical :
    CarryMulSpec (limbs51OfNat 2) (limbs51OfNat 3) (limbs51OfNat (6 + carryMulP)) := by
  unfold CarryMulSpec
  rw [eval5_limbs51OfNat 2 (by omega), eval5_limbs51OfNat 3 (by omega),
    eval5_limbs51OfNat _ (by simp only [carryMulP]; omega)]
  simp only [carryMulP]
  omega

end CatCrypt.Crypto.SecureCompilation.Ascent.CarryMul
