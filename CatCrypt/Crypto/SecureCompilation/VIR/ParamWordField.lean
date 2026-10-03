/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NarrowField
public import Transfer.Congruence.ParamGuard

/-!
# The narrow-field blocks as guarded squares

The single-word multiplication blocks of `NarrowField` are registered as guarded
relatedness squares of ParamTransfer, so that `param_guard` transfers an expression over
`w`-bit words built from these blocks and from wrapping addition and subtraction to the
corresponding expression in `ZMod p`, leaving to a discharger the bound conditions at each
node.

Two decoders read a `w`-bit word into `ZMod p`:

* `wordDec p x = x.toNat`, the unsigned reading, along which the Barrett block realizes the
  field product;
* `scaledDec p c x = x.toNat · c`, the unsigned reading times a constant. At
  `c = (2 ^ w)⁻¹` (`montScale`) the Montgomery block realizes the field product, and at
  `c = −(2 ^ (2 w))⁻¹` (`plantScale`) the Plantard block does.

Each multiply square has the guard "both operands are at most `inMax`" and takes the side
condition of its block (`barOk`, `montOk`, `plantOk`) as a `Fact`. The invertibility of
`2 ^ w` and `2 ^ (2 w)` modulo `p` follows from the congruences in `montOk` and `plantOk`.
Wrapping addition and subtraction are squares along both decoders under the no-overflow
guard `a + b < 2 ^ w` and the order guard `b ≤ a`.

The bound is carried by the guard of each node, not by the relation: the relation is the
equation `dec x = v`, and the Param database holds one square per operation and encoding.

`word_guard` is the guard discharger: it splits conjunctions and closes each conjunct from
hypotheses by `assumption`, `omega`, `bv_omega` after unfolding the three field instances,
or `omega` after removing one wrap of a sum or product whose no-overflow bound `omega`
proves. It does not propagate intervals through a node: the bound on an intermediate word
must follow linearly from hypotheses on the operands. It is registered as an alternative
of `transfer_guard_disch`.

## Main definitions

* `wordDec`, `scaledDec`, `montScale`, `plantScale`: the decoders and the two scales.
* `word_guard`: the guard discharger.

## Main results

* `wordAddRelatedOn`, `wordSubRelatedOn`, `scaledAddRelatedOn`, `scaledSubRelatedOn`: the
  wrapping addition and subtraction squares.
* `mulBarRelatedOn`, `mulMontRelatedOn`, `mulPlantRelatedOn`: the multiply squares.
* `wordDec_mulBar_add`, `montDec_mulMont_add`, `mlkem_wordDec_mulBar_add`: the
  transfer of `(x + y) · z` through each block by `param_guard`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ParamWordField

open Transfer
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowField

/-! ## Decoders -/

/-- The unsigned reading of a `w`-bit word in `ZMod p`. -/
def wordDec (p : ℕ) {w : ℕ} (x : BitVec w) : ZMod p := (x.toNat : ZMod p)

/-- The unsigned reading of a `w`-bit word in `ZMod p`, multiplied by `c`. -/
def scaledDec (p : ℕ) {w : ℕ} (c : ZMod p) (x : BitVec w) : ZMod p := (x.toNat : ZMod p) * c

/-- The Montgomery scale `(2 ^ w)⁻¹` in `ZMod p`. -/
def montScale (p w : ℕ) : ZMod p := ((2 : ZMod p) ^ w)⁻¹

/-- The Plantard scale `−(2 ^ (2 w))⁻¹` in `ZMod p`. -/
def plantScale (p w : ℕ) : ZMod p := -((2 : ZMod p) ^ (2 * w))⁻¹

/-- A modulus `p` with `p · n ≡ −1 (mod m)` is coprime to `m`. -/
theorem coprime_of_mul_add_one_mod {m p n : ℕ} (h : (p * n + 1) % m = 0) : Nat.Coprime m p := by
  have hd : m ∣ p * n + 1 := Nat.dvd_of_mod_eq_zero h
  have hc : Nat.Coprime p (p * n + 1) := by
    simp
  exact (hc.coprime_dvd_right hd).symm

/-- A modulus `p` with `p · n ≡ 1 (mod m)` is coprime to `m`. -/
theorem coprime_of_mul_mod_one {m p n : ℕ} (h : (p * n) % m = 1) : Nat.Coprime m p := by
  have he : p * n = m * (p * n / m) + 1 := by
    have := Nat.div_add_mod (p * n) m
    omega
  have hc : Nat.Coprime m (p * n) := by
    rw [he]; simp
  exact Nat.Coprime.coprime_mul_right_right hc

/-- `2 ^ k` times its inverse is `1` in `ZMod p` when `2 ^ k` and `p` are coprime. -/
theorem two_pow_mul_inv {p k : ℕ} (h : Nat.Coprime (2 ^ k) p) :
    (2 : ZMod p) ^ k * ((2 : ZMod p) ^ k)⁻¹ = 1 := by
  have := ZMod.coe_mul_inv_eq_one (2 ^ k) h
  push_cast at this
  exact this

variable {w p : ℕ}

/-! ## Wrapping addition and subtraction -/

/-- The wrapping word sum realizes `+` along `wordDec p` when the sum does not
overflow. -/
instance wordAddRelatedOn :
    RelatedBinOpOn (wordDec p (w := w)) (fun a b => a.toNat + b.toNat < 2 ^ w) (· + ·) (· + ·)
    where
  comm a b h := by simp only [wordDec, BitVec.toNat_add, Nat.mod_eq_of_lt h, Nat.cast_add]

/-- The wrapping word difference realizes `-` along `wordDec p` when the subtrahend is at
most the minuend. -/
instance wordSubRelatedOn :
    RelatedBinOpOn (wordDec p (w := w)) (fun a b => b.toNat ≤ a.toNat) (· - ·) (· - ·) where
  comm a b h := by
    simp only [wordDec, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h), Nat.cast_sub h]

/-- The wrapping word sum realizes `+` along `scaledDec p c` when the sum does not
overflow. -/
instance scaledAddRelatedOn {c : ZMod p} :
    RelatedBinOpOn (scaledDec p (w := w) c) (fun a b => a.toNat + b.toNat < 2 ^ w)
      (· + ·) (· + ·) where
  comm a b h := by
    simp only [scaledDec, BitVec.toNat_add, Nat.mod_eq_of_lt h, Nat.cast_add, add_mul]

/-- The wrapping word difference realizes `-` along `scaledDec p c` when the subtrahend is
at most the minuend. -/
instance scaledSubRelatedOn {c : ZMod p} :
    RelatedBinOpOn (scaledDec p (w := w) c) (fun a b => b.toNat ≤ a.toNat) (· - ·) (· - ·)
    where
  comm a b h := by
    simp only [scaledDec, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h), Nat.cast_sub h,
      sub_mul]

/-! ## The multiply blocks -/

/-- The Barrett block of `F` realizes the field product along `wordDec p` on operands at
most `inMax`. -/
instance mulBarRelatedOn (F : WordField w p) [hF : Fact (F.barOk = true)] :
    RelatedBinOpOn (wordDec p) (fun a b => a.toNat ≤ F.inMax ∧ b.toNat ≤ F.inMax)
      F.mulBar (· * ·) where
  comm a b h := (F.mulBar_rep hF.out (u := wordDec p a) (v := wordDec p b)
    ⟨h.1, rfl⟩ ⟨h.2, rfl⟩).2

/-- The Montgomery block of `F` realizes the field product along the Montgomery decoder
`scaledDec p (montScale p w)` on operands at most `inMax`. -/
instance mulMontRelatedOn (F : WordField w p) [hF : Fact (F.montOk = true)] :
    RelatedBinOpOn (scaledDec p (montScale p w))
      (fun a b => a.toNat ≤ F.inMax ∧ b.toNat ≤ F.inMax) F.mulMont (· * ·) where
  comm a b h := by
    have key := (F.mulMont_rep hF.out (u := (a.toNat : ZMod p)) (v := (b.toNat : ZMod p))
      ⟨h.1, rfl⟩ ⟨h.2, rfl⟩).2
    have hok := hF.out
    simp only [WordField.montOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hR := two_pow_mul_inv (coprime_of_mul_add_one_mod hok.1.1)
    simp only [scaledDec, montScale]
    linear_combination (((2 : ZMod p) ^ w)⁻¹) ^ 2 * key -
      ((F.mulMont a b).toNat : ZMod p) * ((2 : ZMod p) ^ w)⁻¹ * hR

/-- The Plantard block of `F` realizes the field product along the Plantard decoder
`scaledDec p (plantScale p w)` on operands at most `inMax`. -/
instance mulPlantRelatedOn (F : WordField w p) [hF : Fact (F.plantOk = true)] :
    RelatedBinOpOn (scaledDec p (plantScale p w))
      (fun a b => a.toNat ≤ F.inMax ∧ b.toNat ≤ F.inMax) F.mulPlant (· * ·) where
  comm a b h := by
    have key := (F.mulPlant_rep hF.out (u := (a.toNat : ZMod p)) (v := (b.toNat : ZMod p))
      ⟨h.1, rfl⟩ ⟨h.2, rfl⟩).2
    have hok := hF.out
    simp only [WordField.plantOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hR := two_pow_mul_inv (coprime_of_mul_mod_one hok.1.1)
    simp only [scaledDec, plantScale]
    linear_combination (-(((2 : ZMod p) ^ (2 * w))⁻¹) ^ 2) * key +
      ((F.mulPlant a b).toNat : ZMod p) * ((2 : ZMod p) ^ (2 * w))⁻¹ * hR

/-! ## The three field instances -/

instance mlkemField_barOk_fact : Fact (mlkemField.barOk = true) := ⟨mlkemField_barOk⟩
instance mlkemField_montOk_fact : Fact (mlkemField.montOk = true) := ⟨mlkemField_montOk⟩
instance mlkemField_plantOk_fact : Fact (mlkemField.plantOk = true) := ⟨mlkemField_plantOk⟩
instance mldsaField_barOk_fact : Fact (mldsaField.barOk = true) := ⟨mldsaField_barOk⟩
instance mldsaField_montOk_fact : Fact (mldsaField.montOk = true) := ⟨mldsaField_montOk⟩
instance mldsaField_plantOk_fact : Fact (mldsaField.plantOk = true) := ⟨mldsaField_plantOk⟩
instance babyBearField_barOk_fact : Fact (babyBearField.barOk = true) :=
  ⟨babyBearField_barOk⟩
instance babyBearField_montOk_fact : Fact (babyBearField.montOk = true) :=
  ⟨babyBearField_montOk⟩
instance babyBearField_plantOk_fact : Fact (babyBearField.plantOk = true) :=
  ⟨babyBearField_plantOk⟩

/-! ## The guard discharger -/

/-- The guard discharger of the word squares. It splits a conjunction and closes each
conjunct by `assumption`, by `omega`, by `omega` after removing one wrap of a word sum or
product through `Nat.mod_eq_of_lt`, or by `bv_omega` after unfolding the field instances
`mlkemField`, `mldsaField`, `babyBearField`. -/
syntax "word_guard" : tactic

macro_rules
  | `(tactic| word_guard) =>
    `(tactic| first
      | assumption
      | (apply And.intro <;> word_guard)
      | omega
      | (simp only [BitVec.toNat_add, BitVec.toNat_mul]
         rw [Nat.mod_eq_of_lt (by omega)]
         omega)
      | ((try simp only [mlkemField, mldsaField, babyBearField] at *)
         bv_omega))

macro_rules
  | `(tactic| transfer_guard_disch) => `(tactic| word_guard)

/-! ## Transfer through the blocks -/

/-- The Barrett block on a sum: `(x + y) · z` decodes to the field expression, with the
guards closed from the bounds on the operands. -/
theorem wordDec_mulBar_add (F : WordField w p) [Fact (F.barOk = true)] (x y z : BitVec w)
    (hxy : x.toNat + y.toNat < 2 ^ w) (hs : x.toNat + y.toNat ≤ F.inMax)
    (hz : z.toNat ≤ F.inMax) :
    wordDec p (F.mulBar (x + y) z) = (wordDec p x + wordDec p y) * wordDec p z := by
  param_guard

/-- The Montgomery block on a sum: `(x + y) · z` in the Montgomery domain decodes to the
field expression, with the guards closed from the bounds on the operands. -/
theorem montDec_mulMont_add (F : WordField w p) [Fact (F.montOk = true)] (x y z : BitVec w)
    (hxy : x.toNat + y.toNat < 2 ^ w) (hs : x.toNat + y.toNat ≤ F.inMax)
    (hz : z.toNat ≤ F.inMax) :
    scaledDec p (montScale p w) (F.mulMont (x + y) z) =
      (scaledDec p (montScale p w) x + scaledDec p (montScale p w) y) *
        scaledDec p (montScale p w) z := by
  param_guard

/-- The ML-KEM Barrett block on a sum of two words below `q / 2` times a word below `q`:
the guards close from the numeric bounds. -/
theorem mlkem_wordDec_mulBar_add (x y z : BitVec 16) (hx : x.toNat ≤ 1664)
    (hy : y.toNat ≤ 1664) (hz : z.toNat ≤ 3328) :
    wordDec 3329 (mlkemField.mulBar (x + y) z) =
      (wordDec 3329 x + wordDec 3329 y) * wordDec 3329 z := by
  param_guard

end CatCrypt.Crypto.SecureCompilation.VIR.ParamWordField
