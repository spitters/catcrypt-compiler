/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.Encode

/-!
# Untagged arithmetic, comparisons and Boolean operations: runtime against Aeneas

The runtime names of the leaf audit's section 2.2, as squares
`RCompOk EncRel (opA args) (pure (opC (enc args)))` (`Encode.lean`) or as refuted
squares at a concrete input.

## Main results

| runtime name | runtime operation | Aeneas operation | class | theorem |
|---|---|---|---|---|
| `Add` | `Hax.add` | `x + y` (`UScalar.add`, `IScalar.add`) | 1 | `add_u_square`, `add_i_square` |
| `Sub` | `Hax.sub` | `x - y` | 1 | `sub_u_square`, `sub_i_square` |
| `Mul` | `Hax.mul` | `x * y` | 1 | `mul_u_square`, `mul_i_square` |
| `Div` | `Hax.div` | `x / y` | 1 unsigned, 2 signed | `div_u_square`, `div_i_counterexample` |
| `Rem` | `Hax.rem` | `x % y` | 1 unsigned, 2 signed | `rem_u_square`, `rem_i_counterexample` |
| `Lt` | `Hax.lt` | `decide (x < y)` | 1 | `lt_u_square`, `lt_i_square` |
| `Le` | `Hax.le` | `decide (x ≤ y)` | 1 | `le_u_square`, `le_i_square` |
| `Gt` | `Hax.gt` | `decide (x > y)` | 1 | `gt_u_square`, `gt_i_square` |
| `Ge` | `Hax.ge` | `decide (x ≥ y)` | 1 | `ge_u_square`, `ge_i_square` |
| `Eq`, `eq` | `Hax.beq` | `x == y` | 1 | `beq_u_square`, `beq_i_square` |
| `Ne` | `Hax.bne` | `x != y` | 1 | `bne_u_square`, `bne_i_square` |
| `&&` | `Hax.band` | `if a then b else ok false` | 1 | `band_square` |
| `\|\|` | `Hax.bor` | `if a then ok true else b` | 1 | `bor_square` |
| `Not` | `Hax.Not` | `!a`, `~~~x` | 1 on `Bool` and signed, 2 unsigned | `not_bool_square`, `not_i_square`, `not_u_counterexample` |
| `None` | `none` | `none` | 1 | `none_square` |
| `Some` | `some` | `some` | 1 | `some_square` |

Class 1 for `Add`, `Sub`, `Mul`: the Aeneas operation fails on overflow, and on
every input where it returns a value that value is the exact integer the runtime
computes. `Div` and `Rem` on signed operands: the runtime divides with Lean's
`Int` `/` and `%` (rounding towards negative infinity), Aeneas with `BitVec.sdiv`
and `BitVec.srem` (rounding towards zero); at `-7 / 2` the runtime gives `-4` and
Aeneas `-3`, at `-7 % 2` the runtime gives `1` and Aeneas `-1`. `Not` on an
unsigned operand: the runtime computes `-(x + 1)`, Aeneas the bitwise complement
within the width; at `!5u8` the runtime gives `-6` and Aeneas `250`.

Rust's `&&` and `||` evaluate the right operand only when the left one does not
decide the result; the Aeneas side of `band_square` and `bor_square` is the
conditional that expresses this, and the right operand `b` may fail.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std

/-- Checked unsigned addition returns, when it succeeds, the sum the runtime computes. -/
theorem add_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (x + y) (pure (Hax.add (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  have := UScalar.add_equiv x y
  rw [h] at this
  simp [Hax.add, this.2.1]

/-- Checked signed addition returns, when it succeeds, the sum the runtime computes. -/
theorem add_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (x + y) (pure (Hax.add (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  have := IScalar.add_equiv x y
  rw [h] at this
  simp [Hax.add, this.2.1]

/-- Checked unsigned subtraction returns, when it succeeds, the difference the
    runtime computes. -/
theorem sub_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (x - y) (pure (Hax.sub (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  have := UScalar.sub_equiv x y
  rw [h] at this
  simp [Hax.sub]
  omega

/-- Checked signed subtraction returns, when it succeeds, the difference the
    runtime computes. -/
theorem sub_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (x - y) (pure (Hax.sub (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  have := IScalar.sub_equiv x y
  rw [h] at this
  simp [Hax.sub, this.2.1]

/-- Checked unsigned multiplication returns, when it succeeds, the product the
    runtime computes. -/
theorem mul_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (x * y) (pure (Hax.mul (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  have := UScalar.mul_equiv x y
  change x.mul y = _ at h
  rw [h] at this
  simp [Hax.mul, this.2.1]

/-- Checked signed multiplication returns, when it succeeds, the product the
    runtime computes. -/
theorem mul_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (x * y) (pure (Hax.mul (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  have := IScalar.mul_equiv x y
  change x.mul y = _ at h
  rw [h] at this
  simp [Hax.mul, this.2.2.1]

/-- Unsigned division returns, when the divisor is nonzero, the quotient the
    runtime computes. -/
theorem div_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (x / y) (pure (Hax.div (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  simp only [HDiv.hDiv, UScalar.div] at h
  split at h
  · cases h
    show ((BitVec.udiv x.bv y.bv).toNat : Int) = (x.bv.toNat : Int) / (y.bv.toNat : Int)
    rw [BitVec.udiv_eq, BitVec.toNat_udiv, Int.natCast_ediv]
  · cases h

/-- Signed division is not related to the runtime division: `-7 / 2` is `-3` in
    Aeneas and `-4` in the runtime. -/
theorem div_i_counterexample :
    ¬ RCompOk EncRel ((-7)#i8 / 2#i8) (pure (Hax.div (enc (-7)#i8) (enc 2#i8)) : Id Int) := by
  refine not_rcompOk_of ⟨BitVec.sdiv ((-7)#i8).bv (2#i8).bv⟩ ?_ ?_
  · show IScalar.div _ _ = _
    unfold IScalar.div
    rw [ite_eq_left (by decide +kernel), ite_eq_left (by decide +kernel)]
  · show ¬ (_ : Int) = _
    decide +kernel

/-- Unsigned remainder returns, when the divisor is nonzero, the remainder the
    runtime computes. -/
theorem rem_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (x % y) (pure (Hax.rem (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  simp only [HMod.hMod, UScalar.rem] at h
  split at h
  · cases h
    show ((BitVec.umod x.bv y.bv).toNat : Int) = (x.bv.toNat : Int) % (y.bv.toNat : Int)
    rw [BitVec.umod_eq, BitVec.toNat_umod, Int.natCast_emod]
  · cases h

/-- Signed remainder is not related to the runtime remainder: `-7 % 2` is `-1` in
    Aeneas and `1` in the runtime. -/
theorem rem_i_counterexample :
    ¬ RCompOk EncRel ((-7)#i8 % 2#i8) (pure (Hax.rem (enc (-7)#i8) (enc 2#i8)) : Id Int) := by
  refine not_rcompOk_of ⟨BitVec.srem ((-7)#i8).bv (2#i8).bv⟩ ?_ ?_
  · show IScalar.rem _ _ = _
    unfold IScalar.rem
    rw [ite_eq_left (by decide +kernel), ite_eq_left (by decide +kernel)]
  · show ¬ (_ : Int) = _
    decide +kernel

/-- Unsigned `<` agrees with the runtime `Hax.lt`. -/
theorem lt_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (decide (x < y))) (pure (Hax.lt (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.lt]

/-- Signed `<` agrees with the runtime `Hax.lt`. -/
theorem lt_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (decide (x < y))) (pure (Hax.lt (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.lt]

/-- Unsigned `≤` agrees with the runtime `Hax.le`. -/
theorem le_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (decide (x ≤ y))) (pure (Hax.le (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.le]

/-- Signed `≤` agrees with the runtime `Hax.le`. -/
theorem le_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (decide (x ≤ y))) (pure (Hax.le (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.le]

/-- Unsigned `>` agrees with the runtime `Hax.gt`. -/
theorem gt_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (decide (x > y))) (pure (Hax.gt (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.gt]

/-- Signed `>` agrees with the runtime `Hax.gt`. -/
theorem gt_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (decide (x > y))) (pure (Hax.gt (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.gt]

/-- Unsigned `≥` agrees with the runtime `Hax.ge`. -/
theorem ge_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (decide (x ≥ y))) (pure (Hax.ge (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.ge]

/-- Signed `≥` agrees with the runtime `Hax.ge`. -/
theorem ge_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (decide (x ≥ y))) (pure (Hax.ge (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift]
  simp [Hax.ge]

/-- Unsigned `==` agrees with the runtime `Hax.beq`. -/
theorem beq_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x == y)) (pure (Hax.beq (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift, encRel_iff, enc_bool, Hax.beq, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq]
  exact decide_eq_decide.mpr enc_uscalar_inj.symm

/-- Signed `==` agrees with the runtime `Hax.beq`. -/
theorem beq_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (x == y)) (pure (Hax.beq (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift, encRel_iff, enc_bool, Hax.beq, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq]
  exact decide_eq_decide.mpr enc_iscalar_inj.symm

/-- Unsigned `!=` agrees with the runtime `Hax.bne`. -/
theorem bne_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x != y)) (pure (Hax.bne (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift, encRel_iff, enc_bool, Hax.bne, bne, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq]
  exact congrArg (!·) (decide_eq_decide.mpr enc_uscalar_inj.symm)

/-- Signed `!=` agrees with the runtime `Hax.bne`. -/
theorem bne_i_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (x != y)) (pure (Hax.bne (enc x) (enc y)) : Id Bool) := by
  rw [rcompOk_lift, encRel_iff, enc_bool, Hax.bne, bne, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq]
  exact congrArg (!·) (decide_eq_decide.mpr enc_iscalar_inj.symm)

/-- Rust's `a && b` (the right operand evaluated only when `a` holds) agrees with
    the runtime `Hax.band` whenever the right operands are related. -/
theorem band_square (a : Bool) {b : RustM Bool} {b' : Bool}
    (hb : RCompOk EncRel b (pure b' : Id Bool)) :
    RCompOk EncRel (if a then b else RustM.ok false) (pure (Hax.band (enc a) b') : Id Bool) := by
  cases a
  · exact rcompOk_ok.mpr rfl
  · exact hb

/-- Rust's `a || b` (the right operand evaluated only when `a` fails) agrees with
    the runtime `Hax.bor` whenever the right operands are related. -/
theorem bor_square (a : Bool) {b : RustM Bool} {b' : Bool}
    (hb : RCompOk EncRel b (pure b' : Id Bool)) :
    RCompOk EncRel (if a then RustM.ok true else b) (pure (Hax.bor (enc a) b') : Id Bool) := by
  cases a
  · exact hb
  · exact rcompOk_ok.mpr rfl

/-- Boolean negation agrees with the runtime `Hax.Not` on `Bool`. -/
theorem not_bool_square (a : Bool) :
    RCompOk EncRel (lift (!a)) (pure (Hax.Not (enc a)) : Id Bool) :=
  rcompOk_lift.mpr rfl

/-- The complement of a signed scalar agrees with the runtime `Hax.Not` on `Int`,
    `-(x + 1)`. -/
theorem not_i_square {ty : IScalarTy} (x : IScalar ty) :
    RCompOk EncRel (lift (~~~x)) (pure (Hax.Not (enc x)) : Id Int) := by
  rw [rcompOk_lift]
  show (~~~x.bv).toInt = -(x.bv.toInt + 1)
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_bmod]
  have hn := x.bv.isLt
  have hw := ty.numBits_nonzero
  have hm2 : 2 ^ ty.numBits % 2 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, ty.numBits = k + 1 := ⟨ty.numBits - 1, by omega⟩
    rw [hk, Nat.pow_succ]; simp
  rw [show (2 : Int) ^ ty.numBits = ((2 ^ ty.numBits : Nat) : Int) by push_cast; rfl]
  generalize x.bv.toNat = n at *
  generalize 2 ^ ty.numBits = m at *
  simp only [Int.bmod]
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)]
  split <;> split <;> omega

/-- The complement of an unsigned scalar is not related to the runtime `Hax.Not`:
    `!5u8` is `250` in Aeneas and `-6` in the runtime. -/
theorem not_u_counterexample :
    ¬ RCompOk EncRel (lift (~~~5#u8)) (pure (Hax.Not (enc 5#u8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- `None` is encoded as `none`. -/
theorem none_square {α β : Type} [Encode α β] :
    RCompOk EncRel (RustM.ok (none : Option α)) (pure (none : Option β) : Id (Option β)) :=
  rcompOk_ok.mpr rfl

/-- `Some a` is encoded as `some (enc a)`. -/
theorem some_square {α β : Type} [Encode α β] (a : α) :
    RCompOk EncRel (RustM.ok (some a)) (pure (some (enc a)) : Id (Option β)) :=
  rcompOk_ok.mpr rfl

end CatCrypt.Hax.RustSemantics
