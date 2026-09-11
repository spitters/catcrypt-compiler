/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import Std.Tactic.BVDecide

/-!
# Branchless field-reduction idioms over the scalar `regArith` alphabet

The `Com → RegProg` scalar front (`ScalarLinFront`) targets a flagless, branchless
alphabet: binary ALU (`add sub mul and or xor`), widening-high multiply, immediate
shifts, and materialised constants. A natural question for migrating real field
kernels is whether *modular reduction* — the conditional subtract `if x ≥ p then
x - p else x` — needs a new primitive (a comparison/`sltu`, or a flag-aware
`select`).

It does not. Unsigned comparison and the conditional subtract are **expressible and
machine-checked over exactly this alphabet**, using `sub`, `xor`, `and`, `or`, the
complement (`xor` with the all-ones constant) and a single immediate `>>> 63`. So a
field-reduction kernel is a straight-line `Com` over the existing ops — the compiler
needs no extension, and both backends (ARM, RISC-V) already lower every op.

These are the verified building blocks; a kernel author composes them as `Com`
bindings (each `bSltu`/`bCondSub` line is the obvious sequence of `regArith` ops).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms

/-- Branchless unsigned less-than as a `0/1` word: the borrow-out of `a - b` lives
    in the top bit of `(~a & b) | (~(a ^ b) & (a - b))`. -/
def bSltu (a b : BitVec 64) : BitVec 64 :=
  ((~~~a &&& b) ||| (~~~(a ^^^ b) &&& (a - b))) >>> 63

/-- `bSltu` realises the unsigned comparison `a <ᵤ b` (machine-checked). -/
theorem bSltu_eq (a b : BitVec 64) :
    bSltu a b = (if a.ult b then (1 : BitVec 64) else 0) := by
  unfold bSltu; bv_decide

/-- Branchless conditional subtract — the modular-reduction step for `x < 2p`:
    `if x ≥ p then x - p else x`, as a mask-select driven by `bSltu x p`. -/
def bCondSub (x p : BitVec 64) : BitVec 64 :=
  let mask := 0 - bSltu x p
  (x &&& mask) ||| ((x - p) &&& ~~~mask)

/-- `bCondSub` realises the conditional subtract (machine-checked). When `x < p`
    the mask is all-ones and the result is `x`; when `x ≥ p` it is `x - p`. -/
theorem bCondSub_eq (x p : BitVec 64) :
    bCondSub x p = (if x.ult p then x else x - p) := by
  unfold bCondSub bSltu; bv_decide

/-- For `x < 2p` (the post-addition range), the conditional subtract is exactly the
    reduction `x mod p` — the field-arithmetic correctness of `bCondSub`, reduced to
    a `Nat` fact about the represented values. -/
theorem bCondSub_toNat (x p : BitVec 64) (hp : 0 < p.toNat) (hx : x.toNat < 2 * p.toNat) :
    (bCondSub x p).toNat = x.toNat % p.toNat := by
  have hxlt := x.isLt
  have hplt := p.isLt
  rw [bCondSub_eq]
  by_cases h : x.toNat < p.toNat
  · rw [if_pos (by simp [BitVec.ult, h]), Nat.mod_eq_of_lt h]
  · have hpx : p.toNat ≤ x.toNat := Nat.le_of_not_lt h
    rw [if_neg (by simp only [BitVec.ult, decide_eq_true_eq]; omega),
        BitVec.toNat_sub_of_le hpx, Nat.mod_eq_sub_mod hpx,
        Nat.mod_eq_of_lt (show x.toNat - p.toNat < p.toNat by omega)]

/-- Branchless modular subtraction — add `p` back exactly when `a < b` borrows. -/
def bSubMod (a b p : BitVec 64) : BitVec 64 :=
  (a - b) + ((0 - bSltu a b) &&& p)

/-- `bSubMod` realises the conditional `if a < b then a - b + p else a - b`. -/
theorem bSubMod_eq (a b p : BitVec 64) :
    bSubMod a b p = (if a.ult b then a - b + p else a - b) := by
  unfold bSubMod bSltu; bv_decide

/-- **Field-arithmetic correctness.** For `a, b < p < 2^63` the modular subtract
    returns `(a + p - b) mod p` ( = `(a - b) mod p` in `ZMod p`). -/
theorem bSubMod_toNat (a b p : BitVec 64) (hp : 0 < p.toNat) (hp64 : p.toNat < 2 ^ 63)
    (ha : a.toNat < p.toNat) (hb : b.toNat < p.toNat) :
    (bSubMod a b p).toNat = (a.toNat + p.toNat - b.toNat) % p.toNat := by
  rw [bSubMod_eq]
  have hab := a.isLt; have hbb := b.isLt; have hpb := p.isLt
  by_cases h : a.toNat < b.toNat
  · rw [if_pos (by simp [BitVec.ult, h])]
    have e1 : (a - b).toNat = 2 ^ 64 - (b.toNat - a.toNat) := by rw [BitVec.toNat_sub]; omega
    rw [BitVec.toNat_add, e1,
        show (2 ^ 64 - (b.toNat - a.toNat) + p.toNat) % 2 ^ 64 = a.toNat + p.toNat - b.toNat from by
          omega,
        Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg (by simp only [BitVec.ult, decide_eq_true_eq]; omega)]
    have hba : b.toNat ≤ a.toNat := Nat.le_of_not_lt h
    rw [BitVec.toNat_sub_of_le hba,
        show a.toNat + p.toNat - b.toNat = (a.toNat - b.toNat) + p.toNat from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **Carry-chain building block** (multi-limb bignum). The truncated sum `a + b`
    together with the branchless carry-out `bSltu (a + b) a` recovers the full 65-bit
    sum — the limb-to-limb carry every multi-limb add propagates. -/
theorem addCarry_toNat (a b : BitVec 64) :
    (a + b).toNat + (bSltu (a + b) a).toNat * 2 ^ 64 = a.toNat + b.toNat := by
  rw [bSltu_eq]
  have ha := a.isLt; have hb := b.isLt
  have hadd : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add a b
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  have h0 : (0 : BitVec 64).toNat = 0 := by decide
  by_cases h : (a + b).ult a
  · rw [if_pos h, h1]
    have hlt : (a + b).toNat < a.toNat := by simpa [BitVec.ult] using h
    omega
  · rw [if_neg h, h0]
    have hge : ¬ (a + b).toNat < a.toNat := by simpa [BitVec.ult] using h
    omega

end CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
