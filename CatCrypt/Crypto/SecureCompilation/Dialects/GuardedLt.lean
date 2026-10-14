/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

/-!
# Unsigned less-than over the lowered scalar operations

`lowerSExpr` has no arm for `SLt`.  `ltExpr a b` computes the unsigned comparison
`a < b` of two words with the operations `lowerSExpr` lowers (`SSub`, `SShr`,
`SAdd`, `SMul`, `SAnd`, literals): it is the carry-out of the 64-bit sum
`b + (2^64 - 1 - a)`, which is `1` exactly when `a < b`.  The carry-out of
`u + v` is `((u >>> 1) + (v >>> 1) + (u &&& 1) * (v &&& 1)) >>> 63`, a sum that
does not wrap.

`elimLt` replaces every `SLt` node of an expression by `ltExpr`.  On the fragment
`ltClean` (`srcClean` extended with `SLt`) the result is `srcClean`, and on every
reader it has the word value of the original expression.

## Main definitions

* `ltExpr`: unsigned less-than over the lowered operations
* `elimLt`: `SLt` elimination
* `ltClean`: `srcClean` extended with `SLt`
* `varsIn`: every variable of an expression satisfies a predicate

## Main results

* `evalBV_ltExpr`: `ltExpr a b` evaluates to `1` when `a < b` and `0` otherwise
* `toNat_ltWord`: the same statement as `Nat.blt` on the operand values
* `evalBV_elimLt`: `elimLt` preserves the word value
* `srcClean_elimLt`: `elimLt` maps `ltClean` into `srcClean`
* `evalBV_congr_varsIn`: readers agreeing on the variables agree on the value
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt

open CatCrypt.Crypto.Jasmin.LowCT (SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## The comparison word -/

/-- The word `2^64 - 1`. -/
def wordMax : Nat := 2 ^ 64 - 1

/-- The carry-out of the 64-bit sum `u + v`, over the lowered operations. -/
def carryExpr (u v : SExpr) : SExpr :=
  .SShr (.SAdd (.SAdd (.SShr u (.SLit 1)) (.SShr v (.SLit 1)))
      (.SMul (.SAnd u (.SLit 1)) (.SAnd v (.SLit 1)))) (.SLit 63)

/-- Unsigned `a < b`: the carry-out of `b + (2^64 - 1 - a)`. -/
def ltExpr (a b : SExpr) : SExpr := carryExpr b (.SSub (.SLit wordMax) a)

/-- The word function `ltExpr` computes. -/
def ltWord (x y : BitVec 64) : BitVec 64 := if x.toNat < y.toNat then 1 else 0

/-- The carry-out formula: the word `carryExpr` computes is `1` exactly when the
    64-bit sum `y + w` overflows. -/
theorem carry_word (y w : BitVec 64) :
    ((y >>> 1) + (w >>> 1) + (y &&& 1#64) * (w &&& 1#64)) >>> 63
      = if 2 ^ 64 ≤ y.toNat + w.toNat then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hy := y.isLt
  have hw := w.isLt
  have h1 : (y &&& 1#64).toNat = y.toNat % 2 := by
    rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
  have h2 : (w &&& 1#64).toNat = w.toNat % 2 := by
    rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, h1, h2,
    BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one y.toNat with hp | hp <;>
  rcases Nat.mod_two_eq_zero_or_one w.toNat with hq | hq <;>
  simp only [hp, hq] <;> split_ifs <;> simp <;> omega

/-- `ltExpr a b` evaluates to `ltWord` of the operand values. -/
theorem evalBV_ltExpr (β : String → BitVec 64) (a b : SExpr) :
    (ltExpr a b).evalBV β = ltWord (a.evalBV β) (b.evalBV β) := by
  simp only [ltExpr, carryExpr, SExpr.evalBV]
  have h1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have h63 : (BitVec.ofNat 64 63).toNat = 63 := rfl
  rw [h1, h63]
  rw [VIR.shiftMask_of_lt (by decide : 1 < 64), VIR.shiftMask_of_lt (by decide : 63 < 64),
    carry_word]
  have hx := (a.evalBV β).isLt
  have hsub : (BitVec.ofNat 64 wordMax - a.evalBV β).toNat = wordMax - (a.evalBV β).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have hm : wordMax % 2 ^ 64 = wordMax := by decide
    rw [hm]
    have hw : wordMax = 2 ^ 64 - 1 := rfl
    omega
  rw [hsub, ltWord]
  have hw : wordMax = 2 ^ 64 - 1 := rfl
  split_ifs <;> first | rfl | omega

/-- `ltWord` is `Nat.blt` on the operand values: its value is `1` when
    `Nat.blt x.toNat y.toNat` holds and `0` otherwise. -/
theorem toNat_ltWord (x y : BitVec 64) :
    (ltWord x y).toNat = if Nat.blt x.toNat y.toNat then 1 else 0 := by
  simp only [ltWord, Nat.blt_eq]
  split_ifs <;> rfl

/-- On in-range operands `ltWord` is the image of the `Nat` comparison. -/
theorem ltWord_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ltWord (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  simp only [ltWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  split_ifs <;> rfl

/-! ## `SLt` elimination -/

/-- Replace every `SLt` node by `ltExpr`. -/
def elimLt : SExpr → SExpr
  | .SAdd a b => .SAdd (elimLt a) (elimLt b)
  | .SSub a b => .SSub (elimLt a) (elimLt b)
  | .SMul a b => .SMul (elimLt a) (elimLt b)
  | .SAnd a b => .SAnd (elimLt a) (elimLt b)
  | .SXor a b => .SXor (elimLt a) (elimLt b)
  | .SShl a b => .SShl (elimLt a) (elimLt b)
  | .SShr a b => .SShr (elimLt a) (elimLt b)
  | .SMulHiU a b => .SMulHiU (elimLt a) (elimLt b)
  | .SLt a b => ltExpr (elimLt a) (elimLt b)
  | e => e

/-- `srcClean` extended with `SLt`. -/
def ltClean : SExpr → Prop
  | .SVar x => ¬ isTmpName x
  | .SLit n => n < 2 ^ 64
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b | .SLt a b => ltClean a ∧ ltClean b
  | _ => False

/-- Every variable of the expression satisfies `P`. -/
def varsIn (P : String → Prop) : SExpr → Prop
  | .SVar x => P x
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b | .SLt a b => varsIn P a ∧ varsIn P b
  | _ => True

/-- `elimLt` preserves the word value. -/
theorem evalBV_elimLt (β : String → BitVec 64) :
    ∀ e : SExpr, (elimLt e).evalBV β = e.evalBV β := by
  intro e
  induction e with
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      simp only [elimLt, SExpr.evalBV, iha, ihb]
  | SLt a b iha ihb =>
      simp only [elimLt, evalBV_ltExpr, iha, ihb, ltWord, SExpr.evalBV]
  | _ => rfl

/-- `elimLt` maps `ltClean` into `srcClean`. -/
theorem srcClean_elimLt : ∀ e : SExpr, ltClean e → srcClean (elimLt e) := by
  intro e
  induction e with
  | SVar x => intro h; exact h
  | SLit n => intro h; exact h
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro h; exact ⟨iha h.1, ihb h.2⟩
  | SLt a b iha ihb =>
      intro h
      have ha := iha h.1
      have hb := ihb h.2
      simp only [elimLt, ltExpr, carryExpr, srcClean]
      exact ⟨⟨⟨⟨hb, by decide⟩, ⟨⟨by decide, ha⟩, by decide⟩⟩,
        ⟨⟨hb, by decide⟩, ⟨⟨by decide, ha⟩, by decide⟩⟩⟩, by decide⟩
  | _ => intro h; exact h.elim

/-- `varsIn` is monotone in the predicate. -/
theorem varsIn_mono {P Q : String → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ e : SExpr, varsIn P e → varsIn Q e := by
  intro e
  induction e with
  | SVar x => exact hPQ x
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb
  | SLt a b iha ihb =>
      intro h; exact ⟨iha h.1, ihb h.2⟩
  | _ => intro _; trivial

/-- Readers agreeing on the variables of an `ltClean` expression agree on its
    word value. -/
theorem evalBV_congr_varsIn (P : String → Prop) (β₁ β₂ : String → BitVec 64)
    (hβ : ∀ s, P s → β₁ s = β₂ s) :
    ∀ e : SExpr, ltClean e → varsIn P e → e.evalBV β₁ = e.evalBV β₂ := by
  intro e
  induction e with
  | SVar x => intro _ hv; exact hβ x hv
  | SLit n => intro _ _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb
  | SLt a b iha ihb =>
      intro hc hv
      simp only [SExpr.evalBV, iha hc.1 hv.1, ihb hc.2 hv.2]
  | _ => intro hc; exact hc.elim

end CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt
