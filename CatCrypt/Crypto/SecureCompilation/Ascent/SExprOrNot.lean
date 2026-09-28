/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTSExpr

/-!
# Bitwise NOT and OR as scalar expressions

`SExpr` has no `SOr` or `SNot` constructor.  Both operations are scalar
expressions over the `SXor`/`SAnd` fragment:

* NOT — `~~~x = x ^^^ (2^64 - 1)`, an `SXor` with an all-ones literal (`sNotExpr`);
* OR — De Morgan, `x ||| y = ~~~(~~~x &&& ~~~y)` (`sOrExpr`).

The ascent value leaves (`BitwiseOrNot`) and the hax front's word-operation
lowering (`HaxToLowCTWordOps`) both use these expressions and their `evalBV`
equations.

## Main results

* `sNotExpr`, `evalBV_sNotExpr` — the complement and its `u64` value.
* `sOrExpr`, `evalBV_sOrExpr` — the disjunction and its `u64` value.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT

/-- The literal `2^64 - 1` as a `BitVec 64` is all ones, so xoring a word with it
    complements the word. -/
theorem wNotXorAllOnes (w : BitVec 64) :
    w ^^^ BitVec.ofNat 64 (2 ^ 64 - 1) = ~~~ w := by
  have hall : BitVec.ofNat 64 (2 ^ 64 - 1) = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes,
      Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos 64) Nat.one_pos)]
  rw [hall]
  exact BitVec.xor_allOnes

/-- Bitwise NOT as an `SXor` with the all-ones literal: `~~~e = e ^^^ (2^64 - 1)`. -/
def sNotExpr (e : SExpr) : SExpr := .SXor e (.SLit (2 ^ 64 - 1))

/-- The `u64` value of `sNotExpr e` is the complement of the value of `e`. -/
theorem evalBV_sNotExpr (β : String → BitVec 64) (e : SExpr) :
    SExpr.evalBV β (sNotExpr e) = ~~~ (SExpr.evalBV β e) := by
  simp only [sNotExpr, SExpr.evalBV]
  exact wNotXorAllOnes (SExpr.evalBV β e)

/-- Bitwise OR by De Morgan: `a ||| b = ~~~(~~~a &&& ~~~b)`, an `SAnd` of two
    `sNotExpr` nodes under a third. -/
def sOrExpr (a b : SExpr) : SExpr := sNotExpr (.SAnd (sNotExpr a) (sNotExpr b))

/-- The `u64` value of `sOrExpr a b` is the disjunction of the values of `a` and
    `b`. -/
theorem evalBV_sOrExpr (β : String → BitVec 64) (a b : SExpr) :
    SExpr.evalBV β (sOrExpr a b) = SExpr.evalBV β a ||| SExpr.evalBV β b := by
  simp only [sOrExpr, evalBV_sNotExpr, SExpr.evalBV]
  rw [BitVec.not_and, BitVec.not_not, BitVec.not_not]

end CatCrypt.Crypto.SecureCompilation.Ascent
