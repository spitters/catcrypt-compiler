/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.SExprOrNot

/-!
# Bitwise OR and NOT value leaves — derived over the `SXor`/`SAnd` fragment

`ExprLeaf.lean`'s `corres_setExprBitwise` covers the `SXor`/`SAnd`/`SShl`/`SShr`
fragment of `SExpr`, keeping the clean spec in the `BitVec 64` word algebra
(`IsWordClean`, `SRwordBV`). The `SExpr` datatype (`Jasmin/LowCT.lean`) has **no**
`SOr`/`SNot` arms — the two missing bitwise operations Keccak's `χ = a ^ (¬b & c)`
and the rotate leaf's `|||`-join need. `SExprOrNot` expresses both over the covered
fragment, so each lands as a `corres_setExpr*` value leaf that reuses
`corres_setExprBitwise`:

* **NOT** — `~~~x = x ^^^ allOnes`, the all-ones xor, an `SXor` node with an
  `SLit (2^64-1)` operand (`sNotExpr`).
* **OR** — De Morgan `x ||| y = ~~~(~~~x &&& ~~~y)`, an `SAnd` of two `sNotExpr`
  nodes under a third `sNotExpr` (`sOrExpr`).

Both derived shapes are `IsWordClean` whenever their operands are, and their
`SExpr.evalBV` word value is exactly `~~~` / `|||` — so the leaf transformer is
the clean bitwise operation with no `ZMod` abstraction, matching the arithmetic
vs. bitwise split of `ExprLeaf.lean`.

The Ascend port to Lean was begun by Sebastian Graf (`sgraf812/ascent`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## Word cleanliness of the derived expressions

`sNotExpr`, `sOrExpr` and their `evalBV` equations are in `SExprOrNot`. -/

/-- `sNotExpr` preserves `IsWordClean`: the added `SLit (2^64-1)` operand is a legal
    (`< 2^64`) word-clean literal. -/
theorem isWordClean_sNotExpr (e : SExpr) (he : IsWordClean e) :
    IsWordClean (sNotExpr e) :=
  ⟨he, Nat.sub_lt (by positivity) Nat.one_pos⟩

/-- `sOrExpr` preserves `IsWordClean` when both operands are. -/
theorem isWordClean_sOrExpr (a b : SExpr) (ha : IsWordClean a) (hb : IsWordClean b) :
    IsWordClean (sOrExpr a b) :=
  isWordClean_sNotExpr _ ⟨isWordClean_sNotExpr a ha, isWordClean_sNotExpr b hb⟩

/-! ## The derived value leaves -/

/-- `corres_setExprNot` — the bitwise NOT value leaf. From a concrete env
    `SRwordBV`-related to abstract `a`, the real `semScalar` runs the derived
    `RScalarSetExpr x (sNotExpr e)` (an all-ones xor, discharged by
    `corres_setExprBitwise`) to a state that sets `x` to `~~~ (SExpr.evalBV a e)`
    — the clean word complement — and leaves every other source name untouched. -/
theorem corres_setExprNot (x : String) (e : SExpr) (he : IsWordClean e) :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = x then ~~~ (SExpr.evalBV a e) else a s)
      (.RScalarSetExpr x (sNotExpr e)) := by
  have h := corres_setExprBitwise x (sNotExpr e) (isWordClean_sNotExpr e he)
  simp only [evalBV_sNotExpr] at h
  exact h

/-- `corres_setExprOr` — the bitwise OR value leaf. From a concrete env
    `SRwordBV`-related to abstract `a`, the real `semScalar` runs the derived
    De-Morgan `RScalarSetExpr x (sOrExpr e₁ e₂)` (discharged by
    `corres_setExprBitwise`) to a state that sets `x` to
    `SExpr.evalBV a e₁ ||| SExpr.evalBV a e₂` — the clean word disjunction — and
    leaves every other source name untouched. This is the value leaf the rotate
    leaf's `|||`-join and Keccak `χ` can call in place of an open-coded xor. -/
theorem corres_setExprOr (x : String) (e₁ e₂ : SExpr)
    (he₁ : IsWordClean e₁) (he₂ : IsWordClean e₂) :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = x then SExpr.evalBV a e₁ ||| SExpr.evalBV a e₂ else a s)
      (.RScalarSetExpr x (sOrExpr e₁ e₂)) := by
  have h := corres_setExprBitwise x (sOrExpr e₁ e₂) (isWordClean_sOrExpr e₁ e₂ he₁ he₂)
  simp only [evalBV_sOrExpr] at h
  exact h

/-! ## Concrete Keccak-`χ` closes natively over OR/NOT

Keccak `χ`'s `a ^ (¬b & c)` — with `¬b` now the derived `sNotExpr` rather than an
open-coded all-ones xor — closes through the OR/NOT leaves, as does a bare
`a ||| b` disjoint join. -/

/-- A bitwise NOT `x := ~~~ d` closes through the derived NOT leaf. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "x" then ~~~ (SExpr.evalBV a (.SVar "d")) else a s)
      (.RScalarSetExpr "x" (sNotExpr (.SVar "d"))) :=
  corres_setExprNot "x" (.SVar "d") (notTmp_of_short "d" (by decide))

/-- A disjoint join `x := d ||| a` closes through the derived OR leaf. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "x" then
          SExpr.evalBV a (.SVar "d") ||| SExpr.evalBV a (.SVar "a") else a s)
      (.RScalarSetExpr "x" (sOrExpr (.SVar "d") (.SVar "a"))) :=
  corres_setExprOr "x" (.SVar "d") (.SVar "a")
    (notTmp_of_short "d" (by decide)) (notTmp_of_short "a" (by decide))

end CatCrypt.Crypto.SecureCompilation.Ascent
