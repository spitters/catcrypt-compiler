/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf

/-!
# The constant-time mask-select (branchless cmov) value leaf

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean`._

A crypto kernel is constant time, so the "conditional subtract" of a modular
reduce is not a data-dependent branch but a **branchless select** driven by a
mask word `m ∈ {0…0, 1…1}`:

```
  r := y ^^^ ((x ^^^ y) &&& m)
```

`CondKernelCapstone.lean` proved the *branch* abstraction (`corres_if`, the
`RIfNz` φ-merge). This module is the reusable *branchless* dual: it stays entirely
inside the `BitVec 64` word algebra — the mask select is a composition of `^^^`
and `&&&`, exactly the `IsWordClean` bitwise fragment `corres_setExprBitwise`
covers — so nothing here leaves the `SRwordBV` word relation for `ZMod`.

The genuine content is `ctSelect_bitmask`: the branchless formula equals the
per-bit multiplexer `(x &&& m) ||| (y &&& ~~~m)` **unconditionally**, and
`ctSelect_spec`: for a proper Boolean mask `m ∈ {0, allOnes}` the select is the
intended `if m = 0 then y else x`. The leaf `corres_ctSelect` runs the two-step
xor/and LowCT chain (`d := x ^^^ y`; `r := y ^^^ (d &&& m)`) through `corres_seq`
over the bitwise leaf, concluding the written slot `r` holds `ctSelect m x y`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## The mask select and its word-algebra spec -/

/-- The constant-time (branchless) select. With `cond` a mask word, `ctSelect cond
    x y = y ^^^ ((x ^^^ y) &&& cond)`: for each bit, the bit of `x` where the mask
    bit is set and the bit of `y` where it is clear. When the whole mask is `0…0`
    the result is `y`; when it is `1…1` the result is `x` — the branchless cmov a
    constant-time modular reduce uses instead of a data-dependent branch. -/
def ctSelect (cond x y : BitVec 64) : BitVec 64 :=
  y ^^^ ((x ^^^ y) &&& cond)

/-- **The genuine per-bit content.** The branchless mask formula equals the bitwise
    multiplexer `(x &&& cond) ||| (y &&& ~~~cond)` — for every bit, `x`'s bit where
    the mask is set and `y`'s bit where it is clear — with **no** hypothesis on the
    mask. This is the honest word-algebra characterization of the select. -/
theorem ctSelect_bitmask (cond x y : BitVec 64) :
    ctSelect cond x y = (x &&& cond) ||| (y &&& ~~~cond) := by
  unfold ctSelect
  bv_decide

/-- **The intended select for a Boolean mask.** For a proper mask `cond ∈ {0…0,
    1…1}` the branchless select equals the intended conditional move `if cond = 0
    then y else x`: an all-zero mask keeps `y`, an all-ones mask picks `x`. The
    mask hypothesis is exactly the constant-time discipline's invariant (the mask
    is materialized from a condition bit, never a raw datum). -/
theorem ctSelect_spec (cond x y : BitVec 64)
    (hcond : cond = 0 ∨ cond = BitVec.allOnes 64) :
    ctSelect cond x y = if cond = 0 then y else x := by
  rcases hcond with h | h
  · subst h; rw [if_pos rfl]; unfold ctSelect; bv_decide
  · subst h
    rw [if_neg (by bv_decide)]
    unfold ctSelect; bv_decide

/-! ## The LowCT mask-select chain and its bitwise leaf

The kernel's names — the mask `m`, the operands `x`/`y`, the delta temp `d`, the
result `r` — are all short (length `< 4`) source names, hence non-temp
(`notTmp_of_short`), so each `SVar` leaf is `IsWordClean`. -/

/-- Step 1 of the select chain: the delta `d := x ^^^ y`. -/
def ctSelectStep1 : LowCT :=
  .RScalarSetExpr "d" (.SXor (.SVar "x") (.SVar "y"))

/-- Step 2 of the select chain: the masked recombine `r := y ^^^ (d &&& m)`. -/
def ctSelectStep2 : LowCT :=
  .RScalarSetExpr "r" (.SXor (.SVar "y") (.SAnd (.SVar "d") (.SVar "m")))

/-- The full branchless mask-select LowCT: compute the delta, then recombine. -/
def ctSelectChain : LowCT :=
  .RSeq ctSelectStep1 ctSelectStep2

/-- The abstract post-state of the select chain: the delta slot `d` holds
    `x ^^^ y` and the result slot `r` holds `ctSelect m x y`; every other source
    name is untouched. -/
def ctSelectState (a : String → BitVec 64) : String → BitVec 64 :=
  fun s =>
    if s = "r" then ctSelect (a "m") (a "x") (a "y")
    else if s = "d" then a "x" ^^^ a "y"
    else a s

/-- `ctSelectStep1` is a bitwise value leaf: the delta assignment. -/
theorem corres_ctSelectStep1 :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "d" then SExpr.evalBV a (.SXor (.SVar "x") (.SVar "y")) else a s)
      ctSelectStep1 :=
  corres_setExprBitwise "d" _
    ⟨notTmp_of_short "x" (by decide), notTmp_of_short "y" (by decide)⟩

/-- `ctSelectStep2` is a bitwise value leaf: the masked recombine. -/
theorem corres_ctSelectStep2 :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "r" then
          SExpr.evalBV a (.SXor (.SVar "y") (.SAnd (.SVar "d") (.SVar "m"))) else a s)
      ctSelectStep2 :=
  corres_setExprBitwise "r" _
    ⟨notTmp_of_short "y" (by decide),
     ⟨notTmp_of_short "d" (by decide), notTmp_of_short "m" (by decide)⟩⟩

/-- **`corres_ctSelect` — the constant-time mask-select value leaf.** From a concrete
    env `SRwordBV`-related to abstract `a : String → BitVec 64`, running the two-step
    xor/and LowCT chain `ctSelectChain` under the real `semScalar` makes progress to
    an env related to `ctSelectState a`: the written result slot `r` holds
    `ctSelect (a "m") (a "x") (a "y")`, the delta slot `d` holds `a "x" ^^^ a "y"`,
    and every other source name is untouched. Built by `corres_seq` over the bitwise
    leaf `corres_setExprBitwise`; the spec stays in the `BitVec 64` word algebra. -/
theorem corres_ctSelect :
    Corres SRwordBV (fun _ => True) ctSelectState ctSelectChain := by
  have h :=
    corres_seq SRwordBV corres_ctSelectStep1 corres_ctSelectStep2 (fun _ _ => trivial)
  have hfun : (fun a =>
      (fun a s => if s = "r" then
          SExpr.evalBV a (.SXor (.SVar "y") (.SAnd (.SVar "d") (.SVar "m"))) else a s)
        ((fun a s => if s = "d" then SExpr.evalBV a (.SXor (.SVar "x") (.SVar "y"))
          else a s) a)) = ctSelectState := by
    funext a s
    by_cases hr : s = "r" <;> by_cases hd : s = "d" <;>
      simp [ctSelectState, ctSelect, SExpr.evalBV, hr, hd]
  rw [hfun] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.Ascent
