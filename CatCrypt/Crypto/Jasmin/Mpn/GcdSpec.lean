/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec
public import CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec
public meta import CatCrypt.Crypto.Jasmin.Mpn.SubPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.SubPrototype
public meta import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

@[expose] public section

set_option autoImplicit false

/-!
# VERIFIED REFERENCE + correctness contract for `mpn_gcd`

**EXPERIMENTAL FILE — Phase 3 spec foundation.**  This file establishes the
*verified mathematical reference* for the last genuinely-hard bounded-list GMP
primitive, the multi-precision GCD (`mpn_gcd`), together with the proof that the
limb-level reference computes exactly `Nat.gcd` at the `toNat` denotation level.

It does **not** implement the optimized binary/Lehmer GCD kernel that GMP ships.
The *Euclidean* reference here is the cleanest provably-correct GCD: it is the
limb-level transcription of the textbook `gcd a b = gcd b (a mod b)` recursion,
where `a mod b` is the **verified** Euclidean remainder produced by the committed
`mpnDivRem` (`MpnDivRemSpec`).  The fast (binary / GMP-Lehmer) kernel is a later
*verify-against-this-spec* step: it would refine the same contract,
`toNat (mpnGcd a b) = Nat.gcd (toNat a) (toNat b)`, proved here.

## Design

`mpnGcd a b` recurses Euclid-style on the limb lists:

```
mpnGcd a b = if toNat b = 0 then a
             else mpnGcd b ((mpnDivRem a b).2)   -- the remainder a mod b
```

The recursion is **well-founded on `toNat b`** (a `Nat` measure, not the limb
list length, which need not shrink).  The decreasing step is *exactly* the second
conjunct of `mpnDivRem_spec`: `toNat (mpnDivRem a b).2 < toNat b`.  So GMP's
"GCD always terminates" is here a one-line consequence of the verified division
contract.

The value follows from `Nat.gcd`'s own recursion.  We do **not** introduce a new
`Nat`-level GCD algorithm: the spec is reduced to Mathlib/core's `Nat.gcd` via
`Nat.gcd_rec` + `Nat.gcd_comm`, so `mpnGcd` is proved to denote the standard
`Nat.gcd`, not some bespoke definition.

## Normalization / leading zeros

The little-endian denotation `toNat` (reused from `MpnAddPrototype`) is
**insensitive to leading-zero limbs** (`toNat [3,0,0] = toNat [3] = 3`), so the
spec `toNat (mpnGcd a b) = Nat.gcd (toNat a) (toNat b)` is well-defined *without*
any explicit normalization pass: the base case returns `a` verbatim and its
denotation is already `toNat a = Nat.gcd (toNat a) 0`.  No `normalize` wrapper is
needed for *correctness*; a normalization (strip trailing zero limbs) would only
matter for a *canonical-length output* contract, which is an emission concern,
not a value concern.  We note this explicitly because the task brief suggested a
`normalize a` base case — for the `toNat`-level spec it is provably unnecessary.

## What is proved here (axiom-clean)

1. `mpnGcd` : the limb-list Euclidean GCD, well-founded on the `Nat` measure
   `toNat b`, terminating via `mpnDivRem_spec`.
2. **`mpnGcd_spec`** : `toNat (mpnGcd a b) = Nat.gcd (toNat a) (toNat b)`, by the
   functional-induction principle `mpnGcd.induct`, reducing the step case to
   `Nat.gcd_rec`/`Nat.gcd_comm` and the remainder value from `mpnDivRem_quot_rem`.
3. Corollaries: `mpnGcd_comm_value` (the denotation is symmetric, via
   `Nat.gcd_comm`) and concrete `native_decide` sanity checks.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.GcdSpec

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (toNat)
open CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec (mpnDivRem mpnDivRem_spec mpnDivRem_quot_rem)

/-! ## §1  The limb-list Euclidean GCD reference -/

/-- **The limb-list Euclidean GCD reference.**  `mpnGcd a b` computes the GCD of
    the little-endian limb lists `a`, `b` by the textbook Euclid recursion, using
    the verified Euclidean remainder `(mpnDivRem a b).2 = a mod b`.

    Termination is well-founded on the `Nat` measure `toNat b`: the recursive call
    replaces `b` by the remainder `(mpnDivRem a b).2`, whose denotation is strictly
    smaller (`mpnDivRem_spec`'s second conjunct, valid since `toNat b ≠ 0`).  The
    base case `toNat b = 0` returns `a` unchanged. -/
def mpnGcd (a b : List (BitVec 64)) : List (BitVec 64) :=
  if h : toNat b = 0 then a
  else mpnGcd b (mpnDivRem a b).2
termination_by toNat b
decreasing_by exact (mpnDivRem_spec a b h).2

/-! ## §2  The correctness contract — denotes `Nat.gcd` -/

/-- **The GCD correctness contract for `mpnGcd`.**  The limb-list reference denotes
    exactly `Nat.gcd` at the `toNat` level:

    `toNat (mpnGcd a b) = Nat.gcd (toNat a) (toNat b)`.

    This is **the specification any optimized (binary / GMP-Lehmer) GCD kernel must
    refine.**  Proof by the functional-induction principle `mpnGcd.induct`:
    * base (`toNat b = 0`): `mpnGcd a b = a`, and `Nat.gcd (toNat a) 0 = toNat a`
      (`Nat.gcd_zero_right`);
    * step (`toNat b ≠ 0`): `mpnGcd a b = mpnGcd b (a mod b)`, the IH gives
      `toNat (mpnGcd b (a mod b)) = Nat.gcd (toNat b) (toNat a % toNat b)`
      (using `(mpnDivRem a b).2 = a mod b`, `mpnDivRem_quot_rem`), and
      `Nat.gcd_comm`/`Nat.gcd_rec` align this with `Nat.gcd (toNat a) (toNat b)`. -/
theorem mpnGcd_spec (a b : List (BitVec 64)) :
    toNat (mpnGcd a b) = Nat.gcd (toNat a) (toNat b) := by
  induction a, b using mpnGcd.induct with
  | case1 a b h =>
    -- base case: toNat b = 0 (simp rewrites `toNat b → 0` everywhere via `h`)
    rw [mpnGcd]
    simp only [h, dif_pos]
    rw [Nat.gcd_zero_right]
  | case2 a b h ih =>
    -- step case: toNat b ≠ 0, ih : toNat (mpnGcd b (mpnDivRem a b).2) = gcd …
    rw [mpnGcd]
    simp only [h, dif_neg, not_false_iff]
    rw [ih, (mpnDivRem_quot_rem a b h).2]
    -- goal: Nat.gcd (toNat b) (toNat a % toNat b) = Nat.gcd (toNat a) (toNat b)
    rw [Nat.gcd_comm (toNat a) (toNat b), Nat.gcd_rec (toNat b) (toNat a),
      Nat.gcd_comm (toNat b) (toNat a % toNat b)]

/-- The GCD denotation is symmetric in its limb-list arguments — a direct
    corollary of `mpnGcd_spec` and `Nat.gcd_comm`.  (Note: `mpnGcd a b` and
    `mpnGcd b a` need not be *equal as limb lists*, but they have equal
    denotation.) -/
theorem mpnGcd_comm_value (a b : List (BitVec 64)) :
    toNat (mpnGcd a b) = toNat (mpnGcd b a) := by
  rw [mpnGcd_spec, mpnGcd_spec, Nat.gcd_comm]

/-! ## §3  Concrete sanity checks (decidable `#eval` / `native_decide`) -/

/-- `gcd 12 8 = 4` on single limbs. -/
example : toNat (mpnGcd [12] [8]) = 4 := by native_decide

/-- `gcd 100 60 = 20` on single limbs. -/
example : toNat (mpnGcd [100] [60]) = 20 := by native_decide

/-- Coprime: `gcd 17 5 = 1`. -/
example : toNat (mpnGcd [17] [5]) = 1 := by native_decide

/-- `gcd a 0 = a` (base case returns `a` verbatim; denotation is `toNat a`). -/
example : toNat (mpnGcd [42] [0]) = 42 := by native_decide

/-- Two-limb operand: `gcd (2^64 + 4) 6`.  `toNat [4,1] = 4 + 2^64`,
    `(2^64 + 4) = 18446744073709551620 = 2^2 · 5 · ...`; check it equals
    `Nat.gcd (4 + 2^64) 6` directly. -/
example : toNat (mpnGcd [4, 1] [6]) = Nat.gcd (4 + 2 ^ 64) 6 := by native_decide

/-! ## §4  Jasmin-bridge feasibility — STRUCTURAL PLAN (not implemented)

This reference is the *spec target*; the optimized emitted kernel is a later
phase.  Two orthogonal pieces remain for the Jasmin emission.

### §4.1  What the emission needs beyond the algebra proved here

* **The outer Euclid loop.**  The Lean reference is structured as well-founded
  recursion on `toNat b`; the emitted Jasmin is a `while (toNat b != 0)` loop
  (or the GMP binary/Lehmer variant).  The loop-to-recursion bridge is the same
  obligation already discharged for the per-limb carry/borrow walks (`mpnAddN`,
  `mpnSubN`): a loop invariant `toNat (gcd-so-far) = Nat.gcd (toNat a₀) (toNat b₀)`
  preserved by each iteration, with the well-founded measure `toNat b` providing
  the loop's termination certificate (no `decreasing_by` analogue exists at the
  Jasmin level, so termination must be re-established as a ranking function).

* **The division intrinsic per iteration.**  Each loop body needs a full
  `mpnDivRem` (Knuth Algorithm D) — the q-hat-estimate kernel whose emission is
  itself the open obligation tracked in `MpnDivRemSpec` §5 (normalization shift,
  per-digit window invariant `longDivBits_spec`, multiply-subtract via
  `mpn_submul_1`, and the load-bearing q-hat 2-step correction, Knuth Thm B).
  The GCD emission therefore *depends on* the division emission; the algebra in
  this file is independent of it and reduces against the `mpnDivRem_spec`
  contract regardless of which division kernel implements it.

### §4.2  Reuse summary

| GCD piece                          | Lean status / reuse                                       |
|------------------------------------|-----------------------------------------------------------|
| Euclid recursion `gcd a b = gcd b (a mod b)` | **proved** here as `mpnGcd_spec` (denotes `Nat.gcd`) |
| termination (`toNat b` decreases)  | **proved** here via `mpnDivRem_spec`.2 (well-founded)     |
| remainder `a mod b`                | `mpnDivRem` — Euclidean contract **proved** (`MpnDivRemSpec`) |
| outer `while` loop emission        | loop-invariant bridge, sibling of `mpnAddN`/`mpnSubN` walks; **NEW** ranking-function termination |
| per-iteration division emission    | Knuth-D kernel — open obligation (`MpnDivRemSpec` §5)     |

The algebra (recursion correctness + termination) is fully closed here against
the verified division contract; only the *emission* of the outer loop and the
division intrinsic remain, both reusing existing limb-walk plumbing plus the one
load-bearing q-hat correction already scoped in `MpnDivRemSpec` §5.2. -/

end CatCrypt.Crypto.Jasmin.Mpn.GcdSpec
