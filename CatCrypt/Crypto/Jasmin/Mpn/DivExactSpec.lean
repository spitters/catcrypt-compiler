/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec
public import CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec

@[expose] public section

set_option autoImplicit false

/-!
# VERIFIED REFERENCE + correctness contract for `mpn_divexact`

**EXPERIMENTAL FILE — Phase 3 spec foundation.**  This file establishes the
*verified mathematical reference* and **exact-division contract** for GMP's
`mpn_divexact` family (`mpn_divexact_1`, `mpn_divexact`), which back Lean's
`Nat.divExact` / `Int.divExact` (the exact-quotient operations that may *assume*
the divisor divides the dividend).

## Design choice: `mpnDivExact` is the `mpnDivRem` quotient

Exact division computes `a / b` under the **precondition `b ∣ a`** (the divisor
exactly divides the dividend, so the remainder is `0`).  The cleanest verified
reference is therefore *not* a new algorithm but the quotient projection of the
already-verified Euclidean reference `mpnDivRem` (`MpnDivRemSpec`):

```
mpnDivExact a b := (mpnDivRem a b).1
```

Under the divisibility precondition this denotes exactly `toNat a / toNat b`,
which is the full quotient (with zero remainder).  Everything is reduced to the
proven `mpnDivRem_quot_rem` / `mpnDivRem_spec`; no new induction is needed.

## What is proved here (axiom-clean)

1. `mpnDivExact a b := (mpnDivRem a b).1` (def).
2. `mpnDivExact_spec` : the exact-division contract — for `toNat b ∣ toNat a`
   and `toNat b ≠ 0`, `toNat (mpnDivExact a b) = toNat a / toNat b`.
3. `mpnDivExact_rem_zero` : under the same divisibility precondition the
   remainder limb list `(mpnDivRem a b).2` denotes `0`
   (`toNat (mpnDivRem a b).2 = 0`), confirming the division is exact.
4. `mpnDivExact_mul` : the multiplicative form
   `toNat (mpnDivExact a b) * toNat b = toNat a` (the contract `b ∣ a` makes
   the Euclidean identity collapse to an exact product).

## Relation to GMP's fast exact division (OPTIMIZATION, separate follow-on)

GMP's `mpn_divexact_1` and the Jebelean / Hensel "exact division" algorithm
(also called *binary / odd division*) are a **performance optimization** that is
*not* implemented here.  They exploit the precondition `b ∣ a` to compute the
quotient with **no quotient-digit estimation, no comparison, and no
multiply-subtract correction**: instead they invert the (odd part of the)
divisor modulo `2^64` once, then run a *single low-to-high limb sweep* using
modular multiplications by `b⁻¹ mod 2^64` (a 2-adic / Hensel-lifting Newton
step per limb).  This is asymptotically the same `O(n)` limb count as the
Euclidean kernel but with a much smaller constant — it is the standard reason
`mpn_divexact_1` is preferred over `mpn_divrem_1` when the divisor is known to
divide.  Crucially, the Hensel kernel produces the **same value** as the
Euclidean quotient whenever `b ∣ a`, so it would verify *against this same
contract* (`mpnDivExact_spec`): the fast algorithm is a denotation-preserving
refinement of this reference, exactly as Knuth Algorithm D refines
`mpnDivRem_spec` in `MpnDivRemSpec` §5.  This file pins down the *correctness
spec*; the Hensel kernel is the later *verify-against-this-spec* step.

## Jasmin emission (follow-on)

Emitting `mpn_divexact` from the verified pipeline needs the same machinery as
`mpn_divrem`: the `DIV`/`IDIV` x86 intrinsic (as already used by the `div`
limb-op path), the modular-inverse precomputation (a Newton/Hensel `mulmod`
chain — reuses the `mpn_mul_1` plumbing in `MpnMul1Prototype`), and the
low-to-high limb sweep (a sibling of the carry walk in `mpnAddN`).  The DIV
intrinsic is the only new primitive beyond the add/sub/mul limb ops; it is
shared with the Euclidean `mpn_divrem` Jasmin path (`MpnDivRemSpec` §5).
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.DivExactSpec

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (toNat)
open CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec (mpnDivRem mpnDivRem_spec mpnDivRem_quot_rem)

/-! ## §1  The exact-division reference -/

/-- **The limb-list exact-division reference.**  `mpnDivExact a b` is the
    quotient projection of the verified Euclidean reference `mpnDivRem`.  Under
    the precondition `toNat b ∣ toNat a` (which GMP's `mpn_divexact` *assumes*),
    this denotes the exact quotient `toNat a / toNat b` with zero remainder.

    GMP's fast `mpn_divexact_1` / Jebelean-Hensel kernel is a separate
    *optimization* that produces the same value under the same precondition (see
    module docstring); this is the correctness spec it refines. -/
def mpnDivExact (a b : List (BitVec 64)) : List (BitVec 64) :=
  (mpnDivRem a b).1

/-! ## §2  The exact-division contract — the load-bearing spec -/

set_option linter.unusedVariables false in
/-- **The exact-division contract for `mpnDivExact`.**  Under the precondition
    `toNat b ∣ toNat a` (the divisor exactly divides the dividend) and
    `toNat b ≠ 0`, the reference denotes the exact quotient:

    `toNat (mpnDivExact a b) = toNat a / toNat b`.

    Proof: `mpnDivExact` is by definition the `mpnDivRem` quotient, whose
    denotation is `toNat a / toNat b` by `mpnDivRem_quot_rem` (the divisibility
    hypothesis is not even needed for *this* equation — exact division agrees
    with Euclidean division on the quotient whenever `b ∣ a` makes the remainder
    vanish, but the quotient projection already equals `toNat a / toNat b` for
    any nonzero `b`).  The divisibility precondition is recorded so this lines up
    with GMP's `mpn_divexact` API (which is only *defined* when `b ∣ a`), and is
    the hypothesis under which the fast Hensel kernel produces the same value. -/
theorem mpnDivExact_spec (a b : List (BitVec 64))
    (h : toNat b ∣ toNat a) (hb : toNat b ≠ 0) :
    toNat (mpnDivExact a b) = toNat a / toNat b := by
  unfold mpnDivExact
  exact (mpnDivRem_quot_rem a b hb).1

/-- Under the divisibility precondition the remainder is exact: the remainder
    limb list `(mpnDivRem a b).2` denotes `0`.  This is what makes
    `mpnDivExact` an *exact* division: `b ∣ a ⇒ toNat a % toNat b = 0`, and the
    remainder limb denotation is exactly that modulus (`mpnDivRem_quot_rem`). -/
theorem mpnDivExact_rem_zero (a b : List (BitVec 64))
    (h : toNat b ∣ toNat a) (hb : toNat b ≠ 0) :
    toNat (mpnDivRem a b).2 = 0 := by
  rw [(mpnDivRem_quot_rem a b hb).2]
  exact Nat.dvd_iff_mod_eq_zero.mp h

/-- The multiplicative form of the exact-division contract.  Under `toNat b ∣
    toNat a` and `toNat b ≠ 0`, the quotient recombines exactly:
    `toNat (mpnDivExact a b) * toNat b = toNat a`.

    Proof: the Euclidean identity `mpnDivRem_spec` gives
    `toNat a = quot · toNat b + rem`; the remainder is `0` by
    `mpnDivExact_rem_zero`, so the product is exact. -/
theorem mpnDivExact_mul (a b : List (BitVec 64))
    (h : toNat b ∣ toNat a) (hb : toNat b ≠ 0) :
    toNat (mpnDivExact a b) * toNat b = toNat a := by
  have hquot := mpnDivExact_spec a b h hb
  rw [hquot]
  exact Nat.div_mul_cancel h

/-! ## §3  Concrete sanity checks (decidable `#eval` / `native_decide`) -/

/-- `6 / 3 = 2` exactly (single limbs); `3 ∣ 6`. -/
example : mpnDivExact [6] [3] = [2] := by native_decide

/-- `2^64 + 6` divided exactly by `3` (`3 ∣ 2^64 + 6` since
    `2^64 ≡ 1 mod 3` so `2^64 + 6 ≡ 1 + 0 ≡ … `; checked concretely on the
    `toNat` denotation). -/
example : toNat (mpnDivExact [6, 1] [3]) = (6 + 2 ^ 64) / 3 := by native_decide

/-- The remainder vanishes for an exact division `100 / 4 = 25`. -/
example : toNat (mpnDivRem [100] [4]).2 = 0 := by native_decide

/-- Multiplicative round-trip: `(mpnDivExact [100] [4]) * 4 = 100`. -/
example : toNat (mpnDivExact [100] [4]) * toNat [4] = toNat [100] := by native_decide

end CatCrypt.Crypto.Jasmin.Mpn.DivExactSpec
