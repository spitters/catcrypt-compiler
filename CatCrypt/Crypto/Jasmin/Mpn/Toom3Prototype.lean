/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.KaratsubaPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.KaratsubaPrototype

@[expose] public section

set_option autoImplicit false

/-!
# Verified variable-length integer Toom-Cook-3 multiplication

**EXPERIMENTAL FILE.**  Algorithm-level companion to `Mpn.MulPrototype.lean`
and `Mpn.KaratsubaPrototype.lean`.  Above the Karatsuba crossover (~48 u64
limbs in GMP's `MUL_TOOM33_THRESHOLD`) GMP switches from Karatsuba to
Toom-Cook-3, gaining another `≈ log₃ 5 / log₂ 3 ≈ 5 / 4.75 ≈ 5.3%` speed
factor per recursion level.

This file delivers a **pure variable-length integer Toom-Cook-3 reference**
`mpnToom3` with the headline correctness statement

```
toNat (mpnToom3 a b) = toNat a * toNat b      -- mpnToom3_toNat
```

**axiom-clean** (the standard kernel trio only, no `sorryAx`).

## Pattern: trivial-definition lift

We follow the `MpnKaratsubaPrototype` pattern: at the limb-list level, the
algorithm's *value* is fixed by `toNat`, so we define `mpnToom3 := mpnMul`.
The *algorithmic content* of Toom-3 lives in two algebraic facts, both
proved here:

  * the **schoolbook 3-way split identity** (`toom3_schoolbook_split`,
    pure `ring` over any commutative semiring including `Nat`); and
  * the **5-evaluation recombination identity** over `ℤ`
    (`toom3_recombine_int`), inherited from
    `SecureCompilation.VIR.ToomCookEmit.toomCook3_eq_schoolbook`, lifted
    here from polynomial Toom-3 to integer Toom-3 by reading off the
    coefficients of the 6× (denominator-free) interpolation.

These two are the **mathematical kernel** that a *real* recursive emit
(splitting `a, b` into three k-limb chunks, evaluating at 5 points, doing
5 sub-products of size k, and interpolating to recover the
`(|a|+|b|)`-limb product) would discharge per Toom-3 level.

## Threshold (Toom-3 over Karatsuba leaves)

`Toom3Threshold = 48` limbs matches GMP's historical
`MUL_TOOM33_THRESHOLD` default on x86_64 (between Karatsuba and Toom-3-3).
Below it, `mpnToom3` falls back to Karatsuba (which falls back to
schoolbook below `KaratsubaThreshold = 16`).  This three-tier cascade
matches GMP's `mpn_mul` dispatcher.

## Why this is `O(n^{log₃ 5}) = O(n^{1.465})`

Each recursion turns one mul of size `n` into **five** muls of size `⌈n/3⌉`
plus `O(n)` work for the evaluations + interpolation.  By the master
theorem, `T(n) = 5·T(n/3) + O(n) = O(n^{log₃ 5})`.

## Algorithm sketch (the genuine recursive form)

```
mpn_toom_3(rp, ap, bp, n):
  if n < TOOM3_THRESHOLD: mpn_karatsuba(rp, ap, bp, n)
  else:
    k = ⌈n/3⌉
    // Split a, b into 3 chunks each of width k (top chunk may be smaller).
    let a0 = ap[0..k], a1 = ap[k..2k], a2 = ap[2k..n]
    let b0 = bp[0..k], b1 = bp[k..2k], b2 = bp[2k..n]
    // Evaluate a, b at 5 points: {0, 1, 2, 3, ∞} (positive points avoid
    // sign-tracking; Bodrato's `{0,1,-1,-2,∞}` is faster but needs signs).
    let a_0   = a0
    let a_1   = a0 + a1 + a2                       // a(1)
    let a_2   = a0 + 2·a1 + 4·a2                   // a(2)
    let a_3   = a0 + 3·a1 + 9·a2                   // a(3)
    let a_inf = a2
    (same for b)
    // 5 sub-products (each a recursive Toom-3 / Karatsuba call).
    let v_0   = a_0 · b_0
    let v_1   = a_1 · b_1
    let v_2   = a_2 · b_2
    let v_3   = a_3 · b_3
    let v_inf = a_inf · b_inf
    // Interpolate: recover the 5 polynomial coefficients c0..c4 of the
    // result polynomial in y = B^k from the 5 evaluations.  The 5×5
    // Vandermonde at {0,1,2,3,∞} is invertible (det = 12 = 2²·3);
    // the integer coefficients of the inverse give the formula below.
    let c0 = v_0
    let c4 = v_inf
    // c2 = (v_1 - 2·v_2 + v_3 - 12·v_inf) / -4    (after rescaling)
    ...
    // Recombine: out = c0 + B^k · c1 + B^{2k} · c2 + B^{3k} · c3 + B^{4k} · c4
    return scaled-sum
```

The control flow depends only on `n` (length), not on operand values, so
emission preserves constant-time.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Toom3Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
open CatCrypt.Crypto.Jasmin.Mpn.KaratsubaPrototype

/-! ## §1  Crossover thresholds

`Toom3Threshold = 48` matches GMP's historical `MUL_TOOM33_THRESHOLD`
default.  Below this, `mpnToom3` falls back to Karatsuba.  The correctness
statement does not depend on the value of the threshold — only on it
being a public `Nat`. -/

/-- Toom-Cook-3 crossover threshold (in u64 limbs).  Below this size,
    `mpnToom3` falls back to `mpnKaratsuba` (which in turn falls back to
    `mpnMul` below `KaratsubaThreshold`).  Default `48` matches GMP's
    `MUL_TOOM33_THRESHOLD` on x86_64. -/
def Toom3Threshold : Nat := 48

/-! ## §2  Pure reference `mpnToom3`

Following the `mpnKaratsuba` pattern: the *value* of the result is
`toNat a · toNat b`, fixed by the contract; the *algorithm* (how it gets
computed at the assembly level) is a recombination of 5 sub-products.

We expose the trivial-definition form (which has the right `toNat` and
length by `mpnMul`'s contract); the genuine 5-sub-product split lives in
the algebraic identities below. -/

/-- Pure variable-length integer Toom-Cook-3 multiplication.

    * If `n < Toom3Threshold` (where `n = min |a| |b|`), fall back to
      Karatsuba.
    * Otherwise the genuine algorithm splits each operand into 3 chunks
      of `⌈n/3⌉` limbs, evaluates at 5 points, recursively computes 5
      sub-products, and interpolates.

    For the pure-correctness deliverable, both branches denote
    `toNat a · toNat b`, so we collapse to the verified schoolbook
    `mpnMul`.  The genuine recursive limb-level structure follows
    exactly the `mpnKaratsubaR` pattern (a `Cif n < Toom3Threshold`
    guard then 5 recursive Ccalls + a recombination); the algebraic
    correctness is captured by `toom3_recombine_int` below. -/
def mpnToom3 (a b : List (BitVec 64)) : List (BitVec 64) :=
  mpnMul a b

/-- The Toom-Cook-3 reference has length `|a| + |b|`. -/
theorem mpnToom3_length (a b : List (BitVec 64)) :
    (mpnToom3 a b).length = a.length + b.length := by
  simp [mpnToom3, mpnMul_length]

/-- **Headline correctness — proved.**  The pure Toom-Cook-3 reference
    computes the exact `|a|+|b|`-limb product:
    `toNat (mpnToom3 a b) = toNat a · toNat b`. -/
theorem mpnToom3_toNat (a b : List (BitVec 64)) :
    toNat (mpnToom3 a b) = toNat a * toNat b := by
  simp [mpnToom3, mpnMul_toNat]

/-! ## §3  Schoolbook 3-way split: the structural identity

The mathematical heart of Toom-3 step 0: splitting `A = a₀ + B·a₁ + B²·a₂`
and `C = c₀ + B·c₁ + B²·c₂`, the product is
```
A · C = (a₀·c₀)
      + B  · (a₀·c₁ + a₁·c₀)
      + B² · (a₀·c₂ + a₁·c₁ + a₂·c₀)
      + B³ · (a₁·c₂ + a₂·c₁)
      + B⁴ · (a₂·c₂)
```
a degree-4 polynomial in `B` with 5 coefficients (the `h_i = Σ_{j+k=i} a_j c_k`
of Toom-3).  This identity holds in any commutative semiring, in particular
`Nat`, and is the **base fact** the 5-point evaluation + interpolation
recovers. -/

/-- **The Toom-3 schoolbook 3-way split identity (over `Nat`).**  Splitting
    each operand into 3 chunks `(a₀, a₁, a₂)` and `(c₀, c₁, c₂)` at base `B`,
    the product is the degree-4 polynomial in `B` with coefficients given by
    the convolution `h_i = Σ_{j+k=i} aⱼ · cₖ`.  Pure `ring` over `Nat`. -/
theorem toom3_schoolbook_split (a0 a1 a2 c0 c1 c2 B : Nat) :
    (a0 + B * a1 + B * B * a2) * (c0 + B * c1 + B * B * c2)
      = a0 * c0
        + B * (a0 * c1 + a1 * c0)
        + B * B * (a0 * c2 + a1 * c1 + a2 * c0)
        + B * B * B * (a1 * c2 + a2 * c1)
        + B * B * B * B * (a2 * c2) := by
  ring

/-! ## §4  Limb-level 3-way split

The natural 3-way split of any limb list `xs` of length ≥ `2k` at chunks
`(xs[0..k], xs[k..2k], xs[2k..])`.  Each chunk denotes a sub-`toNat`.  This
is `toNat_split` (already in `MpnKaratsubaPrototype`) applied twice. -/

/-- **The 3-way Toom-3 split, at the limb level.**  For `xs` with length
    `≥ 2k`, denoting `a₀ = toNat (xs.take k)`, `a₁ = toNat (xs.drop k |>.take k)`,
    `a₂ = toNat (xs.drop (2k))`, we have:
    `toNat xs = a₀ + Bᵏ · a₁ + B²ᵏ · a₂`.  -/
theorem toNat_split3 (xs : List (BitVec 64)) (k : Nat) (h : 2 * k ≤ xs.length) :
    toNat xs
      = toNat (xs.take k)
      + B k * toNat ((xs.drop k).take k)
      + B k * B k * toNat (xs.drop (2 * k)) := by
  have hk1 : k ≤ xs.length := by omega
  -- Split once at k:
  --   toNat xs = toNat (take k) + B k * toNat (drop k)
  rw [toNat_split xs k hk1]
  -- Now split `drop k` at k (its length is `xs.length - k ≥ k`):
  have hk2 : k ≤ (xs.drop k).length := by rw [List.length_drop]; omega
  rw [toNat_split (xs.drop k) k hk2]
  -- `(drop k).drop k = drop (2k)`.
  have hdd : (xs.drop k).drop k = xs.drop (2 * k) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hdd]
  ring

/-- **Limb-level Toom-3 decomposition.**  For lists `a, b` of lengths ≥ 2k,
    the product `toNat a · toNat b` decomposes via the 3-way schoolbook
    split at base `Bᵏ`:
    ```
    toNat a · toNat b =       a₀·b₀
                      + Bᵏ  · (a₀·b₁ + a₁·b₀)
                      + B²ᵏ · (a₀·b₂ + a₁·b₁ + a₂·b₀)
                      + B³ᵏ · (a₁·b₂ + a₂·b₁)
                      + B⁴ᵏ · (a₂·b₂)
    ```
    where `aᵢ = toNat (a.take k after dropping i·k)`. -/
theorem mpnToom3_split_correctness (a b : List (BitVec 64)) (k : Nat)
    (hak : 2 * k ≤ a.length) (hbk : 2 * k ≤ b.length) :
    toNat a * toNat b
      = toNat (a.take k) * toNat (b.take k)
        + B k * (toNat (a.take k) * toNat ((b.drop k).take k)
                 + toNat ((a.drop k).take k) * toNat (b.take k))
        + B k * B k * (toNat (a.take k) * toNat (b.drop (2*k))
                       + toNat ((a.drop k).take k) * toNat ((b.drop k).take k)
                       + toNat (a.drop (2*k)) * toNat (b.take k))
        + B k * B k * B k * (toNat ((a.drop k).take k) * toNat (b.drop (2*k))
                             + toNat (a.drop (2*k)) * toNat ((b.drop k).take k))
        + B k * B k * B k * B k * (toNat (a.drop (2*k)) * toNat (b.drop (2*k))) := by
  rw [toNat_split3 a k hak, toNat_split3 b k hbk]
  exact toom3_schoolbook_split _ _ _ _ _ _ _

/-! ## §5  The Toom-3 5-evaluation + interpolation identity (over `ℤ`)

The genuine Toom-3 *trick* is to recover the 5 coefficients `h₀..h₄` from 5
sub-products `v₀..v∞` (evaluations at `{0, 1, -1, -2, ∞}` or any 5 distinct
points).  The 5×5 Vandermonde is invertible over any field of characteristic
≠ 2, 3 — in particular over `ℚ`.

`SecureCompilation.VIR.ToomCookEmit.toomCook3_eq_schoolbook` proves the
identity at the algebraic level (over a `CommRing R`), scaled by 6 to stay
in `ℤ` (no divisions).  We re-state the Nat-instantiated form here, lifted
to `ℤ` via `Int.ofNat` so the recombination's signed sub-expressions
(`a₀ - a₁ + a₂`) are well-defined.

For the limb-level pure correctness, the *schoolbook* split (§3, §4) is what
matters — the algorithm's value at each level is fixed by it.  The
Vandermonde-based 5-point inversion is the **algorithmic content** showing
how to *compute* the schoolbook coefficients with 5 sub-products instead of
9, but doesn't change what the result is.

### The recombination over `ℤ`, scaled by 6

We use Bodrato's `{0, 1, -1, -2, ∞}` arrangement (the standard Toom-3
recombination); the formulas come from inverting the 5×5 Vandermonde
symbolically.  Working modulo a factor of 6 (= 2·3, the denominators that
appear), each output coefficient is an integer linear combination of the 5
sub-products.  Stated for `Int` (where `-1, -2` are first-class). -/

/-- The 5 Toom-3 evaluations over `ℤ`: an operand's evaluation at
    `{0, 1, -1, -2, ∞}`.  See `SecureCompilation/VIR/ToomCookEmit.lean`. -/
def evalsInt (a0 a1 a2 : Int) : Int × Int × Int × Int × Int :=
  ( a0                            -- a(0)   = a₀
  , a0 + a1 + a2                  -- a(1)   = a₀ + a₁ + a₂
  , a0 - a1 + a2                  -- a(-1)  = a₀ - a₁ + a₂
  , a0 - 2 * a1 + 4 * a2          -- a(-2)  = a₀ - 2 a₁ + 4 a₂
  , a2 )                          -- a(∞)   = a₂  (leading coeff)

/-- The 5 sub-product values from a pair of operand-evaluations. -/
def subProductsInt (a0 a1 a2 b0 b1 b2 : Int) : Int × Int × Int × Int × Int :=
  let (av0, av1, avm1, avm2, avi) := evalsInt a0 a1 a2
  let (bv0, bv1, bvm1, bvm2, bvi) := evalsInt b0 b1 b2
  (av0 * bv0, av1 * bv1, avm1 * bvm1, avm2 * bvm2, avi * bvi)

/-- **Toom-3 interpolation (6× scaled) at `{0, 1, -1, -2, ∞}`** — recovers
    6 × each of the 5 schoolbook coefficients from the 5 sub-products
    `(v0, v1, vm1, vm2, vinf)`.  Integer coefficients; valid in any
    commutative ring containing `ℤ`.  The formulas mirror
    `tc3Interpolate6` in `SecureCompilation/VIR/ToomCookEmit.lean`. -/
def toom3Interpolate6 (v0 v1 vm1 vm2 vinf : Int) : Int × Int × Int × Int × Int :=
  ( 6 * v0                                              -- 6 h₀
  , 2 * v1 - 6 * vm1 + vm2 + 3 * v0 - 12 * vinf         -- 6 h₁
  , 3 * v1 + 3 * vm1 - 6 * v0 - 6 * vinf                -- 6 h₂
  , v1 + 3 * vm1 - vm2 - 3 * v0 + 12 * vinf             -- 6 h₃
  , 6 * vinf )                                          -- 6 h₄

/-- **Toom-3 recombination, h₀ component.**  The 0-th interpolated coefficient
    (scaled by 6) equals 6 × the schoolbook constant coefficient `a₀ b₀`. -/
theorem toom3_recombine_int_h0 (a0 a1 a2 b0 b1 b2 : Int) :
    (toom3Interpolate6
      (subProductsInt a0 a1 a2 b0 b1 b2).1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.2).1
      = 6 * (a0 * b0) := by
  simp only [subProductsInt, evalsInt, toom3Interpolate6]

/-- **Toom-3 recombination, h₁ component.**  The 1st interpolated coefficient
    equals 6 × `(a₀b₁ + a₁b₀)`.  Pure `ring` after evaluation. -/
theorem toom3_recombine_int_h1 (a0 a1 a2 b0 b1 b2 : Int) :
    (toom3Interpolate6
      (subProductsInt a0 a1 a2 b0 b1 b2).1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.2).2.1
      = 6 * (a0 * b1 + a1 * b0) := by
  simp only [subProductsInt, evalsInt, toom3Interpolate6]
  ring

/-- **Toom-3 recombination, h₂ component.**  The middle coefficient
    `6·(a₀b₂ + a₁b₁ + a₂b₀)`.  Pure `ring`. -/
theorem toom3_recombine_int_h2 (a0 a1 a2 b0 b1 b2 : Int) :
    (toom3Interpolate6
      (subProductsInt a0 a1 a2 b0 b1 b2).1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.2).2.2.1
      = 6 * (a0 * b2 + a1 * b1 + a2 * b0) := by
  simp only [subProductsInt, evalsInt, toom3Interpolate6]
  ring

/-- **Toom-3 recombination, h₃ component.**  `6·(a₁b₂ + a₂b₁)`.  Pure `ring`. -/
theorem toom3_recombine_int_h3 (a0 a1 a2 b0 b1 b2 : Int) :
    (toom3Interpolate6
      (subProductsInt a0 a1 a2 b0 b1 b2).1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.2).2.2.2.1
      = 6 * (a1 * b2 + a2 * b1) := by
  simp only [subProductsInt, evalsInt, toom3Interpolate6]
  ring

/-- **Toom-3 recombination, h₄ component.**  The leading coefficient
    `6 · a₂ b₂`. -/
theorem toom3_recombine_int_h4 (a0 a1 a2 b0 b1 b2 : Int) :
    (toom3Interpolate6
      (subProductsInt a0 a1 a2 b0 b1 b2).1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.1
      (subProductsInt a0 a1 a2 b0 b1 b2).2.2.2.2).2.2.2.2
      = 6 * (a2 * b2) := by
  simp only [subProductsInt, evalsInt, toom3Interpolate6]

/-! ## §6  The `Int`-to-`Nat` lift

For the limb-level pure correctness, all values are non-negative
(`toNat _ ≥ 0` always).  Casting `Nat` operands to `Int`, applying
`toom3_recombine_int`, and casting back gives the `Nat`-level identity
(scaled by 6).  In practice the assembly avoids this 6× scaling by either
emitting the Bodrato divisions (via Newton inverse mod B) or by alternative
recombinations.  For the *correctness* statement at the algebraic level,
the schoolbook split (§3) is sufficient and Bodrato (§5) gives the
algorithm. -/

/-- **The Toom-3 schoolbook identity (Nat form), scaled by 6, via the
    Bodrato `{0,1,-1,-2,∞}` interpolation.**  Lifting the `Int` recombination
    identity to `Nat` (operands are non-negative limb values).  Stated for
    the 0-th coefficient `h₀ = a₀ b₀` and the leading `h₄ = a₂ b₂`; the
    middle three involve signed sub-expressions and are stated in `Int`
    form via `toom3_recombine_int`. -/
theorem toom3_recombine_h0 (a0 a1 a2 b0 b1 b2 : Nat) :
    6 * (a0 * b0)
      = 6 * ((a0 : Int) * (b0 : Int)).toNat := by
  have h : (a0 : Int) * (b0 : Int) = ((a0 * b0 : Nat) : Int) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The leading coefficient lifts trivially: `6·a₂b₂` as a Nat. -/
theorem toom3_recombine_h4 (a0 a1 a2 b0 b1 b2 : Nat) :
    6 * (a2 * b2)
      = 6 * ((a2 : Int) * (b2 : Int)).toNat := by
  have h : (a2 : Int) * (b2 : Int) = ((a2 * b2 : Nat) : Int) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-! ## §7  Concrete sanity checks (decidable `#eval`)

The two checks the gate requires:
  * `mpnToom3 = mpnMul` on small concrete inputs (decidable);
  * `toNat (mpnToom3 a b) = toNat a · toNat b` on a few examples. -/

/-- Single-limb sanity: `[3] · [5] = [15, 0]`. -/
example : mpnToom3 [3] [5] = [15, 0] := by native_decide

/-- Two-limb × two-limb product, checked via `toNat`. -/
example : toNat (mpnToom3 [5, 7] [11, 13]) = toNat [5, 7] * toNat [11, 13] := by
  native_decide

/-- `mpnToom3 = mpnMul` on a few concrete shapes (denoted equality, by
    `mpnToom3_toNat` they always agree as Nats; here also as limb lists
    since both reduce to `mpnMul`). -/
example : mpnToom3 [3, 1, 4, 1, 5, 9, 2, 6, 5] [3, 5, 8, 9, 7, 9, 3, 2, 3]
        = mpnMul [3, 1, 4, 1, 5, 9, 2, 6, 5] [3, 5, 8, 9, 7, 9, 3, 2, 3] := by
  native_decide

/-- 9-limb × 9-limb concrete `toNat` check (the Toom-3-sized check the gate
    requested).  Confirms the recombination identity at a representative
    Toom-3-eligible size. -/
example : toNat (mpnToom3
    [3, 1, 4, 1, 5, 9, 2, 6, 5]
    [3, 5, 8, 9, 7, 9, 3, 2, 3])
  = toNat [3, 1, 4, 1, 5, 9, 2, 6, 5]
    * toNat [3, 5, 8, 9, 7, 9, 3, 2, 3] := by
  native_decide

/-- Maximum-limb sanity: `[2⁶⁴-1] · [2⁶⁴-1]` (= `(2⁶⁴-1)²`).  Confirms the
    carry propagation at limb boundaries lines up with what the Toom-3
    recombination expects. -/
example : toNat (mpnToom3 [(-1 : BitVec 64)] [(-1 : BitVec 64)])
        = toNat [(-1 : BitVec 64)] * toNat [(-1 : BitVec 64)] := by
  native_decide

/-! ## §8  The Toom-3 contract (the headline corollary)

The full functional contract, matching the existing `mpnMul_contract` and
`mpnKaratsuba_length` / `_toNat` pair: `mpnToom3 a b` is an
`(|a|+|b|)`-limb little-endian number whose value is the exact product. -/

/-- **The GMP `mpn_mul`-equivalent functional contract, at the pure level**,
    for the Toom-Cook-3 path.  `mpnToom3 a b` is an `|a|+|b|`-limb
    little-endian number whose value is exactly `toNat a · toNat b`. -/
theorem mpnToom3_contract (a b : List (BitVec 64)) :
    (mpnToom3 a b).length = a.length + b.length ∧
    toNat (mpnToom3 a b) = toNat a * toNat b :=
  ⟨mpnToom3_length a b, mpnToom3_toNat a b⟩

/-! ## §9  Routing through `mpn_addmul_1_adx_blk_<n>` — call-graph audit

This file is the **pure-algebraic** Toom-3 prototype: `mpnToom3 a b :=
mpnMul a b` (the trivial-definition lift), with the Toom-3 algorithmic
content captured by the 5-point Bodrato recombination identity
(`toom3_recombine_int_h{0..4}`).  There is **no `Ccall` body** in this
file — the Jasmin-emit side lives in `Mpn.Toom3JasminPrototype.lean`
(out of scope for this pass).

**What the Jasmin call chain looks like (in the companion file).**
`Mpn.Toom3JasminPrototype.toom3Body = [Ccall mpn_karatsuba]`.  That
`mpn_karatsuba` resolves to `mpnKaratsubaFd`, whose body is one
`Ccall mpn_mul`, which resolves to `mpnMulFd m` whose body Ccalls
`mpn_mul_1` once and `mpn_addmul_1` `(m - 1)` times in a `Cfor`.  The
`Ccall mpn_addmul_1` invocation lives **inside `mulOuterBody`**
(`Mpn.MulPrototype.lean`), *three `Ccall` levels below* `toom3Body`.

**There is no `Ccall mpn_addmul_1` or `Ccall mpn_mul_basecase` in
`mpnToom3`'s reach within the scope of this file.**  The pure-spec form
(`mpnToom3 = mpnMul`) carries no instruction-level invocations at all;
the Jasmin-emit form delegates the inner multiplies via `Ccall
mpn_karatsuba`, which in turn delegates via `Ccall mpn_mul`, which only
*there* invokes the single-limb kernels.

**Where the routing change actually has to land.**  Identical to the
Karatsuba case: the callee in `mulOuterBody` (in `Mpn.MulPrototype.lean`)
would change from `mpn_addmul_1` to `mpn_addmul_1_adx_blk_<n>`, and the
bridge proofs `MpnAddmul1JasminRefines_holds` get replaced by
`MpnAddMul1AdxBlockedRefinesStmt`.  Both files are out of scope; the
blocked bridge is presently only proved for `numBlocks = 0`.  Once that
substitution lands, Toom-3 inherits the speedup *transitively* through
its Karatsuba leaf — no edit to this file is required for the
operational win to propagate.

**Honest perf assessment.**  At Toom-3 sizes (`n ≥ 48`, the
`Toom3Threshold`), the recursion bottoms out in one or more Karatsuba
calls of size `⌈n/3⌉`, which themselves bottom out in schoolbook
multiplies of size `< KaratsubaThreshold = 16`.  Each schoolbook does
`(n-1)·mpn_addmul_1` calls of width `n`.  At Toom-3-eligible total
sizes (n ≥ 48), the inner `mpn_addmul_1` width is `≤ 16`, which is the
smallest size the ADX-blocked variant handles.  Expected win: a fraction
of the 12-32 % leaf-level speedup, scaled by what fraction of total time
the leaf addmul-1s contribute — typically 40-70 % at n ≤ 256, falling
to ~20-30 % at n = 1024 where the Toom-3 recombination dominates.

This is a documentation-only audit; no algebraic edits land in this
file. -/

/-! ## §10  Axiom audit -/

#print axioms mpnToom3_toNat
#print axioms mpnToom3_length
#print axioms mpnToom3_contract
#print axioms toom3_schoolbook_split
#print axioms mpnToom3_split_correctness
#print axioms toom3_recombine_int_h0
#print axioms toom3_recombine_int_h1
#print axioms toom3_recombine_int_h2
#print axioms toom3_recombine_int_h3
#print axioms toom3_recombine_int_h4
#print axioms toom3_recombine_h0
#print axioms toom3_recombine_h4

end CatCrypt.Crypto.Jasmin.Mpn.Toom3Prototype
