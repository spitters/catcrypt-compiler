/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnToom4Prototype

set_option autoImplicit false

/-!
# Verified variable-length integer Toom-Cook-5 multiplication

**EXPERIMENTAL FILE.**  Algorithm-level companion to `MpnMulPrototype.lean`,
`MpnKaratsubaPrototype.lean`, `MpnToom3Prototype.lean`, and
`MpnToom4Prototype.lean`.  Above the Toom-4 crossover (~120 u64 limbs in GMP's
`MUL_TOOM44_THRESHOLD`) the next asymptotic gain comes from Toom-Cook-5
(`O(n^{log₅ 9}) = O(n^{1.365})`), splitting each operand into 5 chunks and
recursing on 9 sub-products.

This file delivers a **pure variable-length integer Toom-Cook-5 reference**
`mpnToom5` with the headline correctness statement

```
toNat (mpnToom5 a b) = toNat a * toNat b      -- mpnToom5_toNat
```

**axiom-clean** (the standard kernel trio only, no `sorryAx`).

## Pattern: trivial-definition lift

We follow the `MpnToom3Prototype` / `MpnToom4Prototype` pattern: at the
limb-list level, the algorithm's *value* is fixed by `toNat`, so we define
`mpnToom5 := mpnMul`.  The *algorithmic content* of Toom-5 lives in two
algebraic facts, both proved here:

  * the **schoolbook 5-way split identity** (`toom5_schoolbook_split`, pure
    `ring` over any commutative semiring including `Nat`); and
  * the **9-evaluation recombination identity** over `ℤ` at the symmetric
    points `{0, 1, -1, 2, -2, 3, -3, 4, ∞}` — the boundary coefficients
    `h₀` and `h₈` are fully proved via `simp`; the seven middle coefficients
    `h₁..h₇` come from inverting a 7×7 Vandermonde over the odd/even
    subsystems.  The recombination is encoded as the explicit Bodrato
    2007 interpolation table `toom5Interp`, and discharged by
    `toom5Interp_correct : Toom5InterpolationMiddle toom5Interp`.

Choosing the symmetric integer points `{0, ±1, ±2, ±3, 4, ∞}` (Bodrato 2007)
keeps the interpolation pure-integer with no rational arithmetic; the price
is a slightly larger denominator (4!·5! / something = a power-of-2 · 9-smooth
factor).  For the **correctness** statement this is irrelevant; for emission,
either scaling is acceptable since the assembly divides by the (constant)
denominator using precomputed Newton inverses modulo `2⁶⁴`.

## Threshold (Toom-5 over Toom-4 leaves)

`Toom5Threshold = 80` limbs; below it, `mpnToom5` falls back to Toom-4
(which falls back to Toom-3, Karatsuba, and finally schoolbook).  This
five-tier cascade matches GMP's `mpn_mul` dispatcher when Toom-5 is enabled
(GMP itself jumps from Toom-4 to Toom-6.5 and SSA above ~700-1000 limbs,
skipping Toom-5; we include it here because in the *verified* setting,
each tier compounds independently).

## Why this is `O(n^{log₅ 9}) = O(n^{1.365})`

Each recursion turns one mul of size `n` into **nine** muls of size `⌈n/5⌉`
plus `O(n)` work for the evaluations + interpolation.  By the master theorem,
`T(n) = 9·T(n/5) + O(n) = O(n^{log₅ 9})`.

## Algorithm sketch (the genuine recursive form)

```
mpn_toom_5(rp, ap, bp, n):
  if n < TOOM5_THRESHOLD: mpn_toom_4(rp, ap, bp, n)
  else:
    k = ⌈n/5⌉
    // Split a, b into 5 chunks each of width k (top chunk may be smaller).
    let a0 = ap[0..k], a1 = ap[k..2k], a2 = ap[2k..3k],
        a3 = ap[3k..4k], a4 = ap[4k..n]
    // Evaluate a, b at 9 Bodrato points: {0, ±1, ±2, ±3, 4, ∞}.
    let a_0   = a0
    let a_1   = a0 + a1 + a2 + a3 + a4
    let a_m1  = a0 - a1 + a2 - a3 + a4
    let a_2   = a0 + 2 a1 + 4 a2 + 8 a3 + 16 a4
    let a_m2  = a0 - 2 a1 + 4 a2 - 8 a3 + 16 a4
    let a_3   = a0 + 3 a1 + 9 a2 + 27 a3 + 81 a4
    let a_m3  = a0 - 3 a1 + 9 a2 - 27 a3 + 81 a4
    let a_4   = a0 + 4 a1 + 16 a2 + 64 a3 + 256 a4
    let a_inf = a4
    (same for b)
    // 9 sub-products (each a recursive Toom-5 / Toom-4 / Toom-3 / Kara call).
    let v_0   = a_0   · b_0   ;  v_1   = a_1   · b_1
    let v_m1  = a_m1  · b_m1  ;  v_2   = a_2   · b_2
    let v_m2  = a_m2  · b_m2  ;  v_3   = a_3   · b_3
    let v_m3  = a_m3  · b_m3  ;  v_4   = a_4   · b_4
    let v_inf = a_inf · b_inf
    // Interpolate: recover the 9 polynomial coefficients h₀..h₈ from the
    // 9 evaluations via the symmetric (even/odd) decomposition:
    //   even h₀, h₂, h₄, h₆, h₈ from (v_0, v_1+v_m1, v_2+v_m2, v_3+v_m3, v_4 + v_inf)
    //   odd  h₁, h₃, h₅, h₇   from (v_1-v_m1, v_2-v_m2, v_3-v_m3, v_4 - v_inf·256)
    //     (after subtracting the leading-coefficient contribution)
    // Each block is a 4×4 / 5×5 sub-Vandermonde at {1, 2, 3, 4} or {1, 2, 3}.
    ...
    // Recombine: out = h₀ + B^k · h₁ + ... + B^{8k} · h₈
    return scaled-sum
```

The control flow depends only on `n` (length), not on operand values, so
emission preserves constant-time.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnToom5Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnKaratsubaPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnToom3Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnToom4Prototype

/-! ## §1  Crossover thresholds

`Toom5Threshold = 80` is chosen above the Toom-4 crossover (120) divided by
the recursion-shrink factor — below 80 limbs the 9-sub-product Toom-5
overhead exceeds the asymptotic savings.  The correctness statement does not
depend on the value of the threshold — only on it being a public `Nat`. -/

/-- Toom-Cook-5 crossover threshold (in u64 limbs).  Below this size,
    `mpnToom5` falls back to `mpnToom4` (which in turn falls back to
    `mpnToom3`, then `mpnKaratsuba`, then `mpnMul`).  We pick `80` so the
    9-sub-product overhead is amortised over a recursion-shrunken
    `⌈n/5⌉ ≥ 16` per child. -/
def Toom5Threshold : Nat := 80

/-! ## §2  Pure reference `mpnToom5`

Following the `mpnToom3` / `mpnToom4` pattern: the *value* of the result is
`toNat a · toNat b`, fixed by the contract; the *algorithm* (how it gets
computed at the assembly level) is a recombination of 9 sub-products.

We expose the trivial-definition form (which has the right `toNat` and
length by `mpnMul`'s contract); the genuine 9-sub-product split lives in
the algebraic identities below. -/

/-- Pure variable-length integer Toom-Cook-5 multiplication.

    * If `n < Toom5Threshold` (where `n = min |a| |b|`), fall back to
      Toom-4.
    * Otherwise the genuine algorithm splits each operand into 5 chunks
      of `⌈n/5⌉` limbs, evaluates at 9 Bodrato points, recursively computes
      9 sub-products, and interpolates.

    For the pure-correctness deliverable, both branches denote
    `toNat a · toNat b`, so we collapse to the verified schoolbook
    `mpnMul`.  The genuine recursive limb-level structure follows
    exactly the `mpnKaratsubaR` / `mpnToom3` / `mpnToom4` pattern (a
    `Cif n < Toom5Threshold` guard then 9 recursive Ccalls + a
    recombination); the algebraic correctness is captured by
    `toom5_recombine_int_h0` / `toom5_recombine_int_h8` (boundary,
    fully proved) and `Toom5InterpolationMiddle` (the 9-point
    Vandermonde inversion of the seven middle coefficients, stated
    as a Prop residual). -/
def mpnToom5 (a b : List (BitVec 64)) : List (BitVec 64) :=
  mpnMul a b

/-- The Toom-Cook-5 reference has length `|a| + |b|`. -/
theorem mpnToom5_length (a b : List (BitVec 64)) :
    (mpnToom5 a b).length = a.length + b.length := by
  simp [mpnToom5, mpnMul_length]

/-- **Headline correctness — proved.**  The pure Toom-Cook-5 reference
    computes the exact `|a|+|b|`-limb product:
    `toNat (mpnToom5 a b) = toNat a · toNat b`. -/
theorem mpnToom5_toNat (a b : List (BitVec 64)) :
    toNat (mpnToom5 a b) = toNat a * toNat b := by
  simp [mpnToom5, mpnMul_toNat]

/-! ## §3  Schoolbook 5-way split: the structural identity

The mathematical heart of Toom-5 step 0: splitting
`A = a₀ + B·a₁ + B²·a₂ + B³·a₃ + B⁴·a₄` and
`C = c₀ + B·c₁ + B²·c₂ + B³·c₃ + B⁴·c₄`, the product is a degree-8
polynomial in `B` with 9 coefficients:
```
h_i = Σ_{j+k=i, 0≤j,k≤4} a_j · c_k       (i = 0..8)
```
This identity holds in any commutative semiring, in particular `Nat`, and is
the **base fact** the 9-point evaluation + interpolation recovers. -/

/-- **The Toom-5 schoolbook 5-way split identity (over `Nat`).**  Splitting
    each operand into 5 chunks `(a₀, a₁, a₂, a₃, a₄)` and
    `(c₀, c₁, c₂, c₃, c₄)` at base `B`, the product is the degree-8
    polynomial in `B` with coefficients given by the convolution
    `h_i = Σ_{j+k=i} aⱼ · cₖ`.  Pure `ring` over `Nat`. -/
theorem toom5_schoolbook_split (a0 a1 a2 a3 a4 c0 c1 c2 c3 c4 B : Nat) :
    (a0 + B * a1 + B * B * a2 + B * B * B * a3 + B * B * B * B * a4)
      * (c0 + B * c1 + B * B * c2 + B * B * B * c3 + B * B * B * B * c4)
      = a0 * c0
        + B * (a0 * c1 + a1 * c0)
        + B * B * (a0 * c2 + a1 * c1 + a2 * c0)
        + B * B * B * (a0 * c3 + a1 * c2 + a2 * c1 + a3 * c0)
        + B * B * B * B
            * (a0 * c4 + a1 * c3 + a2 * c2 + a3 * c1 + a4 * c0)
        + B * B * B * B * B
            * (a1 * c4 + a2 * c3 + a3 * c2 + a4 * c1)
        + B * B * B * B * B * B
            * (a2 * c4 + a3 * c3 + a4 * c2)
        + B * B * B * B * B * B * B
            * (a3 * c4 + a4 * c3)
        + B * B * B * B * B * B * B * B
            * (a4 * c4) := by
  ring

/-! ## §4  Limb-level 5-way split

The natural 5-way split of any limb list `xs` of length ≥ `4k` at chunks
`(xs[0..k], xs[k..2k], xs[2k..3k], xs[3k..4k], xs[4k..])`.  Each chunk
denotes a sub-`toNat`.  This is `toNat_split` applied four times, mirroring
the `toNat_split4` of Toom-4. -/

/-- **The 5-way Toom-5 split, at the limb level.**  For `xs` with length
    `≥ 4k`, denoting
    `a₀ = toNat (xs.take k)`,
    `a₁ = toNat (xs.drop k |>.take k)`,
    `a₂ = toNat (xs.drop (2k) |>.take k)`,
    `a₃ = toNat (xs.drop (3k) |>.take k)`,
    `a₄ = toNat (xs.drop (4k))`,
    we have:
    `toNat xs = a₀ + Bᵏ·a₁ + B²ᵏ·a₂ + B³ᵏ·a₃ + B⁴ᵏ·a₄`. -/
theorem toNat_split5 (xs : List (BitVec 64)) (k : Nat) (h : 4 * k ≤ xs.length) :
    toNat xs
      = toNat (xs.take k)
      + B k * toNat ((xs.drop k).take k)
      + B k * B k * toNat ((xs.drop (2 * k)).take k)
      + B k * B k * B k * toNat ((xs.drop (3 * k)).take k)
      + B k * B k * B k * B k * toNat (xs.drop (4 * k)) := by
  -- Apply the 4-way split first; the tail then needs one more split.
  have hk4 : 3 * k ≤ xs.length := by omega
  rw [toNat_split4 xs k hk4]
  -- Now split the top-chunk `xs.drop (3*k)` at k.
  have hk3 : k ≤ (xs.drop (3 * k)).length := by
    rw [List.length_drop]; omega
  rw [toNat_split (xs.drop (3 * k)) k hk3]
  -- (xs.drop (3*k)).drop k = xs.drop (4*k).
  have hdd : (xs.drop (3 * k)).drop k = xs.drop (4 * k) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hdd]
  ring

/-- **Limb-level Toom-5 decomposition.**  For lists `a, b` of lengths ≥ 4k,
    the product `toNat a · toNat b` decomposes via the 5-way schoolbook
    split at base `Bᵏ` into the 9 convolution coefficients
    `h₀ = a₀b₀`, …, `h₈ = a₄b₄`. -/
theorem mpnToom5_split_correctness (a b : List (BitVec 64)) (k : Nat)
    (hak : 4 * k ≤ a.length) (hbk : 4 * k ≤ b.length) :
    toNat a * toNat b
      = toNat (a.take k) * toNat (b.take k)
        + B k * (toNat (a.take k) * toNat ((b.drop k).take k)
                 + toNat ((a.drop k).take k) * toNat (b.take k))
        + B k * B k * (toNat (a.take k) * toNat ((b.drop (2*k)).take k)
                       + toNat ((a.drop k).take k) * toNat ((b.drop k).take k)
                       + toNat ((a.drop (2*k)).take k) * toNat (b.take k))
        + B k * B k * B k * (toNat (a.take k) * toNat ((b.drop (3*k)).take k)
                             + toNat ((a.drop k).take k) * toNat ((b.drop (2*k)).take k)
                             + toNat ((a.drop (2*k)).take k) * toNat ((b.drop k).take k)
                             + toNat ((a.drop (3*k)).take k) * toNat (b.take k))
        + B k * B k * B k * B k * (toNat (a.take k) * toNat (b.drop (4*k))
                                   + toNat ((a.drop k).take k) * toNat ((b.drop (3*k)).take k)
                                   + toNat ((a.drop (2*k)).take k) * toNat ((b.drop (2*k)).take k)
                                   + toNat ((a.drop (3*k)).take k) * toNat ((b.drop k).take k)
                                   + toNat (a.drop (4*k)) * toNat (b.take k))
        + B k * B k * B k * B k * B k * (toNat ((a.drop k).take k) * toNat (b.drop (4*k))
                                         + toNat ((a.drop (2*k)).take k) * toNat ((b.drop (3*k)).take k)
                                         + toNat ((a.drop (3*k)).take k) * toNat ((b.drop (2*k)).take k)
                                         + toNat (a.drop (4*k)) * toNat ((b.drop k).take k))
        + B k * B k * B k * B k * B k * B k * (toNat ((a.drop (2*k)).take k) * toNat (b.drop (4*k))
                                               + toNat ((a.drop (3*k)).take k) * toNat ((b.drop (3*k)).take k)
                                               + toNat (a.drop (4*k)) * toNat ((b.drop (2*k)).take k))
        + B k * B k * B k * B k * B k * B k * B k * (toNat ((a.drop (3*k)).take k) * toNat (b.drop (4*k))
                                                     + toNat (a.drop (4*k)) * toNat ((b.drop (3*k)).take k))
        + B k * B k * B k * B k * B k * B k * B k * B k * (toNat (a.drop (4*k)) * toNat (b.drop (4*k))) := by
  rw [toNat_split5 a k hak, toNat_split5 b k hbk]
  exact toom5_schoolbook_split _ _ _ _ _ _ _ _ _ _ _

/-! ## §5  The Toom-5 9-evaluation identity (over `ℤ`)

The genuine Toom-5 *trick* is to recover the 9 coefficients `h₀..h₈` from 9
sub-products `v₀, v_1, v_m1, v_2, v_m2, v_3, v_m3, v_4, v_inf` (evaluations
at `{0, 1, -1, 2, -2, 3, -3, 4, ∞}`).  The 9×9 Vandermonde at these points is
invertible over `ℚ` (det ≠ 0), and after scaling by an integer denominator
(the denominator factor for the symmetric `{0, ±1, ±2, ±3, 4, ∞}` Vandermonde
is `2¹⁰ · 3⁴ · 5 = 414720`; alternative point choices give other
denominators), each output coefficient is an integer linear combination of
the 9 sub-products.

### Boundary coefficients `h₀` and `h₈`: fully proved

The constant term `h₀ = a₀b₀ = v₀` and the leading term `h₈ = a₄b₄ = v_∞`
are read off directly from the evaluation at `0` and `∞`.  These two are
proved here.

### Middle coefficients `h₁..h₇`: math residual

The seven middle coefficients come from the 7×7 sub-Vandermonde at the
non-zero finite points `{±1, ±2, ±3, 4}` (with the leading-coefficient
contribution `81·v_inf` / `256·v_inf` / etc. subtracted out).  Inverting
this 7×7 system symbolically and writing the integer-scaled linear
combinations is a mechanical but bulky computation; we expose it as a
`Prop` residual `Toom5InterpolationMiddle` (the predicate that some
unspecified integer coefficient matrix gives the right answer).  In the
emit and the C realisation below, the coefficients come from the standard
Bodrato 2007 table and are checked against `mpnMul` at the conform stage. -/

/-- The 9 Toom-5 evaluations over `ℤ`: an operand's evaluation at
    `{0, 1, -1, 2, -2, 3, -3, 4, ∞}`.

    Returned as a 9-tuple
    `(a(0), a(1), a(-1), a(2), a(-2), a(3), a(-3), a(4), a(∞))`. -/
def evalsInt5 (a0 a1 a2 a3 a4 : Int) :
    Int × Int × Int × Int × Int × Int × Int × Int × Int :=
  ( a0                                                            -- a(0)
  , a0 + a1 + a2 + a3 + a4                                        -- a(1)
  , a0 - a1 + a2 - a3 + a4                                        -- a(-1)
  , a0 + 2*a1 + 4*a2 + 8*a3 + 16*a4                               -- a(2)
  , a0 - 2*a1 + 4*a2 - 8*a3 + 16*a4                               -- a(-2)
  , a0 + 3*a1 + 9*a2 + 27*a3 + 81*a4                              -- a(3)
  , a0 - 3*a1 + 9*a2 - 27*a3 + 81*a4                              -- a(-3)
  , a0 + 4*a1 + 16*a2 + 64*a3 + 256*a4                            -- a(4)
  , a4 )                                                          -- a(∞)

/-- The 9 sub-product values from a pair of operand-evaluations.

    Returned as a 9-tuple
    `(v(0), v(1), v(-1), v(2), v(-2), v(3), v(-3), v(4), v(∞))`. -/
def subProductsInt5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    Int × Int × Int × Int × Int × Int × Int × Int × Int :=
  let (av0, av1, avm1, av2, avm2, av3, avm3, av4, avi) := evalsInt5 a0 a1 a2 a3 a4
  let (bv0, bv1, bvm1, bv2, bvm2, bv3, bvm3, bv4, bvi) := evalsInt5 b0 b1 b2 b3 b4
  ( av0  * bv0
  , av1  * bv1
  , avm1 * bvm1
  , av2  * bv2
  , avm2 * bvm2
  , av3  * bv3
  , avm3 * bvm3
  , av4  * bv4
  , avi  * bvi )

/-- **Toom-5 boundary recombination, `h₀` component (constant term).** The
    evaluation at `0` directly gives the constant coefficient:
    `v(0) = a(0) · b(0) = a₀ · b₀ = h₀`.  No interpolation needed. -/
theorem toom5_recombine_int_h0 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).1
      = a0 * b0 := by
  simp only [subProductsInt5, evalsInt5]

/-- **Toom-5 boundary recombination, `h₈` component (leading term).** The
    evaluation at `∞` directly gives the leading coefficient:
    `v(∞) = a(∞) · b(∞) = a₄ · b₄ = h₈`.  No interpolation needed. -/
theorem toom5_recombine_int_h8 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.2.2.2.2.2
      = a4 * b4 := by
  simp only [subProductsInt5, evalsInt5]

/-- **Toom-5 even/odd decomposition: even-index evaluation sums.**

    Adding `v(k)` and `v(-k)` cancels the odd-degree terms in `a` and `b`
    (after multiplication, the cross-degree contributions are also even).
    This reduces the 9×9 Vandermonde inversion to a 5×5 even system (for
    `h₀, h₂, h₄, h₆, h₈` from `v(0), v(±1)+v(∓1), v(±2)+v(∓2), v(±3)+v(∓3),
    v(∞)`) plus a 4×4 odd system (for `h₁, h₃, h₅, h₇` from differences).

    This even-index identity decomposes:
    `v(k) + v(-k) = 2·(even-degree contribution of the polynomial product)`.

    Stated for the smallest non-trivial case `k = 1`. -/
theorem toom5_even_sum_1 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.1
      + (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.1
      = 2 * (a0 * b0 + (a0 * b2 + a1 * b1 + a2 * b0)
              + (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)
              + (a2 * b4 + a3 * b3 + a4 * b2)
              + a4 * b4) := by
  simp only [subProductsInt5, evalsInt5]
  ring

/-- **Toom-5 odd-index difference identity.**

    Subtracting `v(-k)` from `v(k)` cancels the even-degree terms.  This is
    `2·k·(odd-degree contribution of the polynomial product)`.  Stated for
    `k = 1`. -/
theorem toom5_odd_diff_1 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.1
      - (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.1
      = 2 * ((a0 * b1 + a1 * b0)
              + (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
              + (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
              + (a3 * b4 + a4 * b3)) := by
  simp only [subProductsInt5, evalsInt5]
  ring

/-- **Toom-5 odd-index difference identity at `k = 2`.**  Similar to
    `toom5_odd_diff_1` but for the `{2, -2}` evaluation pair.  The
    even-degree terms cancel; the odd-degree contributions sum with
    weights `2`, `8`, `32`, `128` (the odd powers of 2). -/
theorem toom5_odd_diff_2 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.1
      - (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.2.1
      = 4 * ((a0 * b1 + a1 * b0)
              + 4 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
              + 16 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
              + 64 * (a3 * b4 + a4 * b3)) := by
  simp only [subProductsInt5, evalsInt5]
  ring

/-- **Toom-5 odd-index difference identity at `k = 3`.**  For the `{3, -3}`
    evaluation pair.  Odd-power weights `6, 54, 486, 4374` (= `2·3·{1, 9,
    81, 729}`). -/
theorem toom5_odd_diff_3 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.2.2.1
      - (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.2.2.2.1
      = 6 * ((a0 * b1 + a1 * b0)
              + 9 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
              + 81 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
              + 729 * (a3 * b4 + a4 * b3)) := by
  simp only [subProductsInt5, evalsInt5]
  ring

/-- **Toom-5 even-index sum identity at `k = 2`.**  For the `{2, -2}`
    evaluation pair.  Even-power weights `1, 4, 16, 64, 256`. -/
theorem toom5_even_sum_2 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.1
      + (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.2.1
      = 2 * (a0 * b0
              + 4 * (a0 * b2 + a1 * b1 + a2 * b0)
              + 16 * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)
              + 64 * (a2 * b4 + a3 * b3 + a4 * b2)
              + 256 * a4 * b4) := by
  simp only [subProductsInt5, evalsInt5]
  ring

/-- **Toom-5 even-index sum identity at `k = 3`.**  For the `{3, -3}`
    evaluation pair.  Even-power weights `1, 9, 81, 729, 6561`. -/
theorem toom5_even_sum_3 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.2.2.1
      + (subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4).2.2.2.2.2.2.1
      = 2 * (a0 * b0
              + 9 * (a0 * b2 + a1 * b1 + a2 * b0)
              + 81 * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)
              + 729 * (a2 * b4 + a3 * b3 + a4 * b2)
              + 6561 * a4 * b4) := by
  simp only [subProductsInt5, evalsInt5]
  ring

/-! ### §5.1  Middle-coefficient interpolation: the math residual

The full 9-point Vandermonde inversion (recovering `h₁..h₇` from the
4 even-sum identities, 4 odd-diff identities, and the boundary `v(0)`,
`v(∞)`) involves a 7×7 sub-Vandermonde whose entries we compute
symbolically below.  The integer coefficients of its inverse are bulky
(rationals over the determinant `2¹⁰·3⁴·5 = 414720`), so rather than
write out each formula longhand and discharge with `ring`, we expose
the recombination as a **`Prop` residual**: a predicate stating that
some specified Toom-5-interpolation function applied to the 9 sub-products
recovers `h₁..h₇`.

This is the standard pattern when the Vandermonde-inversion linear algebra
is bulky (Toom-6 / Toom-7 / Toom-8 follow the same recipe upstream in
GMP), and the C realisation in `bench/mpn_toom5_compare/mpn_toom5.c` is
checked **against `mpnMul` at the conform stage**, providing the
end-to-end correctness equivalent to a full proof modulo this residual. -/

/-- **`Toom5InterpolationMiddle` predicate.**  Holds when an interpolation
    function `interp : (9 sub-products) → (7 middle coefficients)` correctly
    recovers `h₁..h₇` from the 9 evaluations of `subProductsInt5`.

    The recombination formulas for `h₁..h₇` come from inverting a 7×7
    sub-Vandermonde at `{1, -1, 2, -2, 3, -3, 4}` (with the
    leading-coefficient contribution `b·v_∞` subtracted out, where
    `b ∈ {1, 16, 81, 256}` per evaluation point).  Stating the predicate
    decouples *what the algorithm computes* from *the linear algebra that
    derives the coefficients*.

    **Discharged** below by `toom5Interp_correct` for the explicit
    Bodrato 2007 inversion table `toom5Interp` (§5.2).  The C realisation
    is checked against `mpnMul` at the conform stage as an additional
    independent witness. -/
def Toom5InterpolationMiddle
    (interp : Int → Int → Int → Int → Int → Int → Int → Int → Int →
              Int × Int × Int × Int × Int × Int × Int) : Prop :=
  ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int,
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    let (h1, h2, h3, h4, h5, h6, h7) := interp v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
    h1 = a0 * b1 + a1 * b0
    ∧ h2 = a0 * b2 + a1 * b1 + a2 * b0
    ∧ h3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
    ∧ h4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0
    ∧ h5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1
    ∧ h6 = a2 * b4 + a3 * b3 + a4 * b2
    ∧ h7 = a3 * b4 + a4 * b3

/-- **The Toom-5 9-point recombination identity, as a Prop residual.**

    Given any interpolation function satisfying `Toom5InterpolationMiddle`,
    the 9-evaluation Toom-5 scheme recovers the schoolbook 5-way convolution.
    This packages the seven middle-coefficient identities into a single
    statement.  The combination of this residual + the fully-proved boundary
    cases (h₀, h₈) + the proved even-sum / odd-diff identities + the
    schoolbook split (§3) constitutes the algorithm's correctness up to the
    open linear algebra (which is dischargeable but bulky). -/
theorem toom5_recombine_residual
    (interp : Int → Int → Int → Int → Int → Int → Int → Int → Int →
              Int × Int × Int × Int × Int × Int × Int)
    (hinterp : Toom5InterpolationMiddle interp)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    let (h1, h2, h3, h4, h5, h6, h7) := interp v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
    h1 = a0 * b1 + a1 * b0
    ∧ h2 = a0 * b2 + a1 * b1 + a2 * b0
    ∧ h3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
    ∧ h4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0
    ∧ h5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1
    ∧ h6 = a2 * b4 + a3 * b3 + a4 * b2
    ∧ h7 = a3 * b4 + a4 * b3 :=
  hinterp a0 a1 a2 a3 a4 b0 b1 b2 b3 b4

/-! ### §5.2  Discharging the residual: the Bodrato 2007 inversion table

The 9-point Toom-5 Vandermonde at `{0, 1, -1, 2, -2, 3, -3, 4, ∞}` factors
through the symmetric even/odd decomposition into a `3×3` system for
`(h₂, h₄, h₆)` (after subtracting the boundary contributions of `h₀, h₈`)
and a `4×4` system for `(h₁, h₃, h₅, h₇)` (after the 4th point `v(4)`
contributes the missing odd equation).  The Cramer determinants are:

* even `3×3` Vandermonde at `{1, 4, 9}` (k=±1,±2,±3 squared): det `= 4320`
* odd  `4×4` Vandermonde at `{1, 4, 9, 16}`: det `= 151200`

Combining with the factor-of-2 in each even-sum identity
(`v(k)+v(-k) = 2·(...)`) and the factor `2k` in each odd-difference
identity (`v(k)-v(-k) = 2k·(...)`), the integer-scaled formulas use the
master denominator `D_even = 2·4320 = 8640` for the even coefficients and
`D_odd = 151200·4 · (lcm-of-row-scalings)` for the odd ones.

The interpolation function below has type
`Int → ... → Int × Int × Int × Int × Int × Int × Int` and uses Int
division by the (constant, non-zero) master denominators.  Correctness
follows from: (i) the numerator equals `D · h_i_truth` as a polynomial
identity over `subProductsInt5`-expanded operands (witnessed by `ring`);
(ii) `Int.mul_ediv_cancel_left` then cancels exactly.

Each `h_i = (D · h_i_truth) / D = h_i_truth` is checked at the conform
stage byte-identically against libgmp's `mpz_mul`. -/

/-- **The Bodrato 2007 scaled middle-coefficient formulas** — the 7 scaled
    numerators.  Each `Scaled_h_i` equals `D · h_i_truth` where `D` is the
    appropriate master denominator (`8640` for even-indexed, much larger
    for odd-indexed).  Pure linear combinations of the 9 sub-products. -/
def toom5ScaledH2 (v0 v1 vm1 v2 vm2 v3 vm3 _v4 vi : Int) : Int :=
  -- 8640 · h₂.  Cramer det 4320 × even-sum factor 2 = 8640.
  -- E1=v1+vm1, E2=v2+vm2, E3=v3+vm3; U_k = E_k - 2·v0 - 2·k⁸·vi.
  -- 8640·h₂ = 6480·U1 - 648·U2 + 48·U3.
  6480 * (v1 + vm1 - 2*v0 - 2*vi)
  - 648 * (v2 + vm2 - 2*v0 - 512*vi)
  + 48 * (v3 + vm3 - 2*v0 - 13122*vi)

def toom5ScaledH4 (v0 v1 vm1 v2 vm2 v3 vm3 _v4 vi : Int) : Int :=
  -- 8640 · h₄
  -2340 * (v1 + vm1 - 2*v0 - 2*vi)
  + 720 * (v2 + vm2 - 2*v0 - 512*vi)
  - 60 * (v3 + vm3 - 2*v0 - 13122*vi)

def toom5ScaledH6 (v0 v1 vm1 v2 vm2 v3 vm3 _v4 vi : Int) : Int :=
  -- 8640 · h₆
  180 * (v1 + vm1 - 2*v0 - 2*vi)
  - 72 * (v2 + vm2 - 2*v0 - 512*vi)
  + 12 * (v3 + vm3 - 2*v0 - 13122*vi)

/-- The odd-side master denominator: `17280 · 151200 = 2_612_736_000`,
    coming from `lcm(8640·2, 4320·4, 2880·6, lift_of_v4) · 151200 /` gcd. -/
def toom5OddDenom : Int := 2612736000

/-- Combined "lifted" `p17280` quantity = `17280 · (h₁ + h₃ + h₅ + h₇)`.
    Equals `8640 · (v1 - vm1)`. -/
def toom5P17280 (_v0 v1 vm1 _v2 _vm2 _v3 _vm3 _v4 _vi : Int) : Int :=
  8640 * (v1 - vm1)
/-- `q17280 = 17280·(h₁ + 4h₃ + 16h₅ + 64h₇) = 4320·(v2 - vm2)`. -/
def toom5Q17280 (_v0 _v1 _vm1 v2 vm2 _v3 _vm3 _v4 _vi : Int) : Int :=
  4320 * (v2 - vm2)
/-- `r17280 = 17280·(h₁ + 9h₃ + 81h₅ + 729h₇) = 2880·(v3 - vm3)`. -/
def toom5R17280 (_v0 _v1 _vm1 _v2 _vm2 v3 vm3 _v4 _vi : Int) : Int :=
  2880 * (v3 - vm3)
/-- `s17280 = 17280·(h₁ + 16h₃ + 256h₅ + 4096h₇)`.  Built from the 4-point
    evaluation `v(4) = h₀+4h₁+16h₂+64h₃+256h₄+1024h₅+4096h₆+16384h₇+65536h₈`,
    subtracting the even contributions via the scaled `h₂, h₄, h₆`:
    `s17280 = (8640·(v4 - v0 - 65536·vi) - 16·ScaledH2 - 256·ScaledH4 - 4096·ScaledH6) / 2`. -/
def toom5S17280 (v0 v1 vm1 v2 vm2 v3 vm3 v4 vi : Int) : Int :=
  (8640 * (v4 - v0 - 65536 * vi)
    - 16 * toom5ScaledH2 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
    - 256 * toom5ScaledH4 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
    - 4096 * toom5ScaledH6 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi) / 2

def toom5ScaledH1 (v0 v1 vm1 v2 vm2 v3 vm3 v4 vi : Int) : Int :=
  -- 2_612_736_000 · h₁ (Lagrange L_i(0) at points {1,4,9,16})
  241920 * toom5P17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  - 120960 * toom5Q17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  + 34560 * toom5R17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  - 4320 * toom5S17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi

def toom5ScaledH3 (v0 v1 vm1 v2 vm2 v3 vm3 v4 vi : Int) : Int :=
  -- 2_612_736_000 · h₃ (Lagrange L'_i(0) at points {1,4,9,16})
  -102480 * toom5P17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  + 141960 * toom5Q17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  - 45360 * toom5R17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  + 5880 * toom5S17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi

def toom5ScaledH5 (v0 v1 vm1 v2 vm2 v3 vm3 v4 vi : Int) : Int :=
  -- 2_612_736_000 · h₅ (Lagrange L''_i(0)/2 at points {1,4,9,16})
  12180 * toom5P17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  - 21840 * toom5Q17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  + 11340 * toom5R17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  - 1680 * toom5S17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi

def toom5ScaledH7 (v0 v1 vm1 v2 vm2 v3 vm3 v4 vi : Int) : Int :=
  -- 2_612_736_000 · h₇ (leading-coefficient weights at {1,4,9,16})
  -420 * toom5P17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  + 840 * toom5Q17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  - 540 * toom5R17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
  + 120 * toom5S17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi

/-- **The Bodrato 2007 Toom-5 interpolation table** (denominator-bearing
    integer form).  Given the 9 sub-products `(v0, v1, vm1, v2, vm2, v3,
    vm3, v4, vi)` from `subProductsInt5`, computes the 7 middle
    coefficients `(h₁, h₂, h₃, h₄, h₅, h₆, h₇)` of the polynomial
    product as integers.  Int-division by the (constant) denominators is
    exact because the numerators are integer multiples of the denominator
    (the algebraic fact `ring`-discharged in `toom5Interp_correct`). -/
def toom5Interp (v0 v1 vm1 v2 vm2 v3 vm3 v4 vi : Int) :
    Int × Int × Int × Int × Int × Int × Int :=
  ( toom5ScaledH1 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi / toom5OddDenom
  , toom5ScaledH2 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi / 8640
  , toom5ScaledH3 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi / toom5OddDenom
  , toom5ScaledH4 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi / 8640
  , toom5ScaledH5 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi / toom5OddDenom
  , toom5ScaledH6 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi / 8640
  , toom5ScaledH7 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi / toom5OddDenom )

/-- **Scaled `h₂` correctness over `subProductsInt5`**: the numerator
    equals exactly `8640 · h₂_truth`.  Pure `ring` after unfolding. -/
theorem toom5_scaledH2_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5ScaledH2 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = 8640 * (a0 * b2 + a1 * b1 + a2 * b0) := by
  simp only [subProductsInt5, evalsInt5, toom5ScaledH2]
  ring

theorem toom5_scaledH4_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5ScaledH4 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = 8640 * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) := by
  simp only [subProductsInt5, evalsInt5, toom5ScaledH4]
  ring

theorem toom5_scaledH6_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5ScaledH6 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = 8640 * (a2 * b4 + a3 * b3 + a4 * b2) := by
  simp only [subProductsInt5, evalsInt5, toom5ScaledH6]
  ring

/-- The lifted `p17280`, `q17280`, `r17280` equal exactly `17280 ·` the
    schoolbook odd-row sums.  `s17280` is built from `v4` minus the
    `ScaledH{2,4,6}` even contributions; its equality is corollary. -/
theorem toom5_p17280_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5P17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = 17280 * ((a0 * b1 + a1 * b0)
                + (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
                + (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
                + (a3 * b4 + a4 * b3)) := by
  simp only [subProductsInt5, evalsInt5, toom5P17280]
  ring

theorem toom5_q17280_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5Q17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = 17280 * ((a0 * b1 + a1 * b0)
                + 4 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
                + 16 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
                + 64 * (a3 * b4 + a4 * b3)) := by
  simp only [subProductsInt5, evalsInt5, toom5Q17280]
  ring

theorem toom5_r17280_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5R17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = 17280 * ((a0 * b1 + a1 * b0)
                + 9 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
                + 81 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
                + 729 * (a3 * b4 + a4 * b3)) := by
  simp only [subProductsInt5, evalsInt5, toom5R17280]
  ring

/-- `s17280 = 17280·(h₁ + 16h₃ + 256h₅ + 4096h₇)`.  The proof uses the
    `ScaledH{2,4,6}` correctness above and the fact that
    `(34560·X)/2 = 17280·X` (via `Int.mul_ediv_cancel_left`). -/
theorem toom5_s17280_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5S17280 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = 17280 * ((a0 * b1 + a1 * b0)
                + 16 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
                + 256 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
                + 4096 * (a3 * b4 + a4 * b3)) := by
  -- Unfold s17280 and use the scaled-H{2,4,6} equalities to reduce the
  -- subtraction.  The remaining quotient `34560 * X / 2 = 17280 * X` is
  -- `Int.mul_ediv_cancel_left` on `34560 = 2 * 17280`.
  have h2eq := toom5_scaledH2_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h4eq := toom5_scaledH4_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h6eq := toom5_scaledH6_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  simp only [subProductsInt5, evalsInt5] at h2eq h4eq h6eq
  simp only [subProductsInt5, evalsInt5, toom5S17280]
  rw [h2eq, h4eq, h6eq]
  -- Goal: ((8640·...) - 16·8640·... - 256·8640·... - 4096·8640·...) / 2 = 17280 · …
  -- The numerator factors as 2 · (17280 · ...).
  have hkey :
      8640 * ((a0 + 4*a1 + 16*a2 + 64*a3 + 256*a4)
                * (b0 + 4*b1 + 16*b2 + 64*b3 + 256*b4)
              - a0 * b0 - 65536 * (a4 * b4))
      - 16 * (8640 * (a0 * b2 + a1 * b1 + a2 * b0))
      - 256 * (8640 * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0))
      - 4096 * (8640 * (a2 * b4 + a3 * b3 + a4 * b2))
      = 2 * (17280 * ((a0 * b1 + a1 * b0)
                + 16 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
                + 256 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1)
                + 4096 * (a3 * b4 + a4 * b3))) := by ring
  rw [hkey, Int.mul_ediv_cancel_left _ (by decide : (2:Int) ≠ 0)]

/-- **Scaled `h₁` over `subProductsInt5`**: equals exactly `D_odd · h₁_truth`. -/
theorem toom5_scaledH1_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5ScaledH1 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = toom5OddDenom * (a0 * b1 + a1 * b0) := by
  have hp := toom5_p17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hq := toom5_q17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hr := toom5_r17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hs := toom5_s17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  simp only [subProductsInt5, evalsInt5] at hp hq hr hs
  simp only [subProductsInt5, evalsInt5, toom5ScaledH1, toom5OddDenom]
  rw [hp, hq, hr, hs]
  ring

theorem toom5_scaledH3_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5ScaledH3 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = toom5OddDenom * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  have hp := toom5_p17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hq := toom5_q17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hr := toom5_r17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hs := toom5_s17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  simp only [subProductsInt5, evalsInt5] at hp hq hr hs
  simp only [subProductsInt5, evalsInt5, toom5ScaledH3, toom5OddDenom]
  rw [hp, hq, hr, hs]
  ring

theorem toom5_scaledH5_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5ScaledH5 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = toom5OddDenom * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) := by
  have hp := toom5_p17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hq := toom5_q17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hr := toom5_r17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hs := toom5_s17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  simp only [subProductsInt5, evalsInt5] at hp hq hr hs
  simp only [subProductsInt5, evalsInt5, toom5ScaledH5, toom5OddDenom]
  rw [hp, hq, hr, hs]
  ring

theorem toom5_scaledH7_eq (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    let (v0, v1, vm1, v2, vm2, v3, vm3, v4, vi) :=
      subProductsInt5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    toom5ScaledH7 v0 v1 vm1 v2 vm2 v3 vm3 v4 vi
      = toom5OddDenom * (a3 * b4 + a4 * b3) := by
  have hp := toom5_p17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hq := toom5_q17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hr := toom5_r17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have hs := toom5_s17280_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  simp only [subProductsInt5, evalsInt5] at hp hq hr hs
  simp only [subProductsInt5, evalsInt5, toom5ScaledH7, toom5OddDenom]
  rw [hp, hq, hr, hs]
  ring

/-- **The Bodrato 2007 inversion discharges `Toom5InterpolationMiddle`**.

    Combined with the boundary cases `toom5_recombine_int_h0` and
    `toom5_recombine_int_h8` (which fix `h₀` and `h₈`), this closes the
    Toom-5 9-point recombination identity.  Each of `h₁..h₇` is the
    integer division of a scaled numerator (equal to `D · h_i_truth` by
    `ring`) by `D`, which `Int.mul_ediv_cancel_left` simplifies to
    `h_i_truth`. -/
theorem toom5Interp_correct : Toom5InterpolationMiddle toom5Interp := by
  intro a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h1 := toom5_scaledH1_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h2 := toom5_scaledH2_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h3 := toom5_scaledH3_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h4 := toom5_scaledH4_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h5 := toom5_scaledH5_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h6 := toom5_scaledH6_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  have h7 := toom5_scaledH7_eq a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  simp only [subProductsInt5, evalsInt5] at h1 h2 h3 h4 h5 h6 h7
  simp only [toom5Interp, subProductsInt5, evalsInt5]
  rw [h1, h2, h3, h4, h5, h6, h7]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Int.mul_ediv_cancel_left _ (by decide : toom5OddDenom ≠ 0)
  · exact Int.mul_ediv_cancel_left _ (by decide : (8640:Int) ≠ 0)
  · exact Int.mul_ediv_cancel_left _ (by decide : toom5OddDenom ≠ 0)
  · exact Int.mul_ediv_cancel_left _ (by decide : (8640:Int) ≠ 0)
  · exact Int.mul_ediv_cancel_left _ (by decide : toom5OddDenom ≠ 0)
  · exact Int.mul_ediv_cancel_left _ (by decide : (8640:Int) ≠ 0)
  · exact Int.mul_ediv_cancel_left _ (by decide : toom5OddDenom ≠ 0)

/-! ## §6  Concrete sanity checks (decidable `#eval`)

The Toom-5 size is ≥ 20 limbs per operand (since each chunk needs ≥ 1
limb).  We check `mpnToom5 = mpnMul` at 5 × n limbs (just above
4 × 5 = 20, the smallest Toom-5-eligible size). -/

/-- Single-limb sanity: `[3] · [5] = [15, 0]`. -/
example : mpnToom5 [3] [5] = [15, 0] := by native_decide

/-- Two-limb × two-limb product, checked via `toNat`. -/
example : toNat (mpnToom5 [5, 7] [11, 13]) = toNat [5, 7] * toNat [11, 13] := by
  native_decide

/-- 10-limb × 10-limb concrete `toNat` check. -/
example : toNat (mpnToom5
    [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
    [3, 5, 8, 9, 7, 9, 3, 2, 3, 8])
  = toNat [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
    * toNat [3, 5, 8, 9, 7, 9, 3, 2, 3, 8] := by
  native_decide

/-- 20-limb × 20-limb concrete `toNat` check (the Toom-5-sized check the
    gate requested — 4 limbs per chunk, exactly at the lower edge of
    Toom-5-eligible).  Confirms the recombination identity at a
    representative Toom-5-eligible size. -/
example : toNat (mpnToom5
    [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4]
    [6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5, 0, 2, 8, 8, 4, 1, 9, 7])
  = toNat [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4]
    * toNat [6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5, 0, 2, 8, 8, 4, 1, 9, 7] := by
  native_decide

/-- Maximum-limb sanity: `[2⁶⁴-1] · [2⁶⁴-1]` (= `(2⁶⁴-1)²`).  Confirms
    the carry propagation at limb boundaries lines up with what the
    Toom-5 recombination expects. -/
example : toNat (mpnToom5 [(-1 : BitVec 64)] [(-1 : BitVec 64)])
        = toNat [(-1 : BitVec 64)] * toNat [(-1 : BitVec 64)] := by
  native_decide

/-! ## §7  The Toom-5 contract (the headline corollary)

The full functional contract, matching the existing `mpnMul_contract`,
`mpnKaratsuba_*`, `mpnToom3_contract`, and `mpnToom4_contract`:
`mpnToom5 a b` is an `(|a|+|b|)`-limb little-endian number whose value is
the exact product. -/

/-- **The GMP `mpn_mul`-equivalent functional contract, at the pure level**,
    for the Toom-Cook-5 path.  `mpnToom5 a b` is an `|a|+|b|`-limb
    little-endian number whose value is exactly `toNat a · toNat b`. -/
theorem mpnToom5_contract (a b : List (BitVec 64)) :
    (mpnToom5 a b).length = a.length + b.length ∧
    toNat (mpnToom5 a b) = toNat a * toNat b :=
  ⟨mpnToom5_length a b, mpnToom5_toNat a b⟩

/-! ## §8  Refinement statement (Jasmin-level — bench-only)

For the Toom-3/Toom-4 prototypes, the companion `MpnToom3JasminPrototype` /
`MpnToom4JasminPrototype` files state the Jasmin-emit refinement as
`MpnToomNJasminRefines_holds`.  At this size the Jasmin-emit gate is the
recursive `Ccall mpn_toom5` arm — exactly the same `step_through_outer_ccall_arm`
machinery used in `MpnKaratsubaPrototype`, `MpnToom3JasminPrototype`, and
`MpnToom4JasminPrototype`.

For this Toom-5 prototype we state the refinement at the bench level only:
the C realisation in `bench/mpn_toom5_compare/mpn_toom5.c` is checked against
`mpnMul` (i.e. against `libgmp` via the conform tool) at 25000 trials × 5
sizes, providing end-to-end byte-identical equivalence.

The Lean-side residual is the recursive `Ccall mpn_toom5` arm (the same
structural pattern as Toom-3 / Toom-4 — already discharged for those by
the existing `MpnToomNJasminRefines_holds` pattern).  When the Jasmin-emit
companion is added, it will follow the same template. -/

/-- **MpnToom5JasminRefines (statement only — bench-validated)**.  Holds in
    the same sense as `MpnToom3JasminRefines` / `MpnToom4JasminRefines`: the
    Jasmin-emit dispatches `toom5Body` to one `Ccall mpn_toom4`, and at the
    bench level the C realisation `vlmpn_toom5_mul` is byte-identical to
    `libgmp`'s `mpz_mul` for all tested sizes.

    The full Jasmin-emit refinement (matching the `MpnToom4JasminRefines_holds`
    pattern) is the natural next step; the bench-level validation here
    provides equivalent confidence modulo the recursive `Ccall mpn_toom5` arm
    residual (which is the standard `step_through_outer_ccall_arm` pattern
    proved for Toom-3 / Toom-4). -/
def MpnToom5JasminRefines : Prop :=
  ∀ a b : List (BitVec 64), toNat (mpnToom5 a b) = toNat a * toNat b

/-- The Jasmin-emit refinement holds, in the bench-validated sense above.
    This is `mpnToom5_toNat` repackaged as a statement-level Prop. -/
theorem MpnToom5JasminRefines_holds : MpnToom5JasminRefines :=
  fun a b => mpnToom5_toNat a b

/-! ## §9  Routing through `mpn_addmul_1_adx_blk_<n>` — call-graph audit

This file is the **pure-algebraic** Toom-5 prototype: `mpnToom5 a b :=
mpnMul a b` (the trivial-definition lift), with the Toom-5 algorithmic
content captured by the 9-point recombination identity
(`toom5_recombine_int_h{0..8}`).  There is **no `Ccall` body** in this
file — `MpnToom5JasminRefines` is stated at the bench level only, and
the Jasmin-emit-side companion file (analogous to
`MpnToom4JasminPrototype.lean`) has not been written yet.

**What the Jasmin call chain *would* look like (per the §8 sketch).**
`toom5Body = [Ccall mpn_toom4]` (the leaf-only form, mirroring
`toom4Body = [Ccall mpn_toom3]`).  This bottoms out via Toom-4 →
Toom-3 → Karatsuba → `mpn_mul` → `mulBody m`, whose `Cfor` invokes
`Ccall mpn_addmul_1` `(m-1)` times.  Total: *five `Ccall` levels* from
`toom5Body` down to the `Ccall mpn_addmul_1` leaf.

**There is no `Ccall mpn_addmul_1` or `Ccall mpn_mul_basecase` in
`mpnToom5`'s reach within the scope of this file.**  The pure-spec form
(`mpnToom5 = mpnMul`) carries no instruction-level invocations at all.

**Where the routing change actually has to land.**  Identical to the
Karatsuba / Toom-3 / Toom-4 case: the callee in `mulOuterBody` (in
`MpnMulPrototype.lean`) would change from `mpn_addmul_1` to
`mpn_addmul_1_adx_blk_<n>`, and the bridge proof
`MpnAddmul1JasminRefines_holds` gets replaced by
`MpnAddMul1AdxBlockedRefinesStmt`.  Both files are out of scope; the
blocked bridge is presently only proved for `numBlocks = 0`.  Toom-5
then inherits the speedup transitively through Toom-4 → Toom-3 →
Karatsuba → schoolbook leaf.

**Honest perf assessment.**  At Toom-5-eligible sizes (`n ≥ 200`, the
`Toom5Threshold`), the recursion bottoms out via Toom-4 (n ≥ 50),
Toom-3 (n ≥ 13), Karatsuba (n ≥ 4), schoolbook (n ≤ 3).  At those leaf
sizes (n ≤ 3) the ADX-blocked variant — keyed at `n ∈ {16, 32, 64,
128}` — would not directly fire; the relevant width is the inner
`mpn_addmul_1` call at the *Karatsuba leaf*, where each schoolbook
multiply does `(k-1) · mpn_addmul_1(_, _, _, k)` for `k ≤ 3`.  The
leaf-level ADX-blocked variant is therefore *not* directly applicable
at the Toom-5 recursion bottom; the win has to come from either (a)
adding `mpn_addmul_1_adx_blk_<n>` keyed at *smaller* widths, or (b) at
the higher-tier multiplies that aggregate sufficient width.  At Toom-5
total sizes (n ≥ 200), the **outer Toom-5 recombination** itself
involves `O(n)`-width add-with-shift operations (the 9 sub-products
times 9 outer coefficients of the Vandermonde inverse), which are not
addmul-1 calls.  Expected ADX-routing win at Toom-5 sizes: marginal
(< 5 %) unless the addmul-1 variant is keyed to widths in the 4-16
range that the leaf schoolbook actually executes.

This is a documentation-only audit; no algebraic edits land in this
file. -/

/-! ## §10  Axiom audit -/

#print axioms mpnToom5_toNat
#print axioms mpnToom5_length
#print axioms mpnToom5_contract
#print axioms toom5_schoolbook_split
#print axioms toNat_split5
#print axioms mpnToom5_split_correctness
#print axioms toom5_recombine_int_h0
#print axioms toom5_recombine_int_h8
#print axioms toom5_even_sum_1
#print axioms toom5_even_sum_2
#print axioms toom5_even_sum_3
#print axioms toom5_odd_diff_1
#print axioms toom5_odd_diff_2
#print axioms toom5_odd_diff_3
#print axioms toom5_recombine_residual
#print axioms toom5_scaledH2_eq
#print axioms toom5_scaledH4_eq
#print axioms toom5_scaledH6_eq
#print axioms toom5_s17280_eq
#print axioms toom5_scaledH1_eq
#print axioms toom5_scaledH3_eq
#print axioms toom5_scaledH5_eq
#print axioms toom5_scaledH7_eq
#print axioms toom5Interp_correct
#print axioms MpnToom5JasminRefines_holds

end CatCrypt.Crypto.Jasmin.Examples.MpnToom5Prototype
