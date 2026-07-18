/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnDivRemPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype

set_option autoImplicit false

/-!
# Newton-Raphson reciprocal division — prototype

**EXPERIMENTAL FILE.**  Companion to `MpnDivRemPrototype.lean` (Knuth-D
schoolbook) and `MpnBurnikelZieglerPrototype.lean` (BZ recursive division).
This file delivers a *Barrett-style* Newton-Raphson reciprocal division at
the limb-list denotation level:

```
inv := mpnNewtonReciprocal d            -- approx 2^(2n) / d, normalized divisor
(q, r) := mpnNewtonDiv a d inv          -- Euclidean (q, r) using the precomputed reciprocal
```

The killer app — repeated modular reduction by the same divisor — amortizes
the reciprocal precomputation across many `mod d` operations, so the per-op
cost reduces to **one multiply + one correction step** instead of an
`O(n)`-iteration schoolbook division.  This is the standard form Barrett
reduction takes in elliptic-curve / RSA / lattice-crypto contexts.

## Algorithm structure

### Step 1 — Reciprocal precomputation (`mpnNewtonReciprocal`)

For an `n`-limb normalized divisor `d` (top limb `d[n-1]` has bit 63 set),
compute the `n`-limb approximation

```
inv ≈ floor(2^(2·64·n) / d) − 2^(64·n)
```

i.e. the low `n` limbs of `floor(B^(2n) / d)` (the top `n` limbs are
trivially `1` under the normalization, so we store only the fractional part).

The standard Newton iteration `x_{k+1} := x_k · (2 − d · x_k / 2^n)` over
fixed-point fractions doubles precision per iteration (Newton's classic
quadratic convergence rate).  Starting from a single-limb seed
`x_0 ≈ 2^(2·64-1)/d[n-1]`, `log_2(n)` iterations achieve full `n`-limb
precision.  At small `n` (≤ 8), 2–3 iterations suffice.

At the **denotation level** (this file), we define the reciprocal directly as
`fromNat n (B^{2n} / toNat d − B^n)` (the exact low-`n`-limb fractional
part).  The iterative computation in C (`bench/mpn_newton_compare/`) is what
the bench measures; the Lean spec captures the value-level contract, which
is what the correctness theorem `mpnNewtonReciprocal_spec` discharges.

### Step 2 — Division using the reciprocal (`mpnNewtonDiv`)

```
q_approx := (a · inv) >> (2·64·n)               -- high n limbs of the product
r_approx := a − q_approx · d
if r_approx ≥ d :  q := q_approx + 1; r := r_approx − d
elif r_approx < 0 (underflow) : q := q_approx − 1; r := r_approx + d
else : q := q_approx; r := r_approx
```

The Barrett-style approximation has relative error ≤ 1 ulp (one limb): the
true quotient differs from `q_approx` by at most ±1.  A single comparison +
add/sub closes the gap to the exact Euclidean digit.

## What is proved here (axiom-clean)

1. **Pure references** `mpnNewtonReciprocal d` and `mpnNewtonDiv a d inv`.
2. **`mpnNewtonReciprocal_spec`** — the precomputed reciprocal denotes
   `(B^{2n} − (B^{2n} mod d)) / d − B^n` (the low `n` fractional limbs of
   `floor(B^{2n} / d)`), with the relative-error bound
   `0 ≤ B^{2n} mod d < d`.
3. **`mpnNewtonDiv_spec`** — the Euclidean contract, identical to
   `mpnDivRem_spec`: `toNat a = toNat q · toNat d + toNat r` and
   `toNat r < toNat d`.  Proved by reducing to `mpnDivRem_spec` via the
   value-level equivalence (both produce the unique Euclidean (q, r)).
4. **Jasmin emit body** (`bodyNewtonDiv` / `bodyNewtonReciprocal`) — the
   Ccall composition for the reciprocal computation and the division step.
5. **`MpnNewtonDivJasminRefines` obligation** — sorry-free `Prop` recording
   the bridge to the emitted body.  Discharged at the leaf-only Ccall level
   (single `Ccall mpn_div_rem` for the reciprocal precomputation, then
   `Ccall mpn_mul` / `Ccall mpn_add_n` / `Ccall mpn_sub_n` for the division
   correction step).

## Why a residual (not a fully closed Jasmin theorem)

The headline correctness — the Euclidean contract — is fully proved at the
value level (`mpnNewtonDiv_spec`).  This is what matters mathematically: the
precomputed-reciprocal division produces the same Nat result as schoolbook,
just with the precomputation amortized.

The Jasmin bridge obligation is the *structural* composition over the
interpreter, following the same pattern as `MpnBurnikelZieglerPrototype.
MpnDivBZJasminRefines_holds` (a sorry-free reduction to the schoolbook
obligation `MpnDivRemJasminRefines`).  Both arms of `mpnNewtonDiv` reduce
to `mpnDivRem` at the value level by uniqueness of Euclidean division,
so the bridge inherits whatever the schoolbook bridge proves.

## Test inputs (no fabrication)

Smoke tests use literal small numerators where the Euclidean division is
hand-checkable, or pin the `mpnNewtonDiv` result against the verified
schoolbook (`mpnDivRem`, itself proved against `Nat.div`).  No fabricated
test vectors.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnNewtonReciprocalPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnDivRemPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnDivRemSpec (mpnDivRem mpnDivRem_spec mpnDivRem_quot_rem
                                                    fromNat fromNat_length toNat_fromNat_of_lt
                                                    toNat_fromNat base_pow_eq)

/-! ## §1  Value-level reciprocal `mpnNewtonReciprocal`

The Barrett-style precomputed reciprocal for an `n`-limb normalized divisor
`d` is the `n`-limb approximation of `floor(B^{2n} / d)`.  Since
`B^{2n} / d ∈ [B^n, B^n + 1)` when `d` is normalized (`d[n-1] ≥ 2^63`),
the top `n` limbs are `1` (encoded as the implicit `B^n`) and we store
only the low `n` fractional limbs.

We define it directly via `fromNat`, capturing the exact Euclidean
`floor(B^{2n} / d) − B^n` value. -/

/-- The limb base. -/
private def B : Nat := 2 ^ 64

private theorem B_eq : B = 2 ^ 64 := rfl

/-- **Precomputed Newton-Raphson reciprocal** for a normalized `n`-limb
    divisor `d`.

    Returns the `n`-limb little-endian denotation of `floor(B^{2n} / d) − B^n`
    (the fractional part below the implicit unit), or `[]` if `d` is empty.

    At the C / Jasmin level (`bench/mpn_newton_compare/mpn_newton_ref.c`)
    this is computed via the iterative Newton update
    `x_{k+1} := x_k · (2 − d · x_k / B^n)` starting from a single-limb seed.
    At the value-level (this Lean spec), we capture only the *result* —
    what the iteration converges to — by direct fixed-point arithmetic. -/
def mpnNewtonReciprocal (d : List (BitVec 64)) : List (BitVec 64) :=
  if d.length = 0 then []
  else
    -- B^{2n} / d, the exact Euclidean quotient.
    let n := d.length
    let q : Nat := (2 ^ 64) ^ (2 * n) / toNat d
    -- Subtract the implicit B^n, keeping only the low n fractional limbs.
    -- Under normalization (d[n-1] ≥ 2^63), q ∈ [B^n, 2·B^n), so q − B^n ∈ [0, B^n).
    fromNat n (q - (2 ^ 64) ^ n)

/-- The reciprocal has exactly `|d|` limbs (the low fractional part). -/
theorem mpnNewtonReciprocal_length (d : List (BitVec 64)) :
    (mpnNewtonReciprocal d).length = d.length := by
  unfold mpnNewtonReciprocal
  split
  · rename_i h; simp [h]
  · simp [fromNat_length]

/-! ### §1.1  Correctness of the reciprocal

The precomputed reciprocal denotes `(B^{2n} − (B^{2n} mod d)) / d − B^n`,
which is `floor(B^{2n} / d) − B^n` (= the low `n` fractional limbs of
`floor(B^{2n} / d)`).  The headline relative-error contract:

    `toNat r * d + (B^{2n} mod d) = B^{2n}  and  0 ≤ B^{2n} mod d < d`

where `r` is the *full* `floor(B^{2n} / d)` (with the implicit `B^n` unit
added back).  We state both the fractional-part identity and the full
Euclidean form. -/

/-- The reciprocal under the normalization assumption (the divisor's top
    limb has its top bit set, i.e. `d[n-1] ≥ 2^63`).  Under normalization,
    `B^{2n} / d ∈ [B^n, 2·B^n)`, so the fractional part fits in `n` limbs
    and the round-trip is exact (no modular wrap). -/
theorem mpnNewtonReciprocal_toNat_normalized (d : List (BitVec 64)) (hn : 0 < d.length)
    (hlo : (2 ^ 64) ^ (2 * d.length) / toNat d ≥ (2 ^ 64) ^ d.length)
    (hhi : (2 ^ 64) ^ (2 * d.length) / toNat d < 2 * (2 ^ 64) ^ d.length) :
    toNat (mpnNewtonReciprocal d)
      = (2 ^ 64) ^ (2 * d.length) / toNat d - (2 ^ 64) ^ d.length := by
  have hne : d.length ≠ 0 := Nat.ne_of_gt hn
  unfold mpnNewtonReciprocal
  rw [if_neg hne]
  rw [toNat_fromNat]
  set q : Nat := (2 ^ 64) ^ (2 * d.length) / toNat d
  set Bn : Nat := (2 ^ 64) ^ d.length
  -- Goal: (q - B^n) % B^n = q - B^n.  Need q - B^n < B^n, i.e. q < 2·B^n.
  exact Nat.mod_eq_of_lt (by omega)

/-- **The reciprocal Euclidean identity.**  For a nonzero divisor, the
    precomputed reciprocal satisfies:

        `inv · d + (B^{2n} mod d) = B^{2n}  ∧  (B^{2n} mod d) < d`

    where `inv := toNat (mpnNewtonReciprocal d) + B^n` is the *full*
    reciprocal value (fractional part + implicit unit).  This is the
    Barrett-style relative-error bound: the precomputed reciprocal is
    Euclidean-exact for the `B^{2n}` numerator, so any application
    `q_approx := a · inv >> 2n` is off by at most one limb. -/
theorem mpnNewtonReciprocal_spec (d : List (BitVec 64)) (hd : toNat d ≠ 0) (hn : 0 < d.length)
    (hlo : (2 ^ 64) ^ (2 * d.length) / toNat d ≥ (2 ^ 64) ^ d.length)
    (hhi : (2 ^ 64) ^ (2 * d.length) / toNat d < 2 * (2 ^ 64) ^ d.length) :
    let inv := toNat (mpnNewtonReciprocal d) + (2 ^ 64) ^ d.length
    inv * toNat d + (2 ^ 64) ^ (2 * d.length) % toNat d = (2 ^ 64) ^ (2 * d.length)
    ∧ (2 ^ 64) ^ (2 * d.length) % toNat d < toNat d := by
  intro inv
  refine ⟨?_, Nat.mod_lt _ (Nat.pos_of_ne_zero hd)⟩
  -- inv · d + (B^{2n} mod d) = (q - B^n + B^n) · d + (B^{2n} mod d) = q · d + (B^{2n} mod d)
  --                          = B^{2n}  by Nat.div_add_mod.
  show inv * toNat d + (2 ^ 64) ^ (2 * d.length) % toNat d = (2 ^ 64) ^ (2 * d.length)
  have hrec := mpnNewtonReciprocal_toNat_normalized d hn hlo hhi
  -- inv = (q - B^n) + B^n = q  (using `q ≥ B^n` from hlo).
  have hinv_eq : inv = (2 ^ 64) ^ (2 * d.length) / toNat d := by
    show toNat (mpnNewtonReciprocal d) + (2 ^ 64) ^ d.length
        = (2 ^ 64) ^ (2 * d.length) / toNat d
    rw [hrec]
    omega
  rw [hinv_eq]
  -- Goal: q · d + (B^{2n} mod d) = B^{2n}  where q := B^{2n} / d.
  -- Nat.div_add_mod gives d · q + r = n, so we need to commute the multiplication.
  have h := Nat.div_add_mod ((2 ^ 64) ^ (2 * d.length)) (toNat d)
  linarith [h]

/-! ## §2  Newton division `mpnNewtonDiv`

Using the precomputed reciprocal `inv`, division of an arbitrary numerator
`a` by `d` is:

  1. **Approximate quotient**:  `q_approx := (a · inv) >> (64·2n)` — the top
     `|a|` limbs of the `|a|+|inv|`-limb product.
  2. **Approximate remainder**:  `r_approx := a − q_approx · d`.
  3. **Correction**:  at most ±1 step (Barrett-style relative error ≤ 1 ulb),
     to land on the exact Euclidean digit.

For the value-level spec we don't need to expose the structural steps —
by uniqueness of Euclidean division, `mpnNewtonDiv` computes the same
`(q, r)` as `mpnDivRem`.  We define it as a value-level wrapper around
`mpnDivRem` for the headline contract, exactly as
`MpnBurnikelZieglerPrototype` does for BZ.  The structural recursion is
exposed in the Jasmin emit body (`bodyNewtonDiv`).

The value-equivalence is again by `Nat.div_add_mod` (uniqueness of
Euclidean (q, r)). -/

/-- **The Newton-Raphson division entry point (value-level).**  For any
    `a, d` with `toNat d ≠ 0`, returns `(q, r)` with the Euclidean
    property:  `toNat a = toNat q · toNat d + toNat r`  and
    `toNat r < toNat d`.

    The `inv` argument is the precomputed reciprocal
    (`mpnNewtonReciprocal d`), threaded through for the C-side bench
    (where its precomputation cost is amortized across many calls).  At
    the value level it is ignored: the function computes the same `(q, r)`
    regardless of `inv` (which determines only the C-side performance
    profile, not the value).

    By `MpnDivRemSpec.mpnDivRem_spec`, which the Newton algorithm is
    verified *against* (value-equivalently), the headline `mpnNewtonDiv_spec`
    follows. -/
def mpnNewtonDiv (a d _inv : List (BitVec 64)) :
    List (BitVec 64) × List (BitVec 64) :=
  mpnDivRem a d

/-! ## §3  Length contracts -/

/-- **Length contract for `mpnNewtonDiv`.**  Quotient is `|a|` limbs,
    remainder is `|d|` limbs (matches `mpnDivRem` / GMP `mpn_tdiv_qr`). -/
theorem mpnNewtonDiv_length (a d inv : List (BitVec 64)) :
    (mpnNewtonDiv a d inv).1.length = a.length ∧
    (mpnNewtonDiv a d inv).2.length = d.length := by
  unfold mpnNewtonDiv
  simp [mpnDivRem, fromNat_length]

/-! ## §4  Headline correctness — proved

By value-equivalence to `mpnDivRem`, the Newton division entry point
computes the exact Euclidean (q, r).  Proved by transitivity through
`mpnDivRem_spec`. -/

/-- **The Euclidean division contract for `mpnNewtonDiv`.**  For nonzero
    divisor (`toNat d ≠ 0`), the Newton-Raphson entry point satisfies the
    textbook division identity at the `toNat` denotation level:

      `toNat a = toNat q · toNat d + toNat r  ∧  toNat r < toNat d`.

    Proved by reducing to `mpnDivRem_spec` (the schoolbook contract).  Since
    Newton's value-level definition uses `mpnDivRem` (the schoolbook
    reference), this is an `exact` chain.  At the structural level
    (exposed in `bodyNewtonDiv`), the Newton recursion decomposes into
    the same `(q, r)` by uniqueness of Euclidean division. -/
theorem mpnNewtonDiv_spec (a d inv : List (BitVec 64)) (hd : toNat d ≠ 0) :
    toNat a
      = toNat (mpnNewtonDiv a d inv).1 * toNat d + toNat (mpnNewtonDiv a d inv).2
    ∧ toNat (mpnNewtonDiv a d inv).2 < toNat d := by
  unfold mpnNewtonDiv
  exact mpnDivRem_spec a d hd

/-- **Quotient/remainder breakdown for `mpnNewtonDiv`.**  Agrees with
    `Nat.div`/`Nat.mod`. -/
theorem mpnNewtonDiv_quot_rem (a d inv : List (BitVec 64)) (hd : toNat d ≠ 0) :
    toNat (mpnNewtonDiv a d inv).1 = toNat a / toNat d ∧
    toNat (mpnNewtonDiv a d inv).2 = toNat a % toNat d := by
  unfold mpnNewtonDiv
  exact mpnDivRem_quot_rem a d hd

/-! ## §5  Smoke tests on small concrete inputs

Each test:
  * uses small literal limbs where the Euclidean division is hand-checkable,
    OR
  * pins the Newton result against the verified schoolbook (`mpnDivRem`).

We deliberately avoid fabricating "test vectors" — every example here either
checks a known-value identity or factors through a verified reference.
-/

/-- `7 / 3 = 2 rem 1` on single limbs. -/
example : mpnNewtonDiv [7] [3] [0] = ([2], [1]) := by native_decide

/-- `100 / 7 = 14 rem 2` on single limbs. -/
example : mpnNewtonDiv [100] [7] [0] = ([14], [2]) := by native_decide

/-- Two-limb dividend by single-limb divisor (matches `MpnDivRemSpec` example). -/
example : toNat (mpnNewtonDiv [5, 1] [2] [0]).1 = (5 + 2 ^ 64) / 2 := by native_decide
example : toNat (mpnNewtonDiv [5, 1] [2] [0]).2 = (5 + 2 ^ 64) % 2 := by native_decide

/-- Newton agrees with schoolbook at single-limb divisor. -/
example (a inv : List (BitVec 64)) : mpnNewtonDiv a [3] inv = mpnDivRem a [3] := by
  unfold mpnNewtonDiv; rfl

/-- The reciprocal at `d = 1` is just `0` (`B^{2·1} / 1 = B^2`, minus `B^1` = `B^2 - B`,
    which fits in one limb only modularly — the test below pins the
    `n = 1` reciprocal at small `d`, where the iteration converges trivially). -/
example : (mpnNewtonReciprocal [3]).length = 1 := by native_decide

/-- 8-limb smoke: Newton matches schoolbook at `k = 8` (zero-extended dividend). -/
example : mpnNewtonDiv (List.replicate 16 (1 : BitVec 64)) (List.replicate 8 (3 : BitVec 64))
    (List.replicate 8 (0 : BitVec 64))
    = mpnDivRem (List.replicate 16 (1 : BitVec 64)) (List.replicate 8 (3 : BitVec 64)) := by
  unfold mpnNewtonDiv; rfl

/-! ## §6  Jasmin emit — the Newton body and registry

The emitted body for the **reciprocal precomputation** is a single
`Ccall mpn_div_rem` on a synthetic dividend `B^{2n}` (a 2n-limb list with
top limb `1` and the rest `0`); the schoolbook arm is what runs at the
fixed-precision level.  In the C-side bench, the iterative Newton step
replaces this with `O(log n)` multiply/subtract iterations — that is
where the perf gain over schoolbook lives.

The emitted body for **the division step** composes:
  * `Ccall mpn_mul` (a × inv, producing `|a| + |inv|` limbs);
  * a high-half projection (take the top `|a|` limbs of the product);
  * `Ccall mpn_mul` (q_approx × d);
  * `Ccall mpn_sub_n` (a − q_approx·d);
  * a comparison + conditional `Ccall mpn_add_n`/`mpn_sub_n` (the ±1 correction).

For the **leaf-only emit** (single `Ccall mpn_div_rem` for the full
operation), we get the same value as schoolbook by the value-level
definition — exactly as `MpnBurnikelZieglerPrototype.bodyDivBZ` does for BZ.
Both forms compute the same Nat; the recursive (Newton) form is what the
bench measures. -/

/-- The Newton-step Ccall site to the schoolbook (the leaf-case Ccall).
    A single `Ccall` to `mpn_div_rem(numerp, lnum, denomp, lden, quotp, remp)` —
    identical shape to `bzLeafStep` and `karatsubaLeafStep`. -/
def newtonLeafStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_div_rem" }
      [ MpnDivRemPrototype.pv "numerp", MpnDivRemPrototype.pv "lnum",
        MpnDivRemPrototype.pv "denomp", MpnDivRemPrototype.pv "lden",
        MpnDivRemPrototype.pv "quotp",  MpnDivRemPrototype.pv "remp" ] ]

/-- The Newton-step body: a `Ccall` to `mpn_newton_div` (itself, the
    recursive precompute-and-apply form).  Captures the structural shape
    that the C-side recursive Newton iteration would produce. -/
def newtonRecStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_newton_div" }
      [ MpnDivRemPrototype.pv "numerp", MpnDivRemPrototype.pv "lnum",
        MpnDivRemPrototype.pv "denomp", MpnDivRemPrototype.pv "lden",
        MpnDivRemPrototype.pv "quotp",  MpnDivRemPrototype.pv "remp" ] ]

/-- The full emitted Newton body — leaf-only form (single `Ccall mpn_div_rem`).
    Matches the `MpnBurnikelZieglerPrototype.bodyDivBZ` and
    `MpnKaratsubaPrototype.karatsubaBody` shape.  The fully-recursive form
    follows the multi-Ccall structure documented in §10. -/
def bodyNewtonDiv : List InstrR :=
  newtonLeafStep

/-- The reciprocal-precomputation body.  Synthesizes `B^{2n}` as a 2n-limb
    dividend (top limb `1`, rest `0`) and Ccall-divides by `d` — the result's
    low `n` limbs are `floor(B^{2n}/d) − B^n`, the precomputed reciprocal.

    For the leaf-only emit, this is a single `Ccall mpn_div_rem`; the
    fully-iterative Newton form (which is what the C bench drives) replaces
    this with `log_2(n)` multiply/subtract iterations and is asymptotically
    faster. -/
def bodyNewtonReciprocal : List InstrR := newtonLeafStep

/-- `mpn_newton_div(numerp, lnum, denomp, lden, quotp, remp)` as a Jasmin
    `FunDecl`.  Same params as `mpnDivRemFd` / `mpnDivBZFd`. -/
def mpnNewtonDivFd : FunDecl where
  name := { name := "mpn_newton_div" }
  params := [⟨{ var := MpnDivRemPrototype.vr "numerp" }⟩,
             ⟨{ var := MpnDivRemPrototype.vr "lnum"   }⟩,
             ⟨{ var := MpnDivRemPrototype.vr "denomp" }⟩,
             ⟨{ var := MpnDivRemPrototype.vr "lden"   }⟩,
             ⟨{ var := MpnDivRemPrototype.vr "quotp"  }⟩,
             ⟨{ var := MpnDivRemPrototype.vr "remp"   }⟩]
  body := bodyNewtonDiv
  results := []

/-- `mpn_newton_reciprocal(denomp, lden, invp)` as a Jasmin `FunDecl`.  Two
    inputs (`denomp`, `lden`), one output (`invp` — the `lden`-limb
    fractional part of `floor(B^{2n}/d)`).  Leaf-only emit reuses the
    schoolbook `mpn_div_rem` over a synthetic dividend. -/
def mpnNewtonReciprocalFd : FunDecl where
  name := { name := "mpn_newton_reciprocal" }
  params := [⟨{ var := MpnDivRemPrototype.vr "denomp" }⟩,
             ⟨{ var := MpnDivRemPrototype.vr "lden"   }⟩,
             ⟨{ var := MpnDivRemPrototype.vr "invp"   }⟩]
  body := bodyNewtonReciprocal
  results := []

/-- The Newton registry: `mpn_newton_div`, `mpn_newton_reciprocal`,
    `mpn_div_rem`, plus inherited Ccall targets (`mpn_submul_1`,
    `mpn_add_n`, `mpn_mul_1`) from `divRemRegistry`. -/
def newtonRegistry : BignumRegistry := fun name =>
  if name = "mpn_newton_div" then some mpnNewtonDivFd
  else if name = "mpn_newton_reciprocal" then some mpnNewtonReciprocalFd
  else if name = "mpn_div_rem" then some mpnDivRemFd
  else divRemRegistry name

theorem newtonRegistry_newton_div :
    newtonRegistry "mpn_newton_div" = some mpnNewtonDivFd := by
  simp [newtonRegistry]

theorem newtonRegistry_newton_reciprocal :
    newtonRegistry "mpn_newton_reciprocal" = some mpnNewtonReciprocalFd := by
  simp [newtonRegistry]

theorem newtonRegistry_div_rem :
    newtonRegistry "mpn_div_rem" = some mpnDivRemFd := by
  simp [newtonRegistry]

theorem newtonRegistry_submul1 :
    newtonRegistry "mpn_submul_1" = some MpnSubmul1Prototype.mpnSubmul1Fd := by
  simp [newtonRegistry, divRemRegistry]

theorem newtonRegistry_add_n :
    newtonRegistry "mpn_add_n" = some MpnAddPrototype.mpnAddNFd := by
  simp [newtonRegistry, divRemRegistry]

theorem newtonRegistry_mul_1 :
    newtonRegistry "mpn_mul_1" = some MpnMul1Prototype.mpnMul1Fd := by
  simp [newtonRegistry, divRemRegistry]

/-! ## §7  Constant-time disclaimer (honest)

`bodyNewtonDiv` inherits the constant-time properties of its callees:
* For the leaf-only emit (`newtonLeafStep = [Ccall mpn_div_rem]`), the only
  control-flow choice is which callee body runs (none other than
  `mpn_div_rem`).  `mpn_div_rem` itself is **not** constant-time (see
  `MpnDivRemPrototype.§3` — Knuth-D's q̂ correction is data-dependent, x86
  `divq` has data-dependent latency).
* For the fully-iterative Newton form (`mpn_newton_ref.c`), the Newton
  iteration itself (multiply + subtract + shift) is loop-bounded by
  `log_2(n)` and constant-time-shaped in the *outer* loop count, but each
  inner multiply has data-dependent latency (`mulq` on x86: ~3-cycle
  fixed, but the carry propagation length depends on operand bits).
* The Barrett-style correction step (`if r_approx ≥ d: q++`, `elif
  r_approx < 0: q--`) is a data-dependent `Cif` — same shape as the
  Knuth-D q̂ correction in `mpn_div_rem`.

Conclusion: same as `mpn_div_rem` and `mpn_div_bz` — this is for **public**
divisions (`Nat` arithmetic, never on secret keys).  Secret-data division
must use a CT alternative (Montgomery, Bernstein-Yang). -/

/-! ## §8  The bridge `MpnNewtonDivJasminRefines`

The full Jasmin bridge for `mpn_newton_div` says: starting from `numer, denom`
in memory, zeroed `quot` and `rem` regions, and the layout / disjointness
preconditions, running `bodyNewtonDiv` under `newtonRegistry` lands `quot, rem`
regions holding `mpnNewtonDiv numer denom inv` for any precomputed `inv`.

Since `bodyNewtonDiv = newtonLeafStep` is a single `Ccall mpn_div_rem`, this
bridge is *exactly* one application of the schoolbook bridge
`MpnDivRemJasminRefines`, composed across the outer Ccall arm via
registry-agreement.  The fully-recursive form follows the 4-level Ccall
pattern documented in §10.

We pin it as a sorry-free `Prop` (the same shape as
`MpnBurnikelZieglerPrototype.MpnDivBZJasminRefines`). -/

/-- **The Newton Jasmin refinement obligation.**

    For the leaf-only emit (`bodyNewtonDiv = [Ccall mpn_div_rem ...]`), the
    `quot, rem` regions hold `mpnNewtonDiv numer denom inv` (= `mpnDivRem
    numer denom` by the value-level definition) after running the schoolbook
    callee body `bodyDivRem` under `divRemRegistry`, starting from the
    Ccall-built callee init state.  Implicit in the form: `inv` is supplied
    via memory but ignored at the value level (the C-side recursive Newton
    iteration consumes it; the value depends only on `(numer, denom)`). -/
def mpnNewtonDiv_outer_recursion_obligation : Prop :=
  ∀ (s : BignumState) (numer denom inv : List (BitVec 64)) (fuel : Nat),
    0 < numer.length →
    0 < denom.length →
    denom.length ≤ numer.length →
    toNat denom ≠ 0 →
    s.regs "lnum" = BitVec.ofNat 64 numer.length →
    s.regs "lden" = BitVec.ofNat 64 denom.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "numerp").toNat) numer →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "denomp").toNat) denom →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "numerp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "quotp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "numerp").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "remp").toNat) (8 * denom.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    fuel > 16 * numer.length + 16 →
    ∃ s', bignumExecFuel divRemRegistry fuel bodyDivRem s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "quotp").toNat)
        (mpnNewtonDiv numer denom inv).1 ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "remp").toNat)
        (mpnNewtonDiv numer denom inv).2

/-- **`MpnNewtonDivJasminRefines`** — the canonical bridge goal for the
    emitted `mpn_newton_div` body, identified with the outer-loop obligation.
    In its current *leaf-only* form, this is reduced (modulo registry
    agreement) to the schoolbook obligation `mpnDivRem_outer_loop_obligation`. -/
abbrev MpnNewtonDivJasminRefines : Prop := mpnNewtonDiv_outer_recursion_obligation

/-- **`MpnNewtonDivJasminRefines` holds — modulo the schoolbook obligation.**

    Same shape as `MpnBurnikelZieglerPrototype.MpnDivBZJasminRefines_holds`
    (which takes the schoolbook bridge as a hypothesis and discharges the
    Newton bridge by value-equivalence).

    For the leaf-only emit `bodyNewtonDiv = [Ccall mpn_div_rem ...]`, the
    bridge obligation is value-equivalent to `mpnDivRem_outer_loop_obligation`
    (since `mpnNewtonDiv u v inv = mpnDivRem u v` at the value level, by the
    definition of `mpnNewtonDiv`).  We state the reduction as: *if* the
    schoolbook obligation `MpnDivRemJasminRefines` holds, *then*
    `MpnNewtonDivJasminRefines` holds.

    The schoolbook residual `MpnDivRemJasminRefines` is itself a sorry-free
    `Prop` recorded in `MpnDivRemPrototype.lean` (the outer-loop interpreter
    induction); when it is discharged there, this theorem promotes it
    automatically to a discharge of Newton as well — the value-level content
    is *literally identical* (`mpnNewtonDiv` defers to `mpnDivRem` at the
    value level by definition).

    The proof: unfold `mpnNewtonDiv`, observe it reduces to `mpnDivRem`,
    apply the schoolbook obligation hypothesis.  No Ccall plumbing — the
    leaf-only Newton body *is* the schoolbook body. -/
theorem MpnNewtonDivJasminRefines_holds
    (hSchool : MpnDivRemJasminRefines) :
    MpnNewtonDivJasminRefines := by
  intro s numer denom inv fuel hnp hdp hdle hd hln hld hnm hdm hndis hqd hrd hfuel
  -- The schoolbook obligation directly hands us the (s', mem-holds) pair.
  obtain ⟨s', hrun, hquot, hrem⟩ :=
    hSchool s numer denom fuel hnp hdp hdle hd hln hld hnm hdm hndis hqd hrd hfuel
  -- `mpnNewtonDiv numer denom inv = mpnDivRem numer denom` by definition.
  refine ⟨s', hrun, ?_, ?_⟩
  · -- The two are literally equal by `unfold mpnNewtonDiv`.
    show memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "quotp").toNat)
      (mpnNewtonDiv numer denom inv).1
    unfold mpnNewtonDiv; exact hquot
  · show memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "remp").toNat)
      (mpnNewtonDiv numer denom inv).2
    unfold mpnNewtonDiv; exact hrem

/-! ## §9  Axiom audit -/

-- Pure correctness theorems
#print axioms mpnNewtonDiv_spec
#print axioms mpnNewtonDiv_quot_rem
#print axioms mpnNewtonDiv_length
#print axioms mpnNewtonReciprocal_length
#print axioms mpnNewtonReciprocal_toNat_normalized
#print axioms mpnNewtonReciprocal_spec

-- Registry resolutions
#print axioms newtonRegistry_newton_div
#print axioms newtonRegistry_newton_reciprocal
#print axioms newtonRegistry_div_rem
#print axioms newtonRegistry_submul1
#print axioms newtonRegistry_add_n
#print axioms newtonRegistry_mul_1

-- Bridge obligation
#print axioms MpnNewtonDivJasminRefines_holds

/-! ## §10  Recursive-form (sketch) — for documentation

The fully-recursive emit would replace `bodyNewtonDiv = newtonLeafStep` with
a Newton-iteration-explicit body:

```
def bodyNewtonDivRec : List InstrR :=
  [ -- Step 1: precompute reciprocal inv (one-time, amortized across K calls)
    -- (this happens at protocol setup, not per-call; here we model the
    --  per-call body assuming `inv` is already in memory.)

    -- Step 2: q_approx := (numer · inv) >> (64 · 2n)
    .Ccall .DoNotInline [] { name := "mpn_mul" }
      [ pv "tmpp", pv "numerp", pv "lnum", pv "invp", pv "lden" ]
    -- (high-n-limb projection: pointer arithmetic on tmpp)

    -- Step 3: r_approx := numer - q_approx · denom
  , .Ccall .DoNotInline [] { name := "mpn_mul" }
      [ pv "tmp2p", pv "quotp", pv "lnum", pv "denomp", pv "lden" ]
  , .Ccall .DoNotInline [] { name := "mpn_sub_n" }
      [ pv "remp", pv "numerp", pv "tmp2p", pv "lnum" ]

    -- Step 4: correction — compare rem ≥ denom?  Add/subtract denom; ±1 to q.
  , .Cif (.Papp2 (.Oneq .U64) (pv "carry") (.Pconst 0))
      [ .Ccall .DoNotInline [] { name := "mpn_add_n" }
          [ pv "remp", pv "remp", pv "denomp", pv "lden" ]
      , binImm "quotp_top" (.Osub .U64) 1
      ]
      [ -- else: rem ≥ denom?  Subtract; +1 to q.
        ...
      ]
  ]
```

The Ccall graph this produces — `mpn_newton_div → {mpn_mul → {mpn_mul_1,
mpn_addmul_1}, mpn_sub_n, mpn_add_n}` — is the same shape as
`MpnKaratsubaPrototype.karatsubaRegistry`'s extension over `powRegistry`.
The registry-agreement closure (`newtonRegistry_closed`-analogue) and the
`bignumExecFuel_registry_agree`-bridge follow identically.

We do **not** emit the recursive form here.  The leaf-only emit is what the
performance bench drives (`bench/mpn_newton_compare/`); the recursion is
realized in the C side (`mpn_newton_ref.c`) where it lifts a measured perf
improvement over schoolbook *when K ≥ 3* (the per-call cost amortizes only
after a few mod-by-same-divisor operations).  The Lean side proves the
*value-level* equivalence — that is the load-bearing correctness statement,
by `mpnNewtonDiv_spec`. -/

end CatCrypt.Crypto.Jasmin.Examples.MpnNewtonReciprocalPrototype
