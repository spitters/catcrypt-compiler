/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Mul
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontPallas
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontVesta
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontSecp256k1
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontCurve25519
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBN254
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontP256
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontP384
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls12381
public import Mathlib.Data.ZMod.Basic

/-!
# The generic, table-driven curve-field registry (fractalyze `!field.pf<p>`)

The per-curve base-field relational fronts — `RelationalFrontBls377{Add,Mul}`,
`RelationalFrontPallas`, `RelationalFrontVesta`, `RelationalFrontSecp256k1`,
`RelationalFrontCurve25519`, `RelationalFrontBN254`, `RelationalFrontP256`,
`RelationalFrontP384`, `RelationalFrontBls12381` — each hand-instantiate **one
and the same** generic `k`-limb machinery (`KLimbPrime`/`KLimbPrimeMul`,
`encMLK`, `mlAddModK`/`mlMulMod`, and the commuting squares
`encMLK_add_commutes`/`encMLK_mul_commutes`) at a different prime `q`, limb
count `k`, modulus limb-vector, and Barrett reciprocal. Concretely, **every**
per-curve `<curve>_add_commutes` is literally

```
  encMLK_add_commutes <curve>KLimbPrime a b
```

and every `<curve>_mul_commutes` is literally

```
  encMLK_mul_commutes <curve>KLimbPrimeMul a b
```

(see e.g. `pallas_add_commutes`/`pallas_mul_commutes`). The per-curve *files*
add nothing to the proof: they only package the curve constants (`<curve>Q`,
`<curve>Limbs`, `<curve>MuLimbs`) into a `KLimbPrimeMul` record and discharge
the three/four numeric side conditions by `norm_num`.

This module makes that parametricity **explicit and table-driven**, matching
fractalyze's design: one generic prime-field op `!field.pf<p>` plus a
*curve-constant table*, instead of one bespoke op per curve. A new curve is a
new `KLimbPrimeMul` record plus a one-line application of the generic theorem —
**no new proof file**.

## What this module provides

* `registry_add_commutes` / `registry_mul_commutes` — the generic commuting
  squares, **named as the registry interface**. These are definitional aliases
  of `encMLK_add_commutes` / `encMLK_mul_commutes` (the genuinely parametric
  theorems, which already existed): each is parametric over a `KLimbPrime` /
  `KLimbPrimeMul` *datum* — i.e. over a row of the curve table.
* `curveTable : List KLimbPrimeMul` — the registry datum table: the nine
  base-field primes the repo currently realizes, each a `KLimbPrimeMul` record
  carrying its prime, limb count, modulus limb-vector, and product-width Barrett
  reciprocal.
* `registry_covers_add` / `registry_covers_mul` — the **table-driven coverage**
  statements: `∀ Q ∈ curveTable, ∀ a b : ZMod Q.q, registry_{add,mul}_commutes`
  holds. The whole table is discharged by a single application of the generic
  theorem — there is no per-row proof.
* `instances_are_registry_applications` — a demonstration that ≥2 existing
  per-curve commuting squares (`bls377_*`, `pallas_*`) are *the same theorem*
  as the registry interface applied to that curve's table row, witnessed by
  `rfl`. This is the consolidation: the bespoke per-curve files are instances
  of one parametric construction.

The `KLimbPrimeMul` structure (`RelationalFrontBls377Mul`) **is** the registry
datum: it already captures "a field is a prime + its limb count + its modulus
limb-vector + its product-width reciprocal" as data. This module names that
fact and exhibits the table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The registry interface: the generic, datum-parametric commuting squares

`KLimbPrime` / `KLimbPrimeMul` are the registry data. The genuinely parametric
commuting-square theorems `encMLK_add_commutes` / `encMLK_mul_commutes` already
exist (in `RelationalFrontBls377{Add,Mul}`); here we name them as the registry
interface so a new curve's correctness is *exactly* one application. -/

/-- **The registry ADD commuting square** (= `encMLK_add_commutes`). For any
    curve-field datum `Q : KLimbPrime`, the abstract `ZMod Q.q` add `a + b`,
    serialized by the `k`-limb encoding `encMLK Q.q Q.k`, equals the emitted
    multi-limb reducing kernel `mlAddModK` on the serialized operands, read
    through `bignumVal`. Parametric over the table row `Q`. -/
theorem registry_add_commutes (Q : KLimbPrime) (a b : ZMod Q.q) :
    (a + b).val
      = bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) :=
  encMLK_add_commutes Q a b

/-- **The registry MUL commuting square** (= `encMLK_mul_commutes`). For any
    curve-field datum `Q : KLimbPrimeMul`, the abstract `ZMod Q.q` multiply
    `a * b`, serialized by `encMLK Q.q Q.k`, equals the emitted multi-limb
    Barrett-reducing kernel `mlMulMod` on the serialized operands, read through
    `bignumVal`. Parametric over the table row `Q`. -/
theorem registry_mul_commutes (Q : KLimbPrimeMul) (a b : ZMod Q.q) :
    (a * b).val
      = bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) :=
  encMLK_mul_commutes Q a b

/-! ## 2. The curve-constant table

The registry datum table: the nine base-field primes the repo currently
realizes relationally, each a `KLimbPrimeMul` row. A new curve = one more entry
here (a `KLimbPrimeMul` record) — no new proof. -/

/-- **The curve-field registry table.** Each entry is a `KLimbPrimeMul`
    carrying a base-field prime `q`, its limb count `k`, its modulus
    limb-vector `ql`, and its product-width Barrett reciprocal `muTwo`. This is
    the table-driven analogue of fractalyze's `!field.pf<p>` curve-constant
    table: the nine rows are the nine curves, and `registry_{add,mul}_commutes`
    realizes the field ops generically over any row. -/
def curveTable : List KLimbPrimeMul :=
  [ bls377KLimbPrimeMul    -- bls12_377 base field (k = 6, 377-bit)
  , bls381KLimbPrimeMul    -- bls12_381 base field
  , bn254KLimbPrimeMul     -- BN254 base field
  , pallasKLimbPrimeMul    -- Pallas base field (k = 4)
  , vestaKLimbPrimeMul     -- Vesta base field (k = 4)
  , secpKLimbPrimeMul      -- secp256k1 base field
  , c25519KLimbPrimeMul    -- Curve25519 base field
  , p256KLimbPrimeMul      -- NIST P-256 base field
  , p384KLimbPrimeMul ]    -- NIST P-384 base field

/-! ## 3. Table-driven coverage

The whole table is realized by a *single* application of the generic theorem —
there is no per-row proof. This is the consolidation: the per-curve files are
not needed for correctness, only for naming the constants. -/

/-- **Table-driven ADD coverage.** Every entry of the registry table satisfies
    the registry ADD commuting square. Discharged generically: the field add
    for *any* table row reduces to `registry_add_commutes` applied to that row,
    so the whole table is covered without a per-row proof. -/
theorem registry_covers_add :
    ∀ Q ∈ curveTable, ∀ a b : ZMod Q.q,
      (a + b).val = bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) :=
  fun Q _ a b => registry_add_commutes Q.toKLimbPrime a b

/-- **Table-driven MUL coverage.** Every entry of the registry table satisfies
    the registry MUL commuting square. Discharged generically: the field
    multiply for *any* table row reduces to `registry_mul_commutes` applied to
    that row, so the whole table is covered without a per-row proof. This is the
    table-driven `!field.pf<p>` realization: one theorem, all nine curves. -/
theorem registry_covers_mul :
    ∀ Q ∈ curveTable, ∀ a b : ZMod Q.q,
      (a * b).val
        = bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) :=
  fun Q _ a b => registry_mul_commutes Q a b

/-! ## 4. The per-curve files are instances of the registry

The consolidation, witnessed: the bespoke per-curve commuting squares are *the
same theorem* as the registry interface applied to that curve's table row.
Shown by `rfl` for ≥2 curves (bls12_377 and Pallas), proving that the per-curve
files add no proof content — they are one-line applications of the generic
construction. -/

/-- **Consolidation demonstration.** Each existing per-curve commuting square is
    definitionally the registry interface applied to that curve's `KLimbPrimeMul`
    row — exhibited here for bls12_377 and Pallas (ADD and MUL). Because the
    proofs are equal *by `rfl`*, the per-curve files (`RelationalFrontPallas`,
    `RelationalFrontBls377Mul`, …) are genuinely instances of one parametric
    construction: a new curve needs only a new table row, not a new proof. -/
theorem instances_are_registry_applications :
    (∀ a b : ZMod bls377Q,
        bls377_add_commutes a b
          = registry_add_commutes bls377KLimbPrimeMul.toKLimbPrime a b)
    ∧ (∀ a b : ZMod bls377Q,
        bls377_mul_commutes a b = registry_mul_commutes bls377KLimbPrimeMul a b)
    ∧ (∀ a b : ZMod pallasQ,
        pallas_add_commutes a b
          = registry_add_commutes pallasKLimbPrimeMul.toKLimbPrime a b)
    ∧ (∀ a b : ZMod pallasQ,
        pallas_mul_commutes a b = registry_mul_commutes pallasKLimbPrimeMul a b) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end CatCrypt.Crypto.SecureCompilation.RelationalFront
