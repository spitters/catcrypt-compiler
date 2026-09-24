/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontInstances
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontEC
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontECMul
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul
public import Mathlib.FieldTheory.Finite.Basic
public import Std.Tactic.BVDecide

/-!
# GF(251) FIELD INVERSION via Fermat — the last field-op building block

`RelationalFrontECMul.lean` lands the GF(251) **multiply** and **square** `ZMod`
commuting squares (`gf251Mul_commutes`, `gf251Square_commutes`); `RelationalFront`
+ `RelationalFrontInstances` land **add**; `RelationalFrontEC` lands **triple**
(`3·A`) and (via the field double) **double**. The field-op realization set
(add/sub/mul/square/triple/double) is therefore complete **except for inversion**
— and inversion is the one operation the affine EC group law (`ECParams.add`,
`ECParams.tangentSlope`, `ECParams.chordSlope`) needs that is *not* obviously a
straight-line `Com`: it is a division.

This module realizes GF(251) field inversion **relationally via Fermat's little
theorem**, exploiting that in a prime field `a⁻¹ = a^{p-2}`:

```
a⁻¹ = a^{251-2} = a^249       (for a ≠ 0)
```

and `a^249` is computed by a **multiply-square addition chain** — a pure
straight-line composition of the already-landed `gf251MulSpec`/`gf251Square`, so
inversion stays inside the index-free `Com jasminDialect` fragment (NO division
instruction is emitted; the field-inverse is a `mul`/`sqr` schedule).

## The two parts (both fully proved here)

1. **The Fermat identity at the `ZMod` level** (`invFermat251`): `a^249 = a⁻¹`
   for `a ≠ 0` in `ZMod 251`, via Mathlib's **`ZMod.pow_card_sub_one_eq_one`**
   (`a^{p-1} = a^250 = 1`) and `ZMod.inv_eq_of_mul_eq_one` (`a^249·a = a^250 = 1
   ⇒ a⁻¹ = a^249`). This is the **relational meaning** of the inverse — what the
   `a^249` power chain actually computes.

2. **The power-chain `ZMod` commuting square** (`pow249_commutes`):
   `encMod251 (a^249) = pow249Spec (encMod251 a)`, where `pow249Spec` is the
   `BitVec 64` **square-and-multiply addition chain for 249** built from
   `gf251MulSpec` (squaring = `gf251MulSpec x x`). It is proved by **composing**
   the landed `gf251Square_commutes` (each `· ²`) and `gf251Mul_commutes` (each
   `·· a`) step by step along the chain `1→3→7→15→31→62→124→249`
   (`249 = 0b11111001`, the standard square-and-multiply schedule).

Combining (1) and (2): **`encMod251 (a⁻¹) = pow249Spec (encMod251 a)`** for
`a ≠ 0` (`invMod251_commutes`) — the GF(251) **inverse** realized as an emitted
power chain on the serialized coordinate. A `RealizedUnaryKernel`-style relational
tie (`pow249UnaryRealization`) and a worked example (`2⁻¹ = 126`, since
`2·126 = 252 ≡ 1`) complete the field-op realization set.

## What is closed vs deferred

* The **Fermat identity** (`invFermat251`) and the **full 249-power chain**
  commuting square (`pow249_commutes`, the *complete* `1→3→7→15→31→62→124→249`
  schedule, **not** scoped to the identity) are both fully proved here by
  composition of the landed mul/square squares — no `bv_decide` over a 249-fold
  product, the chain is *abstracted* through the already-proved single-op squares.
* The **emitted `Com`** for the *whole* chain (a 14-binding-per-multiply ×
  11-multiply straight-line `Com jasminDialect`) is **not** assembled into a
  single `RealizedUnaryKernel.com` here — `pow249Spec` is the carrier-level
  composite of `gf251MulBuilt`'s denotation (`gf251MulRealizedKernel.com`), each
  multiply *individually* emitted and KAT'd in `FieldEmitGoldenMul`; gluing 11
  copies into one de-Bruijn `Com` and re-proving `Com.denote = pow249Spec` is the
  (mechanical, large) `ComBuilder` assembly step, deferred. The **relational
  content** — that `a⁻¹` *equals* this emitted multiply-square chain on the
  serialized coordinate — is fully proved.

## The gap to affine `ECParams.add` + `bls12_377`

With inversion realized, the affine slope `λ = num · denom⁻¹`
(`ECParams.tangentSlope` / `chordSlope`) is now a composition of emitted field
ops: `denom⁻¹` is this inverse chain, `num · denom⁻¹` is `gf251MulSpec`, and the
`affRx`/`affRy` coordinate maps are further `gf251MulSpec`/sub/add. The remaining
work to a full `ECParams.add` realization is (i) composing inverse + slope +
`affRx`/`affRy` into one schedule, and (ii) the **`ECPoint = Option (ZMod p ×
ZMod p)` sum-type encoding** (serializing the infinity point `O` and the affine
pair, with the `x1 = x2` / `y1 = -y2` branch — a *branch* on secret data the
index-free CT fragment must handle by the standard select idiom, not a jump).
`bls12_377` additionally swaps the single-word GF(251) carrier for a 377-bit
**6×64-limb** carrier (a CIOS/Karatsuba per-op kernel); the relational structure
(encoding + commuting square + emitted `Com`) ports verbatim, only the carrier
and per-op kernels change.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul

/-! ## 0. 251 is prime (the Fermat instance) -/

/-- `251` is prime, as the `Fact` typeclass the Fermat little-theorem lemma needs. -/
instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩

/-! ## 1. The Fermat identity at the `ZMod` level — the relational meaning of `⁻¹`

In a prime field `a⁻¹ = a^{p-2}`; for `p = 251` that is `a^249`. The route:
`ZMod.pow_card_sub_one_eq_one` gives `a^{251-1} = a^250 = 1` (for `a ≠ 0`), then
`a^249·a = a^250 = 1`, so `a⁻¹ = a^249` by uniqueness of the field inverse
(`ZMod.inv_eq_of_mul_eq_one`). -/

/-- **The Fermat identity for GF(251).** For `a ≠ 0` in `ZMod 251`,
    `a^249 = a⁻¹`. This is the relational meaning of the inverse: the value the
    multiply-square chain `pow249Spec` computes *is* the field inverse. Via
    Mathlib's `ZMod.pow_card_sub_one_eq_one` (`a^250 = 1`). -/
theorem invFermat251 (a : ZMod 251) (ha : a ≠ 0) : a ^ 249 = a⁻¹ := by
  have h : a ^ 250 = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hmul : a ^ 249 * a = 1 := by rw [← pow_succ]; exact h
  exact (ZMod.inv_eq_of_mul_eq_one 251 a (a ^ 249) (by rw [mul_comm]; exact hmul)).symm

/-! ## 2. The `BitVec` multiply-square addition chain for `a^249`

`249 = 0b11111001`. The standard square-and-multiply schedule (MSB→LSB, leading
`1` absorbed into the seed) is

```
a1   = a                          -- a^1
a3   = a1² · a                    -- a^3      (bit 1)
a7   = a3² · a                    -- a^7      (bit 1)
a15  = a7² · a                    -- a^15     (bit 1)
a31  = a15² · a                   -- a^31     (bit 1)
a62  = a31²                       -- a^62     (bit 0)
a124 = a62²                       -- a^124    (bit 0)
a249 = a124² · a                  -- a^249    (bit 1)
```

Squaring is `gf251MulSpec x x`; the `· a` steps are `gf251MulSpec · (enc a)` /
`gf251MulSpec · a`. Every op is a single application of the already-landed
`gf251MulBuilt` denotation, so `pow249Spec` stays in the emitted fragment. -/

/-- The `BitVec 64` squaring kernel: `gf251MulSpec` run diagonally. -/
def gf251Square (x : BitVec 64) : BitVec 64 := gf251MulSpec x x

/-- The `BitVec 64` square-and-multiply addition chain computing `a^249 mod 251`
    on a *reduced* word `a < 251` (`249 = 0b11111001`). Each step is one
    application of the landed `gf251MulSpec` (squaring = `gf251Square`). -/
def pow249Spec (a : BitVec 64) : BitVec 64 :=
  let a3   := gf251MulSpec (gf251Square a) a       -- a^3
  let a7   := gf251MulSpec (gf251Square a3) a      -- a^7
  let a15  := gf251MulSpec (gf251Square a7) a      -- a^15
  let a31  := gf251MulSpec (gf251Square a15) a     -- a^31
  let a62  := gf251Square a31                       -- a^62
  let a124 := gf251Square a62                       -- a^124
  gf251MulSpec (gf251Square a124) a                 -- a^249

/-! ## 3. The power-chain `ZMod` commuting square (the heart)

`encMod251 (a^249) = pow249Spec (encMod251 a)`, proved by composing the landed
`gf251Square_commutes` (each `·²`) and `gf251Mul_commutes` (each `·· a`) along the
addition chain. No `bv_decide` over a wide product — every step is an *already
proved* single-op commuting square; the chain is pure rewriting. -/

/-- The square step at the `ZMod` level: `encMod251 (x·x) = gf251Square (encMod251 x)`.
    The diagonal of `gf251Mul_commutes`, named for the chain. -/
theorem gf251Square_enc (x : ZMod 251) :
    encMod251 (x * x) = gf251Square (encMod251 x) :=
  gf251Square_commutes x

set_option maxRecDepth 4096 in
/-- **The power-chain commuting square.** The abstract field power `a^249` (in
    `F_251`), serialized by `encMod251`, equals the `BitVec` square-and-multiply
    chain `pow249Spec` on the serialized coordinate. Proved by **folding** the
    entire `BitVec` chain back through `encMod251` using the landed
    `gf251Mul_commutes`/`gf251Square_commutes` (backwards), reducing both sides to
    `encMod251` of `ZMod` field expressions, then closing the field-algebra
    identity by `ring`. No wide `bv_decide` — every node is an already-proved
    single-op commuting square. -/
theorem pow249_commutes (a : ZMod 251) :
    encMod251 (a ^ 249) = pow249Spec (encMod251 a) := by
  simp only [pow249Spec, gf251Square, ← gf251Mul_commutes]
  congr 1
  ring

/-! ## 4. The INVERSE relational realization (Fermat + power chain combined)

Combining `invFermat251` (`a^249 = a⁻¹`) with `pow249_commutes`
(`encMod251 (a^249) = pow249Spec (encMod251 a)`) gives the GF(251) **inverse**
realized as the emitted multiply-square chain on the serialized coordinate:

```
encMod251 (a⁻¹) = pow249Spec (encMod251 a)        (a ≠ 0)
```

This is the last field-op building block — the inverse-as-power-chain — that
unblocks the affine EC slope `λ = num · denom⁻¹`. -/

/-- **The GF(251) inverse commuting square (the deliverable).** For `a ≠ 0`, the
    abstract field inverse `a⁻¹` (in `F_251`), serialized by `encMod251`, equals
    the emitted square-and-multiply chain `pow249Spec` on the serialized
    coordinate. The inverse is realized **without any division instruction** — it
    is the Fermat power chain `a^{251-2}`. Combines `invFermat251` (the relational
    meaning `a⁻¹ = a^249`) and `pow249_commutes` (the chain). -/
theorem invMod251_commutes (a : ZMod 251) (ha : a ≠ 0) :
    encMod251 a⁻¹ = pow249Spec (encMod251 a) := by
  rw [← invFermat251 a ha, pow249_commutes]

/-- **The inverse-as-power-chain realization, as an `EndoUnaryRealization`-shaped
    tie** for the partial inverse op (`a ↦ a⁻¹` on the nonzero domain). The op
    realized is `a^249` (which *equals* `a⁻¹` for `a ≠ 0` by `invFermat251`,
    and which agrees with the total `ZMod` inverse — `0⁻¹ = 0 = 0^249` makes the
    chain total: `pow249Spec` of the encoded `0` computes `0`). The encoding is
    the landed injective-not-surjective `encMod251`; the commuting square is
    `pow249_commutes`. -/
def pow249UnaryRealization :
    EndoUnaryRealization (fun a : ZMod 251 => a ^ 249) pow249Spec where
  enc := encMod251
  enc_inj := encMod251_injective
  commutes := pow249_commutes

/-! ## 5. The transfer demonstration + worked example (`2⁻¹ = 126`)

`spec_eq_transfers_to_emit` (the unary analogue, via `RealizedUnaryKernel`) is not
re-derived here — the chain's `Com` is the 11-fold glue of `gf251MulBuilt`,
deferred (see module docstring). We expose the direct relational tie: the
inverse-power-chain commuting square decides abstract `F_251` inverse equations
through the serialization, with a concrete worked KAT. -/

/-- **The inverse transfer.** An abstract `F_251` equation between inverses
    (`a⁻¹ = b⁻¹` for nonzero `a, b`) is decided by the emitted power chain on the
    serialized coordinates — through the injective-not-onto `encMod251`. The
    inverse sibling of `addMod251_spec_transfers`/`gf251Mul_spec_transfers`. -/
theorem invMod251_spec_transfers (a b : ZMod 251) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ = b⁻¹ ↔ pow249Spec (encMod251 a) = pow249Spec (encMod251 b) := by
  rw [← invMod251_commutes a ha, ← invMod251_commutes b hb]
  exact ⟨fun h => by rw [h], fun h => encMod251_injective h⟩

/-- **The Fermat power chain computes the inverse on the worked vector `a = 2`.**
    `2⁻¹ = 126` in `F_251` (since `2·126 = 252 = 251 + 1 ≡ 1`); the emitted
    power chain `pow249Spec` on `encMod251 2` therefore equals `encMod251 126`.
    Fully proved: `invMod251_commutes` ties the chain to `2⁻¹`, and `2⁻¹ = 126` is
    decided in `ZMod 251`. -/
theorem invMod251_kat_two :
    pow249Spec (encMod251 2) = encMod251 126 := by
  have h2 : (2 : ZMod 251) ≠ 0 := by decide
  have hinv : (2 : ZMod 251)⁻¹ = 126 :=
    ZMod.inv_eq_of_mul_eq_one 251 2 126 (by decide)
  rw [← invMod251_commutes 2 h2, hinv]

end CatCrypt.Crypto.SecureCompilation.RelationalFront
