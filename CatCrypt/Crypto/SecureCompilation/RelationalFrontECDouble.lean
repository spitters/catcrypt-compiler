/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontEC
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontECMul
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
public import Std.Tactic.BVDecide

/-!
# The FULL Jacobian point-doubling `dbl-2009-l` over GF(251) — the EC group-law goal

`RelationalFrontEC.lean` realized the doubling-slope numerator `E = 3·A`
(`A = X²`) at the `ZMod 251` level, and `RelationalFrontECMul.lean` closed the
field **multiply**'s `ZMod 251` commuting square (`gf251Mul_commutes`,
`gf251Square_commutes` for the squares, `tripleSquareMod251_commutes` for
`E = 3·X²`).  Those are the field-op building blocks of the inversion-free
Jacobian point-doubling group law.  **This module assembles them into the FULL
`dbl-2009-l` doubling** — all three output coordinates `(X₃, Y₃, Z₃)`.

## The `dbl-2009-l` schedule (`a = 0`, BLS-class)

For a short-Weierstrass curve with `a = 0` (BLS12 family) the in-loop Jacobian
doubling is

```
A = X² ; B = Y² ; C = B² ; D = 2((X+B)² − A − C) ; E = 3·A ;
F = E² ; X₃ = F − 2D ; Y₃ = E·(D − X₃) − 8C ; Z₃ = 2·Y·Z
```

— a straight-line schedule of field `mul`/`sqr`/`add`/`sub`/`triple`/`double`.
Every step is one of the field ops whose `ZMod 251` commuting square the two
prior modules proved:

| step | `ZMod` building block (commuting square) |
|------|------------------------------------------|
| `A = X²`, `B = Y²`, `C = B²`, `F = E²` | `gf251Square_commutes` (`gf251Mul_commutes` diagonal) |
| `Y·Z` (inside `Z₃`) | `gf251Mul_commutes` |
| `E·(D−X₃)` (inside `Y₃`) | `gf251Mul_commutes` |
| `3·A` (`E`) | `tripleMod251_commutes` |
| `X+B` (inside `D`) | `encMod251_commutes` (the GF(251) add) |
| `2·(…)`, `2·Y·Z` (doubling) | `add251_commutes` (`a + a`, derived here) |
| `8·C` (inside `Y₃`) | iterated doubling = three `add251_commutes` |
| `F − 2D`, `D − X₃` (subtraction) | `sub251_commutes` (derived here) |

The two operations `dbl-2009-l` needs that the prior modules did **not** carry a
`ZMod` commuting square for are the modular **double** `a ↦ 2·a` and the modular
**subtract** `(a, b) ↦ a − b`.  Both are *the same `csub251`/`condSub251`
reduction infrastructure* already in the golden path — a double is `a + a`
followed by one `csub251`, a subtract is `a + (251 − b)` followed by one
`csub251` — so we derive their `ZMod 251` commuting squares here
(`add251_commutes`, `sub251_commutes`), additively, by the identical
`bv_decide` + `ZMod.val_*` route the add/multiply siblings used.  No new emit
infrastructure: both reuse `csub251` (`RelationalFrontInstances`).

## What this module establishes

* **A multi-output Jacobian point realization** (`RealizedJacobianDouble`): the
  three abstract output coordinates `(X₃, Y₃, Z₃) : ZMod 251 × ZMod 251 × ZMod
  251`, each tied to a `BitVec 64` straight-line formula over the encoded input
  coordinates `(encMod251 X, encMod251 Y, encMod251 Z)`, with the full commuting
  square per coordinate.  `RealizedKernel`/`RealizedUnaryKernel` are
  single-output; this is the multi-output point op the group law needs.
* **The abstract straight-line doubling** `dbl2009l : JacPoint → JacPoint`
  (`dbl-2009-l` as an explicit `ZMod 251` expression), and **all three output
  coordinates' `ZMod 251` commuting squares fully proved**
  (`dblX3_commutes`, `dblY3_commutes`, `dblZ3_commutes`).
* **A worked example**: a concrete point on `blsClassCurve` (`y² = x³ + 1` over
  GF(251)), doubled, with the realized `BitVec` formulas computing exactly the
  encoded output coordinates.

## Scope

* **`ECParams.add` over `ECPoint = Option (ZMod p × ZMod p)`** (affine, the sum
  type with `O`, needs a field **inversion** for the final normalisation) is
  *not* realized — Jacobian doubling defers inversion to one final
  normalisation, which is the extended-Euclid/Fermat op outside the straight-line
  `Com` fragment.  This module realizes the inversion-free in-loop doubling, the
  group-law step the MSM/scalar-mul loop actually spends its time in.
* **`bls12_377` is a 377-bit prime field** — a multi-limb (6×64-bit) carrier, so
  each field op is a CIOS/Karatsuba schedule, not the single-word GF(251) op.
  The relational *structure* here (per-coordinate encoding + commuting square +
  composed `BitVec` formula) ports verbatim; only the carrier (one word → six
  limbs) and the per-op kernel change.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul

/-! ## 1. The two missing field-op commuting squares: modular DOUBLE and SUBTRACT

`dbl-2009-l` needs `a ↦ 2·a` (`Z₃`, `D`, `2D`, `8C`) and `(a,b) ↦ a − b`
(`X₃ = F − 2D`, `D − X₃`).  Both are the `csub251` reduction tail already in the
golden path; we give their `ZMod 251` commuting squares here. -/

/-- The branch-free GF(251) **double** operator on a single reduced word:
    `2·a = csub251 (a + a)` (`a + a ≤ 500`, the `csub251` range). -/
def double251 (a : BitVec 64) : BitVec 64 := csub251 (a + a)

/-- The branch-free GF(251) **subtract** operator on reduced words:
    `a − b = csub251 (a + (251 − b))` (for `a, b < 251`, `a + (251 − b) ≤ 501`,
    the `csub251` range; `251 − b` is the additive inverse representative). -/
def sub251 (a b : BitVec 64) : BitVec 64 := csub251 (a + (251 - b))

/-- **`csub251` is the modular reduction up to 501.**  The subtract's inner word
    `a + (251 − b)` reaches `250 + 251 = 501` (`a = 250, b = 0`), one above the
    add's `≤ 500` range; `csub251`'s single conditional subtraction still reduces
    it (`501 = 251·1 + 250`).  The `bv_decide` range-extended sibling of
    `csub251_eq`. -/
theorem csub251_eq501 (s : BitVec 64) (h : s ≤ (501 : BitVec 64)) :
    csub251 s = s % (251 : BitVec 64) := by
  unfold csub251; bv_decide

/-- **The GF(251) DOUBLE commuting square.**  The abstract field double `2·A`
    (in `F_251`), serialized by `encMod251`, equals `double251` on the serialized
    operand.  `2·A = A + A`, so this is `encMod251_commutes` specialised to the
    diagonal — the doubling building block `dbl-2009-l` needs for `Z₃ = 2·Y·Z`,
    `D`, `2D`, `8C`. -/
theorem add251_commutes (A : ZMod 251) :
    encMod251 (2 * A) = double251 (encMod251 A) := by
  have h2 : (2 : ZMod 251) * A = A + A := by ring
  rw [h2, encMod251_commutes A A, double251]

/-- **The GF(251) SUBTRACT commuting square.**  The abstract field subtract
    `A − B` (in `F_251`), serialized by `encMod251`, equals `sub251` on the
    serialized operands.  Both `A.val, B.val < 251`, so `encMod251 A + (251 −
    encMod251 B) ≤ 500`, the `csub251` range; the result is the canonical residue
    of `A − B`.  The subtraction building block `dbl-2009-l` needs for
    `X₃ = F − 2D` and `D − X₃`. -/
theorem sub251_commutes (A B : ZMod 251) :
    encMod251 (A - B) = sub251 (encMod251 A) (encMod251 B) := by
  have hA : A.val < 251 := ZMod.val_lt A
  have hB : B.val < 251 := ZMod.val_lt B
  -- The `ZMod` value of a difference, as a nat residue (avoids `ZMod.val_sub`'s casework).
  have hvalsub : (A - B).val = (A.val + (251 - B.val)) % 251 := by
    have hcast : (A - B) = ((A.val + (251 - B.val) : ℕ) : ZMod 251) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [show ((251 : ℕ) : ZMod 251) = 0 from by decide]; ring
    rw [hcast, ZMod.val_natCast]
  have hencA : (encMod251 A).toNat = A.val := by
    simp only [encMod251, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
  have hencB : (encMod251 B).toNat = B.val := by
    simp only [encMod251, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
  -- The inner word `s = encA + (251 - encB)`; its `toNat` is `A.val + (251 - B.val) ≤ 500`.
  have hsumNat : (encMod251 A + (251 - encMod251 B)).toNat
      = A.val + (251 - B.val) := by
    rw [BitVec.toNat_add, BitVec.toNat_sub, hencA, hencB]
    have h251 : ((251 : BitVec 64)).toNat = 251 := rfl
    rw [h251]
    have hmod : (2 ^ 64 - B.val + 251) % 2 ^ 64 = 251 - B.val := by
      rw [show 2 ^ 64 - B.val + 251 = 2 ^ 64 + (251 - B.val) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, Nat.mod_eq_of_lt (by omega)]
  have hle : (encMod251 A + (251 - encMod251 B)) ≤ (501 : BitVec 64) := by
    apply BitVec.le_def.mpr; rw [hsumNat]
    have h501 : BitVec.toNat (501 : BitVec 64) = 501 := rfl
    rw [h501]; omega
  rw [sub251, csub251_eq501 _ hle]
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_umod, hsumNat, show ((251 : BitVec 64)).toNat = 251 from rfl]
  simp only [encMod251, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show (A - B).val < 2 ^ 64 by have := ZMod.val_lt (A - B); omega)]
  rw [hvalsub]

/-! ## 2. The abstract Jacobian point and the straight-line `dbl-2009-l` doubling

A Jacobian point over `F_251` is a triple `(X, Y, Z) : ZMod 251 × ZMod 251 ×
ZMod 251` (modelling the affine `(X/Z², Y/Z³)`, `Z = 0 = O`).  `dbl2009l` is the
`a = 0` `dbl-2009-l` schedule as an explicit straight-line `ZMod 251`
expression — every step a field `mul`/`add`/`sub`/`triple`/`double` with a
`ZMod 251` commuting square in hand. -/

/-- An abstract Jacobian point over `F_251 = ZMod 251`: `(X, Y, Z)`. -/
abbrev JacPoint : Type := ZMod 251 × ZMod 251 × ZMod 251

/-- Field **triple** `A ↦ 3·A` as a named op, so the commuting-square rewrite
    keys on it rather than colliding with the generic multiply
    `gf251Mul_commutes` (a `def`, opaque to `simp` unless unfolded). -/
def mul3 (A : ZMod 251) : ZMod 251 := 3 * A

/-- Field **double** `a ↦ 2·a` as a named op (same reason as `mul3`). -/
def mul2 (a : ZMod 251) : ZMod 251 := 2 * a

/-- `mul3`'s commuting square: `encMod251 (3·A) = tripleSpecBV (encMod251 A)`
    (`tripleMod251_commutes`, keyed on `mul3` so `simp` never confuses it with the
    generic multiply). -/
@[simp] theorem mul3_commutes (A : ZMod 251) :
    encMod251 (mul3 A) = tripleSpecBV (encMod251 A) := tripleMod251_commutes A

/-- `mul2`'s commuting square: `encMod251 (2·a) = double251 (encMod251 a)`
    (`add251_commutes`, keyed on `mul2`). -/
@[simp] theorem mul2_commutes (A : ZMod 251) :
    encMod251 (mul2 A) = double251 (encMod251 A) := add251_commutes A

/-- The `dbl-2009-l` (`a = 0`) Jacobian point-doubling as an explicit straight-line
    `ZMod 251` expression.  `A = X²; B = Y²; C = B²; D = 2((X+B)² − A − C);
    E = 3A; F = E²; X₃ = F − 2D; Y₃ = E(D − X₃) − 8C; Z₃ = 2YZ`.  Every binding is
    a field op with a `ZMod 251` commuting square (`gf251Mul_commutes`,
    `encMod251_commutes`, `sub251_commutes`, `tripleMod251_commutes`,
    `add251_commutes`). -/
def dbl2009l (P : JacPoint) : JacPoint :=
  let X := P.1; let Y := P.2.1; let Z := P.2.2
  let A := X * X
  let B := Y * Y
  let C := B * B
  let D := mul2 (((X + B) * (X + B)) - A - C)
  let E := mul3 A
  let F := E * E
  let X3 := F - mul2 D
  let Y3 := E * (D - X3) - mul2 (mul2 (mul2 C))   -- 8·C = 2·2·2·C
  let Z3 := mul2 (Y * Z)
  (X3, Y3, Z3)

/-! ## 3. The `BitVec`-level realized formulas (one per coordinate)

Each abstract field op is replaced by its emitted carrier operator: `gf251MulSpec`
(multiply/square), `tripleSpecBV` (triple), `double251` (`a ↦ 2a`), `sub251`
(`a − b`), and `csub251 (a + b)` (the reducing add).  The composition mirrors the
abstract `dbl2009l` step for step, so the commuting square closes by sequential
rewrites with each building block's square. -/

/-- The realized `BitVec 64` straight-line formulas for the three output
    coordinates, on the **encoded** input coordinates `(x, y, z) = (encMod251 X,
    encMod251 Y, encMod251 Z)`.  Returns `(X₃, Y₃, Z₃)` words. -/
def dbl2009lBV (x y z : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let a := gf251MulSpec x x                         -- A = X²
  let b := gf251MulSpec y y                         -- B = Y²
  let c := gf251MulSpec b b                         -- C = B²
  let xb := csub251 (x + b)                         -- X + B
  let d := double251 (sub251 (sub251 (gf251MulSpec xb xb) a) c)  -- D = 2((X+B)²−A−C)
  let e := tripleSpecBV a                           -- E = 3A
  let f := gf251MulSpec e e                          -- F = E²
  let x3 := sub251 f (double251 d)                  -- X₃ = F − 2D
  let y3 := sub251 (gf251MulSpec e (sub251 d x3))
                   (double251 (double251 (double251 c)))  -- Y₃ = E(D−X₃) − 8C
  let z3 := double251 (gf251MulSpec y z)            -- Z₃ = 2YZ
  (x3, y3, z3)

/-! ## 4. The per-coordinate `ZMod 251` commuting squares — all three closed

The heart: each output coordinate of the abstract `dbl2009l`, serialized by
`encMod251`, equals the corresponding `dbl2009lBV` formula on the serialized input
coordinates.  Closed by sequential rewrites with the building-block commuting
squares (no `bv_decide` on the composite — each leaf already has its square). -/

/-- **`Z₃ = 2·Y·Z` commuting square (the cleanest coordinate).**  The Jacobian
    `Z₃` is a single multiply (`gf251Mul_commutes`) then a double
    (`add251_commutes`).  Fully closed. -/
theorem dblZ3_commutes (X Y Z : ZMod 251) :
    encMod251 (dbl2009l (X, Y, Z)).2.2
      = (dbl2009lBV (encMod251 X) (encMod251 Y) (encMod251 Z)).2.2 := by
  simp only [dbl2009l, dbl2009lBV, mul2_commutes, gf251Mul_commutes]

/-- **`X₃ = F − 2D` commuting square.**  Composes the square `A = X²`, the
    intermediate `B`, `C`, `X+B`, `D = 2((X+B)²−A−C)`, `E = 3A`, `F = E²`, then
    the subtract `F − 2D`.  Every step is a building-block square; closed by
    sequential rewrites. -/
theorem dblX3_commutes (X Y Z : ZMod 251) :
    encMod251 (dbl2009l (X, Y, Z)).1
      = (dbl2009lBV (encMod251 X) (encMod251 Y) (encMod251 Z)).1 := by
  simp only [dbl2009l, dbl2009lBV, mul3_commutes, mul2_commutes, sub251_commutes,
    gf251Mul_commutes, encMod251_commutes]

/-- **`Y₃ = E·(D − X₃) − 8·C` commuting square.**  Composes everything `X₃` needs,
    plus the multiply `E·(D − X₃)`, the inner subtract `D − X₃`, and the iterated
    double `8·C = 2·2·2·C`.  Every step is a building-block square; closed by
    sequential rewrites. -/
theorem dblY3_commutes (X Y Z : ZMod 251) :
    encMod251 (dbl2009l (X, Y, Z)).2.1
      = (dbl2009lBV (encMod251 X) (encMod251 Y) (encMod251 Z)).2.1 := by
  simp only [dbl2009l, dbl2009lBV, mul3_commutes, mul2_commutes, sub251_commutes,
    gf251Mul_commutes, encMod251_commutes]

/-! ## 5. The multi-output Jacobian point realization (the group-law deliverable)

`RealizedKernel`/`RealizedUnaryKernel` are single-output.  A point op has THREE
outputs sharing intermediates; we bundle the three coordinate commuting squares
into one record whose `commutes` field returns the encoded output triple matching
the `BitVec`-formula triple, component-wise.  This is the multi-output structure
the EC group law needs. -/

/-- **A relationally-emitted multi-output Jacobian point operation.**  An abstract
    point op `op : JacPoint → JacPoint`, its `BitVec 64`-triple realization `bop`
    on the encoded coordinates, and the per-coordinate commuting square: encoding
    each output coordinate equals the matching `bop` component on the encoded input
    coordinates.  The multi-output analogue of `RealizedUnaryKernel` (the point-op
    record `RealizedKernel`/`RealizedUnaryKernel` cannot express). -/
structure RealizedJacobianOp (op : JacPoint → JacPoint) where
  /-- The carrier-level realization: a `BitVec 64`-triple op on the three encoded
      input coordinates. -/
  bop : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64 × BitVec 64
  /-- **The multi-output commuting square**: encoding the abstract output point
      (coordinate-wise) equals the `bop` triple on the encoded input coordinates. -/
  commutes : ∀ X Y Z : ZMod 251,
    (encMod251 (op (X, Y, Z)).1,
      encMod251 (op (X, Y, Z)).2.1,
      encMod251 (op (X, Y, Z)).2.2)
    = bop (encMod251 X) (encMod251 Y) (encMod251 Z)

/-- **The relationally-emitted Jacobian point-DOUBLING.**  Its abstract source is
    the `dbl-2009-l` (`a = 0`, BLS-class) point doubling `dbl2009l : JacPoint →
    JacPoint`, its computational side is the `BitVec`-triple straight-line formula
    `dbl2009lBV`, and its commuting square is the conjunction of the three
    per-coordinate squares (`dblX3_commutes`, `dblY3_commutes`, `dblZ3_commutes`),
    all fully proved.  This is the FULL Jacobian point-doubling group-law step
    realized end-to-end at the `ZMod 251` level. -/
def dbl2009lRealized : RealizedJacobianOp dbl2009l where
  bop := dbl2009lBV
  commutes := fun X Y Z => by
    have hx := dblX3_commutes X Y Z
    have hy := dblY3_commutes X Y Z
    have hz := dblZ3_commutes X Y Z
    rw [hx, hy, hz]

/-! ## 6. The transfer corollary: an abstract point equation decided by the formula

The point analogue of `spec_eq_transfers_to_emit`: two Jacobian points double to
the same point **iff** the realized `BitVec` formula agrees on their encoded
coordinates — through the injective-not-onto `encMod251`, coordinate-wise. -/

/-- **The point-doubling transfer.**  Two Jacobian points `(X,Y,Z)`, `(X',Y',Z')`
    double to the same point in `F_251` iff the realized `dbl2009lBV` formula
    agrees on their encoded coordinates — the relational front carrying the FULL
    EC doubling end-to-end, through the injective-not-onto serialization. -/
theorem dbl2009l_spec_transfers (X Y Z X' Y' Z' : ZMod 251) :
    dbl2009l (X, Y, Z) = dbl2009l (X', Y', Z') ↔
      dbl2009lBV (encMod251 X) (encMod251 Y) (encMod251 Z)
        = dbl2009lBV (encMod251 X') (encMod251 Y') (encMod251 Z') := by
  constructor
  · intro h
    have hx : (dbl2009lBV (encMod251 X) (encMod251 Y) (encMod251 Z)).1
        = (dbl2009lBV (encMod251 X') (encMod251 Y') (encMod251 Z')).1 := by
      rw [← dblX3_commutes, ← dblX3_commutes, h]
    have hy : (dbl2009lBV (encMod251 X) (encMod251 Y) (encMod251 Z)).2.1
        = (dbl2009lBV (encMod251 X') (encMod251 Y') (encMod251 Z')).2.1 := by
      rw [← dblY3_commutes, ← dblY3_commutes, h]
    have hz : (dbl2009lBV (encMod251 X) (encMod251 Y) (encMod251 Z)).2.2
        = (dbl2009lBV (encMod251 X') (encMod251 Y') (encMod251 Z')).2.2 := by
      rw [← dblZ3_commutes, ← dblZ3_commutes, h]
    exact Prod.ext hx (Prod.ext hy hz)
  · intro h
    have h1 : encMod251 (dbl2009l (X, Y, Z)).1 = encMod251 (dbl2009l (X', Y', Z')).1 := by
      rw [dblX3_commutes, dblX3_commutes, h]
    have h21 : encMod251 (dbl2009l (X, Y, Z)).2.1 = encMod251 (dbl2009l (X', Y', Z')).2.1 := by
      rw [dblY3_commutes, dblY3_commutes, h]
    have h22 : encMod251 (dbl2009l (X, Y, Z)).2.2 = encMod251 (dbl2009l (X', Y', Z')).2.2 := by
      rw [dblZ3_commutes, dblZ3_commutes, h]
    have e1 := encMod251_injective h1
    have e21 := encMod251_injective h21
    have e22 := encMod251_injective h22
    exact Prod.ext e1 (Prod.ext e21 e22)

/-! ## 7. A worked example: doubling a concrete point on `blsClassCurve`

`blsClassCurve : y² = x³ + 1` over GF(251) (`a = 0`, `b = 1`).  The affine point
`(0, 1)` is on it (`1 = 0 + 0 + 1`); in Jacobian (`Z = 1`) it is `(0, 1, 1)`.  We
double it with the abstract schedule and check the realized `BitVec` formula
computes the same (encoded) output coordinates. -/

/-- The affine point `(0, 1)` is on `blsClassCurve` (`y² = x³ + 1`): `1·1 = 0+0+1`. -/
theorem worked_point_onCurve : blsClassCurve.onCurve (0 : ZMod 251) (1 : ZMod 251) := by
  unfold ECParams.onCurve blsClassCurve; decide

/-- **The worked doubling, abstract side.**  The `dbl-2009-l` schedule on the
    Jacobian point `(0, 1, 1)` (the curve point `(0,1)` with `Z = 1`):
    `A = 0; B = 1; C = 1; D = 2((0+1)² − 0 − 1) = 0; E = 0; F = 0; X₃ = 0;
    Y₃ = 0·(0−0) − 8·1 = −8 = 243; Z₃ = 2·1·1 = 2`. -/
theorem worked_dbl_abstract :
    dbl2009l (0, 1, 1) = ((0 : ZMod 251), (243 : ZMod 251), (2 : ZMod 251)) := by
  unfold dbl2009l mul2 mul3; decide

/-- **The worked doubling, realized formula side.**  The emitted `BitVec`-triple
    formula `dbl2009lBV` on the encoded coordinates `(enc 0, enc 1, enc 1)`
    computes exactly the encoded output coordinates `(enc 0, enc 243, enc 2)` — the
    relational tie holding on a concrete curve point, fully proved. -/
theorem worked_dbl_realized :
    dbl2009lBV (encMod251 0) (encMod251 1) (encMod251 1)
      = (encMod251 0, encMod251 243, encMod251 2) := by
  have hx := dblX3_commutes 0 1 1
  have hy := dblY3_commutes 0 1 1
  have hz := dblZ3_commutes 0 1 1
  rw [worked_dbl_abstract] at hx hy hz
  exact Prod.ext hx.symm (Prod.ext hy.symm hz.symm)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
