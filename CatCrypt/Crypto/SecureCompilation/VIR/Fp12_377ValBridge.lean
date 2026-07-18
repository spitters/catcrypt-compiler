/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp6

/-!
# Carrier bridge: the dialect GT value `Fp12Val bls377Q` ↔ the relational-front `Fp12_377`

CatCrypt carries the `bls12_377` pairing target group `GT = Fp12` in **two**
encodings, both over the genuine 377-bit base prime `bls377Q`
(`FpBLS377 = ZMod bls377Q`):

* the **dialect** carrier `FieldDialect.Fp12Val p` (the denotation target of the
  L3 `Field` VIR dialect — what `pairingCheckDialect` / `pairingCheck2` denote
  into).  Its tower is `Fp12Val = {c0 c1 : Fp6Val}`,
  `Fp6Val = {a0 a1 a2 : Fp2Val}`, `Fp2Val = {c0 c1 : ZMod p}`.  The dialect's
  default `Mul (Fp2Val p)` fixes the **quadratic** non-residue at `u² = −1`
  (correct for BLS12-381/BN254), but it also exposes the **β-parametric** tower
  multiplies `Fp2Val.mulBeta β` / `Fp6Val.mulBeta β ξ0` / `Fp12Val.mulBeta β ξ0`
  for the tower `u² = β` (`β = −5` is the genuine BLS12-377 quadratic
  non-residue).  The **cubic** non-residue is carried as a *single scalar*
  `ξ₀ : ZMod p` encoding `ξ = ξ₀ + u` (`Fp6Val.mulXiBeta β ξ0`); the **dodecic**
  non-residue is the `Fp6` generator `v` itself (`Fp12Val.mulByVBeta`, `w² = v`).
* the **relational-front** carrier `RelationalFront.Fp12_377`
  (`RelationalFrontBls377Fp6.lean`) — the GT field the concrete `bls12_377`
  pairing produces (`RelationalFrontBls377MillerLoop.millerLoop`, valued in
  `Fp12_377`).  Its tower is `Fp12_377 = {c0 c1 : Fp6_377}`,
  `Fp6_377 = {c0 c1 c2 : Fp2_377}`, `Fp2_377 = {c0 c1 : FpBLS377}`, and the
  multiplies carry a **structured** pair of non-residues: the base quadratic
  `ξ₂ : FpBLS377` (`u² = ξ₂`, the `Fp2_377` multiply parameter) and the cubic
  `ξ₆ : Fp2_377` (`v³ = ξ₆`).  The dodecic non-residue is again the generator `v`
  (`Fp6_377.mulByV`, `w² = v`).  Both `Fp6_377` and `Fp12_377` carry a `CommRing`.

This file builds the **forward map** `toFp12 : Fp12_377 → Fp12Val bls377Q` (and
its inverse `ofFp12`) componentwise, and proves it commutes with the operations
both carriers expose, so the relational-front pairing value can be transported
into the dialect GT carrier `Fp12Val bls377Q` — where the dialect's
`pairingCheckDialect` / `pairingCheck2` op (which is generic over the prime `p`)
applies at `p = bls377Q`.  This is what resolves the 377-vs-381 carrier mismatch:
the pairing-check op is curve-generic, and the bridge instantiates it at the
`bls12_377` prime.

## Leaf

`FpBLS377` is `ZMod bls377Q` (`RelationalFrontBls377Fp2.lean`), an `abbrev`, so
the relational-front leaf is **definitionally** the dialect leaf `ZMod p` at
`p = bls377Q`.  The leaf map is therefore the identity.

## What is PROVED — the bridge targets the genuine BLS12-377 non-residue

The bridge maps the relational-front multiply to the dialect's **β-parametric**
tower multiply at `β = ξ₂` — the genuine quadratic non-residue the relational
front carries — so the `Fp2`-level commute holds **unconditionally in `ξ₂`** (no
`ξ₂ = −1` convention). The only cubic-shape requirement is:

* `ξ₆ = ⟨ξ₀, 1⟩`  (the dialect's `mulXiBeta β ξ0` is multiplication by `ξ₀ + u`);
  for `bls12_377` this is `ξ₆ = u = ⟨0, 1⟩` at `ξ₀ = 0`, which the curve takes.

The dodecic non-residue is `v` in **both** encodings (`mulByV`), so — unlike the
BLS12-381 tower bridge (`Fp12ValTowerBridge.lean`), which carries a separate
`hgamma : γ = v` hypothesis on a `Fp12.HasGamma` typeclass — no extra dodecic
hypothesis is needed here.

* `toFp2` (the `Fp2` level) is a ring hom on `+`/`−`/`neg` **unconditionally**,
  and on `*` to `Fp2Val.mulBeta ξ₂` **unconditionally in `ξ₂`**.
* `toFp6` is a ring hom on `+`/`−`, and on `*` to `Fp6Val.mulBeta ξ₂ ξ0`
  **under `hξ6`** only.
* `toFp12` is a ring hom on `+`/`−`, and on `*` to `Fp12Val.mulBeta ξ₂ ξ0`
  **under `hξ6`** only.

Every obligation is **fully proved** (no axiom, no `sorry`); each mul-commute is
a finite tower-algebra identity closed by `ring` over `ZMod bls377Q` after
pushing the leaf map through the schoolbook formulas.

## The genuine BLS12-377 GT carrier

`toFp12_mul_bls377` instantiates the parametric mul-commute at the TRUE
BLS12-377 non-residues: `ξ₂ = −5` (`Fp2 = Fp[u]/(u² + 5)`, `bls377Beta`) and
`ξ₆ = u = ⟨0, 1⟩` (`Fp6 = Fp2[v]/(v³ − u)`, `bls377Xi6`, `ξ₀ = 0`). The dialect's
β-parametric `Fp12Val.mulBeta (−5) 0` *is* the genuine BLS12-377 GT multiply, so
the bridge transports the relational-front pairing value into the real field —
the additive β-parametrization meets the curve's actual quadratic non-residue,
with no `ξ₂ = −1` caveat. The default `Mul (Fp2Val p)` (and `Fp6Val.mul` /
`Fp12Val.mul`) remain the `β = −1` tower, untouched and correct for
BLS12-381/BN254; `Fp{2,6,12}Val.mulBeta_neg_one` certify that the parametric
multiplies specialise back to those at `β = −1`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Fp12_377ValBridge

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The carrier maps (forward and back), componentwise -/

/-- Forward leaf-level map `Fp2_377 → Fp2Val bls377Q` — a structural relabeling
    (the leaf `FpBLS377 = ZMod bls377Q` is definitionally the dialect leaf). -/
def toFp2 (x : Fp2_377) : Fp2Val bls377Q := ⟨x.c0, x.c1⟩

/-- Forward cubic-level map `Fp6_377 → Fp6Val bls377Q`, component-wise. -/
def toFp6 (x : Fp6_377) : Fp6Val bls377Q := ⟨toFp2 x.c0, toFp2 x.c1, toFp2 x.c2⟩

/-- Forward GT map `Fp12_377 → Fp12Val bls377Q`, component-wise. -/
def toFp12 (x : Fp12_377) : Fp12Val bls377Q := ⟨toFp6 x.c0, toFp6 x.c1⟩

/-- Inverse leaf map `Fp2Val bls377Q → Fp2_377`. -/
def ofFp2 (x : Fp2Val bls377Q) : Fp2_377 := ⟨x.c0, x.c1⟩

/-- Inverse cubic map `Fp6Val bls377Q → Fp6_377`. -/
def ofFp6 (x : Fp6Val bls377Q) : Fp6_377 := ⟨ofFp2 x.a0, ofFp2 x.a1, ofFp2 x.a2⟩

/-- Inverse GT map `Fp12Val bls377Q → Fp12_377`. -/
def ofFp12 (x : Fp12Val bls377Q) : Fp12_377 := ⟨ofFp6 x.c0, ofFp6 x.c1⟩

/-- The GT-level forward map (the deliverable: relational-front pairing value
    `→` dialect GT carrier). -/
abbrev toVal : Fp12_377 → Fp12Val bls377Q := toFp12

/-- The GT-level inverse map. -/
abbrev ofVal : Fp12Val bls377Q → Fp12_377 := ofFp12

/-! ## 2. Bijection (`toFp12` is invertible, hence injective on the carrier) -/

@[simp] theorem ofFp2_toFp2 (x : Fp2_377) : ofFp2 (toFp2 x) = x := by
  cases x; rfl

@[simp] theorem toFp2_ofFp2 (x : Fp2Val bls377Q) : toFp2 (ofFp2 x) = x := by
  cases x; rfl

@[simp] theorem ofFp6_toFp6 (x : Fp6_377) : ofFp6 (toFp6 x) = x := by
  cases x; simp [toFp6, ofFp6]

@[simp] theorem toFp6_ofFp6 (x : Fp6Val bls377Q) : toFp6 (ofFp6 x) = x := by
  cases x; simp [toFp6, ofFp6]

@[simp] theorem ofFp12_toFp12 (x : Fp12_377) : ofFp12 (toFp12 x) = x := by
  cases x; simp [toFp12, ofFp12]

@[simp] theorem toFp12_ofFp12 (x : Fp12Val bls377Q) : toFp12 (ofFp12 x) = x := by
  cases x; simp [toFp12, ofFp12]

theorem toFp12_injective : Function.Injective toFp12 :=
  Function.LeftInverse.injective ofFp12_toFp12

theorem toFp12_bijective : Function.Bijective toFp12 :=
  ⟨toFp12_injective, fun y => ⟨ofFp12 y, toFp12_ofFp12 y⟩⟩

/-! ## 3. `toFp2` is a ring hom (`+`/`−`/neg unconditional; `*` under `hξ2`) -/

@[simp] theorem toFp2_c0 (x : Fp2_377) : (toFp2 x).c0 = x.c0 := rfl
@[simp] theorem toFp2_c1 (x : Fp2_377) : (toFp2 x).c1 = x.c1 := rfl
@[simp] theorem toFp2_mk (a b : FpBLS377) :
    toFp2 ⟨a, b⟩ = (⟨a, b⟩ : Fp2Val bls377Q) := rfl

theorem toFp2_add (x y : Fp2_377) : toFp2 (x + y) = toFp2 x + toFp2 y := by
  ext <;> simp [toFp2]

theorem toFp2_sub (x y : Fp2_377) : toFp2 (x - y) = toFp2 x - toFp2 y := by
  ext <;> simp [toFp2]

theorem toFp2_neg (x : Fp2_377) : toFp2 (-x) = -toFp2 x := by
  ext <;> simp [toFp2]

/-- The leaf map carries the `Fp2_377` schoolbook multiply (non-residue `ξ₂`) to
    the dialect β-parametric multiply `Fp2Val.mulBeta ξ₂` — **unconditionally** in
    `ξ₂` (the additive β-parametrization meets the genuine non-residue, so no
    `ξ₂ = −1` convention is forced). -/
theorem toFp2_mul (ξ₂ : FpBLS377) (x y : Fp2_377) :
    toFp2 (Fp2_377.mulSchoolbook ξ₂ x y) = Fp2Val.mulBeta ξ₂ (toFp2 x) (toFp2 y) := by
  ext <;> simp [toFp2, Fp2Val.mulBeta_c0, Fp2Val.mulBeta_c1] <;> ring

/-- The dialect β-parametric `Fp2Val` multiply by `⟨ξ₀, 1⟩` is the dialect
    β-parametric cubic non-residue fold `mulXiBeta β ξ0` (`·(ξ₀ + u)`). -/
theorem mulXiBeta_eq (β ξ0 : ZMod bls377Q) (z : Fp2Val bls377Q) :
    Fp2Val.mulBeta β ⟨ξ0, 1⟩ z = Fp6Val.mulXiBeta β ξ0 z := by
  ext <;> simp [Fp2Val.mulBeta_c0, Fp2Val.mulBeta_c1, Fp6Val.mulXiBeta] <;> ring

/-- The leaf map carries the `Fp2_377` multiply by the cubic non-residue `ξ₆`
    (left factor) to the dialect β-parametric cubic fold `mulXiBeta ξ₂ ξ0`, given
    `ξ₆ = ⟨ξ₀, 1⟩` — unconditionally in `ξ₂`. -/
theorem toFp2_xiFold_l (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (ξ0 : ZMod bls377Q)
    (hξ6 : ξ₆ = ⟨ξ0, 1⟩) (z : Fp2_377) :
    toFp2 (Fp2_377.mulSchoolbook ξ₂ ξ₆ z) = Fp6Val.mulXiBeta ξ₂ ξ0 (toFp2 z) := by
  subst hξ6
  ext <;> simp [toFp2, Fp6Val.mulXiBeta] <;> ring

/-- The leaf map carries the `Fp2_377` multiply by the cubic non-residue `ξ₆`
    (right factor) to the dialect β-parametric cubic fold `mulXiBeta ξ₂ ξ0`.
    (Same as `toFp2_xiFold_l` up to the commutative `Fp2_377` multiply argument
    order; the `Fp12_377.mulByV` fold uses this order.) -/
theorem toFp2_xiFold_r (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (ξ0 : ZMod bls377Q)
    (hξ6 : ξ₆ = ⟨ξ0, 1⟩) (z : Fp2_377) :
    toFp2 (Fp2_377.mulSchoolbook ξ₂ z ξ₆) = Fp6Val.mulXiBeta ξ₂ ξ0 (toFp2 z) := by
  subst hξ6
  ext <;> simp [toFp2, Fp6Val.mulXiBeta] <;> ring

/-! ## 4. `toFp6` is a ring hom (`*` under `hξ2`, `hξ6`) -/

@[simp] theorem toFp6_a0 (x : Fp6_377) : (toFp6 x).a0 = toFp2 x.c0 := rfl
@[simp] theorem toFp6_a1 (x : Fp6_377) : (toFp6 x).a1 = toFp2 x.c1 := rfl
@[simp] theorem toFp6_a2 (x : Fp6_377) : (toFp6 x).a2 = toFp2 x.c2 := rfl

theorem toFp6_add (x y : Fp6_377) :
    toFp6 (x + y) = Fp6Val.add (toFp6 x) (toFp6 y) := by
  ext <;> simp [toFp6, Fp6Val.add, Fp6_377.add_c0, Fp6_377.add_c1, Fp6_377.add_c2,
    toFp2_add]

theorem toFp6_sub (x y : Fp6_377) :
    toFp6 (x - y) = Fp6Val.sub (toFp6 x) (toFp6 y) := by
  ext <;> simp [toFp6, Fp6Val.sub, Fp6_377.sub_c0, Fp6_377.sub_c1, Fp6_377.sub_c2,
    toFp2_sub]

/-- `toFp6` carries the relational-front cubic multiply to the dialect
    β-parametric cubic multiply, given `ξ₆ = ⟨ξ₀, 1⟩` — unconditionally in `ξ₂`
    (the β-parametrization carries the genuine quadratic non-residue `ξ₂`). -/
theorem toFp6_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (ξ0 : ZMod bls377Q)
    (hξ6 : ξ₆ = ⟨ξ0, 1⟩) (x y : Fp6_377) :
    toFp6 (Fp6_377.mulSchoolbook ξ₂ ξ₆ x y)
      = Fp6Val.mulBeta ξ₂ ξ0 (toFp6 x) (toFp6 y) := by
  ext <;>
    simp only [toFp6_a0, toFp6_a1, toFp6_a2, Fp6_377.mulSchoolbook, Fp6Val.mulBeta,
      toFp2_add, toFp2_mul ξ₂, hξ6, toFp2_mk, mulXiBeta_eq]

/-! ## 5. `toFp12` is a ring hom (`*` under `hξ2`, `hξ6`) -/

@[simp] theorem toFp12_c0 (x : Fp12_377) : (toFp12 x).c0 = toFp6 x.c0 := rfl
@[simp] theorem toFp12_c1 (x : Fp12_377) : (toFp12 x).c1 = toFp6 x.c1 := rfl

theorem toFp12_add (x y : Fp12_377) :
    toFp12 (x + y) = Fp12Val.add (toFp12 x) (toFp12 y) := by
  ext <;> simp [toFp12, Fp12Val.add, Fp12_377.add_c0, Fp12_377.add_c1, toFp6_add]

theorem toFp12_sub (x y : Fp12_377) :
    toFp12 (x - y) = Fp12Val.sub (toFp12 x) (toFp12 y) := by
  ext <;> simp [toFp12, Fp12Val.sub, Fp12_377.sub_c0, Fp12_377.sub_c1, toFp6_sub]

/-- `toFp6` carries the relational-front dodecic fold `Fp6_377.mulByV` (`·v`) to
    the dialect β-parametric dodecic fold `Fp12Val.mulByVBeta ξ₂ ξ0`, given
    `ξ₆ = ⟨ξ₀,1⟩` — unconditionally in `ξ₂`. The dodecic non-residue is the
    generator `v` in **both** encodings. -/
theorem toFp6_mulByV (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (ξ0 : ZMod bls377Q)
    (hξ6 : ξ₆ = ⟨ξ0, 1⟩) (z : Fp6_377) :
    toFp6 (Fp6_377.mulByV ξ₂ ξ₆ z) = Fp12Val.mulByVBeta ξ₂ ξ0 (toFp6 z) := by
  ext <;>
    simp only [toFp6_a0, toFp6_a1, toFp6_a2, Fp6_377.mulByV, Fp12Val.mulByVBeta,
      toFp2_xiFold_r ξ₂ ξ₆ ξ0 hξ6]

/-- **The load-bearing mul-commute.** `toFp12` carries the relational-front
    `Fp12_377` Karatsuba/schoolbook multiply (structured `(ξ₂, ξ₆)`) to the
    dialect β-parametric `Fp12Val.mulBeta ξ₂ ξ0` multiply, given `ξ₆ = ⟨ξ₀, 1⟩`
    (`hξ6`) — **unconditionally in the quadratic non-residue `ξ₂`**. The β-tower
    carries the genuine non-residue, so this hits the TRUE BLS12-377 GT field at
    `ξ₂ = −5` (`toFp12_mul_bls377`) with no false `ξ₂ = −1` convention. Fully
    proved by reduction to `toFp6`'s ring-hom laws. -/
theorem toFp12_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (ξ0 : ZMod bls377Q)
    (hξ6 : ξ₆ = ⟨ξ0, 1⟩) (x y : Fp12_377) :
    toFp12 (Fp12_377.mulSchoolbook ξ₂ ξ₆ x y)
      = Fp12Val.mulBeta ξ₂ ξ0 (toFp12 x) (toFp12 y) := by
  ext <;>
    simp only [toFp12_c0, toFp12_c1, Fp12_377.mulSchoolbook, Fp12Val.mulBeta,
      Fp12_377.mul₆, toFp6_add, toFp6_mul ξ₂ ξ₆ ξ0 hξ6,
      toFp6_mulByV ξ₂ ξ₆ ξ0 hξ6]

/-! ## 6. The genuine BLS12-377 GT carrier (β = −5, ξ₀ = 0) -/

/-- The genuine BLS12-377 quadratic non-residue: `Fp2 = Fp[u]/(u² + 5)`, `u² = −5`. -/
def bls377Beta : ZMod bls377Q := -5

/-- The genuine BLS12-377 cubic non-residue scalar `ξ₀ = 0` (`Fp6 = Fp2[v]/(v³ − u)`,
    i.e. `v³ = u`, so `ξ = u = 0 + u`). -/
def bls377Xi0 : ZMod bls377Q := 0

/-- The genuine BLS12-377 cubic non-residue `ξ₆ = u = ⟨0, 1⟩ : Fp2_377`. -/
def bls377Xi6 : Fp2_377 := ⟨bls377Xi0, 1⟩

/-- **The genuine BLS12-377 GT mul-commute.** `toFp12` carries the relational-front
    `Fp12_377` multiply at the TRUE BLS12-377 non-residues (`ξ₂ = −5`, `ξ₆ = u`)
    to the dialect β-parametric `Fp12Val.mulBeta (−5) 0` multiply — the dialect
    GT carrier under the genuine quadratic non-residue, with no `ξ₂ = −1` caveat. -/
theorem toFp12_mul_bls377 (x y : Fp12_377) :
    toFp12 (Fp12_377.mulSchoolbook bls377Beta bls377Xi6 x y)
      = Fp12Val.mulBeta bls377Beta bls377Xi0 (toFp12 x) (toFp12 y) :=
  toFp12_mul bls377Beta bls377Xi6 bls377Xi0 rfl x y

end CatCrypt.Crypto.SecureCompilation.VIR.Fp12_377ValBridge
