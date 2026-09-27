/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

/-!
# Field VIR dialect (the L3 algebraic layer, over ModArith)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The **L3** level of the PrimeIR-style layered crypto-IR stack, sitting between
the elliptic-curve group law and the residue-ring ModArith dialect:

    EllipticCurve(L4) → **Field(L3)** → ModArith(L2) → {Vector | LowCT} → {jasmin | x86}

Today the extension-field tower (`Fp2`/`Fp6`/`Fp12`) lives in the bespoke
pairing-tower files (`Pairing/Fp2Tower.lean`, …), re-derived per curve.  This
dialect gives the **abstract field layer** — the prime field `F_p` *and* the
pairing extension tower — one verified home, mirroring the way `ModArithDialect`
gives the residue-ring layer one home.

## Types (`FieldTy`)

* `fp p`     — the prime field `F_p`, `⟦·⟧ = ZMod p`.
* `fp2 p`    — the quadratic extension `Fp2 = Fp[u]/(u²+1)`, `⟦·⟧ = Fp2Val p`
              (a pair `ZMod p × ZMod p`, `a + b·u`, `u² = −1`).
* `fp6 p`    — the cubic extension `Fp6 = Fp2[v]/(v³−ξ)`, `⟦·⟧ = Fp6Val p`
              (a triple of `Fp2Val p`, `a + b·v + c·v²`, `v³ = ξ`).
* `fp12 p`   — the quadratic extension `Fp12 = Fp6[w]/(w²−v)`, `⟦·⟧ = Fp12Val p`
              (a pair of `Fp6Val p`, `a + b·w`, `w² = v`).  This is the pairing
              target group `GT`.

`ExtDesc` describes prime-ir's generic extension field `!field.ef<N x B, ξ>`, a
binomial extension of a prime field or of another extension. The three towers are
its instances `tower2`, `tower6` and `tower12` (`Fp2Val.equivDesc` and the
`toDesc_mulBeta` lemmas), and `fieldDialectTower τ` indexes the types by the tower
constant per modulus.

The denotation of every Field type is the **abstract** extension-field value
(`ZMod p`-built tower), so a Field op denotes to the abstract field operation —
the once-per-dialect tie of the layered plan.

## Ops (`FieldOp`)

* prime-field `fAdd`/`fSub`/`fNeg`/`fMul`/`fInv` — denote into `ZMod p`'s native
  ops (delegating to the ModArith leaves);
* prime-field `fieldDouble`/`fieldSquare` — the prime-ir `field.double` /
  `field.square` derived ops, denoting to `a + a` and `a * a`;
* extension `ext2Mul`/`ext6Mul`/`ext12Mul` — the Karatsuba/Toom extension
  multiplies, denoting into the abstract `Fp2`/`Fp6`/`Fp12` product;
* `ext2Add`/`ext2Sub` … — componentwise extension add/sub;
* `frobenius2 p` — the `Fp2` Frobenius `x ↦ x^p` (here the conjugation
  `a + b·u ↦ a − b·u`, the `p`-power map for the `u²=−1` extension), denoting to
  the abstract Frobenius.

## Lowering (`FieldLowering.lean`)

A Field op lowers to a **schedule of ModArith ops**: an `ext2Mul` lowers to three
ModArith `montMul` plus adds/subs (Karatsuba `(a+bu)(c+du) = (ac−bd) + (ad+bc)u`);
`ext6Mul`/`ext12Mul` compose.  That lowering is proven denotation- and
CT-preserving in `FieldLowering.lean`, mirroring `ModArithLowering`'s
`lower_denote_preserved` / `lower_ctSafe_preserved`.

## Pure-only + constant-time

Like `ModArithDialect`, every Field-op denotation is a total pure function (no
memory/sampling effect), and **every** Field op is data-oblivious — extension-
field arithmetic is a fixed schedule of base-field ops, index-independent — so
`ctSafe` is `true` for all ops.  This is the L3 instance of the VIR `ctSafe`
story (`CTPredicate.lean`): the field layer is CT by construction.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-! ## 1. Abstract extension-tower values (the denotation targets)

The tower is built over `ZMod p` exactly as the bespoke pairing-tower files build
it over the base ring (`Pairing/Fp2Tower.lean`): `Fp2 = R[u]/(u²+1)`,
`Fp6 = Fp2[v]/(v³−ξ)`, `Fp12 = Fp6[w]/(w²−v)`.  Here `R := ZMod p` and the
non-residue scalar `ξ = ξ₀ + u` is carried at the `Fp6` op (defaulting to the
BN254 `ξ₀ = 9` / BLS `ξ₀ = 1`), so the dialect's denotation is the abstract
field value, parametric in the curve's non-residue. -/

/-- A quadratic-extension value `Fp2 = Fp[u]/(u²+1)`: `c0 + c1·u`. -/
@[ext]
structure Fp2Val (p : Nat) where
  /-- The `1`-component. -/
  c0 : ZMod p
  /-- The `u`-component. -/
  c1 : ZMod p

namespace Fp2Val

variable {p : Nat}

/-- Zero of `Fp2Val`. -/
instance : Zero (Fp2Val p) := ⟨⟨0, 0⟩⟩
/-- One of `Fp2Val` (`1 + 0·u`). -/
instance : One (Fp2Val p) := ⟨⟨1, 0⟩⟩
/-- Componentwise addition. -/
instance : Add (Fp2Val p) := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1⟩⟩
/-- Componentwise negation. -/
instance : Neg (Fp2Val p) := ⟨fun x => ⟨-x.c0, -x.c1⟩⟩
/-- Componentwise subtraction. -/
instance : Sub (Fp2Val p) := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1⟩⟩
/-- Multiplication with the `u² = −1` reduction:
    `(a+bu)(c+du) = (ac−bd) + (ad+bc)u`. -/
instance : Mul (Fp2Val p) :=
  ⟨fun x y => ⟨x.c0 * y.c0 - x.c1 * y.c1, x.c0 * y.c1 + x.c1 * y.c0⟩⟩

@[simp] theorem add_c0 (x y : Fp2Val p) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : Fp2Val p) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem sub_c0 (x y : Fp2Val p) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : Fp2Val p) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem neg_c0 (x : Fp2Val p) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : Fp2Val p) : (-x).c1 = -x.c1 := rfl
@[simp] theorem mul_c0 (x y : Fp2Val p) : (x * y).c0 = x.c0 * y.c0 - x.c1 * y.c1 := rfl
@[simp] theorem mul_c1 (x y : Fp2Val p) : (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 := rfl

/-- The `Fp2` Frobenius (the `p`-power map): conjugation `a + b·u ↦ a − b·u`.
    For the `u² = −1` extension `x^p = conj x`, so this is the abstract
    Frobenius. -/
def frobenius (x : Fp2Val p) : Fp2Val p := ⟨x.c0, -x.c1⟩

@[simp] theorem frobenius_c0 (x : Fp2Val p) : (frobenius x).c0 = x.c0 := rfl
@[simp] theorem frobenius_c1 (x : Fp2Val p) : (frobenius x).c1 = -x.c1 := rfl

/-- β-parametric quadratic multiply for the tower `Fp2 = Fp[u]/(u² − β)`, i.e.
    `u² = β`: `(a+bu)(c+du) = (ac + β·bd) + (ad+bc)u`. The existing `Mul`
    instance is the `β = −1` case (BLS12-381/BN254); `β = −5` gives the
    BLS12-377 quadratic extension. Additive parametrization — the `−1` tower is
    untouched. -/
def mulBeta (β : ZMod p) (x y : Fp2Val p) : Fp2Val p :=
  ⟨x.c0 * y.c0 + β * (x.c1 * y.c1), x.c0 * y.c1 + x.c1 * y.c0⟩

@[simp] theorem mulBeta_c0 (β : ZMod p) (x y : Fp2Val p) :
    (mulBeta β x y).c0 = x.c0 * y.c0 + β * (x.c1 * y.c1) := rfl
@[simp] theorem mulBeta_c1 (β : ZMod p) (x y : Fp2Val p) :
    (mulBeta β x y).c1 = x.c0 * y.c1 + x.c1 * y.c0 := rfl

/-- The β-parametric multiply specialises to the existing `u² = −1` multiply at
    `β = −1`. -/
theorem mulBeta_neg_one (x y : Fp2Val p) : mulBeta (-1) x y = x * y := by
  ext <;> simp [mulBeta, sub_eq_add_neg]

end Fp2Val

/-- A cubic-extension value `Fp6 = Fp2[v]/(v³−ξ)`: `a0 + a1·v + a2·v²`, with
    `a0 a1 a2 : Fp2Val p` and the non-residue scalar carried at the op. -/
@[ext]
structure Fp6Val (p : Nat) where
  /-- The `1`-component. -/
  a0 : Fp2Val p
  /-- The `v`-component. -/
  a1 : Fp2Val p
  /-- The `v²`-component. -/
  a2 : Fp2Val p

namespace Fp6Val

variable {p : Nat}

/-- The `Fp2` non-residue `ξ = ξ₀ + u` (multiplication of an `Fp2` element by the
    `Fp6` non-residue, `mul_xi`). `(a+bu)·(ξ₀+u) = (a·ξ₀ − b) + (a + b·ξ₀)·u`. -/
def mulXi (ξ0 : ZMod p) (x : Fp2Val p) : Fp2Val p :=
  ⟨x.c0 * ξ0 - x.c1, x.c0 + x.c1 * ξ0⟩

/-- Componentwise addition. -/
def add (x y : Fp6Val p) : Fp6Val p := ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2⟩
/-- Componentwise subtraction. -/
def sub (x y : Fp6Val p) : Fp6Val p := ⟨x.a0 - y.a0, x.a1 - y.a1, x.a2 - y.a2⟩
/-- Schoolbook `Fp6` multiply with the `v³ = ξ` reduction (`ξ = ξ₀ + u`).
    `(a0+a1 v+a2 v²)(b0+b1 v+b2 v²)` with `v³ → ξ`, `v⁴ → ξ·v`, giving
    `c0 = a0 b0 + ξ(a1 b2 + a2 b1)`, `c1 = a0 b1 + a1 b0 + ξ(a2 b2)`,
    `c2 = a0 b2 + a1 b1 + a2 b0`. -/
def mul (ξ0 : ZMod p) (x y : Fp6Val p) : Fp6Val p :=
  ⟨ x.a0 * y.a0 + mulXi ξ0 (x.a1 * y.a2 + x.a2 * y.a1),
    x.a0 * y.a1 + x.a1 * y.a0 + mulXi ξ0 (x.a2 * y.a2),
    x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0 ⟩

/-- β-parametric `Fp2` non-residue fold `·(ξ₀ + u)` for the tower `u² = β`:
    `(a+bu)·(ξ₀+u) = (a·ξ₀ + β·b) + (a + b·ξ₀)·u`. The `β = −1` case is `mulXi`. -/
def mulXiBeta (β ξ0 : ZMod p) (x : Fp2Val p) : Fp2Val p :=
  ⟨x.c0 * ξ0 + β * x.c1, x.c0 + x.c1 * ξ0⟩

/-- `mulXiBeta` specialises to `mulXi` at `β = −1`. -/
theorem mulXiBeta_neg_one (ξ0 : ZMod p) (x : Fp2Val p) :
    mulXiBeta (-1) ξ0 x = mulXi ξ0 x := by
  ext <;> simp [mulXiBeta, mulXi, sub_eq_add_neg]

/-- β-parametric schoolbook `Fp6` multiply: `Fp6Val.mul` with every `Fp2`
    product replaced by `Fp2Val.mulBeta β` and `mulXi` by `mulXiBeta β`. -/
def mulBeta (β ξ0 : ZMod p) (x y : Fp6Val p) : Fp6Val p :=
  ⟨ Fp2Val.mulBeta β x.a0 y.a0
      + mulXiBeta β ξ0 (Fp2Val.mulBeta β x.a1 y.a2 + Fp2Val.mulBeta β x.a2 y.a1),
    Fp2Val.mulBeta β x.a0 y.a1 + Fp2Val.mulBeta β x.a1 y.a0
      + mulXiBeta β ξ0 (Fp2Val.mulBeta β x.a2 y.a2),
    Fp2Val.mulBeta β x.a0 y.a2 + Fp2Val.mulBeta β x.a1 y.a1
      + Fp2Val.mulBeta β x.a2 y.a0 ⟩

/-- The β-parametric `Fp6` multiply specialises to `Fp6Val.mul` at `β = −1`. -/
theorem mulBeta_neg_one (ξ0 : ZMod p) (x y : Fp6Val p) :
    mulBeta (-1) ξ0 x y = mul ξ0 x y := by
  simp only [mulBeta, mul, Fp2Val.mulBeta_neg_one, mulXiBeta_neg_one]

end Fp6Val

/-- A quadratic-extension value `Fp12 = Fp6[w]/(w²−v)`: `a + b·w`, with the
    `Fp6` non-residue `v` (the `mulByV` twist). This is the pairing target `GT`. -/
@[ext]
structure Fp12Val (p : Nat) where
  /-- The `1`-component. -/
  c0 : Fp6Val p
  /-- The `w`-component. -/
  c1 : Fp6Val p

namespace Fp12Val

variable {p : Nat}

/-- Multiply an `Fp6` element by `v` (the `w² = v` twist): cyclic shift of the
    `Fp6` coefficients with the top coefficient multiplied by the `Fp6`
    non-residue `ξ`. `(a0+a1 v+a2 v²)·v = ξ·a2 + a0·v + a1·v²`. -/
def mulByV (ξ0 : ZMod p) (x : Fp6Val p) : Fp6Val p :=
  ⟨Fp6Val.mulXi ξ0 x.a2, x.a0, x.a1⟩

/-- Componentwise addition. -/
def add (x y : Fp12Val p) : Fp12Val p :=
  ⟨Fp6Val.add x.c0 y.c0, Fp6Val.add x.c1 y.c1⟩
/-- Componentwise subtraction. -/
def sub (x y : Fp12Val p) : Fp12Val p :=
  ⟨Fp6Val.sub x.c0 y.c0, Fp6Val.sub x.c1 y.c1⟩
/-- Karatsuba `Fp12` multiply with the `w² = v` reduction:
    `(a+bw)(c+dw) = (ac + v·bd) + (ad+bc)w`. -/
def mul (ξ0 : ZMod p) (x y : Fp12Val p) : Fp12Val p :=
  let ac := Fp6Val.mul ξ0 x.c0 y.c0
  let bd := Fp6Val.mul ξ0 x.c1 y.c1
  let ad := Fp6Val.mul ξ0 x.c0 y.c1
  let bc := Fp6Val.mul ξ0 x.c1 y.c0
  ⟨Fp6Val.add ac (mulByV ξ0 bd), Fp6Val.add ad bc⟩

/-- β-parametric `Fp6`-by-`v` fold (the `w² = v` twist) for the tower `u² = β`:
    `Fp12Val.mulByV` with `mulXi` replaced by `mulXiBeta β`. -/
def mulByVBeta (β ξ0 : ZMod p) (x : Fp6Val p) : Fp6Val p :=
  ⟨Fp6Val.mulXiBeta β ξ0 x.a2, x.a0, x.a1⟩

/-- `mulByVBeta` specialises to `mulByV` at `β = −1`. -/
theorem mulByVBeta_neg_one (ξ0 : ZMod p) (x : Fp6Val p) :
    mulByVBeta (-1) ξ0 x = mulByV ξ0 x := by
  simp only [mulByVBeta, mulByV, Fp6Val.mulXiBeta_neg_one]

/-- β-parametric Karatsuba `Fp12` multiply: `Fp12Val.mul` with `Fp6Val.mul`
    replaced by `Fp6Val.mulBeta β` and `mulByV` by `mulByVBeta β`. -/
def mulBeta (β ξ0 : ZMod p) (x y : Fp12Val p) : Fp12Val p :=
  let ac := Fp6Val.mulBeta β ξ0 x.c0 y.c0
  let bd := Fp6Val.mulBeta β ξ0 x.c1 y.c1
  let ad := Fp6Val.mulBeta β ξ0 x.c0 y.c1
  let bc := Fp6Val.mulBeta β ξ0 x.c1 y.c0
  ⟨Fp6Val.add ac (mulByVBeta β ξ0 bd), Fp6Val.add ad bc⟩

/-- The β-parametric `Fp12` multiply specialises to `Fp12Val.mul` at `β = −1`. -/
theorem mulBeta_neg_one (ξ0 : ZMod p) (x y : Fp12Val p) :
    mulBeta (-1) ξ0 x y = mul ξ0 x y := by
  simp only [mulBeta, mul, Fp6Val.mulBeta_neg_one, mulByVBeta_neg_one]

end Fp12Val

/-! ## 2. Types (`FieldTy`) -/

/-- The Field dialect's value-type alphabet: the prime field and the pairing
    extension tower, each carrying the modulus `p`. -/
inductive FieldTy where
  /-- The prime field `F_p`, `⟦·⟧ = ZMod p`. -/
  | fp (p : Nat)
  /-- The quadratic extension `Fp2`, `⟦·⟧ = Fp2Val p`. -/
  | fp2 (p : Nat)
  /-- The cubic extension `Fp6`, `⟦·⟧ = Fp6Val p`. -/
  | fp6 (p : Nat)
  /-- The quadratic-over-cubic extension `Fp12` (= `GT`), `⟦·⟧ = Fp12Val p`. -/
  | fp12 (p : Nat)
  deriving DecidableEq

/-- Total denotation of `FieldTy`: each type denotes into its abstract
    extension-field value (the `ZMod p`-built tower). -/
@[reducible] instance : TyDenote FieldTy where
  denote
    | .fp p => ZMod p
    | .fp2 p => Fp2Val p
    | .fp6 p => Fp6Val p
    | .fp12 p => Fp12Val p

/-! ## 3. Concrete leaf functions

Prime-field leaves delegate to the ModArith leaves (so a Field `fMul` *is* a
ModArith `modMul`, the lowering tie is a direct equality).  The extension leaves
are the abstract `Fp2Val`/`Fp6Val`/`Fp12Val` operations. -/

/-- Prime-field add: delegates to `ModArith`'s `modAddF`. -/
@[reducible] def fAddF {p : Nat} (a b : ZMod p) : ZMod p := modAddF a b
/-- Prime-field sub. -/
@[reducible] def fSubF {p : Nat} (a b : ZMod p) : ZMod p := modSubF a b
/-- Prime-field negate. -/
@[reducible] def fNegF {p : Nat} (a : ZMod p) : ZMod p := modNegF a
/-- Prime-field multiply. -/
@[reducible] def fMulF {p : Nat} (a b : ZMod p) : ZMod p := modMulF a b
/-- Prime-field inverse (delegates to `ModArith`'s `byInverseF`). -/
@[reducible] def fInvF {p : Nat} (a : ZMod p) : ZMod p := byInverseF a

/-- Prime-field nullary constant: the fixed element `c : ZMod p`, independent of
    any input (delegates to `ModArith`'s `modConstF`). This is the field layer's
    home for a round/field constant — the single constant-producing op of the
    algebraic field alphabet (every other `FieldOp` takes at least one field
    argument, so without it every `Com fieldDialect` value originates from a
    context `Var`). -/
@[reducible] def fConstF {p : Nat} (c : ZMod p) : ZMod p := modConstF c

/-- Prime-field identity/copy: returns its single argument unchanged (delegates
    to `ModArith`'s `modCopyF`). This is the field layer's home for a
    **designated-output lane copy** — materializing a value as its own binding,
    the shape a multi-output store ABI reads as one output slot. Its byte
    realization is the idempotent `x | x = x` word copy, so a single-output emit
    stages each of the N final state lanes as one trailing binding. -/
@[reducible] def fCopyF {p : Nat} (a : ZMod p) : ZMod p := modCopyF a

/-- Prime-field doubling `a ↦ a + a` (prime-ir `field.double`). -/
@[reducible] def fDoubleF {p : Nat} (a : ZMod p) : ZMod p := a + a

/-- Prime-field squaring `a ↦ a * a` (prime-ir `field.square`). -/
@[reducible] def fSquareF {p : Nat} (a : ZMod p) : ZMod p := a * a

/-- `Fp2` Karatsuba multiply (the abstract `Fp2Val` product). -/
@[reducible] def ext2MulF {p : Nat} (a b : Fp2Val p) : Fp2Val p := a * b
/-- `Fp2` add. -/
@[reducible] def ext2AddF {p : Nat} (a b : Fp2Val p) : Fp2Val p := a + b
/-- `Fp2` sub. -/
@[reducible] def ext2SubF {p : Nat} (a b : Fp2Val p) : Fp2Val p := a - b
/-- `Fp2` Frobenius (conjugation `a + bu ↦ a − bu`). -/
@[reducible] def frobenius2F {p : Nat} (a : Fp2Val p) : Fp2Val p := Fp2Val.frobenius a

/-- `Fp6` multiply (Karatsuba/schoolbook over `Fp2`, non-residue `ξ₀`). -/
@[reducible] def ext6MulF {p : Nat} (ξ0 : ZMod p) (a b : Fp6Val p) : Fp6Val p :=
  Fp6Val.mul ξ0 a b
/-- `Fp6` add. -/
@[reducible] def ext6AddF {p : Nat} (a b : Fp6Val p) : Fp6Val p := Fp6Val.add a b
/-- `Fp6` sub. -/
@[reducible] def ext6SubF {p : Nat} (a b : Fp6Val p) : Fp6Val p := Fp6Val.sub a b

/-- `Fp12` multiply (Karatsuba over `Fp6`, non-residue `ξ₀`). -/
@[reducible] def ext12MulF {p : Nat} (ξ0 : ZMod p) (a b : Fp12Val p) : Fp12Val p :=
  Fp12Val.mul ξ0 a b
/-- `Fp12` add. -/
@[reducible] def ext12AddF {p : Nat} (a b : Fp12Val p) : Fp12Val p := Fp12Val.add a b
/-- `Fp12` sub. -/
@[reducible] def ext12SubF {p : Nat} (a b : Fp12Val p) : Fp12Val p := Fp12Val.sub a b

/-! ## 4. Op tags -/

/-- Operation tags for the Field dialect: the prime-field ops at `fp` and the
    extension-tower ops at `fp2`/`fp6`/`fp12`. The extension-multiply ops carry
    the curve's non-residue scalar `ξ₀`. -/
inductive FieldOp where
  /-- Prime-field add `a + b : fp p`. -/
  | fAdd (p : Nat)
  /-- Prime-field sub `a - b : fp p`. -/
  | fSub (p : Nat)
  /-- Prime-field negate `-a : fp p`. -/
  | fNeg (p : Nat)
  /-- Prime-field multiply `a * b : fp p`. -/
  | fMul (p : Nat)
  /-- Prime-field inverse `a⁻¹ : fp p`. -/
  | fInv (p : Nat)
  /-- Prime-field nullary constant `c : fp p` (sig `[]`). The field layer's home
      for a round/field constant. -/
  | fConst (p : Nat) (c : ZMod p)
  /-- Prime-field identity/copy `a : fp p` (sig `[fp p]`). Materializes a
      designated-output lane as its own binding (multi-output staging). -/
  | fCopy (p : Nat)
  /-- Prime-field doubling `a + a : fp p` (sig `[fp p]`), prime-ir
      `field.double`. A fold of `derivedDialect`'s `fieldDouble` into this
      dialect: a `Com` is indexed by one dialect, so an op kept in a dialect of
      its own cannot sit beside `fMul`. A coproduct
      `fieldDialect ⊕ derivedDialect` with an injection is unnecessary: the value
      types coincide (`DerivedTy.fp p` and `FieldTy.fp p` both denote `ZMod p`), so
      the op is carried here directly. -/
  | fieldDouble (p : Nat)
  /-- Prime-field squaring `a * a : fp p` (sig `[fp p]`), prime-ir
      `field.square`. Folded in from `derivedDialect` alongside `fieldDouble`,
      for the same reason: one-dialect indexing of `Com`, and a shared `ZMod p`
      carrier that makes the coproduct injection unnecessary. -/
  | fieldSquare (p : Nat)
  /-- `Fp2` Karatsuba multiply `a * b : fp2 p`. -/
  | ext2Mul (p : Nat)
  /-- `Fp2` add. -/
  | ext2Add (p : Nat)
  /-- `Fp2` sub. -/
  | ext2Sub (p : Nat)
  /-- `Fp2` Frobenius (conjugation) `a^p : fp2 p`. -/
  | frobenius2 (p : Nat)
  /-- `Fp6` multiply (non-residue `ξ₀`) `a * b : fp6 p`. -/
  | ext6Mul (p : Nat) (ξ0 : ZMod p)
  /-- `Fp6` add. -/
  | ext6Add (p : Nat)
  /-- `Fp6` sub. -/
  | ext6Sub (p : Nat)
  /-- `Fp12` Karatsuba multiply (non-residue `ξ₀`) `a * b : fp12 p`. -/
  | ext12Mul (p : Nat) (ξ0 : ZMod p)
  /-- `Fp12` add. -/
  | ext12Add (p : Nat)
  /-- `Fp12` sub. -/
  | ext12Sub (p : Nat)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The Field dialect: `Op` is `FieldOp`, `Ty` is `FieldTy`. -/
@[reducible] def fieldDialect : Dialect :=
  { Op := FieldOp, Ty := FieldTy }

/-! ## 6. Op signatures -/

instance : DialectSignature fieldDialect where
  sig op := match op with
    | .fAdd p => [.fp p, .fp p]
    | .fSub p => [.fp p, .fp p]
    | .fNeg p => [.fp p]
    | .fMul p => [.fp p, .fp p]
    | .fInv p => [.fp p]
    | .fConst _ _ => []
    | .fCopy p => [.fp p]
    | .fieldDouble p => [.fp p]
    | .fieldSquare p => [.fp p]
    | .ext2Mul p => [.fp2 p, .fp2 p]
    | .ext2Add p => [.fp2 p, .fp2 p]
    | .ext2Sub p => [.fp2 p, .fp2 p]
    | .frobenius2 p => [.fp2 p]
    | .ext6Mul p _ => [.fp6 p, .fp6 p]
    | .ext6Add p => [.fp6 p, .fp6 p]
    | .ext6Sub p => [.fp6 p, .fp6 p]
    | .ext12Mul p _ => [.fp12 p, .fp12 p]
    | .ext12Add p => [.fp12 p, .fp12 p]
    | .ext12Sub p => [.fp12 p, .fp12 p]
  ret op := match op with
    | .fAdd p => .fp p
    | .fSub p => .fp p
    | .fNeg p => .fp p
    | .fMul p => .fp p
    | .fInv p => .fp p
    | .fConst p _ => .fp p
    | .fCopy p => .fp p
    | .fieldDouble p => .fp p
    | .fieldSquare p => .fp p
    | .ext2Mul p => .fp2 p
    | .ext2Add p => .fp2 p
    | .ext2Sub p => .fp2 p
    | .frobenius2 p => .fp2 p
    | .ext6Mul p _ => .fp6 p
    | .ext6Add p => .fp6 p
    | .ext6Sub p => .fp6 p
    | .ext12Mul p _ => .fp12 p
    | .ext12Add p => .fp12 p
    | .ext12Sub p => .fp12 p

/-! ## 7. Op denotation -/

instance fieldDenote : DialectDenote fieldDialect where
  denote op := match op with
    | .fAdd _ => fun args => fAddF args.head args.tail.head
    | .fSub _ => fun args => fSubF args.head args.tail.head
    | .fNeg _ => fun args => fNegF args.head
    | .fMul _ => fun args => fMulF args.head args.tail.head
    | .fInv _ => fun args => fInvF args.head
    | .fConst _ c => fun _ => fConstF c
    | .fCopy _ => fun args => fCopyF args.head
    | .fieldDouble _ => fun args => fDoubleF args.head
    | .fieldSquare _ => fun args => fSquareF args.head
    | .ext2Mul _ => fun args => ext2MulF args.head args.tail.head
    | .ext2Add _ => fun args => ext2AddF args.head args.tail.head
    | .ext2Sub _ => fun args => ext2SubF args.head args.tail.head
    | .frobenius2 _ => fun args => frobenius2F args.head
    | .ext6Mul _ ξ0 => fun args => ext6MulF ξ0 args.head args.tail.head
    | .ext6Add _ => fun args => ext6AddF args.head args.tail.head
    | .ext6Sub _ => fun args => ext6SubF args.head args.tail.head
    | .ext12Mul _ ξ0 => fun args => ext12MulF ξ0 args.head args.tail.head
    | .ext12Add _ => fun args => ext12AddF args.head args.tail.head
    | .ext12Sub _ => fun args => ext12SubF args.head args.tail.head

/-! ## 8. Constant-time predicate (L3 instance of `CTPredicate.lean`)

Every Field op is data-oblivious: extension-field arithmetic is a fixed schedule
of base-field ops (no `ite` on data, no data-dependent index). So `ctSafe` is
`true` for all ops, mirroring `ModArithOp.ctSafe`. -/

/-- Per-op CT predicate: every Field op is constant-time. -/
def FieldOp.ctSafe : FieldOp → Bool
  | _ => true

@[simp] theorem FieldOp.ctSafe_all (op : FieldOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is. Since all Field ops are CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt fieldDialect} {t : FieldTy} :
    Com fieldDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.** Every Field program is constant-time — the L3-level
    realisation of the VIR CT-safety guarantee. -/
theorem ctSafeCom_all {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

/-- Propositional form, decidable. -/
def ctSafePropCom {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : Prop :=
  ctSafeCom c = true

instance {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : Decidable (ctSafePropCom c) := by
  unfold ctSafePropCom; infer_instance

/-! ## 9. Algebraic denotation facts (the once-per-dialect ties)

These hold **definitionally** because the op denotations are the abstract
extension-field operations. Stated once at the dialect, not re-proved per
migrated curve. -/

/-- `fMul` denotes to `ZMod p` multiplication (= ModArith `modMul`). -/
theorem fMul_denote {p : Nat} (a b : ZMod p) :
    fieldDenote.denote (.fMul p) (.cons a (.cons b .nil)) = a * b := rfl

/-- `fInv` denotes to `ZMod`'s native inverse (= ModArith `byInverse`). -/
theorem fInv_denote {p : Nat} (a : ZMod p) :
    fieldDenote.denote (.fInv p) (.cons a .nil) = a⁻¹ := rfl

/-- `fConst` denotes to its carried constant `c`, independent of the (empty)
    argument vector (= ModArith `modConst`). -/
theorem fConst_denote {p : Nat} (c : ZMod p) :
    fieldDenote.denote (.fConst p c) .nil = c := rfl

/-- `ext2Mul` denotes to the abstract `Fp2` product (the Karatsuba result). -/
theorem ext2Mul_denote {p : Nat} (a b : Fp2Val p) :
    fieldDenote.denote (.ext2Mul p) (.cons a (.cons b .nil)) = a * b := rfl

/-- The `Fp2` multiply denotes coefficient-wise to the Karatsuba formula
    `(ac−bd) + (ad+bc)u`. -/
theorem ext2Mul_denote_c0 {p : Nat} (a b : Fp2Val p) :
    (fieldDenote.denote (.ext2Mul p) (.cons a (.cons b .nil))).c0
      = a.c0 * b.c0 - a.c1 * b.c1 := rfl

theorem ext2Mul_denote_c1 {p : Nat} (a b : Fp2Val p) :
    (fieldDenote.denote (.ext2Mul p) (.cons a (.cons b .nil))).c1
      = a.c0 * b.c1 + a.c1 * b.c0 := rfl

/-- `frobenius2` denotes to the abstract `Fp2` Frobenius (conjugation). -/
theorem frobenius2_denote {p : Nat} (a : Fp2Val p) :
    fieldDenote.denote (.frobenius2 p) (.cons a .nil) = Fp2Val.frobenius a := rfl

/-- `ext6Mul` denotes to the abstract `Fp6` product. -/
theorem ext6Mul_denote {p : Nat} (ξ0 : ZMod p) (a b : Fp6Val p) :
    fieldDenote.denote (.ext6Mul p ξ0) (.cons a (.cons b .nil)) = Fp6Val.mul ξ0 a b := rfl

/-- `ext12Mul` denotes to the abstract `Fp12` product (the `GT` op). -/
theorem ext12Mul_denote {p : Nat} (ξ0 : ZMod p) (a b : Fp12Val p) :
    fieldDenote.denote (.ext12Mul p ξ0) (.cons a (.cons b .nil)) = Fp12Val.mul ξ0 a b := rfl

/-! ## 10. Smoke test

A tiny two-op `Com fieldDialect` over `ZMod 7`: `let c = ext2Mul a b; ret c`.
On `a = 2 + 3u, b = 1 + 1u`, the product is `(2·1 − 3·1) + (2·1 + 3·1)u =
−1 + 5u = 6 + 5u (mod 7)`. -/

/-- Two-op smoke program: one `ext2Mul` over `[fp2 7, fp2 7]`. -/
def smokeProg : Com fieldDialect [.fp2 7, .fp2 7] (.fp2 7) :=
  .var (.mk (.ext2Mul 7) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The smoke program denotes to the `Fp2` product; on `a = 2 + 3u, b = 1 + u`
    that is `6 + 5u (mod 7)`. -/
example :
    smokeProg.denote
        (.cons (⟨2, 3⟩ : Fp2Val 7) (.cons (⟨1, 1⟩ : Fp2Val 7) .nil))
      = (⟨6, 5⟩ : Fp2Val 7) := by
  rfl

/-! ## 11. Representation annotations

`fieldDialectAt ρ` is `fieldDialect` with its types indexed by the representation map
`ρ` of `ModArithDialect`: `!field.pf<p : iW, true>` and the extension types over `p`
are stored as `ρ p` fixes. As for `modArithDialectAt`, the index unfolds away, so
the instances and the denotation are those of `fieldDialect`. -/

/-- The type alphabet of `fieldDialect` indexed by the representation map `ρ`. -/
abbrev FieldTyAt (_ρ : ModArithReprMap) : Type := FieldTy

/-- The representation a type carries: `ρ p` at every type over the modulus `p`. -/
def FieldTyAt.repr {ρ : ModArithReprMap} : FieldTyAt ρ → ModArithRepr
  | .fp p | .fp2 p | .fp6 p | .fp12 p => ρ p

/-- `fieldDialect` with its types indexed by the representation map `ρ`. -/
@[reducible] def fieldDialectAt (_ρ : ModArithReprMap) : Dialect :=
  { Op := FieldOp, Ty := FieldTyAt _ρ }

/-- The dialect indexed by the map that fixes nothing is `fieldDialect`. -/
theorem fieldDialectAt_unfixed : fieldDialectAt .unfixed = fieldDialect := rfl

/-- A program of `fieldDialect` annotated with the representation map `ρ`. -/
def annotateFieldCom (ρ : ModArithReprMap) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : Com (fieldDialectAt ρ) Γ t := c

/-- The program of `fieldDialect` underlying an annotated program. -/
def unannotateFieldCom {ρ : ModArithReprMap} {Γ : Ctxt (fieldDialectAt ρ)}
    {t : FieldTyAt ρ} (c : Com (fieldDialectAt ρ) Γ t) : Com fieldDialect Γ t := c

/-- The annotation does not change the denotation. -/
theorem denote_annotateFieldCom (ρ : ModArithReprMap) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (c : Com fieldDialect Γ t) (V : Ctxt.Valuation Γ) :
    (annotateFieldCom ρ c).denote V = c.denote V := rfl

/-- Removing the annotation does not change the denotation. -/
theorem denote_unannotateFieldCom {ρ : ModArithReprMap} {Γ : Ctxt (fieldDialectAt ρ)}
    {t : FieldTyAt ρ} (c : Com (fieldDialectAt ρ) Γ t) (V : Ctxt.Valuation Γ) :
    (unannotateFieldCom c).denote V = c.denote V := rfl

/-! ## 12. Extension-field descriptors

prime-ir has one extension-field type, `!field.ef<N x B, ξ>`: the binomial extension
`B[v]/(vᴺ − ξ)` of a base field `B`, itself a prime field or an extension. `ExtDesc`
describes such a field, and `ExtDesc.Carrier` with `ExtDesc.mul` is its arithmetic
on coefficient vectors. The non-residue `ξ ∈ B` is the list of its coefficients over
`F_p` in the order of the tower, the flat form of prime-ir's dense attribute; a
shorter list is padded with zeros, so a one-element list `[ξ₀]` is the scalar `ξ₀`. -/

/-- A field in prime-ir's form: a prime field, or a binomial extension of a field. -/
inductive ExtDesc where
  /-- The prime field `F_p` (`!field.pf<p>`). -/
  | prime (p : Nat)
  /-- The extension `B[v]/(vⁿ − ξ)` of `base = B` (`!field.ef<n x B, ξ>`), with `ξ`
      given by its coefficients over `F_p`. -/
  | ext (degree : Nat) (base : ExtDesc) (nonResidue : List Int)
  deriving DecidableEq, Repr

namespace ExtDesc

/-- The modulus of the prime field at the bottom of the tower. -/
def modulus : ExtDesc → Nat
  | prime p => p
  | ext _ b _ => b.modulus

/-- The degree over the prime field. -/
def degreeOverPrime : ExtDesc → Nat
  | prime _ => 1
  | ext n b _ => n * b.degreeOverPrime

/-- The degrees of the tower from the top: `[]` at a prime field. -/
def shape : ExtDesc → List Nat
  | prime _ => []
  | ext n b _ => n :: b.shape

/-- The elements: `ZMod p` at a prime field, coefficient vectors over the base at
    an extension. -/
@[reducible] def Carrier : ExtDesc → Type
  | prime p => ZMod p
  | ext n b _ => Fin n → b.Carrier

/-- Zero. -/
def zero : (d : ExtDesc) → d.Carrier
  | prime p => (0 : ZMod p)
  | ext _ b _ => fun _ => b.zero

/-- Coefficientwise addition. -/
def add : (d : ExtDesc) → d.Carrier → d.Carrier → d.Carrier
  | prime p, x, y => (x + y : ZMod p)
  | ext _ b _, x, y => fun i => b.add (x i) (y i)

/-- The element with the given coefficients over `F_p`, missing coefficients zero. -/
def ofFlat : (d : ExtDesc) → List Int → d.Carrier
  | prime p, l => ((l.headD 0 : Int) : ZMod p)
  | ext _ b _, l => fun i => b.ofFlat (l.drop (i.val * b.degreeOverPrime))

/-- The sum `f 0 + ⋯ + f (m − 1)`. -/
def sum (d : ExtDesc) : Nat → (Nat → d.Carrier) → d.Carrier
  | 0, _ => d.zero
  | m + 1, f => d.add (d.sum m f) (f m)

/-- The coefficient `i` of a vector of length `n`, zero for `i ≥ n`. -/
def coeff {n : Nat} (b : ExtDesc) (x : Fin n → b.Carrier) (i : Nat) : b.Carrier :=
  if h : i < n then x ⟨i, h⟩ else b.zero

/-- Multiplication: at an extension `B[v]/(vⁿ − ξ)`, coefficient `k` of the product
    is `Σ_{i+j=k} xᵢ yⱼ + ξ · Σ_{i+j=k+n} xᵢ yⱼ`. -/
def mul : (d : ExtDesc) → d.Carrier → d.Carrier → d.Carrier
  | prime p, x, y => (x * y : ZMod p)
  | ext n b nr, x, y => fun k =>
      b.sum n fun i => b.sum n fun j =>
        if i + j = k.val then b.mul (coeff b x i) (coeff b y j)
        else if i + j = k.val + n then b.mul (b.ofFlat nr) (b.mul (coeff b x i) (coeff b y j))
        else b.zero

/-- Zero is a left unit of addition. -/
theorem zero_add : (d : ExtDesc) → (x : d.Carrier) → d.add d.zero x = x
  | prime p, x => by simp [add, zero]
  | ext _ b _, x => funext fun i => zero_add b (x i)

/-- Zero is a right unit of addition. -/
theorem add_zero : (d : ExtDesc) → (x : d.Carrier) → d.add x d.zero = x
  | prime p, x => by simp [add, zero]
  | ext _ b _, x => funext fun i => add_zero b (x i)

/-- The quadratic extension `F_p[u]/(u² − β)`. -/
def tower2 (p : Nat) (β : Int) : ExtDesc := ext 2 (prime p) [β]

/-- The cubic extension `Fp2[v]/(v³ − (ξ₀ + u))` of `tower2 p β`. -/
def tower6 (p : Nat) (β ξ0 : Int) : ExtDesc := ext 3 (tower2 p β) [ξ0, 1]

/-- The quadratic extension `Fp6[w]/(w² − v)` of `tower6 p β ξ0`; `v` has the
    coefficients `[0, 0, 1, 0, 0, 0]` over `F_p`. -/
def tower12 (p : Nat) (β ξ0 : Int) : ExtDesc := ext 2 (tower6 p β ξ0) [0, 0, 1, 0, 0, 0]

end ExtDesc

/-! ## 13. The towers as descriptor instances

`Fp2Val`, `Fp6Val` and `Fp12Val` with the β-parametric multiplies are the fields of
`tower2 p β`, `tower6 p β ξ₀` and `tower12 p β ξ₀`: each `equivDesc` is a bijection
onto the descriptor's carrier, and `toDesc_mulBeta` carries `mulBeta` to
`ExtDesc.mul`. At `β = −1` these are the dialect's types (`toDesc_mul`); at `β = −5`,
`ξ₀ = 0` they are the BLS12-377 tower. -/

namespace Fp2Val

variable {p : Nat}

/-- The coefficient vector of an `Fp2` value. -/
def toDesc (β : Int) (x : Fp2Val p) : (ExtDesc.tower2 p β).Carrier := ![x.c0, x.c1]

/-- The `Fp2` value of a coefficient vector. -/
def ofDesc (β : Int) (v : (ExtDesc.tower2 p β).Carrier) : Fp2Val p := ⟨v 0, v 1⟩

/-- `Fp2Val p` and the carrier of `tower2 p β` are equivalent. -/
def equivDesc (β : Int) : Fp2Val p ≃ (ExtDesc.tower2 p β).Carrier where
  toFun := toDesc β
  invFun := ofDesc β
  left_inv _ := rfl
  right_inv v := by
    funext k
    fin_cases k <;> rfl

/-- The β-parametric multiply is the descriptor's multiply. -/
theorem toDesc_mulBeta (β : Int) (x y : Fp2Val p) :
    toDesc β (mulBeta (β : ZMod p) x y) = (ExtDesc.tower2 p β).mul (toDesc β x) (toDesc β y) := by
  funext k
  fin_cases k <;>
    simp [toDesc, mulBeta, ExtDesc.tower2, ExtDesc.mul, ExtDesc.sum, ExtDesc.coeff,
      ExtDesc.ofFlat, ExtDesc.add, ExtDesc.zero]

/-- The `Fp2` multiply is the multiply of `tower2 p (−1)`. -/
theorem toDesc_mul (x y : Fp2Val p) :
    toDesc (-1) (x * y) = (ExtDesc.tower2 p (-1)).mul (toDesc (-1) x) (toDesc (-1) y) := by
  rw [← mulBeta_neg_one, ← toDesc_mulBeta]
  push_cast
  rfl

end Fp2Val

namespace Fp6Val

variable {p : Nat}

/-- The coefficient vector of an `Fp6` value. -/
def toDesc (β ξ0 : Int) (x : Fp6Val p) : (ExtDesc.tower6 p β ξ0).Carrier :=
  ![Fp2Val.toDesc β x.a0, Fp2Val.toDesc β x.a1, Fp2Val.toDesc β x.a2]

/-- The `Fp6` value of a coefficient vector. -/
def ofDesc (β ξ0 : Int) (v : (ExtDesc.tower6 p β ξ0).Carrier) : Fp6Val p :=
  ⟨Fp2Val.ofDesc β (v 0), Fp2Val.ofDesc β (v 1), Fp2Val.ofDesc β (v 2)⟩

/-- `Fp6Val p` and the carrier of `tower6 p β ξ0` are equivalent. -/
def equivDesc (β ξ0 : Int) : Fp6Val p ≃ (ExtDesc.tower6 p β ξ0).Carrier where
  toFun := toDesc β ξ0
  invFun := ofDesc β ξ0
  left_inv _ := rfl
  right_inv v := by
    funext k c
    fin_cases k <;> fin_cases c <;> rfl

/-- The β-parametric multiply is the descriptor's multiply. -/
theorem toDesc_mulBeta (β ξ0 : Int) (x y : Fp6Val p) :
    toDesc β ξ0 (mulBeta (β : ZMod p) (ξ0 : ZMod p) x y)
      = (ExtDesc.tower6 p β ξ0).mul (toDesc β ξ0 x) (toDesc β ξ0 y) := by
  funext k c
  fin_cases k <;> fin_cases c <;>
    simp [toDesc, Fp2Val.toDesc, mulBeta, mulXiBeta, Fp2Val.mulBeta, ExtDesc.tower6,
      ExtDesc.tower2, ExtDesc.mul, ExtDesc.sum, ExtDesc.coeff,
      ExtDesc.ofFlat, ExtDesc.add, ExtDesc.zero, ExtDesc.degreeOverPrime] <;> ring

/-- The `Fp6` multiply is the multiply of `tower6 p (−1) ξ0`. -/
theorem toDesc_mul (ξ0 : Int) (x y : Fp6Val p) :
    toDesc (-1) ξ0 (mul (ξ0 : ZMod p) x y)
      = (ExtDesc.tower6 p (-1) ξ0).mul (toDesc (-1) ξ0 x) (toDesc (-1) ξ0 y) := by
  rw [← mulBeta_neg_one, ← toDesc_mulBeta]
  push_cast
  rfl

/-- The `Fp6` addition is the descriptor's addition. -/
theorem toDesc_add (β ξ0 : Int) (x y : Fp6Val p) :
    toDesc β ξ0 (add x y) = (ExtDesc.tower6 p β ξ0).add (toDesc β ξ0 x) (toDesc β ξ0 y) := by
  funext k c
  fin_cases k <;> fin_cases c <;>
    simp [toDesc, Fp2Val.toDesc, add, ExtDesc.tower6, ExtDesc.tower2, ExtDesc.add]

end Fp6Val

namespace Fp12Val

variable {p : Nat}

/-- The coefficient vector of an `Fp12` value. -/
def toDesc (β ξ0 : Int) (x : Fp12Val p) : (ExtDesc.tower12 p β ξ0).Carrier :=
  ![Fp6Val.toDesc β ξ0 x.c0, Fp6Val.toDesc β ξ0 x.c1]

/-- The `Fp12` value of a coefficient vector. -/
def ofDesc (β ξ0 : Int) (v : (ExtDesc.tower12 p β ξ0).Carrier) : Fp12Val p :=
  ⟨Fp6Val.ofDesc β ξ0 (v 0), Fp6Val.ofDesc β ξ0 (v 1)⟩

/-- `Fp12Val p` and the carrier of `tower12 p β ξ0` are equivalent. -/
def equivDesc (β ξ0 : Int) : Fp12Val p ≃ (ExtDesc.tower12 p β ξ0).Carrier where
  toFun := toDesc β ξ0
  invFun := ofDesc β ξ0
  left_inv _ := rfl
  right_inv v := by
    funext k l c
    fin_cases k <;> fin_cases l <;> fin_cases c <;> rfl

/-- The `w² = v` fold is multiplication by the non-residue of `tower12`. -/
theorem toDesc_mulByVBeta (β ξ0 : Int) (x : Fp6Val p) :
    Fp6Val.toDesc β ξ0 (mulByVBeta (β : ZMod p) (ξ0 : ZMod p) x)
      = (ExtDesc.tower6 p β ξ0).mul ((ExtDesc.tower6 p β ξ0).ofFlat [0, 0, 1, 0, 0, 0])
          (Fp6Val.toDesc β ξ0 x) := by
  funext k c
  fin_cases k <;> fin_cases c <;>
    simp [Fp6Val.toDesc, Fp2Val.toDesc, mulByVBeta, Fp6Val.mulXiBeta, ExtDesc.tower6,
      ExtDesc.tower2, ExtDesc.mul, ExtDesc.sum, ExtDesc.coeff,
      ExtDesc.ofFlat, ExtDesc.add, ExtDesc.zero, ExtDesc.degreeOverPrime] <;> ring

/-- The β-parametric multiply is the descriptor's multiply. -/
theorem toDesc_mulBeta (β ξ0 : Int) (x y : Fp12Val p) :
    toDesc β ξ0 (mulBeta (β : ZMod p) (ξ0 : ZMod p) x y)
      = (ExtDesc.tower12 p β ξ0).mul (toDesc β ξ0 x) (toDesc β ξ0 y) := by
  funext k
  fin_cases k <;>
    simp [toDesc, mulBeta, ExtDesc.tower12, ExtDesc.mul, ExtDesc.sum, ExtDesc.coeff,
      ExtDesc.zero_add, ExtDesc.add_zero, Fp6Val.toDesc_add, Fp6Val.toDesc_mulBeta,
      toDesc_mulByVBeta]

/-- The `Fp12` multiply is the multiply of `tower12 p (−1) ξ0`. -/
theorem toDesc_mul (ξ0 : Int) (x y : Fp12Val p) :
    toDesc (-1) ξ0 (mul (ξ0 : ZMod p) x y)
      = (ExtDesc.tower12 p (-1) ξ0).mul (toDesc (-1) ξ0 x) (toDesc (-1) ξ0 y) := by
  rw [← mulBeta_neg_one, ← toDesc_mulBeta]
  push_cast
  rfl

end Fp12Val

/-- The descriptor of a `FieldTy`, with the tower constant `ξ0 p` over `p`. -/
def FieldTy.extDesc (ξ0 : Nat → Int) : FieldTy → ExtDesc
  | .fp p => .prime p
  | .fp2 p => .tower2 p (-1)
  | .fp6 p => .tower6 p (-1) (ξ0 p)
  | .fp12 p => .tower12 p (-1) (ξ0 p)

/-- The denotation of a `FieldTy` is equivalent to the carrier of its descriptor. -/
def FieldTy.denoteEquiv (ξ0 : Nat → Int) :
    (t : FieldTy) → ⟦t⟧ ≃ (t.extDesc ξ0).Carrier
  | .fp _ => Equiv.refl _
  | .fp2 _ => Fp2Val.equivDesc (-1)
  | .fp6 p => Fp6Val.equivDesc (-1) (ξ0 p)
  | .fp12 p => Fp12Val.equivDesc (-1) (ξ0 p)

/-! ## 14. Tower annotations

`fieldDialectTower τ` is `fieldDialect` with its types indexed by the map `τ` that
fixes, per modulus, the tower constant `ξ₀` of `Fp6 = Fp2[v]/(v³ − (ξ₀ + u))`. The
index unfolds away, so the instances and the denotation are those of `fieldDialect`;
`FieldTyTower.extDesc` reads the descriptor of a type from it. -/

/-- A tower constant per modulus, `none` where the program leaves it to the lowering. -/
abbrev TowerReprMap : Type := Nat → Option Nat

/-- The tower map that fixes nothing. -/
def TowerReprMap.unfixed : TowerReprMap := fun _ => none

/-- The type alphabet of `fieldDialect` indexed by the tower map `τ`. -/
abbrev FieldTyTower (_τ : TowerReprMap) : Type := FieldTy

/-- The descriptor of a type under `τ`; `none` at `Fp6`/`Fp12` over a modulus whose
    tower constant `τ` leaves unfixed. -/
def FieldTyTower.extDesc {τ : TowerReprMap} (t : FieldTyTower τ) : Option ExtDesc :=
  match t with
  | .fp p => some (.prime p)
  | .fp2 p => some (.tower2 p (-1))
  | .fp6 p => (τ p).map fun ξ0 => .tower6 p (-1) ξ0
  | .fp12 p => (τ p).map fun ξ0 => .tower12 p (-1) ξ0

/-- `fieldDialect` with its types indexed by the tower map `τ`. -/
@[reducible] def fieldDialectTower (_τ : TowerReprMap) : Dialect :=
  { Op := FieldOp, Ty := FieldTyTower _τ }

/-- The dialect indexed by the map that fixes nothing is `fieldDialect`. -/
theorem fieldDialectTower_unfixed : fieldDialectTower .unfixed = fieldDialect := rfl

/-- A program of `fieldDialect` annotated with the tower map `τ`. -/
def annotateTowerCom (τ : TowerReprMap) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : Com (fieldDialectTower τ) Γ t := c

/-- The program of `fieldDialect` underlying a tower-annotated program. -/
def unannotateTowerCom {τ : TowerReprMap} {Γ : Ctxt (fieldDialectTower τ)}
    {t : FieldTyTower τ} (c : Com (fieldDialectTower τ) Γ t) : Com fieldDialect Γ t := c

/-- The tower annotation does not change the denotation. -/
theorem denote_annotateTowerCom (τ : TowerReprMap) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (c : Com fieldDialect Γ t) (V : Ctxt.Valuation Γ) :
    (annotateTowerCom τ c).denote V = c.denote V := rfl

/-- Removing the tower annotation does not change the denotation. -/
theorem denote_unannotateTowerCom {τ : TowerReprMap} {Γ : Ctxt (fieldDialectTower τ)}
    {t : FieldTyTower τ} (c : Com (fieldDialectTower τ) Γ t) (V : Ctxt.Valuation Γ) :
    (unannotateTowerCom c).denote V = c.denote V := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
