/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# ModArith Montgomery-domain inverse — first-class `mont_inverse`

A minimal **correspondence** `VIR.Dialect` whose single op is `montInverse`, the
Montgomery-domain field inverse.  It is the CatCrypt counterpart of
fractalyze/prime-ir's `mod_arith.mont_inverse` (`ModArithOps.td`).

## Why this dialect exists (the gap it closes)

Per `PRIME_IR_GAP_ANALYSIS.md` (repo root, §2), CatCrypt already *has* the field
inverse — `ModArithDialect.byInverse` / `FieldDialect.fInv` denote to `ZMod p`'s
native `a⁻¹`, realised by the Bernstein–Yang / Fermat chains — but it does **not**
expose the *Montgomery-domain* inverse as a standalone op.  The gap analysis
classified `mod_arith.mont_inverse` **PARTIAL** — "Fermat chain in Montgomery
domain; no dedicated mont-inverse op".  This dialect **factors that map as a
first-class op**, matching prime-ir's `mod_arith.mont_inverse` one-for-one.

It is a **separate file** from the `to_mont`/`from_mont`/`mont_square` trio
(`ModArithMontOps.lean`) because that file carries residues as **ℤ** with the
`Int.ModEq` redc core, which has no total modular inversion; the inverse is clean
over the **`ZMod p`** carrier, where `⁻¹` is total and the Montgomery convention
is the one `ModArithDialect.montMul`/`montReduce` already fix.

## The Montgomery convention (reused from `ModArithDialect`)

`ModArithDialect.montMulF rInv a b = a · b · R⁻¹` and
`montReduceF rInv t = t · R⁻¹`, where `rInv = (R : ZMod p)⁻¹` is the
Montgomery-radix inverse.  A *residue* `x̃` is the Montgomery form of the logical
value `montReduce rInv x̃ = x̃ · R⁻¹`, and the Montgomery unit (the form of `1`) is
`R = rInv⁻¹`.

## The op (`MontInverseOp`), parametric in `(p, rInv)`

* `montInverse p rInv` — `x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹` (`= x⁻¹ · R²`, since
  `rInv⁻¹ = R`).  This is the residue whose Montgomery product with `x̃` is the
  unit `R`: `montMul rInv x̃ (montInverse x̃) = R`.  Equivalently, its logical value
  is the inverse of `x̃`'s logical value (`montInverse_fromMont`).

## Type (`MontInverseTy`)

* `fp p` — a Montgomery residue at modulus `p`, `⟦·⟧ = ZMod p` (the
  `ModArithDialect.fp` carrier).

## Correctness lemmas (assembled from `ZMod`'s field inverse)

Over a prime modulus (`Fact (Nat.Prime p)`, giving `Field (ZMod p)`), with `x`
and `rInv` nonzero:

* `montInverse_spec` : `montMul rInv x (montInverse rInv x) = rInv⁻¹` — the
  Montgomery product with the inverse is the unit `R`.
* `montInverse_fromMont` : `(fromMont x) · (fromMont (montInverse x)) = 1` — the
  logical values are mutually inverse (the field-level statement).

## Honest classification (read `VIR/DIALECTS.md`)

This is a **HIGH-tier, prime-ir-corresponding / agreement** dialect, NOT an
emit-wired one.  Like `ModArithMontOps`, `tensorExtDialect`, `cmpDialect`, and the
`mlirArith*` family in DIALECTS.md's "correspondence-only" table, it has **no
lowering out** (no `→ Com jasminDialect`, no backend edge).  It substantiates the
"prime-ir `mod_arith.mont_inverse` aligned" claim by giving the Montgomery-domain
inverse a first-class op tied to `ZMod`'s field inverse + the
`ModArithDialect.montMul` convention.  It does **not** add a lowering or emit path
— the bytes-reaching field inverse still flows through the existing Fermat /
Bernstein–Yang emit kernels.  Do not overclaim an emit this file does not build.

## Pure-only + constant-time

The Montgomery inverse is realised by a fixed Fermat / divstep schedule
(data-oblivious by construction — the exponent / step count is public), so its
denotation is a total pure function and it is constant-time (`ctSafe = true`),
exactly the `ModArithDialect.byInverse` CT story.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverse

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect (montMulF montReduceF byInverseF)

/-! ## 1. The leaf function (the Montgomery-domain inverse)

`x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹` (= `x⁻¹ · R²`): the residue whose Montgomery product
with `x̃` is the unit `R = rInv⁻¹`.  Built from `ZMod p`'s native `⁻¹`. -/

/-- `mod_arith.mont_inverse` leaf: the Montgomery-domain inverse
    `x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹` over `ZMod p`, where `rInv = R⁻¹` is the
    Montgomery-radix inverse fixed by `ModArithDialect.montMul` (so `rInv⁻¹ = R`
    and the result is `x⁻¹ · R²`). -/
@[reducible] def montInverseF {p : Nat} (rInv x : ZMod p) : ZMod p :=
  x⁻¹ * rInv⁻¹ * rInv⁻¹

/-! ## 2. Correctness lemmas (assembled from `ZMod`'s native inverse)

Over a prime modulus the carrier is a field, so a nonzero residue is a unit and
`ZMod.mul_inv_of_unit` / `ZMod.inv_mul_of_unit` discharge the cancellations.  We
read the inverse through `ZMod.inv` (the instance `montInverseF` uses), so the
unit witness is built from Fermat's little theorem rather than the field's
`GroupWithZero` inverse, which lives behind a different instance. -/

/-- A nonzero residue at a prime modulus is a unit, witnessed by `x · x^(p-2) = 1`
    (Fermat).  Phrased over `ZMod`'s monoid so it feeds `ZMod.mul_inv_of_unit`. -/
private theorem isUnit_of_ne_zero {p : Nat} [Fact (Nat.Prime p)] {a : ZMod p}
    (ha : a ≠ 0) : IsUnit a :=
  IsUnit.of_mul_eq_one (a ^ (p - 2)) <| by
    rw [← pow_succ', show (p - 2) + 1 = p - 1 from by
      have := (Fact.out : Nat.Prime p).two_le; omega]
    exact ZMod.pow_card_sub_one_eq_one ha

/-- **Montgomery-inverse spec.** The Montgomery product of `x̃` with its
    Montgomery inverse is the unit `R = rInv⁻¹`:
    `montMul rInv x (montInverse rInv x) = rInv⁻¹`. -/
theorem montInverse_spec {p : Nat} [Fact (Nat.Prime p)] (rInv x : ZMod p)
    (hx : x ≠ 0) (hr : rInv ≠ 0) :
    montMulF rInv x (montInverseF rInv x) = rInv⁻¹ := by
  unfold montMulF montInverseF
  have ex : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x (isUnit_of_ne_zero hx)
  have er : rInv⁻¹ * rInv = 1 := ZMod.inv_mul_of_unit rInv (isUnit_of_ne_zero hr)
  rw [show x * (x⁻¹ * rInv⁻¹ * rInv⁻¹) * rInv
        = (x * x⁻¹) * (rInv⁻¹ * rInv) * rInv⁻¹ by ring, ex, er, one_mul, one_mul]

/-- **Logical inverse domain.** The logical (out-of-Montgomery) values of `x̃` and
    of `montInverse x̃` are mutually inverse: `(fromMont x) · (fromMont (montInverse x)) = 1`,
    where `fromMont = montReduce rInv = · R⁻¹`. -/
theorem montInverse_fromMont {p : Nat} [Fact (Nat.Prime p)] (rInv x : ZMod p)
    (hx : x ≠ 0) (hr : rInv ≠ 0) :
    montReduceF rInv x * montReduceF rInv (montInverseF rInv x) = 1 := by
  unfold montReduceF montInverseF
  have ex : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x (isUnit_of_ne_zero hx)
  have emr : rInv * rInv⁻¹ = 1 := ZMod.mul_inv_of_unit rInv (isUnit_of_ne_zero hr)
  have er : rInv⁻¹ * rInv = 1 := ZMod.inv_mul_of_unit rInv (isUnit_of_ne_zero hr)
  rw [show x * rInv * (x⁻¹ * rInv⁻¹ * rInv⁻¹ * rInv)
        = (x * x⁻¹) * (rInv * rInv⁻¹) * (rInv⁻¹ * rInv) by ring,
    ex, emr, er, one_mul, one_mul]

/-! ## 3. Type -/

/-- The Montgomery-inverse dialect's value-type alphabet: a Montgomery residue at
    modulus `p`, `⟦·⟧ = ZMod p` (the `ModArithDialect.fp` carrier). -/
inductive MontInverseTy where
  /-- A Montgomery residue mod `p`, `⟦·⟧ = ZMod p`. -/
  | fp (p : Nat)
  deriving DecidableEq

/-- Total denotation of `MontInverseTy`: the residue denotes exactly to the
    `ModArithDialect.fp` carrier `ZMod p`. -/
@[reducible] instance : TyDenote MontInverseTy where
  denote
    | .fp p => ZMod p

/-! ## 4. Op tag -/

/-- Operation tag for the Montgomery-inverse dialect — prime-ir's
    `mod_arith.mont_inverse`, carrying the Montgomery-radix inverse `rInv`. -/
inductive MontInverseOp where
  /-- `mod_arith.mont_inverse` over `fp p`: `x ↦ x⁻¹ · rInv · rInv`. -/
  | montInverse (p : Nat) (rInv : ZMod p)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The Montgomery-inverse dialect: `Op` is `MontInverseOp`, `Ty` is
    `MontInverseTy`. -/
@[reducible] def montInverseDialect : Dialect :=
  { Op := MontInverseOp, Ty := MontInverseTy }

/-! ## 6. Op signature (arg types + return type — unary `fp → fp`) -/

instance : DialectSignature montInverseDialect where
  sig op := match op with
    | .montInverse p _ => [.fp p]
  ret op := match op with
    | .montInverse p _ => .fp p

/-! ## 7. Op denotation (into the genuine Montgomery inverse) -/

instance montInverseDenote : DialectDenote montInverseDialect where
  denote op := match op with
    | .montInverse _ rInv => fun args => montInverseF rInv args.head

/-! ## 8. Per-op denotation / correctness facts -/

/-- `montInverse` denotes to `x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹`. -/
theorem montInverse_denote {p : Nat} (rInv x : ZMod p) :
    montInverseDenote.denote (.montInverse p rInv) (.cons x .nil)
      = x⁻¹ * rInv⁻¹ * rInv⁻¹ := rfl

/-- **Op-level Montgomery-inverse spec.** The op's Montgomery product with `x̃` is
    the unit `R = rInv⁻¹`. -/
theorem montInverse_denote_spec {p : Nat} [Fact (Nat.Prime p)] (rInv x : ZMod p)
    (hx : x ≠ 0) (hr : rInv ≠ 0) :
    montMulF rInv x (montInverseDenote.denote (.montInverse p rInv) (.cons x .nil))
      = rInv⁻¹ := by
  rw [montInverse_denote]
  exact montInverse_spec rInv x hx hr

/-! ## 9. Constant-time predicate (the dialect's CT instance)

The Montgomery inverse is a fixed Fermat / divstep schedule (public exponent /
step count, no data-dependent branch), so `ctSafe` is `true` for the op. -/

/-- Per-op CT predicate: the Montgomery-inverse op is constant-time. -/
def MontInverseOp.ctSafe : MontInverseOp → Bool
  | _ => true

@[simp] theorem MontInverseOp.ctSafe_all (op : MontInverseOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt montInverseDialect} {t : MontInverseTy}
    (e : Expr montInverseDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt montInverseDialect} {t : MontInverseTy}
    (e : Expr montInverseDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  Since the only op is CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt montInverseDialect} {t : MontInverseTy} :
    Com montInverseDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.** Every Montgomery-inverse program is constant-time. -/
theorem ctSafeCom_all {Γ : Ctxt montInverseDialect} {t : MontInverseTy}
    (c : Com montInverseDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

/-! ## 10. Smoke test

A one-op `Com montInverseDialect`: `let r = montInverse rInv x; ret r` over
`ZMod 7` with `rInv = 1` (Montgomery radix `R = 1`, i.e. the plain field-inverse
specialisation).  On `x = 3` (`3⁻¹ = 5` since `3·5 = 15 = 1 mod 7`) it returns
`5 · 1⁻¹ · 1⁻¹ = 5`. -/

/-- One-op smoke program: a `montInverse` (with `rInv = 1`) over `[fp 7]`. -/
def smokeProg : Com montInverseDialect [.fp 7] (.fp 7) :=
  .var (.mk (.montInverse 7 1) rfl (.cons .here .nil))
    (.ret .here)

/-- The smoke program denotes to `x⁻¹ · 1 · 1 = x⁻¹`; on `x = 3` that is
    `3⁻¹ = 5 (mod 7)`. -/
example : smokeProg.denote (.cons (3 : ZMod 7) .nil) = (5 : ZMod 7) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverse
