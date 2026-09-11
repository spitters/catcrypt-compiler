/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-!
# Field/EC comparison & zero-test ops — first-class `cmp`/`is_zero`

A minimal **correspondence** `VIR.Dialect` whose ops are the field/EC
*predicate* ops of fractalyze/prime-ir: equality (`cmp eq`) and the
identity/zero test (`is_zero`), each a `… → BoolLike` op.  It is the CatCrypt
counterpart of prime-ir's `field.cmp`, `mod_arith.cmp`, and
`elliptic_curve.is_zero` / `elliptic_curve.cmp`.

## Why this dialect exists (the gap it closes)

Per `PRIME_IR_OP_CORRESPONDENCE.md` (repo root, §1 & §4), CatCrypt already *had* the
comparison and identity-test functionality, but only at the **bit / sword
layer** and via the `none` carrier of the EC add law:

* `field.cmp` (§1, line 26) — "no dedicated field-cmp op (cmp done in
  `.bit`/sword layer)" — **PARTIAL**.
* `mod_arith.cmp` (§4, line 60) — "done at sword layer" — **PARTIAL**.
* `elliptic_curve.is_zero` (§4, line 114) — "identity check (option `none`
  carrier in add law)" — **PARTIAL**.
* `elliptic_curve.cmp` (§4, line 122) — "point-eq via coord compare" —
  **PARTIAL**.

The gap analysis classified all four **PARTIAL** — *functionality present, not
factored as a first-class field/EC `cmp`/`is_zero` op*.  This file **factors
those predicates as standalone ops over the existing `FieldDialect`/
`EllipticCurveDialect` value types** (`ZMod p`, `ECPoint p`), each denoting into
a `Bool` (prime-ir's `BoolLike`), matching prime-ir's `cmp`/`is_zero` ops
one-for-one — WITHOUT modifying either dialect's `Op` set (additive only).

## The ops (`CmpOp`)

* `fieldEq p`     — `field.cmp eq` over `fp p`: `(a b : ZMod p) ↦ decide (a = b)`.
* `fieldIsZero p` — `field.cmp eq 0` over `fp p`: `(a : ZMod p) ↦ decide (a = 0)`.
* `ecIsZero p`    — `elliptic_curve.is_zero` over `point p`: `P ↦ P.isNone`
                    (the identity is `ECPoint.zero = none`; see the EC add law's
                    `none` carrier, `EllipticCurveDialect.ECParams.add`).
* `ecEq p`        — `elliptic_curve.cmp eq` over `point p`: `(P Q) ↦ decide (P = Q)`
                    (point-eq, decidable on the `Option (ZMod p × ZMod p)` carrier).

## Type (`CmpTy`)

`CmpTy` re-uses the existing field/EC value types as op *inputs* and adds a
`bool` result type (prime-ir's `BoolLike`), `⟦bool⟧ = Bool`:

* `fp p`     — the prime field (`⟦·⟧ = ZMod p`), the `FieldDialect` carrier.
* `point p`  — the abstract curve group (`⟦·⟧ = ECPoint p`), the `EllipticCurveDialect`
              carrier.
* `bool`     — the `BoolLike` result, `⟦·⟧ = Bool`.

The field/point input denotations are *exactly* the `FieldDialect`/
`EllipticCurveDialect` denotations, so these ops are predicates over the same
values — the once-for-all tie to those dialects, with no new carrier for the
operands.

## The leaf predicates (`fieldEq`, `fieldIsZero`, `ecIsZero`, `ecEq`)

Each leaf is a total decidable predicate returning `Bool`; the agreement lemmas
(`fieldEq_iff`, `fieldIsZero_iff`, `ecIsZero_iff`, `ecEq_iff`) tie the `Bool` to
its `Prop`.  `ecIsZero`'s predicate is `P = ECPoint.zero` (`= none`), matching
how the EC dialect represents the identity.

## Honest classification (read `VIR/DIALECTS.md`)

This is a **HIGH-tier, prime-ir-corresponding / agreement** dialect, NOT an
emit-wired one.  Like `mlirArithDialect`, `mlirPolynomialDialect`, and
`TensorExtDialect` in DIALECTS.md's "correspondence-only" table, it has **no
lowering out** (no `→ Com jasminDialect`, no backend edge).  It substantiates
the "prime-ir `field.cmp` / `mod_arith.cmp` / `elliptic_curve.is_zero` /
`elliptic_curve.cmp` aligned" claim by giving those predicates a first-class op
with a verified `Bool ↔ Prop` denotation.  It does **not** add a lowering or
emit path — the comparisons reaching bytes still flow through the bit/sword
layer.  Do not overclaim an emit this file does not build.

## Constant-time caveat — these are EQUALITY TESTS (read carefully)

Unlike `FieldDialect`/`EllipticCurveDialect`'s arithmetic ops (data-oblivious,
CT by construction), an **equality / zero test over `ZMod p` or `ECPoint p` is
data-dependent**: its result branches on the secret operand value.  Prime-ir's
`cmp` on secret data is a known constant-time hazard — a naive `decide (a = b)`
lowers to a data-dependent branch and is **NOT** generally CT.

We therefore record `ctSafe = false` for the comparison ops **by default** and
expose a per-op `publicData : Bool` flag: a `cmp`/`is_zero` is admitted as CT
**only** when its operands are public (e.g. comparing against a public constant,
a public tag, or a value already declassified) AND realised by a
data-independent / constant-time-compare schedule.  A secret-operand equality
test (`publicData = false`) is **flagged**, never silently accepted — exactly
the EC dialect's `psmul`-style explicit-obligation discipline, applied to the
comparison hazard.  This is the honest CT story: *these ops are not CT in
general; only their public-data uses are.*
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldEcCmpOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-! ## 1. The leaf predicates (the denotation targets)

Each is a total decidable predicate into `Bool` (prime-ir's `BoolLike`).  The
field/point operand types are exactly the `FieldDialect`/`EllipticCurveDialect`
carriers (`ZMod p`, `ECPoint p`), so these are predicates over the same values
the arithmetic dialects manipulate. -/

/-- `field.cmp eq` leaf: field-element equality `a = b` over `ZMod p`, as a
    `Bool`.  Decidable since `ZMod p` has `DecidableEq`. -/
@[reducible] def fieldEq (p : Nat) (a b : ZMod p) : Bool := decide (a = b)

/-- `field.cmp eq 0` leaf: the field zero-test `a = 0` over `ZMod p`, as a
    `Bool`.  This is the `is_zero` specialisation of `fieldEq` against the field
    zero. -/
@[reducible] def fieldIsZero (p : Nat) (a : ZMod p) : Bool := decide (a = 0)

/-- `elliptic_curve.is_zero` leaf: the curve identity test `P = O`, as a `Bool`.
    The identity is `ECPoint.zero = none` (the `none` carrier of the EC add law,
    `EllipticCurveDialect.ECParams.add`), so this is `P.isNone`. -/
@[reducible] def ecIsZero (p : Nat) (P : ECPoint p) : Bool := P.isNone

/-- `elliptic_curve.cmp eq` leaf: point equality `P = Q` over `ECPoint p`, as a
    `Bool`.  Decidable since `ECPoint p = Option (ZMod p × ZMod p)` has
    `DecidableEq`. -/
@[reducible] def ecEq (p : Nat) (P Q : ECPoint p) : Bool := decide (P = Q)

/-! ## 2. Agreement lemmas (`Bool ↔ Prop`)

The `Bool` predicate agrees with its `Prop` meaning — the once-per-op
correctness tie.  `ecIsZero_iff` is stated against `ECPoint.zero` (= `none`),
the EC dialect's identity. -/

/-- **Agreement.** `fieldEq` is `true` iff the field elements are equal. -/
theorem fieldEq_iff {p : Nat} (a b : ZMod p) : fieldEq p a b = true ↔ a = b := by
  simp [fieldEq]

/-- **Agreement.** `fieldIsZero` is `true` iff the field element is zero. -/
theorem fieldIsZero_iff {p : Nat} (a : ZMod p) : fieldIsZero p a = true ↔ a = 0 := by
  simp [fieldIsZero]

/-- **Agreement.** `ecIsZero` is `true` iff the point is the curve identity
    `ECPoint.zero` (= `none`, the EC add law's identity carrier). -/
theorem ecIsZero_iff {p : Nat} (P : ECPoint p) :
    ecIsZero p P = true ↔ P = ECPoint.zero := by
  cases P with
  | none => simp [ecIsZero, ECPoint.zero]
  | some q => simp [ecIsZero, ECPoint.zero]

/-- **Agreement.** `ecEq` is `true` iff the points are equal. -/
theorem ecEq_iff {p : Nat} (P Q : ECPoint p) : ecEq p P Q = true ↔ P = Q := by
  simp [ecEq]

/-- `fieldIsZero` is the `fieldEq`-against-zero specialisation. -/
theorem fieldIsZero_eq_fieldEq_zero {p : Nat} (a : ZMod p) :
    fieldIsZero p a = fieldEq p a 0 := rfl

/-! ## 3. Type (`CmpTy`)

The operand types re-use the existing field/EC carriers; the result is the new
`bool` (`BoolLike`). -/

/-- The comparison dialect's value-type alphabet: the prime-field operand
    (`FieldDialect`'s `fp`), the curve-group operand (`EllipticCurveDialect`'s
    `point`), and the `BoolLike` result. -/
inductive CmpTy where
  /-- The prime field `F_p`, `⟦·⟧ = ZMod p` (the `FieldDialect` carrier). -/
  | fp (p : Nat)
  /-- The abstract curve group, `⟦·⟧ = ECPoint p` (the `EllipticCurveDialect`
      carrier). -/
  | point (p : Nat)
  /-- The `BoolLike` result, `⟦·⟧ = Bool`. -/
  | bool
  deriving DecidableEq

/-- Total denotation of `CmpTy`: the field/point operand types denote exactly to
    the `FieldDialect`/`EllipticCurveDialect` carriers, and `bool` to `Bool`. -/
@[reducible] instance : TyDenote CmpTy where
  denote
    | .fp p => ZMod p
    | .point p => ECPoint p
    | .bool => Bool

/-! ## 4. Op tags (`CmpOp`)

The `cmp`/`is_zero` ops.  Each carries a `publicData : Bool` flag recording
whether its operands are public (the CT obligation — see the module CT caveat).
The flag does NOT change the denotation; it only governs `ctSafe`. -/

/-- Operation tags for the comparison dialect — prime-ir's field/EC predicate
    ops.  The `publicData` flag records whether the operands are public; it
    drives `ctSafe` (an equality test is CT only on public data). -/
inductive CmpOp where
  /-- `field.cmp eq` over `fp p`: `decide (a = b)`. -/
  | fieldEq (p : Nat) (publicData : Bool)
  /-- `field.cmp eq 0` over `fp p`: `decide (a = 0)`. -/
  | fieldIsZero (p : Nat) (publicData : Bool)
  /-- `elliptic_curve.is_zero` over `point p`: `P.isNone` (identity = `none`). -/
  | ecIsZero (p : Nat) (publicData : Bool)
  /-- `elliptic_curve.cmp eq` over `point p`: `decide (P = Q)`. -/
  | ecEq (p : Nat) (publicData : Bool)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The comparison dialect: `Op` is `CmpOp`, `Ty` is `CmpTy`. -/
@[reducible] def cmpDialect : Dialect :=
  { Op := CmpOp, Ty := CmpTy }

/-! ## 6. Op signatures (arg types + return type — every op returns `bool`) -/

instance : DialectSignature cmpDialect where
  sig op := match op with
    | .fieldEq p _ => [.fp p, .fp p]
    | .fieldIsZero p _ => [.fp p]
    | .ecIsZero p _ => [.point p]
    | .ecEq p _ => [.point p, .point p]
  ret op := match op with
    | .fieldEq _ _ => .bool
    | .fieldIsZero _ _ => .bool
    | .ecIsZero _ _ => .bool
    | .ecEq _ _ => .bool

/-! ## 7. Op denotation (into the `Bool` predicate) -/

instance cmpDenote : DialectDenote cmpDialect where
  denote op := match op with
    | .fieldEq p _ => fun args => fieldEq p args.head args.tail.head
    | .fieldIsZero p _ => fun args => fieldIsZero p args.head
    | .ecIsZero p _ => fun args => ecIsZero p args.head
    | .ecEq p _ => fun args => ecEq p args.head args.tail.head

/-! ## 8. Per-op denotation / agreement facts (the once-per-op ties)

These hold **definitionally** because the op denotations are the leaf
predicates; combined with §2's `…_iff`, the op's `Bool` result is tied to its
`Prop` meaning. -/

/-- `fieldEq` denotes to `decide (a = b)`. -/
theorem fieldEq_denote {p : Nat} (pub : Bool) (a b : ZMod p) :
    cmpDenote.denote (.fieldEq p pub) (.cons a (.cons b .nil)) = decide (a = b) := rfl

/-- The `fieldEq` op result is `true` iff the field elements are equal. -/
theorem fieldEq_denote_iff {p : Nat} (pub : Bool) (a b : ZMod p) :
    cmpDenote.denote (.fieldEq p pub) (.cons a (.cons b .nil)) = true ↔ a = b := by
  rw [fieldEq_denote, decide_eq_true_eq]

/-- `fieldIsZero` denotes to `decide (a = 0)`. -/
theorem fieldIsZero_denote {p : Nat} (pub : Bool) (a : ZMod p) :
    cmpDenote.denote (.fieldIsZero p pub) (.cons a .nil) = decide (a = 0) := rfl

/-- The `fieldIsZero` op result is `true` iff the field element is zero. -/
theorem fieldIsZero_denote_iff {p : Nat} (pub : Bool) (a : ZMod p) :
    cmpDenote.denote (.fieldIsZero p pub) (.cons a .nil) = true ↔ a = 0 := by
  rw [fieldIsZero_denote, decide_eq_true_eq]

/-- `ecIsZero` denotes to `P.isNone` (the identity test). -/
theorem ecIsZero_denote {p : Nat} (pub : Bool) (P : ECPoint p) :
    cmpDenote.denote (.ecIsZero p pub) (.cons P .nil) = P.isNone := rfl

/-- The `ecIsZero` op result is `true` iff the point is the curve identity
    `ECPoint.zero` (= `none`). -/
theorem ecIsZero_denote_iff {p : Nat} (pub : Bool) (P : ECPoint p) :
    cmpDenote.denote (.ecIsZero p pub) (.cons P .nil) = true ↔ P = ECPoint.zero := by
  rw [ecIsZero_denote]
  cases P with
  | none => simp [ECPoint.zero]
  | some q => simp [ECPoint.zero]

/-- `ecEq` denotes to `decide (P = Q)`. -/
theorem ecEq_denote {p : Nat} (pub : Bool) (P Q : ECPoint p) :
    cmpDenote.denote (.ecEq p pub) (.cons P (.cons Q .nil)) = decide (P = Q) := rfl

/-- The `ecEq` op result is `true` iff the points are equal. -/
theorem ecEq_denote_iff {p : Nat} (pub : Bool) (P Q : ECPoint p) :
    cmpDenote.denote (.ecEq p pub) (.cons P (.cons Q .nil)) = true ↔ P = Q := by
  rw [ecEq_denote, decide_eq_true_eq]

/-! ## 9. Constant-time predicate — the EQUALITY-TEST hazard (read §"CT caveat")

This is the honest departure from `FieldDialect`/`EllipticCurveDialect`: an
equality / zero test is **data-dependent**, so it is **NOT** CT by construction.
`ctSafe` is `true` **only** when the op's `publicData` flag is set (operands
public, realised by a data-independent compare); a secret-operand comparison
(`publicData = false`) is **flagged**, exactly the EC dialect's `psmul`-style
explicit obligation applied to the comparison hazard. -/

/-- Per-op CT predicate: a comparison/zero-test is CT **iff** its operands are
    public (`publicData = true`).  A secret-operand equality test is NOT CT and
    is flagged (`false`). -/
def CmpOp.ctSafe : CmpOp → Bool
  | .fieldEq _ pub => pub
  | .fieldIsZero _ pub => pub
  | .ecIsZero _ pub => pub
  | .ecEq _ pub => pub

/-- A public-data `fieldEq` is admitted as CT — the obligation a public-constant
    comparison discharges. -/
@[simp] theorem CmpOp.ctSafe_fieldEq_public {p : Nat} :
    (CmpOp.fieldEq p true).ctSafe = true := rfl

/-- **The hazard, made explicit.** A secret-operand `fieldEq` is NOT CT: the
    equality test branches on the secret value, so it is flagged `false`, never
    silently admitted. -/
@[simp] theorem CmpOp.ctSafe_fieldEq_secret {p : Nat} :
    (CmpOp.fieldEq p false).ctSafe = false := rfl

/-- A public-data `ecIsZero` is admitted as CT (e.g. an identity check on an
    already-public point). -/
@[simp] theorem CmpOp.ctSafe_ecIsZero_public {p : Nat} :
    (CmpOp.ecIsZero p true).ctSafe = true := rfl

/-- **The hazard, made explicit.** A secret-operand `ecIsZero` is NOT CT. -/
@[simp] theorem CmpOp.ctSafe_ecIsZero_secret {p : Nat} :
    (CmpOp.ecIsZero p false).ctSafe = false := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt cmpDialect} {t : CmpTy}
    (e : Expr cmpDialect Γ t) : Bool :=
  e.op.ctSafe

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound comparison
    is public-data (`publicData = true`).  A program with any secret-operand
    comparison is flagged, NOT admitted. -/
def ctSafeCom {Γ : Ctxt cmpDialect} {t : CmpTy} :
    Com cmpDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- A comparison program built **only** of public-data ops is CT-safe.  The
    secret-operand ops carry `publicData = false` and are flagged by
    `ctSafeCom`; this is the explicit comparison-hazard obligation. -/
theorem ctSafeCom_public {Γ : Ctxt cmpDialect} {t : CmpTy}
    (c : Com cmpDialect Γ t)
    (h : ∀ {Γ' : Ctxt cmpDialect} {t' : CmpTy} (e : Expr cmpDialect Γ' t'),
          e.op.ctSafe = true) :
    ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp only [ctSafeCom, ctSafeExpr, h e, ih, Bool.and_self]

/-- Propositional form, decidable. -/
def ctSafePropCom {Γ : Ctxt cmpDialect} {t : CmpTy}
    (c : Com cmpDialect Γ t) : Prop :=
  ctSafeCom c = true

instance {Γ : Ctxt cmpDialect} {t : CmpTy}
    (c : Com cmpDialect Γ t) : Decidable (ctSafePropCom c) := by
  unfold ctSafePropCom; infer_instance

/-! ## 10. Smoke test

A one-op `Com cmpDialect`: `let r = fieldIsZero a; ret r` over `ZMod 7`, public
data.  On `a = 0` it returns `true`; the op denotes to the zero-test. -/

/-- One-op smoke program: a public-data `fieldIsZero` over `[fp 7]`. -/
def smokeProg : Com cmpDialect [.fp 7] .bool :=
  .var (.mk (.fieldIsZero 7 true) rfl (.cons .here .nil))
    (.ret .here)

/-- The smoke program denotes to the zero-test; on `a = 0` it is `true`. -/
example : smokeProg.denote (.cons (0 : ZMod 7) .nil) = true := by
  rfl

/-- And on `a = 3 ≠ 0` it is `false`. -/
example : smokeProg.denote (.cons (3 : ZMod 7) .nil) = false := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.FieldEcCmpOps
