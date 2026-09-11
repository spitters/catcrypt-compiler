/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# Field derived ops — first-class `double` / `square` / `powui`

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

Upstream: prime-ir `field.double` / `field.square` / `field.powui` (+
`mod_arith.double` / `mod_arith.square`).

A minimal **correspondence** `VIR.Dialect` whose ops are the prime-field
*derived-arithmetic* ops of fractalyze/prime-ir: doubling (`field.double`),
squaring (`field.square`), and fixed-exponent power (`field.powui`).  It is the
CatCrypt counterpart of prime-ir's `field.double` / `field.square` /
`field.powui` (and equally `mod_arith.double` / `mod_arith.square`, which are
the same maps one ring layer down).

## Why this dialect exists (the gap it closes)

Per `PRIME_IR_OP_CORRESPONDENCE.md` (repo root, §1 & §2), CatCrypt already *computes*
these derived ops — but only by **deriving them from the primitive ops**, never
as standalone ops:

* `field.double` (§1, line 30) — "derived (`fAdd a a`); no dedicated `fDouble`
  op" — **PARTIAL**.
* `field.square` (§1, line 31) — "derived (`fMul a a`); no dedicated `fSquare`
  op" — **PARTIAL**.
* `field.powui` (§1, line 36) — "no dedicated pow op (Fermat chain is a
  fixed-exponent unrolled mul/sqr schedule, `pow249Spec`)" — **PARTIAL**.
* `mod_arith.double` (§2, line 65) — "derived `modAdd a a`" — **PARTIAL**.
* `mod_arith.square` (§2, line 62) — "derived `modMul a a`" — **PARTIAL**.

The gap analysis classified all five **PARTIAL** — *functionality present, not
factored as a first-class derived op*.  This file **factors `double`, `square`,
and `powui` as standalone ops over the existing `FieldDialect` value type**
(`FieldTy.fp p`, carrier `ZMod p`), each with a concrete denotation tied to the
primitive `+` / `*` / `^` — WITHOUT modifying `FieldDialect`'s `Op` set
(additive only).  Since the field prime-field carrier is `ZMod p` and the
ModArith leaves *are* `ZMod p`'s native ops (`fAddF = modAddF`, `fMulF =
modMulF`; see `FieldDialect.lean §3`), the same ops close both the
`field.double/square/powui` and the `mod_arith.double/square` PARTIALs at once.

## The ops (`DerivedOp`), parametric in the prime `p`

* `fieldDouble p` — `a ↦ a + a` (= `2 • a`).  (`field.double` / `mod_arith.double`)
* `fieldSquare p` — `a ↦ a * a` (= `a ^ 2`).  (`field.square` / `mod_arith.square`)
* `fieldPow p k`  — `a ↦ a ^ k`, the **fixed-exponent** power.  (`field.powui`)
  The exponent `k : Nat` is a *static op parameter* (prime-ir's `powui` takes a
  `ui` constant), so the realising schedule is a fixed, data-independent
  mul/square chain (cf. the `pow249Spec` Fermat chain) — not a data-dependent
  loop over a secret exponent.

## Type (`DerivedTy`)

`DerivedTy` re-uses the existing prime-field carrier:

* `fp p` — the prime field `F_p`, `⟦·⟧ = ZMod p` (the `FieldDialect` carrier).

The denotation is *exactly* the `FieldDialect.fp` denotation, so these ops are
maps over the same values the arithmetic dialect manipulates — the once-for-all
tie to that dialect, with no new carrier.

## The leaf functions (`fieldDoubleF`, `fieldSquareF`, `fieldPowF`)

Each leaf is a total function `ZMod p → ZMod p` built from the primitive
`ZMod p` operations; the agreement lemmas tie each to its primitive form:

* `fieldDoubleF p a = a + a`, with `fieldDouble_eq_add` and the scalar form
  `fieldDouble_eq_two_mul : … = 2 * a`.
* `fieldSquareF p a = a * a`, with `fieldSquare_eq_mul` and `fieldSquare_eq_pow
  : … = a ^ 2`.
* `fieldPowF p k a = a ^ k`, with the Horner/repeated-square spec a power op
  needs: `fieldPow_zero`, `fieldPow_succ : fieldPow p (k+1) a = fieldPow p k a *
  a`, and `fieldPow_eq_npow : fieldPow p k a = a ^ k`.

## Pure-only + constant-time

Unlike the equality-test ops of `cmpDialect` (data-dependent, only CT on public
data), `double` / `square` / `powui` are **data-oblivious** arithmetic — a fixed
add/multiply/(fixed-exponent square-and-multiply) schedule, never branching on a
secret operand value.  So they are CT by construction (`ctSafe = true` for every
op), exactly like `FieldDialect`/`ModArithDialect`'s primitive arithmetic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-! ## 1. The leaf functions (the denotation targets)

Each is a total function `ZMod p → ZMod p` built from the primitive `ZMod p`
operations.  The operand type is exactly the `FieldDialect.fp` carrier, so these
are maps over the same values the arithmetic dialect manipulates. -/

/-- `field.double` / `mod_arith.double` leaf: field doubling `a ↦ a + a` over
    `ZMod p`. -/
@[reducible] def fieldDoubleF (p : Nat) (a : ZMod p) : ZMod p := a + a

/-- `field.square` / `mod_arith.square` leaf: field squaring `a ↦ a * a` over
    `ZMod p`. -/
@[reducible] def fieldSquareF (p : Nat) (a : ZMod p) : ZMod p := a * a

/-- `field.powui` leaf: the fixed-exponent power `a ↦ a ^ k` over `ZMod p`.
    `k : Nat` is a static op parameter (prime-ir's `powui` constant), so this is
    a fixed mul/square schedule, not a secret-exponent loop. -/
@[reducible] def fieldPowF (p : Nat) (k : Nat) (a : ZMod p) : ZMod p := a ^ k

/-! ## 2. Agreement lemmas (derived op = primitive form)

Each derived leaf agrees with the primitive operation it factors — the
once-per-op correctness tie.  These are the lemmas the gap analysis asks for:
double as `+` / `2 *`, square as `*` / `^ 2`, and the power's Horner recursion
(`fieldPow_succ`) plus the closed form (`fieldPow_eq_npow`). -/

/-- **Agreement.** `fieldDouble` is field addition with itself: `a + a`. -/
theorem fieldDouble_eq_add {p : Nat} (a : ZMod p) :
    fieldDoubleF p a = a + a := rfl

/-- **Agreement.** `fieldDouble` is the scalar double `2 * a`. -/
theorem fieldDouble_eq_two_mul {p : Nat} (a : ZMod p) :
    fieldDoubleF p a = 2 * a := by
  rw [fieldDoubleF, two_mul]

/-- **Agreement.** `fieldSquare` is field multiplication with itself: `a * a`. -/
theorem fieldSquare_eq_mul {p : Nat} (a : ZMod p) :
    fieldSquareF p a = a * a := rfl

/-- **Agreement.** `fieldSquare` is the square `a ^ 2`. -/
theorem fieldSquare_eq_pow {p : Nat} (a : ZMod p) :
    fieldSquareF p a = a ^ 2 := by
  rw [fieldSquareF, sq]

/-- **Power base case.** `fieldPow p 0 a = 1`. -/
theorem fieldPow_zero {p : Nat} (a : ZMod p) :
    fieldPowF p 0 a = 1 := pow_zero a

/-- **Power Horner step.** `fieldPow p (k+1) a = fieldPow p k a * a` — the
    repeated-square/Horner recursion a fixed-exponent power op realises. -/
theorem fieldPow_succ {p : Nat} (k : Nat) (a : ZMod p) :
    fieldPowF p (k + 1) a = fieldPowF p k a * a := pow_succ a k

/-- **Agreement.** `fieldPow p k a` is the field power `a ^ k`. -/
theorem fieldPow_eq_npow {p : Nat} (k : Nat) (a : ZMod p) :
    fieldPowF p k a = a ^ k := rfl

/-- `fieldSquare` is `fieldPow … 2` — squaring is the exponent-`2`
    specialisation of `powui`. -/
theorem fieldSquare_eq_fieldPow_two {p : Nat} (a : ZMod p) :
    fieldSquareF p a = fieldPowF p 2 a := by
  rw [fieldSquare_eq_pow, fieldPow_eq_npow]

/-! ## 3. Type (`DerivedTy`)

The operand type re-uses the existing prime-field carrier. -/

/-- The derived-ops dialect's value-type alphabet: the prime-field operand
    (`FieldDialect`'s `fp`). -/
inductive DerivedTy where
  /-- The prime field `F_p`, `⟦·⟧ = ZMod p` (the `FieldDialect` carrier). -/
  | fp (p : Nat)
  deriving DecidableEq

/-- Total denotation of `DerivedTy`: the field operand denotes exactly to the
    `FieldDialect` carrier `ZMod p`. -/
@[reducible] instance : TyDenote DerivedTy where
  denote
    | .fp p => ZMod p

/-! ## 4. Op tags (`DerivedOp`)

The `double` / `square` / `powui` ops.  `fieldPow` carries its static exponent
`k : Nat`, mirroring prime-ir's `powui` constant attribute. -/

/-- Operation tags for the derived-ops dialect — prime-ir's field/mod-arith
    derived-arithmetic ops.  `fieldPow` carries its fixed exponent `k`. -/
inductive DerivedOp where
  /-- `field.double` / `mod_arith.double` over `fp p`: `a ↦ a + a`. -/
  | fieldDouble (p : Nat)
  /-- `field.square` / `mod_arith.square` over `fp p`: `a ↦ a * a`. -/
  | fieldSquare (p : Nat)
  /-- `field.powui` over `fp p`: `a ↦ a ^ k`, fixed exponent `k`. -/
  | fieldPow (p : Nat) (k : Nat)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The derived-ops dialect: `Op` is `DerivedOp`, `Ty` is `DerivedTy`. -/
@[reducible] def derivedDialect : Dialect :=
  { Op := DerivedOp, Ty := DerivedTy }

/-! ## 6. Op signatures (arg types + return type — each op is unary `fp → fp`) -/

instance : DialectSignature derivedDialect where
  sig op := match op with
    | .fieldDouble p => [.fp p]
    | .fieldSquare p => [.fp p]
    | .fieldPow p _ => [.fp p]
  ret op := match op with
    | .fieldDouble p => .fp p
    | .fieldSquare p => .fp p
    | .fieldPow p _ => .fp p

/-! ## 7. Op denotation (into the primitive arithmetic) -/

instance derivedDenote : DialectDenote derivedDialect where
  denote op := match op with
    | .fieldDouble p => fun args => fieldDoubleF p args.head
    | .fieldSquare p => fun args => fieldSquareF p args.head
    | .fieldPow p k => fun args => fieldPowF p k args.head

/-! ## 8. Per-op denotation / agreement facts (the once-per-op ties)

These hold **definitionally** because the op denotations are the leaf functions;
combined with §2's agreement lemmas, each op's result is tied to its primitive
`+` / `*` / `^` form. -/

/-- `fieldDouble` denotes to `a + a`. -/
theorem fieldDouble_denote {p : Nat} (a : ZMod p) :
    derivedDenote.denote (.fieldDouble p) (.cons a .nil) = a + a := rfl

/-- The `fieldDouble` op result is the scalar double `2 * a`. -/
theorem fieldDouble_denote_two_mul {p : Nat} (a : ZMod p) :
    derivedDenote.denote (.fieldDouble p) (.cons a .nil) = 2 * a := by
  rw [fieldDouble_denote, two_mul]

/-- `fieldSquare` denotes to `a * a`. -/
theorem fieldSquare_denote {p : Nat} (a : ZMod p) :
    derivedDenote.denote (.fieldSquare p) (.cons a .nil) = a * a := rfl

/-- The `fieldSquare` op result is `a ^ 2`. -/
theorem fieldSquare_denote_pow {p : Nat} (a : ZMod p) :
    derivedDenote.denote (.fieldSquare p) (.cons a .nil) = a ^ 2 := by
  rw [fieldSquare_denote, sq]

/-- `fieldPow` denotes to `a ^ k`. -/
theorem fieldPow_denote {p : Nat} (k : Nat) (a : ZMod p) :
    derivedDenote.denote (.fieldPow p k) (.cons a .nil) = a ^ k := rfl

/-- The `fieldPow` op satisfies the Horner step at the denotation level:
    `⟦fieldPow (k+1)⟧ a = (a ^ k) * a`.  RHS stated over the `ZMod p` leaf so the
    `*` elaborates against the field carrier. -/
theorem fieldPow_denote_succ {p : Nat} (k : Nat) (a : ZMod p) :
    derivedDenote.denote (.fieldPow p (k + 1)) (.cons a .nil)
      = (a ^ k) * a := by
  rw [fieldPow_denote, pow_succ]

/-- The `fieldPow` op at exponent `0` denotes to the field `1`. -/
theorem fieldPow_denote_zero {p : Nat} (a : ZMod p) :
    derivedDenote.denote (.fieldPow p 0) (.cons a .nil) = (1 : ZMod p) := by
  rw [fieldPow_denote, pow_zero]

/-- The `fieldSquare` op is the `fieldPow … 2` op (denotationally): squaring is
    the exponent-`2` `powui`. -/
theorem fieldSquare_denote_eq_fieldPow_two {p : Nat} (a : ZMod p) :
    derivedDenote.denote (.fieldSquare p) (.cons a .nil)
      = derivedDenote.denote (.fieldPow p 2) (.cons a .nil) := by
  rw [fieldSquare_denote_pow, fieldPow_denote]

/-! ## 9. Constant-time predicate (the dialect's CT instance)

Unlike the equality-test ops of `cmpDialect` (data-dependent), every derived op
is data-oblivious: doubling/squaring are a single add/multiply, and the
fixed-exponent power is a static mul/square schedule (the exponent `k` is an op
parameter, not a secret operand).  No `ite` on data, no data-dependent index, so
`ctSafe` is `true` for every op — exactly the `FieldOp.ctSafe_all` story. -/

/-- Per-op CT predicate: every derived-arithmetic op is constant-time. -/
def DerivedOp.ctSafe : DerivedOp → Bool
  | _ => true

@[simp] theorem DerivedOp.ctSafe_all (op : DerivedOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (e : Expr derivedDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (e : Expr derivedDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  Since every op is CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt derivedDialect} {t : DerivedTy} :
    Com derivedDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.**  Every derived-ops program is constant-time: the
    derived arithmetic introduces no data-dependent control flow or memory
    index. -/
theorem ctSafeCom_all {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (c : Com derivedDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

/-- Propositional form, decidable. -/
def ctSafePropCom {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (c : Com derivedDialect Γ t) : Prop :=
  ctSafeCom c = true

instance {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (c : Com derivedDialect Γ t) : Decidable (ctSafePropCom c) := by
  unfold ctSafePropCom; infer_instance

/-! ## 10. Smoke test

A one-op `Com derivedDialect`: `let r = fieldSquare a; ret r` over `ZMod 7`.
On `a = 3` it returns `3 * 3 = 9 = 2 (mod 7)`. -/

/-- One-op smoke program: a `fieldSquare` over `[fp 7]`. -/
def smokeProg : Com derivedDialect [.fp 7] (.fp 7) :=
  .var (.mk (.fieldSquare 7) rfl (.cons .here .nil))
    (.ret .here)

/-- The smoke program denotes to the field square; on `a = 3` that is
    `9 = 2 (mod 7)`. -/
example : smokeProg.denote (.cons (3 : ZMod 7) .nil) = (2 : ZMod 7) := by
  rfl

/-- A `fieldPow` smoke: `let r = fieldPow 3 a; ret r` over `ZMod 7`; on `a = 2`
    that is `2 ^ 3 = 8 = 1 (mod 7)`. -/
def smokePowProg : Com derivedDialect [.fp 7] (.fp 7) :=
  .var (.mk (.fieldPow 7 3) rfl (.cons .here .nil))
    (.ret .here)

/-- The power smoke program: `2 ^ 3 = 1 (mod 7)`. -/
example : smokePowProg.denote (.cons (2 : ZMod 7) .nil) = (1 : ZMod 7) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps
