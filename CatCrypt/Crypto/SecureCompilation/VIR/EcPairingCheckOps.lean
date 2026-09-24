/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Fp12Gt

/-!
# Elliptic-curve `pairing_check` — first-class multi-pairing GT-equality op

A `VIR.Dialect` whose ops are the pairing-target equality tests of
fractalyze/prime-ir's `elliptic_curve.pairing_check`: the single-pairing GT test
`e == 1` and the two-pairing product test `e₁ · e₂ == 1`.  It is the CatCrypt
counterpart of prime-ir's `elliptic_curve.pairing_check`
(`EllipticCurveOps.td`).

## What this op is, and what it composes with

A pairing check decides `∏ᵢ e(Pᵢ, Qᵢ) == 1` in `GT = Fp12` (the verification
equation of BLS signatures, Groth16, KZG, …).  CatCrypt has the **numeric pairing
stages already assembled and proven** at the tower level:

* the Miller loop — `BLS12381PairingTowerEmit.millerFold` /
  `RelationalFront.millerLoop` / the EC-dialect-routed
  `Bls12381MillerFieldEmit.committedMillerLoop`
  (`committedMillerLoop_eq_millerLoop`);
* final exponentiation — `BLS12381PairingTowerEmit.expFold` (hard part) +
  `Bls12381FinalExpFieldEmit.finalExpEasyEmitProg` (easy part);
* the composed pairing `e = finalExp ∘ miller` —
  `BLS12381PairingTowerEmit.pairingEmit` (`pairingEmit_realizes`).

This dialect supplies the **final GT-equality
decision**: `FieldDialect.Fp12Val` carries no `One`/`DecidableEq` and no
`Bool`-returning equality op, so `∏ e == 1` cannot be stated in `fieldDialect`
alone.  `Fp12Gt.lean` adds the GT identity, decidable equality, and `gtIsOneF`;
this file folds the per-pairing GT values with `Fp12Val.mul ξ₀` and tests the
product against `1`.  The GT inputs are the per-pairing `pairingEmit` outputs; the
**GT product lowers onto the proven `FieldOp.ext12Mul` chain**
(`EcPairingCheckLowering.lean`, `DialectLoweringChain.extChainDenote_fp12`).

## The ops (`PairingCheckOp`)

* `gtIsOne p publicData` — `(e : gt p) ↦ (e == 1)`.  Single-pairing check.
* `pairingCheck2 p ξ₀ publicData` — `(e₁ e₂ : gt p) ↦ (e₁ ·_{ξ₀} e₂ == 1)`.
  Two-pairing product check (the BLS-verify / Groth16 shape).

## Type (`PairingCheckTy`)

* `gt p`  — a GT (= `Fp12`) element, `⟦·⟧ = Fp12Val p` (the `FieldDialect`
  pairing-target carrier).
* `bool`  — the `BoolLike` result, `⟦·⟧ = Bool`.

## Constant-time caveat — the GT equality is a comparison (read carefully)

Like `FieldEcCmpOps`'s `cmp`/`is_zero`, a GT equality test is **data-dependent**:
it branches on the (secret-derived) pairing value.  Each op carries a
`publicData : Bool` flag — `ctSafe = publicData`.  A pairing check on a public
verification value (the usual case: signature verification compares public
group elements) is admitted CT; a secret-operand GT comparison is **flagged**,
never silently accepted.

## Classification (see `VIR/DIALECTS.md`)

The GT **product** uses the `ext12Mul` lowering chain (→ `Fp6` schedule
→ `ModArith` → bytes), tied in `EcPairingCheckLowering.lean`.  The **equality
tail** (`gtIsOne`) is a `cmp`-style predicate (bit/sword layer), not a new field
emit.  The Miller-loop + final-exp that *produce* the GT inputs are the proven
tower-level `pairingEmit`.  This op factors the multi-pairing equality decision
and lowers its product onto proven field ops; it does **not** claim a proof that
the schedule equals the mathematical Tate/Weil pairing (no Mathlib `WeilPairing`
to tie to).  Do not overclaim.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Fp12Gt

variable {p : Nat}

/-! ## 1. The leaf functions (the multi-pairing GT product + the checks)

The product folds the per-pairing GT values with `Fp12Val.mul ξ₀` from the GT
identity `1`; the checks test the product (or a single value / a two-value
product) against `1`. -/

/-- The multi-pairing GT product `∏ᵢ eᵢ` (the verification-equation left side),
    folded with `Fp12Val.mul ξ₀` from the GT identity `1`. -/
@[reducible] def pairingProductF (ξ0 : ZMod p) (gts : List (Fp12Val p)) : Fp12Val p :=
  gts.foldl (Fp12Val.mul ξ0) 1

/-- `elliptic_curve.pairing_check` over a list of pairings:
    `∏ᵢ eᵢ == 1 : Bool`. -/
@[reducible] def pairingCheckF (ξ0 : ZMod p) (gts : List (Fp12Val p)) : Bool :=
  gtIsOneF (pairingProductF ξ0 gts)

/-- `elliptic_curve.pairing_check` two-pairing specialisation:
    `e₁ ·_{ξ₀} e₂ == 1 : Bool` (the BLS-verify / Groth16 shape). -/
@[reducible] def pairingCheck2F (ξ0 : ZMod p) (e1 e2 : Fp12Val p) : Bool :=
  gtIsOneF (Fp12Val.mul ξ0 e1 e2)

/-! ## 2. Agreement lemmas (`Bool ↔ Prop`, fold recurrences) -/

/-- **Agreement.** The single-pairing check is `true` iff the GT element is the
    identity. -/
theorem gtIsOne_iff (e : Fp12Val p) : gtIsOneF e = true ↔ e = 1 :=
  gtIsOneF_iff e

/-- **Agreement.** The two-pairing check is `true` iff the GT product is the
    identity. -/
theorem pairingCheck2F_iff (ξ0 : ZMod p) (e1 e2 : Fp12Val p) :
    pairingCheck2F ξ0 e1 e2 = true ↔ Fp12Val.mul ξ0 e1 e2 = 1 := by
  simp [pairingCheck2F]

/-- The empty multi-pairing product is the GT identity (the check passes
    vacuously). -/
@[simp] theorem pairingProductF_nil (ξ0 : ZMod p) :
    pairingProductF ξ0 [] = (1 : Fp12Val p) := rfl

/-- A single-pairing list check reduces to the single GT-identity test (with the
    identity-times factor). -/
theorem pairingCheckF_singleton (ξ0 : ZMod p) (e : Fp12Val p) :
    pairingCheckF ξ0 [e] = gtIsOneF (Fp12Val.mul ξ0 1 e) := rfl

/-! ## 3. Type (`PairingCheckTy`) -/

/-- The pairing-check dialect's value-type alphabet: the GT (= `Fp12`) operand
    and the `BoolLike` result. -/
inductive PairingCheckTy where
  /-- A GT (= `Fp12`) element, `⟦·⟧ = Fp12Val p` (the `FieldDialect` carrier). -/
  | gt (p : Nat)
  /-- The `BoolLike` result, `⟦·⟧ = Bool`. -/
  | bool
  deriving DecidableEq

/-- Total denotation of `PairingCheckTy`: the GT operand denotes to `Fp12Val p`,
    `bool` to `Bool`. -/
@[reducible] instance : TyDenote PairingCheckTy where
  denote
    | .gt p => Fp12Val p
    | .bool => Bool

/-! ## 4. Op tags (`PairingCheckOp`)

Each op carries a `publicData : Bool` flag governing `ctSafe` (the GT equality is
CT only on public verification values). -/

/-- Operation tags for the pairing-check dialect — prime-ir's
    `elliptic_curve.pairing_check`, as a single-pairing GT-identity test and a
    two-pairing product test.  `pairingCheck2` carries the curve non-residue `ξ₀`
    (the `Fp12` multiply parameter). -/
inductive PairingCheckOp where
  /-- `elliptic_curve.pairing_check` single: `(e : gt p) ↦ (e == 1)`. -/
  | gtIsOne (p : Nat) (publicData : Bool)
  /-- `elliptic_curve.pairing_check` two-pairing: `(e₁ e₂) ↦ (e₁ ·_{ξ₀} e₂ == 1)`. -/
  | pairingCheck2 (p : Nat) (ξ0 : ZMod p) (publicData : Bool)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The pairing-check dialect: `Op` is `PairingCheckOp`, `Ty` is
    `PairingCheckTy`. -/
@[reducible] def pairingCheckDialect : Dialect :=
  { Op := PairingCheckOp, Ty := PairingCheckTy }

/-! ## 6. Op signatures (arg types + return type — every op returns `bool`) -/

instance : DialectSignature pairingCheckDialect where
  sig op := match op with
    | .gtIsOne p _ => [.gt p]
    | .pairingCheck2 p _ _ => [.gt p, .gt p]
  ret op := match op with
    | .gtIsOne _ _ => .bool
    | .pairingCheck2 _ _ _ => .bool

/-! ## 7. Op denotation (into the GT-equality `Bool`) -/

instance pairingCheckDenote : DialectDenote pairingCheckDialect where
  denote op := match op with
    | .gtIsOne _ _ => fun args => gtIsOneF args.head
    | .pairingCheck2 _ ξ0 _ => fun args => pairingCheck2F ξ0 args.head args.tail.head

/-! ## 8. Per-op denotation / agreement facts -/

/-- `gtIsOne` denotes to the GT-identity test. -/
theorem gtIsOne_denote (pub : Bool) (e : Fp12Val p) :
    pairingCheckDenote.denote (.gtIsOne p pub) (.cons e .nil) = gtIsOneF e := rfl

/-- The `gtIsOne` op is `true` iff the GT element is the identity. -/
theorem gtIsOne_denote_iff (pub : Bool) (e : Fp12Val p) :
    pairingCheckDenote.denote (.gtIsOne p pub) (.cons e .nil) = true ↔ e = 1 := by
  rw [gtIsOne_denote, gtIsOneF_iff]

/-- `pairingCheck2` denotes to the two-pairing product check. -/
theorem pairingCheck2_denote (ξ0 : ZMod p) (pub : Bool) (e1 e2 : Fp12Val p) :
    pairingCheckDenote.denote (.pairingCheck2 p ξ0 pub) (.cons e1 (.cons e2 .nil))
      = pairingCheck2F ξ0 e1 e2 := rfl

/-- The `pairingCheck2` op is `true` iff the GT product is the identity. -/
theorem pairingCheck2_denote_iff (ξ0 : ZMod p) (pub : Bool) (e1 e2 : Fp12Val p) :
    pairingCheckDenote.denote (.pairingCheck2 p ξ0 pub) (.cons e1 (.cons e2 .nil)) = true
      ↔ Fp12Val.mul ξ0 e1 e2 = 1 := by
  rw [pairingCheck2_denote, pairingCheck2F_iff]

/-! ## 9. Constant-time predicate — the GT-equality hazard

A GT equality test is data-dependent; `ctSafe = publicData`.  A secret-operand
pairing check (`publicData = false`) is flagged, never silently admitted —
exactly the `FieldEcCmpOps` comparison-hazard discipline applied to GT. -/

/-- Per-op CT predicate: a pairing check is CT **iff** its operands are public. -/
def PairingCheckOp.ctSafe : PairingCheckOp → Bool
  | .gtIsOne _ pub => pub
  | .pairingCheck2 _ _ pub => pub

/-- A public-data two-pairing check is admitted as CT (signature verification on
    public group elements). -/
@[simp] theorem PairingCheckOp.ctSafe_pairingCheck2_public {p : Nat} (ξ0 : ZMod p) :
    (PairingCheckOp.pairingCheck2 p ξ0 true).ctSafe = true := rfl

/-- **The hazard, made explicit.** A secret-operand two-pairing check is NOT CT. -/
@[simp] theorem PairingCheckOp.ctSafe_pairingCheck2_secret {p : Nat} (ξ0 : ZMod p) :
    (PairingCheckOp.pairingCheck2 p ξ0 false).ctSafe = false := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt pairingCheckDialect} {t : PairingCheckTy}
    (e : Expr pairingCheckDialect Γ t) : Bool :=
  e.op.ctSafe

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound pairing
    check is public-data. -/
def ctSafeCom {Γ : Ctxt pairingCheckDialect} {t : PairingCheckTy} :
    Com pairingCheckDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- A pairing-check program built only of public-data ops is CT-safe; a
    secret-operand check is flagged by `ctSafeCom`. -/
theorem ctSafeCom_public {Γ : Ctxt pairingCheckDialect} {t : PairingCheckTy}
    (c : Com pairingCheckDialect Γ t)
    (h : ∀ {Γ' : Ctxt pairingCheckDialect} {t' : PairingCheckTy}
          (e : Expr pairingCheckDialect Γ' t'), e.op.ctSafe = true) :
    ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp only [ctSafeCom, ctSafeExpr, h e, ih, Bool.and_self]

/-! ## 10. Smoke test

A one-op `Com pairingCheckDialect`: `let r = gtIsOne e; ret r` over `ZMod 7`,
public data.  On `e = 1` (the GT identity) it returns `true`. -/

/-- One-op smoke program: a public-data `gtIsOne` over `[gt 7]`. -/
def smokeProg : Com pairingCheckDialect [.gt 7] .bool :=
  .var (.mk (.gtIsOne 7 true) rfl (.cons .here .nil))
    (.ret .here)

/-- The smoke program denotes to the GT-identity test; on `e = 1` it is `true`. -/
example : smokeProg.denote (.cons (1 : Fp12Val 7) .nil) = true := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckOps
