/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptOpInfo
public import CatCrypt.Crypto.SecureCompilation.VIR.Grind
public import CatCrypt.Crypto.SecureCompilation.VIR.Regions

/-!
# VIR-level constant-time predicate

A static predicate `ctSafe` on `Expr catCryptDialect Γ t` and `ctSafeCom`
on `Com catCryptDialect Γ t` that captures: *this expression / program
has no data-dependent control flow and no data-dependent memory index*.

## Scope

This is the **first** (Track 3a) CT predicate at the VIR level. It is
designed to:
1. Be quickly checkable (decidable on closed `Com`s).
2. Match the existing ITree/event-sig `CTCompilerPass` at the abstract
   level (the bridge is `Track 3a step 4` in the workplan).
3. Be preserved by simple structural peephole rewrites — see
   `ctSafe_xor_self_cancel` example.

## What this captures

Per `CatCryptOpProperties.ConstantTimeProperties`:
* No data-dependent branch: in CatCrypt's IR this means `ite` is
  considered CT only when wrapped in a CT-public assertion (today, we
  conservatively flag `ite` as non-CT). All non-`ite` ops are CT.
* No data-dependent memory index: `memrefGet`/`memrefSet` use a `Fin n`
  *static* index in CatCryptOp's encoding, so they ARE CT. (If a future
  variable-index variant is added, it would need a separate flag.)

So the predicate is essentially: *contains no `ite` op*. Crude but
sufficient for Curve25519/Ed25519-style straight-line crypto, which is
exactly the Track 3b benchmark target.

## What this does NOT cover yet

* Variable-time div/mod — CatCryptOp has no division ops.
* Variable-time table lookups (e.g., AES S-box) — would need `memrefGet`
  with a `CVar` index, not currently encodable in CatCryptOp.
* Address-aware leakage (cache, branch prediction) — outside VIR scope.

A more refined predicate that flags `ite` as CT-safe when its condition
is annotated `@public` is outside this module's scope.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

namespace CatCryptDialect

/-! ## 1. Per-op CT predicate -/

/-- Is this op CT-preserving under the conservative (no-`ite`) policy? -/
def CatCryptOp.ctSafe : CatCryptOp → Bool
  | .ite _ => false
  -- Dynamic (runtime-index) memory ops are NOT unconditionally constant-time: a
  -- data-dependent memory index is the classic timing/cache leak. CT-ness holds
  -- only when the index is PUBLIC — that is the caller's obligation, discharged
  -- by the public-coins / labeling analysis (RejectionEnvelopeCT), not asserted
  -- here. Conservative `false` keeps `ctSafe` sound.
  | .memrefSetDyn _ | .memrefGetDyn _ | .memrefGetDyn128 _
  | .memrefWSetDyn _ _ | .memrefWGetDyn _ _ => false
  | _ => true

@[grind =]
theorem CatCryptOp.ctSafe_xor : CatCryptOp.ctSafe .xor = true := rfl

@[grind =]
theorem CatCryptOp.ctSafe_bvXor (w : Nat) :
    CatCryptOp.ctSafe (.bvXor w) = true := rfl

@[grind =]
theorem CatCryptOp.ctSafe_ite (t : CryptoTy) :
    CatCryptOp.ctSafe (.ite t) = false := rfl

end CatCryptDialect

open CatCryptDialect

/-! ## 2. Per-expression CT predicate -/

/-- An `Expr` is CT-safe iff its op is CT-safe (args are just variables,
    which carry no timing). -/
def ctSafeExpr {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) : Bool :=
  e.op.ctSafe

@[grind =]
theorem ctSafeExpr_op {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) : ctSafeExpr e = e.op.ctSafe := rfl

/-! ## 3. Per-program CT predicate -/

/-- A `Com` is CT-safe iff every let-bound expression is CT-safe. -/
def ctSafeCom {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    Com catCryptDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-! ## 4. Decidability + Prop bridge -/

/-- Propositional form of CT-safety. -/
def ctSafePropCom {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) : Prop :=
  ctSafeCom c = true

instance {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) : Decidable (ctSafePropCom c) := by
  unfold ctSafePropCom; infer_instance

/-! ## 5. Basic preservation theorems

These say that simple structural manipulations preserve `ctSafeCom`.
The first batch is what peephole rewrites need; chained automatically
via `grind`. -/

@[grind =]
theorem ctSafeCom_ret {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (v : Ctxt.Var Γ t) : ctSafeCom (Com.ret v) = true := rfl

@[grind =]
theorem ctSafeCom_var {Γ : Ctxt catCryptDialect} {t s : CryptoTy}
    (e : Expr catCryptDialect Γ t) (body : Com catCryptDialect (t :: Γ) s) :
    ctSafeCom (Com.var e body) = (ctSafeExpr e && ctSafeCom body) := rfl

/-! ## 6. Smoke test: a straight-line CT-safe program -/

example {Γ : Ctxt catCryptDialect} (v : Ctxt.Var Γ .bit) :
    ctSafeCom (Com.var (d := catCryptDialect) (Γ := Γ) (t := .bit) (s := .bit)
      { op := .xor, retTy_eq := rfl,
        args := .cons v (.cons v .nil) }
      (.ret .here)) = true := by
  grind

/-! ## 7. Region-extended CT-safety: `ctSafeComR`

The straight-line predicate `ctSafeCom` flags every conditional as
non-CT. Once we have *regions* (see `Regions.lean`), we can refine
this: a region whose `SecretLevel` tag is `.Public` (e.g., the
conditional was sampled, or it's a measurement outcome) is CT-safe
provided both branches are; a region tagged `.Secret` is **not**.

The CT-preservation guarantee is stated over this predicate.
The tag is caller-asserted (Phase J in `LowCT.lean` propagates the
flow); this predicate just consumes it. -/

open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-- Region-aware CT predicate. A `.Public`-tagged `ifBit` is CT-safe iff
    both branches are; a `.Secret`-tagged `ifBit` is never CT-safe. -/
def ctSafeComR {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    ComR catCryptDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeComR body
  | .ifBit _ .Public thenBr elseBr =>
      ctSafeComR thenBr && ctSafeComR elseBr
  | .ifBit _ .Secret _ _ => false

@[grind =]
theorem ctSafeComR_ret {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (v : Ctxt.Var Γ t) :
    ctSafeComR (ComR.ret (d := catCryptDialect) v) = true := rfl

@[grind =]
theorem ctSafeComR_var {Γ : Ctxt catCryptDialect} {t s : CryptoTy}
    (e : Expr catCryptDialect Γ t)
    (body : ComR catCryptDialect (t :: Γ) s) :
    ctSafeComR (ComR.var e body) = (ctSafeExpr e && ctSafeComR body) := rfl

@[grind =]
theorem ctSafeComR_ifBit_public {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (cond : Ctxt.Var Γ .bit)
    (thenBr elseBr : ComR catCryptDialect Γ t) :
    ctSafeComR (ComR.ifBit cond .Public thenBr elseBr)
      = (ctSafeComR thenBr && ctSafeComR elseBr) := rfl

@[grind =]
theorem ctSafeComR_ifBit_secret {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (cond : Ctxt.Var Γ .bit)
    (thenBr elseBr : ComR catCryptDialect Γ t) :
    ctSafeComR (ComR.ifBit cond .Secret thenBr elseBr) = false := rfl

/-! ## 8. Smoke tests for the region predicate -/

/-- Smoke test 1: a `Public`-tagged `ifBit` whose two branches are
    CT-safe (here both are `.ret`) is CT-safe. -/
example {Γ : Ctxt catCryptDialect} (cond : Ctxt.Var Γ .bit)
    (v : Ctxt.Var Γ .bit) :
    ctSafeComR (ComR.ifBit (d := catCryptDialect) (t := .bit)
        cond .Public (.ret v) (.ret v)) = true := by
  grind

/-- Smoke test 2: a `Secret`-tagged `ifBit` is never CT-safe,
    regardless of branch contents. -/
example {Γ : Ctxt catCryptDialect} (cond : Ctxt.Var Γ .bit)
    (v : Ctxt.Var Γ .bit) :
    ctSafeComR (ComR.ifBit (d := catCryptDialect) (t := .bit)
        cond .Secret (.ret v) (.ret v)) = false := by
  grind

/-! ## 9. Bridge: `ctSafeCom` lifts to `ctSafeComR` via `ComR.ofCom`

For any region-free `Com c`, the existing `ctSafeCom` matches the
new region-aware `ctSafeComR` on its lift. -/

theorem ctSafeComR_ofCom {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    ∀ (c : Com catCryptDialect Γ t),
      ctSafeComR (ComR.ofCom c) = ctSafeCom c
  | .ret _ => rfl
  | .var e body => by
      unfold ComR.ofCom ctSafeComR ctSafeCom
      rw [ctSafeComR_ofCom body]

end CatCrypt.Crypto.SecureCompilation.VIR
