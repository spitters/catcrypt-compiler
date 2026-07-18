/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# CProg-free variable / valuation bridge (substrate ↔ `catCryptDialect`)

This module collects the **`CProg`/`CExpr`-free** helper defs and lemmas that
relate the CryptoSSA *substrate* (`CVar`, `CHVector`, `HVec`, `CryptoTy`) to the
`catCryptDialect` `Var`/`Valuation`/`lookupArgs` layer. None of these mention
`CExpr`, `CProg`, or the `CExpr→dialect` translators (`toVIRExprT`/`toVIRComT`):
they only relabel de-Bruijn variables and reinterpret heterogeneous valuations.

They were previously housed in `VIR/CryptoToVIR.lean` (the `toVIRVar` /
`toVIRArgs` variable translators) and `Dialects/CryptoSSAToCryptoDialectFull.lean`
(`toVIRVal`, `toVIRVar_lookup`, `lookupArgs_one`/`_two`/`_three`, `argLookup`,
`lookupArgs_toVIRArgs`). Both of those files belong to the `CProg`-bridge cluster
that is being retired; the dialect-targeting Jasmin front
(`Jasmin/JasminToSSADialect*.lean`, `Jasmin/S2NBignumSSADialect.lean`) only ever
used these variable/valuation helpers, so they live here in a `CProg`-free
support module that imports nothing from the retiring cluster.

Imports only the substrate + dialect (`CatCryptDialect`, which itself re-exports
`VIR/Core` and `CryptoSSA`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## 1. Variable translation -/

/-- Translate a CryptoSSA De Bruijn variable to a VIR variable.
    Since `CryptoTy = catCryptDialect.Ty`, context types match directly. -/
def toVIRVar {Γ : Ctx} {t : CryptoTy} : CVar Γ t → Ctxt.Var (d := catCryptDialect) Γ t
  | .here => .here
  | .there v => .there (toVIRVar v)

/-- Translate a CryptoSSA `CHVector` of variables to a VIR `HVector` of
    `Ctxt.Var`s, by pointwise application of `toVIRVar`. -/
def toVIRArgs {Γ : Ctx} :
    {argTys : List CryptoTy} → CHVector (fun t => CVar Γ t) argTys →
    HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) argTys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (toVIRVar v) (toVIRArgs rest)

/-! ## 2. Valuation bridge for `toVIRVar`

`toVIRVar` builds dialect variables, so we bridge `HVec` to `Ctxt.Valuation` and
prove variable lookup commutes with that (identity) relabelling. -/

/-- Reinterpret a CryptoSSA `HVec Γ` as a VIR `Ctxt.Valuation Γ` (same shape). -/
def toVIRVal {Γ : Ctx} : HVec Γ → Ctxt.Valuation (d := catCryptDialect) Γ
  | .nil => .nil
  | .cons v vs => .cons v (toVIRVal vs)

/-- Variable lookup commutes with the bridge, for `toVIRVar`. -/
theorem toVIRVar_lookup {Γ : Ctx} {t : CryptoTy} (x : CVar Γ t) (V : HVec Γ) :
    (toVIRVar x).lookup (toVIRVal V) = x.lookup V := by
  induction x with
  | here => cases V with | cons v vs => rfl
  | there x ih => cases V with | cons v vs => exact ih vs

/-- `lookupArgs` of a one-`toVIRVar` argument vector. -/
theorem lookupArgs_one {Γ : Ctx} {s : CryptoTy} (a : CVar Γ s) (V : HVec Γ) :
    Expr.lookupArgs (d := catCryptDialect)
        (.cons (toVIRVar a) .nil) (toVIRVal V)
      = .cons (a.lookup V) .nil := by
  show HVector.cons ((toVIRVar a).lookup (toVIRVal V)) HVector.nil = _
  rw [toVIRVar_lookup]

/-- `lookupArgs` of a two-`toVIRVar` argument vector. -/
theorem lookupArgs_two {Γ : Ctx} {s t : CryptoTy}
    (a : CVar Γ s) (b : CVar Γ t) (V : HVec Γ) :
    Expr.lookupArgs (d := catCryptDialect)
        (.cons (toVIRVar a) (.cons (toVIRVar b) .nil)) (toVIRVal V)
      = .cons (a.lookup V) (.cons (b.lookup V) .nil) := by
  show HVector.cons ((toVIRVar a).lookup (toVIRVal V))
        (HVector.cons ((toVIRVar b).lookup (toVIRVal V)) HVector.nil) = _
  rw [toVIRVar_lookup, toVIRVar_lookup]

/-- `lookupArgs` of a three-`toVIRVar` argument vector. -/
theorem lookupArgs_three {Γ : Ctx} {r s t : CryptoTy}
    (a : CVar Γ r) (b : CVar Γ s) (c : CVar Γ t) (V : HVec Γ) :
    Expr.lookupArgs (d := catCryptDialect)
        (.cons (toVIRVar a)
          (.cons (toVIRVar b) (.cons (toVIRVar c) .nil))) (toVIRVal V)
      = .cons (a.lookup V) (.cons (b.lookup V) (.cons (c.lookup V) .nil)) := by
  show HVector.cons ((toVIRVar a).lookup (toVIRVal V))
        (HVector.cons ((toVIRVar b).lookup (toVIRVal V))
          (HVector.cons ((toVIRVar c).lookup (toVIRVal V)) HVector.nil)) = _
  rw [toVIRVar_lookup, toVIRVar_lookup, toVIRVar_lookup]

/-- Pointwise `CVar.lookup` of an `extCall` argument vector. -/
def argLookup {Γ : Ctx} : {argTys : List CryptoTy} →
    CHVector (fun t => CVar Γ t) argTys → HVec Γ →
    HVector (fun ty => ⟦ty⟧) argTys
  | [], .nil, _ => .nil
  | _ :: _, .cons v rest, V => .cons (v.lookup V) (argLookup rest V)

/-- `extCall` argument-vector lookup commutes with the bridge, for
    `toVIRArgs`. -/
theorem lookupArgs_toVIRArgs {Γ : Ctx} :
    {argTys : List CryptoTy} → (args : CHVector (fun t => CVar Γ t) argTys) →
    (V : HVec Γ) →
    Expr.lookupArgs (d := catCryptDialect)
        (toVIRArgs args) (toVIRVal V)
      = argLookup args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((toVIRVar v).lookup (toVIRVal V))
            (Expr.lookupArgs (toVIRArgs rest) (toVIRVal V))
          = HVector.cons (v.lookup V) (argLookup rest V)
      rw [toVIRVar_lookup, lookupArgs_toVIRArgs rest V]

end CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
