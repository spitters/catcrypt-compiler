/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CryptoSSA
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# CryptoSSA → VIR (Jasmin dialect): shared type/context/variable maps

Shared infrastructure for sourcing CatCrypt's extraction-side intrinsically-typed
SSA substrate into the typed-SSA Jasmin dialect (`Com jasminDialect`). The
substrate's De Bruijn contexts (`Ctx`) are lists of `CryptoTy`, while the Jasmin
dialect's contexts are lists of `JasminTy`, so the bridge is a **type map**
`mapTy : CryptoTy → JasminTy`, lifted to a **context map**
`mapCtx : Ctx → Ctxt jasminDialect` (`= List.map mapTy`), and the corresponding
variable / argument-vector translations.

## The structural insight

Because `mapCtx (s :: Γ) = mapTy s :: mapCtx Γ` holds *definitionally* (it is
`List.map`), the variable translation
`toJVar : CVar Γ t → Ctxt.Var (mapCtx Γ) (mapTy t)` is the clean
`here ↦ here`, `there ↦ there` — the dependent indices line up by `rfl`. The
argument-vector translation `toJArgs` is the pointwise extension.

## Type map (`mapTy`)

| `CryptoTy`   | `JasminTy`        | rationale                                  |
|--------------|-------------------|--------------------------------------------|
| `sword w`    | `reg w`           | a `w`-bit machine word ↦ a `w`-bit register |
| `bit`        | `reg 1`           | a single bit ↦ a 1-bit register            |
| `unit`       | `reg 0`           | nullary ↦ a 0-bit register                 |
| `memref n`   | `stackArr 64 n`   | `n × u64` limb array ↦ stack array         |
| `pair`/`sum` | `reg 0` (placeholder) | no register/stack analogue              |

`pair`/`sum` have no register/stack analogue in the straight-line Jasmin
fragment, so `mapTy` sends them to a placeholder `reg 0`. The placeholder only
ever appears as a context entry that the lowered fragment never reads.
-/

@[expose] public section

set_option autoImplicit true -- SSA IR front: many context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## 1. Type and context maps -/

/-- Map a `CryptoTy` to a `JasminTy`. `pair`/`sum` have no register/stack
    analogue in the straight-line fragment, so they map to a placeholder
    `reg 0`; the lowering refuses any expression touching them. -/
@[implicit_reducible]
def mapTy : CryptoTy → JasminTy
  | .sword w => .reg w
  | .bit => .reg 1
  | .unit => .reg 0
  | .memref n => .stackArr 64 n
  | .memrefW w n => .stackArr w n
  | .pair _ _ => .reg 0
  | .sum _ _ => .reg 0

/-- Lift the type map over a De Bruijn context. Definitionally `List.map mapTy`,
    so `mapCtx (s :: Γ) = mapTy s :: mapCtx Γ` holds by `rfl`. -/
@[implicit_reducible]
def mapCtx (Γ : Ctx) : Ctxt jasminDialect := Γ.map mapTy

/-! ## 2. Variable translation

Because `mapCtx (s :: Γ) = mapTy s :: mapCtx Γ` reduces, the dependent indices
line up and the translation is the clean `here ↦ here`, `there ↦ there`. -/

/-- Translate a CryptoSSA De Bruijn variable to a Jasmin-dialect variable,
    transporting along `mapTy`/`mapCtx`. -/
def toJVar {Γ : Ctx} {t : CryptoTy} :
    CVar Γ t → Ctxt.Var (d := jasminDialect) (mapCtx Γ) (mapTy t)
  | .here => .here
  | .there v => .there (toJVar v)

/-! ## 3. Argument-vector translation

An argument vector `args : CHVector (CVar Γ ·) argTys` maps pointwise to a Jasmin
`HVector` indexed by `argTys.map mapTy` — matching the signature of
`JasminOp.extCall name (argTys.map mapTy) (mapTy retTy)`, whose
`DialectSignature.sig` is exactly `argTys.map mapTy`. -/

/-- Translate a CryptoSSA `CHVector` of variables to a Jasmin `HVector` of
    `Ctxt.Var`s, indexed by the pointwise-mapped argument types. -/
def toJArgs {Γ : Ctx} :
    {argTys : List CryptoTy} → CHVector (fun t => CVar Γ t) argTys →
    HVector (fun ty => Ctxt.Var (d := jasminDialect) (mapCtx Γ) ty)
      (argTys.map mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (toJVar v) (toJArgs rest)

end CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
