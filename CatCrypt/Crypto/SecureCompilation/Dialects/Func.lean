/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The `func` dialect (D0 fan-out — CatCrypt-side, not in `VIR/`)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The function-call neutral dialect of the MLIR dialect-alignment restructure
(D0 fan-out). It is the
target-neutral *call* fragment — upstream MLIR's `func` / Veir `Func` — defined
over the CatCrypt VIR `Com`/`Dialect` framework.

## Why CatCrypt-side, not in `VIR/`

`VIR/` is our **vendored copy of Veir**, re-synced on stable releases, so a dialect
added inside `VIR/` would be clobbered on the next sync. The new neutral dialects
live in `Crypto/SecureCompilation/Dialects/`, **consuming** the VIR `Dialect` /
`DialectSignature` / `DialectDenote` framework. Op/type names mirror upstream MLIR
`func` (`func.call`) as a migration contract.

## Why this mirrors the *lattice* lowering, not the *arith* one

`Arith.lean` lowers each neutral op to a **concrete** jasmin op (`regArith`/`mulhi`/
…). A `func.call` has no concrete jasmin instruction — it is an opaque named call,
so it lowers to a jasmin `extCall` exactly as the lattice NTT ops do
(`VIR/LatticeToJasmin.lean`). The lattice triple is therefore this dialect's closest
template: `FuncOp.call` → `JasminOp.extCall` is precisely lattice's
`LatticeOp → extCall` pattern.

## Scope of this gate (v1: the scalar `reg` fragment)

`FuncTy` is the scalar integer fragment `int w` (→ jasmin `reg w`), matching the
typed signature `extCall` carries. `FuncOp.call name argTys retTy` is
`func.call @name(args) : (argTys) → retTy`, lowering 1:1 to
`JasminOp.extCall name (argTys.map toJasmin) (toJasmin retTy)`.

A multi-result `callN` op mirroring `JasminOp.callN` is included
(`FuncOp.callN name argTys retTys`); like jasmin's `callN`, its single-`ret`
`Expr`-level denotation is the opaque default of its head result type
(`callNRet`), so the framework's single-return `Expr` arm projects the tuple to
its head slot.

## Denotation

Both `func` ops denote to the **same opaque default** the jasmin target uses
(`JasminTy.default`), so the lowering is denotation-preserving by construction —
mirroring how the lattice `extCall` agrees with `jasminExtSem`. Because `func`'s
return types map to scalar jasmin `reg w` (never the 16-bit `stackArr` the lattice
leaves use), the `extCall` denotation always lands in `jasminExtSem`'s opaque
catch-all, so the agreement is exact and hypothesis-free.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Func

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Types — `i<w>` (the scalar fragment) -/

/-- `func` value types (v1 scalar fragment): a `w`-bit integer `i<w>`,
    `⟦·⟧ = BitVec w` (mirrors jasmin `reg w`). Calls take and return scalar
    registers, matching the typed `extCall` signature. -/
inductive FuncTy where
  | int (w : Nat)
  deriving DecidableEq

/-- Total denotation of `FuncTy`. -/
@[reducible] def FuncTy.denote : FuncTy → Type
  | .int w => BitVec w

instance : TyDenote FuncTy where
  denote := FuncTy.denote

/-- A default inhabitant for each `FuncTy`, matching `JasminTy.default` on the
    `toJasmin` image (`int w ↦ reg w ↦ 0`). The opaque call denotation. -/
def FuncTy.default : (t : FuncTy) → TyDenote.denote t
  | .int w => (0 : BitVec w)

/-! ## 2. Ops — the neutral-`func` fragment (upstream `func` names) -/

/-- The neutral function-call op set.

    * `call name argTys retTy` — `func.call @name(args) : (argTys) → retTy`, a
      single-result named call lowering 1:1 to `JasminOp.extCall`.
    * `callN name argTys retTys` — a `k`-result named call lowering 1:1 to
      `JasminOp.callN`. At the framework's single-`ret` `Expr` level it exposes
      its head result type (`callNRet`), the rest of `retTys` is op-data for the
      lowering. -/
inductive FuncOp where
  /-- `func.call @name(args) : (argTys) → retTy` — single-result call. -/
  | call (name : String) (argTys : List FuncTy) (retTy : FuncTy)
  /-- Multi-result `func.call @name(args) : (argTys) → retTys` — `k` outputs. -/
  | callN (name : String) (argTys : List FuncTy) (retTys : List FuncTy)
  deriving DecidableEq

/-- The `func` dialect over the CatCrypt VIR framework. -/
@[reducible] def funcDialect : Dialect := { Op := FuncOp, Ty := FuncTy }

/-- The single representative result type a multi-result `callN` exposes at the
    framework's single-`ret` `Expr` level (its head/primary result slot), with
    a `.int 0` default for the empty list — mirroring jasmin `callNRet`. -/
def funcCallNRet (retTys : List FuncTy) : FuncTy := retTys.headD (.int 0)

/-! ## 3. Signatures -/

instance : DialectSignature funcDialect where
  sig op := match op with
    | .call _ argTys _ => argTys
    | .callN _ argTys _ => argTys
  ret op := match op with
    | .call _ _ retTy => retTy
    | .callN _ _ retTys => funcCallNRet retTys

/-! ## 4. Denotation (opaque — matches the jasmin `extCall`/`callN` image)

A named call is opaque: its result is the per-type default
(`FuncTy.default` / the head of `callNDefaults`). This is exactly the value the
jasmin target produces for the lowered `extCall`/`callN` (scalar `reg` return ⇒
`jasminExtSem` catch-all ⇒ `JasminTy.default`), so the lowering is
denotation-preserving by construction. -/

instance funcDenote : DialectDenote funcDialect where
  denote op := match op with
    | .call _ _ retTy => fun _ => FuncTy.default retTy
    | .callN _ _ retTys => fun _ => FuncTy.default (funcCallNRet retTys)

/-! ## 5. The lowering image into `jasminDialect` -/

/-- Type image: `i<w>` ↦ jasmin `reg w`. (`⟦i w⟧ = BitVec w = ⟦reg w⟧`
    definitionally, so the value transport across this map is the identity.) -/
def FuncTy.toJasmin : FuncTy → JasminTy
  | .int w => .reg w

/-- Op image into `jasminDialect`: a single-result `call` becomes a jasmin
    `extCall` carrying the `toJasmin`-mapped signature; a `callN` becomes a jasmin
    `callN` carrying the `toJasmin`-mapped argument and result lists. By
    construction the jasmin op's declared signature is `(sig op).map toJasmin`
    with return `toJasmin (ret op)`, so `lowerExpr` needs no cast (cf. lattice's
    `jasminOpOf`). -/
def FuncOp.toJasmin : FuncOp → JasminOp
  | .call name argTys retTy =>
      .extCall name (argTys.map FuncTy.toJasmin) (retTy.toJasmin)
  | .callN name argTys retTys =>
      .callN name (argTys.map FuncTy.toJasmin) (retTys.map FuncTy.toJasmin)

/-- `funcCallNRet` commutes with `toJasmin`: the head of the `toJasmin`-mapped
    result list is the `toJasmin` image of the head (`headD` over `List.map`),
    with `(int 0).toJasmin = reg 0 = callNRet []`. The fact the `callN` return-type
    correspondence needs. -/
theorem funcCallNRet_toJasmin (retTys : List FuncTy) :
    callNRet (retTys.map FuncTy.toJasmin) = (funcCallNRet retTys).toJasmin := by
  cases retTys <;> rfl

/-- The op image preserves the signature: arg types map pointwise via
    `FuncTy.toJasmin` and the result type matches (by construction of the
    `extCall`/`callN` image). Both are `rfl`/`cases`-deep. -/
theorem toJasmin_ret (op : FuncOp) :
    DialectSignature.ret (d := jasminDialect) op.toJasmin
      = (DialectSignature.ret (d := funcDialect) op).toJasmin := by
  cases op with
  | call name argTys retTy => rfl
  | callN name argTys retTys => exact funcCallNRet_toJasmin retTys

theorem toJasmin_sig (op : FuncOp) :
    DialectSignature.sig (d := jasminDialect) op.toJasmin
      = (DialectSignature.sig (d := funcDialect) op).map FuncTy.toJasmin := by
  cases op <;> rfl

/-! ## 6. Smoke test — the dialect denotes -/

/-- One-op smoke program `f(a, b)` over `[i32, i32]`: a single `func.call`
    returning `i64`, denoting to the opaque default. -/
def smokeProg : Com funcDialect [.int 32, .int 32] (.int 64) :=
  .var (.mk (.call "f" [.int 32, .int 32] (.int 64)) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The smoke program denotes to the opaque default `(0 : BitVec 64)`. -/
example :
    smokeProg.denote (.cons (7 : BitVec 32) (.cons (35 : BitVec 32) .nil))
      = (0 : BitVec 64) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.Func
