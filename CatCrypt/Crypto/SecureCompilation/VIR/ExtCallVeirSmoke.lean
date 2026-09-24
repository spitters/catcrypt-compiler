/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir_CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir_CatCryptDialect

/-!
# End-to-end `extCall` smoke test: `LowCT → Com[catCryptDialect] → Veir`

This file demonstrates the *full* verified lowering chain for a
tiny extracted-style kernel containing leaf `RCall`s, the construct handled
without verification by the `LowCTToMLIR.lean` text formatter.

The front is the direct dialect translator
`translateDialectControl` (`Dialects/TranslateDialectDirectControl.lean`): it
translates `LowCT` *directly* to `Com catCryptDialect`, building each leaf
call's `extCall` op (args carried by an intrinsically-typed `HVector` via
`toVIRArgs`). The chain is:

```
LowCT  ──translateDialectControl──▶  Com[catCryptDialect]
       ──lowerClosedComToModuleWithExterns──▶  Veir.IRContext
       ──printModule──▶  MLIR text with `func.call @fp_add`
```

The verified chain therefore covers the case the `LowCTToMLIR` text formatter
handles.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ExtCallVeirSmoke

open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. A tiny extracted-style `LowCT` kernel with leaf calls

`a = fp_zero(); b = fp_zero(); c = fp_add(a, b)` over Curve25519 field
elements. The operands `a` and `b` are bound as the destinations of two
`fp_zero` leaf calls (so they are `TFp25519` storage — `memref 5`),
keeping the whole program closed and type-coherent with `fp_add`. The
dialect front covers `RSeq`/`RCall` (`TranslateDialectDirectArms`'s
leaf-call arms), so every leaf call threads through directly. -/

/-- `a = fp_zero(); b = fp_zero(); c = fp_add(a, b)`. -/
def kernel : LowCT :=
  .RSeq (.RCall "fp_zero" { locVar := "a", locSrc := .TFp25519 } [])
    (.RSeq (.RCall "fp_zero" { locVar := "b", locSrc := .TFp25519 } [])
      (.RCall "fp_add"
        { locVar := "c", locSrc := .TFp25519 }
        [ { locVar := "a", locSrc := .TFp25519 },
          { locVar := "b", locSrc := .TFp25519 } ]))

/-! ## 2. Front: `LowCT → Com[catCryptDialect]`

We drive the direct dialect front `translateDialectControl` from the empty
`VarMap` (`Γ = []`). It returns a `DTransOut []` whose `cont : ComCont [] Γ'`
is a `Com`-prefix carrying the three `extCall` leaves. We close
the program by applying that prefix to a `let _ = (); ret _` terminator at the
final context `Γ'`, giving a closed `Com catCryptDialect [] .unit`. -/

/-- Closed dialect program produced by the dialect front: apply the
    translated `ComCont` prefix to a `constUnit; ret` terminator. -/
def comProgOpt : Option (Com catCryptDialect [] .unit) :=
  match translateDialectControl
      (CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA.VarMap.empty) kernel with
  | some o =>
      o.cont (Com.var { op := .constUnit, retTy_eq := rfl, args := .nil } (.ret .here))
  | none => none

/-- The leaf `RCall`s are supported by the dialect front, and the
    closing `ComCont` application succeeds. -/
theorem comProg_isSome : comProgOpt.isSome := by
  native_decide

/-- The closed dialect program (containing the `extCall` leaves). -/
def comProg : Com catCryptDialect [] .unit :=
  comProgOpt.get comProg_isSome

/-- The dialect program references the externs `fp_zero` and `fp_add` (in source
    order, deduped) — i.e. each leaf `RCall`'s callee name survived the direct
    `LowCT → Com` translation with its name intact. -/
theorem comProg_extern :
    (dedupExternsByName (Com.catcryptExterns comProg)).map (·.1) = ["fp_zero", "fp_add"] := by
  native_decide

/-! ## 3. Back: `Com → Veir`

The generic `ComToVeir` lowering, instantiated at `catCryptDialect` via the
`ToVeirOp`/`ToVeirTy` instances in `ComToVeir_CatCryptDialect.lean`, turns the
`Com` into a Veir `IRContext`. Each `extCall` op lowers to a Veir `func_call`
op carrying a `callee = @<name>` attribute (see `CatCryptOp.toVeirOp` /
`attrsOfOp`). -/

/-- Lower `comProg` to a Veir `builtin.module` with private `func.func` extern
    decls for `fp_zero`/`fp_add` plus the main `func.func`. The result is a
    concrete `IRContext × OperationPtr` — the type-check is the end-to-end
    smoke signal (Veir's `HashMap`-backed `IRContext` does not reduce under the
    kernel for `decide`). -/
def veirModule : Veir.IRContext Veir.OpCode × Veir.OperationPtr :=
  lowerClosedComToModuleWithExterns (d := catCryptDialect) comProg
    (dedupExternsByName (Com.catcryptExterns comProg))
    Veir.OpCode.builtin_module default
    Veir.OpCode.func_func default
    Veir.OpCode.func_return default
    "fp_add_kernel"

/-- The full chain type-checks: `LowCT → Com[catCryptDialect] → Veir`. -/
example : Veir.IRContext Veir.OpCode × Veir.OperationPtr := veirModule

/-- Render the lowered Veir module to MLIR text. Prints a `builtin.module`
    containing `func.func private @fp_zero` / `func.func private @fp_add` and
    the main `func.func @fp_add_kernel` whose body holds the
    `"func.call"(...) {callee = @fp_add}` op. -/
def emitKernelVeirText : IO String := do
  let (ctx, modOp) := veirModule
  VeirPrinterShim.printModuleToString ctx modOp

-- Run the whole pipeline and print the emitted MLIR. The expected output is a
-- `builtin.module` with private `func.func @fp_zero` / `func.func @fp_add`
-- extern decls and a main `func.func @fp_add_kernel` whose body contains
-- `%N = "func.call"(...) {callee = @fp_add}` — i.e. the leaf `extCall`s
-- threaded all the way from `LowCT` to Veir.
#eval do
  let txt ← emitKernelVeirText
  IO.println txt

end CatCrypt.Crypto.SecureCompilation.VIR.ExtCallVeirSmoke
