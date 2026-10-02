/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.MlirScfDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum

/-!
# Sum of MLIR `arith` and `scf` dialects — `Cif` lowering

> **STATUS — MLIR-CORRESPONDENCE LAYER, NOT THE EMIT PATH.** The `arith ⊕ scf`
> agreement sum; NO lowering out, ZERO emit traffic. Composes the `mlirArith` and
> `mlirScf` correspondence layers, both of which duplicate the real
> `jasminDialect` substrate. See `CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md`.

This module constructs the dialect
`mlirArithScfDialect = mlirArithDialect ⊕ mlirScfDialect`, whose `Op` is
a tagged sum `MlirArithScfOp = arith MlirArithOp ∣ scf MlirScfOp` and
whose `Ty` is the shared `CryptoTy`.

The motivation is lowering **`Cif`**. `scfIf` requires a
`CryptoTy.bit` condition operand, but the source DSL holds the
condition as `sword 1`. Bridging requires an intervening
`arith.cmpi 1 != 0` (technically: we use `extui`-style bit extraction
via `cmpi 1` against a `constant 1 0`) — which lives in
`mlirArithDialect`, not `mlirScfDialect`. A single `Com` whose `Com.var`
can interleave both arith and scf ops is therefore required.

## Design

The dialect is the operation sum `Dialect.opSum` (`VIR/DialectOpSum.lean`):

1. The two dialects share `Ty = CryptoTy` exactly, so the sum dialect
   reuses the same `Ty`.
2. The `DialectSignature` and `DialectDenote` instances are the generic
   operation-sum instances, a case split: `arith op ↦ delegate to
   MlirArithDialect`, `scf op ↦ delegate to MlirScfDialect`.
3. Embedding theorems (`arith_embed_denote_eq`, `scf_embed_denote_eq`)
   close by `rfl` because the denotation is a literal case split. The
   whole-program inclusions are `DialectOpSum.inl` / `DialectOpSum.inr`
   with `DialectOpSum.inl_fundamental` / `DialectOpSum.inr_fundamental`.

## Usage

The downstream `compileCif` (in `ComToVeir.lean`) emits a 3-line
program over this sum dialect:

```
let zero    : sword 1 = arith.constant 1 0
let condBit : bit     = arith.cmpi 1 (cond, zero)  -- ne via xnor of eq
let result  : sword w = scf.if condBit (thenF, elseF) input
return result
```

The denotation reduces — by case-split on the bit's value — to the
source `ScfProg.eval`'s `if/then/else`.

## Status

`mlirArithScfDialect` is an instance of `Dialect.opSum`. The union is required
for the `Cif` lowering: the `arith.cmpi 1 != 0` bridge (arith) feeding `scf.if`
(scf) must live in a single `Com` whose `Com.var` chain can interleave both.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlirArithScfSum

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MlirScfDialect

/-! ## 1. Op tags -/

/-- Operations of the sum dialect: either an arith op or an scf op. -/
abbrev MlirArithScfOp : Type := MlirArithOp ⊕ MlirScfOp

/-- An arith op as an op of the sum dialect. -/
@[match_pattern] abbrev MlirArithScfOp.arith (op : MlirArithOp) : MlirArithScfOp :=
  Sum.inl op

/-- An scf op as an op of the sum dialect. -/
@[match_pattern] abbrev MlirArithScfOp.scf (op : MlirScfOp) : MlirArithScfOp :=
  Sum.inr op

/-! ## 2. The dialect, signature, denotation -/

/-- The sum dialect: `Op` is the tagged sum, `Ty` is the shared `CryptoTy`. It is
    the operation sum `Dialect.opSum mlirArithDialect mlirScfDialect`
    (`mlirArithScfDialect_eq_opSum`); the `Op` field is spelled `MlirArithScfOp`
    so that `.arith` and `.scf` resolve against it. -/
@[reducible] def mlirArithScfDialect : Dialect :=
  { Op := MlirArithScfOp, Ty := CryptoTy }

/-- `mlirArithScfDialect` is the operation sum of `mlirArithDialect` and
    `mlirScfDialect`. -/
theorem mlirArithScfDialect_eq_opSum :
    mlirArithScfDialect = Dialect.opSum mlirArithDialect mlirScfDialect := rfl

/-- Operation signatures: the operation-sum signature, a case split delegating to
    the summand. Marked `@[reducible]` so the scf-side embedding's `sig`/`ret`
    reduces under a literal constructor match (needed for the `Expr.mk` shape
    lemmas in `compileCif`). -/
@[reducible] instance instMlirArithScfSignature :
    DialectSignature mlirArithScfDialect :=
  DialectOpSum.instDialectSignatureOpSum (O₁ := MlirArithOp) (O₂ := MlirScfOp)
    (T := CryptoTy)

/-- Operation denotation: the operation-sum denotation, a case split delegating to
    the summand. -/
instance instMlirArithScfDenote :
    DialectDenote mlirArithScfDialect :=
  DialectOpSum.instDialectDenoteOpSum (O₁ := MlirArithOp) (O₂ := MlirScfOp)
    (T := CryptoTy)

/-! ## 3. Embedding agreement

Wrapping an `arith` or `scf` op in the sum preserves its denotation.
Both close by `rfl` because the denotation is a literal case-split. -/

/-- An `arith` op embedded in the sum dialect denotes the same as in
    `mlirArithDialect`. -/
theorem arith_embed_denote_eq (op : MlirArithOp)
    (args : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := mlirArithDialect) op)) :
    DialectDenote.denote (d := mlirArithScfDialect) (.arith op) args
      = DialectDenote.denote (d := mlirArithDialect) op args := rfl

/-- An `scf` op embedded in the sum dialect denotes the same as in
    `mlirScfDialect`. -/
theorem scf_embed_denote_eq (op : MlirScfOp)
    (args : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := mlirScfDialect) op)) :
    DialectDenote.denote (d := mlirArithScfDialect) (.scf op) args
      = DialectDenote.denote (d := mlirScfDialect) op args := rfl

/-! ## 4. Smoke tests

A direct check that the sum dialect's denotation reduces by `rfl` on
concrete inputs. -/

/-- A constant `arith.constant 8 42` embedded in the sum dialect
    denotes to `42`. -/
example :
    DialectDenote.denote (d := mlirArithScfDialect)
        (.arith (.constant 8 42)) HVector.nil
      = (42 : BitVec 8) := rfl

/-- An `scfIf` embedded in the sum dialect denotes to the right branch. -/
example :
    DialectDenote.denote (d := mlirArithScfDialect)
        (.scf (.scfIf 8 (fun x => x + 1) (fun x => x - 1)))
        (HVector.cons true (HVector.cons (5 : BitVec 8) HVector.nil))
      = (6 : BitVec 8) := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.MlirArithScfSum
