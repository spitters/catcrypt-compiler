/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.MlirScfDialect

/-!
# Sum of MLIR `arith` and `scf` dialects — Phase 6d Cif closure

> **STATUS — MLIR-CORRESPONDENCE LAYER, NOT THE EMIT PATH.** The `arith ⊕ scf`
> agreement sum; NO lowering out, ZERO emit traffic. Composes the `mlirArith` and
> `mlirScf` correspondence layers, both of which duplicate the real
> `jasminDialect` substrate. See `CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md`.

This file constructs the dialect
`mlirArithScfDialect = mlirArithDialect ⊕ mlirScfDialect`, whose `Op` is
a tagged sum `MlirArithScfOp = arith MlirArithOp ∣ scf MlirScfOp` and
whose `Ty` is the shared `CryptoTy`.

The motivation is the **Phase 6d `Cif` deferral**. `scfIf` requires a
`CryptoTy.bit` condition operand, but the source DSL holds the
condition as `sword 1`. Bridging requires an intervening
`arith.cmpi 1 != 0` (technically: we use `extui`-style bit extraction
via `cmpi 1` against a `constant 1 0`) — which lives in
`mlirArithDialect`, not `mlirScfDialect`. A single `Com` whose `Com.var`
can interleave both arith and scf ops is therefore required.

## Design

We use a plain `inductive` rather than a generic `Sum`-like construction
because:

1. The two dialects share `Ty = CryptoTy` exactly, so the sum dialect
   reuses the same `Ty` (no extra `Sum`-of-types machinery needed).
2. The `DialectSignature` and `DialectDenote` instances are a clean
   case-split: `arith op ↦ delegate to MlirArithDialect`,
   `scf op ↦ delegate to MlirScfDialect`.
3. Embedding theorems (`arith_embed_denote_eq`, `scf_embed_denote_eq`)
   close by `rfl` because the denotation is a literal case-split.

This is the same pattern the in-tree `VIR/Core.lean` framework supports
naturally — `Dialect` is just an `Op × Ty` pair, so any inductive over
`Op` with a matching signature/denotation instance is a valid dialect.

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

## Status: the canonical op-union pattern (not a duplicate dialect)

`mlirArithScfDialect` is the **canonical tagged-union pattern** for combining
two dialects that share a `Ty`, not a redundant third dialect. It is a principled
`inductive` union of `mlirArith` + `mlirScf` ops (`arith MlirArithOp ∣ scf
MlirScfOp`) whose signature/denotation simply delegate per-tag to the two
component dialects. The union is *required* for the `Cif` lowering — the
`arith.cmpi 1 != 0` bridge (arith) feeding `scf.if` (scf) must live in a single
`Com` whose `Com.var` chain can interleave both. When a future lowering needs ops
from two `Ty`-compatible dialects in one `Com`, reuse this tagged-union shape
rather than introducing a new combined dialect.
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
inductive MlirArithScfOp where
  | arith (op : MlirArithOp)
  | scf   (op : MlirScfOp)

/-! ## 2. The dialect, signature, denotation -/

/-- The sum dialect: `Op` is the tagged sum, `Ty` is the shared
    `CryptoTy`. -/
@[reducible] def mlirArithScfDialect : Dialect :=
  { Op := MlirArithScfOp, Ty := CryptoTy }

/-- Operation signatures: case-split, delegate to the summand. Marked
    `@[reducible]` so the scf-side embedding's `sig`/`ret` reduces under
    a literal constructor match (needed for the `Expr.mk` shape lemmas
    in `compileCif`). -/
@[reducible] instance instMlirArithScfSignature :
    DialectSignature mlirArithScfDialect where
  sig op := match op with
    | .arith a => DialectSignature.sig (d := mlirArithDialect) a
    | .scf   s => DialectSignature.sig (d := mlirScfDialect)   s
  ret op := match op with
    | .arith a => DialectSignature.ret (d := mlirArithDialect) a
    | .scf   s => DialectSignature.ret (d := mlirScfDialect)   s

/-- Operation denotation: case-split, delegate to the summand. -/
instance instMlirArithScfDenote :
    DialectDenote mlirArithScfDialect where
  denote op := match op with
    | .arith a => fun args => DialectDenote.denote (d := mlirArithDialect) a args
    | .scf   s => fun args => DialectDenote.denote (d := mlirScfDialect)   s args

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
