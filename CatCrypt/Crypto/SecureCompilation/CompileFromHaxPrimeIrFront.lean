/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField
public import HaxLean.AST

/-!
# Front integration: `haxpipeT`-extracted `primeir-hax` `Field` calls → `FieldOp` leaf

`CompileFromHaxPrimeIrField` recognizes a `primeir-hax` `Field` trait method by a
qualified name (`Field.mul`, `Primeir_hax.Field.mul`) and ties the emitted
`Com fieldDialect` leaf to its `ZMod p` operation. This module wires that
recognizer to the **`ImpExpr` surface that `haxpipeT` actually produces** — the
front representation `compileFromHax` / `CallRegistry` / `callInline` consume —
so the recognizer keys on a real extraction head rather than a hypothesized name.

## What `haxpipeT` emits for a `Field` call

Running the crate through the typed extraction path
(`haxpipeT --hax hax_frontend_export.json --emit-certified --name Primeir`, i.e.
`scripts/run_haxpipe.sh` — **not** `cargo hax into lean`) lowers the generic
caller `field_demo<F: Field>(x, y) = x.mul(y).add(x)` to a keyed `ImpExpr`:

```text
field_demo_impExpr : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "y" (.var "y")
    (.app "add" [(.app "mul" [(.var "x"), (.var "y")]), (.var "x")]))
```

The `Field::mul x y` call surfaces as `ImpExpr.app "mul" [.var "x", .var "y"]`
and the enclosing `Field::add` as `ImpExpr.app "add" [<mul>, .var "x"]`. This is
a **keyable named `ImpExpr.app`** — the head string is a resolvable handle — so
the front CAN recognize it (contrast the `cargo hax into lean` backend, which
instead produces the native typeclass-dispatched monadic term
`Field.mul F x y : RustM F`, keyed on no `ImpExpr` head at all).

### The one caveat: `haxpipeT` flattens trait dispatch to the bare method name

`haxpipeT` records the method call by its **bare method name** (`"mul"`,
`"add"`), dropping the trait/receiver qualifier: the head is `"mul"`, not
`"Field.mul"` or `"Primeir_hax.Field.mul"`. Method identity survives (the whole
`primeir-hax` design — nominal recognition by method name) but the trait
qualifier does not. So this front reads the bare head through
`primeirFieldHead`, which restores the `Field.<m>` qualifier under the primeir
recognition context (the caller is a `primeir-hax` `Field` extraction; the
concrete modulus `p` is supplied by that same context, exactly as
`CompileFromHaxPrimeIrField` documents for `p`). The bare name is generic, so
this qualifier restoration is context-directed, not a property of the head alone.

## The emit is the opaque arithmetic leaf, not a word-pipeline compile

A recognized `Field` op emits the `Com fieldDialect` leaf directly (the opaque
arithmetic leaf: the concrete `impl` is `#[cfg(not(hax))]`-gated out, so there is
no callee body to `callInline`, and the leaf is *not* lowered through the
`compileFromHax` jasmin/`BitVec` word pipeline — it denotes into `ZMod p`). The
value-tie therefore reuses `CompileFromHaxPrimeIrField`'s `*_recognized_denote`
facts (the `*Tie` machinery), not `compileFromHax_meets_spec` (which is the
word-pipeline analogue over `BitVec`, a different dialect).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrFront

open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField

/-! ## 1. The `haxpipeT` extraction, reproduced verbatim

The exact `ImpExpr` literal `haxpipeT --emit-certified --name Primeir` writes for
`field_demo` (`primeir-hax/src/lib.rs`), pinned here so the front is keyed on the
real extraction output. -/

/-- `field_demo`'s body as `haxpipeT` extracts it: `add(mul(x, y), x)`, the
    `Field::mul`/`Field::add` calls surfaced as bare-headed `ImpExpr.app`. -/
def fieldDemoImpExpr : ImpExpr :=
  .letBind "x" (.var "x")
   (.letBind "y" (.var "y")
    (.app "add" [(.app "mul" [(.var "x"), (.var "y")]), (.var "x")]))

/-- The `Field::mul x y` call node, exactly as it appears (as the first argument
    of the enclosing `add`) inside `fieldDemoImpExpr`. -/
def fieldMulCall : ImpExpr := .app "mul" [.var "x", .var "y"]

/-- The `mul` call node is literally the first argument of `field_demo`'s `add`
    — pins `fieldMulCall` to the real extraction, so the tie below is about the
    `Field::mul` call `haxpipeT` produced, not a stand-in. -/
theorem fieldMulCall_in_demo :
    fieldDemoImpExpr =
      .letBind "x" (.var "x")
       (.letBind "y" (.var "y")
        (.app "add" [fieldMulCall, (.var "x")])) := rfl

/-! ## 2. Bare-head → qualified-name bridge, then the recognizer

`haxpipeT` drops the trait qualifier, so restore it under the primeir context and
key the existing `recognizeFieldOp` on the result. -/

/-- Restore the `Field.<m>` trait qualifier `haxpipeT` stripped, for the bare
    `Field`-method heads. Any other head is passed through unchanged (so a
    non-`Field` head still fails `recognizeFieldOp`'s fail-closed default). -/
def primeirFieldHead (f : String) : String :=
  if f = "mul" then "Field.mul"
  else if f = "add" then "Field.add"
  else if f = "sub" then "Field.sub"
  else if f = "neg" then "Field.neg"
  else if f = "inv" then "Field.inv"
  else f

/-- Recognize a `haxpipeT`-extracted `Field` call node as a prime-IR `FieldOp` at
    modulus `p`: read the `ImpExpr.app` head, restore its trait qualifier, and
    dispatch through `CompileFromHaxPrimeIrField.recognizeFieldOp`. A non-`app`
    node, or an unrecognized head, is rejected (fail-closed). -/
def recognizePrimeirCall (e : ImpExpr) (p : Nat) : Option FieldOp :=
  match e with
  | .app f _ => recognizeFieldOp (primeirFieldHead f) p
  | _ => none

@[simp] theorem recognize_mulCall (p : Nat) :
    recognizePrimeirCall fieldMulCall p = some (.fMul p) := rfl

/-! ## 3. The pass: recognized binary `Field` call → `Com fieldDialect` leaf

`mul`/`add`/`sub` share the binary leaf shape `[fp p, fp p] → fp p`, so one pass
covers them: recognize the head, emit the matching binary opaque leaf. `neg`/`inv`
have arity 1 (a different `Ctxt`) and are handled by their own `*Leaf`s in
`CompileFromHaxPrimeIrField`; this pass is the binary case, of which `mul` is the
canonical target. -/

/-- Compile a `haxpipeT`-extracted binary `Field` call to its opaque
    `Com fieldDialect` leaf. Returns the leaf carrying the recognized `FieldOp`
    (`fMulLeaf`/`fAddLeaf`/`fSubLeaf`); `none` if the node is not a recognized
    binary `Field` call. -/
def compileFieldBinCall (e : ImpExpr) (p : Nat) :
    Option (Com fieldDialect [FieldTy.fp p, FieldTy.fp p] (FieldTy.fp p)) :=
  match recognizePrimeirCall e p with
  | some (.fMul _) => some (fMulLeaf p)
  | some (.fAdd _) => some (fAddLeaf p)
  | some (.fSub _) => some (fSubLeaf p)
  | _ => none

/-- The pass emits `fMulLeaf` for the extracted `Field::mul` call. -/
theorem compileFieldBinCall_mul (p : Nat) :
    compileFieldBinCall fieldMulCall p = some (fMulLeaf p) := rfl

/-! ## 4. End-to-end value tie for `mul`

The extracted `Field::mul` call, run through the front pass, compiles to a
`Com fieldDialect` whose denotation is `ZMod p` multiplication — routed through
`CompileFromHaxPrimeIrField.primeir_field_mul_recognized_denote` (the `*Tie`
machinery), no fresh compiler proof. -/

/-- **`haxpipeT`'s `Field::mul` call compiles-and-ties, end to end.** The
    `ImpExpr` node `haxpipeT` extracts for `Field::mul x y`
    (`fieldMulCall = .app "mul" [.var "x", .var "y"]`, the first argument of
    `field_demo`'s `add`), run through `compileFieldBinCall`, yields the opaque
    `Com fieldDialect` leaf `fMulLeaf p`, whose denotation on inputs `a b` is the
    `ZMod p` field product `a * b` — the `FieldOp.fMul` operation. Pins the
    extraction node, the front pass, and the value-tie together, reusing the
    `*_recognized_denote` `*Tie` fact rather than re-proving the leaf. -/
theorem primeir_field_mul_compiles_and_ties (p : Nat) (a b : ZMod p) :
    ∃ c, compileFieldBinCall fieldMulCall p = some c ∧
         c.denote (.cons a (.cons b .nil)) = a * b :=
  ⟨fMulLeaf p, rfl, primeir_field_mul_recognized_denote p a b⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrFront
