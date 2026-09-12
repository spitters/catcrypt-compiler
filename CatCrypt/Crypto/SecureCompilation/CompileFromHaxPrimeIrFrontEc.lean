/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrMontMul
public import HaxLean.AST

/-!
# Front integration: `haxpipeT`-extracted `primeir-hax` `EcGroup`/`ModArith` calls → dialect leaf

`CompileFromHaxPrimeIrField` recognizes the `primeir-hax` `EcGroup` point-op
family (`recognizeEcOp` → `ECOp` `padd`/`pdbl`/`psmul`) and the `ModArith`
Montgomery family (`recognizeModArithOp` → `ModArithMontOp`) by a **qualified**
trait-method name, and ties each emitted dialect leaf to the dialect's own
denotation. This module wires those recognizers to the **`ImpExpr` surface that
`haxpipeT` actually produces** — the front representation `compileFromHax` /
`CallRegistry` / `callInline` consume — so the recognizer keys on a real
extraction head. It is the `EcGroup`/`ModArith` analogue of the landed `Field`
pass in `CompileFromHaxPrimeIrFront`.

## What `haxpipeT` emits for an `EcGroup` / `ModArith` call

Running the crate through the typed extraction path
(`haxpipeT --hax hax_frontend_export.json --emit-certified --name Primeir`, i.e.
`scripts/run_haxpipe.sh` — **not** `cargo hax into lean`) lowers the generic
callers `ec_demo`/`ec_double_demo`/`modarith_demo` (`primeir-hax/src/lib.rs`) to
keyed `ImpExpr` literals:

```text
ec_demo_impExpr :=
  .letBind "p" (.var "p") (.letBind "q" (.var "q")
    (.app "point_add" [(.var "p"), (.var "q")]))

ec_double_demo_impExpr :=
  .letBind "p" (.var "p") (.app "point_double" [(.var "p")])

modarith_demo_impExpr :=
  .letBind "a" (.var "a") (.letBind "b" (.var "b")
    (.app "mont_mul" [(.var "a"), (.var "b")]))
```

The `EcGroup::point_add P Q` call surfaces as `ImpExpr.app "point_add" [.var "p",
.var "q"]`, `EcGroup::point_double P` as `ImpExpr.app "point_double" [.var "p"]`,
and `ModArith::mont_mul a b` as `ImpExpr.app "mont_mul" [.var "a", .var "b"]` —
each a **keyable named `ImpExpr.app`** whose head string is a resolvable handle
(contrast `cargo hax into lean`, which produces a typeclass-dispatched monadic
term keyed on no `ImpExpr` head).

### The same bare-head caveat as the `Field` pass

`haxpipeT` records the method call by its **bare method name** (`"point_add"`,
`"point_double"`, `"mont_mul"`), dropping the trait/receiver qualifier: the head
is `"point_add"`, not `"EcGroup.point_add"`. Method identity survives (the whole
`primeir-hax` design — nominal recognition by method name) but the trait
qualifier does not. So this front reads the bare head through `primeirEcHead` /
`primeirModArithHead`, which restore the `EcGroup.<m>` / `ModArith.<m>` qualifier
under the primeir recognition context (the caller is a `primeir-hax` extraction;
the prime `p` / curve `C` / Montgomery parameters `(N, R, N')` come from that
same context). The bare name is generic, so the restoration is context-directed.

## The emit is the opaque arithmetic leaf, not a word-pipeline compile

A recognized group op emits the `Com ecDialect` leaf directly (the opaque
arithmetic leaf: the concrete `impl` is `#[cfg(not(hax))]`-gated out, so there is
no callee body to `callInline`). The value-tie reuses
`CompileFromHaxPrimeIrField`'s `*_recognized_denote` facts (the group law
`ECParams.add`), not `compileFromHax_meets_spec`.

## The binary `ModArith::mont_mul` call

The extracted `ModArith::mont_mul` call is **binary**
(`.app "mont_mul" [.var "a", .var "b"]`), and the single `recognizeModArithOp`
table (`CompileFromHaxPrimeIrField`) keys it to the two-operand `.montMul` op.
So the `ModArith` front recognizer (§5) restores the qualifier and dispatches,
and the extracted binary `mont_mul` head recognizes and emits its dialect leaf
(§6), delivering an end-to-end value-tie alongside `EcGroup::point_add` (and
`point_double`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrFrontEc

open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
  (ECOp ECTy ecDialect ecDenote ECParams ECPoint EcCurvePoint ecCurvePoint_add_val)

/-! ## 1. The `haxpipeT` extraction, reproduced verbatim

The exact `ImpExpr` literals `haxpipeT --emit-certified --name Primeir` writes
for `ec_demo` / `ec_double_demo` (`primeir-hax/src/lib.rs`), pinned here so the
front is keyed on the real extraction output. -/

/-- `ec_demo`'s body as `haxpipeT` extracts it: `point_add(p, q)`, the
    `EcGroup::point_add` call surfaced as a bare-headed `ImpExpr.app`. -/
def ecDemoImpExpr : ImpExpr :=
  .letBind "p" (.var "p")
   (.letBind "q" (.var "q")
    (.app "point_add" [(.var "p"), (.var "q")]))

/-- The `EcGroup::point_add P Q` call node, exactly as it appears (as the body of
    the enclosing `letBind`s) inside `ecDemoImpExpr`. -/
def ecPointAddCall : ImpExpr := .app "point_add" [.var "p", .var "q"]

/-- The `point_add` call node is literally the body of `ec_demo`'s `letBind`s —
    pins `ecPointAddCall` to the real extraction, so the tie below is about the
    `EcGroup::point_add` call `haxpipeT` produced, not a stand-in. -/
theorem ecPointAddCall_in_demo :
    ecDemoImpExpr =
      .letBind "p" (.var "p")
       (.letBind "q" (.var "q") ecPointAddCall) := rfl

/-- `ec_double_demo`'s body as `haxpipeT` extracts it: `point_double(p)`. -/
def ecDoubleDemoImpExpr : ImpExpr :=
  .letBind "p" (.var "p") (.app "point_double" [(.var "p")])

/-- The `EcGroup::point_double P` call node, exactly as it appears inside
    `ecDoubleDemoImpExpr`. -/
def ecPointDoubleCall : ImpExpr := .app "point_double" [.var "p"]

/-- The `point_double` call node is literally the body of `ec_double_demo`. -/
theorem ecPointDoubleCall_in_demo :
    ecDoubleDemoImpExpr = .letBind "p" (.var "p") ecPointDoubleCall := rfl

/-! ## 2. Bare-head → qualified-name bridge, then the recognizer

`haxpipeT` drops the trait qualifier, so restore it under the primeir context and
key the existing `recognizeEcOp` on the result. -/

/-- Restore the `EcGroup.<m>` trait qualifier `haxpipeT` stripped, for the bare
    `EcGroup`-method heads. Any other head is passed through unchanged (so a
    non-`EcGroup` head still fails `recognizeEcOp`'s fail-closed default). -/
def primeirEcHead (f : String) : String :=
  if f = "point_add" then "EcGroup.point_add"
  else if f = "point_double" then "EcGroup.point_double"
  else if f = "scalar_mul" then "EcGroup.scalar_mul"
  else f

/-- Recognize a `haxpipeT`-extracted `EcGroup` call node as a prime-IR `ECOp` at
    prime `p` and curve `C`: read the `ImpExpr.app` head, restore its trait
    qualifier, and dispatch through
    `CompileFromHaxPrimeIrField.recognizeEcOp`. A non-`app` node, or an
    unrecognized head, is rejected (fail-closed). -/
def recognizePrimeirEcCall (e : ImpExpr) (p : Nat) (C : ECParams p) : Option ECOp :=
  match e with
  | .app f _ => recognizeEcOp (primeirEcHead f) p C
  | _ => none

@[simp] theorem recognize_pointAddCall (p : Nat) (C : ECParams p) :
    recognizePrimeirEcCall ecPointAddCall p C = some (.padd p C) := rfl

@[simp] theorem recognize_pointDoubleCall (p : Nat) (C : ECParams p) :
    recognizePrimeirEcCall ecPointDoubleCall p C = some (.pdbl p C) := rfl

/-! ## 3. The pass: recognized `EcGroup` call → `Com ecDialect` leaf

`point_add` is binary (`[point p, point p] → point p`); `point_double` is unary
(`[point p] → point p`). Their `Ctxt`s differ, so each has its own pass, each
emitting the matching opaque group-law leaf from `CompileFromHaxPrimeIrField`. -/

/-- Compile a `haxpipeT`-extracted `EcGroup::point_add` call to its opaque
    `Com ecDialect` leaf `pAddLeaf`. `none` if the node is not a recognized
    `point_add` call. -/
def compileEcPointAdd (e : ImpExpr) (p : Nat) (C : ECParams p) :
    Option (Com ecDialect [ECTy.point p, ECTy.point p] (ECTy.point p)) :=
  match recognizePrimeirEcCall e p C with
  | some (.padd _ _) => some (pAddLeaf p C)
  | _ => none

/-- Compile a `haxpipeT`-extracted `EcGroup::point_double` call to its opaque
    `Com ecDialect` leaf `pDblLeaf`. `none` if the node is not a recognized
    `point_double` call. -/
def compileEcPointDouble (e : ImpExpr) (p : Nat) (C : ECParams p) :
    Option (Com ecDialect [ECTy.point p] (ECTy.point p)) :=
  match recognizePrimeirEcCall e p C with
  | some (.pdbl _ _) => some (pDblLeaf p C)
  | _ => none

/-- The pass emits `pAddLeaf` for the extracted `EcGroup::point_add` call. -/
theorem compileEcPointAdd_add (p : Nat) (C : ECParams p) :
    compileEcPointAdd ecPointAddCall p C = some (pAddLeaf p C) := rfl

/-- The pass emits `pDblLeaf` for the extracted `EcGroup::point_double` call. -/
theorem compileEcPointDouble_double (p : Nat) (C : ECParams p) :
    compileEcPointDouble ecPointDoubleCall p C = some (pDblLeaf p C) := rfl

/-! ## 4. End-to-end value tie for `point_add` (and `point_double`)

The extracted `EcGroup::point_add` call, run through the front pass, compiles to
a `Com ecDialect` whose denotation is the dialect group law `ECParams.add` —
routed through `CompileFromHaxPrimeIrField.primeir_ecgroup_point_add_recognized_denote`
(the value-tie machinery), no fresh compiler proof. -/

/-- **`haxpipeT`'s `EcGroup::point_add` call compiles-and-ties, end to end.** The
    `ImpExpr` node `haxpipeT` extracts for `EcGroup::point_add P Q`
    (`ecPointAddCall = .app "point_add" [.var "p", .var "q"]`, the body of
    `ec_demo`), run through `compileEcPointAdd`, yields the opaque `Com ecDialect`
    leaf `pAddLeaf p C`, whose denotation on inputs `P Q` is the dialect
    short-Weierstrass chord/tangent group add `C.add P Q` — the `ECOp.padd`
    operation. Pins the extraction node, the front pass, and the value-tie
    together, reusing the `*_recognized_denote` fact rather than re-proving the
    leaf. -/
theorem primeir_ecgroup_point_add_compiles_and_ties (p : Nat) (C : ECParams p)
    (P Q : ECPoint p) :
    ∃ c, compileEcPointAdd ecPointAddCall p C = some c ∧
         c.denote (.cons P (.cons Q .nil)) = C.add P Q :=
  ⟨pAddLeaf p C, rfl, primeir_ecgroup_point_add_recognized_denote p C P Q⟩

/-- **The compiled `point_add` ties to the group law on on-curve
    points.** For on-curve points `a b : EcCurvePoint C`, the compiled leaf on
    their underlying `ECPoint` values denotes to `(a + b).val` — the
    Mathlib-transported Weierstrass point addition (`EcPointGroup`'s
    `AddCommGroup`), reusing `primeir_ecgroup_point_add_recognized_oncurve`. -/
theorem primeir_ecgroup_point_add_compiles_and_ties_oncurve (p : Nat) [Fact p.Prime]
    (C : ECParams p) (a b : EcCurvePoint C) :
    ∃ c, compileEcPointAdd ecPointAddCall p C = some c ∧
         c.denote (.cons a.val (.cons b.val .nil)) = (a + b).val :=
  ⟨pAddLeaf p C, rfl, primeir_ecgroup_point_add_recognized_oncurve p C a b⟩

/-- **`haxpipeT`'s `EcGroup::point_double` call compiles-and-ties, end to end.**
    The extracted `point_double` node, run through `compileEcPointDouble`, yields
    `pDblLeaf p C`, whose denotation on input `P` is the group double `C.add P P`
    — the `ECOp.pdbl` operation (`EllipticCurveDialect.pdbl_denote`). -/
theorem primeir_ecgroup_point_double_compiles_and_ties (p : Nat) (C : ECParams p)
    (P : ECPoint p) :
    ∃ c, compileEcPointDouble ecPointDoubleCall p C = some c ∧
         c.denote (.cons P .nil) = C.add P P :=
  ⟨pDblLeaf p C, rfl, rfl⟩

/-! ## 5. The `ModArith` front recognizer

The `ModArith` bare-head → qualified bridge and recognizer mirror the `EcGroup`
ones. The single `recognizeModArithOp` table (`CompileFromHaxPrimeIrField`) keys
the whole `ModArith` op-family — the unary `to_mont`/`from_mont`, the
fused-diagonal `mont_square`, and the binary `mont_mul` (the two-operand
`.montMul` op) — so the extracted binary `mont_mul` head recognizes through the
same unified path. -/

/-- `modarith_demo`'s body as `haxpipeT` extracts it: `mont_mul(a, b)`. -/
def modarithDemoImpExpr : ImpExpr :=
  .letBind "a" (.var "a")
   (.letBind "b" (.var "b")
    (.app "mont_mul" [(.var "a"), (.var "b")]))

/-- The `ModArith::mont_mul a b` call node, exactly as it appears inside
    `modarithDemoImpExpr`. Binary. -/
def modarithMontMulCall : ImpExpr := .app "mont_mul" [.var "a", .var "b"]

/-- The `mont_mul` call node is literally the body of `modarith_demo`. -/
theorem modarithMontMulCall_in_demo :
    modarithDemoImpExpr =
      .letBind "a" (.var "a")
       (.letBind "b" (.var "b") modarithMontMulCall) := rfl

/-- Restore the `ModArith.<m>` trait qualifier `haxpipeT` stripped, for the bare
    `ModArith`-method heads. Any other head is passed through unchanged. -/
def primeirModArithHead (f : String) : String :=
  if f = "to_mont" then "ModArith.to_mont"
  else if f = "from_mont" then "ModArith.from_mont"
  else if f = "mont_square" then "ModArith.mont_square"
  else if f = "mont_mul" then "ModArith.mont_mul"
  else f

/-- Recognize a `haxpipeT`-extracted `ModArith` call node as a prime-IR
    `ModArithMontOp` at Montgomery parameters `(N, R, N')`: read the head, restore
    the qualifier, dispatch through
    `CompileFromHaxPrimeIrField.recognizeModArithOp`. Fail-closed. -/
def recognizePrimeirModArithCall (e : ImpExpr) (N R N' : ℤ) :
    Option ModArithMontOps.ModArithMontOp :=
  match e with
  | .app f _ => recognizeModArithOp (primeirModArithHead f) N R N'
  | _ => none

/-- **The extracted binary `ModArith::mont_mul` call recognizes through the
    unified recognizer.** The restored `ModArith.mont_mul` head is keyed by the
    single `recognizeModArithOp` table to the two-operand `.montMul N R N'` op, so
    the front recognizes the extracted binary `mont_mul` on the same path as the
    unary conversions and the fused-diagonal `mont_square`. -/
theorem recognize_montMulCall_ok (N R N' : ℤ) :
    recognizePrimeirModArithCall modarithMontMulCall N R N' = some (.montMul N R N') := rfl

/-! ## 6. The binary `mont_mul` emit leaf and its end-to-end tie

The extracted `mont_mul` call recognizes through the unified
`recognizePrimeirModArithCall` (§5) to the two-operand `.montMul` op. The emit
leaf `montMulLeaf` and its value-tie come from `CompileFromHaxPrimeIrMontMul` (the
Montgomery-multiply emit leaf); this section wires them onto the extracted call,
so the extracted binary `mont_mul` compiles-and-ties end to end. -/

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrMontMul
  (montMulLeaf primeir_modarith_mont_mul_recognized_denote)
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric (montMul)

/-- The `mont_mul` front pass: a recognized binary `mont_mul` call emits the
    `montMulLeaf` `Com modArithMontDialect` leaf, dispatching through the unified
    `recognizePrimeirModArithCall`. -/
def compileMontMul (e : ImpExpr) (N R N' : ℤ) :=
  match recognizePrimeirModArithCall e N R N' with
  | some (.montMul _ _ _) => some (montMulLeaf N R N')
  | _ => none

/-- The pass emits `montMulLeaf` for the extracted `ModArith::mont_mul` call. -/
theorem compileMontMul_mul (N R N' : ℤ) :
    compileMontMul modarithMontMulCall N R N' = some (montMulLeaf N R N') := rfl

/-- **`haxpipeT`'s `ModArith::mont_mul` call compiles-and-ties, end to end.** The
    extracted binary `mont_mul` node, run through `compileMontMul`, yields
    `montMulLeaf N R N'`, whose denotation on `(a, b)` is the dialect's binary
    Montgomery multiply `montMul N R N' a b` — reusing
    `primeir_modarith_mont_mul_recognized_denote`. The binary `mont_mul` reaches a
    dialect leaf tied by value through the unified recognizer. -/
theorem primeir_modarith_mont_mul_compiles_and_ties (N R N' a b : ℤ) :
    ∃ c, compileMontMul modarithMontMulCall N R N' = some c ∧
         c.denote (.cons a (.cons b .nil)) = montMul N R N' a b :=
  ⟨montMulLeaf N R N', rfl, primeir_modarith_mont_mul_recognized_denote N R N' a b⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrFrontEc
