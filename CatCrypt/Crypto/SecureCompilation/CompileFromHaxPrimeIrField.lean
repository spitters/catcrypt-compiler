/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontOps
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.EcConvertOps
public import CatCrypt.Crypto.SecureCompilation.VIR.EcPointGroup
public import Mathlib.Data.ZMod.Basic

/-!
# Front recognizer: `primeir-hax` trait methods → prime-IR dialect ops

Recognizer tables mapping the `primeir-hax` (`primeir-hax/src/lib.rs`) trait
surfaces — `Field`, `ModArith`, `EcGroup` — to the prime-IR correspondence
dialects, each keyed **nominally** on the resolved trait-method name. Sections:

* §1–3: the `Field` op-family → `FieldOp` (`VIR/FieldDialect.lean`).
* §4: the `ModArith` op-family → `modArithMontDialect` (`VIR/ModArithMontOps.lean`).
* §5: the `EcGroup` point-op family → `ecDialect`'s `ECOp` group ops
  (`VIR/EllipticCurveDialect.lean`), plus `to_affine` → `ecConvertDialect`
  (`VIR/EcConvertOps.lean`).

Each table is fail-closed (`Option`, `none` on any unrecognized head) and each
recognized op is tied *by value* to the dialect's own denotation / agreement
lemmas — no fresh compiler proof, no new dialect op.

## §1–3 — the `Field` op-family

The `primeir-hax` crate (`primeir-hax/src/lib.rs`) exposes a `Field` trait whose
method names are chosen to align **nominally** with the prime-IR `FieldOp`
dialect (`VIR/FieldDialect.lean`): `mul`/`add`/`sub`/`neg`/`inv`. A generic
caller `field_demo` exercises those methods, and `cargo hax into lean` extracts
the call site (`primeir-hax/proofs/lean/extraction/Primeir_hax.lean`) as

```text
field_demo (F : Type) [Field F] (x y : F) : RustM F :=
  (Field.add F (← (Field.mul F x y)) x)
```

i.e. a `Field::mul` call surfaces as the typeclass-method application
`Field.mul F x y` (resolved name `Primeir_hax.Field.mul`), in `RustM`.

This module is the recognizer that maps each such resolved `Field` method name
to its `FieldOp`, emitting the corresponding op as a single-op `Com fieldDialect`
leaf — the **opaque arithmetic leaf**: there is no body to inline (the concrete
`impl` is `#[cfg(not(hax))]`-gated out of the extraction), the leaf's realization
comes from the owned/verified kernel underneath, tied *by value* through
`FieldOp.denote`. This generalizes the per-primitive `*Tie` files: instead of
tying one hand-picked emitted kernel to `ZMod p`, it recognizes the whole `Field`
op-family nominally and ties each recognized op to its `ZMod p` field operation.

## Recognition table

| resolved method name       | `FieldOp` (at modulus `p`) | `ZMod p` op |
|----------------------------|----------------------------|-------------|
| `Primeir_hax.Field.mul`    | `FieldOp.fMul p`           | `a * b`     |
| `Primeir_hax.Field.add`    | `FieldOp.fAdd p`           | `a + b`     |
| `Primeir_hax.Field.sub`    | `FieldOp.fSub p`           | `a - b`     |
| `Primeir_hax.Field.neg`    | `FieldOp.fNeg p`           | `-a`        |
| `Primeir_hax.Field.inv`    | `FieldOp.fInv p`           | `a⁻¹`       |

The modulus `p` is not present in the trait extraction (the trait is generic over
`F`); it is supplied by the recognition context — the concrete field instance the
opaque leaf realizes (e.g. `2^255 - 19` for the crate's reference `Fp25519`).

## On the extracted call shape and the ImpExpr front

The extracted call is a **typeclass-method application in `RustM`**
(`Primeir_hax.Field.mul F x y`), not an `ImpExpr.app "path" [x, y]` node: the hax
Lean backend produces native Lean typeclass-dispatched monadic terms, whereas the
`CompileFromHax` / `callInline` / `CallRegistry` front keys recognition on an
`ImpExpr.app` head string. So the recognizer keys on the **resolved trait-method
name** — the nominal handle the crate is designed around ("recognize a call
nominally by trait + method name") — rather than on an `ImpExpr` head. This is
the `*Tie`-style value-tie generalized to a name-keyed op-family table, not a
`callInline` inlining pass (there is no callee body to inline).

## Value tie

`primeir_field_mul_recognized_denote` proves the tie for `mul` (and the analogous
`*_denote` lemmas cover `add`/`sub`/`neg`/`inv`): the emitted `Com fieldDialect`
leaf for the recognized op denotes to the corresponding `ZMod p` field operation,
reusing `FieldDialect`'s op denotation (`fMul_denote`, etc.) — no fresh compiler
proof.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-! ## 1. The recognition table

Keyed on the resolved `Field` trait-method name. Both the fully-qualified
Lean-backend name (`Primeir_hax.Field.<m>`) and the bare class-method name
(`Field.<m>`) are accepted, so a caller that has already stripped the module
prefix still recognizes. -/

/-- Recognize a resolved `primeir-hax` `Field` trait-method name as the prime-IR
    `FieldOp` at modulus `p`. Returns `none` for any non-`Field` head — the
    fail-closed default, so an unrecognized call never silently produces an op. -/
def recognizeFieldOp (name : String) (p : Nat) : Option FieldOp :=
  if name = "Primeir_hax.Field.mul" ∨ name = "Field.mul" then some (.fMul p)
  else if name = "Primeir_hax.Field.add" ∨ name = "Field.add" then some (.fAdd p)
  else if name = "Primeir_hax.Field.sub" ∨ name = "Field.sub" then some (.fSub p)
  else if name = "Primeir_hax.Field.neg" ∨ name = "Field.neg" then some (.fNeg p)
  else if name = "Primeir_hax.Field.inv" ∨ name = "Field.inv" then some (.fInv p)
  else none

@[simp] theorem recognize_mul (p : Nat) :
    recognizeFieldOp "Primeir_hax.Field.mul" p = some (.fMul p) := rfl
@[simp] theorem recognize_add (p : Nat) :
    recognizeFieldOp "Primeir_hax.Field.add" p = some (.fAdd p) := rfl
@[simp] theorem recognize_sub (p : Nat) :
    recognizeFieldOp "Primeir_hax.Field.sub" p = some (.fSub p) := rfl
@[simp] theorem recognize_neg (p : Nat) :
    recognizeFieldOp "Primeir_hax.Field.neg" p = some (.fNeg p) := rfl
@[simp] theorem recognize_inv (p : Nat) :
    recognizeFieldOp "Primeir_hax.Field.inv" p = some (.fInv p) := rfl

/-- An unrecognized head is rejected (fail-closed). -/
theorem recognize_unknown (p : Nat) :
    recognizeFieldOp "Primeir_hax.EcGroup.point_add" p = none := rfl

/-! ## 2. Emit: a recognized op as a single-op `Com fieldDialect` leaf

Each recognized op emits a one-`var` `Com fieldDialect`: the op applied to the
context variables, returning the result. The opaque arithmetic leaf — no body is
inlined (there is none). Binary ops take `[fp p, fp p]`, unary ops `[fp p]`,
mirroring `smokeProg` in `FieldDialect.lean`. -/

/-- The `mul` emit leaf: `let c = fMul a b; ret c` over `[fp p, fp p]`. -/
def fMulLeaf (p : Nat) : Com fieldDialect [FieldTy.fp p, FieldTy.fp p] (FieldTy.fp p) :=
  .var (.mk (.fMul p) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `add` emit leaf. -/
def fAddLeaf (p : Nat) : Com fieldDialect [FieldTy.fp p, FieldTy.fp p] (FieldTy.fp p) :=
  .var (.mk (.fAdd p) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `sub` emit leaf. -/
def fSubLeaf (p : Nat) : Com fieldDialect [FieldTy.fp p, FieldTy.fp p] (FieldTy.fp p) :=
  .var (.mk (.fSub p) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `neg` emit leaf: `let c = fNeg a; ret c` over `[fp p]`. -/
def fNegLeaf (p : Nat) : Com fieldDialect [FieldTy.fp p] (FieldTy.fp p) :=
  .var (.mk (.fNeg p) rfl (.cons .here .nil)) (.ret .here)

/-- The `inv` emit leaf. -/
def fInvLeaf (p : Nat) : Com fieldDialect [FieldTy.fp p] (FieldTy.fp p) :=
  .var (.mk (.fInv p) rfl (.cons .here .nil)) (.ret .here)

/-! ## 3. The value tie

The emitted leaf for each recognized op denotes to the corresponding `ZMod p`
field operation, reusing `FieldDialect`'s op-denotation facts. Stated once per
op; the `mul` tie is the canonical target. -/

/-- **The recognized `Field::mul` call ties to `ZMod p` multiplication.** The op
    that `recognizeFieldOp "Primeir_hax.Field.mul" p` returns (`FieldOp.fMul p`),
    emitted as the `fMulLeaf` `Com fieldDialect` leaf, denotes on inputs `a b` to
    the `ZMod p` field product `a * b` — the value-tie of the recognized call,
    routed through `FieldDialect`'s `fMul_denote` (no fresh compiler proof). -/
theorem primeir_field_mul_recognized_denote (p : Nat) (a b : ZMod p) :
    (fMulLeaf p).denote (.cons a (.cons b .nil)) = a * b := by
  show fieldDenote.denote (.fMul p) (.cons a (.cons b .nil)) = a * b
  exact fMul_denote a b

/-- The recognized `Field::add` call ties to `ZMod p` addition. -/
theorem primeir_field_add_recognized_denote (p : Nat) (a b : ZMod p) :
    (fAddLeaf p).denote (.cons a (.cons b .nil)) = a + b := rfl

/-- The recognized `Field::sub` call ties to `ZMod p` subtraction. -/
theorem primeir_field_sub_recognized_denote (p : Nat) (a b : ZMod p) :
    (fSubLeaf p).denote (.cons a (.cons b .nil)) = a - b := rfl

/-- The recognized `Field::neg` call ties to `ZMod p` negation. -/
theorem primeir_field_neg_recognized_denote (p : Nat) (a : ZMod p) :
    (fNegLeaf p).denote (.cons a .nil) = -a := rfl

/-- The recognized `Field::inv` call ties to `ZMod p` inversion. -/
theorem primeir_field_inv_recognized_denote (p : Nat) (a : ZMod p) :
    (fInvLeaf p).denote (.cons a .nil) = a⁻¹ := by
  show fieldDenote.denote (.fInv p) (.cons a .nil) = a⁻¹
  exact fInv_denote a

/-- **Recognition + emit + tie, end to end for `mul`.** Whenever the recognizer
    accepts the resolved `Field::mul` name (returning `FieldOp.fMul p`), the leaf
    carrying that op denotes to the `ZMod p` product. Pins the recognizer table
    and the value-tie together. -/
theorem primeir_field_mul_recognized (p : Nat) (a b : ZMod p) :
    recognizeFieldOp "Primeir_hax.Field.mul" p = some (.fMul p) ∧
    (fMulLeaf p).denote (.cons a (.cons b .nil)) = a * b :=
  ⟨rfl, primeir_field_mul_recognized_denote p a b⟩

/-! # §4 — the `ModArith` op-family → `modArithMontDialect`

The `primeir-hax` `ModArith` trait (`primeir-hax/src/lib.rs`; extracted class
`Primeir_hax.ModArith`) exposes the Montgomery-domain methods `to_mont`,
`from_mont`, `mont_mul`, named after the `modArithMontDialect`
(`VIR/ModArithMontOps.lean`, prime-ir's `mod_arith` op-family). This section
recognizes each resolved method name as its `ModArithMontOp` at Montgomery
parameters `(N, R, N')` (`N` the modulus, `R` the radix, `N'` the constant with
`N · N' ≡ -1 (mod R)`), emits it as a single-op `Com modArithMontDialect` leaf,
and ties the leaf to the dialect's own denotation (`ModArithMontOps`' agreement
lemmas — no fresh Montgomery reduction). `recognizeModArithOp` is the single
recognizer for the whole `ModArith` op-family, including the binary `mont_mul`.

## Recognition table

| resolved method name             | `ModArithMontOp` (at `N R N'`) | denotes to             |
|----------------------------------|--------------------------------|------------------------|
| `Primeir_hax.ModArith.to_mont`   | `.toMont N R N'`               | `x · R`                |
| `Primeir_hax.ModArith.from_mont` | `.fromMont N R N'`             | `redc N R N' x`        |
| `Primeir_hax.ModArith.mont_square` | `.montSquare N R N'`         | `montMul N R N' x x`   |
| `Primeir_hax.ModArith.mont_mul`  | `.montMul N R N'`              | `montMul N R N' a b`   |

The crate trait method `mont_mul` is **binary** (`(a, b) ↦ a·b·R⁻¹ mod p`), and
`ModArithMontOp` carries it as the two-operand `montMul` constructor
(`VIR/ModArithMontOps.lean`); the unary fused `montSquare` (`= montMul N R N' x x`,
the diagonal) is its `a = b` specialization. The single `recognizeModArithOp`
table keys both — the domain conversions and both Montgomery multiplies — so one
recognizer handles every `ModArith` op. The binary `mont_mul` emit leaf and its
value-tie live in `CompileFromHaxPrimeIrMontMul` (the emit leaf `montMulLeaf`);
this section carries the unary conversions and the fused-square value-tie. -/

open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric (montMul redc)

/-- Recognize a resolved `primeir-hax` `ModArith` trait-method name as its
    `ModArithMontOp` at Montgomery parameters `(N, R, N')`. Fail-closed: any
    non-`ModArith` head returns `none`. The single recognizer for the whole
    `ModArith` op-family: the unary domain-conversion methods `to_mont`/`from_mont`,
    the fused-diagonal `mont_square`, and the binary Montgomery multiply
    `mont_mul` (the two-operand `.montMul` constructor). Both the fully-qualified
    `Primeir_hax.ModArith.<m>` and the bare `ModArith.<m>` forms are accepted. -/
def recognizeModArithOp (name : String) (N R N' : ℤ) :
    Option ModArithMontOps.ModArithMontOp :=
  if name = "Primeir_hax.ModArith.to_mont" ∨ name = "ModArith.to_mont" then
    some (.toMont N R N')
  else if name = "Primeir_hax.ModArith.from_mont" ∨ name = "ModArith.from_mont" then
    some (.fromMont N R N')
  else if name = "Primeir_hax.ModArith.mont_square" ∨ name = "ModArith.mont_square" then
    some (.montSquare N R N')
  else if name = "Primeir_hax.ModArith.mont_mul" ∨ name = "ModArith.mont_mul" then
    some (.montMul N R N')
  else none

@[simp] theorem recognizeModArith_to_mont (N R N' : ℤ) :
    recognizeModArithOp "Primeir_hax.ModArith.to_mont" N R N' = some (.toMont N R N') := rfl
@[simp] theorem recognizeModArith_from_mont (N R N' : ℤ) :
    recognizeModArithOp "Primeir_hax.ModArith.from_mont" N R N' = some (.fromMont N R N') := rfl
@[simp] theorem recognizeModArith_mont_square (N R N' : ℤ) :
    recognizeModArithOp "Primeir_hax.ModArith.mont_square" N R N'
      = some (.montSquare N R N') := rfl
@[simp] theorem recognizeModArith_mont_mul (N R N' : ℤ) :
    recognizeModArithOp "Primeir_hax.ModArith.mont_mul" N R N'
      = some (.montMul N R N') := rfl

/-- An unrecognized head is rejected (fail-closed): a non-`ModArith` method name
    returns `none`. -/
theorem recognizeModArith_unknown (N R N' : ℤ) :
    recognizeModArithOp "Primeir_hax.EcGroup.point_add" N R N' = none := rfl

/-! ## Emit: a recognized op as a single-op `Com modArithMontDialect` leaf

Each op is unary `residue → residue` at the same `(N, R, N')`, so each leaf takes
`[residue N R N']` and returns `residue N R N'`, mirroring `fNegLeaf`/`fInvLeaf`. -/

/-- The `to_mont` emit leaf: `let c = toMont x; ret c` over `[residue N R N']`. -/
def toMontLeaf (N R N' : ℤ) :
    Com ModArithMontOps.modArithMontDialect
      [ModArithMontOps.ModArithMontTy.residue N R N']
      (ModArithMontOps.ModArithMontTy.residue N R N') :=
  .var (.mk (.toMont N R N') rfl (.cons .here .nil)) (.ret .here)

/-- The `from_mont` emit leaf. -/
def fromMontLeaf (N R N' : ℤ) :
    Com ModArithMontOps.modArithMontDialect
      [ModArithMontOps.ModArithMontTy.residue N R N']
      (ModArithMontOps.ModArithMontTy.residue N R N') :=
  .var (.mk (.fromMont N R N') rfl (.cons .here .nil)) (.ret .here)

/-- The `mont_square` (fused Montgomery multiply) emit leaf. -/
def montSquareLeaf (N R N' : ℤ) :
    Com ModArithMontOps.modArithMontDialect
      [ModArithMontOps.ModArithMontTy.residue N R N']
      (ModArithMontOps.ModArithMontTy.residue N R N') :=
  .var (.mk (.montSquare N R N') rfl (.cons .here .nil)) (.ret .here)

/-! ## The value ties

Each recognized-op leaf denotes to the dialect's own Montgomery map, reusing the
`ModArithMontOps` denotation lemmas. -/

/-- The recognized `ModArith::to_mont` call ties to `x ↦ x · R` (enter the
    Montgomery domain), routed through `ModArithMontOps.toMont_denote`. -/
theorem primeir_modarith_to_mont_recognized_denote (N R N' x : ℤ) :
    (toMontLeaf N R N').denote (.cons x .nil) = x * R := by
  show ModArithMontOps.modArithMontDenote.denote (.toMont N R N') (.cons x .nil) = x * R
  exact ModArithMontOps.toMont_denote N R N' x

/-- The recognized `ModArith::from_mont` call ties to `redc N R N'` (leave the
    Montgomery domain), routed through `ModArithMontOps.fromMont_denote`. -/
theorem primeir_modarith_from_mont_recognized_denote (N R N' x : ℤ) :
    (fromMontLeaf N R N').denote (.cons x .nil) = redc N R N' x := by
  show ModArithMontOps.modArithMontDenote.denote (.fromMont N R N') (.cons x .nil)
    = redc N R N' x
  exact ModArithMontOps.fromMont_denote N R N' x

/-- **The recognized Montgomery-multiply call ties to the dialect's Montgomery
    multiply.** The op that `recognizeModArithOp` returns for the `mont_square`
    name (`.montSquare N R N'`), emitted as `montSquareLeaf`, denotes on input `x`
    to `montMul N R N' x x` — the fused Montgomery multiply the dialect defines,
    routed through `ModArithMontOps.montSquare_denote` (no fresh Montgomery
    reduction). This is the Montgomery-multiply value-tie; the crate's binary
    `mont_mul` maps to this diagonal (see the §4 arity-gap note). -/
theorem primeir_modarith_mont_square_recognized_denote (N R N' x : ℤ) :
    (montSquareLeaf N R N').denote (.cons x .nil) = montMul N R N' x x := by
  show ModArithMontOps.modArithMontDenote.denote (.montSquare N R N') (.cons x .nil)
    = montMul N R N' x x
  exact ModArithMontOps.montSquare_denote N R N' x

/-- **Recognition + emit + tie, end to end for the Montgomery multiply.** The
    recognizer accepts the `mont_square` name (returning `.montSquare N R N'`) and
    the leaf carrying that op denotes to `montMul N R N' x x`. -/
theorem primeir_modarith_mont_square_recognized (N R N' x : ℤ) :
    recognizeModArithOp "Primeir_hax.ModArith.mont_square" N R N'
        = some (.montSquare N R N') ∧
    (montSquareLeaf N R N').denote (.cons x .nil) = montMul N R N' x x :=
  ⟨rfl, primeir_modarith_mont_square_recognized_denote N R N' x⟩

/-! # §5 — the `EcGroup` point-op family → `ECOp` / `ecConvertDialect`

The `primeir-hax` `EcGroup` trait (`primeir-hax/src/lib.rs`; extracted class
`Primeir_hax.EcGroup`) exposes `point_add`, `point_double`, `scalar_mul`, and
`to_affine`, named after the `ecDialect` `ECOp` group ops
(`VIR/EllipticCurveDialect.lean`) and — for `to_affine` — the sibling
`ecConvertDialect` (`VIR/EcConvertOps.lean`).

## Recognition tables

The three group ops recognize into `ECOp` (a `recognizeEcOp` table over
`ecDialect`); `to_affine` recognizes into `EcConvertOp` (a separate
`recognizeEcToAffineOp` table, since it is a distinct op-type living in the
`ecConvertDialect`):

| resolved method name              | dialect op                  | denotes to        |
|-----------------------------------|-----------------------------|-------------------|
| `Primeir_hax.EcGroup.point_add`   | `ECOp.padd p C`             | `C.add P Q`       |
| `Primeir_hax.EcGroup.point_double`| `ECOp.pdbl p C`             | `C.add P P`       |
| `Primeir_hax.EcGroup.scalar_mul`  | `ECOp.psmul p C true`       | `C.smul k.val P`  |
| `Primeir_hax.EcGroup.to_affine`   | `EcConvertOp.jacobianToAffine p` | `(X·Z⁻²,Y·Z⁻³)` |

`scalar_mul`'s `Scalar` is **secret**: the recognized op maps to
`ECOp.psmul p C true`, the constant-time ladder realisation the trait mandates
(`ct = true`). Recognizing the `Scalar` newtype as secret (hax-lean
`Secrecy.isSecretInteger`, feeding `cmdCT`'s fail-closed check) is a separate,
deferred piece — out of scope for this op-recognition table. -/

open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
  (ECOp ECTy ecDialect ecDenote ECParams ECPoint EcCurvePoint ecCurvePoint_add_val)

/-- Recognize a resolved `primeir-hax` `EcGroup` point-op name as its `ECOp` at
    prime `p` and curve `C`. Fail-closed. `point_add`/`point_double` are the
    group-law ops; `scalar_mul` maps to the CT ladder `psmul … true` (the
    secret-`Scalar` recognition is deferred — see §5). `to_affine` is a distinct
    op-type (`EcConvertOp`) and has its own table `recognizeEcToAffineOp`. Both
    the `Primeir_hax.EcGroup.<m>` and bare `EcGroup.<m>` forms are accepted. -/
def recognizeEcOp (name : String) (p : Nat) (C : ECParams p) : Option ECOp :=
  if name = "Primeir_hax.EcGroup.point_add" ∨ name = "EcGroup.point_add" then
    some (.padd p C)
  else if name = "Primeir_hax.EcGroup.point_double" ∨ name = "EcGroup.point_double" then
    some (.pdbl p C)
  else if name = "Primeir_hax.EcGroup.scalar_mul" ∨ name = "EcGroup.scalar_mul" then
    some (.psmul p C true)
  else none

/-- Recognize `EcGroup::to_affine` as the `ecConvertDialect` op
    `EcConvertOp.jacobianToAffine p` (normalise a projective group element to its
    affine coordinates). Fail-closed; the group-law names are keyed by
    `recognizeEcOp`, not here. The recognition is nominal (op-family by trait
    method name); the group element is taken realised in Jacobian coordinates,
    the representation `jacobianToAffine` consumes. -/
def recognizeEcToAffineOp (name : String) (p : Nat) :
    Option EcConvertOps.EcConvertOp :=
  if name = "Primeir_hax.EcGroup.to_affine" ∨ name = "EcGroup.to_affine" then
    some (.jacobianToAffine p)
  else none

@[simp] theorem recognizeEc_point_add (p : Nat) (C : ECParams p) :
    recognizeEcOp "Primeir_hax.EcGroup.point_add" p C = some (.padd p C) := rfl
@[simp] theorem recognizeEc_point_double (p : Nat) (C : ECParams p) :
    recognizeEcOp "Primeir_hax.EcGroup.point_double" p C = some (.pdbl p C) := rfl
@[simp] theorem recognizeEc_scalar_mul (p : Nat) (C : ECParams p) :
    recognizeEcOp "Primeir_hax.EcGroup.scalar_mul" p C = some (.psmul p C true) := rfl
@[simp] theorem recognizeEc_to_affine (p : Nat) :
    recognizeEcToAffineOp "Primeir_hax.EcGroup.to_affine" p = some (.jacobianToAffine p) := rfl

/-- An unrecognized head is rejected (fail-closed). -/
theorem recognizeEc_unknown (p : Nat) (C : ECParams p) :
    recognizeEcOp "Primeir_hax.Field.mul" p C = none := rfl

/-! ## Emit: recognized group ops as single-op `Com ecDialect` leaves -/

/-- The `point_add` emit leaf: `let c = padd P Q; ret c` over `[point p, point p]`. -/
def pAddLeaf (p : Nat) (C : ECParams p) :
    Com ecDialect [ECTy.point p, ECTy.point p] (ECTy.point p) :=
  .var (.mk (.padd p C) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The `point_double` emit leaf: `let c = pdbl P; ret c` over `[point p]`. -/
def pDblLeaf (p : Nat) (C : ECParams p) :
    Com ecDialect [ECTy.point p] (ECTy.point p) :=
  .var (.mk (.pdbl p C) rfl (.cons .here .nil)) (.ret .here)

/-- The `scalar_mul` emit leaf: `let c = psmul k P; ret c` over `[scalar p, point p]`
    (the CT ladder, `ct = true`). -/
def pSmulLeaf (p : Nat) (C : ECParams p) :
    Com ecDialect [ECTy.scalar p, ECTy.point p] (ECTy.point p) :=
  .var (.mk (.psmul p C true) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-! ## The value ties

The `point_add` leaf denotes to the dialect group law `ECParams.add`, and — on
**on-curve** points — to the genuine Mathlib-transported group operation
(`EcPointGroup.ecCurvePoint_add_val`). -/

/-- **The recognized `EcGroup::point_add` call ties to the dialect group law.**
    The op that `recognizeEcOp` returns (`ECOp.padd p C`), emitted as `pAddLeaf`,
    denotes on `P Q` to `C.add P Q` — the abstract short-Weierstrass chord/tangent
    group add every `ecDialect` group op denotes to. -/
theorem primeir_ecgroup_point_add_recognized_denote (p : Nat) (C : ECParams p)
    (P Q : ECPoint p) :
    (pAddLeaf p C).denote (.cons P (.cons Q .nil)) = C.add P Q := rfl

/-- **The recognized `point_add` ties to the genuine group law on on-curve
    points.** For on-curve points `a b : EcCurvePoint C`, the `pAddLeaf` leaf on
    their underlying `ECPoint` values denotes to `(a + b).val` — the
    Mathlib-transported Weierstrass point addition (`EcPointGroup`'s
    `AddCommGroup`), reusing `ecCurvePoint_add_val`. This ties the recognized op
    to the point-add *spec* (the proved group law), beyond the raw
    `ECParams.add` map. -/
theorem primeir_ecgroup_point_add_recognized_oncurve (p : Nat) [Fact p.Prime]
    (C : ECParams p) (a b : EcCurvePoint C) :
    (pAddLeaf p C).denote (.cons a.val (.cons b.val .nil)) = (a + b).val := by
  show C.add a.val b.val = (a + b).val
  exact (ecCurvePoint_add_val C a b).symm

/-- **Recognition + emit + tie, end to end for `point_add`.** The recognizer
    accepts the `point_add` name (returning `ECOp.padd p C`) and the leaf carrying
    that op denotes to the dialect group add. -/
theorem primeir_ecgroup_point_add_recognized (p : Nat) (C : ECParams p)
    (P Q : ECPoint p) :
    recognizeEcOp "Primeir_hax.EcGroup.point_add" p C = some (.padd p C) ∧
    (pAddLeaf p C).denote (.cons P (.cons Q .nil)) = C.add P Q :=
  ⟨rfl, primeir_ecgroup_point_add_recognized_denote p C P Q⟩

/-- The op `recognizeEcToAffineOp` returns for `to_affine`
    (`EcConvertOp.jacobianToAffine p`) denotes to the `ecConvertDialect`
    Jacobian→affine normalisation `(X·(Z⁻¹)², Y·(Z⁻¹)³)`, reusing
    `EcConvertOps.jacobianToAffine_denote`. -/
theorem primeir_ecgroup_to_affine_recognized_denote (p : Nat)
    (J : ZMod p × ZMod p × ZMod p) :
    EcConvertOps.ecConvertDenote.denote (.jacobianToAffine p) (.cons J .nil)
      = (J.1 * (J.2.2)⁻¹ ^ 2, J.2.1 * (J.2.2)⁻¹ ^ 3) :=
  EcConvertOps.jacobianToAffine_denote J

/-- **Recognition + emit + tie, end to end for `to_affine`.** The recognizer
    accepts the `to_affine` name (returning `EcConvertOp.jacobianToAffine p`) and
    that op denotes to the Jacobian→affine normalisation. -/
theorem primeir_ecgroup_to_affine_recognized (p : Nat)
    (J : ZMod p × ZMod p × ZMod p) :
    recognizeEcToAffineOp "Primeir_hax.EcGroup.to_affine" p
        = some (.jacobianToAffine p) ∧
    EcConvertOps.ecConvertDenote.denote (.jacobianToAffine p) (.cons J .nil)
      = (J.1 * (J.2.2)⁻¹ ^ 2, J.2.1 * (J.2.2)⁻¹ ^ 3) :=
  ⟨rfl, primeir_ecgroup_to_affine_recognized_denote p J⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField
