/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256Tie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256Tie
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie

/-!
# Security tie: the compile-from-hax UOV GF(2⁸) multiply leaf realizes the
  abstract `Gf256` field multiply the security reference reasons over

`CompileFromHaxUovGf256` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 32` denotation is `gf256MulSpec` — the bit-serial
shift-and-conditional-XOR (Russian-peasant) form for the binary field
`GF(2⁸) = GF(2)[x]/(x⁸+x⁴+x³+x+1)` — and `CompileFromHaxUovGf256Tie` closes the
last hop to the abstract Mathlib-style field `CatCrypt.Util.Gf256.mul`: reading
the leaf's low byte back as a `Gf256 = BitVec 8` element, it is exactly the
abstract field product `Gf256.mul a b`
(`CompileFromHaxUovGf256Tie.gf256MulSpec_setWidth8_eq_field`).

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism, as the
FrodoKEM/NTRU/sntrup/SLH-DSA SecurityTie modules did): it packages that field
multiply as a one-field abstract `MulDeps` dependency record over `Gf256`,
exhibits the *spec* instance (the abstract field multiply the UOV `OV-Ip`
public-map reference is built from) and the *compiled-realization* instance (the
function the verified-compiled leaf actually computes, read back into `Gf256` via
the low-byte projection), proves them equal field-by-field, and feeds that
equality to `tie_transfer` so that **any** property the security layer proves of
the abstract field multiply transfers verbatim to the compiler-emitted leaf,
with no new axioms.

## Why this is parametric-correct for UOV (scope)

UOV's `OV-Ip` public map is parametric over the binary field `GF(2⁸)` and reasons
over it *abstractly* through the field multiply `Gf256.mul` (and the
`Util.Gf256` field laws `mul_one`, `mul_comm`, `mul_assoc`, … established for it).
The compiled leaf computes exactly that field multiply
(`gf256MulSpec_setWidth8_eq_field`): unlike the power-of-two ring ties
(HAWK/FrodoKEM) there is no `%`-reduction identity — the tie is the
**carryless-multiply = field-multiply** equation, the binary-field sibling of the
GF(251)/GF(127) prime-field ties. Therefore the tie is at the **arithmetic
building block** the parametric proof quantifies over: the realization equality
`toMulDeps = mulDepsSpec` holds and `tie_transfer` carries any field-multiply
property onto the compiled artifact. It does **not** discharge the UOV (oil–vinegar
/ MQ) trapdoor assumption, nor instantiate the public-map dimensions `(m, n, v)`
— those remain the parametric hypotheses of `UOV/Security.lean`; this ties the
*emitted arithmetic* to the *abstract arithmetic* the proof uses, which is the
scope of this module.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256SecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256Tie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)
open CatCrypt.Util

/-! ## §1  The abstract one-field multiply dependency record

`MulDeps R` is the miniature `Dependencies` for a binary-field multiply: the
single arithmetic primitive `mul : R → R → R` the UOV `OV-Ip` public map is built
from. A security proof over the field is parametric over a `MulDeps Gf256` and
reasons only through the *spec* the field satisfies. -/

/-- The abstract field-multiply dependency record over a type `R`. -/
structure MulDeps (R : Type*) where
  /-- The field-multiply primitive `a b ↦ a · b`. -/
  mul : R → R → R

/-! ## §2  The abstract spec instance (what the security reference assumes)

`mulDepsSpec` fills the field with the abstract `GF(2⁸)` field multiply
`Util.Gf256.mul` — exactly the field product the UOV `OV-Ip` public map evaluates
and the `Util.Gf256` field laws are stated for. -/

/-- The abstract spec instance: the `Gf256` field multiply `Gf256.mul a b` the
    UOV `OV-Ip` public map evaluates over `GF(2⁸)`. -/
def mulDepsSpec : MulDeps Gf256 where
  mul := fun a b => Gf256.mul a b

/-! ## §3  The compiled realization instance (what the verified compiler emits)

`compiledMulFn` is the function the verified-compiled jasmin `Com` actually
computes, read back as a `Gf256 = BitVec 8` element via the low-byte projection
`setWidth 8` of the emitted width-32 `gf256MulSpec` on zero-extended byte
inputs. -/

/-- The function the verified-compiled UOV GF(2⁸) multiply `Com` computes, read
    back into `Gf256`: each byte input is zero-extended into the width-32 emit
    form (`setWidth 32`) and the leaf output is read back as a `Gf256` via the
    low-byte projection (`setWidth 8`). -/
def compiledMulFn (a b : Gf256) : Gf256 :=
  BitVec.setWidth 8 (gf256MulSpec (BitVec.setWidth 32 a) (BitVec.setWidth 32 b))

/-- The compiled-realization instance: the abstract `MulDeps Gf256` filled with
    the function the **verified compiler emits** for the UOV GF(2⁸) multiply. -/
def toMulDeps : MulDeps Gf256 where
  mul := compiledMulFn

/-! ## §4  The realization theorem and the generic transfer

The compiled multiply, applied to byte inputs and read back via the low-byte
projection, equals the abstract field multiply. This is
`gf256MulSpec_setWidth8_eq_field` (the carryless-multiply = field-multiply
identity, closed in the tie file by `native_decide` over the `2¹⁶` byte
pairs). -/

/-- **The realization theorem.** The compiler-emitted multiply instance equals
    the abstract field-multiply spec instance: on every pair of `Gf256` field
    bytes, the verified-compiled UOV leaf (read back via the low-byte projection)
    computes exactly the abstract `GF(2)[x]/(x⁸+x⁴+x³+x+1)` field product
    `Gf256.mul a b`. Closed field-by-field by
    `CompileFromHaxUovGf256Tie.gf256MulSpec_setWidth8_eq_field`, the
    carryless-multiply = field-multiply identity. -/
theorem toMulDeps_eq_spec : toMulDeps = mulDepsSpec := by
  unfold toMulDeps mulDepsSpec compiledMulFn
  congr 1
  funext a b
  exact gf256MulSpec_setWidth8_eq_field a b

/-- **Compiled UOV GF(2⁸) multiply inherits any abstract field-multiply
    property.** For every property `P` of `MulDeps Gf256`, if `P` holds of the
    abstract field-multiply spec instance then it holds of the compiler-emitted
    realization instance. The mechanized statement that the verified-compiled UOV
    arithmetic leaf plugs into the abstract `OV-Ip` security layer: any property
    the parametric `UOV/Security.lean` proof establishes over the abstract field
    multiply transfers verbatim to `toMulDeps`, the verified compiler's emitted
    primitive — with no new axioms. Instantiates
    `CompileFromHaxSecurityTie.tie_transfer` at `Deps := MulDeps Gf256` with the
    UOV realization equality. -/
theorem appliesToCompiledUov (P : MulDeps Gf256 → Prop) (h : P mulDepsSpec) :
    P toMulDeps :=
  tie_transfer P toMulDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256SecurityTie
