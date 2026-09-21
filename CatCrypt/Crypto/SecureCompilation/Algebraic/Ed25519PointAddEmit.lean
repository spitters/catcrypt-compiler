/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAddLower
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit

/-!
# x86-64 rendering of the lowered Ed25519 extended-coordinate point addition

`pointAddJasmin ed25519D i` is the addition program of `Ed25519PointAddCompile`,
lowered to `jasminDialect` over four 64-bit limbs per coordinate by
`FieldToJasminLimbs25519.loweringL`. It is a `MultiReturnCom` returning the four
limbs of one output coordinate; `MultiReturnCom.toComHead` drops the returned
tuple to its first limb, keeping every binding, which is the single-return `Com`
that `Com.toLprogPhysAbi` exports. The four programs `i = 0 .. 3` share their
bindings and differ only in the returned variable, so the choice of `i` here does
not change the exported body.

`pointAddLprog` exports it as the function `ed25519_point_add` with the ABI maps
below, and `pointAddAsm` renders it with `FheMontMulEmit.fuseMulHiLprog` followed
by `LprogOptPipeline.renderOwned`.

## Argument and output layout

The flattened input context holds thirty-two 64-bit words: the four limbs of each
of `X₁, Y₁, Z₁, T₁, X₂, Y₂, Z₂, T₂`, in that order, least-significant limb first.
`comToLfundef` assigns input word `i` the argument slot `31 - i`, so the load map
reads word `i` from `8 i(%rsi)`.

The last four bindings of the source program are `fCopy` bindings of
`X₃, Y₃, Z₃, T₃` in that order, and each lowers to the four sequential limb
bindings of `FieldLimbs.Curve25519.copyBlk`. The last sixteen bindings of the
exported body are therefore the sixteen output limbs in coordinate order, which
is what the store map writes to `8 j(%rdi)`.

```c
extern uint64_t ed25519_point_add(uint64_t *out, const uint64_t *inp);
//   inp[0..31] = X1,Y1,Z1,T1,X2,Y2,Z2,T2, four limbs each, little-endian;
//   out[0..15] = X3,Y3,Z3,T3, four limbs each.
```

## What is proved and what is not

* Proved, at `Com.denote` / `MultiReturnCom.denote`:
  `Ed25519PointAddLower.pointAddProg_lowered_m1add`. On the limbs of two points of
  `EdwardsPointExt ed25519Ext`, the four lowered programs denote the limbs of the
  four coordinates of `EdwardsPointExt.m1add`, whose affine projection is the sum
  of the affine projections of the inputs
  (`Ed25519PointAddCompile.pointAddProg_m1add`). The addition has no exceptional
  case (`pointAddProg_z3_ne_zero`).
* Proved: `MultiReturnCom.toComHead_denote` ties the exported single-return `Com`
  to the first entry of that multi-return denotation. It says nothing about the
  other fifteen output limbs, which reach the caller through the store map rather
  than the return value.
* Not proved: that `Com.toLprogPhysAbi` with these load and store maps preserves
  that semantics for this body. The physical theorem
  `X86Backend/ToLprogFaithfulAssembled.toLprogPhysAbi_faithful_uniform` covers
  `regArith`-only programs; `X86Backend/ToLprogFaithfulConst` extends the covered
  bindings to `regConst` and `X86Backend/ToLprogFaithfulMulCarrySel` to `mulhi`
  and the carry bindings. The Curve25519 limb blocks also bind `select`, which no
  physical theorem covers, so the export of this body is not covered end to end.
* Not proved: the passes and printer of `renderOwned`. No theorem covers them.
* Not proved here: that the rendered text carries no `UNHANDLED` marker. The
  printer writes `# UNHANDLED-MULXHI-UNFUSED` for a `MULXHI` binding that
  `fuseMulHiLprog` did not fuse, and the corresponding marker for an unfused carry
  binding, so whether the markers are absent depends on the fusion passes matching
  the shape of `mulBlk`. `pointAddAsmHandled` states their absence; it is checked
  outside Lean, by running the emitter.

## Main definitions

* `pointAddCom`: the exported single-return body.
* `pointAddImmSlots`, `pointAddInLoadMap`, `pointAddOutStoreMap`: the ABI maps.
* `pointAddLprog`, `pointAddAsm`: the exported program and its AT&T text.
* `hasUnhandled`, `pointAddAsmHandled`: the `UNHANDLED`-marker test and the
  proposition that `pointAddAsm` has no such marker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs25519
open CatCrypt.Util (ed25519D)

/-- The exported body: the lowered addition, with the returned limb tuple dropped
    to its first limb and every binding kept. -/
def pointAddCom : Com jasminDialect (loweringL.mapCtx inCtxt) FieldLimbs.Curve25519.w64 :=
  (pointAddJasmin ed25519D 0).toComHead

/-- The immediate-slot map: empty. The curve constant `2d` and the limb constants
    are materialized inside the body by the nullary `regConst` op. -/
def pointAddImmSlots : ImmSlotMap := fun _ => none

/-- The input-load map: argument slot `s` holds input word `31 - s`, read from
    `8 (31 - s)(%rsi)`. -/
def pointAddInLoadMap : InLoadMap := fun slot =>
  if slot ≤ 31 then some ("RSI", (31 - slot) * 8) else none

/-- The output-store map: the sixteen output limbs, written to `8 j(%rdi)`. -/
def pointAddOutStoreMap : OutStoreMap :=
  (List.range 16).map (fun j => ("RDI", j * 8))

/-- The exported linear program: `pointAddCom` as the function
    `ed25519_point_add`, loading the thirty-two input limbs from `RSI` and storing
    the last sixteen bindings to `RDI`. -/
def pointAddLprog : Lprog :=
  Com.toLprogPhysAbi pointAddCom "ed25519_point_add" (fun _ => none) pointAddImmSlots
    pointAddInLoadMap pointAddOutStoreMap

/-- The AT&T text of `pointAddLprog` through the MULX fusion pass and
    `renderOwned`. `fuseMulHiLprog` coalesces the low `MUL` and the `MULXHI` that
    `FieldLimbs.Curve25519.mulRowK` emits for the same pair of limbs into the
    printer's two-output `MULX`. The body is straight-line, so the pass runs in
    its default mode, in which `%rdx` carries no live value across a fused pair. -/
def pointAddAsm : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwnedZeroized
    (CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit.fuseMulHiLprog pointAddLprog)

/-- Whether `s` contains the marker `UNHANDLED`. -/
def hasUnhandled (s : String) : Bool :=
  (s.splitOn "UNHANDLED").length ≠ 1

/-- The rendered addition contains no `UNHANDLED` marker. -/
def pointAddAsmHandled : Prop := hasUnhandled pointAddAsm = false

end CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd
