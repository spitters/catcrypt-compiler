/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonBN254Lower
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-!
# x86-64 rendering of the lowered BN254 Poseidon permutation

`permJasminAt 0` is the width-3 circomlib Poseidon permutation over the BN254 scalar
field, lowered to `jasminDialect` over four 64-bit limbs per lane in Montgomery form
(`PoseidonBN254Lower`). It is a `MultiReturnCom`; `MultiReturnCom.toComHead` drops the
returned tuple to its first limb and keeps every binding, which is the single-return
`Com` that `Com.toLprogPhysAbi` exports. The programs `i = 0, 1, 2` share their
bindings, so the choice of `i` does not change the exported body.

## Argument and output layout

The flattened input context holds twelve 64-bit words: the four limbs of the
Montgomery forms `x · 2^256 mod r` of lanes `0, 1, 2`, in that order, least
significant limb first. `comToLfundef` assigns input word `i` the argument slot
`11 - i`, so the load map reads word `i` from `8 i(%rsi)`.

The last three bindings of the source program are `fCopy` bindings of lanes
`0, 1, 2`, and each lowers to the four sequential limb bindings of
`FieldLimbs.Curve25519.copyBlk`. The last twelve bindings of the exported body are
therefore the twelve output limbs in lane order, which the store map writes to
`8 j(%rdi)`.

```c
extern void poseidon_bn254_t3(uint64_t *out, const uint64_t *inp);
//   inp[0..11] = lanes 0, 1, 2, four limbs each of x · 2^256 mod r, little-endian;
//   out[0..11] = the three output lanes in the same form.
```

## What is proved and what is not

* Proved, at `MultiReturnCom.denote`: `PoseidonBN254Lower.permJasminAt_denote`. For
  every input, the three lowered programs denote the limbs of the Montgomery forms
  of the three lanes of `Hash.Poseidon.BN254.permute3`.
* Not proved: that `Com.toLprogPhysAbi` with these load and store maps preserves
  that semantics for this body. The Montgomery blocks bind `select`, which no
  physical export theorem covers.
* Not proved: the passes and printer of `renderOwnedZeroized`, and the absence of
  `UNHANDLED` markers in the rendered text (`permAsmHandled`), which depends on
  `fuseMulHiLprog` fusing every `MULXHI` of the blocks.

## Main definitions

* `permCom`: the exported single-return body.
* `permImmSlots`, `permInLoadMap`, `permOutStoreMap`: the ABI maps.
* `permLprog`, `permAsm`: the exported program and its AT&T text.
* `hasUnhandled`, `permAsmHandled`: the `UNHANDLED`-marker test and the proposition
  that `permAsm` has no such marker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonBN254

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4

/-- The exported body: the lowered permutation, with the returned limb tuple dropped
    to its first limb and every binding kept. -/
def permCom : Com jasminDialect ((loweringL bn254r).mapCtx inCtxt)
    FieldLimbs.Curve25519.w64 :=
  (permJasminAt 0).toComHead

/-- The immediate-slot map: empty. The round constants, the MDS entries and the
    modulus limbs are materialised inside the body by the nullary `regConst` op. -/
def permImmSlots : ImmSlotMap := fun _ => none

/-- The input-load map: argument slot `s` holds input word `11 - s`, read from
    `8 (11 - s)(%rsi)`. -/
def permInLoadMap : InLoadMap := fun slot =>
  if slot ≤ 11 then some ("RSI", (11 - slot) * 8) else none

/-- The output-store map: the twelve output limbs, written to `8 j(%rdi)`. -/
def permOutStoreMap : OutStoreMap :=
  (List.range 12).map (fun j => ("RDI", j * 8))

/-- The exported linear program: `permCom` as the function `poseidon_bn254_t3`,
    loading the twelve input limbs from `RSI` and storing the last twelve bindings to
    `RDI`. -/
def permLprog : Lprog :=
  Com.toLprogPhysAbi permCom "poseidon_bn254_t3" (fun _ => none) permImmSlots
    permInLoadMap permOutStoreMap

/-- The AT&T text of `permLprog` through the MULX fusion pass and
    `renderOwnedZeroized`. `fuseMulHiLprog` coalesces the low `MUL` and the `MULXHI`
    that `FieldLimbs.Curve25519.mulRowK` emits for the same pair of limbs into the
    printer's two-output `MULX`. -/
def permAsm (_ : Unit) : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwnedZeroized
    (CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi.fuseMulHiLprog permLprog)

/-- Whether `s` contains the marker `UNHANDLED`. -/
def hasUnhandled (s : String) : Bool :=
  (s.splitOn "UNHANDLED").length ≠ 1

/-- The rendered permutation contains no `UNHANDLED` marker. -/
def permAsmHandled : Prop := hasUnhandled (permAsm ()) = false

end CatCrypt.Crypto.SecureCompilation.Algebraic.PoseidonBN254
