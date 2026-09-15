/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBearCompile
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportPoseidon2
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# x86-64 rendering of the lowered Poseidon2 BabyBear permutation

`permJasminAt 15` is the Poseidon2 BabyBear permutation `permComAt 15`, a
`Com fieldDialect` over the 16 input lanes, lowered to `jasminDialect` by
`FieldToJasminWord.lowerK babyBear`. Its last sixteen bindings are the `regArith or`
copies of lanes `0 .. 15`, in order. `permLprog` exports it as the function
`poseidon2_bb` through `Com.toLprogPhysAbi` with the Poseidon2 ABI maps of
`JasminLprogExportPoseidon2`: lane `i` is loaded from `8 i(%rsi)` and the `j`-th of
the last sixteen bindings is stored to `8 j(%rdi)`. `permAsm` renders it with
`LprogOptPipeline.renderOwned`.

## What is proved and what is not

* Proved: `Poseidon2BabyBear.permComAt_lowerK_denote`. For every lane `i`, the
  jasmin program `permJasminAt i`, evaluated by `Com.denote` on the BabyBear
  encoding of the inputs, returns the encoding of lane `i` of the field program.
  The sixteen programs `permJasminAt i` share their bindings and differ only in the
  returned variable.
* Proved: `Poseidon2BabyBear.permJasminAt_exportFaithful`. `permJasminAt i` is in
  `UniformScalarArith 64`, and by `JasminLsemGeneralFaithful.comLsemExportFaithful_of_scalar`
  its virtual export `straightOps`, run under the labeled `lsem` from the encoded
  inputs, returns `(permJasminAt i).denote` in its result register. This concerns
  one returned register and no memory loads or stores.
* Not proved: that `toLprogPhysAbi` with these load and store maps, and the passes
  and printer of `renderOwned`, preserve that semantics. The physical theorem
  `toLprogPhysAbi_faithful_uniform` covers `regArith`-only programs, and the lowered
  program contains `regConst` bindings. No theorem covers `renderOwned`.
* Not proved: that `permComAt i` computes lane `i` of
  `Hash.Poseidon2.BabyBear.poseidon2BabyBearPermute`.

The rendered text is checked outside Lean: the permutation KAT of
`bench/poseidon2_compare` and the absence of `UNHANDLED` markers, which the printer
writes as comments in place of instructions it cannot render
(`permAsmHandled`).

## Main definitions

* `permLprog`, `permAsm`: the exported program and its AT&T text.
* `hasUnhandled`, `permAsmHandled`: the `UNHANDLED`-marker test and the
  proposition that `permAsm` has no such marker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBear

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The exported linear program: `permJasminAt 15` as the function `poseidon2_bb`,
    loading the 16 lanes from `RSI` and storing the last 16 bindings to `RDI`. -/
def permLprog : Lprog :=
  Com.toLprogPhysAbi (permJasminAt 15) "poseidon2_bb" (fun _ => none) poseidon2ImmSlots
    poseidon2InLoadMap poseidon2OutStoreMap

/-- The AT&T text of `permLprog` through `renderOwned`. -/
def permAsm : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned permLprog

/-- Whether `s` contains the marker `UNHANDLED`. -/
def hasUnhandled (s : String) : Bool :=
  (s.splitOn "UNHANDLED").length ≠ 1

/-- The rendered permutation contains no `UNHANDLED` marker. -/
def permAsmHandled : Prop := hasUnhandled permAsm = false

end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBear
