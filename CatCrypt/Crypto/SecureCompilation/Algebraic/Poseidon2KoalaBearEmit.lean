/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2KoalaBear
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportPoseidon2
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# x86-64 rendering of the lowered Poseidon2 KoalaBear permutation

`permJasminAt 15` is the Poseidon2 KoalaBear permutation lowered to `jasminDialect`
through `FieldWord.KoalaBear.koalaBear`. Its last sixteen bindings are the copies of
lanes `0 .. 15`, in order. `permLprog` exports it as the function `poseidon2_kb`
through `Com.toLprogPhysAbi` with the width-16 Poseidon2 ABI maps of
`JasminLprogExportPoseidon2`: lane `i` is loaded from `8 i(%rsi)` and the `j`-th of
the last sixteen bindings is stored to `8 j(%rdi)`. `permAsm` renders it with
`LprogOptPipeline.renderOwned`.

## What is proved and what is not

* Proved: `Poseidon2KoalaBear.permJasminAt_spec`. For every lane `i`, the jasmin
  program `permJasminAt i`, evaluated by `Com.denote` on the KoalaBear encoding of
  the inputs, returns the encoding of lane `i` of
  `Hash.Poseidon2.KoalaBear.permute`.
* Proved: `Poseidon2KoalaBear.permJasminAt_exportFaithful`, the virtual export of
  one returned register under the labeled `lsem`.
* Not proved: that `toLprogPhysAbi` with these load and store maps, and the passes
  and printer of `renderOwned`, preserve that semantics.

## Main definitions

* `permLprog`, `permAsm`: the exported program and its AT&T text.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2KoalaBear

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The exported linear program: `permJasminAt 15` as the function `poseidon2_kb`,
    loading the 16 lanes from `RSI` and storing the last 16 bindings to `RDI`. -/
def permLprog (_ : Unit) : Lprog :=
  Com.toLprogPhysAbi (permJasminAt 15) "poseidon2_kb" (fun _ => none) poseidon2ImmSlots
    poseidon2InLoadMap poseidon2OutStoreMap

/-- The AT&T text of `permLprog` through `renderOwned`. -/
def permAsm (_ : Unit) : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (permLprog ())

end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2KoalaBear
