/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16Spec
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.KoalaBear
public import CatCrypt.Crypto.Hash.Poseidon2.KoalaBear

/-!
# Poseidon2 over KoalaBear as a compiled `fieldDialect` program

The width-16 program of `Poseidon2Width16Compile` at the KoalaBear parameters
`Hash.Poseidon2.KoalaBear.params`, lowered to `jasminDialect` through the KoalaBear
single-word field `FieldWord.KoalaBear.koalaBear`.

## Main definitions

* `permComAt i`: the permutation program over the 16 input lanes, returning lane `i`.
* `permJasminAt i`: its lowering.

## Main results

* `permComAt_spec`: `(permComAt i).denote V` is lane `i` of
  `Hash.Poseidon2.KoalaBear.permute` on the input state of `V`.
* `permJasminAt_spec`: for every input valuation `V`, the lowered program returns
  the KoalaBear encoding of that lane.
* `koalaBear_scalarBlocks`, `permJasminAt_exportFaithful`: the KoalaBear blocks are
  in the scalar fragment, and the lowered program satisfies
  `JasminLsemGeneralFaithful.ComLsemExportFaithful`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2KoalaBear

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.KoalaBear (koalaBear)
open CatCrypt.Crypto.Hash.Poseidon2.KoalaBear (params)
open CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16 (inCtxt FP inputState)

/-- The KoalaBear Poseidon2 program returning lane `i`. -/
def permComAt (i : Fin 16) : Com fieldDialect (inCtxt params) (FP params) :=
  Poseidon2Width16.permComAt params i

/-- The lowered KoalaBear Poseidon2 program returning lane `i`. -/
def permJasminAt (i : Fin 16) :
    Com jasminDialect (mapCtxW (inCtxt params)) (mapTyW (FP params)) :=
  Poseidon2Width16.permJasminAt params koalaBear i

theorem sboxDeg_pos : 1 ≤ params.sboxDeg := by decide

/-- **The KoalaBear field program computes the specification.** -/
theorem permComAt_spec (i : Fin 16) (V : Ctxt.Valuation (inCtxt params)) :
    (permComAt i).denote V =
      Hash.Poseidon2.KoalaBear.permute (inputState params V) i :=
  Poseidon2Width16.permComAt_spec sboxDeg_pos i V

/-- **The compiled KoalaBear program computes the specification.** On the KoalaBear
    encoding of any input valuation `V`, the lowered program returns the encoding of
    lane `i` of `Hash.Poseidon2.KoalaBear.permute` applied to the input state of
    `V`. -/
theorem permJasminAt_spec (i : Fin 16) (V : Ctxt.Valuation (inCtxt params)) :
    (permJasminAt i).denote (mapValW koalaBear V) =
      koalaBear.enc (Hash.Poseidon2.KoalaBear.permute (inputState params V) i) :=
  Poseidon2Width16.permJasminAt_spec sboxDeg_pos koalaBear i V

section Scalar

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful (ComLsemExportFaithful)

theorem koalaBear_scalarBlocks : ScalarBlocks koalaBear :=
  scalarBlocks_ofCanonical _ _ _ _ fun a b => by
    unfold FieldWord.KoalaBear.mulBlk
    exact Poseidon2Width16.scalar_foldMulBlk _ _ _ a b

/-- **Virtual export faithfulness of the lowered KoalaBear permutation.** -/
theorem permJasminAt_exportFaithful (i : Fin 16) (fn : String) :
    ComLsemExportFaithful (permJasminAt i) fn
      (lowerK_scalar koalaBear koalaBear_scalarBlocks (permComAt i)).ret_ty :=
  Poseidon2Width16.permJasminAt_exportFaithful params koalaBear koalaBear_scalarBlocks i fn

end Scalar

end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2KoalaBear
