/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMem

set_option autoImplicit false

/-!
# General-`Com` `lsem` export faithfulness — unified headline

The three per-fragment `lsem` export-faithfulness predicates live in:

* `JasminLsemGeneralFaithful` — `ComLsemExportFaithful` /
  `comLsemExportFaithful_of_scalar`, over the plain `Lstate` program-indexed
  `lsem` (`encode`/`decode`), for the `UniformScalarArith` fragment
  (`{regArith, regConst, select}`).
* `JasminLsemGeneralFaithfulMC` — `ComLsemExportFaithfulMC` /
  `comLsemExportFaithfulMC_of_mulcarry`, over `LstateN` (`encodeN`/`decodeN`/
  `lsemFuelMC`), for the `ScalarMulCarryN` fragment
  (`{regArith, select, immediate shifts, mulhi, addCarryLo/Hi}`).
* `JasminLsemGeneralFaithfulLeaf` — `ComLsemExportFaithfulLeaf` /
  `comLsemExportFaithfulLeaf_of_leaf`, over `LstateN` + `LeafEnvN`
  (`lsemFuelLeaf`, under the carried leaf agreement `LeafAgreesN leaf`), for the
  **maximal** `ScalarLeafN` fragment (the above plus `castW` and the opaque
  `extCall` leaf).
* `JasminLsemGeneralFaithfulMem` — `ComLsemExportFaithfulMem` /
  `comLsemExportFaithfulMem_of_mem`, over the bundled state `LstateM` (register
  file + aliasing array carrier) and `lsemFuelMem`, for the `ScalarMemN` fragment
  (the register tower plus the **memory** ops `stackLoad`/`stackStore`). This is
  the orthogonal memory axis: the first export-faithfulness result covering
  aliasing memory mutation (runtime-indexed load/store).

`ScalarLeafN` is the maximal straight-line fragment of the modeled op set: the
subsumption tower

  `UniformRegArith → UniformScalarArith → ScalarArithN → ScalarShiftN
     → ScalarMulCarryN → ScalarCastN → ScalarLeafN`

holds via the `.of_*` lemmas (here: `ScalarCastN.of_scalarMulCarryN`,
`ScalarLeafN.of_scalarCastN`). So **every** straight-line `Com` over the modeled
ops maps into `ScalarLeafN`, and `comLsemExportFaithfulLeaf_of_leaf` discharges
the export gate for it. This file re-exports that leaf result as **the** general
statement and records the per-sub-fragment corollaries obtained by composing the
subsumption lemmas.

The plain-`Lstate` scalar result (`comLsemExportFaithful_of_scalar`) is the
lighter single-width special case: for `Com`s over `{regArith, regConst,
select}` it runs the simpler `encode`/`decode`/`lsem` machinery without the
width-tagged `LstateN` or a `LeafEnvN` hypothesis. It is not subsumed
definitionally by the leaf statement (different state type / no leaf agreement),
but it covers exactly the `UniformScalarArith` base of the same tower.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulAll

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf

/-- **General-`Com` `lsem` export faithfulness for the modeled op set.** For any
    `Com` in the maximal straight-line fragment `ScalarLeafN`, under the carried
    leaf agreement `LeafAgreesN leaf`, the emitted singleton typed program runs
    under the program-indexed leaf `lsem` from the encoded inputs to a state
    whose result register decodes to `Com.denote`. This is
    `comLsemExportFaithfulLeaf_of_leaf` re-exported as the general statement:
    because `ScalarLeafN` subsumes every sub-fragment of the tower, this single
    predicate covers every straight-line `Com` over the modeled ops. -/
theorem general_com_lsem_faithful {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulLeaf leaf com fn hw :=
  comLsemExportFaithfulLeaf_of_leaf hleaf hcom hw fn

/-- **Mul/carry sub-fragment, via the general statement.** Any `Com` over
    `{regArith, select, immediate shifts, mulhi, addCarryLo/Hi}`
    (`ScalarMulCarryN`) is covered by `general_com_lsem_faithful` through the
    subsumption chain `ScalarCastN.of_scalarMulCarryN` then
    `ScalarLeafN.of_scalarCastN`. -/
theorem general_of_mulcarry {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulLeaf leaf com fn hw :=
  general_com_lsem_faithful hleaf
    (ScalarLeafN.of_scalarCastN (ScalarCastN.of_scalarMulCarryN hcom)) hw fn

/-- **Cast sub-fragment, via the general statement.** Any `Com` over the
    mul/carry ops plus `castW` (`ScalarCastN`) is covered by
    `general_com_lsem_faithful` through `ScalarLeafN.of_scalarCastN`. -/
theorem general_of_cast {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulLeaf leaf com fn hw :=
  general_com_lsem_faithful hleaf (ScalarLeafN.of_scalarCastN hcom) hw fn

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulAll
