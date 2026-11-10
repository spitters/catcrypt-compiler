/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
import CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps
import CatCrypt.Crypto.SecureCompilation.Haxc.AndnLegalComplete
import CatCrypt.Crypto.SecureCompilation.Haxc.RorLegalComplete
import CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate

/-!
# The front stages of `compileA` on the field domain

The fields of `FieldDomComplete.FieldDomStages` for the front stages that hold on every
module the translation accepts, and on every program that passes `regionExportableB`, proved
as theorems from the completeness lemmas of the stages: the chain `extChain` after
`refusal?` (`F2`), the export test on its output (`F3`), the legalisation (`F5`), the export
(`F6`), the allocation (`F8`) and the first printed body (`F9`). Each theorem has the type of
its field.

## Main results

* `fieldDom_chainNF` — stage `F2`: on a module `refusal?` accepts, `chainNF` returns a program.
* `fieldDom_exportable` — stage `F3`: that program passes `regionExportableB`.
* `fieldDom_legalize` — stage `F5`: `legalizeRegion` keeps `regionExportableB`.
* `fieldDom_exportRSome` — stage `F6`: `exportR` returns code on a program that passes
  `regionExportableB`.
* `fieldDom_regionLprogCSome` — stage `F8`: the allocation returns a program when the export
  does.
* `fieldDom_firstBodySome` — stage `F9`: the printed program of an allocation has a first
  body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.Hax (HaxModule)

/-- **Stage `F2`**: on a module `refusal?` accepts, the translation and the chain `extChain`
    return a program (`HaxModule.refusal?_eq_none_imp_extChain_isSome` at the table of the
    entry). -/
theorem fieldDom_chainNF {m : HaxModule} {σ : AbiLayout} (hr : m.refusal? σ = none) :
    ∃ x, haxEntry.chainNF m σ = some x := by
  obtain ⟨t, p, hp, h⟩ := HaxModule.refusal?_eq_none_imp_extChain_isSome hr
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (h CatCrypt.Crypto.Hax.hax64WExit)
  refine ⟨⟨_, q⟩, ?_⟩
  change (haxToNF σ m).bind (fun q => ((extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit)
    _ q.1).run q.2).map fun p => (⟨_, p⟩ : Σ t : JasminTy, NFProg jasminDialect (nfCtx σ) [t])) = _
  rw [hp, Option.bind_some, hq, Option.map_some]

/-- **Stage `F3`**: the output of the chain on a module `refusal?` accepts passes
    `regionExportableB` (`HaxModule.refusal?_eq_none_imp_export_isSome`). -/
theorem fieldDom_exportable {m : HaxModule} {σ : AbiLayout} {t : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t]} (hr : m.refusal? σ = none)
    (hq : haxEntry.chainNF m σ = some ⟨t, q⟩) : regionExportableB q = true := by
  obtain ⟨t', p, hp, h⟩ := HaxModule.refusal?_eq_none_imp_export_isSome hr
  obtain ⟨q', hq', -, -, hE, -⟩ := h CatCrypt.Crypto.Hax.hax64WExit
  simp only [NFEntry.chainNF, haxEntry, hp, Option.bind_some, hq', Option.map_some,
    Option.some.injEq] at hq
  cases hq
  exact hE

/-- **Stage `F5`**: the legalised program passes `regionExportableB`
    (`regionExportableB_legalizeRegion`, `regionExportableRorB_eq`). -/
theorem fieldDom_legalize {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} (hq : regionExportableB q = true) :
    regionExportableB (legalizeRegion q) = true :=
  regionExportableB_legalizeRegion ((regionExportableRorB_eq q).trans hq)

/-- **Stage `F6`**: the export returns code on a program that passes `regionExportableB`
    (`exportR_isSome_of_regionExportableB`). -/
theorem fieldDom_exportRSome {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {q : NFProg jasminDialect Γ ts} (hq : regionExportableB q = true) (nArgs : Nat)
    (fn : String) (d n : Nat) : ∃ r0, exportR nArgs fn q d n = some r0 :=
  Option.isSome_iff_exists.mp (ExportComplete.exportR_isSome_of_regionExportableB hq nArgs fn d n _)

/-- **Stage `F8`**: the allocation `regionLprogC` returns a program when the export does; the
    allocation stage refuses nothing after the export (as in `regionLprog_isSome_iff_exportR`). -/
theorem fieldDom_regionLprogCSome {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} {r0 : Exported} (ex : List String)
    (hr0 : exportR Γ.length a.fname q Γ.length 0 = some r0) :
    ∃ P cert, regionLprogC a q none ex = some (P, cert) := by
  simp only [regionLprogC, regionAllocC, exportRLfundef, hr0, Option.bind_some, Option.map_some]
  exact ⟨_, _, rfl⟩

/-- **Stage `F9`**: the printed program of an allocation has a first body: the allocation
    returns a one-function program, and the post-pass and the printer keep its function
    (`firstBody_regionPrinted`, `firstBody_printedLprog_regionPostFuse`). -/
theorem fieldDom_firstBodySome {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} {ex : List String} {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a q none ex = some (P, cert)) :
    ∃ b, firstBody (regionPrinted P) = some b := by
  simp only [regionLprogC, Option.map_eq_some_iff] at hP
  obtain ⟨⟨P0, c0⟩, h0, hPc⟩ := hP
  simp only [Prod.mk.injEq] at hPc
  obtain ⟨rfl, -⟩ := hPc
  simp only [regionAllocC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h0
  obtain ⟨r0, -, fd0, -, h0⟩ := h0
  simp only [Prod.mk.injEq] at h0
  obtain ⟨rfl, -⟩ := h0
  rw [firstBody_regionPrinted, RegionPhysImgGate.firstBody_printedLprog_regionPostFuse rfl]
  exact ⟨_, rfl⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
