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
`refusal?` (field `chainNF`), the export test on its output (`exportable`), the legalisation
(`legalize`), the export (`exportRSome`), the allocation (`regionLprogCSome`) and the first
printed body (`firstBodySome`). Each theorem has the type of its field.

## Main results

* `fieldDom_chainNF` — the chain check: on a module `refusal?` accepts, `chainNF` returns a program.
* `fieldDom_exportable` — the export test: that program passes `regionExportableB`.
* `fieldDom_legalize` — the legalisation: `legalizeRegion` keeps `regionExportableB`.
* `fieldDom_exportRSome` — the export: `exportR` returns code on a program that passes
  `regionExportableB`.
* `fieldDom_regionLprogCSome` — the allocation: it returns a program when the export
  does.
* `fieldDom_firstBodySome` — the first printed body: the printed program of an allocation has a
  first body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.Hax (HaxModule)

/-- **The chain check**: on a module `refusal?` accepts, the translation and the chain `extChain`
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

/-- **The export test**: the output of the chain on a module `refusal?` accepts passes
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

/-- **The legalisation**: the legalised program passes `regionExportableB`
    (`regionExportableB_legalizeRegion`, `regionExportableRorB_eq`). -/
theorem fieldDom_legalize {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} (hq : regionExportableB q = true) :
    regionExportableB (legalizeRegion q) = true :=
  regionExportableB_legalizeRegion ((regionExportableRorB_eq q).trans hq)

/-- **The export**: the export returns code on a program that passes `regionExportableB`
    (`exportR_isSome_of_regionExportableB`). -/
theorem fieldDom_exportRSome {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {q : NFProg jasminDialect Γ ts} (hq : regionExportableB q = true) (nArgs : Nat)
    (fn : String) (d n : Nat) : ∃ r0, exportR nArgs fn q d n = some r0 :=
  Option.isSome_iff_exists.mp (ExportComplete.exportR_isSome_of_regionExportableB hq nArgs fn d n _)

/-- **The allocation**: the allocation `regionLprogC` returns a program when the export does; the
    allocation stage refuses nothing after the export (as in `regionLprog_isSome_iff_exportR`). -/
theorem fieldDom_regionLprogCSome {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} {r0 : Exported} (ex : List String)
    (hr0 : exportR Γ.length a.fname q Γ.length 0 = some r0) :
    ∃ P cert, regionLprogC a q none ex = some (P, cert) := by
  simp only [regionLprogC, regionAllocC, exportRLfundef, hr0, Option.bind_some, Option.map_some]
  exact ⟨_, _, rfl⟩

/-- **The first printed body**: the printed program of an allocation has a first body: the
    allocation returns a one-function program, and the post-pass and the printer keep its function
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
