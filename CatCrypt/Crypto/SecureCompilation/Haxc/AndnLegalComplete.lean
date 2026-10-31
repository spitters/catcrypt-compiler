/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.AndnLegal
public import CatCrypt.Crypto.SecureCompilation.Haxc.RorLegalComplete

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the region export test after the and-not and the region legalisations

The test `regionExportableB` accepts the and-not legalisation `legalizeAndn p` of every
program `p` it accepts (`regionExportableB_legalizeAndn`, an instance of
`regionExportableB_legalizeBy`): the block of an and-not binds two operations
`regArith .and w` and `regArith .xor w` of the stack-memory fragment `opMemB`, and every other
binding is kept. The region legalisation `legalizeRegion` of every program of
`regionExportableRorB` passes the test (`regionExportableB_legalizeRegion`).

## Main results

* `coveredCom_andnBlock` — the block of a binding of `opMemB` binds operations of `opMemB`.
* `regionExportableB_legalizeAndn` — a program that passes `regionExportableB` passes it after
  the and-not legalisation.
* `regionExportableB_legalizeRegion` — a program of `regionExportableRorB` passes
  `regionExportableB` after the region legalisation.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regionExportableB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)

/-- **The block of a binding of `opMemB` binds operations of `opMemB` only.** -/
theorem coveredCom_andnBlock {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (h : opMemB e.op = true) :
    CoveredCom (fun e' => opMemB e'.op = true) (andnBlock e) := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | regArith bop w =>
      cases heq
      cases bop with
      | andn =>
          cases args with
          | cons a xs =>
              cases xs with
              | cons b ys =>
                  cases ys
                  rw [andnBlock]
                  exact ⟨rfl, rfl, trivial⟩
      | _ => exact ⟨h, trivial⟩
  | _ => exact ⟨h, trivial⟩

/-- **Completeness of the region export test after the and-not legalisation.** A program
    that passes `regionExportableB` passes it after `legalizeAndn`. -/
theorem regionExportableB_legalizeAndn {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (hp : regionExportableB p = true) :
    regionExportableB (legalizeAndn p) = true :=
  regionExportableB_legalizeBy coveredCom_andnBlock (fun _ h _ => h)
    ((regionExportableByB_opMemB p).trans hp)

/-- **Completeness of the region export test after the region legalisation.** A program
    whose bindings are operations of `opMemB` or in-range rotates, with the structural
    conditions of `regionExportableB` (`regionExportableRorB`), passes `regionExportableB`
    after `legalizeRegion`. -/
theorem regionExportableB_legalizeRegion {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (hp : regionExportableRorB p = true) :
    regionExportableB (legalizeRegion p) = true :=
  regionExportableB_legalizeAndn (regionExportableB_legalizeRor hp)

end CatCrypt.Crypto.SecureCompilation.Haxc
