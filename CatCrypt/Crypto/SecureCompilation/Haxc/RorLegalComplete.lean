/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RorLegal
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsAbi

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the region export test after the rotate legalisation

The test `regionExportableB` is complete, after the rotate legalisation `legalizeRor`, on the
programs whose bindings are operations of the stack-memory fragment `opMemB` or rotates by an
immediate `rorImm w k` with `0 < k < w` (`opMemRorB`), with the structural conditions of
`regionExportableB` on loops and calls (`regionExportableRorB`): every such program passes the
test after the legalisation (`regionExportableB_legalizeRor`), an instance of
`regionExportableB_legalizeBy`.

## Main definitions

* `rorInRangeB`, `opMemRorB` — the in-range rotates, and the operations of the fragment with
  them.
* `regionExportableRorB` — the test `regionExportableB` with `opMemRorB` in place of
  `opMemB` at the bindings.

## Main results

* `coveredCom_rorBlock` — the block of a binding of `opMemRorB` binds operations of `opMemB`.
* `regionExportableB_legalizeRor` — a program of `regionExportableRorB` passes
  `regionExportableB` after the legalisation.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regionExportableB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)

/-- The rotates by an immediate `rorImm w k` with `0 < k < w`. -/
def rorInRangeB : JasminOp → Bool
  | .rorImm w k => decide (0 < k ∧ k < w)
  | _ => false

/-- The operations of the stack-memory fragment `opMemB` and the in-range rotates. -/
def opMemRorB (op : JasminOp) : Bool := opMemB op || rorInRangeB op

/-- **The test `regionExportableB` with the in-range rotates**: `opMemRorB` in place of
    `opMemB` at the bindings. -/
def regionExportableRorB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : Bool :=
  regionExportableByB opMemRorB p

/-- **The block of a binding of `opMemRorB` binds operations of `opMemB` only.** -/
theorem coveredCom_rorBlock {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (h : opMemRorB e.op = true) :
    CoveredCom (fun e' => opMemB e'.op = true) (rorBlock e) := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | rorImm w k =>
      cases heq
      cases args with
      | cons x xs =>
          cases xs
          by_cases hk : 0 < k ∧ k < w
          · rw [rorBlock, ite_eq_left hk]
            have h2 : k < 2 ^ w := lt_trans hk.2 Nat.lt_two_pow_self
            have h3 : w - k < 2 ^ w := lt_of_le_of_lt (Nat.sub_le w k) Nat.lt_two_pow_self
            simp [shiftOrBlock, CoveredCom, opMemB, h2, h3]
          · rw [rorBlock, ite_eq_right hk]
            simp_all [opMemRorB, rorInRangeB, opMemB]
  | _ => simp_all [rorBlock, CoveredCom, opMemRorB, rorInRangeB]

/-- An operation of `opMemRorB` that is no rotate is an operation of `opMemB`. -/
theorem opMemB_of_opMemRorB {op : JasminOp} (h : opMemRorB op = true)
    (hn : isRorB op = false) : opMemB op = true := by
  cases op <;> simp_all [opMemRorB, rorInRangeB, isRorB]

/-- **Completeness of the region export test after the rotate legalisation.** A program
    whose bindings are operations of `opMemB` or in-range rotates, with the structural
    conditions of `regionExportableB` (`regionExportableRorB`), passes `regionExportableB`
    after `legalizeRor`. -/
theorem regionExportableB_legalizeRor {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (hp : regionExportableRorB p = true) :
    regionExportableB (legalizeRor p) = true :=
  regionExportableB_legalizeBy coveredCom_rorBlock (fun _ => opMemB_of_opMemRorB) hp

end CatCrypt.Crypto.SecureCompilation.Haxc
