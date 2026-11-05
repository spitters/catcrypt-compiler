/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsAbi
public import CatCrypt.Crypto.Hax.NFInline

/-!
# The three tests of the region export

The test `regionExportableB` of the region export is the conjunction of three Boolean tests
on a structured program of `jasminDialect`: every operation of a binding is in the operation
set `opMemB` (`NFProg.allOps opMemB`), every exit-flag loop carries register types
(`whileRegB`), and every `call` is at a signature of `wordSig` (`wordCalls`).

## Main definitions

* `whileRegB` — every exit-flag loop of a program carries register types.

## Main results

* `bindMemNB_eq` — `bindMemNB` is the test `opMemB` on the operation.
* `regionExportableB_eq` — `regionExportableB` is the conjunction of `allOps opMemB`,
  `whileRegB` and `wordCalls`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)

/-- Every exit-flag loop of the program carries register types (`isRegTy`), in every region
    and continuation. -/
def whileRegB : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => whileRegB k
  | _, _, .forLoop _ _ body k => whileRegB body && whileRegB k
  | _, _, .ifThenElse _ thn els k => whileRegB thn && whileRegB els && whileRegB k
  | _, _, .whileLoop (cs := cs) _ body k => cs.all isRegTy && whileRegB body && whileRegB k
  | _, _, .call _ _ k => whileRegB k

/-- **`bindMemNB` is the test `opMemB` on the operation.** -/
theorem bindMemNB_eq {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    bindMemNB e = opMemB e.op := rfl

/-- **`regionExportableB` is the conjunction of the three tests**: the operations of the
    bindings are in `opMemB`, the exit-flag loops carry register types and the calls are at
    signatures of `wordSig`. -/
theorem regionExportableB_eq {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    regionExportableB p = (p.allOps opMemB && whileRegB p && wordCalls p) := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [regionExportableB, NFProg.allOps, whileRegB, wordCalls, ih, bindMemNB_eq]
      cases opMemB e.op <;> simp
  | forLoop count inits body k ihb ihk =>
      simp only [regionExportableB, NFProg.allOps, whileRegB, wordCalls, ihb, ihk]
      cases NFProg.allOps opMemB body <;> cases whileRegB body <;> cases wordCalls body <;>
        simp
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [regionExportableB, NFProg.allOps, whileRegB, wordCalls, iht, ihe, ihk]
      cases NFProg.allOps opMemB thn <;> cases whileRegB thn <;> cases wordCalls thn <;>
        cases NFProg.allOps opMemB els <;> cases whileRegB els <;> cases wordCalls els <;> simp
  | whileLoop inits body k ihb ihk =>
      simp only [regionExportableB, NFProg.allOps, whileRegB, wordCalls, ihb, ihk]
      cases NFProg.allOps opMemB body <;> cases whileRegB body <;> cases wordCalls body <;>
        cases List.all _ isRegTy <;> simp
  | call f args k ih =>
      simp only [regionExportableB, NFProg.allOps, whileRegB, wordCalls, ih]
      cases NFProg.allOps opMemB k <;> cases whileRegB k <;> cases wordCalls k <;> simp

end CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete
