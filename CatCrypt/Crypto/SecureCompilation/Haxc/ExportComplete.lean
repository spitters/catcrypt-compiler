/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsAbi
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportTests

/-!
# The region export on the output of the chain

The test `regionExportableB` of the region export is the conjunction of three Boolean tests
on a structured program of `jasminDialect`: every operation of a binding is in the operation
set `opMemB` of the stack-memory fragment (`NFProg.allOps opMemB`), every exit-flag loop
carries register types (`whileRegB`), and every `call` is at a signature of `wordSig`
(`wordCalls`). On a program that passes the test, the export `exportR` returns code at every
depth, label and instruction set.

The range stage `rangeNF` keeps the tests `whileRegB` and `wordCalls`.

The tests `whileRegB` and `regionExportableB_eq` are in `RegionExportTests`.

## Main results

* `regVar?_isSome_of_var`, `bindMemNB_of_opMemB`, `opMemB_of_bindMemNB` — a binding passes
  `bindMemNB` exactly when its operation is in `opMemB`.
* `wordCalls_of_regionExportableB`, `exportR_isSome_of_regionExportableB` — the export
  returns code on every program that passes `regionExportableB`.
* `whileRegB_carriedGo`, `wordCalls_carriedGo`, `structTests_synRange` — the range stage
  `synRange` keeps `whileRegB` and `wordCalls`, and so does its traversal at every
  annotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB scalarMemNB)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)

/-! ## 1. The tests -/


/-! ## 2. A binding passes `bindMemNB` exactly when its operation is in `opMemB` -/

/-- A context with a variable of a register type has a first register variable. -/
theorem regVar?_isSome_of_var : {Γ : Ctxt jasminDialect} → {w : Nat} →
    Ctxt.Var Γ (JasminTy.reg w) → (regVar? Γ).isSome = true
  | .reg _ :: _, _, _ => rfl
  | .stackArr _ _ :: Γ, _, v => by
      cases v with
      | there v => simpa [regVar?] using regVar?_isSome_of_var v
  | .inlineInt :: Γ, _, v => by
      cases v with
      | there v => simpa [regVar?] using regVar?_isSome_of_var v
  | .bool :: Γ, _, v => by
      cases v with
      | there v => simpa [regVar?] using regVar?_isSome_of_var v

/-- The program `scalarMemNB` reads for a binding: the binding followed by the return of a
    register variable passes `scalarMemNB` exactly when the operation is in `opMemB`. -/
theorem scalarMemNB_var_ret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (p : Σ w : Nat, Ctxt.Var (t :: Γ) (JasminTy.reg w)) :
    scalarMemNB (Com.var e (Com.ret p.2)) = opMemB e.op := by
  simp [scalarMemNB]

/-- **A binding whose operation is in `opMemB` passes `bindMemNB`** (the test is the
    operation's). -/
theorem bindMemNB_of_opMemB {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (h : opMemB e.op = true) : bindMemNB e = true := h

/-- A binding that passes `bindMemNB` has its operation in `opMemB`. -/
theorem opMemB_of_bindMemNB {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (h : bindMemNB e = true) : opMemB e.op = true := h


/-! ## 3. `regionExportableB` is the conjunction of the three tests -/


/-- A program that passes `regionExportableB` is a program of `wordCalls`. -/
theorem wordCalls_of_regionExportableB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : regionExportableB p = true) : wordCalls p = true := by
  rw [regionExportableB_eq] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- **The export returns code on every program that passes `regionExportableB`**, at every
    number of arguments, name, depth, label and instruction set. -/
theorem exportR_isSome_of_regionExportableB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : regionExportableB p = true) (nArgs : Nat)
    (fn : String) (d n : Nat) (I : IsaData) : (exportR nArgs fn p d n I).isSome = true :=
  Option.isSome_iff_exists.mpr
    ((exportR_eq_some_iff nArgs fn p d n).mpr (wordCalls_of_regionExportableB h))

/-! ## 4. The range stage keeps the structural tests -/

section Range

open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop (CarriedAnn carriedGo)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRange)

/-- The traversal of the range stage keeps `whileRegB`, at every annotation. -/
theorem whileRegB_carriedGo : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (a : CarriedAnn) (p : NFProg jasminDialect Γ ts),
    whileRegB (carriedGo A len a p) = whileRegB p
  | _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, .var _ k => by simp only [carriedGo, whileRegB, whileRegB_carriedGo _ _ _ k]
  | _, _, _, _, _, .forLoop _ _ body k => by
      simp only [carriedGo, whileRegB, whileRegB_carriedGo _ _ _ body,
        whileRegB_carriedGo _ _ _ k]
  | _, _, _, _, _, .ifThenElse _ thn els k => by
      simp only [carriedGo, whileRegB, whileRegB_carriedGo _ _ _ thn,
        whileRegB_carriedGo _ _ _ els, whileRegB_carriedGo _ _ _ k]
  | _, _, _, _, _, .whileLoop _ body k => by
      simp only [carriedGo, whileRegB, whileRegB_carriedGo _ _ _ body,
        whileRegB_carriedGo _ _ _ k]
  | _, _, _, _, _, .call _ _ k => by
      simp only [carriedGo, whileRegB, whileRegB_carriedGo _ _ _ k]

/-- The traversal of the range stage keeps `wordCalls`, at every annotation. -/
theorem wordCalls_carriedGo : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (a : CarriedAnn) (p : NFProg jasminDialect Γ ts),
    wordCalls (carriedGo A len a p) = wordCalls p
  | _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, .var _ k => by simp only [carriedGo, wordCalls, wordCalls_carriedGo _ _ _ k]
  | _, _, _, _, _, .forLoop _ _ body k => by
      simp only [carriedGo, wordCalls, wordCalls_carriedGo _ _ _ body,
        wordCalls_carriedGo _ _ _ k]
  | _, _, _, _, _, .ifThenElse _ thn els k => by
      simp only [carriedGo, wordCalls, wordCalls_carriedGo _ _ _ thn,
        wordCalls_carriedGo _ _ _ els, wordCalls_carriedGo _ _ _ k]
  | _, _, _, _, _, .whileLoop _ body k => by
      simp only [carriedGo, wordCalls, wordCalls_carriedGo _ _ _ body,
        wordCalls_carriedGo _ _ _ k]
  | _, _, _, _, _, .call _ _ k => by
      simp only [carriedGo, wordCalls, wordCalls_carriedGo _ _ _ k]

/-- The range stage keeps `whileRegB` and `wordCalls`. -/
theorem structTests_synRange {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    whileRegB (synRange p) = whileRegB p ∧ wordCalls (synRange p) = wordCalls p :=
  ⟨whileRegB_carriedGo _ _ _ p, wordCalls_carriedGo _ _ _ p⟩

end Range

end CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete
