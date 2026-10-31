/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsAbi

/-!
# The region export on the output of the chain

The test `regionExportableB` of the region export is the conjunction of three Boolean tests
on a structured program of `jasminDialect`: every operation of a binding is in the operation
set `opMemB` of the stack-memory fragment (`NFProg.allOps opMemB`), every exit-flag loop
carries register types (`whileRegB`), and every `call` is at a signature of `wordSig`
(`wordCalls`). On a program that passes the test, the export `exportR` returns code at every
depth, label and instruction set.

The range stage `rangeNF` keeps the tests `whileRegB` and `wordCalls`.

## Main definitions

* `whileRegB` — every exit-flag loop of a program carries register types.

## Main results

* `regVar?_isSome_of_var`, `bindMemNB_of_opMemB`, `opMemB_of_bindMemNB` — a binding passes
  `bindMemNB` exactly when its operation is in `opMemB`.
* `regionExportableB_eq` — `regionExportableB` is the conjunction of `allOps opMemB`,
  `whileRegB` and `wordCalls`.
* `wordCalls_of_regionExportableB`, `exportR_isSome_of_regionExportableB` — the export
  returns code on every program that passes `regionExportableB`.
* `whileRegB_rangeGo`, `wordCalls_rangeGo`, `structTests_rangeNF` — the range stage
  `rangeNF` keeps `whileRegB` and `wordCalls`.
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

/-- **`bindMemNB` is the test `opMemB` on the operation.** -/
theorem bindMemNB_eq {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    bindMemNB e = opMemB e.op := rfl

/-! ## 3. `regionExportableB` is the conjunction of the three tests -/

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

open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF (rangeGo rangeNF)

/-- The traversal of the range stage keeps `whileRegB`. -/
theorem whileRegB_rangeGo : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (p : NFProg jasminDialect Γ ts), whileRegB (rangeGo A len p) = whileRegB p
  | _, _, _, _, .ret _ => rfl
  | _, _, _, _, .var _ k => by simp only [rangeGo, whileRegB, whileRegB_rangeGo _ _ k]
  | _, _, _, _, .forLoop _ _ body k => by
      simp only [rangeGo, whileRegB, whileRegB_rangeGo _ _ body, whileRegB_rangeGo _ _ k]
  | _, _, _, _, .ifThenElse _ thn els k => by
      simp only [rangeGo, whileRegB, whileRegB_rangeGo _ _ thn, whileRegB_rangeGo _ _ els,
        whileRegB_rangeGo _ _ k]
  | _, _, _, _, .whileLoop _ body k => by
      simp only [rangeGo, whileRegB, whileRegB_rangeGo _ _ body, whileRegB_rangeGo _ _ k]
  | _, _, _, _, .call _ _ k => by simp only [rangeGo, whileRegB, whileRegB_rangeGo _ _ k]

/-- The traversal of the range stage keeps `wordCalls`. -/
theorem wordCalls_rangeGo : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (p : NFProg jasminDialect Γ ts), wordCalls (rangeGo A len p) = wordCalls p
  | _, _, _, _, .ret _ => rfl
  | _, _, _, _, .var _ k => by simp only [rangeGo, wordCalls, wordCalls_rangeGo _ _ k]
  | _, _, _, _, .forLoop _ _ body k => by
      simp only [rangeGo, wordCalls, wordCalls_rangeGo _ _ body, wordCalls_rangeGo _ _ k]
  | _, _, _, _, .ifThenElse _ thn els k => by
      simp only [rangeGo, wordCalls, wordCalls_rangeGo _ _ thn, wordCalls_rangeGo _ _ els,
        wordCalls_rangeGo _ _ k]
  | _, _, _, _, .whileLoop _ body k => by
      simp only [rangeGo, wordCalls, wordCalls_rangeGo _ _ body, wordCalls_rangeGo _ _ k]
  | _, _, _, _, .call _ _ k => by simp only [rangeGo, wordCalls, wordCalls_rangeGo _ _ k]

/-- The range stage keeps `whileRegB` and `wordCalls`. -/
theorem structTests_rangeNF {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    whileRegB (rangeNF p) = whileRegB p ∧ wordCalls (rangeNF p) = wordCalls p :=
  ⟨whileRegB_rangeGo _ _ p, wordCalls_rangeGo _ _ p⟩

end Range

end CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete
