/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCellNames

/-!
# The entry check on the field domain

The stage `entryB` of the region gate reads the layout and the frame names of the printed
body: no argument name is a general-purpose name or has a frame word; the register of each
parameter is named by its general-purpose name, without a frame word; the save slot
`qsave.R` of the register `R` of each array parameter has a frame word; the regions of the
layout are its array parameters, of at most `2 ^ 61` words, in distinct registers, each of
the length of its parameter; and no move of the body reads a stack-argument name.

On `fieldDomB'` the layout is `fieldAbi k n` with `k ∈ {1, 2}` and `n < 2 ^ 60`: its
parameters are in `%rdi`, `%rsi` and `%rdx`, whose general-purpose names `RDI`, `RSI`, `RDX`
begin with `R`, as the argument names `a<j>` begin with `a`, so neither is a spill, save or
frame-array name, and neither has a frame word in any body. The two conditions read off the
printed body are its prologue facts (`EntryPrologue`): the save slot of the register of each
parameter is a frame name of the body, and no move of the body reads a stack-argument name.

## Main definitions

* `EntryPrologue` — the prologue facts of the printed body that the entry check reads.

## Main results

* `not_mem_frameNames` — a name that begins with none of `k`, `q`, `f` has no frame word.
* `entryB_fieldAbi` — the entry check passes under `fieldAbi k n` on a body with the prologue
  facts.
* `fieldDom_entryB` — the stage `G19` on `fieldDomB'` under `EntryPrologue`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryB stackReadFreeB rsOf
  stackArgB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameNames frameMark bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpList phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (regLen)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi fieldArgReg)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-! ## 1. Names without a frame word -/

/-- A string whose first character differs from that of a nonempty pattern does not have the
    pattern as a prefix. -/
theorem hasPrefix_of_head_ne {q p : String} {c d : Char} (hq : q.toList.head? = some c)
    (hp : p.toList.head? = some d) (hcd : c ≠ d) : hasPrefix q p = false := by
  unfold hasPrefix
  cases hpl : p.toList with
  | nil => rw [hpl] at hp; cases hp
  | cons d' l =>
    cases hql : q.toList with
    | nil => rw [hql] at hq; cases hq
    | cons c' l' =>
      rw [hpl] at hp
      rw [hql] at hq
      simp only [List.head?_cons, Option.some.injEq] at hp hq
      subst hp hq
      simp only [List.isPrefixOf, Bool.and_eq_false_imp, beq_iff_eq]
      exact fun h => absurd h.symm hcd

/-- **A name that begins with none of `k`, `q`, `f` has no frame word** in any body: it is
    no spill, save or frame-array name. -/
theorem not_mem_frameNames {q : String} {c : Char} (hq : q.toList.head? = some c)
    (hk : c ≠ 'k') (hs : c ≠ 'q') (hf : c ≠ 'f') (body : Lcmd) : q ∉ frameNames body := by
  intro hm
  unfold frameNames at hm
  have hp := (List.mem_filter.mp hm).2
  have h1 : hasPrefix q "k." = false := hasPrefix_of_head_ne hq (by decide) hk
  have h2 : hasPrefix q "qsave." = false := hasPrefix_of_head_ne hq (by decide) hs
  have h3 : hasPrefix q "fa." = false := hasPrefix_of_head_ne hq (by decide) hf
  simp [X86Backend.LprogBytes.spillQsaveOff, faParts?, h1, h2, h3] at hp

/-- The frame map of a body gives no word to a name without a frame word. -/
theorem frameMark_none {q : String} {body : Lcmd} (h : q ∉ frameNames body) :
    frameMark (frameNames body) q = none := by
  simp [frameMark, h]

/-! ## 2. The entry check under the field layout -/

/-- **The prologue facts of the printed body that the entry check reads**: the save slot
    `qsave.R` of the register `R` of each parameter of `σ` is a frame name of `b`, and no move
    of `b` reads a stack-argument name. -/
def EntryPrologue (σ : AbiLayout) (b : Lcmd) : Prop :=
  (∀ a ∈ σ.args, slotOfReg (exportReg a.reg) ∈ frameNames b) ∧ stackReadFreeB b = true

/-- **The entry check passes under `fieldAbi k n`** at `k ∈ {1, 2}` and `n ≤ 2 ^ 61` on a
    printed body with the prologue facts. -/
theorem entryB_fieldAbi {k n : Nat} (hk : k = 1 ∨ k = 2) (hn : n ≤ 2 ^ 61)
    (hP : EntryPrologue (fieldAbi k n) b) : entryB (fieldAbi k n) exportReg b = true := by
  obtain ⟨hq, hs⟩ := hP
  have hfr : ∀ q c, q.toList.head? = some c → c ≠ 'k' → c ≠ 'q' → c ≠ 'f' →
      frameMark (frameNames b) q = none := fun q c h1 h2 h3 h4 =>
    frameMark_none (not_mem_frameNames h1 h2 h3 h4 b)
  have hsl : ∀ a ∈ (fieldAbi k n).args,
      (frameMark (frameNames b) (slotOfReg (exportReg a.reg))).isSome = true := by
    intro a ha
    simp [frameMark, hq a ha]
  have e0 : argName 0 = "a0" := by decide
  have e1 : argName 1 = "a1" := by decide
  have e2 : argName 2 = "a2" := by decide
  have x0 : exportReg "%rdi" = "RDI" := by decide
  have x1 : exportReg "%rsi" = "RSI" := by decide
  have x2 : exportReg "%rdx" = "RDX" := by decide
  have p0 : phys "RDI" = "%rdi" := by decide
  have p1 : phys "RSI" = "%rsi" := by decide
  have p2 : phys "RDX" = "%rdx" := by decide
  have g0 : gpOk "RDI" = true := by decide
  have g1 : gpOk "RSI" = true := by decide
  have g2 : gpOk "RDX" = true := by decide
  have ga0 : gpOk "a0" = false := by decide
  have ga1 : gpOk "a1" = false := by decide
  have ga2 : gpOk "a2" = false := by decide
  have f0 := hfr "a0" 'a' rfl (by decide) (by decide) (by decide)
  have f1 := hfr "a1" 'a' rfl (by decide) (by decide) (by decide)
  have f2 := hfr "a2" 'a' rfl (by decide) (by decide) (by decide)
  have fr0 := hfr "RDI" 'R' rfl (by decide) (by decide) (by decide)
  have fr1 := hfr "RSI" 'R' rfl (by decide) (by decide) (by decide)
  have fr2 := hfr "RDX" 'R' rfl (by decide) (by decide) (by decide)
  rcases hk with rfl | rfl
  · have s0 := hsl ⟨"out", "%rdi", .words n⟩ (by simp [fieldAbi, List.range_succ,
      fieldArgReg, FieldRoute.fieldArgName])
    have s1 := hsl ⟨"x", "%rsi", .words n⟩ (by simp [fieldAbi, List.range_succ,
      fieldArgReg, FieldRoute.fieldArgName])
    simp only [entryB, Bool.and_eq_true, hs, and_true]
    simp [fieldAbi, List.range_succ, fieldArgReg, FieldRoute.fieldArgName,
      X86Backend.DecodeGenNode.rsOK, rsOf, X86Backend.DecodeGenNode.abiArgOf,
      X86Backend.DecodeGenNode.abiReg, regLen, X86Backend.DecodeGenMem.regFind,
      e0, e1, x0, x1, p0, p1, g0, g1, ga0, ga1, f0, f1, fr0, fr1]
    exact ⟨⟨by simpa [x0] using s0, by simpa [x1] using s1⟩, by omega⟩
  · have s0 := hsl ⟨"out", "%rdi", .words n⟩ (by simp [fieldAbi, List.range_succ,
      fieldArgReg, FieldRoute.fieldArgName])
    have s1 := hsl ⟨"y", "%rsi", .words n⟩ (by simp [fieldAbi, List.range_succ,
      fieldArgReg, FieldRoute.fieldArgName])
    have s2 := hsl ⟨"x", "%rdx", .words n⟩ (by simp [fieldAbi, List.range_succ,
      fieldArgReg, FieldRoute.fieldArgName])
    simp only [entryB, Bool.and_eq_true, hs, and_true]
    simp [fieldAbi, List.range_succ, fieldArgReg, FieldRoute.fieldArgName,
      X86Backend.DecodeGenNode.rsOK, rsOf, X86Backend.DecodeGenNode.abiArgOf,
      X86Backend.DecodeGenNode.abiReg, regLen, X86Backend.DecodeGenMem.regFind,
      e0, e1, e2, x0, x1, x2, p0, p1, p2, g0, g1, g2, ga0, ga1, ga2, f0, f1, f2, fr0, fr1, fr2]
    exact ⟨⟨by simpa [x0] using s0, by simpa [x1] using s1, by simpa [x2] using s2⟩, by omega⟩

/-! ## 3. The stage `G19` -/

/-- The gate does not refuse at `entryB` when the entry check accepts. -/
theorem regionCoStage_ne_entryB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String} (h : entryB σ nm b = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "entryB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- A field expression has one or two distinct operands. -/
theorem fieldDomE_k {k n : Nat} (h : fieldDomE e = some (k, n)) : k = 1 ∨ k = 2 := by
  obtain ⟨m, p, hm, -⟩ := fieldDomE_wide h
  simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  omega

/-- **Stage `G19` on `fieldDomB'`**: the gate does not refuse at the entry check, when the
    printed body has the prologue facts. -/
theorem fieldDom_entryB (h : fieldDomB' e σ = true) (_hB : FieldBody e σ fname b t r cert)
    (hP : EntryPrologue σ b) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "entryB" := by
  obtain ⟨k, n, hE, rfl, hn⟩ := fieldDomB'_layout h
  exact regionCoStage_ne_entryB (entryB_fieldAbi (fieldDomE_k hE) (by omega) hP)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
