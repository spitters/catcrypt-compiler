/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopJ
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopJ
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the export certificate checks

The export step of the back half accepts a looped program only when its certificate check
returns `true`: `ExportCertLoopBody.comLCertNB` for a single runtime-count loop over an array
accumulator, and `ExportCertLoopJ.exportCertJB` (through `singleLoopJB`) for a counted loop
carrying an array and registers. This module states, for each check, a decidable fragment of
source programs and proves that the check accepts every program of the fragment.

Both fragments rest on the linear store thread `threadLinB`: every array load reads the
current version of the carried array or an invariant array, every array store writes into the
current version and its result becomes the current version, and the body returns the current
version. On such a body the model chain `straightOpsMem` passes `threadCertB` and
`storeOnHeadB` (`threadCertB_of_threadLinB`, `storeOnHeadB_of_threadLinB`). The carried-register
fragment adds a condition on the returned tuple (`retOKB`) under which the export's feedback
needs no staging, so the seeds and the feedback decode to checked register-move lists.

## Main definitions

* `threadLinB` — the linear store thread of a body.
* `loopFragB` — the single-loop fragment.
* `loopFragJB` — the carried-register fragment.

## Main results

* `threadCertB_of_threadLinB` — the thread certificate of a linear body.
* `comLCertNB_complete` — `comLCertNB` accepts every program of `loopFragB`.
* `exportCertJB_complete`, `singleLoopJB_complete` — `exportCertJB` and its gate accept every
  program of `loopFragJB`.
* `loopFragB_mpn_and_n`, `loopFragJB_mpn_and_n` — the front-generated `mpn_and_n` loop lies in
  both fragments.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag straightOpsMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (storeHit? arrUse? useNames
  defNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (ne_of_head? head?_argName
  head?_regName head?_loopReg head?_loopCtr exprArgs_isReg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
  (argName_injective regName_injective regName_ne_argName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody (chainElem storeOnHeadB)

/-! ## 1. Slots and their names -/

/-- The root slot of a variable at depth `cd`: the binder `cd - 1 - varIndex v` counted from
    the bottom of the context. -/
abbrev slotOf {Γ : Ctxt jasminDialect} {τ : JasminTy} (cd : Nat) (v : Ctxt.Var Γ τ) : Nat :=
  cd - 1 - varIndex v

/-- The slot of the first variable of a vector, `none` for the empty vector. -/
def firstSlot? {Γ : Ctxt jasminDialect} (cd : Nat) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → Option Nat
  | [], _ => none
  | _ :: _, .cons v _ => some (slotOf cd v)

/-- The export's name of slot `s` with `nArgs` arguments: an argument name below `nArgs`, a
    chain register above. -/
def nameAt (nArgs s : Nat) : String := if s < nArgs then argName s else regName s

theorem resolveVar_eq_nameAt (cd nArgs : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    resolveVar cd nArgs argName (fun _ => none) v = .reg (nameAt nArgs (slotOf cd v)) := by
  unfold resolveVar nameAt
  by_cases h : slotOf cd v < nArgs <;> simp [h]

theorem nameAt_injective (nArgs : Nat) : Function.Injective (nameAt nArgs) := by
  intro s s' h
  unfold nameAt at h
  split at h <;> split at h
  · exact argName_injective h
  · exact absurd h.symm (regName_ne_argName _ _)
  · exact absurd h (regName_ne_argName _ _)
  · exact regName_injective h

theorem nameAt_head? (nArgs s : Nat) : (nameAt nArgs s).toList.head? ≠ some 'L' := by
  unfold nameAt
  split
  · rw [head?_argName]; decide
  · rw [head?_regName]; decide

/-! ## 2. One binding of the model chain -/

/-- A register binding of the fragment's op set writes its slot register, reads only names of
    its operands, and is neither a store nor an array read. -/
theorem chainElem_reg {op : JasminOp} (hop : opMemB op = true)
    (hs : ∀ w n, op ≠ .stackStore w n) (hl : ∀ w n, op ≠ .stackLoad w n) (cd : Nat)
    (src : List LOperand) :
    storeHit? (chainElem op cd src) = none ∧ arrUse? (chainElem op cd src) = none
      ∧ defNames (chainElem op cd src).1 = [regName cd]
      ∧ ∀ x ∈ useNames (chainElem op cd src).1, ∃ o ∈ src, x ∈ opNames o := by
  cases op <;> simp only [opMemB, Bool.false_eq_true] at hop
  all_goals first
    | exact absurd rfl (hs _ _)
    | exact absurd rfl (hl _ _)
    | skip
  all_goals
    simp only [chainElem, storeHit?, arrUse?]
    (repeat' split) <;>
      simp_all [opToLinstrR, defNames, useNames, opNames, JasminLsemShift.shiftLinstr]
  all_goals
    split_ifs <;> exact ⟨by simp [opNames], fun x hx => List.mem_flatMap.mp hx⟩

theorem exprArgs_go_cons (cd nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    {tys : List JasminTy} (v : Ctxt.Var Γ t) (rest : HVector (fun ty => Ctxt.Var Γ ty) tys) :
    exprArgs.go cd nArgs argName (fun _ => none) (.cons v rest)
      = .reg (nameAt nArgs (slotOf cd v)) :: exprArgs.go cd nArgs argName (fun _ => none) rest
  := by
  rw [← resolveVar_eq_nameAt]; rfl

theorem exprArgs_go_nil (cd nArgs : Nat) {Γ : Ctxt jasminDialect} :
    exprArgs.go cd nArgs argName (fun _ => none)
      (HVector.nil : HVector (fun ty => Ctxt.Var Γ ty) []) = [] := rfl

/-- Every operand of a resolved vector is the register of a slot below the depth. -/
theorem exprArgs_go_nameAt (cd nArgs : Nat) (hcd : 0 < cd) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ exprArgs.go cd nArgs argName (fun _ => none) hv,
        ∃ s, s < cd ∧ o = .reg (nameAt nArgs s)
  | [], .nil => by
      intro o ho
      rw [exprArgs_go_nil] at ho
      cases ho
  | _ :: _, .cons v rest => by
      intro o ho
      rw [exprArgs_go_cons, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨slotOf cd v, by show cd - 1 - varIndex v < cd; omega, rfl⟩
      · exact exprArgs_go_nameAt cd nArgs hcd rest o ho

/-- The operands of an array load: the array slot and the index slot. -/
theorem exprArgs_load (cd nArgs : Nat) {Γ : Ctxt jasminDialect} {w n : Nat} {τ : JasminTy}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackLoad w n) = τ)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackLoad w n))) :
    ∃ a b, exprArgs cd nArgs argName (fun _ => none)
        (⟨JasminOp.stackLoad w n, heq, args⟩ : Expr jasminDialect Γ τ)
        = [.reg (nameAt nArgs a), .reg (nameAt nArgs b)]
      ∧ firstSlot? cd args = some a := by
  match args with
  | .cons x (.cons y .nil) =>
      exact ⟨slotOf cd x, slotOf cd y, by
        show [resolveVar cd nArgs argName (fun _ => none) x,
          resolveVar cd nArgs argName (fun _ => none) y] = _
        rw [resolveVar_eq_nameAt, resolveVar_eq_nameAt], rfl⟩

/-- The operands of an array store: the array slot, the index slot and the value slot. -/
theorem exprArgs_store (cd nArgs : Nat) {Γ : Ctxt jasminDialect} {w n : Nat} {τ : JasminTy}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore w n) = τ)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackStore w n))) :
    ∃ a b c, exprArgs cd nArgs argName (fun _ => none)
        (⟨JasminOp.stackStore w n, heq, args⟩ : Expr jasminDialect Γ τ)
        = [.reg (nameAt nArgs a), .reg (nameAt nArgs b), .reg (nameAt nArgs c)]
      ∧ firstSlot? cd args = some a := by
  match args with
  | .cons x (.cons y (.cons z .nil)) =>
      exact ⟨slotOf cd x, slotOf cd y, slotOf cd z, by
        show [resolveVar cd nArgs argName (fun _ => none) x,
          resolveVar cd nArgs argName (fun _ => none) y,
          resolveVar cd nArgs argName (fun _ => none) z] = _
        rw [resolveVar_eq_nameAt, resolveVar_eq_nameAt, resolveVar_eq_nameAt], rfl⟩

/-- Every store slot of a chain from depth `cd` is at least `cd`. -/
theorem le_of_mem_storeSlots : ∀ {L : List LinstrRM} {cd k : Nat}, k ∈ storeSlots L cd → cd ≤ k
  | [], _, _, h => by simp [storeSlots] at h
  | i :: is, cd, k, h => by
      simp only [storeSlots, List.mem_append] at h
      rcases h with h | h
      · split at h
        · simp at h; omega
        · simp at h
      · have := le_of_mem_storeSlots h; omega

/-- A slot name below the depth is resolved. -/
theorem resolvedB_nameAt {nArgs cd s : Nat} (hs : s < cd) :
    resolvedB nArgs cd (nameAt nArgs s) = true := by
  unfold resolvedB nameAt
  split
  · simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range]
    exact Or.inl (Or.inr ⟨s, by assumption, rfl⟩)
  · simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨s, hs, by omega, rfl⟩

/-! ## 3. The linear store thread -/

/-- **The linear store thread of a body**, from depth `cd` with the thread head at slot `h`
    and `nInv` invariants (slots below `nInv`): every binding's op lies in `opMemB`; an array
    load reads the head or an invariant; an array store writes into the head and its result
    becomes the head; the body returns the head. -/
def threadLinB (nInv : Nat) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (cd h : Nat) → Bool
  | _, _, .ret v, cd, h => slotOf cd v == h
  | _, _, .var e body, cd, h =>
      opMemB e.op && match e.op with
        | .stackLoad _ _ => (firstSlot? cd e.args == some h
              || (firstSlot? cd e.args).any (· < nInv)) && threadLinB nInv body (cd + 1) h
        | .stackStore _ _ => firstSlot? cd e.args == some h && threadLinB nInv body (cd + 1) cd
        | _ => threadLinB nInv body (cd + 1) h

/-- The store-slot list seen from one instruction further. -/
theorem storeSlots_step {i : LinstrRM} {rest : List LinstrRM} {cd : Nat} {Sl : List Nat}
    (hSl : ∀ k, cd ≤ k → (k ∈ Sl ↔ k ∈ storeSlots (i :: rest) cd)) :
    Sl.contains cd = (storeHit? i).isSome
      ∧ ∀ k, cd + 1 ≤ k → (k ∈ Sl ↔ k ∈ storeSlots rest (cd + 1)) := by
  refine ⟨?_, fun k hk => ?_⟩
  · have h := hSl cd (Nat.le_refl _)
    simp only [storeSlots, List.mem_append] at h
    have hn : cd ∉ storeSlots rest (cd + 1) := fun hm => by
      have := le_of_mem_storeSlots hm; omega
    cases hs : (storeHit? i).isSome
    · simp only [hs, Bool.false_eq_true, if_false, List.not_mem_nil, false_or] at h
      simpa [List.contains_iff_mem] using fun hm => hn (h.mp hm)
    · simpa [List.contains_iff_mem] using h.mpr (by simp [hs])
  · rw [hSl k (by omega)]
    simp only [storeSlots, List.mem_append]
    constructor
    · rintro (h | h)
      · split at h <;> simp at h; omega
      · exact h
    · exact Or.inr

/-- A register binding passes one step of the thread certificate. -/
theorem threadCertB_cons_reg (tauC : String → Option String) (nArgs : Nat) (out : String)
    {op : JasminOp} (hop : opMemB op = true) (hs : ∀ w n, op ≠ .stackStore w n)
    (hl : ∀ w n, op ≠ .stackLoad w n) {cd : Nat} {src : List LOperand}
    (hsrc : ∀ o ∈ src, ∃ s, s < cd ∧ o = .reg (nameAt nArgs s)) {Sl : List Nat}
    (hcd : Sl.contains cd = false) (rest : List LinstrRM) (h hE : String) :
    threadCertB tauC nArgs Sl out (chainElem op cd src :: rest) cd h hE
      = threadCertB tauC nArgs Sl out rest (cd + 1) h hE := by
  obtain ⟨h1, h2, h3, h4⟩ := chainElem_reg hop hs hl cd src
  have hall : (useNames (chainElem op cd src).1).all (resolvedB nArgs cd) = true := by
    refine List.all_eq_true.mpr fun x hx => ?_
    obtain ⟨o, ho, hx⟩ := h4 x hx
    obtain ⟨s, hs, rfl⟩ := hsrc o ho
    simp only [opNames, List.mem_singleton] at hx
    subst hx
    exact resolvedB_nameAt hs
  simp only [threadCertB, hall, h1, h2, h3, hcd, Bool.true_and, beq_self_eq_true,
    Bool.not_false]

/-- **The thread certificate of a linear body.** The model chain of a body on the linear store
    thread from head slot `h` passes `threadCertB` from the head's name to the returned name,
    for every store-slot list that agrees with the chain's store slots from depth `cd`, and for
    every computed renaming that sends each invariant argument somewhere other than `out`. -/
theorem threadCertB_of_threadLinB (tauC : String → Option String) (nArgs nInv : Nat)
    (out : String) (hpos : 0 < nArgs) (hinv : nInv ≤ nArgs)
    (htau : ∀ j, j < nInv → ∃ t, tauC (argName j) = some t ∧ t ≠ out) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) (cd h : Nat)
      (Sl : List Nat), threadLinB nInv c cd h = true → nArgs ≤ cd →
      (∀ k, cd ≤ k → (k ∈ Sl ↔ k ∈ storeSlots (straightOpsMem nArgs c cd) cd)) →
      threadCertB tauC nArgs Sl out (straightOpsMem nArgs c cd) cd (nameAt nArgs h)
        (comRetReg nArgs argName c cd) = true
  | _, _, .ret v, cd, h, Sl, hl, _, _ => by
      simp only [threadLinB, beq_iff_eq] at hl
      simp only [straightOpsMem, threadCertB, comRetReg, resolveVar_eq_nameAt, hl,
        beq_self_eq_true]
  | _, _, .var ⟨op, heq, args⟩ body, cd, h, Sl, hl, hcd, hSl => by
      rw [ExportCertLoopBody.straightOpsMem_var] at hSl ⊢
      obtain ⟨hcont, hSl'⟩ := storeSlots_step hSl
      have hsrc : ∀ o ∈ exprArgs cd nArgs argName (fun _ => none)
          (⟨op, heq, args⟩ : Expr jasminDialect _ _), ∃ s, s < cd ∧ o = .reg (nameAt nArgs s) :=
        exprArgs_go_nameAt cd nArgs (by omega) args
      have hret : comRetReg nArgs argName (.var ⟨op, heq, args⟩ body) cd
          = comRetReg nArgs argName body (cd + 1) := rfl
      rw [hret]
      simp only [threadLinB, Bool.and_eq_true] at hl
      obtain ⟨hop, hl⟩ := hl
      cases op <;> simp only [opMemB, Bool.false_eq_true] at hop
      case stackLoad w n =>
        obtain ⟨a, b, hargs, hfa⟩ := exprArgs_load cd nArgs heq args
        simp only [hfa, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.some.injEq,
          Option.any_some, decide_eq_true_eq] at hl
        obtain ⟨hh, hl⟩ := hl
        have hlt : ∀ s, LOperand.reg (nameAt nArgs s) ∈ exprArgs cd nArgs argName
            (fun _ => none) (⟨JasminOp.stackLoad w n, heq, args⟩ : Expr jasminDialect _ _) →
            s < cd := by
          intro s hm
          obtain ⟨s', hs', he⟩ := hsrc _ hm
          simp only [LOperand.reg.injEq] at he
          rw [nameAt_injective nArgs he]; exact hs'
        have hsa := hlt a (by rw [hargs]; simp)
        have hsb := hlt b (by rw [hargs]; simp)
        rw [hargs] at hcont ⊢
        have hc : Sl.contains cd = false := by rw [hcont]; rfl
        have ih := threadCertB_of_threadLinB tauC nArgs nInv out hpos hinv htau body (cd + 1) h
          Sl hl (by omega) hSl'
        have hA : (nameAt nArgs a == nameAt nArgs h
            || (match tauC (nameAt nArgs a) with | some t => t != out | none => false))
            = true := by
          rcases hh with rfl | hi
          · simp
          · obtain ⟨t, ht, hto⟩ := htau a hi
            have : nameAt nArgs a = argName a := by unfold nameAt; rw [if_pos (by omega)]
            rw [this, ht]
            simp [hto]
        show threadCertB tauC nArgs Sl out
          ((.Lopn [.reg (regName cd)] "LOADIDX" [.arrIdx (nameAt nArgs a) (nameAt nArgs b)
            (w / 8)], .load w n) :: _) cd _ _ = true
        simp only [threadCertB, useNames, opNames, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.all_cons, List.all_nil,
          resolvedB_nameAt hsa, resolvedB_nameAt hsb,
          arrUse?, JasminLsemMem.loadStruct?, if_true, Option.map_some, storeHit?, defNames,
          hc, ih, Bool.and_true, Bool.true_and, beq_self_eq_true, Bool.not_false]
        exact hA
      case stackStore w n =>
        obtain ⟨a, b, c, hargs, hfa⟩ := exprArgs_store cd nArgs heq args
        simp only [hfa, Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hl
        obtain ⟨hh, hl⟩ := hl
        have hlt : ∀ s, LOperand.reg (nameAt nArgs s) ∈ exprArgs cd nArgs argName
            (fun _ => none) (⟨JasminOp.stackStore w n, heq, args⟩ : Expr jasminDialect _ _) →
            s < cd := by
          intro s hm
          obtain ⟨s', hs', he⟩ := hsrc _ hm
          simp only [LOperand.reg.injEq] at he
          rw [nameAt_injective nArgs he]; exact hs'
        have hsa := hlt a (by rw [hargs]; simp)
        have hsb := hlt b (by rw [hargs]; simp)
        have hsc := hlt c (by rw [hargs]; simp)
        subst hh
        rw [hargs] at hcont ⊢
        have hc : Sl.contains cd = true := by rw [hcont]; rfl
        have ih := threadCertB_of_threadLinB tauC nArgs nInv out hpos hinv htau body (cd + 1) cd
          Sl hl (by omega) hSl'
        have hcd' : nameAt nArgs cd = regName cd := by
          unfold nameAt; rw [if_neg (by omega)]
        rw [hcd'] at ih
        show threadCertB tauC nArgs Sl out
          ((.Lopn [.reg (regName cd)] "STOREIDX" [.arrIdx (nameAt nArgs a) (nameAt nArgs b)
            (w / 8), .reg (nameAt nArgs c)], .store w n) :: _) cd _ _ = true
        simp only [threadCertB, useNames, opNames, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.cons_append, List.nil_append, List.all_cons, List.all_nil,
          resolvedB_nameAt hsa, resolvedB_nameAt hsb, resolvedB_nameAt hsc, arrUse?,
          JasminLsemMem.storeStruct?, if_true, Option.map_some, storeHit?, hc, ih,
          Bool.and_true, beq_self_eq_true, Bool.true_or]
      all_goals
        rw [threadCertB_cons_reg tauC nArgs out (by simp_all [opMemB]) (by simp)
          (by simp) hsrc (by simpa [storeHit?, chainElem] using hcont)]
        exact threadCertB_of_threadLinB tauC nArgs nInv out hpos hinv htau body (cd + 1) h Sl
          hl (by omega) hSl'

/-- The slot of the variable a body returns. -/
def retSlot : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Nat → Nat
  | _, _, .ret v, cd => slotOf cd v
  | _, _, .var _ body, cd => retSlot body (cd + 1)

/-- **Stores on the head, and the returned slot.** The model chain of a body on the linear
    store thread passes `storeOnHeadB` from the head's name, and the body returns the head
    or a store slot of its chain. -/
theorem storeOnHeadB_of_threadLinB (nArgs nInv : Nat) (hpos : 0 < nArgs) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) (cd h : Nat),
      threadLinB nInv c cd h = true → nArgs ≤ cd →
      storeOnHeadB (straightOpsMem nArgs c cd) (nameAt nArgs h) = true
        ∧ (retSlot c cd = h ∨ retSlot c cd ∈ storeSlots (straightOpsMem nArgs c cd) cd)
  | _, _, .ret v, cd, h, hl, _ => by
      simp only [threadLinB, beq_iff_eq] at hl
      exact ⟨rfl, Or.inl hl⟩
  | _, _, .var ⟨op, heq, args⟩ body, cd, h, hl, hcd => by
      rw [ExportCertLoopBody.straightOpsMem_var]
      have hr : retSlot (.var ⟨op, heq, args⟩ body) cd = retSlot body (cd + 1) := rfl
      rw [hr]
      simp only [threadLinB, Bool.and_eq_true] at hl
      obtain ⟨hop, hl⟩ := hl
      have hreg : threadLinB nInv body (cd + 1) h = true →
          storeHit? (chainElem op cd (exprArgs cd nArgs argName (fun _ => none)
            (⟨op, heq, args⟩ : Expr jasminDialect _ _))) = none →
          storeOnHeadB (chainElem op cd (exprArgs cd nArgs argName (fun _ => none)
              (⟨op, heq, args⟩ : Expr jasminDialect _ _)) :: straightOpsMem nArgs body (cd + 1))
              (nameAt nArgs h) = true
            ∧ (retSlot body (cd + 1) = h ∨ retSlot body (cd + 1) ∈ storeSlots
              (chainElem op cd (exprArgs cd nArgs argName (fun _ => none)
                (⟨op, heq, args⟩ : Expr jasminDialect _ _)) :: straightOpsMem nArgs body (cd + 1))
              cd) := by
        intro hl' hn
        obtain ⟨ih1, ih2⟩ := storeOnHeadB_of_threadLinB nArgs nInv hpos body (cd + 1) h hl'
          (by omega)
        refine ⟨by simp only [storeOnHeadB, hn]; exact ih1, ?_⟩
        simp only [storeSlots, hn, Option.isSome_none, Bool.false_eq_true, if_false,
          List.nil_append]
        exact ih2
      cases op <;> simp only [opMemB, Bool.false_eq_true] at hop
      case stackLoad w n =>
        obtain ⟨a, b, hargs, hfa⟩ := exprArgs_load cd nArgs heq args
        simp only [Bool.and_eq_true] at hl
        exact hreg hl.2 (by rw [hargs]; rfl)
      case stackStore w n =>
        obtain ⟨a, b, c, hargs, hfa⟩ := exprArgs_store cd nArgs heq args
        simp only [hfa, Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hl
        obtain ⟨rfl, hl⟩ := hl
        obtain ⟨ih1, ih2⟩ := storeOnHeadB_of_threadLinB nArgs nInv hpos body (cd + 1) cd hl
          (by omega)
        have hcd' : nameAt nArgs cd = regName cd := by
          unfold nameAt; rw [if_neg (by omega)]
        rw [hcd'] at ih1
        rw [hargs]
        refine ⟨?_, ?_⟩
        · show storeOnHeadB ((.Lopn [.reg (regName cd)] "STOREIDX" [.arrIdx (nameAt nArgs a)
            (nameAt nArgs b) (w / 8), .reg (nameAt nArgs c)], .store w n) :: _) _ = true
          simp only [storeOnHeadB, storeHit?, arrUse?, JasminLsemMem.storeStruct?, if_true,
            Option.map_some, beq_self_eq_true, Bool.true_and]
          exact ih1
        · refine Or.inr ?_
          show _ ∈ storeSlots ((.Lopn [.reg (regName cd)] "STOREIDX" [.arrIdx (nameAt nArgs a)
            (nameAt nArgs b) (w / 8), .reg (nameAt nArgs c)], .store w n) :: _) cd
          simp only [storeSlots, storeHit?, JasminLsemMem.storeStruct?, if_true, Option.map_some,
            Option.isSome_some, List.singleton_append, List.mem_cons]
          exact ih2
      all_goals
        exact hreg hl (chainElem_reg (by simp_all [opMemB]) (by simp) (by simp) cd _).1

/-- The export's name of the returned slot is the returned name. -/
theorem comRetReg_eq_nameAt (nArgs : Nat) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) (cd : Nat),
      comRetReg nArgs argName c cd = nameAt nArgs (retSlot c cd)
  | _, _, .ret v, cd => by simp only [comRetReg, resolveVar_eq_nameAt]; rfl
  | _, _, .var _ body, cd => comRetReg_eq_nameAt nArgs body (cd + 1)

/-! ## 4. Names the export keeps apart -/

theorem argName_ne_loopIdx (j d : Nat) : argName j ≠ loopIdx d :=
  ne_of_head? _ _ 'a' 'L' (head?_argName j)
    (JasminLsemExportCanonLogic.head?_loopIdx (d := d)) (by decide)

theorem argName_ne_loopReg (j d k : Nat) : argName j ≠ loopReg d k :=
  ne_of_head? _ _ 'a' 'L' (head?_argName j) (head?_loopReg d k) (by decide)

theorem notLoopRegB_argName (j : Nat) : notLoopRegB (argName j) = true := by
  simp [notLoopRegB, head?_argName]

theorem notLoopRegB_regName (k : Nat) : notLoopRegB (regName k) = true := by
  simp [notLoopRegB, head?_regName]

theorem fixB_argName (d k : Nat) (Sl : List Nat) (j : Nat) :
    fixB d (regName k) Sl (argName j) = true := by
  simp only [fixB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨fun h => regName_ne_argName k j h.symm, fun i _ => argName_ne_loopReg j d i⟩

theorem fixB_loopIdx (d k : Nat) (Sl : List Nat) : fixB d (regName k) Sl (loopIdx d) = true := by
  simp only [fixB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨fun h => LoopNameDistinct.regName_ne_loopIdx k d h.symm,
    fun i _ => LoopNameDistinct.loopIdx_ne_loopReg d d i⟩

theorem fixB_loopCtr (d k : Nat) (Sl : List Nat) : fixB d (regName k) Sl (loopCtr d) = true := by
  simp only [fixB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨fun h => LoopNameDistinct.regName_ne_loopCtr k d h.symm,
    fun i _ => LoopNameDistinct.loopCtr_ne_loopReg d d i⟩

/-- No variable of a vector has the argument slot `s`. -/
def avoidB {Γ : Ctxt jasminDialect} (s : Nat) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → Bool
  | [], _ => true
  | _ :: _, .cons v rest => ExportCertEntry.argIdx v != s && avoidB s rest

/-- The invariant base registers of a vector that avoids slot `s` are argument names other
    than `argName s`. -/
theorem invRegsOf_avoid {Γ : Ctxt jasminDialect} (s : Nat) :
    ∀ {tys : List JasminTy} (invs : HVector (fun ty => Ctxt.Var Γ ty) tys),
      avoidB s invs = true → ∀ r ∈ JasminLsemExportLift.invRegsOf
        (ExportCertLoop.loopInvOps invs), (∃ j, r = argName j) ∧ r ≠ argName s
  | [], .nil, _, r, hr => by
      simp [ExportCertLoop.loopInvOps, exprArgsHV, JasminLsemExportLift.invRegsOf] at hr
  | _ :: _, .cons v rest, h, r, hr => by
      replace h : (ExportCertEntry.argIdx v != s && avoidB s rest) = true := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rw [ExportCertEntry.invRegsOf_cons, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨⟨_, rfl⟩, fun he => h.1 (argName_injective he)⟩
      · exact invRegsOf_avoid s rest h.2 r hr

/-- The first index of `range m` whose argument name is `argName j`, for `j < m`. -/
theorem find?_range_argName {m j : Nat} (hj : j < m) :
    (List.range m).find? (fun j' => argName j == argName j') = some j := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, j, by simpa using hj, by simp, fun i hi => ?_⟩
  simp only [List.getElem_range, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  intro he
  have := argName_injective he
  omega

/-- `sigmaC` on an invariant argument is its base register. -/
theorem sigmaC_inv {d nInv : Nat} {acc : String} {invRegs : List String} {bound j : Nat}
    (hj : j < nInv) :
    sigmaC d nInv acc invRegs bound (argName j)
      = some (invRegs.getD (nInv - 1 - j) ("Linv" ++ toString d ++ "_" ++ toString j)) := by
  unfold sigmaC
  rw [if_neg (by simpa using fun h => absurd (argName_injective h) (by omega)),
    if_neg (by simpa using fun h => absurd (argName_injective h) (by omega)),
    find?_range_argName hj]

/-! ## 5. Completeness of `comLCertNB` -/

/-- **The fragment of single-loop programs.** A program is one runtime-count loop over an
    array accumulator followed by the return of the loop's result; its update is on the linear
    store thread from the accumulator (`threadLinB`: ops in `opMemB`, loads from the
    accumulator thread or an invariant array, stores into the thread head, the head returned);
    and no invariant seed is the accumulator seed.

    Refused shapes: any other `ComL` program (a straight continuation after the loop, nested
    or sequenced loops, a scalar accumulator); an update op outside `opMemB` (`extCall`,
    `callN`, the vector ops, `rorImm`, `cmp`, `cmpImm`, a zero-width constant, a shift by
    `2 ^ w` or more); an array load from an earlier version of the accumulator thread; a
    store into an invariant array or into an earlier version of the thread; a return of an
    array other than the thread head; an invariant seed that is the accumulator seed. -/
def loopFragB : {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → Bool
  | _, _, @ComL.forLoopNRt _ (.stackArr _ _) _ invTys update _ init invs (.ret _) =>
      threadLinB invTys.length update (invTys.length + 2) (invTys.length + 1)
        && avoidB (ExportCertEntry.argIdx init) invs
  | _, _, _ => false

/-- **Completeness of `comLCertNB`.** Every program of the fragment `loopFragB` passes the
    export certificate check `comLCertNB`. -/
theorem comLCertNB_complete {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (h : loopFragB c = true) : ExportCertLoopBody.comLCertNB c = true := by
  unfold loopFragB at h
  split at h
  · next Γ' w n invTys update count init invs v =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨hlin, havoid⟩ := h
      show ExportCertLoopBody.loopCertNB update count init invs = true
      unfold ExportCertLoopBody.loopCertNB
      rw [ExportCertEntry.resolveVar_top, ExportCertEntry.resolveVar_top]
      simp only
      have hlen := ExportCertEntry.invRegsOf_length invs
      have hinvs := invRegsOf_avoid _ invs havoid
      have hpos : 0 < invTys.length + 2 := by omega
      obtain ⟨hsoh, hret⟩ := storeOnHeadB_of_threadLinB (invTys.length + 2) invTys.length hpos
        update _ _ hlin (Nat.le_refl _)
      have hacc : nameAt (invTys.length + 2) (invTys.length + 1)
          = JasminLsemMemSourceTieUncond.accRegMN invTys := by
        unfold nameAt; rw [if_pos (by omega)]; rfl
      rw [hacc] at hsoh
      have hfixInv : ∀ r ∈ JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs),
          certRho Γ.length (regName Γ.length) (argName (ExportCertEntry.argIdx init))
            (certSlots update) r = r := by
        intro r hr
        obtain ⟨⟨j, rfl⟩, _⟩ := hinvs r hr
        exact certRho_of_fixB (fixB_argName _ _ _ _)
      have htau : ∀ j, j < invTys.length → ∃ t,
          (sigmaC Γ.length invTys.length (regName Γ.length)
            (JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs))
            ((certChain update).length + invTys.length + 2) (argName j)).map
            (certRho Γ.length (regName Γ.length) (argName (ExportCertEntry.argIdx init))
              (certSlots update)) = some t ∧ t ≠ argName (ExportCertEntry.argIdx init) := by
        intro j hj
        rw [sigmaC_inv hj, Option.map_some]
        refine ⟨_, rfl, ?_⟩
        have hmem := List.getElem_mem (l := JasminLsemExportLift.invRegsOf
          (ExportCertLoop.loopInvOps invs)) (n := invTys.length - 1 - j) (by omega)
        rw [List.getD_eq_getElem _ _ (by omega), hfixInv _ hmem]
        exact (hinvs _ hmem).2
      have hthr := threadCertB_of_threadLinB (fun b => (sigmaC Γ.length invTys.length
          (regName Γ.length) (JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs))
          ((certChain update).length + invTys.length + 2) b).map
          (certRho Γ.length (regName Γ.length) (argName (ExportCertEntry.argIdx init))
            (certSlots update)))
        (invTys.length + 2) invTys.length _ hpos
        (by omega) htau update _ _ (certSlots update) hlin (Nat.le_refl _) (fun _ _ => Iff.rfl)
      rw [hacc] at hthr
      have hwalk : certRho Γ.length (regName Γ.length) (argName (ExportCertEntry.argIdx init))
          (certSlots update)
          (JasminLprogExport.loopBodyWalkN Γ.length (regName Γ.length) (loopIdx Γ.length)
            (JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs)) (fun _ => none)
            update (2 + invTys.length)).2 = argName (ExportCertEntry.argIdx init) := by
        rw [JasminLsemExportCanon.loopBodyWalkN_ret_eq_ren (certSigma_loopRen hlen),
          comRetReg_eq_nameAt, Nat.add_comm 2]
        rcases hret with h1 | h1
        · rw [h1, hacc]
          exact (congrArg _ certSigma_acc).trans (certRho_acc _ _ _ _)
        · have hk := le_of_mem_storeSlots h1
          have : nameAt (invTys.length + 2) (retSlot update (invTys.length + 2))
              = regName (retSlot update (invTys.length + 2)) := by
            unfold nameAt; rw [if_neg (by omega)]
          rw [this, certSigma_reg]
          exact certRho_slot h1
      simp only [exportCertB, hlen, beq_self_eq_true, Bool.true_and, notLoopRegB_regName,
        notLoopRegB_argName, fixB_loopIdx, fixB_loopCtr, fixB_argName, hwalk, hsoh,
        Bool.and_true]
      have hrne : regName Γ.length ≠ "" := fun h => by
        have := head?_regName Γ.length; rw [h] at this; cases this
      have hthr' : threadCertB _ _ _ _ (certChain update) _ _
          (JasminLsemMemSourceTieArrUncond.loopBodyRetArrMN update) = true := hthr
      simp only [hthr', Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
      refine ⟨⟨⟨⟨hrne, argName_ne_loopIdx _ _⟩, fun h => JasminLsemExportTransfer.loopCtr_ne_argName
        _ _ h.symm⟩, argName_ne_loopIdx _ _⟩, fun r hr => ?_⟩
      obtain ⟨⟨j, rfl⟩, hne⟩ := hinvs r hr
      exact ⟨⟨⟨⟨notLoopRegB_argName j, fixB_argName _ _ _ _⟩, hne⟩, argName_ne_loopIdx _ _⟩,
        fun h => JasminLsemExportTransfer.loopCtr_ne_argName _ _ h.symm⟩
  · cases h

/-! ## 6. Move lists indexed by positions -/

open ExportCertLoopJ (movPair? movPairs? movesOKB carOnlyB seedSrcB feedSrcB)

/-- A list is the `getD` image of the range of its length. -/
theorem range_map_getD {α : Type} (l : List α) (dflt : α) :
    (List.range l.length).map (fun j => l.getD j dflt) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- The parallel-assignment check of a move list indexed by distinct positions `I`: targets
    are injective on `I`, and a source equals a target only at the same position. -/
theorem movesOKB_of_index (I : List Nat) (U V : Nat → String) (hnd : I.Nodup)
    (hU : ∀ i ∈ I, ∀ j ∈ I, U i = U j → i = j)
    (hV : ∀ i ∈ I, ∀ j ∈ I, V i = U j → i = j) :
    movesOKB (I.map fun j => (U j, V j)) = true := by
  simp only [movesOKB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map,
    Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.map_map]
  refine ⟨?_, ?_⟩
  · exact List.Nodup.map_on (fun i hi j hj h => hU i hi j hj h) hnd
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    by_cases h : V i = U j
    · obtain rfl := hV i hi j hj h
      exact Or.inr rfl
    · exact Or.inl h

/-- The move pairs of a list of register moves, decoded position by position. -/
theorem movPairs?_map {α : Type} (L : List α) (F : α → LinstrRM) (g : α → String × String)
    (h : ∀ a ∈ L, movPair? (F a) = some (g a)) : movPairs? (L.map F) = some (L.map g) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [movPairs?, List.map_cons, List.mapM_cons] at ih ⊢
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]
      rfl

/-- A renamed register move decodes to its renamed target and source. -/
theorem movPair?_renRM (ρ : String → String) (t s : String) :
    movPair? (JasminLsemExportTransfer.renRM ρ
      (.Lopn [.reg t] (withWidthTag 64 "MOV") [.reg s], MemTag.reg none)) = some (ρ t, ρ s) := by
  simp [movPair?, JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR,
    JasminLsemExportTransfer.renOperand]

/-- The feedback staging copies nothing when every returned carried register is returned at
    its own position. -/
theorem feedbackStage_none (d tmp0 : Nat) (targets : List String) :
    ∀ (srcs : List LOperand) (i : Nat),
      (∀ j x, srcs[j]? = some (.reg x) → targets.contains x = true → targets[i + j]? = some x) →
      feedbackStage d tmp0 targets srcs i = ([], srcs)
  | [], _, _ => rfl
  | op :: ops, i, h => by
      have ih := feedbackStage_none d tmp0 targets ops (i + 1) (fun j x hj hc => by
        have := h (j + 1) x (by simpa using hj) hc
        rwa [show i + (j + 1) = i + 1 + j by omega] at this)
      simp only [feedbackStage, ih]
      cases op with
      | reg x =>
          have h0 := h 0 x rfl
          simp only [Nat.add_zero] at h0
          by_cases hc : targets.contains x = true
          · simp [h0 hc]
          · simp only [Bool.not_eq_true] at hc
            simp only [hc, Bool.false_and, Bool.false_eq_true, if_false]
      | _ => rfl

/-- The final feedback moves over register sources: one move per position whose source is
    not its target. -/
theorem feedbackMoves_regs : ∀ (ts xs : List String), ts.length = xs.length →
    feedbackMoves ts (xs.map LOperand.reg)
      = ((ts.zip xs).filter (fun p => !(p.2 == p.1))).map
          (fun p => (⟨0, .Lopn [.reg p.1] (withWidthTag 64 "MOV") [.reg p.2]⟩ : Linstr))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | t :: ts, x :: xs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.map_cons, feedbackMoves, List.zip_cons_cons, List.filter_cons,
        feedbackMoves_regs ts xs h]
      by_cases hx : (x == t) = true
      · simp [hx]
      · simp [hx]

/-! ## 7. Slot lists of a carried-register body -/

/-- The slots of the variables of a vector at depth `cd`. -/
def hvSlots {Γ : Ctxt jasminDialect} (cd : Nat) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → List Nat
  | [], _ => []
  | _ :: _, .cons v rest => slotOf cd v :: hvSlots cd rest

theorem exprArgsHV_eq_hvSlots (cd nArgs : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      exprArgsHV cd nArgs argName (fun _ => none) hv
        = (hvSlots cd hv).map (fun s => .reg (nameAt nArgs s))
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show resolveVar cd nArgs argName (fun _ => none) v
          :: exprArgsHV cd nArgs argName (fun _ => none) rest = _
      rw [resolveVar_eq_nameAt, exprArgsHV_eq_hvSlots cd nArgs rest]
      rfl

theorem hvSlots_length (cd : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      (hvSlots cd hv).length = tys.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => by
      show (hvSlots cd rest).length + 1 = _
      rw [hvSlots_length cd rest]; rfl

/-- The slots of the variables a multi-result body returns. -/
def retSlotsJ : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    MultiReturnCom jasminDialect Γ ts → Nat → List Nat
  | _, _, .ret vs, cd => hvSlots cd vs
  | _, _, .var _ body, cd => retSlotsJ body (cd + 1)

theorem canonRets_eq_retSlotsJ (nArgs : Nat) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat), JasminLsemMemSourceTieRegs.canonRets nArgs m cd
        = (retSlotsJ m cd).map (fun s => .reg (nameAt nArgs s))
  | _, _, .ret vs, cd => exprArgsHV_eq_hvSlots cd nArgs vs
  | _, _, .var _ body, cd => canonRets_eq_retSlotsJ nArgs body (cd + 1)

theorem retSlotsJ_length :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat), (retSlotsJ m cd).length = ts.length
  | _, _, .ret vs, cd => hvSlots_length cd vs
  | _, _, .var _ body, cd => retSlotsJ_length body (cd + 1)

theorem retSlotsJ_head :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
      (m : MultiReturnCom jasminDialect Γ (t :: ts)) (cd : Nat),
      (retSlotsJ m cd).getD 0 0 = retSlot m.toComHead cd
  | _, _, _, .ret (.cons v rest), cd => by
      rw [JasminLsemMemSourceTieRegs.toComHead_ret]; rfl
  | _, _, _, .var e body, cd => by
      rw [JasminLsemMemSourceTieRegs.toComHead_var]
      exact retSlotsJ_head body (cd + 1)

theorem hvSlots_lt (cd : Nat) (hpos : 0 < cd) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ s ∈ hvSlots cd hv, s < cd
  | [], .nil, s, hs => by cases hs
  | _ :: _, .cons v rest, s, hs => by
      rcases List.mem_cons.mp hs with rfl | hs
      · show cd - 1 - varIndex v < cd; omega
      · exact hvSlots_lt cd hpos rest s hs

/-- No slot of a vector that avoids slot `s` is `s`. -/
theorem avoidB_hvSlots {Γ : Ctxt jasminDialect} (s : Nat) :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      avoidB s hv = true → ∀ x ∈ hvSlots Γ.length hv, x ≠ s
  | [], .nil, _, x, hx => by cases hx
  | _ :: _, .cons v rest, h, x, hx => by
      replace h : (ExportCertEntry.argIdx v != s && avoidB s rest) = true := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact avoidB_hvSlots s rest h.2 x hx

theorem retSlotsJ_lt :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat), 0 < cd → ∀ s ∈ retSlotsJ m cd, s < cd + JasminLsemMemSourceTieRegs.mLen m
  | _, _, .ret vs, cd, hpos => by
      intro s hs
      have := hvSlots_lt cd hpos vs s hs
      show s < cd + 0
      omega
  | _, _, .var _ body, cd, _ => by
      intro s hs
      have := retSlotsJ_lt body (cd + 1) (by omega) s hs
      show s < cd + (JasminLsemMemSourceTieRegs.mLen body + 1)
      omega

/-- The slots of the array stores of a body from depth `cd`. -/
def storeSlotsSrc : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Nat →
    List Nat
  | _, _, .ret _, _ => []
  | _, _, .var e body, cd =>
      (match e.op with | .stackStore _ _ => [cd] | _ => []) ++ storeSlotsSrc body (cd + 1)

/-- The store slots of the model chain are the slots of the body's array stores. -/
theorem storeSlots_straightOpsMem (nArgs : Nat) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) (cd : Nat),
      storeSlots (straightOpsMem nArgs c cd) cd = storeSlotsSrc c cd
  | _, _, .ret _, _ => rfl
  | _, _, .var ⟨op, heq, args⟩ body, cd => by
      rw [ExportCertLoopBody.straightOpsMem_var]
      simp only [storeSlots, storeSlotsSrc]
      rw [storeSlots_straightOpsMem nArgs body (cd + 1)]
      congr 1
      cases op
      case stackStore w n =>
        obtain ⟨a, b, c, hargs, _⟩ := exprArgs_store cd nArgs heq args
        rw [hargs]; rfl
      all_goals rfl

/-! ## 8. The computed loop renaming of a carried-register node -/

/-- `sigmaCJ` is defined on every slot name below `bound` at the argument count
    `nInv + 1 + nCar`. -/
theorem sigmaCJ_isSome {d nInv nCar : Nat} {invRegs : List String} {bound s : Nat}
    (hs : s < nInv + 1 + nCar ∨ s < bound) :
    (ExportCertLoopJ.sigmaCJ d nInv nCar invRegs bound (nameAt (nInv + 1 + nCar) s)).isSome
      = true := by
  unfold ExportCertLoopJ.sigmaCJ
  split
  · rfl
  · next h1 =>
      split
      · rfl
      · next h2 =>
          split
          · rfl
          · next h3 =>
              split
              · rfl
              · next h4 =>
                  exfalso
                  rw [List.find?_eq_none] at h1 h3 h4
                  simp only [beq_iff_eq, List.mem_range] at h1 h2 h3 h4
                  unfold nameAt at h1 h2 h3 h4
                  split at h1
                  · next hlt =>
                      simp only [if_pos hlt] at h2 h3
                      by_cases hA : nInv + 1 ≤ s
                      · exact h1 (s - (nInv + 1)) (by omega) (by congr 1; omega)
                      by_cases hB : s = nInv
                      · exact h2 (by rw [hB])
                      · exact h3 s (by omega) rfl
                  · next hge =>
                      simp only [if_neg hge] at h4
                      exact h4 s (by omega) rfl

/-! ## 9. Completeness of `exportCertJB` -/

/-- **The returned positions of a carried-register body.** Each position `p ≥ 1` of the
    returned tuple (a carried register) returns an invariant or the index (slot at most
    `nInv`), its own carried binder (slot `nArgs - 1 - p`), or a body binding that is no array
    store. -/
def retOKB (nArgs nInv : Nat) (stores slots : List Nat) : Bool :=
  (List.range slots.length).all fun p => p == 0 || decide (slots.getD p 0 ≤ nInv)
    || slots.getD p 0 + 1 + p == nArgs
    || (decide (nArgs ≤ slots.getD p 0) && !stores.contains (slots.getD p 0))

open ExportCertFragment (arrMemNB comExpOKB)
open ExportCertLoopJ (noArrB singleLoopJB loopInitOpsJ exportCertJB certSigmaJ sigmaCJ
  tauCJ rhoJ certSlotsJ seedsJ feedJ srcsJ)
open JasminLsemMemSourceTieRegs (nArgsJ chainJ retsJ headJ)

/-- **The fragment of counted carried-register programs.** The loop carries an array and the
    registers `rs`; the body's ops lie in the fragment (`arrMemNB`, `comExpOKB`); the body is
    on the linear store thread from the carried array (`threadLinB`); no invariant seed and no
    carried register seed is the array seed; and each returned carried register is an
    invariant, the index, its own binder or a body binding (`retOKB`).

    Refused shapes: an array among the carried registers `rs`; a body op outside `opMemB`,
    `opPlainB` or `immShiftWireOKB`; an array load from an earlier version of the carried
    array; a store into an invariant array or an earlier version; a return of an array other
    than the thread head; an invariant seed that is the array seed; a carried register that
    returns another carried binder (a rotation such as `(a, b) ↦ (b, a + b)`, which the
    export stages through a body temporary). -/
def loopFragJB {Γ : Ctxt jasminDialect} {w n : Nat} {rs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) : Bool :=
  match inits with
  | .cons init rest =>
      noArrB rs && arrMemNB update.toComHead && comExpOKB update.toComHead
      && threadLinB invTys.length update.toComHead (nArgsJ rs invTys) (nArgsJ rs invTys - 1)
      && avoidB (ExportCertEntry.argIdx init) invs && avoidB (ExportCertEntry.argIdx init) rest
      && retOKB (nArgsJ rs invTys) invTys.length
          (storeSlotsSrc update.toComHead (nArgsJ rs invTys)) (retSlotsJ update (nArgsJ rs invTys))

/-- **Completeness of `exportCertJB`.** Every program of the fragment `loopFragJB` passes the
    export certificate of a counted carried-register node at the loop depth `Γ.length`, with
    the array seed's and the count's argument registers as output and count registers. -/
theorem exportCertJB_complete {Γ : Ctxt jasminDialect} {w n : Nat}
    {rs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (init : Ctxt.Var Γ (JasminTy.stackArr w n)) (rest : HVector (fun ty => Ctxt.Var Γ ty) rs)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (h : loopFragJB update (.cons init rest) invs = true) :
    exportCertJB Γ.length (argName (ExportCertEntry.argIdx init))
      (argName (ExportCertEntry.argIdx count)) update (loopInitOpsJ (.cons init rest))
      (ExportCertLoop.loopInvOps invs) = true := by
  have h' : (noArrB rs && arrMemNB update.toComHead && comExpOKB update.toComHead
      && threadLinB invTys.length update.toComHead (nArgsJ rs invTys) (nArgsJ rs invTys - 1)
      && avoidB (ExportCertEntry.argIdx init) invs && avoidB (ExportCertEntry.argIdx init) rest
      && retOKB (nArgsJ rs invTys) invTys.length
          (storeSlotsSrc update.toComHead (nArgsJ rs invTys))
          (retSlotsJ update (nArgsJ rs invTys))) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨hnoArr, hmem⟩, hexp⟩, hlin⟩, havoid⟩, havoidR⟩, hret⟩ := h'
  have hinvOps : ExportCertLoop.loopInvOps invs
      = (hvSlots Γ.length invs).map (fun s => .reg (nameAt Γ.length s)) :=
    exprArgsHV_eq_hvSlots _ _ invs
  have hlenInv : (ExportCertLoop.loopInvOps invs).length = invTys.length := by
    rw [hinvOps, List.length_map, hvSlots_length]
  have hallReg : ExportCertLoopJ.allRegB (ExportCertLoop.loopInvOps invs) = true := by
    rw [hinvOps]; simp [ExportCertLoopJ.allRegB]
  have hlenR := ExportCertEntry.invRegsOf_length invs
  have hinvs := invRegsOf_avoid _ invs havoid
  have hNA : nArgsJ rs invTys = invTys.length + 1 + (rs.length + 1) := by
    simp only [nArgsJ]; omega
  have hpos : 0 < nArgsJ rs invTys := by simp only [nArgsJ]; omega
  -- the invariant names are fixed by the node renaming and differ from `out`
  have hfixInv : ∀ r ∈ JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs),
      rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update r = r := by
    intro r hr
    obtain ⟨⟨j, rfl⟩, _⟩ := hinvs r hr
    exact certRho_of_fixB (fixB_argName _ _ _ _)
  -- the computed renaming on invariant arguments
  have htau : ∀ j, j < invTys.length → ∃ t,
      tauCJ Γ.length (argName (ExportCertEntry.argIdx init)) (ExportCertLoop.loopInvOps invs)
        update (argName j) = some t ∧ t ≠ argName (ExportCertEntry.argIdx init) := by
    intro j hj
    have hs := sigmaCJ_isSome (d := Γ.length) (nInv := invTys.length) (nCar := rs.length + 1)
      (invRegs := JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs))
      (bound := (chainJ update).length + nArgsJ rs invTys) (s := j) (Or.inl (by omega))
    have hj' : nameAt (invTys.length + 1 + (rs.length + 1)) j = argName j := by
      unfold nameAt; rw [if_pos (by omega)]
    rw [hj'] at hs
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
    have hsound := ExportCertLoopJ.sigmaCJ_sound ht
    rw [ExportCertLoopJ.certSigmaJ_inv hj] at hsound
    have hmem := List.getElem_mem (l := JasminLsemExportLift.invRegsOf
      (ExportCertLoop.loopInvOps invs)) (n := invTys.length - 1 - j) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at hsound
    refine ⟨t, ?_, ?_⟩
    · unfold tauCJ
      rw [ht, Option.map_some, ← hsound, hfixInv _ hmem]
    · rw [← hsound]; exact (hinvs _ hmem).2
  -- the thread certificate
  have hthr := threadCertB_of_threadLinB (tauCJ Γ.length (argName (ExportCertEntry.argIdx init))
      (ExportCertLoop.loopInvOps invs) update) (nArgsJ rs invTys) invTys.length _ hpos
    (by simp only [nArgsJ]; omega) htau update.toComHead _ _ (certSlotsJ update) hlin
    (Nat.le_refl _) (fun _ _ => Iff.rfl)
  have hhead : nameAt (nArgsJ rs invTys) (nArgsJ rs invTys - 1)
      = argName (invTys.length + rs.length + 1) := by
    unfold nameAt; rw [if_pos (by omega)]; congr 1; simp only [nArgsJ]; omega
  have hlenRets : (retSlotsJ update (nArgsJ rs invTys)).length = rs.length + 1 := by
    rw [retSlotsJ_length]; rfl
  have hE : comRetReg (nArgsJ rs invTys) argName update.toComHead (nArgsJ rs invTys)
      = headJ update := by
    simp only [headJ, retsJ]
    rw [canonRets_eq_retSlotsJ, comRetReg_eq_nameAt, ← retSlotsJ_head,
      List.getD_eq_getElem _ _ (by simp [hlenRets]),
      List.getD_eq_getElem _ _ (by simp [hlenRets])]
    simp [JasminLsemWidthN.operandName]
  rw [hhead, hE] at hthr
  -- the carried tuple, position by position
  have hσ := ExportCertLoopJ.certSigmaJ_loopRenJ (d := Γ.length) (nCar := rs.length + 1)
    hallReg
  have hrets := JasminLsemMemSourceTieRegs.loopBodyWalkR_rets hσ update
    (invTys.length + 1 + (rs.length + 1))
  rw [hlenInv, show invTys.length + 1 + (rs.length + 1) = nArgsJ rs invTys from hNA.symm,
    canonRets_eq_retSlotsJ, List.map_map] at hrets
  obtain ⟨X, hX⟩ : ∃ X : Nat → String, X = fun j => certSigmaJ Γ.length invTys.length
      (rs.length + 1) (JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs))
      (nameAt (nArgsJ rs invTys) ((retSlotsJ update (nArgsJ rs invTys)).getD j 0)) :=
    ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Nat → Nat, A = fun j => (hvSlots Γ.length (.cons init rest)).getD j 0 :=
    ⟨_, rfl⟩
  have hwalk : (JasminLprogExport.loopBodyWalkR Γ.length Γ.length (rs.length + 1)
      (some (loopIdx Γ.length)) (ExportCertLoop.loopInvOps invs) update
      (invTys.length + 1 + (rs.length + 1))).2.1
      = (List.range (rs.length + 1)).map (fun j => LOperand.reg (X j)) := by
    rw [show invTys.length + 1 + (rs.length + 1) = nArgsJ rs invTys from hNA.symm]
    rw [hrets]
    conv_lhs => rw [← range_map_getD (retSlotsJ update (nArgsJ rs invTys)) 0]
    rw [List.map_map, hlenRets]
    subst hX
    rfl
  have hslotsI : ∀ s ∈ hvSlots Γ.length (.cons init rest), s < Γ.length :=
    hvSlots_lt Γ.length (by have := JasminLsemSimulation.varIndex_lt init; omega) _
  have hlenI : (hvSlots Γ.length (.cons init rest)).length = rs.length + 1 := by
    rw [hvSlots_length]; rfl
  have hinit : loopInitOpsJ (.cons init rest)
      = (List.range (rs.length + 1)).map (fun j => LOperand.reg (argName (A j))) := by
    unfold loopInitOpsJ
    rw [exprArgsHV_eq_hvSlots, ← hlenI,
      ← range_map_getD (hvSlots Γ.length (.cons init rest)) 0, List.map_map, List.length_map,
      List.length_range]
    apply List.map_congr_left
    intro j hj
    subst hA
    simp only [Function.comp_apply, LOperand.reg.injEq]
    have hj' : j < (hvSlots Γ.length (.cons init rest)).length := List.mem_range.mp hj
    unfold nameAt
    rw [if_pos]
    rw [List.getD_eq_getElem _ _ hj']
    exact hslotsI _ (List.getElem_mem hj')
  have haccs : JasminLsemExportLiftJ.forAccs Γ.length (loopInitOpsJ (.cons init rest)) update
      (ExportCertLoop.loopInvOps invs)
      = (List.range (rs.length + 1)).map (fun j => (regName (Γ.length + (rs.length + 1 - 1 - j)),
          LOperand.reg (argName (A j)), LOperand.reg (X j))) := by
    unfold JasminLsemExportLiftJ.forAccs
    simp only [List.length_cons]
    rw [hwalk, hinit]
    unfold JasminLprogExport.carriedRegs
    rw [List.zip_map', List.zip_map']
  -- the node renaming on the carried registers and the argument names
  have hρ0 : rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
      (regName (Γ.length + (rs.length + 1 - 1 - 0))) = argName (ExportCertEntry.argIdx init) := by
    simp only [Nat.sub_zero, Nat.add_sub_cancel]
    exact certRho_acc _ _ _ _
  have hρj : ∀ j, 1 ≤ j → j ≤ rs.length →
      rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - j)))
        = regName (Γ.length + (rs.length + 1 - 1 - j)) := by
    intro j h1 h2
    refine certRho_fix (fun he => ?_) (fun k _ => LoopNameDistinct.regName_ne_loopReg _ _ _)
    have := regName_injective he
    omega
  have hρarg : ∀ k, rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (argName k)
      = argName k := fun k => certRho_of_fixB (fixB_argName _ _ _ _)
  have hSl : certSlotsJ update = storeSlotsSrc update.toComHead (nArgsJ rs invTys) :=
    storeSlots_straightOpsMem _ _ _
  -- the returned operands, classified
  have hXc : ∀ j, j < rs.length + 1 →
      X j = regName (Γ.length + (rs.length + 1 - 1 - j))
      ∨ (j = 0 ∧ rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (X j)
          = argName (ExportCertEntry.argIdx init) ∧ ∀ k, X j ≠ regName k)
      ∨ (1 ≤ j ∧ rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (X j) = X j
          ∧ X j ≠ argName (ExportCertEntry.argIdx init) ∧ ∀ k, X j ≠ regName k) := by
    intro j hj
    subst hX
    simp only
    by_cases hj0 : j = 0
    · subst hj0
      rw [retSlotsJ_head]
      obtain ⟨_, hr⟩ := storeOnHeadB_of_threadLinB (nArgsJ rs invTys) invTys.length hpos
        update.toComHead _ _ hlin (Nat.le_refl _)
      rcases hr with hr | hr
      · left
        rw [hr]
        have : nameAt (nArgsJ rs invTys) (nArgsJ rs invTys - 1)
            = argName (invTys.length + 1 + rs.length) := by
          unfold nameAt; rw [if_pos (by omega)]; congr 1; omega
        rw [this, ExportCertLoopJ.certSigmaJ_car (by omega)]
        congr 2
      · right; left
        have hk := le_of_mem_storeSlots hr
        have : nameAt (nArgsJ rs invTys) (retSlot update.toComHead (nArgsJ rs invTys))
            = regName (retSlot update.toComHead (nArgsJ rs invTys)) := by
          unfold nameAt; rw [if_neg (by omega)]
        rw [this, ExportCertLoopJ.certSigmaJ_reg]
        exact ⟨rfl, certRho_slot hr, fun k => (LoopNameDistinct.regName_ne_loopReg _ _ _).symm⟩
    · have hr := List.all_eq_true.mp hret j (List.mem_range.mpr (by rw [hlenRets]; exact hj))
      simp only [Bool.or_eq_true, beq_iff_eq, hj0, false_or, decide_eq_true_eq,
        Bool.and_eq_true, Bool.not_eq_true'] at hr
      generalize (retSlotsJ update (nArgsJ rs invTys)).getD j 0 = s at hr ⊢
      rcases hr with (hr | hr) | ⟨hr1, hr2⟩
      · have hn : nameAt (nArgsJ rs invTys) s = argName s := by
          unfold nameAt; rw [if_pos (by omega)]
        rw [hn]
        right; right
        rcases Nat.lt_or_eq_of_le hr with hlt | heq
        · rw [ExportCertLoopJ.certSigmaJ_inv hlt]
          have hmem := List.getElem_mem (l := JasminLsemExportLift.invRegsOf
            (ExportCertLoop.loopInvOps invs)) (n := invTys.length - 1 - s) (by omega)
          rw [List.getD_eq_getElem _ _ (by omega)]
          obtain ⟨⟨k, hk⟩, hne⟩ := hinvs _ hmem
          refine ⟨by omega, hfixInv _ hmem, hne, fun k' => ?_⟩
          rw [hk]; exact fun h => regName_ne_argName _ _ h.symm
        · rw [heq, ExportCertLoopJ.certSigmaJ_idx]
          exact ⟨by omega, certRho_of_fixB (fixB_loopIdx _ _ _),
            fun h => argName_ne_loopIdx _ _ h.symm,
            fun k h => LoopNameDistinct.regName_ne_loopIdx k _ h.symm⟩
      · left
        have hn : nameAt (nArgsJ rs invTys) s = argName (invTys.length + 1 + (rs.length - j)) := by
          unfold nameAt; rw [if_pos (by omega)]; congr 1; simp only [nArgsJ] at hr; omega
        rw [hn, ExportCertLoopJ.certSigmaJ_car (by omega)]
        congr 2
      · right; right
        have hn : nameAt (nArgsJ rs invTys) s = regName s := by
          unfold nameAt; rw [if_neg (by omega)]
        rw [hn, ExportCertLoopJ.certSigmaJ_reg]
        refine ⟨by omega, certRho_fix (fun h => LoopNameDistinct.regName_ne_loopReg _ _ _ h.symm)
          (fun k hk he => ?_), fun h => argName_ne_loopReg _ _ _ h.symm,
          fun k h => LoopNameDistinct.regName_ne_loopReg _ _ _ h.symm⟩
        have := JasminLsemExportCanon.loopReg_injective _ he
        subst this
        rw [hSl] at hk
        simp [hk] at hr2
  -- the seed moves
  have hseeds : movPairs? (seedsJ Γ.length (argName (ExportCertEntry.argIdx init))
      (loopInitOpsJ (.cons init rest)) (ExportCertLoop.loopInvOps invs) update)
      = some ((List.range (rs.length + 1)).map fun j =>
          (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
            (regName (Γ.length + (rs.length + 1 - 1 - j))),
           rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (argName (A j)))) := by
    simp only [seedsJ, haccs, JasminLsemExportLiftJ.regsSeedsRM, List.map_map]
    exact movPairs?_map _ _ _ (fun j _ => movPair?_renRM _ _ _)
  -- the feedback moves
  have hstage := feedbackStage_none Γ.length (JasminLsemExportLiftJ.forTmp0 Γ.length update
      (ExportCertLoop.loopInvOps invs))
    ((List.range (rs.length + 1)).map fun j => regName (Γ.length + (rs.length + 1 - 1 - j)))
    ((List.range (rs.length + 1)).map fun j => LOperand.reg (X j)) 0 (by
      intro j x hj hc
      by_cases hlt : j < rs.length + 1
      · simp only [List.getElem?_map, hlt, List.getElem?_range, Option.map_some,
          Option.some.injEq, LOperand.reg.injEq] at hj
        subst hj
        simp only [List.contains_iff_mem, List.mem_map, List.mem_range] at hc
        obtain ⟨i, _, hi⟩ := hc
        rcases hXc j hlt with h1 | ⟨_, _, h3⟩ | ⟨_, _, _, h3⟩
        · simp [hlt, h1]
        · exact absurd hi.symm (h3 _)
        · exact absurd hi.symm (h3 _)
      · simp [hlt] at hj)
  have hfeed : movPairs? (feedJ Γ.length (argName (ExportCertEntry.argIdx init))
      (loopInitOpsJ (.cons init rest)) (ExportCertLoop.loopInvOps invs) update)
      = some ((((List.range (rs.length + 1)).filter fun j =>
            !(X j == regName (Γ.length + (rs.length + 1 - 1 - j)))).map fun j =>
          (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
            (regName (Γ.length + (rs.length + 1 - 1 - j))),
           rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (X j)))) := by
    have hsrcs : (List.range (rs.length + 1)).map (fun j => LOperand.reg (X j))
        = ((List.range (rs.length + 1)).map X).map LOperand.reg := by
      rw [List.map_map]; rfl
    simp only [feedJ, haccs, List.map_map, JasminLsemExportLiftJ.regsFeedbackRM,
      Function.comp_def]
    rw [hstage, List.nil_append, hsrcs, feedbackMoves_regs _ _ (by simp), List.zip_map',
      List.filter_map]
    simp only [JasminLsemExportLift.liftLcmdRM, List.map_map, Function.comp_def]
    exact movPairs?_map _ _ _ (fun j _ => movPair?_renRM _ _ _)
  -- the targets
  have hU : ∀ i, i < rs.length + 1 → ∀ j, j < rs.length + 1 →
      rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - i)))
      = rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - j))) → i = j := by
    intro i hi j hj he
    rcases Nat.eq_zero_or_pos i with rfl | hi0 <;> rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · rw [hρ0, hρj j hj0 (by omega)] at he
      exact absurd he.symm (regName_ne_argName _ _)
    · rw [hρ0, hρj i hi0 (by omega)] at he
      exact absurd he (regName_ne_argName _ _)
    · rw [hρj i hi0 (by omega), hρj j hj0 (by omega)] at he
      have := regName_injective he
      omega
  have hUout : ∀ j, j < rs.length + 1 →
      rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - j))) = argName (ExportCertEntry.argIdx init)
      → j = 0 := by
    intro j hj he
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · rw [hρj j hj0 (by omega)] at he
      exact absurd he (regName_ne_argName _ _)
  have hUreg : ∀ j, 1 ≤ j → j < rs.length + 1 →
      rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - j)))
      = regName (Γ.length + (rs.length - j)) := by
    intro j h1 h2
    rw [hρj j h1 (by omega)]
    congr 2
  -- the seed sources
  have hA0 : A 0 = ExportCertEntry.argIdx init := by subst hA; rfl
  have hAj : ∀ j, 1 ≤ j → j < rs.length + 1 → A j ≠ ExportCertEntry.argIdx init := by
    intro j h1 h2
    subst hA
    have hlt : j - 1 < (hvSlots Γ.length rest).length := by rw [hvSlots_length]; omega
    have hmem := List.getElem_mem hlt
    have hav := avoidB_hvSlots _ rest havoidR _ hmem
    show (hvSlots Γ.length (.cons init rest)).getD j 0 ≠ _
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    show (hvSlots Γ.length rest).getD j' 0 ≠ _
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    simpa using hav
  -- the seed checks
  have hsOK : movesOKB ((List.range (rs.length + 1)).map fun j =>
      (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - j))),
       rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (argName (A j)))) = true := by
    refine movesOKB_of_index _ _ _ List.nodup_range
      (fun i hi j hj he => hU i (List.mem_range.mp hi) j (List.mem_range.mp hj) he)
      (fun i hi j hj he => ?_)
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    rw [hρarg] at he
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hρ0] at he
      have := argName_injective he
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rfl
      · exact absurd this (hAj i hi0 hi')
    · rw [hρj j hj0 (by omega)] at he
      exact absurd he.symm (regName_ne_argName _ _)
  have hsCar : carOnlyB Γ.length rs.length ((List.range (rs.length + 1)).map fun j =>
      (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - j))),
       rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (argName (A j)))) = true := by
    simp only [carOnlyB, List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply,
      Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · right; rw [hρ0, hρarg, hA0]
    · left; exact ⟨rs.length - j, by omega, hUreg j hj0 hj⟩
  have hsSrc : seedSrcB Γ.length rs.length ((List.range (rs.length + 1)).map fun j =>
      (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - j))),
       rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (argName (A j))))
      (srcsJ (loopInitOpsJ (.cons init rest)) rs.length) = true := by
    simp only [seedSrcB, List.all_eq_true, List.mem_range, List.any_map, List.any_eq_true,
      Function.comp_apply, Bool.and_eq_true, beq_iff_eq]
    intro k hk
    refine ⟨rs.length - k, by omega, ?_, ?_⟩
    · rw [hUreg _ (by omega) (by omega)]; congr 2; omega
    · rw [hρarg, srcsJ, hinit, List.getD_eq_getElem _ _ (by simp)]
      simp [JasminLsemWidthN.operandName]
  -- the feedback checks
  have hmemI : ∀ j, j ∈ (List.range (rs.length + 1)).filter (fun j =>
        !(X j == regName (Γ.length + (rs.length + 1 - 1 - j))))
      ↔ j < rs.length + 1 ∧ X j ≠ regName (Γ.length + (rs.length + 1 - 1 - j)) := by
    intro j
    simp [List.mem_filter]
  have hfOK : movesOKB ((((List.range (rs.length + 1)).filter fun j =>
            !(X j == regName (Γ.length + (rs.length + 1 - 1 - j)))).map fun j =>
          (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
            (regName (Γ.length + (rs.length + 1 - 1 - j))),
           rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (X j)))) = true := by
    refine movesOKB_of_index _ _ _ (List.nodup_range.filter _)
      (fun i hi j hj he => hU i ((hmemI i).mp hi).1 j ((hmemI j).mp hj).1 he)
      (fun i hi j hj he => ?_)
    obtain ⟨hi1, hi2⟩ := (hmemI i).mp hi
    have hj1 := ((hmemI j).mp hj).1
    rcases hXc i hi1 with h1 | ⟨rfl, h2, _⟩ | ⟨_, h2, h3, h4⟩
    · exact absurd h1 hi2
    · rw [h2] at he
      exact (hUout j hj1 he.symm).symm
    · rw [h2] at he
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [hρ0] at he; exact absurd he h3
      · rw [hρj j hj0 (by omega)] at he; exact absurd he (h4 _)
  have hfCar : carOnlyB Γ.length rs.length ((((List.range (rs.length + 1)).filter fun j =>
            !(X j == regName (Γ.length + (rs.length + 1 - 1 - j)))).map fun j =>
          (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
            (regName (Γ.length + (rs.length + 1 - 1 - j))),
           rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (X j)))) = true := by
    simp only [carOnlyB, List.all_map, List.all_eq_true, Function.comp_apply,
      Bool.or_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq]
    intro j hj
    obtain ⟨hj1, hj2⟩ := (hmemI j).mp hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · right
      rcases hXc 0 hj1 with h1 | ⟨_, h2, _⟩ | ⟨h1, _⟩
      · exact absurd h1 hj2
      · rw [hρ0, h2]
      · omega
    · left; exact ⟨rs.length - j, by omega, hUreg j hj0 hj1⟩
  have htauX : ∀ j, j < rs.length + 1 →
      tauCJ Γ.length (argName (ExportCertEntry.argIdx init)) (ExportCertLoop.loopInvOps invs)
        update (JasminLsemWidthN.operandName ((retsJ update).getD j (.imm 0)))
      = some (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (X j)) := by
    intro j hj
    have hjl : j < (retSlotsJ update (nArgsJ rs invTys)).length := by rw [hlenRets]; exact hj
    have hlt := retSlotsJ_lt update (nArgsJ rs invTys) hpos _ (List.getElem_mem hjl)
    have hclen := JasminLsemMemSourceTieRegs.straightOpsMem_toComHead_length
      (nArgsJ rs invTys) update (nArgsJ rs invTys)
    simp only [retsJ]
    rw [canonRets_eq_retSlotsJ, List.getD_eq_getElem _ _ (by simpa using hjl),
      List.getElem_map]
    simp only [JasminLsemWidthN.operandName]
    have hs : (sigmaCJ Γ.length invTys.length (rs.length + 1)
        (JasminLsemExportLift.invRegsOf (ExportCertLoop.loopInvOps invs))
        ((chainJ update).length + nArgsJ rs invTys)
        (nameAt (nArgsJ rs invTys) (retSlotsJ update (nArgsJ rs invTys))[j])).isSome = true := by
      generalize (retSlotsJ update (nArgsJ rs invTys))[j] = s at hlt ⊢
      rw [show nameAt (nArgsJ rs invTys) s = nameAt (invTys.length + 1 + (rs.length + 1)) s by
        rw [hNA]]
      exact sigmaCJ_isSome (Or.inr (by simp only [chainJ] at hclen ⊢; omega))
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
    have hsound := ExportCertLoopJ.sigmaCJ_sound ht
    unfold tauCJ
    rw [ht, Option.map_some, ← hsound, hX]
    simp only [List.getD_eq_getElem _ _ hjl]
  have hfSrc : feedSrcB Γ.length rs.length ((((List.range (rs.length + 1)).filter fun j =>
            !(X j == regName (Γ.length + (rs.length + 1 - 1 - j)))).map fun j =>
          (rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
            (regName (Γ.length + (rs.length + 1 - 1 - j))),
           rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update (X j))))
      (tauCJ Γ.length (argName (ExportCertEntry.argIdx init)) (ExportCertLoop.loopInvOps invs)
        update) (retsJ update) = true := by
    simp only [feedSrcB, List.all_eq_true, List.mem_range]
    intro k hk
    rw [htauX (rs.length - k) (by omega)]
    simp only [Bool.or_eq_true, List.any_map, List.any_eq_true, Function.comp_apply,
      Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_false]
    have hUk : rhoJ Γ.length (argName (ExportCertEntry.argIdx init)) update
        (regName (Γ.length + (rs.length + 1 - 1 - (rs.length - k)))) = regName (Γ.length + k) := by
      rw [hUreg _ (by omega) (by omega)]; congr 2; omega
    by_cases hin : X (rs.length - k) = regName (Γ.length + (rs.length + 1 - 1 - (rs.length - k)))
    · right
      refine ⟨by rw [hin, hUk], fun i hi he => ?_⟩
      obtain ⟨hi1, hi2⟩ := (hmemI i).mp hi
      rw [← hUk] at he
      have := hU i hi1 _ (by omega) he
      subst this
      exact hi2 hin
    · left
      exact ⟨rs.length - k, (hmemI _).mpr ⟨by omega, hin⟩, hUk, rfl⟩
  -- the certificate
  have hthr' : threadCertB (tauCJ Γ.length (argName (ExportCertEntry.argIdx init))
      (ExportCertLoop.loopInvOps invs) update) (nArgsJ rs invTys) (certSlotsJ update)
      (argName (ExportCertEntry.argIdx init)) (chainJ update) (nArgsJ rs invTys)
      (argName (invTys.length + rs.length + 1)) (headJ update) = true := hthr
  simp only [exportCertJB, hseeds, hfeed, hlenInv, beq_self_eq_true, hallReg, hnoArr, hmem,
    hexp, notLoopRegB_argName, fixB_loopIdx, fixB_loopCtr, fixB_argName, hthr', hsOK, hsCar,
    hsSrc, hfOK, hfCar, hfSrc, Bool.true_and, Bool.and_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨argName_ne_loopIdx _ _, fun h => JasminLsemExportTransfer.loopCtr_ne_argName
    _ _ h.symm⟩, argName_ne_loopIdx _ _⟩, fun k _ => ⟨fun h => regName_ne_argName _ _ h.symm,
    regName_ne_argName _ _⟩⟩, fun r hr => ?_⟩
  obtain ⟨⟨j, rfl⟩, hne⟩ := hinvs r hr
  exact ⟨⟨⟨⟨⟨notLoopRegB_argName j, fixB_argName _ _ _ _⟩, hne⟩, argName_ne_loopIdx _ _⟩,
    fun h => JasminLsemExportTransfer.loopCtr_ne_argName _ _ h.symm⟩,
    fun k _ h => regName_ne_argName _ _ h.symm⟩

/-- **Completeness of the counted carried-register gate.** Every program of the fragment
    `loopFragJB` passes `singleLoopJB`, the gate of `exportCertJB` at the export's seed and
    count registers. -/
theorem singleLoopJB_complete {Γ : Ctxt jasminDialect} {w n : Nat}
    {rs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (h : loopFragJB update inits invs = true) :
    singleLoopJB update count inits invs = true := by
  match inits, h with
  | .cons init rest, h =>
      unfold singleLoopJB
      have h0 : (loopInitOpsJ (.cons init rest)).getD 0 (.imm 0)
          = .reg (argName (ExportCertEntry.argIdx init)) :=
        ExportCertEntry.resolveVar_top init
      rw [h0, ExportCertEntry.resolveVar_top]
      exact exportCertJB_complete update init rest count invs h

/-! ## 10. A shipped program in both fragments -/

open MpnLogicalFrontEmit (logicCount logicInit logicInvs)
open MpnLogicalFrontDenote (andUpdate)

/-- The front-generated `mpn_and_n` loop (output array threaded through the stores, the two
    source arrays as invariants) lies in the single-loop fragment. -/
theorem loopFragB_mpn_and_n :
    loopFragB (ComL.forLoopNRt (andUpdate ()) logicCount logicInit logicInvs (.ret .here))
      = true := by
  native_decide

/-- The same loop as a counted carried-register node lies in the carried-register
    fragment. -/
theorem loopFragJB_mpn_and_n :
    loopFragJB (w := 64) (n := MpnLogicalFrontEmit.NL) (rs := [])
      (invTys := [MpnLogicalFrontEmit.AL, MpnLogicalFrontEmit.AL])
      (andUpdate ()).toMulti (.cons logicInit .nil) logicInvs = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertComplete
