/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the export certificate check

The export step of the back half accepts a program with a single runtime-count loop over an
array accumulator only when its certificate check `ExportCertLoopBody.comLCertNB` returns
`true`. This module states a decidable fragment of source programs and proves that the check
accepts every program of the fragment.

The fragment rests on the linear store thread `threadLinB`: every array load reads the
current version of the carried array or an invariant array, every array store writes into the
current version and its result becomes the current version, and the body returns the current
version. On such a body the model chain `straightOpsMem` passes `threadCertB` and
`storeOnHeadB` (`threadCertB_of_threadLinB`, `storeOnHeadB_of_threadLinB`).

## Main definitions

* `threadLinB` — the linear store thread of a body.
* `loopFragB` — the single-loop fragment.

## Main results

* `threadCertB_of_threadLinB` — the thread certificate of a linear body.
* `comLCertNB_complete` — `comLCertNB` accepts every program of `loopFragB`.
* `loopFragB_mpn_and_n` — the front-generated `mpn_and_n` loop lies in the fragment.
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

/-! ## 6. A shipped program in the fragment -/

open MpnLogicalFrontEmit (logicCount logicInit logicInvs)
open MpnLogicalFrontDenote (andUpdate)

/-- The front-generated `mpn_and_n` loop (output array threaded through the stores, the two
    source arrays as invariants) lies in the single-loop fragment. -/
theorem loopFragB_mpn_and_n :
    loopFragB (ComL.forLoopNRt (andUpdate ()) logicCount logicInit logicInvs (.ret .here))
      = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertComplete
