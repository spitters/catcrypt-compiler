/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference

/-!
# de-Bruijn depth and trace position

The emitter names a `Com` binding's destination register by its de-Bruijn depth
(`regName curDepth`, `comToBody`/`bindingHeads`), while the register allocator
indexes bindings by their position in `bodyTrace`, which keeps one `PhysEvent`
per `Lopn` and drops every other instruction. This module relates the two
indices on the `UniformRegArith` binop fragment: for the head list
`bindingHeads nArgs argName (fun _ => none) com d0`, the binding at depth `d`
is the `Lopn` at trace position `d - d0`.

## Contents

* `bodyOpNames_dsts_eq_range`: the destination column of `bodyOpNames` of a
  `UniformRegArith` head list is `fun k => some (regName (d0 + k))` over the
  positions — every head is an `Lopn`, so `bodyOpNames` loses no position, and
  the depth increments once per position.
* `bodyOpNames_comToBody` / `bodyNames_comToBody` / `bodyTrace_comToBody`: the
  terminal `Lret` contributes no operand names, so the emitter output
  `comToBody … com d0` and its binop prefix share `bodyOpNames`, `bodyNames` and
  `bodyTrace`.
* `bodyTrace_wr_eq_depth`: the `PhysEvent` at trace position `k` writes the slot
  of `regName (d0 + k)`. The exporter starts the emission at `curDepth = nArgs`
  (`comToLprog`), so the binding at depth `d` sits at position `d - nArgs`.
* `regName_mem_bodyNames`: a head's destination name is in `bodyNames`.
* `liveAt_of_touched` / `liveAt_wr`: a slot an event touches is live at that
  event's position, in the `LiveAt` sense of `ToLprogFaithfulRAInterference`
  (`physFirstTouch ≤ pos ≤ physLastTouch`).
* `hinj_liveOutNames_at_depth`: the live-out interference condition
  `physRename_hinj_liveOutNames` at the destination `regName d` and the trace
  position `d - d0`, with `hnDst` and `hdLive` discharged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulDepthTrace

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference

/-! ## 1. `bodyOpNames` of a binding-head list -/

/-- The `bodyOpNames` of the head list of a `regArith` binding: the head
    contributes its destination `regName d` and its two resolved source names,
    and the tail is the head list of the body at depth `d + 1`. -/
theorem bodyOpNames_bindingHeads_var {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs : Nat) (bop : JasminBinOp) (w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (a0 a1 : Ctxt.Var Γ (JasminTy.reg w))
    (bdy : Com jasminDialect (JasminTy.reg w :: Γ) s) (d : Nat) :
    bodyOpNames (bindingHeads nArgs argName (fun _ => none)
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d)
      = (some (regName d), [resolveVarName d nArgs a0, resolveVarName d nArgs a1])
          :: bodyOpNames (bindingHeads nArgs argName (fun _ => none) bdy (d + 1)) := by
  rw [bindingHeads_var_eq]
  simp [bodyOpNames, regArithHead, linstrRegNames, LOperand.regName?,
    LOperand.srcRegNames]

/-- **Depth is position.** On a `UniformRegArith` `Com`, the destination column
    of `bodyOpNames (bindingHeads … com d0)` is `some (regName (d0 + k))` at
    position `k`. -/
theorem bodyOpNames_dsts_eq_range {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hu : UniformRegArith com) (nArgs : Nat) :
    ∀ d0 : Nat,
      (bodyOpNames (bindingHeads nArgs argName (fun _ => none) com d0)).map Prod.fst
        = (List.range
            (bodyOpNames (bindingHeads nArgs argName (fun _ => none) com d0)).length).map
            (fun k => some (regName (d0 + k))) := by
  induction hu with
  | ret v => intro d0; rfl
  | var bop heq a0 a1 bdy hw hns hbody ih =>
      intro d0
      rw [bodyOpNames_bindingHeads_var]
      rw [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map, ih (d0 + 1)]
      refine congrArg (List.cons _) ?_
      simp only [Function.comp_def]
      refine List.map_congr_left ?_
      intro k _
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

/-- The destination name of the `Lopn` at position `k` of a `UniformRegArith`
    head list is `regName (d0 + k)`. -/
theorem bodyOpNames_dst_getElem {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hu : UniformRegArith com) (nArgs d0 k : Nat)
    (hk : k < (bodyOpNames (bindingHeads nArgs argName (fun _ => none) com d0)).length) :
    (bodyOpNames (bindingHeads nArgs argName (fun _ => none) com d0))[k].1
      = some (regName (d0 + k)) := by
  have h := congrArg (fun l => l[k]?) (bodyOpNames_dsts_eq_range hu nArgs d0)
  simpa [List.getElem?_map, List.getElem?_range, hk, List.getElem?_eq_getElem hk] using h

/-! ## 2. The terminal `Lret` carries no trace position -/

/-- The terminal `Lret` of `comToBody` contributes no `bodyOpNames` entry, so
    the emitter output and its binop prefix have the same operand-name list. -/
theorem bodyOpNames_comToBody (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (d : Nat) :
    bodyOpNames (comToBody nArgs argName (fun _ => none) com d)
      = bodyOpNames (bindingHeads nArgs argName (fun _ => none) com d) := by
  induction com generalizing d with
  | ret v => simp [comToBody, bindingHeads, bodyOpNames, linstrRegNames]
  | var e bdy ih =>
      have h := ih (d + 1)
      simp only [comToBody, bindingHeads, bodyOpNames, List.filterMap_cons] at h ⊢
      rw [h]

/-- `bodyNames` of the emitter output is `bodyNames` of its binop prefix. -/
theorem bodyNames_comToBody (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (d : Nat) :
    bodyNames (comToBody nArgs argName (fun _ => none) com d)
      = bodyNames (bindingHeads nArgs argName (fun _ => none) com d) := by
  simp only [bodyNames, bodyOpNames_comToBody]

/-- `bodyTrace` of the emitter output is `bodyTrace` of its binop prefix. -/
theorem bodyTrace_comToBody (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (d : Nat) :
    bodyTrace (comToBody nArgs argName (fun _ => none) com d)
      = bodyTrace (bindingHeads nArgs argName (fun _ => none) com d) := by
  have hns : nameSlot (comToBody nArgs argName (fun _ => none) com d)
      = nameSlot (bindingHeads nArgs argName (fun _ => none) com d) := by
    funext n
    simp only [nameSlot, bodyNames_comToBody]
  simp only [bodyTrace, bodyOpNames_comToBody, hns]

/-! ## 3. The trace position of a binding -/

/-- `bodyTrace` keeps one event per `Lopn`, so it has the length of
    `bodyOpNames`. -/
theorem bodyTrace_length (body : Lcmd) :
    (bodyTrace body).length = (bodyOpNames body).length := by
  simp [bodyTrace]

/-- The event at trace position `k` writes the slot of the `k`-th `Lopn`'s
    destination name. -/
theorem bodyTrace_wr (body : Lcmd) (k : Nat) (hk : k < (bodyTrace body).length) :
    (bodyTrace body)[k].wr
      = (((bodyOpNames body)[k]'(by rw [bodyTrace_length] at hk; exact hk)).1.map
          (nameSlot body)).getD 0 := by
  simp only [bodyTrace, List.getElem_map]

/-- **The correspondence.** On a `UniformRegArith` `Com` the event at trace
    position `k` of `bindingHeads … com d0` writes the slot of
    `regName (d0 + k)`: the binding at de-Bruijn depth `d` occupies trace
    position `d - d0`. -/
theorem bodyTrace_wr_eq_depth {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hu : UniformRegArith com) (nArgs d0 k : Nat)
    (hk : k < (bodyTrace (bindingHeads nArgs argName (fun _ => none) com d0)).length) :
    (bodyTrace (bindingHeads nArgs argName (fun _ => none) com d0))[k].wr
      = nameSlot (bindingHeads nArgs argName (fun _ => none) com d0)
          (regName (d0 + k)) := by
  have hk' : k < (bodyOpNames (bindingHeads nArgs argName (fun _ => none) com d0)).length := by
    rw [bodyTrace_length] at hk; exact hk
  rw [bodyTrace_wr _ k hk, bodyOpNames_dst_getElem hu nArgs d0 k hk']
  rfl

/-! ## 4. The destination is in the name universe -/

/-- A head's destination name is one of the body's names: `bodyNames` collects
    every `Lopn`'s destination and sources. -/
theorem regName_mem_bodyNames {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hu : UniformRegArith com) (nArgs d0 k : Nat)
    (hk : k < (bodyOpNames (bindingHeads nArgs argName (fun _ => none) com d0)).length) :
    regName (d0 + k) ∈ bodyNames (bindingHeads nArgs argName (fun _ => none) com d0) := by
  set body := bindingHeads nArgs argName (fun _ => none) com d0 with hbody
  have hmem : (bodyOpNames body)[k] ∈ bodyOpNames body := List.getElem_mem hk
  have hdst : ((bodyOpNames body)[k]).1 = some (regName (d0 + k)) :=
    bodyOpNames_dst_getElem hu nArgs d0 k hk
  have hflat : regName (d0 + k) ∈
      (bodyOpNames body).flatMap (fun p => p.1.toList ++ p.2) := by
    refine List.mem_flatMap.mpr ⟨(bodyOpNames body)[k], hmem, ?_⟩
    rw [hdst]
    simp
  simpa [bodyNames] using List.mem_eraseDups.mpr hflat

/-! ## 5. A touched slot is live at its own position -/

/-- The index `find?` returns on a `zipIdx` list is no larger than the index of
    any element satisfying the predicate. -/
theorem find?_zipIdx_snd_le {α : Type} (p : α → Bool) :
    ∀ (l : List α) (n pos : Nat) (h : pos < l.length), p l[pos] = true →
      ∀ q, (l.zipIdx n).find? (fun r => p r.1) = some q → q.2 ≤ n + pos := by
  intro l
  induction l with
  | nil => intro n pos h; exact absurd h (by simp)
  | cons a rest ih =>
      intro n pos h hp q hq
      rw [List.zipIdx_cons, List.find?_cons] at hq
      by_cases hpa : p a
      · simp only [hpa] at hq
        have hq' : q = (a, n) := by injection hq with hq'; exact hq'.symm
        rw [hq']
        exact Nat.le_add_right n pos
      · simp only [hpa] at hq
        cases pos with
        | zero => exact absurd (by simpa using hp) hpa
        | succ pos' =>
            have := ih (n + 1) pos' (by simpa using h) (by simpa using hp) q hq
            omega

/-- A slot touched by the event at position `pos` is first touched no later than
    `pos`. -/
theorem physFirstTouch_le_of_touched {tr : List PhysEvent} {pos s : Nat}
    (h : pos < tr.length) (hs : s ∈ tr[pos].touched) :
    physFirstTouch tr s ≤ pos := by
  have hmem : (tr[pos], pos) ∈ tr.zipIdx := by
    have : tr.zipIdx[pos]'(by simpa using h) = (tr[pos], pos) := by simp
    exact this ▸ List.getElem_mem (by simpa using h)
  unfold physFirstTouch
  cases hf : tr.zipIdx.find? (fun p => p.1.touched.contains s) with
  | none =>
      have := List.find?_eq_none.mp hf _ hmem
      exact absurd (List.elem_eq_true_of_mem hs) (by simpa using this)
  | some q =>
      obtain ⟨ev, i⟩ := q
      have := find?_zipIdx_snd_le (fun e : PhysEvent => e.touched.contains s) tr 0 pos h
        (by simpa using List.elem_eq_true_of_mem hs) (ev, i) hf
      simpa using this

/-- A slot touched by the event at position `pos` is last touched no earlier
    than `pos`. -/
theorem le_physLastTouch_of_touched {tr : List PhysEvent} {pos s : Nat}
    (h : pos < tr.length) (hs : s ∈ tr[pos].touched) :
    pos ≤ physLastTouch tr s := by
  have hmem : (tr[pos], pos) ∈ tr.zipIdx := by
    have : tr.zipIdx[pos]'(by simpa using h) = (tr[pos], pos) := by simp
    exact this ▸ List.getElem_mem (by simpa using h)
  refine mem_le_foldl_max _ 0 pos ?_
  rw [List.mem_filterMap]
  refine ⟨(tr[pos], pos), hmem, ?_⟩
  simp only [List.elem_eq_true_of_mem hs, if_pos]

/-- A slot an event touches is live at that event's position. -/
theorem liveAt_of_touched {tr : List PhysEvent} {pos s : Nat}
    (h : pos < tr.length) (hs : s ∈ tr[pos].touched) : LiveAt tr pos s :=
  ⟨physFirstTouch_le_of_touched h hs, le_physLastTouch_of_touched h hs⟩

/-- The slot an event writes is live at that event's position. -/
theorem liveAt_wr {tr : List PhysEvent} {pos : Nat} (h : pos < tr.length) :
    LiveAt tr pos tr[pos].wr :=
  liveAt_of_touched h (by simp [PhysEvent.touched])

/-! ## 6. The live-out interference condition at a de-Bruijn depth -/

/-- **`hinj` at the binding of depth `d`.** On a `UniformRegArith` `Com` the
    binding at depth `d` occupies trace position `d - d0`, and at that position
    the live-out interference condition of `physRename_hinj_liveOutNames` holds
    for its destination `regName d`: both the name-universe membership `hnDst`
    and the destination liveness `hdLive` are discharged from the
    depth-position correspondence. -/
theorem hinj_liveOutNames_at_depth {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hu : UniformRegArith com) (nArgs d0 d : Nat)
    (hfit : numGPRegs
      + (physLiveItems (bodyTrace (bindingHeads nArgs argName (fun _ => none) com d0))).length
        ≤ vectorBase)
    (hd : d0 ≤ d)
    (hlt : d - d0 <
      (bodyTrace (bindingHeads nArgs argName (fun _ => none) com d0)).length) :
    ∀ m ∈ liveOutNames (bindingHeads nArgs argName (fun _ => none) com d0) (d - d0),
      physRename (bindingHeads nArgs argName (fun _ => none) com d0)
          (bodyPhysTable (bindingHeads nArgs argName (fun _ => none) com d0)) m
        = physRename (bindingHeads nArgs argName (fun _ => none) com d0)
          (bodyPhysTable (bindingHeads nArgs argName (fun _ => none) com d0))
          (regName d) →
      m = regName d := by
  set body := bindingHeads nArgs argName (fun _ => none) com d0 with hbody
  have hdepth : d0 + (d - d0) = d := by omega
  have hk' : d - d0 < (bodyOpNames body).length := by
    rw [bodyTrace_length] at hlt; exact hlt
  have hnDst : regName d ∈ bodyNames body := by
    have := regName_mem_bodyNames hu nArgs d0 (d - d0) hk'
    rwa [hdepth] at this
  have hwr : (bodyTrace body)[d - d0].wr = nameSlot body (regName d) := by
    have := bodyTrace_wr_eq_depth hu nArgs d0 (d - d0) hlt
    rwa [hdepth] at this
  have hdLive : LiveAt (bodyTrace body) (d - d0) (nameSlot body (regName d)) :=
    hwr ▸ liveAt_wr hlt
  exact physRename_hinj_liveOutNames hfit hlt hnDst hdLive

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulDepthTrace
