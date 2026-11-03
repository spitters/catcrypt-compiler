/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheckComplete
import all Init.Data.Queue

@[expose] public section

set_option autoImplicit false

/-!
# The annotation of the bounds-invariant gate is a fixed point

The gate of the region backend reads `idxInvCheckB entry (idxAnnot entry B) B`. The annotation
`idxAnnot` starts from the candidate facts and restricts them along the edges of the body by the
worklist `annWork`. `IdxInvCheckComplete.idxAnnot_contains` is the lower half of the
greatest-fixed-point argument: every annotation of candidates closed along the edges is
contained in `idxAnnot`. This module proves the upper half and the consequences for the gate.

## The argument

The worklist keeps three invariants (`WInv`): the pending flags and the facts have the same
size; a block that is not pending has the facts of each successor entailed along its edges
(`PostAt`); a pending block is in the queue (`qList`). A visit of block `k` clears its flag and
filters the facts of its successors; a successor whose facts shrank is flagged and queued
unless it is flagged already, so a block whose facts changed is pending again
(`annVisit_rel`). The potential `factCount a + (qList q).length` falls by one at each visit,
and it starts below the fuel `nb * (|cs| + 1) + 1` of `idxAnnot`; so the queue is empty when
the fuel runs out, every block is settled, and the annotation is closed along every edge
(`idxAnnot_post`).

## Main results

* `idxAnnot_post`: the facts of each successor in `idxAnnot` are entailed along each edge.
* `idxInvCheckB_idxAnnot`: when the check accepts some annotation of candidate facts, it
  accepts `idxAnnot`.
* `idxInvCheckB_idxAnnot_of_G`: the gate as a set does not shrink: every entry and body the
  gate of compiler commit 4bd6693e accepted (the check `idxInvCheckBG` with the greedy readers
  at the annotation `idxAnnotG` computed with them) the gate accepts.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-! ## 1. Queues and arrays -/

/-- The elements of a queue in the order in which `dequeue?` yields them. -/
def qList (q : Std.Queue Nat) : List Nat := q.dList ++ q.eList.reverse

theorem qList_enqueue (v : Nat) (q : Std.Queue Nat) : qList (q.enqueue v) = qList q ++ [v] := by
  simp [qList, Std.Queue.enqueue]

theorem qList_foldl_enqueue :
    ∀ (l : List Nat) (q : Std.Queue Nat),
      qList (l.foldl (fun q k => q.enqueue k) q) = qList q ++ l
  | [], q => by simp
  | k :: l, q => by
      rw [List.foldl_cons, qList_foldl_enqueue l, qList_enqueue]
      simp

theorem qList_empty : qList Std.Queue.empty = [] := by simp [qList, Std.Queue.empty]

theorem qList_of_dequeue?_none {q : Std.Queue Nat} (h : q.dequeue? = none) : qList q = [] := by
  unfold Std.Queue.dequeue? at h
  unfold qList
  split at h
  · cases h
  · rename_i hd
    split at h
    · rename_i he
      simp_all
    · cases h

theorem qList_of_dequeue?_some {q q' : Std.Queue Nat} {k : Nat}
    (h : q.dequeue? = some (k, q')) : qList q = k :: qList q' := by
  unfold Std.Queue.dequeue? at h
  unfold qList
  split at h
  · rename_i d ds hd
    cases h
    simp [hd]
  · rename_i hd
    split at h
    · cases h
    · rename_i d ds he
      cases h
      simp [hd, he]

theorem getD_set!_self {α : Type} {a : Array α} {k : Nat} {v d : α} (hk : k < a.size) :
    (a.set! k v).getD k d = v := by
  simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hk]

theorem getD_set!_ne {α : Type} {a : Array α} {k j : Nat} {v d : α} (hj : j ≠ k) :
    (a.set! k v).getD j d = a.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Ne.symm hj]

theorem getD_eq_default {α : Type} {a : Array α} {j : Nat} {d : α} (hj : a.size ≤ j) :
    a.getD j d = d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj]

/-- The number of facts of an annotation array. -/
def factCount (a : Array (List IdxFact)) : Nat := (a.toList.map List.length).sum

theorem sum_length_set : ∀ (l : List (List IdxFact)) (j : Nat) (v : List IdxFact),
    j < l.length → ((l.set j v).map List.length).sum + (l.getD j []).length =
      (l.map List.length).sum + v.length
  | [], _, _, h => by simp at h
  | x :: l, 0, v, _ => by simp; omega
  | x :: l, j + 1, v, h => by
      have := sum_length_set l j v (by simpa using h)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getD_cons_succ]
      omega

theorem factCount_set! {a : Array (List IdxFact)} {j : Nat} {v : List IdxFact}
    (hj : j < a.size) : factCount (a.set! j v) + (a.getD j []).length = factCount a + v.length := by
  unfold factCount
  have h := sum_length_set a.toList j v (by simpa using hj)
  simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  simpa [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD] using h

/-! ## 2. One visit -/

/-- The worklist state. -/
abbrev WSt := Array (List IdxFact) × Array Bool × Std.Queue Nat

/-- **The relation of a worklist state to a later one within a visit**: the sizes are kept,
    facts are only removed, a block whose flag is clear was clear before with its facts
    unchanged, a flagged block was flagged before or is in the queue, the queue only grows at
    its end, and the potential does not grow. -/
def VisitRel (st st' : WSt) : Prop :=
  st'.1.size = st.1.size ∧ st'.2.1.size = st.2.1.size ∧
  (∀ j, ∀ f ∈ st'.1.getD j [], f ∈ st.1.getD j []) ∧
  (∀ j, st'.2.1.getD j false = false →
    st.2.1.getD j false = false ∧ st'.1.getD j [] = st.1.getD j []) ∧
  (∀ j, st'.2.1.getD j false = true → st.2.1.getD j false = true ∨ j ∈ qList st'.2.2) ∧
  (∀ x ∈ qList st.2.2, x ∈ qList st'.2.2) ∧
  factCount st'.1 + (qList st'.2.2).length ≤ factCount st.1 + (qList st.2.2).length

theorem VisitRel.refl (st : WSt) : VisitRel st st :=
  ⟨rfl, rfl, fun _ _ h => h, fun _ h => ⟨h, rfl⟩, fun _ h => Or.inl h, fun _ h => h, le_rfl⟩

theorem VisitRel.trans {st st' st'' : WSt} (h1 : VisitRel st st') (h2 : VisitRel st' st'') :
    VisitRel st st'' := by
  obtain ⟨a1, p1, s1, c1, f1, q1, m1⟩ := h1
  obtain ⟨a2, p2, s2, c2, f2, q2, m2⟩ := h2
  refine ⟨a2.trans a1, p2.trans p1, fun j f hf => s1 j f (s2 j f hf), fun j hj => ?_,
    fun j hj => ?_, fun x hx => q2 x (q1 x hx), m2.trans m1⟩
  · obtain ⟨h1, e1⟩ := c2 j hj
    obtain ⟨h0, e0⟩ := c1 j h1
    exact ⟨h0, e1.trans e0⟩
  · rcases f2 j hj with h | h
    · rcases f1 j h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (q2 _ h')
    · exact Or.inr h

/-- **A visit keeps the relation, and each successor it filters has its facts entailed along
    the edge** at the facts `F` of the visited block. -/
theorem annVisit_rel (F : List SFact) :
    ∀ (es : List (Nat × List SFact × SSt)) (st : WSt), st.2.1.size = st.1.size →
      VisitRel st (annVisit F es st) ∧
        ∀ e ∈ es, ∀ f ∈ (annVisit F es st).1.getD e.1 [],
          entails (F ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true
  | [], st, _ => ⟨VisitRel.refl st, by simp⟩
  | (j, ex, ss) :: es, (a, pend, q), hsz => by
      -- the state after the first edge
      let old := a.getD j []
      let new := old.filter fun f => entails (F ++ ex) (f.toS ss.regs ss.arrs)
      let st1 : WSt :=
        if new.length < old.length then
          if pend.getD j false then (a.set! j new, pend, q)
          else (a.set! j new, pend.set! j true, q.enqueue j)
        else (a, pend, q)
      have hst : annVisit F ((j, ex, ss) :: es) (a, pend, q) = annVisit F es st1 := by
        unfold annVisit
        rw [List.foldl_cons]
      have hnew : ∀ f ∈ new, entails (F ++ ex) (f.toS ss.regs ss.arrs) = true :=
        fun f hf => (List.mem_filter.mp hf).2
      have hsub : ∀ f ∈ new, f ∈ old := fun f hf => (List.mem_filter.mp hf).1
      -- the first edge
      have h1 : VisitRel (a, pend, q) st1 ∧ st1.2.1.size = st1.1.size ∧
          ∀ f ∈ st1.1.getD j [], entails (F ++ ex) (f.toS ss.regs ss.arrs) = true := by
        by_cases hlt : new.length < old.length
        · have hj : j < a.size := by
            by_contra hj
            have : old = [] := getD_eq_default (by omega)
            simp [this] at hlt
          have hfc := factCount_set! (v := new) hj
          have hlt' : new.length < (a.getD j []).length := hlt
          have hsz' : j < pend.size := hsz ▸ hj
          by_cases hp : pend.getD j false = true
          · simp only [st1, hlt, ↓reduceIte, hp]
            refine ⟨⟨by simp, rfl, fun j' f hf => ?_, fun j' hj' => ?_, fun j' hj' => Or.inl hj',
              fun x hx => hx, by dsimp only; omega⟩, by simpa using hsz, ?_⟩
            · by_cases hjj : j' = j
              · subst hjj
                rw [getD_set!_self hj] at hf
                exact hsub f hf
              · rwa [getD_set!_ne hjj] at hf
            · refine ⟨hj', ?_⟩
              have hjj : j' ≠ j := by
                rintro rfl
                simp [hp] at hj'
              exact getD_set!_ne hjj
            · rw [getD_set!_self hj]
              exact hnew
          · simp only [Bool.not_eq_true] at hp
            simp only [st1, hlt, ↓reduceIte, hp, Bool.false_eq_true]
            refine ⟨⟨by simp, by simp, fun j' f hf => ?_, fun j' hj' => ?_, fun j' hj' => ?_,
              fun x hx => ?_, ?_⟩, by simpa using hsz, ?_⟩
            · by_cases hjj : j' = j
              · subst hjj
                rw [getD_set!_self hj] at hf
                exact hsub f hf
              · rwa [getD_set!_ne hjj] at hf
            · have hjj : j' ≠ j := by
                rintro rfl
                simp at hj'
                omega
              rw [getD_set!_ne hjj] at hj'
              exact ⟨hj', getD_set!_ne hjj⟩
            · by_cases hjj : j' = j
              · subst hjj
                exact Or.inr (by simp [qList_enqueue])
              · rw [getD_set!_ne hjj] at hj'
                exact Or.inl hj'
            · simp [qList_enqueue, hx]
            · dsimp only
              rw [qList_enqueue, List.length_append]
              simp only [List.length_singleton]
              omega
            · rw [getD_set!_self hj]
              exact hnew
        · simp only [st1, hlt, ↓reduceIte]
          refine ⟨VisitRel.refl _, hsz, ?_⟩
          have hall : new.length = old.length := by
            have : new.length ≤ old.length := List.length_filter_le _ _
            omega
          exact fun f hf => by
            simpa using (List.length_filter_eq_length_iff.mp hall) f hf
      obtain ⟨hr1, hsz1, he1⟩ := h1
      obtain ⟨hr, hes⟩ := annVisit_rel F es st1 hsz1
      rw [hst]
      refine ⟨hr1.trans hr, ?_⟩
      intro e he f hf
      rcases List.mem_cons.mp he with rfl | he
      · exact he1 f (hr.2.2.1 _ f hf)
      · exact hes e he f hf

/-! ## 3. The worklist -/

/-- The facts of each successor of block `k` are entailed along each edge `E k` from the facts
    of `k`. -/
def PostAt (E : Array (List (Nat × List SFact × SSt))) (a : Array (List IdxFact)) (k : Nat) :
    Prop :=
  ∀ e ∈ E.getD k [], ∀ f ∈ a.getD e.1 [],
    entails (startF (a.getD k []) ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true

/-- **The invariant of the worklist**: flags and facts have one size, a block in range that is
    not flagged is settled (`PostAt`), and a flagged block is in the queue. -/
def WInv (E : Array (List (Nat × List SFact × SSt))) (st : WSt) : Prop :=
  st.2.1.size = st.1.size ∧
  (∀ k < st.1.size, st.2.1.getD k false = false → PostAt E st.1 k) ∧
  (∀ k, st.2.1.getD k false = true → k ∈ qList st.2.2)

/-- The worklist only removes facts. -/
theorem annWork_sub (E : Array (List (Nat × List SFact × SSt))) :
    ∀ (fuel : Nat) (st : WSt), st.2.1.size = st.1.size →
      (annWork E fuel st).size = st.1.size ∧
        ∀ j, ∀ f ∈ (annWork E fuel st).getD j [], f ∈ st.1.getD j []
  | 0, (_, _, _), _ => ⟨rfl, fun _ _ h => h⟩
  | fuel + 1, (a, pend, q), hsz => by
      unfold annWork
      split
      · exact ⟨rfl, fun _ _ h => h⟩
      · rename_i k q' _
        have hsz' : (pend.set! k false).size = a.size := by simpa using hsz
        obtain ⟨hr, -⟩ := annVisit_rel (startF (a.getD k [])) (E.getD k [])
          (a, pend.set! k false, q') hsz'
        have hsz1 : (annVisit (startF (a.getD k [])) (E.getD k [])
            (a, pend.set! k false, q')).2.1.size =
            (annVisit (startF (a.getD k [])) (E.getD k [])
              (a, pend.set! k false, q')).1.size := by
          rw [hr.1, hr.2.1]
          exact hsz'
        obtain ⟨hs, hm⟩ := annWork_sub E fuel _ hsz1
        exact ⟨hs.trans hr.1, fun j f hf => hr.2.2.1 j f (hm j f hf)⟩

/-- **The worklist settles every block when its fuel exceeds the potential.** -/
theorem annWork_post (E : Array (List (Nat × List SFact × SSt))) :
    ∀ (fuel : Nat) (st : WSt), WInv E st →
      factCount st.1 + (qList st.2.2).length < fuel →
      ∀ k < st.1.size, PostAt E (annWork E fuel st) k
  | 0, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, (a, pend, q), ⟨hsz, hpost, hq⟩, hfuel => by
      unfold annWork
      split
      · rename_i hd
        have hq0 := qList_of_dequeue?_none hd
        intro k hk
        refine hpost k hk ?_
        cases hp : pend.getD k false
        · rfl
        · have := hq k hp
          simp [hq0] at this
      · rename_i k q' hd
        have hqq := qList_of_dequeue?_some hd
        have hsz' : (pend.set! k false).size = a.size := by simpa using hsz
        obtain ⟨hr, hes⟩ := annVisit_rel (startF (a.getD k [])) (E.getD k [])
          (a, pend.set! k false, q') hsz'
        obtain ⟨ha1, hp1, hs1, hc1, hf1, hq1, hm1⟩ := hr
        intro j hj
        refine annWork_post E fuel _ ⟨by rw [ha1, hp1]; exact hsz', ?_, ?_⟩ ?_ j
          (by rw [ha1]; exact hj)
        · intro j' hj' hpj'
          obtain ⟨hpj, hej⟩ := hc1 j' hpj'
          dsimp only at hpj hej
          by_cases hjk : j' = k
          · subst hjk
            intro e he f hf
            rw [hej]
            exact hes e he f hf
          · rw [getD_set!_ne hjk] at hpj
            intro e he f hf
            rw [hej]
            exact hpost j' (by rw [ha1] at hj'; exact hj') hpj e he f (hs1 _ f hf)
        · intro j' hpj'
          rcases hf1 j' hpj' with h | h
          · dsimp only at h
            by_cases hjk : j' = k
            · subst hjk
              simp at h
            · rw [getD_set!_ne hjk] at h
              have := hq j' h
              rw [hqq] at this
              rcases List.mem_cons.mp this with h' | h'
              · exact absurd h' hjk
              · exact hq1 _ h'
          · exact h
        · rw [hqq, List.length_cons] at hfuel
          dsimp only at hm1 hfuel
          omega

/-! ## 4. The annotation -/

/-- **The annotation is closed along every edge**: the facts that `idxAnnot` gives each
    successor of each block are entailed by the facts it gives the block and the condition of
    the edge. -/
theorem idxAnnot_post {entry : List IdxFact} {B : List LinstrRM} {G : CFG}
    (hG : cfgOf (B.map Prod.fst) = some G) :
    ∀ k < G.blocks.size, ∀ e ∈ annEdges B G k, ∀ f ∈ annAt (idxAnnot entry B) e.1,
      entails (startF (annAt (idxAnnot entry B) k) ++ e.2.1)
        (f.toS e.2.2.regs e.2.2.arrs) = true := by
  intro k hk e he f hf
  let nb := G.blocks.size
  let cs := idxCands entry B G
  let a0 : Array (List IdxFact) := (Array.range nb).map fun k =>
    if k = 0 then cs.filter fun f => entails (startF entry) (f.toS STerm.reg SArr.cell)
    else cs
  let E := (Array.range nb).map (annEdges B G)
  let q0 := (List.range nb).foldl (fun q k => q.enqueue k) Std.Queue.empty
  have hann : idxAnnot entry B =
      (annWork E (nb * (cs.length + 1) + 1) (a0, Array.replicate nb true, q0)).toList := by
    simp only [idxAnnot, hG]
    rfl
  have hinv : WInv E (a0, Array.replicate nb true, q0) := by
    refine ⟨by simp [a0], fun k hk hp => ?_, fun k hp => ?_⟩
    · simp only [a0, Array.size_map, Array.size_range] at hk
      simp [Array.getD_eq_getD_getElem?, hk] at hp
    · have hk : k < nb := by
        by_contra hk
        have hs : (Array.replicate nb true).size ≤ k := by simpa using hk
        rw [getD_eq_default hs] at hp
        cases hp
      simp [q0, qList_foldl_enqueue, qList_empty, hk]
  have hcount : factCount a0 ≤ nb * cs.length := by
    unfold factCount
    have : ∀ x ∈ a0.toList.map List.length, x ≤ cs.length := by
      intro x hx
      simp only [a0, Array.toList_map, Array.toList_range, List.map_map, List.mem_map,
        List.mem_range, Function.comp_apply] at hx
      obtain ⟨i, -, rfl⟩ := hx
      split
      · exact List.length_filter_le _ _
      · exact le_rfl
    have h := List.sum_le_length_nsmul _ _ this
    simpa [a0] using h
  have hpost := annWork_post E (nb * (cs.length + 1) + 1) _ hinv (by
    simp only [q0, qList_foldl_enqueue, qList_empty, List.nil_append, List.length_range]
    have : nb * (cs.length + 1) = nb * cs.length + nb := Nat.mul_succ nb cs.length
    omega) k (by simpa [a0] using hk)
  have hE : E.getD k [] = annEdges B G k := by
    simp [E, nb, Array.getD_eq_getD_getElem?, hk]
  rw [← hE] at he
  simp only [annAt, hann, List.getD_eq_getElem?_getD, Array.getElem?_toList] at hf ⊢
  simpa [Array.getD_eq_getD_getElem?] using
    hpost e he f (by simpa [Array.getD_eq_getD_getElem?] using hf)

/-- The facts of block `0` of the annotation are entailed by the entry facts. -/
theorem idxAnnot_entry {entry : List IdxFact} {B : List LinstrRM} :
    ∀ f ∈ annAt (idxAnnot entry B) 0,
      entails (startF entry) (f.toS STerm.reg SArr.cell) = true := by
  intro f hf
  unfold idxAnnot at hf
  split at hf
  · rename_i G hG
    have hsub := (annWork_sub ((Array.range G.blocks.size).map (annEdges B G))
      (G.blocks.size * ((idxCands entry B G).length + 1) + 1)
      ((Array.range G.blocks.size).map fun k =>
          if k = 0 then (idxCands entry B G).filter fun f =>
            entails (startF entry) (f.toS STerm.reg SArr.cell)
          else idxCands entry B G,
        Array.replicate G.blocks.size true,
        (List.range G.blocks.size).foldl (fun q k => q.enqueue k) Std.Queue.empty)
      (by simp)).2 0 f (by
        simpa [annAt, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD] using hf)
    by_cases h0 : 0 < G.blocks.size
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, h0,
        ↓reduceIte, Option.map_some, Option.getD_some] at hsub
      exact (List.mem_filter.mp hsub).2
    · simp [Array.getD_eq_getD_getElem?, h0] at hsub
  · simp [annAt] at hf

/-! ## 5. The check at the annotation -/

/-- Unfolding lemma of `annEdges`. -/
theorem annEdges_eq {B : List LinstrRM} {G : CFG} {k : Nat} :
    annEdges B G k =
      match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
      | .ok ss _ =>
          match (G.blk k).term with
          | .fall (some j) => [(j, [], ss)]
          | .goto tg => [(tg, [], ss)]
          | .cond tg nx =>
              match B[(G.blk k).stop - 1]? with
              | some (.Lcond c _, _) =>
                  (tg, edgeFacts (symDec ss c) true, ss) ::
                    match nx with
                    | some j => [(j, edgeFacts (symDec ss c) false, ss)]
                    | none => []
              | _ => []
          | _ => []
      | _ => [] := by
  unfold annEdges
  rfl

/-- **The successor check gives the edges**: when `termInvOk` accepts the facts `F` at the
    terminator `T`, the last instruction `z` and the final symbolic state `ss`, each successor
    fact is entailed along each edge of `T`, the edges `annEdges` reads. -/
theorem termInvOk_edges {ann : List (List IdxFact)} {F : List SFact} {ss : SSt} {T : Term}
    {z : Option LinstrRM} (h : termInvOk ann F ss T z = true) :
    ∀ e ∈ (match T with
          | .fall (some j) => [(j, ([] : List SFact), ss)]
          | .goto tg => [(tg, [], ss)]
          | .cond tg nx =>
              match z with
              | some (.Lcond c _, _) =>
                  (tg, edgeFacts (symDec ss c) true, ss) ::
                    match nx with
                    | some j => [(j, edgeFacts (symDec ss c) false, ss)]
                    | none => []
              | _ => []
          | _ => []),
      ∀ f ∈ annAt ann e.1, entails (F ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true := by
  intro e he f hf
  unfold termInvOk at h
  rcases T with (_ | j) | tg | ⟨tg, nx⟩ | _
  · simp at he
  · simp only [List.mem_singleton] at he
    subst he
    simp only [succOk, List.all_eq_true] at h
    simpa using h f hf
  · simp only [List.mem_singleton] at he
    subst he
    simp only [succOk, List.all_eq_true] at h
    simpa using h f hf
  · dsimp only at h he
    split at h
    · rename_i c _
      simp only [Bool.and_eq_true, succOk, List.all_eq_true] at h
      rcases List.mem_cons.mp he with rfl | he
      · exact h.1 f hf
      · split at h
        · simp only [List.mem_singleton] at he
          subst he
          simp only [List.all_eq_true] at h
          exact h.2 f hf
        · simp at he
    · cases h
  · simp at he

/-- The successor check holds when each successor fact is entailed along each edge and the
    terminator has the shape the check accepts. -/
theorem termInvOk_of_edges {ann ann' : List (List IdxFact)} {F F' : List SFact} {ss : SSt}
    {T : Term} {z : Option LinstrRM} (h : termInvOk ann F ss T z = true)
    (hp : ∀ e ∈ (match T with
          | .fall (some j) => [(j, ([] : List SFact), ss)]
          | .goto tg => [(tg, [], ss)]
          | .cond tg nx =>
              match z with
              | some (.Lcond c _, _) =>
                  (tg, edgeFacts (symDec ss c) true, ss) ::
                    match nx with
                    | some j => [(j, edgeFacts (symDec ss c) false, ss)]
                    | none => []
              | _ => []
          | _ => []),
      ∀ f ∈ annAt ann' e.1, entails (F' ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true) :
    termInvOk ann' F' ss T z = true := by
  unfold termInvOk at h ⊢
  rcases T with (_ | j) | tg | ⟨tg, nx⟩ | _
  · rfl
  · dsimp only at hp
    simp only [succOk, List.all_eq_true]
    intro f hf
    simpa using hp _ (List.mem_singleton_self _) f hf
  · dsimp only at hp
    simp only [succOk, List.all_eq_true]
    intro f hf
    simpa using hp _ (List.mem_singleton_self _) f hf
  · dsimp only at h hp ⊢
    split at h
    · rename_i c _
      simp only [Bool.and_eq_true, succOk, List.all_eq_true]
      dsimp only at hp
      refine ⟨fun f hf => hp _ List.mem_cons_self f hf, ?_⟩
      split
      · rename_i j
        dsimp only at hp
        simp only [List.all_eq_true]
        exact fun f hf => hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) f hf
      · rfl
    · cases h
  · rfl

/-- An accepted block has the facts of its successors entailed along its edges. -/
theorem post_of_blockInvOk {ann : List (List IdxFact)} {B : List LinstrRM} {G : CFG} {k : Nat}
    (h : blockInvOk ann B G k = true) :
    ∀ e ∈ annEdges B G k, ∀ f ∈ annAt ann e.1,
      entails (startF (annAt ann k) ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true := by
  rw [annEdges_eq]
  unfold blockInvOk at h
  generalize B[(G.blk k).stop - 1]? = z at h ⊢
  generalize (G.blk k).term = T at h ⊢
  cases T with
  | ret =>
    intro e he
    split at he <;> simp at he
  | _ =>
    dsimp only at h ⊢
    split at h
    · simp_all
    · simp_all
    · rename_i ss gs hr
      rw [hr]
      simp only [Bool.and_eq_true] at h
      exact termInvOk_edges h.2

/-- An accepted block stays accepted at an annotation that contains its facts and is closed
    along its edges. -/
theorem blockInvOk_of_post {ann ann' : List (List IdxFact)} {B : List LinstrRM} {G : CFG}
    {k : Nat} (h : blockInvOk ann B G k = true)
    (hsub : ∀ f ∈ annAt ann k, f ∈ annAt ann' k)
    (hpost : ∀ e ∈ annEdges B G k, ∀ f ∈ annAt ann' e.1,
      entails (startF (annAt ann' k) ++ e.2.1) (f.toS e.2.2.regs e.2.2.arrs) = true) :
    blockInvOk ann' B G k = true := by
  rw [annEdges_eq] at hpost
  unfold blockInvOk at h ⊢
  have hF : ∀ g ∈ startF (annAt ann k), g ∈ startF (annAt ann' k) := startF_sub hsub
  generalize B[(G.blk k).stop - 1]? = z at h hpost ⊢
  generalize (G.blk k).term = T at h hpost ⊢
  cases T with
  | ret => rfl
  | _ =>
    dsimp only at h hpost ⊢
    split at h
    · rfl
    · cases h
    · rename_i ss gs hr
      rw [hr] at hpost
      simp only [Bool.and_eq_true] at h ⊢
      refine ⟨oblsOk_mono (fun g hg => ?_) h.1, termInvOk_of_edges h.2 hpost⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact List.mem_append_left _ (hF g hg)
      · exact List.mem_append_right _ hg

/-- **The check accepts the annotation whenever it accepts an annotation of candidates**: when
    `idxInvCheckB` accepts the entry facts `entry`, an annotation `ann` whose facts are among the
    candidates `idxCands`, and the body `B`, it accepts `entry`, `idxAnnot entry B` and `B`. -/
theorem idxInvCheckB_idxAnnot {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} {G : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    (hcand : ∀ j < G.blocks.size, ∀ f ∈ annAt ann j, f ∈ idxCands entry B G)
    (h : idxInvCheckB entry ann B = true) : idxInvCheckB entry (idxAnnot entry B) B = true := by
  unfold idxInvCheckB at h ⊢
  rw [hG] at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h ⊢
  have hcont := idxAnnot_contains (entry := entry) hG (P := annAt ann) hcand h.2
    (fun k hk e he _ f hf => post_of_blockInvOk (h.1 k hk) e he f hf)
  refine ⟨fun k hk => blockInvOk_of_post (h.1 k hk) (hcont k hk) (idxAnnot_post hG k hk),
    fun f hf => idxAnnot_entry f hf⟩

/-! ## 6. The gate of commit 4bd6693e -/

/-- `annVisit` with the greedy entailment `entailsG`. -/
def annVisitG (F : List SFact) (es : List (Nat × List SFact × SSt)) (st : WSt) : WSt :=
  es.foldl (fun (a, pend, q) (j, ex, ss) =>
    let old := a.getD j []
    let new := old.filter fun f => entailsG (F ++ ex) (f.toS ss.regs ss.arrs)
    if new.length < old.length then
      if pend.getD j false then (a.set! j new, pend, q)
      else (a.set! j new, pend.set! j true, q.enqueue j)
    else (a, pend, q)) st

/-- `annWork` with the greedy entailment `entailsG`. -/
def annWorkG (E : Array (List (Nat × List SFact × SSt))) : Nat → WSt → Array (List IdxFact)
  | 0, (a, _, _) => a
  | fuel + 1, (a, pend, q) =>
      match q.dequeue? with
      | none => a
      | some (k, q) =>
          annWorkG E fuel (annVisitG (startF (a.getD k [])) (E.getD k []) (a, pend.set! k false, q))

/-- **The annotation of the gate of commit 4bd6693e**: `idxAnnot` with the greedy entailment
    `entailsG` in the restriction. -/
def idxAnnotG (entry : List IdxFact) (B : List LinstrRM) : List (List IdxFact) :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      let nb := G.blocks.size
      let cs := idxCands entry B G
      let a0 := (Array.range nb).map fun k =>
        if k = 0 then cs.filter fun f => entailsG (startF entry) (f.toS STerm.reg SArr.cell)
        else cs
      let E := (Array.range nb).map (annEdges B G)
      let q0 := (List.range nb).foldl (fun q k => q.enqueue k) Std.Queue.empty
      (annWorkG E (nb * (cs.length + 1) + 1) (a0, Array.replicate nb true, q0)).toList
  | none => []

/-- A fact of a set array is in the array before the set or in the value set. -/
theorem mem_getD_set!_cases {a : Array (List IdxFact)} {k j : Nat} {v : List IdxFact}
    {f : IdxFact} (h : f ∈ (a.set! k v).getD j []) : f ∈ a.getD j [] ∨ f ∈ v := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hk : j < a.size
    · rw [getD_set!_self hk] at h
      exact Or.inr h
    · rw [getD_eq_default (by simpa using hk)] at h
      simp at h
  · rw [getD_set!_ne hjk] at h
    exact Or.inl h

theorem annVisitG_sub (F : List SFact) :
    ∀ (es : List (Nat × List SFact × SSt)) (st : WSt) (j : Nat),
      ∀ f ∈ (annVisitG F es st).1.getD j [], f ∈ st.1.getD j []
  | [], _, _ => fun _ h => h
  | (i, ex, ss) :: es, (a, pend, q), j => by
      intro f hf
      unfold annVisitG at hf
      rw [List.foldl_cons] at hf
      dsimp only at hf
      have step : ∀ st' : WSt, (∀ j, ∀ f ∈ st'.1.getD j [], f ∈ a.getD j []) →
          f ∈ (es.foldl _ st').1.getD j [] → f ∈ a.getD j [] := fun st' hst' hf' =>
        hst' j f (annVisitG_sub F es st' j f hf')
      have hset : ∀ j, ∀ f ∈ (a.set! i ((a.getD i []).filter fun f =>
          entailsG (F ++ ex) (f.toS ss.regs ss.arrs))).getD j [], f ∈ a.getD j [] := by
        intro j f hf
        rcases mem_getD_set!_cases hf with h | h
        · exact h
        · have := (List.mem_filter.mp h).1
          by_cases hji : j = i
          · subst hji; exact this
          · rw [getD_set!_ne hji] at hf; exact hf
      split at hf
      · split at hf
        · exact step _ hset hf
        · exact step _ hset hf
      · exact step _ (fun _ _ h => h) hf

theorem annWorkG_sub (E : Array (List (Nat × List SFact × SSt))) :
    ∀ (fuel : Nat) (st : WSt) (j : Nat), ∀ f ∈ (annWorkG E fuel st).getD j [], f ∈ st.1.getD j []
  | 0, (_, _, _), _ => fun _ h => h
  | fuel + 1, (a, pend, q), j => by
      intro f hf
      unfold annWorkG at hf
      split at hf
      · exact hf
      · rename_i k q' _
        exact annVisitG_sub _ _ (a, pend.set! k false, q') j f (annWorkG_sub E fuel _ j f hf)

/-- The facts of the annotation of commit 4bd6693e are candidates. -/
theorem idxAnnotG_cand {entry : List IdxFact} {B : List LinstrRM} {G : CFG}
    (hG : cfgOf (B.map Prod.fst) = some G) :
    ∀ j < G.blocks.size, ∀ f ∈ annAt (idxAnnotG entry B) j, f ∈ idxCands entry B G := by
  intro j hj f hf
  simp only [idxAnnotG, hG, annAt, List.getD_eq_getElem?_getD, Array.getElem?_toList] at hf
  have := annWorkG_sub _ _ _ j f (by simpa [Array.getD_eq_getD_getElem?] using hf)
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hj,
    ↓reduceIte, Option.map_some, Option.getD_some] at this
  split at this
  · exact (List.mem_filter.mp this).1
  · exact this

/-- **The gate does not shrink**: every entry and body that the gate of commit 4bd6693e
    accepted, `idxInvCheckBG` at its annotation `idxAnnotG`, the gate accepts,
    `idxInvCheckB` at the annotation `idxAnnot`. -/
theorem idxInvCheckB_idxAnnot_of_G {entry : List IdxFact} {B : List LinstrRM}
    (h : idxInvCheckBG entry (idxAnnotG entry B) B = true) :
    idxInvCheckB entry (idxAnnot entry B) B = true := by
  have h' := idxInvCheckB_of_G h
  unfold idxInvCheckB at h'
  split at h'
  · rename_i G hG
    refine idxInvCheckB_idxAnnot hG (idxAnnotG_cand hG) ?_
    unfold idxInvCheckB
    rw [hG]
    exact h'
  · cases h'

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
