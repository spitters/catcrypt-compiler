/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference

/-!
# Location injectivity of the allocator's renaming on overlapping hulls

`physBodyWithStores` renames every register operand through
`rmap (.reg n) = .reg (allocName body tbl n)` (`physBodyWithStores_allocName`) over the
table `tbl = physAllocTbl body outStoreMap reservedVec`.
The renaming is global over the body and reuses registers and frame cells across
names whose live ranges are disjoint. This module proves that it separates names
whose live ranges overlap.

## Main results

* `allocName_injOn_overlap`: two distinct body names (no hardware, frame-slot or
  `%livepin` name) whose live ranges over `bodyTraceOut` overlap get distinct images
  under the allocator's renaming `allocName`.
* `allocName_injOn_liveAt`: the same for two names live at one position of
  `bodyTraceOut`.

## Contents

* **Liveness of body names.** Every name of `bodyNames body` touches the trace
  `bodyTrace body`, so its slot is a live item of `bodyTrace body` and of
  `bodyTraceOut body outStoreMap`, inside the slot universe
  (`live_out_of_mem_bodyNames`).
* **The scan table.** `physTableOut_no_collision`: two distinct body names with
  overlapping ranges over `bodyTraceOut` have distinct entries in `physTableOut`
  (from `physTableClassed_no_collision`).
* **The looped call path.** `calleeFirstPhys_inj`: the callee-saved-first
  permutation is injective.
* **The straight-line call path.** `straightCallRelocTable_eq` exposes the two
  loops of `straightCallRelocTableCore` as `usedLoop` and `relocLoop`;
  `usedLoop_used` marks the raw index of every live non-hardware slot used;
  `relocLoop_inv` (invariant `RelocInv`) shows that the relocation hands distinct
  values to distinct used raw indices, each a pool register or a fresh spill index
  in `[gpSpillBase, gpSpillBase + numGPRegs)`; `straightCallComposeTable_ne`
  assembles these into injectivity of the composed table on body names.
* **The renaming.** `allocName_injOn_overlap` for overlapping live ranges and
  `allocName_injOn_liveAt` for two names live at one position of `bodyTraceOut`.

The statements are at the x86 ABI (`x86Abi`), the ABI of `physRegName_inj`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCertInj

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

theorem touched_of_mem_bodyNames {body : Lcmd} {a : String} (ha : a ∈ bodyNames body) :
    ∃ e ∈ bodyTrace body, nameSlot body a ∈ e.touched := by
  unfold bodyNames at ha
  rw [List.mem_eraseDups, List.mem_flatMap] at ha
  obtain ⟨⟨d, s⟩, hds, hmem⟩ := ha
  refine ⟨{ wr := (d.map (nameSlot body)).getD 0, rds := s.map (nameSlot body) }, ?_, ?_⟩
  · unfold bodyTrace
    exact List.mem_map.mpr ⟨(d, s), hds, rfl⟩
  · rcases List.mem_append.mp hmem with h | h
    · cases d with
      | none => simp at h
      | some x =>
        simp only [Option.toList_some, List.mem_singleton] at h
        subst h
        simp [PhysEvent.touched]
    · simp [PhysEvent.touched, List.mem_map_of_mem h]

theorem live_of_touched {tr : List PhysEvent} {s : Nat} (h : ∃ e ∈ tr, s ∈ e.touched) :
    s < physUniverse tr ∧ ∃ it ∈ physLiveItems tr, it.1 = s := by
  obtain ⟨e, he, hs⟩ := h
  have hu : s < physUniverse tr := lt_physUniverse_of_touched he hs
  refine ⟨hu, physLiveItems_mem_of_start_lt hu ?_⟩
  show physFirstTouch tr s < tr.length
  unfold physFirstTouch
  cases hf : tr.zipIdx.find? (fun p => p.1.touched.contains s) with
  | none =>
    exfalso
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hmem : (tr[i], i) ∈ tr.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]; simp [hi]
    have := List.find?_eq_none.mp hf _ hmem
    simp [hs] at this
  | some q =>
    obtain ⟨x, j⟩ := q
    have hq := List.mem_of_find?_eq_some hf
    rw [List.mem_zipIdx_iff_getElem?] at hq
    exact (List.getElem?_eq_some_iff.mp hq).1

theorem mem_bodyTraceOut_of_mem {body : Lcmd} {outStoreMap : OutStoreMap} {e : PhysEvent}
    (he : e ∈ bodyTrace body) : e ∈ bodyTraceOut body outStoreMap := by
  unfold bodyTraceOut
  split
  · exact he
  · exact List.mem_append_left _ he

theorem live_out_of_mem_bodyNames {body : Lcmd} {outStoreMap : OutStoreMap} {a : String}
    (ha : a ∈ bodyNames body) :
    nameSlot body a < physUniverse (bodyTraceOut body outStoreMap) ∧
      ∃ it ∈ physLiveItems (bodyTraceOut body outStoreMap), it.1 = nameSlot body a := by
  obtain ⟨e, he, hs⟩ := touched_of_mem_bodyNames ha
  exact live_of_touched ⟨e, mem_bodyTraceOut_of_mem he, hs⟩

theorem physTableClassed_size (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat) :
    (physTableClassed tr vecArr reserved reservedVec).size = physUniverse tr := by
  simp [physTableClassed]

theorem physTableOut_no_collision {body : Lcmd} {outStoreMap : OutStoreMap}
    {reservedVec : List Nat} {a b : String}
    (hfit : numGPRegs + (physLiveItems (bodyTraceOut body outStoreMap)).length ≤ vectorBase)
    (ha : a ∈ bodyNames body) (hb : b ∈ bodyNames body) (hne : a ≠ b)
    (hov : physRangesOverlap (physLiveRange (bodyTraceOut body outStoreMap) (nameSlot body a))
      (physLiveRange (bodyTraceOut body outStoreMap) (nameSlot body b))) :
    physMapTabled (physTableOut body outStoreMap reservedVec) (nameSlot body a)
      ≠ physMapTabled (physTableOut body outStoreMap reservedVec) (nameSlot body b) := by
  obtain ⟨hu1, hl1⟩ := live_out_of_mem_bodyNames (outStoreMap := outStoreMap) ha
  obtain ⟨hu2, hl2⟩ := live_out_of_mem_bodyNames (outStoreMap := outStoreMap) hb
  have hsl : nameSlot body a ≠ nameSlot body b := fun h => hne (nameSlot_injOn ha hb h)
  exact physTableClassed_no_collision _ _ _ _ hfit hsl hu1 hu2 hl1 hl2 hov

theorem calleeFirstPhys_inj {p q : Nat} (h : calleeFirstPhys p = calleeFirstPhys q) : p = q := by
  have hn : numGPRegs = 13 := rfl
  have hlen : calleeSavedFirstOrder.length = 13 := rfl
  have hnd : calleeSavedFirstOrder.Nodup := by decide
  have hbd : ∀ x ∈ calleeSavedFirstOrder, x < 13 := by decide
  unfold calleeFirstPhys at h
  rw [hn] at h
  by_cases hp : p < 13 <;> by_cases hq : q < 13 <;> simp only [hp, hq, if_true, if_false] at h
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show p < calleeSavedFirstOrder.length by omega),
      List.getElem?_eq_getElem (show q < calleeSavedFirstOrder.length by omega),
      Option.getD_some] at h
    exact (hnd.getElem_inj_iff).mp h
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show p < calleeSavedFirstOrder.length by omega),
      Option.getD_some] at h
    have := hbd _ (List.getElem_mem (show p < calleeSavedFirstOrder.length by omega))
    omega
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show q < calleeSavedFirstOrder.length by omega),
      Option.getD_some] at h
    have := hbd _ (List.getElem_mem (show q < calleeSavedFirstOrder.length by omega))
    omega
  · exact h

/-- One step of the relocation loop of `straightCallRelocTableCore` over raw index
    `raw`, on the state (relocation, remaining callee-saved pool, remaining scratch
    pool, next fresh spill index). -/
def relocBody (usedRaw crossRaw : Array Bool) (raw : Nat)
    (st : Array Nat × List Nat × List Nat × Nat) :
    Id (ForInStep (Array Nat × List Nat × List Nat × Nat)) :=
  if usedRaw[raw]?.getD false = true then
    if crossRaw[raw]?.getD false = true then
      match st.2.1 with
      | r :: rest => pure (ForInStep.yield (st.1.set! raw r, rest, st.2.2.1, st.2.2.2))
      | [] => pure (ForInStep.yield (st.1.set! raw st.2.2.2, st.2.1, st.2.2.1, st.2.2.2 + 1))
    else
      match st.2.2.1 with
      | r :: rest => pure (ForInStep.yield (st.1.set! raw r, st.2.1, rest, st.2.2.2))
      | [] => pure (ForInStep.yield (st.1.set! raw st.2.2.2, st.2.1, st.2.2.1, st.2.2.2 + 1))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2.1, st.2.2.2))

/-- The relocation loop of `straightCallRelocTableCore`, from the used and
    crossing raw-index masks and the first fresh spill index. -/
def relocLoop (usedRaw crossRaw : Array Bool) (spillBase : Nat) : Array Nat :=
  (Id.run (forIn [:numGPRegs]
    (Array.range numGPRegs, straightCallCalleeSavedPool, straightCallScratchPool, spillBase)
    (relocBody usedRaw crossRaw))).1

/-- One step of the mask loop of `straightCallRelocTableCore` over a live item. -/
def usedBody (body : Lcmd) (tbl : Array Nat) (isRead : Array Bool) (it : Nat × Nat × Nat)
    (acc : Array Bool × Array Bool) : Id (ForInStep (Array Bool × Array Bool)) :=
  if ((bodyNames body).toArray[it.1]?.getD "" != "%livepin" &&
      !isHwRegName ((bodyNames body).toArray[it.1]?.getD "")) = true then
    if physMapTabled tbl it.1 < numGPRegs then
      if (((bodyCallTracePositions body).any fun p =>
            decide ((if (((bodyNames body).toArray[it.1]?.getD "").startsWith "a" &&
                (strDropToNat? ((bodyNames body).toArray[it.1]?.getD "") 1).isSome) = true
              then 0 else it.2.1) < p) && decide (p ≤ it.2.2)) ||
          !isRead[it.1]?.getD true) = true then
        pure (ForInStep.yield
          (acc.1.set! (physMapTabled tbl it.1) true, acc.2.set! (physMapTabled tbl it.1) true))
      else pure (ForInStep.yield (acc.1.set! (physMapTabled tbl it.1) true, acc.2))
    else pure (ForInStep.yield (acc.1, acc.2))
  else pure (ForInStep.yield (acc.1, acc.2))

/-- The mask loop of `straightCallRelocTableCore`. -/
def usedLoop (body : Lcmd) (tbl : Array Nat) (isRead : Array Bool) : Array Bool × Array Bool :=
  Id.run (forIn (physLiveItems (bodyTrace body))
    (Array.replicate numGPRegs false, Array.replicate numGPRegs false) (usedBody body tbl isRead))

theorem straightCallRelocTable_eq (body : Lcmd) (tbl : Array Nat) :
    ∃ isRead : Array Bool, straightCallRelocTable body tbl
      = relocLoop (usedLoop body tbl isRead).1 (usedLoop body tbl isRead).2
          (gpSpillBase (bodyVecSlots body) tbl) :=
  ⟨_, rfl⟩

/-- The name condition under which the mask loop marks a slot's raw index used. -/
def maskName (body : Lcmd) (s : Nat) : Bool :=
  ((bodyNames body).toArray[s]?.getD "" != "%livepin" &&
    !isHwRegName ((bodyNames body).toArray[s]?.getD ""))

theorem usedBody_step (body : Lcmd) (tbl : Array Nat) (isRead : Array Bool)
    (it : Nat × Nat × Nat) (acc : Array Bool × Array Bool) (h : acc.1.size = numGPRegs) :
    ∃ acc', usedBody body tbl isRead it acc = pure (.yield acc') ∧ acc'.1.size = numGPRegs ∧
      (∀ r : Nat, acc.1[r]?.getD false = true → acc'.1[r]?.getD false = true) ∧
      (maskName body it.1 = true → physMapTabled tbl it.1 < numGPRegs →
        acc'.1[physMapTabled tbl it.1]?.getD false = true) := by
  unfold usedBody
  by_cases hc : maskName body it.1 = true
  · have hc' := hc
    unfold maskName at hc'
    rw [if_pos hc']
    by_cases hlt : physMapTabled tbl it.1 < numGPRegs
    · rw [if_pos hlt]
      have hset : ∀ (c : Array Bool), (acc.1.set! (physMapTabled tbl it.1) true).size = numGPRegs
          ∧ (∀ r : Nat, acc.1[r]?.getD false = true →
              (acc.1.set! (physMapTabled tbl it.1) true)[r]?.getD false = true)
          ∧ (acc.1.set! (physMapTabled tbl it.1) true)[physMapTabled tbl it.1]?.getD false
              = true := by
        intro _
        refine ⟨by simp [h], ?_, ?_⟩
        · intro r hr
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
          split
          · simp_all
          · exact hr
        · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
          simp [h, hlt]
      obtain ⟨h1, h2, h3⟩ := hset #[]
      split_ifs <;> first
        | exact ⟨(acc.1.set! (physMapTabled tbl it.1) true,
            acc.2.set! (physMapTabled tbl it.1) true), rfl, h1, h2, fun _ _ => h3⟩
        | exact ⟨(acc.1.set! (physMapTabled tbl it.1) true, acc.2), rfl, h1, h2,
            fun _ _ => h3⟩
    · rw [if_neg hlt]
      exact ⟨_, rfl, h, fun r hr => hr, fun _ h' => absurd h' hlt⟩
  · have hc' : ¬ ((bodyNames body).toArray[it.1]?.getD "" != "%livepin" &&
        !isHwRegName ((bodyNames body).toArray[it.1]?.getD "")) = true := hc
    rw [if_neg hc']
    exact ⟨_, rfl, h, fun r hr => hr, fun h' => absurd h' hc⟩

theorem usedLoop_aux (body : Lcmd) (tbl : Array Nat) (isRead : Array Bool) :
    ∀ (l : List (Nat × Nat × Nat)) (acc : Array Bool × Array Bool), acc.1.size = numGPRegs →
      (Id.run (forIn l acc (usedBody body tbl isRead))).1.size = numGPRegs ∧
      (∀ r : Nat, acc.1[r]?.getD false = true →
        (Id.run (forIn l acc (usedBody body tbl isRead))).1[r]?.getD false = true) ∧
      (∀ it ∈ l, maskName body it.1 = true → physMapTabled tbl it.1 < numGPRegs →
        (Id.run (forIn l acc (usedBody body tbl isRead))).1[physMapTabled tbl it.1]?.getD false
          = true)
  | [], acc, h => by simp [h]
  | it :: l, acc, h => by
    obtain ⟨acc', hstep, hs, hmono, hset⟩ := usedBody_step body tbl isRead it acc h
    have hfor : Id.run (forIn (it :: l) acc (usedBody body tbl isRead))
        = Id.run (forIn l acc' (usedBody body tbl isRead)) := by
      simp [List.forIn_cons, hstep]
    obtain ⟨ih1, ih2, ih3⟩ := usedLoop_aux body tbl isRead l acc' hs
    rw [hfor]
    refine ⟨ih1, fun r hr => ih2 r (hmono r hr), ?_⟩
    intro it' hit' hc hlt
    rcases List.mem_cons.mp hit' with rfl | h'
    · exact ih2 _ (hset hc hlt)
    · exact ih3 it' h' hc hlt

theorem usedLoop_used (body : Lcmd) (tbl : Array Nat) (isRead : Array Bool)
    {it : Nat × Nat × Nat} (hit : it ∈ physLiveItems (bodyTrace body))
    (hc : maskName body it.1 = true) (hlt : physMapTabled tbl it.1 < numGPRegs) :
    (usedLoop body tbl isRead).1[physMapTabled tbl it.1]?.getD false = true :=
  (usedLoop_aux body tbl isRead _ _ (by simp)).2.2 it hit hc hlt

/-! ## The relocation loop is injective on the used raw indices -/

/-- The values the relocation loop has handed out at state `σ`: the consumed part
    of each pool and the fresh spill indices in `[sb, σ.ns)`. -/
def RelocAssigned (sb : Nat) (σ : Array Nat × List Nat × List Nat × Nat) (v : Nat) : Prop :=
  (v ∈ straightCallCalleeSavedPool ∧ v ∉ σ.2.1) ∨
    (v ∈ straightCallScratchPool ∧ v ∉ σ.2.2.1) ∨ (sb ≤ v ∧ v < σ.2.2.2)

/-- The invariant of the relocation loop after the raw indices below `k`. -/
def RelocInv (u : Array Bool) (sb k : Nat) (σ : Array Nat × List Nat × List Nat × Nat) :
    Prop :=
  σ.1.size = numGPRegs ∧
  σ.2.1.Nodup ∧ (∀ v ∈ σ.2.1, v ∈ straightCallCalleeSavedPool) ∧
  σ.2.2.1.Nodup ∧ (∀ v ∈ σ.2.2.1, v ∈ straightCallScratchPool) ∧
  sb ≤ σ.2.2.2 ∧ σ.2.2.2 ≤ sb + k ∧
  (∀ r, r < k → u[r]?.getD false = true → RelocAssigned sb σ (σ.1[r]?.getD r)) ∧
  (∀ r₁ r₂, r₁ < k → r₂ < k → u[r₁]?.getD false = true → u[r₂]?.getD false = true →
    r₁ ≠ r₂ → σ.1[r₁]?.getD r₁ ≠ σ.1[r₂]?.getD r₂)

theorem getD_set! (a : Array Nat) (k x r : Nat) (hk : k < a.size) :
    (a.set! k x)[r]?.getD r = if k = r then x else a[r]?.getD r := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : k = r
  · subst h; simp [hk]
  · simp [h]

theorem calleeSavedPool_lt {v : Nat} (h : v ∈ straightCallCalleeSavedPool) : v < numGPRegs := by
  simp only [straightCallCalleeSavedPool, List.mem_cons, List.mem_nil_iff, or_false] at h
  have hn : numGPRegs = 13 := rfl
  omega

theorem scratchPool_lt {v : Nat} (h : v ∈ straightCallScratchPool) : v < numGPRegs := by
  simp only [straightCallScratchPool, List.mem_cons, List.mem_nil_iff, or_false] at h
  have hn : numGPRegs = 13 := rfl
  omega

theorem pools_disjoint {v : Nat} (h1 : v ∈ straightCallCalleeSavedPool)
    (h2 : v ∈ straightCallScratchPool) : False := by
  simp only [straightCallCalleeSavedPool, straightCallScratchPool, List.mem_cons,
    List.mem_nil_iff, or_false] at h1 h2
  omega

theorem relocInv_skip {u : Array Bool} {sb k : Nat} {σ : Array Nat × List Nat × List Nat × Nat}
    (hI : RelocInv u sb k σ) (hu : ¬ u[k]?.getD false = true) :
    RelocInv u sb (k + 1) (σ.1, σ.2.1, σ.2.2.1, σ.2.2.2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hI
  refine ⟨h1, h2, h3, h4, h5, h6, show σ.2.2.2 ≤ sb + (k + 1) by omega, ?_, ?_⟩
  · intro r hr hur
    have : r ≠ k := fun e => hu (e ▸ hur)
    exact h8 r (by omega) hur
  · intro r₁ r₂ hr₁ hr₂ hu₁ hu₂ hne
    have : r₁ ≠ k := fun e => hu (e ▸ hu₁)
    have : r₂ ≠ k := fun e => hu (e ▸ hu₂)
    exact h9 r₁ r₂ (by omega) (by omega) hu₁ hu₂ hne

theorem relocInv_assign {u : Array Bool} {sb k : Nat}
    {σ σ' : Array Nat × List Nat × List Nat × Nat} {x : Nat}
    (hI : RelocInv u sb k σ) (hk : k < numGPRegs) (hσ1 : σ'.1 = σ.1.set! k x)
    (hc1 : σ'.2.1.Nodup) (hc2 : ∀ v ∈ σ'.2.1, v ∈ straightCallCalleeSavedPool)
    (hn1 : σ'.2.2.1.Nodup) (hn2 : ∀ v ∈ σ'.2.2.1, v ∈ straightCallScratchPool)
    (hs1 : sb ≤ σ'.2.2.2) (hs2 : σ'.2.2.2 ≤ sb + (k + 1))
    (hmono : ∀ v, RelocAssigned sb σ v → RelocAssigned sb σ' v)
    (hx : RelocAssigned sb σ' x) (hfresh : ¬ RelocAssigned sb σ x) :
    RelocInv u sb (k + 1) σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hI
  have hks : k < σ.1.size := by omega
  have hget : ∀ r, σ'.1[r]?.getD r = if k = r then x else σ.1[r]?.getD r := by
    intro r; rw [hσ1]; exact getD_set! _ _ _ _ hks
  refine ⟨by rw [hσ1]; simp [h1], hc1, hc2, hn1, hn2, hs1, hs2, ?_, ?_⟩
  · intro r hr hur
    rw [hget]
    by_cases hkr : k = r
    · rw [if_pos hkr]; exact hx
    · rw [if_neg hkr]; exact hmono _ (h8 r (by omega) hur)
  · intro r₁ r₂ hr₁ hr₂ hu₁ hu₂ hne
    rw [hget, hget]
    by_cases hk1 : k = r₁ <;> by_cases hk2 : k = r₂
    · exact absurd (hk1.symm.trans hk2) hne
    · rw [if_pos hk1, if_neg hk2]
      intro he
      exact hfresh (he ▸ h8 r₂ (by omega) hu₂)
    · rw [if_neg hk1, if_pos hk2]
      intro he
      exact hfresh (he ▸ h8 r₁ (by omega) hu₁)
    · rw [if_neg hk1, if_neg hk2]
      exact h9 r₁ r₂ (by omega) (by omega) hu₁ hu₂ hne

/-- Taking the head of a pool keeps the invariant. -/
theorem relocInv_pool_head {u : Array Bool} {sb k : Nat} {R : Array Nat}
    {r₀ : Nat} {rest np : List Nat} {ns : Nat} (hsb : numGPRegs ≤ sb)
    (hI : RelocInv u sb k (R, r₀ :: rest, np, ns)) (hk : k < numGPRegs) :
    RelocInv u sb (k + 1) (R.set! k r₀, rest, np, ns) := by
  have hI' := hI
  obtain ⟨_, h2, h3, h4, h5, h6, h7, _, _⟩ := hI'
  have hr₀ : r₀ ∈ straightCallCalleeSavedPool := h3 r₀ List.mem_cons_self
  have hnot : r₀ ∉ rest := (List.nodup_cons.mp h2).1
  refine relocInv_assign hI hk rfl (List.nodup_cons.mp h2).2
    (fun v hv => h3 v (List.mem_cons_of_mem _ hv)) h4 h5 h6
    (show ns ≤ sb + (k + 1) from Nat.le_succ_of_le h7) ?_
    (Or.inl ⟨hr₀, hnot⟩) ?_
  · intro v hv
    rcases hv with ⟨hv1, hv2⟩ | hv | hv
    · exact Or.inl ⟨hv1, fun h => hv2 (List.mem_cons_of_mem _ h)⟩
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
    · exact h List.mem_cons_self
    · exact pools_disjoint hr₀ h
    · have := calleeSavedPool_lt hr₀; omega

/-- Taking the head of the scratch pool keeps the invariant. -/
theorem relocInv_scratch_head {u : Array Bool} {sb k : Nat} {R : Array Nat}
    {r₀ : Nat} {cp rest : List Nat} {ns : Nat} (hsb : numGPRegs ≤ sb)
    (hI : RelocInv u sb k (R, cp, r₀ :: rest, ns)) (hk : k < numGPRegs) :
    RelocInv u sb (k + 1) (R.set! k r₀, cp, rest, ns) := by
  have hI' := hI
  obtain ⟨_, h2, h3, h4, h5, h6, h7, _, _⟩ := hI'
  have hr₀ : r₀ ∈ straightCallScratchPool := h5 r₀ List.mem_cons_self
  have hnot : r₀ ∉ rest := (List.nodup_cons.mp h4).1
  refine relocInv_assign hI hk rfl h2 h3 (List.nodup_cons.mp h4).2
    (fun v hv => h5 v (List.mem_cons_of_mem _ hv)) h6
    (show ns ≤ sb + (k + 1) from Nat.le_succ_of_le h7) ?_
    (Or.inr (Or.inl ⟨hr₀, hnot⟩)) ?_
  · intro v hv
    rcases hv with hv | ⟨hv1, hv2⟩ | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inl ⟨hv1, fun h => hv2 (List.mem_cons_of_mem _ h)⟩)
    · exact Or.inr (Or.inr hv)
  · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩)
    · exact pools_disjoint h hr₀
    · exact h List.mem_cons_self
    · have := scratchPool_lt hr₀; omega

/-- Handing out a fresh spill index keeps the invariant. -/
theorem relocInv_spill {u : Array Bool} {sb k : Nat} {R : Array Nat}
    {cp np : List Nat} {ns : Nat} (hsb : numGPRegs ≤ sb)
    (hI : RelocInv u sb k (R, cp, np, ns)) (hk : k < numGPRegs) :
    RelocInv u sb (k + 1) (R.set! k ns, cp, np, ns + 1) := by
  have hI' := hI
  obtain ⟨_, h2, h3, h4, h5, h6, h7, _, _⟩ := hI'
  have h6' : sb ≤ ns := h6
  have h7' : ns ≤ sb + k := h7
  refine relocInv_assign hI hk rfl h2 h3 h4 h5 (show sb ≤ ns + 1 by omega)
    (show ns + 1 ≤ sb + (k + 1) by omega) ?_
    (Or.inr (Or.inr ⟨h6', show ns < ns + 1 by omega⟩)) ?_
  · intro v hv
    rcases hv with hv | hv | ⟨hv1, hv2⟩
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr ⟨hv1, show v < ns + 1 by have : v < ns := hv2; omega⟩)
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
    · have := calleeSavedPool_lt h; omega
    · have := scratchPool_lt h; omega
    · have : ns < ns := h; omega

theorem relocBody_step {u c : Array Bool} {sb k : Nat}
    {σ : Array Nat × List Nat × List Nat × Nat} (hsb : numGPRegs ≤ sb)
    (hI : RelocInv u sb k σ) (hk : k < numGPRegs) :
    ∃ σ', relocBody u c k σ = pure (.yield σ') ∧ RelocInv u sb (k + 1) σ' := by
  obtain ⟨R, cp, np, ns⟩ := σ
  unfold relocBody
  by_cases hu : u[k]?.getD false = true
  · rw [if_pos hu]
    by_cases hc : c[k]?.getD false = true
    · rw [if_pos hc]
      cases cp with
      | cons r₀ rest => exact ⟨_, rfl, relocInv_pool_head hsb hI hk⟩
      | nil => exact ⟨_, rfl, relocInv_spill hsb hI hk⟩
    · rw [if_neg hc]
      cases np with
      | cons r₀ rest => exact ⟨_, rfl, relocInv_scratch_head hsb hI hk⟩
      | nil => exact ⟨_, rfl, relocInv_spill hsb hI hk⟩
  · rw [if_neg hu]
    exact ⟨_, rfl, relocInv_skip hI hu⟩

theorem relocLoop_aux {u c : Array Bool} {sb : Nat} (hsb : numGPRegs ≤ sb) :
    ∀ (m k : Nat) (σ : Array Nat × List Nat × List Nat × Nat), k + m = numGPRegs →
      RelocInv u sb k σ →
      RelocInv u sb numGPRegs (Id.run (forIn (List.range' k m) σ (relocBody u c)))
  | 0, k, σ, hkm, hI => by simpa [← hkm] using hI
  | m + 1, k, σ, hkm, hI => by
    obtain ⟨σ', hstep, hI'⟩ := relocBody_step (c := c) hsb hI (by omega)
    have hfor : Id.run (forIn (List.range' k (m + 1)) σ (relocBody u c))
        = Id.run (forIn (List.range' (k + 1) m) σ' (relocBody u c)) := by
      simp [List.range'_succ, List.forIn_cons, hstep]
    rw [hfor]
    exact relocLoop_aux hsb m (k + 1) σ' (by omega) hI'

theorem relocLoop_inv (u c : Array Bool) {sb : Nat} (hsb : numGPRegs ≤ sb) :
    ∃ σ : Array Nat × List Nat × List Nat × Nat, relocLoop u c sb = σ.1 ∧
      RelocInv u sb numGPRegs σ := by
  refine ⟨_, ?_, relocLoop_aux (c := c) hsb numGPRegs 0
    (Array.range numGPRegs, straightCallCalleeSavedPool, straightCallScratchPool, sb)
    (by omega) ?_⟩
  · unfold relocLoop
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp [Std.Legacy.Range.size]
  · refine ⟨by simp, (by decide : straightCallCalleeSavedPool.Nodup), fun v hv => hv,
      (by decide : straightCallScratchPool.Nodup), fun v hv => hv, le_refl sb,
      Nat.le_add_right sb 0, fun r hr => absurd hr (Nat.not_lt_zero r),
      fun r₁ _ hr => absurd hr (Nat.not_lt_zero r₁)⟩

/-! ## The fresh spill base -/

theorem gpSpillBase_foldl_ge (vecArr : Array Bool) :
    ∀ (l : List (Nat × Nat)) (b : Nat), b ≤ l.foldl
      (fun b e => if !slotIsVec vecArr e.2 && numGPRegs ≤ e.1 then Nat.max b (e.1 + 1) else b) b
  | [], _ => le_refl _
  | e :: l, b => by
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (gpSpillBase_foldl_ge vecArr l _)
    split
    · exact Nat.le_max_left _ _
    · exact le_refl _

theorem gpSpillBase_foldl_gt (vecArr : Array Bool) :
    ∀ (l : List (Nat × Nat)) (b : Nat) (e : Nat × Nat), e ∈ l →
      slotIsVec vecArr e.2 = false → numGPRegs ≤ e.1 →
      e.1 < l.foldl
        (fun b e => if !slotIsVec vecArr e.2 && numGPRegs ≤ e.1 then Nat.max b (e.1 + 1)
          else b) b
  | [], _, _, he, _, _ => absurd he (by simp)
  | e' :: l, b, e, he, hv, hg => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | he'
    · refine Nat.lt_of_lt_of_le ?_ (gpSpillBase_foldl_ge vecArr l _)
      simp only [hv, Bool.not_false, decide_eq_true hg, Bool.and_self, if_true]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    · exact gpSpillBase_foldl_gt vecArr l _ e he' hv hg

theorem numGPRegs_le_gpSpillBase (vecArr : Array Bool) (tbl : Array Nat) :
    numGPRegs ≤ gpSpillBase vecArr tbl :=
  gpSpillBase_foldl_ge vecArr _ _

theorem lt_gpSpillBase {vecArr : Array Bool} {tbl : Array Nat} {s : Nat} (hs : s < tbl.size)
    (hv : slotIsVec vecArr s = false) (hg : numGPRegs ≤ tbl[s]) :
    tbl[s] < gpSpillBase vecArr tbl := by
  unfold gpSpillBase
  refine gpSpillBase_foldl_gt vecArr _ _ (tbl[s], s) ?_ hv hg
  rw [List.mem_zipIdx_iff_getElem?]
  simp [hs]

theorem physMapTabled_map (tbl : Array Nat) (f : Nat → Nat) {s : Nat} (hs : s < tbl.size) :
    physMapTabled (tbl.map f) s = f (physMapTabled tbl s) := by
  unfold physMapTabled
  simp [hs]

theorem physMapTabled_of_lt {tbl : Array Nat} {s : Nat} (hs : s < tbl.size) :
    physMapTabled tbl s = tbl[s] := by
  unfold physMapTabled
  simp [hs]

/-- A name of the body has its own name at its slot of the name array. -/
theorem bodyNames_getD_nameSlot {body : Lcmd} {a : String} (ha : a ∈ bodyNames body) :
    (bodyNames body).toArray[nameSlot body a]?.getD "" = a := by
  have hlt : nameSlot body a < (bodyNames body).length := List.idxOf_lt_length_iff.mpr ha
  simp only [List.getElem?_toArray, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact List.getElem_idxOf hlt

theorem maskName_nameSlot {body : Lcmd} {a : String} (ha : a ∈ bodyNames body)
    (hpin : a ≠ "%livepin") (hhw : isHwRegName a = false) :
    maskName body (nameSlot body a) = true := by
  unfold maskName
  rw [bodyNames_getD_nameSlot ha, hhw]
  simp [hpin]

theorem relocAssigned_bound {sb x : Nat} {σ : Array Nat × List Nat × List Nat × Nat}
    (hx : RelocAssigned sb σ x) (hns : σ.2.2.2 ≤ sb + numGPRegs) :
    x < numGPRegs ∨ (sb ≤ x ∧ x < sb + numGPRegs) := by
  rcases hx with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h1, h2⟩
  · exact Or.inl (calleeSavedPool_lt h)
  · exact Or.inl (scratchPool_lt h)
  · exact Or.inr ⟨h1, by omega⟩

/-- A relocated register index differs from an index that the relocation passes
    through: a spill or vector entry of the table. -/
theorem relocated_ne_passthrough {body : Lcmd} {T : Array Nat} {x s : Nat}
    (hcls : ∀ (s : Nat) (h : s < T.size),
      slotIsVec (bodyVecSlots body) s = decide (vectorBase ≤ T[s]))
    (hsp : gpSpillBase (bodyVecSlots body) T + numGPRegs ≤ vectorBase)
    (hx : x < numGPRegs ∨
      (gpSpillBase (bodyVecSlots body) T ≤ x ∧ x < gpSpillBase (bodyVecSlots body) T + numGPRegs))
    (hs : s < T.size) (hg : numGPRegs ≤ physMapTabled T s) :
    x ≠ physMapTabled T s := by
  rw [physMapTabled_of_lt hs] at hg ⊢
  rcases hx with hx | ⟨hx1, hx2⟩
  · omega
  · by_cases hv : vectorBase ≤ T[s]
    · omega
    · have hcl : slotIsVec (bodyVecSlots body) s = false := by
        rw [hcls s hs]; simp [hv]
      have := lt_gpSpillBase hs hcl hg
      omega

/-- **The straight-line call relocation separates distinct table entries** of two
    names of the body that the relocation marks used. -/
theorem straightCallComposeTable_ne {body : Lcmd} {T : Array Nat} {a b : String}
    (hsc : bodyStraightCall body = true)
    (hcls : ∀ (s : Nat) (h : s < T.size),
      slotIsVec (bodyVecSlots body) s = decide (vectorBase ≤ T[s]))
    (hsp : gpSpillBase (bodyVecSlots body) T + numGPRegs ≤ vectorBase)
    (ha : a ∈ bodyNames body) (hb : b ∈ bodyNames body)
    (hma : maskName body (nameSlot body a) = true) (hmb : maskName body (nameSlot body b) = true)
    (hsa : nameSlot body a < T.size) (hsb : nameSlot body b < T.size)
    (hT : physMapTabled T (nameSlot body a) ≠ physMapTabled T (nameSlot body b)) :
    physMapTabled (straightCallComposeTable body T) (nameSlot body a)
      ≠ physMapTabled (straightCallComposeTable body T) (nameSlot body b) := by
  unfold straightCallComposeTable
  rw [if_pos hsc]
  simp only
  rw [physMapTabled_map _ _ hsa, physMapTabled_map _ _ hsb]
  obtain ⟨isRead, hrel⟩ := straightCallRelocTable_eq body T
  obtain ⟨σ, hσ, hI⟩ := relocLoop_inv (usedLoop body T isRead).1 (usedLoop body T isRead).2
    (numGPRegs_le_gpSpillBase (bodyVecSlots body) T)
  rw [hrel, hσ]
  have hused : ∀ n, n ∈ bodyNames body → maskName body (nameSlot body n) = true →
      physMapTabled T (nameSlot body n) < numGPRegs →
      (usedLoop body T isRead).1[physMapTabled T (nameSlot body n)]?.getD false = true := by
    intro n hn hm hlt
    obtain ⟨it, hit, hit1⟩ := (live_of_touched (touched_of_mem_bodyNames hn)).2
    have h := usedLoop_used body T isRead hit (hit1 ▸ hm) (hit1 ▸ hlt)
    rwa [hit1] at h
  obtain ⟨_, _, _, _, _, _, h7, h8, h9⟩ := hI
  have hbound : ∀ n, n ∈ bodyNames body → maskName body (nameSlot body n) = true →
      physMapTabled T (nameSlot body n) < numGPRegs →
      σ.1[physMapTabled T (nameSlot body n)]?.getD (physMapTabled T (nameSlot body n))
          < numGPRegs ∨
        (gpSpillBase (bodyVecSlots body) T ≤
            σ.1[physMapTabled T (nameSlot body n)]?.getD (physMapTabled T (nameSlot body n)) ∧
          σ.1[physMapTabled T (nameSlot body n)]?.getD (physMapTabled T (nameSlot body n))
            < gpSpillBase (bodyVecSlots body) T + numGPRegs) := by
    intro n hn hm hlt
    exact relocAssigned_bound (h8 _ hlt (hused n hn hm hlt)) h7
  by_cases hla : physMapTabled T (nameSlot body a) < numGPRegs <;>
    by_cases hlb : physMapTabled T (nameSlot body b) < numGPRegs
  · simp only [hla, hlb, if_true]
    exact h9 _ _ hla hlb (hused a ha hma hla) (hused b hb hmb hlb) hT
  · simp only [hla, hlb, if_true, if_false]
    exact relocated_ne_passthrough hcls hsp (hbound a ha hma hla) hsb (by omega)
  · simp only [hla, hlb, if_true, if_false]
    exact (relocated_ne_passthrough hcls hsp (hbound b hb hmb hlb) hsa (by omega)).symm
  · simp only [hla, hlb, if_false]
    exact hT

/-! ## The allocator's renaming -/

/-- **Location injectivity on overlapping hulls.** Two distinct names of the body,
    neither a hardware register name, a frame-slot name nor `%livepin`, whose live
    ranges over `bodyTraceOut` overlap, have distinct images under the allocator's
    renaming over the table of `physBodyWithStores`.

    `hfit` bounds the GP scan below `vectorBase`. On a straight-line call body the
    relocation of `straightCallComposeTable` hands out fresh spill indices from
    `gpSpillBase`; `hsp` keeps them below `vectorBase`, and `hcls` (the class of
    every slot is the class its table entry's threshold reads) places every GP
    spill entry below `gpSpillBase`. -/
theorem allocName_injOn_overlap {body : Lcmd} {outStoreMap : OutStoreMap}
    {reservedVec : List Nat} {a b : String}
    (hfit : numGPRegs + (physLiveItems (bodyTraceOut body outStoreMap)).length ≤ vectorBase)
    (hcls : bodyStraightCall body = true →
      ∀ (s : Nat) (h : s < (physTableOut body outStoreMap reservedVec).size),
        slotIsVec (bodyVecSlots body) s
          = decide (vectorBase ≤ (physTableOut body outStoreMap reservedVec)[s]))
    (hsp : bodyStraightCall body = true →
      gpSpillBase (bodyVecSlots body) (physTableOut body outStoreMap reservedVec) + numGPRegs
        ≤ vectorBase)
    (ha : a ∈ bodyNames body) (hb : b ∈ bodyNames body) (hne : a ≠ b)
    (hpa : a ≠ "%livepin") (hpb : b ≠ "%livepin")
    (hwa : isHwRegName a = false) (hwb : isHwRegName b = false)
    (hfa : isFrameSlotName a = false) (hfb : isFrameSlotName b = false)
    (hov : physRangesOverlap (physLiveRange (bodyTraceOut body outStoreMap) (nameSlot body a))
      (physLiveRange (bodyTraceOut body outStoreMap) (nameSlot body b))) :
    allocName body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)) a
      ≠ allocName body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)) b := by
  have hT := physTableOut_no_collision (reservedVec := reservedVec) hfit ha hb hne hov
  have hsize : ∀ n, n ∈ bodyNames body →
      nameSlot body n < (physTableOut body outStoreMap reservedVec).size := by
    intro n hn
    unfold physTableOut
    rw [physTableClassed_size]
    exact (live_out_of_mem_bodyNames hn).1
  unfold allocName
  by_cases hc : bodyHasCall body = true
  · rw [if_pos hc, if_pos hc]
    unfold physNameForBody
    simp only [hfa, hfb, hc, hwa, hwb, Bool.false_eq_true, if_false, if_true]
    by_cases hs : bodyStraightCall body = true
    · simp only [hs, if_true]
      intro h
      exact straightCallComposeTable_ne hs (hcls hs) (hsp hs) ha hb
        (maskName_nameSlot ha hpa hwa) (maskName_nameSlot hb hpb hwb)
        (hsize a ha) (hsize b hb) hT (physRegName_inj h)
    · have hid : straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
          = physTableOut body outStoreMap reservedVec := by
        unfold straightCallComposeTable; rw [if_neg hs]
      simp only [hs, Bool.false_eq_true, if_false, hid]
      intro h
      exact hT (calleeFirstPhys_inj (physRegName_inj h))
  · rw [if_neg hc, if_neg hc]
    have hs : bodyStraightCall body = false := by
      unfold bodyStraightCall; simp only [Bool.not_eq_true] at hc; simp [hc]
    have hid : straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
        = physTableOut body outStoreMap reservedVec := by
      unfold straightCallComposeTable; rw [hs]; rfl
    rw [hid]
    intro h
    exact hT (physRegName_inj h)

/-- **Location injectivity at a common trace position.** Two distinct names of the
    body, neither a hardware register name, a frame-slot name nor `%livepin`, both
    live at one position of `bodyTraceOut`, have distinct images under the
    allocator's renaming. -/
theorem allocName_injOn_liveAt {body : Lcmd} {outStoreMap : OutStoreMap}
    {reservedVec : List Nat} {a b : String} {pos : Nat}
    (hfit : numGPRegs + (physLiveItems (bodyTraceOut body outStoreMap)).length ≤ vectorBase)
    (hcls : bodyStraightCall body = true →
      ∀ (s : Nat) (h : s < (physTableOut body outStoreMap reservedVec).size),
        slotIsVec (bodyVecSlots body) s
          = decide (vectorBase ≤ (physTableOut body outStoreMap reservedVec)[s]))
    (hsp : bodyStraightCall body = true →
      gpSpillBase (bodyVecSlots body) (physTableOut body outStoreMap reservedVec) + numGPRegs
        ≤ vectorBase)
    (ha : a ∈ bodyNames body) (hb : b ∈ bodyNames body) (hne : a ≠ b)
    (hpa : a ≠ "%livepin") (hpb : b ≠ "%livepin")
    (hwa : isHwRegName a = false) (hwb : isHwRegName b = false)
    (hfa : isFrameSlotName a = false) (hfb : isFrameSlotName b = false)
    (hla : LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body a))
    (hlb : LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body b)) :
    allocName body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)) a
      ≠ allocName body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)) b :=
  allocName_injOn_overlap hfit hcls hsp ha hb hne hpa hpb hwa hwb hfa hfb
    (overlap_of_liveAt hla hlb)

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCertInj
