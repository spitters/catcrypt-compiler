/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockEmit

@[expose] public section

set_option autoImplicit false

/-!
# Two emitted store blocks appear in binding order

`physBodyWithStores` expands a virtual body position by position
(`physPositionEmit`, one chunk per position) and appends an inline output store
after the expansion of a designated binding.
`JasminInlineStoreBlockEmit.physBodyWithStores_inlineStoreOps` places one such
block inside the emitted list.

`physBodyWithStores_inlineStoreOps_ordered` places two of them in order: for
virtual positions `k < k'`, both designated and both with a non-spill remapped
destination, the emitted list is
`pre ++ block k ++ mid ++ block k' ++ post`, with each block the
`inlineStoreOps` block of that binding's output cell.

## Scope

The positions are ordered by their virtual index `k < k'`, not by their binding
ordinal. On a body whose instructions are all `Lopn` the two agree; on a body
carrying non-`Lopn` positions the binding ordinal of a position is the number of
`Lopn`s before it, which is monotone in the virtual index but not injective, so
the theorem is stated at the level it proves.

The hypotheses select the spill-free arm at both positions, as in
`physBodyWithStores_inlineStoreOps`: a designated binding whose remapped
destination is a spill slot emits a three-instruction routed arm, which is not
an `inlineStoreOps` block.

The two blocks are placed relative to each other and to the ends of the list.
Nothing is claimed about `mid`, so the statement does not give the contiguous
`storeBlocks` list that `JasminInlineStoreValue.storeBlocks_value` runs.

## Main results

* `split_of_two_getElem` — a list splits around two members given by their
  indices.
* `flatMap_split_two` — a `flatMap` splits around segments of the images of two
  members, in the order the members occur.
* `physPositionEmit_inlineStoreOps` — the chunk one designated position
  contributes splits around the `inlineStoreOps` block of its output cell.
* `physBodyWithStores_inlineStoreOps_ordered` — the two-block ordering.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockOrder

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreValue
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockEmit

/-! ## 1. Splitting a list around two members -/

/-- A list splits around two members named by their indices, the smaller index
    first. -/
theorem split_of_two_getElem {β : Type} {L : List β} {k k' : Nat} {x y : β}
    (hlt : k < k') (hx : L[k]? = some x) (hy : L[k']? = some y) :
    ∃ s t u, L = s ++ x :: (t ++ y :: u) := by
  obtain ⟨hk, hkx⟩ := List.getElem?_eq_some_iff.mp hx
  have hdrop : L.drop k = x :: L.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk, hkx]
  have hmem : y ∈ L.drop (k + 1) := by
    refine List.mem_of_getElem? (i := k' - (k + 1)) ?_
    rw [List.getElem?_drop, show k + 1 + (k' - (k + 1)) = k' by omega]
    exact hy
  obtain ⟨t, u, ht⟩ := List.append_of_mem hmem
  exact ⟨L.take k, t, u, by rw [← ht, ← hdrop, List.take_append_drop]⟩

/-- A `flatMap` splits around segments of the images of two members of its
    list, in the order the members occur. -/
theorem flatMap_split_two {α β : Type} {l : List α} {a b : α} {A B : List β}
    (f : α → List β)
    (hl : ∃ s t u, l = s ++ a :: (t ++ b :: u))
    (ha : ∃ p q, f a = p ++ A ++ q)
    (hb : ∃ p q, f b = p ++ B ++ q) :
    ∃ pre mid post, l.flatMap f = pre ++ A ++ mid ++ B ++ post := by
  obtain ⟨s, t, u, rfl⟩ := hl
  obtain ⟨p1, q1, h1⟩ := ha
  obtain ⟨p2, q2, h2⟩ := hb
  refine ⟨s.flatMap f ++ p1, q1 ++ t.flatMap f ++ p2, q2 ++ u.flatMap f, ?_⟩
  simp [List.flatMap_append, List.flatMap_cons, h1, h2, List.append_assoc]

/-! ## 2. The chunk of one designated position -/

/-- **The chunk a designated position contributes is an `inlineStoreOps`
    block.** At a virtual position holding an `Lopn` with a register
    destination, whose binding ordinal falls in the designated output range,
    whose output target is `(base, off)`, and whose remapped destination is not
    a spill slot, the instructions `physPositionEmit` contributes at that
    position split around exactly the `inlineStoreOps` block of the cell
    `memName storeBase off` and that destination. -/
theorem physPositionEmit_inlineStoreOps
    (shiftImm : ShiftImmOracle) (body : Lcmd) (inLoadMap : InLoadMap)
    (loadBase : String) (outStoreMap : OutStoreMap) (storeBase : String)
    (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    {i : Linstr} {virtIdx : Nat}
    {d : LOperand} {ds : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn (d :: ds) opn srcs)
    (hlo : bindingIndexAt body virtIdx ≥ numBindings body - outStoreMap.length)
    (hhi : bindingIndexAt body virtIdx < numBindings body)
    {base : String} {off : Nat}
    (hout : outStoreMap[bindingIndexAt body virtIdx
              - (numBindings body - outStoreMap.length)]? = some (base, off))
    (hnospill : (physRmap body outStoreMap reservedVec d).isSpill = false) :
    ∃ pre post,
      physPositionEmit shiftImm body inLoadMap loadBase outStoreMap storeBase
          abiW memrefBaseReload callArgBaseReload reservedVec (i, virtIdx)
        = pre ++ atTagZero (inlineStoreOps (physAbiMovBuf body abiW) storeBase off
            (physRmap body outStoreMap reservedVec d)) ++ post := by
  simp only [bindingIndexAt] at hlo hhi hout
  simp only [physRmap, physAllocTbl] at hnospill
  unfold physPositionEmit
  simp only []
  simp only [hi]
  refine split_trans (split_last _ _ _ _) ?_
  split
  · split
    · rename_i _b o hsome
      have ho : o = off := congrArg Prod.snd (Option.some.inj (hsome.symm.trans hout))
      subst ho
      rw [hnospill]
      simp only [Bool.false_eq_true, if_false]
      exact split_refl _
    · rename_i hnone
      exact absurd (hnone.symm.trans hout) (by simp)
  · rename_i hcond
    exact absurd (And.intro hlo hhi) hcond

/-! ## 3. The two-block ordering -/

/-- **Two emitted store blocks appear in binding order.** At two virtual
    positions `k < k'` of the body, each holding an `Lopn` with a register
    destination, each with a binding ordinal in the designated output range and
    a non-spill remapped destination, the list `physBodyWithStores` emits
    contains the `inlineStoreOps` block of the position `k` output cell before
    the block of the position `k'` output cell. -/
theorem physBodyWithStores_inlineStoreOps_ordered
    (shiftImm : ShiftImmOracle) (body : Lcmd) (inLoadMap : InLoadMap)
    (loadBase : String) (outStoreMap : OutStoreMap) (storeBase : String)
    (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    {k k' : Nat} (hlt : k < k')
    {i₁ i₂ : Linstr} (hk : body[k]? = some i₁) (hk' : body[k']? = some i₂)
    {d₁ d₂ : LOperand} {ds₁ ds₂ : List LOperand} {opn₁ opn₂ : String}
    {srcs₁ srcs₂ : List LOperand}
    (hi₁ : i₁.li_i = .Lopn (d₁ :: ds₁) opn₁ srcs₁)
    (hi₂ : i₂.li_i = .Lopn (d₂ :: ds₂) opn₂ srcs₂)
    (hlo₁ : bindingIndexAt body k ≥ numBindings body - outStoreMap.length)
    (hhi₁ : bindingIndexAt body k < numBindings body)
    (hlo₂ : bindingIndexAt body k' ≥ numBindings body - outStoreMap.length)
    (hhi₂ : bindingIndexAt body k' < numBindings body)
    {base₁ base₂ : String} {off₁ off₂ : Nat}
    (hout₁ : outStoreMap[bindingIndexAt body k
              - (numBindings body - outStoreMap.length)]? = some (base₁, off₁))
    (hout₂ : outStoreMap[bindingIndexAt body k'
              - (numBindings body - outStoreMap.length)]? = some (base₂, off₂))
    (hns₁ : (physRmap body outStoreMap reservedVec d₁).isSpill = false)
    (hns₂ : (physRmap body outStoreMap reservedVec d₂).isSpill = false) :
    ∃ pre mid post,
      physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase
          abiW memrefBaseReload callArgBaseReload reservedVec
        = pre ++ atTagZero (inlineStoreOps (physAbiMovBuf body abiW) storeBase off₁
            (physRmap body outStoreMap reservedVec d₁))
          ++ mid ++ atTagZero (inlineStoreOps (physAbiMovBuf body abiW) storeBase off₂
            (physRmap body outStoreMap reservedVec d₂)) ++ post := by
  rw [physBodyWithStores_eq_flatMap]
  refine flatMap_split_two (a := (i₁, k)) (b := (i₂, k')) _ ?_ ?_ ?_
  · refine split_of_two_getElem hlt ?_ ?_
    · simp [List.getElem?_zipIdx, hk]
    · simp [List.getElem?_zipIdx, hk']
  · exact physPositionEmit_inlineStoreOps _ _ _ _ _ _ _ _ _ _ hi₁ hlo₁ hhi₁ hout₁ hns₁
  · exact physPositionEmit_inlineStoreOps _ _ _ _ _ _ _ _ _ _ hi₂ hlo₂ hhi₂ hout₂ hns₂

end CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockOrder
