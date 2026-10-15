/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreValue

@[expose] public section

set_option autoImplicit false

/-!
# The emitted store block is an `inlineStoreOps` block

`physBodyWithStores` expands a virtual body position by position, and after the
expansion of a designated output binding whose remapped destination is not a
spill slot it appends a reload of the out-pointer into `reloadScratch2` and a
move of that destination into the output cell.
`JasminInlineStoreValue.inlineStoreOps` is that pair at `LinstrR`.

`physBodyWithStores_inlineStoreOps` identifies the two: the emitted instruction
list splits around exactly that block, carried at the instruction-index tag `0`
the emitter uses.

## Scope

The theorem places one block inside the emitted list. It does not fix where the
block sits relative to the other positions' expansions beyond the existence of a
prefix and a suffix, and it speaks about one designated binding at a time, so it
does not give the contiguous `storeBlocks` list that
`JasminInlineStoreValue.storeBlocks_value` runs.

`physRmap`, `physAbiMovBuf` and `bindingIndexAt` restate the emitter's internal
`let` bindings `rmap`, `abiMovBuf` and `bidx`. The proof unfolds the emitter and
discharges its branch conditions from hypotheses phrased with these names, so a
restatement that does not agree with the emitter is a proof failure.

The hypotheses select the spill-free arm. A designated binding whose remapped
destination is a spill slot emits a three-instruction routed arm, which is not
an `inlineStoreOps` block.

## Main definitions

* `physRmap` — the operand remap `physBodyWithStores` applies to the body.
* `physBodyIsU64`, `physAbiMovReg`, `physAbiMovBuf` — the ABI move mnemonics.
* `bindingIndexAt` — the binding ordinal of a virtual position.
* `atTagZero` — the `Linstr` wrapper the store block's instructions carry.

## Main results

* `flatMap_split_of_mem`, `split_trans`, `split_last`, `split_refl` — splitting
  a list around a segment.
* `physBodyWithStores_inlineStoreOps` — for a designated binding with a
  non-spill remapped destination, the emitted list splits around exactly the
  `inlineStoreOps` block of its output cell and that destination.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreValue

/-! ## 1. Splitting a list around a segment -/

/-- A `flatMap` splits around the image of any member of its list. -/
theorem flatMap_split_of_mem {α β : Type} (l : List α) (f : α → List β) {a : α}
    (h : a ∈ l) : ∃ pre post, l.flatMap f = pre ++ f a ++ post := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨s.flatMap f, t.flatMap f, by
    simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]⟩

/-- A split inside a split is a split. -/
theorem split_trans {β : Type} {L A B : List β}
    (h1 : ∃ pre post, L = pre ++ A ++ post)
    (h2 : ∃ pre post, A = pre ++ B ++ post) :
    ∃ pre post, L = pre ++ B ++ post := by
  obtain ⟨p1, q1, rfl⟩ := h1
  obtain ⟨p2, q2, rfl⟩ := h2
  exact ⟨p1 ++ p2, q2 ++ q1, by simp [List.append_assoc]⟩

/-- A four-fold concatenation splits around its last segment. -/
theorem split_last {β : Type} (A Bs C D : List β) :
    ∃ pre post, A ++ Bs ++ C ++ D = pre ++ D ++ post :=
  ⟨A ++ Bs ++ C, [], by simp⟩

/-- A list splits around itself. -/
theorem split_refl {β : Type} (B : List β) : ∃ pre post, B = pre ++ B ++ post :=
  ⟨[], [], by simp⟩

/-! ## 2. The emitter's internal bindings -/

/-- The operand remap `physBodyWithStores` applies to the body: the
    callee-saved-first remap for a body carrying a real `Lcall`, the plain remap
    otherwise, both over the output-liveness-extended allocation table. -/
def physRmap (body : Lcmd) (outStoreMap : OutStoreMap) (reservedVec : List Nat) :
    LOperand → LOperand :=
  if bodyHasCall body then
    remapOperandCalleeSave body (physAllocTbl body outStoreMap reservedVec)
  else
    remapOperand body (physAllocTbl body outStoreMap reservedVec)

/-- The body carries a `:64`-tagged `Lopn`. -/
def physBodyIsU64 (body : Lcmd) : Bool :=
  body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)

/-- The spill-routing-leg ABI move mnemonic. -/
def physAbiMovReg (body : Lcmd) (abiW : Nat) : String :=
  if abiW == 256 then "VMOVDQU" else if physBodyIsU64 body then "MOV:64" else "MOV"

/-- The buffer-leg ABI move mnemonic: the narrow moves at `abiW ∈ {8, 16}`, the
    spill-routing-leg mnemonic otherwise. -/
def physAbiMovBuf (body : Lcmd) (abiW : Nat) : String :=
  if abiW == 16 then "MOV:16"
  else if abiW == 8 then "MOV:8"
  else physAbiMovReg body abiW

/-- The binding ordinal of a virtual position: the number of `Lopn`s strictly
    before it in the body. -/
def bindingIndexAt (body : Lcmd) (virtIdx : Nat) : Nat :=
  ((body.take virtIdx).filter (fun li =>
    match li.li_i with
    | .Lopn _ _ _ => true
    | _ => false)).length

/-- The instruction-index tag the inline store block's instructions carry. -/
def atTagZero (l : List LinstrR) : Lcmd := l.map (fun r => ⟨0, r⟩)

/-! ## 3. The emitted block -/

/-- **The emitted store block is an `inlineStoreOps` block.** At a virtual
    position holding an `Lopn` with a register destination, whose binding ordinal
    falls in the designated output range, whose output target is `(base, off)`,
    and whose remapped destination is not a spill slot, the list
    `physBodyWithStores` emits splits around exactly the `inlineStoreOps` block
    of the cell `memName storeBase off` and that destination. -/
theorem physBodyWithStores_inlineStoreOps
    (shiftImm : ShiftImmOracle) (body : Lcmd) (inLoadMap : InLoadMap)
    (loadBase : String) (outStoreMap : OutStoreMap) (storeBase : String)
    (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    {i : Linstr} {virtIdx : Nat} (hmem : (i, virtIdx) ∈ body.zipIdx)
    {d : LOperand} {ds : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn (d :: ds) opn srcs)
    (hlo : bindingIndexAt body virtIdx ≥ numBindings body - outStoreMap.length)
    (hhi : bindingIndexAt body virtIdx < numBindings body)
    {base : String} {off : Nat}
    (hout : outStoreMap[bindingIndexAt body virtIdx
              - (numBindings body - outStoreMap.length)]? = some (base, off))
    (hnospill : (physRmap body outStoreMap reservedVec d).isSpill = false) :
    ∃ pre post,
      physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase
          abiW memrefBaseReload callArgBaseReload reservedVec
        = pre ++ atTagZero (inlineStoreOps (physAbiMovBuf body abiW) storeBase off
            (physRmap body outStoreMap reservedVec d)) ++ post := by
  simp only [bindingIndexAt] at hlo hhi hout
  simp only [physRmap] at hnospill
  unfold physBodyWithStores
  simp only []
  refine split_trans (flatMap_split_of_mem _ _ hmem) ?_
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

end CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockEmit
