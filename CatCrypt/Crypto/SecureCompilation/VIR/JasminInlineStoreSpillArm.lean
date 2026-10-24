/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockOrder

@[expose] public section

set_option autoImplicit false

/-!
# The spill-routed store arm and mixed output target lists

`physBodyWithStores` emits one of two blocks after the expansion of a designated
output binding. When the binding's remapped destination is not a spill slot it
emits the two-instruction block `JasminInlineStoreValue.inlineStoreOps`. When the
destination is a spill slot it emits a three-instruction block that routes the
value through `reloadScratch`: a move of the spill slot into `reloadScratch`, the
reload of the out-pointer into `reloadScratch2`, and a move of `reloadScratch`
into the output cell. `spillStoreOps` is that triple at `LinstrR`.

`mixedStoreBlocks` is the concatenation of the blocks of a list of output
targets, each target naming its cell offset, its source register and which of the
two arms the emitter takes for it. `mixedStoreBlocks_value` reads the cells of
such a run.

The buffer-leg mnemonic is carried under `MovesMasked`: the cell receives the
source word conjoined with a mask. `MovesWord` is the `BitVec.allOnes` case, and
the narrow buffer moves `MOV:8` and `MOV:16` are the `0xFF` and `0xFFFF` cases,
so the results cover every `abiW` whose buffer mnemonic `applyOpn` models.

## Scope

The theorems about `mixedStoreBlocks` are about the block list run as a unit. On
the emit path the blocks are interleaved with the body expansions rather than
contiguous, so they are not statements about the instruction order
`physBodyWithStores` emits; `physBodyWithStores_spillStoreOps` places one spill
block inside the emitted list, as
`JasminInlineStoreBlockEmit.physBodyWithStores_inlineStoreOps` does for the
non-spill block.

The spill-routing-leg mnemonic is carried under `MovesWord` rather than
`MovesMasked`. The emitter's `abiMovReg` is `MOV`, `MOV:64` or `VMOVDQU`, never a
narrow move, so no generality is lost; `VMOVDQU` is outside the `applyOpn`
fragment and satisfies neither predicate, which leaves `abiW = 256` uncovered.

`mixedStoreBlocks_value` requires the source registers to differ from both
scratch registers and from every cell of the list, and the offsets to be pairwise
distinct. A spill source satisfies the two scratch conditions by its `k.` prefix,
but the statement takes them as hypotheses for both arms uniformly.

## Main definitions

* `MovesMasked` — the opcode copies its single source word conjoined with a mask.
* `spillStoreOps` — the spill-routed store block, at `LinstrR`.
* `OutTarget` — a cell offset, a source register, and the arm taken for it.
* `storeBlockFor`, `mixedStoreBlocks` — the block of one target and of a list.

## Main results

* `MovesMasked_allOnes_iff_MovesWord`, `MovesMasked_MOV8`, `MovesMasked_MOV16` —
  the mask predicate against the word predicate and the narrow moves.
* `lsemStep_movMasked` — the step of a masked single-destination `Lopn`.
* `spillStoreOps_run`, `spillStoreOps_value`, `spillStoreOps_frame` — the spill
  block's state, the value it leaves in its cell, and what it leaves alone.
* `inlineStoreOps_run_masked`, `inlineStoreOps_value_masked`,
  `inlineStoreOps_frame_masked` — the same three for the non-spill block under a
  masked buffer mnemonic.
* `mixedStoreBlocks_dsts`, `mixedStoreBlocks_lvm_frame` — a mixed block list
  writes only the two scratch registers and its own cells.
* `mixedStoreBlocks_value` — target `j`'s cell holds the masked entry value of
  target `j`'s source register, whichever arm each target takes.
* `mixedStoreBlocks_value_word` — the `MovesWord` buffer-mnemonic case.
* `physPositionEmit_spillStoreOps`, `physBodyWithStores_spillStoreOps` — for a
  designated binding with a spill remapped destination, the emitted list splits
  around exactly the `spillStoreOps` block of its output cell.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreSpillArm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminBindingPrefixDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreValue
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockOrder

/-! ## 1. Distinctness of the two scratch registers -/

/-- The routing scratch `R15` and the out-pointer scratch `R14` are distinct. -/
theorem reloadScratch_ne_reloadScratch2 : reloadScratch ≠ reloadScratch2 := by
  unfold reloadScratch reloadScratch2; decide +kernel

/-- The out-pointer red-zone save slot is not the routing scratch. -/
theorem abiSaveRdiName_ne_reloadScratch : abiSaveRdiName ≠ reloadScratch := by
  unfold abiSaveRdiName reloadScratch; decide +kernel

/-! ## 2. The masked move predicate -/

/-- The opcode copies its single source word conjoined with `mask`: the modeled
    semantics of the buffer-leg ABI moves. `MovesWord` is the `BitVec.allOnes`
    case and the narrow moves `MOV:8` and `MOV:16` are the `0xFF` and `0xFFFF`
    cases. -/
def MovesMasked (w : Nat) (mask : BitVec w) (opn : String) : Prop :=
  ∀ v : BitVec w, applyOpn (w := w) (stripWidthTag opn) [v] = some (v &&& mask)

/-- The all-ones mask is the word-moving case. -/
theorem MovesMasked_allOnes_iff_MovesWord (w : Nat) (opn : String) :
    MovesMasked w (BitVec.allOnes w) opn ↔ MovesWord w opn := by
  constructor
  · intro h v; rw [h v, BitVec.and_allOnes]
  · intro h v; rw [h v, BitVec.and_allOnes]

/-- `stripWidthTag` leaves the narrow `MOV:8` mnemonic alone. -/
@[simp] theorem stripWidthTag_MOV8 : stripWidthTag "MOV:8" = "MOV:8" := by decide +kernel

/-- `stripWidthTag` leaves the narrow `MOV:16` mnemonic alone. -/
@[simp] theorem stripWidthTag_MOV16 : stripWidthTag "MOV:16" = "MOV:16" := by decide +kernel

/-- `MOV:8` keeps the low byte of its source. -/
theorem MovesMasked_MOV8 (w : Nat) : MovesMasked w (BitVec.ofNat w 0xFF) "MOV:8" := by
  intro v; simp [applyOpn]

/-- `MOV:16` keeps the low two bytes of its source. -/
theorem MovesMasked_MOV16 (w : Nat) : MovesMasked w (BitVec.ofNat w 0xFFFF) "MOV:16" := by
  intro v; simp [applyOpn]

/-- The step of a masked single-destination register-to-register move: the
    destination takes the source's value conjoined with the mask and the pc
    advances. -/
theorem lsemStep_movMasked {w : Nat} (dstName srcName movOpn : String)
    (mask : BitVec w) (s : Lstate w) (hmov : MovesMasked w mask movOpn) :
    lsemStep (.Lopn [.reg dstName] movOpn [.reg srcName]) s
      = some ((s.setReg dstName (s.lvm srcName &&& mask)).nextPc) := by
  have hm : applyOpn (w := w) (stripWidthTag movOpn) [s.lvm srcName]
      = some (s.lvm srcName &&& mask) := hmov _
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, hm]

/-! ## 3. The non-spill block under a masked buffer mnemonic -/

/-- **The non-spill block's run under a masked mnemonic.** -/
theorem inlineStoreOps_run_masked {w : Nat} (movOpn storeBase : String) (off : Nat)
    (srcName : String) (mask : BitVec w) (hmov : MovesMasked w mask movOpn)
    (hsrc : srcName ≠ reloadScratch2) (s : Lstate w) :
    lsemStraight (inlineStoreOps movOpn storeBase off (.reg srcName)) s
      = some ((((s.setReg reloadScratch2 (s.lvm abiSaveRdiName)).nextPc).setReg
          (memName storeBase off) (s.lvm srcName &&& mask)).nextPc) := by
  have hne : ((s.setReg reloadScratch2 (s.lvm abiSaveRdiName)).nextPc).lvm srcName
      = s.lvm srcName := by simp [Lstate.setReg, hsrc]
  rw [inlineStoreOps, lsemStraight_cons,
    lsemStep_mov reloadScratch2 abiSaveRdiName "MOVQ" s (MovesWord_MOVQ w)]
  simp only [lsemStraight_cons,
    lsemStep_movMasked (memName storeBase off) srcName movOpn mask _ hmov, hne,
    lsemStraight_nil]

/-- **The non-spill block leaves the masked source value in its cell.** -/
theorem inlineStoreOps_value_masked {w : Nat} (movOpn storeBase : String) (off : Nat)
    (srcName : String) (mask : BitVec w) (hmov : MovesMasked w mask movOpn)
    (hsrc : srcName ≠ reloadScratch2) (s s' : Lstate w)
    (h : lsemStraight (inlineStoreOps movOpn storeBase off (.reg srcName)) s = some s') :
    s'.lvm (memName storeBase off) = s.lvm srcName &&& mask := by
  rw [inlineStoreOps_run_masked movOpn storeBase off srcName mask hmov hsrc s] at h
  cases h
  simp [Lstate.setReg]

/-- **What the non-spill block leaves alone.** -/
theorem inlineStoreOps_frame_masked {w : Nat} (movOpn storeBase : String) (off : Nat)
    (srcName : String) (mask : BitVec w) (hmov : MovesMasked w mask movOpn)
    (hsrc : srcName ≠ reloadScratch2) (s s' : Lstate w)
    (h : lsemStraight (inlineStoreOps movOpn storeBase off (.reg srcName)) s = some s')
    (r : String) (hr1 : r ≠ reloadScratch2) (hr2 : r ≠ memName storeBase off) :
    s'.lvm r = s.lvm r := by
  rw [inlineStoreOps_run_masked movOpn storeBase off srcName mask hmov hsrc s] at h
  cases h
  simp [Lstate.setReg, hr1, hr2]

/-! ## 4. The spill-routed block -/

/-- The instruction triple `physBodyWithStores` emits after the expansion of a
    designated binding whose destination is a spill slot: move the spill slot
    into `reloadScratch`, recover the out-pointer from its red-zone save slot
    into `reloadScratch2`, then move `reloadScratch` into the cell
    `memName storeBase off`. -/
def spillStoreOps (movReg movBuf storeBase : String) (off : Nat) (src : LOperand) :
    List LinstrR :=
  [ .Lopn [.reg reloadScratch] movReg [src],
    .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName],
    .Lopn [.reg (memName storeBase off)] movBuf [.reg reloadScratch] ]

/-- **The spill block's run.** The routing scratch takes the source's entry
    value, the out-pointer scratch is reloaded, and the cell receives the masked
    source value. No side condition on the source is needed: its value is read by
    the first instruction of the block. -/
theorem spillStoreOps_run {w : Nat} (movReg movBuf storeBase : String) (off : Nat)
    (srcName : String) (mask : BitVec w) (hreg : MovesWord w movReg)
    (hbuf : MovesMasked w mask movBuf) (s : Lstate w) :
    lsemStraight (spillStoreOps movReg movBuf storeBase off (.reg srcName)) s
      = some ((((((s.setReg reloadScratch (s.lvm srcName)).nextPc).setReg
          reloadScratch2 (s.lvm abiSaveRdiName)).nextPc).setReg
          (memName storeBase off) (s.lvm srcName &&& mask)).nextPc) := by
  have h1 : ((s.setReg reloadScratch (s.lvm srcName)).nextPc).lvm abiSaveRdiName
      = s.lvm abiSaveRdiName := by
    simp [Lstate.setReg, abiSaveRdiName_ne_reloadScratch]
  have h2 : ((((s.setReg reloadScratch (s.lvm srcName)).nextPc).setReg
        reloadScratch2 (s.lvm abiSaveRdiName)).nextPc).lvm reloadScratch
      = s.lvm srcName := by
    simp [Lstate.setReg, reloadScratch_ne_reloadScratch2]
  rw [spillStoreOps, lsemStraight_cons,
    lsemStep_mov reloadScratch srcName movReg s hreg]
  simp only [lsemStraight_cons,
    lsemStep_mov reloadScratch2 abiSaveRdiName "MOVQ" _ (MovesWord_MOVQ w), h1,
    lsemStep_movMasked (memName storeBase off) reloadScratch movBuf mask _ hbuf, h2,
    lsemStraight_nil]

/-- **The spill block leaves the masked source value in its cell.** -/
theorem spillStoreOps_value {w : Nat} (movReg movBuf storeBase : String) (off : Nat)
    (srcName : String) (mask : BitVec w) (hreg : MovesWord w movReg)
    (hbuf : MovesMasked w mask movBuf) (s s' : Lstate w)
    (h : lsemStraight (spillStoreOps movReg movBuf storeBase off (.reg srcName)) s
      = some s') :
    s'.lvm (memName storeBase off) = s.lvm srcName &&& mask := by
  rw [spillStoreOps_run movReg movBuf storeBase off srcName mask hreg hbuf s] at h
  cases h
  simp [Lstate.setReg]

/-- **What the spill block leaves alone.** Every register other than the two
    scratch registers and the block's own cell reads as it did on entry. -/
theorem spillStoreOps_frame {w : Nat} (movReg movBuf storeBase : String) (off : Nat)
    (srcName : String) (mask : BitVec w) (hreg : MovesWord w movReg)
    (hbuf : MovesMasked w mask movBuf) (s s' : Lstate w)
    (h : lsemStraight (spillStoreOps movReg movBuf storeBase off (.reg srcName)) s
      = some s')
    (r : String) (hr0 : r ≠ reloadScratch) (hr1 : r ≠ reloadScratch2)
    (hr2 : r ≠ memName storeBase off) :
    s'.lvm r = s.lvm r := by
  rw [spillStoreOps_run movReg movBuf storeBase off srcName mask hreg hbuf s] at h
  cases h
  simp [Lstate.setReg, hr0, hr1, hr2]

/-! ## 5. Mixed target lists -/

/-- One output target: the cell offset, the source register name, and whether the
    emitter routes the source through `reloadScratch`. -/
structure OutTarget where
  /-- The offset of the target's cell in the out buffer. -/
  off : Nat
  /-- The name of the register holding the value to store. -/
  src : String
  /-- Whether the emitter takes the spill-routed arm for this target. -/
  spilled : Bool

/-- The block the emitter contributes for one target. -/
def storeBlockFor (movReg movBuf storeBase : String) (t : OutTarget) : List LinstrR :=
  if t.spilled then spillStoreOps movReg movBuf storeBase t.off (.reg t.src)
  else inlineStoreOps movBuf storeBase t.off (.reg t.src)

/-- The store blocks of a list of output targets, in target order, each target
    taking the arm its `spilled` flag names. -/
def mixedStoreBlocks (movReg movBuf storeBase : String) (targets : List OutTarget) :
    List LinstrR :=
  targets.flatMap (storeBlockFor movReg movBuf storeBase)

/-- Every instruction of one target's block is a single-destination `Lopn`
    writing a scratch register or that target's cell. -/
theorem storeBlockFor_dsts (movReg movBuf storeBase : String) (t : OutTarget) :
    ∀ i ∈ storeBlockFor movReg movBuf storeBase t,
      ∃ dst opn srcs, i = .Lopn [.reg dst] opn srcs ∧
        (dst = reloadScratch ∨ dst = reloadScratch2 ∨ dst = memName storeBase t.off) := by
  intro i hi
  rw [storeBlockFor] at hi
  split at hi
  · rw [spillStoreOps] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h <;> subst h
    · exact ⟨_, _, _, rfl, Or.inl rfl⟩
    · exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, _, _, rfl, Or.inr (Or.inr rfl)⟩
  · rw [inlineStoreOps] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h <;> subst h
    · exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, _, _, rfl, Or.inr (Or.inr rfl)⟩

/-- Every instruction of a mixed block list is a single-destination `Lopn`
    writing a scratch register or one of the list's own cells. -/
theorem mixedStoreBlocks_dsts (movReg movBuf storeBase : String)
    (targets : List OutTarget) :
    ∀ i ∈ mixedStoreBlocks movReg movBuf storeBase targets,
      ∃ dst opn srcs, i = .Lopn [.reg dst] opn srcs ∧
        (dst = reloadScratch ∨ dst = reloadScratch2 ∨
          ∃ t ∈ targets, dst = memName storeBase t.off) := by
  intro i hi
  rw [mixedStoreBlocks, List.mem_flatMap] at hi
  obtain ⟨t, ht, hi⟩ := hi
  obtain ⟨dst, opn, srcs, rfl, hdst⟩ := storeBlockFor_dsts movReg movBuf storeBase t i hi
  refine ⟨dst, opn, srcs, rfl, ?_⟩
  rcases hdst with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨t, ht, h⟩)

/-- **What a mixed block list leaves alone.** A register that is neither scratch
    register nor one of the list's cells reads as it did on entry. -/
theorem mixedStoreBlocks_lvm_frame {w : Nat} (movReg movBuf storeBase : String)
    (targets : List OutTarget) (s s' : Lstate w)
    (h : lsemStraight (mixedStoreBlocks movReg movBuf storeBase targets) s = some s')
    (r : String) (hr0 : r ≠ reloadScratch) (hr1 : r ≠ reloadScratch2)
    (hr2 : ∀ t ∈ targets, r ≠ memName storeBase t.off) :
    s'.lvm r = s.lvm r := by
  refine lsemStraight_lvm_of_dsts
    (fun n => n = reloadScratch ∨ n = reloadScratch2 ∨
      ∃ t ∈ targets, n = memName storeBase t.off)
    _ s s' (mixedStoreBlocks_dsts movReg movBuf storeBase targets) h r ?_
  rintro (rfl | rfl | ⟨t, ht, rfl⟩)
  · exact hr0 rfl
  · exact hr1 rfl
  · exact hr2 t ht rfl

/-- **One target's block leaves the masked source value in its cell**, whichever
    arm the target takes. -/
theorem storeBlockFor_value {w : Nat} (movReg movBuf storeBase : String)
    (mask : BitVec w) (hreg : MovesWord w movReg) (hbuf : MovesMasked w mask movBuf)
    (t : OutTarget) (hsrc : t.src ≠ reloadScratch2) (s s' : Lstate w)
    (h : lsemStraight (storeBlockFor movReg movBuf storeBase t) s = some s') :
    s'.lvm (memName storeBase t.off) = s.lvm t.src &&& mask := by
  rw [storeBlockFor] at h
  split at h
  · exact spillStoreOps_value movReg movBuf storeBase t.off t.src mask hreg hbuf s s' h
  · exact inlineStoreOps_value_masked movBuf storeBase t.off t.src mask hbuf hsrc s s' h

/-- **What one target's block leaves alone**, whichever arm the target takes. -/
theorem storeBlockFor_frame {w : Nat} (movReg movBuf storeBase : String)
    (mask : BitVec w) (hreg : MovesWord w movReg) (hbuf : MovesMasked w mask movBuf)
    (t : OutTarget) (hsrc : t.src ≠ reloadScratch2) (s s' : Lstate w)
    (h : lsemStraight (storeBlockFor movReg movBuf storeBase t) s = some s')
    (r : String) (hr0 : r ≠ reloadScratch) (hr1 : r ≠ reloadScratch2)
    (hr2 : r ≠ memName storeBase t.off) :
    s'.lvm r = s.lvm r := by
  rw [storeBlockFor] at h
  split at h
  · exact spillStoreOps_frame movReg movBuf storeBase t.off t.src mask hreg hbuf
      s s' h r hr0 hr1 hr2
  · exact inlineStoreOps_frame_masked movBuf storeBase t.off t.src mask hbuf hsrc
      s s' h r hr1 hr2

/-- **Each target's cell holds its source's masked entry value.** For a list of
    output targets at a fixed base whose offsets are pairwise distinct and whose
    source registers are neither scratch register nor a cell of the list, running
    the blocks reaches a state in which target `j`'s cell holds the value target
    `j`'s source register held on entry, conjoined with the buffer mnemonic's
    mask. The targets may mix the two arms freely.

    The side conditions are the ones the emit path discharges outside Lean: a
    designated source is either a physical GP register, hence neither `R14` nor
    `R15` nor a cell name, or a `k.`-prefixed spill slot, which is none of the
    three by its prefix; and `scripts/outstoremap-distinct-gate.sh` enforces the
    pairwise distinctness of the offsets. -/
theorem mixedStoreBlocks_value {w : Nat} (movReg movBuf storeBase : String)
    (mask : BitVec w) (hreg : MovesWord w movReg) (hbuf : MovesMasked w mask movBuf) :
    ∀ (targets : List OutTarget) (s s' : Lstate w),
      lsemStraight (mixedStoreBlocks movReg movBuf storeBase targets) s = some s' →
      (∀ t ∈ targets, t.src ≠ reloadScratch) →
      (∀ t ∈ targets, t.src ≠ reloadScratch2) →
      (∀ t ∈ targets, ∀ u ∈ targets, t.src ≠ memName storeBase u.off) →
      targets.Pairwise (fun t u => t.off ≠ u.off) →
      ∀ t ∈ targets, s'.lvm (memName storeBase t.off) = s.lvm t.src &&& mask := by
  intro targets
  induction targets with
  | nil => intro s s' _ _ _ _ _ t ht; simp at ht
  | cons a rest ih =>
      intro s s' hrun hsrcR15 hsrcR14 hsrcCell hdistinct t ht
      rw [mixedStoreBlocks, List.flatMap_cons, lsemStraight_append] at hrun
      rcases hstep : lsemStraight (storeBlockFor movReg movBuf storeBase a) s with _ | s1
      · rw [hstep] at hrun; simp at hrun
      · rw [hstep] at hrun
        simp only [Option.bind_some] at hrun
        have hrest : lsemStraight (mixedStoreBlocks movReg movBuf storeBase rest) s1
            = some s' := by rw [mixedStoreBlocks]; exact hrun
        have hdist' : rest.Pairwise (fun t u => t.off ≠ u.off) :=
          (List.pairwise_cons.mp hdistinct).2
        have hhead : ∀ u ∈ rest, a.off ≠ u.off := (List.pairwise_cons.mp hdistinct).1
        rcases List.mem_cons.mp ht with rfl | ht'
        · have hcell : s'.lvm (memName storeBase t.off)
              = s1.lvm (memName storeBase t.off) := by
            refine mixedStoreBlocks_lvm_frame movReg movBuf storeBase rest s1 s' hrest _
              (memName_ne_reloadScratch storeBase t.off)
              (memName_ne_reloadScratch2 storeBase t.off) ?_
            intro u hu
            exact memName_ne_of_off_ne storeBase (hhead u hu)
          rw [hcell]
          exact storeBlockFor_value movReg movBuf storeBase mask hreg hbuf t
            (hsrcR14 t (by simp)) s s1 hstep
        · have hframe : s1.lvm t.src = s.lvm t.src :=
            storeBlockFor_frame movReg movBuf storeBase mask hreg hbuf a
              (hsrcR14 a (by simp)) s s1 hstep t.src
              (hsrcR15 t (by simp [ht']))
              (hsrcR14 t (by simp [ht']))
              (hsrcCell t (by simp [ht']) a (by simp))
          rw [← hframe]
          exact ih s1 s' hrest (fun u hu => hsrcR15 u (by simp [hu]))
            (fun u hu => hsrcR14 u (by simp [hu]))
            (fun u hu u' hu' => hsrcCell u (by simp [hu]) u' (by simp [hu']))
            hdist' t ht'

/-- **Each target's cell holds its source's entry value** when the buffer
    mnemonic moves a whole word. The `abiW ∈ {0, 64}` case of
    `mixedStoreBlocks_value`. -/
theorem mixedStoreBlocks_value_word {w : Nat} (movReg movBuf storeBase : String)
    (hreg : MovesWord w movReg) (hbuf : MovesWord w movBuf)
    (targets : List OutTarget) (s s' : Lstate w)
    (hrun : lsemStraight (mixedStoreBlocks movReg movBuf storeBase targets) s = some s')
    (hsrcR15 : ∀ t ∈ targets, t.src ≠ reloadScratch)
    (hsrcR14 : ∀ t ∈ targets, t.src ≠ reloadScratch2)
    (hsrcCell : ∀ t ∈ targets, ∀ u ∈ targets, t.src ≠ memName storeBase u.off)
    (hdistinct : targets.Pairwise (fun t u => t.off ≠ u.off)) :
    ∀ t ∈ targets, s'.lvm (memName storeBase t.off) = s.lvm t.src := by
  intro t ht
  have h := mixedStoreBlocks_value movReg movBuf storeBase (BitVec.allOnes w) hreg
    ((MovesMasked_allOnes_iff_MovesWord w movBuf).mpr hbuf) targets s s' hrun
    hsrcR15 hsrcR14 hsrcCell hdistinct t ht
  rw [h, BitVec.and_allOnes]

/-! ## 6. The emitted spill block -/

/-- **The chunk a designated spilled position contributes is a `spillStoreOps`
    block.** At a virtual position holding an `Lopn` with a register destination,
    whose binding ordinal falls in the designated output range, whose output
    target is `(base, off)`, and whose remapped destination is a spill slot, the
    instructions `physPositionEmit` contributes at that position split around
    exactly the `spillStoreOps` block of the cell `memName storeBase off` and
    that destination. -/
theorem physPositionEmit_spillStoreOps
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
    (hspill : (physRmap body outStoreMap reservedVec d).isSpill = true) :
    ∃ pre post,
      physPositionEmit shiftImm body inLoadMap loadBase outStoreMap storeBase
          abiW memrefBaseReload callArgBaseReload reservedVec (i, virtIdx)
        = pre ++ atTagZero (spillStoreOps (physAbiMovReg body abiW)
            (physAbiMovBuf body abiW) storeBase off
            (physRmap body outStoreMap reservedVec d)) ++ post := by
  simp only [bindingIndexAt] at hlo hhi hout
  simp only [physRmap, physAllocTbl] at hspill
  unfold physPositionEmit
  simp only []
  simp only [hi]
  refine split_trans (split_last _ _ _ _) ?_
  split
  · split
    · rename_i _b o hsome
      have ho : o = off := congrArg Prod.snd (Option.some.inj (hsome.symm.trans hout))
      subst ho
      exact split_refl _
    · rename_i hnone
      exact absurd (hnone.symm.trans hout) (by simp)
  · rename_i hcond
    exact absurd (And.intro hlo hhi) hcond

/-- **The emitted spill store block is a `spillStoreOps` block.** The list
    `physBodyWithStores` emits splits around exactly the `spillStoreOps` block of
    the designated spilled binding's output cell and remapped destination. -/
theorem physBodyWithStores_spillStoreOps
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
    (hspill : (physRmap body outStoreMap reservedVec d).isSpill = true) :
    ∃ pre post,
      physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase
          abiW memrefBaseReload callArgBaseReload reservedVec
        = pre ++ atTagZero (spillStoreOps (physAbiMovReg body abiW)
            (physAbiMovBuf body abiW) storeBase off
            (physRmap body outStoreMap reservedVec d)) ++ post := by
  rw [physBodyWithStores_eq_flatMap]
  refine split_trans (flatMap_split_of_mem _ _ hmem) ?_
  exact physPositionEmit_spillStoreOps shiftImm body inLoadMap loadBase outStoreMap
    storeBase abiW memrefBaseReload callArgBaseReload reservedVec hi hlo hhi hout hspill

end CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreSpillArm
