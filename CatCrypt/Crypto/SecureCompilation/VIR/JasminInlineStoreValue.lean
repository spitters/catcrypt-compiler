/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminBindingPrefixDenote

@[expose] public section

set_option autoImplicit false

/-!
# The inline output store block and the value it leaves in its cell

`physBodyWithStores` gets a multi-output kernel's results to the C-side `out`
buffer with an inline store block: after the expansion of each of the last `n`
bindings it emits a reload of the out-pointer into `reloadScratch2` followed by
a move of the binding's destination into the cell `memName storeBase off`.
`inlineStoreOps` is that pair at `LinstrR`, and `storeBlocks` is the
concatenation of the blocks of a list of `(offset, source-register)` targets.

`storeBlocks_value` reads the cells of such a run: the cell of target `j` holds
the value its source register held before the run. Composed with
`JasminBindingPrefixDenote.straightOps_binding_denote`,
`storeBlocks_binding_denote` reads each cell as the denotation of the source
program truncated at the binding the target names.

## Scope

The theorems are about the block list `storeBlocks` run as a unit, and
`storeBlocks_binding_denote` is about the order "whole chain, then all stores".
On the emit path the blocks are interleaved with the body expansions rather than
contiguous, so neither is a statement about the instruction order
`physBodyWithStores` emits. `inlineStoreOps` transcribes the non-spill arm of
that emitter's store block; no theorem here identifies the two, so the link to
the emitted instruction list rests on that transcription.

The store opcode is carried as a parameter under the hypothesis that it moves a
word unchanged (`MovesWord`). The narrow buffer moves `MOV:8` and `MOV:16` do
not satisfy it — their `applyOpn` arms truncate — so the results cover the
`abiW ∈ {0, 64}` exports and not the narrow-element ones.
`JasminInlineStoreSpillArm.MovesMasked` carries the narrow moves, and
`JasminInlineStoreOrder` reads a cell in the order `physBodyWithStores` emits.

## Main definitions

* `MovesWord` — the opcode copies its single source word.
* `inlineStoreOps` — the out-pointer reload and the store, at `LinstrR`.
* `storeBlocks` — the blocks of a list of `(offset, source-register)` targets.

## Main results

* `memName_off_injective`, `memName_ne_reloadScratch`,
  `memName_ne_reloadScratch2` — distinctness of the generated cell names.
* `lsemStep_mov` — the step of a word-moving `Lopn`.
* `inlineStoreOps_run`, `inlineStoreOps_value`, `inlineStoreOps_frame` — one
  block's state, the value it leaves in its cell, and what it leaves alone.
* `storeBlocks_dsts`, `storeBlocks_lvm_frame` — a block list writes only
  `reloadScratch2` and its own cells.
* `storeBlocks_value` — target `j`'s cell holds the entry value of target `j`'s
  source register.
* `storeBlocks_binding_denote` — with the sources the binding registers of a
  uniform-`regArith` chain, target `j`'s cell holds the denotation of the source
  program truncated at that binding.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreValue

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminBindingPrefixDenote
open CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

/-! ## 1. Distinctness of the generated cell names

`memName base off = "mem." ++ base ++ "." ++ toString off`. `toString` has no
exposed body under the module system, so no comparison of two such names
reduces; distinctness goes through `String.toList` and `List` cancellation, the
shape of `JasminLsemSimulation.regName_injective`. -/

/-- Two cells of the same base at distinct offsets have distinct names. -/
theorem memName_off_injective (base : String) {o o' : Nat}
    (h : memName base o = memName base o') : o = o' := by
  unfold memName at h
  apply natToString_injective
  have hd := congrArg String.toList h
  simp only [String.toList_append] at hd
  exact String.toList_injective (List.append_cancel_left hd)

/-- Distinct offsets give distinct cell names at a fixed base. -/
theorem memName_ne_of_off_ne (base : String) {o o' : Nat} (h : o ≠ o') :
    memName base o ≠ memName base o' :=
  fun he => h (memName_off_injective base he)

/-- A cell name is never the reload scratch `R15`. -/
theorem memName_ne_reloadScratch (base : String) (off : Nat) :
    memName base off ≠ reloadScratch := by
  unfold memName reloadScratch
  intro h
  have hd := congrArg (fun s => s.toList.head?) h
  simp [String.toList_append] at hd

/-- A cell name is never the out-pointer scratch `R14`. -/
theorem memName_ne_reloadScratch2 (base : String) (off : Nat) :
    memName base off ≠ reloadScratch2 := by
  unfold memName reloadScratch2
  intro h
  have hd := congrArg (fun s => s.toList.head?) h
  simp [String.toList_append] at hd

/-! ## 2. One block -/

/-- The opcode copies its single source word: the modeled semantics of `MOV`,
    `MOV:64` and `MOVQ`. The narrow buffer moves `MOV:8` and `MOV:16` do not
    satisfy it. -/
def MovesWord (w : Nat) (opn : String) : Prop :=
  ∀ v : BitVec w, applyOpn (w := w) (stripWidthTag opn) [v] = some v

/-- `stripWidthTag` leaves the untagged `MOVQ` mnemonic alone. -/
@[simp] theorem stripWidthTag_MOVQ : stripWidthTag "MOVQ" = "MOVQ" := by decide +kernel

/-- `stripWidthTag` strips the `:64` tag of the wide `MOV`. -/
@[simp] theorem stripWidthTag_MOV64 : stripWidthTag "MOV:64" = "MOV" := by decide +kernel

/-- `MOVQ` moves a word. -/
theorem MovesWord_MOVQ (w : Nat) : MovesWord w "MOVQ" := by
  intro v; simp [applyOpn]

/-- `MOV` moves a word. -/
theorem MovesWord_MOV (w : Nat) : MovesWord w "MOV" := by
  intro v; simp [applyOpn]

/-- `MOV:64` moves a word. -/
theorem MovesWord_MOV64 (w : Nat) : MovesWord w "MOV:64" := by
  intro v; simp [applyOpn]

/-- The step of a single-destination register-to-register move: the destination
    takes the source's value and the pc advances. -/
theorem lsemStep_mov {w : Nat} (dstName srcName movOpn : String) (s : Lstate w)
    (hmov : MovesWord w movOpn) :
    lsemStep (.Lopn [.reg dstName] movOpn [.reg srcName]) s
      = some ((s.setReg dstName (s.lvm srcName)).nextPc) := by
  have hm : applyOpn (w := w) (stripWidthTag movOpn) [s.lvm srcName]
      = some (s.lvm srcName) := hmov _
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, hm]

/-- The instruction pair `physBodyWithStores` emits after the expansion of a
    designated binding whose destination is not a spill slot: recover the
    out-pointer from its red-zone save slot into `reloadScratch2`, then move the
    binding's destination into the cell `memName storeBase off`. -/
def inlineStoreOps (movOpn storeBase : String) (off : Nat) (src : LOperand) :
    List LinstrR :=
  [ .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName],
    .Lopn [.reg (memName storeBase off)] movOpn [src] ]

/-- **The block's run.** A block whose source register is not the out-pointer
    scratch writes `reloadScratch2` and then the cell, the cell receiving the
    source's entry value. -/
theorem inlineStoreOps_run {w : Nat} (movOpn storeBase : String) (off : Nat)
    (srcName : String) (hmov : MovesWord w movOpn)
    (hsrc : srcName ≠ reloadScratch2) (s : Lstate w) :
    lsemStraight (inlineStoreOps movOpn storeBase off (.reg srcName)) s
      = some ((((s.setReg reloadScratch2 (s.lvm abiSaveRdiName)).nextPc).setReg
          (memName storeBase off) (s.lvm srcName)).nextPc) := by
  have hne : ((s.setReg reloadScratch2 (s.lvm abiSaveRdiName)).nextPc).lvm srcName
      = s.lvm srcName := by simp [Lstate.setReg, hsrc]
  rw [inlineStoreOps, lsemStraight_cons,
    lsemStep_mov reloadScratch2 abiSaveRdiName "MOVQ" s (MovesWord_MOVQ w)]
  simp only [lsemStraight_cons,
    lsemStep_mov (memName storeBase off) srcName movOpn _ hmov, hne,
    lsemStraight_nil]

/-- **The block leaves the source's value in its cell.** -/
theorem inlineStoreOps_value {w : Nat} (movOpn storeBase : String) (off : Nat)
    (srcName : String) (hmov : MovesWord w movOpn)
    (hsrc : srcName ≠ reloadScratch2) (s s' : Lstate w)
    (h : lsemStraight (inlineStoreOps movOpn storeBase off (.reg srcName)) s = some s') :
    s'.lvm (memName storeBase off) = s.lvm srcName := by
  rw [inlineStoreOps_run movOpn storeBase off srcName hmov hsrc s] at h
  cases h
  simp [Lstate.setReg]

/-- **What the block leaves alone.** Every register other than the out-pointer
    scratch and the block's own cell reads as it did on entry. -/
theorem inlineStoreOps_frame {w : Nat} (movOpn storeBase : String) (off : Nat)
    (srcName : String) (hmov : MovesWord w movOpn)
    (hsrc : srcName ≠ reloadScratch2) (s s' : Lstate w)
    (h : lsemStraight (inlineStoreOps movOpn storeBase off (.reg srcName)) s = some s')
    (r : String) (hr1 : r ≠ reloadScratch2) (hr2 : r ≠ memName storeBase off) :
    s'.lvm r = s.lvm r := by
  rw [inlineStoreOps_run movOpn storeBase off srcName hmov hsrc s] at h
  cases h
  simp [Lstate.setReg, hr1, hr2]

/-! ## 3. A list of blocks -/

/-- The store blocks of a list of `(offset, source-register)` output targets, in
    target order. -/
def storeBlocks (movOpn storeBase : String) (targets : List (Nat × String)) :
    List LinstrR :=
  targets.flatMap (fun p => inlineStoreOps movOpn storeBase p.1 (.reg p.2))

/-- Every instruction of a block list is a single-destination `Lopn` writing
    either the out-pointer scratch or one of the list's own cells. -/
theorem storeBlocks_dsts (movOpn storeBase : String) (targets : List (Nat × String)) :
    ∀ i ∈ storeBlocks movOpn storeBase targets,
      ∃ dst opn srcs, i = .Lopn [.reg dst] opn srcs ∧
        (dst = reloadScratch2 ∨ ∃ p ∈ targets, dst = memName storeBase p.1) := by
  intro i hi
  rw [storeBlocks, List.mem_flatMap] at hi
  obtain ⟨p, hp, hi⟩ := hi
  rw [inlineStoreOps] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h <;> subst h
  · exact ⟨_, _, _, rfl, Or.inl rfl⟩
  · exact ⟨_, _, _, rfl, Or.inr ⟨p, hp, rfl⟩⟩

/-- **What a block list leaves alone.** A register that is neither the
    out-pointer scratch nor one of the list's cells reads as it did on entry. -/
theorem storeBlocks_lvm_frame {w : Nat} (movOpn storeBase : String)
    (targets : List (Nat × String)) (s s' : Lstate w)
    (h : lsemStraight (storeBlocks movOpn storeBase targets) s = some s')
    (r : String) (hr1 : r ≠ reloadScratch2)
    (hr2 : ∀ p ∈ targets, r ≠ memName storeBase p.1) :
    s'.lvm r = s.lvm r := by
  refine lsemStraight_lvm_of_dsts
    (fun n => n = reloadScratch2 ∨ ∃ p ∈ targets, n = memName storeBase p.1)
    _ s s' (storeBlocks_dsts movOpn storeBase targets) h r ?_
  rintro (rfl | ⟨p, hp, rfl⟩)
  · exact hr1 rfl
  · exact hr2 p hp rfl

/-- **Each target's cell holds its source's entry value.** For a list of output
    targets at a fixed base whose offsets are pairwise distinct and whose source
    registers are neither the out-pointer scratch nor a cell of the list, running
    the blocks reaches a state in which target `j`'s cell holds the value target
    `j`'s source register held on entry.

    The side conditions are the ones the emit path discharges outside Lean: a
    designated source register is a physical GP register, hence neither `R14`
    (`hsrcR14`) nor `R15` nor a cell name (both under `hsrcCell`, since `R15` is
    ruled out by `memName_ne_reloadScratch`), and
    `scripts/outstoremap-distinct-gate.sh` enforces the pairwise distinctness of
    the offsets (`hdistinct`). -/
theorem storeBlocks_value {w : Nat} (movOpn storeBase : String)
    (hmov : MovesWord w movOpn) :
    ∀ (targets : List (Nat × String)) (s s' : Lstate w),
      lsemStraight (storeBlocks movOpn storeBase targets) s = some s' →
      (∀ p ∈ targets, p.2 ≠ reloadScratch2) →
      (∀ p ∈ targets, ∀ q ∈ targets, p.2 ≠ memName storeBase q.1) →
      targets.Pairwise (fun p q => p.1 ≠ q.1) →
      ∀ p ∈ targets, s'.lvm (memName storeBase p.1) = s.lvm p.2 := by
  intro targets
  induction targets with
  | nil => intro s s' _ _ _ _ p hp; simp at hp
  | cons a rest ih =>
      intro s s' hrun hsrcR14 hsrcCell hdistinct p hp
      rw [storeBlocks, List.flatMap_cons, lsemStraight_append] at hrun
      rcases hstep : lsemStraight (inlineStoreOps movOpn storeBase a.1 (.reg a.2)) s
        with _ | s1
      · rw [hstep] at hrun; simp at hrun
      · rw [hstep] at hrun
        simp only [Option.bind_some] at hrun
        have hrest : lsemStraight (storeBlocks movOpn storeBase rest) s1 = some s' := by
          rw [storeBlocks]; exact hrun
        have hdist' : rest.Pairwise (fun p q => p.1 ≠ q.1) :=
          (List.pairwise_cons.mp hdistinct).2
        have hhead : ∀ q ∈ rest, a.1 ≠ q.1 := (List.pairwise_cons.mp hdistinct).1
        rcases List.mem_cons.mp hp with rfl | hp'
        · have hcell : s'.lvm (memName storeBase p.1) = s1.lvm (memName storeBase p.1) := by
            refine storeBlocks_lvm_frame movOpn storeBase rest s1 s' hrest _
              (memName_ne_reloadScratch2 storeBase p.1) ?_
            intro q hq
            exact memName_ne_of_off_ne storeBase (hhead q hq)
          rw [hcell]
          exact inlineStoreOps_value movOpn storeBase p.1 p.2 hmov
            (hsrcR14 p (by simp)) s s1 hstep
        · have hframe : s1.lvm p.2 = s.lvm p.2 :=
            inlineStoreOps_frame movOpn storeBase a.1 a.2 hmov
              (hsrcR14 a (by simp)) s s1 hstep p.2
              (hsrcR14 p (by simp [hp']))
              (hsrcCell p (by simp [hp']) a (by simp))
          rw [← hframe]
          exact ih s1 s' hrest (fun q hq => hsrcR14 q (by simp [hq]))
            (fun q hq q' hq' => hsrcCell q (by simp [hq]) q' (by simp [hq']))
            hdist' p hp'

/-! ## 4. Reading the cells as truncated denotations -/

/-- **A target's cell holds the truncated denotation.** Running the chain a
    uniform-`regArith` `Com` emits and then the store blocks, the cell of a
    target whose source is binding `k`'s register holds the denotation of the
    source program truncated at binding `k`.

    The order here is the whole chain followed by all the stores. On the emit
    path `physBodyWithStores` interleaves each block after its binding's
    expansion instead, so this is the composition of the two proved pieces and
    not a statement about the emitted instruction order. -/
theorem storeBlocks_binding_denote {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com)
    (movOpn storeBase : String) (hmov : MovesWord w movOpn)
    {nArgs curDepth : Nat} {st stMid st' : Lstate w} {V : Ctxt.Valuation Γ}
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgrees w nArgs curDepth st V)
    (hchain : lsemStraight (straightOps nArgs com curDepth) st = some stMid)
    (targets : List (Nat × String))
    (hrun : lsemStraight (storeBlocks movOpn storeBase targets) stMid = some st')
    (hsrcR14 : ∀ p ∈ targets, p.2 ≠ reloadScratch2)
    (hsrcCell : ∀ p ∈ targets, ∀ q ∈ targets, p.2 ≠ memName storeBase q.1)
    (hdistinct : targets.Pairwise (fun p q => p.1 ≠ q.1))
    (off k : Nat) (hmem : (off, regName (curDepth + k)) ∈ targets)
    (hk : k < comLen com) (hty : comBindingTy com k = .reg w) :
    st'.lvm (memName storeBase off)
      = (hty ▸ (comPrefix com k).denote V : ⟦(JasminTy.reg w)⟧) := by
  have hval := storeBlocks_value movOpn storeBase hmov targets stMid st' hrun
    hsrcR14 hsrcCell hdistinct (off, regName (curDepth + k)) hmem
  rw [hval]
  exact straightOps_binding_denote hcom hlen harg hagree hchain hk hty

end CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreValue
