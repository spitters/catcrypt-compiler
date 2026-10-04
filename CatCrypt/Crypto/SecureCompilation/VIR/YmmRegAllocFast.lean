/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.GenericRegAllocFast
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAllocSound

/-!
# Hash-map implementations of the vector allocator

`YmmRegAlloc.ymmMaterialize`, `ymmScratchNeeded`, `spilledRanges`,
`compactSlots` and `slotsReuseDisjoint` look names up in the decision list with
`List.lookup`, once per name an instruction touches, so a program of `n`
instructions with `k` decisions costs about `n · k` steps. Each `…Fast`
definition here computes the same value with the decisions in a hash map built
once (`YmmRegAllocSound.decisionMap`), and each equation `…_eq_fast` is
registered with `@[csimp]`: code compiled in a module importing this one runs
the hash-map versions while the proofs keep the list versions.

`ymmLiveRangesFast`, `ymmAllocWithScratchFast` and `ymmAllocFewestScratchFast`
have the bodies of `ymmLiveRanges`, `ymmAllocWithScratch` and
`ymmAllocFewestScratch`; they are compiled after the equations above and
`GenericRegAllocFast.liveRanges_eq_fast` are registered, so their compiled
bodies call the hash-map versions, and each equals its original by `rfl`.

## Main definitions

* `spillSlotBy`, `residentRegBy`, `ymmMaterializeInstrBy`: the list functions
  with the decisions given as a lookup function.
* `ymmMaterializeFast`, `ymmScratchNeededFast`, `spilledRangesFast`,
  `compactSlotsFast`, `slotsReuseDisjointFast`: the hash-map versions.

## Main results

* `ymmMaterialize_eq_fast`, `ymmScratchNeeded_eq_fast`, `spilledRanges_eq_fast`,
  `compactSlots_eq_fast`, `slotsReuseDisjoint_eq_fast`, `ymmLiveRanges_eq_fast`,
  `ymmAllocWithScratch_eq_fast`, `ymmAllocFewestScratch_eq_fast`: the
  `@[csimp]` equations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc

open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAllocSound

/-! ## Lookups through a function -/

/-- `spillSlotOf` with the decisions given as a lookup function. -/
def spillSlotBy (look : String → Option Slot) (n : String) : Option Int :=
  match look n with
  | some (.spilled off) => some off
  | _ => none

theorem spillSlotBy_lookup (d : List (String × Slot)) :
    spillSlotBy (fun n => d.lookup n) = spillSlotOf d := rfl

/-- `residentReg` with the decisions given as a lookup function. -/
def residentRegBy (look : String → Option Slot) (n : String) : Option String :=
  match look n with
  | some (.resident r) => some r
  | _ => none

theorem residentRegBy_lookup (d : List (String × Slot)) :
    residentRegBy (fun n => d.lookup n) = residentReg d := rfl

/-- The lookup function of the hash map of the decisions is `List.lookup`. -/
theorem decisionMap_lookup (d : List (String × Slot)) :
    (fun n => (decisionMap d)[n]?) = (fun n => d.lookup n) :=
  funext (decisionMap_getElem? d)

/-! ## Materialization and the scratch count -/

/-- `ymmMaterializeInstr` with the decisions given as a lookup function. -/
def ymmMaterializeInstrBy (look : String → Option Slot) (scratch : List String)
    (i : YmmInstr) : List YmmInstr :=
  let spilled := spilledNamesBy look i
  let scr : String → Option String := fun n =>
    (spilled.findIdx? (· == n)).bind (fun k => scratch[k]?)
  let phys : String → String := fun n =>
    match residentRegBy look n with
    | some r => r
    | none   => (scr n).getD n
  let reloads := (ymmReadNames i).eraseDups.filterMap (fun n =>
    (spillSlotBy look n).bind (fun off =>
      (scr n).map (fun s => YmmInstr.yload s ⟨ymmFrameBase, off⟩)))
  let stores := (ymmWrittenNames i).eraseDups.filterMap (fun n =>
    (spillSlotBy look n).bind (fun off =>
      (scr n).map (fun s => YmmInstr.ystore ⟨ymmFrameBase, off⟩ s)))
  reloads ++ renameYmm phys i :: stores

theorem ymmMaterializeInstrBy_lookup (d : List (String × Slot)) (scratch : List String) :
    ymmMaterializeInstrBy (fun n => d.lookup n) scratch = ymmMaterializeInstr d scratch := by
  funext i
  simp only [ymmMaterializeInstrBy, ymmMaterializeInstr, spilledNamesBy_lookup]
  rfl

/-- `ymmMaterialize` over the hash map of the decisions. -/
def ymmMaterializeFast (d : List (String × Slot)) (scratch : List String)
    (block : List YmmInstr) : List YmmInstr :=
  let m := decisionMap d
  block.flatMap (ymmMaterializeInstrBy (fun n => m[n]?) scratch)

/-- The hash-map materialization is the list materialization. -/
@[csimp] theorem ymmMaterialize_eq_fast : @ymmMaterialize = @ymmMaterializeFast := by
  funext d scratch block
  simp only [ymmMaterializeFast, decisionMap_lookup, ymmMaterializeInstrBy_lookup,
    ymmMaterialize]

/-- `ymmScratchNeeded` over the hash map of the decisions. -/
def ymmScratchNeededFast (d : List (String × Slot)) (block : List YmmInstr) : Nat :=
  let m := decisionMap d
  block.foldl (fun k i => max k (spilledNamesBy (fun n => m[n]?) i).length) 0

/-- The hash-map scratch count is the list scratch count. -/
@[csimp] theorem ymmScratchNeeded_eq_fast : @ymmScratchNeeded = @ymmScratchNeededFast := by
  funext d block
  simp only [ymmScratchNeededFast, decisionMap_lookup, spilledNamesBy_lookup,
    ymmScratchNeeded]

/-! ## Frame-cell reuse -/

/-- `spilledRanges` over the hash map of the decisions. -/
def spilledRangesFast (lrs : List LiveRange) (d : List (String × Slot)) :
    List LiveRange :=
  let m := decisionMap d
  (lrs.filter (fun lr => (spillSlotBy (fun n => m[n]?) lr.name).isSome)).mergeSort
    (fun a b => a.defIdx ≤ b.defIdx)

/-- The hash-map spilled ranges are the list spilled ranges. -/
@[csimp] theorem spilledRanges_eq_fast : @spilledRanges = @spilledRangesFast := by
  funext lrs d
  simp only [spilledRangesFast, decisionMap_lookup, spillSlotBy_lookup, spilledRanges]

/-- `compactSlots` with the reassigned cells in a hash map. -/
def compactSlotsFast (lrs : List LiveRange) (frameBase : Int)
    (decisions : List (String × Slot)) : List (String × Slot) :=
  let assign := lookupMap (compactSlotsGo frameBase [] [] (spilledRanges lrs decisions))
  decisions.map (fun d => match d.2 with
    | .spilled off => (d.1, .spilled ((assign[d.1]?).getD off))
    | .resident r => (d.1, .resident r))

/-- The hash-map cell reassignment is the list cell reassignment. -/
@[csimp] theorem compactSlots_eq_fast : @compactSlots = @compactSlotsFast := by
  funext lrs frameBase decisions
  simp only [compactSlotsFast, lookupMap_getElem?, compactSlots]
  rfl

/-- `slotsReuseDisjoint` over the hash map of the decisions. -/
def slotsReuseDisjointFast (lrs : List LiveRange) (decisions : List (String × Slot)) :
    Bool :=
  let m := decisionMap decisions
  let sp := (spilledRanges lrs decisions).filterMap (fun lr =>
    (spillSlotBy (fun n => m[n]?) lr.name).map (fun off => (lr, off)))
  sp.zipIdx.all (fun (p, i) => sp.zipIdx.all (fun (q, j) =>
    i == j || p.2 != q.2 || p.1.lastUse < q.1.defIdx || q.1.lastUse < p.1.defIdx))

/-- The hash-map disjointness check is the list disjointness check. -/
@[csimp] theorem slotsReuseDisjoint_eq_fast :
    @slotsReuseDisjoint = @slotsReuseDisjointFast := by
  funext lrs decisions
  simp only [slotsReuseDisjointFast, decisionMap_lookup, spillSlotBy_lookup,
    slotsReuseDisjoint]

/-! ## The allocation, compiled against the hash-map versions -/

/-- `ymmLiveRanges`, compiled after `liveRanges_eq_fast`. -/
def ymmLiveRangesFast (block : List YmmInstr) : List LiveRange :=
  liveRanges (I := YmmInstr) block

@[csimp] theorem ymmLiveRanges_eq_fast : @ymmLiveRanges = @ymmLiveRangesFast := rfl

/-- `ymmAllocWithScratch`, compiled after `compactSlots_eq_fast`. -/
def ymmAllocWithScratchFast (file pinned scratch : List String) (frameBase : Int)
    (lrs : List LiveRange) (k : Nat) : List String × List (String × Slot) :=
  let sc := scratch.take k
  (sc, compactSlots lrs frameBase (ymmSpillAllocRanges file pinned sc frameBase lrs))

@[csimp] theorem ymmAllocWithScratch_eq_fast :
    @ymmAllocWithScratch = @ymmAllocWithScratchFast := rfl

/-- `ymmAllocFewestScratch`, compiled after `ymmAllocWithScratch_eq_fast` and
    `ymmScratchNeeded_eq_fast`. -/
def ymmAllocFewestScratchFast (file pinned scratch : List String) (frameBase : Int)
    (block : List YmmInstr) (lrs : List LiveRange) :
    List String × List (String × Slot) :=
  let fits := (List.range (scratch.length + 1)).find? (fun k =>
    ymmScratchNeeded (ymmAllocWithScratch file pinned scratch frameBase lrs k).2 block ≤ k)
  ymmAllocWithScratch file pinned scratch frameBase lrs (fits.getD scratch.length)

@[csimp] theorem ymmAllocFewestScratch_eq_fast :
    @ymmAllocFewestScratch = @ymmAllocFewestScratchFast := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc
