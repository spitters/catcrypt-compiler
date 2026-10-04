/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import CatCrypt.Crypto.Optimizer.GenericRegAlloc
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Hash-map implementations of the live-range analysis

`GenericRegAlloc.liveRanges` collects the distinct names of a block with a
list-membership test per name and then scans the whole block once per name for
its first write and its last use, so a block of `n` instructions over `k` names
costs about `n · k` steps. `liveRangesFast` computes the same list in three
passes: the names in first-seen order through a hash set, the first write of
every name in one right fold, and the last use of every name in one left fold.
`liveRanges_eq_fast` states the equality and is registered with `@[csimp]`, so
code compiled in a module importing this one runs the hash-map version while
the proofs keep the list version.

`lookupMap` turns an association list into a hash map with the first entry for
a key winning, as in `List.lookup` (`lookupMap_getElem?`).

## Main definitions

* `lookupMap`: an association list keyed by strings as a hash map.
* `blockNamesFast`, `defIdxMap`, `lastUseMap`: the three passes.
* `liveRangesFast`: the live ranges from the three passes.

## Main results

* `blockNames_eq_fast`, `defIdxMap_getD`, `lastUseMap_getD`: each pass computes
  its list counterpart.
* `liveRanges_eq_fast`: `liveRanges = liveRangesFast`, registered with
  `@[csimp]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.GenericRegAlloc

variable {I : Type}

/-! ## Association lists as hash maps -/

/-- An association list keyed by strings as a hash map. The first entry for a
    key wins, as in `List.lookup`. -/
def lookupMap {α : Type} (l : List (String × α)) : Std.HashMap String α :=
  l.foldr (fun e m => m.insert e.1 e.2) ∅

theorem lookupMap_getElem? {α : Type} (l : List (String × α)) (n : String) :
    (lookupMap l)[n]? = l.lookup n := by
  induction l with
  | nil => simp [lookupMap]
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    simp only [lookupMap, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getElem?_insert, ih, List.lookup_cons, BEq.comm (a := a) (b := n)]
    cases n == a <;> rfl

/-! ## First write and last use -/

/-- `m` with every name of `names` bound to `v`. -/
def insertAll (m : Std.HashMap String Nat) (names : List String) (v : Nat) :
    Std.HashMap String Nat :=
  names.foldl (fun m n => m.insert n v) m

theorem insertAll_getElem? (m : Std.HashMap String Nat) (names : List String) (v : Nat)
    (n : String) :
    (insertAll m names v)[n]? = if names.contains n then some v else m[n]? := by
  induction names generalizing m with
  | nil => simp [insertAll]
  | cons a t ih =>
    simp only [insertAll, List.foldl_cons] at ih ⊢
    rw [ih, Std.HashMap.getElem?_insert, List.contains_cons, BEq.comm (a := n) (b := a)]
    cases t.contains n <;> cases a == n <;> rfl

/-- The first index at which each name of the block is written. A right fold
    over the indexed block, so an earlier write overrides a later one. -/
def defIdxMap [MachineModel I] (block : List I) : Std.HashMap String Nat :=
  block.zipIdx.foldr (fun p m => insertAll m (writtenNames p.1) p.2) ∅

theorem defIdxMap_go [MachineModel I] (l : List (I × Nat)) (n : String) :
    (l.foldr (fun p m => insertAll m (writtenNames p.1) p.2) ∅)[n]?
      = (l.find? (fun (i, _) => (writtenNames i).contains n)).map (·.2) := by
  induction l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [List.foldr_cons, insertAll_getElem?, ih, List.find?_cons]
    cases h : (writtenNames a).contains n <;> simp only [h] <;> rfl

theorem defIdxMap_getD [MachineModel I] (block : List I) (n : String) :
    ((defIdxMap block)[n]?).getD 0 = defIdxOf block n := by
  rw [defIdxMap, defIdxMap_go, defIdxOf]
  cases List.find? (fun (i, _) => (writtenNames i).contains n) block.zipIdx with
  | none => rfl
  | some p => obtain ⟨_, _⟩ := p; rfl

/-- The last index at which each name of the block is read or written. A left
    fold over the indexed block, so a later use overrides an earlier one. -/
def lastUseMap [MachineModel I] (block : List I) : Std.HashMap String Nat :=
  block.zipIdx.foldl (fun m p => insertAll m (writtenNames p.1 ++ readNames p.1) p.2) ∅

theorem lastUseMap_go [MachineModel I] (l : List (I × Nat)) (n : String)
    (m : Std.HashMap String Nat) (acc : Nat) (h : (m[n]?).getD 0 = acc) :
    ((l.foldl (fun m p => insertAll m (writtenNames p.1 ++ readNames p.1) p.2) m)[n]?).getD 0
      = l.foldl (fun acc (i, idx) =>
          if (writtenNames i).contains n ∨ (readNames i).contains n then idx
          else acc) acc := by
  induction l generalizing m acc with
  | nil => simpa using h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    rw [insertAll_getElem?, List.contains_append]
    cases h1 : (writtenNames a).contains n <;> cases h2 : (readNames a).contains n <;>
      simp only [h1, h2, Bool.or_self, Bool.or_true, Bool.or_false, ↓reduceIte, true_or,
        or_true, or_self, Bool.false_eq_true, Option.getD_some, h]

theorem lastUseMap_getD [MachineModel I] (block : List I) (n : String) :
    ((lastUseMap block)[n]?).getD 0 = lastUseIdx block n :=
  lastUseMap_go _ n ∅ 0 (by simp)

/-! ## Distinct names in first-seen order -/

/-- One step of `blockNamesFast`: the set of names seen and the names in
    first-seen order. -/
def blockNamesStep (st : Std.HashSet String × Array String) (n : String) :
    Std.HashSet String × Array String :=
  if st.1.contains n then st else (st.1.insert n, st.2.push n)

theorem blockNames_go (l : List String) (st : Std.HashSet String × Array String)
    (acc : List String) (hs : ∀ x, st.1.contains x = acc.contains x)
    (ha : st.2.toList = acc) :
    (l.foldl blockNamesStep st).2.toList
      = l.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) acc := by
  induction l generalizing st acc with
  | nil => simpa using ha
  | cons n t ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · intro x
      unfold blockNamesStep
      rw [← hs n]
      cases st.1.contains n
      · simp only [Bool.false_eq_true, ↓reduceIte, Std.HashSet.contains_insert,
          List.contains_append, hs x, List.contains_cons, List.contains_nil, Bool.or_false]
        rw [Bool.or_comm, BEq.comm]
      · simp only [↓reduceIte, hs x]
    · unfold blockNamesStep
      rw [← hs n]
      cases st.1.contains n
      · simp [ha]
      · simpa using ha

/-- Every distinct name in the block, in first-seen order, through a hash set. -/
def blockNamesFast [MachineModel I] (block : List I) : List String :=
  ((block.flatMap (fun i => writtenNames i ++ readNames i)).foldl
    blockNamesStep (∅, #[])).2.toList

theorem blockNames_eq_fast : @blockNames = @blockNamesFast := by
  funext I _ block
  rw [blockNames, blockNamesFast, blockNames_go _ _ [] (by simp) rfl]

/-! ## The live ranges -/

/-- The live ranges of every distinct name in the block, in first-seen order,
    from the three hash-map passes. -/
def liveRangesFast [MachineModel I] (block : List I) : List LiveRange :=
  let d := defIdxMap block
  let u := lastUseMap block
  (blockNamesFast block).map (fun n => ⟨n, (d[n]?).getD 0, (u[n]?).getD 0⟩)

/-- The hash-map live ranges are the list live ranges. -/
@[csimp] theorem liveRanges_eq_fast : @liveRanges = @liveRangesFast := by
  funext I _ block
  simp only [liveRanges, liveRangesFast, ← blockNames_eq_fast, defIdxMap_getD,
    lastUseMap_getD]

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
