/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# Redundant spill-reload elimination over `List (JInstr 64)`

A peephole that deletes the reload of an adjacent store/reload pair against the
same frame cell and the same register:

```
movq %r15, 16(%rsp)     -- storeMem "%rsp" 16 (.reg "%r15")
movq 16(%rsp), %r15     -- loadMem "%r15" "%rsp" 16     (deleted)
```

The reload writes back into `%r15` the word the store just read out of it, so it
leaves the whole machine state fixed (`evalInstr_loadMem_storeMem`). Deleting it
preserves `runBlock` on every start state, and preserves the direct-addressing
constant-time class because the output is a sublist of the input.

## Contents

* `isRedundantReload bases i j` — the syntactic recognizer: `i` stores register
  `r` into `(base, off)` with `base ∈ bases`, and `j` loads `(base, off)` back
  into `r`.
* `dropReloads bases` — the rewrite, a single right-to-left sweep deleting the
  reload of each recognized pair.
* `dropReloads_runBlock` — full `runBlock`-state equality on every block and
  every state.
* `dropReloads_allDirect` — constant-time-class preservation, from
  `dropReloads_sublist`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.RedundantReloadElim

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)

/-! ## 1. The state lemmas the deletion rests on -/

/-- Rewriting a register with the value it already holds is the identity. -/
theorem setReg_get_self {w : Nat} (s : JState w) (r : String) :
    s.setReg r (s.get r) = s := by
  have hfun : (fun r' => if r' = r then s.regs r else s.regs r') = s.regs := by
    funext r'
    by_cases h : r' = r <;> simp [h]
  simp only [JState.setReg, JState.get, hfun]

/-- **The reload of a just-spilled register is a no-op.** After
    `storeMem base off (.reg r)`, the cell `(base, off)` holds the value of `r`, so
    `loadMem r base off` writes `r` back to itself and the state is unchanged. -/
theorem evalInstr_loadMem_storeMem (s : JState 64) (base : String) (off : Int)
    (r : String) :
    evalInstr (evalInstr s (JInstr.storeMem base off (.reg r)))
        (JInstr.loadMem r base off)
      = evalInstr s (JInstr.storeMem base off (.reg r)) := by
  have hload : (evalInstr s (JInstr.storeMem base off (.reg r))).load base off
      = (evalInstr s (JInstr.storeMem base off (.reg r))).get r := by
    simp [evalInstr, x86_MOV, JState.store, JState.get]
  show (evalInstr s (JInstr.storeMem base off (.reg r))).setReg r
      (x86_MOV ((evalInstr s (JInstr.storeMem base off (.reg r))).load base off))
    = evalInstr s (JInstr.storeMem base off (.reg r))
  rw [x86_MOV, hload, setReg_get_self]

/-! ## 2. The syntactic recognizer -/

/-- The frame cell and source register of a register-to-memory store. -/
def storeKey : JInstr 64 → Option (String × Int × String)
  | .storeMem base off (.reg r) => some (base, off, r)
  | _ => none

/-- The frame cell and destination register of a memory-to-register load. -/
def loadKey : JInstr 64 → Option (String × Int × String)
  | .loadMem r base off => some (base, off, r)
  | _ => none

theorem storeKey_eq {i : JInstr 64} {base : String} {off : Int} {r : String}
    (h : storeKey i = some (base, off, r)) : i = .storeMem base off (.reg r) := by
  unfold storeKey at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · exact absurd h (by simp)

theorem loadKey_eq {j : JInstr 64} {base : String} {off : Int} {r : String}
    (h : loadKey j = some (base, off, r)) : j = .loadMem r base off := by
  unfold loadKey at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · exact absurd h (by simp)

/-- The spill bases a reload is deleted against: the two frame pointers the owned
    backend materializes spill slots on. -/
def defaultSpillBases : List String := ["%rsp", "%rbp"]

/-- `isRedundantReload bases i j`: `i` stores register `r` into the cell
    `(base, off)` with `base` among `bases`, and `j` loads that same cell back into
    that same `r`. -/
def isRedundantReload (bases : List String) (i j : JInstr 64) : Bool :=
  match storeKey i, loadKey j with
  | some (base, off, r), some (base', off', r') =>
      base == base' && off == off' && r == r' && bases.contains base
  | _, _ => false

/-- A recognized pair is a store followed by the matching reload. -/
theorem eq_of_isRedundantReload {bases : List String} {i j : JInstr 64}
    (h : isRedundantReload bases i j = true) :
    ∃ (base : String) (off : Int) (r : String),
      i = .storeMem base off (.reg r) ∧ j = .loadMem r base off := by
  unfold isRedundantReload at h
  split at h
  · rename_i base off r base' off' r' hsi hlj
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hb, ho⟩, hr⟩, _⟩ := h
    subst hb; subst ho; subst hr
    exact ⟨base, off, r, storeKey_eq hsi, loadKey_eq hlj⟩
  · exact absurd h (by simp)

/-! ## 3. The rewrite -/

/-- Prepend `i` to an already-swept tail, deleting the tail's head when it is the
    redundant reload of `i`. -/
def consDrop (bases : List String) (i : JInstr 64) :
    List (JInstr 64) → List (JInstr 64)
  | [] => [i]
  | j :: rest => if isRedundantReload bases i j then i :: rest else i :: j :: rest

/-- **Redundant spill-reload elimination.** A right-to-left sweep deleting the
    reload of every adjacent store/reload pair against a `bases` frame cell. -/
def dropReloads (bases : List String) : List (JInstr 64) → List (JInstr 64)
  | [] => []
  | i :: rest => consDrop bases i (dropReloads bases rest)

@[simp] theorem dropReloads_nil (bases : List String) : dropReloads bases [] = [] := rfl

@[simp] theorem dropReloads_cons (bases : List String) (i : JInstr 64)
    (rest : List (JInstr 64)) :
    dropReloads bases (i :: rest) = consDrop bases i (dropReloads bases rest) := rfl

/-! ## 4. Semantic soundness -/

/-- The deletion inside `consDrop` preserves `runBlock` on every state. -/
theorem consDrop_runBlock (bases : List String) (i : JInstr 64)
    (k : List (JInstr 64)) (s : JState 64) :
    runBlock s (consDrop bases i k) = runBlock s (i :: k) := by
  cases k with
  | nil => rfl
  | cons j rest =>
    rw [consDrop]
    split
    · rename_i h
      obtain ⟨base, off, r, rfl, rfl⟩ := eq_of_isRedundantReload h
      rw [runBlock_cons, runBlock_cons, runBlock_cons, evalInstr_loadMem_storeMem]
    · rfl

/-- **The pass preserves the whole machine state.** On every block and every start
    state the swept block lands in the same `runBlock` final state as the input. -/
theorem dropReloads_runBlock (bases : List String) :
    ∀ (b : List (JInstr 64)) (s : JState 64),
      runBlock s (dropReloads bases b) = runBlock s b := by
  intro b
  induction b with
  | nil => intro s; rfl
  | cons i rest ih =>
    intro s
    rw [dropReloads_cons, consDrop_runBlock, runBlock_cons, runBlock_cons, ih]

/-! ## 5. Constant-time preservation -/

/-- The swept block is a sublist of the input: the pass only deletes. -/
theorem consDrop_sublist (bases : List String) (i : JInstr 64) (k : List (JInstr 64)) :
    (consDrop bases i k).Sublist (i :: k) := by
  cases k with
  | nil => exact List.Sublist.refl _
  | cons j rest =>
    rw [consDrop]
    split
    · exact ((List.Sublist.refl rest).cons j).cons_cons i
    · exact List.Sublist.refl _

theorem dropReloads_sublist (bases : List String) (b : List (JInstr 64)) :
    (dropReloads bases b).Sublist b := by
  induction b with
  | nil => exact List.nil_sublist _
  | cons i rest ih =>
    rw [dropReloads_cons]
    exact (consDrop_sublist bases i (dropReloads bases rest)).trans (ih.cons_cons i)

/-- `allDirect` is inherited by sublists: it is a conjunction over the members. -/
theorem allDirect_of_sublist {w : Nat} {a b : List (JInstr w)} (h : a.Sublist b)
    (hb : allDirect b = true) : allDirect a = true := by
  rw [allDirect, List.all_eq_true] at hb ⊢
  exact fun i hi => hb i (h.subset hi)

/-- **The pass preserves the direct-addressing constant-time class.** -/
theorem dropReloads_allDirect (bases : List String) (b : List (JInstr 64))
    (h : allDirect b = true) : allDirect (dropReloads bases b) = true :=
  allDirect_of_sublist (dropReloads_sublist bases b) h

end CatCrypt.Crypto.Optimizer.RedundantReloadElim
