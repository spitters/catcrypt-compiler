/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter64

/-!
# Register renaming of `RInst64` blocks, checked against liveness

The RV64 kernels are written over symbolic register names (`d0`, `cy1`, `sum__`, …):
between 37 and 90 names per kernel, against 25 allocatable registers. A renaming onto
physical registers must therefore reuse a register once its value is dead, and the
renaming theorems already in the tree do not cover that: `RiscvRegAlloc.renameRBlock_runRBlock`
and `GenericRegAlloc.renameBlock_runBlock` ask for a globally injective renaming, and
`JInstrRegAllocScoped.runBlock_renameBlock_rel_on` (x86) for one injective on every name
of the block.

This module states renaming correctness under a liveness check. `renGo ρ b L` walks `b`
backwards from the live-out names `L`; at each instruction with destination `d` and
live-after set `La` it asks that `ρ d` differs from `ρ x` for every other `x ∈ La`, and
that `ρ d` is a zero register exactly when `d` is. It returns the live-in names. When it
succeeds, running the renamed block from any state that agrees with the original on the
live-in names (read through `ρ`) ends in a state that agrees on `L`.

The checker is a `Bool`-valued function evaluated by `decide` at each kernel; the
allocation it checks is produced by `allocLive64`, a linear scan over live intervals
that is not itself proved.

## Main definitions

* `renameRInst64`, `renameRBlock64`: apply `ρ` to every register operand.
* `liveBefore`, `renGo`: the backward liveness pass and the checker.
* `nameOf`: the renaming given by an association list, identity off its keys.
* `allocLive64`: the (unverified) allocator.

## Main results

* `evalRInst64_eq_set`, `instVal64_rename`: each instruction is one write of a value
  that depends only on its sources.
* `runRBlock64_rename`: renaming correctness under `renGo`.
* `pull_relOn`: the state read back through `ρ` agrees with the physical state on
  every name, when `ρ` fixes the zero registers.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. Renaming and the written value -/

/-- `r` is one of the two spellings of the zero register. -/
def isZeroReg (r : String) : Bool := r == "zero" || r == "x0"

theorem isZeroReg_iff (r : String) : isZeroReg r = true ↔ (r = "zero" ∨ r = "x0") := by
  simp [isZeroReg]

/-- Apply `ρ` to the destination and every source of an instruction. -/
def renameRInst64 (ρ : String → String) : RInst64 → RInst64
  | .add d a b => .add (ρ d) (ρ a) (ρ b)
  | .sub d a b => .sub (ρ d) (ρ a) (ρ b)
  | .sltu d a b => .sltu (ρ d) (ρ a) (ρ b)
  | .and d a b => .and (ρ d) (ρ a) (ρ b)
  | .or d a b => .or (ρ d) (ρ a) (ρ b)
  | .xor d a b => .xor (ρ d) (ρ a) (ρ b)
  | .mul d a b => .mul (ρ d) (ρ a) (ρ b)
  | .mulhu d a b => .mulhu (ρ d) (ρ a) (ρ b)
  | .li d imm => .li (ρ d) imm
  | .mv d a => .mv (ρ d) (ρ a)
  | .srli d a sh => .srli (ρ d) (ρ a) sh
  | .slli d a sh => .slli (ρ d) (ρ a) sh

/-- Apply `ρ` to every instruction of a block. -/
def renameRBlock64 (ρ : String → String) (b : List RInst64) : List RInst64 :=
  b.map (renameRInst64 ρ)

/-- The value an instruction writes to its destination. -/
def instVal64 (s : RState64) : RInst64 → X64R
  | .add _ a b => opAdd64 (s.get a) (s.get b)
  | .sub _ a b => opSub64 (s.get a) (s.get b)
  | .sltu _ a b => opSltu (s.get a) (s.get b)
  | .and _ a b => opAnd64 (s.get a) (s.get b)
  | .or _ a b => opOr64 (s.get a) (s.get b)
  | .xor _ a b => opXor64 (s.get a) (s.get b)
  | .mul _ a b => opMul64 (s.get a) (s.get b)
  | .mulhu _ a b => opMulhu (s.get a) (s.get b)
  | .li _ imm => BitVec.ofNat 64 imm
  | .mv _ a => s.get a
  | .srli _ a sh => s.get a >>> sh
  | .slli _ a sh => s.get a <<< sh

/-- Every instruction is the single write of `instVal64` to its destination. -/
theorem evalRInst64_eq_set (s : RState64) (i : RInst64) :
    evalRInst64 s i = s.set (rinst64DstSrcs i).1 (instVal64 s i) := by
  cases i <;> rfl

/-- The renamed instruction writes `ρ` of the destination. -/
theorem dst_rename (ρ : String → String) (i : RInst64) :
    (rinst64DstSrcs (renameRInst64 ρ i)).1 = ρ (rinst64DstSrcs i).1 := by
  cases i <;> rfl

/-- The renamed instruction writes the same value when every source agrees through `ρ`. -/
theorem instVal64_rename (ρ : String → String) (s t : RState64) (i : RInst64)
    (h : ∀ a ∈ (rinst64DstSrcs i).2, t.get (ρ a) = s.get a) :
    instVal64 t (renameRInst64 ρ i) = instVal64 s i := by
  cases i <;>
    simp only [renameRInst64, instVal64, rinst64DstSrcs, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq] at h ⊢ <;>
    (try obtain ⟨ha, hb⟩ := h) <;>
    simp only [*]

/-! ## 2. Liveness and the checker -/

/-- The names live before `i`, given the names `L` live after it: its sources, and the
    names of `L` other than its destination. -/
def liveBefore (i : RInst64) (L : List String) : List String :=
  (rinst64DstSrcs i).2.foldr List.insert (L.filter (· != (rinst64DstSrcs i).1))

theorem mem_liveBefore (i : RInst64) (L : List String) (x : String) :
    x ∈ liveBefore i L ↔ x ∈ (rinst64DstSrcs i).2 ∨ (x ∈ L ∧ x ≠ (rinst64DstSrcs i).1) := by
  unfold liveBefore
  induction (rinst64DstSrcs i).2 with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, List.mem_insert_iff, ih, List.mem_cons, or_assoc]

/-- The check at one instruction, with live-after set `La`: the destination's register
    is a zero register exactly when the destination is, and it is not the register of
    another live name (unless it is a zero register, where the write is discarded). -/
def stepOK (ρ : String → String) (i : RInst64) (La : List String) : Bool :=
  let d := (rinst64DstSrcs i).1
  (isZeroReg (ρ d) == isZeroReg d) &&
    La.all (fun x => x == d || ρ x != ρ d || isZeroReg (ρ d))

/-- The backward pass: `some` of the live-in names when every instruction passes
    `stepOK`, `none` otherwise. -/
def renGo (ρ : String → String) : List RInst64 → List String → Option (List String)
  | [], L => some L
  | i :: is, L =>
    match renGo ρ is L with
    | some La => if stepOK ρ i La then some (liveBefore i La) else none
    | none => none

/-- States `s` (symbolic) and `t` (physical) agree on the names `L`, read through `ρ`. -/
def RelOn (ρ : String → String) (L : List String) (s t : RState64) : Prop :=
  ∀ x ∈ L, t.get (ρ x) = s.get x

/-! ## 3. Correctness -/

/-- One instruction preserves the relation from its live-before to its live-after set. -/
theorem relOn_step (ρ : String → String) (i : RInst64) (La : List String) (s t : RState64)
    (hok : stepOK ρ i La = true) (h : RelOn ρ (liveBefore i La) s t) :
    RelOn ρ La (evalRInst64 s i) (evalRInst64 t (renameRInst64 ρ i)) := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at hok
  obtain ⟨hz, hall⟩ := hok
  have hv : instVal64 t (renameRInst64 ρ i) = instVal64 s i :=
    instVal64_rename ρ s t i fun a ha => h a ((mem_liveBefore i La a).2 (Or.inl ha))
  intro x hx
  rw [evalRInst64_eq_set, evalRInst64_eq_set, dst_rename, hv]
  by_cases hxd : x = (rinst64DstSrcs i).1
  · rw [← hxd] at hz ⊢
    by_cases hzx : x = "zero" ∨ x = "x0"
    · have hzr : ρ x = "zero" ∨ ρ x = "x0" := by
        rw [← isZeroReg_iff, hz, isZeroReg_iff]; exact hzx
      simp [RState64.get, hzx, hzr]
    · have hzr : ¬ (ρ x = "zero" ∨ ρ x = "x0") := by
        rw [← isZeroReg_iff, hz, isZeroReg_iff]; exact hzx
      rw [RState64.get_set_same _ _ _ hzr, RState64.get_set_same _ _ _ hzx]
  · rw [RState64.get_set_other _ _ _ _ hxd,
      ← h x ((mem_liveBefore i La x).2 (Or.inr ⟨hx, hxd⟩))]
    rcases hall x hx with (hx' | hne) | hzd
    · exact absurd hx' hxd
    · exact RState64.get_set_other _ _ _ _ hne
    · have hzd' : ρ (rinst64DstSrcs i).1 = "zero" ∨ ρ (rinst64DstSrcs i).1 = "x0" :=
        (isZeroReg_iff _).1 hzd
      simp [RState64.set, hzd']

/-- **Renaming correctness.** If the checker accepts `b` with live-out names `L` and
    returns live-in names `Lin`, then from states agreeing on `Lin` the original and the
    renamed block end in states agreeing on `L`. -/
theorem runRBlock64_rename (ρ : String → String) (b : List RInst64) (L Lin : List String)
    (hok : renGo ρ b L = some Lin) (s t : RState64) (h : RelOn ρ Lin s t) :
    RelOn ρ L (runRBlock64 s b) (runRBlock64 t (renameRBlock64 ρ b)) := by
  induction b generalizing s t Lin with
  | nil =>
    simp only [renGo, Option.some.injEq] at hok
    subst hok
    exact h
  | cons i is ih =>
    simp only [renGo] at hok
    split at hok
    · rename_i La hLa
      split at hok
      · rename_i hstep
        simp only [Option.some.injEq] at hok
        subst hok
        exact ih La hLa _ _ (relOn_step ρ i La s t hstep h)
      · exact absurd hok (by simp)
    · exact absurd hok (by simp)

/-! ## 4. Association-list renamings and the pulled-back state -/

/-- The renaming given by an association list: the paired register for a key, the name
    itself otherwise. -/
def nameOf (alloc : List (String × String)) (n : String) : String :=
  (alloc.lookup n).getD n

/-- The symbolic state read back from a physical one through `ρ`. -/
def pull (ρ : String → String) (t : RState64) : RState64 := ⟨fun x => t.get (ρ x)⟩

/-- When `ρ` fixes both zero registers, the pulled-back state agrees with the physical
    state on every name. -/
theorem pull_relOn (ρ : String → String) (hz : ρ "zero" = "zero") (hx0 : ρ "x0" = "x0")
    (L : List String) (t : RState64) : RelOn ρ L (pull ρ t) t := by
  intro x _
  by_cases h : x = "zero" ∨ x = "x0"
  · rcases h with h | h <;> subst h <;> simp [hz, hx0]
  · simp [pull, RState64.get, h]

/-! ## 5. The allocator (not proved; its output is checked by `renGo`)

A linear scan over live intervals. A name's interval runs from its first appearance to
its last appearance, or to the end of the block when it is live out; a pinned name
that is read before it is written (an input) starts at 0. Pinned names take their
pinned register. Every other name takes the first register of `pool` that no active
interval holds and whose pinned names' intervals do not meet its own. -/

/-- Every register name an instruction mentions. -/
def instNames (i : RInst64) : List String := (rinst64DstSrcs i).1 :: (rinst64DstSrcs i).2

/-- The index of the last instruction mentioning `n`, or `b.length` when `n` is live out. -/
def intervalEnd (b : List RInst64) (liveOut : List String) (n : String) : Nat :=
  if n ∈ liveOut then b.length
  else (b.zipIdx.foldl (fun acc (i, k) => if n ∈ instNames i then k else acc) 0)

/-- The index of the first instruction mentioning `n`, or 0 when it is read there
    before any write. -/
def intervalStart (b : List RInst64) (n : String) : Nat :=
  match b.zipIdx.find? (fun (i, _) => n ∈ instNames i) with
  | some (i, k) => if n ∈ (rinst64DstSrcs i).2 then 0 else k
  | none => 0

/-- The linear scan. `active` holds `(name, register, interval end)`. -/
def allocLive64 (pins : List (String × String)) (pool : List String) (b : List RInst64)
    (liveOut : List String) : List (String × String) :=
  let pinIv := pins.map fun (n, r) => (n, r, intervalStart b n, intervalEnd b liveOut n)
  let free := fun (active : List (String × String × Nat)) (n : String) (k e : Nat) (r : String) =>
    !(active.any fun (_, r', _) => r' == r) &&
      !(pinIv.any fun (m, r', s', e') => r' == r && m != n && s' ≤ e && k ≤ e')
  let step := fun (st : List (String × String) × List (String × String × Nat))
      (ik : RInst64 × Nat) =>
    let (alloc, active) := st
    let (i, k) := ik
    let active := active.filter (fun (_, _, e) => k ≤ e)
    (instNames i).foldl (fun (st : List (String × String) × List (String × String × Nat)) n =>
      let (alloc, active) := st
      if isZeroReg n || (alloc.lookup n).isSome then st
      else
        let e := intervalEnd b liveOut n
        let r := match pins.lookup n with
          | some r => r
          | none => (pool.find? (free active n k e)).getD ("<spill:" ++ n ++ ">")
        (alloc ++ [(n, r)], active ++ [(n, r, e)])) (alloc, active)
  (b.zipIdx.foldl step ([], [])).1

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64
