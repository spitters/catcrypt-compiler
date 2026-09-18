/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# Address memory with runtime indices, and counted loops

`AddrMemDerived` relates the address machine `runBlockA` to the name-keyed `runBlock` for
blocks whose memory operands resolve, statically, to a cell `(bank, offset)`. An indexed
operand `(b, x, sc)` is admitted there only when `x` holds a known constant. This module
admits an indexed operand whose index is a runtime value, and lifts the refinement to the
counted loops `XLoop` of `LprogControlFlow`.

## Runtime indices

The check carries two abstract states: the `DState` of `AddrMemDerived` (pointer and
constant values, relative to fixed base pointers `P`), and a `TagMap` of `AddrMem` (each
register tagged `r` holds the value register `r` had at block entry, `Q r`). An indexed
operand `(b, x, sc)` is a runtime access (`dynIdx`) when `b` holds `ptr e 0` and `x` is
tagged `r`; it addresses `basePtr e + sc · (Q r)`, the cell `(e, sc · Q r)` of bank `e`
(`useCell Q (e, sc, r)`). Its canonical form is the indexed access with base the bank
name, `loadMemIdx d e x sc` or `storeMemIdx e x sc s`, which the name-keyed machine
evaluates at the same cell because the index register holds the same value on both sides.
A runtime store untracks every cell of its bank (`dropBank`).

The runtime accesses of a block are listed by `idxUsesFrom`; the simulation requires the
cell of each to lie in the cell set `K` at the entry values `Q`. This is the index bound:
for a region of `n` words, `sc = 8` and `Q r < n`.

## Cell sets and regions

The memory relation holds on a cell predicate `K` whose cells are pairwise separated
(`SepOn`). `regionCells R` is the predicate of a list of regions, each a bank name, a
lowest offset and a word count; `sepOn_regionCells` gives `SepOn` when the regions lie in
the address space without wrapping and are pairwise disjoint (`RegionsDisjoint`).

## Loops

`passA` and `runXLoopA` are `XLoop.pass` and `runXLoop` over the address machine.
`XLoop.canonI bank A l` is the loop whose body is the canonical body from the abstract
state `A`. `LoopRel` is the relation carried across passes: equal registers and flags, the
invariants of `A`, and agreement on `K`. When the abstract state after the body entails
`A` (`entailsB`), the relation is preserved by every pass.

## Main definitions

* `dynIdx`, `stepI`, `canonStepI`, `accessOKI`, `disciplinedFromI`, `runI`,
  `canonFromI`, `idxUsesFrom`, `useCell`: the check, the canonical block and the runtime
  accesses.
* `SepOn`, `Region`, `regionCells`, `RegionsDisjoint`: cell sets and their layout.
* `passA`, `runXLoopA`, `XLoop.canonI`, `entailsB`, `LoopRel`, `OptRel`.

## Main results

* `runBlockA_simI_core`: one block under the check, from any abstract state.
* `runBlockA_simI`: from the name-keyed view `jOfD bank P sa`, the address run of `blk`
  and the name-keyed run of `canonFromI bank A [] blk` end with equal registers and flags
  and agree on `K`.
* `sepOn_regionCells`: disjoint regions give separated cells.
* `runXLoopA_sim`: the address loop and the canonical name-keyed loop take the same
  number of passes and end related by `LoopRel`.
* `runXLoopA_boundedLoop`: when the canonical loop terminates as `runBoundedLoop`, the
  address loop terminates in a state related to it.
* `passA_regs`, `passA_zf`: a pass leaves the registers of the body, and sets `ZF` exactly
  when the counter reads `0`.
* `andLoop_transfer`: the loop of the shipped `mpn_and_n_loop_owned`, which reloads three
  array pointers from stack slots into `%r14` and indexes them with `%rsi`, passes the check
  (`andLoop_disciplined`, `andLoop_entails`), has the named-ref loop `andBodyNamed` as its
  canonical form (`andLoop_canon`), and is related by `LoopRel` to it under the invariant
  `andInv n` (index plus counter equals `n`, counter nonzero) and disjoint regions of `n`
  words.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll (runBlock_append runBoundedLoop)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived

/-! ## The check -/

/-- The runtime indexed access of `i`: bank `e`, index register `x`, scale `sc` and the
    entry register `r` whose value `x` holds. `b` must hold `ptr e 0`, `x` must carry a
    tag, and the constant-index cell `A.cellIdx` must be undetermined. -/
def dynIdx (bank : String → Option String) (A : DState) (t : TagMap) (i : JInstr 64) :
    Option (String × String × Nat × String) :=
  match idxOf i with
  | some (b, x, sc) =>
      match A.cellIdx bank b x sc with
      | some _ => none
      | none =>
          match A.get bank b, t.get x with
          | some (.ptr e δ), some r => if δ = 0 then some (e, x, sc, r) else none
          | _, _ => none
  | none => none

/-- `i` is an indexed store. -/
def isStoreIdx : JInstr 64 → Bool
  | .storeMemIdx .. => true
  | _ => false

/-- Untrack every cell of bank `e`. -/
def dropBank (A : DState) (e : String) : DState :=
  { A with cells := A.cells.filter fun p => !decide (p.1.1 = e) }

/-- The transfer function: a runtime store untracks its bank; every other instruction
    steps as `stepD`. -/
def stepI (bank : String → Option String) (A : DState) (t : TagMap) (i : JInstr 64) :
    DState :=
  match dynIdx bank A t i with
  | some (e, _, _, _) => if isStoreIdx i then dropBank A e else stepD bank A i
  | none => stepD bank A i

/-- The indexed access `i` with its base replaced by the bank name `e`. -/
def canonDyn (i : JInstr 64) (e : String) : JInstr 64 :=
  match i with
  | .loadMemIdx d _ x sc => .loadMemIdx d e x sc
  | .storeMemIdx _ x sc s => .storeMemIdx e x sc s
  | i => i

/-- The canonical instruction: `canonDyn` at a runtime access, `canonStep` otherwise. -/
def canonStepI (bank : String → Option String) (A : DState) (t : TagMap) (i : JInstr 64) :
    JInstr 64 :=
  match dynIdx bank A t i with
  | some (e, _, _, _) => canonDyn i e
  | none => canonStep bank A i

/-- The instruction is accepted by `accessOKD` or is a runtime indexed access. -/
def accessOKI (bank : String → Option String) (A : DState) (t : TagMap) (i : JInstr 64) :
    Bool :=
  accessOKD bank A i || (dynIdx bank A t i).isSome

/-- `accessOKI` at every instruction, with both abstract states propagated. -/
def disciplinedFromI (bank : String → Option String) :
    DState → TagMap → List (JInstr 64) → Bool
  | _, _, [] => true
  | A, t, i :: is => accessOKI bank A t i &&
      disciplinedFromI bank (stepI bank A t i) (stepTags t i) is

/-- The abstract states after a block. -/
def runI (bank : String → Option String) :
    DState → TagMap → List (JInstr 64) → DState × TagMap
  | A, t, [] => (A, t)
  | A, t, i :: is => runI bank (stepI bank A t i) (stepTags t i) is

/-- The canonical block. -/
def canonFromI (bank : String → Option String) :
    DState → TagMap → List (JInstr 64) → List (JInstr 64)
  | _, _, [] => []
  | A, t, i :: is => canonStepI bank A t i :: canonFromI bank (stepI bank A t i) (stepTags t i) is

/-- The runtime accesses of a block, as `(bank, scale, entry register of the index)`. -/
def idxUsesFrom (bank : String → Option String) :
    DState → TagMap → List (JInstr 64) → List (String × Nat × String)
  | _, _, [] => []
  | A, t, i :: is =>
      (match dynIdx bank A t i with
       | some (e, _, sc, r) => [(e, sc, r)]
       | none => []) ++ idxUsesFrom bank (stepI bank A t i) (stepTags t i) is

/-- The cell of a runtime access at the entry register values `Q`. -/
def useCell (Q : String → BitVec 64) (u : String × Nat × String) : String × Int :=
  (u.1, ((u.2.1 * (Q u.2.2).toNat : Nat) : Int))

/-- The cells of `K` occupy pairwise disjoint eight-byte ranges. -/
def SepOn (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) : Prop :=
  ∀ k k', K k → K k' → k ≠ k' → Disjoint8 (keyAddr bank P k) (keyAddr bank P k')

/-! ## Lemmas on the check -/

theorem absMem_write_on (bank : String → Option String) (P : String → BitVec 64) (m : AMem)
    (v : BitVec 64) {K : String × Int → Prop} (hsep : SepOn bank P K)
    {k k' : String × Int} (hk : K k) (hk' : K k') :
    absMem bank P (write64 m (keyAddr bank P k) v) k'.1 k'.2 =
      if k' = k then v else absMem bank P m k'.1 k'.2 := by
  by_cases h : k' = k
  · subst h
    simp only [absMem, if_pos]
    exact read64_write64_same m _ v
  · rw [if_neg h]
    exact read64_write64_of_disjoint _ _ _ _ (hsep k k' hk hk' (Ne.symm h))

theorem lookupC_dropBank (t : List ((String × Int) × AVal)) (e : String) (c : String × Int) :
    lookupC (t.filter fun p => !decide (p.1.1 = e)) c =
      if c.1 = e then none else lookupC t c := by
  induction t with
  | nil => simp [lookupC]
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k.1 = e
    · rw [List.filter_cons_of_neg (by simp [hk]), ih]
      by_cases hc : c.1 = e
      · simp [hc]
      · have : c ≠ k := fun h => hc (h ▸ hk)
        simp [hc, lookupC, this]
    · rw [List.filter_cons_of_pos (by simp [hk])]
      simp only [lookupC, ih]
      by_cases hc : c.1 = e
      · have : c ≠ k := fun h => hk (h ▸ hc)
        simp [hc, this]
      · simp [hc]

theorem dynIdx_eq_some {bank : String → Option String} {A : DState} {t : TagMap}
    {i : JInstr 64} {e x : String} {sc : Nat} {r : String}
    (h : dynIdx bank A t i = some (e, x, sc, r)) :
    ∃ b, idxOf i = some (b, x, sc) ∧ A.get bank b = some (.ptr e 0) ∧ t.get x = some r := by
  unfold dynIdx at h
  split at h
  · rename_i b x' sc' hi
    split at h
    · cases h
    · split at h
      · rename_i e' δ r' hb hx
        split at h
        · rename_i hδ
          cases h
          subst hδ
          exact ⟨b, hi, hb, hx⟩
        · cases h
      · cases h
  · cases h

theorem dsts_of_idxOf_store {i : JInstr 64} {b x : String} {sc : Nat}
    (h : idxOf i = some (b, x, sc)) (hs : isStoreIdx i = true) :
    ∃ s, i = .storeMemIdx b x sc s := by
  cases i <;> simp_all [idxOf, isStoreIdx]

theorem eq_load_of_idxOf {i : JInstr 64} {b x : String} {sc : Nat}
    (h : idxOf i = some (b, x, sc)) (hs : isStoreIdx i = false) :
    ∃ d, i = .loadMemIdx d b x sc := by
  cases i <;> simp_all [idxOf, isStoreIdx]

/-- The address of a runtime access is the address of its cell. -/
theorem addr_of_dyn {bank : String → Option String} {P Q : String → BitVec 64} {A : DState}
    {t : TagMap} {R : String → BitVec 64} (hinv : RegInvD bank P A R) (htag : TagInv t Q R)
    {b x e r : String} {sc : Nat} (hb : A.get bank b = some (.ptr e 0))
    (hx : t.get x = some r) :
    R b + BitVec.ofInt 64 ((sc * (R x).toNat : Nat) : Int) =
      keyAddr bank P (useCell Q (e, sc, r)) := by
  rw [hinv b _ hb, htag x r hx]
  simp [AVal.denote, keyAddr, useCell]

/-! ## One instruction -/

/-- The simulation invariant is preserved by one runtime indexed access. -/
theorem step_dyn (bank : String → Option String) (P Q : String → BitVec 64)
    (K : String × Int → Prop) (hsep : SepOn bank P K) (A : DState) (t : TagMap)
    (i : JInstr 64) (e x : String) (sc : Nat) (r : String)
    (hdyn : dynIdx bank A t i = some (e, x, sc, r)) (hK0 : K (useCell Q (e, sc, r)))
    (hA : ∀ k ∈ A.cellKeys, K k) (sa : AState) (js : JState 64)
    (hr : sa.regs = js.regs) (hf : sa.flags = js.flags) (hinv : RegInvD bank P A sa.regs)
    (hcell : CellInvD bank P A sa.mem) (htag : TagInv t Q sa.regs)
    (hK : ∀ k, K k → absMem bank P sa.mem k.1 k.2 = js.mem k.1 k.2) :
    (evalInstrA sa i).regs = (evalInstr js (canonStepI bank A t i)).regs ∧
      (evalInstrA sa i).flags = (evalInstr js (canonStepI bank A t i)).flags ∧
      (∀ k, K k → absMem bank P (evalInstrA sa i).mem k.1 k.2 =
        (evalInstr js (canonStepI bank A t i)).mem k.1 k.2) ∧
      RegInvD bank P (stepI bank A t i) (evalInstrA sa i).regs ∧
      CellInvD bank P (stepI bank A t i) (evalInstrA sa i).mem ∧
      (∀ k ∈ (stepI bank A t i).cellKeys, K k) := by
  obtain ⟨b, hix, hb, hx⟩ := dynIdx_eq_some hdyn
  have ha := addr_of_dyn (sc := sc) hinv htag hb hx
  have hxv : js.regs x = Q r := hr ▸ htag x r hx
  unfold canonStepI stepI
  rw [hdyn]
  simp only
  cases hst : isStoreIdx i with
  | false =>
    obtain ⟨d, rfl⟩ := eq_load_of_idxOf hix hst
    simp only [Bool.false_eq_true, if_false]
    have hval : read64 sa.mem (sa.regs b + BitVec.ofInt 64 ((sc * (sa.regs x).toNat : Nat) : Int))
        = js.mem e ((sc * (js.regs x).toNat : Nat) : Int) := by
      have h := hK _ hK0
      simp only [absMem, useCell] at h
      rw [ha, hxv]
      exact h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr] at hval
      simp only [Nat.cast_mul] at hval
      simp only [evalInstrA, canonDyn, evalInstr, JState.setReg, JState.loadIdx, JState.load,
        JState.get, AState.view, x86_MOV, hr, hval]
    · simp only [evalInstrA, canonDyn, evalInstr, JState.setReg, AState.view, hf]
    · intro k hk
      exact hK k hk
    · intro r' v hv
      have hs : stepD bank A (.loadMemIdx d b x sc) = A.setR bank d none := by
        simp only [stepD, DState.loadVal, memCell, idxOf]
        have : A.cellIdx bank b x sc = none := by
          unfold dynIdx at hdyn
          simp only [idxOf] at hdyn
          split at hdyn
          · cases hdyn
          · assumption
        rw [this]; rfl
      rw [hs, DState.get_setR] at hv
      by_cases hrd : r' = d
      · rw [if_pos hrd] at hv; cases hv
      · rw [if_neg hrd] at hv
        simp only [evalInstrA, evalInstr, JState.setReg, if_neg hrd, AState.view]
        exact hinv r' v hv
    · have hs : (stepD bank A (.loadMemIdx d b x sc)).cells = A.cells := by
        simp only [stepD]; rfl
      intro c v hl
      rw [hs] at hl
      exact hcell c v hl
    · have hs : (stepD bank A (.loadMemIdx d b x sc)).cells = A.cells := by
        simp only [stepD]; rfl
      intro c hc
      exact hA c (by simpa [DState.cellKeys, hs] using hc)
  | true =>
    obtain ⟨s, rfl⟩ := dsts_of_idxOf_store hix hst
    simp only [if_true]
    have hsv : s.eval sa.view = s.eval js := by
      cases s <;> simp [JOperand.eval, AState.view, hr]
    have hmem : (evalInstrA sa (.storeMemIdx b x sc s)).mem =
        write64 sa.mem (keyAddr bank P (useCell Q (e, sc, r))) (s.eval js) := by
      simp only [evalInstrA, writeAddr, writeVal, ha, hsv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [evalInstrA, canonDyn, evalInstr, JState.storeIdx, JState.store, AState.view, hr]
    · simp only [evalInstrA, canonDyn, evalInstr, JState.storeIdx, JState.store, AState.view, hf]
    · intro k hk
      rw [hmem, absMem_write_on bank P sa.mem _ hsep hK0 hk]
      simp only [canonDyn, evalInstr, JState.storeIdx, JState.store, JState.get, useCell, hxv,
        x86_MOV]
      by_cases h : k = (e, ((sc * (Q r).toNat : Nat) : Int))
      · subst h; simp
      · have h' : ¬ (k.1 = e ∧ k.2 = (sc : Int) * ((Q r).toNat : Int)) :=
          fun ⟨h1, h2⟩ => h (Prod.ext h1 (by rw [h2]; push_cast; rfl))
        simp only [h, h', if_false]
        exact hK k hk
    · intro r' v hv
      exact hinv r' v hv
    · intro c v hl
      simp only [dropBank] at hl
      rw [lookupC_dropBank] at hl
      split at hl
      · cases hl
      · rename_i hce
        rw [hmem, read64_write64_of_disjoint]
        · exact hcell c v hl
        · refine hsep _ _ hK0 (hA c (mem_cellKeys_of_lookupC hl)) ?_
          intro h
          exact hce (by rw [← h]; rfl)
    · intro c hc
      simp only [dropBank, DState.cellKeys, List.mem_map, List.mem_filter] at hc
      obtain ⟨p, ⟨hp, -⟩, rfl⟩ := hc
      exact hA _ (List.mem_map_of_mem hp)

/-- The simulation invariant is preserved by one instruction that `accessOKD` accepts, when
    the cells its canonical form reads and writes lie in `K`. -/
theorem step_static (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) (hsep : SepOn bank P K) (A : DState) (t : TagMap)
    (i : JInstr 64) (hdyn : dynIdx bank A t i = none) (hok : accessOKD bank A i = true)
    (hRK : ∀ k, readKey (canonStep bank A i) = some k → K k)
    (hWK : ∀ k, writeKey (canonStep bank A i) = some k → K k)
    (hA : ∀ k ∈ A.cellKeys, K k) (sa : AState) (js : JState 64)
    (hr : sa.regs = js.regs) (hf : sa.flags = js.flags) (hinv : RegInvD bank P A sa.regs)
    (hcell : CellInvD bank P A sa.mem)
    (hK : ∀ k, K k → absMem bank P sa.mem k.1 k.2 = js.mem k.1 k.2) :
    (evalInstrA sa i).regs = (evalInstr js (canonStepI bank A t i)).regs ∧
      (evalInstrA sa i).flags = (evalInstr js (canonStepI bank A t i)).flags ∧
      (∀ k, K k → absMem bank P (evalInstrA sa i).mem k.1 k.2 =
        (evalInstr js (canonStepI bank A t i)).mem k.1 k.2) ∧
      RegInvD bank P (stepI bank A t i) (evalInstrA sa i).regs ∧
      CellInvD bank P (stepI bank A t i) (evalInstrA sa i).mem ∧
      (∀ k ∈ (stepI bank A t i).cellKeys, K k) := by
  have hc : canonStepI bank A t i = canonStep bank A i := by
    simp only [canonStepI, hdyn]
  have hs : stepI bank A t i = stepD bank A i := by
    simp only [stepI, hdyn]
  rw [hc, hs]
  obtain ⟨hform, h1, h2, h4⟩ := evalInstrA_canonStep bank P A sa i hok hinv
  have hread : ∀ k, readKey (canonStep bank A i) = some k →
      (jOfD bank P sa).mem k.1 k.2 = js.mem k.1 k.2 := fun k hk => hK k (hRK k hk)
  obtain ⟨hcr, hcf, hcw⟩ := evalInstr_congr (jOfD bank P sa) js _ hform hr hf hread
  refine ⟨h1.trans hcr, h2.trans hcf, ?_, regInvD_step bank P A sa i hok hinv hcell,
    cellInvD_step bank P A sa i hok hinv hcell ?_, ?_⟩
  · intro k' hk'
    rw [evalInstr_mem js _ hform, h4]
    cases hwi : writeKey (canonStep bank A i) with
    | none => exact hK k' hk'
    | some k =>
      simp only
      rw [← hcw, absMem_write_on bank P sa.mem _ hsep (hWK k hwi) hk']
      by_cases h : k' = k
      · subst h
        simp
      · have h' : ¬ (k'.1 = k.1 ∧ k'.2 = k.2) := fun ⟨e1, e2⟩ => h (Prod.ext e1 e2)
        rw [if_neg h, if_neg h']
        exact hK k' hk'
  · intro k hk c hc hck
    exact hsep k c (hWK k hk) (hA c hc) (Ne.symm hck)
  · intro c hc
    rcases cellKeys_stepD bank P A sa i hok hinv c hc with h | h
    · exact hA c h
    · exact hWK c h

theorem accessOKD_of_accessOKI {bank : String → Option String} {A : DState} {t : TagMap}
    {i : JInstr 64} (h : accessOKI bank A t i = true) (hdyn : dynIdx bank A t i = none) :
    accessOKD bank A i = true := by
  simpa [accessOKI, hdyn] using h

theorem mem_footprint_cons_read {i : JInstr 64} {is : List (JInstr 64)} {k : String × Int}
    (h : readKey i = some k) : k ∈ footprint (i :: is) := by
  simp [footprint, h]

theorem mem_footprint_cons_write {i : JInstr 64} {is : List (JInstr 64)} {k : String × Int}
    (h : writeKey i = some k) : k ∈ footprint (i :: is) := by
  simp only [footprint, List.mem_append]
  exact Or.inr (mem_writeKeys_cons.2 (Or.inl h))

theorem mem_footprint_cons_tail {i : JInstr 64} {is : List (JInstr 64)} {k : String × Int}
    (h : k ∈ footprint is) : k ∈ footprint (i :: is) := by
  simp only [footprint, List.mem_append] at h ⊢
  rcases h with h | h
  · left
    simp only [List.filterMap_cons]
    split <;> simp [h]
  · exact Or.inr (mem_writeKeys_cons.2 (Or.inr h))

/-! ## The block simulation -/

/-- **Simulation from an abstract state.** Under the check from `(A, t)`, with the
    invariants of `A` at the base pointers `P` and the tags `t` at the entry values `Q`,
    let `K` be a separated cell set containing the cells `A` tracks, the cells of the
    canonical footprint and the cell of every runtime access. Then the address run of `blk`
    and the name-keyed run of the canonical block end with equal registers and flags and
    agree on `K`, and the invariants of `runI bank A t blk` hold at the end. -/
theorem runBlockA_simI_core (bank : String → Option String) (P Q : String → BitVec 64)
    (K : String × Int → Prop) (hsep : SepOn bank P K) :
    ∀ (blk : List (JInstr 64)) (A : DState) (t : TagMap) (sa : AState) (js : JState 64),
      disciplinedFromI bank A t blk = true →
      (∀ k ∈ footprint (canonFromI bank A t blk), K k) →
      (∀ u ∈ idxUsesFrom bank A t blk, K (useCell Q u)) →
      (∀ k ∈ A.cellKeys, K k) →
      sa.regs = js.regs → sa.flags = js.flags →
      RegInvD bank P A sa.regs → CellInvD bank P A sa.mem → TagInv t Q sa.regs →
      (∀ k, K k → absMem bank P sa.mem k.1 k.2 = js.mem k.1 k.2) →
      (runBlockA sa blk).regs = (runBlock js (canonFromI bank A t blk)).regs ∧
        (runBlockA sa blk).flags = (runBlock js (canonFromI bank A t blk)).flags ∧
        (∀ k, K k → absMem bank P (runBlockA sa blk).mem k.1 k.2 =
          (runBlock js (canonFromI bank A t blk)).mem k.1 k.2) ∧
        RegInvD bank P (runI bank A t blk).1 (runBlockA sa blk).regs ∧
        CellInvD bank P (runI bank A t blk).1 (runBlockA sa blk).mem ∧
        (∀ k ∈ (runI bank A t blk).1.cellKeys, K k) := by
  intro blk
  induction blk with
  | nil =>
    intro A t sa js _ _ _ hA hr hf hinv hcell _ hK
    exact ⟨hr, hf, hK, hinv, hcell, hA⟩
  | cons i is ih =>
    intro A t sa js hd hfp hu hA hr hf hinv hcell htag hK
    simp only [disciplinedFromI, Bool.and_eq_true] at hd
    obtain ⟨hok, hd⟩ := hd
    simp only [canonFromI] at hfp
    simp only [idxUsesFrom, List.mem_append] at hu
    have hfp' : ∀ k ∈ footprint (canonFromI bank (stepI bank A t i) (stepTags t i) is), K k :=
      fun k hk => hfp k (mem_footprint_cons_tail hk)
    have hu' : ∀ u ∈ idxUsesFrom bank (stepI bank A t i) (stepTags t i) is, K (useCell Q u) :=
      fun u hu' => hu u (Or.inr hu')
    have htag' : TagInv (stepTags t i) Q (evalInstrA sa i).regs :=
      tagInv_step t Q sa.view i htag
    have hstep : (evalInstrA sa i).regs = (evalInstr js (canonStepI bank A t i)).regs ∧
        (evalInstrA sa i).flags = (evalInstr js (canonStepI bank A t i)).flags ∧
        (∀ k, K k → absMem bank P (evalInstrA sa i).mem k.1 k.2 =
          (evalInstr js (canonStepI bank A t i)).mem k.1 k.2) ∧
        RegInvD bank P (stepI bank A t i) (evalInstrA sa i).regs ∧
        CellInvD bank P (stepI bank A t i) (evalInstrA sa i).mem ∧
        (∀ k ∈ (stepI bank A t i).cellKeys, K k) := by
      cases hdyn : dynIdx bank A t i with
      | some v =>
        obtain ⟨e, x, sc, r⟩ := v
        have hK0 : K (useCell Q (e, sc, r)) := hu _ (Or.inl (by simp [hdyn]))
        exact step_dyn bank P Q K hsep A t i e x sc r hdyn hK0 hA sa js hr hf hinv hcell htag hK
      | none =>
        have hc : canonStepI bank A t i = canonStep bank A i := by
          simp only [canonStepI, hdyn]
        exact step_static bank P K hsep A t i hdyn (accessOKD_of_accessOKI hok hdyn)
          (fun k hk => hfp k (mem_footprint_cons_read (hc ▸ hk)))
          (fun k hk => hfp k (mem_footprint_cons_write (hc ▸ hk))) hA sa js hr hf hinv hcell hK
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hstep
    simp only [runBlockA_cons, canonFromI, runBlock_cons, runI]
    exact ih _ _ _ _ hd hfp' hu' h6 h1 h2 h4 h5 htag' h3

/-- **Simulation from the name-keyed view.** Under the check from `(A, [])`, with the
    invariants of `A` at `P`, for a separated cell set `K` containing the tracked cells, the
    canonical footprint and the cells of the runtime accesses at the entry registers, the
    address run of `blk` and the name-keyed run of the canonical block from
    `jOfD bank P sa` end with equal registers and flags and agree on `K`. -/
theorem runBlockA_simI (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) (hsep : SepOn bank P K) (A : DState) (blk : List (JInstr 64))
    (hd : disciplinedFromI bank A [] blk = true)
    (hfp : ∀ k ∈ footprint (canonFromI bank A [] blk), K k)
    (hA : ∀ k ∈ A.cellKeys, K k) (sa : AState)
    (hu : ∀ u ∈ idxUsesFrom bank A [] blk, K (useCell sa.regs u))
    (hinv : RegInvD bank P A sa.regs) (hcell : CellInvD bank P A sa.mem) :
    (runBlockA sa blk).regs = (runBlock (jOfD bank P sa) (canonFromI bank A [] blk)).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOfD bank P sa) (canonFromI bank A [] blk)).flags ∧
      ∀ k, K k → absMem bank P (runBlockA sa blk).mem k.1 k.2 =
        (runBlock (jOfD bank P sa) (canonFromI bank A [] blk)).mem k.1 k.2 := by
  obtain ⟨h1, h2, h3, -⟩ := runBlockA_simI_core bank P sa.regs K hsep blk A [] sa (jOfD bank P sa) hd hfp hu hA
    rfl rfl hinv hcell (tagInv_nil sa.regs) (fun _ _ => rfl)
  exact ⟨h1, h2, h3⟩

/-! ## Regions -/

/-- A region: the words of bank `name` at the offsets `lo + 8·j` for `j < cnt`. -/
structure Region where
  /-- The bank. -/
  name : String
  /-- The offset of the lowest word. -/
  lo : Int
  /-- The number of words. -/
  cnt : Nat
  deriving DecidableEq, Repr

/-- The cells of a list of regions. -/
def regionCells (R : List Region) (k : String × Int) : Prop :=
  ∃ g ∈ R, k.1 = g.name ∧ ∃ j < g.cnt, k.2 = g.lo + 8 * (j : Int)

/-- The address of the lowest word of a region, as a natural number. -/
def regionLow (bank : String → Option String) (P : String → BitVec 64) (g : Region) : Nat :=
  (basePtr bank P g.name + BitVec.ofInt 64 g.lo).toNat

/-- Every region lies below `2^64` from its lowest word, and distinct regions have distinct
    banks and disjoint address ranges. -/
def RegionsDisjoint (bank : String → Option String) (P : String → BitVec 64)
    (R : List Region) : Prop :=
  (∀ g ∈ R, regionLow bank P g + 8 * g.cnt ≤ 2 ^ 64) ∧
  ∀ g ∈ R, ∀ h ∈ R, g ≠ h → g.name ≠ h.name ∧
    (regionLow bank P g + 8 * g.cnt ≤ regionLow bank P h ∨
      regionLow bank P h + 8 * h.cnt ≤ regionLow bank P g)

/-- The address of word `j` of a region that does not wrap is its lowest address plus
    `8·j`. -/
theorem keyAddr_region_toNat (bank : String → Option String) (P : String → BitVec 64)
    (g : Region) (j : Nat) (hj : j < g.cnt) (hw : regionLow bank P g + 8 * g.cnt ≤ 2 ^ 64) :
    (keyAddr bank P (g.name, g.lo + 8 * (j : Int))).toNat = regionLow bank P g + 8 * j := by
  have e : keyAddr bank P (g.name, g.lo + 8 * (j : Int)) =
      (basePtr bank P g.name + BitVec.ofInt 64 g.lo) + BitVec.ofNat 64 (8 * j) := by
    simp only [keyAddr, BitVec.ofInt_add, BitVec.add_assoc]
    congr 2
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold regionLow at hw ⊢
  rw [Nat.mod_eq_of_lt (a := 8 * j) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem disjoint8_of_toNat (a b : BitVec 64) (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat)
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hb : b.toNat + 8 ≤ 2 ^ 64) : Disjoint8 a b := by
  simp only [Disjoint8, BitVec.toNat_sub]
  omega

/-- **Disjoint regions give separated cells.** -/
theorem sepOn_regionCells (bank : String → Option String) (P : String → BitVec 64)
    (R : List Region) (hR : RegionsDisjoint bank P R) : SepOn bank P (regionCells R) := by
  rintro ⟨a, o⟩ ⟨a', o'⟩ ⟨g, hg, ha, j, hj, ho⟩ ⟨h, hh, ha', j', hj', ho'⟩ hne
  simp only at ha ho ha' ho'
  subst ha ho ha' ho'
  have hwg := hR.1 g hg
  have hwh := hR.1 h hh
  apply disjoint8_of_toNat
  · rw [keyAddr_region_toNat bank P g j hj hwg, keyAddr_region_toNat bank P h j' hj' hwh]
    by_cases hgh : g = h
    · subst hgh
      have : j ≠ j' := fun e => hne (by rw [e])
      omega
    · rcases (hR.2 g hg h hh hgh).2 with hd | hd <;> omega
  · rw [keyAddr_region_toNat bank P g j hj hwg]; omega
  · rw [keyAddr_region_toNat bank P h j' hj' hwh]; omega

/-! ## Loops -/

/-- One pass of a counted loop over address memory: the body followed by the compare. -/
def passA (l : XLoop 64) (sa : AState) : AState :=
  runBlockA sa (l.body ++ [l.cmpInstr])

/-- `runXLoop` over address memory: run a pass; if `ZF` is then set, fall through with that
    state, otherwise take the back-edge. -/
def runXLoopA (fuel : Nat) (sa : AState) (l : XLoop 64) : Option AState :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if (passA l sa).view.flagB (·.zf) then some (passA l sa) else runXLoopA f (passA l sa) l

/-- The loop with the canonical body from the abstract state `A` and the empty tag map. -/
def canonLoop (bank : String → Option String) (A : DState) (l : XLoop 64) : XLoop 64 :=
  { l with body := canonFromI bank A [] l.body }

/-- Every register value and cell value that `Y` records, `X` records too; `Y` tracks no
    register by its entry value. -/
def entailsB (bank : String → Option String) (X Y : DState) : Bool :=
  !Y.entry &&
    Y.regs.all (fun p => match p.2 with
      | none => true
      | some v => decide (X.get bank p.1 = some v)) &&
    Y.cells.all (fun p => decide (lookupC X.cells p.1 = some p.2))

/-- The relation carried across passes: equal registers and flags, the invariants of `A`,
    the tracked cells inside `K`, and agreement on `K`. -/
def LoopRel (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) (A : DState) (sa : AState) (js : JState 64) : Prop :=
  sa.regs = js.regs ∧ sa.flags = js.flags ∧ RegInvD bank P A sa.regs ∧
    CellInvD bank P A sa.mem ∧ (∀ k ∈ A.cellKeys, K k) ∧
    ∀ k, K k → absMem bank P sa.mem k.1 k.2 = js.mem k.1 k.2

/-- Two optional results are both absent, or both present and related. -/
def OptRel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- An address state is related to its name-keyed view at `P` when the invariants of `A`
    hold and the tracked cells lie in `K`. -/
theorem loopRel_jOfD (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) (A : DState) (sa : AState) (hinv : RegInvD bank P A sa.regs)
    (hcell : CellInvD bank P A sa.mem) (hA : ∀ k ∈ A.cellKeys, K k) :
    LoopRel bank P K A sa (jOfD bank P sa) :=
  ⟨rfl, rfl, hinv, hcell, hA, fun _ _ => rfl⟩

theorem lookupR_mem {t : List (String × Option AVal)} {r : String} {v : Option AVal}
    (h : lookupR t r = some v) : (r, v) ∈ t := by
  induction t with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨k, w⟩ := p
    simp only [lookupR] at h
    by_cases hr : r = k
    · rw [if_pos hr] at h
      cases h
      subst hr
      exact List.mem_cons_self
    · rw [if_neg hr] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookupC_mem {t : List ((String × Int) × AVal)} {c : String × Int} {v : AVal}
    (h : lookupC t c = some v) : (c, v) ∈ t := by
  induction t with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨k, w⟩ := p
    simp only [lookupC] at h
    by_cases hc : c = k
    · rw [if_pos hc] at h
      cases h
      subst hc
      exact List.mem_cons_self
    · rw [if_neg hc] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem entailsB_regInv {bank : String → Option String} {P : String → BitVec 64}
    {X Y : DState} {R : String → BitVec 64} (he : entailsB bank X Y = true)
    (h : RegInvD bank P X R) : RegInvD bank P Y R := by
  simp only [entailsB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.all_eq_true] at he
  obtain ⟨⟨hent, hregs⟩, -⟩ := he
  intro r v hv
  unfold DState.get at hv
  cases hl : lookupR Y.regs r with
  | none => rw [hl, hent] at hv; cases hv
  | some w =>
    rw [hl] at hv
    simp only at hv
    subst hv
    have := hregs _ (lookupR_mem hl)
    simp only [decide_eq_true_eq] at this
    exact h r v this

theorem entailsB_cellInv {bank : String → Option String} {P : String → BitVec 64}
    {X Y : DState} {m : AMem} (he : entailsB bank X Y = true)
    (h : CellInvD bank P X m) : CellInvD bank P Y m := by
  simp only [entailsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at he
  intro c v hv
  exact h c v (he.2 _ (lookupC_mem hv))

theorem entailsB_cellKeys {bank : String → Option String} {X Y : DState}
    (he : entailsB bank X Y = true) {c : String × Int} (hc : c ∈ Y.cellKeys) :
    c ∈ X.cellKeys := by
  simp only [entailsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at he
  simp only [DState.cellKeys, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact mem_cellKeys_of_lookupC (he.2 p hp)

/-- The compare of a loop over address memory leaves registers and memory unchanged and sets
    the flags that the name-keyed compare sets. -/
theorem evalInstrA_cmp (sa : AState) (js : JState 64) (c : String) (hr : sa.regs = js.regs) :
    (evalInstrA sa (.cmp c (.imm 0))).regs = sa.regs ∧
      (evalInstrA sa (.cmp c (.imm 0))).flags = (evalInstr js (.cmp c (.imm 0))).flags ∧
      (evalInstrA sa (.cmp c (.imm 0))).mem = sa.mem ∧
      (evalInstr js (.cmp c (.imm 0))).regs = js.regs ∧
      (evalInstr js (.cmp c (.imm 0))).mem = js.mem := by
  simp [evalInstrA, evalInstr, JState.writeB5, writeAddr, AState.view, hr]

/-- **One pass.** Under the check of the body from `(A, [])`, when the abstract state after
    the body entails `A`, a pass of the address loop and a pass of the canonical loop
    preserve `LoopRel`, provided the runtime accesses of the pass fall in `K`. -/
theorem passA_sim (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) (hsep : SepOn bank P K) (A : DState) (l : XLoop 64)
    (hd : disciplinedFromI bank A [] l.body = true)
    (hfp : ∀ k ∈ footprint (canonFromI bank A [] l.body), K k)
    (hfix : entailsB bank (runI bank A [] l.body).1 A = true)
    (sa : AState) (js : JState 64)
    (hu : ∀ u ∈ idxUsesFrom bank A [] l.body, K (useCell sa.regs u))
    (hrel : LoopRel bank P K A sa js) :
    LoopRel bank P K A (passA l sa) ((canonLoop bank A l).pass js) := by
  obtain ⟨hr, hf, hinv, hcell, hA, hK⟩ := hrel
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := runBlockA_simI_core bank P sa.regs K hsep l.body A [] sa
    js hd hfp hu hA hr hf hinv hcell (tagInv_nil sa.regs) hK
  have hp : (canonLoop bank A l).pass js =
      evalInstr (runBlock js (canonFromI bank A [] l.body)) (.cmp l.ctr (.imm 0)) := by
    simp only [XLoop.pass, canonLoop, XLoop.cmpInstr, runBlock_append, runBlock_cons,
      runBlock_nil]
  have hpa : passA l sa = evalInstrA (runBlockA sa l.body) (.cmp l.ctr (.imm 0)) := by
    simp only [passA, XLoop.cmpInstr, runBlockA_append, runBlockA_cons, runBlockA_nil]
  rw [hp, hpa]
  obtain ⟨c1, c2, c3, c4, c5⟩ := evalInstrA_cmp (runBlockA sa l.body)
    (runBlock js (canonFromI bank A [] l.body)) l.ctr h1
  refine ⟨?_, c2, ?_, ?_, ?_, ?_⟩
  · rw [c1, c4, h1]
  · rw [c1]; exact entailsB_regInv hfix h4
  · rw [c3]; exact entailsB_cellInv hfix h5
  · intro k hk; exact h6 k (entailsB_cellKeys hfix hk)
  · intro k hk; rw [c3, c5]; exact h3 k hk

/-- **The loop lift.** Let the body pass the check from `(A, [])` with a canonical footprint
    in `K`, and let the abstract state after the body entail `A`. Let `Inv` be a predicate on
    address states under which the runtime accesses of a pass fall in `K`, preserved by every
    pass after which the loop continues. Then from related states satisfying `Inv`, the
    address loop and the canonical name-keyed loop both run out of fuel, or both exit, in
    states related by `LoopRel`. -/
theorem runXLoopA_sim (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) (hsep : SepOn bank P K) (A : DState) (l : XLoop 64)
    (hd : disciplinedFromI bank A [] l.body = true)
    (hfp : ∀ k ∈ footprint (canonFromI bank A [] l.body), K k)
    (hfix : entailsB bank (runI bank A [] l.body).1 A = true)
    (Inv : AState → Prop)
    (hidx : ∀ sa, Inv sa → ∀ u ∈ idxUsesFrom bank A [] l.body, K (useCell sa.regs u))
    (hinv : ∀ sa, Inv sa → (passA l sa).view.flagB (·.zf) = false → Inv (passA l sa)) :
    ∀ (fuel : Nat) (sa : AState) (js : JState 64), Inv sa → LoopRel bank P K A sa js →
      OptRel (LoopRel bank P K A) (runXLoopA fuel sa l) (runXLoop fuel js (canonLoop bank A l)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; trivial
  | succ f ih =>
    intro sa js hI hrel
    have hpass := passA_sim bank P K hsep A l hd hfp hfix sa js (hidx sa hI) hrel
    have hz : (passA l sa).view.flagB (·.zf) =
        ((canonLoop bank A l).pass js).flagB (·.zf) := by
      simp only [JState.flagB, AState.view, hpass.2.1]
    simp only [runXLoopA, runXLoop]
    rw [← hz]
    cases hzf : (passA l sa).view.flagB (·.zf) with
    | true => exact hpass
    | false => exact ih _ _ (hinv sa hI hzf) hpass

/-- **Termination through the bounded loop.** Under the hypotheses of `runXLoopA_sim`, when
    the canonical body decrements the counter register by one and the counter of the
    name-keyed state holds `n` with `1 ≤ n < 2^64`, the address loop with fuel at least `n`
    exits in a state related to `runBoundedLoop js n` of the canonical pass. -/
theorem runXLoopA_boundedLoop (bank : String → Option String) (P : String → BitVec 64)
    (K : String × Int → Prop) (hsep : SepOn bank P K) (A : DState) (l : XLoop 64)
    (hd : disciplinedFromI bank A [] l.body = true)
    (hfp : ∀ k ∈ footprint (canonFromI bank A [] l.body), K k)
    (hfix : entailsB bank (runI bank A [] l.body).1 A = true)
    (Inv : AState → Prop)
    (hidx : ∀ sa, Inv sa → ∀ u ∈ idxUsesFrom bank A [] l.body, K (useCell sa.regs u))
    (hinv : ∀ sa, Inv sa → (passA l sa).view.flagB (·.zf) = false → Inv (passA l sa))
    (hdec : ∀ s : JState 64,
      (runBlock s (canonLoop bank A l).body).get l.ctr = s.get l.ctr - 1)
    (n fuel : Nat) (sa : AState) (js : JState 64) (hI : Inv sa)
    (hrel : LoopRel bank P K A sa js) (hn : 1 ≤ n) (hlt : n < 2 ^ 64)
    (hctr : js.get l.ctr = BitVec.ofNat 64 n) (hfuel : n ≤ fuel) :
    ∃ sa', runXLoopA fuel sa l = some sa' ∧
      LoopRel bank P K A sa'
        (runBoundedLoop js n ((canonLoop bank A l).body ++ [(canonLoop bank A l).cmpInstr])) := by
  have hsim := runXLoopA_sim bank P K hsep A l hd hfp hfix Inv hidx hinv fuel sa js hI hrel
  obtain ⟨hb, -⟩ := looped_eq_boundedLoop (fun _ => True) (canonLoop bank A l)
    (fun s _ => ⟨trivial, hdec s⟩) n fuel js trivial hn hlt hctr hfuel
  rw [hb] at hsim
  cases hA : runXLoopA fuel sa l with
  | none => rw [hA] at hsim; exact hsim.elim
  | some sa' => rw [hA] at hsim; exact ⟨sa', rfl, hsim⟩

/-! ## Registers and `ZF` of a pass -/

/-- A register that no instruction of the block may write keeps its value. -/
theorem runBlockA_regs_frame (sa : AState) (blk : List (JInstr 64)) (r : String)
    (h : ∀ i ∈ blk, r ∉ dsts i) : (runBlockA sa blk).regs r = sa.regs r := by
  induction blk generalizing sa with
  | nil => rfl
  | cons i is ih =>
    rw [runBlockA_cons, ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact evalInstr_regs_of_not_mem_dsts sa.view i r (h i List.mem_cons_self)

/-- A pass leaves the registers the body leaves. -/
theorem passA_regs (l : XLoop 64) (sa : AState) :
    (passA l sa).regs = (runBlockA sa l.body).regs := by
  simp only [passA, XLoop.cmpInstr, runBlockA_append, runBlockA_cons, runBlockA_nil]
  exact (evalInstrA_cmp _ (runBlockA sa l.body).view l.ctr rfl).1

/-- After a pass, `ZF` is set exactly when the counter register reads `0`. -/
theorem passA_zf (l : XLoop 64) (sa : AState) :
    (passA l sa).view.flagB (·.zf) = decide ((runBlockA sa l.body).regs l.ctr = 0) := by
  simp only [passA, XLoop.cmpInstr, runBlockA_append, runBlockA_cons, runBlockA_nil,
    evalInstrA, AState.view, evalInstr, JState.writeB5, JState.flagB, x86_CMP, x86_SUB,
    ZF_of_word, JOperand.eval, JState.get, Option.getD_some]
  simp [BitVec.toNat_eq]

/-! ## The `mpn_and_n` trip

The loop of `crates/catcrypt-mpn/asm/mpn_and_n_loop_owned.s`: the label
`.Lmpn_and_n_loop_owned_4`, the counter `%rdi`, and the fifteen instructions of a trip before
`cmpq $0, %rdi`. Each trip reloads the pointers of `ap`, `bp` and `rp` from the stack slots
`48(%rsp)`, `-8(%rsp)` and `56(%rsp)` into `%r14` and accesses `(%r14, %rsi, 8)` with the
runtime index `%rsi`, a copy of `%rax`. Every instruction of the trip has a `JInstr`
constructor. -/

/-- The banks of the loop: the arrays `ap`, `bp`, `rp`, based at the function-entry values of
    `%rsi`, `%rdx`, `%rdi`, and the stack, based at `%rsp`. -/
def andBank (b : String) : Option String :=
  if b = "ap" then some "%rsi"
  else if b = "bp" then some "%rdx"
  else if b = "rp" then some "%rdi"
  else if b = "%rsp" then some "%rsp"
  else none

/-- The loop of `mpn_and_n_loop_owned`. -/
def andLoop : XLoop 64 where
  top := 4
  ctr := "%rdi"
  body :=
    [ .mov "%rsi" (.reg "%rax"),
      .loadMem "%r14" "%rsp" 48,
      .loadMemIdx "%rbp" "%r14" "%rsi" 8,
      .loadMem "%r14" "%rsp" (-8),
      .loadMemIdx "%r8" "%r14" "%rsi" 8,
      .mov "%r9" (.reg "%rbp"),
      .and_ "%r9" (.reg "%r8"),
      .mov "%rbp" (.reg "%r9"),
      .loadMem "%r14" "%rsp" 56,
      .storeMemIdx "%r14" "%rsi" 8 (.reg "%rbp"),
      .mov "%rbx" (.reg "%rbx"),
      .add "%rax" (.imm 1),
      .sub "%rdi" (.imm 1),
      .cmp "%rdi" (.reg "%rcx"),
      .cmp "%rdi" (.reg "%rdx") ]

/-- The abstract state at the loop head: `%rsp` holds the stack base, and the three stack
    slots hold the bases of `rp`, `ap` and `bp`. -/
def andA : DState :=
  ⟨false, [("%rsp", some (.ptr "%rsp" 0))],
    [(("%rsp", 56), .ptr "rp" 0), (("%rsp", 48), .ptr "ap" 0), (("%rsp", -8), .ptr "bp" 0)]⟩

/-- The regions: `n` words of each array, and the nine stack words from `-8(%rsp)`. -/
def andRegions (n : Nat) : List Region :=
  [⟨"ap", 0, n⟩, ⟨"bp", 0, n⟩, ⟨"rp", 0, n⟩, ⟨"%rsp", -8, 9⟩]

/-- The canonical body: the named-ref trip, each array access through its bank. -/
def andBodyNamed : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rax"),
    .loadMem "%r14" "%rsp" 48,
    .loadMemIdx "%rbp" "ap" "%rsi" 8,
    .loadMem "%r14" "%rsp" (-8),
    .loadMemIdx "%r8" "bp" "%rsi" 8,
    .mov "%r9" (.reg "%rbp"),
    .and_ "%r9" (.reg "%r8"),
    .mov "%rbp" (.reg "%r9"),
    .loadMem "%r14" "%rsp" 56,
    .storeMemIdx "rp" "%rsi" 8 (.reg "%rbp"),
    .mov "%rbx" (.reg "%rbx"),
    .add "%rax" (.imm 1),
    .sub "%rdi" (.imm 1),
    .cmp "%rdi" (.reg "%rcx"),
    .cmp "%rdi" (.reg "%rdx") ]

theorem andLoop_disciplined : disciplinedFromI andBank andA [] andLoop.body = true := by
  decide +kernel

theorem andLoop_entails : entailsB andBank (runI andBank andA [] andLoop.body).1 andA = true := by
  decide +kernel

theorem andLoop_uses :
    idxUsesFrom andBank andA [] andLoop.body = [("ap", 8, "%rax"), ("bp", 8, "%rax"),
      ("rp", 8, "%rax")] := by
  decide +kernel

theorem andLoop_canon : canonFromI andBank andA [] andLoop.body = andBodyNamed := by
  rfl

theorem andLoop_footprint :
    footprint andBodyNamed = [("%rsp", 48), ("%rsp", -8), ("%rsp", 56)] := by
  decide +kernel

/-- The loop invariant: the index `%rax` and the counter `%rdi` sum to `n`, and the counter
    is nonzero. -/
def andInv (n : Nat) (sa : AState) : Prop :=
  (sa.regs "%rax").toNat + (sa.regs "%rdi").toNat = n ∧ sa.regs "%rdi" ≠ 0

theorem andBody_rax (sa : AState) :
    (runBlockA sa andLoop.body).regs "%rax" = sa.regs "%rax" + 1 := by
  have e : andLoop.body = andLoop.body.take 11 ++ .add "%rax" (.imm 1) :: andLoop.body.drop 12 :=
    rfl
  rw [e, runBlockA_append, runBlockA_cons,
    runBlockA_regs_frame _ _ _ (by decide)]
  simp only [evalInstrA, evalInstr, JState.writeB5W, x86_ADD, AState.view, JState.get,
    JOperand.eval, if_true]
  rw [runBlockA_regs_frame _ _ _ (by decide)]
  rfl

theorem andBody_rdi (sa : AState) :
    (runBlockA sa andLoop.body).regs "%rdi" = sa.regs "%rdi" - 1 := by
  have e : andLoop.body = andLoop.body.take 12 ++ .sub "%rdi" (.imm 1) :: andLoop.body.drop 13 :=
    rfl
  rw [e, runBlockA_append, runBlockA_cons,
    runBlockA_regs_frame _ _ _ (by decide)]
  simp only [evalInstrA, evalInstr, JState.writeB5W, x86_SUB, AState.view, JState.get,
    JOperand.eval, if_true]
  rw [runBlockA_regs_frame _ _ _ (by decide)]
  rfl

theorem andLoop_idx (n : Nat) (sa : AState) (hI : andInv n sa) :
    ∀ u ∈ idxUsesFrom andBank andA [] andLoop.body,
      regionCells (andRegions n) (useCell sa.regs u) := by
  obtain ⟨hs, hz⟩ := hI
  have hpos : 0 < (sa.regs "%rdi").toNat := by
    rcases Nat.eq_zero_or_pos (sa.regs "%rdi").toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hz
    · exact h
  have hlt : (sa.regs "%rax").toNat < n := by omega
  rw [andLoop_uses]
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨⟨"ap", 0, n⟩, by simp [andRegions], rfl, _, hlt, by simp [useCell]⟩
  · exact ⟨⟨"bp", 0, n⟩, by simp [andRegions], rfl, _, hlt, by simp [useCell]⟩
  · exact ⟨⟨"rp", 0, n⟩, by simp [andRegions], rfl, _, hlt, by simp [useCell]⟩

theorem andLoop_inv (n : Nat) (hn : n < 2 ^ 64) (sa : AState) (hI : andInv n sa)
    (hz : (passA andLoop sa).view.flagB (·.zf) = false) : andInv n (passA andLoop sa) := by
  obtain ⟨hs, hnz⟩ := hI
  rw [passA_zf, andLoop.eq_def] at hz
  simp only [decide_eq_false_iff_not] at hz
  have hz' : sa.regs "%rdi" - 1 ≠ 0 := by
    rw [← andBody_rdi]; exact hz
  have hpos : 0 < (sa.regs "%rdi").toNat := by
    rcases Nat.eq_zero_or_pos (sa.regs "%rdi").toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hnz
    · exact h
  refine ⟨?_, ?_⟩
  · rw [passA_regs, andBody_rax, andBody_rdi, BitVec.toNat_add, BitVec.toNat_sub]
    have := (sa.regs "%rdi").isLt
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1]
    omega
  · rw [passA_regs, andBody_rdi]; exact hz'

/-- **The transferred loop statement for `mpn_and_n`.** For the base pointers `P` of the
    three arrays and the stack, with `n` words per array and the four regions pairwise
    disjoint, from an address state and a name-keyed state related by `LoopRel` whose index
    and counter sum to `n` with a nonzero counter, the shipped pointer loop over address
    memory and the named-ref loop `andBodyNamed` over name-keyed memory both run out of fuel,
    or both exit, in states related by `LoopRel`. -/
theorem andLoop_transfer (P : String → BitVec 64) (n : Nat) (hn : n < 2 ^ 64)
    (hR : RegionsDisjoint andBank P (andRegions n)) (fuel : Nat) (sa : AState)
    (js : JState 64) (hI : andInv n sa)
    (hrel : LoopRel andBank P (regionCells (andRegions n)) andA sa js) :
    OptRel (LoopRel andBank P (regionCells (andRegions n)) andA)
      (runXLoopA fuel sa andLoop) (runXLoop fuel js { andLoop with body := andBodyNamed }) := by
  have h := runXLoopA_sim andBank P (regionCells (andRegions n)) (sepOn_regionCells _ _ _ hR)
    andA andLoop andLoop_disciplined
    (by
      rw [andLoop_canon, andLoop_footprint]
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 7, by decide, by decide⟩
      · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 0, by decide, by decide⟩
      · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 8, by decide, by decide⟩)
    andLoop_entails (andInv n) (andLoop_idx n) (andLoop_inv n hn) fuel sa js hI hrel
  have hc : canonLoop andBank andA andLoop = { andLoop with body := andBodyNamed } := by
    simp only [canonLoop, andLoop_canon]
  rwa [hc] at h

end CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx
