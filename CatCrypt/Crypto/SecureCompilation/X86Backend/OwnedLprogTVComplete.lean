/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-!
# Completeness of the value checker for two-address legalisation

`OwnedLprogTV.ownedCheckM` is sound (`ownedCheckM_sound`). This module gives the shared runs,
the lockstep simulation and the copy chunk from which `OwnedLprogTVTwoAddr` proves that it
accepts the legalisation `TwoAddrLegalize.twoAddrBody` of every straight-line body in its
well-formed fragment: the validator is complete for that pass, in the sense of Tristan and
Leroy.

## Method

The check runs the source block and then the target block over one hash-consed term table
(`blockRuns`). A word interned in a table is interned again, to the same entry and without a
new entry, in every table holding what the first interning added (`Tbl.Sub`,
`Tbl.intern_rerun`). The target run therefore reads the table the source run ends with: it
adds nothing, and equal words are equal entries. A target chunk simulates a source
instruction (`Chunk`) when its run from a state with the same words agrees with the step of
the instruction (`Res`); simulation of every instruction gives agreement of the whole runs
(`tRun_lock`). An instruction simulates itself (`chunk_self`, from `symStep_eqv`), and the
copy `mov d, x` followed by `opn d, [d, b]` simulates `opn d, [x, b]` when `b` does not read
`d` (`chunk_copy`, from `symStep_copy`). A non-empty straight-line body has one block
(`cfgOf_straight`), the live-set iteration covers what it needs after two rounds
(`liveIter_single`), and agreeing runs pass the block check (`blockOkR_fall`).

## Main definitions

* `Tbl.Has`, `Tbl.Sub`: an entry of a table and containment of tables.
* `SSt.Eqv`, `SSt.Inv`: states with the same words, and interned states.
* `SOut.Rel`, `Res`, `Chunk`: agreement of steps, of runs, and simulation of an instruction.
* `copyRouteOk`, `twoAddrWF`, `copyPair`, `twoAddrChunk`: the instructions the copy route
  legalises, the well-formedness for two-address legalisation, and its chunks.
* `straightR`, `straightCFG`: straight-line instructions and the graph of their bodies.

## Main results

* `Tbl.intern_rerun`: interning again in a containing table.
* `symStep_eqv`, `symStep_copy`: the symbolic step ignores the write lists, and the copy
  followed by the tied operation describes the untied operation.
* `tRun_lock`: runs in lockstep.
* `cfgOf_straight`: the graph of a straight-line body.
* `ownedCheckM_of_res`: agreeing runs of two straight-line bodies pass `ownedCheckM`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-! ## 1. Containment of term tables -/

theorem TExt.size_le {E E' : Array TEnt} (h : TExt E E') : E.size ≤ E'.size := by
  rcases Nat.eq_zero_or_pos E.size with h0 | h0
  · omega
  · have e := h (E.size - 1) (by omega)
    rcases Nat.lt_or_ge (E.size - 1) E'.size with h' | h'
    · omega
    · rw [Array.getElem?_eq_none h'] at e; cases e

/-- The table `T` holds the node `n` at entry `k`: its index sends `n` to `k`, and entry `k`
    is `n`. -/
def Tbl.Has (T : Tbl) (n : STerm) (k : Nat) : Prop :=
  T.idx[n]? = some k ∧ T.ents[k]?.map TEnt.node = some n

/-- Every node the table `T` holds, the table `T'` holds at the same entry. -/
def Tbl.Sub (T T' : Tbl) : Prop := ∀ n k, T.Has n k → T'.Has n k

theorem Tbl.Sub.refl (T : Tbl) : T.Sub T := fun _ _ h => h

theorem Tbl.Sub.trans {T T' T'' : Tbl} (h1 : T.Sub T') (h2 : T'.Sub T'') : T.Sub T'' :=
  fun n k h => h2 n k (h1 n k h)

theorem Tbl.Has.lt {T : Tbl} {n : STerm} {k : Nat} (h : T.Has n k) : k < T.ents.size := by
  rcases Nat.lt_or_ge k T.ents.size with h' | h'
  · exact h'
  · have := h.2
    rw [Array.getElem?_eq_none h'] at this
    cases this

theorem Tbl.share_of_has {T : Tbl} {n : STerm} {k : Nat} (h : T.Has n k) :
    T.share n = (T, .ref k) := by
  unfold Tbl.share
  rw [h.1]
  simp [h.2]

theorem Tbl.push_sub {T : Tbl} {n : STerm} (hn : ∀ k, ¬ T.Has n k) : T.Sub (T.push n).1 := by
  intro m k hm
  unfold Tbl.push
  split
  · have hk := hm.lt
    have hne : (n == m) = false := by
      rcases Bool.eq_false_or_eq_true (n == m) with e | e
      · exact absurd ((beq_iff_eq.mp e) ▸ hm) (hn k)
      · exact e
    refine ⟨?_, ?_⟩
    · simp only [Std.HashMap.getElem?_insert, hne, Bool.false_eq_true, ↓reduceIte]
      exact hm.1
    · simp only [Array.getElem?_push, Nat.ne_of_lt hk, ↓reduceIte]
      exact hm.2
  · exact hm

theorem Tbl.share_sub (T : Tbl) (n : STerm) : T.Sub (T.share n).1 := by
  unfold Tbl.share
  split
  · rename_i k hidx
    split
    · exact Tbl.Sub.refl T
    · rename_i hk
      refine Tbl.push_sub fun k' hk' => hk ?_
      have e := hk'.1
      rw [hidx, Option.some.injEq] at e
      subst e
      exact hk'.2
  · rename_i hidx
    refine Tbl.push_sub fun k' hk' => ?_
    have e := hk'.1
    rw [hidx] at e
    cases e

theorem Tbl.push_has {T : Tbl} {n : STerm} (hn : n.refsLt T.ents.size = true) :
    (T.push n).2 = .ref T.ents.size ∧ (T.push n).1.Has n T.ents.size := by
  unfold Tbl.push
  rw [if_pos hn]
  refine ⟨rfl, ?_, ?_⟩
  · simp
  · simp [mkEnt]

theorem Tbl.share_has {T : Tbl} {n : STerm} (hn : n.refsLt T.ents.size = true) :
    ∃ k, (T.share n).2 = .ref k ∧ (T.share n).1.Has n k := by
  unfold Tbl.share
  split
  · rename_i k hidx
    split
    · rename_i hk
      exact ⟨k, rfl, hidx, hk⟩
    · exact ⟨_, (Tbl.push_has hn).1, (Tbl.push_has hn).2⟩
  · exact ⟨_, (Tbl.push_has hn).1, (Tbl.push_has hn).2⟩

theorem Tbl.share_refsLt {T : Tbl} {n : STerm} (hn : n.refsLt T.ents.size = true) :
    (T.share n).2.refsLt (T.share n).1.ents.size = true := by
  obtain ⟨k, hk, hh⟩ := Tbl.share_has hn
  rw [hk]
  simpa [STerm.refsLt] using hh.lt

theorem Tbl.intern_sub : ∀ (T : Tbl) (t : STerm), T.Sub (T.intern t).1
  | T, .immAt _ x => (Tbl.intern_sub T x).trans (Tbl.share_sub _ _)
  | T, .bin _ x y =>
      ((Tbl.intern_sub T x).trans (Tbl.intern_sub _ y)).trans (Tbl.share_sub _ _)
  | T, .un _ x => (Tbl.intern_sub T x).trans (Tbl.share_sub _ _)
  | T, .shImm _ _ x => (Tbl.intern_sub T x).trans (Tbl.share_sub _ _)
  | T, .aget _ _ _ i => (Tbl.intern_sub T i).trans (Tbl.share_sub _ _)
  | T, .aluF _ _ x y o =>
      (((Tbl.intern_sub T x).trans (Tbl.intern_sub _ y)).trans (Tbl.intern_sub _ o)).trans
        (Tbl.share_sub _ _)
  | T, .carryW _ x y c =>
      (((Tbl.intern_sub T x).trans (Tbl.intern_sub _ y)).trans (Tbl.intern_sub _ c)).trans
        (Tbl.share_sub _ _)
  | T, .carryF _ _ x y c =>
      (((Tbl.intern_sub T x).trans (Tbl.intern_sub _ y)).trans (Tbl.intern_sub _ c)).trans
        (Tbl.share_sub _ _)
  | T, .mulx _ x y =>
      ((Tbl.intern_sub T x).trans (Tbl.intern_sub _ y)).trans (Tbl.share_sub _ _)
  | T, .cout _ x y c =>
      (((Tbl.intern_sub T x).trans (Tbl.intern_sub _ y)).trans (Tbl.intern_sub _ c)).trans
        (Tbl.share_sub _ _)
  | T, .sel x y c =>
      (((Tbl.intern_sub T x).trans (Tbl.intern_sub _ y)).trans (Tbl.intern_sub _ c)).trans
        (Tbl.share_sub _ _)
  | T, .reg _ => Tbl.Sub.refl T
  | T, .immW _ _ => Tbl.Sub.refl T
  | T, .cin _ => Tbl.Sub.refl T
  | T, .ref _ => Tbl.Sub.refl T

theorem Tbl.intern_size_le (T : Tbl) (t : STerm) : T.ents.size ≤ (T.intern t).1.ents.size :=
  (Tbl.intern_ext T t).size_le

/-- A word with no inner node: a start register, an immediate, a start flag or an entry. -/
def STerm.atom : STerm → Bool
  | .reg _ => true
  | .immW _ _ => true
  | .cin _ => true
  | .ref _ => true
  | _ => false

theorem Tbl.intern_atom (T : Tbl) {t : STerm} (h : t.atom = true) : T.intern t = (T, t) := by
  cases t <;> simp_all [STerm.atom, Tbl.intern]

theorem Tbl.share_atom {T : Tbl} {n : STerm} (hn : n.refsLt T.ents.size = true) :
    (T.share n).2.refsLt (T.share n).1.ents.size = true ∧ (T.share n).2.atom = true := by
  obtain ⟨k, hk, _⟩ := Tbl.share_has hn
  exact ⟨Tbl.share_refsLt hn, by rw [hk]; rfl⟩

/-- Interning a word that reads only entries of the table gives an atom reading only entries
    of the table it ends in. -/
theorem Tbl.intern_refsLt : ∀ (T : Tbl) (t : STerm), t.refsLt T.ents.size = true →
    (T.intern t).2.refsLt (T.intern t).1.ents.size = true ∧ (T.intern t).2.atom = true
  | T, .immAt m x, h => by
      simp only [STerm.refsLt] at h
      have hx := Tbl.intern_refsLt T x h
      exact Tbl.share_atom (n := .immAt m (T.intern x).2) (by simpa [STerm.refsLt] using hx.1)
  | T, .bin m x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1
      have hy := Tbl.intern_refsLt _ y (STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.2)
      have hn : (STerm.bin m (T.intern x).2 ((T.intern x).1.intern y).2).refsLt
          ((T.intern x).1.intern y).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨STerm.refsLt_mono (Tbl.intern_size_le _ y) _ hx.1, hy.1⟩
      exact Tbl.share_atom hn
  | T, .un m x, h => by
      simp only [STerm.refsLt] at h
      have hx := Tbl.intern_refsLt T x h
      have hn : (STerm.un m (T.intern x).2).refsLt (T.intern x).1.ents.size = true := by
        simpa [STerm.refsLt] using hx.1
      exact Tbl.share_atom hn
  | T, .shImm m k x, h => by
      simp only [STerm.refsLt] at h
      have hx := Tbl.intern_refsLt T x h
      have hn : (STerm.shImm m k (T.intern x).2).refsLt (T.intern x).1.ents.size = true := by
        simpa [STerm.refsLt] using hx.1
      exact Tbl.share_atom hn
  | T, .aget a w n i, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hi := Tbl.intern_refsLt T i h.2
      have hn : (STerm.aget a w n (T.intern i).2).refsLt (T.intern i).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨SArr.refsLt_mono (Tbl.intern_size_le T i) _ h.1, hi.1⟩
      exact Tbl.share_atom hn
  | T, .aluF op ofl x y o, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy := Tbl.intern_refsLt _ y (STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2)
      have ho := Tbl.intern_refsLt _ o (STerm.refsLt_mono
        ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2)
      have hn : (STerm.aluF op ofl (T.intern x).2 ((T.intern x).1.intern y).2
          (((T.intern x).1.intern y).1.intern o).2).refsLt
          (((T.intern x).1.intern y).1.intern o).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ o)) _
          hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ o) _ hy.1⟩, ho.1⟩
      exact Tbl.share_atom hn
  | T, .carryW op x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy := Tbl.intern_refsLt _ y (STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2)
      have ho := Tbl.intern_refsLt _ c (STerm.refsLt_mono
        ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2)
      have hn : (STerm.carryW op (T.intern x).2 ((T.intern x).1.intern y).2
          (((T.intern x).1.intern y).1.intern c).2).refsLt
          (((T.intern x).1.intern y).1.intern c).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ c)) _
          hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ c) _ hy.1⟩, ho.1⟩
      exact Tbl.share_atom hn
  | T, .carryF op ofl x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy := Tbl.intern_refsLt _ y (STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2)
      have ho := Tbl.intern_refsLt _ c (STerm.refsLt_mono
        ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2)
      have hn : (STerm.carryF op ofl (T.intern x).2 ((T.intern x).1.intern y).2
          (((T.intern x).1.intern y).1.intern c).2).refsLt
          (((T.intern x).1.intern y).1.intern c).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ c)) _
          hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ c) _ hy.1⟩, ho.1⟩
      exact Tbl.share_atom hn
  | T, .mulx hi x y, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1
      have hy := Tbl.intern_refsLt _ y (STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.2)
      have hn : (STerm.mulx hi (T.intern x).2 ((T.intern x).1.intern y).2).refsLt
          ((T.intern x).1.intern y).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨STerm.refsLt_mono (Tbl.intern_size_le _ y) _ hx.1, hy.1⟩
      exact Tbl.share_atom hn
  | T, .cout sub x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy := Tbl.intern_refsLt _ y (STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2)
      have ho := Tbl.intern_refsLt _ c (STerm.refsLt_mono
        ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2)
      have hn : (STerm.cout sub (T.intern x).2 ((T.intern x).1.intern y).2
          (((T.intern x).1.intern y).1.intern c).2).refsLt
          (((T.intern x).1.intern y).1.intern c).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ c)) _
          hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ c) _ hy.1⟩, ho.1⟩
      exact Tbl.share_atom hn
  | T, .sel x y c, h => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy := Tbl.intern_refsLt _ y (STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2)
      have ho := Tbl.intern_refsLt _ c (STerm.refsLt_mono
        ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2)
      have hn : (STerm.sel (T.intern x).2 ((T.intern x).1.intern y).2
          (((T.intern x).1.intern y).1.intern c).2).refsLt
          (((T.intern x).1.intern y).1.intern c).1.ents.size = true := by
        simp only [STerm.refsLt, Bool.and_eq_true]
        exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ c)) _
          hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ c) _ hy.1⟩, ho.1⟩
      exact Tbl.share_atom hn
  | T, .reg _, _ => ⟨rfl, rfl⟩
  | T, .immW _ _, _ => ⟨rfl, rfl⟩
  | T, .cin _, _ => ⟨rfl, rfl⟩
  | T, .ref _, h => ⟨h, rfl⟩

theorem Tbl.share_rerun {T T' : Tbl} {n : STerm} (hn : n.refsLt T.ents.size = true)
    (hS : (T.share n).1.Sub T') : T'.share n = (T', (T.share n).2) := by
  obtain ⟨k, hk, hh⟩ := Tbl.share_has hn
  rw [Tbl.share_of_has (hS n k hh), hk]

/-- **Interning again.** A word interned in `T` is interned in every table holding what the
    interning ends with, to the same atom and without a new entry. -/
theorem Tbl.intern_rerun : ∀ (T : Tbl) (t : STerm), t.refsLt T.ents.size = true →
    ∀ (T' : Tbl), (T.intern t).1.Sub T' → T'.intern t = (T', (T.intern t).2)
  | T, .immAt m x, h, T', hS => by
      simp only [STerm.refsLt] at h
      have hx := Tbl.intern_refsLt T x h
      simp only [Tbl.intern] at hS ⊢
      rw [Tbl.intern_rerun T x h T' ((Tbl.share_sub _ _).trans hS)]
      exact Tbl.share_rerun (by simpa [STerm.refsLt] using hx.1) hS
  | T, .bin m x y, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1
      have hy' := STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.2
      have hy := Tbl.intern_refsLt _ y hy'
      simp only [Tbl.intern] at hS ⊢
      have h2 := (Tbl.share_sub _ _).trans hS
      rw [Tbl.intern_rerun T x h.1 T' ((Tbl.intern_sub _ y).trans h2),
        Tbl.intern_rerun _ y hy' T' h2]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨STerm.refsLt_mono (Tbl.intern_size_le _ y) _ hx.1, hy.1⟩
  | T, .un m x, h, T', hS => by
      simp only [STerm.refsLt] at h
      have hx := Tbl.intern_refsLt T x h
      simp only [Tbl.intern] at hS ⊢
      rw [Tbl.intern_rerun T x h T' ((Tbl.share_sub _ _).trans hS)]
      exact Tbl.share_rerun (by simpa [STerm.refsLt] using hx.1) hS
  | T, .shImm m k x, h, T', hS => by
      simp only [STerm.refsLt] at h
      have hx := Tbl.intern_refsLt T x h
      simp only [Tbl.intern] at hS ⊢
      rw [Tbl.intern_rerun T x h T' ((Tbl.share_sub _ _).trans hS)]
      exact Tbl.share_rerun (by simpa [STerm.refsLt] using hx.1) hS
  | T, .aget a w n i, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hi := Tbl.intern_refsLt T i h.2
      simp only [Tbl.intern] at hS ⊢
      rw [Tbl.intern_rerun T i h.2 T' ((Tbl.share_sub _ _).trans hS)]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨SArr.refsLt_mono (Tbl.intern_size_le T i) _ h.1, hi.1⟩
  | T, .aluF op ofl x y o, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy' := STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2
      have hy := Tbl.intern_refsLt _ y hy'
      have ho' := STerm.refsLt_mono ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2
      have ho := Tbl.intern_refsLt _ o ho'
      simp only [Tbl.intern] at hS ⊢
      have h3 := (Tbl.share_sub _ _).trans hS
      have h2 := (Tbl.intern_sub _ o).trans h3
      rw [Tbl.intern_rerun T x h.1.1 T' ((Tbl.intern_sub _ y).trans h2),
        Tbl.intern_rerun _ y hy' T' h2, Tbl.intern_rerun _ o ho' T' h3]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ o)) _
        hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ o) _ hy.1⟩, ho.1⟩
  | T, .carryW op x y o, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy' := STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2
      have hy := Tbl.intern_refsLt _ y hy'
      have ho' := STerm.refsLt_mono ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2
      have ho := Tbl.intern_refsLt _ o ho'
      simp only [Tbl.intern] at hS ⊢
      have h3 := (Tbl.share_sub _ _).trans hS
      have h2 := (Tbl.intern_sub _ o).trans h3
      rw [Tbl.intern_rerun T x h.1.1 T' ((Tbl.intern_sub _ y).trans h2),
        Tbl.intern_rerun _ y hy' T' h2, Tbl.intern_rerun _ o ho' T' h3]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ o)) _
        hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ o) _ hy.1⟩, ho.1⟩
  | T, .carryF op ofl x y o, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy' := STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2
      have hy := Tbl.intern_refsLt _ y hy'
      have ho' := STerm.refsLt_mono ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2
      have ho := Tbl.intern_refsLt _ o ho'
      simp only [Tbl.intern] at hS ⊢
      have h3 := (Tbl.share_sub _ _).trans hS
      have h2 := (Tbl.intern_sub _ o).trans h3
      rw [Tbl.intern_rerun T x h.1.1 T' ((Tbl.intern_sub _ y).trans h2),
        Tbl.intern_rerun _ y hy' T' h2, Tbl.intern_rerun _ o ho' T' h3]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ o)) _
        hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ o) _ hy.1⟩, ho.1⟩
  | T, .mulx hb x y, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1
      have hy' := STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.2
      have hy := Tbl.intern_refsLt _ y hy'
      simp only [Tbl.intern] at hS ⊢
      have h2 := (Tbl.share_sub _ _).trans hS
      rw [Tbl.intern_rerun T x h.1 T' ((Tbl.intern_sub _ y).trans h2),
        Tbl.intern_rerun _ y hy' T' h2]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨STerm.refsLt_mono (Tbl.intern_size_le _ y) _ hx.1, hy.1⟩
  | T, .cout sub x y o, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy' := STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2
      have hy := Tbl.intern_refsLt _ y hy'
      have ho' := STerm.refsLt_mono ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2
      have ho := Tbl.intern_refsLt _ o ho'
      simp only [Tbl.intern] at hS ⊢
      have h3 := (Tbl.share_sub _ _).trans hS
      have h2 := (Tbl.intern_sub _ o).trans h3
      rw [Tbl.intern_rerun T x h.1.1 T' ((Tbl.intern_sub _ y).trans h2),
        Tbl.intern_rerun _ y hy' T' h2, Tbl.intern_rerun _ o ho' T' h3]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ o)) _
        hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ o) _ hy.1⟩, ho.1⟩
  | T, .sel x y o, h, T', hS => by
      simp only [STerm.refsLt, Bool.and_eq_true] at h
      have hx := Tbl.intern_refsLt T x h.1.1
      have hy' := STerm.refsLt_mono (Tbl.intern_size_le T x) _ h.1.2
      have hy := Tbl.intern_refsLt _ y hy'
      have ho' := STerm.refsLt_mono ((Tbl.intern_size_le T x).trans (Tbl.intern_size_le _ y)) _ h.2
      have ho := Tbl.intern_refsLt _ o ho'
      simp only [Tbl.intern] at hS ⊢
      have h3 := (Tbl.share_sub _ _).trans hS
      have h2 := (Tbl.intern_sub _ o).trans h3
      rw [Tbl.intern_rerun T x h.1.1 T' ((Tbl.intern_sub _ y).trans h2),
        Tbl.intern_rerun _ y hy' T' h2, Tbl.intern_rerun _ o ho' T' h3]
      refine Tbl.share_rerun ?_ hS
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_mono ((Tbl.intern_size_le _ y).trans (Tbl.intern_size_le _ o)) _
        hx.1, STerm.refsLt_mono (Tbl.intern_size_le _ o) _ hy.1⟩, ho.1⟩
  | _, .reg _, _, _, _ => rfl
  | _, .immW _ _, _, _, _ => rfl
  | _, .cin _, _, _, _ => rfl
  | _, .ref _, _, _, _ => rfl

/-! ## 2. Words below a table size -/

/-- The substitution that keeps the entries below `n` and sends every other entry to a word
    that is no entry. -/
def keepBelow (n : Nat) (k : Nat) : STerm := if k < n then .ref k else .immW 0 0

mutual
theorem STerm.subst_ref : ∀ t : STerm, t.subst STerm.ref = t
  | .reg _ => rfl
  | .immW _ _ => rfl
  | .immAt _ x => by simp only [STerm.subst, STerm.subst_ref x]
  | .bin _ x y => by simp only [STerm.subst, STerm.subst_ref x, STerm.subst_ref y]
  | .un _ x => by simp only [STerm.subst, STerm.subst_ref x]
  | .shImm _ _ x => by simp only [STerm.subst, STerm.subst_ref x]
  | .aget a _ _ i => by simp only [STerm.subst, SArr.subst_ref a, STerm.subst_ref i]
  | .cin _ => rfl
  | .aluF _ _ x y o => by
      simp only [STerm.subst, STerm.subst_ref x, STerm.subst_ref y, STerm.subst_ref o]
  | .carryW _ x y c => by
      simp only [STerm.subst, STerm.subst_ref x, STerm.subst_ref y, STerm.subst_ref c]
  | .carryF _ _ x y c => by
      simp only [STerm.subst, STerm.subst_ref x, STerm.subst_ref y, STerm.subst_ref c]
  | .mulx _ x y => by simp only [STerm.subst, STerm.subst_ref x, STerm.subst_ref y]
  | .cout _ x y c => by
      simp only [STerm.subst, STerm.subst_ref x, STerm.subst_ref y, STerm.subst_ref c]
  | .sel x y c => by
      simp only [STerm.subst, STerm.subst_ref x, STerm.subst_ref y, STerm.subst_ref c]
  | .ref _ => rfl

theorem SArr.subst_ref : ∀ a : SArr, a.subst STerm.ref = a
  | .cell _ => rfl
  | .aset a _ _ i v => by
      simp only [SArr.subst, SArr.subst_ref a, STerm.subst_ref i, STerm.subst_ref v]
end

theorem keepBelow_agree (n : Nat) : ∀ k, k < n → keepBelow n k = STerm.ref k :=
  fun k hk => by simp [keepBelow, hk]

theorem STerm.subst_keepBelow {n : Nat} {t : STerm} (h : t.refsLt n = true) :
    t.subst (keepBelow n) = t :=
  (STerm.subst_congr (keepBelow_agree n) t h).trans (STerm.subst_ref t)

theorem SArr.subst_keepBelow {n : Nat} {a : SArr} (h : a.refsLt n = true) :
    a.subst (keepBelow n) = a :=
  (SArr.subst_congr (keepBelow_agree n) a h).trans (SArr.subst_ref a)

mutual
theorem STerm.refsLt_of_subst {n : Nat} :
    ∀ t : STerm, t.subst (keepBelow n) = t → t.refsLt n = true
  | .reg _, _ => rfl
  | .immW _ _, _ => rfl
  | .immAt _ x, h => by
      simp only [STerm.subst, STerm.immAt.injEq, true_and] at h
      exact STerm.refsLt_of_subst x h
  | .bin _ x y, h => by
      simp only [STerm.subst, STerm.bin.injEq, true_and] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2⟩
  | .un _ x, h => by
      simp only [STerm.subst, STerm.un.injEq, true_and] at h
      exact STerm.refsLt_of_subst x h
  | .shImm _ _ x, h => by
      simp only [STerm.subst, STerm.shImm.injEq, true_and] at h
      exact STerm.refsLt_of_subst x h
  | .aget a _ _ i, h => by
      simp only [STerm.subst, STerm.aget.injEq, true_and] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨SArr.refsLt_of_subst a h.1, STerm.refsLt_of_subst i h.2⟩
  | .cin _, _ => rfl
  | .aluF _ _ x y o, h => by
      simp only [STerm.subst, STerm.aluF.injEq, true_and] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2.1⟩,
        STerm.refsLt_of_subst o h.2.2⟩
  | .carryW _ x y c, h => by
      simp only [STerm.subst, STerm.carryW.injEq, true_and] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2.1⟩,
        STerm.refsLt_of_subst c h.2.2⟩
  | .carryF _ _ x y c, h => by
      simp only [STerm.subst, STerm.carryF.injEq, true_and] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2.1⟩,
        STerm.refsLt_of_subst c h.2.2⟩
  | .mulx _ x y, h => by
      simp only [STerm.subst, STerm.mulx.injEq, true_and] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2⟩
  | .cout _ x y c, h => by
      simp only [STerm.subst, STerm.cout.injEq, true_and] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2.1⟩,
        STerm.refsLt_of_subst c h.2.2⟩
  | .sel x y c, h => by
      simp only [STerm.subst, STerm.sel.injEq] at h
      simp only [STerm.refsLt, Bool.and_eq_true]
      exact ⟨⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2.1⟩,
        STerm.refsLt_of_subst c h.2.2⟩
  | .ref k, h => by
      simp only [STerm.subst, keepBelow] at h
      simp only [STerm.refsLt, decide_eq_true_eq]
      by_contra hk
      rw [if_neg hk] at h
      cases h

theorem SArr.refsLt_of_subst {n : Nat} :
    ∀ a : SArr, a.subst (keepBelow n) = a → a.refsLt n = true
  | .cell _, _ => rfl
  | .aset a _ _ i v, h => by
      simp only [SArr.subst, SArr.aset.injEq, true_and] at h
      simp only [SArr.refsLt, Bool.and_eq_true]
      exact ⟨⟨SArr.refsLt_of_subst a h.1, STerm.refsLt_of_subst i h.2.1⟩,
        STerm.refsLt_of_subst v h.2.2⟩
end

/-- Every word of the symbolic state `ss` reads only table entries below `n`. -/
def SSt.RefsLt (n : Nat) (ss : SSt) : Prop :=
  (∀ r, (ss.regs r).refsLt n = true) ∧ (∀ q, (ss.arrs q).refsLt n = true) ∧
    ss.zf.refsLt n = true ∧ ss.cf.refsLt n = true ∧ ss.of.refsLt n = true

theorem SSt.RefsLt.subst {n : Nat} {ss : SSt} (h : ss.RefsLt n) : ss.subst (keepBelow n) = ss := by
  obtain ⟨hr, ha, hz, hc, ho⟩ := h
  have hz' : ss.zf.subst (keepBelow n) = ss.zf := by
    cases e : ss.zf with
    | init => rfl
    | cmp x y =>
        rw [e] at hz
        simp only [SFlag.refsLt, Bool.and_eq_true] at hz
        simp only [SFlag.subst, STerm.subst_keepBelow hz.1, STerm.subst_keepBelow hz.2]
  simp only [SSt.subst, STerm.subst_keepBelow (hr _), SArr.subst_keepBelow (ha _), hz',
    STerm.subst_keepBelow hc, STerm.subst_keepBelow ho]

theorem SSt.RefsLt.of_subst {n : Nat} {ss : SSt} (h : ss.subst (keepBelow n) = ss) :
    ss.RefsLt n := by
  obtain ⟨R, A, Z, W, AW, C, O⟩ := ss
  simp only [SSt.subst, SSt.mk.injEq] at h
  obtain ⟨hR, hA, hZ, -, -, hC, hO⟩ := h
  refine ⟨fun r => STerm.refsLt_of_subst _ (congrFun hR r),
    fun q => SArr.refsLt_of_subst _ (congrFun hA q), ?_, STerm.refsLt_of_subst _ hC,
    STerm.refsLt_of_subst _ hO⟩
  cases Z with
  | init => rfl
  | cmp x y =>
      simp only [SFlag.subst, SFlag.cmp.injEq] at hZ
      simp only [SFlag.refsLt, Bool.and_eq_true]
      exact ⟨STerm.refsLt_of_subst _ hZ.1, STerm.refsLt_of_subst _ hZ.2⟩

theorem SG.refsLt_of_subst {n : Nat} {g : SG} (h : g.subst (keepBelow n) = g) :
    g.refsLt n = true := by
  cases g with
  | wid t w =>
      simp only [SG.subst, SG.wid.injEq, and_true] at h
      exact STerm.refsLt_of_subst t h
  | eqW x y =>
      simp only [SG.subst, SG.eqW.injEq] at h
      simp only [SG.refsLt, Bool.and_eq_true]
      exact ⟨STerm.refsLt_of_subst x h.1, STerm.refsLt_of_subst y h.2⟩
  | shp a w m =>
      simp only [SG.subst, SG.shp.injEq, and_true] at h
      exact SArr.refsLt_of_subst a h

theorem map_fixed {α : Type} {f : α → α} : ∀ {l : List α}, l.map f = l → ∀ x ∈ l, f x = x
  | [], _, _, hx => by cases hx
  | a :: l, h, x, hx => by
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact map_fixed h.2 x hx

/-- **A step reads no new entry.** A step from a state below `n` ends in a state below `n`
    with guards below `n`. -/
theorem symStep_refsLt {n : Nat} (i : LinstrRM) {ss : SSt} (h : ss.RefsLt n) {s : SSt}
    {gs : List SG} (hs : symStep i ss = .ok s gs) : s.RefsLt n ∧ ∀ g ∈ gs, g.refsLt n = true := by
  have e := symStep_subst (keepBelow n) i ss
  rw [h.subst, hs] at e
  simp only [SOut.subst, SOut.ok.injEq] at e
  refine ⟨SSt.RefsLt.of_subst e.1.symm, fun g hg => SG.refsLt_of_subst ?_⟩
  exact map_fixed e.2.symm g hg

/-! ## 3. States that differ in their write lists -/

/-- Two symbolic states with one word for every register, array and flag; their lists of
    written names may differ. -/
def SSt.Eqv (s t : SSt) : Prop :=
  s.regs = t.regs ∧ s.arrs = t.arrs ∧ s.zf = t.zf ∧ s.cf = t.cf ∧ s.of = t.of

theorem SSt.Eqv.refl (s : SSt) : s.Eqv s := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The step descriptions `o` from `ss` and `o'` from `ss'` agree: both fail, both are
    outside the fragment, or both succeed with equal guards in states with one word for every
    name, each written list extended by one list of names. -/
def SOut.Rel (ss ss' : SSt) : SOut → SOut → Prop
  | .ok s g, .ok s' g' => s.Eqv s' ∧ g = g' ∧ ∃ ds, s.wr = ds ++ ss.wr ∧ s'.wr = ds ++ ss'.wr
  | .fail, .fail => True
  | .unk, .unk => True
  | _, _ => False

theorem liftR_eqv {ss ss' : SSt} (h : ss.Eqv ss') (o : ROut) :
    SOut.Rel ss ss' (liftR ss o) (liftR ss' o) := by
  obtain ⟨hR, hA, hZ, hC, hO⟩ := h
  cases o with
  | set d t gs =>
      refine ⟨⟨?_, hA, hZ, hC, hO⟩, rfl, [d], rfl, rfl⟩
      simp only [SSt.setR, hR]
  | nop => exact ⟨⟨hR, hA, hZ, hC, hO⟩, rfl, [], rfl, rfl⟩
  | fail => trivial
  | unk => trivial

theorem symMem_eqv {ss ss' : SSt} (h : ss.Eqv ss') (i : LinstrRM) :
    SOut.Rel ss ss' (symMem i ss) (symMem i ss') := by
  have h' := h
  obtain ⟨hR, hA, hZ, hC, hO⟩ := h'
  obtain ⟨x, tag⟩ := i
  unfold symMem
  cases tag with
  | load w n =>
      dsimp only
      split
      · refine ⟨⟨?_, hA, hZ, hC, hO⟩, by rw [hR, hA], [_], rfl, rfl⟩
        simp only [SSt.setR, hR, hA]
      · rw [← hR]; exact liftR_eqv h _
  | store w n =>
      dsimp only
      split
      · refine ⟨⟨hR, ?_, hZ, hC, hO⟩, by rw [hR, hA], [], rfl, rfl⟩
        simp only [SSt.setA, hR, hA]
      · rw [← hR]; exact liftR_eqv h _
  | loadC => trivial
  | storeC => trivial
  | reg cd => dsimp only; rw [← hR]; exact liftR_eqv h _

theorem aluFl_eqv {ss ss' : SSt} (h : ss.Eqv ss') (i : LinstrRM) {o o' : SOut}
    (ho : SOut.Rel ss ss' o o') : SOut.Rel ss ss' (aluFl i ss o) (aluFl i ss' o') := by
  have hT : ∀ b, aluFlT i ss b = aluFlT i ss' b := by
    intro b
    simp only [aluFlT, h.1, h.2.2.2.1, h.2.2.2.2]
  cases o <;> cases o' <;> simp only [SOut.Rel, aluFl] at ho ⊢
  obtain ⟨⟨hR, hA, hZ, -, -⟩, hg, hw⟩ := ho
  exact ⟨⟨hR, hA, hZ, hT false, hT true⟩, hg, hw⟩

theorem symCarry_eqv {ss ss' : SSt} (h : ss.Eqv ss') (op : CarryOp) (d : String)
    (a b : LOperand) : SOut.Rel ss ss' (symCarry op d a b ss) (symCarry op d a b ss') := by
  obtain ⟨hR, hA, hZ, hC, hO⟩ := h
  unfold symCarry
  rw [← hR]
  split
  · cases op <;>
      exact ⟨⟨by simp only [SSt.setR, hR, hC, hO], by simp only [SSt.setR, hA],
        by simp only [SSt.setR, hZ], by simp only [SSt.setR, hC, hO],
        by simp only [SSt.setR, hC, hO]⟩, rfl, [d], rfl, rfl⟩
  · trivial

theorem symWide_eqv {ss ss' : SSt} (h : ss.Eqv ss') (w : WideOp) :
    SOut.Rel ss ss' (symWide w ss) (symWide w ss') := by
  obtain ⟨hR, hA, hZ, hC, hO⟩ := h
  cases w with
  | mov d b =>
      simp only [symWide]
      rw [← hR]
      split
      · exact ⟨⟨by simp only [SSt.setR, hR], hA, hZ, hC, hO⟩, rfl, [d], rfl, rfl⟩
      · trivial
  | mulx lo hi b =>
      simp only [symWide]
      rw [← hR]
      split
      · exact ⟨⟨by simp only [SSt.setR, hR], hA, hZ, hC, hO⟩, rfl, [hi, lo], rfl, rfl⟩
      · trivial

/-- **A step ignores the write lists.** -/
theorem symStep_eqv {ss ss' : SSt} (h : ss.Eqv ss') (i : LinstrRM) :
    SOut.Rel ss ss' (symStep i ss) (symStep i ss') := by
  have h' := h
  obtain ⟨hR, hA, hZ, hC, hO⟩ := h'
  unfold symStep
  rw [← hR]
  split
  · split
    · exact ⟨⟨rfl, hA, rfl, hC, hO⟩, rfl, [], rfl, rfl⟩
    · trivial
  · split
    · exact ⟨⟨by simp only [SSt.setR, hR], hA, hZ, hC, hO⟩, rfl, [_], rfl, rfl⟩
    · split
      · trivial
      · split
        · exact ⟨h, rfl, [], rfl, rfl⟩
        · trivial
        · trivial
        · split
          · exact symCarry_eqv h _ _ _ _
          · split
            · exact symWide_eqv h _
            · exact aluFl_eqv h i (symMem_eqv h i)

/-- The state `s` extends the write list of `ss` by the names `ds` and keeps the word of every
    register outside `ds`. -/
def SSt.Frm (ss s : SSt) : Prop :=
  ∃ ds, s.wr = ds ++ ss.wr ∧ ∀ r, r ∉ ds → s.regs r = ss.regs r

theorem SSt.Frm.refl (ss : SSt) : ss.Frm ss := ⟨[], rfl, fun _ _ => rfl⟩

theorem SSt.Frm.setR {ss s : SSt} (h : ss.Frm s) (d : String) (t : STerm) :
    ss.Frm (s.setR d t) := by
  obtain ⟨ds, hw, hr⟩ := h
  refine ⟨d :: ds, by simp [SSt.setR, hw], fun r hr' => ?_⟩
  simp only [List.mem_cons, not_or] at hr'
  simp only [SSt.setR, if_neg hr'.1]
  exact hr r hr'.2

theorem SSt.Frm.setA {ss s : SSt} (h : ss.Frm s) (d : String) (a : SArr) :
    ss.Frm (s.setA d a) := h

theorem liftR_frm {ss : SSt} {o : ROut} {s : SSt} {gs : List SG}
    (h : liftR ss o = .ok s gs) : ss.Frm s := by
  cases o <;> simp only [liftR, SOut.ok.injEq, reduceCtorEq] at h
  · rw [← h.1]; exact (SSt.Frm.refl ss).setR _ _
  · rw [← h.1]; exact SSt.Frm.refl ss

theorem symMem_frm (i : LinstrRM) {ss s : SSt} {gs : List SG}
    (h : symMem i ss = .ok s gs) : ss.Frm s := by
  obtain ⟨x, tag⟩ := i
  unfold symMem at h
  cases tag with
  | load w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact (SSt.Frm.refl ss).setR _ _
      · exact liftR_frm h
  | store w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact (SSt.Frm.refl ss).setA _ _
      · exact liftR_frm h
  | loadC => cases h
  | storeC => cases h
  | reg cd => exact liftR_frm h

theorem symCarry_frm {op : CarryOp} {d : String} {a b : LOperand} {ss s : SSt} {gs : List SG}
    (h : symCarry op d a b ss = .ok s gs) : ss.Frm s := by
  unfold symCarry at h
  split at h
  · cases op <;> simp only [SOut.ok.injEq] at h <;> rw [← h.1] <;>
      exact (SSt.Frm.refl ss).setR _ _
  · cases h

/-- **A step writes only the names it adds to the write list.** -/
theorem symStep_frm (i : LinstrRM) {ss s : SSt} {gs : List SG}
    (h : symStep i ss = .ok s gs) : ss.Frm s := by
  unfold symStep at h
  split at h
  · split at h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact SSt.Frm.refl ss
    · cases h
  · split at h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact (SSt.Frm.refl ss).setR _ _
    · split at h
      · cases h
      · split at h
        · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact SSt.Frm.refl ss
        · cases h
        · cases h
        · split at h
          · exact symCarry_frm h
          · split at h
            · rename_i w _
              cases w with
              | mov d b =>
                  simp only [symWide] at h
                  split at h
                  · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact (SSt.Frm.refl ss).setR _ _
                  · cases h
              | mulx lo hi b =>
                  simp only [symWide] at h
                  split at h
                  · simp only [SOut.ok.injEq] at h; rw [← h.1]
                    exact ((SSt.Frm.refl ss).setR _ _).setR _ _
                  · cases h
            · cases hm : symMem i ss with
              | ok s1 g1 =>
                  rw [hm] at h
                  simp only [aluFl, SOut.ok.injEq] at h
                  rw [← h.1]
                  obtain ⟨ds, hw, hr⟩ := symMem_frm i hm
                  exact ⟨ds, hw, hr⟩
              | fail => rw [hm] at h; cases h
              | unk => rw [hm] at h; cases h

theorem SSt.Frm.ds_eq {ss s : SSt} {ds : List String} (h : s.wr = ds ++ ss.wr) :
    s.wr.take (s.wr.length - ss.wr.length) = ds := by
  rw [h, List.length_append, Nat.add_sub_cancel, List.take_left' rfl]

/-! ## 4. Interned states -/

/-- The state `ss` is interned below `n`: every word reads only entries below `n`, and every
    register and the carry and overflow flags hold atoms. -/
def SSt.Inv (n : Nat) (ss : SSt) : Prop :=
  ss.RefsLt n ∧ (∀ r, (ss.regs r).atom = true) ∧ ss.cf.atom = true ∧ ss.of.atom = true

theorem SSt.Eqv.symm {s t : SSt} (h : s.Eqv t) : t.Eqv s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem SSt.Eqv.trans {s t u : SSt} (h1 : s.Eqv t) (h2 : t.Eqv u) : s.Eqv u :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.1.trans h2.2.2.2.1,
    h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem SSt.RefsLt.mono {n m : Nat} (hnm : n ≤ m) {ss : SSt} (h : ss.RefsLt n) : ss.RefsLt m := by
  obtain ⟨hr, ha, hz, hc, ho⟩ := h
  refine ⟨fun r => STerm.refsLt_mono hnm _ (hr r), fun q => SArr.refsLt_mono hnm _ (ha q), ?_,
    STerm.refsLt_mono hnm _ hc, STerm.refsLt_mono hnm _ ho⟩
  cases e : ss.zf with
  | init => rfl
  | cmp x y =>
      rw [e] at hz
      simp only [SFlag.refsLt, Bool.and_eq_true] at hz ⊢
      exact ⟨STerm.refsLt_mono hnm _ hz.1, STerm.refsLt_mono hnm _ hz.2⟩

theorem SSt.RefsLt.of_eqv {n : Nat} {s t : SSt} (h : s.RefsLt n) (e : s.Eqv t) : t.RefsLt n := by
  obtain ⟨hR, hA, hZ, hC, hO⟩ := e
  obtain ⟨hr, ha, hz, hc, ho⟩ := h
  exact ⟨fun r => hR ▸ hr r, fun q => hA ▸ ha q, hZ ▸ hz, hC ▸ hc, hO ▸ ho⟩

theorem SSt.Inv.of_eqv {n : Nat} {s t : SSt} (h : s.Inv n) (e : s.Eqv t) : t.Inv n :=
  ⟨h.1.of_eqv e, fun r => e.1 ▸ h.2.1 r, e.2.2.2.1 ▸ h.2.2.1, e.2.2.2.2 ▸ h.2.2.2⟩

theorem Tbl.internRegs_sub : ∀ (T : Tbl) (ss : SSt) (ds : List String),
    T.Sub (T.internRegs ss ds).1
  | T, _, [] => Tbl.Sub.refl T
  | T, ss, d :: ds => (Tbl.intern_sub T (ss.regs d)).trans (Tbl.internRegs_sub _ _ ds)

theorem Tbl.internRegs_size_le : ∀ (T : Tbl) (ss : SSt) (ds : List String),
    T.ents.size ≤ (T.internRegs ss ds).1.ents.size
  | T, ss, ds => (Tbl.internRegs_ext T ss ds).size_le

theorem Tbl.internRegs_snd : ∀ (T : Tbl) (ss : SSt) (ds : List String),
    (T.internRegs ss ds).2 = { ss with regs := (T.internRegs ss ds).2.regs }
  | T, ss, [] => rfl
  | T, ss, d :: ds => by
      simp only [Tbl.internRegs]
      rw [Tbl.internRegs_snd _ _ ds]

/-- Interning registers leaves the words reading entries of the table, makes the interned
    registers atoms and keeps every other register. -/
theorem Tbl.internRegs_inv : ∀ (T : Tbl) (ss : SSt) (ds : List String),
    (∀ r, (ss.regs r).refsLt T.ents.size = true) →
      (∀ r, ((T.internRegs ss ds).2.regs r).refsLt (T.internRegs ss ds).1.ents.size = true) ∧
      (∀ r, r ∈ ds → ((T.internRegs ss ds).2.regs r).atom = true) ∧
      (∀ r, r ∉ ds → (T.internRegs ss ds).2.regs r = ss.regs r)
  | T, ss, [], h => ⟨h, (fun _ hr => by cases hr), fun _ _ => rfl⟩
  | T, ss, d :: ds, h => by
      simp only [Tbl.internRegs]
      have hd := Tbl.intern_refsLt T (ss.regs d) (h d)
      have ih := Tbl.internRegs_inv (T.intern (ss.regs d)).1
        { ss with regs := fun r => if r = d then (T.intern (ss.regs d)).2 else ss.regs r } ds
        (fun r => by
          dsimp only
          split
          · exact hd.1
          · exact STerm.refsLt_mono (Tbl.intern_size_le _ _) _ (h r))
      refine ⟨ih.1, fun r hr => ?_, fun r hr => ?_⟩
      · by_cases hrs : r ∈ ds
        · exact ih.2.1 r hrs
        · rw [ih.2.2 r hrs]
          have : r = d := by
            rcases List.mem_cons.mp hr with h' | h'
            · exact h'
            · exact absurd h' hrs
          simp only [this, ↓reduceIte]
          exact hd.2
      · simp only [List.mem_cons, not_or] at hr
        rw [ih.2.2 r hr.2]
        simp only [if_neg hr.1]

theorem Tbl.internRegs_rerun : ∀ (T : Tbl) (ss ss' : SSt) (ds : List String),
    ss'.regs = ss.regs → (∀ r, (ss.regs r).refsLt T.ents.size = true) → ∀ (T' : Tbl),
    (T.internRegs ss ds).1.Sub T' →
      T'.internRegs ss' ds = (T', { ss' with regs := (T.internRegs ss ds).2.regs })
  | T, ss, ss', [], hR, _, T', _ => by
      simp only [Tbl.internRegs, ← hR]
  | T, ss, ss', d :: ds, hR, h, T', hS => by
      simp only [Tbl.internRegs] at hS ⊢
      have hd := Tbl.intern_refsLt T (ss.regs d) (h d)
      rw [hR, Tbl.intern_rerun T (ss.regs d) (h d) T'
        ((Tbl.internRegs_sub _ _ ds).trans hS)]
      have := Tbl.internRegs_rerun (T.intern (ss.regs d)).1
        { ss with regs := fun r => if r = d then (T.intern (ss.regs d)).2 else ss.regs r }
        { ss' with regs := fun r => if r = d then (T.intern (ss.regs d)).2 else ss.regs r } ds
        rfl (fun r => by
          dsimp only
          split
          · exact hd.1
          · exact STerm.refsLt_mono (Tbl.intern_size_le _ _) _ (h r)) T' hS
      rw [this]

theorem Tbl.internSt_sub (T : Tbl) (ss : SSt) (ds : List String) :
    T.Sub (T.internSt ss ds).1 :=
  ((Tbl.internRegs_sub T ss ds).trans (Tbl.intern_sub _ _)).trans (Tbl.intern_sub _ _)

/-- **Interning a state again.** -/
theorem Tbl.internSt_rerun {T T' : Tbl} {ss ss' : SSt} (e : ss.Eqv ss') (ds : List String)
    (h : ss.RefsLt T.ents.size) (hS : (T.internSt ss ds).1.Sub T') :
    ∃ s', T'.internSt ss' ds = (T', s') ∧ (T.internSt ss ds).2.Eqv s' ∧ s'.wr = ss'.wr ∧
      s'.awr = ss'.awr := by
  obtain ⟨hR, hA, hZ, hC, hO⟩ := e
  simp only [Tbl.internSt] at hS ⊢
  have hS2 := (Tbl.intern_sub _ _).trans hS
  have hS1 := (Tbl.intern_sub _ _).trans hS2
  rw [Tbl.internRegs_rerun T ss ss' ds hR.symm h.1 T' hS1]
  have e1 := Tbl.internRegs_snd T ss ds
  have hsz := Tbl.internRegs_size_le T ss ds
  have hc : (T.internRegs ss ds).2.cf.refsLt (T.internRegs ss ds).1.ents.size = true := by
    rw [e1]; exact STerm.refsLt_mono hsz _ h.2.2.2.1
  have hcf : (T.internRegs ss ds).2.cf = ss'.cf := by rw [e1]; exact hC
  have hof : (T.internRegs ss ds).2.of = ss'.of := by rw [e1]; exact hO
  dsimp only
  rw [← hcf, Tbl.intern_rerun _ _ hc T' hS2]
  have ho : (T.internRegs ss ds).2.of.refsLt
      ((T.internRegs ss ds).1.intern (T.internRegs ss ds).2.cf).1.ents.size = true := by
    rw [e1]
    exact STerm.refsLt_mono (hsz.trans (Tbl.intern_size_le _ _)) _ h.2.2.2.2
  rw [← hof, Tbl.intern_rerun _ _ ho T' hS]
  refine ⟨_, rfl, ⟨rfl, ?_, ?_, rfl, rfl⟩, rfl, rfl⟩
  · rw [e1]; exact hA
  · rw [e1]; exact hZ

/-- Interning the written registers and the flags of a state below the table gives an
    interned state, when the registers outside `ds` already hold atoms. -/
theorem Tbl.internSt_inv {T : Tbl} {ss : SSt} (ds : List String) (h : ss.RefsLt T.ents.size)
    (ha : ∀ r, r ∉ ds → (ss.regs r).atom = true) :
    (T.internSt ss ds).2.Inv (T.internSt ss ds).1.ents.size := by
  have e1 := Tbl.internRegs_snd T ss ds
  have hsz := Tbl.internRegs_size_le T ss ds
  obtain ⟨i1, i2, i3⟩ := Tbl.internRegs_inv T ss ds h.1
  simp only [Tbl.internSt]
  generalize hp : T.internRegs ss ds = p at e1 hsz i1 i2 i3
  obtain ⟨P, ps⟩ := p
  dsimp only at e1 hsz i1 i2 i3 ⊢
  have hc : ps.cf.refsLt P.ents.size = true := by
    rw [e1]; exact STerm.refsLt_mono hsz _ h.2.2.2.1
  have hc' := Tbl.intern_refsLt P ps.cf hc
  have ho : ps.of.refsLt (P.intern ps.cf).1.ents.size = true := by
    rw [e1]; exact STerm.refsLt_mono (hsz.trans (Tbl.intern_size_le _ _)) _ h.2.2.2.2
  have ho' := Tbl.intern_refsLt _ ps.of ho
  have s1 := Tbl.intern_size_le P ps.cf
  have s2 := Tbl.intern_size_le (P.intern ps.cf).1 ps.of
  refine ⟨⟨fun r => STerm.refsLt_mono (s1.trans s2) _ (i1 r), fun q => ?_, ?_,
    STerm.refsLt_mono s2 _ hc'.1, ho'.1⟩, fun r => ?_, hc'.2, ho'.2⟩
  · have hpa : ps.arrs = ss.arrs := by rw [e1]
    simp only [hpa]
    exact SArr.refsLt_mono (hsz.trans (s1.trans s2)) _ (h.2.1 q)
  · have hpz : ps.zf = ss.zf := by rw [e1]
    simp only [hpz]
    exact (SSt.RefsLt.mono (hsz.trans (s1.trans s2)) h).2.2.1
  · by_cases hr : r ∈ ds
    · exact i2 r hr
    · rw [i3 r hr]; exact ha r hr

/-! ## 5. Runs in lockstep -/

/-- The description `o` with the guards `g` put before its own. -/
def SOut.after (g : List SG) : SOut → SOut
  | .ok s g2 => .ok s (g ++ g2)
  | .fail => .fail
  | .unk => .unk

/-- A shared run whose description has the guards `g` put before its own. -/
def runAfter (g : List SG) (r : Tbl × SOut) : Tbl × SOut := (r.1, r.2.after g)

/-- The shared run of a list after a shared run that ended in `r`. -/
def runThen (l : List LinstrRM) (r : Tbl × SOut) : Tbl × SOut :=
  match r.2 with
  | .ok s g => runAfter g (tRun l s r.1)
  | .fail => (r.1, .fail)
  | .unk => (r.1, .unk)

theorem tRun_cons (i : LinstrRM) (is : List LinstrRM) (ss : SSt) (T : Tbl) :
    tRun (i :: is) ss T =
      match symStep i ss with
      | .ok s1 g1 =>
          runAfter g1 (tRun is (T.internSt s1 (s1.wr.take (s1.wr.length - ss.wr.length))).2
            (T.internSt s1 (s1.wr.take (s1.wr.length - ss.wr.length))).1)
      | .fail => (T, .fail)
      | .unk => (T, .unk) := by
  cases h : symStep i ss with
  | ok s1 g1 =>
      simp only [tRun, h]
      generalize tRun is _ _ = r
      obtain ⟨T1, o⟩ := r
      cases o <;> rfl
  | fail => simp only [tRun, h]
  | unk => simp only [tRun, h]

theorem SOut.after_after (g g2 : List SG) (o : SOut) :
    (o.after g2).after g = o.after (g ++ g2) := by
  cases o <;> simp [SOut.after]

theorem tRun_append : ∀ (l1 l2 : List LinstrRM) (ss : SSt) (T : Tbl),
    tRun (l1 ++ l2) ss T = runThen l2 (tRun l1 ss T)
  | [], l2, ss, T => by
      simp only [List.nil_append, tRun, runThen, runAfter, List.nil_append]
      generalize tRun l2 ss T = r
      obtain ⟨T1, o⟩ := r
      cases o <;> rfl
  | i :: l1, l2, ss, T => by
      rw [List.cons_append, tRun_cons, tRun_cons]
      split
      · rw [tRun_append l1 l2]
        generalize tRun l1 _ _ = r
        obtain ⟨T1, o⟩ := r
        cases o with
        | ok s g =>
            simp only [runThen, runAfter, SOut.after]
            generalize tRun l2 s T1 = r2
            obtain ⟨T2, o2⟩ := r2
            cases o2 <;> simp
        | fail => rfl
        | unk => rfl
      · rfl
      · rfl

theorem tRun_sub : ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), T.Sub (tRun is ss T).1
  | [], _, T => Tbl.Sub.refl T
  | i :: is, ss, T => by
      rw [tRun_cons]
      split
      · exact (Tbl.internSt_sub _ _ _).trans (tRun_sub is _ _)
      · exact Tbl.Sub.refl T
      · exact Tbl.Sub.refl T

/-- The source description `o` and the target run `r` agree: both succeed, the target in the
    table `T'`, in states with one word for every name and with equal guards; or both fail;
    or both are outside the fragment. -/
def Res (T' : Tbl) : SOut → Tbl × SOut → Prop
  | .ok s g, (T'', .ok s' g') => T'' = T' ∧ s.Eqv s' ∧ g = g'
  | .fail, (_, .fail) => True
  | .unk, (_, .unk) => True
  | _, _ => False

/-- The target instructions `js` simulate the source instruction `i` over the shared table:
    from states with one word for every name, the run of `js` in a table holding what the run
    of `i` interns agrees with the run of `i`. -/
def Chunk (i : LinstrRM) (js : List LinstrRM) : Prop :=
  ∀ (ss ss' : SSt) (T T' : Tbl), ss.Eqv ss' → ss.Inv T.ents.size → (tRun [i] ss T).1.Sub T' →
    Res T' (tRun [i] ss T).2 (tRun js ss' T')

/-- One source step and one target step with agreeing descriptions run in agreement over the
    shared table. -/
theorem tRun_single_res {i j : LinstrRM} {ss ss1 : SSt} {T T' : Tbl}
    (hrel : SOut.Rel ss ss1 (symStep i ss) (symStep j ss1)) (hI : ss.Inv T.ents.size)
    (hS : (tRun [i] ss T).1.Sub T') : Res T' (tRun [i] ss T).2 (tRun [j] ss1 T') := by
  simp only [tRun] at hS ⊢
  cases hs : symStep i ss with
  | ok s1 g1 =>
      cases ht : symStep j ss1 with
      | ok t1 h1 =>
          rw [hs, ht] at hrel
          obtain ⟨e1, hg, ds, hw1, hw2⟩ := hrel
          subst hg
          rw [hs] at hS
          simp only [SSt.Frm.ds_eq hw1, SSt.Frm.ds_eq hw2] at hS ⊢
          obtain ⟨s'', hs'', e'', -, -⟩ :=
            Tbl.internSt_rerun e1 ds (symStep_refsLt i hI.1 hs).1 hS
          rw [hs'']
          exact ⟨rfl, e'', rfl⟩
      | fail => rw [hs, ht] at hrel; cases hrel
      | unk => rw [hs, ht] at hrel; cases hrel
  | fail =>
      cases ht : symStep j ss1 with
      | fail => trivial
      | _ => rw [hs, ht] at hrel; cases hrel
  | unk =>
      cases ht : symStep j ss1 with
      | unk => trivial
      | _ => rw [hs, ht] at hrel; cases hrel

/-- An instruction is simulated by itself. -/
theorem chunk_self (i : LinstrRM) : Chunk i [i] :=
  fun _ _ _ _ e hI hS => tRun_single_res (symStep_eqv e i) hI hS

/-! ## 6. A copy into the destination before a two-source operation -/

/-- The register file `R` after the copy of `x` into `d`. -/
def copyRegs (R : String → STerm) (d x : String) : String → STerm :=
  fun r => if r = d then R x else R r

/-- An operand that does not read the register `d`. -/
def avoidsReg (d : String) (b : LOperand) : Prop :=
  d ∉ LprogLeak.opNames b

theorem copyRegs_avoid_reg {R : String → STerm} {d x y : String}
    (hb : avoidsReg d (.reg y)) : copyRegs R d x y = R y := by
  have : y ≠ d := fun h => hb (by simp [LprogLeak.opNames, h])
  simp only [copyRegs, if_neg this]

theorem copyRegs_self (R : String → STerm) (d x : String) : copyRegs R d x d = R x := by
  simp [copyRegs]

theorem symOp64_copy_src (R : String → STerm) (d x : String) :
    symOp64 (copyRegs R d x) (.reg d) = symOp64 R (.reg x) := by
  simp [symOp64, copyRegs]

theorem symOp64_copy_avoid (R : String → STerm) {d x : String} {b : LOperand}
    (hb : avoidsReg d b) : symOp64 (copyRegs R d x) b = symOp64 R b := by
  cases b with
  | reg y => simp only [symOp64, copyRegs_avoid_reg hb]
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl


theorem symN_copy (R : String → STerm) (d x opn : String) (b : LOperand)
    (hb : avoidsReg d b) :
    symN (.Lopn [.reg d] opn [.reg x, b]) R =
      symN (.Lopn [.reg d] opn [.reg d, b]) (copyRegs R d x) := by
  cases b with
  | reg y =>
      have hy : y ≠ d := fun h => hb (by simp [LprogLeak.opNames, h])
      have h1 : ∀ a, commSwap opn d a y = false := fun a => by simp [commSwap, hy]
      dsimp only [symN]
      simp only [h1, Bool.false_eq_true, ↓reduceIte]
      rw [copyRegs_avoid_reg hb, copyRegs_self]
  | imm n => dsimp only [symN]; rw [copyRegs_self]
  | arr _ _ => dsimp only [symN]
  | arrIdx _ _ _ => dsimp only [symN]

/-- A two-source instruction is not an immediate move. -/
theorem movImmStruct?_pair (ds : List LOperand) (opn : String) (a b : LOperand) :
    JasminLsemCast.movImmStruct? (.Lopn ds opn [a, b]) = none := by
  unfold JasminLsemCast.movImmStruct?
  split <;> simp_all

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (sarStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
  (mulhiStruct? adcxStruct? adcxhiStruct? sbbStruct? sbbhiStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (castStruct? movImmStruct?) in
theorem symCast_copy (R : String → STerm) (d x opn : String) (b : LOperand)
    (cd : Option Nat) (hb : avoidsReg d b) :
    symCast (.Lopn [.reg d] opn [.reg x, b], cd) R =
      symCast (.Lopn [.reg d] opn [.reg d, b], cd) (copyRegs R d x) := by
  have hN := symN_copy R d x opn b hb
  cases b with
  | reg y =>
      have hy : copyRegs R d x y = R y := copyRegs_avoid_reg hb
      have hd : copyRegs R d x d = R x := copyRegs_self R d x
      simp only [symCast, movImmStruct?_pair]; dsimp only [castStruct?, symMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
        sbbStruct?, sbbhiStruct?, symSh, sarStruct?]
      split_ifs <;> simp_all
  | imm n =>
      simp only [symCast, movImmStruct?_pair]; dsimp only [castStruct?, symMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
        sbbStruct?, sbbhiStruct?, symSh, sarStruct?]
      split_ifs <;> simp_all [copyRegs_self]
  | arr _ _ =>
      simp only [symCast, movImmStruct?_pair]; dsimp only [castStruct?, symMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
        sbbStruct?, sbbhiStruct?, symSh, sarStruct?]
      exact hN
  | arrIdx _ _ _ =>
      simp only [symCast, movImmStruct?_pair]; dsimp only [castStruct?, symMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
        sbbStruct?, sbbhiStruct?, symSh, sarStruct?]
      exact hN

/-- A register-file description that writes the register `d`, or fails, or is outside the
    fragment. -/
def ROut.WritesOnly (d : String) : ROut → Prop
  | .set d' _ _ => d' = d
  | .nop => False
  | _ => True

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (sarStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
  (mulhiStruct? adcxStruct? adcxhiStruct? sbbStruct? sbbhiStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (castStruct? movImmStruct?) in
theorem symCast_writesOnly (R : String → STerm) (d opn : String) (a b : LOperand)
    (cd : Option Nat) : (symCast (.Lopn [.reg d] opn [a, b], cd) R).WritesOnly d := by
  cases a <;> cases b <;> simp only [symCast, movImmStruct?_pair] <;>
    dsimp only [castStruct?, symMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
      sbbStruct?, sbbhiStruct?, symSh, sarStruct?, symN] <;>
    (try split_ifs) <;> trivial

theorem SSt.Eqv.setR_copy {ss ss' : SSt} (e : ss.Eqv ss') (d x : String) (t : STerm) :
    (ss.setR d t).Eqv ((ss'.setR d (ss'.regs x)).setR d t) := by
  obtain ⟨hR, hA, hZ, hC, hO⟩ := e
  refine ⟨?_, hA, hZ, hC, hO⟩
  funext r
  simp only [SSt.setR, hR]
  split <;> rfl

theorem liftR_copy {ss ss' : SSt} (e : ss.Eqv ss') (d x : String) {o : ROut}
    (ho : o.WritesOnly d) :
    SOut.Rel ss (ss'.setR d (ss'.regs x)) (liftR ss o) (liftR (ss'.setR d (ss'.regs x)) o) := by
  cases o with
  | set d' t gs =>
      simp only [ROut.WritesOnly] at ho
      subst ho
      exact ⟨e.setR_copy d' x t, rfl, [d'], rfl, rfl⟩
  | nop => cases ho
  | fail => trivial
  | unk => trivial

theorem copyRegs_eq {ss ss' : SSt} (e : ss.Eqv ss') (d x : String) :
    (ss'.setR d (ss'.regs x)).regs = copyRegs ss.regs d x := by
  funext r
  simp only [SSt.setR, copyRegs, e.1]

theorem symMem_copy {ss ss' : SSt} (e : ss.Eqv ss') (d x opn : String) (b : LOperand)
    (tag : MemTag) (hb : avoidsReg d b) :
    SOut.Rel ss (ss'.setR d (ss'.regs x))
      (symMem (.Lopn [.reg d] opn [.reg x, b], tag) ss)
      (symMem (.Lopn [.reg d] opn [.reg d, b], tag) (ss'.setR d (ss'.regs x))) := by
  have hc : ∀ cd, symCast (.Lopn [.reg d] opn [.reg d, b], cd) (ss'.setR d (ss'.regs x)).regs =
      symCast (.Lopn [.reg d] opn [.reg x, b], cd) ss.regs := fun cd => by
    rw [copyRegs_eq e, ← symCast_copy _ _ _ _ _ _ hb]
  cases tag with
  | load w n =>
      have h1 : loadStruct? (.Lopn [.reg d] opn [.reg x, b]) = none := rfl
      have h2 : loadStruct? (.Lopn [.reg d] opn [.reg d, b]) = none := rfl
      simp only [symMem, h1, h2, hc]
      exact liftR_copy e d x (symCast_writesOnly _ _ _ _ _ _)
  | store w n =>
      have h1 : storeStruct? (.Lopn [.reg d] opn [.reg x, b]) = none := by
        cases b <;> rfl
      have h2 : storeStruct? (.Lopn [.reg d] opn [.reg d, b]) = none := by
        cases b <;> rfl
      simp only [symMem, h1, h2, hc]
      exact liftR_copy e d x (symCast_writesOnly _ _ _ _ _ _)
  | loadC => trivial
  | storeC => trivial
  | reg cd =>
      simp only [symMem, hc]
      exact liftR_copy e d x (symCast_writesOnly _ _ _ _ _ _)

theorem aluFlT_copy {ss ss' : SSt} (e : ss.Eqv ss') (d x opn : String) (b : LOperand)
    (tag : MemTag) (hb : avoidsReg d b) (bo : Bool) :
    aluFlT (.Lopn [.reg d] opn [.reg d, b], tag) (ss'.setR d (ss'.regs x)) bo =
      aluFlT (.Lopn [.reg d] opn [.reg x, b], tag) ss bo := by
  have hc : (ss'.setR d (ss'.regs x)).cf = ss.cf := e.2.2.2.1.symm
  have ho : (ss'.setR d (ss'.regs x)).of = ss.of := e.2.2.2.2.symm
  have hsw : ∀ a, aluSwap (.Lopn [.reg d] opn [.reg a, b], tag) = false := fun a => by
    cases b with
    | reg y =>
        have hy : y ≠ d := fun h => hb (by simp [LprogLeak.opNames, h])
        simp [aluSwap, commSwap, hy]
    | imm _ => rfl
    | arr _ _ => rfl
    | arrIdx _ _ _ => rfl
  simp only [aluFlT, hsw, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [aluFlagOp?, copyRegs_eq e, hc, ho]
  split_ifs <;> simp only [symOp64_copy_src, symOp64_copy_avoid _ hb]

theorem aluFl_copy {ss ss' : SSt} (e : ss.Eqv ss') (d x opn : String) (b : LOperand)
    (tag : MemTag) (hb : avoidsReg d b) {o o' : SOut}
    (h : SOut.Rel ss (ss'.setR d (ss'.regs x)) o o') :
    SOut.Rel ss (ss'.setR d (ss'.regs x)) (aluFl (.Lopn [.reg d] opn [.reg x, b], tag) ss o)
      (aluFl (.Lopn [.reg d] opn [.reg d, b], tag) (ss'.setR d (ss'.regs x)) o') := by
  cases o <;> cases o' <;> simp only [SOut.Rel, aluFl] at h ⊢
  obtain ⟨⟨hR, hA, hZ, -, -⟩, hg, hw⟩ := h
  refine ⟨⟨hR, hA, hZ, ?_, ?_⟩, hg, hw⟩ <;> dsimp only <;> rw [aluFlT_copy e d x opn b tag hb]

theorem symCarry_copy {ss ss' : SSt} (e : ss.Eqv ss') (op : CarryOp) (d x : String)
    (b : LOperand) (hb : avoidsReg d b) :
    SOut.Rel ss (ss'.setR d (ss'.regs x)) (symCarry op d (.reg x) b ss)
      (symCarry op d (.reg d) b (ss'.setR d (ss'.regs x))) := by
  have hc : (ss'.setR d (ss'.regs x)).cf = ss.cf := e.2.2.2.1.symm
  have ho : (ss'.setR d (ss'.regs x)).of = ss.of := e.2.2.2.2.symm
  unfold symCarry
  rw [copyRegs_eq e, symOp64_copy_src, symOp64_copy_avoid _ hb, hc, ho]
  split
  · cases op
    all_goals
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl, [d], rfl, rfl⟩
      · exact (e.setR_copy d x _).1
      · simp only [SSt.setR, e.2.1]
      · simp only [SSt.setR, e.2.2.1]
      · simp only [SSt.setR, e.2.2.2.1]
      · simp only [SSt.setR, e.2.2.2.2]
  · trivial

/-- **The copy and the operation on the destination describe the operation on the copied
    register.** For `i = Lopn [d] opn [x, b]` and `j = Lopn [d] opn [d, b]`, with `b` not
    reading `d` and `opn` not the flag `CMP`, the step of `i` from `ss` and the step of `j`
    after the copy of `x` into `d` agree. -/
theorem symStep_copy {ss ss' : SSt} (e : ss.Eqv ss') (d x opn : String) (b : LOperand)
    (tag : MemTag) (hb : avoidsReg d b) (hcmp : opn ≠ withWidthTag 64 "CMP") :
    SOut.Rel ss (ss'.setR d (ss'.regs x))
      (symStep (.Lopn [.reg d] opn [.reg x, b], tag) ss)
      (symStep (.Lopn [.reg d] opn [.reg d, b], tag) (ss'.setR d (ss'.regs x))) := by
  unfold symStep
  simp only [cmpArgs?, hcmp, if_false, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?]
  split_ifs <;> dsimp only <;>
    first
    | exact symCarry_copy e _ d x b hb
    | exact aluFl_copy e d x opn b tag hb (symMem_copy e d x opn b tag hb)
    | (simp only [symWide, copyRegs_eq e, symOp64_copy_avoid _ hb]
       split
       · exact ⟨e.setR_copy d x _, rfl, [d], rfl, rfl⟩
       · trivial)

theorem SOut.after_nil (o : SOut) : o.after [] = o := by
  cases o <;> rfl

/-- **The copy chunk.** The register copy `mv d, x` followed by `opn d, [d, b]` simulates
    `opn d, [x, b]`, when `b` does not read `d` and `opn` is not the flag `CMP`. -/
theorem chunk_copy (d x opn mv : String) (b : LOperand) (tag tagm : MemTag)
    (hmv : stripWidthTag mv = "MOV") (hb : avoidsReg d b) (hcmp : opn ≠ withWidthTag 64 "CMP") :
    Chunk (.Lopn [.reg d] opn [.reg x, b], tag)
      [(.Lopn [.reg d] mv [.reg x], tagm), (.Lopn [.reg d] opn [.reg d, b], tag)] := by
  intro ss ss' T T' e hI hS
  have hI' := hI.of_eqv e
  have hm : symStep (.Lopn [.reg d] mv [.reg x], tagm) ss' = .ok (ss'.setR d (ss'.regs x)) [] := by
    simp [symStep, cmpArgs?, movRegArgs?, hmv]
  have hint : T'.internSt (ss'.setR d (ss'.regs x)) [d] = (T', ss'.setR d (ss'.regs x)) := by
    simp only [Tbl.internSt, Tbl.internRegs]
    simp only [SSt.setR, ite_true, Tbl.intern_atom T' (hI'.2.1 x), Tbl.intern_atom T' hI'.2.2.1,
      Tbl.intern_atom T' hI'.2.2.2, Prod.mk.injEq, true_and]
    congr 1
    funext r
    split <;> simp_all
  have hrun : tRun [(.Lopn [.reg d] mv [.reg x], tagm)] ss' T' =
      (T', .ok (ss'.setR d (ss'.regs x)) []) := by
    rw [tRun_cons, hm]
    have hw : (ss'.setR d (ss'.regs x)).wr.take
        ((ss'.setR d (ss'.regs x)).wr.length - ss'.wr.length) = [d] :=
      SSt.Frm.ds_eq (ds := [d]) rfl
    simp only [hw, hint, runAfter, tRun, SOut.after, List.append_nil]
  have hres := tRun_single_res (symStep_copy e d x opn b tag hb hcmp) hI hS
  rw [show [(LinstrR.Lopn [.reg d] mv [.reg x], tagm), (LinstrR.Lopn [.reg d] opn [.reg d, b], tag)]
      = [(LinstrR.Lopn [.reg d] mv [.reg x], tagm)] ++ [(LinstrR.Lopn [.reg d] opn [.reg d, b], tag)]
      from rfl, tRun_append, hrun]
  simp only [runThen, runAfter, SOut.after_nil]
  exact hres

/-- **Runs in lockstep.** If every source instruction is simulated by its target chunk, the
    run of the source from an interned state and the run of the concatenated chunks, in a
    table holding what the source run interns, agree. -/
theorem tRun_lock (f : LinstrRM → List LinstrRM) : ∀ (is : List LinstrRM),
    (∀ i ∈ is, Chunk i (f i)) → ∀ (ss ss' : SSt) (T T' : Tbl), ss.Eqv ss' →
      ss.Inv T.ents.size → (tRun is ss T).1.Sub T' →
        Res T' (tRun is ss T).2 (tRun (is.flatMap f) ss' T')
  | [], _, ss, ss', T, T', e, _, _ => ⟨rfl, e, rfl⟩
  | i :: is, hf, ss, ss', T, T', e, hI, hS => by
      have hc := hf i (List.mem_cons_self ..)
      have hc' := hc ss ss' T T' e hI
      rw [List.flatMap_cons, tRun_append]
      rw [tRun_cons] at hS ⊢
      rw [tRun_cons] at hc'
      simp only [tRun] at hc'
      cases hs : symStep i ss with
      | ok s1 g1 =>
          rw [hs] at hS hc'
          dsimp only at hS hc' ⊢
          generalize hds : s1.wr.take (s1.wr.length - ss.wr.length) = ds at hS hc' ⊢
          generalize hp : T.internSt s1 ds = p at hS hc' ⊢
          obtain ⟨P, ps⟩ := p
          simp only [runAfter] at hS hc' ⊢
          have hc2 := hc' ((tRun_sub is ps P).trans hS)
          generalize hq : tRun (f i) ss' T' = q at hc2 ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo with
          | ok s'' g'' =>
              obtain ⟨hQ, e2, hg⟩ := hc2
              rw [hQ] at hq
              simp only [List.append_nil] at hg
              subst hg
              have hR1 := symStep_refsLt i hI.1 hs
              obtain ⟨ds0, hw0, hr0⟩ := symStep_frm i hs
              have hd0 : ds = ds0 := hds ▸ SSt.Frm.ds_eq hw0
              have hI2 : ps.Inv P.ents.size := by
                have := Tbl.internSt_inv (T := T) ds hR1.1 (fun r hr => by
                  rw [hr0 r (hd0 ▸ hr)]; exact hI.2.1 r)
                rw [hp] at this
                exact this
              have ih := tRun_lock f is (fun j hj => hf j (List.mem_cons_of_mem _ hj)) ps s''
                P T' e2 hI2 hS
              rw [hQ]
              simp only [runThen, runAfter]
              generalize tRun is ps P = r1 at ih ⊢
              generalize tRun (is.flatMap f) s'' T' = r2 at ih ⊢
              obtain ⟨R1, o1⟩ := r1
              obtain ⟨R2, o2⟩ := r2
              cases o1 <;> cases o2 <;> simp_all [Res, SOut.after]
          | fail => simp [Res, SOut.after] at hc2
          | unk => simp [Res, SOut.after] at hc2
      | fail =>
          rw [hs] at hc'
          dsimp only at hc' ⊢
          generalize tRun (f i) ss' T' = q at hc' ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo <;> simp_all [Res, runThen]
      | unk =>
          rw [hs] at hc'
          dsimp only at hc' ⊢
          generalize tRun (f i) ss' T' = q at hc' ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo <;> simp_all [Res, runThen]

/-! ## 7. Two-address legalisation -/

open TwoAddrLegalize in
/-- The instruction `opn d, [x, b]` is legalised by the copy route: it needs the tie,
    `x ≠ d`, the copy mnemonic exists, the base is not `CMP` or `TEST`, `b` does not read `d`,
    and `d`, `x` are not both memory names. -/
def copyRouteOk : LinstrR → Bool
  | .Lopn [.reg d] opn [.reg x, b] =>
      needsTie opn b && x != d && (movFor opn).isSome && tieBase opn != "CMP" &&
        tieBase opn != "TEST" && !(LprogLeak.opNames b).contains d &&
        !(LprogAsmPrinter.isMemOperand (.reg d) && LprogAsmPrinter.isMemOperand (.reg x))
  | _ => false

/-- The well-formedness of an instruction for two-address legalisation: it satisfies the
    printer's precondition, or the copy route legalises it. -/
def twoAddrWF (x : LinstrR) : Bool := TwoAddrLegalize.tiedOk x || copyRouteOk x

/-- The copy-route image of an instruction: `mov d, x; opn d, [d, b]`. -/
def copyPair : LinstrR → List LinstrR
  | .Lopn [.reg d] opn [a, b] =>
      match TwoAddrLegalize.movFor opn with
      | some m => [.Lopn [.reg d] m [a], .Lopn [.reg d] opn [.reg d, b]]
      | none => [.Lopn [.reg d] opn [a, b]]
  | x => [x]

theorem legalizeInstr_copy (ok : Bool) (i : Linstr) (h : copyRouteOk i.li_i = true) :
    (TwoAddrLegalize.legalizeInstr ok i).map Linstr.li_i = copyPair i.li_i := by
  obtain ⟨ii, x⟩ := i
  match x, h with
  | .Lopn [.reg d] opn [.reg y, b], h =>
      simp only [copyRouteOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isSome_iff_exists,
        Bool.not_eq_true'] at h
      obtain ⟨⟨⟨⟨⟨⟨hn, hyd⟩, ⟨m, hm⟩⟩, hc⟩, ht⟩, hb⟩, hmem⟩ := h
      have hyd' : (LOperand.reg y != LOperand.reg d) = true := by simpa using hyd
      simp only [TwoAddrLegalize.legalizeInstr, hn, hyd', Bool.and_self, ↓reduceIte, hm,
        TwoAddrLegalize.isRegOrImm, Bool.not_true, Bool.false_eq_true, hb, Bool.not_false, hmem,
        copyPair]
      rw [if_neg (by simp [hc, ht])]
      rfl

/-- The target chunk of a typed instruction under two-address legalisation, with the memory
    tags of the typing `tg`. -/
def twoAddrChunk (tg : LinstrR → MemTag) (p : LinstrRM) : List LinstrRM :=
  if TwoAddrLegalize.tiedOk p.1 then [p] else (copyPair p.1).map fun x => (x, tg x)

/-- A typing that gives a two-source operation one tag whatever its first source. -/
def TagFirstSrc (tg : LinstrR → MemTag) : Prop :=
  ∀ (d opn : String) (a a' b : LOperand),
    tg (.Lopn [.reg d] opn [a, b]) = tg (.Lopn [.reg d] opn [a', b])

theorem tagFirstSrc_const (τ : MemTag) : TagFirstSrc (fun _ => τ) := fun _ _ _ _ _ => rfl

theorem twoAddrBody_typed (tg : LinstrR → MemTag) (body : Lcmd)
    (hwf : ∀ i ∈ body, twoAddrWF i.li_i = true) :
    typeBody tg (TwoAddrLegalize.twoAddrBody body) =
      (typeBody tg body).flatMap (twoAddrChunk tg) := by
  unfold TwoAddrLegalize.twoAddrBody LegalizeShiftImm.legalizeBody typeBody
  rw [List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun i hi => ?_
  have hw := hwf i hi
  simp only [twoAddrWF, Bool.or_eq_true] at hw
  by_cases ht : TwoAddrLegalize.tiedOk i.li_i = true
  · rw [TwoAddrLegalize.legalizeInstr_of_tiedOk _ i ht]
    simp [twoAddrChunk, ht]
  · have hc : copyRouteOk i.li_i = true := hw.resolve_left ht
    have e := legalizeInstr_copy (TwoAddrLegalize.bodyAvoids body) i hc
    simp only [twoAddrChunk, ht, Bool.false_eq_true, ↓reduceIte]
    rw [← e, List.map_map]
    rfl

theorem tieBase_cmp64 : TwoAddrLegalize.tieBase (withWidthTag 64 "CMP") = "CMP" := by
  decide +kernel

/-- Every well-formed typed instruction is simulated by its chunk. -/
theorem chunk_twoAddr {tg : LinstrR → MemTag} (htg : TagFirstSrc tg) {x : LinstrR}
    (h : twoAddrWF x = true) : Chunk (x, tg x) (twoAddrChunk tg (x, tg x)) := by
  by_cases ht : TwoAddrLegalize.tiedOk x = true
  · simp only [twoAddrChunk, ht, ↓reduceIte]
    exact chunk_self _
  · have hc : copyRouteOk x = true := by
      simp only [twoAddrWF, Bool.or_eq_true] at h
      exact h.resolve_left ht
    simp only [twoAddrChunk, ht, Bool.false_eq_true, ↓reduceIte]
    match x, hc with
    | .Lopn [.reg d] opn [.reg y, b], hc =>
        simp only [copyRouteOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isSome_iff_exists]
          at hc
        obtain ⟨⟨⟨⟨⟨⟨-, -⟩, ⟨m, hm⟩⟩, hcmp⟩, -⟩, hb⟩, -⟩ := hc
        simp only [copyPair, hm, List.map_cons, List.map_nil]
        rw [htg d opn (.reg d) (.reg y) b]
        refine chunk_copy d y opn m b _ _ (TwoAddrLegalize.stripWidthTag_movFor hm) ?_ ?_
        · simpa [avoidsReg] using hb
        · rintro rfl
          exact hcmp tieBase_cmp64

/-! ## 8. The graph of a straight-line body -/

section Straight

open AllocCheck.LcmdCFG

/-- An instruction that neither ends nor starts a block and that `cfgOf` accepts. -/
def straightR (x : LinstrR) : Bool := !isTermR x && !isLabelR x && !isBarredR x

theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → β) :
    (forIn (m := Id) l init fun a b => pure (ForInStep.yield (f a b))) =
      l.foldl (fun b a => f a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => simp only [List.forIn_cons, List.foldl_cons]; exact ih (f a init)

theorem isLeader_straight {w : Array LinstrR} (hs : ∀ x ∈ w, straightR x = true) (pc : Nat) :
    isLeader w pc = (pc == 0) := by
  have hl : (w[pc]?.any isLabelR) = false := by
    cases h : w[pc]? with
    | none => rfl
    | some x =>
        have := hs x (Array.mem_of_getElem? h)
        simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
        simp [this.1.2]
  have ht : ∀ p : Nat, (w[p]?.any isTermR) = false := fun p => by
    cases h : w[p]? with
    | none => rfl
    | some x =>
        have := hs x (Array.mem_of_getElem? h)
        simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
        simp [this.1.1]
  unfold isLeader
  rw [hl]
  cases pc with
  | zero => rfl
  | succ p => simp [ht p]

theorem leaderStarts_straight {w : Array LinstrR} (hs : ∀ x ∈ w, straightR x = true)
    (hn : 0 < w.size) : leaderStarts w = #[0] := by
  unfold leaderStarts
  simp only [Id.run]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hb : (fun pc (s : Array Nat) => if isLeader w pc = true then
      (pure (ForInStep.yield (s.push pc)) : Id (ForInStep (Array Nat)))
      else pure (ForInStep.yield s)) =
      fun pc s => pure (ForInStep.yield (if (pc == 0) = true then s.push pc else s)) := by
    funext pc s
    rw [isLeader_straight hs]
    split <;> rfl
  rw [hb, forIn_id_yield]
  have hsz : [:w.size].size = w.size := by simp [Std.Legacy.Range.size]
  rw [hsz]
  obtain ⟨n, hn'⟩ : ∃ n, w.size = n + 1 := ⟨w.size - 1, by omega⟩
  rw [hn', List.range'_succ]
  have key : ∀ (l : List Nat) (s : Array Nat), (∀ a ∈ l, a ≠ 0) →
      l.foldl (fun b a => if (a == 0) = true then b.push a else b) s = s := by
    intro l
    induction l with
    | nil => intro s _; rfl
    | cons a l ih =>
        intro s h
        simp only [List.foldl_cons]
        have ha : (a == 0) = false := by simpa using h a (List.mem_cons_self ..)
        rw [ha]
        exact ih s (fun b hb => h b (List.mem_cons_of_mem _ hb))
  simp only [List.foldl_cons, beq_self_eq_true, ↓reduceIte]
  rw [key _ _ (fun a ha => by simp [List.mem_range'] at ha; omega)]
  rfl

theorem blockIndex_one (n : Nat) : blockIndex n #[0] = Array.replicate n 0 := by
  unfold blockIndex
  simp only [Id.run]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hb : (fun (pc : Nat) (s : Array Nat × Nat) =>
      if (decide (s.2 + 1 < (#[0] : Array Nat).size) && (#[0] : Array Nat)[s.2 + 1]! == pc) = true
      then (pure (ForInStep.yield (s.1.push (s.2 + 1), s.2 + 1)) : Id (ForInStep (Array Nat × Nat)))
      else pure (ForInStep.yield (s.1.push s.2, s.2))) =
      fun pc s => pure (ForInStep.yield
        (if (decide (s.2 + 1 < (#[0] : Array Nat).size) && (#[0] : Array Nat)[s.2 + 1]! == pc) = true
          then (s.1.push (s.2 + 1), s.2 + 1) else (s.1.push s.2, s.2))) := by
    funext pc s
    split <;> rfl
  rw [hb, forIn_id_yield]
  have key : ∀ (l : List Nat) (a : Array Nat),
      l.foldl (fun b pc =>
        if (decide (b.2 + 1 < (#[0] : Array Nat).size) && (#[0] : Array Nat)[b.2 + 1]! == pc) = true
          then (b.1.push (b.2 + 1), b.2 + 1) else (b.1.push b.2, b.2)) (a, 0) =
        (a ++ Array.replicate l.length 0, 0) := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons p l ih =>
        intro a
        rw [List.foldl_cons, if_neg (by simp), ih]
        congr 1
        rw [Array.push_eq_append, Array.append_assoc]
        congr 1
        apply Array.toList_inj.mp
        simp [List.replicate_succ]
  simp only [Std.Legacy.Range.size]
  rw [key]
  show Array.mkEmpty n ++ Array.replicate (List.range' 0 ((n - 0 + 1 - 1) / 1)).length 0 = _
  simp [Array.mkEmpty]

/-- The graph of a straight-line body of `n` instructions: one block, falling off the end. -/
def straightCFG (n : Nat) : CFG :=
  { blocks := #[{ start := 0, stop := n, term := .fall none }],
    blockOf := Array.replicate n 0, preds := #[[]] }

theorem build_straight {w : Array LinstrR} (hs : ∀ x ∈ w, straightR x = true)
    (hn : 0 < w.size) : build w = some (straightCFG w.size) := by
  unfold build
  rw [leaderStarts_straight hs hn]
  obtain ⟨x, hx⟩ : ∃ x, w[w.size - 1]? = some x := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  have hxs := hs x (Array.mem_of_getElem? hx)
  simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at hxs
  simp only [blockIndex_one, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.size_toArray, List.length_cons, List.length_nil]
  simp [hx]
  cases x <;> simp_all [isTermR, straightCFG, Term.succs]

theorem hasDupLabel_straight {w : Array LinstrR} (hs : ∀ x ∈ w, straightR x = true) :
    hasDupLabel w = false := by
  unfold hasDupLabel
  simp only [Id.run]
  rw [← Array.forIn_toList]
  have key : ∀ (f : LinstrR → Option Bool × Std.HashSet LLabel →
      Id (ForInStep (Option Bool × Std.HashSet LLabel))),
      (∀ i s, isLabelR i = false → f i s = pure (ForInStep.yield (none, s.2))) →
      ∀ (l : List LinstrR) (S : Std.HashSet LLabel), (∀ x ∈ l, isLabelR x = false) →
      forIn (m := Id) l ((none : Option Bool), S) f = (none, S) := by
    intro f hf l
    induction l with
    | nil => intro S _; rfl
    | cons a l ih =>
        intro S h
        rw [List.forIn_cons, hf a _ (h a (List.mem_cons_self ..))]
        exact ih S (fun x hx => h x (List.mem_cons_of_mem _ hx))
  rw [key _ (fun i s hi => by cases i <;> first | rfl | simp [isLabelR] at hi) w.toList ∅
    (fun x hx => by
    have := hs x (Array.mem_toList_iff.mp hx)
    simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1.2)]
  rfl

/-- **The graph of a straight-line body.** A non-empty body without terminators, labels and
    barred instructions has one block, which falls off the end. -/
theorem cfgOf_straight {wl : List LinstrR} (hne : wl ≠ [])
    (hs : ∀ x ∈ wl, straightR x = true) : cfgOf wl = some (straightCFG wl.length) := by
  have hs' : ∀ x ∈ wl.toArray, straightR x = true := fun x hx => hs x (by simpa using hx)
  have hn : 0 < wl.toArray.size := by
    simp only [List.size_toArray]
    exact List.length_pos_iff.mpr hne
  have hx : ∀ i : Nat, ∀ x, wl.toArray[i]? = some x →
      isTermR x = false ∧ isLabelR x = false ∧ isBarredR x = false := fun i x h => by
    have := hs' x (Array.mem_of_getElem? h)
    simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  unfold cfgOf
  simp only [build_straight hs' hn, List.size_toArray]
  rw [if_pos]
  unfold wf
  simp only [hasDupLabel_straight hs', Bool.not_false, Bool.and_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [straightCFG, CFG.blk]
  · simp only [straightCFG, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      List.range_one, List.all_cons, List.all_nil, Bool.and_true]
    unfold AllocCheck.LcmdCFG.blockOk
    obtain ⟨y, hy⟩ : ∃ y, wl.toArray[wl.length - 1]? = some y :=
      ⟨_, Array.getElem?_eq_getElem (by simpa using hn)⟩
    simp only [CFG.blk, CFG.nextStart, CFG.next, List.size_toArray, Array.getD_eq_getD_getElem?,
      Array.getElem?_singleton, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range', Bool.not_eq_true', Option.getD_some, ↓reduceIte]
    refine ⟨⟨⟨⟨by simpa using hn, le_refl _⟩, rfl⟩, fun pc _ => ?_⟩, ?_⟩
    · cases h : wl.toArray[pc]? with
      | none => rfl
      | some z => simp [(hx pc z h).1]
    · rw [hy]
      simp [termOk, (hx _ y hy).1, CFG.next]
  · unfold blockOfOk
    simp only [straightCFG, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Array.size_replicate, List.size_toArray, true_and]
    intro pc hpc
    simp [CFG.blk, hpc]
  · simp only [Bool.not_eq_true', Array.any_eq_false]
    intro i hi
    have := (hx i _ (Array.getElem?_eq_getElem hi)).2.2
    simpa using this

end Straight

/-! ## 9. The check of a straight-line pair -/

theorem SSt.inv_start : SSt.start.Inv 0 :=
  ⟨⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩, fun _ => rfl, rfl, rfl⟩

theorem SSt.Inv.mono {n m : Nat} (hnm : n ≤ m) {ss : SSt} (h : ss.Inv n) : ss.Inv m :=
  ⟨h.1.mono hnm, h.2⟩

/-- A shared run from an interned state ends in an interned state with guards reading only
    entries of its final table. -/
theorem tRun_inv : ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), ss.Inv T.ents.size →
    ∀ {T2 : Tbl} {s : SSt} {g : List SG}, tRun is ss T = (T2, .ok s g) →
      s.Inv T2.ents.size ∧ ∀ x ∈ g, x.refsLt T2.ents.size = true
  | [], ss, T, h, T2, s, g, e => by
      simp only [tRun, Prod.mk.injEq, SOut.ok.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨h, fun _ hx => by cases hx⟩
  | i :: is, ss, T, h, T2, s, g, e => by
      rw [tRun_cons] at e
      cases hs : symStep i ss with
      | ok s1 g1 =>
          rw [hs] at e
          dsimp only at e
          have hR1 := symStep_refsLt i h.1 hs
          obtain ⟨ds0, hw0, hr0⟩ := symStep_frm i hs
          rw [SSt.Frm.ds_eq hw0] at e
          have hI2 := Tbl.internSt_inv (T := T) ds0 hR1.1 (fun r hr => by
            rw [hr0 r hr]; exact h.2.1 r)
          generalize hp : T.internSt s1 ds0 = p at e hI2
          obtain ⟨P, ps⟩ := p
          simp only [runAfter] at e
          generalize hr : tRun is ps P = r at e
          obtain ⟨R2, o⟩ := r
          cases o with
          | ok s2 g2 =>
              simp only [SOut.after, Prod.mk.injEq, SOut.ok.injEq] at e
              obtain ⟨rfl, rfl, rfl⟩ := e
              have ih := tRun_inv is ps P hI2 hr
              have hsz : T.ents.size ≤ R2.ents.size := by
                have h1 := (Tbl.internSt_ext T s1 ds0).size_le
                rw [hp] at h1
                have h2 := (tRun_ext is ps P).size_le
                rw [hr] at h2
                exact h1.trans h2
              refine ⟨ih.1, fun x hx => ?_⟩
              rcases List.mem_append.mp hx with hx | hx
              · cases x with
                | wid t w => exact STerm.refsLt_mono hsz _ (hR1.2 _ hx)
                | eqW a b =>
                    have := hR1.2 _ hx
                    simp only [SG.refsLt, Bool.and_eq_true] at this ⊢
                    exact ⟨STerm.refsLt_mono hsz _ this.1, STerm.refsLt_mono hsz _ this.2⟩
                | shp a w m => exact SArr.refsLt_mono hsz _ (hR1.2 _ hx)
              · exact ih.2 x hx
          | fail => simp [SOut.after] at e
          | unk => simp [SOut.after] at e
      | fail => rw [hs] at e; simp at e
      | unk => rw [hs] at e; simp at e

theorem foldl_join_spec : ∀ (l acc : List String),
    (∀ v ∈ acc, v ∈ l.foldl (fun a v => if a.contains v then a else a ++ [v]) acc) ∧
    (∀ v ∈ l, v ∈ l.foldl (fun a v => if a.contains v then a else a ++ [v]) acc) ∧
    ((∀ v ∈ l, v ∈ acc) → l.foldl (fun a v => if a.contains v then a else a ++ [v]) acc = acc)
  | [], acc => ⟨fun _ h => h, (fun _ h => by cases h), fun _ => rfl⟩
  | a :: l, acc => by
      simp only [List.foldl_cons]
      have ih := foldl_join_spec l (if acc.contains a then acc else acc ++ [a])
      have ha : a ∈ (if acc.contains a then acc else acc ++ [a]) := by
        split
        · rename_i h; simpa using h
        · simp
      refine ⟨fun v hv => ih.1 v ?_, fun v hv => ?_, fun h => ?_⟩
      · split
        · exact hv
        · exact List.mem_append_left _ hv
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact ih.1 _ ha
        · exact ih.2.1 v hv
      · have hc : acc.contains a = true := by
          simpa using h a (List.mem_cons_self ..)
        simp only [hc, ↓reduceIte] at ih ⊢
        exact ih.2.2 (fun v hv => h v (List.mem_cons_of_mem _ hv))

/-- The live set `n` holds every name of `m`, and the flag when `m` needs it. -/
def LiveCov (n m : List String × Bool) : Prop := (∀ v ∈ m.1, v ∈ n.1) ∧ (m.2 = true → n.2 = true)

theorem joinLive_cov (n m : List String × Bool) : LiveCov (joinLive n m) m :=
  ⟨fun v hv => (foldl_join_spec m.1 n.1).2.1 v hv, fun h => by simp [joinLive, h]⟩

theorem joinLive_of_cov {n m : List String × Bool} (h : LiveCov n m) : joinLive n m = n := by
  obtain ⟨n1, n2⟩ := n
  simp only [joinLive, (foldl_join_spec m.1 n1).2.2 h.1, Prod.mk.injEq, true_and]
  cases hm : m.2
  · simp
  · have := h.2 hm
    simp only at this
    simp [this]

/-- **Live sets of one block.** For a graph with one block whose needed set `N` does not
    depend on the live sets, the live-set iteration ends with a set covering `N`. -/
theorem liveIter_single {outs : List String} {B : List LinstrRM} {G : AllocCheck.LcmdCFG.CFG}
    {R : Array (Tbl × SOut × SOut)} (hG : G.blocks.size = 1) (N : List String × Bool)
    {r : Tbl × SOut × SOut} (hR : R[0]? = some r)
    (hN : ∀ L, blockNeed outs L (G.blk 0).term r B (G.blk 0) = N) :
    LiveCov ((liveIter outs B G R (4 * G.blocks.size + 64)
      (Array.replicate G.blocks.size ([], false))).getD 0 ([], false)) N := by
  have hround : ∀ L : Array (List String × Bool),
      liveRound outs B G R L = #[joinLive (L.getD 0 ([], false)) N] := by
    intro L
    unfold liveRound
    rw [hG, show Array.range 1 = #[0] by apply Array.toList_inj.mp; simp,
      Array.map_singleton]
    simp only [hR, hN]
  rw [hG]
  show LiveCov ((liveIter outs B G R (67 + 1) #[([], false)]).getD 0 ([], false)) N
  rw [liveIter, hround]
  split
  · rename_i heq
    have hc := joinLive_cov ([], false) N
    have heq' : (joinLive ([], false) N).1.length = 0 ∧ (joinLive ([], false) N).2 = false := by
      simpa [Array.getD] using heq
    replace heq := heq'
    simp only [Array.getD, Array.size_singleton, Nat.zero_lt_one, ↓reduceDIte]
    refine ⟨fun v hv => ?_, fun h => ?_⟩
    · have := hc.1 v hv
      rw [List.length_eq_zero_iff.mp heq.1] at this
      cases this
    · have := hc.2 h
      rw [heq.2] at this
      cases this
  · show LiveCov ((liveIter outs B G R (66 + 1) _).getD 0 ([], false)) N
    rw [liveIter, hround]
    have hJ : joinLive (#[joinLive ([], false) N].getD 0 ([], false)) N =
        joinLive ([], false) N := by
      simp only [Array.getD, Array.size_singleton, Nat.zero_lt_one, ↓reduceDIte]
      exact joinLive_of_cov (joinLive_cov _ _)
    have h0 : (#[([], false)] : Array (List String × Bool)).getD 0 ([], false) = ([], false) := rfl
    rw [h0, hJ, if_pos (by simp)]
    simpa [Array.getD] using joinLive_cov ([], false) N

theorem okIn_of_live {n m : List String × Bool} (h : LiveCov n m) {vs : List String} {rf : Bool}
    (hv : ∀ v ∈ vs, v ∈ m.1) (hr : rf = true → m.2 = true) : okIn n vs rf = true := by
  simp only [okIn, vIn, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  refine ⟨fun v hvs => h.1 v (hv v hvs), ?_⟩
  cases rf
  · rfl
  · simp [h.2 (hr rfl)]

theorem SG.normT_refsLt {E : Array TEnt} (hE : TBnd E) {x : SG} (hx : x.refsLt E.size = true) :
    ∀ y ∈ SG.normT E x, y.refsLt E.size = true := by
  intro y hy
  cases x with
  | wid t w =>
      simp only [SG.normT] at hy
      split at hy
      · split at hy
        · cases hy
        · simp only [List.mem_singleton] at hy; subst hy; rfl
      · simp only [List.mem_singleton] at hy; subst hy
        exact STerm.wbT_refsLt hE t hx
  | eqW a c =>
      simp only [SG.refsLt, Bool.and_eq_true] at hx
      simp only [SG.normT] at hy
      split at hy
      · split at hy
        · cases hy
        · simp only [List.mem_singleton] at hy; subst hy; rfl
      · simp only [List.mem_singleton] at hy; subst hy
        simp only [SG.refsLt, Bool.and_eq_true]
        exact ⟨STerm.wbT_refsLt hE a hx.1, STerm.wbT_refsLt hE c hx.2⟩
  | shp a w m =>
      simp only [SG.normT, List.mem_singleton] at hy
      subst hy
      exact hx

/-- **The check of one falling block.** Two runs of a block ending by falling off the body,
    with states that agree on every word, equal guards, words reading only entries of the
    table, and a live set covering what the block needs, pass `blockOkR`. -/
theorem blockOkR_fall {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {b b' : AllocCheck.LcmdCFG.Block} {T1 : Tbl} {s s' : SSt} {g : List SG}
    (e : s.Eqv s') (hI : s.Inv T1.ents.size) (hg : ∀ x ∈ g, x.refsLt T1.ents.size = true)
    (hE : TBnd T1.ents)
    (hL : LiveCov (L 0) (blockNeed outs L (.fall none) (T1, .ok s g, .ok s' g) B b))
    (hlast : ∀ p, B[b.stop - 1]? = some p → AllocCheck.LcmdCFG.isTermR p.1 = false) :
    blockOkR outs L 0 (.fall none) (T1, .ok s g, .ok s' g) B B' b b' = true := by
  simp only [blockNeed, AllocCheck.LcmdCFG.Term.succs, AllocCheck.LcmdCFG.Term.halts,
    Option.toList, List.flatMap_nil, List.any_nil, ↓reduceIte, Bool.false_or,
    Bool.or_false, Bool.true_and, Option.map_none, Option.getD_none, List.append_nil] at hL
  simp only [blockOkR, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [guardsT, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    refine ⟨fun x hx => hx.elim (hg x) (hg x), fun x hx => ⟨by simpa using hx, ?_⟩⟩
    simp only [okInGT, Bool.and_eq_true]
    obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
    refine ⟨SG.normT_refsLt hE (hg y hy) x hxy, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
    · simp only [List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl ⟨x, hx, hv⟩)
    · simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inl (Or.inl ⟨x, hx, h⟩)
  · cases hb : B[b.stop - 1]? with
    | none => simp [termAgreeT]
    | some p =>
        have hp := hlast p hb
        obtain ⟨x, τ⟩ := p
        cases x <;> simp_all [termAgreeT, AllocCheck.LcmdCFG.isTermR]
  · simp only [exitAgreeT, AllocCheck.LcmdCFG.Term.succs, Option.toList, List.all_nil,
      AllocCheck.LcmdCFG.Term.halts, Bool.not_true, Bool.false_or, Bool.true_and,
      Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    refine ⟨fun r hr => ⟨congrFun e.1 r, ?_⟩, fun q hq => ⟨congrFun e.2.1 q, ?_⟩⟩
    · simp only [okInT, Bool.and_eq_true]
      refine ⟨hI.1.1 r, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
      · simp only [List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨r, hr, hv⟩)
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inl (Or.inr ⟨r, hr, h⟩)
    · simp only [okInAT, Bool.and_eq_true]
      refine ⟨hI.1.2.1 q, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
      · simp only [List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨q, by simpa using hq, hv⟩
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨q, by simpa using hq, h⟩

theorem bodyAt_straight (B : List LinstrRM) :
    bodyAt B ((straightCFG (B.map Prod.fst).length).blk 0) (.fall none) = B := by
  simp [bodyAt, straightCFG, AllocCheck.LcmdCFG.CFG.blk, bstopOf]

/-- **Completeness for straight-line bodies.** Two non-empty straight-line typed bodies whose
    shared runs agree (`Res`), the source run being inside the fragment, pass `ownedCheckM`. -/
theorem ownedCheckM_of_res (outs : List String) {B B' : List LinstrRM} (hne : B ≠ [])
    (hne' : B' ≠ []) (hs : ∀ p ∈ B, straightR p.1 = true) (hs' : ∀ p ∈ B', straightR p.1 = true)
    (hres : Res (tRun B SSt.start Tbl.empty).1 (tRun B SSt.start Tbl.empty).2
      (tRun B' SSt.start (tRun B SSt.start Tbl.empty).1))
    (hunk : (tRun B SSt.start Tbl.empty).2 ≠ .unk) : ownedCheckM outs B B' = true := by
  have hG := cfgOf_straight (wl := B.map Prod.fst) (by simpa using hne)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs p hp)
  have hG' := cfgOf_straight (wl := B'.map Prod.fst) (by simpa using hne')
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs' p hp)
  unfold ownedCheckM
  rw [hG, hG']
  dsimp only
  have hsz : ∀ n, (straightCFG n).blocks.size = 1 := fun _ => rfl
  have hterm : ∀ n, ((straightCFG n).blk 0).term = .fall none := fun _ => rfl
  generalize hp : tRun B SSt.start Tbl.empty = p at hres hunk
  obtain ⟨T1, o⟩ := p
  have hR : (runsOf B B' (straightCFG (B.map Prod.fst).length)
      (straightCFG (B'.map Prod.fst).length))[0]? =
      some (blockRuns B B' ((straightCFG (B.map Prod.fst).length).blk 0)
        ((straightCFG (B'.map Prod.fst).length).blk 0) (.fall none)) := by
    simp [runsOf, hsz, hterm]
  have hBR : blockRuns B B' ((straightCFG (B.map Prod.fst).length).blk 0)
      ((straightCFG (B'.map Prod.fst).length).blk 0) (.fall none) =
      ((tRun B' SSt.start T1).1, o, (tRun B' SSt.start T1).2) := by
    simp only [blockRuns, bodyAt_straight, hp]
  rw [hBR] at hR
  simp only [ownedCheckWithR, hsz, hterm, hR, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Nat.lt_one_iff, forall_eq, beq_self_eq_true, true_and]
  refine ⟨by simp [hne, hne'], ?_⟩
  cases o with
  | unk => exact absurd rfl hunk
  | fail => simp [blockOkR]
  | ok s g =>
      generalize hq : tRun B' SSt.start T1 = q at hres hR
      obtain ⟨Q, o'⟩ := q
      cases o' with
      | ok s' g' =>
          obtain ⟨hQ, e, rfl⟩ := hres
          simp only at hQ
          simp only [hQ] at hR ⊢
          have hinv := tRun_inv B SSt.start Tbl.empty SSt.inv_start hp
          have hE : TBnd T1.ents := by
            have := tRun_valid B SSt.start Tbl.empty tValid_empty
            rw [hp] at this
            exact this.2
          refine blockOkR_fall e hinv.1 hinv.2 hE ?_ ?_
          · refine liveIter_single (hsz _) _ hR (fun L => ?_)
            simp only [blockNeed, hterm, AllocCheck.LcmdCFG.Term.succs,
              AllocCheck.LcmdCFG.Term.halts, Option.toList, List.flatMap_nil, List.any_nil]
          · intro p hp'
            have hmem : p ∈ B := List.mem_of_getElem? hp'
            have := hs p hmem
            simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
            exact this.1.1
      | fail => simp [Res] at hres
      | unk => simp [Res] at hres

/-! ## 10. Completeness of the checker for two-address legalisation -/

theorem copyPair_straight {x : LinstrR} (h : straightR x = true) :
    ∀ y ∈ copyPair x, straightR y = true := by
  intro y hy
  unfold copyPair at hy
  split at hy
  · split at hy <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hy <;>
      rcases hy with rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at hy
    subst hy
    exact h

theorem twoAddrChunk_straight (tg : LinstrR → MemTag) {p : LinstrRM}
    (h : straightR p.1 = true) : ∀ q ∈ twoAddrChunk tg p, straightR q.1 = true := by
  intro q hq
  unfold twoAddrChunk at hq
  split at hq
  · simp only [List.mem_singleton] at hq; subst hq; exact h
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    exact copyPair_straight h y hy

theorem twoAddrChunk_ne_nil (tg : LinstrR → MemTag) (p : LinstrRM) :
    twoAddrChunk tg p ≠ [] := by
  unfold twoAddrChunk
  split
  · simp
  · unfold copyPair
    split
    · split <;> simp
    · simp

theorem tRun_unk_iff (is : List LinstrRM) :
    (tRun is SSt.start Tbl.empty).2 = .unk ↔ symRun is SSt.start = .unk := by
  obtain ⟨⟨σ, hσ⟩, -⟩ := tRun_valid is SSt.start Tbl.empty tValid_empty
  have e := tRun_subst hσ is SSt.start Tbl.empty (TExt.refl _)
  rw [SSt.subst_start] at e
  rw [← e]
  cases (tRun is SSt.start Tbl.empty).2 <;> simp [SOut.subst]

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
