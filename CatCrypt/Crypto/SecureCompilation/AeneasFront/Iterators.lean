/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.IterModel
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify

/-!
# Iterator adapters as index loops

A `for` loop over an iterator adapter is printed by the Aeneas backend as `loop F (st₀, acc)`
whose body `F` steps the adapter state by its `next` function. This module gives, for each
adapter the Aeneas front reads, an `IndexedIter` of `AeneasFront/Reify.lean`: the positions
`pos j` of the state indexed by the trip index `j` below a trip count, at which `next` yields
the item `item j` and `pos (j + 1)`. `Reify.indexedForLoop` reads the loop over such a state as
the counted loop whose step at the index `i` binds `item i` and runs the body on it.

* `enumRangeIter`: `(0..n).enumerate()`, the item `(i, i)`;
* `stepByRangeIter`: `(0..n).step_by(k)`, the item `i * k`, the trip count `⌈n / k⌉`;
* `enumArrayIter`: `a.iter().enumerate()` on an array, the item `(i, a[i])`;
* `zipArrayIter`: `a.iter().zip(b.iter())` on two arrays, the item `(a[i], b[i])`, the trip
  count the smaller length.

Each instance is the correctness square of its adapter: the index loop denotes what the
adapter's `next` denotes in the Aeneas model of `AeneasFront/IterModel.lean`.

## Main results

* `enumRangeIter`, `stepByRangeIter`, `enumArrayIter`, `zipArrayIter`
* `enumRange_item_bind`, `stepByRange_item_bind`, `enumArray_item_bind`, `zipArray_item_bind`:
  the bind of an item in the form the reader reads
* `skipN_range`: `skipN` on a range
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open CatCrypt.Hax.RustSemantics

/-! ## Arithmetic of `usize` words -/

theorem usz_add_one {j : Nat} (h : j + 1 < 2 ^ UScalarTy.Usize.numBits) :
    (usz j + 1#usize : RustM Usize) = .ok (usz (j + 1)) := by
  have h1 : (usz j).val = j := usz_val (by omega)
  have h' := UScalar.add_equiv (usz j) 1#usize
  revert h'
  rcases hx : (usz j + 1#usize : RustM Usize) with z | e | _ <;> intro h'
  · obtain ⟨-, hz, -⟩ := h'
    rw [h1] at hz
    obtain ⟨zb⟩ := z
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [UScalar.val] at hz
    rw [hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    rfl
  · obtain ⟨-, hb⟩ := h'
    exfalso
    apply hb
    simp only [UScalar.inBounds, h1]
    exact h
  · exact h'.elim

theorem usz_mul {j : Nat} (k : Usize) (hj : j < 2 ^ UScalarTy.Usize.numBits)
    (h : j * k.val < 2 ^ UScalarTy.Usize.numBits) :
    (usz j * k : RustM Usize) = .ok (usz (j * k.val)) := by
  have h1 : (usz j).val = j := usz_val hj
  have h' := UScalar.mul_equiv (usz j) k
  change UScalar.mul (usz j) k = _
  revert h'
  rcases hx : UScalar.mul (usz j) k with z | e | _ <;> intro h'
  · obtain ⟨-, hz, -⟩ := h'
    rw [h1] at hz
    obtain ⟨zb⟩ := z
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [UScalar.val] at hz
    rw [hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    grind
  · obtain ⟨-, hb⟩ := h'
    simp only [UScalar.max, h1] at hb
    omega
  · exact h'.elim

/-- The literal `0#usize` is the word of `0`. -/
theorem usz_zero : usz 0 = 0#usize := by
  rfl

theorem index_usz {T : Type} {m : Usize} (a : Aeneas.Std.Array T m) {j : Nat}
    (h : j < a.val.length) : Aeneas.Std.Array.index_usize a (usz j) = .ok a.val[j] := by
  have hm : a.val.length = m.val := a.property
  have hj : j < 2 ^ UScalarTy.Usize.numBits := by
    have := m.bv.isLt
    simp only [UScalar.val] at hm
    omega
  unfold Aeneas.Std.Array.index_usize
  rw [Aeneas.Std.Array.getElem?_Usize_eq, usz_val hj, List.getElem?_eq_getElem h]

/-- A natural number below a `usize` value is below the `usize` bound. -/
theorem lt_usize_bound {j : Nat} (n : Usize) (h : j ≤ n.val) :
    j < 2 ^ UScalarTy.Usize.numBits := by
  have := n.bv.isLt
  simp only [UScalar.val] at h
  omega

/-! ## `enumerate` over a range -/

/-- **`(0..n).enumerate()`.** The trip `j` is at the range `j..n` with the count `j` and
    yields `(j, j)`. -/
def enumRangeIter (n : Usize) :
    IndexedIter (core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize))
      { iter := { start := 0#usize, «end» := n }, count := 0#usize } n where
  pos j := { iter := { start := usz j, «end» := n }, count := usz j }
  item i := .ok (i, i)
  hnext j hj := by
    have hjn : j < 2 ^ UScalarTy.Usize.numBits := lt_usize_bound n hj.le
    have h1 : j + 1 < 2 ^ UScalarTy.Usize.numBits := lt_usize_bound n hj
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.iter.traits.iterator.IteratorRange]
    rw [next_usize, usz_val hjn, ite_eq_left hj]
    simp only [bind_tc_ok, usz_add_one h1]
  hend := by
    refine ⟨{ iter := { start := usz n.val, «end» := n }, count := usz n.val }, ?_⟩
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.iter.traits.iterator.IteratorRange]
    rw [next_usize, usz_val (lt_usize_bound n le_rfl), ite_eq_right (Nat.lt_irrefl _), bind_tc_ok]
  h0 := by
    simp only [usz_zero]

theorem enumRange_item_bind {β : Type} (n i : Usize) (k : Usize × Usize → RustM β) :
    ((enumRangeIter n).item i >>= k) = k (i, i) :=
  bind_tc_ok _ _

/-! ## `step_by` over a range -/

/-- `skipN` on a range from `s ≤ n`: the range from `min (s + m) n`. -/
theorem skipN_range (n : Usize) :
    ∀ (m s : Nat), s ≤ n.val →
      core.iter.adapters.step_by.skipN
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          { start := usz s, «end» := n } m =
        .ok { start := usz (min (s + m) n.val), «end» := n }
  | 0, s, hs => by
    simp only [core.iter.adapters.step_by.skipN, Nat.add_zero, Nat.min_eq_left hs]
  | m + 1, s, hs => by
    have hsn : s < 2 ^ UScalarTy.Usize.numBits := lt_usize_bound n hs
    simp only [core.iter.adapters.step_by.skipN, core.iter.traits.iterator.IteratorRange]
    rw [next_usize, usz_val hsn]
    by_cases h : s < n.val
    · rw [ite_eq_left h, bind_tc_ok]
      simp only
      rw [show min (s + (m + 1)) n.val = min (s + 1 + m) n.val by omega]
      exact skipN_range n m (s + 1) h
    · rw [ite_eq_right h, bind_tc_ok]
      simp only
      rw [show min (s + (m + 1)) n.val = s by omega]

/-- The trip count `⌈n / k⌉` of `(0..n).step_by(k)`. -/
abbrev stepByCnt (n k : Usize) : Usize := usz ((n.val + k.val - 1) / k.val)

/-- The `next` of the range iterator is `IteratorRange.next`; an unfolding lemma. -/
theorem iteratorRange_next {A : Type} (S : core.iter.range.Step A)
    (r : core.ops.range.Range A) :
    (core.iter.traits.iterator.IteratorRange S).next r = core.iter.range.IteratorRange.next S r :=
  rfl

theorem lt_stepTrip {n k j : Nat} (hk : 0 < k) : j < (n + k - 1) / k ↔ j * k < n := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hk, Nat.add_mul, Nat.one_mul]
  omega

theorem stepTrip_le {n k : Nat} (hk : 0 < k) : (n + k - 1) / k ≤ n := by
  refine Nat.le_of_not_lt fun h => ?_
  have h1 := (lt_stepTrip hk).1 h
  have h2 := Nat.le_mul_of_pos_right n hk
  omega

theorem stepByCnt_val (n k : Usize) (hk : 0 < k.val) :
    (stepByCnt n k).val = (n.val + k.val - 1) / k.val :=
  usz_val (lt_usize_bound n (stepTrip_le hk))

/-- **`(0..n).step_by(k)`.** The trip `j` is at the range `min (j * k) n..n` and yields
    `j * k`. -/
def stepByRangeIter (n k : Usize) (hk : 0 < k.val) :
    IndexedIter (core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize))
      { iter := { start := 0#usize, «end» := n }, step_by := k } (stepByCnt n k) where
  pos j := { iter := { start := usz (min (j * k.val) n.val), «end» := n }, step_by := k }
  item i := i * k
  hnext j hj := by
    rw [stepByCnt_val n k hk] at hj
    have hjk : j * k.val < n.val := (lt_stepTrip hk).1 hj
    have hjn : j < 2 ^ UScalarTy.Usize.numBits :=
      lt_usize_bound n (Nat.le_trans (Nat.le_mul_of_pos_right j hk) hjk.le)
    simp only [core.iter.adapters.step_by.IteratorStepBy.next, iteratorRange_next]
    rw [Nat.min_eq_left hjk.le, next_usize, usz_val (lt_usize_bound n hjk.le), ite_eq_left hjk,
      bind_tc_ok, usz_mul k hjn (lt_usize_bound n hjk.le), bind_tc_ok]
    simp only
    rw [skipN_range n (k.val - 1) (j * k.val + 1) hjk, bind_tc_ok,
      show min (j * k.val + 1 + (k.val - 1)) n.val = min ((j + 1) * k.val) n.val by
        rw [Nat.add_mul]; omega]
  hend := by
    refine ⟨{ iter := { start := usz n.val, «end» := n }, step_by := k }, ?_⟩
    have hge : n.val ≤ (stepByCnt n k).val * k.val := by
      rw [stepByCnt_val n k hk]
      exact Nat.le_of_not_lt fun h => Nat.lt_irrefl _ ((lt_stepTrip hk).2 h)
    simp only [core.iter.adapters.step_by.IteratorStepBy.next, iteratorRange_next]
    rw [Nat.min_eq_right hge, next_usize, usz_val (lt_usize_bound n le_rfl),
      ite_eq_right (Nat.lt_irrefl _), bind_tc_ok]
  h0 := by
    simp only [Nat.zero_mul, Nat.zero_min, usz_zero]

theorem stepByRange_item_bind {β : Type} (n k : Usize) (hk : 0 < k.val) (i : Usize)
    (c : Usize → RustM β) :
    ((stepByRangeIter n k hk).item i >>= c) = ((i * k : RustM Usize) >>= c) :=
  rfl

/-! ## `enumerate` over an array -/

/-- **`a.iter().enumerate()` on an array.** The trip `j` is at the index `j` with the count
    `j` and yields `(j, a[j])`. -/
def enumArrayIter {T : Type} {m : Usize} (a : Aeneas.Std.Array T m) :
    IndexedIter (core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter T))
      { iter := { slice := a.to_slice, i := 0 }, count := 0#usize } m where
  pos j := { iter := { slice := a.to_slice, i := j }, count := usz j }
  item i := Aeneas.Std.Array.index_usize a i >>= fun x => .ok (i, x)
  hnext j hj := by
    have hm : a.val.length = m.val := a.property
    have hja : j < a.val.length := by omega
    have h1 : j + 1 < 2 ^ UScalarTy.Usize.numBits := lt_usize_bound m hj
    rw [index_usz a hja, bind_tc_ok, bind_tc_ok]
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next]
    rw [dite_eq_left (show j < (a.to_slice).val.length from hja), bind_tc_ok]
    simp only [usz_add_one h1, bind_tc_ok]
    rfl
  hend := by
    refine ⟨{ iter := { slice := a.to_slice, i := m.val }, count := usz m.val }, ?_⟩
    have hm : a.val.length = m.val := a.property
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next]
    rw [dite_eq_right (show ¬ m.val < (a.to_slice).val.length from fun h => by
      change m.val < a.val.length at h; omega), bind_tc_ok]
  h0 := by
    simp only [usz_zero]

theorem enumArray_item_bind {T β : Type} {m : Usize} (a : Aeneas.Std.Array T m) (i : Usize)
    (k : Usize × T → RustM β) :
    ((enumArrayIter a).item i >>= k) =
      (Aeneas.Std.Array.index_usize a i >>= fun x => k (i, x)) := by
  change ((Aeneas.Std.Array.index_usize a i >>= fun x => .ok (i, x)) >>= k) = _
  rw [bind_assoc_eq]
  simp only [bind_tc_ok]

/-! ## `zip` of two arrays -/

/-- **`a.iter().zip(b.iter())` on two arrays.** The trip `j` is at the index `j` of both and
    yields `(a[j], b[j])`; the trip count is the smaller length. -/
def zipArrayIter {A B : Type} {m m' : Usize} (a : Aeneas.Std.Array A m)
    (b : Aeneas.Std.Array B m') :
    IndexedIter (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        (core.iter.traits.iterator.IteratorSliceIter A)
        (core.iter.traits.iterator.IteratorSliceIter B))
      ⟨{ slice := a.to_slice, i := 0 }, { slice := b.to_slice, i := 0 }⟩ (usz (min m.val m'.val))
    where
  pos j := ⟨{ slice := a.to_slice, i := j }, { slice := b.to_slice, i := j }⟩
  item i := Aeneas.Std.Array.index_usize a i >>= fun x =>
    Aeneas.Std.Array.index_usize b i >>= fun y => .ok (x, y)
  hnext j hj := by
    have hmn : (usz (min m.val m'.val)).val = min m.val m'.val :=
      usz_val (lt_usize_bound m (Nat.min_le_left _ _))
    rw [hmn] at hj
    have hma : a.val.length = m.val := a.property
    have hmb : b.val.length = m'.val := b.property
    have hja : j < a.val.length := by omega
    have hjb : j < b.val.length := by omega
    rw [index_usz a hja, bind_tc_ok, index_usz b hjb, bind_tc_ok, bind_tc_ok]
    simp only [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
      core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next]
    rw [dite_eq_left (show j < (a.to_slice).val.length from hja), bind_tc_ok]
    simp only
    rw [dite_eq_left (show j < (b.to_slice).val.length from hjb), bind_tc_ok]
    rfl
  hend := by
    have hmn : (usz (min m.val m'.val)).val = min m.val m'.val :=
      usz_val (lt_usize_bound m (Nat.min_le_left _ _))
    have hma : a.val.length = m.val := a.property
    have hmb : b.val.length = m'.val := b.property
    rw [hmn]
    simp only [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
      core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next]
    by_cases hab : m.val ≤ m'.val
    · rw [dite_eq_right (show ¬ min m.val m'.val < (a.to_slice).val.length from fun h => by
        change _ < a.val.length at h; omega), bind_tc_ok]
      exact ⟨_, rfl⟩
    · rw [dite_eq_left (show min m.val m'.val < (a.to_slice).val.length by
        change _ < a.val.length; omega), bind_tc_ok]
      simp only
      rw [dite_eq_right (show ¬ min m.val m'.val < (b.to_slice).val.length from fun h => by
        change _ < b.val.length at h; omega), bind_tc_ok]
      exact ⟨_, rfl⟩
  h0 := rfl

theorem zipArray_item_bind {A B β : Type} {m m' : Usize} (a : Aeneas.Std.Array A m)
    (b : Aeneas.Std.Array B m') (i : Usize) (k : A × B → RustM β) :
    ((zipArrayIter a b).item i >>= k) =
      (Aeneas.Std.Array.index_usize a i >>= fun x =>
        Aeneas.Std.Array.index_usize b i >>= fun y => k (x, y)) := by
  change ((Aeneas.Std.Array.index_usize a i >>= fun x =>
    Aeneas.Std.Array.index_usize b i >>= fun y => .ok (x, y)) >>= k) = _
  simp only [bind_assoc_eq, bind_tc_ok]

end CatCrypt.Crypto.SecureCompilation.AeneasFront
