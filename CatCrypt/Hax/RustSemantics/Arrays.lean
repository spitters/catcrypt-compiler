/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.RustSemantics.Encode

/-!
# Arrays, slices and vectors: runtime against Aeneas

The runtime names of the leaf audit's section 2.1. An Aeneas container (`Array α n`,
`Slice α`, `alloc.vec.Vec α`) is related to a runtime `Array β` by `ListRel R` for
an element relation `R` (`Encode.lean`); the squares hold for every `R`, so they
cover arrays of scalars (`R := EncRel`) and arrays of arrays alike.

## Main results

| runtime name | runtime operation | Aeneas operation | class | theorem |
|---|---|---|---|---|
| `index` | `Hax.index` | `Array.index_usize`, `Slice.index_usize` | 1 | `index_array_square`, `index_slice_square` |
| `array_update` | `Hax.array_update` | `Array.update` | 1 | `array_update_square` |
| `repeat` | `Hax.repeat_` | `Array.repeat` | 1 | `repeat_square` |
| `array_lit` | array literal `#[…]` | `Array.make` | 1 | `array_lit_square` |
| `len` | `Hax.array_len` | `Slice.len`, `Vec.len` | 1 | `len_slice_square`, `len_vec_square` |
| `push` | `Hax.push` | `Vec.push` | 1 | `push_square` |
| `with_capacity` | `Hax.with_capacity` | `Vec.with_capacity` | 1 | `with_capacity_square` |
| `extend_from_slice` | `Hax.extend_from_slice` | `Vec.extend_from_slice` | 1 | `extend_from_slice_square` |
| `RangeTo` | `Hax.slice_to` | `SliceIndexRangeToUsizeSlice.index` | 1 | `slice_to_square` |
| `copy_from_slice` | `Hax.copy_from_slice` | `Slice.copy_from_slice` | 1 | `copy_from_slice_square` |
| `index_mut` | `Hax.index` | `Array.index_mut_usize` (value component) | 1 | `index_mut_array_square` |
| `slice_update` | `Hax.slice_update` | `Slice.update_subslice` | 1 | `slice_update_square` |
| `from_elem` | `Hax.from_elem` | `alloc.vec.from_elem` | 1 | `from_elem_square` |
| `new` | `#[]` | `Vec.new` | 1 | `new_square` |
| `deref` | `Hax.deref` | `Vec.deref` | 1 | `deref_square` |

`RangeTo` occurs only as the second argument of `index`/`index_mut`, which the
printer renders as `Hax.slice_to arr n`; its square is the one of that rendering.
`index_mut` with a scalar index is rendered as `Hax.index`; the write-back that
Aeneas returns beside the element has no counterpart in the runtime and the square
relates the element. `extend_from_slice_square` and `from_elem_square` assume a
`Clone` instance that returns its argument, as for every `Copy` type.

In each row the Aeneas operation fails exactly where the runtime returns a value
that Rust does not produce: an index at or beyond the length (`Hax.index` returns
the first entry or `default`, `Hax.array_update` leaves the array unchanged), a
range beyond the length (`Hax.slice_to` truncates), a length mismatch
(`Hax.copy_from_slice` returns the source, `Hax.slice_update` writes a prefix).
These are the operations of the printed Lean runtime. The interpreter table
`Hax.widthArrayOps` is undefined at an `index` or `array_update` beyond the
length, as Rust panics there.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Transfer.Param

section Arrays

variable {α β : Type} {R : α → β → Prop}

/-- `ListRel` by length and index. -/
theorem listRel_iff_getElem {l : List α} {arr : _root_.Array β} :
    ListRel R l arr ↔ l.length = arr.size ∧
      ∀ (i : Nat) (h : i < l.length) (h' : i < arr.size), R l[i] arr[i] := by
  unfold ListRel
  rw [ArrayRel.iff_getElem]
  simp

/-- An entry that an Aeneas container returns at position `k` is related to the entry
    that `Hax.index` reads at `k` from a related runtime array. -/
theorem listRel_index [Inhabited β] {l : List α} {arr : _root_.Array β} (h : ListRel R l arr)
    {k : Nat} {a : α} (hk : l[k]? = some a) : R a (Hax.index arr (k : Int)) := by
  rw [listRel_iff_getElem] at h
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.mp hk
  have hk'' : k < arr.size := h.1 ▸ hk'
  simp only [Hax.index, Int.toNat_natCast, dif_pos hk'']
  exact h.2 k hk' hk''

/-- Entries of related containers at the same position are related. -/
theorem listRel_getElem? {l : List α} {arr : _root_.Array β} (h : ListRel R l arr) {j : Nat}
    {a : α} {b : β} (ha : l[j]? = some a) (hb : arr[j]? = some b) : R a b := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj', rfl⟩ := _root_.Array.getElem?_eq_some_iff.mp hb
  exact (listRel_iff_getElem.mp h).2 j hj hj'

/-- `ListRel` from equal lengths and relatedness of the entries at each position. -/
theorem listRel_of_getElem? {l : List α} {arr : _root_.Array β} (hlen : l.length = arr.size)
    (h : ∀ (j : Nat) (a : α) (b : β), l[j]? = some a → arr[j]? = some b → R a b) :
    ListRel R l arr := by
  refine listRel_iff_getElem.mpr ⟨hlen, fun j hj hj' => ?_⟩
  exact h j _ _ (List.getElem?_eq_getElem hj) (_root_.Array.getElem?_eq_getElem hj')

/-- Array indexing returns, when the index is in range, the entry `Hax.index` reads. -/
theorem index_array_square [Inhabited β] {n : Usize} (v : Aeneas.Std.Array α n)
    {arr : _root_.Array β} (hv : ListRel R v.val arr) (i : Usize) :
    RCompOk R (v.index_usize i) (pure (Hax.index arr (enc i)) : Id β) := by
  rw [rcompOk_iff]
  intro a h
  unfold Aeneas.Std.Array.index_usize at h
  rw [Aeneas.Std.Array.getElem?_Usize_eq] at h
  split at h
  · cases h
  · cases h
    exact listRel_index hv ‹_›

/-- Slice indexing returns, when the index is in range, the entry `Hax.index` reads. -/
theorem index_slice_square [Inhabited β] (v : Slice α) {arr : _root_.Array β}
    (hv : ListRel R v.val arr) (i : Usize) :
    RCompOk R (v.index_usize i) (pure (Hax.index arr (enc i)) : Id β) := by
  rw [rcompOk_iff]
  intro a h
  unfold Slice.index_usize at h
  rw [Slice.getElem?_Usize_eq] at h
  split at h
  · cases h
  · cases h
    exact listRel_index hv ‹_›

/-- Mutable array indexing returns, when the index is in range, an element related
    to the entry `Hax.index` reads. -/
theorem index_mut_array_square [Inhabited β] {n : Usize} (v : Aeneas.Std.Array α n)
    {arr : _root_.Array β} (hv : ListRel R v.val arr) (i : Usize) :
    RCompOk (fun r c => R r.1 c) (v.index_mut_usize i)
      (pure (Hax.index arr (enc i)) : Id β) := by
  rw [rcompOk_iff]
  intro a h
  have hi := (rcompOk_iff.mp (index_array_square v hv i))
  unfold Aeneas.Std.Array.index_mut_usize at h
  simp only [Bind.bind] at h
  cases hx : v.index_usize i with
  | ok x => rw [hx] at h; cases h; exact hi x hx
  | fail e => rw [hx] at h; cases h
  | div => rw [hx] at h; cases h

/-- Array update returns, when the index is in range, an array related to the one
    `Hax.array_update` returns. -/
theorem array_update_square {n : Usize} (v : Aeneas.Std.Array α n) {arr : _root_.Array β}
    (hv : ListRel R v.val arr) (i : Usize) {x : α} {x' : β} (hx : R x x') :
    RCompOk (fun r c => ListRel R r.val c) (v.update i x)
      (pure (Hax.array_update arr (enc i) x') : Id (_root_.Array β)) := by
  rw [rcompOk_iff]
  intro a h
  unfold Aeneas.Std.Array.update at h
  rw [Aeneas.Std.Array.getElem?_Usize_eq] at h
  split at h
  · cases h
  · rename_i y hy
    cases h
    rw [listRel_iff_getElem] at hv ⊢
    have hi : i.val < v.val.length := (List.getElem?_eq_some_iff.mp hy).1
    have hi' : i.val < arr.size := hv.1 ▸ hi
    simp only [Hax.array_update, enc_uscalar, Int.toNat_natCast, dif_pos hi']
    refine ⟨by simp [hv.1], fun j hj hj' => ?_⟩
    simp only [List.getElem_set, _root_.Array.getElem_set]
    split
    · exact hx
    · exact hv.2 j (by simpa using hj) (by simpa using hj')

/-- `[x; n]` is related to `Hax.repeat_`. -/
theorem repeat_square (n : Usize) {x : α} {x' : β} (hx : R x x') :
    RCompOk (fun r c => ListRel R r.val c) (lift (Aeneas.Std.Array.repeat n x))
      (pure (Hax.repeat_ x' (enc n)) : Id (_root_.Array β)) := by
  rw [rcompOk_lift, Aeneas.Std.Array.repeat_val, listRel_iff_getElem]
  simp only [Hax.repeat_, enc_uscalar, Int.toNat_natCast]
  refine ⟨by simp, fun j hj hj' => ?_⟩
  simp only [List.getElem_replicate, List.getElem_toArray]
  exact hx

/-- An array literal is related to the runtime array literal of related entries. -/
theorem array_lit_square {n : Usize} {l : List α} {l' : List β} (hl : l.length = n.val)
    (h : List.Forall₂ R l l') :
    RCompOk (fun r c => ListRel R r.val c) (lift (Aeneas.Std.Array.make n l hl))
      (pure l'.toArray : Id (_root_.Array β)) :=
  rcompOk_lift.mpr h

/-- The length of a slice is the size `Hax.array_len` returns. -/
theorem len_slice_square (v : Slice α) {arr : _root_.Array β} (hv : ListRel R v.val arr) :
    RCompOk EncRel (lift (Slice.len v)) (pure (Hax.array_len arr) : Id Int) := by
  rw [rcompOk_lift, encRel_iff, enc_uscalar, Slice.len_val, Hax.array_len]
  simp [← (listRel_iff_getElem.mp hv).1]

/-- The length of a vector is the size `Hax.array_len` returns. -/
theorem len_vec_square (v : alloc.vec.Vec α) {arr : _root_.Array β}
    (hv : ListRel R v.val arr) :
    RCompOk EncRel (lift (alloc.vec.Vec.len v)) (pure (Hax.array_len arr) : Id Int) := by
  rw [rcompOk_lift, encRel_iff, enc_uscalar, Hax.array_len]
  simp [← (listRel_iff_getElem.mp hv).1]

/-- `Vec::push` returns, when the length stays within `Usize`, a vector related to
    the array `Hax.push` returns. -/
theorem push_square (v : alloc.vec.Vec α) {arr : _root_.Array β} (hv : ListRel R v.val arr)
    {x : α} {x' : β} (hx : R x x') :
    RCompOk (fun r c => ListRel R r.val c) (alloc.vec.Vec.push v x)
      (pure (Hax.push arr x') : Id (_root_.Array β)) := by
  rw [rcompOk_iff]
  intro a h
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · cases h
    rw [listRel_iff_forall₂] at hv ⊢
    simpa [Hax.push] using List.rel_append hv (List.Forall₂.cons hx .nil)
  · cases h

/-- `Vec::with_capacity` is the empty vector, as `Hax.with_capacity`. -/
theorem with_capacity_square (n : Usize) :
    RCompOk (fun r c => ListRel R r.val c) (lift (alloc.vec.Vec.with_capacity α n))
      (pure (Hax.with_capacity (enc n)) : Id (_root_.Array β)) :=
  rcompOk_lift.mpr List.Forall₂.nil

/-- `Vec::new` is related to the empty runtime array. -/
theorem new_square :
    RCompOk (fun r c => ListRel R r.val c) (lift (alloc.vec.Vec.new α))
      (pure #[] : Id (_root_.Array β)) :=
  rcompOk_lift.mpr List.Forall₂.nil

/-- `Deref` of a vector is related to `Hax.deref`, the identity. -/
theorem deref_square (v : alloc.vec.Vec α) {arr : _root_.Array β} (hv : ListRel R v.val arr) :
    RCompOk (fun r c => ListRel R r.val c) (lift (alloc.vec.Vec.deref v))
      (pure (Hax.deref arr) : Id (_root_.Array β)) :=
  rcompOk_lift.mpr hv

/-- `copy_from_slice` returns, when the lengths agree, the source, as
    `Hax.copy_from_slice`. -/
theorem copy_from_slice_square (copyInst : core.marker.Copy α) (s src : Slice α)
    (dst : _root_.Array β) {src' : _root_.Array β} (hsrc : ListRel R src.val src') :
    RCompOk (fun r c => ListRel R r.val c) (core.slice.Slice.copy_from_slice copyInst s src)
      (pure (Hax.copy_from_slice dst src') : Id (_root_.Array β)) := by
  rw [rcompOk_iff]
  intro a h
  unfold core.slice.Slice.copy_from_slice at h
  split at h
  · cases h; exact hsrc
  · cases h

/-- `s[..n]` returns, when `n` is within the length, a slice related to the array
    `Hax.slice_to` returns. -/
theorem slice_to_square (s : Slice α) {arr : _root_.Array β} (hv : ListRel R s.val arr)
    (r : core.ops.range.RangeTo Usize) :
    RCompOk (fun r c => ListRel R r.val c)
      (core.slice.index.SliceIndexRangeToUsizeSlice.index r s)
      (pure (Hax.slice_to arr (enc r.end)) : Id (_root_.Array β)) := by
  rw [rcompOk_iff]
  intro a h
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.index at h
  split at h
  · cases h
    rw [listRel_iff_forall₂] at hv ⊢
    simpa [Hax.slice_to] using List.forall₂_take r.end.val hv
  · cases h

/-- The run of `List.clone` with a `clone` that returns its argument returns the list. -/
theorem list_clone_eq {clone : α → RustM α} (hclone : ∀ a, clone a = .ok a) (l : List α) :
    ∃ h, List.clone clone l = .ok ⟨l, h⟩ := by
  have hm := List.mapM_clone_eq (clone := clone) (l := l) (fun x _ => hclone x)
  unfold List.clone
  split
  · rename_i v hv
    rw [hm] at hv
    cases hv
    exact ⟨rfl, rfl⟩
  · rename_i e hv; rw [hm] at hv; cases hv
  · rename_i hv; rw [hm] at hv; cases hv

/-- `Vec::extend_from_slice` with a `Clone` that returns its argument returns, when
    the length stays within `Usize`, a vector related to the array
    `Hax.extend_from_slice` returns. -/
theorem extend_from_slice_square (cloneInst : core.clone.Clone α)
    (hclone : ∀ a, cloneInst.clone a = .ok a) (v : alloc.vec.Vec α) (s : Slice α)
    {dst src : _root_.Array β} (hv : ListRel R v.val dst) (hs : ListRel R s.val src) :
    RCompOk (fun r c => ListRel R r.val c) (alloc.vec.Vec.extend_from_slice cloneInst v s)
      (pure (Hax.extend_from_slice dst src) : Id (_root_.Array β)) := by
  rw [rcompOk_iff]
  intro a h
  have hc : Slice.clone cloneInst.clone s = .ok s := by
    obtain ⟨_, hl⟩ := list_clone_eq hclone s.val
    simp only [Slice.clone, Bind.bind, hl, bind_ok]
    rfl
  unfold alloc.vec.Vec.extend_from_slice at h
  split at h
  · split at h
    · rename_i s' hs'
      rw [hc] at hs'
      cases hs'
      cases h
      rw [listRel_iff_forall₂] at hv hs ⊢
      simpa [Hax.extend_from_slice] using List.rel_append hv hs
    · cases h
    · cases h
  · cases h

/-- `vec![x; n]` with a `Clone` that returns its argument is related to
    `Hax.from_elem`. -/
theorem from_elem_square (cloneInst : core.clone.Clone α)
    (hclone : ∀ a, cloneInst.clone a = .ok a) {x : α} {x' : β} (hx : R x x') (n : Usize) :
    RCompOk (fun r c => ListRel R r.val c) (alloc.vec.from_elem cloneInst x n)
      (pure (Hax.from_elem x' (enc n)) : Id (_root_.Array β)) := by
  rw [rcompOk_iff]
  intro a h
  obtain ⟨_, hl⟩ := list_clone_eq hclone (List.replicate n.val x)
  simp only [alloc.vec.from_elem, Bind.bind, hl, bind_ok] at h
  cases h
  rw [listRel_iff_getElem]
  simp only [Hax.from_elem, enc_uscalar, Int.toNat_natCast]
  refine ⟨by simp, fun j hj hj' => ?_⟩
  simp only [List.getElem_replicate, List.getElem_toArray]
  exact hx

/-- The loop of `Hax.slice_update` after `n ≤ src.size` steps: positions
    `l, …, l + n - 1` inside `arr` hold `src[0], …, src[n - 1]`, the others keep
    their values, and the size is that of `arr`. -/
theorem slice_update_fold {γ : Type} (arr src : _root_.Array γ) (l : Nat) :
    ∀ n, n ≤ src.size →
      ((List.range n).foldl (fun acc k => match src[k]? with
          | some v => acc.setIfInBounds (l + k) v
          | none => acc) arr).size = arr.size ∧
      ∀ j, ((List.range n).foldl (fun acc k => match src[k]? with
          | some v => acc.setIfInBounds (l + k) v
          | none => acc) arr)[j]? =
        if l ≤ j ∧ j < l + n ∧ j < arr.size then src[j - l]? else arr[j]? := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨rfl, fun j => ?_⟩
    rw [if_neg (by omega)]
    rfl
  | succ n ih =>
    intro hn
    obtain ⟨ihs, ihj⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      _root_.Array.getElem?_eq_getElem (h := by omega)]
    refine ⟨by simp [ihs], fun j => ?_⟩
    rw [_root_.Array.getElem?_setIfInBounds, ihj, ihs]
    by_cases hj : l + n = j
    · subst hj
      simp only [if_true]
      by_cases hs : l + n < arr.size
      · rw [if_pos hs, if_pos ⟨by omega, by omega, hs⟩, Nat.add_sub_cancel_left,
          _root_.Array.getElem?_eq_getElem]
      · rw [if_neg hs, if_neg (by omega), _root_.Array.getElem?_eq_none (by omega)]
    · rw [if_neg hj]
      by_cases hin : l ≤ j ∧ j < l + n ∧ j < arr.size
      · rw [if_pos hin, if_pos ⟨hin.1, by omega, hin.2.2⟩]
      · rw [if_neg hin, if_neg (by omega)]

/-- `s[a..b].copy_from_slice(src)` returns, when `a ≤ b ≤ s.len()` and `src` has
    length `b - a`, a slice related to the array `Hax.slice_update` returns. -/
theorem slice_update_square (s : Slice α) (r : core.ops.range.Range Usize) (ss : Slice α)
    {arr src : _root_.Array β} (hv : ListRel R s.val arr) (hs : ListRel R ss.val src) :
    RCompOk (fun r c => ListRel R r.val c) (Slice.update_subslice s r ss)
      (pure (Hax.slice_update arr (enc r.start) (enc r.end) src) :
        Id (_root_.Array β)) := by
  rw [rcompOk_iff]
  intro a h
  unfold Slice.update_subslice at h
  split at h
  · rename_i hr
    cases h
    have hlen := (listRel_iff_getElem.mp hv).1
    have hlen' := (listRel_iff_getElem.mp hs).1
    simp only [Slice.length] at hr
    have hn : min (r.end.val - r.start.val) src.size = ss.val.length := by omega
    obtain ⟨hsz, hget⟩ : (Hax.slice_update arr (enc r.start) (enc r.end) src).size = arr.size ∧
        ∀ j, (Hax.slice_update arr (enc r.start) (enc r.end) src)[j]? =
          if r.start.val ≤ j ∧ j < r.start.val + ss.val.length ∧ j < arr.size
          then src[j - r.start.val]? else arr[j]? := by
      simp only [Hax.slice_update, enc_uscalar, Int.toNat_natCast, hn]
      exact slice_update_fold arr src r.start.val ss.val.length (by omega)
    refine listRel_of_getElem? (by rw [hsz]; simpa using hlen) fun j a b ha hb => ?_
    rw [hget j] at hb
    by_cases h1 : j < r.start.val
    · rw [List.setSlice!_getElem?_prefix _ _ _ _ h1] at ha
      rw [if_neg (by omega)] at hb
      exact listRel_getElem? hv ha hb
    · by_cases h2 : j < r.start.val + ss.val.length
      · have hj : j < s.val.length := by
          have := (List.getElem?_eq_some_iff.mp ha).1
          simpa using this
        rw [List.setSlice!_getElem?_middle _ _ _ _ ⟨by omega, by omega, hj⟩] at ha
        rw [if_pos ⟨by omega, h2, by omega⟩] at hb
        exact listRel_getElem? hs ha hb
      · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)] at ha
        rw [if_neg (by omega)] at hb
        exact listRel_getElem? hv ha hb
  · cases h

end Arrays

end CatCrypt.Hax.RustSemantics
