/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# Rows of a fixed length and their concatenation

An array of `k`-field structs is laid out as one flat array: the `k` components of
element `i` occupy the positions `i * k`, …, `i * k + k - 1`.  These lemmas relate
component `off` of row `i` of a list of rows of length `k` to component `i * k + off`
of the concatenation of the rows, for reading (`flatten_getElem?_mul_add`), writing
(`flatten_set_mul_add`) and the length (`flatten_length_of_forall`).

## Main results

* `flatIdx_lt` — `i < n` and `off < k` give `i * k + off < n * k`.
* `flatten_getElem?_mul_add`, `flatten_set_mul_add`, `flatten_length_of_forall`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.ListBlocks

/-- **The index bound.**  Field `off < k` of element `i < n` lies below `n * k` in
    the flat array. -/
theorem flatIdx_lt {i n k off : Nat} (hi : i < n) (ho : off < k) : i * k + off < n * k :=
  calc i * k + off < i * k + k := by omega
    _ = (i + 1) * k := (Nat.succ_mul i k).symm
    _ ≤ n * k := Nat.mul_le_mul_right k hi

/-- Rows of length `k` concatenate to `rows.length * k` components. -/
theorem flatten_length_of_forall {β : Type} : ∀ (rows : List (List β)) {k : Nat},
    (∀ r ∈ rows, r.length = k) → rows.flatten.length = rows.length * k
  | [], _, _ => by simp
  | r :: rs, k, hk => by
    rw [List.flatten_cons, List.length_append, hk r List.mem_cons_self,
      flatten_length_of_forall rs (fun r h => hk r (List.mem_cons_of_mem _ h)), List.length_cons,
      Nat.succ_mul, Nat.add_comm]

/-- Component `off` of row `i` of rows of length `k` is component `i * k + off` of
    their concatenation. -/
theorem flatten_getElem?_mul_add {β : Type} : ∀ (rows : List (List β)) {k i off : Nat},
    (∀ r ∈ rows, r.length = k) → (hi : i < rows.length) → off < k →
    rows.flatten[i * k + off]? = (rows[i]'hi)[off]?
  | [], _, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | r :: rs, k, i, off, hk, hi, ho => by
    have hr : r.length = k := hk r List.mem_cons_self
    rw [List.flatten_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by omega)
    | succ i =>
      have he : (i + 1) * k + off = r.length + (i * k + off) := by rw [Nat.succ_mul, hr]; omega
      rw [he, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem_cons_succ]
      exact flatten_getElem?_mul_add rs (fun r h => hk r (List.mem_cons_of_mem _ h))
        (by simpa using hi) ho

/-- Replacing component `i * k + off` of the concatenation of rows of length `k`
    replaces component `off` of row `i`. -/
theorem flatten_set_mul_add {β : Type} : ∀ (rows : List (List β)) {k i off : Nat} (v : β),
    (∀ r ∈ rows, r.length = k) → (hi : i < rows.length) → off < k →
    rows.flatten.set (i * k + off) v = (rows.set i ((rows[i]'hi).set off v)).flatten
  | [], _, _, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | r :: rs, k, i, off, v, hk, hi, ho => by
    have hr : r.length = k := hk r List.mem_cons_self
    rw [List.flatten_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero, List.set_cons_zero,
        List.flatten_cons]
      exact List.set_append_left _ _ (by omega)
    | succ i =>
      have he : (i + 1) * k + off = r.length + (i * k + off) := by rw [Nat.succ_mul, hr]; omega
      rw [he, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
        List.getElem_cons_succ, List.set_cons_succ, List.flatten_cons,
        flatten_set_mul_add rs v (fun r h => hk r (List.mem_cons_of_mem _ h))
          (by simpa using hi) ho]

end Hax.ListBlocks
