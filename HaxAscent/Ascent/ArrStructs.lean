/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Structs
public import HaxAscent.Ascent.RuntimeLeaves
public import HaxAscent.ListBlocks

/-!
# Leaves for arrays of structs in the flat layout

An array `arr : [S; n]` of a struct `S` with `k` fields is laid out as one array of
`n * k` components, `arr[i].f` at position `i * k + off_f` (`off_f` the position of
the field).  `encFlat` is that encoding of an `Array` of right-nested products: the
component lists of the elements (`HaxTupleEnc.encList`), concatenated.  The runtime
leaves `indexLeaf`, `arrayUpdateLeaf` and `lenLeaf` act on it as the field read, the
field write and the length of the flat array:

| call on the flat array | leaf | transport |
|---|---|---|
| `index(arr, i * k + off)` | `indexLeaf` | `indexLeaf_encFlat` |
| `array_update(arr, i * k + off, v)` | `arrayUpdateLeaf` | `arrayUpdateLeaf_encFlat` |
| `len(arr)` | `lenLeaf` | `lenLeaf_encFlat` |

`encFlat_set` states that replacing row `i` by the components of `p` is the flat
encoding of `a.set i p`, so the `k` field writes of one element compose to the
element write.

## Main definitions

* `encFlat` — the flat encoding of an array of products.

## Main results

* `indexLeaf_encFlat`, `arrayUpdateLeaf_encFlat`, `lenLeaf_encFlat`, `encFlat_set`.
* `indexLeaf_nat`, `arrayUpdateLeaf_nat` — the leaves at a natural index.
* `enc_array_eq_map_tuple` — the ordinary encoding of an array of products as the
  array of the tuples of its rows.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open Hax.ListBlocks

variable {α : Type} [HaxTupleEnc α]

/-- The flat encoding of an array of right-nested products: the component lists of
    its elements, concatenated into one array. -/
def encFlat (a : Array α) : Value := .array (a.toList.map HaxTupleEnc.encList).flatten

/-- `array_update` at any natural index is `List.set` (which leaves the list
    unchanged out of range). -/
theorem arrayUpdateLeaf_nat (vs : List Value) (m : Nat) (v : Value) :
    arrayUpdateLeaf [.array vs, .int m, v] = some (.array (vs.set m v)) := by
  simp only [arrayUpdateLeaf, Int.toNat_natCast, Option.some.injEq, Value.array.injEq]
  split
  · rfl
  · rw [List.set_eq_of_length_le (by omega)]

/-- `index` at a natural index in range is the element. -/
theorem indexLeaf_nat (vs : List Value) (m : Nat) (v : Value) (h : vs[m]? = some v) :
    indexLeaf [.array vs, .int m] = some v := by
  simp [indexLeaf, indexVals, h]

/-- The rows of the flat encoding all have `k` components. -/
theorem encFlat_rows {k : Nat} (hk : ∀ p : α, (HaxTupleEnc.encList p).length = k) (a : Array α) :
    ∀ r ∈ a.toList.map HaxTupleEnc.encList, r.length = k := by
  intro r hr
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hr
  exact hk p

/-- **Element field read.**  `index` of the flat encoding at `i * k + off` is the
    encoding of field `off` of element `i`. -/
theorem indexLeaf_encFlat {k off : Nat} {β : Type} [HaxField α off β] [HaxEnc β]
    [HaxField.Lawful α off β] (hk : ∀ p : α, (HaxTupleEnc.encList p).length = k) (a : Array α)
    {i : Nat} (hi : i < a.size) (ho : off < k) :
    indexLeaf [encFlat a, .int ((i * k + off : Nat) : Int)] = some (enc (fieldGet off a[i])) := by
  apply indexLeaf_nat
  rw [flatten_getElem?_mul_add _ (encFlat_rows hk a) (by simpa using hi) ho]
  simp only [List.getElem_map, Array.getElem_toList]
  exact HaxField.Lawful.get_enc (i := off) a[i]

/-- **Element field write.**  `array_update` of the flat encoding at `i * k + off`
    with the encoding of `v` is the flat encoding of the array with field `off` of
    element `i` replaced by `v`. -/
theorem arrayUpdateLeaf_encFlat {k off : Nat} {β : Type} [HaxField α off β] [HaxEnc β]
    [HaxField.Lawful α off β] (hk : ∀ p : α, (HaxTupleEnc.encList p).length = k) (a : Array α)
    {i : Nat} (hi : i < a.size) (ho : off < k) (v : β) :
    arrayUpdateLeaf [encFlat a, .int ((i * k + off : Nat) : Int), enc v] =
      some (encFlat (a.set i (fieldSet off a[i] v))) := by
  rw [encFlat, arrayUpdateLeaf_nat,
    flatten_set_mul_add _ _ (encFlat_rows hk a) (by simpa using hi) ho]
  simp only [List.getElem_map, Array.getElem_toList, encFlat, Array.toList_set, List.map_set,
    HaxField.Lawful.set_enc]

/-- **Element write.**  Replacing row `i` of the flat encoding by the components of
    `p` is the flat encoding of the array with element `i` replaced by `p`. -/
theorem encFlat_set (a : Array α) (i : Nat) (hi : i < a.size) (p : α) :
    Value.array ((a.toList.map HaxTupleEnc.encList).set i (HaxTupleEnc.encList p)).flatten =
      encFlat (a.set i p) := by
  simp [encFlat, Array.toList_set, List.map_set]

/-- **Length.**  `len` of the flat encoding is `size * k`. -/
theorem lenLeaf_encFlat {k : Nat} (hk : ∀ p : α, (HaxTupleEnc.encList p).length = k)
    (a : Array α) : lenLeaf [encFlat a] = some (.int ((a.size * k : Nat) : Int)) := by
  simp only [lenLeaf, encFlat, flatten_length_of_forall _ (encFlat_rows hk a), List.length_map,
    Array.length_toList]

/-- The encoding of an array of products is the array of the tuples of the rows of
    its flat encoding. -/
theorem enc_array_eq_map_tuple [HaxEnc α]
    (henc : ∀ p : α, (enc p : Value) = .tuple (HaxTupleEnc.encList p)) (a : Array α) :
    (enc a : Value) = .array ((a.toList.map HaxTupleEnc.encList).map .tuple) := by
  rw [enc_array_toList, List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => henc p

end Hax.Ascent
