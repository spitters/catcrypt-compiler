/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Builtins
public import HaxAscent.Runtime

/-!
# Leaves of the runtime operations on values

The runtime functions of `HaxLean/Runtime.lean` that are polymorphic in the element type
(`Hax.index`, `Hax.repeat_`, `Hax.push`, `Hax.extend_from_slice`, …) have leaves on
values, one per operation, with a transport lemma for every element type with a `HaxEnc`:
the leaf maps the encoded arguments to the encoding of the runtime function's result.
Arrays are `.array`, integers `.int`.

`indexLeaf` on an empty array returns `.int 0`, the encoding of the default integer; its
transport lemma holds on every input for `Array Int` (`indexLeaf_int`) and on non-empty
arrays for every element type (`indexLeaf_pos`).

## Ranges

A range is the tagged tuple `rangeVal lo hi` (`hi = none` for an unbounded range), which
no integer index equals, and `indexLeaf` on a range value returns the slice
`Hax.slice_to`, `Hax.slice_from`, `Hax.slice_range` or the whole array that the printer
emits for `index arr (RangeTo n)`, `index arr (RangeFrom n)`, `index arr (Range lo hi)`
and `index arr RangeFull`. `iterLeaf` maps a bounded range to the array `Hax.range lo hi`.

The leaves are `irreducible` after their transport lemmas, so that a correspondence
derivation reads a call through the lemmas.

## Scalar leaves

`Leaf.orElse` combines two leaves; `intArrLeaf2`, `eqLeaf`, `notLeaf` and `negLeaf`
combine the `liftFn` leaves of a runtime function at `Int`, `Bool` and `Array Int`, whose
encodings are disjoint.

## Main definitions

* `Leaf.orElse`, `rangeVal`, `rangeOf?`, `sliceVals`
* `indexLeaf`, `arrayUpdateLeaf`, `repeatLeaf`, `arrayLitLeaf`, `lenLeaf`, `pushLeaf`,
  `reverseLeaf`, `vecRemoveLeaf`, `emptyLeaf`, `extendLeaf`, `copyLeaf`, `sliceUpdateLeaf`,
  `identLeaf`, `iterLeaf`,
  `truncateLeaf`, `isEmptyLeaf`, `someLeaf`, `unitLeaf`, `assertLeaf`, `constLeaf`,
  `rangeToLeaf`, `rangeFromLeaf`, `rangeLeaf`
* `intArrLeaf2`, `eqLeaf`, `notLeaf`, `negLeaf`

## Main results

* `Hax.slice_update_map` — `slice_update` commutes with `Array.map`
* `foldRange_eq_foldRangeSpec` — `Hax.foldRange` is the fold of the loop rule
* `liftFn_eq_none`, `leaf1_int_none`, `leaf2_int_none`, `leaf1_bool_none`,
  `leaf2_bool_none` — a function leaf is `none` outside the encoding of its arguments
* `indexLeaf_int`, `indexLeaf_pos`, `indexLeaf_slice_to`, `indexLeaf_slice_from`,
  `indexLeaf_slice_range`, `indexLeaf_full`, `sliceUpdateLeaf_enc` and the transport
  lemmas of the other value leaves
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

/-- **`slice_update` is natural.** Mapping a function over the result of a range update is
    the range update of the mapped arrays. -/
theorem slice_update_map {α β : Type} (f : α → β) (a : Array α) (lo hi : Int)
    (src : Array α) :
    (slice_update a lo hi src).map f = slice_update (a.map f) lo hi (src.map f) := by
  unfold slice_update
  simp only [Array.size_map]
  generalize List.range (min (hi.toNat - lo.toNat) src.size) = ks
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons, Array.getElem?_map]
    rw [ih]
    rcases src[k]? with _ | v <;> simp [Array.map_setIfInBounds]

end Hax

namespace Hax.Ascent

/-! ## The runtime's counted fold -/

/-- **`Hax.foldRange` is the fold of the loop rule.** -/
theorem foldRange_eq_foldRangeSpec {A : Type} (lo hi : Int) (a : A) (f : Int → A → A) :
    Hax.foldRange lo hi a f = foldRangeSpec lo hi a f := by
  unfold Hax.foldRange foldRangeSpec
  suffices H : ∀ n i a, Hax.foldRange.go f n i a = foldFrom f n i a from H _ _ _
  intro n
  induction n with
  | zero => intro i a; rfl
  | succ n ih => intro i a; exact ih (i + 1) (f i a)

/-! ## Combining leaves -/

/-- The leaf that applies `l₁`, and `l₂` to the arguments on which `l₁` returns `none`. -/
def Leaf.orElse (l₁ l₂ : Leaf) : Leaf := fun vs => (l₁ vs).or (l₂ vs)

theorem Leaf.orElse_of_some {l₁ l₂ : Leaf} {vs : List Value} {v : Value}
    (h : l₁ vs = some v) : Leaf.orElse l₁ l₂ vs = some v := by
  simp [Leaf.orElse, h]

theorem Leaf.orElse_of_none {l₁ l₂ : Leaf} {vs : List Value} (h : l₁ vs = none) :
    Leaf.orElse l₁ l₂ vs = l₂ vs := by
  simp [Leaf.orElse, h]

/-- A function leaf is `none` on a list that encodes no argument tuple. -/
theorem liftFn_eq_none {A B : Type} [HaxArgs A] [HaxEnc B] (g : A → B) {vs : List Value}
    (h : ∀ a : A, encArgs a ≠ vs) : liftFn g vs = none := by
  unfold liftFn
  exact dif_neg fun ⟨a, ha⟩ => h a ha

section NoneLemmas

variable {β : Type} [HaxEnc β]

theorem leaf1_int_none (g : Int → β) {v : Value} (hv : ∀ n : Int, v ≠ .int n) :
    leaf1 g [v] = none :=
  liftFn_eq_none _ fun p h => hv p.1 (List.cons.inj h).1.symm

theorem leaf2_int_none (g : Int → Int → β) {v : Value} (w : Value)
    (hv : ∀ n : Int, v ≠ .int n) : leaf2 g [v, w] = none :=
  liftFn_eq_none _ fun p h => hv p.1 (List.cons.inj h).1.symm

theorem leaf1_bool_none (g : Bool → β) {v : Value} (hv : ∀ b : Bool, v ≠ .bool b) :
    leaf1 g [v] = none :=
  liftFn_eq_none _ fun p h => hv p.1 (List.cons.inj h).1.symm

theorem leaf2_bool_none (g : Bool → Bool → β) {v : Value} (w : Value)
    (hv : ∀ b : Bool, v ≠ .bool b) : leaf2 g [v, w] = none :=
  liftFn_eq_none _ fun p h => hv p.1 (List.cons.inj h).1.symm

end NoneLemmas

/-! ## Ranges -/

/-- The value of a range `lo..hi`, and of `lo..` when `hi = none`: a tuple tagged by a
    leading `.unit`. -/
def rangeVal (lo : Int) (hi : Option Int) : Value :=
  .tuple [.unit, .int lo, .option (hi.map .int)]

/-- The bounds of a range value. -/
def rangeOf? : Value → Option (Int × Option Int)
  | .tuple [.unit, .int lo, .option none] => some (lo, none)
  | .tuple [.unit, .int lo, .option (some (.int hi))] => some (lo, some hi)
  | _ => none

theorem rangeOf?_rangeVal (lo : Int) (hi : Option Int) :
    rangeOf? (rangeVal lo hi) = some (lo, hi) := by
  cases hi <;> rfl

theorem rangeVal_isControlFlow (lo : Int) (hi : Option Int) :
    (rangeVal lo hi).isControlFlow = false := rfl

theorem rangeOf?_int (n : Int) : rangeOf? (.int n) = none := rfl

theorem rangeOf?_array (vs : List Value) : rangeOf? (.array vs) = none := rfl

/-- The slice `lo..hi` of a list; `hi = none` is the end of the list. -/
def sliceVals (vs : List Value) (lo : Int) (hi : Option Int) : List Value :=
  vs.extract lo.toNat ((hi.map Int.toNat).getD vs.length)

/-! ## Value leaves -/

/-- The element at `i`, the first element when `i` is out of range, and `.int 0` on the
    empty list: the runtime's `Hax.index` on the encoding. -/
def indexVals (vs : List Value) (i : Int) : Value :=
  vs[i.toNat]?.getD (vs.headD (.int 0))

/-- `index` and `index_mut`: an element for an integer index, a slice for a range. -/
def indexLeaf : Leaf
  | [.array vs, .int i] => some (indexVals vs i)
  | [.array vs, r] => (rangeOf? r).map fun p => .array (sliceVals vs p.1 p.2)
  | _ => none

/-- `array_update`: `Hax.array_update`. -/
def arrayUpdateLeaf : Leaf
  | [.array vs, .int i, v] =>
    some (.array (if i.toNat < vs.length then vs.set i.toNat v else vs))
  | _ => none

/-- `repeat` and `from_elem`: `Hax.repeat_`, `Hax.from_elem`. -/
def repeatLeaf : Leaf
  | [v, .int n] => some (.array (List.replicate n.toNat v))
  | _ => none

/-- `array_lit`: the array of the arguments. -/
def arrayLitLeaf : Leaf := fun vs => some (.array vs)

/-- `len`: `Hax.array_len`. -/
def lenLeaf : Leaf
  | [.array vs] => some (.int vs.length)
  | _ => none

/-- `push`: `Hax.push`. -/
def pushLeaf : Leaf
  | [.array vs, v] => some (.array (vs ++ [v]))
  | _ => none

/-- `vec_remove`: the element at an index in range and the array without it, the
    `vec_remove` builtin of the semantics; undefined out of range. -/
def vecRemoveLeaf : Leaf
  | [.array vs, .int i] =>
    if 0 ≤ i then vs[i.toNat]?.map fun x => .tuple [x, .array (vs.eraseIdx i.toNat)] else none
  | _ => none

/-- `slice_reverse`: `Hax.slice_reverse`, the elements in reverse order. -/
def reverseLeaf : Leaf
  | [.array vs] => some (.array vs.reverse)
  | _ => none

/-- `new` without arguments and `with_capacity`: the empty array. -/
def emptyLeaf : Leaf
  | [] => some (.array [])
  | [.int _] => some (.array [])
  | _ => none

/-- `extend_from_slice`: `Hax.extend_from_slice`. -/
def extendLeaf : Leaf
  | [.array a, .array b] => some (.array (a ++ b))
  | _ => none

/-- `copy_from_slice`: `Hax.copy_from_slice`, the source. -/
def copyLeaf : Leaf
  | [.array _, .array b] => some (.array b)
  | _ => none

/-- `slice_update`: `Hax.slice_update` on the value arrays. -/
def sliceUpdateLeaf : Leaf
  | [.array a, .int lo, .int hi, .array src] =>
    some (.array (Hax.slice_update a.toArray lo hi src.toArray).toList)
  | _ => none

/-- `deref`, `deref_mut`, `clone`, `to_vec`, `into_vec`, `from`: the identity. -/
def identLeaf : Leaf
  | [v] => some v
  | _ => none

/-- `iter`, `into_iter`, `collect`: the identity, and the array `Hax.range lo hi` of a
    bounded range. -/
def iterLeaf : Leaf
  | [v] =>
    match rangeOf? v with
    | some (lo, some hi) => some (.array ((Hax.range lo hi).toList.map .int))
    | some (_, none) => none
    | none => some v
  | _ => none

/-- `truncate`: `Hax.truncate`, the array. -/
def truncateLeaf : Leaf
  | [.array vs, .int _] => some (.array vs)
  | _ => none

/-- `is_empty`: `Hax.is_empty`. -/
def isEmptyLeaf : Leaf
  | [.array vs] => some (.bool vs.isEmpty)
  | _ => none

/-- `Some`: `Option.some`. -/
def someLeaf : Leaf
  | [v] => some (.option (some v))
  | _ => none

/-- A leaf returning `.unit` on every argument list: `panic`, `panic_fmt`, which the
    printer renders as `()`. -/
def unitLeaf : Leaf := fun _ => some .unit

/-- `assert_failed`: `Hax.assert_failed`, the unit value. -/
def assertLeaf : Leaf
  | [_, _, _, _] => some .unit
  | _ => none

/-- A leaf of a constant value on the empty argument list: `None`, `RangeFull`. -/
def constLeaf (v : Value) : Leaf
  | [] => some v
  | _ => none

/-- `RangeTo`. -/
def rangeToLeaf : Leaf
  | [.int n] => some (rangeVal 0 (some n))
  | _ => none

/-- `RangeFrom`. -/
def rangeFromLeaf : Leaf
  | [.int n] => some (rangeVal n none)
  | _ => none

/-- `Range`. -/
def rangeLeaf : Leaf
  | [.int lo, .int hi] => some (rangeVal lo (some hi))
  | _ => none

/-! ### Transport of the value leaves -/

section Transport

variable {α : Type} [HaxEnc α]

theorem enc_array_toList (a : Array α) : enc a = .array (a.toList.map enc) := rfl

theorem sliceVals_enc (a : Array α) (lo : Int) (hi : Option Int) :
    sliceVals (a.toList.map enc) lo hi =
      (a.extract lo.toNat ((hi.map Int.toNat).getD a.size)).toList.map enc := by
  simp [sliceVals, Array.toList_extract, List.extract, List.map_take, List.map_drop]

theorem indexLeaf_int (a : Array Int) (i : Int) :
    indexLeaf [enc a, .int i] = some (.int (Hax.index a i)) := by
  simp only [indexLeaf, enc_array_toList, indexVals, Hax.index, Option.some.injEq]
  by_cases h : i.toNat < a.size
  · simp [h]
  · rw [dif_neg h, List.getElem?_eq_none (by simpa using h)]
    by_cases h0 : 0 < a.size
    · rw [dif_pos h0]
      obtain ⟨l⟩ := a
      cases l with
      | nil => simp at h0
      | cons x l => rfl
    · rw [dif_neg h0]
      obtain ⟨l⟩ := a
      cases l with
      | nil => rfl
      | cons x l => simp at h0

theorem indexLeaf_pos [Inhabited α] (a : Array α) (h0 : 0 < a.size) (i : Int) :
    indexLeaf [enc a, .int i] = some (enc (Hax.index a i)) := by
  simp only [indexLeaf, enc_array_toList, indexVals, Hax.index, Option.some.injEq]
  by_cases h : i.toNat < a.size
  · simp [h]
  · rw [dif_neg h, List.getElem?_eq_none (by simpa using h), dif_pos h0]
    obtain ⟨l⟩ := a
    cases l with
    | nil => simp at h0
    | cons x l => rfl

theorem indexLeaf_range (a : Array α) (lo : Int) (hi : Option Int) :
    indexLeaf [enc a, rangeVal lo hi] =
      some (enc (a.extract lo.toNat ((hi.map Int.toNat).getD a.size))) := by
  have : indexLeaf [enc a, rangeVal lo hi] =
      (rangeOf? (rangeVal lo hi)).map fun p =>
        Value.array (sliceVals (a.toList.map enc) p.1 p.2) := by
    cases hi <;> rfl
  rw [this, rangeOf?_rangeVal, Option.map_some, sliceVals_enc]
  rfl

theorem indexLeaf_slice_to (a : Array α) (n : Int) :
    indexLeaf [enc a, rangeVal 0 (some n)] = some (enc (Hax.slice_to a n)) := by
  rw [indexLeaf_range]; rfl

theorem indexLeaf_slice_from (a : Array α) (n : Int) :
    indexLeaf [enc a, rangeVal n none] = some (enc (Hax.slice_from a n)) := by
  rw [indexLeaf_range]; rfl

theorem indexLeaf_slice_range (a : Array α) (lo hi : Int) :
    indexLeaf [enc a, rangeVal lo (some hi)] = some (enc (Hax.slice_range a lo hi)) := by
  rw [indexLeaf_range]; rfl

theorem indexLeaf_full (a : Array α) :
    indexLeaf [enc a, rangeVal 0 none] = some (enc a) := by
  rw [indexLeaf_range]
  simp [Array.extract_size]

theorem arrayUpdateLeaf_enc (a : Array α) (i : Int) (x : α) :
    arrayUpdateLeaf [enc a, .int i, enc x] = some (enc (Hax.array_update a i x)) := by
  simp only [arrayUpdateLeaf, enc_array_toList, Hax.array_update, List.length_map,
    Array.length_toList, Option.some.injEq]
  split
  · simp [List.map_set]
  · rfl

theorem repeatLeaf_enc (x : α) (n : Int) :
    repeatLeaf [enc x, .int n] = some (enc (Hax.repeat_ x n)) := by
  simp [repeatLeaf, Hax.repeat_, List.map_replicate]

theorem repeatLeaf_from_elem (x : α) (n : Int) :
    repeatLeaf [enc x, .int n] = some (enc (Hax.from_elem x n)) :=
  repeatLeaf_enc x n

theorem arrayLitLeaf_enc (l : List α) :
    arrayLitLeaf (l.map enc) = some (enc l.toArray) := rfl

theorem lenLeaf_enc (a : Array α) : lenLeaf [enc a] = some (.int (Hax.array_len a)) := by
  simp [lenLeaf, Hax.array_len]

theorem pushLeaf_enc (a : Array α) (x : α) :
    pushLeaf [enc a, enc x] = some (enc (Hax.push a x)) := by
  simp [pushLeaf, Hax.push]

theorem vecRemoveLeaf_enc [Inhabited α] (a : Array α) (i : Int) (h0 : 0 ≤ i)
    (h : i < Hax.array_len a) :
    vecRemoveLeaf [enc a, .int i] = some (enc (Hax.vec_remove a i)) := by
  have hi : i.toNat < a.size := by simp only [Hax.array_len] at h; omega
  simp only [vecRemoveLeaf, enc_array_toList, h0, if_true, Hax.vec_remove, hi, and_self,
    dite_true, List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq]
  show _ = Value.tuple [enc a[i.toNat], enc (a.eraseIdx i.toNat hi)]
  rw [enc_array_toList (a.eraseIdx i.toNat hi), Array.toList_eraseIdx]
  simp [List.eraseIdx_eq_take_drop_succ, List.map_take, List.map_drop]

theorem reverseLeaf_enc (a : Array α) :
    reverseLeaf [enc a] = some (enc (Hax.slice_reverse a)) := by
  simp [reverseLeaf, Hax.slice_reverse, enc_array_toList, List.map_reverse]

theorem emptyLeaf_new : emptyLeaf [] = some (enc (#[] : Array α)) := rfl

theorem emptyLeaf_with_capacity (n : Int) :
    emptyLeaf [.int n] = some (enc (Hax.with_capacity (α := α) n)) := rfl

theorem extendLeaf_enc (a b : Array α) :
    extendLeaf [enc a, enc b] = some (enc (Hax.extend_from_slice a b)) := by
  simp [extendLeaf, Hax.extend_from_slice]

theorem copyLeaf_enc (a b : Array α) :
    copyLeaf [enc a, enc b] = some (enc (Hax.copy_from_slice a b)) := rfl

theorem sliceUpdateLeaf_enc (a : Array α) (lo hi : Int) (src : Array α) :
    sliceUpdateLeaf [enc a, .int lo, .int hi, enc src] =
      some (enc (Hax.slice_update a lo hi src)) := by
  simp only [sliceUpdateLeaf, enc_array_toList, Option.some.injEq, Value.array.injEq]
  simp only [← Array.toList_map, Array.toArray_toList, Hax.slice_update_map]

theorem identLeaf_deref {β : Type} [HaxEnc β] (x : β) :
    identLeaf [enc x] = some (enc (Hax.deref x)) := rfl

theorem identLeaf_to_vec {β : Type} [HaxEnc β] (x : β) :
    identLeaf [enc x] = some (enc (Hax.to_vec x)) := rfl

theorem identLeaf_clone {β : Type} [HaxEnc β] (x : β) :
    identLeaf [enc x] = some (enc (Hax.clone x)) := rfl

theorem identLeaf_into_vec {β : Type} [HaxEnc β] (x : β) :
    identLeaf [enc x] = some (enc (Hax.into_vec x)) := rfl

theorem identLeaf_from_val {β : Type} [HaxEnc β] (x : β) :
    identLeaf [enc x] = some (enc (Hax.from_val x)) := rfl

theorem iterLeaf_enc (a : Array α) : iterLeaf [enc a] = some (enc (Hax.iter a)) := rfl

theorem iterLeaf_into_iter (a : Array α) :
    iterLeaf [enc a] = some (enc (Hax.into_iter a)) := rfl

theorem iterLeaf_range (lo hi : Int) :
    iterLeaf [rangeVal lo (some hi)] = some (enc (Hax.range lo hi)) := rfl

theorem truncateLeaf_enc (a : Array α) (n : Int) :
    truncateLeaf [enc a, .int n] = some (enc (Hax.truncate a n)) := rfl

theorem isEmptyLeaf_enc (a : Array α) :
    isEmptyLeaf [enc a] = some (.bool (Hax.is_empty a)) := by
  simp only [isEmptyLeaf, enc_array_toList, Hax.is_empty, Option.some.injEq,
    Value.bool.injEq]
  obtain ⟨l⟩ := a
  cases l <;> rfl

theorem someLeaf_enc (x : α) : someLeaf [enc x] = some (enc (some x)) := rfl

theorem constLeaf_none : constLeaf (.option none) [] = some (enc (none : Option α)) := rfl

theorem constLeaf_nil (v : Value) : constLeaf v [] = some v := rfl

theorem rangeToLeaf_int (n : Int) :
    rangeToLeaf [.int n] = some (rangeVal 0 (some n)) := rfl

theorem rangeFromLeaf_int (n : Int) : rangeFromLeaf [.int n] = some (rangeVal n none) := rfl

theorem rangeLeaf_int (lo hi : Int) :
    rangeLeaf [.int lo, .int hi] = some (rangeVal lo (some hi)) := rfl

theorem unitLeaf_apply (vs : List Value) : unitLeaf vs = some .unit := rfl

end Transport

attribute [irreducible] indexLeaf arrayUpdateLeaf repeatLeaf arrayLitLeaf lenLeaf pushLeaf
  reverseLeaf vecRemoveLeaf
  emptyLeaf extendLeaf copyLeaf sliceUpdateLeaf identLeaf iterLeaf truncateLeaf isEmptyLeaf
  someLeaf unitLeaf assertLeaf constLeaf rangeToLeaf rangeFromLeaf rangeLeaf rangeVal

/-! ## Scalar leaves -/

/-- An integer operation that the runtime also applies pointwise to `Array Int`. -/
noncomputable def intArrLeaf2 (g : Int → Int → Int)
    (h : Array Int → Array Int → Array Int) : Leaf :=
  Leaf.orElse (leaf2 g) (leaf2 h)

/-- An operation the runtime applies to `Int`, `Bool` and `Array Int`. -/
noncomputable def eqLeaf (gi : Int → Int → Bool) (gb : Bool → Bool → Bool)
    (ga : Array Int → Array Int → Bool) : Leaf :=
  Leaf.orElse (leaf2 gi) (Leaf.orElse (leaf2 gb) (leaf2 ga))

/-- `Hax.Not` at `Bool` and at `Int`. -/
noncomputable def notLeaf : Leaf :=
  Leaf.orElse (leaf1 (Hax.Not : Bool → Bool)) (leaf1 (Hax.Not : Int → Int))

/-- `Hax.neg` at `Int` and at `Array Int`. -/
noncomputable def negLeaf : Leaf :=
  Leaf.orElse (leaf1 (Hax.neg : Int → Int)) (leaf1 (Hax.neg : Array Int → Array Int))

end Hax.Ascent
