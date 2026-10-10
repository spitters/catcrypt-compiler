/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.RuntimeLeaves

/-!
# The builtin table of the runtime operations

The literal of a haxpipeT extraction calls the runtime operations by the names of the
hax AST (`index`, `Add`, `cast#8`, …), and the printed surface calls the functions of
`HaxLean/Runtime.lean` that the printer's `runtimeName` and `widthAwareRuntime` assign to
those names. `runtimeBuiltins base` interprets each such name by the leaf of that runtime
function (`HaxAscent/Ascent/RuntimeLeaves.lean`) under the encoding of the extractions,
`Int` as `.int`, `Bool` as `.bool`, `Array α` as `.array`, and every other name by `base`.

The table specifies the meaning of the current runtime; where the runtime differs from
Rust, so does the table. The known differences are:

* untagged `Add`, `Sub`, `Mul` and `wrapping_add`, `wrapping_mul` are unbounded integer
  operations, without overflow check or wrap-around;
* `Div` and `Rem` are the `Int` division and remainder of Lean (`div (-7) 2 = -4`), where
  Rust truncates, and division by zero returns `0`;
* the width tags carry no signedness, and `mod2w` sends a negative argument to `0`, so
  `cast#w`, `BitXor#w`, `Shr#w` and the other tagged operations neither sign-extend nor
  shift arithmetically;
* `Shl#w` and `Shr#w` with a shift of at least `w` return a value where Rust panics;
* `index` out of range returns the first element, and the default element on an empty
  array, where Rust panics; a negative index reads position `0`;
* the arguments of `&&` and `||` are both evaluated;
* no operation is 128-bit specific: `cast#128` and the other tags at width 128 are the
  width-parametric runtime functions at `w = 128`.

## Names

`runtimeTable` holds the untagged names. A tagged name `op#w`, a single `#` followed by
decimal digits or by `size`, is parsed by `parseTag`, and `widthTable` gives the family
`op` a leaf at every width `w`: `cast#w` is `Hax.castVal_w w`, `BitXor#w` is
`Hax.bitxor_w w`, and so on. The tag `size` is the width `Hax.usizeBits`, as in the
printer's `widthAwareRuntime`. A tagged name whose family has no entry, and every name
with several `#` (the struct updates `struct_update#S#i#n`), is left to `base`.

The printer rewrites `index arr (RangeTo n)` into `Hax.slice_to arr n` and the other range
arguments of `index` and `index_mut` into slices, `index_mut arr i` into `Hax.index arr i`,
`collect (Range lo hi)` into `Hax.range lo hi`, `array_lit` into an array literal,
`new []` into `#[]`, and `panic` into `()`. The table follows each: the range constructors
return the tagged value `rangeVal`, and `index` on it returns the slice. A range
constructor anywhere else would have the runtime meaning `Hax.RangeTo n = n`, which the
table does not give it; in the certified extractions every range constructor is an
argument of `index`, `index_mut` or `collect`.

Names the table leaves to `base`: `map` and `flat_map` (their argument is a closure,
which `denote'` does not evaluate), `Ok` and `Err` (no `HaxEnc` for `Except`), `literal`
(the default of a type the leaf does not see), and `new` with arguments (the opaque
`Hax.new`). `str_opaque`, the extraction of a string literal, is the unit value, the
encoding of every string. A tagged name whose family has no width entry, such as the
dependency constant `MAX#32`, is read from `base` (`runtimeBuiltins_of_baseTag`). `min`
and `max`, which the printer emits unchanged, are the `min` and `max` of `Int`. A tuple
projection is the literal's `.proj e i` with the flat component index `i`, read by the
generator (`corresB_proj`) and not by the table.

## Main definitions

* `parseTag`, `widthTable`, `runtimeTable`, `runtimeBuiltins`

## Main results

* `runtimeBuiltins_of_lookup`, `runtimeBuiltins_of_tag`, `runtimeBuiltins_of_base` —
  reading the table
* `RuntimeOps.index_int`, `RuntimeOps.index_slice_to`, `RuntimeOps.slice_update_enc`,
  `RuntimeOps.Ne_int`, … — the `corres_app` equation of each name
* `RuntimeOps.tagged1`, `RuntimeOps.tagged2`, `RuntimeOps.cast_w` — the equation of a
  member of a width family, with `RuntimeOps.cast8`, `RuntimeOps.BitXor32`,
  `RuntimeOps.wrapping_add64`, `RuntimeOps.Not64` as instances
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## The width families -/

/-- The value of a nonempty list of decimal digits. -/
def digitsVal (ds : List Char) : Option Nat :=
  if !ds.isEmpty && ds.all Char.isDigit then
    some (ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  else none

/-- The family and width of a tagged name `op#w`: the part before the first `#`, and the
    rest when it is a nonempty string of decimal digits, or `Hax.usizeBits` when it is
    `size`, the tag of the `usize` and `isize` operands. -/
def parseTag (f : String) : Option (String × Nat) :=
  match f.toList.span (· != '#') with
  | (op, _ :: ds) =>
    if ds = ['s', 'i', 'z', 'e'] then some (String.ofList op, Hax.usizeBits)
    else (digitsVal ds).map fun w => (String.ofList op, w)
  | (_, []) => none

/-- The width families, after the printer's `widthAwareRuntime`: each family name with
    its leaf at every width. -/
noncomputable def widthTable : List (String × (Nat → Leaf)) :=
  [("cast", fun w => leaf1 (Hax.castVal_w w)),
   ("BitAnd", fun w => leaf2 (Hax.bitand_w w)),
   ("bitand", fun w => leaf2 (Hax.bitand_w w)),
   ("BitOr", fun w => leaf2 (Hax.bitor_w w)),
   ("bitor", fun w => leaf2 (Hax.bitor_w w)),
   ("BitXor", fun w => leaf2 (Hax.bitxor_w w)),
   ("bitxor", fun w => leaf2 (Hax.bitxor_w w)),
   ("Shl", fun w => leaf2 (Hax.shl_w w)), ("shl", fun w => leaf2 (Hax.shl_w w)),
   ("Shr", fun w => leaf2 (Hax.shr_w w)), ("shr", fun w => leaf2 (Hax.shr_w w)),
   ("Not", fun w => leaf1 (Hax.bitnot_w w)),
   ("bitnot", fun w => leaf1 (Hax.bitnot_w w)),
   ("rotate_right", fun w => leaf2 (Hax.rotate_right_w w)),
   ("rotate_left", fun w => leaf2 (Hax.rotate_left_w w)),
   ("wrapping_add", fun w => leaf2 (Hax.wrapping_add_w w)),
   ("wrapping_sub", fun w => leaf2 (Hax.wrapping_sub_w w)),
   ("wrapping_mul", fun w => leaf2 (Hax.wrapping_mul_w w)),
   ("wrapping_neg", fun w => leaf1 (Hax.wrapping_neg_w w)),
   ("to_be_bytes", fun w => leaf1 (Hax.to_be_bytes_w w)),
   ("to_le_bytes", fun w => leaf1 (Hax.to_le_bytes_w w)),
   ("from_be_bytes", fun w => leaf1 (Hax.from_be_bytes_w w)),
   ("from_le_bytes", fun w => leaf1 (Hax.from_le_bytes_w w)),
   ("overflowing_add", fun w => leaf2 (Hax.overflowing_add_w w)),
   ("overflowing_sub", fun w => leaf2 (Hax.overflowing_sub_w w))]

/-! ## The table of untagged names -/

/-- The untagged runtime names, after the printer's `runtimeName` and its rewrites of
    `index`, `index_mut`, `collect`, `iter`, `array_lit`, `Not`, `new` and `panic`. -/
noncomputable def runtimeTable : Table :=
  [-- arrays and collections
   ("index", indexLeaf), ("index_mut", indexLeaf),
   ("array_update", arrayUpdateLeaf),
   ("repeat", repeatLeaf), ("from_elem", repeatLeaf),
   ("array_lit", arrayLitLeaf),
   ("len", lenLeaf),
   ("push", pushLeaf),
   ("slice_reverse", reverseLeaf),
   ("vec_remove", vecRemoveLeaf),
   ("with_capacity", emptyLeaf), ("new", emptyLeaf),
   ("extend_from_slice", extendLeaf),
   ("copy_from_slice", copyLeaf),
   ("slice_update", sliceUpdateLeaf),
   ("deref", identLeaf), ("deref_mut", identLeaf), ("clone", identLeaf),
   ("to_vec", identLeaf), ("into_vec", identLeaf), ("from", identLeaf),
   ("iter", iterLeaf), ("into_iter", iterLeaf), ("collect", iterLeaf),
   ("truncate", truncateLeaf),
   ("is_empty", isEmptyLeaf),
   ("RangeTo", rangeToLeaf), ("RangeFrom", rangeFromLeaf), ("Range", rangeLeaf),
   ("RangeFull", constLeaf (rangeVal 0 none)),
   -- arithmetic
   ("Add", intArrLeaf2 Hax.add Hax.add), ("add", intArrLeaf2 Hax.add Hax.add),
   ("Sub", intArrLeaf2 Hax.sub Hax.sub), ("sub", intArrLeaf2 Hax.sub Hax.sub),
   ("Mul", intArrLeaf2 Hax.mul Hax.mul), ("mul", intArrLeaf2 Hax.mul Hax.mul),
   ("Div", intArrLeaf2 Hax.div Hax.div), ("div", intArrLeaf2 Hax.div Hax.div),
   ("Rem", intArrLeaf2 Hax.rem Hax.rem), ("rem", intArrLeaf2 Hax.rem Hax.rem),
   ("Neg", negLeaf), ("neg", negLeaf),
   -- comparison and logic
   ("Lt", leaf2 (Hax.lt : Int → Int → Bool)), ("lt", leaf2 (Hax.lt : Int → Int → Bool)),
   ("Le", leaf2 (Hax.le : Int → Int → Bool)), ("le", leaf2 (Hax.le : Int → Int → Bool)),
   ("Gt", leaf2 (Hax.gt : Int → Int → Bool)), ("gt", leaf2 (Hax.gt : Int → Int → Bool)),
   ("Ge", leaf2 (Hax.ge : Int → Int → Bool)), ("ge", leaf2 (Hax.ge : Int → Int → Bool)),
   ("Eq", eqLeaf Hax.beq Hax.beq Hax.beq), ("eq", eqLeaf Hax.beq Hax.beq Hax.beq),
   ("Ne", eqLeaf Hax.bne Hax.bne Hax.bne), ("ne", eqLeaf Hax.bne Hax.bne Hax.bne),
   ("&&", leaf2 Hax.band), ("and", leaf2 Hax.band), ("And", leaf2 Hax.band),
   ("||", leaf2 Hax.bor), ("or", leaf2 Hax.bor), ("Or", leaf2 Hax.bor),
   ("not", leaf1 Hax.bnot),
   ("Not", notLeaf),
   ("None", constLeaf (.option none)),
   ("Some", someLeaf),
   -- untagged bitwise and wrapping operations
   ("Shl", leaf2 Hax.shl), ("shl", leaf2 Hax.shl),
   ("Shr", leaf2 Hax.shr), ("shr", leaf2 Hax.shr),
   ("BitAnd", leaf2 Hax.bitand), ("bitand", leaf2 Hax.bitand),
   ("BitOr", leaf2 Hax.bitor), ("bitor", leaf2 Hax.bitor),
   ("BitXor", leaf2 Hax.bitxor), ("bitxor", leaf2 Hax.bitxor),
   ("bitnot", leaf1 Hax.bitnot),
   ("rotate_right", leaf2 Hax.rotate_right), ("rotate_left", leaf2 Hax.rotate_left),
   ("wrapping_add", leaf2 (Hax.wrapping_add : Int → Int → Int)),
   ("wrapping_sub", leaf2 (Hax.wrapping_sub : Int → Int → Int)),
   ("wrapping_mul", leaf2 (Hax.wrapping_mul : Int → Int → Int)),
   ("cast", leaf1 Hax.castVal),
   ("min", leaf2 (min : Int → Int → Int)), ("max", leaf2 (max : Int → Int → Int)),
   ("count_ones", leaf1 Hax.count_ones),
   -- rendered as the unit value
   ("panic", unitLeaf), ("panic_fmt", unitLeaf),
   -- a string literal, the encoding of every `String`
   ("str_opaque", unitLeaf),
   ("assert_failed", assertLeaf)]

/-- **The runtime builtin table over `base`.** An untagged runtime name is read from
    `runtimeTable`, a tagged name `op#w` of a family of `widthTable` from that family at
    width `w`, and every other name from `base`. -/
noncomputable def runtimeBuiltins (base : Builtins) : Builtins := fun f vs =>
  match runtimeTable.lookup f with
  | some g => g vs
  | none =>
    match parseTag f with
    | some (op, w) =>
      match widthTable.lookup op with
      | some g => g w vs
      | none => base f vs
    | none => base f vs

section Reading

variable {base : Builtins} {f : String} {vs : List Value}

theorem runtimeBuiltins_of_lookup {g : Leaf} (h : runtimeTable.lookup f = some g) :
    runtimeBuiltins base f vs = g vs := by
  simp only [runtimeBuiltins, h]

/-- **A member of a width family.** -/
theorem runtimeBuiltins_of_tag {op : String} {w : Nat} {g : Nat → Leaf}
    (h₁ : runtimeTable.lookup f = none) (h₂ : parseTag f = some (op, w))
    (h₃ : widthTable.lookup op = some g) :
    runtimeBuiltins base f vs = g w vs := by
  simp only [runtimeBuiltins, h₁, h₂, h₃]

/-- A name that is neither a runtime name nor tagged is read from the base table. -/
theorem runtimeBuiltins_of_base (h₁ : runtimeTable.lookup f = none)
    (h₂ : parseTag f = none) :
    runtimeBuiltins base f vs = base f vs := by
  simp only [runtimeBuiltins, h₁, h₂]

/-- The names `runtimeBuiltins` reads from its base table when `runtimeTable` has no entry
    for them: an untagged name, or a tagged name `op#w` whose family `op` has no entry in
    `widthTable` (a dependency constant `MAX#32`). -/
noncomputable def baseTag (f : String) : Bool :=
  match parseTag f with
  | some (op, _) => (widthTable.lookup op).isNone
  | none => true

/-- A name that is not a runtime name, and is untagged or tagged outside the width
    families, is read from the base table. -/
theorem runtimeBuiltins_of_baseTag (h₁ : runtimeTable.lookup f = none)
    (h₂ : baseTag f = true) :
    runtimeBuiltins base f vs = base f vs := by
  unfold baseTag at h₂
  rcases ht : parseTag f with _ | ⟨op, w⟩
  · exact runtimeBuiltins_of_base h₁ ht
  · rw [ht] at h₂
    simp only [runtimeBuiltins, h₁, ht, Option.isNone_iff_eq_none.mp h₂]

theorem baseTag_of_parseTag (h : parseTag f = none) : baseTag f = true := by
  simp only [baseTag, h]

theorem baseTag_MAX32 : baseTag "MAX#32" = true := by decide

theorem parseTag_cast8 : parseTag "cast#8" = some ("cast", 8) := by decide

theorem parseTag_struct_update : parseTag "struct_update#Sha256State#1#4" = none := by
  decide

theorem parseTag_hash : parseTag "hash" = none := by decide

theorem parseTag_cast_size : parseTag "cast#size" = some ("cast", Hax.usizeBits) := rfl

end Reading

attribute [irreducible] runtimeBuiltins

/-! ## The `corres_app` equations -/

namespace RuntimeOps

variable {base : Builtins} {α : Type} [HaxEnc α]

section Arrays

theorem index_int (a : Array Int) (i : Int) :
    runtimeBuiltins base "index" [enc a, .int i] = some (.int (Hax.index a i)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_int a i)

theorem index_mut_int (a : Array Int) (i : Int) :
    runtimeBuiltins base "index_mut" [enc a, .int i] = some (.int (Hax.index a i)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_int a i)

theorem index_pos [Inhabited α] (a : Array α) (h : 0 < a.size) (i : Int) :
    runtimeBuiltins base "index" [enc a, .int i] = some (enc (Hax.index a i)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_pos a h i)

theorem index_mut_pos [Inhabited α] (a : Array α) (h : 0 < a.size) (i : Int) :
    runtimeBuiltins base "index_mut" [enc a, .int i] = some (enc (Hax.index a i)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_pos a h i)

theorem index_slice_to (a : Array α) (n : Int) :
    runtimeBuiltins base "index" [enc a, rangeVal 0 (some n)] =
      some (enc (Hax.slice_to a n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_slice_to a n)

theorem index_mut_slice_to (a : Array α) (n : Int) :
    runtimeBuiltins base "index_mut" [enc a, rangeVal 0 (some n)] =
      some (enc (Hax.slice_to a n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_slice_to a n)

theorem index_slice_from (a : Array α) (n : Int) :
    runtimeBuiltins base "index" [enc a, rangeVal n none] =
      some (enc (Hax.slice_from a n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_slice_from a n)

theorem index_mut_slice_from (a : Array α) (n : Int) :
    runtimeBuiltins base "index_mut" [enc a, rangeVal n none] =
      some (enc (Hax.slice_from a n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_slice_from a n)

theorem index_slice_range (a : Array α) (lo hi : Int) :
    runtimeBuiltins base "index" [enc a, rangeVal lo (some hi)] =
      some (enc (Hax.slice_range a lo hi)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_slice_range a lo hi)

theorem index_mut_slice_range (a : Array α) (lo hi : Int) :
    runtimeBuiltins base "index_mut" [enc a, rangeVal lo (some hi)] =
      some (enc (Hax.slice_range a lo hi)) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_slice_range a lo hi)

theorem index_full (a : Array α) :
    runtimeBuiltins base "index" [enc a, rangeVal 0 none] = some (enc a) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_full a)

theorem index_mut_full (a : Array α) :
    runtimeBuiltins base "index_mut" [enc a, rangeVal 0 none] = some (enc a) :=
  (runtimeBuiltins_of_lookup rfl).trans (indexLeaf_full a)

theorem RangeTo_int (n : Int) :
    runtimeBuiltins base "RangeTo" [.int n] = some (rangeVal 0 (some n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (rangeToLeaf_int n)

theorem RangeFrom_int (n : Int) :
    runtimeBuiltins base "RangeFrom" [.int n] = some (rangeVal n none) :=
  (runtimeBuiltins_of_lookup rfl).trans (rangeFromLeaf_int n)

theorem Range_int (lo hi : Int) :
    runtimeBuiltins base "Range" [.int lo, .int hi] = some (rangeVal lo (some hi)) :=
  (runtimeBuiltins_of_lookup rfl).trans (rangeLeaf_int lo hi)

theorem RangeFull_nil : runtimeBuiltins base "RangeFull" [] = some (rangeVal 0 none) :=
  (runtimeBuiltins_of_lookup rfl).trans (constLeaf_nil _)

theorem collect_range (lo hi : Int) :
    runtimeBuiltins base "collect" [rangeVal lo (some hi)] =
      some (enc (Hax.range lo hi)) :=
  (runtimeBuiltins_of_lookup rfl).trans (iterLeaf_range lo hi)

theorem array_update_enc (a : Array α) (i : Int) (x : α) :
    runtimeBuiltins base "array_update" [enc a, .int i, enc x] =
      some (enc (Hax.array_update a i x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (arrayUpdateLeaf_enc a i x)

theorem array_update_int (a : Array Int) (i x : Int) :
    runtimeBuiltins base "array_update" [enc a, .int i, .int x] =
      some (enc (Hax.array_update a i x)) :=
  array_update_enc a i x

theorem repeat_enc (x : α) (n : Int) :
    runtimeBuiltins base "repeat" [enc x, .int n] = some (enc (Hax.repeat_ x n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (repeatLeaf_enc x n)

theorem repeat_int (x n : Int) :
    runtimeBuiltins base "repeat" [.int x, .int n] = some (enc (Hax.repeat_ x n)) :=
  repeat_enc x n

theorem from_elem_enc (x : α) (n : Int) :
    runtimeBuiltins base "from_elem" [enc x, .int n] = some (enc (Hax.from_elem x n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (repeatLeaf_from_elem x n)

theorem array_lit_enc (l : List α) :
    runtimeBuiltins base "array_lit" (l.map enc) = some (enc l.toArray) :=
  (runtimeBuiltins_of_lookup rfl).trans (arrayLitLeaf_enc l)

theorem len_enc (a : Array α) :
    runtimeBuiltins base "len" [enc a] = some (.int (Hax.array_len a)) :=
  (runtimeBuiltins_of_lookup rfl).trans (lenLeaf_enc a)

theorem push_enc (a : Array α) (x : α) :
    runtimeBuiltins base "push" [enc a, enc x] = some (enc (Hax.push a x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (pushLeaf_enc a x)

theorem slice_reverse_enc (a : Array α) :
    runtimeBuiltins base "slice_reverse" [enc a] = some (enc (Hax.slice_reverse a)) :=
  (runtimeBuiltins_of_lookup rfl).trans (reverseLeaf_enc a)

theorem vec_remove_enc [Inhabited α] (a : Array α) (i : Int) (h0 : 0 ≤ i)
    (h : i < Hax.array_len a) :
    runtimeBuiltins base "vec_remove" [enc a, .int i] = some (enc (Hax.vec_remove a i)) :=
  (runtimeBuiltins_of_lookup rfl).trans (vecRemoveLeaf_enc a i h0 h)

theorem new_nil : runtimeBuiltins base "new" [] = some (enc (#[] : Array α)) :=
  (runtimeBuiltins_of_lookup rfl).trans emptyLeaf_new

/-- `new []` at `Array Int`, the form whose right side is determined by the left. -/
theorem new_nil_int : runtimeBuiltins base "new" [] = some (enc (#[] : Array Int)) :=
  new_nil

theorem with_capacity_enc (n : Int) :
    runtimeBuiltins base "with_capacity" [.int n] =
      some (enc (Hax.with_capacity (α := α) n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (emptyLeaf_with_capacity n)

/-- `with_capacity` at `Array Int`, the form whose right side is determined by the
    left. -/
theorem with_capacity_int (n : Int) :
    runtimeBuiltins base "with_capacity" [.int n] =
      some (enc (Hax.with_capacity (α := Int) n)) :=
  with_capacity_enc n

theorem extend_from_slice_enc (a b : Array α) :
    runtimeBuiltins base "extend_from_slice" [enc a, enc b] =
      some (enc (Hax.extend_from_slice a b)) :=
  (runtimeBuiltins_of_lookup rfl).trans (extendLeaf_enc a b)

theorem copy_from_slice_enc (a b : Array α) :
    runtimeBuiltins base "copy_from_slice" [enc a, enc b] =
      some (enc (Hax.copy_from_slice a b)) :=
  (runtimeBuiltins_of_lookup rfl).trans (copyLeaf_enc a b)

theorem slice_update_enc (a : Array α) (lo hi : Int) (src : Array α) :
    runtimeBuiltins base "slice_update" [enc a, .int lo, .int hi, enc src] =
      some (enc (Hax.slice_update a lo hi src)) :=
  (runtimeBuiltins_of_lookup rfl).trans (sliceUpdateLeaf_enc a lo hi src)

theorem deref_enc (x : α) :
    runtimeBuiltins base "deref" [enc x] = some (enc (Hax.deref x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (identLeaf_deref x)

theorem to_vec_enc (x : α) :
    runtimeBuiltins base "to_vec" [enc x] = some (enc (Hax.to_vec x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (identLeaf_to_vec x)

theorem clone_enc (x : α) :
    runtimeBuiltins base "clone" [enc x] = some (enc (Hax.clone x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (identLeaf_clone x)

theorem into_vec_enc (x : α) :
    runtimeBuiltins base "into_vec" [enc x] = some (enc (Hax.into_vec x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (identLeaf_into_vec x)

theorem into_iter_enc (a : Array α) :
    runtimeBuiltins base "into_iter" [enc a] = some (enc (Hax.into_iter a)) :=
  (runtimeBuiltins_of_lookup rfl).trans (iterLeaf_into_iter a)

theorem iter_enc (a : Array α) :
    runtimeBuiltins base "iter" [enc a] = some (enc (Hax.iter a)) :=
  (runtimeBuiltins_of_lookup rfl).trans (iterLeaf_enc a)

theorem collect_enc (a : Array α) :
    runtimeBuiltins base "collect" [enc a] = some (enc (Hax.collect a)) :=
  (runtimeBuiltins_of_lookup rfl).trans (iterLeaf_enc a)

theorem truncate_enc (a : Array α) (n : Int) :
    runtimeBuiltins base "truncate" [enc a, .int n] = some (enc (Hax.truncate a n)) :=
  (runtimeBuiltins_of_lookup rfl).trans (truncateLeaf_enc a n)

theorem is_empty_enc (a : Array α) :
    runtimeBuiltins base "is_empty" [enc a] = some (.bool (Hax.is_empty a)) :=
  (runtimeBuiltins_of_lookup rfl).trans (isEmptyLeaf_enc a)

theorem Some_enc (x : α) :
    runtimeBuiltins base "Some" [enc x] = some (enc (some x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (someLeaf_enc x)

theorem None_nil : runtimeBuiltins base "None" [] = some (enc (none : Option α)) :=
  (runtimeBuiltins_of_lookup rfl).trans constLeaf_none

theorem panic_unit (vs : List Value) : runtimeBuiltins base "panic" vs = some .unit :=
  (runtimeBuiltins_of_lookup rfl).trans (unitLeaf_apply vs)

/-- A string literal of the extraction (`str_opaque`, printed `Hax.literal`): the unit
    value, which is the encoding of every string. -/
theorem str_opaque_nil :
    runtimeBuiltins base "str_opaque" [] = some (enc (Hax.literal : String)) :=
  (runtimeBuiltins_of_lookup rfl).trans (unitLeaf_apply [])

end Arrays

section Scalars

theorem Add_int (x y : Int) :
    runtimeBuiltins base "Add" [.int x, .int y] = some (.int (Hax.add x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem Add_arr (a b : Array Int) :
    runtimeBuiltins base "Add" [enc a, enc b] = some (enc (Hax.add a b)) := by
  rw [runtimeBuiltins_of_lookup rfl, intArrLeaf2,
    Leaf.orElse_of_none (leaf2_int_none _ _ fun _ h => Value.noConfusion h)]
  exact leaf2_apply _ a b

theorem Sub_int (x y : Int) :
    runtimeBuiltins base "Sub" [.int x, .int y] = some (.int (Hax.sub x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem Mul_int (x y : Int) :
    runtimeBuiltins base "Mul" [.int x, .int y] = some (.int (Hax.mul x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem Div_int (x y : Int) :
    runtimeBuiltins base "Div" [.int x, .int y] = some (.int (Hax.div x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem Rem_int (x y : Int) :
    runtimeBuiltins base "Rem" [.int x, .int y] = some (.int (Hax.rem x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem Lt_int (x y : Int) :
    runtimeBuiltins base "Lt" [.int x, .int y] = some (.bool (Hax.lt x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem Le_int (x y : Int) :
    runtimeBuiltins base "Le" [.int x, .int y] = some (.bool (Hax.le x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem Gt_int (x y : Int) :
    runtimeBuiltins base "Gt" [.int x, .int y] = some (.bool (Hax.gt x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem Ge_int (x y : Int) :
    runtimeBuiltins base "Ge" [.int x, .int y] = some (.bool (Hax.ge x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem Eq_int (x y : Int) :
    runtimeBuiltins base "Eq" [.int x, .int y] = some (.bool (Hax.beq x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem eq_int (x y : Int) :
    runtimeBuiltins base "eq" [.int x, .int y] = some (.bool (Hax.beq x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem Ne_int (x y : Int) :
    runtimeBuiltins base "Ne" [.int x, .int y] = some (.bool (Hax.bne x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf2_apply _ x y))

theorem Eq_bool (x y : Bool) :
    runtimeBuiltins base "Eq" [.bool x, .bool y] = some (.bool (Hax.beq x y)) := by
  rw [runtimeBuiltins_of_lookup rfl, eqLeaf,
    Leaf.orElse_of_none (leaf2_int_none _ _ fun _ h => Value.noConfusion h)]
  exact Leaf.orElse_of_some (leaf2_apply _ x y)

theorem Ne_bool (x y : Bool) :
    runtimeBuiltins base "Ne" [.bool x, .bool y] = some (.bool (Hax.bne x y)) := by
  rw [runtimeBuiltins_of_lookup rfl, eqLeaf,
    Leaf.orElse_of_none (leaf2_int_none _ _ fun _ h => Value.noConfusion h)]
  exact Leaf.orElse_of_some (leaf2_apply _ x y)

theorem Eq_arr (a b : Array Int) :
    runtimeBuiltins base "Eq" [enc a, enc b] = some (.bool (Hax.beq a b)) := by
  rw [runtimeBuiltins_of_lookup rfl, eqLeaf,
    Leaf.orElse_of_none (leaf2_int_none _ _ fun _ h => Value.noConfusion h),
    Leaf.orElse_of_none (leaf2_bool_none _ _ fun _ h => Value.noConfusion h)]
  exact leaf2_apply _ a b

theorem Ne_arr (a b : Array Int) :
    runtimeBuiltins base "Ne" [enc a, enc b] = some (.bool (Hax.bne a b)) := by
  rw [runtimeBuiltins_of_lookup rfl, eqLeaf,
    Leaf.orElse_of_none (leaf2_int_none _ _ fun _ h => Value.noConfusion h),
    Leaf.orElse_of_none (leaf2_bool_none _ _ fun _ h => Value.noConfusion h)]
  exact leaf2_apply _ a b

theorem and_bool (x y : Bool) :
    runtimeBuiltins base "&&" [.bool x, .bool y] = some (.bool (Hax.band x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem or_bool (x y : Bool) :
    runtimeBuiltins base "||" [.bool x, .bool y] = some (.bool (Hax.bor x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem Not_bool (x : Bool) :
    runtimeBuiltins base "Not" [.bool x] = some (.bool (Hax.Not x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (Leaf.orElse_of_some (leaf1_apply _ x))

theorem Not_int (x : Int) :
    runtimeBuiltins base "Not" [.int x] = some (.int (Hax.Not x)) := by
  rw [runtimeBuiltins_of_lookup rfl, notLeaf,
    Leaf.orElse_of_none (leaf1_bool_none _ fun _ h => Value.noConfusion h)]
  exact leaf1_apply _ x

theorem BitXor_int (x y : Int) :
    runtimeBuiltins base "BitXor" [.int x, .int y] = some (.int (Hax.bitxor x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem BitAnd_int (x y : Int) :
    runtimeBuiltins base "BitAnd" [.int x, .int y] = some (.int (Hax.bitand x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem BitOr_int (x y : Int) :
    runtimeBuiltins base "BitOr" [.int x, .int y] = some (.int (Hax.bitor x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem Shl_int (x y : Int) :
    runtimeBuiltins base "Shl" [.int x, .int y] = some (.int (Hax.shl x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem Shr_int (x y : Int) :
    runtimeBuiltins base "Shr" [.int x, .int y] = some (.int (Hax.shr x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem wrapping_add_int (x y : Int) :
    runtimeBuiltins base "wrapping_add" [.int x, .int y] =
      some (.int (Hax.wrapping_add x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem wrapping_mul_int (x y : Int) :
    runtimeBuiltins base "wrapping_mul" [.int x, .int y] =
      some (.int (Hax.wrapping_mul x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem rotate_right_int (x y : Int) :
    runtimeBuiltins base "rotate_right" [.int x, .int y] =
      some (.int (Hax.rotate_right x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem cast_int (x : Int) :
    runtimeBuiltins base "cast" [.int x] = some (.int (Hax.castVal x)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf1_apply _ x)

theorem min_int (x y : Int) :
    runtimeBuiltins base "min" [.int x, .int y] = some (.int (min x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

theorem max_int (x y : Int) :
    runtimeBuiltins base "max" [.int x, .int y] = some (.int (max x y)) :=
  (runtimeBuiltins_of_lookup rfl).trans (leaf2_apply _ x y)

end Scalars

/-! ### Width families -/

section Tagged

variable {f op : String} {w : Nat}

/-- `cast#w`, for a name that parses as the family `cast` at width `w`. -/
theorem cast_w (h₁ : runtimeTable.lookup f = none) (h₂ : parseTag f = some ("cast", w))
    (x : Int) :
    runtimeBuiltins base f [.int x] = some (.int (Hax.castVal_w w x)) :=
  (runtimeBuiltins_of_tag h₁ h₂ rfl).trans (leaf1_apply _ x)

/-- A binary integer family at width `w`. -/
theorem tagged2 {g : Nat → Int → Int → Int}
    (h₁ : runtimeTable.lookup f = none) (h₂ : parseTag f = some (op, w))
    (h₃ : widthTable.lookup op = some fun w => leaf2 (g w)) (x y : Int) :
    runtimeBuiltins base f [.int x, .int y] = some (.int (g w x y)) :=
  (runtimeBuiltins_of_tag h₁ h₂ h₃).trans (leaf2_apply _ x y)

/-- A unary integer family at width `w`. -/
theorem tagged1 {g : Nat → Int → Int}
    (h₁ : runtimeTable.lookup f = none) (h₂ : parseTag f = some (op, w))
    (h₃ : widthTable.lookup op = some fun w => leaf1 (g w)) (x : Int) :
    runtimeBuiltins base f [.int x] = some (.int (g w x)) :=
  (runtimeBuiltins_of_tag h₁ h₂ h₃).trans (leaf1_apply _ x)

end Tagged

theorem cast8 (x : Int) :
    runtimeBuiltins base "cast#8" [.int x] = some (.int (Hax.castVal_w 8 x)) :=
  cast_w rfl (by decide) x

theorem BitXor32 (x y : Int) :
    runtimeBuiltins base "BitXor#32" [.int x, .int y] =
      some (.int (Hax.bitxor_w 32 x y)) :=
  tagged2 (op := "BitXor") rfl (by decide) rfl x y

theorem wrapping_add64 (x y : Int) :
    runtimeBuiltins base "wrapping_add#64" [.int x, .int y] =
      some (.int (Hax.wrapping_add_w 64 x y)) :=
  tagged2 (op := "wrapping_add") rfl (by decide) rfl x y

theorem Not64 (x : Int) :
    runtimeBuiltins base "Not#64" [.int x] = some (.int (Hax.bitnot_w 64 x)) :=
  tagged1 (op := "Not") rfl (by decide) rfl x

theorem to_be_bytes64 (x : Int) :
    runtimeBuiltins base "to_be_bytes#64" [.int x] = some (enc (Hax.to_be_bytes_w 64 x)) :=
  (runtimeBuiltins_of_tag (op := "to_be_bytes") rfl (by decide) rfl).trans
    (leaf1_apply _ x)

end RuntimeOps

end Hax.Ascent
