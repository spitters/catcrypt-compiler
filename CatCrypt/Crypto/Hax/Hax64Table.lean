/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Hax.HaxCallNames
public import HaxLean.Phase.InlineMapClosure

/-!
# The `u64` tables `hax64Exit` and `hax64WExit`

`hax64Exit` is `Hax.hax64Builtins` restricted to the array operations and the scalar calls
on words; `hax64WExit` extends it by array literals, `repeat`, the array comparisons and the
wide field heads. The structured translation `ImpToNF.impToNF` is sound for a table of
builtins under the call typing it translates with (`ImpToNF.TypedCalls`), and for `repeat`
it needs the table to answer as `Hax.hax64Builtins` does (`ImpToNF.RepeatCalls`). This
module defines both tables and proves both facts for `hax64WExit` at the call typing
`ImpToNF.hax64SigOf`.

## Main definitions

* `hax64ArrShape`, `hax64ScalarAdmit`, `hax64Exit` — the admitted `u64` table
* `hax64LitAdmit`, `hax64RepAdmit`, `hax64EqArrAdmit`, `hax64WideHead`, `hax64WExit` — the
  `u64` table with array constructors

## Main results

* `hax64Exit_some`, `hax64Exit_sub`, `hax64Exit_none`, `arrayOps_hax64Exit` — the values of
  `hax64Exit`
* `hax64WExit_of_ne`, `hax64WExit_wide`, `hax64WExit_sub`, `hax64WExit_none`,
  `arrayOps_hax64WExit` — the values of `hax64WExit`
* `hax64WExit_typedCalls` — the call typing `hax64SigOf` is sound for `hax64WExit`
* `repeatCalls_hax64WExit` — `hax64WExit` satisfies `RepeatCalls`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (Value Builtins hax64Builtins)
open _root_.Hax.InlineMap (ArrayOps)

/-! ## The admitted table -/

/-- A two-operand scalar operation of `scalarOpExprT`: a comparison, `add`, `sub`, a Boolean
    connective or a width-tagged word operation. -/
def hax64ScalarOp (f : String) : Bool := (scalarOpExprT f (.SVar "a") (.SVar "b")).isSome

/-- Every value is an integer word. -/
def hax64IntArgs (vals : List Value) : Bool :=
  vals.all fun v => match v with
    | .int n => decide (0 ≤ n) && decide (n < 2 ^ 64)
    | _ => false

/-- The argument shape of an admitted scalar call: two scalar words for an operation of
    `hax64ScalarOp` (integers or Booleans), one Boolean for `Not`, integer words for any
    other call. -/
def hax64ArgsShape (f : String) (vals : List Value) : Bool :=
  if hax64ScalarOp f then vals.length == 2 && vals.all scalarValNB
  else if f = "Not" then (match vals with | [.bool _] => true | _ => false)
  else hax64IntArgs vals

/-- The argument shapes of the array operations: `len` on an array, `index` on an array and
    an unsigned or non-negative integer index, `array_update` on an array, an unsigned or
    non-negative integer index and a value. -/
def hax64ArrShape (f : String) (vals : List Value) : Bool :=
  match f, vals with
  | "len", [.array _] => true
  | "index", [.array _, .uint _ _] => true
  | "index", [.array _, .int i] => decide (0 ≤ i)
  | "array_update", [.array _, .uint _ _, _] => true
  | "array_update", [.array _, .int i, _] => decide (0 ≤ i)
  | _, _ => false

/-- A call of `exitScalarRes` other than `len` on words, at a call tower type holding a
    word, with a scalar word as result. -/
def hax64ScalarAdmit (f : String) (vals : List Value) (r : Value) : Bool :=
  exitScalarRes f && f != "len" && hax64ArgsShape f vals &&
    exitMarshalOk (towerOfCallName f) && scalarValNB r

/-- **The admitted `u64` table.**  `Hax.hax64Builtins` on the array operations of
    `hax64ArrShape` and the scalar calls of `hax64ScalarAdmit`, refusing every other call and
    every control-flow result. -/
def hax64Exit : Builtins := fun f vals =>
  match hax64Builtins f vals with
  | some r =>
      if !r.isControlFlow && (hax64ArrShape f vals || hax64ScalarAdmit f vals r) then some r
      else none
  | none => none

/-- A value `r` of `hax64Exit` at `f` on `vals` is the value of `Hax.hax64Builtins`, is no
    control-flow value, and either the call has the array shape (`hax64ArrShape`) or it is
    admitted as a scalar call (`hax64ScalarAdmit`). -/
theorem hax64Exit_some {f : String} {vals : List Value} {r : Value}
    (h : hax64Exit f vals = some r) :
    hax64Builtins f vals = some r ∧ r.isControlFlow = false ∧
      (hax64ArrShape f vals = true ∨ hax64ScalarAdmit f vals r = true) := by
  unfold hax64Exit at h
  rcases hb : hax64Builtins f vals with _ | r'
  · rw [hb] at h
    cases h
  · rw [hb] at h
    simp only at h
    split_ifs at h with hc
    cases h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at hc
    exact ⟨rfl, hc⟩

/-- `hax64Exit` is a sub-table of `Hax.hax64Builtins`. -/
theorem hax64Exit_sub {f : String} {vals : List Value} {r : Value}
    (h : hax64Exit f vals = some r) : hax64Builtins f vals = some r :=
  (hax64Exit_some h).1

theorem hax64Exit_of_arrShape {f : String} {vals : List Value} {r : Value}
    (hb : hax64Builtins f vals = some r) (hc : r.isControlFlow = false)
    (hs : hax64ArrShape f vals = true) : hax64Exit f vals = some r := by
  unfold hax64Exit
  rw [hb]
  simp [hc, hs]

/-- A value of `Hax.hax64Builtins` that is no control-flow value and is admitted by
    `hax64ScalarAdmit` is the value of `hax64Exit`. -/
theorem hax64Exit_of_scalarAdmit {f : String} {vals : List Value} {r : Value}
    (hb : hax64Builtins f vals = some r) (hc : r.isControlFlow = false)
    (hs : hax64ScalarAdmit f vals r = true) : hax64Exit f vals = some r := by
  unfold hax64Exit
  rw [hb]
  simp [hc, hs]

/-- `hax64Exit` answers `len`, `index` at an integer and `array_update` at an integer on an
    array as `ArrayOps` requires. -/
theorem arrayOps_hax64Exit : ArrayOps hax64Exit where
  len vs := .inl (hax64Exit_of_arrShape (_root_.Hax.hax64Builtins_arrayLen vs) rfl rfl)
  index vs j h hcf := by
    refine hax64Exit_of_arrShape ?_ hcf (by simp [hax64ArrShape])
    rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_index _ _),
      _root_.Hax.widthArrayOps_index_int]
    simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast, List.getElem?_eq_getElem h,
      Option.bind_some]
    revert hcf
    cases vs[j] <;> simp [Value.isControlFlow]
  update vs j v h := by
    refine hax64Exit_of_arrShape ?_ rfl (by simp [hax64ArrShape])
    rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_array_update _ _ _),
      _root_.Hax.widthArrayOps_array_update_int]
    simp [h]

theorem hax64ArrShape_name {f : String} {vals : List Value} (h : hax64ArrShape f vals = true) :
    f = "len" ∨ f = "index" ∨ f = "array_update" := by
  unfold hax64ArrShape at h
  split at h <;> simp_all

theorem exitScalarRes_len : exitScalarRes "len" = true := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls, exitTowerScalarCall]

/-- The table refuses every call outside `exitScalarRes` other than `index` and
    `array_update`. -/
theorem hax64Exit_none {f : String} (hf : exitScalarRes f = false) (h1 : f ≠ "index")
    (h2 : f ≠ "array_update") (vals : List Value) : hax64Exit f vals = none := by
  rcases h : hax64Exit f vals with _ | r
  · rfl
  · exfalso
    rcases (hax64Exit_some h).2.2 with hs | hs
    · rcases hax64ArrShape_name hs with rfl | rfl | rfl
      · rw [exitScalarRes_len] at hf
        cases hf
      · exact h1 rfl
      · exact h2 rfl
    · simp only [hax64ScalarAdmit, hf, Bool.false_and] at hs
      cases hs

theorem hax64Builtins_index_int {vs : List Value} {i : Int} {vRes : Value} (hi : 0 ≤ i)
    (hb : hax64Builtins "index" [.array vs, .int i] = some vRes) :
    ∃ h : i.toNat < vs.length, vRes = vs[i.toNat] := by
  rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_index _ _),
    _root_.Hax.widthArrayOps_index_int, ite_eq_left hi] at hb
  simp only [Option.bind_eq_some_iff] at hb
  obtain ⟨x, hx, hxv⟩ := hb
  rw [List.getElem?_eq_some_iff] at hx
  obtain ⟨hk, rfl⟩ := hx
  refine ⟨hk, ?_⟩
  split at hxv
  · cases hxv
  · cases hxv
    rfl

/-- **The admission facts of a narrow field head**: a head that is the name of a field method
    followed by `#p` has a scalar result, is no array constructor, has a call tower type that
    holds a word, and is no two-operand scalar operation (the first `#` of every name of
    `scalarOpExprT` is followed by a tag other than `p`, `widthOpOf_spec`). -/
theorem admit_of_fieldPrefix {f : String} {m : _root_.Hax.FieldTag.FieldMethod}
    {ds : List Char} (hf : f.toList = m.nameChars ++ '#' :: 'p' :: ds) :
    exitScalarRes f = true ∧ arrCtorLen f = none ∧
      exitMarshalOk (towerOfCallName f) = true ∧ hax64ScalarOp f = false := by
  have hpre : '#' ∉ m.nameChars := by cases m <;> decide
  have hdrop : ∀ (pre rest : List Char), '#' ∉ pre →
      ((pre ++ '#' :: rest).dropWhile (· != '#')).take 2 = ('#' :: rest).take 2 :=
    fun pre rest h => by
      rw [List.dropWhile_append_of_pos (fun a ha => by
        simp only [bne_iff_ne, ne_eq]; rintro rfl; exact h ha)]
      simp
  have K : (f.toList.dropWhile (· != '#')).take 2 = ['#', 'p'] := by
    rw [hf, hdrop _ _ hpre]
    simp
  have ha : arrCtorLen f = none := by
    simp only [arrCtorLen, hf]
    cases m <;> rfl
  have hw : widthOpOf f = none := by
    cases h : widthOpOf f with
    | none => rfl
    | some r =>
      obtain ⟨op, hop, tag, htag, rfl⟩ := widthOpOf_spec h
      have h1 : '#' ∉ op.toList := by clear h hf K ha htag; revert op; decide
      have h2 : tag.toList.take 1 ≠ ['p'] := by clear h hf K ha hop; revert tag; decide
      rw [String.toList_append, String.toList_append, List.append_assoc] at K
      rw [show ("#" : String).toList = ['#'] from rfl, List.singleton_append,
        hdrop _ _ h1] at K
      exact absurd (by simpa using K) h2
  refine ⟨?_, ha, exitMarshalOk_of_arrCtorLen ha, ?_⟩
  · have hm : '#' ∈ f.toList := by rw [hf]; simp
    simp only [exitScalarRes, exitScalarCall, String.contains_char_eq, hm, decide_true,
      Bool.or_true, Bool.true_or]
  · unfold hax64ScalarOp scalarOpExprT
    split <;> first | (revert K; decide) | simp [hw]

/-! ## The table with array constructors -/

/-- A non-empty array value. -/
def nonemptyArrayB : Value → Bool
  | .array (_ :: _) => true
  | _ => false

/-- The array literals the table admits: fewer than `2^64` values that are all scalar
    words or all non-empty arrays. -/
def hax64LitAdmit (vals : List Value) : Bool :=
  (vals.all scalarValNB || vals.all nonemptyArrayB) && decide (vals.length < 2 ^ 64)

/-- The array constructions `repeat(v, c)` the table admits: a scalar word `v` and a count
    decoding to a number below `2^64`. -/
def hax64RepAdmit (vals : List Value) : Bool :=
  match vals with
  | [vv, vc] => scalarValNB vv && match valueToScalar vc with
      | some k => decide (k < 2 ^ 64)
      | none => false
  | _ => false

/-- The array comparisons `eq#arr`, `ne#arr` the table admits: two arrays of integer words
    (`Hax.hax64IntWordB`). -/
def hax64EqArrAdmit (vals : List Value) : Bool :=
  match vals with
  | [.array a, .array b] => a.all _root_.Hax.hax64IntWordB && b.all _root_.Hax.hax64IntWordB
  | _ => false

/-- A wide field head: a tagged field head `m#p` (`Hax.FieldTag.fieldTag?`) at a modulus
    `p ≥ 2^64`, whose operands and result `Hax.FieldTag.fieldCall` holds as arrays of
    `Hax.FieldTag.fieldLimbs p` limbs. -/
def hax64WideHead (f : String) : Prop :=
  ∃ m p, _root_.Hax.FieldTag.fieldTag? f = some (m, p) ∧ 2 ^ 64 ≤ p

instance (f : String) : Decidable (hax64WideHead f) :=
  decidable_of_iff
    (((_root_.Hax.FieldTag.fieldTag? f).any fun mp => decide (2 ^ 64 ≤ mp.2)) = true) (by
      unfold hax64WideHead
      rcases ht : _root_.Hax.FieldTag.fieldTag? f with _ | ⟨m, p⟩
      · simp
      · simp only [Option.any_some, decide_eq_true_eq, Option.some.injEq, Prod.mk.injEq]
        exact ⟨fun h => ⟨m, p, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨_, rfl⟩, h⟩ => h⟩)

/-- A tagged field head at a modulus below `2^64` is no wide field head. -/
theorem not_hax64WideHead_of_lt {f : String} {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat}
    (ht : _root_.Hax.FieldTag.fieldTag? f = some (m, p)) (hp : p < 2 ^ 64) :
    ¬ hax64WideHead f := by
  rintro ⟨m', p', ht', hl⟩
  rw [ht] at ht'
  cases ht'
  omega

/-- **The `u64` table at a wide field head**: a value of `Hax.hax64Builtins` at a wide field
    head is the array of the limbs of a number, on an argument list whose first value is an
    array. -/
theorem hax64Builtins_wideHead {f : String} (hw : hax64WideHead f) {vals : List Value}
    {r : Value} (h : hax64Builtins f vals = some r) :
    (∃ xs rest, vals = .array xs :: rest) ∧ ∃ ys, r = .array ys := by
  obtain ⟨m, p, ht, hp⟩ := hw
  have hc := _root_.Hax.hax64Builtins_of_fieldTag? ht h
  refine ⟨?_, ?_⟩
  · unfold _root_.Hax.FieldTag.fieldCall at hc
    split at hc
    · split_ifs at hc with hc'
      omega
    · split_ifs at hc with hc'
      omega
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
    · cases hc
  · rcases _root_.Hax.FieldTag.fieldCall_some hc with ⟨n, -, -, hp'⟩ | ⟨-, n, rfl, -⟩
    · omega
    · exact ⟨_, rfl⟩

/-- A wide field head has no value of `Hax.hax64Builtins` on an argument list whose first
    value is a scalar. -/
theorem hax64Builtins_wideHead_scalar {f : String} (hw : hax64WideHead f) {v : Value}
    {rest : List Value} (hv : ScalarValN v) {r : Value} :
    hax64Builtins f (v :: rest) ≠ some r := by
  intro h
  obtain ⟨⟨xs, rest', he⟩, -⟩ := hax64Builtins_wideHead hw h
  cases he
  exact hv.elim

/-- **The `u64` table with array constructors.**  `hax64Exit`, `array_lit` on the argument
    lists of `hax64LitAdmit`, `repeat` of `Hax.hax64Builtins` on the argument lists of
    `hax64RepAdmit`, the array comparisons `eq#arr`, `ne#arr` of `Hax.hax64Builtins` on
    the argument lists of `hax64EqArrAdmit`, and the wide field heads (`hax64WideHead`) of
    `Hax.hax64Builtins`. -/
def hax64WExit : Builtins := fun f vals =>
  if f = "array_lit" then (if hax64LitAdmit vals then some (.array vals) else none)
  else if f = "repeat" then (if hax64RepAdmit vals then hax64Builtins "repeat" vals else none)
  else if f = "eq#arr" ∨ f = "ne#arr" then
    (if hax64EqArrAdmit vals then hax64Builtins f vals else none)
  else if hax64WideHead f then hax64Builtins f vals
  else hax64Exit f vals

theorem hax64WExit_of_ne {f : String} (h : f ≠ "array_lit") (h' : f ≠ "repeat")
    (he : f ≠ "eq#arr") (hn : f ≠ "ne#arr") (hw : ¬ hax64WideHead f := by decide)
    (vals : List Value) :
    hax64WExit f vals = hax64Exit f vals := by
  simp only [hax64WExit, h, h', he, hn, hw, or_self, ite_false]

/-- At a wide field head `hax64WExit` is `Hax.hax64Builtins`. -/
theorem hax64WExit_wide {f : String} (hw : hax64WideHead f) (vals : List Value) :
    hax64WExit f vals = hax64Builtins f vals := by
  have hne : ∀ s : String, ¬ hax64WideHead s → f ≠ s := by
    rintro s hs rfl
    exact hs hw
  have h1 := hne "array_lit" (by decide)
  have h2 := hne "repeat" (by decide)
  have h3 := hne "eq#arr" (by decide)
  have h4 := hne "ne#arr" (by decide)
  simp only [hax64WExit, h1, h2, h3, h4, or_self, ite_false, ite_eq_left hw]

/-- A value of `hax64WExit` at `eq#arr` or `ne#arr` is the value of `Hax.hax64Builtins` on two
    arrays of integer words. -/
theorem hax64WExit_eqArr {f : String} (hf : f = "eq#arr" ∨ f = "ne#arr") {vals : List Value}
    {r : Value} (h : hax64WExit f vals = some r) :
    ∃ a b, vals = [.array a, .array b] ∧ a.all _root_.Hax.hax64IntWordB = true ∧
      b.all _root_.Hax.hax64IntWordB = true ∧ hax64Builtins f vals = some r := by
  have h1 : f ≠ "array_lit" := by rcases hf with rfl | rfl <;> decide
  have h2 : f ≠ "repeat" := by rcases hf with rfl | rfl <;> decide
  simp only [hax64WExit, h1, h2, hf, ite_false, ite_true] at h
  by_cases hadm : hax64EqArrAdmit vals = true
  · rw [ite_eq_left hadm] at h
    unfold hax64EqArrAdmit at hadm
    split at hadm
    · rename_i a b
      simp only [Bool.and_eq_true] at hadm
      exact ⟨a, b, rfl, hadm.1, hadm.2, h⟩
    · cases hadm
  · rw [ite_eq_right hadm] at h
    cases h

theorem hax64WExit_repeat {vals : List Value} {r : Value}
    (h : hax64WExit "repeat" vals = some r) :
    ∃ vv vc k, vals = [vv, vc] ∧ ScalarValN vv ∧ valueToScalar vc = some k ∧ k < 2 ^ 64 ∧
      hax64Builtins "repeat" vals = some r := by
  simp only [hax64WExit, show ("repeat" : String) ≠ "array_lit" by decide, ite_false,
    ite_true] at h
  split_ifs at h with ha
  unfold hax64RepAdmit at ha
  split at ha
  · rename_i vv vc
    simp only [Bool.and_eq_true] at ha
    obtain ⟨hv, hk⟩ := ha
    split at hk
    · rename_i k hk'
      exact ⟨vv, vc, k, rfl, (scalarValNB_iff vv).mp hv, hk', of_decide_eq_true hk, h⟩
    · cases hk
  · cases ha

theorem hax64WExit_arrayLit {vals : List Value} {r : Value}
    (h : hax64WExit "array_lit" vals = some r) :
    hax64LitAdmit vals = true ∧ r = .array vals := by
  simp only [hax64WExit, ite_true] at h
  split_ifs at h with ha
  cases h
  exact ⟨ha, rfl⟩

/-- `hax64WExit` is a sub-table of `Hax.hax64Builtins`. -/
theorem hax64WExit_sub {f : String} {vals : List Value} {r : Value}
    (h : hax64WExit f vals = some r) : hax64Builtins f vals = some r := by
  by_cases hf : f = "array_lit"
  · subst hf
    obtain ⟨-, rfl⟩ := hax64WExit_arrayLit h
    rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_arrayLit vals)]
    rfl
  · by_cases hr : f = "repeat"
    · subst hr
      obtain ⟨-, -, -, -, -, -, -, hb⟩ := hax64WExit_repeat h
      exact hb
    · by_cases he : f = "eq#arr" ∨ f = "ne#arr"
      · obtain ⟨-, -, -, -, -, hb⟩ := hax64WExit_eqArr he h
        exact hb
      · rw [not_or] at he
        by_cases hw : hax64WideHead f
        · rwa [hax64WExit_wide hw] at h
        rw [hax64WExit_of_ne hf hr he.1 he.2 hw] at h
        exact hax64Exit_sub h

theorem exitScalarRes_eqArr : exitScalarRes "eq#arr" = true := by
  first
    | decide
    | simp [exitScalarRes, exitScalarCall]

theorem exitScalarRes_neArr : exitScalarRes "ne#arr" = true := by
  first
    | decide
    | simp [exitScalarRes, exitScalarCall]

theorem hax64WExit_none {f : String} (hf : exitScalarRes f = false) (h1 : f ≠ "index")
    (h2 : f ≠ "array_update") (h3 : f ≠ "array_lit") (h4 : f ≠ "repeat") (vals : List Value) :
    hax64WExit f vals = none := by
  have h5 : f ≠ "eq#arr" := by rintro rfl; rw [exitScalarRes_eqArr] at hf; cases hf
  have h6 : f ≠ "ne#arr" := by rintro rfl; rw [exitScalarRes_neArr] at hf; cases hf
  have hw : ¬ hax64WideHead f := by
    rintro ⟨m, p, ht, -⟩
    have hm := _root_.Hax.FieldTag.mem_toList_of_fieldTag? ht
    simp only [exitScalarRes, exitScalarCall, Bool.or_eq_false_iff] at hf
    have hh := hf.1.2
    simp [String.contains_char_eq, hm] at hh
  rw [hax64WExit_of_ne h3 h4 h5 h6 hw]
  exact hax64Exit_none hf h1 h2 vals

theorem arrayOps_hax64WExit : ArrayOps hax64WExit where
  len vs := by
    rw [hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
    exact arrayOps_hax64Exit.len vs
  index vs j h hcf := by
    rw [hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
    exact arrayOps_hax64Exit.index vs j h hcf
  update vs j v h := by
    rw [hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
    exact arrayOps_hax64Exit.update vs j v h

/-! ## The call typing of `impToNF` -/

/-- The call typing `hax64SigOf` is sound for the `u64` table `hax64WExit`: a value of
    `hax64WExit` at a typed call is a value of `ImpToNF.hax64BuiltinsR`, since `hax64Exit`
    admits a scalar result only in the range of `scalarValNB`. -/
theorem hax64WExit_typedCalls : ImpToNF.TypedCalls hax64WExit ImpToNF.hax64SigOf :=
  ImpToNF.hax64Builtins_typedCalls.mono fun f as r hr vals v hv => by
    by_cases hw : hax64WideHead f
    · rw [hax64WExit_wide hw] at hv
      refine ImpToNF.hax64BuiltinsR_of hv fun hf => ?_
      subst hf
      exact absurd hw (by decide)
    by_cases hl : f = "array_lit"
    · subst hl
      unfold hax64WExit at hv
      rw [ite_eq_left rfl] at hv
      split at hv
      · cases hv
        exact ImpToNF.hax64BuiltinsR_of rfl fun hf => absurd hf (by decide)
      · cases hv
    have hn : f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" := by
      rcases ImpToNF.hax64SigOf_name hr with hm | rfl | rfl | rfl | rfl | rfl | ht
      · exact ImpToNF.hax64NFScalar_ne_arr hm
      · decide
      · decide
      · decide
      · exact absurd rfl hl
      · decide
      · obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp ht
        refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; cases hmp)
    rw [hax64WExit_of_ne hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 hw] at hv
    obtain ⟨hb, -, hadm⟩ := hax64Exit_some hv
    refine ImpToNF.hax64BuiltinsR_of hb fun hf => ?_
    subst hf
    rcases hadm with hs | hs
    · simp [hax64ArrShape] at hs
    · have hsv : scalarValNB v = true := by
        simp only [hax64ScalarAdmit, Bool.and_eq_true] at hs
        exact hs.2
      cases v <;> simp_all [scalarValNB, ImpToNF.wordRangeB]

/-- `hax64WExit` answers `repeat` as `Hax.hax64Builtins` does, on the argument lists it
    admits, so it satisfies `RepeatCalls`. -/
theorem repeatCalls_hax64WExit : ImpToNF.RepeatCalls hax64WExit := by
  intro x N v hN h
  unfold hax64WExit at h
  rw [ite_eq_right (by decide), ite_eq_left rfl] at h
  split at h
  · exact ImpToNF.repeatCalls_hax64Builtins x N v hN h
  · cases h

end CatCrypt.Crypto.Hax
