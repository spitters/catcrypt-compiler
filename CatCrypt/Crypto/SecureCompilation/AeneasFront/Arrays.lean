/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Scalars

/-!
# The array operations of Aeneas as ParamTransfer squares against `hax64WExit`

The array operations of the vendored Aeneas model (`HaxLean/Rust/Array.lean`) on arrays of
unsigned words are read as the calls `index`, `array_update`, `repeat` and `array_lit` of the
compiler's builtin table `hax64WExit`. An array encodes as the chain array of the encodings
of its entries (`arrV`), the encoding `ImpToNF.enc` gives to an array of words.

The squares are stated once for every element width `ty` and every length `n`, as in
`AeneasFront/Scalars.lean`: indexing, update and mutable indexing fail out of range and give
guarded squares (a value of the Aeneas operation is, encoded, the value of the table);
`repeat` never fails and gives a total square, registered as a `Related` instance.

## Main definitions

* `arrV`, `encA`: the encoding of an array and of an outcome of an array

## Main results

* `index_square`, `update_square`, `indexMut_square`, `hax64WExit_repeat_arrV`, `make_square`: the
  pointwise squares
* `index_related`, `update_related`: the guarded squares on outcomes
* `repeatRelated`: the total square of `repeat`, an instance
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std Transfer
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax

/-- The chain value of an Aeneas array of words: the array of the encodings of its
    entries. -/
def arrV {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) : Value :=
  .array (a.val.map wordV)

/-- The outcome encoding of an array of words of the width `ty` and the length `n`. -/
abbrev encA (ty : UScalarTy) (n : Usize) : RustM (Aeneas.Std.Array (UScalar ty) n) →
    Option Value :=
  encR arrV

/-- The chain value of an Aeneas array as a value of the reading is its encoding. -/
theorem toValue_arr {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) :
    (AVal.arr ty n a).toValue = arrV a := by
  simp only [AVal.toValue, arrV]
  rfl

/-! ## The pointwise squares -/

/-- **Indexing.** A value of `index_usize` is, encoded, the value of the table at `index`. -/
theorem index_square {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    (i : Usize) (z : UScalar ty) (h : a.index_usize i = .ok z) :
    hax64WExit "index" [arrV a, wordV i] = some (wordV z) := by
  have hr : appIndex (.arr ty n a) (.w .Usize i) = .ok (.w ty z) := by
    rw [appIndex, asW_w]
    simp only [bind_tc_ok, h]
  have h' := hax64WExit_appIndex hr
  rwa [toValue_arr, toValue_w, toValue_w] at h'

/-- **Update.** A value of `update` is, encoded, the value of the table at
    `array_update`. -/
theorem update_square {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    (i : Usize) (x : UScalar ty) (a' : Aeneas.Std.Array (UScalar ty) n)
    (h : a.update i x = .ok a') :
    hax64WExit "array_update" [arrV a, wordV i, wordV x] = some (arrV a') := by
  have hr : appUpdate (.arr ty n a) (.w .Usize i) (.w ty x) = .ok (.arr ty n a') := by
    rw [appUpdate, asW_w, asW_w]
    simp only [bind_tc_ok, h]
  have h' := hax64WExit_appUpdate hr
  rwa [toValue_arr, toValue_arr, toValue_w, toValue_w] at h'

/-- At an index whose entry `index_usize` returns, `update` returns the array `set`
    writes. -/
theorem update_eq_set {α : Type} {n : Usize} (a : Aeneas.Std.Array α n) (i : Usize) (x v : α)
    (h : a.index_usize i = .ok x) : a.update i v = .ok (a.set i v) := by
  unfold Aeneas.Std.Array.index_usize at h
  unfold Aeneas.Std.Array.update
  split at h
  · cases h
  · rfl

/-- **Mutable indexing.** A value `(x, back)` of `index_mut_usize` gives the value of the
    table at `index`, and for every value `v` the backward function `back` gives the value
    of the table at `array_update`. -/
theorem indexMut_square {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    (i : Usize) (x : UScalar ty) (back : UScalar ty → Aeneas.Std.Array (UScalar ty) n)
    (h : a.index_mut_usize i = .ok (x, back)) :
    hax64WExit "index" [arrV a, wordV i] = some (wordV x) ∧
      ∀ v, hax64WExit "array_update" [arrV a, wordV i, wordV v] = some (arrV (back v)) := by
  unfold Aeneas.Std.Array.index_mut_usize at h
  obtain ⟨y, hy, h⟩ := rustM_bind_ok h
  cases h
  exact ⟨index_square a i x hy, fun v => update_square a i v _ (update_eq_set a i x v hy)⟩

/-- **`repeat`.** At a width of at most `64` bits, `Array.repeat n x` is, encoded, the value
    of the table at `repeat`. -/
private theorem hax64WExit_repeat_arrV {ty : UScalarTy} (hty : ty.numBits ≤ 64) (n : Usize)
    (x : UScalar ty) :
    hax64WExit "repeat" [wordV x, wordV n] = some (arrV (Aeneas.Std.Array.repeat n x)) := by
  have hr : appRepeat (.w ty x) (.w .Usize n) = .ok (.arr ty n (Aeneas.Std.Array.repeat n x)) := by
    rw [appRepeat, asW_w]
    rfl
  have h' := hax64WExit_appRepeat hty hr
  rwa [toValue_arr, toValue_w, toValue_w] at h'

/-- The encodings of words of at most `64` bits are scalar words of the table. -/
theorem all_scalarValNB {ty : UScalarTy} (hty : ty.numBits ≤ 64) (xs : List (UScalar ty)) :
    (xs.map wordV).all scalarValNB = true := by
  have h64 : 2 ^ ty.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hty
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.val < 2 ^ 64 := lt_of_lt_of_le x.hBounds h64
    have hv : scalarValNB (wordV x) = true := by simp [wordV, scalarValNB]; omega
    rw [List.map_cons, List.all_cons, hv, ih, Bool.true_and]

/-- The length of an Aeneas array is below `2 ^ 64`. -/
theorem length_lt_of_usize {ty : UScalarTy} (xs : List (UScalar ty)) (n : Usize)
    (h : xs.length = n.val) : decide ((xs.map wordV).length < 2 ^ 64) = true := by
  have hn : n.val < 2 ^ 64 :=
    lt_of_lt_of_le n.hBounds (Nat.pow_le_pow_right (by decide) usize_numBits_le)
  simp only [List.length_map, h, decide_eq_true_eq]
  exact hn

/-- **Array literals.** At a width of at most `64` bits, `Array.make n xs` is, encoded, the
    value of the table at `array_lit` on the encodings of `xs`. -/
theorem make_square {ty : UScalarTy} (hty : ty.numBits ≤ 64) (n : Usize) (xs : List (UScalar ty))
    (h : xs.length = n.val) :
    hax64WExit "array_lit" (xs.map wordV) = some (arrV (Aeneas.Std.Array.make n xs h)) := by
  have hadm : hax64LitAdmit (xs.map wordV) = true := by
    unfold hax64LitAdmit
    rw [all_scalarValNB hty, Bool.true_or, Bool.true_and]
    exact length_lt_of_usize xs n h
  rw [hax64WExit, ite_eq_left_of_eq_true _ _ (eq_self _),
    ite_eq_left_of_eq_true _ _ (eq_true hadm)]
  rfl

/-! ## The squares on outcomes -/

/-- **Indexing on outcomes**, guarded by a value of the Aeneas operation. -/
theorem index_related {ty : UScalarTy} {n : Usize}
    {a : RustM (Aeneas.Std.Array (UScalar ty) n)} {i : RustM Usize} {a' i' : Option Value}
    (ha : Related (encA ty n) a a') (hi : Related (encU .Usize) i i')
    (hok : OkR (bindR2 (fun x j => x.index_usize j) a i)) :
    Related (encU ty) (bindR2 (fun x j => x.index_usize j) a i)
      (a'.bind fun v => i'.bind fun w => hax64WExit "index" [v, w]) where
  rel := by
    rw [← ha.rel, ← hi.rel]
    obtain ⟨z, hz⟩ := hok
    cases a with
    | ok x =>
      cases i with
      | ok j =>
        rw [bindR2_ok] at hz
        rw [bindR2_ok, hz]
        exact (index_square x j z hz).symm
      | fail _ => cases hz
      | div => cases hz
    | fail _ => cases hz
    | div => cases hz

/-- **`repeat` on outcomes**, a total square registered as an instance. -/
instance repeatRelated {ty : UScalarTy} [TableTy ty] (n : Usize) (a : RustM (UScalar ty))
    (a' : Option Value) [ha : Related (encU ty) a a'] :
    Related (encA ty n) (bindR1 (fun x => .ok (Aeneas.Std.Array.repeat n x)) a)
      (a'.bind fun v => hax64WExit "repeat" [v, wordV n]) where
  rel := by
    rw [← ha.rel]
    exact relatedR1_of (fun _ => ⟨_, rfl⟩) (fun x z hz => by
      cases hz
      exact hax64WExit_repeat_arrV (TableTy.le64 ty) n x) a

end CatCrypt.Crypto.SecureCompilation.AeneasFront
