/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AeneasBackendPrelude

/-!
# The iterator adapters of the Aeneas standard library over the vendored model

The Aeneas Lean backend prints `for` loops over the iterator adapters `enumerate`, `step_by`
and `zip` as calls into the iterator model of its standard library (`Aeneas/Std/Core/Iter.lean`
and `Aeneas/Std/SliceIter.lean` at Aeneas commit `b08bf81`). This module gives those names over
the vendored flat result type `RustM`, so that a backend file using them elaborates with
`import Aeneas` replaced by `import HaxLean.AeneasBackendPrelude` and this module:

* the trait record `core.iter.traits.iterator.Iterator` with the methods `next`, `step_by`
  and `enumerate`, and its instances at a range (`IteratorRange`), a slice iterator
  (`IteratorSliceIter`), `StepBy` and `Enumerate`;
* the adapter states `StepBy`, `Enumerate`, `Zip`, their constructors (`trait_default`) and
  their `next` functions;
* the slice iterator `core.slice.iter.Iter`, `core.slice.Slice.iter`, and the trait record
  `IntoIterator` with its blanket instance, which `zip` takes.

The definitions follow the upstream ones. The instances give the `step_by` and `enumerate`
methods as the default bodies (upstream: `trait_default` at the instance itself, which ignores
the instance); the upstream `take` method and `Take` adapter are not given. The slice
iterator indexes the list of the slice.

## Main results

* `core.iter.adapters.step_by.StepBy`, `core.iter.adapters.enumerate.Enumerate`,
  `core.iter.adapters.zip.Zip` — the adapter states
* `core.iter.traits.iterator.IteratorStepBy`, `core.iter.traits.iterator.IteratorEnumerate`,
  `core.iter.traits.iterator.IteratorSliceIter` — their iterator instances
* `core.iter.traits.collect.IntoIterator.Blanket.into_iter` — the blanket `IntoIterator`
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

/-- `core::iter::adapters::step_by::StepBy`: the inner iterator and the step. -/
structure core.iter.adapters.step_by.StepBy (I : Type) where
  /-- The inner iterator. -/
  iter : I
  /-- The step. -/
  step_by : Usize

/-- `core::iter::adapters::enumerate::Enumerate`: the inner iterator and the count of the
    items it has yielded. -/
structure core.iter.adapters.enumerate.Enumerate (I : Type) where
  /-- The inner iterator. -/
  iter : I
  /-- The index of the next item. -/
  count : Usize

/-- `core::iter::adapters::zip::Zip`: the two inner iterators. -/
structure core.iter.adapters.zip.Zip (A B : Type) where
  mk ::
  /-- The first iterator. -/
  fst : A
  /-- The second iterator. -/
  snd : B

/-- The default body of `Iterator::step_by`: a panic at the step `0`. -/
def core.iter.traits.iterator.Iterator.step_by.default {Self : Type} (self : Self)
    (step_by : Usize) : RustM (core.iter.adapters.step_by.StepBy Self) :=
  if step_by.val = 0 then .fail .panic else .ok ⟨self, step_by⟩

/-- The default body of `Iterator::enumerate`: the count starts at `0`. -/
def core.iter.traits.iterator.Iterator.enumerate.default {Self : Type} (self : Self) :
    RustM (core.iter.adapters.enumerate.Enumerate Self) :=
  .ok { iter := self, count := 0#usize }

/-- The trait `core::iter::traits::iterator::Iterator`: `next` and the adapter methods. -/
structure core.iter.traits.iterator.Iterator (Self : Type) (Self_Item : Type) where
  /-- The next item and the stepped iterator. -/
  next : Self → RustM (Option Self_Item × Self)
  /-- `step_by`. -/
  step_by : Self → Usize → RustM (core.iter.adapters.step_by.StepBy Self) :=
    core.iter.traits.iterator.Iterator.step_by.default
  /-- `enumerate`. -/
  enumerate : Self → RustM (core.iter.adapters.enumerate.Enumerate Self) :=
    core.iter.traits.iterator.Iterator.enumerate.default

/-- `Iterator::step_by` as the backend calls it. -/
def core.iter.traits.iterator.Iterator.step_by.trait_default {Self Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator Self Item) (self : Self)
    (step_by : Usize) : RustM (core.iter.adapters.step_by.StepBy Self) :=
  core.iter.traits.iterator.Iterator.step_by.default self step_by

/-- `Iterator::enumerate` as the backend calls it. -/
def core.iter.traits.iterator.Iterator.enumerate.trait_default {Self Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator Self Item) (self : Self) :
    RustM (core.iter.adapters.enumerate.Enumerate Self) :=
  core.iter.traits.iterator.Iterator.enumerate.default self

/-- The iterator over a range, stepped by `IteratorRange.next`. -/
def core.iter.traits.iterator.IteratorRange {A : Type} (StepInst : core.iter.range.Step A) :
    core.iter.traits.iterator.Iterator (core.ops.range.Range A) A where
  next := core.iter.range.IteratorRange.next StepInst

/-- Skips up to `n` items of an iterator, stopping at its end. -/
def core.iter.adapters.step_by.skipN {I Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator I Item) (iter : I) : Nat → RustM I
  | 0 => .ok iter
  | n + 1 => do
    let (opt, iter) ← iterInst.next iter
    match opt with
    | none => .ok iter
    | some _ => core.iter.adapters.step_by.skipN iterInst iter n

/-- `StepBy::next`: the next item of the inner iterator, then `step - 1` items skipped. -/
def core.iter.adapters.step_by.IteratorStepBy.next {I Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
    core.iter.adapters.step_by.StepBy I →
      RustM (Option Item × core.iter.adapters.step_by.StepBy I) :=
  fun self => do
    let (opt, iter) ← IteratorInst.next self.iter
    match opt with
    | none => .ok (none, { self with iter })
    | some item => do
      let iter ← core.iter.adapters.step_by.skipN IteratorInst iter (self.step_by.val - 1)
      .ok (some item, { iter, step_by := self.step_by })

/-- The iterator `StepBy`. -/
def core.iter.traits.iterator.IteratorStepBy {I Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.step_by.StepBy I) Item where
  next := core.iter.adapters.step_by.IteratorStepBy.next IteratorInst

/-- `Enumerate::next`: the next item of the inner iterator paired with the count, and the
    count incremented by the checked addition. -/
def core.iter.adapters.enumerate.IteratorEnumerate.next {I Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) :
    RustM (Option (Usize × Item) × core.iter.adapters.enumerate.Enumerate I) := do
  let (opt, iter') ← IteratorInst.next self.iter
  match opt with
  | none => .ok (none, { iter := iter', count := self.count })
  | some a => do
    let count' ← self.count + 1#usize
    .ok (some (self.count, a), { iter := iter', count := count' })

/-- The iterator `Enumerate`. -/
def core.iter.traits.iterator.IteratorEnumerate {I Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.enumerate.Enumerate I)
      (Usize × Item) where
  next := core.iter.adapters.enumerate.IteratorEnumerate.next IteratorInst

/-- `core::slice::iter::Iter`: the slice and the index of the next item. -/
structure core.slice.iter.Iter (T : Type) where
  /-- The slice. -/
  slice : Slice T
  /-- The index of the next item. -/
  i : Nat

/-- `<[T]>::iter`: the iterator from the first item. -/
def core.slice.Slice.iter {T : Type} (s : Slice T) : RustM (core.slice.iter.Iter T) :=
  .ok ⟨s, 0⟩

/-- `Iter::next`: the item at the index and the index incremented, `none` at the end. -/
def core.slice.iter.IteratorSliceIter.next {T : Type} (it : core.slice.iter.Iter T) :
    RustM (Option T × core.slice.iter.Iter T) :=
  if h : it.i < it.slice.val.length then
    .ok (some it.slice.val[it.i], { it with i := it.i + 1 })
  else .ok (none, it)

/-- The iterator over a slice. -/
def core.iter.traits.iterator.IteratorSliceIter (T : Type) :
    core.iter.traits.iterator.Iterator (core.slice.iter.Iter T) T where
  next := core.slice.iter.IteratorSliceIter.next

/-- The trait `core::iter::traits::collect::IntoIterator`. -/
structure core.iter.traits.collect.IntoIterator (Self : Type) (Item : Type) (IntoIter : Type) where
  /-- The iterator instance of the result. -/
  iteratorInst : core.iter.traits.iterator.Iterator IntoIter Item
  /-- The conversion. -/
  into_iter : Self → RustM IntoIter

/-- The blanket `into_iter` of an iterator: the iterator itself. -/
def core.iter.traits.collect.IntoIterator.Blanket.into_iter {I Item : Type}
    (_ : core.iter.traits.iterator.Iterator I Item) : I → RustM I :=
  fun x => .ok x

/-- The blanket `IntoIterator` instance of an iterator. -/
def core.iter.traits.collect.IntoIterator.Blanket {I Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
    core.iter.traits.collect.IntoIterator I Item I where
  iteratorInst := IteratorInst
  into_iter := core.iter.traits.collect.IntoIterator.Blanket.into_iter IteratorInst

/-- The default body of `Iterator::zip`: the second operand converted by `into_iter`. -/
def core.iter.traits.iterator.Iterator.zip.default {Self U IntoIter : Type}
    (into_iter : U → RustM IntoIter) :
    Self → U → RustM (core.iter.adapters.zip.Zip Self IntoIter) :=
  fun self other => do
    let b ← into_iter other
    .ok ⟨self, b⟩

/-- `Iterator::zip` as the backend calls it. -/
def core.iter.traits.iterator.Iterator.zip.trait_default {Self U Item0 Item1 IntoIter : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator Self Item0)
    (IntoIterInst : core.iter.traits.collect.IntoIterator U Item1 IntoIter) :
    Self → U → RustM (core.iter.adapters.zip.Zip Self IntoIter) :=
  core.iter.traits.iterator.Iterator.zip.default IntoIterInst.into_iter

/-- `Zip::next`: the next item of the first iterator and, when there is one, of the second. -/
def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    {A B Item_A Item_B : Type}
    (IA : core.iter.traits.iterator.Iterator A Item_A)
    (IB : core.iter.traits.iterator.Iterator B Item_B)
    (z : core.iter.adapters.zip.Zip A B) :
    RustM (Option (Item_A × Item_B) × core.iter.adapters.zip.Zip A B) := do
  let (oa, a') ← IA.next z.fst
  match oa with
  | none => .ok (none, ⟨a', z.snd⟩)
  | some a => do
    let (ob, b') ← IB.next z.snd
    match ob with
    | none => .ok (none, ⟨a', b'⟩)
    | some b => .ok (some (a, b), ⟨a', b'⟩)

end Aeneas.Std
