/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.IterModel

/-!
# Test inputs: loops over the iterator adapters `enumerate` and `zip`

Three functions written in the form the Aeneas Lean backend (commit `b08bf81`) prints a `for`
loop over an iterator adapter: a loop body that steps the adapter state by its `next` function
and matches on the item (as `vec_iter.sum_enumerate` and `iterators.zip_iter` of the Aeneas test
outputs), the loop as `loop` over the body, and the function building the adapter state by the
calls of the iterator model. They are not output of Aeneas; the Rust sources are given in the
docstrings. The accumulator is an argument. The module states no theorem.

* `enum_range_sum`: `for (j, i) in (0..4).enumerate() { acc = acc + a[i] }`;
* `enum_array_sum`: `for (i, x) in a.iter().enumerate() { acc = acc + x + b[i] }`;
* `zip_array_sum`: `for (x, y) in a.iter().zip(b.iter()) { acc = acc + x + y }`.

## Main results

* `enum_range_sum`, `enum_array_sum`, `zip_array_sum` — the three test functions
-/

@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

namespace iter_adapters

/-- The loop body of `enum_range_sum`. -/
def enum_range_sum_loop.body (a : Array Std.U32 4#usize)
    (iter : core.iter.adapters.enumerate.Enumerate (core.ops.range.Range Std.Usize))
    (acc : Std.U32) :
    Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
      (core.ops.range.Range Std.Usize)) × Std.U32) Std.U32) := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done acc)
  | some p =>
    let (_, i) := p
    let x ← Array.index_usize a i
    let acc1 ← acc + x
    ok (cont (iter1, acc1))

/-- The loop of `enum_range_sum`. -/
def enum_range_sum_loop (a : Array Std.U32 4#usize)
    (iter : core.iter.adapters.enumerate.Enumerate (core.ops.range.Range Std.Usize))
    (acc : Std.U32) : Result Std.U32 := do
  loop (fun (iter1, acc1) => enum_range_sum_loop.body a iter1 acc1) (iter, acc)

/-- `fn enum_range_sum(a: &[u32; 4], mut acc: u32) -> u32 {
      for (_, i) in (0..4).enumerate() { acc = acc + a[i]; } acc }` -/
def enum_range_sum (a : Array Std.U32 4#usize) (acc : Std.U32) : Result Std.U32 := do
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 4#usize }
  enum_range_sum_loop a iter acc

/-- The loop body of `enum_array_sum`. -/
def enum_array_sum_loop.body (b : Array Std.U32 4#usize)
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Std.U32))
    (acc : Std.U32) :
    Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter Std.U32)) × Std.U32) Std.U32) := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done acc)
  | some p =>
    let (i, x) := p
    let i1 ← acc + x
    let y ← Array.index_usize b i
    let acc1 ← i1 + y
    ok (cont (iter1, acc1))

/-- The loop of `enum_array_sum`. -/
def enum_array_sum_loop (b : Array Std.U32 4#usize)
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Std.U32))
    (acc : Std.U32) : Result Std.U32 := do
  loop (fun (iter1, acc1) => enum_array_sum_loop.body b iter1 acc1) (iter, acc)

/-- `fn enum_array_sum(a: &[u32; 4], b: &[u32; 4], mut acc: u32) -> u32 {
      for (i, x) in a.iter().enumerate() { acc = acc + x + b[i]; } acc }` -/
def enum_array_sum (a b : Array Std.U32 4#usize) (acc : Std.U32) : Result Std.U32 := do
  let s ← lift (Array.to_slice a)
  let i ← core.slice.Slice.iter s
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) i
  enum_array_sum_loop b iter acc

/-- The loop body of `zip_array_sum`. -/
def zip_array_sum_loop.body
    (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U32)
      (core.slice.iter.Iter Std.U32))
    (acc : Std.U32) :
    Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U32)
      (core.slice.iter.Iter Std.U32)) × Std.U32) Std.U32) := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32)
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done acc)
  | some p =>
    let (x, y) := p
    let i ← acc + x
    let acc1 ← i + y
    ok (cont (iter1, acc1))

/-- The loop of `zip_array_sum`. -/
def zip_array_sum_loop
    (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U32)
      (core.slice.iter.Iter Std.U32))
    (acc : Std.U32) : Result Std.U32 := do
  loop (fun (iter1, acc1) => zip_array_sum_loop.body iter1 acc1) (iter, acc)

/-- `fn zip_array_sum(a: &[u32; 4], b: &[u32; 4], mut acc: u32) -> u32 {
      for (x, y) in a.iter().zip(b.iter()) { acc = acc + x + y; } acc }` -/
def zip_array_sum (a b : Array Std.U32 4#usize) (acc : Std.U32) : Result Std.U32 := do
  let s ← lift (Array.to_slice a)
  let i ← core.slice.Slice.iter s
  let s1 ← lift (Array.to_slice b)
  let i1 ← core.slice.Slice.iter s1
  let iter ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32)
      (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.traits.iterator.IteratorSliceIter Std.U32)) i i1
  zip_array_sum_loop iter acc

end iter_adapters

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
