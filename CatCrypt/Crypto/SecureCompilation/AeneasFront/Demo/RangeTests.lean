/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.RangeEntry
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestJoins
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestArrays
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestLoops
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.ReifiedIterAdapters
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestSignedGuard

/-!
# Tests of `aeneasRange%`

No-panic theorems by `aeneasRange%` on Aeneas test functions: the checked `u32` addition of
`opt_add_1_or_panic` behind its assertion, the array update of `incr_array`, and the counted
loop of `enum_range_sum`; and the refusals, each naming the step that fails: the `i8` sum
`x + 1` without an input bound, `opt_add_1_or_panic` with an input range that contains a panic
(the assertion, the overflow of `x + 1` at `x = 2 ^ 32 - 1`), and a function with a `while`
loop.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.rangeTest

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

/-- `opt_add_1_or_panic b x` has a value for `b` true and `x ≤ 100`. -/
theorem optAdd_noPanic : ∀ (b : Bool) (x : U32), 1 ≤ (b.toNat : Int) ∧ (b.toNat : Int) ≤ 1 →
    0 ≤ (x.val : Int) ∧ (x.val : Int) ≤ 100 → ∃ y, joins.opt_add_1_or_panic b x = .ok y :=
  aeneasRange% joins.opt_add_1_or_panic [(1, 1), (0, 100)]

/-- `incr_array a` has a value when the entries of `a` are at most `1000`. -/
theorem incrArray_noPanic : ∀ (a : Aeneas.Std.Array U32 2#usize),
    (∀ v ∈ a.val, 0 ≤ (v.val : Int) ∧ (v.val : Int) ≤ 1000) →
    ∃ y, arrays.incr_array a = .ok y :=
  aeneasRange% arrays.incr_array [(0, 1000)]

/-- The sum `enum_range_sum a acc` of a counted loop has a value when the entries of `a` and
    `acc` are at most `1000`. -/
theorem enumRangeSum_noPanic : ∀ (a : Aeneas.Std.Array U32 4#usize) (acc : U32),
    (∀ v ∈ a.val, 0 ≤ (v.val : Int) ∧ (v.val : Int) ≤ 1000) →
    0 ≤ (acc.val : Int) ∧ (acc.val : Int) ≤ 1000 →
    ∃ y, iter_adapters.enum_range_sum a acc = .ok y :=
  aeneasRange% iter_adapters.enum_range_sum [(0, 1000), (0, 1000)]

/-- error: aeneasRange%: the interval check refuses: a reachable abort -/
#guard_msgs in
example := aeneasRange% signedGuardTest.incr [_]

/-- error: aeneasRange%: the interval check refuses: a reachable abort -/
#guard_msgs in
example := aeneasRange% joins.opt_add_1_or_panic [_, (0, 100)]

/--
error: aeneasRange%: the interval check refuses: call Add#32 refused at [(0, 4294967295), (1, 1)]
-/
#guard_msgs in
example := aeneasRange% joins.opt_add_1_or_panic [(1, 1), (0, 4294967295)]

/--
error: aeneasRange%: the reading or its completeness refuses: completeAeneas%: the while loop
`Reify.loop` has no complete twin
-/
#guard_msgs (whitespace := lax) in
example := aeneasRange% loops.iter_loop [(0, 10), (0, 10)]

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.rangeTest
