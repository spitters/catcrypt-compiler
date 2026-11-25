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
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestSigned
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestSignedGuard64

/-!
# Tests of `aeneasRange%`

No-panic theorems by `aeneasRange%` on Aeneas test functions: the checked `u32` addition of
`opt_add_1_or_panic` behind its assertion, the array update of `incr_array`, and the counted
loop of `enum_range_sum`, the checked `i32` sums of `ref_incr` and `add` read through their
overflow guard, the checked `i64` sums of `incr` and `incrT` and the difference of `dec` read
through their sign-bit guard, `incr` and `x - 1` by `dec` on ranges with negative values; and
the refusals, each naming the step that fails: `ref_incr` at `x = 2 ^ 31 - 1`, the `i64` sum
`incr` at `x = 2 ^ 63 - 1`, the `i64` difference `x - 1` at `x = -2 ^ 63`, the `i8` sum
`x + 1` without an input bound, `opt_add_1_or_panic` with an input range that contains a panic
(the assertion, the overflow of `x + 1` at `x = 2 ^ 32 - 1`), and a function with a `while`
loop.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.rangeTest

open HaxLean.Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

/-- `opt_add_1_or_panic b x` has a value for `b` true and `x ≤ 100`. -/
theorem optAdd_noPanic : ∀ (b : Bool) (x : U32), 1 ≤ (b.toNat : Int) ∧ (b.toNat : Int) ≤ 1 →
    0 ≤ (x.val : Int) ∧ (x.val : Int) ≤ 100 → ∃ y, joins.opt_add_1_or_panic b x = .ok y :=
  aeneasRange% joins.opt_add_1_or_panic [(1, 1), (0, 100)]

/-- `incr_array a` has a value when the entries of `a` are at most `1000`. -/
theorem incrArray_noPanic : ∀ (a : HaxLean.Aeneas.Std.Array U32 2#usize),
    (∀ v ∈ a.val, 0 ≤ (v.val : Int) ∧ (v.val : Int) ≤ 1000) →
    ∃ y, arrays.incr_array a = .ok y :=
  aeneasRange% arrays.incr_array [(0, 1000)]

/-- The sum `enum_range_sum a acc` of a counted loop has a value when the entries of `a` and
    `acc` are at most `1000`. -/
theorem enumRangeSum_noPanic : ∀ (a : HaxLean.Aeneas.Std.Array U32 4#usize) (acc : U32),
    (∀ v ∈ a.val, 0 ≤ (v.val : Int) ∧ (v.val : Int) ≤ 1000) →
    0 ≤ (acc.val : Int) ∧ (acc.val : Int) ≤ 1000 →
    ∃ y, iter_adapters.enum_range_sum a acc = .ok y :=
  aeneasRange% iter_adapters.enum_range_sum [(0, 1000), (0, 1000)]

/-- The checked `i32` sum `ref_incr x = x + 1`, read through its overflow guard, has a value
    for `x` in `[0, 2 ^ 31 - 2]`. -/
theorem refIncr_noPanic : ∀ x : I32, 0 ≤ x.val ∧ x.val ≤ 2 ^ 31 - 2 →
    ∃ y, paper.ref_incr x = .ok y :=
  aeneasRange% paper.ref_incr [(0, 2 ^ 31 - 2)]

/-- The checked `i32` sum `add a b` has a value for `a` and `b` in `[0, 1000]`. -/
theorem constAdd_noPanic : ∀ a b : I32, 0 ≤ a.val ∧ a.val ≤ 1000 → 0 ≤ b.val ∧ b.val ≤ 1000 →
    ∃ y, constants.add a b = .ok y :=
  aeneasRange% constants.add [(0, 1000), (0, 1000)]

/-- The checked `i64` sum `incr x = x + 1`, read through its sign-bit guard, has a value for `x`
    in `[0, 2 ^ 63 - 2]`. -/
theorem incr64_noPanic : ∀ x : I64, 0 ≤ x.val ∧ x.val ≤ 2 ^ 63 - 2 →
    ∃ y, signedGuard64Test.incr x = .ok y :=
  aeneasRange% signedGuard64Test.incr [(0, 2 ^ 63 - 2)]

/-- The checked `i64` sum `x + 1` in tail position has a value for `x` in `[0, 2 ^ 62]`. -/
theorem incrT64_noPanic : ∀ x : I64, 0 ≤ x.val ∧ x.val ≤ 2 ^ 62 →
    ∃ y, signedGuard64Test.incrT x = .ok y :=
  aeneasRange% signedGuard64Test.incrT [(0, 2 ^ 62)]

/-- The checked `i64` difference `dec x y = x - y` has a value for `x` and `y` in
    `[0, 2 ^ 62]`. -/
theorem dec64_noPanic : ∀ x y : I64, 0 ≤ x.val ∧ x.val ≤ 2 ^ 62 → 0 ≤ y.val ∧ y.val ≤ 2 ^ 62 →
    ∃ z, signedGuard64Test.dec x y = .ok z :=
  aeneasRange% signedGuard64Test.dec [(0, 2 ^ 62), (0, 2 ^ 62)]

/-- The checked `i64` sum `incr x = x + 1` has a value for `x` in `[-2 ^ 62, 2 ^ 62]`: the
    nonnegative and the negative values are checked apart, the negative ones on a subdivided
    range. -/
theorem incr64Signed_noPanic : ∀ x : I64, -2 ^ 62 ≤ x.val ∧ x.val ≤ 2 ^ 62 →
    ∃ y, signedGuard64Test.incr x = .ok y :=
  aeneasRange% signedGuard64Test.incr [(-2 ^ 62, 2 ^ 62)]

/-- The checked `i64` sum `incr x = x + 1` has a value at every negative `x`. -/
theorem incr64Neg_noPanic : ∀ x : I64, -2 ^ 63 ≤ x.val ∧ x.val ≤ -1 →
    ∃ y, signedGuard64Test.incr x = .ok y :=
  aeneasRange% signedGuard64Test.incr [(-2 ^ 63, -1)]

/-- The checked `i64` difference `dec x 1 = x - 1` has a value for `x` in
    `[-2 ^ 62, 2 ^ 62]`. -/
theorem dec64Signed_noPanic : ∀ x y : I64, -2 ^ 62 ≤ x.val ∧ x.val ≤ 2 ^ 62 →
    1 ≤ y.val ∧ y.val ≤ 1 → ∃ z, signedGuard64Test.dec x y = .ok z :=
  aeneasRange% signedGuard64Test.dec [(-2 ^ 62, 2 ^ 62), (1, 1)]

/-- error: aeneasRange%: the interval check refuses: a reachable abort -/
#guard_msgs in
example := aeneasRange% signedGuard64Test.incr [(0, 2 ^ 63 - 1)]

/-- error: aeneasRange%: the interval check refuses: a reachable abort -/
#guard_msgs in
example := aeneasRange% signedGuard64Test.dec [(-2 ^ 63, 0), (1, 1)]

/-- error: aeneasRange%: the interval check refuses: a reachable abort -/
#guard_msgs in
example := aeneasRange% paper.ref_incr [(0, 2 ^ 31 - 1)]

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
