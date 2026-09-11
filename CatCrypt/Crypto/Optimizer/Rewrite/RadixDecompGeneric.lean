/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Digits.Lemmas


@[expose] public section
set_option autoImplicit false

/-!
# Generic radix-`base` limb decomposition / recomposition round-trip

This is the abstract correctness of multi-limb (positional-numeral)
representation — the carrier underneath every concrete bignum / `encMLK` /
`bignumVal` view: a natural number splits into a fixed list of `numLimbs`
limbs (repeated divmod by `base`), and recomposes (Horner evaluation in
`base`) to the original value whenever it fits in `numLimbs` digits.

The keystone is `fromLimbs_toLimbs`:
`n < base ^ numLimbs → fromLimbs base (toLimbs base n numLimbs) = n`,
i.e. `bignumVal ∘ splitLimbs = id` on bounded values, abstractly.

* `toLimbs base n numLimbs` — least-significant-first list of exactly
  `numLimbs` limbs, by repeated `divmod` by `base`.
* `fromLimbs base limbs` — Horner evaluation `Σ limbs[i] * base ^ i`.
  This is definitionally `Nat.ofDigits base` (see `fromLimbs_eq_ofDigits`),
  so Mathlib's variable-length digit round-trip `Nat.ofDigits_digits` is
  recovered, and this file supplies the *fixed-length padded* variant on top.

Worked example: `13` in base `2` with `4` limbs is `[1, 0, 1, 1]`, which
recomposes to `1 + 2*(0 + 2*(1 + 2*(1 + 2*0))) = 13` (`#eval` at the end).
-/

namespace CatCrypt.Optimizer.Rewrite.RadixDecompGeneric

/-- Recompose a least-significant-first limb list into a natural number by
Horner evaluation in `base`: `Σ_i limbs[i] * base ^ i`. -/
def fromLimbs (base : ℕ) (limbs : List ℕ) : ℕ :=
  limbs.foldr (fun d acc => d + base * acc) 0

/-- Decompose `n` into exactly `numLimbs` least-significant-first limbs by
repeated division by `base`. -/
def toLimbs (base : ℕ) (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | (k + 1) => (n % base) :: toLimbs base (n / base) k

@[simp] theorem fromLimbs_nil (base : ℕ) : fromLimbs base [] = 0 := rfl

@[simp] theorem fromLimbs_cons (base d : ℕ) (limbs : List ℕ) :
    fromLimbs base (d :: limbs) = d + base * fromLimbs base limbs := rfl

@[simp] theorem toLimbs_zero (base n : ℕ) : toLimbs base n 0 = [] := rfl

@[simp] theorem toLimbs_succ (base n k : ℕ) :
    toLimbs base n (k + 1) = (n % base) :: toLimbs base (n / base) k := rfl

/-- `fromLimbs` is exactly Mathlib's `Nat.ofDigits` on the same limb list, so
the entire `Nat.digits`/`Nat.ofDigits` API transfers. -/
theorem fromLimbs_eq_ofDigits (base : ℕ) (limbs : List ℕ) :
    fromLimbs base limbs = Nat.ofDigits base limbs := by
  induction limbs with
  | nil => simp [fromLimbs, Nat.ofDigits]
  | cons d limbs ih =>
      simp only [fromLimbs, List.foldr_cons, Nat.ofDigits_cons]
      rw [show List.foldr (fun d acc => d + base * acc) 0 limbs = fromLimbs base limbs from rfl, ih]

/-- `toLimbs` always produces exactly `numLimbs` limbs. -/
@[simp] theorem toLimbs_length (base n numLimbs : ℕ) :
    (toLimbs base n numLimbs).length = numLimbs := by
  induction numLimbs generalizing n with
  | zero => rfl
  | succ k ih => simp [toLimbs, ih]

/-- Every limb produced by `toLimbs` is `< base` (when `1 < base`). -/
theorem toLimbs_lt_base (base : ℕ) (hbase : 1 < base) (n numLimbs : ℕ)
    (d : ℕ) (hd : d ∈ toLimbs base n numLimbs) : d < base := by
  induction numLimbs generalizing n with
  | zero => simp [toLimbs] at hd
  | succ k ih =>
      rw [toLimbs_succ, List.mem_cons] at hd
      rcases hd with h | h
      · subst h; exact Nat.mod_lt _ (lt_of_lt_of_le Nat.zero_lt_one (le_of_lt hbase))
      · exact ih (n / base) h

/-- **Keystone round-trip.** A value that fits in `numLimbs` base-`base` limbs
recomposes from its limb decomposition to itself:
`fromLimbs base (toLimbs base n numLimbs) = n` when `n < base ^ numLimbs`. -/
theorem fromLimbs_toLimbs (base : ℕ) (n numLimbs : ℕ)
    (hn : n < base ^ numLimbs) :
    fromLimbs base (toLimbs base n numLimbs) = n := by
  induction numLimbs generalizing n with
  | zero =>
      simp only [pow_zero, Nat.lt_one_iff] at hn
      subst hn
      rfl
  | succ k ih =>
      rw [toLimbs_succ, fromLimbs_cons]
      have hdiv : n / base < base ^ k := by
        rw [pow_succ] at hn
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hn)
      rw [ih (n / base) hdiv]
      exact Nat.mod_add_div n base

/-- Fixed-length padded round-trip stated through Mathlib's `Nat.ofDigits`:
`toLimbs` is a (zero-padded, fixed-length) section of `Nat.ofDigits`. -/
theorem ofDigits_toLimbs (base : ℕ) (n numLimbs : ℕ)
    (hn : n < base ^ numLimbs) :
    Nat.ofDigits base (toLimbs base n numLimbs) = n := by
  rw [← fromLimbs_eq_ofDigits]
  exact fromLimbs_toLimbs base n numLimbs hn

/-- Worked example: `13` in base `2` with `4` limbs is `[1, 0, 1, 1]`. -/
example : toLimbs 2 13 4 = [1, 0, 1, 1] := rfl

/-- Worked example: the limbs of `13` recompose to `13`. -/
example : fromLimbs 2 [1, 0, 1, 1] = 13 := rfl

end CatCrypt.Optimizer.Rewrite.RadixDecompGeneric
