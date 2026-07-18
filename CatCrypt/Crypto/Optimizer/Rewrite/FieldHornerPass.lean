/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Horner-form polynomial-evaluation rewrite

A verified strength-reduction pass for polynomial evaluation over a generic
commutative ring `R`. A polynomial is represented by its coefficient list
`coeffs : List R`, low-degree first, so `[a, b, c]` denotes `a + b·x + c·x²`.

Two evaluators:

* `evalNaive coeffs x` — the literal monomial sum `∑ᵢ coeffsᵢ · xⁱ`. Computing
  it as written takes `O(n²)` multiplications (each `xⁱ` rebuilt from scratch)
  or `O(n)` extra multiplications plus running-power bookkeeping.
* `evalHorner coeffs x` — the Horner schedule
  `c₀ + x·(c₁ + x·(c₂ + …))`, a single `List.foldr`. It uses exactly `n`
  multiplications and `n` additions and no auxiliary powers.

The keystone is `evalHorner_eq_evalNaive`: the Horner rewrite is
*value-preserving*, so it is a sound optimizer rewrite — only the evaluation
schedule changes, never the result. This is the classical polynomial-evaluation
strength reduction and shows up throughout the field layer: NTT twiddle
evaluation, Barrett/Montgomery modular reduction, and field exponentiation by a
fixed exponent all benefit from it.

The proof is by induction on `coeffs`. The cons step rests on two matching
recurrences,

* `evalHorner (c :: cs) x = c + x * evalHorner cs x`  (definitional, `foldr`);
* `evalNaive (c :: cs) x = c + x * evalNaive cs x`    (`evalNaive_cons`),

where the second factors a single `x` out of every monomial of the tail. We use
a `List.foldr`-based naive evaluator so that this factoring is a clean
`List.map`/`mul_sum` manipulation rather than a `Finset.range` reindex.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.FieldHornerPass

variable {R : Type*} [CommRing R]

/-! ## The two evaluators -/

/-- Naive monomial evaluation of the coefficient list `coeffs` (low-degree
first) at `x`: the sum `∑ᵢ coeffsᵢ · xⁱ`.

We build the monomial list with `List.zipIdx` (each coefficient paired with its
index `i`, contributing `cᵢ · xⁱ`) and sum it. The `List.sum` form makes the
cons-step `x`-factoring (`evalNaive_cons`) a direct `List.map`/`mul_sum`
rewrite. -/
def evalNaive (coeffs : List R) (x : R) : R :=
  (coeffs.zipIdx.map (fun p => p.1 * x ^ p.2)).sum

/-- Horner evaluation: `c₀ + x·(c₁ + x·(c₂ + …))`, a single `List.foldr` using
`n` multiplications and `n` additions. -/
def evalHorner (coeffs : List R) (x : R) : R :=
  coeffs.foldr (fun c acc => c + x * acc) 0

/-! ## Defining recurrences -/

@[simp] theorem evalNaive_nil (x : R) : evalNaive ([] : List R) x = 0 := rfl

@[simp] theorem evalHorner_nil (x : R) : evalHorner ([] : List R) x = 0 := rfl

@[simp] theorem evalHorner_cons (c : R) (cs : List R) (x : R) :
    evalHorner (c :: cs) x = c + x * evalHorner cs x := rfl

/-- The naive evaluator obeys the same `c + x * tail` recurrence as Horner.
The constant term `c · x⁰ = c` splits off, and every monomial of the tail gains
one factor of `x` (the index of each tail coefficient is shifted up by one), so
a single `x` factors out of the whole tail sum. -/
theorem evalNaive_cons (c : R) (cs : List R) (x : R) :
    evalNaive (c :: cs) x = c + x * evalNaive cs x := by
  unfold evalNaive
  -- `(c :: cs).zipIdx = (c, 0) :: (cs.zipIdx with indices shifted by 1)`.
  rw [List.zipIdx_cons]
  simp only [List.map_cons, List.sum_cons, pow_zero, mul_one]
  congr 1
  -- Remaining goal: the tail sum equals `x *` the un-shifted tail sum.
  -- `cs.zipIdx 1` re-indexes `cs.zipIdx 0` by `+1`, so each tail monomial gains
  -- one factor of `x`; pull that single `x` out of the whole sum.
  rw [List.zipIdx_succ, List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, pow_succ]
  ring

/-! ## The keystone: Horner ≡ naive -/

/-- **Soundness of the Horner rewrite.** The Horner schedule evaluates a
coefficient list to the same value as the naive monomial sum, over *any*
commutative ring and at *any* point. Hence rewriting a polynomial evaluation
into Horner form — replacing the `O(n²)` monomial sum by `n` multiplications and
`n` additions — is value-preserving, i.e. a sound optimizer rewrite.

By induction on `coeffs`: the nil case is `0 = 0`; the cons case matches the two
recurrences `evalHorner_cons` and `evalNaive_cons` and applies the tail
hypothesis. -/
theorem evalHorner_eq_evalNaive (coeffs : List R) (x : R) :
    evalHorner coeffs x = evalNaive coeffs x := by
  induction coeffs with
  | nil => simp
  | cons c cs ih => rw [evalHorner_cons, evalNaive_cons, ih]

/-! ## Worked example

For `coeffs = [a, b, c]`, i.e. the polynomial `a + b·x + c·x²`, both evaluators
agree by the keystone, and each reduces to the expected closed form. -/

/-- Naive evaluation of `[a, b, c]` is `a + b·x + c·x²`. -/
theorem evalNaive_three (a b c x : R) :
    evalNaive [a, b, c] x = a + b * x + c * x ^ 2 := by
  simp only [evalNaive, List.zipIdx, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

/-- Horner evaluation of `[a, b, c]` is the schedule `a + x·(b + x·c)`. -/
theorem evalHorner_three (a b c x : R) :
    evalHorner [a, b, c] x = a + x * (b + x * c) := by
  simp only [evalHorner, List.foldr_cons, List.foldr_nil]
  ring

/-- The two forms of `[a, b, c]` coincide: `a + x·(b + x·c) = a + b·x + c·x²`.
A specialization of the keystone, exhibiting the Horner strength reduction on a
concrete degree-2 polynomial. -/
theorem horner_eq_naive_three (a b c x : R) :
    a + x * (b + x * c) = a + b * x + c * x ^ 2 := by
  rw [← evalHorner_three, ← evalNaive_three, evalHorner_eq_evalNaive]

/-- Denotation preservation is characteristic-free: the example holds verbatim
over any `ZMod p`. -/
theorem horner_eq_naive_three_zmod (p : Nat) (a b c x : ZMod p) :
    evalHorner [a, b, c] x = evalNaive [a, b, c] x :=
  evalHorner_eq_evalNaive _ _

end CatCrypt.Crypto.Optimizer.Rewrite.FieldHornerPass
