/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
import Mathlib.Tactic.IntervalCases

/-!
# `mont_bound` — a bounded-arithmetic discharger for the bignum/Montgomery side goals

The ascent bignum/Montgomery vertical produces two families of decidable, linear
side goals:

* **carry-out equalities** — the machine `CF`/borrow bit equals the clean
  over/underflow predicate (`RunBlockCorres.add_carry_eq`,
  `RunBlockCorres.sbb_borrow_eq`);
* **top-carry-zero / range bounds** — the inter-step carry of a Montgomery
  word-step is forced to zero because each partial `< 2·⟦p⟧ < 2^256` while the
  carry weight `(2^64)^(3+|D|) ≥ 2^320` (`FieldReduce.montRedcStep_chain`).

Both live in the LINEAR fragment over the limb values plus one modulus bound, so
`omega` decides them — provided the radix powers are handled correctly. The trap
this module is built around: `set P := (2^64)^n` atomises the power inconsistently
and breaks `omega` (it then sees `P` and `(2^64)^n` as two atoms). The discharger
never does that. It keeps every `(2^64)^e` as a single opaque `Nat` and relates
distinct exponents through the ladder lemma `two_mul_le_pow_of_lt`, which uses
`Nat.pow_le_pow_right`/`pow_succ` and never expands the radix to a numeral.

`mont_bound` is the tactic; its lemma database has two parts. The normalisation
lemmas (`pow256_as_radix`, `pow320_as_radix`, `add_carry_toNat`, `sub_borrow_toNat`)
rewrite the concrete carry weights (`2^256`, `2^320`) into powers of `2^64` and the
`add_carry`/`sub_borrow` result words into their base-`2^64` residues, so the whole
goal speaks one atom family; the reasoning lemmas (`two_mul_le_pow_of_lt`,
`mr_lt_pow`, `mont_carry_zero`) are then applied before `omega`/`interval_cases`
finish it.

At a real callsite the window bound `a < (2^64)^k` is `FieldReduce.valLimbs_lt_pow`
and the range bound `MR < 2·⟦p⟧` is `Number.montgomeryReduce_correct`; the examples
below carry those as hypotheses to keep the file's import surface small.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The lemma database -/

/-- `2^256 = (2^64)^4`: the four-limb radix as a power of the word radix. -/
theorem pow256_as_radix : (2 : ℕ) ^ 256 = (2 ^ 64) ^ 4 := by
  rw [← pow_mul]

/-- `2^320 = (2^64)^5`: the five-word carry weight as a power of the word radix. -/
theorem pow320_as_radix : (2 : ℕ) ^ 320 = (2 ^ 64) ^ 5 := by
  rw [← pow_mul]

/-- The `add_carry` result word as its base-`2^64` residue. -/
theorem add_carry_toNat (x y : BitVec 64) (b : ℕ) :
    (add_carry x y b).toNat = (x.toNat + y.toNat + b) % 2 ^ 64 := by
  rw [add_carry, BitVec.toNat_ofNat]

/-- The `sub_borrow` result word (cast to `ℤ`) as its base-`2^64` residue. -/
theorem sub_borrow_toNat (x y : BitVec 64) (b : ℕ) :
    ((sub_borrow x y b).toNat : Int)
      = ((x.toNat : Int) - y.toNat - b) % ((2 ^ 64 : ℕ) : Int) := by
  rw [sub_borrow, BitVec.toNat_ofInt, Int.toNat_of_nonneg]
  exact Int.emod_nonneg _ (by decide)

/-- **The atomisation-safe power ladder.** From `P < (2^64)^m` and `m < k`,
`2·P ≤ (2^64)^k`. The radix power is never expanded to a numeral: the successor
step `(2^64)^(m+1) = (2^64)^m · 2^64` is `pow_succ`, the growth
`(2^64)^(m+1) ≤ (2^64)^k` is `Nat.pow_le_pow_right`, and the final `omega` sees
each `(2^64)^e` as one consistent atom (with `(2^64)^m · 2^64` linear in that atom).
This is the lemma that lets the top-carry-zero goal cross from the `⟦p⟧ < 2^256`
bound to the `≥ 2^320` carry weight without the `set`-atomisation trap. -/
theorem two_mul_le_pow_of_lt {P m k : ℕ}
    (hP : P < (2 ^ 64) ^ m) (hmk : m < k) : 2 * P ≤ (2 ^ 64) ^ k := by
  have hmono : (2 ^ 64 : ℕ) ^ (m + 1) ≤ (2 ^ 64) ^ k :=
    Nat.pow_le_pow_right (by norm_num) hmk
  have hsucc : (2 ^ 64 : ℕ) ^ (m + 1) = (2 ^ 64) ^ m * 2 ^ 64 := pow_succ _ _
  have hgrow : 2 * (2 ^ 64 : ℕ) ^ m ≤ 2 ^ 64 * (2 ^ 64) ^ m :=
    Nat.mul_le_mul (by norm_num) (le_refl _)
  omega

/-- A Montgomery partial `MR < 2·⟦p⟧` sits below the carry weight `(2^64)^k` when
`⟦p⟧ < (2^64)^m` and `m < k`. The composition of `two_mul_le_pow_of_lt` with the
partial's `< 2·⟦p⟧` range bound; the `MR < Wt` premise of `mont_carry_zero`. -/
theorem mr_lt_pow {MR valP m k : ℕ}
    (hMR : MR < 2 * valP) (hP : valP < (2 ^ 64) ^ m) (hmk : m < k) :
    MR < (2 ^ 64) ^ k :=
  lt_of_lt_of_le hMR (two_mul_le_pow_of_lt hP hmk)

/-- **Carry elimination.** A window value `a < Wt` plus one top carry `cfbit ≤ 1`
weighted at `Wt` equals a target `MR` strictly below the same weight; then the
carry is zero and the window equals the target. `Wt` (typically `(2^64)^k`) stays
an opaque atom — `interval_cases` on the carry bit turns `Wt * cfbit` into `0` or
`Wt`, leaving `omega` a linear goal. -/
theorem mont_carry_zero {a Wt cfbit MR : ℕ}
    (hfold : a + Wt * cfbit = MR) (_ha : a < Wt) (hcf : cfbit ≤ 1)
    (hlt : MR < Wt) : a = MR ∧ cfbit = 0 := by
  interval_cases cfbit <;> omega

/-! ## The tactic

`mont_bound` normalises the goal and hypotheses with the four normalisation lemmas,
then runs a first-match cascade:

1. carry-out equality — reduce `decide _ = decide _` to the iff of the (already
   residue-rewritten) predicates and let `omega` decide wrap ⇔ over/underflow;
2. a straight `omega` for goals already linear over atomic powers;
3. the power-ladder gap `2·P ≤ (2^64)^k`, via `two_mul_le_pow_of_lt`;
4. the top-carry-zero conjunction, via `mont_carry_zero`, deriving `MR < Wt` from
   `MR < 2·P` and the ladder gap. -/
macro "mont_bound" : tactic =>
  `(tactic|
    ((try simp only [pow256_as_radix, pow320_as_radix, add_carry_toNat,
        sub_borrow_toNat] at *) <;>
      first
        | (rw [decide_eq_decide]; omega)
        | omega
        | (apply two_mul_le_pow_of_lt <;> first | assumption | omega)
        | (apply mont_carry_zero <;>
            first
              | assumption
              | omega
              | (apply mr_lt_pow <;> first | assumption | omega))))

/-! ## Representative test goals

Fresh replays of the bound shapes the committed vertical closes; each is a single
`mont_bound`. -/

/-- Top-carry-zero, symbolic-window form (the `montRedcStep_chain` core). The
carry weight `(2^64)^k` with `k > 4` exceeds `2·⟦p⟧` because `⟦p⟧ < 2^256`, so the
inter-step carry is zero and the window equals the reduced value. -/
example (a k cfbit MR valP : ℕ)
    (hfold : a + (2 ^ 64) ^ k * cfbit = MR)
    (ha : a < (2 ^ 64) ^ k)
    (hcf : cfbit ≤ 1)
    (hMR : MR < 2 * valP)
    (hP : valP < 2 ^ 256)
    (hk : 4 < k) :
    a = MR ∧ cfbit = 0 := by mont_bound

/-- Top-carry-zero, concrete `2^320` weight against a `2^256` modulus bound. -/
example (a cfbit MR valP : ℕ)
    (hfold : a + 2 ^ 320 * cfbit = MR)
    (ha : a < 2 ^ 320)
    (hcf : cfbit ≤ 1)
    (hMR : MR < 2 * valP)
    (hP : valP < 2 ^ 256) :
    a = MR ∧ cfbit = 0 := by mont_bound

/-- The `2·⟦p⟧ < carry weight` gap on its own: `2·P ≤ (2^64)^k` from `P < 2^256`. -/
example (valP k : ℕ) (hP : valP < 2 ^ 256) (hk : 4 < k) :
    2 * valP ≤ (2 ^ 64) ^ k := by mont_bound

/-- Limb-window carry-out equality (the ADC leaf): the machine `CF` residue-mismatch
predicate coincides with the clean unsigned-overflow predicate `2^64 ≤ x + y + b`. -/
example (x y : BitVec 64) (b : ℕ) :
    decide ((add_carry x y b).toNat ≠ x.toNat + y.toNat + b)
      = decide (2 ^ 64 ≤ x.toNat + y.toNat + b) := by mont_bound

/-- Limb-window borrow-out equality (the SBB leaf): the machine borrow residue-mismatch
predicate coincides with the clean integer-underflow predicate `x − y − b < 0`. -/
example (x y : BitVec 64) (b : ℕ) (hb : b ≤ 1) :
    decide (((sub_borrow x y b).toNat : Int) ≠ (x.toNat : Int) - (y.toNat + b))
      = decide (((x.toNat : Int) - y.toNat - (b : Int) < 0)) := by mont_bound

end CatCrypt.Crypto.SecureCompilation.Ascent
