/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Unsaturated Solinas arithmetic over the integers

A prime `p = 2^k - Σ c·2^e` is represented by `n` limbs of uniform width `b`: the limb
vector `f : Fin n → ℤ` stands for `evalZ f = Σ f i · 2^(b·i)`, with `k ≤ n·b`. Uniform
weights cover Curve25519 (`b = 51`, `k = 255`, `[(19, 0)]`), Poly1305 (`b = 44`,
`k = 130`, `[(5, 0)]`) and p448 (`b = 56`, `k = 448`, `[(1, 224), (1, 0)]`); fiat-crypto's
non-uniform weights `2^⌈i·k/n⌉` are not needed for these three and are not modelled.

This module is the integer layer of the template, with no bounds on the limbs. A product
term `x_i · y_j` has weight `b·(i+j)`; a weight `W ≥ k` is reduced through `2^k ≡ Σ c·2^e`
(`reduceW`), and a term of multiplier `m` at weight `W` is placed at limb `⌊W/b⌋` with
multiplier `m · 2^(W mod b)` (`place`). The product limbs are the sums of the placed terms
(`mulZ`, `squareZ`). A carry at limb `i` keeps the low `b` bits there and adds the rest,
shifted down by `b`, to limb `i + 1`; at the top limb the carry has weight `n·b` and is
placed by the same reduction (`carryZ`). Every congruence is modulo `pZ = 2^k - Σ c·2^e`.

The low part of a carry is `lowZ b x = (x.toNat mod 2^b)`, which is the word semantics of
`and` with the mask `2^b - 1`; its congruence asks the carried limb to be nonnegative.

## Main definitions

* `UnsatParams`, `UnsatParams.pZ`, `UnsatParams.p`, `UnsatParams.evalZ`: the parameters,
  the prime and the value of a limb vector.
* `UnsatParams.reduceW`, `UnsatParams.place`: the reduction and placement of a weight.
* `UnsatParams.mulTerms`, `UnsatParams.sqTerms`, `UnsatParams.wrapTerms`: the placed terms
  of a product, of a square and of the top carry.
* `prodZ`, `UnsatParams.mulZ`, `UnsatParams.squareZ`: the product limbs.
* `lowZ`, `UnsatParams.carryZ`, `UnsatParams.carryChain`: one carry and a schedule.
* `UnsatParams.Placed`: every placed term lands in a limb below `n`.
* `curve25519Unsat`, `curve25519Chain`: the Curve25519 record and fiat-crypto's carry
  schedule of `carry_mul`.

## Main results

* `UnsatParams.reduceW_cong`: the reduction preserves the value modulo `pZ`.
* `UnsatParams.mulZ_cong`, `UnsatParams.squareZ_cong`: the product limbs are congruent to
  the product of the values.
* `UnsatParams.carryZ_cong`, `UnsatParams.carryChain_cong`: a carry and a schedule of
  carries preserve the value modulo `pZ` on nonnegative limbs.
* `UnsatParams.carryMulZ_cong`, `UnsatParams.carrySquareZ_cong`: the carried product and
  square are congruent to the product of the values.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatZ

/-! ## 1. List sums -/

theorem sum_modEq {α : Type} {m : ℤ} (l : List α) (f g : α → ℤ)
    (h : ∀ a ∈ l, f a ≡ g a [ZMOD m]) : (l.map f).sum ≡ (l.map g).sum [ZMOD m] := by
  induction l with
  | nil => exact Int.ModEq.refl _
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun b hb => h b (by simp [hb]))

theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → ℤ) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem sum_map_filter {α : Type} (l : List α) (p : α → Bool) (f : α → ℤ) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

theorem sum_fin_ite {n : ℕ} (L0 : ℕ) (h : L0 < n) (g : Fin n → ℤ) :
    ∑ L : Fin n, (if (L : ℕ) = L0 then g L else 0) = g ⟨L0, h⟩ := by
  rw [Finset.sum_eq_single ⟨L0, h⟩]
  · simp
  · intro c _ hc
    have : (c : ℕ) ≠ L0 := fun e => hc (Fin.ext e)
    simp [this]
  · simp

/-- A sum over ordered pairs of a symmetric function is the sum over the pairs `i ≤ j`, the
    off-diagonal pairs counted twice. -/
theorem sum_sym {n : ℕ} (f : Fin n → Fin n → ℤ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, (if i ≤ j then (if i = j then 1 else 2) * f i j else 0) = ∑ i, ∑ j, f i j := by
  have h1 : ∑ i, ∑ j, f i j =
      ∑ i, ∑ j, ((if i ≤ j then f i j else 0) + (if j < i then f i j else 0)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases le_or_gt i j with h | h
    · simp [h, not_lt.2 h]
    · simp [h, not_le.2 h]
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) =
      ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  rw [h1]
  simp only [Finset.sum_add_distrib]
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | h | h
  · simp [h, le_of_lt h, ne_of_lt h]; ring
  · subst h; simp
  · simp [not_le.2 h, not_lt.2 (le_of_lt h)]

/-! ## 2. Parameters and values -/

/-- An unsaturated Solinas representation: `n` limbs of width `b` for the prime
    `2^k - Σ c·2^e`, the pairs `(c, e)` listed in `cTerms`. -/
structure UnsatParams where
  /-- The number of limbs. -/
  n : ℕ
  /-- The limb width. -/
  b : ℕ
  /-- The exponent of the leading power. -/
  k : ℕ
  /-- The pairs `(c, e)` of the subtracted terms `c·2^e`. -/
  cTerms : List (ℕ × ℕ)

/-- The entry `i` of a limb vector, `0` when `i ≥ n`. -/
def getZ {n : ℕ} (f : Fin n → ℤ) (i : ℕ) : ℤ := if h : i < n then f ⟨i, h⟩ else 0

/-- Replace limb `i` by `v`. -/
def setAt {n : ℕ} (i : ℕ) (v : ℤ) (f : Fin n → ℤ) : Fin n → ℤ :=
  fun j => if (j : ℕ) = i then v else f j

/-- Add `d` to limb `i`; no change when `i ≥ n`. -/
def addAt {n : ℕ} (i : ℕ) (d : ℤ) (f : Fin n → ℤ) : Fin n → ℤ :=
  fun j => if (j : ℕ) = i then f j + d else f j

/-- The product `v · M`, written `v` when `M = 1`. -/
def mulC (M : ℕ) (v : ℤ) : ℤ := if M = 1 then v else v * M

theorem mulC_eq (M : ℕ) (v : ℤ) : mulC M v = v * M := by
  unfold mulC; split_ifs with h <;> simp [h]

/-- The low `b` bits of the natural part of `x`: the word semantics of `and` with the mask
    `2^b - 1`. -/
def lowZ (b : ℕ) (x : ℤ) : ℤ := ((x.toNat % 2 ^ b : ℕ) : ℤ)

theorem lowZ_nonneg (b : ℕ) (x : ℤ) : 0 ≤ lowZ b x := Int.natCast_nonneg _

theorem lowZ_add {b : ℕ} {x : ℤ} (hx : 0 ≤ x) : lowZ b x + 2 ^ b * (x / 2 ^ b) = x := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  simp only [lowZ, Int.toNat_natCast]
  push_cast
  exact Int.emod_add_mul_ediv _ _

namespace UnsatParams

variable (P : UnsatParams)

/-- The sum `Σ c·2^e` of the subtracted terms. -/
def cSum : ℤ := (P.cTerms.map fun ce => (ce.1 : ℤ) * 2 ^ ce.2).sum

/-- The prime `2^k - Σ c·2^e` as an integer. -/
def pZ : ℤ := 2 ^ P.k - P.cSum

/-- The prime as a natural number. -/
def p : ℕ := P.pZ.toNat

/-- The value `Σ f i · 2^(b·i)` of a limb vector. -/
def evalZ (f : Fin P.n → ℤ) : ℤ := ∑ i : Fin P.n, f i * 2 ^ (P.b * (i : ℕ))

theorem two_pow_k_modEq : (2 : ℤ) ^ P.k ≡ P.cSum [ZMOD P.pZ] :=
  Int.modEq_iff_dvd.2 ⟨-1, by unfold pZ; ring⟩

/-! ## 3. Reduction and placement of weights -/

/-- The value `Σ m · 2^W` of a list of (multiplier, weight) pairs. -/
def wsum (l : List (ℕ × ℕ)) : ℤ := (l.map fun mW => (mW.1 : ℤ) * 2 ^ mW.2).sum

/-- Reduce the term `m · 2^W`: a weight `W ≥ k` becomes the terms `m·c · 2^(W - k + e)`,
    reduced again, for at most `fuel` rounds. -/
def reduceW : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, m, W => [(m, W)]
  | f + 1, m, W =>
    if P.k ≤ W then P.cTerms.flatMap fun ce => reduceW f (m * ce.1) (W - P.k + ce.2)
    else [(m, W)]

theorem wsum_flatMap {α : Type} (l : List α) (g : α → List (ℕ × ℕ)) :
    wsum (l.flatMap g) = (l.map fun a => wsum (g a)).sum :=
  sum_map_flatMap l g _

/-- The reduction preserves the value modulo `pZ`. -/
theorem reduceW_cong (f m W : ℕ) : wsum (P.reduceW f m W) ≡ (m : ℤ) * 2 ^ W [ZMOD P.pZ] := by
  induction f generalizing m W with
  | zero => simp [reduceW, wsum]
  | succ f ih =>
    simp only [reduceW]
    split_ifs with h
    · rw [wsum_flatMap]
      have e : (m : ℤ) * 2 ^ W = m * 2 ^ (W - P.k) * 2 ^ P.k := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
      rw [e]
      refine (sum_modEq _ _ (fun ce => (m : ℤ) * 2 ^ (W - P.k) * ((ce.1 : ℤ) * 2 ^ ce.2))
        fun ce _ => ?_).trans ?_
      · have := ih (m * ce.1) (W - P.k + ce.2)
        rwa [show ((m * ce.1 : ℕ) : ℤ) * 2 ^ (W - P.k + ce.2)
          = (m : ℤ) * 2 ^ (W - P.k) * ((ce.1 : ℤ) * 2 ^ ce.2) by push_cast; rw [pow_add]; ring]
          at this
      · rw [List.sum_map_mul_left]
        exact (P.two_pow_k_modEq.symm).mul_left _
    · simp [wsum]

/-- The limb `⌊W/b⌋` and multiplier `m · 2^(W mod b)` of the term `m · 2^W`. -/
def place (mW : ℕ × ℕ) : ℕ × ℕ := (mW.2 / P.b, mW.1 * 2 ^ (mW.2 % P.b))

theorem place_val (mW : ℕ × ℕ) :
    ((P.place mW).2 : ℤ) * 2 ^ (P.b * (P.place mW).1) = mW.1 * 2 ^ mW.2 := by
  simp only [place]
  push_cast
  rw [mul_assoc, ← pow_add, Nat.mod_add_div]

/-! ## 4. Product terms and product limbs -/

/-- The placed terms `(i, j, limb, multiplier)` of the product `x · y`. -/
def mulTerms : List (Fin P.n × Fin P.n × ℕ × ℕ) :=
  (List.finRange P.n).flatMap fun (i : Fin P.n) =>
    (List.finRange P.n).flatMap fun (j : Fin P.n) =>
      (P.reduceW P.n 1 (P.b * ((i : ℕ) + (j : ℕ)))).map fun mW =>
        (i, j, (P.place mW).1, (P.place mW).2)

/-- The placed terms of the square `x · x`: the pairs `i ≤ j`, an off-diagonal pair with its
    multiplier doubled. -/
def sqTerms : List (Fin P.n × Fin P.n × ℕ × ℕ) :=
  (List.finRange P.n).flatMap fun (i : Fin P.n) =>
    ((List.finRange P.n).filter fun j => i ≤ j).flatMap fun (j : Fin P.n) =>
      (P.reduceW P.n 1 (P.b * ((i : ℕ) + (j : ℕ)))).map fun mW =>
        (i, j, (P.place mW).1, (if i = j then 1 else 2) * (P.place mW).2)

/-- The placed terms `(limb, multiplier)` of the carry out of the top limb, of weight
    `b·n`. -/
def wrapTerms : List (ℕ × ℕ) := (P.reduceW P.n 1 (P.b * P.n)).map P.place

/-- Every placed term of a product, a square and the top carry lands in a limb below `n`. -/
def Placed : Prop :=
  (∀ t ∈ P.mulTerms, t.2.2.1 < P.n) ∧ (∀ t ∈ P.sqTerms, t.2.2.1 < P.n) ∧
    ∀ t ∈ P.wrapTerms, t.1 < P.n

instance : Decidable P.Placed := by unfold Placed; infer_instance

end UnsatParams

/-- The terms `(i, j, multiplier)` of the placed terms `T` at limb `L`. -/
def tbl {n : ℕ} (T : List (Fin n × Fin n × ℕ × ℕ)) (L : Fin n) : List (Fin n × Fin n × ℕ) :=
  (T.filter fun t => t.2.2.1 = (L : ℕ)).map fun t => (t.1, t.2.1, t.2.2.2)

theorem tbl_cons {n : ℕ} (t : Fin n × Fin n × ℕ × ℕ) (T : List (Fin n × Fin n × ℕ × ℕ))
    (L : Fin n) : tbl (t :: T) L =
      if t.2.2.1 = (L : ℕ) then (t.1, t.2.1, t.2.2.2) :: tbl T L else tbl T L := by
  unfold tbl
  by_cases h : t.2.2.1 = (L : ℕ) <;> simp [h]

/-- The value `x_i · (y_j · M)` of the term `(i, j, M)`. -/
def termZ {n : ℕ} (x y : Fin n → ℤ) (t : Fin n × Fin n × ℕ) : ℤ := x t.1 * mulC t.2.2 (y t.2.1)

/-- The sum of the terms `ts` onto the accumulator `a`, each new term added on the left;
    `0` for no term and no accumulator. -/
def sumZ {n : ℕ} (x y : Fin n → ℤ) : List (Fin n × Fin n × ℕ) → Option ℤ → ℤ
  | [], none => 0
  | [], some a => a
  | t :: ts, none => sumZ x y ts (some (termZ x y t))
  | t :: ts, some a => sumZ x y ts (some (termZ x y t + a))

theorem sumZ_eq {n : ℕ} (x y : Fin n → ℤ) (ts : List (Fin n × Fin n × ℕ)) (a : Option ℤ) :
    sumZ x y ts a = a.getD 0 + (ts.map (termZ x y)).sum := by
  induction ts generalizing a with
  | nil => cases a <;> simp [sumZ]
  | cons t ts ih => cases a <;> simp [sumZ, ih]; ring

/-- The product limbs of the placed terms `T`: limb `L` is the sum of the terms at `L`. -/
def prodZ {n : ℕ} (T : List (Fin n × Fin n × ℕ × ℕ)) (x y : Fin n → ℤ) : Fin n → ℤ :=
  fun L => sumZ x y (tbl T L) none

namespace UnsatParams

variable (P : UnsatParams)

/-- The product limbs of `x · y`. -/
def mulZ (x y : Fin P.n → ℤ) : Fin P.n → ℤ := prodZ P.mulTerms x y

/-- The product limbs of `x · x`. -/
def squareZ (x : Fin P.n → ℤ) : Fin P.n → ℤ := prodZ P.sqTerms x x

/-- The value of product limbs is the weighted sum of their placed terms. -/
theorem evalZ_prodZ (T : List (Fin P.n × Fin P.n × ℕ × ℕ)) (hT : ∀ t ∈ T, t.2.2.1 < P.n)
    (x y : Fin P.n → ℤ) : P.evalZ (prodZ T x y) =
      (T.map fun t => x t.1 * (y t.2.1 * t.2.2.2) * 2 ^ (P.b * t.2.2.1)).sum := by
  unfold evalZ prodZ
  simp only [sumZ_eq, Option.getD_none, zero_add]
  induction T with
  | nil => simp [tbl]
  | cons t T ih =>
    have hT' : ∀ s ∈ T, s.2.2.1 < P.n := fun s hs => hT s (by simp [hs])
    have ht : t.2.2.1 < P.n := hT t (by simp)
    have e : ∀ L : Fin P.n, (((tbl (t :: T) L).map (termZ x y)).sum) * 2 ^ (P.b * (L : ℕ)) =
        (if (L : ℕ) = t.2.2.1 then termZ x y (t.1, t.2.1, t.2.2.2) * 2 ^ (P.b * (L : ℕ))
          else 0) + ((tbl T L).map (termZ x y)).sum * 2 ^ (P.b * (L : ℕ)) := by
      intro L
      rw [tbl_cons]
      by_cases h : t.2.2.1 = (L : ℕ)
      · simp [h]; ring
      · simp [h, Ne.symm h]
    simp only [e, Finset.sum_add_distrib, ih hT', sum_fin_ite _ ht, List.map_cons,
      List.sum_cons, termZ, mulC_eq]

/-- The weighted sum of the placed terms of a product of weight `W`. -/
theorem sum_place (xy : ℤ) (W : ℕ) :
    ((P.reduceW P.n 1 W).map fun mW =>
        xy * ((P.place mW).2 : ℤ) * 2 ^ (P.b * (P.place mW).1)).sum ≡
      xy * 2 ^ W [ZMOD P.pZ] := by
  have e : ((P.reduceW P.n 1 W).map fun mW =>
        xy * ((P.place mW).2 : ℤ) * 2 ^ (P.b * (P.place mW).1)).sum =
      xy * wsum (P.reduceW P.n 1 W) := by
    unfold wsum
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun mW _ => ?_
    rw [mul_assoc, place_val]
  rw [e]
  have := (P.reduceW_cong P.n 1 W).mul_left xy
  simpa using this

/-- The product limbs are congruent to the product of the values. -/
theorem mulZ_cong (hT : ∀ t ∈ P.mulTerms, t.2.2.1 < P.n) (x y : Fin P.n → ℤ) :
    P.evalZ (P.mulZ x y) ≡ P.evalZ x * P.evalZ y [ZMOD P.pZ] := by
  rw [mulZ, evalZ_prodZ P _ hT]
  have rhs : P.evalZ x * P.evalZ y = ((List.finRange P.n).map fun i =>
      ((List.finRange P.n).map fun j =>
        x i * y j * 2 ^ (P.b * ((i : ℕ) + (j : ℕ)))).sum).sum := by
    unfold evalZ
    rw [Finset.sum_mul_sum, Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [mul_add, pow_add]; ring
  rw [rhs, mulTerms, sum_map_flatMap]
  refine sum_modEq _ _ _ fun i _ => ?_
  rw [sum_map_flatMap]
  refine sum_modEq _ _ _ fun j _ => ?_
  rw [List.map_map]
  convert P.sum_place (x i * y j) (P.b * ((i : ℕ) + (j : ℕ))) using 3
  funext mW
  simp only [Function.comp]
  ring

/-- The square limbs are congruent to the square of the value. -/
theorem squareZ_cong (hT : ∀ t ∈ P.sqTerms, t.2.2.1 < P.n) (x : Fin P.n → ℤ) :
    P.evalZ (P.squareZ x) ≡ P.evalZ x * P.evalZ x [ZMOD P.pZ] := by
  rw [squareZ, evalZ_prodZ P _ hT]
  have rhs : P.evalZ x * P.evalZ x = ((List.finRange P.n).map fun i =>
      ((List.finRange P.n).map fun j => if i ≤ j then
        (if i = j then 1 else 2) * (x i * x j * 2 ^ (P.b * ((i : ℕ) + (j : ℕ))))
        else 0).sum).sum := by
    unfold evalZ
    rw [Finset.sum_mul_sum,
      ← sum_sym (fun i j => x i * 2 ^ (P.b * (i : ℕ)) * (x j * 2 ^ (P.b * (j : ℕ))))
        (fun i j => by ring), Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [mul_add, pow_add]; ring_nf
  rw [rhs, sqTerms, sum_map_flatMap]
  refine sum_modEq _ _ _ fun i _ => ?_
  rw [sum_map_flatMap, sum_map_filter]
  refine sum_modEq _ _ _ fun j _ => ?_
  by_cases hij : i ≤ j
  · simp only [hij, decide_true, ite_true, List.map_map]
    rw [← mul_assoc]
    convert P.sum_place ((if i = j then 1 else 2) * (x i * x j))
      (P.b * ((i : ℕ) + (j : ℕ))) using 3
    funext mW
    simp only [Function.comp]
    split_ifs <;> push_cast <;> ring
  · simp [hij]

/-! ## 5. Carries -/

/-- Add the multiples `M · h` of the top carry `h` at the limbs of the terms `ts`. -/
def wrapZ (h : ℤ) : List (ℕ × ℕ) → (Fin P.n → ℤ) → Fin P.n → ℤ
  | [], f => f
  | t :: ts, f => wrapZ h ts (addAt t.1 (mulC t.2 h) f)

/-- The carry at limb `i`: the low `b` bits stay at `i`, the rest, divided by `2^b`, is added
    to limb `i + 1`, or for the top limb placed by `wrapTerms`; no change when `i ≥ n`. -/
def carryZ (i : ℕ) (f : Fin P.n → ℤ) : Fin P.n → ℤ :=
  if i < P.n then
    if i + 1 < P.n then addAt (i + 1) (getZ f i / 2 ^ P.b) (setAt i (lowZ P.b (getZ f i)) f)
    else P.wrapZ (getZ f i / 2 ^ P.b) P.wrapTerms (setAt i (lowZ P.b (getZ f i)) f)
  else f

/-- The carries of the schedule `sched`, in order. -/
def carryChain : List ℕ → (Fin P.n → ℤ) → Fin P.n → ℤ
  | [], f => f
  | i :: is, f => carryChain is (P.carryZ i f)

theorem evalZ_setAt {i : ℕ} (h : i < P.n) (v : ℤ) (f : Fin P.n → ℤ) :
    P.evalZ (setAt i v f) = P.evalZ f + (v - getZ f i) * 2 ^ (P.b * i) := by
  unfold evalZ setAt
  have e : ∀ j : Fin P.n, (if (j : ℕ) = i then v else f j) * 2 ^ (P.b * (j : ℕ)) =
      f j * 2 ^ (P.b * (j : ℕ)) +
        (if (j : ℕ) = i then (v - f j) * 2 ^ (P.b * (j : ℕ)) else 0) := by
    intro j; split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, sum_fin_ite _ h, getZ, h, dite_true]

theorem evalZ_addAt {i : ℕ} (h : i < P.n) (d : ℤ) (f : Fin P.n → ℤ) :
    P.evalZ (addAt i d f) = P.evalZ f + d * 2 ^ (P.b * i) := by
  unfold evalZ addAt
  have e : ∀ j : Fin P.n, (if (j : ℕ) = i then f j + d else f j) * 2 ^ (P.b * (j : ℕ)) =
      f j * 2 ^ (P.b * (j : ℕ)) + (if (j : ℕ) = i then d * 2 ^ (P.b * (j : ℕ)) else 0) := by
    intro j; split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, sum_fin_ite _ h]

theorem evalZ_wrapZ (hd : ℤ) (ts : List (ℕ × ℕ)) (hts : ∀ t ∈ ts, t.1 < P.n)
    (f : Fin P.n → ℤ) : P.evalZ (P.wrapZ hd ts f) =
      P.evalZ f + hd * (ts.map fun t => (t.2 : ℤ) * 2 ^ (P.b * t.1)).sum := by
  induction ts generalizing f with
  | nil => simp [wrapZ]
  | cons t ts ih =>
    simp only [wrapZ]
    rw [ih (fun s hs => hts s (by simp [hs])), evalZ_addAt P (hts t (by simp)), mulC_eq]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The weighted sum of the placed top-carry terms is congruent to `2^(b·n)`. -/
theorem wrapTerms_cong :
    (P.wrapTerms.map fun t => (t.2 : ℤ) * 2 ^ (P.b * t.1)).sum ≡
      2 ^ (P.b * P.n) [ZMOD P.pZ] := by
  have := P.sum_place 1 (P.b * P.n)
  simp only [one_mul] at this
  unfold wrapTerms
  rw [List.map_map]
  exact this

/-- A carry preserves the value modulo `pZ` when the carried limb is nonnegative. -/
theorem carryZ_cong (hW : ∀ t ∈ P.wrapTerms, t.1 < P.n) (i : ℕ) (f : Fin P.n → ℤ)
    (hf : 0 ≤ getZ f i) : P.evalZ (P.carryZ i f) ≡ P.evalZ f [ZMOD P.pZ] := by
  have hl := lowZ_add (b := P.b) hf
  unfold carryZ
  split_ifs with h1 h2
  · rw [evalZ_addAt P h2, evalZ_setAt P h1]
    have : (lowZ P.b (getZ f i) - getZ f i) * 2 ^ (P.b * i) +
        getZ f i / 2 ^ P.b * 2 ^ (P.b * (i + 1)) = 0 := by
      rw [mul_add, mul_one, pow_add]
      linear_combination (2 : ℤ) ^ (P.b * i) * hl
    rw [add_assoc, this, add_zero]
  · rw [evalZ_wrapZ P _ _ hW, evalZ_setAt P h1]
    have hn : P.b * P.n = P.b * i + P.b := by
      rw [show P.n = i + 1 by omega, mul_add, mul_one]
    have e : P.evalZ f + (lowZ P.b (getZ f i) - getZ f i) * 2 ^ (P.b * i) +
        getZ f i / 2 ^ P.b * 2 ^ (P.b * P.n) = P.evalZ f := by
      rw [hn, pow_add]
      linear_combination (2 : ℤ) ^ (P.b * i) * hl
    calc P.evalZ f + (lowZ P.b (getZ f i) - getZ f i) * 2 ^ (P.b * i) +
          getZ f i / 2 ^ P.b * (P.wrapTerms.map fun t => (t.2 : ℤ) * 2 ^ (P.b * t.1)).sum
        ≡ P.evalZ f + (lowZ P.b (getZ f i) - getZ f i) * 2 ^ (P.b * i) +
          getZ f i / 2 ^ P.b * 2 ^ (P.b * P.n) [ZMOD P.pZ] :=
          Int.ModEq.add_left _ (P.wrapTerms_cong.mul_left _)
      _ = P.evalZ f := e
  · exact Int.ModEq.refl _

theorem getZ_nonneg {n : ℕ} {f : Fin n → ℤ} (hf : ∀ j, 0 ≤ f j) (i : ℕ) : 0 ≤ getZ f i := by
  unfold getZ; split_ifs
  · exact hf _
  · exact le_rfl

theorem wrapZ_nonneg {hd : ℤ} (hh : 0 ≤ hd) (ts : List (ℕ × ℕ)) {f : Fin P.n → ℤ}
    (hf : ∀ j, 0 ≤ f j) : ∀ j, 0 ≤ P.wrapZ hd ts f j := by
  induction ts generalizing f with
  | nil => exact hf
  | cons t ts ih =>
    refine ih fun j => ?_
    unfold addAt; split_ifs
    · rw [mulC_eq]; exact add_nonneg (hf j) (mul_nonneg hh (Int.natCast_nonneg _))
    · exact hf j

/-- A carry keeps nonnegative limbs nonnegative. -/
theorem carryZ_nonneg (i : ℕ) {f : Fin P.n → ℤ} (hf : ∀ j, 0 ≤ f j) :
    ∀ j, 0 ≤ P.carryZ i f j := by
  have hg := getZ_nonneg hf i
  have hq : 0 ≤ getZ f i / 2 ^ P.b := Int.ediv_nonneg hg (by positivity)
  have hs : ∀ j, 0 ≤ setAt i (lowZ P.b (getZ f i)) f j := fun j => by
    unfold setAt; split_ifs
    · exact lowZ_nonneg _ _
    · exact hf j
  unfold carryZ
  split_ifs
  · intro j; unfold addAt; split_ifs
    · exact add_nonneg (hs j) hq
    · exact hs j
  · exact P.wrapZ_nonneg hq _ hs
  · exact hf

/-- A schedule of carries preserves the value modulo `pZ` on nonnegative limbs. -/
theorem carryChain_cong (hW : ∀ t ∈ P.wrapTerms, t.1 < P.n) (sched : List ℕ)
    (f : Fin P.n → ℤ) (hf : ∀ j, 0 ≤ f j) :
    P.evalZ (P.carryChain sched f) ≡ P.evalZ f [ZMOD P.pZ] := by
  induction sched generalizing f with
  | nil => exact Int.ModEq.refl _
  | cons i is ih =>
    exact (ih _ (P.carryZ_nonneg i hf)).trans (P.carryZ_cong hW i f (getZ_nonneg hf i))

theorem prodZ_nonneg {n : ℕ} (T : List (Fin n × Fin n × ℕ × ℕ)) {x y : Fin n → ℤ}
    (hx : ∀ j, 0 ≤ x j) (hy : ∀ j, 0 ≤ y j) : ∀ L, 0 ≤ prodZ T x y L := by
  intro L
  unfold prodZ
  rw [sumZ_eq, Option.getD_none, zero_add]
  refine List.sum_nonneg fun a ha => ?_
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 ha
  unfold termZ; rw [mulC_eq]
  exact mul_nonneg (hx _) (mul_nonneg (hy _) (Int.natCast_nonneg _))

/-- The carried product is congruent to the product of the values. -/
theorem carryMulZ_cong (hP : P.Placed) (sched : List ℕ) (x y : Fin P.n → ℤ)
    (hx : ∀ j, 0 ≤ x j) (hy : ∀ j, 0 ≤ y j) :
    P.evalZ (P.carryChain sched (P.mulZ x y)) ≡ P.evalZ x * P.evalZ y [ZMOD P.pZ] :=
  (P.carryChain_cong hP.2.2 sched _ (prodZ_nonneg _ hx hy)).trans (P.mulZ_cong hP.1 x y)

/-- The carried square is congruent to the square of the value. -/
theorem carrySquareZ_cong (hP : P.Placed) (sched : List ℕ) (x : Fin P.n → ℤ)
    (hx : ∀ j, 0 ≤ x j) :
    P.evalZ (P.carryChain sched (P.squareZ x)) ≡ P.evalZ x * P.evalZ x [ZMOD P.pZ] :=
  (P.carryChain_cong hP.2.2 sched _ (prodZ_nonneg _ hx hx)).trans (P.squareZ_cong hP.2.1 x)

end UnsatParams

/-! ## 6. Curve25519 -/

/-- Curve25519 at five limbs of 51 bits: `p = 2^255 - 19`. -/
def curve25519Unsat : UnsatParams := ⟨5, 51, 255, [(19, 0)]⟩

/-- fiat-crypto's carry schedule of `curve25519` `carry_mul` and `carry_square`: limbs `0` to
    `4`, the top carry by `19` into limb `0`, then limbs `0` and `1`. -/
def curve25519Chain : List ℕ := [0, 1, 2, 3, 4, 0, 1]

theorem curve25519Unsat_pZ : curve25519Unsat.pZ = 2 ^ 255 - 19 := by
  simp [UnsatParams.pZ, UnsatParams.cSum, curve25519Unsat]

theorem curve25519Unsat_placed : curve25519Unsat.Placed := by decide

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatZ
