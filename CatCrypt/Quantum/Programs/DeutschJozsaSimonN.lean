/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.Qubit
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

set_option autoImplicit false

/-!
# Deutsch–Jozsa and Simon on `n` qubits

The register of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. The `n`-qubit
Hadamard transform has entries `H_n x y = (-1)^{x·y} / √2ⁿ`, the product of the
single-qubit Hadamard entries, and the character sum `∑ₓ (-1)^{x·y}` is `2ⁿ` for `y = 0`
and `0` otherwise.

Deutsch–Jozsa runs `(H_n ⊗ 1) U_f (H_n ⊗ H)` on `|0…0⟩|1⟩` for `f : {0,1}ⁿ → {0,1}` with
`U_f |x, b⟩ = |x, b ⊕ f x⟩`; Simon runs `(H_n ⊗ 1) U_f (H_n ⊗ 1)` on `|0…0⟩|0…0⟩` for
`f : {0,1}ⁿ → {0,1}ᵐ`. The outcome probability of `y` is the squared norm of the
amplitudes `(y, b)` summed over the second register.

## Main definitions

* `sgn a` — `(-1)^a` for `a : ZMod 2`.
* `hadamardN n` — the `n`-qubit Hadamard transform.
* `oracle f` — the standard oracle `|x, b⟩ ↦ |x, b + f x⟩`.
* `djState f`, `djProb f y` — the final Deutsch–Jozsa state and outcome probabilities.
* `simonState f`, `simonProb f y` — the same for Simon's algorithm.

## Main results

* `hadamardN_apply_eq_prod` — `H_n x y = ∏ᵢ H (x i) (y i)` (the tensor power of `H`).
* `sum_sgn_dotProduct` — the character sum `∑ₓ (-1)^{x·y} = if y = 0 then 2ⁿ else 0`.
* `hadamardN_mul_self` — `H_n H_n = 1`.
* `djProb_eq` — `P(y) = |∑ₓ (-1)^{f x + x·y}|² / 4ⁿ`.
* `deutschJozsa_constant` — for constant `f`, the outcome `0` has probability `1`.
* `deutschJozsa_balanced` — for balanced `f`, the outcome `0` has probability `0`.
* `simon_orthogonal_of_prob_ne_zero` — if `f (x + s) = f x` for all `x`, every outcome `y`
  of positive probability satisfies `y · s = 0`.

## References

* Deutsch, Jozsa, *Rapid solution of problems by quantum computation*, Proc. R. Soc. A 439
  (1992)
* Simon, *On the power of quantum computation*, SIAM J. Comput. 26 (1997)
-/

open Matrix

noncomputable section

namespace CatCrypt.Quantum.Programs.DeutschJozsaSimonN

/-- `n`-bit strings. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The sign `(-1)^a` of a bit. -/
def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_one : sgn 1 = -1 := by simp [sgn]

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp [sgn_zero, sgn_one, zmod2_one_add_one]

theorem sgn_mul_self (a : ZMod 2) : sgn a * sgn a = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp [sgn_zero, sgn_one]

theorem sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (g : ZMod 2 → M) :
    ∑ b : ZMod 2, g b = g 0 + g 1 := Fin.sum_univ_two g

/-- `∑_b (-1)^{b a} = 2` if `a = 0` and `0` otherwise. -/
theorem sum_sgn_mul (a : ZMod 2) : ∑ b : ZMod 2, sgn (b * a) = if a = 0 then 2 else 0 := by
  rw [sum_zmod2]
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · simp [sgn_zero]; norm_num
  · simp [sgn_zero, sgn_one]

variable {n m : ℕ}

/-- **Character sum**: `∑ₓ (-1)^{x·y} = 2ⁿ` if `y = 0` and `0` otherwise. -/
theorem sum_sgn_dotProduct (y : Bits n) :
    ∑ x : Bits n, sgn (x ⬝ᵥ y) = if y = 0 then 2 ^ n else 0 := by
  simp only [dotProduct, sgn_sum]
  rw [← Fintype.prod_sum (fun i b => sgn (b * y i))]
  simp only [sum_sgn_mul]
  split_ifs with hy
  · simp [hy]
  · obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h; push Not at h; exact hy (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The `n`-qubit Hadamard transform `H_n x y = (-1)^{x·y} / √2ⁿ`. -/
def hadamardN (n : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun x y => sgn (x ⬝ᵥ y) / (Real.sqrt 2 : ℂ) ^ n

theorem hadamardN_apply (x y : Bits n) :
    hadamardN n x y = sgn (x ⬝ᵥ y) / (Real.sqrt 2 : ℂ) ^ n := rfl

/-- The single-qubit Hadamard entry is `(-1)^{a b} / √2`. -/
theorem hadamard_apply_eq (a b : ZMod 2) :
    Qubit.hadamard a b = sgn (a * b) / (Real.sqrt 2 : ℂ) := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp [Qubit.hadamard, sgn_zero, sgn_one, div_eq_mul_inv] <;> rfl

/-- The `n`-qubit Hadamard transform is the `n`-fold tensor power of `H`. -/
theorem hadamardN_apply_eq_prod (x y : Bits n) :
    hadamardN n x y = ∏ i, Qubit.hadamard (x i) (y i) := by
  rw [Finset.prod_congr rfl (fun i _ => hadamard_apply_eq (x i) (y i)),
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    hadamardN_apply, dotProduct, sgn_sum]

theorem sqrt2_pow_sq (n : ℕ) : ((Real.sqrt 2 : ℂ) ^ n) * ((Real.sqrt 2 : ℂ) ^ n) = 2 ^ n := by
  rw [← mul_pow, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem sqrt2_pow_ne_zero (n : ℕ) : (Real.sqrt 2 : ℂ) ^ n ≠ 0 :=
  pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by positivity))

/-- `H_n` is an involution (in particular unitary, being Hermitian). -/
theorem hadamardN_mul_self : hadamardN n * hadamardN n = 1 := by
  ext x z
  simp only [Matrix.mul_apply, hadamardN_apply, Matrix.one_apply]
  have h : ∀ y : Bits n, sgn (x ⬝ᵥ y) / (Real.sqrt 2 : ℂ) ^ n * (sgn (y ⬝ᵥ z) /
      (Real.sqrt 2 : ℂ) ^ n) = sgn (y ⬝ᵥ (x + z)) / 2 ^ n := by
    intro y
    rw [div_mul_div_comm, sqrt2_pow_sq, ← sgn_add, dotProduct_comm x y, ← dotProduct_add]
  simp only [h, ← Finset.sum_div, sum_sgn_dotProduct]
  have hxz : x + z = 0 ↔ x = z := by
    rw [add_eq_zero_iff_eq_neg, show -z = z from funext fun i => ZMod.neg_eq_self_mod_two (z i)]
  by_cases hx : x = z
  · rw [ite_eq_left (hxz.mpr hx), ite_eq_left hx, div_self (pow_ne_zero _ two_ne_zero)]
  · rw [ite_eq_right (mt hxz.mp hx), ite_eq_right hx, zero_div]

/-! ## Deutsch–Jozsa -/

/-- The standard oracle `U_f |x, b⟩ = |x, b + f x⟩`. -/
def oracle {β : Type} [AddCommGroup β] [DecidableEq β] (f : Bits n → β) :
    Matrix (Bits n × β) (Bits n × β) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = q.2 + f q.1 then 1 else 0

/-- The basis state `|a⟩`. -/
def basisKet {α : Type*} [DecidableEq α] (a : α) : α → ℂ := fun p => if p = a then 1 else 0

theorem oracle_mulVec {β : Type} [AddCommGroup β] [DecidableEq β] [Fintype β]
    (f : Bits n → β) (v : Bits n × β → ℂ) (x : Bits n) (c : β) :
    (oracle f *ᵥ v) (x, c) = v (x, c - f x) := by
  simp only [mulVec, dotProduct, oracle, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single (c - f x)]
    · simp
    · intro b _ hb
      exact ite_eq_right (by rintro ⟨-, h⟩; exact hb (by rw [h]; abel))
    · simp
  · intro x' _ hx
    exact Finset.sum_eq_zero fun b _ => ite_eq_right (by rintro ⟨h, -⟩; exact hx h.symm)
  · simp

theorem kronecker_mulVec_apply {α β : Type} [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) (v : α × β → ℂ) (i : α) (k : β) :
    (kronecker A B *ᵥ v) (i, k) = ∑ j, ∑ l, A i j * B k l * v (j, l) := by
  simp [mulVec, dotProduct, kronecker, kroneckerMap_apply, Fintype.sum_prod_type]

theorem kronecker_mulVec_basisKet {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) (a : α) (b : β) (i : α) (k : β) :
    (kronecker A B *ᵥ basisKet (a, b)) (i, k) = A i a * B k b := by
  rw [kronecker_mulVec_apply]
  simp [basisKet, Prod.mk.injEq, ite_and]

theorem kronecker_one_mulVec_apply {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℂ) (v : α × β → ℂ) (i : α) (k : β) :
    (kronecker A (1 : Matrix β β ℂ) *ᵥ v) (i, k) = ∑ j, A i j * v (j, k) := by
  rw [kronecker_mulVec_apply]
  simp [Matrix.one_apply]

theorem sgn_sub (a b : ZMod 2) : sgn (a - b) = sgn a * sgn b := by
  rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, sgn_add]

/-- The final Deutsch–Jozsa state `(H_n ⊗ 1) U_f (H_n ⊗ H) |0…0⟩|1⟩`. -/
def djState (f : Bits n → ZMod 2) : Bits n × ZMod 2 → ℂ :=
  (kronecker (hadamardN n) (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) *ᵥ
    (oracle f *ᵥ ((kronecker (hadamardN n) (Matrix.of fun a b : ZMod 2 =>
      sgn (a * b) / (Real.sqrt 2 : ℂ))) *ᵥ basisKet ((0 : Bits n), (1 : ZMod 2))))

/-- The probability of reading `y` on the first `n` qubits. -/
def djProb (f : Bits n → ZMod 2) (y : Bits n) : ℝ :=
  ∑ b : ZMod 2, ‖djState f (y, b)‖ ^ 2

/-- The amplitudes of the final Deutsch–Jozsa state. -/
theorem djState_apply (f : Bits n → ZMod 2) (y : Bits n) (b : ZMod 2) :
    djState f (y, b) = sgn b / (Real.sqrt 2 : ℂ) * ((∑ x : Bits n, sgn (f x + x ⬝ᵥ y)) /
      2 ^ n) := by
  simp only [djState, kronecker_one_mulVec_apply, oracle_mulVec, kronecker_mulVec_basisKet,
    hadamardN_apply, Matrix.of_apply, dotProduct_zero, sgn_zero, mul_one, sgn_sub, sgn_add,
    dotProduct_comm _ (y : Bits n)]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sqrt2_pow_sq n]
  field_simp [sqrt2_pow_ne_zero n]

/-- **Deutsch–Jozsa outcome distribution**: `P(y) = |∑ₓ (-1)^{f x + x·y}|² / 4ⁿ`. -/
theorem djProb_eq (f : Bits n → ZMod 2) (y : Bits n) :
    djProb f y = ‖∑ x : Bits n, sgn (f x + x ⬝ᵥ y)‖ ^ 2 / 4 ^ n := by
  have hs : ∀ b : ZMod 2, ‖sgn b‖ = 1 := fun b => by
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp [sgn_zero, sgn_one]
  simp only [djProb, djState_apply, norm_mul, norm_div, hs, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), Complex.norm_ofNat, sum_zmod2]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [show (4 : ℝ) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  ring_nf
  rw [h2]
  ring

/-- `f` is constant. -/
def IsConstant (f : Bits n → ZMod 2) : Prop := ∃ c, ∀ x, f x = c

/-- `f` is balanced: as many inputs map to `0` as to `1`. -/
def IsBalanced (f : Bits n → ZMod 2) : Prop :=
  (Finset.univ.filter fun x => f x = 0).card = (Finset.univ.filter fun x => f x = 1).card

/-- **Deutsch–Jozsa, constant case**: the outcome `0` has probability `1`. -/
theorem deutschJozsa_constant (f : Bits n → ZMod 2) (hf : IsConstant f) : djProb f 0 = 1 := by
  obtain ⟨c, hc⟩ := hf
  rw [djProb_eq]
  simp only [hc, dotProduct_zero, add_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
  have hs : ‖sgn c‖ = 1 := by unfold sgn; split_ifs <;> simp
  rw [norm_mul, hs, mul_one, Complex.norm_natCast]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **Deutsch–Jozsa, balanced case**: the outcome `0` has probability `0`. -/
theorem deutschJozsa_balanced (f : Bits n → ZMod 2) (hf : IsBalanced f) : djProb f 0 = 0 := by
  rw [djProb_eq]
  simp only [dotProduct_zero, add_zero]
  have hsum : ∑ x : Bits n, sgn (f x) = 0 := by
    have h1 : ∀ x, sgn (f x) = if f x = 0 then 1 else -1 := fun x => rfl
    simp only [h1, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
    have h2 : (Finset.univ.filter fun x => ¬ f x = 0) =
        Finset.univ.filter fun x => f x = 1 := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases zmod2_eq_zero_or_one (f x) with h | h <;> simp [h]
    rw [h2, hf]; ring
  simp [hsum]

/-! ## Simon -/

/-- The state of Simon's circuit `(H_n ⊗ 1) U_f (H_n ⊗ 1) |0…0⟩|0…0⟩` before measurement. -/
def simonState (f : Bits n → Bits m) : Bits n × Bits m → ℂ :=
  (kronecker (hadamardN n) (1 : Matrix (Bits m) (Bits m) ℂ)) *ᵥ
    (oracle f *ᵥ ((kronecker (hadamardN n) (1 : Matrix (Bits m) (Bits m) ℂ)) *ᵥ
      basisKet ((0 : Bits n), (0 : Bits m))))

/-- The probability of reading `y` on the first register. -/
def simonProb (f : Bits n → Bits m) (y : Bits n) : ℝ :=
  ∑ z : Bits m, ‖simonState f (y, z)‖ ^ 2

/-- The amplitudes of Simon's state: `⟨y, z| ψ⟩ = ∑_{f x = z} (-1)^{x·y} / 2ⁿ`. -/
theorem simonState_apply (f : Bits n → Bits m) (y : Bits n) (z : Bits m) :
    simonState f (y, z) = (∑ x : Bits n, if f x = z then sgn (x ⬝ᵥ y) else 0) / 2 ^ n := by
  simp only [simonState, kronecker_one_mulVec_apply, oracle_mulVec, kronecker_mulVec_basisKet,
    hadamardN_apply, Matrix.one_apply, dotProduct_zero, sgn_zero, sub_eq_zero,
    dotProduct_comm (y : Bits n)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (f x) z with h | h
  · subst h
    simp only [↓reduceIte, mul_one]
    rw [← sqrt2_pow_sq n]
    field_simp [sqrt2_pow_ne_zero n]
  · simp [h, Ne.symm h]

/-- The fibre sums vanish off the annihilator of a period `s`. -/
theorem sum_fibre_sgn_eq_zero (f : Bits n → Bits m) (s : Bits n)
    (hs : ∀ x, f (x + s) = f x) (y : Bits n) (hy : s ⬝ᵥ y ≠ 0) (z : Bits m) :
    (∑ x : Bits n, if f x = z then sgn (x ⬝ᵥ y) else 0) = 0 := by
  set T := ∑ x : Bits n, if f x = z then sgn (x ⬝ᵥ y) else 0
  have hsy : sgn (s ⬝ᵥ y) = -1 := by
    rcases zmod2_eq_zero_or_one (s ⬝ᵥ y) with h | h
    · exact absurd h hy
    · rw [h, sgn_one]
  have hT : T = -T := by
    calc T = ∑ x : Bits n, if f (x + s) = z then sgn ((x + s) ⬝ᵥ y) else 0 :=
          (Fintype.sum_equiv (Equiv.addRight s) _ _ fun _ => rfl).symm
      _ = ∑ x : Bits n, -(if f x = z then sgn (x ⬝ᵥ y) else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hs, add_dotProduct, sgn_add, hsy]
          split_ifs <;> ring
      _ = -T := Finset.sum_neg_distrib _
  linear_combination hT / 2

/-- **Simon's algorithm, one run**: if `f (x + s) = f x` for every `x`, then every outcome
`y` of positive probability satisfies `y · s = 0`. -/
theorem simon_orthogonal_of_prob_ne_zero (f : Bits n → Bits m) (s : Bits n)
    (hs : ∀ x, f (x + s) = f x) (y : Bits n) (hy : simonProb f y ≠ 0) : y ⬝ᵥ s = 0 := by
  by_contra h
  apply hy
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [simonState_apply, sum_fibre_sgn_eq_zero f s hs y (by rwa [dotProduct_comm]) z]
  simp

end CatCrypt.Quantum.Programs.DeutschJozsaSimonN
