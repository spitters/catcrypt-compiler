/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Every unitary is a product of two-level unitaries

A two-level unitary on a finite index set `ι` acts as a `2 × 2` unitary `B` on the span of two
distinct basis vectors `|i⟩`, `|j⟩` and as the identity on the other basis vectors
(`twoLevel i j B`). Every unitary on `ι` with at least two elements is a product of two-level
unitaries (Nielsen, Chuang, *Quantum Computation and Quantum Information*, Section 4.5.1).

The proof eliminates columns. For a unit vector `v` and an index `i`, a Givens rotation on
`|i⟩, |j⟩` with `v j ≠ 0` sets the `j` entry to `0` and leaves the others outside `{i, j}`;
after at most `|ι| - 1` of them and one phase on `|i⟩, |j⟩`, `v` is mapped to `|i⟩`, by
two-level unitaries that fix every `|k⟩` with `k ≠ i` and `v k = 0`. Applied to a column `l`
of a unitary `U` that is not `|l⟩`, this fixes column `l` and keeps every column that already
was a basis vector (unitarity makes `U l' l = 0` for those), so the number of columns that are
not basis vectors decreases.

## Main definitions

* `twoLevel i j B` — the two-level matrix acting as `B` on `|i⟩, |j⟩`.
* `IsTwoLevelUnitary V` — `V = twoLevel i j B` for distinct `i`, `j` and a unitary `B`.

## Main results

* `twoLevel_mul`, `twoLevel_conjTranspose`, `twoLevel_mem_unitaryGroup` — the algebra of
  two-level matrices on one pair.
* `exists_twoLevel_mulVec_eq_single` — a unit vector is mapped to `|i⟩` by a product of
  two-level unitaries fixing the basis vectors outside its support.
* `unitary_eq_prod_twoLevel` — **every unitary is a product of two-level unitaries**
  (`exists_twoLevel_prod_eq`, by induction on the columns that are not basis vectors).
* `qubit_unitary_eq_prod_twoLevel` — the same on `n ≥ 1` qubits.
-/

@[expose] public section

set_option autoImplicit false

open Matrix

noncomputable section

namespace CatCrypt.Quantum.TwoLevelUniversality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The position of `k` in the pair `(i, j)`: `0` for `i`, `1` otherwise. -/
def idx (i k : ι) : Fin 2 := if k = i then 0 else 1

/-- The two-level matrix acting as `B` on the basis vectors `|i⟩, |j⟩` and as the identity on
the others. -/
def twoLevel (i j : ι) (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun k l =>
    if (k = i ∨ k = j) ∧ (l = i ∨ l = j) then B (idx i k) (idx i l) else if k = l then 1 else 0

/-- A two-level unitary. -/
def IsTwoLevelUnitary (V : Matrix ι ι ℂ) : Prop :=
  ∃ i j : ι, i ≠ j ∧ ∃ B ∈ unitaryGroup (Fin 2) ℂ, V = twoLevel i j B

/-- The basis vector `|i⟩`. -/
def ket (i : ι) : ι → ℂ := Pi.single i 1

/-! ## The algebra of two-level matrices -/

theorem twoLevel_mulVec {i j : ι} (hij : i ≠ j) (B : Matrix (Fin 2) (Fin 2) ℂ) (v : ι → ℂ)
    (k : ι) : (twoLevel i j B *ᵥ v) k =
      if k = i then B 0 0 * v i + B 0 1 * v j
      else if k = j then B 1 0 * v i + B 1 1 * v j else v k := by
  have hji : j ≠ i := Ne.symm hij
  simp only [mulVec, dotProduct, twoLevel, of_apply]
  by_cases hki : k = i
  · subst hki
    rw [Fintype.sum_eq_add k j hij fun m hm => by simp [hm.1, hm.2, Ne.symm hm.1]]
    simp [idx, hji]
  · by_cases hkj : k = j
    · subst hkj
      rw [Fintype.sum_eq_add i k hij fun m hm => by simp [hm.1, hm.2, Ne.symm hm.2]]
      simp [idx, hji]
    · simp [hki, hkj]

theorem twoLevel_mul {i j : ι} (hij : i ≠ j) (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel i j B * twoLevel i j C = twoLevel i j (B * C) := by
  have hji : j ≠ i := Ne.symm hij
  ext k l
  rw [show (twoLevel i j B * twoLevel i j C) k l = (twoLevel i j B *ᵥ fun m => twoLevel i j C m l) k
    from rfl, twoLevel_mulVec hij]
  by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [twoLevel, idx, Matrix.mul_apply, Fin.sum_univ_two, eq_comm (a := i) (b := l),
      eq_comm (a := j) (b := l)]

omit [Fintype ι] in
theorem twoLevel_one (i j : ι) : twoLevel i j 1 = 1 := by
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [twoLevel, idx, Matrix.one_apply]

omit [Fintype ι] in
theorem twoLevel_conjTranspose (i j : ι) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (twoLevel i j B)ᴴ = twoLevel i j Bᴴ := by
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [twoLevel, idx, conjTranspose_apply, eq_comm]

theorem twoLevel_mem_unitaryGroup {i j : ι} (hij : i ≠ j) {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : B ∈ unitaryGroup (Fin 2) ℂ) : twoLevel i j B ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, twoLevel_conjTranspose, twoLevel_mul hij,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hB, twoLevel_one]

/-! ## Givens rotations and phases -/

/-- `√(|a|² + |b|²)` as a complex number. -/
def pairNorm (a b : ℂ) : ℂ := ((Real.sqrt (Complex.normSq a + Complex.normSq b) : ℝ) : ℂ)

theorem pairNorm_sq (a b : ℂ) :
    pairNorm a b ^ 2 = starRingEnd ℂ a * a + starRingEnd ℂ b * b := by
  rw [pairNorm, ← Complex.ofReal_pow,
    Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]

theorem pairNorm_ne_zero {a b : ℂ} (hb : b ≠ 0) : pairNorm a b ≠ 0 := by
  have h : 0 < Complex.normSq a + Complex.normSq b :=
    add_pos_of_nonneg_of_pos (Complex.normSq_nonneg a) (Complex.normSq_pos.mpr hb)
  rw [pairNorm, Complex.ofReal_ne_zero]
  exact (Real.sqrt_pos.mpr h).ne'

theorem star_pairNorm (a b : ℂ) : starRingEnd ℂ (pairNorm a b) = pairNorm a b :=
  Complex.conj_ofReal _

/-- The Givens rotation mapping `(a, b)` to `(√(|a|² + |b|²), 0)`. -/
def givens (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![starRingEnd ℂ a / pairNorm a b, starRingEnd ℂ b / pairNorm a b;
    -b / pairNorm a b, a / pairNorm a b]

theorem givens_mem_unitaryGroup {a b : ℂ} (hb : b ≠ 0) : givens a b ∈ unitaryGroup (Fin 2) ℂ := by
  have hr := pairNorm_ne_zero (a := a) hb
  have h2 := pairNorm_sq a b
  rw [mem_unitaryGroup_iff]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [givens, Matrix.mul_apply, Fin.sum_univ_two, star_pairNorm] <;> field_simp <;>
    first | ring1 | linear_combination h2 | linear_combination -h2

/-- The phase `diag(conj λ, 1)`. -/
def phaseFix (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![starRingEnd ℂ c, 0; 0, 1]

theorem phaseFix_mem_unitaryGroup {c : ℂ} (hc : star c * c = 1) :
    phaseFix c ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [phaseFix, Matrix.mul_apply, Fin.sum_univ_two]
  exact hc

/-! ## Mapping a unit vector to a basis vector -/

omit [Fintype ι] in
theorem ket_apply (i k : ι) : ket i k = if k = i then 1 else 0 := by
  simp [ket, Pi.single_apply]

theorem twoLevel_mulVec_ket {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : twoLevel i j B *ᵥ ket k = ket k := by
  funext m
  rw [twoLevel_mulVec hij]
  by_cases hmi : m = i
  · subst hmi; simp [ket_apply, Ne.symm hki, Ne.symm hkj]
  · by_cases hmj : m = j
    · subst hmj; simp [ket_apply, Ne.symm hki, Ne.symm hkj, hmi]
    · simp [hmi, hmj]

omit [DecidableEq ι] in
theorem sum_eq_of_pair {f g : ι → ℝ} {i j : ι} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = g k) (hp : f i + f j = g i + g j) :
    ∑ k, f k = ∑ k, g k := by
  have := Fintype.sum_eq_add i j hij (f := fun k => f k - g k)
    (fun k hk => by simp [h k hk.1 hk.2])
  rw [Finset.sum_sub_distrib] at this
  linarith

theorem normSq_pairNorm (a b : ℂ) :
    Complex.normSq (pairNorm a b) = Complex.normSq a + Complex.normSq b := by
  rw [pairNorm, Complex.normSq_ofReal,
    Real.mul_self_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

theorem twoLevel_givens_mulVec {i j : ι} (hij : i ≠ j) (v : ι → ℂ) (hv : v j ≠ 0) (k : ι) :
    (twoLevel i j (givens (v i) (v j)) *ᵥ v) k =
      if k = i then pairNorm (v i) (v j) else if k = j then 0 else v k := by
  have hr := pairNorm_ne_zero (a := v i) hv
  have h2 := pairNorm_sq (v i) (v j)
  rw [twoLevel_mulVec hij]
  by_cases hki : k = i
  · subst hki
    simp only [ite_true, givens, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
      cons_val_one]
    field_simp
    linear_combination -h2
  · by_cases hkj : k = j
    · subst hkj
      simp only [hki, ite_false, ite_true, givens, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one, cons_val_one]
      field_simp
      ring
    · simp [hki, hkj]

/-- **Elimination.** A unit vector `v` is mapped to `|i⟩` by a product of two-level unitaries
that fixes every `|k⟩` with `k ≠ i` and `v k = 0`. -/
theorem exists_twoLevel_mulVec_eq_ket [Nontrivial ι] (i : ι) :
    ∀ (m : ℕ) (v : ι → ℂ), (Finset.univ.filter fun k => k ≠ i ∧ v k ≠ 0).card = m →
      ∑ k, Complex.normSq (v k) = 1 →
      ∃ L : List (Matrix ι ι ℂ), (∀ V ∈ L, IsTwoLevelUnitary V) ∧ L.prod *ᵥ v = ket i ∧
        ∀ k, k ≠ i → v k = 0 → L.prod *ᵥ ket k = ket k := by
  intro m
  induction m with
  | zero =>
    intro v hcard hnorm
    have hz : ∀ k, k ≠ i → v k = 0 := by
      intro k hk
      by_contra hv
      have hmem : k ∈ Finset.univ.filter fun k => k ≠ i ∧ v k ≠ 0 := by simp [hk, hv]
      rw [Finset.card_eq_zero] at hcard
      simp [hcard] at hmem
    obtain ⟨j, hji⟩ := exists_ne i
    have hij : i ≠ j := Ne.symm hji
    have hvi : starRingEnd ℂ (v i) * v i = 1 := by
      have hs : ∑ k, Complex.normSq (v k) = Complex.normSq (v i) :=
        Fintype.sum_eq_single i fun k hk => by simp [hz k hk]
      rw [hs] at hnorm
      rw [← Complex.normSq_eq_conj_mul_self, hnorm, Complex.ofReal_one]
    refine ⟨[twoLevel i j (phaseFix (v i))], ?_, ?_, ?_⟩
    · intro V hV
      rw [List.mem_singleton] at hV
      exact ⟨i, j, hij, _, phaseFix_mem_unitaryGroup hvi, hV⟩
    · rw [List.prod_singleton]
      funext k
      rw [twoLevel_mulVec hij]
      by_cases hki : k = i
      · subst hki; simp [phaseFix, ket_apply, hvi, hz j hji]
      · by_cases hkj : k = j
        · subst hkj; simp [phaseFix, ket_apply, hki, hz k hki]
        · simp [ket_apply, hki, hkj, hz k hki]
    · intro k hki _
      rw [List.prod_singleton]
      by_cases hkj : k = j
      · subst hkj
        funext l
        rw [twoLevel_mulVec hij]
        by_cases hli : l = i
        · subst hli; simp [phaseFix, ket_apply, hij]
        · by_cases hlj : l = k
          · subst hlj; simp [phaseFix, ket_apply, hij, hli]
          · simp [hli, hlj]
      · exact twoLevel_mulVec_ket hij hki hkj _
  | succ m ih =>
    intro v hcard hnorm
    obtain ⟨j, hj⟩ : ∃ j, j ≠ i ∧ v j ≠ 0 := by
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter
        fun k => k ≠ i ∧ v k ≠ 0).card)
      exact ⟨j, (Finset.mem_filter.mp hj).2⟩
    have hij : i ≠ j := Ne.symm hj.1
    have hv' := twoLevel_givens_mulVec hij v hj.2
    set G := twoLevel i j (givens (v i) (v j))
    have hfilt : (Finset.univ.filter fun k => k ≠ i ∧ (G *ᵥ v) k ≠ 0)
        = (Finset.univ.filter fun k => k ≠ i ∧ v k ≠ 0).erase j := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hv' k]
      by_cases hki : k = i
      · simp [hki]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    have hcard' : (Finset.univ.filter fun k => k ≠ i ∧ (G *ᵥ v) k ≠ 0).card = m := by
      rw [hfilt, Finset.card_erase_of_mem (by simp [hj.1, hj.2]), hcard]
      rfl
    have hnorm' : ∑ k, Complex.normSq ((G *ᵥ v) k) = 1 := by
      rw [← hnorm]
      refine sum_eq_of_pair hij (fun k hki hkj => by simp [hv' k, hki, hkj]) ?_
      simp [hv' i, hv' j, hij.symm, normSq_pairNorm]
    obtain ⟨L', hL', hL'v, hL'k⟩ := ih (G *ᵥ v) hcard' hnorm'
    refine ⟨L' ++ [G], ?_, ?_, ?_⟩
    · intro V hV
      rcases List.mem_append.mp hV with hV | hV
      · exact hL' V hV
      · rw [List.mem_singleton] at hV
        exact ⟨i, j, hij, _, givens_mem_unitaryGroup hj.2, hV⟩
    · rw [List.prod_append, List.prod_singleton, ← mulVec_mulVec]
      exact hL'v
    · intro k hki hvk
      have hkj : k ≠ j := fun h => hj.2 (h ▸ hvk)
      rw [List.prod_append, List.prod_singleton, ← mulVec_mulVec, twoLevel_mulVec_ket hij hki hkj]
      exact hL'k k hki (by rw [hv' k]; simp [hki, hkj, hvk])

/-! ## Every unitary is a product of two-level unitaries -/

theorem IsTwoLevelUnitary.mem_unitaryGroup {V : Matrix ι ι ℂ} (hV : IsTwoLevelUnitary V) :
    V ∈ unitaryGroup ι ℂ := by
  obtain ⟨i, j, hij, B, hB, rfl⟩ := hV
  exact twoLevel_mem_unitaryGroup hij hB

omit [Fintype ι] in
theorem IsTwoLevelUnitary.conjTranspose {V : Matrix ι ι ℂ} (hV : IsTwoLevelUnitary V) :
    IsTwoLevelUnitary Vᴴ := by
  obtain ⟨i, j, hij, B, hB, rfl⟩ := hV
  refine ⟨i, j, hij, Bᴴ, ?_, twoLevel_conjTranspose i j B⟩
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← star_eq_conjTranspose]
  exact mem_unitaryGroup_iff'.mp hB

theorem list_prod_mem_unitaryGroup :
    ∀ L : List (Matrix ι ι ℂ), (∀ V ∈ L, IsTwoLevelUnitary V) → L.prod ∈ unitaryGroup ι ℂ
  | [], _ => one_mem _
  | V :: L, h => by
    rw [List.prod_cons]
    exact mul_mem (h V List.mem_cons_self).mem_unitaryGroup
      (list_prod_mem_unitaryGroup L fun W hW => h W (List.mem_cons_of_mem V hW))

/-- The set of columns of `U` that are not basis vectors. -/
def badCols (U : Matrix ι ι ℂ) : Finset ι := Finset.univ.filter fun l => (fun k => U k l) ≠ ket l

/-- **Nielsen–Chuang 4.5.1.** On an index set with at least two elements, every unitary is a
product of two-level unitaries. -/
theorem exists_twoLevel_prod_eq [Nontrivial ι] :
    ∀ (m : ℕ) (U : Matrix ι ι ℂ), U ∈ unitaryGroup ι ℂ → (badCols U).card = m →
      ∃ L : List (Matrix ι ι ℂ), (∀ V ∈ L, IsTwoLevelUnitary V) ∧ L.prod = U := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro U hU hcard
  have hUU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff'.mp hU)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · refine ⟨[], by simp, ?_⟩
    rw [List.prod_nil]
    subst hm
    rw [Finset.card_eq_zero] at hcard
    ext k l
    have hl : (fun k => U k l) = ket l := by
      by_contra h
      have hmem : l ∈ badCols U := by simp [badCols, h]
      simp [hcard] at hmem
    have := congrFun hl k
    rw [this, ket_apply, Matrix.one_apply, eq_comm]
  · obtain ⟨l, hl⟩ := Finset.card_pos.mp (hcard ▸ hm : 0 < (badCols U).card)
    have hnorm : ∑ k, Complex.normSq (U k l) = 1 := by
      have h := congrFun (congrFun hUU l) l
      simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq] at h
      have h' : ((∑ k, Complex.normSq (U k l) : ℝ) : ℂ) = 1 := by
        push_cast
        simpa [Complex.normSq_eq_conj_mul_self] using h
      exact_mod_cast h'
    obtain ⟨L, hL, hLv, hLk⟩ := exists_twoLevel_mulVec_eq_ket l _ (fun k => U k l) rfl hnorm
    have hW : L.prod ∈ unitaryGroup ι ℂ := list_prod_mem_unitaryGroup L hL
    have hWW : (L.prod)ᴴ * L.prod = 1 := by
      rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hW
    have hcol : ∀ l', (fun k => (L.prod * U) k l') = L.prod *ᵥ fun k => U k l' := fun _ => rfl
    have hsub : badCols (L.prod * U) ⊆ (badCols U).erase l := by
      intro l' hl'
      rw [Finset.mem_erase]
      by_contra hcon
      simp only [badCols, Finset.mem_filter, Finset.mem_univ, true_and] at hl'
      apply hl'
      by_cases hll : l' = l
      · subst hll; rw [hcol]; exact hLv
      · have hgood : (fun k => U k l') = ket l' := by
          by_contra h
          exact hcon ⟨hll, by simp [badCols, h]⟩
        rw [hcol, hgood]
        refine hLk l' hll ?_
        have h := congrFun (congrFun hUU l') l
        simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_ne hll] at h
        have hs : ∀ k, star (U k l') = if k = l' then 1 else 0 := fun k => by
          rw [show U k l' = ket l' k from congrFun hgood k, ket_apply]
          split_ifs <;> simp
        simpa [hs] using h
    have hlt : (badCols (L.prod * U)).card < m := by
      calc (badCols (L.prod * U)).card ≤ ((badCols U).erase l).card := Finset.card_le_card hsub
        _ < m := by rw [Finset.card_erase_of_mem hl, hcard]; omega
    obtain ⟨L', hL', hL'U⟩ := ih _ hlt (L.prod * U) (mul_mem hW hU) rfl
    refine ⟨(L.map conjTranspose).reverse ++ L', ?_, ?_⟩
    · intro V hV
      rcases List.mem_append.mp hV with hV | hV
      · rw [List.mem_reverse, List.mem_map] at hV
        obtain ⟨V0, h0, rfl⟩ := hV
        exact (hL V0 h0).conjTranspose
      · exact hL' V hV
    · rw [List.prod_append, hL'U, ← conjTranspose_list_prod, ← mul_assoc, hWW, one_mul]

/-- Every unitary on at least two basis states is a product of two-level unitaries. -/
theorem unitary_eq_prod_twoLevel [Nontrivial ι] {U : Matrix ι ι ℂ} (hU : U ∈ unitaryGroup ι ℂ) :
    ∃ L : List (Matrix ι ι ℂ), (∀ V ∈ L, IsTwoLevelUnitary V) ∧ L.prod = U :=
  exists_twoLevel_prod_eq _ U hU rfl

/-- **Two-level decomposition on `n ≥ 1` qubits.** -/
theorem qubit_unitary_eq_prod_twoLevel {n : ℕ} (hn : 1 ≤ n)
    {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hU : U ∈ unitaryGroup (Fin (2 ^ n)) ℂ) :
    ∃ L : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ), (∀ V ∈ L, IsTwoLevelUnitary V) ∧
      L.prod = U := by
  have : Nontrivial (Fin (2 ^ n)) := Fin.nontrivial_iff_two_le.mpr
    (by calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact unitary_eq_prod_twoLevel hU

end CatCrypt.Quantum.TwoLevelUniversality
