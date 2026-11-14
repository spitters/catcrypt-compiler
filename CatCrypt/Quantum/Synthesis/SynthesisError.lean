/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.AngleSnap

/-!
# Errors of approximate circuit synthesis add up

Replacing each factor `Uᵢ` of a product by an approximation `Vᵢ` moves the product by at
most the sum of the per-factor distances `‖Uᵢ - Vᵢ‖`, as long as every factor has norm at
most `1`: `U₁ ⋯ Uₘ - V₁ ⋯ Vₘ` telescopes into `Σᵢ U₁ ⋯ Uᵢ₋₁ (Uᵢ - Vᵢ) Vᵢ₊₁ ⋯ Vₘ`. This holds
in every normed ring, so for unitaries of a C⋆-ring, and for unitary matrices under the `ℓ²`
operator norm.

For gate lists under the compiler's denotation `listMatrix` (head gate applied first), a
circuit whose every gate `g` is replaced by a gate list `r g` within `ε g` of it is within
`Σ_g ε g` of the circuit. Instances: rounding every `Rz` angle by a map `ρ` moves the circuit
by at most `Σ |ρ θ - θ|` over its rotations, and the angle snapping of imported statements
(`AngleSnap.snapQ`) moves a list by at most the sum of the actual per-statement errors, which
is at most the bound `snapQ` returns.

## Main results

* `norm_prod_map_sub_le` — telescoping in a normed ring for factors of norm at most `1`.
* `norm_prod_map_unitary_sub_le` — the same for unitaries of a C⋆-ring.
* `norm_prod_map_unitaryGroup_sub_le` — the same for unitary matrices under the `ℓ²`
  operator norm.
* `norm_listMatrix_flatMap_sub_le_sum` — the circuit form: per-gate replacement errors add.
* `norm_listMatrix_roundRz_sub_le` — rounding the `Rz` angles of a circuit.
* `norm_qelibListMatrix_snapQ_sub_le_sum` — angle snapping is within the sum of its
  per-statement errors, and that sum is within the returned bound.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix.Norms.L2Operator
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append)
open CatCrypt.Quantum.Synthesis.IntervalArith (listMatrix_mem_unitaryGroup norm_embedGate1_le)
open CatCrypt.Quantum.AngleSnap

namespace CatCrypt.Quantum.Synthesis.SynthesisError

/-! ## Telescoping in a normed ring -/

section NormedRing

variable {R : Type*} [NormedRing R] [NormOneClass R] {α : Type*}

/-- A product of factors of norm at most `1` has norm at most `1`. -/
theorem norm_prod_map_le_one (f : α → R) :
    ∀ L : List α, (∀ x ∈ L, ‖f x‖ ≤ 1) → ‖(L.map f).prod‖ ≤ 1
  | [], _ => by simp
  | x :: L, h => by
    rw [List.map_cons, List.prod_cons]
    refine (norm_mul_le _ _).trans ?_
    have h1 := h x List.mem_cons_self
    have h2 := norm_prod_map_le_one f L fun y hy => h y (List.mem_cons_of_mem x hy)
    nlinarith [norm_nonneg (f x), norm_nonneg (L.map f).prod]

/-- **Telescoping.** For factors of norm at most `1`, the distance of the products of
`f x` and of `g x` over a list is at most the sum of the distances of the factors. -/
theorem norm_prod_map_sub_le (f g : α → R) :
    ∀ L : List α, (∀ x ∈ L, ‖f x‖ ≤ 1) → (∀ x ∈ L, ‖g x‖ ≤ 1) →
      ‖(L.map f).prod - (L.map g).prod‖ ≤ (L.map fun x => ‖f x - g x‖).sum
  | [], _, _ => by simp
  | x :: L, hf, hg => by
    have hf' : ∀ y ∈ L, ‖f y‖ ≤ 1 := fun y hy => hf y (List.mem_cons_of_mem x hy)
    have hg' : ∀ y ∈ L, ‖g y‖ ≤ 1 := fun y hy => hg y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine (norm_mul_sub_mul_le (hf x List.mem_cons_self) (norm_prod_map_le_one g L hg')).trans ?_
    have := norm_prod_map_sub_le f g L hf' hg'
    linarith

/-- Telescoping for products taken in the reverse order of the list (head factor
rightmost), the order of a circuit whose head gate is applied first. -/
theorem norm_prod_reverse_map_sub_le (f g : α → R) (L : List α) (hf : ∀ x ∈ L, ‖f x‖ ≤ 1)
    (hg : ∀ x ∈ L, ‖g x‖ ≤ 1) :
    ‖(L.map f).reverse.prod - (L.map g).reverse.prod‖ ≤ (L.map fun x => ‖f x - g x‖).sum := by
  rw [← List.map_reverse, ← List.map_reverse]
  refine (norm_prod_map_sub_le f g L.reverse (fun x hx => hf x (List.mem_reverse.mp hx))
    (fun x hx => hg x (List.mem_reverse.mp hx))).trans ?_
  rw [List.map_reverse, List.sum_reverse]

end NormedRing

/-! ## Unitaries -/

/-- **Telescoping for unitaries.** In a nontrivial C⋆-ring, the distance of two products of
unitaries is at most the sum of the distances of the factors. -/
theorem norm_prod_map_unitary_sub_le {R : Type*} [NormedRing R] [StarRing R] [CStarRing R]
    [Nontrivial R] {α : Type*} (f g : α → unitary R) (L : List α) :
    ‖(L.map fun x => (f x : R)).prod - (L.map fun x => (g x : R)).prod‖
      ≤ (L.map fun x => ‖(f x : R) - g x‖).sum :=
  norm_prod_map_sub_le _ _ L (fun x _ => (CStarRing.norm_coe_unitary (f x)).le)
    (fun x _ => (CStarRing.norm_coe_unitary (g x)).le)

/-- **Telescoping for unitary matrices** under the `ℓ²` operator norm. -/
theorem norm_prod_map_unitaryGroup_sub_le {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {α : Type*} (f g : α → Matrix.unitaryGroup m ℂ) (L : List α) :
    ‖(L.map fun x => (f x : Matrix m m ℂ)).prod - (L.map fun x => (g x : Matrix m m ℂ)).prod‖
      ≤ (L.map fun x => ‖(f x : Matrix m m ℂ) - g x‖).sum :=
  norm_prod_map_unitary_sub_le f g L

/-! ## Circuits -/

variable {n : ℕ}

/-- The matrix of a gate list is the reversed product of the matrices of its gates. -/
theorem listMatrix_eq_prod (l : List (Gate n)) :
    listMatrix l = (l.map gateEmbedding).reverse.prod := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [listMatrix_cons, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

/-- The matrix of a concatenation of gate lists is the reversed product of their matrices. -/
theorem listMatrix_flatMap_eq_prod {α : Type*} (L : List α) (r : α → List (Gate n)) :
    listMatrix (L.flatMap r) = (L.map fun x => listMatrix (r x)).reverse.prod := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [List.flatMap_cons, listMatrix_append, ih, List.map_cons,
      List.reverse_cons, List.prod_append, List.prod_singleton]

theorem norm_listMatrix_le_one (l : List (Gate n)) : ‖listMatrix l‖ ≤ 1 :=
  (CStarRing.norm_of_mem_unitary (listMatrix_mem_unitaryGroup l)).le

theorem norm_gateEmbedding_le_one (g : Gate n) : ‖gateEmbedding g‖ ≤ 1 := by
  have h := norm_listMatrix_le_one [g]
  rwa [listMatrix_cons, listMatrix_nil, one_mul] at h

/-- **Approximate synthesis of a circuit.** If every gate `g` of `l` is replaced by a gate
list `r g` within `ε g` of it, the resulting circuit is within `Σ_{g ∈ l} ε g` of `l`. -/
theorem norm_listMatrix_flatMap_sub_le_sum (l : List (Gate n)) (r : Gate n → List (Gate n))
    (ε : Gate n → ℝ) (h : ∀ g ∈ l, ‖listMatrix (r g) - gateEmbedding g‖ ≤ ε g) :
    ‖listMatrix (l.flatMap r) - listMatrix l‖ ≤ (l.map ε).sum := by
  rw [listMatrix_flatMap_eq_prod, listMatrix_eq_prod]
  refine (norm_prod_reverse_map_sub_le _ _ l (fun g _ => norm_listMatrix_le_one (r g))
    (fun g _ => norm_gateEmbedding_le_one g)).trans ?_
  exact List.sum_le_sum fun g hg => h g hg

/-- Gate-by-gate replacement: a circuit whose every gate `g` is replaced by a gate `r g`
within `ε g` of it is within `Σ_{g ∈ l} ε g` of `l`. -/
theorem norm_listMatrix_map_sub_le_sum (l : List (Gate n)) (r : Gate n → Gate n)
    (ε : Gate n → ℝ) (h : ∀ g ∈ l, ‖gateEmbedding (r g) - gateEmbedding g‖ ≤ ε g) :
    ‖listMatrix (l.map r) - listMatrix l‖ ≤ (l.map ε).sum := by
  rw [listMatrix_eq_prod, listMatrix_eq_prod, List.map_map]
  refine (norm_prod_reverse_map_sub_le (gateEmbedding ∘ r) gateEmbedding l
    (fun g _ => norm_gateEmbedding_le_one (r g)) (fun g _ => norm_gateEmbedding_le_one g)).trans ?_
  exact List.sum_le_sum fun g hg => h g hg

/-! ## Rounding the rotation angles -/

/-- Replace the angle `θ` of every `Rz` gate by `ρ θ`. -/
def roundRz (ρ : ℝ → ℝ) : Gate n → Gate n
  | .Rz q θ => .Rz q (ρ θ)
  | g => g

/-- The moved angle of a gate under `roundRz ρ`: `|ρ θ - θ|` for `Rz θ`, `0` otherwise. -/
def rzErr (ρ : ℝ → ℝ) : Gate n → ℝ
  | .Rz _ θ => |ρ θ - θ|
  | _ => 0

/-- One gate moves by at most its moved angle. -/
theorem norm_gateEmbedding_roundRz_sub_le (ρ : ℝ → ℝ) (g : Gate n) :
    ‖gateEmbedding (roundRz ρ g) - gateEmbedding g‖ ≤ rzErr ρ g := by
  cases g with
  | Rz q θ =>
    simp only [roundRz, rzErr, gateEmbedding]
    rw [embedGate1_sub]
    exact (norm_embedGate1_le _ _).trans (norm_rzGate_sub_le _ _)
  | _ => simp [roundRz, rzErr]

/-- **Rounding the `Rz` angles.** A circuit whose `Rz` angles are moved by `ρ` is within the
sum over its rotations of the moved angles. -/
theorem norm_listMatrix_roundRz_sub_le (ρ : ℝ → ℝ) (l : List (Gate n)) :
    ‖listMatrix (l.map (roundRz ρ)) - listMatrix l‖ ≤ (l.map (rzErr ρ)).sum :=
  norm_listMatrix_map_sub_le_sum l (roundRz ρ) (rzErr ρ) fun g _ =>
    norm_gateEmbedding_roundRz_sub_le ρ g

/-! ## Angle snapping of imported statements -/

open CatCrypt.Quantum.Qelib in
/-- The matrix of a list of statements is the reversed product of their matrices. -/
theorem qelibListMatrix_eq_prod (l : List (OpenQASMImport.QGate n)) :
    qelibListMatrix l = (l.map qelibMatrix).reverse.prod := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [qelibListMatrix, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

open CatCrypt.Quantum.Qelib in
/-- **Angle snapping as an instance.** For statements with distinct operands, the snapped
list is within the sum of the per-statement errors `‖snapGate g - g‖`, and that sum is at
most the bound `snapQ` returns. -/
theorem norm_qelibListMatrix_snapQ_sub_le_sum (l : List (OpenQASMImport.QGate n))
    (hl : ∀ g ∈ l, Distinct g) :
    ‖qelibListMatrix (snapQ l).1 - qelibListMatrix l‖
        ≤ (l.map fun g => ‖qelibMatrix (snapGate g).1 - qelibMatrix g‖).sum ∧
      (l.map fun g => ‖qelibMatrix (snapGate g).1 - qelibMatrix g‖).sum ≤ ((snapQ l).2 : ℝ) := by
  constructor
  · rw [snapQ_fst, qelibListMatrix_eq_prod, qelibListMatrix_eq_prod, List.map_map]
    exact norm_prod_reverse_map_sub_le (qelibMatrix ∘ fun g => (snapGate g).1) qelibMatrix l
      (fun g hg => norm_qelibMatrix_le_one _ ((distinct_snapGate g).2 (hl g hg)))
      (fun g hg => norm_qelibMatrix_le_one g (hl g hg))
  · have h : ((snapQ l).2 : ℝ) = (l.map fun g => ((snapGate g).2 : ℝ)).sum := by
      simp [snapQ, List.map_map, Function.comp_def]
    rw [h]
    exact List.sum_le_sum fun g _ => norm_qelibMatrix_snapGate_sub_le g

end CatCrypt.Quantum.Synthesis.SynthesisError
