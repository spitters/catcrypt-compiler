/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.ApproxEmit

/-!
# Replacing one-qubit gates by words over `H`, `T`, `T†`

The pass `skReplace p` replaces every one-qubit gate of a gate list other than `H`, `T`, `T†`
by the word `p (mat1 g)` over `H`, `T`, `T†` placed on the qubit of the gate. A producer `p`
is sound at precision `ε` (`ProducerSound`) when, on every unitary `U`, its word is over
`H`, `T`, `T†` and within `ε` of `U` up to a phase. Under that hypothesis the output of the
pass is within `k ε` of the input in the `ℓ²` operator norm up to one global phase, `k` the
number of replaced gates. The phase cannot be dropped: the determinant of a word over `H`,
`T`, `T†` is an eighth root of unity, while `rzGate θ` has determinant `e^{iθ}`.

## Main definitions

* `isHT`, `isRot` — the letters of the words and the gates the pass replaces.
* `atQubit` — a one-qubit word placed at a qubit.
* `ProducerSound` — soundness of a word producer at a precision.
* `skReplace` — the pass.

## Main statements

* `listMatrix_atQubit` — the matrix of a placed word is the embedding of its matrix.
* `mat1_mem_unitaryGroup` — the `2 × 2` matrix of a gate is unitary.
* `norm_listMatrix_flatMap_sub_smul_le` — errors of concatenated segments add, with unit
  phases.
* `listMatrix_skReplace_approx` — **correctness of the pass** up to a global phase.
* `isRot_skReplace` — the output has no replaceable gate.
* `length_skReplace` — the length of the output.
-/

@[expose] public section

set_option autoImplicit false

open Complex
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix listMatrix_append listMatrix_cons listMatrix_nil)
open CatCrypt.Quantum.Synthesis.ZYZPass (oneQ?)
open CatCrypt.Quantum.Synthesis.IntervalArith (mat1 listMatrix_mem_unitaryGroup
  norm_embedGate1_le norm_mul_sub_smul_le embed1Hom)
open scoped Matrix.Norms.L2Operator

namespace CatCrypt.Quantum.Synthesis.SK

variable {n : ℕ}

/-- The letters of the words: `H`, `T`, `T†`. -/
def isHT : Gate n → Bool
  | .H _ | .T _ | .Tdg _ => true
  | _ => false

/-- The gates the pass replaces: the one-qubit gates other than `H`, `T`, `T†`. -/
def isRot : Gate n → Bool
  | .X _ | .Y _ | .Z _ | .S _ | .Rz _ _ | .RzQ _ _ => true
  | _ => false

/-- The replaceable gates are the one-qubit gates that are not letters. -/
theorem isRot_eq_true_iff (g : Gate n) : isRot g = true ↔ (oneQ? g).isSome ∧ isHT g = false := by
  cases g <;> simp [isRot, isHT, oneQ?]

/-- A letter is not replaceable. -/
theorem isRot_eq_false_of_isHT {g : Gate n} (h : isHT g = true) : isRot g = false := by
  cases g <;> simp_all [isRot, isHT]

/-- A word on one qubit placed at qubit `q`. -/
def atQubit (q : Fin n) (w : List (Gate 1)) : List (Gate n) :=
  w.map (QFT.mapGate fun _ => q)

/-- On one qubit, the embedding of a gate matrix is the matrix itself. -/
private theorem embedGate1_fin_one (i : Fin 1) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 1 i G = G := by
  rw [Subsingleton.elim i 0]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The matrix of a one-qubit gate placed at `q` is the embedding at `q` of its matrix. -/
theorem gateEmbedding_mapGate_const (q : Fin n) (g : Gate 1) :
    gateEmbedding (QFT.mapGate (fun _ => q) g) = embedGate1 n q (gateEmbedding g) := by
  cases g <;> simp only [QFT.mapGate, gateEmbedding, embedGate1_fin_one]
  all_goals
    rename_i a b
    obtain rfl := Subsingleton.elim a b
    simp [GateUnitarity.embedGate1_one]

/-- The matrix of a word placed at `q` is the embedding at `q` of the matrix of the word. -/
theorem listMatrix_atQubit (q : Fin n) (w : List (Gate 1)) :
    listMatrix (atQubit q w) = embedGate1 n q (listMatrix w) := by
  induction w with
  | nil => simp [atQubit, listMatrix_nil, GateUnitarity.embedGate1_one]
  | cons g w ih =>
    rw [atQubit, List.map_cons, listMatrix_cons, ← atQubit, ih, listMatrix_cons,
      gateEmbedding_mapGate_const, GateUnitarity.embedGate1_mul]

/-- A word over `H`, `T`, `T†` placed at a qubit is over `H`, `T`, `T†`. -/
theorem isHT_atQubit {q : Fin n} {w : List (Gate 1)} (hw : ∀ g ∈ w, isHT g = true) :
    ∀ g ∈ atQubit q w, isHT g = true := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  have := hw g' hg'
  cases g' <;> simp_all [isHT, QFT.mapGate]

/-- The `2 × 2` matrix of a one-qubit gate is unitary. -/
theorem mat1_mem_unitaryGroup (g : Gate n) : mat1 g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hu := listMatrix_mem_unitaryGroup [QFT.mapGate (fun _ => (0 : Fin 1)) g]
  have hm : mat1 (QFT.mapGate (fun _ => (0 : Fin 1)) g) = mat1 g := by
    cases g <;> rfl
  rcases h : oneQ? (QFT.mapGate (fun _ => (0 : Fin 1)) g) with _ | q
  · cases g <;> simp_all [oneQ?, QFT.mapGate, mat1, gateMatrix1]
  · rw [listMatrix_cons, listMatrix_nil, one_mul,
      IntervalArith.gateEmbedding_eq_embedGate1_mat1 h, embedGate1_fin_one, hm] at hu
    exact hu

/-- Phases as unit complex numbers: the concatenation form of
`IntervalArith.norm_listMatrix_flatMap_sub_le` with `c x` in place of `exp (I * φ x)`. -/
theorem norm_listMatrix_flatMap_sub_smul_le {α : Type*} (L : List α) (F G : α → List (Gate n))
    (c : α → ℂ) (ε : α → ℝ) (hc : ∀ x ∈ L, ‖c x‖ = 1)
    (h : ∀ x ∈ L, ‖listMatrix (F x) - c x • listMatrix (G x)‖ ≤ ε x) :
    ‖listMatrix (L.flatMap F) - (L.map c).prod • listMatrix (L.flatMap G)‖ ≤ (L.map ε).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => hc y (List.mem_cons_of_mem x hy))
      fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [List.flatMap_cons, List.flatMap_cons, listMatrix_append, listMatrix_append,
      List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, mul_comm]
    refine (norm_mul_sub_smul_le (listMatrix_mem_unitaryGroup _) (listMatrix_mem_unitaryGroup _)
      _ _ (hc x List.mem_cons_self)).trans ?_
    linarith

/-- A producer of words is sound at precision `ε`: on every unitary its word is over
`H, T, T†` and within `ε` of the unitary up to a phase. -/
def ProducerSound (p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)) (ε : ℝ) : Prop :=
  ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, (∀ g ∈ p U, isHT g = true) ∧
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖listMatrix (p U) - c • U‖ ≤ ε

/-- The replacement of one gate: a replaceable gate on qubit `q` becomes the word of its
matrix at `q`; any other gate is kept. -/
noncomputable def skGate (p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)) (g : Gate n) :
    List (Gate n) :=
  match isRot g, oneQ? g with
  | true, some q => atQubit q (p (mat1 g))
  | _, _ => [g]

/-- The pass: each replaceable gate on qubit `q` becomes the word of its matrix at `q`. -/
noncomputable def skReplace (p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)) :
    List (Gate n) → List (Gate n) :=
  List.flatMap (skGate p)

/-- A replaceable gate has a qubit. -/
theorem exists_oneQ?_of_isRot {g : Gate n} (hr : isRot g = true) : ∃ q, oneQ? g = some q :=
  Option.isSome_iff_exists.mp ((isRot_eq_true_iff g).mp hr).1

/-- The replacement of a replaceable gate on `q`. -/
theorem skGate_of_isRot {p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)} {g : Gate n} {q : Fin n}
    (hr : isRot g = true) (hq : oneQ? g = some q) : skGate p g = atQubit q (p (mat1 g)) := by
  simp only [skGate, hr, hq]

/-- A gate that is not replaceable is kept. -/
theorem skGate_of_isRot_eq_false {p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)} {g : Gate n}
    (hr : isRot g = false) : skGate p g = [g] := by
  simp only [skGate, hr]

/-- The bound of one replaced gate. -/
theorem norm_skGate_sub_le {p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)} {ε : ℝ}
    (hp : ProducerSound p ε) (g : Gate n) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖listMatrix (skGate p g) - c • listMatrix [g]‖ ≤ if isRot g then ε else 0 := by
  cases hr : isRot g
  · refine ⟨1, by simp, ?_⟩
    rw [skGate_of_isRot_eq_false hr]
    simp
  · obtain ⟨q, hq⟩ := exists_oneQ?_of_isRot hr
    obtain ⟨-, c, hc1, hc⟩ := hp (mat1 g) (mat1_mem_unitaryGroup g)
    refine ⟨c, hc1, ?_⟩
    rw [skGate_of_isRot hr hq, listMatrix_atQubit, listMatrix_cons, listMatrix_nil, one_mul,
      IntervalArith.gateEmbedding_eq_embedGate1_mat1 hq, ← GateUnitarity.embedGate1_smul]
    have hsub : embedGate1 n q (listMatrix (p (mat1 g))) - embedGate1 n q (c • mat1 g) =
        embedGate1 n q (listMatrix (p (mat1 g)) - c • mat1 g) :=
      (map_sub (embed1Hom q) _ _).symm
    rw [hsub]
    simp only [↓reduceIte]
    exact (norm_embedGate1_le q _).trans hc

/-- **Correctness of the pass.** Up to one global phase, the output is within the number of
replaced gates times `ε`. -/
theorem listMatrix_skReplace_approx {p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)} {ε : ℝ}
    (hp : ProducerSound p ε) (L : List (Gate n)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖listMatrix (skReplace p L) - c • listMatrix L‖ ≤ (L.countP isRot : ℝ) * ε := by
  choose c hc1 hc using norm_skGate_sub_le hp (n := n)
  refine ⟨(L.map c).prod, ?_, ?_⟩
  · clear hc
    induction L with
    | nil => simp
    | cons x L ih => rw [List.map_cons, List.prod_cons, norm_mul, hc1, ih, one_mul]
  · have h := norm_listMatrix_flatMap_sub_smul_le L (skGate p) (fun g => [g]) c
      (fun g => if isRot g then ε else 0) (fun x _ => hc1 x) (fun x _ => hc x)
    have hL : L.flatMap (fun g => [g]) = L := by simp
    have hs : (L.map fun g => if isRot g then ε else 0).sum = (L.countP isRot : ℝ) * ε := by
      clear h hL
      induction L with
      | nil => simp
      | cons g L ih =>
        rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
        split <;> push_cast <;> ring
    rw [hL, hs] at h
    exact h

/-- The output has no replaceable gate: its one-qubit gates are `H`, `T`, `T†`. -/
theorem isRot_skReplace {p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)} {ε : ℝ}
    (hp : ProducerSound p ε) (L : List (Gate n)) : ∀ g ∈ skReplace p L, isRot g = false := by
  intro g hg
  obtain ⟨g₀, -, hg⟩ := List.mem_flatMap.mp hg
  cases hr : isRot g₀
  · rw [skGate_of_isRot_eq_false hr, List.mem_singleton] at hg
    rwa [hg]
  · obtain ⟨q, hq⟩ := exists_oneQ?_of_isRot hr
    rw [skGate_of_isRot hr hq] at hg
    exact isRot_eq_false_of_isHT (isHT_atQubit (hp _ (mat1_mem_unitaryGroup g₀)).1 g hg)

/-- For words of length at most `ℓ`, the output has length at most `|L| + k ℓ`, `k` the
number of replaced gates. -/
theorem length_skReplace {p : Matrix (Fin 2) (Fin 2) ℂ → List (Gate 1)} {ℓ : ℕ}
    (hl : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, (p U).length ≤ ℓ) (L : List (Gate n)) :
    (skReplace p L).length ≤ L.length + L.countP isRot * ℓ := by
  induction L with
  | nil => simp [skReplace]
  | cons g L ih =>
    rw [skReplace, List.flatMap_cons, List.length_append, ← skReplace, List.length_cons,
      List.countP_cons]
    cases hr : isRot g
    · rw [skGate_of_isRot_eq_false hr]
      simp only [List.length_singleton, Bool.false_eq_true, ↓reduceIte, add_zero]
      omega
    · obtain ⟨q, hq⟩ := exists_oneQ?_of_isRot hr
      have h1 := hl _ (mat1_mem_unitaryGroup g)
      rw [skGate_of_isRot hr hq, atQubit, List.length_map]
      simp only [↓reduceIte, add_mul, one_mul]
      omega

end CatCrypt.Quantum.Synthesis.SK
