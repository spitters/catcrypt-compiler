/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.ControlledGates
public import CatCrypt.Quantum.QFT.Inverse
public import CatCrypt.Quantum.Optimization.MixedCommute
public import CatCrypt.Quantum.Optimization.PhasePolySemantics

/-!
# Predicate ancillae, compute/uncompute and the relative-phase Toffoli

A multi-controlled operation can be realised with one clean ancilla `a`: a circuit `V`
computes a predicate `Π` of the control qubits `cs` into `a`, every gate of the block `U` is
controlled on `a` alone, and the inverse circuit `V⁻¹` uncomputes the ancilla. The circuit
`V` need only be correct up to a diagonal phase `D` that depends on `a` and `cs`, which
admits the relative-phase Toffoli in Clifford+T with four `T` gates (Maslov, Phys. Rev. A 93,
022311, 2016) as the circuit computing the AND of two controls.

The matrix of a gate list is `QFT.listMatrix` (head gate applied first); `P₀ a` and `P₁ a`
below are `embedGate1 n a proj0` and `embedGate1 n a proj1`.

## Main definitions

* `PhaseOn S D` — `D` is diagonal with entries depending only on the bits at `S`.
* `IsPred S Π` — `Π` is the projector of a predicate of the bits at `S`.
* `ancillaCtrlGates V a U` — compute `V`, `U` controlled on `a`, uncompute `invGates V`.
* `rtofGates c₁ c₂ a` — the relative-phase Toffoli with four `T` gates and three `CNOT`s;
  `rtofPhase c₁ c₂ a` — its phase.

## Main results

* `commute_of_phaseOn` — a phase on `S` commutes with every gate list avoiding `S`.
* `listMatrix_predAncilla_conj` — on ancilla `|0⟩`, `ancillaCtrlGates V a U` applies `U`
  exactly where `Π` holds.
* `predAncilla_restores` — it returns the ancilla to `|0⟩`.
* `listMatrix_andAncilla_conj` — the AND instance with `V = mctrlGates cs (X a)`.
* `listMatrix_rtofGates` — the relative-phase Toffoli is `rtofPhase` times the Toffoli, and
  `phaseOn_rtofPhase` — the phase is diagonal on `[c₁, c₂, a]`.
* `listMatrix_rtofAncilla_conj` — the ancilla construction with the relative-phase Toffoli.
* `length_ancillaCtrlGates` — the construction is linear in the length of the block.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append invGates
  listMatrix_invGates length_invGates)

noncomputable section

namespace CatCrypt.Quantum.AndAncilla

variable {n : ℕ}

/-! ## Phases on a set of qubits -/

/-- `D` is diagonal and its entry at `x` depends only on the bits of `x` at the qubits `S`. -/
def PhaseOn (S : List (Fin n)) (D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  ∃ f : Fin (2 ^ n) → ℂ, D = Matrix.diagonal f ∧
    ∀ x y : Fin (2 ^ n), (∀ q ∈ S, gbit n q x.val = gbit n q y.val) → f x = f y

/-- `P` is a `0/1` diagonal depending only on the bits at `S`: the projector of a predicate
    of the qubits `S`. -/
def IsPred (S : List (Fin n)) (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  PhaseOn S P ∧ P * P = P

/-- Every nonzero entry of `M` connects two indices with the same bits at `S`. -/
def KeepsBits (S : List (Fin n)) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  ∀ x y : Fin (2 ^ n), M x y ≠ 0 → ∀ q ∈ S, gbit n q x.val = gbit n q y.val

/-- The identity is a phase on every set of qubits. -/
theorem phaseOn_one (S : List (Fin n)) : PhaseOn S 1 :=
  ⟨fun _ => 1, Matrix.diagonal_one.symm, fun _ _ _ => rfl⟩

/-- A phase on `S` is a phase on every superset of `S`. -/
theorem PhaseOn.mono {S T : List (Fin n)} {D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hD : PhaseOn S D) (hST : S ⊆ T) : PhaseOn T D := by
  obtain ⟨f, rfl, hf⟩ := hD
  exact ⟨f, rfl, fun x y h => hf x y fun q hq => h q (hST hq)⟩

/-- The product of two phases on `S` is a phase on `S`. -/
theorem PhaseOn.mul {S : List (Fin n)} {D E : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hD : PhaseOn S D) (hE : PhaseOn S E) : PhaseOn S (D * E) := by
  obtain ⟨f, rfl, hf⟩ := hD
  obtain ⟨g, rfl, hg⟩ := hE
  exact ⟨fun x => f x * g x, Matrix.diagonal_mul_diagonal f g, fun x y h => by
    simp only [hf x y h, hg x y h]⟩

/-- The sum of two phases on `S` is a phase on `S`. -/
theorem PhaseOn.add {S : List (Fin n)} {D E : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hD : PhaseOn S D) (hE : PhaseOn S E) : PhaseOn S (D + E) := by
  obtain ⟨f, rfl, hf⟩ := hD
  obtain ⟨g, rfl, hg⟩ := hE
  exact ⟨f + g, Matrix.diagonal_add f g, fun x y h => by
    simp only [Pi.add_apply, hf x y h, hg x y h]⟩

/-- A diagonal single-qubit operator on a qubit of `S` is a phase on `S`. -/
theorem phaseOn_embedGate1 {S : List (Fin n)} {q : Fin n} (hq : q ∈ S)
    {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : IsDiagonal G) : PhaseOn S (embedGate1 n q G) :=
  ⟨_, embedGate1_eq_diagonal q hG, fun x y h => by rw [h q hq]⟩

/-- Two diagonal matrices commute. -/
theorem PhaseOn.commute {S T : List (Fin n)} {D E : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hD : PhaseOn S D) (hE : PhaseOn T E) : Commute D E := by
  obtain ⟨f, rfl, -⟩ := hD
  obtain ⟨g, rfl, -⟩ := hE
  change Matrix.diagonal f * Matrix.diagonal g = Matrix.diagonal g * Matrix.diagonal f
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  ring

/-- A phase on `S` commutes with every matrix that keeps the bits at `S`. -/
theorem PhaseOn.commute_of_keepsBits {S : List (Fin n)}
    {D M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hD : PhaseOn S D) (hM : KeepsBits S M) :
    Commute D M := by
  obtain ⟨f, rfl, hf⟩ := hD
  change Matrix.diagonal f * M = M * Matrix.diagonal f
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M x y = 0
  · simp [h]
  · rw [hf x y (hM x y h)]
    ring

/-- The identity keeps every bit. -/
theorem keepsBits_one (S : List (Fin n)) : KeepsBits S 1 := by
  intro x y h q _
  by_cases hxy : x = y
  · rw [hxy]
  · exact absurd (Matrix.one_apply_ne hxy) h

/-- A product of matrices keeping the bits at `S` keeps them. -/
theorem KeepsBits.mul {S : List (Fin n)} {M N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : KeepsBits S M) (hN : KeepsBits S N) : KeepsBits S (M * N) := by
  intro x y h q hq
  rw [Matrix.mul_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hk
  rw [hM x k h₁ q hq, hN k y h₂ q hq]

/-- A single-qubit operator on a qubit outside `S` keeps the bits at `S`. -/
theorem keepsBits_embedGate1 {S : List (Fin n)} {t : Fin n} (ht : ∀ q ∈ S, t ≠ q)
    (G : Matrix (Fin 2) (Fin 2) ℂ) : KeepsBits S (embedGate1 n t G) := by
  intro x y h q hq
  rw [CatCrypt.Quantum.Optimization.DisjointCommute.embedGate1_apply] at h
  by_cases hm : Match n t x.val y.val
  · exact gbit_eq_of_match (Ne.symm (ht q hq)) hm
  · exact absurd (ite_eq_right_iff.mpr fun h' => absurd h' hm) h

/-- A two-qubit operator on qubits outside `S` keeps the bits at `S`. -/
theorem keepsBits_embedGate2 {S : List (Fin n)} {i j : Fin n} (hi : ∀ q ∈ S, i ≠ q)
    (hj : ∀ q ∈ S, j ≠ q) (hij : i ≠ j) (G : Matrix (Fin 4) (Fin 4) ℂ) :
    KeepsBits S (embedGate2 n i j G hij) := by
  intro x y h q hq
  rw [embedGate2_apply hij] at h
  by_cases hm : Match2 n i j x.val y.val
  · apply Fin.ext
    rw [gbit_eq_testBit, gbit_eq_testBit,
      hm (pos n q) (pos_ne (Ne.symm (hi q hq))) (pos_ne (Ne.symm (hj q hq)))]
  · exact absurd (ite_eq_right_iff.mpr fun h' => absurd h' hm) h

/-- A gate avoiding every qubit of `S` keeps the bits at `S`. -/
theorem keepsBits_gateEmbedding {S : List (Fin n)} {g : Gate n}
    (hg : ∀ q ∈ S, Avoids q g) : KeepsBits S (gateEmbedding g) := by
  cases g with
  | CNOT i j =>
    by_cases hij : i = j
    · simp only [gateEmbedding, dite_eq_left hij]; exact keepsBits_one S
    · simp only [gateEmbedding, dite_eq_right hij]
      exact keepsBits_embedGate2 (fun q hq => (hg q hq).1) (fun q hq => (hg q hq).2) hij _
  | CZ i j =>
    by_cases hij : i = j
    · simp only [gateEmbedding, dite_eq_left hij]; exact keepsBits_one S
    · simp only [gateEmbedding, dite_eq_right hij]
      exact keepsBits_embedGate2 (fun q hq => (hg q hq).1) (fun q hq => (hg q hq).2) hij _
  | _ => exact keepsBits_embedGate1 hg _

/-- A gate list avoiding every qubit of `S` keeps the bits at `S`. -/
theorem keepsBits_listMatrix {S : List (Fin n)} :
    ∀ {L : List (Gate n)}, (∀ g ∈ L, ∀ q ∈ S, Avoids q g) → KeepsBits S (listMatrix L)
  | [], _ => by rw [listMatrix_nil]; exact keepsBits_one S
  | g :: L, h => by
    rw [listMatrix_cons]
    exact (keepsBits_listMatrix fun g' hg' => h g' (List.mem_cons_of_mem g hg')).mul
      (keepsBits_gateEmbedding (h g List.mem_cons_self))

/-- **Phases commute with gate lists that avoid their qubits.** -/
theorem commute_of_phaseOn {S : List (Fin n)} {D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {U : List (Gate n)} (hD : PhaseOn S D) (hU : ∀ g ∈ U, ∀ q ∈ S, Avoids q g) :
    Commute D (listMatrix U) :=
  hD.commute_of_keepsBits (keepsBits_listMatrix hU)

/-! ## Unitarity and the commutations on the ancilla -/

/-- The matrix of a gate list is unitary. -/
theorem listMatrix_conjTranspose_mul (l : List (Gate n)) :
    (listMatrix l)ᴴ * listMatrix l = 1 := by
  induction l with
  | nil => rw [listMatrix_nil, Matrix.conjTranspose_one, one_mul]
  | cons g l ih =>
    rw [listMatrix_cons, Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc (listMatrix l)ᴴ, ih,
      one_mul, gateEmbedding_conjTranspose_mul]

/-- A matrix commuting with every single-qubit operator on `a` commutes with each of them. -/
theorem CommOn.commute {a : Fin n} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn a M) (G : Matrix (Fin 2) (Fin 2) ℂ) : Commute M (embedGate1 n a G) :=
  (hM G).symm

/-- `X` maps `|0⟩` into `|1⟩`: `|1⟩⟨1| X |0⟩⟨0| = X |0⟩⟨0|`. -/
theorem proj1_pauliX_proj0 : proj1 * pauliX * proj0 = pauliX * proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The conjugation theorem -/

/-- The algebra of the conjugation theorem in a ring: `Vs` inverts `V`, `W = 1 + P₁ A` is
    the control of `1 + A` on the ancilla, and `V` writes the predicate `Pr` into the ancilla
    up to the phase `D`. -/
theorem conj_ring {R : Type*} [Ring R] {Vs V W D Pr P₀ P₁ X A : R}
    (hVs : Vs * V = 1) (hW : W = 1 + P₁ * A) (hDW : Commute D W)
    (hV : V * P₀ = D * (1 + Pr * (X - 1)) * P₀)
    (hPX : Commute Pr X) (hPA : Commute Pr A) (hPP₀ : Commute Pr P₀) (hPP₁ : Commute Pr P₁)
    (hAP₀ : Commute A P₀) (hAP₁ : Commute A P₁) (hAX : Commute A X)
    (hPr : Pr * Pr = Pr) (h10 : P₁ * P₀ = 0) (h1X0 : P₁ * X * P₀ = X * P₀) :
    Vs * W * V * P₀ = (1 + Pr * A) * P₀ := by
  have hPX1 : Commute Pr (X - 1) := hPX.sub_right (Commute.one_right Pr)
  have e1 : P₁ * A * P₀ = 0 := by rw [← hAP₁.eq, mul_assoc, h10, mul_zero]
  have h1 : P₁ * (X - 1) * P₀ = X * P₀ := by rw [mul_sub, mul_one, sub_mul, h1X0, h10, sub_zero]
  have hswap : P₁ * (A * Pr) = Pr * (A * P₁) := by
    rw [← hPA.eq, ← mul_assoc P₁ Pr A, ← hPP₁.eq, mul_assoc Pr P₁ A, ← hAP₁.eq]
  have e2 : P₁ * A * (Pr * (X - 1)) * P₀ = Pr * X * A * P₀ := by
    calc P₁ * A * (Pr * (X - 1)) * P₀ = P₁ * (A * Pr) * (X - 1) * P₀ := by
          simp only [mul_assoc]
      _ = Pr * (A * P₁) * (X - 1) * P₀ := by rw [hswap]
      _ = Pr * A * (P₁ * (X - 1) * P₀) := by simp only [mul_assoc]
      _ = Pr * X * A * P₀ := by
          rw [h1]
          simp only [mul_assoc]
          rw [← mul_assoc A X P₀, hAX.eq, mul_assoc]
  have e3 : Pr * (X - 1) * (Pr * A) = Pr * (X - 1) * A := by
    rw [← mul_assoc, mul_assoc Pr (X - 1) Pr, ← hPX1.eq, ← mul_assoc Pr Pr, hPr]
  have key : W * (1 + Pr * (X - 1)) * P₀ = (1 + Pr * (X - 1)) * (1 + Pr * A) * P₀ := by
    have eL : W * (1 + Pr * (X - 1)) * P₀
        = P₀ + Pr * (X - 1) * P₀ + P₁ * A * P₀ + P₁ * A * (Pr * (X - 1)) * P₀ := by
      rw [hW]; noncomm_ring
    have eR : (1 + Pr * (X - 1)) * (1 + Pr * A) * P₀
        = P₀ + Pr * A * P₀ + Pr * (X - 1) * P₀ + Pr * (X - 1) * (Pr * A) * P₀ := by
      noncomm_ring
    rw [eL, eR, e1, e2, e3]
    noncomm_ring
  have hN : Commute (1 + Pr * A) P₀ := (Commute.one_left P₀).add_left (hPP₀.mul_left hAP₀)
  calc Vs * W * V * P₀ = Vs * (W * (V * P₀)) := by simp only [mul_assoc]
    _ = Vs * (D * (W * (1 + Pr * (X - 1)) * P₀)) := by
        rw [hV]
        simp only [mul_assoc]
        rw [← mul_assoc W D, ← hDW.eq, mul_assoc]
    _ = Vs * (D * ((1 + Pr * (X - 1)) * (1 + Pr * A) * P₀)) := by rw [key]
    _ = Vs * (D * (1 + Pr * (X - 1)) * P₀) * (1 + Pr * A) := by
        rw [mul_assoc (1 + Pr * (X - 1)) (1 + Pr * A) P₀, hN.eq]
        simp only [mul_assoc]
    _ = (1 + Pr * A) * P₀ := by rw [← hV, ← mul_assoc Vs V P₀, hVs, one_mul, hN.eq]

/-- The ancilla construction: compute with `V`, the block `U` controlled on the ancilla `a`,
    uncompute with the inverse of `V`. -/
def ancillaCtrlGates (V : List (Gate n)) (a : Fin n) (U : List (Gate n)) : List (Gate n) :=
  V ++ ctrlList a U ++ invGates V

/-- **Conjugation theorem.** `V` writes the predicate `Π` of the qubits `cs` into the clean
    ancilla `a`, up to a phase `D` on `a :: cs`. Then on ancilla `|0⟩` the circuit
    `V; (U controlled on a); V⁻¹` applies `U` exactly where `Π` holds. -/
theorem listMatrix_predAncilla_conj {cs : List (Fin n)} {a : Fin n}
    {P D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {V U : List (Gate n)}
    (ha : a ∉ cs) (hP : IsPred cs P) (hD : PhaseOn (a :: cs) D)
    (hV : listMatrix V * embedGate1 n a proj0
      = D * (1 + P * (embedGate1 n a pauliX - 1)) * embedGate1 n a proj0)
    (hU : ∀ g ∈ U, Avoids a g ∧ ∀ c ∈ cs, Avoids c g) :
    listMatrix (ancillaCtrlGates V a U) * embedGate1 n a proj0
      = (1 + P * (listMatrix U - 1)) * embedGate1 n a proj0 := by
  have hcU : CommOn a (listMatrix U) := commOn_listMatrix fun g hg => (hU g hg).1
  have hPU : Commute P (listMatrix U) :=
    commute_of_phaseOn hP.1 fun g hg q hq => (hU g hg).2 q hq
  have hDU : Commute D (listMatrix U) := commute_of_phaseOn hD fun g hg q hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (hU g hg).1
    · exact (hU g hg).2 q hq
  have hP₁ : PhaseOn [a] (embedGate1 n a proj1) :=
    phaseOn_embedGate1 List.mem_cons_self isDiagonal_proj1
  have hP₀ : PhaseOn [a] (embedGate1 n a proj0) :=
    phaseOn_embedGate1 List.mem_cons_self isDiagonal_proj0
  have hPX : Commute P (embedGate1 n a pauliX) :=
    hP.1.commute_of_keepsBits (keepsBits_embedGate1 (by rintro q hq rfl; exact ha hq) _)
  have hDW : Commute D (ctrlMatrix a (listMatrix U)) := by
    rw [ctrlMatrix_eq_one_add]
    exact (Commute.one_right D).add_right
      ((hD.commute hP₁).mul_right (hDU.sub_right (Commute.one_right D)))
  have h10 : embedGate1 n a proj1 * embedGate1 n a proj0 = 0 := by
    rw [embedGate1_mul, proj1_mul_proj0, embedGate1_map_zero]
  have h1X0 : embedGate1 n a proj1 * embedGate1 n a pauliX * embedGate1 n a proj0
      = embedGate1 n a pauliX * embedGate1 n a proj0 := by
    rw [embedGate1_mul, embedGate1_mul, embedGate1_mul, proj1_pauliX_proj0]
  rw [ancillaCtrlGates, listMatrix_append, listMatrix_append, listMatrix_invGates,
    listMatrix_ctrlList fun g hg => (hU g hg).1, ← mul_assoc]
  exact conj_ring (listMatrix_conjTranspose_mul V) (ctrlMatrix_eq_one_add a _) hDW hV hPX
    (hPU.sub_right (Commute.one_right P)) (hP.1.commute hP₀) (hP.1.commute hP₁)
    ((CommOn.commute hcU proj0).sub_left (Commute.one_left _))
    ((CommOn.commute hcU proj1).sub_left (Commute.one_left _))
    ((CommOn.commute hcU pauliX).sub_left (Commute.one_left _)) hP.2 h10 h1X0

/-- The ancilla construction returns the ancilla to `|0⟩`. -/
theorem predAncilla_restores {cs : List (Fin n)} {a : Fin n}
    {P D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {V U : List (Gate n)}
    (ha : a ∉ cs) (hP : IsPred cs P) (hD : PhaseOn (a :: cs) D)
    (hV : listMatrix V * embedGate1 n a proj0
      = D * (1 + P * (embedGate1 n a pauliX - 1)) * embedGate1 n a proj0)
    (hU : ∀ g ∈ U, Avoids a g ∧ ∀ c ∈ cs, Avoids c g) :
    embedGate1 n a proj1 * listMatrix (ancillaCtrlGates V a U) * embedGate1 n a proj0 = 0 := by
  have hcU : CommOn a (listMatrix U) := commOn_listMatrix fun g hg => (hU g hg).1
  have hN : Commute (1 + P * (listMatrix U - 1)) (embedGate1 n a proj0) :=
    (Commute.one_left _).add_left ((hP.1.commute
      (phaseOn_embedGate1 (S := [a]) List.mem_cons_self isDiagonal_proj0)).mul_left
      ((CommOn.commute hcU proj0).sub_left (Commute.one_left _)))
  rw [mul_assoc, listMatrix_predAncilla_conj ha hP hD hV hU, hN.eq, ← mul_assoc,
    embedGate1_mul, proj1_mul_proj0, embedGate1_map_zero, zero_mul]

/-! ## The AND of the controls -/

/-- The product of the `|1⟩` projectors of `cs` is the projector of their AND. -/
theorem isPred_prod_proj1 :
    ∀ cs : List (Fin n), IsPred cs (cs.map fun c => embedGate1 n c proj1).prod
  | [] => by
    simp only [List.map_nil, List.prod_nil]
    exact ⟨phaseOn_one _, one_mul 1⟩
  | c :: cs => by
    obtain ⟨hph, hid⟩ := isPred_prod_proj1 cs
    have hc : PhaseOn (c :: cs) (embedGate1 n c proj1) :=
      phaseOn_embedGate1 List.mem_cons_self isDiagonal_proj1
    have hcs := hph.mono (List.subset_cons_self c cs)
    rw [List.map_cons, List.prod_cons]
    refine ⟨hc.mul hcs, ?_⟩
    rw [mul_assoc, ← mul_assoc _ (embedGate1 n c proj1), (hcs.commute hc).eq, mul_assoc, hid,
      ← mul_assoc, embedGate1_mul, proj1_mul_proj1]

/-- **AND ancilla.** With `V` the multi-controlled `X` on the ancilla, the ancilla
    construction is the block controlled on every qubit of `cs`, on ancilla `|0⟩`. -/
theorem listMatrix_andAncilla_conj {cs : List (Fin n)} {a : Fin n} {U : List (Gate n)}
    (hnd : cs.Nodup) (ha : a ∉ cs) (hU : ∀ g ∈ U, Avoids a g ∧ ∀ c ∈ cs, Avoids c g) :
    listMatrix (ancillaCtrlGates (mctrlGates cs (Gate.X a)) a U) * embedGate1 n a proj0
      = mctrlMatrix cs (listMatrix U) * embedGate1 n a proj0 := by
  have hV : listMatrix (mctrlGates cs (Gate.X a))
      = 1 + (cs.map fun c => embedGate1 n c proj1).prod * (embedGate1 n a pauliX - 1) := by
    rw [listMatrix_mctrlGates (g := Gate.X a) hnd fun c hc =>
        (by rintro rfl; exact ha hc : a ≠ c),
      mctrlMatrix_eq]
    rfl
  rw [listMatrix_predAncilla_conj ha (isPred_prod_proj1 cs) (phaseOn_one _)
    (by rw [hV, one_mul]) hU, mctrlMatrix_eq]

/-! ## The relative-phase Toffoli -/

/-- The relative-phase Toffoli with controls `c₁`, `c₂` and target `a` in Clifford+T, with
    four `T` gates and three `CNOT`s:
    `H a; T a; CNOT c₂ a; T† a; CNOT c₁ a; T a; CNOT c₂ a; T† a; H a`. -/
def rtofGates (c₁ c₂ a : Fin n) : List (Gate n) :=
  [.H a, .T a, .CNOT c₂ a, .Tdg a, .CNOT c₁ a, .T a, .CNOT c₂ a, .Tdg a, .H a]

/-- The phase of the relative-phase Toffoli: the identity where `c₁` reads `0`, `Z_a` where
    `c₁ c₂` read `10`, and `-i Z_a` where they read `11`. -/
def rtofPhase (c₁ c₂ a : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ctrlMatrix c₁ (branchMatrix c₂ (embedGate1 n a pauliZ) (embedGate1 n a ((-Complex.I) • pauliZ)))

/-- The phase of the relative-phase Toffoli is diagonal on `[c₁, c₂, a]`. -/
theorem phaseOn_rtofPhase (c₁ c₂ a : Fin n) : PhaseOn [c₁, c₂, a] (rtofPhase c₁ c₂ a) := by
  have hZ : IsDiagonal ((-Complex.I) • pauliZ) := fun r c h => by
    simp [isDiagonal_pauliZ r c h]
  simp only [rtofPhase, ctrlMatrix, branchMatrix]
  exact (phaseOn_embedGate1 (by simp) isDiagonal_proj0).add
    ((phaseOn_embedGate1 (by simp) isDiagonal_proj1).mul
      (((phaseOn_embedGate1 (by simp) isDiagonal_proj0).mul
          (phaseOn_embedGate1 (by simp) isDiagonal_pauliZ)).add
        ((phaseOn_embedGate1 (by simp) isDiagonal_proj1).mul (phaseOn_embedGate1 (by simp) hZ))))

/-- The four-branch matrix on the controls `c₁`, `c₂` with the single-qubit operator `Gᵢⱼ`
    on `a` where `c₁ c₂` read `ij`. -/
def quadMatrix (c₁ c₂ a : Fin n) (G₀₀ G₀₁ G₁₀ G₁₁ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  branchMatrix c₁ (branchMatrix c₂ (embedGate1 n a G₀₀) (embedGate1 n a G₀₁))
    (branchMatrix c₂ (embedGate1 n a G₁₀) (embedGate1 n a G₁₁))

/-- A sum of matrices commuting with the operators on `c` commutes with them. -/
theorem CommOn.add {c : Fin n} {M N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn c M) (hN : CommOn c N) : CommOn c (M + N) := fun G => by
  rw [mul_add, add_mul, hM G, hN G]

/-- A two-branch matrix on `c₂` of operators on `a` commutes with the operators on a third
    qubit `c`. -/
theorem commOn_branchMatrix_embedGate1 {c c₂ a : Fin n} (h : c₂ ≠ c) (ha : a ≠ c)
    (G G' : Matrix (Fin 2) (Fin 2) ℂ) :
    CommOn c (branchMatrix c₂ (embedGate1 n a G) (embedGate1 n a G')) :=
  CommOn.add ((commOn_embedGate1 h proj0).mul (commOn_embedGate1 ha G))
    ((commOn_embedGate1 h proj1).mul (commOn_embedGate1 ha G'))

/-- Four-branch matrices multiply branchwise. -/
theorem quadMatrix_mul {c₁ c₂ a : Fin n} (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ a) (h2a : c₂ ≠ a)
    (G₀₀ G₀₁ G₁₀ G₁₁ H₀₀ H₀₁ H₁₀ H₁₁ : Matrix (Fin 2) (Fin 2) ℂ) :
    quadMatrix c₁ c₂ a G₀₀ G₀₁ G₁₀ G₁₁ * quadMatrix c₁ c₂ a H₀₀ H₀₁ H₁₀ H₁₁
      = quadMatrix c₁ c₂ a (G₀₀ * H₀₀) (G₀₁ * H₀₁) (G₁₀ * H₁₀) (G₁₁ * H₁₁) := by
  rw [quadMatrix, quadMatrix,
    branchMatrix_mul (commOn_branchMatrix_embedGate1 (Ne.symm h12) (Ne.symm h1a) _ _)
      (commOn_branchMatrix_embedGate1 (Ne.symm h12) (Ne.symm h1a) _ _),
    branchMatrix_mul (commOn_embedGate1 (Ne.symm h2a) _) (commOn_embedGate1 (Ne.symm h2a) _),
    branchMatrix_mul (commOn_embedGate1 (Ne.symm h2a) _) (commOn_embedGate1 (Ne.symm h2a) _),
    embedGate1_mul, embedGate1_mul, embedGate1_mul, embedGate1_mul, quadMatrix]

/-- An operator on `a` is the four-branch matrix with the same operator in every branch. -/
theorem embedGate1_eq_quadMatrix (c₁ c₂ a : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n a G = quadMatrix c₁ c₂ a G G G G := by
  rw [quadMatrix, branchMatrix_self, branchMatrix_self]

/-- The `00` branch of the relative-phase Toffoli is the identity. -/
theorem rtof_entry₀₀ :
    hadamard * tDaggerGate * 1 * tGate * 1 * tDaggerGate * 1 * tGate * hadamard
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 := by
  simp only [mul_one]
  rw [mul_assoc hadamard, tDaggerGate_mul_tGate, mul_one, mul_assoc hadamard,
    tDaggerGate_mul_tGate, mul_one, hadamard_sq]

/-- The `01` branch of the relative-phase Toffoli is the identity. -/
theorem rtof_entry₀₁ :
    hadamard * tDaggerGate * pauliX * tGate * 1 * tDaggerGate * pauliX * tGate * hadamard
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 := by
  grind only [= hadamard_sq, = pauliX_sq, = tDaggerGate_mul_tGate, = tGate_mul_tDaggerGate]

/-- The `10` branch of the relative-phase Toffoli is `Z`. -/
theorem rtof_entry₁₀ :
    hadamard * tDaggerGate * 1 * tGate * pauliX * tDaggerGate * 1 * tGate * hadamard
      = pauliZ * (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  grind only [= hadamard_sq, = tDaggerGate_mul_tGate, = hadamard_pauliX_hadamard]

/-- `exp (i π / 4) ^ 2 = i`. -/
theorem exp_pi_div_four_sq :
    Complex.exp (Complex.I * ↑(Real.pi / 4)) * Complex.exp (Complex.I * ↑(Real.pi / 4))
      = Complex.I := by
  rw [← Complex.exp_add, show Complex.I * ↑(Real.pi / 4) + Complex.I * ↑(Real.pi / 4)
    = ↑Real.pi / 2 * Complex.I by push_cast; ring, Complex.exp_pi_div_two_mul_I]

/-- `exp (-i π / 4) ^ 2 = -i`. -/
theorem exp_neg_pi_div_four_sq :
    Complex.exp (-Complex.I * ↑(Real.pi / 4)) * Complex.exp (-Complex.I * ↑(Real.pi / 4))
      = -Complex.I := by
  rw [← Complex.exp_add, show -Complex.I * ↑(Real.pi / 4) + -Complex.I * ↑(Real.pi / 4)
    = -(↑Real.pi / 2 * Complex.I) by push_cast; ring, Complex.exp_neg,
    Complex.exp_pi_div_two_mul_I, Complex.inv_I]

/-- In a monoid, conjugation by an involution is multiplicative. -/
theorem conj_involution_mul {M : Type*} [Monoid M] {h : M} (hh : h * h = 1) (x y : M) :
    h * (x * y) * h = h * x * h * (h * y * h) := by
  simp only [mul_assoc]
  rw [← mul_assoc h h, hh, one_mul]

/-- The middle of the `11` branch of the relative-phase Toffoli for `T = diag(1, w)`,
    `T† = diag(1, v)` with `w² = i`, `v² = -i`. -/
theorem rtof_mid₁₁ (w v : ℂ) (hw : w * w = Complex.I) (hv : v * v = -Complex.I) :
    Matrix.of ![![1, 0], ![0, v]] * pauliX * Matrix.of ![![1, 0], ![0, w]] * pauliX
        * Matrix.of ![![1, 0], ![0, v]] * pauliX * Matrix.of ![![1, 0], ![0, w]]
      = Complex.I • (pauliZ * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, hw, hv]

/-- The `11` branch of the relative-phase Toffoli is `(-i Z) X`. -/
theorem rtof_entry₁₁ :
    hadamard * tDaggerGate * pauliX * tGate * pauliX * tDaggerGate * pauliX * tGate * hadamard
      = ((-Complex.I) • pauliZ) * pauliX := by
  rw [show hadamard * tDaggerGate * pauliX * tGate * pauliX * tDaggerGate * pauliX * tGate
      * hadamard
      = hadamard * (tDaggerGate * pauliX * tGate * pauliX * tDaggerGate * pauliX * tGate)
        * hadamard by simp only [mul_assoc]]
  rw [tGate, tDaggerGate, rtof_mid₁₁ _ _ exp_pi_div_four_sq exp_neg_pi_div_four_sq,
    Matrix.mul_smul, Matrix.smul_mul, conj_involution_mul hadamard_sq,
    hadamard_pauliZ_hadamard, hadamard_pauliX_hadamard]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Relative-phase Toffoli.** The four-`T` circuit is the Toffoli followed by the diagonal
    phase `rtofPhase c₁ c₂ a`. -/
theorem listMatrix_rtofGates {c₁ c₂ a : Fin n} (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ a) (h2a : c₂ ≠ a) :
    listMatrix (rtofGates c₁ c₂ a) = rtofPhase c₁ c₂ a * listMatrix (toffoliGates c₁ c₂ a) := by
  have hx₁ : gateEmbedding (Gate.CNOT c₁ a) = quadMatrix c₁ c₂ a 1 1 pauliX pauliX := by
    rw [gateEmbedding_CNOT h1a, ctrlMatrix_eq_branchMatrix]
    simp only [quadMatrix, embedGate1_one, branchMatrix_self]
  have hx₂ : gateEmbedding (Gate.CNOT c₂ a) = quadMatrix c₁ c₂ a 1 pauliX 1 pauliX := by
    rw [gateEmbedding_CNOT h2a, ctrlMatrix_eq_branchMatrix]
    simp only [quadMatrix, embedGate1_one, branchMatrix_self]
  have htof : listMatrix (toffoliGates c₁ c₂ a) = quadMatrix c₁ c₂ a 1 1 1 pauliX := by
    rw [listMatrix_toffoliGates h12 h1a h2a, embedGate2_cnot h2a, ctrlMatrix_eq_branchMatrix,
      ctrlMatrix_eq_branchMatrix]
    simp only [quadMatrix, embedGate1_one, branchMatrix_self]
  have hph : rtofPhase c₁ c₂ a = quadMatrix c₁ c₂ a 1 1 pauliZ ((-Complex.I) • pauliZ) := by
    rw [rtofPhase, ctrlMatrix_eq_branchMatrix]
    simp only [quadMatrix, embedGate1_one, branchMatrix_self]
  simp only [rtofGates, listMatrix_cons, listMatrix_nil, one_mul]
  rw [hx₁, hx₂]
  simp only [gateEmbedding]
  rw [embedGate1_eq_quadMatrix c₁ c₂ a hadamard, embedGate1_eq_quadMatrix c₁ c₂ a tGate,
    embedGate1_eq_quadMatrix c₁ c₂ a tDaggerGate, htof, hph]
  simp only [quadMatrix_mul h12 h1a h2a]
  rw [rtof_entry₀₀, rtof_entry₀₁, rtof_entry₁₀, rtof_entry₁₁]

/-- **Relative-phase AND ancilla.** With `V` the relative-phase Toffoli on the controls
    `c₁`, `c₂` and the ancilla `a`, the ancilla construction is the block controlled on both
    qubits, on ancilla `|0⟩`. -/
theorem listMatrix_rtofAncilla_conj {c₁ c₂ a : Fin n} {U : List (Gate n)} (h12 : c₁ ≠ c₂)
    (h1a : c₁ ≠ a) (h2a : c₂ ≠ a) (hU : ∀ g ∈ U, Avoids a g ∧ ∀ c ∈ [c₁, c₂], Avoids c g) :
    listMatrix (ancillaCtrlGates (rtofGates c₁ c₂ a) a U) * embedGate1 n a proj0
      = mctrlMatrix [c₁, c₂] (listMatrix U) * embedGate1 n a proj0 := by
  have ha : a ∉ [c₁, c₂] := by simp [Ne.symm h1a, Ne.symm h2a]
  have htof : listMatrix (toffoliGates c₁ c₂ a) = 1 + ([c₁, c₂].map fun c =>
      embedGate1 n c proj1).prod * (embedGate1 n a pauliX - 1) := by
    rw [listMatrix_toffoliGates h12 h1a h2a, embedGate2_cnot h2a, ← mctrlMatrix_eq]
    rfl
  have hD : PhaseOn (a :: [c₁, c₂]) (rtofPhase c₁ c₂ a) :=
    (phaseOn_rtofPhase c₁ c₂ a).mono (by simp [List.subset_def])
  rw [listMatrix_predAncilla_conj ha (isPred_prod_proj1 _) hD
    (by rw [listMatrix_rtofGates h12 h1a h2a, htof]) hU, mctrlMatrix_eq]

/-! ## Length -/

/-- A controlled gate has at most nineteen gates. -/
theorem length_ctrlGates_le (c : Fin n) (g : Gate n) : (ctrlGates c g).length ≤ 19 := by
  cases g <;> simp only [ctrlGates] <;> (try split) <;>
    simp [OpenQASMImport.cphaseGates, cphaseRz, toffoliGates, cczPhaseGates, cnotConj]

/-- The ancilla construction is linear in the block: at most twice the length of `V` plus
    nineteen gates per gate of `U`. -/
theorem length_ancillaCtrlGates (V : List (Gate n)) (a : Fin n) (U : List (Gate n)) :
    (ancillaCtrlGates V a U).length ≤ 2 * V.length + 19 * U.length := by
  have hU : (ctrlList a U).length ≤ 19 * U.length := by
    induction U with
    | nil => simp [ctrlList]
    | cons g U ih =>
      rw [ctrlList, List.flatMap_cons, List.length_append, ← ctrlList, List.length_cons]
      have := length_ctrlGates_le a g
      omega
  rw [ancillaCtrlGates, List.length_append, List.length_append, length_invGates]
  omega

end CatCrypt.Quantum.AndAncilla
