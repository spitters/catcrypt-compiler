/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.CommuteSound
public import CatCrypt.Quantum.Optimization.UnitarySound
public import CatCrypt.Quantum.Optimization.CommutationRules
public import CatCrypt.Quantum.Optimization.MixedCommute
public import CatCrypt.Quantum.Optimization.ControlCommute
public import CatCrypt.Quantum.Optimization.MatrixCorrect
public import CatCrypt.Quantum.Optimization.FusionSound

/-!
# Real-semantics soundness of the `commuteAndMerge` optimizer pass

`CommutationRules.commuteAndMerge` flattens a circuit to a gate list, runs a
single `mergePass`, and rebuilds the circuit (`Circuit.ofList`). The `mergePass`
walks the list and, for each `Rz` rotation, uses `tryMergeRz` to thread the
rotation forward past *commuting* gates (as certified by `gateCommutes`) until
it meets another `Rz` on the same qubit, which it merges by adding angles.

The pass is stated against the unitary-channel semantics `unitaryDenote`
(ρ ↦ UρU†, `GateUnitarity.unitaryDenote`), yielding

* `commuteAndMerge_unitaryCorrect : UnitaryCorrectQ commuteAndMerge`.

The argument reuses the list-denotation engine from `UnitarySound`
(`unitaryDenote_ofList_append`, `unitaryDenote_circuitToList`) together with two
gate-level facts:

* a **cons-swap** lemma: if `denoteGateU g₁` and `denoteGateU g₂` commute under
  `qbind`, the two orders agree at the head of any gate list;
* a **merge** lemma: two same-qubit `Rz` rotations compose to a single `Rz`
  with summed angle (`rzGate θ₂ * rzGate θ₁ = rzGate (θ₁ + θ₂)`).

The commutation side-conditions accepted by `gateCommutes` for an `Rz` on the
left are discharged by `CommuteSound.diag_same_qubit_commuteU` (same-qubit
diagonal gates), `CommuteSound.embedGate1_disjoint_comm` (disjoint single-qubit
gates). The case of `Rz` commuting with a two-qubit
gate (`CNOT`/`CZ`) — on disjoint qubits, or, for `CZ`, diagonal-vs-diagonal on a
shared qubit, or, for `CNOT`, on the control wire — is `rz_twoQubit_commuteU`,
discharged via the `embedGate1`/`embedGate2` bridge lemmas in `MixedCommute`
(`embedGate1_embedGate2_disjoint_comm` and `embedGate1_embedGate2_diag_comm`)
and `ControlCommute.gateEmbedding_cnot_diag_control_comm`.

## Main results

* `commuteAndMerge_unitaryCorrect` — the pass `commuteAndMerge` preserves `unitaryDenote`.
* `unitaryDenote_commuteAndMerge` — `unitaryDenote (commuteAndMerge c) = unitaryDenote c`.
* `mergePass_correctU` — the gate-list pass `mergePass` preserves the denotation of the list.
* `tryMergeRz_correctU` — threading one `Rz` rotation forward with `tryMergeRz` preserves
  the denotation.
* `unitaryDenote_cons_swap` — two gates whose denotations commute may be swapped at the head
  of a gate list.
* `unitaryDenote_merge_rz` — two adjacent `Rz` rotations on one qubit denote the single
  rotation by the sum of their angles.
* `rz_gateCommutes_commuteU` — an `Rz` rotation and a gate that `gateCommutes` accepts
  commute under the unitary-channel semantics.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.CommutationRules
open CatCrypt.Quantum.Optimization.UnitarySound

noncomputable section

namespace CatCrypt.Quantum.Optimization.CommuteMergeSound

open CatCrypt.Quantum.Optimization.CommuteSound
open CatCrypt.Quantum.Optimization.RoutingPerm (circuitUnitary)
open CatCrypt.Quantum.Optimization.MatrixSound

variable {n : ℕ}

/-! ## Gate-pair commutation under the real unitary semantics -/

/-- Two gates **commute under the unitary semantics** if their `denoteGateU`
channels commute as a `qbind` (equivalently their unitary matrices commute up
to the channel). -/
def GateCommutesU (g₁ g₂ : Gate n) : Prop :=
  QComp.qbind (denoteGateU g₁) (fun _ => denoteGateU g₂)
    = QComp.qbind (denoteGateU g₂) (fun _ => denoteGateU g₁)

/-- `GateCommutesU` lifts to a head-swap of any gate list under `unitaryDenote`:
swapping two commuting gates at the front of a list preserves the denotation. -/
theorem unitaryDenote_cons_swap {g₁ g₂ : Gate n} (h : GateCommutesU g₁ g₂)
    (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (g₁ :: g₂ :: gs))
      = unitaryDenote (Circuit.ofList (g₂ :: g₁ :: gs)) := by
  show QComp.qbind (denoteGateU g₁)
        (fun _ => QComp.qbind (denoteGateU g₂)
          (fun _ => unitaryDenote (Circuit.ofList gs)))
     = QComp.qbind (denoteGateU g₂)
        (fun _ => QComp.qbind (denoteGateU g₁)
          (fun _ => unitaryDenote (Circuit.ofList gs)))
  rw [← QComp.qbind_assoc, ← QComp.qbind_assoc, h]

/-! ## Same-qubit diagonal gates commute under `unitaryDenote` -/

/-- Gates with commuting embeddings commute under `unitaryDenote`. -/
theorem gateCommutesU_of_gateEmbedding_comm {g₁ g₂ : Gate n}
    (h : gateEmbedding g₂ * gateEmbedding g₁ = gateEmbedding g₁ * gateEmbedding g₂) :
    GateCommutesU g₁ g₂ := by
  unfold GateCommutesU
  have e₁ : (fun (_ : Unit) => denoteGateU (n := n) g₂)
          = (fun () => denoteGateU g₂) := funext (fun () => rfl)
  have e₂ : (fun (_ : Unit) => denoteGateU (n := n) g₁)
          = (fun () => denoteGateU g₁) := funext (fun () => rfl)
  rw [e₁, denoteGateU_compose, e₂, denoteGateU_compose]
  exact congrArg _ (Subtype.ext h)

/-- For two diagonal single-qubit gates on the same qubit, `GateCommutesU`
holds. This repackages `CommuteSound.gateEmbedding_unitaryGroup_diag_comm`. -/
theorem gateCommutesU_diag {q : Fin n} {g₁ g₂ : Gate n}
    (h₁ : IsDiagOn q g₁) (h₂ : IsDiagOn q g₂) : GateCommutesU g₁ g₂ := by
  unfold GateCommutesU
  have e₁ : (fun (_ : Unit) => denoteGateU (n := n) g₂)
          = (fun () => denoteGateU g₂) := funext (fun () => rfl)
  have e₂ : (fun (_ : Unit) => denoteGateU (n := n) g₁)
          = (fun () => denoteGateU g₁) := funext (fun () => rfl)
  rw [e₁, denoteGateU_compose, e₂, denoteGateU_compose,
    gateEmbedding_unitaryGroup_diag_comm h₁ h₂]

/-- Disjoint-qubit single-qubit gates commute under `unitaryDenote`. -/
theorem gateCommutesU_disjoint_embed1 {i j : Fin n} (hij : i ≠ j)
    (G H : Matrix (Fin 2) (Fin 2) ℂ)
    {g₁ g₂ : Gate n}
    (h₁ : gateEmbedding g₁ = embedGate1 n i G)
    (h₂ : gateEmbedding g₂ = embedGate1 n j H) : GateCommutesU g₁ g₂ :=
  gateCommutesU_of_gateEmbedding_comm (by rw [h₁, h₂, embedGate1_disjoint_comm hij.symm H G])

/-! ## `Rz` rotation merge: angles add -/

/-- Two `Rz` rotation matrices on the same qubit compose by adding angles:
`rzGate θ₂ * rzGate θ₁ = rzGate (θ₁ + θ₂)` (`FusionSound.rzGate_mul`). -/
theorem rzGate_mul_rzGate (θ₁ θ₂ : ℝ) :
    rzGate θ₂ * rzGate θ₁ = rzGate (θ₁ + θ₂) := by
  rw [FusionSound.rzGate_mul, add_comm]

/-- Merging two same-qubit `Rz` rotations at the head of a gate list preserves the
unitary: the angles add. -/
theorem circuitUnitary_merge_rz (i : Fin n) (θ φ : ℝ) (gs : List (Gate n)) :
    circuitUnitary (Circuit.ofList (Gate.Rz i θ :: Gate.Rz i φ :: gs)) =
      circuitUnitary (Circuit.ofList (Gate.Rz i (θ + φ) :: gs)) := by
  simp only [circuitUnitary_ofList_cons, mul_assoc]
  congr 1
  apply Subtype.ext
  change embedGate1 n i (rzGate φ) * embedGate1 n i (rzGate θ) =
    embedGate1 n i (rzGate (θ + φ))
  rw [embedGate1_mul, rzGate_mul_rzGate]

/-- Merging two same-qubit `Rz` rotations preserves `unitaryDenote` at the head
of a gate list: `Rz i θ₁ ; Rz i θ₂ ; gs ≡ Rz i (θ₁ + θ₂) ; gs`. -/
theorem unitaryDenote_merge_rz (i : Fin n) (θ₁ θ₂ : ℝ) (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (Gate.Rz i θ₁ :: Gate.Rz i θ₂ :: gs))
      = unitaryDenote (Circuit.ofList (Gate.Rz i (θ₁ + θ₂) :: gs)) :=
  unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_merge_rz i θ₁ θ₂ gs)

/-! ## `Rz` past a gate `gateCommutes` accepts, at the matrix -/

/-- **Mixed-arity commutation**: an `Rz` rotation on qubit `q` commutes with a
two-qubit gate `g₂` (`CNOT`/`CZ`) whenever the conservative checker
`gateCommutes` certifies the pair commutes.  There are three routes, one per
acceptance of the checker: the two-qubit gate acts on qubits disjoint from `q`
(tensor-disjointness); `g₂ = CZ` is diagonal and so commutes with the diagonal
`Rz` even on a shared qubit; or `g₂ = CNOT q t` and `q` is the control wire, on
which both gates are diagonal. -/
theorem gateEmbedding_rz_twoQubit_comm {q : Fin n} (θ : ℝ) {g₂ : Gate n}
    (htwo : ∃ i j, g₂ = Gate.CNOT i j ∨ g₂ = Gate.CZ i j)
    (h : gateCommutes (Gate.Rz q (0 : ℝ)) g₂ = true) :
    gateEmbedding (Gate.Rz q θ) * gateEmbedding g₂
      = gateEmbedding g₂ * gateEmbedding (Gate.Rz q θ) := by
  -- `rzGate θ = diag(1, e^{iθ})` and `czGate = diag(1,1,1,-1)` are diagonal.
  have hrzDiag : MixedCommute.IsDiagonal (rzGate θ) := by
    intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [rzGate]
  have hczDiag : MixedCommute.IsDiagonal czGate := by
    intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [czGate]
  -- The `Rz` embedding is `embedGate1 n q (rzGate θ)`.
  have hRz : gateEmbedding (Gate.Rz q θ) = embedGate1 n q (rzGate θ) := rfl
  rw [hRz]
  obtain ⟨i, j, hg | hg⟩ := htwo <;> subst hg
  · -- CNOT case: `gateCommutes` certifies either that `q` is disjoint from
    -- `{i, j}`, or that `q = i` is the control wire.
    by_cases hij : i = j
    · -- degenerate `i = j`: embedding is the identity.
      subst hij; simp [gateEmbedding]
    · simp only [gateEmbedding, dite_eq_right hij]
      by_cases hqi : q = i
      · subst hqi
        exact ControlCommute.embedGate1_embedGate2_control_comm hij θ
      · have hcomm : disjointQubits (Gate.Rz q 0) (Gate.CNOT i j) = true := by
          by_contra hd
          simp only [gateCommutes, hd, isDiagonal, Bool.and_false,
            ite_false] at h
          exact absurd h (by simp [hqi])
        simp only [disjointQubits, targetQubits, List.all_cons, List.all_nil,
          List.contains_cons, List.contains_nil, Bool.and_true, Bool.not_or,
          Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hcomm
        exact MixedCommute.embedGate1_embedGate2_disjoint_comm hcomm.1 hcomm.2.1 hij _ _
  · -- CZ case: either disjoint, or both-diagonal (CZ is diagonal).
    by_cases hij : i = j
    · subst hij; simp [gateEmbedding]
    · simp only [gateEmbedding, dite_eq_right hij]
      exact MixedCommute.embedGate1_embedGate2_diag_comm hij hrzDiag hczDiag

/-- The embedding of any gate `g` that `gateCommutes` with `Rz q` commutes with
the embedding of `Rz q θ` (the abstract angle `θ` is irrelevant to commutation,
only the conservative `gateCommutes` flag matters).  Single-qubit cases are
discharged in full (same-qubit diagonal via `embedGate1_diagB_comm`, disjoint
via `embedGate1_disjoint_comm`); the two-qubit cases route through the residual
`gateEmbedding_rz_twoQubit_comm`. -/
theorem gateEmbedding_rz_comm {q : Fin n} {g : Gate n} (θ : ℝ)
    (h : gateCommutes (Gate.Rz q (0 : ℝ)) g = true) :
    gateEmbedding (Gate.Rz q θ) * gateEmbedding g
      = gateEmbedding g * gateEmbedding (Gate.Rz q θ) := by
  -- The non-diagonal single-qubit gates (`H`, `X`, `Y`) commute with
  -- `Rz q` only on a *disjoint* qubit; `gateCommutes = true` forces `q ≠ i`.
  have disjointCase : ∀ (i : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ),
      q ≠ i →
      embedGate1 n q (rzGate θ) * embedGate1 n i M
        = embedGate1 n i M * embedGate1 n q (rzGate θ) :=
    fun i M hqi => embedGate1_disjoint_comm hqi (rzGate θ) M
  -- The diagonal single-qubit gates (`Z`, `S`, `T`, `Tdg`, `Rz`) commute with
  -- `Rz q` on the *same* or any other qubit (diagonal matrices commute).
  have diagCase : ∀ (i : Fin n) (b : ℂ),
      embedGate1 n q (rzGate θ) * embedGate1 n i (diagB b)
        = embedGate1 n i (diagB b) * embedGate1 n q (rzGate θ) := by
    intro i b
    by_cases hqi : q = i
    · subst hqi; rw [rzGate_eq_diagB]; exact embedGate1_diagB_comm q _ b
    · exact embedGate1_disjoint_comm hqi (rzGate θ) (diagB b)
  cases g with
  | H i =>
    have hqi : q ≠ i := by
      intro he; subst he
      simp [gateCommutes, disjointQubits, targetQubits, isDiagonal] at h
    show embedGate1 n q (rzGate θ) * embedGate1 n i _
      = embedGate1 n i _ * embedGate1 n q (rzGate θ)
    exact disjointCase i _ hqi
  | X i =>
    have hqi : q ≠ i := by
      intro he; subst he
      simp [gateCommutes, disjointQubits, targetQubits, isDiagonal] at h
    show embedGate1 n q (rzGate θ) * embedGate1 n i _
      = embedGate1 n i _ * embedGate1 n q (rzGate θ)
    exact disjointCase i _ hqi
  | Y i =>
    have hqi : q ≠ i := by
      intro he; subst he
      simp [gateCommutes, disjointQubits, targetQubits, isDiagonal] at h
    show embedGate1 n q (rzGate θ) * embedGate1 n i _
      = embedGate1 n i _ * embedGate1 n q (rzGate θ)
    exact disjointCase i _ hqi
  | Z i =>
    show embedGate1 n q (rzGate θ) * gateEmbedding (Gate.Z i)
      = gateEmbedding (Gate.Z i) * embedGate1 n q (rzGate θ)
    rw [show gateEmbedding (Gate.Z i) = embedGate1 n i (diagB (-1)) by
      simp only [gateEmbedding, pauliZ_eq_diagB]]
    exact diagCase i (-1)
  | S i =>
    show embedGate1 n q (rzGate θ) * gateEmbedding (Gate.S i)
      = gateEmbedding (Gate.S i) * embedGate1 n q (rzGate θ)
    rw [show gateEmbedding (Gate.S i) = embedGate1 n i (diagB Complex.I) by
      simp only [gateEmbedding, phaseS_eq_diagB]]
    exact diagCase i Complex.I
  | T i =>
    show embedGate1 n q (rzGate θ) * gateEmbedding (Gate.T i)
      = gateEmbedding (Gate.T i) * embedGate1 n q (rzGate θ)
    rw [show gateEmbedding (Gate.T i)
        = embedGate1 n i (diagB (Complex.exp (Complex.I * ↑(Real.pi / 4)))) by
      simp only [gateEmbedding, tGate_eq_diagB]]
    exact diagCase i _
  | Tdg i =>
    show embedGate1 n q (rzGate θ) * gateEmbedding (Gate.Tdg i)
      = gateEmbedding (Gate.Tdg i) * embedGate1 n q (rzGate θ)
    rw [show gateEmbedding (Gate.Tdg i)
        = embedGate1 n i (diagB (Complex.exp (-Complex.I * ↑(Real.pi / 4)))) by
      simp only [gateEmbedding, tDaggerGate_eq_diagB]]
    exact diagCase i _
  | Rz i α =>
    show embedGate1 n q (rzGate θ) * embedGate1 n i (rzGate α)
      = embedGate1 n i (rzGate α) * embedGate1 n q (rzGate θ)
    rw [rzGate_eq_diagB α]
    exact diagCase i _
  | RzQ i a =>
    change embedGate1 n q (rzGate θ) * embedGate1 n i (rzGate (PiLin.toReal a))
      = embedGate1 n i (rzGate (PiLin.toReal a)) * embedGate1 n q (rzGate θ)
    rw [rzGate_eq_diagB (PiLin.toReal a)]
    exact diagCase i _
  | CNOT i j =>
    exact gateEmbedding_rz_twoQubit_comm θ ⟨i, j, Or.inl rfl⟩ h
  | CZ i j =>
    exact gateEmbedding_rz_twoQubit_comm θ ⟨i, j, Or.inr rfl⟩ h

/-- `gateCommutes (Rz i θ) g` does not depend on the angle `θ`. -/
theorem gateCommutes_rz_angle (i : Fin n) (θ : ℝ) (g : Gate n) :
    gateCommutes (Gate.Rz i θ) g = gateCommutes (Gate.Rz i 0) g := by
  cases g <;> rfl

/-- An `Rz i θ` and a gate it `gateCommutes` with have commuting embeddings. -/
theorem gateEmbedding_rz_comm_of_gateCommutes {i : Fin n} {θ : ℝ} {g : Gate n}
    (hc : gateCommutes (Gate.Rz i θ) g = true) :
    gateEmbedding g * gateEmbedding (Gate.Rz i θ) =
      gateEmbedding (Gate.Rz i θ) * gateEmbedding g :=
  (gateEmbedding_rz_comm θ (gateCommutes_rz_angle i θ g ▸ hc)).symm

/-! ## Residual: `Rz` past a two-qubit gate (`CNOT`/`CZ`)

`tryMergeRz` may thread an `Rz i θ` past a `CNOT`/`CZ` gate when `gateCommutes`
accepts it — because the two-qubit gate is on disjoint qubits
(`disjointQubits`), because for `CZ` both are diagonal in the computational
basis, or because for `CNOT` the rotation sits on the control wire. In the
disjoint case the `embedGate1` and `embedGate2` factors act on disjoint bit
positions (`MixedCommute.embedGate1_embedGate2_disjoint_comm`); in the
shared-`CZ` case both embeddings are diagonal matrices, which always commute
(`MixedCommute.embedGate1_embedGate2_diag_comm`, with `rzGate`/`czGate`
diagonal); the control case is
`ControlCommute.gateEmbedding_cnot_diag_control_comm`. -/
theorem rz_twoQubit_commuteU (i : Fin n) (θ : ℝ) (g : Gate n)
    (htwo : (∃ a b, g = Gate.CNOT a b) ∨ (∃ a b, g = Gate.CZ a b))
    (hc : gateCommutes (Gate.Rz i θ) g = true) :
    GateCommutesU (Gate.Rz i θ) g :=
  gateCommutesU_of_gateEmbedding_comm (gateEmbedding_rz_twoQubit_comm θ
    (by rcases htwo with ⟨a, b, h⟩ | ⟨a, b, h⟩; exacts [⟨a, b, .inl h⟩, ⟨a, b, .inr h⟩])
    (gateCommutes_rz_angle i θ g ▸ hc)).symm

/-! ## Master gate-pair commutation: `Rz` past any `gateCommutes`-accepted gate -/

/-- A single-qubit-target gate `g` with target `j ≠ i` commutes with `Rz i θ`
under `unitaryDenote` (disjoint single-qubit embeddings). -/
theorem rz_single_disjoint_commuteU {i j : Fin n} (θ : ℝ) (hij : i ≠ j)
    {g : Gate n} {H : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : gateEmbedding g = embedGate1 n j H) :
    GateCommutesU (Gate.Rz i θ) g :=
  gateCommutesU_disjoint_embed1 hij (rzGate θ) H (by simp [gateEmbedding]) hg

/-- **Master soundness of the `gateCommutes` heuristic for an `Rz` on the left**,
under the real unitary semantics: whenever `gateCommutes (Rz i θ) g` returns
`true`, the gates commute under `GateCommutesU` (hence `unitaryDenote`). -/
theorem rz_gateCommutes_commuteU (i : Fin n) (θ : ℝ) (g : Gate n)
    (hc : gateCommutes (Gate.Rz i θ) g = true) :
    GateCommutesU (Gate.Rz i θ) g :=
  gateCommutesU_of_gateEmbedding_comm (gateEmbedding_rz_comm_of_gateCommutes hc)

/-! ## `unitaryDenote` is a head-congruence over gate lists -/

/-- `unitaryDenote (ofList (g :: xs))` factors as `denoteGateU g` bound to the
denotation of the tail. -/
theorem unitaryDenote_ofList_cons (g : Gate n) (xs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (g :: xs))
      = QComp.qbind (denoteGateU g) (fun _ => unitaryDenote (Circuit.ofList xs)) :=
  rfl

/-- Equal tail denotations give equal `g :: ·` denotations. -/
theorem unitaryDenote_cons_congr (g : Gate n) {xs ys : List (Gate n)}
    (h : unitaryDenote (Circuit.ofList xs) = unitaryDenote (Circuit.ofList ys)) :
    unitaryDenote (Circuit.ofList (g :: xs))
      = unitaryDenote (Circuit.ofList (g :: ys)) := by
  rw [unitaryDenote_ofList_cons, unitaryDenote_ofList_cons, h]

/-! ## `tryMergeRz` preserves `unitaryDenote` -/

/-- Threading an `Rz i θ` through `tryMergeRz` preserves the unitary: when the merge
succeeds with result `gs'`, `Rz i θ :: gs` and `gs'` realize one unitary. -/
theorem circuitUnitary_tryMergeRz (i : Fin n) (θ : ℝ) :
    ∀ {gs gs' : List (Gate n)}, tryMergeRz i θ gs = some gs' →
      circuitUnitary (Circuit.ofList (Gate.Rz i θ :: gs))
        = circuitUnitary (Circuit.ofList gs')
  | [], _, h => by simp [tryMergeRz] at h
  | g :: gs, gs', h => by
      simp only [tryMergeRz] at h
      cases hrz : asRz g with
      | some p =>
        obtain ⟨j, φ⟩ := p
        have hgRz : g = Gate.Rz j φ := by
          cases g <;> simp only [asRz, Option.some.injEq, Prod.mk.injEq,
            reduceCtorEq] at hrz
          obtain ⟨hi, hθ⟩ := hrz; subst hi; subst hθ; rfl
        subst hgRz
        simp only [asRz] at h
        by_cases hij : i = j
        · subst hij
          simp only [decide_true, ite_true, Option.some.injEq] at h
          subst h
          exact circuitUnitary_merge_rz i θ φ gs
        · rw [ite_eq_right (by simpa using hij)] at h
          by_cases hcom : gateCommutes (Gate.Rz i θ) (Gate.Rz j φ) = true
          · rw [ite_eq_left hcom] at h
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨rest', hrest', rfl⟩ := h
            rw [circuitUnitary_ofList_swap (gateEmbedding_rz_comm_of_gateCommutes hcom) gs]
            exact circuitUnitary_ofList_cons_congr (Gate.Rz j φ)
              (circuitUnitary_tryMergeRz i θ hrest')
          · rw [ite_eq_right hcom] at h; exact absurd h (by simp)
      | none =>
        rw [hrz] at h
        by_cases hcom : gateCommutes (Gate.Rz i θ) g = true
        · rw [ite_eq_left hcom] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨rest', hrest', rfl⟩ := h
          rw [circuitUnitary_ofList_swap (gateEmbedding_rz_comm_of_gateCommutes hcom) gs]
          exact circuitUnitary_ofList_cons_congr g (circuitUnitary_tryMergeRz i θ hrest')
        · rw [ite_eq_right hcom] at h; exact absurd h (by simp)

/-- Threading an `Rz i θ` through `tryMergeRz` — past commuting gates and into a
matching `Rz` to merge — preserves `unitaryDenote`: if the merge succeeds with
result `gs'`, then `Rz i θ :: gs` and `gs'` have the same denotation. -/
theorem tryMergeRz_correctU (i : Fin n) (θ : ℝ) :
    ∀ {gs gs' : List (Gate n)}, tryMergeRz i θ gs = some gs' →
      unitaryDenote (Circuit.ofList (Gate.Rz i θ :: gs))
        = unitaryDenote (Circuit.ofList gs') :=
  fun h => unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_tryMergeRz i θ h)

/-! ## Flattening (`CommutationRules.circuitToList`) preserves `unitaryDenote` -/

/-- Flattening a circuit via `CommutationRules.circuitToList` and rebuilding with
`ofList` preserves `unitaryDenote`. (Mirrors `UnitarySound.unitaryDenote_circuitToList`
for the `CommutationRules` flattener, which `commuteAndMerge` actually uses.) -/
theorem unitaryDenote_circuitToList' (c : Circuit n) :
    unitaryDenote (Circuit.ofList (circuitToList c)) = unitaryDenote c :=
  unitaryDenote_eq_of_circuitUnitary_eq
    (circuitUnitary_ofList_flatten _ rfl (fun _ _ => rfl) (fun _ _ => rfl) c)

/-! ## `mergePass` preserves `unitaryDenote` -/

/-- One `mergePass` over a gate list preserves the unitary. -/
theorem circuitUnitary_mergePass :
    ∀ (fuel : ℕ) (gs : List (Gate n)),
      circuitUnitary (Circuit.ofList (mergePass gs fuel))
        = circuitUnitary (Circuit.ofList gs)
  | 0, gs => by simp only [mergePass]
  | fuel + 1, gs => by
      cases gs with
      | nil => simp only [mergePass]
      | cons g rest =>
        rw [show mergePass (g :: rest) (fuel + 1)
              = (match asRz g with
                 | some (i, θ) =>
                   match tryMergeRz i θ rest with
                   | some rest' => mergePass rest' fuel
                   | none => g :: mergePass rest fuel
                 | none => g :: mergePass rest fuel) from rfl]
        split
        · next i θ hrz =>
          have hgRz : g = Gate.Rz i θ := by
            cases g <;> simp only [asRz, Option.some.injEq, Prod.mk.injEq,
              reduceCtorEq] at hrz
            obtain ⟨hi, hθ⟩ := hrz; subst hi; subst hθ; rfl
          split
          · next rest' hmerge =>
            rw [circuitUnitary_mergePass fuel rest', hgRz]
            exact (circuitUnitary_tryMergeRz i θ hmerge).symm
          · exact circuitUnitary_ofList_cons_congr g (circuitUnitary_mergePass fuel rest)
        · exact circuitUnitary_ofList_cons_congr g (circuitUnitary_mergePass fuel rest)

/-- One `mergePass` over a gate list preserves `unitaryDenote (ofList ·)`:
each `Rz`-merge it performs is justified by `tryMergeRz_correctU`, and every
other step keeps the head gate unchanged. -/
theorem mergePass_correctU :
    ∀ (fuel : ℕ) (gs : List (Gate n)),
      unitaryDenote (Circuit.ofList (mergePass gs fuel))
        = unitaryDenote (Circuit.ofList gs) :=
  fun fuel gs => unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_mergePass fuel gs)

/-! ## Main theorem: `commuteAndMerge` is unitary-correct -/

/-- `commuteAndMerge` preserves `circuitUnitary`. -/
theorem commuteAndMerge_matrixCorrect :
    MatrixCorrect (commuteAndMerge : Circuit n → Circuit n) := by
  intro c
  unfold commuteAndMerge
  rw [circuitUnitary_mergePass,
    circuitUnitary_ofList_flatten _ rfl (fun _ _ => rfl) (fun _ _ => rfl) c]

/-- `commuteAndMerge` preserves `unitaryDenote`: flattening, one merge pass, and
rebuilding yield a circuit with the same unitary-channel denotation. -/
theorem unitaryDenote_commuteAndMerge (c : Circuit n) :
    unitaryDenote (commuteAndMerge c) = unitaryDenote c :=
  unitaryDenote_eq_of_circuitUnitary_eq (commuteAndMerge_matrixCorrect c)

/-- **`commuteAndMerge` is correct under the unitary-channel semantics.**

`UnitaryCorrectQ` for `unitaryDenote` (ρ ↦ UρU†): the reordering of commuting
gates and the merging of same-qubit `Rz` rotations both preserve the unitary
denotation. -/
theorem commuteAndMerge_unitaryCorrect :
    UnitaryCorrectQ (commuteAndMerge : Circuit n → Circuit n) :=
  commuteAndMerge_matrixCorrect.unitaryCorrectQ

end CatCrypt.Quantum.Optimization.CommuteMergeSound
