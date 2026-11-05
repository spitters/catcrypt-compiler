/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.Optimization.HardwareRouting
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Qubit-permutation infrastructure for Hardware Routing

The hardware-routing pass `insertSwaps` (in `HardwareRouting.lean`) inserts
SWAP gates so that every two-qubit gate of a circuit acts on a pair of qubits
adjacent in a coupling graph, wrapping each non-adjacent two-qubit gate `g` on
`(i, j)` as `swapGate i mid ; g.relabel i mid ; swapGate i mid`
(`mid = findCloserNeighbor cg i j`). Under the unitary semantics
`unitaryDenote` (`GateUnitarity.lean`) the SWAP unitary `S` is self-inverse and
the relabelled middle gate undoes the conjugation, so the block realizes
`S · U_{g.relabel} · S = U_g` — the gate's action is preserved while it now runs
on an adjacent pair.

This file develops the unitary/permutation substrate used by that argument:
`circuitUnitary` (the single unitary a circuit realizes) with its
`unitaryDenote` characterization, the qubit-permutation unitary
`qubitPermUnitary σ` and its conjugation channel, and the SWAP self-inverse
fact `swapGate_unitary_self_inverse`. The braiding identity
`SwapConj.swapConj_relabel` (proved downstream, where the embedding/permutation
bridge is available) consumes this substrate, and the end-to-end
preservation theorems for `routeGate`/`insertSwaps` live in `SwapConj.lean`.

The "up to qubit permutation" infrastructure (`unitaryEquivPerm`, `permConj`,
`permChannel`, `permConj_unitaryChannel`) is built on the channel semantics
and kept for reuse: it is the right frame for any route that threads
a *running* permutation re-mapping subsequent gates.

## Qubit-permutation unitary

A permutation `σ : Equiv.Perm (Fin n)` of qubit labels induces a
permutation `qubitBitPerm σ : Equiv.Perm (Fin (2 ^ n))` of computational
basis states, by relabeling bit positions through the standard equivalence
`finFunctionFinEquiv : (Fin n → Fin 2) ≃ Fin (2 ^ n)`. Its permutation
matrix `qubitPermMatrix σ` is unitary, giving a `permChannel σ` — the
conjugation channel `ρ ↦ P_σ ρ P_σᴴ`.

## Main definitions

* `circuitUnitary`     — the single unitary realized by a circuit, with
  `unitaryDenote_eq_channel : unitaryDenote c = unitaryChannel (circuitUnitary c)`
* `qubitBitPerm σ`     — basis-state permutation induced by qubit permutation `σ`
* `qubitPermUnitary σ` — its permutation matrix as a unitary-group element
* `permChannel σ`      — the conjugation channel `ρ ↦ P_σ ρ P_σᴴ`
* `unitaryEquivPerm c c' σ` — `unitaryDenote c'` equals `unitaryDenote c`
  conjugated by `permChannel σ`

## Main results

* `permChannel_one`         — `permChannel 1 = qpure ()` (identity channel)
* `unitaryEquivPerm_refl`   — reflexivity at `σ = 1`
* `unitaryEquivPerm_trans`  — composition along permutation product
* `permConj_unitaryChannel` — `permConj σ` of a unitary channel is the channel
  of the matrix-conjugated unitary `P_σ · U · P_{σ⁻¹}`
* `swapGate_unitary_self_inverse` — `SWAP² = I` under `unitaryDenote`

## References

* Hietala et al. — A Verified Optimizer for Quantum Circuits (POPL 2021)
* Watrous — The Theory of Quantum Information, §2.2 (unitary channels)
* Nielsen & Chuang — Quantum Computation and Quantum Information, §1.3 (SWAP)
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix
open CatCrypt.Quantum CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.HardwareRouting

noncomputable section

namespace CatCrypt.Quantum.Optimization.RoutingPerm

variable {n : ℕ}

/-! ## Circuit as a single unitary

Every circuit's `unitaryDenote` is a unitary channel `ρ ↦ U ρ Uᴴ`. We make
the unitary `U` explicit so that conjugation by a qubit permutation can be
expressed at the matrix level. -/

/-- The single unitary-group element realized by a circuit. Gates compose by
    matrix multiplication in run order: the later gate multiplies on the left
    (matching `unitaryChannel_compose`). -/
def circuitUnitary : Circuit n → Matrix.unitaryGroup (Fin (2 ^ n)) ℂ
  | .empty      => 1
  | .gate g c   => circuitUnitary c * gateEmbedding_unitaryGroup g
  | .seq c₁ c₂  => circuitUnitary c₂ * circuitUnitary c₁

/-- `unitaryDenote` of a circuit is the unitary channel of `circuitUnitary`. -/
theorem unitaryDenote_eq_channel (c : Circuit n) :
    unitaryDenote c = unitaryChannel (circuitUnitary c) := by
  induction c with
  | empty =>
    show QComp.qpure () = unitaryChannel (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    rw [unitaryChannel_one_eq_qpure]
  | gate g c ih =>
    show QComp.qbind (denoteGateU g) (fun _ => unitaryDenote c) = _
    simp only [ih, denoteGateU]
    have heta : (fun (_ : Unit) => unitaryChannel (circuitUnitary c)) =
        (fun () => unitaryChannel (circuitUnitary c)) := funext (fun () => rfl)
    rw [heta, unitaryChannel_compose]
    rfl
  | seq c₁ c₂ ih₁ ih₂ =>
    show QComp.qbind (unitaryDenote c₁) (fun _ => unitaryDenote c₂) = _
    simp only [ih₁, ih₂]
    have heta : (fun (_ : Unit) => unitaryChannel (circuitUnitary c₂)) =
        (fun () => unitaryChannel (circuitUnitary c₂)) := funext (fun () => rfl)
    rw [heta, unitaryChannel_compose]
    rfl

/-! ## Qubit-permutation unitary

A permutation of qubit labels permutes the computational basis states. We
realize this through `finFunctionFinEquiv : (Fin n → Fin 2) ≃ Fin (2 ^ n)`:
a basis state is a bit-vector `Fin n → Fin 2`, and `σ` relabels its
coordinates. -/

/-- The action of a qubit permutation `σ` on bit-vectors: relabel coordinates
    by `σ`. As an `Equiv.Perm (Fin n → Fin 2)`. -/
def bitFunPerm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Fin 2) :=
  Equiv.arrowCongr σ (Equiv.refl (Fin 2))

/-- The basis-state permutation on `Fin (2 ^ n)` induced by a qubit
    permutation `σ`, transported through `finFunctionFinEquiv`. -/
def qubitBitPerm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (2 ^ n)) :=
  finFunctionFinEquiv.permCongr (bitFunPerm σ)

@[simp]
theorem bitFunPerm_one : bitFunPerm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext f i
  simp [bitFunPerm, Equiv.arrowCongr, Equiv.Perm.one_def]

@[simp]
theorem qubitBitPerm_one : qubitBitPerm (1 : Equiv.Perm (Fin n)) = 1 := by
  rw [qubitBitPerm, bitFunPerm_one, ← Equiv.permCongrHom_coe_equiv]
  exact map_one finFunctionFinEquiv.permCongrHom

/-- `bitFunPerm` is a homomorphism: in the `arrowCongr` precomposition
    convention the two `.symm` precompositions stack in the same order. -/
theorem bitFunPerm_mul (σ τ : Equiv.Perm (Fin n)) :
    bitFunPerm (σ * τ) = bitFunPerm σ * bitFunPerm τ := by
  ext f i
  simp only [bitFunPerm, Equiv.arrowCongr, Equiv.coe_fn_mk, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp, id_eq, Equiv.Perm.mul_def,
    Equiv.symm_trans_apply, Equiv.coe_trans]

/-- `qubitBitPerm` is a homomorphism (transported through `permCongr`). -/
theorem qubitBitPerm_mul (σ τ : Equiv.Perm (Fin n)) :
    qubitBitPerm (σ * τ) = qubitBitPerm σ * qubitBitPerm τ := by
  rw [qubitBitPerm, qubitBitPerm, qubitBitPerm, bitFunPerm_mul,
    Equiv.permCongr_mul]

/-- The permutation matrix of `qubitBitPerm σ`, as a unitary-group element. -/
def qubitPermUnitary (σ : Equiv.Perm (Fin n)) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  ⟨(qubitBitPerm σ).permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[simp]
theorem qubitPermUnitary_one :
    qubitPermUnitary (1 : Equiv.Perm (Fin n)) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext
  show (qubitBitPerm (1 : Equiv.Perm (Fin n))).permMatrix ℂ = _
  rw [qubitBitPerm_one, Matrix.permMatrix_one, UnitaryGroup.one_val]

/-! ## Permutation channel -/

/-- The conjugation channel `ρ ↦ P_σ ρ P_σᴴ` induced by a qubit permutation. -/
def permChannel (σ : Equiv.Perm (Fin n)) : QComp (2 ^ n) Unit :=
  unitaryChannel (qubitPermUnitary σ)

/-- The identity permutation channel is the pure (identity) channel. -/
@[simp]
theorem permChannel_one : permChannel (1 : Equiv.Perm (Fin n)) = QComp.qpure () := by
  rw [permChannel, qubitPermUnitary_one, unitaryChannel_one_eq_qpure]

/-! ## Equivalence up to qubit permutation -/

/-- `unitaryEquivPerm c c' σ`: the circuit `c'` realizes the same unitary as
    `c`, conjugated by the qubit-permutation `σ`. Concretely the channel of
    `c'` equals "apply `P_σᴴ`, then `c`, then `P_σ`", i.e. `ρ ↦ P_σ U_c P_σᴴ ρ
    (P_σ U_c P_σᴴ)ᴴ`. At `σ = 1` this collapses to plain unitary equivalence. -/
def unitaryEquivPerm (c c' : Circuit n) (σ : Equiv.Perm (Fin n)) : Prop :=
  unitaryDenote c' =
    QComp.qbind (permChannel σ⁻¹)
      (fun _ => QComp.qbind (unitaryDenote c) (fun _ => permChannel σ))

/-- `qubitPermUnitary` is an anti-homomorphism: matrices compose in the
    opposite order from permutations (`permMatrix_mul`): `P_{ab} = P_b * P_a`. -/
theorem qubitPermUnitary_mul (a b : Equiv.Perm (Fin n)) :
    (qubitPermUnitary (a * b) : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) =
      qubitPermUnitary b * qubitPermUnitary a := by
  apply Subtype.ext
  show (qubitBitPerm (a * b)).permMatrix ℂ =
    ((qubitPermUnitary b * qubitPermUnitary a : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
      Matrix _ _ ℂ)
  rw [qubitBitPerm_mul, Matrix.permMatrix_mul, UnitaryGroup.mul_val]
  rfl

/-- Two permutation channels compose into the permutation channel of the
    product: "apply `P_σ` then `P_τ`" equals "apply `P_{στ}`". -/
theorem permChannel_compose (σ τ : Equiv.Perm (Fin n)) :
    QComp.qbind (permChannel σ) (fun _ => permChannel τ) =
      permChannel (σ * τ) := by
  simp only [permChannel]
  have heta : (fun (_ : Unit) => unitaryChannel (qubitPermUnitary τ)) =
      (fun () => unitaryChannel (qubitPermUnitary (n := n) τ)) := funext (fun () => rfl)
  rw [heta, unitaryChannel_compose, qubitPermUnitary_mul]

/-- Conjugation of an arbitrary channel `Q` by the qubit permutation `σ`:
    "apply `P_σ⁻¹`, then `Q`, then `P_σ`". -/
def permConj (σ : Equiv.Perm (Fin n)) (Q : QComp (2 ^ n) Unit) : QComp (2 ^ n) Unit :=
  QComp.qbind (permChannel σ⁻¹) (fun _ => QComp.qbind Q (fun _ => permChannel σ))

theorem unitaryEquivPerm_def (c c' : Circuit n) (σ : Equiv.Perm (Fin n)) :
    unitaryEquivPerm c c' σ ↔ unitaryDenote c' = permConj σ (unitaryDenote c) := by
  rfl

/-- Conjugating by the identity permutation is a no-op. -/
@[simp]
theorem permConj_one (Q : QComp (2 ^ n) Unit) : permConj (1 : Equiv.Perm (Fin n)) Q = Q := by
  simp only [permConj, inv_one, permChannel_one]
  rw [QComp.qpure_qbind]
  have heta : (fun (_ : Unit) => QComp.qpure (d := 2 ^ n) ()) = QComp.qpure :=
    funext (fun () => rfl)
  rw [heta, QComp.qbind_qpure]

/-- Conjugation channels compose: conjugating by `σ` then by `τ` is
    conjugating by the product `σ * τ` (the combined permutation unitary is
    `P_τ P_σ = P_{σ*τ}`). -/
theorem permConj_permConj (σ τ : Equiv.Perm (Fin n)) (Q : QComp (2 ^ n) Unit) :
    permConj τ (permConj σ Q) = permConj (σ * τ) Q := by
  -- Notation:  A = P_τ⁻¹, B = P_σ⁻¹, C = P_σ, D = P_τ, with `X ; Y := qbind X (fun _ => Y)`.
  -- permConj τ (permConj σ Q) = A ; ((B ; (Q ; C)) ; D)
  -- Reassociate to (A ; B) ; (Q ; (C ; D)), then fold the two permChannel pairs.
  simp only [permConj]
  -- trailing fold: C ; D = P_σ ; P_τ = P_{σ*τ}
  have htrail : QComp.qbind (permChannel σ) (fun _ => permChannel τ) =
      permChannel (σ * τ) := permChannel_compose σ τ
  -- leading fold: A ; B = P_τ⁻¹ ; P_σ⁻¹ = P_{τ⁻¹ * σ⁻¹} = P_{(σ*τ)⁻¹}
  have hlead : QComp.qbind (permChannel τ⁻¹) (fun _ => permChannel σ⁻¹) =
      permChannel (σ * τ)⁻¹ := by rw [permChannel_compose, _root_.mul_inv_rev]
  -- Step 1: (B ; (Q ; C)) ; D = B ; ((Q ; C) ; D) = B ; (Q ; (C ; D))
  rw [QComp.qbind_assoc (permChannel σ⁻¹)]
  simp only [QComp.qbind_assoc]
  -- Step 2: collapse C ; D
  rw [htrail]
  -- Now LHS = A ; (B ; (Q ; P_{σ*τ})); reassociate to (A ; B) ; (Q ; P_{σ*τ})
  rw [← QComp.qbind_assoc (permChannel τ⁻¹)]
  rw [hlead]

/-- Reflexivity: every circuit is `unitaryEquivPerm`-related to itself at the
    identity permutation. -/
theorem unitaryEquivPerm_refl (c : Circuit n) :
    unitaryEquivPerm c c 1 := by
  rw [unitaryEquivPerm_def, permConj_one]

/-- Composition: if `c'` is `c` conjugated by `σ`, and `c''` is `c'` conjugated
    by `τ`, then `c''` is `c` conjugated by `σ * τ`. -/
theorem unitaryEquivPerm_trans {c c' c'' : Circuit n} {σ τ : Equiv.Perm (Fin n)}
    (h₁ : unitaryEquivPerm c c' σ) (h₂ : unitaryEquivPerm c' c'' τ) :
    unitaryEquivPerm c c'' (σ * τ) := by
  rw [unitaryEquivPerm_def] at h₁ h₂ ⊢
  rw [h₂, h₁, permConj_permConj]

/-! ## SWAP under the unitary semantics

`swapGate i j` is the 3-CNOT decomposition. We record its self-inverse
property under `unitaryDenote`. The `Circuit.denote` version in
`HardwareRouting.lean` is vacuous: its denotation ignores the gates. -/

/-- A single CNOT is its own inverse as a unitary-group element:
    `U_{CNOT(i,j)} * U_{CNOT(i,j)} = 1`. For distinct qubits this is
    `embedGate2_mul + cnot_sq + embedGate2_one`; for `i = j` the embedding is
    the identity matrix. -/
theorem cnotUnitary_sq (i j : Fin n) :
    gateEmbedding_unitaryGroup (Gate.CNOT i j) *
        gateEmbedding_unitaryGroup (Gate.CNOT i j) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext
  show gateEmbedding (Gate.CNOT i j) * gateEmbedding (Gate.CNOT i j) =
    (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
  simp only [gateEmbedding]
  by_cases h : i = j
  · subst h; simp
  · rw [dite_eq_right h, embedGate2_mul, cnot_sq, embedGate2_one]

/-- SWAP is self-inverse under the unitary semantics:
    `unitaryDenote (swapGate i j ; swapGate i j) = unitaryDenote empty`.

    This is the matrix identity `SWAP² = I`. With the 3-CNOT decomposition
    `SWAP = C ; C' ; C` (`C = CNOT(i,j)`, `C' = CNOT(j,i)`), the doubled circuit
    cancels pairwise from the inside out using `cnotUnitary_sq` — no braiding is
    needed: `S * S = (C C' C)(C C' C) = C C' (C C) C' C = C C' C' C = C C = 1`. -/
theorem swapGate_unitary_self_inverse (i j : Fin n) :
    unitaryDenote (Circuit.seq (swapGate i j) (swapGate i j)) =
      unitaryDenote (Circuit.empty : Circuit n) := by
  rw [unitaryDenote_eq_channel, unitaryDenote_eq_channel]
  congr 1
  -- Reduce to the unitary-group identity `S * S = 1`.
  set C : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := gateEmbedding_unitaryGroup (Gate.CNOT i j)
  set C' : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := gateEmbedding_unitaryGroup (Gate.CNOT j i)
  have hC : C * C = 1 := cnotUnitary_sq i j
  have hC' : C' * C' = 1 := cnotUnitary_sq j i
  show circuitUnitary (Circuit.seq (swapGate i j) (swapGate i j)) =
    circuitUnitary (Circuit.empty : Circuit n)
  -- `circuitUnitary` of `swapGate i j` is `(C * C') * C` (run-order composition).
  show (((1 * C) * (1 * C')) * (1 * C)) * (((1 * C) * (1 * C')) * (1 * C)) = 1
  simp only [one_mul]
  -- (C C' C)(C C' C) = C C' (C C) C' C = C C' C' C = C (C' C') C = C C = 1
  calc C * C' * C * (C * C' * C)
      = C * C' * (C * C) * C' * C := by group
    _ = C * C' * C' * C := by rw [hC]; group
    _ = C * (C' * C') * C := by group
    _ = C * C := by rw [hC']; group
    _ = 1 := hC

/-- Conjugating a unitary channel by the qubit permutation `σ` is the unitary
    channel of the matrix-conjugated unitary `P_σ · U · P_{σ⁻¹}`. This turns the
    monadic `permConj` into a single matrix conjugation. -/
theorem permConj_unitaryChannel (σ : Equiv.Perm (Fin n))
    (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    permConj σ (unitaryChannel U) =
      unitaryChannel (qubitPermUnitary σ * U * qubitPermUnitary σ⁻¹) := by
  simp only [permConj, permChannel]
  rw [show (fun (_ : Unit) => unitaryChannel (qubitPermUnitary σ)) =
        (fun () => unitaryChannel (qubitPermUnitary σ)) from rfl, unitaryChannel_compose]
  rw [show (fun (_ : Unit) => unitaryChannel (qubitPermUnitary σ * U)) =
        (fun () => unitaryChannel (qubitPermUnitary σ * U)) from rfl, unitaryChannel_compose]

/-! The end-to-end routing preservation theorems (`routeGate_circuitUnitary`,
`insertSwaps_circuitUnitary`, `insertSwaps_unitaryDenote`,
`insertSwaps_unitaryCorrect`) are proved in `SwapConj.lean`, where the braiding
identity `swapConj_relabel` (`S · U_{g.relabel} · S = U_g`) is available. -/

end CatCrypt.Quantum.Optimization.RoutingPerm
