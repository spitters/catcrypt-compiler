/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.Qubit
public import CatCryptCore.Quantum.QRHL
public import CatCrypt.Quantum.Measurement
public import CatCryptCore.Quantum.PartialTrace

/-!
# Quantum Teleportation

Formalizes the quantum teleportation protocol (Bennett et al., 1993) and proves
correctness as a qHL theorem: the output state equals the input state.

## Protocol

Given an unknown qubit |ψ⟩ and a shared Bell pair |Φ⁺⟩ between Alice and Bob:

1. **Bell measurement**: Alice performs a Bell measurement on her two qubits
   (the unknown qubit and her half of the Bell pair), obtaining outcome (i, j) ∈ {0,1}².
2. **Correction**: Bob applies the Pauli correction X^j Z^i to his qubit.
3. **Result**: Bob's qubit is now in state |ψ⟩.

## Quantum Circuit

```
|ψ⟩ ─────●─── H ──[measure]──→ (i)
          │                        │
|Φ⁺⟩ ────⊕──────────────────────  │
          │                        │
|0⟩ ─────────── Z^i X^j ──────→ |ψ⟩
```

## Main results

* `teleportProtocol` — the protocol as a QComp on 8-dim space (3 qubits)
* `teleportLogicalChannel_eq_id` — the channel from Alice's input qubit to Bob's corrected
  qubit, summed over the four outcomes, is the identity channel
* `teleportation_qIndist` — the qHL form: the output state equals the input state

## References

* Bennett et al. — *Teleporting an Unknown Quantum State*, PRL 70(13), 1993
* Nielsen & Chuang — §1.3.7
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix
open CatCrypt.Quantum
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.PartialTrace

noncomputable section

namespace CatCrypt.Quantum.Programs.Teleportation

/-! ## Pauli Corrections -/

/-- Pauli correction indexed by Bell measurement outcome (i, j).
    correction(0,0) = I, correction(0,1) = X, correction(1,0) = Z, correction(1,1) = XZ -/
def correction : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => pauliX
  | ⟨1, _⟩, ⟨0, _⟩ => pauliZ
  | ⟨1, _⟩, ⟨1, _⟩ => pauliX * pauliZ

/-- Each correction is unitary. -/
theorem correction_unitary (i j : Fin 2) :
    correction i j * (correction i j)ᴴ = 1 := by
  fin_cases i <;> fin_cases j <;> simp only [correction]
  -- (0,0): 1 * 1ᴴ = 1
  · rw [conjTranspose_one, Matrix.mul_one]
  -- (0,1): X * Xᴴ = 1
  · rw [pauliX_hermitian, pauliX_sq]
  -- (1,0): Z * Zᴴ = 1
  · rw [pauliZ_hermitian, pauliZ_sq]
  -- (1,1): XZ * (XZ)ᴴ = 1
  · rw [conjTranspose_mul, pauliZ_hermitian, pauliX_hermitian,
        mul_assoc, ← mul_assoc pauliZ, pauliZ_sq, Matrix.one_mul, pauliX_sq]

/-! ## Bell Measurement -/

/-- Bell measurement operators on two qubits (4-dim space).
    Indexed by (i, j) ∈ {0,1}², projecting onto the four Bell states. -/
def bellMeasOp : Fin 2 × Fin 2 → Matrix (Fin 4) (Fin 4) ℂ
  | ⟨⟨0, _⟩, ⟨0, _⟩⟩ => densityOf bellPhiPlusKet  -- |Φ⁺⟩⟨Φ⁺|
  | ⟨⟨0, _⟩, ⟨1, _⟩⟩ => densityOf bellPsiPlusKet  -- |Ψ⁺⟩⟨Ψ⁺|
  | ⟨⟨1, _⟩, ⟨0, _⟩⟩ => densityOf bellPhiMinusKet -- |Φ⁻⟩⟨Φ⁻|
  | ⟨⟨1, _⟩, ⟨1, _⟩⟩ => densityOf bellPsiMinusKet -- |Ψ⁻⟩⟨Ψ⁻|

/-- Each Bell measurement operator is Hermitian. -/
private theorem bellMeasOp_hermitian (ij : Fin 2 × Fin 2) :
    (bellMeasOp ij)ᴴ = bellMeasOp ij := by
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp only [bellMeasOp] <;>
    exact densityOf_hermitian _

/-- (↑√2)⁻¹ * (↑√2)⁻¹ = (2 : ℂ)⁻¹. -/
private theorem sqrt2_inv_sq :
    (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; ring

/-- A rank-1 projector |ψ⟩⟨ψ| is idempotent when ⟨ψ|ψ⟩ = 1. -/
private theorem densityOf_idempotent {d : ℕ} (ψ : Ket d) (hψ : IsNormalized ψ) :
    densityOf ψ * densityOf ψ = densityOf ψ := by
  ext i j
  simp only [densityOf, ketbra, Matrix.mul_apply, of_apply]
  simp_rw [show ∀ k, ψ i * starRingEnd ℂ (ψ k) * (ψ k * starRingEnd ℂ (ψ j)) =
    ψ i * (starRingEnd ℂ (ψ k) * ψ k) * starRingEnd ℂ (ψ j) from fun k => by ring]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have : ∑ k : Fin d, starRingEnd ℂ (ψ k) * ψ k = 1 := hψ
  rw [this, mul_one]

private theorem bellPhiPlusKet_normalized : IsNormalized bellPhiPlusKet := by
  change braket bellPhiPlusKet bellPhiPlusKet = 1
  simp [braket, bellPhiPlusKet, Fin.sum_univ_four, sqrt2_inv_sq]; norm_num

private theorem bellPsiPlusKet_normalized : IsNormalized bellPsiPlusKet := by
  change braket bellPsiPlusKet bellPsiPlusKet = 1
  simp [braket, bellPsiPlusKet, Fin.sum_univ_four, sqrt2_inv_sq]; norm_num

private theorem bellPhiMinusKet_normalized : IsNormalized bellPhiMinusKet := by
  change braket bellPhiMinusKet bellPhiMinusKet = 1
  simp [braket, bellPhiMinusKet, Fin.sum_univ_four, sqrt2_inv_sq]; norm_num

private theorem bellPsiMinusKet_normalized : IsNormalized bellPsiMinusKet := by
  change braket bellPsiMinusKet bellPsiMinusKet = 1
  simp [braket, bellPsiMinusKet, Fin.sum_univ_four, sqrt2_inv_sq]; norm_num

/-- Each Bell projector is idempotent (P² = P). -/
private theorem bellMeasOp_idempotent (ij : Fin 2 × Fin 2) :
    bellMeasOp ij * bellMeasOp ij = bellMeasOp ij := by
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp only [bellMeasOp]
  · exact densityOf_idempotent _ bellPhiPlusKet_normalized
  · exact densityOf_idempotent _ bellPsiPlusKet_normalized
  · exact densityOf_idempotent _ bellPhiMinusKet_normalized
  · exact densityOf_idempotent _ bellPsiMinusKet_normalized

/-- Bell measurement operators form a complete projective measurement. -/
theorem bellMeas_completeness :
    ∑ ij : Fin 2 × Fin 2, (bellMeasOp ij)ᴴ * bellMeasOp ij =
      (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp_rw [bellMeasOp_hermitian, bellMeasOp_idempotent]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, bellMeasOp]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [densityOf, ketbra, bellPhiPlusKet, bellPhiMinusKet,
      bellPsiPlusKet, bellPsiMinusKet, sqrt2_inv_sq] <;>
    norm_num

/-! ## Teleportation Protocol -/

/-- Teleportation protocol on 3 qubits (8-dim space = 2³).

    Input:  qubit 1 = |ψ⟩ (unknown), qubits 2-3 = |Φ⁺⟩ (shared Bell pair)
    Step 1: Bell-measure qubits 1-2, obtaining outcome (i,j)
    Step 2: Apply correction(i,j) to qubit 3
    Output: qubit 3 = |ψ⟩

    Modeled as a QComp on the 8-dim joint space with classical output (i,j). -/
def teleportKrausOp (ij : Fin 2 × Fin 2) : Matrix (Fin 8) (Fin 8) ℂ :=
  TensorProduct.kronecker (bellMeasOp ij) (correction ij.1 ij.2)

/-- Each correction satisfies U†U = I (reverse unitarity). -/
theorem correction_unitary' (i j : Fin 2) :
    (correction i j)ᴴ * correction i j = 1 := by
  -- All corrections are Hermitian (Paulis are self-adjoint), so U† = U and U†U = UU = U² = I
  fin_cases i <;> fin_cases j <;> simp only [correction]
  · rw [conjTranspose_one, Matrix.one_mul]
  · rw [pauliX_hermitian, pauliX_sq]
  · rw [pauliZ_hermitian, pauliZ_sq]
  · rw [conjTranspose_mul, pauliZ_hermitian, pauliX_hermitian,
        mul_assoc, ← mul_assoc pauliX, pauliX_sq, Matrix.one_mul, pauliZ_sq]

/-- Completeness of teleportation Kraus operators: `∑_{i,j} M†M = I₈`.

    Each term simplifies via kronecker algebra:
    `(bellMeasOp ⊗ₖ correction)† * (bellMeasOp ⊗ₖ correction)`
    `= (bellMeasOp†·bellMeasOp) ⊗ₖ (correction†·correction)`
    `= bellMeasOp ⊗ₖ I`  (projector + unitary)

    Then `∑ bellMeasOp ⊗ₖ I = (∑ bellMeasOp) ⊗ₖ I = I₄ ⊗ₖ I₂ = I₈`. -/
theorem teleport_kraus_completeness :
    ∑ ij : Fin 2 × Fin 2, (teleportKrausOp ij)ᴴ * teleportKrausOp ij =
      (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have step : ∀ ij : Fin 2 × Fin 2,
      (teleportKrausOp ij)ᴴ * teleportKrausOp ij =
      ((bellMeasOp ij)ᴴ * bellMeasOp ij) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro ij
    simp only [teleportKrausOp]
    rw [TensorProduct.conjTranspose_kronecker,
      TensorProduct.kronecker_mul_kronecker,
      correction_unitary' ij.1 ij.2]
  simp_rw [step]
  rw [TensorProduct.kronecker_finset_sum_left,
    bellMeas_completeness, TensorProduct.kronecker_one_one]

def teleportProtocol : QComp 8 (Fin 2 × Fin 2) :=
  QComp.ofKraus teleportKrausOp teleport_kraus_completeness

/-! ## Correctness

Teleportation correctness is the **channel identity**: feed an input
qubit `ρ` together with the shared Bell pair `|Φ⁺⟩`, run all four Bell-measurement
branches (each carrying its Pauli correction on register 3), trace out the two
measured qubits (registers 1–2), and the surviving register 3 is exactly `ρ`.
This is a real `2×2`-matrix computation over the four Kraus branches with the
Pauli corrections; it is **not** a definitional `rfl`. -/

/-- (1/√2)·(1/√2) = 1/2 as a complex scalar — the recurring Bell-state norm fact. -/
private theorem sqrt2_inv_mul_self :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 : ℂ) / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- Tactic body shared by the four entry lemmas below: fully expand the four Kraus
    branches over the joint `8`-dimensional space (Bell-measurement projectors and
    Pauli corrections) at a fixed, numeral output entry. The `finProdEquiv` index
    arithmetic reduces only because the entry indices are concrete numerals — this is
    why each entry is a separate lemma rather than one parametric statement. -/
private theorem teleport_traceOut_entry_00 (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (partialTrace₁ (d₁ := 4) (d₂ := 2)
        (∑ ij : Fin 2 × Fin 2,
          teleportKrausOp ij * (ρ ⊗ₖ bellPhiPlus) * (teleportKrausOp ij)ᴴ)) 0 0 = ρ 0 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, mul_assoc, teleportKrausOp, bellMeasOp, correction]
  rw [partialTrace₁_apply, Fin.sum_univ_four]
  simp only [Fin.isValue,
    show (finProdEquiv 4 2 (0, (0 : Fin 2)) : Fin 8) = 0 from by decide,
    show (finProdEquiv 4 2 (1, (0 : Fin 2)) : Fin 8) = 2 from by decide,
    show (finProdEquiv 4 2 (2, (0 : Fin 2)) : Fin 8) = 4 from by decide,
    show (finProdEquiv 4 2 (3, (0 : Fin 2)) : Fin 8) = 6 from by decide,
    Matrix.add_apply, Matrix.mul_apply, Nat.reduceMul]
  simp only [Fin.sum_univ_eight]
  simp only [TensorProduct.kronecker_apply, finProdFinEquiv_symm_apply,
    finProdEquiv, Fin.divNat, Fin.modNat, Fin.isValue, conjTranspose_apply,
    densityOf, ketbra, bellPhiPlus, bellPhiPlusKet, bellPhiMinusKet, bellPsiPlusKet,
    bellPsiMinusKet, pauliX, pauliZ, Matrix.of_apply, Matrix.one_apply]
  norm_num [Complex.conj_ofReal, sqrt2_inv_mul_self]
  ring

private theorem teleport_traceOut_entry_01 (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (partialTrace₁ (d₁ := 4) (d₂ := 2)
        (∑ ij : Fin 2 × Fin 2,
          teleportKrausOp ij * (ρ ⊗ₖ bellPhiPlus) * (teleportKrausOp ij)ᴴ)) 0 1 = ρ 0 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, mul_assoc, teleportKrausOp, bellMeasOp, correction]
  rw [partialTrace₁_apply, Fin.sum_univ_four]
  simp only [Fin.isValue,
    show (finProdEquiv 4 2 (0, (0 : Fin 2)) : Fin 8) = 0 from by decide,
    show (finProdEquiv 4 2 (1, (0 : Fin 2)) : Fin 8) = 2 from by decide,
    show (finProdEquiv 4 2 (2, (0 : Fin 2)) : Fin 8) = 4 from by decide,
    show (finProdEquiv 4 2 (3, (0 : Fin 2)) : Fin 8) = 6 from by decide,
    show (finProdEquiv 4 2 (0, (1 : Fin 2)) : Fin 8) = 1 from by decide,
    show (finProdEquiv 4 2 (1, (1 : Fin 2)) : Fin 8) = 3 from by decide,
    show (finProdEquiv 4 2 (2, (1 : Fin 2)) : Fin 8) = 5 from by decide,
    show (finProdEquiv 4 2 (3, (1 : Fin 2)) : Fin 8) = 7 from by decide,
    Matrix.add_apply, Matrix.mul_apply, Nat.reduceMul]
  simp only [Fin.sum_univ_eight]
  simp only [TensorProduct.kronecker_apply, finProdFinEquiv_symm_apply,
    finProdEquiv, Fin.divNat, Fin.modNat, Fin.isValue, conjTranspose_apply,
    densityOf, ketbra, bellPhiPlus, bellPhiPlusKet, bellPhiMinusKet, bellPsiPlusKet,
    bellPsiMinusKet, pauliX, pauliZ, Matrix.of_apply, Matrix.one_apply]
  norm_num [Complex.conj_ofReal, sqrt2_inv_mul_self]
  ring

private theorem teleport_traceOut_entry_10 (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (partialTrace₁ (d₁ := 4) (d₂ := 2)
        (∑ ij : Fin 2 × Fin 2,
          teleportKrausOp ij * (ρ ⊗ₖ bellPhiPlus) * (teleportKrausOp ij)ᴴ)) 1 0 = ρ 1 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, mul_assoc, teleportKrausOp, bellMeasOp, correction]
  rw [partialTrace₁_apply, Fin.sum_univ_four]
  simp only [Fin.isValue,
    show (finProdEquiv 4 2 (0, (0 : Fin 2)) : Fin 8) = 0 from by decide,
    show (finProdEquiv 4 2 (1, (0 : Fin 2)) : Fin 8) = 2 from by decide,
    show (finProdEquiv 4 2 (2, (0 : Fin 2)) : Fin 8) = 4 from by decide,
    show (finProdEquiv 4 2 (3, (0 : Fin 2)) : Fin 8) = 6 from by decide,
    show (finProdEquiv 4 2 (0, (1 : Fin 2)) : Fin 8) = 1 from by decide,
    show (finProdEquiv 4 2 (1, (1 : Fin 2)) : Fin 8) = 3 from by decide,
    show (finProdEquiv 4 2 (2, (1 : Fin 2)) : Fin 8) = 5 from by decide,
    show (finProdEquiv 4 2 (3, (1 : Fin 2)) : Fin 8) = 7 from by decide,
    Matrix.add_apply, Matrix.mul_apply, Nat.reduceMul]
  simp only [Fin.sum_univ_eight]
  simp only [TensorProduct.kronecker_apply, finProdFinEquiv_symm_apply,
    finProdEquiv, Fin.divNat, Fin.modNat, Fin.isValue, conjTranspose_apply,
    densityOf, ketbra, bellPhiPlus, bellPhiPlusKet, bellPhiMinusKet, bellPsiPlusKet,
    bellPsiMinusKet, pauliX, pauliZ, Matrix.of_apply, Matrix.one_apply]
  norm_num [Complex.conj_ofReal, sqrt2_inv_mul_self]
  ring

private theorem teleport_traceOut_entry_11 (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (partialTrace₁ (d₁ := 4) (d₂ := 2)
        (∑ ij : Fin 2 × Fin 2,
          teleportKrausOp ij * (ρ ⊗ₖ bellPhiPlus) * (teleportKrausOp ij)ᴴ)) 1 1 = ρ 1 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, mul_assoc, teleportKrausOp, bellMeasOp, correction]
  rw [partialTrace₁_apply, Fin.sum_univ_four]
  simp only [Fin.isValue,
    show (finProdEquiv 4 2 (0, (1 : Fin 2)) : Fin 8) = 1 from by decide,
    show (finProdEquiv 4 2 (1, (1 : Fin 2)) : Fin 8) = 3 from by decide,
    show (finProdEquiv 4 2 (2, (1 : Fin 2)) : Fin 8) = 5 from by decide,
    show (finProdEquiv 4 2 (3, (1 : Fin 2)) : Fin 8) = 7 from by decide,
    Matrix.add_apply, Matrix.mul_apply, Nat.reduceMul]
  simp only [Fin.sum_univ_eight]
  simp only [TensorProduct.kronecker_apply, finProdFinEquiv_symm_apply,
    finProdEquiv, Fin.divNat, Fin.modNat, Fin.isValue, conjTranspose_apply,
    densityOf, ketbra, bellPhiPlus, bellPhiPlusKet, bellPhiMinusKet, bellPsiPlusKet,
    bellPsiMinusKet, pauliX, pauliZ, Matrix.of_apply, Matrix.one_apply]
  norm_num [Complex.conj_ofReal, sqrt2_inv_mul_self]
  ring

/-- **Teleportation correctness (channel identity).**

    Summed over the four Bell-measurement outcomes (each with its Pauli correction)
    and traced over the two measured qubits, the teleportation protocol returns the
    input qubit `ρ` unchanged:

    `tr₁₂(∑_{i,j} M_{i,j} (ρ ⊗ |Φ⁺⟩⟨Φ⁺|) M_{i,j}†) = ρ`.

    Stated for an arbitrary `2×2` matrix `ρ` (hence for every density matrix, e.g.
    `ρ = |ψ⟩⟨ψ|`): teleportation faithfully transfers the quantum state. -/
theorem teleport_traceOut_eq_input (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (partialTrace₁ (d₁ := 4) (d₂ := 2)
        (∑ ij : Fin 2 × Fin 2,
          teleportKrausOp ij * (ρ ⊗ₖ bellPhiPlus) * (teleportKrausOp ij)ᴴ)) = ρ := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact teleport_traceOut_entry_00 ρ
  · exact teleport_traceOut_entry_01 ρ
  · exact teleport_traceOut_entry_10 ρ
  · exact teleport_traceOut_entry_11 ρ

/-- The **logical teleportation channel** `QComp 2 Unit`: take Alice's input qubit
    `ρ` on register 3's-worth of space, adjoin the shared Bell pair `|Φ⁺⟩`, run all
    four Bell-measurement branches with their corrections, and trace out the two
    measured qubits, leaving Bob's qubit. This is a quantum channel whose
    single branch is the marginal teleportation map. -/
def teleportLogicalChannel : QComp 2 Unit where
  branch _ :=
    { toFun := fun ρ =>
        partialTrace₁ (d₁ := 4) (d₂ := 2)
          (∑ ij : Fin 2 × Fin 2,
            teleportKrausOp ij * (ρ ⊗ₖ bellPhiPlus) * (teleportKrausOp ij)ᴴ)
      map_add' := by
        intro ρ₁ ρ₂
        rw [← map_add]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun ij _ => ?_)
        have hk : (ρ₁ + ρ₂) ⊗ₖ bellPhiPlus = ρ₁ ⊗ₖ bellPhiPlus + ρ₂ ⊗ₖ bellPhiPlus := by
          ext a b; simp only [TensorProduct.kronecker_apply, Matrix.add_apply]; ring
        rw [hk, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c ρ
        simp only [RingHom.id_apply]
        rw [← LinearMap.map_smul]
        congr 1
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun ij _ => ?_)
        have hk : (c • ρ) ⊗ₖ bellPhiPlus = c • (ρ ⊗ₖ bellPhiPlus) := by
          ext a b; simp only [TensorProduct.kronecker_apply, Matrix.smul_apply, smul_eq_mul]; ring
        rw [hk, Matrix.mul_smul, Matrix.smul_mul] }
  branch_psd _ ρ hρ := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [teleport_traceOut_eq_input]
    exact hρ
  branch_summable ρ := by
    apply summable_of_ne_finset_zero (s := Finset.univ)
    intro x hx; exact absurd (Finset.mem_univ x) hx
  branch_stp ρ _ := by
    rw [tsum_fintype]
    simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
    rw [teleport_traceOut_eq_input]

/-- The logical teleportation channel **is** the identity channel (`qpure ()`):
    its single branch returns the input qubit on every input, so teleportation is
    a perfect — `ε = 0` — implementation of the identity channel. -/
theorem teleportLogicalChannel_eq_id : teleportLogicalChannel = QComp.qpure () := by
  apply QComp.ext_fun
  intro u ρ
  obtain rfl : u = () := rfl
  change partialTrace₁ (d₁ := 4) (d₂ := 2)
      (∑ ij : Fin 2 × Fin 2,
        teleportKrausOp ij * (ρ ⊗ₖ bellPhiPlus) * (teleportKrausOp ij)ᴴ)
    = (QComp.qpure () : QComp 2 Unit).branch () ρ
  rw [teleport_traceOut_eq_input]
  simp [QComp.qpure]

/-- **Teleportation as a perfect (relational) correctness statement.**

    The teleportation channel is perfectly indistinguishable (`ε = 0`) from the
    identity channel: no distinguisher can separate "teleport the qubit" from
    "do nothing". The statement is over the Bell-measurement Kraus operators and
    Pauli corrections, and follows from the channel identity
    `teleportLogicalChannel_eq_id`. -/
theorem teleportation_qIndist :
    QRHL.qIndist teleportLogicalChannel (QComp.qpure ()) 0 := by
  rw [teleportLogicalChannel_eq_id]
  exact QRHL.qIndist_refl _

/-! ## No Classical Communication Without Entanglement -/

/-- `ket1` is normalized: `⟨1|1⟩ = 1`. -/
private theorem ket1_normalized : IsNormalized ket1 := by
  change braket ket1 ket1 = 1
  simp [braket, ket1, Fin.sum_univ_two]

/-- `densityOf ket0` has a zero at entry `(1, 1)`. -/
private theorem densityOf_ket0_one_one :
    (densityOf ket0 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
  simp [densityOf, ketbra, of_apply, ket0]

/-- `densityOf ket1` has a one at entry `(1, 1)`. -/
private theorem densityOf_ket1_one_one :
    (densityOf ket1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := by
  simp [densityOf, ketbra, of_apply, ket1]

/-- Without the shared Bell pair, teleportation is impossible:
    no local operation by Alice on register 1 can transfer |ψ⟩ to Bob's register 2.

    The key insight is the no-signalling principle: for product-state inputs
    `|ψ⟩⟨ψ| ⊗ |0⟩⟨0|`, any local operation on register 1 leaves the reduced
    state on register 2 proportional to `|0⟩⟨0|`, independent of `ψ`.
    But teleportation requires the output on register 2 to equal `|ψ⟩⟨ψ|`,
    which varies with `ψ` — a contradiction.

    Here `C : QComp 2 (Fin 2)` models Alice's local operation on her qubit
    (register 1). The product structure of the output is forced by locality:
    `(C.branch a (|ψ⟩⟨ψ|)) ⊗ |0⟩⟨0|`. Tracing out register 1 yields a
    scalar multiple of `|0⟩⟨0|`, which cannot equal `|1⟩⟨1|`. -/
theorem no_teleportation_without_entanglement :
    ¬ ∃ (C : QComp 2 (Fin 2)),
      ∀ (ψ : Ket 2), IsNormalized ψ →
        (partialTrace₁ (d₁ := 2) (d₂ := 2)
          (∑' a, (C.branch a (densityOf ψ)) ⊗ₖ (densityOf ket0))) =
          densityOf ψ := by
  -- Proof by contradiction
  intro ⟨C, hC⟩
  -- Instantiate with ψ = ket1
  have h1 := hC ket1 ket1_normalized
  -- Rewrite tsum as finite sum (Fin 2 is Fintype)
  rw [tsum_fintype] at h1
  -- Factor out the constant ⊗ₖ densityOf ket0
  rw [kronecker_finset_sum_left] at h1
  -- Apply partialTrace₁_kronecker: tr₁(A ⊗ₖ B) = tr(A) • B
  rw [partialTrace₁_kronecker] at h1
  -- Now h1 : trace(∑ a, C.branch a (densityOf ket1)) • densityOf ket0 = densityOf ket1
  -- Evaluate both sides at entry (1, 1)
  have h11 := congr_fun (congr_fun h1 1) 1
  simp only [Matrix.smul_apply, smul_eq_mul, densityOf_ket0_one_one,
    mul_zero, densityOf_ket1_one_one] at h11
  exact absurd h11 (by norm_num)

end CatCrypt.Quantum.Programs.Teleportation
