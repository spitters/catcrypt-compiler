/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.Qubit
public import CatCrypt.Quantum.Instrument
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

set_option autoImplicit false


/-!
# Entanglement Distillation (BBPSSW Protocol)

Formalizes the BBPSSW entanglement distillation protocol (Bennett, Brassard,
Popescu, Schumacher, Smolin, Wootters 1996): given two copies of a noisy
Bell pair, produce one copy of a higher-fidelity Bell pair with some
probability of success.

## Protocol (BBPSSW)

Given two noisy EPR pairs, each with fidelity F to |Phi+>:

1. Alice and Bob each apply CNOT (control: pair 1, target: pair 2)
2. Both measure their target qubit (pair 2) in the Z basis
3. They communicate measurement results over a classical channel
4. **If results agree**: keep pair 1 (higher fidelity)
5. **If results disagree**: discard (protocol fails)

## Key Property

If the input fidelity F > 1/2, the output fidelity F' > F.
Specifically: F' = (F^2 + (1-F)^2/9) / (F^2 + 2F(1-F)/3 + 5(1-F)^2/9)

This is the core building block for quantum repeaters: iterating distillation
brings fidelity arbitrarily close to 1.

## Main results

* `distillProtocol` -- the BBPSSW protocol as a `QComp 16 Bool`
* `distill_branch_true_apply` -- the Kraus output of the success branch,
  entrywise
* `distill_success_probability` -- `Tr[output]` equals the BBPSSW denominator
* `distill_output_fidelity_numerator` -- `Tr[(|Φ⁺⟩⟨Φ⁺| ⊗ I)·output]` equals the
  BBPSSW numerator
* `distill_output_fidelity_eq_formula` -- the protocol's actual conditional
  output fidelity equals the BBPSSW formula `F'`
* `distill_fidelity_improvement` -- output fidelity exceeds input fidelity
* `distill_probability` -- success probability as a function of input fidelity

## References

* Bennett et al. -- *Purification of Noisy Entanglement and Faithful
  Teleportation via Noisy Channels*, PRL 76(5), 1996
* Deutsch et al. -- *Quantum Privacy Amplification*, PRL 77(13), 1996
-/

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical
open CatCrypt.Quantum
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.Programs.EntanglementDistillation

/-! ## Werner State (Noisy Bell Pair) -/

/-- A Werner state with fidelity F: a mixture of |Phi+> with weight F and
    the maximally mixed state with weight (1-F).
    rho_F = F * |Phi+><Phi+| + (1-F)/3 * (I_4 - |Phi+><Phi+|)
    where I_4 is the 4x4 identity matrix.
    This is the standard 1-parameter family of noisy Bell pairs. -/
def wernerState (F : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (F : ℂ) • bellPhiPlus + ((1 - F) / 3 : ℂ) • ((1 : Matrix (Fin 4) (Fin 4) ℂ) - bellPhiPlus)

private theorem sqrt2_inv_sq :
    (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  push_cast; ring

/-- |Φ+⟩ is a unit vector: ⟨Φ+|Φ+⟩ = 1. Mirrors `Teleportation`'s
    structural proof rather than the prior 4×4-fin_cases hammer. -/
private theorem bellPhiPlusKet_normalized : IsNormalized bellPhiPlusKet := by
  show braket bellPhiPlusKet bellPhiPlusKet = 1
  simp [braket, bellPhiPlusKet, Fin.sum_univ_four, sqrt2_inv_sq]; norm_num

/-- Trace of a rank-1 density matrix |ψ⟩⟨ψ| equals ⟨ψ|ψ⟩; combined with
    normalization, the trace is 1. Uses the public `densityOf_trace_one`
    primitive in `Qubit.lean` instead of expanding by matrix entries. -/
private theorem bellPhiPlus_trace : bellPhiPlus.trace = 1 := by
  show (densityOf bellPhiPlusKet).trace = 1
  exact densityOf_trace_one _ bellPhiPlusKet_normalized

private theorem identity_trace_four : (1 : Matrix (Fin 4) (Fin 4) ℂ).trace = 4 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.one_apply, Fin.sum_univ_four]
  norm_num

/-- The Werner state has trace 1 for any fidelity F. -/
theorem wernerState_trace (F : ℝ) :
    (wernerState F).trace = 1 := by
  simp only [wernerState]
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub]
  rw [bellPhiPlus_trace, identity_trace_four]
  simp only [smul_eq_mul]; push_cast; ring

/-- A rank-1 projector |ψ⟩⟨ψ| is idempotent when ⟨ψ|ψ⟩ = 1. Structural
    proof (Finset.sum_mul / mul_sum), mirroring Teleportation. -/
private theorem densityOf_idempotent {d : ℕ} (ψ : Ket d) (hψ : IsNormalized ψ) :
    densityOf ψ * densityOf ψ = densityOf ψ := by
  ext i j
  simp only [densityOf, ketbra, Matrix.mul_apply, Matrix.of_apply]
  simp_rw [show ∀ k, ψ i * starRingEnd ℂ (ψ k) * (ψ k * starRingEnd ℂ (ψ j)) =
    ψ i * (starRingEnd ℂ (ψ k) * ψ k) * starRingEnd ℂ (ψ j) from fun k => by ring]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have : ∑ k : Fin d, starRingEnd ℂ (ψ k) * ψ k = 1 := hψ
  rw [this, mul_one]

private theorem bellPhiPlus_idempotent : bellPhiPlus * bellPhiPlus = bellPhiPlus := by
  show densityOf bellPhiPlusKet * densityOf bellPhiPlusKet = densityOf bellPhiPlusKet
  exact densityOf_idempotent _ bellPhiPlusKet_normalized

/-- The fidelity of a Werner state with respect to |Phi+> is F
    (by construction). -/
theorem wernerState_fidelity (F : ℝ) :
    (bellPhiPlus * wernerState F).trace = F := by
  simp only [wernerState]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one]
  rw [bellPhiPlus_idempotent]
  simp only [sub_self, smul_zero, add_zero]
  rw [Matrix.trace_smul, bellPhiPlus_trace, smul_eq_mul, mul_one]

/-! ## CNOT on Two Pairs -/

/-- CNOT gate on the 16-dim space (4 qubits): control = qubit i of pair 1,
    target = qubit i of pair 2. Applied independently by Alice (qubits 0, 2)
    and Bob (qubits 1, 3). -/
def bilateralCNOT : Matrix (Fin 16) (Fin 16) ℂ :=
  -- Alice's CNOT(0,2) and Bob's CNOT(1,3) acting on |q0 q1 q2 q3>.
  -- Maps |a b c d> to |a b (a xor c) (b xor d)>.
  Matrix.of fun i j =>
    let a := j.val / 8           -- qubit 0
    let b := (j.val / 4) % 2     -- qubit 1
    let c := (j.val / 2) % 2     -- qubit 2
    let d := j.val % 2           -- qubit 3
    let c' := (a + c) % 2        -- a xor c
    let d' := (b + d) % 2        -- b xor d
    let target := a * 8 + b * 4 + c' * 2 + d'
    if i.val = target then 1 else 0

/-- The XOR involution underlying `bilateralCNOT`:
    `|a, b, c, d⟩ ↔ |a, b, a⊕c, b⊕d⟩`. -/
private def bilateralXorFun (j : Fin 16) : Fin 16 :=
  let a := j.val / 8
  let b := (j.val / 4) % 2
  let c := (j.val / 2) % 2
  let d := j.val % 2
  ⟨a * 8 + b * 4 + ((a + c) % 2) * 2 + ((b + d) % 2), by
    have : j.val < 16 := j.isLt; omega⟩

private theorem bilateralXorFun_involutive : Function.Involutive bilateralXorFun := by
  intro j
  fin_cases j <;> rfl

/-- `bilateralXorPerm` is the XOR involution as an `Equiv.Perm`. -/
private noncomputable def bilateralXorPerm : Equiv.Perm (Fin 16) :=
  Function.Involutive.toPerm _ bilateralXorFun_involutive

private theorem bilateralCNOT_eq_permMatrix :
    bilateralCNOT = Equiv.Perm.permMatrix ℂ bilateralXorPerm := by
  ext i j
  -- Both sides are 0/1 indicator functions; align their predicates.
  -- LHS: bilateralCNOT i j = 1 iff i.val = (bilateralXorFun j).val.
  -- RHS: permMatrix σ i j = 1 iff σ i = j; for involutive σ, σ i = j ↔ i = σ j.
  simp only [bilateralCNOT, Matrix.of_apply, Equiv.Perm.permMatrix,
             PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff]
  -- Goal: (if i.val = ⟨...⟩.val then 1 else 0) = (if bilateralXorPerm i = j then 1 else 0)
  -- The LHS condition is, by definition, `i.val = (bilateralXorFun j).val`,
  -- which equals `i = bilateralXorFun j` via `Fin.ext`.
  refine if_congr ?_ rfl rfl
  -- Build the equivalence i.val = target(j) ↔ bilateralXorPerm i = j.
  -- For the involutive σ: i = σ j ↔ σ i = j.
  change (i.val = (bilateralXorFun j).val) ↔ (bilateralXorPerm i = j)
  constructor
  · intro hv
    have hij : i = bilateralXorFun j := Fin.ext hv
    -- bilateralXorPerm i = bilateralXorFun i; use hij + involution.
    show bilateralXorFun i = j
    rw [hij]
    exact bilateralXorFun_involutive j
  · intro hv
    -- bilateralXorFun i = j gives, by applying σ: i = σ j.
    have hij : i = bilateralXorFun j := by
      have h1 : bilateralXorFun (bilateralXorFun i) = i :=
        bilateralXorFun_involutive i
      have h2 : bilateralXorFun j = bilateralXorFun (bilateralXorFun i) := by
        rw [← hv]; rfl
      rw [h2, h1]
    exact congrArg Fin.val hij

/-- The bilateral CNOT is unitary, via the structural fact that it's a
    permutation matrix arising from an XOR involution. Replaces the
    earlier `ext i j; by_cases; omega` hammer that loops under 4.29. -/
theorem bilateralCNOT_unitary :
    bilateralCNOT * bilateralCNOTᴴ = 1 := by
  rw [bilateralCNOT_eq_permMatrix]
  rw [Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  show Equiv.Perm.permMatrix ℂ (bilateralXorPerm⁻¹ * bilateralXorPerm) = 1
  rw [inv_mul_cancel]
  exact Matrix.permMatrix_one

/-! ## Distillation Protocol -/

/-- Measurement operators for the target pair (qubits 2, 3) in the Z basis.
    Outcome = True (agree): both |00> or both |11>
    Outcome = False (disagree): |01> or |10> -/
def distillMeasOp : Bool → Matrix (Fin 16) (Fin 16) ℂ
  | true  =>
    -- Diagonal projection onto subspace where qubits 2,3 agree (both 00 or both 11)
    Matrix.diagonal fun i =>
      let c := (i.val / 2) % 2
      let d := i.val % 2
      if c = d then 1 else 0
  | false =>
    -- Diagonal projection onto subspace where qubits 2,3 disagree (01 or 10)
    Matrix.diagonal fun i =>
      let c := (i.val / 2) % 2
      let d := i.val % 2
      if c ≠ d then 1 else 0

/-- Kraus operators for the BBPSSW distillation protocol.
    K_b = distillMeasOp(b) * bilateralCNOT -/
def distillKrausOp (b : Bool) : Matrix (Fin 16) (Fin 16) ℂ :=
  distillMeasOp b * bilateralCNOT

/-- Star (complex conjugate) of an indicator `if p then 1 else 0` is itself. -/
private theorem indicator_star (p : Prop) [Decidable p] :
    star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

/-- An indicator `if p then 1 else 0` of type ℂ squares to itself. -/
private theorem indicator_sq (p : Prop) [Decidable p] :
    (if p then (1 : ℂ) else 0) * (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

/-- distillMeasOp is Hermitian (diagonal with real entries). -/
private theorem distillMeasOp_hermitian (b : Bool) :
    (distillMeasOp b)ᴴ = distillMeasOp b := by
  -- Both branches are `Matrix.diagonal` of a 0/1-valued function; real
  -- diagonals are Hermitian.  Reduce via `Matrix.diagonal_conjTranspose`
  -- and apply the pointwise `indicator_star` lemma.
  cases b
  all_goals
    simp only [distillMeasOp, Matrix.diagonal_conjTranspose]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    exact indicator_star _

/-- distillMeasOp is idempotent (diagonal 0/1 projector). -/
private theorem distillMeasOp_idempotent (b : Bool) :
    distillMeasOp b * distillMeasOp b = distillMeasOp b := by
  -- Reduce `diagonal * diagonal` to `diagonal (d * d)` then use the
  -- pointwise `indicator_sq` lemma.
  cases b
  all_goals
    simp only [distillMeasOp, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    exact indicator_sq _

/-- The two distillMeasOp projectors sum to identity. -/
private theorem distillMeasOp_complete :
    ∑ b : Bool, distillMeasOp b = (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  -- The Boolean sum is `distillMeasOp true + distillMeasOp false`. Both
  -- branches are diagonal, with indicators partitioning `c = d` vs `c ≠ d`,
  -- so the pointwise sum is constantly 1.
  rw [Fintype.sum_bool]
  ext i j
  simp only [distillMeasOp, Matrix.add_apply, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : (i.val / 2) % 2 = i.val % 2
    · simp [h]
    · simp [h]
  · simp [hij]

/-- Reverse unitarity of bilateralCNOT. -/
private theorem bilateralCNOT_unitary' :
    bilateralCNOTᴴ * bilateralCNOT = 1 :=
  mul_eq_one_comm.mpr bilateralCNOT_unitary

/-- Completeness of distillation Kraus operators. -/
theorem distill_kraus_completeness :
    ∑ b : Bool, (distillKrausOp b)ᴴ * distillKrausOp b =
      (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  -- K_b = P_b * CNOT, so K†_b * K_b = CNOT† * P†_b * P_b * CNOT = CNOT† * P_b * CNOT
  have step : ∀ b : Bool,
      (distillKrausOp b)ᴴ * distillKrausOp b =
      bilateralCNOTᴴ * distillMeasOp b * bilateralCNOT := by
    intro b
    simp only [distillKrausOp, conjTranspose_mul, mul_assoc]
    rw [← mul_assoc (distillMeasOp b)ᴴ, distillMeasOp_hermitian,
        distillMeasOp_idempotent]
  simp_rw [step]
  -- ∑ b, CNOT† * P_b * CNOT = CNOT† * (∑ b, P_b) * CNOT = CNOT† * I * CNOT = I
  rw [← Finset.sum_mul, ← Finset.mul_sum, distillMeasOp_complete, Matrix.mul_one,
      bilateralCNOT_unitary']

/-- The BBPSSW distillation protocol as a QComp.
    Input: two noisy Bell pairs (16-dim = 4 qubits)
    Output: Bool (True = success/agree, False = fail/disagree) -/
def distillProtocol : QComp 16 Bool :=
  QComp.ofKraus distillKrausOp distill_kraus_completeness

/-! ## Connecting the protocol to the BBPSSW fidelity formula -/

private theorem sqrt2_inv_pow2 :
    ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
  rw [sq]; exact sqrt2_inv_sq

/-- The Bell-state amplitude squared (with conjugation): `(1/√2)·conj(1/√2) = 1/2`. -/
private theorem s_conj_s :
    (↑(1 / Real.sqrt 2) : ℂ) * (starRingEnd ℂ) ↑(1 / Real.sqrt 2) = 1 / 2 := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
      show (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) / 2 by
        rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num]
  norm_num

/-- Diagonal entries of the Werner state: `W 0 0 = W 3 3 = F/2 + (1-F)/6`,
    `W 1 1 = W 2 2 = (1-F)/3`. -/
private theorem wernerState_diag00 (F : ℝ) :
    (wernerState F) 0 0 = (F : ℂ) / 2 + (1 - F) / 6 := by
  simp only [wernerState, bellPhiPlus, densityOf, ketbra, bellPhiPlusKet,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val_zero, smul_eq_mul]
  simp only [s_conj_s, ite_true]; ring

private theorem wernerState_diag33 (F : ℝ) :
    (wernerState F) 3 3 = (F : ℂ) / 2 + (1 - F) / 6 := by
  simp only [wernerState, bellPhiPlus, densityOf, ketbra, bellPhiPlusKet,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero]; rw [sqrt2_inv_sq]; ring

private theorem wernerState_diag11 (F : ℝ) :
    (wernerState F) 1 1 = (1 - F) / 3 := by
  simp only [wernerState, bellPhiPlus, densityOf, ketbra, bellPhiPlusKet,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    smul_eq_mul]
  norm_num

private theorem wernerState_diag22 (F : ℝ) :
    (wernerState F) 2 2 = (1 - F) / 3 := by
  simp only [wernerState, bellPhiPlus, densityOf, ketbra, bellPhiPlusKet,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    smul_eq_mul]
  norm_num

/-- Off-diagonal coherence entries of the Werner state:
    `W 0 3 = W 3 0 = F/2 - (1-F)/6`. -/
private theorem wernerState_offdiag03 (F : ℝ) :
    (wernerState F) 0 3 = (F : ℂ) / 2 - (1 - F) / 6 := by
  simp only [wernerState, bellPhiPlus, densityOf, ketbra, bellPhiPlusKet,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  rw [ite_eq_right (by decide : ¬((0 : Fin 4) = 3))]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero]; rw [sqrt2_inv_sq]; ring

private theorem wernerState_offdiag30 (F : ℝ) :
    (wernerState F) 3 0 = (F : ℂ) / 2 - (1 - F) / 6 := by
  simp only [wernerState, bellPhiPlus, densityOf, ketbra, bellPhiPlusKet,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  rw [ite_eq_right (by decide : ¬((3 : Fin 4) = 0))]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero]; rw [sqrt2_inv_sq]; ring

/-- Conjugating a matrix by `bilateralCNOT` permutes both indices by the XOR
    involution: `(CNOT * M * CNOTᴴ) i j = M (σ i) (σ j)`. -/
private theorem bilateralCNOT_conj_apply
    (M : Matrix (Fin 16) (Fin 16) ℂ) (i j : Fin 16) :
    (bilateralCNOT * M * bilateralCNOTᴴ) i j =
      M (bilateralXorFun i) (bilateralXorFun j) := by
  rw [bilateralCNOT_eq_permMatrix, Matrix.conjTranspose_permMatrix,
      Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
      Matrix.submatrix_submatrix]
  simp only [Matrix.submatrix_apply, Function.comp_apply, id_eq]
  rfl

/-- The success-branch indicator: qubits 2 and 3 agree. -/
private def agreeInd (i : Fin 16) : ℂ :=
  if (i.val / 2) % 2 = i.val % 2 then 1 else 0

/-- The success branch of `distillProtocol` on input `ρ`, entrywise:
    `output i j = [agree i] · [agree j] · ρ (σ i) (σ j)`, where `σ` is the
    bilateral-CNOT XOR involution. This is the Kraus output of the
    protocol, fully explicit in the input entries. -/
private theorem distill_branch_true_apply
    (ρ : Matrix (Fin 16) (Fin 16) ℂ) (i j : Fin 16) :
    (distillProtocol.branch true ρ) i j =
      agreeInd i * agreeInd j * ρ (bilateralXorFun i) (bilateralXorFun j) := by
  rw [show distillProtocol.branch true ρ
        = distillKrausOp true * ρ * (distillKrausOp true)ᴴ from
      QComp.ofKraus_branch _ _ _ _]
  -- K = D * CNOT, so K ρ Kᴴ = D * (CNOT ρ CNOTᴴ) * D  (D Hermitian)
  have hK : distillKrausOp true * ρ * (distillKrausOp true)ᴴ
      = distillMeasOp true * (bilateralCNOT * ρ * bilateralCNOTᴴ)
          * distillMeasOp true := by
    rw [distillKrausOp, Matrix.conjTranspose_mul, distillMeasOp_hermitian]
    simp only [Matrix.mul_assoc]
  rw [hK]
  -- Outer product `(D * X) * D`: collapse the last factor at `b = j`.
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · -- Inner product `D * X`: collapse the first factor at `b' = i`.
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [bilateralCNOT_conj_apply]
      simp only [distillMeasOp, Matrix.diagonal_apply_eq, agreeInd]
      ring
    · intro b _ hb
      simp only [distillMeasOp, Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro b _ hb
    simp only [distillMeasOp, Matrix.diagonal_apply_ne _ hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Success probability of the protocol equals the BBPSSW denominator.**

    The trace of the success branch of `distillProtocol` on the input
    `wernerState F ⊗ₖ wernerState F` — i.e. the probability that Alice and Bob
    obtain agreeing measurement outcomes — is exactly the BBPSSW success
    probability `F² + 2F(1-F)/3 + 5((1-F)/3)²`. -/
theorem distill_success_probability (F : ℝ) :
    (distillProtocol.branch true (wernerState F ⊗ₖ wernerState F)).trace =
      (F ^ 2 + 2 * F * (1 - F) / 3 + 5 * ((1 - F) / 3) ^ 2 : ℂ) := by
  rw [Matrix.trace, Fin.sum_univ_succ]
  simp only [Matrix.diag_apply, distill_branch_true_apply, agreeInd,
    bilateralXorFun, kronecker_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, finProdEquiv, finProdFinEquiv,
    Equiv.coe_fn_symm_mk]
  norm_num [Fin.divNat, Fin.modNat, wernerState_diag00, wernerState_diag11,
    wernerState_diag22, wernerState_diag33]
  ring

/-- The four nonzero entries of `bellPhiPlus = |Φ⁺⟩⟨Φ⁺|`, at indices
    `(0,0), (0,3), (3,0), (3,3)`, are all `1/2`. -/
private theorem bellPhiPlus_00 : bellPhiPlus 0 0 = 1 / 2 := by
  simp only [bellPhiPlus, densityOf, ketbra, bellPhiPlusKet, Matrix.of_apply,
    Matrix.cons_val_zero]
  rw [s_conj_s]
private theorem bellPhiPlus_03 : bellPhiPlus 0 3 = 1 / 2 := by
  simp only [bellPhiPlus, densityOf, ketbra, bellPhiPlusKet, Matrix.of_apply]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero]; rw [sqrt2_inv_sq]; norm_num
private theorem bellPhiPlus_30 : bellPhiPlus 3 0 = 1 / 2 := by
  simp only [bellPhiPlus, densityOf, ketbra, bellPhiPlusKet, Matrix.of_apply]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero]; rw [sqrt2_inv_sq]; norm_num
private theorem bellPhiPlus_33 : bellPhiPlus 3 3 = 1 / 2 := by
  simp only [bellPhiPlus, densityOf, ketbra, bellPhiPlusKet, Matrix.of_apply]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero]; rw [sqrt2_inv_sq]; norm_num

/-- **Output-state fidelity numerator equals the BBPSSW numerator.**

    `Tr[(|Φ⁺⟩⟨Φ⁺| ⊗ I₄) · output]`, the (unnormalised) fidelity of pair 1 of
    the success-branch output of `distillProtocol` against `|Φ⁺⟩`,
    equals the BBPSSW numerator `F² + ((1-F)/3)²`. Dividing by
    `distill_success_probability` recovers the BBPSSW output fidelity `F'`. -/
theorem distill_output_fidelity_numerator (F : ℝ) :
    ((bellPhiPlus ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ))
        * distillProtocol.branch true (wernerState F ⊗ₖ wernerState F)).trace =
      (F ^ 2 + ((1 - F) / 3) ^ 2 : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, distill_branch_true_apply,
    agreeInd, bilateralXorFun, kronecker_apply, Matrix.one_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, finProdEquiv, finProdFinEquiv,
    Equiv.coe_fn_symm_mk, Fin.divNat, Fin.modNat]
  norm_num
  simp only [show (⟨2, by omega⟩ : Fin 4) = 2 from rfl,
    show (⟨3, by omega⟩ : Fin 4) = 3 from rfl,
    bellPhiPlus_00, bellPhiPlus_03, bellPhiPlus_30, bellPhiPlus_33,
    wernerState_diag00, wernerState_diag11, wernerState_diag22, wernerState_diag33,
    wernerState_offdiag03, wernerState_offdiag30]
  simp only [bellPhiPlus, wernerState, densityOf, ketbra, bellPhiPlusKet,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The protocol realises the BBPSSW fidelity formula.**

    The conditional output fidelity of `distillProtocol` on
    `wernerState F ⊗ₖ wernerState F`, the ratio of the Kraus-output traces
    `Tr[(|Φ⁺⟩⟨Φ⁺| ⊗ I) · output] / Tr[output]`, equals the BBPSSW formula `F'`
    of `distill_fidelity_improvement`: `F'` is the fidelity the program
    produces. -/
theorem distill_output_fidelity_eq_formula (F : ℝ) :
    ((bellPhiPlus ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ))
        * distillProtocol.branch true (wernerState F ⊗ₖ wernerState F)).trace
      / (distillProtocol.branch true (wernerState F ⊗ₖ wernerState F)).trace =
      ((F ^ 2 + ((1 - F) / 3) ^ 2)
        / (F ^ 2 + 2 * F * (1 - F) / 3 + 5 * ((1 - F) / 3) ^ 2) : ℂ) := by
  rw [distill_output_fidelity_numerator, distill_success_probability]

/-! ## Fidelity Improvement -/

/-- **Fidelity improvement theorem**: if the input fidelity F > 1/2,
    the output fidelity F' (conditioned on success) is strictly greater than F.

    The output fidelity is:
    F' = (F^2 + ((1-F)/3)^2) / (F^2 + 2*F*(1-F)/3 + 5*((1-F)/3)^2)

    The numerator and denominator are the Kraus-output traces of
    `distillProtocol`: see `distill_output_fidelity_numerator`,
    `distill_success_probability`, and `distill_output_fidelity_eq_formula`,
    which prove that this `F'` is exactly the fidelity the protocol produces. -/
theorem distill_fidelity_improvement (F : ℝ) (hF_low : 1/2 < F) (hF_high : F < 1) :
    let F' := (F^2 + ((1-F)/3)^2) / (F^2 + 2*F*(1-F)/3 + 5*((1-F)/3)^2)
    F' > F := by
  simp only [gt_iff_lt]
  have h_denom : 0 < F ^ 2 + 2 * F * (1 - F) / 3 + 5 * ((1 - F) / 3) ^ 2 := by
    nlinarith [sq_nonneg F, sq_nonneg (1 - F)]
  rw [lt_div_iff₀ h_denom]
  have h1 : 0 < 1 - F := by linarith
  have h3 : 0 < 2 * F - 1 := by linarith
  have h4 : 0 < 4 * F - 1 := by linarith
  have key : 0 < (1 - F) * (2 * F - 1) * (4 * F - 1) := by positivity
  have expand : 9 * (F ^ 2 + ((1 - F) / 3) ^ 2 -
    F * (F ^ 2 + 2 * F * (1 - F) / 3 + 5 * ((1 - F) / 3) ^ 2)) =
    (1 - F) * (2 * F - 1) * (4 * F - 1) := by ring
  linarith

/-- The success probability of distillation as a function of input fidelity. -/
theorem distill_probability (F : ℝ) (hF_low : 0 ≤ F) (hF_high : F ≤ 1) :
    let p_success := F^2 + 2*F*(1-F)/3 + 5*((1-F)/3)^2
    0 < p_success ∧ p_success ≤ 1 := by
  simp only
  constructor
  · nlinarith [sq_nonneg F, sq_nonneg ((1 - F) / 3)]
  · have expand : 9 * (F ^ 2 + 2 * F * (1 - F) / 3 + 5 * ((1 - F) / 3) ^ 2) =
      8 * F ^ 2 - 4 * F + 5 := by ring
    have bound : 8 * F ^ 2 - 4 * F + 5 ≤ 9 := by nlinarith [sq_nonneg (F - 1)]
    linarith

/-- One round of distillation as a map on fidelity, the `F'` of
    `distill_fidelity_improvement`. -/
noncomputable def distillStep (F : ℝ) : ℝ :=
  (F^2 + ((1-F)/3)^2) / (F^2 + 2*F*(1-F)/3 + 5*((1-F)/3)^2)

/-- A fidelity below one stays below one after a round. -/
theorem distillStep_lt_one (F : ℝ) (hF_low : 1/2 < F) (hF_high : F < 1) :
    distillStep F < 1 := by
  have h_denom : 0 < F ^ 2 + 2 * F * (1 - F) / 3 + 5 * ((1 - F) / 3) ^ 2 := by
    nlinarith [sq_nonneg F, sq_nonneg (1 - F)]
  rw [distillStep, div_lt_one h_denom]
  nlinarith [sq_nonneg (1 - F)]

/-- The open interval `(1/2, 1)` is preserved by a round of distillation. -/
theorem distillStep_mem (F : ℝ) (hF_low : 1/2 < F) (hF_high : F < 1) :
    1/2 < distillStep F ∧ distillStep F < 1 := by
  refine ⟨lt_trans hF_low ?_, distillStep_lt_one F hF_low hF_high⟩
  simpa [distillStep] using distill_fidelity_improvement F hF_low hF_high

/-- **Iterating distillation increases fidelity monotonically.** From a
    fidelity strictly between `1/2` and `1`, every round stays in that interval
    and strictly improves on the one before.

    This is the sequence's monotonicity and boundedness, which is what
    `distill_fidelity_improvement` supports. It is not a rate: the limit being
    `1` rather than some smaller fixed point needs the map's fixed-point
    analysis, which is not proved here. -/
theorem distillStep_iterate_mem (F₀ : ℝ) (hF₀ : 1/2 < F₀) (hF₁ : F₀ < 1) :
    ∀ k : ℕ, 1/2 < distillStep^[k] F₀ ∧ distillStep^[k] F₀ < 1 := by
  intro k
  induction k with
  | zero => exact ⟨hF₀, hF₁⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact distillStep_mem _ ih.1 ih.2

theorem distill_iterate_strictMono (F₀ : ℝ) (hF₀ : 1/2 < F₀) (hF₁ : F₀ < 1)
    (k : ℕ) : distillStep^[k] F₀ < distillStep^[k+1] F₀ := by
  obtain ⟨hlo, hhi⟩ := distillStep_iterate_mem F₀ hF₀ hF₁ k
  rw [Function.iterate_succ_apply']
  simpa [distillStep] using distill_fidelity_improvement _ hlo hhi

end CatCrypt.Quantum.Programs.EntanglementDistillation
