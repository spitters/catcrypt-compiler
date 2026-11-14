/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.AndLadder

/-!
# The five-gate Toffoli construction of Barenco et al.

With `V = H S H`, the square root of `X` (`V² = X`, `V V† = V† V = 1`), the Toffoli gate with
controls `a`, `b` and target `t` is the circuit (Barenco et al., *Elementary gates for quantum
computation*, 1995, Lemma 6.1 with `V² = X`)

  `CV(b, t); CNOT(a, b); CV†(b, t); CNOT(a, b); CV(a, t)`.

The proof is the algebra of controlled matrices: on the `|0⟩` branch of `a` the circuit is
`CV†(b, t) CV(b, t) = 1`; on the `|1⟩` branch it is `V_t · X_b CV†(b, t) X_b · CV(b, t)`, and
`X_b CV†(b, t) X_b` is `V†` on the `|0⟩` branch of `b`, so the branch is `V_t` times the
two-branch matrix `(V†, V)` on `b`, which is `(V V†, V V) = (1, X)`: `X_t` controlled on `b`.

Each controlled `V` is realised in the compiler's gate set by controlling the three gates
`H S H` (`ControlledGates.ctrlList`).

## Main definitions

* `sqrtX`, `sqrtXDag` — `V = H S H` and `V† = H S† H` with `S† = S Z`.
* `barencoGates a b t` — the five controlled gates as a gate list.

## Main results

* `sqrtX_mul_sqrtX`, `sqrtX_mul_sqrtXDag`, `sqrtXDag_mul_sqrtX` — `V² = X`, `V V† = V† V = 1`.
* `barenco_toffoli` — the five-gate product equals `X_t` controlled on `b` and on `a`.
* `listMatrix_barencoGates` — the gate list has the matrix of the Toffoli gate, and the same
  matrix as `ControlledGates.toffoliGates`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.AndAncilla (CommOn.add)
open CatCrypt.Quantum.AndLadder (commOn_ctrlMatrix)
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append)

namespace CatCrypt.Quantum.Synthesis.ToffoliBarenco

variable {n : ℕ}

/-! ## The square root of `X` -/

/-- `V = H S H`, a square root of `X`. -/
noncomputable def sqrtX : Matrix (Fin 2) (Fin 2) ℂ := hadamard * phaseS * hadamard

/-- `V† = H S† H`, with `S† = S Z`. -/
noncomputable def sqrtXDag : Matrix (Fin 2) (Fin 2) ℂ := hadamard * (phaseS * pauliZ) * hadamard

theorem pauliZ_mul_phaseS : pauliZ * phaseS = phaseS * pauliZ := by
  rw [← phaseS_sq_eq_pauliZ, mul_assoc]

theorem sqrtX_mul_sqrtX : sqrtX * sqrtX = pauliX := by
  have h : sqrtX * sqrtX = hadamard * (phaseS * phaseS) * hadamard := by
    simp only [sqrtX, mul_assoc]
    rw [← mul_assoc hadamard hadamard, hadamard_sq, one_mul]
  rw [h, phaseS_sq_eq_pauliZ, hadamard_pauliZ_hadamard]

theorem sqrtX_mul_sqrtXDag : sqrtX * sqrtXDag = 1 := by
  have h : sqrtX * sqrtXDag = hadamard * (phaseS * (phaseS * pauliZ)) * hadamard := by
    simp only [sqrtX, sqrtXDag, mul_assoc]
    rw [← mul_assoc hadamard hadamard, hadamard_sq, one_mul]
  rw [h, phaseS_sdg, mul_one, hadamard_sq]

theorem sqrtXDag_mul_sqrtX : sqrtXDag * sqrtX = 1 := by
  have h : sqrtXDag * sqrtX = hadamard * (phaseS * (phaseS * pauliZ)) * hadamard := by
    simp only [sqrtX, sqrtXDag, mul_assoc]
    rw [← mul_assoc hadamard hadamard, hadamard_sq, one_mul, ← mul_assoc pauliZ,
      pauliZ_mul_phaseS, mul_assoc]
  rw [h, phaseS_sdg, mul_one, hadamard_sq]

/-! ## The five-gate identity -/

/-- **Barenco et al.** For distinct qubits `a`, `b`, `t`, the product (rightmost applied
first) `CV(a,t) · CNOT(a,b) · CV†(b,t) · CNOT(a,b) · CV(b,t)` is the Toffoli gate: `X_t`
controlled on `b` and on `a`. -/
theorem barenco_toffoli {a b t : Fin n} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ctrlMatrix a (embedGate1 n t sqrtX) * ctrlMatrix a (embedGate1 n b pauliX)
        * ctrlMatrix b (embedGate1 n t sqrtXDag) * ctrlMatrix a (embedGate1 n b pauliX)
        * ctrlMatrix b (embedGate1 n t sqrtX)
      = ctrlMatrix a (ctrlMatrix b (embedGate1 n t pauliX)) := by
  set V := embedGate1 n t sqrtX
  set Vd := embedGate1 n t sqrtXDag
  set Xb := embedGate1 n b pauliX
  have hVa : CommOn a V := commOn_embedGate1 (Ne.symm hat) _
  have hVb : CommOn b V := commOn_embedGate1 (Ne.symm hbt) _
  have hVdb : CommOn b Vd := commOn_embedGate1 (Ne.symm hbt) _
  have hXa : CommOn a Xb := commOn_embedGate1 (Ne.symm hab) _
  have hWa : CommOn a (ctrlMatrix b V) := commOn_ctrlMatrix (Ne.symm hab) hVa
  have hWda : CommOn a (ctrlMatrix b Vd) :=
    commOn_ctrlMatrix (Ne.symm hab) (commOn_embedGate1 (Ne.symm hat) _)
  have hVdV : Vd * V = 1 := by
    simp only [V, Vd]; rw [embedGate1_mul, sqrtXDag_mul_sqrtX, embedGate1_one]
  have hVVd : V * Vd = 1 := by
    simp only [V, Vd]; rw [embedGate1_mul, sqrtX_mul_sqrtXDag, embedGate1_one]
  have hVV : V * V = embedGate1 n t pauliX := by
    simp only [V]; rw [embedGate1_mul, sqrtX_mul_sqrtX]
  -- the `|0⟩` branch of `a`
  have h0 : ctrlMatrix b Vd * ctrlMatrix b V = 1 := by
    rw [ctrlMatrix_mul hVdb, hVdV, ctrlMatrix_one]
  -- the `|1⟩` branch of `a`
  have h1 : V * (Xb * (ctrlMatrix b Vd * (Xb * ctrlMatrix b V)))
      = ctrlMatrix b (embedGate1 n t pauliX) := by
    have hX : Xb * ctrlMatrix b Vd * Xb = branchMatrix b Vd 1 := pauliX_ctrlMatrix_pauliX hVdb
    calc V * (Xb * (ctrlMatrix b Vd * (Xb * ctrlMatrix b V)))
        = branchMatrix b V V * ((Xb * ctrlMatrix b Vd * Xb) * branchMatrix b 1 V) := by
          rw [branchMatrix_self, ← ctrlMatrix_eq_branchMatrix]; simp only [mul_assoc]
      _ = branchMatrix b (V * Vd) (V * V) := by
          rw [hX, branchMatrix_mul hVdb (commOn_one b), branchMatrix_mul hVb hVb, mul_one,
            one_mul]
      _ = _ := by rw [hVVd, hVV, ← ctrlMatrix_eq_branchMatrix]
  rw [ctrlMatrix_eq_branchMatrix a V, ctrlMatrix_eq_branchMatrix a Xb,
    ← branchMatrix_self (c := a) (ctrlMatrix b Vd), ← branchMatrix_self (c := a) (ctrlMatrix b V),
    ctrlMatrix_eq_branchMatrix a (ctrlMatrix b _)]
  simp only [mul_assoc]
  rw [branchMatrix_mul (commOn_one a) hXa, branchMatrix_mul hWda hWda,
    branchMatrix_mul (commOn_one a) hXa, branchMatrix_mul (commOn_one a) hVa]
  simp only [one_mul]
  rw [h0, h1]

/-! ## The gate list -/

/-- `V = H S H` on `t` as gates. -/
def sqrtXGates (t : Fin n) : List (Gate n) := [.H t, .S t, .H t]

/-- `V† = H S† H` on `t` as gates, with `S† = S Z`. -/
def sqrtXDagGates (t : Fin n) : List (Gate n) := [.H t, .Z t, .S t, .H t]

theorem listMatrix_sqrtXGates (t : Fin n) : listMatrix (sqrtXGates t) = embedGate1 n t sqrtX := by
  simp only [sqrtXGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, sqrtX,
    embedGate1_mul]

theorem listMatrix_sqrtXDagGates (t : Fin n) :
    listMatrix (sqrtXDagGates t) = embedGate1 n t sqrtXDag := by
  simp only [sqrtXDagGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, sqrtXDag,
    embedGate1_mul, mul_assoc]

/-- The five controlled gates of the Barenco construction, in circuit order:
`CV(b, t); CNOT(a, b); CV†(b, t); CNOT(a, b); CV(a, t)`. -/
def barencoGates (a b t : Fin n) : List (Gate n) :=
  ctrlList b (sqrtXGates t) ++ [Gate.CNOT a b] ++ ctrlList b (sqrtXDagGates t) ++
    [Gate.CNOT a b] ++ ctrlList a (sqrtXGates t)

/-- **The Barenco Toffoli as a circuit.** The gate list `barencoGates a b t` has the matrix of
the Toffoli gate with controls `a`, `b` and target `t`, which is also the matrix of the
compiler's Toffoli `toffoliGates a b t`. -/
theorem listMatrix_barencoGates {a b t : Fin n} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    listMatrix (barencoGates a b t) = ctrlMatrix a (ctrlMatrix b (embedGate1 n t pauliX)) ∧
      listMatrix (barencoGates a b t) = listMatrix (toffoliGates a b t) := by
  have hav : ∀ (c : Fin n), c ≠ t → ∀ g ∈ sqrtXGates t, Avoids c g := by
    intro c hc g hg
    simp only [sqrtXGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> exact Ne.symm hc
  have havd : ∀ g ∈ sqrtXDagGates t, Avoids b g := by
    intro g hg
    simp only [sqrtXDagGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact Ne.symm hbt
  have hcnot : gateEmbedding (Gate.CNOT a b) = ctrlMatrix a (embedGate1 n b pauliX) := by
    simp only [gateEmbedding, dite_eq_right hab, embedGate2_cnot]
  have hmain : listMatrix (barencoGates a b t)
      = ctrlMatrix a (ctrlMatrix b (embedGate1 n t pauliX)) := by
    simp only [barencoGates, listMatrix_append, listMatrix_cons, listMatrix_nil, one_mul,
      listMatrix_ctrlList (hav b hbt), listMatrix_ctrlList havd, listMatrix_ctrlList (hav a hat),
      listMatrix_sqrtXGates, listMatrix_sqrtXDagGates, hcnot, ← mul_assoc]
    exact barenco_toffoli hab hat hbt
  refine ⟨hmain, ?_⟩
  rw [hmain, listMatrix_toffoliGates hab hat hbt, embedGate2_cnot]

end CatCrypt.Quantum.Synthesis.ToffoliBarenco
