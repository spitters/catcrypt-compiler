/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.OpenQASMImportGates
public import CatCrypt.Quantum.ControlledGates

/-!
# The `qelib1.inc` matrices of the imported statements

`OpenQASMImport.QGate` is the type of OpenQASM 2 gate statements and
`OpenQASMImport.lowerQ` the gate list the importer builds for each. `qelibMatrix` is the
matrix `qelib1.inc` defines for a statement, in the conventions of `embedGate1` and
`embedGate2` (qubit `0` is the most significant bit), and the lowered list realises it up
to the exact global phase `exp (i · phase g)`.

The phases, with `θ` the rotation angle: `θ/2` for `rx(θ)`, `ry(θ)`, `rz(θ)` and
`u(θ,φ,λ)`; `π/4` for `u2`; zero for every other statement. `rz(θ)` is
`diag(e^{-iθ/2}, e^{iθ/2})`, while its list is `RzQ θ = diag(1, e^{iθ})`; `p(θ)` is
`RzQ θ` exactly.

## Main results

* `qelibMatrix`, `phase` — the matrix and the global phase of a statement.
* `listMatrix_ccxGates`, `listMatrix_cczGates` — the seven-`T` Toffoli and `ccz` lists
  realise the doubly controlled `X` and `Z` exactly.
* `listMatrix_lowerQ` — `listMatrix (lowerQ g) = exp (i · phase g) • qelibMatrix g` for a
  statement with distinct operands.
* `listMatrix_flatMap_lowerQ` — the same for a list of statements, with the sum of the
  phases.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.OpenQASMImportGates
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.Optimization.PhasePolySemantics
open CatCrypt.Quantum.Optimization.PhasePolynomial (Parity)
open CatCrypt.Quantum.Optimization.DisjointCommute (gbit)
open CatCrypt.Quantum.Optimization.RoutingPerm (qubitPermUnitary)
open CatCrypt.Quantum.Optimization.SwapConj (swapBitPerm)
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)

noncomputable section

namespace CatCrypt.Quantum.Qelib

variable {n : ℕ}

/-! ## Matrices -/

/-- `qelib1.inc`'s `rz(θ) = diag(e^{-iθ/2}, e^{iθ/2})`. -/
def rzMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![Complex.exp (-(Complex.I * (θ / 2 : ℝ))), 0],
    ![0, Complex.exp (Complex.I * (θ / 2 : ℝ))]]

/-- `diag(1, e^{iθ}) = e^{iθ/2} · rz(θ)`. -/
theorem rzGate_eq_smul_rzMatrix (θ : ℝ) :
    rzGate θ = Complex.exp (Complex.I * (θ / 2 : ℝ)) • rzMatrix θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzGate, rzMatrix, ← Complex.exp_add]
  ring_nf

/-- The doubly controlled `X` with controls `a`, `b` and target `t`; the identity when
    two operands coincide. -/
def ccxMatrix (a b t : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  if h : b ≠ t then ctrlMatrix a (embedGate2 n b t cnot h) else 1

/-- The doubly controlled `Z` on `a`, `b`, `t`; the identity when `b = t`. -/
def cczMatrix (a b t : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  if h : b ≠ t then ctrlMatrix a (embedGate2 n b t czGate h) else 1

/-- The matrix `qelib1.inc` defines for a statement. -/
def qelibMatrix : OpenQASMImport.QGate n → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | .h q => embedGate1 n q hadamard
  | .x q => embedGate1 n q pauliX
  | .y q => embedGate1 n q pauliY
  | .z q => embedGate1 n q pauliZ
  | .s q => embedGate1 n q phaseS
  | .sdg q => embedGate1 n q sdgMatrix
  | .t q => embedGate1 n q tGate
  | .tdg q => embedGate1 n q tDaggerGate
  | .sx q => embedGate1 n q sxMatrix
  | .sxdg q => embedGate1 n q sxdgMatrix
  | .rx q θ => embedGate1 n q (rxMatrix θ.toReal)
  | .ry q θ => embedGate1 n q (ryMatrix θ.toReal)
  | .rz q θ => embedGate1 n q (rzMatrix θ.toReal)
  | .p q θ => embedGate1 n q (rzGate θ.toReal)
  | .u q θ φ l => embedGate1 n q (uMatrix θ.toReal φ.toReal l.toReal)
  | .u2 q φ l => embedGate1 n q (uMatrix (Real.pi / 2) φ.toReal l.toReal)
  | .cx c t => gateEmbedding (.CNOT c t)
  | .cz c t => gateEmbedding (.CZ c t)
  | .swap a b => (qubitPermUnitary (swapBitPerm a b)).val
  | .cp c t θ => ctrlMatrix c (embedGate1 n t (rzGate θ.toReal))
  | .ccx a b t => ccxMatrix a b t
  | .ccz a b t => cczMatrix a b t

/-- The global phase of the lowered list of a statement: `listMatrix (lowerQ g)` is
    `exp (i · phase g) • qelibMatrix g`. -/
def phase : OpenQASMImport.QGate n → PiLin
  | .rx _ θ | .ry _ θ | .rz _ θ | .u _ θ _ _ => θ / 2
  | .u2 _ _ _ => 1 / 4
  | _ => 0

/-- The operands of a statement are pairwise distinct, as OpenQASM requires; only `cp`,
    `ccx` and `ccz` need it for `listMatrix_lowerQ`. -/
def Distinct : OpenQASMImport.QGate n → Prop
  | .cp c t _ => c ≠ t
  | .ccx a b t | .ccz a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t
  | _ => True

instance : DecidablePred (Distinct (n := n)) := fun g => by
  cases g <;> unfold Distinct <;> infer_instance

/-- The matrix of a list of statements, head applied first. -/
def qelibListMatrix : List (OpenQASMImport.QGate n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | [] => 1
  | g :: l => qelibListMatrix l * qelibMatrix g

/-- The sum of the phases of a list of statements. -/
def listPhase (l : List (OpenQASMImport.QGate n)) : PiLin :=
  (l.map phase).sum

/-! ## The Toffoli lists -/

/-- `CNOT`s with a common target commute. -/
theorem embedGate2_cnot_comm_target {a b t : Fin n} (hat : a ≠ t) (hbt : b ≠ t) :
    embedGate2 n a t cnot hat * embedGate2 n b t cnot hbt
      = embedGate2 n b t cnot hbt * embedGate2 n a t cnot hat := by
  have hz : embedGate2 n a t czGate hat * embedGate2 n b t czGate hbt
      = embedGate2 n b t czGate hbt * embedGate2 n a t czGate hat := by
    rw [embedGate2_czGate, embedGate2_czGate, pauliZ_eq_rzGate, ctrlMatrix_rzGate,
      ctrlMatrix_rzGate, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    ring
  have hh := embedGate1_hadamard_mul_self (n := n) t
  have e : ∀ A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      embedGate1 n t hadamard * A * embedGate1 n t hadamard *
          (embedGate1 n t hadamard * B * embedGate1 n t hadamard)
        = embedGate1 n t hadamard * (A * B) * embedGate1 n t hadamard := by
    intro A B
    calc _ = embedGate1 n t hadamard * (A * ((embedGate1 n t hadamard *
          embedGate1 n t hadamard) * (B * embedGate1 n t hadamard))) := by
          simp only [mul_assoc]
      _ = _ := by rw [hh, one_mul]; simp only [mul_assoc]
  rw [← hadamard_czGate_hadamard hat, ← hadamard_czGate_hadamard hbt, e, e, hz]

/-- A `CNOT` moves right past a phase diagonal, its parity transformed. -/
theorem cnot_mul_phaseDiag_mul {c t : Fin n} (hct : c ≠ t) (p : Parity n) (θ : ℝ)
    (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    embedGate2 n c t cnot hct * (phaseDiag p θ * X)
      = phaseDiag (cnotParity p c t) θ * (embedGate2 n c t cnot hct * X) := by
  rw [← mul_assoc, cnot_mul_phaseDiag hct, mul_assoc]

/-- Two equal `CNOT`s cancel. -/
theorem cnot_mul_cnot_mul {c t : Fin n} (hct : c ≠ t) (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    embedGate2 n c t cnot hct * (embedGate2 n c t cnot hct * X) = X := by
  rw [← mul_assoc, embedGate2_mul, cnot_sq, embedGate2_one, one_mul]

/-- The `CNOT`-and-`T` part of the Toffoli list, with the trailing gates on the controls:
    the doubly controlled `Z`. -/
theorem listMatrix_ccxPhase {a b t : Fin n} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    listMatrix [Gate.CNOT b t, .Tdg t, .CNOT a t, .T t, .CNOT b t, .Tdg t, .CNOT a t, .T b,
      .T t, .CNOT a b, .T a, .Tdg b, .CNOT a b]
      = ctrlMatrix a (embedGate2 n b t czGate hbt) := by
  have hC : ∀ {x y : Fin n} (h : x ≠ y), gateEmbedding (Gate.CNOT x y) = embedGate2 n x y cnot h :=
    fun h => by simp only [gateEmbedding, dite_eq_right h]
  have hT : ∀ q : Fin n, gateEmbedding (Gate.T q) = phaseDiag (singletonParity q) (Real.pi / 4) :=
    fun q => by rw [gateEmbedding, tGate_eq_rzGate, rz_embed_eq_phaseDiag]
  have hTd : ∀ q : Fin n,
      gateEmbedding (Gate.Tdg q) = phaseDiag (singletonParity q) (-(Real.pi / 4)) :=
    fun q => by rw [gateEmbedding, tDaggerGate_eq_rzGate, rz_embed_eq_phaseDiag]
  have hnet : embedGate2 n a t cnot hat * (embedGate2 n b t cnot hbt *
      (embedGate2 n a t cnot hat * embedGate2 n b t cnot hbt)) = 1 := by
    rw [embedGate2_cnot_comm_target hat hbt, cnot_mul_cnot_mul, embedGate2_mul, cnot_sq,
      embedGate2_one]
  simp only [listMatrix_cons, listMatrix_nil, one_mul, hC hat, hC hbt, hC hab, hT, hTd, mul_assoc,
    cnot_mul_phaseDiag_mul, cnot_mul_cnot_mul, hnet, mul_one]
  rw [embedGate2_czGate, pauliZ_eq_rzGate, ctrlMatrix_ctrlMatrix_rzGate]
  simp only [phaseDiag, Matrix.diagonal_mul_diagonal, ← Complex.exp_add]
  congr 1
  funext x
  congr 1
  simp only [parityForm_cnotParity, parityForm_singletonParity, singletonParity, cnotParity,
    decide_true, ite_true, Bool.xor_true, bitZ]
  generalize gbit n a x.val = u
  generalize gbit n b x.val = v
  generalize gbit n t x.val = w
  fin_cases u <;> fin_cases v <;> fin_cases w <;>
    simp [Ne.symm hab, Ne.symm hat, Ne.symm hbt, ZMod.val_one,
      show ((1 : ZMod 2) + 1) = 0 from by decide]
  ring

/-- The seven-`T` Toffoli list is the doubly controlled `X`, exactly. -/
theorem listMatrix_ccxGates {a b t : Fin n} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    listMatrix (ccxGates a b t) = ctrlMatrix a (embedGate2 n b t cnot hbt) := by
  have hsplit : ccxGates a b t = Gate.H t :: ([Gate.CNOT b t, .Tdg t, .CNOT a t, .T t,
      .CNOT b t, .Tdg t, .CNOT a t, .T b, .T t, .CNOT a b] ++
        Gate.H t :: [.T a, .Tdg b, .CNOT a b]) := rfl
  have hcomm : listMatrix [Gate.T a, .Tdg b, .CNOT a b] * embedGate1 n t hadamard
      = embedGate1 n t hadamard * listMatrix [Gate.T a, .Tdg b, .CNOT a b] :=
    (commOn_listMatrix (by simp [Avoids, hat, hbt]) hadamard).symm
  rw [hsplit, listMatrix_cons, listMatrix_append, listMatrix_cons]
  simp only [gateEmbedding]
  rw [hcomm, mul_assoc (embedGate1 n t hadamard), ← listMatrix_append]
  rw [show [Gate.CNOT b t, .Tdg t, .CNOT a t, .T t, .CNOT b t, .Tdg t, .CNOT a t, .T b, .T t,
      .CNOT a b] ++ [Gate.T a, .Tdg b, .CNOT a b] = [Gate.CNOT b t, .Tdg t, .CNOT a t, .T t,
      .CNOT b t, .Tdg t, .CNOT a t, .T b, .T t, .CNOT a b, .T a, .Tdg b, .CNOT a b] from rfl,
    listMatrix_ccxPhase hab hat hbt,
    mul_ctrlMatrix_mul (commOn_embedGate1 (Ne.symm hat) _) (embedGate1_hadamard_mul_self t),
    hadamard_czGate_hadamard]

/-- The `ccz` list is the doubly controlled `Z`, exactly. -/
theorem listMatrix_cczGates {a b t : Fin n} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    listMatrix (cczGates a b t) = ctrlMatrix a (embedGate2 n b t czGate hbt) := by
  have hh := embedGate1_hadamard_mul_self (n := n) t
  rw [cczGates, listMatrix_append, listMatrix_cons, listMatrix_cons, listMatrix_nil, one_mul,
    listMatrix_ccxGates hab hat hbt, ← mul_assoc]
  simp only [gateEmbedding]
  rw [mul_ctrlMatrix_mul (commOn_embedGate1 (Ne.symm hat) _) hh,
    ← hadamard_czGate_hadamard hbt]
  congr 1
  calc _ = (embedGate1 n t hadamard * embedGate1 n t hadamard) * embedGate2 n b t czGate hbt *
        (embedGate1 n t hadamard * embedGate1 n t hadamard) := by simp only [mul_assoc]
    _ = _ := by rw [hh, one_mul, mul_one]

/-! ## Statements -/

/-- **The lowering of a statement** realises its `qelib1.inc` matrix up to the global phase
    `exp (i · phase g)`. -/
theorem listMatrix_lowerQ (g : OpenQASMImport.QGate n) (hg : Distinct g) :
    listMatrix (lowerQ g) = Complex.exp (Complex.I * (phase g).toReal) • qelibMatrix g := by
  cases g with
  | sdg q =>
    simp only [lowerQ, sdgGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding,
      embedGate1_mul, tDaggerGate_mul_self, phase, qelibMatrix, PiLin.toReal_zero,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
  | sx q => simp [lowerQ, phase, qelibMatrix, listMatrix_sxGates]
  | sxdg q => simp [lowerQ, phase, qelibMatrix, listMatrix_sxdgGates]
  | rx q θ => simp [lowerQ, phase, qelibMatrix, listMatrix_rxGates, PiLin.toReal_div_ofPi]
  | ry q θ => simp [lowerQ, phase, qelibMatrix, listMatrix_ryGates, PiLin.toReal_div_ofPi]
  | rz q θ =>
    simp [lowerQ, phase, qelibMatrix, listMatrix_cons, listMatrix_nil, gateEmbedding,
      PiLin.toReal_div_ofPi, rzGate_eq_smul_rzMatrix θ.toReal, embedGate1_smul]
  | u q θ φ l => simp [lowerQ, phase, qelibMatrix, listMatrix_uGates, PiLin.toReal_div_ofPi]
  | u2 q φ l =>
    rw [lowerQ, listMatrix_uGates]
    simp only [phase, qelibMatrix, PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi,
      PiLin.toReal_ofPi]
    congr 3 <;> push_cast <;> ring
  | swap a b => simp [lowerQ, phase, qelibMatrix, listMatrix_swapCnotGates]
  | cp c t θ => simp [lowerQ, phase, qelibMatrix, listMatrix_cphaseGates (hg : c ≠ t)]
  | ccx a b t =>
    obtain ⟨hab, hat, hbt⟩ := hg
    simp [lowerQ, phase, qelibMatrix, ccxMatrix, hbt, listMatrix_ccxGates hab hat hbt]
  | ccz a b t =>
    obtain ⟨hab, hat, hbt⟩ := hg
    simp [lowerQ, phase, qelibMatrix, cczMatrix, hbt, listMatrix_cczGates hab hat hbt]
  | _ => simp [lowerQ, phase, qelibMatrix, listMatrix_cons, listMatrix_nil, gateEmbedding]

/-- **The lowering of a list of statements** realises the product of their `qelib1.inc`
    matrices up to the global phase `exp (i · listPhase l)`. -/
theorem listMatrix_flatMap_lowerQ (l : List (OpenQASMImport.QGate n))
    (hl : ∀ g ∈ l, Distinct g) :
    listMatrix (l.flatMap lowerQ)
      = Complex.exp (Complex.I * (listPhase l).toReal) • qelibListMatrix l := by
  induction l with
  | nil => simp [listPhase, qelibListMatrix, listMatrix_nil]
  | cons g l ih =>
    rw [List.flatMap_cons, listMatrix_append, ih (fun g' h' => hl g' (by simp [h'])),
      listMatrix_lowerQ g (hl g (by simp)), smul_mul_smul, ← Complex.exp_add]
    simp only [listPhase, List.map_cons, List.sum_cons, PiLin.toReal_add, qelibListMatrix]
    congr 2
    push_cast
    ring

end CatCrypt.Quantum.Qelib
