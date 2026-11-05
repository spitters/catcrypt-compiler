/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.ControlledProjections
public import CatCrypt.Quantum.QFT.Circuit

/-!
# Controlled gates as gate lists

For a gate `g : Gate n` and a control qubit `c` that `g` does not act on, `ctrlGates c g`
is a list of `Gate n` constructors whose matrix is the controlled unitary
`|0⟩⟨0|_c ⊗ I + |1⟩⟨1|_c ⊗ U_g`, exactly, with no global phase. The conventions are those
of `embedGate1` and `embedGate2` (qubit `0` is the most significant bit), and the matrix of
a list is `QFT.listMatrix` (head gate applied first).

The decompositions are the standard ones:

* `X`, `Z`: one `CNOT`, one `CZ`;
* `Y = S X S†`: `S†; CNOT; S` on the target;
* `H`: `S; H; T; CNOT; T†; H; S†` on the target;
* the phase gates `S`, `T`, `T†`, `Rz θ`, `RzQ a`: the controlled phase
  `CNOT; P(-θ/2)_t; CNOT; P(θ/2)_c; P(θ/2)_t`;
* `CZ`: a seven-`T` doubly controlled `Z` written as four conjugated phases,
  `CCZ = T_c T_a T_b · (CNOT T† CNOT)³ · (CNOT CNOT T CNOT CNOT)`;
* `CNOT`: the Toffoli `H_b · CCZ · H_b`.

Multi-controlled gates `mctrlGates cs g` control every gate of `mctrlGates cs' g` on the
next qubit, ancilla-free; their matrix is `mctrlMatrix cs U_g`, which is the identity plus
`(∏ |1⟩⟨1|_c) (U_g - I)`.

## Main results

* `ctrlMatrix_mul` — controlling on `c` is multiplicative on matrices that commute with
  every single-qubit operator on `c`.
* `listMatrix_ctrl_sandwich` — `L₁ ++ CNOT c t :: L₂` with `L₁`, `L₂` avoiding `c` and
  `L₂ L₁ = I` realises the control of `L₂ X_t L₁`.
* `listMatrix_ctrlGates` — the matrix of `ctrlGates c g` is `ctrlMatrix c (gateEmbedding g)`.
* `listMatrix_ctrlList` — controlling a gate list gate by gate controls its matrix.
* `listMatrix_mctrlGates` — the matrix of `mctrlGates cs g` is
  `mctrlMatrix cs (gateEmbedding g)`.
* `mctrlMatrix_eq` — `mctrlMatrix cs M = 1 + (∏_{c ∈ cs} |1⟩⟨1|_c) * (M - 1)`.
* `listMatrix_branchGates` — two lists controlled on `|0⟩` and `|1⟩` of `c`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.Optimization.PhasePolySemantics
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append)
open CatCrypt.Quantum.OpenQASMImport (cphaseGates)
open CatCrypt.Quantum.Optimization.PhasePolynomial (Parity)

noncomputable section

namespace CatCrypt.Quantum.ControlledGates

variable {n : ℕ}

/-! ## The two-branch matrix -/

/-- The two-branch matrix on qubit `c`: `|0⟩⟨0|_c ⊗ M₀ + |1⟩⟨1|_c ⊗ M₁`. -/
def branchMatrix (c : Fin n) (M₀ M₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  embedGate1 n c proj0 * M₀ + embedGate1 n c proj1 * M₁

/-- `M` commutes with every single-qubit operator on `c`. -/
def CommOn (c : Fin n) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  ∀ G : Matrix (Fin 2) (Fin 2) ℂ, embedGate1 n c G * M = M * embedGate1 n c G

/-! ## Commutation with the control qubit -/

theorem commOn_one (c : Fin n) : CommOn c 1 := fun G => by rw [one_mul, mul_one]

theorem CommOn.mul {c : Fin n} {M N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn c M) (hN : CommOn c N) : CommOn c (M * N) := fun G => by
  rw [← mul_assoc, hM G, mul_assoc, hN G, mul_assoc]

theorem commOn_embedGate1 {c t : Fin n} (h : t ≠ c) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    CommOn c (embedGate1 n t G) := fun H => embedGate1_disjoint_comm (Ne.symm h) H G

theorem commOn_embedGate2 {c i j : Fin n} (hi : i ≠ c) (hj : j ≠ c) (hij : i ≠ j)
    (G : Matrix (Fin 4) (Fin 4) ℂ) : CommOn c (embedGate2 n i j G hij) := fun H =>
  embedGate1_embedGate2_disjoint_comm (Ne.symm hi) (Ne.symm hj) hij H G

/-- The gate `g` does not act on qubit `c`. -/
def Avoids (c : Fin n) : Gate n → Prop
  | .H i | .X i | .Y i | .Z i | .T i | .Tdg i | .S i => i ≠ c
  | .Rz i _ | .RzQ i _ => i ≠ c
  | .CNOT i j | .CZ i j => i ≠ c ∧ j ≠ c

theorem commOn_gateEmbedding {c : Fin n} {g : Gate n} (h : Avoids c g) :
    CommOn c (gateEmbedding g) := by
  cases g with
  | CNOT i j =>
    by_cases hij : i = j
    · simp only [gateEmbedding, dite_eq_left hij]; exact commOn_one c
    · simp only [gateEmbedding, dite_eq_right hij]; exact commOn_embedGate2 h.1 h.2 hij _
  | CZ i j =>
    by_cases hij : i = j
    · simp only [gateEmbedding, dite_eq_left hij]; exact commOn_one c
    · simp only [gateEmbedding, dite_eq_right hij]; exact commOn_embedGate2 h.1 h.2 hij _
  | _ => exact commOn_embedGate1 h _

theorem commOn_listMatrix {c : Fin n} :
    ∀ {L : List (Gate n)}, (∀ g ∈ L, Avoids c g) → CommOn c (listMatrix L)
  | [], _ => commOn_one c
  | g :: L, h => by
    rw [listMatrix_cons]
    exact (commOn_listMatrix fun g' hg' => h g' (List.mem_cons_of_mem g hg')).mul
      (commOn_gateEmbedding (h g List.mem_cons_self))

/-! ## The algebra of controlled matrices -/

theorem embedGate1_proj_mul {c : Fin n} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn c M) (P Q : Matrix (Fin 2) (Fin 2) ℂ) (N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    embedGate1 n c P * M * (embedGate1 n c Q * N) = embedGate1 n c (P * Q) * (M * N) := by
  rw [← embedGate1_mul, mul_assoc, ← mul_assoc M, ← hM Q, mul_assoc, mul_assoc]

/-- Two-branch matrices multiply branchwise. -/
theorem branchMatrix_mul {c : Fin n} {M₀ M₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h₀ : CommOn c M₀) (h₁ : CommOn c M₁) (N₀ N₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    branchMatrix c M₀ M₁ * branchMatrix c N₀ N₁ = branchMatrix c (M₀ * N₀) (M₁ * N₁) := by
  simp only [branchMatrix, add_mul, mul_add, embedGate1_proj_mul h₀, embedGate1_proj_mul h₁,
    proj0_mul_proj0, proj0_mul_proj1, proj1_mul_proj0, proj1_mul_proj1, embedGate1_map_zero,
    zero_mul, add_zero, zero_add]

theorem ctrlMatrix_eq_branchMatrix (c : Fin n) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ctrlMatrix c M = branchMatrix c 1 M := by
  rw [ctrlMatrix, branchMatrix, mul_one]

theorem branchMatrix_self {c : Fin n} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    branchMatrix c M M = M := by
  rw [branchMatrix, ← add_mul, embedGate1_proj0_add_proj1, one_mul]

/-- Controlling on `c` is multiplicative. -/
theorem ctrlMatrix_mul {c : Fin n} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn c M) (N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ctrlMatrix c M * ctrlMatrix c N = ctrlMatrix c (M * N) := by
  rw [ctrlMatrix_eq_branchMatrix, ctrlMatrix_eq_branchMatrix, ctrlMatrix_eq_branchMatrix,
    branchMatrix_mul (commOn_one c) hM, one_mul]

/-- Conjugating a controlled matrix by `A`, `B` with `A * B = 1` and `A` commuting with the
    control gives the control of the conjugate. -/
theorem mul_ctrlMatrix_mul {c : Fin n} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hA : CommOn c A) (hAB : A * B = 1) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    A * ctrlMatrix c M * B = ctrlMatrix c (A * M * B) := by
  rw [ctrlMatrix, ctrlMatrix, mul_add, add_mul, ← hA proj0, mul_assoc, hAB, mul_one,
    ← mul_assoc A, ← hA proj1]
  simp only [mul_assoc]

/-! ## The sandwich lemma -/

/-- A gate list `L₁ ++ g₀ :: L₂` whose middle gate `g₀` is a controlled `M`, and whose outer
    lists avoid the control and multiply to the identity, realises the control of
    `L₂ · M · L₁`. -/
theorem listMatrix_ctrl_sandwich {c : Fin n} {g₀ : Gate n}
    {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hg : gateEmbedding g₀ = ctrlMatrix c M)
    {L₁ L₂ : List (Gate n)} (h₂ : ∀ g ∈ L₂, Avoids c g)
    (hid : listMatrix L₂ * listMatrix L₁ = 1) :
    listMatrix (L₁ ++ g₀ :: L₂) = ctrlMatrix c (listMatrix L₂ * M * listMatrix L₁) := by
  rw [listMatrix_append, listMatrix_cons, hg,
    mul_ctrlMatrix_mul (commOn_listMatrix h₂) hid]

/-! ## Single-qubit `2 × 2` identities -/

theorem exp_pi_div_four :
    Complex.exp (Complex.I * ↑(Real.pi / 4)) = ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 + Complex.I) := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

theorem exp_neg_pi_div_four :
    Complex.exp (-Complex.I * ↑(Real.pi / 4)) = ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 - Complex.I) := by
  rw [neg_mul, ← mul_neg, mul_comm, ← Complex.ofReal_neg, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

/-- The target branch of the controlled `Y`: `S · X · S† = Y`. -/
theorem phaseS_pauliX_sdg : phaseS * pauliX * (phaseS * pauliZ) = pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [phaseS, pauliX, pauliZ, pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- `S · S† = 1`. -/
theorem phaseS_sdg : phaseS * (phaseS * pauliZ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [phaseS, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The control branch of the controlled `H`: `S† H T† · T H S = 1`. -/
theorem ctrlH_id :
    pauliZ * phaseS * hadamard * tDaggerGate * (tGate * hadamard * phaseS) = 1 := by
  have h1 : pauliZ * phaseS * hadamard * tDaggerGate * (tGate * hadamard * phaseS)
      = pauliZ * phaseS * (hadamard * (tDaggerGate * tGate) * hadamard) * phaseS := by
    simp only [mul_assoc]
  rw [h1, tDaggerGate_mul_tGate, mul_one, hadamard_sq, mul_one, mul_assoc, phaseS_sq_eq_pauliZ]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The target branch of the controlled `H`: `S† H T† · X · T H S = H`. -/
theorem ctrlH_target :
    pauliZ * phaseS * hadamard * tDaggerGate * pauliX * (tGate * hadamard * phaseS)
      = hadamard := by
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  rw [tGate, tDaggerGate, exp_pi_div_four, exp_neg_pi_div_four]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, phaseS, hadamard, pauliX, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq]

/-! ## Diagonal matrices and the controlled phase -/

theorem isDiagonal_rzGate (θ : ℝ) : IsDiagonal (rzGate θ) :=
  rzGate_isDiagonal θ

/-- A single-qubit embedding of a diagonal matrix is the diagonal matrix of its entries at
    the qubit's bit. -/
theorem embedGate1_eq_diagonal (q : Fin n) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : IsDiagonal G) :
    embedGate1 n q G = Matrix.diagonal fun x : Fin (2 ^ n) =>
      G (gbit n q x.val) (gbit n q x.val) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    have hM : Match n q x.val x.val := fun _ _ => rfl
    rw [CatCrypt.Quantum.Optimization.DisjointCommute.embedGate1_apply, ite_eq_left hM,
      Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    exact embedGate1_isDiagonal q hG x y hxy

/-- The controlled phase is the diagonal with phase `exp (i θ)` where both qubits read `1`. -/
theorem ctrlMatrix_rzGate (c t : Fin n) (θ : ℝ) :
    ctrlMatrix c (embedGate1 n t (rzGate θ)) = Matrix.diagonal fun x : Fin (2 ^ n) =>
      Complex.exp (Complex.I * θ * ((gbit n c x.val).val : ℂ) * ((gbit n t x.val).val : ℂ)) := by
  rw [ctrlMatrix, embedGate1_eq_diagonal c isDiagonal_proj0,
    embedGate1_eq_diagonal c isDiagonal_proj1, embedGate1_eq_diagonal t (isDiagonal_rzGate θ),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
  congr 1
  funext x
  generalize gbit n c x.val = u
  generalize gbit n t x.val = v
  fin_cases u <;> fin_cases v <;> simp [proj0, proj1, rzGate]

/-- Conjugating a parity by `CNOT` adds the control bit when the parity selects the target. -/
theorem parityForm_cnotParity (p : Parity n) (c t : Fin n) (x : ℕ) :
    parityForm (cnotParity p c t) x = parityForm p x + if p t then bitZ n c x else 0 := by
  have h2 : ∀ u : ZMod 2, u + u = 0 := by decide
  have hi : ∀ i : Fin n, (if cnotParity p c t i then bitZ n i x else 0)
      = (if p i then bitZ n i x else 0) + if i = c then (if p t then bitZ n c x else 0) else 0 := by
    intro i
    by_cases hic : i = c
    · subst hic
      cases hpi : p i <;> cases hpt : p t <;> simp [cnotParity, hpi, hpt, h2]
    · simp [cnotParity, hic]
  simp only [parityForm, hi, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The controlled phase by `2α` as the product `P(α)_t P(α)_c · CNOT · P(-α)_t · CNOT`. -/
theorem cphase_matrix {c t : Fin n} (hct : c ≠ t) (α : ℝ) :
    embedGate1 n t (rzGate α) * embedGate1 n c (rzGate α) * embedGate2 n c t cnot hct
        * embedGate1 n t (rzGate (-α)) * embedGate2 n c t cnot hct
      = ctrlMatrix c (embedGate1 n t (rzGate (2 * α))) := by
  rw [rz_embed_eq_phaseDiag, rz_embed_eq_phaseDiag, rz_embed_eq_phaseDiag, mul_assoc,
    mul_assoc, ← mul_assoc (embedGate2 n c t cnot hct), cnot_conj_phaseDiag hct,
    ctrlMatrix_rzGate]
  simp only [phaseDiag, Matrix.diagonal_mul_diagonal, parityForm_singletonParity,
    parityForm_cnotParity, ← Complex.exp_add]
  congr 1
  funext x
  congr 1
  simp only [singletonParity, decide_true, ite_true, bitZ]
  generalize gbit n c x.val = u
  generalize gbit n t x.val = v
  fin_cases u <;> fin_cases v <;>
    simp [ZMod.val_one, show ((1 : ZMod 2) + 1) = 0 from by decide]
  ring

theorem tDaggerGate_eq_rzGate : tDaggerGate = rzGate (-(Real.pi / 4)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tDaggerGate, rzGate]

theorem tGate_eq_rzGate : tGate = rzGate (Real.pi / 4) := rfl

theorem phaseS_eq_rzGate : phaseS = rzGate (2 * (Real.pi / 4)) := by
  have h : Complex.exp (Complex.I * ↑(2 * (Real.pi / 4))) = Complex.I := by
    rw [show (2 * (Real.pi / 4) : ℝ) = Real.pi / 2 by ring, mul_comm, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [rzGate, h, phaseS]

theorem pauliZ_eq_rzGate : pauliZ = rzGate Real.pi := by
  have h : Complex.exp (Complex.I * ↑Real.pi) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, rzGate, h]

/-- A diagonal matrix controlled on `c` is diagonal. -/
theorem ctrlMatrix_diagonal (c : Fin n) (f : Fin (2 ^ n) → ℂ) :
    ctrlMatrix c (Matrix.diagonal f) = Matrix.diagonal fun x : Fin (2 ^ n) =>
      proj0 (gbit n c x.val) (gbit n c x.val) + proj1 (gbit n c x.val) (gbit n c x.val) * f x := by
  rw [ctrlMatrix, embedGate1_eq_diagonal c isDiagonal_proj0,
    embedGate1_eq_diagonal c isDiagonal_proj1, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add]

/-- The doubly controlled phase is the diagonal with phase `exp (i θ)` where all three
    qubits read `1`. -/
theorem ctrlMatrix_ctrlMatrix_rzGate (c a b : Fin n) (θ : ℝ) :
    ctrlMatrix c (ctrlMatrix a (embedGate1 n b (rzGate θ))) = Matrix.diagonal fun x : Fin (2 ^ n) =>
      Complex.exp (Complex.I * θ * ((gbit n c x.val).val : ℂ) * ((gbit n a x.val).val : ℂ)
        * ((gbit n b x.val).val : ℂ)) := by
  rw [ctrlMatrix_rzGate, ctrlMatrix_diagonal]
  congr 1
  funext x
  generalize gbit n c x.val = u
  fin_cases u <;> simp [proj0, proj1, mul_assoc]

/-! ## `CNOT`-conjugated phases and the doubly controlled `Z` -/

/-- The list `CNOT x y; L; CNOT x y`. -/
def cnotConj (x y : Fin n) (L : List (Gate n)) : List (Gate n) :=
  Gate.CNOT x y :: (L ++ [Gate.CNOT x y])

theorem listMatrix_cnotConj {x y : Fin n} (hxy : x ≠ y) (L : List (Gate n)) :
    listMatrix (cnotConj x y L)
      = embedGate2 n x y cnot hxy * listMatrix L * embedGate2 n x y cnot hxy := by
  rw [cnotConj, listMatrix_cons, listMatrix_append, listMatrix_cons, listMatrix_nil, one_mul,
    gateEmbedding, dite_eq_right hxy]

theorem listMatrix_cnotConj_phaseDiag {x y : Fin n} (hxy : x ≠ y) {L : List (Gate n)}
    {p : Parity n} {θ : ℝ} (h : listMatrix L = phaseDiag p θ) :
    listMatrix (cnotConj x y L) = phaseDiag (cnotParity p x y) θ := by
  rw [listMatrix_cnotConj hxy, h, cnot_conj_phaseDiag hxy]

theorem listMatrix_T (q : Fin n) :
    listMatrix [Gate.T q] = phaseDiag (singletonParity q) (Real.pi / 4) := by
  rw [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, tGate_eq_rzGate,
    rz_embed_eq_phaseDiag]

theorem listMatrix_Tdg (q : Fin n) :
    listMatrix [Gate.Tdg q] = phaseDiag (singletonParity q) (-(Real.pi / 4)) := by
  rw [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, tDaggerGate_eq_rzGate,
    rz_embed_eq_phaseDiag]

/-- The doubly controlled `Z` on `c`, `a`, `b` with seven `T` gates: the phase
    `ω^(c + a + b - (c⊕a) - (a⊕b) - (c⊕b) + (c⊕a⊕b)) = (-1)^(c a b)`, `ω = exp (i π / 4)`,
    as three single-qubit `T`s and four `CNOT`-conjugated phases. -/
def cczPhaseGates (c a b : Fin n) : List (Gate n) :=
  [Gate.T c, Gate.T a, Gate.T b] ++ cnotConj c a [Gate.Tdg a] ++ cnotConj a b [Gate.Tdg b]
    ++ cnotConj c b [Gate.Tdg b] ++ cnotConj c a (cnotConj a b [Gate.T b])

theorem listMatrix_cczPhaseGates {c a b : Fin n} (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    listMatrix (cczPhaseGates c a b) = ctrlMatrix c (embedGate2 n a b czGate hab) := by
  rw [embedGate2_czGate, pauliZ_eq_rzGate, ctrlMatrix_ctrlMatrix_rzGate, cczPhaseGates]
  simp only [listMatrix_append,
    listMatrix_cnotConj_phaseDiag hca (listMatrix_cnotConj_phaseDiag hab (listMatrix_T b)),
    listMatrix_cnotConj_phaseDiag hcb (listMatrix_Tdg b),
    listMatrix_cnotConj_phaseDiag hab (listMatrix_Tdg b),
    listMatrix_cnotConj_phaseDiag hca (listMatrix_Tdg a), listMatrix_cons, listMatrix_nil,
    one_mul, gateEmbedding, tGate_eq_rzGate, rz_embed_eq_phaseDiag]
  simp only [phaseDiag, Matrix.diagonal_mul_diagonal, ← Complex.exp_add]
  congr 1
  funext x
  congr 1
  simp only [parityForm_cnotParity, parityForm_singletonParity, singletonParity, cnotParity,
    decide_true, ite_true, Bool.xor_true, bitZ]
  generalize gbit n c x.val = u
  generalize gbit n a x.val = v
  generalize gbit n b x.val = w
  fin_cases u <;> fin_cases v <;> fin_cases w <;>
    simp [hab, ZMod.val_one, show ((1 : ZMod 2) + 1) = 0 from by decide]
  ring

theorem embedGate1_hadamard_mul_self (q : Fin n) :
    embedGate1 n q hadamard * embedGate1 n q hadamard = 1 := by
  rw [embedGate1_mul, hadamard_sq, embedGate1_one]

/-- `H_b · CZ(a, b) · H_b = CNOT(a, b)`. -/
theorem hadamard_czGate_hadamard {a b : Fin n} (hab : a ≠ b) :
    embedGate1 n b hadamard * embedGate2 n a b czGate hab * embedGate1 n b hadamard
      = embedGate2 n a b cnot hab := by
  rw [embedGate2_czGate, mul_ctrlMatrix_mul (commOn_embedGate1 (Ne.symm hab) _)
    (embedGate1_hadamard_mul_self b), embedGate1_mul, embedGate1_mul, hadamard_pauliZ_hadamard,
    embedGate2_cnot]

/-- The Toffoli gate with controls `c`, `a` and target `b`: `H_b · CCZ · H_b`. -/
def toffoliGates (c a b : Fin n) : List (Gate n) :=
  Gate.H b :: (cczPhaseGates c a b ++ [Gate.H b])

theorem listMatrix_toffoliGates {c a b : Fin n} (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    listMatrix (toffoliGates c a b) = ctrlMatrix c (embedGate2 n a b cnot hab) := by
  rw [toffoliGates, listMatrix_cons, listMatrix_append, listMatrix_cons, listMatrix_nil, one_mul,
    listMatrix_cczPhaseGates hca hcb hab]
  show embedGate1 n b hadamard * _ * embedGate1 n b hadamard = _
  rw [mul_ctrlMatrix_mul (commOn_embedGate1 (Ne.symm hcb) _) (embedGate1_hadamard_mul_self b),
    hadamard_czGate_hadamard]

/-! ## Controlled gates -/

/-- The controlled phase `diag(1, 1, 1, exp (i θ))` on `c`, `t`:
    `CNOT; P(-θ/2)_t; CNOT; P(θ/2)_c; P(θ/2)_t`, with the half angle written
    `θ * (1/2 : ℚ)`. -/
def cphaseRz (c t : Fin n) (θ : ℝ) : List (Gate n) :=
  [Gate.CNOT c t, Gate.Rz t (-(θ * ((1 / 2 : ℚ) : ℝ))), Gate.CNOT c t,
    Gate.Rz c (θ * ((1 / 2 : ℚ) : ℝ)), Gate.Rz t (θ * ((1 / 2 : ℚ) : ℝ))]

theorem listMatrix_cphaseRz {c t : Fin n} (hct : c ≠ t) (θ : ℝ) :
    listMatrix (cphaseRz c t θ) = ctrlMatrix c (embedGate1 n t (rzGate θ)) := by
  have h := cphase_matrix hct (θ * ((1 / 2 : ℚ) : ℝ))
  rw [show 2 * (θ * ((1 / 2 : ℚ) : ℝ)) = θ by push_cast; ring] at h
  simp only [cphaseRz, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, dite_eq_right hct]
  exact h

/-- The matrix of `cphaseGates c t a` is `Rz a` on `t` controlled on `c`. -/
theorem listMatrix_cphaseGates {c t : Fin n} (hct : c ≠ t) (a : PiLin) :
    listMatrix (cphaseGates c t a) =
      ctrlMatrix c (embedGate1 n t (rzGate a.toReal)) := by
  have hpos : PiLin.toReal (a / 2) = a.toReal / 2 := by
    rw [PiLin.ofNat_eq_ofPi, PiLin.toReal_div_ofPi]; norm_num
  have hneg : PiLin.toReal (-(a / 2)) = -(a.toReal / 2) := by
    rw [PiLin.toReal_neg, hpos]
  have h2 : 2 * (a.toReal / 2) = a.toReal := by ring
  simp only [cphaseGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding,
    dite_eq_right hct, hneg, hpos]
  rw [cphase_matrix hct, h2]

/-- The gate `g` controlled on qubit `c`, as a list of `Gate` constructors. The
    rotations `T`, `T†` are controlled at the angles `1/4` and `-1/4` of `π`. -/
def ctrlGates (c : Fin n) : Gate n → List (Gate n)
  | .H t => [.S t, .H t, .T t, .CNOT c t, .Tdg t, .H t, .S t, .Z t]
  | .X t => [.CNOT c t]
  | .Y t => [.Z t, .S t, .CNOT c t, .S t]
  | .Z t => [.CZ c t]
  | .T t => cphaseGates c t (1 / 4)
  | .Tdg t => cphaseGates c t (-(1 / 4))
  | .S t => [.CNOT c t, .Tdg t, .CNOT c t, .T c, .T t]
  | .Rz t θ => cphaseRz c t θ
  | .RzQ t a => cphaseGates c t a
  | .CNOT a b => if a = b then [] else toffoliGates c a b
  | .CZ a b => if a = b then [] else cczPhaseGates c a b

theorem ctrlMatrix_one (c : Fin n) : ctrlMatrix c 1 = 1 := by
  rw [ctrlMatrix, mul_one, embedGate1_proj0_add_proj1]

/-- **Controlled gates.** The matrix of `ctrlGates c g` is `U_g` controlled on `c`. -/
theorem listMatrix_ctrlGates {c : Fin n} {g : Gate n} (h : Avoids c g) :
    listMatrix (ctrlGates c g) = ctrlMatrix c (gateEmbedding g) := by
  cases g with
  | H t =>
    have hct : c ≠ t := Ne.symm h
    show listMatrix ([Gate.S t, Gate.H t, Gate.T t] ++ Gate.CNOT c t ::
      [Gate.Tdg t, Gate.H t, Gate.S t, Gate.Z t]) = _
    rw [listMatrix_ctrl_sandwich (gateEmbedding_CNOT hct) (by simp [Avoids, hct.symm])
      (by simp only [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul,
        ctrlH_id, embedGate1_one])]
    simp only [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul,
      ctrlH_target]
  | X t => rw [ctrlGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding_CNOT (Ne.symm h),
      gateEmbedding]
  | Y t =>
    have hct : c ≠ t := Ne.symm h
    show listMatrix ([Gate.Z t, Gate.S t] ++ Gate.CNOT c t :: [Gate.S t]) = _
    rw [listMatrix_ctrl_sandwich (gateEmbedding_CNOT hct) (by simp [Avoids, hct.symm])
      (by simp only [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul,
        phaseS_sdg, embedGate1_one])]
    simp only [listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul,
      phaseS_pauliX_sdg]
  | Z t => rw [ctrlGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding_CZ (Ne.symm h),
      gateEmbedding]
  | T t =>
    rw [ctrlGates, listMatrix_cphaseGates (Ne.symm h), gateEmbedding, tGate_eq_rzGate]
    simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.toReal_ofPi]
    push_cast
    ring_nf
  | Tdg t =>
    rw [ctrlGates, listMatrix_cphaseGates (Ne.symm h), gateEmbedding, tDaggerGate_eq_rzGate]
    simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.neg_ofPi,
      PiLin.toReal_ofPi]
    push_cast
    ring_nf
  | S t =>
    have hct : c ≠ t := Ne.symm h
    simp only [ctrlGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, dite_eq_right hct,
      tGate_eq_rzGate, tDaggerGate_eq_rzGate]
    rw [cphase_matrix hct, ← phaseS_eq_rzGate]
  | Rz t θ => rw [ctrlGates, listMatrix_cphaseRz (Ne.symm h), gateEmbedding]
  | RzQ t a => rw [ctrlGates, listMatrix_cphaseGates (Ne.symm h), gateEmbedding]
  | CNOT a b =>
    by_cases hab : a = b
    · simp only [ctrlGates, gateEmbedding, ite_eq_left hab, dite_eq_left hab, listMatrix_nil, ctrlMatrix_one]
    · simp only [ctrlGates, gateEmbedding, ite_eq_right hab, dite_eq_right hab]
      exact listMatrix_toffoliGates (Ne.symm h.1) (Ne.symm h.2) hab
  | CZ a b =>
    by_cases hab : a = b
    · simp only [ctrlGates, gateEmbedding, ite_eq_left hab, dite_eq_left hab, listMatrix_nil, ctrlMatrix_one]
    · simp only [ctrlGates, gateEmbedding, ite_eq_right hab, dite_eq_right hab]
      exact listMatrix_cczPhaseGates (Ne.symm h.1) (Ne.symm h.2) hab
/-- The gates of `ctrlGates c g` act only on `c` and the qubits of `g`. -/
theorem avoids_ctrlGates {c d : Fin n} {g : Gate n} (hcd : c ≠ d) (hg : Avoids d g) :
    ∀ g' ∈ ctrlGates c g, Avoids d g' := by
  cases g with
  | CNOT a b =>
    by_cases hab : a = b
    · simp [ctrlGates, hab]
    · simp only [ctrlGates, ite_eq_right hab, toffoliGates, cczPhaseGates, cnotConj]
      simp_all [Avoids]
  | CZ a b =>
    by_cases hab : a = b
    · simp [ctrlGates, hab]
    · simp only [ctrlGates, ite_eq_right hab, cczPhaseGates, cnotConj]
      simp_all [Avoids]
  | _ => simp_all [ctrlGates, cphaseRz, cphaseGates, Avoids]

/-- The list `L` controlled on `c`, gate by gate. -/
def ctrlList (c : Fin n) (L : List (Gate n)) : List (Gate n) := L.flatMap (ctrlGates c)

/-- Controlling a gate list gate by gate controls its matrix. -/
theorem listMatrix_ctrlList {c : Fin n} :
    ∀ {L : List (Gate n)}, (∀ g ∈ L, Avoids c g) →
      listMatrix (ctrlList c L) = ctrlMatrix c (listMatrix L)
  | [], _ => by rw [ctrlList, List.flatMap_nil, listMatrix_nil, ctrlMatrix_one]
  | g :: L, h => by
    have hL : ∀ g' ∈ L, Avoids c g' := fun g' hg' => h g' (List.mem_cons_of_mem g hg')
    rw [ctrlList, List.flatMap_cons, listMatrix_append, ← ctrlList, listMatrix_ctrlList hL,
      listMatrix_ctrlGates (h g List.mem_cons_self), listMatrix_cons,
      ctrlMatrix_mul (commOn_listMatrix hL)]

theorem avoids_ctrlList {c d : Fin n} (hcd : c ≠ d) {L : List (Gate n)}
    (hL : ∀ g ∈ L, Avoids d g) : ∀ g' ∈ ctrlList c L, Avoids d g' := by
  intro g' hg'
  obtain ⟨g, hg, hg'⟩ := List.mem_flatMap.mp hg'
  exact avoids_ctrlGates hcd (hL g hg) g' hg'

/-! ## Multi-controlled gates -/

/-- The gate `g` controlled on every qubit of `cs`, ancilla-free: each gate of the list
    for the tail is controlled on the head. -/
def mctrlGates : List (Fin n) → Gate n → List (Gate n)
  | [], g => [g]
  | c :: cs, g => ctrlList c (mctrlGates cs g)

/-- The matrix `M` controlled on every qubit of `cs`. -/
def mctrlMatrix : List (Fin n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ →
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | [], M => M
  | c :: cs, M => ctrlMatrix c (mctrlMatrix cs M)

theorem avoids_mctrlGates {d : Fin n} {g : Gate n} (hg : Avoids d g) :
    ∀ {cs : List (Fin n)}, d ∉ cs → ∀ g' ∈ mctrlGates cs g, Avoids d g'
  | [], _, g', hg' => by
    rw [mctrlGates, List.mem_singleton] at hg'
    exact hg' ▸ hg
  | c :: cs, hd, g', hg' => by
    rw [List.mem_cons, not_or] at hd
    exact avoids_ctrlList (Ne.symm hd.1) (avoids_mctrlGates hg hd.2) g' hg'

/-- **Multi-controlled gates.** For distinct controls that `g` does not act on, the matrix of
    `mctrlGates cs g` is `U_g` controlled on every qubit of `cs`. -/
theorem listMatrix_mctrlGates {g : Gate n} :
    ∀ {cs : List (Fin n)}, cs.Nodup → (∀ c ∈ cs, Avoids c g) →
      listMatrix (mctrlGates cs g) = mctrlMatrix cs (gateEmbedding g)
  | [], _, _ => by rw [mctrlGates, mctrlMatrix, listMatrix_cons, listMatrix_nil, one_mul]
  | c :: cs, hnd, h => by
    rw [List.nodup_cons] at hnd
    have hcs : ∀ c' ∈ cs, Avoids c' g := fun c' hc' => h c' (List.mem_cons_of_mem c hc')
    rw [mctrlGates, mctrlMatrix,
      listMatrix_ctrlList (avoids_mctrlGates (h c List.mem_cons_self) hnd.1),
      listMatrix_mctrlGates hnd.2 hcs]

theorem ctrlMatrix_eq_one_add (c : Fin n) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ctrlMatrix c M = 1 + embedGate1 n c proj1 * (M - 1) := by
  rw [ctrlMatrix, mul_sub, mul_one, ← embedGate1_proj0_add_proj1 c]
  abel

/-- The multi-controlled matrix is the identity plus `(∏_{c ∈ cs} |1⟩⟨1|_c) (M - I)`. -/
theorem mctrlMatrix_eq (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ∀ cs : List (Fin n),
      mctrlMatrix cs M = 1 + (cs.map fun c => embedGate1 n c proj1).prod * (M - 1)
  | [] => by rw [mctrlMatrix, List.map_nil, List.prod_nil, one_mul]; abel
  | c :: cs => by
    rw [mctrlMatrix, mctrlMatrix_eq M cs, ctrlMatrix_eq_one_add, List.map_cons, List.prod_cons,
      add_sub_cancel_left, mul_assoc]

/-! ## Two branches on one control -/

/-- `X_c` conjugates the control on `|1⟩` into the control on `|0⟩`. -/
theorem pauliX_ctrlMatrix_pauliX {c : Fin n} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn c M) :
    embedGate1 n c pauliX * ctrlMatrix c M * embedGate1 n c pauliX = branchMatrix c M 1 := by
  have h1 : embedGate1 n c pauliX * (embedGate1 n c proj1 * M) * embedGate1 n c pauliX
      = embedGate1 n c (pauliX * proj1 * pauliX) * M := by
    rw [mul_assoc, mul_assoc, ← hM pauliX, ← embedGate1_mul, ← embedGate1_mul]
    simp only [mul_assoc]
  rw [ctrlMatrix, mul_add, add_mul, h1, embedGate1_mul, embedGate1_mul, pauliX_proj0_pauliX,
    pauliX_proj1_pauliX, branchMatrix, mul_one, add_comm]

/-- `L₀` on the `|0⟩` branch and `L₁` on the `|1⟩` branch of qubit `c`:
    `X_c; ctrl L₀; X_c; ctrl L₁`. -/
def branchGates (c : Fin n) (L₀ L₁ : List (Gate n)) : List (Gate n) :=
  Gate.X c :: (ctrlList c L₀ ++ Gate.X c :: ctrlList c L₁)

/-- **Two branches.** The matrix of `branchGates c L₀ L₁` is
    `|0⟩⟨0|_c ⊗ L₀ + |1⟩⟨1|_c ⊗ L₁`. -/
theorem listMatrix_branchGates {c : Fin n} {L₀ L₁ : List (Gate n)}
    (h₀ : ∀ g ∈ L₀, Avoids c g) (h₁ : ∀ g ∈ L₁, Avoids c g) :
    listMatrix (branchGates c L₀ L₁) = branchMatrix c (listMatrix L₀) (listMatrix L₁) := by
  rw [branchGates, listMatrix_cons, listMatrix_append, listMatrix_cons, listMatrix_ctrlList h₀,
    listMatrix_ctrlList h₁]
  show ctrlMatrix c (listMatrix L₁) * embedGate1 n c pauliX * ctrlMatrix c (listMatrix L₀)
      * embedGate1 n c pauliX = _
  rw [mul_assoc (ctrlMatrix c (listMatrix L₁)) (embedGate1 n c pauliX), mul_assoc,
    pauliX_ctrlMatrix_pauliX (commOn_listMatrix h₀), ctrlMatrix_eq_branchMatrix,
    branchMatrix_mul (commOn_one c) (commOn_listMatrix h₁), one_mul, mul_one]

end CatCrypt.Quantum.ControlledGates
