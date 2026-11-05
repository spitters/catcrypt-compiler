/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QFT.Spec
public import CatCrypt.Quantum.OpenQASMImport
public import CatCrypt.Quantum.Optimization.PhasePolySemantics
public import CatCrypt.Quantum.Optimization.SwapConj
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# A width-generic circuit for the quantum Fourier transform

The textbook circuit: on the first qubit a Hadamard followed by the phases
`2π / 2 ^ k` controlled by the later qubits, then the same circuit on the
remaining qubits. Qubit `0` is the most significant bit of the basis index
(`embedGate1`), as in Nielsen and Chuang, so the circuit without the final
swaps realises the transform with the bits of the output index reversed.

## Main definitions

* `succGate` — a gate on `n` qubits relabelled to the last `n` of `n + 1`.
* `blk A M` — the matrix `A ⊗ M` on `Fin (2 ^ (n + 1))`, the first qubit
  carrying `A`.
* `qftPhaseGates n` — the controlled phases targeting qubit `0` of `n + 1`.
* `qftCoreGates n` — the circuit without the final swaps.
* `bitRev n` — reversal of the `n` low bits of a natural number.
* `qftSwapGates n` — the swaps of qubit `q` with qubit `n - 1 - q`, each as
  three `CNOT` gates.
* `qftGates n` — the transform circuit, `qftCoreGates n` followed by
  `qftSwapGates n`. Every angle is a rational multiple of `π` (`Gate.RzQ`).

## Main results

* `embedGate1_succ`, `embedGate2_succ`, `embedGate1_zero` — gate embeddings at
  width `n + 1` as blocks.
* `cphaseGates_matrix` — the controlled-phase gate list is the diagonal
  matrix `exp (i θ x_c x_t)`.
* `qftCoreGates_matrix_apply` — the entry of the swap-free circuit at row `y`
  and column `x` is `qftRoot n ^ (x * bitRev n y) / qftNorm n`.
* `qftCoreGates_matrix` — the swap-free circuit is `qftMatrix n` with its rows
  permuted by bit reversal.
* `unitaryDenote_qftCoreGates` — the channel form of that statement.
* `qftSwapGates_matrix_apply` — the swaps are the permutation matrix of bit
  reversal.
* `qftGates_matrix` — the matrix of `qftGates n` is `qftMatrix n`.
* `unitaryDenote_qftGates` — `qftGates n` denotes the channel of
  `qftUnitary n`.

## References

* Nielsen, Chuang — Quantum Computation and Quantum Information, §5.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix Kronecker
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.Optimization.PhasePolySemantics
open CatCrypt.Quantum.Optimization
open CatCrypt.Quantum.OpenQASMImport (cphaseGates)
open CatCrypt.Quantum.Optimization.RoutingPerm
open CatCrypt.Quantum.Optimization.SwapConj
open CatCrypt.Quantum.Optimization.HardwareRouting (swapGate)

noncomputable section

namespace CatCrypt.Quantum.QFT

variable {n : ℕ}

/-! ## The matrix of a gate list -/

/-- The matrix a gate list realises; the head gate is applied first. -/
def listMatrix (l : List (Gate n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (RoutingPerm.circuitUnitary (Circuit.ofList l)).val

theorem listMatrix_nil : listMatrix ([] : List (Gate n)) = 1 := rfl

theorem listMatrix_cons (g : Gate n) (l : List (Gate n)) :
    listMatrix (g :: l) = listMatrix l * gateEmbedding g := rfl

theorem listMatrix_append (l₁ l₂ : List (Gate n)) :
    listMatrix (l₁ ++ l₂) = listMatrix l₂ * listMatrix l₁ := by
  rw [listMatrix, circuitUnitary_ofList_append]
  rfl

theorem unitaryDenote_ofList (l : List (Gate n)) :
    unitaryDenote (Circuit.ofList l)
      = unitaryChannel (RoutingPerm.circuitUnitary (Circuit.ofList l)) :=
  RoutingPerm.unitaryDenote_eq_channel _

/-! ## Splitting off the first qubit -/

/-- A basis index of `n + 1` qubits as the bit of qubit `0` and the index of
    the remaining `n` qubits. -/
def split (n : ℕ) : Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ' 2 n).symm)

theorem split_val (a : Fin 2) (b : Fin (2 ^ n)) :
    (split n (a, b)).val = 2 ^ n * a.val + b.val := by
  simp [split, add_comm]

theorem testBit_split (a : Fin 2) (b : Fin (2 ^ n)) (p : ℕ) :
    (split n (a, b)).val.testBit p
      = if p < n then b.val.testBit p else a.val.testBit (p - n) := by
  rw [split_val, Nat.testBit_two_pow_mul_add _ b.isLt]

theorem split_div (a : Fin 2) (b : Fin (2 ^ n)) : (split n (a, b)).val / 2 ^ n = a.val := by
  rw [split_val, Nat.mul_add_div (Nat.two_pow_pos n), Nat.div_eq_of_lt b.isLt, add_zero]

theorem split_mod (a : Fin 2) (b : Fin (2 ^ n)) : (split n (a, b)).val % 2 ^ n = b.val := by
  rw [split_val, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]

private theorem fin2_eq_of_testBit {a a' : Fin 2} (h : a.val.testBit 0 = a'.val.testBit 0) :
    a = a' := by
  apply Fin.ext
  have ha := a.isLt
  have ha' := a'.isLt
  rw [Nat.testBit_zero, Nat.testBit_zero, decide_eq_decide] at h
  omega

private theorem testBit_fin2_pos (a : Fin 2) {q : ℕ} (hq : 0 < q) : a.val.testBit q = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt (by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq))

private theorem testBit_index_ge (b : Fin (2 ^ n)) {p : ℕ} (hp : n ≤ p) :
    b.val.testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by norm_num) hp))

theorem pos_succ (i : Fin n) : pos (n + 1) i.succ = pos n i := by
  simp only [pos, Fin.val_succ]
  omega

theorem pos_zero : pos (n + 1) 0 = n := by
  simp [pos]

theorem gbit_succ_split (i : Fin n) (a : Fin 2) (b : Fin (2 ^ n)) :
    gbit (n + 1) i.succ (split n (a, b)).val = gbit n i b.val := by
  apply Fin.ext
  rw [gbit_eq_testBit, gbit_eq_testBit, testBit_split, pos_succ, ite_eq_left (pos_lt i)]

theorem gbit_zero_split (a : Fin 2) (b : Fin (2 ^ n)) :
    gbit (n + 1) 0 (split n (a, b)).val = a := by
  apply Fin.ext
  rw [gbit_val, pos_zero, split_div, Nat.mod_eq_of_lt a.isLt]

theorem match_succ_split (i : Fin n) (a a' : Fin 2) (b b' : Fin (2 ^ n)) :
    Match (n + 1) i.succ (split n (a, b)).val (split n (a', b')).val
      ↔ a = a' ∧ Match n i b.val b'.val := by
  constructor
  · intro h
    refine ⟨fin2_eq_of_testBit ?_, fun p hp => ?_⟩
    · have hn := h n (by rw [pos_succ]; exact (pos_lt i).ne')
      simpa only [testBit_split, lt_irrefl, ite_false, Nat.sub_self] using hn
    · by_cases hpn : p < n
      · have hh := h p (by rwa [pos_succ])
        rwa [testBit_split, testBit_split, ite_eq_left hpn, ite_eq_left hpn] at hh
      · rw [testBit_index_ge b (not_lt.mp hpn), testBit_index_ge b' (not_lt.mp hpn)]
  · rintro ⟨rfl, h⟩ p hp
    rw [testBit_split, testBit_split]
    split_ifs
    · exact h p (by rwa [pos_succ] at hp)
    · rfl

theorem match2_succ_split (i j : Fin n) (a a' : Fin 2) (b b' : Fin (2 ^ n)) :
    Match2 (n + 1) i.succ j.succ (split n (a, b)).val (split n (a', b')).val
      ↔ a = a' ∧ Match2 n i j b.val b'.val := by
  constructor
  · intro h
    refine ⟨fin2_eq_of_testBit ?_, fun p hp hp' => ?_⟩
    · have hn := h n (by rw [pos_succ]; exact (pos_lt i).ne')
        (by rw [pos_succ]; exact (pos_lt j).ne')
      simpa only [testBit_split, lt_irrefl, ite_false, Nat.sub_self] using hn
    · by_cases hpn : p < n
      · have hh := h p (by rwa [pos_succ]) (by rwa [pos_succ])
        rwa [testBit_split, testBit_split, ite_eq_left hpn, ite_eq_left hpn] at hh
      · rw [testBit_index_ge b (not_lt.mp hpn), testBit_index_ge b' (not_lt.mp hpn)]
  · rintro ⟨rfl, h⟩ p hp hp'
    rw [testBit_split, testBit_split]
    split_ifs
    · exact h p (by rwa [pos_succ] at hp) (by rwa [pos_succ] at hp')
    · rfl

theorem match_zero_split (a a' : Fin 2) (b b' : Fin (2 ^ n)) :
    Match (n + 1) 0 (split n (a, b)).val (split n (a', b')).val ↔ b = b' := by
  constructor
  · intro h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hpn : p < n
    · have hh := h p (by rw [pos_zero]; exact hpn.ne)
      rwa [testBit_split, testBit_split, ite_eq_left hpn, ite_eq_left hpn] at hh
    · rw [testBit_index_ge b (not_lt.mp hpn), testBit_index_ge b' (not_lt.mp hpn)]
  · rintro rfl p hp
    rw [pos_zero] at hp
    rw [testBit_split, testBit_split]
    split_ifs with hlt
    · rfl
    · rw [testBit_fin2_pos a (by omega), testBit_fin2_pos a' (by omega)]

/-! ## Block matrices -/

/-- The matrix `A ⊗ M` on `n + 1` qubits: `A` on qubit `0` and `M` on the
    remaining `n` qubits. -/
def blk (A : Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ :=
  Matrix.reindex (split n) (split n) (A ⊗ₖ M)

theorem blk_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (a a' : Fin 2) (b b' : Fin (2 ^ n)) :
    blk A M (split n (a, b)) (split n (a', b')) = A a a' * M b b' := by
  simp [blk]

theorem blk_mul (A A' : Matrix (Fin 2) (Fin 2) ℂ)
    (M M' : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    blk A M * blk A' M' = blk (A * A') (M * M') := by
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    = 1 := by
  simp only [blk, Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

/-- Two matrices on `n + 1` qubits are equal when they agree at all split
    indices. -/
theorem ext_split {M N : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ}
    (h : ∀ a b a' b', M (split n (a, b)) (split n (a', b')) = N (split n (a, b)) (split n (a', b'))) :
    M = N := by
  ext r c
  obtain ⟨⟨a, b⟩, rfl⟩ := (split n).surjective r
  obtain ⟨⟨a', b'⟩, rfl⟩ := (split n).surjective c
  exact h a b a' b'

/-- A one-qubit gate on a later qubit is a block with the identity on qubit
    `0`. -/
theorem embedGate1_succ (i : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 (n + 1) i.succ G = blk 1 (embedGate1 n i G) := by
  refine ext_split fun a b a' b' => ?_
  rw [blk_apply, embedGate1_apply, embedGate1_apply, gbit_succ_split, gbit_succ_split,
    Matrix.one_apply]
  by_cases haa : a = a'
  · by_cases hM : Match n i b.val b'.val
    · rw [ite_eq_left ((match_succ_split i a a' b b').mpr ⟨haa, hM⟩), ite_eq_left haa, ite_eq_left hM, one_mul]
    · rw [ite_eq_right (fun h => hM ((match_succ_split i a a' b b').mp h).2), ite_eq_right hM, mul_zero]
  · rw [ite_eq_right (fun h => haa ((match_succ_split i a a' b b').mp h).1), ite_eq_right haa, zero_mul]

theorem idx4_succ_split (i j : Fin n) (a : Fin 2) (b : Fin (2 ^ n)) :
    idx4 (n + 1) i.succ j.succ (split n (a, b)).val = idx4 n i j b.val := by
  simp only [idx4, gbit_succ_split]

/-- A two-qubit gate on later qubits is a block with the identity on qubit
    `0`. -/
theorem embedGate2_succ {i j : Fin n} (hij : i ≠ j) (G : Matrix (Fin 4) (Fin 4) ℂ) :
    embedGate2 (n + 1) i.succ j.succ G (fun h => hij (Fin.succ_injective _ h))
      = blk 1 (embedGate2 n i j G hij) := by
  refine ext_split fun a b a' b' => ?_
  rw [blk_apply, embedGate2_apply, embedGate2_apply, idx4_succ_split, idx4_succ_split,
    Matrix.one_apply]
  by_cases haa : a = a'
  · by_cases hM : Match2 n i j b.val b'.val
    · rw [ite_eq_left ((match2_succ_split i j a a' b b').mpr ⟨haa, hM⟩), ite_eq_left haa, ite_eq_left hM,
        one_mul]
    · rw [ite_eq_right (fun h => hM ((match2_succ_split i j a a' b b').mp h).2), ite_eq_right hM, mul_zero]
  · rw [ite_eq_right (fun h => haa ((match2_succ_split i j a a' b b').mp h).1), ite_eq_right haa, zero_mul]

/-- A one-qubit gate on qubit `0` is a block with the identity on the
    remaining qubits. -/
theorem embedGate1_zero (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 (n + 1) 0 G = blk G 1 := by
  refine ext_split fun a b a' b' => ?_
  rw [blk_apply, embedGate1_apply, gbit_zero_split, gbit_zero_split, Matrix.one_apply]
  by_cases hbb : b = b'
  · rw [ite_eq_left ((match_zero_split a a' b b').mpr hbb), ite_eq_left hbb, mul_one]
  · rw [ite_eq_right (fun h => hbb ((match_zero_split a a' b b').mp h)), ite_eq_right hbb, mul_zero]

/-! ## Relabelling a gate list to the later qubits -/

/-- A gate on `n` qubits acting on the last `n` qubits of `n + 1`. -/
def succGate : Gate n → Gate (n + 1)
  | .H i      => .H i.succ
  | .X i      => .X i.succ
  | .Y i      => .Y i.succ
  | .Z i      => .Z i.succ
  | .T i      => .T i.succ
  | .Tdg i    => .Tdg i.succ
  | .S i      => .S i.succ
  | .CNOT c t => .CNOT c.succ t.succ
  | .CZ c t   => .CZ c.succ t.succ
  | .Rz i θ   => .Rz i.succ θ
  | .RzQ i q  => .RzQ i.succ q

theorem gateEmbedding_succGate (g : Gate n) :
    gateEmbedding (succGate g) = blk 1 (gateEmbedding g) := by
  cases g with
  | CNOT c t =>
    by_cases h : c = t
    · simp only [succGate, gateEmbedding, h, dite_eq_left, blk_one]
    · have h' : c.succ ≠ t.succ := fun e => h (Fin.succ_injective _ e)
      simp only [succGate, gateEmbedding, dite_eq_right h, dite_eq_right h']
      exact embedGate2_succ h _
  | CZ c t =>
    by_cases h : c = t
    · simp only [succGate, gateEmbedding, h, dite_eq_left, blk_one]
    · have h' : c.succ ≠ t.succ := fun e => h (Fin.succ_injective _ e)
      simp only [succGate, gateEmbedding, dite_eq_right h, dite_eq_right h']
      exact embedGate2_succ h _
  | _ => simp only [succGate, gateEmbedding, embedGate1_succ]

theorem listMatrix_map_succGate (l : List (Gate n)) :
    listMatrix (l.map succGate) = blk 1 (listMatrix l) := by
  induction l with
  | nil => rw [List.map_nil, listMatrix_nil, listMatrix_nil, blk_one]
  | cons g l ih =>
    rw [List.map_cons, listMatrix_cons, listMatrix_cons, ih, gateEmbedding_succGate, blk_mul,
      one_mul]

/-! ## The controlled phase -/

private theorem phase_key (θ : ℂ) (u w : Fin 2) :
    Complex.I * θ * (((w.val : ZMod 2)).val : ℂ) + Complex.I * θ * (((u.val : ZMod 2)).val : ℂ)
        + Complex.I * (-θ) * ((((u.val : ZMod 2) + (w.val : ZMod 2))).val : ℂ)
      = Complex.I * (2 * θ) * (u.val : ℂ) * (w.val : ℂ) := by
  fin_cases u <;> fin_cases w <;> simp [ZMod.val_one, show ((1 : ZMod 2) + 1) = 0 from by decide]
  ring

private theorem parityForm_pair {c t : Fin n} (hct : c ≠ t) (x : ℕ) :
    parityForm (cnotParity (singletonParity t) c t) x = bitZ n c x + bitZ n t x := by
  have hp : ∀ i : Fin n, (if cnotParity (singletonParity t) c t i then bitZ n i x else 0)
      = (if i = c then bitZ n i x else 0) + (if i = t then bitZ n i x else 0) := by
    intro i
    by_cases hic : i = c
    · subst hic
      simp [cnotParity, singletonParity, hct]
    · by_cases hit : i = t
      · subst hit
        simp [cnotParity, singletonParity, hic]
      · simp [cnotParity, singletonParity, hic, hit]
  simp only [parityForm, hp, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The controlled-phase gate list by `a · π` is the diagonal matrix with the
    phase `exp (i a π)` at the indices where both qubits read `1`. -/
theorem cphaseGates_matrix {c t : Fin n} (hct : c ≠ t) (a : QasmAngle) :
    listMatrix (cphaseGates c t a) = Matrix.diagonal fun x : Fin (2 ^ n) =>
      Complex.exp (Complex.I * (2 * ((QasmAngle.toReal (a / 2) : ℝ) : ℂ))
        * ((gbit n c x.val).val : ℂ) * ((gbit n t x.val).val : ℂ)) := by
  have hC : gateEmbedding (Gate.CNOT c t : Gate n) = embedGate2 n c t cnot hct := by
    simp only [gateEmbedding, dite_eq_right hct]
  have hneg : PiLin.toReal (-(PiLin.ofPi a / 2)) = -QasmAngle.toReal (a / 2) := by
    simp [QasmAngle.toReal]
  have hpos : PiLin.toReal (PiLin.ofPi a / 2) = QasmAngle.toReal (a / 2) := by
    simp [QasmAngle.toReal]
  simp only [cphaseGates, listMatrix_cons, listMatrix_nil, one_mul, hC]
  show embedGate1 n t (rzGate _) * embedGate1 n c (rzGate _) * embedGate2 n c t cnot hct
      * embedGate1 n t (rzGate _) * embedGate2 n c t cnot hct = _
  rw [rz_embed_eq_phaseDiag, rz_embed_eq_phaseDiag, rz_embed_eq_phaseDiag, mul_assoc,
    mul_assoc, ← mul_assoc (embedGate2 n c t cnot hct), cnot_conj_phaseDiag hct, hneg, hpos]
  simp only [phaseDiag, Matrix.diagonal_mul_diagonal, parityForm_singletonParity,
    parityForm_pair hct, ← Complex.exp_add]
  congr 1
  funext x
  congr 1
  have key := phase_key ((QasmAngle.toReal (a / 2) : ℝ) : ℂ) (gbit n c x.val) (gbit n t x.val)
  simpa only [bitZ, Complex.ofReal_neg] using key

/-! ## The phases onto the first qubit -/

/-- The controlled phases targeting qubit `0` of `n + 1` whose controls read
    the bit positions below `k`: the control at position `p` carries the angle
    `π · 2 ^ p / 2 ^ n`. -/
def qftPhasesBelow (n k : ℕ) : List (Gate (n + 1)) :=
  (List.range k).flatMap fun p =>
    if h : p < n then cphaseGates (⟨n - p, by omega⟩ : Fin (n + 1)) 0 ((2 ^ p / 2 ^ n : ℚ))
    else []

/-- The controlled phases of the first stage of the transform on `n + 1`
    qubits. -/
def qftPhaseGates (n : ℕ) : List (Gate (n + 1)) := qftPhasesBelow n n

/-- The diagonal of the phases whose controls read the positions below `k`. -/
def qftPhaseDiag (n k : ℕ) : Fin (2 ^ (n + 1)) → ℂ := fun x =>
  qftRoot (n + 1) ^ ((gbit (n + 1) 0 x.val).val * (x.val % 2 ^ k))

private theorem qftRoot_pow_eq_exp (n m : ℕ) :
    qftRoot n ^ m = Complex.exp (Complex.I * (2 * Real.pi * m / 2 ^ n)) := by
  rw [qftRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem qftPhasesBelow_matrix (n : ℕ) :
    ∀ k, k ≤ n → listMatrix (qftPhasesBelow n k) = Matrix.diagonal (qftPhaseDiag n k) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [qftPhasesBelow, List.range_zero, List.flatMap_nil, listMatrix_nil,
      ← Matrix.diagonal_one]
    congr 1
    funext x
    simp [qftPhaseDiag, Nat.mod_one]
  | succ k ih =>
    intro hk
    have hkn : k < n := hk
    have hne : (⟨n - k, by omega⟩ : Fin (n + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      omega
    have hpos : pos (n + 1) (⟨n - k, by omega⟩ : Fin (n + 1)) = k := by
      simp only [pos]
      omega
    rw [qftPhasesBelow, List.range_succ, List.flatMap_append, List.flatMap_singleton, dite_eq_left hkn,
      listMatrix_append, cphaseGates_matrix hne]
    change _ * listMatrix (qftPhasesBelow n k) = _
    rw [ih (Nat.le_of_lt hkn), Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    simp only [qftPhaseDiag, qftRoot_pow_eq_exp, ← Complex.exp_add, gbit_val, hpos, pos_zero,
      QasmAngle.toReal, Nat.mod_pow_succ]
    congr 1
    push_cast
    field_simp
    ring

/-! ## The circuit without the final swaps -/

/-- The transform circuit without the final swaps: on qubit `0` a Hadamard
    and the phases controlled by the later qubits, then the circuit for `n`
    qubits on the later qubits. -/
def qftCoreGates : (n : ℕ) → List (Gate n)
  | 0 => []
  | n + 1 => Gate.H 0 :: (qftPhaseGates n ++ (qftCoreGates n).map succGate)

/-- Reversal of the `n` low bits of a natural number. -/
def bitRev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, y => y / 2 ^ n + 2 * bitRev n (y % 2 ^ n)

theorem bitRev_lt (n y : ℕ) (hy : y < 2 ^ n) : bitRev n y < 2 ^ n := by
  induction n generalizing y with
  | zero => simp [bitRev]
  | succ n ih =>
    have h1 : y / 2 ^ n < 2 := Nat.div_lt_of_lt_mul (by rwa [pow_succ] at hy)
    have h2 := ih (y % 2 ^ n) (Nat.mod_lt _ (Nat.two_pow_pos n))
    simp only [bitRev, pow_succ]
    omega

private theorem hadamard_apply (a a' : Fin 2) :
    hadamard a a' = (-1 : ℂ) ^ (a.val * a'.val) / ((Real.sqrt 2 : ℝ) : ℂ) := by
  fin_cases a <;> fin_cases a' <;> simp [hadamard, neg_div]

private theorem qftNorm_succ (n : ℕ) :
    qftNorm (n + 1) = qftNorm n * ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [qftNorm, qftNorm, ← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  congr 2
  push_cast
  ring

theorem qftCoreGates_step (n : ℕ) :
    listMatrix (qftCoreGates (n + 1))
      = blk 1 (listMatrix (qftCoreGates n)) * Matrix.diagonal (qftPhaseDiag n n)
          * blk hadamard 1 := by
  rw [qftCoreGates, listMatrix_cons, listMatrix_append, listMatrix_map_succGate, qftPhaseGates,
    qftPhasesBelow_matrix n n le_rfl]
  show _ * embedGate1 (n + 1) 0 hadamard = _
  rw [embedGate1_zero]

/-- The entry of the swap-free circuit at row `y` and column `x`. -/
theorem qftCoreGates_matrix_apply :
    ∀ (n : ℕ) (y x : Fin (2 ^ n)),
      listMatrix (qftCoreGates n) y x = qftRoot n ^ (x.val * bitRev n y.val) / qftNorm n := by
  intro n
  induction n with
  | zero =>
    intro y x
    have hyx : y = x := Fin.ext (by
      have hy := y.isLt
      have hx := x.isLt
      simp only [pow_zero] at hy hx
      omega)
    simp [qftCoreGates, listMatrix_nil, hyx, bitRev, qftNorm]
  | succ n ih =>
    intro y x
    obtain ⟨⟨a, b⟩, rfl⟩ := (split n).surjective y
    obtain ⟨⟨a', b'⟩, rfl⟩ := (split n).surjective x
    rw [qftCoreGates_step, Matrix.mul_assoc, Matrix.mul_apply,
      ← (split n).sum_comp, Fintype.sum_prod_type]
    simp only [blk_apply, Matrix.one_apply, Matrix.diagonal_mul, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [ih, hadamard_apply, qftPhaseDiag, gbit_zero_split, split_mod, bitRev, split_div,
      split_mod, split_val, qftNorm_succ]
    have h1 : qftRoot (n + 1) ^ ((2 ^ n * a'.val + b'.val) * (a.val + 2 * bitRev n b.val))
        = qftRoot (n + 1) ^ (a.val * b'.val) * qftRoot n ^ (b'.val * bitRev n b.val)
            * (-1 : ℂ) ^ (a.val * a'.val) := by
      rw [← qftRoot_succ_sq n, ← qftRoot_succ_pow_two_pow n, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add]
      have h2 : (2 ^ n * a'.val + b'.val) * (a.val + 2 * bitRev n b.val)
          = a.val * b'.val + 2 * (b'.val * bitRev n b.val) + 2 ^ n * (a.val * a'.val)
            + 2 ^ (n + 1) * (a'.val * bitRev n b.val) := by ring
      rw [h2, pow_add _ _ (2 ^ (n + 1) * _), pow_mul _ (2 ^ (n + 1)), qftRoot_pow_two_pow,
        one_pow, mul_one]
    rw [h1]
    have hn := qftNorm_ne_zero n
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp

/-- Bit reversal on basis indices. -/
def bitRevFin (n : ℕ) (y : Fin (2 ^ n)) : Fin (2 ^ n) := ⟨bitRev n y.val, bitRev_lt n y.val y.isLt⟩

/-- The swap-free circuit is the transform with its rows permuted by bit
    reversal. -/
theorem qftCoreGates_matrix (n : ℕ) :
    listMatrix (qftCoreGates n) = (qftMatrix n).submatrix (bitRevFin n) id := by
  ext y x
  rw [qftCoreGates_matrix_apply]
  rfl

theorem qftMatrix_submatrix_bitRev_mem (n : ℕ) :
    (qftMatrix n).submatrix (bitRevFin n) id ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [← qftCoreGates_matrix]
  exact (RoutingPerm.circuitUnitary (Circuit.ofList (qftCoreGates n))).property

/-- The swap-free circuit denotes the channel of the transform with its rows
    permuted by bit reversal. -/
theorem unitaryDenote_qftCoreGates (n : ℕ) :
    unitaryDenote (Circuit.ofList (qftCoreGates n))
      = unitaryChannel ⟨(qftMatrix n).submatrix (bitRevFin n) id,
          qftMatrix_submatrix_bitRev_mem n⟩ := by
  rw [unitaryDenote_ofList]
  congr 1
  exact Subtype.ext (qftCoreGates_matrix n)

/-! ## Bit reversal on indices -/

theorem testBit_bitRev :
    ∀ (n y p : ℕ), y < 2 ^ n → p < n → (bitRev n y).testBit p = y.testBit (n - 1 - p) := by
  intro n
  induction n with
  | zero => intro y p _ hp; exact absurd hp (Nat.not_lt_zero p)
  | succ n ih =>
    intro y p hy hp
    have h1 : y / 2 ^ n < 2 := Nat.div_lt_of_lt_mul (by rwa [pow_succ] at hy)
    cases p with
    | zero =>
      rw [bitRev, Nat.testBit_zero, Nat.testBit_eq_decide_div_mod_eq]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.add_mul_mod_self_left]
    | succ p =>
      have hp' : p < n := Nat.lt_of_succ_lt_succ hp
      have hhalf : ∀ a B : ℕ, a < 2 → (a + 2 * B) / 2 = B := by
        intro a B ha
        omega
      have hdiv : (y / 2 ^ n + 2 * bitRev n (y % 2 ^ n)) / 2 = bitRev n (y % 2 ^ n) :=
        hhalf _ _ h1
      rw [bitRev, Nat.testBit_succ, hdiv, ih _ p (Nat.mod_lt _ (Nat.two_pow_pos n)) hp',
        Nat.testBit_mod_two_pow, decide_eq_true (by omega : n - 1 - p < n), Bool.true_and]
      congr 1
      omega

theorem bitRevFin_bitRevFin (n : ℕ) (y : Fin (2 ^ n)) : bitRevFin n (bitRevFin n y) = y := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < n
  · show (bitRev n (bitRev n y.val)).testBit p = _
    rw [testBit_bitRev n _ p (bitRev_lt n _ y.isLt) hp,
      testBit_bitRev n _ _ y.isLt (by omega)]
    congr 1
    omega
  · rw [testBit_index_ge _ (not_lt.mp hp), testBit_index_ge _ (not_lt.mp hp)]

theorem eq_bitRevFin_iff (n : ℕ) (c r : Fin (2 ^ n)) :
    c = bitRevFin n r ↔ ∀ p, p < n → c.val.testBit p = r.val.testBit (n - 1 - p) := by
  constructor
  · rintro rfl p hp
    exact testBit_bitRev n _ p r.isLt hp
  · intro h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p < n
    · rw [h p hp]
      exact (testBit_bitRev n _ p r.isLt hp).symm
    · rw [testBit_index_ge _ (not_lt.mp hp), testBit_index_ge _ (not_lt.mp hp)]

/-! ## The final swaps -/

/-- The swap of two qubits as three `CNOT` gates. -/
def swapGates (a b : Fin n) : List (Gate n) :=
  [Gate.CNOT a b, Gate.CNOT b a, Gate.CNOT a b]

theorem swapGates_matrix (a b : Fin n) :
    listMatrix (swapGates a b) = (qubitPermUnitary (swapBitPerm a b)).val := by
  rw [← swapGate_circuitUnitary]
  simp only [listMatrix, swapGates, Circuit.ofList, swapGate, circuitUnitary, Circuit.single,
    one_mul, mul_assoc]

/-- A basis permutation on the left permutes the rows. -/
theorem qubitPermUnitary_mul_apply (σ : Equiv.Perm (Fin n))
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (r c : Fin (2 ^ n)) :
    ((qubitPermUnitary σ).val * M) r c = M (qubitBitPerm σ r) c := by
  rw [Matrix.mul_apply]
  simp only [qubitPermUnitary_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The swaps of qubit `q` with qubit `n - 1 - q` for `q < k`. -/
def qftSwapsBelow (n k : ℕ) : List (Gate n) :=
  (List.range k).flatMap fun q =>
    if h : q < n then swapGates (⟨q, h⟩ : Fin n) ⟨n - 1 - q, by omega⟩ else []

/-- The bit-reversal swaps: qubit `q` with qubit `n - 1 - q` for `q < n / 2`. -/
def qftSwapGates (n : ℕ) : List (Gate n) := qftSwapsBelow n (n / 2)

/-- The position map of the first `k` swaps: the `k` outermost positions on
    each side are reversed. -/
def revBelow (n k p : ℕ) : ℕ := if p < k ∨ n - k ≤ p then n - 1 - p else p

theorem qftSwapsBelow_matrix_apply (n : ℕ) :
    ∀ k, 2 * k ≤ n → ∀ r c : Fin (2 ^ n),
      listMatrix (qftSwapsBelow n k) r c
        = if ∀ p, p < n → c.val.testBit p = r.val.testBit (revBelow n k p) then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro _ r c
    rw [qftSwapsBelow, List.range_zero, List.flatMap_nil, listMatrix_nil, Matrix.one_apply]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro rfl p hp
      simp only [revBelow]
      rw [ite_eq_right (by omega)]
    · intro h
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro p
      by_cases hp : p < n
      · have hh := h p hp
        simp only [revBelow] at hh
        rw [ite_eq_right (by omega)] at hh
        exact hh.symm
      · rw [testBit_index_ge _ (not_lt.mp hp), testBit_index_ge _ (not_lt.mp hp)]
  | succ k ih =>
    intro hk r c
    have hkn : k < n := by omega
    rw [qftSwapsBelow, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      dite_eq_left hkn, listMatrix_append, swapGates_matrix, qubitPermUnitary_mul_apply]
    change listMatrix (qftSwapsBelow n k) _ _ = _
    rw [ih (by omega)]
    refine if_congr (forall_congr' fun p => forall_congr' fun hp => ?_) rfl rfl
    have hlt : revBelow n k p < n := by
      simp only [revBelow]
      split_ifs <;> omega
    have hbit : (qubitBitPerm (swapBitPerm (⟨k, hkn⟩ : Fin n) ⟨n - 1 - k, by omega⟩) r).val.testBit
          (revBelow n k p)
        = r.val.testBit ((swapBitPerm (⟨k, hkn⟩ : Fin n) ⟨n - 1 - k, by omega⟩).symm
            ⟨revBelow n k p, hlt⟩).val :=
      qubitBitPerm_testBit _ r ⟨revBelow n k p, hlt⟩
    have hidx : ∀ q (hq : q < n), q = revBelow n k p →
        ((swapBitPerm (⟨k, hkn⟩ : Fin n) ⟨n - 1 - k, by omega⟩).symm ⟨q, hq⟩).val
          = revBelow n (k + 1) p := by
      intro q hq hqe
      rw [swapBitPerm_symm, swapBitPerm, Equiv.swap_apply_def]
      simp only [posIdx, pos, Fin.mk.injEq, revBelow] at hqe ⊢
      simp only [apply_ite Fin.val]
      split_ifs at hqe ⊢ <;> omega
    rw [hbit, hidx _ hlt rfl]

theorem qftSwapGates_matrix_apply (n : ℕ) (r c : Fin (2 ^ n)) :
    listMatrix (qftSwapGates n) r c = if c = bitRevFin n r then 1 else 0 := by
  rw [qftSwapGates, qftSwapsBelow_matrix_apply n (n / 2) (by omega)]
  refine if_congr ?_ rfl rfl
  rw [eq_bitRevFin_iff]
  refine forall_congr' fun p => forall_congr' fun hp => ?_
  have hrev : revBelow n (n / 2) p = n - 1 - p := by
    simp only [revBelow]
    split_ifs <;> omega
  rw [hrev]

/-! ## The transform circuit -/

/-- The quantum Fourier transform circuit on `n` qubits: for each qubit in
    turn a Hadamard and the phases controlled by the later qubits, then the
    bit-reversal swaps. All angles are rational multiples of `π`. -/
def qftGates (n : ℕ) : List (Gate n) := qftCoreGates n ++ qftSwapGates n

/-- The matrix of the transform circuit is `qftMatrix n`. -/
theorem qftGates_matrix (n : ℕ) : listMatrix (qftGates n) = qftMatrix n := by
  ext k x
  rw [qftGates, listMatrix_append, Matrix.mul_apply]
  simp only [qftSwapGates_matrix_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [qftCoreGates_matrix_apply, qftMatrix_apply]
  have h := congrArg Fin.val (bitRevFin_bitRevFin n k)
  simp only [bitRevFin] at h
  rw [show (bitRevFin n k).val = bitRev n k.val from rfl, h]

/-- The transform circuit denotes the channel of the quantum Fourier
    transform. -/
theorem unitaryDenote_qftGates (n : ℕ) :
    unitaryDenote (Circuit.ofList (qftGates n)) = unitaryChannel (qftUnitary n) := by
  rw [unitaryDenote_ofList]
  congr 1
  exact Subtype.ext (qftGates_matrix n)

end CatCrypt.Quantum.QFT
