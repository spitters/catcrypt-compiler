/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.ControlledGates

/-!
# The Gottesman–Knill theorem in the Heisenberg picture

A signed Pauli string on `n` qubits is `iᵏ X(x) Z(z)` with `k : ZMod 4` and bit vectors
`x z : Fin n → ZMod 2`, where `X(x) = ∏ᵢ X_i^{x i}` and `Z(z) = ∏ᵢ Z_i^{z i}`. Conjugating a
Pauli string by a Clifford gate gives a Pauli string again, and the new string is computed
from the old one by changing at most two bits of `x` and `z` and the phase:

* `H_q`: swap `x q` and `z q`, add `2 (x q)(z q)` to the phase (`H X H = Z`, `H Z H = X`,
  `Z X = -X Z`);
* `S_q`: add `x q` to `z q` and to the phase (`S X S† = i X Z`, `S Z S† = Z`);
* `CNOT(c, t)`: add `x c` to `x t` and `z t` to `z c` (`X_c ↦ X_c X_t`, `Z_t ↦ Z_c Z_t`,
  `X_t` and `Z_c` fixed).

So for a circuit `C` of `H`, `S` and `CNOT` gates, `U_C P U_C†` is the Pauli string obtained by
running these updates gate by gate (Gottesman, *The Heisenberg representation of quantum
computers*, 1998). Each update writes the phase and at most two bits, on the qubits of the
gate, so on a tableau of `m` Pauli strings (for a stabilizer state, the `n` stabilizer
generators) a circuit costs at most `3 m |C|` entry updates.

## Main definitions

* `PauliStr n` — a signed Pauli string, `PauliStr.mat` its matrix.
* `IsHSC g` — `g` is an `H`, `S` or `CNOT` gate (on two distinct qubits).
* `PauliStr.conjGate g`, `PauliStr.conjCircuit C` — the tableau updates.
* `updCost g`, `tableauCost m C` — the number of entries an update writes.

## Main results

* `conj_gate` — `U_g P U_g† = (P.conjGate g).mat` for every `H`, `S`, `CNOT` gate `g`.
* `gottesman_knill` — `U_C P U_C† = (P.conjCircuit C).mat` for every circuit `C` of such gates.
* `conjGate_eq_of_not_mem` — an update changes only the bits on the qubits of its gate.
* `tableauCost_le` — the update of a tableau of `m` strings writes at most `3 m |C|` entries.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.Optimization.DisjointCommute (embedGate1_disjoint_comm)
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons)

namespace CatCrypt.Quantum.GottesmanKnill

/-! ## Products over a commuting family of involutions -/

section Family

variable {R : Type*} [Monoid R] {n : ℕ}

/-- `∏ᵢ E_i ^ (x i)` over the qubits in the order of `List.finRange n`. -/
def pw (E : Fin n → R) (x : Fin n → ZMod 2) : R :=
  ((List.finRange n).map fun i => E i ^ (x i).val).prod

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  exacts [Or.inl rfl, Or.inr rfl]

theorem pow_val_add {e : R} (he : e * e = 1) (a b : ZMod 2) :
    e ^ (a + b).val = e ^ a.val * e ^ b.val := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 from rfl, show ZMod.val (1 : ZMod 2) = 1 from rfl, he]

variable {E : Fin n → R}

theorem prod_map_add (hc : ∀ i j, Commute (E i) (E j)) (hs : ∀ i, E i * E i = 1)
    (x y : Fin n → ZMod 2) : ∀ l : List (Fin n),
    (l.map fun i => E i ^ ((x + y) i).val).prod
      = (l.map fun i => E i ^ (x i).val).prod * (l.map fun i => E i ^ (y i).val).prod
  | [] => by simp
  | i :: l => by
    have hcomm : Commute (E i ^ (y i).val) (l.map fun i => E i ^ (x i).val).prod := by
      refine Commute.list_prod_right _ _ fun z hz => ?_
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
      exact (hc i j).pow_pow _ _
    simp only [List.map_cons, List.prod_cons]
    rw [prod_map_add hc hs x y l, Pi.add_apply, pow_val_add (hs i), mul_assoc,
      ← mul_assoc (E i ^ (y i).val), hcomm.eq]
    simp only [mul_assoc]

/-- `X(x + y) = X(x) X(y)`. -/
theorem pw_add (hc : ∀ i j, Commute (E i) (E j)) (hs : ∀ i, E i * E i = 1)
    (x y : Fin n → ZMod 2) : pw E (x + y) = pw E x * pw E y :=
  prod_map_add hc hs x y _

theorem prod_map_single (q : Fin n) (a : ZMod 2) : ∀ l : List (Fin n), l.Nodup →
    (l.map fun i => E i ^ ((Pi.single q a : Fin n → ZMod 2) i).val).prod
      = if q ∈ l then E q ^ a.val else 1
  | [], _ => by simp
  | i :: l, hl => by
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons, prod_map_single q a l hl.2, List.mem_cons]
    by_cases hi : i = q
    · subst hi; simp [hl.1]
    · simp [Ne.symm hi]

/-- `X(e_q a) = X_q ^ a`. -/
theorem pw_single (q : Fin n) (a : ZMod 2) : pw E (Pi.single q a) = E q ^ a.val := by
  rw [pw, prod_map_single q a _ (List.nodup_finRange n)]
  simp

theorem update_eq_add (x : Fin n → ZMod 2) (q : Fin n) (v : ZMod 2) :
    Function.update x q v = Function.update x q 0 + Pi.single q v := by
  funext i
  by_cases hi : i = q
  · subst hi; simp
  · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]

/-- Splitting off qubit `q`: `X(x) = X(x[q ↦ 0]) X_q^{x q}`. -/
theorem pw_split (hc : ∀ i j, Commute (E i) (E j)) (hs : ∀ i, E i * E i = 1)
    (x : Fin n → ZMod 2) (q : Fin n) :
    pw E x = pw E (Function.update x q 0) * E q ^ (x q).val := by
  conv_lhs => rw [← Function.update_eq_self q x, update_eq_add]
  rw [pw_add hc hs, pw_single]

/-- An element commuting with the factors that occur commutes with the product. -/
theorem commute_pw {F : R} (x : Fin n → ZMod 2) (h : ∀ i, x i ≠ 0 → Commute F (E i)) :
    Commute F (pw E x) := by
  refine Commute.list_prod_right _ _ fun z hz => ?_
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  by_cases hi : x i = 0
  · simp [hi]
  · exact (h i hi).pow_right _

end Family

/-! ## Pauli strings -/

variable {n : ℕ}

/-- The single-qubit `X` on qubit `i`. -/
noncomputable abbrev Xq (i : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := embedGate1 n i pauliX

/-- The single-qubit `Z` on qubit `i`. -/
noncomputable abbrev Zq (i : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := embedGate1 n i pauliZ

/-- A signed Pauli string `iᵏ X(x) Z(z)`. -/
structure PauliStr (n : ℕ) where
  /-- The phase exponent `k` of `iᵏ`. -/
  ph : ZMod 4
  /-- The `X` part. -/
  x : Fin n → ZMod 2
  /-- The `Z` part. -/
  z : Fin n → ZMod 2

/-- The matrix `iᵏ X(x) Z(z)` of a signed Pauli string. -/
noncomputable def PauliStr.mat (P : PauliStr n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (Complex.I ^ P.ph.val) • (pw Xq P.x * pw Zq P.z)

/-! ## Single-qubit identities -/

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_mul_pauliX : pauliZ * pauliX = (-1 : ℂ) • (pauliX * pauliZ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem phaseS_pauliX_mul_phaseS_pauliZ : phaseS * pauliX * (phaseS * pauliZ) = Complex.I • (pauliX * pauliZ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, phaseS, Matrix.mul_apply, Fin.sum_univ_two]

theorem phaseS_mul_pauliZ : phaseS * pauliZ = pauliZ * phaseS := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, phaseS, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj0_sub_proj1 : proj0 - proj1 = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1, pauliZ]

theorem pauliX_pauliZ_pauliX : pauliX * pauliZ * pauliX = (-1 : ℂ) • pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Embedded identities -/

theorem commute_embedGate1 {i j : Fin n} {G H : Matrix (Fin 2) (Fin 2) ℂ}
    (h : i ≠ j ∨ G * H = H * G) : Commute (embedGate1 n i G) (embedGate1 n j H) := by
  rcases h with h | h
  · exact embedGate1_disjoint_comm h G H
  · by_cases hij : i = j
    · subst hij
      show embedGate1 n i G * embedGate1 n i H = embedGate1 n i H * embedGate1 n i G
      rw [embedGate1_mul, embedGate1_mul, h]
    · exact embedGate1_disjoint_comm hij G H

theorem commute_Xq (i j : Fin n) : Commute (Xq i) (Xq j) := commute_embedGate1 (Or.inr rfl)

theorem commute_Zq (i j : Fin n) : Commute (Zq i) (Zq j) := commute_embedGate1 (Or.inr rfl)

theorem Xq_mul_self (i : Fin n) : Xq i * Xq i = 1 := by
  rw [embedGate1_mul, pauliX_mul_self, embedGate1_one]

theorem Zq_mul_self (i : Fin n) : Zq i * Zq i = 1 := by
  rw [embedGate1_mul, pauliZ_mul_self, embedGate1_one]

/-- Conjugation by `G` with left inverse `G'`, as a monoid endomorphism. -/
def conjHom (G G' : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (h : G' * G = 1) (h' : G * G' = 1) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ →* Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ where
  toFun A := G * A * G'
  map_one' := by rw [mul_one, h']
  map_mul' A B := by
    simp only [mul_assoc]
    rw [← mul_assoc G' G, h, one_mul]

theorem conjHom_apply {G G' : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (h : G' * G = 1)
    (h' : G * G' = 1) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    conjHom G G' h h' A = G * A * G' := rfl

theorem conj_of_commute {G G' A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (h' : G * G' = 1)
    (hc : Commute G A) : G * A * G' = A := by
  rw [hc.eq, mul_assoc, h', mul_one]

theorem conj_smul (G G' A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (c : ℂ) :
    G * (c • A) * G' = c • (G * A * G') := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Splitting off qubit `q` in the matrix of a Pauli string, `X` part. -/
theorem pwX_split (x : Fin n → ZMod 2) (q : Fin n) :
    pw Xq x = pw Xq (Function.update x q 0) * Xq q ^ (x q).val :=
  pw_split commute_Xq Xq_mul_self x q

theorem pwZ_split (z : Fin n → ZMod 2) (q : Fin n) :
    pw Zq z = pw Zq (Function.update z q 0) * Zq q ^ (z q).val :=
  pw_split commute_Zq Zq_mul_self z q

theorem pwX_update (x : Fin n → ZMod 2) (q : Fin n) (v : ZMod 2) :
    pw Xq (Function.update x q v) = pw Xq (Function.update x q 0) * Xq q ^ v.val := by
  rw [update_eq_add, pw_add commute_Xq Xq_mul_self, pw_single]

theorem pwZ_update (z : Fin n → ZMod 2) (q : Fin n) (v : ZMod 2) :
    pw Zq (Function.update z q v) = pw Zq (Function.update z q 0) * Zq q ^ v.val := by
  rw [update_eq_add, pw_add commute_Zq Zq_mul_self, pw_single]

theorem update_zero_ne {x : Fin n → ZMod 2} {q i : Fin n} (h : Function.update x q 0 i ≠ 0) :
    i ≠ q := by
  rintro rfl; simp at h

theorem I_pow_val_add (u v : ZMod 4) :
    Complex.I ^ (u + v).val = Complex.I ^ u.val * Complex.I ^ v.val := by
  have h : ∀ m : ℕ, Complex.I ^ m = Complex.I ^ (m % 4) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]
  rw [ZMod.val_add, ← h, pow_add]

/-! ## The tableau update -/

/-- The Pauli string `U_g P U_g†` for an `H`, `S` or `CNOT` gate `g`; other gates leave `P`
unchanged (the theorems are stated for `H`, `S` and `CNOT`). -/
def PauliStr.conjGate : Gate n → PauliStr n → PauliStr n
  | .H q, P => ⟨P.ph + 2 * (((P.x q).val * (P.z q).val : ℕ) : ZMod 4),
      Function.update P.x q (P.z q), Function.update P.z q (P.x q)⟩
  | .S q, P => ⟨P.ph + (((P.x q).val : ℕ) : ZMod 4), P.x, P.z + Pi.single q (P.x q)⟩
  | .CNOT c t, P => ⟨P.ph, P.x + Pi.single t (P.x c), P.z + Pi.single c (P.z t)⟩
  | _, P => P

/-! ## Hadamard -/

theorem Hq_mul_self (q : Fin n) : embedGate1 n q hadamard * embedGate1 n q hadamard = 1 :=
  embedGate1_hadamard_mul_self q

theorem conjH_pwX (x : Fin n → ZMod 2) (q : Fin n) :
    embedGate1 n q hadamard * pw Xq x * embedGate1 n q hadamard
      = pw Xq (Function.update x q 0) * Zq q ^ (x q).val := by
  rw [pwX_split x q, ← conjHom_apply (Hq_mul_self q) (Hq_mul_self q), map_mul, map_pow,
    conjHom_apply, conjHom_apply, embedGate1_mul, embedGate1_mul, hadamard_pauliX_hadamard,
    conj_of_commute (Hq_mul_self q) (commute_pw _ fun i hi =>
      commute_embedGate1 (Or.inl (Ne.symm (update_zero_ne hi))))]

theorem conjH_pwZ (z : Fin n → ZMod 2) (q : Fin n) :
    embedGate1 n q hadamard * pw Zq z * embedGate1 n q hadamard
      = pw Zq (Function.update z q 0) * Xq q ^ (z q).val := by
  rw [pwZ_split z q, ← conjHom_apply (Hq_mul_self q) (Hq_mul_self q), map_mul, map_pow,
    conjHom_apply, conjHom_apply, embedGate1_mul, embedGate1_mul, hadamard_pauliZ_hadamard,
    conj_of_commute (Hq_mul_self q) (commute_pw _ fun i hi =>
      commute_embedGate1 (Or.inl (Ne.symm (update_zero_ne hi))))]

/-- `Z^a X^b = (-1)^{ab} X^b Z^a` on one qubit. -/
theorem Zq_pow_mul_Xq_pow (q : Fin n) (a b : ZMod 2) :
    Zq q ^ a.val * Xq q ^ b.val
      = Complex.I ^ (2 * ((a.val * b.val : ℕ) : ZMod 4)).val • (Xq q ^ b.val * Zq q ^ a.val) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
    have h2 : (2 * (((1 * 1 : ℕ)) : ZMod 4)).val = 2 := rfl
    rw [h1, h2, pow_one, pow_one, embedGate1_mul, embedGate1_mul, pauliZ_mul_pauliX,
      embedGate1_smul, Complex.I_sq]

/-- The conjugate transpose of a gate is any right inverse. -/
theorem conjTranspose_gateEmbedding_eq (g : Gate n) {G' : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : gateEmbedding g * G' = 1) : (gateEmbedding g)ᴴ = G' := by
  calc (gateEmbedding g)ᴴ = (gateEmbedding g)ᴴ * (gateEmbedding g * G') := by rw [h, mul_one]
    _ = G' := by rw [← mul_assoc, gateEmbedding_conjTranspose_mul, one_mul]

/-- **Hadamard.** `H_q P H_q† = (P.conjGate (H q)).mat`. -/
theorem conj_H (q : Fin n) (P : PauliStr n) :
    gateEmbedding (Gate.H q) * P.mat * (gateEmbedding (Gate.H q))ᴴ
      = (P.conjGate (Gate.H q)).mat := by
  rw [conjTranspose_gateEmbedding_eq (Gate.H q) (Hq_mul_self q)]
  show embedGate1 n q hadamard * P.mat * embedGate1 n q hadamard = _
  simp only [PauliStr.mat, PauliStr.conjGate]
  rw [conj_smul, ← conjHom_apply (Hq_mul_self q) (Hq_mul_self q), map_mul, conjHom_apply,
    conjHom_apply, conjH_pwX, conjH_pwZ, pwX_update P.x q (P.z q), pwZ_update P.z q (P.x q),
    I_pow_val_add, ← smul_smul]
  congr 1
  set A := pw Xq (Function.update P.x q 0)
  set B := pw Zq (Function.update P.z q 0)
  have hXB : Commute (Xq q ^ (P.z q).val) B :=
    (commute_pw _ fun i hi => commute_embedGate1 (Or.inl (Ne.symm (update_zero_ne hi)))).pow_left _
  have hZB : Commute (Zq q ^ (P.x q).val) B := (commute_pw _ fun i _ => commute_Zq q i).pow_left _
  calc A * Zq q ^ (P.x q).val * (B * Xq q ^ (P.z q).val)
      = A * (Zq q ^ (P.x q).val * Xq q ^ (P.z q).val) * B := by
        rw [← hXB.eq]; simp only [mul_assoc]
    _ = A * (Complex.I ^ (2 * (((P.x q).val * (P.z q).val : ℕ) : ZMod 4)).val •
          (Xq q ^ (P.z q).val * Zq q ^ (P.x q).val)) * B := by rw [Zq_pow_mul_Xq_pow]
    _ = _ := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← hZB.eq]; simp only [mul_assoc]

/-! ## Phase gate -/

theorem Sq_mul_Sdg (q : Fin n) :
    embedGate1 n q phaseS * embedGate1 n q (phaseS * pauliZ) = 1 := by
  rw [embedGate1_mul, phaseS_sdg, embedGate1_one]

theorem Sdg_mul_Sq (q : Fin n) :
    embedGate1 n q (phaseS * pauliZ) * embedGate1 n q phaseS = 1 := by
  rw [embedGate1_mul, mul_assoc, ← phaseS_mul_pauliZ, phaseS_sdg, embedGate1_one]

theorem conjS_pwX (x : Fin n → ZMod 2) (q : Fin n) :
    embedGate1 n q phaseS * pw Xq x * embedGate1 n q (phaseS * pauliZ)
      = pw Xq (Function.update x q 0) * (Complex.I • (Xq q * Zq q)) ^ (x q).val := by
  rw [pwX_split x q, ← conjHom_apply (Sdg_mul_Sq q) (Sq_mul_Sdg q), map_mul, map_pow,
    conjHom_apply, conjHom_apply, embedGate1_mul, embedGate1_mul, phaseS_pauliX_mul_phaseS_pauliZ,
    embedGate1_smul, embedGate1_mul,
    conj_of_commute (Sq_mul_Sdg q) (commute_pw _ fun i hi =>
      commute_embedGate1 (Or.inl (Ne.symm (update_zero_ne hi))))]

theorem conjS_pwZ (z : Fin n → ZMod 2) (q : Fin n) :
    embedGate1 n q phaseS * pw Zq z * embedGate1 n q (phaseS * pauliZ) = pw Zq z :=
  conj_of_commute (Sq_mul_Sdg q) (commute_pw _ fun _ _ => commute_embedGate1 (Or.inr phaseS_mul_pauliZ))

/-- **Phase gate.** `S_q P S_q† = (P.conjGate (S q)).mat`. -/
theorem conj_S (q : Fin n) (P : PauliStr n) :
    gateEmbedding (Gate.S q) * P.mat * (gateEmbedding (Gate.S q))ᴴ
      = (P.conjGate (Gate.S q)).mat := by
  rw [conjTranspose_gateEmbedding_eq (Gate.S q) (Sq_mul_Sdg q)]
  show embedGate1 n q phaseS * P.mat * embedGate1 n q (phaseS * pauliZ) = _
  simp only [PauliStr.mat, PauliStr.conjGate]
  rw [conj_smul, ← conjHom_apply (Sdg_mul_Sq q) (Sq_mul_Sdg q), map_mul, conjHom_apply,
    conjHom_apply, conjS_pwX, conjS_pwZ, pwX_split P.x q, pw_add commute_Zq Zq_mul_self,
    pw_single, I_pow_val_add, ← smul_smul]
  congr 1
  have hZB : Commute (Zq q) (pw Zq P.z) := commute_pw _ fun i _ => commute_Zq q i
  rcases zmod2_cases (P.x q) with h | h <;> rw [h]
  · simp
  · have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
    have h2 : ZMod.val (1 : ZMod 4) = 1 := rfl
    rw [h1, Nat.cast_one, h2]
    simp only [pow_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← hZB.eq]
    simp only [mul_assoc]

/-! ## CNOT -/

theorem proj0_mul_pauliZ : proj0 * pauliZ = pauliZ * proj0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj1_mul_pauliZ : proj1 * pauliZ = pauliZ * proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj1, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

section CNOT

variable {c t : Fin n}

theorem cnot_mul_self (hct : c ≠ t) : ctrlMatrix c (Xq t) * ctrlMatrix c (Xq t) = 1 := by
  rw [ctrlMatrix_mul (commOn_embedGate1 (Ne.symm hct) _), Xq_mul_self, ctrlMatrix_one]

theorem cnot_Xc_cnot (hct : c ≠ t) :
    ctrlMatrix c (Xq t) * Xq c * ctrlMatrix c (Xq t) = Xq c * Xq t := by
  have hM : CommOn c (Xq t) := commOn_embedGate1 (Ne.symm hct) _
  calc ctrlMatrix c (Xq t) * Xq c * ctrlMatrix c (Xq t)
      = Xq c * (Xq c * ctrlMatrix c (Xq t) * Xq c) * ctrlMatrix c (Xq t) := by
        simp only [← mul_assoc, Xq_mul_self, one_mul]
    _ = Xq c * Xq t := by
        rw [pauliX_ctrlMatrix_pauliX hM, ctrlMatrix_eq_branchMatrix, mul_assoc,
          branchMatrix_mul hM (commOn_one c), mul_one, one_mul, branchMatrix_self]

theorem branchMatrix_neg (c : Fin n) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    branchMatrix c M ((-1 : ℂ) • M) = Zq c * M := by
  rw [branchMatrix, Matrix.mul_smul, ← Matrix.smul_mul, ← embedGate1_smul, ← add_mul,
    ← embedGate1_map_add]
  congr 2
  rw [← proj0_sub_proj1, neg_one_smul, sub_eq_add_neg]

theorem cnot_Zt_cnot (hct : c ≠ t) :
    ctrlMatrix c (Xq t) * Zq t * ctrlMatrix c (Xq t) = Zq c * Zq t := by
  have hM : CommOn c (Xq t) := commOn_embedGate1 (Ne.symm hct) _
  have hZ : CommOn c (Zq t) := commOn_embedGate1 (Ne.symm hct) _
  rw [ctrlMatrix_eq_branchMatrix, ← branchMatrix_self (c := c) (Zq t),
    branchMatrix_mul (commOn_one c) hM, branchMatrix_mul (by simpa using hZ) (hM.mul hZ), one_mul,
    mul_one, embedGate1_mul, embedGate1_mul, pauliX_pauliZ_pauliX, embedGate1_smul,
    branchMatrix_neg, branchMatrix_self]

theorem commute_cnot_Xq {i : Fin n} (hi : i ≠ c) :
    Commute (ctrlMatrix c (Xq t)) (Xq i) := by
  refine Commute.add_left ?_ (Commute.mul_left ?_ (commute_Xq t i))
  · exact commute_embedGate1 (Or.inl (Ne.symm hi))
  · exact commute_embedGate1 (Or.inl (Ne.symm hi))

theorem commute_cnot_Zq {i : Fin n} (hi : i ≠ t) :
    Commute (ctrlMatrix c (Xq t)) (Zq i) := by
  refine Commute.add_left ?_ (Commute.mul_left ?_ (commute_embedGate1 (Or.inl (Ne.symm hi))))
  · exact commute_embedGate1 (Or.inr proj0_mul_pauliZ)
  · exact commute_embedGate1 (Or.inr proj1_mul_pauliZ)

theorem conjCNOT_pwX (hct : c ≠ t) (x : Fin n → ZMod 2) :
    ctrlMatrix c (Xq t) * pw Xq x * ctrlMatrix c (Xq t) = pw Xq (x + Pi.single t (x c)) := by
  rw [pwX_split x c, ← conjHom_apply (cnot_mul_self hct) (cnot_mul_self hct), map_mul, map_pow,
    conjHom_apply, conjHom_apply, cnot_Xc_cnot hct,
    conj_of_commute (cnot_mul_self hct) (commute_pw _ fun i hi =>
      commute_cnot_Xq (update_zero_ne hi)),
    (commute_Xq c t).mul_pow, ← mul_assoc, ← pwX_split, pw_add commute_Xq Xq_mul_self, pw_single]

theorem conjCNOT_pwZ (hct : c ≠ t) (z : Fin n → ZMod 2) :
    ctrlMatrix c (Xq t) * pw Zq z * ctrlMatrix c (Xq t) = pw Zq (z + Pi.single c (z t)) := by
  rw [pwZ_split z t, ← conjHom_apply (cnot_mul_self hct) (cnot_mul_self hct), map_mul, map_pow,
    conjHom_apply, conjHom_apply, cnot_Zt_cnot hct,
    conj_of_commute (cnot_mul_self hct) (commute_pw _ fun i hi =>
      commute_cnot_Zq (update_zero_ne hi)),
    (commute_Zq c t).mul_pow, ((commute_Zq c t).pow_pow _ _).eq, ← mul_assoc, ← pwZ_split,
    pw_add commute_Zq Zq_mul_self, pw_single]

/-- **CNOT.** `CNOT(c,t) P CNOT(c,t)† = (P.conjGate (CNOT c t)).mat`. -/
theorem conj_CNOT (hct : c ≠ t) (P : PauliStr n) :
    gateEmbedding (Gate.CNOT c t) * P.mat * (gateEmbedding (Gate.CNOT c t))ᴴ
      = (P.conjGate (Gate.CNOT c t)).mat := by
  have hG : gateEmbedding (Gate.CNOT c t) = ctrlMatrix c (Xq t) := by
    simp only [gateEmbedding, dite_eq_right hct, embedGate2_cnot]
  rw [conjTranspose_gateEmbedding_eq (Gate.CNOT c t) (hG ▸ cnot_mul_self hct), hG]
  simp only [PauliStr.mat, PauliStr.conjGate]
  rw [conj_smul, ← conjHom_apply (cnot_mul_self hct) (cnot_mul_self hct), map_mul, conjHom_apply,
    conjHom_apply, conjCNOT_pwX hct, conjCNOT_pwZ hct]

end CNOT

/-! ## Clifford circuits -/

/-- `g` is an `H` or `S` gate, or a `CNOT` on two distinct qubits. -/
def IsHSC : Gate n → Prop
  | .H _ | .S _ => True
  | .CNOT c t => c ≠ t
  | _ => False

/-- **One gate.** `U_g P U_g† = (P.conjGate g).mat` for every `H`, `S` and `CNOT` gate. -/
theorem conj_gate {g : Gate n} (hg : IsHSC g) (P : PauliStr n) :
    gateEmbedding g * P.mat * (gateEmbedding g)ᴴ = (P.conjGate g).mat := by
  cases g with
  | H q => exact conj_H q P
  | S q => exact conj_S q P
  | CNOT c t => exact conj_CNOT hg P
  | _ => exact hg.elim

/-- The Pauli string `U_C P U_C†`, computed gate by gate (head gate first). -/
def PauliStr.conjCircuit (P : PauliStr n) (C : List (Gate n)) : PauliStr n :=
  C.foldl (fun P g => P.conjGate g) P

/-- **Gottesman–Knill, Heisenberg picture.** For a circuit `C` of `H`, `S` and `CNOT` gates and
a signed Pauli string `P`, `U_C P U_C†` is the signed Pauli string `P.conjCircuit C`. -/
theorem gottesman_knill : ∀ (C : List (Gate n)) (P : PauliStr n), (∀ g ∈ C, IsHSC g) →
    listMatrix C * P.mat * (listMatrix C)ᴴ = (P.conjCircuit C).mat
  | [], P, _ => by simp [PauliStr.conjCircuit, listMatrix_nil]
  | g :: C, P, h => by
    rw [listMatrix_cons, Matrix.conjTranspose_mul]
    calc listMatrix C * gateEmbedding g * P.mat * ((gateEmbedding g)ᴴ * (listMatrix C)ᴴ)
        = listMatrix C * (gateEmbedding g * P.mat * (gateEmbedding g)ᴴ) * (listMatrix C)ᴴ := by
          simp only [mul_assoc]
      _ = ((P.conjGate g).conjCircuit C).mat := by
          rw [conj_gate (h g List.mem_cons_self),
            gottesman_knill C _ fun g' hg' => h g' (List.mem_cons_of_mem g hg')]

/-! ## Cost of the update -/

/-- The qubits a gate acts on. -/
def gateQubits : Gate n → List (Fin n)
  | .H q | .X q | .Y q | .Z q | .T q | .Tdg q | .S q => [q]
  | .Rz q _ | .RzQ q _ => [q]
  | .CNOT c t | .CZ c t => [c, t]

/-- **Locality.** The update of a gate changes the bits of `x` and `z` only on the qubits of
the gate. -/
theorem conjGate_eq_of_not_mem (g : Gate n) (P : PauliStr n) {i : Fin n}
    (hi : i ∉ gateQubits g) : (P.conjGate g).x i = P.x i ∧ (P.conjGate g).z i = P.z i := by
  cases g <;> simp_all [gateQubits, PauliStr.conjGate, Function.update_of_ne]

/-- The number of tableau entries the update of one Pauli string writes: the phase and at most
two bits. -/
def updCost : Gate n → ℕ
  | .H _ => 3
  | .S _ => 2
  | .CNOT _ _ => 2
  | _ => 0

/-- The number of entries written when a circuit updates a tableau of `m` Pauli strings. -/
def tableauCost (m : ℕ) (C : List (Gate n)) : ℕ := m * (C.map updCost).sum

theorem updCost_le (g : Gate n) : updCost g ≤ 3 := by
  cases g <;> simp [updCost]

/-- **Linear cost.** Updating a tableau of `m` Pauli strings (for a stabilizer state on `n`
qubits, `m = n`) by a circuit `C` writes at most `3 m |C|` entries. -/
theorem tableauCost_le (m : ℕ) (C : List (Gate n)) : tableauCost m C ≤ 3 * m * C.length := by
  have h : (C.map updCost).sum ≤ 3 * C.length := by
    induction C with
    | nil => simp
    | cons g C ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; linarith [updCost_le g]
  rw [tableauCost, mul_comm 3 m, mul_assoc]
  exact Nat.mul_le_mul_left m h

end CatCrypt.Quantum.GottesmanKnill
