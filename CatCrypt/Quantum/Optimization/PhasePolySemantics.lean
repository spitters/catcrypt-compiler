/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.MixedCommute
public import CatCrypt.Quantum.Optimization.PhasePolynomial
public import CatCrypt.Quantum.Optimization.MatrixCorrect

/-!
# Semantics of phase-polynomial parities

A parity `p : Fin n → Bool` selects a subset of the `n` qubits. At a
computational-basis index `x : Fin (2 ^ n)` its *parity form* `⟨p, x⟩` is the
`ZMod 2` sum of the selected bits of `x`, and the associated *phase diagonal*
is the diagonal matrix `diag (fun x => exp (i θ ⟨p, x⟩))`.

This is the matrix layer under a `{CNOT, Rz}` circuit block: an `Rz θ` on a
wire carrying the parity `p` is the phase diagonal of `p`, and conjugating a
phase diagonal by a `CNOT` transforms the parity linearly.

## Main results

* `phaseDiag_mul` — phase diagonals of the same parity add their angles.
* `phaseDiag_zero` — the phase diagonal at angle `0` is the identity.
* `phaseDiag_comm` — any two phase diagonals commute.
* `parityForm_cnot` — the parity form at the `CNOT` image of a basis index
  equals the parity form of `cnotParity p c t` at that index.
* `cnot_mul_phaseDiag` — a `CNOT` moves past a phase diagonal, replacing the
  parity `p` by `cnotParity p c t`.
* `cnot_conj_phaseDiag` — conjugating the phase diagonal of `p` by
  `CNOT (c, t)` gives the phase diagonal of `cnotParity p c t`.
* `rz_embed_eq_phaseDiag` — the embedded `Rz q θ` matrix is the phase diagonal
  of the singleton parity at `q`.
* `cnotLadder_circuitUnitary` — the unitary of a `CNOT` ladder around an
  `Rz q θ` is the phase diagonal of `ladderParity q l`.
* `ladderParity_apply` — for a duplicate-free control list avoiding `q`, that
  parity selects `q` together with the controls.

## References

* Amy, Maslov, Mosca — Polynomial-time T-depth optimization of Clifford+T
  circuits via matroid partitioning, IEEE Trans. on CAD, 2014
* Nam, Ross, Su, Childs, Maslov — Automated optimization of large quantum
  circuits with continuous parameters, npj Quantum Information, 2018
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit

noncomputable section

namespace CatCrypt.Quantum.Optimization.PhasePolySemantics

open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.Optimization.PhasePolynomial (Parity)

variable {n : ℕ}

/-! ## The parity form -/

/-- The bit that qubit `i` reads at the basis index `x`, as an element of
    `ZMod 2`. -/
def bitZ (n : ℕ) (i : Fin n) (x : ℕ) : ZMod 2 := ((gbit n i x).val : ZMod 2)

theorem bitZ_eq_testBit (i : Fin n) (x : ℕ) :
    bitZ n i x = ((x.testBit (pos n i)).toNat : ZMod 2) := by
  rw [bitZ, gbit_eq_testBit]

/-- The parity form `⟨p, x⟩`: the `ZMod 2` sum of the bits of `x` selected
    by `p`. -/
def parityForm (p : Parity n) (x : ℕ) : ZMod 2 :=
  ∑ i : Fin n, if p i then bitZ n i x else 0

/-- The phase diagonal of a parity: the diagonal matrix whose entry at the
    basis index `x` is `exp (i θ ⟨p, x⟩)`. -/
def phaseDiag (p : Parity n) (θ : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal fun x => Complex.exp (Complex.I * (θ : ℂ) * ((parityForm p x.val).val : ℂ))

/-! ## Diagonal algebra -/

theorem phaseDiag_isDiagonal (p : Parity n) (θ : ℝ) :
    MixedCommute.IsDiagonal (phaseDiag p θ) := by
  intro r c hrc
  simp only [phaseDiag, Matrix.diagonal_apply, ite_eq_right hrc]

/-- Phase diagonals of the same parity add their angles. -/
theorem phaseDiag_mul (p : Parity n) (θ₁ θ₂ : ℝ) :
    phaseDiag p θ₁ * phaseDiag p θ₂ = phaseDiag p (θ₁ + θ₂) := by
  simp only [phaseDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The phase diagonal at angle `0` is the identity matrix. -/
theorem phaseDiag_zero (p : Parity n) : phaseDiag p 0 = 1 := by
  simp only [phaseDiag, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
  exact Matrix.diagonal_one

/-- Any two phase diagonals commute. -/
theorem phaseDiag_comm (p q : Parity n) (θ φ : ℝ) :
    phaseDiag p θ * phaseDiag q φ = phaseDiag q φ * phaseDiag p θ := by
  simp only [phaseDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  ring

/-! ## The `CNOT` action on parities -/

/-- The parity `p` transformed by conjugation with `CNOT` of control `c` and
    target `t`: the `t` component is XORed into the `c` component. -/
def cnotParity (p : Parity n) (c t : Fin n) : Parity n :=
  fun i => if i = c then xor (p c) (p t) else p i

@[simp]
theorem cnotParity_self (p : Parity n) (c t : Fin n) :
    cnotParity p c t c = xor (p c) (p t) := by
  simp [cnotParity]

theorem cnotParity_of_ne {p : Parity n} {c t i : Fin n} (h : i ≠ c) :
    cnotParity p c t i = p i := by
  simp only [cnotParity, ite_eq_right h]

/-! ## Splitting a sum off two indices -/

/-- Two sums over `Fin n` agree when the summands agree off a pair of indices
    and the two pair contributions have equal sums. -/
private theorem sum_eq_of_off_pair {M : Type*} [AddCommMonoid M] {c t : Fin n}
    (hct : c ≠ t) (f g : Fin n → M)
    (hoff : ∀ i, i ≠ c → i ≠ t → f i = g i)
    (hpair : f c + f t = g c + g t) :
    ∑ i : Fin n, f i = ∑ i : Fin n, g i := by
  have htu : t ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ t
  have hcu : c ∈ (Finset.univ : Finset (Fin n)).erase t :=
    Finset.mem_erase.mpr ⟨hct, Finset.mem_univ c⟩
  rw [← Finset.sum_erase_add _ f htu, ← Finset.sum_erase_add _ g htu,
    ← Finset.sum_erase_add _ f hcu, ← Finset.sum_erase_add _ g hcu]
  have hsum : ∑ i ∈ ((Finset.univ : Finset (Fin n)).erase t).erase c, f i
      = ∑ i ∈ ((Finset.univ : Finset (Fin n)).erase t).erase c, g i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hoff i (Finset.mem_erase.mp hi).1
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
  rw [hsum, add_assoc, add_assoc, hpair]

/-! ## The parity form under the `CNOT` basis map -/

theorem bitZ_eq_of_match2 {c t i : Fin n} (hic : i ≠ c) (hit : i ≠ t) {x y : ℕ}
    (h : Match2 n c t x y) : bitZ n i x = bitZ n i y := by
  rw [bitZ_eq_testBit, bitZ_eq_testBit, h (pos n i) (pos_ne hic) (pos_ne hit)]

/-- The parity form at a basis index `y` reached from `x` by the `CNOT` basis
    map — same control bit, target bit XORed with the control bit, all other
    bits unchanged — is the parity form of `cnotParity p c t` at `x`. -/
theorem parityForm_cnot {c t : Fin n} (hct : c ≠ t) (p : Parity n) {x y : ℕ}
    (hM : Match2 n c t x y)
    (hc : bitZ n c y = bitZ n c x)
    (ht : bitZ n t y = bitZ n t x + bitZ n c x) :
    parityForm p y = parityForm (cnotParity p c t) x := by
  have key : ∀ (P Q : Bool) (u v : ZMod 2),
      (if P then u else 0) + (if Q then v + u else 0)
        = (if xor P Q then u else 0) + (if Q then v else 0) := by decide
  refine sum_eq_of_off_pair hct _ _ ?_ ?_
  · intro i hic hit
    rw [cnotParity_of_ne hic, bitZ_eq_of_match2 hic hit hM]
  · rw [cnotParity_self, cnotParity_of_ne (Ne.symm hct), hc, ht]
    exact key (p c) (p t) (bitZ n c x) (bitZ n t x)

/-! ## The `CNOT` entry constraint -/

/-- The `Fin 4` subindex of a two-qubit gate built from its two bits. -/
private def pack (a b : Fin 2) : Fin 4 :=
  ⟨a.val * 2 + b.val, by have := a.isLt; have := b.isLt; omega⟩

private theorem idx4_eq_pack (i j : Fin n) (v : ℕ) :
    idx4 n i j v = pack (gbit n i v) (gbit n j v) := rfl

/-- A nonzero `cnot` entry forces the column bits to be the row bits with the
    target bit XORed by the control bit. -/
private theorem cnot_pack_bits {a b a' b' : Fin 2}
    (h : cnot (pack a b) (pack a' b') ≠ 0) :
    ((a'.val : ZMod 2) = (a.val : ZMod 2)) ∧
      ((b'.val : ZMod 2) = (b.val : ZMod 2) + (a.val : ZMod 2)) := by
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp_all [cnot, pack]
  decide

/-! ## Conjugation of a phase diagonal by a `CNOT` -/

/-- A `CNOT` with control `c` and target `t` moves past the phase diagonal of
    `p`, which becomes the phase diagonal of `cnotParity p c t`. -/
theorem cnot_mul_phaseDiag {c t : Fin n} (hct : c ≠ t) (p : Parity n) (θ : ℝ) :
    embedGate2 n c t cnot hct * phaseDiag p θ
      = phaseDiag (cnotParity p c t) θ * embedGate2 n c t cnot hct := by
  ext x y
  simp only [phaseDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : embedGate2 n c t cnot hct x y = 0
  · rw [hz, zero_mul, mul_zero]
  · have hpar : parityForm p y.val = parityForm (cnotParity p c t) x.val := by
      rw [MixedCommute.embedGate2_apply hct] at hz
      by_cases hM : Match2 n c t x.val y.val
      · rw [ite_eq_left hM] at hz
        rw [idx4_eq_pack, idx4_eq_pack] at hz
        obtain ⟨hc, ht⟩ := cnot_pack_bits hz
        exact parityForm_cnot hct p hM hc ht
      · rw [ite_eq_right hM] at hz
        exact absurd rfl hz
    rw [hpar, mul_comm]

/-- Conjugating the phase diagonal of `p` by a `CNOT` with control `c` and
    target `t` gives the phase diagonal of `cnotParity p c t`. -/
theorem cnot_conj_phaseDiag {c t : Fin n} (hct : c ≠ t) (p : Parity n) (θ : ℝ) :
    embedGate2 n c t cnot hct * phaseDiag p θ * embedGate2 n c t cnot hct
      = phaseDiag (cnotParity p c t) θ := by
  rw [cnot_mul_phaseDiag hct, mul_assoc, embedGate2_mul, cnot_sq, embedGate2_one, mul_one]

/-! ## The `Rz` gate as a phase diagonal -/

/-- The parity selecting exactly the qubit `q`. -/
def singletonParity (q : Fin n) : Parity n := fun i => decide (i = q)

@[simp]
theorem parityForm_singletonParity (q : Fin n) (x : ℕ) :
    parityForm (singletonParity q) x = bitZ n q x := by
  simp [parityForm, singletonParity]

/-- `rzGate θ` is diagonal. -/
theorem rzGate_isDiagonal (θ : ℝ) : MixedCommute.IsDiagonal (rzGate θ) := by
  intro r c hrc
  fin_cases r <;> fin_cases c <;> simp_all [rzGate]

private theorem rzGate_diag_entry (θ : ℝ) (b : Fin 2) :
    rzGate θ b b = Complex.exp (Complex.I * (θ : ℂ) * ((((b.val : ZMod 2)).val : ℂ))) := by
  fin_cases b <;> simp [rzGate, ZMod.val_one]

/-- The embedded `Rz q θ` matrix is the phase diagonal of the singleton parity
    at `q`. -/
theorem rz_embed_eq_phaseDiag (q : Fin n) (θ : ℝ) :
    embedGate1 n q (rzGate θ) = phaseDiag (singletonParity q) θ := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    have hM : Match n q x.val x.val := fun _ _ => rfl
    rw [embedGate1_apply, phaseDiag, Matrix.diagonal_apply, ite_eq_left rfl,
      ite_eq_left hM, parityForm_singletonParity, bitZ]
    exact rzGate_diag_entry θ (gbit n q x.val)
  · rw [phaseDiag, Matrix.diagonal_apply, ite_eq_right hxy]
    exact MixedCommute.embedGate1_isDiagonal q (rzGate_isDiagonal θ) x y hxy

/-! ## The `CNOT` ladder -/

/-- The gate list realizing a rotation on a parity: build the parity of `l`
    onto the wire `q` with a `CNOT` ladder, rotate `q` by `θ`, then unwind. -/
def cnotLadder (q : Fin n) (l : List (Fin n)) (θ : ℝ) : List (Gate n) :=
  l.map (fun r => Gate.CNOT r q) ++ [Gate.Rz q θ] ++
    l.reverse.map (fun r => Gate.CNOT r q)

/-- The parity realized by `cnotLadder q l θ`: the singleton parity at `q`
    conjugated by the ladder's `CNOT`s, innermost first. -/
def ladderParity (q : Fin n) : List (Fin n) → Parity n
  | [] => singletonParity q
  | r :: rest => cnotParity (ladderParity q rest) r q

/-- The `CNOT` ladder around an `Rz θ` realizes the phase diagonal of
    `ladderParity q l`, provided no ladder control coincides with the rotation
    wire `q`. -/
theorem cnotLadder_circuitUnitary (q : Fin n) (θ : ℝ) :
    ∀ l : List (Fin n), (∀ r ∈ l, r ≠ q) →
      (RoutingPerm.circuitUnitary (Circuit.ofList (cnotLadder q l θ))).val
        = phaseDiag (ladderParity q l) θ := by
  intro l
  induction l with
  | nil =>
    intro _
    rw [show cnotLadder q [] θ = [Gate.Rz q θ] by simp [cnotLadder],
      circuitUnitary_ofList_single]
    show embedGate1 n q (rzGate θ) = _
    rw [rz_embed_eq_phaseDiag]
    rfl
  | cons r rest ih =>
    intro hq
    have hrq : r ≠ q := hq r (List.mem_cons_self ..)
    have hrest : ∀ s ∈ rest, s ≠ q := fun s hs => hq s (List.mem_cons_of_mem r hs)
    have hsplit : cnotLadder q (r :: rest) θ
        = [Gate.CNOT r q] ++ cnotLadder q rest θ ++ [Gate.CNOT r q] := by
      simp [cnotLadder, List.append_assoc]
    have hC : (gateEmbedding_unitaryGroup (Gate.CNOT r q : Gate n)).val
        = embedGate2 n r q cnot hrq := by
      show gateEmbedding (Gate.CNOT r q : Gate n) = _
      simp only [gateEmbedding, dite_eq_right hrq]
    rw [hsplit, circuitUnitary_ofList_append, circuitUnitary_ofList_append,
      circuitUnitary_ofList_single]
    show (gateEmbedding_unitaryGroup (Gate.CNOT r q : Gate n)).val *
      ((RoutingPerm.circuitUnitary (Circuit.ofList (cnotLadder q rest θ))).val *
        (gateEmbedding_unitaryGroup (Gate.CNOT r q : Gate n)).val) = _
    rw [ih hrest, hC, ← mul_assoc]
    exact cnot_conj_phaseDiag hrq (ladderParity q rest) θ

/-- For a duplicate-free control list avoiding the rotation wire, the ladder
    parity selects exactly the rotation wire together with the controls. -/
theorem ladderParity_apply (q : Fin n) :
    ∀ l : List (Fin n), (∀ r ∈ l, r ≠ q) → l.Nodup → ∀ i : Fin n,
      ladderParity q l i = (decide (i = q) || decide (i ∈ l)) := by
  intro l
  induction l with
  | nil => intro _ _ i; simp [ladderParity, singletonParity]
  | cons r rest ih =>
    intro hq hnd i
    have hrq : r ≠ q := hq r (by simp)
    have hrest : ∀ s ∈ rest, s ≠ q := fun s hs => hq s (by simp [hs])
    have hrnotin : r ∉ rest := (List.nodup_cons.mp hnd).1
    have hndr : rest.Nodup := (List.nodup_cons.mp hnd).2
    show cnotParity (ladderParity q rest) r q i = _
    by_cases hir : i = r
    · subst hir
      rw [cnotParity_self, ih hrest hndr i, ih hrest hndr q]
      simp [hrq, hrnotin]
    · rw [cnotParity_of_ne hir, ih hrest hndr i]
      simp [List.mem_cons, hir]

end CatCrypt.Quantum.Optimization.PhasePolySemantics
