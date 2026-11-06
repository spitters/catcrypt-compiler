/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QRegister
public import CatCrypt.Quantum.QPL

/-!
# Register measurement

The measurement of a typed register (a quantum variable) in the computational basis is a
derived QPL program: it measures the qubits of the register one at a time with QPL's `meas`,
from the last position to the first, records each outcome as a bit, and returns the `w`-bit
value of the register. On the basis state `|x⟩` it returns the value `r.val x` of the register
with probability one and leaves the state `|x⟩` unchanged (`measReg_branch_basisState`).

## Main definitions

* `basisState x` — the density matrix `|x⟩⟨x|` of the basis state `x`.
* `Reg.measAux r m acc` — measure the positions `m - 1, …, 0` of the register into the bit
  string `acc`, then return its value.
* `Reg.measReg r` — the register measurement, returning a value in `Fin (2 ^ w)`.

## Main results

* `measQubit_branch_basisState` — measuring one qubit of `|x⟩` gives its bit with
  certainty and leaves `|x⟩` unchanged.
* `Reg.measReg_branch_basisState` — the register measurement of `|x⟩` has the single
  outcome `r.val x`, with post-measurement state `|x⟩`.
* `Reg.measReg_trace_basisState` — its outcome probabilities.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum
open CatCrypt.Quantum.Measurement
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.QPL

noncomputable section

namespace CatCrypt.Quantum.QRegister

variable {n w : ℕ} {Ops : Type}

/-- The density matrix `|x⟩⟨x|` of the basis state `x`. -/
def basisState (x : Fin (2 ^ n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := Matrix.single x x 1

/-- The single-qubit computational-basis projectors are diagonal. -/
theorem isDiagonal_qubitProj (b : Bool) : IsDiagonal (QPL.qubitProj b) := by
  intro r c h
  cases b <;> fin_cases r <;> fin_cases c <;> simp_all [QPL.qubitProj]

/-- **Measuring one qubit of a basis state.** The outcome is the bit of `x` at the qubit with
    certainty, and the state stays `|x⟩`. -/
theorem measQubit_branch_basisState (q : Fin n) (b : Bool) (x : Fin (2 ^ n)) :
    (QPL.measQubit q).branch b (basisState x)
      = if b = decide (gbit n q x.val = 1) then basisState x else 0 := by
  simp only [QPL.measQubit, projectiveMeasure, measureOps, QPL.measQubitPM, LinearMap.coe_mk,
    AddHom.coe_mk, GateUnitarity.embedGate1_conjTranspose, QPL.qubitProj_conjTranspose,
    embedGate1_eq_diagonal _ (isDiagonal_qubitProj b)]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, basisState, Matrix.single_apply]
  by_cases hij : x = i ∧ x = j
  · obtain ⟨rfl, rfl⟩ := hij
    rcases Fin.exists_fin_two.mp ⟨gbit n q x.val, rfl⟩ with h | h <;> cases b <;>
      simp [QPL.qubitProj, h]
  · split_ifs <;> simp [hij]

namespace Reg

variable (r : Reg n w)

/-- Measure the positions `m - 1, …, 0` of the register, writing outcome `|1⟩` or `|0⟩` of
    position `i` into bit `i` of the string `acc`, and return the value of the string. -/
def measAux : ℕ → (Fin w → Fin 2) → XQPL Ops n (Fin (2 ^ w))
  | 0, acc => .ret ((bitEquiv w).symm acc)
  | m + 1, acc =>
    if h : m < w then
      .meas (r.q ⟨m, h⟩) (measAux m (Function.update acc ⟨m, h⟩ 1))
        (measAux m (Function.update acc ⟨m, h⟩ 0))
    else measAux m acc

/-- The measurement of the register in the computational basis: each of its qubits is
    measured, and the program returns the value of the register. -/
def measReg : XQPL Ops n (Fin (2 ^ w)) := r.measAux w fun _ => 0

/-- The partial register measurement of `|x⟩`: when `acc` already holds the bits of `x` at
    the positions from `m` on, measuring the positions below `m` returns `r.val x`. -/
theorem measAux_branch_basisState [OpDenote Ops n] (x : Fin (2 ^ n)) (v : Fin (2 ^ w)) :
    ∀ (m : ℕ) (acc : Fin w → Fin 2), (∀ i : Fin w, m ≤ i.val → acc i = gbit n (r.q i) x.val) →
      (r.measAux (Ops := Ops) m acc).denote.branch v (basisState x)
        = if v = r.val x then basisState x else 0
  | 0, acc, h => by
    have hacc : (bitEquiv w).symm acc = r.val x := by
      rw [val]
      congr 1
      funext i
      exact h i (Nat.zero_le _)
    simp only [measAux, XQPL.denote_ret, QComp.qpure, hacc]
    split_ifs <;> simp
  | m + 1, acc, h => by
    by_cases hm : m < w
    · simp only [measAux, hm, dite_true, XQPL.denote_meas, QComp.qbind, LinearMap.coe_mk,
        AddHom.coe_mk, tsum_fintype, Fintype.sum_bool, measQubit_branch_basisState]
      have hupd : ∀ c, gbit n (r.q ⟨m, hm⟩) x.val = c → ∀ i : Fin w, m ≤ i.val →
          Function.update acc ⟨m, hm⟩ c i = gbit n (r.q i) x.val := by
        intro c hc i hi
        by_cases hi' : i = ⟨m, hm⟩
        · subst hi'
          simp [hc]
        · rw [Function.update_of_ne hi']
          exact h i (by have := Fin.val_ne_of_ne hi'; simp only at this; omega)
      rcases Fin.exists_fin_two.mp ⟨gbit n (r.q ⟨m, hm⟩) x.val, rfl⟩ with hb | hb
      · simp [hb, measAux_branch_basisState x v m _ (hupd 0 hb)]
      · simp [hb, measAux_branch_basisState x v m _ (hupd 1 hb)]
    · simp only [measAux, hm, dite_false]
      exact measAux_branch_basisState x v m acc fun i hi => by omega

/-- **Register measurement of a basis state.** On `|x⟩` the register measurement has the
    single outcome `r.val x`, and the post-measurement state is `|x⟩`. -/
theorem measReg_branch_basisState [OpDenote Ops n] (x : Fin (2 ^ n)) (v : Fin (2 ^ w)) :
    (r.measReg (Ops := Ops)).denote.branch v (basisState x)
      = if v = r.val x then basisState x else 0 :=
  r.measAux_branch_basisState x v w _ fun i hi => absurd i.isLt (by omega)

/-- The register measurement of `|x⟩` returns `r.val x` with probability one. -/
theorem measReg_trace_basisState [OpDenote Ops n] (x : Fin (2 ^ n)) (v : Fin (2 ^ w)) :
    ((r.measReg (Ops := Ops)).denote.branch v (basisState x)).trace
      = if v = r.val x then 1 else 0 := by
  rw [r.measReg_branch_basisState]
  split_ifs <;> simp [basisState]

end Reg

end CatCrypt.Quantum.QRegister
