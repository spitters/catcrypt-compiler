/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Qelib
public import CatCrypt.Quantum.QrunchFuse

/-!
# Swap elision: an output permutation in place of `swap` statements

`elideQ` scans a list of OpenQASM 2 statements, drops every `swap` and relabels the
statements after it, so that the program is realised up to a qubit relabelling (a final
layout), as in Qiskit's `ElidePermutations` pass. The pass keeps a permutation `π` of the
qubits that maps a wire of the input program, at the current point of the scan, to the
wire of the output program that carries the same state. A statement on input wires `q` is
emitted on the output wires `π q`; a `swap a b` replaces `π` by `π * swap a b` and emits
nothing. The returned permutation is the value of `π` at the end: the state of input
qubit `q` at the end of the input program is the state of output wire `π q` at the end of
the output program.

`wireMatrix σ` is the permutation matrix on the `2 ^ n` basis states of the qubit
relabelling `σ`, in the qubit convention of `embedGate1` (qubit `0` is the most significant
bit); `wireMatrix (swap a b)` is the matrix of the statement `swap a b`.

## Main results

* `relabelQ` — qubit relabelling of a statement.
* `qelibMatrix_mul_wireMatrix` — `qelibMatrix g * wireMatrix σ =
  wireMatrix σ * qelibMatrix (relabelQ σ g)`.
* `elideQ` — the pass, returning the statements and the output permutation.
* `qelibListMatrix_elideQ` — `qelibListMatrix l = wireMatrix π * qelibListMatrix l'` for
  `(l', π) = elideQ l`: the output program followed by the qubit permutation.
* `countP_elideQ` — the pass keeps the `cx` statements; counting `swap` as three `cx`, the
  count falls by three per `swap`.
* `length_elideQ_le` — the pass does not lengthen the list.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.Qelib
open CatCrypt.Quantum.ControlledGates (ctrlMatrix)
open CatCrypt.Quantum.Optimization.RoutingPerm
open CatCrypt.Quantum.Optimization.SwapConj
open CatCrypt.Quantum.Optimization.DisjointCommute

noncomputable section

namespace CatCrypt.Quantum.SwapElide

variable {n : ℕ}

/-! ## Qubit relabelling of a statement -/

/-- The statement `g` with each qubit `q` replaced by `σ q`. -/
def relabelQ (σ : Equiv.Perm (Fin n)) : QGate n → QGate n
  | .h q => .h (σ q)
  | .x q => .x (σ q)
  | .y q => .y (σ q)
  | .z q => .z (σ q)
  | .s q => .s (σ q)
  | .sdg q => .sdg (σ q)
  | .t q => .t (σ q)
  | .tdg q => .tdg (σ q)
  | .sx q => .sx (σ q)
  | .sxdg q => .sxdg (σ q)
  | .rx q θ => .rx (σ q) θ
  | .ry q θ => .ry (σ q) θ
  | .rz q θ => .rz (σ q) θ
  | .p q θ => .p (σ q) θ
  | .u q θ φ l => .u (σ q) θ φ l
  | .u2 q φ l => .u2 (σ q) φ l
  | .cx c t => .cx (σ c) (σ t)
  | .cz c t => .cz (σ c) (σ t)
  | .swap a b => .swap (σ a) (σ b)
  | .cp c t θ => .cp (σ c) (σ t) θ
  | .ccx a b t => .ccx (σ a) (σ b) (σ t)
  | .ccz a b t => .ccz (σ a) (σ b) (σ t)

/-- Relabelling by a product is relabelling by the right factor, then by the left. -/
theorem relabelQ_mul (σ τ : Equiv.Perm (Fin n)) (g : QGate n) :
    relabelQ (σ * τ) g = relabelQ σ (relabelQ τ g) := by
  cases g <;> simp [relabelQ]

/-- Relabelling by the identity is the identity. -/
theorem relabelQ_one (g : QGate n) : relabelQ 1 g = g := by
  cases g <;> simp [relabelQ]

/-! ## The permutation matrix of a qubit relabelling -/

/-- The qubit relabelling `σ` read in the bit-position convention of `qubitPermUnitary`:
    conjugation by the reversal `k ↦ n - 1 - k`. -/
def revConj : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n) :=
  (MulAut.conj (Fin.revPerm (n := n))).toMonoidHom

/-- The permutation matrix of the qubit relabelling `σ` on the `2 ^ n` basis states, in the
    qubit convention of `embedGate1`. -/
def wireMatrix (σ : Equiv.Perm (Fin n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (qubitPermUnitary (revConj σ)).val

/-- The identity relabelling has the identity matrix. -/
theorem wireMatrix_one : wireMatrix (1 : Equiv.Perm (Fin n)) = 1 := by
  simp [wireMatrix]

/-- `wireMatrix` reverses products. -/
theorem wireMatrix_mul (σ τ : Equiv.Perm (Fin n)) :
    wireMatrix (σ * τ) = wireMatrix τ * wireMatrix σ := by
  simp only [wireMatrix, map_mul, qubitPermUnitary_mul, Matrix.UnitaryGroup.mul_val]

/-- The relabelling of a transposition is the position transposition `swapBitPerm`. -/
theorem revConj_swap (a b : Fin n) : revConj (Equiv.swap a b) = swapBitPerm a b := by
  have hr : ∀ k : Fin n, Fin.revPerm k = posIdx k := fun k => by
    ext; simp only [Fin.revPerm_apply, Fin.val_rev, posIdx, pos]; omega
  rw [revConj, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← Equiv.swap_apply_apply, swapBitPerm,
    hr, hr]

/-- `wireMatrix (swap a b)` is the matrix of the statement `swap a b`. -/
theorem wireMatrix_swap (a b : Fin n) :
    wireMatrix (Equiv.swap a b) = qelibMatrix (QGate.swap a b) := by
  simp only [wireMatrix, revConj_swap, qelibMatrix]

/-- The matrix of a transposition is an involution. -/
theorem swapMat_mul_self (a b : Fin n) :
    (qubitPermUnitary (swapBitPerm a b)).val * (qubitPermUnitary (swapBitPerm a b)).val = 1 := by
  rw [← Matrix.UnitaryGroup.mul_val, ← qubitPermUnitary_mul, swapBitPerm, Equiv.swap_mul_self,
    qubitPermUnitary_one, Matrix.UnitaryGroup.one_val]

/-! ## Conjugation by a transposition -/

section Swap

variable (a b : Fin n)

/-- One-qubit embeddings are relabelled by conjugation with a transposition. -/
theorem embedGate1_swap_conj (q : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n (Equiv.swap a b q) G =
      (qubitPermUnitary (swapBitPerm a b)).val * embedGate1 n q G *
        (qubitPermUnitary (swapBitPerm a b)).val := by
  have hinv : (swapBitPerm a b)⁻¹ = swapBitPerm a b := Equiv.swap_inv _ _
  ext r c
  have h := conj_qubitPermUnitary_apply (swapBitPerm a b) (embedGate1 n q G) r c
  rw [hinv] at h
  rw [h, embedGate1_apply, embedGate1_apply, gbit_qubitBitPerm_swap, gbit_qubitBitPerm_swap]
  have e : ∀ (i : Fin n) (u v : ℕ), Match n i u v ↔ Match2 n i i u v :=
    fun i u v => ⟨fun h p hp _ => h p hp, fun h p hp => h p hp hp⟩
  have hm : Match n q (qubitBitPerm (swapBitPerm a b) r).val
      (qubitBitPerm (swapBitPerm a b) c).val ↔ Match n (Equiv.swap a b q) r.val c.val := by
    rw [e, e]; exact match2_qubitBitPerm_swap a b q q r c
  by_cases hM : Match n (Equiv.swap a b q) r.val c.val
  · rw [ite_eq_left hM, ite_eq_left (hm.mpr hM)]
  · rw [ite_eq_right hM, ite_eq_right (fun h' => hM (hm.mp h'))]

/-- Two-qubit embeddings are relabelled by conjugation with a transposition. -/
theorem embedGate2_swap_conj (G : Matrix (Fin 4) (Fin 4) ℂ) {i j : Fin n} (hij : i ≠ j)
    (hij' : Equiv.swap a b i ≠ Equiv.swap a b j) :
    embedGate2 n (Equiv.swap a b i) (Equiv.swap a b j) G hij' =
      (qubitPermUnitary (swapBitPerm a b)).val * embedGate2 n i j G hij *
        (qubitPermUnitary (swapBitPerm a b)).val := by
  have h := embedGate2_relabel a b G hij hij'
  rwa [swapBitPerm, Equiv.swap_inv] at h

/-- Controlled matrices are relabelled by conjugation with a transposition. -/
theorem ctrlMatrix_swap_conj (c : Fin n) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ctrlMatrix (Equiv.swap a b c)
        ((qubitPermUnitary (swapBitPerm a b)).val * M *
          (qubitPermUnitary (swapBitPerm a b)).val) =
      (qubitPermUnitary (swapBitPerm a b)).val * ctrlMatrix c M *
        (qubitPermUnitary (swapBitPerm a b)).val := by
  have hS := swapMat_mul_self a b
  rw [ctrlMatrix, ctrlMatrix, embedGate1_swap_conj, embedGate1_swap_conj, Matrix.mul_add,
    Matrix.add_mul]
  congr 1
  simp only [mul_assoc]
  rw [← mul_assoc (qubitPermUnitary (swapBitPerm a b)).val
    (qubitPermUnitary (swapBitPerm a b)).val, hS, one_mul]

/-- The matrix of a statement relabelled by a transposition is its conjugate. -/
theorem qelibMatrix_relabelQ_swap (g : QGate n) :
    qelibMatrix (relabelQ (Equiv.swap a b) g) =
      (qubitPermUnitary (swapBitPerm a b)).val * qelibMatrix g *
        (qubitPermUnitary (swapBitPerm a b)).val := by
  have hinv : (swapBitPerm a b)⁻¹ = swapBitPerm a b := Equiv.swap_inv _ _
  have hS := swapMat_mul_self a b
  have hne : ∀ {d t : Fin n}, d ≠ t → Equiv.swap a b d ≠ Equiv.swap a b t :=
    fun h => (Equiv.injective _).ne h
  cases g <;> simp only [relabelQ, qelibMatrix] <;>
    try exact embedGate1_swap_conj a b _ _
  case cx c t =>
    have h := gateEmbedding_relabel_CNOT c t a b
    rwa [hinv] at h
  case cz c t =>
    have h := gateEmbedding_relabel_CZ c t a b
    rwa [hinv] at h
  case swap c d =>
    have key : swapBitPerm (Equiv.swap a b c) (Equiv.swap a b d) =
        swapBitPerm a b * swapBitPerm c d * swapBitPerm a b := by
      rw [show swapBitPerm (Equiv.swap a b c) (Equiv.swap a b d) =
          Equiv.swap (posIdx (Equiv.swap a b c)) (posIdx (Equiv.swap a b d)) from rfl,
        ← swapBitPerm_posIdx, ← swapBitPerm_posIdx, Equiv.swap_apply_apply, hinv]
      rfl
    simp only [key, qubitPermUnitary_mul, Matrix.UnitaryGroup.mul_val, mul_assoc]
  case cp c t θ =>
    rw [embedGate1_swap_conj]; exact ctrlMatrix_swap_conj a b c _
  case ccx c d t =>
    unfold ccxMatrix
    by_cases h : d ≠ t
    · rw [dite_eq_left (hne h), dite_eq_left h, embedGate2_swap_conj a b _ h (hne h),
        ctrlMatrix_swap_conj]
    · have h' : ¬ Equiv.swap a b d ≠ Equiv.swap a b t := by
        push Not at h ⊢; rw [h]
      rw [dite_eq_right h', dite_eq_right h, mul_one, hS]
  case ccz c d t =>
    unfold cczMatrix
    by_cases h : d ≠ t
    · rw [dite_eq_left (hne h), dite_eq_left h, embedGate2_swap_conj a b _ h (hne h),
        ctrlMatrix_swap_conj]
    · have h' : ¬ Equiv.swap a b d ≠ Equiv.swap a b t := by
        push Not at h ⊢; rw [h]
      rw [dite_eq_right h', dite_eq_right h, mul_one, hS]

end Swap

/-- **Relabelling a statement.** The matrix of `g` followed by the relabelling `σ` is the
    relabelling followed by `g` relabelled by `σ`. -/
theorem qelibMatrix_mul_wireMatrix (σ : Equiv.Perm (Fin n)) (g : QGate n) :
    qelibMatrix g * wireMatrix σ = wireMatrix σ * qelibMatrix (relabelQ σ g) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing g with
  | one => simp [wireMatrix_one, relabelQ_one]
  | swap_mul f x y _ ih =>
    have hs : qelibMatrix (relabelQ (Equiv.swap x y) (relabelQ f g)) =
        wireMatrix (Equiv.swap x y) * qelibMatrix (relabelQ f g) *
          wireMatrix (Equiv.swap x y) := by
      rw [wireMatrix, revConj_swap]; exact qelibMatrix_relabelQ_swap x y _
    have hSS : wireMatrix (Equiv.swap x y) * wireMatrix (Equiv.swap x y) = 1 := by
      rw [wireMatrix, revConj_swap]; exact swapMat_mul_self x y
    rw [wireMatrix_mul, ← mul_assoc, ih, relabelQ_mul, hs]
    simp only [mul_assoc]
    rw [← mul_assoc (wireMatrix (Equiv.swap x y)) (wireMatrix (Equiv.swap x y)), hSS, one_mul]

/-! ## The pass -/

/-- The scan from the permutation `σ`: each `swap a b` is dropped and multiplies `σ` on the
    right by `swap a b`; every other statement is emitted relabelled by `σ`. -/
def elideFrom : Equiv.Perm (Fin n) → List (QGate n) → List (QGate n) × Equiv.Perm (Fin n)
  | σ, [] => ([], σ)
  | σ, .swap a b :: l => elideFrom (σ * Equiv.swap a b) l
  | σ, g :: l => let r := elideFrom σ l; (relabelQ σ g :: r.1, r.2)

/-- **Swap elision.** Drop the `swap` statements and return the output permutation `π`:
    input qubit `q` at the end of the program is output wire `π q`. -/
def elideQ (l : List (QGate n)) : List (QGate n) × Equiv.Perm (Fin n) :=
  elideFrom 1 l

/-- The invariant of the scan: the input followed by `wireMatrix σ` is the output followed
    by the final permutation. -/
theorem qelibListMatrix_mul_wireMatrix_elideFrom (σ : Equiv.Perm (Fin n))
    (l : List (QGate n)) :
    qelibListMatrix l * wireMatrix σ =
      wireMatrix (elideFrom σ l).2 * qelibListMatrix (elideFrom σ l).1 := by
  induction l generalizing σ with
  | nil => simp [elideFrom, qelibListMatrix]
  | cons g l ih =>
    cases g <;> simp only [elideFrom, qelibListMatrix]
    case swap a b =>
      rw [← ih, wireMatrix_mul, wireMatrix_swap, mul_assoc]
    all_goals rw [mul_assoc, qelibMatrix_mul_wireMatrix, ← mul_assoc, ih, mul_assoc]

/-- **The output up to the permutation.** For `(l', π) = elideQ l`, the matrix of `l` is
    the matrix of `l'` followed by the qubit permutation `wireMatrix π`. -/
theorem qelibListMatrix_elideQ (l : List (QGate n)) :
    qelibListMatrix l = wireMatrix (elideQ l).2 * qelibListMatrix (elideQ l).1 := by
  have h := qelibListMatrix_mul_wireMatrix_elideFrom 1 l
  rwa [wireMatrix_one, mul_one] at h

/-! ## Counts -/

/-- Whether a statement is a `swap`. -/
def isSwap : QGate n → Bool
  | .swap _ _ => true
  | _ => false

/-- The number of `swap` statements of a list. -/
def swapCount (l : List (QGate n)) : ℕ := l.countP isSwap

/-- **Counts of kept statements.** A count of statements that relabelling preserves and
    that no `swap` meets is the same on the output; for the `cx` count `cxCount` of the
    pipeline, `p` is `isCx`. -/
theorem countP_elideFrom (p : QGate n → Bool) (hp : ∀ σ g, p (relabelQ σ g) = p g)
    (hs : ∀ a b, p (QGate.swap a b) = false) (σ : Equiv.Perm (Fin n)) (l : List (QGate n)) :
    (elideFrom σ l).1.countP p = l.countP p := by
  induction l generalizing σ with
  | nil => rfl
  | cons g l ih =>
    cases g <;> simp [elideFrom, List.countP_cons, hp, hs, ih]

/-- The output has no `swap` statement. -/
theorem swapCount_elideFrom (σ : Equiv.Perm (Fin n)) (l : List (QGate n)) :
    swapCount (elideFrom σ l).1 = 0 := by
  induction l generalizing σ with
  | nil => rfl
  | cons g l ih =>
    cases g <;> simp only [elideFrom] <;> exact ih _

/-- **The kept counts.** For a count `p` as in `countP_elideFrom` (the `cx` count), the
    output count equals the input count; counting each `swap` as three `cx` besides, the
    pass removes three per `swap` of the input. -/
theorem countP_elideQ (p : QGate n → Bool) (hp : ∀ σ g, p (relabelQ σ g) = p g)
    (hs : ∀ a b, p (QGate.swap a b) = false) (l : List (QGate n)) :
    (elideQ l).1.countP p = l.countP p ∧
      (elideQ l).1.countP p + 3 * swapCount (elideQ l).1 + 3 * swapCount l =
        l.countP p + 3 * swapCount l := by
  have h := countP_elideFrom p hp hs 1 l
  have h0 := swapCount_elideFrom 1 l
  simp only [elideQ] at *
  exact ⟨h, by omega⟩

/-- The scan does not lengthen the list. -/
theorem length_elideFrom_le (σ : Equiv.Perm (Fin n)) (l : List (QGate n)) :
    (elideFrom σ l).1.length ≤ l.length := by
  induction l generalizing σ with
  | nil => simp [elideFrom]
  | cons g l ih =>
    cases g <;> simp only [elideFrom, List.length_cons] <;> grind

/-- **The pass does not lengthen the list.** -/
theorem length_elideQ_le (l : List (QGate n)) : (elideQ l).1.length ≤ l.length :=
  length_elideFrom_le 1 l

/-- **The pass keeps the `cx` count**; each removed `swap` is three `cx` fewer once lowered. -/
theorem cxCount_elideQ (l : List (QGate n)) :
    QrunchFuse.cxCount (elideQ l).1 = QrunchFuse.cxCount l :=
  (countP_elideQ QrunchFuse.isCx (fun _ g => by cases g <;> rfl) (fun _ _ => rfl) l).1

end CatCrypt.Quantum.SwapElide
