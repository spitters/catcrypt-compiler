/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.NotPropagation
public import CatCrypt.Quantum.Optimization.UnitarySound
public import CatCrypt.Quantum.Optimization.PhaseInvariance
public import CatCrypt.Quantum.Optimization.MixedCommute
public import CatCrypt.Quantum.Optimization.DisjointCommute
public import CatCrypt.Quantum.Optimization.MatrixCorrect

/-!
# Real-semantics soundness of the NOT-propagation pass

The pass is stated against the unitary-channel semantics `unitaryDenote`
(ρ ↦ U ρ U†) from `GateUnitarity`.

The pass is `notPropagationPass c = Circuit.ofList (cancelXX (propagateNot
(circuitToList c)))`, so soundness factors through three list transforms:

* `cancelXX_correctU` — removing an adjacent `X(i); X(i)` pair preserves the list
  denotation (`X² = I`, via `embedGate1_mul` + `pauliX_sq` + `embedGate1_one`,
  reusing `GateUnitarity.gateEmbedding_X_sq`).
* `propagateX_correctU` — pushing one `X(q)` rightward through the remaining gate
  list preserves the denotation of `X(q) :: rest`.
* `propagateNot_correctU` — scanning left-to-right and propagating each `X` gate
  preserves the whole-list denotation.

These wire (via `UnitarySound.unitaryDenote_ofList_append` and
`unitaryDenote_circuitToList`) into the top-level
`notPropagationPass_unitaryCorrect : UnitaryCorrectQ notPropagationPass`.

## Reused infrastructure

* `UnitarySound.unitaryDenote_ofList_append`, `unitaryDenote_circuitToList` — the
  list-denotation engine (homomorphic over `++`; flatten/rebuild is the identity).
* `GateUnitarity.gateEmbedding_X_sq`, `denoteGateU_compose`,
  `unitaryChannel_one_eq_qpure` — the `X² = I` channel fact.
* `UnitaryChannel.conjugate_smul_unit`, `unitaryChannel_eq_of_conjugate` — the
  global-phase machinery (available for any X-conjugation rule that holds only up
  to a global phase).

## The `propagateX` commutation branches

The `propagateX` commutation branches — `X` commuting past a *different-qubit*
gate, and the two `X`-through-`CNOT` rules (target-commute and
control-propagate-to-both) — each reduce to a **mixed** `embedGate1 * embedGate2`
(or different-position `embedGate1 * embedGate1`) matrix identity. These are
supplied by `DisjointCommute.embedGate1_disjoint_comm` (single qubit),
`MixedCommute.embedGate1_embedGate2_disjoint_comm` (disjoint `CNOT`/`CZ`), and —
for the two shared-qubit `CNOT`/`X` rules — the bridge lemmas in this file
(`embedGate1_eq_embedGate2_low` / `_high` reduce a single-qubit `X` to a
two-qubit embedding, after which `embedGate2_mul` plus the 4×4 facts
`cnot_embedLow_X_comm` / `cnot_embedHigh_X_ctrl` close them). Everything in this
file — the `X²` cancellation, the commutation branches, the fuel inductions, and
the top-level wiring — is fully proved.

## Main results

* `cancelXX_correctU` — removing adjacent `X(i); X(i)` pairs preserves `unitaryDenote`
  of a gate list.
* `circuitUnitary_propagateX` — `propagateX q rest` realizes the unitary of
  `X(q) :: rest`.
* `circuitUnitary_propagateNot` — one left-to-right NOT-propagation scan preserves the
  unitary of a gate list.
* `embedGate1_eq_embedGate2_low`, `embedGate1_eq_embedGate2_high` — a one-qubit
  embedding on qubit `j` (resp. `i`) equals a two-qubit embedding on `i, j`.
* `notPropagationPass_matrixCorrect` — `notPropagationPass` preserves `circuitUnitary`.
* `notPropagationPass_unitaryCorrect` — `notPropagationPass` is `UnitaryCorrectQ`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.UnitarySound
open CatCrypt.Quantum.Optimization.NotPropagation
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.Optimization.RoutingPerm (circuitUnitary)
open CatCrypt.Quantum.Optimization.MatrixSound

namespace CatCrypt.Quantum.Optimization.NotPropSound

variable {n : ℕ}

/-! ## `X² = I` at the list level -/

/-- An adjacent `X(q); X(q)` pair realizes the identity. -/
theorem circuitUnitary_XX_cancel (q : Fin n) (rest : List (Gate n)) :
    circuitUnitary (Circuit.ofList (Gate.X q :: Gate.X q :: rest))
      = circuitUnitary (Circuit.ofList rest) := by
  have hsq : gateEmbedding_unitaryGroup (Gate.X q) * gateEmbedding_unitaryGroup (Gate.X q)
      = (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
    apply Subtype.ext
    change embedGate1 n q pauliX * embedGate1 n q pauliX = 1
    rw [embedGate1_mul, pauliX_sq, embedGate1_one]
  rw [circuitUnitary_ofList_cons, circuitUnitary_ofList_cons, mul_assoc, hsq, mul_one]

/-- Removing adjacent `X(i); X(i)` pairs preserves the unitary. -/
theorem circuitUnitary_cancelXX :
    ∀ (gs : List (Gate n)) (fuel : ℕ),
      circuitUnitary (Circuit.ofList (cancelXX gs fuel))
        = circuitUnitary (Circuit.ofList gs) := by
  intro gs fuel
  induction fuel generalizing gs with
  | zero => simp only [cancelXX]
  | succ fuel' ih =>
    match gs with
    | [] => simp only [cancelXX]
    | [g] => simp only [cancelXX]
    | g₁ :: g₂ :: rest =>
      have hcons : circuitUnitary (Circuit.ofList (g₁ :: cancelXX (g₂ :: rest) fuel'))
          = circuitUnitary (Circuit.ofList (g₁ :: g₂ :: rest)) :=
        circuitUnitary_ofList_cons_congr g₁ (ih (g₂ :: rest))
      simp only [cancelXX]
      cases hx₁ : isXGate g₁ with
      | none => exact hcons
      | some i =>
        cases hx₂ : isXGate g₂ with
        | none => exact hcons
        | some j =>
          by_cases hij : i = j
          · subst hij
            simp only [decide_true, ite_true]
            obtain rfl : g₁ = Gate.X i := by
              cases g₁ <;> simp_all [isXGate]
            obtain rfl : g₂ = Gate.X i := by
              cases g₂ <;> simp_all [isXGate]
            rw [ih rest, circuitUnitary_XX_cancel]
          · simp only [decide_eq_true_eq, hij, ite_false]
            exact hcons

/-- An adjacent `X(q); X(q)` pair cancels under the real unitary semantics:
`unitaryDenote (ofList (X q :: X q :: rest)) = unitaryDenote (ofList rest)`. -/
theorem unitaryDenote_XX_cancel (q : Fin n) (rest : List (Gate n)) :
    unitaryDenote (Circuit.ofList (Gate.X q :: Gate.X q :: rest))
      = unitaryDenote (Circuit.ofList rest) :=
  unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_XX_cancel q rest)

/-- Cons of a gate onto an `ofList` denotation unfolds to a `qbind`. -/
theorem unitaryDenote_ofList_cons (g : Gate n) (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (g :: gs))
      = QComp.qbind (denoteGateU g) (fun _ => unitaryDenote (Circuit.ofList gs)) :=
  rfl

/-! ## `cancelXX` preserves the real semantics -/

/-- Removing adjacent `X(i); X(i)` pairs preserves `unitaryDenote`. -/
theorem cancelXX_correctU :
    ∀ (gs : List (Gate n)) (fuel : ℕ),
      unitaryDenote (Circuit.ofList (cancelXX gs fuel))
        = unitaryDenote (Circuit.ofList gs) :=
  fun gs fuel => unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_cancelXX gs fuel)

/-! ## Mixed `embedGate1` / `embedGate2` infrastructure for shared-qubit X-CNOT

The shared-qubit `X`-through-`CNOT` rules need matrix identities relating the
single-qubit embedding `embedGate1 n t pauliX` with the two-qubit embedding
`embedGate2 n c t cnot` when the X qubit *coincides* with a `CNOT` qubit. We
bridge these by exhibiting `embedGate1 n j G` as a two-qubit embedding on the
pair `(i, j)` with the gate matrix acting as `G` on the low qubit `j` and the
identity on the high qubit `i` (`embedLow`). Then all shared identities reduce
to `embedGate2_mul` plus 4×4 matrix arithmetic. -/

/-- The 4×4 matrix acting as the 2×2 gate `G` on the **low** qubit (index `j`
    in `embedGate2 i j`) and as the identity on the **high** qubit (index `i`).
    With the `idx4` convention (qubit `i` high bit, qubit `j` low bit), the
    `(a,b)` entry is `G (a%2) (b%2)` when `a/2 = b/2`, else `0`. -/
def embedLow (G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun a b =>
    if a.val / 2 = b.val / 2 then
      G ⟨a.val % 2, Nat.mod_lt _ (by omega)⟩ ⟨b.val % 2, Nat.mod_lt _ (by omega)⟩
    else 0

/-- `idx4 v / 2 = gbit i v` (the high bit of the 2-qubit subindex is qubit `i`). -/
theorem idx4_div_two (i j : Fin n) (v : ℕ) :
    (idx4 n i j v).val / 2 = (gbit n i v).val := by
  simp only [idx4]
  have hj : (gbit n j v).val < 2 := (gbit n j v).isLt
  omega

/-- `idx4 v % 2 = gbit j v` (the low bit of the 2-qubit subindex is qubit `j`). -/
theorem idx4_mod_two (i j : Fin n) (v : ℕ) :
    (idx4 n i j v).val % 2 = (gbit n j v).val := by
  simp only [idx4]
  have hj : (gbit n j v).val < 2 := (gbit n j v).isLt
  omega

/-- **Bridge lemma.** A single-qubit gate `G` on qubit `j` equals the two-qubit
    embedding on `(i, j)` of `embedLow G` (which is `I` on the high qubit `i`
    and `G` on the low qubit `j`), for any `i ≠ j`. -/
theorem embedGate1_eq_embedGate2_low {i j : Fin n} (hij : i ≠ j)
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n j G = embedGate2 n i j (embedLow G) hij := by
  ext r c
  rw [embedGate1_apply, embedGate2_apply hij]
  by_cases hM : Match n j r.val c.val
  · -- `Match n j` ⇒ agree off pos j ⇒ in particular `Match2` and same high bit.
    have hM2 : Match2 n i j r.val c.val := fun p _ hpj => hM p hpj
    have hgi : gbit n i r.val = gbit n i c.val :=
      gbit_eq_of_match hij hM
    rw [ite_eq_left hM, ite_eq_left hM2]
    simp only [embedLow, Matrix.of_apply, idx4_div_two, idx4_mod_two]
    rw [ite_eq_left (by rw [hgi])]
  · rw [ite_eq_right hM]
    by_cases hM2 : Match2 n i j r.val c.val
    · rw [ite_eq_left hM2]
      simp only [embedLow, Matrix.of_apply, idx4_div_two]
      rw [ite_eq_right]
      -- if high bits agreed then `Match n j` would hold (only pos j can differ).
      intro hgi
      apply hM
      intro p hpj
      by_cases hpi : p = pos n i
      · subst hpi
        have hb : (gbit n i r.val).val = (gbit n i c.val).val := hgi
        rw [gbit_eq_testBit, gbit_eq_testBit] at hb
        cases hr : r.val.testBit (pos n i) <;> cases hc : c.val.testBit (pos n i) <;>
          simp_all
      · exact hM2 p hpi hpj
    · rw [ite_eq_right hM2]

/-- The 4×4 matrix acting as the 2×2 gate `G` on the **high** qubit (index `i`
    in `embedGate2 i j`) and as the identity on the **low** qubit (index `j`).
    The `(a,b)` entry is `G (a/2) (b/2)` when `a%2 = b%2`, else `0`. -/
def embedHigh (G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun a b =>
    if a.val % 2 = b.val % 2 then
      G ⟨a.val / 2, by omega⟩ ⟨b.val / 2, by omega⟩
    else 0

/-- **Bridge lemma (high qubit).** A single-qubit gate `G` on qubit `i` equals
    the two-qubit embedding on `(i, j)` of `embedHigh G` (which is `G` on the
    high qubit `i` and `I` on the low qubit `j`), for any `i ≠ j`. -/
theorem embedGate1_eq_embedGate2_high {i j : Fin n} (hij : i ≠ j)
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i G = embedGate2 n i j (embedHigh G) hij := by
  ext r c
  rw [embedGate1_apply, embedGate2_apply hij]
  by_cases hM : Match n i r.val c.val
  · have hM2 : Match2 n i j r.val c.val := fun p hpi _ => hM p hpi
    have hgj : gbit n j r.val = gbit n j c.val :=
      gbit_eq_of_match (Ne.symm hij) hM
    rw [ite_eq_left hM, ite_eq_left hM2]
    simp only [embedHigh, Matrix.of_apply, idx4_div_two, idx4_mod_two]
    rw [ite_eq_left (by rw [hgj])]
  · rw [ite_eq_right hM]
    by_cases hM2 : Match2 n i j r.val c.val
    · rw [ite_eq_left hM2]
      simp only [embedHigh, Matrix.of_apply, idx4_mod_two]
      rw [ite_eq_right]
      intro hgj
      apply hM
      intro p hpi
      by_cases hpj : p = pos n j
      · subst hpj
        have hb : (gbit n j r.val).val = (gbit n j c.val).val := hgj
        rw [gbit_eq_testBit, gbit_eq_testBit] at hb
        cases hr : r.val.testBit (pos n j) <;> cases hc : c.val.testBit (pos n j) <;>
          simp_all
      · exact hM2 p hpi hpj
    · rw [ite_eq_right hM2]

/-! ### 4×4 `CNOT`/`X` algebraic identities (control = high bit, target = low bit) -/

/-- `CNOT` commutes with `X` on its **target** (low) qubit: `cnot · (I⊗X) = (I⊗X) · cnot`. -/
theorem cnot_embedLow_X_comm :
    Programs.Qubit.cnot * embedLow pauliX = embedLow pauliX * Programs.Qubit.cnot := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Programs.Qubit.cnot, embedLow, pauliX, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.of_apply]

/-- `X` on the **control** (high) qubit pushes through `CNOT` to both qubits:
    `cnot · (X⊗I) = (I⊗X) · (X⊗I) · cnot`. -/
theorem cnot_embedHigh_X_ctrl :
    Programs.Qubit.cnot * embedHigh pauliX
      = embedLow pauliX * embedHigh pauliX * Programs.Qubit.cnot := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Programs.Qubit.cnot, embedLow, embedHigh, pauliX, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.of_apply]

/-! ### Lifting the `CNOT`/`X` identities to the full `embedGate1`/`embedGate2` level -/

/-- `gateEmbedding (X q) = embedGate1 n q pauliX`. -/
theorem gateEmbedding_X (q : Fin n) :
    gateEmbedding (Gate.X q) = embedGate1 n q pauliX := rfl

/-- A degenerate `CNOT(c,c)` embeds as the identity. -/
theorem gateEmbedding_CNOT_self (c : Fin n) :
    gateEmbedding (Gate.CNOT c c) = 1 := by simp only [gateEmbedding, dite_eq_left]

/-- A degenerate `CZ(i,i)` embeds as the identity. -/
theorem gateEmbedding_CZ_self (i : Fin n) :
    gateEmbedding (Gate.CZ i i) = 1 := by simp only [gateEmbedding, dite_eq_left]

/-- **Target-commute** at the embedding level: `X` on the target qubit `t`
    commutes with `CNOT(c,t)`. -/
theorem embedGate1_X_cnot_target_comm {c t : Fin n} (hct : c ≠ t) :
    embedGate1 n t pauliX * embedGate2 n c t Programs.Qubit.cnot hct
      = embedGate2 n c t Programs.Qubit.cnot hct * embedGate1 n t pauliX := by
  rw [embedGate1_eq_embedGate2_low hct pauliX, embedGate2_mul, embedGate2_mul,
    cnot_embedLow_X_comm]

/-- **Control-propagate** at the embedding level: `X` on the control qubit `c`
    pushes through `CNOT(c,t)` and becomes `X(c)·X(t)` afterwards. With the
    matrix-product convention (rightmost applied first), `X(c)` applied first
    then `CNOT` equals `CNOT` first then `X(t)·X(c)`. -/
theorem embedGate2_cnot_X_control {c t : Fin n} (hct : c ≠ t) :
    embedGate2 n c t Programs.Qubit.cnot hct * embedGate1 n c pauliX
      = embedGate1 n t pauliX * embedGate1 n c pauliX
        * embedGate2 n c t Programs.Qubit.cnot hct := by
  rw [embedGate1_eq_embedGate2_high hct pauliX, embedGate1_eq_embedGate2_low hct pauliX,
    embedGate2_mul, embedGate2_mul, embedGate2_mul, cnot_embedHigh_X_ctrl]

/-! ## `propagateX` preserves the real semantics

`propagateX q rest` pushes a single `X(q)` rightward through `rest`. Apart from
the `X(q); X(q) = I` cancellation (`unitaryDenote_XX_cancel`, fully proved), every
branch *commutes* `X(q)` past the head gate `g`:

* a different-qubit gate (`X(j)`, `H/Y/Z/S/T/Tdg/Rz/CZ` on disjoint qubits) —
  needs a **different-position** `embedGate1 * embedGate1` (or `embedGate1 *
  embedGate2`) commutation identity;
* `X(t); CNOT(c,t) = CNOT(c,t); X(t)` — needs a **mixed** `embedGate1 * embedGate2`
  identity (the target-commute rule);
* `X(c); CNOT(c,t) = CNOT(c,t); X(c); X(t)` — the control rule, which additionally
  inserts an `X(t)`.

The disjoint commutations come from `DisjointCommute.embedGate1_disjoint_comm`
(single qubit), `MixedCommute.embedGate1_embedGate2_disjoint_comm` (disjoint
`CNOT`/`CZ`); the two shared-qubit `CNOT`/`X` rules come from the bridge lemmas
above (`embedGate1_X_cnot_target_comm`, `embedGate2_cnot_X_control`). -/

/-- **Head-commutation under the unitary semantics.** If two gates commute at the
    matrix level, swapping the order of the leading two gates preserves the
    `qbind` denotation of the rest. -/
theorem commuteHeadU (g₁ g₂ : Gate n) (K : QComp (2 ^ n) Unit)
    (hcomm : gateEmbedding g₂ * gateEmbedding g₁
           = gateEmbedding g₁ * gateEmbedding g₂) :
    QComp.qbind (denoteGateU g₁) (fun _ => QComp.qbind (denoteGateU g₂) (fun _ => K))
      = QComp.qbind (denoteGateU g₂) (fun _ => QComp.qbind (denoteGateU g₁) (fun _ => K)) := by
  have hug : gateEmbedding_unitaryGroup g₂ * gateEmbedding_unitaryGroup g₁
           = gateEmbedding_unitaryGroup g₁ * gateEmbedding_unitaryGroup g₂ :=
    Subtype.ext hcomm
  rw [← QComp.qbind_assoc, ← QComp.qbind_assoc]
  have h1 : (fun (_ : Unit) => denoteGateU (n := n) g₂) = (fun () => denoteGateU g₂) := rfl
  have h2 : (fun (_ : Unit) => denoteGateU (n := n) g₁) = (fun () => denoteGateU g₁) := rfl
  rw [h1, denoteGateU_compose, h2, denoteGateU_compose, hug]

/-- Fold a two-gate `qbind` prefix into a single `unitaryChannel`. -/
theorem qbind2_fold (a b : Gate n) (K : QComp (2 ^ n) Unit) :
    QComp.qbind (denoteGateU a) (fun _ => QComp.qbind (denoteGateU b) (fun _ => K))
      = QComp.qbind (unitaryChannel (gateEmbedding_unitaryGroup b
          * gateEmbedding_unitaryGroup a)) (fun _ => K) := by
  rw [← QComp.qbind_assoc]
  have h : (fun (_ : Unit) => denoteGateU (n := n) b) = (fun () => denoteGateU b) := rfl
  rw [h, denoteGateU_compose]

/-- Fold a three-gate `qbind` prefix into a single `unitaryChannel`. -/
theorem qbind3_fold (a b c : Gate n) (K : QComp (2 ^ n) Unit) :
    QComp.qbind (denoteGateU a) (fun _ => QComp.qbind (denoteGateU b)
        (fun _ => QComp.qbind (denoteGateU c) (fun _ => K)))
      = QComp.qbind (unitaryChannel (gateEmbedding_unitaryGroup c
          * gateEmbedding_unitaryGroup b * gateEmbedding_unitaryGroup a)) (fun _ => K) := by
  rw [qbind2_fold b c, ← QComp.qbind_assoc]
  have h : (fun (_ : Unit) => unitaryChannel (gateEmbedding_unitaryGroup (n := n) c
            * gateEmbedding_unitaryGroup b))
        = (fun () => unitaryChannel (gateEmbedding_unitaryGroup c
            * gateEmbedding_unitaryGroup b)) := rfl
  rw [show denoteGateU a = unitaryChannel (gateEmbedding_unitaryGroup a) from rfl,
    h, unitaryChannel_compose, mul_assoc]

/-- **Single-qubit disjoint commutation** at the `gateEmbedding` level:
    `X(q)` commutes with any single-qubit gate `g` on a different qubit `j ≠ q`. -/
theorem gateEmbedding_X_single_disjoint {q j : Fin n} (hqj : q ≠ j)
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n j G * embedGate1 n q pauliX
      = embedGate1 n q pauliX * embedGate1 n j G :=
  embedGate1_disjoint_comm (Ne.symm hqj) G pauliX

/-- The shared disjoint-single-qubit propagation step, factored over the gate's
    `2×2` matrix `G`. Given `q ≠ j` and `gateEmbedding g = embedGate1 n j G`,
    `propagateX q (g :: gs)` denotes the same channel as `X(q) :: g :: gs`. -/
theorem gateCommuteU_single {q j : Fin n} {fuel' : ℕ} {gs : List (Gate n)}
    {G : Matrix (Fin 2) (Fin 2) ℂ} (g : Gate n) (hqj : q ≠ j)
    (ih : ∀ rest, unitaryDenote (Circuit.ofList (propagateX q rest fuel'))
        = unitaryDenote (Circuit.ofList (Gate.X q :: rest)))
    (hg : gateEmbedding g = embedGate1 n j G)
    (hbranch : propagateX q (g :: gs) (fuel' + 1) = g :: propagateX q gs fuel') :
    unitaryDenote (Circuit.ofList (propagateX q (g :: gs) (fuel' + 1)))
      = unitaryDenote (Circuit.ofList (Gate.X q :: g :: gs)) := by
  rw [hbranch, unitaryDenote_ofList_cons, ih gs, unitaryDenote_ofList_cons,
    unitaryDenote_ofList_cons]
  refine commuteHeadU g (Gate.X q) _ ?_
  rw [hg, gateEmbedding_X]
  exact (gateEmbedding_X_single_disjoint hqj G).symm

/-- The step of `propagateX` past a single-qubit gate on another qubit. -/
theorem circuitUnitary_propagateX_single {q j : Fin n} {fuel' : ℕ} {gs : List (Gate n)}
    {G : Matrix (Fin 2) (Fin 2) ℂ} (g : Gate n) (hqj : q ≠ j)
    (ih : ∀ rest, circuitUnitary (Circuit.ofList (propagateX q rest fuel'))
        = circuitUnitary (Circuit.ofList (Gate.X q :: rest)))
    (hg : gateEmbedding g = embedGate1 n j G)
    (hbranch : propagateX q (g :: gs) (fuel' + 1) = g :: propagateX q gs fuel') :
    circuitUnitary (Circuit.ofList (propagateX q (g :: gs) (fuel' + 1)))
      = circuitUnitary (Circuit.ofList (Gate.X q :: g :: gs)) := by
  rw [hbranch]
  refine circuitUnitary_cons_swap_of (ih gs) ?_
  rw [hg, gateEmbedding_X]
  exact (gateEmbedding_X_single_disjoint hqj G).symm

/-- `propagateX q rest` realizes the unitary of `X(q) :: rest`. -/
theorem circuitUnitary_propagateX (q : Fin n) :
    ∀ (rest : List (Gate n)) (fuel : ℕ),
      circuitUnitary (Circuit.ofList (propagateX q rest fuel))
        = circuitUnitary (Circuit.ofList (Gate.X q :: rest)) := by
  intro rest fuel
  induction fuel generalizing rest with
  | zero => simp only [propagateX]
  | succ fuel' ih =>
    match rest with
    | [] => rfl
    | g :: gs =>
      cases g with
      | X j =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.X q :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, decide_true, ite_true]
          rw [circuitUnitary_XX_cancel]
        · change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.X j :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, decide_eq_true_eq, hqj, ite_false]
          refine circuitUnitary_cons_swap_of (ih gs) ?_
          rw [gateEmbedding_X, gateEmbedding_X]
          exact (gateEmbedding_X_single_disjoint hqj pauliX).symm
      | CNOT c t =>
        by_cases hct : c = t
        · subst hct
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.CNOT c c :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT]
          by_cases hqt : q = c
          · subst hqt
            simp only [decide_true, ite_true]
            refine circuitUnitary_cons_swap_of (ih gs) ?_
            rw [gateEmbedding_CNOT_self, gateEmbedding_X, Matrix.one_mul, Matrix.mul_one]
          · simp only [decide_eq_true_eq, hqt, ite_false]
            refine circuitUnitary_cons_swap_of (ih gs) ?_
            rw [gateEmbedding_CNOT_self, gateEmbedding_X, Matrix.one_mul, Matrix.mul_one]
        · change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.CNOT c t :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT]
          by_cases hqt : q = t
          · subst hqt
            simp only [decide_true, ite_true]
            refine circuitUnitary_cons_swap_of (ih gs) ?_
            simp only [gateEmbedding, dite_eq_right hct]
            exact embedGate1_X_cnot_target_comm hct
          · by_cases hqc : q = c
            · subst hqc
              simp only [decide_eq_true_eq, hqt, ite_false, decide_true, ite_true]
              rw [circuitUnitary_ofList_cons, ih (Gate.X t :: gs)]
              simp only [circuitUnitary_ofList_cons, mul_assoc]
              congr 1
              apply Subtype.ext
              change gateEmbedding (Gate.X t) *
                  (gateEmbedding (Gate.X q) * gateEmbedding (Gate.CNOT q t))
                = gateEmbedding (Gate.CNOT q t) * gateEmbedding (Gate.X q)
              rw [← mul_assoc]
              simp only [gateEmbedding, dite_eq_right hct]
              exact (embedGate2_cnot_X_control hct).symm
            · simp only [decide_eq_true_eq, hqt, ite_false, hqc]
              refine circuitUnitary_cons_swap_of (ih gs) ?_
              simp only [gateEmbedding, dite_eq_right hct]
              exact embedGate1_embedGate2_disjoint_comm hqc hqt hct _ _
      | H j =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.H q :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := hadamard) (Gate.H j) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | Y j =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.Y q :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := pauliY) (Gate.Y j) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | Z j =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.Z q :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := pauliZ) (Gate.Z j) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | S j =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.S q :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := phaseS) (Gate.S j) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | T j =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.T q :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := tGate) (Gate.T j) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | Tdg j =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.Tdg q :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := tDaggerGate) (Gate.Tdg j) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | Rz j θ =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.Rz q θ :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := rzGate θ) (Gate.Rz j θ) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | RzQ j a =>
        by_cases hqj : q = j
        · subst hqj
          change circuitUnitary
            (Circuit.ofList (propagateX q (Gate.RzQ q a :: gs) (fuel' + 1))) = _
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ite_false]
        · refine circuitUnitary_propagateX_single (G := rzGate (PiLin.toReal a))
            (Gate.RzQ j a) hqj ih rfl ?_
          simp only [propagateX, isXGate, isCNOT, List.all_cons, List.all_nil,
            Bool.and_true, decide_eq_true_eq, ite_eq_left hqj]
      | CZ i j =>
        change circuitUnitary
          (Circuit.ofList (propagateX q (Gate.CZ i j :: gs) (fuel' + 1))) = _
        simp only [propagateX, isXGate, isCNOT]
        by_cases hqi : q = i
        · subst hqi
          simp only [List.all_cons, List.all_nil, Bool.and_true, ne_eq,
            not_true_eq_false, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
        · by_cases hqj : q = j
          · subst hqj
            simp only [List.all_cons, List.all_nil, Bool.and_true, ne_eq, hqi,
              not_false_eq_true, decide_true, not_true_eq_false, decide_false,
              Bool.and_false, Bool.false_eq_true, ite_false]
          · by_cases hij : i = j
            · subst hij
              simp only [List.all_cons, List.all_nil, Bool.and_true, ne_eq, hqi,
                not_false_eq_true, decide_true, ite_true]
              refine circuitUnitary_cons_swap_of (ih gs) ?_
              rw [gateEmbedding_CZ_self, gateEmbedding_X, Matrix.one_mul, Matrix.mul_one]
            · simp only [List.all_cons, List.all_nil, Bool.and_true, ne_eq, hqi,
                not_false_eq_true, decide_true, hqj, ite_true]
              refine circuitUnitary_cons_swap_of (ih gs) ?_
              simp only [gateEmbedding, dite_eq_right hij]
              exact embedGate1_embedGate2_disjoint_comm hqi hqj hij _ _

/-- One left-to-right NOT-propagation scan preserves the unitary. -/
theorem circuitUnitary_propagateNot :
    ∀ (gs : List (Gate n)) (fuel : ℕ),
      circuitUnitary (Circuit.ofList (propagateNot gs fuel))
        = circuitUnitary (Circuit.ofList gs) := by
  intro gs fuel
  induction fuel generalizing gs with
  | zero => simp only [propagateNot]
  | succ fuel' ih =>
    match gs with
    | [] => simp only [propagateNot]
    | g :: rest =>
      cases hx : isXGate g with
      | none =>
        simp only [propagateNot, hx]
        exact circuitUnitary_ofList_cons_congr g (ih rest)
      | some q =>
        obtain rfl : g = Gate.X q := by cases g <;> simp_all [isXGate]
        simp only [propagateNot, isXGate]
        rw [circuitUnitary_propagateX]
        exact circuitUnitary_ofList_cons_congr _ (ih rest)

/-- `propagateX q rest` pushes a single `X(q)` through `rest` while preserving the
real unitary semantics: it denotes the same channel as `X(q) :: rest`.

Every branch either cancels (`X(q); X(q) = I`), commutes `X(q)` past a
disjoint gate, threads it through a `CNOT` (target-commute / control-propagate),
or — for a single-qubit gate sharing qubit `q` — leaves the `X` in place. -/
theorem propagateX_correctU (q : Fin n) :
    ∀ (rest : List (Gate n)) (fuel : ℕ),
      unitaryDenote (Circuit.ofList (propagateX q rest fuel))
        = unitaryDenote (Circuit.ofList (Gate.X q :: rest)) :=
  fun rest fuel => unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_propagateX q rest fuel)

/-- **Commutation primitive.** Pushing the leading `X(q)` past a non-`X`-cancelling
    head gate `g` preserves the real unitary semantics. A direct consequence of
    the inductive `propagateX_correctU`: every branch reduces to a disjoint-position
    `embedGate1 * embedGate1` / `embedGate1 * embedGate2` commutation, or one of the
    two shared-qubit `CNOT`/`X` matrix identities. -/
theorem propagateX_commute_stepU (q : Fin n) (g : Gate n) (gs : List (Gate n))
    (fuel' : ℕ)
    (_ih : unitaryDenote (Circuit.ofList (propagateX q gs fuel'))
        = unitaryDenote (Circuit.ofList (Gate.X q :: gs))) :
    unitaryDenote (Circuit.ofList (propagateX q (g :: gs) (fuel' + 1)))
      = unitaryDenote (Circuit.ofList (Gate.X q :: g :: gs)) :=
  propagateX_correctU q (g :: gs) (fuel' + 1)

/-! ## `propagateNot` preserves the real semantics -/

/-- One left-to-right NOT-propagation scan preserves `unitaryDenote`. -/
theorem propagateNot_correctU :
    ∀ (gs : List (Gate n)) (fuel : ℕ),
      unitaryDenote (Circuit.ofList (propagateNot gs fuel))
        = unitaryDenote (Circuit.ofList gs) :=
  fun gs fuel => unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_propagateNot gs fuel)

/-! ## Top-level soundness of the NOT-propagation pass -/

/-- `NotPropagation.circuitToList` preserves `circuitUnitary`. -/
theorem circuitUnitary_ofList_circuitToList_notProp (c : Circuit n) :
    circuitUnitary (Circuit.ofList (NotPropagation.circuitToList c)) = circuitUnitary c :=
  circuitUnitary_ofList_flatten _ rfl (fun _ _ => rfl) (fun _ _ => rfl) c

/-- Flattening a circuit with `NotPropagation.circuitToList` and rebuilding
preserves `unitaryDenote` (the local `circuitToList` is definitionally the same
as `TemplateMatching.circuitToList`, but distinct as a name). -/
theorem unitaryDenote_circuitToList' (c : Circuit n) :
    unitaryDenote (Circuit.ofList (NotPropagation.circuitToList c)) = unitaryDenote c :=
  unitaryDenote_eq_of_circuitUnitary_eq (circuitUnitary_ofList_circuitToList_notProp c)

/-- `notPropagationPass` preserves `circuitUnitary`. -/
theorem notPropagationPass_matrixCorrect :
    MatrixCorrect (notPropagationPass : Circuit n → Circuit n) := by
  intro c
  simp only [notPropagationPass]
  rw [circuitUnitary_cancelXX, circuitUnitary_propagateNot,
    circuitUnitary_ofList_circuitToList_notProp]

/-- **The NOT-propagation pass preserves the unitary semantics.**
`notPropagationPass c` denotes the same unitary channel `ρ ↦ U ρ U†` as `c`. -/
theorem notPropagationPass_unitaryDenote (c : Circuit n) :
    unitaryDenote (notPropagationPass c) = unitaryDenote c :=
  unitaryDenote_eq_of_circuitUnitary_eq (notPropagationPass_matrixCorrect c)

/-- The NOT-propagation pass is unitary-correct (`UnitaryCorrectQ`). -/
theorem notPropagationPass_unitaryCorrect :
    UnitaryCorrectQ (notPropagationPass : Circuit n → Circuit n) :=
  notPropagationPass_matrixCorrect.unitaryCorrectQ

end CatCrypt.Quantum.Optimization.NotPropSound
