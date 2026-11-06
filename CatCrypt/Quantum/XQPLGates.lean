/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QPL
public import CatCrypt.Quantum.ControlledGates
public import CatCrypt.Quantum.QFT.Inverse

/-!
# XQPL operations with exact gate lists: lowering, adjoint, control and conjugation

An operation set `Ops` with an `OpGates Ops n` instance gives each operation an exact gate
list whose circuit has the denotation of the operation. Such programs lower to QPL by
`XQPL.lowerXQPL`, which replaces each operation by its gate list and preserves the
denotation (`XQPL.lowerXQPL_denote`). Operation sets combine by `⊕`.

A program of the measurement-free fragment (`XQPL.isMeasFree`) has an exact gate list
`XQPL.toGates` and a return value `XQPL.retVal`; its denotation is the channel of the
circuit of that list followed by the return (`XQPL.denote_eq_toGates`), and its exact
unitary is `XQPL.unitary p h = QFT.listMatrix (p.toGates h)` (head gate applied first).
The adjoint and the controlled version of a measurement-free program are defined on the
exact gate list, not on the denotation, which is a channel and determines the unitary
only up to a global phase. Both return `XQPL.ofGates l`, a measurement-free program again.

## Main definitions

* `OpGateList Ops n` -- a gate list for each operation, without denotation
* `OpGates Ops n` -- an exact gate list for each operation, denoting the operation
* `XQPL.applyGates`, `XQPL.ofGates` -- a gate list in front of a program; a gate list as
  a program
* `XQPL.lowerXQPL` -- lowering to QPL through the gate lists of the operations
* `XQPL.toGates`, `XQPL.retVal`, `XQPL.unitary` -- the exact gate list, the return value
  and the exact unitary of a measurement-free program
* `XQPL.adjoint` -- the inverse gate list (`QFT.invGates`)
* `XQPL.controlled`, `XQPL.mcontrolledNoAnc` -- control on one qubit (`ctrlList`) and on a
  list of qubits without ancillae (`mctrlGates`)
* `conjugate U V` -- the conjugation `U ++ V ++ invGates U`

## Main results

* `XQPL.lowerXQPL_denote` -- the lowering preserves the denotation
* `XQPL.denote_eq_toGates`, `XQPL.toGates_ofGates`
* `XQPL.unitary_adjoint`, `XQPL.denote_adjoint`
* `XQPL.unitary_controlled`, `XQPL.unitary_mcontrolledNoAnc`
* `listMatrix_conjugate`, `listMatrix_conjugate_ctrl` -- the controlled conjugation
  controls only the middle list
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.QPL

open scoped Matrix
open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Optimization
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append
  invGate invGates listMatrix_invGates)

variable {n : ℕ}

/-! ## Operations with exact gate lists -/

/-- A gate list for each operation of `Ops`. It carries no denotation, so the gate lists of
    programs are computable. -/
class OpGateList (Ops : Type) (n : ℕ) where
  /-- The gate list of an operation. -/
  gates : Ops → List (Gate n)

/-- An exact gate list for each operation of `Ops`, whose circuit has the denotation of
    the operation. -/
class OpGates (Ops : Type) (n : ℕ) [OpDenote Ops n] extends OpGateList Ops n where
  /-- An operation denotes the circuit of its gate list. -/
  denote_eq : ∀ op, OpDenote.denote op = GateUnitarity.unitaryDenote (Circuit.ofList (gates op))

/- The gate lists of a concrete operation set resolve to its `OpGateList` instance, which is
computable, before the projection from `OpGates`, which carries the denotation. -/
attribute [instance 100] OpGates.toOpGateList

/-- The operations of `A ⊕ B` denote as the operations of `A` and of `B`. -/
instance instOpDenoteSum {A B : Type} [OpDenote A n] [OpDenote B n] : OpDenote (A ⊕ B) n where
  denote := Sum.elim OpDenote.denote OpDenote.denote

/-- The gate lists of `A ⊕ B` are those of `A` and of `B`. -/
instance instOpGateListSum {A B : Type} [OpGateList A n] [OpGateList B n] :
    OpGateList (A ⊕ B) n where
  gates := Sum.elim OpGateList.gates OpGateList.gates

/-- The exact gate lists of `A ⊕ B` are those of `A` and of `B`. -/
instance instOpGatesSum {A B : Type} [OpDenote A n] [OpDenote B n] [OpGates A n]
    [OpGates B n] : OpGates (A ⊕ B) n where
  toOpGateList := instOpGateListSum
  denote_eq
    | .inl a => OpGates.denote_eq a
    | .inr b => OpGates.denote_eq b

namespace XQPL

variable {Ops : Type} {α : Type}

/-! ## Gate lists as programs -/

/-- Apply a list of gates in sequence, then continue with `k`. -/
def applyGates (gates : List (Gate n)) (k : XQPL Ops n α) : XQPL Ops n α :=
  gates.foldr (fun g acc => .gate g acc) k

/-- A gate list as a program returning `()`. -/
def ofGates (l : List (Gate n)) : XQPL Ops n Unit := applyGates l (.ret ())

theorem applyGates_append (l₁ l₂ : List (Gate n)) (k : XQPL Ops n α) :
    applyGates (l₁ ++ l₂) k = applyGates l₁ (applyGates l₂ k) := by
  simp only [applyGates, List.foldr_append]

/-- A gate list in front of a program denotes the circuit of the list followed by the
    program. -/
theorem denote_applyGates [OpDenote Ops n] (l : List (Gate n)) (k : XQPL Ops n α) :
    (applyGates l k).denote =
      QComp.qbind (GateUnitarity.unitaryDenote (Circuit.ofList l)) (fun _ => k.denote) := by
  induction l with
  | nil =>
    simp only [applyGates, List.foldr_nil, Circuit.ofList, GateUnitarity.unitaryDenote,
      QComp.qpure_qbind]
  | cons g l ih =>
    rw [Circuit.ofList, GateUnitarity.unitaryDenote, QComp.qbind_assoc, ← ih]
    rfl

theorem isMeasFree_applyGates (l : List (Gate n)) {k : XQPL Ops n α} (hk : k.isMeasFree) :
    (applyGates l k).isMeasFree := by
  induction l with
  | nil => exact hk
  | cons g l ih => exact ih

theorem isMeasFree_ofGates (l : List (Gate n)) : (ofGates l : XQPL Ops n Unit).isMeasFree :=
  isMeasFree_applyGates l trivial

/-! ## Lowering to QPL -/

/-- Lower a program to QPL, replacing each operation by its gate list. -/
def lowerXQPL [OpDenote Ops n] [OpGates Ops n] : XQPL Ops n α → QPL n α
  | .ret a => .ret a
  | .gate g k => .gate g (lowerXQPL k)
  | .meas i kt kf => .meas i (lowerXQPL kt) (lowerXQPL kf)
  | .custom op k => applyGates (OpGateList.gates op) (lowerXQPL k)
  | .fail => .fail

/-- **Soundness of the lowering.** A program and its lowering to QPL have the same
    denotation. -/
theorem lowerXQPL_denote [OpDenote Ops n] [OpGates Ops n] (p : XQPL Ops n α) :
    (lowerXQPL p).denote = p.denote := by
  induction p with
  | ret a => rfl
  | gate g k ih => simp only [lowerXQPL, XQPL.denote, ih]
  | meas i kt kf iht ihf => simp only [lowerXQPL, XQPL.denote, iht, ihf]
  | custom op k ih =>
    rw [lowerXQPL, denote_applyGates, ih, XQPL.denote, OpGates.denote_eq]
  | fail => rfl

/-! ## The measurement-free fragment -/

/-- Decidability of measurement-freeness, by recursion on the program. -/
def decIsMeasFree : (p : XQPL Ops n α) → Decidable p.isMeasFree
  | .ret _ => isTrue trivial
  | .gate _ k => decIsMeasFree k
  | .meas _ _ _ => isFalse id
  | .custom _ k => decIsMeasFree k
  | .fail => isFalse id

instance : DecidablePred (XQPL.isMeasFree (Ops := Ops) (n := n) (α := α)) := decIsMeasFree

/-- The exact gate list of a measurement-free program: its gates and the gate lists of
    its operations, in program order. -/
def toGates [OpGateList Ops n] :
    (p : XQPL Ops n α) → p.isMeasFree → List (Gate n)
  | .ret _, _ => []
  | .gate g k, h => g :: k.toGates h
  | .meas _ _ _, h => False.elim h
  | .custom op k, h => OpGateList.gates op ++ k.toGates h
  | .fail, h => False.elim h

/-- The return value of a measurement-free program. -/
def retVal : (p : XQPL Ops n α) → p.isMeasFree → α
  | .ret a, _ => a
  | .gate _ k, h => k.retVal h
  | .meas _ _ _, h => False.elim h
  | .custom _ k, h => k.retVal h
  | .fail, h => False.elim h

/-- The exact unitary of a measurement-free program: the matrix of its gate list. -/
def unitary [OpGateList Ops n] (p : XQPL Ops n α) (h : p.isMeasFree) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  listMatrix (p.toGates h)

theorem denote_eq_applyGates_toGates [OpDenote Ops n] [OpGates Ops n] (p : XQPL Ops n α)
    (h : p.isMeasFree) :
    p.denote = (applyGates (p.toGates h) (.ret (p.retVal h)) : XQPL Ops n α).denote := by
  induction p with
  | ret a => rfl
  | gate g k ih =>
    simp only [XQPL.denote, toGates, retVal, applyGates, List.foldr_cons]
    rw [ih h]; rfl
  | meas i kt kf _ _ => exact False.elim h
  | custom op k ih =>
    simp only [toGates, retVal, applyGates_append, denote_applyGates, XQPL.denote,
      OpGates.denote_eq, ih h]
  | fail => exact False.elim h

/-- A measurement-free program denotes the circuit of its exact gate list followed by its
    return value. -/
theorem denote_eq_toGates [OpDenote Ops n] [OpGates Ops n] (p : XQPL Ops n α)
    (h : p.isMeasFree) :
    p.denote = QComp.qbind (GateUnitarity.unitaryDenote (Circuit.ofList (p.toGates h)))
      (fun _ => QComp.qpure (p.retVal h)) := by
  rw [denote_eq_applyGates_toGates p h, denote_applyGates]
  rfl

theorem toGates_applyGates [OpGateList Ops n] (l : List (Gate n))
    {k : XQPL Ops n α} (hk : k.isMeasFree) :
    (applyGates l k).toGates (isMeasFree_applyGates l hk) = l ++ k.toGates hk := by
  induction l with
  | nil => rfl
  | cons g l ih => simp only [applyGates, List.foldr_cons, toGates, List.cons_append] at ih ⊢; grind

/-- The exact gate list of `ofGates l` is `l`. -/
theorem toGates_ofGates [OpGateList Ops n] (l : List (Gate n))
    (h : (ofGates l : XQPL Ops n Unit).isMeasFree := isMeasFree_ofGates l) :
    (ofGates l : XQPL Ops n Unit).toGates h = l :=
  (toGates_applyGates l (k := (.ret () : XQPL Ops n Unit)) trivial).trans (List.append_nil l)

/-- The unitary of `ofGates l` is the matrix of `l`. -/
theorem unitary_ofGates [OpGateList Ops n] (l : List (Gate n))
    (h : (ofGates l : XQPL Ops n Unit).isMeasFree) :
    (ofGates l : XQPL Ops n Unit).unitary h = listMatrix l := by
  rw [unitary, toGates_ofGates]

/-! ## Adjoint -/

/-- The adjoint of a measurement-free program: the inverse of its exact gate list. -/
def adjoint [OpGateList Ops n] (p : XQPL Ops n Unit) (h : p.isMeasFree) :
    XQPL Ops n Unit :=
  ofGates (invGates (p.toGates h))

/-- The unitary of the adjoint is the conjugate transpose of the unitary. -/
theorem unitary_adjoint [OpGateList Ops n] (p : XQPL Ops n Unit)
    (h : p.isMeasFree) :
    (adjoint p h).unitary (isMeasFree_ofGates _) = (p.unitary h)ᴴ := by
  exact (unitary_ofGates _ _).trans (listMatrix_invGates _)

/-- The adjoint denotes the channel of the inverse of the unitary of the circuit of the
    exact gate list. -/
theorem denote_adjoint [OpDenote Ops n] [OpGates Ops n] (p : XQPL Ops n Unit)
    (h : p.isMeasFree) :
    (adjoint p h).denote = UnitaryChannel.unitaryChannel
      (RoutingPerm.circuitUnitary (Circuit.ofList (p.toGates h)))⁻¹ := by
  have hU : RoutingPerm.circuitUnitary (Circuit.ofList (invGates (p.toGates h))) =
      (RoutingPerm.circuitUnitary (Circuit.ofList (p.toGates h)))⁻¹ :=
    Subtype.ext (listMatrix_invGates _)
  change (ofGates (invGates (p.toGates h)) : XQPL Ops n Unit).denote = _
  rw [denote_eq_toGates _ (isMeasFree_ofGates _), toGates_ofGates, QFT.unitaryDenote_ofList,
    hU]
  exact QComp.qbind_qpure _

/-! ## Control -/

/-- The measurement-free program `p` controlled on the qubit `c`, gate by gate. -/
def controlled [OpGateList Ops n] (c : Fin n) (p : XQPL Ops n Unit)
    (h : p.isMeasFree) : XQPL Ops n Unit :=
  ofGates (ctrlList c (p.toGates h))

/-- For a program whose gates avoid `c`, the unitary of the controlled program is the
    control of the unitary on `c`. -/
theorem unitary_controlled [OpGateList Ops n] (c : Fin n) (p : XQPL Ops n Unit)
    (h : p.isMeasFree) (hc : ∀ g ∈ p.toGates h, Avoids c g) :
    (controlled c p h).unitary (isMeasFree_ofGates _) = ctrlMatrix c (p.unitary h) := by
  exact (unitary_ofGates _ _).trans (listMatrix_ctrlList hc)

/-- The measurement-free program `p` controlled on every qubit of `cs`, ancilla-free. -/
def mcontrolledNoAnc [OpGateList Ops n] (cs : List (Fin n))
    (p : XQPL Ops n Unit) (h : p.isMeasFree) : XQPL Ops n Unit :=
  ofGates ((p.toGates h).flatMap (mctrlGates cs))

end XQPL

/-- A gate list controlled gate by gate on every qubit of `cs` realises the matrix of the
    list controlled on every qubit of `cs`, for distinct controls the list avoids. -/
theorem listMatrix_flatMap_mctrlGates (L : List (Gate n)) :
    ∀ {cs : List (Fin n)}, cs.Nodup → (∀ c ∈ cs, ∀ g ∈ L, Avoids c g) →
      listMatrix (L.flatMap (mctrlGates cs)) = mctrlMatrix cs (listMatrix L)
  | [], _, _ => by simp only [mctrlGates, List.flatMap_singleton', mctrlMatrix]
  | c :: cs, hnd, h => by
    rw [List.nodup_cons] at hnd
    have hcs : ∀ c' ∈ cs, ∀ g ∈ L, Avoids c' g := fun c' hc' => h c' (List.mem_cons_of_mem c hc')
    have hav : ∀ g' ∈ L.flatMap (mctrlGates cs), Avoids c g' := by
      intro g' hg'
      obtain ⟨g, hg, hg'⟩ := List.mem_flatMap.mp hg'
      exact avoids_mctrlGates (h c List.mem_cons_self g hg) hnd.1 g' hg'
    have hfl : L.flatMap (mctrlGates (c :: cs)) = ctrlList c (L.flatMap (mctrlGates cs)) := by
      simp only [mctrlGates, ctrlList, List.flatMap_assoc]
    rw [hfl, listMatrix_ctrlList hav, listMatrix_flatMap_mctrlGates L hnd.2 hcs, mctrlMatrix]

namespace XQPL

variable {Ops : Type}

/-- For distinct controls that the program's gates avoid, the unitary of the
    multi-controlled program is the unitary controlled on every qubit of `cs`. -/
theorem unitary_mcontrolledNoAnc [OpGateList Ops n] (cs : List (Fin n))
    (p : XQPL Ops n Unit) (h : p.isMeasFree) (hnd : cs.Nodup)
    (hc : ∀ c ∈ cs, ∀ g ∈ p.toGates h, Avoids c g) :
    (mcontrolledNoAnc cs p h).unitary (isMeasFree_ofGates _) = mctrlMatrix cs (p.unitary h) := by
  exact (unitary_ofGates _ _).trans (listMatrix_flatMap_mctrlGates _ hnd hc)

end XQPL

/-! ## Conjugation -/

/-- The conjugation of `V` by `U`: `U`, then `V`, then the inverse of `U`. -/
def conjugate (U V : List (Gate n)) : List (Gate n) := U ++ V ++ invGates U

/-- The matrix of a conjugation is `(L U)ᴴ * L V * L U`. -/
theorem listMatrix_conjugate (U V : List (Gate n)) :
    listMatrix (conjugate U V) = (listMatrix U)ᴴ * listMatrix V * listMatrix U := by
  rw [conjugate, listMatrix_append, listMatrix_append, listMatrix_invGates, mul_assoc]

/-- The inverse of a gate acts on the qubits of the gate. -/
theorem avoids_invGate {c : Fin n} {g : Gate n} (h : Avoids c g) : Avoids c (invGate g) := by
  cases g <;> simpa [invGate, Avoids] using h

/-- **Controlled conjugation.** Controlling only the middle list of a conjugation controls
    the whole conjugation, when both lists avoid the control. -/
theorem listMatrix_conjugate_ctrl {c : Fin n} {U V : List (Gate n)}
    (hU : ∀ g ∈ U, Avoids c g) (hV : ∀ g ∈ V, Avoids c g) :
    listMatrix (conjugate U (ctrlList c V)) = ctrlMatrix c (listMatrix (conjugate U V)) := by
  have hA : CommOn c (listMatrix U)ᴴ := by
    rw [← listMatrix_invGates]
    refine commOn_listMatrix fun g hg => ?_
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hg)
    exact avoids_invGate (hU g₀ hg₀)
  have hAB : (listMatrix U)ᴴ * listMatrix U = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (RoutingPerm.circuitUnitary (Circuit.ofList U)).2
  rw [listMatrix_conjugate, listMatrix_conjugate, listMatrix_ctrlList hV,
    mul_ctrlMatrix_mul hA hAB]

end CatCrypt.Quantum.QPL
