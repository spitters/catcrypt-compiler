/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.Optimization.FullOptimizer

/-!
# Real-semantics soundness of template-based circuit optimization

The template-matching optimizer (`applyTemplates`, `optimizeLevel1`) is stated
against the unitary-channel semantics `unitaryDenote` (ρ ↦ UρU†,
`GateUnitarity.unitaryDenote`). The key is a small reusable soundness engine:

* `unitaryDenote_ofList_append` — list denotation is homomorphic over `++`;
* `unitaryDenote_circuitToList` — flattening a circuit to a gate list and back
  preserves `unitaryDenote`;
* `matchPrefix_eq_append` — a successful prefix match exposes the matched span;
* `applyTemplate_correctU` / `applyTemplates_correctU` — applying any
  `CorrectU` template (pattern and replacement equal under `unitaryDenote`)
  preserves `unitaryDenote`.

Every standard single-qubit template is then discharged `CorrectU` by reusing
the already-proven matrix identities in `GateUnitarity` (`templateHH_correct`,
`templateTT_correct`, `templateHXH_correct`, …), yielding
`verifiedOptimize_unitaryCorrect`: a semantics-preserving optimizer pass on the
unitary-channel meaning of the circuit.

The engine is generic in the template list, so the two templates whose real
soundness needs extra matrix work — `cancelCNOT` (two-qubit, via
`embedGate2_mul` + `cnot_sq`) and `mergeTdgTdg` (`Tdg² = Rz(-π/2)` up to the
global phase `e^{−iπ/4}`, which the channel discards) — drop in unchanged once
their `CorrectU` facts are supplied.

## Main results

* `CorrectU` — a template whose pattern and replacement have the same `unitaryDenote`.
* `unitaryDenote_ofList_append` — the list denotation maps `++` to sequential
  composition.
* `unitaryDenote_circuitToList` — flattening a circuit to a gate list and rebuilding it
  preserves `unitaryDenote`.
* `applyTemplate_correctU` — applying one `CorrectU` template preserves `unitaryDenote`.
* `applyTemplates_correctU` — the fuel-bounded optimizer over a list of `CorrectU`
  templates preserves `unitaryDenote`.
* `verifiedTemplates_correctU` — every template of `verifiedTemplates q` is `CorrectU`.
* `verifiedOptimize_unitaryCorrect` — the optimizer over `verifiedTemplates q` is
  `UnitaryCorrectQ`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.TemplateMatching
open CatCrypt.Quantum.Optimization.FullOptimizer

namespace CatCrypt.Quantum.Optimization.UnitarySound

variable {n : ℕ}

/-! ## Real-semantics template correctness -/

/-- A template is **unitary-correct** when its pattern and replacement have the
same `unitaryDenote` — the real channel semantics, not the trivial one. -/
def CorrectU (t : Template n) : Prop :=
  TemplateCorrectU t.pattern t.replacement

/-! ## The soundness engine -/

/-- List denotation (`unitaryDenote ∘ ofList`) is homomorphic over append. -/
theorem unitaryDenote_ofList_append (xs ys : List (Gate n)) :
    unitaryDenote (Circuit.ofList (xs ++ ys)) =
      QComp.qbind (unitaryDenote (Circuit.ofList xs))
        (fun _ => unitaryDenote (Circuit.ofList ys)) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, Circuit.ofList, unitaryDenote, QComp.qpure_qbind]
  | cons g xs ih =>
    simp only [List.cons_append, Circuit.ofList, unitaryDenote, ih, QComp.qbind_assoc]

/-- `unitaryDenote (ofList (g :: xs))` factors as `denoteGateU g` bound to the
denotation of the tail. -/
theorem unitaryDenote_ofList_cons (g : Gate n) (xs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (g :: xs))
      = QComp.qbind (denoteGateU g) (fun _ => unitaryDenote (Circuit.ofList xs)) :=
  rfl

/-- Equal tail denotations give equal `g :: ·` denotations. -/
theorem unitaryDenote_cons_congr (g : Gate n) {xs ys : List (Gate n)}
    (h : unitaryDenote (Circuit.ofList xs) = unitaryDenote (Circuit.ofList ys)) :
    unitaryDenote (Circuit.ofList (g :: xs))
      = unitaryDenote (Circuit.ofList (g :: ys)) := by
  rw [unitaryDenote_ofList_cons, unitaryDenote_ofList_cons, h]

/-- Flattening a circuit to its gate list (and rebuilding) preserves
`unitaryDenote`. -/
theorem unitaryDenote_circuitToList (c : Circuit n) :
    unitaryDenote (Circuit.ofList (circuitToList c)) = unitaryDenote c := by
  induction c with
  | empty => rfl
  | gate g c ih =>
    simp only [circuitToList, Circuit.ofList, unitaryDenote, ih]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [circuitToList, unitaryDenote_ofList_append, ih₁, ih₂, unitaryDenote]

/-- A successful prefix match exposes the matched span: if `matchPrefix pat gs`
succeeds with remainder `rest`, then `gs = pat ++ rest`. -/
theorem matchPrefix_eq_append :
    ∀ {pat gs rest : List (Gate n)}, matchPrefix pat gs = some rest → gs = pat ++ rest := by
  intro pat
  induction pat with
  | nil =>
    intro gs rest h
    simp only [matchPrefix, Option.some.injEq] at h
    subst h; rfl
  | cons p ps ih =>
    intro gs rest h
    cases gs with
    | nil => simp [matchPrefix] at h
    | cons g gs =>
      simp only [matchPrefix] at h
      split at h
      · next hpg =>
        have : p = g := Gate.eq_of_beqSyn hpg
        subst this
        rw [ih h, List.cons_append]
      · simp at h

/-- Applying a `CorrectU` template to a gate list preserves the list denotation. -/
theorem applyTemplateList_correctU (t : Template n) (ht : CorrectU t) :
    ∀ {gs gs' : List (Gate n)}, applyTemplateList t gs = some gs' →
      unitaryDenote (Circuit.ofList gs') = unitaryDenote (Circuit.ofList gs)
  | [], _, h => by simp [applyTemplateList] at h
  | g :: gs, gs', h => by
      simp only [applyTemplateList] at h
      cases hm : matchPrefix (circuitToList t.pattern) (g :: gs) with
      | some rest =>
        rw [hm] at h
        simp only [Option.some.injEq] at h
        subst h
        have happ : (g :: gs) = circuitToList t.pattern ++ rest :=
          matchPrefix_eq_append hm
        have hpr : unitaryDenote (Circuit.ofList (circuitToList t.replacement))
                 = unitaryDenote (Circuit.ofList (circuitToList t.pattern)) := by
          rw [unitaryDenote_circuitToList, unitaryDenote_circuitToList]
          exact ht.symm
        rw [happ, unitaryDenote_ofList_append, unitaryDenote_ofList_append, hpr]
      | none =>
        rw [hm] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨a, ha, rfl⟩ := h
        show unitaryDenote (Circuit.ofList (g :: a))
          = unitaryDenote (Circuit.ofList (g :: gs))
        simp only [Circuit.ofList, unitaryDenote]
        rw [applyTemplateList_correctU t ht ha]

/-- Applying a `CorrectU` template to a circuit preserves `unitaryDenote`. -/
theorem applyTemplate_correctU (t : Template n) (ht : CorrectU t) (c : Circuit n) :
    unitaryDenote (applyTemplate t c) = unitaryDenote c := by
  unfold applyTemplate
  cases h : applyTemplateList t (circuitToList c) with
  | none => rfl
  | some gs =>
      simp only
      rw [applyTemplateList_correctU t ht h, unitaryDenote_circuitToList]

/-- Folding a list of `CorrectU` templates preserves `unitaryDenote`. -/
theorem foldl_applyTemplate_correctU :
    ∀ (templates : List (Template n)) (c : Circuit n),
      (∀ t ∈ templates, CorrectU t) →
      unitaryDenote (templates.foldl (fun acc t => applyTemplate t acc) c)
        = unitaryDenote c
  | [], _, _ => rfl
  | t :: ts, c, hall => by
      rw [List.foldl_cons,
        foldl_applyTemplate_correctU ts (applyTemplate t c)
          (fun t' ht' => hall t' (List.mem_cons_of_mem t ht')),
        applyTemplate_correctU t (hall t List.mem_cons_self) c]

/-- The full fuel-bounded template optimizer preserves `unitaryDenote`. -/
theorem applyTemplates_correctU (templates : List (Template n))
    (hall : ∀ t ∈ templates, CorrectU t) (c : Circuit n) (fuel : ℕ) :
    unitaryDenote (applyTemplates templates c fuel) = unitaryDenote c := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel' ih =>
    have hpres : unitaryDenote (templates.foldl (fun acc t => applyTemplate t acc) c)
        = unitaryDenote c := foldl_applyTemplate_correctU templates c hall
    have hunfold : applyTemplates templates c (fuel' + 1) =
        (if (templates.foldl (fun acc t => applyTemplate t acc) c).gateCount < c.gateCount
         then applyTemplates templates
                (templates.foldl (fun acc t => applyTemplate t acc) c) fuel'
         else templates.foldl (fun acc t => applyTemplate t acc) c) := rfl
    rw [hunfold]
    split
    · rw [ih]; exact hpres
    · exact hpres

/-! ## The standard single-qubit templates are unitary-correct

Each is discharged by reusing the corresponding already-proven matrix identity
in `GateUnitarity`. -/

theorem cancelHH_correctU (q : Fin n) : CorrectU (cancelHH q) := templateHH_correct q
theorem cancelXXTemplate_correctU (q : Fin n) : CorrectU (cancelXXTemplate q) :=
  templateXX_correct q
theorem cancelYY_correctU (q : Fin n) : CorrectU (cancelYY q) := templateYY_correct q
theorem cancelZZ_correctU (q : Fin n) : CorrectU (cancelZZ q) := templateZZ_correct q
theorem cancelTTdg_correctU (q : Fin n) : CorrectU (cancelTTdg q) := templateTTdg_correct q
theorem cancelTdgT_correctU (q : Fin n) : CorrectU (cancelTdgT q) := templateTdgT_correct q
theorem mergeTT_correctU (q : Fin n) : CorrectU (mergeTT q) := templateTT_correct q
theorem mergeSS_correctU (q : Fin n) : CorrectU (mergeSS q) := templateSS_correct q
theorem hxh_to_z_correctU (q : Fin n) : CorrectU (hxh_to_z q) := templateHXH_correct q
theorem hzh_to_x_correctU (q : Fin n) : CorrectU (hzh_to_x q) := templateHZH_correct q

/-- The verified single-qubit template set for a qubit `q`: every entry is
proven `CorrectU` against the real unitary semantics. -/
def verifiedTemplates (q : Fin n) : List (Template n) :=
  [ cancelHH q, cancelXXTemplate q, cancelYY q, cancelZZ q,
    cancelTTdg q, cancelTdgT q, mergeTT q, mergeSS q,
    hxh_to_z q, hzh_to_x q ]

theorem verifiedTemplates_correctU (q : Fin n) :
    ∀ t ∈ verifiedTemplates q, CorrectU t := by
  intro t ht
  fin_cases ht
  · exact cancelHH_correctU q
  · exact cancelXXTemplate_correctU q
  · exact cancelYY_correctU q
  · exact cancelZZ_correctU q
  · exact cancelTTdg_correctU q
  · exact cancelTdgT_correctU q
  · exact mergeTT_correctU q
  · exact mergeSS_correctU q
  · exact hxh_to_z_correctU q
  · exact hzh_to_x_correctU q

/-- **The verified template optimizer is semantics-preserving.**
Running the standard single-qubit templates for qubit `q` preserves the
unitary-channel denotation `unitaryDenote`. This is `UnitaryCorrectQ` in the
sense of `GateUnitarity`. -/
theorem verifiedOptimize_unitaryCorrect (q : Fin n) (fuel : ℕ) :
    UnitaryCorrectQ (fun c => applyTemplates (verifiedTemplates q) c fuel) := by
  intro c
  exact (applyTemplates_correctU (verifiedTemplates q)
    (verifiedTemplates_correctU q) c fuel).symm

end CatCrypt.Quantum.Optimization.UnitarySound
