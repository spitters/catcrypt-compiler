/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QrunchRound

/-!
# The qubit pairs of a Qrunch round: connectivity is preserved

The qubit pairs of a qelib1 statement list (`cxPairs`) are the unordered pairs `s(a, b)` of
the qubits of its multi-qubit statements: `cx`, `cz`, `swap` and `cp` carry the pair of their
operands, `ccx` and `ccz` the three pairs of their operands. The qubit pairs of a gate list
(`gPairs`) are the pairs of its `CNOT` and `CZ` gates. A pass keeps connectivity when the
qubit pairs of its output are among those of its input: after routing a circuit onto the
coupling map of a device, every two-qubit statement lies on an edge of the map, and a pass
that keeps connectivity puts no two-qubit statement on a pair that is not an edge
(`cxPairs_subset_of_routed`).

Every stage of a round of `QrunchRound` keeps connectivity: the lowering `lowerQ`, the stages
Level 1, Level 2 (each of its six named passes) and the resynthesis level (`kakEmit` on the
two-qubit blocks, whose templates lie on the pair of their block, and the ZYZ pass on the
one-qubit runs), the basis translation `toQelib` and the statement passes `fuseQ`,
`commuteQ`, `pauliQ` and `QrunchShort.shortQ`, and the angle snapping `AngleSnap.snapQ`.
Swap elision `SwapElide.elideQ` relabels the wires and does not keep connectivity, so the
whole run is stated with `elide := false`.

## Main definitions

* `stmtPairs`, `cxPairs` — the qubit pairs of a statement and of a statement list.
* `gatePairs`, `gPairs` — the qubit pairs of a gate and of a gate list.
* `StagePairs` — a stage keeps connectivity.

## Main results

* `cxPairs_basisPasses_subset` — the Qrunch-basis passes keep connectivity.
* `gPairs_kakEmit_subset`, `gPairs_zyzEmit_subset` — the KAK and ZYZ passes keep it.
* `stagePairs_resynthAt` — the resynthesis level keeps connectivity, at every pair of fits.
* `gPairs_level1Gates_subset`, `gPairs_level2Gates_subset` — Level 1 and Level 2 keep it.
* `cxPairs_round_subset` — one round keeps connectivity.
* `cxPairs_runRounds_subset` — the iteration keeps connectivity.
* `cxPairs_compileQGates_subset` — the whole run without swap elision keeps connectivity.
* `routed_compileQGates` — the whole run without swap elision maps a statement list routed on a
  coupling map to one routed on the map.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.OpenQASMImport (QGate lowerQ)
open CatCrypt.Quantum.QrunchFuse
open CatCrypt.Quantum.QrunchRound

namespace CatCrypt.Quantum.QrunchConnect

variable {n : ℕ}

/-! ## Qubit pairs -/

/-- The qubit pairs of a statement: the pair of the operands of a two-qubit statement, the
three pairs of the operands of a three-qubit statement, none for a one-qubit statement. -/
def stmtPairs : QGate n → List (Sym2 (Fin n))
  | .cx a b | .cz a b | .swap a b | .cp a b _ => [s(a, b)]
  | .ccx a b c | .ccz a b c => [s(a, b), s(a, c), s(b, c)]
  | _ => []

/-- The qubit pairs of a statement list: the pairs on which it has a multi-qubit statement. -/
def cxPairs (l : List (QGate n)) : List (Sym2 (Fin n)) := l.flatMap stmtPairs

/-- The qubit pair of a gate: the pair of a `CNOT` or a `CZ`, none for a one-qubit gate. -/
def gatePairs : Gate n → List (Sym2 (Fin n))
  | .CNOT a b | .CZ a b => [s(a, b)]
  | _ => []

/-- The qubit pairs of a gate list: the pairs on which it has a two-qubit gate. -/
def gPairs (l : List (Gate n)) : List (Sym2 (Fin n)) := l.flatMap gatePairs

/-- Unfolding lemma: the empty statement list has no pair. -/
@[simp] theorem cxPairs_nil : cxPairs ([] : List (QGate n)) = [] := rfl

/-- The pairs of a statement in front of a list. -/
@[simp] theorem cxPairs_cons (g : QGate n) (l : List (QGate n)) :
    cxPairs (g :: l) = stmtPairs g ++ cxPairs l := by
  simp [cxPairs]

/-- The pairs of a concatenation of statement lists. -/
@[simp] theorem cxPairs_append (l l' : List (QGate n)) :
    cxPairs (l ++ l') = cxPairs l ++ cxPairs l' := by
  simp [cxPairs]

/-- Unfolding lemma: the empty gate list has no pair. -/
@[simp] theorem gPairs_nil : gPairs ([] : List (Gate n)) = [] := rfl

/-- The pairs of a gate in front of a list. -/
@[simp] theorem gPairs_cons (g : Gate n) (l : List (Gate n)) :
    gPairs (g :: l) = gatePairs g ++ gPairs l := by
  simp [gPairs]

/-- The pairs of a concatenation of gate lists. -/
@[simp] theorem gPairs_append (l l' : List (Gate n)) :
    gPairs (l ++ l') = gPairs l ++ gPairs l' := by
  simp [gPairs]

/-- A pair of a statement list is a pair of one of its statements. -/
theorem mem_cxPairs {p : Sym2 (Fin n)} {l : List (QGate n)} :
    p ∈ cxPairs l ↔ ∃ g ∈ l, p ∈ stmtPairs g := by
  simp [cxPairs]

/-- A pair of a gate list is a pair of one of its gates. -/
theorem mem_gPairs {p : Sym2 (Fin n)} {l : List (Gate n)} :
    p ∈ gPairs l ↔ ∃ g ∈ l, p ∈ gatePairs g := by
  simp [gPairs]

/-- The reversed statement list has the same pairs. -/
@[simp] theorem mem_cxPairs_reverse {p : Sym2 (Fin n)} {l : List (QGate n)} :
    p ∈ cxPairs l.reverse ↔ p ∈ cxPairs l := by
  simp [mem_cxPairs]

/-- The reversed gate list has the same pairs. -/
@[simp] theorem mem_gPairs_reverse {p : Sym2 (Fin n)} {l : List (Gate n)} :
    p ∈ gPairs l.reverse ↔ p ∈ gPairs l := by
  simp [mem_gPairs]

/-- Two inclusions of lists give the inclusion of their concatenations. -/
theorem append_subset_append {α : Type*} {a b c d : List α} (h₁ : a ⊆ b) (h₂ : c ⊆ d) :
    a ++ c ⊆ b ++ d :=
  List.append_subset.mpr ⟨List.Subset.trans h₁ (List.subset_append_left _ _),
    List.Subset.trans h₂ (List.subset_append_right _ _)⟩

/-- A gate list whose gates are among those of `l` has its pairs among those of `l`. -/
theorem gPairs_subset_of_subset {l l' : List (Gate n)} (h : l' ⊆ l) : gPairs l' ⊆ gPairs l := by
  intro p hp
  obtain ⟨g, hg, hp⟩ := mem_gPairs.mp hp
  exact mem_gPairs.mpr ⟨g, h hg, hp⟩

/-! ## One-qubit statements -/

/-- A rotation statement has no pair. -/
@[simp] theorem stmtPairs_mkQ (A : Axis) (q : Fin n) (a : PiLin) : stmtPairs (mkQ A q a) = [] := by
  cases A <;> rfl

/-- An emitted rotation has no pair. -/
@[simp] theorem cxPairs_emit (q : Fin n) (e : Pend) : cxPairs (emit q e) = [] := by
  rcases e with _ | ⟨A, a⟩
  · rfl
  · by_cases h : isId A a = true <;> simp [emit, h]

/-- Flushed rotations have no pair. -/
@[simp] theorem cxPairs_flushOn (F : Fin n → Pend) (L : List (Fin n)) :
    cxPairs (flushOn F L) = [] := by
  induction L with
  | nil => rfl
  | cons q L ih => simp_all [flushOn]

/-- Rotation statements on one qubit have no pair. -/
@[simp] theorem cxPairs_onQ (q : Fin n) (l : List (Axis × PiLin)) : cxPairs (onQ q l) = [] := by
  induction l with
  | nil => rfl
  | cons e l ih => simp_all [onQ]

/-! ## The statement passes -/

/-- A step of the fusion scan emits pairs of its input statement only. -/
theorem cxPairs_step_subset (v : Vector Pend n) (g : QGate n) :
    cxPairs (step v g).1 ⊆ stmtPairs g := by
  unfold step
  split
  · split
    · split <;> simp
    · simp
  · split
    · split <;> simp
    · simp

/-- The fusion scan keeps connectivity. -/
theorem cxPairs_fuseAux_subset (l : List (QGate n)) :
    ∀ v : Vector Pend n, cxPairs (fuseAux v l) ⊆ cxPairs l := by
  induction l with
  | nil => intro v; simp [fuseAux]
  | cons g l ih =>
    intro v
    simp only [fuseAux, cxPairs_append, cxPairs_cons]
    exact append_subset_append (cxPairs_step_subset v g) (ih _)

/-- **Fusion keeps connectivity.** -/
theorem cxPairs_fuseQ_subset (l : List (QGate n)) : cxPairs (fuseQ l) ⊆ cxPairs l :=
  cxPairs_fuseAux_subset l _

/-- **The backward commutation pass keeps connectivity.** -/
theorem cxPairs_commuteQ_subset (l : List (QGate n)) :
    cxPairs (QrunchCommute.commuteQ l) ⊆ cxPairs l := by
  intro p hp
  simp only [QrunchCommute.commuteQ, mem_cxPairs_reverse] at hp
  simpa using cxPairs_fuseQ_subset l.reverse hp

/-- A step of the Clifford frame scan emits pairs of its input statement only. -/
theorem cxPairs_frameStep_subset (U W : Vector Pend n) (g : QGate n) :
    cxPairs (frameStep U W g).1 ⊆ stmtPairs g := by
  unfold frameStep
  split
  · simp [frameRot]
  · have hs := cxPairs_step_subset U g
    split
    · split <;> simpa using hs
    · simpa using hs

/-- The Clifford frame scan keeps connectivity. -/
theorem cxPairs_frameAux_subset (l : List (QGate n)) :
    ∀ U W : Vector Pend n, cxPairs (frameAux U W l).1 ⊆ cxPairs l := by
  induction l with
  | nil => intro U W; simp [frameAux]
  | cons g l ih =>
    intro U W
    simp only [frameAux, cxPairs_append, cxPairs_cons]
    exact append_subset_append (cxPairs_frameStep_subset U W g) (ih _ _)

/-- **The Pauli frame pass keeps connectivity.** -/
theorem cxPairs_pauliQ_subset (l : List (QGate n)) : cxPairs (pauliQ l).1 ⊆ cxPairs l :=
  cxPairs_frameAux_subset l _ _

/-- A step of the run-shortening scan emits pairs of its input statement only. -/
theorem cxPairs_shortStep_subset (U W : Vector Pend n) (g : QGate n) :
    cxPairs (QrunchShort.shortStep U W g).1 ⊆ stmtPairs g := by
  unfold QrunchShort.shortStep
  split
  · simp [QrunchShort.shortRot]
  · exact cxPairs_frameStep_subset U W g

/-- The run-shortening scan keeps connectivity. -/
theorem cxPairs_shortAux_subset (l : List (QGate n)) :
    ∀ U W : Vector Pend n, cxPairs (QrunchShort.shortAux U W l).1 ⊆ cxPairs l := by
  induction l with
  | nil => intro U W; simp [QrunchShort.shortAux]
  | cons g l ih =>
    intro U W
    simp only [QrunchShort.shortAux, cxPairs_append, cxPairs_cons]
    exact append_subset_append (cxPairs_shortStep_subset U W g) (ih _ _)

/-- **The run-shortening pass keeps connectivity.** -/
theorem cxPairs_shortQ_subset (l : List (QGate n)) :
    cxPairs (QrunchShort.shortQ l).1 ⊆ cxPairs l :=
  cxPairs_shortAux_subset l _ _

/-- The statements of a gate keep its pair. -/
theorem cxPairs_gateQ_subset (g : Gate n) :
    cxPairs (QrunchBasis.gateQ g).1 ⊆ gatePairs g := by
  cases g <;> simp [QrunchBasis.gateQ, gatePairs, stmtPairs]
  split <;> simp [stmtPairs]

/-- **The basis translation keeps connectivity.** -/
theorem cxPairs_toQelib_subset (l : List (Gate n)) :
    cxPairs (QrunchBasis.toQelib l).1 ⊆ gPairs l := by
  fun_induction QrunchBasis.toQelib l with
  | case1 => simp
  | case2 => assumption
  | case3 | case5 | case6 =>
    grind only [= List.subset_def, gPairs_cons, cxPairs_append, append_subset_append,
      cxPairs_gateQ_subset]
  | case4 => assumption

/-- **Angle snapping keeps the pairs.** -/
theorem cxPairs_snapQ (l : List (QGate n)) : cxPairs (AngleSnap.snapQ l).1 = cxPairs l := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [AngleSnap.snapQ_cons, cxPairs_cons, cxPairs_cons, ih]
    congr 1
    cases g <;> rfl

/-- **The basis passes keep connectivity.** -/
theorem cxPairs_basisPasses_subset (l : List (Gate n)) :
    cxPairs (basisPasses l).1 ⊆ gPairs l := by
  simp only [basisPasses]
  exact List.Subset.trans (cxPairs_fuseQ_subset _) <| List.Subset.trans (cxPairs_shortQ_subset _) <|
    List.Subset.trans (cxPairs_pauliQ_subset _) <| List.Subset.trans (cxPairs_commuteQ_subset _) <|
    List.Subset.trans (cxPairs_fuseQ_subset _) (cxPairs_toQelib_subset l)

/-! ## The lowering -/

/-- **The lowering keeps the pairs** of a statement. -/
theorem gPairs_lowerQ_subset (g : QGate n) : gPairs (lowerQ g) ⊆ stmtPairs g := by
  cases g <;> simp [lowerQ, stmtPairs, gatePairs, OpenQASMImport.sdgGates,
    OpenQASMImport.sxGates, OpenQASMImport.sxdgGates, OpenQASMImport.rxGates,
    OpenQASMImport.ryGates, OpenQASMImport.uGates, OpenQASMImport.swapCnotGates,
    OpenQASMImport.cphaseGates, OpenQASMImport.ccxGates, OpenQASMImport.cczGates]

/-- The lowering of a statement list keeps connectivity. -/
theorem gPairs_flatMap_lowerQ_subset (l : List (QGate n)) :
    gPairs (l.flatMap lowerQ) ⊆ cxPairs l := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.flatMap_cons, gPairs_append, cxPairs_cons]
    exact append_subset_append (gPairs_lowerQ_subset g) ih

/-! ## Circuit passes -/

/-- A gate in front of two gate lists keeps an inclusion of their pairs. -/
theorem gPairs_cons_subset_cons (g : Gate n) {l l' : List (Gate n)} (h : gPairs l ⊆ gPairs l') :
    gPairs (g :: l) ⊆ gPairs (g :: l') := by
  rw [gPairs_cons, gPairs_cons]
  exact append_subset_append (List.Subset.refl _) h

/-- The gate list of a circuit built from a gate list is that list. -/
@[simp] theorem circuitToList_ofList (l : List (Gate n)) :
    circuitToList (Circuit.ofList l) = l := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [Circuit.ofList, circuitToList, ih]

/-- The two flattenings of a circuit agree. -/
theorem toGateList_eq_circuitToList (c : Circuit n) :
    OpenQASM.toGateList c = circuitToList c := by
  induction c with
  | empty => rfl
  | gate g c ih => simp [OpenQASM.toGateList, circuitToList, ih]
  | seq c₁ c₂ ih₁ ih₂ => simp [OpenQASM.toGateList, circuitToList, ih₁, ih₂]

/-- A circuit pass keeps connectivity: the pairs of its output are among those of its input. -/
def PassPairs (p : Circuit n → Circuit n) : Prop :=
  ∀ c, gPairs (circuitToList (p c)) ⊆ gPairs (circuitToList c)

/-- A pass list whose passes keep connectivity keeps connectivity. -/
theorem passPairs_runPasses (ps : List (Circuit n → Circuit n)) (h : ∀ p ∈ ps, PassPairs p) :
    PassPairs (Optimization.PassPipeline.runPasses ps) := by
  induction ps with
  | nil => intro c; exact List.Subset.refl _
  | cons p ps ih =>
    intro c
    exact List.Subset.trans (ih (fun q hq => h q (List.mem_cons_of_mem p hq)) (p c))
      (h p List.mem_cons_self c)

/-! ### The template pass -/

section Template

open Optimization.TemplatePass

/-- The template pass keeps connectivity when every replacement has no pair. -/
theorem gPairs_templatePassAuxC_subset (cs : Gate n → List (CTemplate n))
    (hcs : ∀ g, ∀ t ∈ cs g, gPairs t.rep = []) (stk todo : List (Gate n)) :
    gPairs (templatePassAuxC cs stk todo) ⊆ gPairs stk ++ gPairs todo := by
  fun_induction templatePassAuxC cs stk todo with
  | case1 stk => intro p hp; simp_all
  | case2 stk g todo rest rep h ih =>
    obtain ⟨t, ht, hstk, rfl⟩ := matchStackC_spec h
    have hrep := hcs g t ht
    have hr : ∀ p ∈ gPairs rest, p ∈ gatePairs g ∨ p ∈ gPairs stk := by
      intro p hp
      have h2 : p ∈ gPairs (g :: stk) := by rw [hstk]; simp [hp]
      simpa using h2
    intro p hp
    have h3 := ih hp
    simp only [gPairs_append, hrep, List.nil_append, List.mem_append, gPairs_cons] at h3 ⊢
    grind
  | case3 stk g todo h ih =>
    intro p hp
    have h3 := ih hp
    simp only [List.mem_append, gPairs_cons] at h3 ⊢
    grind

/-- The replacements of the Level 1 templates have no pair. -/
theorem gPairs_level1Family_rep :
    ∀ g : Gate n, ∀ t ∈ compileFamily (level1Family
      Optimization.FullOptimizer.standardTemplates Optimization.FullOptimizer.cnotTemplates) g,
      gPairs t.rep = [] := by
  intro g ct hc
  obtain ⟨t, ht, -, hr, -⟩ := mem_compileList hc
  rw [hr]
  refine level1Family_forall (P := fun t => gPairs (circuitToList t.replacement) = [])
    (fun q u hu => ?_) (fun c t _ u hu => ?_) g t ht
  · simp only [Optimization.FullOptimizer.standardTemplates, List.mem_cons, List.not_mem_nil,
      or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [Optimization.FullOptimizer.cnotTemplates, List.mem_cons, List.not_mem_nil,
      or_false] at hu
    subst hu
    rfl

/-- **The Level 1 template pass keeps connectivity.** -/
theorem passPairs_templatePass :
    PassPairs (Optimization.PassPipeline.NamedPass.run (n := n) .templatePass) := by
  intro c
  simp only [Optimization.PassPipeline.NamedPass.run, level1Pass_eq, templatePassC,
    compiledPassC, compiledPass, circuitToList_ofList]
  exact List.Subset.trans (gPairs_templatePassAuxC_subset _ gPairs_level1Family_rep _ _)
    (by simp)

end Template

/-! ### Commutation and merging -/

section Merge

open Optimization.CommutationRules

/-- A merge of an `Rz` keeps the pairs of the list it moves over. -/
theorem gPairs_tryMergeRz_subset (i : Fin n) (θ : ℝ) :
    ∀ gs r : List (Gate n), tryMergeRz i θ gs = some r → gPairs r ⊆ gPairs gs := by
  intro gs
  induction gs with
  | nil => intro r h; simp [tryMergeRz] at h
  | cons g gs ih =>
    intro r h
    unfold tryMergeRz at h
    split at h
    · split at h
      · cases h
        simp [gatePairs]
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨r', hr', rfl⟩ := h
          exact gPairs_cons_subset_cons g (ih r' hr')
        · cases h
    · split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        exact gPairs_cons_subset_cons g (ih r' hr')
      · cases h

/-- The merge pass keeps connectivity. -/
theorem gPairs_mergePass_subset :
    ∀ (fuel : ℕ) (gs : List (Gate n)), gPairs (mergePass gs fuel) ⊆ gPairs gs := by
  intro fuel
  induction fuel with
  | zero => intro gs; exact List.Subset.refl _
  | succ k ih =>
    intro gs
    cases gs with
    | nil => exact List.Subset.refl _
    | cons g rest =>
      simp only [mergePass]
      split
      · split
        · rename_i hm
          exact List.Subset.trans (ih _) (List.Subset.trans
            (gPairs_tryMergeRz_subset _ _ _ _ hm) (List.subset_append_right _ _))
        · exact gPairs_cons_subset_cons g (ih rest)
      · exact gPairs_cons_subset_cons g (ih rest)

/-- **Commutation and merging keeps connectivity.** -/
theorem passPairs_commuteAndMerge : PassPairs (commuteAndMerge (n := n)) := by
  intro c
  simp only [commuteAndMerge, circuitToList_ofList]
  exact gPairs_mergePass_subset _ _

end Merge

/-! ### Commutation-aware cancellation -/

section Cancel

open Optimization.CommuteCancel

/-- An absorbed pair reduces to gates with no pair. -/
theorem gPairs_absorb {x y : Gate n} {r : List (Gate n)}
    (h : Optimization.CommuteCancel.absorb x y = some r) :
    gPairs r = [] := by
  cases x <;> cases y <;> simp only [Optimization.CommuteCancel.absorb, reduceCtorEq] at h <;>
    grind [gPairs, gatePairs]

/-- A scan keeps the pairs of the items it moves over. -/
theorem gPairs_flat_scan (x : Gate n) :
    ∀ (k : ℕ) (ys r : List (Item n)), scan x k ys = some r →
      gPairs (flat r) ⊆ gPairs (flat ys) := by
  intro k
  induction k with
  | zero => intro ys r h; simp [scan] at h
  | succ k ih =>
    intro ys r h
    cases ys with
    | nil => simp [scan] at h
    | cons y ys =>
      simp only [scan] at h
      split at h
      · rename_i r0 hr0
        cases h
        have h0 : gPairs r0 = [] := by
          cases y with
          | gate g => exact gPairs_absorb hr0
          | xblock => simp [absorbItem] at hr0
        intro p hp
        simp only [flat, List.flatMap_append, List.flatMap_map, Item.gates, gPairs_append,
          List.mem_append] at hp
        grind [flat, gPairs, List.flatMap_singleton']
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨r', hr', rfl⟩ := h
          simp only [flat, List.flatMap_cons, gPairs_append] at ih hr' ⊢
          exact append_subset_append (List.Subset.refl _) (ih ys r' hr')
        · cases h

/-- The cancellation sweep keeps connectivity. -/
theorem gPairs_flat_cancelGo :
    ∀ (k : ℕ) (l : List (Item n)), gPairs (flat (cancelGo k l)) ⊆ gPairs (flat l) := by
  intro k
  induction k with
  | zero => intro l; exact List.Subset.refl _
  | succ k ih =>
    intro l
    cases l with
    | nil => exact List.Subset.refl _
    | cons x rest =>
      cases x with
      | gate g =>
        simp only [cancelGo]
        split
        · rename_i rest' h
          refine List.Subset.trans (ih rest') (List.Subset.trans (gPairs_flat_scan g _ _ _ h) ?_)
          simp only [flat, List.flatMap_cons, gPairs_append]
          exact List.subset_append_right _ _
        · simp only [flat, List.flatMap_cons, gPairs_append] at ih ⊢
          exact append_subset_append (List.Subset.refl _) (ih rest)
      | xblock q ds hd =>
        simp only [cancelGo, flat, List.flatMap_cons, gPairs_append] at ih ⊢
        exact append_subset_append (List.Subset.refl _) (ih rest)

/-- **Commutation-aware cancellation keeps connectivity.** -/
theorem passPairs_commuteCancel : PassPairs (commuteCancel (n := n)) := by
  intro c
  simp only [commuteCancel, commuteCancelList, circuitToList_ofList]
  refine List.Subset.trans (gPairs_flat_cancelGo _ _) ?_
  rw [flat_toItems]

end Cancel

/-! ### `RzQ` canonicalisation, T merging and NOT propagation -/

/-- The canonical gates of a gate keep its pair. -/
theorem gPairs_rzqCanon (g : Gate n) : gPairs (Optimization.RzQCanon.rzqCanon g) ⊆ gatePairs g := by
  cases g <;> simp only [Optimization.RzQCanon.rzqCanon] <;> (try split_ifs) <;> simp [gatePairs]

/-- **`RzQ` canonicalisation keeps connectivity.** -/
theorem passPairs_rzqCanonPass : PassPairs (Optimization.RzQCanon.rzqCanonPass (n := n)) := by
  intro c
  induction c with
  | empty => exact List.Subset.refl _
  | gate g c ih =>
    simp only [Optimization.RzQCanon.rzqCanonPass, circuitToList, gPairs_append,
      circuitToList_ofList, gPairs_cons]
    exact append_subset_append (gPairs_rzqCanon g) ih
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Optimization.RzQCanon.rzqCanonPass, circuitToList, gPairs_append]
    exact append_subset_append ih₁ ih₂

section TMerge

open Optimization.TCountOpt

/-- The rest after a run of `T` gates keeps the pairs. -/
theorem gPairs_countConsecutiveT (q : Fin n) :
    ∀ gs : List (Gate n), gPairs (countConsecutiveT q gs).2 ⊆ gPairs gs := by
  intro gs
  induction gs with
  | nil => exact List.Subset.refl _
  | cons g gs ih =>
    cases g <;> simp only [countConsecutiveT] <;> try exact List.Subset.refl _
    split
    · simpa [gatePairs] using ih
    · exact List.Subset.refl _

/-- A power of `T` has no pair. -/
theorem gPairs_tPowerToGates (q : Fin n) (k : ℕ) : gPairs (tPowerToGates q k) = [] := by
  unfold tPowerToGates
  split <;> rfl

/-- T merging keeps connectivity on gate lists. -/
theorem gPairs_tMergeList_subset :
    ∀ (fuel : ℕ) (gs : List (Gate n)), gPairs (tMergeList gs fuel) ⊆ gPairs gs := by
  intro fuel
  induction fuel with
  | zero => intro gs; exact List.Subset.refl _
  | succ k ih =>
    intro gs
    cases gs with
    | nil => exact List.Subset.refl _
    | cons g rest =>
      cases g with
      | T q =>
        simp only [tMergeList]
        rcases hc : countConsecutiveT q rest with ⟨count, remaining⟩
        have h1 := gPairs_countConsecutiveT q rest
        rw [hc] at h1
        simp only [gPairs_append, gPairs_tPowerToGates, List.nil_append, gPairs_cons, gatePairs]
        exact List.Subset.trans (ih remaining) h1
      | _ => exact gPairs_cons_subset_cons _ (ih rest)

/-- **T merging keeps connectivity.** -/
theorem passPairs_tMerge : PassPairs (tMerge (n := n)) := by
  intro c
  simp only [tMerge, circuitToList_ofList]
  exact gPairs_tMergeList_subset _ _

end TMerge

section NotProp

open Optimization.NotPropagation

/-- An `X` gate has no pair. -/
theorem gatePairs_of_isXGate {g : Gate n} {i : Fin n} (h : isXGate g = some i) :
    gatePairs g = [] := by
  cases g <;> simp [isXGate, gatePairs] at h ⊢

/-- Cancelling `X; X` keeps connectivity. -/
theorem gPairs_cancelXX_subset :
    ∀ (fuel : ℕ) (gs : List (Gate n)), gPairs (cancelXX gs fuel) ⊆ gPairs gs := by
  intro fuel
  induction fuel with
  | zero => intro gs; simp [cancelXX]
  | succ k ih =>
    intro gs
    match gs with
    | [] => exact List.Subset.refl _
    | [g] => exact List.Subset.refl _
    | g₁ :: g₂ :: rest =>
      simp only [cancelXX]
      split
      · rename_i i j h₁ h₂
        split
        · simp only [gPairs_cons, gatePairs_of_isXGate h₁, gatePairs_of_isXGate h₂,
            List.nil_append]
          exact ih rest
        · exact gPairs_cons_subset_cons _ (ih _)
      · exact gPairs_cons_subset_cons _ (ih _)

/-- Propagating an `X` keeps the pairs of the list it moves through. -/
theorem gPairs_propagateX_subset (q : Fin n) :
    ∀ (fuel : ℕ) (rest : List (Gate n)), gPairs (propagateX q rest fuel) ⊆ gPairs rest := by
  intro fuel
  induction fuel with
  | zero => intro rest; simp [propagateX, gatePairs]
  | succ k ih =>
    intro rest
    cases rest with
    | nil => simp [propagateX, gatePairs]
    | cons g gs =>
      simp only [propagateX]
      split
      · rename_i j hj
        split
        · simp [gatePairs_of_isXGate hj]
        · exact gPairs_cons_subset_cons _ (ih _)
      · split
        · split
          · exact gPairs_cons_subset_cons _ (ih _)
          · split
            · refine gPairs_cons_subset_cons _ (List.Subset.trans (ih _) ?_)
              simp [gatePairs]
            · exact gPairs_cons_subset_cons _ (ih _)
        · split_ifs
          · exact gPairs_cons_subset_cons _ (ih _)
          · intro p hp
            simpa [gatePairs] using hp

/-- NOT propagation keeps connectivity on gate lists. -/
theorem gPairs_propagateNot_subset :
    ∀ (fuel : ℕ) (gs : List (Gate n)), gPairs (propagateNot gs fuel) ⊆ gPairs gs := by
  intro fuel
  induction fuel with
  | zero => intro gs; simp [propagateNot]
  | succ k ih =>
    intro gs
    cases gs with
    | nil => exact List.Subset.refl _
    | cons g rest =>
      simp only [propagateNot]
      split
      · rename_i q hq
        refine List.Subset.trans (gPairs_propagateX_subset q _ _) (List.Subset.trans (ih rest) ?_)
        simp [gatePairs_of_isXGate hq]
      · exact gPairs_cons_subset_cons _ (ih rest)

/-- **NOT propagation where it does not lengthen the circuit keeps connectivity.** -/
theorem passPairs_notPropagationNoLonger :
    PassPairs (Optimization.PassPipeline.notPropagationNoLonger (n := n)) := by
  intro c
  unfold Optimization.PassPipeline.notPropagationNoLonger
  split
  · simp only [notPropagationPass, circuitToList_ofList]
    exact List.Subset.trans (gPairs_cancelXX_subset _ _) (gPairs_propagateNot_subset _ _)
  · exact List.Subset.refl _

end NotProp

/-! ### Level 1 and Level 2 -/

section Levels

open Optimization.PassPipeline Optimization.FullOptimizer

/-- A list of named passes whose passes keep connectivity keeps connectivity. -/
theorem passPairs_runNamed (ps : List (NamedPass n)) (h : ∀ q ∈ ps, PassPairs q.run) :
    PassPairs (runNamed ps) :=
  passPairs_runPasses _ fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact h q hq

/-- Every pass of Level 2 keeps connectivity. -/
theorem passPairs_level2 : ∀ q ∈ levelPasses (n := n) .Level2, PassPairs q.run := by
  intro q hq
  simp only [levelPasses, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact passPairs_templatePass
  · exact passPairs_commuteAndMerge
  · exact passPairs_commuteCancel
  · exact passPairs_rzqCanonPass
  · exact passPairs_tMerge
  · exact passPairs_notPropagationNoLonger

/-- **Level 1 keeps connectivity.** -/
theorem gPairs_level1Gates_subset (c : Circuit n) :
    gPairs (OpenQASM.toGateList (fullOptimize .Level1 c)) ⊆ gPairs (circuitToList c) := by
  rw [toGateList_eq_circuitToList, fullOptimize_eq_runNamed]
  refine passPairs_runNamed _ (fun q hq => ?_) c
  simp only [levelPasses, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  exact passPairs_templatePass

/-- **Level 2 keeps connectivity.** -/
theorem gPairs_level2Gates_subset (c : Circuit n) :
    gPairs (Optimization.ResynthLevel.level2Gates c) ⊆ gPairs (circuitToList c) := by
  rw [Optimization.ResynthLevel.level2Gates, toGateList_eq_circuitToList,
    fullOptimize_eq_runNamed]
  exact passPairs_runNamed _ passPairs_level2 c

end Levels

/-! ## The resynthesis level -/

section KAK

open Synthesis.KAKPass Synthesis.KAKPassSmall

/-- Each open block holds a gate on its pair. -/
def Opened (os : List (OpenBlk n)) : Prop := ∀ b ∈ os, s(b.i, b.j) ∈ gPairs b.blk

/-- The blocks of the scan hold gates of its input only, and each block holds a gate on its
pair. -/
theorem collectAux_spec (l : List (Gate n)) :
    ∀ os : List (OpenBlk n), Opened os → ∀ b ∈ collectAux os l,
      (∀ x ∈ b.gates, x ∈ stGates os ∨ x ∈ l) ∧
        ∀ i j gs, b = .pair i j gs → s(i, j) ∈ gPairs gs := by
  induction l with
  | nil =>
    intro os hos b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    refine ⟨fun x hx => Or.inl ?_, fun i j gs h => ?_⟩
    · simp only [OpenBlk.emit, Block.gates, List.mem_reverse] at hx
      exact List.mem_flatMap.mpr ⟨c, hc, List.mem_reverse.mpr hx⟩
    · simp only [OpenBlk.emit, Block.pair.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact mem_gPairs_reverse.mpr (hos c hc)
  | cons g gs ih =>
    intro os hos
    have hU : ∀ c ∈ os.filter (fun c => !c.touches g), c ∈ os := fun c hc =>
      (List.mem_filter.mp hc).1
    have hst : ∀ x, x ∈ stGates (os.filter (fun c => !c.touches g)) → x ∈ stGates os := by
      intro x hx
      obtain ⟨c, hc, hx⟩ := List.mem_flatMap.mp hx
      exact List.mem_flatMap.mpr ⟨c, hU c hc, hx⟩
    simp only [collectAux]
    split
    · next b hj =>
      obtain ⟨hT, -⟩ := joinable_spec hj
      have hbT : b ∈ os.filter (OpenBlk.touches g) := by
        rw [hT]; exact List.mem_singleton_self b
      have hb : b ∈ os := (List.mem_filter.mp hbT).1
      intro x hx
      have hO : Opened (os.filter (fun c => !c.touches g) ++ [⟨b.i, b.j, g :: b.blk⟩]) := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hos c (hU c hc)
        · simp only [List.mem_singleton] at hc
          subst hc
          simpa using Or.inr (hos b hb)
      obtain ⟨h1, h2⟩ := ih _ hO x hx
      refine ⟨fun y hy => ?_, h2⟩
      rcases h1 y hy with hy | hy
      · simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil, List.mem_append,
          List.reverse_cons, List.mem_singleton] at hy
        rcases hy with hy | hy | rfl
        · exact Or.inl (hst y hy)
        · exact Or.inl (List.mem_flatMap.mpr ⟨b, hb, hy⟩)
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem g hy)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        have hc' : c ∈ os := (List.mem_filter.mp hc).1
        refine ⟨fun y hy => Or.inl ?_, fun i j gs' h => ?_⟩
        · simp only [OpenBlk.emit, Block.gates, List.mem_reverse] at hy
          exact List.mem_flatMap.mpr ⟨c, hc', List.mem_reverse.mpr hy⟩
        · simp only [OpenBlk.emit, Block.pair.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact mem_gPairs_reverse.mpr (hos c hc')
      · split at hx
        · next a b' hp =>
          have hg : s(a, b') ∈ gatePairs g := by
            cases g <;> simp only [pairOf?, Option.ite_none_left_eq_some, reduceCtorEq,
              Option.some.injEq, Prod.mk.injEq] at hp <;> simp [gatePairs, hp.2.1, hp.2.2]
          have hO : Opened (os.filter (fun c => !c.touches g) ++ [⟨a, b', [g]⟩]) := by
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · exact hos c (hU c hc)
            · simp only [List.mem_singleton] at hc
              subst hc
              simpa using hg
          obtain ⟨h1, h2⟩ := ih _ hO x hx
          refine ⟨fun y hy => ?_, h2⟩
          rcases h1 y hy with hy | hy
          · simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil,
              List.mem_append, List.reverse_cons, List.reverse_nil, List.nil_append,
              List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact Or.inl (hst y hy)
            · exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem g hy)
        · rcases List.mem_cons.mp hx with rfl | hx
          · refine ⟨fun y hy => ?_, fun i j gs' h => by cases h⟩
            simp only [Block.gates, List.mem_singleton] at hy
            exact Or.inr (hy ▸ List.mem_cons_self)
          · have hO : Opened (os.filter (fun c => !c.touches g)) := fun c hc => hos c (hU c hc)
            obtain ⟨h1, h2⟩ := ih _ hO x hx
            refine ⟨fun y hy => ?_, h2⟩
            rcases h1 y hy with hy | hy
            · exact Or.inl (hst y hy)
            · exact Or.inr (List.mem_cons_of_mem g hy)

/-- A KAK template on `(i, j)` has its two-qubit gates on the pair `s(i, j)`. -/
theorem gPairs_tmplGatesQ (k : Fin 4) (i j : Fin n) (θ : Fin 15 → PiLin) :
    ∀ p ∈ gPairs (tmplGatesQ k i j θ), p = s(i, j) := by
  fin_cases k <;> simp [tmplGatesQ, tmplGatesA, gatePairs]

variable {β : Type}

/-- A segment of the KAK pass keeps the pairs of its block. -/
theorem gPairs_blockEmit_subset (fit : BlockFit n β) (b : Block n)
    (hb : ∀ i j gs, b = .pair i j gs → s(i, j) ∈ gPairs gs) :
    gPairs (blockEmit fit b).1 ⊆ gPairs b.gates := by
  cases b with
  | gate g => exact List.Subset.refl _
  | pair i j gs =>
    simp only [blockEmit, Block.gates]
    split
    · split
      · intro p hp
        rw [gPairs_tmplGatesQ _ _ _ _ p hp]
        exact hb i j gs rfl
      · exact List.Subset.refl _
    · exact List.Subset.refl _

/-- **The KAK pass keeps connectivity**, whatever the fitter answers. -/
theorem gPairs_kakEmit_subset (fit : BlockFit n β) (l : List (Gate n)) :
    gPairs (kakEmit fit l).1 ⊆ gPairs l := by
  rw [kakEmit_fst]
  intro p hp
  obtain ⟨x, hx, hpx⟩ := mem_gPairs.mp hp
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
  have hs := collectAux_spec l [] (by simp [Opened]) b hb
  have h1 := gPairs_blockEmit_subset fit b hs.2 (mem_gPairs.mpr ⟨x, hxb, hpx⟩)
  obtain ⟨y, hy, hpy⟩ := mem_gPairs.mp h1
  refine mem_gPairs.mpr ⟨y, ?_, hpy⟩
  simpa [stGates] using hs.1 y hy

end KAK

section ZYZ

open Synthesis.ZYZPass

/-- The gate segments of the run scan are gates of its input. -/
theorem runAux_gate_mem (l : List (Gate n)) :
    ∀ v : Vector (List (Gate n)) n, ∀ s ∈ runAux v l, ∀ g, s = .gate g → g ∈ l := by
  induction l with
  | nil =>
    intro v s hs g h
    subst h
    simp [runAux, emitRuns] at hs
  | cons x xs ih =>
    intro v s hs g h
    simp only [runAux] at hs
    split at hs
    · exact List.mem_cons_of_mem x (ih _ s hs g h)
    · rcases List.mem_append.mp hs with hs | hs
      · subst h
        simp [emitRunsL] at hs
      · rcases List.mem_cons.mp hs with rfl | hs
        · cases h
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem x (ih _ s hs g h)

/-- A run template has no pair. -/
theorem gPairs_runTemplate (a : Synthesis.ZYZPass.Axis) (q : Fin n) (θ : Fin 3 → PiLin) :
    gPairs (runTemplate a q θ) = [] := by
  cases a <;> simp [runTemplate, xyxGatesQ, Synthesis.KAK.zyzGatesQ, gPairs, gatePairs,
    OpenQASMImport.rxGates]

variable {β : Type}

/-- **The ZYZ pass keeps connectivity**, whatever the fitter answers. -/
theorem gPairs_zyzEmit_subset (fit : ZFit n β) (l : List (Gate n)) :
    gPairs (zyzEmit fit l).1 ⊆ gPairs l := by
  rw [zyzEmit_fst]
  intro p hp
  obtain ⟨x, hx, hpx⟩ := mem_gPairs.mp hp
  obtain ⟨si, hsi, hxs⟩ := List.mem_flatMap.mp hx
  have hs : si.1 ∈ collectRuns l := List.fst_mem_of_mem_zipIdx hsi
  rcases hseg : si.1 with g | ⟨q, gs⟩
  · rw [hseg] at hxs
    simp only [segEmit, List.mem_singleton] at hxs
    subst hxs
    exact mem_gPairs.mpr ⟨x, runAux_gate_mem l _ si.1 hs x hseg, hpx⟩
  · rw [hseg] at hxs hs
    have hv := valid_collectRuns l _ hs
    simp only [segEmit] at hxs
    split at hxs
    · have h0 := mem_gPairs.mpr ⟨x, hxs, hpx⟩
      rw [gPairs_runTemplate] at h0
      simp at h0
    · have hq := hv x hxs
      cases x <;> simp [oneQ?] at hq <;> simp [gatePairs] at hpx

end ZYZ

/-- A stage keeps connectivity: the two-qubit gates of its output lie on pairs of its input. -/
def StagePairs (stage : Circuit n → Optimization.ResynthLevel.Resynth n) : Prop :=
  ∀ c, gPairs (stage c).out ⊆ gPairs (circuitToList c)

/-- **The resynthesis level keeps connectivity**, at every pair of fits. -/
theorem stagePairs_resynthAt
    (kf : Synthesis.KAKPassSmall.BlockFit n Optimization.ResynthLevel.Payload)
    (zf : Array Synthesis.ZYZPass.Axis →
      Synthesis.ZYZPass.ZFit n Optimization.ResynthLevel.Payload) :
    StagePairs (Optimization.ResynthLevel.resynthAt kf zf) := by
  intro c
  simp only [Optimization.ResynthLevel.resynthAt, Optimization.ResynthLevel.Resynth.ofKak]
  exact List.Subset.trans (gPairs_zyzEmit_subset _ _)
    (List.Subset.trans (gPairs_kakEmit_subset _ _) (gPairs_level2Gates_subset c))

/-- The resynthesis level at the checked fits, with or without the T-guard, keeps
connectivity. -/
theorem stagePairs_resynthT (tSafe : Bool) :
    StagePairs (Optimization.ResynthLevel.resynthT (n := n) tSafe) := fun c =>
  stagePairs_resynthAt
    (Optimization.ResynthLevel.tGuardFit tSafe Synthesis.QrunchFit.qrunchFitChecked)
    (fun ax => Optimization.ResynthLevel.tGuardZFit tSafe
      (Synthesis.QrunchFit.qrunchZFitChecked ax)) c

/-- The resynthesis level at the checked fits keeps connectivity. -/
theorem stagePairs_resynth : StagePairs (Optimization.ResynthLevel.resynth (n := n)) :=
  stagePairs_resynthT false

/-! ## The round, the iteration and the whole run -/

/-- **One round keeps connectivity**, for a stage that keeps it. -/
theorem cxPairs_round_subset {stage : Circuit n → Optimization.ResynthLevel.Resynth n}
    (hS : StagePairs stage) {qs : List (QGate n)} {o : RoundOut n}
    (h : QrunchRound.round stage qs = some o) : cxPairs o.out ⊆ cxPairs qs := by
  unfold QrunchRound.round at h
  dsimp only at h
  split_ifs at h with h1 h2
  obtain rfl := Option.some.inj h
  refine List.Subset.trans (cxPairs_basisPasses_subset _) (List.Subset.trans (hS _) ?_)
  rw [circuitToList_ofList]
  exact gPairs_flatMap_lowerQ_subset qs

/-- The rounds after the first keep connectivity. -/
theorem cxPairs_iterFrom_subset {stage : Circuit n → Optimization.ResynthLevel.Resynth n}
    (hS : StagePairs stage) (k : ℕ) (l : List (QGate n)) :
    cxPairs (finalOut l (iterFrom stage k l)) ⊆ cxPairs l := by
  induction k generalizing l with
  | zero => exact List.Subset.refl _
  | succ k ih =>
    unfold iterFrom
    split
    · rename_i o ho
      split
      · exact List.Subset.trans (ih o.out) (cxPairs_round_subset hS ho)
      · exact List.Subset.refl _
    · exact List.Subset.refl _

/-- **The iteration keeps connectivity**, for a stage that keeps it. -/
theorem cxPairs_runRounds_subset {stage : Circuit n → Optimization.ResynthLevel.Resynth n}
    (hS : StagePairs stage) (k : ℕ) (qs : List (QGate n)) :
    cxPairs (finalOut qs (runRounds stage k qs)) ⊆ cxPairs qs := by
  unfold runRounds
  split
  · rename_i o ho
    exact List.Subset.trans (cxPairs_iterFrom_subset hS _ o.out) (cxPairs_round_subset hS ho)
  · exact List.Subset.refl _

/-- **The whole run without swap elision keeps connectivity**, for a stage that keeps it. -/
theorem cxPairs_compileQGates_subset {stage : Circuit n → Optimization.ResynthLevel.Resynth n}
    (hS : StagePairs stage) (k : ℕ) (snap : Bool) (qs : List (QGate n)) :
    cxPairs (compileQGates stage k false snap qs).out ⊆ cxPairs qs := by
  simp only [compileQGates]
  refine List.Subset.trans (cxPairs_runRounds_subset hS k _) ?_
  cases snap <;> simp [prepQ, cxPairs_snapQ]

/-! ## Routing on a coupling map -/

/-- A statement list is routed on the coupling map `cg` when each of its qubit pairs is an
edge of the map, in one direction or the other. -/
def Routed (cg : Optimization.HardwareRouting.CouplingGraph n) (l : List (QGate n)) : Prop :=
  ∀ a b : Fin n, s(a, b) ∈ cxPairs l → cg a b = true ∨ cg b a = true

/-- A statement list whose pairs are among those of a routed list is routed. -/
theorem cxPairs_subset_of_routed {cg : Optimization.HardwareRouting.CouplingGraph n}
    {l l' : List (QGate n)} (h : cxPairs l' ⊆ cxPairs l) (hl : Routed cg l) : Routed cg l' :=
  fun a b hab => hl a b (h hab)

/-- **Route, then compile**: the whole run without swap elision, at a stage that keeps
connectivity, maps a statement list routed on a coupling map to one routed on the map. -/
theorem routed_compileQGates {cg : Optimization.HardwareRouting.CouplingGraph n}
    {stage : Circuit n → Optimization.ResynthLevel.Resynth n} (hS : StagePairs stage) (k : ℕ)
    (snap : Bool) {qs : List (QGate n)} (hq : Routed cg qs) :
    Routed cg (compileQGates stage k false snap qs).out :=
  cxPairs_subset_of_routed (cxPairs_compileQGates_subset hS k snap qs) hq

end CatCrypt.Quantum.QrunchConnect
