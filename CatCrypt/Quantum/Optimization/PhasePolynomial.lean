/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit

/-!
# Phase Polynomial Optimization for T-Count Reduction

Phase polynomial optimization (Amy et al. 2014, Nam et al. 2018) represents
a {CNOT, Rz} sub-circuit as a *phase polynomial* over GF(2) parities of the
input bits. By collecting all Rz rotations applied to the same parity, we
can merge angles and cancel redundant T gates:

* T(p) + T(p)       = S(p)            (saves 1 T gate)
* 4 x T(p)          = Z(p)            (saves 3 T gates)
* 8 x T(p)          = I               (saves 8 T gates)

After merging, each surviving (parity, angle) pair is resynthesized as a CNOT
ladder that accumulates the parity onto one wire, an `Rz` on that wire, and the
reversed ladder; the polynomial's linear part is emitted after the ladders.

## Main definitions

* `Parity`              -- XOR set representation (which input bits contribute)
* `ParityState`         -- current parity assignment per qubit
* `PhasePoly`           -- phase polynomial: list of (parity, angle) pairs + CNOT network
* `toPhasePoly`         -- extract phase polynomial from a gate list
* `PhasePoly.optimize`  -- merge same-parity phases, cancel 2π multiples
* `PhasePoly.toCircuit` -- per-term CNOT-ladder resynthesis followed by the CNOT network
* `phasePolyOpt`        -- full pipeline: flatten → extract → optimize → resynthesize

## Main results

* `toPhasePoly_phases_length`    -- extraction records one phase per rotation gate
* `optimize_phases_length_le`    -- optimization does not lengthen the phase list
* `toCircuit_rotationCount_le`   -- resynthesis emits at most one `Rz` per phase
* `rotationCount_phasePolyOpt_le` -- the three steps above compose to a
  non-increase of the rotation count
* `toCircuit_ladder_example`     -- the emitted gate list of a two-qubit parity
  with a trailing CNOT network, pinned by kernel reduction
* `phasePolyOpt_tCount_eq_zero`  -- the pipeline output has T-count 0, because
  resynthesis emits only `Rz` and `CNOT` gates and `circuitTCount` counts only
  `Gate.T` and `Gate.Tdg`

The pipeline has no denotational correctness theorem: no statement here relates
`phasePolyOpt c` to the semantics of `c`.

## References

* Amy, Maslov, Mosca -- Polynomial-time T-depth optimization of Clifford+T
  circuits via matroid partitioning, IEEE Trans. on CAD, 2014
* Nam, Ross, Su, Childs, Maslov -- Automated optimization of large quantum
  circuits with continuous parameters, npj Quantum Information, 2018
-/

@[expose] public section

set_option autoImplicit true

noncomputable section

namespace CatCrypt.Quantum.Optimization.PhasePolynomial

open CatCrypt.Quantum.QCircuit

/-! ## Parity Representation -/

/-- A parity: characteristic function of the XOR set over `n` input bits.
    `p i = true` means input bit `i` participates in this parity. -/
abbrev Parity (n : ℕ) := Fin n → Bool

/-- Parity state: for each of the `n` qubits, which input bits XOR to
    produce the qubit's current value. -/
def ParityState (n : ℕ) := Fin n → Parity n

/-- Initial parity state: qubit `i` holds exactly input bit `i`. -/
def ParityState.initial : ParityState n :=
  fun i j => decide (i = j)

/-- XOR two parities (symmetric difference of bit sets). -/
def Parity.xor (p q : Parity n) : Parity n :=
  fun i => Bool.xor (p i) (q i)

/-- Update parity state after a CNOT(control, target):
    the target qubit's parity becomes `target XOR control`. -/
def ParityState.applyCNOT (st : ParityState n) (ctrl tgt : Fin n) : ParityState n :=
  fun q =>
    if q = tgt then Parity.xor (st ctrl) (st tgt)
    else st q

/-- Decide equality on parities (pointwise Bool equality). -/
instance : DecidableEq (Parity n) :=
  fun p q =>
    if h : ∀ i, p i = q i then
      isTrue (funext h)
    else
      isFalse (fun heq => h (fun i => congr_fun heq i))

/-! ## Phase Polynomial -/

/-- A phase polynomial representation of a {CNOT, Rz} circuit.

    * `phases` -- list of (parity, rotation angle) pairs
    * `cnotNetwork` -- CNOT gates that set up parities (control, target) -/
structure PhasePoly (n : ℕ) where
  /-- Map from parity (XOR pattern) to accumulated phase angle. -/
  phases : List (Parity n × ℝ)
  /-- Linear reversible part: CNOT network as (control, target) pairs. -/
  cnotNetwork : List (Fin n × Fin n)
  deriving Inhabited

/-! ## Extraction: Circuit → Phase Polynomial -/

/-- Process a single gate in the context of a running parity state,
    accumulating phases and CNOTs. -/
def processGate (st : ParityState n) (acc : PhasePoly n) :
    Gate n → ParityState n × PhasePoly n
  | .CNOT c t =>
    let st' := st.applyCNOT c t
    (st', { acc with cnotNetwork := acc.cnotNetwork ++ [(c, t)] })
  | .Rz q θ =>
    let parity := st q
    (st, { acc with phases := acc.phases ++ [(parity, θ)] })
  | .T q =>
    let parity := st q
    (st, { acc with phases := acc.phases ++ [(parity, Real.pi / 4)] })
  | .Tdg q =>
    let parity := st q
    (st, { acc with phases := acc.phases ++ [(parity, -(Real.pi / 4))] })
  | .S q =>
    let parity := st q
    (st, { acc with phases := acc.phases ++ [(parity, Real.pi / 2)] })
  | .Z q =>
    let parity := st q
    (st, { acc with phases := acc.phases ++ [(parity, Real.pi)] })
  | _ => (st, acc)  -- H, X, Y, CZ, RzQ: not in {CNOT, Rz} fragment

/-- Convert a list of gates (assumed to be from the {CNOT, Rz} fragment)
    to a phase polynomial by processing gates left-to-right, tracking
    parity evolution through CNOTs. -/
def toPhasePoly (gs : List (Gate n)) : PhasePoly n :=
  let init : ParityState n × PhasePoly n :=
    (ParityState.initial, ⟨[], []⟩)
  (gs.foldl (fun (st_acc : ParityState n × PhasePoly n) g =>
    processGate st_acc.1 st_acc.2 g) init).2

/-! ## Optimization: Merge Phases -/

/-- Add one (parity, angle) pair to an accumulated phase list: sum the angles
    when the parity already occurs, and append a new entry otherwise. -/
def addPhase (acc : List (Parity n × ℝ)) (pθ : Parity n × ℝ) : List (Parity n × ℝ) :=
  match acc.find? (fun q => decide (pθ.1 = q.1)) with
  | some _ => acc.map (fun q => if pθ.1 = q.1 then (q.1, q.2 + pθ.2) else q)
  | none => acc ++ [pθ]

/-- Merge phases with the same parity by summing their angles. -/
def mergePhases (phases : List (Parity n × ℝ)) : List (Parity n × ℝ) :=
  phases.foldl addPhase []

/-- Remove phases that are multiples of 2π (equivalent to identity). -/
def removeTrivialPhases (phases : List (Parity n × ℝ)) : List (Parity n × ℝ) :=
  phases.filter (fun (_, θ) => θ % (2 * Real.pi) ≠ 0)

/-- Optimize a phase polynomial: merge same-parity phases and remove
    2π-multiples.

    Merging is where the rotation count drops. Two T gates on the same parity
    become a single phase of π/2, four become π, and eight become a 2π multiple
    that `removeTrivialPhases` drops. The resynthesis emits each surviving phase
    as an `Rz`, so this reduction is visible in the number of rotations, not in
    `circuitTCount`. -/
def PhasePoly.optimize (pp : PhasePoly n) : PhasePoly n :=
  { pp with phases := removeTrivialPhases (mergePhases pp.phases) }

/-! ## Resynthesis: Phase Polynomial → Circuit -/

/-- The qubits participating in a parity, in increasing index order. -/
def parityQubits (p : Parity n) : List (Fin n) :=
  (List.finRange n).filter (fun i => p i)

/-- Gate list realizing one (parity, angle) pair. For a parity whose
    participating qubits are `q :: rest`, the list is the CNOT ladder
    `CNOT r q` for each `r ∈ rest`, the rotation `Rz q θ`, then the reversed
    ladder. The ladder gates share the target `q` and have distinct controls, so
    each is involutive and the second half inverts the first. A parity with no
    participating qubit contributes the phase `e^{iθ·0} = 1` and emits no
    gates. -/
def synthesizePhaseGates (p : Parity n) (θ : ℝ) : List (Gate n) :=
  match parityQubits p with
  | [] => []
  | q :: rest =>
    rest.map (fun r => Gate.CNOT r q)
      ++ [Gate.Rz q θ]
      ++ rest.reverse.map (fun r => Gate.CNOT r q)

/-- Circuit realizing one (parity, angle) pair, as the ladder of
    `synthesizePhaseGates`. -/
def synthesizePhase (p : Parity n) (θ : ℝ) : Circuit n :=
  Circuit.ofList (synthesizePhaseGates p θ)

/-- Resynthesize a phase polynomial to a circuit: the per-term ladders of
    `synthesizePhase` in order, followed by the CNOT gates of the polynomial's
    linear part in their recorded order.

    Each ladder rotates by the parity that extraction recorded, which is a
    parity of the input basis state, so the ladders carry the diagonal part of
    the segment and the trailing CNOT list carries its linear part. -/
def PhasePoly.toCircuit (pp : PhasePoly n) : Circuit n :=
  let phaseCircuits := pp.phases.map (fun (p, θ) => synthesizePhase p θ)
  let phasePart := phaseCircuits.foldl (fun acc c => Circuit.seq acc c) Circuit.empty
  Circuit.seq phasePart
    (Circuit.ofList (pp.cnotNetwork.map (fun ct => Gate.CNOT ct.1 ct.2)))

/-! ## Full Pipeline -/

/-- Flatten a circuit to the gate list it applies, left to right. -/
def flattenCircuit : Circuit n → List (Gate n)
  | .empty     => []
  | .gate g c  => g :: flattenCircuit c
  | .seq c₁ c₂ => flattenCircuit c₁ ++ flattenCircuit c₂

/-- Full phase polynomial optimization pipeline:
    flatten → extract phase polynomial → optimize → resynthesize. -/
def phasePolyOpt (c : Circuit n) : Circuit n :=
  (toPhasePoly (flattenCircuit c)).optimize.toCircuit

/-! ## T-Count Metrics -/

/-- Count T and Tdg gates in a gate list. -/
def listTCount : List (Gate n) → ℕ
  | [] => 0
  | g :: gs =>
    (match g with
     | .T _   => 1
     | .Tdg _ => 1
     | _      => 0) + listTCount gs

/-- T-count of a circuit (via flattening). -/
def circuitTCount (c : Circuit n) : ℕ :=
  listTCount (flattenCircuit c)

/-- The T-count of a concatenation is the sum of the T-counts. -/
private theorem listTCount_append (l₁ l₂ : List (Gate n)) :
    listTCount (l₁ ++ l₂) = listTCount l₁ + listTCount l₂ := by
  induction l₁ with
  | nil => simp [listTCount]
  | cons g gs ih => simp [listTCount, ih, Nat.add_assoc]

private theorem flattenCircuit_seq (c₁ c₂ : Circuit n) :
    flattenCircuit (.seq c₁ c₂) = flattenCircuit c₁ ++ flattenCircuit c₂ := by
  simp [flattenCircuit]

private theorem flattenCircuit_ofList (gs : List (Gate n)) :
    flattenCircuit (Circuit.ofList gs) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [Circuit.ofList, flattenCircuit, ih]

private theorem listTCount_map_cnot (l : List (Fin n × Fin n)) :
    listTCount (l.map (fun ct => Gate.CNOT ct.1 ct.2)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [listTCount, ih]

private theorem listTCount_ladder (q : Fin n) (l : List (Fin n)) :
    listTCount (l.map (fun r => Gate.CNOT r q)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [listTCount, ih]

private theorem synthesizePhase_tCount (p : Parity n) (θ : ℝ) :
    circuitTCount (synthesizePhase p θ) = 0 := by
  simp only [circuitTCount, synthesizePhase, flattenCircuit_ofList, synthesizePhaseGates]
  cases parityQubits p with
  | nil => rfl
  | cons q rest =>
    simp only [listTCount_append, listTCount, listTCount_ladder]

/-- The resynthesized circuit has T-count 0: `toCircuit` emits only `Rz` and
    `CNOT` gates, and `circuitTCount` counts only `Gate.T` and `Gate.Tdg`. -/
theorem toCircuit_tCount (pp : PhasePoly n) :
    circuitTCount pp.toCircuit = 0 := by
  simp only [PhasePoly.toCircuit, circuitTCount, flattenCircuit_seq, listTCount_append,
    flattenCircuit_ofList]
  rw [listTCount_map_cnot, Nat.add_zero]
  suffices h : ∀ (cs : List (Circuit n)) (acc : Circuit n),
      listTCount (flattenCircuit acc) = 0 →
      (∀ c ∈ cs, circuitTCount c = 0) →
      listTCount (flattenCircuit (cs.foldl (fun a c => Circuit.seq a c) acc)) = 0 by
    apply h
    · simp [flattenCircuit, listTCount]
    · intro c hc
      simp [List.mem_map] at hc
      obtain ⟨p, θ, _, rfl⟩ := hc
      exact synthesizePhase_tCount p θ
  intro cs acc hacc hcs
  induction cs generalizing acc with
  | nil => exact hacc
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp only [flattenCircuit_seq, listTCount_append]
      have := hcs c (.head _)
      simp [circuitTCount] at this
      omega
    · intro c' hc'
      exact hcs c' (.tail _ hc')

/-- The pipeline output has T-count 0 for every input circuit. Resynthesis emits
    only `Rz` and `CNOT` gates, and `circuitTCount` counts only `Gate.T` and
    `Gate.Tdg`, so the output count is 0 independently of what the merging step
    did. Any inequality `circuitTCount (phasePolyOpt c) ≤ f c` is a consequence
    of this equation and constrains neither `mergePhases` nor
    `removeTrivialPhases`. -/
theorem phasePolyOpt_tCount_eq_zero (c : Circuit n) :
    circuitTCount (phasePolyOpt c) = 0 := by
  simp only [phasePolyOpt, toCircuit_tCount]

/-! ## Rotation Count -/

/-- Count the diagonal rotation gates (`T`, `Tdg`, `S`, `Z`, `Rz`) in a gate
    list. These are the gates `processGate` records as phases. -/
def rotationCount : List (Gate n) → ℕ
  | [] => 0
  | g :: gs =>
    (match g with
     | .T _ => 1
     | .Tdg _ => 1
     | .S _ => 1
     | .Z _ => 1
     | .Rz _ _ => 1
     | _ => 0) + rotationCount gs

/-- Rotation count of a circuit (via flattening). -/
def circuitRotationCount (c : Circuit n) : ℕ :=
  rotationCount (flattenCircuit c)

private theorem rotationCount_append (l₁ l₂ : List (Gate n)) :
    rotationCount (l₁ ++ l₂) = rotationCount l₁ + rotationCount l₂ := by
  induction l₁ with
  | nil => simp [rotationCount]
  | cons g gs ih => simp [rotationCount, ih, Nat.add_assoc]

private theorem rotationCount_ladder (q : Fin n) (l : List (Fin n)) :
    rotationCount (l.map (fun r => Gate.CNOT r q)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [rotationCount, ih]

private theorem rotationCount_map_cnot (l : List (Fin n × Fin n)) :
    rotationCount (l.map (fun ct => Gate.CNOT ct.1 ct.2)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [rotationCount, ih]

/-! ### Extraction records one phase per rotation gate -/

private theorem processGate_phases_length (st : ParityState n) (acc : PhasePoly n)
    (g : Gate n) :
    (processGate st acc g).2.phases.length = acc.phases.length + rotationCount [g] := by
  cases g <;> simp [processGate, rotationCount]

private theorem foldl_processGate_phases_length (gs : List (Gate n)) :
    ∀ (st : ParityState n) (acc : PhasePoly n),
      ((gs.foldl (fun st_acc g => processGate st_acc.1 st_acc.2 g) (st, acc)).2).phases.length
        = acc.phases.length + rotationCount gs := by
  induction gs with
  | nil => intro st acc; simp [rotationCount]
  | cons g gs ih =>
    intro st acc
    simp only [List.foldl_cons]
    rw [ih (processGate st acc g).1 (processGate st acc g).2,
      processGate_phases_length]
    simp [rotationCount, Nat.add_assoc]

/-- The extracted phase polynomial has one phase entry per rotation gate. -/
theorem toPhasePoly_phases_length (gs : List (Gate n)) :
    (toPhasePoly gs).phases.length = rotationCount gs := by
  simp [toPhasePoly, foldl_processGate_phases_length]

/-! ### Optimization does not lengthen the phase list -/

private theorem addPhase_length_le (acc : List (Parity n × ℝ)) (pθ : Parity n × ℝ) :
    (addPhase acc pθ).length ≤ acc.length + 1 := by
  unfold addPhase
  split <;> simp

private theorem foldl_addPhase_length_le (l : List (Parity n × ℝ)) :
    ∀ acc : List (Parity n × ℝ),
      (l.foldl addPhase acc).length ≤ acc.length + l.length := by
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    have h₁ := ih (addPhase acc a)
    have h₂ := addPhase_length_le acc a
    omega

/-- Merging phases does not lengthen the phase list. -/
theorem mergePhases_length_le (l : List (Parity n × ℝ)) :
    (mergePhases l).length ≤ l.length := by
  have := foldl_addPhase_length_le l []
  simpa [mergePhases] using this

/-- Optimization does not lengthen the phase list. -/
theorem optimize_phases_length_le (pp : PhasePoly n) :
    pp.optimize.phases.length ≤ pp.phases.length :=
  le_trans (List.length_filter_le _ _) (mergePhases_length_le _)

/-! ### Resynthesis emits at most one rotation per phase -/

private theorem synthesizePhase_rotationCount (p : Parity n) (θ : ℝ) :
    circuitRotationCount (synthesizePhase p θ) ≤ 1 := by
  simp only [circuitRotationCount, synthesizePhase, flattenCircuit_ofList,
    synthesizePhaseGates]
  cases parityQubits p with
  | nil => simp [rotationCount]
  | cons q rest =>
    simp only [rotationCount_append, rotationCount, rotationCount_ladder]
    omega

private theorem rotationCount_foldl_seq (cs : List (Circuit n)) :
    ∀ (acc : Circuit n) (k : ℕ), circuitRotationCount acc ≤ k →
      (∀ c ∈ cs, circuitRotationCount c ≤ 1) →
      circuitRotationCount (cs.foldl (fun a c => Circuit.seq a c) acc) ≤ k + cs.length := by
  induction cs with
  | nil => intro acc k hacc _; simpa using hacc
  | cons c rest ih =>
    intro acc k hacc hcs
    simp only [List.foldl_cons, List.length_cons]
    have hstep : circuitRotationCount (Circuit.seq acc c) ≤ k + 1 := by
      have := hcs c (.head _)
      simp only [circuitRotationCount, flattenCircuit_seq, rotationCount_append]
      simp only [circuitRotationCount] at hacc this
      omega
    have := ih (Circuit.seq acc c) (k + 1) hstep (fun c' hc' => hcs c' (.tail _ hc'))
    omega

/-- Resynthesis emits at most one rotation gate per phase entry. -/
theorem toCircuit_rotationCount_le (pp : PhasePoly n) :
    circuitRotationCount pp.toCircuit ≤ pp.phases.length := by
  simp only [circuitRotationCount, PhasePoly.toCircuit, flattenCircuit_seq,
    rotationCount_append, flattenCircuit_ofList, rotationCount_map_cnot, Nat.add_zero]
  have h := rotationCount_foldl_seq (pp.phases.map (fun pθ => synthesizePhase pθ.1 pθ.2))
    Circuit.empty 0 (by simp [circuitRotationCount, flattenCircuit, rotationCount])
    (by
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨pθ, _, rfl⟩ := hc
      exact synthesizePhase_rotationCount _ _)
  simpa [circuitRotationCount] using h

/-- The pipeline does not increase the number of diagonal rotation gates.

    Extraction records one phase per rotation gate, merging and 2π-removal only
    shorten the phase list, and resynthesis emits at most one `Rz` per surviving
    phase. The inequality is an upper bound, so it is satisfied by any pass that
    emits no rotations; the content that constrains this pipeline is in the three
    steps it composes, `toPhasePoly_phases_length`, `optimize_phases_length_le`
    and `toCircuit_rotationCount_le`. -/
theorem rotationCount_phasePolyOpt_le (c : Circuit n) :
    circuitRotationCount (phasePolyOpt c) ≤ circuitRotationCount c := by
  calc circuitRotationCount (phasePolyOpt c)
      ≤ (toPhasePoly (flattenCircuit c)).optimize.phases.length :=
        toCircuit_rotationCount_le _
    _ ≤ (toPhasePoly (flattenCircuit c)).phases.length := optimize_phases_length_le _
    _ = rotationCount (flattenCircuit c) := toPhasePoly_phases_length _

/-! ## Concrete Examples -/

/-- A three-qubit phase polynomial with one phase on the parity `q0 XOR q2` and
    the linear part `CNOT(q0, q1)`. -/
def ladderExample (θ : ℝ) : PhasePoly 3 :=
  ⟨[(fun i => decide (i ≠ 1), θ)], [(0, 1)]⟩

/-- The gate list `toCircuit` emits for `ladderExample`: the ladder
    `CNOT(q2, q0)` accumulating the parity `q0 XOR q2` onto wire `q0`, the
    rotation on `q0`, the reversed ladder, and the polynomial's own
    `CNOT(q0, q1)`. -/
theorem toCircuit_ladder_example (θ : ℝ) :
    flattenCircuit (ladderExample θ).toCircuit
      = [Gate.CNOT 2 0, Gate.Rz 0 θ, Gate.CNOT 2 0, Gate.CNOT 0 1] := rfl

/-- Example: T(0); CNOT(0,1); T(0) on 2 qubits.
    Both T gates act on the same parity (qubit 0 holds input bit 0 at both
    points, since CNOT does not change qubit 0's parity), so `mergePhases` sums
    their angles into a single phase of π/2 on that parity. -/
def tMergeExample : Circuit 2 :=
  .gate (.T 0) (.gate (.CNOT 0 1) (.gate (.T 0) .empty))

/-- A two-qubit circuit applying the merged π/2 phase as `S(0)`, followed by
    `CNOT(0,1)`. `phasePolyOpt` emits the merged phase as `Rz(0, π/2)` rather
    than `S(0)`, so it does not produce this circuit syntactically. -/
def tMergeExpected : Circuit 2 :=
  .gate (.S 0) (.gate (.CNOT 0 1) .empty)

/-- The example circuit has T-count 2 before optimization. -/
theorem tMergeExample_tCount : circuitTCount tMergeExample = 2 := by rfl

/-- The expected optimized circuit has T-count 0. -/
theorem tMergeExpected_tCount : circuitTCount tMergeExpected = 0 := by rfl

end CatCrypt.Quantum.Optimization.PhasePolynomial
