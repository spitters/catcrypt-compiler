/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.Optimization.CommutationRules
public import CatCrypt.Quantum.Optimization.RotationMerging

/-!
# Phase Polynomial Rotation Merging (V2)

Enhanced rotation merging that handles non-adjacent Rz gates across larger
windows using a phase polynomial representation. V1 (RotationMerging.lean) only
merges adjacent Rz gates reachable by commuting through intermediate gates; V2
extracts a phase polynomial from circuit segments, optimizes the polynomial
(merging terms with the same parity and dropping zero-angle terms), and
resynthesizes the circuit.

## Key Insight

When Rz gates are separated by CNOTs (common in chemistry and variational
circuits), the phase polynomial representation lets us merge them even though
they are non-adjacent:

```
Rz(alpha, q0); CNOT(q0,q1); Rz(beta, q0)
  --> PhasePolynomial: terms [(q0, alpha), (q0, beta)], CNOTs [(q0,q1)]
  --> merged terms: [(q0, alpha+beta)]
  --> Rz(alpha+beta, q0); CNOT(q0,q1)
```

`CNOT(q0,q1)` rewrites the parity of `q1`, leaving the parity of `q0` alone, so
both rotations carry the parity `q0` and merge.

## Main definitions

* `PhasePolynomial n`       -- phase polynomial: parity-angle pairs + CNOT structure
* `extractPhasePolynomial`  -- extract polynomial from a gate list
* `optimizePhasePolynomial` -- merge same-parity terms, drop zero-angle terms
* `resynthesizeCircuit`     -- resynthesize optimized gate list from polynomial
* `phasePolynomialOpt`      -- full pipeline: extract, optimize, resynthesize

## References

* Amy, Maslov, Mosca -- *Polynomial-Time T-depth Optimization of Clifford+T
  Circuits Via Matroid Partitioning*, IEEE TQC 2014
* Nam et al. -- *Automated optimization of large quantum circuits with
  continuous parameters*, npj Quantum Information 2018
-/

@[expose] public section

set_option autoImplicit true

noncomputable section

namespace CatCrypt.Quantum.Optimization.RotationMergingV2

open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Optimization.CommutationRules
open CatCrypt.Quantum.Optimization.RotationMerging

/-! ## Phase Polynomial Representation -/

/-- A parity term: a subset of qubits (represented as a sorted list of `Fin n`)
    paired with a rotation angle. The parity represents the XOR of the
    corresponding qubit values. -/
structure ParityTerm (n : ℕ) where
  /-- Qubit indices whose parity this term represents (sorted). -/
  parity : List (Fin n)
  /-- Rotation angle for this parity term. -/
  angle  : ℝ

/-- Phase polynomial representation of a circuit region.

    A phase polynomial consists of:
    - A list of parity-angle terms: each represents an Rz rotation controlled
      by the XOR of a subset of qubits.
    - A CNOT structure: the sequence of CNOT gates that defines the parity
      transformations.

    The semantics is: the product of `Rz(angle_i, parity_i)` gates interleaved
    with the CNOT structure. -/
structure PhasePolynomial (n : ℕ) where
  /-- Parity-angle terms. -/
  terms : List (ParityTerm n)
  /-- CNOT structure (control, target) pairs. -/
  cnots : List (Fin n × Fin n)

/-! ## XOR Parity Tracking -/

/-- Parity state: for each qubit, track which original qubits its current
    value depends on (via XOR from CNOTs). Initially qubit `i` depends only
    on itself. -/
def ParityState (n : ℕ) := Fin n → List (Fin n)

/-- Initial parity state: each qubit depends only on itself. -/
def initParityState (n : ℕ) : ParityState n :=
  fun i => [i]

/-- Toggle membership in a sorted list (symmetric difference with singleton). -/
def toggleMember [DecidableEq α] [Ord α] (x : α) : List α → List α
  | [] => [x]
  | a :: rest =>
    if x == a then rest
    else if compare x a == .lt then x :: a :: rest
    else a :: toggleMember x rest

/-- Apply a CNOT to the parity state: target := target XOR control.
    In parity terms, the target qubit's parity list gets XORed with
    the control qubit's parity list. A CNOT whose control and target coincide
    is the identity gate, and leaves the parity state unchanged. -/
def applyCNOTToParity (ps : ParityState n) (ctrl tgt : Fin n) : ParityState n :=
  if ctrl == tgt then ps
  else
    fun i =>
      if i == tgt then
        -- XOR the control's parity into the target's parity
        let ctrlParity := ps ctrl
        ctrlParity.foldl (fun acc q => toggleMember q acc) (ps tgt)
      else ps i

/-! ## Phase Polynomial Extraction -/

/-- Extract a phase polynomial from a list of gates.

    Processes gates left to right:
    - Rz-family gates contribute a parity term using the current parity of
      their target qubit.
    - CNOT gates update the parity state and are recorded in the CNOT structure.
    - Gates outside the Rz family and CNOT are discarded. `optimizeSegments`
      only passes segments whose gates are all Rz-family or CNOT, so that arm
      is unreachable from the pipeline. -/
def extractPhasePolynomial (gs : List (Gate n)) :
    PhasePolynomial n :=
  let rec go : List (Gate n) → ParityState n →
      List (ParityTerm n) → List (Fin n × Fin n) → PhasePolynomial n
    | [], _, terms, cnots => ⟨terms.reverse, cnots.reverse⟩
    | g :: rest, ps, terms, cnots =>
      match isRzGate g with
      | some (q, θ) =>
        let parity := ps q
        let term : ParityTerm n := ⟨parity, θ⟩
        go rest ps (term :: terms) cnots
      | none =>
        match g with
        | .CNOT c t => go rest (applyCNOTToParity ps c t) terms ((c, t) :: cnots)
        | _ => go rest ps terms cnots
  go gs (initParityState n) [] []

/-! ## Phase Polynomial Optimization -/

/-- Check if two parity lists are equal (both should be sorted). -/
def parityEq [DecidableEq α] (p1 p2 : List α) : Bool :=
  p1 == p2

/-- Merge terms with the same parity by adding their angles.
    Uses a simple quadratic scan (sufficient for practical circuit sizes). -/
def mergeTerms (terms : List (ParityTerm n)) : List (ParityTerm n) :=
  let rec go : List (ParityTerm n) → List (ParityTerm n) → List (ParityTerm n)
    | [], acc => acc.reverse
    | t :: rest, acc =>
      -- Check if any term in acc has the same parity
      let (merged, found) := acc.foldl (fun (acc', found') t' =>
        if !found' && parityEq t.parity t'.parity then
          (⟨t'.parity, t'.angle + t.angle⟩ :: acc', true)
        else (t' :: acc', found')) ([], false)
      if found then go rest merged.reverse
      else go rest (t :: acc)
  go terms []

/-- Test whether an angle is zero. Angles are exact reals, so this is equality
    with `0` and does not identify nonzero multiples of 2pi. -/
def isZeroAngle (θ : ℝ) : Bool :=
  decide (θ = 0)

/-- Remove terms with zero angle. -/
def removeZeroTerms (terms : List (ParityTerm n)) : List (ParityTerm n) :=
  terms.filter (fun t => !isZeroAngle t.angle)

/-- Optimize a phase polynomial:
    1. Merge terms with the same parity (add angles).
    2. Remove terms with zero angle (identity rotations). -/
def optimizePhasePolynomial (pp : PhasePolynomial n) : PhasePolynomial n :=
  { pp with terms := removeZeroTerms (mergeTerms pp.terms) }

/-! ## Circuit Resynthesis -/

/-- Gate list realizing one parity term `⟨q :: rest, θ⟩`: a CNOT ladder
    accumulating the parity of `q :: rest` onto wire `q`, the rotation
    `Rz q θ`, then the reversed ladder restoring wire `q`. The ladder gates
    share the target `q` and have distinct controls drawn from `rest`, so they
    commute with each other and are involutive, and the second half inverts the
    first. A term with an empty parity contributes the phase `e^{iθ·0} = 1`, so
    it emits no gates. -/
def termToGates (t : ParityTerm n) : List (Gate n) :=
  match t.parity with
  | q :: rest =>
    rest.map (fun r => Gate.CNOT r q)
      ++ [Gate.Rz q t.angle]
      ++ rest.reverse.map (fun r => Gate.CNOT r q)
  | [] => []

/-- Resynthesize a gate list from a phase polynomial.

    The emitted list is the concatenation of the per-term ladders of
    `termToGates`, followed by the `CNOT` gates of the polynomial's CNOT
    structure in their original order. Each ladder applies its rotation to the
    parity the extraction recorded, which is a parity of the input basis state,
    so the ladders together form the diagonal part of the segment and the
    trailing CNOT list forms its linear part. -/
def resynthesizeCircuit (pp : PhasePolynomial n) : List (Gate n) :=
  let phaseGates := pp.terms.flatMap termToGates
  let cnotGates := pp.cnots.map (fun (c, t) => Gate.CNOT c t)
  phaseGates ++ cnotGates

/-! ## Full Pipeline -/

/-- Partition a gate list into phase-polynomial-amenable segments
    (containing only Rz-family and CNOT gates) and non-amenable segments. -/
def isPhasePolyGate : Gate n → Bool
  | .CNOT _ _ => true
  | g => isRzFamily g

/-- Split a gate list at the first non-phase-poly gate. -/
def splitAtNonPhasePoly (gs : List (Gate n)) :
    List (Gate n) × List (Gate n) :=
  let pfx := gs.takeWhile isPhasePolyGate
  let sfx := gs.dropWhile isPhasePolyGate
  (pfx, sfx)

/-- Apply phase polynomial optimization to each amenable segment of a gate list.
    Uses fuel for termination. -/
def optimizeSegments (gs : List (Gate n)) (fuel : ℕ := gs.length + 1) :
    List (Gate n) :=
  match fuel with
  | 0 => gs
  | fuel' + 1 =>
    match gs with
    | [] => []
    | _ =>
      let (segment, rest) := splitAtNonPhasePoly gs
      if segment.isEmpty then
        -- First gate is non-phase-poly; emit it and continue
        match gs with
        | [] => []
        | g :: gs' => g :: optimizeSegments gs' fuel'
      else
        -- Optimize the segment via phase polynomial
        let pp := extractPhasePolynomial segment
        let ppOpt := optimizePhasePolynomial pp
        let optimized := resynthesizeCircuit ppOpt
        optimized ++ optimizeSegments rest fuel'

/-- The phase polynomial optimization pass: flatten, optimize segments, rebuild. -/
def phasePolynomialOpt (c : Circuit n) : Circuit n :=
  let gs := circuitToList c
  Circuit.ofList (optimizeSegments gs)

/-! ## Examples -/

/-- Wire signature of a gate: `(0, q, q)` for `Rz q θ`, `(1, c, t)` for
    `CNOT c t`, and `(2, 0, 0)` for every other gate. Rotation angles are reals
    with no executable equality test, so an emitted gate list is compared
    through this projection. -/
def gateSig : Gate n → ℕ × ℕ × ℕ
  | .Rz q _   => (0, q.val, q.val)
  | .CNOT c t => (1, c.val, t.val)
  | _         => (2, 0, 0)

/-- Resynthesis of the segment `CNOT(q0,q1); T q1`. The rotation carries the
    parity `q0 XOR q1`, so the ladder accumulates that parity onto wire `q0`
    with `CNOT(q1,q0)`, rotates wire `q0`, unwinds, and the segment's own
    `CNOT(q0,q1)` follows. -/
theorem resynthesize_cnotThenT_sig :
    (resynthesizeCircuit
        (extractPhasePolynomial ([Gate.CNOT 0 1, Gate.T 1] : List (Gate 2)))).map gateSig
      = [(1, 1, 0), (0, 0, 0), (1, 1, 0), (1, 0, 1)] := rfl

/-- V1 rotation merging on `Rz(θ, q0); CNOT(q0,q1); Rz(φ, q0)`: both rotations
    sit on the CNOT's **control** wire, where `gateCommutes` certifies the
    slide, so `mergeRotations` emits `Rz(θ+φ, q0); CNOT(q0,q1)`. The angles are
    reals with no executable equality test, so the emitted list is compared
    through `gateSig`. -/
theorem mergeRotations_rz_cnot_control_sig (θ φ : ℝ) :
    (mergeRotations ([Gate.Rz 0 θ, Gate.CNOT 0 1, Gate.Rz 0 φ] : List (Gate 2))).map gateSig
      = [(0, 0, 0), (1, 0, 1)] := rfl

/-- V1 rotation merging on `Rz(θ, q1); CNOT(q0,q1); Rz(φ, q1)`: the rotations
    sit on the CNOT's **target** wire, where they do not commute with it, so the
    pass leaves all three gates in place. -/
theorem mergeRotations_rz_cnot_target_sig (θ φ : ℝ) :
    (mergeRotations ([Gate.Rz 1 θ, Gate.CNOT 0 1, Gate.Rz 1 φ] : List (Gate 2))).map gateSig
      = [(0, 1, 1), (1, 0, 1), (0, 1, 1)] := rfl

/-- Example: Rz gates separated by a CNOT on the same qubit.
    V2 uses the phase polynomial to merge them.

    ```
    Rz(pi/4, q0); CNOT(q0, q1); Rz(pi/4, q0)
    ```

    Phase polynomial:
    - term 1: parity = [q0], angle = pi/4
    - CNOT(q0, q1) updates parity: q1 -> q0 XOR q1
    - term 2: parity = [q0], angle = pi/4
    - After merging: parity = [q0], angle = pi/2

    Resynthesized: `Rz(pi/2, q0); CNOT(q0, q1)` -/
noncomputable def exampleV2Before : Circuit 2 :=
  .gate (.Rz 0 (Real.pi / 4))
    (.gate (.CNOT 0 1)
      (.gate (.Rz 0 (Real.pi / 4)) .empty))

/-- The V2 example has 3 gates before optimization. -/
theorem exampleV2Before_gateCount :
    exampleV2Before.gateCount = 3 := rfl

/-- Example: T-depth reduction via phase polynomial.
    Four T gates on the same qubit with CNOTs between them.

    The four rotations carry the parities `[q0], [q0], [q1], [q1]`, since
    `CNOT(q1,q0)` rewrites the parity of `q0` to `q1`. Merging pairs them into
    `(q0, pi/2)` and `(q1, pi/2)`, both single-qubit parities, so the ladders
    are bare rotations and the resynthesis is
    `Rz(pi/2, q0); Rz(pi/2, q1); CNOT(q0,q1); CNOT(q1,q0); CNOT(q0,q1)`. -/
noncomputable def exampleTDepth : Circuit 2 :=
  .gate (.T 0)
    (.gate (.CNOT 0 1)
      (.gate (.T 0)
        (.gate (.CNOT 1 0)
          (.gate (.T 0)
            (.gate (.CNOT 0 1)
              (.gate (.T 0) .empty))))))

/-- The T-depth example has 7 gates. -/
theorem exampleTDepth_gateCount :
    exampleTDepth.gateCount = 7 := rfl

end CatCrypt.Quantum.Optimization.RotationMergingV2
