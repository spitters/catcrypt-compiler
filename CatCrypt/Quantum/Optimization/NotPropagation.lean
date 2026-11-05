/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit

/-!
# NOT (X) Gate Propagation

Push X (NOT) gates through CNOTs to enable more cancellations.  This is
a standard optimization pass in VOQC (Hietala et al., POPL 2021) and
other verified quantum compilers.

## Key Identities

* `X(t); CNOT(c,t) = CNOT(c,t); X(t)` -- X commutes past target of CNOT
* `X(c); CNOT(c,t) = CNOT(c,t); X(c); X(t)` -- X on control propagates to both
* `X; X = I` -- X is self-inverse (involution)
* `X; Z = -Z; X` (up to global phase, which is invisible in density matrices)

## Main definitions

* `propagateNot`                -- push X gates rightward through CNOTs
* `cancelXX`                    -- remove adjacent X; X pairs
* `notPropagationPass`          -- full pass: propagate then cancel
* `notPropagationPass_gateCount_le` -- does not increase gate count (proved)

Semantic preservation is stated over `unitaryDenote` in the companion module
`NotPropSound` (`notPropagationPass_unitaryDenote`).

## References

* Hietala et al. -- A Verified Optimizer for Quantum Circuits (POPL 2021)
* Amy et al. -- A Meet-in-the-Middle Algorithm for Fast Synthesis of
  Depth-Optimal Quantum Circuits, IEEE Trans. on CAD, 2013
-/

@[expose] public section

set_option autoImplicit true

noncomputable section

namespace CatCrypt.Quantum.Optimization.NotPropagation

open CatCrypt.Quantum.QCircuit

/-! ## X Gate Detection -/

/-- Check if a gate is an X (NOT) gate and return its target qubit. -/
def isXGate : Gate n → Option (Fin n)
  | .X i => some i
  | _    => none

/-- Check if a gate is a CNOT and return (control, target). -/
def isCNOT : Gate n → Option (Fin n × Fin n)
  | .CNOT c t => some (c, t)
  | _         => none

/-! ## X; X Cancellation -/

/-- Remove adjacent X; X pairs from a gate list (self-inverse cancellation).
    Uses fuel for termination. -/
def cancelXX (gs : List (Gate n)) (fuel : ℕ := gs.length + 1) :
    List (Gate n) :=
  match fuel with
  | 0 => gs
  | fuel' + 1 =>
    match gs with
    | [] => []
    | [g] => [g]
    | g₁ :: g₂ :: rest =>
      match isXGate g₁, isXGate g₂ with
      | some i, some j =>
        if decide (i = j) then
          -- X(i); X(i) = I -- cancel and continue
          cancelXX rest fuel'
        else
          g₁ :: cancelXX (g₂ :: rest) fuel'
      | _, _ => g₁ :: cancelXX (g₂ :: rest) fuel'

/-! ## NOT Propagation Through CNOTs -/

/-- Propagate a single X gate on qubit `q` through the subsequent gate list.
    Returns the modified gate list with the X either absorbed (cancelled with
    another X), propagated through CNOTs, or left in place.

    Key rules:
    - `X(q); CNOT(c, t)` where `q = t`: commutes through → `CNOT(c,t); X(t)`
    - `X(q); CNOT(c, t)` where `q = c`: produces `CNOT(c,t); X(c); X(t)`
    - `X(q); X(q)`: cancels to identity
    - `X(q); G` where G is on disjoint qubits: commutes through -/
def propagateX (q : Fin n) (rest : List (Gate n)) (fuel : ℕ := rest.length + 1) :
    List (Gate n) :=
  match fuel with
  | 0 => Gate.X q :: rest
  | fuel' + 1 =>
    match rest with
    | [] =>
      -- X reached end of circuit; keep it
      [Gate.X q]
    | g :: gs =>
      match isXGate g with
      | some j =>
        if decide (q = j) then
          -- X(q); X(q) = I -- cancel both
          gs
        else
          -- X on different qubit; commute past
          g :: propagateX q gs fuel'
      | none =>
        match isCNOT g with
        | some (c, t) =>
          if decide (q = t) then
            -- X(t); CNOT(c,t) = CNOT(c,t); X(t) -- commute through
            g :: propagateX q gs fuel'
          else if decide (q = c) then
            -- X(c); CNOT(c,t) = CNOT(c,t); X(c); X(t)
            -- Propagate X(c) further, and insert X(t)
            g :: propagateX q (Gate.X t :: gs) fuel'
          else
            -- Disjoint qubits; commute through
            g :: propagateX q gs fuel'
        | none =>
          -- For other gates: check if qubits are disjoint
          let qubits := match g with
            | .H i | .Y i | .Z i | .S i | .T i | .Tdg i | .Rz i _ | .RzQ i _ => [i]
            | .CZ i j => [i, j]
            | _ => []  -- shouldn't happen
          if qubits.all (fun i => decide (q ≠ i)) then
            -- Disjoint; commute through
            g :: propagateX q gs fuel'
          else
            -- Cannot commute; leave X in place
            Gate.X q :: g :: gs

/-! ## Full Propagation Pass -/

/-- One pass of NOT propagation: scan left to right, propagate each X gate.
    Uses fuel for termination. -/
def propagateNot (gs : List (Gate n)) (fuel : ℕ := gs.length + 1) :
    List (Gate n) :=
  match fuel with
  | 0 => gs
  | fuel' + 1 =>
    match gs with
    | [] => []
    | g :: rest =>
      match isXGate g with
      | some q =>
        -- Found an X gate; propagate it through the rest
        let rest' := propagateNot rest fuel'
        propagateX q rest' (rest'.length + 1)
      | none =>
        g :: propagateNot rest fuel'

/-- Flatten a circuit to a gate list. -/
def circuitToList : Circuit n → List (Gate n)
  | .empty     => []
  | .gate g c  => g :: circuitToList c
  | .seq c₁ c₂ => circuitToList c₁ ++ circuitToList c₂

/-- The NOT propagation pass: flatten, propagate X gates, cancel X; X pairs,
    and rebuild the circuit. -/
def notPropagationPass (c : Circuit n) : Circuit n :=
  let gs := circuitToList c
  let propagated := propagateNot gs
  let cancelled := cancelXX propagated
  Circuit.ofList cancelled

/-! ## Correctness -/

/-- NOT propagation does not increase gate count.
    X; X cancellations strictly reduce, and CNOT propagation may add X gates
    but subsequent cancellation removes them. -/
private theorem cancelXX_length_le :
    ∀ (gs : List (Gate n)) (fuel : Nat), (cancelXX gs fuel).length ≤ gs.length := by
  intro gs fuel
  induction fuel generalizing gs with
  | zero => simp [cancelXX]
  | succ fuel' ih =>
    match gs with
    | [] => simp [cancelXX]
    | [g] => simp [cancelXX]
    | g₁ :: g₂ :: rest =>
      simp only [cancelXX]
      repeat split
      all_goals simp only [List.length_cons]
      all_goals first
        | exact le_trans (ih _) (by omega)  -- cancel case
        | exact Nat.succ_le_succ (ih _)    -- recurse on tail

private theorem circuitToList_length (c : Circuit n) :
    (circuitToList c).length = c.gateCount := by
  induction c with
  | empty => simp [circuitToList]
  | gate g c ih => simp [circuitToList, ih, Nat.add_comm]
  | seq c₁ c₂ ih₁ ih₂ => simp [circuitToList, ih₁, ih₂]

/-- In every branch of `propagateX`, the output length is bounded by
    `rest.length + fuel + 1`. -/
private theorem propagateX_length_le (q : Fin n) (rest : List (Gate n))
    (fuel : Nat) : (propagateX q rest fuel).length ≤ rest.length + fuel + 1 := by
  induction fuel generalizing rest with
  | zero => simp [propagateX]
  | succ fuel' ih =>
    match rest with
    | [] => simp [propagateX]
    | g :: gs =>
      -- We case-split on the gate constructor to fully reduce propagateX.
      cases g with
      | X j =>
        simp only [propagateX, isXGate]
        split
        · simp only [List.length_cons]; omega  -- cancel
        · simp only [List.length_cons]; have := ih gs; omega
      | CNOT c' t =>
        simp only [propagateX, isXGate, isCNOT]
        split
        · simp only [List.length_cons]; have := ih gs; omega
        · split
          · simp only [List.length_cons]
            have := ih (Gate.X t :: gs)
            simp only [List.length_cons] at this; omega
          · simp only [List.length_cons]; have := ih gs; omega
      | H i =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | Y i =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | Z i =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | S i =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | T i =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | Tdg i =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | Rz i θ =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | RzQ i a =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega
      | CZ i j =>
        simp only [propagateX, isXGate, isCNOT]
        split <;> simp only [List.length_cons] <;> (try have := ih gs) <;> omega

private theorem propagateNot_length_le (gs : List (Gate n)) (fuel : Nat) :
    (propagateNot gs fuel).length ≤ 2 ^ gs.length * (gs.length + 1) := by
  induction fuel generalizing gs with
  | zero =>
    simp [propagateNot]
    calc gs.length ≤ 1 * (gs.length + 1) := by omega
      _ ≤ 2 ^ gs.length * (gs.length + 1) :=
          Nat.mul_le_mul_right _ Nat.one_le_two_pow
  | succ fuel' ih =>
    match gs with
    | [] => simp [propagateNot]
    | g :: rest =>
      unfold propagateNot
      match hx : isXGate g with
      | some q =>
        simp only [hx]
        set rest' := propagateNot rest fuel'
        have h_rest : rest'.length ≤ 2 ^ rest.length * (rest.length + 1) := ih rest
        have h_propX := propagateX_length_le q rest' (rest'.length + 1)
        simp only [List.length_cons, Nat.pow_succ]
        -- h_propX: ≤ rest'.length + rest'.length + 2
        -- h_rest:  rest'.length ≤ 2^rest.length * (rest.length + 1)
        -- Goal: ≤ 2 * 2^rest.length * (rest.length + 2)
        nlinarith [Nat.one_le_two_pow (n := rest.length)]
      | none =>
        simp only [hx]
        have h := ih rest
        simp only [List.length_cons, Nat.pow_succ]
        nlinarith [Nat.one_le_two_pow (n := rest.length)]

theorem notPropagationPass_gateCount_le (c : Circuit n) :
    (notPropagationPass c).gateCount ≤
      2 ^ c.gateCount * (c.gateCount + 1) := by
  simp only [notPropagationPass, gateCount_ofList]
  calc (cancelXX (propagateNot (circuitToList c))).length
      ≤ (propagateNot (circuitToList c)).length := cancelXX_length_le _ _
    _ ≤ 2 ^ (circuitToList c).length * ((circuitToList c).length + 1) :=
        propagateNot_length_le _ _
    _ = 2 ^ c.gateCount * (c.gateCount + 1) := by
        rw [circuitToList_length]

/-! ## Examples -/

/-- Example: `X(0); CNOT(0,1); X(0)`.
    Step 1: X(0) propagates through CNOT(0,1) → CNOT(0,1); X(0); X(1)
    Step 2: X(0); X(0) cancels → CNOT(0,1); X(1) -/
def exNotBefore : Circuit 2 :=
  .gate (.X 0) (.gate (.CNOT 0 1) (.gate (.X 0) .empty))

def exNotAfter : Circuit 2 :=
  .gate (.CNOT 0 1) (.gate (.X 1) .empty)

theorem exNotBefore_gateCount : exNotBefore.gateCount = 3 := by rfl
theorem exNotAfter_gateCount : exNotAfter.gateCount = 2 := by rfl

theorem exNot_reduced :
    exNotAfter.gateCount < exNotBefore.gateCount := by
  simp [exNotAfter, exNotBefore, Circuit.gateCount]

/-- Example: `X(1); CNOT(0,1)` — X on the target commutes through. -/
def exTargetCommute : Circuit 2 :=
  .gate (.X 1) (.gate (.CNOT 0 1) .empty)

/-- After propagation: `CNOT(0,1); X(1)`. -/
def exTargetCommuteResult : Circuit 2 :=
  .gate (.CNOT 0 1) (.gate (.X 1) .empty)

end CatCrypt.Quantum.Optimization.NotPropagation
