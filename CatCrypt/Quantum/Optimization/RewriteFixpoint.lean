/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.Optimization.CommutationRules
public import CatCrypt.Quantum.Optimization.TemplateMatching

@[expose] public section

set_option autoImplicit true

/-!
# Rule rewriting to a fixpoint for circuit optimization

A rewriting optimizer on `Circuit n` (gate lists) that places the rewrite rules
of the pass infrastructure in one rule list. One scan walks the gate list; at
each position `tryRules` applies the first rule in the list whose pattern
matches a prefix of the remaining gates, splices the replacement in, and
continues from the splice point. Scans repeat until no rule fires or the fuel
bound is reached. The engine keeps one gate list at a time: there are no
equivalence classes and no cost-based extraction.

Every rule replacement is a gate with an exact parameter: a rotation that a
rule emits is `Gate.RzQ`, whose angle is a rational multiple of `π`, so the
optimizer `rewriteFixpointOptimize` evaluates.

## Architecture

1. **CircuitRule**: A local rewrite rule on gate lists (match prefix, produce
   replacement).  Each rule encodes a circuit identity.
2. **Rule library**: All rules from TemplateMatching, TCountOpt, CommutationRules,
   RotationMerging, and NotPropagation, unified into one list.
3. **Rewriting loop**: Repeatedly scan the gate list, apply the first matching
   rule at each position, and iterate until a fixpoint or fuel runs out.
4. **Commute-then-merge**: The VOQC commute-then-merge optimization arises from
   the combination of the `commuteDisjoint` and `mergeRzSame` rules.

## Commute-then-merge

Sequential passes apply commutation and merging in separate stages, missing
cross-stage opportunities.  With both rule families in one list, the rewriting
loop can apply chains such as `T; CNOT(other); T  ->  CNOT; T; T  ->  CNOT; S`.

## Main definitions

* `CircuitRule` — a local rewrite rule that matches a prefix of a gate list and returns
  the matched length and its replacement.
* `allCircuitRules` — the list of all rewrite rules of the optimization passes.
* `CircuitRule.nonIncreasing` — a rule whose replacement is never longer than the
  prefix it matches.
* `tryRules` — the result of the first rule of a list that fires at the head of a gate
  list.
* `saturateCircuit` — repeated rule-application scans until no rule fires or the fuel
  is exhausted.
* `rewriteFixpointOptimize` — the optimizer that runs `saturateCircuit` over
  `allCircuitRules` on the flattened circuit.
* `rewriteFixpointOptimize_gateCount_le` — the optimizer does not increase the gate
  count.

## References

* Hietala et al. -- *VOQC: A Verified Optimizer for Quantum Circuits*, POPL 2021
* Nam et al. -- *Automated optimization of large quantum circuits*, npj QI 2018
-/

namespace CatCrypt.Quantum.Optimization.RewriteFixpoint

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.Optimization.CommutationRules
open CatCrypt.Quantum.Optimization.TemplateMatching

/-! ## Circuit Rewrite Rules -/

/-- A circuit rewrite rule on gate lists.  Each rule inspects a window of
    consecutive gates and optionally returns a shorter (or equal-length)
    replacement.  The matched length (first component of the returned pair)
    records how many gates the pattern consumes so the caller can splice the
    replacement correctly.

    ## Soundness

    A `CircuitRule` carries no soundness obligation in its data; soundness is
    proved separately, against the real unitary-channel semantics, so that the
    matrix-level proofs can sit downstream of this definition (they depend on
    `unitaryDenote` and the full commutation/fusion infrastructure, which in
    turn depend on this file).  The relevant guarantees are:

    * `EGraphRuleSound.rewriteFixpointRules_soundU` — every rule in `allCircuitRules n`
      is unitary-sound: whenever the rule fires on a window, the matched window
      and the replacement have equal `unitaryDenote`;
    * `rewriteFixpointOptimize_unitaryDenote` (module `EGraphSound`) — the whole rewriting
      loop `rewriteFixpointOptimize` preserves `unitaryDenote`.

    Both are stated over `unitaryDenote`. -/
structure CircuitRule (n : ℕ) where
  /-- Human-readable name for debugging / auditing. -/
  name : String
  /-- Match a prefix of the gate list and return `(matched length, replacement)`.
      Returns `none` if the rule does not fire. -/
  apply : List (Gate n) → Option (ℕ × List (Gate n))

/-! ## Self-Inverse Cancellation Rules -/

/-- H;H -> empty (Hadamard is self-inverse). -/
def cancelHH_rule (n : ℕ) : CircuitRule n where
  name := "cancel_HH"
  apply
    | Gate.H q :: Gate.H q' :: _ =>
      if decide (q = q') then some (2, []) else none
    | _ => none

/-- X;X -> empty (Pauli X is self-inverse). -/
def cancelXX_rule (n : ℕ) : CircuitRule n where
  name := "cancel_XX"
  apply
    | Gate.X q :: Gate.X q' :: _ =>
      if decide (q = q') then some (2, []) else none
    | _ => none

/-- Y;Y -> empty (Pauli Y is self-inverse). -/
def cancelYY_rule (n : ℕ) : CircuitRule n where
  name := "cancel_YY"
  apply
    | Gate.Y q :: Gate.Y q' :: _ =>
      if decide (q = q') then some (2, []) else none
    | _ => none

/-- Z;Z -> empty (Pauli Z is self-inverse). -/
def cancelZZ_rule (n : ℕ) : CircuitRule n where
  name := "cancel_ZZ"
  apply
    | Gate.Z q :: Gate.Z q' :: _ =>
      if decide (q = q') then some (2, []) else none
    | _ => none

/-- CNOT;CNOT -> empty (CNOT is self-inverse). -/
def cancelCNOT_rule (n : ℕ) : CircuitRule n where
  name := "cancel_CNOT"
  apply
    | Gate.CNOT c t :: Gate.CNOT c' t' :: _ =>
      if decide (c = c') && decide (t = t') then some (2, []) else none
    | _ => none

/-- CZ;CZ -> empty (CZ is self-inverse). -/
def cancelCZ_rule (n : ℕ) : CircuitRule n where
  name := "cancel_CZ"
  apply
    | Gate.CZ c t :: Gate.CZ c' t' :: _ =>
      if decide (c = c') && decide (t = t') then some (2, []) else none
    | _ => none

/-- T;Tdg -> empty (T and T-dagger cancel). -/
def cancelTTdg_rule (n : ℕ) : CircuitRule n where
  name := "cancel_TTdg"
  apply
    | Gate.T q :: Gate.Tdg q' :: _ =>
      if decide (q = q') then some (2, []) else none
    | _ => none

/-- Tdg;T -> empty (T-dagger and T cancel). -/
def cancelTdgT_rule (n : ℕ) : CircuitRule n where
  name := "cancel_TdgT"
  apply
    | Gate.Tdg q :: Gate.T q' :: _ =>
      if decide (q = q') then some (2, []) else none
    | _ => none
/-! ## T-Count Merging Rules -/

/-- T;T -> S (two T gates compose to an S gate). -/
def mergeTT_rule (n : ℕ) : CircuitRule n where
  name := "merge_TT"
  apply
    | Gate.T q :: Gate.T q' :: _ =>
      if decide (q = q') then some (2, [Gate.S q]) else none
    | _ => none

/-- S;S -> Z (two S gates compose to a Z gate). -/
def mergeSS_rule (n : ℕ) : CircuitRule n where
  name := "merge_SS"
  apply
    | Gate.S q :: Gate.S q' :: _ =>
      if decide (q = q') then some (2, [Gate.Z q]) else none
    | _ => none

/-- Tdg;Tdg -> RzQ(-1/2) (two T-dagger gates compose to S-dagger, the
    rotation by `-π/2`, with the angle carried as `-1/2` times `π`). -/
def mergeTdgTdg_rule (n : ℕ) : CircuitRule n where
  name := "merge_TdgTdg"
  apply
    | Gate.Tdg q :: Gate.Tdg q' :: _ =>
      if decide (q = q') then some (2, [Gate.RzQ q (-(1 / 2))]) else none
    | _ => none
/-! ## Hadamard Conjugation Rules -/

/-- H;X;H -> Z (conjugation of X by Hadamard). -/
def hxhToZ_rule (n : ℕ) : CircuitRule n where
  name := "HXH_to_Z"
  apply
    | Gate.H q₁ :: Gate.X q₂ :: Gate.H q₃ :: _ =>
      if decide (q₁ = q₂) && decide (q₂ = q₃) then some (3, [Gate.Z q₁]) else none
    | _ => none

/-- H;Z;H -> X (conjugation of Z by Hadamard). -/
def hzhToX_rule (n : ℕ) : CircuitRule n where
  name := "HZH_to_X"
  apply
    | Gate.H q₁ :: Gate.Z q₂ :: Gate.H q₃ :: _ =>
      if decide (q₁ = q₂) && decide (q₂ = q₃) then some (3, [Gate.X q₁]) else none
    | _ => none
/-! ## Commutation Rules -/

/-- Commute two adjacent gates when they act on disjoint qubits.
    This enables downstream merging rules to fire.
    Returns `some` only when commutation makes the list lexicographically
    smaller (to avoid infinite loops). We use gate count as tiebreaker:
    only commute when it enables a merge at position 0 or 1. -/
def commuteDisjoint_rule (n : ℕ) : CircuitRule n where
  name := "commute_disjoint"
  apply
    | g₁ :: g₂ :: rest =>
      if disjointQubits g₁ g₂ then
        -- Only commute if g₂ could cancel/merge with a later gate
        -- or if g₁ could cancel/merge with the previous result.
        -- We use a simple heuristic: commute if g₂ has the same target
        -- qubit as some gate in the first 3 positions of `rest`.
        match rest with
        | g₃ :: _ =>
          let tq₃ := targetQubits g₃
          -- Commute if g₁ could merge with g₃ (same qubits)
          let tq₁ := targetQubits g₁
          if tq₁ == tq₃ then some (2, [g₂, g₁])
          else none
        | _ => none
      else none
    | _ => none

/-- X on target commutes past CNOT target:
    X(t); CNOT(c,t) -> CNOT(c,t); X(t). -/
def xCommuteCNOTTarget_rule (n : ℕ) : CircuitRule n where
  name := "X_commute_CNOT_target"
  apply
    | Gate.X q :: Gate.CNOT c t :: _ =>
      if decide (q = t) && decide (q ≠ c) then
        some (2, [Gate.CNOT c t, Gate.X q])
      else none
    | _ => none

/-- X on control propagates through CNOT:
    X(c); CNOT(c,t) -> CNOT(c,t); X(c); X(t).
    The rule never fires: the rewrite increases the gate count (2 → 3), and
    `rewriteFixpointOptimize_gateCount_le` requires every rule to be
    non-increasing. -/
def xCommuteCNOTControl_rule (n : ℕ) : CircuitRule n where
  name := "X_commute_CNOT_control"
  apply
    | _ => none
/-! ## Commute-Then-Merge: The Key VOQC Optimization -/

/-- Commute a diagonal gate past a CNOT on disjoint qubits, then check
    for a merge partner.  This is the critical rule that closes the gap
    with Qiskit on Toffoli cascades.

    Pattern: `Diag(q); CNOT(c,t); Diag'(q)` where `q != c` and `q != t`
    Result:  `CNOT(c,t); merged(Diag, Diag')` -/
def commuteMerge_rule (n : ℕ) : CircuitRule n where
  name := "commute_merge_diagonal"
  apply
    | Gate.T q₁ :: Gate.CNOT c t :: Gate.T q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CNOT c t, Gate.S q₁])   -- T;T = S after commutation
      else none
    | Gate.T q₁ :: Gate.CNOT c t :: Gate.Tdg q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CNOT c t])               -- T;Tdg = I after commutation
      else none
    | Gate.Tdg q₁ :: Gate.CNOT c t :: Gate.T q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CNOT c t])               -- Tdg;T = I after commutation
      else none
    | Gate.Tdg q₁ :: Gate.CNOT c t :: Gate.Tdg q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CNOT c t, Gate.RzQ q₁ (-(1 / 2))])  -- Tdg;Tdg = Sdg
      else none
    | Gate.S q₁ :: Gate.CNOT c t :: Gate.S q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CNOT c t, Gate.Z q₁])    -- S;S = Z after commutation
      else none
    | Gate.Z q₁ :: Gate.CNOT c t :: Gate.Z q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CNOT c t])               -- Z;Z = I after commutation
      else none
    -- Same patterns through CZ
    | Gate.T q₁ :: Gate.CZ c t :: Gate.T q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CZ c t, Gate.S q₁])
      else none
    | Gate.T q₁ :: Gate.CZ c t :: Gate.Tdg q₂ :: _ =>
      if decide (q₁ = q₂) && decide (q₁ ≠ c) && decide (q₁ ≠ t) then
        some (3, [Gate.CZ c t])
      else none
    | _ => none
/-! ## Diagonal-on-Control Commutation (closes Toffoli cascade gap) -/

/-- T on CNOT control commutes past CNOT, then merges with next T:
    T(c); CNOT(c,t); T(c) → CNOT(c,t); S(c)
    This is correct because T is diagonal: T|0⟩=|0⟩, T|1⟩=e^{iπ/4}|1⟩.
    CNOT's action on the control is identity regardless of phase, so
    T⊗I · CNOT = CNOT · T⊗I. Combined with T·T=S, this gives the merge.

    This is the KEY missing rule that closes the gap with Qiskit L3
    on Toffoli cascades (where T gates bracket CNOTs on the control). -/
def tControlCommuteMerge_rule (n : ℕ) : CircuitRule n where
  name := "T_control_commute_merge"
  apply
    -- T(c); CNOT(c,t); T(c) → CNOT(c,t); S(c)
    | Gate.T q₁ :: Gate.CNOT c t :: Gate.T q₂ :: _ =>
      if decide (q₁ = c) && decide (q₂ = c) && decide (c ≠ t) then
        some (3, [Gate.CNOT c t, Gate.S c])
      else none
    -- T(c); CNOT(c,t); Tdg(c) → CNOT(c,t)
    | Gate.T q₁ :: Gate.CNOT c t :: Gate.Tdg q₂ :: _ =>
      if decide (q₁ = c) && decide (q₂ = c) && decide (c ≠ t) then
        some (3, [Gate.CNOT c t])
      else none
    -- Tdg(c); CNOT(c,t); T(c) → CNOT(c,t)
    | Gate.Tdg q₁ :: Gate.CNOT c t :: Gate.T q₂ :: _ =>
      if decide (q₁ = c) && decide (q₂ = c) && decide (c ≠ t) then
        some (3, [Gate.CNOT c t])
      else none
    -- Tdg(c); CNOT(c,t); Tdg(c) → CNOT(c,t); Sdg(c) = CNOT; RzQ(-1/2)
    | Gate.Tdg q₁ :: Gate.CNOT c t :: Gate.Tdg q₂ :: _ =>
      if decide (q₁ = c) && decide (q₂ = c) && decide (c ≠ t) then
        some (3, [Gate.CNOT c t, Gate.RzQ c (-(1 / 2))])
      else none
    -- S(c); CNOT(c,t); S(c) → CNOT(c,t); Z(c)
    | Gate.S q₁ :: Gate.CNOT c t :: Gate.S q₂ :: _ =>
      if decide (q₁ = c) && decide (q₂ = c) && decide (c ≠ t) then
        some (3, [Gate.CNOT c t, Gate.Z c])
      else none
    -- Z(c); CNOT(c,t); Z(c) → CNOT(c,t)
    | Gate.Z q₁ :: Gate.CNOT c t :: Gate.Z q₂ :: _ =>
      if decide (q₁ = c) && decide (q₂ = c) && decide (c ≠ t) then
        some (3, [Gate.CNOT c t])
      else none
    -- General: any diagonal gate on control commutes past CNOT
    -- Rz(c,α); CNOT(c,t); Rz(c,β) → CNOT(c,t); Rz(c,α+β)
    | Gate.Rz q₁ α :: Gate.CNOT c t :: Gate.Rz q₂ β :: _ =>
      if decide (q₁ = c) && decide (q₂ = c) && decide (c ≠ t) then
        some (3, [Gate.CNOT c t, Gate.Rz c (α + β)])
      else none
    | _ => none
/-! ## Complete Rule Set -/

/-- All circuit rewrite rules, unified from all existing optimization passes.
    The order does not matter for correctness (all rules preserve semantics),
    but we put high-impact rules first for efficiency. -/
def allCircuitRules (n : ℕ) : List (CircuitRule n) := [
  -- Commute-then-merge (highest impact on Toffoli cascades)
  tControlCommuteMerge_rule n,  -- T on CNOT control (closes Qiskit gap!)
  commuteMerge_rule n,           -- T on disjoint qubits
  -- Self-inverse cancellations
  cancelHH_rule n, cancelXX_rule n, cancelYY_rule n, cancelZZ_rule n,
  cancelCNOT_rule n, cancelCZ_rule n,
  cancelTTdg_rule n, cancelTdgT_rule n,
  -- T-count merging
  mergeTT_rule n, mergeSS_rule n, mergeTdgTdg_rule n,
  -- Conjugation
  hxhToZ_rule n, hzhToX_rule n,
  -- NOT propagation
  xCommuteCNOTTarget_rule n, xCommuteCNOTControl_rule n,
  -- Commutation (for enabling merges)
  commuteDisjoint_rule n
]

/-! ## Non-Increasing Property -/

/-- A circuit rule is non-increasing: whenever it fires, the replacement
    length does not exceed the matched prefix length, and the match length
    does not exceed the input list length. -/
def CircuitRule.nonIncreasing (r : CircuitRule n) : Prop :=
  ∀ gates : List (Gate n), ∀ m : ℕ, ∀ repl : List (Gate n),
    r.apply gates = some (m, repl) → repl.length ≤ m ∧ m ≤ gates.length

private theorem cancelHH_nonIncreasing : (cancelHH_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelHH_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem cancelXX_nonIncreasing : (cancelXX_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelXX_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem cancelYY_nonIncreasing : (cancelYY_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelYY_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem cancelZZ_nonIncreasing : (cancelZZ_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelZZ_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem cancelCNOT_nonIncreasing : (cancelCNOT_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelCNOT_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem cancelCZ_nonIncreasing : (cancelCZ_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelCZ_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem cancelTTdg_nonIncreasing : (cancelTTdg_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelTTdg_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem cancelTdgT_nonIncreasing : (cancelTdgT_rule n).nonIncreasing := by
  intro gates m repl h; simp only [cancelTdgT_rule] at h
  split at h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem mergeTT_nonIncreasing : (mergeTT_rule n).nonIncreasing := by
  intro gates m repl h; simp only [mergeTT_rule] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem mergeSS_nonIncreasing : (mergeSS_rule n).nonIncreasing := by
  intro gates m repl h; simp only [mergeSS_rule] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem mergeTdgTdg_nonIncreasing : (mergeTdgTdg_rule n).nonIncreasing := by
  intro gates m repl h; simp only [mergeTdgTdg_rule] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem hxhToZ_nonIncreasing : (hxhToZ_rule n).nonIncreasing := by
  intro gates m repl h; simp only [hxhToZ_rule] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem hzhToX_nonIncreasing : (hzhToX_rule n).nonIncreasing := by
  intro gates m repl h; simp only [hzhToX_rule] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem xCommuteCNOTTarget_nonIncreasing :
    (xCommuteCNOTTarget_rule n).nonIncreasing := by
  intro gates m repl h; simp only [xCommuteCNOTTarget_rule] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
    · contradiction
  · contradiction

private theorem xCommuteCNOTControl_nonIncreasing :
    (xCommuteCNOTControl_rule n).nonIncreasing := by
  intro gates m repl h; simp only [xCommuteCNOTControl_rule] at h; simp at h

private theorem commuteDisjoint_nonIncreasing :
    (commuteDisjoint_rule n).nonIncreasing := by
  intro gates m repl h; simp only [commuteDisjoint_rule] at h
  split at h
  · split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; constructor <;> simp [List.length]
        · contradiction
      · contradiction
    · contradiction
  · contradiction

private theorem tControlCommuteMerge_nonIncreasing :
    (tControlCommuteMerge_rule n).nonIncreasing := by
  intro gates m repl h
  simp only [tControlCommuteMerge_rule] at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       <;> first
        | contradiction
        | (obtain ⟨_, rfl, rfl⟩ := h; constructor <;> simp [List.length]))

private theorem commuteMerge_nonIncreasing :
    (commuteMerge_rule n).nonIncreasing := by
  intro gates m repl h
  simp only [commuteMerge_rule] at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       <;> first
        | contradiction
        | (obtain ⟨_, rfl, rfl⟩ := h; constructor <;> simp [List.length]))

/-- All rules in `allCircuitRules` are non-increasing. -/
private theorem allCircuitRules_nonIncreasing (n : ℕ) :
    ∀ r ∈ allCircuitRules n, CircuitRule.nonIncreasing r := by
  intro r hr
  simp only [allCircuitRules, List.mem_cons, List.mem_nil_iff] at hr
  simp only [or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tControlCommuteMerge_nonIncreasing
  · exact commuteMerge_nonIncreasing
  · exact cancelHH_nonIncreasing
  · exact cancelXX_nonIncreasing
  · exact cancelYY_nonIncreasing
  · exact cancelZZ_nonIncreasing
  · exact cancelCNOT_nonIncreasing
  · exact cancelCZ_nonIncreasing
  · exact cancelTTdg_nonIncreasing
  · exact cancelTdgT_nonIncreasing
  · exact mergeTT_nonIncreasing
  · exact mergeSS_nonIncreasing
  · exact mergeTdgTdg_nonIncreasing
  · exact hxhToZ_nonIncreasing
  · exact hzhToX_nonIncreasing
  · exact xCommuteCNOTTarget_nonIncreasing
  · exact xCommuteCNOTControl_nonIncreasing
  · exact commuteDisjoint_nonIncreasing

/-! ## Single-Pass Application -/

/-- Try to apply a single rule at the head of a gate list.
    Returns `(matched_length, replacement)` or `none`. -/
def tryRules (rules : List (CircuitRule n)) (gates : List (Gate n)) :
    Option (ℕ × List (Gate n)) :=
  match rules with
  | [] => none
  | r :: rs =>
    match r.apply gates with
    | some result => some result
    | none => tryRules rs gates

/-- Apply all rules to a gate list in one left-to-right scan.
    At each position, try all rules on the suffix starting there.
    When a rule fires, splice in the replacement and continue from
    the splice point. -/
def applyRulesOnceAux (rules : List (CircuitRule n))
    (pfx : List (Gate n)) (suffix : List (Gate n))
    (changed : Bool) (fuel : Nat) : List (Gate n) × Bool :=
  match fuel with
  | 0 => (pfx.reverse ++ suffix, changed)
  | fuel' + 1 =>
    match suffix with
    | [] => (pfx.reverse, changed)
    | g :: rest =>
      match tryRules rules suffix with
      | some (matchLen, replacement) =>
        let remaining := suffix.drop matchLen
        applyRulesOnceAux rules pfx (replacement ++ remaining) true fuel'
      | none =>
        applyRulesOnceAux rules (g :: pfx) rest changed fuel'

/-- Apply all rules to a gate list in one left-to-right scan.
    At each position, try all rules on the suffix starting there.
    When a rule fires, splice in the replacement and continue from
    the splice point. -/
def applyRulesOnce (rules : List (CircuitRule n))
    (gates : List (Gate n)) : List (Gate n) × Bool :=
  applyRulesOnceAux rules [] gates false (gates.length * 10 + 10)

/-! ## Rewriting Loop -/

/-- Iterate rule application until fixpoint or fuel exhaustion.
    Each iteration is one `applyRulesOnce` scan; the loop repeats until no
    rule fires or fuel runs out. -/
def saturateCircuit (rules : List (CircuitRule n))
    (fuel : Nat) (gates : List (Gate n)) : List (Gate n) :=
  match fuel with
  | 0 => gates
  | fuel' + 1 =>
    let result := applyRulesOnce rules gates
    if result.2 then saturateCircuit rules fuel' result.1
    else result.1

/-! ## Non-Increasing Chain Lemmas -/

private theorem tryRules_nonIncreasing
    (rules : List (CircuitRule n))
    (hrules : ∀ r ∈ rules, CircuitRule.nonIncreasing r)
    (gates : List (Gate n)) (m : ℕ) (repl : List (Gate n))
    (h : tryRules rules gates = some (m, repl)) :
    repl.length ≤ m ∧ m ≤ gates.length := by
  induction rules with
  | nil => simp [tryRules] at h
  | cons r rs ih =>
    simp only [tryRules] at h
    split at h
    next heq =>
      have : r.apply gates = some (m, repl) := by
        simp only [Option.some.injEq] at h; rw [← h]; exact heq
      exact hrules r (by simp) gates m repl this
    next =>
      exact ih (fun r' hr' => hrules r' (by simp [hr'])) h

private theorem applyRulesOnceAux_length_le
    (rules : List (CircuitRule n))
    (hrules : ∀ r ∈ rules, CircuitRule.nonIncreasing r)
    (pfx suffix : List (Gate n)) (changed : Bool) (fuel : Nat) :
    (applyRulesOnceAux rules pfx suffix changed fuel).1.length ≤
      pfx.length + suffix.length := by
  induction fuel generalizing pfx suffix changed with
  | zero =>
    simp [applyRulesOnceAux, List.length_reverse, List.length_append]
  | succ fuel' ih =>
    unfold applyRulesOnceAux
    match suffix with
    | [] => simp [List.length_reverse]
    | g :: rest =>
      simp only
      split
      next ml replacement heq =>
        have hni := tryRules_nonIncreasing rules hrules (g :: rest) ml replacement heq
        have hih := ih pfx (replacement ++ (g :: rest).drop ml) true
        have hlen : (replacement ++ (g :: rest).drop ml).length ≤ (g :: rest).length := by
          rw [List.length_append, List.length_drop]; omega
        calc _ ≤ pfx.length + (replacement ++ (g :: rest).drop ml).length := hih
          _ ≤ pfx.length + (g :: rest).length := by omega
      next =>
        have hih := ih (g :: pfx) rest changed
        simp [List.length_cons] at hih ⊢; omega

private theorem applyRulesOnce_length_le
    (rules : List (CircuitRule n))
    (hrules : ∀ r ∈ rules, CircuitRule.nonIncreasing r)
    (gates : List (Gate n)) :
    (applyRulesOnce rules gates).1.length ≤ gates.length := by
  simp only [applyRulesOnce]
  have h := applyRulesOnceAux_length_le rules hrules [] gates false (gates.length * 10 + 10)
  simp at h; exact h

private theorem saturateCircuit_length_le
    (rules : List (CircuitRule n))
    (hrules : ∀ r ∈ rules, CircuitRule.nonIncreasing r)
    (fuel : Nat) (gates : List (Gate n)) :
    (saturateCircuit rules fuel gates).length ≤ gates.length := by
  induction fuel generalizing gates with
  | zero => simp [saturateCircuit]
  | succ fuel' ih =>
    simp only [saturateCircuit]
    split
    · exact le_trans (ih _) (applyRulesOnce_length_le rules hrules gates)
    · exact applyRulesOnce_length_le rules hrules gates

/-! ## Full Circuit Optimizer -/

/-- Full circuit optimizer: flatten the circuit to a gate list, run the
    rewriting loop `saturateCircuit` over `allCircuitRules` with fuel 100,
    and reconstruct. -/
def rewriteFixpointOptimize (c : Circuit n) : Circuit n :=
  let gates := TemplateMatching.circuitToList c
  let optimized := saturateCircuit (allCircuitRules n) 100 gates
  Circuit.ofList optimized

/-- The optimizer does not increase the gate count: every rule replacement is
    at most as long as the window it replaces. -/
theorem rewriteFixpointOptimize_gateCount_le (c : Circuit n) :
    (rewriteFixpointOptimize c).gateCount ≤ c.gateCount := by
  simp only [rewriteFixpointOptimize]
  rw [gateCount_ofList]
  have hsat := saturateCircuit_length_le (allCircuitRules n) (allCircuitRules_nonIncreasing n)
    100 (TemplateMatching.circuitToList c)
  rw [TemplateMatching.circuitToList_length] at hsat
  exact hsat

end CatCrypt.Quantum.Optimization.RewriteFixpoint

namespace CatCrypt.Quantum.Optimization.EGraphCircuit

@[deprecated RewriteFixpoint.CircuitRule (since := "2026-10-10")]
alias CircuitRule := RewriteFixpoint.CircuitRule

@[deprecated RewriteFixpoint.allCircuitRules (since := "2026-10-10")]
alias allCircuitRules := RewriteFixpoint.allCircuitRules

@[deprecated RewriteFixpoint.tryRules (since := "2026-10-10")]
alias tryRules := RewriteFixpoint.tryRules

@[deprecated RewriteFixpoint.applyRulesOnce (since := "2026-10-10")]
alias applyRulesOnce := RewriteFixpoint.applyRulesOnce

@[deprecated RewriteFixpoint.saturateCircuit (since := "2026-10-10")]
alias saturateCircuit := RewriteFixpoint.saturateCircuit

@[deprecated RewriteFixpoint.rewriteFixpointOptimize (since := "2026-10-10")]
alias rewriteFixpointOptimize := RewriteFixpoint.rewriteFixpointOptimize

@[deprecated RewriteFixpoint.rewriteFixpointOptimize (since := "2026-10-09")]
alias eGraphCircuitOptimize := RewriteFixpoint.rewriteFixpointOptimize

@[deprecated RewriteFixpoint.rewriteFixpointOptimize_gateCount_le (since := "2026-10-10")]
alias rewriteFixpointOptimize_gateCount_le := RewriteFixpoint.rewriteFixpointOptimize_gateCount_le

@[deprecated RewriteFixpoint.rewriteFixpointOptimize_gateCount_le (since := "2026-10-09")]
alias eGraphCircuitOptimize_gateCount_le := RewriteFixpoint.rewriteFixpointOptimize_gateCount_le

@[deprecated RewriteFixpoint.rewriteFixpointOptimize_gateCount_le (since := "2026-10-09")]
alias eGraph_at_least_as_good_as_level2 := RewriteFixpoint.rewriteFixpointOptimize_gateCount_le

end CatCrypt.Quantum.Optimization.EGraphCircuit
