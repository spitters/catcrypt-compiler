/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit

/-!
# Template Matching for Circuit Optimization

Template matching is a pattern-based optimization technique: a library of
circuit identities (templates) specifies pairs `(pattern, replacement)` where
the pattern and replacement have the same semantics. The optimizer scans the
circuit for occurrences of each pattern and substitutes the (cheaper)
replacement.

This approach is used in production quantum compilers such as IBM Qiskit,
Google Cirq, and the t|ket> compiler.

## Main definitions

* `Template n`          -- a circuit identity (pattern, replacement)
* Library of templates: `cancelHH`, `cancelXX`, `cancelCNOT`, `mergeRz`,
  `hxh_to_z`, `hzh_to_x`
* `applyTemplate`       -- find and replace the first match of a template
* `applyTemplates`      -- apply a list of templates exhaustively

Semantic correctness of a template and of the transformations built from it
is stated over `GateUnitarity.unitaryDenote` in
`Optimization/UnitarySound.lean` (`CorrectU`, `applyTemplates_correctU`).

## References

* Iten et al. -- Introduction to UniversalQCompiler, 2019
* Maslov -- Basic circuit compilation techniques for an ion-trap quantum
  machine, New J. Phys. 2017
* Rahman, Rice -- Templates for positive and negative control Toffoli
  networks, LNCS 2014
-/

@[expose] public section

set_option autoImplicit true

namespace CatCrypt.Quantum.Optimization.TemplateMatching

open CatCrypt.Quantum.QCircuit

/-! ## Template Type -/

/-- A circuit template: a (pattern, replacement) pair where the pattern and
    replacement have the same denotation. The optimizer finds instances of
    the pattern in the circuit and substitutes the replacement. -/
structure Template (n : ℕ) where
  /-- The pattern to match. -/
  pattern : Circuit n
  /-- The replacement circuit (should be cheaper). -/
  replacement : Circuit n

/-! ## Template Library -/

/-- H . H = I (Hadamard is self-inverse). -/
def cancelHH (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.H q)) (Circuit.single (Gate.H q))
  replacement := Circuit.empty

/-- X . X = I (Pauli X is self-inverse). -/
def cancelXX (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.X q)) (Circuit.single (Gate.X q))
  replacement := Circuit.empty

/-- Y . Y = I (Pauli Y is self-inverse). -/
def cancelYY (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.Y q)) (Circuit.single (Gate.Y q))
  replacement := Circuit.empty

/-- Z . Z = I (Pauli Z is self-inverse). -/
def cancelZZ (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.Z q)) (Circuit.single (Gate.Z q))
  replacement := Circuit.empty

/-- CNOT . CNOT = I (CNOT is self-inverse). -/
def cancelCNOT (c t : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.CNOT c t))
                         (Circuit.single (Gate.CNOT c t))
  replacement := Circuit.empty

/-- Rz(alpha) . Rz(beta) = Rz(alpha + beta) (rotation merging). -/
def mergeRz (q : Fin n) (α β : ℝ) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.Rz q α))
                         (Circuit.single (Gate.Rz q β))
  replacement := Circuit.single (Gate.Rz q (α + β))

/-- H . X . H = Z (conjugation of X by H gives Z). -/
def hxh_to_z (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.H q))
              (Circuit.seq (Circuit.single (Gate.X q))
                           (Circuit.single (Gate.H q)))
  replacement := Circuit.single (Gate.Z q)

/-- H . Z . H = X (conjugation of Z by H gives X). -/
def hzh_to_x (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.H q))
              (Circuit.seq (Circuit.single (Gate.Z q))
                           (Circuit.single (Gate.H q)))
  replacement := Circuit.single (Gate.X q)

/-- S . S = Z (two S gates compose to Z). -/
def mergeSS (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.S q)) (Circuit.single (Gate.S q))
  replacement := Circuit.single (Gate.Z q)

/-- T . Tdg = I (T and T-dagger cancel). -/
def cancelTTdg (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.T q)) (Circuit.single (Gate.Tdg q))
  replacement := Circuit.empty

/-- Tdg . T = I (T-dagger and T cancel, reverse order). -/
def cancelTdgT (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.Tdg q)) (Circuit.single (Gate.T q))
  replacement := Circuit.empty

/-- T . T = S (two T gates compose to an S gate). -/
def mergeTT (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.T q)) (Circuit.single (Gate.T q))
  replacement := Circuit.single (Gate.S q)

/-- Tdg . Tdg = Sdg (two T-dagger gates compose to S-dagger). `Sdg` is not a
    `Gate` constructor; the replacement is the rotation `RzQ q (-1/2)`, the angle
    carried as `-1/2` times `π`. -/
def mergeTdgTdg (q : Fin n) : Template n where
  pattern := Circuit.seq (Circuit.single (Gate.Tdg q)) (Circuit.single (Gate.Tdg q))
  replacement := Circuit.single (Gate.RzQ q (-(1 / 2)))

-- Note: S . S = Z is already present as `mergeSS` above.

/-! ## Template Application -/

/-- Syntactic gate equality, decided rather than assumed.

    `Gate.Rz` carries a real, so `Gate n` has no computable `DecidableEq` and
    the matcher used `Classical.decEq`, which made every pass above it
    noncomputable. Matching does not need a decision procedure, only a sound
    test: `eq_of_beqSyn` says a `true` answer is an equality, and the test
    answers `false` on a pair of rotations rather than guessing. No template
    pattern contains an `Rz`, so nothing that used to match stops matching. -/
def Gate.beqSyn {n : ℕ} : Gate n → Gate n → Bool
  | .H a, .H b => a == b
  | .X a, .X b => a == b
  | .Y a, .Y b => a == b
  | .Z a, .Z b => a == b
  | .T a, .T b => a == b
  | .Tdg a, .Tdg b => a == b
  | .S a, .S b => a == b
  | .CNOT a b, .CNOT c d => a == c && b == d
  | .CZ a b, .CZ c d => a == c && b == d  | .RzQ a p, .RzQ b q => a == b && p == q
  | _, _ => false

/-- **A `true` answer from the test is an equality.** -/
theorem Gate.eq_of_beqSyn {n : ℕ} : ∀ {g h : Gate n}, Gate.beqSyn g h = true → g = h := by
  intro g h hb
  cases g <;> cases h <;> simp_all [Gate.beqSyn]

/-- Flatten a circuit into a list of gates. -/
def circuitToList : Circuit n → List (Gate n)
  | .empty     => []
  | .gate g c  => g :: circuitToList c
  | .seq c₁ c₂ => circuitToList c₁ ++ circuitToList c₂

/-- `circuitToList` preserves gate count as list length. -/
theorem circuitToList_length (c : Circuit n) :
    (circuitToList c).length = c.gateCount := by
  induction c with
  | empty => simp [circuitToList]
  | gate g c ih => simp [circuitToList, ih, Nat.add_comm]
  | seq c₁ c₂ ih₁ ih₂ => simp [circuitToList, ih₁, ih₂]

/-- Check if a gate list starts with the pattern gate list.
    Returns the remaining gates after the match, or `none` if no match. -/
def matchPrefix : (pattern gates : List (Gate n)) → Option (List (Gate n))
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, g :: gs =>
    if Gate.beqSyn p g then matchPrefix ps gs
    else none

/-- Apply a template to a gate list: find the first occurrence of the
    pattern and replace it with the replacement. Returns `none` if the
    pattern is not found. -/
def applyTemplateList (t : Template n) : List (Gate n) → Option (List (Gate n))
  | [] => none
  | g :: gs =>
    match matchPrefix (circuitToList t.pattern) (g :: gs) with
    | some rest => some (circuitToList t.replacement ++ rest)
    | none => (applyTemplateList t gs).map (g :: ·)

/-- Apply a template to a circuit: find and replace the first match. -/
def applyTemplate (t : Template n) (c : Circuit n) : Circuit n :=
  match applyTemplateList t (circuitToList c) with
  | some gs => Circuit.ofList gs
  | none => c

/-- Apply a list of templates to a circuit, each at most once,
    iterating until no template matches. Uses a fuel parameter
    to guarantee termination. -/
def applyTemplates (templates : List (Template n)) (c : Circuit n)
    (fuel : ℕ := 100) : Circuit n :=
  match fuel with
  | 0 => c
  | fuel' + 1 =>
    let c' := templates.foldl (fun acc t => applyTemplate t acc) c
    if c'.gateCount < c.gateCount then
      applyTemplates templates c' fuel'
    else c'

end CatCrypt.Quantum.Optimization.TemplateMatching
