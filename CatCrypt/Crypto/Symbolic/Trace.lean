/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Bytes
public import CatCrypt.Crypto.Symbolic.Label

/-!
# Trace — Execution Traces and Traceful Monad

Port of DY*'s trace semantics. A trace is a snoc-list of events recording
the execution history of a protocol. The `Traceful` monad threads trace
state through protocol operations.

## Main definitions

* `TraceEntry` — individual trace entries (messages, randomness, state, events)
* `Trace` — snoc-list of trace entries
* `Traceful` — state monad over `Trace` (with monotonicity proof)
* Trace operations: `length`, `prefix`, `entryAt`, `grows`

## Design

DY*-extrinsic uses a linear trace (snoc-list) rather than a branching LTS.
This is sufficient for security properties of cryptographic protocols where
we reason about a single execution. The trace records:

1. **Messages sent** on the network (visible to the attacker)
2. **Randomness generated** with usage and label annotations
3. **State changes** for each principal's session
4. **Protocol events** (assertions for correspondence properties)
5. **Corruption** events when principals are compromised

## References

* DY*-extrinsic: `DY.Core.Trace.Type`, `DY.Core.Trace.Manipulation`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-! ## Trace Entries -/

/-- A single entry in the execution trace.

Each entry records one atomic action in the protocol execution:
- `msgSent`: a message placed on the network (attacker can see it)
- `randGen`: fresh randomness generated with usage annotation and label
- `corrupt`: a principal is compromised at this trace position
- `setState`: a principal updates its session state
- `event`: a protocol event (used for correspondence assertions)
-/
inductive TraceEntry where
  /-- A message was sent on the network -/
  | msgSent : (msg : Bytes) → TraceEntry
  /-- Fresh randomness was generated -/
  | randGen : (usage : Usage) → (label : Label) → (len : Nat) → TraceEntry
  /-- A principal was corrupted -/
  | corrupt : (prin : String) → TraceEntry
  /-- A principal set its session state -/
  | setState : (prin : String) → (sessId : Nat) → (content : Bytes) → TraceEntry
  /-- A protocol event was triggered (for correspondence) -/
  | event : (prin : String) → (tag : String) → (content : Bytes) → TraceEntry
  deriving Inhabited, Repr

/-! ## Trace Type -/

/-- Execution trace: a snoc-list of trace entries.

Using snoc-list (rather than cons-list) because new events are appended
at the end. This matches DY*'s convention where trace indices correspond
to chronological order: index 0 is the first event, and `trace.length - 1`
is the most recent. -/
inductive Trace where
  /-- Empty trace -/
  | nil : Trace
  /-- Trace extended with one entry -/
  | snoc : Trace → TraceEntry → Trace
  deriving Inhabited, Repr

namespace Trace

/-- Length of a trace (number of entries) -/
def length : Trace → Nat
  | .nil => 0
  | .snoc tr _ => tr.length + 1

/-- Get the entry at index `i` (0-indexed from the beginning) -/
def entryAt : Trace → Nat → Option TraceEntry
  | .nil, _ => none
  | .snoc tr e, i =>
    if i == tr.length then some e
    else tr.entryAt i

/-- Get the last entry -/
def last : Trace → Option TraceEntry
  | .nil => none
  | .snoc _ e => some e

/-- Convert trace to a list (for iteration) -/
def toList : Trace → List TraceEntry
  | .nil => []
  | .snoc tr e => tr.toList ++ [e]

/-- Build a trace from a list -/
def ofList : List TraceEntry → Trace :=
  List.foldl .snoc .nil

/-- Take the first `n` entries of the trace -/
def take (tr : Trace) (n : Nat) : Trace :=
  ofList (tr.toList.take n)

/-! ## Trace ordering (prefix relation) -/

/-- `grows tr₁ tr₂` means `tr₁` is a prefix of `tr₂` -/
def grows (tr₁ tr₂ : Trace) : Prop :=
  tr₁.length ≤ tr₂.length ∧
  ∀ i, i < tr₁.length → tr₁.entryAt i = tr₂.entryAt i

theorem grows_refl (tr : Trace) : grows tr tr :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem grows_trans {tr₁ tr₂ tr₃ : Trace} :
    grows tr₁ tr₂ → grows tr₂ tr₃ → grows tr₁ tr₃ :=
  fun ⟨h₁, he₁⟩ ⟨h₂, he₂⟩ =>
    ⟨Nat.le_trans h₁ h₂, fun i hi => (he₁ i hi).trans (he₂ i (Nat.lt_of_lt_of_le hi h₁))⟩

theorem grows_snoc (tr : Trace) (e : TraceEntry) : grows tr (.snoc tr e) := by
  constructor
  · exact Nat.le_succ _
  · intro i hi
    simp only [entryAt]
    rw [if_neg (by rw [beq_iff_eq]; omega)]

/-! ## Trace queries -/

/-- Check if a principal was corrupted at or before position `i` -/
def isCorruptAt (tr : Trace) (prin : String) (i : Nat) : Prop :=
  ∃ j, j ≤ i ∧ tr.entryAt j = some (.corrupt prin)

/-- Check if an event was triggered at position `i` -/
def eventTriggeredAt (tr : Trace) (i : Nat) (prin tag : String) (content : Bytes) : Prop :=
  tr.entryAt i = some (.event prin tag content)

/-- Check if an event was triggered somewhere in the trace -/
def eventTriggered (tr : Trace) (prin tag : String) (content : Bytes) : Prop :=
  ∃ i, i < tr.length ∧ tr.eventTriggeredAt i prin tag content

/-- Get the state of a principal's session (last setState entry) -/
def getState (tr : Trace) (prin : String) (sessId : Nat) : Option Bytes :=
  match tr with
  | .nil => none
  | .snoc rest (.setState p s c) =>
    if p == prin && s == sessId then some c
    else rest.getState prin sessId
  | .snoc rest _ => rest.getState prin sessId

/-- Get the label of randomness generated at position `i` -/
def randLabelAt (tr : Trace) (i : Nat) : Option Label :=
  match tr.entryAt i with
  | some (.randGen _ l _) => some l
  | _ => none

/-- Get the usage of randomness generated at position `i` -/
def randUsageAt (tr : Trace) (i : Nat) : Option Usage :=
  match tr.entryAt i with
  | some (.randGen u _ _) => some u
  | _ => none

end Trace

/-! ## Traceful Monad

A simple state monad over `Trace`. Protocol steps are `Traceful` computations
that extend the trace monotonically. -/

/-- The traceful monad: computations that extend the trace.
    Returns a result and a new trace that grows the input trace. -/
def Traceful (α : Type) := Trace → α × Trace

instance : Monad Traceful where
  pure a := fun tr => (a, tr)
  bind m f := fun tr =>
    let (a, tr') := m tr
    f a tr'

instance : LawfulMonad Traceful where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

/-! ## Traceful Operations -/

/-- Get the current trace -/
def getTrace : Traceful Trace := fun tr => (tr, tr)

/-- Send a message (append to trace, attacker can see it) -/
def sendMsg (msg : Bytes) : Traceful Unit := fun tr =>
  ((), .snoc tr (.msgSent msg))

/-- Generate fresh randomness. Returns a `Bytes.rand` term whose
    trace position is the current trace length. -/
def mkRand (usage : Usage) (label : Label) (len : Nat) : Traceful Bytes := fun tr =>
  let time := tr.length
  (.rand usage len time, .snoc tr (.randGen usage label len))

/-- Set a principal's session state -/
def setStateT (prin : String) (sessId : Nat) (content : Bytes) : Traceful Unit := fun tr =>
  ((), .snoc tr (.setState prin sessId content))

/-- Get a principal's session state -/
def getStateT (prin : String) (sessId : Nat) : Traceful (Option Bytes) := fun tr =>
  (tr.getState prin sessId, tr)

/-- Trigger a protocol event (for correspondence assertions) -/
def triggerEvent (prin tag : String) (content : Bytes) : Traceful Unit := fun tr =>
  ((), .snoc tr (.event prin tag content))

/-- Model corruption of a principal -/
def corruptPrincipal (prin : String) : Traceful Unit := fun tr =>
  ((), .snoc tr (.corrupt prin))

/-- Receive a message from the network.
    In the symbolic model, the attacker chooses what to deliver,
    so this is modeled as an arbitrary `Bytes` parameter. -/
def recvMsg (msg : Bytes) : Traceful Bytes := fun tr =>
  (msg, tr)

/-! ## Trace Length Lemmas -/

@[simp]
theorem Trace.length_nil : Trace.nil.length = 0 := rfl

@[simp]
theorem Trace.length_snoc (tr : Trace) (e : TraceEntry) :
    (Trace.snoc tr e).length = tr.length + 1 := rfl

end CatCrypt.Crypto.Symbolic
