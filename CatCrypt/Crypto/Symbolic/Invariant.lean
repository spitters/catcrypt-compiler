/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Trace

/-!
# Trace Invariants

Port of DY*'s trace invariant methodology. Protocol-specific predicates constrain
which traces are valid, and the framework ensures invariant preservation.

## Main definitions

* `labelOf` — structural label assignment for bytes terms
* `Trace.corruptSet` — set of principals corrupted in a trace
* `bytesPublishable` — a bytes value's label is corrupt given the trace's corruption
* `ProtocolInvariants` — typeclass bundling protocol-specific predicates
* `traceInvariant` — a trace satisfies all entry-level invariants

## Design

Labels are assigned structurally via `labelOf`:
- Literals, public keys, hashes, signatures, MACs → `top` (always public)
- Random values → label from trace entry at generation time
- Concatenation, AEAD encryption, KDF extract → `meet` of component labels
- PKE, KDF expand, KEM shared secret → label of protected component
- DH shared secret → label of the secret key (asymmetric by construction)

A value is "publishable" when its label is corrupt given the trace's corruption set.
The main theorem (`attacker_only_knows_publishable` in `Attacker.lean`) shows that
everything the DY attacker derives is publishable.

## References

* DY*-extrinsic: `DY.Core.Trace.Invariant`, `DY.Core.Label`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-! ## Trace Queries -/

/-- Whether `entryAt` returning `some` implies the index is valid. -/
theorem Trace.entryAt_lt_length {tr : Trace} {i : Nat} {e : TraceEntry}
    (h : tr.entryAt i = some e) : i < tr.length := by
  induction tr with
  | nil => simp [Trace.entryAt] at h
  | snoc tr' _ ih =>
    simp only [Trace.entryAt] at h
    split at h
    · rename_i heq; rw [beq_iff_eq] at heq; simp [Trace.length]; omega
    · exact Nat.lt_succ_of_lt (ih h)

/-! ## Label Assignment

Structural label assignment for bytes terms. The label tracks which
principals must be corrupted for the attacker to derive the value. -/

/-- Assign a corruption label to a bytes term based on its structure.

The label convention:
- `top`: always available to the attacker (public values)
- `principalLabel p`: requires corruption of principal `p`
- `meet l₁ l₂`: requires BOTH l₁ AND l₂ to be corrupt
- `bot`: never available (unreachable in practice) -/
def labelOf (tr : Trace) : Bytes → Label
  | .literal _ => .top
  | .rand _ _ time => tr.randLabelAt time |>.getD .bot
  | .concat b₁ b₂ => .meet (labelOf tr b₁) (labelOf tr b₂)
  | .aeadEnc key _nonce msg _ad => .meet (labelOf tr key) (labelOf tr msg)
  | .pk _ => .top
  | .pkeEnc _ _ msg => labelOf tr msg
  | .vk _ => .top
  | .sign _ _ _ => .top
  | .hash _ => .top
  | .dhPub _ => .top
  | .dh sk _ => labelOf tr sk
  | .kdfExtract salt ikm => .meet (labelOf tr salt) (labelOf tr ikm)
  | .kdfExpand prk _ _ => labelOf tr prk
  | .kemPub _ => .top
  | .kemEncap _ ss => labelOf tr ss
  | .kemSecretShared ss => labelOf tr ss
  | .mac _ _ => .top

/-! ## Corruption Set -/

/-- The set of principals corrupted anywhere in the trace. -/
def Trace.corruptSet (tr : Trace) : String → Prop :=
  fun p => ∃ i, i < tr.length ∧ tr.entryAt i = some (.corrupt p)

/-- If there's a corrupt entry at position i, the principal is in corruptSet. -/
theorem Trace.corruptSet_of_entryAt {tr : Trace} {i : Nat} {prin : String}
    (hEntry : tr.entryAt i = some (.corrupt prin)) :
    tr.corruptSet prin :=
  ⟨i, Trace.entryAt_lt_length hEntry, hEntry⟩

/-- corruptSet implies isCorruptAt at the end of the trace. -/
theorem Trace.corruptSet_iff_isCorruptAt {tr : Trace} {prin : String}
    (hLen : 0 < tr.length) :
    tr.corruptSet prin ↔ tr.isCorruptAt prin (tr.length - 1) := by
  constructor
  · rintro ⟨i, hi, he⟩; exact ⟨i, by omega, he⟩
  · rintro ⟨j, hj, he⟩; exact ⟨j, by omega, he⟩

/-! ## Label Assignment Helpers -/

/-- A bytes value has exactly label `l` in trace `tr`.
This is equivalent to `labelOf tr b = l`. -/
def hasLabel (tr : Trace) (b : Bytes) (l : Label) : Prop :=
  labelOf tr b = l

/-! ## Publishability -/

/-- A bytes value is publishable if its label is corrupt under the trace's
corruption set. This means: the principals whose corruption is needed to
derive the value ARE in fact corrupted in the trace. -/
def bytesPublishable (tr : Trace) (b : Bytes) : Prop :=
  (labelOf tr b).isCorrupt tr.corruptSet

/-! ## Protocol Invariants -/

/-- Protocol invariants: protocol-specific predicates over trace entries.

Each protocol instantiates this class to specify what constitutes a
valid trace. The framework then proves that the attacker knowledge
closure respects these invariants. -/
class ProtocolInvariants where
  /-- Predicate on principal states: `statePred tr prin sessId content`
      holds when `content` is a valid state for `prin`'s session `sessId`
      at trace `tr`. -/
  statePred : Trace → String → Nat → Bytes → Prop
  /-- Predicate on protocol events: `eventPred tr i prin tag content`
      holds when the event at position `i` is a valid protocol event.
      The position `i` enables authentication properties. -/
  eventPred : Trace → Nat → String → String → Bytes → Prop
  /-- Predicate on random value usage: `usagePred usage label` holds
      when this combination of usage and label is valid. -/
  usagePred : Usage → Label → Prop
  /-- State label soundness: a principal's state content has a label
      that is corrupt whenever the principal is corrupt. This ensures
      corrupted state is publishable. -/
  statePred_label : ∀ tr prin sessId content,
    statePred tr prin sessId content →
    ∀ C : String → Prop, C prin → (labelOf tr content).isCorrupt C

/-- Whether a trace entry satisfies the protocol invariant at the given
trace and position. -/
def traceEntryInvariant [ProtocolInvariants] (tr : Trace) (i : Nat) : TraceEntry → Prop
  | .msgSent msg => bytesPublishable tr msg
  | .randGen usage label _len => ProtocolInvariants.usagePred usage label
  | .corrupt _prin => True
  | .setState prin sessId content =>
    ProtocolInvariants.statePred tr prin sessId content
  | .event prin tag content =>
    ProtocolInvariants.eventPred tr i prin tag content

/-- A trace satisfies the protocol invariant if every entry does.
Entries are checked against the FULL trace (not just the prefix),
which simplifies the main theorem's proof. -/
def traceInvariant [ProtocolInvariants] (tr : Trace) : Prop :=
  ∀ i, i < tr.length → ∀ e, tr.entryAt i = some e → traceEntryInvariant tr i e

/-- The empty trace satisfies any invariant. -/
theorem traceInvariant_nil [ProtocolInvariants] : traceInvariant (Trace.nil) :=
  fun i hi => absurd hi (by simp [Trace.length])

end CatCrypt.Crypto.Symbolic
