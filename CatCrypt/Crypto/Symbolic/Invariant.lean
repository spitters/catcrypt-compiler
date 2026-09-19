/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Trace

/-!
# Trace Invariants

A trace invariant in the style of DY*. Protocol-specific predicates constrain
which traces are valid.

## Main definitions

* `labelOf` — structural label assignment for bytes terms
* `Trace.corruptSet` — set of principals corrupted in a trace
* `Trace.Extends`, `aeadFlows` — trace extension, and the flow condition under which
  a ciphertext is public
* `bytesPublishable` — a bytes value's label is corrupt given the trace's corruption
* `ProtocolInvariants` — typeclass bundling protocol-specific predicates
* `traceInvariant` — a trace satisfies all entry-level invariants

## Design

Labels are assigned structurally via `labelOf`:
- Literals, public keys, hashes, signatures, MACs → `top` (always public)
- Random values → label from trace entry at generation time
- Concatenation, KDF extract → `meet` of component labels
- AEAD encryption → `top` when the key label flows to the plaintext label, else `meet`
- PKE, KDF expand, KEM shared secret → label of protected component
- DH shared secret → label of the secret key (asymmetric by construction)

A value is "publishable" when its label is corrupt given the trace's corruption set.
The main theorem (`attacker_only_knows_publishable` in `Attacker.lean`) shows that
everything the DY attacker derives is publishable.

## Differences from DY*

* An `aeadEnc` ciphertext is labelled `top` when the label of its key flows to
  the label of its plaintext in the trace and in every extension of it
  (`aeadFlows`), as in DY*; otherwise it takes the `meet` of the two labels.
  `pkeEnc` and `kemEncap` take the label of the protected component, so a
  public-key ciphertext of an uncompromised secret is not publishable.
* The label of `dh sk pk` is the label of `sk` alone, so a secret shared with a
  peer whose exponent the attacker holds is labelled as secret. DY* labels it
  with the join of both keys' labels.
* `traceInvariant` is a predicate on traces. No theorem states that the traces
  reachable under attacker sends, corruption and interleaved sessions satisfy
  it; the protocol developments establish it for one attacker-free run each.
* Signatures and MACs are labelled `top` and carry no predicate, so event
  predicates state authentication correspondences without a discharge
  obligation at signing time.

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

/-! ## Trace extension -/

/-- `tr'` extends `tr`: it is `tr` followed by further entries. -/
inductive Trace.Extends (tr : Trace) : Trace → Prop where
  | refl : Trace.Extends tr tr
  | snoc {tr' : Trace} (e : TraceEntry) : Trace.Extends tr tr' → Trace.Extends tr (.snoc tr' e)

theorem Trace.Extends.trans {tr₁ tr₂ tr₃ : Trace} (h₁₂ : tr₁.Extends tr₂)
    (h₂₃ : tr₂.Extends tr₃) : tr₁.Extends tr₃ := by
  induction h₂₃ with
  | refl => exact h₁₂
  | snoc e _ ih => exact .snoc e ih

theorem Trace.Extends.snoc_self (tr : Trace) (e : TraceEntry) : tr.Extends (.snoc tr e) :=
  .snoc e .refl

/-! ## Label Assignment

Structural label assignment for bytes terms. The label tracks which
principals must be corrupted for the attacker to derive the value. -/

/-- Assign a corruption label to a bytes term based on its structure.

The label convention:
- `top`: always available to the attacker (public values)
- `principalLabel p`: requires corruption of principal `p`
- `meet l₁ l₂`: requires BOTH l₁ AND l₂ to be corrupt
- `bot`: never available (unreachable in practice) -/
noncomputable def labelOf (tr : Trace) : Bytes → Label
  | .literal _ => .top
  | .rand _ _ time => tr.randLabelAt time |>.getD .bot
  | .concat b₁ b₂ => .meet (labelOf tr b₁) (labelOf tr b₂)
  | .aeadEnc key _nonce msg _ad =>
    open Classical in
    if ∀ tr', tr.Extends tr' → canFlow (labelOf tr' key) (labelOf tr' msg) then .top
    else .meet (labelOf tr key) (labelOf tr msg)
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


/-! ## The label of a ciphertext -/

/-- The plaintext of an encryption may flow to its key in `tr` and in every
extension of `tr`: whoever holds the key may hold the plaintext. -/
def aeadFlows (tr : Trace) (key msg : Bytes) : Prop :=
  ∀ tr', tr.Extends tr' → canFlow (labelOf tr' key) (labelOf tr' msg)

theorem aeadFlows_of_extends {tr tr' : Trace} (h : tr.Extends tr') {key msg : Bytes}
    (hf : aeadFlows tr key msg) : aeadFlows tr' key msg :=
  fun tr'' h' => hf tr'' (h.trans h')

theorem labelOf_aeadEnc_of_flows {tr : Trace} {key nonce msg ad : Bytes}
    (hf : aeadFlows tr key msg) : labelOf tr (.aeadEnc key nonce msg ad) = .top := by
  have : (∀ tr', tr.Extends tr' → canFlow (labelOf tr' key) (labelOf tr' msg)) := hf
  simp only [labelOf, this, if_true]
  exact if_pos this

theorem labelOf_aeadEnc_of_not_flows {tr : Trace} {key nonce msg ad : Bytes}
    (hf : ¬ aeadFlows tr key msg) :
    labelOf tr (.aeadEnc key nonce msg ad) = .meet (labelOf tr key) (labelOf tr msg) := by
  have : ¬ (∀ tr', tr.Extends tr' → canFlow (labelOf tr' key) (labelOf tr' msg)) := hf
  simp only [labelOf]
  exact if_neg this

/-- A ciphertext of corrupt key and plaintext is corrupt. -/
theorem isCorrupt_labelOf_aeadEnc {tr : Trace} {key nonce msg ad : Bytes} {C : String → Prop}
    (hk : (labelOf tr key).isCorrupt C) (hm : (labelOf tr msg).isCorrupt C) :
    (labelOf tr (.aeadEnc key nonce msg ad)).isCorrupt C := by
  classical
  by_cases hf : aeadFlows tr key msg
  · rw [labelOf_aeadEnc_of_flows hf]; simp [Label.isCorrupt]
  · rw [labelOf_aeadEnc_of_not_flows hf]; exact ⟨hk, hm⟩

/-- The plaintext of a corrupt ciphertext under a corrupt key is corrupt. -/
theorem isCorrupt_msg_of_aeadEnc {tr : Trace} {key nonce msg ad : Bytes} {C : String → Prop}
    (hk : (labelOf tr key).isCorrupt C)
    (hct : (labelOf tr (.aeadEnc key nonce msg ad)).isCorrupt C) :
    (labelOf tr msg).isCorrupt C := by
  classical
  by_cases hf : aeadFlows tr key msg
  · exact hf tr .refl C hk
  · rw [labelOf_aeadEnc_of_not_flows hf] at hct; exact hct.2

/-- Corruption of a ciphertext label is preserved along a trace extension when
it is preserved for the key and the plaintext. -/
theorem isCorrupt_labelOf_aeadEnc_mono {tr tr' : Trace} (hext : tr.Extends tr')
    {key nonce msg ad : Bytes} {C : String → Prop}
    (ihk : (labelOf tr key).isCorrupt C → (labelOf tr' key).isCorrupt C)
    (ihm : (labelOf tr msg).isCorrupt C → (labelOf tr' msg).isCorrupt C) :
    (labelOf tr (.aeadEnc key nonce msg ad)).isCorrupt C →
      (labelOf tr' (.aeadEnc key nonce msg ad)).isCorrupt C := by
  classical
  intro h
  by_cases hf : aeadFlows tr key msg
  · rw [labelOf_aeadEnc_of_flows (aeadFlows_of_extends hext hf)]; simp [Label.isCorrupt]
  · rw [labelOf_aeadEnc_of_not_flows hf] at h
    exact isCorrupt_labelOf_aeadEnc (ihk h.1) (ihm h.2)

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
