/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.Defs
public import CatCrypt.Crypto.Symbolic.MLS.Model

/-!
# MLS Trace Invariants

MLS-specific instantiation of `ProtocolInvariants`. Defines the state and
event predicates that constrain valid MLS traces.

## Main definitions

* `mlsInvariants` — `ProtocolInvariants` instance for MLS
* Invariant preservation lemmas for each protocol step

## Design

The MLS event predicate captures the core correspondence property:
- **CommitVerified** → either a matching **Commit** exists (with the same
  tree root hash), or the committer is corrupted

The pattern is identical to EDHOC's `InitiatorMsg3 → ResponderMsg2 ∨ corrupt`.

## Scope

The `CommitVerified` clause postulates the correspondence that
`mls_commit_authentication` reads back; it mentions no signature.
`traceInvariant` for these invariants is established for the single honest
trace `tr₁₀` (`honestSession_mls_invariant`) and for no other trace.

## References

* Wallez et al., USENIX Security 2023 — TreeSync authentication theorem
* DY*-extrinsic: Protocol-specific invariant files
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Trace Extension Helpers

Boilerplate lemmas for trace monotonicity, adapted from EDHOC/Invariants.lean. -/

/-- Entries at or beyond the trace length are none. -/
theorem Trace.entryAt_ge_none (tr : Trace) (i : Nat) (h : tr.length ≤ i) :
    tr.entryAt i = none := by
  induction tr with
  | nil => simp [Trace.entryAt]
  | snoc tr' _ ih =>
    simp only [Trace.entryAt]
    have hne : ¬(i == tr'.length) := by rw [beq_iff_eq]; simp [Trace.length] at h; omega
    rw [ite_eq_right hne]
    exact ih (by simp [Trace.length] at h; omega)

/-- For i ≠ tr.length, entryAt of snoc gives the original entry. -/
theorem Trace.entryAt_snoc_ne (tr : Trace) (e : TraceEntry) (i : Nat)
    (h : i ≠ tr.length) :
    (Trace.snoc tr e).entryAt i = tr.entryAt i := by
  simp only [Trace.entryAt]
  have : ¬(i == tr.length) := by rw [beq_iff_eq]; exact h
  rw [ite_eq_right this]

/-- labelOf isCorrupt is preserved under trace extension. -/
theorem labelOf_isCorrupt_mono_snoc (tr : Trace) (e : TraceEntry) (b : Bytes)
    (C : String → Prop) :
    (labelOf tr b).isCorrupt C → (labelOf (Trace.snoc tr e) b).isCorrupt C := by
  induction b with
  | literal _ | pk _ | vk _ | sign _ _ _ | hash _ | dhPub _ | kemPub _ | mac _ _ =>
    exact id
  | rand _usage _len time =>
    by_cases h : time = tr.length
    · subst h
      have h1 : tr.entryAt tr.length = none := Trace.entryAt_ge_none tr tr.length (Nat.le.refl)
      have h2 : tr.randLabelAt tr.length = none := by
        simp [Trace.randLabelAt, h1]
      simp [labelOf, h2, Label.isCorrupt]
    · have hSame : (Trace.snoc tr e).randLabelAt time = tr.randLabelAt time := by
        simp [Trace.randLabelAt, Trace.entryAt_snoc_ne tr e time h]
      simp only [labelOf, hSame]; exact id
  | concat _ _ ih₁ ih₂ =>
    simp only [labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ih₁ h₁, ih₂ h₂⟩
  | aeadEnc _ _ _ _ ihk _ ihm _ =>
    exact isCorrupt_labelOf_aeadEnc_mono (Trace.Extends.snoc_self tr e) ihk ihm
  | kdfExtract _ _ ihs ihi =>
    simp only [labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ihs h₁, ihi h₂⟩
  | pkeEnc _ _ _ _ _ ihm => exact ihm
  | dh _ _ ihsk _ => exact ihsk
  | kdfExpand _ _ _ ihp _ => exact ihp
  | kemEncap _ _ _ ihss => exact ihss
  | kemSecretShared _ ihss => exact ihss

/-- corruptSet is monotone under snoc. -/
theorem corruptSet_mono_snoc (tr : Trace) (e : TraceEntry) (p : String) :
    tr.corruptSet p → (Trace.snoc tr e).corruptSet p := by
  rintro ⟨i, hi, hentry⟩
  exact ⟨i, by simp [Trace.length]; omega,
    by rw [Trace.entryAt_snoc_ne tr e i (by omega)]; exact hentry⟩

/-- bytesPublishable is monotone under snoc. -/
theorem bytesPublishable_mono_snoc (tr : Trace) (e : TraceEntry) (b : Bytes) :
    bytesPublishable tr b → bytesPublishable (Trace.snoc tr e) b := by
  intro h
  have h1 := Label.isCorrupt_mono (corruptSet_mono_snoc tr e) _ h
  exact labelOf_isCorrupt_mono_snoc tr e b _ h1

/-- canFlow to labelOf is preserved under snoc. -/
theorem canFlow_labelOf_mono_snoc (tr : Trace) (e : TraceEntry)
    (l : Label) (b : Bytes) :
    canFlow l (labelOf tr b) → canFlow l (labelOf (Trace.snoc tr e) b) := by
  intro hFlow C hC
  exact labelOf_isCorrupt_mono_snoc tr e b C (hFlow C hC)

/-- `String.toUTF8` is injective. -/
theorem String.toUTF8_injective : Function.Injective String.toUTF8 := by
  intro ⟨b1, h1⟩ ⟨b2, h2⟩ (h : b1 = b2)
  cases h; rfl

/-! ## MLS Protocol Invariants -/

/-- MLS-specific state predicate.

A state is valid if corrupting the principal is sufficient to learn it.
Same pattern as EDHOC. -/
def mlsStatePred (tr : Trace) (prin : String) (_sessId : Nat) (content : Bytes) : Prop :=
  canFlow (principalLabel prin) (labelOf tr content)

/-- MLS-specific event predicate.

- A **CommitVerified** event is valid when a matching earlier Commit event
  exists or the committer is corrupt. The predicate postulates this
  correspondence; it mentions no signature.
- **GroupEstablished**, **Commit**, **PathSecret** and **EpochKey** events are
  valid when their content is well formed.
- Other events are valid. -/
def mlsEventPred (tr : Trace) (i : Nat) (prin tag : String) (content : Bytes) : Prop :=
  if tag == commitVerifiedTag then
    -- CommitVerified: either a matching Commit exists, or committer is corrupted
    ∃ (committer : String) (groupId : Bytes) (epoch : Nat) (rootHash : Bytes),
      content = mkCommitVerifiedContent prin committer groupId epoch rootHash ∧
      ((∃ j, j < i ∧ tr.eventTriggeredAt j committer commitTag
        (mkCommitContent committer groupId epoch rootHash)) ∨
       tr.isCorruptAt committer i)
  else if tag == groupEstablishedTag then
    -- GroupEstablished: the member participated in establishing the group
    ∃ (groupId : Bytes) (epoch : Nat) (rootHash : Bytes),
      content = mkGroupContent prin groupId epoch rootHash
  else if tag == commitTag then
    -- Commit: the committer created a valid commit
    ∃ (groupId : Bytes) (epoch : Nat) (rootHash : Bytes),
      content = mkCommitContent prin groupId epoch rootHash
  else if tag == pathSecretTag then
    -- PathSecret: committer generated a path secret
    ∃ (pathSecret : Bytes),
      content = mkPathSecretContent prin pathSecret
  else if tag == epochKeyTag then
    -- EpochKey: member derived an epoch key
    ∃ (epochKey : Bytes),
      content = mkEpochKeyContent prin epochKey
  else True

/-- MLS-specific usage predicate.

MLS uses KEM keys (path secrets, commit secrets, HPKE), nonces
(signature and AEAD nonces), signing keys (credential), and AEAD keys
(application). -/
def mlsUsagePred (usage : Usage) (_label : Label) : Prop :=
  usage = .nonce ∨ usage = .kemKey ∨ usage = .sigKey ∨ usage = .aeadKey

/-- MLS protocol invariants instance. -/
instance mlsInvariants : ProtocolInvariants where
  statePred := mlsStatePred
  eventPred := mlsEventPred
  usagePred := mlsUsagePred
  statePred_label := fun _ _ _ _ h C hc => h C hc

/-- eventPred is preserved under trace extension for old positions. -/
theorem mlsEventPred_mono_snoc (tr : Trace) (e : TraceEntry) (i : Nat)
    (hi : i < tr.length) (prin tag : String) (content : Bytes) :
    mlsEventPred tr i prin tag content →
    mlsEventPred (Trace.snoc tr e) i prin tag content := by
  unfold mlsEventPred
  split
  · -- commitVerifiedTag
    rintro ⟨committer, groupId, epoch, rootHash, hcontent, hauth⟩
    exact ⟨committer, groupId, epoch, rootHash, hcontent, hauth.elim
      (fun ⟨j, hji, hevent⟩ => .inl ⟨j, hji, by
        show (Trace.snoc tr e).entryAt j = _
        rw [Trace.entryAt_snoc_ne tr e j (by omega)]
        exact hevent⟩)
      (fun ⟨k, hki, hentry⟩ => .inr ⟨k, hki, by
        rw [Trace.entryAt_snoc_ne tr e k (by omega)]
        exact hentry⟩)⟩
  · split
    · -- groupEstablishedTag
      exact id
    · split
      · -- commitTag
        exact id
      · split
        · -- pathSecretTag
          exact id
        · split
          · -- epochKeyTag
            exact id
          · exact id

/-! ## Invariant Preservation -/

/-- Sending a publishable message preserves the trace invariant. -/
theorem traceInvariant_sendMsg {tr : Trace} {msg : Bytes}
    (hInv : @traceInvariant mlsInvariants tr)
    (hPub : bytesPublishable (.snoc tr (.msgSent msg)) msg) :
    @traceInvariant mlsInvariants (.snoc tr (.msgSent msg)) := by
  intro i hi e he
  by_cases hieq : i = tr.length
  · subst hieq
    have : (Trace.snoc tr (.msgSent msg)).entryAt tr.length = some (.msgSent msg) := by
      simp [Trace.entryAt]
    rw [this] at he; cases he
    exact hPub
  · have hilt : i < tr.length := by simp [Trace.length] at hi; omega
    rw [Trace.entryAt_snoc_ne tr _ i hieq] at he
    have hOld := hInv i hilt e he
    cases e with
    | msgSent _ => exact bytesPublishable_mono_snoc tr (.msgSent msg) _ hOld
    | randGen _ _ _ => exact hOld
    | corrupt _ => trivial
    | setState _ _ content =>
      exact canFlow_labelOf_mono_snoc tr (.msgSent msg) _ content hOld
    | event p t c => exact mlsEventPred_mono_snoc tr (.msgSent msg) i hilt p t c hOld

/-- Generating randomness with valid usage preserves the trace invariant. -/
theorem traceInvariant_randGen {tr : Trace} {usage : Usage} {label : Label} {len : Nat}
    (hInv : @traceInvariant mlsInvariants tr)
    (hUsage : mlsUsagePred usage label) :
    @traceInvariant mlsInvariants (.snoc tr (.randGen usage label len)) := by
  intro i hi e he
  by_cases hieq : i = tr.length
  · subst hieq
    have : (Trace.snoc tr (.randGen usage label len)).entryAt tr.length =
      some (.randGen usage label len) := by simp [Trace.entryAt]
    rw [this] at he; cases he
    exact hUsage
  · have hilt : i < tr.length := by simp [Trace.length] at hi; omega
    rw [Trace.entryAt_snoc_ne tr _ i hieq] at he
    have hOld := hInv i hilt e he
    cases e with
    | msgSent _ => exact bytesPublishable_mono_snoc tr (.randGen usage label len) _ hOld
    | randGen _ _ _ => exact hOld
    | corrupt _ => trivial
    | setState _ _ content =>
      exact canFlow_labelOf_mono_snoc tr (.randGen usage label len) _ content hOld
    | event p t c =>
      exact mlsEventPred_mono_snoc tr (.randGen usage label len) i hilt p t c hOld

/-- Triggering a valid event preserves the trace invariant. -/
theorem traceInvariant_event {tr : Trace} {prin tag : String} {content : Bytes}
    (hInv : @traceInvariant mlsInvariants tr)
    (hEvent : mlsEventPred (.snoc tr (.event prin tag content))
      tr.length prin tag content) :
    @traceInvariant mlsInvariants (.snoc tr (.event prin tag content)) := by
  intro i hi e he
  by_cases hieq : i = tr.length
  · subst hieq
    have : (Trace.snoc tr (.event prin tag content)).entryAt tr.length =
      some (.event prin tag content) := by simp [Trace.entryAt]
    rw [this] at he; cases he
    exact hEvent
  · have hilt : i < tr.length := by simp [Trace.length] at hi; omega
    rw [Trace.entryAt_snoc_ne tr _ i hieq] at he
    have hOld := hInv i hilt e he
    cases e with
    | msgSent _ => exact bytesPublishable_mono_snoc tr (.event prin tag content) _ hOld
    | randGen _ _ _ => exact hOld
    | corrupt _ => trivial
    | setState _ _ c =>
      exact canFlow_labelOf_mono_snoc tr (.event prin tag content) _ c hOld
    | event p t c =>
      exact mlsEventPred_mono_snoc tr (.event prin tag content) i hilt p t c hOld

/-- The empty trace satisfies the MLS invariant. -/
theorem traceInvariant_nil : @traceInvariant mlsInvariants .nil :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

end CatCrypt.Crypto.Symbolic.MLS
