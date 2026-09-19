/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.Defs
public import CatCrypt.Crypto.Symbolic.EDHOC.Model

/-!
# EDHOC Trace Invariants

EDHOC-specific instantiation of `ProtocolInvariants`. Defines the state and
event predicates that constrain valid EDHOC traces.

## Main definitions

* `edhocInvariants` — `ProtocolInvariants` instance for EDHOC
* Invariant preservation lemmas for each protocol step

## Design

The EDHOC event predicate captures two correspondence properties:
1. **InitiatorMsg3** → either a matching **ResponderMsg2** exists, or the
   responder is corrupted (responder authentication)
2. **ResponderVerified** → either a matching **InitiatorMsg3** exists, or the
   initiator is corrupted (initiator authentication)

This follows the same pattern as `TLS/Invariants.lean` where
`ClientFinished` requires a matching `ServerFinished`.

## Scope

Both correspondences are part of `edhocEventPred`;
`edhoc_responder_authentication` and `edhoc_initiator_authentication` read
them back. `traceInvariant` for these invariants is established for the single
honest method-0 trace `tr₁₁` (`honestSession_m0_invariant`) and for no other
trace.

## References

* DY*-extrinsic: `DY.Lib.State.Typed`, protocol-specific invariant files
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-! ## Trace Extension Helpers -/

/-- Entries at or beyond the trace length are none. -/
theorem Trace.entryAt_ge_none (tr : Trace) (i : Nat) (h : tr.length ≤ i) :
    tr.entryAt i = none := by
  induction tr with
  | nil => simp [Trace.entryAt]
  | snoc tr' _ ih =>
    simp only [Trace.entryAt]
    have hne : ¬(i == tr'.length) := by rw [beq_iff_eq]; simp [Trace.length] at h; omega
    rw [if_neg hne]
    exact ih (by simp [Trace.length] at h; omega)

/-- For i ≠ tr.length, entryAt of snoc gives the original entry. -/
theorem Trace.entryAt_snoc_ne (tr : Trace) (e : TraceEntry) (i : Nat)
    (h : i ≠ tr.length) :
    (Trace.snoc tr e).entryAt i = tr.entryAt i := by
  simp only [Trace.entryAt]
  have : ¬(i == tr.length) := by rw [beq_iff_eq]; exact h
  rw [if_neg this]

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

/-! ## EDHOC Protocol Invariants -/

/-- EDHOC-specific state predicate.

A state is valid if corrupting the principal is sufficient to learn it. -/
def edhocStatePred (tr : Trace) (prin : String) (_sessId : Nat) (content : Bytes) : Prop :=
  canFlow (principalLabel prin) (labelOf tr content)

/-- EDHOC-specific event predicate.

- An **InitiatorMsg3** event is valid when a matching earlier ResponderMsg2
  event exists or the responder is corrupt.
- A **ResponderVerified** event is valid when a matching earlier InitiatorMsg3
  event exists or the initiator is corrupt.
- A **ResponderMsg2** event is valid when its content is well formed.
- Other events are valid.

The first two clauses postulate the correspondences. They mention no signature
or MAC, and no role program is shown to establish them before recording the
event. -/
def edhocEventPred (tr : Trace) (i : Nat) (prin tag : String) (content : Bytes) : Prop :=
  if tag == initiatorMsg3Tag then
    ∃ (peer : String) (prk_out : Bytes),
      content = mkMsg3Content prin peer prk_out ∧
      ((∃ j, j < i ∧ ∃ g_y, tr.eventTriggeredAt j peer responderMsg2Tag
        (mkMsg2Content peer prin g_y prk_out)) ∨
       tr.isCorruptAt peer i)
  else if tag == responderVerifiedTag then
    ∃ (peer : String) (prk_out : Bytes),
      content = mkMsg3Content peer prin prk_out ∧
      ((∃ j, j < i ∧ tr.eventTriggeredAt j peer initiatorMsg3Tag
        (mkMsg3Content peer prin prk_out)) ∨
       tr.isCorruptAt peer i)
  else if tag == responderMsg2Tag then
    ∃ (peer : String) (g_y prk_out : Bytes),
      content = mkMsg2Content prin peer g_y prk_out
  else True

/-- EDHOC-specific usage predicate.

EDHOC uses DH keys, nonces, signature keys, and MAC keys. -/
def edhocUsagePred (usage : Usage) (_label : Label) : Prop :=
  usage = .dhKey ∨ usage = .nonce ∨ usage = .sigKey ∨ usage = .macKey

/-- EDHOC protocol invariants instance -/
instance edhocInvariants : ProtocolInvariants where
  statePred := edhocStatePred
  eventPred := edhocEventPred
  usagePred := edhocUsagePred
  statePred_label := fun _ _ _ _ h C hc => h C hc

/-- eventPred is preserved under trace extension for old positions. -/
theorem edhocEventPred_mono_snoc (tr : Trace) (e : TraceEntry) (i : Nat)
    (hi : i < tr.length) (prin tag : String) (content : Bytes) :
    edhocEventPred tr i prin tag content →
    edhocEventPred (Trace.snoc tr e) i prin tag content := by
  unfold edhocEventPred
  split
  · -- initiatorMsg3Tag
    rintro ⟨peer, prk_out, hcontent, hauth⟩
    exact ⟨peer, prk_out, hcontent, hauth.elim
      (fun ⟨j, hji, g_y, hevent⟩ => .inl ⟨j, hji, g_y, by
        show (Trace.snoc tr e).entryAt j = _
        rw [Trace.entryAt_snoc_ne tr e j (by omega)]
        exact hevent⟩)
      (fun ⟨k, hki, hentry⟩ => .inr ⟨k, hki, by
        rw [Trace.entryAt_snoc_ne tr e k (by omega)]
        exact hentry⟩)⟩
  · split
    · -- responderVerifiedTag
      rintro ⟨peer, prk_out, hcontent, hauth⟩
      exact ⟨peer, prk_out, hcontent, hauth.elim
        (fun ⟨j, hji, hevent⟩ => .inl ⟨j, hji, by
          show (Trace.snoc tr e).entryAt j = _
          rw [Trace.entryAt_snoc_ne tr e j (by omega)]
          exact hevent⟩)
        (fun ⟨k, hki, hentry⟩ => .inr ⟨k, hki, by
          rw [Trace.entryAt_snoc_ne tr e k (by omega)]
          exact hentry⟩)⟩
    · split
      · exact id
      · exact id

/-! ## Invariant Preservation -/

/-- Sending a publishable message preserves the trace invariant. -/
theorem traceInvariant_sendMsg {tr : Trace} {msg : Bytes}
    (hInv : traceInvariant tr)
    (hPub : bytesPublishable (.snoc tr (.msgSent msg)) msg) :
    traceInvariant (.snoc tr (.msgSent msg)) := by
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
    | event p t c => exact edhocEventPred_mono_snoc tr (.msgSent msg) i hilt p t c hOld

/-- Generating randomness with valid usage preserves the trace invariant. -/
theorem traceInvariant_randGen {tr : Trace} {usage : Usage} {label : Label} {len : Nat}
    (hInv : traceInvariant tr)
    (hUsage : edhocUsagePred usage label) :
    traceInvariant (.snoc tr (.randGen usage label len)) := by
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
      exact edhocEventPred_mono_snoc tr (.randGen usage label len) i hilt p t c hOld

/-- Triggering a valid event preserves the trace invariant. -/
theorem traceInvariant_event {tr : Trace} {prin tag : String} {content : Bytes}
    (hInv : traceInvariant tr)
    (hEvent : edhocEventPred (.snoc tr (.event prin tag content))
      tr.length prin tag content) :
    traceInvariant (.snoc tr (.event prin tag content)) := by
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
      exact edhocEventPred_mono_snoc tr (.event prin tag content) i hilt p t c hOld

/-- The empty trace satisfies the invariant. -/
theorem traceInvariant_nil : @traceInvariant edhocInvariants .nil :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

end CatCrypt.Crypto.Symbolic.EDHOC
