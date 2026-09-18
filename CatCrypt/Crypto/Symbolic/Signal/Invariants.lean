/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Signal.Model
public import CatCrypt.Crypto.Symbolic.TracefulSpec

/-!
# Signal Trace Invariants

Signal-specific instantiation of `ProtocolInvariants`. Defines the event
and state predicates for X3DH sessions.

## Main definitions

* `signalInvariants` — `ProtocolInvariants` instance for Signal X3DH
* Invariant preservation lemmas for each protocol step

## Design

The event predicate encodes:
- `X3DHResp` events require a matching `X3DHInit` event or corruption
- `X3DHInit` events are unconstrained (initiator can start any time)
- All other events are trivially valid

## Scope

The `X3DHResp` clause postulates the correspondence that
`signal_x3dh_authentication` reads back; it mentions no signature or MAC.
`traceInvariant` for these invariants is established for the single honest
trace `tr₅` (`honestX3DH_invariant`) and for no other trace.
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

/-! ## Signal Protocol Invariants -/

/-- Signal-specific state predicate. -/
def signalStatePred (tr : Trace) (prin : String) (_sessId : Nat) (content : Bytes) : Prop :=
  canFlow (principalLabel prin) (labelOf tr content)

/-- Signal-specific event predicate.

An event is valid if it corresponds to a well-formed X3DH step:
- X3DHResp events require a matching X3DHInit event or corruption
- X3DHInit events are always valid (initiator's assertion)
- All other events are trivially valid -/
def signalEventPred (tr : Trace) (i : Nat) (prin tag : String) (content : Bytes) : Prop :=
  if tag == x3dhRespTag then
    ∃ (peer : String) (rootKey : Bytes),
      content = mkX3DHContent prin peer rootKey ∧
      ((∃ j, j < i ∧ tr.eventTriggeredAt j peer x3dhInitTag
        (mkX3DHContent peer prin rootKey)) ∨
       tr.isCorruptAt peer i)
  else if tag == x3dhInitTag then
    ∃ (peer : String) (rootKey : Bytes),
      content = mkX3DHContent prin peer rootKey
  else True

/-- Signal-specific usage predicate. -/
def signalUsagePred (usage : Usage) (_label : Label) : Prop :=
  usage = .dhKey ∨ usage = .nonce

/-- Signal protocol invariants instance. -/
instance signalInvariants : ProtocolInvariants where
  statePred := signalStatePred
  eventPred := signalEventPred
  usagePred := signalUsagePred
  statePred_label := fun _ _ _ _ h C hc => h C hc

/-! ## Invariant Preservation -/

theorem signalEventPred_mono_snoc (tr : Trace) (e : TraceEntry) (i : Nat)
    (hi : i < tr.length) (prin tag : String) (content : Bytes) :
    signalEventPred tr i prin tag content →
    signalEventPred (Trace.snoc tr e) i prin tag content := by
  unfold signalEventPred
  split
  · rintro ⟨peer, rootKey, hcontent, hauth⟩
    exact ⟨peer, rootKey, hcontent, hauth.elim
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
    | event p t c => exact signalEventPred_mono_snoc tr (.msgSent msg) i hilt p t c hOld

/-- Generating randomness with valid usage preserves the trace invariant. -/
theorem traceInvariant_randGen {tr : Trace} {usage : Usage} {label : Label} {len : Nat}
    (hInv : traceInvariant tr)
    (hUsage : signalUsagePred usage label) :
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
    | event p t c => exact signalEventPred_mono_snoc tr (.randGen usage label len) i hilt p t c hOld

/-- Triggering a valid event preserves the trace invariant. -/
theorem traceInvariant_event {tr : Trace} {prin tag : String} {content : Bytes}
    (hInv : traceInvariant tr)
    (hEvent : signalEventPred (.snoc tr (.event prin tag content))
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
      exact signalEventPred_mono_snoc tr (.event prin tag content) i hilt p t c hOld

/-- The empty trace satisfies the Signal invariant. -/
theorem traceInvariant_nil : @traceInvariant signalInvariants .nil :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

end CatCrypt.Crypto.Symbolic.Signal
