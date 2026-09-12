/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Invariant

/-!
# Traceful Hoare Logic

Hoare-style specification framework for `Traceful` programs. Provides
compositional reasoning about trace invariant preservation: each primitive
operation (`mkRand`, `sendMsg`, `triggerEvent`) has a specification theorem,
and these compose via `bind_spec` and `pure_spec`.

## Main definitions

* `TracefulSpec` — Hoare triple for `Traceful` programs
* `EventPredMono` — typeclass extending `ProtocolInvariants` with monotonicity
* `traceInvariant_snoc` — generic invariant preservation for any entry
* `mkRand_preserves` / `sendMsg_preserves` / `triggerEvent_preserves` —
  primitive preservation theorems
* `labelOf_mkRand` / `hasLabel_mkRand` — label connection theorems

## Motivation

All three symbolic protocol formalizations (MLS, EDHOC, TLS) share identical
boilerplate for trace monotonicity and invariant preservation. This file
factors out the common infrastructure, enabling protocol verification files
to focus on protocol-specific logic rather than trace plumbing.

## References

* DY*-extrinsic: `DY.Core.Trace.Invariant`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-! ## Trace Extension Lemmas

These lemmas were previously duplicated (as `private`) in each protocol's
`Invariants.lean`. We make them public here for reuse. -/

/-- Entries at or beyond the trace length are `none`. -/
theorem Trace.entryAt_ge_none (tr : Trace) (i : Nat) (h : tr.length ≤ i) :
    tr.entryAt i = none := by
  induction tr with
  | nil => simp [Trace.entryAt]
  | snoc tr' _ ih =>
    simp only [Trace.entryAt]
    have hne : ¬(i == tr'.length) := by rw [beq_iff_eq]; simp [Trace.length] at h; omega
    rw [if_neg hne]
    exact ih (by simp [Trace.length] at h; omega)

/-- For `i ≠ tr.length`, `entryAt` of `snoc` gives the original entry. -/
theorem Trace.entryAt_snoc_ne (tr : Trace) (e : TraceEntry) (i : Nat)
    (h : i ≠ tr.length) :
    (Trace.snoc tr e).entryAt i = tr.entryAt i := by
  simp only [Trace.entryAt]
  have : ¬(i == tr.length) := by rw [beq_iff_eq]; exact h
  rw [if_neg this]

/-- `entryAt` of `snoc` at position `tr.length` gives the new entry. -/
@[simp]
theorem Trace.entryAt_snoc_length (tr : Trace) (e : TraceEntry) :
    (Trace.snoc tr e).entryAt tr.length = some e := by
  simp [Trace.entryAt]

/-- `labelOf` corruption is preserved under trace extension. -/
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
      have h2 : tr.randLabelAt tr.length = none := by simp [Trace.randLabelAt, h1]
      simp [labelOf, h2, Label.isCorrupt]
    · have hSame : (Trace.snoc tr e).randLabelAt time = tr.randLabelAt time := by
        simp [Trace.randLabelAt, Trace.entryAt_snoc_ne tr e time h]
      simp only [labelOf, hSame]; exact id
  | concat _ _ ih₁ ih₂ =>
    simp only [labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ih₁ h₁, ih₂ h₂⟩
  | aeadEnc _ _ _ _ ihk _ ihm _ =>
    simp only [labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ihk h₁, ihm h₂⟩
  | kdfExtract _ _ ihs ihi =>
    simp only [labelOf, Label.isCorrupt]
    exact fun ⟨h₁, h₂⟩ => ⟨ihs h₁, ihi h₂⟩
  | pkeEnc _ _ _ _ _ ihm => exact ihm
  | dh _ _ ihsk _ => exact ihsk
  | kdfExpand _ _ _ ihp _ => exact ihp
  | kemEncap _ _ _ ihss => exact ihss
  | kemSecretShared _ ihss => exact ihss

/-- `corruptSet` is monotone under `snoc`. -/
theorem corruptSet_mono_snoc (tr : Trace) (e : TraceEntry) (p : String) :
    tr.corruptSet p → (Trace.snoc tr e).corruptSet p := by
  rintro ⟨i, hi, hentry⟩
  exact ⟨i, by simp [Trace.length]; omega,
    by rw [Trace.entryAt_snoc_ne tr e i (by omega)]; exact hentry⟩

/-- `bytesPublishable` is monotone under `snoc`. -/
theorem bytesPublishable_mono_snoc (tr : Trace) (e : TraceEntry) (b : Bytes) :
    bytesPublishable tr b → bytesPublishable (Trace.snoc tr e) b := by
  intro h
  have h1 := Label.isCorrupt_mono (corruptSet_mono_snoc tr e) _ h
  exact labelOf_isCorrupt_mono_snoc tr e b _ h1

/-- `canFlow` to `labelOf` is preserved under `snoc`. -/
theorem canFlow_labelOf_mono_snoc (tr : Trace) (e : TraceEntry)
    (l : Label) (b : Bytes) :
    canFlow l (labelOf tr b) → canFlow l (labelOf (Trace.snoc tr e) b) := by
  intro hFlow C hC
  exact labelOf_isCorrupt_mono_snoc tr e b C (hFlow C hC)

/-- `isCorruptAt` is monotone under `snoc`. -/
theorem Trace.isCorruptAt_mono_snoc (tr : Trace) (e : TraceEntry)
    (prin : String) (i : Nat) :
    tr.isCorruptAt prin i → (Trace.snoc tr e).isCorruptAt prin i := by
  rintro ⟨j, hji, hentry⟩
  have hjlt := Trace.entryAt_lt_length hentry
  exact ⟨j, hji, by rw [Trace.entryAt_snoc_ne tr e j (by omega)]; exact hentry⟩

/-- `eventTriggeredAt` is preserved under `snoc` for old positions. -/
theorem Trace.eventTriggeredAt_mono_snoc (tr : Trace) (e : TraceEntry)
    (i : Nat) (hi : i < tr.length) (prin tag : String) (content : Bytes) :
    tr.eventTriggeredAt i prin tag content →
    (Trace.snoc tr e).eventTriggeredAt i prin tag content := by
  intro h
  show (Trace.snoc tr e).entryAt i = _
  rw [Trace.entryAt_snoc_ne tr e i (by omega)]
  exact h

/-! ## Hoare Triple -/

/-- Hoare triple for `Traceful` programs.

`TracefulSpec pre f post` means: for any trace satisfying `pre`,
running `f` produces a result `a` and trace `tr'` satisfying `post a tr'`. -/
def TracefulSpec {α : Type} (pre : Trace → Prop) (f : Traceful α)
    (post : α → Trace → Prop) : Prop :=
  ∀ tr, pre tr → post (f tr).1 (f tr).2

/-- Sequential composition of Hoare triples. -/
theorem bind_spec {α β : Type} {pre : Trace → Prop} {mid : α → Trace → Prop}
    {post : β → Trace → Prop}
    {f : Traceful α} {g : α → Traceful β}
    (hf : TracefulSpec pre f mid)
    (hg : ∀ a, TracefulSpec (mid a) (g a) post) :
    TracefulSpec pre (f >>= g) post := by
  intro tr hpre
  have hfSpec := hf tr hpre
  exact hg (f tr).1 (f tr).2 hfSpec

/-- Pure values preserve any precondition. -/
theorem pure_spec {α : Type} {pre : Trace → Prop} (a : α) :
    TracefulSpec pre (pure a) (fun a' tr => pre tr ∧ a' = a) := by
  intro tr hpre; exact ⟨hpre, rfl⟩

/-! ## Specification for non-trace-modifying operations -/

/-- Specification for `recvMsg`: receives a message from the network.
`recvMsg` does not modify the trace. -/
theorem recvMsg_spec [ProtocolInvariants] {msg : Bytes} :
    TracefulSpec
      (fun tr => traceInvariant tr)
      (recvMsg msg)
      (fun b tr' => traceInvariant tr' ∧ b = msg) :=
  fun _tr hInv => ⟨hInv, rfl⟩

/-- Specification for `getTrace`: reads the current trace.
`getTrace` does not modify the trace. -/
theorem getTrace_spec [ProtocolInvariants] :
    TracefulSpec
      (fun tr => traceInvariant tr)
      getTrace
      (fun t tr' => traceInvariant tr' ∧ t = tr') :=
  fun _tr hInv => ⟨hInv, rfl⟩

/-! ## Label Connection Theorems

These connect `mkRand` to the label system, closing the gap between
protocol code and security theorems that use `hasLabel`. -/

/-- Fresh randomness gets its declared label in the extended trace. -/
theorem labelOf_mkRand (tr : Trace) (usage : Usage) (label : Label) (len : Nat) :
    labelOf (mkRand usage label len tr).2 (mkRand usage label len tr).1 = label := by
  simp [mkRand, labelOf, Trace.randLabelAt]

/-- Fresh randomness satisfies `hasLabel` in the extended trace. -/
theorem hasLabel_mkRand (tr : Trace) (usage : Usage) (label : Label) (len : Nat) :
    hasLabel (mkRand usage label len tr).2 (mkRand usage label len tr).1 label :=
  labelOf_mkRand tr usage label len

/-! ## Trace Growth Tracking -/

/-- After `mkRand`, the trace length increases by 1. -/
theorem trace_length_mkRand (tr : Trace) (usage : Usage) (label : Label) (len : Nat) :
    (mkRand usage label len tr).2.length = tr.length + 1 := by
  simp [mkRand]

/-- After `sendMsg`, the trace length increases by 1. -/
theorem trace_length_sendMsg (tr : Trace) (msg : Bytes) :
    (sendMsg msg tr).2.length = tr.length + 1 := by
  simp [sendMsg]

/-- After `triggerEvent`, the trace length increases by 1. -/
theorem trace_length_triggerEvent (tr : Trace) (prin tag : String) (content : Bytes) :
    (triggerEvent prin tag content tr).2.length = tr.length + 1 := by
  simp [triggerEvent]

/-- `recvMsg` does not change the trace. -/
theorem trace_length_recvMsg (tr : Trace) (msg : Bytes) :
    (recvMsg msg tr).2.length = tr.length := by
  simp [recvMsg]

/-! ## EventPred Monotonicity Class

To complete the generic specification theorems, we need `eventPred` and
`statePred` to be monotone under trace extension. This is a natural
property that all three protocols satisfy. -/

/-- Protocol invariants with monotonicity under trace extension.

Every protocol satisfying `ProtocolInvariants` also satisfies this:
events and states at old positions retain their invariant after trace
extension. All three protocols (TLS, EDHOC, MLS) already prove these
as private lemmas; this class makes the property reusable. -/
class EventPredMono extends ProtocolInvariants where
  eventPred_mono_snoc : ∀ (tr : Trace) (e : TraceEntry) (i : Nat),
    i < tr.length → ∀ (prin tag : String) (content : Bytes),
    eventPred tr i prin tag content →
    eventPred (Trace.snoc tr e) i prin tag content
  statePred_mono_snoc : ∀ (tr : Trace) (e : TraceEntry)
    (prin : String) (sessId : Nat) (content : Bytes),
    statePred tr prin sessId content →
    statePred (Trace.snoc tr e) prin sessId content

/-- Generic invariant preservation for `snoc` with `EventPredMono`. -/
theorem traceInvariant_snoc [inst : EventPredMono]
    (tr : Trace) (e : TraceEntry)
    (hInv : traceInvariant tr)
    (hNew : traceEntryInvariant (.snoc tr e) tr.length e) :
    traceInvariant (.snoc tr e) := by
  intro i hi entry he
  by_cases hieq : i = tr.length
  · subst hieq
    rw [Trace.entryAt_snoc_length] at he; cases he
    exact hNew
  · have hilt : i < tr.length := by simp [Trace.length] at hi; omega
    rw [Trace.entryAt_snoc_ne tr _ i hieq] at he
    have hOld := hInv i hilt entry he
    cases entry with
    | msgSent _ => exact bytesPublishable_mono_snoc tr e _ hOld
    | randGen _ _ _ => exact hOld
    | corrupt _ => trivial
    | setState prin sessId content =>
      exact inst.statePred_mono_snoc tr e prin sessId content hOld
    | event p t c => exact inst.eventPred_mono_snoc tr e i hilt p t c hOld

/-! ## Primitive Preservation Theorems -/

/-- `mkRand` preserves `traceInvariant`. -/
theorem mkRand_preserves [inst : EventPredMono]
    {tr : Trace} {usage : Usage} {label : Label} {len : Nat}
    (hInv : traceInvariant tr)
    (hUsage : inst.usagePred usage label) :
    traceInvariant (mkRand usage label len tr).2 := by
  simp only [mkRand]
  exact traceInvariant_snoc tr _ hInv hUsage

/-- `sendMsg` preserves `traceInvariant`. -/
theorem sendMsg_preserves [inst : EventPredMono]
    {tr : Trace} {msg : Bytes}
    (hInv : traceInvariant tr)
    (hPub : bytesPublishable (.snoc tr (.msgSent msg)) msg) :
    traceInvariant (sendMsg msg tr).2 := by
  simp only [sendMsg]
  exact traceInvariant_snoc tr _ hInv hPub

/-- `triggerEvent` preserves `traceInvariant`. -/
theorem triggerEvent_preserves [inst : EventPredMono]
    {tr : Trace} {prin tag : String} {content : Bytes}
    (hInv : traceInvariant tr)
    (hEvent : inst.eventPred (.snoc tr (.event prin tag content))
      tr.length prin tag content) :
    traceInvariant (triggerEvent prin tag content tr).2 := by
  simp only [triggerEvent]
  exact traceInvariant_snoc tr _ hInv hEvent

/-- `triggerEvent` records the event at the expected position. -/
theorem triggerEvent_records (tr : Trace) (prin tag : String) (content : Bytes) :
    (triggerEvent prin tag content tr).2.eventTriggeredAt
      tr.length prin tag content := by
  show (Trace.snoc tr _).entryAt tr.length = _
  exact Trace.entryAt_snoc_length tr _

end CatCrypt.Crypto.Symbolic
