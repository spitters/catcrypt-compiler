/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Symbolic.TLS.Events
public meta import CatCrypt.Crypto.Symbolic.TLS.Invariants
public import CatCrypt.Crypto.Symbolic.TLS.Invariants
public meta import CatCrypt.Crypto.Symbolic.TimedLabel
public import CatCrypt.Crypto.Symbolic.TimedLabel
public meta import CatCrypt.Crypto.Symbolic.TracefulSpec
public import CatCrypt.Crypto.Symbolic.TracefulSpec
public meta import CatCrypt.Crypto.Symbolic.SigningDiscipline
public import CatCrypt.Crypto.Symbolic.SigningDiscipline

/-!
# TLS Protocol Verification

The trace that `honestSession` produces from `.nil` is the explicit
eight-entry trace `tr₈`, and `tr₈` satisfies `traceInvariant` for
`tlsInvariants`.

## Main results

* `tlsEventPredMono` — TLS invariants are monotone under snoc
* `honestSession_invariant` — the trace of `honestSession` from `.nil`
  satisfies the invariant
* `honestResumption_invariant` — the trace of `honestResumptionSession` from
  `.nil` satisfies the invariant
* `tr₈_appKey_server_not_known` — the attacker does not know the application
  key on `tr₈`

## Scope

`tr₈` and `ptr₇` are attacker-free runs of the full and the PSK-DHE handshake:
two honest parties, two public messages, no
corruption, one session each. They are the only traces for which the TLS invariant is
established. No theorem shows that `clientHandshake` or `serverHandshake`
preserves the invariant, and none covers attacker sends, corruption or
interleaved sessions. The `ClientFinished` step of the invariant proof supplies
the `ServerFinished` witness by pointing at the entry that `honestSession`
itself recorded; no signature is checked.
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-! ## EventPredMono Instance -/

instance tlsEventPredMono : EventPredMono where
  toProtocolInvariants := tlsInvariants
  eventPred_mono_snoc := by
    intro tr e i hi prin tag content
    exact tlsEventPred_mono_snoc tr e i hi prin tag content
  statePred_mono_snoc := by
    intro tr e prin _ content
    show tlsStatePred tr prin _ content → tlsStatePred (.snoc tr e) prin _ content
    exact canFlow_labelOf_mono_snoc tr e _ content

/-! ## Honest Session: Step-by-Step Trace Construction

We define the trace produced by `honestSession` explicitly, prove it matches,
then prove invariant by chaining preservation lemmas. -/

abbrev Inv := @traceInvariant tlsInvariants

-- Name the intermediate traces for readability
noncomputable def tr₀ : Trace := .nil
noncomputable def x (client : String) := Bytes.rand .dhKey 32 0
noncomputable def tr₁ (client : String) : Trace :=
  .snoc tr₀ (.randGen .dhKey (principalLabel client) 32)

noncomputable def gx (client : String) := Bytes.dhPub (x client)

noncomputable def tr₂ (client server : String) : Trace :=
  .snoc (tr₁ client) (.event client clientHelloTag (mkClientHelloContent client server (gx client)))

noncomputable def tr₃ (client server : String) : Trace :=
  .snoc (tr₂ client server) (.msgSent (mkClientHelloContent client server (gx client)))

noncomputable def y (client server : String) := Bytes.rand .dhKey 32 (tr₃ client server).length

noncomputable def tr₄ (client server : String) : Trace :=
  .snoc (tr₃ client server) (.randGen .dhKey (principalLabel server) 32)

noncomputable def gy (client server : String) := Bytes.dhPub (y client server)

noncomputable def serverNonce (client server : String) :=
  Bytes.rand .nonce 32 (tr₄ client server).length

noncomputable def tr₅ (client server : String) : Trace :=
  .snoc (tr₄ client server) (.randGen .nonce (principalLabel server) 32)

noncomputable def appKey_server (client server : String) :=
  keySchedule (Bytes.dh (y client server) (gx client))

noncomputable def sfContent (client server : String) :=
  mkFinishedContent server client (appKey_server client server)

noncomputable def tr₆ (client server : String) : Trace :=
  .snoc (tr₅ client server) (.event server serverFinishedTag (sfContent client server))

noncomputable def serverSig (client server : String) (serverSigKey : Bytes) :=
  Bytes.sign serverSigKey (serverNonce client server)
    (Bytes.hash (Bytes.concat (mkClientHelloContent client server (gx client)) (gy client server)))

noncomputable def tr₇ (client server : String) (serverSigKey : Bytes) : Trace :=
  .snoc (tr₆ client server) (.msgSent (.concat (gy client server) (serverSig client server serverSigKey)))

noncomputable def cfContent (client server : String) :=
  mkFinishedContent client server (appKey_server client server)

noncomputable def tr₈ (client server : String) (serverSigKey : Bytes) : Trace :=
  .snoc (tr₇ client server serverSigKey) (.event client clientFinishedTag (cfContent client server))

/-- The output of `honestSession` is `tr₈`. -/
theorem honestSession_eq (client server : String) (serverSigKey : Bytes) :
    (honestSession client server serverSigKey .nil).2 = tr₈ client server serverSigKey := by
  unfold honestSession tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀
  unfold cfContent serverSig gy y sfContent appKey_server serverNonce gx x
  simp only [bind, instMonadTraceful, mkRand, triggerEvent, sendMsg,
    Trace.length_nil, Trace.length_snoc]
  rfl

/-- The trace produced by `honestSession` from the empty trace satisfies the
TLS trace invariant. The proof extends `traceInvariant_nil` one entry at a
time along `tr₈`. It covers this one trace and no other. -/
theorem honestSession_invariant (client server : String) (serverSigKey : Bytes) :
    Inv (honestSession client server serverSigKey .nil).2 := by
  rw [honestSession_eq]
  unfold tr₈
  -- Step 8: event clientFinished (depends on all previous)
  -- First prove the chain of intermediate invariants
  have hInv₀ : Inv tr₀ := traceInvariant_nil
  have hInv₁ : Inv (tr₁ client) := traceInvariant_randGen hInv₀ (Or.inl rfl)
  have hInv₂ : Inv (tr₂ client server) := by
    unfold tr₂
    apply traceInvariant_event hInv₁
    show tlsEventPred _ _ _ _ _
    unfold tlsEventPred; simp [clientHelloTag, serverFinishedTag, clientFinishedTag,
      pskClientFinishedTag, pskServerFinishedTag, newSessionTicketTag]
  have hInv₃ : Inv (tr₃ client server) := by
    unfold tr₃
    apply traceInvariant_sendMsg hInv₂
    unfold gx mkClientHelloContent
    simp [bytesPublishable, labelOf, Label.isCorrupt]
  have hInv₄ : Inv (tr₄ client server) :=
    traceInvariant_randGen hInv₃ (Or.inl rfl)
  have hInv₅ : Inv (tr₅ client server) :=
    traceInvariant_randGen hInv₄ (Or.inr (Or.inl rfl))
  have hInv₆ : Inv (tr₆ client server) := by
    unfold tr₆
    apply traceInvariant_event hInv₅
    show tlsEventPred _ _ _ _ _
    unfold tlsEventPred; simp [serverFinishedTag, clientFinishedTag,
      pskClientFinishedTag, pskServerFinishedTag, newSessionTicketTag]
    exact ⟨client, _, rfl⟩
  have hInv₇ : Inv (tr₇ client server serverSigKey) := by
    unfold tr₇
    apply traceInvariant_sendMsg hInv₆
    unfold gy serverSig
    simp [bytesPublishable, labelOf, Label.isCorrupt]
  -- The key step: clientFinished requires matching serverFinished
  apply traceInvariant_event hInv₇
  show tlsEventPred _ _ _ _ _
  unfold tlsEventPred
  simp only [clientFinishedTag, BEq.beq]
  -- Need: ∃ peer appKey, ... ∧ (∃ j < current, eventTriggeredAt j server serverFinished ... ∨ corrupt)
  refine ⟨server, _, rfl, .inl ⟨(tr₅ client server).length, ?_, ?_⟩⟩
  · -- (tr₅ c s).length < (tr₇ c s serverSigKey).length
    unfold tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀
    simp [Trace.length]
  · -- eventTriggeredAt at position (tr₅ c s).length in tr₈
    -- tr₈ = snoc(tr₇, event_cf) = snoc(snoc(snoc(tr₅, event_sf), msgSent), event_cf)
    -- We peel off event_cf and msgSent to reach event_sf at position tr₅.length
    show (Trace.snoc (tr₇ client server serverSigKey)
        (.event client clientFinishedTag (cfContent client server))).entryAt
      (tr₅ client server).length =
      some (.event server serverFinishedTag (sfContent client server))
    unfold tr₇ tr₆
    simp [Trace.entryAt, Trace.length, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]

/-- The honest session triggers a `ServerFinished` event. -/
theorem honestSession_serverFinished (client server : String) (serverSigKey : Bytes) :
    ∃ j, (honestSession client server serverSigKey .nil).2.eventTriggeredAt
      j server serverFinishedTag (sfContent client server) := by
  rw [honestSession_eq]
  exact ⟨(tr₅ client server).length, by
    unfold tr₈ tr₇ tr₆ Trace.eventTriggeredAt
    simp [Trace.entryAt, Trace.length, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]⟩

/-- The honest session triggers a `ClientFinished` event. -/
theorem honestSession_clientFinished (client server : String) (serverSigKey : Bytes) :
    ∃ j, (honestSession client server serverSigKey .nil).2.eventTriggeredAt
      j client clientFinishedTag (cfContent client server) := by
  rw [honestSession_eq]
  exact ⟨(tr₇ client server serverSigKey).length, by
    unfold tr₈ Trace.eventTriggeredAt
    rfl⟩

/-! ## Facts about the honest trace `tr₈`

`tr₈` has eight entries and none of them is a `.corrupt` entry. Its two
`msgSent` entries (positions 2 and 6) contain only DH public keys, literals,
signatures and hashes, whose timed labels are `.top`. The attacker of
`AttackerKnows (tr₈ …)` therefore sees two public messages and no corrupted
state. -/

theorem tr₈_length (c s : String) (sk : Bytes) :
    (tr₈ c s sk).length = 8 := by
  unfold tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀; simp [Trace.length]

/-- No corrupt entries in the honest TLS trace. -/
theorem tr₈_no_corrupt (c s : String) (sk : Bytes) (i : Nat) (p : String) :
    (tr₈ c s sk).entryAt i ≠ some (.corrupt p) := by
  unfold tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀
  simp only [Trace.entryAt, Trace.length, Nat.reduceAdd, beq_iff_eq]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    simp_all

/-- All `msgSent` entries in the honest TLS trace are timed-publishable. -/
theorem hNetworkTimed_honest (client server : String) (serverSigKey : Bytes) :
    ∀ msg i,
      (tr₈ client server serverSigKey).entryAt i = some (.msgSent msg) →
      bytesTimedPublishable (tr₈ client server serverSigKey) msg := by
  intro msg i hi
  by_cases h8 : 8 ≤ i
  · have := Trace.entryAt_ge_none (tr₈ client server serverSigKey) i
      (by rw [tr₈_length]; omega)
    rw [this] at hi; cases hi
  · -- i < 8 (from ¬(8 ≤ i))
    have hi8 : i < 8 := Nat.lt_of_not_le h8
    -- Enumerate using split on the trace structure
    unfold tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀ at hi
    simp only [Trace.entryAt, Trace.length, Nat.reduceAdd, beq_iff_eq] at hi
    split at hi <;> (try split at hi) <;> (try split at hi) <;>
      (try split at hi) <;> (try split at hi) <;> (try split at hi) <;>
      (try split at hi) <;> (try split at hi) <;> (try simp_all) <;>
      (try (subst_eqs; simp [bytesTimedPublishable, timedLabelOf, TimedLabel.isCorrupt,
        mkClientHelloContent, gy, gx, serverSig]))

/-- No `.corrupt` entries ⟹ `hCorruptStateTimed` is vacuously true. -/
theorem hCorruptStateTimed_honest (client server : String) (serverSigKey : Bytes) :
    ∀ prin sessId content i j,
      (tr₈ client server serverSigKey).entryAt i = some (.corrupt prin) →
      (tr₈ client server serverSigKey).entryAt j = some (.setState prin sessId content) →
      bytesTimedPublishable (tr₈ client server serverSigKey) content := by
  intro _ _ _ i _ hi
  exact absurd hi (tr₈_no_corrupt client server serverSigKey i _)

/-- On the honest trace `tr₈` the attacker does not know the server-side
application key `appKey_server = keySchedule (dh y gx)`.

The statement concerns the single trace `tr₈`, which contains two public
messages and no corruption. The label of `appKey_server` is that of the
server's ephemeral `y`, so publishability would place `server` in the
corruption set of `tr₈`, which is empty. The statement says nothing about a
trace in which the attacker sends a message or a party is corrupted. -/
theorem tr₈_appKey_server_not_known
    (client server : String) (serverSigKey : Bytes) :
    ¬ AttackerKnows (tr₈ client server serverSigKey)
      (appKey_server client server) := by
  intro hKnows
  have hInv : Inv (tr₈ client server serverSigKey) := by
    rw [← honestSession_eq]
    exact honestSession_invariant client server serverSigKey
  have hPub := attacker_only_knows_publishable hInv hKnows
  have hLabel : labelOf (tr₈ client server serverSigKey) (appKey_server client server) =
      .meet (.meet (.meet .top .top) (principalLabel server)) .top := by
    unfold appKey_server y tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀
    simp [keySchedule, Bytes.zeros, labelOf, Trace.randLabelAt, Trace.entryAt, Trace.length]
  unfold bytesPublishable at hPub
  rw [hLabel] at hPub
  simp only [Label.isCorrupt, principalLabel, and_true, true_and] at hPub
  obtain ⟨j, _, hentry⟩ := hPub
  exact tr₈_no_corrupt client server serverSigKey j server hentry

/-! ## PSK Resumption: Trace Construction and Invariant

The PSK-DHE resumption session `honestResumptionSession` produces 7 trace entries.
We prove invariant from `.nil` with an arbitrary PSK. -/

-- PSK named traces
noncomputable def ptr₀ : Trace := .nil
noncomputable def px (client : String) := Bytes.rand .dhKey 32 0
noncomputable def ptr₁ (client : String) : Trace :=
  .snoc ptr₀ (.randGen .dhKey (principalLabel client) 32)

noncomputable def pgx (client : String) := Bytes.dhPub (px client)

noncomputable def ptr₂ (client server : String) (psk : Bytes) : Trace :=
  .snoc (ptr₁ client) (.event client pskClientHelloTag
    (mkClientHelloContent client server (pgx client)))

noncomputable def ptr₃ (client server : String) (psk : Bytes) : Trace :=
  .snoc (ptr₂ client server psk) (.msgSent
    (.concat (mkClientHelloContent client server (pgx client)) (pskBinder psk (pgx client))))

noncomputable def py (client server : String) (psk : Bytes) :=
  Bytes.rand .dhKey 32 (ptr₃ client server psk).length

noncomputable def ptr₄ (client server : String) (psk : Bytes) : Trace :=
  .snoc (ptr₃ client server psk) (.randGen .dhKey (principalLabel server) 32)

noncomputable def pgy (client server : String) (psk : Bytes) :=
  Bytes.dhPub (py client server psk)

noncomputable def psk_appKey (client server : String) (psk : Bytes) :=
  pskKeySchedule psk (Bytes.dh (py client server psk) (pgx client))

noncomputable def ptr₅ (client server : String) (psk : Bytes) : Trace :=
  .snoc (ptr₄ client server psk) (.event server pskServerFinishedTag
    (mkPSKFinishedContent server client (psk_appKey client server psk)))

noncomputable def ptr₆ (client server : String) (psk : Bytes) : Trace :=
  .snoc (ptr₅ client server psk) (.msgSent (pgy client server psk))

noncomputable def ptr₇ (client server : String) (psk : Bytes) : Trace :=
  .snoc (ptr₆ client server psk) (.event client pskClientFinishedTag
    (mkPSKFinishedContent client server (psk_appKey client server psk)))

/-- The output of `honestResumptionSession` is `ptr₇`. -/
theorem honestResumptionSession_eq (client server : String) (psk : Bytes) :
    (honestResumptionSession client server psk .nil).2 =
    ptr₇ client server psk := by
  unfold honestResumptionSession ptr₇ ptr₆ ptr₅ ptr₄ ptr₃ ptr₂ ptr₁ ptr₀
  unfold psk_appKey pgy py pgx px
  simp only [bind, instMonadTraceful, mkRand, triggerEvent, sendMsg,
    Trace.length_nil, Trace.length_snoc]
  rfl

/-- The trace of the PSK-DHE resumption session from `.nil` satisfies the invariant. -/
theorem honestResumption_invariant (client server : String) (psk : Bytes) :
    Inv (honestResumptionSession client server psk .nil).2 := by
  rw [honestResumptionSession_eq]
  unfold ptr₇
  -- Chain of intermediate invariants
  have hInv₀ : Inv ptr₀ := traceInvariant_nil
  have hInv₁ : Inv (ptr₁ client) := traceInvariant_randGen hInv₀ (Or.inl rfl)
  have hInv₂ : Inv (ptr₂ client server psk) := by
    unfold ptr₂
    apply traceInvariant_event hInv₁
    show tlsEventPred _ _ _ _ _
    unfold tlsEventPred; simp [pskClientHelloTag, clientFinishedTag, serverFinishedTag,
      pskClientFinishedTag, pskServerFinishedTag, newSessionTicketTag]
  have hInv₃ : Inv (ptr₃ client server psk) := by
    unfold ptr₃
    apply traceInvariant_sendMsg hInv₂
    unfold pgx mkClientHelloContent pskBinder
    simp [bytesPublishable, labelOf, Label.isCorrupt]
  have hInv₄ : Inv (ptr₄ client server psk) :=
    traceInvariant_randGen hInv₃ (Or.inl rfl)
  have hInv₅ : Inv (ptr₅ client server psk) := by
    unfold ptr₅
    apply traceInvariant_event hInv₄
    show tlsEventPred _ _ _ _ _
    unfold tlsEventPred; simp [pskServerFinishedTag, clientFinishedTag, serverFinishedTag,
      pskClientFinishedTag]
    exact ⟨client, _, rfl⟩
  have hInv₆ : Inv (ptr₆ client server psk) := by
    unfold ptr₆
    apply traceInvariant_sendMsg hInv₅
    unfold pgy
    simp [bytesPublishable, labelOf, Label.isCorrupt]
  -- Final step: pskClientFinished requires matching pskServerFinished
  apply traceInvariant_event hInv₆
  show tlsEventPred _ _ _ _ _
  unfold tlsEventPred
  -- pskClientFinishedTag resolves to 3rd branch
  have h1 : (pskClientFinishedTag == clientFinishedTag) = false := by decide
  have h2 : (pskClientFinishedTag == serverFinishedTag) = false := by decide
  have h3 : (pskClientFinishedTag == pskClientFinishedTag) = true := by decide
  rw [if_neg (by rw [h1]; decide), if_neg (by rw [h2]; decide), if_pos (by rw [h3])]
  refine ⟨server, _, rfl, .inl ⟨(ptr₄ client server psk).length, ?_, ?_⟩⟩
  · -- (ptr₄ c s psk).length < (ptr₆ c s psk).length
    unfold ptr₆ ptr₅ ptr₄ ptr₃ ptr₂ ptr₁ ptr₀
    simp [Trace.length]
  · -- eventTriggeredAt at position ptr₄.length in ptr₇
    show (Trace.snoc (ptr₆ client server psk)
        (.event client pskClientFinishedTag
          (mkPSKFinishedContent client server (psk_appKey client server psk)))).entryAt
      (ptr₄ client server psk).length =
      some (.event server pskServerFinishedTag
        (mkPSKFinishedContent server client (psk_appKey client server psk)))
    unfold ptr₆ ptr₅
    simp [Trace.entryAt, Trace.length, ptr₄, ptr₃, ptr₂, ptr₁, ptr₀]

end CatCrypt.Crypto.Symbolic.TLS
