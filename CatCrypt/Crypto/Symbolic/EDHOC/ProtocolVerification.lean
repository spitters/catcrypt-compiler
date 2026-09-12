/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Invariants
public import CatCrypt.Crypto.Symbolic.TracefulSpec
public import CatCrypt.Crypto.Symbolic.SigningDiscipline

/-!
# EDHOC Protocol Verification

Proves that EDHOC Method 0 (SIG-SIG) honest session maintains
`traceInvariant`, starting from the empty trace. Methods 1-3 follow
the same pattern with additional DH operations.

## Main results

* `edhocEventPredMono` — EDHOC invariants are monotone under snoc
* `honestSession_m0_invariant` — M0 honest session maintains invariant from `.nil`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-! ## EventPredMono Instance -/

instance edhocEventPredMono : EventPredMono where
  toProtocolInvariants := edhocInvariants
  eventPred_mono_snoc := by
    intro tr e i hi prin tag content
    show edhocEventPred tr i prin tag content → edhocEventPred (.snoc tr e) i prin tag content
    unfold edhocEventPred
    split
    · rintro ⟨peer, prk_out, hcontent, hauth⟩
      exact ⟨peer, prk_out, hcontent, hauth.elim
        (fun ⟨j, hji, g_y, hevent⟩ => .inl ⟨j, hji, g_y, by
          show (Trace.snoc tr e).entryAt j = _
          rw [Trace.entryAt_snoc_ne tr e j (by omega)]
          exact hevent⟩)
        (fun ⟨k, hki, hentry⟩ => .inr ⟨k, hki, by
          rw [Trace.entryAt_snoc_ne tr e k (by omega)]
          exact hentry⟩)⟩
    · split
      · rintro ⟨peer, prk_out, hcontent, hauth⟩
        exact ⟨peer, prk_out, hcontent, hauth.elim
          (fun ⟨j, hji, hevent⟩ => .inl ⟨j, hji, by
            show (Trace.snoc tr e).entryAt j = _
            rw [Trace.entryAt_snoc_ne tr e j (by omega)]
            exact hevent⟩)
          (fun ⟨k, hki, hentry⟩ => .inr ⟨k, hki, by
            rw [Trace.entryAt_snoc_ne tr e k (by omega)]
            exact hentry⟩)⟩
      · split <;> exact id  -- responderMsg2Tag or True
  statePred_mono_snoc := by
    intro tr e prin _ content
    show edhocStatePred tr prin _ content → edhocStatePred (.snoc tr e) prin _ content
    exact canFlow_labelOf_mono_snoc tr e _ content

/-! ## Method 0 (SIG-SIG) Honest Session

Define the trace produced by composing initiator and responder M0 roles,
using the shared DH key (avoiding symbolic DH commutativity). -/

/-- Honest M0 session: initiator and responder with signature-based auth.
Both sides use the responder-computed DH shared secret (DH commutativity). -/
def honestSession_m0 (I R : String) (sigKey_I sigKey_R : Bytes) :
    Traceful Bytes := do
  -- Initiator: generate ephemeral DH
  let x ← mkRand .dhKey (principalLabel I) 32
  let g_x := Bytes.dhPub x
  triggerEvent I initiatorMsg1Tag (mkMsg1Content I R g_x)
  sendMsg (mkMsg1Content I R g_x)
  -- Responder: generate ephemeral DH, compute shared secret
  let y ← mkRand .dhKey (principalLabel R) 32
  let g_y := Bytes.dhPub y
  let dh_xy := Bytes.dh y g_x  -- responder's view
  let prk_out := edhocKeySchedule_m0 dh_xy
  -- Responder: sign and send message_2
  let nonce_R ← mkRand .nonce (principalLabel R) 32
  let sig_2 := Bytes.sign sigKey_R nonce_R (Bytes.hash g_y)
  triggerEvent R responderMsg2Tag (mkMsg2Content R I g_y prk_out)
  sendMsg (Bytes.concat g_y sig_2)
  -- Initiator: sign and send message_3 (using shared prk_out)
  let nonce_I ← mkRand .nonce (principalLabel I) 32
  let sig_3 := Bytes.sign sigKey_I nonce_I (Bytes.hash g_x)
  triggerEvent I initiatorMsg3Tag (mkMsg3Content I R prk_out)
  sendMsg sig_3
  -- Responder: verify and trigger final event
  triggerEvent R responderVerifiedTag (mkMsg3Content I R prk_out)
  return prk_out

abbrev Inv := @traceInvariant edhocInvariants

/-! ### Named Intermediate Traces -/

noncomputable def tr₀ : Trace := .nil

noncomputable def eX (I : String) := Bytes.rand .dhKey 32 0
noncomputable def tr₁ (I : String) : Trace :=
  .snoc tr₀ (.randGen .dhKey (principalLabel I) 32)

noncomputable def gX (I : String) := Bytes.dhPub (eX I)

noncomputable def tr₂ (I R : String) : Trace :=
  .snoc (tr₁ I) (.event I initiatorMsg1Tag (mkMsg1Content I R (gX I)))
noncomputable def tr₃ (I R : String) : Trace :=
  .snoc (tr₂ I R) (.msgSent (mkMsg1Content I R (gX I)))

noncomputable def eY (I R : String) := Bytes.rand .dhKey 32 (tr₃ I R).length
noncomputable def tr₄ (I R : String) : Trace :=
  .snoc (tr₃ I R) (.randGen .dhKey (principalLabel R) 32)

noncomputable def gY (I R : String) := Bytes.dhPub (eY I R)
noncomputable def dhXY (I R : String) := Bytes.dh (eY I R) (gX I)
noncomputable def prkOut (I R : String) := edhocKeySchedule_m0 (dhXY I R)

noncomputable def nonceR (I R : String) := Bytes.rand .nonce 32 (tr₄ I R).length
noncomputable def tr₅ (I R : String) : Trace :=
  .snoc (tr₄ I R) (.randGen .nonce (principalLabel R) 32)

noncomputable def sig2 (I R : String) (sigKey_R : Bytes) :=
  Bytes.sign sigKey_R (nonceR I R) (Bytes.hash (gY I R))

noncomputable def msg2Content (I R : String) :=
  mkMsg2Content R I (gY I R) (prkOut I R)

noncomputable def tr₆ (I R : String) : Trace :=
  .snoc (tr₅ I R) (.event R responderMsg2Tag (msg2Content I R))
noncomputable def tr₇ (I R : String) (sigKey_R : Bytes) : Trace :=
  .snoc (tr₆ I R) (.msgSent (.concat (gY I R) (sig2 I R sigKey_R)))

noncomputable def nonceI (I R : String) (sigKey_R : Bytes) :=
  Bytes.rand .nonce 32 (tr₇ I R sigKey_R).length
noncomputable def tr₈ (I R : String) (sigKey_R : Bytes) : Trace :=
  .snoc (tr₇ I R sigKey_R) (.randGen .nonce (principalLabel I) 32)

noncomputable def sig3 (I R : String) (sigKey_I sigKey_R : Bytes) :=
  Bytes.sign sigKey_I (nonceI I R sigKey_R) (Bytes.hash (gX I))

noncomputable def msg3Content (I R : String) :=
  mkMsg3Content I R (prkOut I R)

noncomputable def tr₉ (I R : String) (sigKey_R : Bytes) : Trace :=
  .snoc (tr₈ I R sigKey_R) (.event I initiatorMsg3Tag (msg3Content I R))
noncomputable def tr₁₀ (I R : String) (sigKey_I sigKey_R : Bytes) : Trace :=
  .snoc (tr₉ I R sigKey_R) (.msgSent (sig3 I R sigKey_I sigKey_R))
noncomputable def tr₁₁ (I R : String) (sigKey_I sigKey_R : Bytes) : Trace :=
  .snoc (tr₁₀ I R sigKey_I sigKey_R) (.event R responderVerifiedTag (msg3Content I R))

/-- The output of `honestSession_m0` is `tr₁₁`. -/
theorem honestSession_m0_eq (I R : String) (sigKey_I sigKey_R : Bytes) :
    (honestSession_m0 I R sigKey_I sigKey_R .nil).2 = tr₁₁ I R sigKey_I sigKey_R := by
  unfold honestSession_m0 tr₁₁ tr₁₀ tr₉ tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀
  unfold msg3Content msg2Content sig3 sig2 nonceI nonceR prkOut dhXY gY gX eY eX
  simp only [bind, instMonadTraceful, mkRand, triggerEvent, sendMsg,
    Trace.length_nil, Trace.length_snoc]
  rfl

/-- The honest EDHOC M0 session maintains trace invariant from the empty trace.

**No `traceInvariant` hypothesis** — derived from `traceInvariant .nil`. -/
theorem honestSession_m0_invariant (I R : String) (sigKey_I sigKey_R : Bytes) :
    Inv (honestSession_m0 I R sigKey_I sigKey_R .nil).2 := by
  rw [honestSession_m0_eq]
  unfold tr₁₁
  -- Chain of intermediate invariants
  have hInv₀ : Inv tr₀ := traceInvariant_nil
  have hInv₁ : Inv (tr₁ I) := traceInvariant_randGen hInv₀ (Or.inl rfl)
  have hInv₂ : Inv (tr₂ I R) := by
    unfold tr₂; apply traceInvariant_event hInv₁
    show edhocEventPred _ _ _ _ _; unfold edhocEventPred
    simp [initiatorMsg1Tag, initiatorMsg3Tag, responderVerifiedTag, responderMsg2Tag]
  have hInv₃ : Inv (tr₃ I R) := by
    unfold tr₃; apply traceInvariant_sendMsg hInv₂
    unfold gX; simp [bytesPublishable, labelOf, mkMsg1Content, Label.isCorrupt]
  have hInv₄ : Inv (tr₄ I R) := traceInvariant_randGen hInv₃ (Or.inl rfl)
  have hInv₅ : Inv (tr₅ I R) := traceInvariant_randGen hInv₄ (Or.inr (Or.inl rfl))
  have hInv₆ : Inv (tr₆ I R) := by
    unfold tr₆; apply traceInvariant_event hInv₅
    show edhocEventPred _ _ _ _ _; unfold edhocEventPred
    simp [responderMsg2Tag, initiatorMsg3Tag, responderVerifiedTag]
    exact ⟨I, _, _, rfl⟩
  have hInv₇ : Inv (tr₇ I R sigKey_R) := by
    unfold tr₇; apply traceInvariant_sendMsg hInv₆
    unfold gY sig2; simp [bytesPublishable, labelOf, Label.isCorrupt]
  have hInv₈ : Inv (tr₈ I R sigKey_R) := traceInvariant_randGen hInv₇ (Or.inr (Or.inl rfl))
  have hInv₉ : Inv (tr₉ I R sigKey_R) := by
    unfold tr₉; apply traceInvariant_event hInv₈
    show edhocEventPred _ _ _ _ _; unfold edhocEventPred
    simp only [initiatorMsg3Tag, BEq.beq]
    -- Need: ∃ peer prk_out, ... ∧ (∃ j < i, ∃ g_y, ResponderMsg2 at j ∨ corrupt)
    refine ⟨R, _, rfl, .inl ⟨(tr₅ I R).length, ?_, gY I R, ?_⟩⟩
    · unfold tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀; simp [Trace.length]
    · -- ResponderMsg2 at position tr₅.length
      show (Trace.snoc (tr₈ I R sigKey_R) _).entryAt (tr₅ I R).length = _
      unfold tr₈ tr₇ tr₆ msg2Content
      simp [Trace.entryAt, Trace.length, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]
  have hInv₁₀ : Inv (tr₁₀ I R sigKey_I sigKey_R) := by
    unfold tr₁₀; apply traceInvariant_sendMsg hInv₉
    unfold sig3; simp [bytesPublishable, labelOf, Label.isCorrupt]
  -- Final step: responderVerified requires matching initiatorMsg3
  apply traceInvariant_event hInv₁₀
  show edhocEventPred _ _ _ _ _; unfold edhocEventPred
  -- Navigate past the tag comparisons via split
  split
  · -- responderVerifiedTag ≠ initiatorMsg3Tag
    exfalso; unfold responderVerifiedTag initiatorMsg3Tag at *; simp_all
  · split
    · -- responderVerifiedTag = responderVerifiedTag ✓
      refine ⟨I, _, rfl, .inl ⟨(tr₈ I R sigKey_R).length, ?_, ?_⟩⟩
      · unfold tr₁₀ tr₉ tr₈ tr₇ tr₆ tr₅ tr₄ tr₃ tr₂ tr₁ tr₀; simp [Trace.length]
      · -- InitiatorMsg3 at position tr₈.length
        show (Trace.snoc (tr₁₀ I R sigKey_I sigKey_R) _).entryAt
          (tr₈ I R sigKey_R).length = _
        unfold tr₁₀ tr₉ msg3Content
        simp [Trace.entryAt, Trace.length, tr₈, tr₇, tr₆, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]
    · split
      · exfalso; unfold responderVerifiedTag responderMsg2Tag at *; simp_all
      · trivial

/-- The honest M0 session triggers a `ResponderMsg2` event. -/
theorem honestSession_m0_responderMsg2 (I R : String) (sigKey_I sigKey_R : Bytes) :
    ∃ j, (honestSession_m0 I R sigKey_I sigKey_R .nil).2.eventTriggeredAt
      j R responderMsg2Tag (msg2Content I R) := by
  rw [honestSession_m0_eq]
  exact ⟨(tr₅ I R).length, by
    unfold tr₁₁ tr₁₀ tr₉ tr₈ tr₇ tr₆ Trace.eventTriggeredAt
    simp [Trace.entryAt, Trace.length, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]⟩

/-- The honest M0 session triggers an `InitiatorMsg3` event. -/
theorem honestSession_m0_initiatorMsg3 (I R : String) (sigKey_I sigKey_R : Bytes) :
    ∃ j, (honestSession_m0 I R sigKey_I sigKey_R .nil).2.eventTriggeredAt
      j I initiatorMsg3Tag (msg3Content I R) := by
  rw [honestSession_m0_eq]
  exact ⟨(tr₈ I R sigKey_R).length, by
    unfold tr₁₁ tr₁₀ tr₉ Trace.eventTriggeredAt
    simp [Trace.entryAt, Trace.length, tr₈, tr₇, tr₆, tr₅, tr₄, tr₃, tr₂, tr₁, tr₀]⟩

/-- The honest M0 session triggers a `ResponderVerified` event. -/
theorem honestSession_m0_responderVerified (I R : String) (sigKey_I sigKey_R : Bytes) :
    ∃ j, (honestSession_m0 I R sigKey_I sigKey_R .nil).2.eventTriggeredAt
      j R responderVerifiedTag (msg3Content I R) := by
  rw [honestSession_m0_eq]
  exact ⟨(tr₁₀ I R sigKey_I sigKey_R).length, by
    unfold tr₁₁ Trace.eventTriggeredAt
    rfl⟩

end CatCrypt.Crypto.Symbolic.EDHOC
