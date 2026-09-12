/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Invariants

/-!
# EDHOC Initiator Authentication

Theorem: If a responder verifies message_3 (triggers `ResponderVerified`),
then either the initiator actually sent message_3 (triggered `InitiatorMsg3`),
or the initiator is compromised.

## Main result

* `edhoc_initiator_authentication` — initiator authentication via correspondence

## Proof Sketch

1. Responder triggers `ResponderVerified(I, R, prk_out)` at position `i`
2. By `edhocEventPred`, either a matching `InitiatorMsg3` event exists,
   or the initiator is corrupted
3. Injectivity of `mkMsg3Content` extracts the peer identity and key

This is the dual of responder authentication, analogous to client
authentication in mutual-auth TLS.

## References

* DY*-extrinsic: mutual authentication proofs
* ProVerif: `query event(RespVerified(R,I,k)) ==> event(InitMsg3(I,R,k)) | corrupt(I)`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-- **Initiator Authentication**: If a responder verifies the EDHOC handshake
(confirming message_3), then the initiator actually sent message_3
with a matching key, or the initiator is compromised.

This is the dual of responder authentication. -/
theorem edhoc_initiator_authentication
    (tr : Trace) (i : Nat) (responder initiator : String) (prk_out : Bytes) :
    traceInvariant tr →
    tr.eventTriggeredAt i responder responderVerifiedTag
      (mkMsg3Content initiator responder prk_out) →
    (∃ j, j < i ∧ tr.eventTriggeredAt j initiator initiatorMsg3Tag
      (mkMsg3Content initiator responder prk_out)) ∨
    tr.isCorruptAt initiator i := by
  intro hInv hEvent
  have hi := Trace.entryAt_lt_length hEvent
  have hPred := hInv i hi _ hEvent
  change edhocEventPred tr i responder responderVerifiedTag
    (mkMsg3Content initiator responder prk_out) at hPred
  unfold edhocEventPred at hPred
  unfold responderVerifiedTag initiatorMsg3Tag responderMsg2Tag at hPred
  simp only [beq_self_eq_true, ↓reduceIte] at hPred
  obtain ⟨peer, prk_out', hcontent, hauth⟩ := hPred
  simp only [mkMsg3Content, Bytes.concat.injEq, Bytes.literal.injEq] at hcontent
  obtain ⟨hpeer, hrest⟩ := hcontent
  obtain ⟨_, hprk⟩ := hrest
  have hpeer' : peer = initiator := String.toUTF8_injective hpeer.symm
  subst hpeer'; subst hprk
  exact hauth

end CatCrypt.Crypto.Symbolic.EDHOC
