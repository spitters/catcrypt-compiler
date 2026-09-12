/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Invariants

/-!
# EDHOC Responder Authentication

Theorem: If an initiator completes message_3 (triggers `InitiatorMsg3`),
then either the responder also sent message_2 (triggered `ResponderMsg2`),
or the responder is compromised.

## Main result

* `edhoc_responder_authentication` — responder authentication via correspondence

## Proof Sketch

1. Initiator triggers `InitiatorMsg3(I, R, prk_out)` at position `i`
2. By `eventPred`, the initiator verified the responder's message_2
3. By `edhocEventPred`, either a matching `ResponderMsg2` event exists,
   or the responder is corrupted
4. Injectivity of `mkMsg3Content` extracts the peer identity and key

## References

* DY*-extrinsic: TLS13 server authentication proof (same pattern)
* ProVerif: `query event(InitMsg3(I,R,k)) ==> event(RespMsg2(R,I,_,k)) | corrupt(R)`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-- **Responder Authentication**: If an initiator completes the EDHOC handshake
(sending message_3), then the responder also participated (sending message_2
with a matching key), or the responder is compromised.

This is the EDHOC analogue of TLS 1.3 server authentication. -/
theorem edhoc_responder_authentication
    (tr : Trace) (i : Nat) (initiator responder : String) (prk_out : Bytes) :
    traceInvariant tr →
    tr.eventTriggeredAt i initiator initiatorMsg3Tag
      (mkMsg3Content initiator responder prk_out) →
    (∃ j, j < i ∧ ∃ g_y, tr.eventTriggeredAt j responder responderMsg2Tag
      (mkMsg2Content responder initiator g_y prk_out)) ∨
    tr.isCorruptAt responder i := by
  intro hInv hEvent
  have hi := Trace.entryAt_lt_length hEvent
  have hPred := hInv i hi _ hEvent
  change edhocEventPred tr i initiator initiatorMsg3Tag
    (mkMsg3Content initiator responder prk_out) at hPred
  unfold edhocEventPred at hPred
  simp only [beq_self_eq_true, ↓reduceIte] at hPred
  obtain ⟨peer, prk_out', hcontent, hauth⟩ := hPred
  simp only [mkMsg3Content, Bytes.concat.injEq, Bytes.literal.injEq] at hcontent
  obtain ⟨_, hpeer_key⟩ := hcontent
  obtain ⟨hpeer, hprk⟩ := hpeer_key
  have hpeer' : peer = responder := String.toUTF8_injective hpeer.symm
  subst hpeer'; subst hprk
  exact hauth

end CatCrypt.Crypto.Symbolic.EDHOC
