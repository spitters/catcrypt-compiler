/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Invariants

/-!
# EDHOC: the InitiatorMsg3 / ResponderMsg2 event correspondence

On a trace satisfying `edhocInvariants`, an `InitiatorMsg3` event is preceded
by a matching `ResponderMsg2` event unless the responder is corrupt.

## Main result

* `edhoc_responder_authentication` — the correspondence, read back from
  `edhocEventPred`

## Proof

1. The invariant gives `edhocEventPred` at the position of the
   `InitiatorMsg3(I, R, prk_out)` event.
2. That clause states that a matching `ResponderMsg2` event exists or the
   responder is corrupt.
3. Injectivity of `mkMsg3Content` identifies the peer and the key.

## Scope

* The correspondence is postulated by `edhocEventPred`. No signature or MAC
  predicate enters the proof.
* `traceInvariant` for `edhocInvariants` is established only for the single
  honest method-0 trace `tr₁₁` (`honestSession_m0_invariant`). No theorem
  covers attacker sends, corruption, interleaved sessions or methods 1–3.
* The role programs of `Model.lean` are not verified. The initiator programs
  of methods 0 and 2 discard the result of `Bytes.signVerify` on `sig_2`, and
  those of methods 1 and 3 do not check `mac_2`; each records `InitiatorMsg3`
  regardless.

## References

* DY*-extrinsic: TLS13 server authentication proof (same pattern)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-- On a trace satisfying the invariant, an `InitiatorMsg3` event at `i` is
preceded by a `ResponderMsg2` event with the same key, or the responder is
corrupt at `i`.

The conclusion is the clause of `edhocEventPred` for `InitiatorMsg3` events,
which the invariant hypothesis supplies. The invariant is established only for
the honest method-0 trace `tr₁₁`, and no role program is shown to maintain
it. -/
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
