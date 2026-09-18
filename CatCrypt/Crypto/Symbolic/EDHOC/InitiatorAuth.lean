/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Invariants

/-!
# EDHOC: the ResponderVerified / InitiatorMsg3 event correspondence

On a trace satisfying `edhocInvariants`, a `ResponderVerified` event is
preceded by a matching `InitiatorMsg3` event unless the initiator is corrupt.

## Main result

* `edhoc_initiator_authentication` — the correspondence, read back from
  `edhocEventPred`

## Proof

1. The invariant gives `edhocEventPred` at the position of the
   `ResponderVerified(I, R, prk_out)` event.
2. That clause states that a matching `InitiatorMsg3` event exists or the
   initiator is corrupt.
3. Injectivity of `mkMsg3Content` identifies the peer and the key.

## Scope

* The correspondence is postulated by `edhocEventPred`. No signature or MAC
  predicate enters the proof.
* `traceInvariant` for `edhocInvariants` is established only for the single
  honest method-0 trace `tr₁₁` (`honestSession_m0_invariant`).
* The role programs of `Model.lean` are not verified. The responder programs
  of methods 0 and 1 discard the result of `Bytes.signVerify` on `sig_3`, and
  those of methods 2 and 3 do not check `mac_3`; each records
  `ResponderVerified` regardless.

## References

* DY*-extrinsic: mutual authentication proofs
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-- On a trace satisfying the invariant, a `ResponderVerified` event at `i` is
preceded by an `InitiatorMsg3` event with the same key, or the initiator is
corrupt at `i`.

The conclusion is the clause of `edhocEventPred` for `ResponderVerified`
events, which the invariant hypothesis supplies. The invariant is established
only for the honest method-0 trace `tr₁₁`, and no role program is shown to
maintain it. -/
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
