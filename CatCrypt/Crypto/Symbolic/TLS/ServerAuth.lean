/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TLS.Invariants

/-!
# TLS 1.3: the ClientFinished / ServerFinished event correspondence

On a trace satisfying `tlsInvariants`, a `ClientFinished` event is preceded by
a matching `ServerFinished` event unless the server is corrupt.

## Main result

* `tls13_server_authentication` — the correspondence, read back from
  `tlsEventPred`

## Scope

* `tlsEventPred` requires, for every `ClientFinished` event, a matching earlier
  `ServerFinished` event or a corrupt server. The theorem unpacks that
  requirement and identifies the peer and key by injectivity of
  `mkFinishedContent`. No signature or MAC predicate enters the proof, and
  `attacker_only_knows_publishable` is not used.
* `traceInvariant` for `tlsInvariants` is established only for the single
  honest trace `tr₈` (`honestSession_invariant`). No theorem shows that a trace
  with attacker sends, corruption or interleaved sessions satisfies it.
* The role programs of `Model.lean` are not verified against the invariant.
  `clientHandshake` discards the result of `Bytes.signVerify` and records
  `ClientFinished` regardless, so the correspondence is not a property of that
  program.

## References

* DY*-extrinsic: TLS13 server authentication proof
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-- On a trace satisfying the invariant, a `ClientFinished` event at `i` is
preceded by a `ServerFinished` event with the same key, or the server is
corrupt at `i`.

The conclusion is the clause of `tlsEventPred` for `ClientFinished` events,
which the invariant hypothesis supplies. The invariant is established only for
the honest trace `tr₈`, and no role program is shown to maintain it. -/
theorem tls13_server_authentication
    (tr : Trace) (i : Nat) (client server : String) (appKey : Bytes) :
    traceInvariant tr →
    tr.eventTriggeredAt i client clientFinishedTag
      (mkFinishedContent client server appKey) →
    (∃ j, j < i ∧ tr.eventTriggeredAt j server serverFinishedTag
      (mkFinishedContent server client appKey)) ∨
    tr.isCorruptAt server i := by
  intro hInv hEvent
  -- Extract the event entry from the trace
  have hi := Trace.entryAt_lt_length hEvent
  -- The trace invariant at position i gives us the event predicate
  have hPred := hInv i hi _ hEvent
  -- Unfold through the typeclass to get tlsEventPred
  change tlsEventPred tr i client clientFinishedTag (mkFinishedContent client server appKey) at hPred
  unfold tlsEventPred at hPred
  simp only [beq_self_eq_true, ↓reduceIte] at hPred
  obtain ⟨peer, appKey', hcontent, hauth⟩ := hPred
  -- From hcontent: mkFinishedContent client server appKey = mkFinishedContent client peer appKey'
  -- This gives peer = server and appKey' = appKey by injectivity
  simp only [mkFinishedContent, Bytes.concat.injEq, Bytes.literal.injEq] at hcontent
  obtain ⟨_, hpeer_key⟩ := hcontent
  obtain ⟨hpeer, happKey⟩ := hpeer_key
  have hpeer' : peer = server := String.toUTF8_injective hpeer.symm
  subst hpeer'; subst happKey
  exact hauth

end CatCrypt.Crypto.Symbolic.TLS
