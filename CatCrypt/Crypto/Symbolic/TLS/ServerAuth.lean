/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TLS.Invariants

/-!
# TLS 1.3 Server Authentication

Theorem: If a client completes a handshake (triggers `ClientFinished`),
then either the server also completed its side (triggered `ServerFinished`),
or the server's signing key is compromised.

## Main result

* `tls13_server_authentication` — server authentication via correspondence

## Proof Sketch

1. Client triggers `ClientFinished(client, server, appKey)` at position `i`
2. By `eventPred`, the client verified a signature from `server`
3. The signature `sign(sk_s, nonce, transcript)` was verified against `vk(sk_s)`
4. By `attacker_only_knows_publishable`, if the attacker produced the signature,
   then `sk_s` must be publishable (= server is corrupted)
5. If the attacker did NOT produce it, then the server must have produced it,
   which means `ServerFinished` was triggered

## References

* DY*-extrinsic: TLS13 server authentication proof
* ProVerif: `query event(ClientFinished(x,y,k)) ==> event(ServerFinished(y,x,k)) | corrupt(y)`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-- **Server Authentication**: If a client completes the TLS 1.3 handshake,
then the server also completed it (with matching keys), or the server
is compromised.

This corresponds to ProVerif's authentication query and is the first
of the four main symbolic security properties. -/
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
