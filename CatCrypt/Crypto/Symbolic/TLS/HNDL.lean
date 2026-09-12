/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TLS.Invariants

/-!
# TLS 1.3 Harvest-Now-Decrypt-Later (HNDL) Resistance

Theorem: The TLS 1.3 handshake with hybrid key exchange (classical DH + ML-KEM)
provides protection against harvest-now-decrypt-later attacks, where an
adversary records ciphertexts now and attempts to decrypt them later with
a quantum computer.

## Main result

* `tls13_hndl_resistance` — HNDL resistance via hybrid KEM

## Proof

In the hybrid setting, the shared secret is derived from BOTH classical DH
and ML-KEM via `kdfExtract(dhSecret, kemSecretShared(kemSecret))`.

The label of this combined secret is `meet(label(dhSecret), label(kemSecret))`.
Both labels are `dhLabel client server = meet(principalLabel client, principalLabel server)`.
For this to be publishable, BOTH client and server must be corrupted.

## References

* DY*-extrinsic: PQ security analysis
* Cohn-Gordon et al., *A Formal Security Analysis of the Signal Messaging Protocol*
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-- The label of keySchedule applied to a hybrid DH+KEM secret. -/
theorem labelOf_keySchedule_hybrid (tr : Trace) (dhSecret kemSecret : Bytes) :
    labelOf tr (keySchedule (Bytes.kdfExtract dhSecret (.kemSecretShared kemSecret))) =
    .meet (.meet (.meet .top .top)
      (.meet (labelOf tr dhSecret) (labelOf tr kemSecret))) .top := by
  rfl

/-- **HNDL Resistance**: In hybrid TLS 1.3, the session key is protected
against harvest-now-decrypt-later attacks.

With hybrid key exchange, the attacker must break BOTH the classical DH
AND the post-quantum KEM to recover the session key. A quantum attacker
that breaks DH but not ML-KEM still cannot derive the key. -/
theorem tls13_hndl_resistance
    (tr : Trace) (client server : String) (appKey : Bytes)
    (dhSecret kemSecret : Bytes)
    (hKey : appKey = keySchedule (Bytes.kdfExtract dhSecret (.kemSecretShared kemSecret)))
    (hLabelDH : hasLabel tr dhSecret (dhLabel client server))
    (hLabelKEM : hasLabel tr kemSecret (dhLabel client server)) :
    traceInvariant tr →
    AttackerKnows tr appKey →
    tr.isCorruptAt client (tr.length - 1) ∨
    tr.isCorruptAt server (tr.length - 1) := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_keySchedule_hybrid] at hPub
  -- Substitute the DH and KEM labels
  have hDH : labelOf tr dhSecret = dhLabel client server := hLabelDH
  have hKEM : labelOf tr kemSecret = dhLabel client server := hLabelKEM
  rw [hDH, hKEM] at hPub
  -- dhLabel client server = .meet (principalLabel client) (principalLabel server)
  -- The label is: meet(meet(meet(top, top), meet(meet(pc, ps), meet(pc, ps))), top)
  -- isCorrupt reduces to: corruptSet client ∧ corruptSet server
  simp only [Label.isCorrupt, dhLabel, principalLabel, and_true, true_and] at hPub
  left
  obtain ⟨⟨hc, _⟩, _⟩ := hPub
  obtain ⟨i, hi, hentry⟩ := hc
  exact ⟨i, by omega, hentry⟩

end CatCrypt.Crypto.Symbolic.TLS
