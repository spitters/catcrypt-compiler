/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TLS.Invariants

/-!
# TLS 1.3 Key Secrecy

Theorem: The application traffic key derived during the TLS 1.3 handshake
is not known to the attacker unless one of the participants is compromised.

## Main result

* `tls13_key_secrecy` — session key secrecy

## Proof

1. By `attacker_only_knows_publishable`, `bytesPublishable tr appKey`
2. The appKey is derived via `keySchedule(dh(x, dhPub(y)))` where x has
   label `principalLabel client`
3. Computing `labelOf` through `keySchedule`: the label reduces to a nested
   meet of `.top` values and `principalLabel client`
4. `isCorrupt` of this label requires `corruptSet client`
5. Therefore `isCorruptAt client (tr.length - 1)`

## References

* DY*-extrinsic: TLS13 key secrecy proof
* ProVerif: `query attacker(appKey) ==> corrupt(client) | corrupt(server)`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-- The label of the TLS key schedule output only depends on the label of
the DH shared secret (all other inputs are public constants). -/
private theorem labelOf_keySchedule (tr : Trace) (dhSS : Bytes) :
    labelOf tr (keySchedule dhSS) =
    .meet (.meet (.meet .top .top) (labelOf tr dhSS)) .top := by
  rfl

/-- **Key Secrecy**: The TLS 1.3 application traffic key is secret
unless either the client or the server is compromised. -/
theorem tls13_key_secrecy
    (tr : Trace) (client server : String) (appKey : Bytes)
    (x y : Bytes)
    (hKey : appKey = keySchedule (Bytes.dh x (Bytes.dhPub y)))
    (hLabelX : hasLabel tr x (principalLabel client))
    (hLabelY : hasLabel tr y (principalLabel server)) :
    traceInvariant tr →
    AttackerKnows tr appKey →
    tr.isCorruptAt client (tr.length - 1) ∨
    tr.isCorruptAt server (tr.length - 1) := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  -- Compute the label: keySchedule preserves DH label through meet with .top
  unfold bytesPublishable at hPub
  rw [labelOf_keySchedule] at hPub
  -- labelOf tr (dh x (dhPub y)) = labelOf tr x = principalLabel client
  have hDHLabel : labelOf tr (Bytes.dh x (Bytes.dhPub y)) = principalLabel client := by
    show labelOf tr x = principalLabel client
    exact hLabelX
  rw [hDHLabel] at hPub
  -- hPub : (.meet (.meet (.meet .top .top) (principalLabel client)) .top).isCorrupt tr.corruptSet
  -- This reduces to: tr.corruptSet client
  simp only [Label.isCorrupt, principalLabel, and_true, true_and] at hPub
  -- hPub : tr.corruptSet client
  left
  obtain ⟨i, hi, hentry⟩ := hPub
  exact ⟨i, by omega, hentry⟩

end CatCrypt.Crypto.Symbolic.TLS
