/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.TLS.Invariants

/-!
# TLS 1.3 PSK Key Secrecy

Proves that PSK-derived application keys remain secret unless
a session principal is corrupted.

## Main Results

* `tls13_psk_key_secrecy` — PSK application key secrecy
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.TLS

open CatCrypt.Crypto.Symbolic

/-- The label of the PSK key schedule output depends on the PSK label
    and the DH shared secret label. -/
theorem labelOf_pskKeySchedule (tr : Trace) (psk dhSS : Bytes) :
    labelOf tr (pskKeySchedule psk dhSS) =
    .meet (.meet (.meet .top (labelOf tr psk)) (labelOf tr dhSS)) .top := by
  rfl

/-- **PSK Key Secrecy**: If the attacker learns the PSK-derived application key,
    then the client is corrupted (because the DH ephemeral x has the client's
    principal label, which flows into the key schedule). -/
theorem tls13_psk_key_secrecy
    (tr : Trace) (client server : String)
    (appKey : Bytes) (x y : Bytes) (psk : Bytes)
    (hKey : appKey = pskKeySchedule psk (Bytes.dh x (Bytes.dhPub y)))
    (hLabelX : hasLabel tr x (principalLabel client))
    (hLabelY : hasLabel tr y (principalLabel server))
    (hInv : @traceInvariant tlsInvariants tr)
    (hKnows : AttackerKnows tr appKey) :
    tr.isCorruptAt client (tr.length - 1) ∨
    tr.isCorruptAt server (tr.length - 1) := by
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_pskKeySchedule] at hPub
  -- labelOf(dh x (dhPub y)) = labelOf(x) = principalLabel client
  have hDHLabel : labelOf tr (Bytes.dh x (Bytes.dhPub y)) = principalLabel client := by
    show labelOf tr x = principalLabel client
    exact hLabelX
  rw [hDHLabel] at hPub
  -- hPub requires corruptSet client (through the meet structure)
  simp only [Label.isCorrupt, principalLabel, and_true, true_and] at hPub
  left
  obtain ⟨i, hi, hentry⟩ := hPub.2
  exact ⟨i, by omega, hentry⟩

end CatCrypt.Crypto.Symbolic.TLS
