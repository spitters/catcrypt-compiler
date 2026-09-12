/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Invariants

/-!
# EDHOC Key Secrecy

Theorem: The EDHOC session key (prk_out) is not known to the attacker
unless one of the participants is compromised.

## Main results

* `edhoc_m3_key_secrecy` — key secrecy for Method 3 (STAT-STAT)
* `edhoc_m0_key_secrecy` — key secrecy for Method 0 (SIG-SIG)
* `edhoc_m1_key_secrecy` — key secrecy for Method 1 (SIG-STAT)
* `edhoc_m2_key_secrecy` — key secrecy for Method 2 (STAT-SIG)

## Proof

The key insight: `labelOf(dh(sk, _)) = labelOf(sk)`, and for an initiator's
ephemeral key `x` with label `principalLabel I`, we have:
- `labelOf(dh(x, g_y)) = principalLabel I`
- `labelOf(kdfExtract(salt, ikm)) = meet(labelOf(salt), labelOf(ikm))`
- `labelOf(kdfExpand(prk, _, _)) = labelOf(prk)`

All `.top` components (from hash, literal) contribute nothing.
The final label reduces to include `principalLabel I`, so the attacker
can only know the key if the initiator is corrupted.

## References

* DY*-extrinsic: TLS13 key secrecy proof (same label analysis pattern)
* ProVerif: `query attacker(prk_out) ==> corrupt(I) | corrupt(R)`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

/-! ## Label Analysis for Key Schedules

Label computation for each key schedule:

- **m0**: `kdfExpand(kdfExtract(hash(dhXY), dhXY), _, _)`
  = `labelOf(kdfExtract(hash(dhXY), dhXY))`
  = `meet(top, labelOf(dhXY))`

- **m1**: `kdfExpand(kdfExtract(kdfExpand(kdfExtract(hash(dhXY), dhXY), _, _), dhRX), _, _)`
  = `labelOf(kdfExtract(salt_3e2m, dhRX))`
  = `meet(meet(top, labelOf(dhXY)), labelOf(dhRX))`

- **m2**: same structure as m1 but with dhIY instead of dhRX

- **m3**: `meet(meet(meet(top, labelOf(dhXY)), labelOf(dhRX)), labelOf(dhIY))`
-/

/-- Label of Method 0 key schedule: `meet(top, labelOf(dhXY))`. -/
private theorem labelOf_edhocKeySchedule_m0 (tr : Trace) (dhXY : Bytes) :
    labelOf tr (edhocKeySchedule_m0 dhXY) =
    .meet .top (labelOf tr dhXY) := by
  rfl

/-- Label of Method 1 key schedule: `meet(meet(top, labelOf(dhXY)), labelOf(dhRX))`. -/
theorem labelOf_edhocKeySchedule_m1 (tr : Trace) (dhXY dhRX : Bytes) :
    labelOf tr (edhocKeySchedule_m1 dhXY dhRX) =
    .meet (.meet .top (labelOf tr dhXY)) (labelOf tr dhRX) := by
  rfl

/-- Label of Method 2 key schedule: `meet(meet(top, labelOf(dhXY)), labelOf(dhIY))`. -/
theorem labelOf_edhocKeySchedule_m2 (tr : Trace) (dhXY dhIY : Bytes) :
    labelOf tr (edhocKeySchedule_m2 dhXY dhIY) =
    .meet (.meet .top (labelOf tr dhXY)) (labelOf tr dhIY) := by
  rfl

/-- Label of Method 3 key schedule:
    `meet(meet(meet(top, labelOf(dhXY)), labelOf(dhRX)), labelOf(dhIY))`. -/
private theorem labelOf_edhocKeySchedule_m3 (tr : Trace) (dhXY dhRX dhIY : Bytes) :
    labelOf tr (edhocKeySchedule_m3 dhXY dhRX dhIY) =
    .meet (.meet (.meet .top (labelOf tr dhXY)) (labelOf tr dhRX))
      (labelOf tr dhIY) := by
  rfl

/-! ## Key Secrecy Theorems -/

/-- **Key Secrecy (Method 3, STAT-STAT)**: The EDHOC session key for
Method 3 is secret unless the initiator is corrupted.

The initiator's ephemeral key `x` has label `principalLabel I`.
Since `labelOf(dh(x, _)) = labelOf(x) = principalLabel I`,
the entire key schedule's label includes `principalLabel I`.
Therefore, the attacker can only derive the key if `I` is corrupted. -/
theorem edhoc_m3_key_secrecy
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x : Bytes) (g_y pk_R : Bytes) (sk_I : Bytes)
    (hKey : prk_out = edhocKeySchedule_m3
      (Bytes.dh x g_y) (Bytes.dh x pk_R) (Bytes.dh sk_I g_y))
    (hLabelX : hasLabel tr x (principalLabel I)) :
    traceInvariant tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I (tr.length - 1) := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_edhocKeySchedule_m3] at hPub
  -- labelOf(dh(x, _)) = labelOf(x) = principalLabel I
  have hDH1 : labelOf tr (Bytes.dh x g_y) = principalLabel I := hLabelX
  have hDH2 : labelOf tr (Bytes.dh x pk_R) = principalLabel I := hLabelX
  rw [hDH1, hDH2] at hPub
  simp only [Label.isCorrupt, principalLabel, true_and] at hPub
  obtain ⟨⟨hcI, _⟩, _⟩ := hPub
  obtain ⟨j, hj, hentry⟩ := hcI
  exact ⟨j, by omega, hentry⟩

/-- **Key Secrecy (Method 0, SIG-SIG)**: Single ephemeral DH. -/
theorem edhoc_m0_key_secrecy
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x g_y : Bytes)
    (hKey : prk_out = edhocKeySchedule_m0 (Bytes.dh x g_y))
    (hLabelX : hasLabel tr x (principalLabel I)) :
    traceInvariant tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I (tr.length - 1) := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_edhocKeySchedule_m0] at hPub
  have hDH : labelOf tr (Bytes.dh x g_y) = principalLabel I := hLabelX
  rw [hDH] at hPub
  simp only [Label.isCorrupt, principalLabel, true_and] at hPub
  obtain ⟨j, hj, hentry⟩ := hPub
  exact ⟨j, by omega, hentry⟩

/-- **Key Secrecy (Method 1, SIG-STAT)**: Ephemeral + responder static DH. -/
theorem edhoc_m1_key_secrecy
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x g_y pk_R : Bytes)
    (hKey : prk_out = edhocKeySchedule_m1 (Bytes.dh x g_y) (Bytes.dh x pk_R))
    (hLabelX : hasLabel tr x (principalLabel I)) :
    traceInvariant tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I (tr.length - 1) := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_edhocKeySchedule_m1] at hPub
  have hDH1 : labelOf tr (Bytes.dh x g_y) = principalLabel I := hLabelX
  have hDH2 : labelOf tr (Bytes.dh x pk_R) = principalLabel I := hLabelX
  rw [hDH1, hDH2] at hPub
  simp only [Label.isCorrupt, principalLabel, true_and] at hPub
  obtain ⟨j, hj, hentry⟩ := hPub.1
  exact ⟨j, by omega, hentry⟩

/-- **Key Secrecy (Method 2, STAT-SIG)**: Ephemeral + initiator static DH. -/
theorem edhoc_m2_key_secrecy
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x g_y sk_I : Bytes)
    (hKey : prk_out = edhocKeySchedule_m2 (Bytes.dh x g_y) (Bytes.dh sk_I g_y))
    (hLabelX : hasLabel tr x (principalLabel I)) :
    traceInvariant tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I (tr.length - 1) := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_edhocKeySchedule_m2] at hPub
  have hDH : labelOf tr (Bytes.dh x g_y) = principalLabel I := hLabelX
  rw [hDH] at hPub
  simp only [Label.isCorrupt, principalLabel, true_and] at hPub
  obtain ⟨j, hj, hentry⟩ := hPub.1
  exact ⟨j, by omega, hentry⟩

end CatCrypt.Crypto.Symbolic.EDHOC
