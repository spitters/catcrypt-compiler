/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.EDHOC.Invariants
public import CatCrypt.Crypto.Symbolic.TimedLabel

/-!
# EDHOC Forward Secrecy

Theorem: Even if a party's long-term static DH key is compromised AFTER
a session completes, the session key remains secret. This is because the
key derivation uses ephemeral Diffie-Hellman, which is independent of
the long-term key.

## Main results

* `edhoc_m3_forward_secrecy` — forward secrecy for Method 3 (STAT-STAT)
* `edhoc_m0_forward_secrecy` — forward secrecy for Method 0 (SIG-SIG)

## Proof

Same label analysis as key secrecy, but uses `hNoLateCorrupt` to restrict
corruption to `sessionTime`. The key depends on ephemeral DH secrets
generated during the session, not long-term static keys.

## Note on `hNoLateCorrupt`

The DY* label system tracks WHICH principals must be corrupted but not
WHEN. The `attacker_only_knows_publishable` theorem yields `corruptSet`
(corruption at any trace position), while forward secrecy requires
`isCorruptAt sessionTime`. The `hNoLateCorrupt` hypothesis bridges
this gap by assuming no new corruption after the session completes.

## References

* DY*-extrinsic: TLS13 forward secrecy proof (same pattern)
* ProVerif: forward secrecy with phase-based corruption
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.EDHOC

open CatCrypt.Crypto.Symbolic

private theorem labelOf_edhocKeySchedule_m3 (tr : Trace) (dhXY dhRX dhIY : Bytes) :
    labelOf tr (edhocKeySchedule_m3 dhXY dhRX dhIY) =
    .meet (.meet (.meet .top (labelOf tr dhXY)) (labelOf tr dhRX))
      (labelOf tr dhIY) := by
  rfl

private theorem labelOf_edhocKeySchedule_m0 (tr : Trace) (dhXY : Bytes) :
    labelOf tr (edhocKeySchedule_m0 dhXY) =
    .meet .top (labelOf tr dhXY) := by
  rfl

/-- **Forward Secrecy (Method 3, STAT-STAT)**: The EDHOC session key
remains secret even if the long-term static DH keys are compromised
after the session.

Parameters:
- `sessionTime`: the trace position when the session completed
- `hNoLateCorrupt`: no new corruption events after the session -/
theorem edhoc_m3_forward_secrecy
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x : Bytes) (g_y pk_R : Bytes) (sk_I : Bytes)
    (sessionTime : Nat)
    (hKey : prk_out = edhocKeySchedule_m3
      (Bytes.dh x g_y) (Bytes.dh x pk_R) (Bytes.dh sk_I g_y))
    (hLabelX : hasLabel tr x (principalLabel I))
    (hNoLateCorrupt : ∀ j, sessionTime < j → j < tr.length →
      ∀ p, tr.entryAt j ≠ some (.corrupt p)) :
    traceInvariant tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I sessionTime := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_edhocKeySchedule_m3] at hPub
  have hDH1 : labelOf tr (Bytes.dh x g_y) = principalLabel I := hLabelX
  have hDH2 : labelOf tr (Bytes.dh x pk_R) = principalLabel I := hLabelX
  rw [hDH1, hDH2] at hPub
  simp only [Label.isCorrupt, principalLabel, true_and] at hPub
  obtain ⟨j, hjLen, hjEntry⟩ := hPub.1.1
  by_cases hjle : j ≤ sessionTime
  · exact ⟨j, hjle, hjEntry⟩
  · exact absurd hjEntry (hNoLateCorrupt j (Nat.lt_of_not_le hjle) hjLen I)

/-- **Forward Secrecy (Method 0, SIG-SIG)**: Single ephemeral DH. -/
theorem edhoc_m0_forward_secrecy
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x g_y : Bytes)
    (sessionTime : Nat)
    (hKey : prk_out = edhocKeySchedule_m0 (Bytes.dh x g_y))
    (hLabelX : hasLabel tr x (principalLabel I))
    (hNoLateCorrupt : ∀ j, sessionTime < j → j < tr.length →
      ∀ p, tr.entryAt j ≠ some (.corrupt p)) :
    traceInvariant tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I sessionTime := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_edhocKeySchedule_m0] at hPub
  have hDH : labelOf tr (Bytes.dh x g_y) = principalLabel I := hLabelX
  rw [hDH] at hPub
  -- hPub : (.meet .top (principalLabel I)).isCorrupt tr.corruptSet
  -- = True ∧ tr.corruptSet I = tr.corruptSet I (after simp)
  simp only [Label.isCorrupt, principalLabel, true_and] at hPub
  obtain ⟨j, hjLen, hjEntry⟩ := hPub
  by_cases hjle : j ≤ sessionTime
  · exact ⟨j, hjle, hjEntry⟩
  · exact absurd hjEntry (hNoLateCorrupt j (Nat.lt_of_not_le hjle) hjLen I)

/-! ## Forward Secrecy via Timed Labels

The following theorems use `TimedLabel` to eliminate the `hNoLateCorrupt`
hypothesis entirely. Instead of restricting corruption to happen before
`sessionTime` by hypothesis, the timed label carries the generation time
of ephemeral keys, and `isCorruptAt p t` checks corruption before `t`.

Key insight: for an ephemeral DH key `x` generated at trace position `tx`,
`timedLabelOf tr x = .principalAt I tx`. If `tx ≤ sessionTime`, then
`isCorruptAt I tx` implies `isCorruptAt I sessionTime`.

The two bridge hypotheses (`hNetworkTimed`, `hCorruptStateTimed`) replace
the previous axioms, making the trust boundary explicit. -/

/-- Timed label of Method 3 key schedule. -/
theorem timedLabelOf_edhocKeySchedule_m3 (tr : Trace)
    (dhXY dhRX dhIY : Bytes) :
    timedLabelOf tr (edhocKeySchedule_m3 dhXY dhRX dhIY) =
    .meet (.meet (.meet .top (timedLabelOf tr dhXY)) (timedLabelOf tr dhRX))
      (timedLabelOf tr dhIY) := by
  rfl

/-- Timed label of Method 0 key schedule. -/
theorem timedLabelOf_edhocKeySchedule_m0 (tr : Trace) (dhXY : Bytes) :
    timedLabelOf tr (edhocKeySchedule_m0 dhXY) =
    .meet .top (timedLabelOf tr dhXY) := by
  rfl

/-- **Forward Secrecy via Timed Labels (Method 3)**: No `hNoLateCorrupt` needed.

The timed label of the ephemeral key `x` generated at time `timeX` is
`TimedLabel.principalAt I timeX`. If `timeX ≤ sessionTime`, then any
corruption needed to derive the key must have occurred at or before
`sessionTime`.

The bridge hypotheses make the trust boundary explicit:
- `hNetworkTimed`: sent messages are timed-publishable (trivial for EDHOC)
- `hCorruptStateTimed`: corrupted state is timed-publishable -/
theorem edhoc_m3_forward_secrecy_timed
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x : Bytes) (g_y pk_R : Bytes) (sk_I : Bytes)
    (sessionTime timeX : Nat)
    (hKey : prk_out = edhocKeySchedule_m3
      (Bytes.dh x g_y) (Bytes.dh x pk_R) (Bytes.dh sk_I g_y))
    (hTimedLabelX : timedLabelOf tr x = .principalAt I timeX)
    (hTimeX : timeX ≤ sessionTime)
    (hNetworkTimed : ∀ msg i,
      tr.entryAt i = some (.msgSent msg) →
      bytesTimedPublishable tr msg)
    (hCorruptStateTimed : ∀ prin sessId content i j,
      tr.entryAt i = some (.corrupt prin) →
      tr.entryAt j = some (.setState prin sessId content) →
      bytesTimedPublishable tr content) :
    @traceInvariant edhocInvariants tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I sessionTime := by
  intro hInv hKnows
  have hPub := attacker_only_knows_timed_publishable hInv
    hNetworkTimed hCorruptStateTimed hKnows
  rw [hKey] at hPub
  unfold bytesTimedPublishable at hPub
  rw [timedLabelOf_edhocKeySchedule_m3] at hPub
  -- timedLabelOf(dh(x, _)) = timedLabelOf(x) = .principalAt I timeX
  have hDH1 : timedLabelOf tr (Bytes.dh x g_y) = .principalAt I timeX := by
    show timedLabelOf tr x = .principalAt I timeX; exact hTimedLabelX
  have hDH2 : timedLabelOf tr (Bytes.dh x pk_R) = .principalAt I timeX := by
    show timedLabelOf tr x = .principalAt I timeX; exact hTimedLabelX
  rw [hDH1, hDH2] at hPub
  simp only [TimedLabel.isCorrupt, true_and] at hPub
  -- hPub.1.1 : tr.isCorruptAt I timeX
  obtain ⟨j, hj, hentry⟩ := hPub.1.1
  exact ⟨j, by omega, hentry⟩

/-- **Forward Secrecy via Timed Labels (Method 0)**: No `hNoLateCorrupt` needed. -/
theorem edhoc_m0_forward_secrecy_timed
    (tr : Trace) (I : String) (prk_out : Bytes)
    (x g_y : Bytes)
    (sessionTime timeX : Nat)
    (hKey : prk_out = edhocKeySchedule_m0 (Bytes.dh x g_y))
    (hTimedLabelX : timedLabelOf tr x = .principalAt I timeX)
    (hTimeX : timeX ≤ sessionTime)
    (hNetworkTimed : ∀ msg i,
      tr.entryAt i = some (.msgSent msg) →
      bytesTimedPublishable tr msg)
    (hCorruptStateTimed : ∀ prin sessId content i j,
      tr.entryAt i = some (.corrupt prin) →
      tr.entryAt j = some (.setState prin sessId content) →
      bytesTimedPublishable tr content) :
    @traceInvariant edhocInvariants tr →
    AttackerKnows tr prk_out →
    tr.isCorruptAt I sessionTime := by
  intro hInv hKnows
  have hPub := attacker_only_knows_timed_publishable hInv
    hNetworkTimed hCorruptStateTimed hKnows
  rw [hKey] at hPub
  unfold bytesTimedPublishable at hPub
  rw [timedLabelOf_edhocKeySchedule_m0] at hPub
  have hDH : timedLabelOf tr (Bytes.dh x g_y) = .principalAt I timeX := by
    show timedLabelOf tr x = .principalAt I timeX; exact hTimedLabelX
  rw [hDH] at hPub
  simp only [TimedLabel.isCorrupt, true_and] at hPub
  obtain ⟨j, hj, hentry⟩ := hPub
  exact ⟨j, by omega, hentry⟩

end CatCrypt.Crypto.Symbolic.EDHOC
