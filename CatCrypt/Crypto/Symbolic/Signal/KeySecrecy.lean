/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Signal.Invariants

/-!
# Signal X3DH Key Secrecy

Theorem: The X3DH root key is secret unless the initiator (who controls
the ephemeral key) is corrupted.

## Main result

* `signal_x3dh_key_secrecy` — root key secrecy

## Proof

The root key is `signalKeySchedule(dh1, dh2, dh3, dh4)` where all 4 DH
computations use Alice's ephemeral key `ek` (labeled `principalLabel alice`).
The label chain is:
1. `labelOf(dh_i) = labelOf(ek) = principalLabel alice` (for dh2, dh3, dh4)
   or `labelOf(ikA) = principalLabel alice` (for dh1)
2. `kdfExtract` meet preserves the label
3. `isCorrupt` → `corruptSet alice`

## References

* DY* Signal: key secrecy (Bhargavan et al.)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Signal

open CatCrypt.Crypto.Symbolic

/-- The label of the Signal key schedule output depends on the labels of the
4 DH shared secrets. Since kdfExtract uses meet, and concat uses meet,
the result label is the meet of all 4 DH labels. -/
theorem labelOf_signalKeySchedule (tr : Trace) (dh1 dh2 dh3 dh4 : Bytes) :
    labelOf tr (signalKeySchedule dh1 dh2 dh3 dh4) =
    .meet .top
      (.meet (.meet (labelOf tr dh1) (labelOf tr dh2))
             (.meet (labelOf tr dh3) (labelOf tr dh4))) := by
  unfold signalKeySchedule Bytes.zeros
  rfl

/-- **Key Secrecy**: The Signal X3DH root key is secret unless Alice
(the initiator who generates the ephemeral key `ek`) is corrupted. -/
theorem signal_x3dh_key_secrecy
    (tr : Trace) (alice : String) (rootKey : Bytes)
    (ek ikA : Bytes) (ikB spkB opkB : Bytes)
    (hKey : rootKey = signalKeySchedule
      (Bytes.dh ikA (Bytes.dhPub spkB))
      (Bytes.dh ek (Bytes.dhPub ikB))
      (Bytes.dh ek (Bytes.dhPub spkB))
      (Bytes.dh ek (Bytes.dhPub opkB)))
    (hLabelEK : hasLabel tr ek (principalLabel alice))
    (hLabelIKA : hasLabel tr ikA (principalLabel alice)) :
    @traceInvariant signalInvariants tr →
    AttackerKnows tr rootKey →
    tr.isCorruptAt alice (tr.length - 1) := by
  intro hInv hKnows
  have hPub := attacker_only_knows_publishable hInv hKnows
  rw [hKey] at hPub
  unfold bytesPublishable at hPub
  rw [labelOf_signalKeySchedule] at hPub
  -- labelOf(dh(ek, dhPub(ikB))) = labelOf(ek) = principalLabel alice
  -- similarly for dh3, dh4; dh1 uses ikA which also has principalLabel alice
  have hDH1 : labelOf tr (Bytes.dh ikA (Bytes.dhPub spkB)) = principalLabel alice := hLabelIKA
  have hDH2 : labelOf tr (Bytes.dh ek (Bytes.dhPub ikB)) = principalLabel alice := hLabelEK
  have hDH3 : labelOf tr (Bytes.dh ek (Bytes.dhPub spkB)) = principalLabel alice := hLabelEK
  have hDH4 : labelOf tr (Bytes.dh ek (Bytes.dhPub opkB)) = principalLabel alice := hLabelEK
  rw [hDH1, hDH2, hDH3, hDH4] at hPub
  simp only [Label.isCorrupt, principalLabel, true_and, and_self] at hPub
  obtain ⟨i, hi, hentry⟩ := hPub
  exact ⟨i, by omega, hentry⟩

end CatCrypt.Crypto.Symbolic.Signal
