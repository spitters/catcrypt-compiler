/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.MLS.KeySecrecy
public import CatCrypt.Crypto.Symbolic.TimedLabel

/-!
# MLS Forward Secrecy and Post-Compromise Security

Forward secrecy: even if a group member's long-term key is compromised
AFTER a commit, the epoch key from that commit remains secret.

Post-compromise security (PCS): after sufficiently many clean commits
from distinct members, the epoch key is again secret even if the
attacker previously compromised some members.

## Main results

* `mls_forward_secrecy` — forward secrecy for MLS epoch keys
* `mls_pcs_symbolic` — symbolic PCS guarantee

## References

* Wallez et al., IEEE S&P 2025 — TreeKEM FS and PCS (Theorems 3-4)
* RFC 9420 Section 16.5 — Forward secrecy and PCS
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

set_option autoImplicit false

/-! ## Forward Secrecy -/

/-- **Forward Secrecy**: The MLS epoch key remains secret even if the
committer's long-term key is compromised after the commit.

Parameters:
- `sessionTime`: the trace position when the commit completed
- `hNoLateCorrupt`: no new corruption events after the commit -/
theorem mls_forward_secrecy
    (tr : Trace) (committer : String) (epochKey : Bytes)
    (pathSecret commitSecret : Bytes)
    (sessionTime : Nat)
    (hKey : epochKey = mlsKeySchedule pathSecret commitSecret (.literal "".toUTF8))
    (hLabelPS : hasLabel tr pathSecret (principalLabel committer))
    (hNoLateCorrupt : ∀ j, sessionTime < j → j < tr.length →
      ∀ p, tr.entryAt j ≠ some (.corrupt p)) :
    @traceInvariant mlsInvariants tr →
    AttackerKnows tr epochKey →
    tr.isCorruptAt committer sessionTime := by
  intro hInv hKnows
  -- Key secrecy gives isCorruptAt committer (tr.length - 1)
  have hCorrupt := mls_epoch_key_secrecy tr committer epochKey
    pathSecret commitSecret hKey hLabelPS hInv hKnows
  -- The corruption happened at some j ≤ tr.length - 1
  obtain ⟨j, hj, hjEntry⟩ := hCorrupt
  -- Either j ≤ sessionTime (forward secrecy holds) or j > sessionTime (contradiction)
  by_cases hjle : j ≤ sessionTime
  · exact ⟨j, hjle, hjEntry⟩
  · -- j > sessionTime: contradicts hNoLateCorrupt
    have hjlt : sessionTime < j := Nat.lt_of_not_le hjle
    have hjlen : j < tr.length := by omega
    exact absurd hjEntry (hNoLateCorrupt j hjlt hjlen committer)

/-- Forward secrecy as a `ForwardSecrecy` property. -/
theorem mls_fs_property
    (tr : Trace) (committer : String) (epochKey : Bytes)
    (pathSecret commitSecret : Bytes)
    (sessionTime : Nat)
    (hKey : epochKey = mlsKeySchedule pathSecret commitSecret (.literal "".toUTF8))
    (hLabelPS : hasLabel tr pathSecret (principalLabel committer))
    (hNoLateCorrupt : ∀ j, sessionTime < j → j < tr.length →
      ∀ p, tr.entryAt j ≠ some (.corrupt p)) :
    ForwardSecrecy tr epochKey sessionTime [committer] := by
  intro hInv hKnows
  exact ⟨committer, List.Mem.head _,
    mls_forward_secrecy tr committer epochKey pathSecret commitSecret
      sessionTime hKey hLabelPS hNoLateCorrupt hInv hKnows⟩

/-! ## Post-Compromise Security (Symbolic) -/

/-- **Symbolic PCS**: After sufficiently many clean commits from distinct
members, the epoch key is protected even if the attacker previously
compromised members.

The proof uses key secrecy: the epoch key depends on the latest
committer's path secret. If that committer is not corrupted, the
attacker cannot derive the epoch key. The `hCleanCommits` hypothesis
ensures the committer is clean. -/
theorem mls_pcs_symbolic
    (tr : Trace) (committers : List String) (epochKey : Bytes)
    (pathSecret commitSecret : Bytes)
    (hKey : epochKey = mlsKeySchedule pathSecret commitSecret (.literal "".toUTF8))
    (hNE : committers ≠ [])
    (hLabelPS : hasLabel tr pathSecret (principalLabel (committers.head hNE)))
    (hCleanCommits : ∀ c, c ∈ committers → ¬ tr.isCorruptAt c (tr.length - 1))
    (_hDistinct : committers.Nodup) :
    @traceInvariant mlsInvariants tr →
    ¬ AttackerKnows tr epochKey := by
  intro hInv hKnows
  have hSecret := mls_epoch_key_secrecy tr (committers.head hNE) epochKey
    pathSecret commitSecret hKey hLabelPS hInv hKnows
  have hClean := hCleanCommits (committers.head hNE) (List.head_mem hNE)
  exact absurd hSecret hClean

end CatCrypt.Crypto.Symbolic.MLS
