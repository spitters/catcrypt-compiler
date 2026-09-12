/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.Defs
public import CatCrypt.Crypto.Symbolic.MLS.Invariants

/-!
# MLS Commit Authentication

Theorem: If a receiver verifies a commit (triggers `CommitVerified`),
then either the committer actually sent the commit (triggered `Commit`),
or the committer is compromised.

## Main result

* `mls_commit_authentication` — commit authentication via event correspondence

## Proof Sketch

1. Receiver triggers `CommitVerified(R, C, groupId, epoch, rootHash)` at position `i`
2. By `mlsEventPred`, the receiver verified the committer's commit
3. By the event predicate, either a matching `Commit` event exists,
   or the committer is corrupted
4. Injectivity of `mkCommitVerifiedContent` extracts the committer identity

This is the core **TreeSync authentication theorem** adapted to DY-lite.
It corresponds to the Inria `treesync_authentication` theorem.

## References

* Wallez et al., USENIX Security 2023 — TreeSync authentication (Theorem 1)
* RFC 9420 Section 12.4 — Commit verification
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-- `String.toUTF8` is injective (local copy for this file). -/
theorem String.toUTF8_injective' : Function.Injective String.toUTF8 := by
  intro ⟨b1, h1⟩ ⟨b2, h2⟩ (h : b1 = b2)
  cases h; rfl

/-- **Commit Authentication**: If a receiver verifies a commit
(triggers `CommitVerified`), then the committer also created the commit
(triggered `Commit` with a matching root hash), or the committer is
compromised.

This is the MLS analogue of EDHOC responder authentication. It ensures
that TreeSync group state updates are authentic — a verified commit
corresponds to a real commit or requires committer corruption.

Corresponds to the Inria TreeSync "authentication guarantee"
(Wallez et al., USENIX Security 2023, Theorem 1). -/
theorem mls_commit_authentication
    (tr : Trace) (i : Nat) (receiver committer : String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) :
    @traceInvariant mlsInvariants tr →
    tr.eventTriggeredAt i receiver commitVerifiedTag
      (mkCommitVerifiedContent receiver committer groupId epoch rootHash) →
    (∃ j, j < i ∧ tr.eventTriggeredAt j committer commitTag
      (mkCommitContent committer groupId epoch rootHash)) ∨
    tr.isCorruptAt committer i := by
  intro hInv hEvent
  have hi := Trace.entryAt_lt_length hEvent
  have hPred := hInv i hi _ hEvent
  change mlsEventPred tr i receiver commitVerifiedTag
    (mkCommitVerifiedContent receiver committer groupId epoch rootHash) at hPred
  unfold mlsEventPred at hPred
  simp only [beq_self_eq_true, ↓reduceIte] at hPred
  obtain ⟨committer', groupId', epoch', rootHash', hcontent, hauth⟩ := hPred
  -- Extract field equalities via structural injectivity of Bytes.concat
  simp only [mkCommitVerifiedContent, Bytes.concat.injEq, Bytes.literal.injEq] at hcontent
  -- hcontent: receiver = receiver ∧ committer = committer' ∧ groupId = groupId' ∧ epoch_bytes ∧ rootHash = rootHash'
  obtain ⟨_hrcv, hcomm, hgid, hep, hrh⟩ := hcontent
  -- Rewrite all primed variables in hauth to match goal
  rw [String.toUTF8_injective' hcomm.symm, hgid.symm, hrh.symm] at hauth
  -- Epoch matches at the Bytes level: rewrite commit content in hauth
  rw [show mkCommitContent committer groupId epoch' rootHash =
        mkCommitContent committer groupId epoch rootHash from by
      unfold mkCommitContent; rw [← hep]] at hauth
  exact hauth

/-- **Commit Authentication (alternative form)**: Using the `Authentication`
type from `Properties.lean`. -/
theorem mls_commit_auth_property
    (tr : Trace) (i : Nat) (receiver committer : String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes) :
    Authentication tr i receiver committer
      commitVerifiedTag commitTag
      (mkCommitVerifiedContent receiver committer groupId epoch rootHash)
      (mkCommitContent committer groupId epoch rootHash) := by
  intro hInv hEvent
  have h := mls_commit_authentication tr i receiver committer groupId epoch rootHash hInv hEvent
  exact h.elim (fun ⟨j, hj, he⟩ => .inl ⟨j, hj, he⟩) (fun hc => .inr (.inr hc))

end CatCrypt.Crypto.Symbolic.MLS
