/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.Defs
public import CatCrypt.Crypto.Symbolic.MLS.Invariants

/-!
# MLS: the CommitVerified / Commit event correspondence

On a trace satisfying `mlsInvariants`, a `CommitVerified` event is preceded by
a matching `Commit` event unless the committer is corrupt.

## Main result

* `mls_commit_authentication` — the correspondence, read back from
  `mlsEventPred`

## Proof

1. The invariant gives `mlsEventPred` at the position of the
   `CommitVerified(R, C, groupId, epoch, rootHash)` event.
2. That clause states that a matching `Commit` event exists or the committer
   is corrupt.
3. Injectivity of `mkCommitVerifiedContent` identifies the committer.

## Scope

* The correspondence is postulated by `mlsEventPred`. No signature predicate
  enters the proof, so the statement is weaker than the TreeSync
  authentication theorem of the reference below, which derives the
  correspondence from signature unforgeability.
* `traceInvariant` for `mlsInvariants` is established only for the single
  honest trace `tr₁₀` (`honestSession_mls_invariant`).
* `processCommit` checks the committer's signature before recording
  `CommitVerified`, but it appears in no theorem and is not verified against
  the invariant.

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

/-- On a trace satisfying the invariant, a `CommitVerified` event at `i` is
preceded by a `Commit` event of the named committer with the same group,
epoch and root hash, or the committer is corrupt at `i`.

The conclusion is the clause of `mlsEventPred` for `CommitVerified` events,
which the invariant hypothesis supplies. The invariant is established only for
the honest trace `tr₁₀`, and no role program is shown to maintain it. The
statement has the shape of the TreeSync authentication guarantee
(Wallez et al., USENIX Security 2023, Theorem 1) without its derivation from
signatures. -/
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
