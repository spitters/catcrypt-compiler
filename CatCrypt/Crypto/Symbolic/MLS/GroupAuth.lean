/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.MLS.CommitAuth
public import CatCrypt.Crypto.Symbolic.MLS.ParentHash

/-!
# MLS Group Authentication

Combines commit authentication, injectivity of the symbolic tree hash
and tree invariants: a verified commit has a matching commit event or a
corrupted committer, and two views of the group agree at every leaf when
their root hashes are equal.

## Scope

The commit-authentication part reads back the correspondence postulated by
`mlsEventPred`, and the trace invariant is established only for the single
attacker-free run `honestSession_mls_invariant`. `TreeSyncValid` is a
hypothesis of `mls_treesync_security`; no MLS operation is proved to preserve
it. The tree hash is injective because `Bytes.hash` is a free constructor, so
the parent hash mechanism plays no part.

## Main results

* `mls_group_consistency` — both receivers' commits are real, or the
  committer is corrupt
* `ValidLeaves_getLeaf` — leaf validity at every index
* `mls_treesync_security` — credential agreement and attestation under
  the TreeSync invariants

## Design

This file bridges the individual security results:
1. **Commit Authentication** (`CommitAuth.lean`): verified commits correspond
   to real commits or committer corruption
2. **Tree hash injectivity** (`ParentHash.lean`): trees with equal root hashes
   have equal leaf content
3. **Tree Invariants** (`TreeInvariants.lean`): tree structure is well-formed

Combined: two members who verify a commit each have a matching commit event
or a corrupted committer, and their trees agree on every leaf position
whenever the two root hashes are equal.

## References

* Wallez et al., USENIX Security 2023 — TreeSync group authentication (Theorem 4)
* RFC 9420 Section 12.4.2 — Commit validation
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Group Authentication -/

/-- **Group Consistency**: two members who each verify a commit for the same
group, epoch and root hash either face a corrupted committer, or both
verifications are backed by a real `Commit` event of that committer and the
two trees agree at every leaf position.

Each receiver's verification event contributes its own commit witness, ordered
before that receiver's index, and corruption is reported at `max i₁ i₂`, the
later of the two verification points. Leaf agreement comes from the two root
hashes being equal, by structural injectivity of the symbolic hash, and uses
neither verification event.

The credential-level refinement, in which agreeing leaves also carry a valid
credential attested by the auth service to a group member, is
`mls_treesync_security`. -/
theorem mls_group_consistency
    (tr : Trace) (i₁ i₂ : Nat) (receiver₁ receiver₂ committer : String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes)
    {n : Nat} (tree₁ tree₂ : SymTree n)
    (hHash₁ : treeHash tree₁ = rootHash)
    (hHash₂ : treeHash tree₂ = rootHash) :
    @traceInvariant mlsInvariants tr →
    tr.eventTriggeredAt i₁ receiver₁ commitVerifiedTag
      (mkCommitVerifiedContent receiver₁ committer groupId epoch rootHash) →
    tr.eventTriggeredAt i₂ receiver₂ commitVerifiedTag
      (mkCommitVerifiedContent receiver₂ committer groupId epoch rootHash) →
    -- Either: committer is corrupted
    tr.isCorruptAt committer (max i₁ i₂) ∨
    -- Or: both verifications have a matching Commit event AND all leaf
    -- positions agree
    (((∃ j₁, j₁ < i₁ ∧ tr.eventTriggeredAt j₁ committer commitTag
        (mkCommitContent committer groupId epoch rootHash)) ∧
      (∃ j₂, j₂ < i₂ ∧ tr.eventTriggeredAt j₂ committer commitTag
        (mkCommitContent committer groupId epoch rootHash))) ∧
     (∀ idx : LeafIndex n, getLeaf tree₁ idx = getLeaf tree₂ idx)) := by
  intro hInv hEvent₁ hEvent₂
  have hAuth₁ := mls_commit_authentication tr i₁ receiver₁ committer groupId epoch rootHash
    hInv hEvent₁
  have hAuth₂ := mls_commit_authentication tr i₂ receiver₂ committer groupId epoch rootHash
    hInv hEvent₂
  cases hAuth₁ with
  | inr hCorrupt =>
    -- Committer is corrupted at i₁ ≤ max i₁ i₂
    left
    obtain ⟨j, hj, hentry⟩ := hCorrupt
    exact ⟨j, by omega, hentry⟩
  | inl hCommit₁ =>
    cases hAuth₂ with
    | inr hCorrupt =>
      -- Committer is corrupted at i₂ ≤ max i₁ i₂
      left
      obtain ⟨j, hj, hentry⟩ := hCorrupt
      exact ⟨j, by omega, hentry⟩
    | inl hCommit₂ =>
      right
      refine ⟨⟨hCommit₁, hCommit₂⟩, ?_⟩
      -- Trees agree by injectivity of the symbolic tree hash
      intro idx
      have hHash : treeHash tree₁ = treeHash tree₂ := by rw [hHash₁, hHash₂]
      exact treeHash_detects_leaf_change tree₁ tree₂ idx hHash

/-! ## Auth Service Integration -/

/-- Every leaf of a tree satisfying `ValidLeaves` has valid content. -/
theorem ValidLeaves_getLeaf : ∀ {n : Nat} (t : SymTree n), ValidLeaves t →
    ∀ idx : LeafIndex n, leafIsValid (getLeaf t idx) := by
  intro n
  induction n with
  | zero =>
    intro t hValid idx
    cases t with | leaf c =>
    exact hValid
  | succ n' ih =>
    intro t hValid idx
    cases t with | node c l r =>
    obtain ⟨hl, hr⟩ := hValid
    obtain ⟨⟨i, hi⟩⟩ := idx
    show leafIsValid (getLeaf (.node c l r) ⟨⟨i, hi⟩⟩)
    rw [getLeaf.eq_2]
    split
    · exact ih l hl _
    · exact ih r hr _

/-- **TreeSync Security**: a receiver whose group state satisfies the
TreeSync invariants verifies a commit only if the committer is corrupted,
or a matching commit event exists and every party holding a tree with the
same root hash sees the same credential at every leaf, each credential
being valid and attested by the auth service to a group member.

`gs` is the receiver's group state and `gs'` is any other party's view
carrying the same root hash; `gs'` needs no invariant of its own, because
the agreement and the attestation transfer to it along the leafwise
equality.

The proof uses the `validLeaves` and `authServiceValid` fields of
`TreeSyncValid`. Leaf agreement comes from the two root hashes being equal,
by structural injectivity of the symbolic hash, so the `parentHashValid`
and `unmergedValid` fields are not needed for it.

Corresponds to the Inria TreeSync group authentication result
(Wallez et al., USENIX Security 2023, Theorem 4). -/
theorem mls_treesync_security
    (tr : Trace) (i : Nat) (receiver committer : String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes)
    {n : Nat} (gs gs' : GroupState n) (unmerged : List (LeafIndex n))
    (hValid : TreeSyncValid tr gs unmerged)
    (hHash : treeHash gs.tree = rootHash)
    (hHash' : treeHash gs'.tree = rootHash) :
    @traceInvariant mlsInvariants tr →
    tr.eventTriggeredAt i receiver commitVerifiedTag
      (mkCommitVerifiedContent receiver committer groupId epoch rootHash) →
    tr.isCorruptAt committer i ∨
    ((∃ j, j < i ∧ tr.eventTriggeredAt j committer commitTag
        (mkCommitContent committer groupId epoch rootHash)) ∧
      ∀ (idx : LeafIndex n) (cred sigKey hpkePub : Bytes),
        getLeaf gs.tree idx = .leaf cred sigKey hpkePub →
        getLeaf gs'.tree idx = .leaf cred sigKey hpkePub ∧
        leafIsValid (.leaf cred sigKey hpkePub) ∧
        ∃ member, member ∈ gs.members ∧
          hasLabel tr sigKey (principalLabel member)) := by
  intro hInv hEvent
  have hTrees : treeHash gs.tree = treeHash gs'.tree := by rw [hHash, hHash']
  cases mls_commit_authentication tr i receiver committer groupId epoch rootHash
      hInv hEvent with
  | inl hCommit =>
    refine Or.inr ⟨hCommit, ?_⟩
    intro idx cred sigKey hpkePub hLeaf
    refine ⟨?_, ?_, hValid.authServiceValid idx cred sigKey hpkePub hLeaf⟩
    · rw [← treeHash_detects_leaf_change gs.tree gs'.tree idx hTrees]
      exact hLeaf
    · rw [← hLeaf]
      exact ValidLeaves_getLeaf gs.tree hValid.validLeaves idx
  | inr hCorrupt => exact Or.inl hCorrupt

end CatCrypt.Crypto.Symbolic.MLS
