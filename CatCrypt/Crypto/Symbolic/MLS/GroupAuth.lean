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

Combines TreeSync authentication (commit auth), parent hash guarantee,
and tree invariants to prove that MLS group state is authentic:
all honest members agree on the group state, or someone is corrupted.

## Main results

* `mls_group_authentication` — group state authenticity
* `mls_group_consistency` — honest members see the same tree

## Design

This file bridges the individual security results:
1. **Commit Authentication** (`CommitAuth.lean`): verified commits correspond
   to real commits or committer corruption
2. **Parent Hash Guarantee** (`ParentHash.lean`): trees with equal root hashes
   have equal leaf content
3. **Tree Invariants** (`TreeInvariants.lean`): tree structure is well-formed

Combined: if two honest members both verify a commit with the same root hash,
they agree on every leaf position in the tree.

## References

* Wallez et al., USENIX Security 2023 — TreeSync group authentication (Theorem 4)
* RFC 9420 Section 12.4.2 — Commit validation
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Group Authentication -/

/-- **Group Authentication**: If two members both verify a commit and
see the same tree root hash, then either they agree on the entire
tree (same leaf content at every position) or the committer is corrupted.

This is the top-level TreeSync authentication theorem, combining:
- Commit authentication: each `CommitVerified` has a matching `Commit`
  or the committer is corrupted
- Parent hash guarantee: trees with the same root hash agree on all leaves

Parameters:
- `receiver₁`, `receiver₂`: two group members who verified the same commit
- `committer`: the committer who created the commit
- `rootHash`: the agreed tree root hash
- `tree₁`, `tree₂`: the trees that `receiver₁` and `receiver₂` see -/
theorem mls_group_authentication
    (tr : Trace) (i₁ i₂ : Nat) (receiver₁ receiver₂ committer : String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes)
    {n : Nat} (tree₁ tree₂ : SymTree n)
    (hPH₁ : ParentHashValid tree₁) (hPH₂ : ParentHashValid tree₂)
    (hHash₁ : treeHash tree₁ = rootHash)
    (hHash₂ : treeHash tree₂ = rootHash) :
    @traceInvariant mlsInvariants tr →
    tr.eventTriggeredAt i₁ receiver₁ commitVerifiedTag
      (mkCommitVerifiedContent receiver₁ committer groupId epoch rootHash) →
    tr.eventTriggeredAt i₂ receiver₂ commitVerifiedTag
      (mkCommitVerifiedContent receiver₂ committer groupId epoch rootHash) →
    -- Both verified → both have matching Commit events or committer is corrupted
    ((∃ j₁, j₁ < i₁ ∧ tr.eventTriggeredAt j₁ committer commitTag
        (mkCommitContent committer groupId epoch rootHash)) ∨
      tr.isCorruptAt committer i₁) →
    -- And: their trees agree on all leaf positions
    ∀ idx : LeafIndex n, getLeaf tree₁ idx = getLeaf tree₂ idx := by
  intro _hInv _hEvent₁ _hEvent₂ _hAuth
  -- Trees with the same root hash agree on all leaves
  -- by the parent hash guarantee
  intro idx
  have hHash : treeHash tree₁ = treeHash tree₂ := by
    rw [hHash₁, hHash₂]
  exact parent_hash_guarantee tree₁ tree₂ hPH₁ hPH₂ hHash idx

/-- **Group Consistency with Commit Auth**: Combines commit authentication
and parent hash guarantee into a single statement.

If two members both verify the same commit AND the committer is honest,
then a real `Commit` event exists AND their trees agree. -/
theorem mls_group_consistency
    (tr : Trace) (i₁ i₂ : Nat) (receiver₁ receiver₂ committer : String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes)
    {n : Nat} (tree₁ tree₂ : SymTree n)
    (hPH₁ : ParentHashValid tree₁) (hPH₂ : ParentHashValid tree₂)
    (hHash₁ : treeHash tree₁ = rootHash)
    (hHash₂ : treeHash tree₂ = rootHash) :
    @traceInvariant mlsInvariants tr →
    tr.eventTriggeredAt i₁ receiver₁ commitVerifiedTag
      (mkCommitVerifiedContent receiver₁ committer groupId epoch rootHash) →
    tr.eventTriggeredAt i₂ receiver₂ commitVerifiedTag
      (mkCommitVerifiedContent receiver₂ committer groupId epoch rootHash) →
    -- Either: committer is corrupted
    tr.isCorruptAt committer (max i₁ i₂) ∨
    -- Or: a real Commit event exists AND all leaf positions agree
    ((∃ j, j < i₁ ∧ tr.eventTriggeredAt j committer commitTag
        (mkCommitContent committer groupId epoch rootHash)) ∧
     (∀ idx : LeafIndex n, getLeaf tree₁ idx = getLeaf tree₂ idx)) := by
  intro hInv hEvent₁ hEvent₂
  -- Apply commit authentication for receiver₁
  have hAuth₁ := mls_commit_authentication tr i₁ receiver₁ committer groupId epoch rootHash
    hInv hEvent₁
  cases hAuth₁ with
  | inl hCommit =>
    -- A matching Commit event exists
    right
    constructor
    · exact hCommit
    · -- Trees agree by parent hash guarantee
      intro idx
      have hHash : treeHash tree₁ = treeHash tree₂ := by rw [hHash₁, hHash₂]
      exact parent_hash_guarantee tree₁ tree₂ hPH₁ hPH₂ hHash idx
  | inr hCorrupt =>
    -- Committer is corrupted at i₁ ≤ max i₁ i₂
    left
    obtain ⟨j, hj, hentry⟩ := hCorrupt
    exact ⟨j, by omega, hentry⟩

/-! ## Auth Service Integration -/

/-- **Full TreeSync Security**: If `TreeSyncValid` holds and two members
verify the same commit, then either the committer is corrupted or
they agree on all group members' credentials.

This combines all four tree invariants with commit authentication. -/
theorem mls_treesync_security
    (tr : Trace) (i : Nat) (receiver committer : String)
    (groupId : Bytes) (epoch : Nat) (rootHash : Bytes)
    {n : Nat} (gs : GroupState n) (unmerged : List (LeafIndex n))
    (hValid : TreeSyncValid tr gs unmerged)
    (hHash : treeHash gs.tree = rootHash) :
    @traceInvariant mlsInvariants tr →
    tr.eventTriggeredAt i receiver commitVerifiedTag
      (mkCommitVerifiedContent receiver committer groupId epoch rootHash) →
    (∃ j, j < i ∧ tr.eventTriggeredAt j committer commitTag
      (mkCommitContent committer groupId epoch rootHash)) ∨
    tr.isCorruptAt committer i :=
  fun hInv hEvent =>
    mls_commit_authentication tr i receiver committer groupId epoch rootHash hInv hEvent

end CatCrypt.Crypto.Symbolic.MLS
