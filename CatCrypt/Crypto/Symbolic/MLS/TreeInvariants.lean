/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.MLS.TreeTypes

/-!
# MLS TreeSync: Tree Invariants

The four tree invariants from the Inria TreeSync proof (Wallez et al.,
USENIX Security 2023), formalized as `Prop` predicates over symbolic trees.

## Main definitions

* `ValidLeaves` — every non-blank leaf has a valid credential signature
* `ParentHashValid` — parent hash links chain correctly (Merkle integrity)
* `UnmergedLeavesValid` — pending updates tracked consistently
* `AuthServiceValid` — auth service attests all group members
* `TreeSyncValid` — conjunction of all four invariants

## References

* RFC 9420 Section 7.9 — Tree invariants
* Wallez et al., USENIX Security 2023 — TreeSync: four tree invariants
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Invariant 1: Valid Leaves -/

/-- A leaf node has a valid credential. -/
def leafIsValid : NodeContent → Prop
  | .blank => True
  | .leaf cred sigKey _hpkePub =>
    ∃ (identity : Bytes),
      cred = Bytes.sign sigKey (.rand .nonce 32 0) identity ∨
      Bytes.signVerify (.vk sigKey) cred = some identity
  | .parent _ _ => True

/-- **Invariant 1: Valid Leaves** — every non-blank leaf has a valid credential. -/
def ValidLeaves : {n : Nat} → SymTree n → Prop
  | _, .leaf c => leafIsValid c
  | _, .node _ l r => ValidLeaves l ∧ ValidLeaves r

/-! ## Invariant 2: Parent Hash Validity -/

/-- A parent node's hash correctly commits to its child. -/
def parentHashLinksTo (parentNode : NodeContent) (siblingHash : Bytes) : Prop :=
  match parentNode with
  | .parent hpkePub ph => ph = parentHashOf hpkePub siblingHash
  | _ => True

/-- **Invariant 2: Parent Hash Valid** — parent hashes chain correctly. -/
def ParentHashValid : {n : Nat} → SymTree n → Prop
  | _, .leaf _ => True
  | _, .node c l r =>
    parentHashLinksTo c (treeHash r) ∧
    parentHashLinksTo c (treeHash l) ∧
    ParentHashValid l ∧ ParentHashValid r

/-! ## Invariant 3: Unmerged Leaves Valid -/

/-- Pending updates tracked consistently. -/
def UnmergedLeavesValid {n : Nat} (unmerged : List (LeafIndex n)) (tree : SymTree n) : Prop :=
  ∀ idx, idx ∈ unmerged → getLeaf tree idx ≠ .blank

/-! ## Invariant 4: Auth Service Valid -/

/-- **Invariant 4: Auth Service Valid** — auth service attests all members' credentials. -/
def AuthServiceValid {n : Nat} (tr : Trace) (members : List String) (tree : SymTree n) : Prop :=
  ∀ (idx : LeafIndex n) (cred sigKey hpkePub : Bytes),
    getLeaf tree idx = .leaf cred sigKey hpkePub →
    ∃ member, member ∈ members ∧
      hasLabel tr sigKey (principalLabel member)

/-! ## Combined Invariant -/

/-- **TreeSync Valid**: the conjunction of all four tree invariants. -/
structure TreeSyncValid {n : Nat} (tr : Trace) (gs : GroupState n)
    (unmerged : List (LeafIndex n)) : Prop where
  validLeaves : ValidLeaves gs.tree
  parentHashValid : ParentHashValid gs.tree
  unmergedValid : UnmergedLeavesValid unmerged gs.tree
  authServiceValid : AuthServiceValid tr gs.members gs.tree

/-! ## Invariant Preservation Lemmas -/

/-- Valid leaves are preserved when updating a leaf with valid content. -/
theorem ValidLeaves_setLeaf {n : Nat} (tree : SymTree n) (idx : LeafIndex n)
    (c : NodeContent) (hTree : ValidLeaves tree) (hLeaf : leafIsValid c) :
    ValidLeaves (setLeaf tree idx c) := by
  induction n with
  | zero =>
    cases tree with
    | leaf _ => exact hLeaf
  | succ n' ih =>
    cases tree with
    | node nc l r =>
      have ⟨hl, hr⟩ := hTree
      rw [setLeaf.eq_2]
      split
      · exact ⟨ih _ _ hl, hr⟩
      · exact ⟨hl, ih _ _ hr⟩

/-- A blank tree (all blank leaves) has valid leaves. -/
def blankTree : (n : Nat) → SymTree n
  | 0 => .leaf .blank
  | n + 1 => .node .blank (blankTree n) (blankTree n)

theorem ValidLeaves_blankTree : ∀ n, ValidLeaves (blankTree n)
  | 0 => trivial
  | n + 1 => ⟨ValidLeaves_blankTree n, ValidLeaves_blankTree n⟩

theorem ParentHashValid_blankTree : ∀ n, ParentHashValid (blankTree n)
  | 0 => trivial
  | n + 1 => ⟨trivial, trivial, ParentHashValid_blankTree n, ParentHashValid_blankTree n⟩

/-! ## Tree Hash Properties -/

/-- Different leaf contents produce different tree hashes. -/
theorem treeHash_leaf_injective {c₁ c₂ : NodeContent} :
    treeHash (.leaf c₁) = treeHash (.leaf c₂) → c₁ = c₂ := by
  simp [treeHash]
  exact nodeContentHash_injective c₁ c₂

/-- Different subtrees produce different tree hashes at depth n+1. -/
theorem treeHash_node_injective {n : Nat} {nc₁ nc₂ : NodeContent}
    {l₁ r₁ l₂ r₂ : SymTree n} :
    treeHash (.node nc₁ l₁ r₁) = treeHash (.node nc₂ l₂ r₂) →
    nodeContentHash nc₁ = nodeContentHash nc₂ ∧
    treeHash l₁ = treeHash l₂ ∧ treeHash r₁ = treeHash r₂ := by
  simp only [treeHash, Bytes.hash.injEq, Bytes.concat.injEq]
  exact fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

end CatCrypt.Crypto.Symbolic.MLS
