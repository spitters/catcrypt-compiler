/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Symbolic.Properties
public import CatCrypt.Crypto.Symbolic.Properties

/-!
# MLS TreeSync: Symbolic Tree Types

Symbolic binary tree data structures for MLS TreeSync (RFC 9420 Section 7).
Trees are depth-indexed complete binary trees where each node contains
symbolic `Bytes` for cryptographic material.

## Main definitions

* `NodeContent` — Content of a tree node (blank, leaf, parent)
* `SymTree n` — Depth-indexed complete binary tree
* `treeHash` — Symbolic tree hash via `Bytes.hash` (injective by construction)
* `parentHashOf` — Parent hash computation
* `GroupState` — MLS group state (members, tree, epoch, groupId)

## Design

The key advantage over F*: `Bytes.hash` is an injective constructor in the
symbolic term algebra, so collision resistance is FREE. The F* TreeSync proof
needs `z3rlimit=100` for parent hash integrity; we get it from structural
injectivity of `Bytes.hash`.

## References

* RFC 9420 Section 7 — TreeSync sub-protocol
* Wallez et al., USENIX Security 2023 — TreeSync symbolic security
* Wallez et al., IEEE S&P 2025 — TreeKEM symbolic security
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

/-! ## Tree Node Content -/

/-- Content of a TreeSync node.

In MLS, each tree node is either:
- **Blank**: an empty/removed position
- **Leaf**: contains a credential, signature key, and HPKE public key
- **Parent**: contains an HPKE public key and a parent hash

All fields are symbolic `Bytes` terms. -/
inductive NodeContent where
  /-- Empty node (removed member or unused position) -/
  | blank : NodeContent
  /-- Leaf node: member's cryptographic material -/
  | leaf : (credential sigKey hpkePub : Bytes) → NodeContent
  /-- Parent node: HPKE key for encryption + parent hash for integrity -/
  | parent : (hpkePub parentHash : Bytes) → NodeContent
  deriving Inhabited

/-! ## Symbolic Binary Trees -/

/-- Depth-indexed complete binary tree.

`SymTree n` is a complete binary tree of depth `n`:
- `SymTree 0` is a single leaf
- `SymTree (n+1)` has a node with left and right subtrees of depth `n`

This matches the RFC 9420 ratchet tree structure where leaves are at
depth `⌈log₂ n⌉` and every internal node has exactly two children. -/
inductive SymTree : Nat → Type where
  /-- Leaf node at depth 0 -/
  | leaf : NodeContent → SymTree 0
  /-- Internal node at depth n+1 with two subtrees of depth n -/
  | node : {n : Nat} → NodeContent → SymTree n → SymTree n → SymTree (n + 1)

namespace SymTree

variable {n : Nat}

/-- Get the content of a tree node. -/
def content : SymTree n → NodeContent
  | .leaf c => c
  | .node c _ _ => c

/-- Get the left subtree (only for internal nodes). -/
def left : SymTree (n + 1) → SymTree n
  | .node _ l _ => l

/-- Get the right subtree (only for internal nodes). -/
def right : SymTree (n + 1) → SymTree n
  | .node _ _ r => r

/-- Number of leaves in a tree of depth n. -/
def numLeaves (_t : SymTree n) : Nat := 2 ^ n

end SymTree

/-! ## Tree Hashing

Symbolic tree hashing uses `Bytes.hash` and `Bytes.concat` to compute
Merkle-style hashes. Since `Bytes.hash` is an injective constructor in
the term algebra, collision resistance is immediate. -/

/-- Tag for leaf hash vs parent hash (domain separation). -/
def leafHashTag : Bytes := .literal "MLS.LeafHash".toUTF8
def parentHashTag : Bytes := .literal "MLS.ParentHash".toUTF8

/-- Symbolic hash of a tree node's content.

For the symbolic model, we use `Bytes.hash` of a tagged concatenation.
This is structurally injective — two different contents have different hashes
by construction (no collision resistance needed). -/
def nodeContentHash : NodeContent → Bytes
  | .blank => Bytes.hash (.literal "blank".toUTF8)
  | .leaf cred sigKey hpkePub =>
    Bytes.hash (.concat leafHashTag (.concat cred (.concat sigKey hpkePub)))
  | .parent hpkePub ph =>
    Bytes.hash (.concat parentHashTag (.concat hpkePub ph))

/-- Symbolic hash of a complete tree.

Computes a Merkle-style hash:
- Leaf: hash of leaf content
- Internal: hash of (node content ++ left hash ++ right hash) -/
def treeHash : {n : Nat} → SymTree n → Bytes
  | _, .leaf c => nodeContentHash c
  | _, .node c l r =>
    Bytes.hash (.concat (nodeContentHash c)
      (.concat (treeHash l) (treeHash r)))

/-- Parent hash: hash of a parent node's content together with the
co-path sibling's tree hash. This creates a Merkle-style commitment
from parent to child. -/
def parentHashOf (hpkePub siblingHash : Bytes) : Bytes :=
  Bytes.hash (.concat parentHashTag (.concat hpkePub siblingHash))

/-! ## Tree Hash Injectivity

The key insight: `Bytes.hash` is injective (free constructor), so
`treeHash t₁ = treeHash t₂` implies structural equality at each level.
This replaces the SMT-heavy parent hash guarantee proof from F*. -/

/-- The leaf and parent hash tags are distinct (as ByteArrays). -/
theorem leafHashTag_bytes_ne : "MLS.LeafHash".toUTF8 ≠ "MLS.ParentHash".toUTF8 := by
  native_decide

/-- The leaf and parent hash tags are distinct. -/
theorem leafHashTag_ne_parentHashTag : leafHashTag ≠ parentHashTag := by
  simp only [leafHashTag, parentHashTag]
  exact fun h => leafHashTag_bytes_ne (Bytes.literal.inj h)

/-- The parent hash tag is distinct from the leaf hash tag. -/
theorem parentHashTag_ne_leafHashTag : parentHashTag ≠ leafHashTag :=
  Ne.symm leafHashTag_ne_parentHashTag

/-- nodeContentHash is injective. -/
theorem nodeContentHash_injective :
    ∀ c₁ c₂ : NodeContent, nodeContentHash c₁ = nodeContentHash c₂ → c₁ = c₂ := by
  intro c₁ c₂ h
  cases c₁ with
  | blank =>
    cases c₂ with
    | blank => rfl
    | leaf => simp [nodeContentHash] at h
    | parent => simp [nodeContentHash] at h
  | leaf cred₁ sig₁ hpke₁ =>
    cases c₂ with
    | blank => simp [nodeContentHash] at h
    | leaf cred₂ sig₂ hpke₂ =>
      simp only [nodeContentHash, Bytes.hash.injEq, Bytes.concat.injEq] at h
      obtain ⟨_, hcred, hsig, hhpke⟩ := h
      subst hcred; subst hsig; subst hhpke; rfl
    | parent hpke₂ ph₂ =>
      simp only [nodeContentHash, Bytes.hash.injEq, Bytes.concat.injEq] at h
      exact absurd h.1 leafHashTag_ne_parentHashTag
  | parent hpke₁ ph₁ =>
    cases c₂ with
    | blank => simp [nodeContentHash] at h
    | leaf cred₂ sig₂ hpke₂ =>
      simp only [nodeContentHash, Bytes.hash.injEq, Bytes.concat.injEq] at h
      exact absurd h.1 parentHashTag_ne_leafHashTag
    | parent hpke₂ ph₂ =>
      simp only [nodeContentHash, Bytes.hash.injEq, Bytes.concat.injEq] at h
      obtain ⟨_, hhpke, hph⟩ := h
      subst hhpke; subst hph; rfl

/-! ## Leaf and Path Indexing -/

/-- Leaf index type: a number in [0, 2^n). -/
structure LeafIndex (n : Nat) where
  val : Fin (2 ^ n)
  deriving DecidableEq

/-- Get the content of a leaf by index. -/
def getLeaf : {n : Nat} → SymTree n → LeafIndex n → NodeContent
  | 0, .leaf c, _ => c
  | n' + 1, .node _ l r, ⟨⟨i, hi⟩⟩ =>
    if h : i < 2 ^ n' then
      getLeaf l ⟨⟨i, h⟩⟩
    else
      have : i - 2 ^ n' < 2 ^ n' := by omega
      getLeaf r ⟨⟨i - 2 ^ n', this⟩⟩

/-- Set the content of a leaf by index. -/
def setLeaf : {n : Nat} → SymTree n → LeafIndex n → NodeContent → SymTree n
  | 0, .leaf _, _, c => .leaf c
  | n' + 1, .node nc l r, ⟨⟨i, hi⟩⟩, c =>
    if h : i < 2 ^ n' then
      .node nc (setLeaf l ⟨⟨i, h⟩⟩ c) r
    else
      have : i - 2 ^ n' < 2 ^ n' := by omega
      .node nc l (setLeaf r ⟨⟨i - 2 ^ n', this⟩⟩ c)

/-- Direction in a binary tree: go left or right. -/
inductive Direction where
  | left : Direction
  | right : Direction
  deriving DecidableEq

/-- Compute the direct path from a leaf to the root.

The direct path is the sequence of directions from the root to the leaf.
For leaf index `i` at depth `n`, the path is determined by the binary
representation of `i`. -/
def directPath : (n : Nat) → LeafIndex n → List Direction
  | 0, _ => []
  | n' + 1, ⟨⟨i, hi⟩⟩ =>
    if h : i < 2 ^ n' then
      .left :: directPath n' ⟨⟨i, h⟩⟩
    else
      have : i - 2 ^ n' < 2 ^ n' := by omega
      .right :: directPath n' ⟨⟨i - 2 ^ n', this⟩⟩

/-! ## Group State -/

/-- MLS Group State.

Contains the full state of an MLS group at a given epoch:
- `members`: list of member identities (principal names)
- `tree`: the ratchet tree
- `epoch`: current epoch counter
- `groupId`: unique group identifier -/
structure GroupState (n : Nat) where
  /-- List of member identities -/
  members : List String
  /-- The ratchet tree -/
  tree : SymTree n
  /-- Current epoch number -/
  epoch : Nat
  /-- Unique group identifier -/
  groupId : Bytes

/-! ## TreeKEM Key Schedule (Symbolic)

The symbolic key schedule for TreeKEM uses `kdfExpand` to derive
node secrets from a path secret, following RFC 9420 Section 7.4. -/

/-- Derive a node secret from a path secret and node index.

In the real protocol, this is `DeriveTreeSecret(path_secret, "node", index, 32)`.
In the symbolic model, we use `kdfExpand` with a domain-separated info string. -/
def treeKDF (pathSecret : Bytes) (nodeIndex : Nat) : Bytes :=
  Bytes.kdfExpand pathSecret
    (.concat (.literal "MLS.TreeKEM.node".toUTF8)
      (.literal (toString nodeIndex).toUTF8)) 32

/-- Derive the HPKE key pair for a tree node.

Takes a node secret and derives the HPKE secret key. The public key
is `Bytes.kemPub` of the secret key. -/
def deriveHPKEKey (nodeSecret : Bytes) : Bytes :=
  Bytes.kdfExpand nodeSecret (.literal "MLS.TreeKEM.hpke".toUTF8) 32

/-- Derive the next path secret (for the parent node).

Takes the current path secret and derives the path secret for the
next level up in the tree. -/
def derivePathSecret (pathSecret : Bytes) : Bytes :=
  Bytes.kdfExpand pathSecret (.literal "MLS.TreeKEM.path".toUTF8) 32

/-- Full TreeKEM key schedule: derive all node secrets along a path.

Given an initial `pathSecret` at a leaf, derives secrets for each node
on the direct path to the root. Returns a list of `pathLen` node secrets. -/
def treeKeySchedule (pathSecret : Bytes) : Nat → List Bytes
  | 0 => []
  | n + 1 =>
    let nodeSecret := treeKDF pathSecret n
    let nextPathSecret := derivePathSecret pathSecret
    nodeSecret :: treeKeySchedule nextPathSecret n

/-- Derive the epoch secret from the final path secret and group context. -/
def deriveEpochSecret (pathSecret groupContext : Bytes) : Bytes :=
  Bytes.kdfExtract groupContext pathSecret

end CatCrypt.Crypto.Symbolic.MLS
