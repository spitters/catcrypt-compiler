/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.MLS.Invariants

/-!
# MLS Parent Hash Guarantee

The parent hash guarantee ensures that if two trees have the same root hash
and valid parent hash invariants, their structures agree on all direct paths.

## Main results

* `treeHash_injective` — trees with equal hashes have equal structure
* `treeHash_detects_leaf_change` — equal root hash implies equal leaves
* `parent_hash_guarantee` — equal root hash implies agreement on every leaf

## Symbolic hash injectivity

In the F* TreeSync proof, the parent hash guarantee requires `z3rlimit=100`
and SMT reasoning about hash collision resistance. Here `Bytes.hash` is an
injective constructor in the symbolic term algebra, so
`treeHash t₁ = treeHash t₂` implies structural equality via
`Bytes.hash.injEq`. The results in this file rest on that injectivity; the
`ParentHashValid` invariant is not among their hypotheses.

## References

* RFC 9420 Section 7.9.2 — Parent Hash Validity
* Wallez et al., USENIX Security 2023 — Parent hash guarantee (Theorem 3)
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.MLS

open CatCrypt.Crypto.Symbolic

set_option autoImplicit false

/-! ## Tree Hash Structural Injectivity -/

/-- **Tree Hash Injectivity**: Trees with equal root hashes have
structurally equal content at every level.

This is the fundamental theorem that replaces hash collision resistance
in the symbolic model. Since `Bytes.hash` is a free constructor,
`treeHash t₁ = treeHash t₂` forces structural equality at each level. -/
theorem treeHash_content_eq : ∀ {n : Nat} (t₁ t₂ : SymTree n),
    treeHash t₁ = treeHash t₂ → t₁.content = t₂.content := by
  intro n
  induction n with
  | zero =>
    intro t₁ t₂ h
    cases t₁ with | leaf c₁ =>
    cases t₂ with | leaf c₂ =>
    -- h : nodeContentHash c₁ = nodeContentHash c₂
    exact nodeContentHash_injective c₁ c₂ h
  | succ _ _ih =>
    intro t₁ t₂ h
    cases t₁ with | node c₁ l₁ r₁ =>
    cases t₂ with | node c₂ l₂ r₂ =>
    -- h : Bytes.hash (concat (nodeContentHash c₁) (concat (treeHash l₁) (treeHash r₁))) = ...
    simp only [treeHash, Bytes.hash.injEq, Bytes.concat.injEq] at h
    exact nodeContentHash_injective c₁ c₂ h.1

/-- If two trees have equal root hashes, their left subtrees have equal hashes. -/
theorem treeHash_eq_left {n : Nat} {c₁ c₂ : NodeContent} {l₁ r₁ l₂ r₂ : SymTree n}
    (h : treeHash (.node c₁ l₁ r₁) = treeHash (.node c₂ l₂ r₂)) :
    treeHash l₁ = treeHash l₂ := by
  simp only [treeHash, Bytes.hash.injEq, Bytes.concat.injEq] at h
  exact h.2.1

/-- If two trees have equal root hashes, their right subtrees have equal hashes. -/
theorem treeHash_eq_right {n : Nat} {c₁ c₂ : NodeContent} {l₁ r₁ l₂ r₂ : SymTree n}
    (h : treeHash (.node c₁ l₁ r₁) = treeHash (.node c₂ l₂ r₂)) :
    treeHash r₁ = treeHash r₂ := by
  simp only [treeHash, Bytes.hash.injEq, Bytes.concat.injEq] at h
  exact h.2.2

/-! ## Tree Hash Integrity -/

/-- **Tree Hash Integrity**: Trees with equal root hashes have equal
leaves at every position. Proved by structural injectivity alone
(no parent hash invariant needed). -/
theorem treeHash_detects_leaf_change {n : Nat} (t₁ t₂ : SymTree n)
    (idx : LeafIndex n)
    (hHash : treeHash t₁ = treeHash t₂) :
    getLeaf t₁ idx = getLeaf t₂ idx := by
  induction n with
  | zero =>
    cases t₁ with | leaf c₁ =>
    cases t₂ with | leaf c₂ =>
    -- goal: getLeaf (.leaf c₁) idx = getLeaf (.leaf c₂) idx, i.e. c₁ = c₂
    -- hHash : nodeContentHash c₁ = nodeContentHash c₂
    show c₁ = c₂
    exact nodeContentHash_injective c₁ c₂ hHash
  | succ n ih =>
    cases t₁ with | node c₁ l₁ r₁ =>
    cases t₂ with | node c₂ l₂ r₂ =>
    obtain ⟨⟨i, hi⟩⟩ := idx
    show getLeaf (.node c₁ l₁ r₁) ⟨⟨i, hi⟩⟩ = getLeaf (.node c₂ l₂ r₂) ⟨⟨i, hi⟩⟩
    rw [getLeaf.eq_2, getLeaf.eq_2]
    split
    · exact ih l₁ l₂ _ (treeHash_eq_left hHash)
    · exact ih r₁ r₂ _ (treeHash_eq_right hHash)

/-- Contrapositive form: if leaf content differs, root hash differs. -/
theorem treeHash_ne_of_leaf_ne {n : Nat} (t₁ t₂ : SymTree n) (idx : LeafIndex n)
    (hLeaf : getLeaf t₁ idx ≠ getLeaf t₂ idx) :
    treeHash t₁ ≠ treeHash t₂ :=
  fun h => absurd (treeHash_detects_leaf_change t₁ t₂ idx h) hLeaf

/-! ## Full Parent Hash Guarantee -/

/-- **Parent Hash Guarantee**: two trees with the same root hash agree
on every leaf position.

Corresponds to the Inria TreeSync parent hash guarantee
(Wallez et al., USENIX Security 2023, Theorem 3), which is stated there
under the parent hash invariant and proved from hash collision
resistance with `z3rlimit=100`.

In this symbolic model the parent hash invariant is not a hypothesis and
the parent hash mechanism does no work in the proof. `Bytes.hash` is an
injective constructor of the term algebra, so equal root hashes force
structural equality of the two trees, and the statement is
`treeHash_detects_leaf_change`. Two trees whose parent hash fields are
arbitrary satisfy the conclusion just as well. -/
theorem parent_hash_guarantee {n : Nat} (t₁ t₂ : SymTree n)
    (hHash : treeHash t₁ = treeHash t₂) :
    ∀ idx : LeafIndex n, getLeaf t₁ idx = getLeaf t₂ idx :=
  fun idx => treeHash_detects_leaf_change t₁ t₂ idx hHash

end CatCrypt.Crypto.Symbolic.MLS
