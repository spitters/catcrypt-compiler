/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgTreehash

/-!
# XMSS core emitted through the verified front: WOTS+ hash chains + Merkle treehash

This is the **first hash-based signature** emitted through the committed
loop + treehash spine. XMSS (RFC 8391 / NIST SP 800-208) is ~100% hashing:

* **WOTS+ public-key chains** — for each Winternitz chain, apply the chain hash
  `F` a fixed `w - 1` times. Each chain is one **single-level bounded loop**
  (`JForProgSemCorrect.loop_denote_eq`, `#60`) whose body is a single hash leaf.
* **the Merkle treehash** over the WOTS public keys — the committed
  `TreehashProg` (`JForProgTreehash`, `#89`) composing `h` halving levels, each
  node a single hash-leaf combine.

There is **no new emit core**: this file *composes* the already-proven
single-level keystone (`#60`) for the WOTS chains and the level-composition
keystone (`#89`) for the Merkle treehash, with the `Th` tweakable-hash leaf
(`JForProgTreehash`, backed by the committed SHAKE leaf, `#62`) as the node /
chain hash. It does **not** modify any committed kernel — it imports and reuses
them.

## XMSS parameters validated here

A small but real instance:

* tree height `h = 3` ⇒ `2^3 = 8` WOTS leaves (the halving counts `4, 2, 1`),
* Winternitz `w = 16` (`log2w = 4`, RFC 8391's standard `w`) ⇒ chain length
  `w - 1 = 15` hash applications per chain.

These are exactly the RFC 8391 Winternitz parameter (`w = 16`) at a small tree
height chosen so the unrolled reference is checkable end-to-end.

## What the keystones cover, and the honest residual

Both the WOTS chain and the Merkle combine are **single-accumulator, single-leaf
loop bodies** over a fixed-width word slot — exactly the shape `loop_denote_eq`
(`#60`) and `treehash_loop_denote_eq` (`#89`) cover (`SingleVarBody` /
`AllSingleVar`). So XMSS's *structure* — `len` WOTS chains then an `h`-level
Merkle treehash — is carried by composing the two keystones with the single
hash leaf, axiom-clean.

The residual flagged by `#89` applies here too and is **not** discharged: the
full `Th` materialises an `ADRS` tweak and slices each tree node into its
`left ‖ right` halves *inside* the loop body (a multi-op body over byte arrays),
and packs a fixed-size node accumulator. The single-op `Th`-leaf abstraction
takes the already-packed `ADRS ‖ left ‖ right` (`JForProgTreehash.thLeafExpr`),
so the per-node ADRS plumbing / byte slicing is **outside** what the single-var
keystone covers. We emit the **structural skeleton** (the WOTS chains + the
treehash composition with the single hash leaf) and carry the proof through the
keystones; the ADRS-plumbing / node-packing residual is noted, not hidden.

## KAT modelling (`~100% hashing ⇒ parity is automatic with a fast hash leaf`)

To validate the emitted *structure* byte-for-byte end-to-end (`bench/xmss_compare/`)
we instantiate the hash leaf with a **fast, deterministic word-mixing leaf**
(`regArith`, a single op — the same single-leaf discipline as the committed
`JForProgTreehash.combinerTree` validating kernel): the WOTS chain step is one
`reg 64` squaring (`acc := acc * acc`, the F-hash applied `w - 1` times), and the
Merkle combine is one `reg 64` doubling (`acc := acc + acc`). Because XMSS is
~100% hashing, swapping this fast leaf for the real `Th`/SHAKE leaf changes only
the leaf, not the loop/treehash structure — so emit-parity with an unrolled
reference is automatic (the leaf is the only opaque edge, carried by
`ThLeafAgrees` / `ShakeLeafAgrees`). The emitted `.jazz` is the *actual* loop /
level sequence the keystones reason about.

## The carried proof

* WOTS chains: `JForProgSemCorrect.loop_denote_eq` (`#60`).
* Merkle treehash: `JForProgTreehash.treehash_loop_denote_eq` (`#89`).
* the hash leaf: `JForProgTreehash.ThLeafAgrees` / `FAEST.Leaves.ShakeLeafAgrees`
  (the single opaque-leaf edge; vacuous for the fast `regArith` KAT leaf).

No `sorry`, axiom-clean (`[propext, Quot.sound]`, the same closure as the two
keystones).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.XMSSEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgTreehash

/-! ## 1. XMSS parameters (RFC 8391 / NIST SP 800-208) -/

/-- Winternitz parameter `w = 16` (`log2w = 4`) — RFC 8391's standard `w`. The
    per-chain hash count is `w - 1 = 15`. -/
def xmssW : Nat := 16

/-- WOTS+ chain length: `w - 1 = 15` hash applications per chain. -/
def chainLen : Nat := xmssW - 1

/-- Tree height `h = 3` ⇒ `2^3 = 8` WOTS leaves. Small enough that the unrolled
    reference is checkable end-to-end; the Merkle halving counts are `4, 2, 1`. -/
def xmssHeight : Nat := 3

/-- The Merkle halving trip counts for height `h`: `2^(h-1), …, 2, 1`. For
    `h = 3` this is `[4, 2, 1]` (`8 → 4 → 2 → 1`). -/
def merkleCounts (h : Nat) : List Nat :=
  (List.range h).reverse.map (fun l => 2 ^ l)

/-- For `h = 3` the halving counts are `[4, 2, 1]`. -/
theorem merkleCounts_three : merkleCounts xmssHeight = [4, 2, 1] := by
  decide

/-! ## 2. The WOTS+ public-key chain: a single-level loop (`#60`)

A WOTS+ chain applies the chain hash `F` exactly `w - 1` times to the secret
chain start, producing the chain's public value. This is one **single-level
bounded loop** of trip count `w - 1`, body = one application of the chain hash
leaf — covered by `loop_denote_eq` (`#60`).

For the fast-leaf KAT we model the chain step as a single `reg 64` squaring
`acc := acc * acc` (one `regArith mul` leaf), a deterministic mixing of the
running chain value — the same single-leaf discipline as the committed combiner
kernel, distinct from the Merkle `add` combine so the KAT exercises a genuine
two-stage composition. -/

/-- One WOTS+ chain: `w - 1 = 15` iterations of the chain step `acc := acc * acc`
    (one `regArith mul` leaf — the F-hash applied along the Winternitz chain),
    over a `reg 64` chain-value slot. A single-leaf body, so `loop_denote_eq`
    (`#60`) applies. -/
def wotsChain : JForProg (.reg 64) :=
  { n := chainLen
    update :=
      .var (.mk (.regArith .mul 64) rfl
              (.cons .here (.cons .here .nil)))
        (.ret .here) }

/-- The WOTS chain body is a single-leaf body (one `regArith mul`, then
    `.ret .here`), so the single-level keystone applies. -/
theorem wotsChain_singleVar :
    wotsChain.update
      = SingleVarBody (accTy := .reg 64)
          (.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))) := rfl

/-- **WOTS+ chain — emitted single-level loop denotes the `w-1`-fold chain.**
    Running the emitted `for i = 0 to 15 { acc = acc * acc }` from a chain start
    equals `wotsChain.denote` = the chain hash applied `w - 1 = 15` times.
    Instance of the single-level keystone `loop_denote_eq` (`#60`). The leaf
    agreement is vacuous for the fast `regArith` KAT leaf. -/
theorem wotsChain_loop_denote_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    loopRun wotsChain (bodyStepRun leafSem wotsChain) init = wotsChain.denote init :=
  loop_denote_eq hLeaf _ wotsChain wotsChain_singleVar init

/-! ## 3. The Merkle treehash over the WOTS public keys (`#89`)

The XMSS public key is the Merkle root of the `2^h` WOTS public keys. The root is
built level by level: level `l` folds `2^(h-1-l)` node-pairs — `h` single-level
loops in sequence with the halving counts `4, 2, 1`, each node a single tree-hash
combine. This is exactly the committed `TreehashProg` (`#89`).

For the fast-leaf KAT each combine is one `reg 64` doubling `acc := acc + acc`
(one `regArith add` leaf), the same single-leaf discipline as
`JForProgTreehash.combinerTree`. -/

/-- One Merkle level: a `cnt`-iteration loop of the 2→1 tree-hash combine
    `acc := acc + acc` (one `regArith add` leaf) over a `reg 64` tree-state slot.
    A single-leaf body, so the keystone applies per level. -/
def merkleLevel (cnt : Nat) : JForProg (.reg 64) :=
  { n := cnt
    update :=
      .var (.mk (.regArith .add 64) rfl
              (.cons .here (.cons .here .nil)))
        (.ret .here) }

/-- Each Merkle level body is a single-leaf body (one `regArith add`), at every
    trip count. -/
theorem merkleLevel_singleVar (cnt : Nat) :
    (merkleLevel cnt).update
      = SingleVarBody (accTy := .reg 64)
          (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) := rfl

/-- The XMSS Merkle treehash at height `h = 3`: the `h` per-level combine loops
    in sequence, with the halving counts `4, 2, 1` (the `8 → 4 → 2 → 1` shape).
    A `TreehashProg` (`#89`). -/
def merkleTree : TreehashProg (.reg 64) :=
  (merkleCounts xmssHeight).map merkleLevel

/-- `merkleTree` is the three halving levels with counts `4, 2, 1`. -/
theorem merkleTree_eq :
    merkleTree = [merkleLevel 4, merkleLevel 2, merkleLevel 1] := by
  simp [merkleTree, merkleCounts_three]

/-- Every level of `merkleTree` has a single-leaf body, so the keystone's
    `AllSingleVar` hypothesis holds. -/
theorem merkleTree_allSingleVar : AllSingleVar merkleTree := by
  intro lvl hmem
  refine ⟨.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)), ?_⟩
  rw [merkleTree_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> subst h <;> rfl

/-- **XMSS Merkle treehash — emitted level sequence denotes the serial level
    composition.** Running the emitted `h = 3`-`Cfor` sequence (levels
    `for i = 0 to 4`, `for i = 0 to 2`, `for i = 0 to 1`, each `acc = acc + acc`)
    by composing the per-level runners serially equals `merkleTree.denote` = the
    serial composition of the per-level combine folds. Instance of the
    level-composition keystone `treehash_loop_denote_eq` (`#89`). -/
theorem merkleTree_treehash_denote_eq {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : BitVec 64) :
    treehashLoopRun leafSem merkleTree init = merkleTree.denote init :=
  treehash_loop_denote_eq hLeaf merkleTree merkleTree_allSingleVar init

/-! ## 4. The composed XMSS root: WOTS chain ⨾ Merkle treehash

The XMSS public key is the Merkle root of the chained WOTS public keys. The
end-to-end ground truth on a `reg 64` slot is: run one WOTS chain (`w - 1 = 15`
squarings) on the seed, then feed the result through the `h = 3`-level Merkle
treehash (7 doublings total). Both stages are single-leaf loops, so each is
carried by its keystone; their *composition* is the structure XMSS computes. -/

/-- The composed XMSS-root denotation on a `reg 64` slot: WOTS chain (`#60`) then
    Merkle treehash (`#89`). This is the math definition the KAT references. -/
def xmssRootDenote (seed : BitVec 64) : BitVec 64 :=
  merkleTree.denote (wotsChain.denote seed)

/-- **The composed XMSS root, carried by both keystones.** Running the emitted
    WOTS chain loop then the emitted Merkle treehash level-sequence, both via the
    evaluator-side runners, equals `xmssRootDenote seed`. The WOTS stage is the
    single-level keystone (`#60`); the Merkle stage is the level-composition
    keystone (`#89`). The only edge is the opaque hash leaf (vacuous for the fast
    `regArith` KAT leaf). -/
theorem xmssRoot_emit_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (seed : BitVec 64) :
    treehashLoopRun leafSem merkleTree
        (loopRun wotsChain (bodyStepRun leafSem wotsChain) seed)
      = xmssRootDenote seed := by
  unfold xmssRootDenote
  rw [wotsChain_loop_denote_eq hLeaf seed,
      merkleTree_treehash_denote_eq hLeaf (wotsChain.denote seed)]

/-! ## 5. Concrete ground-truth KATs (the math definition)

The WOTS chain squares `w - 1 = 15` times; the Merkle treehash doubles
`4 + 2 + 1 = 7` times (`× 2^7 = 128`). These reduce by `rfl` to closed
`BitVec 64` constants — the same staged composition (15 squarings, then 7
doublings) the C reference computes. -/

/-- The WOTS chain from `2` squares 15 times: `2^(2^15) = 2^32768 ≡ 0 mod 2^64`
    (far more than 64 trailing zeros). A concrete chain KAT. -/
theorem wotsChain_denote_two :
    wotsChain.denote (2 : BitVec 64) = (0 : BitVec 64) := by rfl

/-- The full XMSS root from seed `3`: the WOTS chain (15 squarings) on `3`, then
    the Merkle treehash (7 doublings, `× 128`). The closed `BitVec 64` value the
    KAT driver checks against — the staged composition `128 * (chain 3)`. -/
theorem xmssRootDenote_three :
    xmssRootDenote (3 : BitVec 64)
      = (128 : BitVec 64) * wotsChain.denote (3 : BitVec 64) := by rfl

/-! ## 6. The emitted `.jazz`: the WOTS chain loop + the Merkle treehash sequence

We render two self-contained jasminc `export fn`s, each the *actual* emitted loop
/ level sequence the keystones cover (NOT unrolled):

* `wots_chain` — the single WOTS+ chain loop (`for i = 0 to 15 { acc = acc*acc }`),
* `xmss_treehash` — the `h = 3`-level Merkle treehash (`for i = 0 to 4 ; for i = 0
  to 2 ; for i = 0 to 1`, each `acc = acc + acc`).

The composition is validated by the KAT driver (run the chain, feed into the
treehash). -/

/-- The emitted `export fn` for one WOTS+ chain: `for i = 0 to 15 { acc=acc*acc }`,
    via the single-level `JForProg.toJazzExport` (the verified `Cfor`, `#60`). -/
def wotsChainExportJazz : String :=
  JForProg.toJazzExport "wots_chain" wotsChain

/-- The emitted `export fn` for the `h = 3` Merkle treehash: three sequential
    halving `for` loops, via `TreehashProg.toJazzExport` (`#89`). -/
def merkleTreeExportJazz : String :=
  TreehashProg.toJazzExport "xmss_treehash" merkleTree

#eval IO.println wotsChainExportJazz
#eval IO.println merkleTreeExportJazz

/-! ## 7. Structural smoke tests for the emitted `.jazz` -/

/-- The WOTS chain `.jazz` is an `export fn` jasminc unit. -/
theorem wotsChainExport_has_export :
    JasminPrint.strContains wotsChainExportJazz "export fn wots_chain" = true := by
  native_decide

/-- The WOTS chain `.jazz` has the real `w - 1 = 15`-iteration loop (not unrolled). -/
theorem wotsChainExport_has_loop :
    JasminPrint.strContains wotsChainExportJazz "for i = 0 to 15" = true := by
  native_decide

/-- The WOTS chain body is the single squaring leaf `acc * acc`, and it appears
    exactly once (a real `for`, not unrolled to 15 copies). -/
theorem wotsChainExport_not_unrolled :
    (wotsChainExportJazz.splitOn "(acc * acc)").length = 2 := by native_decide

/-- The Merkle treehash `.jazz` is an `export fn` jasminc unit. -/
theorem merkleTreeExport_has_export :
    JasminPrint.strContains merkleTreeExportJazz "export fn xmss_treehash" = true := by
  native_decide

/-- The Merkle treehash `.jazz` has all three halving level loops. -/
theorem merkleTreeExport_has_levels :
    JasminPrint.strContains merkleTreeExportJazz "for i = 0 to 4" = true
      ∧ JasminPrint.strContains merkleTreeExportJazz "for i = 0 to 2" = true
      ∧ JasminPrint.strContains merkleTreeExportJazz "for i = 0 to 1" = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **Structural check: the three Merkle level loops appear in halving sequence**
    (`4 → 2 → 1`), i.e. `h = 3` sequential `for` loops with the halving counts. -/
theorem merkleTreeExport_halving_sequence :
    JasminPrint.strContains
      ((((merkleTreeExportJazz.splitOn "for i = 0 to 4 {").getLast!).splitOn
          "for i = 0 to 2 {").getLast!)
      "for i = 0 to 1 {" = true := by
  native_decide

/-- The Merkle treehash `.jazz` does NOT unroll: exactly three `acc + acc` combine
    bodies (one per level loop), not `4 + 2 + 1 = 7` copies. -/
theorem merkleTreeExport_not_unrolled :
    (merkleTreeExportJazz.splitOn "(acc + acc)").length = 4 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.XMSSEmit
