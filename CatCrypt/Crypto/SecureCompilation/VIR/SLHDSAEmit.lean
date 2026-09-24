/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.XMSSEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.XMSSEmit

/-!
# SLH-DSA / SPHINCS+ (FIPS 205) core emitted through the verified front: the
# hypertree (d composed XMSS treehashes) + FORS (k independent treehashes)

This is the **deepest hash-based signature** emitted through the committed
loop + treehash spine. There is **no new emit core**: SLH-DSA's full tree
structure is the XMSS pieces (`XMSSEmit`) and the
level-composition loop theorem (`JForProgTreehash`) *composed further*:

* **the HYPERTREE** — `d` XMSS-tree layers stacked: each layer's root signs the
  next layer up. Each layer is one XMSS Merkle treehash (the committed
  `TreehashProg`); the `d`-layer hypertree is those `d` per-layer
  treehashes composed, threading the root up. Because `TreehashProg` is a *list*
  of per-level loops and its denotation is the serial `foldl` over that list,
  the `d`-layer composition is itself a single `TreehashProg` (the `d` layers'
  levels concatenated), so the whole hypertree is covered in one application of
  `treehash_loop_denote_eq` — `loop_denote_eq` composed `d · h'` times.
* **FORS** (the few-time signature) — `k` independent Merkle treehashes over the
  message-hash indices, then a `k`-into-1 root compression. Each FORS tree is a
  `TreehashProg`; the `k` trees plus the compression are again one
  flattened `TreehashProg`, covered in one `treehash_loop_denote_eq`.

The node / leaf hash is the committed `Th` tweakable-hash leaf
(`JForProgTreehash.thLeafExpr`, backed by the committed SHAKE leaf) — the
single-op, packed `ADRS ‖ left ‖ right` leaf, the *same*
single-var-body coverage as XMSS. This file **imports and composes** the
committed kernels; it modifies none of them.

## SLH-DSA parameters validated here (small, but real-shaped)

A small instance matching FIPS 205's parameter-set *shape* (Table 1; the `f`
variants use `h' = 3`, the standard `w = 16`):

* hypertree layers `d = 2`,
* per-layer XMSS tree height `h' = 3` (`2^3 = 8` WOTS leaves, halving counts
  `4, 2, 1` — identical to `XMSSEmit`, so the per-layer treehash is *literally*
  the committed `XMSSEmit.merkleTree`),
* FORS trees `k = 3`, each of height `a = 2` (`2^2 = 4` leaves, halving counts
  `2, 1`), then a `k - 1 = 2`-step root compression.

These are small enough that the unrolled reference is checkable end-to-end, and
the structure (stacked XMSS treehashes + parallel FORS treehashes) is exactly
FIPS 205's. The `f`/`s` parameter sets only change the counts `d, h', k, a`
(and the node-byte length `n`), not the structure the spine emits.

## What the loop theorems cover, and scope

The hypertree's per-layer Merkle combine and FORS's per-tree combine are
**single-accumulator, single-leaf loop bodies** over a fixed-width word slot —
exactly the shape `loop_denote_eq` / `treehash_loop_denote_eq`
cover (`SingleVarBody` / `AllSingleVar`). So SLH-DSA's full *tree structure* —
`d` stacked XMSS treehashes for the hypertree, `k` parallel treehashes for FORS
— is carried by the two loop theorems with the single `Th` hash leaf, axiom-clean.

The scope limit of `XMSSEmit` / `JForProgTreehash` carries over unchanged: the
full `Th` materialises an `ADRS` tweak (here, per layer / per
FORS tree, the layer/tree address) and slices each node into its `left ‖ right`
halves *inside* the body (a multi-op body over byte arrays), and packs a
fixed-size node accumulator. The single-op `Th`-leaf abstraction takes the
already-packed `ADRS ‖ left ‖ right` (`JForProgTreehash.thLeafExpr`), so the
per-node ADRS plumbing / byte slicing is **outside** the single-var loop theorem.
We emit the **structural skeleton** (the `d`-layer hypertree composition + the
`k`-fold FORS, both via the committed treehash spine) and carry the proof
through the loop theorems; ADRS plumbing and node packing are outside the
proved statement.

## KAT modelling

As in `XMSSEmit`, we instantiate the hash leaf with a **fast, deterministic
word-mixing leaf** (`regArith`, a single op) so the emitted *structure* is
validated byte-for-byte end-to-end (`bench/slhdsa_compare/`): the hypertree
combine is one `reg 64` doubling (`acc := acc + acc`, the XMSS Merkle combine,
identical to `XMSSEmit`), and the FORS combine is one `reg 64` squaring
(`acc := acc * acc`, distinct from the hypertree's `add` so the KAT exercises a
two-component composition). Because SLH-DSA is ~100% hashing, swapping
this fast leaf for the real `Th` / SHAKE leaf changes only the leaf, not the
loop / treehash structure — so emit-parity is automatic (the leaf is the only
opaque edge, carried by `ThLeafAgrees`). The emitted `.jazz` is the *actual*
level sequence the loop theorems reason about.

## The carried proof

* hypertree: `JForProgTreehash.treehash_loop_denote_eq` on the
  `d`-layer-concatenated `TreehashProg` — equivalently `loop_denote_eq` (via
  `XMSSEmit.merkleTree`) composed `d · h'` times.
* FORS: `JForProgTreehash.treehash_loop_denote_eq` on the `k`-tree FORS
  `TreehashProg`.
* the hash leaf: `JForProgTreehash.ThLeafAgrees` (the single opaque-leaf edge;
  vacuous for the fast `regArith` KAT leaf).

All goals closed, axiom-clean (`[propext, Quot.sound]`, the same closure as the two
loop theorems and `XMSSEmit`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SLHDSAEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgTreehash
open CatCrypt.Crypto.SecureCompilation.VIR.XMSSEmit

/-! ## 1. SLH-DSA parameters (FIPS 205, Table 1 shape) -/

/-- Hypertree layers `d = 2` (FIPS 205's `d`; the real `f` sets use `d = 22`).
    Each layer is a full XMSS tree whose root signs the layer above. -/
def slhD : Nat := 2

/-- Per-layer XMSS tree height `h' = 3` — identical to `XMSSEmit.xmssHeight`, so
    each hypertree layer is *literally* the committed `XMSSEmit.merkleTree`
    (halving counts `4, 2, 1`). FIPS 205's `f` variants use `h' = 3`. -/
def slhHPrime : Nat := XMSSEmit.xmssHeight

/-- FORS trees `k = 3` (FIPS 205's `k`; the real `128f` set uses `k = 33`). -/
def slhForsK : Nat := 3

/-- FORS per-tree height `a = 2` (`2^2 = 4` leaves; halving counts `2, 1`). FIPS
    205's `128f` set uses `a = 6`. -/
def slhForsA : Nat := 2

/-- Sanity: the per-layer height matches XMSS's, and `h' = 3 ⇒ counts `4,2,1`. -/
theorem slhHPrime_eq : slhHPrime = 3 := rfl

/-! ## 2. The HYPERTREE: `d` XMSS treehashes stacked (`XMSSEmit` per layer)

The SLH-DSA hypertree signs `d` XMSS-tree layers: layer `0`'s root is signed by
layer `1`'s WOTS leaf, whose tree root is signed by layer `2`, … up to the
top-level root (the public key). Each layer is one XMSS Merkle treehash — the
committed `XMSSEmit.merkleTree` (`TreehashProg`, halving counts `4,2,1`).

The `d`-layer hypertree threads the root *up* through the layers: layer 0's
treehash output is the input to layer 1's treehash, etc. Because
`TreehashProg.denote` is the serial `foldl` over the level list, **stacking `d`
layers is concatenating their level lists into one `TreehashProg`** — so the
whole hypertree is one `treehash_loop_denote_eq`. -/

/-- The hypertree as a single `TreehashProg`: the `d` per-layer XMSS treehashes
    (each the committed `XMSSEmit.merkleTree`, counts `4,2,1`) **concatenated**.
    `TreehashProg.denote` folds over the whole list, so this threads layer 0's
    root into layer 1's treehash, …, up to the top root — the FIPS 205 hypertree
    composition, carried by one loop theorem application. -/
def hyperTree : TreehashProg (.reg 64) :=
  (List.range slhD).flatMap (fun _ => XMSSEmit.merkleTree)

/-- For `d = 2` the hypertree is the two XMSS layers' levels concatenated:
    `[ml 4, ml 2, ml 1, ml 4, ml 2, ml 1]` (the `4,2,1` halving repeated per
    layer). -/
theorem hyperTree_eq :
    hyperTree
      = XMSSEmit.merkleTree ++ XMSSEmit.merkleTree := by
  show (List.range 2).flatMap (fun _ => XMSSEmit.merkleTree)
       = XMSSEmit.merkleTree ++ XMSSEmit.merkleTree
  rfl

/-- Every level of the hypertree has a single-leaf body (one `regArith add` — the
    XMSS Merkle combine), so the loop theorem's `AllSingleVar` hypothesis holds: a
    hypertree level is a `merkleTree` level, and those are single-var. -/
theorem hyperTree_allSingleVar : AllSingleVar hyperTree := by
  intro lvl hmem
  refine ⟨.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)), ?_⟩
  rw [hyperTree_eq, List.mem_append] at hmem
  -- Either occurrence is a `merkleTree` level; reuse `XMSSEmit`'s witness.
  have hm : ∀ l ∈ XMSSEmit.merkleTree,
      l.update = SingleVarBody (accTy := .reg 64)
        (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) := by
    intro l hl
    obtain ⟨e, he⟩ := XMSSEmit.merkleTree_allSingleVar l hl
    -- `merkleTree`'s witness is exactly this leaf.
    rw [merkleTree_eq] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with h | h | h <;> subst h <;> rfl
  rcases hmem with h | h
  · exact hm lvl h
  · exact hm lvl h

/-- **HYPERTREE — emitted `d`-layer level sequence denotes the stacked XMSS
    treehash composition.** Running the emitted hypertree (`d` XMSS treehashes
    back to back, each a real halving `for`-sequence) by composing the per-level
    runners serially equals `hyperTree.denote` = layer 0's treehash fed into
    layer 1's, … up to the top root. Instance of the level-composition loop theorem
    `treehash_loop_denote_eq`; per-layer this is `XMSSEmit.merkleTree`.
    The only edge is the opaque hash leaf (vacuous for the fast
    `regArith` KAT leaf). -/
theorem hyperTree_treehash_denote_eq {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : BitVec 64) :
    treehashLoopRun leafSem hyperTree init = hyperTree.denote init :=
  treehash_loop_denote_eq hLeaf hyperTree hyperTree_allSingleVar init

/-- **The hypertree is the per-layer XMSS treehash composed `d`-fold.** Stacking
    `d` XMSS layers (each `XMSSEmit.merkleTree`) is, at the denotation level,
    `merkleTree.denote` applied `d` times — the FIPS 205 root-threads-up
    composition. For `d = 2`: `hyperTree.denote x = merkleTree (merkleTree x)`. -/
theorem hyperTree_denote_two_layers (x : BitVec 64) :
    hyperTree.denote x
      = XMSSEmit.merkleTree.denote (XMSSEmit.merkleTree.denote x) := by
  rw [hyperTree_eq]
  -- `(a ++ b).denote = b.denote ∘ a.denote`: foldl over append.
  simp only [TreehashProg.denote, List.foldl_append]

/-! ## 3. FORS: `k` independent treehashes + a `k`-into-1 root compression

FORS (forest of random subsets) is the SLH-DSA few-time signature: the message
hash selects one leaf in each of `k` Merkle trees of height `a`; the `k` tree
roots are then compressed into the FORS public-key root. Each FORS tree is one
Merkle treehash (`TreehashProg`, halving counts for `a = 2`: `2, 1`); the
`k`-into-1 compression is one more combine loop of trip count `k - 1`.

As with the hypertree, the `k` FORS trees plus the root compression are one
flattened `TreehashProg`, covered by a single `treehash_loop_denote_eq`. The
FORS combine leaf is one `reg 64` squaring (`acc := acc * acc`, `regArith mul`)
— distinct from the hypertree's `add` so the KAT exercises a two-part
composition. -/

/-- One FORS combine loop of trip count `cnt`: `acc := acc * acc` for `cnt`
    iterations (one `regArith mul` leaf — the FORS node hash). A single-leaf
    body, so the loop theorem applies per level. -/
def forsLevel (cnt : Nat) : JForProg (.reg 64) :=
  { n := cnt
    update :=
      .var (.mk (.regArith .mul 64) rfl
              (.cons .here (.cons .here .nil)))
        (.ret .here) }

/-- Each FORS level body is a single-leaf body (one `regArith mul`), at every
    trip count. -/
theorem forsLevel_singleVar (cnt : Nat) :
    (forsLevel cnt).update
      = SingleVarBody (accTy := .reg 64)
          (.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))) := rfl

/-- The halving trip counts for one FORS tree of height `a`: `2^(a-1), …, 2, 1`.
    For `a = 2` this is `[2, 1]` (`4 → 2 → 1`). -/
def forsCounts (a : Nat) : List Nat :=
  (List.range a).reverse.map (fun l => 2 ^ l)

/-- For `a = 2` the FORS halving counts are `[2, 1]`. -/
theorem forsCounts_two : forsCounts slhForsA = [2, 1] := by decide

/-- One FORS subtree (height `a`): the `a` per-level FORS combine loops, the
    halving counts `2, 1`. A `TreehashProg`. -/
def forsSubtree : TreehashProg (.reg 64) :=
  (forsCounts slhForsA).map forsLevel

/-- For `a = 2` a FORS subtree is `[forsLevel 2, forsLevel 1]`. -/
theorem forsSubtree_eq : forsSubtree = [forsLevel 2, forsLevel 1] := by
  simp [forsSubtree, forsCounts_two]

/-- The full FORS treehash as a single `TreehashProg`: the `k` FORS subtrees
    **concatenated**, then a final `k - 1`-step root-compression level folding
    the `k` subtree roots into the FORS public-key root. `TreehashProg.denote`
    folds over the whole list, so this runs subtree 0, then subtree 1, …, then
    compresses — the FIPS 205 FORS root, carried by one loop theorem. -/
def forsTree : TreehashProg (.reg 64) :=
  (List.range slhForsK).flatMap (fun _ => forsSubtree) ++ [forsLevel (slhForsK - 1)]

/-- For `k = 3` the FORS tree is the three subtrees' levels concatenated plus the
    2-step root compression: `[fl 2, fl 1, fl 2, fl 1, fl 2, fl 1, fl 2]`. -/
theorem forsTree_eq :
    forsTree
      = forsSubtree ++ forsSubtree ++ forsSubtree ++ [forsLevel (slhForsK - 1)] := by
  show (List.range 3).flatMap (fun _ => forsSubtree) ++ [forsLevel (slhForsK - 1)]
       = forsSubtree ++ forsSubtree ++ forsSubtree ++ [forsLevel (slhForsK - 1)]
  rfl

/-- Every level of the FORS tree has a single-leaf body (one `regArith mul`), so
    the loop theorem's `AllSingleVar` hypothesis holds. -/
theorem forsTree_allSingleVar : AllSingleVar forsTree := by
  intro lvl hmem
  refine ⟨.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil)), ?_⟩
  -- Every member is a `forsLevel cnt` (in a subtree or the compression), so its
  -- body is the single `regArith mul` leaf — uniform across all FORS levels.
  rw [forsTree] at hmem
  rw [List.mem_append] at hmem
  rcases hmem with h | h
  · -- in one of the `k` subtrees: a `forsLevel` (via `forsSubtree`'s map)
    rw [List.mem_flatMap] at h
    obtain ⟨_, _, hsub⟩ := h
    rw [forsSubtree, List.mem_map] at hsub
    obtain ⟨_, _, rfl⟩ := hsub
    rfl
  · -- the root-compression level
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; rfl

/-- **FORS — emitted `k`-tree level sequence denotes the parallel FORS treehash +
    compression.** Running the emitted FORS treehash (`k` subtrees back to back,
    then the root compression, each a real `for`) by composing the per-level
    runners serially equals `forsTree.denote` = the `k` subtree folds then the
    `k`-into-1 compression. Instance of `treehash_loop_denote_eq`. The
    only edge is the opaque hash leaf (vacuous for the fast `regArith` KAT
    leaf). -/
theorem forsTree_treehash_denote_eq {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : BitVec 64) :
    treehashLoopRun leafSem forsTree init = forsTree.denote init :=
  treehash_loop_denote_eq hLeaf forsTree forsTree_allSingleVar init

/-! ## 4. The composed SLH-DSA root: FORS root ⨾ hypertree root

In SLH-DSA the FORS public key is itself a leaf signed by the bottom hypertree
layer; the signature root threads up: the FORS root is the input to the
hypertree, which produces the top-level public-key root. The end-to-end ground
truth on a `reg 64` slot is: run the FORS treehash on the message-hash seed,
feed its root through the `d`-layer hypertree. Both stages are single-leaf
treehashes, so each is carried by `treehash_loop_denote_eq`; their composition is the structure
SLH-DSA computes. -/

/-- The composed SLH-DSA-root denotation on a `reg 64` slot: FORS treehash
    then the `d`-layer hypertree (per layer `XMSSEmit.merkleTree`). This is the
    math definition the KAT references. -/
def slhRootDenote (seed : BitVec 64) : BitVec 64 :=
  hyperTree.denote (forsTree.denote seed)

/-- **The composed SLH-DSA root, carried by the loop theorem (twice).** Running the
    emitted FORS treehash then the emitted hypertree, both via the
    evaluator-side runner, equals `slhRootDenote seed`. The FORS stage and the
    hypertree stage are each `treehash_loop_denote_eq`; the hypertree is
    additionally `XMSSEmit.merkleTree` composed `d`-fold. The only edge
    is the opaque hash leaf (vacuous for the fast `regArith` KAT leaf). -/
theorem slhRoot_emit_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (seed : BitVec 64) :
    treehashLoopRun leafSem hyperTree
        (treehashLoopRun leafSem forsTree seed)
      = slhRootDenote seed := by
  unfold slhRootDenote
  rw [forsTree_treehash_denote_eq hLeaf seed,
      hyperTree_treehash_denote_eq hLeaf (forsTree.denote seed)]

/-! ## 5. Concrete ground-truth KATs (the math definition)

The hypertree doubles `2 · (4 + 2 + 1) = 14` times (`× 2^14 = 16384`); one FORS
subtree squares `2 + 1 = 3` times, the `k = 3` subtrees square `9` times total,
then the root compression squares `k - 1 = 2` more, so FORS squares `11` times
(`x ↦ x^(2^11) = x^2048`). These reduce by `rfl` to closed `BitVec 64`
constants — the same staged composition the C reference computes. -/

/-- The hypertree of `1` doubles `14` times: `2^14 = 16384`. A concrete
    hypertree KAT. -/
theorem hyperTree_denote_one :
    hyperTree.denote (1 : BitVec 64) = (16384 : BitVec 64) := by rfl

/-- The FORS treehash of `2` squares `11` times: `2^(2^11) = 2^2048 ≡ 0 mod 2^64`
    (far more than 64 trailing zeros). A concrete FORS KAT. -/
theorem forsTree_denote_two :
    forsTree.denote (2 : BitVec 64) = (0 : BitVec 64) := by rfl

/-- The full SLH-DSA root from seed `3`: the FORS treehash (11 squarings) on `3`,
    then the `d = 2`-layer hypertree (14 doublings, `× 16384`). The closed
    `BitVec 64` value the KAT driver checks — the staged composition
    `16384 * (fors 3)`. -/
theorem slhRootDenote_three :
    slhRootDenote (3 : BitVec 64)
      = (16384 : BitVec 64) * forsTree.denote (3 : BitVec 64) := by rfl

/-! ## 6. The emitted `.jazz`: the hypertree level sequence + the FORS level
# sequence

We render two self-contained jasminc `export fn`s, each the *actual* emitted
level sequence the loop theorem covers (NOT unrolled):

* `slhdsa_hypertree` — the `d = 2`-layer hypertree (`2 ·` the `4,2,1` halving
  level sequence, each `acc = acc + acc`),
* `slhdsa_fors` — the `k = 3`-tree FORS (`3 ·` the `2,1` halving level sequence
  plus the `k - 1 = 2`-step root compression, each `acc = acc * acc`).

The composition is validated by the KAT driver (run FORS, feed into the
hypertree). -/

/-- The emitted `export fn` for the `d = 2`-layer hypertree: the two XMSS
    treehashes back to back, via `TreehashProg.toJazzExport`. -/
def hyperTreeExportJazz : String :=
  TreehashProg.toJazzExport "slhdsa_hypertree" hyperTree

/-- The emitted `export fn` for the `k = 3`-tree FORS treehash + root
    compression, via `TreehashProg.toJazzExport`. -/
def forsTreeExportJazz : String :=
  TreehashProg.toJazzExport "slhdsa_fors" forsTree

#eval IO.println hyperTreeExportJazz
#eval IO.println forsTreeExportJazz

/-! ## 7. Structural smoke tests for the emitted `.jazz` -/

/- The hypertree `.jazz` is an `export fn` jasminc unit. -/
#guard (JasminPrint.strContains hyperTreeExportJazz "export fn slhdsa_hypertree")

/- The hypertree `.jazz` has the halving level loops of *both* XMSS layers: the
    `4,2,1` halving counts appear (once per layer). -/
#guard (JasminPrint.strContains hyperTreeExportJazz "for i = 0 to 4")
    && (JasminPrint.strContains hyperTreeExportJazz "for i = 0 to 2")
    && (JasminPrint.strContains hyperTreeExportJazz "for i = 0 to 1")

/-- **Structural check: the hypertree is `d = 2` stacked XMSS treehashes** —
    exactly `6 = d · h'` level loops (`2 ·` the `4,2,1` halving sequence), each a
    real `for`, not unrolled. The combine body `acc = acc + acc` appears once per
    level: `6` times for `d · h' = 6` levels. -/
theorem hyperTreeExport_d_layers :
    (hyperTreeExportJazz.splitOn "(acc + acc)").length = 7 := by native_decide

/- The FORS `.jazz` is an `export fn` jasminc unit. -/
#guard (JasminPrint.strContains forsTreeExportJazz "export fn slhdsa_fors")

/- The FORS `.jazz` has the per-subtree halving level loops (`2, 1`) and the
    `k - 1 = 2`-step root compression loop. -/
#guard (JasminPrint.strContains forsTreeExportJazz "for i = 0 to 2")
    && (JasminPrint.strContains forsTreeExportJazz "for i = 0 to 1")

/-- **Structural check: FORS is `k = 3` subtrees plus a root compression** —
    exactly `7 = k · a + 1` level loops (`3 ·` the `2,1` halving sequence, then
    the `k - 1` compression), each a real `for`, not unrolled. The FORS combine
    body `acc = acc * acc` appears once per level: `7` times for `k · a + 1 = 7`
    levels. -/
theorem forsTreeExport_k_trees :
    (forsTreeExportJazz.splitOn "(acc * acc)").length = 8 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.SLHDSAEmit
