/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.SLHDSAEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.SLHDSAEmit

/-!
# WOTS+ data-dependent chains for SLH-DSA / SPHINCS+ (FIPS 205) signing, emitted
# through the verified front: the per-chain variable-length hash loop + the
# `len`-chain composition

## Scope

This module supplies the capability the SLH-DSA *signing* algorithm needs on top
of the emitted tree structure (`SLHDSAEmit.lean`, the `d`-layer hypertree +
`k`-tree FORS via the treehash theorem `treehash_loop_denote_eq`, and
`XMSSEmit.lean`'s `len` *fixed-length* WOTS public-key chains via the
single-level theorem `loop_denote_eq`): the **data-dependent WOTS+ chain**.

In WOTS+ *verification of the public key* every chain is iterated the full
`w - 1` times — that fixed-length chain is `XMSSEmit.wotsChain`, carried by
`loop_denote_eq`. In WOTS+ **signing**, by contrast, each of the
`len` chains is revealed at a position `i ∈ [0, w-1]` **derived from the message
digest + checksum** — so the per-chain hash loop has a *data-dependent* trip
count, exactly like ML-DSA's rejection loop (`RejectLoop.lean`). `SLHDSAEmit.lean`
does not cover this case; this module does.

### The proven theorems

* `wotsChainStep` — the single-leaf F-hash chain-step body (one `regArith` leaf,
  the same single-`var` shape `loop_denote_eq` / `treehash_loop_denote_eq`
  cover), as a `JForProg (.reg 64)`.
* `wotsChainAt digit` — the WOTS+ chain run to a **data-dependent** position
  `digit ∈ [0, w-1]`: the *same* chain-step body run `digit` times. This is the
  signing-side chain, distinct from `XMSSEmit.wotsChain`'s fixed `w-1`. We build
  it as `JForProgCT.withCount wotsChainStep digit` — the count-varying helper of
  `loop_denote_eq` — so the variable trip count is a first-class field, not
  an unroll.
* **`wotsChain_loop_denote_eq`** — *the WOTS theorem*, the counterpart of
  `treehash_loop_denote_eq`: running the emitted variable-count chain
  loop (`for i = 0 to digit { acc = F(acc) }`) equals `(wotsChainAt digit).denote`
  = the chain hash applied exactly `digit` times. It is an instance of the
  single-level theorem `loop_denote_eq` at the resolved count — the
  loop counterpart of `RejectLoop.lowerGuardedLoop`'s "resolve the public
  trip-count on the incoming state, then the bounded-loop lowering applies
  verbatim". The chain position is **public** (the digit is part of the
  signature, learned by any verifier), so resolving the trip count leaks
  nothing — the same CT discipline as `RejectLoop`'s public rejection guard.
* `wotsSig_denote_eq` — the **`len`-chain composition**: the WOTS+ signature is
  all `len` chains, each at its own digit position. We compose them as a *list
  of per-chain loops* (one `JForProg` per chain, with that chain's resolved
  count), exactly the `TreehashProg` *list-of-loops* idiom; its
  denotation is the per-chain `foldl`, and the emitted run equals it by the
  per-chain theorem composed `len` times — a `foldl` congruence, no new core.

### Orchestration (composed on top)

* `wotsSig` — the `len`-chain WOTS+ signature as a `List (JForProg (.reg 64))`,
  one entry per chain at its digit position. Its `denote` is the serial `foldl`.
* `slhSign` — the **whole-sign skeleton**: FORS sign (the `k`-tree FORS via the
  `SLHDSAEmit.forsTree`) ⨾ the `d`-layer hypertree WOTS
  signatures (the WOTS theorem, per layer) ⨾ threaded through the
  message-digest-derived chain positions. Sequenced at the denotation level
  (`slhSign_denote`), the FIPS-205 sign data-flow: digest → FORS root → per-layer
  WOTS signatures up the hypertree.

### The external leaf (threaded, not discharged)

* The **message digest + index derivation** (FIPS 205 `H_msg` / the `SHA2`/`SHAKE`
  hash that produces the `len` chain positions and the tree/leaf indices) is an
  **opaque ABI leaf**, threaded exactly like the FAEST whole-sign hash
  (`FAEST/Composition.lean`) and the `Th` tweakable hash
  (`JForProgTreehash.thLeafExpr`, backed by the SHAKE leaf). We
  model the chain positions abstractly as a `digits : Fin len → Fin w` function
  (the output of the digest leaf), declare the digest leaf interface, and carry
  its agreement as a hypothesis — never discharged here, all goals closed.

### Outside the scope

* **Lower-to-binary + KAT.** This module emits the chain-loop *structure* and
  proves the denotation theorem; it does **not** claim a running binary. The
  variable-count chain loop emits as the constant-size looped back-edge
  (`RejectLoop.rejectLoopLcmd` / `LprogControlFlow.loopLcmd`) at the
  public-resolved count; binding it to a concrete x86 `.s` and KATing
  against FIPS-205 / PQClean `slh-dsa` vectors is outside this module. No KAT
  vectors are fabricated here; the only concrete checks are the *structural*
  smoke tests on the emitted `.jazz` and the pure word-level ground-truth values
  the chain composition computes (`rfl`-checkable, not a hash KAT).
* The full `Th` materialises an ADRS tweak and slices nodes inside the body
  (multi-op over byte arrays); this is not modelled. The single-op leaf
  abstraction keeps the per-chain body single-`var` (covered by
  `loop_denote_eq`).

All goals closed; the only carried edges are the opaque-leaf agreements (`LeafAgrees`
for the chain leaf — vacuous for the fast `regArith` KAT leaf — and the digest
leaf interface), the same closure as the two theorems (`[propext, Quot.sound]`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.WotsChainEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgTreehash
open CatCrypt.Crypto.SecureCompilation.VIR.SLHDSAEmit

/-! ## 1. SLH-DSA WOTS+ parameters (FIPS 205-SHA2-128s shape)

The Winternitz parameter `w = 16` (`lg w = 4`) and the chain count
`len = len1 + len2 = 67` for the SHA2-128s set (`n = 16`-byte nodes:
`len1 = ⌈8n / lg w⌉ = 32`, `len2 = ⌊lg(len1·(w-1)) / lg w⌋ + 1 = 3`,
`len = 35`? — FIPS 205 Table 2 gives `len = 35` for `n=16`). We keep the
*structure* parametric over `len`; the small validating instance uses a handful
of chains so the unrolled reference stays `rfl`-checkable. The `w = 16`
Winternitz width is the real one. -/

/-- Winternitz width `w = 16` (FIPS 205's standard `w`; `lg w = 4`). Each chain
    position is a digit in `[0, w-1] = [0, 15]`. Identical to `XMSSEmit.xmssW`. -/
def wotsW : Nat := 16

/-- Max chain length `w - 1 = 15` — the fixed full chain (public-key side); the
    signing side reveals each chain at a position `≤ w - 1`. -/
def wotsChainLen : Nat := wotsW - 1

/-- WOTS+ chain count for the validating instance: a small `len` so the unrolled
    reference is `rfl`-checkable. FIPS 205-SHA2-128s uses `len = 35`; the emitted
    *structure* (a list of `len` per-chain loops) is identical for any `len`. -/
def wotsLen : Nat := 4

theorem wotsW_eq : wotsW = 16 := rfl
theorem wotsChainLen_eq : wotsChainLen = 15 := rfl

/-! ## 2. The WOTS+ chain-step body: a single-leaf loop body

The chain step is one application of the WOTS+ chain hash `F`. As in
`XMSSEmit.wotsChain` we model it with the fast deterministic single-`regArith`
leaf `acc := acc * acc` (one `regArith mul`) for the structural KAT; swapping it
for the real `F`/SHAKE leaf changes only the leaf, not the loop structure (the
leaf is the only opaque edge, carried by `LeafAgrees`). The body is single-`var`,
so `loop_denote_eq` covers it at *any* count — which is what lets the
trip count be data-dependent. -/

/-- The WOTS+ chain-step body witness: one `regArith mul` leaf
    (`acc := F(acc)`), the single-`var` shape `loop_denote_eq` covers. Shared by
    every chain and every position, so that theorem applies uniformly. -/
def chainStepExpr : Expr jasminDialect [(.reg 64)] (.reg 64) :=
  .mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))

/-- The WOTS+ chain at a **data-dependent** position `digit`: the chain-step body
    run `digit` times over a `reg 64` chain-value slot. Built via
    `JForProgCT.withCount` of the shared chain-step body, so the trip count is a
    first-class loop field (`n := digit`), *not* an unroll. This is the
    signing-side chain, distinct from `XMSSEmit.wotsChain`'s fixed `w - 1`. -/
def wotsChainAt (digit : Nat) : JForProg (.reg 64) :=
  { n := digit
    update := .var chainStepExpr (.ret .here) }

/-- The chain body is a single-leaf body (one `regArith mul`, then `.ret .here`)
    at **every** position `digit`, so the single-level theorem applies
    uniformly across data-dependent trip counts. -/
theorem wotsChainAt_singleVar (digit : Nat) :
    (wotsChainAt digit).update = SingleVarBody (accTy := .reg 64) chainStepExpr :=
  rfl

/-- The chain count is exactly the data-dependent position. -/
theorem wotsChainAt_n (digit : Nat) : (wotsChainAt digit).n = digit := rfl

/-! ## 3. The WOTS theorem: the emitted variable-count chain loop denotes the
# `digit`-fold chain (the data-dependent counterpart of `treehash_loop_denote_eq`)

The WOTS counterpart of `treehash_loop_denote_eq`. Running
the emitted `for i = 0 to digit { acc = F(acc) }` — whose trip count `digit` is
resolved from the (public) message digest — equals `(wotsChainAt digit).denote`
= the chain hash applied exactly `digit` times. It is the single-level theorem
`loop_denote_eq` at the resolved count: the loop counterpart of
`RejectLoop.lowerGuardedLoop`'s public-trip-count resolution. -/

/-- **WOTS+ data-dependent chain theorem** (`wotsChain_loop_denote_eq`): the
    emitted variable-count chain loop denotes the `digit`-fold chain. For the
    single-leaf chain-step body, running the emitted `for i = 0 to digit
    { acc = F(acc) }` from a chain start equals `(wotsChainAt digit).denote` =
    the chain hash applied exactly `digit` times — for **any** data-dependent
    position `digit ∈ [0, w-1]`. Instance of `loop_denote_eq` at the
    resolved count; the chain position is public (part of the signature), so
    resolving the trip count leaks nothing (the `RejectLoop` CT discipline). The
    only carried edge is the opaque chain leaf `LeafAgrees` (vacuous for the fast
    `regArith` KAT leaf). -/
theorem wotsChain_loop_denote_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (digit : Nat) (init : BitVec 64) :
    loopRun (wotsChainAt digit) (bodyStepRun leafSem (wotsChainAt digit)) init
      = (wotsChainAt digit).denote init :=
  loop_denote_eq hLeaf chainStepExpr (wotsChainAt digit)
    (wotsChainAt_singleVar digit) init

/-! ## 4. The `len`-chain WOTS+ signature: a list of per-chain loops (treehash idiom)

A WOTS+ signature is the `len` chains, each revealed at its own digit position.
We model the per-chain positions as `digits : Fin len → Fin w` — the output of
the message-digest leaf (§6) — and the signature as the **list of per-chain
loops** `wotsChainAt (digits i)`, exactly the `TreehashProg` list-of-loops idiom.
Its denotation is the serial `foldl` over the per-chain loops; the
emitted run equals it by the per-chain theorem composed `len` times. -/

/-- The `len`-chain WOTS+ signature as a list of per-chain loops, one
    `wotsChainAt (digits i)` per chain at its data-dependent position. The
    `TreehashProg` (= `List (JForProg)`) list-of-loops idiom. The
    positions `digits` come from the message-digest leaf (§6). -/
def wotsSig {len : Nat} (digits : Fin len → Nat) : TreehashProg (.reg 64) :=
  (List.finRange len).map (fun i => wotsChainAt (digits i))

/-- Every chain of the signature has a single-leaf body, so the level-composition
    theorem's `AllSingleVar` hypothesis holds: each entry is a `wotsChainAt`,
    and those are single-`var` at every position. -/
theorem wotsSig_allSingleVar {len : Nat} (digits : Fin len → Nat) :
    AllSingleVar (wotsSig digits) := by
  intro lvl hmem
  refine ⟨chainStepExpr, ?_⟩
  rw [wotsSig, List.mem_map] at hmem
  obtain ⟨i, _, rfl⟩ := hmem
  exact wotsChainAt_singleVar (digits i)

/-- **WOTS+ signature — the emitted `len`-chain level sequence denotes the serial
    per-chain composition.** Running the emitted WOTS+ signature (`len` chains
    back to back, each a real variable-count `for i = 0 to digit`) by composing
    the per-chain runners serially equals `(wotsSig digits).denote` = chain 0 at
    its position fed into chain 1 at its position, … Instance of the
    level-composition theorem `treehash_loop_denote_eq`; per chain this
    is the data-dependent theorem `wotsChain_loop_denote_eq`. The only edge is
    the opaque chain leaf (vacuous for the fast `regArith` KAT leaf). -/
theorem wotsSig_denote_eq {len : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (digits : Fin len → Nat) (init : BitVec 64) :
    treehashLoopRun leafSem (wotsSig digits) init
      = (wotsSig digits).denote init :=
  treehash_loop_denote_eq hLeaf (wotsSig digits) (wotsSig_allSingleVar digits) init

/-! ## 5. The whole-sign orchestration skeleton: FORS ⨾ hypertree WOTS sigs

FIPS 205 signing: the message digest selects the FORS leaves (FORS sign produces
the FORS public-key root via `SLHDSAEmit.forsTree`); the
FORS root is then signed up the `d`-layer hypertree, each layer a WOTS+ signature
(the WOTS theorem). The whole-sign denotation threads the FORS root through the
`d`-layer WOTS signatures.

We compose this at the **denotation level** — the FIPS-205 sign data-flow —
reusing `SLHDSAEmit.forsTree` for FORS and the per-layer
`wotsSig` for the hypertree. The per-layer chain positions come from the digest
leaf; we model the `d` layers' digit functions as `layerDigits : Fin d →
Fin len → Nat`. -/

/-- A `foldl` of two index-stepped functions that agree on every accumulator over
    the same list and seed coincide. (Local mirror of `JForProgCT.foldl_congr_fun`,
    which is `private`; the step here is indexed by a list element `i`.) -/
theorem foldl_congr_fun {α β : Type}
    (f g : α → β → α) (hfg : ∀ a u, f a u = g a u) :
    ∀ (l : List β) (init : α), l.foldl f init = l.foldl g init
  | [], _ => rfl
  | _ :: l, init => by
      rw [List.foldl_cons, List.foldl_cons, hfg]
      exact foldl_congr_fun f g hfg l _

/-- One hypertree-layer WOTS+ signature denotation at its layer's digit
    positions: run the `len`-chain WOTS+ signature on the incoming node. -/
def hyperLayerSign {len : Nat} (digits : Fin len → Nat) (node : BitVec 64) :
    BitVec 64 :=
  (wotsSig digits).denote node

/-- The whole SLH-DSA sign denotation skeleton: FORS sign
    (`SLHDSAEmit.forsTree`) on the message-digest seed, then the `d`-layer
    hypertree WOTS+ signatures (`wotsSig`), threading the FORS root up
    through the layers. The FIPS-205 sign data-flow: digest → FORS root →
    per-layer WOTS signatures up the hypertree. The digest/index derivation
    (the `digits`, `seed`) is the external leaf (§6), threaded not discharged. -/
def slhSign {len : Nat} (layerDigits : Fin slhD → Fin len → Nat)
    (seed : BitVec 64) : BitVec 64 :=
  (List.finRange slhD).foldl
    (fun node i => hyperLayerSign (layerDigits i) node)
    (SLHDSAEmit.forsTree.denote seed)

/-- **The whole-sign skeleton, carried by the two theorems.** Running the emitted
    FORS treehash then, for each hypertree layer, the emitted
    WOTS+ signature, threading the FORS root up, equals
    `slhSign layerDigits seed`. The FORS stage is
    `SLHDSAEmit.forsTree_treehash_denote_eq`; each layer's WOTS+ signature
    is `wotsSig_denote_eq` (this file, per layer `wotsChain_loop_denote_eq`). The
    only edge is the opaque hash leaf (vacuous for the fast `regArith` KAT
    leaf). -/
theorem slhSign_denote {len : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (layerDigits : Fin slhD → Fin len → Nat)
    (seed : BitVec 64) :
    (List.finRange slhD).foldl
        (fun node i => treehashLoopRun leafSem (wotsSig (layerDigits i)) node)
        (treehashLoopRun leafSem SLHDSAEmit.forsTree seed)
      = slhSign layerDigits seed := by
  unfold slhSign
  -- FORS root: the FORS treehash theorem.
  rw [SLHDSAEmit.forsTree_treehash_denote_eq hLeaf seed]
  -- Per-layer WOTS+ signatures: a `foldl` congruence, each layer via the WOTS
  -- signature theorem on every incoming node.
  exact foldl_congr_fun
    (fun node i => treehashLoopRun leafSem (wotsSig (layerDigits i)) node)
    (fun node i => hyperLayerSign (layerDigits i) node)
    (fun node i => wotsSig_denote_eq hLeaf (layerDigits i) node)
    (List.finRange slhD) _

/-! ## 6. The message-digest + index-derivation leaf (external, threaded)

The chain positions `digits`, the FORS leaf indices, and the tree/leaf indices
all come from FIPS 205's `H_msg` (the `SHA2`/`SHAKE` message hash) over the
message + randomizer. This is an **opaque ABI leaf**, threaded exactly like the
FAEST whole-sign hash (`FAEST/Composition.lean`) and the `Th` tweakable hash
(backed by the SHAKE leaf). We declare its interface and carry
its agreement as a hypothesis — never discharged here. -/

/-- The leaf name the front-end emits for the SLH-DSA message-digest + index
    derivation (`H_msg : (R ‖ PK ‖ M) ↦ (md ‖ idx_tree ‖ idx_leaf)`, from which
    the `len` chain digits and the tree/leaf indices are sliced). -/
def hMsgLeafName : String := "slhdsa_h_msg"

/-- The abstract message-digest spec: from a message-hash seed it produces the
    `len` chain positions for a layer (each `< w`). This is the interface the
    SLH-DSA sign proof reasons against; the SHA2/SHAKE leaf realises
    it (the digits are sliced from the digest's bits). Modeled as a function
    producing positions, the output the chain loops consume. -/
structure HMsgPrimitive (len : Nat) where
  /-- The `len` chain positions (digits in `[0, w-1]`) derived from the digest of
      a message-hash seed. -/
  digits : BitVec 64 → Fin len → Nat
  /-- Each derived position is a valid chain digit `< w`. -/
  digits_lt : ∀ (seed : BitVec 64) (i : Fin len), digits seed i < wotsW

/-- The digest leaf is the only data-source for the chain positions: the WOTS+
    signature at the leaf-derived positions is `wotsSig (prims.digits seed)`.
    This ties the (otherwise free) `digits` of §4/§5 to the opaque digest leaf —
    the leaf is threaded, its agreement carried, never discharged. -/
def wotsSigFromDigest {len : Nat} (prims : HMsgPrimitive len) (seed : BitVec 64) :
    TreehashProg (.reg 64) :=
  wotsSig (prims.digits seed)

/-- **The digest-derived WOTS+ signature is carried by the WOTS theorem.** With the
    chain positions sliced from the opaque digest leaf, the emitted WOTS+
    signature still denotes the serial per-chain composition — the digest leaf is
    threaded (it supplies `digits`), and the per-chain theorem closes the rest.
    No new core; the digest leaf's agreement is carried, not discharged. -/
theorem wotsSigFromDigest_denote_eq {len : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (prims : HMsgPrimitive len) (seed init : BitVec 64) :
    treehashLoopRun leafSem (wotsSigFromDigest prims seed) init
      = (wotsSigFromDigest prims seed).denote init :=
  wotsSig_denote_eq hLeaf (prims.digits seed) init

/-! ## 7. Concrete ground-truth values (the math definition, `rfl`-checkable)

These are **not** hash KATs (no FIPS-205 / PQClean vectors are fabricated):
they are the pure word-level values the chain composition computes with the fast
`regArith mul` leaf (squaring), closed by `rfl`. They pin the data-dependent
trip-count semantics: a chain at position `digit` squares `digit` times. -/

/-- A chain at position `0` is the identity (zero hash applications): the
    data-dependent chain at the bottom of its Winternitz interval. -/
theorem wotsChainAt_zero (init : BitVec 64) :
    (wotsChainAt 0).denote init = init := by rfl

/-- A chain at position `3` squares three times: `x ↦ x^(2^3) = x^8`. For
    `init = 2`: `2^8 = 256`. A concrete data-dependent-position value. -/
theorem wotsChainAt_three_two :
    (wotsChainAt 3).denote (2 : BitVec 64) = (256 : BitVec 64) := by rfl

/-- A chain at the **full** position `w - 1 = 15` squares fifteen times,
    matching `XMSSEmit.wotsChain` (the public-key-side fixed chain) — the
    signing-side variable chain at its top position coincides with the
    verification chain. For `init = 2`: `2^(2^15) ≡ 0 mod 2^64`. -/
theorem wotsChainAt_full_two :
    (wotsChainAt wotsChainLen).denote (2 : BitVec 64) = (0 : BitVec 64) := by rfl

/-- A concrete `len = 4` WOTS+ signature digit schedule: positions `1, 2, 3, 4`
    (one per chain). The composition squares `1 + 2 + 3 + 4 = 10` times total. -/
def sampleDigits : Fin 4 → Nat := fun i => i.val + 1

/-- The sample WOTS+ signature composes `1+2+3+4 = 10` squarings: from `1` that
    is `1^(2^10) = 1`. A concrete multi-chain composition ground truth. -/
theorem sampleSig_denote_one :
    (wotsSig sampleDigits).denote (1 : BitVec 64) = (1 : BitVec 64) := by rfl

/-- From `2` the sample signature squares `10` times: `2^(2^10) = 2^1024 ≡ 0
    mod 2^64`. The multi-chain composition exercises a `len`-fold
    threading of the data-dependent chains. -/
theorem sampleSig_denote_two :
    (wotsSig sampleDigits).denote (2 : BitVec 64) = (0 : BitVec 64) := by rfl

/-! ## 8. The emitted `.jazz`: the `len`-chain WOTS+ signature level sequence

The WOTS+ signature is the structured program `JForProg.seqToNF` of its chains, one
counted loop per chain whose trip count is the chain position, printed by the single
Jasmin printer (`JasminPrintText.emitJazzNF`). The structured program denotes the
signature (`wotsSigNF_denote`). The trip counts are the data-dependent chain
positions, resolved (public) into the loop counts. -/

/-- The structured program of the WOTS+ signature at the positions `digits`. -/
def wotsSigNF {len : Nat} (digits : Fin len → Nat) : NFProg jasminDialect [.reg 64] [.reg 64] :=
  JForProg.seqToNF (wotsSig digits) (Δ := [])

/-- The structured program of the WOTS+ signature denotes `(wotsSig digits).denote`, at
    every fuel, when every position is below `2 ^ 64`. -/
theorem wotsSigNF_denote {len : Nat} (digits : Fin len → Nat) (h : ∀ i, digits i < 2 ^ 64)
    (fuel : Nat) (a : BitVec 64) :
    (wotsSigNF digits).denote fuel (.cons a .nil) =
      some (.cons ((wotsSig digits).denote a) .nil) :=
  JForProg.seqToNF_denote (wotsSig digits)
    (by
      intro p hp
      simp only [wotsSig, List.mem_map] at hp
      obtain ⟨i, -, rfl⟩ := hp
      exact h i) fuel a .nil

/-- The text of the `export fn` of the sample `len = 4` WOTS+ signature; empty when the
    printer refuses, which the check of §9 excludes. -/
def wotsSigExportJazz : String :=
  (JasminPrintText.emitJazzNF "slhdsa_wots_sign" (JasminPrintText.JazzSig.acc (.reg 64))
    (wotsSigNF sampleDigits)).getD ""

/-! ## 9. Structural checks of the emitted `.jazz` -/

-- The WOTS+ signature text is the `export fn slhdsa_wots_sign` with `len = 4` counted
-- loops of 1, 2, 3 and 4 trips in this order, and one squaring per loop body (the
-- `1 + 2 + 3 + 4 = 10` squarings are not unrolled).
set_option kat.ms 1000 in
#kat JasminPrint.strContains wotsSigExportJazz "export fn slhdsa_wots_sign(" &&
  JasminPrint.strContains
    ((((((wotsSigExportJazz.splitOn " = 1;").getLast!).splitOn " = 2;").getLast!).splitOn
      " = 3;").getLast!) " = 4;" &&
  (wotsSigExportJazz.splitOn "while (").length == 5 &&
  (wotsSigExportJazz.splitOn " *= ").length == 5

end CatCrypt.Crypto.SecureCompilation.VIR.WotsChainEmit
