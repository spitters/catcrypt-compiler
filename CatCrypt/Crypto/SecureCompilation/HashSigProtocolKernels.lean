/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# Hash-based signatures as `ProtocolKernels` instantiations (axis-6, batch)

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch of
hash-based signature protocols**: WOTS+, XMSS (RFC 8391), LMS / LM-OTS
(RFC 8554), and SPHINCS+.  Every one of these is built from *iterated hash
chains* and *Merkle tree folds* — the two canonical unary `state → state`
pipelines.  They are therefore an exact fit for the unary template, just like
the Merkle authentication path (`MerkleProtocolKernels.lean`) and HKDF
(`HkdfProtocolKernels.lean`).

## Why hash-based signatures are unary `ProtocolKernels` pipelines

The single shape underlying all four protocols is the **tweakable-hash chain**:
a running node is hashed `step` times, each step parameterised by a fixed
address/tweak, so step `i` is a *unary* map `node → node` on the digest carrier.

* **WOTS+** (Winternitz one-time signature): each of the `len` secret-key
  components is walked up its hash chain by applying the chain step `w - 1`
  times — `c⁰ ↦ c¹ = F(c⁰) ↦ … ↦ c^{w-1}`.  A single chain of length `c` is a
  unary pipeline of `c` chain steps (this is exactly the repo's owned
  `"treehash_chain_" ++ toString n` per-level chain emit, with `Th` the
  tweakable-hash leaf — `X86Backend/TreehashChainEmit.lean`).
* **XMSS** (RFC 8391): a WOTS+ public key is compressed by an L-tree (a Merkle
  fold of the `len` chain tops), then the L-tree roots are folded up a Merkle
  authentication path to the XMSS root.  Both the L-tree and the auth path are
  Merkle folds — unary `node → node` steps (cf. `MerkleProtocolKernels.lean`).
* **LMS / LM-OTS** (RFC 8554): LM-OTS walks each component up its Winternitz
  chain (unary chain steps); LMS folds the per-leaf OTS public keys up a Merkle
  tree to the LMS root (unary Merkle folds).
* **SPHINCS+**: a FORS few-times signature (Merkle folds of the FORS trees'
  authentication paths) feeds a hypertree — a stack of `d` XMSS layers, each an
  XMSS auth-path fold — up to the SPHINCS+ root.  Again all unary folds.

In every case the protocol's whole hash computation is a sequence of unary
`state → state` steps — exactly the shape `ProtocolKernels` models, and exactly
the shape `pipeN` / `composeSpecs` already compose.

## What this file delivers (parametric / general-length, per the template)

Following `MerkleProtocolKernels`'s general depth-`d` form, every result here is
**parametric** in the chain length / tree height, so one theorem covers any
parameter set (WOTS+-w, XMSS-h, LMS-h, SPHINCS+-d):

* `wotsChainLeaves` / `wotsChainSpecs` and `wots_chain_realizes` — a Winternitz
  chain of arbitrary length `c` of abstract chain-step specs.
* `xmssProtocol` / `xmss_protocol_realizes` — WOTS+ chains ++ L-tree folds ++
  Merkle auth-path folds, over arbitrary lengths.
* `lmsProtocol` / `lms_protocol_realizes` — LM-OTS chains ++ LMS Merkle folds.
* `sphincsProtocol` / `sphincs_protocol_realizes` — FORS folds ++ `d` XMSS
  hypertree layers.

The per-kernel realizations are **hypotheses** (`KernelRealizes` facts) — each
is the per-step leaf-bytes KAT a real protocol cites at instantiation.  The
abstract chain/fold step specs are opaque parameters: the deliverable is
the protocol-structure composition over a *real* protocol, not re-deriving any
one tweakable hash's bytes.  No fabricated `leafSpec`; nothing protocol-specific
beyond listing each protocol's kernels and citing their realizations.

## The point (axis-6 on a batch of real protocols)

Each protocol's whole emit-realization — "the emitted per-step hash kernels
recompute the abstract chain/tree composite" — falls out of a single
`runRealizes` call on the assembled `ProtocolKernels`, with no per-protocol
proof skeleton.  The contribution is that the hash-chain / Merkle-fold structure
of an entire family of standardised signature schemes assembles for free from
the per-kernel residuals.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashSigProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  A reusable "uniform-leaf chain" realization bundle

Hash-based signatures repeatedly need the same combinator: a *chain* of `n`
copies of one emitted leaf (the same tweakable-hash kernel reused per step),
whose step specs `step 0, …, step (n-1)` are position-wise realized.  This is
the `hkdfRealized`-style induction generalised to a single shared leaf; it
underlies every chain below (WOTS+, LM-OTS, hypertree layers). -/

/-- A chain leaf list: `n` copies of one emitted leaf `leaf` (the shared
    tweakable-hash kernel reused once per chain step). -/
def chainLeaves (leaf : String) (n : Nat) : List String :=
  List.replicate n leaf

/-- A chain spec list: the per-step specs `step 0, …, step (n-1)` in chain
    order (`step i` = the `i`-th tweakable-hash application). -/
def chainSpecs (step : Nat → C → C) (n : Nat) : List (C → C) :=
  (List.range n).map (fun i => step i)

/-- **The uniform-leaf chain realization.**  If the single shared kernel `leaf`
    realizes every chain step `step i`, then `chainLeaves`/`chainSpecs` are
    position-wise realized — the `Forall₂` the template's `realized` field
    demands, for a chain of arbitrary length `n`.  Proof: induction on `n`,
    matching `List.replicate` against `(List.range n).map`. -/
theorem chainRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf : String) (step : Nat → C → C) (n : Nat)
    (hstep : ∀ i, KernelRealizes decode (step i) leaf leafSpec) :
    List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec)
      (chainLeaves leaf n) (chainSpecs step n) := by
  unfold chainLeaves chainSpecs
  induction n with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.replicate_succ']
      exact List.rel_append ih (List.Forall₂.cons (hstep m) List.Forall₂.nil)

/-- Appending two position-wise realization bundles — the `Forall₂` of a
    concatenation is the concatenation of the `Forall₂`s.  Used to glue a
    protocol's phases (chains ++ folds ++ …) into one bundle. -/
theorem appendRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    {l₁ l₂ : List String} {s₁ s₂ : List (C → C)}
    (h₁ : List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec) l₁ s₁)
    (h₂ : List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec) l₂ s₂) :
    List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec)
      (l₁ ++ l₂) (s₁ ++ s₂) :=
  List.rel_append h₁ h₂

/-! ## §1  WOTS+ — the Winternitz one-time-signature hash chain

A WOTS+ chain walks one secret-key component up its hash chain by applying the
chain step `c` times: `c⁰ ↦ F(c⁰) ↦ F²(c⁰) ↦ … ↦ Fᶜ(c⁰)`.  `chainStep i` is
the `i`-th tweakable-hash application `F`-with-address-`i`; the emitted kernel is
the single reused tweakable-hash leaf (the `"treehash_chain_"` per-step body in
`X86Backend/TreehashChainEmit.lean`).  The whole chain is a unary
`pipeN` pipeline of length `c`. -/

/-- The emitted leaf-name of the WOTS+ tweakable-hash chain step. -/
def wotsChainLeaf : String := "wotsplus_chain_f"

/-- The WOTS+ chain leaf list: `c` copies of the reused chain-step kernel. -/
def wotsChainLeaves (c : Nat) : List String := chainLeaves wotsChainLeaf c

/-- The WOTS+ chain spec list: the per-step tweakable-hash specs
    `chainStep 0, …, chainStep (c-1)`, applied in chain order. -/
def wotsChainSpecs (chainStep : Nat → C → C) (c : Nat) : List (C → C) :=
  chainSpecs chainStep c

/-- The assembled WOTS+ chain `ProtocolKernels`: `c` copies of the chain-step
    kernel, the per-step specs, the decoder, and the per-step realizations
    (assembled by `chainRealized`). -/
def wotsChainProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (chainStep : Nat → C → C) (c : Nat)
    (hstep : ∀ i, KernelRealizes decode (chainStep i) wotsChainLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := wotsChainLeaves c
  specs := wotsChainSpecs chainStep c
  decode := decode
  realized := chainRealized leafSpec decode wotsChainLeaf chainStep c hstep

/-- **The WOTS+ chain emit-realization (general chain length `c`).**  The whole
    emitted Winternitz chain — `pipeN` over `c` copies of the chain-step kernel —
    decodes to the composite `composeSpecs (wotsChainSpecs …)` of the input
    component (the `c`-fold tweakable-hash walk up the chain).  Obtained by a
    single `runRealizes` call from nothing but the per-step realizations and the
    generic composition law, for arbitrary `c`. -/
theorem wots_chain_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (chainStep : Nat → C → C) (c : Nat)
    (hstep : ∀ i, KernelRealizes decode (chainStep i) wotsChainLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (wotsChainLeaves c) oldDest xVal)
      = composeSpecs (wotsChainSpecs chainStep c) (decode xVal) :=
  (wotsChainProtocol leafSpec decode chainStep c hstep).runRealizes oldDest xVal

/-! ## §2  XMSS (RFC 8391) — WOTS+ chains ++ L-tree ++ Merkle auth path

XMSS verification recomputes the XMSS root from a WOTS+ signature in three
unary-fold phases:

1. **WOTS+ chains**: complete each component's Winternitz chain (the remaining
   `chainStep` applications) — a chain pipeline (§1).
2. **L-tree**: compress the `len` chain tops into the WOTS+ public-key node by a
   Merkle fold (`lTreeStep i` = hash the running node with L-tree sibling `i`).
3. **Merkle auth path**: fold the WOTS+ pk node up the XMSS authentication path
   to the root (`authStep i` = hash with auth-path sibling `i`).

Each phase is a list of unary `C → C` steps; the whole verification is their
concatenation — one `pipeN` pipeline. -/

/-- The emitted leaf-name of the XMSS L-tree Merkle compression step. -/
def xmssLTreeLeaf : String := "xmss_ltree_h"

/-- The emitted leaf-name of the XMSS authentication-path Merkle fold step. -/
def xmssAuthLeaf : String := "xmss_rand_hash"

/-- The XMSS verification leaf list (general parameters): the WOTS+ chain
    (`wotsLen` copies of the chain leaf) ++ the L-tree (`lLen` copies of the
    L-tree leaf) ++ the auth path (`hHeight` copies of the auth leaf). -/
def xmssLeaves (wotsLen lLen hHeight : Nat) : List String :=
  chainLeaves wotsChainLeaf wotsLen ++
    (chainLeaves xmssLTreeLeaf lLen ++
      chainLeaves xmssAuthLeaf hHeight)

/-- The XMSS verification spec list: the WOTS+ chain steps ++ the L-tree fold
    steps ++ the auth-path fold steps, in pipeline order. -/
def xmssSpecs (chainStep lTreeStep authStep : Nat → C → C)
    (wotsLen lLen hHeight : Nat) : List (C → C) :=
  chainSpecs chainStep wotsLen ++
    (chainSpecs lTreeStep lLen ++
      chainSpecs authStep hHeight)

/-- The assembled XMSS `ProtocolKernels`: the three-phase leaf list, the matching
    spec list, the decoder, and the position-wise realization bundle glued from
    the three phases' `chainRealized` bundles via `appendRealized`. -/
def xmssProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (chainStep lTreeStep authStep : Nat → C → C)
    (wotsLen lLen hHeight : Nat)
    (hChain : ∀ i, KernelRealizes decode (chainStep i) wotsChainLeaf leafSpec)
    (hLTree : ∀ i, KernelRealizes decode (lTreeStep i) xmssLTreeLeaf leafSpec)
    (hAuth : ∀ i, KernelRealizes decode (authStep i) xmssAuthLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := xmssLeaves wotsLen lLen hHeight
  specs := xmssSpecs chainStep lTreeStep authStep wotsLen lLen hHeight
  decode := decode
  realized :=
    appendRealized leafSpec decode
      (chainRealized leafSpec decode wotsChainLeaf chainStep wotsLen hChain)
      (appendRealized leafSpec decode
        (chainRealized leafSpec decode xmssLTreeLeaf lTreeStep lLen hLTree)
        (chainRealized leafSpec decode xmssAuthLeaf authStep hHeight hAuth))

/-- **The XMSS verification emit-realization (general parameters).**  The whole
    emitted XMSS pipeline — WOTS+ chains ++ L-tree folds ++ Merkle auth-path
    folds, `pipeN` over `xmssLeaves` — decodes to the composite
    `composeSpecs (xmssSpecs …)` of the input: recompute the XMSS root from the
    WOTS+ signature.  Obtained by one `runRealizes` call from the per-step
    realizations of all three phases, for arbitrary `wotsLen`, `lLen`,
    `hHeight`. -/
theorem xmss_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (chainStep lTreeStep authStep : Nat → C → C)
    (wotsLen lLen hHeight : Nat)
    (hChain : ∀ i, KernelRealizes decode (chainStep i) wotsChainLeaf leafSpec)
    (hLTree : ∀ i, KernelRealizes decode (lTreeStep i) xmssLTreeLeaf leafSpec)
    (hAuth : ∀ i, KernelRealizes decode (authStep i) xmssAuthLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (xmssLeaves wotsLen lLen hHeight) oldDest xVal)
      = composeSpecs (xmssSpecs chainStep lTreeStep authStep wotsLen lLen hHeight)
          (decode xVal) :=
  (xmssProtocol leafSpec decode chainStep lTreeStep authStep
    wotsLen lLen hHeight hChain hLTree hAuth).runRealizes oldDest xVal

/-! ## §3  LMS / LM-OTS (RFC 8554) — Winternitz chains ++ LMS Merkle tree

LMS verification recomputes the LMS root from an LM-OTS signature in two phases:

1. **LM-OTS chains**: complete each component's Winternitz chain to recover the
   LM-OTS public key (`otsStep i` = the `i`-th LM-OTS chain hash) — a chain
   pipeline.
2. **LMS Merkle path**: fold the recovered LM-OTS pk up the LMS Merkle
   authentication path to the LMS root (`lmsStep i` = hash with LMS auth-path
   sibling `i`).

Both phases are unary fold pipelines; concatenated they are the whole LMS
verification. -/

/-- The emitted leaf-name of the LM-OTS Winternitz chain step. -/
def lmOtsChainLeaf : String := "lmots_chain_h"

/-- The emitted leaf-name of the LMS Merkle authentication-path fold step. -/
def lmsTreeLeaf : String := "lms_tree_h"

/-- The LMS verification leaf list (general parameters): the LM-OTS chain
    (`otsLen` copies of the LM-OTS chain leaf) ++ the LMS Merkle path
    (`hHeight` copies of the LMS tree leaf). -/
def lmsLeaves (otsLen hHeight : Nat) : List String :=
  chainLeaves lmOtsChainLeaf otsLen ++ chainLeaves lmsTreeLeaf hHeight

/-- The LMS verification spec list: the LM-OTS chain steps ++ the LMS Merkle
    fold steps, in pipeline order. -/
def lmsSpecs (otsStep lmsStep : Nat → C → C) (otsLen hHeight : Nat) :
    List (C → C) :=
  chainSpecs otsStep otsLen ++ chainSpecs lmsStep hHeight

/-- The assembled LMS `ProtocolKernels`: the two-phase leaf list, the matching
    spec list, the decoder, and the realization bundle glued from the LM-OTS
    chain and LMS Merkle phases via `appendRealized`. -/
def lmsProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (otsStep lmsStep : Nat → C → C) (otsLen hHeight : Nat)
    (hOts : ∀ i, KernelRealizes decode (otsStep i) lmOtsChainLeaf leafSpec)
    (hLms : ∀ i, KernelRealizes decode (lmsStep i) lmsTreeLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := lmsLeaves otsLen hHeight
  specs := lmsSpecs otsStep lmsStep otsLen hHeight
  decode := decode
  realized :=
    appendRealized leafSpec decode
      (chainRealized leafSpec decode lmOtsChainLeaf otsStep otsLen hOts)
      (chainRealized leafSpec decode lmsTreeLeaf lmsStep hHeight hLms)

/-- **The LMS verification emit-realization (general parameters).**  The whole
    emitted LMS pipeline — LM-OTS Winternitz chains ++ LMS Merkle path folds,
    `pipeN` over `lmsLeaves` — decodes to the composite `composeSpecs (lmsSpecs …)`
    of the input: recompute the LMS root from the LM-OTS signature.  One
    `runRealizes` call from the per-step realizations of both phases, for
    arbitrary `otsLen`, `hHeight`. -/
theorem lms_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (otsStep lmsStep : Nat → C → C) (otsLen hHeight : Nat)
    (hOts : ∀ i, KernelRealizes decode (otsStep i) lmOtsChainLeaf leafSpec)
    (hLms : ∀ i, KernelRealizes decode (lmsStep i) lmsTreeLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (lmsLeaves otsLen hHeight) oldDest xVal)
      = composeSpecs (lmsSpecs otsStep lmsStep otsLen hHeight) (decode xVal) :=
  (lmsProtocol leafSpec decode otsStep lmsStep otsLen hHeight hOts hLms).runRealizes
    oldDest xVal

/-! ## §4  SPHINCS+ — FORS folds ++ a hypertree of XMSS layers

SPHINCS+ verification recomputes the SPHINCS+ root in two phases:

1. **FORS**: a few-times signature recovers the FORS public key by folding each
   FORS tree's authentication path up to its root and compressing the roots
   (`forsStep i` = the `i`-th FORS tweakable-hash fold) — a fold pipeline.
2. **Hypertree**: the FORS pk is then carried up a *hypertree* of `d` XMSS
   layers, each layer an XMSS authentication-path fold to the next layer's WOTS+
   leaf (`htStep i` = the `i`-th hypertree XMSS-layer fold) — another fold
   pipeline, of length `d · h` (the `d` layers' combined auth-path heights).

Both phases are unary fold pipelines over the SPHINCS+ tweakable hash; their
concatenation is the whole SPHINCS+ verification.  We keep the hypertree as a
single combined fold list of length `htLen` (`= d · h`), which is the clean
decomposition: each layer's auth path is itself a Merkle fold (§2), so the whole
hypertree is the concatenation of `d` such folds — one fold list. -/

/-- The emitted leaf-name of the SPHINCS+ FORS tweakable-hash fold step. -/
def sphincsForsLeaf : String := "sphincsplus_fors_thash"

/-- The emitted leaf-name of the SPHINCS+ hypertree XMSS-layer fold step. -/
def sphincsHtLeaf : String := "sphincsplus_ht_thash"

/-- The SPHINCS+ verification leaf list (general parameters): the FORS folds
    (`forsLen` copies of the FORS leaf) ++ the hypertree folds (`htLen` copies
    of the hypertree leaf, `htLen = d · h`). -/
def sphincsLeaves (forsLen htLen : Nat) : List String :=
  chainLeaves sphincsForsLeaf forsLen ++ chainLeaves sphincsHtLeaf htLen

/-- The SPHINCS+ verification spec list: the FORS fold steps ++ the hypertree
    fold steps, in pipeline order. -/
def sphincsSpecs (forsStep htStep : Nat → C → C) (forsLen htLen : Nat) :
    List (C → C) :=
  chainSpecs forsStep forsLen ++ chainSpecs htStep htLen

/-- The assembled SPHINCS+ `ProtocolKernels`: the two-phase leaf list, the
    matching spec list, the decoder, and the realization bundle glued from the
    FORS and hypertree phases via `appendRealized`. -/
def sphincsProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (forsStep htStep : Nat → C → C) (forsLen htLen : Nat)
    (hFors : ∀ i, KernelRealizes decode (forsStep i) sphincsForsLeaf leafSpec)
    (hHt : ∀ i, KernelRealizes decode (htStep i) sphincsHtLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := sphincsLeaves forsLen htLen
  specs := sphincsSpecs forsStep htStep forsLen htLen
  decode := decode
  realized :=
    appendRealized leafSpec decode
      (chainRealized leafSpec decode sphincsForsLeaf forsStep forsLen hFors)
      (chainRealized leafSpec decode sphincsHtLeaf htStep htLen hHt)

/-- **The SPHINCS+ verification emit-realization (general parameters).**  The
    whole emitted SPHINCS+ pipeline — FORS folds ++ hypertree XMSS-layer folds,
    `pipeN` over `sphincsLeaves` — decodes to the composite
    `composeSpecs (sphincsSpecs …)` of the input: recompute the SPHINCS+ root
    from the FORS + hypertree signature.  One `runRealizes` call from the
    per-step realizations of both phases, for arbitrary `forsLen` and
    `htLen` (`= d · h`). -/
theorem sphincs_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (forsStep htStep : Nat → C → C) (forsLen htLen : Nat)
    (hFors : ∀ i, KernelRealizes decode (forsStep i) sphincsForsLeaf leafSpec)
    (hHt : ∀ i, KernelRealizes decode (htStep i) sphincsHtLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (sphincsLeaves forsLen htLen) oldDest xVal)
      = composeSpecs (sphincsSpecs forsStep htStep forsLen htLen) (decode xVal) :=
  (sphincsProtocol leafSpec decode forsStep htStep forsLen htLen hFors hHt).runRealizes
    oldDest xVal

end CatCrypt.Crypto.SecureCompilation.HashSigProtocolKernels
