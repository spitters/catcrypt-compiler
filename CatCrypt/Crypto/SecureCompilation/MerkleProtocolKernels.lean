/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# A Merkle authentication path as a `ProtocolKernels` instantiation (axis-6)

`ProtocolEmitRealizes` factors the per-protocol emit-realization skeleton into a
single composition law (`pipeN_realizes`) and a bundling structure
(`ProtocolKernels` + `ProtocolKernels.runRealizes`).  `ProtocolKernelsDemo`
exercises that template on a deliberately trivial carrier.  This file is the
**second** instantiation — on a *real* hash-chain protocol: verifying a Merkle
**authentication path** (the membership proof used in SPHINCS+, XMSS, and
certificate transparency).

## Why a Merkle path is a unary `ProtocolKernels` pipeline

Verifying a depth-`d` Merkle authentication path recomputes the root from a leaf
digest by folding, at each level, the running node with the next sibling on the
path:

```text
node₀ = leaf
node₁ = H(combine(node₀, sibling₁))     -- level-1 fold
node₂ = H(combine(node₁, sibling₂))     -- level-2 fold
…
root  = node_d = H(combine(node_{d-1}, sibling_d))
```

Each sibling `siblingᵢ` is a **fixed parameter** of level `i` (it is part of the
authentication path being checked), so level `i`'s fold is a *unary* map
`node → node` on the digest carrier.  The whole verification is therefore a
unary pipeline `node₀ ↦ node₁ ↦ … ↦ root` — exactly the shape the unary
`ProtocolKernels` models.  This mirrors the repo's real treehash combiner
(`SecureCompilation/VIR/JForProgTreehash.lean`'s 2→1 `combinerTree`) and the
owned per-level chain emit (`X86Backend/TreehashChainOwnedEmit.lean`'s
`"treehash_chain_" ++ toString n`): per level, one hash of the running node with
that level's sibling.

## What this file builds

* a carrier `C` (the digest type) and `d` abstract per-level fold specs
  `fold₁, …, fold_d : C → C` (`foldᵢ` = "hash the running node with sibling `i`")
  — the specs are abstract because the *point* is the chain composition over a
  real protocol structure, not the bytes of any one hash;
* per-level realizations as **hypotheses** `hᵢ : KernelRealizes decode foldᵢ
  leafᵢ leafSpec` — exactly how a real protocol cites its emitted kernels: each
  is the per-level leaf-bytes KAT, supplied at instantiation;
* a concrete depth-3 assembly `merkleProtocol3` and its whole-path realization
  `merkle_path_realizes3` via one `runRealizes` call;
* a **general depth-`d`** assembly `merkleProtocol` directly over a `List` of
  `(leaf, fold, realization)`, and its `merkle_path_realizes` — the whole
  authentication-path emit-realization for arbitrary depth, assembled purely
  from the per-level realizations and the generic composition law.

## The point (axis-6) on a real protocol

Per-protocol emit for a Merkle authentication path is *exactly* this
instantiation: list the path's per-level hash kernels, cite each level's
realization (its leaf-bytes KAT), and apply the template.  The whole-path
emit-realization — "the emitted per-level kernels recompute the abstract folded
root" — falls out of `runRealizes` with no new per-protocol proof skeleton.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MerkleProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-! ## §1  A concrete depth-3 Merkle authentication path

Three per-level fold specs over an abstract digest carrier `C`.  `foldᵢ` folds
the running node with sibling `i` (a fixed parameter of level `i`); applied in
pipeline order the composite recomputes the root from the leaf digest. -/

variable {C : Type*}

/-- The depth-3 path's per-level leaf-names, in pipeline order.  Modeled on the
    real owned per-level chain emit `"treehash_chain_" ++ toString n`
    (`X86Backend/TreehashChainOwnedEmit.lean`). -/
def merkleLeaves3 : List String :=
  ["merkle_path_fold_1", "merkle_path_fold_2", "merkle_path_fold_3"]

/-- Bundle a depth-3 Merkle authentication-path verifier from its decoder and
    the three per-level fold realizations.  This is the axis-6 instantiation on
    a real protocol: list the per-level hash leaves, list the per-level fold
    specs, supply the decoder, and assemble the per-level realizations into the
    position-wise `Forall₂`. -/
def merkleProtocol3 (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf₁ leaf₂ leaf₃ : String) (fold₁ fold₂ fold₃ : C → C)
    (h₁ : KernelRealizes decode fold₁ leaf₁ leafSpec)
    (h₂ : KernelRealizes decode fold₂ leaf₂ leafSpec)
    (h₃ : KernelRealizes decode fold₃ leaf₃ leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := [leaf₁, leaf₂, leaf₃]
  specs := [fold₁, fold₂, fold₃]
  decode := decode
  realized :=
    List.Forall₂.cons h₁ (List.Forall₂.cons h₂ (List.Forall₂.cons h₃ List.Forall₂.nil))

/-- **The worked axis-6 deliverable (depth 3).**  The depth-3 authentication
    path's whole emitted pipeline (`pipeN` over the three per-level leaves)
    decodes to the composite fold `composeSpecs [fold₁, fold₂, fold₃]` of the
    input leaf digest — the recomputed root.  Obtained by a single `runRealizes`
    call on the assembled `ProtocolKernels`, from nothing but the three
    per-level realizations. -/
theorem merkle_path_realizes3 (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf₁ leaf₂ leaf₃ : String) (fold₁ fold₂ fold₃ : C → C)
    (h₁ : KernelRealizes decode fold₁ leaf₁ leafSpec)
    (h₂ : KernelRealizes decode fold₂ leaf₂ leafSpec)
    (h₃ : KernelRealizes decode fold₃ leaf₃ leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec [leaf₁, leaf₂, leaf₃] oldDest xVal)
      = composeSpecs [fold₁, fold₂, fold₃] (decode xVal) :=
  (merkleProtocol3 leafSpec decode leaf₁ leaf₂ leaf₃ fold₁ fold₂ fold₃ h₁ h₂ h₃).runRealizes
    oldDest xVal

/-- The depth-3 composite fold made concrete: applied in pipeline order it is
    `fold₃ ∘ fold₂ ∘ fold₁` — fold with sibling 1, then 2, then 3, recomputing
    the root level by level. -/
theorem composeSpecs_merkle3 (fold₁ fold₂ fold₃ : C → C) (x : C) :
    composeSpecs [fold₁, fold₂, fold₃] x = fold₃ (fold₂ (fold₁ x)) := by
  simp [composeSpecs, Function.comp]

/-! ## §2  A general depth-`d` Merkle authentication path

The depth-3 assembly above is the `List.Forall₂.cons …` spelling for a fixed
length.  Since `pipeN` / `composeSpecs` already handle arbitrary length, the
**general depth-`d`** path needs no new proof skeleton: bundle the per-level
leaves, folds, and a single `Forall₂` of per-level realizations, then call
`runRealizes`.  The hypothesis is stated directly as the position-wise
`Forall₂` between the path's per-level leaves and their fold specs. -/

/-- Bundle a depth-`d` Merkle authentication-path verifier: the per-level
    leaf-names, the per-level fold specs, the decoder, and the position-wise
    `Forall₂` of per-level realizations (each discharged by that level's
    leaf-bytes KAT).  `d` is implicit in the list lengths. -/
def merkleProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaves : List String) (folds : List (C → C))
    (realized : List.Forall₂
      (fun leaf fold => KernelRealizes decode fold leaf leafSpec) leaves folds) :
    ProtocolKernels C leafSpec where
  leaves := leaves
  specs := folds
  decode := decode
  realized := realized

/-- **The whole authentication-path emit-realization (general depth `d`).**  If
    every per-level kernel of the path realizes its fold spec (position-wise,
    via `Forall₂`), then the whole `pipeN` pipeline over the path's per-level
    leaves decodes to the composite fold `composeSpecs folds` of the input leaf
    digest — the recomputed root, for arbitrary depth.  Assembled purely from
    the per-level realizations and the generic composition law via one
    `runRealizes` call. -/
theorem merkle_path_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaves : List String) (folds : List (C → C))
    (realized : List.Forall₂
      (fun leaf fold => KernelRealizes decode fold leaf leafSpec) leaves folds)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec leaves oldDest xVal)
      = composeSpecs folds (decode xVal) :=
  (merkleProtocol leafSpec decode leaves folds realized).runRealizes oldDest xVal

end CatCrypt.Crypto.SecureCompilation.MerkleProtocolKernels
