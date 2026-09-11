/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# HKDF (RFC 5869) as an axis-6 `ProtocolKernels` instantiation

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on an **actual
protocol**: HKDF, the HMAC-based key-derivation function of RFC 5869.

HKDF is structurally a **unary hash chain**:

* `HKDF-Extract(salt, IKM)` runs one HMAC application to produce a
  pseudorandom key `PRK`;
* `HKDF-Expand(PRK, info, L)` runs a *chain* of HMAC applications
  `T(1) = HMAC(PRK, info ‖ 0x01)`, `T(i) = HMAC(PRK, T(i-1) ‖ info ‖ i)`,
  feeding each block's output into the next.

Both phases are HMAC-of-the-running-state, i.e. a sequence of `state → state`
steps over the keying material — exactly the *unary* pipeline the
`ProtocolKernels` template models (unlike a mixed-arity primitive such as
ML-KEM).  HKDF is therefore a faithful, clean real-protocol instantiation of the
axis-6 template.

## What this file delivers

* `hkdfSpecs` — the HKDF kernel pipeline as a list of unary specs over a carrier
  `C`: one `extractStep` followed by `n` `expandStep i` HMAC rounds.  These are
  **abstract** opaque models of each HKDF round; the deliverable is the
  protocol-structure composition, not re-deriving HKDF's HMAC internals.
* `hkdfLeaves` — the matching emitted leaf-names, taken from the real HKDF
  extraction (`"hkdf_sha256_extract"`, `"hkdf_sha256_expand"`, …; cf.
  `CatCrypt/Crypto/HKDF/`).
* `hkdfProtocol` — the assembled `ProtocolKernels C leafSpec`, whose `realized`
  field is the position-wise `List.Forall₂` of the per-kernel realizations,
  each taken as a **hypothesis** — which is exactly how a protocol cites each
  HMAC kernel's leaf-bytes KAT at instantiation.
* `hkdf_protocol_realizes` — the whole-HKDF emit-realization,
  `decode (pipeN hkdfLeaves …) = composeSpecs hkdfSpecs (decode x)`, obtained by
  a single `runRealizes` call from nothing but the per-kernel realizations and
  the generic composition law.

## The point (axis-6 on a real protocol)

HKDF — a real RFC-5869 protocol — has its *whole* emit-realization assembled
from its hash-kernel rows by `runRealizes`, with no per-protocol proof skeleton:
the hash-chain structure fits the unary `ProtocolKernels` template exactly.  The
per-kernel realizations are honest hypotheses (each is the kernel's leaf-bytes
KAT); the contribution is that the protocol-level composition assembles for free
from them.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HkdfProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-! ## §1  The HKDF kernel specs (abstract, unary)

We model HKDF's pipeline over an arbitrary carrier `C` with abstract opaque
round functions.  `extractStep : C → C` stands for the single HKDF-Extract HMAC
application; `expandStep i : C → C` stands for the `i`-th HKDF-Expand HMAC block
`T(i) = HMAC(PRK, T(i-1) ‖ info ‖ i)`.  Concretely these are HMAC-of-the-running
state; here they are opaque parameters because the deliverable is the
pipeline-realization *composition* over HKDF's structure, not HKDF's HMAC
internals. -/

variable {C : Type*}

/-- The HKDF kernel-spec list for an `n`-block expand: one `extractStep`
    followed by `n` expand blocks `expandStep 0, …, expandStep (n-1)`.  Pipeline
    order is HKDF order: extract first, then each expand block in sequence. -/
def hkdfSpecs (extractStep : C → C) (expandStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  extractStep :: (List.range n).map (fun i => expandStep i)

/-! ## §2  The HKDF emitted-kernel leaf-names

Taken from the real HKDF extraction (`CatCrypt/Crypto/HKDF/`): the extract leaf
`"hkdf_sha256_extract"` and the expand leaf `"hkdf_sha256_expand"`.  Each expand
block reuses the same emitted expand kernel, so the leaf list is the extract
leaf followed by `n` copies of the expand leaf — matching `hkdfSpecs`'s length. -/

/-- The emitted leaf-name of the HKDF-Extract kernel (SHA-256 instance). -/
def hkdfExtractLeaf : String := "hkdf_sha256_extract"

/-- The emitted leaf-name of the HKDF-Expand HMAC-block kernel (SHA-256). -/
def hkdfExpandLeaf : String := "hkdf_sha256_expand"

/-- The HKDF emitted-kernel leaf list for an `n`-block expand: the extract leaf,
    then `n` copies of the expand leaf — same length and order as
    `hkdfSpecs … n`. -/
def hkdfLeaves (n : Nat) : List String :=
  hkdfExtractLeaf :: List.replicate n hkdfExpandLeaf

/-! ## §3  The assembled HKDF `ProtocolKernels`

Given the decoder, the abstract round specs, and each kernel's `KernelRealizes`
fact (the per-kernel leaf-bytes KAT, taken as a hypothesis — the extract row and
one row per expand block), we bundle them into a `ProtocolKernels C leafSpec`.
The `realized` field is the position-wise `List.Forall₂` over
`hkdfLeaves n`/`hkdfSpecs … n`. -/

/-- The position-wise realization bundle for the `n`-block expand pipeline,
    assembled by induction on `n` from the extract-kernel realization and one
    expand-block realization per block.  This is the `List.Forall₂.cons`/`nil`
    assembly the template's `realized` field demands, generalized to `n`. -/
theorem hkdfRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (extractStep : C → C) (expandStep : Nat → C → C) (n : Nat)
    (hExtract : KernelRealizes decode extractStep hkdfExtractLeaf leafSpec)
    (hExpand : ∀ i, KernelRealizes decode (expandStep i) hkdfExpandLeaf leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      (hkdfLeaves n) (hkdfSpecs extractStep expandStep n) := by
  unfold hkdfLeaves hkdfSpecs
  refine List.Forall₂.cons hExtract ?_
  -- Tail: `replicate n hkdfExpandLeaf` realizes `(range n).map (expandStep ·)`.
  induction n with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.replicate_succ']
      exact List.rel_append ih (List.Forall₂.cons (hExpand m) List.Forall₂.nil)

/-- **The assembled HKDF protocol.**  The axis-6 instantiation on a real
    protocol: the extract + `n` expand leaves, their abstract round specs, the
    decoder, and the per-kernel realizations assembled into the position-wise
    `Forall₂` via `hkdfRealized`. -/
def hkdfProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (extractStep : C → C) (expandStep : Nat → C → C) (n : Nat)
    (hExtract : KernelRealizes decode extractStep hkdfExtractLeaf leafSpec)
    (hExpand : ∀ i, KernelRealizes decode (expandStep i) hkdfExpandLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := hkdfLeaves n
  specs := hkdfSpecs extractStep expandStep n
  decode := decode
  realized :=
    hkdfRealized leafSpec decode extractStep expandStep n hExtract hExpand

/-! ## §4  The whole-HKDF emit-realization

`ProtocolKernels.runRealizes` applied to `hkdfProtocol` is the axis-6
deliverable on a real protocol: the full extract-then-`n`-expand `pipeN`
pipeline, read through `decode`, computes the composite `composeSpecs hkdfSpecs`
of the input keying material.  Assembled purely from the per-kernel
realizations `hExtract`, `hExpand` and the generic composition law — no
per-protocol proof skeleton. -/

/-- **The whole-HKDF emit-realization (axis-6 on a real protocol).**  HKDF's
    entire emitted hash chain — `pipeN` over `hkdfLeaves n` (one extract kernel
    then `n` expand HMAC blocks) — decodes to the composite
    `composeSpecs (hkdfSpecs …)` of the input.  Obtained by a single
    `runRealizes` call on the assembled `ProtocolKernels`, from nothing but the
    per-kernel realizations (each an honest leaf-bytes KAT hypothesis) and the
    generic composition law. -/
theorem hkdf_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (extractStep : C → C) (expandStep : Nat → C → C) (n : Nat)
    (hExtract : KernelRealizes decode extractStep hkdfExtractLeaf leafSpec)
    (hExpand : ∀ i, KernelRealizes decode (expandStep i) hkdfExpandLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (hkdfLeaves n) oldDest xVal)
      = composeSpecs (hkdfSpecs extractStep expandStep n) (decode xVal) :=
  (hkdfProtocol leafSpec decode extractStep expandStep n hExtract hExpand).runRealizes
    oldDest xVal

end CatCrypt.Crypto.SecureCompilation.HkdfProtocolKernels
