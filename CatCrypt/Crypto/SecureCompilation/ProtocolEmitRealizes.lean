/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue

/-!
# The generic PROTOCOL emit-realization template (axis-6 enabler)

Per-protocol emit-realization results — "the emitted kernels of protocol `P`
compute `P`'s abstract specification" — share one algebraic skeleton: each
*leaf* of the computation is emit-realized (its leaf-call value decodes to a
single-kernel spec applied to the decoded arguments), and the *pipeline* feeds
one kernel's output to the next.  The composition is then just the composition
of the kernel specs.

This module factors out that skeleton as a **composition law** over the
`LeafSpec.call` oracle (`Jasmin/LowCT.lean §6`):

* `KernelRealizes decode spec leaf leafSpec` — the single-kernel realization
  predicate (`GenericNttEmitValue.NttEmitRealizes`'s shape, generalized to an
  abstract carrier `C` and a unary spec for clean composition).
* `pipe2` / `pipe2_realizes` — the **composition primitive**: two realized
  kernels chained (`leaf1` then `leaf2`-of-`leaf1`) realize the composite spec
  `spec2 ∘ spec1`.  Proof: two substitution rewrites — `h2` on the outer call,
  then `h1` on its argument.
* `pipeN` / `pipeN_realizes` — the n-kernel generalization: a `List.foldl`
  pipeline of realized kernels realizes the `List.foldr`-composite of their
  specs.  Hypothesis bundled via `List.Forall₂` to avoid dependent-index
  fiddliness; proved by induction on the `Forall₂` witness.
* `ProtocolKernels` / `ProtocolKernels.runRealizes` — the **per-protocol
  template**: bundle a protocol's kernel list, its kernels' specs, the decoder,
  and the (per-kernel) realizations; `runRealizes` then delivers the
  whole-pipeline emit-realization for free.

## The point (axis-6)

A protocol whose every kernel is emit-realized has its *whole computation*
emit-realized — the composition of the kernel specs — by `pipeN_realizes`.
Per-protocol emit reduces to a thin instantiation: list the kernels, cite each
kernel's realization (e.g. each `KernelRealizes` discharged by a leaf-bytes KAT
as in `GenericNttEmitValue.nttKernelRealizes_canonical`), and apply the
template.  Nothing here is protocol-specific: the law is purely the algebra of
substituting realized leaf-calls into one another.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  The single-kernel realization predicate

`KernelRealizes decode spec leaf leafSpec` is the unary, carrier-generic shape
of `GenericNttEmitValue.NttEmitRealizes`: for every operand value `xVal` (and
any prior dest value `oldDest`), the `leaf`-call on the `.TFp` carrier with one
positional `.TFp` argument decodes (via `decode : RustVal .TFp → C`) to
`spec (decode xVal)` — the abstract single-kernel value.

Keeping the spec **unary** makes the composition law clean (one output feeds one
input).  The binary case — two positional `.TFp` arguments and a `spec : C → C →
C` — is entirely analogous; `GenericNttEmitValue.NttEmitRealizes` is exactly
that binary instance with `C := Fin n → R` and `spec := nttMul n ω`. -/

/-- **The single-kernel emit-realization predicate** (carrier-generic, unary).
    The `leaf`-call value decodes to `spec` applied to the decoded argument —
    the localized "this leaf computes `spec`" residual, exactly the shape a
    leaf-bytes KAT discharges. -/
def KernelRealizes {C : Type*} (decode : RustVal .TFp → C) (spec : C → C)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (xVal oldDest : RustVal .TFp),
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = spec (decode xVal)

/-! ## §2  The composition primitive — two kernels

Model a 2-kernel pipeline as the **value** obtained by applying `leaf1` to the
input, then feeding that `RustVal .TFp` output to `leaf2`.  Working at the value
level (rather than re-storing into a `RustState` and re-reading) sidesteps any
encode/decode round-trip: the realization of each kernel is about its leaf-call
value directly, so chaining the values composes the realizations directly. -/

/-- The value produced by chaining `leaf1` then `leaf2`: `leaf2`'s sole `.TFp`
    argument is `leaf1`'s output value. -/
def pipe2 (leafSpec : LeafSpec) (leaf1 leaf2 : String)
    (oldDest xVal : RustVal .TFp) : RustVal .TFp :=
  leafSpec.call leaf2 .TFp [.TFp] oldDest
    [⟨.TFp, leafSpec.call leaf1 .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]⟩]

/-- **The composition primitive.**  If `leaf1` realizes `spec1` and `leaf2`
    realizes `spec2`, then the chained pipeline `pipe2 … leaf1 leaf2` realizes
    the composite `spec2 ∘ spec1`.

    Proof: unfold `pipe2`; `h2` rewrites the outer `leaf2`-call to `spec2` of its
    argument's decode; that argument is the `leaf1`-call, whose decode is
    `spec1 (decode xVal)` by `h1`.  Two substitution rewrites — the realized
    kernels compose to a realized pipeline. -/
theorem pipe2_realizes {C : Type*} (decode : RustVal .TFp → C)
    (spec1 spec2 : C → C) (leaf1 leaf2 : String) (leafSpec : LeafSpec)
    (h1 : KernelRealizes decode spec1 leaf1 leafSpec)
    (h2 : KernelRealizes decode spec2 leaf2 leafSpec) :
    ∀ (xVal oldDest : RustVal .TFp),
      decode (pipe2 leafSpec leaf1 leaf2 oldDest xVal)
        = spec2 (spec1 (decode xVal)) := by
  intro xVal oldDest
  unfold pipe2
  rw [h2 _ oldDest, h1 xVal oldDest]

/-! ## §3  The n-kernel pipeline

Fold the kernel list left-to-right, threading the running `RustVal .TFp`
through each leaf-call.  `pipeN leafSpec [k₁, …, kₘ] oldDest xVal` applies `k₁`
to `xVal`, then `k₂` to that, …, returning the final value.

The realization hypothesis is bundled as `List.Forall₂` between the leaves and
their specs: position-wise, `leaves[i]` realizes `specs[i]`.  This avoids
dependent `List.get` index juggling — induction is on the `Forall₂` witness. -/

/-- The value produced by chaining a *list* of kernels left-to-right. -/
def pipeN (leafSpec : LeafSpec) (leaves : List String)
    (oldDest xVal : RustVal .TFp) : RustVal .TFp :=
  leaves.foldl
    (fun acc leaf => leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, acc⟩])
    xVal

/-- The composite spec of a kernel list: `[s₁, …, sₘ]` ↦ `sₘ ∘ … ∘ s₁` (apply
    `s₁` first).  Written as a left fold so it matches `pipeN`'s threading order. -/
def composeSpecs {C : Type*} (specs : List (C → C)) : C → C :=
  specs.foldl (fun acc f => f ∘ acc) id

/-- **The n-kernel composition law.**  If each leaf in `leaves` realizes the
    corresponding spec in `specs` (position-wise, via `List.Forall₂`), then the
    `pipeN` pipeline realizes the composite spec `composeSpecs specs`
    (= `specs.foldl (· ∘ ·)` applied in order).

    Proof: induction on the `Forall₂` witness.  The nil case is `decode xVal =
    id (decode xVal)`.  The cons case threads `KernelRealizes` for the head
    (rewriting the first leaf-call's decode to `spec (decode xVal)`), then
    applies the induction hypothesis to the remaining pipeline started from that
    new value — `foldl` over the tail with the new accumulator on both sides. -/
theorem pipeN_realizes {C : Type*} (decode : RustVal .TFp → C)
    (leafSpec : LeafSpec) :
    ∀ (leaves : List String) (specs : List (C → C)),
      List.Forall₂ (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
        leaves specs →
      ∀ (oldDest xVal : RustVal .TFp),
        decode (pipeN leafSpec leaves oldDest xVal)
          = composeSpecs specs (decode xVal) := by
  intro leaves specs h
  induction h with
  | nil =>
      intro oldDest xVal
      simp [pipeN, composeSpecs]
  | @cons leaf spec restL restS hhead _htail ih =>
      intro oldDest xVal
      -- Peel the first leaf-call off both pipeline and spec-fold.
      have hstep : decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
          = spec (decode xVal) := hhead xVal oldDest
      -- `pipeN` of the cons is `pipeN` of the tail started from the new value.
      have hpipe : pipeN leafSpec (leaf :: restL) oldDest xVal
          = pipeN leafSpec restL oldDest
              (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]) := by
        simp [pipeN, List.foldl_cons]
      -- `composeSpecs` of the cons is `composeSpecs` of the tail post-composed
      -- with the head spec — i.e. apply head first, then the tail composite.
      have hcomp : ∀ (g : C → C) (ss : List (C → C)) (c : C),
          ss.foldl (fun acc f => f ∘ acc) g c
            = ss.foldl (fun acc f => f ∘ acc) id (g c) := by
        intro g ss
        induction ss generalizing g with
        | nil => intro c; rfl
        | cons s ss' ihs =>
            intro c
            simp only [List.foldl_cons]
            rw [ihs (s ∘ g), ihs (s ∘ id)]
            simp
      rw [hpipe, ih oldDest
        (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]), hstep]
      -- Goal: composeSpecs restS (spec (decode xVal))
      --     = composeSpecs (spec :: restS) (decode xVal)
      simp only [composeSpecs, List.foldl_cons]
      rw [hcomp (spec ∘ id) restS (decode xVal)]
      simp

/-! ## §4  The per-protocol template

`ProtocolKernels` bundles a protocol's emitted-kernel pipeline: the kernel
leaf-names, their abstract single-kernel specs, the decoder, and the per-kernel
realizations (position-wise via `Forall₂`).  `runRealizes` then delivers the
whole-pipeline emit-realization for free — the protocol's entire computation
decodes to the composite spec.

To instantiate for a concrete protocol: provide its kernel `leaves`, the matching
`specs`, the `decode`, and a `Forall₂` of `KernelRealizes` proofs (each
discharged by that kernel's leaf-bytes KAT, e.g. as in
`GenericNttEmitValue.nttKernelRealizes_canonical`).  `runRealizes` is the
protocol's emit-realization theorem. -/

/-- **The per-protocol emit template.**  A protocol's emitted pipeline: kernel
    leaf-names, their specs, the decoder, and the position-wise realization
    bundle. -/
structure ProtocolKernels (C : Type*) (leafSpec : LeafSpec) where
  /-- The protocol's emitted kernel leaf-names, in pipeline order. -/
  leaves : List String
  /-- The abstract single-kernel spec of each leaf (same order). -/
  specs : List (C → C)
  /-- The decoder reading the `.TFp` slot as the abstract carrier `C`. -/
  decode : RustVal .TFp → C
  /-- Each leaf realizes its spec (position-wise) — the per-kernel residuals. -/
  realized : List.Forall₂
    (fun leaf spec => KernelRealizes decode spec leaf leafSpec) leaves specs

/-- **The whole-protocol emit-realization.**  The bundled protocol's full
    `pipeN` pipeline decodes to the composite of its kernel specs.  This is the
    axis-6 deliverable: per-protocol emit is `ProtocolKernels` + this one call. -/
theorem ProtocolKernels.runRealizes {C : Type*} {leafSpec : LeafSpec}
    (P : ProtocolKernels C leafSpec) (oldDest xVal : RustVal .TFp) :
    P.decode (pipeN leafSpec P.leaves oldDest xVal)
      = composeSpecs P.specs (P.decode xVal) :=
  pipeN_realizes P.decode leafSpec P.leaves P.specs P.realized oldDest xVal

end CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
