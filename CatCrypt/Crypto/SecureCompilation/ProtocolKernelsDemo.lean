/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# The axis-6 per-protocol template, worked end-to-end

`ProtocolEmitRealizes` factors the per-protocol emit-realization skeleton into a
single composition law (`pipeN_realizes`) and a bundling structure
(`ProtocolKernels` + `ProtocolKernels.runRealizes`).  This file is the **worked
instantiation** of that template: it shows what "per-protocol emit = list kernel
rows + cite each kernel's realization + compose" looks like concretely.

The demonstrator is over a deliberately trivial carrier and trivial specs — the
point is the **composition mechanism running end-to-end on an instantiated
`ProtocolKernels`**, not any cryptographic content.  We:

* fix the carrier `C := ℕ` and a two-kernel pipeline with abstract specs
  `spec1 := (· + 1)` and `spec2 := (· * 2)` (any concrete unary ops work — the
  composition is spec-agnostic);
* take each kernel's `KernelRealizes` fact as a **hypothesis** — this is exactly
  how a real protocol cites its kernels: a faithful realizer is the per-kernel
  leaf-bytes KAT, supplied at instantiation (cf.
  `GenericNttEmitValue.nttKernelRealizes_canonical` for a discharged instance);
* assemble those hypotheses into a `ProtocolKernels ℕ leafSpec` value whose
  `realized` field is the position-wise `List.Forall₂` of the per-kernel facts;
* apply `ProtocolKernels.runRealizes` to obtain the **whole-pipeline
  emit-realization** — running the two-leaf `pipeN` pipeline decodes to the
  composite `composeSpecs [spec1, spec2]` of the input.

## The point (axis-6)

Per-protocol emit-realization is *exactly* this instantiation.  To scale to a
real protocol: replace the two abstract leaves with the protocol's emitted
kernel leaf-names, replace the abstract specs with the kernels' real specs (e.g.
the registered ML-KEM NTT-multiply spec), and replace each hypothesis with that
kernel's discharged realization (its leaf-bytes KAT).  The list grows; the
`runRealizes` call is unchanged.  The whole-protocol emit-realization assembles
purely from the per-kernel realizations and the generic composition law — no new
per-protocol proof skeleton.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ProtocolKernelsDemo

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-! ## The two abstract kernel specs

A two-kernel pipeline over the concrete carrier `ℕ`.  `spec1` increments,
`spec2` doubles; applied in pipeline order the composite is `fun x => 2*(x+1)`.
These stand in for a protocol's two emitted-kernel specs. -/

/-- First kernel's abstract spec: increment. -/
def spec1 : ℕ → ℕ := fun x => x + 1

/-- Second kernel's abstract spec: double. -/
def spec2 : ℕ → ℕ := fun x => x * 2

/-! ## The assembled `ProtocolKernels` value

Given a realizer `leafSpec`, a decoder `decode`, the two leaf-names, and each
kernel's `KernelRealizes` fact (the per-kernel KAT, taken as a hypothesis), we
bundle them into a `ProtocolKernels ℕ leafSpec`.  The `realized` field is the
position-wise `List.Forall₂` over `[leaf1, leaf2]`/`[spec1, spec2]`, built with
two `List.Forall₂.cons` and a closing `List.Forall₂.nil`. -/

/-- Bundle a two-kernel demo protocol from its decoder and the two per-kernel
    realizations.  This is the axis-6 instantiation: list the leaves, list the
    specs, supply the decoder, and assemble the per-kernel realizations into the
    position-wise `Forall₂`. -/
def demoProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → ℕ)
    (leaf1 leaf2 : String)
    (h1 : KernelRealizes decode spec1 leaf1 leafSpec)
    (h2 : KernelRealizes decode spec2 leaf2 leafSpec) :
    ProtocolKernels ℕ leafSpec where
  leaves := [leaf1, leaf2]
  specs := [spec1, spec2]
  decode := decode
  realized := List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil)

/-! ## The whole-pipeline emit-realization

`ProtocolKernels.runRealizes` applied to `demoProtocol` is the axis-6
deliverable: the full two-leaf `pipeN` pipeline, read through `decode`, computes
the composite of the two kernel specs.  Assembled purely from the per-kernel
realizations `h1`, `h2` and the generic composition law. -/

/-- **The worked axis-6 deliverable.**  The demo protocol's whole emitted
    pipeline (`pipeN` over `[leaf1, leaf2]`) decodes to the composite
    `composeSpecs [spec1, spec2]` of the input — obtained by a single
    `runRealizes` call on the assembled `ProtocolKernels`, from nothing but the
    two per-kernel realizations. -/
theorem demo_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → ℕ)
    (leaf1 leaf2 : String)
    (h1 : KernelRealizes decode spec1 leaf1 leafSpec)
    (h2 : KernelRealizes decode spec2 leaf2 leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec [leaf1, leaf2] oldDest xVal)
      = composeSpecs [spec1, spec2] (decode xVal) :=
  (demoProtocol leafSpec decode leaf1 leaf2 h1 h2).runRealizes oldDest xVal

/-! ## The composite, made concrete

A sanity check that `composeSpecs [spec1, spec2]` is the expected `fun x =>
2*(x+1)`, so the conclusion of `demo_protocol_realizes` is fully concrete: the
whole pipeline computes "increment then double". -/

/-- `composeSpecs [spec1, spec2]` applies `spec1` first, then `spec2`:
    incrementing then doubling, i.e. `x ↦ (x + 1) * 2`. -/
theorem composeSpecs_demo (x : ℕ) :
    composeSpecs [spec1, spec2] x = (x + 1) * 2 := by
  simp [composeSpecs, spec1, spec2, Function.comp]

end CatCrypt.Crypto.SecureCompilation.ProtocolKernelsDemo
