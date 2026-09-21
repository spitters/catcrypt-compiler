/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer
public import CatCrypt.Crypto.SecureCompilation.ConcreteNegacyclicRealizer

/-!
# Kernel realization as a typeclass-resolved registry — the Trocq `Related` engine, for emit

`GenericKernelRealization` factors every per-primitive emit→value seam into one
predicate: `decode (leafSpec.call leaf … args) = spec (decode-of-args)` — a
`RelatedBinOp.comm` / `ReprTransfer.BinOpHomOn` *commuting square* whose
transport witness is the decoding map `decode` (the map₁, univalence-free
direction of a Trocq `Param` relation).  That file states the realizations as
ordinary `Prop`s and composes them by hand (`pipe2_realizes`).

This file promotes the **same** predicate to a **typeclass-resolved registry**,
mirroring the in-repo Trocq engine `Bridges/Transfer/Related.lean` field-for-field:

| Trocq (`Related.lean`)            | here (kernel realization)             |
|-----------------------------------|---------------------------------------|
| `class Related enc a b`           | `class KernelRealizesC decode spec leaf leafSpec` |
| `class RelatedBinOp enc op bop`   | `class KernelRealizes2C decode spec leaf leafSpec` (binary leaf) |
| `theorem transferRel`             | `transferKernelC` / `transferKernel2C` (extract the equation) |
| `instance composeBinOp`           | `composeKernelC` (pipe-compose two unary kernels) |
| `instance bbMulRelated` (closed)  | `nttMulC` / `nttNegaMulC` (closed concrete realizers) |

So:

* the realization **table is a typeclass database**: each registered kernel is an
  `instance`, and instance resolution synthesizes a kernel's realization (and, by
  the composition instance, a *composite* pipeline's realization) automatically —
  the fractalyze table-driven mechanism realized via Lean's instance resolution;
* `decode` is the transport witness — the map₁, univalence-free direction (no
  univalence is invoked anywhere here, exactly as in `Related`'s `map4` cap);
* **adding a primitive with a concrete realizer = one `instance`**.

## What is a *bare* instance and what is not (the honesty boundary)

Trocq registers `bbMulRelated` as a bare `instance` precisely because
`bbFieldMul_eq` is an **unconditional** theorem — the commuting square holds with
no hypothesis.  We follow the same rule:

* The cyclic-transform realizer at (3329, 256, ω = 17)
  (`ConcreteNttRealizer.mlkem_nttEmitRealizes_concrete`, which realizes
  `nttMul 256 17 = cyclicConv 256` over `ZMod 3329` — multiplication modulo
  `X^256 − 1`, not FIPS 203's transform) and the ML-DSA negacyclic realizer
  (`ConcreteNegacyclicRealizer.mldsa_nttNegaEmitRealizes_concrete`) hold with
  no hypothesis (their byte-level `decode ∘ encode = id` is the theorem
  `decodeP_encodeP` / `decodeP3_encodeP3`, not a KAT).  They are therefore
  bare instances — registered as `nttMulC` / `nttNegaMulC`.  Each is
  parametric over the kernel's `limbStore : LimbStoreSpec` (the realizer
  `LeafSpec` is built from it), so the instance is a parametric instance keyed on
  `limbStore`, not on a fixed store.
* The **per-primitive `.TFp` seams** (`barrett_iff_kernel`, `fermat_iff_kernel`,
  `ntt_iff_kernel2`, `montMul_iff_kernel2`) are `Iff.rfl` *re-statements*; the
  underlying realization still needs a concrete realizer that discharges the
  leaf-bytes KAT before it is a closed fact.  They are therefore **not** bare
  instances here — exactly as a `RelatedBinOp` whose commuting square is still an
  open KAT would not be registered.  They become instances only once a concrete
  realizer (à la `ConcreteNttRealizer`) discharges them.

## Carriers: `.TFp` (generic engine) vs `.TPolyMod q n` (honest NTT registry)

The generic `KernelRealizes` / `KernelRealizes2` predicates live over the `.TFp`
carrier (`= JArray 48`, 384 bits).  That carrier is **too small** for a
round-trip on a degree-256 polynomial vector mod 3329 or mod 8380417
(pigeonhole — see `ConcreteNttRealizer`'s module docstring), so the *concrete*
realizers live over the larger `.TPolyMod q n` carrier (`NttEmitRealizesP` /
`NttNegaEmitRealizesP`).  We give the typeclass engine over **both**:

* `KernelRealizesC` / `KernelRealizes2C` + `composeKernelC` — the generic `.TFp`
  engine (classes + extractors + composition), mirroring `Related` structurally;
* `NttEmitRealizes2C` — the `.TPolyMod q n` binary NTT class that the two
  hypothesis-free concrete realizers populate as bare instances, so instance
  resolution finds the (3329, 256, ω = 17) cyclic-transform and the ML-DSA
  negacyclic realizations automatically.

## References
* `CatCrypt/Crypto/Bridges/Transfer/Related.lean` — the template engine.
* NIST FIPS 203 (ML-KEM), FIPS 204 (ML-DSA).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.KernelRealizesClass

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization

/-! ## §1  The resolvable classes (mirror of `Related` / `RelatedBinOp`)

`KernelRealizesC` wraps the unary `KernelRealizes` predicate; `KernelRealizes2C`
wraps the binary `KernelRealizes2`.  Each is a single-field `Prop` class — the
field is the realization — exactly as `Related`'s single field is `rel`.  Making
them classes is what lets instance resolution synthesize a registry lookup. -/

/-- **Unary kernel-realization class** — the `Related` analogue.  An instance
    `KernelRealizesC decode spec leaf leafSpec` asserts that the `leaf`-call,
    read through `decode`, computes `spec` of the decoded argument: the unary
    commuting square, registered for instance resolution. -/
class KernelRealizesC {C : Type*} (decode : RustVal .TFp → C) (spec : C → C)
    (leaf : String) (leafSpec : LeafSpec) : Prop where
  /-- The registered unary realization. -/
  realizes : KernelRealizes decode spec leaf leafSpec

/-- **Binary kernel-realization class** — the `RelatedBinOp` analogue.  An
    instance asserts that the two-operand `leaf`-call, read through `decode`,
    computes `spec` of the two decoded operands: the binary commuting square,
    registered for instance resolution. -/
class KernelRealizes2C {C : Type*} (decode : RustVal .TFp → C) (spec : C → C → C)
    (leaf : String) (leafSpec : LeafSpec) : Prop where
  /-- The registered binary realization. -/
  realizes : KernelRealizes2 decode spec leaf leafSpec

/-! ## §2  The transfer extractors (mirror of `transferRel`) -/

/-- **Transfer (unary).**  From a synthesized `KernelRealizesC` instance, extract
    the realization equation at a point — the `Trocq.transferRel` analogue. -/
theorem transferKernelC {C : Type*} {decode : RustVal .TFp → C} {spec : C → C}
    {leaf : String} {leafSpec : LeafSpec} [h : KernelRealizesC decode spec leaf leafSpec]
    (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]) = spec (decode xVal) :=
  transferKernel h.realizes xVal oldDest

/-- **Transfer (binary).**  From a synthesized `KernelRealizes2C` instance, extract
    the binary realization equation at a point. -/
theorem transferKernel2C {C : Type*} {decode : RustVal .TFp → C} {spec : C → C → C}
    {leaf : String} {leafSpec : LeafSpec}
    [h : KernelRealizes2C decode spec leaf leafSpec]
    (aVal bVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = spec (decode aVal) (decode bVal) :=
  transferKernel2 h.realizes aVal bVal oldDest

/-! ## §3  The composition law (mirror of `composeBinOp`)

`Related.composeBinOp` synthesizes a composite `Related enc (op a b) (bop a' b')`
from a `RelatedBinOp` and two `Related`s.  The kernel analogue composes two
*unary* realized kernels into the realization of their pipeline (`pipe2`): the
output of `leaf1` (realizing `spec1`) feeds `leaf2` (realizing `spec2`), and the
pipeline realizes `spec2 ∘ spec1`.

We provide this as an explicit composition **lemma** (`composeKernelC`), not a
bare `instance`.  Reason — and this is the instance-resolution lesson: an
`instance` producing `KernelRealizesC decode (spec2 ∘ spec1) (…pipe of leaf1
leaf2…) …` cannot key on a stable syntactic head the way `composeBinOp` does.
`composeBinOp` keys on the *op-tree head* `op a b`, which is present in the goal;
here the "composite leaf" is a `pipe2`-formed `String`-level pipeline that is not
a head Lean can match a goal against without already knowing both leaves.  Making
it an instance would force resolution to *guess* the `pipe2` split — diverging.
So composition is a lemma the caller applies with both kernels named, while the
*leaf* realizations themselves remain instance-resolved.  (`Related`'s analogue
works only because the op-tree is syntactically present; a string-pipeline is
not.) -/

/-- **Composition lemma** — the `composeBinOp` analogue for kernel pipelines.
    Two unary kernel classes synthesize the realization of their `pipe2`
    pipeline at the composite spec `spec2 ∘ spec1`.  The two leaf realizations
    are found by instance resolution (`inferInstance`); only the pipeline split
    is supplied explicitly. -/
theorem composeKernelC {C : Type*} (decode : RustVal .TFp → C) (spec1 spec2 : C → C)
    (leaf1 leaf2 : String) (leafSpec : LeafSpec)
    [h1 : KernelRealizesC decode spec1 leaf1 leafSpec]
    [h2 : KernelRealizesC decode spec2 leaf2 leafSpec]
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf1 leaf2 oldDest xVal) = spec2 (spec1 (decode xVal)) :=
  pipe2_realizes decode spec1 spec2 leaf1 leaf2 leafSpec h1.realizes h2.realizes xVal oldDest

/-! ## §4  Registering the concrete realizers as instances (the typeclass table)

These are the closed rows of the registry — the `bbMulRelated` analogue.  Both
NTT-multiply realizers are theorems without hypothesis over the `.TPolyMod q n`
carrier (`NttEmitRealizesP` / `NttNegaEmitRealizesP`), so they are bare
instances.  We give a `.TPolyMod q n` binary class `NttEmitRealizes2C`,
parametric over the kernel's `limbStore` (the realizer `LeafSpec` is built from
it), and populate it from the two concrete realizers — so instance resolution
finds the (3329, 256, ω = 17) cyclic-transform and the ML-DSA negacyclic
realizations automatically.

A *new* lattice primitive with a concrete realizer of this shape becomes one more
`instance` of `NttEmitRealizes2C`; nothing else changes. -/

/-- **Binary NTT-multiply class over the `.TPolyMod q n` carrier.**  The
    `.TPolyMod`-carrier twin of `KernelRealizes2C`: a registered instance asserts
    the two-polynomial `leaf`-call decodes (over the `.TPolyMod q n` byte
    carrier) to `spec` of the two decoded polynomials.  Used
    for the lattice realizers, whose carrier `.TFp` cannot hold by pigeonhole. -/
class NttEmitRealizes2C (q n : ℕ) [NeZero q] [NeZero n]
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (spec : (Fin n → ZMod q) → (Fin n → ZMod q) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec) : Prop where
  /-- The registered binary `.TPolyMod`-carrier realization. -/
  realizes : ∀ (aVal bVal oldDest : RustVal (.TPolyMod q n)),
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = spec (decode aVal) (decode bVal)

/-- **Transfer for the `.TPolyMod` NTT class.**  Extract the realization equation
    at a point — the `.TPolyMod`-carrier `transferRel` analogue. -/
theorem transferNtt2C {q n : ℕ} [NeZero q] [NeZero n]
    {decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q)}
    {spec : (Fin n → ZMod q) → (Fin n → ZMod q) → (Fin n → ZMod q)}
    {leaf : String} {leafSpec : LeafSpec}
    [h : NttEmitRealizes2C q n decode spec leaf leafSpec]
    (aVal bVal oldDest : RustVal (.TPolyMod q n)) :
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = spec (decode aVal) (decode bVal) :=
  h.realizes aVal bVal oldDest

/-- The cyclic transform at (3329, 256, ω = 17) — registered (closed) instance.
    The realizer `ConcreteNttRealizer.mlkem_nttEmitRealizes_concrete`, which
    computes `nttMul 256 17 = cyclicConv 256` over `ZMod 3329` (multiplication
    modulo `X^256 − 1`, not FIPS 203's transform), is a bare instance of the
    registry — the `bbMulRelated` analogue.  Parametric over the kernel's
    `limbStore`. -/
instance nttMulC (limbStore : LimbStoreSpec) :
    NttEmitRealizes2C 3329 256
      (ConcreteNttRealizer.decodeTPoly (q := 3329) (n := 256) (by rfl))
      (CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric.nttMul 256 (17 : ZMod 3329))
      "ntt_poly_mul_3329_256"
      (ConcreteNttRealizer.cyclicConvLeafSpecP (q := 3329) (n := 256) (by rfl)
        "ntt_poly_mul_3329_256" limbStore) where
  realizes := ConcreteNttRealizer.mlkem_nttEmitRealizes_concrete limbStore

/-- **ML-DSA negacyclic NTT-multiply — registered (closed) instance.**  The
    unconditional negacyclic realizer
    `ConcreteNegacyclicRealizer.mldsa_nttNegaEmitRealizes_concrete` is a bare
    instance of the registry.  Parametric over the kernel's `limbStore`. -/
instance nttNegaMulC (limbStore : LimbStoreSpec) :
    NttEmitRealizes2C 8380417 256
      (ConcreteNegacyclicRealizer.decodeTPoly3 (q := 8380417) (n := 256) (by decide))
      (CatCrypt.Crypto.Optimizer.Lattice.NegacyclicMultiplyCorrect.nttNegaMul
        (1753 : ZMod 8380417))
      "ntt_poly_mul_8380417_256"
      (ConcreteNegacyclicRealizer.negaConvLeafSpecP3 (q := 8380417) (n := 256)
        (1753 : ZMod 8380417) (by decide) "ntt_poly_mul_8380417_256" limbStore) where
  realizes := ConcreteNegacyclicRealizer.mldsa_nttNegaEmitRealizes_concrete limbStore

/-! ## §5  The payoff: instance resolution finds the registered realizations -/

/-- Instance resolution finds the registered (3329, 256, ω = 17)
    cyclic-transform realization with no manual proof — the registry is a
    typeclass database. -/
example (limbStore : LimbStoreSpec) :
    NttEmitRealizes2C 3329 256
      (ConcreteNttRealizer.decodeTPoly (q := 3329) (n := 256) (by rfl))
      (CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric.nttMul 256 (17 : ZMod 3329))
      "ntt_poly_mul_3329_256"
      (ConcreteNttRealizer.cyclicConvLeafSpecP (q := 3329) (n := 256) (by rfl)
        "ntt_poly_mul_3329_256" limbStore) :=
  inferInstance

/-- Instance resolution finds the registered ML-DSA negacyclic realization with no
    manual proof. -/
example (limbStore : LimbStoreSpec) :
    NttEmitRealizes2C 8380417 256
      (ConcreteNegacyclicRealizer.decodeTPoly3 (q := 8380417) (n := 256) (by decide))
      (CatCrypt.Crypto.Optimizer.Lattice.NegacyclicMultiplyCorrect.nttNegaMul
        (1753 : ZMod 8380417))
      "ntt_poly_mul_8380417_256"
      (ConcreteNegacyclicRealizer.negaConvLeafSpecP3 (q := 8380417) (n := 256)
        (1753 : ZMod 8380417) (by decide) "ntt_poly_mul_8380417_256" limbStore) :=
  inferInstance

/-- And the realization equation is extracted from the synthesized instance via
    `transferNtt2C` — the `transferRel` payoff, here for the registered
    (3329, 256, ω = 17) cyclic-transform kernel. -/
example (limbStore : LimbStoreSpec)
    (aVal bVal oldDest : RustVal (.TPolyMod 3329 256)) :
    ConcreteNttRealizer.decodeTPoly (q := 3329) (n := 256) (by rfl)
        ((ConcreteNttRealizer.cyclicConvLeafSpecP (q := 3329) (n := 256) (by rfl)
            "ntt_poly_mul_3329_256" limbStore).call
          "ntt_poly_mul_3329_256" (.TPolyMod 3329 256)
          [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
          [⟨.TPolyMod 3329 256, aVal⟩, ⟨.TPolyMod 3329 256, bVal⟩])
      = CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric.nttMul 256
          (17 : ZMod 3329)
          (ConcreteNttRealizer.decodeTPoly (q := 3329) (n := 256) (by rfl) aVal)
          (ConcreteNttRealizer.decodeTPoly (q := 3329) (n := 256) (by rfl) bVal) :=
  transferNtt2C aVal bVal oldDest

end CatCrypt.Crypto.SecureCompilation.KernelRealizesClass
