/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
import CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
import CatCrypt.Crypto.SecureCompilation.BarrettReduceEmitValue
import CatCrypt.Crypto.SecureCompilation.FermatInverseEmitValue
import CatCrypt.Crypto.SecureCompilation.MontgomeryMulEmitValue

/-!
# One generic kernel-realization mechanism — the per-primitive seams are a table

This file is the consolidation the "generic / fractalyze-MLIR" direction calls for: a
SINGLE realization predicate, parametric over the carrier `C` and the abstract `spec`,
of which `Barrett` / `Fermat` (unary) and `Montgomery-mul` / `NTT-multiply` (binary) are
**instances obtained by pinning `spec`** — not four separate mechanisms.

The predicate `decode (leafSpec.call leaf args) = spec (decode-of-args)` is exactly the
shape of the Trocq-style proof-transfer engine: it is a `RelatedBinOp.comm` /
`ReprTransfer.BinOpHomOn` square with the **decoding map `decode` as the (map₁, univalence-
free) transport witness** (ParamTransfer's `Transfer.Base.Related`, the dependency imported
by `Bridges/Transfer/CompilerRegistry.lean`; and `Bridges/ReprTransfer.lean`). So:

* `KernelRealizes` (unary, from `ProtocolEmitRealizes`) and `KernelRealizes2` (binary, here)
  are the two generic predicates.
* `transferKernel` / `transferKernel2` extract the realization equation at a point — the
  analogue of Trocq's `transferRel`.
* the per-primitive seams reduce to these by `Iff.rfl` (`barrett_iff_kernel`,
  `fermat_iff_kernel`, `ntt_iff_kernel2`, `montMul_iff_kernel2`) — the seam *names* are
  table entries, the mechanism is one.
* `KernelTableEntry` + `nttArith` table give the registry shape; sequential kernel linking
  is `ProtocolEmitRealizes.pipeN_realizes` (`spec`s compose to `composeSpecs`).

Adding a primitive = a table row (a `leaf`, a `spec`, and its commuting-square discharge),
never a new predicate. This is the fractalyze `!field.pf<p>`-style table over one transport.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GenericKernelRealization

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
open CatCrypt.Crypto.SecureCompilation.BarrettReduceEmitValue
open CatCrypt.Crypto.SecureCompilation.FermatInverseEmitValue
open CatCrypt.Crypto.SecureCompilation.MontgomeryMulEmitValue
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.FermatInverseGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryMulGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric

/-! ## §1  The binary generic predicate (the unary `KernelRealizes` is upstream) -/

/-- **Binary generic kernel-realization** — the binary twin of
`ProtocolEmitRealizes.KernelRealizes`: the leaf, applied to two `.TFp` operands and read
through `decode`, computes `spec` of the decoded operands. Carrier-generic in `C`,
spec-generic in `spec`. (`ReprTransfer.BinOpHomOn` along `decode`, the Trocq map-level
transport square.) -/
def KernelRealizes2 {C : Type*} (decode : RustVal .TFp → C) (spec : C → C → C)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = spec (decode aVal) (decode bVal)

/-- Extract the realization equation at a point — the `Trocq.transferRel` analogue
(unary). -/
theorem transferKernel {C : Type*} {decode : RustVal .TFp → C} {spec : C → C}
    {leaf : String} {leafSpec : LeafSpec} (h : KernelRealizes decode spec leaf leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]) = spec (decode xVal) :=
  h xVal oldDest

/-- Extract the binary realization equation at a point — the `Trocq.transferRel`
analogue (binary). -/
theorem transferKernel2 {C : Type*} {decode : RustVal .TFp → C} {spec : C → C → C}
    {leaf : String} {leafSpec : LeafSpec} (h : KernelRealizes2 decode spec leaf leafSpec)
    (aVal bVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = spec (decode aVal) (decode bVal) :=
  h aVal bVal oldDest

/-! ## §2  The per-primitive seams ARE instances (each by `Iff.rfl`) -/

/-- The Barrett reduce seam is the generic predicate at `spec := (· % q)`. -/
theorem barrett_iff_kernel (q k : ℕ) (decode : RustVal .TFp → ℕ)
    (leaf : String) (leafSpec : LeafSpec) :
    BarrettEmitRealizes q k decode leaf leafSpec
      ↔ KernelRealizes decode (· % q) leaf leafSpec := Iff.rfl

/-- The Fermat constant-time-inverse seam is the generic predicate at
`spec := fermatInv p`. -/
theorem fermat_iff_kernel (p : ℕ) [Fact p.Prime] (decode : RustVal .TFp → ZMod p)
    (leaf : String) (leafSpec : LeafSpec) :
    FermatInvEmitRealizes p decode leaf leafSpec
      ↔ KernelRealizes decode (fermatInv p) leaf leafSpec := Iff.rfl

/-- The NTT-multiply seam is the binary generic predicate at `spec := nttMul n ω`. -/
theorem ntt_iff_kernel2 {R : Type*} [Field R] (n : ℕ) (ω : R)
    (decode : RustVal .TFp → (Fin n → R)) (leaf : String) (leafSpec : LeafSpec) :
    NttEmitRealizes n ω decode leaf leafSpec
      ↔ KernelRealizes2 decode (nttMul n ω) leaf leafSpec := Iff.rfl

/-- The Montgomery-multiply seam is the binary generic predicate at
`spec := montMul N R N'`. -/
theorem montMul_iff_kernel2 (N R N' : ℤ) (decode : RustVal .TFp → ℤ)
    (leaf : String) (leafSpec : LeafSpec) :
    MontMulEmitRealizes N R N' decode leaf leafSpec
      ↔ KernelRealizes2 decode (montMul N R N') leaf leafSpec := Iff.rfl

/-! ## §3  The registry table

A `KernelTableEntry` is one row: a leaf name and the abstract spec it realizes (the
carrier `C` and the realizing `leafSpec` are the row's parameters). A protocol's emit set
is a *list* of such rows; per-protocol emit becomes: list the rows, cite each row's
realization (`KernelRealizes`/`KernelRealizes2`), compose via `pipeN_realizes`. No new
predicate per primitive — the fractalyze table-over-one-transport. -/
structure KernelTableEntry (C : Type*) (leafSpec : LeafSpec) where
  /-- The emitted leaf's name (e.g. `"ntt_poly_mul_3329_256"`). -/
  leaf : String
  /-- The unary abstract spec this leaf realizes through `decode`. -/
  spec : C → C
  /-- `decode` is the transport witness. -/
  decode : RustVal .TFp → C
  /-- The realization fact (its commuting-square discharge lives at the call site). -/
  realized : KernelRealizes decode spec leaf leafSpec

/-- The realization equation for any table row — uniform over the table, by
`transferKernel`. -/
theorem KernelTableEntry.realizes {C : Type*} {leafSpec : LeafSpec}
    (e : KernelTableEntry C leafSpec) (xVal oldDest : RustVal .TFp) :
    e.decode (leafSpec.call e.leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = e.spec (e.decode xVal) :=
  transferKernel e.realized xVal oldDest

/-! ## §4  Kernel linking is the upstream composition

Sequential composition of realized kernels is `ProtocolEmitRealizes.pipe2_realizes`
(`spec2 ∘ spec1`) and `pipeN_realizes` (`composeSpecs`). Re-exported here as the
table-level linking law so the registry + the composition live together. -/
theorem link_two {C : Type*} {decode : RustVal .TFp → C} {spec1 spec2 : C → C}
    {leaf1 leaf2 : String} {leafSpec : LeafSpec}
    (h1 : KernelRealizes decode spec1 leaf1 leafSpec)
    (h2 : KernelRealizes decode spec2 leaf2 leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf1 leaf2 oldDest xVal) = spec2 (spec1 (decode xVal)) :=
  pipe2_realizes decode spec1 spec2 leaf1 leaf2 leafSpec h1 h2 xVal oldDest

end CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
