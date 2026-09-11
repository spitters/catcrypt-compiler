/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.SecureCompilation.KernelRealizesClass

/-!
# Field add/mul are rows of the one generic kernel-realization registry

`GenericKernelRealization.lean` folds the per-primitive emit→value seams —
NTT-multiply, Barrett reduce, Fermat inverse, Montgomery mul — into ONE generic
predicate `KernelRealizes2` (binary) / `KernelRealizes` (unary), of which each
primitive is an instance obtained by pinning the abstract `spec` (the
`*_iff_kernel2` / `*_iff_kernel` seams, each `Iff.rfl`).

The **original** generic emit→value bridge, `GenericFieldEmitValue.lean`, was
built *before* that consolidation: it carries its own field-agnostic
realization predicate `FieldEmitRealizes q decode op leaf leafSpec`, generic
over the field binop `op : ZMod q → ZMod q → ZMod q` so that *both* the curve
add commuting square (`c25519_add_commutes` & siblings) and the mul commuting
square are instances. This file folds that predicate into the unified registry,
completing the consolidation:

* `field_iff_kernel2` shows `FieldEmitRealizes` is **definitionally** the binary
  generic predicate `KernelRealizes2` at carrier `C := ZMod q` and `spec := op`
  — so field arithmetic is not a separate mechanism, it is one more row of the
  same `KernelRealizes2` table that NTT/Barrett/Fermat/Montgomery populate.
* `field_add_iff_kernel2` / `field_mul_iff_kernel2` are the two field-op rows:
  the same seam pinned at `op := (· + ·)` and `op := (· * ·)` (the `ZMod q` ring
  ops). They are the field add / field mul registry entries — the `bbAddRelated`
  / `bbMulRelated` analogues at the row level.

## What is a bare instance and what is not (the honesty boundary)

Exactly as for the other `.TFp` seams (`barrett_iff_kernel`, `ntt_iff_kernel2`,
…), the field-op realization is **not** registered as a bare `KernelRealizes2C`
instance. The only field-op realizer available is
`GenericFieldEmitValue.fieldEmitRealizes_canonical`, which is **conditional**:
it needs a decoder section `hsection : ∀ z, decode (encode z) = z` (the
`encode`/`decode` round-trip that the per-curve commuting square + AUCurves
field-op correctness discharge outside Lean). A `RelatedBinOp` whose commuting
square is still an open round-trip is not registered bare — so we expose the
conditional realizer as a *lemma* (`field_KernelRealizes2C_of_section`) that
yields the class instance once a caller supplies the section, mirroring the
documented boundary in `KernelRealizesClass.lean §"What is a bare instance"`.

## The consolidation is complete

With this file, every emit→realization bridge in the registry — field add, field
mul, NTT-multiply, Barrett reduce, Fermat inverse, Montgomery mul — is an
instance of the **one** generic predicate `KernelRealizes2` (or its unary twin
`KernelRealizes`), connected by `Iff.rfl`. Adding a primitive is a table row, not
a new mechanism.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldOpRegistryEntry

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.KernelRealizesClass

/-! ## §1  Field arithmetic IS the binary generic predicate (by `Iff.rfl`)

`FieldEmitRealizes q decode op leaf leafSpec` and
`KernelRealizes2 (C := ZMod q) decode op leaf leafSpec` have the *same body* —
`∀ aVal bVal oldDest, decode (leafSpec.call leaf .TFp [.TFp,.TFp] oldDest
[⟨.TFp,aVal⟩,⟨.TFp,bVal⟩]) = op (decode aVal) (decode bVal)` — modulo the
abstract-binop argument name (`op` vs `spec`). So the original field bridge's
predicate is *definitionally* a row of the unified registry. -/

/-- **The field-op seam IS the binary generic kernel predicate.**  The original
    `FieldEmitRealizes` (the curve-generic emit→value bridge over `ZMod q`) is
    definitionally the binary generic `KernelRealizes2` at carrier `C := ZMod q`
    and `spec := op`.  Field arithmetic is therefore one more row of the same
    `KernelRealizes2` table that NTT/Barrett/Fermat/Montgomery populate — not a
    separate mechanism. -/
theorem field_iff_kernel2 (q : ℕ) (decode : RustVal .TFp → ZMod q)
    (op : ZMod q → ZMod q → ZMod q) (leaf : String) (leafSpec : LeafSpec) :
    FieldEmitRealizes q decode op leaf leafSpec
      ↔ KernelRealizes2 decode op leaf leafSpec := Iff.rfl

/-! ## §2  The two field-op rows: ADD and MUL

The field add / field mul registry entries are the same seam pinned at the two
`ZMod q` ring operations — the `bbAddRelated` / `bbMulRelated` analogues. -/

/-- **Field-ADD registry row.**  The field add commuting square
    (`c25519_add_commutes` & siblings) is the binary generic predicate at
    `spec := (· + ·)` over `ZMod q`. -/
theorem field_add_iff_kernel2 (q : ℕ) (decode : RustVal .TFp → ZMod q)
    (leaf : String) (leafSpec : LeafSpec) :
    FieldEmitRealizes q decode (· + ·) leaf leafSpec
      ↔ KernelRealizes2 decode (· + ·) leaf leafSpec := Iff.rfl

/-- **Field-MUL registry row.**  The field mul commuting square is the binary
    generic predicate at `spec := (· * ·)` over `ZMod q`. -/
theorem field_mul_iff_kernel2 (q : ℕ) (decode : RustVal .TFp → ZMod q)
    (leaf : String) (leafSpec : LeafSpec) :
    FieldEmitRealizes q decode (· * ·) leaf leafSpec
      ↔ KernelRealizes2 decode (· * ·) leaf leafSpec := Iff.rfl

/-! ## §3  The conditional realizer → registry class (not a bare instance)

The only field-op realizer is `fieldEmitRealizes_canonical`, which needs a
decoder section `hsection`.  As with the other `.TFp` seams, we therefore do not
register a bare `KernelRealizes2C` instance; instead we expose the conditional
realizer as a lemma producing the class once a caller supplies the section. -/

/-- **The conditional field-op registry class.**  Given a decoder section
    `hsection : ∀ z, decode (encode z) = z`, the canonical field-op realizer
    built from `fieldBinopCallSpec` populates the binary kernel class
    `KernelRealizes2C` at `spec := op` over `ZMod q` — i.e. it becomes a (section-
    conditional) row of the typeclass registry.  This is the honest boundary: the
    section is the cross-prover residual (`encode`/`decode` round-trip), exactly
    as the other `.TFp` seams remain conditional on their concrete-realizer KAT.
    -/
theorem field_KernelRealizes2C_of_section (q : ℕ) (decode : RustVal .TFp → ZMod q)
    (op : ZMod q → ZMod q → ZMod q) (encode : ZMod q → RustVal .TFp)
    (hsection : ∀ z : ZMod q, decode (encode z) = z)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2C decode op leaf
      { call := fieldBinopCallSpec q decode op encode leaf, limbStore := limbStore } :=
  ⟨(field_iff_kernel2 q decode op leaf _).mp
    (fieldEmitRealizes_canonical q decode op encode hsection leaf limbStore)⟩

/-! ## §4  Payoff: the field rows resolve through the unified transfer extractor

Once the section-conditional class is in scope, the field-op realization equation
is extracted by the *same* `transferKernel2C` the lattice rows use — one transfer
mechanism over the whole registry, field arithmetic included. -/

/-- The field-op realization equation, extracted through the unified
    `transferKernel2C` from the section-conditional registry class — the same
    extractor the NTT / Montgomery rows use, now applied to a field-op row. -/
theorem field_transfer_of_section (q : ℕ) (decode : RustVal .TFp → ZMod q)
    (op : ZMod q → ZMod q → ZMod q) (encode : ZMod q → RustVal .TFp)
    (hsection : ∀ z : ZMod q, decode (encode z) = z)
    (leaf : String) (limbStore : LimbStoreSpec)
    (aVal bVal oldDest : RustVal .TFp) :
    decode
        (({ call := fieldBinopCallSpec q decode op encode leaf,
            limbStore := limbStore } : LeafSpec).call
          leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = op (decode aVal) (decode bVal) :=
  letI : KernelRealizes2C decode op leaf
      { call := fieldBinopCallSpec q decode op encode leaf, limbStore := limbStore } :=
    field_KernelRealizes2C_of_section q decode op encode hsection leaf limbStore
  transferKernel2C aVal bVal oldDest

end CatCrypt.Crypto.SecureCompilation.FieldOpRegistryEntry
