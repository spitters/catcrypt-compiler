/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.Hash.Keccak

/-!
# A hash permutation is a registry row of the one generic kernel predicate

Hashes are the most-shared crypto primitive (signatures, KDFs, XOFs, sponges all
bottom out in one permutation/compression), so registering one as a **table row** of
the generic `KernelRealizes` predicate unlocks every hash-based protocol the
generic/table way — a row, not a new mechanism.

A hash permutation is *unary* (`state → state`), so it fits the existing unary
`ProtocolEmitRealizes.KernelRealizes decode spec leaf leafSpec` predicate verbatim, at
`spec := keccak_f steps` (the abstract FIPS-202 Keccak-f[1600] permutation,
`CatCrypt.Crypto.Hash.Keccak.keccak_f`, with its step-mappings `steps` fixed). The
carrier `C` is `KeccakState = BitVec 1600`; `decode : RustVal .TFp → KeccakState` is the
(univalence-free) transport witness, exactly as for the Barrett / Fermat unary rows.

* `HashKernelRealizes` is the predicate at `spec := keccak_f steps` — and
  `hash_iff_kernel : HashKernelRealizes … ↔ KernelRealizes decode (keccak_f steps) …`
  is `Iff.rfl`: this is the same generic predicate, pinned, not a fresh seam.
* `transferHashKernel` extracts the realization equation at a point (the
  `Trocq.transferRel` analogue) — the leaf decodes to `keccak_f steps` of its input.
* `hashTableEntry` builds a `KernelTableEntry KeccakState leafSpec` for the hash,
  demonstrating it slots into the SAME registry as NTT / field / reduce. Adding a hash
  to the portfolio is therefore one row: a `leaf`, the spec `keccak_f steps`, and the
  realization fact — no bespoke per-hash predicate.

The point is structural and holds for *any* `spec`: the generic predicate accepts a hash
permutation just as it accepts a modular reduce. Keccak-f is the cleanest pure permutation
`def` in-repo (`KeccakState → KeccakState` with `steps` fixed); SHA-2 compression would be
another row of the same kind.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashKernelRegistryEntry

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Hash.Keccak

/-! ## §1  The hash row: the generic predicate at `spec := keccak_f steps` -/

/-- **Hash kernel-realization** — a registry ROW of the unary generic predicate
`ProtocolEmitRealizes.KernelRealizes`, pinned at `spec := keccak_f steps` (the abstract
FIPS-202 Keccak-f[1600] permutation with step-mappings `steps` fixed). The carrier is
`KeccakState = BitVec 1600`; `decode` is the transport witness. This is NOT a new
mechanism — it is the one generic predicate at a hash `spec`. -/
def HashKernelRealizes (steps : KeccakStepMappings)
    (decode : RustVal .TFp → KeccakState) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode (keccak_f steps) leaf leafSpec

/-- The hash seam is the generic predicate at `spec := keccak_f steps` — by `Iff.rfl`,
exactly as `barrett_iff_kernel` / `fermat_iff_kernel`. The seam *name* is a table entry;
the mechanism is one. -/
theorem hash_iff_kernel (steps : KeccakStepMappings)
    (decode : RustVal .TFp → KeccakState) (leaf : String) (leafSpec : LeafSpec) :
    HashKernelRealizes steps decode leaf leafSpec
      ↔ KernelRealizes decode (keccak_f steps) leaf leafSpec := Iff.rfl

/-! ## §2  The realization-equation extractor (the `transferRel` analogue) -/

/-- Extract the hash realization equation at a point — `transferKernel` specialised to the
hash row: the emitted leaf, read through `decode`, computes `keccak_f steps` of its decoded
input. -/
theorem transferHashKernel {steps : KeccakStepMappings}
    {decode : RustVal .TFp → KeccakState} {leaf : String} {leafSpec : LeafSpec}
    (h : HashKernelRealizes steps decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]) = keccak_f steps (decode xVal) :=
  transferKernel h xVal oldDest

/-! ## §3  The hash table row in the SAME registry as NTT / field / reduce -/

/-- A `KernelTableEntry KeccakState leafSpec` for the hash permutation — built from any
realization hypothesis. This demonstrates the hash slots into the SAME `KernelTableEntry`
registry as the NTT / field / reduce rows: adding a hash to a protocol's emit set is one
row (`leaf`, `spec := keccak_f steps`, the realization fact), not a bespoke seam. -/
def hashTableEntry {steps : KeccakStepMappings} {decode : RustVal .TFp → KeccakState}
    {leaf : String} {leafSpec : LeafSpec}
    (h : HashKernelRealizes steps decode leaf leafSpec) :
    KernelTableEntry KeccakState leafSpec where
  leaf := leaf
  spec := keccak_f steps
  decode := decode
  realized := h

/-- The hash table row's realization equation, uniform over the registry via
`KernelTableEntry.realizes`. -/
theorem hashTableEntry_realizes {steps : KeccakStepMappings}
    {decode : RustVal .TFp → KeccakState} {leaf : String} {leafSpec : LeafSpec}
    (h : HashKernelRealizes steps decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (hashTableEntry h).decode
        (leafSpec.call (hashTableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (hashTableEntry h).spec ((hashTableEntry h).decode xVal) :=
  (hashTableEntry h).realizes xVal oldDest

/-! ## §4  A corollary: realized hash kernels link like any other row

Two hash kernels (or a hash followed by any other realized unary kernel over the same
carrier and `decode`) compose through `link_two`: the registry's sequential-composition
law is uniform over the table, so hash rows link to NTT / field / reduce rows with no extra
machinery. -/
theorem link_hash_then {steps₁ steps₂ : KeccakStepMappings}
    {decode : RustVal .TFp → KeccakState} {leaf₁ leaf₂ : String} {leafSpec : LeafSpec}
    (h₁ : HashKernelRealizes steps₁ decode leaf₁ leafSpec)
    (h₂ : HashKernelRealizes steps₂ decode leaf₂ leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf₁ leaf₂ oldDest xVal)
      = keccak_f steps₂ (keccak_f steps₁ (decode xVal)) :=
  link_two h₁ h₂ xVal oldDest

end CatCrypt.Crypto.SecureCompilation.HashKernelRegistryEntry
