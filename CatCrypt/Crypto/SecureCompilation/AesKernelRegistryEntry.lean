/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.Primitives.AES128

/-!
# AES block encryption is a registry row of the one generic kernel predicate

AES is the most-shared symmetric primitive (AES-GCM, AEAD constructions, and FAEST's
AES one-way function all bottom out in one block-cipher call), so registering it as a
**table row** of the generic `KernelRealizes` predicate unlocks every AES-based protocol
the generic/table way — a row, not a new mechanism.

AES block encryption at a fixed key is *unary* (`block → block`), so it fits the existing
unary `ProtocolEmitRealizes.KernelRealizes decode spec leaf leafSpec` predicate verbatim,
at `spec := aes128_encrypt key` (the abstract FIPS-197 AES-128 block encryption,
`CatCrypt.Crypto.Primitives.AES128.aes128_encrypt`, with the 128-bit key `key` fixed). The
carrier `C` is `State = Fin 16 → UInt8` (the 16-byte AES block, column-major);
`decode : RustVal .TFp → State` is the (univalence-free) transport witness, exactly as for
the Keccak hash / Barrett / Fermat unary rows.

* `AesKernelRealizes` is the predicate at `spec := aes128_encrypt key` — and
  `aes_iff_kernel : AesKernelRealizes … ↔ KernelRealizes decode (aes128_encrypt key) …`
  is `Iff.rfl`: this is the same generic predicate, pinned, not a fresh seam.
* `transferAesKernel` extracts the realization equation at a point (the
  `Trocq.transferRel` analogue) — the leaf decodes to `aes128_encrypt key` of its input.
* `aesTableEntry` builds a `KernelTableEntry State leafSpec` for the block cipher,
  demonstrating it slots into the SAME registry as NTT / field / reduce / hash. Adding AES
  to the portfolio is therefore one row: a `leaf`, the spec `aes128_encrypt key`, and the
  realization fact — no bespoke per-cipher predicate.

The point is structural and holds for *any* `spec`: the generic predicate accepts a block
cipher just as it accepts a modular reduce or a hash permutation. Fixing the key keeps the
spec the clean unary shape `State → State`; the binary `(key, block) ↦ aes128_encrypt key
block` shape would instead be a `KernelRealizes2` row, but the key-fixed unary form is
cleaner and matches the Keccak hash row, so we register that. AES-256 or the AES round
function (`aesRound`) would be further rows of the same kind.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AesKernelRegistryEntry

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Primitives.AES128

/-! ## §1  The AES row: the generic predicate at `spec := aes128_encrypt key` -/

/-- **AES kernel-realization** — a registry ROW of the unary generic predicate
`ProtocolEmitRealizes.KernelRealizes`, pinned at `spec := aes128_encrypt key` (the abstract
FIPS-197 AES-128 block encryption with the 128-bit key `key` fixed). The carrier is
`State = Fin 16 → UInt8` (the 16-byte block); `decode` is the transport witness. This is
NOT a new mechanism — it is the one generic predicate at an AES `spec`. -/
def AesKernelRealizes (key : Key128)
    (decode : RustVal .TFp → State) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode (aes128_encrypt key) leaf leafSpec

/-- The AES seam is the generic predicate at `spec := aes128_encrypt key` — by `Iff.rfl`,
exactly as `barrett_iff_kernel` / `fermat_iff_kernel` / `hash_iff_kernel`. The seam *name*
is a table entry; the mechanism is one. -/
theorem aes_iff_kernel (key : Key128)
    (decode : RustVal .TFp → State) (leaf : String) (leafSpec : LeafSpec) :
    AesKernelRealizes key decode leaf leafSpec
      ↔ KernelRealizes decode (aes128_encrypt key) leaf leafSpec := Iff.rfl

/-! ## §2  The realization-equation extractor (the `transferRel` analogue) -/

/-- Extract the AES realization equation at a point — `transferKernel` specialised to the
AES row: the emitted leaf, read through `decode`, computes `aes128_encrypt key` of its
decoded input. -/
theorem transferAesKernel {key : Key128}
    {decode : RustVal .TFp → State} {leaf : String} {leafSpec : LeafSpec}
    (h : AesKernelRealizes key decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = aes128_encrypt key (decode xVal) :=
  transferKernel h xVal oldDest

/-! ## §3  The AES table row in the SAME registry as NTT / field / reduce / hash -/

/-- A `KernelTableEntry State leafSpec` for AES block encryption — built from any
realization hypothesis. This demonstrates AES slots into the SAME `KernelTableEntry`
registry as the NTT / field / reduce / hash rows: adding AES to a protocol's emit set is
one row (`leaf`, `spec := aes128_encrypt key`, the realization fact), not a bespoke seam. -/
def aesTableEntry {key : Key128} {decode : RustVal .TFp → State}
    {leaf : String} {leafSpec : LeafSpec}
    (h : AesKernelRealizes key decode leaf leafSpec) :
    KernelTableEntry State leafSpec where
  leaf := leaf
  spec := aes128_encrypt key
  decode := decode
  realized := h

/-- The AES table row's realization equation, uniform over the registry via
`KernelTableEntry.realizes`. -/
theorem aesTableEntry_realizes {key : Key128}
    {decode : RustVal .TFp → State} {leaf : String} {leafSpec : LeafSpec}
    (h : AesKernelRealizes key decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (aesTableEntry h).decode
        (leafSpec.call (aesTableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (aesTableEntry h).spec ((aesTableEntry h).decode xVal) :=
  (aesTableEntry h).realizes xVal oldDest

/-! ## §4  A corollary: realized AES kernels link like any other row

Two AES kernels (or an AES encryption followed by any other realized unary kernel over the
same carrier and `decode`) compose through `link_two`: the registry's sequential-composition
law is uniform over the table, so AES rows link to NTT / field / reduce / hash rows with no
extra machinery. This is the CBC/cascade shape: chained block encryptions over one block
carrier. -/
theorem link_aes_then {key₁ key₂ : Key128}
    {decode : RustVal .TFp → State} {leaf₁ leaf₂ : String} {leafSpec : LeafSpec}
    (h₁ : AesKernelRealizes key₁ decode leaf₁ leafSpec)
    (h₂ : AesKernelRealizes key₂ decode leaf₂ leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf₁ leaf₂ oldDest xVal)
      = aes128_encrypt key₂ (aes128_encrypt key₁ (decode xVal)) :=
  link_two h₁ h₂ xVal oldDest

end CatCrypt.Crypto.SecureCompilation.AesKernelRegistryEntry
