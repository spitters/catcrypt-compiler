/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.Primitives.HMAC
public import CatCrypt.Crypto.Primitives.SHAKE128

/-!
# HMAC and SHA-3/SHAKE are registry rows of the one generic kernel predicate

Keyed-hash (HMAC) and the SHA-3/SHAKE extendable-output functions are the workhorses of
KDF/MAC/XOF-based protocols (HKDF, HMAC-DRBG, the SLH-DSA hash chains, SHAKE-seeded PQC),
so registering them as **table rows** of the generic `KernelRealizes` predicate unlocks
every HMAC/HKDF/SHAKE-based protocol the generic/table way — a row, not a new mechanism.
These slot into the SAME `KernelTableEntry` registry as the NTT / field / reduce / hash
rows; the mechanism is one transport, the seam names are table entries.

Two rows, of the two shapes the registry already supports:

* **HMAC is *binary*** (`key → msg → tag`), so it fits the binary generic predicate
  `GenericKernelRealization.KernelRealizes2` verbatim, at `spec := hmacSha256`
  (the RFC-2104 keyed hash, `CatCrypt.Crypto.Primitives.HMAC.hmacSha256`). The carrier
  `C` is `List UInt8` (a byte string); `decode : RustVal .TFp → List UInt8` is the
  (univalence-free) transport witness, exactly as for the NTT / Montgomery binary rows.
* **SHAKE is *unary*** (`msg → digest`), so it fits the unary generic predicate
  `ProtocolEmitRealizes.KernelRealizes` verbatim, at `spec := shake128_32`
  (SHAKE-128 with a fixed 32-byte digest, `CatCrypt.Crypto.Primitives.SHAKE128.shake128_32`,
  the seed-derivation shape used by SLH-DSA). The carrier is again `List UInt8`.

For each row:

* `*KernelRealizes(2)` is the predicate at the pinned `spec` — and `*_iff_kernel(2)` is
  `Iff.rfl`: the same generic predicate, pinned, not a fresh seam.
* `transfer*Kernel(2)` extracts the realization equation at a point (the
  `Trocq.transferRel` analogue).
* `*TableEntry` builds a `KernelTableEntry … leafSpec` (SHAKE row, unary), demonstrating it
  slots into the SAME registry as NTT / field / reduce / hash. Adding a keyed-hash or XOF to
  a protocol's emit set is therefore one row: a `leaf`, the spec, and the realization fact —
  no bespoke per-primitive predicate.

The point is structural and holds for *any* `spec`: the generic predicate accepts a keyed
hash and an XOF just as it accepts a modular reduce. `hmacSha256` / `shake128_32` are the
cleanest pure keyed-hash / XOF `def`s in-repo; SHA3-256 (`Keccak.sha3_256_params`-driven)
would be another unary row of the same kind once its pure `msg → digest` `def` is exposed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HmacKernelRegistryEntry

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Primitives.HMAC
open CatCrypt.Crypto.Primitives.SHAKE128

/-! ## §1  The HMAC row: the binary generic predicate at `spec := hmacSha256` -/

/-- **HMAC kernel-realization** — a registry ROW of the *binary* generic predicate
`GenericKernelRealization.KernelRealizes2`, pinned at `spec := hmacSha256` (the RFC-2104
keyed hash `key → msg → tag`). The carrier is `List UInt8` (a byte string);
`decode` is the transport witness. This is NOT a new mechanism — it is the one binary
generic predicate at a keyed-hash `spec`. -/
def HmacKernelRealizes (decode : RustVal .TFp → List UInt8)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes2 decode hmacSha256 leaf leafSpec

/-- The HMAC seam is the binary generic predicate at `spec := hmacSha256` — by `Iff.rfl`,
exactly as `ntt_iff_kernel2` / `montMul_iff_kernel2`. The seam *name* is a table entry; the
mechanism is one. -/
theorem hmac_iff_kernel2 (decode : RustVal .TFp → List UInt8)
    (leaf : String) (leafSpec : LeafSpec) :
    HmacKernelRealizes decode leaf leafSpec
      ↔ KernelRealizes2 decode hmacSha256 leaf leafSpec := Iff.rfl

/-- Extract the HMAC realization equation at a point — `transferKernel2` specialised to the
HMAC row: the emitted leaf, read through `decode`, computes `hmacSha256` of its decoded key
and message operands. -/
theorem transferHmacKernel {decode : RustVal .TFp → List UInt8}
    {leaf : String} {leafSpec : LeafSpec}
    (h : HmacKernelRealizes decode leaf leafSpec) (keyVal msgVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, keyVal⟩, ⟨.TFp, msgVal⟩])
      = hmacSha256 (decode keyVal) (decode msgVal) :=
  transferKernel2 h keyVal msgVal oldDest

/-! ## §2  The SHAKE row: the unary generic predicate at `spec := shake128_32` -/

/-- **SHAKE kernel-realization** — a registry ROW of the *unary* generic predicate
`ProtocolEmitRealizes.KernelRealizes`, pinned at `spec := shake128_32` (SHAKE-128 with a
fixed 32-byte digest, the `msg → digest` seed-derivation shape). The carrier is
`List UInt8`; `decode` is the transport witness. This is NOT a new mechanism — it is the one
unary generic predicate at an XOF `spec`. -/
def ShakeKernelRealizes (decode : RustVal .TFp → List UInt8)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode shake128_32 leaf leafSpec

/-- The SHAKE seam is the unary generic predicate at `spec := shake128_32` — by `Iff.rfl`,
exactly as `barrett_iff_kernel` / `fermat_iff_kernel`. -/
theorem shake_iff_kernel (decode : RustVal .TFp → List UInt8)
    (leaf : String) (leafSpec : LeafSpec) :
    ShakeKernelRealizes decode leaf leafSpec
      ↔ KernelRealizes decode shake128_32 leaf leafSpec := Iff.rfl

/-- Extract the SHAKE realization equation at a point — `transferKernel` specialised to the
SHAKE row: the emitted leaf, read through `decode`, computes `shake128_32` of its decoded
input. -/
theorem transferShakeKernel {decode : RustVal .TFp → List UInt8}
    {leaf : String} {leafSpec : LeafSpec}
    (h : ShakeKernelRealizes decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]) = shake128_32 (decode xVal) :=
  transferKernel h xVal oldDest

/-! ## §3  The SHAKE table row in the SAME registry as NTT / field / reduce / hash -/

/-- A `KernelTableEntry (List UInt8) leafSpec` for the SHAKE XOF — built from any
realization hypothesis. This demonstrates the XOF slots into the SAME `KernelTableEntry`
registry (unary) as the NTT / field / reduce / hash rows: adding an XOF to a protocol's emit
set is one row (`leaf`, `spec := shake128_32`, the realization fact), not a bespoke seam.
(HMAC, being binary, is a `KernelRealizes2` row; the unary `KernelTableEntry` registry holds
the unary rows.) -/
def shakeTableEntry {decode : RustVal .TFp → List UInt8}
    {leaf : String} {leafSpec : LeafSpec}
    (h : ShakeKernelRealizes decode leaf leafSpec) :
    KernelTableEntry (List UInt8) leafSpec where
  leaf := leaf
  spec := shake128_32
  decode := decode
  realized := h

/-- The SHAKE table row's realization equation, uniform over the registry via
`KernelTableEntry.realizes`. -/
theorem shakeTableEntry_realizes {decode : RustVal .TFp → List UInt8}
    {leaf : String} {leafSpec : LeafSpec}
    (h : ShakeKernelRealizes decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (shakeTableEntry h).decode
        (leafSpec.call (shakeTableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (shakeTableEntry h).spec ((shakeTableEntry h).decode xVal) :=
  (shakeTableEntry h).realizes xVal oldDest

/-! ## §4  A corollary: realized SHAKE kernels link like any other row

A SHAKE kernel followed by any other realized unary kernel over the same carrier and
`decode` composes through `link_two`: the registry's sequential-composition law is uniform
over the table, so XOF rows link to NTT / field / reduce / hash rows with no extra
machinery. -/
theorem link_shake_then {decode : RustVal .TFp → List UInt8}
    {spec₂ : List UInt8 → List UInt8} {leaf₁ leaf₂ : String} {leafSpec : LeafSpec}
    (h₁ : ShakeKernelRealizes decode leaf₁ leafSpec)
    (h₂ : KernelRealizes decode spec₂ leaf₂ leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf₁ leaf₂ oldDest xVal)
      = spec₂ (shake128_32 (decode xVal)) :=
  link_two h₁ h₂ xVal oldDest

end CatCrypt.Crypto.SecureCompilation.HmacKernelRegistryEntry
