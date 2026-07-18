/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
import CatCrypt.Crypto.Primitives.SHA256

/-!
# SHA-256 compression is a registry row of the one generic kernel predicate

SHA-2 is the most-shared crypto primitive after a permutation (HMAC, HKDF,
RSA/ECDSA hashing, X.509, TLS transcripts all bottom out in the SHA-256
compression function), so registering it as a **table row** of the generic
`KernelRealizes` predicate unlocks every SHA-2-based protocol the generic/table
way — a row, not a new mechanism.

The SHA-256 compression function is `compress : State256 → (Fin 64 → UInt8) →
State256` (`CatCrypt.Crypto.Primitives.SHA256.compress`): a 64-byte block drives
the 8-word state to its successor state. Fixing the block argument yields a
*unary* per-block step `compress · block : State256 → State256`, which fits the
existing unary `ProtocolEmitRealizes.KernelRealizes decode spec leaf leafSpec`
predicate verbatim, at `spec := fun s => compress s block` — exactly as the
Keccak row fixes `steps` in `keccak_f steps`. The carrier `C` is
`State256 = Fin 8 → UInt32`; `decode : RustVal .TFp → State256` is the
(univalence-free) transport witness, exactly as for the Barrett / Fermat /
hash unary rows.

* `Sha256KernelRealizes` is the predicate at `spec := fun s => compress s block`
  — and `sha256_iff_kernel : Sha256KernelRealizes … ↔ KernelRealizes decode
  (fun s => compress s block) …` is `Iff.rfl`: this is the same generic
  predicate, pinned, not a fresh seam.
* `transferSha256Kernel` extracts the realization equation at a point (the
  `Trocq.transferRel` analogue) — the leaf decodes to `compress · block` of its
  input state.
* `sha256TableEntry` builds a `KernelTableEntry State256 leafSpec` for the
  compression step, demonstrating it slots into the SAME registry as NTT /
  field / reduce / hash. Adding SHA-256 to the portfolio is therefore one row:
  a `leaf`, the spec `fun s => compress s block`, and the realization fact — no
  bespoke per-hash predicate.

The point is structural and holds for *any* `spec`: the generic predicate
accepts a SHA-2 compression step just as it accepts a modular reduce. The block
argument is a parameter of the row (as `steps` is for the Keccak row), so a
multi-block hash is a `link`-composed chain of compression rows over the same
carrier and `decode` — see `link_sha256_then`. This covers SHA-2-based
protocols (HMAC, HKDF, signatures) the generic way.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Sha256KernelRegistryEntry

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Primitives.SHA256

/-! ## §1  The SHA-256 row: the generic predicate at `spec := compress · block` -/

/-- **SHA-256 kernel-realization** — a registry ROW of the unary generic
predicate `ProtocolEmitRealizes.KernelRealizes`, pinned at
`spec := fun s => compress s block` (the FIPS 180-4 SHA-256 compression function
with the 64-byte `block` fixed). The carrier is `State256 = Fin 8 → UInt32`;
`decode` is the transport witness. This is NOT a new mechanism — it is the one
generic predicate at a SHA-256 `spec`. -/
def Sha256KernelRealizes (block : Fin 64 → UInt8)
    (decode : RustVal .TFp → State256) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode (fun s => compress s block) leaf leafSpec

/-- The SHA-256 seam is the generic predicate at `spec := fun s => compress s block`
— by `Iff.rfl`, exactly as `barrett_iff_kernel` / `fermat_iff_kernel` /
`hash_iff_kernel`. The seam *name* is a table entry; the mechanism is one. -/
theorem sha256_iff_kernel (block : Fin 64 → UInt8)
    (decode : RustVal .TFp → State256) (leaf : String) (leafSpec : LeafSpec) :
    Sha256KernelRealizes block decode leaf leafSpec
      ↔ KernelRealizes decode (fun s => compress s block) leaf leafSpec := Iff.rfl

/-! ## §2  The realization-equation extractor (the `transferRel` analogue) -/

/-- Extract the SHA-256 realization equation at a point — `transferKernel`
specialised to the SHA-256 row: the emitted leaf, read through `decode`, computes
`compress · block` of its decoded input state. -/
theorem transferSha256Kernel {block : Fin 64 → UInt8}
    {decode : RustVal .TFp → State256} {leaf : String} {leafSpec : LeafSpec}
    (h : Sha256KernelRealizes block decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]) = compress (decode xVal) block :=
  transferKernel h xVal oldDest

/-! ## §3  The SHA-256 table row in the SAME registry as NTT / field / reduce / hash -/

/-- A `KernelTableEntry State256 leafSpec` for the SHA-256 compression step —
built from any realization hypothesis. This demonstrates the compression step
slots into the SAME `KernelTableEntry` registry as the NTT / field / reduce /
hash rows: adding SHA-256 to a protocol's emit set is one row
(`leaf`, `spec := fun s => compress s block`, the realization fact), not a
bespoke seam. -/
def sha256TableEntry {block : Fin 64 → UInt8} {decode : RustVal .TFp → State256}
    {leaf : String} {leafSpec : LeafSpec}
    (h : Sha256KernelRealizes block decode leaf leafSpec) :
    KernelTableEntry State256 leafSpec where
  leaf := leaf
  spec := fun s => compress s block
  decode := decode
  realized := h

/-- The SHA-256 table row's realization equation, uniform over the registry via
`KernelTableEntry.realizes`. -/
theorem sha256TableEntry_realizes {block : Fin 64 → UInt8}
    {decode : RustVal .TFp → State256} {leaf : String} {leafSpec : LeafSpec}
    (h : Sha256KernelRealizes block decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (sha256TableEntry h).decode
        (leafSpec.call (sha256TableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (sha256TableEntry h).spec ((sha256TableEntry h).decode xVal) :=
  (sha256TableEntry h).realizes xVal oldDest

/-! ## §4  A corollary: realized SHA-256 kernels link like any other row

Two SHA-256 compression kernels (one per block — the natural shape of a
multi-block hash), or a compression step followed by any other realized unary
kernel over the same carrier and `decode`, compose through `link_two`: the
registry's sequential-composition law is uniform over the table, so SHA-256 rows
link to NTT / field / reduce / hash rows with no extra machinery. -/
theorem link_sha256_then {block₁ block₂ : Fin 64 → UInt8}
    {decode : RustVal .TFp → State256} {leaf₁ leaf₂ : String} {leafSpec : LeafSpec}
    (h₁ : Sha256KernelRealizes block₁ decode leaf₁ leafSpec)
    (h₂ : Sha256KernelRealizes block₂ decode leaf₂ leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf₁ leaf₂ oldDest xVal)
      = compress (compress (decode xVal) block₁) block₂ :=
  link_two h₁ h₂ xVal oldDest

end CatCrypt.Crypto.SecureCompilation.Sha256KernelRegistryEntry
