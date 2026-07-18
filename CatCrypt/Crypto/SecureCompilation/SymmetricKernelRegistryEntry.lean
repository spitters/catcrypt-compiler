/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
import CatCrypt.Crypto.Jasmin.ChaCha20Block
import CatCrypt.Crypto.Primitives.Poly1305

/-!
# The ChaCha20 block and the Poly1305 step are registry ROWS of the one generic predicate

ChaCha20-Poly1305 (RFC 8439) is the IETF AEAD: ChaCha20 supplies the keystream, Poly1305 the
one-time-key MAC. Both bottom out in a single *unary* pure kernel, so each is a **table row**
of the generic `KernelRealizes` predicate — registering them covers the whole AEAD the
generic/table way, mirroring the Keccak hash row (`HashKernelRegistryEntry`), not a new
mechanism.

Both kernels fit the existing unary
`ProtocolEmitRealizes.KernelRealizes decode spec leaf leafSpec` predicate verbatim:

* **ChaCha20** at `spec := chachaBlock` (the RFC 8439 §2.3 block function,
  `CatCrypt.Crypto.Jasmin.ChaCha20Block.chachaBlock : ChaChaState → ChaChaState`, with
  `ChaChaState = Fin 16 → BitVec 32`). The carrier `C` is `ChaChaState`; `decode` is the
  (univalence-free) transport witness, exactly as for the Barrett / Fermat / Keccak rows.
* **Poly1305** at `spec := fun acc => processBlock r acc block` — the per-block accumulator
  update `acc ↦ ((acc + block) * r) mod (2^130 − 5)` from
  `CatCrypt.Crypto.Primitives.Poly1305.processBlock`, curried over `acc` at a fixed key part
  `r` and message block. The carrier `C` is `Nat` (the field element / accumulator).

For each row:

* `<X>KernelRealizes` is the predicate pinned at the chosen `spec` — and
  `<x>_iff_kernel : <X>KernelRealizes … ↔ KernelRealizes decode <spec> …` is `Iff.rfl`:
  the same generic predicate, pinned, not a fresh seam.
* `transfer<X>Kernel` extracts the realization equation at a point (the `Trocq.transferRel`
  analogue) — the leaf decodes to `<spec>` of its decoded input.
* `<x>TableEntry` builds a `KernelTableEntry C leafSpec`, demonstrating each slots into the
  SAME registry as the NTT / field / reduce / hash rows. Adding a symmetric-cipher primitive
  to the portfolio is therefore one row: a `leaf`, the `spec`, and the realization fact —
  no bespoke per-primitive predicate.

The point is structural and holds for *any* unary `spec`: the generic predicate accepts a
ChaCha20 block and a Poly1305 step just as it accepts a modular reduce or a Keccak permutation.

Both `chachaBlock` (`ChaChaState → ChaChaState`) and Poly1305's `processBlock` (curried to
`Nat → Nat`) are clean pure `def`s; the Vec256/4-way SIMD ChaCha leaves
(`Vale.ChaCha20Vec256`, `Jasmin.Chacha4WayReflect`) are opaque vectorised leaves with no pure
spec, so we register the scalar `chachaBlock` row, not the vectorised ones.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SymmetricKernelRegistryEntry

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Jasmin.ChaCha20Block (ChaChaState chachaBlock)
open CatCrypt.Crypto.Primitives.Poly1305 (processBlock)

/-! ## §1  The ChaCha20 row: the generic predicate at `spec := chachaBlock` -/

/-- **ChaCha20 kernel-realization** — a registry ROW of the unary generic predicate
`ProtocolEmitRealizes.KernelRealizes`, pinned at `spec := chachaBlock` (the RFC 8439 §2.3
ChaCha20 block function). The carrier is `ChaChaState = Fin 16 → BitVec 32`; `decode` is the
transport witness. This is NOT a new mechanism — it is the one generic predicate at the
ChaCha20-block `spec`. -/
def ChaCha20KernelRealizes
    (decode : RustVal .TFp → ChaChaState) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode chachaBlock leaf leafSpec

/-- The ChaCha20 seam is the generic predicate at `spec := chachaBlock` — by `Iff.rfl`,
exactly as `barrett_iff_kernel` / `fermat_iff_kernel` / `hash_iff_kernel`. The seam *name* is
a table entry; the mechanism is one. -/
theorem chacha20_iff_kernel
    (decode : RustVal .TFp → ChaChaState) (leaf : String) (leafSpec : LeafSpec) :
    ChaCha20KernelRealizes decode leaf leafSpec
      ↔ KernelRealizes decode chachaBlock leaf leafSpec := Iff.rfl

/-- Extract the ChaCha20 realization equation at a point — `transferKernel` specialised to the
ChaCha20 row: the emitted leaf, read through `decode`, computes `chachaBlock` of its decoded
input. -/
theorem transferChaCha20Kernel
    {decode : RustVal .TFp → ChaChaState} {leaf : String} {leafSpec : LeafSpec}
    (h : ChaCha20KernelRealizes decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]) = chachaBlock (decode xVal) :=
  transferKernel h xVal oldDest

/-- A `KernelTableEntry ChaChaState leafSpec` for the ChaCha20 block — built from any
realization hypothesis. This demonstrates the ChaCha20 block slots into the SAME
`KernelTableEntry` registry as the NTT / field / reduce / hash rows. -/
def chacha20TableEntry {decode : RustVal .TFp → ChaChaState}
    {leaf : String} {leafSpec : LeafSpec}
    (h : ChaCha20KernelRealizes decode leaf leafSpec) :
    KernelTableEntry ChaChaState leafSpec where
  leaf := leaf
  spec := chachaBlock
  decode := decode
  realized := h

/-- The ChaCha20 table row's realization equation, uniform over the registry via
`KernelTableEntry.realizes`. -/
theorem chacha20TableEntry_realizes
    {decode : RustVal .TFp → ChaChaState} {leaf : String} {leafSpec : LeafSpec}
    (h : ChaCha20KernelRealizes decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (chacha20TableEntry h).decode
        (leafSpec.call (chacha20TableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (chacha20TableEntry h).spec ((chacha20TableEntry h).decode xVal) :=
  (chacha20TableEntry h).realizes xVal oldDest

/-! ## §2  The Poly1305 row: the generic predicate at `spec := processBlock r · block`

The Poly1305 MAC core is a fold of the per-block accumulator update
`acc ↦ ((acc + block) * r) mod (2^130 − 5)`. At a fixed key part `r` and message block, that
update is the unary kernel `fun acc => processBlock r acc block : Nat → Nat`, so it is a row
of the same generic predicate, carrier `C := Nat`. -/

/-- **Poly1305 kernel-realization** — a registry ROW of the unary generic predicate
`ProtocolEmitRealizes.KernelRealizes`, pinned at `spec := fun acc => processBlock r acc block`
(the RFC 8439 §2.5 Poly1305 per-block accumulator update at key part `r` and block `block`).
The carrier is `Nat` (the field accumulator); `decode` is the transport witness. -/
def Poly1305KernelRealizes (r : Nat) (block : List UInt8)
    (decode : RustVal .TFp → Nat) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode (fun acc => processBlock r acc block) leaf leafSpec

/-- The Poly1305 seam is the generic predicate at `spec := fun acc => processBlock r acc block`
— by `Iff.rfl`, exactly as the other rows. -/
theorem poly1305_iff_kernel (r : Nat) (block : List UInt8)
    (decode : RustVal .TFp → Nat) (leaf : String) (leafSpec : LeafSpec) :
    Poly1305KernelRealizes r block decode leaf leafSpec
      ↔ KernelRealizes decode (fun acc => processBlock r acc block) leaf leafSpec := Iff.rfl

/-- Extract the Poly1305 realization equation at a point — `transferKernel` specialised to the
Poly1305 row: the emitted leaf, read through `decode`, computes one accumulator update
`processBlock r · block` of its decoded input. -/
theorem transferPoly1305Kernel {r : Nat} {block : List UInt8}
    {decode : RustVal .TFp → Nat} {leaf : String} {leafSpec : LeafSpec}
    (h : Poly1305KernelRealizes r block decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = processBlock r (decode xVal) block :=
  transferKernel h xVal oldDest

/-- A `KernelTableEntry Nat leafSpec` for the Poly1305 per-block update — built from any
realization hypothesis. This demonstrates the Poly1305 step slots into the SAME
`KernelTableEntry` registry as the NTT / field / reduce / hash / ChaCha20 rows. -/
def poly1305TableEntry {r : Nat} {block : List UInt8} {decode : RustVal .TFp → Nat}
    {leaf : String} {leafSpec : LeafSpec}
    (h : Poly1305KernelRealizes r block decode leaf leafSpec) :
    KernelTableEntry Nat leafSpec where
  leaf := leaf
  spec := fun acc => processBlock r acc block
  decode := decode
  realized := h

/-- The Poly1305 table row's realization equation, uniform over the registry via
`KernelTableEntry.realizes`. -/
theorem poly1305TableEntry_realizes {r : Nat} {block : List UInt8}
    {decode : RustVal .TFp → Nat} {leaf : String} {leafSpec : LeafSpec}
    (h : Poly1305KernelRealizes r block decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (poly1305TableEntry h).decode
        (leafSpec.call (poly1305TableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (poly1305TableEntry h).spec ((poly1305TableEntry h).decode xVal) :=
  (poly1305TableEntry h).realizes xVal oldDest

/-! ## §3  A corollary: the two AEAD rows link like any other row

The ChaCha20 keystream and the Poly1305 step are realized kernels, so they compose through
`link_two`: the registry's sequential-composition law is uniform over the table. Successive
Poly1305 blocks (the MAC fold) chain together, and any unary kernel over the same carrier and
`decode` links with no extra machinery — the same composition the hash / field / NTT rows use. -/
theorem link_poly1305_steps {r : Nat} {block₁ block₂ : List UInt8}
    {decode : RustVal .TFp → Nat} {leaf₁ leaf₂ : String} {leafSpec : LeafSpec}
    (h₁ : Poly1305KernelRealizes r block₁ decode leaf₁ leafSpec)
    (h₂ : Poly1305KernelRealizes r block₂ decode leaf₂ leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf₁ leaf₂ oldDest xVal)
      = processBlock r (processBlock r (decode xVal) block₁) block₂ :=
  link_two h₁ h₂ xVal oldDest

end CatCrypt.Crypto.SecureCompilation.SymmetricKernelRegistryEntry
