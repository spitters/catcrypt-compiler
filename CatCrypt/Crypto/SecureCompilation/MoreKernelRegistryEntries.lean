/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
public import CatCrypt.Crypto.Primitives.GF128
public import CatCrypt.Crypto.Hash.Poseidon2.BabyBear
public import CatCrypt.Crypto.KeyAgreement.MontgomeryLadder

/-!
# More primitive families as registry rows of the one generic kernel predicate

This file broadens the kernel-realization registry with several MORE primitive
families, each a **table row** of the single generic `KernelRealizes` /
`KernelRealizes2` predicate (`GenericKernelRealization`), pinned at a pure
abstract `spec`. As for the hash / SHA-256 / HMAC rows, each is the *same*
mechanism at a fresh `spec` — a row, not a new seam. Every `*_iff_kernel(2)` is
`Iff.rfl`; every `transfer*Kernel(2)` is the `Trocq.transferRel` analogue.

Four families, of the two shapes the registry already supports:

* **GF(2^128) multiplication is *binary*** (`a → b → a·b` in GF(2^128)), the
  GHASH core of AES-GCM (NIST SP 800-38D, Algorithm 1). It fits the binary
  generic predicate `KernelRealizes2` verbatim, at `spec := gf128_mul`
  (`CatCrypt.Crypto.Primitives.GF128.gf128_mul`). The carrier `C` is
  `BitVec 128`; `decode` is the (univalence-free) transport witness.
* **The Poseidon2 permutation is *unary*** (`state → state`), the ZK-hash
  workhorse (Plonky3 Merkle trees, FRI). It fits the unary generic predicate
  `KernelRealizes` verbatim, at `spec := poseidon2BabyBearPermute`
  (`CatCrypt.Crypto.Hash.Poseidon2.BabyBear.poseidon2BabyBearPermute`), with the
  carrier `C = Fin width → F` (`F = ZMod babyBearPrime`, `width = 16`) fixed.
* **Poseidon2 2-to-1 compression is *binary*** (`left → right → digest`), the
  Merkle-node compressor. It fits `KernelRealizes2`, at
  `spec := poseidon2BabyBearCompress`, carrier `C = F`.
* **The Montgomery-ladder step is *unary*** (`(R₀,R₁) → (R₀',R₁')`) once the
  scalar bit is fixed (`CatCrypt.Crypto.ECC.ladderStep · b`), the x-only scalar
  multiplication core (Curve25519). It fits `KernelRealizes`, parametric over the
  group `G` and the fixed bit `b`, at `spec := fun st => ladderStep st b`,
  carrier `C = G × G`.

For each row:

* `*KernelRealizes(2)` is the predicate at the pinned `spec` — and
  `*_iff_kernel(2)` is `Iff.rfl`: the same generic predicate, pinned, not a fresh
  seam.
* `transfer*Kernel(2)` extracts the realization equation at a point (the
  `Trocq.transferRel` analogue).
* for the unary rows, `*TableEntry` builds a `KernelTableEntry … leafSpec`
  (slotting into the SAME registry as NTT / field / reduce / hash / SHA-256 /
  SHAKE), and `link_*_then` shows the row composes with any other unary row over
  the same carrier and `decode` through `link_two`.

The point is structural and holds for *any* `spec`: the generic predicate accepts
a GF(2^128) multiply, a ZK-hash permutation, and a ladder step just as it accepts
a modular reduce. These are the cleanest pure `def`s in-repo for each family;
adding a primitive to a protocol's emit set is one row — a `leaf`, the `spec`, and
the realization fact.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MoreKernelRegistryEntries

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Primitives.GF128
open CatCrypt.Crypto.Hash.Poseidon2.BabyBear
open CatCrypt.Crypto.ECC

/-! ## §1  The GF(2^128)-multiply row: the binary generic predicate at `spec := gf128_mul`

GHASH's GF(2^128) product (AES-GCM, NIST SP 800-38D) is *binary*, so it is a
`KernelRealizes2` row over the carrier `BitVec 128`. -/

/-- **GF(2^128)-multiply kernel-realization** — a registry ROW of the *binary*
generic predicate `GenericKernelRealization.KernelRealizes2`, pinned at
`spec := gf128_mul` (the GHASH GF(2^128) product). The carrier is `BitVec 128`;
`decode` is the transport witness. This is NOT a new mechanism — it is the one
binary generic predicate at a GF(2^128) `spec`. -/
def Gf128MulKernelRealizes (decode : RustVal .TFp → BitVec 128)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes2 decode gf128_mul leaf leafSpec

/-- The GF(2^128)-multiply seam is the binary generic predicate at
`spec := gf128_mul` — by `Iff.rfl`, exactly as `ntt_iff_kernel2` /
`montMul_iff_kernel2`. -/
theorem gf128Mul_iff_kernel2 (decode : RustVal .TFp → BitVec 128)
    (leaf : String) (leafSpec : LeafSpec) :
    Gf128MulKernelRealizes decode leaf leafSpec
      ↔ KernelRealizes2 decode gf128_mul leaf leafSpec := Iff.rfl

/-- Extract the GF(2^128)-multiply realization equation at a point —
`transferKernel2` specialised to the GF(2^128) row: the emitted leaf, read
through `decode`, computes `gf128_mul` of its decoded operands. -/
theorem transferGf128MulKernel {decode : RustVal .TFp → BitVec 128}
    {leaf : String} {leafSpec : LeafSpec}
    (h : Gf128MulKernelRealizes decode leaf leafSpec) (aVal bVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = gf128_mul (decode aVal) (decode bVal) :=
  transferKernel2 h aVal bVal oldDest

/-! ## §2  The Poseidon2-permutation row: the unary generic predicate at
`spec := poseidon2BabyBearPermute`

The Poseidon2 permutation is `state → state` with the width-16 Baby Bear
parameters fixed, so it is a unary `KernelRealizes` row over the carrier
`Fin width → F`. -/

/-- **Poseidon2-permutation kernel-realization** — a registry ROW of the *unary*
generic predicate `ProtocolEmitRealizes.KernelRealizes`, pinned at
`spec := poseidon2BabyBearPermute` (the width-16 Baby Bear Poseidon2 permutation).
The carrier is `Fin width → F`; `decode` is the transport witness. This is NOT a
new mechanism — it is the one unary generic predicate at a ZK-hash `spec`. -/
def Poseidon2PermKernelRealizes (decode : RustVal .TFp → (Fin width → F))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode poseidon2BabyBearPermute leaf leafSpec

/-- The Poseidon2-permutation seam is the unary generic predicate at
`spec := poseidon2BabyBearPermute` — by `Iff.rfl`, exactly as
`barrett_iff_kernel` / `hash_iff_kernel`. -/
theorem poseidon2Perm_iff_kernel (decode : RustVal .TFp → (Fin width → F))
    (leaf : String) (leafSpec : LeafSpec) :
    Poseidon2PermKernelRealizes decode leaf leafSpec
      ↔ KernelRealizes decode poseidon2BabyBearPermute leaf leafSpec := Iff.rfl

/-- Extract the Poseidon2-permutation realization equation at a point —
`transferKernel` specialised to the Poseidon2 row: the emitted leaf, read through
`decode`, computes `poseidon2BabyBearPermute` of its decoded input state. -/
theorem transferPoseidon2PermKernel {decode : RustVal .TFp → (Fin width → F)}
    {leaf : String} {leafSpec : LeafSpec}
    (h : Poseidon2PermKernelRealizes decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = poseidon2BabyBearPermute (decode xVal) :=
  transferKernel h xVal oldDest

/-- A `KernelTableEntry (Fin width → F) leafSpec` for the Poseidon2 permutation —
built from any realization hypothesis. It slots into the SAME `KernelTableEntry`
registry (unary) as the NTT / field / reduce / hash rows. -/
def poseidon2PermTableEntry {decode : RustVal .TFp → (Fin width → F)}
    {leaf : String} {leafSpec : LeafSpec}
    (h : Poseidon2PermKernelRealizes decode leaf leafSpec) :
    KernelTableEntry (Fin width → F) leafSpec where
  leaf := leaf
  spec := poseidon2BabyBearPermute
  decode := decode
  realized := h

/-- The Poseidon2-permutation table row's realization equation, uniform over the
registry via `KernelTableEntry.realizes`. -/
theorem poseidon2PermTableEntry_realizes {decode : RustVal .TFp → (Fin width → F)}
    {leaf : String} {leafSpec : LeafSpec}
    (h : Poseidon2PermKernelRealizes decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (poseidon2PermTableEntry h).decode
        (leafSpec.call (poseidon2PermTableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (poseidon2PermTableEntry h).spec ((poseidon2PermTableEntry h).decode xVal) :=
  (poseidon2PermTableEntry h).realizes xVal oldDest

/-- A Poseidon2-permutation kernel followed by any other realized unary kernel
over the same carrier and `decode` composes through `link_two`. -/
theorem link_poseidon2Perm_then {decode : RustVal .TFp → (Fin width → F)}
    {spec₂ : (Fin width → F) → (Fin width → F)} {leaf₁ leaf₂ : String} {leafSpec : LeafSpec}
    (h₁ : Poseidon2PermKernelRealizes decode leaf₁ leafSpec)
    (h₂ : KernelRealizes decode spec₂ leaf₂ leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf₁ leaf₂ oldDest xVal)
      = spec₂ (poseidon2BabyBearPermute (decode xVal)) :=
  link_two h₁ h₂ xVal oldDest

/-! ## §3  The Poseidon2 2-to-1-compression row: the binary generic predicate at
`spec := poseidon2BabyBearCompress`

Merkle-node compression is `left → right → digest`, so it is a `KernelRealizes2`
row over the carrier `F`. -/

/-- **Poseidon2-compression kernel-realization** — a registry ROW of the *binary*
generic predicate `KernelRealizes2`, pinned at `spec := poseidon2BabyBearCompress`
(the 2-to-1 Merkle-node compressor). The carrier is `F`; `decode` is the transport
witness. -/
def Poseidon2CompressKernelRealizes (decode : RustVal .TFp → F)
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes2 decode poseidon2BabyBearCompress leaf leafSpec

/-- The Poseidon2-compression seam is the binary generic predicate at
`spec := poseidon2BabyBearCompress` — by `Iff.rfl`. -/
theorem poseidon2Compress_iff_kernel2 (decode : RustVal .TFp → F)
    (leaf : String) (leafSpec : LeafSpec) :
    Poseidon2CompressKernelRealizes decode leaf leafSpec
      ↔ KernelRealizes2 decode poseidon2BabyBearCompress leaf leafSpec := Iff.rfl

/-- Extract the Poseidon2-compression realization equation at a point —
`transferKernel2` specialised to the compression row. -/
theorem transferPoseidon2CompressKernel {decode : RustVal .TFp → F}
    {leaf : String} {leafSpec : LeafSpec}
    (h : Poseidon2CompressKernelRealizes decode leaf leafSpec)
    (leftVal rightVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, leftVal⟩, ⟨.TFp, rightVal⟩])
      = poseidon2BabyBearCompress (decode leftVal) (decode rightVal) :=
  transferKernel2 h leftVal rightVal oldDest

/-! ## §4  The Montgomery-ladder-step row: the unary generic predicate at
`spec := fun st => ladderStep st b`

One Montgomery-ladder step (Curve25519 scalar multiplication, Bernstein 2006) is
`(R₀,R₁) → (R₀',R₁')` once the scalar bit `b` is fixed, so it is a unary
`KernelRealizes` row over the carrier `G × G`, parametric over the group `G` and
the bit `b`. -/

/-- **Montgomery-ladder-step kernel-realization** — a registry ROW of the *unary*
generic predicate `ProtocolEmitRealizes.KernelRealizes`, pinned at
`spec := fun st => ladderStep st b` (one ladder step with the scalar bit `b`
fixed, as `steps` is fixed for the Keccak row). The carrier is `G × G`; `decode`
is the transport witness. -/
def LadderStepKernelRealizes {G : Type*} [AddCommGroup G] (b : Bool)
    (decode : RustVal .TFp → G × G) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  KernelRealizes decode (fun st => ladderStep st b) leaf leafSpec

/-- The Montgomery-ladder-step seam is the unary generic predicate at
`spec := fun st => ladderStep st b` — by `Iff.rfl`, exactly as
`barrett_iff_kernel` / `hash_iff_kernel`. -/
theorem ladderStep_iff_kernel {G : Type*} [AddCommGroup G] (b : Bool)
    (decode : RustVal .TFp → G × G) (leaf : String) (leafSpec : LeafSpec) :
    LadderStepKernelRealizes b decode leaf leafSpec
      ↔ KernelRealizes decode (fun st => ladderStep st b) leaf leafSpec := Iff.rfl

/-- Extract the Montgomery-ladder-step realization equation at a point —
`transferKernel` specialised to the ladder-step row: the emitted leaf, read
through `decode`, computes one `ladderStep · b` of its decoded input state. -/
theorem transferLadderStepKernel {G : Type*} [AddCommGroup G] {b : Bool}
    {decode : RustVal .TFp → G × G} {leaf : String} {leafSpec : LeafSpec}
    (h : LadderStepKernelRealizes b decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    decode (leafSpec.call leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = ladderStep (decode xVal) b :=
  transferKernel h xVal oldDest

/-- A `KernelTableEntry (G × G) leafSpec` for one Montgomery-ladder step — built
from any realization hypothesis. It slots into the SAME unary `KernelTableEntry`
registry as the NTT / field / reduce / hash rows. -/
def ladderStepTableEntry {G : Type*} [AddCommGroup G] {b : Bool}
    {decode : RustVal .TFp → G × G} {leaf : String} {leafSpec : LeafSpec}
    (h : LadderStepKernelRealizes b decode leaf leafSpec) :
    KernelTableEntry (G × G) leafSpec where
  leaf := leaf
  spec := fun st => ladderStep st b
  decode := decode
  realized := h

/-- The Montgomery-ladder-step table row's realization equation, uniform over the
registry via `KernelTableEntry.realizes`. -/
theorem ladderStepTableEntry_realizes {G : Type*} [AddCommGroup G] {b : Bool}
    {decode : RustVal .TFp → G × G} {leaf : String} {leafSpec : LeafSpec}
    (h : LadderStepKernelRealizes b decode leaf leafSpec) (xVal oldDest : RustVal .TFp) :
    (ladderStepTableEntry h).decode
        (leafSpec.call (ladderStepTableEntry h).leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
      = (ladderStepTableEntry h).spec ((ladderStepTableEntry h).decode xVal) :=
  (ladderStepTableEntry h).realizes xVal oldDest

/-- Two consecutive Montgomery-ladder steps (bits `b₁` then `b₂`) over the same
carrier and `decode` compose through `link_two` — the natural shape of a multi-bit
ladder fold. -/
theorem link_ladderStep_then {G : Type*} [AddCommGroup G] {b₁ b₂ : Bool}
    {decode : RustVal .TFp → G × G} {leaf₁ leaf₂ : String} {leafSpec : LeafSpec}
    (h₁ : LadderStepKernelRealizes b₁ decode leaf₁ leafSpec)
    (h₂ : LadderStepKernelRealizes b₂ decode leaf₂ leafSpec)
    (xVal oldDest : RustVal .TFp) :
    decode (pipe2 leafSpec leaf₁ leaf₂ oldDest xVal)
      = ladderStep (ladderStep (decode xVal) b₁) b₂ :=
  link_two h₁ h₂ xVal oldDest

end CatCrypt.Crypto.SecureCompilation.MoreKernelRegistryEntries
