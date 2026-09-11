/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# A batch of key-exchange / secure-transport protocols as `ProtocolKernels`

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch** of real
key-exchange / secure-transport protocols, exactly as `KdfMacProtocolKernels.lean`
does for the KDF / MAC / DRBG family.  Each protocol here is structurally a
**unary kernel chain** — a left-to-right sequence of `state → state` steps over
the running keying / transcript / sponge material — which is precisely the shape
the `ProtocolKernels` template models.

The protocols covered:

* **TLS 1.3 handshake / key schedule** (RFC 8446): the handshake first runs the
  ephemeral `X25519` Diffie–Hellman (one ladder-step prefix), then the
  `HKDF-Extract` / `HKDF-Expand-Label` key schedule (a chain of HMAC
  derivations), each threaded into the transcript hash.  We model this as one DH
  prefix kernel then `n` key-schedule derivation kernels.
* **Signal X3DH** key agreement: the four core Diffie–Hellman computations
  `DH1 … DH4` over the long-term / ephemeral / one-time keys, followed by a
  single `KDF` over the concatenated DH outputs.  We model this as a fixed
  4-element list of DH ladder steps then the KDF kernel.
* **Noise** handshake pattern (e.g. `Noise_XX`): the handshake threads the
  running `(ChainingKey, Hash)` state through a chain of `MixKey` (an `HKDF`
  application) and `MixHash` (a `hash_two`) steps.  We model this as one
  `MixHash` initialisation prefix then `n` `MixKey` / `MixHash` mixing steps.
* **Signal Double Ratchet** key derivation: each ratchet step runs one `DH`
  followed by a chain of `KDF_RK` / `KDF_CK` chain-key advances.  We model this
  as one DH prefix then `n` chain-key derivation kernels.

## What each instance delivers (mirroring the KDF/MAC batch)

For each protocol `P` we provide:

* `<P>Specs` — the kernel pipeline as a list of **abstract, unary** `C → C`
  step specs.  These are opaque models of each round; the deliverable is the
  protocol-structure composition, not re-deriving each round's DH / HMAC / sponge
  internals.
* `<P>Leaves` — the matching emitted leaf-names, taken from the real
  extraction (`CatCrypt/Crypto/{TLS,Signal/X3DH,Noise,Signal/DoubleRatchet,
  X25519,HKDF}`), e.g. `"x25519_ladder_step"`, `"hkdf_expand_label"`, `"dh"`,
  `"kdf"`, `"mix_key"`, `"mix_hash"`.
* `<P>Protocol : ProtocolKernels C leafSpec` — the assembled bundle, whose
  `realized` field is the position-wise `List.Forall₂` of the per-kernel
  realizations, **each taken as a hypothesis** (the kernel's leaf-bytes KAT).
* `<P>_protocol_realizes` — the whole-protocol emit-realization,
  `decode (pipeN <P>Leaves …) = composeSpecs <P>Specs (decode x)`, obtained by a
  single `runRealizes` call from nothing but the per-kernel realizations and the
  generic composition law.

## The point (axis-6 on a batch of transport protocols)

Each of these RFC / Signal protocols has its *whole* emit-realization assembled
from its kernel rows by `runRealizes`, with no per-protocol proof skeleton: the
key-exchange / transport kernel-chain structure fits the unary `ProtocolKernels`
template exactly.  The per-kernel realizations are honest hypotheses (each is the
kernel's leaf-bytes KAT); the contribution is that the protocol-level
composition assembles for free from them.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TransportProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  Two shared chain helpers

Two pipeline shapes recur across the protocols below.

**Shape A (prefix + n blocks).**  One *prefix* kernel followed by `n` copies of a
*block* kernel — exactly the `chainSpecs` / `chainLeaves` / `chainRealized`
shape used in `KdfMacProtocolKernels.lean`.  We re-derive that helper here so
this file is self-contained (it differs from the KDF file only in the
namespace).  TLS 1.3 (DH prefix then `n` key-schedule steps), Noise (MixHash
prefix then `n` mixing steps), and Double Ratchet (DH prefix then `n` chain-key
steps) all use this shape.

**Shape B (explicit leaf/spec list).**  A fixed, position-wise list of kernels
whose realizations are supplied one per position.  X3DH (four distinct DH steps
then one KDF) uses this shape; it is the bare `ProtocolKernels` constructor with
the `Forall₂` supplied directly. -/

/-! ### §0.1  Shape A — one prefix then `n` blocks -/

/-- A one-prefix-then-`n`-blocks unary spec list. -/
def chainSpecs (prefixStep : C → C) (blockStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  prefixStep :: (List.range n).map (fun i => blockStep i)

/-- The matching one-prefix-then-`n`-blocks leaf list. -/
def chainLeaves (prefixLeaf blockLeaf : String) (n : Nat) : List String :=
  prefixLeaf :: List.replicate n blockLeaf

/-- The position-wise realization bundle for the one-prefix-then-`n`-blocks
    pipeline, assembled by induction on `n` from the prefix realization and one
    block realization per block. -/
theorem chainRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (blockStep : Nat → C → C)
    (prefixLeaf blockLeaf : String) (n : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      (chainLeaves prefixLeaf blockLeaf n)
      (chainSpecs prefixStep blockStep n) := by
  unfold chainLeaves chainSpecs
  refine List.Forall₂.cons hPrefix ?_
  induction n with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.replicate_succ']
      exact List.rel_append ih (List.Forall₂.cons (hBlock m) List.Forall₂.nil)

/-- The assembled one-prefix-then-`n`-blocks `ProtocolKernels`. -/
def chainProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (blockStep : Nat → C → C)
    (prefixLeaf blockLeaf : String) (n : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := chainLeaves prefixLeaf blockLeaf n
  specs := chainSpecs prefixStep blockStep n
  decode := decode
  realized :=
    chainRealized leafSpec decode prefixStep blockStep prefixLeaf blockLeaf n
      hPrefix hBlock

/-- The whole-pipeline emit-realization of a one-prefix-then-`n`-blocks chain,
    obtained by a single `runRealizes` call. -/
theorem chain_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (blockStep : Nat → C → C)
    (prefixLeaf blockLeaf : String) (n : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (chainLeaves prefixLeaf blockLeaf n) oldDest xVal)
      = composeSpecs (chainSpecs prefixStep blockStep n) (decode xVal) :=
  (chainProtocol leafSpec decode prefixStep blockStep prefixLeaf blockLeaf n
      hPrefix hBlock).runRealizes oldDest xVal

/-! ### §0.2  Shape B — explicit leaf/spec list

For a protocol whose kernel list is a fixed, non-uniform sequence (e.g. four
distinct DH steps then a KDF), the `ProtocolKernels` bundle is assembled
directly from a `List.Forall₂` of per-position `KernelRealizes` proofs.  The
`listProtocol` / `list_protocol_realizes` pair below is a thin wrapper exposing
exactly that constructor with no extra structure. -/

/-- The assembled `ProtocolKernels` for an explicit leaf/spec list whose
    position-wise realizations are supplied directly. -/
def listProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaves : List String) (specs : List (C → C))
    (realized : List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec) leaves specs) :
    ProtocolKernels C leafSpec where
  leaves := leaves
  specs := specs
  decode := decode
  realized := realized

/-- The whole-pipeline emit-realization of an explicit leaf/spec list, obtained
    by a single `runRealizes` call. -/
theorem list_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaves : List String) (specs : List (C → C))
    (realized : List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec) leaves specs)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec leaves oldDest xVal)
      = composeSpecs specs (decode xVal) :=
  (listProtocol leafSpec decode leaves specs realized).runRealizes oldDest xVal

/-! ## §1  TLS 1.3 handshake / key schedule (RFC 8446)

The TLS 1.3 handshake first runs the ephemeral `X25519` Diffie–Hellman to obtain
the shared secret, then drives the RFC 8446 §7.1 key schedule: an
`HKDF-Extract` followed by a chain of `HKDF-Expand-Label` / `Derive-Secret`
steps over the running secret, each one an HMAC application.  We model the whole
handshake as one `X25519`-ladder DH prefix then `n` key-schedule derivation
kernels (the extract-then-expand chain after the DH).

Leaf names from the real extraction: the X25519 ladder step
`"x25519_ladder_step"` (`CatCrypt/Crypto/SecureCompilation/KemProtocolKernels.lean`)
and the HKDF expand-label derivation `"hkdf_expand_label"`
(`CatCrypt/Crypto/TLS/Extraction`, mirrored in `KdfMacProtocolKernels.lean`). -/

/-- The TLS 1.3 handshake `X25519` Diffie–Hellman ladder-step leaf. -/
def tls13DhLeaf : String := "x25519_ladder_step"

/-- The TLS 1.3 key-schedule `HKDF-Expand-Label` / `Derive-Secret` derivation
    leaf. -/
def tls13DeriveLeaf : String := "hkdf_expand_label"

/-- The TLS 1.3 handshake kernel-spec list: one `dhStep` (X25519) then `n`
    `deriveStep i` key-schedule derivations. -/
def tls13Specs (dhStep : C → C) (deriveStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs dhStep deriveStep n

/-- The TLS 1.3 handshake leaf list: the X25519 leaf then `n` copies of the
    expand-label leaf. -/
def tls13Leaves (n : Nat) : List String :=
  chainLeaves tls13DhLeaf tls13DeriveLeaf n

/-- **The assembled TLS 1.3 handshake protocol.** -/
def tls13Protocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (dhStep : C → C) (deriveStep : Nat → C → C) (n : Nat)
    (hDh : KernelRealizes decode dhStep tls13DhLeaf leafSpec)
    (hDerive : ∀ i,
      KernelRealizes decode (deriveStep i) tls13DeriveLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  chainProtocol leafSpec decode dhStep deriveStep
    tls13DhLeaf tls13DeriveLeaf n hDh hDerive

/-- **The whole-TLS-1.3-handshake emit-realization (axis-6 on a real protocol).**
    The entire emitted handshake chain — one X25519 DH kernel then `n`
    HKDF-Expand-Label derivations — decodes to the composite
    `composeSpecs (tls13Specs …)` of the input.  Assembled by one `runRealizes`
    call from the per-kernel realizations (each an honest leaf-bytes KAT
    hypothesis) and the generic composition law. -/
theorem tls13_handshake_protocol_realizes (leafSpec : LeafSpec)
    (decode : RustVal .TFp → C)
    (dhStep : C → C) (deriveStep : Nat → C → C) (n : Nat)
    (hDh : KernelRealizes decode dhStep tls13DhLeaf leafSpec)
    (hDerive : ∀ i,
      KernelRealizes decode (deriveStep i) tls13DeriveLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (tls13Leaves n) oldDest xVal)
      = composeSpecs (tls13Specs dhStep deriveStep n) (decode xVal) :=
  chain_protocol_realizes leafSpec decode dhStep deriveStep
    tls13DhLeaf tls13DeriveLeaf n hDh hDerive oldDest xVal

/-! ## §2  Signal X3DH key agreement

The X3DH key agreement computes four Diffie–Hellman values `DH1 … DH4` over the
identity / ephemeral / signed-prekey / one-time-prekey combinations, then runs a
single `KDF` over their concatenation to derive the shared secret.  This is a
fixed, non-uniform pipeline — four `dh` kernels then one `kdf` kernel — so it
uses Shape B (the explicit leaf/spec list) rather than the prefix-then-blocks
chain.

Leaf names from the real extraction (`CatCrypt/Crypto/Signal/X3DH/Extraction`):
the DH leaf `"dh"` (called four times) and the KDF leaf `"kdf"`. -/

/-- The X3DH Diffie–Hellman leaf (one per `DH1 … DH4`). -/
def x3dhDhLeaf : String := "dh"

/-- The X3DH final `KDF` leaf over the concatenated DH outputs. -/
def x3dhKdfLeaf : String := "kdf"

/-- The X3DH leaf list: four `dh` kernels then the final `kdf` kernel. -/
def x3dhLeaves : List String :=
  [x3dhDhLeaf, x3dhDhLeaf, x3dhDhLeaf, x3dhDhLeaf, x3dhKdfLeaf]

/-- The X3DH kernel-spec list: the four DH steps `dh1 … dh4` then `kdf`. -/
def x3dhSpecs (dh1 dh2 dh3 dh4 kdf : C → C) : List (C → C) :=
  [dh1, dh2, dh3, dh4, kdf]

/-- The position-wise realization bundle for the X3DH pipeline, assembled
    directly from the five per-kernel realizations. -/
theorem x3dhRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (dh1 dh2 dh3 dh4 kdf : C → C)
    (hDh1 : KernelRealizes decode dh1 x3dhDhLeaf leafSpec)
    (hDh2 : KernelRealizes decode dh2 x3dhDhLeaf leafSpec)
    (hDh3 : KernelRealizes decode dh3 x3dhDhLeaf leafSpec)
    (hDh4 : KernelRealizes decode dh4 x3dhDhLeaf leafSpec)
    (hKdf : KernelRealizes decode kdf x3dhKdfLeaf leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      x3dhLeaves (x3dhSpecs dh1 dh2 dh3 dh4 kdf) := by
  unfold x3dhLeaves x3dhSpecs
  exact List.Forall₂.cons hDh1 (List.Forall₂.cons hDh2 (List.Forall₂.cons hDh3
    (List.Forall₂.cons hDh4 (List.Forall₂.cons hKdf List.Forall₂.nil))))

/-- **The assembled X3DH protocol.** -/
def x3dhProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (dh1 dh2 dh3 dh4 kdf : C → C)
    (hDh1 : KernelRealizes decode dh1 x3dhDhLeaf leafSpec)
    (hDh2 : KernelRealizes decode dh2 x3dhDhLeaf leafSpec)
    (hDh3 : KernelRealizes decode dh3 x3dhDhLeaf leafSpec)
    (hDh4 : KernelRealizes decode dh4 x3dhDhLeaf leafSpec)
    (hKdf : KernelRealizes decode kdf x3dhKdfLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  listProtocol leafSpec decode x3dhLeaves (x3dhSpecs dh1 dh2 dh3 dh4 kdf)
    (x3dhRealized leafSpec decode dh1 dh2 dh3 dh4 kdf hDh1 hDh2 hDh3 hDh4 hKdf)

/-- **The whole-X3DH emit-realization (axis-6 on a real protocol).**  The entire
    emitted X3DH pipeline — four `dh` kernels then the `kdf` kernel — decodes to
    the composite `composeSpecs (x3dhSpecs …)` of the input.  Assembled by one
    `runRealizes` call from the five per-kernel realizations (each an honest
    leaf-bytes KAT hypothesis). -/
theorem x3dh_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (dh1 dh2 dh3 dh4 kdf : C → C)
    (hDh1 : KernelRealizes decode dh1 x3dhDhLeaf leafSpec)
    (hDh2 : KernelRealizes decode dh2 x3dhDhLeaf leafSpec)
    (hDh3 : KernelRealizes decode dh3 x3dhDhLeaf leafSpec)
    (hDh4 : KernelRealizes decode dh4 x3dhDhLeaf leafSpec)
    (hKdf : KernelRealizes decode kdf x3dhKdfLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec x3dhLeaves oldDest xVal)
      = composeSpecs (x3dhSpecs dh1 dh2 dh3 dh4 kdf) (decode xVal) :=
  list_protocol_realizes leafSpec decode x3dhLeaves (x3dhSpecs dh1 dh2 dh3 dh4 kdf)
    (x3dhRealized leafSpec decode dh1 dh2 dh3 dh4 kdf hDh1 hDh2 hDh3 hDh4 hKdf)
    oldDest xVal

/-! ## §3  Noise handshake pattern (e.g. `Noise_XX`)

A Noise handshake threads a running `(ChainingKey, Hash)` symmetric state through
a chain of `MixHash` (a `hash_two` over the running hash and the next message
fragment) and `MixKey` (an `HKDF` over the chaining key and a DH output) steps.
After the initial `MixHash` that absorbs the protocol-name/prologue, the
handshake is a chain of `n` mixing steps.  We model this as one `MixHash`
initialisation prefix then `n` `MixKey` mixing steps.

Leaf names from the real extraction (`CatCrypt/Crypto/Noise/Extraction`): the
`MixHash` kernel `"mix_hash"` and the `MixKey` kernel `"mix_key"` (the emitted
`mix_hash_impExpr` / `mix_key_impExpr` kernels). -/

/-- The Noise `MixHash` kernel leaf (initialisation / hash mixing). -/
def noiseMixHashLeaf : String := "mix_hash"

/-- The Noise `MixKey` kernel leaf (HKDF over the chaining key and a DH output). -/
def noiseMixKeyLeaf : String := "mix_key"

/-- The Noise handshake kernel-spec list: one `initStep` (`MixHash`) then `n`
    `mixStep i` (`MixKey`) mixing steps. -/
def noiseSpecs (initStep : C → C) (mixStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs initStep mixStep n

/-- The Noise handshake leaf list: the `MixHash` leaf then `n` copies of the
    `MixKey` leaf. -/
def noiseLeaves (n : Nat) : List String :=
  chainLeaves noiseMixHashLeaf noiseMixKeyLeaf n

/-- **The assembled Noise handshake protocol.** -/
def noiseProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (initStep : C → C) (mixStep : Nat → C → C) (n : Nat)
    (hInit : KernelRealizes decode initStep noiseMixHashLeaf leafSpec)
    (hMix : ∀ i, KernelRealizes decode (mixStep i) noiseMixKeyLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  chainProtocol leafSpec decode initStep mixStep
    noiseMixHashLeaf noiseMixKeyLeaf n hInit hMix

/-- **The whole-Noise-handshake emit-realization (axis-6 on a real protocol).**
    The entire emitted Noise mixing chain — one `MixHash` init kernel then `n`
    `MixKey` mixing steps — decodes to the composite `composeSpecs (noiseSpecs …)`
    of the input.  Assembled by one `runRealizes` call from the per-kernel
    realizations (each an honest leaf-bytes KAT hypothesis). -/
theorem noise_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (initStep : C → C) (mixStep : Nat → C → C) (n : Nat)
    (hInit : KernelRealizes decode initStep noiseMixHashLeaf leafSpec)
    (hMix : ∀ i, KernelRealizes decode (mixStep i) noiseMixKeyLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (noiseLeaves n) oldDest xVal)
      = composeSpecs (noiseSpecs initStep mixStep n) (decode xVal) :=
  chain_protocol_realizes leafSpec decode initStep mixStep
    noiseMixHashLeaf noiseMixKeyLeaf n hInit hMix oldDest xVal

/-! ## §4  Signal Double Ratchet key derivation

Each Double Ratchet step runs one `DH` (the ratchet DH) to obtain fresh shared
material, then advances the symmetric ratchet via a chain of root-key /
chain-key KDFs.  We model one ratchet step as one `DH` prefix then `n`
`KDF_CK` chain-key advances (the message-key derivation chain that follows the
ratchet DH).

Leaf names from the real extraction
(`CatCrypt/Crypto/Signal/DoubleRatchet/Extraction`): the DH leaf `"dh"` and the
chain-key KDF leaf `"kdf_ck"` (the emitted `dh_impExpr` / `kdf_ck_impExpr`
kernels). -/

/-- The Double Ratchet `DH` kernel leaf (the ratchet Diffie–Hellman). -/
def doubleRatchetDhLeaf : String := "dh"

/-- The Double Ratchet `KDF_CK` chain-key advance kernel leaf. -/
def doubleRatchetKdfCkLeaf : String := "kdf_ck"

/-- The Double Ratchet kernel-spec list: one `dhStep` then `n` `kdfCkStep i`
    chain-key advances. -/
def doubleRatchetSpecs (dhStep : C → C) (kdfCkStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs dhStep kdfCkStep n

/-- The Double Ratchet leaf list: the `dh` leaf then `n` copies of the `kdf_ck`
    leaf. -/
def doubleRatchetLeaves (n : Nat) : List String :=
  chainLeaves doubleRatchetDhLeaf doubleRatchetKdfCkLeaf n

/-- **The assembled Double Ratchet protocol.** -/
def doubleRatchetProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (dhStep : C → C) (kdfCkStep : Nat → C → C) (n : Nat)
    (hDh : KernelRealizes decode dhStep doubleRatchetDhLeaf leafSpec)
    (hKdfCk : ∀ i,
      KernelRealizes decode (kdfCkStep i) doubleRatchetKdfCkLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  chainProtocol leafSpec decode dhStep kdfCkStep
    doubleRatchetDhLeaf doubleRatchetKdfCkLeaf n hDh hKdfCk

/-- **The whole-Double-Ratchet emit-realization (axis-6 on a real protocol).**
    The entire emitted ratchet-step chain — one `dh` kernel then `n` `kdf_ck`
    chain-key advances — decodes to the composite
    `composeSpecs (doubleRatchetSpecs …)` of the input.  Assembled by one
    `runRealizes` call from the per-kernel realizations. -/
theorem double_ratchet_protocol_realizes (leafSpec : LeafSpec)
    (decode : RustVal .TFp → C)
    (dhStep : C → C) (kdfCkStep : Nat → C → C) (n : Nat)
    (hDh : KernelRealizes decode dhStep doubleRatchetDhLeaf leafSpec)
    (hKdfCk : ∀ i,
      KernelRealizes decode (kdfCkStep i) doubleRatchetKdfCkLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (doubleRatchetLeaves n) oldDest xVal)
      = composeSpecs (doubleRatchetSpecs dhStep kdfCkStep n) (decode xVal) :=
  chain_protocol_realizes leafSpec decode dhStep kdfCkStep
    doubleRatchetDhLeaf doubleRatchetKdfCkLeaf n hDh hKdfCk oldDest xVal

end CatCrypt.Crypto.SecureCompilation.TransportProtocolKernels
