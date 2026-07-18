/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# A batch of classical signature / MAC protocols as axis-6 `ProtocolKernels` instances

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch** of
classical discrete-log signature schemes, exactly as `HkdfProtocolKernels.lean`
and `KdfMacProtocolKernels.lean` do for the KDF / MAC families.  The KDF / MAC
protocols are HMAC- or Keccak-of-the-running-state chains; these signature
schemes have a different but equally unary shape: **hash the message, then a
scalar / field-arithmetic chain** over the running scalar carrier.

A discrete-log signature's response is computed by hashing the message (or
commitment) to a scalar, then folding that scalar through a fixed sequence of
field operations:

```text
e    = hash(message)            -- the hash-to-scalar prefix kernel
s₀   = …                        -- field-arith steps (mul/add/inverse) over the
…                               --   running scalar, one emitted kernel each
sig  = …
```

Because each field step's other operand (the secret key, the nonce, a fixed
group element) is a parameter of that step, every step is a *unary* map
`scalar → scalar` on the carrier — exactly the shape the unary
`ProtocolKernels` template models.  The whole signing response is therefore a
unary pipeline `e ↦ s₀ ↦ … ↦ sig`, and its whole emit-realization assembles
from the hash row plus the field-arithmetic rows by the generic template, with
no per-protocol proof skeleton.

## Protocols covered

* **EdDSA / Ed25519 sign** (RFC 8032): hash the message with SHA-512, reduce the
  wide digest mod the group order, then the scalar chain `s = r + e·a`
  (multiply the reduced challenge `e` by the secret scalar `a`, add the nonce
  `r`).  Leaves from `CatCrypt/Crypto/EdDSA/`:
  `"scalar_sn_reduce_wide"` (the digest → `mod L` reduction),
  `"scalar_mul"`, `"scalar_add"`.
* **ECDSA** (FIPS 186-4): hash the message to a scalar, invert the nonce `k`,
  then `s = k⁻¹·(h + r·d)`.  Leaves from `CatCrypt/Crypto/ECDSA/`:
  `"hash_to_scalar"`, `"scalar_inv"`, `"scalar_mul"`.
* **Schnorr** (the canonical Σ-protocol signature): hash the commitment to the
  challenge, then `s = r + c·x`.  Leaves from `CatCrypt/Crypto/Schnorr/`:
  `"hash_challenge"`, `"scalar_mul"`, `"scalar_add"`.
* **FROST** (threshold Schnorr, RFC 9591): compute the binding challenge, invert
  the Lagrange denominator for the signer's coefficient, then the Schnorr
  scalar chain `z = r + c·λ·s`.  Leaves from `CatCrypt/Crypto/FROST/`:
  `"compute_challenge"`, `"denom_inv"`, `"scalar_mul"`, `"scalar_add"`.

## What each instance delivers (mirroring HKDF / KdfMac)

For each protocol `P` we provide:

* `<P>Specs` — the kernel pipeline as a list of **abstract, unary** `C → C`
  scalar-step specs (the hash-to-scalar prefix plus the field-arith steps).
  These are opaque models of each step; the deliverable is the
  protocol-structure composition, not re-deriving each field operation's
  internals (those are the registered field / Montgomery / Fermat-inverse rows).
* `<P>Leaves` — the matching emitted leaf-names, taken from the real extractions
  (`CatCrypt/Crypto/{EdDSA,ECDSA,Schnorr,FROST}/`).
* `<P>Protocol : ProtocolKernels C leafSpec` — the assembled bundle, whose
  `realized` field is the position-wise `List.Forall₂` of the per-kernel
  realizations, **each taken as a hypothesis** (the kernel's leaf-bytes KAT).
* `<P>_protocol_realizes` — the whole-protocol emit-realization,
  `decode (pipeN <P>Leaves …) = composeSpecs <P>Specs (decode x)`, obtained by a
  single `runRealizes` call from nothing but the per-kernel realizations and the
  generic composition law.

## The point (axis-6 on a batch of signatures)

These signatures' whole emit-realizations assemble from their hash +
field-arithmetic kernel rows by the generic template: the hash-then-scalar-chain
structure fits the unary `ProtocolKernels` template exactly.  The per-kernel
realizations are honest hypotheses (each is the kernel's leaf-bytes KAT); the
contribution is that the protocol-level composition assembles for free from them,
with no per-protocol proof skeleton.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SignatureProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  A fixed-length assembly helper

Each signature below is a *fixed* short sequence of distinct kernels (a
hash-to-scalar prefix plus two or three field-arith steps), not a
prefix-then-`n`-repeats chain.  So — unlike the KDF chains — we assemble the
position-wise `Forall₂` directly from the explicit per-step realizations.  We
provide a small helper for the common 3- and 4-step shapes so each protocol
instance is a thin renaming.  Both reduce to the generic
`ProtocolKernels.runRealizes`. -/

/-- Assemble a 3-step signature pipeline (hash-to-scalar prefix then two
    field-arith steps) into a `ProtocolKernels`, from the decoder and the three
    per-step realizations. -/
def sig3Protocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf₁ leaf₂ leaf₃ : String) (step₁ step₂ step₃ : C → C)
    (h₁ : KernelRealizes decode step₁ leaf₁ leafSpec)
    (h₂ : KernelRealizes decode step₂ leaf₂ leafSpec)
    (h₃ : KernelRealizes decode step₃ leaf₃ leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := [leaf₁, leaf₂, leaf₃]
  specs := [step₁, step₂, step₃]
  decode := decode
  realized :=
    List.Forall₂.cons h₁ (List.Forall₂.cons h₂ (List.Forall₂.cons h₃ List.Forall₂.nil))

/-- The whole-pipeline emit-realization of a 3-step signature, by one
    `runRealizes` call. -/
theorem sig3_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf₁ leaf₂ leaf₃ : String) (step₁ step₂ step₃ : C → C)
    (h₁ : KernelRealizes decode step₁ leaf₁ leafSpec)
    (h₂ : KernelRealizes decode step₂ leaf₂ leafSpec)
    (h₃ : KernelRealizes decode step₃ leaf₃ leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec [leaf₁, leaf₂, leaf₃] oldDest xVal)
      = composeSpecs [step₁, step₂, step₃] (decode xVal) :=
  (sig3Protocol leafSpec decode leaf₁ leaf₂ leaf₃ step₁ step₂ step₃ h₁ h₂ h₃).runRealizes
    oldDest xVal

/-- Assemble a 4-step signature pipeline into a `ProtocolKernels`, from the
    decoder and the four per-step realizations. -/
def sig4Protocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf₁ leaf₂ leaf₃ leaf₄ : String) (step₁ step₂ step₃ step₄ : C → C)
    (h₁ : KernelRealizes decode step₁ leaf₁ leafSpec)
    (h₂ : KernelRealizes decode step₂ leaf₂ leafSpec)
    (h₃ : KernelRealizes decode step₃ leaf₃ leafSpec)
    (h₄ : KernelRealizes decode step₄ leaf₄ leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := [leaf₁, leaf₂, leaf₃, leaf₄]
  specs := [step₁, step₂, step₃, step₄]
  decode := decode
  realized :=
    List.Forall₂.cons h₁ (List.Forall₂.cons h₂
      (List.Forall₂.cons h₃ (List.Forall₂.cons h₄ List.Forall₂.nil)))

/-- The whole-pipeline emit-realization of a 4-step signature, by one
    `runRealizes` call. -/
theorem sig4_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf₁ leaf₂ leaf₃ leaf₄ : String) (step₁ step₂ step₃ step₄ : C → C)
    (h₁ : KernelRealizes decode step₁ leaf₁ leafSpec)
    (h₂ : KernelRealizes decode step₂ leaf₂ leafSpec)
    (h₃ : KernelRealizes decode step₃ leaf₃ leafSpec)
    (h₄ : KernelRealizes decode step₄ leaf₄ leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec [leaf₁, leaf₂, leaf₃, leaf₄] oldDest xVal)
      = composeSpecs [step₁, step₂, step₃, step₄] (decode xVal) :=
  (sig4Protocol leafSpec decode leaf₁ leaf₂ leaf₃ leaf₄
      step₁ step₂ step₃ step₄ h₁ h₂ h₃ h₄).runRealizes oldDest xVal

/-! ## §1  EdDSA / Ed25519 sign (RFC 8032)

Ed25519 signing computes `s = r + e·a` where `e = SHA-512(R ‖ A ‖ M) mod L` is
the challenge scalar reduced from the wide SHA-512 digest, `a` is the secret
scalar, and `r` is the per-message nonce.  Over the running scalar carrier this
is a unary chain: reduce the (already-hashed) wide digest mod the group order,
multiply by the secret scalar, add the nonce.

Leaf names from the real extraction (`CatCrypt/Crypto/EdDSA/`):
`"scalar_sn_reduce_wide"` (the `Ed25519ReduceEmit` digest → `mod L` reduction
kernel), `"scalar_mul"` and `"scalar_add"` (the group-order scalar field ops). -/

/-- The Ed25519 wide-digest → `mod L` reduction kernel leaf. -/
def ed25519ReduceLeaf : String := "scalar_sn_reduce_wide"

/-- The Ed25519 scalar-multiply kernel leaf (`e·a` mod `L`). -/
def ed25519MulLeaf : String := "scalar_mul"

/-- The Ed25519 scalar-add kernel leaf (`r + e·a` mod `L`). -/
def ed25519AddLeaf : String := "scalar_add"

/-- The Ed25519-sign kernel-spec list: reduce the wide digest, multiply by the
    secret scalar, add the nonce — three unary scalar steps. -/
def eddsaSpecs (reduceStep mulStep addStep : C → C) : List (C → C) :=
  [reduceStep, mulStep, addStep]

/-- The Ed25519-sign leaf list, matching `eddsaSpecs` in length and order. -/
def eddsaLeaves : List String :=
  [ed25519ReduceLeaf, ed25519MulLeaf, ed25519AddLeaf]

/-- **The assembled Ed25519-sign protocol.** -/
def eddsaProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (reduceStep mulStep addStep : C → C)
    (hReduce : KernelRealizes decode reduceStep ed25519ReduceLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep ed25519MulLeaf leafSpec)
    (hAdd : KernelRealizes decode addStep ed25519AddLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  sig3Protocol leafSpec decode ed25519ReduceLeaf ed25519MulLeaf ed25519AddLeaf
    reduceStep mulStep addStep hReduce hMul hAdd

/-- **The whole-Ed25519-sign emit-realization (axis-6 on a real signature).**
    The entire emitted scalar chain — reduce, multiply, add — decodes to the
    composite `composeSpecs (eddsaSpecs …)` of the input.  Assembled by one
    `runRealizes` call from the per-kernel realizations (each an honest
    leaf-bytes KAT hypothesis) and the generic composition law. -/
theorem eddsa_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (reduceStep mulStep addStep : C → C)
    (hReduce : KernelRealizes decode reduceStep ed25519ReduceLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep ed25519MulLeaf leafSpec)
    (hAdd : KernelRealizes decode addStep ed25519AddLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec eddsaLeaves oldDest xVal)
      = composeSpecs (eddsaSpecs reduceStep mulStep addStep) (decode xVal) :=
  sig3_realizes leafSpec decode ed25519ReduceLeaf ed25519MulLeaf ed25519AddLeaf
    reduceStep mulStep addStep hReduce hMul hAdd oldDest xVal

/-! ## §2  ECDSA (FIPS 186-4)

ECDSA signing computes `s = k⁻¹·(h + r·d)` where `h = hash(M)` is the message
hashed to a scalar, `k` is the per-message nonce, `r` is the commitment's
x-coordinate, and `d` is the secret key.  Over the running scalar carrier this
is the unary chain: hash the message to a scalar, invert the nonce, then the
modular multiply that finishes the response.

Leaf names from the real extraction (`CatCrypt/Crypto/ECDSA/`):
`"hash_to_scalar"` (the hash-then-reduce leaf), `"scalar_inv"` (the modular
inverse — the Fermat-inverse registry row), `"scalar_mul"`. -/

/-- The ECDSA hash-to-scalar kernel leaf. -/
def ecdsaHashLeaf : String := "hash_to_scalar"

/-- The ECDSA modular-inverse kernel leaf (`k⁻¹` mod `n` — the Fermat-inverse
    registry row). -/
def ecdsaInvLeaf : String := "scalar_inv"

/-- The ECDSA scalar-multiply kernel leaf. -/
def ecdsaMulLeaf : String := "scalar_mul"

/-- The ECDSA-sign kernel-spec list: hash to scalar, invert the nonce, modular
    multiply — three unary scalar steps. -/
def ecdsaSpecs (hashStep invStep mulStep : C → C) : List (C → C) :=
  [hashStep, invStep, mulStep]

/-- The ECDSA-sign leaf list, matching `ecdsaSpecs` in length and order. -/
def ecdsaLeaves : List String :=
  [ecdsaHashLeaf, ecdsaInvLeaf, ecdsaMulLeaf]

/-- **The assembled ECDSA-sign protocol.** -/
def ecdsaProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (hashStep invStep mulStep : C → C)
    (hHash : KernelRealizes decode hashStep ecdsaHashLeaf leafSpec)
    (hInv : KernelRealizes decode invStep ecdsaInvLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep ecdsaMulLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  sig3Protocol leafSpec decode ecdsaHashLeaf ecdsaInvLeaf ecdsaMulLeaf
    hashStep invStep mulStep hHash hInv hMul

/-- **The whole-ECDSA-sign emit-realization (axis-6 on a real signature).**  The
    entire emitted scalar chain — hash-to-scalar, inverse, multiply — decodes to
    the composite `composeSpecs (ecdsaSpecs …)` of the input.  Assembled by one
    `runRealizes` call from the per-kernel realizations (each an honest
    leaf-bytes KAT hypothesis) and the generic composition law. -/
theorem ecdsa_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (hashStep invStep mulStep : C → C)
    (hHash : KernelRealizes decode hashStep ecdsaHashLeaf leafSpec)
    (hInv : KernelRealizes decode invStep ecdsaInvLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep ecdsaMulLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec ecdsaLeaves oldDest xVal)
      = composeSpecs (ecdsaSpecs hashStep invStep mulStep) (decode xVal) :=
  sig3_realizes leafSpec decode ecdsaHashLeaf ecdsaInvLeaf ecdsaMulLeaf
    hashStep invStep mulStep hHash hInv hMul oldDest xVal

/-! ## §3  Schnorr (the canonical Σ-protocol signature)

Schnorr signing computes `s = r + c·x` where `c = hash(R ‖ M)` is the challenge,
`r` is the nonce, and `x` is the secret key.  Over the running scalar carrier
this is the unary chain: hash the commitment to the challenge, multiply by the
secret key, add the nonce.

Leaf names from the real extraction (`CatCrypt/Crypto/Schnorr/`):
`"hash_challenge"`, `"scalar_mul"`, `"scalar_add"`. -/

/-- The Schnorr hash-to-challenge kernel leaf. -/
def schnorrHashLeaf : String := "hash_challenge"

/-- The Schnorr scalar-multiply kernel leaf (`c·x`). -/
def schnorrMulLeaf : String := "scalar_mul"

/-- The Schnorr scalar-add kernel leaf (`r + c·x`). -/
def schnorrAddLeaf : String := "scalar_add"

/-- The Schnorr-sign kernel-spec list: hash to challenge, multiply by the secret
    key, add the nonce — three unary scalar steps. -/
def schnorrSpecs (hashStep mulStep addStep : C → C) : List (C → C) :=
  [hashStep, mulStep, addStep]

/-- The Schnorr-sign leaf list, matching `schnorrSpecs` in length and order. -/
def schnorrLeaves : List String :=
  [schnorrHashLeaf, schnorrMulLeaf, schnorrAddLeaf]

/-- **The assembled Schnorr-sign protocol.** -/
def schnorrProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (hashStep mulStep addStep : C → C)
    (hHash : KernelRealizes decode hashStep schnorrHashLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep schnorrMulLeaf leafSpec)
    (hAdd : KernelRealizes decode addStep schnorrAddLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  sig3Protocol leafSpec decode schnorrHashLeaf schnorrMulLeaf schnorrAddLeaf
    hashStep mulStep addStep hHash hMul hAdd

/-- **The whole-Schnorr-sign emit-realization (axis-6 on a real signature).**
    The entire emitted scalar chain — hash-to-challenge, multiply, add — decodes
    to the composite `composeSpecs (schnorrSpecs …)` of the input.  Assembled by
    one `runRealizes` call from the per-kernel realizations (each an honest
    leaf-bytes KAT hypothesis) and the generic composition law. -/
theorem schnorr_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (hashStep mulStep addStep : C → C)
    (hHash : KernelRealizes decode hashStep schnorrHashLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep schnorrMulLeaf leafSpec)
    (hAdd : KernelRealizes decode addStep schnorrAddLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec schnorrLeaves oldDest xVal)
      = composeSpecs (schnorrSpecs hashStep mulStep addStep) (decode xVal) :=
  sig3_realizes leafSpec decode schnorrHashLeaf schnorrMulLeaf schnorrAddLeaf
    hashStep mulStep addStep hHash hMul hAdd oldDest xVal

/-! ## §4  FROST — threshold Schnorr (RFC 9591)

FROST's signature share is `z = r + c·λ·s` where `c` is the binding challenge,
`λ` is the signer's Lagrange coefficient (computed from a denominator inverse),
`s` is the signer's secret share, and `r` is the nonce.  Over the running scalar
carrier this is the unary chain: compute the binding challenge, invert the
Lagrange denominator, the scalar multiply that forms `c·λ·s`, then add the nonce.

Leaf names from the real extraction (`CatCrypt/Crypto/FROST/`):
`"compute_challenge"`, `"denom_inv"` (the Lagrange-denominator field inverse),
`"scalar_mul"`, `"scalar_add"`. -/

/-- The FROST binding-challenge kernel leaf. -/
def frostChallengeLeaf : String := "compute_challenge"

/-- The FROST Lagrange-denominator inverse kernel leaf. -/
def frostDenomInvLeaf : String := "denom_inv"

/-- The FROST scalar-multiply kernel leaf (`c·λ·s`). -/
def frostMulLeaf : String := "scalar_mul"

/-- The FROST scalar-add kernel leaf (`r + c·λ·s`). -/
def frostAddLeaf : String := "scalar_add"

/-- The FROST signature-share kernel-spec list: compute the challenge, invert the
    Lagrange denominator, scalar multiply, add the nonce — four unary scalar
    steps. -/
def frostSpecs (challengeStep denomInvStep mulStep addStep : C → C) :
    List (C → C) :=
  [challengeStep, denomInvStep, mulStep, addStep]

/-- The FROST signature-share leaf list, matching `frostSpecs` in length and
    order. -/
def frostLeaves : List String :=
  [frostChallengeLeaf, frostDenomInvLeaf, frostMulLeaf, frostAddLeaf]

/-- **The assembled FROST signature-share protocol.** -/
def frostProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (challengeStep denomInvStep mulStep addStep : C → C)
    (hChallenge : KernelRealizes decode challengeStep frostChallengeLeaf leafSpec)
    (hDenomInv : KernelRealizes decode denomInvStep frostDenomInvLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep frostMulLeaf leafSpec)
    (hAdd : KernelRealizes decode addStep frostAddLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  sig4Protocol leafSpec decode frostChallengeLeaf frostDenomInvLeaf frostMulLeaf
    frostAddLeaf challengeStep denomInvStep mulStep addStep
    hChallenge hDenomInv hMul hAdd

/-- **The whole-FROST signature-share emit-realization (axis-6 on a threshold
    signature).**  The entire emitted scalar chain — challenge, Lagrange-denom
    inverse, multiply, add — decodes to the composite `composeSpecs
    (frostSpecs …)` of the input.  Assembled by one `runRealizes` call from the
    per-kernel realizations (each an honest leaf-bytes KAT hypothesis) and the
    generic composition law. -/
theorem frost_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (challengeStep denomInvStep mulStep addStep : C → C)
    (hChallenge : KernelRealizes decode challengeStep frostChallengeLeaf leafSpec)
    (hDenomInv : KernelRealizes decode denomInvStep frostDenomInvLeaf leafSpec)
    (hMul : KernelRealizes decode mulStep frostMulLeaf leafSpec)
    (hAdd : KernelRealizes decode addStep frostAddLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec frostLeaves oldDest xVal)
      = composeSpecs (frostSpecs challengeStep denomInvStep mulStep addStep)
          (decode xVal) :=
  sig4_realizes leafSpec decode frostChallengeLeaf frostDenomInvLeaf frostMulLeaf
    frostAddLeaf challengeStep denomInvStep mulStep addStep
    hChallenge hDenomInv hMul hAdd oldDest xVal

end CatCrypt.Crypto.SecureCompilation.SignatureProtocolKernels
