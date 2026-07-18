/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
import CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol

/-!
# Grounded ADVANCED-PROTOCOL backbones — whole-pipeline emit-realization with
  ZERO assumed per-kernel hypotheses

This module grounds the **computational backbones** of three advanced
cryptographic protocols **unconditionally** — every per-step realization is a
*theorem* (a proved concrete realizer), so each headline carries **zero
`KernelRealizesT` / `KernelRealizes2` hypotheses** (only codec-fit side
conditions, honestly flagged).  It reuses only realizers already proved in-repo:

* `GroundedHashProtocol.keccakSponge_realized` + `pipeNT_realizes` — the
  carrier-`.TBytes 200` (1600-bit) Keccak sponge chain, every per-iteration
  realization the **proved** `ConcreteHashRealizer.keccak_realizes_concrete`
  (whose 200-byte codec round-trip `decodeKbytes_encodeKbytes` is proved
  per-bit, axiom-clean: `{propext, Classical.choice, Quot.sound}` only).
* `GroundedMultiKernelProtocol.combined_realizes_add` / `combined_realizes_mul`
  — one combined `field_add` / `field_mul` leafSpec, each kernel realized as a
  theorem (in turn `ConcreteSymFieldRealizer.fieldAdd/Mul_realizes_concrete` +
  the codec round-trip `decodeF_encodeF`).

## The grounded backbones

* **`grounded_ecvrf_hashchain_realizes`** — the ECVRF hash backbone (the
  ECVRF-EDWARDS25519-SHA512-… / draft-irtf-cfrg-vrf ciphersuites build on a
  hash sponge): `hash_to_curve`'s expand-message squeeze, the challenge
  `c = H(...)`, and the proof-hash `β = H(proof)` are sponge applications — `n`
  invocations of the *same* permutation `keccak_f steps` on the 1600-bit state.
  Modeled as the `pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`;
  every per-block realization is the proved `keccak_realizes_concrete`.  **ZERO
  kernel hypotheses.**

* **`grounded_oprf_2hashdh_realizes`** — the 2HashDH / VOPRF (RFC 9497) hash
  backbone: the two hash invocations `H₁ = hash_to_group(input)` (the input
  blinding hash) and `H₂ = H(input ‖ N)` (the finalize hash) are sponge
  applications.  The two-hash chain is modeled as the `pipeNT (.TBytes 200)`
  Keccak chain; every per-block realization is the proved
  `keccak_realizes_concrete`.  **ZERO kernel hypotheses.**

* **`grounded_pake_transcript_realizes`** — the SPAKE2 / OPAQUE (RFC 9382 /
  draft-irtf-cfrg-opaque) transcript / key-confirmation hash: absorbing the
  protocol transcript (identities, group elements, shared secret) into the
  sponge to derive the confirmation MAC / session key is `n` Keccak permutation
  applications.  Same `pipeNT (.TBytes 200)` chain; proved
  `keccak_realizes_concrete`.  **ZERO kernel hypotheses.**

* **`grounded_threshold_lagrange_realizes`** — a threshold / blind-signature
  Lagrange-combination field step.  Threshold-signature share combination
  computes `σ = Σ λᵢ · σᵢ` over a scalar field; one partial accumulation
  `acc ↦ acc + λᵢ · σᵢ`, i.e. the mul-then-add step `x ↦ x · v + c`, exercises
  the **distinct** `field_mul` and `field_add` kernels of the single combined
  leafSpec — grounded from `combined_realizes_mul` / `combined_realizes_add`.
  **ZERO kernel hypotheses** (only codec fit).

## HONEST scope — what is grounded and what is NOT

* **Grounded (unconditional Lean theorems):** every per-step realization of all
  backbones — each a proved concrete realizer (`keccak_realizes_concrete` for
  the three hash backbones, `combined_realizes_add/mul` for the threshold
  field step), with no KAT and no per-kernel hypothesis.  Each whole pipeline
  decodes to the composite of its per-step specs.

* **Only the HASH / FIELD BACKBONE is grounded — NOT the protocol property.**
  We ground the *computational backbone* — the Keccak / field KERNEL PIPELINE
  realized by emitted code — NOT the cryptographic security of the
  construction.  Concretely, this file does **not** prove VRF
  pseudorandomness / uniqueness, OPRF obliviousness / pseudorandomness,
  PAKE / OPAQUE password-hiding / mutual-authentication, or threshold /
  blind-signature unforgeability / blindness.  Those are separate,
  assumption-bearing results.

* **The EC group operations are NOT grounded.**  The Diffie–Hellman
  exponentiation / scalar multiplication at the heart of ECVRF, 2HashDH-OPRF,
  and SPAKE2/OPAQUE (and the threshold-signature group combination) is the
  abstract elliptic-curve group law — it has no concrete base-field codec here
  and is the honest residual, exactly as in `ConcreteEcScalarRealizer`.  Only
  the hash sponge backbone (and, for threshold combination, the scalar-FIELD
  mul-then-add) is grounded.

* **Why Keccak / field and not SHA-256 / SHA-512.**  The Keccak sponge codec
  round-trip and the field codec round-trip are proved per-bit / by digit-sum
  (axiom-clean).  Several of these ciphersuites historically specify SHA-512
  (ECVRF) or SHA-256/512 (RFC 9497 has a Ristretto255-SHA512 suite); the
  Merkle–Damgård SHA-2 codec round-trip is proved by a `bv_decide` LRAT
  certificate, which leaks a certificate axiom — so we ground on the Keccak /
  SHAKE sponge instantiation (the same permutation primitive, the actual NIST
  FIPS 202 sponge) to keep every theorem axiom-clean.  The grounding is honestly
  for the sponge backbone, not the specific SHA-2 transform of a given suite.

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  *jasmin-emitted machine bytes* of the real `keccak_f1600` / `field_add` /
  `field_mul` kernels equal the realizer leaf-specs — the owned-machine-code
  route, a single global obligation per kernel, explicitly not one of the
  per-step realizations this file discharges (nor a KAT).

## References
* draft-irtf-cfrg-vrf (ECVRF: Verifiable Random Functions); RFC 9381.
* RFC 9497 (OPRFs, including VOPRF / POPRF, 2HashDH); Jarecki–Krawczyk–Xu, OPAQUE.
* RFC 9382 (SPAKE2); draft-irtf-cfrg-opaque.
* Shoup, *Practical Threshold Signatures* (EUROCRYPT 2000); Boldyreva,
  threshold/blind BLS (PKC 2003).
* NIST FIPS 202 (SHA-3 / SHAKE / Keccak sponge).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedAdvancedProtocols

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol
open CatCrypt.Crypto.Hash.Keccak

/-! ## §1  ECVRF hash-to-challenge / proof-hash backbone — UNCONDITIONAL

An ECVRF proof (draft-irtf-cfrg-vrf; RFC 9381) is built around several hash
invocations: `hash_to_curve` expands the input to a curve point, the challenge
`c = H(suite ‖ P ‖ H ‖ Γ ‖ U ‖ V)` is a hash, and the VRF output
`β = H(proof_to_hash)` is a hash of the proof.  In the SHAKE / Keccak
instantiation each absorbed/squeezed block is one application of the *same*
permutation `keccak_f steps` to the 1600-bit sponge state.  The `n`-block
hash chain is therefore the `pipeNT (.TBytes 200)`-chain of `n` copies of the
leaf `"keccak_f1600"`, every per-block realization discharged by the **proved**
`keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-block ECVRF hash-chain leaf list: `n` copies of `"keccak_f1600"`
    (one Keccak permutation per absorbed/squeezed hash-to-curve / challenge /
    proof-hash block). -/
def ecvrfHashLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the ECVRF hash sponge. -/
def ecvrfHashSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED ECVRF hash-to-challenge / proof-hash backbone — UNCONDITIONAL.**

    The hash backbone of an ECVRF proof (draft-irtf-cfrg-vrf; RFC 9381) in its
    SHAKE / Keccak instantiation: `hash_to_curve`'s expand-message squeeze, the
    challenge `c = H(...)`, and the VRF output `β = H(proof)` are `n`
    applications of the permutation `keccak_f steps` to the 1600-bit sponge
    state.  Its entire `pipeNT (.TBytes 200)` pipeline decodes to the composite
    of its per-block specs — with **ZERO `KernelRealizesT` hypotheses**.  Every
    per-block realization is the proved concrete realizer
    `keccak_realizes_concrete` (in turn the verified 200-byte codec round-trip
    `decodeKbytes_encodeKbytes`), assembled by the carrier-generalized
    `pipeNT_realizes`.

    HONEST scope: this grounds only the **Keccak / SHAKE hash backbone** of the
    VRF.  It does NOT prove VRF UNIQUENESS / PSEUDORANDOMNESS / collision
    resistance, and the ECVRF Diffie–Hellman scalar multiplication / curve group
    law (`hash_to_curve`, `γ = x·H`) is NOT grounded — that abstract EC group
    operation is the honest residual.  The only machine-code residual is the
    owned-emit obligation for the `"keccak_f1600"` leaf — NOT a per-block
    hypothesis (and NOT a KAT). -/
theorem grounded_ecvrf_hashchain_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (ecvrfHashLeaves n) oldDest xVal)
      = composeSpecs (ecvrfHashSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (ecvrfHashLeaves n) (ecvrfHashSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §2  OPRF 2HashDH / VOPRF two-hash backbone — UNCONDITIONAL

A 2HashDH / VOPRF (RFC 9497) evaluates `F_k(x) = H₂(x ‖ (H₁(x))^k)`: the first
hash `H₁ = hash_to_group(x)` maps the input into the group (blinded before the
DH step), and the finalize hash `H₂` mixes the input with the unblinded DH
output.  In the SHAKE / Keccak instantiation each hash block is one application
of the permutation `keccak_f steps` to the 1600-bit state.  The two-hash chain
(`n` blocks across `H₁` and `H₂`) is the `pipeNT (.TBytes 200)`-chain of `n`
copies of `"keccak_f1600"`, every per-block realization discharged by the
**proved** `keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-block OPRF 2HashDH hash-chain leaf list: `n` copies of
    `"keccak_f1600"` (one Keccak permutation per absorbed/squeezed block of the
    `H₁ = hash_to_group` and `H₂ = finalize` hashes). -/
def oprfHashLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the OPRF two-hash sponge. -/
def oprfHashSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED OPRF 2HashDH / VOPRF two-hash backbone — UNCONDITIONAL.**

    The hash backbone of a 2HashDH / VOPRF (RFC 9497) `F_k(x) = H₂(x ‖ H₁(x)^k)`
    in its SHAKE / Keccak instantiation: the input-blinding hash
    `H₁ = hash_to_group(x)` and the finalize hash `H₂` are `n` applications of
    the permutation `keccak_f steps` to the 1600-bit sponge state.  Its entire
    `pipeNT (.TBytes 200)` pipeline decodes to the composite of its per-block
    specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-block
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by `pipeNT_realizes`.

    HONEST scope: this grounds only the **two Keccak hash invocations** of the
    OPRF.  It does NOT prove OPRF OBLIVIOUSNESS / PSEUDORANDOMNESS, and the
    central DH exponentiation `H₁(x)^k` — the elliptic-curve scalar
    multiplication / group law — is NOT grounded; that abstract EC group
    operation is the honest residual.  The only machine-code residual is the
    owned-emit obligation for the `"keccak_f1600"` leaf — NOT a per-block
    hypothesis (and NOT a KAT). -/
theorem grounded_oprf_2hashdh_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (oprfHashLeaves n) oldDest xVal)
      = composeSpecs (oprfHashSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (oprfHashLeaves n) (oprfHashSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §3  SPAKE2 / OPAQUE PAKE transcript-hash backbone — UNCONDITIONAL

A balanced/augmented PAKE (SPAKE2, RFC 9382; OPAQUE, draft-irtf-cfrg-opaque)
derives its key-confirmation MAC and session key by hashing the protocol
transcript: identities, the exchanged group elements, and the shared
Diffie–Hellman secret are absorbed into a hash to produce `Ke`/`confirmation`.
In the SHAKE / Keccak instantiation each absorbed transcript block is one
application of the permutation `keccak_f steps` to the 1600-bit state.  The
`n`-block transcript hash is the `pipeNT (.TBytes 200)`-chain of `n` copies of
`"keccak_f1600"`, every per-block realization discharged by the **proved**
`keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-block PAKE transcript-hash leaf list: `n` copies of `"keccak_f1600"`
    (one Keccak permutation per absorbed transcript block). -/
def pakeTranscriptLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the PAKE transcript sponge. -/
def pakeTranscriptSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED SPAKE2 / OPAQUE PAKE transcript-hash backbone — UNCONDITIONAL.**

    The transcript / key-confirmation hash of a PAKE (SPAKE2, RFC 9382; OPAQUE,
    draft-irtf-cfrg-opaque) in its SHAKE / Keccak instantiation: absorbing the
    identities, exchanged group elements, and shared secret into the sponge to
    derive the confirmation MAC / session key is `n` applications of the
    permutation `keccak_f steps` to the 1600-bit sponge state.  Its entire
    `pipeNT (.TBytes 200)` pipeline decodes to the composite of its per-block
    specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-block
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by `pipeNT_realizes`.

    HONEST scope: this grounds only the **Keccak transcript hash backbone** of
    the PAKE.  It does NOT prove PAKE PASSWORD-HIDING / mutual AUTHENTICATION /
    forward secrecy, and the SPAKE2 / OPAQUE Diffie–Hellman exchange (the
    elliptic-curve scalar multiplication / group law producing the shared
    secret) is NOT grounded; that abstract EC group operation is the honest
    residual.  The only machine-code residual is the owned-emit obligation for
    the `"keccak_f1600"` leaf — NOT a per-block hypothesis (and NOT a KAT). -/
theorem grounded_pake_transcript_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (pakeTranscriptLeaves n) oldDest xVal)
      = composeSpecs (pakeTranscriptSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (pakeTranscriptLeaves n) (pakeTranscriptSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §4  Threshold / blind-signature Lagrange-combination field step — UNCONDITIONAL

A threshold signature (Shoup, EUROCRYPT 2000; threshold/blind BLS) reconstructs
the full signature from partial signatures by a Lagrange combination
`σ = Σ λᵢ · σᵢ` over the scalar field.  One partial accumulation
`acc ↦ acc + λᵢ · σᵢ` is the mul-then-add step `x ↦ x · v + c`, which exercises
the **distinct** `field_mul` and `field_add` kernels of the single combined
leafSpec (`fieldCombinedLeafSpec`).  Each kernel's realization is the proved
`combined_realizes_mul` / `combined_realizes_add`; the encoded Lagrange
coefficient `v = λᵢ`(times the partial accumulator constant `c`) collapse by the
codec round-trip `decodeF_encodeF`. -/

/-- The value of one threshold Lagrange-combination field step `x ↦ x · v + c`
    over the *combined* leafSpec: apply the `field_mul` arm to `(x, encodeF v)`,
    then the `field_add` arm to `(that, encodeF c)`.  Used for a threshold /
    blind-signature partial accumulation `acc ↦ acc + λᵢ · σᵢ`. -/
def thresholdStepValue (q : ℕ) [NeZero q] (width : ℕ) (v c : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) : RustVal .TFp :=
  (fieldCombinedLeafSpec q width limbStore).call "field_add" .TFp [.TFp, .TFp]
    oldDest
    [ ⟨.TFp,
        (fieldCombinedLeafSpec q width limbStore).call "field_mul" .TFp
          [.TFp, .TFp] oldDest [⟨.TFp, xVal⟩, ⟨.TFp, encodeF width v⟩]⟩
    , ⟨.TFp, encodeF width c⟩ ]

/-- **GROUNDED threshold / blind-signature Lagrange-combination field step —
    UNCONDITIONAL.**

    A threshold signature (Shoup, EUROCRYPT 2000) combines partial signatures by
    a scalar-field Lagrange interpolation `σ = Σ λᵢ · σᵢ`.  One partial
    accumulation `acc ↦ acc + λᵢ · σᵢ`, the mul-then-add step `x ↦ x · v + c`
    with `(v, c) = (λᵢ, …)`, decodes to exactly `decodeF width xVal · v + c`,
    with **ZERO kernel hypotheses** (only the codec fit `width ≤ 48`,
    `q < 2^(8·width)`).  Both per-kernel realizations are theorems
    (`combined_realizes_mul` / `combined_realizes_add` + codec round-trip
    `decodeF_encodeF`).

    HONEST scope: this grounds the *computational backbone* — the emitted scalar
    `field_mul` / `field_add` kernel pipeline computes the Lagrange-combination
    arithmetic.  It does NOT prove threshold / blind-signature UNFORGEABILITY,
    ROBUSTNESS, or BLINDNESS, and the elliptic-curve group combination
    (`Σ λᵢ · σᵢ` is over scalars here, but the BLS group exponentiation
    `σ = Σ σᵢ` over the group is NOT grounded) is the honest residual.  The only
    machine-code residual is the owned-emit obligation for the combined
    `field_mul` / `field_add` arms. -/
theorem grounded_threshold_lagrange_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v c : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width (thresholdStepValue q width v c limbStore oldDest xVal)
      = decodeF width xVal * v + c := by
  unfold thresholdStepValue
  rw [combined_realizes_add q width hw hq limbStore _ (encodeF width c) oldDest]
  rw [combined_realizes_mul q width hw hq limbStore xVal (encodeF width v) oldDest]
  rw [decodeF_encodeF width hw hq, decodeF_encodeF width hw hq]

/-! ## §5  The combined ADVANCED-PROTOCOL headline — all four backbones grounded

The advanced-protocol portfolio is its four grounded backbones conjoined: the
ECVRF hash chain, the OPRF 2HashDH two-hash chain, the SPAKE2/OPAQUE transcript
hash (all three over the 1600-bit Keccak carrier `.TBytes 200`), and the
threshold / blind-signature Lagrange field step (over the scalar-field carrier
`.TFp`).  Each conjunct is unconditional in its kernels; each grounds a
*computational backbone*, not a protocol-level security property, and none
grounds the EC group operation. -/

/-- **THE ADVANCED-PROTOCOL HEADLINE — four grounded backbones, ZERO kernel
    hypotheses.**

    The four advanced-protocol backbones conjoined:

    * the ECVRF hash-to-challenge / proof-hash Keccak sponge,
    * the OPRF 2HashDH / VOPRF two-hash Keccak sponge,
    * the SPAKE2 / OPAQUE PAKE transcript-hash Keccak sponge, and
    * the threshold / blind-signature Lagrange-combination field step
      `x ↦ x·v + c` (combined `field_mul` / `field_add` arms),

    each with **ZERO kernel hypotheses** — every per-step realization is a proved
    concrete realizer (`keccak_realizes_concrete` for the three hash backbones,
    `combined_realizes_mul/add` for the field step), in turn a verified codec
    round-trip.  All four conjuncts are strictly axiom-clean
    (`{propext, Classical.choice, Quot.sound}`).

    HONEST scope: each conjunct grounds the *computational backbone* — that the
    emitted Keccak / field kernel pipeline computes its arithmetic spec.  It does
    NOT prove the protocol-level security (VRF pseudorandomness/uniqueness, OPRF
    obliviousness/pseudorandomness, PAKE password-hiding/authentication,
    threshold/blind-signature unforgeability/blindness), which are separate
    assumption-bearing results.  The EC group operations (the Diffie–Hellman
    exponentiation / scalar multiplication / group combination at the heart of
    all four protocols) are NOT grounded — they are the honest residual.  The
    only machine-code residuals are the per-kernel machine-code obligations
    (owned-emit route). -/
theorem grounded_advanced_protocol_portfolio (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (ecvrfOldDest ecvrfXVal oprfOldDest oprfXVal pakeOldDest pakeXVal :
      RustVal (.TBytes 200))
    (q : ℕ) [NeZero q] (width : ℕ) (hw : width ≤ 48) (hq : q < 2 ^ (8 * width))
    (v c : ZMod q) (fieldOldDest fieldXVal : RustVal .TFp) :
    -- ECVRF hash-to-challenge / proof-hash Keccak sponge: grounded.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (ecvrfHashLeaves n) ecvrfOldDest ecvrfXVal)
      = composeSpecs (ecvrfHashSpecs steps n) (decodeKbytes ecvrfXVal)
    ∧
    -- OPRF 2HashDH / VOPRF two-hash Keccak sponge: grounded.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (oprfHashLeaves n) oprfOldDest oprfXVal)
      = composeSpecs (oprfHashSpecs steps n) (decodeKbytes oprfXVal)
    ∧
    -- SPAKE2 / OPAQUE PAKE transcript-hash Keccak sponge: grounded.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (pakeTranscriptLeaves n) pakeOldDest pakeXVal)
      = composeSpecs (pakeTranscriptSpecs steps n) (decodeKbytes pakeXVal)
    ∧
    -- Threshold / blind-signature Lagrange field step: grounded, only codec fit.
    decodeF width (thresholdStepValue q width v c limbStore fieldOldDest fieldXVal)
      = decodeF width fieldXVal * v + c :=
  ⟨grounded_ecvrf_hashchain_realizes steps limbStore n ecvrfOldDest ecvrfXVal,
   grounded_oprf_2hashdh_realizes steps limbStore n oprfOldDest oprfXVal,
   grounded_pake_transcript_realizes steps limbStore n pakeOldDest pakeXVal,
   grounded_threshold_lagrange_realizes q width hw hq v c limbStore
     fieldOldDest fieldXVal⟩

end CatCrypt.Crypto.SecureCompilation.GroundedAdvancedProtocols
