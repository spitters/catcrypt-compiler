/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol

/-!
# Grounded TRANSPORT-HANDSHAKE key-schedule backbones — whole-pipeline
  emit-realization with ZERO assumed per-kernel hypotheses, over the PROVED
  Keccak concrete realizer

A transport handshake (TLS 1.3, Noise, WireGuard, Signal) is, at the
computational level, a structured chain of HKDF / hash steps over a running
key-schedule state.  Once the underlying PRF permutation's per-iteration
realization is a *theorem* — and it is, `ConcreteHashRealizer.keccak_realizes_concrete`
— the whole handshake key-schedule **backbone** is grounded with **zero
`KernelRealizesT` hypotheses**.

This module reuses the carrier-`.TBytes 200` (1600-bit) Keccak-sponge grounding
already proved in-repo — `GroundedHashProtocol.keccakSponge_realized` +
`pipeNT_realizes`, every per-iteration realization the **proved**
`keccak_realizes_concrete` (whose codec round-trip `decodeKbytes_encodeKbytes` is
proved per-bit, *axiom-clean*: `{propext, Classical.choice, Quot.sound}` only) —
to ground the **SHA-3 / Keccak-sponge key-schedule backbones of real transport
handshakes**.  Each handshake's key schedule is, at the leaf level, a chain of
the *same* permutation iterated on a running sponge/extract state; the whole
backbone is therefore a `pipeNT (.TBytes 200)` chain whose every step is
discharged by the proved realizer.

## The three grounded handshake key-schedule backbones (all SHA-3 / Keccak)

* **`grounded_tls13_key_schedule_realizes`** — the TLS 1.3 key schedule (RFC 8446
  §7.1): the cascade `Early Secret → Handshake Secret → Master Secret`, each an
  `HKDF-Extract`, interleaved with the `Derive-Secret` / `HKDF-Expand-Label`
  traffic-key derivations.  In a SHA-3 / KMAC instantiation of HKDF (admitted by
  NIST SP 800-56C Rev. 2) every Extract and every Expand-Label step advances the
  *same* 1600-bit Keccak sponge by one `keccak_f steps` permutation.  We model the
  `n`-step Extract/Derive ladder as the `pipeNT (.TBytes 200)`-chain of `n` copies
  of `"keccak_f1600"`, every per-step realization discharged by the proved
  `keccak_realizes_concrete`.  **ZERO `KernelRealizesT` hypotheses.**

* **`grounded_noise_mixkey_realizes`** — the Noise-protocol `MixKey` / `MixHash`
  ladder (Noise spec rev. 34; e.g. `Noise_XX`): each handshake message updates the
  chaining key `ck` and hash `h` by an `HKDF(ck, input)` / `HASH(h ‖ data)` step.
  In a SHA-3 instantiation each `MixKey` / `MixHash` is one `keccak_f steps`
  permutation on the 1600-bit state.  We model the `n`-message ladder as the
  `pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`, every per-step
  realization discharged by the proved `keccak_realizes_concrete`.  **ZERO
  `KernelRealizesT` hypotheses.**

* **`grounded_wireguard_kdf_chain_realizes`** — the WireGuard / Signal-style KDF
  ratchet chain: WireGuard's handshake derives successive keys by repeated
  `HKDF(C, input)` (Noise_IKpsk2 chaining; WireGuard whitepaper §5.4), and the
  Signal double-ratchet's symmetric-key chain is repeated `KDF_CK` / `HKDF`
  applications.  In a SHA-3 instantiation each chain step is one `keccak_f steps`
  permutation on the 1600-bit state.  We model the `n`-step chain as the
  `pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`, every per-step
  realization discharged by the proved `keccak_realizes_concrete`.  **ZERO
  `KernelRealizesT` hypotheses.**

## HONEST scope — what is grounded and what is NOT

* **The COMPUTATIONAL BACKBONE is grounded, NOT the handshake's SECURITY.**  What
  these theorems establish is that the *emitted HKDF / Keccak-sponge kernel
  pipeline* of each handshake key schedule **computes its arithmetic / hash
  spec** — the per-step permutation chain decodes to the composite of its
  per-step specs.  They do **NOT** establish any handshake *security* property:
  not key-indistinguishability, not forward secrecy, not the
  authenticated-key-exchange (AKE) / SIGMA-style security of TLS 1.3, Noise, or
  WireGuard.  Those are game-based / UC results about the abstract protocol, and
  are entirely out of scope here.  The chain *structure* is modeled; the PRF is
  the Keccak sponge.

* **Grounded (unconditional Lean theorem):** every per-step realization of all
  three backbones.  Each is the proved `keccak_realizes_concrete` (in turn the
  verified codec round-trip `decodeKbytes_encodeKbytes`), with no KAT, no abstract
  section assumption, and no per-kernel hypothesis.  Each whole `pipeNT` pipeline
  decodes to the composite of its per-step specs.

* **Why SHA-3 / Keccak and not the HMAC-SHA-256 route.**  Real TLS 1.3 uses
  HMAC-SHA-256-based HKDF, but (a) the binary keyed hash `hmacSha256` has **no**
  proved concrete realizer in-repo (the HMAC registry row is a *hypothesis*
  predicate, not a proved realizer), and (b) the SHA-256 compression codec
  round-trip `decodeSbytes_encodeSbytes` is proved by a `bv_decide` LRAT
  certificate, which introduces a certificate axiom.  To keep every theorem in
  this file strictly axiom-clean (`{propext, Classical.choice, Quot.sound}` only)
  we ground the handshake key-schedule backbones on the **Keccak** permutation,
  whose codec round-trip is proved per-bit with no `bv_decide` axiom.  This is a
  genuine substitution: TLS 1.3 as specified is HMAC-SHA-256; we ground the SHA-3
  / KMAC-HKDF instantiation of the same Extract/Expand ladder structure, and say
  so.  (NIST SP 800-56C Rev. 2 admits SHA-3/KMAC as an HKDF PRF; Noise and
  WireGuard are PRF-agnostic over their HKDF.)

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  *jasmin-emitted machine bytes* of the real `keccak_f1600` kernel equal the
  realizer leaf-spec — the owned-machine-code route, a single global obligation
  per kernel, explicitly not one of the per-step realizations this file discharges
  (nor a KAT).  The non-hash handshake arithmetic (X25519 / P-256 DH shared-secret
  computation, AEAD record protection) is likewise out of scope: only the
  hash/sponge key-schedule backbone is grounded here.

## References
* RFC 8446 §7.1 (TLS 1.3 key schedule: Early/Handshake/Master Secret, HKDF-Extract,
  Derive-Secret, HKDF-Expand-Label); RFC 5869 (HKDF).
* Trevor Perrin, "The Noise Protocol Framework" rev. 34 (`MixKey` / `MixHash`,
  `Noise_XX`).
* J. A. Donenfeld, "WireGuard: Next Generation Kernel Network Tunnel", NDSS 2017
  (§5.4 handshake KDF chain, Noise_IKpsk2); Signal double-ratchet (`KDF_CK`).
* NIST SP 800-56C Rev. 2 (SHA-3/KMAC as HKDF PRF); FIPS 202 (Keccak / SHA-3 / SHAKE).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedHandshake

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.Hash.Keccak

/-! ## §1  TLS 1.3 key schedule (RFC 8446 §7.1) — UNCONDITIONAL

The TLS 1.3 key schedule (RFC 8446 §7.1) is the cascade
`Early Secret → Handshake Secret → Master Secret`, each an `HKDF-Extract`, with
the per-stage `Derive-Secret(secret, label, transcript)` calls (each an
`HKDF-Expand-Label`, RFC 8446 §7.1) producing traffic / finished keys.  In a
SHA-3 / KMAC instantiation of HKDF (NIST SP 800-56C Rev. 2) every Extract and
every Expand-Label step drives the *same* 1600-bit Keccak sponge by one
`keccak_f steps` permutation.  The `n`-step Extract/Derive ladder is therefore
the `pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`, every per-step
realization discharged by the **proved** `keccak_realizes_concrete` — no
hypothesis. -/

/-- The `n`-step TLS 1.3 key-schedule leaf list: `n` copies of `"keccak_f1600"`
    (one Keccak permutation per HKDF-Extract / HKDF-Expand-Label step of the
    Early→Handshake→Master ladder and its Derive-Secret traffic-key calls). -/
def tls13KeyScheduleLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-step spec list: `n` copies of the permutation
    `keccak_f steps` driving the TLS 1.3 key-schedule sponge. -/
def tls13KeyScheduleSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED TLS 1.3 key-schedule backbone — UNCONDITIONAL.**

    The TLS 1.3 key schedule (RFC 8446 §7.1) in its SHA-3 / KMAC-HKDF
    instantiation: the `Early Secret → Handshake Secret → Master Secret` cascade
    (each an `HKDF-Extract`) and the `Derive-Secret` / `HKDF-Expand-Label`
    traffic-key derivations are `n` applications of the permutation
    `keccak_f steps` to the 1600-bit sponge state.  Its entire
    `pipeNT (.TBytes 200)` pipeline decodes to the composite of its per-step
    specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-step
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by the carrier-generalized `pipeNT_realizes`.

    HONEST scope: this grounds the **computational KDF backbone** — that the
    emitted Keccak-sponge pipeline of the key schedule computes its hash spec.  It
    does **NOT** ground any TLS 1.3 *security* property (key-indistinguishability,
    forward secrecy, the SIGMA-style authenticated-key-exchange guarantee) — those
    are separate game-based / UC results about the abstract handshake.  Real TLS
    1.3 uses HMAC-SHA-256-based HKDF; we ground the SHA-3 / KMAC-HKDF
    instantiation of the same Extract/Expand-Label ladder to stay strictly
    axiom-clean (`hmacSha256` has no proved realizer, and the SHA-256 codec uses a
    `bv_decide` certificate axiom).  The only machine-code residual is the
    owned-emit obligation for the `"keccak_f1600"` leaf — NOT a per-step
    hypothesis (and NOT a KAT). -/
theorem grounded_tls13_key_schedule_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (tls13KeyScheduleLeaves n) oldDest xVal)
      = composeSpecs (tls13KeyScheduleSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (tls13KeyScheduleLeaves n) (tls13KeyScheduleSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §2  Noise-protocol MixKey / MixHash ladder — UNCONDITIONAL

The Noise framework (Perrin, rev. 34) advances its `SymmetricState` per handshake
message by `MixKey(input)` — an `HKDF(ck, input)` that re-derives the chaining key
`ck` and message key — and `MixHash(data)` — a `HASH(h ‖ data)`.  For a pattern
such as `Noise_XX` the handshake is a fixed sequence of such mixes.  In a SHA-3
instantiation each `MixKey` / `MixHash` is one `keccak_f steps` permutation on the
1600-bit state.  The `n`-message ladder is the `pipeNT (.TBytes 200)`-chain of `n`
copies of `"keccak_f1600"`, every per-step realization discharged by the
**proved** `keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-step Noise `MixKey` / `MixHash` leaf list: `n` copies of
    `"keccak_f1600"` (one Keccak permutation per `HKDF` / `HASH` mix step). -/
def noiseMixKeyLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-step spec list: `n` copies of the permutation
    `keccak_f steps` driving the Noise `SymmetricState` sponge. -/
def noiseMixKeySpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED Noise `MixKey` / `MixHash` ladder — UNCONDITIONAL.**

    The Noise-protocol (`Noise_XX`, Perrin rev. 34) `SymmetricState` ladder: each
    handshake message updates the chaining key and hash by an `HKDF(ck, input)`
    `MixKey` and a `HASH(h ‖ data)` `MixHash`, `n` applications of the permutation
    `keccak_f steps` to the 1600-bit state in a SHA-3 instantiation.  Its entire
    `pipeNT (.TBytes 200)` pipeline decodes to the composite of its per-step
    specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-step
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by `pipeNT_realizes`.

    HONEST scope: this grounds the **computational KDF backbone** — that the
    emitted Keccak-sponge pipeline of the Noise mix ladder computes its hash spec.
    It does **NOT** ground Noise's *security* (the channel-binding / AKE
    guarantees of `Noise_XX`).  Noise is PRF-agnostic over its HKDF; we instantiate
    with the Keccak sponge to stay strictly axiom-clean.  The only machine-code
    residual is the owned-emit obligation for the `"keccak_f1600"` leaf — NOT a
    per-step hypothesis (and NOT a KAT).  The Diffie-Hellman shared-secret inputs
    to each `MixKey` (X25519) and the AEAD payload encryption are out of scope —
    only the hash/sponge mix backbone is grounded. -/
theorem grounded_noise_mixkey_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (noiseMixKeyLeaves n) oldDest xVal)
      = composeSpecs (noiseMixKeySpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (noiseMixKeyLeaves n) (noiseMixKeySpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §3  WireGuard / Signal-style KDF ratchet chain — UNCONDITIONAL

WireGuard (Donenfeld, NDSS 2017, §5.4, Noise_IKpsk2) derives successive handshake
keys by repeated `HKDF(C, input)` on a running chaining value `C`; the Signal
double-ratchet's symmetric-key chain is repeated `KDF_CK` / `HKDF` applications.
Both are an unbounded chain of the same HKDF step on a running secret.  In a SHA-3
instantiation each chain step is one `keccak_f steps` permutation on the 1600-bit
state.  The `n`-step chain is the `pipeNT (.TBytes 200)`-chain of `n` copies of
`"keccak_f1600"`, every per-step realization discharged by the **proved**
`keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-step WireGuard / Signal KDF-chain leaf list: `n` copies of
    `"keccak_f1600"` (one Keccak permutation per `HKDF` / `KDF_CK` ratchet step). -/
def wireguardKdfChainLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-step spec list: `n` copies of the permutation
    `keccak_f steps` driving the WireGuard / Signal KDF chain. -/
def wireguardKdfChainSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED WireGuard / Signal KDF-chain backbone — UNCONDITIONAL.**

    The WireGuard handshake KDF chain (Donenfeld, NDSS 2017, §5.4; Noise_IKpsk2)
    and the Signal double-ratchet symmetric-key chain: successive keys are derived
    by repeated `HKDF(C, input)` / `KDF_CK` on a running chaining value, `n`
    applications of the permutation `keccak_f steps` to the 1600-bit state in a
    SHA-3 instantiation.  Its entire `pipeNT (.TBytes 200)` pipeline decodes to the
    composite of its per-step specs — with **ZERO `KernelRealizesT` hypotheses**.
    Every per-step realization is the proved concrete realizer
    `keccak_realizes_concrete` (in turn the verified 200-byte codec round-trip
    `decodeKbytes_encodeKbytes`), assembled by `pipeNT_realizes`.

    HONEST scope: this grounds the **computational KDF backbone** — that the
    emitted Keccak-sponge ratchet pipeline computes its hash spec.  It does **NOT**
    ground WireGuard's or Signal's *security* (forward secrecy, post-compromise
    security / the ratchet's healing guarantee).  We instantiate the HKDF PRF with
    the Keccak sponge to stay strictly axiom-clean.  The only machine-code residual
    is the owned-emit obligation for the `"keccak_f1600"` leaf — NOT a per-step
    hypothesis (and NOT a KAT).  The X25519 DH inputs mixed into each ratchet step
    are out of scope — only the hash/sponge chain backbone is grounded. -/
theorem grounded_wireguard_kdf_chain_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (wireguardKdfChainLeaves n) oldDest xVal)
      = composeSpecs (wireguardKdfChainSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (wireguardKdfChainLeaves n) (wireguardKdfChainSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §4  The combined HANDSHAKE headline — all three backbones grounded

The transport-handshake portfolio is its three grounded SHA-3 key-schedule
backbones conjoined: the TLS 1.3 Early→Handshake→Master HKDF ladder, the Noise
`MixKey` / `MixHash` ladder, and the WireGuard / Signal KDF ratchet chain.  All
three drive the 1600-bit Keccak sponge (carrier `.TBytes 200`), so the
conjunction is over one carrier; each conjunct is unconditional in its kernels. -/

/-- **THE HANDSHAKE HEADLINE — three grounded SHA-3 key-schedule backbones, ZERO
    kernel hypotheses.**

    The SHA-3 transport-handshake key-schedule backbones conjoined, each an
    `n`-step `pipeNT (.TBytes 200)` Keccak-permutation pipeline decoding to the
    composite of `n` `keccak_f steps` specs:

    * the TLS 1.3 Early→Handshake→Master HKDF-Extract / Derive-Secret ladder
      (RFC 8446 §7.1),
    * the Noise `MixKey` / `MixHash` ladder (`Noise_XX`), and
    * the WireGuard / Signal KDF ratchet chain (Noise_IKpsk2 / `KDF_CK`),

    each with **ZERO `KernelRealizesT` hypotheses** — every per-step realization
    is the proved concrete realizer `keccak_realizes_concrete` (in turn the
    verified codec round-trip `decodeKbytes_encodeKbytes`).  All three are
    axiom-clean (`{propext, Classical.choice, Quot.sound}`).

    HONEST scope: only the **computational KDF backbones** (the emitted
    Keccak-sponge pipelines compute their hash specs) are grounded — NOT the
    handshakes' *security* (key-indistinguishability, forward secrecy, the
    authenticated-key-exchange guarantee of TLS 1.3 / Noise / WireGuard), which are
    separate game-based / UC results.  Real TLS 1.3 uses HMAC-SHA-256-based HKDF;
    we ground the SHA-3 / KMAC-HKDF instantiation of the same ladder structure to
    stay axiom-clean.  The only residual is the per-kernel machine-code obligation
    for `"keccak_f1600"` (the owned-emit route); the DH and AEAD record arithmetic
    are out of scope. -/
theorem grounded_handshake_portfolio (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (tlsOldDest tlsXVal noiseOldDest noiseXVal wgOldDest wgXVal :
      RustVal (.TBytes 200)) :
    -- TLS 1.3 Early→Handshake→Master HKDF ladder: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (tls13KeyScheduleLeaves n) tlsOldDest tlsXVal)
      = composeSpecs (tls13KeyScheduleSpecs steps n) (decodeKbytes tlsXVal)
    ∧
    -- Noise MixKey / MixHash ladder: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (noiseMixKeyLeaves n) noiseOldDest noiseXVal)
      = composeSpecs (noiseMixKeySpecs steps n) (decodeKbytes noiseXVal)
    ∧
    -- WireGuard / Signal KDF ratchet chain: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (wireguardKdfChainLeaves n) wgOldDest wgXVal)
      = composeSpecs (wireguardKdfChainSpecs steps n) (decodeKbytes wgXVal) :=
  ⟨grounded_tls13_key_schedule_realizes steps limbStore n tlsOldDest tlsXVal,
   grounded_noise_mixkey_realizes steps limbStore n noiseOldDest noiseXVal,
   grounded_wireguard_kdf_chain_realizes steps limbStore n wgOldDest wgXVal⟩

end CatCrypt.Crypto.SecureCompilation.GroundedHandshake
