/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol

/-!
# Grounded KDF / KEM backbones — whole-pipeline emit-realization with ZERO
  assumed per-kernel hypotheses, over the PROVED Keccak concrete realizer

`GroundedHashProtocol` grounds a Keccak sponge from the **proved**, unconditional
concrete realizer `ConcreteHashRealizer.keccak_realizes_concrete` — carrier
`.TBytes 200` (1600 bits), codec round-trip `decodeKbytes_encodeKbytes` (a
theorem, proved per-bit, *axiom-clean*: only `propext` / `Classical.choice` /
`Quot.sound`).

This module reuses that proved realizer — through the same carrier-parametric
composition law `GroundedHashProtocol.pipeNT_realizes` — to ground the
**SHA-3 / Keccak hash-iteration backbones of real KDF / KEM constructions**.  A
KDF or a KEM key schedule is, at the leaf level, a chain of the *same* permutation
iterated on a running sponge state; once that permutation's per-iteration
realization is a theorem (it is — `keccak_realizes_concrete`), the whole KDF / KEM
backbone is grounded with **zero `KernelRealizesT` hypotheses**.

## The three grounded backbones (all SHA-3 / Keccak)

* **`grounded_sha3_hkdf_realizes`** — a SHA-3-based HKDF Extract→Expand chain
  (the KMAC / cSHAKE realization of HKDF; NIST SP 800-56C Rev. 2 admits
  SHA-3/KMAC as the KDF PRF).  Both HKDF phases — Extract (compress salt/IKM into
  the PRK sponge state) and Expand (squeeze output keying material) — advance the
  *same* 1600-bit sponge by one `keccak_f steps` permutation per absorbed/squeezed
  block.  We model the `n`-block Extract→Expand run as the
  `pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`, every per-block
  realization discharged by the proved `keccak_realizes_concrete`.  **ZERO
  `KernelRealizesT` hypotheses.**

* **`grounded_sha3_kdf_squeeze_realizes`** — a SHA-3 / SHAKE XOF used directly as
  a KDF (FIPS 202 / SP 800-185; e.g. ML-KEM's `KDF` / `J`).  Producing keystream
  from the sponge is `n` iterations of the *same* permutation `keccak_f steps`
  over the 1600-bit state.  We model the squeeze as the `pipeNT (.TBytes 200)`
  chain of `n` copies of `"keccak_f1600"`, every per-iteration realization
  discharged by the proved `keccak_realizes_concrete`.  **ZERO `KernelRealizesT`
  hypotheses.**

* **`grounded_kem_decaps_backbone_realizes`** — the KEM session-key derivation
  backbone of an FO-transform KEM (e.g. ML-KEM `Decaps` / `Encaps`, FIPS 203):
  the shared secret is hashed and a key schedule is squeezed from a Keccak sponge.
  The backbone is `n` iterations of `keccak_f steps` on the 1600-bit hash/sponge
  state, every per-iteration realization discharged by the proved
  `keccak_realizes_concrete`.  **ZERO `KernelRealizesT` hypotheses.**

## HONEST scope — what is grounded and what is NOT

* **Grounded (unconditional Lean theorem):** every per-block / per-iteration
  realization of all three backbones.  Each is the proved
  `keccak_realizes_concrete` (in turn the verified codec round-trip
  `decodeKbytes_encodeKbytes`), with no KAT, no abstract section assumption, and
  no per-kernel hypothesis.  Each whole `pipeNT` pipeline decodes to the composite
  of its per-step specs.

* **Why SHA-3 / Keccak and not the SHA-2 / HMAC route.**  HKDF is classically
  defined over HMAC-SHA-256, but (a) the binary keyed hash `hmacSha256` has **no**
  proved concrete realizer in-repo (the HMAC registry row
  `HmacKernelRegistryEntry.HmacKernelRealizes` is a *hypothesis* predicate, not a
  proved realizer), so the HMAC wrapper cannot be grounded here, and (b) the
  SHA-256 compression codec round-trip `decodeSbytes_encodeSbytes` is proved by a
  `bv_decide` LRAT certificate (`wordOfBytes_split`), which introduces a
  certificate axiom.  To keep every theorem in this file axiom-clean
  (`{propext, Classical.choice, Quot.sound}` only) we ground the KDF/KEM backbones
  on the **Keccak** permutation, whose codec round-trip is proved per-bit with no
  `bv_decide` axiom and which is also the actual PRF of SP 800-56C's SHA-3/KMAC
  KDF and of ML-KEM's hash/sponge key schedule.

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  *jasmin-emitted machine bytes* of the real `keccak_f1600` kernel equal the
  realizer leaf-spec — the owned-machine-code route, a single global obligation
  per kernel, explicitly not one of the per-iteration realizations this file
  discharges (nor a KAT).  The KEM's lattice arithmetic (NTT, sampling,
  re-encryption check) is likewise out of scope: only the hash/sponge backbone is
  grounded here.

## References
* RFC 5869 (HKDF); NIST SP 800-56C Rev. 2, SP 800-108 (KDFs, SHA-3/KMAC PRF).
* NIST FIPS 202 (SHA-3 / SHAKE / sponge), SP 800-185 (cSHAKE / KMAC XOFs).
* NIST FIPS 203 (ML-KEM); Fujisaki–Okamoto transform (KEM Decaps/Encaps).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedKdfKem

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.Hash.Keccak

/-! ## §1  SHA-3-based HKDF Extract→Expand chain — UNCONDITIONAL

HKDF (RFC 5869) is `HKDF-Extract` then `HKDF-Expand`.  In the SHA-3 / KMAC
realization (admitted by NIST SP 800-56C Rev. 2) both phases drive the *same*
1600-bit Keccak sponge: Extract absorbs salt and input keying material into the
PRK state, Expand squeezes the output keying material — each absorbed or squeezed
block costs one application of the permutation `keccak_f steps`.  Fixing the step
mappings, the `n`-block Extract→Expand run is the `pipeNT (.TBytes 200)`-chain of
`n` copies of the leaf `"keccak_f1600"`, every per-block realization discharged by
the **proved** `keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-block SHA-3 HKDF (Extract→Expand) leaf list: `n` copies of
    `"keccak_f1600"` (one permutation per absorbed/squeezed sponge block). -/
def sha3HkdfLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the HKDF sponge. -/
def sha3HkdfSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED SHA-3 HKDF Extract→Expand chain — UNCONDITIONAL.**

    A SHA-3 / KMAC realization of HKDF (RFC 5869; NIST SP 800-56C Rev. 2): the
    Extract and Expand phases drive the same 1600-bit Keccak sponge, one
    `keccak_f steps` permutation per absorbed/squeezed block, `n` blocks in total.
    Its entire `pipeNT (.TBytes 200)` pipeline decodes to the composite of its
    per-block specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-block
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by the carrier-generalized `pipeNT_realizes`.

    Honest scope: this grounds HKDF in its **SHA-3 / Keccak-permutation**
    realization.  The classical HMAC-SHA-256 realization is NOT grounded here —
    `hmacSha256` has no proved concrete realizer in-repo, and the SHA-256 codec
    round-trip uses a `bv_decide` certificate axiom; grounding on Keccak keeps
    this theorem axiom-clean.

    The only residual is the machine-code obligation — that the jasmin-emitted
    bytes of the real `keccak_f1600` kernel equal the realizer — the
    owned-machine-code route, NOT a per-block hypothesis (and NOT a KAT). -/
theorem grounded_sha3_hkdf_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (sha3HkdfLeaves n) oldDest xVal)
      = composeSpecs (sha3HkdfSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (sha3HkdfLeaves n) (sha3HkdfSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §2  SHA-3 / SHAKE KDF squeeze — UNCONDITIONAL

A SHA-3 / SHAKE XOF used directly as a KDF (NIST FIPS 202, SP 800-185 — e.g.
ML-KEM's `KDF` / `J` hash) produces keying material by *squeezing* the sponge:
after absorbing, each output rate-block costs one application of the permutation
`keccak_f steps` to the 1600-bit state.  The `n`-block squeeze is the
`pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`, every
per-iteration realization discharged by the **proved** `keccak_realizes_concrete`
— no hypothesis. -/

/-- The `n`-squeeze-block SHA-3/SHAKE KDF leaf list: `n` copies of
    `"keccak_f1600"` (one permutation per squeezed rate block). -/
def sha3KdfLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps`. -/
def sha3KdfSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED SHA-3 / SHAKE KDF squeeze — UNCONDITIONAL.**

    A SHA-3 / SHAKE-based KDF (FIPS 202 / SP 800-185 XOF-as-KDF; e.g. ML-KEM's
    `KDF` / `J`): producing `n` rate-blocks of keying material costs `n`
    applications of the permutation `keccak_f steps` to the 1600-bit sponge state.
    Its entire `pipeNT (.TBytes 200)` pipeline decodes to the composite of its
    per-block specs — with **ZERO `KernelRealizesT` hypotheses**.  Every
    per-iteration realization is the proved concrete realizer
    `keccak_realizes_concrete` (in turn the verified 200-byte codec round-trip
    `decodeKbytes_encodeKbytes`), assembled by `pipeNT_realizes`.

    The only residual is the machine-code obligation for the `"keccak_f1600"`
    leaf — the owned-machine-code route, NOT a per-block hypothesis (and NOT a
    KAT). -/
theorem grounded_sha3_kdf_squeeze_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (sha3KdfLeaves n) oldDest xVal)
      = composeSpecs (sha3KdfSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (sha3KdfLeaves n) (sha3KdfSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §3  KEM Decaps / Encaps session-key backbone — UNCONDITIONAL

An FO-transform KEM (e.g. ML-KEM, FIPS 203) derives the session key in `Decaps` /
`Encaps` by hashing the shared secret and squeezing a key schedule from a Keccak
sponge: `K = KDF(shared_secret ‖ …)`, the SHA-3 hash/sponge advanced one
permutation per absorbed/squeezed block.  The session-key backbone is therefore
`n` iterations of `keccak_f steps` over the 1600-bit hash/sponge state — exactly
the same proved-`keccak_realizes_concrete` skeleton, here named for the KEM key
schedule.  **ZERO `KernelRealizesT` hypotheses.** -/

/-- The `n`-block KEM session-key backbone leaf list: `n` copies of
    `"keccak_f1600"` (the SHA-3 hash/sponge of the KEM key schedule). -/
def kemDecapsLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the KEM key schedule's sponge. -/
def kemDecapsSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED KEM Decaps / Encaps session-key backbone — UNCONDITIONAL.**

    The session-key derivation backbone of an FO-transform KEM (ML-KEM `Decaps` /
    `Encaps`, FIPS 203): the shared secret is hashed and a key schedule is
    squeezed from a Keccak sponge, `n` permutation applications of
    `keccak_f steps` on the 1600-bit hash/sponge state.  Its entire
    `pipeNT (.TBytes 200)` pipeline decodes to the composite of its per-block
    specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-iteration
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by `pipeNT_realizes`.

    Honest scope: this grounds the **SHA-3 hash/sponge backbone** of the KEM key
    schedule (the FIPS-203 `H` / `J` / `G` / `KDF` calls are all Keccak-permutation
    chains).  It does NOT model the lattice arithmetic of the KEM (NTT, sampling,
    re-encryption check) — those are separate, non-hash kernels with their own
    realizers; only the hash/sponge backbone is grounded here.

    The only residual is the machine-code obligation for the `"keccak_f1600"`
    leaf — the owned-machine-code route, NOT a per-block hypothesis (and NOT a
    KAT). -/
theorem grounded_kem_decaps_backbone_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (kemDecapsLeaves n) oldDest xVal)
      = composeSpecs (kemDecapsSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (kemDecapsLeaves n) (kemDecapsSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §4  The combined KDF/KEM headline — all three backbones grounded

The KDF/KEM portfolio is its three grounded SHA-3 backbones conjoined: the HKDF
Extract→Expand chain, the SHAKE KDF squeeze, and the KEM Decaps/Encaps session-key
backbone.  All three drive the 1600-bit Keccak sponge (carrier `.TBytes 200`), so
the conjunction is over one carrier; each conjunct is unconditional in its
kernels. -/

/-- **THE KDF/KEM HEADLINE — three grounded SHA-3 backbones, ZERO kernel
    hypotheses.**

    The SHA-3 KDF/KEM hash backbones conjoined, each an `n`-block
    `pipeNT (.TBytes 200)` Keccak-permutation pipeline decoding to the composite
    of `n` `keccak_f steps` specs:

    * the SHA-3 HKDF Extract→Expand chain,
    * the SHA-3/SHAKE KDF squeeze, and
    * the KEM Decaps/Encaps session-key backbone,

    each with **ZERO `KernelRealizesT` hypotheses** — every per-step realization
    is the proved concrete realizer `keccak_realizes_concrete` (in turn the
    verified codec round-trip `decodeKbytes_encodeKbytes`).  All three are
    axiom-clean (`{propext, Classical.choice, Quot.sound}`).

    The only residual is the per-kernel machine-code obligation for
    `"keccak_f1600"` (the owned-machine-code route).  Honest scope: the HMAC
    keyed-hash wrapper of the classical HKDF and the lattice arithmetic of the KEM
    are NOT grounded here — only the SHA-3 hash/sponge backbones are. -/
theorem grounded_kdf_kem_portfolio (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (hkdfOldDest hkdfXVal kdfOldDest kdfXVal kemOldDest kemXVal :
      RustVal (.TBytes 200)) :
    -- SHA-3 HKDF Extract→Expand chain: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (sha3HkdfLeaves n) hkdfOldDest hkdfXVal)
      = composeSpecs (sha3HkdfSpecs steps n) (decodeKbytes hkdfXVal)
    ∧
    -- SHA-3/SHAKE KDF squeeze: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (sha3KdfLeaves n) kdfOldDest kdfXVal)
      = composeSpecs (sha3KdfSpecs steps n) (decodeKbytes kdfXVal)
    ∧
    -- KEM Decaps/Encaps session-key backbone: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (kemDecapsLeaves n) kemOldDest kemXVal)
      = composeSpecs (kemDecapsSpecs steps n) (decodeKbytes kemXVal) :=
  ⟨grounded_sha3_hkdf_realizes steps limbStore n hkdfOldDest hkdfXVal,
   grounded_sha3_kdf_squeeze_realizes steps limbStore n kdfOldDest kdfXVal,
   grounded_kem_decaps_backbone_realizes steps limbStore n kemOldDest kemXVal⟩

end CatCrypt.Crypto.SecureCompilation.GroundedKdfKem
