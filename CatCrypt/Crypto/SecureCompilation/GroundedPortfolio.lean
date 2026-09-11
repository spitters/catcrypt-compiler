/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol
public import CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol
public import CatCrypt.Crypto.SecureCompilation.GroundedAesFieldProtocols
public import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
public import CatCrypt.Crypto.SecureCompilation.GroundedRealProtocol
public import CatCrypt.Crypto.SecureCompilation.GroundedChaChaPoly
public import CatCrypt.Crypto.SecureCompilation.GroundedAesGcm
public import CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt
public import CatCrypt.Crypto.SecureCompilation.GroundedZkProtocol
public import CatCrypt.Crypto.SecureCompilation.GroundedSignatureCore

/-!
# Grounded portfolio — a single checkable index of the zero-assumed-kernel-hypothesis
  protocol realizations

This module is a *capstone index*.  It collects, in one place, every
whole-pipeline emit-realization that the `Grounded*` modules discharge with
**zero assumed per-kernel hypotheses** — each protocol's per-kernel realization
is a *theorem* (a proved concrete realizer composed with a verified codec
round-trip), not a hypothesised leaf-bytes KAT.

The entries below are definitional aliases (`abbrev … := @Module.name`).
Each forces its source theorem to elaborate and be in scope, so this file is a
compile-time check that *all* the grounded results hold: if any source theorem
were removed or its statement weakened past the alias, this file would fail to
typecheck.  No entry is a vacuous `True` stub.

## The grounded portfolio (by category)

Each row is a whole-pipeline (or whole-kernel) emit-realization grounded with
ZERO `KernelRealizes` / `KernelRealizes2` / `KernelRealizesT` hypotheses; the
per-kernel realizations are theorems from the proved concrete realizers plus the
verified codec round-trips.

* **AEAD / symmetric modes**
  * ChaCha20-Poly1305 (RFC 8439): keystream phase + MAC phase + combined
    (`chachapoly_keystream_grounded`, `chachapoly_mac_grounded`,
    `chachapoly_grounded`).
  * AES-GCM (SP 800-38D): AES-CTR keystream + GHASH `GF(2^128)` fold + combined
    (`grounded_aesgcm_ctr_realizes`, `grounded_aesgcm_ghash_realizes`,
    `grounded_aesgcm`).
  * AES-ECB chain, AES-OFB keystream (FIPS 197 / SP 800-38A)
    (`grounded_aes_ecb_realizes`, `grounded_aes_ofb_keystream_realizes`).

* **KDF / field-arithmetic pipelines**
  * Accumulate-by-constant chain, single Horner step, multi-step Horner /
    polynomial evaluation, field multiply-accumulate / inner-product step
    (`grounded_accumulate_realizes`, `grounded_horner_realizes`,
    `grounded_poly_eval_realizes`, `grounded_inner_product_step_realizes`).
  * Mixed-kernel pipeline through one combined-dispatch leafSpec
    (`grounded_multikernel_realizes`) and the named Horner polynomial evaluation
    over distinct mul/add kernels (`grounded_horner_eval_realizes`).

* **Hash sponges / compression chains**
  * Keccak-f[1600] sponge (FIPS 202) and SHA-256 Merkle–Damgård chain (FIPS 180-4)
    (`grounded_keccak_sponge_realizes`, `grounded_sha256_chain_realizes`).

* **Lattice (ML-KEM)**
  * ML-KEM NTT-multiply (FIPS 203) and the `k`-step matrix–vector pointwise
    core (`mlkem_ntt_grounded`, `grounded_mlkem_matvec_realizes`).

* **Zero-knowledge (Fiat-Shamir transcript)**
  * Poseidon2 Baby-Bear Fiat-Shamir transcript chain for STARK / Plonky3 / FRI
    verifiers (`grounded_poseidon_transcript_realizes`).

* **Signatures (scalar-arithmetic core)**
  * Schnorr / EdDSA scalar response combine `x ↦ c·x + r` and its batch /
    multi-scalar form (`grounded_schnorr_response_realizes`,
    `grounded_schnorr_batch_realizes`).

## The shared residual — stated precisely

These are **composition-layer** results: each grounds a whole pipeline on
*proved concrete realizers*.  The grounding eliminates the per-kernel
realization hypotheses; what remains is a single, shared residual:

* **Owned machine-code obligation.**  For each distinct kernel, the
  jasmin-emitted machine bytes must equal the realizer's `LeafSpec` (emitted
  assembly ≡ realizer `leafSpec`).  This is **one global obligation per kernel**,
  discharged by the owned route — *not* a per-protocol or per-kernel hypothesis,
  and *not* a KAT.  The NTT route discharges it structurally
  (`X86Backend/LoopRealization.lean`; the owned realization is free of
  `jasminc_preserves_ct` under `#print axioms`).

Two protocols carry one further caveat, neither a kernel hypothesis:

* **Poly1305 (ChaCha20-Poly1305 MAC phase)** additionally carries a codec-fit /
  *range* side-condition on the accumulator (`hrange`, `width ≥ 17` covers every
  reachable accumulator `< 2^130 - 5`) — analogous to the field protocols'
  `width ≤ 48` codec-fit, not a kernel realization.
* **Schnorr / EdDSA** grounds only the *scalar-field* response equation.  The
  **EC point operations** (`s·G`, `c·P`, `R + c·P`) are group operations with no
  concrete field realizer and are explicitly *un-realized* — the residual
  of that grounding.

## Scope, restated

This index does not claim end-to-end machine-checked security for whole
protocols.  It claims exactly: the *composition layer* of each listed pipeline is
grounded on proved concrete realizers, with no assumed per-kernel realization;
the only shared remaining obligation is the owned machine-code equality, plus the
two noted caveats (Poly1305 range, Schnorr EC point ops un-realized).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedPortfolio

/-! ## §1  AEAD / symmetric modes

ChaCha20-Poly1305, AES-GCM, and the AES block-mode chains. Each per-kernel
realization is a proved concrete realizer (`chacha_realizes_concrete`,
`poly1305_realizes_concrete`, `aes_realizes_concrete`, `gf128_realizes_concrete`)
composed with a verified codec round-trip — no assumed kernel hypothesis. -/

/-- ChaCha20 keystream phase (RFC 8439) grounded — alias of the source theorem. -/
abbrev chachapoly_keystream_is_grounded :=
  @GroundedChaChaPoly.chachapoly_keystream_grounded

/-- Poly1305 MAC phase (RFC 8439) grounded — alias of the source theorem. -/
abbrev chachapoly_mac_is_grounded :=
  @GroundedChaChaPoly.chachapoly_mac_grounded

/-- ChaCha20-Poly1305 AEAD (both phases) grounded — alias of the source theorem. -/
abbrev chachapoly_is_grounded :=
  @GroundedChaChaPoly.chachapoly_grounded

/-- AES-GCM CTR keystream (SP 800-38D) grounded — alias of the source theorem. -/
abbrev aesgcm_ctr_is_grounded :=
  @GroundedAesGcm.grounded_aesgcm_ctr_realizes

/-- AES-GCM GHASH `GF(2^128)` fold grounded — alias of the source theorem. -/
abbrev aesgcm_ghash_is_grounded :=
  @GroundedAesGcm.grounded_aesgcm_ghash_realizes

/-- AES-GCM (both phases) grounded — alias of the source theorem. -/
abbrev aesgcm_is_grounded :=
  @GroundedAesGcm.grounded_aesgcm

/-- AES-ECB chain (FIPS 197) grounded — alias of the source theorem. -/
abbrev aes_ecb_is_grounded :=
  @GroundedAesFieldProtocols.grounded_aes_ecb_realizes

/-- AES-OFB keystream (SP 800-38A) grounded — alias of the source theorem. -/
abbrev aes_ofb_keystream_is_grounded :=
  @GroundedRealProtocol.grounded_aes_ofb_keystream_realizes

/-! ## §2  KDF / field-arithmetic pipelines

Accumulate-by-constant, Horner / polynomial evaluation, inner-product
multiply-accumulate, and the mixed-kernel pipeline through one combined-dispatch
leafSpec. Each per-kernel realization is the proved `fieldAdd_realizes_concrete`
/ `fieldMul_realizes_concrete` plus the `decodeF_encodeF` codec round-trip. -/

/-- Accumulate-by-constant field chain grounded — alias of the source theorem. -/
abbrev accumulate_is_grounded :=
  @GroundedFieldProtocol.grounded_accumulate_realizes

/-- Single Horner step `x ↦ x*v + c` grounded — alias of the source theorem. -/
abbrev horner_step_is_grounded :=
  @GroundedFieldProtocol.grounded_horner_realizes

/-- Multi-step Horner / polynomial evaluation grounded — alias of the source theorem. -/
abbrev poly_eval_is_grounded :=
  @GroundedAesFieldProtocols.grounded_poly_eval_realizes

/-- Field multiply-accumulate / inner-product step grounded — alias of the source theorem. -/
abbrev inner_product_step_is_grounded :=
  @GroundedAesFieldProtocols.grounded_inner_product_step_realizes

/-- Mixed-kernel pipeline (one combined-dispatch leafSpec, two distinct kernels)
    grounded — alias of the source theorem. -/
abbrev multikernel_is_grounded :=
  @GroundedMultiKernelProtocol.grounded_multikernel_realizes

/-- Named Horner polynomial evaluation over distinct mul/add kernels grounded —
    alias of the source theorem. -/
abbrev horner_eval_is_grounded :=
  @GroundedRealProtocol.grounded_horner_eval_realizes

/-! ## §3  Hash sponges / compression chains

Keccak-f[1600] sponge (FIPS 202) and the SHA-256 Merkle–Damgård chain
(FIPS 180-4), over carrier-generalized composition (`pipeNT_realizes`). Each
per-iteration realization is the proved `keccak_realizes_concrete` /
`sha256_realizes_concrete` plus the verified codec round-trip. -/

/-- Keccak-f[1600] sponge (FIPS 202) grounded — alias of the source theorem. -/
abbrev keccak_sponge_is_grounded :=
  @GroundedHashProtocol.grounded_keccak_sponge_realizes

/-- SHA-256 Merkle–Damgård chain (FIPS 180-4) grounded — alias of the source theorem. -/
abbrev sha256_chain_is_grounded :=
  @GroundedHashProtocol.grounded_sha256_chain_realizes

/-! ## §4  Lattice (ML-KEM)

The ML-KEM NTT-multiply (FIPS 203) — already unconditional (the codec round-trip
`decodeP_encodeP` plus `nttMul_eq_cyclicConv'` at the proven primitive root) —
and the `k`-step matrix–vector pointwise core built from it. -/

/-- ML-KEM NTT-multiply (FIPS 203) grounded — alias of the source theorem. -/
abbrev mlkem_ntt_is_grounded :=
  @GroundedMlkemNtt.mlkem_ntt_grounded

/-- ML-KEM matrix–vector pointwise-multiply core grounded — alias of the
    source theorem. -/
abbrev mlkem_matvec_is_grounded :=
  @GroundedMlkemNtt.grounded_mlkem_matvec_realizes

/-! ## §5  Zero-knowledge (Fiat-Shamir transcript)

The Poseidon2 Baby-Bear Fiat-Shamir transcript chain (STARK / Plonky3 / FRI
verifiers), each per-round realization the proved
`poseidon2_perm_realizes_concrete` plus the verified codec round-trip. -/

/-- Poseidon2 Baby-Bear Fiat-Shamir transcript grounded — alias of the source theorem. -/
abbrev poseidon_transcript_is_grounded :=
  @GroundedZkProtocol.grounded_poseidon_transcript_realizes

/-! ## §6  Signatures (scalar-arithmetic core)

The Schnorr / EdDSA scalar response combine `x ↦ c·x + r` and its batch /
multi-scalar form, dispatched through one combined leafSpec whose two arms are
the proved `combined_realizes_mul` / `combined_realizes_add`. The EC point
operations are the un-realized residual (see module docstring). -/

/-- Schnorr / EdDSA scalar response combine grounded — alias of the source theorem. -/
abbrev schnorr_response_is_grounded :=
  @GroundedSignatureCore.grounded_schnorr_response_realizes

/-- Schnorr / EdDSA batch / multi-scalar response grounded — alias of the source theorem. -/
abbrev schnorr_batch_is_grounded :=
  @GroundedSignatureCore.grounded_schnorr_batch_realizes

end CatCrypt.Crypto.SecureCompilation.GroundedPortfolio
