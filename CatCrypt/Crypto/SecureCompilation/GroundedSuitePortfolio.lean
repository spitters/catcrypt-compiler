/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedPortfolio
public import CatCrypt.Crypto.SecureCompilation.GroundedKdfKem
public import CatCrypt.Crypto.SecureCompilation.GroundedKdfHardening
public import CatCrypt.Crypto.SecureCompilation.GroundedSigTransport
public import CatCrypt.Crypto.SecureCompilation.GroundedPqcSignatures
public import CatCrypt.Crypto.SecureCompilation.GroundedHandshake
public import CatCrypt.Crypto.SecureCompilation.GroundedMpcZk
public import CatCrypt.Crypto.SecureCompilation.GroundedSnarkBackbones
public import CatCrypt.Crypto.SecureCompilation.GroundedFheThreshold
public import CatCrypt.Crypto.SecureCompilation.GroundedAdvancedProtocols

/-!
# Grounded suite portfolio — capstone index over the whole grounding effort

This module is the *top-level capstone index* for the protocol-grounding suite.
It aggregates, in one compile-checked place, the per-domain **portfolio**
theorems that the `Grounded*` modules expose, plus the per-protocol headline
entries already collected in `GroundedPortfolio`.

Each entry is a genuine definitional alias (`abbrev name := @Module.thm`), which
forces its source theorem to elaborate and stay in scope.  If any source
portfolio theorem were removed or weakened past its alias, this file would fail
to typecheck — so it is a live, compile-time index of the grounding effort.

## What each grounded portfolio asserts

Every entry grounds the **computational backbone** of a protocol family: the
emitted whole-kernel pipeline *computes its arithmetic / hash specification*
(field add/mul, Horner / polynomial folds, Keccak / SHA sponges, NTT-domain
pointwise multiply, Poseidon2 transcript), discharged with **ZERO assumed
per-kernel realization hypotheses** (`KernelRealizes` / `KernelRealizes2` /
`KernelRealizesT`).  Each per-step realization is a *theorem* — a proved
concrete realizer (`keccak_realizes_concrete`, `fieldAdd_realizes_concrete`,
`fieldMul_realizes_concrete`, `nttMul`-at-the-primitive-root, …) composed with a
verified codec round-trip — not a hypothesised leaf-bytes KAT.  The only side
conditions are codec-fit / range obligations (`width` bounds, accumulator range).

## Domain portfolios indexed here

* **KDF / KEM** — `grounded_kdf_kem_portfolio` (HKDF-Extract/Expand + KEM
  Decaps/Encaps session-key backbone over the Keccak sponge).
* **KDF hardening** — `grounded_kdf_hardening_portfolio`.
* **Signature transport** — `grounded_sig_transport_portfolio`.
* **PQC signatures** — `grounded_pqc_signature_portfolio` (VOLE / Fiat-Shamir
  fold backbone).
* **Handshake / transport** — `grounded_handshake_portfolio`.
* **MPC / ZK** — `grounded_mpc_zk_portfolio`.
* **SNARK backbones** — `grounded_snark_portfolio` (Horner / fold transcript
  cores).
* **FHE / threshold** — `grounded_fhe_threshold_portfolio` (the strict
  NTT-domain pointwise-multiply portfolio).
* **Advanced protocols** — `grounded_advanced_protocol_portfolio`.

Plus the per-protocol headline entries of `GroundedPortfolio` (AEAD modes,
field-arithmetic KDF pipelines, hash sponges, ML-KEM NTT, Poseidon2 transcript,
Schnorr / EdDSA scalar core).

## Honest scope and residual

Each grounded portfolio grounds the **computational backbone only** — *not*
protocol-level security, soundness, or unforgeability (privacy, robustness,
EUF-CMA, KEM IND-CCA, distributed-KeyGen simulatability are separate
cryptographic results and are NOT claimed here).

The shared residual is the **owned machine-code obligation**: for each distinct
emitted kernel, the jasmin-emitted machine bytes must equal the realizer's
`LeafSpec`.  This is one global obligation per kernel, discharged by the owned
route — not a per-protocol or per-kernel hypothesis, and not a KAT.

Two further honest caveats, neither a kernel hypothesis:

* The **EC group operations** of Schnorr / EdDSA (`s·G`, `c·P`, `R + c·P`) have
  no concrete field realizer and remain explicitly *un-grounded* — only the
  scalar-field response equation is grounded.
* The lattice NTT variants that are isolated behind `native_decide` (the two
  ML-KEM-root caveats) are kept OUT of the *strict* per-domain portfolios (e.g.
  the FHE / threshold strict portfolio conjoins only the strictly clean fold and
  pointwise-multiply backbones).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedSuitePortfolio

/-! ## §1  KDF / KEM and KDF hardening -/

/-- KDF / KEM grounded portfolio (HKDF + KEM session-key backbone) — alias of
    the source theorem. -/
abbrev kdf_kem_suite_grounded :=
  @GroundedKdfKem.grounded_kdf_kem_portfolio

/-- KDF hardening grounded portfolio — alias of the source theorem. -/
abbrev kdf_hardening_suite_grounded :=
  @GroundedKdfHardening.grounded_kdf_hardening_portfolio

/-! ## §2  Signatures and PQC signatures -/

/-- Signature transport grounded portfolio — alias of the source theorem. -/
abbrev sig_transport_suite_grounded :=
  @GroundedSigTransport.grounded_sig_transport_portfolio

/-- PQC signature grounded portfolio (VOLE / Fiat-Shamir fold) — alias of the
    source theorem. -/
abbrev pqc_signature_suite_grounded :=
  @GroundedPqcSignatures.grounded_pqc_signature_portfolio

/-! ## §3  Transport / handshake -/

/-- Handshake / transport grounded portfolio — alias of the source theorem. -/
abbrev handshake_suite_grounded :=
  @GroundedHandshake.grounded_handshake_portfolio

/-! ## §4  MPC / ZK / SNARK -/

/-- MPC / ZK grounded portfolio — alias of the source theorem. -/
abbrev mpc_zk_suite_grounded :=
  @GroundedMpcZk.grounded_mpc_zk_portfolio

/-- SNARK backbone grounded portfolio (Horner / fold transcript cores) — alias
    of the source theorem. -/
abbrev snark_suite_grounded :=
  @GroundedSnarkBackbones.grounded_snark_portfolio

/-! ## §5  FHE / threshold (strict NTT-domain portfolio) -/

/-- FHE / threshold strict grounded portfolio (NTT-domain pointwise multiply) —
    alias of the source theorem. -/
abbrev fhe_threshold_suite_grounded :=
  @GroundedFheThreshold.grounded_fhe_threshold_portfolio

/-! ## §6  Advanced protocols -/

/-- Advanced-protocol grounded portfolio — alias of the source theorem. -/
abbrev advanced_protocol_suite_grounded :=
  @GroundedAdvancedProtocols.grounded_advanced_protocol_portfolio

/-! ## §7  Per-protocol headline rollup (re-export of `GroundedPortfolio`)

These re-export the AEAD / field-arithmetic / hash-sponge / lattice / ZK /
signature headline entries already collected in `GroundedPortfolio`, so this
single module is a checkable index of the whole grounding effort. -/

/-- ChaCha20-Poly1305 AEAD grounded — re-export of `GroundedPortfolio`. -/
abbrev chachapoly_grounded :=
  @GroundedPortfolio.chachapoly_is_grounded

/-- AES-GCM grounded — re-export of `GroundedPortfolio`. -/
abbrev aesgcm_grounded :=
  @GroundedPortfolio.aesgcm_is_grounded

/-- Keccak-f[1600] sponge grounded — re-export of `GroundedPortfolio`. -/
abbrev keccak_sponge_grounded :=
  @GroundedPortfolio.keccak_sponge_is_grounded

/-- SHA-256 Merkle–Damgård chain grounded — re-export of `GroundedPortfolio`. -/
abbrev sha256_chain_grounded :=
  @GroundedPortfolio.sha256_chain_is_grounded

/-- ML-KEM NTT-multiply grounded — re-export of `GroundedPortfolio`. -/
abbrev mlkem_ntt_grounded :=
  @GroundedPortfolio.mlkem_ntt_is_grounded

/-- Poseidon2 Fiat-Shamir transcript grounded — re-export of `GroundedPortfolio`. -/
abbrev poseidon_transcript_grounded :=
  @GroundedPortfolio.poseidon_transcript_is_grounded

/-- Schnorr / EdDSA scalar response grounded — re-export of `GroundedPortfolio`. -/
abbrev schnorr_response_grounded :=
  @GroundedPortfolio.schnorr_response_is_grounded

end CatCrypt.Crypto.SecureCompilation.GroundedSuitePortfolio
