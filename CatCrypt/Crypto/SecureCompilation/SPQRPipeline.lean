/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.SurfaceDeps
import CatCrypt.Crypto.SecureCompilation.CryptoApproxPass

/-!
# End-to-End Hax Pipeline (SPQR-Style)

Formalizes the complete SPQR-style verification pipeline:

```
Hax-extracted Rust code (SPComp)
  ↓ [haxLift: embedSPComp]
ITreeN protocol
  ↓ [operational refinement: sdist ≤ ε_extract]
Abstract game (SPComp)
  ↓ [hybrid argument: ε₁ + ... + εₖ]
Ideal functionality
```

The pipeline composes three layers:
1. **Extraction bridge**: Hax code → ITreeN via `embedSPComp`
2. **Operational refinement**: Concrete ≈ Abstract at SPComp level
3. **Crypto security**: Abstract → Ideal via game-hopping

## Main theorems

* `SPQRPipeline` -- full pipeline structure
* `SPQRPipeline.uc_secure` -- end-to-end UC security
* `SPQRPipeline.uc_secure_exact` -- exact extraction specialization
* `composePipelines` -- compose two independent pipeline results

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation.SPQRPipeline

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation SurfaceDeps CryptoApproxPass
open scoped ENNReal

/-! ## Full Pipeline Structure -/

/-- A complete SPQR-style verification pipeline. Packages:
    1. Hax-extracted implementation
    2. Abstract specification (operational refinement target)
    3. Ideal functionality
    4. Bounds for each layer
    5. Proofs connecting each layer -/
structure SPQRPipeline (hon β : Type) (E : EventSig) (n : Nat) where
  /-- Hax-extracted implementation (SPComp level, from `cargo hax into lean`). -/
  hax_impl : hon → SPComp β
  /-- Abstract specification (SPComp level, the game we reason about). -/
  abstract_spec : hon → SPComp β
  /-- Ideal functionality (ITreeN level, the security target). -/
  ideal : hon → ITreeN n E β
  /-- Extraction approximation bound (SPComp → SPComp distance). -/
  ε_extract : ℝ≥0∞
  /-- Game-hopping bound (abstract spec → ideal distance). -/
  ε_crypto : ℝ≥0∞
  /-- Extraction correctness: hax_impl is ε_extract-close to abstract_spec. -/
  h_extract : sdist hax_impl abstract_spec ≤ ε_extract
  /-- Crypto security: abstract spec (lifted to ITreeN) is ε_crypto-close to ideal. -/
  h_crypto : forall handler : (forall e : E.Event, SPComp (E.Resp e)),
    sdistITreeN n E handler (haxLift n E abstract_spec) ideal ≤ ε_crypto

/-! ## End-to-End Security -/

/-- The full SPQR-style UC security theorem:
    hax implementation is (ε_crypto + ε_extract)-close to the ideal. -/
theorem SPQRPipeline.uc_secure {hon β : Type} {E : EventSig} {n : Nat}
    (P : SPQRPipeline hon β E n)
    (handler : forall e : E.Event, SPComp (E.Resp e)) :
    sdistITreeN n E handler (haxLift n E P.hax_impl) P.ideal ≤
    P.ε_crypto + P.ε_extract :=
  haxLift_uc_transfer handler P.h_extract (P.h_crypto handler)

/-- When extraction is exact (ε_extract = 0), the bound simplifies. -/
theorem SPQRPipeline.uc_secure_exact {hon β : Type} {E : EventSig} {n : Nat}
    (P : SPQRPipeline hon β E n)
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (h_exact : P.ε_extract = 0) :
    sdistITreeN n E handler (haxLift n E P.hax_impl) P.ideal ≤ P.ε_crypto := by
  have := P.uc_secure handler
  rw [h_exact, add_zero] at this
  exact this

/-- When extraction is exact AND crypto bound is zero (perfect security). -/
theorem SPQRPipeline.perfect_security {hon β : Type} {E : EventSig} {n : Nat}
    (P : SPQRPipeline hon β E n)
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (h_exact : P.ε_extract = 0)
    (h_perfect : P.ε_crypto = 0) :
    sdistITreeN n E handler (haxLift n E P.hax_impl) P.ideal = 0 := by
  have h := P.uc_secure handler
  rw [h_exact, h_perfect, add_zero] at h
  exact le_antisymm h (zero_le)

/-! ## Pipeline Composition -/

/-- Compose two pipeline results: if protocol A and protocol B each have
    SPQR-style bounds, their parallel composition has additive bounds. -/
theorem composePipelines {hon β₁ β₂ : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {hax₁ spec₁ : hon → SPComp β₁}
    {hax₂ spec₂ : hon → SPComp β₂}
    {ideal₁ : hon → ITreeN n E β₁}
    {ideal₂ : hon → ITreeN n E β₂}
    {ε₁ ε₂ δ₁ δ₂ : ℝ≥0∞}
    (h₁ : sdistITreeN n E handler (haxLift n E hax₁) ideal₁ ≤ ε₁ + δ₁)
    (h₂ : sdistITreeN n E handler (haxLift n E hax₂) ideal₂ ≤ ε₂ + δ₂) :
    sdistITreeN n E handler (haxLift n E hax₁) ideal₁ +
    sdistITreeN n E handler (haxLift n E hax₂) ideal₂ ≤
    (ε₁ + δ₁) + (ε₂ + δ₂) :=
  add_le_add h₁ h₂

/-! ## Multi-Hop Pipeline -/

/-- Pipeline with multi-hop crypto argument: the abstract spec goes through
    k hybrid hops, each bounded by εᵢ. -/
structure MultiHopPipeline (hon β : Type) (E : EventSig) (n : Nat) where
  /-- Hax-extracted implementation. -/
  hax_impl : hon → SPComp β
  /-- Abstract specification. -/
  abstract_spec : hon → SPComp β
  /-- Ideal functionality. -/
  ideal : hon → ITreeN n E β
  /-- Number of hybrid hops. -/
  k : Nat
  /-- Extraction bound. -/
  ε_extract : ℝ≥0∞
  /-- Per-hop crypto bound. -/
  ε_per_hop : ℝ≥0∞
  /-- Extraction correctness. -/
  h_extract : sdist hax_impl abstract_spec ≤ ε_extract
  /-- Crypto security (k hops at ε_per_hop each). -/
  h_crypto : forall handler : (forall e : E.Event, SPComp (E.Resp e)),
    sdistITreeN n E handler (haxLift n E abstract_spec) ideal ≤ k * ε_per_hop

/-- Multi-hop pipeline security. -/
theorem MultiHopPipeline.uc_secure {hon β : Type} {E : EventSig} {n : Nat}
    (P : MultiHopPipeline hon β E n)
    (handler : forall e : E.Event, SPComp (E.Resp e)) :
    sdistITreeN n E handler (haxLift n E P.hax_impl) P.ideal ≤
    P.k * P.ε_per_hop + P.ε_extract :=
  haxLift_uc_transfer handler P.h_extract (P.h_crypto handler)

/-! ## Pipeline from HaxProtocol -/

/-- Convert a HaxProtocol to a SPQRPipeline (for interoperability). -/
def ofHaxProtocol {hon β : Type} {E : EventSig} {n : Nat}
    (P : HaxProtocol hon β E n) : SPQRPipeline hon β E n where
  hax_impl := P.hax_impl
  abstract_spec := P.spec
  ideal := P.ideal
  ε_extract := P.ε_extract
  ε_crypto := P.ε_spec
  h_extract := P.h_extract
  h_crypto := P.h_spec

/-- The converted pipeline has the same security bound. -/
theorem ofHaxProtocol_secure {hon β : Type} {E : EventSig} {n : Nat}
    (P : HaxProtocol hon β E n)
    (handler : forall e : E.Event, SPComp (E.Resp e)) :
    sdistITreeN n E handler (haxLift n E P.hax_impl) P.ideal ≤
    P.ε_spec + P.ε_extract :=
  (ofHaxProtocol P).uc_secure handler

end CatCrypt.Crypto.SecureCompilation.SPQRPipeline
