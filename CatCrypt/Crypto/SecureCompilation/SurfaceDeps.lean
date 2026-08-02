/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Resolved
import CatCrypt.Hax.CType

/-!
# Hax Extraction Bridge

Connects Hax-extracted SPComp code to the ITreeN secure compilation framework
via `embedSPComp`. Models the SPQR-style pipeline:

```
hax_extracted (SPComp) --[embedSPComp]--> ITreeN --[CompilerCorrectResolved]--> UC security
```

## Key insight

`embedSPComp` lifts SPComp computations to ITreeN without adding events.
Since `flattenAll_embedSPComp` shows `flattenAll handler n (embedSPComp n c) = c`,
the handler is irrelevant for embedded computations. This means:

1. **Exact correctness**: If `hax_impl = spec`, then `haxLift` of both are resolved-correct.
2. **Approximate correctness**: If `sdist hax_impl spec ≤ ε`, the ITreeN lifting preserves ε.
3. **UC transfer**: Compose with spec-level UC proofs for full pipeline security.

## Main theorems

* `haxLift_exact_resolved` -- exact Hax code gives CompilerCorrectResolved
* `haxLift_approx_sdist` -- approximate Hax code preserves sdist bound
* `haxLift_uc_transfer` -- full UC transfer from spec through Hax extraction
* `HaxProtocol.uc_secure` -- SPQR-style full pipeline theorem

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation.SurfaceDeps

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open scoped ENNReal

/-! ## Hax Lifting -/

/-- Lift an SPComp function to ITreeN via embedSPComp.
    This is the "Hax compiler": extracted Rust code (modeled as SPComp)
    is lifted to the ITreeN world for UC composition. -/
noncomputable def haxLift {hon β : Type} (n : Nat) (E : EventSig) (f : hon -> SPComp β) :
    hon -> ITreeN n E β :=
  fun x => embedSPComp n (f x)

/-! ## Exact Correctness -/

/-- If `hax_impl` and `spec` agree pointwise, their liftings are resolved-correct. -/
theorem haxLift_exact_resolved {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {hax_impl spec : hon -> SPComp β}
    (h : forall x, hax_impl x = spec x) :
    CompilerCorrectResolved handler
      (haxLift n E hax_impl)
      (haxLift n E spec) := by
  intro x
  simp only [haxLift, flattenAll_embedSPComp, h]

/-- Exact haxLift gives sdist = 0. -/
theorem haxLift_exact_sdist_zero {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {hax_impl spec : hon -> SPComp β}
    (h : forall x, hax_impl x = spec x) :
    sdistITreeN n E handler (haxLift n E hax_impl) (haxLift n E spec) = 0 :=
  resolved_sdist_zero handler (haxLift_exact_resolved handler h)

/-! ## Approximate Correctness -/

/-- If `sdist hax_impl spec ≤ ε` at the SPComp level, the ITreeN lifting
    preserves the bound. The handler is irrelevant because `flattenAll_embedSPComp`
    strips it away. -/
theorem haxLift_approx_sdist {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {hax_impl spec : hon -> SPComp β}
    {ε : ℝ≥0∞}
    (h : sdist hax_impl spec ≤ ε) :
    sdistITreeN n E handler (haxLift n E hax_impl) (haxLift n E spec) ≤ ε := by
  unfold sdistITreeN haxLift
  simp only [flattenAll_embedSPComp]
  exact h

/-! ## UC Security Transfer -/

/-- Full UC transfer: if the spec UC-emulates ideal at ε₁, and the Hax extraction
    is ε₂-close to the spec, then the Hax code UC-emulates ideal at ε₁ + ε₂.

    This is the SPQR-style pipeline theorem. -/
theorem haxLift_uc_transfer {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {hax_impl spec : hon -> SPComp β}
    {ideal : hon -> ITreeN n E β}
    {ε₁ ε₂ : ℝ≥0∞}
    (h_approx : sdist hax_impl spec ≤ ε₂)
    (h_sec : sdistITreeN n E handler (haxLift n E spec) ideal ≤ ε₁) :
    sdistITreeN n E handler (haxLift n E hax_impl) ideal ≤ ε₁ + ε₂ := by
  calc sdistITreeN n E handler (haxLift n E hax_impl) ideal
      ≤ sdistITreeN n E handler (haxLift n E hax_impl) (haxLift n E spec)
        + sdistITreeN n E handler (haxLift n E spec) ideal := sdistITreeN_triangle ..
    _ ≤ ε₂ + ε₁ := add_le_add (haxLift_approx_sdist handler h_approx) h_sec
    _ = ε₁ + ε₂ := add_comm _ _

/-! ## SPQR-Style Protocol Bundle -/

/-- A Hax-extracted protocol with its spec and security proof.
    Models the SPQR pipeline: extracted code + crypto dependencies + bridge proof. -/
structure HaxProtocol (hon β : Type) (E : EventSig) (n : Nat) where
  /-- Hax-extracted implementation (SPComp level). -/
  hax_impl : hon -> SPComp β
  /-- Specification (SPComp level). -/
  spec : hon -> SPComp β
  /-- Ideal functionality (ITreeN level). -/
  ideal : hon -> ITreeN n E β
  /-- Extraction approximation bound. -/
  ε_extract : ℝ≥0∞
  /-- Spec-to-ideal security bound. -/
  ε_spec : ℝ≥0∞
  /-- Proof that extraction is ε_extract-close to spec. -/
  h_extract : sdist hax_impl spec ≤ ε_extract
  /-- Proof that spec is ε_spec-close to ideal (at ITreeN level). -/
  h_spec : forall handler : (forall e : E.Event, SPComp (E.Resp e)),
    sdistITreeN n E handler (haxLift n E spec) ideal ≤ ε_spec

/-- The Hax-extracted code is `(ε_spec + ε_extract)`-close to the ideal
    functionality *(composition plumbing)*.

    A triangle inequality over the two distances the structure already carries,
    composed by `haxLift_uc_transfer`. The conclusion is a bound on
    `sdistITreeN`, not a `UCEmulates` with a simulator. -/
theorem HaxProtocol.uc_secure {hon β : Type} {E : EventSig} {n : Nat}
    (P : HaxProtocol hon β E n)
    (handler : forall e : E.Event, SPComp (E.Resp e)) :
    sdistITreeN n E handler (haxLift n E P.hax_impl) P.ideal ≤
    P.ε_spec + P.ε_extract :=
  haxLift_uc_transfer handler P.h_extract (P.h_spec handler)

/-- When extraction is exact (ε_extract = 0), the bound simplifies. -/
theorem HaxProtocol.uc_secure_exact {hon β : Type} {E : EventSig} {n : Nat}
    (P : HaxProtocol hon β E n)
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (h_exact : P.ε_extract = 0) :
    sdistITreeN n E handler (haxLift n E P.hax_impl) P.ideal ≤ P.ε_spec := by
  have := P.uc_secure handler
  rw [h_exact, add_zero] at this
  exact this

/-! ## Connecting to CompilerCorrectResolved -/

/-- haxLift of the spec, followed by any resolved-correct ITreeN compilation,
    gives a full pipeline from Hax extraction to compiled UC security. -/
theorem haxLift_compiled_uc_transfer {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {hax_impl spec : hon -> SPComp β}
    {compiled ideal : hon -> ITreeN n E β}
    {ε₁ ε₂ : ℝ≥0∞}
    (h_approx : sdist hax_impl spec ≤ ε₂)
    (h_compile : CompilerCorrectResolved handler (haxLift n E spec) compiled)
    (h_sec : sdistITreeN n E handler compiled ideal ≤ ε₁) :
    sdistITreeN n E handler (haxLift n E hax_impl) ideal ≤ ε₁ + ε₂ := by
  have h_spec : sdistITreeN n E handler (haxLift n E spec) ideal ≤ ε₁ := by
    calc sdistITreeN n E handler (haxLift n E spec) ideal
        ≤ sdistITreeN n E handler (haxLift n E spec) compiled
          + sdistITreeN n E handler compiled ideal := sdistITreeN_triangle ..
      _ = 0 + sdistITreeN n E handler compiled ideal := by
          rw [resolved_sdist_zero handler h_compile]
      _ = sdistITreeN n E handler compiled ideal := zero_add _
      _ ≤ ε₁ := h_sec
  exact haxLift_uc_transfer handler h_approx h_spec

end CatCrypt.Crypto.SecureCompilation.SurfaceDeps
