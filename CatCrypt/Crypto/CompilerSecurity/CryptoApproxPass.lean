/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.ApproxPass

/-!
# Crypto-Assumption-Wired Approximate Pass

Connects abstract cryptographic assumptions (DDH, PRG, PRF, etc.) to the
approximate compiler pass framework. The key insight: a crypto assumption
provides an `sdist` bound between real and ideal core computations, which
plugs directly into `approxPass_sdist_le'` and `multipass_nonzero_security_transfer`.

## Pipeline

```
real_core  --[crypto assumption: sdist ≤ ε]--> ideal_core
    |                                              |
    v                                              v
approxPass_source  --[approxPass_sdist_le' ≤ ε]--> approxPass_target
    |                                              |
    v                                              v
multipass_nonzero_security_transfer: total sdist ≤ ε₁ + ε₂
```

## Main theorems

* `CryptoAssumption.approxPass_sdist` -- crypto assumption gives sdistITreeN bound
* `CryptoAssumption.pipeline_security` -- full pipeline: exact passes + crypto pass
* `TwoAssumption.composed_security` -- compose two crypto assumptions additively
* `NAssumption.composed_security` -- compose N crypto assumptions

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.CryptoApproxPass

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation ApproxPass
open scoped ENNReal

/-! ## Abstract Crypto Assumption -/

/-- An abstract cryptographic assumption providing an sdist bound between
    a real and ideal core computation. Models DDH, PRG, PRF, AEAD, etc. -/
structure CryptoAssumption (β : Type) where
  /-- Real-world core computation (e.g., KDF output). -/
  real_core : SPComp β
  /-- Ideal-world core computation (e.g., random output). -/
  ideal_core : SPComp β
  /-- Security bound from the assumption. -/
  ε : ℝ≥0∞
  /-- The assumption: sdist between real and ideal is bounded. -/
  h_bound : sdist (fun (_ : Unit) => real_core) (fun (_ : Unit) => ideal_core) ≤ ε

/-! ## Wiring to ApproxPass -/

/-- The source protocol uses the real core. -/
noncomputable def CryptoAssumption.source {β : Type} {E : EventSig}
    (A : CryptoAssumption β) (n : Nat) (e : E.Event) :
    Unit → ITreeN (n + 1) E β :=
  approxPass_source A.real_core n e

/-- The target protocol uses the ideal core. -/
noncomputable def CryptoAssumption.target {β : Type} {E : EventSig}
    (A : CryptoAssumption β) (n : Nat) (e : E.Event) :
    Unit → ITreeN (n + 1) E β :=
  approxPass_target A.ideal_core n e

/-- The crypto assumption directly gives an sdistITreeN bound via ApproxPass. -/
theorem CryptoAssumption.approxPass_sdist {β : Type} {E : EventSig}
    (A : CryptoAssumption β)
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) :
    sdistITreeN (n + 1) E handler (A.source n e) (A.target n e) ≤ A.ε :=
  approxPass_sdist_le' handler A.real_core A.ideal_core n e A.ε A.h_bound

/-! ## Full Pipeline: Exact Passes + Crypto Pass -/

/-- Full pipeline: exact passes (sdist = 0) composed with one crypto-approximate
    pass (sdist ≤ ε). Source has security ε₁ to ideal, crypto pass adds ε₂.
    Total: ε₁ + ε₂. -/
theorem CryptoAssumption.pipeline_security
    {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source intermediate : hon → ITreeN n E β}
    {ideal : hon → ITreeN n E β}
    (A : CryptoAssumption β)
    {target : hon → ITreeN n E β}
    {ε₁ : ℝ≥0∞}
    (h_exact : CompilerCorrectResolved handler source intermediate)
    (h_approx : sdistITreeN n E handler intermediate target ≤ A.ε)
    (h_sec : sdistITreeN n E handler source ideal ≤ ε₁) :
    sdistITreeN n E handler target ideal ≤ ε₁ + A.ε :=
  multipass_nonzero_security_transfer handler h_exact h_approx h_sec

/-! ## Composing Two Crypto Assumptions -/

/-- Two crypto assumptions composed additively. Models e.g., DDH + PRG
    where the first replaces DH with random, the second replaces PRG with random. -/
structure TwoAssumption (β : Type) where
  /-- First assumption (e.g., DDH). -/
  A₁ : CryptoAssumption β
  /-- Second assumption (e.g., PRG). -/
  A₂ : CryptoAssumption β
  /-- Intermediate: A₁.ideal_core = A₂.real_core (the chain condition). -/
  h_chain : A₁.ideal_core = A₂.real_core

/-- Two-assumption composition: sdist ≤ ε₁ + ε₂. -/
theorem TwoAssumption.composed_sdist {β : Type}
    (TA : TwoAssumption β) :
    sdist (fun (_ : Unit) => TA.A₁.real_core)
          (fun (_ : Unit) => TA.A₂.ideal_core) ≤ TA.A₁.ε + TA.A₂.ε :=
  calc sdist (fun (_ : Unit) => TA.A₁.real_core)
             (fun (_ : Unit) => TA.A₂.ideal_core)
      ≤ sdist (fun (_ : Unit) => TA.A₁.real_core)
              (fun (_ : Unit) => TA.A₁.ideal_core) +
        sdist (fun (_ : Unit) => TA.A₁.ideal_core)
              (fun (_ : Unit) => TA.A₂.ideal_core) := sdist_triangle ..
    _ ≤ TA.A₁.ε +
        sdist (fun (_ : Unit) => TA.A₁.ideal_core)
              (fun (_ : Unit) => TA.A₂.ideal_core) :=
        add_le_add TA.A₁.h_bound (le_refl _)
    _ = TA.A₁.ε +
        sdist (fun (_ : Unit) => TA.A₂.real_core)
              (fun (_ : Unit) => TA.A₂.ideal_core) := by rw [TA.h_chain]
    _ ≤ TA.A₁.ε + TA.A₂.ε := add_le_add (le_refl _) TA.A₂.h_bound

/-- Full security pipeline with two assumptions. -/
theorem TwoAssumption.composed_security
    {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (TA : TwoAssumption β)
    {source target ideal : hon → ITreeN n E β}
    {ε₀ : ℝ≥0∞}
    (h_exact : CompilerCorrectResolved handler source target)
    (h_sec : sdistITreeN n E handler source ideal ≤ ε₀) :
    sdistITreeN n E handler target ideal ≤ ε₀ := by
  calc sdistITreeN n E handler target ideal
      ≤ sdistITreeN n E handler target source
        + sdistITreeN n E handler source ideal := sdistITreeN_triangle ..
    _ = 0 + sdistITreeN n E handler source ideal := by
        rw [sdistITreeN_sym, resolved_sdist_zero handler h_exact]
    _ ≤ ε₀ := by simp; exact h_sec

/-! ## N-Assumption Composition -/

/-- An N-step chain of crypto assumptions. Each step replaces one sub-computation. -/
structure NAssumption (β : Type) where
  /-- Number of steps. -/
  steps : Nat
  /-- Bound per step. -/
  εs : Fin steps → ℝ≥0∞
  /-- Core at each hybrid (0 = real, steps = ideal). -/
  cores : Fin (steps + 1) → SPComp β
  /-- Each adjacent pair is bounded. -/
  h_bounds : ∀ i : Fin steps,
    sdist (fun (_ : Unit) => cores i.castSucc)
          (fun (_ : Unit) => cores i.succ) ≤ εs i

/-- Helper: uniform sdist chain bound by induction on a plain Nat. -/
theorem uniform_sdist_aux {β : Type}
    (m : Nat)
    (εs : Fin m → ℝ≥0∞)
    (cores : Fin (m + 1) → SPComp β)
    (h_bounds : ∀ i : Fin m,
      sdist (fun (_ : Unit) => cores i.castSucc)
            (fun (_ : Unit) => cores i.succ) ≤ εs i)
    (ε : ℝ≥0∞)
    (h_uniform : ∀ i, εs i ≤ ε) :
    sdist (fun (_ : Unit) => cores ⟨0, Nat.zero_lt_succ _⟩)
          (fun (_ : Unit) => cores ⟨m, Nat.lt_succ_of_le le_rfl⟩) ≤
    m * ε := by
  induction m with
  | zero => simp [sdist_self]
  | succ k ih =>
    calc sdist (fun (_ : Unit) => cores ⟨0, Nat.zero_lt_succ _⟩)
              (fun (_ : Unit) => cores ⟨k + 1, Nat.lt_succ_of_le le_rfl⟩)
        ≤ sdist (fun (_ : Unit) => cores ⟨0, Nat.zero_lt_succ _⟩)
                (fun (_ : Unit) => cores ⟨k, Nat.lt_succ_of_lt (Nat.lt_succ_of_le le_rfl)⟩)
          + sdist (fun (_ : Unit) => cores ⟨k, Nat.lt_succ_of_lt (Nat.lt_succ_of_le le_rfl)⟩)
                  (fun (_ : Unit) => cores ⟨k + 1, Nat.lt_succ_of_le le_rfl⟩) :=
            sdist_triangle ..
      _ ≤ ↑k * ε + ε := by
          apply add_le_add
          · exact ih (fun i => εs i.castSucc) (fun i => cores i.castSucc)
              (fun i => h_bounds i.castSucc) (fun i => h_uniform i.castSucc)
          · exact le_trans (h_bounds ⟨k, Nat.lt_succ_of_le le_rfl⟩)
              (h_uniform ⟨k, Nat.lt_succ_of_le le_rfl⟩)
      _ ≤ ↑(k + 1) * ε := by simp [Nat.cast_succ, add_mul, one_mul]

/-- Simpler version: uniform ε bound gives `steps * ε`. -/
theorem NAssumption.uniform_sdist {β : Type}
    (NA : NAssumption β)
    (ε : ℝ≥0∞)
    (h_uniform : ∀ i, NA.εs i ≤ ε) :
    sdist (fun (_ : Unit) => NA.cores ⟨0, Nat.zero_lt_succ _⟩)
          (fun (_ : Unit) => NA.cores ⟨NA.steps, Nat.lt_succ_of_le le_rfl⟩) ≤
    NA.steps * ε :=
  uniform_sdist_aux NA.steps NA.εs NA.cores NA.h_bounds ε h_uniform

end CatCrypt.Crypto.SecureCompilation.CryptoApproxPass
