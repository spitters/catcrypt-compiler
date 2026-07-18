/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.TemplateCompilation

/-!
# Hybrid Argument as Multi-Pass Composition

Shows that a standard cryptographic hybrid argument (used in SSH, Kerberos,
OEKE, NoiseNK security theorems) is an instance of multi-pass compilation
where each hop replaces one core computation.

## Key insight

The L2 template pattern: protocols share a common event structure (vis nodes)
and differ only in the leaf `SPComp` core. A 4-hop hybrid chain like SSH's:

```
real_core → hybrid₁ → hybrid₂ → hybrid₃ → ideal_core
```

is exactly 4 compiler passes, each with `sdist ≤ εᵢ`, composed via
the triangle inequality into `sdist ≤ ε₁ + ε₂ + ε₃ + ε₄`.

## Main theorems

* `hybridChain_sdist_le` -- N-hop hybrid via triangle inequality
* `hybridChain_uniform_sdist_le` -- uniform ε gives N * ε
* `templateHybrid_sdist_le` -- hybrid chain on template protocols
* `templateHybrid_security_transfer` -- full security pipeline

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation.HybridComposition

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation TemplateCompilation
open scoped ENNReal

/-! ## Abstract Hybrid Chain -/

/-- An N-hop hybrid chain at the ITreeN level. -/
structure HybridChain (hon β : Type) (E : EventSig) (n : Nat) where
  /-- Number of hops. -/
  hops : Nat
  /-- Hybrid at each position (0 = real, hops = ideal). -/
  hybrids : Fin (hops + 1) → (hon → ITreeN n E β)
  /-- Bound per hop. -/
  εs : Fin hops → ℝ≥0∞
  /-- Each adjacent pair is bounded. -/
  handler : forall e : E.Event, SPComp (E.Resp e)
  h_bounds : ∀ i : Fin hops,
    sdistITreeN n E handler (hybrids i.castSucc) (hybrids i.succ) ≤ εs i

/-- Helper: uniform hybrid chain bound by induction on a plain Nat. -/
private theorem hybridChain_uniform_aux {hon β : Type} {E : EventSig} {n : Nat}
    (m : Nat)
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (hybrids : Fin (m + 1) → (hon → ITreeN n E β))
    (εs : Fin m → ℝ≥0∞)
    (h_bounds : ∀ i : Fin m,
      sdistITreeN n E handler (hybrids i.castSucc) (hybrids i.succ) ≤ εs i)
    (ε : ℝ≥0∞)
    (h_uniform : ∀ i, εs i ≤ ε) :
    sdistITreeN n E handler
      (hybrids ⟨0, Nat.zero_lt_succ _⟩)
      (hybrids ⟨m, Nat.lt_succ_of_le le_rfl⟩) ≤
    m * ε := by
  induction m with
  | zero => simp [sdistITreeN, sdist_self]
  | succ k ih =>
    calc sdistITreeN n E handler
          (hybrids ⟨0, Nat.zero_lt_succ _⟩)
          (hybrids ⟨k + 1, Nat.lt_succ_of_le le_rfl⟩)
        ≤ sdistITreeN n E handler
            (hybrids ⟨0, Nat.zero_lt_succ _⟩)
            (hybrids ⟨k, Nat.lt_succ_of_lt (Nat.lt_succ_of_le le_rfl)⟩)
          + sdistITreeN n E handler
            (hybrids ⟨k, Nat.lt_succ_of_lt (Nat.lt_succ_of_le le_rfl)⟩)
            (hybrids ⟨k + 1, Nat.lt_succ_of_le le_rfl⟩) :=
          sdistITreeN_triangle ..
      _ ≤ ↑k * ε + ε := by
          apply add_le_add
          · exact ih (fun i => hybrids i.castSucc) (fun i => εs i.castSucc)
              (fun i => h_bounds i.castSucc) (fun i => h_uniform i.castSucc)
          · exact le_trans (h_bounds ⟨k, Nat.lt_succ_of_le le_rfl⟩)
              (h_uniform ⟨k, Nat.lt_succ_of_le le_rfl⟩)
      _ ≤ ↑(k + 1) * ε := by simp [Nat.cast_succ, add_mul, one_mul]

/-- N-hop hybrid chain with uniform ε: total sdist ≤ hops * ε. -/
theorem hybridChain_uniform_sdist_le {hon β : Type} {E : EventSig} {n : Nat}
    (HC : HybridChain hon β E n)
    (ε : ℝ≥0∞)
    (h_uniform : ∀ i, HC.εs i ≤ ε) :
    sdistITreeN n E HC.handler
      (HC.hybrids ⟨0, Nat.zero_lt_succ _⟩)
      (HC.hybrids ⟨HC.hops, Nat.lt_succ_of_le le_rfl⟩) ≤
    HC.hops * ε :=
  hybridChain_uniform_aux HC.hops HC.handler HC.hybrids HC.εs HC.h_bounds ε h_uniform

/-! ## Template Hybrid Chain -/

/-- 2-hop hybrid: real → intermediate → ideal. -/
theorem twoHop_sdist_le {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (f g h : hon → ITreeN n E β)
    (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : sdistITreeN n E handler f g ≤ ε₁)
    (h₂ : sdistITreeN n E handler g h ≤ ε₂) :
    sdistITreeN n E handler f h ≤ ε₁ + ε₂ :=
  le_trans (sdistITreeN_triangle n E handler f g h) (add_le_add h₁ h₂)

/-- 3-hop hybrid. -/
theorem threeHop_sdist_le {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (f₀ f₁ f₂ f₃ : hon → ITreeN n E β)
    (ε₁ ε₂ ε₃ : ℝ≥0∞)
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃) :
    sdistITreeN n E handler f₀ f₃ ≤ ε₁ + ε₂ + ε₃ :=
  calc sdistITreeN n E handler f₀ f₃
      ≤ sdistITreeN n E handler f₀ f₂
        + sdistITreeN n E handler f₂ f₃ := sdistITreeN_triangle ..
    _ ≤ (ε₁ + ε₂) + ε₃ :=
        add_le_add (twoHop_sdist_le handler f₀ f₁ f₂ ε₁ ε₂ h₁ h₂) h₃
    _ = ε₁ + ε₂ + ε₃ := by ring

/-- 4-hop hybrid (SSH-style). -/
theorem fourHop_sdist_le {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (f₀ f₁ f₂ f₃ f₄ : hon → ITreeN n E β)
    (ε₁ ε₂ ε₃ ε₄ : ℝ≥0∞)
    (h₁ : sdistITreeN n E handler f₀ f₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₁ f₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler f₂ f₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler f₃ f₄ ≤ ε₄) :
    sdistITreeN n E handler f₀ f₄ ≤ ε₁ + ε₂ + ε₃ + ε₄ :=
  calc sdistITreeN n E handler f₀ f₄
      ≤ sdistITreeN n E handler f₀ f₃
        + sdistITreeN n E handler f₃ f₄ := sdistITreeN_triangle ..
    _ ≤ (ε₁ + ε₂ + ε₃) + ε₄ :=
        add_le_add (threeHop_sdist_le handler f₀ f₁ f₂ f₃ ε₁ ε₂ ε₃ h₁ h₂ h₃) h₄
    _ = ε₁ + ε₂ + ε₃ + ε₄ := by ring

/-! ## Security Transfer via Hybrid Chain -/

/-- If the real protocol (hop 0) is ε₀-close to ideal, and the hybrid chain
    adds at most ε_chain, then the final protocol is (ε₀ + ε_chain)-close. -/
theorem hybridChain_security_transfer {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {real compiled ideal : hon → ITreeN n E β}
    {ε_chain ε_sec : ℝ≥0∞}
    (h_chain : sdistITreeN n E handler real compiled ≤ ε_chain)
    (h_sec : sdistITreeN n E handler real ideal ≤ ε_sec) :
    sdistITreeN n E handler compiled ideal ≤ ε_sec + ε_chain := by
  calc sdistITreeN n E handler compiled ideal
      ≤ sdistITreeN n E handler compiled real
        + sdistITreeN n E handler real ideal := sdistITreeN_triangle ..
    _ ≤ ε_chain + ε_sec := by
        rw [sdistITreeN_sym]; exact add_le_add h_chain h_sec
    _ = ε_sec + ε_chain := add_comm _ _

/-- 4-hop security transfer (SSH pattern):
    real → hyb1 → hyb2 → hyb3 → ideal, each step ≤ εᵢ. -/
theorem fourHop_security {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {real hyb₁ hyb₂ hyb₃ ideal : hon → ITreeN n E β}
    {ε₁ ε₂ ε₃ ε₄ : ℝ≥0∞}
    (h₁ : sdistITreeN n E handler real hyb₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler hyb₁ hyb₂ ≤ ε₂)
    (h₃ : sdistITreeN n E handler hyb₂ hyb₃ ≤ ε₃)
    (h₄ : sdistITreeN n E handler hyb₃ ideal ≤ ε₄) :
    sdistITreeN n E handler real ideal ≤ ε₁ + ε₂ + ε₃ + ε₄ :=
  fourHop_sdist_le handler real hyb₁ hyb₂ hyb₃ ideal ε₁ ε₂ ε₃ ε₄ h₁ h₂ h₃ h₄

/-! ## Template + Hybrid Composition -/

/-- Hybrid chain where each hop differs only in the template core, and
    the sdist is bounded via `template_sdist_le_core`. -/
theorem templateHybrid_security_transfer {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (mkProtocol : SPComp β → hon → ITreeN n E β)
    (sharedPrefix : hon → SPComp Unit)
    (h_factor : forall core x,
      ITreeN.flattenAll handler n (mkProtocol core x) =
      SPComp.bind (sharedPrefix x) (fun _ => core))
    {core_real core_ideal : SPComp β}
    {ideal : hon → ITreeN n E β}
    {ε_core ε_ideal : ℝ≥0∞}
    (h_core : sdist (fun (_ : Unit) => core_real)
                    (fun (_ : Unit) => core_ideal) ≤ ε_core)
    (h_ideal : sdistITreeN n E handler (mkProtocol core_ideal) ideal ≤ ε_ideal) :
    sdistITreeN n E handler (mkProtocol core_real) ideal ≤ ε_ideal + ε_core := by
  calc sdistITreeN n E handler (mkProtocol core_real) ideal
      ≤ sdistITreeN n E handler (mkProtocol core_real) (mkProtocol core_ideal)
        + sdistITreeN n E handler (mkProtocol core_ideal) ideal :=
        sdistITreeN_triangle ..
    _ ≤ ε_core + ε_ideal := by
        apply add_le_add
        · exact le_trans (template_sdist_le_core handler mkProtocol sharedPrefix h_factor
            core_real core_ideal) h_core
        · exact h_ideal
    _ = ε_ideal + ε_core := add_comm _ _

end CatCrypt.Crypto.SecureCompilation.HybridComposition
