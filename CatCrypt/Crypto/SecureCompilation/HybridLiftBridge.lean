/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.TemplateCompilation
import CatCrypt.Crypto.SecureCompilation.HybridComposition

/-!
# L2 HybridLift as CompilerCorrectResolved

Shows that the L2 template pattern (used in SSH, Kerberos, NoiseNK, OEKE,
WireGuard protocols) is an instance of `CompilerCorrectResolved`. When two
template instances share the same core, they are `CompilerCorrectResolved`.
When they have different cores, their `sdistITreeN` reduces to the `sdist`
between cores.

This is the bridge between the existing L2 security proofs and the secure
compilation framework: each "hybrid hop" in the L2 chain is a
compilation-style step.

## Key insight

The L2 template factoring property:

```
flattenAll handler n (template core x s) =
  bind (sharedPrefix handler x s) (fun _ => bind core formatResult)
```

means `CompilerCorrectResolved` for equal cores is trivial, and `sdistITreeN`
for different cores is bounded by `sdist` between cores (via the template
sdist bound from TemplateCompilation.lean).

## Main theorems

* `L2Template` -- abstract L2 template structure
* `L2Template.resolved_of_core_eq` -- equal cores gives CompilerCorrectResolved
* `L2Template.sdist_le_core` -- sdistITreeN bounded by core sdist
* `L2Template.fourHop_security` -- 4-hop security (SSH/Kerberos pattern)
* `L2Template.compilation_pipeline` -- compilation preserves L2 security

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation.HybridLiftBridge

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation TemplateCompilation HybridComposition
open scoped ENNReal

/-! ## Abstract L2 Template -/

/-- Abstract L2 template: a protocol parameterized by a core computation,
    where `flattenAll` factors through a shared prefix. This captures the
    pattern used in SSH/Kerberos/NoiseNK/OEKE security proofs. -/
structure L2Template (hon β : Type) (E : EventSig) (n : Nat) where
  /-- Template: takes a core and produces a protocol. -/
  mkProtocol : SPComp β → hon → ITreeN n E β
  /-- Event handler. -/
  handler : forall e : E.Event, SPComp (E.Resp e)
  /-- Shared prefix (handler binds, state setup). -/
  sharedPrefix : hon → SPComp Unit
  /-- The factoring property: flattenAll of the template factors through
      the shared prefix. This is the key structural property. -/
  h_factor : forall core x,
    ITreeN.flattenAll handler n (mkProtocol core x) =
    SPComp.bind (sharedPrefix x) (fun _ => core)

/-! ## Core Equality → CompilerCorrectResolved -/

/-- When two template instances use equal cores, they are CompilerCorrectResolved.
    This is the fundamental bridge between L2 and secure compilation. -/
theorem L2Template.resolved_of_core_eq {hon β : Type} {E : EventSig} {n : Nat}
    (T : L2Template hon β E n)
    (core₁ core₂ : SPComp β) (h_eq : core₁ = core₂) :
    CompilerCorrectResolved T.handler (T.mkProtocol core₁) (T.mkProtocol core₂) :=
  template_resolved_of_flattenAll_factor T.handler T.mkProtocol T.sharedPrefix
    T.h_factor core₁ core₂ h_eq

/-- Equal cores gives zero sdist. -/
theorem L2Template.sdist_zero_of_core_eq {hon β : Type} {E : EventSig} {n : Nat}
    (T : L2Template hon β E n)
    (core₁ core₂ : SPComp β) (h_eq : core₁ = core₂) :
    sdistITreeN n E T.handler (T.mkProtocol core₁) (T.mkProtocol core₂) = 0 :=
  resolved_sdist_zero T.handler (T.resolved_of_core_eq core₁ core₂ h_eq)

/-! ## sdist Bound via Core sdist -/

/-- The sdistITreeN between two template instances is bounded by the sdist
    between their cores. This is the generic version of SSH's
    `sdist_template_le_core`. -/
theorem L2Template.sdist_le_core {hon β : Type} {E : EventSig} {n : Nat}
    (T : L2Template hon β E n)
    (core₁ core₂ : SPComp β) :
    sdistITreeN n E T.handler (T.mkProtocol core₁) (T.mkProtocol core₂) ≤
    sdist (fun (_ : Unit) => core₁) (fun (_ : Unit) => core₂) :=
  template_sdist_le_core T.handler T.mkProtocol T.sharedPrefix T.h_factor core₁ core₂

/-! ## Hybrid Chain on Templates -/

/-- 2-hop hybrid on template cores: core₀ → core₁ → core₂. -/
theorem L2Template.twoHop_sdist {hon β : Type} {E : EventSig} {n : Nat}
    (T : L2Template hon β E n)
    (core₀ core₁ core₂ : SPComp β)
    (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : sdist (fun (_ : Unit) => core₀) (fun (_ : Unit) => core₁) ≤ ε₁)
    (h₂ : sdist (fun (_ : Unit) => core₁) (fun (_ : Unit) => core₂) ≤ ε₂) :
    sdistITreeN n E T.handler (T.mkProtocol core₀) (T.mkProtocol core₂) ≤ ε₁ + ε₂ :=
  twoHop_sdist_le T.handler (T.mkProtocol core₀) (T.mkProtocol core₁) (T.mkProtocol core₂)
    ε₁ ε₂
    (le_trans (T.sdist_le_core core₀ core₁) h₁)
    (le_trans (T.sdist_le_core core₁ core₂) h₂)

/-- 4-hop hybrid on template cores (SSH/Kerberos pattern):
    core_real → core₁ → core₂ → core₃ → core_ideal.
    Each hop uses a different crypto assumption. -/
theorem L2Template.fourHop_sdist {hon β : Type} {E : EventSig} {n : Nat}
    (T : L2Template hon β E n)
    (core₀ core₁ core₂ core₃ core₄ : SPComp β)
    (ε₁ ε₂ ε₃ ε₄ : ℝ≥0∞)
    (h₁ : sdist (fun (_ : Unit) => core₀) (fun (_ : Unit) => core₁) ≤ ε₁)
    (h₂ : sdist (fun (_ : Unit) => core₁) (fun (_ : Unit) => core₂) ≤ ε₂)
    (h₃ : sdist (fun (_ : Unit) => core₂) (fun (_ : Unit) => core₃) ≤ ε₃)
    (h₄ : sdist (fun (_ : Unit) => core₃) (fun (_ : Unit) => core₄) ≤ ε₄) :
    sdistITreeN n E T.handler (T.mkProtocol core₀) (T.mkProtocol core₄) ≤
    ε₁ + ε₂ + ε₃ + ε₄ :=
  fourHop_sdist_le T.handler
    (T.mkProtocol core₀) (T.mkProtocol core₁)
    (T.mkProtocol core₂) (T.mkProtocol core₃) (T.mkProtocol core₄)
    ε₁ ε₂ ε₃ ε₄
    (le_trans (T.sdist_le_core core₀ core₁) h₁)
    (le_trans (T.sdist_le_core core₁ core₂) h₂)
    (le_trans (T.sdist_le_core core₂ core₃) h₃)
    (le_trans (T.sdist_le_core core₃ core₄) h₄)

/-! ## Security Transfer -/

/-- 4-hop security pipeline: if the template with core_real has sdist ≤ ε to
    the ideal, then the template with any core in the hybrid chain inherits
    the bound plus the hybrid chain distance. -/
theorem L2Template.fourHop_security {hon β : Type} {E : EventSig} {n : Nat}
    (T : L2Template hon β E n)
    {core_real core₁ core₂ core₃ core_ideal : SPComp β}
    {ideal : hon → ITreeN n E β}
    {ε₁ ε₂ ε₃ ε₄ : ℝ≥0∞}
    (h₁ : sdist (fun (_ : Unit) => core_real) (fun (_ : Unit) => core₁) ≤ ε₁)
    (h₂ : sdist (fun (_ : Unit) => core₁) (fun (_ : Unit) => core₂) ≤ ε₂)
    (h₃ : sdist (fun (_ : Unit) => core₂) (fun (_ : Unit) => core₃) ≤ ε₃)
    (h₄ : sdist (fun (_ : Unit) => core₃) (fun (_ : Unit) => core_ideal) ≤ ε₄)
    (h_ideal : sdistITreeN n E T.handler (T.mkProtocol core_ideal) ideal = 0) :
    sdistITreeN n E T.handler (T.mkProtocol core_real) ideal ≤
    ε₁ + ε₂ + ε₃ + ε₄ := by
  calc sdistITreeN n E T.handler (T.mkProtocol core_real) ideal
      ≤ sdistITreeN n E T.handler (T.mkProtocol core_real) (T.mkProtocol core_ideal)
        + sdistITreeN n E T.handler (T.mkProtocol core_ideal) ideal :=
        sdistITreeN_triangle ..
    _ ≤ (ε₁ + ε₂ + ε₃ + ε₄) + 0 := by
        apply add_le_add
        · exact T.fourHop_sdist core_real core₁ core₂ core₃ core_ideal
            ε₁ ε₂ ε₃ ε₄ h₁ h₂ h₃ h₄
        · exact le_of_eq h_ideal
    _ = ε₁ + ε₂ + ε₃ + ε₄ := by simp

/-! ## Compilation Pipeline on L2 Templates -/

/-- Compilation + L2 security: if the compiled protocol is CompilerCorrectResolved
    to the template, and the template has 4-hop security, the compiled protocol
    inherits the bound. -/
theorem L2Template.compilation_pipeline {hon β : Type} {E : EventSig} {n : Nat}
    (T : L2Template hon β E n)
    {compiled : hon → ITreeN n E β}
    {core_real : SPComp β}
    {ideal : hon → ITreeN n E β}
    {ε : ℝ≥0∞}
    (h_compile : CompilerCorrectResolved T.handler (T.mkProtocol core_real) compiled)
    (h_sec : sdistITreeN n E T.handler (T.mkProtocol core_real) ideal ≤ ε) :
    sdistITreeN n E T.handler compiled ideal ≤ ε :=
  resolved_security_transfer T.handler h_compile h_sec

end CatCrypt.Crypto.SecureCompilation.HybridLiftBridge
