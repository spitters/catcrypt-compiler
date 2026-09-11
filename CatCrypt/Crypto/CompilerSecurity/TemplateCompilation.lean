/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Resolved

/-!
# Template Compilation Bridge

Connects the L2 "template" pattern (used in SSH, Kerberos, NoiseNK, OEKE protocols)
to the `CompilerCorrectResolved` framework.

The template pattern: protocols share a common event structure (vis nodes) and differ
only in the leaf `SPComp` core. Two template instances with equal cores are
`CompilerCorrectResolved`, and `sdist` between them reduces to `sdist` of the cores.

## Main theorems

* `template_resolved_of_flattenAll_factor` -- factoring + core equality gives resolved CC
* `template_resolved_of_core_eq` -- core equality implies CompilerCorrectResolved
* `eventElim_resolved` -- compilation that removes a debug event
* `resolved_security_transfer` -- generic security transfer via resolved correctness

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TemplateCompilation

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open scoped ENNReal

/-! ## Generic Template Factoring -/

/-- If `flattenAll` of a template factors through a shared prefix, and two template
    instances use equal cores, they are `CompilerCorrectResolved`. -/
theorem template_resolved_of_flattenAll_factor
    {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (mkProtocol : SPComp β -> hon -> ITreeN n E β)
    (sharedPrefix : hon -> SPComp Unit)
    (h_factor : forall core x,
      ITreeN.flattenAll handler n (mkProtocol core x) =
      SPComp.bind (sharedPrefix x) (fun _ => core))
    (core₁ core₂ : SPComp β)
    (h_eq : core₁ = core₂) :
    CompilerCorrectResolved handler (mkProtocol core₁) (mkProtocol core₂) := by
  intro x
  rw [h_factor, h_factor, h_eq]

/-- Two template instances with the same core are resolved-correct for any handler. -/
theorem template_resolved_of_core_eq
    {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (mkProtocol : SPComp β -> hon -> ITreeN n E β)
    (core₁ core₂ : SPComp β)
    (h_eq : core₁ = core₂) :
    CompilerCorrectResolved handler (mkProtocol core₁) (mkProtocol core₂) := by
  intro x; rw [h_eq]

/-- Stateful version: template resolved correctness from core equality. -/
theorem template_stateful_resolved_of_core_eq
    {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (mkProtocol : SPComp β -> hon -> S -> ITreeN n E β)
    (core₁ core₂ : SPComp β)
    (h_eq : core₁ = core₂) :
    forall x s, ITreeN.flattenAll handler n (mkProtocol core₁ x s) =
                ITreeN.flattenAll handler n (mkProtocol core₂ x s) := by
  intros; rw [h_eq]

/-! ## Generic sdist Bound via Factoring -/

/-- If `flattenAll` factors through a shared prefix, then `sdistITreeN` between
    two template instances is bounded by `sdist` between their cores.

    This is the generic version of `sdist_template_le_core` from SSH/L2/HybridLift. -/
theorem template_sdist_le_core
    {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (mkProtocol : SPComp β -> hon -> ITreeN n E β)
    (sharedPrefix : hon -> SPComp Unit)
    (h_factor : forall core x,
      ITreeN.flattenAll handler n (mkProtocol core x) =
      SPComp.bind (sharedPrefix x) (fun _ => core))
    (core₁ core₂ : SPComp β) :
    sdistITreeN n E handler (mkProtocol core₁) (mkProtocol core₂) ≤
    sdist (fun (_ : Unit) => core₁) (fun (_ : Unit) => core₂) := by
  unfold sdistITreeN sdist
  apply iSup_le; intro D
  apply iSup_le; intro x
  apply iSup_le; intro h₀
  simp only [h_factor, SPComp.bind_assoc]
  apply absDiff_prTrue_bind_le (sharedPrefix x)
    (fun _ => SPComp.bind core₁ D) (fun _ => SPComp.bind core₂ D) h₀
  · intro _ h'
    apply le_add_of_absDiff_le
    exact le_iSup₂_of_le D () (le_iSup_of_le h' le_rfl)
  · intro _ h'
    apply le_add_of_absDiff_le
    rw [absDiff_comm]
    exact le_iSup₂_of_le D () (le_iSup_of_le h' le_rfl)

/-! ## Event Elimination as Template Compilation -/

/-- Source with an extra vis event before the core. -/
noncomputable def eventElim_source {β : Type} {E : EventSig}
    (n : Nat) (e : E.Event) (core : SPComp β) :
    Unit -> ITreeN (n + 1) E β :=
  fun () => ITreeN.vis n e (fun _ => embedSPComp n core)

/-- Target inlines the handler result, preserving the handler's probability mass. -/
noncomputable def eventElim_target {β : Type} {E : EventSig}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) (core : SPComp β) :
    Unit -> ITreeN (n + 1) E β :=
  fun () => ITreeN.bind' handler (n + 1)
    (embedSPComp (n + 1) (handler e))
    (fun _ => embedSPComp (n + 1) core)

/-- Event elimination is `CompilerCorrectResolved`. -/
theorem eventElim_resolved {β : Type} {E : EventSig}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) (core : SPComp β) :
    CompilerCorrectResolved handler
      (eventElim_source (E := E) n e core)
      (eventElim_target handler n e core) := by
  intro ()
  simp only [eventElim_source, eventElim_target]
  rw [flattenAll_vis handler n e, flattenAll_bind, flattenAll_embedSPComp]
  simp only [flattenAll_embedSPComp]

/-- sdist = 0 for the event elimination pass. -/
theorem eventElim_sdist_zero {β : Type} {E : EventSig}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) (core : SPComp β) :
    sdistITreeN (n + 1) E handler
      (eventElim_source (E := E) n e core)
      (eventElim_target handler n e core) = 0 :=
  resolved_sdist_zero handler (eventElim_resolved handler n e core)

/-! ## Security Transfer via Resolved Correctness -/

/-- Generic security transfer: resolved correctness preserves sdist bounds. -/
theorem resolved_security_transfer {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon -> ITreeN n E β}
    {ideal : hon -> ITreeN n E β}
    {ε : ℝ≥0∞}
    (hcc : CompilerCorrectResolved handler source target)
    (hsec : sdistITreeN n E handler source ideal ≤ ε) :
    sdistITreeN n E handler target ideal ≤ ε :=
  calc sdistITreeN n E handler target ideal
      ≤ sdistITreeN n E handler target source
        + sdistITreeN n E handler source ideal := sdistITreeN_triangle ..
    _ = 0 + sdistITreeN n E handler source ideal := by
        rw [sdistITreeN_sym, resolved_sdist_zero handler hcc]
    _ ≤ ε := by simp; exact hsec

end CatCrypt.Crypto.SecureCompilation.TemplateCompilation
