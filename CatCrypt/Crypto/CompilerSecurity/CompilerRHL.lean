/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Framework

/-!
# Relational Hoare Logic for Compiler Correctness

Structural rules for proving `CompilerCorrect` between source and target
ITreeN computations. Inspired by Jasmin's `wkequiv` / `wiequiv_f` RHL
(arXiv 2511.11292, Section 4).

## Rules

* `rhl_done` — both sides return the same value
* `rhl_vis_match` — both sides emit the same event with related continuations
* `rhl_tau_match` — both sides take a silent step with related continuations
* `rhl_bind` — sequential composition
* `rhl_embed` — lift SPComp equality to ITreeN
* `rhl_consequence` — weaken via function equality
* `rhl_trans` — transitivity (compose compiler passes)

## Key design

In the bounded `ITreeN n E` setting, `CompilerCorrect` is definitional
equality of functions. The RHL rules decompose structural equality of
ITreeN computations into simpler equalities on sub-components.

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN
open scoped ENNReal

/-! ## Structural Rules -/

/-- Both sides return the same value. -/
theorem rhl_done {α : Type} {E : EventSig} {n : Nat}
    (a : α) :
    @CompilerCorrect Unit _ E n
      (fun _ => ITreeN.done n a)
      (fun _ => ITreeN.done n a) :=
  fun _ => rfl

/-- Both sides emit the same visible event with pointwise-equal continuations. -/
theorem rhl_vis_match {α : Type} {E : EventSig} {n : Nat}
    (e : E.Event) {k₁ k₂ : E.Resp e → ITreeN n E α}
    (hk : ∀ r, k₁ r = k₂ r) :
    @CompilerCorrect Unit _ E (n + 1)
      (fun _ => ITreeN.vis n e k₁)
      (fun _ => ITreeN.vis n e k₂) := by
  intro _
  have : k₁ = k₂ := funext hk
  subst this; rfl

/-- Both sides take a silent step with equal continuations. -/
theorem rhl_tau_match {α : Type} {E : EventSig} {n : Nat}
    {k₁ k₂ : ITreeN n E α}
    (hk : k₁ = k₂) :
    @CompilerCorrect Unit _ E (n + 1)
      (fun _ => ITreeN.yield n k₁)
      (fun _ => ITreeN.yield n k₂) := by
  intro _; rw [hk]

/-- Embed SPComp equality into ITreeN. -/
theorem rhl_embed_spcomp {α : Type} {E : EventSig} {n : Nat}
    {c₁ c₂ : SPComp α}
    (h : c₁ = c₂) :
    @CompilerCorrect Unit _ E n
      (fun _ => embedSPComp n c₁)
      (fun _ => embedSPComp n c₂) :=
  fun _ => congrArg (embedSPComp n) h

/-! ## Composition Rules -/

/-- Sequential bind: if heads and tails are equal, so is the composition. -/
theorem rhl_bind {hon α β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {f₁ f₂ : hon → ITreeN n E α}
    {g₁ g₂ : α → ITreeN n E β}
    (hf : CompilerCorrect f₁ f₂)
    (hg : ∀ a, g₁ a = g₂ a) :
    CompilerCorrect
      (fun x => ITreeN.bind' handler n (f₁ x) g₁)
      (fun x => ITreeN.bind' handler n (f₂ x) g₂) :=
  fun x => by simp only [hf x, funext hg]

/-- Consequence: rewrite source/target via function equalities. -/
theorem rhl_consequence {hon β : Type} {E : EventSig} {n : Nat}
    {f₁ f₂ g₁ g₂ : hon → ITreeN n E β}
    (hf : ∀ x, f₁ x = g₁ x)
    (hg : ∀ x, f₂ x = g₂ x)
    (h : CompilerCorrect g₁ g₂) :
    CompilerCorrect f₁ f₂ :=
  fun x => by rw [hf x, hg x]; exact h x

/-- Transitivity: compose two correct passes. -/
theorem rhl_trans {hon β : Type} {E : EventSig} {n : Nat}
    {p₁ p₂ p₃ : hon → ITreeN n E β}
    (h₁₂ : CompilerCorrect p₁ p₂)
    (h₂₃ : CompilerCorrect p₂ p₃) :
    CompilerCorrect p₁ p₃ :=
  compiler_correct_trans h₁₂ h₂₃

/-! ## Per-Round Rules -/

/-- At level 0 (SPComp), compiler correctness reduces to SPComp equality. -/
theorem rhl_spcomp {hon α : Type} {E : EventSig}
    {f₁ f₂ : hon → SPComp α}
    (h : ∀ x, f₁ x = f₂ x) :
    @CompilerCorrect hon α E 0 f₁ f₂ := h

/-- Distribute compiler correctness over a common SPComp prefix. -/
theorem rhl_spcomp_bind {hon α β : Type} {E : EventSig} {n : Nat}
    {c : hon → SPComp α}
    {k₁ k₂ : α → ITreeN (n + 1) E β}
    (hk : ∀ a, k₁ a = k₂ a) :
    @CompilerCorrect hon β E (n + 1)
      (fun x => SPComp.bind (c x) k₁)
      (fun x => SPComp.bind (c x) k₂) :=
  fun x => by rw [funext hk]

/-! ## Stateful Rules -/

/-- Lift pointwise RHL to stateful computations. -/
theorem rhl_stateful {hon S β : Type} {E : EventSig} {n : Nat}
    {source target : hon → StatefulITreeN S n E β}
    (h : ∀ x s, source x s = target x s) :
    CompilerCorrectStateful source target := h

/-- Stateful bind. -/
theorem rhl_stateful_bind {hon S α β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {f₁ f₂ : hon → StatefulITreeN S n E α}
    {g₁ g₂ : α × S → ITreeN n E (β × S)}
    (hf : CompilerCorrectStateful f₁ f₂)
    (hg : ∀ a, g₁ a = g₂ a) :
    CompilerCorrectStateful
      (fun x s => ITreeN.bind' handler n (f₁ x s) g₁)
      (fun x s => ITreeN.bind' handler n (f₂ x s) g₂) :=
  fun x s => by show ITreeN.bind' handler n (f₁ x s) g₁ = ITreeN.bind' handler n (f₂ x s) g₂
                simp only [hf x s, funext hg]

/-! ## Template-Based Rules -/

/-- If two computations share a template parameterized by a core SPComp,
    and the core computations are equal, then the full computations are equal.

    This is the key pattern for Jasmin-style compiler correctness:
    most passes preserve the event structure and only change the leaf
    computations. -/
theorem rhl_template {hon β γ : Type} {E : EventSig} {n : Nat}
    (template : SPComp γ → hon → ITreeN n E β)
    {core₁ core₂ : SPComp γ}
    (hcore : core₁ = core₂) :
    CompilerCorrect (template core₁) (template core₂) :=
  fun x => congrFun (congrArg template hcore) x

/-- Stateful template rule. -/
theorem rhl_stateful_template {hon S β γ : Type} {E : EventSig} {n : Nat}
    (template : SPComp γ → hon → StatefulITreeN S n E β)
    {core₁ core₂ : SPComp γ}
    (hcore : core₁ = core₂) :
    CompilerCorrectStateful (template core₁) (template core₂) :=
  fun x s => congrFun (congrFun (congrArg template hcore) x) s

end CatCrypt.Crypto.SecureCompilation
