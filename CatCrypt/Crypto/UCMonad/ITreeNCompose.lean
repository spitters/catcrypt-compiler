/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.UCMonad.ITreeN

/-!
# ITreeN Composition and Simulation

This file defines composition operations for `ITreeN n E α`, including:
- `resolveVis`: eliminate all visible events, converting to `emptyEvSig`
- `interpret`: UC simulator — replace events from `E` with computations in `E'`
- `UCEmulatesConcurrent`: UC emulation with adversary interaction between rounds

## Axiom status

**0 axioms**, **0 sorries**. All proofs complete.
-/

@[expose] public section

namespace UCMonad.ITreeNUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Section 1: Resolve Vis Events -/

/-- Eliminate all visible events from an `ITreeN`, producing an event-free tree.
    Events are resolved using the SPComp-level handler, preserving round structure. -/
noncomputable def ITreeN.resolveVis {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    (n : Nat) → ITreeN n E α → ITreeN n emptyEvSig α
  | 0, c => c
  | n + 1, c => SPComp.bind c (fun
    | .inl a => SPComp.pure (Sum.inl a)
    | .inr (.inl k) => SPComp.pure (Sum.inr (Sum.inl (ITreeN.resolveVis handler n k)))
    | .inr (.inr ⟨e, k⟩) =>
      SPComp.bind (handler e) (fun r =>
        SPComp.pure (Sum.inr (Sum.inl (ITreeN.resolveVis handler n (k r))))))

/-! ## Section 2: Interpret (UC Simulator) -/

/-- UC simulator interpretation: replace events from `E` with `ITreeN`-level
    computations in `E'`. The simulator `sim` handles each `E`-event by
    producing an `ITreeN n E' (E.Resp e)` computation. -/
noncomputable def ITreeN.interpret {α : Type} {E E' : EventSig}
    (spHandler : ∀ e : E'.Event, SPComp (E'.Resp e)) :
    (n : Nat) → (sim : ∀ e : E.Event, ITreeN n E' (E.Resp e)) →
    ITreeN n E α → ITreeN n E' α
  | 0, _, c => c
  | n + 1, sim, c => SPComp.bind c (fun
    | .inl a => (SPComp.pure (Sum.inl a) : SPComp (ITreeNStep n E' α))
    | .inr (.inl k) =>
      (SPComp.pure (Sum.inr (Sum.inl
        (ITreeN.interpret spHandler n
          (fun e => ITreeN.flatten spHandler n (sim e)) k))) :
        SPComp (ITreeNStep n E' α))
    | .inr (.inr ⟨e, k⟩) =>
      -- Run the simulator for event e, bind the response, recurse
      (SPComp.pure (Sum.inr (Sum.inl
        (ITreeN.bind' spHandler n (ITreeN.flatten spHandler n (sim e))
          (fun r => ITreeN.interpret spHandler n
            (fun e' => ITreeN.flatten spHandler n (sim e')) (k r))))) :
        SPComp (ITreeNStep n E' α)))

/-! ## Section 3: UC Emulation with Concurrent Adversary -/

/-- UC emulation with concurrent adversary interaction.

    Unlike `UCEmulates` (which uses `flattenAll` to collapse all rounds),
    `UCEmulatesConcurrent` keeps the round structure, allowing the adversary
    to interact between rounds via visible events. -/
noncomputable def UCEmulatesConcurrent {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (ε : ℝ≥0∞) {hon out leak view : Type}
    (π : hon → ITreeN n E (out ⊕ leak))
    (F : hon → ITreeN n E (out ⊕ view)) :=
  ∀ A : (out ⊕ leak) → ITreeN n E Bool,
  ∃ S : (out ⊕ view) → ITreeN n E Bool,
    sdistITreeN n E handler
      (fun a => ITreeN.bind' handler n (π a) A)
      (fun a => ITreeN.bind' handler n (F a) S) ≤ ε

/-- Reflexivity: any protocol UC-emulates itself with distance 0. -/
theorem UCEmulatesConcurrent_refl {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak : Type}
    (π : hon → ITreeN n E (out ⊕ leak)) :
    UCEmulatesConcurrent handler n 0 π π := by
  intro A; exact ⟨A, le_of_eq (sdistITreeN_self n E handler _)⟩

/-- Transitivity: UC emulation composes with additive distance. -/
theorem UCEmulatesConcurrent_trans {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak₁ leak₂ view₂ : Type}
    {π : hon → ITreeN n E (out ⊕ leak₁)}
    {Q : hon → ITreeN n E (out ⊕ leak₂)}
    {F : hon → ITreeN n E (out ⊕ view₂)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : UCEmulatesConcurrent handler n ε₁ π Q)
    (h₂ : UCEmulatesConcurrent handler n ε₂ Q F) :
    UCEmulatesConcurrent handler n (ε₁ + ε₂) π F := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (sdistITreeN_triangle n E handler _ _ _) (add_le_add hS₁ hS₂)⟩

/-- Adversary composition: composing the adversary with a continuation
    preserves UC emulation. Given UC emulation `h` and a continuation `k_π`,
    the adversary `A ∘ k_π` uses the base simulator directly. -/
theorem UCEmulatesConcurrent_adversary_comp {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out₁ out₂ leak view : Type}
    {π : hon → ITreeN n E (out₁ ⊕ leak)}
    {F : hon → ITreeN n E (out₁ ⊕ view)}
    {ε : ℝ≥0∞}
    (h : UCEmulatesConcurrent handler n ε π F)
    (k_π : (out₁ ⊕ leak) → ITreeN n E (out₂ ⊕ leak))
    (A : (out₂ ⊕ leak) → ITreeN n E Bool) :
    ∃ S₁ : (out₁ ⊕ view) → ITreeN n E Bool,
      sdistITreeN n E handler
        (fun a => ITreeN.bind' handler n (ITreeN.bind' handler n (π a) k_π) A)
        (fun a => ITreeN.bind' handler n (F a) S₁) ≤ ε := by
  -- Rewrite bind-bind to bind-(bind) via bind_assoc
  have hassoc : ∀ a, ITreeN.bind' handler n (ITreeN.bind' handler n (π a) k_π) A =
      ITreeN.bind' handler n (π a) (fun x => ITreeN.bind' handler n (k_π x) A) :=
    fun a => itreeN_bind_assoc handler n (π a) k_π A
  simp only [hassoc]
  exact h (fun x => ITreeN.bind' handler n (k_π x) A)

end UCMonad.ITreeNUC
