/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.UCMonad.StateTITreeN
import CatCrypt.Crypto.UCMonad.ITreeNCompose
import CatCrypt.Crypto.UCMonad.ITreeNMultiSession
import CatCrypt.Crypto.UCMonad.ITreeNKCompose

/-!
# UCEmulatesConcurrentStateful: UC Emulation for Stateful Protocols

This file defines `UCEmulatesConcurrentStateful`, a variant of
`UCEmulatesConcurrent` (ITreeNCompose.lean) for stateful protocols that
use `StatefulITreeN S n E` (i.e., `StateT S (ITreeN n E)`).

## Problem

`UCEmulatesConcurrent` requires `out ⊕ leak` (Sum) return type, but
stateful protocols return `(out ⊕ leak) × State` (Product via StateT).
The types don't unify.

## Solution

The adversary receives `(out ⊕ leak) × S`, matching how `sdistITreeN`
already works for stateful protocols via the uncurrying pattern from
`StateTInstance.lean`.

## Main definitions

* `UCEmulatesConcurrentStateful` — UC emulation for stateful protocols
* `UCEmulatesConcurrentStateful_of_sdistITreeN` — lift from sdist bounds
* `UCEmulatesConcurrentStateful_refl` — reflexivity (distance 0)
* `UCEmulatesConcurrentStateful_trans` — transitivity (additive distance)
* `UCEmulatesConcurrentStateful_multisession` — k copies with same bound
* `sdistITreeN_stateful_par` — parallel composition (max bound)
* `sdistITreeN_bind` — sequential bind (additive bound)
* `sdistITreeN_stateful_seq` — stateful sequential composition
* `UCEmulatesConcurrentStateful_seq` — sequential at UC level
* `UCEmulatesConcurrentStatefulK` — Kantorovich-based UC for stateful protocols
* `UCEmulatesConcurrentStatefulK_implies_flat` — backward compatibility bridge
* `UCEmulatesConcurrentStatefulK_of_kdistITreeN` — lift from kdist bounds

## Axiom status

**0 axioms**, **0 sorries**. All proofs complete.
-/

namespace UCMonad.StateTITreeNCompose

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN
open scoped ENNReal

/-! ## Definition -/

/-- UC emulation with concurrent adversary interaction for stateful protocols.

    The adversary `A` receives `(out ⊕ leak) × S` — the protocol output paired
    with the final state. The simulator `Sim` receives `(out ⊕ view) × S`.

    This generalizes `UCEmulatesConcurrent` to `StatefulITreeN S n E`. -/
noncomputable def UCEmulatesConcurrentStateful {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (ε : ℝ≥0∞) {hon S out leak view : Type}
    (π : hon → StatefulITreeN S n E (out ⊕ leak))
    (F : hon → StatefulITreeN S n E (out ⊕ view)) :=
  ∀ A : ((out ⊕ leak) × S) → ITreeN n E Bool,
  ∃ Sim : ((out ⊕ view) × S) → ITreeN n E Bool,
    sdistITreeN n E handler
      (fun (ps : hon × S) => ITreeN.bind' handler n (π ps.1 ps.2) A)
      (fun (ps : hon × S) => ITreeN.bind' handler n (F ps.1 ps.2) Sim) ≤ ε

/-! ## From sdist bounds -/

/-- Lift a `sdistITreeN` bound to `UCEmulatesConcurrentStateful`.

    When `leak = view` (same interface), the simulator is the identity (`Sim = A`).
    The bound follows from `sdistITreeN_comp_right`. -/
theorem UCEmulatesConcurrentStateful_of_sdistITreeN {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S out leak : Type} {ε : ℝ≥0∞}
    {π F : hon → StatefulITreeN S n E (out ⊕ leak)}
    (h : sdistITreeN n E handler
      (fun (ps : hon × S) => π ps.1 ps.2)
      (fun (ps : hon × S) => F ps.1 ps.2) ≤ ε) :
    UCEmulatesConcurrentStateful handler n ε π F := by
  intro A
  exact ⟨A, le_trans (sdistITreeN_comp_right n E handler _ _ A) h⟩

/-! ## Structural properties -/

/-- Reflexivity: any stateful protocol UC-emulates itself with distance 0. -/
theorem UCEmulatesConcurrentStateful_refl {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S out leak : Type}
    (π : hon → StatefulITreeN S n E (out ⊕ leak)) :
    UCEmulatesConcurrentStateful handler n 0 π π := by
  intro A
  exact ⟨A, le_of_eq (sdistITreeN_self n E handler _)⟩

/-- Transitivity: UC emulation for stateful protocols composes with additive distance. -/
theorem UCEmulatesConcurrentStateful_trans {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S out leak₁ leak₂ view₂ : Type}
    {π : hon → StatefulITreeN S n E (out ⊕ leak₁)}
    {Q : hon → StatefulITreeN S n E (out ⊕ leak₂)}
    {F : hon → StatefulITreeN S n E (out ⊕ view₂)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : UCEmulatesConcurrentStateful handler n ε₁ π Q)
    (h₂ : UCEmulatesConcurrentStateful handler n ε₂ Q F) :
    UCEmulatesConcurrentStateful handler n (ε₁ + ε₂) π F := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (sdistITreeN_triangle n E handler _ _ _) (add_le_add hS₁ hS₂)⟩

/-! ## Multi-session -/

/-- Replacing the first component of a product input doesn't increase sdist
    when the function only depends on the second component. -/
theorem sdistITreeN_project_snd_unit {α β γ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f g : β → ITreeN n E γ) :
    sdistITreeN n E handler
      (fun (ps : α × β) => f ps.2) (fun (ps : α × β) => g ps.2) ≤
    sdistITreeN n E handler
      (fun (ps : Unit × β) => f ps.2) (fun (ps : Unit × β) => g ps.2) := by
  unfold sdistITreeN sdist
  apply iSup_le; intro D
  apply iSup_le; intro ⟨_, b⟩
  apply iSup_le; intro h₀
  exact le_iSup₂_of_le D ((), b) (le_iSup_of_le h₀ le_rfl)

/-- Stateful multi-session: k copies of the same stateful protocol UC-emulate
    with the same bound. The bound doesn't increase because each session is
    independent and the sdist takes the supremum over all inputs. -/
theorem UCEmulatesConcurrentStateful_multisession {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {S out leak view : Type} {ε : ℝ≥0∞}
    (π : StatefulITreeN S n E (out ⊕ leak))
    (F : StatefulITreeN S n E (out ⊕ view))
    (h : UCEmulatesConcurrentStateful handler n ε (fun () => π) (fun () => F))
    (k : Nat) :
    UCEmulatesConcurrentStateful handler n ε
      (fun (_ : Fin k) => π) (fun (_ : Fin k) => F) := by
  intro A
  obtain ⟨Sim, hSim⟩ := h A
  refine ⟨Sim, ?_⟩
  -- Goal: sdist over Fin k × S ≤ ε; hypothesis: sdist over Unit × S ≤ ε
  -- The functions only depend on the S component, so we can project
  show sdistITreeN n E handler
    (fun (ps : Fin k × S) => ITreeN.bind' handler n (π ps.2) A)
    (fun (ps : Fin k × S) => ITreeN.bind' handler n (F ps.2) Sim) ≤ ε
  exact le_trans
    (sdistITreeN_project_snd_unit handler n
      (fun s => ITreeN.bind' handler n (π s) A)
      (fun s => ITreeN.bind' handler n (F s) Sim))
    hSim

/-! ## Parallel composition -/

/-- Stateful parallel composition at sdist level: coproduct of two stateful
    protocols. Distance is `max(ε₁, ε₂)`, reflecting the coproduct structure
    (only one branch runs per input). -/
theorem sdistITreeN_stateful_par {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon₁ S₁ β₁ hon₂ S₂ β₂ : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon₁ → StatefulITreeN S₁ n E β₁)
    (π₂ F₂ : hon₂ → StatefulITreeN S₂ n E β₂)
    (h₁ : sdistITreeN n E handler
      (fun (ps : hon₁ × S₁) => π₁ ps.1 ps.2)
      (fun (ps : hon₁ × S₁) => F₁ ps.1 ps.2) ≤ ε₁)
    (h₂ : sdistITreeN n E handler
      (fun (ps : hon₂ × S₂) => π₂ ps.1 ps.2)
      (fun (ps : hon₂ × S₂) => F₂ ps.1 ps.2) ≤ ε₂) :
    sdistITreeN n E handler
      (mapSumITreeN handler n
        (fun (ps : hon₁ × S₁) => π₁ ps.1 ps.2)
        (fun (ps : hon₂ × S₂) => π₂ ps.1 ps.2))
      (mapSumITreeN handler n
        (fun (ps : hon₁ × S₁) => F₁ ps.1 ps.2)
        (fun (ps : hon₂ × S₂) => F₂ ps.1 ps.2)) ≤ ε₁ ⊔ ε₂ :=
  sdist_mapSumITreeN_le handler n _ _ _ _ h₁ h₂

/-! ## Sequential composition -/

/-- Sequential bind: composing two ITreeN computations in sequence.
    The bound is additive via triangle + left/right PPLs.

    This is the workhorse for sequential composition of protocols:
    swapping the first stage costs ε₁ (by right PPL), swapping the
    second stage costs ε₂ (by left PPL). -/
theorem sdistITreeN_bind {α β γ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : α → ITreeN n E β) (π₂ F₂ : β → ITreeN n E γ)
    (h₁ : sdistITreeN n E handler π₁ F₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler π₂ F₂ ≤ ε₂) :
    sdistITreeN n E handler
      (fun a => ITreeN.bind' handler n (π₁ a) π₂)
      (fun a => ITreeN.bind' handler n (F₁ a) F₂) ≤ ε₁ + ε₂ :=
  calc sdistITreeN n E handler _ _
      ≤ sdistITreeN n E handler
          (fun a => ITreeN.bind' handler n (π₁ a) π₂)
          (fun a => ITreeN.bind' handler n (F₁ a) π₂)
        + sdistITreeN n E handler
          (fun a => ITreeN.bind' handler n (F₁ a) π₂)
          (fun a => ITreeN.bind' handler n (F₁ a) F₂) :=
        sdistITreeN_triangle n E handler _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add
        (le_trans (sdistITreeN_comp_right n E handler π₁ F₁ π₂) h₁)
        (le_trans (sdistITreeN_comp_left n E handler F₁ π₂ F₂) h₂)

/-- Stateful sequential composition: two stateful protocols with the same
    state S, composed via monadic bind. The sdist bound is additive.

    This is `sdistITreeN_bind` specialized to the uncurried representation
    of `StatefulITreeN`. -/
theorem sdistITreeN_stateful_seq {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S mid γ : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon → StatefulITreeN S n E mid)
    (π₂ F₂ : mid → StatefulITreeN S n E γ)
    (h₁ : sdistITreeN n E handler
      (fun (ps : hon × S) => π₁ ps.1 ps.2)
      (fun (ps : hon × S) => F₁ ps.1 ps.2) ≤ ε₁)
    (h₂ : sdistITreeN n E handler
      (fun (ps : mid × S) => π₂ ps.1 ps.2)
      (fun (ps : mid × S) => F₂ ps.1 ps.2) ≤ ε₂) :
    sdistITreeN n E handler
      (fun (ps : hon × S) =>
        ITreeN.bind' handler n (π₁ ps.1 ps.2) fun p => π₂ p.1 p.2)
      (fun (ps : hon × S) =>
        ITreeN.bind' handler n (F₁ ps.1 ps.2) fun p => F₂ p.1 p.2) ≤ ε₁ + ε₂ :=
  sdistITreeN_bind handler n
    (fun (ps : hon × S) => π₁ ps.1 ps.2)
    (fun (ps : hon × S) => F₁ ps.1 ps.2)
    (fun (ps : mid × S) => π₂ ps.1 ps.2)
    (fun (ps : mid × S) => F₂ ps.1 ps.2)
    h₁ h₂

/-- Stateful sequential composition at UC level: if two stateful protocols
    with the same state are each ε-close to their ideals, the composition
    UC-emulates the ideal composition with additive bound. -/
theorem UCEmulatesConcurrentStateful_seq {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S mid out leak : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon → StatefulITreeN S n E mid)
    (π₂ F₂ : mid → StatefulITreeN S n E (out ⊕ leak))
    (h₁ : sdistITreeN n E handler
      (fun (ps : hon × S) => π₁ ps.1 ps.2)
      (fun (ps : hon × S) => F₁ ps.1 ps.2) ≤ ε₁)
    (h₂ : sdistITreeN n E handler
      (fun (ps : mid × S) => π₂ ps.1 ps.2)
      (fun (ps : mid × S) => F₂ ps.1 ps.2) ≤ ε₂) :
    UCEmulatesConcurrentStateful handler n (ε₁ + ε₂)
      (fun a s => ITreeN.bind' handler n (π₁ a s) fun p => π₂ p.1 p.2)
      (fun a s => ITreeN.bind' handler n (F₁ a s) fun p => F₂ p.1 p.2) :=
  UCEmulatesConcurrentStateful_of_sdistITreeN handler n
    (sdistITreeN_stateful_seq handler n π₁ F₁ π₂ F₂ h₁ h₂)

/-! ## Kantorovich sequential composition -/

/-- Sequential bind with Kantorovich metric: composing two ITreeN computations.
    The bound is additive via triangle + left/right Kantorovich PPLs.

    This is the Kantorovich analogue of `sdistITreeN_bind`. -/
theorem kdistITreeN_bind {α β γ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : α → ITreeN n E β) (π₂ F₂ : β → ITreeN n E γ)
    (h₁ : kdistITreeN n E handler π₁ F₁ ≤ ε₁)
    (h₂ : kdistITreeN n E handler π₂ F₂ ≤ ε₂) :
    kdistITreeN n E handler
      (fun a => ITreeN.bind' handler n (π₁ a) π₂)
      (fun a => ITreeN.bind' handler n (F₁ a) F₂) ≤ ε₁ + ε₂ :=
  calc kdistITreeN n E handler _ _
      ≤ kdistITreeN n E handler
          (fun a => ITreeN.bind' handler n (π₁ a) π₂)
          (fun a => ITreeN.bind' handler n (F₁ a) π₂)
        + kdistITreeN n E handler
          (fun a => ITreeN.bind' handler n (F₁ a) π₂)
          (fun a => ITreeN.bind' handler n (F₁ a) F₂) :=
        kdistITreeN_triangle n E handler _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add
        (le_trans (kdistITreeN_comp_right n E handler π₁ F₁ π₂) h₁)
        (le_trans (kdistITreeN_comp_left n E handler F₁ π₂ F₂) h₂)

/-- Stateful sequential composition with Kantorovich metric: two stateful
    protocols with the same state S, composed via monadic bind.

    This is the Kantorovich analogue of `sdistITreeN_stateful_seq`. -/
theorem kdistITreeN_stateful_seq {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S mid γ : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon → StatefulITreeN S n E mid)
    (π₂ F₂ : mid → StatefulITreeN S n E γ)
    (h₁ : kdistITreeN n E handler
      (fun (ps : hon × S) => π₁ ps.1 ps.2)
      (fun (ps : hon × S) => F₁ ps.1 ps.2) ≤ ε₁)
    (h₂ : kdistITreeN n E handler
      (fun (ps : mid × S) => π₂ ps.1 ps.2)
      (fun (ps : mid × S) => F₂ ps.1 ps.2) ≤ ε₂) :
    kdistITreeN n E handler
      (fun (ps : hon × S) =>
        ITreeN.bind' handler n (π₁ ps.1 ps.2) fun p => π₂ p.1 p.2)
      (fun (ps : hon × S) =>
        ITreeN.bind' handler n (F₁ ps.1 ps.2) fun p => F₂ p.1 p.2) ≤ ε₁ + ε₂ :=
  kdistITreeN_bind handler n
    (fun (ps : hon × S) => π₁ ps.1 ps.2)
    (fun (ps : hon × S) => F₁ ps.1 ps.2)
    (fun (ps : mid × S) => π₂ ps.1 ps.2)
    (fun (ps : mid × S) => F₂ ps.1 ps.2)
    h₁ h₂

/-! ## Kantorovich-based stateful UC -/

/-- UC emulation with concurrent adversary interaction for stateful protocols,
    using the **Kantorovich bisimulation metric** `kdistITreeN` instead of `sdistITreeN`.

    The Kantorovich metric preserves round structure: it bounds the distance at
    each round individually, not just the flattened total. This gives a strictly
    stronger guarantee than `UCEmulatesConcurrentStateful`. -/
noncomputable def UCEmulatesConcurrentStatefulK {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (ε : ℝ≥0∞) {hon S out leak view : Type}
    (π : hon → StatefulITreeN S n E (out ⊕ leak))
    (F : hon → StatefulITreeN S n E (out ⊕ view)) :=
  ∀ A : ((out ⊕ leak) × S) → ITreeN n E Bool,
  ∃ Sim : ((out ⊕ view) × S) → ITreeN n E Bool,
    kdistITreeN n E handler
      (fun (ps : hon × S) => ITreeN.bind' handler n (π ps.1 ps.2) A)
      (fun (ps : hon × S) => ITreeN.bind' handler n (F ps.1 ps.2) Sim) ≤ ε

/-- `UCEmulatesConcurrentStatefulK` implies `UCEmulatesConcurrentStateful`:
    the Kantorovich-based notion is strictly stronger than the flattening-based one. -/
theorem UCEmulatesConcurrentStatefulK_implies_flat {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S out leak view : Type} {ε : ℝ≥0∞}
    {π : hon → StatefulITreeN S n E (out ⊕ leak)}
    {F : hon → StatefulITreeN S n E (out ⊕ view)}
    (h : UCEmulatesConcurrentStatefulK handler n ε π F) :
    UCEmulatesConcurrentStateful handler n ε π F := by
  intro A
  obtain ⟨Sim, hSim⟩ := h A
  exact ⟨Sim, le_trans (sdistITreeN_le_kdistITreeN n E handler _ _) hSim⟩

/-- Lift a `kdistITreeN` bound (same leak interface) to `UCEmulatesConcurrentStatefulK`.

    When `leak = view`, the simulator is the identity (`Sim = A`).
    The bound follows from `kdistITreeN_comp_right`. -/
theorem UCEmulatesConcurrentStatefulK_of_kdistITreeN {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S out leak : Type} {ε : ℝ≥0∞}
    {π F : hon → StatefulITreeN S n E (out ⊕ leak)}
    (h : kdistITreeN n E handler
      (fun (ps : hon × S) => π ps.1 ps.2)
      (fun (ps : hon × S) => F ps.1 ps.2) ≤ ε) :
    UCEmulatesConcurrentStatefulK handler n ε π F := by
  intro A
  exact ⟨A, le_trans (kdistITreeN_comp_right n E handler _ _ A) h⟩

/-- Reflexivity for Kantorovich stateful UC. -/
theorem UCEmulatesConcurrentStatefulK_refl {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S out leak : Type}
    (π : hon → StatefulITreeN S n E (out ⊕ leak)) :
    UCEmulatesConcurrentStatefulK handler n 0 π π := by
  intro A
  exact ⟨A, le_of_eq (kdistITreeN_self n E handler _)⟩

/-- Transitivity for Kantorovich stateful UC with additive distance. -/
theorem UCEmulatesConcurrentStatefulK_trans {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon S out leak₁ leak₂ view₂ : Type}
    {π : hon → StatefulITreeN S n E (out ⊕ leak₁)}
    {Q : hon → StatefulITreeN S n E (out ⊕ leak₂)}
    {F : hon → StatefulITreeN S n E (out ⊕ view₂)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : UCEmulatesConcurrentStatefulK handler n ε₁ π Q)
    (h₂ : UCEmulatesConcurrentStatefulK handler n ε₂ Q F) :
    UCEmulatesConcurrentStatefulK handler n (ε₁ + ε₂) π F := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (kdistITreeN_triangle n E handler _ _ _) (add_le_add hS₁ hS₂)⟩

/-! ## Dynamic Session Creation (Arbitrary Index Types) -/

/-- Generalized multi-session bound for arbitrary index types.

    If per-index sdist is bounded by ε, the overall sdist over `(ι × β)` is
    also bounded. Supports dynamically created sessions with unbounded index
    sets (not just `Fin k`). -/
theorem sdistITreeN_indexed {ι β γ : Type} {E : EventSig}
    {ε : ℝ≥0∞}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f g : ι → β → ITreeN n E γ)
    (h : ∀ i, sdistITreeN n E handler (f i) (g i) ≤ ε) :
    sdistITreeN n E handler
      (fun (p : ι × β) => f p.1 p.2)
      (fun (p : ι × β) => g p.1 p.2) ≤ ε := by
  apply iSup_le; intro D
  apply iSup_le; intro ⟨i, b⟩
  apply iSup_le; intro h₀
  refine le_trans ?_ (h i)
  show _ ≤ sdist _ _
  exact le_iSup₂_of_le D b (le_iSup_of_le h₀ le_rfl)

end UCMonad.StateTITreeNCompose
