/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.UCMonad.ITreeNMetric
public import CatCrypt.Crypto.UCMonad.ITreeNInterleave

/-!
# Kantorovich-Based Concurrent UC Composition

This file defines `UCEmulatesConcurrentK`, a concurrent UC emulation notion
that uses the Kantorovich bisimulation metric `kdistITreeN` instead of the
flattening metric `sdistITreeN`. The Kantorovich metric preserves round
structure and distinguishes different interleaving schedules, giving
Canetti-style concurrent UC where the adversary adaptively schedules sessions.

All 9 composition theorems from `ITreeNCompose`, `ITreeNMultiSession`, and
`ITreeNInterleave` are reproved using `kdistITreeN`, plus a backward
compatibility bridge showing that `UCEmulatesConcurrentK` implies the
original `UCEmulatesConcurrent`.

## Main results

* `UCEmulatesConcurrentK` — concurrent UC using Kantorovich metric
* `UCEmulatesConcurrentK_refl` — reflexivity
* `UCEmulatesConcurrentK_trans` — transitivity (additive)
* `UCEmulatesConcurrentK_adversary_comp` — adversary composition
* `UCEmulatesConcurrentK_of_kdist` — same-interface kdist implies K-UC
* `UCEmulatesConcurrentK_par_of_kdist` — parallel composition (max bound)
* `UCEmulatesConcurrentK_multisession` — k-fold multi-session
* `UCEmulatesConcurrentK_pair` — product composition (additive bound)
* `UCEmulatesConcurrentK_vec_copies` — k-ary copies
* `UCEmulatesConcurrentK_compile` — subroutine composition (additive)
* `UCEmulatesConcurrentK_implies_flat` — backward compatibility bridge

## Axiom status

**0 axioms**, **0 sorries**. All proofs complete.
-/

@[expose] public section

namespace UCMonad.ITreeNUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal
open UCMonad.RoundMUC

/-! ## Pointwise ≤ Kleisli -/

/-- Each pointwise distance is ≤ the sup (Kleisli distance). -/
theorem kdistITreeN_pt_le {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) (a : α) :
    (kdistITreeN_pt n E β).dist (f a) (g a) ≤ kdistITreeN n E handler f g :=
  le_iSup (fun a => (kdistITreeN_pt n E β).dist (f a) (g a)) a

/-! ## Phase B: Kantorovich Helper Lemmas -/

/-- Coproduct tensor bound for Kantorovich: distance is max, not sum,
    since only one branch runs per input. -/
theorem kdist_mapSumITreeN_le {α₁ α₂ β₁ β₂ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f₁ f₂ : α₁ → ITreeN n E β₁) (g₁ g₂ : α₂ → ITreeN n E β₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (hf : kdistITreeN n E handler f₁ f₂ ≤ ε₁)
    (hg : kdistITreeN n E handler g₁ g₂ ≤ ε₂) :
    kdistITreeN n E handler
      (mapSumITreeN handler n f₁ g₁) (mapSumITreeN handler n f₂ g₂) ≤ ε₁ ⊔ ε₂ := by
  apply iSup_le; intro x
  cases x with
  | inl a =>
    simp only [mapSumITreeN]
    calc (kdistITreeN_pt n E (β₁ ⊕ β₂)).dist
          (ITreeN.bind' handler n (f₁ a) (fun b => ITreeN.done n (Sum.inl b)))
          (ITreeN.bind' handler n (f₂ a) (fun b => ITreeN.done n (Sum.inl b)))
        ≤ (kdistITreeN_pt n E β₁).dist (f₁ a) (f₂ a) :=
          kdistITreeN_pt_comp_right n E handler (f₁ a) (f₂ a) _
      _ ≤ kdistITreeN n E handler f₁ f₂ := kdistITreeN_pt_le n E handler f₁ f₂ a
      _ ≤ ε₁ := hf
      _ ≤ ε₁ ⊔ ε₂ := le_sup_left
  | inr c =>
    simp only [mapSumITreeN]
    calc (kdistITreeN_pt n E (β₁ ⊕ β₂)).dist
          (ITreeN.bind' handler n (g₁ c) (fun d => ITreeN.done n (Sum.inr d)))
          (ITreeN.bind' handler n (g₂ c) (fun d => ITreeN.done n (Sum.inr d)))
        ≤ (kdistITreeN_pt n E β₂).dist (g₁ c) (g₂ c) :=
          kdistITreeN_pt_comp_right n E handler (g₁ c) (g₂ c) _
      _ ≤ kdistITreeN n E handler g₁ g₂ := kdistITreeN_pt_le n E handler g₁ g₂ c
      _ ≤ ε₂ := hg
      _ ≤ ε₁ ⊔ ε₂ := le_sup_right

/-- Kantorovich distance of constant functions from any type ≤ from Unit. -/
theorem kdistITreeN_const_le_unit {β : Type} {E : EventSig} {α : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (c c' : ITreeN n E β) :
    kdistITreeN n E handler (fun (_ : α) => c) (fun (_ : α) => c')
    ≤ kdistITreeN n E handler (fun () => c) (fun () => c') := by
  unfold kdistITreeN
  apply iSup_le; intro _
  exact le_iSup_of_le () le_rfl

/-! ## Phase C: Core Definition and Properties -/

/-- UC emulation with concurrent adversary interaction, using the **Kantorovich
    bisimulation metric** `kdistITreeN` instead of the flattening metric.

    The Kantorovich metric preserves round structure, distinguishing different
    interleaving schedules. This gives Canetti-style concurrent UC where
    the adversary adaptively schedules sessions. -/
noncomputable def UCEmulatesConcurrentK {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (ε : ℝ≥0∞) {hon out leak view : Type}
    (π : hon → ITreeN n E (out ⊕ leak))
    (F : hon → ITreeN n E (out ⊕ view)) :=
  ∀ A : (out ⊕ leak) → ITreeN n E Bool,
  ∃ S : (out ⊕ view) → ITreeN n E Bool,
    kdistITreeN n E handler
      (fun a => ITreeN.bind' handler n (π a) A)
      (fun a => ITreeN.bind' handler n (F a) S) ≤ ε

/-- Reflexivity: any protocol K-UC-emulates itself with distance 0. -/
theorem UCEmulatesConcurrentK_refl {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak : Type}
    (π : hon → ITreeN n E (out ⊕ leak)) :
    UCEmulatesConcurrentK handler n 0 π π := by
  intro A; exact ⟨A, le_of_eq (kdistITreeN_self n E handler _)⟩

/-- Transitivity: K-UC emulation composes with additive distance. -/
theorem UCEmulatesConcurrentK_trans {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak₁ leak₂ view₂ : Type}
    {π : hon → ITreeN n E (out ⊕ leak₁)}
    {Q : hon → ITreeN n E (out ⊕ leak₂)}
    {F : hon → ITreeN n E (out ⊕ view₂)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : UCEmulatesConcurrentK handler n ε₁ π Q)
    (h₂ : UCEmulatesConcurrentK handler n ε₂ Q F) :
    UCEmulatesConcurrentK handler n (ε₁ + ε₂) π F := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (kdistITreeN_triangle n E handler _ _ _) (add_le_add hS₁ hS₂)⟩

/-- Adversary composition: composing the adversary with a continuation
    preserves K-UC emulation. -/
theorem UCEmulatesConcurrentK_adversary_comp {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out₁ out₂ leak view : Type}
    {π : hon → ITreeN n E (out₁ ⊕ leak)}
    {F : hon → ITreeN n E (out₁ ⊕ view)}
    {ε : ℝ≥0∞}
    (h : UCEmulatesConcurrentK handler n ε π F)
    (k_π : (out₁ ⊕ leak) → ITreeN n E (out₂ ⊕ leak))
    (A : (out₂ ⊕ leak) → ITreeN n E Bool) :
    ∃ S₁ : (out₁ ⊕ view) → ITreeN n E Bool,
      kdistITreeN n E handler
        (fun a => ITreeN.bind' handler n (ITreeN.bind' handler n (π a) k_π) A)
        (fun a => ITreeN.bind' handler n (F a) S₁) ≤ ε := by
  have hassoc : ∀ a, ITreeN.bind' handler n (ITreeN.bind' handler n (π a) k_π) A =
      ITreeN.bind' handler n (π a) (fun x => ITreeN.bind' handler n (k_π x) A) :=
    fun a => itreeN_bind_assoc handler n (π a) k_π A
  simp only [hassoc]
  exact h (fun x => ITreeN.bind' handler n (k_π x) A)

/-! ## Phase D: UC from kdist + Parallel + Multisession -/

/-- Same-interface kdist bound implies K-UC emulation. -/
theorem UCEmulatesConcurrentK_of_kdist {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak : Type} {ε : ℝ≥0∞}
    (π F : hon → ITreeN n E (out ⊕ leak))
    (h : kdistITreeN n E handler π F ≤ ε) :
    UCEmulatesConcurrentK handler n ε π F := by
  intro A
  exact ⟨A, le_trans (kdistITreeN_comp_right n E handler π F A) h⟩

/-- Parallel composition of K-UC emulation from kdist bounds.
    The max bound (not sum!) reflects the coproduct structure. -/
theorem UCEmulatesConcurrentK_par_of_kdist {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon₁ hon₂ β₁ β₂ : Type} {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon₁ → ITreeN n E β₁) (π₂ F₂ : hon₂ → ITreeN n E β₂)
    (h₁ : kdistITreeN n E handler π₁ F₁ ≤ ε₁)
    (h₂ : kdistITreeN n E handler π₂ F₂ ≤ ε₂) :
    UCEmulatesConcurrentK handler n (ε₁ ⊔ ε₂)
      (mapSumITreeN handler n π₁ π₂) (mapSumITreeN handler n F₁ F₂) :=
  UCEmulatesConcurrentK_of_kdist handler n _ _
    (kdist_mapSumITreeN_le handler n π₁ F₁ π₂ F₂ h₁ h₂)

/-- k-fold multi-session: if π K-UC-emulates F for a single session,
    then k copies also K-UC-emulate with the same bound. -/
theorem UCEmulatesConcurrentK_multisession {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {out leak view : Type} {ε : ℝ≥0∞}
    (π : ITreeN n E (out ⊕ leak))
    (F : ITreeN n E (out ⊕ view))
    (h : UCEmulatesConcurrentK handler n ε (fun () => π) (fun () => F))
    (k : Nat) :
    UCEmulatesConcurrentK handler n ε
      (fun (_ : Fin k) => π) (fun (_ : Fin k) => F) := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans (kdistITreeN_const_le_unit handler n _ _) hS⟩

/-! ## Phase E: Pair/Vec Composition -/

/-- Pair bound for Kantorovich: distance of pairs is at most sum of distances.
    Triangle through midpoint `pairITreeN handler n g₁ f₂`, working pointwise. -/
theorem kdist_pairITreeN_le {α β₁ β₂ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f₁ g₁ : α → ITreeN n E β₁) (f₂ g₂ : α → ITreeN n E β₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : kdistITreeN n E handler f₁ g₁ ≤ ε₁)
    (h₂ : kdistITreeN n E handler f₂ g₂ ≤ ε₂) :
    kdistITreeN n E handler (pairITreeN handler n f₁ f₂)
      (pairITreeN handler n g₁ g₂) ≤ ε₁ + ε₂ := by
  -- Work pointwise: for each a, triangle through pairITreeN g₁ f₂ a
  apply iSup_le; intro a
  simp only [pairITreeN]
  calc (kdistITreeN_pt n E (β₁ × β₂)).dist
        (ITreeN.bind' handler n (f₁ a)
          (fun b => ITreeN.bind' handler n (f₂ a) (fun c => ITreeN.done n (b, c))))
        (ITreeN.bind' handler n (g₁ a)
          (fun b => ITreeN.bind' handler n (g₂ a) (fun c => ITreeN.done n (b, c))))
      ≤ (kdistITreeN_pt n E (β₁ × β₂)).dist
          (ITreeN.bind' handler n (f₁ a)
            (fun b => ITreeN.bind' handler n (f₂ a) (fun c => ITreeN.done n (b, c))))
          (ITreeN.bind' handler n (g₁ a)
            (fun b => ITreeN.bind' handler n (f₂ a) (fun c => ITreeN.done n (b, c))))
        + (kdistITreeN_pt n E (β₁ × β₂)).dist
          (ITreeN.bind' handler n (g₁ a)
            (fun b => ITreeN.bind' handler n (f₂ a) (fun c => ITreeN.done n (b, c))))
          (ITreeN.bind' handler n (g₁ a)
            (fun b => ITreeN.bind' handler n (g₂ a) (fun c => ITreeN.done n (b, c)))) :=
        (kdistITreeN_pt n E (β₁ × β₂)).dist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := by
        apply add_le_add
        · -- Leg 1: changing f₁ a → g₁ a (right PPL pointwise)
          exact le_trans (kdistITreeN_pt_comp_right n E handler (f₁ a) (g₁ a) _)
            (le_trans (kdistITreeN_pt_le n E handler f₁ g₁ a) h₁)
        · -- Leg 2: changing f₂ a → g₂ a (left PPL on g₁ a, right PPL on inner)
          calc (kdistITreeN_pt n E (β₁ × β₂)).dist
                (ITreeN.bind' handler n (g₁ a) _) (ITreeN.bind' handler n (g₁ a) _)
              ≤ ⨆ b, (kdistITreeN_pt n E (β₁ × β₂)).dist
                  (ITreeN.bind' handler n (f₂ a) (fun c => ITreeN.done n (b, c)))
                  (ITreeN.bind' handler n (g₂ a) (fun c => ITreeN.done n (b, c))) :=
                kdistITreeN_pt_comp_left n E handler (g₁ a) _ _
            _ ≤ ε₂ := by
                apply iSup_le; intro _
                exact le_trans (kdistITreeN_pt_comp_right n E handler (f₂ a) (g₂ a) _)
                  (le_trans (kdistITreeN_pt_le n E handler f₂ g₂ a) h₂)

/-- k-ary product bound for Kantorovich: distance is at most k * ε. -/
theorem kdist_vecITreeN_le {β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (k : Nat) (f g : Fin k → ITreeN n E β) (ε : ℝ≥0∞)
    (h : ∀ i, kdistITreeN n E handler (fun () => f i) (fun () => g i) ≤ ε) :
    kdistITreeN n E handler (fun () => vecITreeN handler n k f)
      (fun () => vecITreeN handler n k g) ≤ k * ε := by
  induction k with
  | zero => simp [vecITreeN, kdistITreeN_self]
  | succ k ih =>
    simp only [vecITreeN]
    rw [show (↑(k + 1) : ℝ≥0∞) * ε = ε + ↑k * ε from by push_cast; ring]
    exact kdist_pairITreeN_le handler n _ _ _ _ (h 0)
      (ih (f ∘ Fin.succ) (g ∘ Fin.succ) (fun i => h i.succ))

/-- K-UC pair composition: product composition with additive bound. -/
theorem UCEmulatesConcurrentK_pair {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon β₁ β₂ leak : Type} {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon → ITreeN n E β₁) (π₂ F₂ : hon → ITreeN n E β₂)
    (h₁ : kdistITreeN n E handler π₁ F₁ ≤ ε₁)
    (h₂ : kdistITreeN n E handler π₂ F₂ ≤ ε₂) :
    UCEmulatesConcurrentK handler n (ε₁ + ε₂)
      (fun a => ITreeN.bind' handler n (pairITreeN handler n π₁ π₂ a)
        (fun p => ITreeN.done n (Sum.inl p : (β₁ × β₂) ⊕ leak)))
      (fun a => ITreeN.bind' handler n (pairITreeN handler n F₁ F₂ a)
        (fun p => ITreeN.done n (Sum.inl p : (β₁ × β₂) ⊕ leak))) := by
  apply UCEmulatesConcurrentK_of_kdist
  calc kdistITreeN n E handler _ _
      ≤ kdistITreeN n E handler (pairITreeN handler n π₁ π₂)
          (pairITreeN handler n F₁ F₂) :=
        kdistITreeN_comp_right n E handler _ _ _
    _ ≤ ε₁ + ε₂ := kdist_pairITreeN_le handler n _ _ _ _ h₁ h₂

/-- K-UC k-ary composition: k copies of a K-UC-secure protocol. -/
theorem UCEmulatesConcurrentK_vec_copies {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {out leak : Type} {ε : ℝ≥0∞} (k : Nat)
    (π F : ITreeN n E (out ⊕ leak))
    (h : UCEmulatesConcurrentK handler n ε (fun () => π) (fun () => F)) :
    UCEmulatesConcurrentK handler n ε
      (fun (_ : Fin k) => π) (fun (_ : Fin k) => F) :=
  UCEmulatesConcurrentK_multisession handler n π F h k

/-! ## Phase F: Subroutine Compilation -/

/-- Compilation with same subroutine preserves kdist. -/
theorem kdist_compileITreeN_same {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε : ℝ≥0∞}
    (π F : α → ITreeN n E (β ⊕ γ))
    (ρ : γ → ITreeN n E δ)
    (hπ : kdistITreeN n E handler π F ≤ ε) :
    kdistITreeN n E handler
      (compileITreeN handler n π ρ) (compileITreeN handler n F ρ) ≤ ε :=
  le_trans (kdistITreeN_comp_right n E handler π F _) hπ

/-- Compilation preserves kdist bounds additively.
    Triangle through `compileITreeN π ρ_ideal`. -/
theorem kdist_compileITreeN {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε₁ ε₂ : ℝ≥0∞}
    (π F : α → ITreeN n E (β ⊕ γ))
    (ρ_real ρ_ideal : γ → ITreeN n E δ)
    (hπ : kdistITreeN n E handler π F ≤ ε₁)
    (hρ : kdistITreeN n E handler ρ_real ρ_ideal ≤ ε₂) :
    kdistITreeN n E handler
      (compileITreeN handler n π ρ_real)
      (compileITreeN handler n F ρ_ideal) ≤ ε₁ + ε₂ := by
  -- Triangle through compileITreeN π ρ_ideal
  calc kdistITreeN n E handler
        (compileITreeN handler n π ρ_real)
        (compileITreeN handler n F ρ_ideal)
      ≤ kdistITreeN n E handler
          (compileITreeN handler n π ρ_real)
          (compileITreeN handler n π ρ_ideal)
        + kdistITreeN n E handler
          (compileITreeN handler n π ρ_ideal)
          (compileITreeN handler n F ρ_ideal) :=
        kdistITreeN_triangle n E handler _ _ _
    _ ≤ ε₂ + ε₁ := by
        apply add_le_add
        · -- Subroutine swap: same π, different ρ
          show kdistITreeN n E handler
            (fun a => ITreeN.bind' handler n (π a) (mapSumITreeN handler n (ITreeN.done n) ρ_real))
            (fun a => ITreeN.bind' handler n (π a) (mapSumITreeN handler n (ITreeN.done n) ρ_ideal))
            ≤ ε₂
          calc kdistITreeN n E handler _ _
              ≤ kdistITreeN n E handler
                  (mapSumITreeN handler n (ITreeN.done n) ρ_real)
                  (mapSumITreeN handler n (ITreeN.done n) ρ_ideal) :=
                kdistITreeN_comp_left n E handler π _ _
            _ ≤ kdistITreeN n E handler (ITreeN.done n) (ITreeN.done n) ⊔
                kdistITreeN n E handler ρ_real ρ_ideal :=
                kdist_mapSumITreeN_le handler n _ _ _ _ le_rfl le_rfl
            _ = 0 ⊔ kdistITreeN n E handler ρ_real ρ_ideal := by
                rw [kdistITreeN_self]
            _ = kdistITreeN n E handler ρ_real ρ_ideal := by simp
            _ ≤ ε₂ := hρ
        · -- Protocol swap: different π, same ρ_ideal
          exact kdist_compileITreeN_same handler n π F ρ_ideal hπ
    _ = ε₁ + ε₂ := add_comm ε₂ ε₁

/-- K-UC subroutine composition: compilation preserves K-UC emulation
    with additive bounds. -/
theorem UCEmulatesConcurrentK_compile {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε₁ ε₂ : ℝ≥0∞}
    (π F : α → ITreeN n E (β ⊕ γ))
    (ρ_real ρ_ideal : γ → ITreeN n E δ)
    (hπ : kdistITreeN n E handler π F ≤ ε₁)
    (hρ : kdistITreeN n E handler ρ_real ρ_ideal ≤ ε₂) :
    UCEmulatesConcurrentK handler n (ε₁ + ε₂)
      (compileITreeN handler n π ρ_real)
      (compileITreeN handler n F ρ_ideal) :=
  UCEmulatesConcurrentK_of_kdist handler n _ _
    (kdist_compileITreeN handler n π F ρ_real ρ_ideal hπ hρ)

/-! ## Phase G: Backward Compatibility Bridge -/

/-- `UCEmulatesConcurrentK` implies `UCEmulatesConcurrent`:
    the Kantorovich-based notion is strictly stronger than the flattening-based one. -/
theorem UCEmulatesConcurrentK_implies_flat {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak view : Type} {ε : ℝ≥0∞}
    {π : hon → ITreeN n E (out ⊕ leak)}
    {F : hon → ITreeN n E (out ⊕ view)}
    (h : UCEmulatesConcurrentK handler n ε π F) :
    UCEmulatesConcurrent handler n ε π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans (sdistITreeN_le_kdistITreeN n E handler _ _) hS⟩

end UCMonad.ITreeNUC
