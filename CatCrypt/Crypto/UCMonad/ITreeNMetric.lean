/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.UCMonad.ITreeN
import CatCrypt.Crypto.UCMonad.RoundMKantorovich

/-!
# Kantorovich Bisimulation Metric on ITreeN

This file defines a **Kantorovich bisimulation metric** on `ITreeN n E`, extending
the `RoundMKantorovich` infrastructure to bounded interaction trees with visible events.

The key extension over `RoundM` is handling the Vis continuation component
`Σ e, E.Resp e → ITreeN n E α`: different events get distance `⊤`, same events
get the supremum over responses of the recursive metric.

## Main definitions

* `visContinuationMetric` — EPseudoMetric on `Σ e, E.Resp e → ITreeN n E β`
* `kdistITreeN_pt` — recursive Kantorovich metric on `ITreeN n E β`
* `kdistITreeN` — sup over inputs
* `UCMonadMetric_ITreeN_Kantorovich` — alternative UCMonadMetric instance

## Axiom status

**0 axioms**, **0 sorries**. Right PPL and Left PPL proved by induction on `n`,
following the structure of `RoundMKantorovich` with additional Vis branch case analysis.
-/

namespace UCMonad.ITreeNUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal
open UCMonad.RoundMUC
open Classical

/-! ## Vis Continuation Metric -/

/-- Metric on `Σ e, E.Resp e → X`: different events → ⊤,
    same event → sup over responses of the component metric. -/
private noncomputable def visDist {X : Type} (E : EventSig) (dX : EPseudoMetric X)
    (p q : Σ (e : E.Event), E.Resp e → X) : ℝ≥0∞ :=
  if h : p.1 = q.1 then
    ⨆ (r : E.Resp p.1), dX.dist (p.2 r) (q.2 (h ▸ r))
  else ⊤

private theorem visDist_self {X : Type} (E : EventSig) (dX : EPseudoMetric X)
    (p : Σ (e : E.Event), E.Resp e → X) : visDist E dX p p = 0 := by
  unfold visDist; rw [dif_pos rfl]
  apply le_antisymm _ (zero_le)
  exact iSup_le (fun r => le_of_eq (dX.dist_self _))

private theorem visDist_sym {X : Type} (E : EventSig) (dX : EPseudoMetric X)
    (p q : Σ (e : E.Event), E.Resp e → X) :
    visDist E dX p q = visDist E dX q p := by
  obtain ⟨ep, fp⟩ := p; obtain ⟨eq, fq⟩ := q
  simp only [visDist]
  by_cases h : ep = eq
  · subst h; simp only [dite_true]
    apply le_antisymm <;> (apply iSup_le; intro r)
    · rw [dX.dist_sym]; exact le_iSup_of_le r le_rfl
    · rw [dX.dist_sym]; exact le_iSup_of_le r le_rfl
  · rw [dif_neg h, dif_neg (Ne.symm h)]

private theorem visDist_triangle {X : Type} (E : EventSig) (dX : EPseudoMetric X)
    (p q s : Σ (e : E.Event), E.Resp e → X) :
    visDist E dX p s ≤ visDist E dX p q + visDist E dX q s := by
  obtain ⟨ep, fp⟩ := p; obtain ⟨eq, fq⟩ := q; obtain ⟨es, fs⟩ := s
  simp only [visDist]
  by_cases hps : ep = es
  · subst hps
    by_cases hpq : ep = eq
    · subst hpq; simp only [dite_true]
      apply iSup_le; intro r
      exact le_trans (dX.dist_triangle _ _ _)
        (add_le_add (le_iSup_of_le r le_rfl) (le_iSup_of_le r le_rfl))
    · rw [show (dite (ep = eq) _ (fun _ => (⊤ : ℝ≥0∞))) = ⊤ from dif_neg hpq]
      simp
  · rw [show (dite (ep = es) _ (fun _ => (⊤ : ℝ≥0∞))) = ⊤ from dif_neg hps]
    by_cases hpq : ep = eq
    · subst hpq
      rw [show (dite (ep = es) _ (fun _ => (⊤ : ℝ≥0∞))) = ⊤ from dif_neg hps, add_top]
    · rw [show (dite (ep = eq) _ (fun _ => (⊤ : ℝ≥0∞))) = ⊤ from dif_neg hpq, top_add]

noncomputable def visContinuationMetric {X : Type} (E : EventSig) (dX : EPseudoMetric X) :
    EPseudoMetric (Σ (e : E.Event), E.Resp e → X) where
  dist := visDist E dX
  dist_self := visDist_self E dX
  dist_sym := visDist_sym E dX
  dist_triangle := visDist_triangle E dX

/-! ## Recursive Kantorovich Metric on ITreeN -/

/-- Pointwise Kantorovich metric on `ITreeN n E β`. At each level, the step type
    `β ⊕ ITreeN n E β ⊕ (Σ e, E.Resp e → ITreeN n E β)` gets a nested sum metric
    using `discreteMetric β`, the recursive metric, and `visContinuationMetric`. -/
noncomputable def kdistITreeN_pt :
    (n : Nat) → (E : EventSig) → (β : Type) → EPseudoMetric (ITreeN n E β)
  | 0, _, β => kantLiftMetric (discreteMetric β)
  | n + 1, E, β =>
    kantLiftMetric (sumMetric (discreteMetric β)
      (sumMetric (kdistITreeN_pt n E β) (visContinuationMetric E (kdistITreeN_pt n E β))))

/-- Kantorovich distance between Kleisli morphisms: sup over inputs. -/
noncomputable def kdistITreeN {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) : ℝ≥0∞ :=
  ⨆ (a : α), (kdistITreeN_pt n E β).dist (f a) (g a)

/-! ## Pseudometric Properties -/

theorem kdistITreeN_self {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f : α → ITreeN n E β) : kdistITreeN n E handler f f = 0 := by
  simp [kdistITreeN, (kdistITreeN_pt n E β).dist_self]

theorem kdistITreeN_sym {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) :
    kdistITreeN n E handler f g = kdistITreeN n E handler g f := by
  simp only [kdistITreeN, (kdistITreeN_pt n E β).dist_sym]

theorem kdistITreeN_triangle {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g h : α → ITreeN n E β) :
    kdistITreeN n E handler f h ≤
    kdistITreeN n E handler f g + kdistITreeN n E handler g h := by
  apply iSup_le; intro a
  exact le_trans ((kdistITreeN_pt n E β).dist_triangle _ _ _)
    (add_le_add (le_iSup (fun a => (kdistITreeN_pt n E β).dist (f a) (g a)) a)
      (le_iSup (fun a => (kdistITreeN_pt n E β).dist (g a) (h a)) a))

/-! ## Per-Round Decomposition Lemmas -/

/-- Vis peeling with cast: at a vis node where both trees share the same event,
    the Kantorovich distance ≤ sup over responses of the continuation distances.

    This is the key decomposition tool for per-round analysis of ITreeN protocols. -/
theorem kdistITreeN_pt_vis_cast_le {β : Type} {E : EventSig}
    (n m : Nat) (h : m + 1 = n) (e : E.Event)
    (k₁ k₂ : E.Resp e → ITreeN m E β) (ε : ℝ≥0∞)
    (hk : ∀ r, (kdistITreeN_pt m E β).dist (k₁ r) (k₂ r) ≤ ε) :
    (kdistITreeN_pt n E β).dist (h ▸ ITreeN.vis m e k₁) (h ▸ ITreeN.vis m e k₂) ≤ ε := by
  subst h
  simp only [ITreeN.vis, kdistITreeN_pt]
  apply le_trans (kantLift_pure _ _ _)
  simp only [sumMetric_dist_inr_inr, visContinuationMetric, visDist, dite_true]
  exact iSup_le hk

/-! ## Pointwise Right PPL -/

/-- Abbreviation for the step metric at level n. -/
private noncomputable abbrev stepMetric (n : Nat) (E : EventSig) (β : Type) :=
  sumMetric (discreteMetric β)
    (sumMetric (kdistITreeN_pt n E β) (visContinuationMetric E (kdistITreeN_pt n E β)))

set_option maxHeartbeats 1600000 in
theorem kdistITreeN_pt_comp_right :
    ∀ (n : Nat) (E : EventSig) {β γ : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (μ ν : ITreeN n E β) (k : β → ITreeN n E γ),
    (kdistITreeN_pt n E γ).dist (ITreeN.bind' handler n μ k)
      (ITreeN.bind' handler n ν k) ≤
    (kdistITreeN_pt n E β).dist μ ν := by
  intro n; induction n with
  | zero =>
    intro E β γ handler μ ν k
    -- At level 0, ITreeN 0 E α = SPComp α, bind' = SPComp.bind
    show kantLift (discreteMetric γ) (SPComp.bind μ k) (SPComp.bind ν k) ≤
         kantLift (discreteMetric β) μ ν
    apply kantLift_comp_right _ _ μ ν k
    intro D' _hD'
    exact isLipDist_discrete _
  | succ m ih =>
    intro E β γ handler μ ν k
    -- At level m+1, bind'_succ gives SPComp.bind with 3-way case
    simp only [ITreeN.bind'_succ, kdistITreeN_pt]
    -- Source metric: stepMetric m E β
    -- Target metric: stepMetric m E γ
    apply kantLift_comp_right
      (sumMetric (discreteMetric β)
        (sumMetric (kdistITreeN_pt m E β)
          (visContinuationMetric E (kdistITreeN_pt m E β))))
      (sumMetric (discreteMetric γ)
        (sumMetric (kdistITreeN_pt m E γ)
          (visContinuationMetric E (kdistITreeN_pt m E γ)))) μ ν
    -- Need: ∀ D' Lip(d_γ), (fun b => bind (cont b) D') is Lip(d_β)
    intro D' hD' x y h₀
    -- Case split on the step types x, y
    cases x with
    | inl a₁ =>
      cases y with
      | inl a₂ =>
        -- Both done: discrete metric case
        simp only [sumMetric_dist_inl_inl, discreteMetric]
        by_cases h : a₁ = a₂
        · subst h; simp [absDiff_self]
        · simp only [if_neg h]; exact le_top
      | inr s₂ =>
        -- Cross case: distance = ⊤
        simp
      -- added for the second half of the inl case above
    | inr s₁ =>
      cases y with
      | inl _ =>
        -- Cross case: distance = ⊤
        simp
      | inr s₂ =>
        -- Both .inr: case split on inner sum
        cases s₁ with
        | inl c₁ =>
          cases s₂ with
          | inl c₂ =>
            -- Both silent continuations: use IH
            simp only [sumMetric_dist_inr_inr, sumMetric_dist_inl_inl, SPComp.pure_bind]
            -- D' applied to (.inr (.inl (bind' m c_i (flatten ∘ k))))
            -- Need: absDiff ≤ kdistITreeN_pt m E β . dist c₁ c₂
            exact le_trans
              (hD' (.inr (.inl (ITreeN.bind' handler m c₁
                    (fun a => ITreeN.flatten handler m (k a)))))
                   (.inr (.inl (ITreeN.bind' handler m c₂
                    (fun a => ITreeN.flatten handler m (k a))))) h₀)
              (by simp only [sumMetric_dist_inr_inr, sumMetric_dist_inl_inl]
                  exact ih E handler c₁ c₂ (fun a => ITreeN.flatten handler m (k a)))
          | inr _ =>
            -- Cross case: silent vs vis, distance = ⊤
            simp
        | inr vc₁ =>
          cases s₂ with
          | inl _ =>
            -- Cross case: vis vs silent, distance = ⊤
            simp
          | inr vc₂ =>
            -- Both Vis: ⟨e₁, kk₁⟩ and ⟨e₂, kk₂⟩
            obtain ⟨e₁, kk₁⟩ := vc₁
            obtain ⟨e₂, kk₂⟩ := vc₂
            simp only [sumMetric_dist_inr_inr, SPComp.pure_bind]
            -- The mapped Vis continuations
            -- Goal: absDiff(prTrue(D' (.inr (.inr ⟨e₁, mapped_kk₁⟩))) h₀,
            --               prTrue(D' (.inr (.inr ⟨e₂, mapped_kk₂⟩))) h₀)
            --      ≤ visDist E (kdistITreeN_pt m E β) ⟨e₁, kk₁⟩ ⟨e₂, kk₂⟩
            -- Use hD' on the mapped vis continuations, then bound by original vis distance
            apply le_trans
              (hD' (.inr (.inr ⟨e₁, fun r => ITreeN.bind' handler m (kk₁ r)
                      (fun a => ITreeN.flatten handler m (k a))⟩))
                   (.inr (.inr ⟨e₂, fun r => ITreeN.bind' handler m (kk₂ r)
                      (fun a => ITreeN.flatten handler m (k a))⟩)) h₀)
            -- Now need: visDist E (kdistITreeN_pt m E γ) mapped₁ mapped₂
            --         ≤ visDist E (kdistITreeN_pt m E β) ⟨e₁,kk₁⟩ ⟨e₂,kk₂⟩
            simp only [sumMetric_dist_inr_inr, visContinuationMetric]
            show visDist E (kdistITreeN_pt m E γ)
                ⟨e₁, fun r => ITreeN.bind' handler m (kk₁ r)
                    (fun a => ITreeN.flatten handler m (k a))⟩
                ⟨e₂, fun r => ITreeN.bind' handler m (kk₂ r)
                    (fun a => ITreeN.flatten handler m (k a))⟩ ≤
              visDist E (kdistITreeN_pt m E β) ⟨e₁, kk₁⟩ ⟨e₂, kk₂⟩
            unfold visDist; dsimp only
            by_cases he : e₁ = e₂
            · subst he; simp only [dite_true]
              apply iSup_le; intro r
              exact le_trans
                (ih E handler (kk₁ r) (kk₂ r)
                  (fun a => ITreeN.flatten handler m (k a)))
                (le_iSup_of_le r le_rfl)
            · simp only [dif_neg he]; exact le_top

/-! ## Flatten Non-Expansiveness for ITreeN -/

set_option maxHeartbeats 1600000 in
/-- `ITreeN.flatten` is non-expansive from `kdistITreeN_pt (m+1)` to `kdistITreeN_pt m`. -/
theorem flatten_nonexpansive_ITreeN
    {E : EventSig} {β : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (m : Nat)
    (μ ν : ITreeN (m + 1) E β) :
    (kdistITreeN_pt m E β).dist (ITreeN.flatten handler m μ) (ITreeN.flatten handler m ν) ≤
    (kdistITreeN_pt (m + 1) E β).dist μ ν := by
  cases m with
  | zero =>
    -- flatten 0 μ = SPComp.bind μ (3-way match)
    -- kdistITreeN_pt 0 = kantLiftMetric (discreteMetric β)
    -- kdistITreeN_pt 1 = kantLiftMetric (stepMetric 0 E β)
    show kantLift (discreteMetric β) (ITreeN.flatten handler 0 μ) (ITreeN.flatten handler 0 ν) ≤
         kantLift (stepMetric 0 E β) μ ν
    simp only [ITreeN.flatten_zero]
    apply kantLift_comp_right (stepMetric 0 E β) (discreteMetric β) μ ν
    intro D' hD' x y h₀
    cases x with
    | inl a₁ =>
      cases y with
      | inl a₂ => simp [SPComp.pure_bind]; exact hD' a₁ a₂ h₀
      | inr _ => simp
    | inr s₁ =>
      cases y with
      | inl _ => simp
      | inr s₂ =>
        cases s₁ with
        | inl k₁ =>
          cases s₂ with
          | inl k₂ =>
            -- Silent: k₁, k₂ are SPComp β (= ITreeN 0 E β)
            simp only [sumMetric_dist_inr_inr, sumMetric_dist_inl_inl,
              kdistITreeN_pt, kantLiftMetric]
            exact le_iSup₂_of_le D' hD' (le_iSup_of_le h₀ le_rfl)
          | inr _ => simp
        | inr vc₁ =>
          cases s₂ with
          | inl _ => simp
          | inr vc₂ =>
            -- Vis case: flatten maps ⟨e, k⟩ to bind (handler e) k
            obtain ⟨e₁, kk₁⟩ := vc₁
            obtain ⟨e₂, kk₂⟩ := vc₂
            simp only [sumMetric_dist_inr_inr, visContinuationMetric, visDist]
            by_cases he : e₁ = e₂
            · subst he; simp only [dite_true]
              -- Goal: absDiff(prTrue(bind (bind (handler e₁) kk₁) D') h₀,
              --               prTrue(bind (bind (handler e₁) kk₂) D') h₀)
              --      ≤ ⨆ r, kdist_pt 0 (kk₁ r) (kk₂ r)
              -- Reassociate bind
              rw [SPComp.bind_assoc, SPComp.bind_assoc]
              set ε := ⨆ r, (kdistITreeN_pt 0 E β).dist (kk₁ r) (kk₂ r)
              apply absDiff_prTrue_bind_le (handler e₁) _ _ h₀ ε
              · intro r h'
                apply le_add_of_absDiff_le
                apply le_trans _ (le_iSup (fun r => (kdistITreeN_pt 0 E β).dist (kk₁ r) (kk₂ r)) r)
                -- kdistITreeN_pt 0 = kantLiftMetric (discreteMetric β) = kantLift
                -- Need: absDiff(prTrue(bind (kk₁ r) D') h', prTrue(bind (kk₂ r) D') h') ≤ kantLift _ (kk₁ r) (kk₂ r)
                exact le_iSup₂_of_le D' hD' (le_iSup_of_le h' le_rfl)
              · intro r h'
                apply le_add_of_absDiff_le; rw [absDiff_comm]
                apply le_trans _ (le_iSup (fun r => (kdistITreeN_pt 0 E β).dist (kk₁ r) (kk₂ r)) r)
                exact le_iSup₂_of_le D' hD' (le_iSup_of_le h' le_rfl)
            · simp only [dif_neg he]; exact le_top
  | succ m' =>
    -- flatten (m'+1) μ = SPComp.bind μ (3-way match preserving .inl, identity on .inr)
    show kantLift (stepMetric m' E β) (ITreeN.flatten handler (m' + 1) μ)
           (ITreeN.flatten handler (m' + 1) ν) ≤
         kantLift (stepMetric (m' + 1) E β) μ ν
    simp only [ITreeN.flatten_succ]
    apply kantLift_comp_right (stepMetric (m' + 1) E β) (stepMetric m' E β) μ ν
    intro D' hD' x y h₀
    cases x with
    | inl a₁ =>
      cases y with
      | inl a₂ =>
        simp only [sumMetric_dist_inl_inl, SPComp.pure_bind]
        exact le_trans (hD' (.inl a₁) (.inl a₂) h₀) (by simp)
      | inr _ => simp
    | inr s₁ =>
      cases y with
      | inl _ => simp
      | inr s₂ =>
        cases s₁ with
        | inl k₁ =>
          cases s₂ with
          | inl k₂ =>
            -- Silent: identity map, use kantLift direct
            simp only [sumMetric_dist_inr_inr, sumMetric_dist_inl_inl,
              kdistITreeN_pt, kantLiftMetric]
            exact le_iSup₂_of_le D' hD' (le_iSup_of_le h₀ le_rfl)
          | inr _ => simp
        | inr vc₁ =>
          cases s₂ with
          | inl _ => simp
          | inr vc₂ =>
            obtain ⟨e₁, kk₁⟩ := vc₁
            obtain ⟨e₂, kk₂⟩ := vc₂
            -- Vis: flatten maps ⟨e, k⟩ to bind (handler e) k
            -- Source dist: visDist with kdistITreeN_pt (m'+1)
            -- Target dist: via D'
            simp only [sumMetric_dist_inr_inr, visContinuationMetric]
            -- The flatten on the vis case: SPComp.bind (handler e) kk
            show absDiff
                (prTrue (SPComp.bind (SPComp.bind (handler e₁) kk₁) D') h₀)
                (prTrue (SPComp.bind (SPComp.bind (handler e₂) kk₂) D') h₀) ≤
              visDist E (kdistITreeN_pt (m' + 1) E β) ⟨e₁, kk₁⟩ ⟨e₂, kk₂⟩
            unfold visDist; dsimp only
            by_cases he : e₁ = e₂
            · subst he; simp only [dite_true]
              rw [SPComp.bind_assoc, SPComp.bind_assoc]
              set ε := ⨆ r, (kdistITreeN_pt (m' + 1) E β).dist (kk₁ r) (kk₂ r)
              apply absDiff_prTrue_bind_le (handler e₁) _ _ h₀ ε
              · intro r h'
                apply le_add_of_absDiff_le
                apply le_trans _ (le_iSup (fun r =>
                  (kdistITreeN_pt (m' + 1) E β).dist (kk₁ r) (kk₂ r)) r)
                -- kdistITreeN_pt (m'+1) = kantLiftMetric (stepMetric m')
                -- = kantLift (stepMetric m')
                show absDiff (prTrue (SPComp.bind (kk₁ r) D') h')
                    (prTrue (SPComp.bind (kk₂ r) D') h') ≤ _
                exact le_iSup₂_of_le D' hD' (le_iSup_of_le h' le_rfl)
              · intro r h'
                apply le_add_of_absDiff_le; rw [absDiff_comm]
                apply le_trans _ (le_iSup (fun r =>
                  (kdistITreeN_pt (m' + 1) E β).dist (kk₁ r) (kk₂ r)) r)
                show absDiff (prTrue (SPComp.bind (kk₁ r) D') h')
                    (prTrue (SPComp.bind (kk₂ r) D') h') ≤ _
                exact le_iSup₂_of_le D' hD' (le_iSup_of_le h' le_rfl)
            · rw [dif_neg he]; exact le_top

/-! ## Pointwise Left PPL -/

set_option maxHeartbeats 1600000 in
theorem kdistITreeN_pt_comp_left :
    ∀ (n : Nat) (E : EventSig) {β γ : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (c : ITreeN n E β) (g₁ g₂ : β → ITreeN n E γ),
    (kdistITreeN_pt n E γ).dist (ITreeN.bind' handler n c g₁)
      (ITreeN.bind' handler n c g₂) ≤
    ⨆ (b : β), (kdistITreeN_pt n E γ).dist (g₁ b) (g₂ b) := by
  intro n; induction n with
  | zero =>
    intro E β γ handler c g₁ g₂
    exact kantLift_comp_left (discreteMetric γ) c g₁ g₂
  | succ m ih =>
    intro E β γ handler c g₁ g₂
    simp only [ITreeN.bind'_succ, kdistITreeN_pt]
    set d_γ := sumMetric (discreteMetric γ)
      (sumMetric (kdistITreeN_pt m E γ) (visContinuationMetric E (kdistITreeN_pt m E γ)))
    -- Step 1: kantLift_comp_left gives ≤ ⨆ x, kantLift d_γ (cont₁ x) (cont₂ x)
    apply le_trans (kantLift_comp_left d_γ c _ _)
    -- Step 2: bound ⨆ over step type by ⨆ over β
    apply iSup_le; intro x
    cases x with
    | inl b =>
      -- x = .inl b: cont maps to g₁ b / g₂ b directly
      exact le_iSup (fun b => kantLift d_γ (g₁ b) (g₂ b)) b
    | inr s =>
      cases s with
      | inl cont =>
        -- x = .inr (.inl cont): silent continuation
        -- cont₁ = pure (.inr (.inl (bind' m cont (flatten ∘ g₁))))
        -- cont₂ = pure (.inr (.inl (bind' m cont (flatten ∘ g₂))))
        calc kantLift d_γ
              (SPComp.pure (.inr (.inl (ITreeN.bind' handler m cont
                (fun a => ITreeN.flatten handler m (g₁ a))))))
              (SPComp.pure (.inr (.inl (ITreeN.bind' handler m cont
                (fun a => ITreeN.flatten handler m (g₂ a))))))
            ≤ d_γ.dist
              (.inr (.inl (ITreeN.bind' handler m cont
                (fun a => ITreeN.flatten handler m (g₁ a)))))
              (.inr (.inl (ITreeN.bind' handler m cont
                (fun a => ITreeN.flatten handler m (g₂ a))))) :=
              kantLift_pure d_γ _ _
          _ = (kdistITreeN_pt m E γ).dist
              (ITreeN.bind' handler m cont (fun a => ITreeN.flatten handler m (g₁ a)))
              (ITreeN.bind' handler m cont (fun a => ITreeN.flatten handler m (g₂ a))) := by
              simp only [d_γ, sumMetric_dist_inr_inr, sumMetric_dist_inl_inl]
          _ ≤ ⨆ (b : β), (kdistITreeN_pt m E γ).dist
              (ITreeN.flatten handler m (g₁ b)) (ITreeN.flatten handler m (g₂ b)) :=
              ih E handler cont _ _
          _ ≤ ⨆ (b : β), kantLift d_γ (g₁ b) (g₂ b) := by
              apply iSup_le; intro b
              exact le_trans (flatten_nonexpansive_ITreeN handler m (g₁ b) (g₂ b))
                (le_iSup (fun b => kantLift d_γ (g₁ b) (g₂ b)) b)
      | inr vc =>
        -- x = .inr (.inr ⟨e, kk⟩): vis continuation
        obtain ⟨e, kk⟩ := vc
        -- cont₁ = pure (.inr (.inr ⟨e, fun r => bind' m (kk r) (flatten ∘ g₁)⟩))
        -- cont₂ = pure (.inr (.inr ⟨e, fun r => bind' m (kk r) (flatten ∘ g₂)⟩))
        calc kantLift d_γ
              (SPComp.pure (.inr (.inr ⟨e, fun r => ITreeN.bind' handler m (kk r)
                (fun a => ITreeN.flatten handler m (g₁ a))⟩)))
              (SPComp.pure (.inr (.inr ⟨e, fun r => ITreeN.bind' handler m (kk r)
                (fun a => ITreeN.flatten handler m (g₂ a))⟩)))
            ≤ d_γ.dist
              (.inr (.inr ⟨e, fun r => ITreeN.bind' handler m (kk r)
                (fun a => ITreeN.flatten handler m (g₁ a))⟩))
              (.inr (.inr ⟨e, fun r => ITreeN.bind' handler m (kk r)
                (fun a => ITreeN.flatten handler m (g₂ a))⟩)) :=
              kantLift_pure d_γ _ _
          _ = (visContinuationMetric E (kdistITreeN_pt m E γ)).dist
              ⟨e, fun r => ITreeN.bind' handler m (kk r)
                (fun a => ITreeN.flatten handler m (g₁ a))⟩
              ⟨e, fun r => ITreeN.bind' handler m (kk r)
                (fun a => ITreeN.flatten handler m (g₂ a))⟩ := by
              simp only [d_γ, sumMetric_dist_inr_inr]
          _ = ⨆ (r : E.Resp e), (kdistITreeN_pt m E γ).dist
              (ITreeN.bind' handler m (kk r) (fun a => ITreeN.flatten handler m (g₁ a)))
              (ITreeN.bind' handler m (kk r) (fun a => ITreeN.flatten handler m (g₂ a))) := by
              simp only [visContinuationMetric, visDist, dite_true]
          _ ≤ ⨆ (_r : E.Resp e), ⨆ (b : β), (kdistITreeN_pt m E γ).dist
              (ITreeN.flatten handler m (g₁ b)) (ITreeN.flatten handler m (g₂ b)) := by
              apply iSup_le; intro r
              exact le_iSup_of_le r (ih E handler (kk r) _ _)
          _ ≤ ⨆ (b : β), (kdistITreeN_pt m E γ).dist
              (ITreeN.flatten handler m (g₁ b)) (ITreeN.flatten handler m (g₂ b)) := by
              apply iSup_le; intro _; exact le_rfl
          _ ≤ ⨆ (b : β), kantLift d_γ (g₁ b) (g₂ b) := by
              apply iSup_le; intro b
              exact le_trans (flatten_nonexpansive_ITreeN handler m (g₁ b) (g₂ b))
                (le_iSup (fun b => kantLift d_γ (g₁ b) (g₂ b)) b)

/-! ## Right and Left PPL -/

/-- Right PPL: post-composition with the same continuation doesn't increase distance. -/
theorem kdistITreeN_comp_right {α β γ : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) (k : β → ITreeN n E γ) :
    kdistITreeN n E handler (fun a => ITreeN.bind' handler n (f a) k)
      (fun a => ITreeN.bind' handler n (g a) k) ≤ kdistITreeN n E handler f g := by
  apply iSup_le; intro a
  exact le_trans (kdistITreeN_pt_comp_right n E handler (f a) (g a) k)
    (le_iSup (fun a => (kdistITreeN_pt n E β).dist (f a) (g a)) a)

/-- Left PPL: pre-composition with the same computation doesn't increase distance. -/
theorem kdistITreeN_comp_left {α β γ : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f : α → ITreeN n E β) (g₁ g₂ : β → ITreeN n E γ) :
    kdistITreeN n E handler (fun a => ITreeN.bind' handler n (f a) g₁)
      (fun a => ITreeN.bind' handler n (f a) g₂) ≤ kdistITreeN n E handler g₁ g₂ := by
  apply iSup_le; intro a
  exact le_trans (kdistITreeN_pt_comp_left n E handler (f a) g₁ g₂) le_rfl

/-! ## UCMonadMetric Instance -/

noncomputable def UCMonadMetric_ITreeN_Kantorovich (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    UCMonadMetric (ITreeN n E) := by
  letI : Monad (ITreeN n E) := instMonadITreeN n E handler
  letI : LawfulMonad (ITreeN n E) := instLawfulMonadITreeN n E handler
  exact {
    ucMapSum := mapSumITreeN handler n
    ucMapSum_inl := fun _f _g _a => rfl
    ucMapSum_inr := fun _f _g _c => rfl
    ucMapSum_pure_pure := mapSumITreeN_pure_pure handler n
    ucMapSum_pure_kleisli := fun f g => mapSumITreeN_pure_kleisli handler n f g
    ucSdist := kdistITreeN n E handler
    ucSdist_self := kdistITreeN_self n E handler
    ucSdist_sym := kdistITreeN_sym n E handler
    ucSdist_triangle := kdistITreeN_triangle n E handler
    ucSdist_comp_right := kdistITreeN_comp_right n E handler
    ucSdist_comp_left := kdistITreeN_comp_left n E handler
  }

/-! ## Comparison: Flattening ≤ Kantorovich -/

/-- Pointwise: flattening distance ≤ Kantorovich distance.
    `flattenAll` composes `n` flatten steps; each is non-expansive
    w.r.t. the Kantorovich metric, so the composed distance is ≤. -/
private theorem sdist_flattenAll_le_kdistITreeN_pt :
    ∀ (n : Nat) (E : EventSig) {β : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (μ ν : ITreeN n E β),
    kantLift (discreteMetric β) (ITreeN.flattenAll handler n μ)
      (ITreeN.flattenAll handler n ν) ≤ (kdistITreeN_pt n E β).dist μ ν := by
  intro n; induction n with
  | zero => intro _ _ _ _ _; exact le_rfl
  | succ m ih =>
    intro E β handler μ ν
    simp only [ITreeN.flattenAll_succ]
    exact le_trans (ih E handler (ITreeN.flatten handler m μ)
      (ITreeN.flatten handler m ν)) (flatten_nonexpansive_ITreeN handler m μ ν)

/-- Kleisli: `sdistITreeN ≤ kdistITreeN`.
    The flattening-based metric is bounded by the Kantorovich metric. -/
theorem sdistITreeN_le_kdistITreeN {α β : Type} (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → ITreeN n E β) :
    sdistITreeN n E handler f g ≤ kdistITreeN n E handler f g := by
  unfold sdistITreeN sdist
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro h₀
  apply le_trans _ (le_iSup (fun a => (kdistITreeN_pt n E β).dist (f a) (g a)) a)
  apply le_trans _ (sdist_flattenAll_le_kdistITreeN_pt n E handler (f a) (g a))
  exact le_iSup₂_of_le D (isLipDist_discrete D) (le_iSup_of_le h₀ le_rfl)

end UCMonad.ITreeNUC
