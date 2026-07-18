/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.UCMonad.RoundM

/-!
# Kantorovich Bisimulation Metric on RoundM

This file defines a **Kantorovich bisimulation metric** on `RoundM n`, providing
a strictly finer distance than the flattening-based `sdistRoundM`. While `sdistRoundM`
collapses all rounds via `flattenAll` and then measures `sdist`, the Kantorovich metric
preserves round structure by using Lipschitz dispatchers at each continuation point.

## References

* Balle, Gaboardi, Geumlek (2024): Kantorovich liftings for probabilistic programs
* Desharnais, Gupta, Jagadeesan, Panangaden (2004): Bisimulation metrics
-/

namespace UCMonad.RoundMUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal
open Classical

/-! ## Phase 1: Extended Pseudometric Foundations -/

/-- A lightweight bundled extended pseudometric. -/
structure EPseudoMetric (α : Type) where
  dist : α → α → ℝ≥0∞
  dist_self : ∀ x, dist x x = 0
  dist_sym : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

/-- The discrete metric: 0 for equal, ⊤ for distinct. -/
noncomputable def discreteMetric (α : Type) : EPseudoMetric α where
  dist x y := if x = y then 0 else ⊤
  dist_self x := if_pos rfl
  dist_sym x y := by
    by_cases h : x = y
    · subst h; rfl
    · have h' : y ≠ x := fun h' => h h'.symm
      simp only [if_neg h, if_neg h']
  dist_triangle x y z := by
    by_cases hxz : x = z
    · subst hxz; simp
    · simp only [if_neg hxz]
      by_cases hxy : x = y
      · simp only [if_pos hxy, zero_add]; exact if_neg (hxz ∘ (hxy ▸ ·)) ▸ le_rfl
      · simp only [if_neg hxy]; exact le_top

/-! ### Sum distance with explicit reduction lemmas -/

/-- Distance function for the sum metric. Defined separately for better reduction. -/
private noncomputable def sumDist {α β : Type}
    (d₁ : EPseudoMetric α) (d₂ : EPseudoMetric β) :
    (α ⊕ β) → (α ⊕ β) → ℝ≥0∞
  | .inl a₁, .inl a₂ => d₁.dist a₁ a₂
  | .inr b₁, .inr b₂ => d₂.dist b₁ b₂
  | .inl _, .inr _ => ⊤
  | .inr _, .inl _ => ⊤

@[simp] private theorem sumDist_inl_inl {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {a₁ a₂ : α} :
    sumDist d₁ d₂ (.inl a₁) (.inl a₂) = d₁.dist a₁ a₂ := rfl

@[simp] private theorem sumDist_inr_inr {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {b₁ b₂ : β} :
    sumDist d₁ d₂ (.inr b₁) (.inr b₂) = d₂.dist b₁ b₂ := rfl

@[simp] private theorem sumDist_inl_inr {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {a : α} {b : β} :
    sumDist d₁ d₂ (.inl a) (.inr b) = ⊤ := rfl

@[simp] private theorem sumDist_inr_inl {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {b : β} {a : α} :
    sumDist d₁ d₂ (.inr b) (.inl a) = ⊤ := rfl

/-- Sum metric on `α ⊕ β`: same-side delegates, cross = ⊤. -/
noncomputable def sumMetric {α β : Type} (d₁ : EPseudoMetric α) (d₂ : EPseudoMetric β) :
    EPseudoMetric (α ⊕ β) where
  dist := sumDist d₁ d₂
  dist_self x := by cases x with | inl a => exact d₁.dist_self a | inr b => exact d₂.dist_self b
  dist_sym x y := by
    cases x with
    | inl a => cases y with | inl a' => exact d₁.dist_sym a a' | inr _ => rfl
    | inr b => cases y with | inl _ => rfl | inr b' => exact d₂.dist_sym b b'
  dist_triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp
    · exact d₁.dist_triangle _ _ _
    · exact d₂.dist_triangle _ _ _

@[simp] theorem sumMetric_dist_inl_inl {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {a₁ a₂ : α} :
    (sumMetric d₁ d₂).dist (.inl a₁) (.inl a₂) = d₁.dist a₁ a₂ := rfl

@[simp] theorem sumMetric_dist_inr_inr {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {b₁ b₂ : β} :
    (sumMetric d₁ d₂).dist (.inr b₁) (.inr b₂) = d₂.dist b₁ b₂ := rfl

@[simp] theorem sumMetric_dist_inl_inr {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {a : α} {b : β} :
    (sumMetric d₁ d₂).dist (.inl a) (.inr b) = ⊤ := rfl

@[simp] theorem sumMetric_dist_inr_inl {α β : Type}
    {d₁ : EPseudoMetric α} {d₂ : EPseudoMetric β} {b : β} {a : α} :
    (sumMetric d₁ d₂).dist (.inr b) (.inl a) = ⊤ := rfl

/-! ## Phase 2: Kantorovich Lifting -/

/-- A distinguisher `D : β → SPComp Bool` is Lipschitz with respect to `d`. -/
def IsLipDist {β : Type} (d : EPseudoMetric β) (D : β → SPComp Bool) : Prop :=
  ∀ a b h₀, absDiff (prTrue (D a) h₀) (prTrue (D b) h₀) ≤ d.dist a b

/-- Kantorovich lifting via Lipschitz distinguisher supremum. -/
noncomputable def kantLift {β : Type} (d : EPseudoMetric β) (μ ν : SPComp β) : ℝ≥0∞ :=
  ⨆ (D : β → SPComp Bool) (_ : IsLipDist d D) (h₀ : Heap),
    absDiff (prTrue (SPComp.bind μ D) h₀) (prTrue (SPComp.bind ν D) h₀)

theorem kantLift_self {β : Type} (d : EPseudoMetric β) (μ : SPComp β) :
    kantLift d μ μ = 0 := by
  simp [kantLift, absDiff_self]

theorem kantLift_sym {β : Type} (d : EPseudoMetric β) (μ ν : SPComp β) :
    kantLift d μ ν = kantLift d ν μ := by
  simp only [kantLift]; congr 1; funext D; congr 1; funext _; congr 1; funext h₀
  exact absDiff_comm _ _

theorem kantLift_triangle {β : Type} (d : EPseudoMetric β) (μ ν ρ : SPComp β) :
    kantLift d μ ρ ≤ kantLift d μ ν + kantLift d ν ρ := by
  apply iSup_le; intro D; apply iSup_le; intro hD; apply iSup_le; intro h₀
  calc absDiff (prTrue (SPComp.bind μ D) h₀) (prTrue (SPComp.bind ρ D) h₀)
      ≤ absDiff (prTrue (SPComp.bind μ D) h₀) (prTrue (SPComp.bind ν D) h₀) +
        absDiff (prTrue (SPComp.bind ν D) h₀) (prTrue (SPComp.bind ρ D) h₀) :=
        absDiff_triangle _ _ _
    _ ≤ kantLift d μ ν + kantLift d ν ρ :=
        add_le_add (le_iSup₂_of_le D hD (le_iSup_of_le h₀ le_rfl))
          (le_iSup₂_of_le D hD (le_iSup_of_le h₀ le_rfl))

noncomputable def kantLiftMetric {β : Type} (d : EPseudoMetric β) :
    EPseudoMetric (SPComp β) where
  dist := kantLift d
  dist_self := kantLift_self d
  dist_sym := kantLift_sym d
  dist_triangle := kantLift_triangle d

/-! ### Discrete Kantorovich = unconstrained supremum -/

theorem isLipDist_discrete {β : Type} (D : β → SPComp Bool) :
    IsLipDist (discreteMetric β) D := by
  intro a b h₀; unfold discreteMetric; simp only
  by_cases h : a = b
  · subst h; simp [absDiff_self]
  · simp only [if_neg h]; exact le_top

theorem kantLift_discrete_eq {β : Type} (μ ν : SPComp β) :
    kantLift (discreteMetric β) μ ν =
    ⨆ (D : β → SPComp Bool) (h₀ : Heap),
      absDiff (prTrue (SPComp.bind μ D) h₀) (prTrue (SPComp.bind ν D) h₀) := by
  apply le_antisymm
  · apply iSup_le; intro D; apply iSup_le; intro _; apply iSup_le; intro h₀
    exact le_iSup₂_of_le D h₀ le_rfl
  · apply iSup_le; intro D; apply iSup_le; intro h₀
    exact le_iSup₂_of_le D (isLipDist_discrete D) (le_iSup_of_le h₀ le_rfl)

/-! ### Post-Processing Lemmas for kantLift -/

theorem kantLift_comp_right {β γ : Type} (d : EPseudoMetric β) (d' : EPseudoMetric γ)
    (μ ν : SPComp β) (k : β → SPComp γ)
    (hk : ∀ D', IsLipDist d' D' → IsLipDist d (fun b => SPComp.bind (k b) D')) :
    kantLift d' (SPComp.bind μ k) (SPComp.bind ν k) ≤ kantLift d μ ν := by
  apply iSup_le; intro D'; apply iSup_le; intro hD'; apply iSup_le; intro h₀
  let D : β → SPComp Bool := fun b => SPComp.bind (k b) D'
  rw [show SPComp.bind (SPComp.bind μ k) D' = SPComp.bind μ D from SPComp.bind_assoc _ _ _,
      show SPComp.bind (SPComp.bind ν k) D' = SPComp.bind ν D from SPComp.bind_assoc _ _ _]
  exact le_iSup₂_of_le D (hk D' hD') (le_iSup_of_le h₀ le_rfl)

theorem kantLift_comp_left {β γ : Type} (d : EPseudoMetric γ)
    (c : SPComp β) (g₁ g₂ : β → SPComp γ) :
    kantLift d (SPComp.bind c g₁) (SPComp.bind c g₂) ≤
    ⨆ (b : β), kantLift d (g₁ b) (g₂ b) := by
  apply iSup_le; intro D; apply iSup_le; intro hD; apply iSup_le; intro h₀
  rw [show SPComp.bind (SPComp.bind c g₁) D = SPComp.bind c (fun b => SPComp.bind (g₁ b) D)
        from SPComp.bind_assoc _ _ _,
      show SPComp.bind (SPComp.bind c g₂) D = SPComp.bind c (fun b => SPComp.bind (g₂ b) D)
        from SPComp.bind_assoc _ _ _]
  set ε := ⨆ (b : β), kantLift d (g₁ b) (g₂ b)
  apply absDiff_prTrue_bind_le c _ _ h₀ ε
  · intro b h'; dsimp only
    apply le_add_of_absDiff_le
    apply le_trans _ (le_iSup (fun b => kantLift d (g₁ b) (g₂ b)) b)
    exact le_iSup₂_of_le D hD (le_iSup_of_le h' le_rfl)
  · intro b h'; dsimp only
    apply le_add_of_absDiff_le; rw [absDiff_comm]
    apply le_trans _ (le_iSup (fun b => kantLift d (g₁ b) (g₂ b)) b)
    exact le_iSup₂_of_le D hD (le_iSup_of_le h' le_rfl)

theorem kantLift_pure {β : Type} (d : EPseudoMetric β) (x y : β) :
    kantLift d (SPComp.pure x) (SPComp.pure y) ≤ d.dist x y := by
  apply iSup_le; intro D; apply iSup_le; intro hD; apply iSup_le; intro h₀
  rw [SPComp.pure_bind, SPComp.pure_bind]; exact hD x y h₀

/-! ## Phase 3: Recursive Kantorovich on RoundM -/

noncomputable def kdistRoundM_pt : (n : Nat) → (β : Type) → EPseudoMetric (RoundM n β)
  | 0, β => kantLiftMetric (discreteMetric β)
  | n + 1, β => kantLiftMetric (sumMetric (discreteMetric β) (kdistRoundM_pt n β))

noncomputable def kdistRoundM {α β : Type} (n : Nat) (f g : α → RoundM n β) : ℝ≥0∞ :=
  ⨆ (a : α), (kdistRoundM_pt n β).dist (f a) (g a)

/-! ### Pseudometric Properties -/

theorem kdistRoundM_self {α β : Type} (n : Nat) (f : α → RoundM n β) :
    kdistRoundM n f f = 0 := by
  simp [kdistRoundM, (kdistRoundM_pt n β).dist_self]

theorem kdistRoundM_sym {α β : Type} (n : Nat) (f g : α → RoundM n β) :
    kdistRoundM n f g = kdistRoundM n g f := by
  simp only [kdistRoundM, (kdistRoundM_pt n β).dist_sym]

theorem kdistRoundM_triangle {α β : Type} (n : Nat)
    (f g h : α → RoundM n β) :
    kdistRoundM n f h ≤ kdistRoundM n f g + kdistRoundM n g h := by
  apply iSup_le; intro a
  exact le_trans ((kdistRoundM_pt n β).dist_triangle _ _ _)
    (add_le_add (le_iSup (fun a => (kdistRoundM_pt n β).dist (f a) (g a)) a)
      (le_iSup (fun a => (kdistRoundM_pt n β).dist (g a) (h a)) a))

/-! ### Flatten non-expansiveness -/

/-- Auxiliary: any `d`-Lip distinguisher composed with flatCont₀ is
    `sumMetric disc (kdistRoundM_pt 0 β)`-Lip. -/
private theorem flatCont_zero_lip {β : Type} (D' : β → SPComp Bool) (hD' : IsLipDist (discreteMetric β) D') :
    IsLipDist (sumMetric (discreteMetric β) (kdistRoundM_pt 0 β))
      (fun x : β ⊕ RoundM 0 β => match x with
        | .inl a => SPComp.bind (SPComp.pure a) D'
        | .inr k => SPComp.bind k D') := by
  intro x y h₀
  cases x with
  | inl a₁ =>
    cases y with
    | inl a₂ => simp [SPComp.pure_bind]; exact hD' a₁ a₂ h₀
    | inr _ => simp
  | inr k₁ =>
    cases y with
    | inl _ => simp
    | inr k₂ =>
      simp only [sumMetric_dist_inr_inr, kdistRoundM_pt, kantLiftMetric]
      exact le_iSup₂_of_le D' hD' (le_iSup_of_le h₀ le_rfl)

/-- Auxiliary: any `sumMetric disc (kdistRoundM_pt m)`-Lip distinguisher composed with
    flatCont_{m+1} is `sumMetric disc (kdistRoundM_pt (m+1))`-Lip. -/
private theorem flatCont_succ_lip {β : Type} (m : Nat) (D' : (β ⊕ RoundM m β) → SPComp Bool)
    (hD' : IsLipDist (sumMetric (discreteMetric β) (kdistRoundM_pt m β)) D') :
    IsLipDist (sumMetric (discreteMetric β) (kdistRoundM_pt (m + 1) β))
      (fun x : β ⊕ RoundM (m + 1) β => match x with
        | .inl a => SPComp.bind (SPComp.pure (Sum.inl a) : SPComp (β ⊕ RoundM m β)) D'
        | .inr k => SPComp.bind k D') := by
  intro x y h₀
  cases x with
  | inl a₁ =>
    cases y with
    | inl a₂ =>
      simp only [sumMetric_dist_inl_inl, SPComp.pure_bind]
      exact le_trans (hD' (.inl a₁) (.inl a₂) h₀) (by simp)
    | inr _ => simp
  | inr k₁ =>
    cases y with
    | inl _ => simp
    | inr k₂ =>
      simp only [sumMetric_dist_inr_inr, kdistRoundM_pt, kantLiftMetric]
      exact le_iSup₂_of_le D' hD' (le_iSup_of_le h₀ le_rfl)

/-- flatten is non-expansive from `kdistRoundM_pt (m+1)` to `kdistRoundM_pt m`. -/
private theorem flatten_nonexpansive (m : Nat) {β : Type}
    (μ ν : RoundM (m + 1) β) :
    (kdistRoundM_pt m β).dist (RoundM.flatten m μ) (RoundM.flatten m ν) ≤
    (kdistRoundM_pt (m + 1) β).dist μ ν := by
  cases m with
  | zero =>
    -- flatten 0 μ = SPComp.bind μ (fun | .inl a => pure a | .inr k => k)
    -- kdistRoundM_pt 0 = kantLiftMetric (discreteMetric β)
    -- kdistRoundM_pt 1 = kantLiftMetric (sumMetric discrete (kdist_pt 0))
    show kantLift (discreteMetric β) (RoundM.flatten 0 μ) (RoundM.flatten 0 ν) ≤
         kantLift (sumMetric (discreteMetric β) (kdistRoundM_pt 0 β)) μ ν
    simp only [RoundM.flatten_zero]
    apply kantLift_comp_right
      (sumMetric (discreteMetric β) (kdistRoundM_pt 0 β)) (discreteMetric β) μ ν
    intro D' hD' x y h₀
    cases x with
    | inl a₁ =>
      cases y with
      | inl a₂ => simp [SPComp.pure_bind]; exact hD' a₁ a₂ h₀
      | inr _ => simp
    | inr k₁ =>
      cases y with
      | inl _ => simp
      | inr k₂ =>
        simp only [sumMetric_dist_inr_inr, kdistRoundM_pt, kantLiftMetric]
        exact le_iSup₂_of_le D' hD' (le_iSup_of_le h₀ le_rfl)
  | succ m' =>
    -- flatten (m'+1) μ = SPComp.bind μ (fun | .inl a => pure (.inl a) | .inr k => k)
    show kantLift (sumMetric (discreteMetric β) (kdistRoundM_pt m' β))
           (RoundM.flatten (m' + 1) μ) (RoundM.flatten (m' + 1) ν) ≤
         kantLift (sumMetric (discreteMetric β) (kdistRoundM_pt (m' + 1) β)) μ ν
    simp only [RoundM.flatten_succ]
    apply kantLift_comp_right
      (sumMetric (discreteMetric β) (kdistRoundM_pt (m' + 1) β))
      (sumMetric (discreteMetric β) (kdistRoundM_pt m' β)) μ ν
    intro D' hD' x y h₀
    cases x with
    | inl a₁ =>
      cases y with
      | inl a₂ =>
        simp only [sumMetric_dist_inl_inl, SPComp.pure_bind]
        exact le_trans (hD' (.inl a₁) (.inl a₂) h₀) (by simp)
      | inr _ => simp
    | inr k₁ =>
      cases y with
      | inl _ => simp
      | inr k₂ =>
        simp only [sumMetric_dist_inr_inr, kdistRoundM_pt, kantLiftMetric]
        exact le_iSup₂_of_le D' hD' (le_iSup_of_le h₀ le_rfl)

/-! ### Right PPL -/

private theorem kdistRoundM_pt_comp_right :
    ∀ (n : Nat) {β γ : Type} (μ ν : RoundM n β) (k : β → RoundM n γ),
    (kdistRoundM_pt n γ).dist (RoundM.bind' n μ k) (RoundM.bind' n ν k) ≤
    (kdistRoundM_pt n β).dist μ ν := by
  intro n; induction n with
  | zero =>
    intro β γ μ ν k
    show kantLift (discreteMetric γ) (SPComp.bind μ k) (SPComp.bind ν k) ≤
         kantLift (discreteMetric β) μ ν
    apply kantLift_comp_right _ _ μ ν k
    intro D' _hD' b₁ b₂ h₀
    unfold discreteMetric; simp only
    by_cases h : b₁ = b₂
    · subst h; simp [absDiff_self]
    · simp only [if_neg h]; exact le_top
  | succ m ih =>
    intro β γ μ ν k
    simp only [RoundM.bind'_succ, kdistRoundM_pt]
    apply kantLift_comp_right
      (sumMetric (discreteMetric β) (kdistRoundM_pt m β))
      (sumMetric (discreteMetric γ) (kdistRoundM_pt m γ)) μ ν
    intro D' hD' x y h₀
    cases x with
    | inl a₁ =>
      cases y with
      | inl a₂ =>
        simp only [sumMetric_dist_inl_inl, discreteMetric]
        by_cases h : a₁ = a₂
        · subst h; simp [absDiff_self]
        · simp only [if_neg h]; exact le_top
      | inr _ => simp
    | inr c₁ =>
      cases y with
      | inl _ => simp
      | inr c₂ =>
        simp only [sumMetric_dist_inr_inr, SPComp.pure_bind]
        exact le_trans
          (hD' (.inr (RoundM.bind' m c₁ (fun a => RoundM.flatten m (k a))))
               (.inr (RoundM.bind' m c₂ (fun a => RoundM.flatten m (k a)))) h₀)
          (by simp only [sumMetric_dist_inr_inr]
              exact ih c₁ c₂ (fun a => RoundM.flatten m (k a)))

theorem kdistRoundM_comp_right {α β γ : Type} (n : Nat)
    (f g : α → RoundM n β) (k : β → RoundM n γ) :
    kdistRoundM n (fun a => f a >>= k) (fun a => g a >>= k) ≤ kdistRoundM n f g := by
  apply iSup_le; intro a
  exact le_trans (kdistRoundM_pt_comp_right n (f a) (g a) k)
    (le_iSup (fun a => (kdistRoundM_pt n β).dist (f a) (g a)) a)

/-! ### Left PPL -/

private theorem kdistRoundM_pt_comp_left :
    ∀ (n : Nat) {β γ : Type} (c : RoundM n β) (g₁ g₂ : β → RoundM n γ),
    (kdistRoundM_pt n γ).dist (RoundM.bind' n c g₁) (RoundM.bind' n c g₂) ≤
    ⨆ (b : β), (kdistRoundM_pt n γ).dist (g₁ b) (g₂ b) := by
  intro n; induction n with
  | zero =>
    intro β γ c g₁ g₂
    exact kantLift_comp_left (discreteMetric γ) c g₁ g₂
  | succ m ih =>
    intro β γ c g₁ g₂
    simp only [RoundM.bind'_succ, kdistRoundM_pt]
    -- Goal: kantLift d_γ (SPComp.bind c cont₁) (SPComp.bind c cont₂) ≤ ⨆ b, kantLift d_γ (g₁ b) (g₂ b)
    -- where cont_i x = match x with | .inl a => g_i a | .inr k => pure (.inr (bind' m k (flatten ∘ g_i)))
    -- Step 1: kantLift_comp_left gives ≤ ⨆ x, kantLift d_γ (cont₁ x) (cont₂ x)
    -- Step 2: bound ⨆ x by ⨆ b
    set d_γ := sumMetric (discreteMetric γ) (kdistRoundM_pt m γ)
    -- Use le_trans with the intermediate ⨆ over sum type
    apply le_trans (kantLift_comp_left d_γ c _ _)
    apply iSup_le; intro x
    cases x with
    | inl b => exact le_iSup (fun b => kantLift d_γ (g₁ b) (g₂ b)) b
    | inr cont =>
      -- kantLift d_γ (pure (.inr X)) (pure (.inr Y)) ≤ d_γ.dist (.inr X) (.inr Y)
      --   = (kdistRoundM_pt m γ).dist X Y     by sumMetric reduction
      --   = (kdistRoundM_pt m γ).dist (bind' m cont (flatten ∘ g₁)) (bind' m cont (flatten ∘ g₂))
      --   ≤ ⨆ b, (kdistRoundM_pt m γ).dist (flatten (g₁ b)) (flatten (g₂ b))   by ih
      --   ≤ ⨆ b, (kdistRoundM_pt (m+1) γ).dist (g₁ b) (g₂ b)   by flatten_nonexpansive
      --   = ⨆ b, kantLift d_γ (g₁ b) (g₂ b)
      calc kantLift d_γ
              (SPComp.pure (.inr (RoundM.bind' m cont (fun a => RoundM.flatten m (g₁ a)))))
              (SPComp.pure (.inr (RoundM.bind' m cont (fun a => RoundM.flatten m (g₂ a)))))
          ≤ d_γ.dist
              (.inr (RoundM.bind' m cont (fun a => RoundM.flatten m (g₁ a))))
              (.inr (RoundM.bind' m cont (fun a => RoundM.flatten m (g₂ a)))) :=
            kantLift_pure d_γ _ _
        _ = (kdistRoundM_pt m γ).dist
              (RoundM.bind' m cont (fun a => RoundM.flatten m (g₁ a)))
              (RoundM.bind' m cont (fun a => RoundM.flatten m (g₂ a))) := by
            simp only [d_γ, sumMetric_dist_inr_inr]
        _ ≤ ⨆ (b : β), (kdistRoundM_pt m γ).dist
              (RoundM.flatten m (g₁ b)) (RoundM.flatten m (g₂ b)) :=
            ih cont _ _
        _ ≤ ⨆ (b : β), kantLift d_γ (g₁ b) (g₂ b) := by
            apply iSup_le; intro b
            exact le_trans (flatten_nonexpansive m (g₁ b) (g₂ b))
              (le_iSup (fun b => kantLift d_γ (g₁ b) (g₂ b)) b)

theorem kdistRoundM_comp_left {α β γ : Type} (n : Nat)
    (f : α → RoundM n β) (g₁ g₂ : β → RoundM n γ) :
    kdistRoundM n (fun a => f a >>= g₁) (fun a => f a >>= g₂) ≤ kdistRoundM n g₁ g₂ := by
  apply iSup_le; intro a
  exact le_trans (kdistRoundM_pt_comp_left n (f a) g₁ g₂) le_rfl

/-! ## Phase 4: Comparison + UCMonadMetric -/

private theorem sdist_flattenAll_le_kdistRoundM_pt :
    ∀ (n : Nat) {β : Type} (μ ν : RoundM n β),
    kantLift (discreteMetric β) (RoundM.flattenAll n μ) (RoundM.flattenAll n ν) ≤
    (kdistRoundM_pt n β).dist μ ν := by
  intro n; induction n with
  | zero => intro β μ ν; exact le_rfl
  | succ m ih =>
    intro β μ ν; simp only [RoundM.flattenAll_succ]
    exact le_trans (ih (RoundM.flatten m μ) (RoundM.flatten m ν))
      (flatten_nonexpansive m μ ν)

theorem sdistRoundM_le_kdistRoundM {α β : Type} (n : Nat)
    (f g : α → RoundM n β) :
    sdistRoundM n f g ≤ kdistRoundM n f g := by
  unfold sdistRoundM sdist
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro h₀
  dsimp only
  apply le_trans _ (le_iSup (fun a => (kdistRoundM_pt n β).dist (f a) (g a)) a)
  apply le_trans _ (sdist_flattenAll_le_kdistRoundM_pt n (f a) (g a))
  exact le_iSup₂_of_le D (isLipDist_discrete D) (le_iSup_of_le h₀ le_rfl)

noncomputable def UCMonadMetric_RoundM_Kantorovich (n : Nat) :
    UCMonadMetric (RoundM n) where
  ucMapSum := mapSumRoundM n
  ucMapSum_inl := fun _f _g _a => rfl
  ucMapSum_inr := fun _f _g _c => rfl
  ucMapSum_pure_pure := mapSumRoundM_pure_pure n
  ucMapSum_pure_kleisli := fun f g => mapSumRoundM_pure_kleisli n f g
  ucSdist := kdistRoundM n
  ucSdist_self := kdistRoundM_self n
  ucSdist_sym := kdistRoundM_sym n
  ucSdist_triangle := kdistRoundM_triangle n
  ucSdist_comp_right := kdistRoundM_comp_right n
  ucSdist_comp_left := kdistRoundM_comp_left n

end UCMonad.RoundMUC
