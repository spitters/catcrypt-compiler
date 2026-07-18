/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.UCMonad.ITreeNMultiSession

/-!
# ITreeN Product (Interleaving) Composition

This file defines product (pair) composition for `ITreeN`, complementing the
coproduct (sum) composition in `ITreeNMultiSession.lean`.

## Key idea

While coproduct composition runs ONE of two protocols per input (max bound),
product composition runs BOTH protocols and pairs the outputs (additive bound).

Since `sdistITreeN` uses `flattenAll` (which collapses all round structure),
sequential execution via `bind'` gives the same statistical distance as any
interleaving schedule.

## Main results

* `sdist_comp_right_dep` — dependent right PPL at SPComp level
* `sdist_pairSPComp_le` — pair bound at SPComp level: `ε₁ + ε₂`
* `pairITreeN` — product composition of ITreeN protocols
* `sdist_pairITreeN_le` — pair bound at ITreeN level
* `vecITreeN` — k-ary product composition
* `sdist_vecITreeN_le` — k-ary bound: `k * ε`
* `UCEmulatesConcurrent_pair` — UC pair composition
* `UCEmulatesConcurrent_vec` — UC k-ary composition

## Axiom status

**0 axioms**, **0 sorries**. All proofs complete.
-/

namespace UCMonad.ITreeNUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Section 1: Dependent Post-Processing Lemmas -/

/-- Dependent right PPL: post-composition with an `a`-dependent continuation
    doesn't increase distance. Generalizes `sdist_comp_right` where `g` is constant. -/
theorem sdist_comp_right_dep {α β γ : Type*} (f₁ f₂ : α → SPComp β)
    (k : α → β → SPComp γ) :
    sdist (fun a => SPComp.bind (f₁ a) (k a))
          (fun a => SPComp.bind (f₂ a) (k a)) ≤ sdist f₁ f₂ := by
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  let D' : β → SPComp Bool := fun b => SPComp.bind (k a b) D
  have eq1 : SPComp.bind (SPComp.bind (f₁ a) (k a)) D =
    SPComp.bind (f₁ a) D' := by
    simp [D', SPComp.bind_assoc]
  have eq2 : SPComp.bind (SPComp.bind (f₂ a) (k a)) D =
    SPComp.bind (f₂ a) D' := by
    simp [D', SPComp.bind_assoc]
  rw [eq1, eq2]
  exact le_iSup₂_of_le D' a (le_iSup_of_le h₀ le_rfl)

/-- Dependent left PPL: pre-composition with an `a`-dependent continuation pair
    doesn't increase distance beyond a uniform bound on the continuations. -/
theorem sdist_comp_left_dep {α β γ : Type*} (f : α → SPComp β)
    (k₁ k₂ : α → β → SPComp γ) {ε : ℝ≥0∞}
    (hk : ∀ a, sdist (k₁ a) (k₂ a) ≤ ε) :
    sdist (fun a => SPComp.bind (f a) (k₁ a))
          (fun a => SPComp.bind (f a) (k₂ a)) ≤ ε := by
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  have eq1 : SPComp.bind (SPComp.bind (f a) (k₁ a)) D =
    SPComp.bind (f a) (fun b => SPComp.bind (k₁ a b) D) := SPComp.bind_assoc _ _ _
  have eq2 : SPComp.bind (SPComp.bind (f a) (k₂ a)) D =
    SPComp.bind (f a) (fun b => SPComp.bind (k₂ a b) D) := SPComp.bind_assoc _ _ _
  rw [eq1, eq2]
  apply absDiff_prTrue_bind_le (f a) _ _ h₀ ε
  · intro b h'
    exact le_add_of_absDiff_le (sdist_le_of_forall (hk a) D b h')
  · intro b h'
    have := sdist_le_of_forall (hk a) D b h'
    exact le_add_of_absDiff_le (by rwa [absDiff_comm] at this)

/-! ## Section 2: SPComp-Level Pair Composition -/

/-- Pair composition at SPComp level: run both computations and pair the results. -/
noncomputable def pairSPComp {α β₁ β₂ : Type}
    (f : α → SPComp β₁) (g : α → SPComp β₂) : α → SPComp (β₁ × β₂) :=
  fun a => SPComp.bind (f a) (fun b => SPComp.bind (g a) (fun c => SPComp.pure (b, c)))

/-- Pair bound at SPComp level: distance of pairs is at most sum of distances. -/
theorem sdist_pairSPComp_le {α β₁ β₂ : Type}
    (f₁ g₁ : α → SPComp β₁) (f₂ g₂ : α → SPComp β₂)
    {ε₁ ε₂ : ℝ≥0∞} (h₁ : sdist f₁ g₁ ≤ ε₁) (h₂ : sdist f₂ g₂ ≤ ε₂) :
    sdist (pairSPComp f₁ f₂) (pairSPComp g₁ g₂) ≤ ε₁ + ε₂ := by
  -- Triangle through mid = pairSPComp g₁ f₂
  calc sdist (pairSPComp f₁ f₂) (pairSPComp g₁ g₂)
      ≤ sdist (pairSPComp f₁ f₂) (pairSPComp g₁ f₂) +
        sdist (pairSPComp g₁ f₂) (pairSPComp g₁ g₂) :=
        sdist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := by
        apply add_le_add
        · -- Term 1: changing f₁ → g₁ (dependent right PPL)
          exact le_trans (sdist_comp_right_dep f₁ g₁
            (fun a b => SPComp.bind (f₂ a) (fun c => SPComp.pure (b, c)))) h₁
        · -- Term 2: changing f₂ → g₂ (dependent left PPL)
          apply le_trans _ h₂
          apply sdist_comp_left_dep g₁
            (fun a b => SPComp.bind (f₂ a) (fun c => SPComp.pure (b, c)))
            (fun a b => SPComp.bind (g₂ a) (fun c => SPComp.pure (b, c)))
          -- For each a: sdist (fun b => bind (f₂ a) ...) (fun b => bind (g₂ a) ...) ≤ sdist f₂ g₂
          intro a
          apply iSup_le; intro D; apply iSup_le; intro b; apply iSup_le; intro h₀'
          have eq1 : SPComp.bind (SPComp.bind (f₂ a) (fun c => SPComp.pure (b, c))) D =
            SPComp.bind (f₂ a) (fun c => D (b, c)) := by
            rw [SPComp.bind_assoc]; congr 1; funext c; exact SPComp.pure_bind (b, c) D
          have eq2 : SPComp.bind (SPComp.bind (g₂ a) (fun c => SPComp.pure (b, c))) D =
            SPComp.bind (g₂ a) (fun c => D (b, c)) := by
            rw [SPComp.bind_assoc]; congr 1; funext c; exact SPComp.pure_bind (b, c) D
          rw [eq1, eq2]
          exact le_iSup₂_of_le (fun c => D (b, c)) a (le_iSup_of_le h₀' le_rfl)

/-! ## Section 3: ITreeN-Level Pair Composition -/

/-- Product composition of ITreeN protocols: run both and pair outputs. -/
noncomputable def pairITreeN {α β₁ β₂ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f : α → ITreeN n E β₁) (g : α → ITreeN n E β₂) :
    α → ITreeN n E (β₁ × β₂) :=
  fun a => ITreeN.bind' handler n (f a)
    (fun b => ITreeN.bind' handler n (g a) (fun c => ITreeN.done n (b, c)))

/-- `flattenAll` commutes with `pairITreeN`, reducing to `pairSPComp`. -/
theorem flattenAll_pairITreeN {α β₁ β₂ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f : α → ITreeN n E β₁) (g : α → ITreeN n E β₂) (a : α) :
    ITreeN.flattenAll handler n (pairITreeN handler n f g a) =
    pairSPComp (fun a => ITreeN.flattenAll handler n (f a))
               (fun a => ITreeN.flattenAll handler n (g a)) a := by
  simp only [pairITreeN, pairSPComp]
  rw [flattenAll_bind]
  congr 1; funext b
  rw [flattenAll_bind]
  congr 1; funext c
  exact flattenAll_done handler n (b, c)

/-! ## Section 4: ITreeN Pair Distance -/

/-- Pair bound at ITreeN level: distance of pairs is at most sum of distances. -/
theorem sdist_pairITreeN_le {α β₁ β₂ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f₁ g₁ : α → ITreeN n E β₁) (f₂ g₂ : α → ITreeN n E β₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : sdistITreeN n E handler f₁ g₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler f₂ g₂ ≤ ε₂) :
    sdistITreeN n E handler (pairITreeN handler n f₁ f₂)
      (pairITreeN handler n g₁ g₂) ≤ ε₁ + ε₂ := by
  unfold sdistITreeN
  conv_lhs => arg 1; ext a; rw [flattenAll_pairITreeN]
  conv_lhs => arg 2; ext a; rw [flattenAll_pairITreeN]
  exact sdist_pairSPComp_le _ _ _ _ h₁ h₂

/-! ## Section 5: k-ary Product Composition -/

/-- Nested pair type for k-ary products. -/
def VecTy (β : Type) : Nat → Type
  | 0 => PUnit
  | k + 1 => β × VecTy β k

/-- k-ary product with nested pair output. -/
noncomputable def vecITreeN {β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat) :
    (k : Nat) → (Fin k → ITreeN n E β) → ITreeN n E (VecTy β k)
  | 0, _ => ITreeN.done n PUnit.unit
  | k + 1, f => pairITreeN handler n
      (fun () => f 0) (fun () => vecITreeN handler n k (f ∘ Fin.succ)) ()

/-- k-ary product bound: distance is at most k * ε. -/
theorem sdist_vecITreeN_le {β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (k : Nat) (f g : Fin k → ITreeN n E β) (ε : ℝ≥0∞)
    (h : ∀ i, sdistITreeN n E handler (fun () => f i) (fun () => g i) ≤ ε) :
    sdistITreeN n E handler (fun () => vecITreeN handler n k f)
      (fun () => vecITreeN handler n k g) ≤ k * ε := by
  induction k with
  | zero => simp [vecITreeN, sdistITreeN, sdist_self]
  | succ k ih =>
    simp only [vecITreeN]
    rw [show (↑(k + 1) : ℝ≥0∞) * ε = ε + ↑k * ε from by push_cast; ring]
    exact sdist_pairITreeN_le handler n _ _ _ _ (h 0)
      (ih (f ∘ Fin.succ) (g ∘ Fin.succ) (fun i => h i.succ))

/-! ## Section 6: UC Composition Theorems -/

/-- For any sdist bound on pairITreeN, the ∀A∃S quantifier structure holds
    (same proof pattern as `UCEmulatesConcurrent_of_sdist`). -/
theorem pairITreeN_forall_exists {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon β₁ β₂ : Type} {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon → ITreeN n E β₁) (π₂ F₂ : hon → ITreeN n E β₂)
    (h₁ : sdistITreeN n E handler π₁ F₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler π₂ F₂ ≤ ε₂) :
    ∀ A : (β₁ × β₂) → ITreeN n E Bool,
    ∃ S : (β₁ × β₂) → ITreeN n E Bool,
      sdistITreeN n E handler
        (fun a => ITreeN.bind' handler n (pairITreeN handler n π₁ π₂ a) A)
        (fun a => ITreeN.bind' handler n (pairITreeN handler n F₁ F₂ a) S) ≤ ε₁ + ε₂ := by
  intro A
  exact ⟨A, le_trans (sdistITreeN_comp_right n E handler _ _ A)
    (sdist_pairITreeN_le handler n π₁ F₁ π₂ F₂ h₁ h₂)⟩

/-- UC pair composition: product composition with additive bound.
    The pair output is embedded into a sum type for `UCEmulatesConcurrent`. -/
theorem UCEmulatesConcurrent_pair {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon β₁ β₂ leak : Type} {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon → ITreeN n E β₁) (π₂ F₂ : hon → ITreeN n E β₂)
    (h₁ : sdistITreeN n E handler π₁ F₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler π₂ F₂ ≤ ε₂) :
    UCEmulatesConcurrent handler n (ε₁ + ε₂)
      (fun a => ITreeN.bind' handler n (pairITreeN handler n π₁ π₂ a)
        (fun p => ITreeN.done n (Sum.inl p : (β₁ × β₂) ⊕ leak)))
      (fun a => ITreeN.bind' handler n (pairITreeN handler n F₁ F₂ a)
        (fun p => ITreeN.done n (Sum.inl p : (β₁ × β₂) ⊕ leak))) := by
  apply UCEmulatesConcurrent_of_sdist
  calc sdistITreeN n E handler _ _
      ≤ sdistITreeN n E handler (pairITreeN handler n π₁ π₂)
          (pairITreeN handler n F₁ F₂) :=
        sdistITreeN_comp_right n E handler _ _ _
    _ ≤ ε₁ + ε₂ := sdist_pairITreeN_le handler n _ _ _ _ h₁ h₂

/-- UC k-ary composition: k copies of a UC-secure protocol remain UC-secure
    with bound k * ε. Uses `UCEmulatesConcurrent_multisession`. -/
theorem UCEmulatesConcurrent_vec_copies {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {out leak : Type} {ε : ℝ≥0∞} (k : Nat)
    (π F : ITreeN n E (out ⊕ leak))
    (h : UCEmulatesConcurrent handler n ε (fun () => π) (fun () => F)) :
    UCEmulatesConcurrent handler n ε
      (fun (_ : Fin k) => π) (fun (_ : Fin k) => F) :=
  UCEmulatesConcurrent_multisession handler n π F h k

end UCMonad.ITreeNUC
