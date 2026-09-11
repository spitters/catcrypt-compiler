/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.UCMonad.ITreeNCompose

/-!
# ITreeN Multi-Session and Parallel Composition

This file proves multi-session and parallel composition theorems for `ITreeN`,
lifting the SPComp-level results from `RC.lean` to the ITreeN level.

## Main results

* `sdist_mapSumITreeN_le` — coproduct tensor bound: `max(ε₁, ε₂)`
* `UCEmulatesConcurrent_of_sdist` — sdist implies concurrent UC (same-interface)
* `UCEmulatesConcurrent_par` — parallel composition preserves concurrent UC
* `UCEmulatesConcurrent_multisession` — k copies with same bound
* `compileITreeN` — subroutine compilation at ITreeN level
* `sdist_compileITreeN` — compilation preserves sdist bounds additively
* `UCEmulatesConcurrent_compile` — UC subroutine composition

## Axiom status

**0 axioms**, **0 sorries**. All proofs complete.
-/

@[expose] public section

namespace UCMonad.ITreeNUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Section 1: flattenAll commutes with done -/

theorem flatten_done_aux {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    (n : Nat) → (a : α) →
    ITreeN.flatten handler n (ITreeN.done (E := E) (n + 1) a) = ITreeN.done n a
  | 0, a => by unfold ITreeN.flatten ITreeN.done; exact SPComp.pure_bind (Sum.inl a) _
  | _ + 1, a => by unfold ITreeN.flatten ITreeN.done; exact SPComp.pure_bind (Sum.inl a) _

theorem flattenAll_done {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    (n : Nat) → (a : α) →
    ITreeN.flattenAll (E := E) handler n (ITreeN.done n a) = SPComp.pure a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [ITreeN.flattenAll_succ, flatten_done_aux handler n a]
    exact flattenAll_done handler n a

/-! ## Section 2: flattenAll commutes with mapSumITreeN -/

theorem flattenAll_mapSumITreeN {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f : α → ITreeN n E β) (g : γ → ITreeN n E δ) (x : α ⊕ γ) :
    ITreeN.flattenAll handler n (mapSumITreeN handler n f g x) =
    mapSumSP (fun a => ITreeN.flattenAll handler n (f a))
           (fun c => ITreeN.flattenAll handler n (g c)) x := by
  cases x with
  | inl a =>
    simp only [mapSumITreeN, mapSumSP_inl, SPComp.map]
    rw [flattenAll_bind]
    congr 1; funext b
    exact flattenAll_done handler n (Sum.inl b)
  | inr c =>
    simp only [mapSumITreeN, mapSumSP_inr, SPComp.map]
    rw [flattenAll_bind]
    congr 1; funext d
    exact flattenAll_done handler n (Sum.inr d)

/-! ## Section 3: Coproduct tensor bound -/

/-- For coproduct tensor at ITreeN level: distance is max, not sum,
    since only one branch runs per input. -/
theorem sdist_mapSumITreeN_le {α₁ α₂ β₁ β₂ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (f₁ f₂ : α₁ → ITreeN n E β₁) (g₁ g₂ : α₂ → ITreeN n E β₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (hf : sdistITreeN n E handler f₁ f₂ ≤ ε₁)
    (hg : sdistITreeN n E handler g₁ g₂ ≤ ε₂) :
    sdistITreeN n E handler
      (mapSumITreeN handler n f₁ g₁) (mapSumITreeN handler n f₂ g₂) ≤ ε₁ ⊔ ε₂ := by
  unfold sdistITreeN
  -- Rewrite flattenAll through mapSumITreeN
  conv_lhs =>
    arg 1; ext x; rw [flattenAll_mapSumITreeN]
  conv_lhs =>
    arg 2; ext x; rw [flattenAll_mapSumITreeN]
  -- Now at SPComp level: sdist(mapSumSP ..., mapSumSP ...) ≤ ε₁ ⊔ ε₂
  exact sdist_mapSumSP_le _ _ _ _ hf hg

/-! ## Section 4: sdist of constant functions -/

/-- sdist of constant functions from any type is ≤ sdist from Unit. -/
theorem sdistITreeN_const_le_unit {β : Type} {E : EventSig} {α : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (c c' : ITreeN n E β) :
    sdistITreeN n E handler (fun (_ : α) => c) (fun (_ : α) => c')
    ≤ sdistITreeN n E handler (fun () => c) (fun () => c') := by
  unfold sdistITreeN sdist
  apply iSup_le; intro D
  apply iSup_le; intro _
  apply iSup_le; intro h₀
  exact le_iSup₂_of_le D () (le_iSup_of_le h₀ le_rfl)

/-! ## Section 5: UC emulation from sdist -/

/-- Same-interface sdist bound implies concurrent UC emulation. -/
theorem UCEmulatesConcurrent_of_sdist {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak : Type} {ε : ℝ≥0∞}
    (π F : hon → ITreeN n E (out ⊕ leak))
    (h : sdistITreeN n E handler π F ≤ ε) :
    UCEmulatesConcurrent handler n ε π F := by
  intro A
  exact ⟨A, le_trans (sdistITreeN_comp_right n E handler π F A) h⟩

/-! ## Section 6: Parallel composition -/

/-- Parallel composition of concurrent UC emulation from sdist bounds.
    The max bound (not sum!) reflects the coproduct structure. -/
theorem UCEmulatesConcurrent_par_of_sdist {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon₁ hon₂ β₁ β₂ : Type} {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : hon₁ → ITreeN n E β₁) (π₂ F₂ : hon₂ → ITreeN n E β₂)
    (h₁ : sdistITreeN n E handler π₁ F₁ ≤ ε₁)
    (h₂ : sdistITreeN n E handler π₂ F₂ ≤ ε₂) :
    UCEmulatesConcurrent handler n (ε₁ ⊔ ε₂)
      (mapSumITreeN handler n π₁ π₂) (mapSumITreeN handler n F₁ F₂) :=
  UCEmulatesConcurrent_of_sdist handler n _ _
    (sdist_mapSumITreeN_le handler n π₁ F₁ π₂ F₂ h₁ h₂)

/-! ## Section 7: Multi-session theorem -/

/-- k-fold multi-session: if π UC-emulates F for a single session,
    then k copies also UC-emulate with the same bound.

    The bound doesn't change because `sdistITreeN` takes the sup over
    all inputs. When all sessions run the same protocol, the sup over
    `Fin k` equals the sup over a single input. -/
theorem UCEmulatesConcurrent_multisession {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {out leak view : Type} {ε : ℝ≥0∞}
    (π : ITreeN n E (out ⊕ leak))
    (F : ITreeN n E (out ⊕ view))
    (h : UCEmulatesConcurrent handler n ε (fun () => π) (fun () => F))
    (k : Nat) :
    UCEmulatesConcurrent handler n ε
      (fun (_ : Fin k) => π) (fun (_ : Fin k) => F) := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans (sdistITreeN_const_le_unit handler n _ _) hS⟩

/-! ## Section 8: Subroutine compilation -/

/-- Subroutine compilation at ITreeN level: replace each subroutine call
    (in the `.inr` output) with a concrete implementation. -/
noncomputable def compileITreeN {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    (π : α → ITreeN n E (β ⊕ γ)) (ρ : γ → ITreeN n E δ) :
    α → ITreeN n E (β ⊕ δ) :=
  fun a => ITreeN.bind' handler n (π a)
    (mapSumITreeN handler n (ITreeN.done n) ρ)

/-! ## Section 9: Compilation distance bound -/

/-- Compilation with same subroutine preserves sdist. -/
theorem sdist_compileITreeN_same {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε : ℝ≥0∞}
    (π F : α → ITreeN n E (β ⊕ γ))
    (ρ : γ → ITreeN n E δ)
    (hπ : sdistITreeN n E handler π F ≤ ε) :
    sdistITreeN n E handler
      (compileITreeN handler n π ρ) (compileITreeN handler n F ρ) ≤ ε :=
  le_trans (sdistITreeN_comp_right n E handler π F _) hπ

/-- Compilation preserves sdist bounds additively.
    Triangle through `compileITreeN π ρ_ideal`. -/
theorem sdist_compileITreeN {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε₁ ε₂ : ℝ≥0∞}
    (π F : α → ITreeN n E (β ⊕ γ))
    (ρ_real ρ_ideal : γ → ITreeN n E δ)
    (hπ : sdistITreeN n E handler π F ≤ ε₁)
    (hρ : sdistITreeN n E handler ρ_real ρ_ideal ≤ ε₂) :
    sdistITreeN n E handler
      (compileITreeN handler n π ρ_real)
      (compileITreeN handler n F ρ_ideal) ≤ ε₁ + ε₂ := by
  -- Triangle through compileITreeN π ρ_ideal
  calc sdistITreeN n E handler
        (compileITreeN handler n π ρ_real)
        (compileITreeN handler n F ρ_ideal)
      ≤ sdistITreeN n E handler
          (compileITreeN handler n π ρ_real)
          (compileITreeN handler n π ρ_ideal)
        + sdistITreeN n E handler
          (compileITreeN handler n π ρ_ideal)
          (compileITreeN handler n F ρ_ideal) :=
        sdistITreeN_triangle n E handler _ _ _
    _ ≤ ε₂ + ε₁ := by
        apply add_le_add
        · -- Subroutine swap: same π, different ρ
          show sdistITreeN n E handler
            (fun a => ITreeN.bind' handler n (π a) (mapSumITreeN handler n (ITreeN.done n) ρ_real))
            (fun a => ITreeN.bind' handler n (π a) (mapSumITreeN handler n (ITreeN.done n) ρ_ideal))
            ≤ ε₂
          calc sdistITreeN n E handler _ _
              ≤ sdistITreeN n E handler
                  (mapSumITreeN handler n (ITreeN.done n) ρ_real)
                  (mapSumITreeN handler n (ITreeN.done n) ρ_ideal) :=
                sdistITreeN_comp_left n E handler π _ _
            _ ≤ sdistITreeN n E handler (ITreeN.done n) (ITreeN.done n) ⊔
                sdistITreeN n E handler ρ_real ρ_ideal :=
                sdist_mapSumITreeN_le handler n _ _ _ _ le_rfl le_rfl
            _ = 0 ⊔ sdistITreeN n E handler ρ_real ρ_ideal := by
                rw [sdistITreeN_self]
            _ = sdistITreeN n E handler ρ_real ρ_ideal := by simp
            _ ≤ ε₂ := hρ
        · -- Protocol swap: different π, same ρ_ideal
          exact sdist_compileITreeN_same handler n π F ρ_ideal hπ
    _ = ε₁ + ε₂ := add_comm ε₂ ε₁

/-! ## Section 10: UC subroutine composition -/

/-- UC subroutine composition at ITreeN level.
    If protocol π is sdist-close to F and subroutine ρ_real is sdist-close to ρ_ideal,
    the compiled protocol UC-emulates the compiled functionality. -/
theorem UCEmulatesConcurrent_compile {α β γ δ : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) (n : Nat)
    {ε₁ ε₂ : ℝ≥0∞}
    (π F : α → ITreeN n E (β ⊕ γ))
    (ρ_real ρ_ideal : γ → ITreeN n E δ)
    (hπ : sdistITreeN n E handler π F ≤ ε₁)
    (hρ : sdistITreeN n E handler ρ_real ρ_ideal ≤ ε₂) :
    UCEmulatesConcurrent handler n (ε₁ + ε₂)
      (compileITreeN handler n π ρ_real)
      (compileITreeN handler n F ρ_ideal) :=
  UCEmulatesConcurrent_of_sdist handler n _ _
    (sdist_compileITreeN handler n π F ρ_real ρ_ideal hπ hρ)

end UCMonad.ITreeNUC
