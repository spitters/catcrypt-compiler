/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!
# Constructive Knaster-Tarski on Finite Sets

All proofs are complete; termination is by well-founded recursion.

Constructive greatest-fixpoint computation for monotone functions on `Finset α`.
The construction follows Dziembowski, Fabianski, Micciancio, Stefanski (CSF 2026, ePrint 2025/1700).

## What is proved

* `Finset.greatestFixpoint` — iteratively computes the GFP from an upper bound
* `Finset.greatestFixpoint_isFixpoint` — the result is a fixpoint
* `Finset.greatestFixpoint_access` — transport a transitive relation through the
  fixpoint iteration (the "accessibility" lemma)

## How it works

Given a monotone `f : Finset α → Finset α` bounded by `fBound`:

1. Start with `S = fBound` (upper bound)
2. If `f S = S`, done (found fixpoint)
3. Otherwise `f S ⊂ S` (strictly, since `f S ⊆ S` and `f S ≠ S`)
4. Replace `S` with `f S` and repeat

Termination: `S.card` decreases strictly at each step.

## Role in the architecture

The `greatestFixpoint_access` lemma is the key lemma for the computational soundness
proof: it transports computational indistinguishability (as a transitive relation)
through each GFP iteration step (hiding one more key). The module follows
Dziembowski et al. and is not connected to `SPComp` `sdist` bounds; that connection
is outside the scope of the `Soundness/` directory.

## References

* Dziembowski et al., "Computational Soundness of Symbolic Encryption in Lean 4",
  ePrint 2025/1700, file `Core/Fixpoints.lean` of the accompanying Lean development
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Soundness

/-! ## Greatest Fixpoint -/

/-- Compute the greatest fixpoint of a monotone function on `Finset α` by
iterating downward from an upper bound.

Given:
- `f` : monotone function on finite sets
- `fBound` : upper bound such that `f X ⊆ fBound` for all `X`

The iteration starts at `fBound` and repeatedly applies `f` until a fixpoint
is reached. Termination is guaranteed because `Finset.card` decreases strictly
at each non-fixpoint step. -/
def Finset.greatestFixpoint {α : Type} [DecidableEq α]
    (f : Finset α → Finset α)
    (f_monotone : ∀ X Y, X ⊆ Y → f X ⊆ f Y)
    (fBound : Finset α)
    (hBound : ∀ X, f X ⊆ fBound) : Finset α :=
  let rec gfix (S : Finset α) (_ : S ⊆ fBound) (h2 : f S ⊆ S) : Finset α :=
    if _ : f S = S then S
    else gfix (f S) (hBound S) (f_monotone _ _ h2)
  termination_by S.card
  decreasing_by
    apply Finset.card_lt_card
    exact h2.ssubset_of_ne (by assumption)
  gfix fBound (Finset.Subset.refl fBound) (hBound fBound)

/-- The greatest fixpoint is indeed a fixpoint: `f (gfp f) = gfp f`. -/
theorem Finset.greatestFixpoint_isFixpoint {α : Type} [DecidableEq α]
    (f : Finset α → Finset α)
    (f_monotone : ∀ X Y, X ⊆ Y → f X ⊆ f Y)
    (fBound : Finset α)
    (hBound : ∀ X, f X ⊆ fBound) :
    f (Finset.greatestFixpoint f f_monotone fBound hBound) =
    Finset.greatestFixpoint f f_monotone fBound hBound := by
  simp [Finset.greatestFixpoint]
  let rec gfixL (S : Finset α) (X : S ⊆ fBound) (Y : f S ⊆ S) :
      f (Finset.greatestFixpoint.gfix f f_monotone fBound hBound S X Y) =
      Finset.greatestFixpoint.gfix f f_monotone fBound hBound S X Y := by
    rw [Finset.greatestFixpoint.gfix]
    split
    · assumption
    · exact gfixL (f S) (hBound S) (f_monotone _ _ Y)
  termination_by S.card
  decreasing_by
    apply Finset.card_lt_card
    exact Y.ssubset_of_ne (by assumption)
  exact gfixL fBound (Finset.Subset.refl fBound) (hBound fBound)

/-- **Accessibility lemma**: Transport a relation through the fixpoint iteration.

Given a "split" of the fixpoint operator into `f₁ : Finset α → Z` and
`f₂ : Z → Finset α` (so the iteration operates on `f₂ ∘ f₁`), and a
transitive, reflexive relation `R` on `Z` that is preserved by each
iteration step, then `R` holds between the initial value and the fixpoint.

This is the key lemma for computational soundness: we instantiate `Z` with
distribution families, `R` with computational indistinguishability, and
each step corresponds to hiding one more key (which is indistinguishable
by IND-CPA security). -/
theorem Finset.greatestFixpoint_access {α : Type} [DecidableEq α] {Z : Type}
    (f₁ : Finset α → Z) (f₂ : Z → Finset α)
    (f_monotone : ∀ X Y, X ⊆ Y → f₂ (f₁ X) ⊆ f₂ (f₁ Y))
    (fBound : Z)
    (hBound : ∀ X, f₂ (f₁ X) ⊆ f₂ fBound)
    (R : Z → Z → Prop)
    (hTrans : ∀ {x y z}, R x y → R y z → R x z)
    (_hRefl : ∀ z, R z z)
    (hStep : ∀ x, f₂ (f₁ x) ⊆ x → R (f₁ x) (f₁ (f₂ (f₁ x))))
    (hSup : R fBound (f₁ (f₂ fBound))) :
    R fBound (f₁ (Finset.greatestFixpoint
      (fun x => f₂ (f₁ x)) f_monotone (f₂ fBound) hBound)) := by
  simp [Finset.greatestFixpoint]
  let rec gfixL (S : Finset α) (X : S ⊆ f₂ fBound) (Y : f₂ (f₁ S) ⊆ S)
      (hR : R fBound (f₁ S)) :
      R fBound (f₁ (Finset.greatestFixpoint.gfix
        (fun x => f₂ (f₁ x)) f_monotone (f₂ fBound) hBound S X Y)) := by
    rw [Finset.greatestFixpoint.gfix]
    split
    · exact hR
    · exact gfixL (f₂ (f₁ S)) (hBound S) (f_monotone _ _ Y)
        (hTrans hR (hStep S Y))
  termination_by S.card
  decreasing_by
    apply Finset.card_lt_card
    exact Y.ssubset_of_ne (by assumption)
  exact gfixL (f₂ fBound) (Finset.Subset.refl (f₂ fBound)) (hBound (f₂ fBound)) hSup

end CatCrypt.Crypto.Symbolic.Soundness
