/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Core

/-!
# Assertions lifted along a projection of states

A machine state `σ` with locations `L` often contains a component `τ` with locations `L'`
(for example its byte memory), reached by a projection `p : σ → τ`, whose locations embed
into those of `σ` by `e : L' → L`. The pair is compatible (`ProjCompat p e`) when states that
agree on `e '' S` project to states that agree on `S`. Under this condition an assertion `P`
over `τ` lifts to the assertion `SAssert.comap p e hpe P` over `σ`, with footprint `e '' P.fp`
and predicate `P.holds ∘ p`.

For an injective `e` the lift commutes with `∗`, `bigSep` and pure assertions, preserves
entailment, and carries a triple of a transformer `g` of `τ` to a triple of every transformer
`f` of `σ` with `p ∘ f = g ∘ p`.

`Footprinted.ofGet get` is the footprint structure of a state that is read location by
location through `get : σ → (l : L) → V l`; the values of different locations may have
different types.

## Main definitions

* `Footprinted.ofGet`: agreement of states read location by location.
* `ProjCompat`: compatibility of a projection of states with an embedding of locations.
* `SAssert.comap`: the lift of an assertion along a compatible projection.

## Main results

* `SAssert.ext`: assertions with equal footprints and predicates are equal.
* `SAssert.comap_entails`: the lift preserves entailment.
* `SAssert.comap_sep`, `SAssert.comap_pure`, `SAssert.comap_emp`, `SAssert.comap_bigSep`:
  for an injective embedding the lift commutes with the connectives.
* `Triple.comap`: a triple of `g` lifts to a triple of every `f` with `p ∘ f = g ∘ p`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

universe u v w u' v'

open Footprinted

/-- The footprint structure of a state read location by location through `get`: two states
    agree on `S` when `get` returns equal values at every location of `S`. -/
@[instance_reducible] def Footprinted.ofGet {σ : Type u} {L : Type v} {V : L → Type w}
    (get : σ → (l : L) → V l) : Footprinted σ L where
  AgreeOn S s t := ∀ l ∈ S, get s l = get t l
  agreeOn_refl _ _ _ _ := rfl
  agreeOn_symm h l hl := (h l hl).symm
  agreeOn_trans h h' l hl := (h l hl).trans (h' l hl)
  agreeOn_anti hST h l hl := h l (hST hl)

section Lift

variable {σ : Type u} {L : Type v} [Footprinted σ L]
variable {τ : Type u'} {L' : Type v'} [Footprinted τ L']

/-- The projection `p` and the embedding of locations `e` are compatible: states that agree
    on `e '' S` project to states that agree on `S`. -/
def ProjCompat (p : σ → τ) (e : L' → L) : Prop :=
  ∀ (S : Set L') (s t : σ), AgreeOn (e '' S) s t → AgreeOn S (p s) (p t)

namespace SAssert

/-- Two assertions with equal footprints and equal predicates are equal. -/
theorem ext {P Q : SAssert σ L} (hfp : P.fp = Q.fp) (hholds : P.holds = Q.holds) : P = Q := by
  cases P
  cases Q
  cases hfp
  cases hholds
  rfl

variable (p : σ → τ) (e : L' → L) (hpe : ProjCompat p e)

/-- The lift of an assertion over `τ` along the projection `p`: footprint `e '' P.fp`,
    predicate `P.holds ∘ p`. -/
def comap (P : SAssert τ L') : SAssert σ L where
  fp := e '' P.fp
  holds s := P.holds (p s)
  supp s t h hs := P.supp (p s) (p t) (hpe P.fp s t h) hs

@[simp] theorem fp_comap (P : SAssert τ L') : (comap p e hpe P).fp = e '' P.fp := rfl

@[simp] theorem holds_comap (P : SAssert τ L') (s : σ) :
    (comap p e hpe P).holds s ↔ P.holds (p s) := Iff.rfl

variable {p e hpe}

/-- The lift preserves entailment. -/
theorem comap_entails {P Q : SAssert τ L'} (h : P ⊢ₛ Q) : comap p e hpe P ⊢ₛ comap p e hpe Q :=
  fun s hs => ⟨(h (p s) hs).1, Set.image_mono (h (p s) hs).2⟩

/-- For an injective embedding of locations the lift commutes with `∗`. -/
theorem comap_sep (he : Function.Injective e) (P Q : SAssert τ L') :
    comap p e hpe (P ∗ Q) = comap p e hpe P ∗ comap p e hpe Q :=
  ext (Set.image_union e _ _) <| funext fun s =>
    propext (by simp only [holds_comap, holds_sep, fp_comap, Set.disjoint_image_iff he])

/-- The lift of a pure assertion is the pure assertion. -/
theorem comap_pure (φ : Prop) : comap p e hpe (⌜φ⌝ : SAssert τ L') = ⌜φ⌝ :=
  ext (Set.image_empty e) rfl

theorem comap_emp : comap p e hpe (emp : SAssert τ L') = emp := comap_pure True

/-- For an injective embedding of locations the lift commutes with `bigSep`. -/
theorem comap_bigSep (he : Function.Injective e) (l : List (SAssert τ L')) :
    comap p e hpe (bigSep l) = bigSep (l.map (comap p e hpe)) := by
  induction l with
  | nil => exact comap_emp
  | cons P l ih => rw [bigSep_cons, comap_sep he, ih, List.map_cons, bigSep_cons]

end SAssert

/-- A triple of a transformer `g` of the component lifts to a triple of every transformer `f`
    of the whole state that commutes with the projection. -/
theorem Triple.comap {p : σ → τ} {e : L' → L} {hpe : ProjCompat p e} {P Q : SAssert τ L'}
    {f : σ → σ} {g : τ → τ} (hfg : ∀ s, p (f s) = g (p s)) (h : Triple P g Q) :
    Triple (SAssert.comap p e hpe P) f (SAssert.comap p e hpe Q) := fun s hs => by
  show Q.holds (p (f s))
  rw [hfg]
  exact h (p s) hs

end Lift

end CatCrypt.Crypto.SecureCompilation.SepLogic
