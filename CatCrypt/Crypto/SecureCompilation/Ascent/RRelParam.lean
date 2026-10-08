/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRel
public import Transfer.Integrations.ParamRCompOk
public import Transfer.Hierarchy.ParamHierarchy

/-!
# The Kleisli relations of ParamTransfer as relational refinements

The relational refinement `RRel` of `CatCryptCore/Refinement/RRel.lean` has the two
Kleisli relations of ParamTransfer as instances. `RComp`
(`Integrations/ParamTripleTransfer.lean`) is `RRel` at the identity assertion map
and equal exception postconditions. `RCompOk` (`Integrations/ParamRCompOk.lean`) is
`RRel` from the total side to the failing side, at the embedding `⌜·⌝` of `.pure`
assertions, with the flipped value relation and the trivial exception postcondition
on the failing side.

`Param.rrel` packages `RRel γ RE p.R` between two monads as a `Param` at
`(map2a, map2a)`, given functions `M A → N A` and `N A' → M A'` that are
`RRel`-related to the identity at equality.

## Main definitions

* `Param.rrel`: `RRel` as a `Param .map2a .map2a (M A) (N A')`.

## Main results

* `rcomp_iff_rrel`: `RComp` is `RRel` at `AssnRel.id` and equality.
* `rcompOk_iff_rrel`: `RCompOk` is `RRel` at `AssnRel.purify`, flipped.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

universe u v w

namespace Transfer.Param

open Std.Do CatCrypt.Refinement

variable {M : Type u → Type v} {N : Type u → Type w} {ps : PostShape.{u}} {α α' : Type u}

/-- `RComp` is `RRel` at the identity assertion map and equal exception
    postconditions. -/
theorem rcomp_iff_rrel [WP M ps] {R : α → α' → Prop} {c : M α} {c' : M α'} :
    RComp (ps := ps) R c c' ↔ RRel (AssnRel.id ps) (· = ·) R c c' := by
  constructor
  · rintro h Q Q' hQ E _ rfl
    exact h Q Q' E hQ
  · intro h Q Q' E hQ
    exact @h Q Q' hQ E E rfl

/-- `RCompOk R c c'` is `RRel` from the total computation `c'` to the failing
    computation `c`, at the embedding `⌜·⌝` of `.pure` assertions, with the
    flipped value relation and the exception postcondition of `c` equal to
    `ExceptConds.true` (partial correctness). -/
theorem rcompOk_iff_rrel [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {c : M α} {c' : N α'} :
    RCompOk R c c' ↔
      RRel (AssnRel.purify ps) (fun _ E => E = ExceptConds.true) (fun a' a => R a a') c' c := by
  constructor
  · rintro h Q' Q hQ E' E rfl
    refine SPred.pure_elim' fun hwp => ?_
    refine (h (fun a' => (Q' a').down) (fun _ => hwp)).trans
      ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
    exact SPred.pure_elim' fun ⟨a', hr, hq⟩ => (SPred.pure_intro hq).trans (@hQ a' a hr)
  · intro h Q' hQ'
    exact (SPred.pure_intro (hQ' True.intro)).trans
      (@h (fun a' => ⌜Q' a'⌝) (fun a => ⌜∃ a', R a a' ∧ Q' a'⌝)
        (fun a' a hr => SPred.pure_mono fun hq => ⟨a', hr, hq⟩) ExceptConds.false
        ExceptConds.true rfl)

/-- `RRel γ RE p.R` between the monads `M` and `N` is a `Param` at
    `(map2a, map2a)`, given `φ : M A → N A` with `RRel γ RE Eq c (φ c)` and
    `ψ : N A' → M A'` with `RRel γ RE Eq (ψ c') c'`. The forward map is
    `p.fwd.map <$> φ c`, the backward map `p.bwd.map <$> ψ c'`. At `M = N`,
    `γ = AssnRel.id ps`, `RE = Eq` and `φ = ψ = id` this is `Param.rcomp`.

    `(map2a, map2a)` is the largest class reached. `Map2bHas` forward would need
    `RRel γ RE p.R c c' → p.fwd.map <$> φ c = c'`: `RRel` is a refinement order on
    the images under `wp`, so it determines `c'` up to its weakest precondition and
    not as a term, and neither `WPMonad` nor `AssnRel` makes `wp` injective. The
    backward direction fails in the same way. -/
def Param.rrel {M N : Type u → Type u} {ps ps' : PostShape.{u}} [Monad M] [WPMonad M ps]
    [Monad N] [WPMonad N ps'] (γ : AssnRel ps ps')
    (RE : ExceptConds ps → ExceptConds ps' → Prop) {A A' : Type u}
    (p : Param .map2a .map2a A A')
    (φ : M A → N A) (hφ : ∀ c, RRel γ RE (· = ·) c (φ c))
    (ψ : N A' → M A') (hψ : ∀ c', RRel γ RE (· = ·) (ψ c') c') :
    Param .map2a .map2a (M A) (N A') where
  R := RRel γ RE p.R
  fwd :=
    { map := fun c => p.fwd.map <$> φ c
      map_in_R := by
        rintro c _ rfl
        exact (hφ c).map_right p.fwd.map fun a _ h => by subst h; exact p.fwd.map_in_R a _ rfl }
  bwd :=
    { map := fun c' => p.bwd.map <$> ψ c'
      map_in_R := by
        rintro c' _ rfl
        exact (hψ c').map_left p.bwd.map fun a _ h => by subst h; exact p.bwd.map_in_R a _ rfl }

end Transfer.Param

end
