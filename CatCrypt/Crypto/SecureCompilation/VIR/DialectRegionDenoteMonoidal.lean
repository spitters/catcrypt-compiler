/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectRegionMonoidal
public import CatCryptCore.ForMathlib.CategoryTheory.KleisliOptionMonoidal

/-!
# The denotation functors of regions are strong braided monoidal

For each fuel, the denotation functor `Region.denoteFunctor fuel` from the symmetric monoidal
category `Region d` of `VIR/DialectRegionMonoidal.lean` to the Kleisli category of `Option`,
with its symmetric monoidal structure of `ForMathlib/CategoryTheory/KleisliOptionMonoidal.lean`,
is strong monoidal and braided. The unit isomorphism identifies `PUnit` with the valuations of
the empty list. The tensorator identifies a pair of valuations of `Γ` and `Δ` with a valuation
of `Γ ++ Δ`: its forward map is the append of valuations and its inverse the pair of pullbacks
along the two inclusions. Naturality of the tensorator is the denotation of the whiskers, and
the coherence conditions are the denotations of the associator, the unitors and the braiding.

## Main definitions

* `Region.denoteεIso` — the unit isomorphism `PUnit ≅ Valuation []`.
* `Region.denoteμIso` — the tensorator `Valuation Γ × Valuation Δ ≅ Valuation (Γ ++ Δ)`.
* `Region.denoteCoreMonoidal` — the strong monoidal structure of `Region.denoteFunctor fuel`.
* `Region.instBraidedDenoteFunctor` — `Region.denoteFunctor fuel` is a braided functor.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Valuation)
open MultiBlockLowering (hvAppend inlHom inrHom)
open FieldDialectBlockDescent (pullV)

namespace Region

open CategoryTheory MonoidalCategory

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
  [DialectDenoteM d Option] [CallDenote d]

/-- **The unit isomorphism** of the denotation functor: `PUnit` and the valuations of the empty
    list, each a single point. -/
def denoteεIso (fuel : Nat) :
    𝟙_ (KleisliCat Option) ≅ (denoteFunctor (d := d) fuel).obj (𝟙_ (Region d)) where
  hom := fun _ => some (HVector.nil : Valuation ([] : Ctxt d))
  inv := fun _ => some PUnit.unit
  hom_inv_id := funext fun _ => rfl
  inv_hom_id := funext fun V =>
    congrArg some (valuation_nil_eq (d := d) HVector.nil V)

/-- **The tensorator** of the denotation functor: a pair of valuations of `Γ` and `Δ` goes to
    their append, and a valuation of `Γ ++ Δ` to its pullbacks along the two inclusions. -/
def denoteμIso (fuel : Nat) (Γ Δ : Region d) :
    (denoteFunctor fuel).obj Γ ⊗ (denoteFunctor fuel).obj Δ ≅
      (denoteFunctor fuel).obj (Γ ⊗ Δ) where
  hom := fun (p : Valuation (Γ : Ctxt d) × Valuation (Δ : Ctxt d)) =>
    some (hvAppend p.1 p.2)
  inv := fun V =>
    some (pullV (inlHom (Δ : Ctxt d)) V, pullV (inrHom (Γ : Ctxt d)) V)
  hom_inv_id := funext fun p => by
    obtain ⟨a, b⟩ := p
    exact congrArg some (Prod.ext (pullV_inlHom a b) (pullV_inrHom a b) :
      ((pullV (inlHom (Δ : Ctxt d)) (hvAppend a b), pullV (inrHom (Γ : Ctxt d)) (hvAppend a b)) :
        Valuation (Γ : Ctxt d) × Valuation (Δ : Ctxt d)) = (a, b))
  inv_hom_id := funext fun V => congrArg some (hvAppend_split V)

/-- **The denotation functor is strong monoidal.** -/
def denoteCoreMonoidal (fuel : Nat) : (denoteFunctor (d := d) fuel).CoreMonoidal where
  εIso := denoteεIso fuel
  μIso := denoteμIso fuel
  μIso_hom_natural_left {X Y} f X' := funext fun p => by
    obtain ⟨a, b⟩ := p
    change ((den fuel f a).bind fun x => some (x, b)).bind
        (fun p : Valuation (Y : Ctxt d) × Valuation (X' : Ctxt d) => some (hvAppend p.1 p.2)) =
      den fuel (f ▷ X') (hvAppend a b)
    exact (Option.bind_assoc _ _ _).trans (den_whiskerRight fuel f X' a b).symm
  μIso_hom_natural_right {X Y} X' f := funext fun p => by
    obtain ⟨a, b⟩ := p
    change ((den fuel f b).bind fun y => some (a, y)).bind
        (fun p : Valuation (X' : Ctxt d) × Valuation (Y : Ctxt d) => some (hvAppend p.1 p.2)) =
      den fuel (X' ◁ f) (hvAppend a b)
    exact (Option.bind_assoc _ _ _).trans (den_whiskerLeft fuel X' f a b).symm
  associativity X Y Z := funext fun p => by
    obtain ⟨⟨a, b⟩, c⟩ := p
    exact den_associator_hom fuel X Y Z a b c
  left_unitality X := funext fun p => by
    obtain ⟨⟨⟩, a⟩ := p
    exact (den_leftUnitor_hom fuel X a).symm
  right_unitality X := funext fun p => by
    obtain ⟨a, ⟨⟩⟩ := p
    exact (den_rightUnitor_hom fuel X a HVector.nil).symm

/-- **The denotation functor is braided**: it sends the braiding of regions, the swap of the two
    parts of a valuation, to the swap of the two components of a pair. -/
instance instBraidedDenoteFunctor (fuel : Nat) : (denoteFunctor (d := d) fuel).Braided where
  toMonoidal := (denoteCoreMonoidal fuel).toMonoidal
  braided X Y := funext fun p => by
    obtain ⟨a, b⟩ := p
    exact den_braiding_hom fuel X Y a b

end Region

end CatCrypt.Crypto.SecureCompilation.VIR
