/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectRegionMonoidal
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectRegionFunctor

/-!
# The action of a morphism of dialects on regions is strong monoidal

For a morphism `f : a ⟶ b` of `Dial`, the functor `Region.mapFunctor f` from `Region a.dia` to
`Region b.dia` is a braided strong monoidal functor for the symmetric monoidal structures of
`VIR/DialectRegionMonoidal.lean`. The unit map is the identity of the empty list, and the
tensorator of `Γ` and `Δ` is the renaming isomorphism along `List.map_append`, from
`Γ.map m ++ Δ.map m` to `(Γ ++ Δ).map m`.

The transport `transArgs` of valuations commutes with append up to the renaming along
`List.map_append` (`Dial.Hom.transArgs_hvAppend`). Every valuation of a mapped type list is a
transport (`Dial.Hom.transArgs_surjective`), and the action of `f` on a morphism denotes at a
transported valuation the transport of the denotation (`Region.den_mapHom`). Each law of a
monoidal functor is an equality of morphisms of `Region b.dia`, proved by `Region.hom_ext_den` at
a valuation split by `Region.exists_hvAppend` into transported parts.

## Main definitions

* `Region.mapμIso` — the tensorator of `Region.mapFunctor f`.
* `Region.mapCoreMonoidal` — the strong monoidal structure of `Region.mapFunctor f`.
* `Region.mapMonoidal`, `Region.mapBraided` — the monoidal and braided functor structures.

## Main results

* `Dial.Hom.transArgs_hvAppend` — the transport of an appended valuation is the append of the
  transports, along `List.map_append`.
* `Region.den_mapHom` — the action on a morphism denotes the transport of its denotation.
* `Region.den_mapμIso_hom` — the tensorator denotes the transport of the append.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open FieldDialectBlockDescent (pullV)
open BlockLoweringCPS (castHom)
open BlockLoweringExtend (transArgs)
open MultiBlockLowering (hvAppend)
open DialectCategory
open CategoryTheory MonoidalCategory

/-! ## 1. The transport of appended valuations -/

namespace Dial

/-- The pullback along the renaming by an equality of contexts is the cast along the
    equality. -/
theorem pullV_castHom {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {A B : Ctxt d} (h : A = B) (V : Valuation B) :
    pullV (castHom h) V = (h ▸ V : Valuation A) := by
  subst h
  exact FieldDialectBlockDescent.pullV_id V

/-- The pullbacks along the renamings by an equality of contexts and by its inverse are
    mutually inverse. -/
theorem pullV_castHom_castHom {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {A B : Ctxt d} (h : A = B) (V : Valuation A) :
    pullV (castHom h) (pullV (castHom h.symm) V) = V := by
  subst h
  rw [pullV_castHom, pullV_castHom]

namespace Hom

variable {a b : Dial}

/-- **The transport of an appended valuation is the append of the transports**, read along
    `List.map_append`. -/
theorem transArgs_hvAppend (f : Hom a b) : {X Y : Ctxt a.dia} → (A : Valuation X) →
    (B : Valuation Y) →
    pullV (castHom (List.map_append (f := f.lower.mapTy) (l₁ := X) (l₂ := Y)).symm)
        (transArgs f.lower.mapTy f.transTy (hvAppend A B)) =
      hvAppend (transArgs f.lower.mapTy f.transTy A) (transArgs f.lower.mapTy f.transTy B)
  | [], _, .nil, B => pullV_castHom _ _
  | t :: X, Y, .cons x A, B => by
      show pullV (castHom (List.map_append (f := f.lower.mapTy) (l₁ := t :: X) (l₂ := Y)).symm)
          (Valuation.extend (transArgs f.lower.mapTy f.transTy (hvAppend A B)) (f.transTy x)) =
        Valuation.extend (hvAppend (transArgs f.lower.mapTy f.transTy A)
          (transArgs f.lower.mapTy f.transTy B)) (f.transTy x)
      refine (pullV_castHom_extend rfl
        (List.map_append (f := f.lower.mapTy) (l₁ := X) (l₂ := Y)).symm _ _ _).trans ?_
      exact congrArg (fun W => Valuation.extend W (f.transTy x)) (transArgs_hvAppend f A B)

/-- The append of two transports, read along `List.map_append`, is the transport of the
    append. -/
theorem hvAppend_transArgs (f : Hom a b) {X Y : Ctxt a.dia} (A : Valuation X)
    (B : Valuation Y) :
    pullV (castHom (List.map_append (f := f.lower.mapTy) (l₁ := X) (l₂ := Y)))
        (hvAppend (transArgs f.lower.mapTy f.transTy A) (transArgs f.lower.mapTy f.transTy B)) =
      transArgs f.lower.mapTy f.transTy (hvAppend A B) := by
  rw [← transArgs_hvAppend f A B]
  exact pullV_castHom_castHom _ _

end Hom

end Dial

/-! ## 2. The action on morphisms at denotations, and the tensorator -/

namespace Region

variable {a b : Dial}

/-- **The action of a morphism of `Dial` on a morphism of regions denotes the transport of its
    denotation** at a transported valuation. -/
theorem den_mapHom (f : Dial.Hom a b) (fuel : Nat) {Γ ts : Region a.dia} (g : Γ ⟶ ts)
    (V : Valuation (Γ : Ctxt a.dia)) :
    den fuel ((mapFunctor f).map g) (transArgs f.lower.mapTy f.transTy V) =
      (den fuel g V).map (transArgs f.lower.mapTy f.transTy) := by
  induction g using Quot.inductionOn with
  | _ p => exact f.denote_mapProg fuel p V

/-- **The tensorator of the action of a morphism of `Dial`**: the renaming isomorphism along
    `List.map_append`. -/
def mapμIso (f : Dial.Hom a b) (X Y : Region a.dia) :
    (mapFunctor f).obj X ⊗ (mapFunctor f).obj Y ≅ (mapFunctor f).obj (X ⊗ Y) :=
  renIso (castHom (List.map_append (f := f.lower.mapTy) (l₁ := (X : Ctxt a.dia))
      (l₂ := (Y : Ctxt a.dia))))
    (castHom (List.map_append (f := f.lower.mapTy) (l₁ := (X : Ctxt a.dia))
      (l₂ := (Y : Ctxt a.dia))).symm)
    (fun V => Dial.pullV_castHom_castHom _ V) (fun W => Dial.pullV_castHom_castHom _ W)

/-- The tensorator denotes the transport of the append of two valuations. -/
theorem den_mapμIso_hom (f : Dial.Hom a b) (fuel : Nat) (X Y : Region a.dia)
    (A : Valuation (X : Ctxt a.dia)) (B : Valuation (Y : Ctxt a.dia)) :
    den fuel (mapμIso f X Y).hom
        (hvAppend (transArgs f.lower.mapTy f.transTy A) (transArgs f.lower.mapTy f.transTy B)) =
      some (transArgs f.lower.mapTy f.transTy (hvAppend A B)) :=
  (den_ren fuel _ _).trans (congrArg some (f.hvAppend_transArgs A B))

section Total

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
  [DialectDenoteM d Option] [CallDenote d]

/-- A composite whose first morphism denotes a value denotes the second morphism at it. -/
theorem den_comp_of_eq (fuel : Nat) {Γ ts us : Region d} {g : Γ ⟶ ts} (h : ts ⟶ us)
    {V : Valuation (Γ : Ctxt d)} {W : Valuation (ts : Ctxt d)} (hg : den fuel g V = some W) :
    den fuel (g ≫ h) V = den fuel h W :=
  (den_comp fuel g h V).trans (congrArg (· >>= den fuel h) hg)

/-- The right whisker of a morphism that denotes a value denotes the append of the value. -/
theorem den_whiskerRight_of_eq (fuel : Nat) {Γ ts : Region d} {g : Γ ⟶ ts} (Δ : Region d)
    {A : Valuation (Γ : Ctxt d)} {W : Valuation (ts : Ctxt d)} (B : Valuation (Δ : Ctxt d))
    (hg : den fuel g A = some W) : den fuel (g ▷ Δ) (hvAppend A B) = some (hvAppend W B) :=
  (den_whiskerRight fuel g Δ A B).trans (congrArg (· >>= fun r => some (hvAppend r B)) hg)

/-- The left whisker of a morphism that denotes a value denotes the append of the value. -/
theorem den_whiskerLeft_of_eq (fuel : Nat) (Γ : Region d) {Δ us : Region d} {g : Δ ⟶ us}
    (A : Valuation (Γ : Ctxt d)) {B : Valuation (Δ : Ctxt d)} {W : Valuation (us : Ctxt d)}
    (hg : den fuel g B = some W) : den fuel (Γ ◁ g) (hvAppend A B) = some (hvAppend A W) :=
  (den_whiskerLeft fuel Γ g A B).trans (congrArg (· >>= fun r => some (hvAppend A r)) hg)

end Total

/-- The action on a morphism that denotes a value denotes the transport of the value. -/
theorem den_mapHom_of_eq (f : Dial.Hom a b) (fuel : Nat) {Γ ts : Region a.dia} {g : Γ ⟶ ts}
    {V : Valuation (Γ : Ctxt a.dia)} {W : Valuation (ts : Ctxt a.dia)}
    (hg : den fuel g V = some W) :
    den fuel ((mapFunctor f).map g) (transArgs f.lower.mapTy f.transTy V) =
      some (transArgs f.lower.mapTy f.transTy W) :=
  (den_mapHom f fuel g V).trans (congrArg (Option.map _) hg)

/-! ## 3. The strong monoidal structure -/

/-- **The action of a morphism of `Dial` on regions is strong monoidal.** -/
def mapCoreMonoidal (f : Dial.Hom a b) : (mapFunctor f).CoreMonoidal where
  εIso := Iso.refl _
  μIso := mapμIso f
  μIso_hom_natural_left {X Y} g X' := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := ((mapFunctor f).obj X : Ctxt b.dia))
      (ys := ((mapFunctor f).obj X' : Ctxt b.dia)) V
    obtain ⟨A, rfl⟩ := f.transArgs_surjective X A
    obtain ⟨B, rfl⟩ := f.transArgs_surjective X' B
    refine (den_comp fuel _ _ _).trans ?_
    refine (congrArg (· >>= _) (den_whiskerRight fuel ((mapFunctor f).map g)
      ((mapFunctor f).obj X') (transArgs f.lower.mapTy f.transTy A)
      (transArgs f.lower.mapTy f.transTy B))).trans ?_
    refine (congrArg (fun o => (o >>= fun r => some (hvAppend r
      (transArgs f.lower.mapTy f.transTy B))) >>= _) (den_mapHom f fuel g A)).trans ?_
    refine Eq.trans ?_ (den_comp fuel _ _ _).symm
    refine Eq.trans ?_ (congrArg (· >>= _) (den_mapμIso_hom f fuel X X' A B)).symm
    refine Eq.trans ?_ (den_mapHom f fuel (g ▷ X') (hvAppend A B)).symm
    refine Eq.trans ?_ (congrArg (Option.map _) (den_whiskerRight fuel g X' A B)).symm
    cases den fuel g A with
    | none => rfl
    | some r => exact den_mapμIso_hom f fuel Y X' r B
  μIso_hom_natural_right {X Y} X' g := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := ((mapFunctor f).obj X' : Ctxt b.dia))
      (ys := ((mapFunctor f).obj X : Ctxt b.dia)) V
    obtain ⟨A, rfl⟩ := f.transArgs_surjective X' A
    obtain ⟨B, rfl⟩ := f.transArgs_surjective X B
    refine (den_comp fuel _ _ _).trans ?_
    refine (congrArg (· >>= _) (den_whiskerLeft fuel ((mapFunctor f).obj X')
      ((mapFunctor f).map g) (transArgs f.lower.mapTy f.transTy A)
      (transArgs f.lower.mapTy f.transTy B))).trans ?_
    refine (congrArg (fun o => (o >>= fun r => some (hvAppend
      (transArgs f.lower.mapTy f.transTy A) r)) >>= _) (den_mapHom f fuel g B)).trans ?_
    refine Eq.trans ?_ (den_comp fuel _ _ _).symm
    refine Eq.trans ?_ (congrArg (· >>= _) (den_mapμIso_hom f fuel X' X A B)).symm
    refine Eq.trans ?_ (den_mapHom f fuel (X' ◁ g) (hvAppend A B)).symm
    refine Eq.trans ?_ (congrArg (Option.map _) (den_whiskerLeft fuel X' g A B)).symm
    cases den fuel g B with
    | none => rfl
    | some r => exact den_mapμIso_hom f fuel X' Y A r
  associativity X Y Z := hom_ext_den fun fuel V => by
    obtain ⟨AB, C, rfl⟩ := exists_hvAppend
      (xs := ((mapFunctor f).obj X ⊗ (mapFunctor f).obj Y : Region b.dia))
      (ys := ((mapFunctor f).obj Z : Ctxt b.dia)) V
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := ((mapFunctor f).obj X : Ctxt b.dia))
      (ys := ((mapFunctor f).obj Y : Ctxt b.dia)) AB
    obtain ⟨A, rfl⟩ := f.transArgs_surjective X A
    obtain ⟨B, rfl⟩ := f.transArgs_surjective Y B
    obtain ⟨C, rfl⟩ := f.transArgs_surjective Z C
    refine (den_comp_of_eq fuel _ (den_whiskerRight_of_eq fuel ((mapFunctor f).obj Z)
      (transArgs f.lower.mapTy f.transTy C) (den_mapμIso_hom f fuel X Y A B))).trans ?_
    refine (den_comp_of_eq fuel _ (den_mapμIso_hom f fuel (X ⊗ Y) Z (hvAppend A B) C)).trans ?_
    refine (den_mapHom_of_eq f fuel (den_associator_hom fuel X Y Z A B C)).trans ?_
    refine Eq.symm ((den_comp_of_eq fuel _ (den_associator_hom fuel ((mapFunctor f).obj X)
      ((mapFunctor f).obj Y) ((mapFunctor f).obj Z) (transArgs f.lower.mapTy f.transTy A)
      (transArgs f.lower.mapTy f.transTy B) (transArgs f.lower.mapTy f.transTy C))).trans ?_)
    refine (den_comp_of_eq fuel _ (den_whiskerLeft_of_eq fuel ((mapFunctor f).obj X)
      (transArgs f.lower.mapTy f.transTy A) (den_mapμIso_hom f fuel Y Z B C))).trans ?_
    exact den_mapμIso_hom f fuel X (Y ⊗ Z) A (hvAppend B C)
  left_unitality X := hom_ext_den fun fuel V => by
    obtain ⟨A, rfl⟩ := f.transArgs_surjective X V
    refine (den_leftUnitor_hom fuel ((mapFunctor f).obj X) _).trans ?_
    refine Eq.symm ((den_comp_of_eq fuel _ (den_whiskerRight_of_eq fuel
      ((mapFunctor f).obj X) (W := (HVector.nil : Valuation ([] : Ctxt b.dia)))
      (A := (HVector.nil : Valuation ([] : Ctxt b.dia)))
      (transArgs f.lower.mapTy f.transTy A) (den_id fuel _ _))).trans ?_)
    refine (den_comp_of_eq fuel _ (den_mapμIso_hom f fuel (𝟙_ (Region a.dia)) X
      (HVector.nil : Valuation ([] : Ctxt a.dia)) A)).trans ?_
    exact den_mapHom_of_eq f fuel (den_leftUnitor_hom fuel X _)
  right_unitality X := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := ((mapFunctor f).obj X : Ctxt b.dia))
      (ys := ([] : Ctxt b.dia)) V
    cases B
    obtain ⟨A, rfl⟩ := f.transArgs_surjective X A
    refine (den_rightUnitor_hom fuel ((mapFunctor f).obj X) _ _).trans ?_
    refine Eq.symm ((den_comp_of_eq fuel _ (den_whiskerLeft_of_eq fuel
      ((mapFunctor f).obj X) (transArgs f.lower.mapTy f.transTy A)
      (W := (HVector.nil : Valuation ([] : Ctxt b.dia)))
      (B := (HVector.nil : Valuation ([] : Ctxt b.dia))) (den_id fuel _ _))).trans ?_)
    refine (den_comp_of_eq fuel _ (den_mapμIso_hom f fuel X (𝟙_ (Region a.dia)) A
      (HVector.nil : Valuation ([] : Ctxt a.dia)))).trans ?_
    exact den_mapHom_of_eq f fuel (den_rightUnitor_hom fuel X A _)

/-- **The monoidal functor structure** of the action of a morphism of `Dial` on regions. -/
instance mapMonoidal (f : Dial.Hom a b) : (mapFunctor f).Monoidal :=
  (mapCoreMonoidal f).toMonoidal

/-- **The braided functor structure** of the action of a morphism of `Dial` on regions: the
    action carries the swap of two type lists to the swap of their images. -/
instance mapBraided (f : Dial.Hom a b) : (mapFunctor f).Braided where
  __ := mapMonoidal f
  braided X Y := hom_ext_den fun fuel V => by
    obtain ⟨A, B, rfl⟩ := exists_hvAppend (xs := ((mapFunctor f).obj X : Ctxt b.dia))
      (ys := ((mapFunctor f).obj Y : Ctxt b.dia)) V
    obtain ⟨A, rfl⟩ := f.transArgs_surjective X A
    obtain ⟨B, rfl⟩ := f.transArgs_surjective Y B
    change den fuel ((mapμIso f X Y).hom ≫ (mapFunctor f).map (β_ X Y).hom) _ =
      den fuel ((β_ ((mapFunctor f).obj X) ((mapFunctor f).obj Y)).hom ≫ (mapμIso f Y X).hom) _
    refine (den_comp_of_eq fuel _ (den_mapμIso_hom f fuel X Y A B)).trans ?_
    refine (den_mapHom_of_eq f fuel (den_braiding_hom fuel X Y A B)).trans ?_
    refine Eq.symm ((den_comp_of_eq fuel _ (den_braiding_hom fuel ((mapFunctor f).obj X)
      ((mapFunctor f).obj Y) (transArgs f.lower.mapTy f.transTy A)
      (transArgs f.lower.mapTy f.transTy B))).trans ?_)
    exact den_mapμIso_hom f fuel Y X B A

end Region

end CatCrypt.Crypto.SecureCompilation.VIR
