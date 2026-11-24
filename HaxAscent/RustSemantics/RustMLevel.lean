/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.WRPDouble
public import HaxLean.RuntimeM
public import HaxAscent.RustSemantics.TripleToFnCorresWP
public import CatCrypt.Crypto.SecureCompilation.Ascent.RustMSquareDouble

/-!
# `RustM` as a level of the double category of refinement squares

The `Std.WP` interpretation of `Aeneas.Std.RustM` (total correctness: a value satisfies the
postcondition, a failure the exception postcondition, divergence nothing) is exact at `pure`
and at `bind`, so `RustM` is a level `WRPDouble.Level` of the thin double category of
refinement squares. Beside it the specification level is `Id` with `Prop` assertions: a
specification of a hax function is a total function, and the weakest precondition of
`pure (f x)` at `Id` is the postcondition at `f x`.

In the two-level family `fam`, a square with the specification `pure ∘ f` on top and a
`RustM` program `p` at the bottom, whose vertical arrows have the identity concretization of
`Prop`, the exception map to `⊥` and return relations `Rin` and `Rout`, holds exactly when
from inputs related by `Rin` the program returns a value related by `Rout` to the value of
`f` (`sq_iff_forall_ok`). With `Rin` the equality under a guard `G` and `Rout` the equality,
the square is the guarded total triple `Triple (p x) True (fun r => r = f x) ⊥` of the hax
runtime and of Aeneas's specifications (`sq_iff_triple_guard`); `addM_w_sq` is the instance
at checked addition.

The function correspondence `Hax.Ascent.FnCorres` of the hax ascent is a statement about the
relational source semantics, which is no monad level; a square of `fam` whose bottom is the
`RustM` reading `toRustMS app e (ρ a)` gives it (`fnCorres_of_sq`). The squares of `fam` with
state-passing programs are the squares of the relational double category `MLevel C S` with
the program on top and the value map at the bottom (`sq_iff_mlevel_sq`); by determinism of
`RustM` and totality of the value map, they give the transposed relational square with the
specification on top (`mlevel_sq_spec_of_sq`), which constrains the `.ok` results only.

## Main definitions

* `instWPMonadExact`: the `Std.WP` interpretation of `RustM` is exact.
* `rustMLevel`, `specLevel`: `RustM` and `Id` as levels; `fam`: the two-level family.
* `specArrow`: the vertical arrow from the specification level to the `RustM` level with a
  return relation.

## Main results

* `sq_iff_refines_fam`: a square of `fam` is a family of refinements.
* `sq_iff_forall_ok`, `sq_iff_triple`, `sq_iff_triple_guard`: specification squares as
  total triples.
* `addM_w_sq`: checked addition refines `Hax.add` under its guard.
* `fnCorres_of_sq`: a square over the `RustM` reading gives the function correspondence.
* `sq_iff_mlevel_sq`, `mlevel_sq_spec_of_sq`: the squares of `fam` and the relational
  squares of `MLevel C S`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CatCrypt.Hax.RustSemantics.RustMLevel

open Aeneas.Std
open _root_.Std.WP Lean.Order
open CatCrypt.Refinement RefinementWP

/-- The `Std.WP` interpretation of `RustM` is exact at `pure` and at `bind`. -/
instance instWPMonadExact :
    WPMonadExact RustM.{u} (Pred := Prop) (EPosts := Error → Prop) where
  wp_pure_le _ _ _ := PartialOrder.rel_refl
  wp_bind_le x _ _ _ := by cases x <;> exact PartialOrder.rel_refl

/-- `RustM` as a level: `Prop` assertions, exception postconditions `Error → Prop`. -/
abbrev rustMLevel : WRPDouble.Level.{0, 0, 0, 0} where
  m := RustM
  Pred := Prop
  E := Error → Prop

/-- The specification level: `Id` with `Prop` assertions and no exceptions. -/
abbrev specLevel : WRPDouble.Level.{0, 0, 0, 0} where
  m := Id
  Pred := Prop
  E := EStack⟨⟩

/-- The two level indices: the specification and the `RustM` code. -/
inductive Side : Type where
  /-- The specification level `specLevel`. -/
  | spec
  /-- The code level `rustMLevel`. -/
  | code

/-- The two-level family: `Id` specifications and `RustM` code. -/
abbrev fam : Side → WRPDouble.Level.{0, 0, 0, 0}
  | .spec => specLevel
  | .code => rustMLevel

/-- A square of `fam` is a family of refinements (`WRPDouble.sq_iff_refines` at `fam`). -/
theorem sq_iff_refines_fam {i j : Side} {X Y X' Y' : Type} (pu : X → (fam i).m Y)
    (f : WRPDouble.VHom fam ⟨i, X⟩ ⟨j, X'⟩) (g : WRPDouble.VHom fam ⟨i, Y⟩ ⟨j, Y'⟩)
    (pw : X' → (fam j).m Y') :
    WRPDouble.Sq fam (.mk pu) f g (.mk pw) ↔
      f.γ = g.γ ∧ f.eps = g.eps ∧
        ∀ xc xa, Refines (f.R xc xa) f.γ f.eps (pw xc) (pu xa) g.R :=
  WRPDouble.sq_iff_refines fam pu f g pw

/-- The vertical arrow from the specification level at `X` to the `RustM` level at `X'`: the
identity concretization of `Prop`, the exception map to `⊥` (the code does not fail) and
the return relation `R`. -/
noncomputable def specArrow {X X' : Type} (R : X' → X → Prop) :
    WRPDouble.VHom fam ⟨.spec, X⟩ ⟨.code, X'⟩ where
  γ := Concretization.id
  sup _ := PartialOrder.rel_refl
  meet _ _ := PartialOrder.rel_refl
  bot := PartialOrder.rel_refl
  top := PartialOrder.rel_refl
  eps _ := bot
  R := R

/-- The specification program `pure ∘ f` as a horizontal arrow of the specification level. -/
abbrev specH {X Y : Type} (f : X → Y) : WRPDouble.HHom fam ⟨.spec, X⟩ ⟨.spec, Y⟩ :=
  .mk fun x => (pure (f x) : Id Y)

/-- A `RustM` program as a horizontal arrow of the code level. -/
abbrev codeH {X Y : Type} (p : X → RustM Y) : WRPDouble.HHom fam ⟨.code, X⟩ ⟨.code, Y⟩ :=
  .mk p

/-- **A specification square is total correctness.** The square with top `pure ∘ f` at the
specification level, bottom `p` at the `RustM` level and sides `specArrow Rin`,
`specArrow Rout` holds exactly when, from inputs related by `Rin`, `p` returns a value related
by `Rout` to the value of `f`. -/
theorem sq_iff_forall_ok {X Y X' Y' : Type} (f : X → Y) (p : X' → RustM Y')
    (Rin : X' → X → Prop) (Rout : Y' → Y → Prop) :
    WRPDouble.Sq fam (specH f) (specArrow Rin) (specArrow Rout) (codeH p) ↔
      ∀ xc xa, Rin xc xa → ∃ r, p xc = .ok r ∧ Rout r (f xa) := by
  rw [sq_iff_refines_fam]
  refine (and_iff_right rfl).trans ((and_iff_right rfl).trans ?_)
  refine forall_congr' fun xc => forall_congr' fun xa => ?_
  change Refines (Rin xc xa) Concretization.id (fun _ => bot) (p xc) (pure (f xa) : Id Y)
    Rout ↔ _
  constructor
  · intro h hR
    have h' := wrp_transport h (fun y => y = f xa) bot
    simp only [meet_prop_eq_and, WPMonadExact.wp_pure_eq, Concretization.id] at h'
    obtain ⟨r, hr, hpost⟩ :=
      stdWP_triple_iff_exists_ok.1 ⟨fun _ => h' ⟨hR, trivial⟩⟩ trivial
    simp only [Concretization.post, iSup_prop_eq_exists, meet_prop_eq_and] at hpost
    grind
  · intro h
    refine wrp_intro fun Qa Ea => ?_
    simp only [meet_prop_eq_and, WPMonadExact.wp_pure_eq, Concretization.id]
    rintro ⟨hR, hQ⟩
    obtain ⟨r, hr, hRo⟩ := h hR
    rw [hr]
    change Concretization.id.post Rout Qa r
    simp only [Concretization.post, Concretization.id, iSup_prop_eq_exists, meet_prop_eq_and]
    grind

/-- A specification square is the family of total triples of `p` with precondition `Rin`. -/
theorem sq_iff_triple {X Y X' Y' : Type} (f : X → Y) (p : X' → RustM Y')
    (Rin : X' → X → Prop) (Rout : Y' → Y → Prop) :
    WRPDouble.Sq fam (specH f) (specArrow Rin) (specArrow Rout) (codeH p) ↔
      ∀ xc xa, Triple (p xc) (Rin xc xa) (fun r => Rout r (f xa)) bot := by
  rw [sq_iff_forall_ok]
  simp only [stdWP_triple_iff_exists_ok]

/-- **A guarded triple is a square.** The guarded total triples of `p` against `f` are the
square with top `pure ∘ f`, bottom `p`, left return relation the equality under the guard
`G` and right return relation the equality: `p` refines `f` under `G`. -/
theorem sq_iff_triple_guard {X Y : Type} (f : X → Y) (p : X → RustM Y) (G : X → Prop) :
    (∀ x, G x → Triple (p x) True (fun r => r = f x) bot) ↔
      WRPDouble.Sq fam (specH f) (specArrow fun xc xa => xc = xa ∧ G xa) (specArrow Eq)
        (codeH p) := by
  rw [sq_iff_forall_ok]
  simp only [stdWP_triple_iff_exists_ok]
  constructor
  · rintro h xc xa ⟨rfl, hG⟩
    exact h xc hG trivial
  · intro h x hG _
    exact h x x ⟨rfl, hG⟩

/-- Checked addition at width `w` refines `Hax.add` under its guard, no overflow. -/
theorem addM_w_sq (w : Nat) :
    WRPDouble.Sq fam (specH fun ab : Int × Int => _root_.Hax.add ab.1 ab.2)
      (specArrow fun xc xa => xc = xa ∧ (0 ≤ xa.1 + xa.2 ∧ xa.1 + xa.2 < 2 ^ w))
      (specArrow Eq) (codeH fun ab => _root_.Hax.addM_w w ab.1 ab.2) := by
  refine (sq_iff_triple_guard _ _ _).1 fun ab hG => ?_
  have h := stdWP_triple_iff_exists_ok.1 (_root_.Hax.addM_w_spec w ab.1 ab.2) hG
  exact stdWP_triple_iff_exists_ok.2 fun _ => h

section Ascent

variable {bi : _root_.Hax.Builtins} {A β : Type} [_root_.Hax.Ascent.HaxEnc β]
  {e : _root_.Hax.ImpExpr} {entry : A → _root_.Hax.Env} {G : A → Prop} {f : A → β}
  {app : String → List AVal → RustM AVal}

/-- **The hax ascent from a square.** A square of `fam` with the specification `f` on top,
the `RustM` reading of `e` at the bottom, the equality under the guard `G` on the left and
the encoding relation on the right gives the function correspondence of `e` with `f`. -/
theorem fnCorres_of_sq (happ : AppOk bi app) (ρ : A → AEnv)
    (hρ : ∀ a, G a → entry a = encEnv (ρ a))
    (h : WRPDouble.Sq fam (specH f)
      (specArrow fun xc xa => xc = xa ∧ G xa)
      (specArrow fun (r : AVal × AEnv) b => r.1.toValue = _root_.Hax.Ascent.HaxEnc.enc b)
      (codeH fun a => toRustMS app e (ρ a))) :
    _root_.Hax.Ascent.FnCorres bi e entry G f := by
  refine fnCorres_of_toRustMS_tripleWP happ ρ hρ fun a hG => ?_
  have h' := (sq_iff_forall_ok _ _ _ _).1 h a a ⟨rfl, hG⟩
  exact stdWP_triple_iff_exists_ok.2 fun _ => h'

end Ascent

section MLevel

open CategoryTheory ThinDoubleCategory _root_.Hax.Ascent.RustM

variable {C S A B : Type}

/-- **Specification squares are relational squares.** For a state-passing continuation `f`
and a value map `W`, the square of `fam` with `W` on top and `f` at the bottom is the square
of `MLevel C S` with `f` on top and `W` at the bottom, with the same sides. -/
theorem sq_iff_mlevel_sq (k : A → C → RustM (B × C)) (R : A × C → A × S → Prop)
    (R' : B × C → B × S → Prop) (W : S → A → B) :
    WRPDouble.Sq fam (specH fun x : A × S => (W x.2 x.1, x.2)) (specArrow R) (specArrow R')
        (codeH fun x : A × C => k x.1 x.2) ↔
      Sq (C := MLevel C S) (a := .conc A) (b := .conc B) (c := .abs A) (d := .abs B)
        k R R' W := by
  rw [sq_iff_forall_ok, MLevel.sq_conc_iff]
  grind only [Prod.exists]

/-- **The transposed relational square.** A square of `fam` with the value map `W` on top and
the continuation `k` at the bottom gives the square of `MLevel C S` with `W` on top, `k` at
the bottom and the converses of the sides: every `.ok` result of `k` is related to the value
of `W`. -/
theorem mlevel_sq_spec_of_sq (k : A → C → RustM (B × C)) (R : A × C → A × S → Prop)
    (R' : B × C → B × S → Prop) (W : S → A → B)
    (h : WRPDouble.Sq fam (specH fun x : A × S => (W x.2 x.1, x.2)) (specArrow R)
        (specArrow R') (codeH fun x : A × C => k x.1 x.2)) :
    Sq (C := MLevel C S) (a := .abs A) (b := .abs B) (c := .conc A) (d := .conc B)
      W (fun y x => R x y) (fun y x => R' x y) k := by
  have h' := (MLevel.sq_conc_iff k R R' W).1 ((sq_iff_mlevel_sq k R R' W).1 h)
  intro y x x' hR hk
  obtain ⟨z, hz, hR'⟩ := h' x y.1 y.2 hR
  have hzx : z = x' := by
    have hok := hz.symm.trans (show k x.1 x.2 = .ok x' from hk)
    cases hok
    rfl
  exact ⟨_, rfl, hzx ▸ hR'⟩

end MLevel

end CatCrypt.Hax.RustSemantics.RustMLevel
