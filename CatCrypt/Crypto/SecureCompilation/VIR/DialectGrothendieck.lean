/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.CategoryTheory.GrothendieckCocartesian
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectRegionFunctor
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses

/-!
# Regions over dialects as an opfibration

The total category `Grothendieck Dial.regionFunctor` has as objects the pairs of a dialect of
`Dial` and a type list of it, and as morphisms from `(a, Γ)` to `(b, Δ)` the pairs of a
morphism `L : a ⟶ b` of `Dial` and a class of programs of `b` from `Γ.map L.lower.mapTy` to
`Δ`. The forgetful functor to `Dial` is a Grothendieck opfibration: the morphism
`x.toTransport L`, with base component `L` and identity fibre component, is strongly
co-Cartesian over `L` (`Dial.G8_OPFIB`).

A program `p` of `x.base` over the context `x.fiber` and a morphism `L` give the morphism
`Dial.loweredHom x L p` of the total category, with base component `L` and fibre component
the class of `L.mapProg p`. It factors through the lift `x.toTransport L` by the vertical
morphism `Dial.liftVertical x L p`, whose fibre component is the class of `L.mapProg p`
(`Dial.lift_factor`), and every morphism over the identity through which it factors is that
one (`Dial.lift_factor_unique`).

## What each statement uses

* The simulation square `Dial.lift_cert` uses the functor `Dial.regionFunctor` only: it is
  `Dial.Hom.denote_mapProg` read through `Region.denoteFunctor` at the action
  `Dial.regionFunctor.map f` of a morphism on a fibre. The co-Cartesian property is not used.
* `Dial.G8_OPFIB`, the cofibred instance and `Dial.lift_factor` use strictness of the functor:
  they hold for every functor into `Cat`.
* `Dial.lift_factor_unique` uses the co-Cartesian property. It states uniqueness of the
  factorisation and gives no simulation statement.
* The certificate `Dial.catToJasminStepCert` of the pipeline's lowering step uses
  `Dial.lift_cert` at `Dial.catToJasmin`, the agreement `Dial.mapStep_catToJasmin` of the
  partial lowering with the action of the morphism on the class of the restricted program,
  and `DialectRestrict.denote_restrictNF?`, by which the restricted program denotes as the
  program. It does not use the co-Cartesian property.

## Main definitions

* `Dial.loweredHom` — the morphism of the total category given by a lowered program.
* `Dial.liftVertical` — the vertical morphism through which it factors.
* `Dial.Hom.ForwardSim` — the forward-simulation statement of a morphism of `Dial` on
  classes of programs, in the form of `PassChain.StepCert.ofTransport`.
* `Dial.Hom.stepCert` — the certificate of the total lowering along a morphism of `Dial`.
* `Dial.catToJasminStepCert` — the certificate of the step
  `NFProgPasses.mapStep NFProgCatToJasmin.catToJasmin`.

## Main results

* `Dial.G8_OPFIB` — `x.toTransport L` is strongly co-Cartesian.
* `Dial.forget_regionFunctor_isCofibered` — the forgetful functor is cofibred.
* `Dial.lift_factor`, `Dial.lift_factor_unique` — the factorisation of a lowered program
  through the lift, and its uniqueness.
* `Dial.lift_cert` — every morphism of `Dial` is forward-simulating.
* `DialectRestrict.denote_restrictNF?` — the restriction of a program denotes as the program.
* `Dial.Hom.denote_of_map_mk_eq` — the simulation square at a program whose class the
  action of a morphism reaches.
* `Dial.mapStep_catToJasmin_denote` — the transport statement of the pipeline's lowering
  step.
* `Dial.catToJasminStepCert_eq_ofMap?` — the certificate from the lift is the certificate
  `PassChain.StepCert.ofMap?` of the partial lowering.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open BlockLoweringExtend (transArgs)
open CategoryTheory

/-! ## 1. The opfibration -/

namespace Dial

/-- **Regions over dialects form an opfibration.** For an object `x` of the total category
    and a morphism `L` of `Dial` out of its dialect, the morphism `x.toTransport L` is
    strongly co-Cartesian over `L` for the forgetful functor. -/
theorem G8_OPFIB (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d') :
    (Grothendieck.forget regionFunctor).IsStronglyCocartesian L (x.toTransport L) :=
  Grothendieck.isStronglyCocartesian_toTransport x L

/-- The forgetful functor from regions over dialects to `Dial` is cofibred. -/
instance forget_regionFunctor_isCofibered :
    (Grothendieck.forget regionFunctor).IsCofibered :=
  Functor.IsCofibered.of_exists_isStronglyCocartesian fun a _ f =>
    ⟨a.transport f, a.toTransport f, G8_OPFIB a f⟩

/-- **The morphism of the total category given by a lowered program**: base component `L`
    and fibre component the class of `L.mapProg p`. -/
def loweredHom (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d')
    {ts : Region x.base.dia} (p : NFProg x.base.dia (x.fiber : Ctxt x.base.dia) ts) :
    x ⟶ (⟨d', Region.mapObj L ts⟩ : Grothendieck regionFunctor) where
  base := L
  fiber := (regionFunctor.map L).toFunctor.map
    (Region.Hom.mk p : @Quiver.Hom (Region x.base.dia) _ x.fiber ts)

/-- The fibre component of `loweredHom` is the class of the lowered program. -/
theorem loweredHom_fiber (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d')
    {ts : Region x.base.dia} (p : NFProg x.base.dia (x.fiber : Ctxt x.base.dia) ts) :
    (loweredHom x L p).fiber =
      (Region.Hom.mk (Dial.Hom.mapProg L p) : Region.mapObj L x.fiber ⟶ Region.mapObj L ts) :=
  rfl

/-- The base component of `loweredHom` is `L`, written as `L` followed by the identity. -/
theorem loweredHom_base_comp (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d')
    {ts : Region x.base.dia} (p : NFProg x.base.dia (x.fiber : Ctxt x.base.dia) ts) :
    (loweredHom x L p).base = L ≫ 𝟙 d' :=
  (Category.comp_id L).symm

/-- **The vertical morphism of a lowered program**: the morphism from `x.transport L` over
    the identity of `d'` whose fibre component is the class of `L.mapProg p`, read along
    `regionFunctor.map (L ≫ 𝟙 d') = regionFunctor.map L ≫ regionFunctor.map (𝟙 d')`. -/
def liftVertical (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d')
    {ts : Region x.base.dia} (p : NFProg x.base.dia (x.fiber : Ctxt x.base.dia) ts) :
    x.transport L ⟶ (⟨d', Region.mapObj L ts⟩ : Grothendieck regionFunctor) :=
  x.transportDesc L (𝟙 d') (loweredHom x L p) (loweredHom_base_comp x L p)

/-- The vertical morphism of a lowered program lies over the identity. -/
theorem liftVertical_base (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d')
    {ts : Region x.base.dia} (p : NFProg x.base.dia (x.fiber : Ctxt x.base.dia) ts) :
    (liftVertical x L p).base = 𝟙 d' := rfl

/-- **The factorisation of a lowered program through the lift.** The morphism given by the
    lowering of `p` along `L` is the lift `x.toTransport L` followed by the vertical morphism
    of the lowered program. -/
theorem lift_factor (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d')
    {ts : Region x.base.dia} (p : NFProg x.base.dia (x.fiber : Ctxt x.base.dia) ts) :
    x.toTransport L ≫ liftVertical x L p = loweredHom x L p := by
  unfold liftVertical
  exact Grothendieck.toTransport_comp_transportDesc x L (𝟙 d') (loweredHom x L p)
    (loweredHom_base_comp x L p)

/-- **Uniqueness of the factorisation.** A morphism over the identity of `d'` through which
    the lowering of `p` along `L` factors is the vertical morphism of the lowered program.
    The proof is the uniqueness part of the co-Cartesian property of the lift. -/
theorem lift_factor_unique (x : Grothendieck regionFunctor) {d' : Dial} (L : x.base ⟶ d')
    {ts : Region x.base.dia} (p : NFProg x.base.dia (x.fiber : Ctxt x.base.dia) ts)
    (χ : x.transport L ⟶ (⟨d', Region.mapObj L ts⟩ : Grothendieck regionFunctor))
    (hb : χ.base = 𝟙 d') (h : x.toTransport L ≫ χ = loweredHom x L p) :
    χ = liftVertical x L p := by
  have : (Grothendieck.forget regionFunctor).IsCocartesian L (x.toTransport L) :=
    Grothendieck.isCocartesian_toTransport x L
  have hχ : (Grothendieck.forget regionFunctor).IsHomLift (𝟙 d') χ := by
    have h₀ := CategoryTheory.IsHomLift.map (Grothendieck.forget regionFunctor) χ
    rwa [show (Grothendieck.forget regionFunctor).map χ = 𝟙 d' from hb] at h₀
  have : (Grothendieck.forget regionFunctor).IsHomLift (𝟙 d') (liftVertical x L p) :=
    Grothendieck.isHomLift_transportDesc x L (𝟙 d') (loweredHom x L p)
      (loweredHom_base_comp x L p)
  exact Functor.IsCocartesian.ext (Grothendieck.forget regionFunctor) L (x.toTransport L)
    χ (liftVertical x L p) (h.trans (lift_factor x L p).symm)

/-! ## 2. The simulation square of a morphism -/

/-- **The forward-simulation statement of a morphism of `Dial`.** At every fuel, the image
    of a class of programs under the action of `f` denotes, at the transport of a valuation,
    the transport of the denotation of the class. -/
def Hom.ForwardSim {a b : Dial} (f : a ⟶ b) : Prop :=
  ∀ (fuel : Nat) {Γ ts : Region a.dia} (g : Γ ⟶ ts) (V : Valuation (d := a.dia) Γ),
    ((Region.denoteFunctor fuel).map ((regionFunctor.map f).toFunctor.map g) :
        Valuation (d := b.dia) (Region.mapObj f Γ) →
          Option (Valuation (d := b.dia) (Region.mapObj f ts)))
        (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy V) =
      (((Region.denoteFunctor fuel).map g :
          Valuation (d := a.dia) Γ → Option (Valuation (d := a.dia) ts)) V).map
        (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy)

/-- **Every morphism of `Dial` is forward-simulating.** This is `Dial.Hom.denote_mapProg` on
    classes; it uses the functor `Dial.regionFunctor` and not the co-Cartesian property of
    the lift. -/
theorem lift_cert {a b : Dial} (f : a ⟶ b) : Hom.ForwardSim f := by
  rintro fuel Γ ts ⟨p⟩ V
  exact Dial.Hom.denote_mapProg f fuel p V

end Dial

/-! ## 3. The restriction of a program denotes as the program -/

namespace DialectRestrict

open DialectOpSum (castVar castArgs lookup_castVar lookupArgs_castArgs)

/-- The append of two vectors over the types of a restricted dialect is their append over the
    types of the dialect. -/
theorem hvAppend_restrict {d : Dialect.{0, 0}} (p : d.Op → Prop) {f : d.Ty → Type} :
    {xs ys : List d.Ty} → (A : HVector f xs) → (B : HVector f ys) →
      MultiBlockLowering.hvAppend (d := d.restrict p) A B =
        MultiBlockLowering.hvAppend (d := d) A B
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons a A, B => congrArg (HVector.cons a) (hvAppend_restrict p A B)

/-- The iteration of a loop body over a restricted dialect is its iteration over the
    dialect. -/
theorem whileIter_restrict {d : Dialect.{0, 0}} (p : d.Op → Prop) [TyDenote d.Ty]
    [HasBoolBit d] {cs : List d.Ty}
    (step : Valuation (d := d) cs → Option (Valuation (d := d) (HasBitType.bit (d := d) :: cs))) :
    (n : Nat) → (acc : Valuation (d := d) cs) →
      NFProg.whileIter (d := d.restrict p) step n acc = NFProg.whileIter (d := d) step n acc
  | 0, _ => rfl
  | n + 1, acc => by
      simp only [NFProg.whileIter, whileIter_restrict p step n]
      rfl

/-- **The restriction of a program denotes as the program**, at every fuel and valuation. -/
theorem denote_restrictNF? {d : Dialect.{0, 0}} (p : d.Op → Prop) [DecidablePred p]
    [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [DialectDenote d]
    [CallDenote d] (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (prog : NFProg d Γ ts) :
    ∀ p₀ : NFProg (d.restrict p) Γ ts, restrictNF? p prog = some p₀ →
      ∀ V : Valuation (d := d) Γ, p₀.denote fuel V = prog.denote fuel V := by
  induction prog with
  | ret vs =>
      intro p₀ h V
      cases h
      exact congrArg some (lookupArgs_castArgs vs V)
  | var e k ih =>
      intro p₀ h V
      rcases e with ⟨op, hret, args⟩
      subst hret
      simp only [restrictNF?] at h
      split at h
      · obtain ⟨k₀, hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [NFProg.denote, Expr.denoteM_option_eq_some, ih k₀ hk]
        exact congrArg (fun y => some y >>= fun x => NFProg.denote fuel k (V.extend x))
          (congrArg (DialectDenote.denote (d := d) op) (lookupArgs_castArgs args V))
      · cases h
  | forLoop count inits body k ihb ihk =>
      intro p₀ h V
      simp only [restrictNF?] at h
      obtain ⟨b₀, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k₀, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.denote, ihb b₀ hb, ihk k₀ hk, lookup_castVar, lookupArgs_castArgs,
        hvAppend_restrict]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro p₀ h V
      simp only [restrictNF?] at h
      obtain ⟨t₀, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e₀, he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k₀, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.denote, iht t₀ ht, ihe e₀ he, ihk k₀ hk, lookup_castVar,
        hvAppend_restrict]
      rfl
  | whileLoop inits body k ihb ihk =>
      intro p₀ h V
      simp only [restrictNF?] at h
      obtain ⟨b₀, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k₀, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.denote, ihb b₀ hb, ihk k₀ hk, lookupArgs_castArgs, hvAppend_restrict]
      exact congrArg (· >>= fun acc => NFProg.denote fuel k (MultiBlockLowering.hvAppend acc V))
        (whileIter_restrict p _ fuel _)
  | call f args k ih =>
      intro p₀ h V
      simp only [restrictNF?] at h
      obtain ⟨k₀, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.denote, ih k₀ hk, lookupArgs_castArgs, hvAppend_restrict]
      rfl

end DialectRestrict

/-! ## 4. Certificates from the simulation square -/

namespace Dial

open NFProgPasses DialectRestrict
open CryptoToJasminComCorrect (ctTransTy)
open DialectToJasminComCorrect (ctMapValD)

/-- **The certificate of the total lowering along a morphism of `Dial`**, from
    `Dial.lift_cert`: the input and output relations are the graphs of the transport. -/
def Hom.stepCert {a b : Dial} (f : a ⟶ b) (fuel : Nat) (Γ : Ctxt a.dia) (ts : List a.dia.Ty) :
    PassChain.StepCert (fun p : NFProg a.dia Γ ts => some (Dial.Hom.mapProg f p))
      (nfSem fuel a.dia Γ ts)
      (nfSem fuel b.dia (Γ.map (f : Dial.Hom a b).lower.mapTy)
        (ts.map (f : Dial.Hom a b).lower.mapTy)) :=
  PassChain.StepCert.ofTransport _ _
    (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy)
    (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy) fun p q V hf => by
      cases hf
      exact lift_cert f fuel (Region.Hom.mk p : @Quiver.Hom (Region a.dia) _ Γ ts) V

/-- **The simulation square at a program whose class the action reaches.** If the action of
    `f` sends the class of `p₀` to the class of `q`, then `q` denotes, at the transport of a
    valuation, the transport of the denotation of `p₀`. -/
theorem Hom.denote_of_map_mk_eq {a b : Dial} (f : a ⟶ b) (fuel : Nat) {Γ : Ctxt a.dia}
    {ts : List a.dia.Ty} (p₀ : NFProg a.dia Γ ts)
    (q : NFProg b.dia (Γ.map (f : Dial.Hom a b).lower.mapTy)
      (ts.map (f : Dial.Hom a b).lower.mapTy))
    (h : (regionFunctor.map f).toFunctor.map
        (Region.Hom.mk p₀ : @Quiver.Hom (Region a.dia) _ Γ ts) =
      (Region.Hom.mk q : Region.mapObj f Γ ⟶ Region.mapObj f ts))
    (V : Valuation (d := a.dia) Γ) :
    q.denote fuel (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy V) =
      (p₀.denote fuel V).map
        (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy) := by
  have hs := lift_cert f fuel (Region.Hom.mk p₀ : @Quiver.Hom (Region a.dia) _ Γ ts) V
  rw [h] at hs
  exact hs

/-- The valuation transport of `Dial.catToJasmin` is the transport of the argument vector. -/
theorem ctMapValD_eq_transArgs {Γ : Ctxt CatCryptDialect.catCryptDialect}
    (V : Valuation (d := CatCryptDialect.catCryptDialect) Γ) :
    ctMapValD V = transArgs CryptoToJasminCom.mapTy (fun x => ctTransTy x) V :=
  ((Dial.Hom.pullV_castHom_transArgs catToJasmin (Γ := Γ) V).symm.trans
    (FieldDialectBlockDescent.pullV_id _))

/-- **The transport statement of the pipeline's lowering step, from the lift.** If the
    partial lowering `NFProgCatToJasmin.catToJasmin` returns `q` on `p`, then `q` denotes at
    the transported valuation the transport of the denotation of `p`. The proof is
    `Dial.lift_cert` at `Dial.catToJasmin` on the class of the restriction of `p`
    (`Dial.mapStep_catToJasmin`), with `DialectRestrict.denote_restrictNF?`. -/
theorem mapStep_catToJasmin_denote (hT : NFProgCatToJasmin.catToJasmin.RegionTypes)
    (fuel : Nat) {Γ : Ctxt CatCryptDialect.catCryptDialect}
    {ts : List CatCryptDialect.catCryptDialect.Ty}
    (p : NFProg CatCryptDialect.catCryptDialect Γ ts)
    (q : NFProg JasminDialect.jasminDialect (CryptoToJasminCom.mapCtx Γ)
      (ts.map CryptoToJasminCom.mapTy))
    (h : (mapStep NFProgCatToJasmin.catToJasmin hT Γ ts).run p = some q)
    (V : Valuation (d := CatCryptDialect.catCryptDialect) Γ) :
    q.denote fuel (ctMapValD V) =
      (p.denote fuel V).map (transArgs CryptoToJasminCom.mapTy (fun x => ctTransTy x)) := by
  obtain ⟨p₀, hr, hq⟩ := mapStep_catToJasmin hT p q h
  have hs := Hom.denote_of_map_mk_eq catToJasmin fuel p₀ q hq V
  have hd := denote_restrictNF? (fun op => (DialectCategory.catTemplate op).isSome) fuel p p₀
    hr V
  rw [ctMapValD_eq_transArgs, ← hd]
  exact hs

/-- **The certificate of the pipeline's lowering step, from the lift**: the step
    `mapStep NFProgCatToJasmin.catToJasmin` with the graph of `ctMapValD` as input relation
    and the graph of the transport of result tuples as output relation, from
    `Dial.mapStep_catToJasmin_denote`. -/
def catToJasminStepCert (hT : NFProgCatToJasmin.catToJasmin.RegionTypes) (fuel : Nat)
    (Γ : Ctxt CatCryptDialect.catCryptDialect)
    (ts : List CatCryptDialect.catCryptDialect.Ty) :
    PassChain.StepCert (mapStep NFProgCatToJasmin.catToJasmin hT Γ ts).run
      (nfSem fuel CatCryptDialect.catCryptDialect Γ ts)
      (nfSem fuel JasminDialect.jasminDialect (NFProgCatToJasmin.catToJasmin.mapCtx Γ)
        (ts.map NFProgCatToJasmin.catToJasmin.mapTy)) :=
  PassChain.StepCert.ofTransport _ _ ctMapValD
    (transArgs NFProgCatToJasmin.catToJasmin.mapTy (fun x => ctTransTy x)) fun p q V hf =>
      mapStep_catToJasmin_denote hT fuel p q hf V

/-- **The certificate from the lift is the certificate `PassChain.StepCert.ofMap?` of the
    partial lowering.** Both are `PassChain.StepCert.ofTransport` at the same transports, so
    they have the same relations and differ in the proof of the transport statement only;
    the equality holds by proof irrelevance. -/
theorem catToJasminStepCert_eq_ofMap? (fuel : Nat) (Γ : Ctxt CatCryptDialect.catCryptDialect)
    (ts : List CatCryptDialect.catCryptDialect.Ty) :
    catToJasminStepCert NFProgCatToJasmin.catToJasmin_regionTypes fuel Γ ts =
      PassChain.StepCert.ofMap? NFProgCatToJasmin.catToJasmin
        NFProgCatToJasmin.catToJasmin_regionTypes (fun x => ctTransTy x) ctMapValD
        NFProgCatToJasmin.catToJasmin_varTransports
        (fun e blk hb V => NFProgCatToJasmin.catToJasmin_block e blk hb V)
        NFProgCatToJasmin.catToJasmin_mapValExtends
        NFProgCatToJasmin.catToJasmin_regionTransports fuel Γ ts :=
  rfl

end Dial

end CatCrypt.Crypto.SecureCompilation.VIR
