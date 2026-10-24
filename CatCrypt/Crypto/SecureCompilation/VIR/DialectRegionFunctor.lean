/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectRegionCategory
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCategoryBase

/-!
# The functor of regions over the category of dialects

A morphism `f : a ⟶ b` of `Dial` acts on the regions of `a`. A type list `Γ` goes to
`Γ.map f.lower.mapTy`, and a program `p : NFProg a.dia Γ ts` goes to
`f.mapProg p`, the lowering `NFProg.map f.lower` of `p` at the renaming of
`f.lower.mapCtx Γ` into `Γ.map f.lower.mapTy` along the equality of the two contexts.

Every valuation of `Γ.map f.lower.mapTy` is the transport `transArgs` of a valuation of `Γ`
(`Dial.Hom.transArgs_surjective`), and `f.mapProg p` denotes at a transported valuation the
transport of the denotation of `p` (`Dial.Hom.denote_mapProg`). The denotation of
`f.mapProg p` is therefore determined by the denotation of `p`: the action respects
`Region.DenoteEq`, and it preserves the return of every variable and the composition
`NFProg.seq` at denotations. This is the functor `Region.mapFunctor f`.

The assignment `a ↦ Region a.dia`, `f ↦ Region.mapFunctor f` is a functor
`Dial.regionFunctor : Dial ⥤ Cat`. The action of an identity is the identity functor and the
action of a composite is the composite of the actions; both are equalities of functors whose
object parts are `List.map_id'` and `List.map_map`, proved through `Functor.hext` from the
heterogeneous equality of classes `Region.mk_heq_mk`.

The pipeline lowers a program of the crypto dialect by the partial lowering
`NFProgCatToJasmin.catToJasmin`. `DialectRestrict.map?_ofTemplate?` states that the partial
lowering of a partial template is the restriction `restrictNF?` to the accepted operations
followed by the total lowering of the restricted dialect, so the output of the pipeline's
step `NFProgPasses.mapStep` is `Dial.regionFunctor.map Dial.catToJasmin` at the class of the
restricted program (`Dial.mapStep_catToJasmin`).

## Main definitions

* `Dial.Hom.mapProg` — the lowering of a program along a morphism, between mapped type lists.
* `Region.mapObj`, `Region.mapHom`, `Region.mapFunctor` — the action of a morphism of `Dial`
  on type lists, on classes of programs, and as a functor.
* `Dial.regionFunctor` — the functor of regions, from `Dial` to `Cat`.

## Main results

* `Dial.Hom.transArgs_surjective`, `Dial.Hom.denote_mapProg` — surjectivity of the transport
  on valuations, and the denotation of a lowered program.
* `Region.DenoteEq.mapProg`, `Region.denoteEq_mapProg_ret`, `Region.denoteEq_mapProg_seq` —
  the action respects denotational equality, identities and composition.
* `Region.mk_heq_mk` — the heterogeneous equality of two classes of programs over equal type
  lists.
* `Region.mapFunctor_id`, `Region.mapFunctor_comp` — the action of an identity and of a
  composite.
* `DialectRestrict.appHom_acceptedLowering`, `DialectRestrict.liftTo_acceptedLowering` — the
  renamings under bindings agree for the accepted lowering and the partial template lowering.
* `DialectRestrict.map?_ofTemplate?` — the partial lowering of a partial template is the
  restriction followed by the total lowering of the accepted operations.
* `Dial.map?_catToJasmin_eq_map` — the pipeline's lowering of a program is `NFProg.map` of its
  restriction along the lowering of `Dial.catToJasmin`.
* `Dial.mapStep_catToJasmin` — the pipeline's lowering step on a program is the action of
  `Dial.catToJasmin` on the class of its restriction.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open FieldDialectBlockDescent (BlockLoweringData pullV pullV_id)
open BlockLoweringCPS (castHom)
open BlockLoweringExtend (transArgs)
open BlockLoweringDataComp
open DialectCategory
open CategoryTheory

/-! ## 1. The lowering of a program between mapped type lists -/

namespace Dial

/-- Pulling an extended valuation back along the renaming by an equality of contexts is
    extending the pulled-back valuation, carried along the equality of the cons. -/
theorem pullV_castHom_extend {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {A B C : Ctxt d} {s : d.Ty}
    (hc : A = s :: B) (hB : B = C) (hA : A = s :: C) (y : ⟦s⟧) (W : Valuation C) :
    pullV (castHom hA) (Valuation.extend W y) =
      (hc ▸ Valuation.extend (pullV (castHom hB) W) y : Valuation A) := by
  subst hB hc
  exact (pullV_id _).trans (congrArg (fun W' => Valuation.extend W' y) (pullV_id W).symm)

namespace Hom

variable {a b : Dial}

/-- The context map of a morphism is the pointwise type map. -/
theorem mapCtx_eq (f : Hom a b) : (Γ : Ctxt a.dia) → f.lower.mapCtx Γ = Γ.map f.lower.mapTy
  | [] => f.mapCtx_nil
  | t :: Γ => (f.lower.mapCtx_cons t Γ).trans (congrArg (f.lower.mapTy t :: ·) (mapCtx_eq f Γ))

/-- The valuation transport of a morphism is the transport of the argument vector, read
    along the equality of the context map and the pointwise type map. -/
theorem pullV_castHom_transArgs (f : Hom a b) : {Γ : Ctxt a.dia} → (V : Valuation Γ) →
    pullV (castHom (f.mapCtx_eq Γ)) (transArgs f.lower.mapTy f.transTy V) = f.mapVal V
  | [], _ => valuation_eq_of_nil f.mapCtx_nil _ _
  | t :: Γ, .cons x V => by
      show pullV (castHom (f.mapCtx_eq (t :: Γ)))
          (Valuation.extend (transArgs f.lower.mapTy f.transTy V) (f.transTy x)) =
        f.mapVal (Valuation.extend V x)
      refine Eq.trans ?_ (f.mapValExtends V x).symm
      have ih := pullV_castHom_transArgs f V
      refine (pullV_castHom_extend (f.lower.mapCtx_cons t Γ) (f.mapCtx_eq Γ) _ _ _).trans ?_
      rw [ih]

/-- **Surjectivity of the transport on valuations.** Every valuation of a mapped type list
    is the transport of a valuation. -/
theorem transArgs_surjective (f : Hom a b) : (Γ : Ctxt a.dia) →
    (W : Valuation (d := b.dia) (Γ.map f.lower.mapTy)) →
    ∃ V : Valuation Γ, transArgs f.lower.mapTy f.transTy V = W
  | [], .nil => ⟨.nil, rfl⟩
  | t :: Γ, .cons y W => by
      obtain ⟨x, rfl⟩ := f.surjective t y
      obtain ⟨V, rfl⟩ := transArgs_surjective f Γ W
      exact ⟨.cons x V, rfl⟩

/-- **The lowering of a program along a morphism**, from the mapped type list of its context
    to the mapped type list of its results: `NFProg.map` at the renaming of the mapped
    context into the mapped type list. -/
def mapProg (f : Hom a b) {Γ : Ctxt a.dia} {ts : List a.dia.Ty} (p : NFProg a.dia Γ ts) :
    NFProg b.dia (Γ.map f.lower.mapTy) (ts.map f.lower.mapTy) :=
  NFProg.map f.lower f.regionTypes p (castHom (f.mapCtx_eq Γ))

/-- **The denotation of a lowered program.** At a transported valuation, the lowering of `p`
    denotes the transport of the denotation of `p`, at every fuel. -/
theorem denote_mapProg (f : Hom a b) (fuel : Nat) {Γ : Ctxt a.dia} {ts : List a.dia.Ty}
    (p : NFProg a.dia Γ ts) (V : Valuation Γ) :
    (f.mapProg p).denote fuel (transArgs f.lower.mapTy f.transTy V) =
      (p.denote fuel V).map (transArgs f.lower.mapTy f.transTy) :=
  f.map_denote_ren fuel p _ V _ (f.pullV_castHom_transArgs V)

end Hom

end Dial

/-! ## 2. The action of a morphism on the category of regions -/

namespace Region

variable {a b c : Dial}

/-- The lowering along a morphism respects denotational equality. -/
theorem DenoteEq.mapProg (f : Dial.Hom a b) {Γ : Ctxt a.dia} {ts : List a.dia.Ty}
    {p q : NFProg a.dia Γ ts} (h : DenoteEq p q) : DenoteEq (f.mapProg p) (f.mapProg q) := by
  intro fuel W
  obtain ⟨V, rfl⟩ := f.transArgs_surjective Γ W
  rw [f.denote_mapProg, f.denote_mapProg, h fuel V]

/-- The lowering of the return of every variable denotes as the return of every variable. -/
theorem denoteEq_mapProg_ret (f : Dial.Hom a b) (Γ : Ctxt a.dia) :
    DenoteEq (f.mapProg (.ret (allVars Γ)))
      (.ret (allVars (d := b.dia) (Γ.map f.lower.mapTy))) := by
  intro fuel W
  obtain ⟨V, rfl⟩ := f.transArgs_surjective Γ W
  rw [f.denote_mapProg, NFProg.denote_ret, NFProg.denote_ret, lookupArgs_allVars,
    lookupArgs_allVars]
  rfl

/-- **The lowering of a composition denotes as the composition of the lowerings.** -/
theorem denoteEq_mapProg_seq (f : Dial.Hom a b) {Γ : Ctxt a.dia} {ts us : List a.dia.Ty}
    (p : NFProg a.dia Γ ts) (q : NFProg a.dia ts us) :
    DenoteEq (f.mapProg (p.seq q)) ((f.mapProg p).seq (f.mapProg q)) := by
  intro fuel W
  obtain ⟨V, rfl⟩ := f.transArgs_surjective Γ W
  rw [f.denote_mapProg, NFProg.denote_seq, NFProg.denote_seq, f.denote_mapProg]
  cases p.denote fuel V with
  | none => rfl
  | some r => exact (f.denote_mapProg fuel q r).symm

/-- The action of a morphism of `Dial` on type lists: the pointwise type map. -/
def mapObj (f : Dial.Hom a b) (Γ : Region a.dia) : Region b.dia :=
  List.map f.lower.mapTy (Γ : Ctxt a.dia)

/-- **The action of a morphism of `Dial` on morphisms of regions**: the lowering of a
    program, on classes. -/
def mapHom (f : Dial.Hom a b) {Γ ts : Region a.dia} (g : Γ ⟶ ts) :
    mapObj f Γ ⟶ mapObj f ts :=
  Quot.map (fun (p : NFProg a.dia Γ ts) => f.mapProg p) (fun _ _ h => DenoteEq.mapProg f h) g

/-- The action on the class of a program is the class of its lowering. -/
theorem mapHom_mk (f : Dial.Hom a b) {Γ ts : Region a.dia} (p : NFProg a.dia Γ ts) :
    mapHom f (Hom.mk p : Γ ⟶ ts) = (Hom.mk (f.mapProg p) : mapObj f Γ ⟶ mapObj f ts) := rfl

/-- **The action of a morphism of `Dial` as a functor** between the categories of regions. -/
def mapFunctor (f : Dial.Hom a b) : Region a.dia ⥤ Region b.dia where
  obj := mapObj f
  map g := mapHom f g
  map_id Γ := Quot.sound (denoteEq_mapProg_ret f Γ)
  map_comp := by
    rintro Γ ts us ⟨p⟩ ⟨q⟩
    exact Quot.sound (denoteEq_mapProg_seq f p q)

/-- **Heterogeneous equality of classes.** Two programs over equal contexts and equal result
    lists have the same class, read along the two equalities, when at equal valuations
    their denotations are the images of one partial result under two maps that agree. -/
theorem mk_heq_mk {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] [DialectDenoteM d Option] [CallDenote d] {Γ Γ' ts ts' : Region d}
    (hΓ : Γ = Γ') (hts : ts = ts') {p : NFProg d Γ ts} {q : NFProg d Γ' ts'}
    (h : ∀ (fuel : Nat) (V : Valuation (d := d) Γ) (V' : Valuation (d := d) Γ'), V ≍ V' →
      ∃ (α : Type) (o : Option α) (T : α → Valuation (d := d) ts)
        (T' : α → Valuation (d := d) ts'),
        (∀ r, T r ≍ T' r) ∧ p.denote fuel V = o.map T ∧ q.denote fuel V' = o.map T') :
    (Hom.mk p : Γ ⟶ ts) ≍ (Hom.mk q : Γ' ⟶ ts') := by
  subst hΓ hts
  refine heq_of_eq (mk_eq_mk fun fuel V => ?_)
  obtain ⟨α, o, T, T', hT, hp, hq⟩ := h fuel V V HEq.rfl
  obtain rfl : T = T' := funext fun r => eq_of_heq (hT r)
  exact hp.trans hq.symm

/-- **The action of an identity is the identity functor.** -/
theorem mapFunctor_id (a : Dial) : mapFunctor (𝟙 a : Dial.Hom a a) = 𝟭 (Region a.dia) := by
  refine Functor.hext (fun Γ => List.map_id' (Γ : Ctxt a.dia)) ?_
  rintro Γ ts ⟨p⟩
  refine mk_heq_mk (List.map_id' (Γ : Ctxt a.dia)) (List.map_id' (ts : Ctxt a.dia))
    fun fuel W V hW => ?_
  obtain ⟨V₀, rfl⟩ := Dial.Hom.transArgs_surjective (𝟙 a : Dial.Hom a a) Γ W
  obtain rfl : V₀ = V := eq_of_heq ((Dial.transArgs_id_heq V₀).symm.trans hW)
  exact ⟨_, p.denote fuel V₀, _, fun r => r, fun r => Dial.transArgs_id_heq r,
    Dial.Hom.denote_mapProg (𝟙 a : Dial.Hom a a) fuel p V₀, Option.map_id'.symm⟩

/-- **The action of a composite is the composite of the actions.** -/
theorem mapFunctor_comp (f : a ⟶ b) (g : b ⟶ c) :
    mapFunctor (f ≫ g : Dial.Hom a c) =
      mapFunctor (f : Dial.Hom a b) ⋙ mapFunctor (g : Dial.Hom b c) := by
  have hobj : ∀ Γ : Region a.dia, mapObj (f ≫ g : Dial.Hom a c) Γ =
      mapObj (g : Dial.Hom b c) (mapObj (f : Dial.Hom a b) Γ) :=
    fun Γ => (List.map_map (g := (g : Dial.Hom b c).lower.mapTy)
      (f := (f : Dial.Hom a b).lower.mapTy) (l := (Γ : Ctxt a.dia))).symm
  refine Functor.hext hobj ?_
  rintro Γ ts ⟨p⟩
  show (Hom.mk ((f ≫ g : Dial.Hom a c).mapProg p) : mapObj (f ≫ g : Dial.Hom a c) Γ ⟶ _) ≍
    (Hom.mk ((g : Dial.Hom b c).mapProg ((f : Dial.Hom a b).mapProg p)) :
      mapObj (g : Dial.Hom b c) (mapObj (f : Dial.Hom a b) Γ) ⟶ _)
  refine mk_heq_mk (hobj Γ) (hobj ts) fun fuel W V hW => ?_
  obtain ⟨V₀, rfl⟩ := Dial.Hom.transArgs_surjective (f ≫ g : Dial.Hom a c) Γ W
  obtain rfl : transArgs (g : Dial.Hom b c).lower.mapTy (g : Dial.Hom b c).transTy
      (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy V₀) = V :=
    eq_of_heq ((Dial.transArgs_comp_heq (f : Dial.Hom a b).lower.mapTy
      (g : Dial.Hom b c).lower.mapTy (f : Dial.Hom a b).transTy (g : Dial.Hom b c).transTy
      V₀).symm.trans hW)
  refine ⟨_, p.denote fuel V₀, _,
    fun r => transArgs (g : Dial.Hom b c).lower.mapTy (g : Dial.Hom b c).transTy
      (transArgs (f : Dial.Hom a b).lower.mapTy (f : Dial.Hom a b).transTy r),
    fun r => Dial.transArgs_comp_heq (f : Dial.Hom a b).lower.mapTy
      (g : Dial.Hom b c).lower.mapTy (f : Dial.Hom a b).transTy (g : Dial.Hom b c).transTy r,
    Dial.Hom.denote_mapProg (f ≫ g : Dial.Hom a c) fuel p V₀, ?_⟩
  show ((g : Dial.Hom b c).mapProg ((f : Dial.Hom a b).mapProg p)).denote fuel _ = _
  refine (Dial.Hom.denote_mapProg (g : Dial.Hom b c) fuel _ _).trans ?_
  refine (congrArg _ (Dial.Hom.denote_mapProg (f : Dial.Hom a b) fuel p V₀)).trans ?_
  cases p.denote fuel V₀ <;> rfl

end Region

/-! ## 3. The functor of regions -/

namespace Dial

/-- **The functor of regions.** A dialect goes to its category of regions and a morphism of
    `Dial` to its action on regions. -/
def regionFunctor : Dial ⥤ Cat.{0, 0} where
  obj a := Cat.of (Region a.dia)
  map f := (Region.mapFunctor f).toCatHom
  map_id a := congrArg Functor.toCatHom (Region.mapFunctor_id a)
  map_comp f g := congrArg Functor.toCatHom (Region.mapFunctor_comp f g)

end Dial

/-! ## 4. A partial template lowering on the accepted operations -/

namespace DialectRestrict

open DialectOpSum (castVar castArgs)

section Agreement

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [DialectSignature d'] [TyDenote d.Ty]
  [HasWord64 d] [HasBoolBit d] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
  (F : LoweringFrame d d') (S : F.Template?)

omit [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [TyDenote d'.Ty] [HasWord64 d']
  [HasBoolBit d'] in
/-- The renaming under a prefix of bindings is the same for the accepted lowering and for the
    partial template lowering. -/
theorem appHom_acceptedLowering {Γ : Ctxt d} {Δ : Ctxt d'} (ren : Ctxt.Hom (F.mapCtx Γ) Δ) :
    (cs : List d.Ty) →
      (NFProg.appHom (acceptedLowering F S).toPartial (Γ := Γ) cs ren :
          Ctxt.Hom (F.mapCtx (cs ++ Γ)) (cs.map F.mapTy ++ Δ)) =
        (NFProg.appHom (PartialBlockLowering.ofTemplate? F S) cs ren :
          Ctxt.Hom (F.mapCtx (cs ++ Γ)) (cs.map F.mapTy ++ Δ))
  | [] => rfl
  | c :: cs => by
      funext t v
      have ih := appHom_acceptedLowering ren cs
      simp only [NFProg.appHom, NFProg.liftTo, PartialBlockLowering.bodyHom]
      show BlockLoweringCPS.consHom _ _ (castHom (F.mapCtx_cons c (cs ++ Γ)) v) =
        BlockLoweringCPS.consHom _ _ (castHom (F.mapCtx_cons c (cs ++ Γ)) v)
      generalize castHom (F.mapCtx_cons c (cs ++ Γ)) v = w
      cases w with
      | here => rfl
      | there w =>
          show Var.there (NFProg.appHom (acceptedLowering F S).toPartial (Γ := Γ) cs ren w) =
            Var.there (NFProg.appHom (PartialBlockLowering.ofTemplate? F S) cs ren w)
          exact congrArg Var.there (congrFun (congrFun ih _) w)

omit [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [TyDenote d'.Ty] [HasWord64 d']
  [HasBoolBit d'] in
/-- The renaming under one binding is the same for the accepted lowering and for the partial
    template lowering. -/
theorem liftTo_acceptedLowering {Γ : Ctxt d} {Δ : Ctxt d'} {t : d.Ty} {t' : d'.Ty}
    (h : F.mapTy t = t') (ren : Ctxt.Hom (F.mapCtx Γ) Δ) :
    (NFProg.liftTo (acceptedLowering F S).toPartial (Γ := Γ) h ren :
        Ctxt.Hom (F.mapCtx (t :: Γ)) (t' :: Δ)) =
      (NFProg.liftTo (PartialBlockLowering.ofTemplate? F S) h ren :
        Ctxt.Hom (F.mapCtx (t :: Γ)) (t' :: Δ)) :=
  rfl

/-- **The partial lowering of a partial template is the restriction followed by the total
    lowering of the accepted operations.** `NFProg.map?` along the partial template lowering
    of `S` is defined exactly on the programs `restrictNF?` accepts, and there it is
    `NFProg.map?` of the restricted program along `acceptedLowering F S`. -/
theorem map?_ofTemplate? (hT : (PartialBlockLowering.ofTemplate? F S).RegionTypes)
    {Γ : Ctxt d} {ts : List d.Ty} (prog : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (F.mapCtx Γ) Δ),
      NFProg.map? (PartialBlockLowering.ofTemplate? F S) hT prog ren =
        (restrictNF? (fun op => (S op).isSome) prog).bind fun p₀ =>
          NFProg.map? (acceptedLowering F S).toPartial ⟨hT.word_eq, hT.bit_eq⟩ p₀ ren := by
  have bindNone : ∀ {α β : Type} (x : Option α) (f : α → Option β), (∀ a, f a = none) →
      x.bind f = none := by
    intro α β x f h
    cases x with
    | none => rfl
    | some a => exact h a
  induction prog with
  | ret vs =>
      intro Δ ren
      exact congrArg (fun ws => some (NFProg.ret ws)) (mapArgs_acceptedLowering F S ren vs).symm
  | var e k ih =>
      intro Δ ren
      rcases e with ⟨op, hret, args⟩
      subst hret
      simp only [NFProg.map?, restrictNF?, ih]
      by_cases h : (S op).isSome
      · rw [dite_eq_left h]
        have hb := templateBlock?_ofRestrict F S
          (⟨⟨op, h⟩, rfl, castArgs (O' := {op : d.Op // (S op).isSome}) args⟩ :
            Expr (d.restrict fun op => (S op).isSome) _ _)
        rw [ofRestrict, castArgs_castArgs, castArgs_self] at hb
        rw [hb]
        cases restrictNF? (fun op => (S op).isSome) k with
        | none => exact spliceNF?_none _
        | some k₀ => rfl
      · rw [dite_eq_right h]
        show ((S op).map _).bind _ = none
        rw [Option.not_isSome_iff_eq_none.mp h]
        rfl
  | forLoop count inits body k ihb ihk =>
      intro Δ ren
      simp only [NFProg.map?, restrictNF?, ihb, ihk]
      cases restrictNF? (fun op => (S op).isSome) body with
      | none => rfl
      | some b₀ =>
        cases restrictNF? (fun op => (S op).isSome) k with
        | none => exact bindNone _ _ fun _ => rfl
        | some k₀ =>
          simp only [Option.bind_some, Option.map_some, NFProg.map?, mapArgs_acceptedLowering,
            appHom_acceptedLowering]
          rw [← mapVar_restrictFrame (fun op => (S op).isSome = true) F count]
          exact congrArg
            (fun r : Ctxt.Hom (F.mapCtx (_ ++ HasWord64.word (d := d) :: _)) _ =>
              (NFProg.map? (acceptedLowering F S).toPartial _ b₀ r).bind _)
            (appHom_acceptedLowering F S
              (NFProg.liftTo (PartialBlockLowering.ofTemplate? F S) hT.word_eq ren) _).symm
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren
      simp only [NFProg.map?, restrictNF?, iht, ihe, ihk]
      cases restrictNF? (fun op => (S op).isSome) thn with
      | none => rfl
      | some t₀ =>
        cases restrictNF? (fun op => (S op).isSome) els with
        | none => exact bindNone _ _ fun _ => rfl
        | some e₀ =>
          cases restrictNF? (fun op => (S op).isSome) k with
          | none => exact bindNone _ _ fun _ => bindNone _ _ fun _ => rfl
          | some k₀ =>
            simp only [Option.bind_some, Option.map_some, NFProg.map?, appHom_acceptedLowering]
            rw [← mapVar_restrictFrame (fun op => (S op).isSome = true) F cond]
            rfl
  | whileLoop inits body k ihb ihk =>
      intro Δ ren
      simp only [NFProg.map?, restrictNF?, ihb, ihk]
      cases restrictNF? (fun op => (S op).isSome) body with
      | none => rfl
      | some b₀ =>
        cases restrictNF? (fun op => (S op).isSome) k with
        | none => exact bindNone _ _ fun _ => rfl
        | some k₀ =>
          simp only [Option.bind_some, Option.map_some, NFProg.map?, mapArgs_acceptedLowering,
            appHom_acceptedLowering]
          rfl
  | call f args k ih =>
      intro Δ ren
      simp only [NFProg.map?, restrictNF?, ih]
      cases restrictNF? (fun op => (S op).isSome) k with
      | none => rfl
      | some k₀ =>
        simp only [Option.bind_some, Option.map_some, NFProg.map?, mapArgs_acceptedLowering,
          appHom_acceptedLowering]
        rfl

end Agreement

end DialectRestrict

/-! ## 5. The pipeline's lowering step -/

namespace Dial

open DialectRestrict CatCryptDialect JasminDialect

/-- **The pipeline's lowering on a program is the total lowering of its restriction.** If
    `NFProg.map?` along `NFProgCatToJasmin.catToJasmin` at the identity renaming, the run of
    `NFProgPasses.mapStep`, returns `q` on a program `p` of the crypto dialect, then `p`
    restricts to a program `p₀` of the accepted operations and `q` is `NFProg.map` of `p₀`
    along the lowering of `Dial.catToJasmin`. -/
theorem map?_catToJasmin_eq_map (hT : NFProgCatToJasmin.catToJasmin.RegionTypes)
    {Γ : Ctxt catCryptDialect} {ts : List catCryptDialect.Ty}
    (p : NFProg catCryptDialect Γ ts)
    (q : NFProg jasminDialect (CryptoToJasminCom.mapCtx Γ) (ts.map CryptoToJasminCom.mapTy))
    (h : NFProg.map? NFProgCatToJasmin.catToJasmin hT p (fun v => v) = some q) :
    ∃ p₀ : NFProg cryptoAccepted.dia Γ ts,
      restrictNF? (fun op => (catTemplate op).isSome) p = some p₀ ∧
        q = NFProg.map catToJasmin.lower catToJasmin.regionTypes p₀ (fun v => v) := by
  have aux : ∀ (P : PartialBlockLowering catCryptDialect jasminDialect)
      (_ : P = PartialBlockLowering.ofTemplate? catFrame catTemplate) (hP : P.RegionTypes)
      (hP' : (PartialBlockLowering.ofTemplate? catFrame catTemplate).RegionTypes),
      NFProg.map? (PartialBlockLowering.ofTemplate? catFrame catTemplate) hP' p (fun v => v) ≍
        NFProg.map? P hP p (fun v => v) := by
    intro P e
    subst e
    intro _ _
    rfl
  have hT' : (PartialBlockLowering.ofTemplate? catFrame catTemplate).RegionTypes :=
    catToJasmin_eq_ofTemplate? ▸ hT
  have h' : NFProg.map? (PartialBlockLowering.ofTemplate? catFrame catTemplate) hT' p
      (fun v => v) = some q :=
    (eq_of_heq (aux _ catToJasmin_eq_ofTemplate? hT hT')).trans h
  rw [map?_ofTemplate?] at h'
  cases hr : restrictNF? (fun op => (catTemplate op).isSome) p with
  | none =>
      rw [hr] at h'
      cases h'
  | some p₀ =>
      rw [hr] at h'
      exact ⟨p₀, rfl, Option.some.inj (h'.symm.trans
        (NFProg.map?_toPartial catToJasmin.lower catToJasmin.regionTypes p₀ (fun v => v)))⟩

/-- **The pipeline's lowering step is the action of `Dial.catToJasmin` on regions.** The
    class of the program `NFProgPasses.mapStep` returns on `p` is the image, under the
    functor of regions at `Dial.catToJasmin`, of the class of the restriction of `p`. -/
theorem mapStep_catToJasmin (hT : NFProgCatToJasmin.catToJasmin.RegionTypes)
    {Γ : Ctxt catCryptDialect} {ts : List catCryptDialect.Ty}
    (p : NFProg catCryptDialect Γ ts)
    (q : NFProg jasminDialect (CryptoToJasminCom.mapCtx Γ) (ts.map CryptoToJasminCom.mapTy))
    (h : NFProg.map? NFProgCatToJasmin.catToJasmin hT p (fun v => v) = some q) :
    ∃ p₀ : NFProg cryptoAccepted.dia Γ ts,
      restrictNF? (fun op => (catTemplate op).isSome) p = some p₀ ∧
        (regionFunctor.map catToJasmin).toFunctor.map
            (Region.Hom.mk p₀ : @Quiver.Hom (Region cryptoAccepted.dia) _ Γ ts) =
          (Region.Hom.mk q : Region.mapObj catToJasmin Γ ⟶ Region.mapObj catToJasmin ts) := by
  obtain ⟨p₀, hr, rfl⟩ := map?_catToJasmin_eq_map hT p q h
  exact ⟨p₀, hr, rfl⟩

end Dial

end CatCrypt.Crypto.SecureCompilation.VIR
