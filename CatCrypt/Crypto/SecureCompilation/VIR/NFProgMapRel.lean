/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMapMulti
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel

/-!
# Graded relational lowering of structured programs

`NFProg.mapM L hT` lowers a structured program along a multi-value lowering `L`. This module
states its correctness relative to a representation family `F : RepFamily L`: a grade
transfer `xfer` assigns grades to the results of let-bindings, and the relational block
square `BlockSquareRelE` asks each op block to send related arguments to a related result.

`gradeNF xfer gw p gΓ` is the abstract interpretation of `p` over grades. A let-binding
takes the grade `xfer` returns; the trip index of a counted loop takes the grade `gw`; a
counted loop and an exit-flag loop require their body to return the grade of the carried
tuple it starts from (a constant grade on the carried tuple); a branch requires its two arms
to return equal grades. Grades are compared by a decidable equality on `F.G t`; no
subsumption order is used. A loop whose carried grade grows with the trip index (an
accumulator bound `j · B` after `j` trips) does not satisfy the constant-grade check; such
loops are related by `NFProg.denote_forLoop_rel_graded` directly.

`RegionRel L hT F gw` asks that related trip counters read the same trip count, that the
trip index is related at `gw` to the target trip index, and that related bits read the same
`Bool`.

## Main definitions

* `NFProg.gradesDecEq`: decidable equality of grade vectors.
* `NFProg.gradeNF`: the grade interpreter over `NFProg`.
* `NFProg.RegionRel`: the conditions of a representation family at the trip counter, the
  trip index and the bit.

## Main results

* `NFProg.spliceM_pred`: the predicate form of `spliceM_denote`.
* `NFProg.flatRel_appHomM`: `appHomM` relates appended valuations related part by part.
* `NFProg.mapM_rel`: if `gradeNF xfer gw p gΓ = some gs` and the target valuation is related
  to `V` at `gΓ` along `ren`, the source and lowered denotations are `Option.Rel`-related
  at `gs`, at every fuel.
* `NFProg.mapM_rel_fwd`: the forward form for an op-level transfer and `BlockSquareRel`: a
  successful source run is matched by a successful run of the lowered program with related
  results.
* `NFProg.regionRel_graph`, `NFProg.gradeNF_goodXfer`, `NFProg.mapM_denote_of_rel`: at the
  unit-grade family `graphFamily L enc`, `mapM_rel` gives the equation of `mapM_denote`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering
open MultiBlockLoweringRel
open FieldDialectBlockDescent (pullV)
open BlockLoweringCPS (valuation_ext lookup_pullV)

namespace NFProg

/-! ## 1. The grade interpreter -/

section Grade

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] {G : d.Ty → Type} [∀ t, DecidableEq (G t)]

/-- Decidable equality of grade vectors from decidable equality of grades. -/
@[instance_reducible] def gradesDecEq : {ts : List d.Ty} → DecidableEq (HVector G ts)
  | [], .nil, .nil => isTrue rfl
  | _ :: _, .cons a as, .cons b bs =>
      if h : a = b then
        match gradesDecEq as bs with
        | isTrue h' => isTrue (by subst h; subst h'; rfl)
        | isFalse h' => isFalse fun e => h' (by cases e; rfl)
      else isFalse fun e => h (by cases e; rfl)

attribute [local instance] gradesDecEq

/-- **The grade interpreter over `NFProg`.** A return reads the grades of its variables; a
let-binding takes the grade `xfer` returns; the trip index of a counted loop has the grade
`gw`; the body of a counted or exit-flag loop must return the grade of the carried tuple at
entry, and the two arms of a branch must return equal grades. A call is not graded. -/
def gradeNF (xfer : XferE d G) (gw : G (HasWord64.word (d := d))) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → HVector G Γ → Option (HVector G ts)
  | _, _, .ret vs, gΓ => some (gradeArgs gΓ vs)
  | _, _, .var e k, gΓ =>
      (xfer e (gradeArgs gΓ e.args)).bind fun g =>
        gradeNF xfer gw k (.cons (e.retTy_eq ▸ g) gΓ)
  | _, _, .forLoop _ inits body k, gΓ =>
      (gradeNF xfer gw body (hvAppend (gradeArgs gΓ inits) (.cons gw gΓ))).bind fun gb =>
        if gb = gradeArgs gΓ inits then gradeNF xfer gw k (hvAppend (gradeArgs gΓ inits) gΓ)
        else none
  | _, _, .ifThenElse _ thn els k, gΓ =>
      (gradeNF xfer gw thn gΓ).bind fun gt => (gradeNF xfer gw els gΓ).bind fun ge =>
        if gt = ge then gradeNF xfer gw k (hvAppend gt gΓ) else none
  | _, _, .whileLoop inits body k, gΓ =>
      (gradeNF xfer gw body (hvAppend (gradeArgs gΓ inits) gΓ)).bind fun gb =>
        if gb.tail = gradeArgs gΓ inits then
          gradeNF xfer gw k (hvAppend (gradeArgs gΓ inits) gΓ)
        else none
  | _, _, .call .., _ => none

end Grade

/-! ## 2. The predicate form of `spliceM_denote` -/

section Splice

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d] [CallDenote d]

/-- **Predicate form of `spliceM_denote`.** If `k ren res` denotes a result satisfying `P`
whenever `ren` preserves lookups back to `W` and `res` holds the values of the block, the
splice denotes a result satisfying `P`. -/
theorem spliceM_pred (fuel : Nat) {ts : List d.Ty} :
    {Δ : Ctxt d} → {as : List d.Ty} → (blk : MultiReturnCom d Δ as) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) as → NFProg d Δ' ts) →
    (W : Valuation Δ) → (P : Option (Valuation ts) → Prop) →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : HVector (fun u => Var Δ' u) as)
        (W' : Valuation Δ'),
        (∀ {s : d.Ty} (v : Var Δ s), (ren v).lookup W' = v.lookup W) →
        MultiReturnCom.lookupVars res W' = blk.denote W →
        P ((k ren res).denote fuel W')) →
    P ((spliceM blk k).denote fuel W)
  | _, _, .ret vs, _, W, _, hk => hk (fun x => x) vs W (fun _ => rfl) rfl
  | _, _, .var e blk, _, W, P, hk => by
      simp only [spliceM, denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      exact spliceM_pred fuel blk _ (W.extend (e.denote W)) P
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2)

end Splice

/-! ## 3. The flattened relation along the renamings of `mapM` -/

section FlatRelRen

variable {d d' : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d]
  [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

omit [TyDenote d.Ty] [DialectSignature d] in
/-- The pullback along `splitHom` of an appended valuation whose left part starts with the
registers `A₁` of one source entry. -/
theorem pullV_splitHom_cons (m : d.Ty → List d'.Ty) {x : d.Ty} {xs ys : Ctxt d}
    (A₁ : Valuation (m x)) (A₂ : Valuation (ctxFlat m xs)) (B : Valuation (ctxFlat m ys)) :
    pullV (splitHom m (x :: xs) ys) (hvAppend (hvAppend A₁ A₂) B) =
      hvAppend A₁ (pullV (splitHom m xs ys) (hvAppend A₂ B)) := by
  have hF : pullV (fun w => inlHom (ctxFlat m ys) (inlHom (ctxFlat m xs) w))
      (hvAppend (hvAppend A₁ A₂) B) = A₁ := by
    rw [pullV_comp (fun w => inlHom (ctxFlat m xs) w) (fun w => inlHom (ctxFlat m ys) w),
      pullV_inlHom, pullV_inlHom]
  have hM : pullV (appendHom (fun u => inlHom (ctxFlat m ys) (inrHom (m x) u))
        (inrHom (m x ++ ctxFlat m xs))) (hvAppend (hvAppend A₁ A₂) B) = hvAppend A₂ B := by
    rw [pullV_appendHom, pullV_comp (fun u => inrHom (m x) u)
      (fun w => inlHom (ctxFlat m ys) w), pullV_inlHom, pullV_inrHom, pullV_inrHom]
  have hG : pullV (fun w => appendHom (fun u => inlHom (ctxFlat m ys) (inrHom (m x) u))
        (inrHom (m x ++ ctxFlat m xs)) (splitHom m xs ys w)) (hvAppend (hvAppend A₁ A₂) B) =
      pullV (splitHom m xs ys) (hvAppend A₂ B) := by
    rw [pullV_comp (fun w => splitHom m xs ys w)
      (fun w => appendHom (fun u => inlHom (ctxFlat m ys) (inrHom (m x) u))
        (inrHom (m x ++ ctxFlat m xs)) w), hM]
  exact (pullV_appendHom _ _ _).trans (congrArg₂ hvAppend hF hG)

/-- The pullback along `splitHom` of two related appended valuations is related at the
appended grades. -/
theorem flatRel_splitHom {L : MultiBlockLoweringData d d'} (F : RepFamily L) {Γ : Ctxt d}
    {gΓ : HVector F.G Γ} {V : Valuation Γ} {B : Valuation (L.mapCtx Γ)}
    (hB : FlatRel F gΓ V B) :
    ∀ {cs : Ctxt d} {gc : HVector F.G cs} {a : Valuation cs} {A : Valuation (L.mapCtx cs)},
      FlatRel F gc a A →
      FlatRel F (hvAppend gc gΓ) (hvAppend a V)
        (pullV (splitHom L.mapTys cs Γ) (hvAppend A B)) := by
  intro cs gc a A hA
  induction hA with
  | @nil W =>
      cases W
      show FlatRel F gΓ V (pullV (fun v => v) B)
      rw [FieldDialectBlockDescent.pullV_id]
      exact hB
  | @cons t cs g gs x a A₁ A₂ hx _ ih =>
      show FlatRel F (.cons g (hvAppend gs gΓ)) (.cons x (hvAppend a V))
        (pullV (splitHom L.mapTys (t :: cs) Γ) (hvAppend (hvAppend A₁ A₂) B))
      rw [pullV_splitHom_cons]
      exact .cons hx ih

/-- **`appHomM` on related valuations.** If the pullback of `W` along `ren` is related to `V`
at `gΓ`, the pullback along `appHomM` of `A` appended to `W` is related to `a` appended to
`V` at the appended grades, for `A` related to `a` at `gc`. -/
theorem flatRel_appHomM {L : MultiBlockLoweringData d d'} (F : RepFamily L) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (W : Valuation Δ) {gΓ : HVector F.G Γ}
    {V : Valuation Γ} (hW : FlatRel F gΓ V (pullV ren W)) {cs : Ctxt d}
    {gc : HVector F.G cs} {a : Valuation cs} {A : Valuation (L.mapCtx cs)}
    (hA : FlatRel F gc a A) :
    FlatRel F (hvAppend gc gΓ) (hvAppend a V) (pullV (appHomM L.mapTys cs ren) (hvAppend A W)) := by
  unfold appHomM
  rw [pullV_comp (fun v => splitHom L.mapTys cs Γ v)
      (fun v => appendHom (inlHom Δ) (fun w => inrHom (ctxFlat L.mapTys cs) (ren w)) v),
    pullV_appendHom, pullV_inlHom,
    pullV_comp (fun w => ren w) (fun w => inrHom (ctxFlat L.mapTys cs) w), pullV_inrHom]
  exact flatRel_splitHom F hW hA

/-- The variables `homToHV (argsHom ren vs)` read values related to the source arguments at
their grades. -/
theorem flatRel_lookupArgs {L : MultiBlockLoweringData d d'} (F : RepFamily L) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (W : Valuation Δ) {gΓ : HVector F.G Γ}
    {V : Valuation Γ} (hW : FlatRel F gΓ V (pullV ren W)) {ts : List d.Ty}
    (vs : HVector (fun t => Var Γ t) ts) :
    FlatRel F (gradeArgs gΓ vs) (Expr.lookupArgs vs V)
      (Expr.lookupArgs (homToHV _ (argsHom L.mapTys ren vs)) W) := by
  have e := lookupVars_homToHV W _ (argsHom L.mapTys ren vs)
  rw [lookupVars_eq_lookupArgs] at e
  rw [e]
  exact flatRel_args F ren W gΓ V hW vs

omit [TyDenote d.Ty] in
/-- The single register of a source variable whose type maps to a singleton list, read
through `ren`. -/
theorem lookup_singleVar_pullV (L : MultiBlockLoweringData d d') {Γ : Ctxt d} {Δ : Ctxt d'}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (W : Valuation Δ) {a : d.Ty} {a' : d'.Ty}
    (h : L.mapTys a = [a']) (v : Var Γ a) :
    (ren (varHom L.mapTys v (singleVar h))).lookup W =
      (castVal h (pullV (varHom L.mapTys v) (pullV ren W))).head := by
  rw [← lookup_pullV, ← lookup_pullV, lookup_singleVar]

end FlatRelRen

/-! ## 4. The region conditions and the relational lowering theorem -/

section MapRel

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- **The region conditions of a representation family.** Related trip counters read the
same trip count; the source trip index `i` is related at the grade `gw` to the target trip
index `i`; related bits read the same `Bool`. -/
structure RegionRel [DialectDenote d'] (L : MultiBlockLoweringData d d') (hT : RegionTypesM L)
    (F : RepFamily L) (gw : F.G (HasWord64.word (d := d))) : Prop where
  /-- A counter register related to `x` reads the trip count of `x`. -/
  toNat_rel : ∀ (g : F.G (HasWord64.word (d := d))) (x : ⟦HasWord64.word (d := d)⟧)
    (A : Valuation (L.mapTys (HasWord64.word (d := d)))), F.R g x A →
      HasWord64.toNat (d := d') (castVal hT.word_eq A).head = HasWord64.toNat (d := d) x
  /-- The target trip index is related to the source trip index at `gw`. -/
  ofNat_rel : ∀ i : Nat, F.R gw (HasWord64.ofNat (d := d) i)
    (castVal hT.word_eq.symm (.cons (HasWord64.ofNat (d := d') i) .nil))
  /-- A bit register related to `b` reads the `Bool` of `b`. -/
  toBool_rel : ∀ (g : F.G (HasBitType.bit (d := d))) (b : ⟦HasBitType.bit (d := d)⟧)
    (A : Valuation (L.mapTys (HasBitType.bit (d := d)))), F.R g b A →
      HasBoolBit.toBool (d := d') (castVal hT.bit_eq A).head = HasBoolBit.toBool (d := d) b

variable [DialectDenote d] [DialectDenote d']

attribute [local instance] gradesDecEq

/-- An `Option.Rel`-related pair whose right side is mapped by `f` stays related when `f`
sends related values to `S`-related ones. -/
theorem rel_map_right {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {f : β → γ}
    {o : Option α} {o' : Option β} (h : Option.Rel R o o') (hf : ∀ a b, R a b → S a (f b)) :
    Option.Rel S o (o'.map f) := by
  cases h with
  | none => exact .none
  | some h => exact .some (hf _ _ h)

/-- The forward reading of `Option.Rel`: a successful left side has a successful related
right side. -/
theorem rel_fwd {α β : Type} {R : α → β → Prop} {o : Option α} {o' : Option β}
    (h : Option.Rel R o o') {a : α} (ha : o = some a) : ∃ b, o' = some b ∧ R a b := by
  subst ha
  cases h with
  | some h => exact ⟨_, rfl, h⟩

/-- **Graded relational lowering of a structured program.** Under the relational block
square of an expression-level transfer `xfer` and `RegionRel`, if the grade interpreter
grades `p` at `gs` from `gΓ` and the pullback of `W` along `ren` is related to `V` at `gΓ`,
then at every fuel the source denotation and the denotation of `mapM L hT p ren` both fail
or both succeed with results related at `gs`. -/
theorem mapM_rel [CallDenote d] [CallDenote d'] (L : MultiBlockLoweringData d d')
    (hT : RegionTypesM L) (F : RepFamily L)
    [∀ t, DecidableEq (F.G t)] (xfer : XferE d F.G) (hBlk : L.BlockSquareRelE F xfer)
    (gw : F.G (HasWord64.word (d := d))) (hReg : RegionRel L hT F gw) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ (gΓ : HVector F.G Γ) (gs : HVector F.G ts), gradeNF xfer gw p gΓ = some gs →
      ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
        FlatRel F gΓ V (pullV ren W) →
        Option.Rel (FlatRel F gs) (p.denote fuel V) ((mapM L hT p ren).denote fuel W) := by
  induction p with
  | ret vs =>
      intro gΓ gs hg Δ ren V W hW
      obtain rfl := Option.some.inj hg
      exact .some (flatRel_lookupArgs F ren W hW vs)
  | var e k ih =>
      intro gΓ gs hg Δ ren V W hW
      obtain ⟨g, hg', hk⟩ := Option.bind_eq_some_iff.mp hg
      rw [denote_var, Expr.denoteM_option_eq_some, Option.bind_eq_bind, Option.bind_some]
      refine spliceM_pred fuel _ _ W
        (fun o => Option.Rel (FlatRel F gs) (k.denote fuel (V.extend (e.denote V))) o)
        (fun ren' res W' h1 h2 => ?_)
      refine ih _ gs hk _ (V.extend (e.denote V)) W' ?_
      have hW' : pullV ren' W' = W :=
        valuation_ext _ _ fun v => by rw [lookup_pullV]; exact h1 v
      have hR : FlatRel F gΓ V (pullV (fun w => ren' (ren w)) W') := by
        rw [pullV_comp (fun w => ren w) (fun w => ren' w), hW']
        exact hW
      rw [pullV_appendHom]
      refine .cons ?_ hR
      rw [pullV_hvToHom, h2, multiReturnCom_denote_rename]
      have hA := flatRel_args F ren W gΓ V hW e.args
      rcases e with ⟨op, rfl, args⟩
      exact hBlk ⟨op, rfl, args⟩ _ g hg' _ _ hA
  | forLoop count inits body k ihb ihk =>
      intro gΓ gs hg Δ ren V W hW
      simp only [gradeNF, Option.bind_eq_some_iff] at hg
      obtain ⟨gb, hb, hk⟩ := hg
      split_ifs at hk with he
      subst he
      simp only [mapM]
      refine denote_forLoop_rel fuel fuel
        (RΓ := fun V W => FlatRel F gΓ V (pullV ren W)) (Rc := FlatRel F (gradeArgs gΓ inits))
        count inits body k _ _ _ _ ?_ ?_ ?_ ?_ V W hW
      · intro V W hW
        rw [lookup_singleVar_pullV]
        exact (hReg.toNat_rel _ _ _ (flatRel_var F hW count)).symm
      · intro V W hW
        exact flatRel_lookupArgs F ren W hW inits
      · intro V W hW i a a' ha
        refine ihb _ _ hb _ _ _ (flatRel_appHomM F _ _ ?_ ha)
        rw [pullV_liftOne]
        exact .cons (hReg.ofNat_rel i) hW
      · intro V W hW a a' ha
        exact ihk _ _ hk _ _ _ (flatRel_appHomM F ren W hW ha)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro gΓ gs hg Δ ren V W hW
      simp only [gradeNF, Option.bind_eq_some_iff] at hg
      obtain ⟨gt, ht, ge, he, hk⟩ := hg
      split_ifs at hk with hq
      subst hq
      simp only [mapM]
      refine denote_ifThenElse_rel fuel fuel
        (RΓ := fun V W => FlatRel F gΓ V (pullV ren W)) (Rr := FlatRel F gt)
        cond thn els k _ _ _ _ ?_ ?_ ?_ ?_ V W hW
      · intro V W hW
        rw [lookup_singleVar_pullV]
        exact (hReg.toBool_rel _ _ _ (flatRel_var F hW cond)).symm
      · intro V W hW
        exact iht _ _ ht ren V W hW
      · intro V W hW
        exact ihe _ _ he ren V W hW
      · intro V W hW a a' ha
        exact ihk _ _ hk _ _ _ (flatRel_appHomM F ren W hW ha)
  | whileLoop inits body k ihb ihk =>
      intro gΓ gs hg Δ ren V W hW
      simp only [gradeNF, Option.bind_eq_some_iff] at hg
      obtain ⟨gb, hb, hk⟩ := hg
      split_ifs at hk with he
      simp only [mapM]
      refine denote_whileLoop_rel fuel
        (RΓ := fun V W => FlatRel F gΓ V (pullV ren W)) (Rc := FlatRel F (gradeArgs gΓ inits))
        inits body k _ _ _ ?_ ?_ ?_ V W hW
      · intro V W hW
        exact flatRel_lookupArgs F ren W hW inits
      · intro V W hW a a' ha
        rw [denote_castRet]
        refine rel_map_right (ihb _ _ hb _ _ _ (flatRel_appHomM F ren W hW ha))
          (fun r y hr => ?_)
        obtain ⟨A, B, rfl, hA, hB⟩ := FlatRel.inv_cons hr
        rw [castVal_append hT.bit_eq A B]
        refine ⟨?_, (hReg.toBool_rel _ _ _ hA).symm⟩
        rw [← he]
        exact hB
      · intro V W hW a a' ha
        exact ihk _ _ hk _ _ _ (flatRel_appHomM F ren W hW ha)
  | call =>
      intro gΓ gs hg
      simp [gradeNF] at hg

/-- **Graded relational lowering, forward form.** Under the relational block square of an
op-level transfer `xfer` and `RegionRel`, if the grade interpreter grades `p` at `gs` from
`gΓ`, the pullback of `W` along `ren` is related to `V` at `gΓ`, and the source run at fuel
`fuel` returns `y`, then `mapM L hT p ren` at the same fuel returns a valuation related to
`y` at `gs`. -/
theorem mapM_rel_fwd [CallDenote d] [CallDenote d'] (L : MultiBlockLoweringData d d')
    (hT : RegionTypesM L)
    (F : RepFamily L) [∀ t, DecidableEq (F.G t)] (xfer : XferOp d F.G)
    (hBlk : L.BlockSquareRel F xfer) (gw : F.G (HasWord64.word (d := d)))
    (hReg : RegionRel L hT F gw) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (gΓ : HVector F.G Γ) (gs : HVector F.G ts)
    (hg : gradeNF xfer.toE gw p gΓ = some gs) {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ)
    (V : Valuation Γ) (W : Valuation Δ) (hW : FlatRel F gΓ V (pullV ren W))
    (y : Valuation ts) (hy : p.denote fuel V = some y) :
    ∃ y', (mapM L hT p ren).denote fuel W = some y' ∧ FlatRel F gs y y' :=
  rel_fwd (mapM_rel L hT F xfer.toE hBlk.toE gw hReg fuel p gΓ gs hg ren V W hW) hy

/-! ### The unit-grade case -/

/-- Decidable equality of unit grades. -/
instance graphFamily_decEq (L : MultiBlockLoweringData d d') (enc : L.Enc) (t : d.Ty) :
    DecidableEq ((L.graphFamily enc).G t) :=
  (inferInstance : DecidableEq Unit)

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
  [DialectDenote d] in
/-- Two vectors of unit grades are equal. -/
theorem unitGrades_eq : ∀ {ts : List d.Ty} (a b : HVector (fun _ => Unit) ts), a = b
  | [], .nil, .nil => rfl
  | _ :: _, .cons () a, .cons () b => by rw [unitGrades_eq a b]

omit [DialectDenote d] in
/-- `RegionTransportsM` of an encoding gives `RegionRel` of its unit-grade family. -/
theorem regionRel_graph (L : MultiBlockLoweringData d d') (hT : RegionTypesM L)
    (enc : L.Enc) (hR : RegionTransportsM L hT enc) :
    RegionRel L hT (L.graphFamily enc) () where
  toNat_rel _ x A h := by
    rw [show A = enc x from h]
    exact hR.toNat_enc x
  ofNat_rel i := (hR.ofNat_enc i).symm
  toBool_rel _ b A h := by
    rw [show A = enc b from h]
    exact hR.toBool_enc b

omit [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] [DialectDenote d'] in
/-- A `Good`-covered program without `call` is graded by `goodXfer` at the unit grades. -/
theorem gradeNF_goodXfer (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hc : p.callFree = true) (hp : p.Covered Good) :
    ∀ gΓ : HVector (L.graphFamily enc).G Γ,
      gradeNF (L.goodXfer enc Good) () p gΓ = some (unitGrades ts) := by
  induction p with
  | ret vs =>
      intro gΓ
      exact congrArg some (unitGrades_eq _ _)
  | var e k ih =>
      intro gΓ
      have h1 : L.goodXfer enc Good e (gradeArgs gΓ e.args) = some () := ite_eq_left hp.1
      simp only [gradeNF, h1]
      exact ih hc hp.2 _
  | forLoop count inits body k ihb ihk =>
      intro gΓ
      simp only [callFree, Bool.and_eq_true] at hc
      simp only [gradeNF, ihb hc.1 hp.1]
      exact (ite_eq_left (unitGrades_eq _ _)).trans (ihk hc.2 hp.2 _)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro gΓ
      simp only [callFree, Bool.and_eq_true] at hc
      simp only [gradeNF, iht hc.1.1 hp.1, ihe hc.1.2 hp.2.1]
      exact (ite_eq_left rfl).trans (ihk hc.2 hp.2.2 _)
  | whileLoop inits body k ihb ihk =>
      intro gΓ
      simp only [callFree, Bool.and_eq_true] at hc
      simp only [gradeNF, ihb hc.1 hp.1]
      exact (ite_eq_left (unitGrades_eq _ _)).trans (ihk hc.2 hp.2 _)
  | call => simp [callFree] at hc

/-- **`mapM_denote` as the unit-grade case of `mapM_rel`.** Under the `Good`-gated block
square and `RegionTransportsM`, a `Good`-covered program without `call` lowered by `mapM` at
a renaming `ren` relating `W` to the flattened encoding of `V` denotes, at every fuel, the
flattened encoding of the source denotation. -/
theorem mapM_denote_of_rel [CallDenote d] [CallDenote d'] (L : MultiBlockLoweringData d d')
    (hT : RegionTypesM L)
    (enc : L.Enc) (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hBlk : L.BlockSquare enc Good) (hR : RegionTransportsM L hT enc) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hc : p.callFree = true)
    (hp : p.Covered Good)
    {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : pullV ren W = flatVal enc V) :
    (mapM L hT p ren).denote fuel W = (p.denote fuel V).map (flatVal enc) := by
  have h := mapM_rel L hT (L.graphFamily enc) (L.goodXfer enc Good)
    (L.blockSquareRelE_graph enc Good hBlk) () (regionRel_graph L hT enc hR) fuel p
    (unitGrades Γ) (unitGrades ts) (gradeNF_goodXfer L enc Good p hc hp _) ren V W
    ((L.flatRel_graph_iff enc _ V _).mpr hren)
  revert h
  generalize p.denote fuel V = o
  generalize (mapM L hT p ren).denote fuel W = o'
  intro h
  cases h with
  | none => rfl
  | some h => exact congrArg some ((L.flatRel_graph_iff enc _ _ _).mp h)

end MapRel

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
