/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.NarrowField

/-!
# Graded relational multi-value block lowering

A representation family `F : RepFamily L` for a multi-value lowering `L` from `d` to `d'`
assigns to each source type `t` a type of grades `F.G t` and to each grade `g` a relation
`F.R g` between source values of type `t` and target valuations of `L.mapTys t`. A
redundant representation (a word below a bound congruent to a field element, a Montgomery
form, a signed lane) is such a relation; a functional encoding `enc` is the case
`G = fun _ => Unit`, `R () x w ↔ w = enc x`.

A grade transfer `xfer` maps the grades of the arguments of an expression to the grade of
its result, or fails. `gradeCom xfer c gΓ` is the abstract interpretation of `c` under
`xfer` from the grades `gΓ` of its inputs; it is computable when `xfer` is, so the grade
certificate of a concrete program closes by `rfl`. The relational block square
`BlockSquareRel` asks that each op block maps related arguments to a related result
whenever the transfer succeeds.

## Main definitions

* `gradeVar`, `gradeArgs`: the grade of a variable and of an argument vector.
* `XferE`, `XferOp`: grade transfers of expressions and of ops.
* `gradeCom`, `gradeComM`, `gradeComOp`: the abstract interpreters over `Com` and
  `MultiReturnCom`.
* `RepFamily`, `FlatRel`: the representation family and its pointwise lift to flattened
  valuations.
* `MultiBlockLoweringData.BlockSquareRelE`, `BlockSquareRel`: the relational block squares
  for expression-level and op-level transfers.
* `graphFamily`, `goodXfer`: the unit-grade family of an encoding and the transfer of a
  coverage predicate.
* `zpDialect`, `barLowering`, `barFamily`, `barXfer`: a source dialect of addition and
  multiplication in `ZMod p`, its lowering to `w`-bit `jasminDialect` blocks through the
  Barrett multiply, the bound family `Rep p` and the bound transfer.

## Main results

* `MultiBlockLoweringData.multiFundamental_relE`, `multiFundamental_rel`: the graded
  fundamental theorem; if `gradeCom xfer c gΓ = some g` and the inputs are related at
  `gΓ`, the lowered program's result is related to the source value at `g`.
* `MultiBlockLoweringData.multiFundamentalM_relE`: the same for multi-result programs.
* `MultiBlockLoweringData.multiFundamental_on_of_rel`: `multiFundamental_on` as the
  unit-grade case.
* `barLowering_blockSquareRel`: the relational block square of the Barrett lowering.
* `mulAdd_lowered`: the lowered program `a · b + c` returns a word representing the
  `ZMod p` value under the bound computed by `gradeComOp`; `mulAdd_lowered_mlkem` is its
  instance at `q = 3329` in 16-bit words with output bound `6976`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering

/-! ## 1. Grades and the abstract interpreter -/

section Grades

variable {d : Dialect} {G : d.Ty → Type}

/-- The grade of a variable in a grade environment. -/
def gradeVar : {Γ : Ctxt d} → {t : d.Ty} → Var Γ t → HVector G Γ → G t
  | _, _, .here, .cons g _ => g
  | _, _, .there v, .cons _ gs => gradeVar v gs

/-- The grades of a vector of variables. -/
def gradeArgs {Γ : Ctxt d} (gΓ : HVector G Γ) :
    {ts : List d.Ty} → HVector (fun u => Var Γ u) ts → HVector G ts
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (gradeVar v gΓ) (gradeArgs gΓ vs)

/-- The unit grade environment of a context. -/
def unitGrades : (Γ : Ctxt d) → HVector (fun _ => Unit) Γ
  | [] => .nil
  | _ :: Γ => .cons () (unitGrades Γ)

variable [DialectSignature d]

/-- A grade transfer of expressions: from the grades of the arguments of `e`, the grade of
its result, or failure. -/
abbrev XferE (d : Dialect) [DialectSignature d] (G : d.Ty → Type) : Type _ :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t),
    HVector G (DialectSignature.sig e.op) → Option (G (DialectSignature.ret e.op))

/-- A grade transfer of ops. -/
abbrev XferOp (d : Dialect) [DialectSignature d] (G : d.Ty → Type) : Type _ :=
  (op : d.Op) → HVector G (DialectSignature.sig op) → Option (G (DialectSignature.ret op))

/-- The expression-level transfer of an op-level transfer. -/
def XferOp.toE (xfer : XferOp d G) : XferE d G := fun e gs => xfer e.op gs

/-- **The abstract interpreter of a grade transfer over `Com`.** -/
def gradeCom (xfer : XferE d G) :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → HVector G Γ → Option (G t)
  | _, _, .ret v, gΓ => some (gradeVar v gΓ)
  | _, _, .var e body, gΓ =>
      (xfer e (gradeArgs gΓ e.args)).bind fun g => gradeCom xfer body (.cons (e.retTy_eq ▸ g) gΓ)

/-- **The abstract interpreter of a grade transfer over `MultiReturnCom`.** -/
def gradeComM (xfer : XferE d G) :
    {Γ : Ctxt d} → {ts : List d.Ty} → MultiReturnCom d Γ ts → HVector G Γ →
      Option (HVector G ts)
  | _, _, .ret vs, gΓ => some (gradeArgs gΓ vs)
  | _, _, .var e body, gΓ =>
      (xfer e (gradeArgs gΓ e.args)).bind fun g =>
        gradeComM xfer body (.cons (e.retTy_eq ▸ g) gΓ)

/-- The abstract interpreter of an op-level transfer. -/
abbrev gradeComOp (xfer : XferOp d G) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (gΓ : HVector G Γ) : Option (G t) :=
  gradeCom xfer.toE c gΓ

end Grades

/-! ## 2. Representation families -/

section Family

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
variable {d' : Dialect} [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

/-- **A representation family** of a multi-value lowering: grades for each source type and,
for each grade, a relation between source values and target valuations. -/
structure RepFamily (L : MultiBlockLoweringData d d') where
  /-- The grades of a source type. -/
  G : d.Ty → Type
  /-- The relation of a grade between a source value and its target registers. -/
  R : ∀ {t : d.Ty}, G t → ⟦t⟧ → Valuation (L.mapTys t) → Prop

/-- **The flattened relation.** A flattened valuation is related to a source valuation at
the grades `gΓ` when it is the append of target valuations related entrywise. -/
inductive FlatRel {L : MultiBlockLoweringData d d'} (F : RepFamily L) :
    {Γ : Ctxt d} → HVector F.G Γ → Valuation Γ → Valuation (L.mapCtx Γ) → Prop
  | nil {W : Valuation (L.mapCtx [])} : FlatRel F .nil .nil W
  | cons {t : d.Ty} {Γ : Ctxt d} {g : F.G t} {gs : HVector F.G Γ} {x : ⟦t⟧}
      {V : Valuation Γ} {A : Valuation (L.mapTys t)} {B : Valuation (L.mapCtx Γ)} :
      F.R g x A → FlatRel F gs V B → FlatRel F (.cons g gs) (.cons x V) (hvAppend A B)

/-- The pullback of a related flattened valuation along `varHom v` is related to the value
of `v` at its grade. -/
theorem flatRel_var {L : MultiBlockLoweringData d d'} (F : RepFamily L) {Γ : Ctxt d}
    {gΓ : HVector F.G Γ} {V : Valuation Γ} {W : Valuation (L.mapCtx Γ)}
    (h : FlatRel F gΓ V W) :
    ∀ {u : d.Ty} (v : Var Γ u),
      F.R (gradeVar v gΓ) (v.lookup V) (pullV (varHom L.mapTys v) W) := by
  induction h with
  | nil => intro u v; nomatch v
  | @cons t Γ g gs x V A B hA _ ih =>
      intro u v
      cases v with
      | here =>
          show F.R g x (pullV (inlHom (ctxFlat L.mapTys Γ)) (hvAppend A B))
          rw [pullV_inlHom]
          exact hA
      | there v =>
          show F.R (gradeVar v gs) (v.lookup V)
            (pullV (fun w => inrHom (L.mapTys t) (varHom L.mapTys v w)) (hvAppend A B))
          rw [pullV_comp, pullV_inrHom]
          exact ih v

/-- The pullback along `argsHom ren args` of a valuation whose pullback along `ren` is
related at `gΓ` is related at the grades of the arguments. -/
theorem flatRel_args {L : MultiBlockLoweringData d d'} (F : RepFamily L) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (W : Valuation Δ)
    (gΓ : HVector F.G Γ) (V : Valuation Γ) (hW : FlatRel F gΓ V (pullV ren W)) :
    ∀ {ts : Ctxt d} (args : HVector (fun u => Var Γ u) ts),
      FlatRel F (gradeArgs gΓ args) (Expr.lookupArgs args V)
        (pullV (argsHom L.mapTys ren args) W)
  | [], .nil => .nil
  | u :: ts, .cons a rest => by
      show FlatRel F (gradeArgs gΓ (.cons a rest)) (Expr.lookupArgs (.cons a rest) V)
        (pullV (Γ := L.mapTys u ++ L.mapCtx ts)
          (appendHom (fun w => ren (varHom L.mapTys a w)) (argsHom L.mapTys ren rest)) W)
      rw [pullV_appendHom, pullV_comp]
      exact .cons (flatRel_var F hW a) (flatRel_args F ren W gΓ V hW rest)

end Family

/-! ## 3. The predicate form of the multi-result splice -/

section SpliceK

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- **Predicate form of `spliceMultiK_denote`.** If `k ren res` denotes a value satisfying
`P` whenever `ren` preserves lookups back to `W` and `res` holds the block's values, the
spliced program denotes a value satisfying `P`. -/
theorem spliceMultiK_pred : {Γ : Ctxt d} → {ts bs : List d.Ty} →
    (blk : MultiReturnCom d Γ ts) →
    (k : {Δ : Ctxt d} → Ctxt.Hom Γ Δ → HVector (fun u => Var Δ u) ts →
      MultiReturnCom d Δ bs) →
    (W : Valuation Γ) → (P : ListDenote bs → Prop) →
    (∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (res : HVector (fun u => Var Δ u) ts)
        (W' : Valuation Δ),
        (∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W' = v.lookup W) →
        MultiReturnCom.lookupVars res W' = blk.denote W →
        P ((k ren res).denote W')) →
    P ((spliceMultiK blk k).denote W)
  | _, _, _, .ret vs, _, W, _, hk => hk (fun x => x) vs W (fun _ => rfl) rfl
  | _, _, _, .var e blk, _, W, P, hk =>
      spliceMultiK_pred blk _ (Valuation.extend W (e.denote W)) P
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2)

end SpliceK

end CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel

/-! ## 4. The relational block square and the graded fundamental theorem -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering.MultiBlockLoweringData

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel

section Fundamental

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
variable {d' : Dialect} [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

/-- **The relational block square of an expression-level transfer.** Whenever the transfer
of `e` succeeds at `gs` with grade `g`, the block of `e.op` maps target arguments related
at `gs` to a result related at `g` to the op's value. -/
def BlockSquareRelE (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferE d F.G) : Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (gs : HVector F.G (DialectSignature.sig e.op))
    (g : F.G (DialectSignature.ret e.op)), xfer e gs = some g →
    ∀ (vals : Valuation (DialectSignature.sig e.op))
      (W : Valuation (L.mapCtx (DialectSignature.sig e.op))),
      FlatRel F gs vals W →
      F.R g (DialectDenote.denote e.op vals) ((L.lowerOp e.op).denote W)

/-- **The relational block square of an op-level transfer.** -/
def BlockSquareRel (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferOp d F.G) : Prop :=
  ∀ (op : d.Op) (gs : HVector F.G (DialectSignature.sig op))
    (g : F.G (DialectSignature.ret op)), xfer op gs = some g →
    ∀ (vals : Valuation (DialectSignature.sig op))
      (W : Valuation (L.mapCtx (DialectSignature.sig op))),
      FlatRel F gs vals W →
      F.R g (DialectDenote.denote op vals) ((L.lowerOp op).denote W)

/-- The op-level block square is the expression-level block square of `xfer.toE`. -/
theorem BlockSquareRel.toE {L : MultiBlockLoweringData d d'} {F : RepFamily L}
    {xfer : XferOp d F.G} (h : L.BlockSquareRel F xfer) : L.BlockSquareRelE F xfer.toE :=
  fun e gs g hx => h e.op gs g hx

/-- **Graded transport square of a lowered let-binding.** -/
theorem lowerBind_rel (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferE d F.G) (hBlk : L.BlockSquareRelE F xfer)
    {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt d'} {bs : List d'.Ty}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (e : Expr d Γ t) (gΓ : HVector F.G Γ)
    (g : F.G (DialectSignature.ret e.op)) (hg : xfer e (gradeArgs gΓ e.args) = some g)
    (kBody : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Ctxt.Hom (L.mapCtx (t :: Γ)) Δ' →
      MultiReturnCom d' Δ' bs)
    (W : Valuation Δ) (V : Valuation Γ) (P : ListDenote bs → Prop)
    (hW : FlatRel F gΓ V (pullV ren W))
    (hk : ∀ {Δ' : Ctxt d'} (ren' : Ctxt.Hom Δ Δ') (renB : Ctxt.Hom (L.mapCtx (t :: Γ)) Δ')
        (W' : Valuation Δ'),
        (∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W) →
        FlatRel F (.cons (e.retTy_eq ▸ g) gΓ) (Valuation.extend V (e.denote V)) (pullV renB W') →
        P ((kBody ren' renB).denote W')) :
    P ((L.lowerBind ren e kBody).denote W) := by
  refine spliceMultiK_pred _ _ W P (fun ren' res W' h1 h2 => hk ren' _ W' h1 ?_)
  have hW' : pullV ren' W' = W := valuation_ext _ _ fun v => by rw [lookup_pullV]; exact h1 v
  have hR : FlatRel F gΓ V (pullV (fun w => ren' (ren w)) W') := by
    rw [pullV_comp (fun w => ren w) (fun w => ren' w), hW']
    exact hW
  rw [pullV_appendHom]
  refine .cons ?_ hR
  rw [pullV_hvToHom, h2, multiReturnCom_denote_rename]
  have hA := flatRel_args F ren W gΓ V hW e.args
  rcases e with ⟨op, rfl, args⟩
  exact hBlk ⟨op, rfl, args⟩ _ g hg _ _ hA

/-- **Graded continuation-passing transport square of `lowerR`.** -/
theorem lowerR_rel (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferE d F.G) (hBlk : L.BlockSquareRelE F xfer) :
    ∀ {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt d'} {bs : List d'.Ty}
      (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (c : Com d Γ t)
      (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) (L.mapTys t) →
        MultiReturnCom d' Δ' bs)
      (gΓ : HVector F.G Γ) (g : F.G t) (W : Valuation Δ) (V : Valuation Γ)
      (P : ListDenote bs → Prop),
      gradeCom xfer c gΓ = some g → FlatRel F gΓ V (pullV ren W) →
      (∀ {Δ' : Ctxt d'} (ren' : Ctxt.Hom Δ Δ') (res : HVector (fun u => Var Δ' u) (L.mapTys t))
          (W' : Valuation Δ'),
          (∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W) →
          F.R g (c.denote V) (MultiReturnCom.lookupVars res W') →
          P ((k ren' res).denote W')) →
      P ((L.lowerR ren c k).denote W)
  | _, _, _, _, ren, .ret v, k, gΓ, g, W, V, P, hc, hW, hk => by
      refine hk (fun x => x) _ W (fun _ => rfl) ?_
      have hg : gradeVar v gΓ = g := Option.some.inj hc
      subst hg
      rw [lookupVars_homToHV, pullV_comp]
      exact flatRel_var F hW v
  | _, _, _, _, ren, .var e body, k, gΓ, g, W, V, P, hc, hW, hk => by
      obtain ⟨g', hg', hb⟩ := Option.bind_eq_some_iff.mp hc
      exact L.lowerBind_rel F xfer hBlk ren e gΓ g' hg' _ W V P hW
        (fun ren' renB W' h1 hB =>
          lowerR_rel L F xfer hBlk renB body _ _ g W' _ P hb hB
            (fun ren'' res W'' h1' h2' =>
              hk (fun x => ren'' (ren' x)) res W''
                (fun v => (h1' (ren' v)).trans (h1 v)) h2'))

/-- **Graded continuation-passing transport square of `lowerRM`.** -/
theorem lowerRM_rel (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferE d F.G) (hBlk : L.BlockSquareRelE F xfer) :
    ∀ {Γ : Ctxt d} {ts : List d.Ty} {Δ : Ctxt d'} {bs : List d'.Ty}
      (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (m : MultiReturnCom d Γ ts)
      (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) (L.mapCtx ts) →
        MultiReturnCom d' Δ' bs)
      (gΓ : HVector F.G Γ) (gs : HVector F.G ts) (W : Valuation Δ) (V : Valuation Γ)
      (P : ListDenote bs → Prop),
      gradeComM xfer m gΓ = some gs → FlatRel F gΓ V (pullV ren W) →
      (∀ {Δ' : Ctxt d'} (ren' : Ctxt.Hom Δ Δ') (res : HVector (fun u => Var Δ' u) (L.mapCtx ts))
          (W' : Valuation Δ'),
          (∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W) →
          FlatRel F gs (m.denote V) (MultiReturnCom.lookupVars res W') →
          P ((k ren' res).denote W')) →
      P ((L.lowerRM ren m k).denote W)
  | _, _, _, _, ren, .ret vs, k, gΓ, gs, W, V, P, hc, hW, hk => by
      refine hk (fun x => x) _ W (fun _ => rfl) ?_
      have hg : gradeArgs gΓ vs = gs := Option.some.inj hc
      subst hg
      rw [lookupVars_homToHV]
      show FlatRel F _ (MultiReturnCom.lookupVars vs V) _
      rw [lookupVars_eq_lookupArgs]
      exact flatRel_args F ren W gΓ V hW vs
  | _, _, _, _, ren, .var e body, k, gΓ, gs, W, V, P, hc, hW, hk => by
      obtain ⟨g', hg', hb⟩ := Option.bind_eq_some_iff.mp hc
      exact L.lowerBind_rel F xfer hBlk ren e gΓ g' hg' _ W V P hW
        (fun ren' renB W' h1 hB =>
          lowerRM_rel L F xfer hBlk renB body _ _ gs W' _ P hb hB
            (fun ren'' res W'' h1' h2' =>
              hk (fun x => ren'' (ren' x)) res W''
                (fun v => (h1' (ren' v)).trans (h1 v)) h2'))

/-- **Graded fundamental theorem, expression-level transfer.** If the abstract interpreter
grades `c` at `g` from `gΓ` and the target inputs are related to `V` at `gΓ`, the lowered
program's result is related to `c.denote V` at `g`. -/
theorem multiFundamental_relE (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferE d F.G) (hBlk : L.BlockSquareRelE F xfer)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (gΓ : HVector F.G Γ) (g : F.G t)
    (hc : gradeCom xfer c gΓ = some g) (V : Valuation Γ) (W : Valuation (L.mapCtx Γ))
    (hW : FlatRel F gΓ V W) :
    F.R g (c.denote V) ((L.lowerMulti c).denote W) :=
  L.lowerR_rel F xfer hBlk (fun v => v) c _ gΓ g W V (F.R g (c.denote V)) hc
    (by rw [pullV_id]; exact hW) (fun _ _ _ _ h2 => h2)

/-- **Graded fundamental theorem.** Under the relational block square of an op-level
transfer `xfer`, if `gradeComOp xfer c gΓ = some g` and the target inputs are related to
`V` at `gΓ`, the lowered program's result is related to `c.denote V` at `g`. -/
theorem multiFundamental_rel (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferOp d F.G) (hBlk : L.BlockSquareRel F xfer)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (gΓ : HVector F.G Γ) (g : F.G t)
    (hc : gradeComOp xfer c gΓ = some g) (V : Valuation Γ) (W : Valuation (L.mapCtx Γ))
    (hW : FlatRel F gΓ V W) :
    F.R g (c.denote V) ((L.lowerMulti c).denote W) :=
  L.multiFundamental_relE F xfer.toE hBlk.toE c gΓ g hc V W hW

/-- **Graded fundamental theorem, multi-result source.** -/
theorem multiFundamentalM_relE (L : MultiBlockLoweringData d d') (F : RepFamily L)
    (xfer : XferE d F.G) (hBlk : L.BlockSquareRelE F xfer)
    {Γ : Ctxt d} {ts : List d.Ty} (m : MultiReturnCom d Γ ts) (gΓ : HVector F.G Γ)
    (gs : HVector F.G ts) (hm : gradeComM xfer m gΓ = some gs) (V : Valuation Γ)
    (W : Valuation (L.mapCtx Γ)) (hW : FlatRel F gΓ V W) :
    FlatRel F gs (m.denote V) ((L.lowerMultiM m).denote W) :=
  L.lowerRM_rel F xfer hBlk (fun v => v) m _ gΓ gs W V (FlatRel F gs (m.denote V)) hm
    (by rw [pullV_id]; exact hW) (fun _ _ _ _ h2 => h2)

/-! ### The unit-grade case -/

/-- The unit-grade family of an encoding: a target valuation is related to `x` when it is
`enc x`. -/
def graphFamily (L : MultiBlockLoweringData d d') (enc : L.Enc) : RepFamily L where
  G _ := Unit
  R _ x w := w = enc x

omit [DialectDenote d] [DialectDenote d'] in
/-- Under the unit-grade family, the flattened relation is the graph of `flatVal enc`. -/
theorem flatRel_graph_iff (L : MultiBlockLoweringData d d') (enc : L.Enc) :
    ∀ {Γ : Ctxt d} (gs : HVector (graphFamily L enc).G Γ) (V : Valuation Γ)
      (W : Valuation (L.mapCtx Γ)),
      FlatRel (graphFamily L enc) gs V W ↔ W = flatVal enc V := by
  intro Γ gs V W
  constructor
  · intro h
    induction h with
    | @nil W => cases W; rfl
    | cons hA _ ih =>
        show hvAppend _ _ = hvAppend _ _
        rw [show _ = _ from hA, ih]
  · rintro rfl
    induction V with
    | nil => cases gs; exact .nil
    | cons x V ih =>
        cases gs
        exact .cons rfl (ih _)

open Classical in
/-- The unit-grade transfer of a coverage predicate: it succeeds exactly on `Good`
expressions. -/
noncomputable def goodXfer (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) : XferE d (graphFamily L enc).G :=
  fun e _ => if Good e then some () else none

omit [DialectDenote d] [DialectDenote d'] in
/-- A `Good`-covered program is graded by `goodXfer`. -/
theorem gradeCom_goodXfer (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t), CoveredCom Good c →
      ∀ gΓ : HVector (graphFamily L enc).G Γ, gradeCom (goodXfer L enc Good) c gΓ = some ()
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, hc, gΓ => by
      have h1 : goodXfer L enc Good e (gradeArgs gΓ e.args) = some () := by
        unfold goodXfer
        exact ite_eq_left hc.1
      simp only [gradeCom, h1]
      exact gradeCom_goodXfer L enc Good body hc.2 _

/-- The `Good`-gated block square is the relational block square of `goodXfer` under the
unit-grade family. -/
theorem blockSquareRelE_graph (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good) :
    L.BlockSquareRelE (graphFamily L enc) (goodXfer L enc Good) := by
  intro Γ t e gs g hx vals W hW
  have hG : Good e := by
    by_contra hn
    simp only [goodXfer, ite_eq_right hn, reduceCtorEq] at hx
  rw [(flatRel_graph_iff L enc gs vals W).mp hW]
  exact hBlk e hG vals

/-- **`multiFundamental_on` as the unit-grade case of the graded fundamental theorem.** -/
theorem multiFundamental_on_of_rel (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (hc : CoveredCom Good c) (V : Valuation Γ) :
    (L.lowerMulti c).denote (flatVal enc V) = enc (c.denote V) :=
  L.multiFundamental_relE (graphFamily L enc) (goodXfer L enc Good)
    (L.blockSquareRelE_graph enc Good hBlk) c (unitGrades Γ) ()
    (L.gradeCom_goodXfer enc Good c hc _) V (flatVal enc V)
    ((flatRel_graph_iff L enc _ V _).mpr rfl)

end Fundamental

end CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering.MultiBlockLoweringData

/-! ## 5. A graded instance: `ZMod p` through the Barrett multiply -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowField
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate (binE Rw)

section FlatRelInv

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
variable {d' : Dialect} [TyDenote d'.Ty] [DialectSignature d']

/-- Inversion of the flattened relation at a nonempty context. -/
theorem FlatRel.inv_cons {L : MultiBlockLoweringData d d'} {F : RepFamily L} {t : d.Ty}
    {Γ : Ctxt d} {gs : HVector F.G (t :: Γ)} {V : Valuation (t :: Γ)}
    {W : Valuation (L.mapCtx (t :: Γ))} (h : FlatRel F gs V W) :
    ∃ (A : Valuation (L.mapTys t)) (B : Valuation (L.mapCtx Γ)), W = hvAppend A B ∧
      F.R gs.head V.head A ∧ FlatRel F gs.tail V.tail B := by
  cases h with
  | cons hA hB => exact ⟨_, _, rfl, hA, hB⟩

end FlatRelInv

/-- The ops of `zpDialect`: addition and multiplication. -/
inductive ZOp where
  | add
  | mul

/-- The dialect of `ZMod p` with addition and multiplication. -/
def zpDialect (_p : ℕ) : Dialect where
  Op := ZOp
  Ty := Unit

instance (p : ℕ) : TyDenote (zpDialect p).Ty where
  denote _ := ZMod p

instance (p : ℕ) : DialectSignature (zpDialect p) where
  sig _ := [(), ()]
  ret _ := ()

/-- The denotation of the ops of `zpDialect` on their two arguments. -/
def zDenote (p : ℕ) : ZOp → ZMod p → ZMod p → ZMod p
  | .add, a, b => a + b
  | .mul, a, b => a * b

instance (p : ℕ) : DialectDenote (zpDialect p) where
  denote op args := zDenote p op args.head args.tail.head

/-- The addition expression of `zpDialect`. -/
def zAdd {p : ℕ} {Γ : Ctxt (zpDialect p)} (x y : Var Γ ()) : Expr (zpDialect p) Γ () :=
  ⟨ZOp.add, rfl, .cons x (.cons y .nil)⟩

/-- The multiplication expression of `zpDialect`. -/
def zMul {p : ℕ} {Γ : Ctxt (zpDialect p)} (x y : Var Γ ()) : Expr (zpDialect p) Γ () :=
  ⟨ZOp.mul, rfl, .cons x (.cons y .nil)⟩

/-- The `w`-bit addition block: `a + b` modulo `2 ^ w`. -/
def addBlk (w : ℕ) : Com jasminDialect (C2 w) (.reg w) :=
  .var (binE .add w .here (.there .here)) (.ret .here)

/-- **The Barrett lowering.** An element of `ZMod p` is one `w`-bit register; addition
lowers to `addBlk`, multiplication to the Barrett block of `F`. -/
def barLowering {w p : ℕ} (F : WordField w p) :
    MultiBlockLoweringData (zpDialect p) jasminDialect where
  mapTys _ := [Rw w]
  lowerOp
    | .add => (addBlk w).toMulti
    | .mul => (barBlk w p F.barS F.barT F.barM).toMulti

/-- **The bound family.** The grade of a register is a bound `B`, and the register is
related to `v` when it represents `v` with bound `B` (`Rep p B`). -/
def barFamily {w p : ℕ} (F : WordField w p) : RepFamily (barLowering F) where
  G _ := ℕ
  R g a W := Rep p g (W.head : BitVec w) a

/-- The bound transfer on two bounds: addition sums the bounds when the sum fits `w` bits;
multiplication accepts bounds at most `inMax` and returns `barOut`. -/
def barXferN {w p : ℕ} (F : WordField w p) : ZOp → ℕ → ℕ → Option ℕ
  | .add, a, b => if a + b < 2 ^ w then some (a + b) else none
  | .mul, a, b => if a ≤ F.inMax ∧ b ≤ F.inMax then some F.barOut else none

/-- The bound transfer of the Barrett lowering. -/
def barXfer {w p : ℕ} (F : WordField w p) : XferOp (zpDialect p) (barFamily F).G :=
  fun op gs => barXferN F op gs.head gs.tail.head

/-- `Rep` is monotone in the bound. -/
theorem rep_mono {p w : ℕ} {B B' : ℕ} {x : BitVec w} {v : ZMod p} (h : Rep p B x v)
    (hB : B ≤ B') : Rep p B' x v :=
  ⟨h.1.trans hB, h.2⟩

/-- The `w`-bit sum of words representing `u`, `v` with bounds `B`, `B'` and `B + B' < 2 ^ w`
represents `u + v` with bound `B + B'`. -/
theorem rep_add {p w : ℕ} {B B' : ℕ} {x y : BitVec w} {u v : ZMod p} (hx : Rep p B x u)
    (hy : Rep p B' y v) (hlt : B + B' < 2 ^ w) : Rep p (B + B') (x + y) (u + v) := by
  have hle : x.toNat + y.toNat ≤ B + B' := Nat.add_le_add hx.1 hy.1
  have e : (x + y).toNat = x.toNat + y.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (lt_of_le_of_lt hle hlt)]
  refine ⟨e ▸ hle, ?_⟩
  rw [e, Nat.cast_add, hx.2, hy.2]

/-- The output register of `addBlk` is the sum of its inputs. -/
theorem addBlk_toMulti_head {w : ℕ} (x y : BitVec w) :
    ((addBlk w).toMulti.denote (.cons x (.cons y .nil))).head = x + y := by
  rw [Com.denote_toMulti]
  rfl

/-- The output register of the Barrett block is `mulBar` of its inputs. -/
theorem barBlk_toMulti_head {w p : ℕ} (F : WordField w p) (x y : BitVec w) :
    ((barBlk w p F.barS F.barT F.barM).toMulti.denote (.cons x (.cons y .nil))).head
      = F.mulBar x y := by
  rw [Com.denote_toMulti]
  rfl

/-- **The relational block square of the Barrett lowering.** -/
theorem barLowering_blockSquareRel {w p : ℕ} (F : WordField w p) (hF : F.barOk = true) :
    (barLowering F).BlockSquareRel (barFamily F) (barXfer F) := by
  intro op gs g hx vals W hW
  obtain ⟨A, B, rfl, hA, hB⟩ :=
    FlatRel.inv_cons (L := barLowering F) (F := barFamily F) (t := ()) (Γ := [()]) hW
  obtain ⟨B₁, B₂, rfl, hB₁, -⟩ :=
    FlatRel.inv_cons (L := barLowering F) (F := barFamily F) (t := ()) (Γ := []) hB
  rcases A with _ | ⟨x, _ | _⟩
  rcases B₁ with _ | ⟨y, _ | _⟩
  rcases B₂ with _ | _
  have hA' : Rep p gs.head (x : BitVec w) vals.head := hA
  have hB' : Rep p gs.tail.head (y : BitVec w) vals.tail.head := hB₁
  cases op with
  | add =>
      have hx' : barXferN F .add gs.head gs.tail.head = some g := hx
      simp only [barXferN] at hx'
      split_ifs at hx' with hlt
      cases hx'
      show Rep p _ ((addBlk w).toMulti.denote (.cons x (.cons y .nil))).head _
      rw [addBlk_toMulti_head]
      exact rep_add hA' hB' hlt
  | mul =>
      have hx' : barXferN F .mul gs.head gs.tail.head = some g := hx
      simp only [barXferN] at hx'
      split_ifs at hx' with hle
      cases hx'
      show Rep p _
        ((barBlk w p F.barS F.barT F.barM).toMulti.denote (.cons x (.cons y .nil))).head _
      rw [barBlk_toMulti_head]
      exact F.mulBar_rep hF (rep_mono hA' hle.1) (rep_mono hB' hle.2)

/-- The three-input context of `zpDialect`. -/
abbrev Ctx3 (p : ℕ) : Ctxt (zpDialect p) := [(), (), ()]

/-- The source program `let t = a · b; let r = t + c; ret r`. -/
def mulAdd (p : ℕ) : Com (zpDialect p) (Ctx3 p) () :=
  .var (zMul .here (.there .here))
    (.var (zAdd .here (.there (.there (.there .here))))
      (.ret .here))

/-- `mulAdd` denotes `a · b + c`. -/
theorem mulAdd_denote {p : ℕ} (a b c : ZMod p) :
    ((mulAdd p).denote (.cons a (.cons b (.cons c .nil))) : ZMod p) = a * b + c :=
  rfl

/-- **The lowered `a · b + c`.** If the bound interpreter grades `mulAdd` at `g` from three
inputs with bound `inMax`, then on words representing `a`, `b`, `c` with bound `inMax` the
lowered program returns a word representing `a · b + c` with bound `g`. -/
theorem mulAdd_lowered {w p : ℕ} (F : WordField w p) (hF : F.barOk = true) {g : ℕ}
    (hg : gradeComOp (barXfer F) (mulAdd p)
      (.cons F.inMax (.cons F.inMax (.cons F.inMax .nil))) = some g)
    {x y z : BitVec w} {a b c : ZMod p} (hx : Rep p F.inMax x a) (hy : Rep p F.inMax y b)
    (hz : Rep p F.inMax z c) :
    Rep p g (((barLowering F).lowerMulti (mulAdd p)).denote
      (.cons x (.cons y (.cons z .nil)))).head (a * b + c) := by
  have hW : FlatRel (barFamily F) (Γ := Ctx3 p) (.cons F.inMax (.cons F.inMax (.cons F.inMax .nil)))
      (.cons a (.cons b (.cons c .nil)))
      (hvAppend (.cons x .nil : Valuation [Rw w]) (hvAppend (.cons y .nil : Valuation [Rw w])
        (hvAppend (.cons z .nil : Valuation [Rw w]) .nil))) :=
    .cons hx (.cons hy (.cons hz .nil))
  exact (barLowering F).multiFundamental_rel (barFamily F) (barXfer F)
    (barLowering_blockSquareRel F hF) (mulAdd p) _ g hg _ _ hW

/-- The bound certificate of `mulAdd` at `q = 3329` in 16-bit words: from inputs below
`3329`, the Barrett product has bound `3648` and the sum has bound `6976`. -/
theorem mulAdd_grade_mlkem :
    gradeComOp (barXfer mlkemField) (mulAdd 3329)
      (.cons (3328 : ℕ) (.cons (3328 : ℕ) (.cons (3328 : ℕ) .nil))) = some (6976 : ℕ) :=
  rfl

/-- **The lowered `a · b + c` at `q = 3329`.** On 16-bit words representing `a`, `b`, `c`
with bound `3328`, the lowered program returns a word representing `a · b + c` with bound
`6976`. -/
theorem mulAdd_lowered_mlkem {x y z : BitVec 16} {a b c : ZMod 3329}
    (hx : Rep 3329 3328 x a) (hy : Rep 3329 3328 y b) (hz : Rep 3329 3328 z c) :
    Rep 3329 6976 (((barLowering mlkemField).lowerMulti (mulAdd 3329)).denote
      (.cons x (.cons y (.cons z .nil)))).head (a * b + c) :=
  mulAdd_lowered mlkemField mlkemField_barOk mulAdd_grade_mlkem hx hy hz

end CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel
