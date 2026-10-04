/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Category.KleisliCat
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringDataComp
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum

/-!
# The categorical presentation of dialects, lowerings and regions

Dialects are the objects and block lowerings `BlockLoweringData d d'` the morphisms,
composed by `BlockLoweringData.compBlock`. The identity is `BlockLoweringData.id d`, which
sends each expression `e` to the one-binding block `let x := e; ret x`.

The unit and associativity laws hold syntactically, field by field, under conditions on
the lowerings involved:

* right unit (`compBlock_id`): unconditional, an equality of records;
* left unit (`id_compBlock`): under `HeadVar L`, which says that `L.mapVar` sends the head
  variable of `t :: Γ` to the head variable of `L.mapTy t :: L.mapCtx Γ`;
* associativity (`compBlock_assoc`): under `SpliceNatural N` for the last lowering, which
  says that `N.blockLowerCom` commutes with the block splice `spliceCom`. The general case
  needs it because `L.compBlock M` lowers the block of `L` by `M.blockLowerCom`, and
  `blockLowerCom` is a functor on splices only when the lowering commutes with renamings.

No `CategoryTheory.Category` instance is given on lowerings, since the left unit and
associativity laws are conditional.

The operation sum `Dialect.opSum d e` over a shared type alphabet carries a copairing
`copair L₁ L₂`, a block lowering out of the sum that lowers the operations of `d` by `L₁`
and those of `e` by `L₂`, for two lowerings with the same type and context maps. It is
unique on operations (`copair_unique`): a lowering with the frame of `L₁` that agrees with
`L₁` on the operations of `d` and with `L₂` on those of `e` is the copairing. The
injections are `DialectOpSum.inl` and `DialectOpSum.inr` (`inl_fundamental`,
`inr_fundamental`). `BlockLoweringData.extendId L` is the whiskering of `L` by the identity
on `e`: it lowers an operation of `d` by `L` followed by the left injection
(`extendId_inl`), maps an operation of `e` to itself (`extendId_inr`), and is the
copairing of these two components (`extendId_eq_copair`).

The coproduct of dialects with disjoint type alphabets, `Dialect.sum`, has the injections
`DialectCoproduct.inlLowering` and `DialectCoproduct.inrLowering`. It has no copairing of
block lowerings: a lowering out of `d ⊕ e` acts on contexts that mix types of both
summands, and a lowering of `d` acts only on contexts of `d`.

The identity law of `NFProg.map?` is stated at the level of denotations
(`map_id_denote`): the identity lowering returns a program of result types
`ts.map (fun t => t)`, which is not definitionally `ts`.

Regions form a category over the contexts of a dialect: the prefixes `NFPre d Γ Δ` are the
morphisms, `NFPre.nil` the identity and `NFPre.append` the composition
(`RegionCtx.instCategory`). `NFPre.plug` is the action of prefixes on programs
(`plug_append`), and the denotation at a fuel is a functor into the Kleisli category of
`Option` (`regionDenote`), which restates `NFPre.denote_append`.

This module is a presentation: no pass of the compilation pipeline uses its laws. The
pipeline composes lowerings as chains of passes (`VIR/PassChain.lean`).

## Main definitions

* `BlockLoweringData.id` — the identity block lowering.
* `DialectCategory.HeadVar`, `DialectCategory.SpliceNatural` — the side conditions of the
  left unit and associativity laws.
* `DialectCategory.copair` — the copairing out of an operation sum.
* `DialectCategory.extendIdRight` — the identity component of `extendId`.
* `DialectCategory.RegionCtx` — the contexts of a dialect as the objects of the region
  category.
* `DialectCategory.regionDenote` — the denotation of prefixes as a functor into
  `KleisliCat Option`.

## Main results

* `DialectCategory.blockLowerCom_id`, `DialectCategory.compBlock_id`,
  `DialectCategory.id_compBlock`, `DialectCategory.blockLowerCom_compBlock`,
  `DialectCategory.compBlock_assoc` — the category laws of block lowerings, with
  `DialectCategory.headVar_id` and `DialectCategory.spliceNatural_id`.
* `DialectCategory.copair_inl`, `DialectCategory.copair_inr`,
  `DialectCategory.copair_unique` — the universal property of the operation sum.
* `DialectCategory.extendId_inl`, `DialectCategory.extendId_inr`,
  `DialectCategory.extendId_eq_copair` — `extendId` as whiskering.
* `NFPre.nil_append`, `NFPre.append_nil`, `NFPre.append_assoc`, `NFPre.nil_plug`,
  `NFPre.plug_append`, `NFPre.denote_nil` — the laws of region composition.
* `DialectCategory.map_id_denote` — the identity lowering of a structured program
  preserves its denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open FieldDialectBlockDescent (BlockLoweringData spliceCom substHeadHom)

/-- **The identity block lowering**: types, contexts and variables are unchanged, and an
    expression `e` becomes the one-binding block `let x := e; ret x`. -/
def FieldDialectBlockDescent.BlockLoweringData.id (d : Dialect) [DialectSignature d] :
    BlockLoweringData d d where
  mapTy := fun t => t
  mapCtx := fun Γ => Γ
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => v
  lowerExprBlock := fun e => .var e (.ret .here)

namespace DialectCategory

/-! ## 1. Renaming -/

section Rename

variable {d : Dialect}

/-- Pointwise equal renamings rename an argument vector equally. -/
theorem renameVars_congr {Γ Γ' : Ctxt d} {f g : Ctxt.Hom Γ Γ'}
    (h : ∀ {t : d.Ty} (v : Var Γ t), f v = g v) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    HVector.renameVars f vs = HVector.renameVars g vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      simp only [HVector.renameVars, h v, renameVars_congr h vs]

/-- Renaming an argument vector twice renames it by the composite. -/
theorem renameVars_renameVars {Γ Γ' Γ'' : Ctxt d} (f : Ctxt.Hom Γ' Γ'')
    (g : Ctxt.Hom Γ Γ') :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    HVector.renameVars f (HVector.renameVars g vs) =
      HVector.renameVars (fun v => f (g v)) vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      simp only [HVector.renameVars, renameVars_renameVars f g vs]

/-- Renaming an argument vector by the identity leaves it unchanged. -/
theorem renameVars_self {Γ : Ctxt d} :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    HVector.renameVars (fun v => v) vs = vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      simp only [HVector.renameVars, renameVars_self vs]

/-- The lifts of pointwise equal renamings are pointwise equal. -/
theorem lift_congr {Γ Γ' : Ctxt d} {s : d.Ty} {f g : Ctxt.Hom Γ Γ'}
    (h : ∀ {t : d.Ty} (v : Var Γ t), f v = g v) {t : d.Ty} (v : Var (s :: Γ) t) :
    Ctxt.Hom.lift f v = Ctxt.Hom.lift g v := by
  cases v with
  | here => rfl
  | there v => simp only [Ctxt.Hom.lift, h v]

variable [DialectSignature d]

/-- Pointwise equal renamings rename a program equally. -/
theorem rename_congr : {Γ Γ' : Ctxt d} → {τ : d.Ty} → {f g : Ctxt.Hom Γ Γ'} →
    (∀ {t : d.Ty} (v : Var Γ t), f v = g v) → (c : Com d Γ τ) →
    Com.rename f c = Com.rename g c
  | _, _, _, _, _, h, .ret v => by simp only [Com.rename, h v]
  | _, _, _, _, _, h, .var e body => by
      simp only [Com.rename, Expr.rename, renameVars_congr h,
        rename_congr (lift_congr h) body]

/-- Renaming a program twice renames it by the composite. -/
theorem rename_rename : {Γ Γ' Γ'' : Ctxt d} → {τ : d.Ty} → (f : Ctxt.Hom Γ' Γ'') →
    (g : Ctxt.Hom Γ Γ') → (c : Com d Γ τ) →
    Com.rename f (Com.rename g c) = Com.rename (fun v => f (g v)) c
  | _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, f, g, .var e body => by
      simp only [Com.rename, Expr.rename, renameVars_renameVars, rename_rename]
      congr 1
      exact rename_congr (fun v => by cases v <;> rfl) body

/-- Renaming by a renaming that is pointwise the identity leaves a program unchanged. -/
theorem rename_of_forall_eq : {Γ : Ctxt d} → {τ : d.Ty} → {f : Ctxt.Hom Γ Γ} →
    (∀ {t : d.Ty} (v : Var Γ t), f v = v) → (c : Com d Γ τ) → Com.rename f c = c
  | _, _, _, h, .ret v => by simp only [Com.rename, h v]
  | Γ, _, f, h, .var (t := u) e body => by
      have hl : ∀ {t : d.Ty} (v : Var (u :: Γ) t), Ctxt.Hom.lift f v = v := by
        intro t v
        cases v with
        | here => rfl
        | there v => simp only [Ctxt.Hom.lift, h v]
      have he : HVector.renameVars f e.args = e.args := by
        rw [renameVars_congr h e.args]
        exact renameVars_self e.args
      simp only [Com.rename, Expr.rename, he, rename_of_forall_eq hl body]

/-- Splicing a block in front of the return of its result is the block. -/
theorem spliceCom_ret_here : {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
    spliceCom c (.ret .here) = c
  | _, _, .ret _ => rfl
  | _, _, .var e body => by
      show Com.var e (spliceCom body (.ret .here)) = _
      rw [spliceCom_ret_here body]

end Rename

/-! ## 2. Identity and composition of block lowerings -/

section Lowerings

variable {d d' d'' d''' : Dialect} [DialectSignature d] [DialectSignature d']
  [DialectSignature d''] [DialectSignature d''']

/-- The whole-program recursion of the identity lowering is the identity. -/
theorem blockLowerCom_id : {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
    (BlockLoweringData.id d).blockLowerCom c = c
  | _, _, .ret _ => rfl
  | _, _, .var e body => by
      show Com.var e (Com.rename (substHeadHom .here) (Com.rename
        (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ _))
        ((BlockLoweringData.id d).blockLowerCom body))) = _
      rw [blockLowerCom_id body]
      exact congrArg (Com.var e) ((rename_rename _ _ body).trans
        (rename_of_forall_eq (fun v => by cases v <;> rfl) body))

/-- **Right unit.** A block lowering followed by the identity lowering is the lowering. -/
theorem compBlock_id (L : BlockLoweringData d d') :
    L.compBlock (BlockLoweringData.id d') = L := by
  cases L
  simp only [BlockLoweringData.compBlock, blockLowerCom_id]
  rfl

/-- The variable map of `L` sends the head variable of `t :: Γ` to the head variable of
    `L.mapTy t :: L.mapCtx Γ`, read along `L.mapCtx_cons`. -/
def HeadVar (L : BlockLoweringData d d') : Prop :=
  ∀ (t : d.Ty) (Γ : Ctxt d),
    (L.mapCtx_cons t Γ ▸ L.mapVar (Var.here : Var (t :: Γ) t) :
      Var (L.mapTy t :: L.mapCtx Γ) (L.mapTy t)) = Var.here

/-- A cast return is the return of the cast variable. -/
theorem eqRec_ret {Γ Δ : Ctxt d} {a : d.Ty} (h : Γ = Δ) (v : Var Γ a) :
    (h ▸ Com.ret v : Com d Δ a) = Com.ret (h ▸ v) := by
  subst h
  rfl

/-- **Left unit.** The identity lowering followed by `L` is `L`, when `L` maps the head
    variable to the head variable. -/
theorem id_compBlock (L : BlockLoweringData d d') (hL : HeadVar L) :
    (BlockLoweringData.id d).compBlock L = L := by
  have key : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t),
      L.blockLowerCom (Com.var e (Com.ret Var.here)) = L.lowerExprBlock e := by
    intro Γ t e
    show spliceCom (L.lowerExprBlock e) (L.mapCtx_cons t Γ ▸ Com.ret (L.mapVar .here)) = _
    rw [eqRec_ret, hL t Γ, spliceCom_ret_here]
  cases L
  simp only [BlockLoweringData.compBlock]
  congr 1
  funext Γ t e
  exact key e

/-- The whole-program recursion of `M` commutes with the block splice: lowering a splice
    splices the lowered block in front of the lowered continuation. -/
def SpliceNatural (M : BlockLoweringData d' d'') : Prop :=
  ∀ {Γ : Ctxt d'} {t s : d'.Ty} (c : Com d' Γ t) (k : Com d' (t :: Γ) s),
    M.blockLowerCom (spliceCom c k) =
      spliceCom (M.blockLowerCom c) (M.mapCtx_cons t Γ ▸ M.blockLowerCom k)

/-- A `▸` cast along `h : a = b` is `HEq` to the uncast term. -/
theorem cast_heq_self {α : Sort _} {F : α → Sort _} {a b : α} (h : a = b) (x : F a) :
    (h ▸ x : F b) ≍ x := by
  subst h
  rfl

/-- The whole-program recursion carries a cast program to a program `HEq` to the
    lowering of the uncast one. -/
theorem blockLowerCom_eqRec_heq (M : BlockLoweringData d' d'') {Γ Δ : Ctxt d'} {s : d'.Ty}
    (h : Γ = Δ) (c : Com d' Γ s) :
    M.blockLowerCom (h ▸ c : Com d' Δ s) ≍ M.blockLowerCom c := by
  subst h
  rfl

/-- **Functoriality of the whole-program recursion.** Under `SpliceNatural M`, the
    recursion of `L.compBlock M` is the recursion of `L` followed by that of `M`. -/
theorem blockLowerCom_compBlock (L : BlockLoweringData d d') (M : BlockLoweringData d' d'')
    (hM : SpliceNatural M) : {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
    (L.compBlock M).blockLowerCom c = M.blockLowerCom (L.blockLowerCom c)
  | _, _, .ret _ => rfl
  | Γ, _, .var (t := bs) e body => by
      show spliceCom (M.blockLowerCom (L.lowerExprBlock e))
          ((L.compBlock M).mapCtx_cons bs Γ ▸ (L.compBlock M).blockLowerCom body) =
        M.blockLowerCom (spliceCom (L.lowerExprBlock e)
          (L.mapCtx_cons bs Γ ▸ L.blockLowerCom body))
      rw [hM]
      congr 1
      apply eq_of_heq
      refine (cast_heq_self (F := fun X => Com d'' X _) _ _).trans ?_
      refine HEq.trans ?_ (cast_heq_self (F := fun X => Com d'' X _) _ _).symm
      rw [blockLowerCom_compBlock L M hM body]
      exact (blockLowerCom_eqRec_heq M _ _).symm

/-- **Associativity**, when the last lowering satisfies `SpliceNatural`. -/
theorem compBlock_assoc (L : BlockLoweringData d d') (M : BlockLoweringData d' d'')
    (N : BlockLoweringData d'' d''') (hN : SpliceNatural N) :
    (L.compBlock M).compBlock N = L.compBlock (M.compBlock N) := by
  simp only [BlockLoweringData.compBlock]
  congr 1
  funext Γ t e
  exact (blockLowerCom_compBlock M N hN _).symm

/-- The identity lowering commutes with the block splice. -/
theorem spliceNatural_id : SpliceNatural (BlockLoweringData.id d) := by
  intro Γ t s c k
  exact (blockLowerCom_id _).trans (by rw [blockLowerCom_id c, blockLowerCom_id k]; rfl)

/-- The identity lowering maps the head variable to the head variable. -/
theorem headVar_id : HeadVar (BlockLoweringData.id d) := fun _ _ => rfl

end Lowerings

/-! ## 3. The operation sum as a coproduct -/

section OpSum

open DialectOpSum (castVar castArgs)

variable {O₁ O₂ : Type} {T : Type} [DialectSignature (⟨O₁, T⟩ : Dialect)]
  [DialectSignature (⟨O₂, T⟩ : Dialect)] {f : Dialect} [DialectSignature f]

/-- The block of an operation of the sum under the copairing: an operation of the left
    summand gets the block of `L₁`, an operation of the right summand the block of `L₂`,
    read along the equalities of the type and context maps. -/
def copairBlock (L₁ : BlockLoweringData ⟨O₁, T⟩ f) (L₂ : BlockLoweringData ⟨O₂, T⟩ f)
    (hTy : ∀ t, L₂.mapTy t = L₁.mapTy t) (hCtx : ∀ Γ, L₂.mapCtx Γ = L₁.mapCtx Γ)
    {Γ : List T} {t : T} : (op : O₁ ⊕ O₂) →
    DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) op = t →
    HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
      (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) op) →
    Com f (L₁.mapCtx Γ) (L₁.mapTy t)
  | .inl o, h, args => L₁.lowerExprBlock ⟨o, h, castArgs args⟩
  | .inr o, h, args =>
      cast (congrArg₂ (Com f) (hCtx Γ) (hTy t)) (L₂.lowerExprBlock ⟨o, h, castArgs args⟩)

/-- **The copairing out of an operation sum.** For block lowerings `L₁` of `d` and `L₂`
    of `e` into `f` with equal type and context maps, the block lowering of
    `Dialect.opSum d e` that lowers the operations of `d` by `L₁` and those of `e` by
    `L₂`; types, contexts and variables are mapped as by `L₁`. -/
def copair (L₁ : BlockLoweringData ⟨O₁, T⟩ f) (L₂ : BlockLoweringData ⟨O₂, T⟩ f)
    (hTy : ∀ t, L₂.mapTy t = L₁.mapTy t) (hCtx : ∀ Γ, L₂.mapCtx Γ = L₁.mapCtx Γ) :
    BlockLoweringData (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) f where
  mapTy := L₁.mapTy
  mapCtx := L₁.mapCtx
  mapCtx_cons := L₁.mapCtx_cons
  mapVar := fun v => L₁.mapVar (castVar v)
  lowerExprBlock := fun e => copairBlock L₁ L₂ hTy hCtx e.op e.retTy_eq e.args

variable (L₁ : BlockLoweringData ⟨O₁, T⟩ f) (L₂ : BlockLoweringData ⟨O₂, T⟩ f)
  (hTy : ∀ t, L₂.mapTy t = L₁.mapTy t) (hCtx : ∀ Γ, L₂.mapCtx Γ = L₁.mapCtx Γ)

/-- The copairing lowers an operation of the left summand by `L₁`. -/
theorem copair_inl {Γ : List T} {t : T} (o : O₁)
    (h : DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inl o) = t)
    (args : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
      (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inl o))) :
    (copair L₁ L₂ hTy hCtx).lowerExprBlock ⟨.inl o, h, args⟩ =
      L₁.lowerExprBlock ⟨o, h, castArgs args⟩ := rfl

/-- The copairing lowers an operation of the right summand by `L₂`. -/
theorem copair_inr {Γ : List T} {t : T} (o : O₂)
    (h : DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inr o) = t)
    (args : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
      (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inr o))) :
    (copair L₁ L₂ hTy hCtx).lowerExprBlock ⟨.inr o, h, args⟩ ≍
      L₂.lowerExprBlock ⟨o, h, castArgs args⟩ :=
  cast_heq _ _

/-- **Uniqueness on operations.** A block lowering out of the operation sum with the type,
    context and variable maps of the copairing, which lowers each operation of the left
    summand as `L₁` and each operation of the right summand as `L₂`, is the copairing. -/
theorem copair_unique (M : BlockLoweringData (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) f)
    (hMTy : M.mapTy = L₁.mapTy) (hMCtx : M.mapCtx = L₁.mapCtx)
    (hMVar : ∀ {Γ : List T} {t : T} (v : Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t),
      M.mapVar v ≍ L₁.mapVar (castVar v))
    (hInl : ∀ {Γ : List T} {t : T} (o : O₁)
      (h : DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inl o) = t)
      (args : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
        (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inl o))),
      M.lowerExprBlock ⟨.inl o, h, args⟩ ≍ L₁.lowerExprBlock ⟨o, h, castArgs args⟩)
    (hInr : ∀ {Γ : List T} {t : T} (o : O₂)
      (h : DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inr o) = t)
      (args : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
        (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inr o))),
      M.lowerExprBlock ⟨.inr o, h, args⟩ ≍ L₂.lowerExprBlock ⟨o, h, castArgs args⟩) :
    M = copair L₁ L₂ hTy hCtx := by
  cases M with
  | mk mapTy mapCtx mapCtx_cons mapVar lowerExprBlock =>
    subst hMTy hMCtx
    have hV : @mapVar = fun {Γ} {t} v => L₁.mapVar (castVar v) := by
      funext Γ t v
      exact eq_of_heq (hMVar v)
    subst hV
    simp only [copair]
    congr 1
    funext Γ t e
    rcases e with ⟨op | op, h, args⟩
    · exact eq_of_heq (hInl op h args)
    · exact eq_of_heq ((hInr op h args).trans (cast_heq _ _).symm)

end OpSum

/-! ## 4. `extendId` as whiskering -/

section Extend

open DialectOpSum (castArgs)
open BlockLoweringExtend (SigMaps sumMapArgs)

variable {O₁ O₁' O₂ : Type} {T T' : Type}
  [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]
  [DialectSignature (⟨O₁', T'⟩ : Dialect)] [DialectSignature (⟨O₂, T'⟩ : Dialect)]
  (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩) (hS : SigMaps O₂ L.mapTy)

/-- **Left whiskering.** On an operation of the left summand, `extendId L` is the block of
    `L` followed by the left injection, that is the composite `L.comp DialectOpSum.inl`. -/
theorem extendId_inl {Γ : List T} {t : T} (o : O₁)
    (h : DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inl o) = t)
    (args : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
      (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inl o))) :
    (L.extendId hS).lowerExprBlock ⟨.inl o, h, args⟩ =
      (L.comp (DialectOpSum.inl (O₂ := O₂))).lowerExprBlock ⟨o, h, castArgs args⟩ := rfl

/-- **Right whiskering by the identity.** On an operation of the right summand,
    `extendId L` is the one-binding block applying the same operation to the mapped
    arguments. -/
theorem extendId_inr {Γ : List T} {t : T} (o : O₂)
    (h : DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inr o) = t)
    (args : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
      (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inr o))) :
    (L.extendId hS).lowerExprBlock ⟨.inr o, h, args⟩ =
      .var ⟨.inr o, (hS.ret_eq o).trans (congrArg L.mapTy h),
        (hS.sig_eq o).symm ▸ sumMapArgs L args⟩ (.ret .here) := rfl

/-- A variable cast twice between dialects over `T` is the variable cast once. -/
theorem castVar_castVar {O O' O'' : Type} :
    {Γ : List T} → {t : T} → (v : Var (d := ⟨O, T⟩) Γ t) →
    DialectOpSum.castVar (O := O') (O' := O'') (DialectOpSum.castVar (O' := O') v) =
      DialectOpSum.castVar v
  | _, _, .here => rfl
  | _, _, .there v => congrArg Var.there (castVar_castVar v)

/-- An argument vector cast twice between dialects over `T` is the vector cast once. -/
theorem castArgs_castArgs {O O' O'' : Type} {Γ : List T} :
    {ts : List T} → (vs : HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts) →
    castArgs (O := O') (O' := O'') (castArgs (O' := O') vs) = castArgs vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => congrArg₂ HVector.cons (castVar_castVar v) (castArgs_castArgs vs)

/-- A variable cast to its own dialect is the variable. -/
theorem castVar_self {O : Type} : {Γ : List T} → {t : T} → (v : Var (d := ⟨O, T⟩) Γ t) →
    DialectOpSum.castVar (O' := O) v = v
  | _, _, .here => rfl
  | _, _, .there v => congrArg Var.there (castVar_self v)

/-- An argument vector cast to its own dialect is the vector. -/
theorem castArgs_self {O : Type} {Γ : List T} :
    {ts : List T} → (vs : HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts) →
    castArgs (O' := O) vs = vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => congrArg₂ HVector.cons (castVar_self v) (castArgs_self vs)

/-- The right component of `extendId L`: the block lowering of `e` into
    `Dialect.opSum d' e` that maps each operation of `e` to itself, with the type,
    context and variable maps of `L`. -/
def extendIdRight : BlockLoweringData ⟨O₂, T⟩ (Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) where
  mapTy := L.mapTy
  mapCtx := L.mapCtx
  mapCtx_cons := L.mapCtx_cons
  mapVar := fun v => DialectOpSum.castVar (L.mapVar (DialectOpSum.castVar v))
  lowerExprBlock := fun e =>
    (L.extendId hS).lowerExprBlock
      ⟨.inr e.op, e.retTy_eq, castArgs (O' := O₁ ⊕ O₂) e.args⟩

/-- **`extendId` as a copairing.** `extendId L` is the copairing of `L` followed by the
    left injection with the identity part `extendIdRight L`. -/
theorem extendId_eq_copair :
    L.extendId hS =
      copair (L.comp (DialectOpSum.inl (O₂ := O₂))) (extendIdRight L hS)
        (fun _ => rfl) (fun _ => rfl) :=
  copair_unique _ _ _ _ (L.extendId hS) rfl rfl (fun _ => HEq.rfl)
    (fun _ _ _ => HEq.rfl)
    (fun o h args => by
      show _ ≍ (L.extendId hS).lowerExprBlock ⟨.inr o, h, castArgs (castArgs args)⟩
      rw [castArgs_castArgs, castArgs_self])

end Extend

/-! ## 5. The identity lowering of a structured program -/

section MapId

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- The identity lowering sends the trip-counter type and the bit type to themselves. -/
theorem regionTypes_id : NFProg.RegionTypes (BlockLoweringData.id d) := ⟨rfl, rfl⟩

variable [DialectDenote d]

/-- **The identity lowering preserves denotation.** A structured program without `call`
    lowered by the identity block lowering denotes, at every fuel, its own results, read
    along `List.map (fun t => t)`. -/
theorem map_id_denote [CallDenote d] (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hc : p.callFree = true) (V : Valuation Γ) :
    (NFProg.map (BlockLoweringData.id d) regionTypes_id p hc (fun v => v)).denote fuel V =
      (p.denote fuel V).map
        (BlockLoweringExtend.transArgs (fun t => t) (fun x => x)) :=
  NFProg.map_denote_of_blockOpTransports (BlockLoweringData.id d) (fun x => x)
    (fun V => V) regionTypes_id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ fuel p hc V

end MapId

end DialectCategory

/-! ## 6. Regions as a category -/

namespace NFPre

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- The empty prefix is a left unit of composition. -/
theorem nil_append {Γ Δ : Ctxt d} (p : NFPre d Γ Δ) : NFPre.nil.append p = p := rfl

/-- The empty prefix is a right unit of composition. -/
theorem append_nil {Γ Δ : Ctxt d} (p : NFPre d Γ Δ) : p.append .nil = p := by
  induction p with
  | nil => rfl
  | var e p ih => exact congrArg (NFPre.var e) ih
  | forLoop count inits body p ih => exact congrArg (NFPre.forLoop count inits body) ih
  | ifThenElse cond thn els p ih => exact congrArg (NFPre.ifThenElse cond thn els) ih

/-- Composition of prefixes is associative. -/
theorem append_assoc {Γ Δ Θ Ξ : Ctxt d} (p : NFPre d Γ Δ) (q : NFPre d Δ Θ)
    (r : NFPre d Θ Ξ) : (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | var e p ih => exact congrArg (NFPre.var e) (ih q)
  | forLoop count inits body p ih =>
      exact congrArg (NFPre.forLoop count inits body) (ih q)
  | ifThenElse cond thn els p ih => exact congrArg (NFPre.ifThenElse cond thn els) (ih q)

/-- Plugging the empty prefix leaves a program unchanged. -/
theorem nil_plug {Γ : Ctxt d} {ts : List d.Ty} (k : NFProg d Γ ts) :
    NFPre.nil.plug k = k := rfl

/-- **Plugging is an action.** Plugging a composite prefix is plugging the second prefix,
    then the first. -/
theorem plug_append {Γ Δ Θ : Ctxt d} {ts : List d.Ty} (p : NFPre d Γ Δ) (q : NFPre d Δ Θ)
    (k : NFProg d Θ ts) : (p.append q).plug k = p.plug (q.plug k) := by
  induction p with
  | nil => rfl
  | var e p ih => exact congrArg (NFProg.var e) (ih q)
  | forLoop count inits body p ih =>
      exact congrArg (NFProg.forLoop count inits body) (ih q)
  | ifThenElse cond thn els p ih => exact congrArg (NFProg.ifThenElse cond thn els) (ih q)

/-- The empty prefix denotes the unit of `Option`. -/
theorem denote_nil [DialectDenoteM d Option] [CallDenote d] (fuel : Nat) {Γ : Ctxt d} (V : Valuation Γ) :
    (NFPre.nil : NFPre d Γ Γ).denote fuel V = some V := rfl

end NFPre

namespace DialectCategory

open CategoryTheory

/-- The contexts of a dialect, as the objects of the category of regions. -/
def RegionCtx (d : Dialect.{0, 0}) : Type := Ctxt d

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **The category of regions**: prefixes `NFPre d Γ Δ` are the morphisms, the empty
    prefix the identity and `NFPre.append` the composition. -/
instance RegionCtx.instCategory : Category (RegionCtx d) where
  Hom Γ Δ := NFPre d Γ Δ
  id _ := NFPre.nil
  comp p q := p.append q
  id_comp _ := rfl
  comp_id := NFPre.append_nil
  assoc := NFPre.append_assoc

/-- **The denotation of regions as a functor into the Kleisli category of `Option`.** A
    context goes to its valuations and a prefix to its denotation at the fuel `fuel`;
    preservation of composition is `NFPre.denote_append`. -/
def regionDenote [DialectDenoteM d Option] [CallDenote d] (fuel : Nat) : RegionCtx d ⥤ KleisliCat Option where
  obj Γ := KleisliCat.mk Option (Valuation (Γ : Ctxt d))
  map p := NFPre.denote fuel p
  map_id _ := rfl
  map_comp p q := funext fun V => NFPre.denote_append fuel p q V

end DialectCategory

end CatCrypt.Crypto.SecureCompilation.VIR
