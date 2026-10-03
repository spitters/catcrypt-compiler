/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCategory
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtendWitness

/-!
# Template lowerings

A lowering frame `LoweringFrame d d'` is the variable part of a block lowering: a type
map, a context map that sends the empty context to the empty context and a cons to a cons,
and the variable map that sends the head to the head and a weakened variable to the
weakening of its image. A frame acts on renamings (`LoweringFrame.mapHom`): a renaming
`f : Γ → Δ` goes to the renaming of `mapCtx Γ` into `mapCtx Δ` that sends `mapVar v` to
`mapVar (f v)`, and every renaming out of `mapCtx Γ` is determined by its values on the
images of `mapVar` (`LoweringFrame.hom_ext`).

An op template assigns to each operation `op` of `d` a program of `d'` over the context
`mapCtx (sig op)`, returning `mapTy (ret op)`. `BlockLoweringData.ofTemplate F T` lowers an
expression `e` by renaming the argument variables of `T e.op` to the images of `e.args`.
Template lowerings commute with renaming (`blockLowerCom_ofTemplate_rename`): they are
natural transformations between the presheaves of programs on the category of contexts and
renamings. Naturality at the weakenings and head substitutions used by `spliceCom` is
`SpliceNatural`, so the left unit and associativity laws of `compBlock` hold on template
lowerings without side conditions, and template lowerings form a category
(`TemplateDialect.instCategory`).

Template lowerings are closed under the constructions on block lowerings: the identity
lowering, `compBlock`, `extendId` and `copair` of template lowerings are template
lowerings, and so are the block forms of the inclusions `DialectOpSum.inl` and
`DialectOpSum.inr`. A partial op template, `none` on the refused operations, gives a
partial block lowering (`PartialBlockLowering.ofTemplate?`). `DerivedToField.lowering` and
its extension `BlockLoweringExtend.Witness.lowering` are template lowerings.

The category of template lowerings is a presentation: no pass of the compilation
pipeline uses its laws. The construction used to define a pipeline lowering is
`BlockLoweringData.ofTemplate`, which defines `gf2ToJasmin` (`VIR/Gf2Dialect.lean`).

## Main definitions

* `DialectCategory.LoweringFrame` — the type, context and variable maps with their laws.
* `DialectCategory.LoweringFrame.mapHom` — the action of a frame on renamings.
* `DialectCategory.LoweringFrame.templateBlock` — the instance of an op template at an
  expression.
* `BlockLoweringData.ofTemplate` — the block lowering of an op template.
* `PartialBlockLowering.ofTemplate?` — the partial block lowering of a partial op template.
* `DialectCategory.LoweringFrame.comp`, `DialectCategory.LoweringFrame.extendId`,
  `DialectCategory.LoweringFrame.copair`, `DialectCategory.castFrame` — the frames of the
  constructions on lowerings.
* `DialectCategory.TemplateDialect` — dialects as the objects of the category of template
  lowerings.

## Main results

* `DialectCategory.LoweringFrame.extendHom_mapVar`, `DialectCategory.LoweringFrame.hom_ext`
  — the universal property of the mapped context.
* `DialectCategory.templateBlock_rename`, `DialectCategory.blockLowerCom_ofTemplate_rename`
  — template lowerings commute with renaming.
* `DialectCategory.spliceNatural_ofTemplate`, `DialectCategory.headVar_ofTemplate` — the
  side conditions of the category laws hold on template lowerings.
* `DialectCategory.ofTemplate_id_comp`, `DialectCategory.ofTemplate_comp_assoc` — the left
  unit and associativity laws on template lowerings.
* `DialectCategory.id_eq_ofTemplate`, `DialectCategory.ofTemplate_comp`,
  `DialectCategory.extendId_ofTemplate`, `DialectCategory.copair_ofTemplate`,
  `DialectCategory.idComp_inl_eq_ofTemplate`, `DialectCategory.idComp_inr_eq_ofTemplate` —
  closure of template lowerings.
* `DialectCategory.mapVar_heq_of_frames` — the variable map of a frame is determined by its
  type and context maps.
* `DialectCategory.templateBlock?_rename`, `DialectCategory.spliceNatural_ofTemplate?` —
  naturality of partial template lowerings.
* `DialectCategory.TemplateDialect.instCategory` — the category of template lowerings.
* `DialectCategory.derivedToField_eq_ofTemplate`, `DialectCategory.witness_eq_ofTemplate`
  — the derived-to-field lowering and its extension are template lowerings.
* `DialectCategory.rename_spliceCom`, `DialectCategory.spliceCom_assoc` — renaming
  distributes over the block splice, and the block splice is associative.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)
open FieldDialectBlockDescent (BlockLoweringData spliceCom substHeadHom)
open BlockLoweringCPS (consHom castHom)

namespace DialectCategory

/-! ## 1. Casts, renaming and the block splice -/

section Splice

variable {d : Dialect} [DialectSignature d]

omit [DialectSignature d] in
/-- Two variable casts compose to the cast along the composite equality. -/
theorem castHom_castHom {Γ₁ Γ₂ Γ₃ : Ctxt d} (h₁ : Γ₁ = Γ₂) (h₂ : Γ₂ = Γ₃) {t : d.Ty}
    (v : Var Γ₁ t) : castHom h₂ (castHom h₁ v) = castHom (h₁.trans h₂) v := by
  subst h₁ h₂
  rfl

omit [DialectSignature d] in
/-- A variable cast forth and back is the variable. -/
theorem castHom_symm_castHom {Γ₁ Γ₂ : Ctxt d} (h : Γ₁ = Γ₂) {t : d.Ty} (v : Var Γ₁ t) :
    castHom h.symm (castHom h v) = v := by
  subst h
  rfl

/-- A cast program is the program renamed by the variable cast. -/
theorem eqRec_eq_rename {Γ₁ Γ₂ : Ctxt d} {s : d.Ty} (h : Γ₁ = Γ₂) (c : Com d Γ₁ s) :
    (h ▸ c : Com d Γ₂ s) = Com.rename (castHom h) c := by
  subst h
  exact (rename_of_forall_eq (fun _ => rfl) c).symm

/-- Renaming commutes with a cast of the return type. -/
theorem rename_eqRec_ty {Γ Γ' : Ctxt d} {a b : d.Ty} (h : a = b) (ρ : Ctxt.Hom Γ Γ')
    (c : Com d Γ a) :
    Com.rename ρ (h ▸ c : Com d Γ b) = (h ▸ Com.rename ρ c : Com d Γ' b) := by
  subst h
  rfl

/-- Renaming distributes over the block splice. -/
theorem rename_spliceCom : {Γ Δ : Ctxt d} → {t s : d.Ty} → (ρ : Ctxt.Hom Γ Δ) →
    (c : Com d Γ t) → (k : Com d (t :: Γ) s) →
    Com.rename ρ (spliceCom c k) = spliceCom (Com.rename ρ c) (Com.rename (Ctxt.Hom.lift ρ) k)
  | _, _, _, _, ρ, .ret v, k => by
      show Com.rename ρ (Com.rename (substHeadHom v) k)
        = Com.rename (substHeadHom (ρ v)) (Com.rename (Ctxt.Hom.lift ρ) k)
      rw [rename_rename, rename_rename]
      exact rename_congr (fun w => by cases w <;> rfl) k
  | _, _, _, _, ρ, .var (t := bs) e body, k => by
      show Com.var (Expr.rename ρ e)
          (Com.rename (Ctxt.Hom.lift ρ)
            (spliceCom body (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) k)))
        = Com.var (Expr.rename ρ e)
          (spliceCom (Com.rename (Ctxt.Hom.lift ρ) body)
            (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs))
              (Com.rename (Ctxt.Hom.lift ρ) k)))
      rw [rename_spliceCom (Ctxt.Hom.lift ρ) body, rename_rename, rename_rename]
      congr 2
      exact rename_congr (fun w => by
        cases w with
        | here => rfl
        | there w => cases w <;> rfl) k

/-- **Associativity of the block splice.** Splicing `k` after the splice of `a` and `b` is
    splicing, after `a`, the splice of `b` and the weakened `k`. -/
theorem spliceCom_assoc : {Γ : Ctxt d} → {t u s : d.Ty} → (a : Com d Γ t) →
    (b : Com d (t :: Γ) u) → (k : Com d (u :: Γ) s) →
    spliceCom (spliceCom a b) k =
      spliceCom a (spliceCom b (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ t)) k))
  | _, _, _, _, .ret v, b, k => by
      show spliceCom (Com.rename (substHeadHom v) b) k = Com.rename (substHeadHom v) _
      rw [rename_spliceCom, rename_rename]
      congr 1
      exact (rename_of_forall_eq (fun w => by cases w <;> rfl) k).symm
  | _, _, _, _, .var (t := bs) e a, b, k => by
      show Com.var e (spliceCom (spliceCom a _) _) = Com.var e (spliceCom a _)
      rw [spliceCom_assoc a, rename_spliceCom, rename_rename, rename_rename]
      congr 3
      exact rename_congr (fun w => by
        cases w with
        | here => rfl
        | there w => rfl) k

end Splice

/-! ## 2. Lowering frames -/

/-- **A lowering frame** from `d` to `d'`: a type map, a context map sending the empty
    context to the empty context and a cons to a cons, and a variable map sending the head
    variable to the head variable and a weakened variable to the weakening of its image,
    both read along `mapCtx_cons`. -/
structure LoweringFrame (d d' : Dialect) [DialectSignature d] [DialectSignature d'] where
  /-- Type map. -/
  mapTy : d.Ty → d'.Ty
  /-- Context map. -/
  mapCtx : Ctxt d → Ctxt d'
  /-- The empty context maps to the empty context. -/
  mapCtx_nil : mapCtx [] = []
  /-- `cons`-compatibility of the context map. -/
  mapCtx_cons : ∀ (t : d.Ty) (Γ : Ctxt d), mapCtx (t :: Γ) = mapTy t :: mapCtx Γ
  /-- Variable map. -/
  mapVar : ∀ {Γ : Ctxt d} {t : d.Ty}, Var Γ t → Var (mapCtx Γ) (mapTy t)
  /-- The head variable maps to the head variable. -/
  mapVar_here : ∀ (t : d.Ty) (Γ : Ctxt d),
    castHom (mapCtx_cons t Γ) (mapVar (Var.here : Var (t :: Γ) t)) = Var.here
  /-- A weakened variable maps to the weakening of its image. -/
  mapVar_there : ∀ (s : d.Ty) (Γ : Ctxt d) {t : d.Ty} (v : Var Γ t),
    castHom (mapCtx_cons s Γ) (mapVar (Var.there v : Var (s :: Γ) t)) = Var.there (mapVar v)

namespace LoweringFrame

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']
  (F : LoweringFrame d d')

/-- The renaming out of a mapped context determined by its values on mapped variables:
    `mapVar v` goes to `g v`. -/
def extendHom {Δ : Ctxt d'} : {Γ : Ctxt d} → (∀ {t : d.Ty}, Var Γ t → Var Δ (F.mapTy t)) →
    Ctxt.Hom (F.mapCtx Γ) Δ
  | [], _ => fun w => nomatch castHom F.mapCtx_nil w
  | t :: Γ, g => fun w =>
      consHom (extendHom (fun v => g (Var.there v))) (g Var.here) (castHom (F.mapCtx_cons t Γ) w)

/-- `extendHom g` sends `mapVar v` to `g v`. -/
theorem extendHom_mapVar {Δ : Ctxt d'} : {Γ : Ctxt d} →
    (g : ∀ {t : d.Ty}, Var Γ t → Var Δ (F.mapTy t)) → {t : d.Ty} → (v : Var Γ t) →
    F.extendHom g (F.mapVar v) = g v
  | t :: Γ, g, _, .here => by
      show consHom _ (g Var.here) (castHom (F.mapCtx_cons t Γ) (F.mapVar Var.here)) = _
      rw [F.mapVar_here]
      rfl
  | s :: Γ, g, _, .there v => by
      show consHom _ _ (castHom (F.mapCtx_cons s Γ) (F.mapVar (Var.there v))) = _
      rw [F.mapVar_there]
      exact extendHom_mapVar (fun v => g (Var.there v)) v

/-- **Extensionality.** Two renamings out of a mapped context that agree on the mapped
    variables agree everywhere. -/
theorem hom_ext {Δ : Ctxt d'} : {Γ : Ctxt d} → (h₁ h₂ : Ctxt.Hom (F.mapCtx Γ) Δ) →
    (∀ {t : d.Ty} (v : Var Γ t), h₁ (F.mapVar v) = h₂ (F.mapVar v)) →
    ∀ {s : d'.Ty} (w : Var (F.mapCtx Γ) s), h₁ w = h₂ w
  | [], _, _, _, _, w => nomatch castHom F.mapCtx_nil w
  | t :: Γ, h₁, h₂, H, _, w => by
      rw [← castHom_symm_castHom (F.mapCtx_cons t Γ) w]
      generalize castHom (F.mapCtx_cons t Γ) w = w'
      cases w' with
      | here =>
          have hv : castHom (F.mapCtx_cons t Γ).symm Var.here =
              F.mapVar (Var.here : Var (t :: Γ) t) := by
            rw [← F.mapVar_here t Γ, castHom_symm_castHom]
          rw [hv]
          exact H _
      | there u =>
          refine hom_ext
            (fun u => h₁ (castHom (F.mapCtx_cons t Γ).symm (Var.there u)))
            (fun u => h₂ (castHom (F.mapCtx_cons t Γ).symm (Var.there u))) ?_ u
          intro t' v
          have hv : castHom (F.mapCtx_cons t Γ).symm (Var.there (F.mapVar v)) =
              F.mapVar (Var.there v : Var (t :: Γ) t') := by
            rw [← F.mapVar_there t Γ v, castHom_symm_castHom]
          show h₁ _ = h₂ _
          rw [hv]
          exact H _

/-- Two renamings out of a mapped context that agree on the mapped variables rename a
    program equally. -/
theorem rename_ext {Δ : Ctxt d'} {Γ : Ctxt d} {s : d'.Ty} (h₁ h₂ : Ctxt.Hom (F.mapCtx Γ) Δ)
    (H : ∀ {t : d.Ty} (v : Var Γ t), h₁ (F.mapVar v) = h₂ (F.mapVar v))
    (c : Com d' (F.mapCtx Γ) s) : Com.rename h₁ c = Com.rename h₂ c :=
  rename_congr (fun w => F.hom_ext h₁ h₂ H w) c

/-- **The action of a frame on renamings.** A renaming `f : Γ → Δ` goes to the renaming
    of `mapCtx Γ` into `mapCtx Δ` sending `mapVar v` to `mapVar (f v)`. -/
def mapHom {Γ Δ : Ctxt d} (f : Ctxt.Hom Γ Δ) : Ctxt.Hom (F.mapCtx Γ) (F.mapCtx Δ) :=
  F.extendHom (fun v => F.mapVar (f v))

/-- `mapHom f` sends `mapVar v` to `mapVar (f v)`. -/
theorem mapHom_mapVar {Γ Δ : Ctxt d} (f : Ctxt.Hom Γ Δ) {t : d.Ty} (v : Var Γ t) :
    F.mapHom f (F.mapVar v) = F.mapVar (f v) :=
  F.extendHom_mapVar _ v

/-- An op template over a frame: for each operation `op`, a program of `d'` over the
    mapped argument context `mapCtx (sig op)` returning the mapped result type. -/
abbrev Template : Type _ :=
  (op : d.Op) → Com d' (F.mapCtx (DialectSignature.sig op)) (F.mapTy (DialectSignature.ret op))

end LoweringFrame

/-- An argument vector as a renaming out of its type list: position `i` goes to the
    `i`-th argument. -/
def argsHom {d : Dialect} {Γ : Ctxt d} : {ts : List d.Ty} → HVector (fun t => Var Γ t) ts →
    Ctxt.Hom ts Γ
  | [], .nil => fun w => nomatch w
  | _ :: _, .cons a as => fun w => match w with
    | .here => a
    | .there w => argsHom as w

/-- The renaming of a renamed argument vector is the composite. -/
theorem argsHom_renameVars {d : Dialect} {Γ Γ' : Ctxt d} (f : Ctxt.Hom Γ Γ') :
    {ts : List d.Ty} → (as : HVector (fun t => Var Γ t) ts) → {t : d.Ty} → (w : Var ts t) →
    argsHom (HVector.renameVars f as) w = f (argsHom as w)
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ as, _, .there w => argsHom_renameVars f as w

namespace LoweringFrame

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']
  (F : LoweringFrame d d')

/-- **The instance of an op template at an expression.** The program `T e.op` under the
    renaming that sends its argument variables to the images of `e.args`. -/
def templateBlock (T : F.Template) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) :
    Com d' (F.mapCtx Γ) (F.mapTy t) :=
  congrArg F.mapTy e.retTy_eq ▸ Com.rename (F.mapHom (argsHom e.args)) (T e.op)

end LoweringFrame

/-- **The block lowering of an op template.** Types, contexts and variables are mapped by
    the frame `F`, and an expression `e` becomes the instance of `T e.op` at the arguments
    of `e`. -/
@[reducible] def _root_.CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent.BlockLoweringData.ofTemplate
    {d d' : Dialect} [DialectSignature d] [DialectSignature d']
    (F : LoweringFrame d d') (T : F.Template) : BlockLoweringData d d' where
  mapTy := F.mapTy
  mapCtx := F.mapCtx
  mapCtx_cons := F.mapCtx_cons
  mapVar := F.mapVar
  lowerExprBlock := fun e => F.templateBlock T e

/-! ## 3. Naturality of template lowerings -/

section Naturality

variable {d d' d'' d''' : Dialect} [DialectSignature d] [DialectSignature d']
  [DialectSignature d''] [DialectSignature d''']
  (F : LoweringFrame d d') (T : F.Template)

/-- **The instance of a template commutes with renaming.** -/
theorem templateBlock_rename {Γ Δ : Ctxt d} {t : d.Ty} (f : Ctxt.Hom Γ Δ) (e : Expr d Γ t) :
    F.templateBlock T (e.rename f) = Com.rename (F.mapHom f) (F.templateBlock T e) := by
  rcases e with ⟨op, h, args⟩
  subst h
  show Com.rename (F.mapHom (argsHom (HVector.renameVars f args))) (T op) =
    Com.rename (F.mapHom f) (Com.rename (F.mapHom (argsHom args)) (T op))
  rw [rename_rename]
  refine F.rename_ext _ _ (fun v => ?_) _
  simp only [LoweringFrame.mapHom_mapVar, argsHom_renameVars]

/-- **Template lowerings commute with renaming.** The whole-program recursion of
    `ofTemplate F T` carries a renamed program to the lowered program renamed by
    `F.mapHom`. -/
theorem blockLowerCom_ofTemplate_rename : {Γ Δ : Ctxt d} → {t : d.Ty} →
    (f : Ctxt.Hom Γ Δ) → (c : Com d Γ t) →
    (BlockLoweringData.ofTemplate F T).blockLowerCom (Com.rename f c) =
      Com.rename (F.mapHom f) ((BlockLoweringData.ofTemplate F T).blockLowerCom c)
  | _, _, _, f, .ret v => by
      show Com.ret (F.mapVar (f v)) = Com.ret (F.mapHom f (F.mapVar v))
      rw [F.mapHom_mapVar]
  | Γ, Δ, _, f, .var (t := bs) e body => by
      show spliceCom (F.templateBlock T (e.rename f))
          ((BlockLoweringData.ofTemplate F T).mapCtx_cons bs Δ ▸
            (BlockLoweringData.ofTemplate F T).blockLowerCom (Com.rename f.lift body)) =
        Com.rename (F.mapHom f) (spliceCom (F.templateBlock T e)
          ((BlockLoweringData.ofTemplate F T).mapCtx_cons bs Γ ▸
            (BlockLoweringData.ofTemplate F T).blockLowerCom body))
      rw [rename_spliceCom, templateBlock_rename, blockLowerCom_ofTemplate_rename,
        eqRec_eq_rename, eqRec_eq_rename, rename_rename, rename_rename]
      congr 1
      refine F.rename_ext _ _ (fun v => ?_) _
      cases v with
      | here =>
          show castHom _ (F.mapHom f.lift (F.mapVar Var.here)) =
            Ctxt.Hom.lift (F.mapHom f) (castHom _ (F.mapVar Var.here))
          rw [F.mapHom_mapVar, F.mapVar_here]
          exact F.mapVar_here bs Δ
      | there u =>
          show castHom _ (F.mapHom f.lift (F.mapVar (Var.there u))) =
            Ctxt.Hom.lift (F.mapHom f) (castHom _ (F.mapVar (Var.there u)))
          rw [F.mapHom_mapVar, F.mapVar_there]
          show castHom _ (F.mapVar (Var.there (f u))) = Var.there (F.mapHom f (F.mapVar u))
          rw [F.mapVar_there, F.mapHom_mapVar]

/-- **Template lowerings are natural for the block splice.** -/
theorem spliceNatural_ofTemplate : SpliceNatural (BlockLoweringData.ofTemplate F T) := by
  intro Γ t s c k
  induction c generalizing s with
  | ret v =>
      show (BlockLoweringData.ofTemplate F T).blockLowerCom (Com.rename (substHeadHom v) k) =
        Com.rename (substHeadHom (F.mapVar v))
          ((BlockLoweringData.ofTemplate F T).mapCtx_cons _ _ ▸
            (BlockLoweringData.ofTemplate F T).blockLowerCom k)
      rw [blockLowerCom_ofTemplate_rename, eqRec_eq_rename, rename_rename]
      refine F.rename_ext _ _ (fun w => ?_) _
      cases w with
      | here =>
          show F.mapHom _ (F.mapVar Var.here) = substHeadHom _ (castHom _ (F.mapVar Var.here))
          rw [F.mapHom_mapVar, F.mapVar_here]
          rfl
      | there u =>
          show F.mapHom _ (F.mapVar (Var.there u)) =
            substHeadHom _ (castHom _ (F.mapVar (Var.there u)))
          rw [F.mapHom_mapVar, F.mapVar_there]
          rfl
  | var e body ih =>
      rename_i Γ₀ bs r
      show spliceCom (F.templateBlock T e)
          ((BlockLoweringData.ofTemplate F T).mapCtx_cons bs Γ₀ ▸
            (BlockLoweringData.ofTemplate F T).blockLowerCom
              (spliceCom body (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne Γ₀ bs)) k))) =
        spliceCom (spliceCom (F.templateBlock T e)
            ((BlockLoweringData.ofTemplate F T).mapCtx_cons bs Γ₀ ▸
              (BlockLoweringData.ofTemplate F T).blockLowerCom body))
          ((BlockLoweringData.ofTemplate F T).mapCtx_cons r Γ₀ ▸
            (BlockLoweringData.ofTemplate F T).blockLowerCom k)
      rw [ih, spliceCom_assoc, blockLowerCom_ofTemplate_rename]
      congr 1
      simp only [eqRec_eq_rename, rename_spliceCom, rename_rename]
      congr 1
      refine F.rename_ext _ _ (fun w => ?_) _
      cases w with
      | here =>
          rw [F.mapHom_mapVar]
          show Ctxt.Hom.lift (castHom _) (castHom _ (F.mapVar Var.here)) =
            Ctxt.Hom.lift _ (castHom _ (F.mapVar Var.here))
          rw [F.mapVar_here, F.mapVar_here]
          rfl
      | there u =>
          rw [F.mapHom_mapVar]
          show Ctxt.Hom.lift (castHom _) (castHom _ (F.mapVar (Var.there (Var.there u)))) =
            Ctxt.Hom.lift _ (castHom _ (F.mapVar (Var.there u)))
          rw [F.mapVar_there, F.mapVar_there]
          show Var.there (castHom _ (F.mapVar (Var.there u))) =
            Var.there (Var.there (F.mapVar u))
          rw [F.mapVar_there]

/-- **Template lowerings map the head variable to the head variable.** -/
theorem headVar_ofTemplate : HeadVar (BlockLoweringData.ofTemplate F T) :=
  F.mapVar_here

/-- **Left unit on template lowerings.** -/
theorem ofTemplate_id_comp :
    (BlockLoweringData.id d).compBlock (BlockLoweringData.ofTemplate F T) =
      BlockLoweringData.ofTemplate F T :=
  id_compBlock _ (headVar_ofTemplate F T)

/-- **Associativity on template lowerings.** Three block lowerings, the last one a
    template lowering, compose associatively. -/
theorem ofTemplate_comp_assoc (L : BlockLoweringData d d') (M : BlockLoweringData d' d'')
    (G : LoweringFrame d'' d''') (S : G.Template) :
    (L.compBlock M).compBlock (BlockLoweringData.ofTemplate G S) =
      L.compBlock (M.compBlock (BlockLoweringData.ofTemplate G S)) :=
  compBlock_assoc _ _ _ (spliceNatural_ofTemplate G S)

end Naturality

/-! ## 4. Closure of template lowerings -/

section Closure

namespace LoweringFrame

variable {d d' d'' : Dialect} [DialectSignature d] [DialectSignature d']
  [DialectSignature d'']

/-- The variable map carries a cast variable to the cast of its image. -/
theorem mapVar_castHom (F : LoweringFrame d d') {Γ₁ Γ₂ : Ctxt d} (h : Γ₁ = Γ₂) {t : d.Ty}
    (v : Var Γ₁ t) : F.mapVar (castHom h v) = castHom (congrArg F.mapCtx h) (F.mapVar v) := by
  subst h
  rfl

/-- The image of the head variable is the head variable, cast back along `mapCtx_cons`. -/
theorem mapVar_here_eq (F : LoweringFrame d d') (t : d.Ty) (Γ : Ctxt d) :
    F.mapVar (Var.here : Var (t :: Γ) t) = castHom (F.mapCtx_cons t Γ).symm Var.here := by
  rw [← F.mapVar_here t Γ, castHom_symm_castHom]

/-- The image of a weakened variable is the weakened image, cast back along
    `mapCtx_cons`. -/
theorem mapVar_there_eq (F : LoweringFrame d d') (s : d.Ty) (Γ : Ctxt d) {t : d.Ty}
    (v : Var Γ t) :
    F.mapVar (Var.there v : Var (s :: Γ) t) =
      castHom (F.mapCtx_cons s Γ).symm (Var.there (F.mapVar v)) := by
  rw [← F.mapVar_there s Γ v, castHom_symm_castHom]

/-- **The composite frame**: type, context and variable maps compose as functions. -/
def comp (F : LoweringFrame d d') (G : LoweringFrame d' d'') : LoweringFrame d d'' where
  mapTy := G.mapTy ∘ F.mapTy
  mapCtx := G.mapCtx ∘ F.mapCtx
  mapCtx_nil := (congrArg G.mapCtx F.mapCtx_nil).trans G.mapCtx_nil
  mapCtx_cons := fun t Γ => (congrArg G.mapCtx (F.mapCtx_cons t Γ)).trans (G.mapCtx_cons _ _)
  mapVar := fun v => G.mapVar (F.mapVar v)
  mapVar_here := fun t Γ => by
    show castHom _ (G.mapVar (F.mapVar Var.here)) = Var.here
    rw [F.mapVar_here_eq, G.mapVar_castHom, castHom_castHom]
    exact G.mapVar_here _ _
  mapVar_there := fun s Γ t v => by
    show castHom _ (G.mapVar (F.mapVar (Var.there v))) = Var.there (G.mapVar (F.mapVar v))
    rw [F.mapVar_there_eq, G.mapVar_castHom, castHom_castHom]
    exact G.mapVar_there _ _ _

end LoweringFrame

variable {d d' d'' : Dialect} [DialectSignature d] [DialectSignature d']
  [DialectSignature d'']

/-- **Composition of template lowerings.** The composite of two template lowerings is the
    template lowering over the composite frame whose template lowers each template of the
    first by the second. -/
theorem ofTemplate_comp (F : LoweringFrame d d') (T : F.Template) (G : LoweringFrame d' d'')
    (S : G.Template) :
    (BlockLoweringData.ofTemplate F T).compBlock (BlockLoweringData.ofTemplate G S) =
      BlockLoweringData.ofTemplate (F.comp G)
        (fun op => (BlockLoweringData.ofTemplate G S).blockLowerCom (T op)) := by
  simp only [BlockLoweringData.compBlock]
  congr 1
  funext Γ t e
  rcases e with ⟨op, h, args⟩
  subst h
  show (BlockLoweringData.ofTemplate G S).blockLowerCom
      (Com.rename (F.mapHom (argsHom args)) (T op)) =
    Com.rename ((F.comp G).mapHom (argsHom args))
      ((BlockLoweringData.ofTemplate G S).blockLowerCom (T op))
  rw [blockLowerCom_ofTemplate_rename]
  refine (F.comp G).rename_ext _ _ (fun v => ?_) _
  show G.mapHom (F.mapHom (argsHom args)) (G.mapVar (F.mapVar v)) =
    (F.comp G).mapHom (argsHom args) ((F.comp G).mapVar v)
  rw [LoweringFrame.mapHom_mapVar, LoweringFrame.mapHom_mapVar, LoweringFrame.mapHom_mapVar]
  rfl

/-- The argument vector of the variables of `ts`, in order. -/
def idArgs {d : Dialect} : (ts : List d.Ty) → HVector (fun t => Var ts t) ts
  | [] => .nil
  | _ :: ts => .cons Var.here (HVector.renameVars (Ctxt.Hom.weakenOne ts _) (idArgs ts))

omit [DialectSignature d] in
/-- The renaming of the identity argument vector is the identity. -/
theorem argsHom_idArgs : (ts : List d.Ty) → {t : d.Ty} → (w : Var ts t) →
    argsHom (idArgs ts) w = w
  | _ :: _, _, .here => rfl
  | _ :: ts, _, .there w => by
      show argsHom (HVector.renameVars (Ctxt.Hom.weakenOne ts _) (idArgs ts)) w = Var.there w
      rw [argsHom_renameVars, argsHom_idArgs]
      rfl

omit [DialectSignature d] in
/-- An argument vector is determined by its renaming. -/
theorem argsHom_inj {Γ : Ctxt d} : {ts : List d.Ty} → (as bs : HVector (fun t => Var Γ t) ts) →
    (∀ {t : d.Ty} (w : Var ts t), argsHom as w = argsHom bs w) → as = bs
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons a as, .cons b bs, H => by
      have hab : a = b := H Var.here
      rw [hab, argsHom_inj as bs (fun w => H (Var.there w))]

omit [DialectSignature d] in
/-- The identity argument vector renamed by an argument vector is that vector. -/
theorem renameVars_idArgs {Γ : Ctxt d} {ts : List d.Ty} (as : HVector (fun t => Var Γ t) ts) :
    HVector.renameVars (argsHom as) (idArgs ts) = as :=
  argsHom_inj _ _ fun w => by rw [argsHom_renameVars, argsHom_idArgs]

namespace LoweringFrame

/-- An argument vector carried by the variable map. -/
def mapArgs (F : LoweringFrame d d') {Γ : Ctxt d} : {ts : List d.Ty} →
    HVector (fun t => Var Γ t) ts → HVector (fun t => Var (F.mapCtx Γ) t) (ts.map F.mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (F.mapVar v) (mapArgs F vs)

/-- The mapped argument vector of a renamed vector is the mapped vector renamed by
    `mapHom`. -/
theorem mapArgs_renameVars (F : LoweringFrame d d') {Γ Δ : Ctxt d} (f : Ctxt.Hom Γ Δ) :
    {ts : List d.Ty} → (as : HVector (fun t => Var Γ t) ts) →
    F.mapArgs (HVector.renameVars f as) = HVector.renameVars (F.mapHom f) (F.mapArgs as)
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show HVector.cons (F.mapVar (f v)) (F.mapArgs (HVector.renameVars f vs)) =
        HVector.cons (F.mapHom f (F.mapVar v)) (HVector.renameVars (F.mapHom f) (F.mapArgs vs))
      rw [F.mapHom_mapVar, mapArgs_renameVars F f vs]

/-- The instance renaming of an argument vector carries the mapped identity vector to the
    mapped argument vector. -/
theorem renameVars_mapArgs_idArgs (F : LoweringFrame d d') {Γ : Ctxt d} {ts : List d.Ty}
    (as : HVector (fun t => Var Γ t) ts) :
    HVector.renameVars (F.mapHom (argsHom as)) (F.mapArgs (idArgs ts)) = F.mapArgs as := by
  rw [← mapArgs_renameVars, renameVars_idArgs]

end LoweringFrame

omit [DialectSignature d] in
/-- Renaming an argument vector commutes with a cast of its type list. -/
theorem renameVars_eqRec {Γ Δ : Ctxt d} (ρ : Ctxt.Hom Γ Δ) {ts ts' : List d.Ty} (h : ts = ts')
    (as : HVector (fun t => Var Γ t) ts) :
    HVector.renameVars ρ (h ▸ as : HVector (fun t => Var Γ t) ts') =
      (h ▸ HVector.renameVars ρ as : HVector (fun t => Var Δ t) ts') := by
  subst h
  rfl

end Closure

/-! ## 5. Template lowerings and the operation sum -/

section OpSum

open DialectOpSum (castVar castArgs)
open BlockLoweringExtend (SigMaps sumMapArgs)

variable {O O' : Type} {T : Type} [DialectSignature (⟨O, T⟩ : Dialect)]
  [DialectSignature (⟨O', T⟩ : Dialect)]

omit [DialectSignature (⟨O, T⟩ : Dialect)] [DialectSignature (⟨O', T⟩ : Dialect)] in
/-- A variable cast is a variable cast of the other dialect. -/
theorem castHom_castVar {Γ₁ Γ₂ : List T} (h : Γ₁ = Γ₂) {t : T} (v : Var (d := ⟨O, T⟩) Γ₁ t) :
    castHom h (castVar (O' := O') v) = castVar (O' := O') (castHom h v) := by
  subst h
  rfl

omit [DialectSignature (⟨O, T⟩ : Dialect)] [DialectSignature (⟨O', T⟩ : Dialect)] in
/-- The renaming of a cast argument vector at a cast variable. -/
theorem argsHom_castArgs {Γ : List T} : {ts : List T} →
    (as : HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts) → {t : T} →
    (w : Var (d := ⟨O, T⟩) ts t) →
    argsHom (castArgs (O' := O') as) (castVar (O' := O') w) = castVar (O' := O') (argsHom as w)
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ as, _, .there w => argsHom_castArgs as w

omit [DialectSignature (⟨O, T⟩ : Dialect)] [DialectSignature (⟨O', T⟩ : Dialect)] in
/-- Casting a renamed argument vector renames the cast vector by the conjugate
    renaming. -/
theorem castArgs_renameVars {Γ Δ : List T} (ρ : Ctxt.Hom (d := ⟨O, T⟩) Γ Δ) :
    {ts : List T} → (as : HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts) →
    castArgs (O' := O') (HVector.renameVars ρ as) =
      HVector.renameVars (d := ⟨O', T⟩)
        (fun v => castVar (O' := O') (ρ (castVar (O' := O) v))) (castArgs (O' := O') as)
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show HVector.cons (castVar (O' := O') (ρ v)) (castArgs (HVector.renameVars ρ vs)) =
        HVector.cons (castVar (O' := O') (ρ (castVar (O' := O) (castVar (O' := O') v)))) _
      rw [castVar_castVar, castVar_self, castArgs_renameVars ρ vs]

omit [DialectSignature (⟨O, T⟩ : Dialect)] [DialectSignature (⟨O', T⟩ : Dialect)] in
/-- The conjugate of a lifted renaming by the variable casts is the lift of the
    conjugate. -/
theorem castVar_lift {Γ Δ : List T} {s : T} (ρ : Ctxt.Hom (d := ⟨O, T⟩) Γ Δ) :
    {t : T} → (v : Var (d := ⟨O', T⟩) (s :: Γ) t) →
    castVar (O' := O') (Ctxt.Hom.lift (s := s) ρ (castVar (O' := O) v)) =
      Ctxt.Hom.lift (d := ⟨O', T⟩) (fun w => castVar (O' := O') (ρ (castVar (O' := O) w))) v
  | _, .here => rfl
  | _, .there _ => rfl

variable {O₁ O₂ : Type} [DialectSignature (⟨O₁, T⟩ : Dialect)]
  [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- The left inclusion commutes with renaming, up to the conjugation of the renaming by
    the variable casts. -/
theorem inl_lowerCom_rename : {Γ Δ : List T} → {t : T} → (ρ : Ctxt.Hom (d := ⟨O₁, T⟩) Γ Δ) →
    (c : Com ⟨O₁, T⟩ Γ t) →
    (DialectOpSum.inl (O₂ := O₂)).lowerCom (Com.rename ρ c) =
      Com.rename (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)
        (fun v => castVar (O' := O₁ ⊕ O₂) (ρ (castVar (O' := O₁) v)))
        ((DialectOpSum.inl (O₂ := O₂)).lowerCom c)
  | _, _, _, ρ, .ret v => by
      show Com.ret (castVar (O' := O₁ ⊕ O₂) (ρ v)) =
        Com.ret (castVar (O' := O₁ ⊕ O₂) (ρ (castVar (O' := O₁) (castVar (O' := O₁ ⊕ O₂) v))))
      rw [castVar_castVar, castVar_self]
  | _, _, _, ρ, .var e body => by
      show Com.var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) _ _ = Com.var _ _
      congr 1
      · show (⟨Sum.inl e.op, e.retTy_eq, castArgs (HVector.renameVars ρ e.args)⟩ :
            Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) _ _) =
          ⟨Sum.inl e.op, e.retTy_eq, HVector.renameVars _ (castArgs e.args)⟩
        rw [castArgs_renameVars]
      · show (DialectOpSum.inl (O₂ := O₂)).lowerCom (Com.rename ρ.lift body) =
          Com.rename (Ctxt.Hom.lift _) ((DialectOpSum.inl (O₂ := O₂)).lowerCom body)
        rw [inl_lowerCom_rename]
        exact rename_congr (fun v => castVar_lift (O' := O₁ ⊕ O₂) ρ v) _

/-- **The cast frame** between two dialects over `T`: types and contexts are unchanged and
    variables are read through `castVar`. -/
@[reducible] def castFrame (O O' : Type) (T : Type) [DialectSignature (⟨O, T⟩ : Dialect)]
    [DialectSignature (⟨O', T⟩ : Dialect)] : LoweringFrame ⟨O, T⟩ ⟨O', T⟩ where
  mapTy := fun t => t
  mapCtx := fun Γ => Γ
  mapCtx_nil := rfl
  mapCtx_cons := fun _ _ => rfl
  mapVar := castVar
  mapVar_here := fun _ _ => rfl
  mapVar_there := fun _ _ _ _ => rfl

omit [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)] in
/-- The instance renaming of the cast frame carries the cast identity vector to the cast
    argument vector. -/
theorem renameVars_castArgs_idArgs {Γ : List T} {ts : List T}
    (as : HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts) :
    HVector.renameVars ((castFrame O O' T).mapHom (argsHom as))
      (castArgs (O' := O') (idArgs (d := ⟨O, T⟩) ts)) = castArgs as := by
  refine argsHom_inj _ _ fun w => ?_
  obtain ⟨w₀, rfl⟩ : ∃ w₀ : Var (d := ⟨O, T⟩) ts _, w = castVar (O' := O') w₀ :=
    ⟨castVar (O' := O) w, by rw [castVar_castVar, castVar_self]⟩
  rw [argsHom_renameVars, argsHom_castArgs, argsHom_castArgs, argsHom_idArgs]
  exact (castFrame O O' T).mapHom_mapVar _ w₀

/-- The template of the left inclusion: the operation `op`, tagged `.inl`, applied to the
    variables of its signature. -/
def inlTemplate : (castFrame O₁ (O₁ ⊕ O₂) T).Template := fun op =>
  .var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)
    ⟨Sum.inl op, rfl, castArgs (idArgs (d := ⟨O₁, T⟩) (DialectSignature.sig op))⟩ (.ret .here)

/-- The template of the right inclusion: the operation `op`, tagged `.inr`, applied to the
    variables of its signature. -/
def inrTemplate : (castFrame O₂ (O₁ ⊕ O₂) T).Template := fun op =>
  .var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)
    ⟨Sum.inr op, rfl, castArgs (idArgs (d := ⟨O₂, T⟩) (DialectSignature.sig op))⟩ (.ret .here)

/-- **The left inclusion is a template lowering**: its block form, the identity block
    lowering followed by `DialectOpSum.inl`, is the template lowering of `inlTemplate`. -/
theorem idComp_inl_eq_ofTemplate :
    (BlockLoweringData.id ⟨O₁, T⟩).comp (DialectOpSum.inl (O₂ := O₂)) =
      BlockLoweringData.ofTemplate (castFrame O₁ (O₁ ⊕ O₂) T) inlTemplate := by
  simp only [BlockLoweringData.comp]
  congr 1
  funext Γ t e
  rcases e with ⟨op, h, args⟩
  subst h
  show Com.var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) ⟨Sum.inl op, rfl, castArgs args⟩
      (.ret .here) = Com.var ⟨Sum.inl op, rfl, HVector.renameVars
        ((castFrame O₁ (O₁ ⊕ O₂) T).mapHom (argsHom args))
        (castArgs (O' := O₁ ⊕ O₂) (idArgs (d := ⟨O₁, T⟩) (DialectSignature.sig op)))⟩
      (.ret .here)
  rw [renameVars_castArgs_idArgs]

/-- **The right inclusion is a template lowering**: its block form, the identity block
    lowering followed by `DialectOpSum.inr`, is the template lowering of `inrTemplate`. -/
theorem idComp_inr_eq_ofTemplate :
    (BlockLoweringData.id ⟨O₂, T⟩).comp (DialectOpSum.inr (O₁ := O₁)) =
      BlockLoweringData.ofTemplate (castFrame O₂ (O₁ ⊕ O₂) T) inrTemplate := by
  simp only [BlockLoweringData.comp]
  congr 1
  funext Γ t e
  rcases e with ⟨op, h, args⟩
  subst h
  show Com.var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) ⟨Sum.inr op, rfl, castArgs args⟩
      (.ret .here) = Com.var ⟨Sum.inr op, rfl, HVector.renameVars
        ((castFrame O₂ (O₁ ⊕ O₂) T).mapHom (argsHom args))
        (castArgs (O' := O₁ ⊕ O₂) (idArgs (d := ⟨O₂, T⟩) (DialectSignature.sig op)))⟩
      (.ret .here)
  rw [renameVars_castArgs_idArgs]

section Copair

variable {f : Dialect} [DialectSignature f]

/-- **The frame of a copairing**: the frame `F` of the left summand on the operation sum,
    with the variable map read through `castVar`. -/
@[reducible] def LoweringFrame.copair (F : LoweringFrame ⟨O₁, T⟩ f) :
    LoweringFrame (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) f where
  mapTy := F.mapTy
  mapCtx := F.mapCtx
  mapCtx_nil := F.mapCtx_nil
  mapCtx_cons := F.mapCtx_cons
  mapVar := fun v => F.mapVar (castVar (O' := O₁) v)
  mapVar_here := fun t Γ => F.mapVar_here t Γ
  mapVar_there := fun s Γ _ v => F.mapVar_there s Γ (castVar v)

omit [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)] in
/-- A variable map over the type and context maps of a frame `F` that satisfies the head
    and weakening laws is the variable map of `F` read through `castVar`. -/
theorem mapVar_eq_of_laws {O O' : Type} [DialectSignature (⟨O, T⟩ : Dialect)]
    [DialectSignature (⟨O', T⟩ : Dialect)] (F : LoweringFrame ⟨O, T⟩ f)
    (mapVar' : ∀ {Γ : List T} {t : T}, Var (d := ⟨O', T⟩) Γ t → Var (F.mapCtx Γ) (F.mapTy t))
    (h_here : ∀ (t : T) (Γ : List T),
      castHom (F.mapCtx_cons t Γ) (mapVar' (Var.here : Var (d := ⟨O', T⟩) (t :: Γ) t)) =
        Var.here)
    (h_there : ∀ (s : T) (Γ : List T) {t : T} (v : Var (d := ⟨O', T⟩) Γ t),
      castHom (F.mapCtx_cons s Γ) (mapVar' (Var.there v : Var (d := ⟨O', T⟩) (s :: Γ) t)) =
        Var.there (mapVar' v)) :
    {Γ : List T} → {t : T} → (v : Var (d := ⟨O', T⟩) Γ t) →
      mapVar' v = F.mapVar (castVar (O' := O) v)
  | t :: Γ, _, .here => by
      show _ = F.mapVar Var.here
      rw [F.mapVar_here_eq, ← h_here t Γ, castHom_symm_castHom]
  | s :: Γ, _, .there v => by
      show _ = F.mapVar (Var.there (castVar v))
      rw [F.mapVar_there_eq, ← mapVar_eq_of_laws F mapVar' h_here h_there v,
        ← h_there s Γ v, castHom_symm_castHom]

omit [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)] in
/-- **The variable map of a frame is determined by its type and context maps.** Two frames
    out of dialects over `T` with equal type and context maps have variable maps related by
    `castVar`. -/
theorem mapVar_heq_of_frames {O O' : Type} [DialectSignature (⟨O, T⟩ : Dialect)]
    [DialectSignature (⟨O', T⟩ : Dialect)] (F : LoweringFrame ⟨O, T⟩ f)
    (F' : LoweringFrame ⟨O', T⟩ f) (hTy : F'.mapTy = F.mapTy) (hCtx : F'.mapCtx = F.mapCtx) :
    ∀ {Γ : List T} {t : T} (v : Var (d := ⟨O', T⟩) Γ t),
      F'.mapVar v ≍ F.mapVar (castVar (O' := O) v) := by
  cases F' with
  | mk mapTy mapCtx mapCtx_nil mapCtx_cons mapVar mapVar_here mapVar_there =>
    simp only at hTy hCtx
    subst hTy hCtx
    intro Γ t v
    exact heq_of_eq (mapVar_eq_of_laws F mapVar mapVar_here mapVar_there v)

/-- The template of a copairing: the template of `L₁` on the left summand and the template
    of `L₂`, read along the equalities of the type and context maps, on the right. -/
def copairTemplate (F₁ : LoweringFrame ⟨O₁, T⟩ f) (T₁ : F₁.Template)
    (F₂ : LoweringFrame ⟨O₂, T⟩ f) (T₂ : F₂.Template) (hTy : ∀ t, F₂.mapTy t = F₁.mapTy t)
    (hCtx : ∀ Γ, F₂.mapCtx Γ = F₁.mapCtx Γ) : (F₁.copair (O₂ := O₂)).Template
  | .inl o => T₁ o
  | .inr o => cast (congrArg₂ (Com f) (hCtx _) (hTy _)) (T₂ o)

/-- **The copairing of two template lowerings is a template lowering**, over the frame
    `F₁.copair` with the template `copairTemplate`. -/
theorem copair_ofTemplate (F₁ : LoweringFrame ⟨O₁, T⟩ f) (T₁ : F₁.Template)
    (F₂ : LoweringFrame ⟨O₂, T⟩ f) (T₂ : F₂.Template) (hTy : ∀ t, F₂.mapTy t = F₁.mapTy t)
    (hCtx : ∀ Γ, F₂.mapCtx Γ = F₁.mapCtx Γ) :
    copair (BlockLoweringData.ofTemplate F₁ T₁) (BlockLoweringData.ofTemplate F₂ T₂) hTy hCtx =
      BlockLoweringData.ofTemplate (F₁.copair (O₂ := O₂))
        (copairTemplate F₁ T₁ F₂ T₂ hTy hCtx) := by
  symm
  refine copair_unique _ _ _ _ _ rfl rfl (fun _ => HEq.rfl) (fun o h args => ?_)
    (fun o h args => ?_)
  · subst h
    refine heq_of_eq ?_
    show Com.rename ((F₁.copair (O₂ := O₂)).mapHom (argsHom args)) (T₁ o) =
      Com.rename (F₁.mapHom (argsHom (castArgs args))) (T₁ o)
    refine F₁.rename_ext _ _ (fun w => ?_) _
    have hw : F₁.mapVar w = (F₁.copair (O₂ := O₂)).mapVar (castVar (O' := O₁ ⊕ O₂) w) := by
      show _ = F₁.mapVar (castVar (castVar w))
      rw [castVar_castVar, castVar_self]
    obtain ⟨w₀, rfl⟩ : ∃ w₀ : Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) _ _,
        w = castVar (O' := O₁) w₀ :=
      ⟨castVar (O' := O₁ ⊕ O₂) w, by rw [castVar_castVar, castVar_self]⟩
    rw [hw, LoweringFrame.mapHom_mapVar, LoweringFrame.mapHom_mapVar, argsHom_castArgs]
  · subst h
    cases F₂ with
    | mk mapTy mapCtx mapCtx_nil mapCtx_cons mapVar mapVar_here mapVar_there =>
      have hT : mapTy = F₁.mapTy := funext hTy
      have hC : mapCtx = F₁.mapCtx := funext hCtx
      subst hT hC
      refine heq_of_eq ?_
      let F₂ : LoweringFrame ⟨O₂, T⟩ f :=
        ⟨F₁.mapTy, F₁.mapCtx, mapCtx_nil, mapCtx_cons, mapVar, mapVar_here, mapVar_there⟩
      have key : ∀ {Γ : List T} {t : T} (v : Var (d := ⟨O₂, T⟩) Γ t),
          mapVar v = F₁.mapVar (castVar (O' := O₁) v) :=
        fun v => mapVar_eq_of_laws F₁ mapVar mapVar_here mapVar_there v
      show Com.rename ((F₁.copair (O₂ := O₂)).mapHom (argsHom args)) (T₂ o) =
        Com.rename (F₂.mapHom (argsHom (castArgs args))) (T₂ o)
      refine F₂.rename_ext _ _ (fun w => ?_) _
      have hw : F₂.mapVar w = (F₁.copair (O₂ := O₂)).mapVar (castVar (O' := O₁ ⊕ O₂) w) := by
        show mapVar w = F₁.mapVar (castVar (castVar w))
        rw [key, castVar_castVar]
      obtain ⟨w₀, rfl⟩ : ∃ w₀ : Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) _ _,
          w = castVar (O' := O₂) w₀ :=
        ⟨castVar (O' := O₁ ⊕ O₂) w, by rw [castVar_castVar, castVar_self]⟩
      rw [F₂.mapHom_mapVar, hw, LoweringFrame.mapHom_mapVar, argsHom_castArgs,
        castVar_castVar, castVar_self]
      show _ = mapVar _
      rw [key, castVar_castVar]

end Copair

variable {O₁' : Type} {T' : Type} [DialectSignature (⟨O₁', T'⟩ : Dialect)]
  [DialectSignature (⟨O₂, T'⟩ : Dialect)]

/-- **The frame of `extendId`**: the frame `F` on the operation sums, with the variable map
    read through the variable casts. -/
@[reducible] def LoweringFrame.extendId (F : LoweringFrame ⟨O₁, T⟩ ⟨O₁', T'⟩) :
    LoweringFrame (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) where
  mapTy := F.mapTy
  mapCtx := F.mapCtx
  mapCtx_nil := F.mapCtx_nil
  mapCtx_cons := F.mapCtx_cons
  mapVar := fun v => castVar (O' := O₁' ⊕ O₂) (F.mapVar (castVar (O' := O₁) v))
  mapVar_here := fun t Γ => by
    show castHom _ (castVar (O' := O₁' ⊕ O₂) (F.mapVar Var.here)) = Var.here
    rw [castHom_castVar, F.mapVar_here]
    rfl
  mapVar_there := fun s Γ t v => by
    show castHom _ (castVar (O' := O₁' ⊕ O₂) (F.mapVar (Var.there (castVar (O' := O₁) v)))) = _
    rw [castHom_castVar, F.mapVar_there]
    rfl

/-- **The template of `extendId`.** An operation of the left summand gets its template
    under `F`, included into the target sum; an operation of the right summand gets the
    one-binding block applying the same operation to the mapped argument variables. -/
def extendIdTemplate (F : LoweringFrame ⟨O₁, T⟩ ⟨O₁', T'⟩) (S : F.Template)
    (hS : SigMaps O₂ F.mapTy) : (F.extendId (O₂ := O₂)).Template
  | .inl o => (DialectOpSum.inl (O₂ := O₂)).lowerCom (S o)
  | .inr o => .var ⟨Sum.inr o, hS.ret_eq o,
      (hS.sig_eq o).symm ▸ (F.extendId (O₂ := O₂)).mapArgs
        (idArgs (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inr o)))⟩
      (.ret .here)

/-- `sumMapArgs` is the argument map of the frame of `extendId`. -/
theorem sumMapArgs_eq (F : LoweringFrame ⟨O₁, T⟩ ⟨O₁', T'⟩) (S : F.Template) {Γ : List T} :
    {ts : List T} → (as : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t) ts) →
    sumMapArgs (BlockLoweringData.ofTemplate F S) as = (F.extendId (O₂ := O₂)).mapArgs as
  | [], .nil => rfl
  | _ :: _, .cons _ vs => congrArg (HVector.cons _) (sumMapArgs_eq F S vs)

/-- **`extendId` of a template lowering is a template lowering**, over the frame
    `F.extendId` with the template `extendIdTemplate`. -/
theorem extendId_ofTemplate (F : LoweringFrame ⟨O₁, T⟩ ⟨O₁', T'⟩) (S : F.Template)
    (hS : SigMaps O₂ F.mapTy) :
    (BlockLoweringData.ofTemplate F S).extendId hS =
      BlockLoweringData.ofTemplate F.extendId (extendIdTemplate F S hS) := by
  simp only [BlockLoweringData.extendId]
  congr 1
  funext Γ t e
  rcases e with ⟨op | op, h, args⟩ <;> subst h
  · show (DialectOpSum.inl (O₂ := O₂)).lowerCom
        (Com.rename (F.mapHom (argsHom (castArgs args))) (S op)) =
      Com.rename ((F.extendId (O₂ := O₂)).mapHom (argsHom args))
        ((DialectOpSum.inl (O₂ := O₂)).lowerCom (S op))
    rw [inl_lowerCom_rename]
    refine (F.extendId (O₂ := O₂)).rename_ext (Γ := DialectSignature.sig
      (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (.inl op)) _ _ (fun v => ?_) _
    show castVar (F.mapHom _ (castVar (castVar (F.mapVar (castVar v))))) =
      (F.extendId (O₂ := O₂)).mapHom _ ((F.extendId (O₂ := O₂)).mapVar v)
    rw [LoweringFrame.mapHom_mapVar, castVar_castVar, castVar_self,
      LoweringFrame.mapHom_mapVar, argsHom_castArgs]
  · show Com.var ⟨Sum.inr op, _, (hS.sig_eq op).symm ▸
        sumMapArgs (BlockLoweringData.ofTemplate F S) args⟩ (.ret .here) =
      Com.var ⟨Sum.inr op, _, HVector.renameVars ((F.extendId (O₂ := O₂)).mapHom (argsHom args))
        ((hS.sig_eq op).symm ▸ (F.extendId (O₂ := O₂)).mapArgs (idArgs _))⟩ (.ret .here)
    rw [renameVars_eqRec, LoweringFrame.renameVars_mapArgs_idArgs, sumMapArgs_eq]

end OpSum

/-! ## 6. Partial templates -/

section Partial

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']

/-- A partial op template over a frame: for each operation, a program over the mapped
    argument context, or `none` where the lowering refuses the operation. -/
abbrev LoweringFrame.Template? (F : LoweringFrame d d') : Type _ :=
  (op : d.Op) →
    Option (Com d' (F.mapCtx (DialectSignature.sig op)) (F.mapTy (DialectSignature.ret op)))

/-- The instance of a partial op template at an expression: the instance of `T e.op` at
    the arguments of `e`, or `none` where `T e.op` is `none`. -/
def LoweringFrame.templateBlock? (F : LoweringFrame d d') (T : F.Template?) {Γ : Ctxt d}
    {t : d.Ty} (e : Expr d Γ t) : Option (Com d' (F.mapCtx Γ) (F.mapTy t)) :=
  (T e.op).map fun c => congrArg F.mapTy e.retTy_eq ▸ Com.rename (F.mapHom (argsHom e.args)) c

/-- **The partial block lowering of a partial op template.** -/
@[reducible] def _root_.CatCrypt.Crypto.SecureCompilation.VIR.PartialBlockLowering.ofTemplate?
    (F : LoweringFrame d d') (T : F.Template?) : PartialBlockLowering d d' where
  mapTy := F.mapTy
  mapCtx := F.mapCtx
  mapCtx_cons := F.mapCtx_cons
  mapVar := F.mapVar
  lowerExprBlock? e := F.templateBlock? T e

/-- **The instance of a partial template commutes with renaming**: the refusal set is
    invariant under renaming, and an accepted expression renamed has the renamed block. -/
theorem templateBlock?_rename (F : LoweringFrame d d') (T : F.Template?) {Γ Δ : Ctxt d}
    {t : d.Ty} (f : Ctxt.Hom Γ Δ) (e : Expr d Γ t) :
    F.templateBlock? T (e.rename f) = (F.templateBlock? T e).map (Com.rename (F.mapHom f)) := by
  rcases e with ⟨op, h, args⟩
  subst h
  show (T op).map (fun c => Com.rename (F.mapHom (argsHom (HVector.renameVars f args))) c) =
    ((T op).map fun c => Com.rename (F.mapHom (argsHom args)) c).map (Com.rename (F.mapHom f))
  rw [Option.map_map]
  congr 1
  funext c
  show Com.rename (F.mapHom (argsHom (HVector.renameVars f args))) c =
    Com.rename (F.mapHom f) (Com.rename (F.mapHom (argsHom args)) c)
  rw [rename_rename]
  refine F.rename_ext _ _ (fun v => ?_) _
  simp only [LoweringFrame.mapHom_mapVar, argsHom_renameVars]

/-- A partial template that is `some` everywhere is the total template lowering. -/
theorem ofTemplate?_some (F : LoweringFrame d d') (T : F.Template) :
    PartialBlockLowering.ofTemplate? F (fun op => some (T op)) =
      (BlockLoweringData.ofTemplate F T).toPartial := rfl

/-- On an accepted expression, a partial template lowering agrees with the template
    lowering of any total template that extends it. -/
theorem ofTemplate?_eq_some (F : LoweringFrame d d') (T : F.Template?) (T' : F.Template)
    (hT' : ∀ op c, T op = some c → T' op = c) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (b : Com d' (F.mapCtx Γ) (F.mapTy t))
    (hb : (PartialBlockLowering.ofTemplate? F T).lowerExprBlock? e = some b) :
    (BlockLoweringData.ofTemplate F T').lowerExprBlock e = b := by
  rcases e with ⟨op, h, args⟩
  subst h
  change (T op).map (fun c => Com.rename (F.mapHom (argsHom args)) c) = some b at hb
  rcases hc : T op with _ | c
  · rw [hc] at hb
    exact absurd hb (by simp)
  · rw [hc] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    show Com.rename (F.mapHom (argsHom args)) (T' op) = b
    rw [hT' op c hc, hb]

/-- **Naturality of partial template lowerings on accepted expressions.** Every total
    template extending a partial template gives a lowering natural for the block splice,
    which agrees with the partial lowering on the expressions it accepts. -/
theorem spliceNatural_ofTemplate? (F : LoweringFrame d d') (T : F.Template?) (T' : F.Template)
    (hT' : ∀ op c, T op = some c → T' op = c) :
    SpliceNatural (BlockLoweringData.ofTemplate F T') ∧
      ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (b : Com d' (F.mapCtx Γ) (F.mapTy t)),
        (PartialBlockLowering.ofTemplate? F T).lowerExprBlock? e = some b →
          (BlockLoweringData.ofTemplate F T').lowerExprBlock e = b :=
  ⟨spliceNatural_ofTemplate F T', fun e b hb => ofTemplate?_eq_some F T T' hT' e b hb⟩

end Partial

/-! ## 7. The category of template lowerings -/

section Category

/-- The identity frame: types, contexts and variables are unchanged. -/
@[reducible] def LoweringFrame.id (d : Dialect) [DialectSignature d] : LoweringFrame d d where
  mapTy := fun t => t
  mapCtx := fun Γ => Γ
  mapCtx_nil := rfl
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => v
  mapVar_here := fun _ _ => rfl
  mapVar_there := fun _ _ _ _ => rfl

/-- The template of the identity lowering: each operation applied to the variables of its
    signature. -/
def idTemplate (d : Dialect) [DialectSignature d] : (LoweringFrame.id d).Template := fun op =>
  .var ⟨op, rfl, idArgs (DialectSignature.sig op)⟩ (.ret .here)

/-- **The identity block lowering is a template lowering.** -/
theorem id_eq_ofTemplate (d : Dialect) [DialectSignature d] :
    BlockLoweringData.id d = BlockLoweringData.ofTemplate (LoweringFrame.id d) (idTemplate d) := by
  simp only [BlockLoweringData.id]
  congr 1
  funext Γ t e
  rcases e with ⟨op, h, args⟩
  subst h
  show Com.var ⟨op, rfl, args⟩ (.ret .here) =
    Com.var ⟨op, rfl, HVector.renameVars ((LoweringFrame.id d).mapHom (argsHom args))
      (idArgs (DialectSignature.sig op))⟩ (.ret .here)
  rw [renameVars_congr (g := argsHom args)
    (fun w => (LoweringFrame.id d).hom_ext _ (argsHom args)
      (fun v => (LoweringFrame.id d).mapHom_mapVar _ v) w), renameVars_idArgs]

open CategoryTheory

/-- A dialect with its signature, as an object of the category of template lowerings. -/
structure TemplateDialect where
  /-- The dialect. -/
  dia : Dialect.{0, 0}
  /-- Its signature. -/
  [sig : DialectSignature dia]

attribute [instance] TemplateDialect.sig

/-- The block lowerings between two dialects that are template lowerings. -/
def TemplateHom (a b : TemplateDialect) : Type :=
  {L : BlockLoweringData a.dia b.dia //
    ∃ (F : LoweringFrame a.dia b.dia) (T : F.Template), L = BlockLoweringData.ofTemplate F T}

/-- **The category of template lowerings**: dialects are the objects, template lowerings
    the morphisms, `BlockLoweringData.id` the identity and `compBlock` the composition. -/
instance TemplateDialect.instCategory : Category TemplateDialect where
  Hom a b := TemplateHom a b
  id a := ⟨BlockLoweringData.id a.dia, _, _, id_eq_ofTemplate a.dia⟩
  comp L M := ⟨L.1.compBlock M.1, by
    obtain ⟨F, T, hL⟩ := L.2
    obtain ⟨G, S, hM⟩ := M.2
    rw [hL, hM]
    exact ⟨_, _, ofTemplate_comp F T G S⟩⟩
  id_comp M := Subtype.ext (by
    obtain ⟨G, S, hM⟩ := M.2
    show (BlockLoweringData.id _).compBlock M.1 = M.1
    rw [hM]
    exact ofTemplate_id_comp G S)
  comp_id L := Subtype.ext (compBlock_id L.1)
  assoc L M N := Subtype.ext (by
    obtain ⟨G, S, hN⟩ := N.2
    show (L.1.compBlock M.1).compBlock N.1 = L.1.compBlock (M.1.compBlock N.1)
    rw [hN]
    exact ofTemplate_comp_assoc L.1 M.1 G S)

end Category

/-! ## 8. The derived-to-field lowering and its extension -/

section Witness

open FieldDialect (FieldTy fieldDialect)
open FieldDerivedOps

/-- The frame of `DerivedToField.lowering`: the type map `DerivedToField.mapTy`, applied
    pointwise to contexts. -/
@[reducible] def derivedFrame : LoweringFrame derivedDialect fieldDialect where
  mapTy := DerivedToField.mapTy
  mapCtx := DerivedToField.mapCtx
  mapCtx_nil := rfl
  mapCtx_cons := DerivedToField.mapCtx_cons
  mapVar := DerivedToField.mapVar
  mapVar_here := fun _ _ => rfl
  mapVar_there := fun _ _ _ _ => rfl

/-- The op template of `DerivedToField.lowering`: each derived operation becomes its field
    block at the argument variable. -/
def derivedTemplate : derivedFrame.Template
  | .fieldDouble p => DerivedToField.doubleBlock p Var.here
  | .fieldSquare p => DerivedToField.squareBlock p Var.here
  | .fieldPow p k => DerivedToField.powBlock p k Var.here

/-- Renaming commutes with the multiplication chain: the chain at `a`, renamed by `ρ`, is
    the chain at `ρ a`. -/
theorem rename_powBlock (p : Nat) : (k : Nat) → {Γ Δ : Ctxt fieldDialect} →
    (ρ : Ctxt.Hom Γ Δ) → (a : Var Γ (FieldTy.fp p)) →
    Com.rename ρ (DerivedToField.powBlock p k a) = DerivedToField.powBlock p k (ρ a)
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | (k + 2), _, _, ρ, a => by
      show Com.rename ρ (spliceCom (DerivedToField.powBlock p (k + 1) a) _) =
        spliceCom (DerivedToField.powBlock p (k + 1) (ρ a)) _
      rw [rename_spliceCom, rename_powBlock p (k + 1) ρ a]
      rfl

/-- **`DerivedToField.lowering` is a template lowering.** -/
theorem derivedToField_eq_ofTemplate :
    DerivedToField.lowering = BlockLoweringData.ofTemplate derivedFrame derivedTemplate := by
  simp only [DerivedToField.lowering]
  congr 1
  funext Γ t e
  rcases e with ⟨op, h, args⟩
  subst h
  cases op with
  | fieldDouble p =>
      rcases args with _ | ⟨a, _ | _⟩
      rfl
  | fieldSquare p =>
      rcases args with _ | ⟨a, _ | _⟩
      rfl
  | fieldPow p k =>
      rcases args with _ | ⟨a, _ | _⟩
      show DerivedToField.powBlock p k (DerivedToField.mapVar a) =
        Com.rename (derivedFrame.mapHom (argsHom (.cons a .nil)))
          (DerivedToField.powBlock p k Var.here)
      rw [rename_powBlock]
      rfl

/-- **The extended lowering is a template lowering**: the template of `extendId` over the
    frame of `DerivedToField.lowering`. -/
theorem witness_eq_ofTemplate :
    BlockLoweringExtend.Witness.lowering =
      BlockLoweringData.ofTemplate derivedFrame.extendId
        (extendIdTemplate derivedFrame derivedTemplate BlockLoweringExtend.Witness.sigMaps) := by
  have key : ∀ (L : BlockLoweringData derivedDialect fieldDialect)
      (hL : L = BlockLoweringData.ofTemplate derivedFrame derivedTemplate)
      (hS : BlockLoweringExtend.SigMaps FieldToModArithLowering.FpOp L.mapTy)
      (hS' : BlockLoweringExtend.SigMaps FieldToModArithLowering.FpOp derivedFrame.mapTy),
      L.extendId hS = BlockLoweringData.ofTemplate derivedFrame.extendId
        (extendIdTemplate derivedFrame derivedTemplate hS') := by
    intro L hL hS hS'
    subst hL
    exact extendId_ofTemplate derivedFrame derivedTemplate hS
  exact key _ derivedToField_eq_ofTemplate _ _

/-- The extended lowering is natural for the block splice. -/
theorem spliceNatural_witness : SpliceNatural BlockLoweringExtend.Witness.lowering := by
  rw [witness_eq_ofTemplate]
  exact spliceNatural_ofTemplate _ _

/-- The extended lowering maps the head variable to the head variable. -/
theorem headVar_witness : HeadVar BlockLoweringExtend.Witness.lowering := by
  rw [witness_eq_ofTemplate]
  exact headVar_ofTemplate _ _

end Witness

end DialectCategory

end CatCrypt.Crypto.SecureCompilation.VIR

