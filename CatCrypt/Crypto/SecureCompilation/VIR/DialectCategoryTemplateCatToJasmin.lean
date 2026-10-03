/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCategoryTemplate
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin

/-!
# `catToJasmin` as a partial template lowering

The partial block lowering `NFProgCatToJasmin.catToJasmin` sends an expression `e` of
`catCryptDialect` to the one-binding block of `toJExprD e`, and refuses `e` where
`toJExprD e` is `none`. Whether `toJExprD` refuses depends on the operation alone, and the
translation commutes with renaming (`toJExprD_rename`), so `catToJasmin` is the partial
template lowering of `catTemplate`, the translation of each operation applied to the
variables of its signature (`catToJasmin_eq_ofTemplate?`).

## Main definitions

* `DialectCategory.catFrame`, `DialectCategory.catTemplate` — the frame and the partial op
  template of `catToJasmin`.

## Main results

* `DialectCategory.toJExprD_rename` — `toJExprD` commutes with renaming.
* `DialectCategory.catToJasmin_eq_ofTemplate?` — `catToJasmin` is a partial template
  lowering.
* `DialectCategory.spliceNatural_catToJasmin` — on accepted expressions, `catToJasmin`
  agrees with a template lowering natural for the block splice.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)
open CatCryptDialect
open JasminDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open DialectToJasminCom
open CryptoToJasminCom (mapTy mapCtx)
open FieldDialectBlockDescent (BlockLoweringData)

namespace DialectCategory

/-- The frame of `catToJasmin`: the type map `CryptoToJasminCom.mapTy`, applied pointwise
    to contexts, with the variable map `toJVarD`. -/
@[reducible] def catFrame : LoweringFrame catCryptDialect jasminDialect where
  mapTy := mapTy
  mapCtx := mapCtx
  mapCtx_nil := rfl
  mapCtx_cons := fun _ _ => rfl
  mapVar := toJVarD
  mapVar_here := fun _ _ => rfl
  mapVar_there := fun _ _ _ _ => rfl

/-- The partial op template of `catToJasmin`: the one-binding block of `toJExprD` at the
    expression applying the operation to the variables of its signature, or `none` where
    `toJExprD` refuses the operation. -/
def catTemplate : catFrame.Template? := fun op =>
  (toJExprD (⟨op, rfl, idArgs (DialectSignature.sig op)⟩ : Expr catCryptDialect _ _)).map
    fun e' => .var e' (.ret .here)

/-- `mapHom` of the frame of `catToJasmin` on a translated variable. -/
theorem catFrame_mapHom_toJVarD {Γ Δ : Ctxt catCryptDialect} (f : Ctxt.Hom Γ Δ)
    {t : CryptoTy} (v : Var Γ t) : catFrame.mapHom f (toJVarD v) = toJVarD (f v) :=
  catFrame.mapHom_mapVar f v

/-- `toJArgsD` commutes with renaming. -/
theorem toJArgsD_renameVars {Γ Δ : Ctxt catCryptDialect} (f : Ctxt.Hom Γ Δ) :
    {tys : List CryptoTy} → (args : HVector (fun t => Var Γ t) tys) →
    toJArgsD (HVector.renameVars f args) =
      HVector.renameVars (catFrame.mapHom f) (toJArgsD args)
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show HVector.cons (toJVarD (f v)) (toJArgsD (HVector.renameVars f vs)) =
        HVector.cons (catFrame.mapHom f (toJVarD v)) (HVector.renameVars _ (toJArgsD vs))
      rw [catFrame_mapHom_toJVarD, toJArgsD_renameVars f vs]

/-- Renaming a vector with a head renames the head and the tail. -/
theorem renameVars_cons {d : Dialect} {Γ Γ' : Ctxt d} (g : Ctxt.Hom Γ Γ') {t : d.Ty}
    {ts : List d.Ty} (v : Var Γ t) (vs : HVector (fun t => Var Γ t) ts) :
    HVector.renameVars g (HVector.cons v vs) = HVector.cons (g v) (HVector.renameVars g vs) :=
  rfl

/-- **`toJExprD` commutes with renaming**: the refusal set is invariant under renaming,
    and the translation of a renamed expression is the renamed translation. -/
theorem toJExprD_rename {Γ Δ : Ctxt catCryptDialect} {t : CryptoTy} (f : Ctxt.Hom Γ Δ)
    (e : Expr catCryptDialect Γ t) :
    toJExprD (e.rename f) = (toJExprD e).map (Expr.rename (catFrame.mapHom f)) := by
  obtain ⟨op, hop, args⟩ := e
  subst hop
  cases op
  case' ite => rename_i ty; cases ty
  case' vsimd => rename_i sop; cases sop
  case' extCall => rename_i retTy; cases retTy
  all_goals first
    | rfl
    | (dsimp only [toJExprD, Expr.rename, Option.map]
       exact congrArg some (congrArg (Expr.mk _ _) (toJArgsD_renameVars f args)))
    | (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
       dsimp only [toJExprD, Expr.rename, mkBin, Option.map]
       repeat erw [renameVars_cons]
       repeat erw [catFrame_mapHom_toJVarD]
       rfl)

/-- On every expression, the block of `catToJasmin` is the instance of `catTemplate`. -/
theorem catToJasmin_lowerExprBlock? {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) :
    NFProgCatToJasmin.catToJasmin.lowerExprBlock? e = catFrame.templateBlock? catTemplate e := by
  rcases e with ⟨op, h, args⟩
  subst h
  show (toJExprD (⟨op, rfl, args⟩ : Expr catCryptDialect Γ _)).map
      (fun e' => Com.var e' (.ret .here)) =
    (catTemplate op).map (fun c => Com.rename (catFrame.mapHom (argsHom args)) c)
  have he : (⟨op, rfl, args⟩ : Expr catCryptDialect Γ _) =
      Expr.rename (argsHom args) ⟨op, rfl, idArgs (DialectSignature.sig op)⟩ := by
    show _ = (⟨op, rfl, HVector.renameVars (argsHom args) (idArgs _)⟩ :
      Expr catCryptDialect Γ _)
    rw [renameVars_idArgs]
  rw [he, toJExprD_rename, Option.map_map]
  simp only [catTemplate, Option.map_map]
  rfl

/-- **`catToJasmin` is a partial template lowering**: the partial template lowering of
    `catTemplate` over the frame `catFrame`. -/
theorem catToJasmin_eq_ofTemplate? :
    NFProgCatToJasmin.catToJasmin = PartialBlockLowering.ofTemplate? catFrame catTemplate := by
  simp only [NFProgCatToJasmin.catToJasmin]
  congr 1
  funext Γ t e
  exact catToJasmin_lowerExprBlock? e

/-- `catToJasmin` agrees, on the expressions it accepts, with the template lowering of any
    total template extending `catTemplate`, and that lowering is natural for the block
    splice. -/
theorem spliceNatural_catToJasmin (T' : catFrame.Template)
    (hT' : ∀ op c, catTemplate op = some c → T' op = c) :
    SpliceNatural (BlockLoweringData.ofTemplate catFrame T') ∧
      ∀ {Γ : Ctxt catCryptDialect} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
        (b : Com jasminDialect (mapCtx Γ) (mapTy t)),
        NFProgCatToJasmin.catToJasmin.lowerExprBlock? e = some b →
          (BlockLoweringData.ofTemplate catFrame T').lowerExprBlock e = b := by
  refine ⟨spliceNatural_ofTemplate _ _, fun e b hb => ?_⟩
  rw [catToJasmin_lowerExprBlock?] at hb
  exact ofTemplate?_eq_some catFrame catTemplate T' hT' e b hb

end DialectCategory

end CatCrypt.Crypto.SecureCompilation.VIR
