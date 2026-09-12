/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-!
# Composition of block-expanding dialect lowerings

`FieldDialectBlockDescent.BlockLoweringData d d'` is the dialect-to-dialect
lowering whose per-op rule `lowerExprBlock` returns a whole target `Com` block,
so one source op may expand to several target ops. `blockLowerCom` is its
whole-program recursion and `blockFundamental` derives denotation preservation
from three leaf obligations (`VarTransports`, `BlockOpTransports`,
`MapValExtends`).

`LoweringDataComp` supplies `LoweringData.comp` and `comp_fundamental` for the
single-`Expr` lowering. This file is the block counterpart: a block lowering
`d → d'` composes with a single-`Expr` lowering `d' → d''`, and with a block
lowering `d' → d''`, into one `BlockLoweringData d d''` whose whole-program
transport square is derived from the two stages' leaf obligations.

The composite's per-op block is the first stage's block mapped through the
second stage's whole-program recursion, so the second stage's whole-program
square — `ComParametricityTransport.fundamental`, respectively
`blockFundamental` — is what discharges the composite's `BlockOpTransports`.
The other two obligations are the two stages' obligations chained, with the
`mapCtx_cons` reindexings glued by `heq_eqRec'` / `heq_congr_valMap`.

A composed descent such as `fieldComToJasmin = fieldFpDescent.comp
modArithToJasmin` therefore admits a block-expanding first stage: a source op
whose lowering expands to several target ops can sit in a dialect whose descent
is composed, instead of requiring a dialect of its own.

## Main definitions

* `BlockLoweringData.comp` — a block lowering `d → d'` followed by a
  single-`Expr` lowering `d' → d''`; its per-op block is
  `LoweringData.lowerCom` applied to the first stage's block.
* `BlockLoweringData.compBlock` — a block lowering `d → d'` followed by a block
  lowering `d' → d''`; its per-op block is `blockLowerCom` applied to the first
  stage's block.
* `compTransTy` / `compMapVal`, `compBlockTransTy` / `compBlockMapVal` — the
  composite value and valuation transports.

## Main results

* `comp_varTransports`, `comp_blockOpTransports`, `comp_mapValExtends` — the
  three leaf obligations of `L1.comp L2`, from those of the two stages.
* `comp_blockFundamental` — the whole-program transport square of `L1.comp L2`.
* `compBlock_varTransports`, `compBlock_blockOpTransports`,
  `compBlock_mapValExtends`, `compBlock_blockFundamental` — the same for
  `L1.compBlock L2`.
* `Validation.dupThenId_blockDescends` — the one-op-to-two-block toy lowering
  composed with an identity `LoweringData`, and its whole-program square on a
  concrete multi-binding program (`Validation.sampleProg_compDescends`,
  `Validation.dupThenId_sampleProg_eval`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringDataComp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport (LoweringData fundamental)

universe u v

/-! ## 1. Cast bookkeeping

Both stages state their `MapValExtends` obligation modulo the `mapCtx_cons`
reindexing, so gluing the two needs three facts about the `Eq.rec` that `▸`
elaborates to: an equation against a cast follows from the `HEq` of the uncast
sides, a cast is `HEq` to the uncast term, and a valuation map applied to
`HEq` arguments over equal contexts gives `HEq` results. -/

/-- An equation whose right-hand side is a `▸` cast follows from the `HEq` of
    the two uncast sides. -/
theorem eq_eqRec_of_heq {α : Sort u} {F : α → Sort v} {a b : α} (h : a = b)
    (x : F a) (y : F b) (hxy : x ≍ y) : x = h ▸ y := by
  cases h; exact eq_of_heq hxy

/-- A `▸` cast is `HEq` to the uncast term. -/
theorem heq_eqRec' {α : Sort u} {F : α → Sort v} {a b : α} (h : a = b) (y : F b) :
    (h ▸ y : F a) ≍ y := by
  cases h; rfl

/-- A context-indexed valuation map sends `HEq` valuations over equal contexts
    to `HEq` valuations. -/
theorem heq_congr_valMap {e e' : Dialect} [TyDenote e.Ty] [TyDenote e'.Ty]
    {F : Ctxt e → Ctxt e'}
    (m : ∀ {Δ : Ctxt e}, Ctxt.Valuation Δ → Ctxt.Valuation (F Δ))
    {Γ₁ Γ₂ : Ctxt e} (h : Γ₁ = Γ₂)
    (y : Ctxt.Valuation Γ₁) (z : Ctxt.Valuation Γ₂) (hyz : y ≍ z) :
    m y ≍ m z := by
  cases h; rw [eq_of_heq hyz]

variable {d d' d'' : Dialect}
variable [DialectSignature d] [DialectSignature d'] [DialectSignature d'']

/-! ## 2. A block lowering followed by a single-`Expr` lowering -/

/-- **Composition of a block lowering with a single-`Expr` lowering.** Type and
    context maps compose as functions and the variable map is the composite; the
    per-op block is the first stage's block mapped through the second stage's
    canonical whole-program recursion `LoweringData.lowerCom`, so a source op
    that expanded to several ops in `d'` still expands in `d''`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent.BlockLoweringData.comp
    (L1 : BlockLoweringData d d') (L2 : LoweringData d' d'') : BlockLoweringData d d'' where
  mapTy := L2.mapTy ∘ L1.mapTy
  mapCtx := L2.mapCtx ∘ L1.mapCtx
  mapCtx_cons := fun t Γ => by
    simp only [Function.comp_apply, L1.mapCtx_cons, L2.mapCtx_cons]
  mapVar := fun v => L2.mapVar (L1.mapVar v)
  lowerExprBlock := fun e => L2.lowerCom (L1.lowerExprBlock e)

variable (L1 : BlockLoweringData d d') (L2 : LoweringData d' d'')

/-- The composite's `mapTy` is the function composite. -/
@[simp] theorem comp_mapTy : (L1.comp L2).mapTy = L2.mapTy ∘ L1.mapTy := rfl

/-- The composite's `mapCtx` is the function composite. -/
@[simp] theorem comp_mapCtx : (L1.comp L2).mapCtx = L2.mapCtx ∘ L1.mapCtx := rfl

/-- The composite's `mapVar` is the composite of the two variable maps. -/
@[simp] theorem comp_mapVar {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t) :
    (L1.comp L2).mapVar v = L2.mapVar (L1.mapVar v) := rfl

/-- The composite's per-op block is the first stage's block, lowered through the
    second stage's canonical `Com` recursion. -/
@[simp] theorem comp_lowerExprBlock {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) :
    (L1.comp L2).lowerExprBlock e = L2.lowerCom (L1.lowerExprBlock e) := rfl

section Semantic

variable [TyDenote d.Ty] [TyDenote d'.Ty] [TyDenote d''.Ty]

/-- The composite value transport `⟦t⟧ → ⟦L2.mapTy (L1.mapTy t)⟧`. -/
def compTransTy (transTy1 : TransTy L1)
    (transTy2 : ComParametricityTransport.TransTy L2) : TransTy (L1.comp L2) :=
  fun {_t} x => transTy2 (transTy1 x)

/-- The composite valuation transport
    `Valuation Γ → Valuation (L2.mapCtx (L1.mapCtx Γ))`. -/
def compMapVal (mapVal1 : MapVal L1)
    (mapVal2 : ComParametricityTransport.MapVal L2) : MapVal (L1.comp L2) :=
  fun {_Γ} V => mapVal2 (mapVal1 V)

variable (transTy1 : TransTy L1) (mapVal1 : MapVal L1)
variable (transTy2 : ComParametricityTransport.TransTy L2)
variable (mapVal2 : ComParametricityTransport.MapVal L2)

/-- Variable leaf of the composite: the second stage's variable leaf at the
    once-transported variable, followed by the first stage's. -/
theorem comp_varTransports
    (hVar1 : VarTransports L1 transTy1 mapVal1)
    (hVar2 : ComParametricityTransport.VarTransports L2 transTy2 mapVal2) :
    VarTransports (L1.comp L2) (compTransTy L1 L2 transTy1 transTy2)
      (compMapVal L1 L2 mapVal1 mapVal2) := by
  intro Γ t v V
  show (L2.mapVar (L1.mapVar v)).lookup (mapVal2 (mapVal1 V))
      = transTy2 (transTy1 (v.lookup V))
  rw [hVar2 (L1.mapVar v) (mapVal1 V), hVar1 v V]

/-- Binding-threading of the composite: the first stage's threading pushed
    through the second stage's valuation transport, then the second stage's
    threading, with the two `mapCtx_cons` reindexings glued. -/
theorem comp_mapValExtends
    (hExt1 : MapValExtends L1 transTy1 mapVal1)
    (hExt2 : ComParametricityTransport.MapValExtends L2 transTy2 mapVal2) :
    MapValExtends (L1.comp L2) (compTransTy L1 L2 transTy1 transTy2)
      (compMapVal L1 L2 mapVal1 mapVal2) := by
  intro Γ t V x
  refine eq_eqRec_of_heq ((L1.comp L2).mapCtx_cons t Γ) _ _ ?_
  show mapVal2 (mapVal1 (Ctxt.Valuation.extend V x))
      ≍ Ctxt.Valuation.extend (mapVal2 (mapVal1 V)) (transTy2 (transTy1 x))
  have h1 : mapVal1 (Ctxt.Valuation.extend V x)
      = (L1.mapCtx_cons t Γ ▸ Ctxt.Valuation.extend (mapVal1 V) (transTy1 x)) := hExt1 V x
  rw [h1]
  refine HEq.trans (heq_congr_valMap mapVal2 (L1.mapCtx_cons t Γ) _ _
    (heq_eqRec' (L1.mapCtx_cons t Γ) _)) ?_
  have h2 : mapVal2 (Ctxt.Valuation.extend (mapVal1 V) (transTy1 x))
      = (L2.mapCtx_cons (L1.mapTy t) (L1.mapCtx Γ) ▸
          Ctxt.Valuation.extend (mapVal2 (mapVal1 V)) (transTy2 (transTy1 x))) :=
    hExt2 (mapVal1 V) (transTy1 x)
  exact (heq_of_eq h2).trans (heq_eqRec' (L2.mapCtx_cons (L1.mapTy t) (L1.mapCtx Γ)) _)

section Denote

variable [DialectDenote d] [DialectDenote d'] [DialectDenote d'']

/-- **Block leaf of the composite.** The composite's block is the first stage's
    block mapped through `L2.lowerCom`, so the square is
    `ComParametricityTransport.fundamental` for `L2` at that block, composed with
    the first stage's block square. -/
theorem comp_blockOpTransports
    (hOp1 : BlockOpTransports L1 transTy1 mapVal1)
    (hVar2 : ComParametricityTransport.VarTransports L2 transTy2 mapVal2)
    (hOp2 : ComParametricityTransport.OpLowerTransports L2 transTy2 mapVal2)
    (hExt2 : ComParametricityTransport.MapValExtends L2 transTy2 mapVal2) :
    BlockOpTransports (L1.comp L2) (compTransTy L1 L2 transTy1 transTy2)
      (compMapVal L1 L2 mapVal1 mapVal2) := by
  intro Γ t e V
  show (L2.lowerCom (L1.lowerExprBlock e)).denote (mapVal2 (mapVal1 V))
      = transTy2 (transTy1 (e.denote V))
  have h2 := fundamental L2 transTy2 mapVal2 hVar2 hOp2 hExt2
    (L1.lowerExprBlock e) (mapVal1 V)
  exact h2.trans (congrArg transTy2 (hOp1 e V))

/-- **Whole-program transport square of the composite.** For every source
    program, the block-expanded descent through `d'` and on to `d''` denotes to
    the composite transport of the source denotation. Each stage contributes only
    its own leaf obligations; the composite square is `blockFundamental` at
    `L1.comp L2`. -/
theorem comp_blockFundamental
    (hVar1 : VarTransports L1 transTy1 mapVal1)
    (hOp1 : BlockOpTransports L1 transTy1 mapVal1)
    (hExt1 : MapValExtends L1 transTy1 mapVal1)
    (hVar2 : ComParametricityTransport.VarTransports L2 transTy2 mapVal2)
    (hOp2 : ComParametricityTransport.OpLowerTransports L2 transTy2 mapVal2)
    (hExt2 : ComParametricityTransport.MapValExtends L2 transTy2 mapVal2)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ) :
    ((L1.comp L2).blockLowerCom c).denote (compMapVal L1 L2 mapVal1 mapVal2 V)
      = compTransTy L1 L2 transTy1 transTy2 (c.denote V) :=
  blockFundamental (L1.comp L2) (compTransTy L1 L2 transTy1 transTy2)
    (compMapVal L1 L2 mapVal1 mapVal2)
    (comp_varTransports L1 L2 transTy1 mapVal1 transTy2 mapVal2 hVar1 hVar2)
    (comp_blockOpTransports L1 L2 transTy1 mapVal1 transTy2 mapVal2 hOp1 hVar2 hOp2 hExt2)
    (comp_mapValExtends L1 L2 transTy1 mapVal1 transTy2 mapVal2 hExt1 hExt2) c V

end Denote

end Semantic

/-! ## 3. A block lowering followed by a block lowering

The same composition with `blockLowerCom` in place of `lowerCom`: the second
stage may itself expand each op it sees into a block, and its whole-program
square is `blockFundamental` rather than
`ComParametricityTransport.fundamental`. -/

/-- **Composition of two block lowerings.** The per-op block is the first
    stage's block mapped through the second stage's block-expanding recursion
    `blockLowerCom`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent.BlockLoweringData.compBlock
    (L1 : BlockLoweringData d d') (L2 : BlockLoweringData d' d'') :
    BlockLoweringData d d'' where
  mapTy := L2.mapTy ∘ L1.mapTy
  mapCtx := L2.mapCtx ∘ L1.mapCtx
  mapCtx_cons := fun t Γ => by
    simp only [Function.comp_apply, L1.mapCtx_cons, L2.mapCtx_cons]
  mapVar := fun v => L2.mapVar (L1.mapVar v)
  lowerExprBlock := fun e => L2.blockLowerCom (L1.lowerExprBlock e)

variable (M2 : BlockLoweringData d' d'')

/-- The block composite's `mapTy` is the function composite. -/
@[simp] theorem compBlock_mapTy : (L1.compBlock M2).mapTy = M2.mapTy ∘ L1.mapTy := rfl

/-- The block composite's `mapCtx` is the function composite. -/
@[simp] theorem compBlock_mapCtx : (L1.compBlock M2).mapCtx = M2.mapCtx ∘ L1.mapCtx := rfl

/-- The block composite's `mapVar` is the composite of the two variable maps. -/
@[simp] theorem compBlock_mapVar {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t) :
    (L1.compBlock M2).mapVar v = M2.mapVar (L1.mapVar v) := rfl

/-- The block composite's per-op block is the first stage's block, lowered
    through the second stage's block-expanding recursion. -/
@[simp] theorem compBlock_lowerExprBlock {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) :
    (L1.compBlock M2).lowerExprBlock e = M2.blockLowerCom (L1.lowerExprBlock e) := rfl

section SemanticBlock

variable [TyDenote d.Ty] [TyDenote d'.Ty] [TyDenote d''.Ty]

/-- The value transport of a composite of two block lowerings. -/
def compBlockTransTy (transTy1 : TransTy L1) (transTy2 : TransTy M2) :
    TransTy (L1.compBlock M2) :=
  fun {_t} x => transTy2 (transTy1 x)

/-- The valuation transport of a composite of two block lowerings. -/
def compBlockMapVal (mapVal1 : MapVal L1) (mapVal2 : MapVal M2) :
    MapVal (L1.compBlock M2) :=
  fun {_Γ} V => mapVal2 (mapVal1 V)

variable (transTy1 : TransTy L1) (mapVal1 : MapVal L1)
variable (transTy2 : TransTy M2) (mapVal2 : MapVal M2)

/-- Variable leaf of the block composite. -/
theorem compBlock_varTransports
    (hVar1 : VarTransports L1 transTy1 mapVal1)
    (hVar2 : VarTransports M2 transTy2 mapVal2) :
    VarTransports (L1.compBlock M2) (compBlockTransTy L1 M2 transTy1 transTy2)
      (compBlockMapVal L1 M2 mapVal1 mapVal2) := by
  intro Γ t v V
  show (M2.mapVar (L1.mapVar v)).lookup (mapVal2 (mapVal1 V))
      = transTy2 (transTy1 (v.lookup V))
  rw [hVar2 (L1.mapVar v) (mapVal1 V), hVar1 v V]

/-- Binding-threading of the block composite. -/
theorem compBlock_mapValExtends
    (hExt1 : MapValExtends L1 transTy1 mapVal1)
    (hExt2 : MapValExtends M2 transTy2 mapVal2) :
    MapValExtends (L1.compBlock M2) (compBlockTransTy L1 M2 transTy1 transTy2)
      (compBlockMapVal L1 M2 mapVal1 mapVal2) := by
  intro Γ t V x
  refine eq_eqRec_of_heq ((L1.compBlock M2).mapCtx_cons t Γ) _ _ ?_
  show mapVal2 (mapVal1 (Ctxt.Valuation.extend V x))
      ≍ Ctxt.Valuation.extend (mapVal2 (mapVal1 V)) (transTy2 (transTy1 x))
  have h1 : mapVal1 (Ctxt.Valuation.extend V x)
      = (L1.mapCtx_cons t Γ ▸ Ctxt.Valuation.extend (mapVal1 V) (transTy1 x)) := hExt1 V x
  rw [h1]
  refine HEq.trans (heq_congr_valMap mapVal2 (L1.mapCtx_cons t Γ) _ _
    (heq_eqRec' (L1.mapCtx_cons t Γ) _)) ?_
  have h2 : mapVal2 (Ctxt.Valuation.extend (mapVal1 V) (transTy1 x))
      = (M2.mapCtx_cons (L1.mapTy t) (L1.mapCtx Γ) ▸
          Ctxt.Valuation.extend (mapVal2 (mapVal1 V)) (transTy2 (transTy1 x))) :=
    hExt2 (mapVal1 V) (transTy1 x)
  exact (heq_of_eq h2).trans (heq_eqRec' (M2.mapCtx_cons (L1.mapTy t) (L1.mapCtx Γ)) _)

section DenoteBlock

variable [DialectDenote d] [DialectDenote d'] [DialectDenote d'']

/-- **Block leaf of the block composite.** The composite's block is the first
    stage's block mapped through `M2.blockLowerCom`, so the square is
    `blockFundamental` for `M2` at that block, composed with the first stage's
    block square. -/
theorem compBlock_blockOpTransports
    (hOp1 : BlockOpTransports L1 transTy1 mapVal1)
    (hVar2 : VarTransports M2 transTy2 mapVal2)
    (hOp2 : BlockOpTransports M2 transTy2 mapVal2)
    (hExt2 : MapValExtends M2 transTy2 mapVal2) :
    BlockOpTransports (L1.compBlock M2) (compBlockTransTy L1 M2 transTy1 transTy2)
      (compBlockMapVal L1 M2 mapVal1 mapVal2) := by
  intro Γ t e V
  show (M2.blockLowerCom (L1.lowerExprBlock e)).denote (mapVal2 (mapVal1 V))
      = transTy2 (transTy1 (e.denote V))
  have h2 := blockFundamental M2 transTy2 mapVal2 hVar2 hOp2 hExt2
    (L1.lowerExprBlock e) (mapVal1 V)
  exact h2.trans (congrArg transTy2 (hOp1 e V))

/-- **Whole-program transport square of a composite of two block lowerings.**
    Both stages may expand one op into several; each contributes only its own
    leaf obligations. -/
theorem compBlock_blockFundamental
    (hVar1 : VarTransports L1 transTy1 mapVal1)
    (hOp1 : BlockOpTransports L1 transTy1 mapVal1)
    (hExt1 : MapValExtends L1 transTy1 mapVal1)
    (hVar2 : VarTransports M2 transTy2 mapVal2)
    (hOp2 : BlockOpTransports M2 transTy2 mapVal2)
    (hExt2 : MapValExtends M2 transTy2 mapVal2)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ) :
    ((L1.compBlock M2).blockLowerCom c).denote (compBlockMapVal L1 M2 mapVal1 mapVal2 V)
      = compBlockTransTy L1 M2 transTy1 transTy2 (c.denote V) :=
  blockFundamental (L1.compBlock M2) (compBlockTransTy L1 M2 transTy1 transTy2)
    (compBlockMapVal L1 M2 mapVal1 mapVal2)
    (compBlock_varTransports L1 M2 transTy1 mapVal1 transTy2 mapVal2 hVar1 hVar2)
    (compBlock_blockOpTransports L1 M2 transTy1 mapVal1 transTy2 mapVal2 hOp1 hVar2 hOp2 hExt2)
    (compBlock_mapValExtends L1 M2 transTy1 mapVal1 transTy2 mapVal2 hExt1 hExt2) c V

end DenoteBlock

end SemanticBlock

/-! ## 4. Worked instantiation

`FieldDialectBlockDescent.Validation.dupBlockLowering` expands one source op
into a two-binding target block. Composing it with the identity single-`Expr`
lowering of the same toy dialect gives a composite that computes on a concrete
program and whose whole-program square is `comp_blockFundamental`. -/

namespace Validation

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent.Validation

/-- The identity single-`Expr` self-lowering of the toy dialect. -/
def idLowering : LoweringData toyDialect toyDialect where
  mapTy := id
  mapCtx := id
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => v
  lowerExpr := fun e => e

/-- Identity value transport of `idLowering`. -/
def idExprTransTy : ComParametricityTransport.TransTy idLowering := fun x => x

/-- Identity valuation transport of `idLowering`. -/
def idExprMapVal : ComParametricityTransport.MapVal idLowering := fun V => V

/-- Variable leaf of `idLowering`. -/
theorem idExprVarTransports :
    ComParametricityTransport.VarTransports idLowering idExprTransTy idExprMapVal :=
  fun _ _ => rfl

/-- Per-op leaf of `idLowering`. -/
theorem idExprOpLowerTransports :
    ComParametricityTransport.OpLowerTransports idLowering idExprTransTy idExprMapVal :=
  fun _ _ => rfl

/-- Binding-threading of `idLowering`. -/
theorem idExprMapValExtends :
    ComParametricityTransport.MapValExtends idLowering idExprTransTy idExprMapVal :=
  fun _ _ => rfl

/-- The one-op-to-two-block lowering composed with the identity single-`Expr`
    lowering. -/
def dupThenId : BlockLoweringData toyDialect toyDialect :=
  dupBlockLowering.comp idLowering

/-- **The composite's whole-program square.** For every toy program, the
    composite descent preserves denotation, from the two stages' leaf
    obligations through `comp_blockFundamental`. -/
theorem dupThenId_blockDescends {Γ : Ctxt toyDialect} {t : toyDialect.Ty}
    (c : Com toyDialect Γ t) (V : Ctxt.Valuation Γ) :
    (dupThenId.blockLowerCom c).denote
        (compMapVal dupBlockLowering idLowering idMapVal idExprMapVal V)
      = compTransTy dupBlockLowering idLowering idTransTy idExprTransTy (c.denote V) :=
  comp_blockFundamental dupBlockLowering idLowering idTransTy idMapVal
    idExprTransTy idExprMapVal
    dupVarTransports dupBlockOpTransports dupMapValExtends
    idExprVarTransports idExprOpLowerTransports idExprMapValExtends c V

/-- The composite's square on the concrete two-binding program. -/
theorem sampleProg_compDescends (V : Ctxt.Valuation ([()] : Ctxt toyDialect)) :
    (dupThenId.blockLowerCom sampleProg).denote
        (compMapVal dupBlockLowering idLowering idMapVal idExprMapVal V)
      = compTransTy dupBlockLowering idLowering idTransTy idExprTransTy (sampleProg.denote V) :=
  dupThenId_blockDescends sampleProg V

/-- A concrete input valuation for the one-element toy context. -/
def sampleInput : Ctxt.Valuation ([()] : Ctxt toyDialect) := .cons (7 : Nat) .nil

/-- The composite computes: the descended program evaluates on `sampleInput`.
    The source program has two bindings, each `dup` expands to a two-binding
    block, and the identity second stage passes the value through. -/
theorem dupThenId_sampleProg_eval :
    (dupThenId.blockLowerCom sampleProg).denote sampleInput = (7 : Nat) := rfl

end Validation

end CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringDataComp
