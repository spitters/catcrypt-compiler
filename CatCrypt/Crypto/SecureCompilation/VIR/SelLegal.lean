/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.SelDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86

/-!
# Legalisation of the lane-wise unsigned minimum and half-width multiply

A structured program over `tileSel d`, the operation sum of `scalarTile d` and the lane-wise
operation set `selTile d` (`VIR/SelDialect.lean`), is legalised to a program over `d` at a
lane shape `T : TileTarget d`. The record `SelTarget T` extends the shape with a gate for the
two operations: a two-operand block of `d` on the register type of the shape for `tileMinu`
and for `tileMulu`, or `none`, with the lane law of every block it gives.

`selLegal S` is a partial block lowering of `tileSel d` to `d` with the type map, the context
map and the value transports of `tileLegal T`. On an operation of `scalarTile d` its block is
the block of `tileLegal T` (`selLegal_ofScalarTileExpr`); on an operation of `selTile d` it is
the block of the gate of `S` at the shape of `T`, and `none` at every other shape. The
certificate of `legaliseSel S` has the input relation `packVal T` and the output relation
`packOuts T` of `tileLegalCert T`.

`dwordSel` and `qwordSel` extend the targets `selD` (sixteen 32-bit lanes) and `selQ` (eight
64-bit lanes) of `TileSelectX86` over `jasminVec`:

| operation | `dwordSel` 16x32 | `qwordSel` 8x64 |
|---|---|---|
| `tileMinu` | `lw 32 minu` | `lw 64 minu` |
| `tileMulu` | refused | `lw 64 muludq` |

## Main definitions

* `SelTarget`, `SelTarget.gate`, `SelTarget.Quiet`: the gate of the two operations at a lane
  shape, the gate on `SelTileOp`, and the leakage models in which its blocks emit no event.
* `tileSelPure`: the pure denotation of `tileSel d`, a local instance of this file.
* `selLegal`, `legaliseSel`: the partial block lowering of `tileSel d` and the program map.
* `tileSelSem`, `selLegalCert`: the semantics of programs of `tileSel d` and the step
  certificate of `legaliseSel`.
* `minuBlk`, `muluBlk`: the blocks of the lane-wise unsigned minimum and of `vpmuludq`.
* `dwordSel`, `qwordSel`: the gates at the two lane shapes of a ZMM register.
* `vecTileSel`, `dwordSelCert`, `qwordSelCert`: the source dialect over `jasminVec` and the
  step certificates at the two shapes.

## Main results

* `SelTarget.gate_sound`: a block of the gate computes the transport of the value of the
  lane-wise operation.
* `selLegal_ofScalarTileExpr`: on an expression of `scalarTile d` the block of `selLegal S`
  is the block of `tileLegal T`.
* `selLegal_denote`: a legalised program denotes, on the transported valuation, the transport
  of the results of its source, at every fuel.
* `selLegal_leakRun`: in a quiet model, a legalised program runs to the transported results
  and to the events of the source run.
* `minuBlk_spec`, `muluBlk_spec`: the lane laws of the two blocks.
* `dwordSel_quiet`, `qwordSel_quiet`, `dwordSel_leakRun`, `qwordSel_leakRun`: the blocks emit
  no event, and a legalised program runs to the events of its source.
* `sel_gate_table`: the entries of the table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SelLegal

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegalX86 (packAt)
open CatCrypt.Crypto.SecureCompilation.VIR.SelDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (LOp lane semLW lane_semLW)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (consHom lookup_pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (umin)
open Ctxt (Var Valuation)

/-! ## 1. The gate of the two operations at a lane shape -/

section Generic

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- **The gate of the lane-wise unsigned minimum and half-width multiply at the lane shape
    `T`.** A two-operand block of `d` on the register type of the shape for each operation,
    or `none`, with the lane law of every block it gives. -/
structure SelTarget (T : TileTarget d) where
  /-- The block of the lane-wise unsigned minimum. -/
  minu? : Option (Com d [T.regTy, T.regTy] T.regTy)
  /-- The block of the lane-wise half-width multiply. -/
  mulu? : Option (Com d [T.regTy, T.regTy] T.regTy)
  /-- Lane `k` of the minimum block is the unsigned minimum of lane `k` of the operands. -/
  minu_lane : ∀ blk, minu? = some blk →
    ∀ (a b : Fin T.laneCount → BitVec T.laneBits) (k : Fin T.laneCount),
      T.lane (blk.denote (.cons (T.pack T.shapeTy a) (.cons (T.pack T.shapeTy b) .nil))) k
        = umin (a k) (b k)
  /-- Lane `k` of the multiply block is the half-width product of lane `k` of the
      operands. -/
  mulu_lane : ∀ blk, mulu? = some blk →
    ∀ (a b : Fin T.laneCount → BitVec T.laneBits) (k : Fin T.laneCount),
      T.lane (blk.denote (.cons (T.pack T.shapeTy a) (.cons (T.pack T.shapeTy b) .nil))) k
        = halfProd (a k) (b k)

variable (T : TileTarget d)

/-- A two-operand block of the shape read at a tile type: the block at the shape of `T`, and
    `none` at every other shape. -/
def shapeGate (blk? : Option (Com d [T.regTy, T.regTy] T.regTy)) (n w : Nat) :
    Option (Com d [T.ty (.tile n w), T.ty (.tile n w)] (T.ty (.tile n w))) :=
  if h : n = T.laneCount ∧ w = T.laneBits then
    blk?.map (T.atShape (fun t => Com d [T.ty t, T.ty t] (T.ty t)) h)
  else none

/-- A block of `shapeGate` whose lanes at the shape are those of the lane-wise function `F`
    denotes, on packed operands, the packing of `F`. -/
theorem shapeGate_sound (blk? : Option (Com d [T.regTy, T.regTy] T.regTy))
    (F : ∀ {n w : Nat}, (Fin n → BitVec w) → (Fin n → BitVec w) → Fin n → BitVec w)
    (hF : ∀ blk, blk? = some blk →
      ∀ (a b : Fin T.laneCount → BitVec T.laneBits) (k : Fin T.laneCount),
        T.lane (blk.denote (.cons (T.pack T.shapeTy a) (.cons (T.pack T.shapeTy b) .nil))) k
          = F a b k)
    (n w : Nat) (blk : Com d [T.ty (.tile n w), T.ty (.tile n w)] (T.ty (.tile n w)))
    (h : shapeGate T blk? n w = some blk) (a b : Fin n → BitVec w) :
    blk.denote (.cons (T.pack (.tile n w) a) (.cons (T.pack (.tile n w) b) .nil)) =
      T.pack (.tile n w) (F a b) := by
  unfold shapeGate at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [TileTarget.atShape_self]
    refine T.lane_inj _ _ (fun k => ?_)
    rw [T.lane_pack, hF b0 h0 a b k]
  · cases h

variable {T}

/-- **The gate on `SelTileOp`.** The block of a lane-wise operation on its mapped argument
    context: the block of `S` at the shape of `T`, and `none` at every other shape. -/
def SelTarget.gate (S : SelTarget T) : (o : SelTileOp) →
    Option (Com d ((DialectSignature.sig (d := selTile d) o).map (legalTy T))
      (legalTy T (DialectSignature.ret (d := selTile d) o)))
  | .tileMinu n w => shapeGate T S.minu? n w
  | .tileMulu n w => shapeGate T S.mulu? n w

/-- **The gate is sound.** A block of the gate denotes, on the packed argument values, the
    packing of the value of the lane-wise operation. -/
theorem SelTarget.gate_sound (S : SelTarget T) (o : SelTileOp)
    (blk : Com d ((DialectSignature.sig (d := selTile d) o).map (legalTy T))
      (legalTy T (DialectSignature.ret (d := selTile d) o)))
    (h : S.gate o = some blk)
    (args : HVector (fun t : d.Ty ⊕ TileTy => ⟦t⟧)
      (DialectSignature.sig (d := selTile d) o)) :
    blk.denote (transArgs (legalTy T) (packTy T) args) =
      packTy T (DialectDenote.denote (d := selTile d) o args) := by
  cases o with
  | tileMinu n w =>
      cases args with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      exact shapeGate_sound T S.minu? tileMinuApply S.minu_lane n w blk h a b
  | tileMulu n w =>
      cases args with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      exact shapeGate_sound T S.mulu? tileMuluApply S.mulu_lane n w blk h a b

/-- The leakage models of `d` in which the blocks of `S` emit no event. -/
structure SelTarget.Quiet (S : SelTarget T) (M : LeakModel d) : Prop where
  /-- The minimum block emits no event. -/
  minu : ∀ blk, S.minu? = some blk → ∀ W, Com.ctLeak M blk W = []
  /-- The multiply block emits no event. -/
  mulu : ∀ blk, S.mulu? = some blk → ∀ W, Com.ctLeak M blk W = []

/-- A block of the gate emits no event in a quiet model. -/
theorem SelTarget.Quiet.gate {S : SelTarget T} {M : LeakModel d} (hQ : S.Quiet M)
    (o : SelTileOp)
    (blk : Com d ((DialectSignature.sig (d := selTile d) o).map (legalTy T))
      (legalTy T (DialectSignature.ret (d := selTile d) o)))
    (h : S.gate o = some blk) (W : Valuation (d := d) _) : Com.ctLeak M blk W = [] := by
  cases o <;> simp only [SelTarget.gate, shapeGate] at h <;> split at h <;>
    first
    | cases h
    | (rename_i hs
       obtain ⟨rfl, rfl⟩ := hs
       obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
       rw [TileTarget.atShape_self]
       first
       | exact hQ.minu b0 h0 W
       | exact hQ.mulu b0 h0 W)

/-! ## 2. The lowering of the operation sum -/

/-- The pure denotation of `tileSel d` over a pure denotation of `d`: an operation of
    `scalarTile d` by the denotation of the coproduct, a lane-wise operation by its
    denotation. -/
@[instance_reducible] def tileSelPure (d : Dialect.{0, 0}) [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d] : DialectDenote (tileSel d) where
  denote
    | .inl o => fun args => (scalarTilePure d).denote o args
    | .inr o => fun args => DialectDenote.denote (d := selTile d) o args

attribute [local instance] scalarTilePure tileSelPure

/-- The renaming of the mapped argument context of a lane-wise operation to its mapped
    argument variables. -/
def selArgHom (T : TileTarget d) {Γ : Ctxt (tileSel d)} : (ts : List (d.Ty ⊕ TileTy)) →
    HVector (fun t => Var Γ t) ts →
    Ctxt.Hom (d := d) (ts.map (legalTy T)) ((tileLegal T).mapCtx Γ)
  | [], _ => fun v => nomatch v
  | _ :: ts, .cons a as => fun v =>
      consHom (selArgHom T ts as) ((tileLegal T).mapVar (castVar a)) v

/-- **Legalisation of `tileSel d` at the shape `T` with the gate `S`**: the partial block
    lowering with the type, context and variable maps of `tileLegal T` that gives an
    operation of `scalarTile d` the block of `tileLegal T` and a lane-wise operation the
    block of the gate of `S`. -/
@[reducible] def selLegal (S : SelTarget T) : PartialBlockLowering (tileSel d) d where
  mapTy := (tileLegal T).mapTy
  mapCtx := (tileLegal T).mapCtx
  mapCtx_cons := (tileLegal T).mapCtx_cons
  mapVar := fun v => (tileLegal T).mapVar (castVar v)
  lowerExprBlock? := fun e =>
    match e with
    | ⟨.inl o, h, args⟩ => (tileLegal T).lowerExprBlock? ⟨o, h, castArgs args⟩
    | ⟨.inr o, h, args⟩ =>
        (S.gate o).map fun blk => h ▸ Com.rename (selArgHom T _ args) blk

/-- A variable read in another dialect over the same types and back is the variable. -/
theorem castVar_castVar {O O' A : Type} :
    ∀ {Γ : List A} {t : A} (v : Var (d := ⟨O, A⟩) Γ t),
      castVar (O := O') (O' := O) (castVar (O' := O') v) = v
  | _, _, .here => rfl
  | _, _, .there v => congrArg Var.there (castVar_castVar v)

/-- Arguments read in another dialect over the same types and back are the arguments. -/
theorem castArgs_castArgs {O O' A : Type} {Γ : List A} :
    ∀ {ts : List A} (args : HVector (fun t => Var (d := ⟨O, A⟩) Γ t) ts),
      castArgs (O := O') (O' := O) (castArgs (O' := O') args) = args
  | [], .nil => rfl
  | _ :: _, .cons v vs => congrArg₂ HVector.cons (castVar_castVar v) (castArgs_castArgs vs)

/-- **The two legalisations agree on `scalarTile d`.** On an expression of `scalarTile d`
    included in `tileSel d`, the block of `selLegal S` is the block of `tileLegal T`. -/
theorem selLegal_ofScalarTileExpr (S : SelTarget T) {Γ : List (d.Ty ⊕ TileTy)}
    {t : d.Ty ⊕ TileTy} (e : Expr (scalarTile d) Γ t) :
    (selLegal S).lowerExprBlock? (ofScalarTileExpr d e) = (tileLegal T).lowerExprBlock? e := by
  obtain ⟨op, h, args⟩ := e
  show (tileLegal T).lowerExprBlock? ⟨op, h, castArgs (castArgs args)⟩ = _
  rw [castArgs_castArgs]

/-- The variable leaf of `selLegal S`. -/
theorem selLegal_varTransports (S : SelTarget T) :
    (selLegal S).VarTransports (packTy T) (packVal T) :=
  fun v V => (tileLegal_varTransports T (castVar v) V).trans
    (congrArg (packTy T) (lookup_castVar v V))

/-- The binding leaf of `selLegal S`. -/
theorem selLegal_mapValExtends (S : SelTarget T) :
    (selLegal S).MapValExtends (packTy T) (packVal T) :=
  fun V x => tileLegal_mapValExtends T V x

/-- The transported valuation read along `selArgHom` is the transport of the argument
    values. -/
theorem pullV_selArgHom (T : TileTarget d) {Γ : Ctxt (tileSel d)} (V : Valuation Γ) :
    (ts : List (d.Ty ⊕ TileTy)) → (args : HVector (fun t => Var Γ t) ts) →
    pullV (selArgHom T ts args) (packVal T V) =
      transArgs (legalTy T) (packTy T) (Expr.lookupArgs (d := tileSel d) args V)
  | [], .nil => rfl
  | _ :: ts, .cons a as => by
      show HVector.cons (((tileLegal T).mapVar (castVar a)).lookup (packVal T V))
        (pullV (selArgHom T ts as) (packVal T V)) = HVector.cons _ _
      rw [tileLegal_varTransports T (castVar a) V, pullV_selArgHom T V ts as,
        lookup_castVar a V]

/-- **The block leaf of `selLegal S`.** -/
theorem selLegal_block (S : SelTarget T) {Γ : Ctxt (tileSel d)} {t : (tileSel d).Ty}
    (ex : Expr (tileSel d) Γ t)
    (blk : Com d ((selLegal S).mapCtx Γ) ((selLegal S).mapTy t))
    (hb : (selLegal S).lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    blk.denote (packVal T V) = packTy T (ex.denote V) := by
  obtain ⟨op, rfl, args⟩ := ex
  cases op with
  | inl o =>
      refine (tileLegal_block T ⟨o, rfl, castArgs args⟩ blk hb V).trans ?_
      show packTy T (DialectDenote.denote (d := scalarTile d) o
        (Expr.lookupArgs (d := scalarTile d) (castArgs args) V)) = _
      rw [lookupArgs_castArgs args V]
      rfl
  | inr o =>
      obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
      refine (Com.denote_rename (selArgHom T _ args) b0 (packVal T V)).trans ?_
      rw [pullV_selArgHom]
      exact S.gate_sound o b0 h0 _

/-- **The block leak leaf of `selLegal S`** in a model in which the blocks of `T` and of `S`
    are quiet. -/
theorem selLegal_blockLeak {S : SelTarget T} {M : LeakModel d} (hT : T.Quiet M)
    (hS : S.Quiet M) {Γ : Ctxt (tileSel d)} {t : (tileSel d).Ty}
    (ex : Expr (tileSel d) Γ t)
    (blk : Com d ((selLegal S).mapCtx Γ) ((selLegal S).mapTy t))
    (hb : (selLegal S).lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    Com.ctLeak M blk (packVal T V) = Expr.ctLeak (tileSelLeak d M) ex V := by
  obtain ⟨op, rfl, args⟩ := ex
  cases op with
  | inl o =>
      refine (tileLegal_blockLeak hT ⟨o, rfl, castArgs args⟩ blk hb V).trans ?_
      show opLeak (scalarTileLeak d M) o
          (Expr.lookupArgs (d := scalarTile d) (castArgs args) V) =
        opLeak (tileSelLeak d M) (.inl o) (Expr.lookupArgs (d := tileSel d) args V)
      rw [lookupArgs_castArgs args V, tileSel_opLeak_inl]
  | inr o =>
      obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
      refine (NFProg.Com.ctLeak_rename_pullV M (selArgHom T _ args) b0 (packVal T V)).trans ?_
      exact hS.gate o b0 h0 _

variable [HasWord64 d] [HasBoolBit d]

/-- The type map of `selLegal S` keeps the trip-counter type and the bit type. -/
theorem selLegal_regionTypes (S : SelTarget T) : (selLegal S).RegionTypes := ⟨rfl, rfl⟩

/-- The value transport of `selLegal S` keeps trip counts, trip indices and bits. -/
theorem selLegal_regionTransports (S : SelTarget T) :
    (selLegal S).RegionTransports (selLegal_regionTypes S) (packTy T) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **Legalisation of a program of `tileSel d`.** The lowering of a program without `call`
    along `selLegal S`; `none` when the program has a `call` or an operation one of the two
    gates refuses. -/
def legaliseSel (S : SelTarget T) {Γ : Ctxt (tileSel d)} {ts : List (tileSel d).Ty}
    (p : NFProg (tileSel d) Γ ts) :
    Option (NFProg d (Γ.map (legalTy T)) (ts.map (legalTy T))) :=
  if p.callFree = true then
    NFProg.map? (selLegal S) (selLegal_regionTypes S) p (fun v => v)
  else none

omit [HasWord64 d] [HasBoolBit d] in
/-- The denotation of `tileSel d` over the pure denotation of `d` is the pure denotation of
    the operation sum. -/
theorem tileSelDenote_pure :
    tileSelDenote d (instDialectDenoteMOptionOfPure d) =
      instDialectDenoteMOptionOfPure (tileSel d) := by
  show DialectDenoteM.mk _ = DialectDenoteM.mk _
  congr 1
  funext op args
  rcases op with o | o
  · cases o <;> rfl
  · rfl

/-- **Legalisation preserves denotations.** A legalised program denotes, on the transported
    valuation, the transport of the results of its source, at every fuel. -/
theorem selLegal_denote [CallDenote d] (S : SelTarget T) (fuel : Nat)
    {Γ : Ctxt (tileSel d)} {ts : List (tileSel d).Ty} (p : NFProg (tileSel d) Γ ts)
    (q : NFProg d (Γ.map (legalTy T)) (ts.map (legalTy T))) (h : legaliseSel S p = some q)
    (V : Valuation Γ) :
    q.denote fuel (packVal T V) =
      (tileSelDenP d (instDialectDenoteMOptionOfPure d) fuel p V).map (packOuts T) := by
  unfold legaliseSel at h
  split at h
  · rename_i hc
    unfold tileSelDenP
    rw [tileSelDenote_pure]
    exact NFProg.map?_denote (selLegal S) (packTy T) (packVal T) (selLegal_regionTypes S)
      (fun _ => True) (selLegal_varTransports S)
      (fun ex _ blk hb V => selLegal_block S ex blk hb V) (selLegal_mapValExtends S)
      (selLegal_regionTransports S) fuel p hc
      (NFProg.covered_of_forall _ (fun _ => trivial) p) _ V _ (pullV_id _) q h
  · cases h

/-- **Legalisation preserves runs and events.** In a model of `d` in which the blocks of `T`
    and of `S` are quiet, a legalised program runs, on the transported valuation, to the
    transport of the results and to the events of the run of its source. -/
theorem selLegal_leakRun {S : SelTarget T} {M : LeakModel d} (hT : T.Quiet M)
    (hS : S.Quiet M) (fuel : Nat)
    {Γ : Ctxt (tileSel d)} {ts : List (tileSel d).Ty} (p : NFProg (tileSel d) Γ ts)
    (q : NFProg d (Γ.map (legalTy T)) (ts.map (legalTy T))) (h : legaliseSel S p = some q)
    (V : Valuation Γ) :
    NFProg.leakRun M fuel q (packVal T V) =
      (tileSelLeakRun d (instDialectDenoteMOptionOfPure d) M fuel p V).map
        fun r => (packOuts T r.1, r.2) := by
  unfold legaliseSel at h
  split at h
  · unfold tileSelLeakRun
    rw [tileSelDenote_pure, NFProg.leakRunM_eq_leakRun]
    exact NFProg.map?_leakRun (selLegal S) (packTy T) (packVal T) (tileSelLeak d M) M
      (selLegal_regionTypes S) (fun _ => True) (selLegal_varTransports S)
      (fun ex _ blk hb V => selLegal_block S ex blk hb V)
      (fun ex _ blk hb V => selLegal_blockLeak hT hS ex blk hb V) (selLegal_mapValExtends S)
      (selLegal_regionTransports S) fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) _ V _ (pullV_id _) q h
  · cases h

/-- The semantics of programs of `tileSel d` over the pure denotation of `d`, at the fuel
    `fuel`. -/
def tileSelSem (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    [HasWord64 d] [HasBoolBit d] (fuel : Nat) (Γ : Ctxt (tileSel d))
    (ts : List (tileSel d).Ty) : PassChain.Sem (NFProg (tileSel d) Γ ts) where
  In := Valuation Γ
  Out := Valuation ts
  den := fun p V => tileSelDenP d (instDialectDenoteMOptionOfPure d) fuel p V

open PassChain in
/-- **The certificate of legalisation.** The step `legaliseSel S` from the semantics of
    programs of `tileSel d` to that of programs of `d`: the input relation is the graph of
    `packVal T` and the output relation the graph of `packOuts T`, as in `tileLegalCert T`. -/
def selLegalCert [CallDenote d] (S : SelTarget T) (fuel : Nat) (Γ : Ctxt (tileSel d))
    (ts : List (tileSel d).Ty) :
    StepCert (legaliseSel S (Γ := Γ) (ts := ts)) (tileSelSem d fuel Γ ts)
      (targetSem d fuel (Γ.map (legalTy T)) (ts.map (legalTy T))) :=
  StepCert.ofTransport _ _ (fun V => packVal T V) (fun o => packOuts T o)
    fun p q V hf => selLegal_denote S fuel p q hf V

end Generic

/-! ## 3. The two lane shapes of a ZMM register -/

section X86

variable {L n r : Nat}

/-- The block of the lane-wise unsigned minimum at lanes of `L` bits: one instruction. -/
def minuBlk (L : Nat) : Blk2 := .var (lwE L .minu .here (.there .here)) (.ret .here)

/-- The block of the half-width multiply of qword lanes: one `vpmuludq`. -/
def muluBlk : Blk2 := .var (lwE 64 .muludq .here (.there .here)) (.ret .here)

/-- **The lane law of `minuBlk`**: lane `k` of its value is the unsigned minimum of lane `k`
    of its operands, and its operation is a vector operation. -/
theorem minuBlk_spec (hS : IsShape L n r) :
    (∀ (x y : BitVec 512) (k : Fin n),
      vlane L n ((minuBlk L).denote (.cons x (.cons y .nil))) k =
        tileMinuApply (vlane L n x) (vlane L n y) k) ∧ allVec (minuBlk L) := by
  refine ⟨fun x y k => ?_, ⟨_, rfl⟩, trivial⟩
  unfold minuBlk vlane
  simp only [denote_var, denote_ret, lookup_here, lwE_denote]
  rw [tileSelect_lookup_here_cons, tileSelect_lookup_there_cons, tileSelect_lookup_here_cons]
  exact lane_semLW .minu x y hS.pos.1 (hS.bound k.isLt)

/-- **The lane law of `muluBlk`**: qword `k` of its value is the half-width product of qword
    `k` of its operands, and its operation is a vector operation. -/
theorem muluBlk_spec :
    (∀ (x y : BitVec 512) (k : Fin 8),
      vlane 64 8 (muluBlk.denote (.cons x (.cons y .nil))) k =
        tileMuluApply (vlane 64 8 x) (vlane 64 8 y) k) ∧ allVec muluBlk := by
  refine ⟨fun x y k => ?_, ⟨_, rfl⟩, trivial⟩
  unfold muluBlk vlane
  simp only [denote_var, denote_ret, lookup_here, lwE_denote]
  rw [tileSelect_lookup_here_cons, tileSelect_lookup_there_cons, tileSelect_lookup_here_cons]
  exact lane_semLW .muludq x y (by omega) (isShape_qword.bound k.isLt)

/-- The lane-wise minimum of the lanes of two packed tiles of sixteen 32-bit lanes. -/
theorem minu_packAt_dword (a b : Fin 16 → BitVec 32) (k : Fin 16) :
    tileMinuApply (vlane 32 16 (packAt 16 32 (vof 32 16) (.tile 16 32) a))
      (vlane 32 16 (packAt 16 32 (vof 32 16) (.tile 16 32) b)) k = umin (a k) (b k) := by
  rw [vlane_packAt_dword a, vlane_packAt_dword b]
  rfl

/-- The lane-wise minimum of the lanes of two packed tiles of eight 64-bit lanes. -/
theorem minu_packAt_qword (a b : Fin 8 → BitVec 64) (k : Fin 8) :
    tileMinuApply (vlane 64 8 (packAt 8 64 (vof 64 8) (.tile 8 64) a))
      (vlane 64 8 (packAt 8 64 (vof 64 8) (.tile 8 64) b)) k = umin (a k) (b k) := by
  rw [vlane_packAt_qword a, vlane_packAt_qword b]
  rfl

/-- The lane-wise half-width product of the lanes of two packed tiles of eight 64-bit
    lanes. -/
theorem mulu_packAt_qword (a b : Fin 8 → BitVec 64) (k : Fin 8) :
    tileMuluApply (vlane 64 8 (packAt 8 64 (vof 64 8) (.tile 8 64) a))
      (vlane 64 8 (packAt 8 64 (vof 64 8) (.tile 8 64) b)) k = halfProd (a k) (b k) := by
  rw [vlane_packAt_qword a, vlane_packAt_qword b]
  rfl

/-- Lane `k` of `minuBlk 32` on packed tiles of sixteen 32-bit lanes. -/
theorem minuBlk_dword (a b : Fin 16 → BitVec 32) (k : Fin 16) :
    vlane 32 16 ((minuBlk 32).denote (.cons (packAt 16 32 (vof 32 16) (.tile 16 32) a)
      (.cons (packAt 16 32 (vof 32 16) (.tile 16 32) b) .nil))) k = umin (a k) (b k) :=
  ((minuBlk_spec isShape_dword).1 (packAt 16 32 (vof 32 16) (.tile 16 32) a)
    (packAt 16 32 (vof 32 16) (.tile 16 32) b) k).trans (minu_packAt_dword a b k)

/-- Lane `k` of `minuBlk 64` on packed tiles of eight 64-bit lanes. -/
theorem minuBlk_qword (a b : Fin 8 → BitVec 64) (k : Fin 8) :
    vlane 64 8 ((minuBlk 64).denote (.cons (packAt 8 64 (vof 64 8) (.tile 8 64) a)
      (.cons (packAt 8 64 (vof 64 8) (.tile 8 64) b) .nil))) k = umin (a k) (b k) :=
  ((minuBlk_spec isShape_qword).1 (packAt 8 64 (vof 64 8) (.tile 8 64) a)
    (packAt 8 64 (vof 64 8) (.tile 8 64) b) k).trans (minu_packAt_qword a b k)

/-- Lane `k` of `muluBlk` on packed tiles of eight 64-bit lanes. -/
theorem muluBlk_qword (a b : Fin 8 → BitVec 64) (k : Fin 8) :
    vlane 64 8 (muluBlk.denote (.cons (packAt 8 64 (vof 64 8) (.tile 8 64) a)
      (.cons (packAt 8 64 (vof 64 8) (.tile 8 64) b) .nil))) k = halfProd (a k) (b k) :=
  (muluBlk_spec.1 (packAt 8 64 (vof 64 8) (.tile 8 64) a)
    (packAt 8 64 (vof 64 8) (.tile 8 64) b) k).trans (mulu_packAt_qword a b k)

/-- The value transport of `selD` at its shape is the lane assembly. -/
theorem selD_pack (a : Fin 16 → BitVec 32) :
    selD.pack (.tile 16 32) a = packAt 16 32 (vof 32 16) (.tile 16 32) a := by
  simp only [selD]

/-- The value transport of `selQ` at its shape is the lane assembly. -/
theorem selQ_pack (a : Fin 8 → BitVec 64) :
    selQ.pack (.tile 8 64) a = packAt 8 64 (vof 64 8) (.tile 8 64) a := by
  simp only [selQ]

/-- **The gate at sixteen 32-bit lanes.** The unsigned minimum is `vpminud`; the half-width
    multiply is refused. -/
def dwordSel : SelTarget selD where
  minu? := some (minuBlk 32)
  mulu? := none
  minu_lane := by
    intro blk h a b k
    cases h
    exact (congrArg₂
      (fun u v : BitVec 512 => vlane 32 16 ((minuBlk 32).denote (.cons u (.cons v .nil))) k)
      (selD_pack a) (selD_pack b)).trans (minuBlk_dword a b k)
  mulu_lane := by
    intro blk h
    cases h

/-- **The gate at eight 64-bit lanes.** The unsigned minimum is `vpminuq`; the half-width
    multiply is `vpmuludq`. -/
def qwordSel : SelTarget selQ where
  minu? := some (minuBlk 64)
  mulu? := some muluBlk
  minu_lane := by
    intro blk h a b k
    cases h
    exact (congrArg₂
      (fun u v : BitVec 512 => vlane 64 8 ((minuBlk 64).denote (.cons u (.cons v .nil))) k)
      (selQ_pack a) (selQ_pack b)).trans (minuBlk_qword a b k)
  mulu_lane := by
    intro blk h a b k
    cases h
    exact (congrArg₂
      (fun u v : BitVec 512 => vlane 64 8 (muluBlk.denote (.cons u (.cons v .nil))) k)
      (selQ_pack a) (selQ_pack b)).trans (muluBlk_qword a b k)

/-- The blocks of `dwordSel` emit no event, over every leakage model of `jasminDialect`. -/
theorem dwordSel_quiet (M : LeakModel jasminDialect) : dwordSel.Quiet (jasminVecLeak M) where
  minu := by
    intro blk h W
    cases h
    exact ctLeak_allVec M _ (minuBlk_spec isShape_dword).2 W
  mulu := by
    intro blk h
    cases h

/-- The blocks of `qwordSel` emit no event, over every leakage model of `jasminDialect`. -/
theorem qwordSel_quiet (M : LeakModel jasminDialect) : qwordSel.Quiet (jasminVecLeak M) where
  minu := by
    intro blk h W
    cases h
    exact ctLeak_allVec M _ (minuBlk_spec isShape_qword).2 W
  mulu := by
    intro blk h W
    cases h
    exact ctLeak_allVec M _ muluBlk_spec.2 W

/-- The operation sum of `scalarTile jasminVec` and the lane-wise operation set: the source
    dialect of the legalisation over `jasminVec`. -/
abbrev vecTileSel : Dialect := tileSel jasminVec

instance : DialectSignature vecTileSel := instDialectSignatureTileSel jasminVec
instance : HasWord64 vecTileSel := instHasWord64TileSel jasminVec
instance : HasBoolBit vecTileSel := instHasBoolBitTileSel jasminVec
instance : CallDenote vecTileSel := instCallDenoteTileSel jasminVec

open PassChain in
/-- **The certificate of legalisation at sixteen 32-bit lanes.** -/
def dwordSelCert (fuel : Nat) (Γ : Ctxt vecTileSel) (ts : List vecTileSel.Ty) :
    StepCert (legaliseSel dwordSel (Γ := Γ) (ts := ts)) (tileSelSem jasminVec fuel Γ ts)
      (targetSem jasminVec fuel (Γ.map (legalTy selD)) (ts.map (legalTy selD))) :=
  selLegalCert dwordSel fuel Γ ts

open PassChain in
/-- **The certificate of legalisation at eight 64-bit lanes.** -/
def qwordSelCert (fuel : Nat) (Γ : Ctxt vecTileSel) (ts : List vecTileSel.Ty) :
    StepCert (legaliseSel qwordSel (Γ := Γ) (ts := ts)) (tileSelSem jasminVec fuel Γ ts)
      (targetSem jasminVec fuel (Γ.map (legalTy selQ)) (ts.map (legalTy selQ))) :=
  selLegalCert qwordSel fuel Γ ts

/-- **Legalisation at sixteen 32-bit lanes preserves runs and events.** -/
theorem dwordSel_leakRun (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt vecTileSel} {ts : List vecTileSel.Ty}
    (p : NFProg vecTileSel Γ ts)
    (q : NFProg jasminVec (Γ.map (legalTy selD)) (ts.map (legalTy selD)))
    (h : legaliseSel dwordSel p = some q) (V : Valuation Γ) :
    NFProg.leakRun (jasminVecLeak M) fuel q (packVal selD V) =
      (tileSelLeakRun jasminVec (instDialectDenoteMOptionOfPure jasminVec) (jasminVecLeak M)
        fuel p V).map fun r => (packOuts selD r.1, r.2) :=
  selLegal_leakRun (selD_quiet M) (dwordSel_quiet M) fuel p q h V

/-- **Legalisation at eight 64-bit lanes preserves runs and events.** -/
theorem qwordSel_leakRun (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt vecTileSel} {ts : List vecTileSel.Ty}
    (p : NFProg vecTileSel Γ ts)
    (q : NFProg jasminVec (Γ.map (legalTy selQ)) (ts.map (legalTy selQ)))
    (h : legaliseSel qwordSel p = some q) (V : Valuation Γ) :
    NFProg.leakRun (jasminVecLeak M) fuel q (packVal selQ V) =
      (tileSelLeakRun jasminVec (instDialectDenoteMOptionOfPure jasminVec) (jasminVecLeak M)
        fuel p V).map fun r => (packOuts selQ r.1, r.2) :=
  selLegal_leakRun (selQ_quiet M) (qwordSel_quiet M) fuel p q h V

/-- **The gate table.** The unsigned minimum is one lane-wise `minu` at both shapes; the
    half-width multiply is one `vpmuludq` at qword lanes and refused at dword lanes. -/
theorem sel_gate_table :
    dwordSel.gate (.tileMinu 16 32) = some (minuBlk 32) ∧
      qwordSel.gate (.tileMinu 8 64) = some (minuBlk 64) ∧
      qwordSel.gate (.tileMulu 8 64) = some muluBlk ∧
      dwordSel.gate (.tileMulu 16 32) = none :=
  ⟨rfl, rfl, rfl, rfl⟩

end X86

end CatCrypt.Crypto.SecureCompilation.VIR.SelLegal
