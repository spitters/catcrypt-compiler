/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproductElim
public import CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-!
# Legalisation of tile operations at a lane shape

A structured program over `scalarTile d` (the coproduct of a scalar dialect `d` and
`tileDialect`) is legalised to a program over `d` at a lane shape of the target. The shape
is a record `TileTarget d`: a lane count and a lane width, a type of `d` for every tile type
with a value transport `pack`, the lane read of the register type of the shape with its
two laws, and a gate that gives a straight-line block of `d` for a constant, a one-operand
or a two-operand tile operation at the shape, or refuses it. A tile operation at another
shape is refused. The scalar summand passes by the identity.

`tileLegal T` is the partial block lowering `T.lowering.sumElimId`, and `legalise T` is
`NFProg.map?` along it on programs without `call`.

## Main definitions

* `UnOp`, `BinOp` — the one-operand and two-operand tile operations at a fixed shape.
* `TileTarget` — the lane shape of a target with its gate and lane laws.
* `TileTarget.gate`, `TileTarget.lowering` — the gate on `TileOp` and the partial block
  lowering of `tileDialect`.
* `TileTarget.Quiet` — the leakage models of `d` in which the blocks of the gate emit no
  event.
* `scalarTilePure` — the pure denotation of `scalarTile d`, a local instance of this file.
* `tileLegal`, `legalTy`, `packTy`, `packVal`, `legalise` — the lowering of the coproduct,
  its type map, its transports and the program map.
* `scalarTileSem`, `tileLegalCert` — the semantics of programs of `scalarTile d` and the
  step certificate of `legalise`.

## Main results

* `TileTarget.gate_sound` — a block of the gate computes the transport of the value of the
  tile operation.
* `tileLegal_denote` — a legalised program denotes, on the transported valuation, the
  transport of the results of its source, at every fuel.
* `tileLegal_leakRun` — in a quiet model, a legalised program runs to the transported
  results and to the events of the source run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileLegal

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (consHom lookup_pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

/-! ## 1. Tile operations at a fixed shape -/

/-- The one-operand tile operations at a fixed shape. -/
inductive UnOp where
  /-- `tileBroadcast` of the lane `lane`. -/
  | broadcast (lane : Nat)
  /-- `tileReduce`. -/
  | reduce
  /-- `tileShiftImm` by the immediate `k`. -/
  | shiftImm (op : TileImmOp) (k : Nat)
  deriving DecidableEq

/-- The two-operand tile operations at a fixed shape. -/
inductive BinOp where
  /-- `tileBin`. -/
  | bin (bop : JasminBinOp)
  /-- `tilePermute`: the first operand is the index tile. -/
  | permute
  /-- `tileMulhu`. -/
  | mulhu
  /-- `tileShuffle` by the index list `idx`. -/
  | shuffle (idx : List Nat)
  /-- `tileBlend` by the mask `mask`. -/
  | blend (mask : List Bool)

/-- The value of a one-operand tile operation. -/
def UnOp.apply {n w : Nat} : UnOp → (Fin n → BitVec w) → Fin n → BitVec w
  | .broadcast l, a => tileBroadcastApply l a
  | .reduce, a => tileReduceApply a
  | .shiftImm op k, a => tileShiftImmApply op k a

/-- The value of a two-operand tile operation. -/
def BinOp.apply {n w : Nat} : BinOp → (Fin n → BitVec w) → (Fin n → BitVec w) →
    Fin n → BitVec w
  | .bin bop, a, b => tileBinApply bop a b
  | .permute, idx, a => tilePermuteApply idx a
  | .mulhu, a, b => tileMulhuApply a b
  | .shuffle idx, a, b => tileShuffleApply idx a b
  | .blend mask, a, b => tileBlendApply mask a b

/-! ## 2. The lane shape of a target -/

/-- **The lane shape of a target dialect `d`.** `laneCount` lanes of `laneBits` bits; a
    type of `d` for every tile type and the value transport `pack`; the lane read `lane` of
    the type of the shape, which inverts `pack` and is injective; and the gate: a block of
    `d` for a constant, a one-operand and a two-operand tile operation at the shape, or
    `none`, with the lane law of every block it gives. -/
structure TileTarget (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] where
  /-- Number of lanes. -/
  laneCount : Nat
  /-- Width of one lane. -/
  laneBits : Nat
  /-- The type of `d` that holds a tile. -/
  ty : TileTy → d.Ty
  /-- The value of `d` that holds a tile. -/
  pack : (t : TileTy) → ⟦t⟧ → ⟦ty t⟧
  /-- Lane `k` of a value of the type of the shape. -/
  lane : ⟦ty (.tile laneCount laneBits)⟧ → Fin laneCount → BitVec laneBits
  /-- Lane `k` of a packed tile is its lane `k`. -/
  lane_pack : ∀ (x : Fin laneCount → BitVec laneBits) (k : Fin laneCount),
    lane (pack (.tile laneCount laneBits) x) k = x k
  /-- Two values with equal lanes are equal. -/
  lane_inj : ∀ x y : ⟦ty (.tile laneCount laneBits)⟧, (∀ k, lane x k = lane y k) → x = y
  /-- The block of the constant tile of the value `c`. -/
  const? : Nat → Option (Com d [] (ty (.tile laneCount laneBits)))
  /-- The block of a one-operand tile operation. -/
  unary? : UnOp → Option
    (Com d [ty (.tile laneCount laneBits)] (ty (.tile laneCount laneBits)))
  /-- The block of a two-operand tile operation. -/
  binary? : BinOp → Option
    (Com d [ty (.tile laneCount laneBits), ty (.tile laneCount laneBits)]
      (ty (.tile laneCount laneBits)))
  /-- Every lane of a constant block is the constant. -/
  const_lane : ∀ c blk, const? c = some blk → ∀ k : Fin laneCount,
    lane (blk.denote .nil) k = BitVec.ofNat laneBits c
  /-- Lane `k` of a one-operand block is lane `k` of the tile operation. -/
  unary_lane : ∀ o blk, unary? o = some blk →
    ∀ (a : Fin laneCount → BitVec laneBits) (k : Fin laneCount),
      lane (blk.denote (.cons (pack (.tile laneCount laneBits) a) .nil)) k = o.apply a k
  /-- Lane `k` of a two-operand block is lane `k` of the tile operation. -/
  binary_lane : ∀ o blk, binary? o = some blk →
    ∀ (a b : Fin laneCount → BitVec laneBits) (k : Fin laneCount),
      lane (blk.denote (.cons (pack (.tile laneCount laneBits) a)
        (.cons (pack (.tile laneCount laneBits) b) .nil))) k = o.apply a b k

namespace TileTarget

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  (T : TileTarget d)

/-- The tile type of the shape. -/
abbrev shapeTy : TileTy := .tile T.laneCount T.laneBits

/-- The type of `d` of the shape. -/
abbrev regTy : d.Ty := T.ty T.shapeTy

/-- A value of the type of the shape is the packing of its lanes. -/
theorem pack_lane (x : ⟦T.regTy⟧) : T.pack T.shapeTy (T.lane x) = x :=
  T.lane_inj _ _ (fun k => T.lane_pack _ k)

/-- A family at the tile type of the shape, read at an equal tile type. -/
def atShape (F : TileTy → Type) {n w : Nat} (h : n = T.laneCount ∧ w = T.laneBits)
    (x : F T.shapeTy) : F (.tile n w) :=
  h.1 ▸ h.2 ▸ x

/-- `atShape` at the shape is the identity. -/
@[simp] theorem atShape_self (F : TileTy → Type)
    (h : T.laneCount = T.laneCount ∧ T.laneBits = T.laneBits) (x : F T.shapeTy) :
    T.atShape F h x = x := rfl

/-- The gate at a constant of a tile type. -/
def constGate (n w c : Nat) : Option (Com d [] (T.ty (.tile n w))) :=
  if h : n = T.laneCount ∧ w = T.laneBits then
    (T.const? c).map (T.atShape (fun t => Com d [] (T.ty t)) h)
  else none

/-- The gate at a one-operand operation of a tile type. -/
def unaryGate (n w : Nat) (o : UnOp) : Option (Com d [T.ty (.tile n w)] (T.ty (.tile n w))) :=
  if h : n = T.laneCount ∧ w = T.laneBits then
    (T.unary? o).map (T.atShape (fun t => Com d [T.ty t] (T.ty t)) h)
  else none

/-- The gate at a two-operand operation of a tile type. -/
def binaryGate (n w : Nat) (o : BinOp) :
    Option (Com d [T.ty (.tile n w), T.ty (.tile n w)] (T.ty (.tile n w))) :=
  if h : n = T.laneCount ∧ w = T.laneBits then
    (T.binary? o).map (T.atShape (fun t => Com d [T.ty t, T.ty t] (T.ty t)) h)
  else none

/-- **The gate.** The block of a tile operation on its mapped argument context: the block
    of the target at the shape, and `none` at every other shape. -/
def gate : (op : TileOp) →
    Option (Com d ((DialectSignature.sig (d := tileDialect) op).map T.ty)
      (T.ty (DialectSignature.ret (d := tileDialect) op)))
  | .tileBin bop n w => T.binaryGate n w (.bin bop)
  | .tilePermute n w => T.binaryGate n w .permute
  | .tileBroadcast n w l => T.unaryGate n w (.broadcast l)
  | .tileReduce n w => T.unaryGate n w .reduce
  | .tileConst n w c => T.constGate n w c
  | .tileShiftImm op n w k => T.unaryGate n w (.shiftImm op k)
  | .tileMulhu n w => T.binaryGate n w .mulhu
  | .tileShuffle n w idx => T.binaryGate n w (.shuffle idx)
  | .tileBlend n w mask => T.binaryGate n w (.blend mask)

/-- The value transport of tiles. -/
def tr : {t : TileTy} → ⟦t⟧ → ⟦T.ty t⟧ := fun {t} x => T.pack t x

/-- The valuation transport of tiles. -/
def mv {Γ : Ctxt tileDialect} (V : Valuation Γ) : Valuation (d := d) (Γ.map T.ty) :=
  transArgs T.ty T.tr V

theorem constGate_sound (n w c : Nat) (blk : Com d [] (T.ty (.tile n w)))
    (h : T.constGate n w c = some blk) :
    blk.denote .nil = T.pack (.tile n w) (tileConstApply n w c) := by
  unfold constGate at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [atShape_self]
    refine T.lane_inj _ _ (fun k => ?_)
    rw [T.lane_pack, T.const_lane c b0 h0 k]
    rfl
  · cases h

theorem unaryGate_sound (n w : Nat) (o : UnOp)
    (blk : Com d [T.ty (.tile n w)] (T.ty (.tile n w))) (h : T.unaryGate n w o = some blk)
    (a : Fin n → BitVec w) :
    blk.denote (.cons (T.pack (.tile n w) a) .nil) = T.pack (.tile n w) (o.apply a) := by
  unfold unaryGate at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [atShape_self]
    refine T.lane_inj _ _ (fun k => ?_)
    rw [T.lane_pack, T.unary_lane o b0 h0 a k]
  · cases h

theorem binaryGate_sound (n w : Nat) (o : BinOp)
    (blk : Com d [T.ty (.tile n w), T.ty (.tile n w)] (T.ty (.tile n w)))
    (h : T.binaryGate n w o = some blk) (a b : Fin n → BitVec w) :
    blk.denote (.cons (T.pack (.tile n w) a) (.cons (T.pack (.tile n w) b) .nil)) =
      T.pack (.tile n w) (o.apply a b) := by
  unfold binaryGate at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [atShape_self]
    refine T.lane_inj _ _ (fun k => ?_)
    rw [T.lane_pack, T.binary_lane o b0 h0 a b k]
  · cases h

/-- **The gate is sound.** A block of the gate denotes, on the packed argument values, the
    packing of the value of the tile operation. -/
theorem gate_sound (op : TileOp)
    (blk : Com d ((DialectSignature.sig (d := tileDialect) op).map T.ty)
      (T.ty (DialectSignature.ret (d := tileDialect) op)))
    (h : T.gate op = some blk)
    (args : HVector (fun t : TileTy => ⟦t⟧) (DialectSignature.sig (d := tileDialect) op)) :
    blk.denote (T.mv args) = T.tr (DialectDenote.denote (d := tileDialect) op args) := by
  cases op with
  | tileConst n w c => cases args; exact T.constGate_sound n w c blk h
  | tileBroadcast n w l =>
      cases args with | cons a rest => ?_
      cases rest
      exact T.unaryGate_sound n w _ blk h a
  | tileReduce n w =>
      cases args with | cons a rest => ?_
      cases rest
      exact T.unaryGate_sound n w _ blk h a
  | tileShiftImm o n w k =>
      cases args with | cons a rest => ?_
      cases rest
      exact T.unaryGate_sound n w _ blk h a
  | tileBin bop n w =>
      cases args with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      exact T.binaryGate_sound n w _ blk h a b
  | tilePermute n w =>
      cases args with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      exact T.binaryGate_sound n w _ blk h a b
  | tileMulhu n w =>
      cases args with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      exact T.binaryGate_sound n w _ blk h a b
  | tileShuffle n w idx =>
      cases args with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      exact T.binaryGate_sound n w _ blk h a b
  | tileBlend n w mask =>
      cases args with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      exact T.binaryGate_sound n w _ blk h a b

/-! ## 3. The leakage of the gate -/

/-- The leakage models of `d` in which every block of the target emits no event. -/
structure Quiet (M : LeakModel d) : Prop where
  /-- A constant block emits no event. -/
  const : ∀ c blk, T.const? c = some blk → ∀ W, Com.ctLeak M blk W = []
  /-- A one-operand block emits no event. -/
  unary : ∀ o blk, T.unary? o = some blk → ∀ W, Com.ctLeak M blk W = []
  /-- A two-operand block emits no event. -/
  binary : ∀ o blk, T.binary? o = some blk → ∀ W, Com.ctLeak M blk W = []

variable {T} in
theorem Quiet.gate {M : LeakModel d} (hQ : T.Quiet M) (op : TileOp)
    (blk : Com d ((DialectSignature.sig (d := tileDialect) op).map T.ty)
      (T.ty (DialectSignature.ret (d := tileDialect) op)))
    (h : T.gate op = some blk) (W : Valuation (d := d) _) : Com.ctLeak M blk W = [] := by
  cases op <;> simp only [TileTarget.gate, constGate, unaryGate, binaryGate] at h <;> split at h <;>
    first
    | cases h
    | (rename_i hs
       obtain ⟨rfl, rfl⟩ := hs
       obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
       rw [atShape_self]
       first
       | exact hQ.const _ b0 h0 W
       | exact hQ.unary _ b0 h0 W
       | exact hQ.binary _ b0 h0 W)

/-! ## 4. The partial block lowering of `tileDialect` -/

/-- The variable map along `T.ty`. -/
def mapVar : {Γ : Ctxt tileDialect} → {t : TileTy} → Var Γ t →
    Var (d := d) (Γ.map T.ty) (T.ty t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVar v)

/-- The renaming of the mapped argument context of an operation to its mapped argument
    variables. -/
def argHom {Γ : Ctxt tileDialect} : (ts : List TileTy) → HVector (fun t => Var Γ t) ts →
    Ctxt.Hom (d := d) (ts.map T.ty) (Γ.map T.ty)
  | [], _ => fun v => nomatch v
  | _ :: ts, .cons a as => fun v => consHom (argHom ts as) (T.mapVar a) v

/-- The partial block lowering of `tileDialect` to `d`: the block of the gate at the
    operation of an expression, under the renaming to its argument variables. -/
def lowering : PartialBlockLowering tileDialect d where
  mapTy := T.ty
  mapCtx := List.map T.ty
  mapCtx_cons := fun _ _ => rfl
  mapVar := T.mapVar
  lowerExprBlock? := fun e =>
    (T.gate e.op).map fun blk => congrArg T.ty e.retTy_eq ▸ Com.rename (T.argHom _ e.args) blk

theorem lookup_mapVar : ∀ {Γ : Ctxt tileDialect} {t : TileTy} (v : Var Γ t) (V : Valuation Γ),
    (T.mapVar v).lookup (T.mv V) = T.tr (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVar v xs

theorem pullV_argHom {Γ : Ctxt tileDialect} (V : Valuation Γ) :
    (ts : List TileTy) → (args : HVector (fun t => Var Γ t) ts) →
    pullV (T.argHom ts args) (T.mv V) = T.mv (Expr.lookupArgs args V)
  | [], .nil => rfl
  | _ :: ts, .cons a as => by
      show HVector.cons ((T.mapVar a).lookup (T.mv V))
        (pullV (T.argHom ts as) (T.mv V)) = HVector.cons _ _
      rw [T.lookup_mapVar a V, pullV_argHom V ts as]
      rfl

/-- The binding leaf of `T.lowering`. -/
theorem lowering_mapValExtends :
    T.lowering.MapValExtends (fun {t} => T.tr (t := t)) (fun {Γ} => T.mv (Γ := Γ)) :=
  fun _ _ => rfl

/-- **The block leaf of `T.lowering`.** -/
theorem lowering_block {Γ : Ctxt tileDialect} {t : TileTy} (ex : Expr tileDialect Γ t)
    (blk : Com d (T.lowering.mapCtx Γ) (T.lowering.mapTy t))
    (hb : T.lowering.lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    blk.denote (T.mv V) = T.tr (ex.denote V) := by
  obtain ⟨op, rfl, args⟩ := ex
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
  show (Com.rename (T.argHom _ args) b0).denote (T.mv V) = _
  rw [Com.denote_rename, T.pullV_argHom]
  exact T.gate_sound op b0 h0 _

variable {T} in
/-- **The block leak leaf of `T.lowering`** in a quiet model: a block emits no event, as
    its tile operation in `tileLeakModel`. -/
theorem lowering_blockLeak {M : LeakModel d} (hQ : T.Quiet M) {Γ : Ctxt tileDialect}
    {t : TileTy} (ex : Expr tileDialect Γ t)
    (blk : Com d (T.lowering.mapCtx Γ) (T.lowering.mapTy t))
    (hb : T.lowering.lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    Com.ctLeak M blk (T.mv V) = Expr.ctLeak tileLeakModel ex V := by
  obtain ⟨op, rfl, args⟩ := ex
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
  show Com.ctLeak M (Com.rename (T.argHom _ args) b0) (T.mv V) = []
  rw [NFProg.Com.ctLeak_rename_pullV]
  exact hQ.gate op b0 h0 _

end TileTarget

/-! ## 5. The lowering of the coproduct -/

section Legal

/-- The pure denotation of `scalarTile d` over a pure denotation of `d`: the denotation of
    the coproduct. -/
@[instance_reducible] def scalarTilePure (d : Dialect.{0, 0}) [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d] : DialectDenote (scalarTile d) :=
  instDialectDenoteSum (d := d) (e := tileDialect)

attribute [local instance] scalarTilePure

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  (T : TileTarget d)

/-- **Tile legalisation at the shape `T`**: the partial block lowering of `scalarTile d`
    to `d` that keeps the scalar operations and lowers a tile operation by the gate. -/
def tileLegal : PartialBlockLowering (scalarTile d) d := T.lowering.sumElimId

/-- The type map of `tileLegal T`. -/
abbrev legalTy : (scalarTile d).Ty → d.Ty := (tileLegal T).mapTy

/-- The value transport of `tileLegal T`: the identity on scalars, `pack` on tiles. -/
def packTy : (tileLegal T).TransTy :=
  fun {t} => T.lowering.sumTransTy (fun {t} => T.tr (t := t)) (t := t)

/-- The valuation transport of `tileLegal T`. -/
def packVal : (tileLegal T).MapVal :=
  fun {Γ} => T.lowering.sumMapVal (fun {t} => T.tr (t := t)) (Γ := Γ)

/-- The transport of a result tuple. -/
abbrev packOuts {ts : List (scalarTile d).Ty} (o : Valuation ts) :
    Valuation (d := d) (ts.map (legalTy T)) :=
  transArgs (legalTy T) (packTy T) o

/-- The variable leaf of `tileLegal T`. -/
theorem tileLegal_varTransports : (tileLegal T).VarTransports (packTy T) (packVal T) :=
  PartialBlockLowering.sumElimId_varTransports T.lowering _

/-- The binding leaf of `tileLegal T`. -/
theorem tileLegal_mapValExtends : (tileLegal T).MapValExtends (packTy T) (packVal T) :=
  PartialBlockLowering.sumElimId_mapValExtends T.lowering _

/-- **The block leaf of `tileLegal T`.** -/
theorem tileLegal_block {Γ : Ctxt (scalarTile d)} {t : (scalarTile d).Ty}
    (ex : Expr (scalarTile d) Γ t) (blk : Com d ((tileLegal T).mapCtx Γ) ((tileLegal T).mapTy t))
    (hb : (tileLegal T).lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    blk.denote (packVal T V) = packTy T (ex.denote V) :=
  PartialBlockLowering.sumElimId_block T.lowering _ _ T.lowering_mapValExtends
    (fun ex blk hb V => T.lowering_block ex blk hb V) ex blk hb V

variable {T} in
/-- **The block leak leaf of `tileLegal T`** in a quiet model. -/
theorem tileLegal_blockLeak {M : LeakModel d} (hQ : T.Quiet M) {Γ : Ctxt (scalarTile d)}
    {t : (scalarTile d).Ty} (ex : Expr (scalarTile d) Γ t)
    (blk : Com d ((tileLegal T).mapCtx Γ) ((tileLegal T).mapTy t))
    (hb : (tileLegal T).lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    Com.ctLeak M blk (packVal T V) = Expr.ctLeak (scalarTileLeak d M) ex V :=
  PartialBlockLowering.sumElimId_blockLeak M tileLeakModel T.lowering _ _
    T.lowering_mapValExtends (fun ex blk hb V => TileTarget.lowering_blockLeak hQ ex blk hb V)
    ex blk hb V

variable [HasWord64 d] [HasBoolBit d]

/-- The type map of `tileLegal T` keeps the trip-counter type and the bit type. -/
theorem tileLegal_regionTypes : (tileLegal T).RegionTypes := ⟨rfl, rfl⟩

/-- The value transport of `tileLegal T` keeps trip counts, trip indices and bits. -/
theorem tileLegal_regionTransports :
    (tileLegal T).RegionTransports (tileLegal_regionTypes T) (packTy T) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **Legalisation of a program.** The lowering of a program without `call` along
    `tileLegal T`; `none` when the program has a `call` or a tile operation the gate
    refuses. -/
def legalise {Γ : Ctxt (scalarTile d)} {ts : List (scalarTile d).Ty}
    (p : NFProg (scalarTile d) Γ ts) :
    Option (NFProg d (Γ.map (legalTy T)) (ts.map (legalTy T))) :=
  if p.callFree = true then NFProg.map? (tileLegal T) (tileLegal_regionTypes T) p (fun v => v)
  else none

omit [HasWord64 d] [HasBoolBit d] in
/-- The denotation of `scalarTile d` over the pure denotation of `d` is the pure
    denotation of the coproduct. -/
theorem scalarTileDenote_pure :
    scalarTileDenote d (instDialectDenoteMOptionOfPure d) =
      instDialectDenoteMOptionOfPure (scalarTile d) := by
  show DialectDenoteM.mk _ = DialectDenoteM.mk _
  congr 1
  funext op args
  cases op <;> rfl

/-- **Legalisation preserves denotations.** A legalised program denotes, on the transported
    valuation, the transport of the results of its source, at every fuel. -/
theorem tileLegal_denote [CallDenote d] (fuel : Nat) {Γ : Ctxt (scalarTile d)}
    {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts)
    (q : NFProg d (Γ.map (legalTy T)) (ts.map (legalTy T))) (h : legalise T p = some q)
    (V : Valuation Γ) :
    q.denote fuel (packVal T V) =
      (scalarTileDenP d (instDialectDenoteMOptionOfPure d) fuel p V).map (packOuts T) := by
  unfold legalise at h
  split at h
  · rename_i hc
    unfold scalarTileDenP
    rw [scalarTileDenote_pure]
    exact NFProg.map?_denote (tileLegal T) (packTy T) (packVal T) (tileLegal_regionTypes T)
      (fun _ => True) (tileLegal_varTransports T)
      (fun ex _ blk hb V => tileLegal_block T ex blk hb V) (tileLegal_mapValExtends T)
      (tileLegal_regionTransports T) fuel p hc
      (NFProg.covered_of_forall _ (fun _ => trivial) p) _ V _ (pullV_id _) q h
  · cases h

variable {T} in
/-- **Legalisation preserves runs and events.** In a model of `d` in which the blocks of
    the target are quiet, a legalised program runs, on the transported valuation, to the
    transport of the results and to the events of the run of its source. -/
theorem tileLegal_leakRun {M : LeakModel d} (hQ : T.Quiet M) (fuel : Nat)
    {Γ : Ctxt (scalarTile d)} {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts)
    (q : NFProg d (Γ.map (legalTy T)) (ts.map (legalTy T))) (h : legalise T p = some q)
    (V : Valuation Γ) :
    NFProg.leakRun M fuel q (packVal T V) =
      (scalarTileLeakRun d (instDialectDenoteMOptionOfPure d) M fuel p V).map
        fun r => (packOuts T r.1, r.2) := by
  unfold legalise at h
  split at h
  · unfold scalarTileLeakRun
    rw [scalarTileDenote_pure, NFProg.leakRunM_eq_leakRun]
    exact NFProg.map?_leakRun (tileLegal T) (packTy T) (packVal T) (scalarTileLeak d M) M
      (tileLegal_regionTypes T) (fun _ => True) (tileLegal_varTransports T)
      (fun ex _ blk hb V => tileLegal_block T ex blk hb V)
      (fun ex _ blk hb V => tileLegal_blockLeak hQ ex blk hb V) (tileLegal_mapValExtends T)
      (tileLegal_regionTransports T) fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) _ V _ (pullV_id _) q h
  · cases h

/-- The semantics of programs of `scalarTile d` over the pure denotation of `d`, at the
    fuel `fuel`. -/
def scalarTileSem (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    [HasWord64 d] [HasBoolBit d] (fuel : Nat) (Γ : Ctxt (scalarTile d))
    (ts : List (scalarTile d).Ty) : PassChain.Sem (NFProg (scalarTile d) Γ ts) where
  In := Valuation Γ
  Out := Valuation ts
  den := fun p V => scalarTileDenP d (instDialectDenoteMOptionOfPure d) fuel p V

/-- The semantics of programs of `d` at the fuel `fuel`. -/
def targetSem (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    [HasWord64 d] [HasBoolBit d] [CallDenote d] (fuel : Nat) (Δ : Ctxt d) (ts : List d.Ty) :
    PassChain.Sem (NFProg d Δ ts) where
  In := Valuation Δ
  Out := Valuation ts
  den := fun q W => q.denote fuel W

open PassChain in
/-- **The certificate of legalisation.** The step `legalise T` from the semantics of
    programs of `scalarTile d` to that of programs of `d`: the input relation is the graph
    of `packVal T` and the output relation the graph of `packOuts T`. -/
def tileLegalCert [CallDenote d] (fuel : Nat) (Γ : Ctxt (scalarTile d))
    (ts : List (scalarTile d).Ty) :
    StepCert (legalise T (Γ := Γ) (ts := ts)) (scalarTileSem d fuel Γ ts)
      (targetSem d fuel (Γ.map (legalTy T)) (ts.map (legalTy T))) :=
  StepCert.ofTransport _ _ (fun V => packVal T V) (fun o => packOuts T o)
    fun p q V hf => tileLegal_denote T fuel p q hf V

end Legal

end CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
