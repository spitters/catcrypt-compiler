/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecMem
public import CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneStripAccept

/-!
# Legalisation of the tile memory and broadcast operations

A structured program over `jasminTileMem`, the operation sum of `scalarTile jasminDialect` and
the bridge operations `tileLoad`, `tileStore`, `tileSplat` (`VIR/TileBridge.lean`), is
legalised to a program over `jasminVecMem` (`VIR/X86VecMem.lean`) at a lane shape
`T : TileTarget jasminVecMem`.

`memShape T` reads a lane shape of `jasminVec` as a lane shape of `jasminVecMem`: the same
types, value transport and lane read, and every block included by `memCom`. The record
`MemTarget T` extends a shape with a gate for the three bridge operations: a block of
`jasminVecMem` for a load and a store at every array length and for a broadcast, or `none`,
with the lane law of every block it gives.

`bridgeLegal S` is a partial block lowering of `jasminTileMem` to `jasminVecMem` with the type
map, the context map and the value transports of `tileLegal T`. A scalar operation and a tile
operation get the block of `tileLegal T`; a bridge operation gets the block of the gate of `S`
at the shape of `T`, and `none` at every other shape. `legaliseBridge S` is the program map.

`qwordMem` and `dwordMem` are the gates at `memShape selQ` (eight 64-bit lanes) and
`memShape selD` (sixteen 32-bit lanes): `tileLoad` is one `vload`, `tileStore` one `vstore`,
`tileSplat` one `vsplat`.

For a loop `stripMine l w` accepts, the legalised strip-mined program runs to the results of
the loop, and its events are `stripEv` of the events of the loop. `scaledAddLoop N` passes
`stripMine 3 64` and `legaliseBridge qwordMem` for every `N ≥ 8`.

## Main definitions

* `tileVecMem`: the coproduct of `jasminVecMem` and `tileDialect`.
* `memShape`: a lane shape of `jasminVec` as a lane shape of `jasminVecMem`.
* `MemTarget`, `MemTarget.gate`, `MemTarget.Addr`: the gate of the bridge operations at a lane
  shape, the gate on `BridgeOp`, and the leakage models in which a load block and a store
  block emit the reading of the index and a broadcast block no event.
* `tileMemPure`: the pure denotation of `jasminTileMem`, a local instance of this file.
* `bridgeLegal`, `legaliseBridge`: the partial block lowering and the program map.
* `bridgeLegalCert`, `bridgeLegalLeakCert`: the step certificates of `legaliseBridge` for
  denotations and for events.
* `loadBlk`, `vstoreBlk`, `splatBlk`: the one-operation blocks of `vload`, `vstore`, `vsplat`.
* `qwordMem`, `dwordMem`: the gates at the two lane shapes of a ZMM register.
* `scalarRd`: the scalar reading of a legalised tuple of scalar types.
* `scaledAddVec`: the legalised strip-mined program of `scaledAddLoop`.

## Main results

* `memShape_quiet`: the blocks of `memShape T` emit no event when those of `T` emit none.
* `MemTarget.gate_sound`: a block of the gate computes the transport of the value of the
  bridge operation.
* `MemTarget.Addr.gate`: a block of the gate emits the events of the bridge operation.
* `bridgeLegal_denote`: a legalised program denotes, on the transported valuation, the
  transport of the results of its source, at every fuel.
* `bridgeLegal_leakRun`, `bridgeLegal_events`: a legalised program runs to the transported
  results and to the events of the source run.
* `qwordMem_addr`, `dwordMem_addr`: the leakage of the blocks of the two gates.
* `bridge_gate_table`: the blocks of the two gates.
* `strip_legal_denote`, `strip_legal_events`: the legalised strip-mined program of a loop
  runs to the results of the loop, with the events `stripEv` of the events of the loop.
* `scaledAddStrip_legal`: `legaliseBridge qwordMem` accepts the strip-mined `scaledAddLoop N`
  for `8 ≤ N`.
* `scaledAddVec_denote`, `scaledAddVec_events`: the result and the events of `scaledAddVec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileBridgeLegal

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
open CatCrypt.Crypto.SecureCompilation.VIR.TileBridge
open CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegalX86 (packAt)
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecMem
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (lane bcast)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (consHom lookup_pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF (LaneQuiet)
open CatCrypt.Crypto.SecureCompilation.VIR.LaneStripKernel (ArrAddr)
open CatCrypt.Crypto.SecureCompilation.VIR.LaneStrip
open CatCrypt.Crypto.SecureCompilation.VIR.LaneStripAccept
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

/-! ## 1. Lane shapes of `jasminVec` in `jasminVecMem` -/

/-- The coproduct of `jasminVecMem` and `tileDialect`: the source dialect of `tileLegal` at a
    lane shape of `jasminVecMem`. -/
abbrev tileVecMem : Dialect := scalarTile jasminVecMem

instance : DialectSignature tileVecMem := instDialectSignatureScalarTile jasminVecMem
instance : HasWord64 tileVecMem := instHasWord64ScalarTile jasminVecMem
instance : HasBoolBit tileVecMem := instHasBoolBitScalarTile jasminVecMem
instance : CallDenote tileVecMem := instCallDenoteScalarTile jasminVecMem

/-- **A lane shape of `jasminVec` as a lane shape of `jasminVecMem`**: the types, the value
    transport and the lane read of `T`, and every block of `T` included by `memCom`. -/
def memShape (T : TileTarget jasminVec) : TileTarget jasminVecMem where
  laneCount := T.laneCount
  laneBits := T.laneBits
  ty := T.ty
  pack := T.pack
  lane := T.lane
  lane_pack := T.lane_pack
  lane_inj := T.lane_inj
  const? := fun c => (T.const? c).map memCom
  unary? := fun o => (T.unary? o).map memCom
  binary? := fun o => (T.binary? o).map memCom
  const_lane := by
    intro c blk h k
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (congrArg (fun x => T.lane x k) (memCom_denote b0 _)).trans (T.const_lane c b0 h0 k)
  unary_lane := by
    intro o blk h a k
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (congrArg (fun x => T.lane x k) (memCom_denote b0 _)).trans
      (T.unary_lane o b0 h0 a k)
  binary_lane := by
    intro o blk h a b k
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (congrArg (fun x => T.lane x k) (memCom_denote b0 _)).trans
      (T.binary_lane o b0 h0 a b k)

/-- **The blocks of `memShape T` emit no event** in `jasminVecMemLeak M` when the blocks of
    `T` emit none in `jasminVecLeak M`. -/
theorem memShape_quiet {T : TileTarget jasminVec} {M : LeakModel jasminDialect}
    (hQ : T.Quiet (jasminVecLeak M)) : (memShape T).Quiet (jasminVecMemLeak M) where
  const := by
    intro c blk h W
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (memCom_ctLeak M b0 W).trans (hQ.const c b0 h0 W)
  unary := by
    intro o blk h W
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (memCom_ctLeak M b0 W).trans (hQ.unary o b0 h0 W)
  binary := by
    intro o blk h W
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (memCom_ctLeak M b0 W).trans (hQ.binary o b0 h0 W)

/-! ## 2. The gate of the bridge operations at a lane shape -/

/-- The lane width of a tile type. -/
def tileBits : TileTy → Nat
  | .tile _ w => w

section Gate

/-- **The gate of the bridge operations at the lane shape `T`.** A block of `jasminVecMem`
    for a load and for a store at every array length, and for a broadcast, or `none`, with
    the lane law of every block it gives. -/
structure MemTarget (T : TileTarget jasminVecMem) where
  /-- The block of a load from an array of `N` elements. -/
  load? : (N : Nat) →
    Option (Com jasminVecMem [JasminTy.stackArr T.laneBits N, JasminTy.reg 64] T.regTy)
  /-- The block of a store to an array of `N` elements. -/
  store? : (N : Nat) →
    Option (Com jasminVecMem [JasminTy.stackArr T.laneBits N, JasminTy.reg 64, T.regTy]
      (JasminTy.stackArr T.laneBits N))
  /-- The block of a broadcast. -/
  splat? : Option (Com jasminVecMem [JasminTy.reg T.laneBits] T.regTy)
  /-- Lane `k` of a load block is the element at the index plus `k`. -/
  load_lane : ∀ N blk, load? N = some blk →
    ∀ (a : Fin N → BitVec T.laneBits) (i : BitVec 64) (k : Fin T.laneCount),
      T.lane (blk.denote (.cons a (.cons i .nil))) k = stackGet a (i.toNat + k.val)
  /-- A store block on a packed tile returns the array the lane store writes. -/
  store_val : ∀ N blk, store? N = some blk →
    ∀ (a : Fin N → BitVec T.laneBits) (i : BitVec 64)
      (t : Fin T.laneCount → BitVec T.laneBits),
      blk.denote (.cons a (.cons i (.cons (T.pack T.shapeTy t) .nil))) =
        jasminLaneStore a i.toNat t
  /-- Every lane of a broadcast block is the register. -/
  splat_lane : ∀ blk, splat? = some blk →
    ∀ (x : BitVec T.laneBits) (k : Fin T.laneCount),
      T.lane (blk.denote (.cons x .nil)) k = x

variable {T : TileTarget jasminVecMem}

/-- **The gate on `BridgeOp`.** The block of a bridge operation on its mapped argument
    context: the block of `S` at the shape of `T`, and `none` at every other shape. -/
def MemTarget.gate (S : MemTarget T) : (o : BridgeOp) →
    Option (Com jasminVecMem ((DialectSignature.sig (d := jasminBridge) o).map (legalTy T))
      (legalTy T (DialectSignature.ret (d := jasminBridge) o)))
  | .tileLoad L w N =>
      if h : L = T.laneCount ∧ w = T.laneBits then
        (S.load? N).map (T.atShape
          (fun t => Com jasminVecMem [JasminTy.stackArr (tileBits t) N, JasminTy.reg 64]
            (T.ty t)) h)
      else none
  | .tileStore L w N =>
      if h : L = T.laneCount ∧ w = T.laneBits then
        (S.store? N).map (T.atShape
          (fun t => Com jasminVecMem [JasminTy.stackArr (tileBits t) N, JasminTy.reg 64, T.ty t]
            (JasminTy.stackArr (tileBits t) N)) h)
      else none
  | .tileSplat L w =>
      if h : L = T.laneCount ∧ w = T.laneBits then
        (S.splat?).map (T.atShape
          (fun t => Com jasminVecMem [JasminTy.reg (tileBits t)] (T.ty t)) h)
      else none

/-- **The gate is sound.** A block of the gate denotes, on the packed argument values, the
    packing of the value of the bridge operation. -/
theorem MemTarget.gate_sound (S : MemTarget T) (o : BridgeOp)
    (blk : Com jasminVecMem ((DialectSignature.sig (d := jasminBridge) o).map (legalTy T))
      (legalTy T (DialectSignature.ret (d := jasminBridge) o)))
    (h : S.gate o = some blk)
    (args : HVector (fun t : JasminTy ⊕ TileTy => ⟦t⟧)
      (DialectSignature.sig (d := jasminBridge) o)) :
    blk.denote (transArgs (legalTy T) (packTy T) args) =
      packTy T (DialectDenote.denote (d := jasminBridge) o args) := by
  cases o with
  | tileLoad L w N =>
      cases args with | cons a rest => ?_
      cases rest with | cons i rest => ?_
      cases rest
      simp only [MemTarget.gate] at h
      split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [TileTarget.atShape_self]
        refine T.lane_inj _
          (T.pack T.shapeTy (jasminLaneLoad T.laneCount a (BitVec.toNat (w := 64) i)))
          (fun k => ?_)
        exact (S.load_lane N b0 h0 a i k).trans
          (T.lane_pack (jasminLaneLoad T.laneCount a (BitVec.toNat (w := 64) i)) k).symm
      · cases h
  | tileStore L w N =>
      cases args with | cons a rest => ?_
      cases rest with | cons i rest => ?_
      cases rest with | cons t rest => ?_
      cases rest
      simp only [MemTarget.gate] at h
      split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [TileTarget.atShape_self]
        exact S.store_val N b0 h0 a i t
      · cases h
  | tileSplat L w =>
      cases args with | cons x rest => ?_
      cases rest
      simp only [MemTarget.gate] at h
      split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [TileTarget.atShape_self]
        refine T.lane_inj _
          (T.pack T.shapeTy (fun _ : Fin T.laneCount => (x : BitVec T.laneBits)))
          (fun k => ?_)
        exact (S.splat_lane b0 h0 x k).trans
          (T.lane_pack (fun _ : Fin T.laneCount => (x : BitVec T.laneBits)) k).symm
      · cases h

/-- The leakage models of `jasminDialect` over which a load block and a store block of `S`
    emit one address event, the reading of the index, and a broadcast block emits none. -/
structure MemTarget.Addr (S : MemTarget T) (M : LeakModel jasminDialect) : Prop where
  /-- A load block emits the reading of its index. -/
  load : ∀ N blk, S.load? N = some blk →
    ∀ (a : Fin N → BitVec T.laneBits) (i : BitVec 64),
      Com.ctLeak (jasminVecMemLeak M) blk (.cons a (.cons i .nil)) =
        [CTLeak.addr "" ((M.valNat (.reg 64) i : Nat) : Int)]
  /-- A store block emits the reading of its index. -/
  store : ∀ N blk, S.store? N = some blk →
    ∀ (a : Fin N → BitVec T.laneBits) (i : BitVec 64) (v : ⟦T.regTy⟧),
      Com.ctLeak (jasminVecMemLeak M) blk (.cons a (.cons i (.cons v .nil))) =
        [CTLeak.addr "" ((M.valNat (.reg 64) i : Nat) : Int)]
  /-- A broadcast block emits no event. -/
  splat : ∀ blk, S.splat? = some blk → ∀ W, Com.ctLeak (jasminVecMemLeak M) blk W = []

/-- **A block of the gate emits the events of the bridge operation**: one address event per
    load and per store, none for a broadcast. -/
theorem MemTarget.Addr.gate {S : MemTarget T} {M : LeakModel jasminDialect} (hA : S.Addr M)
    (o : BridgeOp)
    (blk : Com jasminVecMem ((DialectSignature.sig (d := jasminBridge) o).map (legalTy T))
      (legalTy T (DialectSignature.ret (d := jasminBridge) o)))
    (h : S.gate o = some blk)
    (args : HVector (fun t : JasminTy ⊕ TileTy => ⟦t⟧)
      (DialectSignature.sig (d := jasminBridge) o)) :
    Com.ctLeak (jasminVecMemLeak M) blk (transArgs (legalTy T) (packTy T) args) =
      opLeak (tileMemLeak jasminDialect M) (.inr o) args := by
  cases o with
  | tileLoad L w N =>
      cases args with | cons a rest => ?_
      cases rest with | cons i rest => ?_
      cases rest
      simp only [MemTarget.gate] at h
      split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [TileTarget.atShape_self]
        exact (hA.load N b0 h0 a i).trans rfl
      · cases h
  | tileStore L w N =>
      cases args with | cons a rest => ?_
      cases rest with | cons i rest => ?_
      cases rest with | cons t rest => ?_
      cases rest
      simp only [MemTarget.gate] at h
      split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [TileTarget.atShape_self]
        exact (hA.store N b0 h0 a i _).trans rfl
      · cases h
  | tileSplat L w =>
      simp only [MemTarget.gate] at h
      split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [TileTarget.atShape_self]
        exact (hA.splat b0 h0 _).trans
          (tileMem_opLeak_tileSplat jasminDialect M _ _ args).symm
      · cases h

end Gate

/-! ## 3. The lowering of the operation sum -/

section Lowering

/-- The pure denotation of `jasminTileMem`: an operation of `scalarTile jasminDialect` by the
    denotation of the coproduct, a bridge operation by its denotation. -/
@[instance_reducible] def tileMemPure : DialectDenote jasminTileMem where
  denote
    | .inl o => fun args => (scalarTilePure jasminDialect).denote o args
    | .inr o => fun args => DialectDenote.denote (d := jasminBridge) o args

attribute [local instance] scalarTilePure tileMemPure

/-- The denotation of `jasminTileMem` over the pure denotation of `jasminDialect` is the pure
    denotation of the operation sum. -/
theorem tileMemDenote_pure :
    tileMemDenote jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) =
      instDialectDenoteMOptionOfPure jasminTileMem := by
  show DialectDenoteM.mk _ = DialectDenoteM.mk _
  congr 1
  funext op args
  rcases op with o | o
  · cases o <;> rfl
  · rfl

/-- `unmapInl` depends on the type alphabet of the scalar dialect only. -/
theorem unmapInl_alphabet {O O' A : Type} [TyDenote A] : ∀ {ts : List A}
    (x : HVector (fun t => ⟦t⟧) (ts.map (Sum.inl (β := TileTy)))),
    unmapInl (d := ⟨O, A⟩) (e := tileDialect) x =
      unmapInl (d := ⟨O', A⟩) (e := tileDialect) x
  | [], _ => rfl
  | t :: _, .cons x xs => by
      show HVector.cons (f := fun t : A => ⟦t⟧) (t := t) x
          (unmapInl (d := ⟨O, A⟩) (e := tileDialect) xs) =
        HVector.cons (f := fun t : A => ⟦t⟧) (t := t) x
          (unmapInl (d := ⟨O', A⟩) (e := tileDialect) xs)
      rw [unmapInl_alphabet (O := O) (O' := O') xs]

/-- `unmapInr` depends on the type alphabet of the scalar dialect only. -/
theorem unmapInr_alphabet {O O' A : Type} [TyDenote A] : ∀ {ts : List TileTy}
    (x : HVector (fun t => ⟦t⟧) (ts.map (Sum.inr (α := A)))),
    unmapInr (d := ⟨O, A⟩) (e := tileDialect) x =
      unmapInr (d := ⟨O', A⟩) (e := tileDialect) x
  | [], _ => rfl
  | t :: _, .cons x xs => by
      show HVector.cons (f := fun t : TileTy => ⟦t⟧) (t := t) x
          (unmapInr (d := ⟨O, A⟩) (e := tileDialect) xs) =
        HVector.cons (f := fun t : TileTy => ⟦t⟧) (t := t) x
          (unmapInr (d := ⟨O', A⟩) (e := tileDialect) xs)
      rw [unmapInr_alphabet (O := O) (O' := O') xs]

variable {T : TileTarget jasminVecMem}

/-- The renaming of the mapped argument context of a bridge operation to its mapped argument
    variables. -/
def memArgHom (T : TileTarget jasminVecMem) {Γ : Ctxt jasminTileMem} :
    (ts : List (JasminTy ⊕ TileTy)) → HVector (fun t => Var Γ t) ts →
    Ctxt.Hom (d := jasminVecMem) (ts.map (legalTy T)) ((tileLegal T).mapCtx Γ)
  | [], _ => fun v => nomatch v
  | _ :: ts, .cons a as => fun v =>
      consHom (memArgHom T ts as) ((tileLegal T).mapVar (castVar a)) v

/-- **Legalisation of `jasminTileMem` at the shape `T` with the gate `S`**: the partial block
    lowering with the type, context and variable maps of `tileLegal T` that gives a scalar
    operation and a tile operation the block of `tileLegal T` and a bridge operation the block
    of the gate of `S`. -/
@[reducible] def bridgeLegal (S : MemTarget T) :
    PartialBlockLowering jasminTileMem jasminVecMem where
  mapTy := (tileLegal T).mapTy
  mapCtx := (tileLegal T).mapCtx
  mapCtx_cons := (tileLegal T).mapCtx_cons
  mapVar := fun v => (tileLegal T).mapVar (castVar v)
  lowerExprBlock? := fun e =>
    match e with
    | ⟨.inl (.inl o), h, args⟩ =>
        (tileLegal T).lowerExprBlock? ⟨.inl (.inl (.inl o)), h, castArgs args⟩
    | ⟨.inl (.inr o), h, args⟩ => (tileLegal T).lowerExprBlock? ⟨.inr o, h, castArgs args⟩
    | ⟨.inr o, h, args⟩ =>
        (S.gate o).map fun blk => h ▸ Com.rename (memArgHom T _ args) blk

/-- The variable leaf of `bridgeLegal S`. -/
theorem bridgeLegal_varTransports (S : MemTarget T) :
    (bridgeLegal S).VarTransports (packTy T) (packVal T) :=
  fun v V => (tileLegal_varTransports T (castVar v) V).trans
    (congrArg (packTy T) (lookup_castVar v V))

/-- The binding leaf of `bridgeLegal S`. -/
theorem bridgeLegal_mapValExtends (S : MemTarget T) :
    (bridgeLegal S).MapValExtends (packTy T) (packVal T) :=
  fun V x => tileLegal_mapValExtends T V x

/-- The transported valuation read along `memArgHom` is the transport of the argument
    values. -/
theorem pullV_memArgHom (T : TileTarget jasminVecMem) {Γ : Ctxt jasminTileMem}
    (V : Valuation Γ) :
    (ts : List (JasminTy ⊕ TileTy)) → (args : HVector (fun t => Var Γ t) ts) →
    pullV (memArgHom T ts args) (packVal T V) =
      transArgs (legalTy T) (packTy T) (Expr.lookupArgs (d := jasminTileMem) args V)
  | [], .nil => rfl
  | _ :: ts, .cons a as => by
      show HVector.cons (((tileLegal T).mapVar (castVar a)).lookup (packVal T V))
        (pullV (memArgHom T ts as) (packVal T V)) = HVector.cons _ _
      rw [tileLegal_varTransports T (castVar a) V, pullV_memArgHom T V ts as,
        lookup_castVar a V]

/-- **The block leaf of `bridgeLegal S`.** -/
theorem bridgeLegal_block (S : MemTarget T) {Γ : Ctxt jasminTileMem} {t : jasminTileMem.Ty}
    (ex : Expr jasminTileMem Γ t)
    (blk : Com jasminVecMem ((bridgeLegal S).mapCtx Γ) ((bridgeLegal S).mapTy t))
    (hb : (bridgeLegal S).lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    blk.denote (packVal T V) = packTy T (ex.denote V) := by
  obtain ⟨op, rfl, args⟩ := ex
  rcases op with (o | o) | o
  · refine (tileLegal_block T ⟨.inl (.inl (.inl o)), rfl, castArgs args⟩ blk hb V).trans ?_
    show packTy T (t := Sum.inl (DialectSignature.ret (d := jasminDialect) o))
      (DialectDenote.denote (d := jasminDialect) o
      (unmapInl (d := jasminVecMem) (e := tileDialect)
        (Expr.lookupArgs (d := scalarTile jasminVecMem) (castArgs args) V))) = _
    rw [lookupArgs_castArgs args V,
      unmapInl_alphabet (O := jasminVecMem.Op) (O' := JasminOp)]
    rfl
  · refine (tileLegal_block T ⟨.inr o, rfl, castArgs args⟩ blk hb V).trans ?_
    show packTy T (t := Sum.inr (DialectSignature.ret (d := tileDialect) o))
      (DialectDenote.denote (d := tileDialect) o
      (unmapInr (d := jasminVecMem) (e := tileDialect)
        (Expr.lookupArgs (d := scalarTile jasminVecMem) (castArgs args) V))) = _
    rw [lookupArgs_castArgs args V,
      unmapInr_alphabet (O := jasminVecMem.Op) (O' := JasminOp)]
    rfl
  · obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    refine (Com.denote_rename (memArgHom T _ args) b0 (packVal T V)).trans ?_
    rw [pullV_memArgHom]
    exact S.gate_sound o b0 h0 _

/-- **The block leak leaf of `bridgeLegal S`**: over a model in which the blocks of `T` are
    quiet and the blocks of `S` emit the reading of the index, a block emits the events of
    its source operation. -/
theorem bridgeLegal_blockLeak {S : MemTarget T} {M : LeakModel jasminDialect}
    (hT : T.Quiet (jasminVecMemLeak M)) (hS : S.Addr M) {Γ : Ctxt jasminTileMem}
    {t : jasminTileMem.Ty} (ex : Expr jasminTileMem Γ t)
    (blk : Com jasminVecMem ((bridgeLegal S).mapCtx Γ) ((bridgeLegal S).mapTy t))
    (hb : (bridgeLegal S).lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    Com.ctLeak (jasminVecMemLeak M) blk (packVal T V) =
      Expr.ctLeak (tileMemLeak jasminDialect M) ex V := by
  obtain ⟨op, rfl, args⟩ := ex
  rcases op with (o | o) | o
  · refine (tileLegal_blockLeak hT ⟨.inl (.inl (.inl o)), rfl, castArgs args⟩ blk hb
      V).trans ?_
    show opLeak (scalarTileLeak jasminVecMem (jasminVecMemLeak M)) (.inl (.inl (.inl o)))
        (Expr.lookupArgs (d := scalarTile jasminVecMem) (castArgs args) V) =
      opLeak (tileMemLeak jasminDialect M) (.inl (.inl o))
        (Expr.lookupArgs (d := jasminTileMem) args V)
    rw [lookupArgs_castArgs args V, tileMem_opLeak_inl, scalarTile_opLeak_inl,
      scalarTile_opLeak_inl, unmapInl_alphabet (O := jasminVecMem.Op) (O' := JasminOp)]
    exact jasminVecMem_opLeak_scalar M o _
  · refine (tileLegal_blockLeak hT ⟨.inr o, rfl, castArgs args⟩ blk hb V).trans ?_
    show opLeak (scalarTileLeak jasminVecMem (jasminVecMemLeak M)) (.inr o)
        (Expr.lookupArgs (d := scalarTile jasminVecMem) (castArgs args) V) =
      opLeak (tileMemLeak jasminDialect M) (.inl (.inr o))
        (Expr.lookupArgs (d := jasminTileMem) args V)
    rw [lookupArgs_castArgs args V, tileMem_opLeak_inl, scalarTile_opLeak_inr,
      scalarTile_opLeak_inr]
  · obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    refine (NFProg.Com.ctLeak_rename_pullV (jasminVecMemLeak M) (memArgHom T _ args) b0
      (packVal T V)).trans ?_
    rw [pullV_memArgHom]
    exact hS.gate o b0 h0 _

/-- The type map of `bridgeLegal S` keeps the trip-counter type and the bit type. -/
theorem bridgeLegal_regionTypes (S : MemTarget T) : (bridgeLegal S).RegionTypes := ⟨rfl, rfl⟩

/-- The value transport of `bridgeLegal S` keeps trip counts, trip indices and bits. -/
theorem bridgeLegal_regionTransports (S : MemTarget T) :
    (bridgeLegal S).RegionTransports (bridgeLegal_regionTypes S) (packTy T) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **Legalisation of a program of `jasminTileMem`.** The lowering of a program without `call`
    along `bridgeLegal S`; `none` when the program has a `call` or an operation a gate
    refuses. -/
def legaliseBridge (S : MemTarget T) {Γ : Ctxt jasminTileMem} {ts : List jasminTileMem.Ty}
    (p : NFProg jasminTileMem Γ ts) :
    Option (NFProg jasminVecMem (Γ.map (legalTy T)) (ts.map (legalTy T))) :=
  if p.callFree = true then
    NFProg.map? (bridgeLegal S) (bridgeLegal_regionTypes S) p (fun v => v)
  else none

/-- **Legalisation preserves denotations.** A legalised program denotes, on the transported
    valuation, the transport of the results of its source, at every fuel. -/
theorem bridgeLegal_denote (S : MemTarget T) (fuel : Nat) {Γ : Ctxt jasminTileMem}
    {ts : List jasminTileMem.Ty} (p : NFProg jasminTileMem Γ ts)
    (q : NFProg jasminVecMem (Γ.map (legalTy T)) (ts.map (legalTy T)))
    (h : legaliseBridge S p = some q) (V : Valuation Γ) :
    q.denote fuel (packVal T V) =
      (tileMemDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) fuel p V).map
        (packOuts T) := by
  unfold legaliseBridge at h
  split at h
  · rename_i hc
    unfold tileMemDenP
    rw [tileMemDenote_pure]
    exact NFProg.map?_denote (bridgeLegal S) (packTy T) (packVal T) (bridgeLegal_regionTypes S)
      (fun _ => True) (bridgeLegal_varTransports S)
      (fun ex _ blk hb V => bridgeLegal_block S ex blk hb V) (bridgeLegal_mapValExtends S)
      (bridgeLegal_regionTransports S) fuel p hc
      (NFProg.covered_of_forall _ (fun _ => trivial) p) _ V _ (pullV_id _) q h
  · cases h

/-- **Legalisation preserves runs and events.** Over a model in which the blocks of `T` are
    quiet and the blocks of `S` emit the reading of the index, a legalised program runs, on
    the transported valuation, to the transport of the results and to the events of the run
    of its source: one address event per vector load and per vector store, as per `tileLoad`
    and per `tileStore`. -/
theorem bridgeLegal_leakRun {S : MemTarget T} {M : LeakModel jasminDialect}
    (hT : T.Quiet (jasminVecMemLeak M)) (hS : S.Addr M) (fuel : Nat)
    {Γ : Ctxt jasminTileMem} {ts : List jasminTileMem.Ty} (p : NFProg jasminTileMem Γ ts)
    (q : NFProg jasminVecMem (Γ.map (legalTy T)) (ts.map (legalTy T)))
    (h : legaliseBridge S p = some q) (V : Valuation Γ) :
    NFProg.leakRun (jasminVecMemLeak M) fuel q (packVal T V) =
      (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel p
        V).map fun r => (packOuts T r.1, r.2) := by
  unfold legaliseBridge at h
  split at h
  · unfold tileMemLeakRun
    rw [tileMemDenote_pure, NFProg.leakRunM_eq_leakRun]
    exact NFProg.map?_leakRun (bridgeLegal S) (packTy T) (packVal T)
      (tileMemLeak jasminDialect M) (jasminVecMemLeak M)
      (bridgeLegal_regionTypes S) (fun _ => True) (bridgeLegal_varTransports S)
      (fun ex _ blk hb V => bridgeLegal_block S ex blk hb V)
      (fun ex _ blk hb V => bridgeLegal_blockLeak hT hS ex blk hb V)
      (bridgeLegal_mapValExtends S) (bridgeLegal_regionTransports S) fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) _ V _ (pullV_id _) q h
  · cases h

/-- **The events of a legalised program** are the events of its source. -/
theorem bridgeLegal_events {S : MemTarget T} {M : LeakModel jasminDialect}
    (hT : T.Quiet (jasminVecMemLeak M)) (hS : S.Addr M) (fuel : Nat)
    {Γ : Ctxt jasminTileMem} {ts : List jasminTileMem.Ty} (p : NFProg jasminTileMem Γ ts)
    (q : NFProg jasminVecMem (Γ.map (legalTy T)) (ts.map (legalTy T)))
    (h : legaliseBridge S p = some q) (V : Valuation Γ) :
    (NFProg.leakRun (jasminVecMemLeak M) fuel q (packVal T V)).map Prod.snd =
      (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel p
        V).map Prod.snd := by
  rw [bridgeLegal_leakRun hT hS fuel p q h V, Option.map_map]
  rfl

/-- The leak semantics of programs of `jasminVecMem` at the model `jasminVecMemLeak M`. -/
def vecMemLeakSem (M : LeakModel jasminDialect) (fuel : Nat) (Δ : Ctxt jasminVecMem)
    (ts : List jasminVecMem.Ty) : PassChain.LeakSem (NFProg jasminVecMem Δ ts) where
  In := Valuation Δ
  Ev := CTLeak
  leak q W := (NFProg.leakRun (jasminVecMemLeak M) fuel q W).map Prod.snd

open PassChain in
/-- **The certificate of legalisation.** The step `legaliseBridge S` from the semantics of
    programs of `jasminTileMem` to that of programs of `jasminVecMem`: the input relation is
    the graph of `packVal T` and the output relation the graph of `packOuts T`, as in
    `tileLegalCert T`. -/
def bridgeLegalCert (S : MemTarget T) (fuel : Nat) (Γ : Ctxt jasminTileMem)
    (ts : List jasminTileMem.Ty) :
    StepCert (legaliseBridge S (Γ := Γ) (ts := ts)) (memSem fuel Γ ts)
      (targetSem jasminVecMem fuel (Γ.map (legalTy T)) (ts.map (legalTy T))) :=
  StepCert.ofTransport _ _ (fun V => packVal T V) (fun o => packOuts T o)
    fun p q V hf => bridgeLegal_denote S fuel p q hf V

open PassChain in
/-- **The leakage certificate of legalisation.** Between the two-run semantics of the two
    leak semantics: the input relation is the graph of `packVal T` on each valuation, and the
    output relation is equality of the pairs of event lists. -/
def bridgeLegalLeakCert {S : MemTarget T} {M : LeakModel jasminDialect}
    (hT : T.Quiet (jasminVecMemLeak M)) (hS : S.Addr M) (fuel : Nat) (Γ : Ctxt jasminTileMem)
    (ts : List jasminTileMem.Ty) :
    StepCert (legaliseBridge S (Γ := Γ) (ts := ts)) (memLeakSem M fuel Γ ts).twoRun
      (vecMemLeakSem M fuel (Γ.map (legalTy T)) (ts.map (legalTy T))).twoRun where
  relIn V W := W = (packVal T V.1, packVal T V.2)
  relOut a b := b = a
  sound := by
    intro p q V W o hf hVW hd
    obtain ⟨V1, V2⟩ := V
    subst hVW
    obtain ⟨hd1, hd2⟩ := (memLeakSem M fuel Γ ts).twoRun_den_eq_some hd
    exact ⟨o, (vecMemLeakSem M fuel _ _).twoRun_den q _ _ _ _
      ((bridgeLegal_events hT hS fuel p q hf V1).trans hd1)
      ((bridgeLegal_events hT hS fuel p q hf V2).trans hd2), rfl⟩

end Lowering

/-! ## 4. The two lane shapes of a ZMM register -/

section X86

/-- The block of a load of lanes of `w` bits from an array of `N` elements: one `vload`. -/
def loadBlk (w N : Nat) :
    Com jasminVecMem [JasminTy.stackArr w N, JasminTy.reg 64] VReg :=
  .var (vloadE w N .here (.there .here)) (.ret .here)

/-- The block of a store of lanes of `w` bits to an array of `N` elements: one `vstore`. -/
def vstoreBlk (w N : Nat) :
    Com jasminVecMem [JasminTy.stackArr w N, JasminTy.reg 64, VReg] (JasminTy.stackArr w N) :=
  .var (vstoreE w N .here (.there .here) (.there (.there .here))) (.ret .here)

/-- The block of a broadcast of a register of `w` bits: one `vsplat`. -/
def splatBlk (w : Nat) : Com jasminVecMem [JasminTy.reg w] VReg :=
  .var (vsplatE w .here) (.ret .here)

/-- A let-binding of `jasminVecMem` denotes its body on the extended valuation. -/
theorem memDenote_var {Γ : Ctxt jasminVecMem} {s t : JasminTy} (e : Expr jasminVecMem Γ s)
    (body : Com jasminVecMem (s :: Γ) t) (V : Valuation Γ) :
    (Com.var e body).denote V = body.denote (V.extend (e.denote V)) := Eq.trans rfl rfl

/-- A return of `jasminVecMem` denotes the value of its variable. -/
theorem memDenote_ret {Γ : Ctxt jasminVecMem} {t : JasminTy} (v : Var Γ t) (V : Valuation Γ) :
    (Com.ret v : Com jasminVecMem Γ t).denote V = v.lookup V := Eq.trans rfl rfl

/-- The variable bound last reads the value the valuation was extended by. -/
theorem memLookup_here {Γ : Ctxt jasminVecMem} {t : JasminTy} (v : ⟦t⟧) (V : Valuation Γ) :
    (Var.here : Var (t :: Γ) t).lookup (V.extend v) = v := Eq.trans rfl rfl

/-- The value of `loadBlk`. -/
theorem loadBlk_denote (w N : Nat) (a : Fin N → BitVec w) (i : BitVec 64) :
    (loadBlk w N).denote (.cons a (.cons i .nil)) = vecLoad w a i.toNat := by
  simp only [loadBlk, memDenote_var, memDenote_ret, vloadE_denote, memLookup_here]
  exact congrArg₂ (vecLoad w) (Eq.trans rfl rfl) (Eq.trans rfl rfl)

/-- The value of `vstoreBlk`. -/
theorem vstoreBlk_denote (w N : Nat) (a : Fin N → BitVec w) (i : BitVec 64) (v : BitVec 512) :
    (vstoreBlk w N).denote (.cons a (.cons i (.cons v .nil))) = vecStore w a i.toNat v := by
  simp only [vstoreBlk, memDenote_var, memDenote_ret, vstoreE_denote, memLookup_here]
  exact Eq.trans rfl rfl

/-- The value of `splatBlk`. -/
theorem splatBlk_denote (w : Nat) (x : BitVec w) :
    (splatBlk w).denote (.cons x .nil) = bcast w x := by
  simp only [splatBlk, memDenote_var, memDenote_ret, vsplatE_denote, memLookup_here]
  exact congrArg (bcast w) (Eq.trans rfl rfl)

/-- `loadBlk` emits the reading of its index. -/
theorem loadBlk_ctLeak (M : LeakModel jasminDialect) (w N : Nat) (a : Fin N → BitVec w)
    (i : BitVec 64) :
    Com.ctLeak (jasminVecMemLeak M) (loadBlk w N) (.cons a (.cons i .nil)) =
      [CTLeak.addr "" ((M.valNat (.reg 64) i : Nat) : Int)] := rfl

/-- `vstoreBlk` emits the reading of its index. -/
theorem vstoreBlk_ctLeak (M : LeakModel jasminDialect) (w N : Nat) (a : Fin N → BitVec w)
    (i : BitVec 64) (v : BitVec 512) :
    Com.ctLeak (jasminVecMemLeak M) (vstoreBlk w N) (.cons a (.cons i (.cons v .nil))) =
      [CTLeak.addr "" ((M.valNat (.reg 64) i : Nat) : Int)] := rfl

/-- `splatBlk` emits no event. -/
theorem splatBlk_ctLeak (M : LeakModel jasminDialect) (w : Nat)
    (W : Valuation (d := jasminVecMem) [JasminTy.reg w]) :
    Com.ctLeak (jasminVecMemLeak M) (splatBlk w) W = [] := rfl

/-- The lane shape of eight 64-bit lanes in `jasminVecMem`. -/
abbrev memQ : TileTarget jasminVecMem := memShape selQ

/-- The lane shape of sixteen 32-bit lanes in `jasminVecMem`. -/
abbrev memD : TileTarget jasminVecMem := memShape selD

/-- **The gate at eight 64-bit lanes.** `tileLoad` is one `vload`, `tileStore` one `vstore`,
    `tileSplat` one `vsplat`, at the lane width 64. -/
def qwordMem : MemTarget memQ where
  load? := fun N => some (loadBlk 64 N)
  store? := fun N => some (vstoreBlk 64 N)
  splat? := some (splatBlk 64)
  load_lane := by
    intro N blk h a i k
    cases h
    exact (congrArg (fun x : BitVec 512 => vlane 64 8 x k) (loadBlk_denote 64 N a i)).trans
      (lane_vecLoad (w := 64) (k := k.val) a i.toNat (by decide)
        (isShape_qword.bound k.isLt))
  store_val := by
    intro N blk h a i t
    cases h
    have hp : memQ.pack memQ.shapeTy t = packAt 8 64 (vof 64 8) (.tile 8 64) t := by
      simp only [memQ, memShape, selQ]
    rw [hp]
    exact (vstoreBlk_denote 64 N a i _).trans
      (vecStore_eq_laneStore (w := 64) a i.toNat _ t
        (fun j => congrFun (vlane_packAt_qword t) j))
  splat_lane := by
    intro blk h x k
    cases h
    exact (congrArg (fun y : BitVec 512 => vlane 64 8 y k) (splatBlk_denote 64 x)).trans
      (lane_vsplat (w := 64) (k := k.val) x (by decide) (isShape_qword.bound k.isLt))

/-- **The gate at sixteen 32-bit lanes.** `tileLoad` is one `vload`, `tileStore` one
    `vstore`, `tileSplat` one `vsplat`, at the lane width 32. -/
def dwordMem : MemTarget memD where
  load? := fun N => some (loadBlk 32 N)
  store? := fun N => some (vstoreBlk 32 N)
  splat? := some (splatBlk 32)
  load_lane := by
    intro N blk h a i k
    cases h
    exact (congrArg (fun x : BitVec 512 => vlane 32 16 x k) (loadBlk_denote 32 N a i)).trans
      (lane_vecLoad (w := 32) (k := k.val) a i.toNat (by decide)
        (isShape_dword.bound k.isLt))
  store_val := by
    intro N blk h a i t
    cases h
    have hp : memD.pack memD.shapeTy t = packAt 16 32 (vof 32 16) (.tile 16 32) t := by
      simp only [memD, memShape, selD]
    rw [hp]
    exact (vstoreBlk_denote 32 N a i _).trans
      (vecStore_eq_laneStore (w := 32) a i.toNat _ t
        (fun j => congrFun (vlane_packAt_dword t) j))
  splat_lane := by
    intro blk h x k
    cases h
    exact (congrArg (fun y : BitVec 512 => vlane 32 16 y k) (splatBlk_denote 32 x)).trans
      (lane_vsplat (w := 32) (k := k.val) x (by decide) (isShape_dword.bound k.isLt))

/-- The blocks of `qwordMem` emit one address event per load and per store and none for a
    broadcast, over every leakage model of `jasminDialect`. -/
theorem qwordMem_addr (M : LeakModel jasminDialect) : qwordMem.Addr M where
  load := by
    intro N blk h a i
    cases h
    exact loadBlk_ctLeak M 64 N a i
  store := by
    intro N blk h a i v
    cases h
    exact vstoreBlk_ctLeak M 64 N a i v
  splat := by
    intro blk h W
    cases h
    exact splatBlk_ctLeak M 64 W

/-- The blocks of `dwordMem` emit one address event per load and per store and none for a
    broadcast, over every leakage model of `jasminDialect`. -/
theorem dwordMem_addr (M : LeakModel jasminDialect) : dwordMem.Addr M where
  load := by
    intro N blk h a i
    cases h
    exact loadBlk_ctLeak M 32 N a i
  store := by
    intro N blk h a i v
    cases h
    exact vstoreBlk_ctLeak M 32 N a i v
  splat := by
    intro blk h W
    cases h
    exact splatBlk_ctLeak M 32 W

/-- The blocks of `memQ` emit no event, over every leakage model of `jasminDialect`. -/
theorem memQ_quiet (M : LeakModel jasminDialect) : memQ.Quiet (jasminVecMemLeak M) :=
  memShape_quiet (selQ_quiet M)

/-- The blocks of `memD` emit no event, over every leakage model of `jasminDialect`. -/
theorem memD_quiet (M : LeakModel jasminDialect) : memD.Quiet (jasminVecMemLeak M) :=
  memShape_quiet (selD_quiet M)

/-- **The gate table.** At both shapes a load is one `vload`, a store one `vstore` and a
    broadcast one `vsplat`. -/
theorem bridge_gate_table (N : Nat) :
    qwordMem.gate (.tileLoad 8 64 N) = some (loadBlk 64 N) ∧
      qwordMem.gate (.tileStore 8 64 N) = some (vstoreBlk 64 N) ∧
      qwordMem.gate (.tileSplat 8 64) = some (splatBlk 64) ∧
      dwordMem.gate (.tileLoad 16 32 N) = some (loadBlk 32 N) ∧
      dwordMem.gate (.tileStore 16 32 N) = some (vstoreBlk 32 N) ∧
      dwordMem.gate (.tileSplat 16 32) = some (splatBlk 32) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end X86

/-! ## 5. The composition with strip-mining -/

section Strip

variable {T : TileTarget jasminVecMem}

/-- The scalar reading of a legalised tuple of scalar types: the tuple, entrywise. -/
def scalarRd (T : TileTarget jasminVecMem) : (ts : List JasminTy) →
    Valuation (d := jasminVecMem) ((ts.map (Sum.inl (β := TileTy))).map (legalTy T)) →
    Valuation (d := jasminDialect) ts
  | [], _ => .nil
  | _ :: ts, .cons x xs => .cons x (scalarRd T ts xs)

/-- The scalar reading of the transport of a tuple of scalar types is its scalar reading. -/
theorem scalarRd_packOuts (T : TileTarget jasminVecMem) : (ts : List JasminTy) →
    (o : Valuation (d := jasminTileMem) (ts.map (Sum.inl (β := TileTy)))) →
    scalarRd T ts (packOuts T o) = unmapInl (d := jasminDialect) (e := tileDialect) o
  | [], _ => rfl
  | t :: ts, .cons x xs =>
      congrArg (HVector.cons (f := fun t : JasminTy => ⟦t⟧) (t := t) x)
        (scalarRd_packOuts T ts xs)

variable {l w : Nat} {Γ : Ctxt jasminDialect} {ts : List JasminTy}

/-- **The legalised strip-mined program runs to the results of the loop.** For a program
    `stripMine l w` accepts and a legalisation of the strip-mined program, the scalar reading
    of the denotation of the legalised program on the transport of a valuation `W` is the
    denotation of the program on the scalar reading of `W`, at every fuel. -/
theorem strip_legal_denote (S : MemTarget T) (fuel : Nat) (p : NFProg jasminDialect Γ ts)
    (q₀ : NFProg jasminTileMem (Γ.map (Sum.inl (β := TileTy)))
      (ts.map (Sum.inl (β := TileTy))))
    (hs : stripMine l w p = some q₀)
    (q : NFProg jasminVecMem ((Γ.map (Sum.inl (β := TileTy))).map (legalTy T))
      ((ts.map (Sum.inl (β := TileTy))).map (legalTy T)))
    (hq : legaliseBridge S q₀ = some q)
    (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy)))) :
    (q.denote fuel (packVal T W)).map (scalarRd T ts) =
      p.denote fuel (unmapInl (d := jasminDialect) (e := tileDialect) W) := by
  rw [bridgeLegal_denote S fuel q₀ q hq W, Option.map_map,
    ← stripMine_denote fuel p q₀ hs W]
  exact congrArg (fun f => Option.map f _) (funext (scalarRd_packOuts T ts))

/-- **The events of the legalised strip-mined program** are `stripEv` of the events of the
    loop: over a model in which the lifted operations and the added index operations are
    quiet, a scalar load and store emit their index, the blocks of `T` are quiet and the
    blocks of `S` emit the reading of the index. -/
theorem strip_legal_events {S : MemTarget T} (M : LeakModel jasminDialect)
    (hT : T.Quiet (jasminVecMemLeak M)) (hS : S.Addr M) (hM : LaneQuiet w M) (hA : ArrAddr M)
    (hI : IdxQuiet l M) (fuel : Nat) (p : NFProg jasminDialect Γ ts)
    (q₀ : NFProg jasminTileMem (Γ.map (Sum.inl (β := TileTy)))
      (ts.map (Sum.inl (β := TileTy))))
    (hs : stripMine l w p = some q₀)
    (q : NFProg jasminVecMem ((Γ.map (Sum.inl (β := TileTy))).map (legalTy T))
      ((ts.map (Sum.inl (β := TileTy))).map (legalTy T)))
    (hq : legaliseBridge S q₀ = some q)
    (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy)))) :
    (NFProg.leakRun (jasminVecMemLeak M) fuel q (packVal T W)).map Prod.snd =
      ((NFProg.leakRunM M fuel p
        (unmapInl (d := jasminDialect) (e := tileDialect) W)).map Prod.snd).map
        (stripEv (2 ^ l) (iterEvents M p)) :=
  (bridgeLegal_events hT hS fuel q₀ q hq W).trans (stripMine_events M hM hA hI fuel p q₀ hs W)

end Strip

/-! ## 6. The scaled addition of arrays -/

section Accept

/-- **`legaliseBridge qwordMem` accepts the strip-mined `scaledAddLoop N`**, for arrays of at
    least 8 elements. -/
theorem scaledAddStrip_legal (N : Nat) (h : 8 ≤ N) :
    (legaliseBridge qwordMem (scaledAddStrip N h)).isSome = true := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' h
  rfl

/-- The legalised strip-mined program of `scaledAddLoop N`: a program of `jasminVecMem`. -/
def scaledAddVec (N : Nat) (h : 8 ≤ N) :
    NFProg jasminVecMem
      (((scaledAddCtx N).map (Sum.inl (β := TileTy))).map (legalTy memQ))
      (([JasminTy.stackArr 64 N].map (Sum.inl (β := TileTy))).map (legalTy memQ)) :=
  (legaliseBridge qwordMem (scaledAddStrip N h)).get (scaledAddStrip_legal N h)

/-- `legaliseBridge qwordMem` returns `scaledAddVec`. -/
theorem legaliseBridge_scaledAddStrip (N : Nat) (h : 8 ≤ N) :
    legaliseBridge qwordMem (scaledAddStrip N h) = some (scaledAddVec N h) :=
  (Option.some_get (scaledAddStrip_legal N h)).symm

/-- **The result of `scaledAddVec`.** On the transport of a valuation whose scalar reading is
    the trip count, the arrays and the word, the scalar reading of the result of
    `scaledAddVec` is `scaledAddOut`, at every fuel. -/
theorem scaledAddVec_denote (N : Nat) (h : 8 ≤ N) (fuel : Nat) (cnt : BitVec 64)
    (a b : Fin N → BitVec 64) (c : BitVec 64) (out : Fin N → BitVec 64)
    (W : Valuation (d := jasminTileDialect) ((scaledAddCtx N).map (Sum.inl (β := TileTy))))
    (hW : unmapInl (d := jasminDialect) (e := tileDialect) W = scaledAddIn cnt a b c out) :
    ((scaledAddVec N h).denote fuel (packVal memQ W)).map
        (scalarRd memQ [JasminTy.stackArr 64 N]) =
      some (arrTuple (scaledAddOut cnt a b c out)) := by
  rw [strip_legal_denote qwordMem fuel (scaledAddLoop N) (scaledAddStrip N h)
    (stripMine_scaledAddLoop N h) (scaledAddVec N h) (legaliseBridge_scaledAddStrip N h) W, hW]
  exact scaledAddLoop_denote N fuel cnt a b c out

/-- **The events of `scaledAddVec`** over `addrModel` are `stripEv 8 3` of the events of the
    loop. -/
theorem scaledAddVec_events (N : Nat) (h : 8 ≤ N) (fuel : Nat)
    (W : Valuation (d := jasminTileDialect) ((scaledAddCtx N).map (Sum.inl (β := TileTy)))) :
    (NFProg.leakRun (jasminVecMemLeak addrModel) fuel (scaledAddVec N h)
        (packVal memQ W)).map Prod.snd =
      ((NFProg.leakRunM addrModel fuel (scaledAddLoop N)
        (unmapInl (d := jasminDialect) (e := tileDialect) W)).map Prod.snd).map
        (stripEv 8 3) :=
  strip_legal_events addrModel (memQ_quiet addrModel) (qwordMem_addr addrModel)
    (addrModel_laneQuiet 64) addrModel_arrAddr (addrModel_idxQuiet 3) fuel (scaledAddLoop N)
    (scaledAddStrip N h) (stripMine_scaledAddLoop N h) (scaledAddVec N h)
    (legaliseBridge_scaledAddStrip N h) W

end Accept

end CatCrypt.Crypto.SecureCompilation.VIR.TileBridgeLegal
