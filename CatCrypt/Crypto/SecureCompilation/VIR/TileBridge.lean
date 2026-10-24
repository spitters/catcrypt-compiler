/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum

/-!
# Tile memory and broadcast operations over a scalar dialect

`scalarTile d` (`VIR/NFTileSum.lean`) is the coproduct of a scalar dialect `d` and
`tileDialect`: its type alphabet is `d.Ty ⊕ TileTy`, and no operation of either summand has
operands of both. The bridge operation set `BridgeOp` is a third family of operations over the
same alphabet whose signatures mix the two: a load of `L` consecutive array elements into a
tile, a store of the lanes of a tile to `L` consecutive array positions, and the broadcast of
a scalar element to every lane.

The class `HasLaneArr d` names what the bridge needs of the scalar dialect: an element type
`elt w` read as a `w`-bit lane, an array type `arr w N`, and the total read and write of an
array at a position. Positions are natural numbers; an operation takes its index as a value of
the trip-counter type `HasWord64.word` and reads it by `HasWord64.toNat`.

`tileMem d` is the operation sum `Dialect.opSum (scalarTile d) (bridge d)`
(`VIR/DialectOpSum.lean`). Its trip counter, branch bit and call environment are those of
`scalarTile d`, so `NFProg (tileMem d)` has the counted loops and branches of
`NFProg (scalarTile d)` with the bridge operations among its let-bindings.

The leakage model `tileMemLeak M` extends `scalarTileLeak d M`: `tileLoad` and `tileStore`
have the class `addrAt 1` and emit one address event, the reading of the index; `tileSplat`
is quiet. One event per access of `L` lanes is the event of one vector load or store.

`jasminDialect` is an instance of `HasLaneArr` with `elt w = reg w`,
`arr w N = stackArr w N`, `stackGet` and `stackSet`.

## Main definitions

* `HasLaneArr`, `laneLoad`, `laneStore`, `laneSplat` — the lane interface of a scalar dialect
  and the three functions on values.
* `BridgeOp`, `bridge`, `tileMem` — the bridge operation set, its dialect and the operation
  sum with `scalarTile d`.
* `tileMemDenote`, `tileMemDenP`, `tileMemLeak`, `tileMemLeakRun` — the denotation and the
  leakage model of `tileMem d`, and the denotation and leakage run of its programs.
* `embedExpr`, `embed` — the inclusion of `NFProg (scalarTile d)` into `NFProg (tileMem d)`.
* `instHasLaneArrJasmin`, `jasminLaneLoad`, `jasminLaneStore`, `jasminBridge`,
  `jasminTileMem`, `jasminTileMemDenote` — the instance at `jasminDialect`.

## Main results

* `tileMem_opLeak_inl`, `tileMem_opLeak_scalar`, `tileMem_opLeak_tile` — an operation of
  `scalarTile d` emits in `tileMem d` the events it emits in `scalarTile d`.
* `tileMem_opLeak_tileLoad`, `tileMem_opLeak_tileStore`, `tileMem_opLeak_tileSplat` — the
  events of the bridge operations.
* `tileMem_nfCTRel_of_levelCheck'` — a program the level checker accepts is constant time
  relative to its runs.
* `embed_denote`, `embed_leakRunM`, `embed_levelCheck'`, `embed_nfCTRel` — the inclusion
  preserves the denotation, the leakage run and the result of the level checker.
* `jasmin_tileLoad_denote`, `jasmin_tileStore_denote`, `jasmin_tileSplat_denote` — the bridge
  operations over `jasminDialect` in terms of `stackGet` and `stackSet`.
* `jasmin_laneStore_outside`, `jasmin_laneStore_inside` — a store of `L` lanes at index `i`
  leaves every position outside the residues of `i, …, i + L - 1` unchanged, and for
  `L ≤ N` position `i + j` reads back lane `j`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileBridge

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
  (jasminDialect JasminTy stackGet stackSet)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## 1. The lane interface of a scalar dialect -/

/-- A scalar dialect with lane elements and arrays of them: the element type `elt w`, read as
    a `w`-bit lane by `toLane` and written from one by `ofLane`; the array type `arr w N` of
    `N` elements; and the total read `get` and write `set` of an array at a position. -/
class HasLaneArr (d : Dialect.{0, 0}) [TyDenote d.Ty] where
  /-- The type of a `w`-bit element. -/
  elt : Nat → d.Ty
  /-- The type of an array of `N` elements of `w` bits. -/
  arr : Nat → Nat → d.Ty
  /-- The lane an element denotes. -/
  toLane : {w : Nat} → ⟦elt w⟧ → BitVec w
  /-- The element of a lane. -/
  ofLane : {w : Nat} → BitVec w → ⟦elt w⟧
  /-- The element of an array at a position. -/
  get : {w N : Nat} → ⟦arr w N⟧ → Nat → ⟦elt w⟧
  /-- The array with the element at a position replaced. -/
  set : {w N : Nat} → ⟦arr w N⟧ → Nat → ⟦elt w⟧ → ⟦arr w N⟧

section Lanes

variable (d : Dialect.{0, 0}) [TyDenote d.Ty] [HasLaneArr d]

/-- The tile of `L` lanes read from the array `a` at the position `i`: lane `j` is the
    element at `i + j`. -/
def laneLoad (L : Nat) {w N : Nat} (a : ⟦HasLaneArr.arr (d := d) w N⟧) (i : Nat) :
    Fin L → BitVec w :=
  fun j => HasLaneArr.toLane (d := d) (HasLaneArr.get a (i + j.val))

/-- The array `a` after the lanes of the tile `t` are written at the positions
    `i, …, i + L - 1`, lane `0` first. -/
def laneStore {L w N : Nat} (a : ⟦HasLaneArr.arr (d := d) w N⟧) (i : Nat)
    (t : Fin L → BitVec w) : ⟦HasLaneArr.arr (d := d) w N⟧ :=
  (List.finRange L).foldl
    (fun acc j => HasLaneArr.set acc (i + j.val) (HasLaneArr.ofLane (d := d) (t j))) a

/-- The tile of `L` lanes with the element `x` in every lane. -/
def laneSplat (L : Nat) {w : Nat} (x : ⟦HasLaneArr.elt (d := d) w⟧) : Fin L → BitVec w :=
  fun _ => HasLaneArr.toLane (d := d) x

/-- Lane `j` of a load at `i` is the element at `i + j`. -/
@[simp] theorem laneLoad_apply (L : Nat) {w N : Nat} (a : ⟦HasLaneArr.arr (d := d) w N⟧)
    (i : Nat) (j : Fin L) :
    laneLoad d L a i j = HasLaneArr.toLane (d := d) (HasLaneArr.get a (i + j.val)) := rfl

/-- Every lane of a broadcast is the lane of the element. -/
@[simp] theorem laneSplat_apply (L : Nat) {w : Nat} (x : ⟦HasLaneArr.elt (d := d) w⟧)
    (j : Fin L) : laneSplat d L x j = HasLaneArr.toLane (d := d) x := rfl

end Lanes

/-! ## 2. The bridge operation set -/

/-- The operations between arrays or elements of a scalar dialect and tiles. -/
inductive BridgeOp where
  /-- Load `L` consecutive `w`-bit elements of an array of `N` elements into a tile. -/
  | tileLoad (L w N : Nat)
  /-- Store the `L` lanes of a tile to consecutive positions of an array of `N` elements. -/
  | tileStore (L w N : Nat)
  /-- Broadcast a `w`-bit element to the `L` lanes of a tile. -/
  | tileSplat (L w : Nat)

section Bridge

variable (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d] [HasWord64 d]
  [HasLaneArr d]

/-- The dialect of the bridge operations over the type alphabet of `scalarTile d`. -/
abbrev bridge : Dialect.{0, 0} where
  Op := BridgeOp
  Ty := d.Ty ⊕ TileTy

/-- The signatures of the bridge operations: `tileLoad` takes an array and an index and
    returns a tile; `tileStore` takes an array, an index and a tile and returns the array;
    `tileSplat` takes an element and returns a tile. -/
instance instDialectSignatureBridge : DialectSignature (bridge d) where
  sig
    | .tileLoad _ w N => [.inl (HasLaneArr.arr (d := d) w N), .inl (HasWord64.word (d := d))]
    | .tileStore L w N =>
        [.inl (HasLaneArr.arr (d := d) w N), .inl (HasWord64.word (d := d)), .inr (.tile L w)]
    | .tileSplat _ w => [.inl (HasLaneArr.elt (d := d) w)]
  ret
    | .tileLoad L w _ => .inr (.tile L w)
    | .tileStore _ w N => .inl (HasLaneArr.arr (d := d) w N)
    | .tileSplat L w => .inr (.tile L w)

/-- The denotation of the bridge operations: `laneLoad`, `laneStore` and `laneSplat` at the
    position the index denotes. -/
instance instDialectDenoteBridge : DialectDenote (bridge d) where
  denote
    | .tileLoad L w N => fun args =>
        let a : ⟦HasLaneArr.arr (d := d) w N⟧ := args.head
        let i : ⟦HasWord64.word (d := d)⟧ := args.tail.head
        (laneLoad d L a (HasWord64.toNat (d := d) i) : Fin L → BitVec w)
    | .tileStore L w N => fun args =>
        let a : ⟦HasLaneArr.arr (d := d) w N⟧ := args.head
        let i : ⟦HasWord64.word (d := d)⟧ := args.tail.head
        let t : Fin L → BitVec w := args.tail.tail.head
        (laneStore d a (HasWord64.toNat (d := d) i) t : ⟦HasLaneArr.arr (d := d) w N⟧)
    | .tileSplat L w => fun args =>
        let x : ⟦HasLaneArr.elt (d := d) w⟧ := args.head
        (laneSplat d L x : Fin L → BitVec w)

/-- The event class of a bridge operation: `tileLoad` and `tileStore` address memory at
    their index, argument `1`; `tileSplat` is quiet. -/
def bridgeKind : BridgeOp → LeakKind
  | .tileLoad .. => .addrAt 1
  | .tileStore .. => .addrAt 1
  | .tileSplat .. => .quiet

/-! ## 3. The operation sum with `scalarTile d` -/

/-- The operation sum of `scalarTile d` and the bridge operations. -/
abbrev tileMem : Dialect.{0, 0} := Dialect.opSum (scalarTile d) (bridge d)

/-- The signature of `tileMem d`: the signature of the summand. -/
instance instDialectSignatureTileMem : DialectSignature (tileMem d) where
  sig
    | .inl o => DialectSignature.sig (d := scalarTile d) o
    | .inr o => DialectSignature.sig (d := bridge d) o
  ret
    | .inl o => DialectSignature.ret (d := scalarTile d) o
    | .inr o => DialectSignature.ret (d := bridge d) o

/-- The trip counter of `tileMem d` is the counter of `d`. -/
instance instHasWord64TileMem : HasWord64 (tileMem d) where
  word := .inl (HasWord64.word (d := d))
  toNat := HasWord64.toNat (d := d)
  ofNat := HasWord64.ofNat (d := d)

/-- The bit of `tileMem d` is the bit of `d`. -/
instance instHasBoolBitTileMem [HasBoolBit d] : HasBoolBit (tileMem d) where
  bit := .inl (HasBitType.bit (d := d))
  toBool := HasBoolBit.toBool (d := d)

/-- `tileMem d` denotes calls in the empty environment. -/
instance instCallDenoteTileMem : CallDenote (tileMem d) := ⟨.empty⟩

/-- The denotation of `tileMem d` over the denotation `D` of `d`: an operation of
    `scalarTile d` by `scalarTileDenote d D`, a bridge operation by its total denotation. -/
@[instance_reducible] def tileMemDenote (D : DialectDenoteM d Option) :
    DialectDenoteM (tileMem d) Option where
  denoteM
    | .inl o, args => (scalarTileDenote d D).denoteM o args
    | .inr o, args => some (DialectDenote.denote (d := bridge d) o args)

/-- An operation of `scalarTile d` denotes in `tileMem d` as in `scalarTile d`. -/
@[simp] theorem tileMemDenote_inl (D : DialectDenoteM d Option) (o : (scalarTile d).Op)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := scalarTile d) o)) :
    (tileMemDenote d D).denoteM (.inl o) args = (scalarTileDenote d D).denoteM o args := rfl

/-- `tileLoad` returns the tile `laneLoad` reads at the position the index denotes. -/
@[simp] theorem tileMemDenote_tileLoad (D : DialectDenoteM d Option) (L w N : Nat)
    (a : ⟦HasLaneArr.arr (d := d) w N⟧) (i : ⟦HasWord64.word (d := d)⟧) :
    (tileMemDenote d D).denoteM (.inr (.tileLoad L w N)) (.cons a (.cons i .nil))
      = some (laneLoad d L a (HasWord64.toNat (d := d) i)) := rfl

/-- `tileStore` returns the array `laneStore` writes at the position the index denotes. -/
@[simp] theorem tileMemDenote_tileStore (D : DialectDenoteM d Option) (L w N : Nat)
    (a : ⟦HasLaneArr.arr (d := d) w N⟧) (i : ⟦HasWord64.word (d := d)⟧)
    (t : Fin L → BitVec w) :
    (tileMemDenote d D).denoteM (.inr (.tileStore L w N)) (.cons a (.cons i (.cons t .nil)))
      = some (laneStore d a (HasWord64.toNat (d := d) i) t) := rfl

/-- `tileSplat` returns the tile with the element in every lane. -/
@[simp] theorem tileMemDenote_tileSplat (D : DialectDenoteM d Option) (L w : Nat)
    (x : ⟦HasLaneArr.elt (d := d) w⟧) :
    (tileMemDenote d D).denoteM (.inr (.tileSplat L w)) (.cons x .nil)
      = some (laneSplat d L x) := rfl

/-! ## 4. The leakage model -/

/-- The leakage model of `tileMem d` over a model `M` of `d`: an operation of `scalarTile d`
    has its class in `scalarTileLeak d M`, a bridge operation the class `bridgeKind` gives
    it, and a value the reading of `scalarTileLeak d M`. -/
def tileMemLeak (M : LeakModel d) : LeakModel (tileMem d) where
  kind := Sum.elim (scalarTileLeak d M).kind bridgeKind
  valNat := (scalarTileLeak d M).valNat

/-- An operation of `scalarTile d` has the class `scalarTileLeak d M` gives it. -/
@[simp] theorem tileMemLeak_kind_inl (M : LeakModel d) (op : (scalarTile d).Op) :
    (tileMemLeak d M).kind (.inl op) = (scalarTileLeak d M).kind op := rfl

/-- A bridge operation has the class `bridgeKind` gives it. -/
@[simp] theorem tileMemLeak_kind_inr (M : LeakModel d) (op : BridgeOp) :
    (tileMemLeak d M).kind (.inr op) = bridgeKind op := rfl

/-- The readings of a list of values are those of `scalarTileLeak d M`. -/
theorem tileMem_valsNat (M : LeakModel d) :
    ∀ {ts : List (d.Ty ⊕ TileTy)} (vals : HVector (fun t => ⟦t⟧) ts),
      valsNat (tileMemLeak d M) vals = valsNat (scalarTileLeak d M) vals
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show (scalarTileLeak d M).valNat _ x :: valsNat (tileMemLeak d M) xs
        = (scalarTileLeak d M).valNat _ x :: valsNat (scalarTileLeak d M) xs
      rw [tileMem_valsNat M xs]

/-- **The events of an operation of `scalarTile d`** in `tileMem d` are its events in
    `scalarTile d`. -/
theorem tileMem_opLeak_inl (M : LeakModel d) (op : (scalarTile d).Op)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := scalarTile d) op)) :
    opLeak (tileMemLeak d M) (.inl op) vals = opLeak (scalarTileLeak d M) op vals := by
  unfold opLeak
  rw [tileMemLeak_kind_inl, tileMem_valsNat d M vals]

/-- A scalar operation emits in `tileMem d` the events it emits in `d`. -/
theorem tileMem_opLeak_scalar (M : LeakModel d) (op : d.Op)
    (vals : HVector (fun t => ⟦t⟧)
      ((DialectSignature.sig op).map (Sum.inl (β := TileTy)))) :
    opLeak (tileMemLeak d M) (.inl (.inl op)) vals
      = opLeak M op (unmapInl (e := tileDialect) vals) :=
  (tileMem_opLeak_inl d M (.inl op) vals).trans (scalarTile_opLeak_inl d M op vals)

/-- A tile operation emits no event in `tileMem d`. -/
theorem tileMem_opLeak_tile (M : LeakModel d) (op : TileOp)
    (vals : HVector (fun t => ⟦t⟧)
      ((DialectSignature.sig (d := tileDialect) op).map (Sum.inr (α := d.Ty)))) :
    opLeak (tileMemLeak d M) (.inl (.inr op)) vals = [] :=
  (tileMem_opLeak_inl d M (.inr op) vals).trans (scalarTile_opLeak_inr d M op vals)

/-- **`tileLoad` emits one address event**, the reading of its index. -/
theorem tileMem_opLeak_tileLoad (M : LeakModel d) (L w N : Nat)
    (a : ⟦HasLaneArr.arr (d := d) w N⟧) (i : ⟦HasWord64.word (d := d)⟧) :
    opLeak (tileMemLeak d M) (.inr (.tileLoad L w N)) (.cons a (.cons i .nil))
      = [CTLeak.addr "" ((M.valNat (HasWord64.word (d := d)) i : Nat) : Int)] := rfl

/-- **`tileStore` emits one address event**, the reading of its index. -/
theorem tileMem_opLeak_tileStore (M : LeakModel d) (L w N : Nat)
    (a : ⟦HasLaneArr.arr (d := d) w N⟧) (i : ⟦HasWord64.word (d := d)⟧)
    (t : Fin L → BitVec w) :
    opLeak (tileMemLeak d M) (.inr (.tileStore L w N)) (.cons a (.cons i (.cons t .nil)))
      = [CTLeak.addr "" ((M.valNat (HasWord64.word (d := d)) i : Nat) : Int)] := rfl

/-- **`tileSplat` emits no event.** -/
theorem tileMem_opLeak_tileSplat (M : LeakModel d) (L w : Nat)
    (vals : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := bridge d) (.tileSplat L w))) :
    opLeak (tileMemLeak d M) (.inr (.tileSplat L w)) vals = [] := rfl

/-- The level checker requires a public index of `tileLoad`. -/
theorem tileMem_opAccepts_tileLoad (M : LeakModel d) (L w N : Nat) (ls : List SecretLevel) :
    opAccepts (tileMemLeak d M) (.inr (.tileLoad L w N)) ls
      = decide (ls.getD 1 .Secret = .Public) := rfl

/-- The level checker requires a public index of `tileStore`. -/
theorem tileMem_opAccepts_tileStore (M : LeakModel d) (L w N : Nat) (ls : List SecretLevel) :
    opAccepts (tileMemLeak d M) (.inr (.tileStore L w N)) ls
      = decide (ls.getD 1 .Secret = .Public) := rfl

/-- The level checker places no constraint on `tileSplat`. -/
theorem tileMem_opAccepts_tileSplat (M : LeakModel d) (L w : Nat) (ls : List SecretLevel) :
    opAccepts (tileMemLeak d M) (.inr (.tileSplat L w)) ls = true := rfl

/-- The constraint of an operation of `scalarTile d` is its constraint in `scalarTile d`. -/
@[simp] theorem tileMem_opAccepts_inl (M : LeakModel d) (op : (scalarTile d).Op)
    (ls : List SecretLevel) :
    opAccepts (tileMemLeak d M) (.inl op) ls = opAccepts (scalarTileLeak d M) op ls := rfl

/-! ## 5. Programs of `tileMem d` -/

variable [HasBoolBit d]

/-- The denotation of a program of `tileMem d` over the denotation `D` of `d`. -/
abbrev tileMemDenP (D : DialectDenoteM d Option) (fuel : Nat) {Γ : Ctxt (tileMem d)}
    {ts : List (tileMem d).Ty} (p : NFProg (tileMem d) Γ ts) (V : Valuation Γ) :
    Option (Valuation ts) :=
  @NFProg.denote (tileMem d) _ _ _ _ (tileMemDenote d D) _ fuel Γ ts p V

/-- The leakage run of a program of `tileMem d` over the denotation `D` and the leakage
    model `M` of `d`. -/
abbrev tileMemLeakRun (D : DialectDenoteM d Option) (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt (tileMem d)} {ts : List (tileMem d).Ty} (p : NFProg (tileMem d) Γ ts)
    (V : Valuation Γ) : Option (Valuation ts × List CTLeak) :=
  @NFProg.leakRunM (tileMem d) _ _ _ _ (tileMemDenote d D) (tileMemLeak d M) fuel _ _ p V

/-- **The level checker on `tileMem d`.** A program the checker `levelCheck'` accepts at
    `tileMemLeak d M` for the entry labels `L` is constant time for `L` relative to the runs
    that succeed, over every denotation of `d`. -/
theorem tileMem_nfCTRel_of_levelCheck' (D : DialectDenoteM d Option) (M : LeakModel d)
    (fuel : Nat) {Γ : Ctxt (tileMem d)} {ts : List (tileMem d).Ty}
    (p : NFProg (tileMem d) Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' (tileMemLeak d M) p L).isSome) :
    @NFCTRel (tileMem d) _ _ _ _ (tileMemDenote d D) (tileMemLeak d M) Γ ts L fuel p :=
  @NFProg.nfCTRel_of_levelCheck' (tileMem d) _ _ _ _ (tileMemDenote d D)
    (tileMemLeak d M) fuel Γ ts p L h

/-! ## 6. The inclusion of `NFProg (scalarTile d)` -/

/-- An expression of `scalarTile d` as an expression of `tileMem d`: the operation tagged
    `.inl`, the arguments unchanged. -/
def embedExpr {Γ : Ctxt (scalarTile d)} {t : (scalarTile d).Ty}
    (e : Expr (scalarTile d) Γ t) : Expr (tileMem d) Γ t where
  op := .inl e.op
  retTy_eq := e.retTy_eq
  args := castArgs e.args

/-- A program of `scalarTile d` as a program of `tileMem d`: every let-bound operation
    tagged `.inl`, the regions kept. -/
def embed : {Γ : Ctxt (scalarTile d)} → {ts : List (scalarTile d).Ty} →
    NFProg (scalarTile d) Γ ts → NFProg (tileMem d) Γ ts
  | _, _, .ret vs => .ret (castArgs vs)
  | _, _, .var e k => .var (embedExpr d e) (embed k)
  | _, _, .forLoop count inits body k =>
      .forLoop (castVar count) (castArgs inits) (embed body) (embed k)
  | _, _, .ifThenElse cond thn els k =>
      .ifThenElse (castVar cond) (embed thn) (embed els) (embed k)
  | _, _, .whileLoop inits body k => .whileLoop (castArgs inits) (embed body) (embed k)
  | _, _, .call f args k => .call f (castArgs args) (embed k)

omit [HasBoolBit d] in
/-- An included expression denotes as the expression. -/
theorem embedExpr_denoteM (D : DialectDenoteM d Option) {Γ : Ctxt (scalarTile d)}
    {t : (scalarTile d).Ty} (e : Expr (scalarTile d) Γ t) (V : Valuation Γ) :
    @Expr.denoteM (tileMem d) Option _ _ (tileMemDenote d D) Γ t (embedExpr d e) V
      = @Expr.denoteM (scalarTile d) Option _ _ (scalarTileDenote d D) Γ t e V := by
  obtain ⟨op, rfl, args⟩ := e
  show (scalarTileDenote d D).denoteM op
      (Expr.lookupArgs (d := tileMem d) (castArgs args) V) = _
  rw [lookupArgs_castArgs args V]
  rfl

omit [HasBoolBit d] in
/-- An included expression emits the events of the expression. -/
theorem embedExpr_ctLeak (M : LeakModel d) {Γ : Ctxt (scalarTile d)}
    {t : (scalarTile d).Ty} (e : Expr (scalarTile d) Γ t) (V : Valuation Γ) :
    Expr.ctLeak (tileMemLeak d M) (embedExpr d e) V
      = Expr.ctLeak (scalarTileLeak d M) e V := by
  show opLeak (tileMemLeak d M) (.inl e.op)
      (Expr.lookupArgs (d := tileMem d) (castArgs e.args) V) = _
  rw [lookupArgs_castArgs e.args V, tileMem_opLeak_inl]
  rfl

/-! The functions below take the dialect as a parameter and recurse on a list or a count, so
their instances at `tileMem d` and at `scalarTile d` are equal by induction. -/

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The append of two vectors over the types of `tileMem d` is their append over the types of
    `scalarTile d`. -/
theorem hvAppend_tileMem {f : (d.Ty ⊕ TileTy) → Type} :
    ∀ {xs ys : List (d.Ty ⊕ TileTy)} (A : HVector f xs) (B : HVector f ys),
      hvAppend (d := tileMem d) A B = hvAppend (d := scalarTile d) A B
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons a A, B => congrArg (HVector.cons a) (hvAppend_tileMem A B)

omit [DialectSignature d] [HasWord64 d] [HasLaneArr d] in
/-- The exit-flag iteration of `tileMem d` is that of `scalarTile d`. -/
theorem whileIter_tileMem {cs : List (d.Ty ⊕ TileTy)}
    (step : Valuation (d := scalarTile d) cs →
      Option (Valuation (d := scalarTile d) (HasBitType.bit (d := scalarTile d) :: cs))) :
    ∀ (n : Nat) (acc : Valuation (d := scalarTile d) cs),
      NFProg.whileIter (d := tileMem d) step n acc
        = NFProg.whileIter (d := scalarTile d) step n acc
  | 0, _ => rfl
  | n + 1, acc => by
      show (step acc >>= fun r => if HasBoolBit.toBool (d := scalarTile d) r.head
          then NFProg.whileIter (d := tileMem d) step n r.tail else some r.tail)
        = (step acc >>= fun r => if HasBoolBit.toBool (d := scalarTile d) r.head
          then NFProg.whileIter (d := scalarTile d) step n r.tail else some r.tail)
      simp only [whileIter_tileMem step n]

omit [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The counted iteration with events of `tileMem d` is that of `scalarTile d`. -/
theorem forIterLeak_tileMem {cs : List (d.Ty ⊕ TileTy)}
    (step : Nat → Valuation (d := scalarTile d) cs →
      Option (Valuation (d := scalarTile d) cs × List CTLeak)) :
    ∀ (is : List Nat) (acc : Valuation (d := scalarTile d) cs),
      forIterLeak (d := tileMem d) step is acc = forIterLeak (d := scalarTile d) step is acc
  | [], _ => rfl
  | i :: is, acc => by
      show ((step i acc).bind fun r =>
          (forIterLeak (d := tileMem d) step is r.1).map fun q => (q.1, r.2 ++ q.2))
        = ((step i acc).bind fun r =>
          (forIterLeak (d := scalarTile d) step is r.1).map fun q => (q.1, r.2 ++ q.2))
      simp only [forIterLeak_tileMem step is]

omit [DialectSignature d] [HasWord64 d] [HasLaneArr d] in
/-- The exit-flag iteration with events of `tileMem d` is that of `scalarTile d`. -/
theorem whileIterLeak_tileMem {cs : List (d.Ty ⊕ TileTy)}
    (step : Valuation (d := scalarTile d) cs →
      Option (Valuation (d := scalarTile d) (HasBitType.bit (d := scalarTile d) :: cs)
        × List CTLeak)) :
    ∀ (n : Nat) (acc : Valuation (d := scalarTile d) cs),
      whileIterLeak (d := tileMem d) step n acc
        = whileIterLeak (d := scalarTile d) step n acc
  | 0, _ => rfl
  | n + 1, acc => by
      show ((step acc).bind fun r =>
          if HasBoolBit.toBool (d := scalarTile d) r.1.head then
            (whileIterLeak (d := tileMem d) step n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
        = ((step acc).bind fun r =>
          if HasBoolBit.toBool (d := scalarTile d) r.1.head then
            (whileIterLeak (d := scalarTile d) step n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
      simp only [whileIterLeak_tileMem step n]

/-- **The inclusion preserves the denotation**: an included program denotes, at every fuel
    and valuation, what the program denotes. -/
theorem embed_denote (D : DialectDenoteM d Option) (fuel : Nat) {Γ : Ctxt (scalarTile d)}
    {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts) (V : Valuation Γ) :
    tileMemDenP d D fuel (embed d p) V = scalarTileDenP d D fuel p V := by
  induction p with
  | ret vs => exact congrArg some (lookupArgs_castArgs vs V)
  | var e k ih =>
      simp only [embed, NFProg.denote, embedExpr_denoteM, ih]
      rfl
  | forLoop count inits body k ihb ihk =>
      simp only [embed, NFProg.denote, ihb, ihk, lookupArgs_castArgs, lookup_castVar,
        hvAppend_tileMem]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [embed, NFProg.denote, iht, ihe, ihk, lookup_castVar, hvAppend_tileMem]
      rfl
  | whileLoop inits body k ihb ihk =>
      simp only [embed, NFProg.denote, ihb, ihk, lookupArgs_castArgs, hvAppend_tileMem,
        whileIter_tileMem]
  | call f args k ih =>
      simp only [embed, NFProg.denote, ih, lookupArgs_castArgs, hvAppend_tileMem]
      rfl

/-- **The inclusion preserves the leakage run**: an included program runs, at every fuel and
    valuation, to the results and the events of the program. -/
theorem embed_leakRunM (D : DialectDenoteM d Option) (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt (scalarTile d)} {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts)
    (V : Valuation Γ) :
    tileMemLeakRun d D M fuel (embed d p) V = scalarTileLeakRun d D M fuel p V := by
  induction p with
  | ret vs => exact congrArg (fun x => some (x, [])) (lookupArgs_castArgs vs V)
  | var e k ih =>
      simp only [embed, NFProg.leakRunM, embedExpr_denoteM, embedExpr_ctLeak, ih]
      rfl
  | forLoop count inits body k ihb ihk =>
      simp only [embed, NFProg.leakRunM, ihb, ihk, lookupArgs_castArgs, lookup_castVar,
        hvAppend_tileMem, forIterLeak_tileMem]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [embed, NFProg.leakRunM, iht, ihe, ihk, lookup_castVar, hvAppend_tileMem]
      rfl
  | whileLoop inits body k ihb ihk =>
      simp only [embed, NFProg.leakRunM, ihb, ihk, lookupArgs_castArgs, hvAppend_tileMem,
        whileIterLeak_tileMem]
  | call f args k => rfl

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The level of a variable of `scalarTile d` read in `tileMem d` is its level. -/
theorem lvlOf_castVar :
    ∀ {Γ : List (d.Ty ⊕ TileTy)} {t : d.Ty ⊕ TileTy} (v : Var (d := scalarTile d) Γ t)
      (L : Labels (d := scalarTile d) Γ),
      lvlOf (d := tileMem d) (castVar v) L = lvlOf v L
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ L => lvlOf_castVar v L

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The levels of arguments of `scalarTile d` read in `tileMem d` are their levels. -/
theorem argLvls_castArgs {Γ : List (d.Ty ⊕ TileTy)} (L : Labels (d := scalarTile d) Γ) :
    ∀ {ts : List (d.Ty ⊕ TileTy)} (args : HVector (fun t => Var (d := scalarTile d) Γ t) ts),
      argLvls (d := tileMem d) L (castArgs args) = argLvls L args
  | [], .nil => rfl
  | _ :: _, .cons v vs =>
      congrArg₂ List.cons (lvlOf_castVar d v L) (argLvls_castArgs L vs)

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The levels of returned variables of `scalarTile d` read in `tileMem d` are their
    levels. -/
theorem retLvls_castArgs {Γ : List (d.Ty ⊕ TileTy)} (L : Labels (d := scalarTile d) Γ) :
    ∀ {ts : List (d.Ty ⊕ TileTy)} (vs : HVector (fun t => Var (d := scalarTile d) Γ t) ts),
      retLvls (d := tileMem d) L (castArgs vs) = retLvls L vs
  | [], .nil => rfl
  | _ :: _, .cons v vs =>
      congrArg₂ HVector.cons (lvlOf_castVar d v L) (retLvls_castArgs L vs)

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The pointwise order of levels over the types of `tileMem d` is that of `scalarTile d`. -/
theorem lvlsLe_tileMem : ∀ {cs : List (d.Ty ⊕ TileTy)} (A B : Labels (d := scalarTile d) cs),
    lvlsLe (d := tileMem d) A B = lvlsLe (d := scalarTile d) A B
  | [], .nil, .nil => rfl
  | _ :: _, .cons a A, .cons b B => congrArg (lvlLe a b && ·) (lvlsLe_tileMem A B)

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The all-secret levels over the types of `tileMem d` are those of `scalarTile d`. -/
theorem allSecret_tileMem : ∀ (cs : List (d.Ty ⊕ TileTy)),
    allSecret (d := tileMem d) cs = allSecret (d := scalarTile d) cs
  | [] => rfl
  | _ :: cs => by
      show HVector.cons SecretLevel.Secret (allSecret (d := tileMem d) cs)
        = HVector.cons SecretLevel.Secret (allSecret (d := scalarTile d) cs)
      rw [allSecret_tileMem cs]

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasLaneArr d] [HasBoolBit d] in
/-- The pointwise join of levels over the types of `tileMem d` is that of `scalarTile d`. -/
theorem lvlJoin_tileMem : ∀ {cs : List (d.Ty ⊕ TileTy)} (A B : Labels (d := scalarTile d) cs),
    lvlJoin (d := tileMem d) A B = lvlJoin (d := scalarTile d) A B
  | [], .nil, .nil => rfl
  | _ :: _, .cons a A, .cons b B => by
      show HVector.cons (a.join b) (lvlJoin (d := tileMem d) A B)
        = HVector.cons (a.join b) (lvlJoin (d := scalarTile d) A B)
      rw [lvlJoin_tileMem A B]

omit [DialectSignature d] [HasWord64 d] [HasLaneArr d] in
/-- The condition on the levels of an exit-flag loop body in `tileMem d` is that of
    `scalarTile d`. -/
theorem flagOk_tileMem {cs : List (d.Ty ⊕ TileTy)}
    (FB : Labels (d := scalarTile d) (HasBitType.bit (d := scalarTile d) :: cs))
    (A : Labels (d := scalarTile d) cs) :
    flagOk (d := tileMem d) FB A = flagOk (d := scalarTile d) FB A :=
  congrArg (decide (FB.head = .Public) && ·) (lvlsLe_tileMem d FB.tail A)

/-- **The inclusion keeps the result of the level checker.** -/
theorem embed_levelCheck' (M : LeakModel d) {Γ : Ctxt (scalarTile d)}
    {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts) (L : Labels Γ) :
    NFProg.levelCheck' (tileMemLeak d M) (embed d p) L
      = NFProg.levelCheck' (scalarTileLeak d M) p L := by
  induction p with
  | ret vs => with_unfolding_all exact congrArg some (retLvls_castArgs d L vs)
  | var e k ih =>
      simp only [embed, NFProg.levelCheck', embedExpr, ih]
      rw [argLvls_castArgs d L e.args]
      rfl
  | forLoop count inits body k ihb ihk =>
      simp only [embed, NFProg.levelCheck', ihb, ihk, hvAppend_tileMem, lvlsLe_tileMem,
        allSecret_tileMem]
      rw [lvlOf_castVar d count L, retLvls_castArgs d L inits]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [embed, NFProg.levelCheck', iht, ihe, ihk, hvAppend_tileMem, lvlJoin_tileMem]
      rw [lvlOf_castVar d cond L]
      rcases NFProg.levelCheck' (scalarTileLeak d M) thn L with _ | R₁ <;>
        rcases NFProg.levelCheck' (scalarTileLeak d M) els L with _ | R₂ <;> rfl
  | whileLoop inits body k ihb ihk =>
      simp only [embed, NFProg.levelCheck', ihb, ihk, hvAppend_tileMem, flagOk_tileMem,
        allSecret_tileMem]
      rw [retLvls_castArgs d L inits]
      rfl
  | call f args k => with_unfolding_all rfl

/-- An included program the level checker accepts in `scalarTile d` is constant time in
    `tileMem d` relative to its runs. -/
theorem embed_nfCTRel (D : DialectDenoteM d Option) (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt (scalarTile d)} {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts)
    (L : Labels Γ) (h : (NFProg.levelCheck' (scalarTileLeak d M) p L).isSome) :
    @NFCTRel (tileMem d) _ _ _ _ (tileMemDenote d D) (tileMemLeak d M) Γ ts L fuel
      (embed d p) :=
  tileMem_nfCTRel_of_levelCheck' d D M fuel _ L ((embed_levelCheck' d M p L).symm ▸ h)

end Bridge

/-! ## 7. The instance at `jasminDialect` -/

/-- The lane interface of `jasminDialect`: an element is a register `reg w`, an array a
    stack array `stackArr w N`, read by `stackGet` and written by `stackSet`, both at the
    position modulo `N`. -/
instance instHasLaneArrJasmin : HasLaneArr jasminDialect where
  elt w := JasminTy.reg w
  arr w N := JasminTy.stackArr w N
  toLane x := x
  ofLane x := x
  get a k := stackGet a k
  set a k v := stackSet a k v

/-- Reading a position whose residue differs from the residue of the written position gives
    the element of the array before the write. -/
theorem stackGet_stackSet_of_ne {w N : Nat} (a : Fin N → BitVec w) (k k' : Nat)
    (v : BitVec w) (h : k' % N ≠ k % N) : stackGet (stackSet a k v) k' = stackGet a k' := by
  cases N with
  | zero => rfl
  | succ m =>
      simp only [stackGet, stackSet]
      rw [ite_eq_right]
      intro hc
      exact h (congrArg Fin.val hc)

/-- Reading the written position of a non-empty array gives the written element. -/
theorem stackGet_stackSet_self {w N : Nat} (hN : 0 < N) (a : Fin N → BitVec w) (k : Nat)
    (v : BitVec w) : stackGet (stackSet a k v) k = v := by
  cases N with
  | zero => exact absurd hN (Nat.lt_irrefl 0)
  | succ m => simp only [stackGet, stackSet, ite_true]

/-- Folding writes at the positions `i + j` over a list of lanes none of whose positions has
    the residue of `k` leaves the element at `k` unchanged. -/
theorem stackGet_foldl_stackSet_of_ne {L w N : Nat} (i : Nat) (t : Fin L → BitVec w)
    (k : Nat) :
    ∀ (l : List (Fin L)) (a : Fin N → BitVec w), (∀ j ∈ l, (i + j.val) % N ≠ k % N) →
      stackGet (l.foldl (fun acc j => stackSet acc (i + j.val) (t j)) a) k = stackGet a k
  | [], _, _ => rfl
  | j :: l, a, h => by
      rw [List.foldl_cons,
        stackGet_foldl_stackSet_of_ne i t k l _
          (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')),
        stackGet_stackSet_of_ne _ _ _ _ (h j List.mem_cons_self).symm]

/-- For `L ≤ N` the positions `i + j` of the lanes `j < L` have distinct residues modulo
    `N`. -/
theorem lane_residue_inj {L N : Nat} (hL : L ≤ N) (i : Nat) {j j' : Fin L}
    (h : (i + j.val) % N = (i + j'.val) % N) : j = j' :=
  Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' i h)
    (Nat.lt_of_lt_of_le j.isLt hL) (Nat.lt_of_lt_of_le j'.isLt hL))

/-- For `L ≤ N`, folding writes at the positions `i + j` over a list of distinct lanes that
    contains `j` leaves lane `j` of the tile at position `i + j`. -/
theorem stackGet_foldl_stackSet_of_mem {L w N : Nat} (hL : L ≤ N) (i : Nat)
    (t : Fin L → BitVec w) (j : Fin L) :
    ∀ (l : List (Fin L)) (a : Fin N → BitVec w), l.Nodup → j ∈ l →
      stackGet (l.foldl (fun acc j => stackSet acc (i + j.val) (t j)) a) (i + j.val) = t j
  | [], _, _, hm => absurd hm List.not_mem_nil
  | j' :: l, a, hnd, hm => by
      rw [List.foldl_cons]
      by_cases hj : j' = j
      · subst hj
        rw [stackGet_foldl_stackSet_of_ne i t _ l _
            (fun j'' hj'' hc =>
              (List.nodup_cons.mp hnd).1
                ((lane_residue_inj hL i hc : j'' = j') ▸ hj'')),
          stackGet_stackSet_self (Nat.lt_of_lt_of_le j'.pos hL)]
      · exact stackGet_foldl_stackSet_of_mem hL i t j l _ (List.nodup_cons.mp hnd).2
          ((List.mem_cons.mp hm).resolve_left (Ne.symm hj))

/-- `laneLoad` at a stack array. -/
abbrev jasminLaneLoad (L : Nat) {w N : Nat} (a : Fin N → BitVec w) (i : Nat) :
    Fin L → BitVec w :=
  @laneLoad jasminDialect _ instHasLaneArrJasmin L w N a i

/-- `laneStore` at a stack array. -/
abbrev jasminLaneStore {L w N : Nat} (a : Fin N → BitVec w) (i : Nat)
    (t : Fin L → BitVec w) : Fin N → BitVec w :=
  @laneStore jasminDialect _ instHasLaneArrJasmin L w N a i t

/-- Lane `j` of a load from a stack array at `i` is `stackGet` at `i + j`. -/
theorem jasmin_laneLoad_apply (L : Nat) {w N : Nat} (a : Fin N → BitVec w) (i : Nat)
    (j : Fin L) :
    jasminLaneLoad L a i j = stackGet a (i + j.val) := rfl

/-- A store to a stack array is the fold of `stackSet` over the lanes, lane `0` first. -/
theorem jasmin_laneStore_eq {L w N : Nat} (a : Fin N → BitVec w) (i : Nat)
    (t : Fin L → BitVec w) :
    jasminLaneStore a i t
      = (List.finRange L).foldl (fun acc j => stackSet acc (i + j.val) (t j)) a := rfl

/-- **Frame of a lane store.** A store of `L` lanes at `i` leaves the element at every
    position `k` whose residue modulo `N` is none of the residues of `i, …, i + L - 1`. -/
theorem jasmin_laneStore_outside {L w N : Nat} (a : Fin N → BitVec w) (i : Nat)
    (t : Fin L → BitVec w) (k : Nat) (h : ∀ j : Fin L, (i + j.val) % N ≠ k % N) :
    stackGet (jasminLaneStore a i t) k = stackGet a k :=
  stackGet_foldl_stackSet_of_ne i t k _ a (fun j _ => h j)

/-- **Read-back of a lane store.** For `L ≤ N`, after a store of `L` lanes at `i` the
    element at position `i + j` is lane `j`. -/
theorem jasmin_laneStore_inside {L w N : Nat} (hL : L ≤ N) (a : Fin N → BitVec w) (i : Nat)
    (t : Fin L → BitVec w) (j : Fin L) :
    stackGet (jasminLaneStore a i t) (i + j.val) = t j :=
  stackGet_foldl_stackSet_of_mem hL i t j _ a (List.nodup_finRange L) (List.mem_finRange j)

/-- The frame of a lane store at an entry of the array: an entry `p` that is none of the
    residues of `i, …, i + L - 1` is unchanged. -/
theorem jasmin_laneStore_apply_of_ne {L w N : Nat} (a : Fin N → BitVec w) (i : Nat)
    (t : Fin L → BitVec w) (p : Fin N) (h : ∀ j : Fin L, (i + j.val) % N ≠ p.val) :
    jasminLaneStore a i t p = a p := by
  rw [← JasminDialect.stackGet_id (jasminLaneStore a i t) p, ← JasminDialect.stackGet_id a p]
  exact jasmin_laneStore_outside a i t p.val
    (fun j => by rw [Nat.mod_eq_of_lt p.isLt]; exact h j)

/-- For `L ≤ N`, a load of `L` lanes at `i` after a store of `L` lanes at `i` returns the
    stored tile. -/
theorem jasmin_laneLoad_laneStore {L w N : Nat} (hL : L ≤ N) (a : Fin N → BitVec w) (i : Nat)
    (t : Fin L → BitVec w) :
    jasminLaneLoad L (jasminLaneStore a i t) i = t :=
  funext fun j => jasmin_laneStore_inside hL a i t j

/-- The bridge operations over `jasminDialect`. -/
abbrev jasminBridge : Dialect := bridge jasminDialect

instance : DialectSignature jasminBridge := instDialectSignatureBridge jasminDialect
instance : DialectDenote jasminBridge := instDialectDenoteBridge jasminDialect

/-- The operation sum of `jasminTileDialect` and the bridge operations. -/
abbrev jasminTileMem : Dialect := tileMem jasminDialect

instance : DialectSignature jasminTileMem := instDialectSignatureTileMem jasminDialect
instance : HasWord64 jasminTileMem := instHasWord64TileMem jasminDialect
instance : HasBoolBit jasminTileMem := instHasBoolBitTileMem jasminDialect
instance : CallDenote jasminTileMem := instCallDenoteTileMem jasminDialect

/-- The denotation of `jasminTileMem`: every summand is total. -/
@[instance_reducible] def jasminTileMemDenote : DialectDenoteM jasminTileMem Option :=
  tileMemDenote jasminDialect (instDialectDenoteMOptionOfPure jasminDialect)

/-- `tileLoad` over `jasminDialect` returns the tile whose lane `j` is `stackGet` at the
    index plus `j`. -/
theorem jasmin_tileLoad_denote (L w N : Nat) (a : Fin N → BitVec w) (i : BitVec 64) :
    jasminTileMemDenote.denoteM (.inr (.tileLoad L w N))
        (.cons a (.cons i .nil))
      = some (fun j : Fin L => stackGet a (i.toNat + j.val)) := rfl

/-- `tileStore` over `jasminDialect` returns the fold of `stackSet` over the lanes from the
    index. -/
theorem jasmin_tileStore_denote (L w N : Nat) (a : Fin N → BitVec w) (i : BitVec 64)
    (t : Fin L → BitVec w) :
    jasminTileMemDenote.denoteM (.inr (.tileStore L w N))
        (.cons a (.cons i (.cons t .nil)))
      = some (jasminLaneStore a i.toNat t) := rfl

/-- `tileSplat` over `jasminDialect` returns the tile with the register in every lane. -/
theorem jasmin_tileSplat_denote (L w : Nat) (x : BitVec w) :
    jasminTileMemDenote.denoteM (.inr (.tileSplat L w))
        (.cons x .nil)
      = some (fun _ : Fin L => x) := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.TileBridge
