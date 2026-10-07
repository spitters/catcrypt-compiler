/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproductLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakM

/-!
# Structured programs over a scalar dialect and `tileDialect`

For a scalar dialect `d`, `scalarTile d` is the coproduct `Dialect.sum d tileDialect`: the
operations and types of `d` in the left summand and the lane operations and tile types of
`tileDialect` in the right summand. The trip counter, the branch bit and the call environment
that `NFProg` requires are those of `d`, so a program of `NFProg (scalarTile d)` has counted
loops and branches over scalars of `d` with tile values among its variables and carried
tuples. Its denotation `scalarTileDenP` takes an `Option`-valued denotation of `d`; an
operation of `tileDialect` is total.

`tileLeakModel` is the leakage model of `tileDialect`: every operation is quiet. A tile is a
value held in lane registers, and no operation of the dialect addresses memory or branches;
the gather `tilePermute` selects among the lanes of a value. The quiet class is a modelling
choice of this level: a lowering of a tile operation to a target states, as its own leakage
relation, that the instructions it emits have events that do not depend on the lanes.
`scalarTileLeak M` is the coproduct of a leakage model `M` of `d` with `tileLeakModel`, and
the level checker `NFProg.levelCheck'` at it is sound (`scalarTile_nfCTRel_of_levelCheck'`).

`nfTileDialect` and `jasminTileDialect` are the instances at `nfDialect` and `jasminDialect`.

## Main definitions

* `scalarTile`, `scalarTileDenote`, `scalarTileDenP` — the coproduct, its denotation over a
  denotation of the scalar summand, and the denotation of its programs.
* `tileValNat`, `tileLeakModel` — the leakage model of `tileDialect`.
* `scalarTileLeak`, `scalarTileLeakRun` — the leakage model and the leakage run of the
  coproduct.
* `nfTileDialect`, `nfTileDenote`, `jasminTileDialect`, `jasminTileDenote` — the instances.
* `tileAccLoop` — a counted loop that adds a tile to a carried tile on each trip.

## Main results

* `tile_opLeak`, `tile_ctLeak` — an operation and a straight-line program of `tileDialect`
  emit no event.
* `scalarTile_opLeak_inl`, `scalarTile_opLeak_inr` — in the coproduct a scalar operation
  emits its events of `d`, and a tile operation emits none.
* `scalarTile_nfCTRel_of_levelCheck'` — a program the level checker accepts is constant
  time relative to its runs.
* `tileAccLoop_denote`, `tileAccLoop_levelCheck`, `tileAccLoop_nfCTRel` — the denotation of
  the loop at every trip count, lane count and width, and its acceptance by the checker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## 1. The leakage model of `tileDialect` -/

/-- The natural-number reading of a tile: its lanes as the digits of a number in base
    `2 ^ w`, lane `0` least significant. -/
def tileValNat : (t : TileTy) → ⟦t⟧ → Nat
  | .tile n w, a => (List.finRange n).foldr (fun i acc => (a i).toNat + 2 ^ w * acc) 0

/-- The leakage model of `tileDialect`: every operation is quiet. -/
def tileLeakModel : LeakModel tileDialect where
  kind := fun _ => .quiet
  valNat := tileValNat

/-- Every operation of `tileDialect` has the quiet class. -/
@[simp] theorem tileLeakModel_kind (op : TileOp) : tileLeakModel.kind op = .quiet := rfl

/-- An operation of `tileDialect` emits no event. -/
theorem tile_opLeak (op : TileOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := tileDialect) op)) :
    opLeak tileLeakModel op vals = [] := rfl

/-- The level checker places no constraint on an operation of `tileDialect`. -/
theorem tile_opAccepts (op : TileOp) (ls : List SecretLevel) :
    opAccepts tileLeakModel op ls = true := rfl

/-- A straight-line program of `tileDialect` emits no event. -/
theorem tile_ctLeak : ∀ {Γ : Ctxt tileDialect} {t : TileTy} (c : Com tileDialect Γ t)
    (V : Valuation Γ), Com.ctLeak tileLeakModel c V = []
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V => by
      show Expr.ctLeak tileLeakModel e V ++ _ = []
      rw [tile_ctLeak body]; rfl

/-! ## 2. The coproduct with a scalar dialect -/

section Sum

variable (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]

/-- The coproduct of the scalar dialect `d` and `tileDialect`. -/
abbrev scalarTile : Dialect.{0, 0} := Dialect.sum d tileDialect

instance instDialectSignatureScalarTile : DialectSignature (scalarTile d) :=
  instDialectSignatureSum (d := d) (e := tileDialect)

/-- The trip counter of `scalarTile d` is the counter of `d`. -/
instance instHasWord64ScalarTile [HasWord64 d] : HasWord64 (scalarTile d) where
  word := .inl (HasWord64.word (d := d))
  toNat := HasWord64.toNat (d := d)
  ofNat := HasWord64.ofNat (d := d)

/-- The bit of `scalarTile d` is the bit of `d`. -/
instance instHasBoolBitScalarTile [HasBoolBit d] : HasBoolBit (scalarTile d) where
  bit := .inl (HasBitType.bit (d := d))
  toBool := HasBoolBit.toBool (d := d)

/-- `scalarTile d` denotes calls in the empty environment. -/
instance instCallDenoteScalarTile : CallDenote (scalarTile d) := ⟨.empty⟩

/-- The denotation of `scalarTile d` over the denotation `D` of `d`: an operation of the
    left summand by `D`, an operation of the right summand by its total denotation. -/
@[instance_reducible] def scalarTileDenote (D : DialectDenoteM d Option) :
    DialectDenoteM (scalarTile d) Option where
  denoteM
    | .inl o, args => D.denoteM o (unmapInl args)
    | .inr o, args => some (DialectDenote.denote o (unmapInr args))

/-- The leakage model of `scalarTile d`: the coproduct of a model `M` of `d` and
    `tileLeakModel`. -/
def scalarTileLeak (M : LeakModel d) : LeakModel (scalarTile d) := sumLeak M tileLeakModel

/-- An operation of the left summand has the class `M` gives it. -/
@[simp] theorem scalarTileLeak_kind_inl (M : LeakModel d) (op : d.Op) :
    (scalarTileLeak d M).kind (.inl op) = M.kind op := rfl

/-- An operation of the right summand is quiet. -/
@[simp] theorem scalarTileLeak_kind_inr (M : LeakModel d) (op : TileOp) :
    (scalarTileLeak d M).kind (.inr op) = .quiet := rfl

/-- A scalar operation emits in the coproduct the events it emits in `d`. -/
theorem scalarTile_opLeak_inl (M : LeakModel d) (op : d.Op)
    (vals : HVector (fun t => ⟦t⟧)
      ((DialectSignature.sig op).map (Sum.inl (β := TileTy)))) :
    opLeak (scalarTileLeak d M) (.inl op) vals = opLeak M op (unmapInl (e := tileDialect) vals) :=
  opLeak_inl M tileLeakModel op vals

/-- A tile operation emits no event in the coproduct. -/
theorem scalarTile_opLeak_inr (M : LeakModel d) (op : TileOp)
    (vals : HVector (fun t => ⟦t⟧)
      ((DialectSignature.sig (d := tileDialect) op).map (Sum.inr (α := d.Ty)))) :
    opLeak (scalarTileLeak d M) (.inr op) vals = [] :=
  opLeak_inr_quiet M tileLeakModel op rfl vals

/-- The level checker places no constraint on a tile operation of the coproduct. -/
theorem scalarTile_opAccepts_inr (M : LeakModel d) (op : TileOp) (ls : List SecretLevel) :
    opAccepts (scalarTileLeak d M) (.inr op) ls = true := rfl

variable [HasWord64 d] [HasBoolBit d]

/-- The denotation of a program of `scalarTile d` over the denotation `D` of `d`. -/
abbrev scalarTileDenP (D : DialectDenoteM d Option) (fuel : Nat) {Γ : Ctxt (scalarTile d)}
    {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts) (V : Valuation Γ) :
    Option (Valuation ts) :=
  @NFProg.denote (scalarTile d) _ _ _ _ (scalarTileDenote d D) _ fuel Γ ts p V

/-- The leakage run of a program of `scalarTile d` over the denotation `D` and the leakage
    model `M` of `d`. -/
abbrev scalarTileLeakRun (D : DialectDenoteM d Option) (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt (scalarTile d)} {ts : List (scalarTile d).Ty} (p : NFProg (scalarTile d) Γ ts)
    (V : Valuation Γ) : Option (Valuation ts × List CTLeak) :=
  @NFProg.leakRunM (scalarTile d) _ _ _ _ (scalarTileDenote d D) (scalarTileLeak d M) fuel
    _ _ p V

/-- **The level checker on `scalarTile d`.** A program the checker `levelCheck'` accepts at
    `scalarTileLeak d M` for the entry labels `L` is constant time for `L` relative to the
    runs that succeed, over every denotation of `d`. -/
theorem scalarTile_nfCTRel_of_levelCheck' (D : DialectDenoteM d Option) (M : LeakModel d)
    (fuel : Nat) {Γ : Ctxt (scalarTile d)} {ts : List (scalarTile d).Ty}
    (p : NFProg (scalarTile d) Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' (scalarTileLeak d M) p L).isSome) :
    @NFCTRel (scalarTile d) _ _ _ _ (scalarTileDenote d D) (scalarTileLeak d M) Γ ts L fuel p :=
  @NFProg.nfCTRel_of_levelCheck' (scalarTile d) _ _ _ _ (scalarTileDenote d D)
    (scalarTileLeak d M) fuel Γ ts p L h

/-! ## 3. A counted loop over tiles -/

/-- The counted loop that adds the tile `x` to a carried tile once per trip. The context is
    `[count, x, a]`: the trip count, a scalar of `d`, and two tiles of `n` lanes of `w` bits.
    The body adds `x` to the carried tile with `tileBin .add`. -/
def tileAccLoop (n w : Nat) :
    NFProg (scalarTile d)
      [.inl (HasWord64.word (d := d)), .inr (.tile n w), .inr (.tile n w)]
      [.inr (.tile n w)] :=
  NFProg.forLoop (d := scalarTile d) (cs := [.inr (.tile n w)])
    (Γ := [.inl (HasWord64.word (d := d)), .inr (.tile n w), .inr (.tile n w)])
    .here (.cons (.there (.there .here)) .nil)
    (.var ⟨.inr (.tileBin .add n w), rfl,
        .cons .here (.cons (.there (.there (.there .here))) .nil)⟩
      (.ret (.cons .here .nil)))
    (.ret (.cons .here .nil))

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] in
/-- Folding over `m` indices a step that adds the tile `x` to a carried one-tile tuple adds
    `m` copies of `x` in every lane. -/
theorem foldlM_range_tileAdd {n w : Nat} (x : Fin n → BitVec w)
    (f : Valuation (d := scalarTile d) [.inr (.tile n w)] → Nat →
      Option (Valuation (d := scalarTile d) [.inr (.tile n w)]))
    (hf : ∀ (a : Fin n → BitVec w) (i : Nat),
      f (.cons a .nil) i = some (.cons (fun j => a j + x j) .nil)) :
    (m : Nat) → (a : Fin n → BitVec w) →
    (List.range m).foldlM f (.cons a .nil)
      = some (.cons (fun j => a j + BitVec.ofNat w m * x j) .nil)
  | 0, a => by simp
  | m + 1, a => by
      rw [List.range_succ, List.foldlM_append, foldlM_range_tileAdd x f hf m a]
      simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil, hf]
      show some _ = some _
      congr 2
      funext j
      rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.add_assoc]
      simp

/-- `tileAccLoop d n w` at the trip count `cnt`, the tile `x` and the start tile `a` returns
    the tile with lane `j` equal to `a j + cnt * x j` in `BitVec w`, at every fuel, lane
    count and width, over every denotation of `d`. -/
theorem tileAccLoop_denote (D : DialectDenoteM d Option) (n w : Nat)
    (cnt : ⟦HasWord64.word (d := d)⟧) (x a : Fin n → BitVec w) (fuel : Nat) :
    scalarTileDenP d D fuel (tileAccLoop d n w) (.cons cnt (.cons x (.cons a .nil)))
      = some (.cons
          (fun j => a j + BitVec.ofNat w (HasWord64.toNat (d := d) cnt) * x j) .nil) := by
  unfold scalarTileDenP tileAccLoop
  erw [@NFProg.denote_forLoop (scalarTile d) _ _ _ _ (scalarTileDenote d D) _]
  erw [foldlM_range_tileAdd d x _ (fun a i => rfl)]
  rfl

/-- The level checker accepts `tileAccLoop d n w` at a public trip count and every level of
    the two tiles, over every leakage model of `d`. -/
theorem tileAccLoop_levelCheck (M : LeakModel d) (n w : Nat) (lx la : SecretLevel) :
    (NFProg.levelCheck' (scalarTileLeak d M) (tileAccLoop d n w)
      (.cons .Public (.cons lx (.cons la .nil)))).isSome := by
  cases lx <;> cases la <;> rfl

/-- `tileAccLoop d n w` is constant time at a public trip count and every level of the two
    tiles, relative to its runs. -/
theorem tileAccLoop_nfCTRel (D : DialectDenoteM d Option) (M : LeakModel d) (n w : Nat)
    (lx la : SecretLevel) (fuel : Nat) :
    @NFCTRel (scalarTile d) _ _ _ _ (scalarTileDenote d D) (scalarTileLeak d M) _ _
      (.cons .Public (.cons lx (.cons la .nil))) fuel (tileAccLoop d n w) :=
  scalarTile_nfCTRel_of_levelCheck' d D M fuel _ _ (tileAccLoop_levelCheck d M n w lx la)

end Sum

/-! ## 4. The instances at `nfDialect` and `jasminDialect` -/

/-- The coproduct of `nfDialect` and `tileDialect`. -/
abbrev nfTileDialect : Dialect := scalarTile nfDialect

instance : DialectSignature nfTileDialect := instDialectSignatureScalarTile nfDialect
instance : HasWord64 nfTileDialect := instHasWord64ScalarTile nfDialect
instance : HasBoolBit nfTileDialect := instHasBoolBitScalarTile nfDialect
instance : CallDenote nfTileDialect := instCallDenoteScalarTile nfDialect

/-- The denotation of `nfTileDialect` at the leaf table `T`. -/
@[instance_reducible] def nfTileDenote (T : NfLeafTable) : DialectDenoteM nfTileDialect Option :=
  scalarTileDenote nfDialect (nfDenote T)

/-- The coproduct of `jasminDialect` and `tileDialect`. -/
abbrev jasminTileDialect : Dialect := scalarTile jasminDialect

instance : DialectSignature jasminTileDialect := instDialectSignatureScalarTile jasminDialect
instance : HasWord64 jasminTileDialect := instHasWord64ScalarTile jasminDialect
instance : HasBoolBit jasminTileDialect := instHasBoolBitScalarTile jasminDialect
instance : CallDenote jasminTileDialect := instCallDenoteScalarTile jasminDialect

/-- The denotation of `jasminTileDialect`: both summands are total. -/
@[instance_reducible] def jasminTileDenote : DialectDenoteM jasminTileDialect Option :=
  scalarTileDenote jasminDialect (instDialectDenoteMOptionOfPure jasminDialect)

/-- `tileAccLoop` over `nfDialect`: the trip count is a 64-bit word, and lane `j` of the
    result is `a j + cnt * x j`. -/
theorem tileAccLoop_nf_denote (T : NfLeafTable) (n w : Nat) (cnt : BitVec 64)
    (x a : Fin n → BitVec w) (fuel : Nat) :
    scalarTileDenP nfDialect (nfDenote T) fuel (tileAccLoop nfDialect n w)
        (.cons cnt (.cons x (.cons a .nil)))
      = some (.cons (fun j => a j + BitVec.ofNat w cnt.toNat * x j) .nil) :=
  tileAccLoop_denote nfDialect (nfDenote T) n w cnt x a fuel

end CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
