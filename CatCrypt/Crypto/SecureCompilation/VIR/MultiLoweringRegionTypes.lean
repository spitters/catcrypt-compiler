/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMapMulti
public import CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin

/-!
# Setting the region types of a multi-value lowering

`NFProg.mapM L` needs `RegionTypesM L`: the trip-counter type and the bit type of the source
dialect are each represented by one register of the corresponding target type. A lowering
built for straight-line code may represent them otherwise (`towerToField` sends both to
`[]`). When no op signature or return type mentions either type (`OpTypesAvoid d IsRegionTy`),
`L.withRegionTypes hw` is the lowering with the same op blocks whose type map sends the
trip-counter type to `[HasWord64.word]`, the bit type to `[HasBitType.bit]` and every other
type `t` to `L.mapTys t`. A `RegionValCodec d d'` encodes the values of the two types; its
encoding `regionEnc C enc` is the codec on them and `enc` elsewhere.

The witness is `towerSqLoop p β`, the counted loop of `n` squarings in `Fp2` carrying one
`fp2` value, lowered by `mapM` along `(towerToLimbs P).withRegionTypes` to `jasminDialect`.

## Main definitions

* `IsRegionTy`, `OpTypesAvoid`: the region types of a dialect, and the condition that no op
  mentions a type satisfying a predicate.
* `regionMapTys`, `RegionValCodec`, `regionEnc`: the type map with the region types set,
  the encoding of region values, and the resulting encoding.
* `MultiBlockLoweringData.withRegionTypes`: the lowering with the region types set.
* `castRetM`: a multi-result program carried along an equality of result types.
* `towerAvoid`, `towerJasminCodec`, `towerLimbsR`, `towerLimbsREnc`: the hypothesis, the
  codec, the lowering and the encoding for `towerToLimbs P`.
* `sqIter`, `towerSqLoop`, `towerSqLoopLimbs`: the `n`-fold square in `Fp2`, the counted loop
  of `Fp2` squarings and its lowering to limbs.

## Main results

* `withRegionTypes_blockSquare`, `withRegionTypes_fundamental`: the block square and the
  whole-program square of `L.withRegionTypes hw` from the block square of `L`.
* `regionTypesM_withRegionTypes`, `regionTransportsM_withRegionTypes`: the region conditions
  of `mapM` for `L.withRegionTypes hw`.
* `withRegionTypes_mapM_denote`: preservation of `mapM` along `L.withRegionTypes hw`.
* `towerSqLoop_denote_src`: the source loop computes the `n`-fold square.
* `towerSqLoop_denote`: the lowered loop maps the encoding of `(n, x)` to the encoding of the
  `n`-fold square of `x`, at every fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering
open FieldDialectBlockDescent (pullV)
open BlockLoweringCPS (castHom)

namespace MultiBlockLowering

/-! ## 1. Region types and the type map -/

section RegionTys

variable {d d' : Dialect.{0, 0}} [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
  [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- The region types of `d`: the trip-counter type and the bit type. -/
def IsRegionTy (t : d.Ty) : Prop :=
  t = HasWord64.word (d := d) ∨ t = HasBitType.bit (d := d)

/-- No op signature or return type of `d` contains a type satisfying `P`. -/
def OpTypesAvoid (d : Dialect) [DialectSignature d] (P : d.Ty → Prop) : Prop :=
  ∀ op : d.Op, (∀ t ∈ DialectSignature.sig op, ¬ P t) ∧ ¬ P (DialectSignature.ret op)

variable [DecidableEq d.Ty]

/-- The type map `m` with the trip-counter type sent to `[HasWord64.word]` and the bit type
    to `[HasBitType.bit]`. -/
def regionMapTys (m : d.Ty → List d'.Ty) (t : d.Ty) : List d'.Ty :=
  if t = HasWord64.word (d := d) then [HasWord64.word (d := d')]
  else if t = HasBitType.bit (d := d) then [HasBitType.bit (d := d')] else m t

/-- `regionMapTys` sends the trip-counter type to `[HasWord64.word]`. -/
theorem regionMapTys_word (m : d.Ty → List d'.Ty) :
    regionMapTys m (HasWord64.word (d := d)) = [HasWord64.word (d := d')] :=
  if_pos rfl

/-- `regionMapTys` sends the bit type to `[HasBitType.bit]` when it differs from the
    trip-counter type. -/
theorem regionMapTys_bit (m : d.Ty → List d'.Ty)
    (hwb : HasBitType.bit (d := d) ≠ HasWord64.word (d := d)) :
    regionMapTys m (HasBitType.bit (d := d)) = [HasBitType.bit (d := d')] := by
  rw [regionMapTys, if_neg hwb, if_pos rfl]

/-- `regionMapTys m` agrees with `m` off the region types. -/
theorem regionMapTys_of_not (m : d.Ty → List d'.Ty) {t : d.Ty} (h : ¬ IsRegionTy t) :
    regionMapTys m t = m t := by
  rw [regionMapTys, if_neg (fun hw => h (Or.inl hw)), if_neg (fun hb => h (Or.inr hb))]

/-- The flattening by `regionMapTys m` of a context free of region types is the flattening
    by `m`. -/
theorem ctxFlat_regionMapTys (m : d.Ty → List d'.Ty) :
    ∀ (Γ : List d.Ty), (∀ t ∈ Γ, ¬ IsRegionTy t) → ctxFlat (regionMapTys m) Γ = ctxFlat m Γ
  | [], _ => rfl
  | t :: Γ, h => by
      show regionMapTys m t ++ ctxFlat (regionMapTys m) Γ = m t ++ ctxFlat m Γ
      rw [regionMapTys_of_not m (h t List.mem_cons_self),
        ctxFlat_regionMapTys m Γ (fun s hs => h s (List.mem_cons_of_mem t hs))]

end RegionTys

/-! ## 2. Casts of multi-result programs and appended valuations -/

section Casts

variable {d : Dialect} [DialectSignature d] [TyDenote d.Ty]

/-- A multi-result program with its result types carried along an equality. -/
def castRetM {Γ : Ctxt d} {ts ts' : List d.Ty} (h : ts = ts') (m : MultiReturnCom d Γ ts) :
    MultiReturnCom d Γ ts' :=
  h ▸ m

/-- A multi-result program with its result types carried denotes the carried results. -/
theorem denote_castRetM [DialectDenote d] {Γ : Ctxt d} {ts ts' : List d.Ty} (h : ts = ts')
    (m : MultiReturnCom d Γ ts) (V : Valuation Γ) :
    (castRetM h m).denote V = NFProg.castVal h (m.denote V) := by
  subst h
  rfl

omit [DialectSignature d] in
/-- Carrying a valuation along an equality of a context with itself is the identity. -/
theorem castVal_self {A : Ctxt d} (h : A = A) (X : Valuation A) : NFProg.castVal h X = X :=
  rfl

omit [DialectSignature d] in
/-- Appending two carried valuations is carrying their append. -/
theorem hvAppend_castVal {A A' B B' : Ctxt d} (h₁ : A = A') (h₂ : B = B') (X : Valuation A)
    (Y : Valuation B) :
    hvAppend (NFProg.castVal h₁ X) (NFProg.castVal h₂ Y) =
      NFProg.castVal (congrArg₂ (· ++ ·) h₁ h₂) (hvAppend X Y) := by
  subst h₁ h₂
  rfl

end Casts

/-! ## 3. The lowering with the region types set -/

section WithRegionTypes

variable {d d' : Dialect.{0, 0}} [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
  [DecidableEq d.Ty] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- **The encoding of the region values.** `encWord` sends a source trip counter to a
    target trip counter with the same trip count and the trip indices to the trip indices;
    `encBit` sends a source bit to a target bit with the same reading. -/
structure RegionValCodec (d d' : Dialect.{0, 0}) [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
    [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d'] where
  /-- The encoding of a trip counter. -/
  encWord : ⟦HasWord64.word (d := d)⟧ → ⟦HasWord64.word (d := d')⟧
  /-- The encoding of a bit. -/
  encBit : ⟦HasBitType.bit (d := d)⟧ → ⟦HasBitType.bit (d := d')⟧
  /-- An encoded counter denotes the same trip count. -/
  toNat_encWord : ∀ x, HasWord64.toNat (d := d') (encWord x) = HasWord64.toNat (d := d) x
  /-- The encoded trip index is the trip index. -/
  encWord_ofNat : ∀ i, encWord (HasWord64.ofNat (d := d) i) = HasWord64.ofNat (d := d') i
  /-- An encoded bit reads as the same `Bool`. -/
  toBool_encBit : ∀ b, HasBoolBit.toBool (d := d') (encBit b) = HasBoolBit.toBool (d := d) b

/-- **The encoding with the region types set**: the codec at the trip-counter type and at
    the bit type, `enc` elsewhere. -/
def regionEnc (C : RegionValCodec d d') {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) {t : d.Ty} (x : ⟦t⟧) :
    Valuation (regionMapTys m t) :=
  if hw : t = HasWord64.word (d := d) then
    NFProg.castVal (by rw [hw, regionMapTys_word])
      (.cons (C.encWord (NFProg.tyCast hw x)) .nil)
  else if hb : t = HasBitType.bit (d := d) then
    NFProg.castVal (by rw [regionMapTys, if_neg hw, if_pos hb])
      (.cons (C.encBit (NFProg.tyCast hb x)) .nil)
  else NFProg.castVal (regionMapTys_of_not m (fun h => h.elim hw hb)).symm (enc x)

/-- `regionEnc` at the trip-counter type. -/
theorem regionEnc_word (C : RegionValCodec d d') {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) (x : ⟦HasWord64.word (d := d)⟧) :
    regionEnc C enc x = NFProg.castVal (regionMapTys_word m).symm (.cons (C.encWord x) .nil) := by
  rw [regionEnc, dif_pos rfl]
  rfl

/-- `regionEnc` at the bit type. -/
theorem regionEnc_bit (C : RegionValCodec d d') {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t))
    (hwb : HasBitType.bit (d := d) ≠ HasWord64.word (d := d)) (b : ⟦HasBitType.bit (d := d)⟧) :
    regionEnc C enc b =
      NFProg.castVal (regionMapTys_bit m hwb).symm (.cons (C.encBit b) .nil) := by
  rw [regionEnc, dif_neg hwb, dif_pos rfl]
  rfl

/-- `regionEnc` off the region types. -/
theorem regionEnc_of_not (C : RegionValCodec d d') {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) {t : d.Ty} (h : ¬ IsRegionTy t) (x : ⟦t⟧) :
    regionEnc C enc x = NFProg.castVal (regionMapTys_of_not m h).symm (enc x) := by
  rw [regionEnc, dif_neg (fun hw => h (Or.inl hw)), dif_neg (fun hb => h (Or.inr hb))]

/-- The flattened `regionEnc` encoding of a valuation free of region types is the carried
    flattened `enc` encoding. -/
theorem flatVal_regionEnc (C : RegionValCodec d d') {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) :
    ∀ {Γ : Ctxt d} (h : ∀ t ∈ Γ, ¬ IsRegionTy t) (V : Valuation Γ),
      flatVal (regionEnc C enc) V =
        NFProg.castVal (ctxFlat_regionMapTys m Γ h).symm (flatVal enc V)
  | [], _, .nil => rfl
  | t :: Γ, h, .cons x V => by
      show hvAppend (regionEnc C enc x) (flatVal (regionEnc C enc) V) = _
      rw [regionEnc_of_not C enc (h t List.mem_cons_self),
        flatVal_regionEnc C enc (fun s hs => h s (List.mem_cons_of_mem t hs)) V,
        hvAppend_castVal]
      rfl

variable [DialectSignature d] [DialectSignature d']

/-- **The lowering with the region types set.** The type map is `regionMapTys L.mapTys`; the
    block of an op is the block of `L`, carried along the agreement of the two type maps on
    the op's signature and return type. -/
@[reducible] def MultiBlockLoweringData.withRegionTypes (L : MultiBlockLoweringData d d')
    (hw : OpTypesAvoid d IsRegionTy) : MultiBlockLoweringData d d' where
  mapTys := regionMapTys L.mapTys
  lowerOp op :=
    castRetM (regionMapTys_of_not L.mapTys (hw op).2).symm
      (MultiReturnCom.rename (castHom (ctxFlat_regionMapTys L.mapTys _ (hw op).1).symm)
        (L.lowerOp op))

variable [DialectDenote d] [DialectDenote d']

/-- **Block square of `L.withRegionTypes hw`** from the block square of `L`. -/
theorem withRegionTypes_blockSquare (L : MultiBlockLoweringData d d')
    (hw : OpTypesAvoid d IsRegionTy) (C : RegionValCodec d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good) :
    (L.withRegionTypes hw).BlockSquare (regionEnc C enc) Good := by
  intro Γ t e hg vals
  show (castRetM _ (MultiReturnCom.rename _ (L.lowerOp e.op))).denote _ = _
  rw [denote_castRetM, multiReturnCom_denote_rename,
    NFProg.pullV_castHom_symm (ctxFlat_regionMapTys L.mapTys _ (hw e.op).1),
    flatVal_regionEnc C enc (hw e.op).1, NFProg.castVal_castVal, castVal_self, hBlk e hg vals]
  exact (regionEnc_of_not C enc (hw e.op).2 _).symm

/-- **Fundamental theorem of `L.withRegionTypes hw`.** -/
theorem withRegionTypes_fundamental (L : MultiBlockLoweringData d d')
    (hw : OpTypesAvoid d IsRegionTy) (C : RegionValCodec d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (hc : BlockLoweringCPS.CoveredCom Good c)
    (V : Valuation Γ) :
    ((L.withRegionTypes hw).lowerMulti c).denote (flatVal (regionEnc C enc) V) =
      regionEnc C enc (c.denote V) :=
  (L.withRegionTypes hw).multiFundamental_on (regionEnc C enc) Good
    (withRegionTypes_blockSquare L hw C enc Good hBlk) c hc V

end WithRegionTypes

/-! ## 4. The region conditions and preservation -/

section Regions

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DecidableEq d.Ty] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d']
  [HasBoolBit d']

/-- The region types of `L.withRegionTypes hw`, for distinct trip-counter and bit types. -/
theorem regionTypesM_withRegionTypes (L : MultiBlockLoweringData d d')
    (hw : OpTypesAvoid d IsRegionTy) (hwb : HasBitType.bit (d := d) ≠ HasWord64.word (d := d)) :
    NFProg.RegionTypesM (L.withRegionTypes hw) where
  word_eq := regionMapTys_word L.mapTys
  bit_eq := regionMapTys_bit L.mapTys hwb

/-- The region transports of `L.withRegionTypes hw` at `regionEnc C enc`. -/
theorem regionTransportsM_withRegionTypes (L : MultiBlockLoweringData d d')
    (hw : OpTypesAvoid d IsRegionTy) (hwb : HasBitType.bit (d := d) ≠ HasWord64.word (d := d))
    (C : RegionValCodec d d') (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (L.mapTys t)) :
    NFProg.RegionTransportsM (L.withRegionTypes hw) (regionTypesM_withRegionTypes L hw hwb)
      (regionEnc C enc) where
  toNat_enc x := by
    show HasWord64.toNat (d := d') (NFProg.castVal _ (regionEnc C enc x)).head = _
    rw [regionEnc_word, NFProg.castVal_castVal]
    exact C.toNat_encWord x
  ofNat_enc i := by
    show regionEnc C enc _ = _
    rw [regionEnc_word, C.encWord_ofNat]
  toBool_enc b := by
    show HasBoolBit.toBool (d := d') (NFProg.castVal _ (regionEnc C enc b)).head = _
    rw [regionEnc_bit C enc hwb, NFProg.castVal_castVal]
    exact C.toBool_encBit b

variable [DialectDenote d] [DialectDenote d']

/-- **Preservation along `L.withRegionTypes hw`.** Under the `Good`-gated block square of `L`,
    a `Good`-covered program lowered by `mapM` along `L.withRegionTypes hw`, at a renaming
    relating `W` to the flattened `regionEnc` encoding of `V`, denotes at every fuel the
    flattened encoding of the source denotation. -/
theorem withRegionTypes_mapM_denote (L : MultiBlockLoweringData d d')
    (hw : OpTypesAvoid d IsRegionTy) (hwb : HasBitType.bit (d := d) ≠ HasWord64.word (d := d))
    (C : RegionValCodec d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good)
    {Δ : Ctxt d'} (ren : Ctxt.Hom ((L.withRegionTypes hw).mapCtx Γ) Δ) (V : Valuation Γ)
    (W : Valuation Δ) (hren : pullV ren W = flatVal (regionEnc C enc) V) :
    (NFProg.mapM (L.withRegionTypes hw) (regionTypesM_withRegionTypes L hw hwb) p ren).denote
        fuel W = (p.denote fuel V).map (flatVal (regionEnc C enc)) :=
  NFProg.mapM_denote (L.withRegionTypes hw) _ (regionEnc C enc) Good
    (withRegionTypes_blockSquare L hw C enc Good hBlk)
    (regionTransportsM_withRegionTypes L hw hwb C enc) fuel p hp ren V W hren

end Regions

end MultiBlockLowering

/-! ## 5. The witness: a counted loop of `Fp2` squarings lowered to limbs -/

namespace TowerLoopWitness

open TowerDialect TowerToLimbs JasminDialect NFProgJasmin FieldDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

/-- No tower op mentions `word` or `bit`. -/
theorem towerAvoid : OpTypesAvoid towerDialect IsRegionTy := by
  intro op
  rcases op with ⟨l⟩ | ⟨l⟩ | ⟨l⟩ | ⟨l⟩ | ⟨l⟩ | ⟨l⟩ | _ | _ | ⟨l⟩ | _ | _ | _ | _ <;>
    (try cases l) <;> refine ⟨?_, ?_⟩ <;>
    simp [IsRegionTy, DialectSignature.sig, DialectSignature.ret, HasWord64.word,
      HasBitType.bit]

/-- The `bit` and `word` types of the tower dialect differ. -/
theorem tower_bit_ne_word :
    HasBitType.bit (d := towerDialect) ≠ HasWord64.word (d := towerDialect) := by
  intro h
  cases h

/-- The region codec from the tower dialect to `jasminDialect`: a trip counter is the same
    64-bit word, a bit is `1#1` or `0#1`. -/
def towerJasminCodec : RegionValCodec towerDialect jasminDialect where
  encWord x := x
  encBit b := if b then 1#1 else 0#1
  toNat_encWord _ := rfl
  encWord_ofNat _ := rfl
  toBool_encBit b := by cases b <;> rfl

/-- The tower-to-limbs lowering with the trip counter on one `reg 64` register and the bit
    on one `reg 1` register. -/
@[reducible] def towerLimbsR {n : Nat} (P : LimbParams n) :
    MultiBlockLoweringData towerDialect jasminDialect :=
  (towerToLimbs P).withRegionTypes towerAvoid

/-- The encoding of `towerLimbsR P`. -/
def towerLimbsREnc {n : Nat} (P : LimbParams n) : (towerLimbsR P).Enc :=
  regionEnc towerJasminCodec (towerLimbEnc P)

/-- The `n`-fold square in `Fp2 = F_p[u]/(u² − β)`. -/
def sqIter (p : Nat) (β : Int) (n : Nat) (x : Fp2Val p) : Fp2Val p :=
  (fun y => Fp2Val.mulBeta (β : ZMod p) y y)^[n] x

/-- **The counted loop of `Fp2` squarings.** The context is `[n, x]`, the trip count and the
    start value; the loop carries one `fp2` value and squares it on each trip. -/
def towerSqLoop (p : Nat) (β : Int) :
    NFProg towerDialect [TowerTy.word, TowerTy.fp2 p β] [TowerTy.fp2 p β] :=
  NFProg.forLoop (d := towerDialect) (cs := [TowerTy.fp2 p β])
    (Γ := [TowerTy.word, TowerTy.fp2 p β]) .here (.cons (.there .here) .nil)
    (.var ⟨TowerOp.square .two p β 0, rfl, .cons .here .nil⟩ (.ret (.cons .here .nil)))
    (.ret (.cons .here .nil))

/-- Every op of `towerSqLoop p β` is at the modulus `p`. -/
theorem towerSqLoop_covered (p : Nat) (β : Int) : (towerSqLoop p β).Covered (TowerAt p) :=
  ⟨⟨rfl, trivial⟩, trivial⟩

/-- Folding the squaring step over `List.range m` from `y` gives the `m`-fold square. -/
theorem foldlM_range_sq (p : Nat) (β : Int)
    (f : Valuation (d := towerDialect) [TowerTy.fp2 p β] → Nat →
      Option (Valuation (d := towerDialect) [TowerTy.fp2 p β]))
    (hf : ∀ (y : Fp2Val p) i, f (.cons y .nil) i =
      some (.cons (Fp2Val.mulBeta (β : ZMod p) y y) .nil)) :
    ∀ (m : Nat) (y : Fp2Val p), (List.range m).foldlM f (.cons y .nil) =
      some (.cons (sqIter p β m y) .nil)
  | 0, _ => rfl
  | m + 1, y => by
      rw [List.range_succ, List.foldlM_append, foldlM_range_sq p β f hf m y]
      simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil, hf]
      rw [show sqIter p β (m + 1) y =
          Fp2Val.mulBeta (β : ZMod p) (sqIter p β m y) (sqIter p β m y) from
        Function.iterate_succ_apply' _ _ _]
      rfl

/-- **The source loop computes the `n`-fold square.** -/
theorem towerSqLoop_denote_src (p : Nat) (β : Int) (fuel : Nat) (w : BitVec 64)
    (x : Fp2Val p) :
    (towerSqLoop p β).denote fuel (.cons w (.cons x .nil)) =
      some (.cons (sqIter p β w.toNat x) .nil) := by
  rw [towerSqLoop, NFProg.denote_forLoop]
  erw [foldlM_range_sq p β _ (fun _ _ => rfl) w.toNat x]
  rfl

/-- The region types of `towerLimbsR P`. -/
theorem towerLimbsR_regionTypes {n : Nat} (P : LimbParams n) :
    NFProg.RegionTypesM (towerLimbsR P) :=
  regionTypesM_withRegionTypes (towerToLimbs P) towerAvoid tower_bit_ne_word

/-- **The loop of `Fp2` squarings lowered to limbs**: `towerSqLoop P.p β` lowered by `mapM`
    along `towerLimbsR P` into the flattened context. -/
def towerSqLoopLimbs {n : Nat} (P : LimbParams n) (β : Int) :
    NFProg jasminDialect ((towerLimbsR P).mapCtx [TowerTy.word, TowerTy.fp2 P.p β])
      ((towerLimbsR P).mapCtx [TowerTy.fp2 P.p β]) :=
  NFProg.mapM (towerLimbsR P) (towerLimbsR_regionTypes P) (towerSqLoop P.p β) (fun v => v)

/-- **The lowered loop computes the encoded `n`-fold square.** At every fuel, the lowered
    loop maps the encoding of the trip count `w` (one `reg 64` register) and of `x` (the limbs
    of the Montgomery forms of its two coordinates) to the encoding of the `w.toNat`-fold
    square of `x`. -/
theorem towerSqLoop_denote {n : Nat} (P : LimbParams n) (β : Int) (fuel : Nat) (w : BitVec 64)
    (x : Fp2Val P.p) :
    (towerSqLoopLimbs P β).denote fuel (flatVal (towerLimbsREnc P) (.cons w (.cons x .nil))) =
      some (flatVal (towerLimbsREnc P) (.cons (sqIter P.p β w.toNat x) .nil)) := by
  refine (withRegionTypes_mapM_denote (towerToLimbs P) towerAvoid tower_bit_ne_word
    towerJasminCodec (towerLimbEnc P) (TowerAt P.p) (towerToLimbs_blockSquare P) fuel
    (towerSqLoop P.p β) (towerSqLoop_covered P.p β) _ _ _
    (FieldDialectBlockDescent.pullV_id _)).trans ?_
  rw [towerSqLoop_denote_src]
  rfl

end TowerLoopWitness

end CatCrypt.Crypto.SecureCompilation.VIR
