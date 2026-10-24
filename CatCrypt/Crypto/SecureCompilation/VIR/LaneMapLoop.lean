/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVecCore
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

/-!
# The lane map on loop programs

`laneMapLoop S X` is the lane map of `LaneMapVecCore` extended in two directions.

* **More ops.** A lane-shape extension `X : LaneExt S` adds packed *blocks* for scalar
  binary ops the shape has no single packed instruction for (`binBlock`), and the
  broadcast of a scalar register into every lane (`castBlock`, the image of a
  `castW w S.laneBits` whose source is not lane-typed). A lane-width `stackStore` into a
  widened array lowers to the store of the packed value. An op all of whose operand
  and result types the lane map fixes (`LaneShape.fixedTy`: registers of another width,
  unwidened arrays, flags and inline integers) passes through unchanged; its value is
  the same in every lane. This covers the index arithmetic of a loop body at `reg 64`.
* **Loops.** The map is defined on `ComL`, the straight-line `Com` with the loop nodes
  of `JasminLprogExport`. For a shape whose lanes are not 64 bits wide the loop index
  and every trip count stay `reg 64` scalars, shared by all lanes, and each loop node
  maps to the same node over the lane-mapped body.

The lowering is written in continuation-passing style against a context homomorphism
`H : Ctxt.Hom (S.widenCtxt Γ) Δ` from the widened source context to the target context,
so that each op's block (built in `S.widenCtxt Γ`) is renamed into the target context and
spliced before the rest of the program.

## Main definitions

* `LaneShape.fixedTy`, `LaneShape.passOK`: the types and ops the lane map fixes.
* `LaneExt`: the block and broadcast extension of a lane shape, with its lane laws.
* `LaneShape.lowerExprX`, `LaneShape.CoveredExprX`: the extended per-op lowering and
  its covered fragment.
* `LaneShape.lowerC`, `LaneShape.lowerL`: the lowering of `Com` and `ComL` along a
  context homomorphism.
* `LaneShape.CoveredX`, `LaneShape.CoveredL`: the covered straight-line and loop
  programs, with `Decidable` instances.
* `spliceComLK`: the splice of a straight-line block before a loop program.
* `laneMapStraight`, `laneMapLoop`: the lowering at the canonical homomorphism.

## Main results

* `LaneShape.blockOpLaneX`: each covered op's block, read at lane `k`, computes the
  scalar op on lane `k`.
* `LaneShape.lowerC_lane`, `LaneShape.lowerL_lane`: lane `k` of a lowered program is the
  scalar program on lane `k`, by induction on the program and, at each loop node, on
  the trip count.
* `laneMapLoop_denote`: lane `k` of the lane-mapped `ComL` program's value is the scalar
  program's value on the lane-`k` valuation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (ComL JLoopBody JLoopBodyN)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
  (spliceComK consHom castHom lookup_pullV valuation_ext)

/-! ## 1. Fixed types -/

namespace LaneShape

variable (S : LaneShape)

/-- The types the lane map leaves unchanged and reads identically in every lane:
    registers of a width other than the lane width, stack arrays that do not widen,
    inline integers and flags. -/
def fixedTy : JasminTy → Bool
  | .reg w => w != S.laneBits
  | .stackArr w _ => !(S.arrWiden && w == S.laneBits)
  | .inlineInt => true
  | .bool => true

/-- A fixed type is its own widening. -/
theorem widenTy_fixed {t : JasminTy} (h : S.fixedTy t = true) : S.widenTy t = t := by
  cases t with
  | reg w =>
      simp only [fixedTy, bne_iff_ne, ne_eq] at h
      exact S.widenTy_reg_of_ne h
  | stackArr w n =>
      apply S.widenTy_arr_of_not
      simp only [fixedTy, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp] at h
      exact fun ⟨hA, hw⟩ => absurd (h hA) (by simp [hw])
  | inlineInt => rfl
  | bool => rfl

/-- At a fixed type, lane extraction is the identity (up to the type cast). -/
theorem laneOfTy_fixed (k : Fin S.laneCount) {t : JasminTy} (h : S.fixedTy t = true)
    (v : ⟦S.widenTy t⟧) :
    S.laneOfTy k t v = cast (congrArg TyDenote.denote (S.widenTy_fixed h)) v := by
  cases t with
  | reg w =>
      have hw : w ≠ S.laneBits := by simpa [fixedTy] using h
      simp only [laneOfTy, dite_eq_right hw]
  | stackArr w n =>
      have hw : ¬(S.arrWiden = true ∧ w = S.laneBits) := by
        simp only [fixedTy, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp] at h
        exact fun ⟨hA, hw⟩ => absurd (h hA) (by simp [hw])
      simp only [laneOfTy, dite_eq_right hw]
  | inlineInt => rfl
  | bool => rfl

/-! ## 2. Pass-through ops -/

theorem fixedTy_head {ty : JasminTy} {tys : List JasminTy}
    (h : (ty :: tys).all S.fixedTy = true) : S.fixedTy ty = true := by
  simp only [List.all_cons, Bool.and_eq_true] at h
  exact h.1

theorem fixedTy_tail {ty : JasminTy} {tys : List JasminTy}
    (h : (ty :: tys).all S.fixedTy = true) : tys.all S.fixedTy = true := by
  simp only [List.all_cons, Bool.and_eq_true] at h
  exact h.2

/-- Transport an argument vector of fixed types to the widened context. -/
def mapArgsFixed {Γ : Ctxt jasminDialect} : (tys : List JasminTy) →
    tys.all S.fixedTy = true →
    HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (S.widenCtxt Γ) ty) tys
  | [], _, .nil => .nil
  | _ :: tys, h, .cons v rest =>
      .cons (S.widenTy_fixed (S.fixedTy_head h) ▸ S.mapVar v)
        (mapArgsFixed tys (S.fixedTy_tail h) rest)

/-- Reading transported fixed-type arguments is reading the original arguments against
    the lane-`k` valuation. -/
theorem lookupArgs_mapArgsFixed {Γ : Ctxt jasminDialect}
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    (tys : List JasminTy) → (h : tys.all S.fixedTy = true) →
    (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    Expr.lookupArgs (S.mapArgsFixed tys h args) W = Expr.lookupArgs args (S.laneOf k Γ W)
  | [], _, .nil => rfl
  | ty :: tys, h, .cons v rest => by
      have hty : S.fixedTy ty = true := S.fixedTy_head h
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupArgs_mapArgsFixed W k tys _ rest, lookup_cast, ← S.laneOf_lookup v W k,
        S.laneOfTy_fixed k hty]

/-- An op the lane map passes through: its result type and all its operand types are
    fixed. -/
def passOK {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) : Bool :=
  S.fixedTy t && (DialectSignature.sig e.op).all S.fixedTy

theorem fixedTy_of_passOK {Γ : Ctxt jasminDialect} {t : JasminTy}
    {e : Expr jasminDialect Γ t} (h : S.passOK e = true) : S.fixedTy t = true := by
  simp only [passOK, Bool.and_eq_true] at h
  exact h.1

theorem args_of_passOK {Γ : Ctxt jasminDialect} {t : JasminTy}
    {e : Expr jasminDialect Γ t} (h : S.passOK e = true) :
    (DialectSignature.sig e.op).all S.fixedTy = true := by
  simp only [passOK, Bool.and_eq_true] at h
  exact h.2

/-- The block of a pass-through op: the op itself over the transported operands. -/
def passBlock {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (h : S.passOK e = true) : Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  (S.widenTy_fixed (S.fixedTy_of_passOK h)).symm ▸
    Com.var (⟨e.op, e.retTy_eq, S.mapArgsFixed _ (S.args_of_passOK h) e.args⟩ :
      Expr jasminDialect (S.widenCtxt Γ) t) (.ret .here)

/-- Lane `k` of a pass-through block is the scalar op on the lane-`k` valuation. -/
theorem passBlock_lane {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (h : S.passOK e = true) (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((S.passBlock e h).denote W) = e.denote (S.laneOf k Γ W) := by
  rw [S.laneOfTy_fixed k (S.fixedTy_of_passOK h), passBlock, denote_cast jasminDenote,
    cast_cast, cast_eq]
  obtain ⟨op, rfl, args⟩ := e
  show Expr.denote ⟨op, rfl, S.mapArgsFixed _ _ args⟩ W = Expr.denote ⟨op, rfl, args⟩ _
  simp only [Expr.denote]
  rw [S.lookupArgs_mapArgsFixed W k]

/-- Lane `k` of each element of an array updated at one index is the update of the
    lane-`k` array. -/
theorem lane_stackSet {n : Nat} (arr : Fin n → BitVec S.regBits)
    (m : Nat) (v : BitVec S.regBits) (k : Fin S.laneCount) :
    (fun j => S.lane (stackSet arr m v j) k)
      = stackSet (fun j => S.lane (arr j) k) m (S.lane v k) := by
  cases n with
  | zero => funext j; exact j.elim0
  | succ _ =>
      funext j
      simp only [stackSet]
      split <;> rfl

end LaneShape

/-! ## 3. The block and broadcast extension -/

/-- A two-operand packed block builder at register width `R`. -/
abbrev BinBuilder (R : Nat) : Type :=
  (Γ : Ctxt jasminDialect) → Ctxt.Var Γ (.reg R) → Ctxt.Var Γ (.reg R) →
    Com jasminDialect Γ (.reg R)

/-- A block builder from a `w`-bit scalar register to an `R`-bit packed register. -/
abbrev CastBuilder (w R : Nat) : Type :=
  (Γ : Ctxt jasminDialect) → Ctxt.Var Γ (.reg w) → Com jasminDialect Γ (.reg R)

/-- An extension of a lane shape: the packed block of each scalar binary op the shape
    has a block for, and the broadcast block of each scalar register width, with their
    lane laws under `jasminDenote`. -/
structure LaneExt (S : LaneShape) where
  /-- The packed block of a scalar binary op, if the extension has one. -/
  binBlock : JasminBinOp → Option (BinBuilder S.regBits)
  /-- Lane `k` of a packed block is the scalar op on lane `k` of its operands. -/
  bin_lane : ∀ (bop : JasminBinOp) (f : BinBuilder S.regBits), binBlock bop = some f →
    ∀ (Γ : Ctxt jasminDialect) (a b : Ctxt.Var Γ (.reg S.regBits))
      (V : Ctxt.Valuation Γ) (k : Fin S.laneCount),
      S.lane ((f Γ a b).denote V) k = bop.apply (S.lane (a.lookup V) k) (S.lane (b.lookup V) k)
  /-- The broadcast block of a `w`-bit scalar register, if the extension has one. -/
  castBlock : (w : Nat) → Option (CastBuilder w S.regBits)
  /-- Every lane of a broadcast block is the zero-extension or truncation of the scalar
      to the lane width. -/
  cast_lane : ∀ (w : Nat) (f : CastBuilder w S.regBits), castBlock w = some f →
    ∀ (Γ : Ctxt jasminDialect) (a : Ctxt.Var Γ (.reg w)) (V : Ctxt.Valuation Γ)
      (k : Fin S.laneCount),
      S.lane ((f Γ a).denote V) k = (a.lookup V).setWidth S.laneBits

/-- The empty extension: no blocks and no broadcasts. -/
def LaneExt.none (S : LaneShape) : LaneExt S where
  binBlock := fun _ => Option.none
  bin_lane := fun _ _ h => by cases h
  castBlock := fun _ => Option.none
  cast_lane := fun _ _ h => by cases h

namespace LaneShape

variable (S : LaneShape) (X : LaneExt S)

/-- The block of a packed two-operand block builder. -/
def binBlk {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits)
    (f : BinBuilder S.regBits) (a b : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w)) :=
  (S.widenTy_reg hw).symm ▸ f _ (S.wideVar hw a) (S.wideVar hw b)

/-- The block of a broadcast of a scalar register of another width. -/
def castBlk {Γ : Ctxt jasminDialect} {w w' : Nat} (hw' : w' = S.laneBits)
    (hw : w ≠ S.laneBits) (f : CastBuilder w S.regBits) (a : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w')) :=
  (S.widenTy_reg hw').symm ▸ f _ (S.widenTy_reg_of_ne hw ▸ S.mapVar a)

/-- The block of a lane-width store into a widened array: the store of the packed value
    into the widened element at the same index. -/
def storeBlk {Γ : Ctxt jasminDialect} {w : Nat} (hA : S.arrWiden = true)
    (hw : w = S.laneBits) (n : Nat) (arr : Ctxt.Var Γ (.stackArr w n))
    (idx : Ctxt.Var Γ (.reg 64)) (v : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.stackArr w n)) :=
  (S.widenTy_arr hA hw n).symm ▸
    Com.var ⟨.stackStore S.regBits n, rfl,
      .cons (S.arrVar hA hw arr) (.cons (S.idxVar hA idx) (.cons (S.wideVar hw v) .nil))⟩
      (.ret .here)

/-- The pass-through block when the op passes through, the lowering of
    `LaneMapVecCore` otherwise. -/
def passOr {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  if h : S.passOK e = true then S.passBlock e h else S.lowerExprBlock e

/-- The extended per-op block: a lane-width `regArith` lowers to the shape's packed op
    or else the extension's block; a lane-width `stackStore` into a widened array lowers
    to the packed store; a `castW` from another width to the lane width lowers to the
    extension's broadcast; every other op passes through when its types are fixed and
    lowers as in `LaneMapVecCore` otherwise. -/
def lowerExprX {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  match e with
  | ⟨.regArith bop w, h, .cons a (.cons b .nil)⟩ =>
      if hw : w = S.laneBits then
        if S.covers bop = true then S.lowerExprBlock ⟨.regArith bop w, h, .cons a (.cons b .nil)⟩
        else
          match X.binBlock bop with
          | some f => congrArg S.widenTy h ▸ S.binBlk hw f a b
          | none => S.fallbackBlock Γ t
      else S.passOr ⟨.regArith bop w, h, .cons a (.cons b .nil)⟩
  | ⟨.stackStore w n, h, .cons arr (.cons idx (.cons v .nil))⟩ =>
      if hw : S.arrWiden = true ∧ w = S.laneBits then
        congrArg S.widenTy h ▸ S.storeBlk hw.1 hw.2 n arr idx v
      else S.passOr ⟨.stackStore w n, h, .cons arr (.cons idx (.cons v .nil))⟩
  | ⟨.castW w w', h, .cons a .nil⟩ =>
      if hw : w' = S.laneBits ∧ w ≠ S.laneBits then
        match X.castBlock w with
        | some f => congrArg S.widenTy h ▸ S.castBlk hw.1 hw.2 f a
        | none => S.fallbackBlock Γ t
      else S.passOr ⟨.castW w w', h, .cons a .nil⟩
  | e => S.passOr e

/-- The ops the extended lowering maps lane-preservingly. -/
def CoveredExprX {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Prop :=
  match e.op with
  | .regArith bop w =>
      (w = S.laneBits ∧ (S.covers bop = true ∨ (X.binBlock bop).isSome = true))
        ∨ S.passOK e = true
  | .stackStore w _ => (S.arrWiden = true ∧ w = S.laneBits) ∨ S.passOK e = true
  | .castW w w' =>
      (w' = S.laneBits ∧ w ≠ S.laneBits ∧ (X.castBlock w).isSome = true)
        ∨ S.passOK e = true
  | _ => S.CoveredExpr e ∨ S.passOK e = true

/-- A program whose every op is covered by the extended lowering. -/
def CoveredX {Γ : Ctxt jasminDialect} {t : JasminTy} : Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => S.CoveredExprX X e ∧ CoveredX body

/-! ## 4. The per-op lane square of the extended lowering -/

omit X in
/-- At the default leaf semantics `jasminExtSem`, `jasminDenoteWith` is `jasminDenote`. -/
theorem denoteWith_extSem : jasminDenoteWith jasminExtSem = jasminDenote := by
  unfold jasminDenoteWith
  congr 1
  funext op
  cases op <;> rfl

omit X in
/-- The per-op lane square of `LaneMapVecCore` under `jasminDenote`. -/
theorem blockOpLane_ext (hm : S.MulhiLane jasminExtSem) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) (he : S.CoveredExpr e)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((S.lowerExprBlock e).denote W) = e.denote (S.laneOf k Γ W) := by
  have h := S.blockOpLane jasminExtSem hm e he W k
  rw [denoteWith_extSem] at h
  exact h

omit X in
/-- Lane `k` of `passOr` on a pass-through or core-covered op. -/
theorem passOr_lane (hm : S.MulhiLane jasminExtSem) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) (he : S.CoveredExpr e ∨ S.passOK e = true)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((S.passOr e).denote W) = e.denote (S.laneOf k Γ W) := by
  unfold passOr
  split
  · exact S.passBlock_lane e ‹_› W k
  · exact S.blockOpLane_ext hm e (he.resolve_right ‹_›) W k

omit X in
/-- The lane type is not fixed. -/
theorem fixedTy_lane : S.fixedTy (.reg S.laneBits) = false := by
  simp [fixedTy]

/-- Lane `k` of a packed block is the scalar op on lane `k`. -/
theorem laneOfTy_binBlk {Γ : Ctxt jasminDialect} (bop : JasminBinOp)
    (f : BinBuilder S.regBits) (hf : X.binBlock bop = some f)
    (a b : Ctxt.Var Γ (.reg S.laneBits)) (W : Ctxt.Valuation (S.widenCtxt Γ))
    (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits) ((S.binBlk rfl f a b).denote W)
      = bop.apply (a.lookup (S.laneOf k Γ W)) (b.lookup (S.laneOf k Γ W)) := by
  rw [laneOfTy_lane, binBlk, denote_cast jasminDenote, toReg, cast_cast, cast_eq,
    X.bin_lane bop f hf, lane_wideVar, lane_wideVar]

/-- Every lane of a broadcast block is the scalar at the lane width. -/
theorem laneOfTy_castBlk {Γ : Ctxt jasminDialect} {w : Nat} (hw : w ≠ S.laneBits)
    (f : CastBuilder w S.regBits) (hf : X.castBlock w = some f)
    (a : Ctxt.Var Γ (.reg w)) (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits) ((S.castBlk rfl hw f a).denote W)
      = (a.lookup (S.laneOf k Γ W)).setWidth S.laneBits := by
  have hfix : S.fixedTy (.reg w) = true := by simpa [fixedTy] using hw
  rw [laneOfTy_lane, castBlk, denote_cast jasminDenote, toReg, cast_cast, cast_eq,
    X.cast_lane w f hf, lookup_cast, ← S.laneOf_lookup a W k, S.laneOfTy_fixed k hfix]

omit X in
/-- Lane `k` of a packed store is the store into the lane-`k` array. -/
theorem laneOfTy_storeBlk {Γ : Ctxt jasminDialect} (hA : S.arrWiden = true) (n : Nat)
    (arr : Ctxt.Var Γ (.stackArr S.laneBits n)) (idx : Ctxt.Var Γ (.reg 64))
    (v : Ctxt.Var Γ (.reg S.laneBits)) (W : Ctxt.Valuation (S.widenCtxt Γ))
    (k : Fin S.laneCount) :
    S.laneOfTy k (.stackArr S.laneBits n) ((S.storeBlk hA rfl n arr idx v).denote W)
      = stackSet (arr.lookup (S.laneOf k Γ W)) (idx.lookup (S.laneOf k Γ W)).toNat
          (v.lookup (S.laneOf k Γ W)) := by
  simp only [laneOfTy, hA, and_self, dite_true, cast_eq]
  rw [storeBlk, denote_cast jasminDenote, cast_cast, cast_eq]
  show (fun i => S.lane (stackSet ((S.arrVar hA rfl arr).lookup W)
      ((S.idxVar hA idx).lookup W).toNat ((S.wideVar rfl v).lookup W) i) k) = _
  rw [S.lane_stackSet, S.lane_arrVar hA, S.idxVar_lookup hA idx W k, lane_wideVar]

/-- **Per-op lane square of the extended lowering.** For each op covered by the extended
    lowering, the block read at lane `k` computes the scalar op on lane `k`. -/
theorem blockOpLaneX (hm : S.MulhiLane jasminExtSem) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) (he : S.CoveredExprX X e)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((S.lowerExprX X e).denote W) = e.denote (S.laneOf k Γ W) := by
  obtain ⟨op, rfl, args⟩ := e
  cases op
  case regArith bop w =>
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    by_cases hw : w = S.laneBits
    · subst hw
      have hne : ¬ S.passOK (⟨.regArith bop S.laneBits, rfl, .cons a (.cons b .nil)⟩ :
          Expr jasminDialect Γ (.reg S.laneBits)) = true := fun h => by
        have := S.fixedTy_of_passOK h
        rw [fixedTy_lane] at this
        cases this
      have hc := (he.resolve_right hne).2
      by_cases hcov : S.covers bop = true
      · have hblk : S.lowerExprX X (⟨.regArith bop S.laneBits, rfl, .cons a (.cons b .nil)⟩ :
            Expr jasminDialect Γ (.reg S.laneBits))
            = S.lowerExprBlock ⟨.regArith bop S.laneBits, rfl, .cons a (.cons b .nil)⟩ := by
          exact (dite_eq_left rfl).trans (ite_eq_left hcov)
        rw [hblk]
        exact S.blockOpLane_ext hm
          (⟨.regArith bop S.laneBits, rfl, .cons a (.cons b .nil)⟩ :
            Expr jasminDialect Γ (.reg S.laneBits)) ⟨rfl, hcov⟩ W k
      · obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (hc.resolve_left hcov)
        have hblk : S.lowerExprX X (⟨.regArith bop S.laneBits, rfl, .cons a (.cons b .nil)⟩ :
            Expr jasminDialect Γ (.reg S.laneBits)) = S.binBlk rfl f a b := by
          refine (dite_eq_left rfl).trans ((ite_eq_right hcov).trans ?_)
          rw [hf]
        change S.laneOfTy k (.reg S.laneBits) _ = _
        rw [hblk, S.laneOfTy_binBlk X bop f hf]
        rfl
    · have hp : S.passOK (⟨.regArith bop w, rfl, .cons a (.cons b .nil)⟩ :
          Expr jasminDialect Γ (.reg w)) = true := he.resolve_left (fun h => hw h.1)
      have hblk : S.lowerExprX X (⟨.regArith bop w, rfl, .cons a (.cons b .nil)⟩ :
          Expr jasminDialect Γ (.reg w))
          = S.passOr ⟨.regArith bop w, rfl, .cons a (.cons b .nil)⟩ :=
        dite_eq_right hw
      rw [hblk]
      exact S.passOr_lane hm _ (Or.inr hp) W k
  case stackStore w n =>
    cases args; rename_i arr rest
    cases rest; rename_i idx rest2
    cases rest2; rename_i v rest3
    cases rest3
    by_cases hw : S.arrWiden = true ∧ w = S.laneBits
    · obtain ⟨hA, rfl⟩ := hw
      have hblk : S.lowerExprX X (⟨.stackStore S.laneBits n, rfl,
          .cons arr (.cons idx (.cons v .nil))⟩ :
            Expr jasminDialect Γ (.stackArr S.laneBits n)) = S.storeBlk hA rfl n arr idx v :=
        dite_eq_left (And.intro hA rfl)
      change S.laneOfTy k (.stackArr S.laneBits n) _ = _
      rw [hblk, S.laneOfTy_storeBlk hA]
      rfl
    · have hp := he.resolve_left hw
      have hblk : S.lowerExprX X (⟨.stackStore w n, rfl,
          .cons arr (.cons idx (.cons v .nil))⟩ : Expr jasminDialect Γ (.stackArr w n))
          = S.passOr ⟨.stackStore w n, rfl, .cons arr (.cons idx (.cons v .nil))⟩ :=
        dite_eq_right hw
      rw [hblk]
      exact S.passOr_lane hm _ (Or.inr hp) W k
  case castW w w' =>
    cases args; rename_i a rest
    cases rest
    by_cases hw : w' = S.laneBits ∧ w ≠ S.laneBits
    · obtain ⟨rfl, hw2⟩ := hw
      have hne : ¬ S.passOK (⟨.castW w S.laneBits, rfl, .cons a .nil⟩ :
          Expr jasminDialect Γ (.reg S.laneBits)) = true := fun h => by
        have := S.fixedTy_of_passOK h
        rw [fixedTy_lane] at this
        cases this
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (he.resolve_right hne).2.2
      have hblk : S.lowerExprX X (⟨.castW w S.laneBits, rfl, .cons a .nil⟩ :
          Expr jasminDialect Γ (.reg S.laneBits)) = S.castBlk rfl hw2 f a := by
        refine (dite_eq_left (And.intro rfl hw2)).trans ?_
        rw [hf]
      change S.laneOfTy k (.reg S.laneBits) _ = _
      rw [hblk, S.laneOfTy_castBlk X hw2 f hf]
      rfl
    · have hp := he.resolve_left (fun h => hw ⟨h.1, h.2.1⟩)
      have hblk : S.lowerExprX X (⟨.castW w w', rfl, .cons a .nil⟩ :
          Expr jasminDialect Γ (.reg w')) = S.passOr ⟨.castW w w', rfl, .cons a .nil⟩ :=
        dite_eq_right hw
      rw [hblk]
      exact S.passOr_lane hm _ (Or.inr hp) W k
  all_goals exact S.passOr_lane hm _ he W k

end LaneShape

/-! ## 5. Splicing a block before a continuation -/

/-- `spliceComK blk k` satisfies every property that `k ren res` satisfies whenever
    `ren` preserves lookups and `res` holds the block's value. -/
theorem spliceComK_prop {Γ : Ctxt jasminDialect} {a b : JasminTy}
    (blk : Com jasminDialect Γ a)
    (k : {Δ : Ctxt jasminDialect} → Ctxt.Hom Γ Δ → Ctxt.Var Δ a → Com jasminDialect Δ b)
    (W : Ctxt.Valuation Γ) (P : ⟦b⟧ → Prop)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) (res : Ctxt.Var Δ a)
        (W' : Ctxt.Valuation Δ),
        (∀ {s : JasminTy} (v : Ctxt.Var Γ s), (ren v).lookup W' = v.lookup W) →
        res.lookup W' = blk.denote W → P ((k ren res).denote W')) :
    P ((spliceComK blk k).denote W) := by
  induction blk with
  | ret v => exact hk (fun x => x) v W (fun _ => rfl) rfl
  | var e blk ih =>
      exact ih (fun ren res => k (fun x => ren (.there x)) res) _
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W' (fun v => h1 (.there v)) h2)

/-- **Block splice into a loop program.** `spliceComLK blk k` keeps the bindings of the
    straight-line block `blk` and, at its return variable `res`, continues with the loop
    program `k ren res`, where `ren` renames the context of `blk` into the extended
    context. -/
def spliceComLK : {Γ : Ctxt jasminDialect} → {a b : JasminTy} →
    Com jasminDialect Γ a →
    ({Δ : Ctxt jasminDialect} → Ctxt.Hom Γ Δ → Ctxt.Var Δ a → ComL Δ b) → ComL Γ b
  | _, _, _, .ret v, k => k (fun x => x) v
  | _, _, _, .var e blk, k =>
      .var e (spliceComLK blk (fun ren res => k (fun x => ren (.there x)) res))

/-- `spliceComLK blk k` satisfies every property that `k ren res` satisfies whenever
    `ren` preserves lookups and `res` holds the block's value. -/
theorem spliceComLK_prop {Γ : Ctxt jasminDialect} {a b : JasminTy}
    (blk : Com jasminDialect Γ a)
    (k : {Δ : Ctxt jasminDialect} → Ctxt.Hom Γ Δ → Ctxt.Var Δ a → ComL Δ b)
    (W : Ctxt.Valuation Γ) (P : ⟦b⟧ → Prop)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) (res : Ctxt.Var Δ a)
        (W' : Ctxt.Valuation Δ),
        (∀ {s : JasminTy} (v : Ctxt.Var Γ s), (ren v).lookup W' = v.lookup W) →
        res.lookup W' = blk.denote W → P ((k ren res).denote W')) :
    P ((spliceComLK blk k).denote W) := by
  induction blk with
  | ret v => exact hk (fun x => x) v W (fun _ => rfl) rfl
  | var e blk ih =>
      exact ih (fun ren res => k (fun x => ren (.there x)) res) _
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W' (fun v => h1 (.there v)) h2)

/-- Pullbacks along two homomorphisms that agree on lookups are equal. -/
theorem pullV_congr {Γ Δ Δ' : Ctxt jasminDialect} (g : Ctxt.Hom Γ Δ') (h : Ctxt.Hom Γ Δ)
    (W' : Ctxt.Valuation Δ') (W : Ctxt.Valuation Δ)
    (hgh : ∀ {s : JasminTy} (v : Ctxt.Var Γ s), (g v).lookup W' = (h v).lookup W) :
    pullV g W' = pullV h W :=
  valuation_ext _ _ fun v => by rw [lookup_pullV, lookup_pullV, hgh]

/-! ## 6. The straight-line lowering along a homomorphism -/

namespace LaneShape

variable (S : LaneShape) (X : LaneExt S)

/-- The lane map of a straight-line program along a homomorphism `H` from the widened
    source context to the target context: each op's block is renamed along `H` and
    spliced before the lowering of the rest. -/
def lowerC : {Γ Δ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    Ctxt.Hom (S.widenCtxt Γ) Δ → Com jasminDialect Δ (S.widenTy t)
  | _, _, _, .ret v, H => .ret (H (S.mapVar v))
  | _, _, _, .var e body, H =>
      spliceComK (Com.rename H (S.lowerExprX X e))
        (fun ren res => lowerC body (consHom (fun x => ren (H x)) res))

/-- Lane `k` of a variable read along `H` is the variable read in the lane-`k`
    valuation of the pullback. -/
theorem laneOfTy_lookupH {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (H : Ctxt.Hom (S.widenCtxt Γ) Δ) (v : Ctxt.Var Γ t) (W : Ctxt.Valuation Δ)
    (k : Fin S.laneCount) :
    S.laneOfTy k t ((H (S.mapVar v)).lookup W) = v.lookup (S.laneOf k Γ (pullV H W)) := by
  rw [Var.lookup_rename, S.laneOf_lookup]

/-- **Lane theorem of the straight-line lowering.** If the lane-`k` valuation of the
    pullback along `H` is `V`, lane `k` of the lowered program's value is the scalar
    program's value at `V`. -/
theorem lowerC_lane (hm : S.MulhiLane jasminExtSem) (k : Fin S.laneCount) :
    {Γ Δ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    S.CoveredX X c → (H : Ctxt.Hom (S.widenCtxt Γ) Δ) → (W : Ctxt.Valuation Δ) →
    (V : Ctxt.Valuation Γ) → S.laneOf k Γ (pullV H W) = V →
    S.laneOfTy k t ((S.lowerC X c H).denote W) = c.denote V
  | _, _, _, .ret v, _, H, W, V, hV => by
      show S.laneOfTy k _ ((H (S.mapVar v)).lookup W) = v.lookup V
      rw [S.laneOfTy_lookupH, hV]
  | Γ, _, _, .var (t := u) e body, hc, H, W, V, hV => by
      obtain ⟨he, hbody⟩ := hc
      refine spliceComK_prop (Com.rename H (S.lowerExprX X e)) _ W
        (fun x => S.laneOfTy k _ x = body.denote (V.extend (e.denote V))) ?_
      intro Δ' ren res W' hren hres
      refine lowerC_lane hm k body hbody _ W' _ ?_
      show HVector.cons (S.laneOfTy k u (res.lookup W'))
          (S.laneOf k Γ (pullV (fun x => ren (H x)) W')) = HVector.cons (e.denote V) V
      rw [hres, Com.denote_rename, S.blockOpLaneX X hm e he, hV,
        pullV_congr (fun x => ren (H x)) H W' W (fun v => hren (H v)), hV]

/-! ## 7. Loop plumbing: the scalar loop index -/

variable {S}

/-- At a shape whose lanes are not 64 bits wide, `reg 64` is fixed. -/
theorem fixedTy_reg64 (h64 : S.laneBits ≠ 64) : S.fixedTy (.reg 64) = true := by
  simpa [fixedTy] using fun h => h64 h.symm

/-- At a shape whose lanes are not 64 bits wide, `reg 64` is its own widening. -/
theorem widen64 (h64 : S.laneBits ≠ 64) : S.widenTy (.reg 64) = .reg 64 :=
  S.widenTy_fixed (fixedTy_reg64 h64)

/-- Lane `k` of a `reg 64` value cast to the widened type is the value. -/
theorem laneOfTy_reg64 (h64 : S.laneBits ≠ 64) (k : Fin S.laneCount) (y : BitVec 64) :
    S.laneOfTy k (.reg 64) (cast (congrArg TyDenote.denote (widen64 h64).symm) y) = y := by
  rw [S.laneOfTy_fixed k (fixedTy_reg64 h64), cast_cast, cast_eq]

/-- The renaming of a widened `[reg 64, *L]` context onto `[reg 64, *widenCtxt L]`. -/
def idx1Hom (h64 : S.laneBits ≠ 64) (L : Ctxt jasminDialect) :
    Ctxt.Hom (S.widenCtxt (.reg 64 :: L)) (.reg 64 :: S.widenCtxt L) :=
  castHom (congrArg (fun u => u :: S.widenCtxt L) (widen64 h64))

/-- The renaming of a widened `[a, reg 64, *L]` context onto
    `[widenTy a, reg 64, *widenCtxt L]`. -/
def idx2Hom (h64 : S.laneBits ≠ 64) (a : JasminTy) (L : Ctxt jasminDialect) :
    Ctxt.Hom (S.widenCtxt (a :: .reg 64 :: L)) (S.widenTy a :: .reg 64 :: S.widenCtxt L) :=
  castHom (congrArg (fun u => S.widenTy a :: u :: S.widenCtxt L) (widen64 h64))

/-- The renaming of a widened `[a, reg 64, reg 64, *L]` context onto
    `[widenTy a, reg 64, reg 64, *widenCtxt L]`. -/
def idx3Hom (h64 : S.laneBits ≠ 64) (a : JasminTy) (L : Ctxt jasminDialect) :
    Ctxt.Hom (S.widenCtxt (a :: .reg 64 :: .reg 64 :: L))
      (S.widenTy a :: .reg 64 :: .reg 64 :: S.widenCtxt L) :=
  castHom (congrArg (fun u => S.widenTy a :: u :: u :: S.widenCtxt L) (widen64 h64))

theorem pullV_castHom1 {u : JasminTy} {L : Ctxt jasminDialect} (hr : u = .reg 64)
    (y : BitVec 64) (R : Ctxt.Valuation L) :
    pullV (castHom (congrArg (fun u => u :: L) hr))
        (HVector.cons y R : Ctxt.Valuation (JasminTy.reg 64 :: L))
      = HVector.cons (cast (congrArg TyDenote.denote hr.symm) y) R := by
  subst hr
  exact pullV_id _

theorem pullV_castHom2 {a u : JasminTy} {L : Ctxt jasminDialect} (hr : u = .reg 64)
    (x : ⟦a⟧) (y : BitVec 64) (R : Ctxt.Valuation L) :
    pullV (castHom (congrArg (fun u => a :: u :: L) hr))
        (HVector.cons x (HVector.cons y R) : Ctxt.Valuation (a :: JasminTy.reg 64 :: L))
      = HVector.cons x (HVector.cons (cast (congrArg TyDenote.denote hr.symm) y) R) := by
  subst hr
  exact pullV_id _

theorem pullV_castHom3 {a u : JasminTy} {L : Ctxt jasminDialect} (hr : u = .reg 64)
    (x : ⟦a⟧) (y z : BitVec 64) (R : Ctxt.Valuation L) :
    pullV (castHom (congrArg (fun u => a :: u :: u :: L) hr))
        (HVector.cons x (HVector.cons y (HVector.cons z R)) :
          Ctxt.Valuation (a :: JasminTy.reg 64 :: JasminTy.reg 64 :: L))
      = HVector.cons x (HVector.cons (cast (congrArg TyDenote.denote hr.symm) y)
          (HVector.cons (cast (congrArg TyDenote.denote hr.symm) z) R)) := by
  subst hr
  exact pullV_id _

theorem pullV_idx1Hom (h64 : S.laneBits ≠ 64) {L : Ctxt jasminDialect} (y : BitVec 64)
    (R : Ctxt.Valuation (S.widenCtxt L)) :
    pullV (idx1Hom h64 L) (HVector.cons y R : Ctxt.Valuation (JasminTy.reg 64 :: _))
      = HVector.cons (cast (congrArg TyDenote.denote (widen64 h64).symm) y) R :=
  pullV_castHom1 (widen64 h64) y R

theorem pullV_idx2Hom (h64 : S.laneBits ≠ 64) {a : JasminTy} {L : Ctxt jasminDialect}
    (x : ⟦S.widenTy a⟧) (y : BitVec 64) (R : Ctxt.Valuation (S.widenCtxt L)) :
    pullV (idx2Hom h64 a L)
        (HVector.cons x (HVector.cons y R) : Ctxt.Valuation (_ :: JasminTy.reg 64 :: _))
      = HVector.cons x (HVector.cons (cast (congrArg TyDenote.denote (widen64 h64).symm) y) R) :=
  pullV_castHom2 (widen64 h64) x y R

theorem pullV_idx3Hom (h64 : S.laneBits ≠ 64) {a : JasminTy} {L : Ctxt jasminDialect}
    (x : ⟦S.widenTy a⟧) (y z : BitVec 64) (R : Ctxt.Valuation (S.widenCtxt L)) :
    pullV (idx3Hom h64 a L)
        (HVector.cons x (HVector.cons y (HVector.cons z R)) :
          Ctxt.Valuation (_ :: JasminTy.reg 64 :: JasminTy.reg 64 :: _))
      = HVector.cons x (HVector.cons (cast (congrArg TyDenote.denote (widen64 h64).symm) y)
          (HVector.cons (cast (congrArg TyDenote.denote (widen64 h64).symm) z) R)) :=
  pullV_castHom3 (widen64 h64) x y z R

/-- Denoting a program cast along an equality of result types is the cast of the
    denotation. -/
theorem denote_castRet {Γ : Ctxt jasminDialect} {τ τ' : JasminTy} (h : τ = τ')
    (c : Com jasminDialect Γ τ) (V : Ctxt.Valuation Γ) :
    (cast (congrArg (Com jasminDialect Γ) h) c).denote V
      = cast (congrArg TyDenote.denote h) (c.denote V) := by
  subst h
  rfl

/-- A `reg 64` variable read along `H`, at the register type. -/
def cnt64 (h64 : S.laneBits ≠ 64) {Γ Δ : Ctxt jasminDialect}
    (H : Ctxt.Hom (S.widenCtxt Γ) Δ) (c : Ctxt.Var Γ (.reg 64)) : Ctxt.Var Δ (.reg 64) :=
  widen64 h64 ▸ H (S.mapVar c)

/-- A `reg 64` variable read along `H` is the scalar variable read in the lane-`k`
    valuation of the pullback. -/
theorem lookup_cnt64 (h64 : S.laneBits ≠ 64) {Γ Δ : Ctxt jasminDialect}
    (H : Ctxt.Hom (S.widenCtxt Γ) Δ) (c : Ctxt.Var Γ (.reg 64)) (W : Ctxt.Valuation Δ)
    (k : Fin S.laneCount) :
    (cnt64 h64 H c).lookup W = c.lookup (S.laneOf k Γ (pullV H W)) := by
  rw [cnt64, lookup_cast, ← S.laneOfTy_lookupH, S.laneOfTy_fixed k (fixedTy_reg64 h64)]

variable (S)

/-- Transport the invariant operands of a loop along `H`. -/
def mapInvs {Γ Δ : Ctxt jasminDialect} (H : Ctxt.Hom (S.widenCtxt Γ) Δ) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var Δ ty) (S.widenCtxt tys)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (H (S.mapVar v)) (mapInvs H rest)

/-- Lane `k` of the transported invariants is the scalar invariants in the lane-`k`
    valuation of the pullback. -/
theorem laneOf_mapInvs {Γ Δ : Ctxt jasminDialect} (H : Ctxt.Hom (S.widenCtxt Γ) Δ)
    (W : Ctxt.Valuation Δ) (k : Fin S.laneCount) :
    {tys : List JasminTy} → (invs : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    S.laneOf k tys (Expr.lookupArgs (S.mapInvs H invs) W)
      = Expr.lookupArgs invs (S.laneOf k Γ (pullV H W))
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons (S.laneOfTy k _ ((H (S.mapVar v)).lookup W))
          (S.laneOf k _ (Expr.lookupArgs (S.mapInvs H rest) W)) = _
      rw [S.laneOfTy_lookupH, laneOf_mapInvs H W k rest]
      rfl

/-- The lane-`k` valuation of the pullback along the continuation renaming of a loop
    node. -/
theorem laneOf_pullV_cont {Γ Δ : Ctxt jasminDialect} {a : JasminTy}
    (H : Ctxt.Hom (S.widenCtxt Γ) Δ) (x : ⟦S.widenTy a⟧) (W : Ctxt.Valuation Δ)
    (k : Fin S.laneCount) :
    S.laneOf k (a :: Γ)
        (pullV (consHom (fun v => (H v).there) (Ctxt.Var.here (Γ := Δ) (t := S.widenTy a)))
          (HVector.cons x W))
      = HVector.cons (S.laneOfTy k a x) (S.laneOf k Γ (pullV H W)) := by
  show HVector.cons _ (S.laneOf k Γ (pullV (fun v => (H v).there) (HVector.cons x W))) = _
  rw [pullV_there]
  rfl

/-! ## 8. One trip of a lowered loop body -/

/-- One trip of a lowered multi-binder loop body, read at lane `k`, is one trip of the
    scalar body at lane `k`. -/
theorem stepC_lane (hm : S.MulhiLane jasminExtSem) (h64 : S.laneBits ≠ 64)
    (k : Fin S.laneCount) {acc : JasminTy} {inv : Ctxt jasminDialect}
    (u : Com jasminDialect (acc :: .reg 64 :: inv) acc) (hu : S.CoveredX X u)
    (invs' : Ctxt.Valuation (S.widenCtxt inv)) (invs : Ctxt.Valuation inv)
    (hinv : S.laneOf k inv invs' = invs) (t : Nat) (a : ⟦S.widenTy acc⟧) :
    S.laneOfTy k acc (JLoopBodyN.stepC (S.lowerC X u (idx2Hom h64 acc inv)) invs' t a)
      = JLoopBodyN.stepC u invs t (S.laneOfTy k acc a) := by
  refine S.lowerC_lane X hm k u hu _ _ _ ?_
  rw [pullV_idx2Hom]
  show HVector.cons _ (HVector.cons (S.laneOfTy k (.reg 64) (cast _ (BitVec.ofNat 64 t)))
    (S.laneOf k inv invs')) = _
  rw [laneOfTy_reg64 h64, hinv]
  rfl

/-- One inner trip of a lowered nested loop body, read at lane `k`, is one inner trip of
    the scalar body at lane `k`. -/
theorem stepCNested_lane (hm : S.MulhiLane jasminExtSem) (h64 : S.laneBits ≠ 64)
    (k : Fin S.laneCount) {acc : JasminTy} {inv : Ctxt jasminDialect}
    (u : Com jasminDialect (acc :: .reg 64 :: .reg 64 :: inv) acc) (hu : S.CoveredX X u)
    (invs' : Ctxt.Valuation (S.widenCtxt inv)) (invs : Ctxt.Valuation inv)
    (hinv : S.laneOf k inv invs' = invs) (jd t : Nat) (a : ⟦S.widenTy acc⟧) :
    S.laneOfTy k acc
        (JLoopBodyN.stepCNested (S.lowerC X u (idx3Hom h64 acc inv)) invs' jd t a)
      = JLoopBodyN.stepCNested u invs jd t (S.laneOfTy k acc a) := by
  refine S.lowerC_lane X hm k u hu _ _ _ ?_
  rw [pullV_idx3Hom]
  show HVector.cons _ (HVector.cons (S.laneOfTy k (.reg 64) (cast _ (BitVec.ofNat 64 t)))
    (HVector.cons (S.laneOfTy k (.reg 64) (cast _ (BitVec.ofNat 64 jd)))
      (S.laneOf k inv invs'))) = _
  rw [laneOfTy_reg64 h64, laneOfTy_reg64 h64, hinv]
  rfl

/-- The lowering of an inner-count body, at the `reg 64` result type. -/
def lowerCount (h64 : S.laneBits ≠ 64) {inv : Ctxt jasminDialect}
    (ic : Com jasminDialect (.reg 64 :: inv) (.reg 64)) :
    Com jasminDialect (.reg 64 :: S.widenCtxt inv) (.reg 64) :=
  cast (congrArg (Com jasminDialect (JasminTy.reg 64 :: S.widenCtxt inv)) (widen64 h64))
    (S.lowerC X ic (idx1Hom h64 inv))

/-- The lowered inner-count body of a nested loop computes, at every outer index, the
    scalar inner trip count at lane `k`; the trip count is the same in every lane. -/
theorem innerTrip_lane (hm : S.MulhiLane jasminExtSem) (h64 : S.laneBits ≠ 64)
    (k : Fin S.laneCount) {inv : Ctxt jasminDialect}
    (ic : Com jasminDialect (.reg 64 :: inv) (.reg 64)) (hic : S.CoveredX X ic)
    (invs' : Ctxt.Valuation (S.widenCtxt inv)) (invs : Ctxt.Valuation inv)
    (hinv : S.laneOf k inv invs' = invs) (jd : Nat) :
    JLoopBodyN.innerTripAtC (S.lowerCount X h64 ic) invs' jd
      = JLoopBodyN.innerTripAtC ic invs jd := by
  unfold JLoopBodyN.innerTripAtC lowerCount
  rw [denote_castRet (widen64 h64)]
  congr 1
  have h := S.lowerC_lane X hm k ic hic (idx1Hom h64 inv)
    (HVector.cons (BitVec.ofNat 64 jd) invs') (HVector.cons (BitVec.ofNat 64 jd) invs) (by
      rw [pullV_idx1Hom]
      show HVector.cons (S.laneOfTy k (.reg 64) (cast _ (BitVec.ofNat 64 jd)))
        (S.laneOf k inv invs') = _
      rw [laneOfTy_reg64 h64, hinv])
  rw [S.laneOfTy_fixed k (fixedTy_reg64 h64)] at h
  exact h

/-- A fold commutes with a map that carries each step to the other fold's step. -/
theorem foldl_lane {α β : Type} (g : α → β) (f' : α → Nat → α) (f : β → Nat → β)
    (h : ∀ a t, g (f' a t) = f (g a) t) : (l : List Nat) → (a : α) →
    g (l.foldl f' a) = l.foldl f (g a)
  | [], _ => rfl
  | t :: l, a => by
      rw [List.foldl_cons, List.foldl_cons, foldl_lane g f' f h l, h]

/-! ## 9. The loop lowering -/

/-- The lane map of a loop program along a homomorphism `H`, at a shape whose lanes are
    not 64 bits wide. A straight-line binding splices its op's renamed block; a loop node
    maps to the same node over the lowered body, the trip counts and the loop index stay
    `reg 64`, and the continuation is lowered with the loop's accumulator bound. -/
def lowerL (h64 : S.laneBits ≠ 64) : {Γ Δ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → Ctxt.Hom (S.widenCtxt Γ) Δ → ComL Δ (S.widenTy t)
  | _, _, _, .ret v, H => .ret (H (S.mapVar v))
  | _, _, _, .var e body, H =>
      spliceComLK (Com.rename H (S.lowerExprX X e))
        (fun ren res => lowerL h64 body (consHom (fun x => ren (H x)) res))
  | _, _, _, .forLoop loop init body, H =>
      .forLoop ⟨loop.n, S.lowerC X loop.update (fun v => v)⟩ (H (S.mapVar init))
        (lowerL h64 body (consHom (fun x => (H x).there) .here))
  | _, _, _, .forLoopN loop init invs body, H =>
      .forLoopN ⟨loop.n, S.lowerC X loop.update (idx2Hom h64 _ _)⟩ (H (S.mapVar init))
        (S.mapInvs H invs) (lowerL h64 body (consHom (fun x => (H x).there) .here))
  | _, _, _, .forLoopNRt update count init invs body, H =>
      .forLoopNRt (S.lowerC X update (idx2Hom h64 _ _)) (cnt64 h64 H count)
        (H (S.mapVar init)) (S.mapInvs H invs)
        (lowerL h64 body (consHom (fun x => (H x).there) .here))
  | _, _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body, H =>
      .forLoopNRtNested (S.lowerCount X h64 innerCount)
        (S.lowerC X innerUpdate (idx3Hom h64 _ _)) (cnt64 h64 H outerCount)
        (H (S.mapVar init)) (S.mapInvs H invs)
        (lowerL h64 body (consHom (fun x => (H x).there) .here))
  | _, _, _, .whileNz update guard init invs body, H =>
      .whileNz (S.lowerC X update (idx2Hom h64 _ _)) (cnt64 h64 H guard)
        (H (S.mapVar init)) (S.mapInvs H invs)
        (lowerL h64 body (consHom (fun x => (H x).there) .here))
  | _, _, _, .forLoopBlock loopBody count init invs body, H =>
      .forLoopBlock (lowerL h64 loopBody (idx2Hom h64 _ _)) (cnt64 h64 H count)
        (H (S.mapVar init)) (S.mapInvs H invs)
        (lowerL h64 body (consHom (fun x => (H x).there) .here))

/-- A loop program whose every straight-line op and every loop body is covered by the
    extended lowering. -/
def CoveredL {Γ : Ctxt jasminDialect} {t : JasminTy} : ComL Γ t → Prop
  | .ret _ => True
  | .var e body => S.CoveredExprX X e ∧ CoveredL body
  | .forLoop loop _ body => S.CoveredX X loop.update ∧ CoveredL body
  | .forLoopN loop _ _ body => S.CoveredX X loop.update ∧ CoveredL body
  | .forLoopNRt update _ _ _ body => S.CoveredX X update ∧ CoveredL body
  | .forLoopNRtNested innerCount innerUpdate _ _ _ body =>
      S.CoveredX X innerCount ∧ S.CoveredX X innerUpdate ∧ CoveredL body
  | .whileNz update _ _ _ body => S.CoveredX X update ∧ CoveredL body
  | .forLoopBlock loopBody _ _ _ body => CoveredL loopBody ∧ CoveredL body

/-- **Lane theorem of the loop lowering.** If the lane-`k` valuation of the pullback
    along `H` is `V`, lane `k` of the lowered loop program's value is the scalar
    program's value at `V`. At each loop node the trip count is the same scalar in every
    lane, and the accumulator is related lane-wise by induction over the trips
    (`foldl_lane`), each trip by the straight-line lane theorem `lowerC_lane`. -/
theorem lowerL_lane (hm : S.MulhiLane jasminExtSem) (h64 : S.laneBits ≠ 64)
    (k : Fin S.laneCount) :
    {Γ Δ : Ctxt jasminDialect} → {t : JasminTy} → (c : ComL Γ t) →
    S.CoveredL X c → (H : Ctxt.Hom (S.widenCtxt Γ) Δ) → (W : Ctxt.Valuation Δ) →
    (V : Ctxt.Valuation Γ) → S.laneOf k Γ (pullV H W) = V →
    S.laneOfTy k t ((S.lowerL X h64 c H).denote W) = c.denote V
  | _, _, _, .ret v, _, H, W, V, hV => by
      show S.laneOfTy k _ ((H (S.mapVar v)).lookup W) = v.lookup V
      rw [S.laneOfTy_lookupH, hV]
  | Γ, _, _, .var (t := u) e body, hc, H, W, V, hV => by
      obtain ⟨he, hbody⟩ := hc
      refine spliceComLK_prop (Com.rename H (S.lowerExprX X e)) _ W
        (fun x => S.laneOfTy k _ x = body.denote (V.extend (e.denote V))) ?_
      intro Δ' ren res W' hren hres
      refine lowerL_lane hm h64 k body hbody _ W' _ ?_
      show HVector.cons (S.laneOfTy k u (res.lookup W'))
          (S.laneOf k Γ (pullV (fun x => ren (H x)) W')) = HVector.cons (e.denote V) V
      rw [hres, Com.denote_rename, S.blockOpLaneX X hm e he, hV,
        pullV_congr (fun x => ren (H x)) H W' W (fun v => hren (H v)), hV]
  | Γ, _, _, .forLoop (accTy := acc) loop init body, hc, H, W, V, hV => by
      subst hV
      obtain ⟨hu, hbody⟩ := hc
      refine lowerL_lane hm h64 k body hbody _ _ _ ?_
      refine (S.laneOf_pullV_cont H _ W k).trans ?_
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      rw [← S.laneOfTy_lookupH H init W k]
      refine foldl_lane _ _ _ (fun a _ => ?_) _ _
      refine S.lowerC_lane X hm k loop.update hu (fun v => v) _ _ ?_
      rw [pullV_id]
      rfl
  | Γ, _, _, .forLoopN (accTy := acc) (invTys := inv) loop init invs body, hc, H, W, V, hV => by
      subst hV
      obtain ⟨hu, hbody⟩ := hc
      refine lowerL_lane hm h64 k body hbody _ _ _ ?_
      refine (S.laneOf_pullV_cont H _ W k).trans ?_
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      rw [← S.laneOfTy_lookupH H init W k]
      exact foldl_lane _ _ _
        (fun a t => S.stepC_lane X hm h64 k loop.update hu _ _ (S.laneOf_mapInvs H W k invs) t a)
        _ _
  | Γ, _, _, .forLoopNRt (accTy := acc) (invTys := inv) update count init invs body, hc, H, W,
      V, hV => by
      subst hV
      obtain ⟨hu, hbody⟩ := hc
      refine lowerL_lane hm h64 k body hbody _ _ _ ?_
      refine (S.laneOf_pullV_cont H _ W k).trans ?_
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      rw [lookup_cnt64 h64 H count W k, ← S.laneOfTy_lookupH H init W k]
      exact foldl_lane _ _ _
        (fun a t => S.stepC_lane X hm h64 k update hu _ _ (S.laneOf_mapInvs H W k invs) t a)
        _ _
  | Γ, _, _, .forLoopNRtNested (accTy := acc) (invTys := inv) innerCount innerUpdate outerCount
      init invs body, hc, H, W, V, hV => by
      subst hV
      obtain ⟨hic, hiu, hbody⟩ := hc
      refine lowerL_lane hm h64 k body hbody _ _ _ ?_
      refine (S.laneOf_pullV_cont H _ W k).trans ?_
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      rw [lookup_cnt64 h64 H outerCount W k, ← S.laneOfTy_lookupH H init W k]
      refine foldl_lane _ _ _ (fun a jd => ?_) _ _
      rw [S.innerTrip_lane X hm h64 k innerCount hic _ _ (S.laneOf_mapInvs H W k invs) jd]
      exact foldl_lane _ _ _
        (fun a2 t => S.stepCNested_lane X hm h64 k innerUpdate hiu _ _
          (S.laneOf_mapInvs H W k invs) jd t a2) _ _
  | Γ, _, _, .whileNz (accTy := acc) (invTys := inv) update guard init invs body, hc, H, W,
      V, hV => by
      subst hV
      obtain ⟨hu, hbody⟩ := hc
      refine lowerL_lane hm h64 k body hbody _ _ _ ?_
      refine (S.laneOf_pullV_cont H _ W k).trans ?_
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      rw [lookup_cnt64 h64 H guard W k, ← S.laneOfTy_lookupH H init W k]
      exact foldl_lane _ _ _
        (fun a t => S.stepC_lane X hm h64 k update hu _ _ (S.laneOf_mapInvs H W k invs) t a)
        _ _
  | Γ, _, _, .forLoopBlock (accTy := acc) (invTys := inv) loopBody count init invs body, hc, H,
      W, V, hV => by
      subst hV
      obtain ⟨hlb, hbody⟩ := hc
      refine lowerL_lane hm h64 k body hbody _ _ _ ?_
      refine (S.laneOf_pullV_cont H _ W k).trans ?_
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      rw [lookup_cnt64 h64 H count W k, ← S.laneOfTy_lookupH H init W k]
      refine foldl_lane _ _ _ (fun a t => ?_) _ _
      refine lowerL_lane hm h64 k loopBody hlb (idx2Hom h64 acc inv) _ _ ?_
      rw [pullV_idx2Hom]
      show HVector.cons _ (HVector.cons (S.laneOfTy k (.reg 64) (cast _ (BitVec.ofNat 64 t)))
        (S.laneOf k inv (Expr.lookupArgs (S.mapInvs H invs) W))) = _
      rw [laneOfTy_reg64 h64, S.laneOf_mapInvs H W k invs]
      rfl

end LaneShape

/-! ## 10. Deciding coverage -/

namespace LaneShape

variable (S : LaneShape) (X : LaneExt S)

instance decCoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Decidable (S.CoveredExpr e) := by
  obtain ⟨op, h, args⟩ := e
  cases op <;> unfold CoveredExpr <;> infer_instance

instance decCoveredExprX {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Decidable (S.CoveredExprX X e) := by
  obtain ⟨op, h, args⟩ := e
  cases op <;> unfold CoveredExprX <;> infer_instance

instance decCoveredX : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → Decidable (S.CoveredX X c)
  | _, _, .ret _ => isTrue trivial
  | _, _, .var e body =>
      have := decCoveredX body
      inferInstanceAs (Decidable (S.CoveredExprX X e ∧ S.CoveredX X body))

instance decCoveredL : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : ComL Γ t) → Decidable (S.CoveredL X c)
  | _, _, .ret _ => isTrue trivial
  | _, _, .var e body =>
      have := decCoveredL body
      inferInstanceAs (Decidable (S.CoveredExprX X e ∧ S.CoveredL X body))
  | _, _, .forLoop loop _ body =>
      have := decCoveredL body
      inferInstanceAs (Decidable (S.CoveredX X loop.update ∧ S.CoveredL X body))
  | _, _, .forLoopN loop _ _ body =>
      have := decCoveredL body
      inferInstanceAs (Decidable (S.CoveredX X loop.update ∧ S.CoveredL X body))
  | _, _, .forLoopNRt update _ _ _ body =>
      have := decCoveredL body
      inferInstanceAs (Decidable (S.CoveredX X update ∧ S.CoveredL X body))
  | _, _, .forLoopNRtNested innerCount innerUpdate _ _ _ body =>
      have := decCoveredL body
      inferInstanceAs (Decidable
        (S.CoveredX X innerCount ∧ S.CoveredX X innerUpdate ∧ S.CoveredL X body))
  | _, _, .whileNz update _ _ _ body =>
      have := decCoveredL body
      inferInstanceAs (Decidable (S.CoveredX X update ∧ S.CoveredL X body))
  | _, _, .forLoopBlock loopBody _ _ _ body =>
      have := decCoveredL loopBody
      have := decCoveredL body
      inferInstanceAs (Decidable (S.CoveredL X loopBody ∧ S.CoveredL X body))

end LaneShape

/-! ## 11. The lane maps at the canonical homomorphism -/

open LaneShape in
/-- The lane map of a straight-line program with the extended lowering. -/
def laneMapStraight (S : LaneShape) (X : LaneExt S) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  S.lowerC X c (fun v => v)

open LaneShape in
/-- The lane map of a loop program, at a shape whose lanes are not 64 bits wide. -/
def laneMapLoop (S : LaneShape) (X : LaneExt S) (h64 : S.laneBits ≠ 64)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) :
    ComL (S.widenCtxt Γ) (S.widenTy t) :=
  S.lowerL X h64 c (fun v => v)

open LaneShape in
/-- **The straight-line lane theorem of the extended lowering.** For a covered program,
    lane `k` of the lane-mapped program's value is the scalar program's value on the
    lane-`k` valuation. -/
theorem laneMapStraight_denote (S : LaneShape) (X : LaneExt S)
    (hm : S.MulhiLane jasminExtSem) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (hc : S.CoveredX X c)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((laneMapStraight S X c).denote W) = c.denote (S.laneOf k Γ W) :=
  S.lowerC_lane X hm k c hc (fun v => v) W _ (by rw [pullV_id])

open LaneShape in
/-- **The loop lane theorem.** For a covered loop program at a shape whose lanes are not
    64 bits wide, lane `k` of the lane-mapped program's value is the scalar program's
    value on the lane-`k` valuation. -/
theorem laneMapLoop_denote (S : LaneShape) (X : LaneExt S) (h64 : S.laneBits ≠ 64)
    (hm : S.MulhiLane jasminExtSem) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (hc : S.CoveredL X c)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((laneMapLoop S X h64 c).denote W) = c.denote (S.laneOf k Γ W) :=
  S.lowerL_lane X hm h64 k c hc (fun v => v) W _ (by rw [pullV_id])

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
