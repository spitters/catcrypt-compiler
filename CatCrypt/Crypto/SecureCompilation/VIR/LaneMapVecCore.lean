/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-!
# The lane map parametrised by a lane shape

`laneMapVec S` is the `Com jasminDialect → Com jasminDialect` transform that runs
`S.laneCount` independent copies of a scalar `S.laneBits`-bit program in the lanes of one
`S.regBits`-bit register. The lane shape `S : LaneShape` fixes the lane width, the lane
count, the register width, the lane read, the packed expression of each scalar
`JasminBinOp` it covers, the packed block of each immediate shift or rotate it covers,
the constant broadcast, optionally a high-multiply expression, and whether stack arrays
of lane-width words widen to arrays of registers (structure-of-arrays layout). The
transform is a `FieldDialectBlockDescent.BlockLoweringData` instance: every
`reg S.laneBits` becomes a `reg S.regBits`, each covered op lowers to a block, and every
other op takes an opaque nullary `extCall` fallback.

The shapes live beside the packed ops they use: `qwordZmm` in `LaneMapZmm`, `dwordZmm`
in `LaneMapZmmD`, `dwordYmm` in `Optimizer.Batch8`, `qwordYmm` in `LaneMapVec`.

## Main definitions

* `LaneShape`: the lane-shape record with its per-op lane laws.
* `ImmOp`: the immediate-count shifts and rotate, with their scalar meaning.
* `LaneShape.widenTy` / `widenCtxt` / `mapVar`: the type, context and de Bruijn maps.
* `LaneShape.lowering`, `laneMapVec`: the block lowering and the whole-program map.
* `LaneShape.laneOfTy` / `laneOf`: extraction of lane `k` of a value and a valuation.
* `LaneShape.Covered`: the fragment on which the lane map is lane-preserving.

## Main results

* `LaneShape.blockOpLane`: each covered op's block, read at lane `k`, computes the
  scalar op on lane `k`.
* `laneMapVec_denote`: for a covered program, lane `k` of the mapped program's value
  is the scalar program's value on lane `k` of the inputs.
* `laneMapVec_denote_agree`: lanes in a set `P` of the mapped program's value depend
  only on the lanes in `P` of the inputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-! ## 1. The lane shape -/

/-- An `extCall` leaf semantics, the parameter of `jasminDenoteWith`. -/
abbrev LeafSem : Type :=
  (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧

/-- A two-operand packed expression builder at register width `R`. -/
abbrev PackBuilder (R : Nat) : Type :=
  (Γ : Ctxt jasminDialect) → Ctxt.Var Γ (.reg R) → Ctxt.Var Γ (.reg R) →
    Expr jasminDialect Γ (.reg R)

/-- A one-operand packed block builder at register width `R`. -/
abbrev UnaryBuilder (R : Nat) : Type :=
  (Γ : Ctxt jasminDialect) → Ctxt.Var Γ (.reg R) → Com jasminDialect Γ (.reg R)

/-- The immediate-count ops of the scalar dialect: `shlImm`, `shrImm`, `sarImm` and
    `rorImm`. -/
inductive ImmOp where
  | shl
  | shr
  | sar
  | ror
deriving DecidableEq

/-- The scalar meaning of an immediate-count op at count `n`, as `jasminDenote` gives
    it. -/
def ImmOp.apply {w : Nat} : ImmOp → Nat → BitVec w → BitVec w
  | .shl, n, a => a <<< n
  | .shr, n, a => a >>> n
  | .sar, n, a => BitVec.sshiftRight a n
  | .ror, n, a => a.rotateRight n

/-- A lane shape: `laneCount` lanes of `laneBits` bits in a `regBits`-bit register, the
    lane read, the packed expression of each covered scalar `JasminBinOp`, the packed
    block of each lowered immediate-count op and the counts it is correct at, the
    constant broadcast, an optional high-multiply expression, whether lane-width stack
    arrays widen, the name of the uncovered fallback leaf, and the lane laws. -/
structure LaneShape where
  /-- Width of one lane. -/
  laneBits : Nat
  /-- Number of lanes. -/
  laneCount : Nat
  /-- Width of the register. -/
  regBits : Nat
  /-- The register holds exactly the lanes. -/
  regBits_eq : regBits = laneBits * laneCount
  /-- Lane `k` of a register value. -/
  lane : BitVec regBits → Fin laneCount → BitVec laneBits
  /-- The scalar ops with a packed counterpart. -/
  covers : JasminBinOp → Bool
  /-- The packed expression of a scalar op. -/
  packExpr : JasminBinOp → PackBuilder regBits
  /-- The register constant whose every lane is the scalar constant. -/
  bcast : Nat → Nat
  /-- The packed high multiply, if the shape has one. -/
  mulhiExpr : Option (PackBuilder regBits)
  /-- The packed block of an immediate-count op at each count, if the shape lowers it. -/
  immBlock : ImmOp → Option (Nat → UnaryBuilder regBits)
  /-- The counts at which the packed block of an immediate-count op is lane-correct. -/
  immCovers : ImmOp → Nat → Bool
  /-- Whether `stackArr laneBits n` widens to `stackArr regBits n`, element `i` of the
      widened array holding element `i` of every lane's array. -/
  arrWiden : Bool
  /-- The name of the nullary leaf an uncovered op lowers to. -/
  fallbackName : String
  /-- Lane `k` of a covered packed op is the scalar op on lane `k` of its operands. -/
  pack_lane : ∀ (leafSem : LeafSem) (bop : JasminBinOp), covers bop = true →
    ∀ (Γ : Ctxt jasminDialect) (a b : Ctxt.Var Γ (.reg regBits))
      (V : Ctxt.Valuation Γ) (k : Fin laneCount),
      lane (@Expr.denote _ _ _ (jasminDenoteWith leafSem) _ _ (packExpr bop Γ a b) V) k
        = bop.apply (lane (a.lookup V) k) (lane (b.lookup V) k)
  /-- Every lane of the broadcast constant is the scalar constant. -/
  const_lane : ∀ (kk : Nat) (k : Fin laneCount),
    lane (BitVec.ofNat regBits (bcast kk)) k = BitVec.ofNat laneBits kk
  /-- Lane `k` of a lowered immediate-count block, at a covered count, is the scalar op
      on lane `k` of its operand. -/
  imm_lane : ∀ (leafSem : LeafSem) (op : ImmOp) (f : Nat → UnaryBuilder regBits),
    immBlock op = some f → ∀ (n : Nat), immCovers op n = true →
    ∀ (Γ : Ctxt jasminDialect) (a : Ctxt.Var Γ (.reg regBits))
      (V : Ctxt.Valuation Γ) (k : Fin laneCount),
      lane (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (f n Γ a) V) k
        = op.apply n (lane (a.lookup V) k)
  /-- The `reg 64` index of a widened array load is not a lane-width register. -/
  arr_index : arrWiden = true → laneBits ≠ 64
  /-- The lanes of the zero register are zero (the read of an empty array). -/
  lane_zero : arrWiden = true → ∀ k : Fin laneCount, lane 0 k = 0

namespace LaneShape

variable (S : LaneShape)

/-- Under `leafSem`, lane `k` of the high-multiply expression is `mulHiW` of lane `k`
    of its operands. -/
def MulhiLane (leafSem : LeafSem) : Prop :=
  ∀ f, S.mulhiExpr = some f →
    ∀ (Γ : Ctxt jasminDialect) (a b : Ctxt.Var Γ (.reg S.regBits))
      (V : Ctxt.Valuation Γ) (k : Fin S.laneCount),
      S.lane (@Expr.denote _ _ _ (jasminDenoteWith leafSem) _ _ (f Γ a b) V) k
        = mulHiW (S.lane (a.lookup V) k) (S.lane (b.lookup V) k)

/-! ## 2. Type, context and variable maps -/

/-- Widen `reg S.laneBits` to `reg S.regBits` and, when `S.arrWiden`, `stackArr S.laneBits n`
    to `stackArr S.regBits n`; fix every other Jasmin type. -/
@[implicit_reducible]
def widenTy : JasminTy → JasminTy
  | .reg w => if w = S.laneBits then .reg S.regBits else .reg w
  | .stackArr w n =>
      cond S.arrWiden (if w = S.laneBits then .stackArr S.regBits n else .stackArr w n)
        (.stackArr w n)
  | t => t

/-- Context map: `widenTy` pointwise. -/
@[implicit_reducible]
def widenCtxt (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := Γ.map S.widenTy

/-- `List.map` is definitionally `cons`-compatible. -/
theorem mapCtx_cons (t : JasminTy) (Γ : Ctxt jasminDialect) :
    S.widenCtxt (t :: Γ) = S.widenTy t :: S.widenCtxt Γ := rfl

/-- de Bruijn index transport along `widenTy`. -/
def mapVar {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → Ctxt.Var (S.widenCtxt Γ) (S.widenTy t)
  | .here => .here
  | .there v => .there (mapVar v)

/-- A lane-width register widens to the register width. -/
theorem widenTy_reg {w : Nat} (hw : w = S.laneBits) :
    S.widenTy (.reg w) = .reg S.regBits := by
  simp [widenTy, hw]

/-- A register of another width is fixed. -/
theorem widenTy_reg_of_ne {w : Nat} (hw : w ≠ S.laneBits) :
    S.widenTy (.reg w) = .reg w := by
  simp [widenTy, hw]

/-- A lane-width stack array widens to an array of registers when `S.arrWiden`. -/
theorem widenTy_arr {w : Nat} (hA : S.arrWiden = true) (hw : w = S.laneBits) (n : Nat) :
    S.widenTy (.stackArr w n) = .stackArr S.regBits n := by
  simp [widenTy, hA, hw]

/-- Every other stack array is fixed. -/
theorem widenTy_arr_of_not {w : Nat} (h : ¬(S.arrWiden = true ∧ w = S.laneBits)) (n : Nat) :
    S.widenTy (.stackArr w n) = .stackArr w n := by
  unfold widenTy
  cases hA : S.arrWiden
  · rfl
  · have hw : w ≠ S.laneBits := fun hw => h ⟨hA, hw⟩
    simp [hw]

/-- A mapped lane-width variable, read at the register type. -/
def wideVar {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits)
    (a : Ctxt.Var Γ (.reg w)) : Ctxt.Var (S.widenCtxt Γ) (.reg S.regBits) :=
  S.widenTy_reg hw ▸ S.mapVar a

/-- A mapped lane-width stack array, read at the widened array type. -/
def arrVar {Γ : Ctxt jasminDialect} {w n : Nat} (hA : S.arrWiden = true)
    (hw : w = S.laneBits) (arr : Ctxt.Var Γ (.stackArr w n)) :
    Ctxt.Var (S.widenCtxt Γ) (.stackArr S.regBits n) :=
  S.widenTy_arr hA hw n ▸ S.mapVar arr

/-- A mapped `reg 64` array index, read at `reg 64`. -/
def idxVar {Γ : Ctxt jasminDialect} (hA : S.arrWiden = true) (idx : Ctxt.Var Γ (.reg 64)) :
    Ctxt.Var (S.widenCtxt Γ) (.reg 64) :=
  S.widenTy_reg_of_ne (fun h => S.arr_index hA h.symm) ▸ S.mapVar idx

/-! ## 3. The block lowering -/

/-- The block of a packed two-operand expression. -/
def packBlock {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits)
    (f : PackBuilder S.regBits) (a b : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w)) :=
  (S.widenTy_reg hw).symm ▸
    Com.var (f _ (S.wideVar hw a) (S.wideVar hw b)) (.ret .here)

/-- The block of a packed one-operand builder. -/
def unaryBlock {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits)
    (f : UnaryBuilder S.regBits) (a : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w)) :=
  (S.widenTy_reg hw).symm ▸ f _ (S.wideVar hw a)

/-- The block of a broadcast constant. -/
def constBlock {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits) (kk : Nat) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w)) :=
  (S.widenTy_reg hw).symm ▸
    Com.var ⟨.regConst S.regBits (S.bcast kk), rfl, .nil⟩ (.ret .here)

/-- The block of a widened array load: the load of the widened element at the same
    index. -/
def loadBlock {Γ : Ctxt jasminDialect} {w : Nat} (hA : S.arrWiden = true)
    (hw : w = S.laneBits) (n : Nat) (arr : Ctxt.Var Γ (.stackArr w n))
    (idx : Ctxt.Var Γ (.reg 64)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w)) :=
  (S.widenTy_reg hw).symm ▸
    Com.var ⟨.stackLoad S.regBits n, rfl,
      .cons (S.arrVar hA hw arr) (.cons (S.idxVar hA idx) .nil)⟩ (.ret .here)

/-- The block of an uncovered op: an opaque nullary leaf. -/
def fallbackBlock (Γ : Ctxt jasminDialect) (t : JasminTy) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  Com.var ⟨.extCall S.fallbackName [] (S.widenTy t), rfl, .nil⟩ (.ret .here)

/-- The block of an immediate-count op: the shape's packed block at a lane-width
    operand, the fallback otherwise. -/
def immLower {Γ : Ctxt jasminDialect} {t : JasminTy} {w : Nat} (op : ImmOp) (n : Nat)
    (h : JasminTy.reg w = t) (a : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  match S.immBlock op with
  | some f =>
      if hw : w = S.laneBits then congrArg S.widenTy h ▸ S.unaryBlock hw (f n) a
      else S.fallbackBlock Γ t
  | none => S.fallbackBlock Γ t

/-- The per-op block: the packed op of a covered `regArith`, the broadcast of a
    `regConst`, the high-multiply expression of a `mulhi`, the immediate-count block of a
    `shlImm` / `shrImm` / `sarImm` / `rorImm`, the widened load of a `stackLoad`, the
    fallback otherwise. -/
def lowerExprBlock {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  match e with
  | ⟨.regArith bop w, h, .cons a (.cons b .nil)⟩ =>
      if hw : w = S.laneBits ∧ S.covers bop = true then
        congrArg S.widenTy h ▸ S.packBlock hw.1 (S.packExpr bop) a b
      else S.fallbackBlock Γ t
  | ⟨.regConst w kk, h, .nil⟩ =>
      if hw : w = S.laneBits then congrArg S.widenTy h ▸ S.constBlock hw kk
      else S.fallbackBlock Γ t
  | ⟨.mulhi w, h, .cons a (.cons b .nil)⟩ =>
      match S.mulhiExpr with
      | some f =>
          if hw : w = S.laneBits then congrArg S.widenTy h ▸ S.packBlock hw f a b
          else S.fallbackBlock Γ t
      | none => S.fallbackBlock Γ t
  | ⟨.shlImm _ n, h, .cons a .nil⟩ => S.immLower .shl n h a
  | ⟨.shrImm _ n, h, .cons a .nil⟩ => S.immLower .shr n h a
  | ⟨.sarImm _ n, h, .cons a .nil⟩ => S.immLower .sar n h a
  | ⟨.rorImm _ n, h, .cons a .nil⟩ => S.immLower .ror n h a
  | ⟨.stackLoad w n, h, .cons arr (.cons idx .nil)⟩ =>
      if hw : S.arrWiden = true ∧ w = S.laneBits then
        congrArg S.widenTy h ▸ S.loadBlock hw.1 hw.2 n arr idx
      else S.fallbackBlock Γ t
  | ⟨_, _, _⟩ => S.fallbackBlock Γ t

/-- The lane-map lowering of the shape. -/
def lowering : BlockLoweringData jasminDialect jasminDialect where
  mapTy := S.widenTy
  mapCtx := S.widenCtxt
  mapCtx_cons := S.mapCtx_cons
  mapVar := S.mapVar
  lowerExprBlock := S.lowerExprBlock

end LaneShape

/-- The lane map of a whole scalar program at lane shape `S`. -/
def laneMapVec (S : LaneShape) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  S.lowering.blockLowerCom c

namespace LaneShape

variable (S : LaneShape)

/-! ## 4. Lane extraction -/

/-- A value of the widened lane type, read at the register type. -/
def toReg (v : ⟦S.widenTy (.reg S.laneBits)⟧) : BitVec S.regBits :=
  cast (congrArg TyDenote.denote (S.widenTy_reg rfl)) v

/-- Extract lane `k` of a mapped value. A mapped `reg S.laneBits` yields its lane `k`, a
    widened stack array the array of its elements' lanes `k`; every other type passes
    through unchanged. -/
def laneOfTy (k : Fin S.laneCount) : (s : JasminTy) → ⟦S.widenTy s⟧ → ⟦s⟧
  | .reg w, v =>
      if h : w = S.laneBits then
        cast (congrArg BitVec h.symm)
          (S.lane (cast (congrArg TyDenote.denote (S.widenTy_reg h)) v) k)
      else cast (by simp [widenTy, h]) v
  | .stackArr w n, v =>
      if h : S.arrWiden = true ∧ w = S.laneBits then
        cast (congrArg (fun w => Fin n → BitVec w) h.2.symm)
          (fun i => S.lane ((cast (congrArg TyDenote.denote (S.widenTy_arr h.1 h.2 n)) v) i) k)
      else cast (congrArg TyDenote.denote (S.widenTy_arr_of_not h n)) v
  | .inlineInt, v => v
  | .bool, v => v

/-- Lane extraction at the lane type is the lane read. -/
theorem laneOfTy_lane (k : Fin S.laneCount) (v : ⟦S.widenTy (.reg S.laneBits)⟧) :
    S.laneOfTy k (.reg S.laneBits) v = S.lane (S.toReg v) k := by
  simp only [laneOfTy, toReg]
  rfl

/-- Extract lane `k` of a whole mapped valuation, slot by slot. -/
def laneOf (k : Fin S.laneCount) : (Γ : Ctxt jasminDialect) →
    Ctxt.Valuation (S.widenCtxt Γ) → Ctxt.Valuation Γ
  | [], _ => .nil
  | s :: _, W => .cons (S.laneOfTy k s W.head) (laneOf k _ W.tail)

/-- Reading a mapped variable and extracting lane `k` equals reading the original
    variable against the lane-`k` valuation. -/
theorem laneOf_lookup : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (v : Ctxt.Var Γ t) → (W : Ctxt.Valuation (S.widenCtxt Γ)) → (k : Fin S.laneCount) →
    S.laneOfTy k t ((S.mapVar v).lookup W) = v.lookup (S.laneOf k Γ W)
  | _, _, .here, W, _ => by cases W; rfl
  | _, _, .there w, W, k => by
      cases W with
      | cons _ rest => exact laneOf_lookup w rest k

/-- Reading a type-cast variable is the cast of the read. -/
theorem lookup_cast {Γ : Ctxt jasminDialect} {t t' : JasminTy} (h : t = t')
    (v : Ctxt.Var Γ t) (W : Ctxt.Valuation Γ) :
    (h ▸ v : Ctxt.Var Γ t').lookup W = cast (congrArg TyDenote.denote h) (v.lookup W) := by
  subst h; rfl

/-- Denoting a type-cast program is the cast of the denotation. -/
theorem denote_cast (D : DialectDenote jasminDialect) {Γ : Ctxt jasminDialect}
    {t t' : JasminTy} (h : t = t') (c : Com jasminDialect Γ t) (W : Ctxt.Valuation Γ) :
    @Com.denote _ _ _ D _ _ (h ▸ c) W
      = cast (congrArg TyDenote.denote h) (@Com.denote _ _ _ D _ _ c W) := by
  subst h; rfl

/-- Lane `k` of a mapped lane-width variable, read at the register type. -/
theorem lane_wideVar {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ (.reg S.laneBits))
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.lane ((S.wideVar rfl a).lookup W) k = a.lookup (S.laneOf k Γ W) := by
  rw [← S.laneOf_lookup a W k, laneOfTy_lane, wideVar, lookup_cast]
  rfl

/-- Lane `k` of each element of a mapped lane-width array, read at the widened array
    type, is the lane-`k` array. -/
theorem lane_arrVar {Γ : Ctxt jasminDialect} {n : Nat} (hA : S.arrWiden = true)
    (arr : Ctxt.Var Γ (.stackArr S.laneBits n)) (W : Ctxt.Valuation (S.widenCtxt Γ))
    (k : Fin S.laneCount) :
    (fun i => S.lane ((S.arrVar hA rfl arr).lookup W i) k) = arr.lookup (S.laneOf k Γ W) := by
  rw [← S.laneOf_lookup arr W k, arrVar, lookup_cast]
  simp only [laneOfTy, hA, and_self, dite_true]
  rfl

/-- A mapped `reg 64` index, read at `reg 64`, is the index of every lane. -/
theorem idxVar_lookup {Γ : Ctxt jasminDialect} (hA : S.arrWiden = true)
    (idx : Ctxt.Var Γ (.reg 64)) (W : Ctxt.Valuation (S.widenCtxt Γ))
    (k : Fin S.laneCount) :
    (S.idxVar hA idx).lookup W = idx.lookup (S.laneOf k Γ W) := by
  have hne : (64 : Nat) ≠ S.laneBits := fun h => S.arr_index hA h.symm
  rw [← S.laneOf_lookup idx W k, idxVar, lookup_cast]
  simp only [laneOfTy, dif_neg hne]

/-- Lane `k` of an array read is the read of the lane-`k` array. -/
theorem lane_stackGet (hA : S.arrWiden = true) {n : Nat} (arr : Fin n → BitVec S.regBits)
    (m : Nat) (k : Fin S.laneCount) :
    S.lane (stackGet arr m) k = stackGet (fun i => S.lane (arr i) k) m := by
  cases n with
  | zero => exact S.lane_zero hA k
  | succ _ => rfl

/-- Lane `k` of a packed block is lane `k` of its expression. -/
theorem laneOfTy_packBlock (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (f : PackBuilder S.regBits) (a b : Ctxt.Var Γ (.reg S.laneBits))
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits)
        (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (S.packBlock rfl f a b) W)
      = S.lane (@Expr.denote _ _ _ (jasminDenoteWith leafSem) _ _
          (f _ (S.wideVar rfl a) (S.wideVar rfl b)) W) k := by
  rw [laneOfTy_lane, packBlock, denote_cast, toReg, cast_cast, cast_eq]
  rfl

/-- Lane `k` of a one-operand block is lane `k` of its builder's value. -/
theorem laneOfTy_unaryBlock (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (f : UnaryBuilder S.regBits) (a : Ctxt.Var Γ (.reg S.laneBits))
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits)
        (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (S.unaryBlock rfl f a) W)
      = S.lane (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
          (f _ (S.wideVar rfl a)) W) k := by
  rw [laneOfTy_lane, unaryBlock, denote_cast, toReg, cast_cast, cast_eq]

/-- Lane `k` of a constant block is the scalar constant. -/
theorem laneOfTy_constBlock (leafSem : LeafSem) {Γ : Ctxt jasminDialect} (kk : Nat)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits)
        (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (S.constBlock (Γ := Γ) rfl kk) W)
      = BitVec.ofNat S.laneBits kk := by
  rw [laneOfTy_lane, constBlock, denote_cast, toReg, cast_cast, cast_eq]
  exact S.const_lane kk k

/-- Lane `k` of a widened load is the load of the lane-`k` array. -/
theorem laneOfTy_loadBlock (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (hA : S.arrWiden = true) (n : Nat) (arr : Ctxt.Var Γ (.stackArr S.laneBits n))
    (idx : Ctxt.Var Γ (.reg 64)) (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits)
        (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (S.loadBlock hA rfl n arr idx) W)
      = stackGet (arr.lookup (S.laneOf k Γ W)) (idx.lookup (S.laneOf k Γ W)).toNat := by
  rw [laneOfTy_lane, loadBlock, denote_cast, toReg, cast_cast, cast_eq]
  show S.lane (stackGet ((S.arrVar hA rfl arr).lookup W) ((S.idxVar hA idx).lookup W).toNat) k
    = _
  rw [S.lane_stackGet hA, S.lane_arrVar hA, S.idxVar_lookup hA idx W k]

/-- Lane `k` of a covered immediate-count block is the scalar op on lane `k`. -/
theorem laneOfTy_immLower (leafSem : LeafSem) {Γ : Ctxt jasminDialect} (op : ImmOp)
    (n : Nat) (a : Ctxt.Var Γ (.reg S.laneBits)) (hs : (S.immBlock op).isSome = true)
    (hc : S.immCovers op n = true) (W : Ctxt.Valuation (S.widenCtxt Γ))
    (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits)
        (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (S.immLower op n rfl a) W)
      = op.apply n (a.lookup (S.laneOf k Γ W)) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hs
  have hblk : S.immLower op n rfl a = S.unaryBlock rfl (f n) a := by
    unfold immLower
    rw [hf]
    exact dif_pos rfl
  rw [hblk, laneOfTy_unaryBlock, S.imm_lane leafSem op f hf n hc, lane_wideVar]

/-! ## 5. The covered fragment -/

/-- The scalar ops the lane map maps lane-preservingly: a covered `regArith` at the
    lane width, a `regConst` at the lane width, a `mulhi` at the lane width when the
    shape has a high multiply, an immediate-count op at the lane width and a covered
    count when the shape lowers it, and a lane-width `stackLoad` when arrays widen. -/
def CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  match e.op with
  | .regArith bop w => w = S.laneBits ∧ S.covers bop = true
  | .regConst w _ => w = S.laneBits
  | .mulhi w => w = S.laneBits ∧ S.mulhiExpr.isSome = true
  | .shlImm w n => w = S.laneBits ∧ (S.immBlock .shl).isSome = true ∧ S.immCovers .shl n = true
  | .shrImm w n => w = S.laneBits ∧ (S.immBlock .shr).isSome = true ∧ S.immCovers .shr n = true
  | .sarImm w n => w = S.laneBits ∧ (S.immBlock .sar).isSome = true ∧ S.immCovers .sar n = true
  | .rorImm w n => w = S.laneBits ∧ (S.immBlock .ror).isSome = true ∧ S.immCovers .ror n = true
  | .stackLoad w _ => S.arrWiden = true ∧ w = S.laneBits
  | _ => False

/-- A program whose every op is covered. -/
def Covered {Γ : Ctxt jasminDialect} {t : JasminTy} : Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => S.CoveredExpr e ∧ Covered body

/-! ## 6. The per-op lane square -/

/-- **Per-op lane square.** For each covered op, the block denoted with
    `jasminDenoteWith leafSem` and read at lane `k` computes the scalar op on lane `k`,
    given the high-multiply law. -/
theorem blockOpLane (leafSem : LeafSem) (hm : S.MulhiLane leafSem)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : S.CoveredExpr e) (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        (S.lowerExprBlock e) W) = e.denote (S.laneOf k Γ W) := by
  obtain ⟨op, rfl, args⟩ := e
  cases op <;> try (simp only [CoveredExpr] at he; done)
  case regArith bop w =>
    obtain ⟨hw, hc⟩ := he
    subst hw
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    have hblk : S.lowerExprBlock (⟨.regArith bop S.laneBits, rfl, .cons a (.cons b .nil)⟩ :
        Expr jasminDialect Γ (.reg S.laneBits)) = S.packBlock rfl (S.packExpr bop) a b := by
      exact dif_pos (And.intro rfl hc)
    change S.laneOfTy k (.reg S.laneBits) _ = _
    rw [hblk, laneOfTy_packBlock, S.pack_lane leafSem bop hc, lane_wideVar, lane_wideVar]
    rfl
  case regConst w kk =>
    simp only [CoveredExpr] at he
    subst he
    cases args
    have hblk : S.lowerExprBlock (⟨.regConst S.laneBits kk, rfl, .nil⟩ :
        Expr jasminDialect Γ (.reg S.laneBits)) = S.constBlock rfl kk := by
      exact dif_pos rfl
    change S.laneOfTy k (.reg S.laneBits) _ = _
    rw [hblk, laneOfTy_constBlock]
    rfl
  case mulhi w =>
    obtain ⟨hw, hs⟩ := he
    subst hw
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hs
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    have hblk : S.lowerExprBlock (⟨.mulhi S.laneBits, rfl, .cons a (.cons b .nil)⟩ :
        Expr jasminDialect Γ (.reg S.laneBits)) = S.packBlock rfl f a b := by
      show (match S.mulhiExpr with
        | some f => if hw : S.laneBits = S.laneBits then S.packBlock hw f a b
            else S.fallbackBlock Γ (.reg S.laneBits)
        | none => S.fallbackBlock Γ (.reg S.laneBits)) = _
      rw [hf]
      exact dif_pos rfl
    change S.laneOfTy k (.reg S.laneBits) _ = _
    rw [hblk, laneOfTy_packBlock, hm f hf, lane_wideVar, lane_wideVar]
    rfl
  case shlImm w n =>
    obtain ⟨hw, hs, hc⟩ := he
    subst hw
    cases args; rename_i a rest
    cases rest
    exact S.laneOfTy_immLower leafSem .shl n a hs hc W k
  case shrImm w n =>
    obtain ⟨hw, hs, hc⟩ := he
    subst hw
    cases args; rename_i a rest
    cases rest
    exact S.laneOfTy_immLower leafSem .shr n a hs hc W k
  case sarImm w n =>
    obtain ⟨hw, hs, hc⟩ := he
    subst hw
    cases args; rename_i a rest
    cases rest
    exact S.laneOfTy_immLower leafSem .sar n a hs hc W k
  case rorImm w n =>
    obtain ⟨hw, hs, hc⟩ := he
    subst hw
    cases args; rename_i a rest
    cases rest
    exact S.laneOfTy_immLower leafSem .ror n a hs hc W k
  case stackLoad w n =>
    obtain ⟨hA, hw⟩ := he
    subst hw
    cases args; rename_i arr rest
    cases rest; rename_i idx rest2
    cases rest2
    have hblk : S.lowerExprBlock (⟨.stackLoad S.laneBits n, rfl, .cons arr (.cons idx .nil)⟩ :
        Expr jasminDialect Γ (.reg S.laneBits)) = S.loadBlock hA rfl n arr idx := by
      exact dif_pos (And.intro hA rfl)
    change S.laneOfTy k (.reg S.laneBits) _ = _
    rw [hblk, laneOfTy_loadBlock]
    rfl

end LaneShape

/-! ## 7. Whole-program lane preservation -/

open LaneShape in
/-- **`laneMapVec` is lane-preserving.** For a covered program and a leaf semantics
    satisfying the high-multiply law, lane `k` of the mapped program's denotation under
    `jasminDenoteWith leafSem` equals the scalar program's `jasminDenote` denotation on
    the lane-`k` valuation. -/
theorem laneMapVec_denote (S : LaneShape) (leafSem : LeafSem) (hm : S.MulhiLane leafSem) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    S.Covered c → (W : Ctxt.Valuation (S.widenCtxt Γ)) → (k : Fin S.laneCount) →
    S.laneOfTy k t (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec S c) W)
      = c.denote (S.laneOf k Γ W)
  | _, _, .ret v, _, W, k => S.laneOf_lookup v W k
  | Γ, _, .var e body, hc, W, k => by
      obtain ⟨he, hbody⟩ := hc
      have hop := S.blockOpLane leafSem hm e he W k
      show S.laneOfTy k _ (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
            (spliceCom (S.lowerExprBlock e) (laneMapVec S body)) W)
          = body.denote (Ctxt.Valuation.extend (S.laneOf k Γ W) (e.denote (S.laneOf k Γ W)))
      erw [@spliceCom_denote _ _ _ (jasminDenoteWith leafSem)]
      have IH := laneMapVec_denote S leafSem hm body hbody
        (Ctxt.Valuation.extend W
          (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (S.lowerExprBlock e) W)) k
      refine IH.trans ?_
      congr 1
      show Ctxt.Valuation.extend (S.laneOf k Γ W)
          (S.laneOfTy k _ (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
            (S.lowerExprBlock e) W))
          = Ctxt.Valuation.extend (S.laneOf k Γ W) (e.denote (S.laneOf k Γ W))
      rw [hop]

/-- The lane theorem at a program returning the lane type, read with the lane read. -/
theorem laneMapVec_denote_lane (S : LaneShape) (leafSem : LeafSem)
    (hm : S.MulhiLane leafSem) {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg S.laneBits)) (hc : S.Covered c)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.lane (S.toReg (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec S c) W)) k
      = c.denote (S.laneOf k Γ W) := by
  rw [← LaneShape.laneOfTy_lane]
  exact laneMapVec_denote S leafSem hm c hc W k

/-- **Lane restriction.** The lanes in `P` of a covered mapped program's value depend
    only on the lanes in `P` of the inputs. -/
theorem laneMapVec_denote_agree (S : LaneShape) (leafSem : LeafSem)
    (hm : S.MulhiLane leafSem) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (hc : S.Covered c) (P : Fin S.laneCount → Prop)
    (W W' : Ctxt.Valuation (S.widenCtxt Γ))
    (hW : ∀ k, P k → S.laneOf k Γ W = S.laneOf k Γ W') (k : Fin S.laneCount) (hk : P k) :
    S.laneOfTy k t (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec S c) W)
      = S.laneOfTy k t
          (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec S c) W') := by
  rw [laneMapVec_denote S leafSem hm c hc, laneMapVec_denote S leafSem hm c hc, hW k hk]

/-- At the default leaf semantics `jasminExtSem`, `jasminDenoteWith` is `jasminDenote`. -/
private theorem denoteWith_extSem : jasminDenoteWith jasminExtSem = jasminDenote := by
  unfold jasminDenoteWith
  congr 1
  funext op
  cases op <;> rfl

/-- The lane theorem under the default denotation `jasminDenote`, for a shape without a
    high multiply. -/
theorem laneMapVec_denote_default (S : LaneShape) (hm : S.mulhiExpr = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) (hc : S.Covered c)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((laneMapVec S c).denote W) = c.denote (S.laneOf k Γ W) := by
  have h := laneMapVec_denote S jasminExtSem (fun f hf => by rw [hm] at hf; cases hf) c hc W k
  rw [denoteWith_extSem] at h
  exact h

/-- The per-op lane square under the default denotation `jasminDenote`, for a shape
    without a high multiply. -/
theorem LaneShape.blockOpLane_default (S : LaneShape) (hm : S.mulhiExpr = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : S.CoveredExpr e) (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k t ((S.lowerExprBlock e).denote W) = e.denote (S.laneOf k Γ W) := by
  have h := S.blockOpLane jasminExtSem (fun f hf => by rw [hm] at hf; cases hf) e he W k
  rw [denoteWith_extSem] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
