/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD
public import CatCrypt.Crypto.Optimizer.PackedArith256

/-!
# The lane map parametrised by a lane shape

`laneMapVec S` is the `Com jasminDialect → Com jasminDialect` transform that runs
`S.laneCount` independent copies of a scalar `S.laneBits`-bit program in the lanes of one
`S.regBits`-bit register. The lane shape `S : LaneShape` fixes the lane width, the lane
count, the register width, the lane read, the packed expression of each scalar
`JasminBinOp` it covers, the constant broadcast and, optionally, a high-multiply leaf.
The transform is a `FieldDialectBlockDescent.BlockLoweringData` instance: every
`reg S.laneBits` becomes a `reg S.regBits`, each covered op lowers to a one-binding
block, and every other op takes an opaque nullary `extCall` fallback.

Three shapes are instantiated: `qwordZmm` (eight 64-bit lanes, `vpackZMM`), `dwordZmm`
(sixteen 32-bit lanes, `vpackZMMd`, the leaf `zmm_mulhi32x16`) and `qwordYmm` (four
64-bit lanes on the 256-bit `vymm` ops). `qwordYmm` covers `add`, `sub`, `mul`, `and`,
`or`, `xor` and `andn`; the dialect has no 256-bit packed shift by a per-lane count
(`vpsllvq` / `vpsrlvq`), so `shl` and `shr` are outside its fragment.

## Main definitions

* `LaneShape`: the lane-shape record with its per-op lane laws.
* `LaneShape.widenTy` / `widenCtxt` / `mapVar`: the type, context and de Bruijn maps.
* `LaneShape.lowering`, `laneMapVec`: the block lowering and the whole-program map.
* `LaneShape.laneOfTy` / `laneOf`: extraction of lane `k` of a value and a valuation.
* `LaneShape.Covered`: the fragment on which the lane map is lane-preserving.
* `qwordZmm`, `dwordZmm`, `qwordYmm`: the three shapes.

## Main results

* `laneMapVec_denote`: for a covered program, lane `k` of the mapped program's value
  is the scalar program's value on lane `k` of the inputs.
* `laneMapVec_denote_agree`: lanes in a set `P` of the mapped program's value depend
  only on the lanes in `P` of the inputs.
* `laneMapZmm_eq_laneMapVec`, `laneMapZmmD_eq_laneMapVec`: the two ZMM lane maps are
  `laneMapVec` at `qwordZmm` and `dwordZmm` on their covered fragments.
* `laneMapZmm_denote_of_laneMapVec`, `laneMapZmmD_denote_of_laneMapVec`: the
  statements of `LaneMapZmm.laneMapZmm_denote` and `LaneMapZmmD.laneMapZmmD_denote`,
  derived from `laneMapVec_denote`.
* `laneMapZmm_low_lanes_agree`: lanes `0..3` of `laneMapZmm c` depend only on lanes
  `0..3` of the inputs.
* `laneMapYmm_denote`: the lane theorem at four 64-bit lanes on 256-bit registers.
* `laneMapZmm_low_lanes_eq_laneMapYmm`: on a program covered by `qwordYmm`, lanes
  `0..3` of `laneMapZmm c` are the lanes of `laneMapVec qwordYmm c` when the inputs
  agree on those lanes.
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

/-- A lane shape: `laneCount` lanes of `laneBits` bits in a `regBits`-bit register, the
    lane read, the packed expression of each covered scalar `JasminBinOp`, the constant
    broadcast, an optional high-multiply expression, the name of the uncovered
    fallback leaf, and the lane laws of the packed expressions and of the broadcast. -/
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

/-- Widen `reg S.laneBits` to `reg S.regBits`; fix every other Jasmin type. -/
@[implicit_reducible]
def widenTy : JasminTy → JasminTy
  | .reg w => if w = S.laneBits then .reg S.regBits else .reg w
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

/-- A mapped lane-width variable, read at the register type. -/
def wideVar {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits)
    (a : Ctxt.Var Γ (.reg w)) : Ctxt.Var (S.widenCtxt Γ) (.reg S.regBits) :=
  S.widenTy_reg hw ▸ S.mapVar a

/-! ## 3. The block lowering -/

/-- The block of a packed two-operand expression. -/
def packBlock {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits)
    (f : PackBuilder S.regBits) (a b : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w)) :=
  (S.widenTy_reg hw).symm ▸
    Com.var (f _ (S.wideVar hw a) (S.wideVar hw b)) (.ret .here)

/-- The block of a broadcast constant. -/
def constBlock {Γ : Ctxt jasminDialect} {w : Nat} (hw : w = S.laneBits) (kk : Nat) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy (.reg w)) :=
  (S.widenTy_reg hw).symm ▸
    Com.var ⟨.regConst S.regBits (S.bcast kk), rfl, .nil⟩ (.ret .here)

/-- The block of an uncovered op: an opaque nullary leaf. -/
def fallbackBlock (Γ : Ctxt jasminDialect) (t : JasminTy) :
    Com jasminDialect (S.widenCtxt Γ) (S.widenTy t) :=
  Com.var ⟨.extCall S.fallbackName [] (S.widenTy t), rfl, .nil⟩ (.ret .here)

/-- The per-op block: the packed op of a covered `regArith`, the broadcast of a
    `regConst`, the high-multiply expression of a `mulhi`, the fallback otherwise. -/
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

/-- Extract lane `k` of a mapped value. A mapped `reg S.laneBits` yields its lane `k`;
    every other type passes through unchanged. -/
def laneOfTy (k : Fin S.laneCount) : (s : JasminTy) → ⟦S.widenTy s⟧ → ⟦s⟧
  | .reg w, v =>
      if h : w = S.laneBits then
        cast (congrArg BitVec h.symm)
          (S.lane (cast (congrArg TyDenote.denote (S.widenTy_reg h)) v) k)
      else cast (by simp [widenTy, h]) v
  | .stackArr _ _, v => v
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

/-- Lane `k` of a constant block is the scalar constant. -/
theorem laneOfTy_constBlock (leafSem : LeafSem) {Γ : Ctxt jasminDialect} (kk : Nat)
    (W : Ctxt.Valuation (S.widenCtxt Γ)) (k : Fin S.laneCount) :
    S.laneOfTy k (.reg S.laneBits)
        (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (S.constBlock (Γ := Γ) rfl kk) W)
      = BitVec.ofNat S.laneBits kk := by
  rw [laneOfTy_lane, constBlock, denote_cast, toReg, cast_cast, cast_eq]
  exact S.const_lane kk k

/-! ## 5. The covered fragment -/

/-- The scalar ops the lane map maps lane-preservingly: a covered `regArith` at the
    lane width, a `regConst` at the lane width, and a `mulhi` at the lane width when the
    shape has a high multiply. -/
def CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  match e.op with
  | .regArith bop w => w = S.laneBits ∧ S.covers bop = true
  | .regConst w _ => w = S.laneBits
  | .mulhi w => w = S.laneBits ∧ S.mulhiExpr.isSome = true
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

/-! ## 8. Eight 64-bit lanes: `laneMapZmm` -/

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom (zmmPackQ_lane constZmm)

/-- Eight 64-bit lanes in a ZMM register, on the packed ops `vpackZMM`. -/
def qwordZmm : LaneShape where
  laneBits := 64
  laneCount := 8
  regBits := 512
  regBits_eq := rfl
  lane := zmmLane
  covers := fun _ => true
  packExpr := fun bop _ a b => ⟨.vpackZMM bop, rfl, .cons a (.cons b .nil)⟩
  bcast := fun kk => (constZmm kk).toNat
  mulhiExpr := none
  fallbackName := "laneMapZmm_uncovered"
  pack_lane := fun _ bop _ _ a b V k => zmmPackQ_lane bop (a.lookup V) (b.lookup V) k
  const_lane := LaneMapZmm.constZmm_lane

/-- The variable maps of `LaneMapZmm` and of `qwordZmm` agree. -/
theorem mapVar_qwordZmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (v : Ctxt.Var Γ t) → LaneMapZmm.mapVar v = qwordZmm.mapVar v
  | _, _, .here => rfl
  | _, _, .there v => congrArg Ctxt.Var.there (mapVar_qwordZmm v)

/-- On a covered op, the blocks of `LaneMapZmm` and of `qwordZmm` agree. -/
theorem lowerExprBlock_qwordZmm {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : LaneMapZmm.CoveredExpr e) :
    LaneMapZmm.lowering.lowerExprBlock e = qwordZmm.lowerExprBlock e := by
  obtain ⟨op, rfl, args⟩ := e
  cases op <;> try (simp only [LaneMapZmm.CoveredExpr] at he; done)
  case regArith bop w =>
    simp only [LaneMapZmm.CoveredExpr] at he
    subst he
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    show Com.var (⟨JasminOp.vpackZMM bop, rfl,
          .cons (LaneMapZmm.mapVar a) (.cons (LaneMapZmm.mapVar b) .nil)⟩ :
            Expr jasminDialect (LaneMapZmm.widenZCtxt Γ) (.reg 512)) (.ret .here)
        = Com.var (⟨JasminOp.vpackZMM bop, rfl,
          .cons (qwordZmm.mapVar a) (.cons (qwordZmm.mapVar b) .nil)⟩ :
            Expr jasminDialect (LaneMapZmm.widenZCtxt Γ) (.reg 512)) (.ret .here)
    rw [mapVar_qwordZmm, mapVar_qwordZmm]
  case regConst w kk =>
    simp only [LaneMapZmm.CoveredExpr] at he
    subst he
    cases args
    rfl

/-- On a covered program, `laneMapZmm` is `laneMapVec qwordZmm`. -/
theorem laneMapZmm_eq_laneMapVec : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → LaneMapZmm.LaneMapZmmCovered c →
    LaneMapZmm.laneMapZmm c = laneMapVec qwordZmm c
  | _, _, .ret v, _ => congrArg Com.ret (mapVar_qwordZmm v)
  | _, _, .var e body, hc => by
      show spliceCom (LaneMapZmm.lowering.lowerExprBlock e) (LaneMapZmm.laneMapZmm body)
        = spliceCom (qwordZmm.lowerExprBlock e) (laneMapVec qwordZmm body)
      rw [lowerExprBlock_qwordZmm e hc.1, laneMapZmm_eq_laneMapVec body hc.2]
      rfl

/-- The lane extractions of `LaneMapZmm` and of `qwordZmm` agree. -/
theorem laneOfTy_qwordZmm (k : Fin 8) :
    (s : JasminTy) → (v : ⟦LaneMapZmm.widenZTy s⟧) →
    LaneMapZmm.laneOfTy k s v = qwordZmm.laneOfTy k s v
  | .reg w, v => by
      by_cases h : w = 64
      · subst h; rfl
      · simp only [LaneMapZmm.laneOfTy, LaneShape.laneOfTy, dif_neg h,
          dif_neg (show ¬w = qwordZmm.laneBits from h)]
        rfl
  | .stackArr _ _, _ => rfl
  | .inlineInt, _ => rfl
  | .bool, _ => rfl

/-- The valuation lane extractions of `LaneMapZmm` and of `qwordZmm` agree. -/
theorem laneOf_qwordZmm (k : Fin 8) : (Γ : Ctxt jasminDialect) →
    (W : Ctxt.Valuation (LaneMapZmm.widenZCtxt Γ)) →
    LaneMapZmm.laneOf k Γ W = qwordZmm.laneOf k Γ W
  | [], _ => rfl
  | s :: Γ, W => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [laneOfTy_qwordZmm k s, laneOf_qwordZmm k Γ]
      rfl

/-- A program covered by `LaneMapZmm` is covered by `qwordZmm`. -/
theorem covered_qwordZmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → LaneMapZmm.LaneMapZmmCovered c → qwordZmm.Covered c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, hc => by
      refine ⟨?_, covered_qwordZmm body hc.2⟩
      have he := hc.1
      obtain ⟨op, rfl, args⟩ := e
      cases op <;> simp_all [LaneMapZmm.CoveredExpr, LaneShape.CoveredExpr, qwordZmm]

/-- **`LaneMapZmm.laneMapZmm_denote` from `laneMapVec_denote`.** For a covered program
    returning `reg 64`, qword lane `k` of `laneMapZmm c` is the scalar program's value
    on the lane-`k` valuation. -/
theorem laneMapZmm_denote_of_laneMapVec {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : LaneMapZmm.LaneMapZmmCovered c)
    (W : Ctxt.Valuation (LaneMapZmm.widenZCtxt Γ)) (k : Fin 8) :
    zmmLane ((LaneMapZmm.laneMapZmm c).denote W) k = c.denote (LaneMapZmm.laneOf k Γ W) := by
  have h := laneMapVec_denote qwordZmm jasminExtSem
    (fun _ hf => by simp [qwordZmm] at hf) c (covered_qwordZmm c hc) W k
  rw [denoteWith_extSem] at h
  rw [laneMapZmm_eq_laneMapVec c hc, laneOf_qwordZmm]
  exact h

/-- **Lane restriction of `laneMapZmm`.** Qword lanes `0..3` of a covered program's
    mapped value depend only on qword lanes `0..3` of the inputs. -/
theorem laneMapZmm_low_lanes_agree {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : LaneMapZmm.LaneMapZmmCovered c)
    (W W' : Ctxt.Valuation (LaneMapZmm.widenZCtxt Γ))
    (hW : ∀ k : Fin 8, k.val < 4 → LaneMapZmm.laneOf k Γ W = LaneMapZmm.laneOf k Γ W')
    (k : Fin 8) (hk : k.val < 4) :
    zmmLane ((LaneMapZmm.laneMapZmm c).denote W) k
      = zmmLane ((LaneMapZmm.laneMapZmm c).denote W') k := by
  rw [laneMapZmm_denote_of_laneMapVec c hc, laneMapZmm_denote_of_laneMapVec c hc, hW k hk]

/-! ## 9. Sixteen 32-bit lanes: `laneMapZmmD` -/

open CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane (zmmPackD_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom (bcastD)

/-- Sixteen 32-bit lanes in a ZMM register, on the packed ops `vpackZMMd` and the
    high-multiply leaf `zmm_mulhi32x16`. -/
def dwordZmm : LaneShape where
  laneBits := 32
  laneCount := 16
  regBits := 512
  regBits_eq := rfl
  lane := zmmLane32
  covers := fun _ => true
  packExpr := fun bop _ a b => ⟨.vpackZMMd bop, rfl, .cons a (.cons b .nil)⟩
  bcast := fun kk => (bcastD (BitVec.ofNat 32 kk)).toNat
  mulhiExpr := some fun _ a b =>
    ⟨.extCall LaneMapZmmD.mulhiLeafName [.reg 512, .reg 512] (.reg 512), rfl,
      .cons a (.cons b .nil)⟩
  fallbackName := "laneMapZmmD_uncovered"
  pack_lane := fun _ bop _ _ a b V k => zmmPackD_lane bop (a.lookup V) (b.lookup V) k
  const_lane := LaneMapZmmD.constD_lane

/-- `MulHi32Leaf` is the high-multiply law of `dwordZmm`. -/
theorem mulhiLane_dwordZmm (leafSem : LeafSem) (hleaf : LaneMapZmmD.MulHi32Leaf leafSem) :
    dwordZmm.MulhiLane leafSem := by
  intro f hf Γ a b V k
  cases Option.some.inj hf
  exact hleaf _ _ k

/-- The variable maps of `LaneMapZmmD` and of `dwordZmm` agree. -/
theorem mapVar_dwordZmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (v : Ctxt.Var Γ t) → LaneMapZmmD.mapVar v = dwordZmm.mapVar v
  | _, _, .here => rfl
  | _, _, .there v => congrArg Ctxt.Var.there (mapVar_dwordZmm v)

/-- On a covered op, the blocks of `LaneMapZmmD` and of `dwordZmm` agree. -/
theorem lowerExprBlock_dwordZmm {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : LaneMapZmmD.CoveredExpr e) :
    LaneMapZmmD.lowering.lowerExprBlock e = dwordZmm.lowerExprBlock e := by
  obtain ⟨op, rfl, args⟩ := e
  cases op <;> try (simp only [LaneMapZmmD.CoveredExpr] at he; done)
  case regArith bop w =>
    simp only [LaneMapZmmD.CoveredExpr] at he
    subst he
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    show Com.var (⟨JasminOp.vpackZMMd bop, rfl,
          .cons (LaneMapZmmD.mapVar a) (.cons (LaneMapZmmD.mapVar b) .nil)⟩ :
            Expr jasminDialect (LaneMapZmmD.widenDCtxt Γ) (.reg 512)) (.ret .here)
        = Com.var (⟨JasminOp.vpackZMMd bop, rfl,
          .cons (dwordZmm.mapVar a) (.cons (dwordZmm.mapVar b) .nil)⟩ :
            Expr jasminDialect (LaneMapZmmD.widenDCtxt Γ) (.reg 512)) (.ret .here)
    rw [mapVar_dwordZmm, mapVar_dwordZmm]
  case regConst w kk =>
    simp only [LaneMapZmmD.CoveredExpr] at he
    subst he
    cases args
    rfl
  case mulhi w =>
    simp only [LaneMapZmmD.CoveredExpr] at he
    subst he
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    show Com.var (⟨JasminOp.extCall LaneMapZmmD.mulhiLeafName [.reg 512, .reg 512] (.reg 512),
          rfl, .cons (LaneMapZmmD.mapVar a) (.cons (LaneMapZmmD.mapVar b) .nil)⟩ :
            Expr jasminDialect (LaneMapZmmD.widenDCtxt Γ) (.reg 512)) (.ret .here)
        = Com.var (⟨JasminOp.extCall LaneMapZmmD.mulhiLeafName [.reg 512, .reg 512] (.reg 512),
          rfl, .cons (dwordZmm.mapVar a) (.cons (dwordZmm.mapVar b) .nil)⟩ :
            Expr jasminDialect (LaneMapZmmD.widenDCtxt Γ) (.reg 512)) (.ret .here)
    rw [mapVar_dwordZmm, mapVar_dwordZmm]

/-- On a covered program, `laneMapZmmD` is `laneMapVec dwordZmm`. -/
theorem laneMapZmmD_eq_laneMapVec : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → LaneMapZmmD.LaneMapZmmDCovered c →
    LaneMapZmmD.laneMapZmmD c = laneMapVec dwordZmm c
  | _, _, .ret v, _ => congrArg Com.ret (mapVar_dwordZmm v)
  | _, _, .var e body, hc => by
      show spliceCom (LaneMapZmmD.lowering.lowerExprBlock e) (LaneMapZmmD.laneMapZmmD body)
        = spliceCom (dwordZmm.lowerExprBlock e) (laneMapVec dwordZmm body)
      rw [lowerExprBlock_dwordZmm e hc.1, laneMapZmmD_eq_laneMapVec body hc.2]
      rfl

/-- The lane extractions of `LaneMapZmmD` and of `dwordZmm` agree. -/
theorem laneOfTy_dwordZmm (k : Fin 16) :
    (s : JasminTy) → (v : ⟦LaneMapZmmD.widenDTy s⟧) →
    LaneMapZmmD.laneOfTy k s v = dwordZmm.laneOfTy k s v
  | .reg w, v => by
      by_cases h : w = 32
      · subst h; rfl
      · simp only [LaneMapZmmD.laneOfTy, LaneShape.laneOfTy, dif_neg h,
          dif_neg (show ¬w = dwordZmm.laneBits from h)]
        rfl
  | .stackArr _ _, _ => rfl
  | .inlineInt, _ => rfl
  | .bool, _ => rfl

/-- The valuation lane extractions of `LaneMapZmmD` and of `dwordZmm` agree. -/
theorem laneOf_dwordZmm (k : Fin 16) : (Γ : Ctxt jasminDialect) →
    (W : Ctxt.Valuation (LaneMapZmmD.widenDCtxt Γ)) →
    LaneMapZmmD.laneOf k Γ W = dwordZmm.laneOf k Γ W
  | [], _ => rfl
  | s :: Γ, W => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [laneOfTy_dwordZmm k s, laneOf_dwordZmm k Γ]
      rfl

/-- A program covered by `LaneMapZmmD` is covered by `dwordZmm`. -/
theorem covered_dwordZmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → LaneMapZmmD.LaneMapZmmDCovered c → dwordZmm.Covered c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, hc => by
      refine ⟨?_, covered_dwordZmm body hc.2⟩
      have he := hc.1
      obtain ⟨op, rfl, args⟩ := e
      cases op <;> simp_all [LaneMapZmmD.CoveredExpr, LaneShape.CoveredExpr, dwordZmm]

/-- **`LaneMapZmmD.laneMapZmmD_denote` from `laneMapVec_denote`.** For a covered program
    returning `reg 32` and a leaf semantics satisfying `MulHi32Leaf`, dword lane `k` of
    `laneMapZmmD c` under `jasminDenoteWith leafSem` is the scalar program's value on
    the lane-`k` valuation. -/
theorem laneMapZmmD_denote_of_laneMapVec (leafSem : LeafSem)
    (hleaf : LaneMapZmmD.MulHi32Leaf leafSem) {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 32)) (hc : LaneMapZmmD.LaneMapZmmDCovered c)
    (W : Ctxt.Valuation (LaneMapZmmD.widenDCtxt Γ)) (k : Fin 16) :
    zmmLane32 (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        (LaneMapZmmD.laneMapZmmD c) W) k
      = c.denote (LaneMapZmmD.laneOf k Γ W) := by
  rw [laneMapZmmD_eq_laneMapVec c hc, laneOf_dwordZmm]
  exact laneMapVec_denote dwordZmm leafSem (mulhiLane_dwordZmm leafSem hleaf) c
    (covered_dwordZmm c hc) W k

/-! ## 10. Four 64-bit lanes on 256-bit registers -/

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
  (yQwordW yOfQwordsW vpaddqW vpsubqW vpmullqW vpandW vporW vpxorW vpandnW)

/-- The 256-bit packed expression of a scalar op on four 64-bit lanes. `shl` and `shr`
    have no 256-bit packed form with a per-lane count; they are not covered, and their
    entry `vpaddq` is never emitted. -/
def ymmPackExpr : JasminBinOp → PackBuilder 256
  | .add => fun _ a b => ⟨.vymm .vpaddq, rfl, .cons a (.cons b .nil)⟩
  | .sub => fun _ a b => ⟨.vymm .vpsubq, rfl, .cons a (.cons b .nil)⟩
  | .mul => fun _ a b => ⟨.vymm .vpmullq, rfl, .cons a (.cons b .nil)⟩
  | .and => fun _ a b => ⟨.vymm .vpand, rfl, .cons a (.cons b .nil)⟩
  | .or => fun _ a b => ⟨.vymm .vpor, rfl, .cons a (.cons b .nil)⟩
  | .xor => fun _ a b => ⟨.vymm .vpxor, rfl, .cons a (.cons b .nil)⟩
  | .andn => fun _ a b => ⟨.vymm .vpandn, rfl, .cons a (.cons b .nil)⟩
  | .shl => fun _ a b => ⟨.vymm .vpaddq, rfl, .cons a (.cons b .nil)⟩
  | .shr => fun _ a b => ⟨.vymm .vpaddq, rfl, .cons a (.cons b .nil)⟩

/-- The scalar ops with a 256-bit packed form on four 64-bit lanes: all but `shl` and
    `shr`. -/
def ymmCovers : JasminBinOp → Bool
  | .shl => false
  | .shr => false
  | _ => true

/-- Qword lane `k` of a bitwise and-not is the and-not of the lanes. -/
theorem yQwordW_andn (a b : BitVec 256) (k : Fin 4) :
    yQwordW (vpandnW a b) k.val = (~~~yQwordW a k.val) &&& yQwordW b k.val := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [vpandnW, yQwordW, BitVec.getElem_extractLsb', BitVec.getElem_and,
    BitVec.getElem_not, BitVec.getLsbD_and, BitVec.getLsbD_not]
  have h : 64 * k.val + i < 256 := by omega
  simp [h]

/-- Four 64-bit lanes in a YMM register, on the `vymm` ops. -/
def qwordYmm : LaneShape where
  laneBits := 64
  laneCount := 4
  regBits := 256
  regBits_eq := rfl
  lane := fun v k => yQwordW v k.val
  covers := ymmCovers
  packExpr := ymmPackExpr
  bcast := fun kk => (yOfQwordsW (fun _ => BitVec.ofNat 64 kk)).toNat
  mulhiExpr := none
  fallbackName := "laneMapYmm_uncovered"
  pack_lane := by
    intro _ bop hc _ a b V k
    cases bop
    case add =>
      show yQwordW (vpaddqW (a.lookup V) (b.lookup V)) k.val = _
      rw [vpaddqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]
      rfl
    case sub =>
      show yQwordW (vpsubqW (a.lookup V) (b.lookup V)) k.val = _
      rw [vpsubqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]
      rfl
    case mul =>
      show yQwordW (vpmullqW (a.lookup V) (b.lookup V)) k.val = _
      rw [vpmullqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]
      rfl
    case and =>
      show yQwordW (vpandW (a.lookup V) (b.lookup V)) k.val = _
      exact BitVec.extractLsb'_and
    case or =>
      show yQwordW (vporW (a.lookup V) (b.lookup V)) k.val = _
      exact BitVec.extractLsb'_or
    case xor =>
      show yQwordW (vpxorW (a.lookup V) (b.lookup V)) k.val = _
      exact BitVec.extractLsb'_xor
    case andn =>
      show yQwordW (vpandnW (a.lookup V) (b.lookup V)) k.val = _
      exact yQwordW_andn _ _ k
    case shl => exact absurd hc (by decide)
    case shr => exact absurd hc (by decide)
  const_lane := by
    intro kk k
    show yQwordW (BitVec.ofNat 256 (yOfQwordsW _).toNat) k.val = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]

/-- **The lane theorem at four 64-bit lanes.** For a program covered by `qwordYmm`
    returning `reg 64`, qword lane `k` of the 256-bit mapped program's value is the
    scalar program's value on the lane-`k` valuation. -/
theorem laneMapYmm_denote (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : qwordYmm.Covered c)
    (W : Ctxt.Valuation (qwordYmm.widenCtxt Γ)) (k : Fin 4) :
    yQwordW (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec qwordYmm c) W) k.val
      = c.denote (qwordYmm.laneOf k Γ W) :=
  laneMapVec_denote qwordYmm leafSem (fun _ hf => by simp [qwordYmm] at hf) c hc W k

/-- A program covered by `qwordYmm` is covered by `LaneMapZmm`. -/
theorem laneMapZmmCovered_of_qwordYmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → qwordYmm.Covered c → LaneMapZmm.LaneMapZmmCovered c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, hc => by
      refine ⟨?_, laneMapZmmCovered_of_qwordYmm body hc.2⟩
      have he := hc.1
      obtain ⟨op, rfl, args⟩ := e
      cases op <;> simp_all [LaneMapZmm.CoveredExpr, LaneShape.CoveredExpr, qwordYmm]

/-- **The 256-bit map is the low half of the 512-bit map.** For a program covered by
    `qwordYmm` returning `reg 64`, if qword lane `k < 4` of the ZMM inputs `W` agrees
    with qword lane `k` of the YMM inputs `W'`, then qword lane `k` of `laneMapZmm c` at
    `W` is qword lane `k` of `laneMapVec qwordYmm c` at `W'`. -/
theorem laneMapZmm_low_lanes_eq_laneMapYmm {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : qwordYmm.Covered c)
    (W : Ctxt.Valuation (LaneMapZmm.widenZCtxt Γ)) (W' : Ctxt.Valuation (qwordYmm.widenCtxt Γ))
    (hW : ∀ k : Fin 4,
      LaneMapZmm.laneOf (Fin.castLE (by decide) k) Γ W = qwordYmm.laneOf k Γ W')
    (k : Fin 4) :
    zmmLane ((LaneMapZmm.laneMapZmm c).denote W) (Fin.castLE (by decide) k)
      = yQwordW ((laneMapVec qwordYmm c).denote W') k.val := by
  have h := laneMapYmm_denote jasminExtSem c hc W' k
  rw [denoteWith_extSem] at h
  rw [laneMapZmm_denote_of_laneMapVec c (laneMapZmmCovered_of_qwordYmm c hc), hW k, h]

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
