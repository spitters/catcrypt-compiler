/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom

/-!
# The ZMM lane map: eight scalar `u64` programs in one AVX-512 register

`laneMapZmm` is the `Com jasminDialect → Com jasminDialect` transform that runs eight
independent copies of a scalar 64-bit program in the eight qword lanes of a ZMM
register: every `reg 64` value becomes a `reg 512`, every scalar binding
`regArith bop 64` becomes the packed binding `vpackZMM bop`, and every constant
`regConst 64 k` becomes the lane broadcast `regConst 512 (constZmm k).toNat`.

The transform is a `FieldDialectBlockDescent.BlockLoweringData` instance, the qword
ZMM counterpart of the dword YMM widening `Optimizer.Batch8`. Each covered op lowers
to a one-binding block; `blockLowerCom` splices the blocks. The type map sends
`reg 64` to `reg 512` and fixes every other type.

## Covered scalar ops

All nine `JasminBinOp`s at width 64 (`add`, `sub`, `mul`, `and`, `or`, `xor`, `andn`,
`shl`, `shr`) and `regConst 64 k`. `vpackZMM bop` denotes `zmmPackQ bop`, which
applies `bop.apply` at width 64 in each lane, reading the shift count of `shl` / `shr`
from the same lane of the second operand; so each packed op is the scalar op lane by
lane. Every other op takes an opaque nullary `extCall` fallback, outside the
`LaneMapZmmCovered` fragment the denotation theorem is stated over.

## Main definitions

* `widenZTy` / `widenZCtxt` / `mapVar`: the type, context and de Bruijn transports.
* `lowering`: the `BlockLoweringData jasminDialect jasminDialect`.
* `laneMapZmm`: the whole-program lane map.
* `laneOfTy` / `laneOf`: per-type and per-valuation extraction of qword lane `k`.
* `LaneMapZmmCovered`: the fragment on which the lane map is lane-preserving.

## Main results

* `laneOf_lookup`: reading a mapped variable and extracting lane `k` equals reading
  the original variable against the lane-`k` valuation.
* `blockOpLane`: each covered op's packed block, read at lane `k`, computes the
  scalar op on lane `k`.
* `laneMapZmm_denote`: for a covered program returning `reg 64`, lane `k` of the
  mapped program's denotation equals the scalar program's denotation on lane `k`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom
  (zmmPackQ_lane zmmOfLanes_zmmLane' constZmm)

/-! ## 1. Type, context and variable maps -/

/-- Widen `reg 64` to `reg 512`; fix every other Jasmin type. -/
@[implicit_reducible]
def widenZTy : JasminTy → JasminTy
  | .reg w => if w = 64 then .reg 512 else .reg w
  | t => t

/-- Context map: `widenZTy` pointwise. -/
@[implicit_reducible]
def widenZCtxt (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := Γ.map widenZTy

/-- `List.map` is definitionally `cons`-compatible. -/
theorem mapCtx_cons (t : JasminTy) (Γ : Ctxt jasminDialect) :
    widenZCtxt (t :: Γ) = widenZTy t :: widenZCtxt Γ := rfl

/-- de Bruijn index transport along `widenZTy`. -/
def mapVar {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → Ctxt.Var (widenZCtxt Γ) (widenZTy t)
  | .here => .here
  | .there v => .there (mapVar v)

/-! ## 2. The block lowering -/

/-- The lane-map lowering. Each covered scalar op becomes a one-binding packed block;
    every other op takes the opaque nullary-`extCall` fallback. -/
def lowering : BlockLoweringData jasminDialect jasminDialect where
  mapTy := widenZTy
  mapCtx := widenZCtxt
  mapCtx_cons := mapCtx_cons
  mapVar := mapVar
  lowerExprBlock := fun {_Γ t} e =>
    match e with
    | ⟨.regArith bop 64, h, .cons a (.cons b .nil)⟩ =>
        congrArg widenZTy h ▸
          Com.var ⟨.vpackZMM bop, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regConst 64 kk, h, .nil⟩ =>
        congrArg widenZTy h ▸
          Com.var ⟨.regConst 512 (constZmm kk).toNat, rfl, .nil⟩ (.ret .here)
    | ⟨_, _, _⟩ =>
        Com.var ⟨.extCall "laneMapZmm_uncovered" [] (widenZTy t), rfl, .nil⟩ (.ret .here)

/-- The lane map of a whole scalar program: eight `u64` lanes in one ZMM register. -/
def laneMapZmm {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect (widenZCtxt Γ) (widenZTy t) :=
  lowering.blockLowerCom c

/-! ## 3. Lane extraction -/

/-- Extract qword lane `k` of a mapped value. A mapped `reg 64` (a `reg 512`) yields
    its lane-`k` qword `zmmLane v k`; every other type passes through unchanged. -/
def laneOfTy (k : Fin 8) : (s : JasminTy) → ⟦widenZTy s⟧ → ⟦s⟧
  | .reg w, v => by
      by_cases h : w = 64
      · subst h; exact zmmLane v k
      · simp only [widenZTy, if_neg h] at v; exact v
  | .stackArr _ _, v => v
  | .inlineInt, v => v
  | .bool, v => v

/-- Lane extraction at `reg 64` is `zmmLane`. -/
theorem laneOfTy_reg64 (k : Fin 8) (v : ⟦widenZTy (.reg 64)⟧) :
    laneOfTy k (.reg 64) v = zmmLane v k := rfl

/-- Extract qword lane `k` of a whole mapped valuation, slot by slot. -/
def laneOf (k : Fin 8) : (Γ : Ctxt jasminDialect) →
    Ctxt.Valuation (widenZCtxt Γ) → Ctxt.Valuation Γ
  | [], _ => .nil
  | s :: _, W => .cons (laneOfTy k s W.head) (laneOf k _ W.tail)

/-- Reading a mapped variable and extracting lane `k` equals reading the original
    variable against the lane-`k` valuation. -/
theorem laneOf_lookup : {Γ : Ctxt jasminDialect} → {t : JasminTy} → (v : Ctxt.Var Γ t) →
    (W : Ctxt.Valuation (widenZCtxt Γ)) → (k : Fin 8) →
    laneOfTy k t ((mapVar v).lookup W) = v.lookup (laneOf k Γ W)
  | _, _, .here, W, _ => by cases W; rfl
  | _, _, .there w, W, k => by
      cases W with
      | cons _ rest => exact laneOf_lookup w rest k

/-- Lane `k` of the broadcast constant is the scalar constant. -/
theorem constZmm_lane (kk : Nat) (k : Fin 8) :
    zmmLane (BitVec.ofNat 512 (constZmm kk).toNat) k = BitVec.ofNat 64 kk := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, constZmm, zmmOfLanes_zmmLane']

/-! ## 4. The covered fragment -/

/-- The scalar ops `laneMapZmm` maps lane-preservingly: every `regArith bop 64` and
    every `regConst 64 k`. -/
def CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  match e.op with
  | .regArith _ w => w = 64
  | .regConst w _ => w = 64
  | _ => False

/-- A program whose every op is covered. -/
def LaneMapZmmCovered {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => CoveredExpr e ∧ LaneMapZmmCovered body

/-! ## 5. The per-op lane square -/

/-- **Per-op lane square.** For each covered op, the packed block read at qword lane
    `k` computes the scalar op on lane `k`. -/
theorem blockOpLane {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : CoveredExpr e) (W : Ctxt.Valuation (widenZCtxt Γ)) (k : Fin 8) :
    laneOfTy k t ((lowering.lowerExprBlock e).denote W) = e.denote (laneOf k Γ W) := by
  obtain ⟨op, rfl, args⟩ := e
  cases op <;> try (simp only [CoveredExpr] at he; done)
  case regArith bop w =>
    simp only [CoveredExpr] at he; subst he
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    have LA := laneOf_lookup a W k
    have LB := laneOf_lookup b W k
    simp only [laneOfTy_reg64] at LA LB
    show zmmLane (zmmPackQ bop ((mapVar a).lookup W) ((mapVar b).lookup W)) k
        = (⟨.regArith bop 64, rfl, .cons a (.cons b .nil)⟩ :
            Expr jasminDialect Γ (.reg 64)).denote (laneOf k Γ W)
    rw [zmmPackQ_lane, LA, LB]; rfl
  case regConst w kk =>
    simp only [CoveredExpr] at he; subst he
    cases args
    show zmmLane (BitVec.ofNat 512 (constZmm kk).toNat) k
        = (⟨.regConst 64 kk, rfl, .nil⟩ : Expr jasminDialect Γ (.reg 64)).denote (laneOf k Γ W)
    rw [constZmm_lane]; rfl

/-! ## 6. Whole-program lane preservation -/

/-- **`laneMapZmm` is lane-preserving.** For a covered program returning `reg 64`,
    qword lane `k` of the mapped program's denotation equals the scalar program's
    denotation on the lane-`k` valuation. The induction on the `Com` let-chain uses
    `spliceCom_denote` to peel each block and `blockOpLane` for each op. -/
theorem laneMapZmm_denote : {Γ : Ctxt jasminDialect} → (c : Com jasminDialect Γ (.reg 64)) →
    LaneMapZmmCovered c → (W : Ctxt.Valuation (widenZCtxt Γ)) → (k : Fin 8) →
    zmmLane ((laneMapZmm c).denote W) k = c.denote (laneOf k Γ W)
  | _, .ret v, _, W, k => laneOf_lookup v W k
  | Γ, .var e body, hc, W, k => by
      obtain ⟨he, hbody⟩ := hc
      have hop := blockOpLane e he W k
      show zmmLane ((spliceCom (lowering.lowerExprBlock e) (laneMapZmm body)).denote W) k
          = body.denote (Ctxt.Valuation.extend (laneOf k Γ W) (e.denote (laneOf k Γ W)))
      erw [spliceCom_denote]
      have IH := laneMapZmm_denote body hbody
        (Ctxt.Valuation.extend W ((lowering.lowerExprBlock e).denote W)) k
      refine IH.trans ?_
      congr 1
      show Ctxt.Valuation.extend (laneOf k Γ W)
          (laneOfTy k _ ((lowering.lowerExprBlock e).denote W))
          = Ctxt.Valuation.extend (laneOf k Γ W) (e.denote (laneOf k Γ W))
      rw [hop]

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm
