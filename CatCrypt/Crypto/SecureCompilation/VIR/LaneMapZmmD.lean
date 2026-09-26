/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom

/-!
# The dword ZMM lane map: sixteen scalar `u32` programs in one AVX-512 register

`laneMapZmmD` is the `Com jasminDialect → Com jasminDialect` transform that runs sixteen
independent copies of a scalar 32-bit program in the sixteen dword lanes of a ZMM
register: every `reg 32` value becomes a `reg 512`, every scalar binding
`regArith bop 32` becomes the packed binding `vpackZMMd bop`, every constant
`regConst 32 k` becomes the lane broadcast `regConst 512 (bcastD (BitVec.ofNat 32 k)).toNat`,
and every `mulhi 32` becomes the two-operand leaf `extCall "zmm_mulhi32x16"`.

The transform is a `FieldDialectBlockDescent.BlockLoweringData` instance, the dword
counterpart of the qword lane map `LaneMapZmm`. Each covered op lowers to a one-binding
block; `blockLowerCom` splices the blocks. The type map sends `reg 32` to `reg 512` and
fixes every other type. Lane `k : Fin 16` of a `reg 512` value is `zmmLane32 v k`, bits
`32k .. 32k+31`, the layout `zmmPackD` uses.

## Covered scalar ops

All nine `JasminBinOp`s at width 32 (`add`, `sub`, `mul`, `and`, `or`, `xor`, `andn`,
`shl`, `shr`), `regConst 32 k` and `mulhi 32`. `vpackZMMd bop` denotes `zmmPackD bop`,
which applies `bop.apply` at width 32 in each lane, reading the shift count of `shl` /
`shr` from the same lane of the second operand; so each packed op is the scalar op lane
by lane. The leaf `zmm_mulhi32x16` has no fixed meaning in `jasminDenote`; the lane
theorem denotes the mapped program with `jasminDenoteWith leafSem` under `MulHi32Leaf
leafSem`, the hypothesis that the leaf computes `mulHiW` in every dword lane. Every
other op takes an opaque nullary `extCall` fallback, outside the `LaneMapZmmDCovered`
fragment.

## Main definitions

* `widenDTy` / `widenDCtxt` / `mapVar`: the type, context and de Bruijn transports.
* `lowering`: the `BlockLoweringData jasminDialect jasminDialect`.
* `laneMapZmmD`: the whole-program lane map.
* `laneOfTy` / `laneOf`: per-type and per-valuation extraction of dword lane `k`.
* `MulHi32Leaf`: the lane-wise specification of the `zmm_mulhi32x16` leaf.
* `LaneMapZmmDCovered`: the fragment on which the lane map is lane-preserving.

## Main results

* `laneOf_lookup`: reading a mapped variable and extracting lane `k` equals reading
  the original variable against the lane-`k` valuation.
* `blockOpLane`: each covered op's packed block, denoted with `jasminDenoteWith leafSem`
  and read at lane `k`, computes the scalar op on lane `k`.
* `laneMapZmmD_denote`: for a covered program returning `reg 32`, lane `k` of the
  mapped program's denotation under `jasminDenoteWith leafSem` equals the scalar
  program's `jasminDenote` denotation on lane `k`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane (zmmPackD_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom (bcastD bcastD_lane)

/-! ## 1. Type, context and variable maps -/

/-- Widen `reg 32` to `reg 512`; fix every other Jasmin type. -/
@[implicit_reducible]
def widenDTy : JasminTy → JasminTy
  | .reg w => if w = 32 then .reg 512 else .reg w
  | t => t

/-- Context map: `widenDTy` pointwise. -/
@[implicit_reducible]
def widenDCtxt (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := Γ.map widenDTy

/-- `List.map` is definitionally `cons`-compatible. -/
theorem mapCtx_cons (t : JasminTy) (Γ : Ctxt jasminDialect) :
    widenDCtxt (t :: Γ) = widenDTy t :: widenDCtxt Γ := rfl

/-- de Bruijn index transport along `widenDTy`. -/
def mapVar {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → Ctxt.Var (widenDCtxt Γ) (widenDTy t)
  | .here => .here
  | .there v => .there (mapVar v)

/-! ## 2. The block lowering -/

/-- The name of the sixteen-lane high-multiply leaf. -/
def mulhiLeafName : String := "zmm_mulhi32x16"

/-- The dword lane-map lowering. Each covered scalar op becomes a one-binding packed
    block; every other op takes the opaque nullary-`extCall` fallback. -/
def lowering : BlockLoweringData jasminDialect jasminDialect where
  mapTy := widenDTy
  mapCtx := widenDCtxt
  mapCtx_cons := mapCtx_cons
  mapVar := mapVar
  lowerExprBlock := fun {_Γ t} e =>
    match e with
    | ⟨.regArith bop 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widenDTy h ▸
          Com.var ⟨.vpackZMMd bop, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regConst 32 kk, h, .nil⟩ =>
        congrArg widenDTy h ▸
          Com.var ⟨.regConst 512 (bcastD (BitVec.ofNat 32 kk)).toNat, rfl, .nil⟩ (.ret .here)
    | ⟨.mulhi 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widenDTy h ▸
          Com.var ⟨.extCall mulhiLeafName [.reg 512, .reg 512] (.reg 512), rfl,
            .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨_, _, _⟩ =>
        Com.var ⟨.extCall "laneMapZmmD_uncovered" [] (widenDTy t), rfl, .nil⟩ (.ret .here)

/-- The dword lane map of a whole scalar program: sixteen `u32` lanes in one ZMM
    register. -/
def laneMapZmmD {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect (widenDCtxt Γ) (widenDTy t) :=
  lowering.blockLowerCom c

/-! ## 3. Lane extraction -/

/-- Extract dword lane `k` of a mapped value. A mapped `reg 32` (a `reg 512`) yields
    its lane-`k` dword `zmmLane32 v k`; every other type passes through unchanged. -/
def laneOfTy (k : Fin 16) : (s : JasminTy) → ⟦widenDTy s⟧ → ⟦s⟧
  | .reg w, v => by
      by_cases h : w = 32
      · subst h; exact zmmLane32 v k
      · simp only [widenDTy, if_neg h] at v; exact v
  | .stackArr _ _, v => v
  | .inlineInt, v => v
  | .bool, v => v

/-- Lane extraction at `reg 32` is `zmmLane32`. -/
theorem laneOfTy_reg32 (k : Fin 16) (v : ⟦widenDTy (.reg 32)⟧) :
    laneOfTy k (.reg 32) v = zmmLane32 v k := rfl

/-- Extract dword lane `k` of a whole mapped valuation, slot by slot. -/
def laneOf (k : Fin 16) : (Γ : Ctxt jasminDialect) →
    Ctxt.Valuation (widenDCtxt Γ) → Ctxt.Valuation Γ
  | [], _ => .nil
  | s :: _, W => .cons (laneOfTy k s W.head) (laneOf k _ W.tail)

/-- Reading a mapped variable and extracting lane `k` equals reading the original
    variable against the lane-`k` valuation. -/
theorem laneOf_lookup : {Γ : Ctxt jasminDialect} → {t : JasminTy} → (v : Ctxt.Var Γ t) →
    (W : Ctxt.Valuation (widenDCtxt Γ)) → (k : Fin 16) →
    laneOfTy k t ((mapVar v).lookup W) = v.lookup (laneOf k Γ W)
  | _, _, .here, W, _ => by cases W; rfl
  | _, _, .there w, W, k => by
      cases W with
      | cons _ rest => exact laneOf_lookup w rest k

/-- Lane `k` of the broadcast constant is the scalar constant. -/
theorem constD_lane (kk : Nat) (k : Fin 16) :
    zmmLane32 (BitVec.ofNat 512 (bcastD (BitVec.ofNat 32 kk)).toNat) k
      = BitVec.ofNat 32 kk := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, bcastD_lane]

/-! ## 4. The leaf specification and the covered fragment -/

/-- The `zmm_mulhi32x16` leaf of `leafSem` computes, in every dword lane `k`, the high
    word `mulHiW` of the product of lane `k` of its two operands. -/
def MulHi32Leaf
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧) : Prop :=
  ∀ (a b : BitVec 512) (k : Fin 16),
    zmmLane32 (leafSem mulhiLeafName [.reg 512, .reg 512] (.reg 512) (.cons a (.cons b .nil))) k
      = mulHiW (zmmLane32 a k) (zmmLane32 b k)

/-- The scalar ops `laneMapZmmD` maps lane-preservingly: every `regArith bop 32`,
    every `regConst 32 k` and `mulhi 32`. -/
def CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  match e.op with
  | .regArith _ w => w = 32
  | .regConst w _ => w = 32
  | .mulhi w => w = 32
  | _ => False

/-- A program whose every op is covered. -/
def LaneMapZmmDCovered {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => CoveredExpr e ∧ LaneMapZmmDCovered body

/-! ## 5. The per-op lane square -/

/-- **Per-op lane square.** For each covered op, the packed block denoted with
    `jasminDenoteWith leafSem` and read at dword lane `k` computes the scalar op on
    lane `k`, given `MulHi32Leaf leafSem`. -/
theorem blockOpLane
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧)
    (hleaf : MulHi32Leaf leafSem) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : CoveredExpr e) (W : Ctxt.Valuation (widenDCtxt Γ))
    (k : Fin 16) :
    laneOfTy k t (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        (lowering.lowerExprBlock e) W) = e.denote (laneOf k Γ W) := by
  obtain ⟨op, rfl, args⟩ := e
  cases op <;> try (simp only [CoveredExpr] at he; done)
  case regArith bop w =>
    simp only [CoveredExpr] at he; subst he
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    have LA := laneOf_lookup a W k
    have LB := laneOf_lookup b W k
    simp only [laneOfTy_reg32] at LA LB
    show zmmLane32 (zmmPackD bop ((mapVar a).lookup W) ((mapVar b).lookup W)) k
        = (⟨.regArith bop 32, rfl, .cons a (.cons b .nil)⟩ :
            Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
    rw [zmmPackD_lane, LA, LB]; rfl
  case regConst w kk =>
    simp only [CoveredExpr] at he; subst he
    cases args
    show zmmLane32 (BitVec.ofNat 512 (bcastD (BitVec.ofNat 32 kk)).toNat) k
        = (⟨.regConst 32 kk, rfl, .nil⟩ : Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
    rw [constD_lane]; rfl
  case mulhi w =>
    simp only [CoveredExpr] at he; subst he
    cases args; rename_i a rest
    cases rest; rename_i b rest2
    cases rest2
    have LA := laneOf_lookup a W k
    have LB := laneOf_lookup b W k
    simp only [laneOfTy_reg32] at LA LB
    show zmmLane32 (leafSem mulhiLeafName [.reg 512, .reg 512] (.reg 512)
          (.cons ((mapVar a).lookup W) (.cons ((mapVar b).lookup W) .nil))) k
        = (⟨.mulhi 32, rfl, .cons a (.cons b .nil)⟩ :
            Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
    rw [hleaf, LA, LB]; rfl

/-! ## 6. Whole-program lane preservation -/

/-- **`laneMapZmmD` is lane-preserving.** For a covered program returning `reg 32` and
    a leaf semantics satisfying `MulHi32Leaf`, dword lane `k` of the mapped program's
    denotation under `jasminDenoteWith leafSem` equals the scalar program's
    `jasminDenote` denotation on the lane-`k` valuation. The induction on the `Com`
    let-chain uses `spliceCom_denote` to peel each block and `blockOpLane` for each
    op. -/
theorem laneMapZmmD_denote
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧)
    (hleaf : MulHi32Leaf leafSem) :
    {Γ : Ctxt jasminDialect} → (c : Com jasminDialect Γ (.reg 32)) →
    LaneMapZmmDCovered c → (W : Ctxt.Valuation (widenDCtxt Γ)) → (k : Fin 16) →
    zmmLane32 (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapZmmD c) W) k
      = c.denote (laneOf k Γ W)
  | _, .ret v, _, W, k => laneOf_lookup v W k
  | Γ, .var e body, hc, W, k => by
      obtain ⟨he, hbody⟩ := hc
      have hop := blockOpLane leafSem hleaf e he W k
      show zmmLane32 (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
            (spliceCom (lowering.lowerExprBlock e) (laneMapZmmD body)) W) k
          = body.denote (Ctxt.Valuation.extend (laneOf k Γ W) (e.denote (laneOf k Γ W)))
      erw [@spliceCom_denote _ _ _ (jasminDenoteWith leafSem)]
      have IH := laneMapZmmD_denote leafSem hleaf body hbody
        (Ctxt.Valuation.extend W
          (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (lowering.lowerExprBlock e) W)) k
      refine IH.trans ?_
      congr 1
      show Ctxt.Valuation.extend (laneOf k Γ W)
          (laneOfTy k _ (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
            (lowering.lowerExprBlock e) W))
          = Ctxt.Valuation.extend (laneOf k Γ W) (e.denote (laneOf k Γ W))
      rw [hop]

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD
