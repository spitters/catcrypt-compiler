/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmRenderValidated
public import CatCrypt.Crypto.Optimizer.CopyProp

/-!
# The lane-map vector route: coverage check, validated render, soundness

`vectorizeEmit V sym inOffset nOut c inBound` is the compiler entry point of the vector
route for a straight-line scalar program `c : Com jasminDialect Γ t`. The lane shape
`V : VecShape` is one of

* `q8zmm`: eight 64-bit lanes per ZMM register (`LaneMapVec.qwordZmm`);
* `d16zmm`: sixteen 32-bit lanes per ZMM register (`LaneMapVec.dwordZmm`);
* `q4ymm`: four 64-bit lanes per YMM register (`LaneMapVec.qwordYmmV`).

The entry point first checks that every binding of `c` is covered by the lane shape
(`firstUncovered`, a Boolean test sound for `LaneShape.Covered`) and returns an error
naming the first uncovered binding otherwise. It then deletes the register copies of `c`
outside its last `nOut` bindings (`CopyProp.copyElimOut`) and renders the lane map of the
result through `ZmmRenderValidated.laneMapValidated` at the shape's lane width, binding
map and register mode, which returns the AT&T text only when the translation validator
accepts it. At each shape the render is the one `ZmmRenderValidated.renderValidated`
(64-bit lanes, `ymm` selecting YMM) or `renderValidatedD` (32-bit lanes) computes on
`copyElimOut nOut c` (`vectorizeEmit_q8zmm`, `vectorizeEmit_q4ymm`,
`vectorizeEmit_d16zmm`).

`vectorizeEmit_sound` composes three results: the coverage the check establishes gives
the lane theorem `LaneMapVec.laneMapVec_denote` of the shape (lane `k` of the lane-mapped
program is the scalar program on lane `k` of the inputs); the validated render gives
`ZmmRenderValidated.laneMapValidated_sound` (the text stores, lane by lane, the last
`nOut` bindings of the copy-free program); and `CopyProp.copyElimOut_outputs` identifies
those bindings with the last `nOut` bindings of `c` (`bindWords_getElem?_outputs`: entry
`nBinds c - n + j` of `bindWords` is entry `j` of `ComDCE.outputs n c`).

## Main definitions

* `VecShape`, `VecShape.laneShape`: the lane shapes of the route and their `LaneShape`.
* `coveredExprB`, `firstUncovered`: the Boolean coverage test.
* `vectorizeEmit`: the entry point.

## Main results

* `coveredExprB_iff`, `covered_of_firstUncovered`: the coverage test decides
  `LaneShape.Covered`.
* `bindWords_eq_map_bindVals`, `bindWords_getElem?_outputs`: `bindWords` is
  `ComDCE.bindVals` read as `W`-bit words, and its entry `nBinds c − n + j` is entry `j`
  of `ComDCE.outputs n c` read the same way.
* `bindWords_copyElimOut`: copy elimination keeps the last `nOut` entries of `bindWords`.
* `vectorizeEmit_q8zmm`, `vectorizeEmit_q4ymm`, `vectorizeEmit_d16zmm`: the entry point
  on a covered program is the validated render.
* `vectorizeEmit_sound`: soundness of the entry point.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmRenderValidated
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender (LaneW exprZBindScalar
  exprZBindScalar32)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode MState run lane)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (parse)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt regAs)
open CatCrypt.Crypto.Optimizer.CopyProp (copyElimOut copyElimOut_outputs)

/-! ## 1. The lane shapes of the route -/

/-- The lane shapes the vector route renders: eight 64-bit lanes per ZMM register,
    sixteen 32-bit lanes per ZMM register, four 64-bit lanes per YMM register. -/
inductive VecShape where
  | q8zmm
  | d16zmm
  | q4ymm
deriving DecidableEq, Repr

/-- The lane map of each shape. -/
def VecShape.laneShape : VecShape → LaneShape
  | .q8zmm => qwordZmm
  | .d16zmm => dwordZmm
  | .q4ymm => qwordYmmV

/-- The lane width of each shape's render. -/
def VecShape.laneW : VecShape → LaneW
  | .q8zmm => .q
  | .d16zmm => .d
  | .q4ymm => .q

/-- The register mode of each shape's render. -/
def VecShape.mode : VecShape → Mode
  | .q8zmm => .zmm
  | .d16zmm => .zmm
  | .q4ymm => .ymm

/-- The binding map of each shape's render. -/
def VecShape.bindMap : VecShape → BindMap
  | .q8zmm => exprZBindScalar
  | .d16zmm => exprZBindScalar32
  | .q4ymm => exprZBindScalar

/-- The render's lane width is the lane map's lane width. -/
theorem VecShape.laneW_bits (V : VecShape) : V.laneW.bits = V.laneShape.laneBits := by
  cases V <;> rfl

/-- The render's lane count is the lane map's lane count. -/
theorem VecShape.act_div (V : VecShape) :
    V.mode.act / V.laneW.bits = V.laneShape.laneCount := by
  cases V <;> rfl

/-- The binding map of each shape satisfies each binding it produces. -/
theorem VecShape.bindSound : (V : VecShape) → BindSound V.laneW V.bindMap
  | .q8zmm => exprZBindScalar_sound
  | .d16zmm => exprZBindScalar32_sound
  | .q4ymm => exprZBindScalar_sound

/-- The binding map of each shape names its bindings in order. -/
theorem VecShape.bindShape : (V : VecShape) → BindShape V.laneW V.bindMap
  | .q8zmm => exprZBindScalar_shape
  | .d16zmm => exprZBindScalar32_shape
  | .q4ymm => exprZBindScalar_shape

/-! ## 2. The coverage test -/

/-- The Boolean form of `LaneShape.CoveredExpr`. -/
def coveredExprB (S : LaneShape) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Bool :=
  match e.op with
  | .regArith bop w => decide (w = S.laneBits) && S.covers bop
  | .regConst w _ => decide (w = S.laneBits)
  | .mulhi w => decide (w = S.laneBits) && S.mulhiExpr.isSome
  | .shlImm w n => decide (w = S.laneBits) && (S.immBlock .shl).isSome && S.immCovers .shl n
  | .shrImm w n => decide (w = S.laneBits) && (S.immBlock .shr).isSome && S.immCovers .shr n
  | .sarImm w n => decide (w = S.laneBits) && (S.immBlock .sar).isSome && S.immCovers .sar n
  | .rorImm w n => decide (w = S.laneBits) && (S.immBlock .ror).isSome && S.immCovers .ror n
  | .stackLoad w _ => S.arrWiden && decide (w = S.laneBits)
  | _ => false

/-- `coveredExprB` decides `LaneShape.CoveredExpr`. -/
theorem coveredExprB_iff (S : LaneShape) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : coveredExprB S e = true ↔ S.CoveredExpr e := by
  obtain ⟨op, h, args⟩ := e
  cases op <;> simp [coveredExprB, LaneShape.CoveredExpr, and_assoc]

/-- A label of an op for the coverage error. -/
def opLabel : JasminOp → String
  | .regArith _ w => s!"regArith at width {w}"
  | .regConst w _ => s!"regConst at width {w}"
  | .mulhi w => s!"mulhi at width {w}"
  | .shlImm w n => s!"shlImm {n} at width {w}"
  | .shrImm w n => s!"shrImm {n} at width {w}"
  | .sarImm w n => s!"sarImm {n} at width {w}"
  | .rorImm w n => s!"rorImm {n} at width {w}"
  | .stackLoad w n => s!"stackLoad at width {w}, length {n}"
  | .extCall name _ _ => s!"extCall {name}"
  | _ => "an op without a lane-map block"

/-- The index and op of the first binding of `c`, counted from `i`, that `S` does not
    cover, or `none` when `S` covers every binding. -/
def firstUncovered (S : LaneShape) {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Nat → Option (Nat × JasminOp)
  | .ret _, _ => none
  | .var e body, i =>
      if coveredExprB S e then firstUncovered S body (i + 1) else some (i, e.op)

/-- A program without an uncovered binding is covered. -/
theorem covered_of_firstUncovered (S : LaneShape) : {Γ : Ctxt jasminDialect} →
    {t : JasminTy} → (c : Com jasminDialect Γ t) → (i : Nat) →
    firstUncovered S c i = none → S.Covered c
  | _, _, .ret _, _, _ => trivial
  | _, _, .var e body, i, h => by
      simp only [firstUncovered] at h
      split at h
      · rename_i he
        exact ⟨(coveredExprB_iff S e).1 he, covered_of_firstUncovered S body (i + 1) h⟩
      · cases h

/-! ## 3. The output bindings -/

/-- `bindWords W V c` is the list `ComDCE.bindVals c V` with each value read as a `W`-bit
    word. -/
theorem bindWords_eq_map_bindVals (W : Nat) : ∀ {Γ : JCtxt} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (c : Com jasminDialect Γ t),
    bindWords W V c
      = (Optimizer.ComDCE.bindVals c V).map (fun p => regAs p.1 W p.2)
  | _, _, _, .ret _ => rfl
  | _, _, V, .var e body => by
      simp only [bindWords, Optimizer.ComDCE.bindVals, List.map_cons,
        bindWords_eq_map_bindVals W (V.extend (e.denote V)) body]

theorem nBinds_eq_comLen : ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t),
    nBinds c = Optimizer.UncomputePass.comLen c
  | _, _, .ret _ => rfl
  | _, _, .var _ body => by
      simp only [nBinds, Optimizer.UncomputePass.comLen_var, nBinds_eq_comLen body]

/-- Entry `nBinds c − n + j` of `bindWords W V c` is entry `j` of the last `n` binding
    values `ComDCE.outputs n c V`, read as a `W`-bit word. -/
theorem bindWords_getElem?_outputs (W n j : Nat) {Γ : JCtxt} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (c : Com jasminDialect Γ t) :
    (bindWords W V c)[nBinds c - n + j]?
      = ((Optimizer.ComDCE.outputs n c V)[j]?).map (fun p => regAs p.1 W p.2) := by
  rw [bindWords_eq_map_bindVals, Optimizer.ComDCE.outputs, List.getElem?_drop,
    List.getElem?_map, Optimizer.ComDCE.length_bindVals, nBinds_eq_comLen]

/-- Copy elimination outside the last `n` bindings keeps entry `nBinds − n + j` of
    `bindWords`: the last `n` binding values. -/
theorem bindWords_copyElimOut (W n j : Nat) {Γ : JCtxt} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (c : Com jasminDialect Γ t) :
    (bindWords W V (copyElimOut n c))[nBinds (copyElimOut n c) - n + j]?
      = (bindWords W V c)[nBinds c - n + j]? := by
  rw [bindWords_getElem?_outputs, bindWords_getElem?_outputs, copyElimOut_outputs]

/-! ## 4. The entry point -/

/-- **The vector route.** The AT&T text of the function `sym` computing the lane map of
    the straight-line scalar program `c` at lane shape `V`, parameter `s` loaded from
    byte offset `inOffset s`, the last `nOut` bindings stored as the outputs, with the
    range analysis run from inputs at most `B` when `inBound = some B`. The register
    copies outside the last `nOut` bindings are deleted before rendering
    (`CopyProp.copyElimOut`). Returns an error naming the first binding outside the
    shape's coverage, or the renderer's or the translation validator's error. -/
def vectorizeEmit (V : VecShape) {Γ : JCtxt} {t : JasminTy} (sym : String)
    (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t)
    (inBound : Option Nat := none) : Except String String :=
  match firstUncovered V.laneShape c 0 with
  | some (i, op) =>
      .error s!"vectorizeEmit {sym}: binding {i} ({opLabel op}) is outside the lane shape \
        {reprStr V}"
  | none =>
      laneMapValidated V.laneW V.bindMap V.mode sym inOffset nOut (copyElimOut nOut c) inBound

/-- At eight 64-bit ZMM lanes, the entry point on a covered program is
    `renderValidated` of its copy-free form. -/
theorem vectorizeEmit_q8zmm {Γ : JCtxt} {t : JasminTy} (sym : String)
    (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t) (inBound : Option Nat)
    (h : firstUncovered qwordZmm c 0 = none) :
    vectorizeEmit .q8zmm sym inOffset nOut c inBound
      = renderValidated sym inOffset nOut (copyElimOut nOut c) inBound := by
  simp only [vectorizeEmit, VecShape.laneShape, h]
  rfl

/-- At four 64-bit YMM lanes, the entry point on a covered program is `renderValidated`
    of its copy-free form with `ymm`. -/
theorem vectorizeEmit_q4ymm {Γ : JCtxt} {t : JasminTy} (sym : String)
    (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t) (inBound : Option Nat)
    (h : firstUncovered qwordYmmV c 0 = none) :
    vectorizeEmit .q4ymm sym inOffset nOut c inBound
      = renderValidated sym inOffset nOut (copyElimOut nOut c) inBound (ymm := true) := by
  simp only [vectorizeEmit, VecShape.laneShape, h]
  rfl

/-- At sixteen 32-bit ZMM lanes, the entry point on a covered program is
    `renderValidatedD` of its copy-free form. -/
theorem vectorizeEmit_d16zmm {Γ : JCtxt} {t : JasminTy} (sym : String)
    (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t) (inBound : Option Nat)
    (h : firstUncovered dwordZmm c 0 = none) :
    vectorizeEmit .d16zmm sym inOffset nOut c inBound
      = renderValidatedD sym inOffset nOut (copyElimOut nOut c) inBound := by
  simp only [vectorizeEmit, VecShape.laneShape, h]
  rfl

/-- **Soundness of the vector route.** When `vectorizeEmit V` returns `text` for `c`:

    1. `c` is covered by the lane shape;
    2. for every leaf semantics satisfying the shape's high-multiply law (none is needed
       without a high multiply; `LaneMapVec.mulhiLane_dwordZmm` gives it for `d16zmm`),
       lane `k` of the lane-mapped program `laneMapVec V.laneShape c` on the vector
       valuation `W` is the scalar program on lane `k` of `W`;
    3. the text parses to a program that, for lane valuations `Vs` of the parameters
       (each input word at most `B` when `inBound = some B`) laid out at the offsets
       `inOffset`, stores at output `j` a vector whose lane `k` is the value of binding
       `nBinds c - nOut + j` of the scalar run from `Vs k`. -/
theorem vectorizeEmit_sound (V : VecShape) {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : vectorizeEmit V sym inOffset nOut c inBound = .ok text) :
    V.laneShape.Covered c ∧
    (∀ (leafSem : LeafSem), V.laneShape.MulhiLane leafSem →
      ∀ (W : Ctxt.Valuation (V.laneShape.widenCtxt Γ)) (k : Fin V.laneShape.laneCount),
        V.laneShape.laneOfTy k t
            (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec V.laneShape c) W)
          = c.denote (V.laneShape.laneOf k Γ W)) ∧
    ∃ prog ro, parse V.mode text = .ok (prog, ro) ∧
      ∀ (Vs : Nat → Ctxt.Valuation Γ) (inp : Nat → BitVec 512),
        (∀ B, inBound = some B → ∀ k < V.mode.act / V.laneW.bits,
          ∀ v : Ctxt.Var Γ (.reg V.laneW.bits), (v.lookup (Vs k)).toNat ≤ B) →
        (∀ k < V.mode.act / V.laneW.bits, ∀ v : Ctxt.Var Γ (.reg V.laneW.bits),
          lane V.laneW.bits (inp (inOffset (varDepth v))) k = v.lookup (Vs k)) →
        ∀ σ : MState, σ.log = [] →
        ∃ σ', run V.mode inp ro σ prog = some σ' ∧
          ∀ j < nOut, ∃ y, σ'.outAt (V.mode.stride * j) = some y ∧
            ∀ k < V.mode.act / V.laneW.bits, ∃ x,
              (bindWords V.laneW.bits (Vs k) c)[nBinds c - nOut + j]? = some (some x) ∧
              lane V.laneW.bits y k = x := by
  unfold vectorizeEmit at h
  split at h
  · cases h
  · rename_i hc
    have hcov := covered_of_firstUncovered V.laneShape c 0 hc
    refine ⟨hcov, fun leafSem hm W k => laneMapVec_denote V.laneShape leafSem hm c hcov W k,
      ?_⟩
    obtain ⟨prog, ro, hp, hrun⟩ := laneMapValidated_sound V.bindSound V.bindShape h
    refine ⟨prog, ro, hp, fun Vs inp hB hin σ hσ => ?_⟩
    obtain ⟨σ', hσ', hout⟩ := hrun Vs inp hB hin σ hσ
    refine ⟨σ', hσ', fun j hj => ?_⟩
    obtain ⟨y, hy, hk⟩ := hout j hj
    exact ⟨y, hy, fun k hk' => by
      rw [← bindWords_copyElimOut]
      exact hk k hk'⟩

end CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit
