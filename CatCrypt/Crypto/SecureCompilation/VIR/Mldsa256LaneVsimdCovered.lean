/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimdDenote
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimdDenote


@[expose] public section
set_option autoImplicit false

/-!
# A 256-bit AVX2 `VPMULHW` re-sourced through the 128-bit `vsimd` front by lane decomposition

The lattice pointwise-multiply kernels (ML-KEM / ML-DSA NTT basemul) issue a
**256-bit** `VPMULHW` — the packed 16×`i16` SIGNED high-16 multiply over a whole
`ymm` register. The vsimd front's covered `SimdOp` alphabet carries only the
**128-bit** `mulhi16` (`VPMULHW` over an `xmm`, 8×`i16`). This module reaches the
256-bit tier **without any new dialect width or 256-bit carrier**: it re-sources
the 256-bit op as TWO 128-bit `mulhi16` `vsimd` ops on the register's low and high
128-bit halves.

This works because `VPMULHW` is **lane-independent**: each 16-bit output lane is a
function of only its own input lanes, so the low 128 bits of the 256-bit result is
exactly the 128-bit `VPMULHW` of the low input halves, and likewise for the high.
No lane-crossing (`vpermq` / `vperm2i128` / cross-`vpblendd`) is involved, so the
decomposition is exact — proved below as `vpmulhw256_lane_decomp`.

```
ymm_out = VPMULHW ymm_a ymm_b       (256-bit, 16 lanes)
        = ( VPMULHW a_hi b_hi ) ++ ( VPMULHW a_lo b_lo )     -- two independent 128-bit halves
```

The 128-bit halves enter as four `.sword 128` context slots
`[a_lo, a_hi, b_lo, b_hi]`; the body is the two `vsimd.mulhi16` `RVsimdSetExpr`
ops producing `out_lo`, `out_hi`. Both live in the existing `IsCoveredV` fragment.

## What is banked

* `mldsa256LaneVsimdLowCT` — the 256-bit `VPMULHW` as an `RSeq` of two 128-bit
  `vsimd.mulhi16` half-lane ops.
* `mldsa256Lane_coveredV : IsCoveredV …` — structural coverage.
* `mldsa256Lane_frontV_fires` — the vsimd front fires (`isSome`, `native_decide`).
* `mldsa256LaneProg_lowers` — the front-emitted program lowers end-to-end to
  `Com jasminDialect` through the verified `cryptoDialectToJasminCom` (owned `.s`).
* `mldsa256LaneVsimdCovered_denote` — **the deliverable**: the whole-program
  machine denote of the two-lane kernel through the vsimd front, a one-line
  instantiation of the front-general homomorphism `translateDialectControlV_denote`.
* `vpmulhw256_lane_decomp` — **the lane-decomposition correctness**: the 256-bit
  `VPMULHW` reference `vpmulhw256W` equals the concatenation of the two 128-bit
  `vpmulhw16W` half-ops the front emits. So the two `vsimd` lanes compute exactly
  the 256-bit YMM op.
* `mldsa256LaneDenote_matches256` — the front-emitted lane programs denote the two
  128-bit halves of the 256-bit reference on ML-DSA/ML-KEM-shaped input vectors.

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.Mldsa256LaneVsimdCovered`
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Mldsa256LaneVsimdCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (vpmulhw16W laneMulHiS16W)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 0. The 256-bit `VPMULHW` reference semantics (16 × `i16` signed high-multiply)

`vpmulhw256W` is the genuine 256-bit AVX2 `VPMULHW`: 16 independent signed 16-bit
high-multiplies across the whole `ymm`, the natural extension of the 128-bit
`vpmulhw16W` fold (8 lanes) to 16 lanes. Each lane `k` reads bits `[16k, 16k+16)`
of both operands — no cross-lane dependency. -/

/-- The 256-bit `VPMULHW`: 16 × signed 16-bit high-multiply lanes. -/
def vpmulhw256W (a b : BitVec 256) : BitVec 256 :=
  (List.range 16).foldl
    (fun acc k =>
      acc ||| ((laneMulHiS16W (BitVec.extractLsb' (16 * k) 16 a)
                              (BitVec.extractLsb' (16 * k) 16 b)).setWidth 256 <<< (16 * k)))
    0

/-! ## 1. The two-lane input context `[a_lo, a_hi, b_lo, b_hi]` (four 128-bit halves) -/

/-- Input context: the low/high 128-bit halves of the two 256-bit operands, each a
    `.sword 128` slot. De Bruijn order `a_lo = .here`, `a_hi`, `b_lo`, `b_hi`. -/
def mlΓ : Ctx := [.sword 128, .sword 128, .sword 128, .sword 128]

/-- `VarMap` binding the four half-registers to the four 128-bit slots. -/
def mlVM : VarMap mlΓ :=
  (((VarMap.empty.bind "b_hi").bind "b_lo").bind "a_hi").bind "a_lo"

/-! ## 2. The high-level source: 256-bit `VPMULHW` as two 128-bit `mulhi16` lanes -/

/-- The 256-bit `VPMULHW` as two lane-independent 128-bit `vsimd.mulhi16` ops:
    `out_lo := VPMULHW(a_lo, b_lo)` on the low 128-bit halves, `out_hi :=
    VPMULHW(a_hi, b_hi)` on the high halves. Both are `vsimd`-tagged `RVsimdSetExpr`
    nodes over `.sword 128` slots — no 256-bit carrier. -/
def mldsa256LaneVsimdLowCT : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "out_lo" "vsimd.mulhi16" ["a_lo", "b_lo"])
        (LowCT.RVsimdSetExpr "out_hi" "vsimd.mulhi16" ["a_hi", "b_hi"])

/-! ## 3. Coverage -/

/-- **The lane-decomposed kernel is `IsCoveredV`**: an `RSeq` of two `vsimd`-tagged
    `mulhi16` `RVsimdSetExpr` ops, each tag parsing. -/
theorem mldsa256Lane_coveredV : IsCoveredV mldsa256LaneVsimdLowCT :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
        (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))

/-! ## 4. The vsimd front fires + reaches owned `.s` -/

/-- **The vsimd front fires on the whole lane-decomposed kernel.** -/
theorem mldsa256Lane_frontV_fires :
    (translateDialectControlV mlVM mldsa256LaneVsimdLowCT).isSome := by native_decide

/-- The front-emitted low-lane result program (returns the `.sword 128` slot `out_lo`). -/
def mldsa256LaneProgLo : Option (Com catCryptDialect mlΓ (.sword 128)) :=
  vsimdResultProg mlVM mldsa256LaneVsimdLowCT "out_lo"

/-- The front-emitted high-lane result program (returns the `.sword 128` slot `out_hi`). -/
def mldsa256LaneProgHi : Option (Com catCryptDialect mlΓ (.sword 128)) :=
  vsimdResultProg mlVM mldsa256LaneVsimdLowCT "out_hi"

/-- The front actually emits both lane result programs. -/
theorem mldsa256LaneProgLo_isSome : mldsa256LaneProgLo.isSome := by native_decide
theorem mldsa256LaneProgHi_isSome : mldsa256LaneProgHi.isSome := by native_decide

/-- Both front-emitted lane programs lower end-to-end to `Com jasminDialect` through
    the verified `cryptoDialectToJasminCom` map — i.e. they reach owned `.s`. -/
theorem mldsa256LaneProg_lowers :
    (mldsa256LaneProgLo.bind cryptoDialectToJasminCom).isSome ∧
    (mldsa256LaneProgHi.bind cryptoDialectToJasminCom).isSome := by
  constructor <;> native_decide

/-! ## 5. THE DELIVERABLE — the whole-program denote homomorphism -/

/-- **Whole-program machine denote of the lane-decomposed 256-bit `VPMULHW`** through
    the vsimd front: for any consistent triple on which the front fires and `semV`
    succeeds, the descended dialect-`Com` prefix denotes exactly the two-lane
    kernel's `semV` `SimdOp`-fold semantics (per-tail continuation). A one-line
    instantiation of `translateDialectControlV_denote`. -/
theorem mldsa256LaneVsimdCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnv) (o : DTransOut Γ),
      ConsistentV vm V env →
      translateDialectControlV vm mldsa256LaneVsimdLowCT = some o →
      semV mldsa256LaneVsimdLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentV o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  translateDialectControlV_denote mldsa256Lane_coveredV

/-! ## 6. THE LANE-DECOMPOSITION CORRECTNESS

The 256-bit `VPMULHW` reference `vpmulhw256W` equals the concatenation of the two
128-bit `vpmulhw16W` half-ops the front emits: the low 128 bits are `VPMULHW` on
the low input halves, the high 128 bits are `VPMULHW` on the high input halves.
This is the load-bearing lane-independence fact that makes the 128-bit re-sourcing
of the 256-bit op exact — `BitVec` `x ++ y` places `x` (here the high lane) in the
top 128 bits. -/

/-- Nested `extractLsb'` collapse: extracting a sub-window of a window is the
    corresponding window of the original, whenever the inner window covers it. Used
    to normalise the half-operand lane windows (`extractLsb' (16k) 16 (extractLsb'
    128 128 a)` → `extractLsb' (128+16k) 16 a`) so each lane's multiply argument
    matches the flat 256-bit lane, letting `bv_decide` discharge the placement with
    `laneMulHiS16W` uninterpreted. -/
theorem extractLsb'_nest {w : Nat} (start len start0 len0 : Nat) (x : BitVec w)
    (h : start + len ≤ len0) :
    (x.extractLsb' start0 len0).extractLsb' start len = x.extractLsb' (start0 + start) len := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
  have h1 : start + i < len0 := by omega
  simp only [h1, decide_true, Bool.true_and]
  congr 1
  omega

/-- **Lane decomposition of the 256-bit `VPMULHW`.** For any two 256-bit operands
    `a`, `b`, the 256-bit high-multiply equals the concatenation of the two 128-bit
    high-multiplies on the low and high halves — so the two `vsimd.mulhi16` lanes
    the front emits compute exactly the 256-bit YMM op. Each side unfolds to the
    same 16 per-lane `laneMulHiS16W` windows (after collapsing the nested half
    extracts); `bv_decide` closes the bit-placement with the lane multiply
    uninterpreted. -/
theorem vpmulhw256_lane_decomp (a b : BitVec 256) :
    vpmulhw256W a b =
      vpmulhw16W (a.extractLsb' 128 128) (b.extractLsb' 128 128) ++
      vpmulhw16W (a.extractLsb' 0 128)   (b.extractLsb' 0 128) := by
  simp (disch := omega) only [vpmulhw256W, vpmulhw16W,
    show List.range 16 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] from rfl,
    show List.range 8 = [0,1,2,3,4,5,6,7] from rfl,
    List.foldl_cons, List.foldl_nil, extractLsb'_nest]
  bv_decide

/-! ## 7. `denote = 256-bit reference` — corroborating KATs through the front

The front-emitted lane programs, run through their own `Com.denote`, reproduce the
low and high 128-bit halves of the 256-bit `VPMULHW` reference on
lattice-shaped input vectors (mixed-sign `i16` coefficients, including `±(q-1)/2`
range values). -/

/-- Denote the low-lane program at the four half-inputs. -/
def mldsa256DenoteLo (a_lo a_hi b_lo b_hi : BitVec 128) : Option (BitVec 128) :=
  mldsa256LaneProgLo.map (fun com =>
    com.denote (.cons a_lo (.cons a_hi (.cons b_lo (.cons b_hi .nil)))))

/-- Denote the high-lane program at the four half-inputs. -/
def mldsa256DenoteHi (a_lo a_hi b_lo b_hi : BitVec 128) : Option (BitVec 128) :=
  mldsa256LaneProgHi.map (fun com =>
    com.denote (.cons a_lo (.cons a_hi (.cons b_lo (.cons b_hi .nil)))))

/-- **The two front lanes match the 256-bit reference halves.** For a
    lattice-shaped operand pair (`a = a_hi ++ a_lo`, `b = b_hi ++ b_lo`), the front's
    low/high lane denotes equal the low/high 128-bit halves of `vpmulhw256W a b`. -/
theorem mldsa256LaneDenote_matches256 :
    let a_lo : BitVec 128 := 0x0007fff8000100029c40ffff00030001
    let a_hi : BitVec 128 := 0x1234fedc00105a5affff8000000affff
    let b_lo : BitVec 128 := 0x00030002fffe000100057fff00020002
    let b_hi : BitVec 128 := 0x0002000180007fff1111ffff00040003
    mldsa256DenoteLo a_lo a_hi b_lo b_hi =
      some ((vpmulhw256W (a_hi ++ a_lo) (b_hi ++ b_lo)).extractLsb' 0 128) ∧
    mldsa256DenoteHi a_lo a_hi b_lo b_hi =
      some ((vpmulhw256W (a_hi ++ a_lo) (b_hi ++ b_lo)).extractLsb' 128 128) := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## 8. Axiom audit -/

#print axioms mldsa256Lane_coveredV
#print axioms mldsa256Lane_frontV_fires
#print axioms mldsa256LaneProg_lowers
#print axioms mldsa256LaneVsimdCovered_denote
#print axioms vpmulhw256_lane_decomp
#print axioms mldsa256LaneDenote_matches256

end CatCrypt.Crypto.SecureCompilation.VIR.Mldsa256LaneVsimdCovered
