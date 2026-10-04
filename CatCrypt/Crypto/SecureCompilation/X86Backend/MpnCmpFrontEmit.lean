/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1CarrySelectEmit
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1CarrySelectEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# `mpn_cmp` as a front-generated runtime-trip loop

`mpn_cmp(ap, bp, n)` compares two `n`-limb little-endian values and reports `+1`
when `ap > bp`, `-1` when `ap < bp`, and `0` when they are equal. This module
sources that comparison through the verified runtime-loop front: the per-limb
body is covered `LowCT` (`RArrLoad` / `RScalarSetExpr` / `RArrStore` over the
runtime loop index), and
`Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRt` front-compiles it into a
`ComL.forLoopNRt` — one body copy behind a `jne` back-edge, the trip counter
seeded from the runtime `n` register.

```
  cmpLimbBodyLowCT (RArrLoad ap/bp at j = top - idx, bSltu pair, mask select,
                    RArrStore rp at 0)
    --(rolledForLoopNRt)--> JLoopBodyN.update : Com jasminDialect …
    --(ComL.forLoopNRt update n rp [ap, bp, n] (ret rp))--------> ComL
    --(ComL.toLprogPhysAbi / renderLprogAtt)--------------------> AT&T .s
```

## Full scan, not early exit

The loop visits every limb. GMP's `mpn_cmp` returns at the first differing limb,
which makes its trip count a function of the operand contents: the number of
iterations, and hence the running time, reveals the position of the highest
differing limb. On secret operands that is a timing side channel. The scan here
descends most-significant limb first and folds each limb into the running result
with mask arithmetic, so the trip count is the public limb count `n` and the
instruction sequence per trip is fixed.

The `LowCT` covered fragment does admit a data-dependent `while`
(`LowCT.RWhileNz`, accepted by `translateDialectDirectControl` and lowered onto
an `Lcond` back-edge), so an early-exit shape is expressible; it is not used
here.

The selection is "first difference wins", read most-significant first: once the
running result is nonzero it is never overwritten. The mask `keep` is all-ones
exactly while the result is still `0`.

## The result cell

`rolledForLoopNRt` threads a memref accumulator, so the comparison outcome rides
in cell `0` of a one-word output array `rp`. The loop invariants are the two
operand arrays and the limb count.

## ABI

```c
extern uint64_t *mpn_cmp_ct(uint64_t *rp, const uint64_t *ap,
                            const uint64_t *bp, uint64_t n);
```

`rp` (RDI), `ap` (RSI), `bp` (RDX), `n` (RCX). `rp` holds one word, zero on
entry and receiving `1`, `-1` or `0`. The zeroed entry value is the `h0`
hypothesis of `cmpFold_val`.

## Main results

* `cmpSign_radix`: the radix step for the value-level sign — comparing
  `x + 2^64·A` against `y + 2^64·B` is comparing `A` against `B` unless they are
  equal, in which case it is comparing `x` against `y`.
* `selW_eq`: the emitted mask select is `if prev = 0 then s else prev`.
* `cmpStepW_eq`: the emitted `bSltu` difference is the sign of the limb
  comparison.
* `cmpFold_val`: the loop invariant over the memref carrier — after `k` trips
  cell `0` of the accumulator holds
  `cmpSign (bignumVal (ap[top+1-k … top])) (bignumVal (bp[top+1-k … top]))`,
  for every `NR` / `NA` / `NB`.
* `cmpFold_val_full`: the same at `k = top + 1`, against `bignumVal` of the whole
  operands.
* `cmpRtProg_denote`: the runtime-trip loop program's denotation as the
  `JLoopBodyN` fold of the front body.
* `cmpRtLprogOpt` / `cmpRtAsmOpt`: the owned `Lprog` and its AT&T text.

## Control flow

`cmpLimbBodyLowCT` carries no `RIfNz` and no `RWhileNz`: the selection is mask
arithmetic over `bSltu`, so one loop trip is a fixed straight-line instruction
sequence and the only control flow in the kernel is the trip-count back-edge,
whose count is the public limb count `n`.

## Scope

`cmpSign_radix`, `selW_eq`, `cmpStepW_eq`, `cmpFold_val` and `cmpFold_val_full`
hold for every `NR` / `NA` / `NB`; `NU` fixes only the memref width of the
concrete front-compiled instance below, whose rendered SIB accesses are
byte-offset and so size-agnostic.

`cmpRtProg_denote` carries the front-compilation hypothesis
`frontLoopBodyJ … = some update` and concludes at `JLoopBodyN.denote` of that
`update`. Identifying that denotation with `cmpFoldStep` — so that the invariant
reads as a statement about the emitted kernel — is the separate
source-preservation step (`translateDialectControl_denote_ctl` composed with
`cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu bSltu_eq)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (memGetDyn_memSetDyn_self seqAll sv ltuCmds)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (segCells segCells_cons)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1CarrySelectEmit
  (reloadSlots)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The value-level comparison sign -/

/-- The comparison outcome as a word: `1` when `m > n`, `-1` when `m < n`, `0`
    when they are equal. This is the GMP `mpn_cmp` return value. -/
def cmpSign (m n : Nat) : BitVec 64 :=
  if m < n then -1 else if n < m then 1 else 0

/-- The outcome is `0` exactly on equal values. -/
theorem cmpSign_eq_zero_iff (m n : Nat) : cmpSign m n = 0 ↔ m = n := by
  unfold cmpSign
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [if_pos hlt] at h; exact absurd h (by decide)
    · rw [if_neg (by omega), if_pos (by omega)] at h; exact absurd h (by decide)
  · intro h; subst h; simp

/-- **The radix step for the comparison sign.** Comparing `x + 2^64·A` against
    `y + 2^64·B` is comparing the high parts `A` and `B`, unless those are equal,
    in which case it is comparing the low limbs `x` and `y`. -/
theorem cmpSign_radix (x y : BitVec 64) (A B : Nat) :
    cmpSign (x.toNat + 2 ^ 64 * A) (y.toNat + 2 ^ 64 * B)
      = if A = B then cmpSign x.toNat y.toNat else cmpSign A B := by
  have hx := x.isLt
  have hy := y.isLt
  rcases lt_trichotomy A B with h | h | h
  · have hAB : A + 1 ≤ B := h
    have hlt : x.toNat + 2 ^ 64 * A < y.toNat + 2 ^ 64 * B := by nlinarith
    rw [if_neg (by omega)]
    unfold cmpSign
    rw [if_pos hlt, if_pos h]
  · subst h
    rw [if_pos rfl]
    unfold cmpSign
    rcases lt_trichotomy x.toNat y.toNat with h' | h' | h'
    · rw [if_pos (by omega), if_pos h']
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos h']
  · have hBA : B + 1 ≤ A := h
    have hgt : y.toNat + 2 ^ 64 * B < x.toNat + 2 ^ 64 * A := by nlinarith
    rw [if_neg (by omega)]
    unfold cmpSign
    rw [if_neg (by omega), if_pos hgt, if_neg (by omega), if_pos h]

/-! ## 2. The word functions the emitted body computes -/

/-- The per-limb sign as the difference of the two branch-free unsigned
    comparisons: `1` when `x > y`, `-1` when `x < y`, `0` when equal. -/
def cmpStepW (x y : BitVec 64) : BitVec 64 := bSltu y x - bSltu x y

/-- The per-limb sign is the value-level comparison of the two limbs. -/
theorem cmpStepW_eq (x y : BitVec 64) : cmpStepW x y = cmpSign x.toNat y.toNat := by
  unfold cmpStepW cmpSign
  rw [bSltu_eq, bSltu_eq]
  simp only [BitVec.ult, decide_eq_true_eq]
  split_ifs <;> first | rfl | decide | omega

/-- **The emitted mask select.** `keep = bSltu 0 prev - 1` is all-ones exactly
    while `prev` is still `0`, so `prev ^ (keep & (s ^ prev))` overwrites the
    running result with `s` only on the first differing limb. -/
theorem selW_eq (prev s : BitVec 64) :
    prev ^^^ ((bSltu 0 prev - 1) &&& (s ^^^ prev)) = if prev = 0 then s else prev := by
  by_cases h : prev = 0
  · subst h
    rw [if_pos rfl]
    unfold bSltu
    bv_decide
  · rw [if_neg h]
    unfold bSltu
    bv_decide

/-- One "first difference wins" limb selection: keep the running result once it
    is nonzero, otherwise take this limb's sign. -/
def cmpSelW (prev x y : BitVec 64) : BitVec 64 :=
  prev ^^^ ((bSltu 0 prev - 1) &&& (cmpStepW x y ^^^ prev))

/-- The selection in closed form. -/
theorem cmpSelW_eq (prev x y : BitVec 64) :
    cmpSelW prev x y = if prev = 0 then cmpSign x.toNat y.toNat else prev := by
  rw [cmpSelW, selW_eq, cmpStepW_eq]

/-! ## 3. The same selection over the memref carrier

The emitted loop carries the one-word output array as its accumulator and folds
one body copy over the trip indices, descending through the operand limbs.
`cmpFoldStep` is that body's word-level effect and `cmpFold` the
`(List.range k).foldl` shape `JLoopBodyN.denote` folds the emitted body in. -/

/-- One trip of the emitted loop on the accumulator array: at trip `t` the
    descending limb index is `j = top - t`; read the running result from cell
    `0`, the two operand limbs from `ap[j]` and `bp[j]`, and write the selected
    result back to cell `0`. -/
def cmpFoldStep {NR NA NB : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (top : Nat) (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn acc 0
    (cmpSelW (memGetDyn acc 0) (memGetDyn ap (top - t)) (memGetDyn bp (top - t)))

/-- The `k`-fold of `cmpFoldStep` over the trip indices `0, …, k-1`: the
    `(List.range k).foldl` shape `JLoopBodyN.denote` folds the emitted loop body
    in, at accumulator type `.stackArr 64 NR`. -/
def cmpFold {NR NA NB : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (top k : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range k).foldl (cmpFoldStep ap bp top) acc

/-- The fold peels its last trip. -/
theorem cmpFold_succ {NR NA NB : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (top k : Nat) (acc : Fin NR → BitVec 64) :
    cmpFold ap bp top (k + 1) acc = cmpFoldStep ap bp top (cmpFold ap bp top k acc) k := by
  simp [cmpFold, List.range_succ, List.foldl_append]

/-- **The comparison loop invariant.** After `k` trips, cell `0` of the
    accumulator holds the comparison sign of the top `k` limbs of the two
    operands: the most-significant differing limb among those already visited
    decides, and later (less significant) limbs cannot overwrite it. -/
theorem cmpFold_val {NR NA NB : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (top : Nat) (acc : Fin NR → BitVec 64) (hNR : 0 < NR)
    (h0 : memGetDyn acc 0 = 0) :
    ∀ k : Nat, k ≤ top + 1 →
      memGetDyn (cmpFold ap bp top k acc) 0
        = cmpSign (bignumVal (segCells ap (top + 1 - k) k))
            (bignumVal (segCells bp (top + 1 - k) k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [cmpFold, segCells, bignumVal, cmpSign, h0]
  | succ m ih =>
      intro hm
      have hm' : m ≤ top + 1 := by omega
      have hIH := ih hm'
      have hbase : top + 1 - (m + 1) = top - m := by omega
      have hshift : top - m + 1 = top + 1 - m := by omega
      rw [cmpFold_succ, cmpFoldStep, memGetDyn_memSetDyn_self _ 0 _ hNR,
        cmpSelW_eq, hIH, hbase, segCells_cons, segCells_cons, hshift]
      simp only [bignumVal, cmpSign_radix]
      by_cases hEq : bignumVal (segCells ap (top + 1 - m) m)
          = bignumVal (segCells bp (top + 1 - m) m)
      · rw [if_pos hEq, if_pos ((cmpSign_eq_zero_iff _ _).mpr hEq)]
      · rw [if_neg hEq, if_neg (fun hc => hEq ((cmpSign_eq_zero_iff _ _).mp hc))]

/-- **The comparison against the whole operands.** Running the loop for its full
    `top + 1` trips from a zeroed result cell leaves cell `0` holding
    `cmpSign (bignumVal ap) (bignumVal bp)` over the limbs `0, …, top`. -/
theorem cmpFold_val_full {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (top : Nat) (acc : Fin NR → BitVec 64) (hNR : 0 < NR)
    (h0 : memGetDyn acc 0 = 0) :
    memGetDyn (cmpFold ap bp top (top + 1) acc) 0
      = cmpSign (bignumVal (segCells ap 0 (top + 1)))
          (bignumVal (segCells bp 0 (top + 1))) := by
  have h := cmpFold_val ap bp top acc hNR h0 (top + 1) (Nat.le_refl _)
  rwa [show top + 1 - (top + 1) = 0 from by omega] at h

/-! ## 4. The loop body as covered `LowCT`

The body runs over the catCryptDialect context
`Gbody = [rp : .memref NR, idx : .sword 64, ap : .memref NU, bp : .memref NU,
n : .sword 64]` — the accumulator array, the runtime loop index, then the two
operand arrays and the limb count. All arithmetic is in the `srcClean` `SExpr`
fragment, so `translateDialectControl` covers it. -/

/-- Limb count of the operand arrays in the denotation model. The rendered SIB
    loads use byte offsets, so the assembly is size-agnostic; this only bounds
    the in-Lean model. The arithmetic results of §1–§3 are stated for every
    `NR` / `NA` / `NB`. -/
abbrev NU : Nat := 8

/-- Word count of the output array: the single result cell. -/
abbrev NR : Nat := 1

/-- The output-array slot `rp` (one word), the loop accumulator. -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * NR)⟩

/-- The first operand slot `ap` (`NU` words), a loop invariant. -/
def apLoc : Located := ⟨"ap", .TBytes (8 * NU)⟩

/-- The second operand slot `bp` (`NU` words), a loop invariant. -/
def bpLoc : Located := ⟨"bp", .TBytes (8 * NU)⟩

/-- One `mpn_cmp` limb at the runtime loop index `idx`: form the descending limb
    index `j = (n - 1) - idx`, read the running result from `rp[0]` and the two
    operand limbs from `ap[j]` and `bp[j]`, form the limb sign as the difference
    of the two branch-free unsigned comparisons, and store the mask-selected
    result back to `rp[0]`. -/
def cmpLimbBodyLowCT : LowCT := seqAll (
  [ LowCT.RScalarSetExpr "top" (.SSub (sv "n") (.SLit 1))
  , .RScalarSetExpr "j" (.SSub (sv "top") (sv "idx"))
  , .RScalarSetExpr "z" (.SLit 0)
  , .RArrLoad ⟨"x", .TU64⟩ apLoc "j"
  , .RArrLoad ⟨"y", .TU64⟩ bpLoc "j"
  , .RArrLoad ⟨"prev", .TU64⟩ rpLoc "z" ]
  ++ ltuCmds "lt" (sv "x") (sv "y")
  ++ ltuCmds "gt" (sv "y") (sv "x")
  ++ [ LowCT.RScalarSetExpr "step" (.SSub (sv "gt") (sv "lt")) ]
  ++ ltuCmds "nz" (.SLit 0) (sv "prev")
  ++ [ LowCT.RScalarSetExpr "keep" (.SSub (sv "nz") (.SLit 1))
     , .RScalarSetExpr "dif" (.SXor (sv "step") (sv "prev"))
     , .RScalarSetExpr "out" (.SXor (sv "prev") (.SAnd (sv "keep") (sv "dif")))
     , .RArrStore rpLoc "z" ⟨"out", .TU64⟩ ])

/-- The loop-body context: accumulator `rp`, runtime loop index, then the two
    operand arrays and the limb count as invariants. -/
def Gbody : Ctx :=
  [.memref NR, .sword 64, .memref NU, .memref NU, .sword 64]

/-- The body `VarMap`: `n` bound deepest, then `bp`, `ap`, `idx`, and `rp` at
    `.here`. -/
def vmBody : VarMap Gbody :=
  (((((VarMap.empty.bind (t := .sword 64) "n").bind
      (t := .memref NU) "bp").bind
      (t := .memref NU) "ap").bind
      (t := .sword 64) "idx").bind (t := .memref NR) "rp")

/-! ## 5. The runtime-trip loop program

Outer argument context `[n, bp, ap, rp]` (newest first), routing `rp → RDI`,
`ap → RSI`, `bp → RDX`, `n → RCX`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The output-array jasmin type. -/
abbrev AR : JasminTy := .stackArr 64 NR

/-- The operand-array jasmin type. -/
abbrev AO : JasminTy := .stackArr 64 NU

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, AO, AO, AR]

/-- The runtime trip count `n` (RCX). -/
def cmpCount : Ctxt.Var Gouter r64 := .here

/-- The accumulator seed: the one-word output array `rp` (RDI). -/
def cmpInit : Ctxt.Var Gouter AR := .there (.there (.there .here))

/-- The loop invariants, arrays first: the operands `ap` (RSI) and `bp` (RDX),
    then the limb count `n` (RCX). -/
def cmpInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AO, AO, r64] :=
  .cons (.there (.there .here))
    (.cons (.there .here)
      (.cons .here .nil))

/-- The front-compiled runtime-trip `mpn_cmp`: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the
    one-word result array threaded as the loop accumulator and `ap`/`bp`/`n` as
    loop invariants. `none` if the front declines. -/
def cmpRtProgOpt (_ : Unit) : Option (ComL Gouter AR) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.memref NU, .memref NU, .sword 64])
    vmBody "rp" cmpLimbBodyLowCT cmpCount cmpInit cmpInvs

-- The front accepts the body and wraps it in a `ComL.forLoopNRt`.
#guard (cmpRtProgOpt ()).isSome

/-- **The emitted loop's denotation is the `JLoopBodyN` fold of the front
    body.** Whenever the front compiles `cmpLimbBodyLowCT` to `update`, the
    runtime-trip program's denotation at any valuation is the `n`-fold of
    `update` over the trip indices, seeded by the `rp` argument and threading
    `ap`, `bp` and `n`. The instance of `rolledForLoopNRt_denote` at this
    kernel. -/
theorem cmpRtProg_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.memref NU, CryptoTy.memref NU, CryptoTy.sword 64]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NR) vmBody "rp" cmpLimbBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    (cmpRtProgOpt ()).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(cmpCount.lookup V).toNat, update⟩
          (Expr.lookupArgs cmpInvs V) (cmpInit.lookup V)) :=
  rolledForLoopNRt_denote vmBody "rp" cmpLimbBodyLowCT cmpCount cmpInit cmpInvs
    hupd V

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 4-argument-ABI `Lprog` for the runtime-trip `mpn_cmp`
    under the C symbol `fname` (`RDI = rp`, `RSI = ap`, `RDX = bp`,
    `RCX = n`). -/
def cmpRtLprogOpt (fname : String) : Option Lprog :=
  (cmpRtProgOpt ()).map (fun c =>
    ComL.toLprogPhysAbi c fname (argName 0) [argName 1, argName 2]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64])

/-- The owned AT&T `.s` text for the runtime-trip `mpn_cmp`. -/
def cmpRtAsmOpt (fname : String) : Option String :=
  (cmpRtLprogOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 4-argument-ABI physical body of the front-compiled runtime-count loop. -/
def cmpRtPhysBodyOpt (_ : Unit) : Option Lcmd :=
  (cmpRtProgOpt ()).map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1, argName 2]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

-- The physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard ((cmpRtPhysBodyOpt ()).map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

-- `rp` (RDI), `ap` (RSI) and `bp` (RDX) are the three pointer arguments; `n`
-- (RCX) is a scalar, so no access may reload its base from its qsave slot.
#guard ((cmpRtPhysBodyOpt ()).map (fun b =>
  !(reloadSlots b).isEmpty
    && (reloadSlots b).all (fun q =>
        q == "qsave.RDI" || q == "qsave.RSI" || q == "qsave.RDX")))
  = some true

-- Rendered-asm correctness is the external GMP KAT; an in-Lean strContains check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 7. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for the runtime-trip `mpn_cmp_ct` into the
    `bench/mpn_cmp_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_cmp_front_compare/gen_com"
  IO.FS.createDirAll dir
  match cmpRtAsmOpt "mpn_cmp_ct" with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_cmp_ct_owned.s") s
      IO.println "WROTE bench/mpn_cmp_front_compare/gen_com/mpn_cmp_ct_owned.s"
  | none => throw (IO.userError "the runtime-loop front declined mpn_cmp")

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
