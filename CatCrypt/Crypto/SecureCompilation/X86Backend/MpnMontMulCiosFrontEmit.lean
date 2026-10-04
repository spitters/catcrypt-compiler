/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseCarrySelectEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseCarrySelectEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# CIOS Montgomery multiplication as a front-generated nested runtime-trip loop

`mpn_mont_mul(rp, up, vp, np, kn, n0p)` computes the Coarsely Integrated Operand
Scanning Montgomery product of Koc-Acar-Kaliski §5. This module sources it
through the carry-selecting nested runtime-loop front: the per-trip body is
covered `LowCT` (`RArrLoad` / `RScalarSetExpr` / `RArrStore` over the two runtime
loop indices) and
`Dialects.TranslateDialectRuntimeLoopCarrySelect.rolledForLoopNRtNestedC`
front-compiles it together with an inner-trip-count body into a
`ComL.forLoopNRtNested`.

## Main results

* `mont_flat_val` / `mont_flat_carry` / `mont_flat_low`: the read-back laws of one
  emitted trip on the accumulator array.
* `phaseA_val`: the multiply-accumulate sweep's value identity — after `T` trips
  the product region plus the weighted running carry has absorbed
  `value(vp[0..T)) · up[jd]`.
* `phaseA_done`: the whole sweep, `value(t) := value(t) + up[jd] · value(vp)` with
  a cleared carry, under the CIOS size bound.
* `phaseB_val`: the reduction sweep's shift identity — the loop invariant that
  carries the one-word right shift.
* `phaseB_done`: the whole sweep, `2^64 · value(t') = value(t) + m · value(np)`.
* `ciosPass_val`: one outer CIOS pass,
  `2^64 · value(t') = value(t) + up[jd] · value(vp) + m · value(np)`.
* `ciosFold_val`: the accumulated invariant
  `(2^64)^n · value(t_n) = value(up[0..n)) · value(vp) + M · value(np)` for a
  multiplier `M` produced by the fold.
* `ciosFold_congr`: the Montgomery congruence
  `value(t_n) · (2^64)^n ≡ value(up[0..n)) · value(vp) (mod value(np))`.
* `montProgOpt` / `montProg_denote`: the front-compiled nested runtime-trip
  program and its denotation as the `JLoopBodyN.nestedDenote` double fold.
* `montRtLprogOpt` / `montRtAsmOpt`: the owned `Lprog` and the rendered AT&T `.s`.

## The accumulator packing

`JLoopBodyN` carries ONE accumulator of ONE `JasminTy`, so the CIOS accumulator
`t`, the running carry `C` and the Montgomery digit `m` cannot each be a separate
loop-carried value. All three live in the one output array `rp`, which holds
`kn + 5` words:

```
  rp[0 .. kn+2]   the CIOS accumulator t (kn+3 words; rp[kn+2] stays 0)
  rp[kn+3]        the running carry C
  rp[kn+4]        the Montgomery digit m
```

`up`, `vp`, `np`, `kn` and `n0p` are loop invariants and the row index is the
outer loop binder.

## The fused sweep schedule

`nestedDenote` has no prologue or epilogue around the inner fold, so the two CIOS
sweeps of an outer pass share one inner loop of `2·kn + 5` trips. Every trip is
the same multiply-accumulate word step
`(S, C) := t[src] + a · b + C; t[dst] := S`, with the trip index `s` selecting its
operands branch-free:

* trips `s < kn+2` are the multiply-accumulate sweep at `idx = s`, with
  `a = up[jd]`, `b = vp[idx]`, `src = dst = idx`;
* trips `s ≥ kn+2` are the reduction sweep at `idx = s - (kn+2)`, with
  `a = m`, `b = np[idx]`, `src = idx`, `dst = idx - 1` — the one-word right
  shift;
* in both sweeps the mask `0 - bSltu idx kn` clamps the multiplicand index and
  zeroes the loaded limb past `idx = kn`, so the trailing trips degenerate to
  carry flushes with no branch and no out-of-bounds read;
* the Montgomery digit is latched by every multiply-accumulate trip
  (`m := t[0] · n0p`, read after that trip's store, so `t[0]` is final from the
  first trip on) and left alone by every reduction trip, selected by the same
  phase mask.

The reduction sweep runs to `idx = kn+2` rather than `idx = kn`: the two extra
trips move the carry into `t[kn]` and restore `t[kn+1] = 0`, so an outer pass
leaves the accumulator in the shape the next pass reads.

## ABI

```c
extern uint64_t *mpn_mont_mul_rt(uint64_t *rp, const uint64_t *up,
                                 const uint64_t *vp, const uint64_t *np,
                                 uint64_t kn, uint64_t n0p);
```

`rp` (RDI), `up` (RSI), `vp` (RDX), `np` (RCX), `kn` (R8), `n0p` (R9). `rp` holds
`kn + 5` words, zeroed on entry; on return `rp[0..kn)` is the Montgomery product
before the conditional final subtraction.

## Scope

`ciosPass_val`, `ciosFold_val` and `ciosFold_congr` are statements about the
word-level model of §1–§4, for every `NR` / `NU` / `NV` / `NN` and every runtime
`kn`. They stop **before** the conditional final subtraction: the theorems give
`value(t) ≡ value(u) · value(v) · R⁻¹ (mod value(np))` together with the bound
`value(t) < 2 · value(np)`, not the reduced representative in `[0, value(np))`.
The final subtraction is a separate `mpn_sub_n` pass and is not emitted here.

`montProg_denote` carries the two front-compilation hypotheses and concludes at
`JLoopBodyN.nestedDenote` of the front bodies. Identifying that denotation with
`ciosStep` — so that `ciosFold_val` reads as a statement about the emitted kernel
— is the separate source-preservation step (`translateDialectControl_denote_ctl`
composed with `cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMontMulCiosFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu bSltu_eq)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
  (bignumVal bignumVal_snoc bignumVal_lt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_succ cells_length memGetDyn_memSetDyn_ne memGetDyn_memSetDyn_self
   seqAll ltuCmds sv notE ones)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
  (mulAddLimb mulAddLimb_val mulAddLimb_flush cells_setDyn_of_le
   bignumVal_cells_setDyn bignumVal_cells_zero)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 5. The loop bodies as covered `LowCT`

The inner body runs over the catCryptDialect context
`Gbody = [rp : .memref NR, s : .sword 64, jd : .sword 64, up : .memref NU,
          vp : .memref NV, np : .memref NN, kn : .sword 64, n0p : .sword 64]` —
the accumulator array, the inner loop index, the outer loop index, then the five
invariants. All arithmetic is in the `srcClean` `SExpr` fragment (`SMul`,
`SMulHiU`, `SAdd`, `SSub`, `SAnd`, `SXor`, `SShr`). -/

/-- Limb count of the multiplicand array in the denotation model. -/
abbrev NU : Nat := 8

/-- Limb count of the multiplier array in the denotation model. -/
abbrev NV : Nat := 8

/-- Limb count of the modulus array in the denotation model. -/
abbrev NN : Nat := 8

/-- Word count of the accumulator array: the `NU + 3` accumulator words, the
    running-carry cell and the Montgomery-digit cell. -/
abbrev NR : Nat := NU + 5

/-- The accumulator-array slot `rp`, the loop accumulator. -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * NR)⟩

/-- The multiplicand-array slot `up`, a loop invariant. -/
def upLoc : Located := ⟨"up", .TBytes (8 * NU)⟩

/-- The multiplier-array slot `vp`, a loop invariant. -/
def vpLoc : Located := ⟨"vp", .TBytes (8 * NV)⟩

/-- The modulus-array slot `np`, a loop invariant. -/
def npLoc : Located := ⟨"np", .TBytes (8 * NN)⟩

/-- The inner trip count of every outer pass: `2·kn + 5` — the `kn + 2`
    multiply-accumulate trips and the `kn + 3` reduction trips. Recomputed from
    the loop-invariant `kn` each outer pass. -/
def cntBodyLowCT : LowCT :=
  .RScalarSetExpr "cnt" (.SAdd (.SAdd (sv "kn") (sv "kn")) (.SLit 5))

/-- One fused CIOS trip at the runtime indices `(jd, s)`: build the phase mask
    from `bSltu s (kn+2)` and the limb mask from `bSltu idx kn`, select the
    multiplier `up[jd]` or the Montgomery digit and the multiplicand `vp[idx]` or
    `np[idx]`, form the widening product, add the running carry from `rp[kn+3]`
    and the accumulator word `rp[idx]`, synthesise both carry-out bits
    branch-free, store the low word to `rp[idx]` in the multiply-accumulate sweep
    and to `rp[idx-1]` in the reduction sweep, store the new carry, then latch the
    Montgomery digit `rp[0] · n0p` in the multiply-accumulate sweep. -/
def tripBodyLowCT : LowCT := seqAll (
  [ LowCT.RScalarSetExpr "kp2" (.SAdd (sv "kn") (.SLit 2)) ]
  ++ ltuCmds "pa" (sv "s") (sv "kp2")
  ++ [ LowCT.RScalarSetExpr "mska" (.SSub (.SLit 0) (sv "pa"))
     , .RScalarSetExpr "mskb" (notE (sv "mska"))
     , .RScalarSetExpr "off" (.SAnd (sv "kp2") (sv "mskb"))
     , .RScalarSetExpr "idx" (.SSub (sv "s") (sv "off")) ]
  ++ ltuCmds "lt" (sv "idx") (sv "kn")
  ++ [ LowCT.RScalarSetExpr "mskl" (.SSub (.SLit 0) (sv "lt"))
     , .RScalarSetExpr "im" (.SAnd (sv "idx") (sv "mskl"))
     , .RArrLoad ⟨"vv", .TU64⟩ vpLoc "im"
     , .RArrLoad ⟨"nn", .TU64⟩ npLoc "im"
     , .RArrLoad ⟨"uu", .TU64⟩ upLoc "jd"
     , .RScalarSetExpr "mdi" (.SAdd (sv "kn") (.SLit 4))
     , .RArrLoad ⟨"mm", .TU64⟩ rpLoc "mdi"
     , .RScalarSetExpr "bx" (.SXor (sv "nn") (sv "vv"))
     , .RScalarSetExpr "by" (.SAnd (sv "bx") (sv "mska"))
     , .RScalarSetExpr "bz" (.SXor (sv "nn") (sv "by"))
     , .RScalarSetExpr "bb" (.SAnd (sv "bz") (sv "mskl"))
     , .RScalarSetExpr "ax" (.SXor (sv "mm") (sv "uu"))
     , .RScalarSetExpr "ay" (.SAnd (sv "ax") (sv "mska"))
     , .RScalarSetExpr "aa" (.SXor (sv "mm") (sv "ay")) ]
  ++ ltuCmds "pz" (.SLit 0) (sv "idx")
  ++ [ LowCT.RScalarSetExpr "dz" (.SAnd (sv "pz") (sv "mskb"))
     , .RScalarSetExpr "dst" (.SSub (sv "idx") (sv "dz"))
     , .RScalarSetExpr "cyi" (.SAdd (sv "kn") (.SLit 3))
     , .RArrLoad ⟨"cy", .TU64⟩ rpLoc "cyi"
     , .RArrLoad ⟨"rr", .TU64⟩ rpLoc "idx"
     , .RScalarSetExpr "lo" (.SMul (sv "aa") (sv "bb"))
     , .RScalarSetExpr "hi" (.SMulHiU (sv "aa") (sv "bb"))
     , .RScalarSetExpr "s1" (.SAdd (sv "lo") (sv "cy")) ]
  ++ ltuCmds "k1" (sv "s1") (sv "lo")
  ++ [ LowCT.RScalarSetExpr "s2" (.SAdd (sv "s1") (sv "rr")) ]
  ++ ltuCmds "k2" (sv "s2") (sv "s1")
  ++ [ LowCT.RScalarSetExpr "hc" (.SAdd (.SAdd (sv "hi") (sv "k1")) (sv "k2"))
     , .RArrStore rpLoc "dst" ⟨"s2", .TU64⟩
     , .RArrStore rpLoc "cyi" ⟨"hc", .TU64⟩
     , .RScalarSetExpr "z0" (.SLit 0)
     , .RArrLoad ⟨"t0", .TU64⟩ rpLoc "z0"
     , .RScalarSetExpr "mn" (.SMul (sv "t0") (sv "n0p"))
     , .RScalarSetExpr "mx" (.SXor (sv "mm") (sv "mn"))
     , .RScalarSetExpr "my" (.SAnd (sv "mx") (sv "mska"))
     , .RScalarSetExpr "mo" (.SXor (sv "mm") (sv "my"))
     , .RArrStore rpLoc "mdi" ⟨"mo", .TU64⟩ ])

/-- The loop invariants: the three input arrays, the runtime limb count and the
    Montgomery constant `n0p = -N⁻¹ mod 2^64`. -/
def Ginv : Ctx := [.memref NU, .memref NV, .memref NN, .sword 64, .sword 64]

/-- The inner-body context: accumulator, inner index, outer index, invariants. -/
def Gbody : Ctx := .memref NR :: .sword 64 :: .sword 64 :: Ginv

/-- The inner-count-body context: outer index, invariants. -/
def Gcount : Ctx := .sword 64 :: Ginv

/-- The inner-body `VarMap`: `n0p` bound deepest, then `kn`, `np`, `vp`, `up`,
    `jd`, `s`, and `rp` at `.here`. -/
def vmBody : VarMap Gbody :=
  (((((((VarMap.empty.bind (t := .sword 64) "n0p").bind
      (t := .sword 64) "kn").bind
      (t := .memref NN) "np").bind
      (t := .memref NV) "vp").bind
      (t := .memref NU) "up").bind
      (t := .sword 64) "jd").bind
      (t := .sword 64) "s").bind (t := .memref NR) "rp"

/-- The inner-count-body `VarMap`. -/
def vmCount : VarMap Gcount :=
  (((((VarMap.empty.bind (t := .sword 64) "n0p").bind
      (t := .sword 64) "kn").bind
      (t := .memref NN) "np").bind
      (t := .memref NV) "vp").bind
      (t := .memref NU) "up").bind (t := .sword 64) "jd"

/-! ## 6. The nested runtime-trip loop program

Outer argument context `[n0p, kn, np, vp, up, rp]` (newest first), routing
`rp → RDI`, `up → RSI`, `vp → RDX`, `np → RCX`, `kn → R8`, `n0p → R9`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The accumulator-array jasmin type. -/
abbrev AR : JasminTy := .stackArr 64 NR

/-- The multiplicand-array jasmin type. -/
abbrev AU : JasminTy := .stackArr 64 NU

/-- The multiplier-array jasmin type. -/
abbrev AV : JasminTy := .stackArr 64 NV

/-- The modulus-array jasmin type. -/
abbrev AN : JasminTy := .stackArr 64 NN

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, r64, AN, AV, AU, AR]

/-- The runtime outer trip count `kn` (R8). -/
def montOuterCount : Ctxt.Var Gouter r64 := .there .here

/-- The accumulator seed: the output array `rp` (RDI). -/
def montInit : Ctxt.Var Gouter AR :=
  .there (.there (.there (.there (.there .here))))

/-- The loop invariants: `up` (RSI), `vp` (RDX), `np` (RCX), `kn` (R8) and `n0p`
    (R9). -/
def montInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AU, AV, AN, r64, r64] :=
  .cons (.there (.there (.there (.there .here))))
    (.cons (.there (.there (.there .here)))
      (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))

/-- The front-compiled carry-selected nested runtime-trip CIOS Montgomery
    multiply: one inner body copy behind two `jne` back-edges, the outer trip
    counter seeded from the runtime `kn` register, the inner trip recomputed as
    `2·kn + 5` each outer pass, the accumulator array threaded as the loop
    accumulator and `up`/`vp`/`np`/`kn`/`n0p` as loop invariants. `none` if
    either front declines. -/
def montProgOpt : Option (ComL Gouter AR) :=
  rolledForLoopNRtNestedC (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := Ginv)
    vmCount "cnt" cntBodyLowCT
    vmBody "rp" tripBodyLowCT
    montOuterCount montInit montInvs

-- The carry-selecting front accepts both bodies and wraps them in a
-- `ComL.forLoopNRtNested`.
#guard montProgOpt.isSome

-- The spine is the nested runtime-loop node, not an unrolled inner sweep.
#guard (montProgOpt.map (fun c => match c with
  | .forLoopNRtNested _ _ _ _ _ _ => true
  | _ => false)) = some true

/-- **The emitted nest's denotation is the `JLoopBodyN.nestedDenote` double fold
    of the front bodies.** Whenever the carry-selecting front compiles
    `cntBodyLowCT` to `innerCount` and `tripBodyLowCT` to `innerUpdate`, the
    program's denotation at any valuation is the outer fold over `kn` passes of
    the inner fold over the recomputed trip count, seeded by the `rp` argument
    and threading the invariants. The instance of
    `rolledForLoopNRtNestedC_denote` at this kernel. -/
theorem montProg_denote
    {innerCount : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.sword 64))}
    {innerUpdate : Com jasminDialect
      (CryptoToJasminCom.mapCtx
        (CryptoTy.memref NR :: .sword 64 :: .sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hcnt : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .sword 64) (Γbody := .sword 64 :: Ginv)
      vmCount "cnt" cntBodyLowCT = some innerCount)
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .memref NR)
      (Γbody := CryptoTy.memref NR :: .sword 64 :: .sword 64 :: Ginv)
      vmBody "rp" tripBodyLowCT = some innerUpdate)
    (V : Ctxt.Valuation Gouter) :
    montProgOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate
          (montOuterCount.lookup V).toNat (Expr.lookupArgs montInvs V)
          (montInit.lookup V)) :=
  rolledForLoopNRtNestedC_denote vmCount "cnt" cntBodyLowCT vmBody "rp"
    tripBodyLowCT montOuterCount montInit montInvs hcnt hupd V

/-! ## 7. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 6-argument-ABI `Lprog` for the runtime-trip CIOS
    Montgomery multiply under the C symbol `fname` (`RDI = rp`, `RSI = up`,
    `RDX = vp`, `RCX = np`, `R8 = kn`, `R9 = n0p`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FheMontMulEmit.fuseMulHiLprog` in its `saveRdx` looped-body mode: the
    kernel's multiply sits inside two back-edges, so `%rdx` is saved and restored
    around the pinned multiplicand. -/
def montRtLprogOpt (fname : String) : Option Lprog :=
  montProgOpt.map (fun c =>
    FheMontMulEmit.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1, argName 2, argName 3]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
        [64, 64, 64, 64, 64, 64])
      (saveRdx := true))

/-- The owned AT&T `.s` text for the runtime-trip CIOS Montgomery multiply. -/
def montRtAsmOpt (fname : String) : Option String :=
  (montRtLprogOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 6-argument-ABI physical body of the front-compiled nested loop. -/
def montRtPhysBodyOpt : Option Lcmd :=
  montProgOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1, argName 2, argName 3]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
      [64, 64, 64, 64, 64, 64]).lfd_body)

/-- The red-zone qsave slot each streaming memref access of a physical body
    reloads its SIB base from, in body order. -/
def reloadSlots (body : Lcmd) : List String :=
  (body.zip (body.drop 1)).filterMap (fun (prev, cur) =>
    match cur.li_i, prev.li_i with
    | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
        some q
    | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
        some q
    | _, _ => none)

-- The physical body carries two bottom-test back-edges: the outer pass loop and
-- the inner trip loop, so the emit is a nest and not an unrolled chain.
#guard (montRtPhysBodyOpt.map (fun body =>
  (body.filter (fun i => match i.li_i with
    | .Lcond (.reg "NZ") _ => true | _ => false)).length)) = some 2

-- `rp` (RDI), `up` (RSI), `vp` (RDX) and `np` (RCX) are the four pointer
-- arguments; `kn` (R8) and `n0p` (R9) are scalars, so no access may reload its
-- base from their qsave slots.
#guard (montRtPhysBodyOpt.map (fun b =>
  !(reloadSlots b).isEmpty
    && (reloadSlots b).all (fun q =>
        q == "qsave.RDI" || q == "qsave.RSI" || q == "qsave.RDX"
          || q == "qsave.RCX")))
  = some true

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 8. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for the nested runtime-trip CIOS Montgomery
    multiply into the `bench/mpn_montmul_front_compare/gen_com` harness
    directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_montmul_front_compare/gen_com"
  IO.FS.createDirAll dir
  match montRtAsmOpt "mpn_mont_mul_rt" with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_mont_mul_rt_owned.s") s
      IO.println "WROTE bench/mpn_montmul_front_compare/gen_com/mpn_mont_mul_rt_owned.s"
  | none => throw (IO.userError "the nested runtime-loop front declined mpn_mont_mul")

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMontMulCiosFrontEmit
