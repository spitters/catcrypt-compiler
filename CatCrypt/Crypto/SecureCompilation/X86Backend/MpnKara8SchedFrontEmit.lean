/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4FixedFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4FixedFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
public import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# 8×8 → 16-limb Karatsuba multiply as a reg-ptr-out leaf-call schedule

`mpn_kara8_sched(out, inp)` computes `out[0..16) = ap[0..8) · bp[0..8)` (a full
512×512 → 1024-bit product) with **three** 4×4 sub-multiplies instead of the four
a schoolbook nest uses, one level up from the committed 4-limb Karatsuba. It is a
straight-line orchestration of by-pointer leaf calls through the array-ABI
backend, calling the committed `probe_mul4` 4×4 → 8-limb multiply as the
sub-multiply. The two C pointers are the canonical 2-pointer reg-ptr-out ABI
`f(out = RDI, inp = RSI)`; `inp` points at the concatenated input `[ap(8) |
bp(8)]` (128 bytes), `out` at the 16-limb result (128 bytes).

## Karatsuba decomposition

With `a0 = ap[0:4]`, `a1 = ap[4:8]`, `b0 = bp[0:4]`, `b1 = bp[4:8]`:

```
  z0 = a0·b0                               (probe_mul4, 8 limbs)
  z2 = a1·b1                               (probe_mul4, 8 limbs)
  sa = a0 + a1 = (sa_lo:4, ca:1)           (probe_add4c, 5 limbs)
  sb = b0 + b1 = (sb_lo:4, cb:1)           (probe_add4c, 5 limbs)
  m0 = sa_lo · sb_lo                       (probe_mul4, 8 limbs)
  m  = sa·sb = m0 + (ca·sb_lo + cb·sa_lo)·2^256 + ca·cb·2^512   (9 limbs)
  z1 = m − z0 − z2                         (9 limbs, non-negative)
  r  = z0 + z1·2^256 + z2·2^512            (16 limbs)
```

`z0`, `z2`, and `m0 = sa_lo·sb_lo` are the only full 4×4 multiplies — three, not
four. `z1 = a0·b1 + a1·b0`, and `m ≥ z0 + z2` because `(a0+a1)(b0+b1) ≥ a0b0 +
a1b1`, so the subtraction is exact and `z1 ≥ 0`; `z1 < 2^513` fits in 9 limbs.

## The middle corrections

`ca` and `cb` are the `0/1` carry limbs of the two half-sums. The correction
terms `ca·sb_lo`, `cb·sa_lo` are conditional on them. The whole 5-limb half-sum
buffer (`sa` / `sb`, carry at limb 4) is passed to `probe_midcorrect8`, which
extracts the carry internally and forms each conditional product branch-free as
`sb_lo · ca` / `sa_lo · cb` with the covered `SMul` (a `0/1` multiplier selects
the operand or zero), and `ca·cb` likewise. The correction lands at limb offset 4
(2^256) and `ca·cb` at limb 8 (2^512). The middle columns then ripple:

```
  r0..r3 = m0[0..3]
  r4 = m0[4] + ca·sb0 + cb·sa0                 (carry kc4 into limb 5)
  r5 = m0[5] + ca·sb1 + cb·sa1 + kc4           (carry kc5 into limb 6)
  r6 = m0[6] + ca·sb2 + cb·sa2 + kc5           (carry kc6 into limb 7)
  r7 = m0[7] + ca·sb3 + cb·sa3 + kc6           (carry kc7 into limb 8)
  r8 = ca·cb + kc7
```

Each column carry-out is the branch-free `ltuCmds` compare of a running sum
against its first summand; `kc4 ≤ 2`, `kc5, kc6, kc7 ≤ 3`, and `r8 ≤ 4 < 2^64`
because `m < 2^514`.

## The `z1 = m − z0 − z2` subtract

`probe_sub9_2x8` subtracts the two 8-limb corner products from the 9-limb `m` in
two borrow-propagating passes (`m − z0`, then `− z2`), the borrow synthesised
by the same `ltuCmds` idiom the fixed add/sub leaves use. The final borrow is
dropped because `z1 ≥ 0`.

## Assembly (limb-column plan)

`base16 = join16(z0, z2)` seats the two non-overlapping corner products
(`base16[0:8) = z0`, `base16[8:16) = z2`), then `z1·2^256` is added in at limb
offset 4 by `probe_addinto16_9at4` (a 9-limb addend, `z1[0:9)` into
`base16[4:13)`, carry rippling through limb 15). No carry escapes limb 15 because
the exact product is `< 2^1024`.

## ABI of the assembly / correction leaves

```c
extern void probe_add4c(uint64_t *rp, const uint64_t *ap, const uint64_t *bp);
extern void probe_join16(uint64_t *rp, const uint64_t *lop, const uint64_t *hip);
extern void probe_addinto16_9at4(uint64_t *rp, const uint64_t *basep, const uint64_t *addp);
extern void probe_midcorrect8(uint64_t *rp, const uint64_t *m0p,
                              const uint64_t *sap, const uint64_t *sbp);
extern void probe_sub9_2x8(uint64_t *rp, const uint64_t *mp,
                           const uint64_t *z0p, const uint64_t *z2p);
```

`rp` (RDI), then operand pointers in `RSI`, `RDX`, `RCX`. Buffers-only,
reg-ptr-out. The three-input leaves use the SysV 4-pointer ABI
`["RDI","RSI","RDX","RCX"]`, matching the array-ABI orchestration's operand
register order.

## Main results

* `probeAdd4cAsm` / `probeMidCorrect8Asm` / `probeSub9_2x8Asm` /
  `probeJoin16Asm` / `probeAddInto16_9At4Asm` — the five owned assembly /
  correction / add leaves, front-compiled (`translateDialectControl` +
  `cryptoDialectToJasminCom`) and rendered through `Com.toLprogPhysAbi` /
  `renderOwned`.
* `kara8Schedule` / `kara8SchedCom` / the `#guard` on its `.isSome` — the 9-call
  reg-ptr-out Karatsuba schedule and its front-generated orchestration `Com`.
* `kara8SchedAsm` — the owned AT&T `.s`, via the offset-threading array-ABI
  lowering and `renderOwned`.
* `emitMain` — writes `mpn_kara8_sched_owned.s` and the leaf `.s` for the
  byte-KAT.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnKara8SchedFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (seqAll ltuCmds sv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (renderOwned)

/-! ## 1. The `probe_add4c` add-with-carry leaf

`probe_add4c(rp, ap, bp)` sets `rp[0..5) = ap[0..4) + bp[0..4)`, the 5th limb the
carry out of the 4-limb add. Used for the two half-sums `sa = a0 + a1`,
`sb = b0 + b1`; each addend is a 256-bit half, so the sum is `< 2^257` and the
carry limb is `0/1`. Each column carry-out is the branch-free `ltuCmds`
compare of a running sum against its first summand. -/

namespace Add4c

/-- The output-array slot `rp` (5 words: sum with carry). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 5)⟩

/-- The first 4-limb addend `ap`. -/
def apLoc : Located := ⟨"ap", .TBytes (8 * 4)⟩

/-- The second 4-limb addend `bp`. -/
def bpLoc : Located := ⟨"bp", .TBytes (8 * 4)⟩

/-- Index-constant slots `ix0..ix4`. -/
def idxInit : List LowCT :=
  (List.range 5).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `a0..a3` from `ap` and `b0..b3` from `bp`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"a0", .TU64⟩ apLoc "ix0"
  , .RArrLoad ⟨"a1", .TU64⟩ apLoc "ix1"
  , .RArrLoad ⟨"a2", .TU64⟩ apLoc "ix2"
  , .RArrLoad ⟨"a3", .TU64⟩ apLoc "ix3"
  , .RArrLoad ⟨"b0", .TU64⟩ bpLoc "ix0"
  , .RArrLoad ⟨"b1", .TU64⟩ bpLoc "ix1"
  , .RArrLoad ⟨"b2", .TU64⟩ bpLoc "ix2"
  , .RArrLoad ⟨"b3", .TU64⟩ bpLoc "ix3" ]

/-- The carry-propagating column sums for `ap + bp`:

    * `s0 = a0 + b0`, carry `c0`;
    * `s1 = a1 + b1 + c0`, carry `c1`;
    * `s2 = a2 + b2 + c1`, carry `c2`;
    * `s3 = a3 + b3 + c2`, carry `c3` (the 5th limb `0/1`). -/
def columns : List LowCT :=
  [ .RScalarSetExpr "s0" (.SAdd (sv "a0") (sv "b0")) ]
  ++ ltuCmds "c0" (sv "s0") (sv "a0")
  ++ [ .RScalarSetExpr "t1" (.SAdd (sv "a1") (sv "b1")) ]
  ++ ltuCmds "d1a" (sv "t1") (sv "a1")
  ++ [ .RScalarSetExpr "s1" (.SAdd (sv "t1") (sv "c0")) ]
  ++ ltuCmds "d1b" (sv "s1") (sv "t1")
  ++ [ .RScalarSetExpr "c1" (.SAdd (sv "d1a") (sv "d1b"))
     , .RScalarSetExpr "t2" (.SAdd (sv "a2") (sv "b2")) ]
  ++ ltuCmds "d2a" (sv "t2") (sv "a2")
  ++ [ .RScalarSetExpr "s2" (.SAdd (sv "t2") (sv "c1")) ]
  ++ ltuCmds "d2b" (sv "s2") (sv "t2")
  ++ [ .RScalarSetExpr "c2" (.SAdd (sv "d2a") (sv "d2b"))
     , .RScalarSetExpr "t3" (.SAdd (sv "a3") (sv "b3")) ]
  ++ ltuCmds "d3a" (sv "t3") (sv "a3")
  ++ [ .RScalarSetExpr "s3" (.SAdd (sv "t3") (sv "c2")) ]
  ++ ltuCmds "d3b" (sv "s3") (sv "t3")
  ++ [ .RScalarSetExpr "c3" (.SAdd (sv "d3a") (sv "d3b")) ]

/-- Store `s0..s3` and the carry limb `c3` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"s0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"s1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"s2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"s3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"c3", .TU64⟩ ]

/-- The full straight-line `probe_add4c` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ columns ++ storeOutputs)

/-- Head-first kernel context `[bp, ap, rp]`. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 5]

/-- `rp` deepest (→ RDI), then `ap` (→ RSI), then `bp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 5) "rp").bind
    (t := .memref 4) "ap").bind (t := .memref 4) "bp"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 5)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 5, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `probe_add4c` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_add4c` under the buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_add4c"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_add4c`. -/
def asm : Option String := lprog.map renderOwned

end Add4c

/-- The `probe_add4c` owned leaf `.s`. -/
def probeAdd4cAsm : Option String := Add4c.asm

/-! ## 2. The `probe_midcorrect8` correction leaf

`probe_midcorrect8(rp, m0p, sap, sbp)` forms the middle product `m = sa·sb` as a
9-limb buffer, given `m0 = sa_lo·sb_lo` (8 limbs) and the two 5-limb half-sums
`sa = (sa0..sa3, ca)`, `sb = (sb0..sb3, cb)` (carry at limb 4):

```
  m = m0 + (ca·sb_lo + cb·sa_lo)·2^256 + ca·cb·2^512.
```

Each conditional product is formed branch-free with `SMul` — `ca`, `cb ∈ {0,1}`,
so `sb_i·ca` is `sb_i` or `0` — landing `ca·sb_lo` and `cb·sa_lo` in limbs 4..7
and `ca·cb` in limb 8. Uses the 4-pointer SysV ABI (`RDI` out; `m0p`, `sap`,
`sbp` in `RSI`, `RDX`, `RCX`). -/

namespace MidCorrect8

/-- The output-array slot `rp` (9 words: the middle product `m`). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 9)⟩

/-- The `m0 = sa_lo·sb_lo` low product (8 words). -/
def m0Loc : Located := ⟨"m0p", .TBytes (8 * 8)⟩

/-- The half-sum `sa = (sa0..sa3, ca)` (5 words, carry at limb 4). -/
def saLoc : Located := ⟨"sap", .TBytes (8 * 5)⟩

/-- The half-sum `sb = (sb0..sb3, cb)` (5 words, carry at limb 4). -/
def sbLoc : Located := ⟨"sbp", .TBytes (8 * 5)⟩

/-- Index-constant slots `ix0..ix8`. -/
def idxInit : List LowCT :=
  (List.range 9).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `m0_0..m0_7` from `m0p`, `sa0..sa3, ca` from `sap`, `sb0..sb3, cb` from
    `sbp`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"m0_0", .TU64⟩ m0Loc "ix0"
  , .RArrLoad ⟨"m0_1", .TU64⟩ m0Loc "ix1"
  , .RArrLoad ⟨"m0_2", .TU64⟩ m0Loc "ix2"
  , .RArrLoad ⟨"m0_3", .TU64⟩ m0Loc "ix3"
  , .RArrLoad ⟨"m0_4", .TU64⟩ m0Loc "ix4"
  , .RArrLoad ⟨"m0_5", .TU64⟩ m0Loc "ix5"
  , .RArrLoad ⟨"m0_6", .TU64⟩ m0Loc "ix6"
  , .RArrLoad ⟨"m0_7", .TU64⟩ m0Loc "ix7"
  , .RArrLoad ⟨"sa0", .TU64⟩ saLoc "ix0"
  , .RArrLoad ⟨"sa1", .TU64⟩ saLoc "ix1"
  , .RArrLoad ⟨"sa2", .TU64⟩ saLoc "ix2"
  , .RArrLoad ⟨"sa3", .TU64⟩ saLoc "ix3"
  , .RArrLoad ⟨"ca", .TU64⟩ saLoc "ix4"
  , .RArrLoad ⟨"sb0", .TU64⟩ sbLoc "ix0"
  , .RArrLoad ⟨"sb1", .TU64⟩ sbLoc "ix1"
  , .RArrLoad ⟨"sb2", .TU64⟩ sbLoc "ix2"
  , .RArrLoad ⟨"sb3", .TU64⟩ sbLoc "ix3"
  , .RArrLoad ⟨"cb", .TU64⟩ sbLoc "ix4" ]

/-- The branch-free conditional products and the carry-rippling middle columns:

    * `ti = ca·sb_i`, `ui = cb·sa_i` (the two corrections), `cc = ca·cb`;
    * `r4 = m0_4 + t0 + u0`, carry `kc4`;
    * `r5 = m0_5 + t1 + u1 + kc4`, carry `kc5`;
    * `r6 = m0_6 + t2 + u2 + kc5`, carry `kc6`;
    * `r7 = m0_7 + t3 + u3 + kc6`, carry `kc7`;
    * `r8 = cc + kc7`.

    `kc4 ≤ 2`, `kc5, kc6, kc7 ≤ 3`, and `r8 ≤ 4 < 2^64` since `m < 2^514`. -/
def columns : List LowCT :=
  [ .RScalarSetExpr "t0" (.SMul (sv "ca") (sv "sb0"))
  , .RScalarSetExpr "t1" (.SMul (sv "ca") (sv "sb1"))
  , .RScalarSetExpr "t2" (.SMul (sv "ca") (sv "sb2"))
  , .RScalarSetExpr "t3" (.SMul (sv "ca") (sv "sb3"))
  , .RScalarSetExpr "u0" (.SMul (sv "cb") (sv "sa0"))
  , .RScalarSetExpr "u1" (.SMul (sv "cb") (sv "sa1"))
  , .RScalarSetExpr "u2" (.SMul (sv "cb") (sv "sa2"))
  , .RScalarSetExpr "u3" (.SMul (sv "cb") (sv "sa3"))
  , .RScalarSetExpr "cc" (.SMul (sv "ca") (sv "cb"))
  -- limb 4: m0_4 + t0 + u0
  , .RScalarSetExpr "p4a" (.SAdd (sv "m0_4") (sv "t0")) ]
  ++ ltuCmds "k4a" (sv "p4a") (sv "m0_4")
  ++ [ .RScalarSetExpr "r4" (.SAdd (sv "p4a") (sv "u0")) ]
  ++ ltuCmds "k4b" (sv "r4") (sv "p4a")
  ++ [ .RScalarSetExpr "kc4" (.SAdd (sv "k4a") (sv "k4b"))
  -- limb 5: m0_5 + t1 + u1 + kc4
     , .RScalarSetExpr "q5a" (.SAdd (sv "m0_5") (sv "t1")) ]
  ++ ltuCmds "j5a" (sv "q5a") (sv "m0_5")
  ++ [ .RScalarSetExpr "q5b" (.SAdd (sv "q5a") (sv "u1")) ]
  ++ ltuCmds "j5b" (sv "q5b") (sv "q5a")
  ++ [ .RScalarSetExpr "r5" (.SAdd (sv "q5b") (sv "kc4")) ]
  ++ ltuCmds "j5c" (sv "r5") (sv "q5b")
  ++ [ .RScalarSetExpr "kc5" (.SAdd (.SAdd (sv "j5a") (sv "j5b")) (sv "j5c"))
  -- limb 6: m0_6 + t2 + u2 + kc5
     , .RScalarSetExpr "q6a" (.SAdd (sv "m0_6") (sv "t2")) ]
  ++ ltuCmds "j6a" (sv "q6a") (sv "m0_6")
  ++ [ .RScalarSetExpr "q6b" (.SAdd (sv "q6a") (sv "u2")) ]
  ++ ltuCmds "j6b" (sv "q6b") (sv "q6a")
  ++ [ .RScalarSetExpr "r6" (.SAdd (sv "q6b") (sv "kc5")) ]
  ++ ltuCmds "j6c" (sv "r6") (sv "q6b")
  ++ [ .RScalarSetExpr "kc6" (.SAdd (.SAdd (sv "j6a") (sv "j6b")) (sv "j6c"))
  -- limb 7: m0_7 + t3 + u3 + kc6
     , .RScalarSetExpr "q7a" (.SAdd (sv "m0_7") (sv "t3")) ]
  ++ ltuCmds "j7a" (sv "q7a") (sv "m0_7")
  ++ [ .RScalarSetExpr "q7b" (.SAdd (sv "q7a") (sv "u3")) ]
  ++ ltuCmds "j7b" (sv "q7b") (sv "q7a")
  ++ [ .RScalarSetExpr "r7" (.SAdd (sv "q7b") (sv "kc6")) ]
  ++ ltuCmds "j7c" (sv "r7") (sv "q7b")
  ++ [ .RScalarSetExpr "kc7" (.SAdd (.SAdd (sv "j7a") (sv "j7b")) (sv "j7c"))
  -- limb 8: cc + kc7
     , .RScalarSetExpr "r8" (.SAdd (sv "cc") (sv "kc7")) ]

/-- Store `m0_0..m0_3, r4..r8` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"m0_0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"m0_1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"m0_2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"m0_3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"r4", .TU64⟩
  , .RArrStore rpLoc "ix5" ⟨"r5", .TU64⟩
  , .RArrStore rpLoc "ix6" ⟨"r6", .TU64⟩
  , .RArrStore rpLoc "ix7" ⟨"r7", .TU64⟩
  , .RArrStore rpLoc "ix8" ⟨"r8", .TU64⟩ ]

/-- The full straight-line `probe_midcorrect8` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ columns ++ storeOutputs)

/-- Head-first kernel context `[sbp, sap, m0p, rp]`. -/
def inΓ : Ctx := [.memref 5, .memref 5, .memref 8, .memref 9]

/-- `rp` deepest (→ RDI), then `m0p` (→ RSI), `sap` (→ RDX), `sbp` (head → RCX). -/
def inVM : VarMap inΓ :=
  (((VarMap.empty.bind (t := .memref 9) "rp").bind
    (t := .memref 8) "m0p").bind
    (t := .memref 5) "sap").bind (t := .memref 5) "sbp"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 9)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 9, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `probe_midcorrect8` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_midcorrect8` under the 4-pointer buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_midcorrect8"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX", "RCX"]) (abiTyin := [64, 64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_midcorrect8`. -/
def asm : Option String := lprog.map renderOwned

end MidCorrect8

/-- The `probe_midcorrect8` owned leaf `.s`. -/
def probeMidCorrect8Asm : Option String := MidCorrect8.asm

/-! ## 3. The `probe_sub9_2x8` subtract leaf

`probe_sub9_2x8(rp, mp, z0p, z2p)` sets `rp[0..9) = mp[0..9) − z0p[0..8) −
z2p[0..8)` — the middle Karatsuba term `z1`. Two borrow-propagating passes
(`m − z0`, then `− z2`), each borrow synthesised by the `ltuCmds` unsigned-less
idiom; the wrapping subtraction is the owned backend's `SSub`. The final borrow
is dropped because `z1 = a0·b1 + a1·b0 ≥ 0`. Uses the 4-pointer SysV ABI. -/

namespace Sub9

/-- The output-array slot `rp` (9 words: `z1`). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 9)⟩

/-- The 9-limb minuend `m`. -/
def mLoc : Located := ⟨"mp", .TBytes (8 * 9)⟩

/-- The 8-limb subtrahend `z0`. -/
def z0Loc : Located := ⟨"z0p", .TBytes (8 * 8)⟩

/-- The 8-limb subtrahend `z2`. -/
def z2Loc : Located := ⟨"z2p", .TBytes (8 * 8)⟩

/-- Index-constant slots `ix0..ix8`. -/
def idxInit : List LowCT :=
  (List.range 9).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `m0..m8` from `mp`, `z0_0..z0_7` from `z0p`, `z2_0..z2_7` from `z2p`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"m0", .TU64⟩ mLoc "ix0"
  , .RArrLoad ⟨"m1", .TU64⟩ mLoc "ix1"
  , .RArrLoad ⟨"m2", .TU64⟩ mLoc "ix2"
  , .RArrLoad ⟨"m3", .TU64⟩ mLoc "ix3"
  , .RArrLoad ⟨"m4", .TU64⟩ mLoc "ix4"
  , .RArrLoad ⟨"m5", .TU64⟩ mLoc "ix5"
  , .RArrLoad ⟨"m6", .TU64⟩ mLoc "ix6"
  , .RArrLoad ⟨"m7", .TU64⟩ mLoc "ix7"
  , .RArrLoad ⟨"m8", .TU64⟩ mLoc "ix8"
  , .RArrLoad ⟨"z0_0", .TU64⟩ z0Loc "ix0"
  , .RArrLoad ⟨"z0_1", .TU64⟩ z0Loc "ix1"
  , .RArrLoad ⟨"z0_2", .TU64⟩ z0Loc "ix2"
  , .RArrLoad ⟨"z0_3", .TU64⟩ z0Loc "ix3"
  , .RArrLoad ⟨"z0_4", .TU64⟩ z0Loc "ix4"
  , .RArrLoad ⟨"z0_5", .TU64⟩ z0Loc "ix5"
  , .RArrLoad ⟨"z0_6", .TU64⟩ z0Loc "ix6"
  , .RArrLoad ⟨"z0_7", .TU64⟩ z0Loc "ix7"
  , .RArrLoad ⟨"z2_0", .TU64⟩ z2Loc "ix0"
  , .RArrLoad ⟨"z2_1", .TU64⟩ z2Loc "ix1"
  , .RArrLoad ⟨"z2_2", .TU64⟩ z2Loc "ix2"
  , .RArrLoad ⟨"z2_3", .TU64⟩ z2Loc "ix3"
  , .RArrLoad ⟨"z2_4", .TU64⟩ z2Loc "ix4"
  , .RArrLoad ⟨"z2_5", .TU64⟩ z2Loc "ix5"
  , .RArrLoad ⟨"z2_6", .TU64⟩ z2Loc "ix6"
  , .RArrLoad ⟨"z2_7", .TU64⟩ z2Loc "ix7" ]

/-- Pass 1: `d = m − z0` (9-limb difference, borrow rippling limbs 0..8; `z0`
    has no limb 8, so `d8 = m8 − g7`). Each limb `> 0` subtracts the subtrahend
    word then the incoming borrow, the borrow-out the sum of the two `ltuCmds`
    under-flows. -/
def pass1 : List LowCT :=
  [ .RScalarSetExpr "d0" (.SSub (sv "m0") (sv "z0_0")) ]
  ++ ltuCmds "g0" (sv "m0") (sv "z0_0")
  ++ [ .RScalarSetExpr "e1" (.SSub (sv "m1") (sv "z0_1")) ]
  ++ ltuCmds "h1a" (sv "m1") (sv "z0_1")
  ++ [ .RScalarSetExpr "d1" (.SSub (sv "e1") (sv "g0")) ]
  ++ ltuCmds "h1b" (sv "e1") (sv "g0")
  ++ [ .RScalarSetExpr "g1" (.SAdd (sv "h1a") (sv "h1b"))
     , .RScalarSetExpr "e2" (.SSub (sv "m2") (sv "z0_2")) ]
  ++ ltuCmds "h2a" (sv "m2") (sv "z0_2")
  ++ [ .RScalarSetExpr "d2" (.SSub (sv "e2") (sv "g1")) ]
  ++ ltuCmds "h2b" (sv "e2") (sv "g1")
  ++ [ .RScalarSetExpr "g2" (.SAdd (sv "h2a") (sv "h2b"))
     , .RScalarSetExpr "e3" (.SSub (sv "m3") (sv "z0_3")) ]
  ++ ltuCmds "h3a" (sv "m3") (sv "z0_3")
  ++ [ .RScalarSetExpr "d3" (.SSub (sv "e3") (sv "g2")) ]
  ++ ltuCmds "h3b" (sv "e3") (sv "g2")
  ++ [ .RScalarSetExpr "g3" (.SAdd (sv "h3a") (sv "h3b"))
     , .RScalarSetExpr "e4" (.SSub (sv "m4") (sv "z0_4")) ]
  ++ ltuCmds "h4a" (sv "m4") (sv "z0_4")
  ++ [ .RScalarSetExpr "d4" (.SSub (sv "e4") (sv "g3")) ]
  ++ ltuCmds "h4b" (sv "e4") (sv "g3")
  ++ [ .RScalarSetExpr "g4" (.SAdd (sv "h4a") (sv "h4b"))
     , .RScalarSetExpr "e5" (.SSub (sv "m5") (sv "z0_5")) ]
  ++ ltuCmds "h5a" (sv "m5") (sv "z0_5")
  ++ [ .RScalarSetExpr "d5" (.SSub (sv "e5") (sv "g4")) ]
  ++ ltuCmds "h5b" (sv "e5") (sv "g4")
  ++ [ .RScalarSetExpr "g5" (.SAdd (sv "h5a") (sv "h5b"))
     , .RScalarSetExpr "e6" (.SSub (sv "m6") (sv "z0_6")) ]
  ++ ltuCmds "h6a" (sv "m6") (sv "z0_6")
  ++ [ .RScalarSetExpr "d6" (.SSub (sv "e6") (sv "g5")) ]
  ++ ltuCmds "h6b" (sv "e6") (sv "g5")
  ++ [ .RScalarSetExpr "g6" (.SAdd (sv "h6a") (sv "h6b"))
     , .RScalarSetExpr "e7" (.SSub (sv "m7") (sv "z0_7")) ]
  ++ ltuCmds "h7a" (sv "m7") (sv "z0_7")
  ++ [ .RScalarSetExpr "d7" (.SSub (sv "e7") (sv "g6")) ]
  ++ ltuCmds "h7b" (sv "e7") (sv "g6")
  ++ [ .RScalarSetExpr "g7" (.SAdd (sv "h7a") (sv "h7b"))
     , .RScalarSetExpr "d8" (.SSub (sv "m8") (sv "g7")) ]

/-- Pass 2: `r = d − z2` (9-limb difference; final borrow out of limb 8 dropped
    because `z1 ≥ 0`; `z2` has no limb 8, so `r8 = d8 − n7`). -/
def pass2 : List LowCT :=
  [ .RScalarSetExpr "r0" (.SSub (sv "d0") (sv "z2_0")) ]
  ++ ltuCmds "n0" (sv "d0") (sv "z2_0")
  ++ [ .RScalarSetExpr "f1" (.SSub (sv "d1") (sv "z2_1")) ]
  ++ ltuCmds "o1a" (sv "d1") (sv "z2_1")
  ++ [ .RScalarSetExpr "r1" (.SSub (sv "f1") (sv "n0")) ]
  ++ ltuCmds "o1b" (sv "f1") (sv "n0")
  ++ [ .RScalarSetExpr "n1" (.SAdd (sv "o1a") (sv "o1b"))
     , .RScalarSetExpr "f2" (.SSub (sv "d2") (sv "z2_2")) ]
  ++ ltuCmds "o2a" (sv "d2") (sv "z2_2")
  ++ [ .RScalarSetExpr "r2" (.SSub (sv "f2") (sv "n1")) ]
  ++ ltuCmds "o2b" (sv "f2") (sv "n1")
  ++ [ .RScalarSetExpr "n2" (.SAdd (sv "o2a") (sv "o2b"))
     , .RScalarSetExpr "f3" (.SSub (sv "d3") (sv "z2_3")) ]
  ++ ltuCmds "o3a" (sv "d3") (sv "z2_3")
  ++ [ .RScalarSetExpr "r3" (.SSub (sv "f3") (sv "n2")) ]
  ++ ltuCmds "o3b" (sv "f3") (sv "n2")
  ++ [ .RScalarSetExpr "n3" (.SAdd (sv "o3a") (sv "o3b"))
     , .RScalarSetExpr "f4" (.SSub (sv "d4") (sv "z2_4")) ]
  ++ ltuCmds "o4a" (sv "d4") (sv "z2_4")
  ++ [ .RScalarSetExpr "r4" (.SSub (sv "f4") (sv "n3")) ]
  ++ ltuCmds "o4b" (sv "f4") (sv "n3")
  ++ [ .RScalarSetExpr "n4" (.SAdd (sv "o4a") (sv "o4b"))
     , .RScalarSetExpr "f5" (.SSub (sv "d5") (sv "z2_5")) ]
  ++ ltuCmds "o5a" (sv "d5") (sv "z2_5")
  ++ [ .RScalarSetExpr "r5" (.SSub (sv "f5") (sv "n4")) ]
  ++ ltuCmds "o5b" (sv "f5") (sv "n4")
  ++ [ .RScalarSetExpr "n5" (.SAdd (sv "o5a") (sv "o5b"))
     , .RScalarSetExpr "f6" (.SSub (sv "d6") (sv "z2_6")) ]
  ++ ltuCmds "o6a" (sv "d6") (sv "z2_6")
  ++ [ .RScalarSetExpr "r6" (.SSub (sv "f6") (sv "n5")) ]
  ++ ltuCmds "o6b" (sv "f6") (sv "n5")
  ++ [ .RScalarSetExpr "n6" (.SAdd (sv "o6a") (sv "o6b"))
     , .RScalarSetExpr "f7" (.SSub (sv "d7") (sv "z2_7")) ]
  ++ ltuCmds "o7a" (sv "d7") (sv "z2_7")
  ++ [ .RScalarSetExpr "r7" (.SSub (sv "f7") (sv "n6")) ]
  ++ ltuCmds "o7b" (sv "f7") (sv "n6")
  ++ [ .RScalarSetExpr "n7" (.SAdd (sv "o7a") (sv "o7b"))
     , .RScalarSetExpr "r8" (.SSub (sv "d8") (sv "n7")) ]

/-- Store `r0..r8` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"r0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"r1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"r2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"r3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"r4", .TU64⟩
  , .RArrStore rpLoc "ix5" ⟨"r5", .TU64⟩
  , .RArrStore rpLoc "ix6" ⟨"r6", .TU64⟩
  , .RArrStore rpLoc "ix7" ⟨"r7", .TU64⟩
  , .RArrStore rpLoc "ix8" ⟨"r8", .TU64⟩ ]

/-- The full straight-line `probe_sub9_2x8` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ pass1 ++ pass2 ++ storeOutputs)

/-- Head-first kernel context `[z2p, z0p, mp, rp]`. -/
def inΓ : Ctx := [.memref 8, .memref 8, .memref 9, .memref 9]

/-- `rp` deepest (→ RDI), then `mp` (→ RSI), `z0p` (→ RDX), `z2p` (head → RCX). -/
def inVM : VarMap inΓ :=
  (((VarMap.empty.bind (t := .memref 9) "rp").bind
    (t := .memref 9) "mp").bind
    (t := .memref 8) "z0p").bind (t := .memref 8) "z2p"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 9)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 9, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `probe_sub9_2x8` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_sub9_2x8` under the 4-pointer buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_sub9_2x8"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX", "RCX"]) (abiTyin := [64, 64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_sub9_2x8`. -/
def asm : Option String := lprog.map renderOwned

end Sub9

/-- The `probe_sub9_2x8` owned leaf `.s`. -/
def probeSub9_2x8Asm : Option String := Sub9.asm

/-! ## 4. The `probe_join16` assembly leaf

`probe_join16(rp, lop, hip)` sets `rp[0..8) = lop[0..8)` and `rp[8..16) =
hip[0..8)` — a byte concatenation of two 8-limb buffers into a 16-limb buffer.
Used to seat the two non-overlapping corner products `z0` (low) and `z2` (high)
into the 16-limb accumulator base. -/

namespace Join16

/-- The output-array slot `rp` (16 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 16)⟩

/-- The low-half source `lop` (8 words → result limbs 0..7). -/
def lopLoc : Located := ⟨"lop", .TBytes (8 * 8)⟩

/-- The high-half source `hip` (8 words → result limbs 8..15). -/
def hipLoc : Located := ⟨"hip", .TBytes (8 * 8)⟩

/-- Index-constant slots `ix0..ix15`. -/
def idxInit : List LowCT :=
  (List.range 16).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `l0..l7` from `lop` and `h0..h7` from `hip`. -/
def loadInputs : List LowCT :=
  (List.range 8).map (fun i => .RArrLoad ⟨s!"l{i}", .TU64⟩ lopLoc s!"ix{i}")
  ++ (List.range 8).map (fun i => .RArrLoad ⟨s!"h{i}", .TU64⟩ hipLoc s!"ix{i}")

/-- Store the low half at limbs 0..7 and the high half at limbs 8..15. -/
def storeOutputs : List LowCT :=
  (List.range 8).map (fun i => .RArrStore rpLoc s!"ix{i}" ⟨s!"l{i}", .TU64⟩)
  ++ (List.range 8).map (fun i => .RArrStore rpLoc s!"ix{i + 8}" ⟨s!"h{i}", .TU64⟩)

/-- The full straight-line `probe_join16` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ storeOutputs)

/-- Head-first kernel context `[hip, lop, rp]`. -/
def inΓ : Ctx := [.memref 8, .memref 8, .memref 16]

/-- `rp` deepest (→ RDI), then `lop` (→ RSI), then `hip` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 16) "rp").bind
    (t := .memref 8) "lop").bind (t := .memref 8) "hip"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 16)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 16, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `probe_join16` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_join16` under the buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_join16"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_join16`. -/
def asm : Option String := lprog.map renderOwned

end Join16

/-- The `probe_join16` owned leaf `.s`. -/
def probeJoin16Asm : Option String := Join16.asm

/-! ## 5. The `probe_addinto16_9at4` assembly leaf

`probe_addinto16_9at4(rp, basep, addp)` sets
`rp[0..16) = basep[0..16) + addp[0..9)·2^256` — a 16-limb accumulator plus a
9-limb addend shifted left by four limbs, the carry rippling from limb 4 through
limb 15. Limbs 0..3 pass through; the final carry out of limb 15 is dropped (the
full product fits in 16 limbs). Each column carry-out is the branch-free
`ltuCmds` compare of a running sum against its first summand. -/

namespace AddInto16_9At4

/-- The output-array slot `rp` (16 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 16)⟩

/-- The 16-limb accumulator `basep`. -/
def basepLoc : Located := ⟨"basep", .TBytes (8 * 16)⟩

/-- The 9-limb addend `addp` (added at limb offset 4). -/
def addpLoc : Located := ⟨"addp", .TBytes (8 * 9)⟩

/-- Index-constant slots `ix0..ix15`. -/
def idxInit : List LowCT :=
  (List.range 16).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `b0..b15` from `basep` and `a0..a8` from `addp`. -/
def loadInputs : List LowCT :=
  (List.range 16).map (fun i => .RArrLoad ⟨s!"b{i}", .TU64⟩ basepLoc s!"ix{i}")
  ++ (List.range 9).map (fun i => .RArrLoad ⟨s!"a{i}", .TU64⟩ addpLoc s!"ix{i}")

/-- The carry-propagating column sums for `base + add·2^256`, with a 9-limb
    addend `a0..a8` landing in base limbs 4..12:

    * limb 4: `s4 = b4 + a0`, carry `c4`;
    * limbs 5..12: `s_k = b_k + a_{k-4} + c_{k-1}`, carry `c_k`;
    * limbs 13..15: `s_k = b_k + c_{k-1}`, carry `c_k` (final carry dropped).

    `r0..r3 = b0..b3` pass through. -/
def columns : List LowCT :=
  -- limb 4: b4 + a0 (no carry-in)
  [ .RScalarSetExpr "s4" (.SAdd (sv "b4") (sv "a0")) ]
  ++ ltuCmds "c4" (sv "s4") (sv "b4")
  -- limb 5: b5 + a1 + c4
  ++ [ .RScalarSetExpr "t5" (.SAdd (sv "b5") (sv "a1")) ]
  ++ ltuCmds "p5a" (sv "t5") (sv "b5")
  ++ [ .RScalarSetExpr "s5" (.SAdd (sv "t5") (sv "c4")) ]
  ++ ltuCmds "p5b" (sv "s5") (sv "t5")
  ++ [ .RScalarSetExpr "c5" (.SAdd (sv "p5a") (sv "p5b"))
  -- limb 6: b6 + a2 + c5
     , .RScalarSetExpr "t6" (.SAdd (sv "b6") (sv "a2")) ]
  ++ ltuCmds "p6a" (sv "t6") (sv "b6")
  ++ [ .RScalarSetExpr "s6" (.SAdd (sv "t6") (sv "c5")) ]
  ++ ltuCmds "p6b" (sv "s6") (sv "t6")
  ++ [ .RScalarSetExpr "c6" (.SAdd (sv "p6a") (sv "p6b"))
  -- limb 7: b7 + a3 + c6
     , .RScalarSetExpr "t7" (.SAdd (sv "b7") (sv "a3")) ]
  ++ ltuCmds "p7a" (sv "t7") (sv "b7")
  ++ [ .RScalarSetExpr "s7" (.SAdd (sv "t7") (sv "c6")) ]
  ++ ltuCmds "p7b" (sv "s7") (sv "t7")
  ++ [ .RScalarSetExpr "c7" (.SAdd (sv "p7a") (sv "p7b"))
  -- limb 8: b8 + a4 + c7
     , .RScalarSetExpr "t8" (.SAdd (sv "b8") (sv "a4")) ]
  ++ ltuCmds "p8a" (sv "t8") (sv "b8")
  ++ [ .RScalarSetExpr "s8" (.SAdd (sv "t8") (sv "c7")) ]
  ++ ltuCmds "p8b" (sv "s8") (sv "t8")
  ++ [ .RScalarSetExpr "c8" (.SAdd (sv "p8a") (sv "p8b"))
  -- limb 9: b9 + a5 + c8
     , .RScalarSetExpr "t9" (.SAdd (sv "b9") (sv "a5")) ]
  ++ ltuCmds "p9a" (sv "t9") (sv "b9")
  ++ [ .RScalarSetExpr "s9" (.SAdd (sv "t9") (sv "c8")) ]
  ++ ltuCmds "p9b" (sv "s9") (sv "t9")
  ++ [ .RScalarSetExpr "c9" (.SAdd (sv "p9a") (sv "p9b"))
  -- limb 10: b10 + a6 + c9
     , .RScalarSetExpr "t10" (.SAdd (sv "b10") (sv "a6")) ]
  ++ ltuCmds "p10a" (sv "t10") (sv "b10")
  ++ [ .RScalarSetExpr "s10" (.SAdd (sv "t10") (sv "c9")) ]
  ++ ltuCmds "p10b" (sv "s10") (sv "t10")
  ++ [ .RScalarSetExpr "c10" (.SAdd (sv "p10a") (sv "p10b"))
  -- limb 11: b11 + a7 + c10
     , .RScalarSetExpr "t11" (.SAdd (sv "b11") (sv "a7")) ]
  ++ ltuCmds "p11a" (sv "t11") (sv "b11")
  ++ [ .RScalarSetExpr "s11" (.SAdd (sv "t11") (sv "c10")) ]
  ++ ltuCmds "p11b" (sv "s11") (sv "t11")
  ++ [ .RScalarSetExpr "c11" (.SAdd (sv "p11a") (sv "p11b"))
  -- limb 12: b12 + a8 + c11
     , .RScalarSetExpr "t12" (.SAdd (sv "b12") (sv "a8")) ]
  ++ ltuCmds "p12a" (sv "t12") (sv "b12")
  ++ [ .RScalarSetExpr "s12" (.SAdd (sv "t12") (sv "c11")) ]
  ++ ltuCmds "p12b" (sv "s12") (sv "t12")
  ++ [ .RScalarSetExpr "c12" (.SAdd (sv "p12a") (sv "p12b"))
  -- limb 13: b13 + c12
     , .RScalarSetExpr "s13" (.SAdd (sv "b13") (sv "c12")) ]
  ++ ltuCmds "c13" (sv "s13") (sv "b13")
  -- limb 14: b14 + c13
  ++ [ .RScalarSetExpr "s14" (.SAdd (sv "b14") (sv "c13")) ]
  ++ ltuCmds "c14" (sv "s14") (sv "b14")
  -- limb 15: b15 + c14 (final carry dropped)
  ++ [ .RScalarSetExpr "s15" (.SAdd (sv "b15") (sv "c14")) ]

/-- Store `r0..r15` through the `rp` pointer (`r0..r3 = b0..b3`, `r4..r15 =
    s4..s15`). -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"b0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"b1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"b2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"b3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"s4", .TU64⟩
  , .RArrStore rpLoc "ix5" ⟨"s5", .TU64⟩
  , .RArrStore rpLoc "ix6" ⟨"s6", .TU64⟩
  , .RArrStore rpLoc "ix7" ⟨"s7", .TU64⟩
  , .RArrStore rpLoc "ix8" ⟨"s8", .TU64⟩
  , .RArrStore rpLoc "ix9" ⟨"s9", .TU64⟩
  , .RArrStore rpLoc "ix10" ⟨"s10", .TU64⟩
  , .RArrStore rpLoc "ix11" ⟨"s11", .TU64⟩
  , .RArrStore rpLoc "ix12" ⟨"s12", .TU64⟩
  , .RArrStore rpLoc "ix13" ⟨"s13", .TU64⟩
  , .RArrStore rpLoc "ix14" ⟨"s14", .TU64⟩
  , .RArrStore rpLoc "ix15" ⟨"s15", .TU64⟩ ]

/-- The full straight-line `probe_addinto16_9at4` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ columns ++ storeOutputs)

/-- Head-first kernel context `[addp, basep, rp]`. -/
def inΓ : Ctx := [.memref 9, .memref 16, .memref 16]

/-- `rp` deepest (→ RDI), then `basep` (→ RSI), then `addp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 16) "rp").bind
    (t := .memref 16) "basep").bind (t := .memref 9) "addp"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 16)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 16, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `probe_addinto16_9at4` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_addinto16_9at4` under the buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_addinto16_9at4"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_addinto16_9at4`. -/
def asm : Option String := lprog.map renderOwned

end AddInto16_9At4

/-- The `probe_addinto16_9at4` owned leaf `.s`. -/
def probeAddInto16_9At4Asm : Option String := AddInto16_9At4.asm

/-! ## 6. Buffer types and the orchestration schedule

Root-order slots (`OrchestrationFront` §Slot convention): slot `0` is the tail
(oldest) element of the context, the highest slot its head. The array-ABI backend
packs argument buffer `j` at `inArgOff j` in root order, so with `ap` at slot 0
and `bp` at slot 1 the C input pointer addresses `[ap | bp]`. -/

/-- A 5-limb half-sum buffer (`sa` / `sb`, carry at limb 4), 40 bytes. -/
abbrev B5 : JasminTy := .stackArr 64 5

/-- An 8-limb buffer (each input half source; the two corner products; `m0`),
    64 bytes. -/
abbrev B8 : JasminTy := .stackArr 64 8

/-- A 9-limb buffer (the middle product `m`; the middle term `z1`), 72 bytes. -/
abbrev B9 : JasminTy := .stackArr 64 9

/-- The 16-limb result / accumulator buffer, 128 bytes. -/
abbrev B16 : JasminTy := .stackArr 64 16

/-- The orchestration argument context, newest-first `[bp, ap]`: `ap` is the tail
    (root slot 0), `bp` the head (root slot 1). Both 8-limb inputs. -/
abbrev OrchΓ : Ctxt jasminDialect := [B8, B8]

/-- The 9-call reg-ptr-out Karatsuba multiply schedule. `nArgs = 2`, so call `k`
    binds its result at slot `2 + k`.

    * `z0`, `z2` — the corner products, `probe_mul4` on `ap`/`bp` halves at
      limb offsets 0 and 4 (byte offsets 0 and 32) — slots 2, 3;
    * `sa`, `sb` — the half-sums via `probe_add4c` (slots 4, 5);
    * `m0` — the low middle product `sa_lo·sb_lo` via `probe_mul4` (slot 6);
    * `m` — the corrected middle product via `probe_midcorrect8` (slot 7);
    * `z1 = m − z0 − z2` via `probe_sub9_2x8` (slot 8);
    * `base16 = join16(z0, z2)` (slot 9);
    * `r = base16 + z1·2^256` via `probe_addinto16_9at4` (slot 10).

    Result slot 10 (type `B16`) is the full 1024-bit product. -/
def kara8Schedule : List CallPhase :=
  [ { leaf := "probe_mul4", argTys := [B8, B8], retTy := B8, argSlots := [0, 1], argOffs := [0, 0] }
  , { leaf := "probe_mul4", argTys := [B8, B8], retTy := B8, argSlots := [0, 1], argOffs := [32, 32] }
  , { leaf := "probe_add4c", argTys := [B8, B8], retTy := B5, argSlots := [0, 0], argOffs := [0, 32] }
  , { leaf := "probe_add4c", argTys := [B8, B8], retTy := B5, argSlots := [1, 1], argOffs := [0, 32] }
  , { leaf := "probe_mul4", argTys := [B5, B5], retTy := B8, argSlots := [4, 5], argOffs := [0, 0] }
  , { leaf := "probe_midcorrect8", argTys := [B8, B5, B5], retTy := B9, argSlots := [6, 4, 5] }
  , { leaf := "probe_sub9_2x8", argTys := [B9, B8, B8], retTy := B9, argSlots := [7, 2, 3] }
  , { leaf := "probe_join16", argTys := [B8, B8], retTy := B16, argSlots := [2, 3] }
  , { leaf := "probe_addinto16_9at4", argTys := [B16, B9], retTy := B16, argSlots := [9, 8] } ]

/-- The front-generated straight-line orchestration `Com`. Returns the slot-10
    result (type `B16`). `none` only on an ill-typed / out-of-range slot. -/
def kara8SchedCom : Option (Com jasminDialect OrchΓ B16) :=
  buildOrchCom OrchΓ kara8Schedule 10 B16

-- Generation gate: the schedule resolves to a well-typed orchestration `Com`
-- (front / dialect level, not the render).
#guard kara8SchedCom.isSome

/-! ## 7. Array-ABI export

`Com.toLprogArrAbi` threads the schedule's per-call operand byte offsets onto the
array-ABI call records before `emitOneCall` folds them into the operand `leaq`
displacements. `schedArgOffs kara8Schedule` is the `argOffs` of each phase in call
order. -/

/-- The owned AT&T `.s` for `mpn_kara8_sched`: the array-ABI orchestration with the
    schedule's operand byte offsets, rendered by the owned printer. -/
def kara8SchedAsm : Option String :=
  kara8SchedCom.map (fun c =>
    renderOwned (Com.toLprogArrAbi c "mpn_kara8_sched" (schedArgOffs kara8Schedule)))

/-! ## 8. Emit driver

The renders are written while this module elaborates, so `lake` owns them as
build outputs. The seven `.s` — the orchestration and its six owned leaf callees
(`probe_mul4` reused as the sub-multiply) — link into the C byte-KAT against a
`__int128`/wide reference over the concatenated input. -/

/-- Write the orchestration and the leaf `.s` into the reg-ptr-out KAT gen
    directory. -/
def emitMain : IO Unit := do
  let dir := "bench/regptr_out_probe/gen_com"
  IO.FS.createDirAll dir
  match kara8SchedAsm with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_kara8_sched_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/mpn_kara8_sched_owned.s"
      IO.println "  array-ABI Karatsuba orchestration, 3 sub-multiplies, REAL calls"
  | none => throw (IO.userError "buildOrchCom / offset lowering declined the kara8 schedule")
  match probeAdd4cAsm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_add4c_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_add4c_owned.s"
  | none => IO.println "SKIP probe_add4c: front declined"
  match probeMidCorrect8Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_midcorrect8_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_midcorrect8_owned.s"
  | none => IO.println "SKIP probe_midcorrect8: front declined"
  match probeSub9_2x8Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_sub9_2x8_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_sub9_2x8_owned.s"
  | none => IO.println "SKIP probe_sub9_2x8: front declined"
  match probeJoin16Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_join16_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_join16_owned.s"
  | none => IO.println "SKIP probe_join16: front declined"
  match probeAddInto16_9At4Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_addinto16_9at4_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_addinto16_9at4_owned.s"
  | none => IO.println "SKIP probe_addinto16_9at4: front declined"
  match MpnMul4FixedFrontEmit.probeMul4Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_mul4_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_mul4_owned.s"
  | none => IO.println "SKIP probe_mul4: fixed-4 schoolbook multiply front declined"

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnKara8SchedFrontEmit
