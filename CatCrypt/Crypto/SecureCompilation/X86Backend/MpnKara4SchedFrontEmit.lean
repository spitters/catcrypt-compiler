/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul2FixedFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul2FixedFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSub2FixedFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSub2FixedFrontEmit
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
# 4×4 → 8-limb Karatsuba multiply as a reg-ptr-out leaf-call schedule

`mpn_kara4_sched(out, inp)` computes `out[0..8) = ap[0..4) · bp[0..4)` (a full
256×256 → 512-bit product) with **three** 2×2 sub-multiplies instead of the four a
schoolbook nest uses, as a straight-line orchestration of by-pointer leaf calls
through the array-ABI backend. The two C pointers are the canonical 2-pointer
reg-ptr-out ABI `f(out = RDI, inp = RSI)`; `inp` points at the concatenated input
`[ap(4) | bp(4)]` (64 bytes), `out` at the 8-limb result (64 bytes).

## Karatsuba decomposition

With `a0 = ap[0:2]`, `a1 = ap[2:4]`, `b0 = bp[0:2]`, `b1 = bp[2:4]`:

```
  z0 = a0·b0                               (probe_mul2, 4 limbs)
  z2 = a1·b1                               (probe_mul2, 4 limbs)
  sa = a0 + a1 = (sa_lo:2, ca:1)           (probe_add2c, 3 limbs)
  sb = b0 + b1 = (sb_lo:2, cb:1)           (probe_add2c, 3 limbs)
  m0 = sa_lo · sb_lo                       (probe_mul2, 4 limbs)
  m  = sa·sb = m0 + ca·sb_lo·2^128 + cb·sa_lo·2^128 + ca·cb·2^256   (5 limbs)
  z1 = m − z0 − z2                         (5 limbs, non-negative)
  r  = z0 + z1·2^128 + z2·2^256            (8 limbs)
```

`z0`, `z2`, and `m0 = sa_lo·sb_lo` are the only full 2×2 multiplies — three, not
four. `z1 = a0·b1 + a1·b0`, and `m ≥ z0 + z2` because `(a0+a1)(b0+b1) ≥ a0b0 +
a1b1`, so the subtraction is exact and `z1 ≥ 0`; `z1 < 2^257` fits in 5 limbs.

## The middle corrections

`ca` and `cb` are the `0/1` carry limbs of the two half-sums. The correction
terms `ca·sb_lo`, `cb·sa_lo` are conditional on them. Rather than routing each
carry as a separate one-limb leaf operand, the whole 3-limb half-sum buffer
(`sa` / `sb`, carry at limb 2) is passed to `probe_midcorrect`, which extracts the
carry internally and forms each conditional product branch-free as
`sb_lo · ca` / `sa_lo · cb` with the covered `SMul` (a `0/1` multiplier selects
the operand or zero), and `ca·cb` likewise. The five middle columns then ripple:

```
  r0 = m0[0],  r1 = m0[1]
  r2 = m0[2] + ca·sb0 + cb·sa0                 (carry kc2 into limb 3)
  r3 = m0[3] + ca·sb1 + cb·sa1 + kc2           (carry kc3 into limb 4)
  r4 = ca·cb + kc3
```

Each column carry-out is the branch-free `ltuCmds` compare of a running sum
against its first summand; `kc2 ≤ 2` and `kc3 ≤ 3`, and `r4 ≤ 4 < 2^64` because
`m < 2^258`.

## The `z1 = m − z0 − z2` subtract

`probe_sub5_2x4` subtracts the two 4-limb corner products from the 5-limb `m` in
two borrow-propagating passes (`m − z0`, then `− z2`), the borrow synthesised
by the same `ltuCmds` idiom the fixed add/sub leaves use. The final borrow is
dropped because `z1 ≥ 0`.

## Assembly (limb-column plan)

`base8 = join8(z0, z2)` seats the two non-overlapping corner products
(`base8[0:4) = z0`, `base8[4:8) = z2`), then `z1·2^128` is added in at limb offset
2 by `probe_addinto8_5at2` (a 5-limb addend, `z1[0:5)` into `base8[2:7)`, carry
rippling to limb 7). No carry escapes limb 7 because the exact product is
`< 2^512`.

## ABI of the assembly / correction leaves

```c
extern void probe_join8(uint64_t *rp, const uint64_t *lop, const uint64_t *hip);
extern void probe_addinto8_5at2(uint64_t *rp, const uint64_t *basep, const uint64_t *addp);
extern void probe_midcorrect(uint64_t *rp, const uint64_t *m0p,
                             const uint64_t *sap, const uint64_t *sbp);
extern void probe_sub5_2x4(uint64_t *rp, const uint64_t *mp,
                           const uint64_t *z0p, const uint64_t *z2p);
```

`rp` (RDI), then operand pointers in `RSI`, `RDX`, `RCX`. Buffers-only,
reg-ptr-out. The three-input leaves use the SysV 4-pointer ABI
`["RDI","RSI","RDX","RCX"]`, matching the array-ABI orchestration's operand
register order.

## Main results

* `probeJoin8Asm` / `probeAddInto8_5At2Asm` / `probeMidCorrectAsm` /
  `probeSub5_2x4Asm` — the four owned assembly / correction leaves,
  front-compiled (`translateDialectControl` + `cryptoDialectToJasminCom`) and
  rendered through `Com.toLprogPhysAbi` / `renderOwned`.
* `kara4Schedule` / `kara4SchedCom` / the `#guard` on its `.isSome` — the 9-call
  reg-ptr-out Karatsuba schedule and its front-generated orchestration `Com`.
* `kara4SchedAsm` — the owned AT&T `.s`, via the offset-threading array-ABI
  lowering and `renderOwned`.
* `emitMain` — writes `mpn_kara4_sched_owned.s` and the leaf `.s` for the
  byte-KAT.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnKara4SchedFrontEmit

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

/-! ## 1. The `probe_join8` assembly leaf

`probe_join8(rp, lop, hip)` sets `rp[0..4) = lop[0..4)` and `rp[4..8) =
hip[0..4)` — a byte concatenation of two 4-limb buffers into an 8-limb buffer.
Used to seat the two non-overlapping corner products `z0` (low) and `z2` (high)
into the 8-limb accumulator base. -/

namespace Join8

/-- The output-array slot `rp` (8 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 8)⟩

/-- The low-half source `lop` (4 words → result limbs 0..3). -/
def lopLoc : Located := ⟨"lop", .TBytes (8 * 4)⟩

/-- The high-half source `hip` (4 words → result limbs 4..7). -/
def hipLoc : Located := ⟨"hip", .TBytes (8 * 4)⟩

/-- Index-constant slots `ix0..ix7`. -/
def idxInit : List LowCT :=
  (List.range 8).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `l0..l3` from `lop` and `h0..h3` from `hip`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"l0", .TU64⟩ lopLoc "ix0"
  , .RArrLoad ⟨"l1", .TU64⟩ lopLoc "ix1"
  , .RArrLoad ⟨"l2", .TU64⟩ lopLoc "ix2"
  , .RArrLoad ⟨"l3", .TU64⟩ lopLoc "ix3"
  , .RArrLoad ⟨"h0", .TU64⟩ hipLoc "ix0"
  , .RArrLoad ⟨"h1", .TU64⟩ hipLoc "ix1"
  , .RArrLoad ⟨"h2", .TU64⟩ hipLoc "ix2"
  , .RArrLoad ⟨"h3", .TU64⟩ hipLoc "ix3" ]

/-- Store the low half at limbs 0..3 and the high half at limbs 4..7. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"l0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"l1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"l2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"l3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"h0", .TU64⟩
  , .RArrStore rpLoc "ix5" ⟨"h1", .TU64⟩
  , .RArrStore rpLoc "ix6" ⟨"h2", .TU64⟩
  , .RArrStore rpLoc "ix7" ⟨"h3", .TU64⟩ ]

/-- The full straight-line `probe_join8` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ storeOutputs)

/-- Head-first kernel context `[hip, lop, rp]`. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 8]

/-- `rp` deepest (→ RDI), then `lop` (→ RSI), then `hip` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 8) "rp").bind
    (t := .memref 4) "lop").bind (t := .memref 4) "hip"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 8)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 8, vv⟩ => r.cont (Com.ret (toVIRVar vv))
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

-- The front translates and lowers `probe_join8` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_join8` under the buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_join8"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_join8`. -/
def asm : Option String := lprog.map renderOwned

end Join8

/-- The `probe_join8` owned leaf `.s`. -/
def probeJoin8Asm : Option String := Join8.asm

/-! ## 2. The `probe_addinto8_5at2` assembly leaf

`probe_addinto8_5at2(rp, basep, addp)` sets
`rp[0..8) = basep[0..8) + addp[0..5)·2^128` — an 8-limb accumulator plus a 5-limb
addend shifted left by two limbs, the carry rippling from limb 2 through limb 7.
Limbs 0 and 1 pass through; the final carry out of limb 7 is dropped (the full
product fits in 8 limbs). Each column carry-out is the branch-free `ltuCmds`
compare of a running sum against its first summand. -/

namespace AddInto8_5At2

/-- The output-array slot `rp` (8 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 8)⟩

/-- The 8-limb accumulator `basep`. -/
def basepLoc : Located := ⟨"basep", .TBytes (8 * 8)⟩

/-- The 5-limb addend `addp` (added at limb offset 2). -/
def addpLoc : Located := ⟨"addp", .TBytes (8 * 5)⟩

/-- Index-constant slots `ix0..ix7`. -/
def idxInit : List LowCT :=
  (List.range 8).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `b0..b7` from `basep` and `a0..a4` from `addp`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"b0", .TU64⟩ basepLoc "ix0"
  , .RArrLoad ⟨"b1", .TU64⟩ basepLoc "ix1"
  , .RArrLoad ⟨"b2", .TU64⟩ basepLoc "ix2"
  , .RArrLoad ⟨"b3", .TU64⟩ basepLoc "ix3"
  , .RArrLoad ⟨"b4", .TU64⟩ basepLoc "ix4"
  , .RArrLoad ⟨"b5", .TU64⟩ basepLoc "ix5"
  , .RArrLoad ⟨"b6", .TU64⟩ basepLoc "ix6"
  , .RArrLoad ⟨"b7", .TU64⟩ basepLoc "ix7"
  , .RArrLoad ⟨"a0", .TU64⟩ addpLoc "ix0"
  , .RArrLoad ⟨"a1", .TU64⟩ addpLoc "ix1"
  , .RArrLoad ⟨"a2", .TU64⟩ addpLoc "ix2"
  , .RArrLoad ⟨"a3", .TU64⟩ addpLoc "ix3"
  , .RArrLoad ⟨"a4", .TU64⟩ addpLoc "ix4" ]

/-- The carry-propagating column sums for `base + add·2^128`, with a 5-limb
    addend `a0..a4` landing in base limbs 2..6:

    * `s2 = b2 + a0`, carry `c2`;
    * `s3 = b3 + a1 + c2`, carry `c3`;
    * `s4 = b4 + a2 + c3`, carry `c4`;
    * `s5 = b5 + a3 + c4`, carry `c5`;
    * `s6 = b6 + a4 + c5`, carry `c6`;
    * `s7 = b7 + c6` (final carry dropped).

    `r0 = b0`, `r1 = b1` pass through. -/
def columns : List LowCT :=
  [ .RScalarSetExpr "s2" (.SAdd (sv "b2") (sv "a0")) ]
  ++ ltuCmds "c2" (sv "s2") (sv "b2")
  ++ [ .RScalarSetExpr "t3" (.SAdd (sv "b3") (sv "a1")) ]
  ++ ltuCmds "c3a" (sv "t3") (sv "b3")
  ++ [ .RScalarSetExpr "s3" (.SAdd (sv "t3") (sv "c2")) ]
  ++ ltuCmds "c3b" (sv "s3") (sv "t3")
  ++ [ .RScalarSetExpr "c3" (.SAdd (sv "c3a") (sv "c3b"))
     , .RScalarSetExpr "t4" (.SAdd (sv "b4") (sv "a2")) ]
  ++ ltuCmds "c4a" (sv "t4") (sv "b4")
  ++ [ .RScalarSetExpr "s4" (.SAdd (sv "t4") (sv "c3")) ]
  ++ ltuCmds "c4b" (sv "s4") (sv "t4")
  ++ [ .RScalarSetExpr "c4" (.SAdd (sv "c4a") (sv "c4b"))
     , .RScalarSetExpr "t5" (.SAdd (sv "b5") (sv "a3")) ]
  ++ ltuCmds "c5a" (sv "t5") (sv "b5")
  ++ [ .RScalarSetExpr "s5" (.SAdd (sv "t5") (sv "c4")) ]
  ++ ltuCmds "c5b" (sv "s5") (sv "t5")
  ++ [ .RScalarSetExpr "c5" (.SAdd (sv "c5a") (sv "c5b"))
     , .RScalarSetExpr "t6" (.SAdd (sv "b6") (sv "a4")) ]
  ++ ltuCmds "c6a" (sv "t6") (sv "b6")
  ++ [ .RScalarSetExpr "s6" (.SAdd (sv "t6") (sv "c5")) ]
  ++ ltuCmds "c6b" (sv "s6") (sv "t6")
  ++ [ .RScalarSetExpr "c6" (.SAdd (sv "c6a") (sv "c6b"))
     , .RScalarSetExpr "s7" (.SAdd (sv "b7") (sv "c6")) ]

/-- Store `r0..r7` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"b0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"b1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"s2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"s3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"s4", .TU64⟩
  , .RArrStore rpLoc "ix5" ⟨"s5", .TU64⟩
  , .RArrStore rpLoc "ix6" ⟨"s6", .TU64⟩
  , .RArrStore rpLoc "ix7" ⟨"s7", .TU64⟩ ]

/-- The full straight-line `probe_addinto8_5at2` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ columns ++ storeOutputs)

/-- Head-first kernel context `[addp, basep, rp]`. -/
def inΓ : Ctx := [.memref 5, .memref 8, .memref 8]

/-- `rp` deepest (→ RDI), then `basep` (→ RSI), then `addp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 8) "rp").bind
    (t := .memref 8) "basep").bind (t := .memref 5) "addp"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 8)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 8, vv⟩ => r.cont (Com.ret (toVIRVar vv))
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

-- The front translates and lowers `probe_addinto8_5at2` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_addinto8_5at2` under the buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_addinto8_5at2"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_addinto8_5at2`. -/
def asm : Option String := lprog.map renderOwned

end AddInto8_5At2

/-- The `probe_addinto8_5at2` owned leaf `.s`. -/
def probeAddInto8_5At2Asm : Option String := AddInto8_5At2.asm

/-! ## 3. The `probe_midcorrect` correction leaf

`probe_midcorrect(rp, m0p, sap, sbp)` forms the middle product
`m = sa·sb` as a 5-limb buffer, given `m0 = sa_lo·sb_lo` (4 limbs) and the two
3-limb half-sums `sa = (sa0, sa1, ca)`, `sb = (sb0, sb1, cb)` (carry at limb 2):

```
  m = m0 + ca·sb_lo·2^128 + cb·sa_lo·2^128 + ca·cb·2^256.
```

Each conditional product is formed branch-free with `SMul` — `ca`, `cb ∈ {0,1}`,
so `sb0·ca` is `sb0` or `0` — landing `ca·sb_lo` and `cb·sa_lo` in limbs 2..3 and
`ca·cb` in limb 4. Uses the 4-pointer SysV ABI (`RDI` out; `m0p`, `sap`, `sbp`
in `RSI`, `RDX`, `RCX`). -/

namespace MidCorrect

/-- The output-array slot `rp` (5 words: the middle product `m`). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 5)⟩

/-- The `m0 = sa_lo·sb_lo` low product (4 words). -/
def m0Loc : Located := ⟨"m0p", .TBytes (8 * 4)⟩

/-- The half-sum `sa = (sa0, sa1, ca)` (3 words, carry at limb 2). -/
def saLoc : Located := ⟨"sap", .TBytes (8 * 3)⟩

/-- The half-sum `sb = (sb0, sb1, cb)` (3 words, carry at limb 2). -/
def sbLoc : Located := ⟨"sbp", .TBytes (8 * 3)⟩

/-- Index-constant slots `ix0..ix4`. -/
def idxInit : List LowCT :=
  (List.range 5).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `m0_0..m0_3` from `m0p`, `sa0, sa1, ca` from `sap`, `sb0, sb1, cb` from
    `sbp`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"m0_0", .TU64⟩ m0Loc "ix0"
  , .RArrLoad ⟨"m0_1", .TU64⟩ m0Loc "ix1"
  , .RArrLoad ⟨"m0_2", .TU64⟩ m0Loc "ix2"
  , .RArrLoad ⟨"m0_3", .TU64⟩ m0Loc "ix3"
  , .RArrLoad ⟨"sa0", .TU64⟩ saLoc "ix0"
  , .RArrLoad ⟨"sa1", .TU64⟩ saLoc "ix1"
  , .RArrLoad ⟨"ca", .TU64⟩ saLoc "ix2"
  , .RArrLoad ⟨"sb0", .TU64⟩ sbLoc "ix0"
  , .RArrLoad ⟨"sb1", .TU64⟩ sbLoc "ix1"
  , .RArrLoad ⟨"cb", .TU64⟩ sbLoc "ix2" ]

/-- The branch-free conditional products and the three carry-rippling columns:

    * `t0 = ca·sb0`, `t1 = ca·sb1` (the `ca·sb_lo` correction);
    * `u0 = cb·sa0`, `u1 = cb·sa1` (the `cb·sa_lo` correction);
    * `cc = ca·cb` (the top correction bit);
    * `r2 = m0_2 + t0 + u0`, carry `kc2`;
    * `r3 = m0_3 + t1 + u1 + kc2`, carry `kc3`;
    * `r4 = cc + kc3`.

    `kc2 ≤ 2`, `kc3 ≤ 3`, and `r4 ≤ 4 < 2^64` since `m < 2^258`. -/
def columns : List LowCT :=
  [ .RScalarSetExpr "t0" (.SMul (sv "ca") (sv "sb0"))
  , .RScalarSetExpr "t1" (.SMul (sv "ca") (sv "sb1"))
  , .RScalarSetExpr "u0" (.SMul (sv "cb") (sv "sa0"))
  , .RScalarSetExpr "u1" (.SMul (sv "cb") (sv "sa1"))
  , .RScalarSetExpr "cc" (.SMul (sv "ca") (sv "cb"))
  , .RScalarSetExpr "p2" (.SAdd (sv "m0_2") (sv "t0")) ]
  ++ ltuCmds "k2" (sv "p2") (sv "m0_2")
  ++ [ .RScalarSetExpr "r2" (.SAdd (sv "p2") (sv "u0")) ]
  ++ ltuCmds "k2b" (sv "r2") (sv "p2")
  ++ [ .RScalarSetExpr "kc2" (.SAdd (sv "k2") (sv "k2b"))
     , .RScalarSetExpr "q3a" (.SAdd (sv "m0_3") (sv "t1")) ]
  ++ ltuCmds "j3a" (sv "q3a") (sv "m0_3")
  ++ [ .RScalarSetExpr "q3b" (.SAdd (sv "q3a") (sv "u1")) ]
  ++ ltuCmds "j3b" (sv "q3b") (sv "q3a")
  ++ [ .RScalarSetExpr "r3" (.SAdd (sv "q3b") (sv "kc2")) ]
  ++ ltuCmds "j3c" (sv "r3") (sv "q3b")
  ++ [ .RScalarSetExpr "kc3" (.SAdd (.SAdd (sv "j3a") (sv "j3b")) (sv "j3c"))
     , .RScalarSetExpr "r4" (.SAdd (sv "cc") (sv "kc3")) ]

/-- Store `m0_0, m0_1, r2, r3, r4` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"m0_0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"m0_1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"r2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"r3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"r4", .TU64⟩ ]

/-- The full straight-line `probe_midcorrect` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ columns ++ storeOutputs)

/-- Head-first kernel context `[sbp, sap, m0p, rp]`. -/
def inΓ : Ctx := [.memref 3, .memref 3, .memref 4, .memref 5]

/-- `rp` deepest (→ RDI), then `m0p` (→ RSI), `sap` (→ RDX), `sbp` (head → RCX). -/
def inVM : VarMap inΓ :=
  (((VarMap.empty.bind (t := .memref 5) "rp").bind
    (t := .memref 4) "m0p").bind
    (t := .memref 3) "sap").bind (t := .memref 3) "sbp"

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

-- The front translates and lowers `probe_midcorrect` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_midcorrect` under the 4-pointer buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_midcorrect"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX", "RCX"]) (abiTyin := [64, 64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_midcorrect`. -/
def asm : Option String := lprog.map renderOwned

end MidCorrect

/-- The `probe_midcorrect` owned leaf `.s`. -/
def probeMidCorrectAsm : Option String := MidCorrect.asm

/-! ## 4. The `probe_sub5_2x4` subtract leaf

`probe_sub5_2x4(rp, mp, z0p, z2p)` sets `rp[0..5) = mp[0..5) − z0p[0..4) −
z2p[0..4)` — the middle Karatsuba term `z1`. Two borrow-propagating passes
(`m − z0`, then `− z2`), each borrow synthesised by the `ltuCmds` unsigned-less
idiom; the wrapping subtraction is the owned backend's `SSub`. The final borrow is
dropped because `z1 = a0·b1 + a1·b0 ≥ 0`. Uses the 4-pointer SysV ABI. -/

namespace Sub5

/-- The output-array slot `rp` (5 words: `z1`). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 5)⟩

/-- The 5-limb minuend `m`. -/
def mLoc : Located := ⟨"mp", .TBytes (8 * 5)⟩

/-- The 4-limb subtrahend `z0`. -/
def z0Loc : Located := ⟨"z0p", .TBytes (8 * 4)⟩

/-- The 4-limb subtrahend `z2`. -/
def z2Loc : Located := ⟨"z2p", .TBytes (8 * 4)⟩

/-- Index-constant slots `ix0..ix4`. -/
def idxInit : List LowCT :=
  (List.range 5).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `m0..m4` from `mp`, `z0_0..z0_3` from `z0p`, `z2_0..z2_3` from `z2p`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"m0", .TU64⟩ mLoc "ix0"
  , .RArrLoad ⟨"m1", .TU64⟩ mLoc "ix1"
  , .RArrLoad ⟨"m2", .TU64⟩ mLoc "ix2"
  , .RArrLoad ⟨"m3", .TU64⟩ mLoc "ix3"
  , .RArrLoad ⟨"m4", .TU64⟩ mLoc "ix4"
  , .RArrLoad ⟨"z0_0", .TU64⟩ z0Loc "ix0"
  , .RArrLoad ⟨"z0_1", .TU64⟩ z0Loc "ix1"
  , .RArrLoad ⟨"z0_2", .TU64⟩ z0Loc "ix2"
  , .RArrLoad ⟨"z0_3", .TU64⟩ z0Loc "ix3"
  , .RArrLoad ⟨"z2_0", .TU64⟩ z2Loc "ix0"
  , .RArrLoad ⟨"z2_1", .TU64⟩ z2Loc "ix1"
  , .RArrLoad ⟨"z2_2", .TU64⟩ z2Loc "ix2"
  , .RArrLoad ⟨"z2_3", .TU64⟩ z2Loc "ix3" ]

/-- Pass 1: `d = m − z0` (5-limb difference, borrow rippling limbs 0..4).
    Each limb `> 0` subtracts the subtrahend word then the incoming borrow, with
    the borrow-out the sum of the two `ltuCmds` under-flows (at most one fires). -/
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
     , .RScalarSetExpr "d4" (.SSub (sv "m4") (sv "g3")) ]

/-- Pass 2: `r = d − z2` (5-limb difference; final borrow out of limb 4 dropped
    because `z1 ≥ 0`). -/
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
     , .RScalarSetExpr "r4" (.SSub (sv "d4") (sv "n3")) ]

/-- Store `r0..r4` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"r0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"r1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"r2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"r3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"r4", .TU64⟩ ]

/-- The full straight-line `probe_sub5_2x4` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ pass1 ++ pass2 ++ storeOutputs)

/-- Head-first kernel context `[z2p, z0p, mp, rp]`. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 5, .memref 5]

/-- `rp` deepest (→ RDI), then `mp` (→ RSI), `z0p` (→ RDX), `z2p` (head → RCX). -/
def inVM : VarMap inΓ :=
  (((VarMap.empty.bind (t := .memref 5) "rp").bind
    (t := .memref 5) "mp").bind
    (t := .memref 4) "z0p").bind (t := .memref 4) "z2p"

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

-- The front translates and lowers `probe_sub5_2x4` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_sub5_2x4` under the 4-pointer buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_sub5_2x4"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX", "RCX"]) (abiTyin := [64, 64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_sub5_2x4`. -/
def asm : Option String := lprog.map renderOwned

end Sub5

/-- The `probe_sub5_2x4` owned leaf `.s`. -/
def probeSub5_2x4Asm : Option String := Sub5.asm

/-! ## 5. Buffer types and the orchestration schedule

Root-order slots (`OrchestrationFront` §Slot convention): slot `0` is the tail
(oldest) element of the context, the highest slot its head. The array-ABI backend
packs argument buffer `j` at `inArgOff j` in root order, so with `ap` at slot 0
and `bp` at slot 1 the C input pointer addresses `[ap | bp]`. -/

/-- A 4-limb buffer (each input half; the two corner products; `m0`), 32 bytes. -/
abbrev B4 : JasminTy := .stackArr 64 4

/-- A 3-limb half-sum buffer (`sa` / `sb`, carry at limb 2), 24 bytes. -/
abbrev B3 : JasminTy := .stackArr 64 3

/-- A 5-limb buffer (the middle product `m`; the middle term `z1`), 40 bytes. -/
abbrev B5 : JasminTy := .stackArr 64 5

/-- The 8-limb result / accumulator buffer, 64 bytes. -/
abbrev B8 : JasminTy := .stackArr 64 8

/-- The orchestration argument context, newest-first `[bp, ap]`: `ap` is the tail
    (root slot 0), `bp` the head (root slot 1). -/
abbrev OrchΓ : Ctxt jasminDialect := [B4, B4]

/-- The 9-call reg-ptr-out Karatsuba multiply schedule. `nArgs = 2`, so call `k`
    binds its result at slot `2 + k`.

    * `z0`, `z2` — the corner products at sub-buffer offsets (slots 2, 3);
    * `sa`, `sb` — the half-sums via `probe_add2c` (slots 4, 5);
    * `m0` — the low middle product `sa_lo·sb_lo` (slot 6);
    * `m` — the corrected middle product via `probe_midcorrect` (slot 7);
    * `z1 = m − z0 − z2` via `probe_sub5_2x4` (slot 8);
    * `base8 = join8(z0, z2)` (slot 9);
    * `r = base8 + z1·2^128` via `probe_addinto8_5at2` (slot 10).

    Result slot 10 (type `B8`) is the full 512-bit product. -/
def kara4Schedule : List CallPhase :=
  [ { leaf := "probe_mul2", argTys := [B4, B4], retTy := B4, argSlots := [0, 1], argOffs := [0, 0] }
  , { leaf := "probe_mul2", argTys := [B4, B4], retTy := B4, argSlots := [0, 1], argOffs := [16, 16] }
  , { leaf := "probe_add2c", argTys := [B4, B4], retTy := B3, argSlots := [0, 0], argOffs := [0, 16] }
  , { leaf := "probe_add2c", argTys := [B4, B4], retTy := B3, argSlots := [1, 1], argOffs := [0, 16] }
  , { leaf := "probe_mul2", argTys := [B3, B3], retTy := B4, argSlots := [4, 5], argOffs := [0, 0] }
  , { leaf := "probe_midcorrect", argTys := [B4, B3, B3], retTy := B5, argSlots := [6, 4, 5] }
  , { leaf := "probe_sub5_2x4", argTys := [B5, B4, B4], retTy := B5, argSlots := [7, 2, 3] }
  , { leaf := "probe_join8", argTys := [B4, B4], retTy := B8, argSlots := [2, 3] }
  , { leaf := "probe_addinto8_5at2", argTys := [B8, B5], retTy := B8, argSlots := [9, 8] } ]

/-- The front-generated straight-line orchestration `Com`. Returns the slot-10
    result (type `B8`). `none` only on an ill-typed / out-of-range slot. -/
def kara4SchedCom : Option (Com jasminDialect OrchΓ B8) :=
  buildOrchCom OrchΓ kara4Schedule 10 B8

-- Generation gate: the schedule resolves to a well-typed orchestration `Com`
-- (front / dialect level, not the render).
#guard kara4SchedCom.isSome

/-! ## 6. Array-ABI export

`Com.toLprogArrAbi` threads the schedule's per-call operand byte offsets onto the
array-ABI call records before `emitOneCall` folds them into the operand `leaq`
displacements. `schedArgOffs kara4Schedule` is the `argOffs` of each phase in call
order. -/

/-- The owned AT&T `.s` for `mpn_kara4_sched`: the array-ABI orchestration with the
    schedule's operand byte offsets, rendered by the owned printer. -/
def kara4SchedAsm : Option String :=
  kara4SchedCom.map (fun c =>
    renderOwned (Com.toLprogArrAbi c "mpn_kara4_sched" (schedArgOffs kara4Schedule)))

/-! ## 7. Emit driver

The renders are written while this module elaborates, so `lake` owns them as
build outputs. The seven `.s` — the orchestration and its six owned leaf callees
(`probe_mul2` / `probe_add2c` reused) — link into the C byte-KAT against a
`__int128` concatenated-input reference. -/

/-- Write the orchestration and the leaf `.s` into the reg-ptr-out KAT gen
    directory. -/
def emitMain : IO Unit := do
  let dir := "bench/regptr_out_probe/gen_com"
  IO.FS.createDirAll dir
  match kara4SchedAsm with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_kara4_sched_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/mpn_kara4_sched_owned.s"
      IO.println "  array-ABI Karatsuba orchestration, 3 sub-multiplies, REAL calls"
  | none => throw (IO.userError "buildOrchCom / offset lowering declined the kara4 schedule")
  match probeJoin8Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_join8_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_join8_owned.s"
  | none => IO.println "SKIP probe_join8: front declined"
  match probeAddInto8_5At2Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_addinto8_5at2_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_addinto8_5at2_owned.s"
  | none => IO.println "SKIP probe_addinto8_5at2: front declined"
  match probeMidCorrectAsm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_midcorrect_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_midcorrect_owned.s"
  | none => IO.println "SKIP probe_midcorrect: front declined"
  match probeSub5_2x4Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_sub5_2x4_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_sub5_2x4_owned.s"
  | none => IO.println "SKIP probe_sub5_2x4: front declined"
  match MpnMul2FixedFrontEmit.probeMul2Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_mul2_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_mul2_owned.s"
  | none => IO.println "SKIP probe_mul2: fixed-2 schoolbook multiply front declined"
  match MpnAddSub2FixedFrontEmit.probeAdd2cAsm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_add2c_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_add2c_owned.s"
  | none => IO.println "SKIP probe_add2c: fixed-2 add-with-carry front declined"

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnKara4SchedFrontEmit
