/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul2FixedFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul2FixedFrontEmit

@[expose] public section

set_option autoImplicit false

/-!
# Leaf-call nest over the memref front: a `probe_mul2` call plus regArith combine

A straight-line `LowCT` that mixes an `RCallN "probe_mul2"` leaf call — whose
destination is a scratch memref buffer — with `RArrLoad` / `RArrStore` array
access and `RScalarSetExpr` index arithmetic, front-compiled by the direct
control front and lowered to the owned x86 backend.

```
  probeBody (LowCT: RScalarSetExpr index consts, RCallN probe_mul2 → scratch
             memref, RArrLoad the product limbs, RArrStore to rp)
    --(translateDialectControl + cryptoDialectToJasminCom)--> Com jasminDialect
    --(Com.toLprogPhysAbi, ["RDI","RSI","RDX"])-------------> Lprog
    --(fuseMulHiLprog; renderOwned)------------------------> owned AT&T `.s`
```

## Scratch-memref `RCallN` lowering

`RCallN "probe_mul2" [dest] [ap, bp]` with a memref-typed `dest` lowers cleanly
end-to-end: the front binds `dest` as a fresh memref slot, `RArrLoad` reads the
product limbs from it, and the whole body reaches a rendered owned `.s`. The
lowering treats the leaf as opaque, so the memref destination is admitted with
no additional support.

The call the front emits is value-returning: `loopCallNDestsD` models each
`RCallN` destination as the *result* of `extCall (callNLeafName f i)`, so the
lowered call passes the two argument pointers in `RDI` / `RSI` and captures the
product-buffer pointer from `RAX`, under the mangled leaf name
`callN:probe_mul2#0`.

## Fresh-buffer scope

The front admits memref slots only from the entry context (the ABI pointers) or
as leaf-call results. `RLetZero` — the only buffer-declaring `LowCT`
constructor — is elided (its faithful image `memrefZero` has no jasmin
lowering), so a fresh scratch buffer cannot be declared and then written by
`RArrStore`. `gap1Inline` witnesses that an `RLetZero` scratch buffer followed
by an `RArrStore` into it is declined by the front.

## Main results

* `probeBody` — the straight-line `LowCT` mixing an `RCallN "probe_mul2"`
  scratch-memref leaf call with `RArrLoad` / `RArrStore` and `RScalarSetExpr`.
* `#guard` on the `.isSome` of `translateDialectControl` and of
  `DialectToJasminCom.cryptoDialectToJasminCom ∘ frontCom` — the front translates
  and lowers `probeBody` to a `Com jasminDialect` end-to-end.
* `probeLprog` / `probeAsm` — the owned `Lprog` and rendered AT&T `.s` via
  `Com.toLprogPhysAbi` under the buffers-only ABI `["RDI","RSI","RDX"]`, the
  `fuseMulHiLprog` post-pass, and `renderOwned`.
* `gap1Inline` and its `#guard` — the front declines a fresh `RLetZero` scratch
  buffer written by `RArrStore`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4NestProbe

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (seqAll ltuCmds sv)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (renderOwned)

/-! ## 1. The straight-line body -/

/-- The output-array slot `rp` (8 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 8)⟩

/-- The multiplicand-array slot `ap` (4 words). -/
def apLoc : Located := ⟨"ap", .TBytes (8 * 4)⟩

/-- The multiplier-array slot `bp` (4 words). -/
def bpLoc : Located := ⟨"bp", .TBytes (8 * 4)⟩

/-- The scratch product-array slot `p00` (4 words), bound by the leaf call. -/
def p00Loc : Located := ⟨"p00", .TBytes (8 * 4)⟩

/-- The eight index-constant scalar slots `ix0..ix7`. -/
def idxInit : List LowCT :=
  (List.range 8).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- A leaf-call nest: `RCallN "probe_mul2"` into a scratch memref, `RArrLoad`
    the product limbs from it, `RArrStore` them to `rp`. -/
def probeBody : LowCT :=
  seqAll (idxInit ++
    [ .RCallN "probe_mul2" [p00Loc] [apLoc, bpLoc]
    , .RArrLoad ⟨"r0", .TU64⟩ p00Loc "ix0"
    , .RArrLoad ⟨"r1", .TU64⟩ p00Loc "ix1"
    , .RArrLoad ⟨"r2", .TU64⟩ p00Loc "ix2"
    , .RArrLoad ⟨"r3", .TU64⟩ p00Loc "ix3"
    , .RArrStore rpLoc "ix0" ⟨"r0", .TU64⟩
    , .RArrStore rpLoc "ix1" ⟨"r1", .TU64⟩
    , .RArrStore rpLoc "ix2" ⟨"r2", .TU64⟩
    , .RArrStore rpLoc "ix3" ⟨"r3", .TU64⟩ ])

/-! ## 2. Input context + `VarMap` (`rp ← RDI`, `ap ← RSI`, `bp ← RDX`) -/

/-- Head-first kernel context `[bp, ap, rp]`. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 8]

/-- `rp` deepest (→ RDI), then `ap` (→ RSI), then `bp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 8) "rp").bind
    (t := .memref 4) "ap").bind (t := .memref 4) "bp"

-- The front translates the leaf-call nest.
#guard (translateDialectControl inVM probeBody).isSome

/-! ## 3. Front-compile, lower -/

/-- Push `probeBody` through the direct control front and cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 8)) :=
  match translateDialectControl inVM probeBody with
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

-- The front lowers `probeBody` to a `Com jasminDialect` end-to-end.
#guard frontCom.isSome
#guard loweredOpt.isSome

/-! ## 4. The owned `Lprog` and the rendered `.s` -/

/-- The owned two-address `Lprog` under the buffers-only ABI. -/
def probeLprog : Option Lprog :=
  loweredOpt.map (fun s =>
    fuseMulHiLprog
      (Com.toLprogPhysAbi s.2.2 "mpn_mul4_nest"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true))
      (saveRdx := false))

/-- The owned AT&T `.s` text. -/
def probeAsm : Option String :=
  probeLprog.map renderOwned

/-! ## 5. Fresh-buffer scope -/

/-- An `RLetZero` scratch buffer written by a sibling `RArrStore`. The front
    elides `RLetZero`, so `ah` is never bound and the `RArrStore` cannot
    resolve its array slot. -/
def gap1Inline : LowCT :=
  .RSeq (seqAll (idxInit ++ [ .RArrLoad ⟨"a2", .TU64⟩ apLoc "ix2" ]))
    (.RLetZero "ah" (.TBytes 16)
      (.RArrStore ⟨"ah", .TBytes 16⟩ "ix0" ⟨"a2", .TU64⟩))

-- The front declines a fresh `RLetZero` scratch buffer written by `RArrStore`.
#guard !(translateDialectControl inVM gap1Inline).isSome

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4NestProbe
