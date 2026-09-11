/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Fixed 4-limb add, reg-ptr-out, OWNED x86 (front-generated)

`probe_add4(rp, ap, bp)` sets `rp[0..4) = ap[0..4) + bp[0..4)` modulo `2^256`
(the final carry-out is dropped, so the result is exactly four limbs). The
kernel is straight-line (loop-free): the four limb sums and their carry
propagation are a fixed chain of covered `LowCT` bindings, front-compiled by the
direct control front and lowered to the owned x86 backend.

```
  add4Body (LowCT: RArrLoad ap/bp, SAdd + bSltu carry adds, RArrStore rp)
    --(translateDialectControl + cryptoDialectToJasminCom)--> Com jasminDialect
    --(Com.toLprogPhysAbi, ["RDI","RSI","RDX"])-------------> Lprog
    --(renderOwned)----------------------------------------> gen_com/probe_add4_owned.s
```

## Algorithm

With `a = Σ a_i·2^{64 i}` and `b = Σ b_i·2^{64 i}` (`i ∈ [0,4)`), the ripple
carry propagates through the four columns:

```
  s0 = a0 + b0                    (mod 2^64), carry c0
  s1 = a1 + b1 + c0              (mod 2^64), carry cw1
  s2 = a2 + b2 + cw1            (mod 2^64), carry cw2
  s3 = a3 + b3 + cw2            (mod 2^64), final carry dropped
```

Each column carry-out is synthesised branch-free by `FieldReduceIdioms.bSltu`
(the `ltuCmds` shape reused from `MpnMul1FrontEmit`) as the compare of a running
sum against its first summand — the alphabet the covered `SExpr` fragment
admits (`SLt` has no dialect lowering). A two-summand column with carry-in adds
in two `SAdd` steps and sums the two carry bits.

## ABI

```c
extern void probe_add4(uint64_t *rp, const uint64_t *ap, const uint64_t *bp);
```

`rp` (RDI, 4 words), `ap` (RSI, 4 words), `bp` (RDX, 4 words). Buffers-only,
reg-ptr-out: the sum is written through the `rp` pointer, no scalar arguments
and no runtime trip count.

## Main results

* `add4Body` — the straight-line covered `LowCT` for the 4-limb ripple add.
* `add4LoweredOpt` / the `#guard` on its `.isSome` — the front translates and
  lowers `add4Body` to a `Com jasminDialect` end-to-end.
* `probeAdd4Lprog` / `probeAdd4Asm` — the owned `Lprog` and rendered AT&T `.s`,
  via `Com.toLprogPhysAbi` under the buffers-only ABI `["RDI","RSI","RDX"]` and
  `renderOwned`.
* `emitMain` — writes `probe_add4_owned.s` for the reg-ptr-out byte-KAT.

## Scope

The module ELABORATES the front pipeline and the owned render; the byte-exact
sum identity is the external C KAT (`bench/regptr_out_probe`) against a
reference, the instrument that catches a dropped argument register or a
mis-marshalled out-pointer that the denotation gate does not.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAdd4FixedFrontEmit

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (renderOwned)

/-! ## 1. The straight-line `LowCT` body -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The output-array slot `rp` (4 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 4)⟩

/-- The first-summand-array slot `ap` (4 words). -/
def apLoc : Located := ⟨"ap", .TBytes (8 * 4)⟩

/-- The second-summand-array slot `bp` (4 words). -/
def bpLoc : Located := ⟨"bp", .TBytes (8 * 4)⟩

/-- The four index-constant scalar slots `ix0..ix3` for the array accesses. -/
def idxInit : List LowCT :=
  (List.range 4).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `a0..a3` from `ap[0..3]` and `b0..b3` from `bp[0..3]`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"a0", .TU64⟩ apLoc "ix0"
  , .RArrLoad ⟨"a1", .TU64⟩ apLoc "ix1"
  , .RArrLoad ⟨"a2", .TU64⟩ apLoc "ix2"
  , .RArrLoad ⟨"a3", .TU64⟩ apLoc "ix3"
  , .RArrLoad ⟨"b0", .TU64⟩ bpLoc "ix0"
  , .RArrLoad ⟨"b1", .TU64⟩ bpLoc "ix1"
  , .RArrLoad ⟨"b2", .TU64⟩ bpLoc "ix2"
  , .RArrLoad ⟨"b3", .TU64⟩ bpLoc "ix3" ]

/-- The four carry-propagating column sums:

    * `s0 = a0 + b0`, carry `c0`;
    * `s1 = a1 + b1 + c0`, carry `cw1 = c1a + c1b`;
    * `s2 = a2 + b2 + cw1`, carry `cw2 = c2a + c2b`;
    * `s3 = a3 + b3 + cw2` (final carry dropped).

    Each `c*` carry-out bit is the branch-free `ltuCmds` of a running sum against
    its first summand. -/
def columns : List LowCT :=
  [ .RScalarSetExpr "s0" (.SAdd (sv "a0") (sv "b0")) ]
  ++ ltuCmds "c0" (sv "s0") (sv "a0")
  ++ [ .RScalarSetExpr "t1" (.SAdd (sv "a1") (sv "b1")) ]
  ++ ltuCmds "c1a" (sv "t1") (sv "a1")
  ++ [ .RScalarSetExpr "s1" (.SAdd (sv "t1") (sv "c0")) ]
  ++ ltuCmds "c1b" (sv "s1") (sv "t1")
  ++ [ .RScalarSetExpr "cw1" (.SAdd (sv "c1a") (sv "c1b"))
     , .RScalarSetExpr "t2" (.SAdd (sv "a2") (sv "b2")) ]
  ++ ltuCmds "c2a" (sv "t2") (sv "a2")
  ++ [ .RScalarSetExpr "s2" (.SAdd (sv "t2") (sv "cw1")) ]
  ++ ltuCmds "c2b" (sv "s2") (sv "t2")
  ++ [ .RScalarSetExpr "cw2" (.SAdd (sv "c2a") (sv "c2b"))
     , .RScalarSetExpr "s3" (.SAdd (.SAdd (sv "a3") (sv "b3")) (sv "cw2")) ]

/-- Store the four sum words `s0..s3` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"s0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"s1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"s2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"s3", .TU64⟩ ]

/-- The full straight-line 4-limb ripple-carry add body. -/
def add4Body : LowCT :=
  seqAll (idxInit ++ loadInputs ++ columns ++ storeOutputs)

/-! ## 2. Input context + `VarMap` (`rp ← RDI`, `ap ← RSI`, `bp ← RDX`) -/

/-- Head-first kernel context `[bp, ap, rp]`, each a 4-cell `u64` memref. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 4]

/-- `rp` deepest (→ RDI), then `ap` (→ RSI), then `bp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 4) "rp").bind
    (t := .memref 4) "ap").bind (t := .memref 4) "bp"

/-! ## 3. Front-compile, lower -/

/-- Push `add4Body` through the direct control front and cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 4)) :=
  match translateDialectControl inVM add4Body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def add4LoweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `add4Body` end-to-end.
#guard add4LoweredOpt.isSome

/-! ## 4. The owned `Lprog` and the rendered `.s`

`Com.toLprogPhysAbi` lowers the straight-line `Com` to the buffers-only SysV
ABI `probe_add4(rp = RDI, ap = RSI, bp = RDX)`: the memref self-addressing emits
the `LOADIDX` input loads and the `STOREIDX` reg-ptr-out stores, `forceLivePin`
keeps the three pointer arguments in distinct registers. The body carries no
wide multiply, so no `fuseMulHiLprog` post-pass is applied. `renderOwned` is the
owned AT&T printer with the basic-block optimisation pass. -/

/-- The owned two-address `Lprog` for `probe_add4` under the buffers-only ABI. -/
def probeAdd4Lprog : Option Lprog :=
  add4LoweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_add4"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_add4`. -/
def probeAdd4Asm : Option String :=
  probeAdd4Lprog.map renderOwned

/-! ## 5. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for `probe_add4` into the reg-ptr-out probe
    KAT gen directory. -/
def emitMain : IO Unit := do
  let dir := "bench/regptr_out_probe/gen_com"
  IO.FS.createDirAll dir
  match probeAdd4Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_add4_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_add4_owned.s"
  | none => IO.println "SKIP probe_add4: fixed-4 ripple add front declined"

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAdd4FixedFrontEmit
