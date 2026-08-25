/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Fixed 2×2 → 4-limb schoolbook multiply, reg-ptr-out, OWNED x86 (front-generated)

`probe_mul2(rp, up, vp)` sets `rp[0..4) = up[0..2) · vp[0..2)` by fixed-size
schoolbook multiplication over full 64-bit words. The kernel is straight-line
(loop-free): the four partial products and the carry-propagating column sums are
a fixed chain of covered `LowCT` bindings, front-compiled by the direct control
front and lowered to the owned x86 backend.

```
  mul2Body (LowCT: RArrLoad up/vp, SMul/SMulHiU partials, SAdd/bSltu carry adds,
            RArrStore rp)
    --(translateDialectControl + cryptoDialectToJasminCom)--> Com jasminDialect
    --(Com.toLprogPhysAbi, ["RDI","RSI","RDX"])-------------> Lprog
    --(fuseMulHiLprog saveRdx:=false; renderOwned)----------> gen_com/probe_mul2_owned.s
```

## Algorithm

With `u = u0 + u1·2^64` and `v = v0 + v1·2^64`, the four word products
`p_ij = u_i · v_j` (each split `SMul` low / `SMulHiU` high) sum by column:

```
  r0 = lo00
  r1 = hi00 + lo01 + lo10           (mod 2^64), carry cw1
  r2 = hi01 + hi10 + lo11 + cw1     (mod 2^64), carry cw2
  r3 = hi11 + cw2
```

Each column carry is synthesised branch-free by `FieldReduceIdioms.bSltu`
(the `ltuCmds` shape reused from `MpnMul1FrontEmit`), the alphabet the covered
`SExpr` fragment admits (`SLt` has no dialect lowering).

## ABI

```c
extern void probe_mul2(uint64_t *rp, const uint64_t *up, const uint64_t *vp);
```

`rp` (RDI, 4 words), `up` (RSI, 2 words), `vp` (RDX, 2 words). Buffers-only,
reg-ptr-out: the product is written through the `rp` pointer, no scalar
arguments and no runtime trip count. The callee shape
`VIR.RegPtrOutCallProbe.probeMul2Asm` targets.

## Main results

* `mul2Body` — the straight-line covered `LowCT` for the 2×2 → 4-limb product.
* `mul2LoweredOpt` / the `#guard` on its `.isSome` — the front translates and
  lowers `mul2Body` to a `Com jasminDialect` end-to-end.
* `probeMul2Lprog` / `probeMul2Asm` — the owned `Lprog` and rendered AT&T `.s`,
  via `Com.toLprogPhysAbi` under the buffers-only ABI `["RDI","RSI","RDX"]`,
  the `fuseMulHiLprog` mulx post-pass, and `renderOwned`.
* `emitMain` — writes `probe_mul2_owned.s` for the reg-ptr-out byte-KAT.

## Scope

The module ELABORATES the front pipeline and the owned render; the byte-exact
product identity is the external C KAT
(`bench/regptr_out_probe`) against a `__int128` reference, the instrument that
catches a dropped argument register or a mis-marshalled out-pointer that the
denotation gate does not.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul2FixedFrontEmit

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit (fuseMulHiLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (renderOwned)

/-! ## 1. The straight-line `LowCT` body -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The output-array slot `rp` (4 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 4)⟩

/-- The multiplicand-array slot `up` (2 words). -/
def upLoc : Located := ⟨"up", .TBytes (8 * 2)⟩

/-- The multiplier-array slot `vp` (2 words). -/
def vpLoc : Located := ⟨"vp", .TBytes (8 * 2)⟩

/-- The four index-constant scalar slots `ix0..ix3` for the array accesses. -/
def idxInit : List LowCT :=
  (List.range 4).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `u0, u1` from `up[0..1]` and `v0, v1` from `vp[0..1]`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"u0", .TU64⟩ upLoc "ix0"
  , .RArrLoad ⟨"u1", .TU64⟩ upLoc "ix1"
  , .RArrLoad ⟨"v0", .TU64⟩ vpLoc "ix0"
  , .RArrLoad ⟨"v1", .TU64⟩ vpLoc "ix1" ]

/-- The four widening partial products `p_ij = u_i · v_j`, low word via `SMul`
    and high word via `SMulHiU`. -/
def partials : List LowCT :=
  [ .RScalarSetExpr "lo00" (.SMul (sv "u0") (sv "v0"))
  , .RScalarSetExpr "hi00" (.SMulHiU (sv "u0") (sv "v0"))
  , .RScalarSetExpr "lo01" (.SMul (sv "u0") (sv "v1"))
  , .RScalarSetExpr "hi01" (.SMulHiU (sv "u0") (sv "v1"))
  , .RScalarSetExpr "lo10" (.SMul (sv "u1") (sv "v0"))
  , .RScalarSetExpr "hi10" (.SMulHiU (sv "u1") (sv "v0"))
  , .RScalarSetExpr "lo11" (.SMul (sv "u1") (sv "v1"))
  , .RScalarSetExpr "hi11" (.SMulHiU (sv "u1") (sv "v1")) ]

/-- The carry-propagating column sums:

    * `r0 = lo00`;
    * `r1 = hi00 + lo01 + lo10`, carry `cw1 = c1a + c1b`;
    * `r2 = hi01 + hi10 + lo11 + cw1`, carry `cw2 = c2a + c2b + c2c`;
    * `r3 = hi11 + cw2`.

    Each `c*` carry-out bit is the branch-free `ltuCmds` of a sum against its
    first summand. -/
def columns : List LowCT :=
  [ .RScalarSetExpr "r0" (sv "lo00")
  , .RScalarSetExpr "s1a" (.SAdd (sv "hi00") (sv "lo01")) ]
  ++ ltuCmds "c1a" (sv "s1a") (sv "hi00")
  ++ [ .RScalarSetExpr "s1b" (.SAdd (sv "s1a") (sv "lo10")) ]
  ++ ltuCmds "c1b" (sv "s1b") (sv "s1a")
  ++ [ .RScalarSetExpr "r1" (sv "s1b")
     , .RScalarSetExpr "cw1" (.SAdd (sv "c1a") (sv "c1b"))
     , .RScalarSetExpr "s2a" (.SAdd (sv "hi01") (sv "hi10")) ]
  ++ ltuCmds "c2a" (sv "s2a") (sv "hi01")
  ++ [ .RScalarSetExpr "s2b" (.SAdd (sv "s2a") (sv "lo11")) ]
  ++ ltuCmds "c2b" (sv "s2b") (sv "s2a")
  ++ [ .RScalarSetExpr "s2c" (.SAdd (sv "s2b") (sv "cw1")) ]
  ++ ltuCmds "c2c" (sv "s2c") (sv "s2b")
  ++ [ .RScalarSetExpr "r2" (sv "s2c")
     , .RScalarSetExpr "cw2" (.SAdd (.SAdd (sv "c2a") (sv "c2b")) (sv "c2c"))
     , .RScalarSetExpr "r3" (.SAdd (sv "hi11") (sv "cw2")) ]

/-- Store the four product words `r0..r3` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"r0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"r1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"r2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"r3", .TU64⟩ ]

/-- The full straight-line 2×2 → 4-limb schoolbook multiply body. -/
def mul2Body : LowCT :=
  seqAll (idxInit ++ loadInputs ++ partials ++ columns ++ storeOutputs)

/-! ## 2. Input context + `VarMap` (`rp ← RDI`, `up ← RSI`, `vp ← RDX`) -/

/-- Head-first kernel context `[vp, up, rp]`: `rp` a 4-cell `u64` memref, `up`
    and `vp` 2-cell `u64` memrefs. -/
def inΓ : Ctx := [.memref 2, .memref 2, .memref 4]

/-- `rp` deepest (→ RDI), then `up` (→ RSI), then `vp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 4) "rp").bind
    (t := .memref 2) "up").bind (t := .memref 2) "vp"

/-! ## 3. Front-compile, lower -/

/-- Push `mul2Body` through the direct control front and cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 4)) :=
  match translateDialectControl inVM mul2Body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def mul2LoweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `mul2Body` end-to-end.
#guard mul2LoweredOpt.isSome

/-! ## 4. The owned `Lprog` and the rendered `.s`

`Com.toLprogPhysAbi` lowers the straight-line `Com` to the buffers-only SysV
ABI `probe_mul2(rp = RDI, up = RSI, vp = RDX)`: the memref self-addressing emits
the `LOADIDX` input loads and the `STOREIDX` reg-ptr-out stores, `forceLivePin`
keeps the three pointer arguments in distinct registers. `fuseMulHiLprog`
coalesces each paired low `MUL` / high `MULXHI` into the printer's two-output
`mulx`; the body is loop-free, so `saveRdx := false`. `renderOwned` is the owned
AT&T printer with the basic-block optimisation pass. -/

/-- The owned two-address `Lprog` for `probe_mul2` under the buffers-only ABI. -/
def probeMul2Lprog : Option Lprog :=
  mul2LoweredOpt.map (fun s =>
    fuseMulHiLprog
      (Com.toLprogPhysAbi s.2.2 "probe_mul2"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true))
      (saveRdx := false))

/-- The owned AT&T `.s` text for `probe_mul2`. -/
def probeMul2Asm : Option String :=
  probeMul2Lprog.map renderOwned

/-! ## 5. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for `probe_mul2` into the reg-ptr-out probe
    KAT gen directory. -/
def emitMain : IO Unit := do
  let dir := "bench/regptr_out_probe/gen_com"
  IO.FS.createDirAll dir
  match probeMul2Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_mul2_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_mul2_owned.s"
  | none => IO.println "SKIP probe_mul2: fixed-2 schoolbook multiply front declined"

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul2FixedFrontEmit
