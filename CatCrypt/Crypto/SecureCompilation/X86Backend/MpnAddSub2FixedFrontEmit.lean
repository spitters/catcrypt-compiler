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
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Fixed 2-limb add-with-carry and subtract-with-borrow, reg-ptr-out, OWNED x86

Two fixed-size leaves for the Karatsuba recombination, both straight-line
(loop-free) and front-compiled to the owned x86 backend:

* `probe_add2c(rp, ap, bp)` sets `rp[0..2) = (ap[0..2) + bp[0..2)) mod 2^128`
  and `rp[2]` to the carry-out bit (`0` or `1`). The three output limbs are the
  two sum words plus the carry, so a half-sum that overflows 128 bits is
  captured in full.
* `probe_sub2(rp, ap, bp)` sets `rp[0..2) = (ap[0..2) − bp[0..2)) mod 2^128`
  (two's-complement wrapping over full 64-bit words) and `rp[2]` to the
  borrow-out bit (`0` or `1`).

```
  add2cBody / sub2Body
    (LowCT: RArrLoad ap/bp, SAdd/SSub words, bSltu carry/borrow, RArrStore rp)
    --(translateDialectControl + cryptoDialectToJasminCom)--> Com jasminDialect
    --(Com.toLprogPhysAbi, ["RDI","RSI","RDX"])-------------> Lprog
    --(renderOwned)----------------------------------------> gen_com/*_owned.s
```

## Algorithm

With `a = a0 + a1·2^64` and `b = b0 + b1·2^64`:

```
  add2c:  s0 = a0 + b0,           c0 = (s0 <u a0)
          s1 = a1 + b1 + c0,      c1 = carry-out of the two-add column
          rp = [s0, s1, c1]
  sub2:   d0 = a0 − b0,           w0 = (a0 <u b0)
          d1 = a1 − b1 − w0,      w1 = borrow-out of the two-sub column
          rp = [d0, d1, w1]
```

Each carry/borrow bit is synthesised branch-free by
`FieldReduceIdioms.bSltu` (the `ltuCmds` shape reused from `MpnMul1FrontEmit`),
the alphabet the covered `SExpr` fragment admits (`SLt` has no dialect
lowering). Subtraction uses the covered `SSub`, the same constructor `ltuCmds`
itself uses for its magnitude test.

## ABI

```c
extern void probe_add2c(uint64_t *rp, const uint64_t *ap, const uint64_t *bp);
extern void probe_sub2 (uint64_t *rp, const uint64_t *ap, const uint64_t *bp);
```

`rp` (RDI, 3 words), `ap` (RSI, 2 words), `bp` (RDX, 2 words). Buffers-only,
reg-ptr-out: the result is written through `rp`, no scalar arguments and no
runtime trip count.

## Main results

* `add2cBody` / `sub2Body` — the straight-line covered `LowCT` bodies.
* `add2cLoweredOpt` / `sub2LoweredOpt` and the `#guard` on each `.isSome` — the
  front translates and lowers each body to a `Com jasminDialect` end-to-end.
* `probeAdd2cLprog` / `probeSub2Lprog` and `probeAdd2cAsm` / `probeSub2Asm` —
  the owned `Lprog`s and rendered AT&T `.s`, via `Com.toLprogPhysAbi` under the
  buffers-only ABI `["RDI","RSI","RDX"]` and `renderOwned`.
* `emitMain` — writes `probe_add2c_owned.s` and `probe_sub2_owned.s` for the
  reg-ptr-out byte-KAT.

## Scope

The module ELABORATES the front pipeline and the owned render; the byte-exact
sum/difference identities are the external C KAT (`bench/regptr_out_probe`)
against a `__int128` reference, the instrument that catches a dropped argument
register or a mis-marshalled out-pointer that the denotation gate does not.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSub2FixedFrontEmit

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

/-! ## 1. Slots and index constants -/

/-- The output-array slot `rp` (3 words: two result limbs + carry/borrow). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 3)⟩

/-- The first operand-array slot `ap` (2 words). -/
def apLoc : Located := ⟨"ap", .TBytes (8 * 2)⟩

/-- The second operand-array slot `bp` (2 words). -/
def bpLoc : Located := ⟨"bp", .TBytes (8 * 2)⟩

/-- The three index-constant scalar slots `ix0, ix1, ix2`. -/
def idxInit : List LowCT :=
  (List.range 3).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `a0, a1` from `ap[0..1]` and `b0, b1` from `bp[0..1]`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"a0", .TU64⟩ apLoc "ix0"
  , .RArrLoad ⟨"a1", .TU64⟩ apLoc "ix1"
  , .RArrLoad ⟨"b0", .TU64⟩ bpLoc "ix0"
  , .RArrLoad ⟨"b1", .TU64⟩ bpLoc "ix1" ]

/-! ## 2. The add-with-carry body -/

/-- The two-limb add-with-carry column sums:

    * `s0 = a0 + b0`, carry `c0 = (s0 <u a0)`;
    * `s1a = a1 + b1`, `c1a = (s1a <u a1)`;
    * `s1 = s1a + c0`, `c1b = (s1 <u s1a)`;
    * carry-out `c1 = c1a + c1b`.

    At most one of `c1a`, `c1b` is set, so their sum is the `0`/`1` carry. -/
def addColumns : List LowCT :=
  [ .RScalarSetExpr "s0" (.SAdd (sv "a0") (sv "b0")) ]
  ++ ltuCmds "c0" (sv "s0") (sv "a0")
  ++ [ .RScalarSetExpr "s1a" (.SAdd (sv "a1") (sv "b1")) ]
  ++ ltuCmds "c1a" (sv "s1a") (sv "a1")
  ++ [ .RScalarSetExpr "s1" (.SAdd (sv "s1a") (sv "c0")) ]
  ++ ltuCmds "c1b" (sv "s1") (sv "s1a")
  ++ [ .RScalarSetExpr "c1" (.SAdd (sv "c1a") (sv "c1b")) ]

/-- Store `s0, s1, c1` through the `rp` pointer. -/
def addStore : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"s0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"s1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"c1", .TU64⟩ ]

/-- The full straight-line 2-limb add-with-carry body. -/
def add2cBody : LowCT :=
  seqAll (idxInit ++ loadInputs ++ addColumns ++ addStore)

/-! ## 3. The subtract-with-borrow body -/

/-- The two-limb subtract-with-borrow column differences:

    * `d0 = a0 − b0`, borrow `w0 = (a0 <u b0)`;
    * `d1a = a1 − b1`, `wa = (a1 <u b1)`;
    * `d1 = d1a − w0`, `wb = (d1a <u w0)`;
    * borrow-out `w1 = wa + wb`.

    At most one of `wa`, `wb` is set, so their sum is the `0`/`1` borrow. -/
def subColumns : List LowCT :=
  [ .RScalarSetExpr "d0" (.SSub (sv "a0") (sv "b0")) ]
  ++ ltuCmds "w0" (sv "a0") (sv "b0")
  ++ [ .RScalarSetExpr "d1a" (.SSub (sv "a1") (sv "b1")) ]
  ++ ltuCmds "wa" (sv "a1") (sv "b1")
  ++ [ .RScalarSetExpr "d1" (.SSub (sv "d1a") (sv "w0")) ]
  ++ ltuCmds "wb" (sv "d1a") (sv "w0")
  ++ [ .RScalarSetExpr "w1" (.SAdd (sv "wa") (sv "wb")) ]

/-- Store `d0, d1, w1` through the `rp` pointer. -/
def subStore : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"d0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"d1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"w1", .TU64⟩ ]

/-- The full straight-line 2-limb subtract-with-borrow body. -/
def sub2Body : LowCT :=
  seqAll (idxInit ++ loadInputs ++ subColumns ++ subStore)

/-! ## 4. Input context + `VarMap` (`rp ← RDI`, `ap ← RSI`, `bp ← RDX`) -/

/-- Head-first kernel context `[bp, ap, rp]`: `rp` a 3-cell `u64` memref, `ap`
    and `bp` 2-cell `u64` memrefs. -/
def inΓ : Ctx := [.memref 2, .memref 2, .memref 3]

/-- `rp` deepest (→ RDI), then `ap` (→ RSI), then `bp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 3) "rp").bind
    (t := .memref 2) "ap").bind (t := .memref 2) "bp"

/-! ## 5. Front-compile, lower -/

/-- Push a body through the direct control front and cap with `ret rp`. -/
def frontComOf (body : LowCT) : Option (Com catCryptDialect inΓ (.memref 3)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 3, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- Lower a front-emitted dialect program to a `Com jasminDialect`. -/
def loweredOf (body : LowCT) :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontComOf body with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-- The front-lowered add-with-carry program. -/
def add2cLoweredOpt := loweredOf add2cBody

/-- The front-lowered subtract-with-borrow program. -/
def sub2LoweredOpt := loweredOf sub2Body

-- The front translates and lowers each body end-to-end.
#guard add2cLoweredOpt.isSome
#guard sub2LoweredOpt.isSome

/-! ## 6. The owned `Lprog`s and the rendered `.s`

`Com.toLprogPhysAbi` lowers each straight-line `Com` to the buffers-only SysV
ABI `probe_*(rp = RDI, ap = RSI, bp = RDX)`: the memref self-addressing emits
the `LOADIDX` input loads and the `STOREIDX` reg-ptr-out stores, `forceLivePin`
keeps the three pointer arguments in distinct registers. The bodies carry no
multiplies, so no `fuseMulHiLprog` post-pass. `renderOwned` is the owned AT&T
printer with the basic-block optimisation pass. -/

/-- The owned two-address `Lprog` for `probe_add2c` under the buffers-only ABI. -/
def probeAdd2cLprog : Option Lprog :=
  add2cLoweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_add2c"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned two-address `Lprog` for `probe_sub2` under the buffers-only ABI. -/
def probeSub2Lprog : Option Lprog :=
  sub2LoweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_sub2"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_add2c`. -/
def probeAdd2cAsm : Option String :=
  probeAdd2cLprog.map renderOwned

/-- The owned AT&T `.s` text for `probe_sub2`. -/
def probeSub2Asm : Option String :=
  probeSub2Lprog.map renderOwned

/-! ## 7. Emit driver

The renders are written while this module elaborates, so `lake` produces them
from this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for `probe_add2c` and `probe_sub2` into the
    reg-ptr-out probe KAT gen directory. -/
def emitMain : IO Unit := do
  let dir := "bench/regptr_out_probe/gen_com"
  IO.FS.createDirAll dir
  match probeAdd2cAsm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_add2c_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_add2c_owned.s"
  | none => IO.println "SKIP probe_add2c: fixed-2 add-with-carry front declined"
  match probeSub2Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_sub2_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_sub2_owned.s"
  | none => IO.println "SKIP probe_sub2: fixed-2 subtract-with-borrow front declined"

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSub2FixedFrontEmit
