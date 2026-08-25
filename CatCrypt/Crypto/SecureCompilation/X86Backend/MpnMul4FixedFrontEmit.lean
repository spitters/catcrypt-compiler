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
# Fixed 4×4 → 8-limb schoolbook multiply, reg-ptr-out, OWNED x86 (front-generated)

`probe_mul4(rp, up, vp)` sets `rp[0..8) = up[0..4) · vp[0..4)` by fixed-size
schoolbook multiplication over full 64-bit words. The kernel is straight-line
(loop-free): the sixteen partial products and the carry-propagating column sums
are a fixed chain of covered `LowCT` bindings, front-compiled by the direct
control front and lowered to the owned x86 backend.

```
  mul4Body (LowCT: RArrLoad up/vp, SMul/SMulHiU partials, SAdd/bSltu carry adds,
            RArrStore rp)
    --(translateDialectControl + cryptoDialectToJasminCom)--> Com jasminDialect
    --(Com.toLprogPhysAbi, ["RDI","RSI","RDX"])-------------> Lprog
    --(fuseMulHiLprog saveRdx:=false; renderOwned)----------> gen_com/probe_mul4_owned.s
```

## Algorithm

With `u = Σ u_i·2^(64i)` and `v = Σ v_j·2^(64j)` for `i, j ∈ {0,1,2,3}`, the
sixteen word products `p_ij = u_i · v_j` split into low word `lo_ij` (`SMul`) and
high word `hi_ij` (`SMulHiU`). `lo_ij` contributes to column `i+j` and `hi_ij` to
column `i+j+1`:

```
  col0 = lo00
  col1 = hi00 + lo01 + lo10
  col2 = hi01 + hi10 + lo02 + lo11 + lo20
  col3 = hi02 + hi11 + hi20 + lo03 + lo12 + lo21 + lo30
  col4 = hi03 + hi12 + hi21 + hi30 + lo13 + lo22 + lo31
  col5 = hi13 + hi22 + hi31 + lo23 + lo32
  col6 = hi23 + hi32 + lo33
  col7 = hi33
```

Each column sums several 64-bit values plus the carry WORD out of the previous
column, so its own carry-out can exceed 1. A column is summed as a chain of
`SAdd`s; each `SAdd` step contributes a single carry bit synthesised branch-free
by `FieldReduceIdioms.bSltu` (the `ltuCmds` shape, `sum <u first-summand`). The
column result `r_k` is the last accumulator (low 64 bits of the total), and the
carry WORD into column `k+1` is the sum of those single-bit carries.

## ABI

```c
extern void probe_mul4(uint64_t *rp, const uint64_t *up, const uint64_t *vp);
```

`rp` (RDI, 8 words), `up` (RSI, 4 words), `vp` (RDX, 4 words). Buffers-only,
reg-ptr-out: the product is written through the `rp` pointer, no scalar
arguments and no runtime trip count.

## Main results

* `mul4Body` — the straight-line covered `LowCT` for the 4×4 → 8-limb product.
* `mul4LoweredOpt` / the `#guard` on its `.isSome` — the front translates and
  lowers `mul4Body` to a `Com jasminDialect` end-to-end.
* `probeMul4Lprog` / `probeMul4Asm` — the owned `Lprog` and rendered AT&T `.s`,
  via `Com.toLprogPhysAbi` under the buffers-only ABI `["RDI","RSI","RDX"]`,
  the `fuseMulHiLprog` mulx post-pass, and `renderOwned`.
* `emitMain` — writes `probe_mul4_owned.s` for the reg-ptr-out byte-KAT.

## Scope

The module ELABORATES the front pipeline and the owned render; the byte-exact
product identity is the external C KAT (`bench/regptr_out_probe`) against a
`__int128` schoolbook reference.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4FixedFrontEmit

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

/-- The output-array slot `rp` (8 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 8)⟩

/-- The multiplicand-array slot `up` (4 words). -/
def upLoc : Located := ⟨"up", .TBytes (8 * 4)⟩

/-- The multiplier-array slot `vp` (4 words). -/
def vpLoc : Located := ⟨"vp", .TBytes (8 * 4)⟩

/-- The eight index-constant scalar slots `ix0..ix7` for the array accesses. -/
def idxInit : List LowCT :=
  (List.range 8).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `u0..u3` from `up[0..3]` and `v0..v3` from `vp[0..3]`. -/
def loadInputs : List LowCT :=
  (List.range 4).map (fun i => .RArrLoad ⟨s!"u{i}", .TU64⟩ upLoc s!"ix{i}")
  ++ (List.range 4).map (fun i => .RArrLoad ⟨s!"v{i}", .TU64⟩ vpLoc s!"ix{i}")

/-- The sixteen widening partial products `p_ij = u_i · v_j`, low word `lo{i}{j}`
    via `SMul` and high word `hi{i}{j}` via `SMulHiU`. -/
def partials : List LowCT :=
  (List.range 4).flatMap (fun i =>
    (List.range 4).flatMap (fun j =>
      [ .RScalarSetExpr s!"lo{i}{j}" (.SMul (sv s!"u{i}") (sv s!"v{j}"))
      , .RScalarSetExpr s!"hi{i}{j}" (.SMulHiU (sv s!"u{i}") (sv s!"v{j}")) ]))

/-- Chain the additions of `rest` onto accumulator `prevAcc` (index `i`),
    emitting one branch-free carry bit per step. Returns the emitted commands,
    the carry-bit slot names, and the final accumulator name. -/
def sumColAux (tag : String) (i : Nat) (prevAcc : String) :
    List SExpr → List LowCT × List String × String
  | [] => ([], [], prevAcc)
  | w :: ws =>
      let curAcc := tag ++ "a" ++ toString (i + 1)
      let cbit := tag ++ "c" ++ toString (i + 1)
      let step : List LowCT :=
        [ .RScalarSetExpr curAcc (.SAdd (.SVar prevAcc) w) ]
        ++ ltuCmds cbit (.SVar curAcc) (.SVar prevAcc)
      let (restCmds, restCarries, lastAcc) := sumColAux tag (i + 1) curAcc ws
      (step ++ restCmds, cbit :: restCarries, lastAcc)

/-- Sum one column of `vals` (partial-product words plus the incoming carry
    word). Binds `rname` to the low 64 bits and `cwName` to the carry WORD into
    the next column (the sum of the per-step carry bits). `tag` prefixes the
    accumulator and carry-bit scratch slots so they stay globally unique. -/
def sumCol (tag rname cwName : String) : List SExpr → List LowCT
  | [] => [ .RScalarSetExpr rname (.SLit 0), .RScalarSetExpr cwName (.SLit 0) ]
  | w0 :: rest =>
      let acc0 := tag ++ "a0"
      let (chain, carries, lastAcc) := sumColAux tag 0 acc0 rest
      let cwExpr : SExpr :=
        match carries with
        | [] => .SLit 0
        | c :: cs => cs.foldl (fun e x => .SAdd e (.SVar x)) (.SVar c)
      [ .RScalarSetExpr acc0 w0 ]
      ++ chain
      ++ [ .RScalarSetExpr rname (.SVar lastAcc)
         , .RScalarSetExpr cwName cwExpr ]

/-- The eight carry-propagating column sums `r0..r7` with running carry words
    `cw0..cw7`. Column `k+1` consumes `cwk`. -/
def columns : List LowCT :=
     sumCol "k0" "r0" "cw0" [sv "lo00"]
  ++ sumCol "k1" "r1" "cw1" [sv "hi00", sv "lo01", sv "lo10", sv "cw0"]
  ++ sumCol "k2" "r2" "cw2"
       [sv "hi01", sv "hi10", sv "lo02", sv "lo11", sv "lo20", sv "cw1"]
  ++ sumCol "k3" "r3" "cw3"
       [sv "hi02", sv "hi11", sv "hi20", sv "lo03", sv "lo12", sv "lo21",
        sv "lo30", sv "cw2"]
  ++ sumCol "k4" "r4" "cw4"
       [sv "hi03", sv "hi12", sv "hi21", sv "hi30", sv "lo13", sv "lo22",
        sv "lo31", sv "cw3"]
  ++ sumCol "k5" "r5" "cw5"
       [sv "hi13", sv "hi22", sv "hi31", sv "lo23", sv "lo32", sv "cw4"]
  ++ sumCol "k6" "r6" "cw6" [sv "hi23", sv "hi32", sv "lo33", sv "cw5"]
  ++ sumCol "k7" "r7" "cw7" [sv "hi33", sv "cw6"]

/-- Store the eight product words `r0..r7` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  (List.range 8).map (fun i => .RArrStore rpLoc s!"ix{i}" ⟨s!"r{i}", .TU64⟩)

/-- The full straight-line 4×4 → 8-limb schoolbook multiply body. -/
def mul4Body : LowCT :=
  seqAll (idxInit ++ loadInputs ++ partials ++ columns ++ storeOutputs)

/-! ## 2. Input context + `VarMap` (`rp ← RDI`, `up ← RSI`, `vp ← RDX`) -/

/-- Head-first kernel context `[vp, up, rp]`: `rp` an 8-cell `u64` memref, `up`
    and `vp` 4-cell `u64` memrefs. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 8]

/-- `rp` deepest (→ RDI), then `up` (→ RSI), then `vp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 8) "rp").bind
    (t := .memref 4) "up").bind (t := .memref 4) "vp"

/-! ## 3. Front-compile, lower -/

/-- Push `mul4Body` through the direct control front and cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 8)) :=
  match translateDialectControl inVM mul4Body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 8, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def mul4LoweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `mul4Body` end-to-end.
#guard mul4LoweredOpt.isSome

/-! ## 4. The owned `Lprog` and the rendered `.s`

`Com.toLprogPhysAbi` lowers the straight-line `Com` to the buffers-only SysV
ABI `probe_mul4(rp = RDI, up = RSI, vp = RDX)`: the memref self-addressing emits
the `LOADIDX` input loads and the `STOREIDX` reg-ptr-out stores, `forceLivePin`
keeps the three pointer arguments in distinct registers. `fuseMulHiLprog`
coalesces each paired low `MUL` / high `MULXHI` into the printer's two-output
`mulx`; the body is loop-free, so `saveRdx := false`. `renderOwned` is the owned
AT&T printer with the basic-block optimisation pass. -/

/-- The owned two-address `Lprog` for `probe_mul4` under the buffers-only ABI. -/
def probeMul4Lprog : Option Lprog :=
  mul4LoweredOpt.map (fun s =>
    fuseMulHiLprog
      (Com.toLprogPhysAbi s.2.2 "probe_mul4"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true))
      (saveRdx := false))

/-- The owned AT&T `.s` text for `probe_mul4`. -/
def probeMul4Asm : Option String :=
  probeMul4Lprog.map renderOwned

/-! ## 5. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for `probe_mul4` into the reg-ptr-out probe
    KAT gen directory. -/
def emitMain : IO Unit := do
  let dir := "bench/regptr_out_probe/gen_com"
  IO.FS.createDirAll dir
  match probeMul4Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_mul4_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_mul4_owned.s"
  | none => IO.println "SKIP probe_mul4: fixed-4 schoolbook multiply front declined"

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4FixedFrontEmit
