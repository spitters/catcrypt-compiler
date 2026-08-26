/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddFrontEmit
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
import CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

set_option autoImplicit false

/-!
# Runtime-N `mpn_add_n` through the carry-selecting rolled-loop front

The deployed `mpn_add_n_loop_owned` (`MpnLoopFrontEmit`) threads its carry
through the plain body front (`translateDialectControl`), whose branch-free
half-add split costs two shift/mask stages per limb and renders no `adcx`.
`FrontRoutePlan` carries a second body-front axis value for the same rolled
runtime-N loop shape: `.carrySelect`
(`CarryChainSelect.translateDialectCarrySelect`), the front
`MpnMul1CarrySelectEmit` deploys for `mpn_mul_1`. This module routes the
`mpn_add_n` loop body through that axis, in the `bSltu` window form the
selector fuses to `bvAddCarryLo`/`bvAddCarryHi` (the shape of
`MpnAddFrontEmit.addChain`), at two tilings:

* **1 limb per trip** (`addAdxRollProg`) — the deployed kernel's loop
  structure, ABI and scalar carry accumulator, with the per-limb carry window
  in selectable form: `t := a[i] + b[i]; ltu c1 t a[i]; s := t + cy;
  ltu c2 s t; cy := c1 + c2`.
* **4 limbs per trip** (`addAdxRoll4Prog`) — the GMP/`blk4` tiling: four
  chained carry windows per iteration, limb indices `4·idx + j` computed from
  the trip counter, the inter-block carry crossing the back-edge as the
  scalar accumulator value. The counter argument is the BLOCK count (the
  `blk4` ABI: `4 | n`, `n/4` in `RCX`).

Both export through `ComL.toLprogPhysAbiScalarAcc` (carry seeded `MOV acc, #0`
via `mpnSeedImm`, carry-out in `RAX`, GMP 4-register signature) and render
after `AdxChainFuse.fuseAdxChain`, which collapses the value-threaded
`ADCX`/`ADCXHI` limb triples into a live-flag `adcx` chain inside the body.
The carry still crosses the back-edge as a value (`bt`-inject on entry,
`setc` capture on exit) — the per-block reseed cost of the hand `blk4` twin.
A carry kept in `CF` across the back-edge itself is outside the machine
alphabet: the exporter's loop control is `cmpq`/`jne` over a `SUB`-decremented
counter (`CF`-clobbering) and `JInstr`/the printer carry no `dec`/`lea`.

Acceptance is reported by `#eval` probes rather than gates: each front
compile prints `accepted` (with `adcx`/back-edge shape facts) or `declined`,
and `emitMain` writes only the accepted kernels. The libgmp KAT wiring
follows acceptance (`bench/integration/Makefile.loop_owned`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddNAdxRolledFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype
  (seqAll N Γbody vmBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
  (ΓouterCarry mpnSeedImm gmpAbiArgs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddFrontEmit (ltuCmds v)

/-! ## 1. The loop bodies in selectable carry-window form -/

/-- One add carry-window limb: sum `t := a + b` with carry `ca`, then
    `s := t + cin` with carry `cb`, carry-out `cout := ca + cb`; the
    intermediate slot names carry the suffix `sfx`. The `MpnAddFrontEmit.addChain` mid-step
    shape, the one `CarryChainSelect.selectGo` fuses to
    `bvAddCarryLo`/`bvAddCarryHi`. -/
def limbWin (sfx a b cin cout : String) : List LowCT :=
  [ .RScalarSetExpr s!"t{sfx}" (.SAdd (v a) (v b)) ]
  ++ ltuCmds s!"ca{sfx}" (v s!"t{sfx}") (v a)
  ++ [ .RScalarSetExpr s!"s{sfx}" (.SAdd (v s!"t{sfx}") (v cin)) ]
  ++ ltuCmds s!"cb{sfx}" (v s!"s{sfx}") (v s!"t{sfx}")
  ++ [ .RScalarSetExpr cout (.SAdd (v s!"ca{sfx}") (v s!"cb{sfx}")) ]

/-- The 1-limb-per-trip `mpn_add_n` body: load `a[idx]`/`b[idx]`, one carry
    window threading the scalar accumulator `cy`, store the sum limb. -/
def addAdxBody : LowCT := seqAll <|
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"av", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RArrLoad ⟨"bv", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix" ]
  ++ limbWin "0" "av" "bv" "cy" "cy"
  ++ [ .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"s0", .TU64⟩ ]

/-- The 4-limb-per-trip body: limb indices `4·idx + j`, four chained carry
    windows (`cy → k1 → k2 → k3 → cy`), four stores. The counter argument is
    the block count. -/
def addAdx4Body : LowCT := seqAll <|
  [ .RScalarSetExpr "ix0" (.SShl (.SVar "idx") (.SLit 2))
  , .RScalarSetExpr "ix1" (.SAdd (v "ix0") (.SLit 1))
  , .RScalarSetExpr "ix2" (.SAdd (v "ix0") (.SLit 2))
  , .RScalarSetExpr "ix3" (.SAdd (v "ix0") (.SLit 3))
  , .RArrLoad ⟨"a0", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix0"
  , .RArrLoad ⟨"b0", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix0"
  , .RArrLoad ⟨"a1", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix1"
  , .RArrLoad ⟨"b1", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix1"
  , .RArrLoad ⟨"a2", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix2"
  , .RArrLoad ⟨"b2", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix2"
  , .RArrLoad ⟨"a3", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix3"
  , .RArrLoad ⟨"b3", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix3" ]
  ++ limbWin "0" "a0" "b0" "cy" "k1"
  ++ limbWin "1" "a1" "b1" "k1" "k2"
  ++ limbWin "2" "a2" "b2" "k2" "k3"
  ++ limbWin "3" "a3" "b3" "k3" "cy"
  ++ [ .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix0" ⟨"s0", .TU64⟩
     , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix1" ⟨"s1", .TU64⟩
     , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix2" ⟨"s2", .TU64⟩
     , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix3" ⟨"s3", .TU64⟩ ]

/-! ## 2. Front compile through the carry-select rolled-loop axis

`ΓouterCarry`, the count/init/invariant variables, the `VarMap` and the
`mpnSeedImm`/`gmpAbiArgs` ABI are the deployed add kernel's
(`MpnLoopFrontEmit.addRtProgOpt`); only the body front axis differs. -/

/-- Front-compile a carry-window body through
    `FrontRoutePlan.compileLoop .carrySelect` at the runtime trip count. -/
def adxRollProgOf (body : LowCT) : Option (ComL ΓouterCarry (mapTy (.sword 64))) :=
  Dialects.FrontRoutePlan.compileLoop (Γouter := ΓouterCarry)
    (accCTy := .sword 64) (invCTys := [.memref N, .memref N, .memref N])
    .carrySelect (.runtime (.there .here))
    vmBody "cy" body
    (.here)
    (.cons (.there (.there (.there .here)))
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) .nil)))

/-- The 1-limb-per-trip carry-selected `mpn_add_n` program. -/
def addAdxRollProg : Option (ComL ΓouterCarry (mapTy (.sword 64))) :=
  adxRollProgOf addAdxBody

/-- The 4-limb-per-trip (block-count ABI) carry-selected program. -/
def addAdxRoll4Prog : Option (ComL ΓouterCarry (mapTy (.sword 64))) :=
  adxRollProgOf addAdx4Body

/-- Export under the GMP 4-register signature with the `MOV acc, #0` carry
    seed, fuse the value-threaded ADX triples, render AT&T. -/
def toAsmOf (name : String) (prog : Option (ComL ΓouterCarry (mapTy (.sword 64)))) :
    Option String :=
  prog.map (fun c =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (AdxChainFuse.fuseAdxChain
      (ComL.toLprogPhysAbiScalarAcc c name
        (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64])))

def addAdxRollAsm : Option String :=
  toAsmOf "mpn_add_n_adxroll_loop_owned" addAdxRollProg
def addAdxRoll4Asm : Option String :=
  toAsmOf "mpn_add_n_adxroll4_loop_owned" addAdxRoll4Prog

/-! ## 3. Acceptance probes (printed, non-fatal) -/

/-- One-line acceptance/shape report for a rendered kernel. -/
def acceptanceLine (tag : String) (asm? : Option String) : String :=
  match asm? with
  | none => s!"{tag}: front DECLINED"
  | some s =>
      s!"{tag}: accepted; adcx={strContains s "adcxq"} " ++
      s!"backedge={strContains s "jne .L"} unhandled={strContains s "UNHANDLED"} " ++
      s!"lines={(s.splitOn "\n").length}"

#eval IO.println (acceptanceLine "adxroll (1 limb/trip)" addAdxRollAsm)
#eval IO.println (acceptanceLine "adxroll4 (4 limbs/trip)" addAdxRoll4Asm)

/-! ## 4. Emit driver (writes accepted kernels only) -/

/-- Write the accepted carry-selected rolled add kernels to
    `bench/integration/gen_com/` (run from the repo root); a declined front
    is reported, not fatal. KAT wiring follows acceptance. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/integration/gen_com"
  let wr (p tag : String) (asm? : Option String) : IO Unit := do
    match asm? with
    | some s => IO.FS.writeFile p s; IO.println s!"wrote {p}"
    | none => IO.println s!"{tag}: front declined, nothing written"
  wr "bench/integration/gen_com/mpn_add_n_adxroll_loop_owned.s"
    "adxroll" addAdxRollAsm
  wr "bench/integration/gen_com/mpn_add_n_adxroll4_loop_owned.s"
    "adxroll4" addAdxRoll4Asm

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddNAdxRolledFrontEmit
