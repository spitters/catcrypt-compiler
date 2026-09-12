/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# `mpn_mul_1` as a carry-selected runtime-trip loop

`MpnMul1FrontEmit` sources `mpn_mul_1(rp, up, n, v)` through
`TranslateDialectRuntimeLoop.rolledForLoopNRt`, whose body front is
`translateDialectControl`. That front has no carry-flag surface, so the per-limb
carry-out is synthesised branch-free by the three-command `bSltu` window and the
rendered text carries no `adcx`.

This module re-sources the SAME loop body (`MpnMul1FrontEmit.limbBodyLowCT`,
`MpnMul1FrontEmit.vmBody`) through the rolled-loop dispatcher
`FrontRoutePlan.compileLoop` at a runtime trip count and the `carrySelect` body
front, which is `CarryChainSelect.translateDialectCarrySelect`. That is the route
`FrontRoutePlanKernels` pins for this body. The selector recognises the
body's `s := lo + cy; ltu c s lo` window as an `addStart` step and emits
`bvAddCarryLo`/`bvAddCarryHi` in its place, which the owned backend renders as
`adcx` inside the loop's back-edge. Nothing about the body source, the ABI, the
accumulator threading or the `MULXHI` fusion changes.

The arithmetic contract is `MpnMul1FrontEmit`'s: `mul1Fold_val` /
`mul1Fold_val_zero` state the carry-chain invariant over the memref carrier for
every `NR` / `NU`, and `mul1RtProgC_denote` below is the denotation of this
program as the `JLoopBodyN.denote` fold of the carry-selected body.

## Main results

* `mul1RtProgCOpt` — the carry-selected runtime-trip `mpn_mul_1` program.
* `mul1RtProgC_denote` — its denotation as the `JLoopBodyN` fold of the
  carry-selected front body.
* `mul1RtLprogCOpt` / `mul1RtAsmCOpt` — the owned `Lprog` and its AT&T text.
* `#guard`s pinning that the physical body carries a real back-edge.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1CarrySelectEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (NR NU AR AU r64 Gouter limbBodyLowCT vmBody mul1Count mul1Init mul1Invs)

/-- The carry-selected runtime-trip `mpn_mul_1`: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the output
    array threaded as the loop accumulator and `v`/`up` as loop invariants, with
    the per-limb carry window rewritten to a `bvAddCarryLo`/`bvAddCarryHi` pair.
    `none` if the carry-selecting front declines. -/
def mul1RtProgCOpt : Option (ComL Gouter AR) :=
  Dialects.FrontRoutePlan.compileLoop (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.sword 64, .memref NU])
    .carrySelect (.runtime mul1Count)
    vmBody "rp" limbBodyLowCT mul1Init mul1Invs

-- The carry-selecting front accepts the body and wraps it in a `ComL.forLoopNRt`.
#guard mul1RtProgCOpt.isSome

/-- **The carry-selected loop's denotation is the `JLoopBodyN` fold of its front
    body.** Whenever the carry-selecting front compiles `limbBodyLowCT` to
    `update`, the program's denotation at any valuation is the `n`-fold of
    `update` over the trip indices, seeded by the `rp` argument and threading `v`
    and `up`. The instance of `rolledForLoopNRtC_denote` at this kernel. -/
theorem mul1RtProgC_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.sword 64, CryptoTy.memref NU]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .memref NR) vmBody "rp" limbBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    mul1RtProgCOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(mul1Count.lookup V).toNat, update⟩
          (Expr.lookupArgs mul1Invs V) (mul1Init.lookup V)) :=
  rolledForLoopNRtC_denote vmBody "rp" limbBodyLowCT mul1Count mul1Init mul1Invs
    hupd V

/-- The rolled, owned-RA 4-argument-ABI `Lprog` for the carry-selected
    runtime-trip `mpn_mul_1` under the C symbol `fname`
    (`RDI = rp`, `RSI = up`, `RDX = n`, `RCX = v`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FheMontMulEmit.fuseMulHiLprog` in its `saveRdx` looped-body mode. -/
def mul1RtLprogCOpt (fname : String) : Option Lprog :=
  mul1RtProgCOpt.map (fun c =>
    FheMontMulEmit.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64])
      (saveRdx := true))

/-- The owned AT&T `.s` text for the carry-selected runtime-trip `mpn_mul_1`. -/
def mul1RtAsmCOpt (fname : String) : Option String :=
  (mul1RtLprogCOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 4-argument-ABI physical body of the carry-selected runtime-count loop. -/
def mul1RtPhysBodyCOpt : Option Lcmd :=
  mul1RtProgCOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

-- The physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard (mul1RtPhysBodyCOpt.map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

/-- The red-zone qsave slot each streaming memref access reloads its SIB base
    from, in body order. -/
def mul1RtReloadsC : List String :=
  match mul1RtPhysBodyCOpt with
  | none => []
  | some body =>
      (body.zip (body.drop 1)).filterMap (fun (prev, cur) =>
        match cur.li_i, prev.li_i with
        | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
            some q
        | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
            some q
        | _, _ => none)

-- `rp` (RDI) and `up` (RSI) are the two pointer arguments; `n` (RDX) and `v`
-- (RCX) are scalars, so no access may reload its base from their qsave slots.
#guard mul1RtReloadsC.contains "qsave.RSI"
#guard mul1RtReloadsC.all (fun q => q == "qsave.RDI" || q == "qsave.RSI")

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

-- The physical body is 61 instructions: the carry window's ~25-op
-- branch-free expansion collapsed to the `bvAddCarryLo`/`bvAddCarryHi` pair.
-- Measured 61 under Lean 4.32, one more than the 60 pinned on 4.30.
#guard (mul1RtPhysBodyCOpt.map (fun body => decide (body.length ≤ 61))) = some true

/-! ## Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. It
lands beside `MpnMul1FrontEmit`'s render in the same harness directory, which
benches the two re-sourcings of the same body side by side. -/

/-- Write the owned-backend `.s` for the carry-selected runtime-trip `mpn_mul_1`
    into the `bench/mpn_mul_1_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_mul_1_front_compare/gen_com"
  IO.FS.createDirAll dir
  match mul1RtAsmCOpt "mpn_mul_1_rt_adx" with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_mul_1_rt_adx_owned.s") s
      IO.println "WROTE bench/mpn_mul_1_front_compare/gen_com/mpn_mul_1_rt_adx_owned.s"
  | none => throw (IO.userError "the carry-selecting front declined mpn_mul_1")

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1CarrySelectEmit
