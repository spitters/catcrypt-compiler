/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan

/-!
# `mpn_addmul_1` and `mpn_submul_1` as carry-selected runtime-trip loops

`MpnAddmulSubmul1FrontEmit` sources both kernels through
`TranslateDialectRuntimeLoop.rolledForLoopNRt`, whose body front is
`translateDialectControl`. That front has no carry-flag surface, so each of the
body's two carry bits is synthesised branch-free by a `bSltu` window.

This module re-sources the SAME loop bodies
(`MpnAddmulSubmul1FrontEmit.addmulBodyLowCT` / `.submulBodyLowCT`) through the
rolled-loop dispatcher `FrontRoutePlan.compileLoop` at a runtime trip count and
the `carrySelect` body front, which is
`CarryChainSelect.translateDialectCarrySelect`. The selector recognises the
shared prefix's `s := lo + cy; ltu c s lo` window as an `addStart` step; in
`mpn_addmul_1` it recognises `u := s + o; ltu d u s` as a second `addStart`, and
in `mpn_submul_1` it recognises `u := o - s; ltu d o s` as a `subStart` in the
complement-add convention. Both are emitted as `bvAddCarryLo`/`bvAddCarryHi`
pairs, which the owned backend renders as `adcx` inside the loop's back-edge.
The body source, the ABI, the accumulator threading and the `MULXHI` fusion are
unchanged.

The arithmetic contract is `MpnAddmulSubmul1FrontEmit`'s: `accFold_val` and its
`addmulFold_val` / `submulFold_val` instances state the carry-chain invariant
over the memref carrier for every `NR` / `NU` / carry-cell index.

## Main results

* `addmulRtProgCOpt` / `submulRtProgCOpt` — the carry-selected runtime-trip
  programs.
* `addmulRtProgC_denote` / `submulRtProgC_denote` — each program's denotation as
  the `JLoopBodyN` fold of its carry-selected front body.
* `addmulRtAsmCOpt` / `submulRtAsmCOpt` — the owned AT&T `.s` texts.
* `#guard`s pinning that each rendered text contains `adcx` and `mulx`, carries a
  real back-edge, reloads the `up` base from the `up` argument's save slot, and
  emits no `UNHANDLED` sentinel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1CarrySelectEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (NR NU AR AU r64 Gouter)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
  (addmulBodyLowCT submulBodyLowCT vmBody accCount accInit accInvs rtLprogOpt
   rtPhysBodyOpt addmulRtProgOpt submulRtProgOpt addmulRtAsmOpt submulRtAsmOpt)

/-- The carry-selected runtime-trip `mpn_addmul_1`: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the output
    array threaded as the loop accumulator and `up`/`n`/`v` as loop invariants,
    with both per-limb carry windows rewritten to
    `bvAddCarryLo`/`bvAddCarryHi` pairs. `none` if the carry-selecting front
    declines. -/
def addmulRtProgCOpt : Option (ComL Gouter AR) :=
  Dialects.FrontRoutePlan.compileLoop (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.memref NU, .sword 64, .sword 64])
    .carrySelect (.runtime accCount)
    vmBody "rp" addmulBodyLowCT accInit accInvs

/-- The carry-selected runtime-trip `mpn_submul_1`, in the same shape: the carry
    window is an `addStart` step and the borrow window a `subStart` step in the
    complement-add convention. `none` if the carry-selecting front declines. -/
def submulRtProgCOpt : Option (ComL Gouter AR) :=
  Dialects.FrontRoutePlan.compileLoop (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.memref NU, .sword 64, .sword 64])
    .carrySelect (.runtime accCount)
    vmBody "rp" submulBodyLowCT accInit accInvs

-- The carry-selecting front accepts both bodies and wraps each in a
-- `ComL.forLoopNRt`.
#guard addmulRtProgCOpt.isSome
#guard submulRtProgCOpt.isSome

/-- **The carry-selected `mpn_addmul_1` loop's denotation is the `JLoopBodyN`
    fold of its front body.** Whenever the carry-selecting front compiles
    `addmulBodyLowCT` to `update`, the program's denotation at any valuation is
    the `n`-fold of `update` over the trip indices, seeded by the `rp` argument
    and threading `up`, `n` and `v`. The instance of `rolledForLoopNRtC_denote`
    at this kernel. -/
theorem addmulRtProgC_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.memref NU, CryptoTy.sword 64, CryptoTy.sword 64]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .memref NR) vmBody "rp" addmulBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    addmulRtProgCOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, update⟩
          (Expr.lookupArgs accInvs V) (accInit.lookup V)) :=
  rolledForLoopNRtC_denote vmBody "rp" addmulBodyLowCT accCount accInit accInvs
    hupd V

/-- **The carry-selected `mpn_submul_1` loop's denotation is the `JLoopBodyN`
    fold of its front body.** The instance of `rolledForLoopNRtC_denote` at the
    multiply-subtract kernel. -/
theorem submulRtProgC_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.memref NU, CryptoTy.sword 64, CryptoTy.sword 64]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .memref NR) vmBody "rp" submulBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    submulRtProgCOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, update⟩
          (Expr.lookupArgs accInvs V) (accInit.lookup V)) :=
  rolledForLoopNRtC_denote vmBody "rp" submulBodyLowCT accCount accInit accInvs
    hupd V

/-! ## The owned `Lprog`s and the rendered `.s` -/

/-- The owned AT&T `.s` text for the carry-selected runtime-trip
    `mpn_addmul_1`. -/
def addmulRtAsmCOpt (fname : String) : Option String :=
  (rtLprogOpt addmulRtProgCOpt fname).map renderLprogAtt

/-- The owned AT&T `.s` text for the carry-selected runtime-trip
    `mpn_submul_1`. -/
def submulRtAsmCOpt (fname : String) : Option String :=
  (rtLprogOpt submulRtProgCOpt fname).map renderLprogAtt

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

-- Each physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard ((rtPhysBodyOpt addmulRtProgCOpt).map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true
#guard ((rtPhysBodyOpt submulRtProgCOpt).map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

-- `rp` (RDI) and `up` (RSI) are the two pointer arguments; `n` (RDX) and `v`
-- (RCX) are scalars, so no access may reload its base from their qsave slots.
#guard ((rtPhysBodyOpt addmulRtProgCOpt).map (fun b =>
  (reloadSlots b).contains "qsave.RSI"
    && (reloadSlots b).all (fun q => q == "qsave.RDI" || q == "qsave.RSI")))
  = some true
#guard ((rtPhysBodyOpt submulRtProgCOpt).map (fun b =>
  (reloadSlots b).contains "qsave.RSI"
    && (reloadSlots b).all (fun q => q == "qsave.RDI" || q == "qsave.RSI")))
  = some true

-- Each carry-selected physical body is strictly shorter than the same body
-- through the plain front: the fused windows replace the branch-free `bSltu`
-- expansions.
#guard ((match rtPhysBodyOpt addmulRtProgCOpt, rtPhysBodyOpt addmulRtProgOpt with
  | some bc, some bp => decide (bc.length < bp.length)
  | _, _ => false) : Bool)
#guard ((match rtPhysBodyOpt submulRtProgCOpt, rtPhysBodyOpt submulRtProgOpt with
  | some bc, some bp => decide (bc.length < bp.length)
  | _, _ => false) : Bool)

-- The carry-selected renders carry the hardware carry chain (`adcx`), the
-- widening multiply and the streaming SIB operands, and emit no `UNHANDLED`
-- sentinel; the renders through the plain front carry no `adcx`.
#guard ((addmulRtAsmCOpt "mpn_addmul_1_rt_adx").getD "").length > 0
#guard !(strContains ((addmulRtAsmCOpt "mpn_addmul_1_rt_adx").getD "") "UNHANDLED")
#guard strContains ((addmulRtAsmCOpt "mpn_addmul_1_rt_adx").getD "") "adcx"
#guard strContains ((addmulRtAsmCOpt "mpn_addmul_1_rt_adx").getD "") "mulx"
#guard strContains ((addmulRtAsmCOpt "mpn_addmul_1_rt_adx").getD "") "(%r14,"
#guard !(strContains ((addmulRtAsmOpt "mpn_addmul_1_rt").getD "") "adcx")

#guard ((submulRtAsmCOpt "mpn_submul_1_rt_adx").getD "").length > 0
#guard !(strContains ((submulRtAsmCOpt "mpn_submul_1_rt_adx").getD "") "UNHANDLED")
#guard strContains ((submulRtAsmCOpt "mpn_submul_1_rt_adx").getD "") "adcx"
#guard strContains ((submulRtAsmCOpt "mpn_submul_1_rt_adx").getD "") "mulx"
#guard strContains ((submulRtAsmCOpt "mpn_submul_1_rt_adx").getD "") "(%r14,"
#guard !(strContains ((submulRtAsmOpt "mpn_submul_1_rt").getD "") "adcx")

-- Physical body lengths through the plain and the carry-selecting front, for
-- `mpn_addmul_1` then `mpn_submul_1`.
#eval ((rtPhysBodyOpt addmulRtProgOpt).map List.length,
       (rtPhysBodyOpt addmulRtProgCOpt).map List.length,
       (rtPhysBodyOpt submulRtProgOpt).map List.length,
       (rtPhysBodyOpt submulRtProgCOpt).map List.length)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1CarrySelectEmit
