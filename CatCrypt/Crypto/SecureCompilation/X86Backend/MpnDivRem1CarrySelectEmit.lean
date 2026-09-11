/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan

/-!
# `mpn_divrem_1` as a carry-selected runtime-trip loop

`MpnDivRem1FrontEmit` sources `mpn_divrem_1(qp, up, n, d, dinv)` through
`TranslateDialectRuntimeLoop.rolledForLoopNRt`, whose body front is
`translateDialectControl`. That front has no carry-flag surface, so each of the
body's three comparison bits is synthesised branch-free by a `bSltu` window.

This module re-sources the SAME loop body
(`MpnDivRem1FrontEmit.divLimbBodyLowCT`) through the rolled-loop dispatcher
`FrontRoutePlan.compileLoop` at a runtime trip count and the `carrySelect` body
front, which is `CarryChainSelect.translateDialectCarrySelect`. The selector
recognises the
reciprocal step's `qla := ql + u0; ltu c0 qla ql` window as an `addStart` step
and emits a `bvAddCarryLo`/`bvAddCarryHi` pair in its place, which the owned
backend renders as `adcx` inside the loop's back-edge. The body's other two
comparison windows are not carry-outs of an adjacent word addition — `ltu c1 qla
r` compares two independently computed words, and `ltu c2 ra d` follows a merge
whose right operand is `msk & d` rather than an atom — so both fall through to
`translateDialectControl` unchanged. The body source, the ABI, the accumulator
threading and the `MULXHI` fusion are unchanged.

The arithmetic contract is `MpnDivRem1FrontEmit`'s: `divFold_val` states the
quotient/remainder invariant over the memref carrier.

## Main results

* `divRem1RtProgCOpt` — the carry-selected runtime-trip `mpn_divrem_1` program.
* `divRem1RtProgC_denote` — its denotation as the `JLoopBodyN` fold of the
  carry-selected front body.
* `divRem1RtLprogCOpt` / `divRem1RtAsmCOpt` — the owned `Lprog` and its AT&T
  text.
* `#guard`s pinning that the physical body carries a real back-edge.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1CarrySelectEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (NR NU AQ AU r64 Gouter vmBody divLimbBodyLowCT divCount divInit divInvs
   divRem1RtProgOpt divRem1RtAsmOpt divRem1RtPhysBodyOpt)

/-- The carry-selected runtime-trip `mpn_divrem_1`: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the output
    array threaded as the loop accumulator and `d`/`dinv`/`n`/`up` as loop
    invariants, with the reciprocal step's carry window rewritten to a
    `bvAddCarryLo`/`bvAddCarryHi` pair. `none` if the carry-selecting front
    declines. -/
def divRem1RtProgCOpt : Option (ComL Gouter AQ) :=
  Dialects.FrontRoutePlan.compileLoop (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.sword 64, .sword 64, .sword 64, .memref NU])
    .carrySelect (.runtime divCount)
    vmBody "qp" divLimbBodyLowCT divInit divInvs

-- The carry-selecting front accepts the body and wraps it in a
-- `ComL.forLoopNRt`.
#guard divRem1RtProgCOpt.isSome

/-- **The carry-selected loop's denotation is the `JLoopBodyN` fold of its front
    body.** Whenever the carry-selecting front compiles `divLimbBodyLowCT` to
    `update`, the program's denotation at any valuation is the `n`-fold of
    `update` over the trip indices, seeded by the `qp` argument and threading
    `d`, `dinv`, `n` and `up`. The instance of `rolledForLoopNRtC_denote` at this
    kernel. -/
theorem divRem1RtProgC_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.sword 64, CryptoTy.sword 64, CryptoTy.sword 64,
         CryptoTy.memref NU]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .memref NR) vmBody "qp" divLimbBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    divRem1RtProgCOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(divCount.lookup V).toNat, update⟩
          (Expr.lookupArgs divInvs V) (divInit.lookup V)) :=
  rolledForLoopNRtC_denote vmBody "qp" divLimbBodyLowCT divCount divInit divInvs
    hupd V

/-! ## The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 5-argument-ABI `Lprog` for the carry-selected
    runtime-trip `mpn_divrem_1` under the C symbol `fname`
    (`RDI = qp`, `RSI = up`, `RDX = n`, `RCX = d`, `R8 = dinv`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FheMontMulEmit.fuseMulHiLprog` in its `saveRdx` looped-body mode. -/
def divRem1RtLprogCOpt (fname : String) : Option Lprog :=
  divRem1RtProgCOpt.map (fun c =>
    FheMontMulEmit.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
        [64, 64, 64, 64, 64])
      (saveRdx := true))

/-- The owned AT&T `.s` text for the carry-selected runtime-trip
    `mpn_divrem_1`. -/
def divRem1RtAsmCOpt (fname : String) : Option String :=
  (divRem1RtLprogCOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 5-argument-ABI physical body of the carry-selected runtime-count
    loop. -/
def divRem1RtPhysBodyCOpt : Option Lcmd :=
  divRem1RtProgCOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
      [64, 64, 64, 64, 64]).lfd_body)

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

-- The physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard (divRem1RtPhysBodyCOpt.map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

-- `qp` (RDI) and `up` (RSI) are the two pointer arguments; `n` (RDX), `d` (RCX)
-- and `dinv` (R8) are scalars, so no access may reload its base from their
-- qsave slots.
#guard (divRem1RtPhysBodyCOpt.map (fun b =>
  !(reloadSlots b).isEmpty
    && (reloadSlots b).all (fun q => q == "qsave.RDI" || q == "qsave.RSI")))
  = some true

-- The carry-selected physical body is strictly shorter than the same body
-- through the plain front: the fused window replaces the branch-free `bSltu`
-- expansion of the reciprocal step's carry.
#guard ((match divRem1RtPhysBodyCOpt, divRem1RtPhysBodyOpt with
  | some bc, some bp => decide (bc.length < bp.length)
  | _, _ => false) : Bool)

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

-- Physical body lengths through the plain and the carry-selecting front.
#eval (divRem1RtPhysBodyOpt.map List.length,
       divRem1RtPhysBodyCOpt.map List.length)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1CarrySelectEmit
