/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# `mpn_mul_basecase` as a carry-selected nested runtime-trip loop

`MpnMulBasecaseFrontEmit` sources `mpn_mul_basecase(rp, up, vp, un, vn)` through
`TranslateDialectRuntimeLoop.rolledForLoopNRtNested`, whose body front is
`translateDialectControl`. That front has no carry-flag surface, so each of the
inner body's three comparison bits is synthesised branch-free by a `bSltu`
window.

This module re-sources the SAME bodies
(`MpnMulBasecaseFrontEmit.cntBodyLowCT` / `.rowBodyLowCT`) through
`TranslateDialectRuntimeLoopCarrySelect.rolledForLoopNRtNestedC`, whose body
front is `CarryChainSelect.translateDialectCarrySelect`. The selector recognises
the two carry windows of the multiply-accumulate step — `s1 := lo + cy; ltu k1 s1
lo` and `s2 := s1 + rr; ltu k2 s2 s1` — as `addStart` steps and emits
`bvAddCarryLo`/`bvAddCarryHi` pairs in their place, which the owned backend
renders as `adcx` inside the inner back-edge. The flush-trip mask's `ltu kb t un`
is a standalone comparison, not the carry-out of an adjacent word addition, so it
falls through to `translateDialectControl` unchanged. The body source, the ABI,
the accumulator threading and the `MULXHI` fusion are unchanged.

The arithmetic contract is `MpnMulBasecaseFrontEmit`'s: `bcFold_val` states the
schoolbook product invariant over the memref carrier, and `bcFold_val_sqr` its
squaring specialisation.

## Main results

* `bcProgCOpt` — the carry-selected nested runtime-trip `mpn_mul_basecase`
  program.
* `bcProgC_denote` — its denotation as the `JLoopBodyN.nestedDenote` double fold
  of the carry-selected front bodies.
* `bcRtLprogCOpt` / `bcRtAsmCOpt` — the owned `Lprog` and its AT&T text.
* `#guard`s pinning that the physical body carries both back-edges.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseCarrySelectEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
  (NR NU NV AR AU AV r64 Gouter Ginv vmCount vmBody cntBodyLowCT rowBodyLowCT
   bcOuterCount bcInit bcInvs bcProgOpt bcRtAsmOpt bcRtPhysBodyOpt)

/-- The carry-selected nested runtime-trip `mpn_mul_basecase`: one inner body
    copy behind two `jne` back-edges, the outer trip counter seeded from the
    runtime `vn` register, the inner trip recomputed as `un + 1` each outer pass,
    the output array threaded as the loop accumulator and `up`/`vp`/`un`/`vn` as
    loop invariants, with both per-position carry windows rewritten to
    `bvAddCarryLo`/`bvAddCarryHi` pairs. `none` if either carry-selecting front
    declines. -/
def bcProgCOpt : Option (ComL Gouter AR) :=
  rolledForLoopNRtNestedC (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := Ginv)
    vmCount "cnt" cntBodyLowCT
    vmBody "rp" rowBodyLowCT
    bcOuterCount bcInit bcInvs

-- The carry-selecting front accepts both bodies and wraps them in a
-- `ComL.forLoopNRtNested`.
#guard bcProgCOpt.isSome

-- The spine is the nested runtime-loop node, not an unrolled inner sweep.
#guard (bcProgCOpt.map (fun c => match c with
  | .forLoopNRtNested _ _ _ _ _ _ => true
  | _ => false)) = some true

/-- **The carry-selected nest's denotation is the `JLoopBodyN.nestedDenote`
    double fold of its front bodies.** Whenever the carry-selecting front
    compiles `cntBodyLowCT` to `innerCount` and `rowBodyLowCT` to `innerUpdate`,
    the program's denotation at any valuation is the outer fold over `vn` rows of
    the inner fold over the recomputed trip count, seeded by the `rp` argument
    and threading the invariants. The instance of
    `rolledForLoopNRtNestedC_denote` at this kernel. -/
theorem bcProgC_denote
    {innerCount : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.sword 64))}
    {innerUpdate : Com jasminDialect
      (CryptoToJasminCom.mapCtx
        (CryptoTy.memref NR :: .sword 64 :: .sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hcnt : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .sword 64) (Γbody := .sword 64 :: Ginv)
      vmCount "cnt" cntBodyLowCT = some innerCount)
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJC
      (accCTy := .memref NR)
      (Γbody := CryptoTy.memref NR :: .sword 64 :: .sword 64 :: Ginv)
      vmBody "rp" rowBodyLowCT = some innerUpdate)
    (V : Ctxt.Valuation Gouter) :
    bcProgCOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate
          (bcOuterCount.lookup V).toNat (Expr.lookupArgs bcInvs V)
          (bcInit.lookup V)) :=
  rolledForLoopNRtNestedC_denote vmCount "cnt" cntBodyLowCT vmBody "rp" rowBodyLowCT
    bcOuterCount bcInit bcInvs hcnt hupd V

/-! ## The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 5-argument-ABI `Lprog` for the carry-selected
    runtime-trip `mpn_mul_basecase` under the C symbol `fname`
    (`RDI = rp`, `RSI = up`, `RDX = vp`, `RCX = un`, `R8 = vn`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FuseMulHi.fuseMulHiLprog` in its `saveRdx` looped-body mode. -/
def bcRtLprogCOpt (fname : String) : Option Lprog :=
  bcProgCOpt.map (fun c =>
    FuseMulHi.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1, argName 2]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
        [64, 64, 64, 64, 64])
      (saveRdx := true))

/-- The owned AT&T `.s` text for the carry-selected runtime-trip
    `mpn_mul_basecase`. -/
def bcRtAsmCOpt (fname : String) : Option String :=
  (bcRtLprogCOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 5-argument-ABI physical body of the carry-selected nested loop. -/
def bcRtPhysBodyCOpt : Option Lcmd :=
  bcProgCOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1, argName 2]
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

-- The physical body carries two bottom-test back-edges: the outer row loop and
-- the inner limb loop, so the emit is a nest and not an unrolled chain.
#guard (bcRtPhysBodyCOpt.map (fun body =>
  (body.filter (fun i => match i.li_i with
    | .Lcond (.reg "NZ") _ => true | _ => false)).length)) = some 2

-- `rp` (RDI), `up` (RSI) and `vp` (RDX) are the three pointer arguments; `un`
-- (RCX) and `vn` (R8) are scalars, so no access may reload its base from their
-- qsave slots.
#guard (bcRtPhysBodyCOpt.map (fun b =>
  !(reloadSlots b).isEmpty
    && (reloadSlots b).all (fun q =>
        q == "qsave.RDI" || q == "qsave.RSI" || q == "qsave.RDX")))
  = some true

-- The carry-selected physical body is strictly shorter than the same body
-- through the plain front: the two fused windows replace the branch-free
-- `bSltu` expansions of the multiply-accumulate step's carries.
#guard ((match bcRtPhysBodyCOpt, bcRtPhysBodyOpt with
  | some bc, some bp => decide (bc.length < bp.length)
  | _, _ => false) : Bool)

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

-- Physical body lengths through the plain and the carry-selecting front.
#eval (bcRtPhysBodyOpt.map List.length,
       bcRtPhysBodyCOpt.map List.length)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseCarrySelectEmit
