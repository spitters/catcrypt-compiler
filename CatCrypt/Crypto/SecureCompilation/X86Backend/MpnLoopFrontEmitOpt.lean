/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate

@[expose] public section

set_option autoImplicit false

/-!
# Optimized twins of the front-sourced runtime-N mpn loop kernels

`MpnLoopFrontEmit` renders its deployed kernels through the bare
`renderLprogAtt`: every `Lprog → Lprog` pass is opt-in, none is applied, so the
deployed `.s` is the exporter's output verbatim. This module emits an `_opt`
twin for the five GMP seam kernels (`add`/`sub`/`and`/`ior`/`xor`), rendered
after the two segment-confined passes:

* `LcmdReloadElim.reloadElimLprog` — deletes the reload of an adjacent
  store/reload spill pair (`dropReloadsLcmd_lsem` is the `lsemStraight` tie up
  to `ArchAgree`; pairing is adjacency-based, so a deleted reload sits in the
  same straight-line segment as its store, and a jump target is preceded by an
  `Llabel`, never by a spill store).
* `LcmdCopyPropagate.copyPropagateLprog` — forwards register/immediate copies
  and drops fully-overwritten moves. Every `Llabel`/`Lcond`/`Lgoto` is a
  barrier: facts are cleared there and the liveness scan treats all registers
  as live across one, so no fact crosses the loop back-edge. The pass carries
  no `lsem` theorem; its flips are gated by the libgmp KAT
  (`bench/integration/Makefile.loop_owned`).

The composition excludes `LprogStoreToLoad.elimReloadsLprog` and
`Optimizer.LoadCSE.loadCSELprog`: their forward-scan environments persist
across control-flow instructions (`writtenNames` is `[]` there), and their
`lsemStraight` statements cover a body only up to its first control-flow
instruction, so on a looped body a binding recorded before the loop label and
invalidated by an in-loop write after the use position escapes both the
theorem and the kill scan. It also excludes `LprogScheduler.scheduleLprog`:
that pass is stated for the pre-RA virtual body, and the post-RA physical
bodies here chain through reused scratch registers, leaving no independent
adjacent `Lopn` pairs to transpose.

The unoptimized deployed symbols stay `MpnLoopFrontEmit.emitMain`'s outputs
and are the baseline twin; the `_opt` kernels carry distinct symbol names
(`mpn_*_loop_owned_opt`) so both link into one KAT/bench binary. Byte-level
conformance for both tiers is the external libgmp KAT
(`bench/integration/mpn_loop_owned_kat.c`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmitOpt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.Jasmin.LowCT (SExpr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
  (addRtProgOpt subRtProgOpt mpnSeedImm gmpAbiArgs binLprog)

/-- The segment-confined `Lprog` pass composition for the looped mpn kernels:
    adjacent spill-pair deletion, then copy propagation with dead-move
    elimination. -/
def mpnLoopOptLprog (p : Lprog) : Lprog :=
  LcmdCopyPropagate.copyPropagateLprog (LcmdReloadElim.reloadElimLprog p)

/-! ## 1. The five `_opt` seam kernels

`add`/`sub` are the scalar-accumulator carry family re-exported under the
`_opt` symbol from the same front programs as the deployed kernels
(`addRtProgOpt`/`subRtProgOpt`); `and`/`ior`/`xor` are the array-accumulator
`binLprog` family at the `_opt` name. Each `Lprog` then runs through
`mpnLoopOptLprog` before rendering. -/

/-- `mpn_add_n_loop_owned_opt`: the front add loop under the `_opt` symbol,
    carry seeded `MOV acc, #0`, carry-out in `RAX`, optimized render. -/
def addLprogOpt : Option Lprog :=
  (addRtProgOpt ()).map (fun c =>
    mpnLoopOptLprog (ComL.toLprogPhysAbiScalarAcc c "mpn_add_n_loop_owned_opt"
      (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64]))

/-- `mpn_sub_n_loop_owned_opt`: the front sub loop under the `_opt` symbol,
    borrow seeded `MOV acc, #0`, borrow-out in `RAX`, optimized render. -/
def subLprogOpt : Option Lprog :=
  (subRtProgOpt ()).map (fun c =>
    mpnLoopOptLprog (ComL.toLprogPhysAbiScalarAcc c "mpn_sub_n_loop_owned_opt"
      (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64]))

/-- `mpn_and_n_loop_owned_opt`. -/
def andLprogOpt : Option Lprog :=
  (binLprog "mpn_and_n_loop_owned_opt" .SAnd).map mpnLoopOptLprog

/-- `mpn_ior_n_loop_owned_opt` (`a OR b = (a XOR b) XOR (a AND b)`, as in the
    deployed kernel — the `SExpr` alphabet has no `SOr`). -/
def iorLprogOpt : Option Lprog :=
  (binLprog "mpn_ior_n_loop_owned_opt"
    (fun x y => .SXor (.SXor x y) (.SAnd x y))).map mpnLoopOptLprog

/-- `mpn_xor_n_loop_owned_opt`. -/
def xorLprogOpt : Option Lprog :=
  (binLprog "mpn_xor_n_loop_owned_opt" .SXor).map mpnLoopOptLprog

/-! ## 2. Front-acceptance gates

Each `_opt` kernel compiles iff its deployed twin does: the symbol name enters
only the total export/optimize maps, so `Option.isSome` transfers from the
`MpnLoopFrontEmit` gates with no re-evaluation of the front. -/

theorem addLprogOpt_isSome : addLprogOpt.isSome := by
  have h := MpnLoopFrontEmit.addLprogFront_isSome
  unfold MpnLoopFrontEmit.addLprogFront at h
  rw [Option.isSome_map] at h
  unfold addLprogOpt
  rw [Option.isSome_map]
  exact h

theorem subLprogOpt_isSome : subLprogOpt.isSome := by
  have h := MpnLoopFrontEmit.subLprogFront_isSome
  unfold MpnLoopFrontEmit.subLprogFront at h
  rw [Option.isSome_map] at h
  unfold subLprogOpt
  rw [Option.isSome_map]
  exact h

theorem andLprogOpt_isSome : andLprogOpt.isSome := by
  have h := MpnLoopFrontEmit.andLprog_isSome
  unfold MpnLoopFrontEmit.andLprog MpnLoopFrontEmit.binLprog
    rolledForLoopNRtLprog at h
  rw [Option.isSome_map] at h
  unfold andLprogOpt MpnLoopFrontEmit.binLprog rolledForLoopNRtLprog
  rw [Option.isSome_map, Option.isSome_map]
  exact h

theorem iorLprogOpt_isSome : iorLprogOpt.isSome := by
  have h := MpnLoopFrontEmit.iorLprog_isSome
  unfold MpnLoopFrontEmit.iorLprog MpnLoopFrontEmit.binLprog
    rolledForLoopNRtLprog at h
  rw [Option.isSome_map] at h
  unfold iorLprogOpt MpnLoopFrontEmit.binLprog rolledForLoopNRtLprog
  rw [Option.isSome_map, Option.isSome_map]
  exact h

theorem xorLprogOpt_isSome : xorLprogOpt.isSome := by
  have h := MpnLoopFrontEmit.xorLprog_isSome
  unfold MpnLoopFrontEmit.xorLprog MpnLoopFrontEmit.binLprog
    rolledForLoopNRtLprog at h
  rw [Option.isSome_map] at h
  unfold xorLprogOpt MpnLoopFrontEmit.binLprog rolledForLoopNRtLprog
  rw [Option.isSome_map, Option.isSome_map]
  exact h

/-! ## 3. Rendered text and shape pins -/

def addAsmOpt : String := (addLprogOpt.map renderLprogAtt).getD ""
def subAsmOpt : String := (subLprogOpt.map renderLprogAtt).getD ""
def andAsmOpt : String := (andLprogOpt.map renderLprogAtt).getD ""
def iorAsmOpt : String := (iorLprogOpt.map renderLprogAtt).getD ""
def xorAsmOpt : String := (xorLprogOpt.map renderLprogAtt).getD ""

/-- The deployed unoptimized renders, for the size comparison pins. -/
def addAsmBase : String := ((MpnLoopFrontEmit.addLprogFront ()).map renderLprogAtt).getD ""
def subAsmBase : String := ((MpnLoopFrontEmit.subLprogFront ()).map renderLprogAtt).getD ""
def andAsmBase : String := ((MpnLoopFrontEmit.andLprog ()).map renderLprogAtt).getD ""
def iorAsmBase : String := ((MpnLoopFrontEmit.iorLprog ()).map renderLprogAtt).getD ""
def xorAsmBase : String := ((MpnLoopFrontEmit.xorLprog ()).map renderLprogAtt).getD ""

/-- Rendered line count. -/
def lineCount (s : String) : Nat := (s.splitOn "\n").length

/- Each `_opt` kernel reaches its own symbol, keeps the runtime-N guarded-loop
   back-edge, and renders every op (no `UNHANDLED` sentinel). -/
#guard strContains addAsmOpt "mpn_add_n_loop_owned_opt"
    && strContains addAsmOpt "jne .L"
    && strContains addAsmOpt "cmpq $0,"
    && !(strContains addAsmOpt "UNHANDLED")
#guard strContains subAsmOpt "mpn_sub_n_loop_owned_opt"
    && strContains subAsmOpt "jne .L"
    && !(strContains subAsmOpt "UNHANDLED")
#guard strContains andAsmOpt "mpn_and_n_loop_owned_opt"
    && strContains andAsmOpt "andq"
    && strContains andAsmOpt "jne .L"
    && !(strContains andAsmOpt "UNHANDLED")
#guard strContains iorAsmOpt "mpn_ior_n_loop_owned_opt"
    && strContains iorAsmOpt "jne .L"
    && !(strContains iorAsmOpt "UNHANDLED")
#guard strContains xorAsmOpt "mpn_xor_n_loop_owned_opt"
    && strContains xorAsmOpt "xorq"
    && strContains xorAsmOpt "jne .L"
    && !(strContains xorAsmOpt "UNHANDLED")

/- The optimized render of each seam kernel is strictly shorter than the
   deployed unoptimized render (the two symbols differ only in name, which
   does not change the line count). -/
#guard lineCount addAsmOpt < lineCount addAsmBase
#guard lineCount subAsmOpt < lineCount subAsmBase
#guard lineCount andAsmOpt < lineCount andAsmBase
#guard lineCount iorAsmOpt < lineCount iorAsmBase
#guard lineCount xorAsmOpt < lineCount xorAsmBase

/-! ## 4. Emit driver -/

/-- Write the five `_opt` seam kernels to `bench/integration/gen_com/` (run
    from the repo root). The unoptimized deployed symbols remain
    `MpnLoopFrontEmit.emitMain` / `MpnLoopEmit.emitMain` outputs; these are
    their renamed optimized twins, KAT'd alongside them by
    `bench/integration/Makefile.loop_owned`. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/integration/gen_com"
  let wr (p : String) (o : Option Lprog) : IO Unit := do
    match o with
    | some lp => IO.FS.writeFile p (renderLprogAtt lp)
    | none => throw (IO.userError s!"front-compile failed for {p}")
  wr "bench/integration/gen_com/mpn_add_n_loop_owned_opt.s" addLprogOpt
  wr "bench/integration/gen_com/mpn_sub_n_loop_owned_opt.s" subLprogOpt
  wr "bench/integration/gen_com/mpn_and_n_loop_owned_opt.s" andLprogOpt
  wr "bench/integration/gen_com/mpn_ior_n_loop_owned_opt.s" iorLprogOpt
  wr "bench/integration/gen_com/mpn_xor_n_loop_owned_opt.s" xorLprogOpt
  IO.println "wrote 5 optimized-twin mpn seam kernels (reloadElim + copyPropagate)"

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmitOpt
