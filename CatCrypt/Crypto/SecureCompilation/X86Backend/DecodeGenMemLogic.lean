/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer

@[expose] public section

set_option autoImplicit false

/-!
# The binary logical loops through the memory class check

The loop bodies of `mpn_and_n`, `mpn_xor_n` and `mpn_ior_n` on the flag machine are the
looped segments of the export node of the front-compiled limb bodies, with the accumulator
register and the store result sent to the output array `a0` by a node renaming. Their decoded machine loop
bodies load both limbs through pointers reloaded from the frame slots at `48(%rsp)` and
`-8(%rsp)`, index through the copy `%rsi` of the loop index `%rax`, and store through the
pointer reloaded from `56(%rsp)`. This module checks them with `DecodeGenMem.loopOK` and
derives the simulation of the `and` loop body from `DecodeGenMem.decSim_of_loopOK_idx`.

## Main results

* `andLoopBody_eq`: the renamed `and` looped segment is the literal `andLoopBodyLit`.
* `and_loopOK`: the check accepts `andLoopBodyLit` against the decoded loop body
  `AddrMemIdx.andLoop.body`.
* `and_loop_decSim`: the `and` looped segment simulates `andLoop.body` from a loop head
  whose index register `%rax` holds a value below `8`, under `MemSep` of the three regions.
* The `#kat` checks run `loopOK` on the `and`, `xor` and `ior` loop bodies against the loop
  bodies decoded from the function bytes of the exported kernels.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMemLogic

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx (andLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem

/-! ## 1. The flag-machine loop bodies -/

/-- The node renaming of a logical loop whose store result is `L4_r<k>`: the accumulator
    register and the store result to the output array `a0`. -/
def logicRho (k : Nat) (r : String) : String :=
  if r = "r4" ∨ r = "L4_r" ++ toString k then "a0" else r

/-- The looped segment of the `and` node, renamed. -/
def andLoopBody : List LinstrRM :=
  (forLoopBodyNRtRM 4 (regName 4) (andUpdate ()) [.reg (argName 1), .reg (argName 2)]
    (fun _ => none)).map (renRM (logicRho 8))

/-- The looped segment of the `xor` node, renamed. -/
def xorLoopBody : List LinstrRM :=
  (forLoopBodyNRtRM 4 (regName 4) (xorUpdate ()) [.reg (argName 1), .reg (argName 2)]
    (fun _ => none)).map (renRM (logicRho 8))

/-- The looped segment of the `ior` node, renamed. -/
def iorLoopBody : List LinstrRM :=
  (forLoopBodyNRtRM 4 (regName 4) (iorUpdate ()) [.reg (argName 1), .reg (argName 2)]
    (fun _ => none)).map (renRM (logicRho 10))

/-- The renamed `and` looped segment: two loads, the limb operation and its copy, the store
    to `a0`, the accumulator touch, the index and counter updates and the invariant
    touches. -/
def andLoopBodyLit : List LinstrRM :=
  [ (.Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8], .load 64 8)
  , (.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a2" "Lidx4" 8], .load 64 8)
  , binRegI "AND:64" "L4_r6" "L4_r4" "L4_r5"
  , immShiftI "SHL" "L4_r7" "L4_r6" 0
  , (.Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "Lidx4" 8, .reg "L4_r7"], .store 64 8)
  , movRI "a0" "a0"
  , addImmI "Lidx4" "Lidx4" 1
  , subImmI "Lctr4" "Lctr4" 1
  , cmpRI "Lctr4" (.reg "a1")
  , cmpRI "Lctr4" (.reg "a2") ]

theorem andLoopBody_eq : andLoopBody = andLoopBodyLit := by
  decide +kernel

/-! ## 2. Register maps and regions -/

/-- The register map of the `and` and `xor` loops. -/
def andPi (r : String) : String :=
  if r = "a0" then "%rbx" else if r = "a1" then "%rcx" else if r = "a2" then "%rdx"
  else if r = "Lidx4" then "%rax" else if r = "Lctr4" then "%rdi"
  else if r = "L4_r4" then "%rbp" else if r = "L4_r5" then "%r8"
  else if r = "L4_r6" then "%r9" else if r = "L4_r7" then "%rbp" else r

/-- The register map of the `ior` loop. -/
def iorPi (r : String) : String :=
  if r = "a0" then "%rbx" else if r = "a1" then "%rcx" else if r = "a2" then "%rdx"
  else if r = "Lidx4" then "%rax" else if r = "Lctr4" then "%rdi"
  else if r = "L4_r4" then "%rbp" else if r = "L4_r5" then "%r8"
  else if r = "L4_r6" then "%r9" else if r = "L4_r7" then "%r10"
  else if r = "L4_r8" then "%rbp" else if r = "L4_r9" then "%r8" else r

/-- The regions of the logical loops: the output `a0` with its pointer at `56(%rsp)`, the
    sources `a1` at `48(%rsp)` and `a2` at `-8(%rsp)`, eight words each. -/
def logicRegions : List Region := [⟨"a0", 8, 56⟩, ⟨"a1", 8, 48⟩, ⟨"a2", 8, -8⟩]

/-- The check data of the `and` and `xor` loops. -/
def andEnv : MemEnv := ⟨andPi, "%rsp", logicRegions, 8⟩

/-- The check data of the `ior` loop. -/
def iorEnv : MemEnv := ⟨iorPi, "%rsp", logicRegions, 8⟩

/-- The names live at the loop head: the three pointers, the index and the counter. -/
def logicLive : List String := ["a0", "a1", "a2", "Lidx4", "Lctr4"]

/-- The loop body of a decoded program: the machine instructions from the target of the
    first back-edge `jne` up to the compare in front of it. -/
def decLoopBody (prog : List RInstr) : Option (List (JInstr 64)) :=
  let rec go : Nat → List RInstr → Option (Nat × Nat)
    | _, [] => none
    | i, .jcc 5 t :: _ => some (i, t)
    | i, _ :: r => go (i + 1) r
  (go 0 prog).bind fun (i, t) =>
    ((prog.drop t).take (i - t - 1)).mapM fun x =>
      match x with
      | .op j => some j
      | _ => none

/-! ## 3. The `and` loop body -/

theorem and_loopOK : loopOK andEnv logicLive (Abs.idx "%rax") andLoopBodyLit andLoop.body
    = true := by
  decide +kernel

/-- **The `and` loop body through the memory class check.** From a loop head related by
    `MCorr` on the live names, with the loop index register `%rax` below `8`, the renamed
    `and` looped segment simulates the decoded loop body `andLoop.body`, under the
    separation of the three regions. -/
theorem and_loop_decSim {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : MemSep logicRegions base rsp) (zl : Prop) :
    DecSim (fun sa b zf => MCorr andEnv base rsp (logicLive, Abs.empty) zl sa b zf
        ∧ (sa.regs "%rax").toNat < 8)
      (MCorr andEnv base rsp (logicLive, Abs.empty) False) andLoopBody andLoop.body := by
  rw [andLoopBody_eq]
  exact decSim_of_loopOK_idx (E := andEnv) hsep and_loopOK zl

/-! ## 4. Coverage of the check on the decoded kernels -/

set_option kat.ms 1000 in
#kat decLoopBody (binDecoded (andMidDecoded .and_)) == some andLoop.body

#kat ((decodeLprog (encodeLfundefBytes (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64"))).bind
  decLoopBody).any (loopOK andEnv logicLive (Abs.idx "%rax") andLoopBody)

#kat ((decodeLprog (encodeLfundefBytes (binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64"))).bind
  decLoopBody).any (loopOK andEnv logicLive (Abs.idx "%rax") xorLoopBody)

#kat ((decodeLprog (encodeLfundefBytes (binLoopBody (iorMid "SHL:0:64") "SHL:0:64"))).bind
  decLoopBody).any (loopOK iorEnv logicLive (Abs.idx "%rax") iorLoopBody)

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMemLogic
