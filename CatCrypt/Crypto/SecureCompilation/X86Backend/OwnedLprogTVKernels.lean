/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGKernels
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizeBasicBlocksCT
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGKernels
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizeBasicBlocksCT

/-!
# The value translation validation on shipped kernel bodies

`OwnedLprogTV.ownedCheckTy` on a program and the output of `LprogOptPipeline.ownedLprog`.

The optimisation of `OptimizeBasicBlocksCT.cpSubBody` has the same value at every name
under the three-address reading of `lsemFuelMemF` (`ownedCheckM` accepts it), and violates
the printer's two-address precondition, so `ownedCheckTy` rejects it; its legalisation
`TwoAddrLegalize.twoAddrBody` and the whole `ownedLprog` output are accepted, and a body
with the sources of the subtraction exchanged is rejected.

On the kernels, `ownedResult` is the result of the check, the number of source blocks whose
instructions before the terminator fail from every state, and the number of blocks. A block
that always fails is accepted without a comparison, since no halting run passes through it.
With the wire typing `tyWire`, no block of the five `mpn_*_loop_owned` loops fails and all
are accepted: `lsemFuelMemF` steps their array-ABI moves `MOVQ` (`qsave.<R>`) and
`LOAD:64`/`STORE:64` (`mem.<B>.<off>`) as register copies (`JasminLsemMemFlagGuard.copyQ`).
The one block of the X25519 ladder step fails at its first `ADC:64`, and the entry and loop
blocks of the rolled Keccak-f1600 at `LOADSYM` and `ROR:63:64`; `lsemFuelMemF` steps none
of these.

## Main definitions

* `tagOf`, `tyWire`: typings of a body.
* `blockFails`, `ownedResult`: the check on a program and its owned output, with the blocks
  that fail from every state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVKernels

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (cfgOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (ownedLprog optimizeBasicBlocks)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizeBasicBlocksCT (cpSubBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (twoAddrBody)

/-- The memory tag of an instruction: a runtime-indexed load or store at the shape
    `(64, 4)`, every other instruction at the register tag. -/
def tagOf : LinstrR → MemTag
  | .Lopn _ "LOADIDX" _ => .load 64 4
  | .Lopn _ "STOREIDX" _ => .store 64 4
  | _ => .reg none

/-- A body typed by `tagOf`, without its trailing `Lret`. -/
def tyWire (c : Lcmd) : List LinstrRM := dropRet (typeBody tagOf c)

/-- The registers `cpSubBody` writes. -/
def cpOuts : List String := ["RAX", "RCX", "RDX", "R8"]

/-- The program with the one function `cp` of body `body` and results `cpOuts`. -/
def progOf (body : Lcmd) : Lprog :=
  { lp_funcs := [("cp", { lfd_body := body, lfd_res := cpOuts })] }

/-- `cpSubBody` with the sources of its subtraction exchanged. -/
def cpSwapped : Lcmd :=
  [ ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "SUB:64" [.reg "RCX", .reg "RBX"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "ADD:64" [.reg "RAX", .reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "T" "RDX" 8]⟩ ]

/-- For each block of a typed body, whether its instructions before the terminator fail
    from every state. -/
def blockFails (B : List LinstrRM) : List Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G => (List.range G.blocks.size).map fun k =>
      match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
      | .fail => true
      | _ => false
  | none => []

/-- The result of `ownedCheckTy ty` on a program and its `ownedLprog` output, with the
    number of source blocks that fail from every state and the number of blocks. -/
def ownedResult (ty : Lcmd → List LinstrRM) (p : Option Lprog) : Option (Bool × Nat × Nat) :=
  p.map fun P =>
    let B := (P.lp_funcs.head?.map (fun f => ty f.2.lfd_body)).getD []
    (ownedCheckTy ty P (ownedLprog P), ((blockFails B).filter id).length, (blockFails B).length)

/-- The rolled Keccak-f1600 program before `ownedLprog`. -/
def keccakRolledPre : Option Lprog :=
  match CatCrypt.Crypto.Jasmin.KeccakJincImport.keccakF1600Rolled with
  | .ok r => CatCrypt.Crypto.Jasmin.JincElab.rolledLprog r.fn r.tables
      CatCrypt.Crypto.Jasmin.KeccakJincImport.keccakF1600Sym
  | .error _ => none

/-! ## The two-address counterexample -/

#kat ownedCheckM cpOuts (tyWire cpSubBody) (tyWire (optimizeBasicBlocks cpSubBody))
#kat ownedCheckTy tyWire (progOf cpSubBody) (progOf (optimizeBasicBlocks cpSubBody)) == false
#kat ownedCheckTy tyWire (progOf cpSubBody) (progOf (twoAddrBody (optimizeBasicBlocks cpSubBody)))
#kat ownedCheckTy tyWire (progOf cpSubBody) (ownedLprog (progOf cpSubBody))
#kat ownedCheckM cpOuts (tyWire cpSubBody) (tyWire cpSwapped) == false

/-! ## Kernels, wire typing -/

#kat ownedResult tyWire MpnLoopFrontEmit.andLprog == some (true, 0, 3)
#kat ownedResult tyWire MpnLoopFrontEmit.iorLprog == some (true, 0, 3)
#kat ownedResult tyWire MpnLoopFrontEmit.xorLprog == some (true, 0, 3)
#kat ownedResult tyWire MpnLoopFrontEmit.addLprogFront == some (true, 0, 3)
#kat ownedResult tyWire MpnLoopFrontEmit.subLprogFront == some (true, 0, 3)
set_option kat.ms 800 in
#kat ownedResult tyWire (some Fe25519LfundefBridge.monoStepLprog) == some (true, 1, 1)
set_option kat.ms 2500 in
#kat ownedResult tyWire keccakRolledPre == some (true, 2, 3)

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVKernels
