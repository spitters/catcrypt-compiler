/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMemLogic
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMemLogic
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

@[expose] public section

set_option autoImplicit false

/-!
# The binary logical loop nodes from the System V entry

`DecodeGenNode.decNodeAbi_result` states, for a node that passes `nodeCheck`, that the
decoded bytes halt in a state whose result read-back is the flag machine's output array.
This module instantiates it at the physical bodies of `mpn_and_n`, `mpn_xor_n` and
`mpn_ior_n` on eight-word arrays. The decoded node comes from
`DecodeGen.decodeLprog_node_gen` and the node from `DecodeGenNode.nodeCheck`; every
hypothesis is a Boolean check closed by kernel evaluation.

## The layout

`logicAbi` passes the output `rp` in `%rdi`, the sources `ap` in `%rsi` and `bp` in `%rdx`,
eight words each, and the count in `%rcx`, bounded by `8`. The result is the eight words at
the entry value of `%rdi`. The body uses the stack words from `-80` to `-8` below the entry
stack pointer.

## Main results

* `logicNode_eq`: the renamed export node of a logical loop is the renamed seeds followed by
  the guarded loop over its renamed looped segment.
* `logic_result`: `decNodeAbi_result` at the output array `a0` of `logicAbi`.
* `and_result`, `xor_result`, `ior_result`: the function bytes of the physical body decode to
  a program that, from a System V entry state satisfying `logicAbi.Regions` and the entry
  correspondence, halts in a state whose result read-back is the flag machine's array `a0`
  after the renamed node.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNodeLogic

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMemLogic
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)

/-! ## 1. The layout and the flag-machine node -/

/-- The System V layout of the logical loops on eight-word arrays. -/
def logicAbi : AbiLayout where
  args := [⟨"rp", "%rdi", .words 8⟩, ⟨"ap", "%rsi", .words 8⟩, ⟨"bp", "%rdx", .words 8⟩,
    ⟨"n", "%rcx", .scalar⟩]
  consts := []
  result := .words "%rdi" 8
  bounds := [("%rcx", 8)]
  frameLo := -80
  frameHi := -8

/-- The seeds of the logical nodes, renamed: the accumulator touch on `a0`, the index at `0`
    and the counter from `a3`. -/
def logicSeeds (k : Nat) : List LinstrRM :=
  (loopSeedsRM 4 (regName 4) (.reg (argName 0)) (.reg (argName 3))).map (renRM (logicRho k))

/-- The renamed export node of a logical loop is its renamed seeds followed by the guarded
    loop over its renamed looped segment. -/
theorem logicNode_eq (k : Nat) {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr 64 8 :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr 64 8))
    (invOps : List LOperand) (hctr : logicRho k (loopCtr 4) = loopCtr 4) :
    (forLoopLcmdNRtRM 4 (regName 4) (.reg (argName 0)) (.reg (argName 3)) update invOps
        (fun _ => none)).map (renRM (logicRho k))
      = logicSeeds k ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) (loopCtr 4)
          ((forLoopBodyNRtRM 4 (regName 4) update invOps (fun _ => none)).map
            (renRM (logicRho k))) := by
  unfold forLoopLcmdNRtRM
  rw [List.map_append, JasminLsemExportCanon.guardedFlagLoopLinstrRM_map_renRM, hctr]
  rfl

deriving instance DecidableEq for Shape
deriving instance DecidableEq for DShape

/-! ## 2. The decoded node of a physical body -/

/-- The decoded prologue of a logical body: the frame `lea` and the first seventeen items. -/
def logicPre (body : Lcmd) : List (JInstr 64) :=
  leaFrame (-(Int.ofNat (Params.ofBody body).frame)) :: opsD (Params.ofBody body) (body.take 17)

/-- The decoded loop of a logical body with `n` loop items, on the counter `%rdi`. -/
def logicLoopD (body : Lcmd) (n : Nat) : LprogControlFlow.XLoop 64 :=
  ⟨4, "%rdi", opsD (Params.ofBody body) ((body.drop 20).take n)⟩

/-- The decoded epilogue of a logical body with `n` loop items: six restores and the frame
    `lea`. -/
def logicPost (body : Lcmd) (n : Nat) : List (JInstr 64) :=
  opsD (Params.ofBody body) ((body.drop (23 + n)).take 6)
    ++ [leaFrame (Int.ofNat (Params.ofBody body).frame)]

/-- The guard and back-edge compare of the logical bodies. -/
def logicCmp : Linstr := ⟨0, .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0]⟩

/-- **A logical node realises the result read-back.** For a physical body whose bytes decode
    to its node layout and whose node passes `nodeCheck` against `logicAbi`, the instance of
    `decNodeAbi_result` at the output array `a0`. -/
theorem logic_result (body : Lcmd) (n : Nat) (E : MemEnv) (seeds flagBody : List LinstrRM)
    (hdec : decodeLprog (encodeLfundefBytes body)
      = some (nodeLayout (logicPre body) (logicLoopD body n) (logicPost body n)))
    (hchk : nodeCheck logicAbi E seeds flagBody 4 (4 + 0x40000000) "Lctr4" "%rax" logicLive
      (logicPre body) (logicPost body n) (logicLoopD body n) = true)
    (hrs : E.rs = logicRegions)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hreg : logicAbi.Regions sa) (hent : NodeEntry (abiReg logicAbi) logicRegions sa b) :
    ∃ prog sa' t k, decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn
          (seeds ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" flagBody)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∃ arr : Fin 8 → BitVec 64, t.prog.base.getArr "a0" 64 8 = some arr
          ∧ logicAbi.ResultOf sa sa' (.array ((List.range 8).map
              fun j => .int (stackGet arr j).toNat)) := by
  have h8 : regLen E.rs "a0" = 8 := by rw [hrs]; decide +kernel
  have := decNodeAbi_result logicAbi E fn _ _ _ _ _ _ _ _ _ _ _ hdec hchk "a0" "%rdi"
    (by decide +kernel) (by rw [h8]; rfl) (by rw [h8]; decide) sa b zf hpc hreg (hrs ▸ hent)
  rw [h8] at this
  exact this

/-! ## 3. The `and`, `xor` and `ior` nodes -/

/-- The physical body of `mpn_and_n`. -/
def andBody : Lcmd := binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64"

/-- The physical body of `mpn_xor_n`. -/
def xorBody : Lcmd := binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64"

/-- The physical body of `mpn_ior_n`. -/
def iorBody : Lcmd := binLoopBody (iorMid "SHL:0:64") "SHL:0:64"

theorem and_decode : decodeLprog (encodeLfundefBytes andBody)
    = some (nodeLayout (logicPre andBody) (logicLoopD andBody 15) (logicPost andBody 15)) :=
  decodeLprog_node_gen andBody (andBody.take 17) ((andBody.drop 20).take 15)
    ((andBody.drop 38).take 6) logicCmp ⟨0, .Lcond (.reg "Z") 1073741828⟩
    ⟨0, .Llabel .internal 4⟩ logicCmp ⟨0, .Lcond (.reg "NZ") 4⟩
    ⟨0, .Llabel .internal 1073741828⟩ ⟨0, .Lret⟩ 4 1073741828 "%rdi" .internal .internal
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) rfl rfl
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem xor_decode : decodeLprog (encodeLfundefBytes xorBody)
    = some (nodeLayout (logicPre xorBody) (logicLoopD xorBody 15) (logicPost xorBody 15)) :=
  decodeLprog_node_gen xorBody (xorBody.take 17) ((xorBody.drop 20).take 15)
    ((xorBody.drop 38).take 6) logicCmp ⟨0, .Lcond (.reg "Z") 1073741828⟩
    ⟨0, .Llabel .internal 4⟩ logicCmp ⟨0, .Lcond (.reg "NZ") 4⟩
    ⟨0, .Llabel .internal 1073741828⟩ ⟨0, .Lret⟩ 4 1073741828 "%rdi" .internal .internal
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) rfl rfl
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem ior_decode : decodeLprog (encodeLfundefBytes iorBody)
    = some (nodeLayout (logicPre iorBody) (logicLoopD iorBody 19) (logicPost iorBody 19)) :=
  decodeLprog_node_gen iorBody (iorBody.take 17) ((iorBody.drop 20).take 19)
    ((iorBody.drop 42).take 6) logicCmp ⟨0, .Lcond (.reg "Z") 1073741828⟩
    ⟨0, .Llabel .internal 4⟩ logicCmp ⟨0, .Lcond (.reg "NZ") 4⟩
    ⟨0, .Llabel .internal 1073741828⟩ ⟨0, .Lret⟩ 4 1073741828 "%rdi" .internal .internal
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) rfl rfl
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem and_nodeCheck :
    nodeCheck logicAbi andEnv (logicSeeds 8) (andLoopBody ()) 4 (4 + 0x40000000) "Lctr4" "%rax"
      logicLive (logicPre andBody) (logicPost andBody 15) (logicLoopD andBody 15) = true := by
  decide +kernel

theorem xor_nodeCheck :
    nodeCheck logicAbi andEnv (logicSeeds 8) (xorLoopBody ()) 4 (4 + 0x40000000) "Lctr4" "%rax"
      logicLive (logicPre xorBody) (logicPost xorBody 15) (logicLoopD xorBody 15) = true := by
  decide +kernel

theorem ior_nodeCheck :
    nodeCheck logicAbi iorEnv (logicSeeds 10) (iorLoopBody ()) 4 (4 + 0x40000000) "Lctr4" "%rax"
      logicLive (logicPre iorBody) (logicPost iorBody 19) (logicLoopD iorBody 19) = true := by
  decide +kernel

/-- **The `mpn_and_n` bytes realise the result read-back.** -/
theorem and_result (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hreg : logicAbi.Regions sa) (hent : NodeEntry (abiReg logicAbi) logicRegions sa b) :
    ∃ prog sa' t k, decodeLprog (encodeLfundefBytes andBody) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn
          (logicSeeds 8 ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" (andLoopBody ()))) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∃ arr : Fin 8 → BitVec 64, t.prog.base.getArr "a0" 64 8 = some arr
          ∧ logicAbi.ResultOf sa sa' (.array ((List.range 8).map
              fun j => .int (stackGet arr j).toNat)) :=
  logic_result andBody 15 andEnv _ _ and_decode and_nodeCheck rfl fn sa b zf hpc hreg hent

/-- **The `mpn_xor_n` bytes realise the result read-back.** -/
theorem xor_result (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hreg : logicAbi.Regions sa) (hent : NodeEntry (abiReg logicAbi) logicRegions sa b) :
    ∃ prog sa' t k, decodeLprog (encodeLfundefBytes xorBody) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn
          (logicSeeds 8 ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" (xorLoopBody ()))) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∃ arr : Fin 8 → BitVec 64, t.prog.base.getArr "a0" 64 8 = some arr
          ∧ logicAbi.ResultOf sa sa' (.array ((List.range 8).map
              fun j => .int (stackGet arr j).toNat)) :=
  logic_result xorBody 15 andEnv _ _ xor_decode xor_nodeCheck rfl fn sa b zf hpc hreg hent

/-- **The `mpn_ior_n` bytes realise the result read-back.** -/
theorem ior_result (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hreg : logicAbi.Regions sa) (hent : NodeEntry (abiReg logicAbi) logicRegions sa b) :
    ∃ prog sa' t k, decodeLprog (encodeLfundefBytes iorBody) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn
          (logicSeeds 10 ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" (iorLoopBody ()))) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∃ arr : Fin 8 → BitVec 64, t.prog.base.getArr "a0" 64 8 = some arr
          ∧ logicAbi.ResultOf sa sa' (.array ((List.range 8).map
              fun j => .int (stackGet arr j).toNat)) :=
  logic_result iorBody 19 iorEnv _ _ ior_decode ior_nodeCheck rfl fn sa b zf hpc hreg hent

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNodeLogic
