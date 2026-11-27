/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.List.Sort.Impl
import all Init.Data.Array.Basic
import all Init.Data.String.TakeDrop
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.String
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Basic
import all Init.Data.String.Defs
import all Init.Data.String.ToSlice
import all Init.Data.String.Decode
import all Init.Data.String.Bootstrap
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopBytesEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubBytesCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportScalarAcc
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan

@[expose] public section


set_option autoImplicit false

/-!
# The exporter terms of the linked add and sub kernels, without compiled evaluation

`MpnLoopBytesEmit.kernels` maps `mpn_add_n_loop_owned` and `mpn_sub_n_loop_owned` to
`MpnLoopFrontEmit.addLprogFront ()` and `subLprogFront ()`, the scalar-accumulator exports
(`ComL.toLprogPhysAbiScalarAcc`) of the front-compiled loops. This module computes the object
bytes `MpnLoopBytesEmit.objBytes` of each program with the kernel and rewriting only, and
proves them equal to the linked objects `MpnAddSubShipped.addObj` / `subObj`: the theorems
about those bytes are about the programs the object list maps to the symbols.

## The route (as `MpnBinExportTerm`)

* The front's `Option` is split at `MpnAddSubFrontDenote.addUpdate` / `subUpdate`
  (`addLprogFront_eq`).
* The exporter's only stage the kernel does not evaluate is `canonicalizeMemrefThread` (a
  `Std.HashMap String`); it is computed by rewriting (`addCanon_eq`). The rest of the exporter,
  copied as `scalarAccOfCanon` with the canonicalised body as an input
  (`toLfundefPhysAbiScalarAcc_eq_ofCanon`, by `rfl`), is evaluated by the kernel.

## Main results

* `addObjBytes_eq`, `subObjBytes_eq`: `MpnLoopBytesEmit.objBytes (addLprogFront ()) = some addObj`
  and the same for sub.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubExportTerm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote (addUpdate addUpdate_eq subUpdate subUpdate_eq)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
  (compileLoop compileLoopCont compileLoopCont_ret_here)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes encodeLprogChecked encodeLprog encodableLcmd)

/-! ## 1. The exporter after canonicalisation -/

/-- `ComL.toLfundefPhysAbiScalarAcc` with the canonicalised body `canon` as an input in place
    of `canonicalizeMemrefThread virt0.lfd_body`; every other stage is the exporter's text. -/
def scalarAccOfCanon (virt0 : Lfundef) (canon : Lcmd)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI", "RDX", "RCX"])
    (abiTyin : List Nat := [64, 64, 64, 64]) : Lfundef :=
  let livePin : Lcmd :=
    if abiArgs.length ≥ 3 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  let body1 := livePin ++ canon
  let virt := { virt0 with lfd_body := body1 }
  let tbl := physTableOut virt.lfd_body []
  let prologue := buildPrologue virt tbl (fun _ => none) ++ argRegSaves (abiArgs.drop 2)
  let argMat := buildArgPtrMaterialize virt tbl abiArgs (fun _ => none)
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  let memrefBaseReload : String → Option String :=
    let pairs : List (String × String) :=
      (abiArgs.zipIdx).filterMap (fun ⟨abiReg, j⟩ =>
        match abiSaveOfExt abiReg with
        | some saveName =>
            some (physNameForBody virt.lfd_body tbl (argName j), saveName)
        | none => none)
    fun base => (pairs.find? (fun p => p.1 == base)).map Prod.snd
  let bodyWithReload := (physBodyWithStores shiftImm' virt.lfd_body
    (fun _ => none) reloadScratch2 [] reloadScratch2 0 memrefBaseReload).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  let retMat : Lcmd :=
    match virt.lfd_res.head? with
    | some rn =>
        let phys := physNameForBody virt.lfd_body tbl rn
        if phys == sysvRetReg then []
        else [⟨0, .Lopn [.reg sysvRetReg] "MOVQ" [.reg phys]⟩]
    | none => []
  let bodyWithRestore := insertEpilogue bodyWithReload (retMat ++ calleeSaveRestoreEpilogue)
  { virt with
    lfd_body := prologue ++ argMat ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := [sysvRetReg]
    lfd_tyout := [64] }

theorem toLfundefPhysAbiScalarAcc_eq_ofCanon {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) :
    ComL.toLfundefPhysAbiScalarAcc c (fun _ => none) immSlotMap abiArgs abiTyin
      = scalarAccOfCanon (ComL.toLfundef c immSlotMap)
          (canonicalizeMemrefThread (ComL.toLfundef c immSlotMap).lfd_body)
          (fun _ => none) abiArgs abiTyin := rfl

theorem stripWidthTag_loadidx : stripWidthTag "LOADIDX" = "LOADIDX" := by kernel_rfl
theorem stripWidthTag_storeidx : stripWidthTag "STOREIDX" = "STOREIDX" := by kernel_rfl

/-! ## 2. `mpn_add_n_loop_owned` -/

/-- The runtime-trip loop node of `addRtProgOpt` over `addUpdate`. -/
noncomputable def addCom : ComL ΓouterCarry (mapTy (.sword 64)) :=
  ComL.forLoopNRt addUpdate (.there .here) .here
    (.cons (.there (.there (.there .here)))
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) .nil))) (.ret .here)

/-- **The linked program is the scalar-accumulator export of `addCom`.** -/
theorem addLprogFront_eq : addLprogFront () = some (ComL.toLprogPhysAbiScalarAcc addCom
    "mpn_add_n_loop_owned" (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64]) := by
  unfold addLprogFront addRtProgOpt
  change Option.map _ (compileLoop (Γouter := ΓouterCarry) .plain (.runtime _) _ _ _ _ _) = _
  erw [← compileLoopCont_ret_here]
  simp only [compileLoopCont]
  unfold rolledForLoopNRtCont
  split
  next u hu =>
    have : u = addUpdate := Option.some.inj (hu.symm.trans addUpdate_eq)
    subst this; rfl
  next hu => exact absurd (hu.symm.trans addUpdate_eq) (by simp)

/-- The virtual body of `addCom` at the zero seed. -/
def addVirtLit : Lcmd := ([
      .Lopn [.reg "r5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lidx5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lctr5"] "MOV:64" [.reg "a3"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "Z") 1073741829,
      .Llabel (.internal) 5,
      .Lopn [.reg "L5_r5"] "SHL:0:64" [.reg "Lidx5"],
      .Lopn [.reg "L5_r6"] "LOADIDX" [.arrIdx "a1" "L5_r5" 8],
      .Lopn [.reg "L5_r7"] "LOADIDX" [.arrIdx "a2" "L5_r5" 8],
      .Lopn [.reg "L5_r8"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r9"] "SHR:1:64" [.reg "L5_r6"],
      .Lopn [.reg "L5_r10"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r11"] "SHR:1:64" [.reg "L5_r7"],
      .Lopn [.reg "L5_r12"] "ADD:64" [.reg "L5_r9", .reg "L5_r11"],
      .Lopn [.reg "L5_r13"] "AND:64" [.reg "L5_r6", .reg "L5_r7"],
      .Lopn [.reg "L5_r14"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r15"] "AND:64" [.reg "L5_r13", .reg "L5_r14"],
      .Lopn [.reg "L5_r16"] "ADD:64" [.reg "L5_r12", .reg "L5_r15"],
      .Lopn [.reg "L5_r17"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r18"] "SHR:63:64" [.reg "L5_r16"],
      .Lopn [.reg "L5_r19"] "SHL:0:64" [.reg "L5_r18"],
      .Lopn [.reg "L5_r20"] "ADD:64" [.reg "L5_r6", .reg "L5_r7"],
      .Lopn [.reg "L5_r21"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r22"] "AND:64" [.reg "L5_r20", .reg "L5_r21"],
      .Lopn [.reg "L5_r23"] "SHL:0:64" [.reg "L5_r22"],
      .Lopn [.reg "L5_r24"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r25"] "SHR:1:64" [.reg "L5_r23"],
      .Lopn [.reg "L5_r26"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r27"] "SHR:1:64" [.reg "r5"],
      .Lopn [.reg "L5_r28"] "ADD:64" [.reg "L5_r25", .reg "L5_r27"],
      .Lopn [.reg "L5_r29"] "AND:64" [.reg "L5_r23", .reg "r5"],
      .Lopn [.reg "L5_r30"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r31"] "AND:64" [.reg "L5_r29", .reg "L5_r30"],
      .Lopn [.reg "L5_r32"] "ADD:64" [.reg "L5_r28", .reg "L5_r31"],
      .Lopn [.reg "L5_r33"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r34"] "SHR:63:64" [.reg "L5_r32"],
      .Lopn [.reg "L5_r35"] "SHL:0:64" [.reg "L5_r34"],
      .Lopn [.reg "L5_r36"] "ADD:64" [.reg "L5_r23", .reg "r5"],
      .Lopn [.reg "L5_r37"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r38"] "AND:64" [.reg "L5_r36", .reg "L5_r37"],
      .Lopn [.reg "L5_r39"] "SHL:0:64" [.reg "L5_r38"],
      .Lopn [.reg "L5_r40"] "STOREIDX" [.arrIdx "a0" "L5_r5" 8, .reg "L5_r39"],
      .Lopn [.reg "L5_r41"] "ADD:64" [.reg "L5_r19", .reg "L5_r35"],
      .Lopn [.reg "L5_r42"] "SHL:0:64" [.reg "L5_r41"],
      .Lopn [.reg "r5"] "MOV:64" [.reg "L5_r42"],
      .Lopn [.reg "Lidx5"] "ADD:64" [.reg "Lidx5", .imm 1],
      .Lopn [.reg "Lctr5"] "SUB:64" [.reg "Lctr5", .imm 1],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a1"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a2"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a0"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "NZ") 5,
      .Llabel (.internal) 1073741829,
      .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem addVirt_eq : (ComL.toLfundef addCom mpnSeedImm).lfd_body = addVirtLit := by
  kernel_rfl

/-- The alias map of the store thread: the store result `L5_r40` resolves to `a0`. -/
theorem addChain_eq :
    arrChainAlias addVirtLit = (({} : Std.HashMap String String).insert "L5_r40" "a0") := by
  simp [arrChainAlias, addVirtLit, isMemStore, stripWidthTag_loadidx, stripWidthTag_storeidx]

/-- The canonicalised body. -/
def addCanonLit : Lcmd := ([
      .Lopn [.reg "r5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lidx5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lctr5"] "MOV:64" [.reg "a3"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "Z") 1073741829,
      .Llabel (.internal) 5,
      .Lopn [.reg "L5_r5"] "SHL:0:64" [.reg "Lidx5"],
      .Lopn [.reg "L5_r6"] "LOADIDX" [.arrIdx "a1" "L5_r5" 8],
      .Lopn [.reg "L5_r7"] "LOADIDX" [.arrIdx "a2" "L5_r5" 8],
      .Lopn [.reg "L5_r8"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r9"] "SHR:1:64" [.reg "L5_r6"],
      .Lopn [.reg "L5_r10"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r11"] "SHR:1:64" [.reg "L5_r7"],
      .Lopn [.reg "L5_r12"] "ADD:64" [.reg "L5_r9", .reg "L5_r11"],
      .Lopn [.reg "L5_r13"] "AND:64" [.reg "L5_r6", .reg "L5_r7"],
      .Lopn [.reg "L5_r14"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r15"] "AND:64" [.reg "L5_r13", .reg "L5_r14"],
      .Lopn [.reg "L5_r16"] "ADD:64" [.reg "L5_r12", .reg "L5_r15"],
      .Lopn [.reg "L5_r17"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r18"] "SHR:63:64" [.reg "L5_r16"],
      .Lopn [.reg "L5_r19"] "SHL:0:64" [.reg "L5_r18"],
      .Lopn [.reg "L5_r20"] "ADD:64" [.reg "L5_r6", .reg "L5_r7"],
      .Lopn [.reg "L5_r21"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r22"] "AND:64" [.reg "L5_r20", .reg "L5_r21"],
      .Lopn [.reg "L5_r23"] "SHL:0:64" [.reg "L5_r22"],
      .Lopn [.reg "L5_r24"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r25"] "SHR:1:64" [.reg "L5_r23"],
      .Lopn [.reg "L5_r26"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r27"] "SHR:1:64" [.reg "r5"],
      .Lopn [.reg "L5_r28"] "ADD:64" [.reg "L5_r25", .reg "L5_r27"],
      .Lopn [.reg "L5_r29"] "AND:64" [.reg "L5_r23", .reg "r5"],
      .Lopn [.reg "L5_r30"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r31"] "AND:64" [.reg "L5_r29", .reg "L5_r30"],
      .Lopn [.reg "L5_r32"] "ADD:64" [.reg "L5_r28", .reg "L5_r31"],
      .Lopn [.reg "L5_r33"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r34"] "SHR:63:64" [.reg "L5_r32"],
      .Lopn [.reg "L5_r35"] "SHL:0:64" [.reg "L5_r34"],
      .Lopn [.reg "L5_r36"] "ADD:64" [.reg "L5_r23", .reg "r5"],
      .Lopn [.reg "L5_r37"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r38"] "AND:64" [.reg "L5_r36", .reg "L5_r37"],
      .Lopn [.reg "L5_r39"] "SHL:0:64" [.reg "L5_r38"],
      .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L5_r5" 8, .reg "L5_r39"],
      .Lopn [.reg "L5_r41"] "ADD:64" [.reg "L5_r19", .reg "L5_r35"],
      .Lopn [.reg "L5_r42"] "SHL:0:64" [.reg "L5_r41"],
      .Lopn [.reg "r5"] "MOV:64" [.reg "L5_r42"],
      .Lopn [.reg "Lidx5"] "ADD:64" [.reg "Lidx5", .imm 1],
      .Lopn [.reg "Lctr5"] "SUB:64" [.reg "Lctr5", .imm 1],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a1"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a2"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a0"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "NZ") 5,
      .Llabel (.internal) 1073741829,
      .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem addCanon_eq : canonicalizeMemrefThread addVirtLit = addCanonLit := by
  unfold canonicalizeMemrefThread
  rw [addChain_eq]
  simp [Std.HashMap.isEmpty_insert, addVirtLit, addCanonLit, canonMemrefOperand,
    canonMemrefName, Std.HashMap.getD_insert]

/-- The physical body of the linked `mpn_add_n_loop_owned`. -/
def addPhysLit : Lcmd := ([
      .Lopn [.reg "qsave.RDI"] "MOVQ" [.reg "RDI"],
      .Lopn [.reg "qsave.RSI"] "MOVQ" [.reg "RSI"],
      .Lopn [.reg "qsave.RBX"] "MOVQ" [.reg "RBX"],
      .Lopn [.reg "qsave.RBP"] "MOVQ" [.reg "RBP"],
      .Lopn [.reg "qsave.R12"] "MOVQ" [.reg "R12"],
      .Lopn [.reg "qsave.R13"] "MOVQ" [.reg "R13"],
      .Lopn [.reg "qsave.R14"] "MOVQ" [.reg "R14"],
      .Lopn [.reg "qsave.R15"] "MOVQ" [.reg "R15"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "RSI"],
      .Lopn [.reg "qsave.RDX"] "MOVQ" [.reg "RDX"],
      .Lopn [.reg "qsave.RCX"] "MOVQ" [.reg "RCX"],
      .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RDI"],
      .Lopn [.reg "RCX"] "MOVQ" [.reg "qsave.RSI"],
      .Lopn [.reg "RSI"] "MOVQ" [.reg "qsave.RCX"],
      .Lopn [.reg "RAX"] "MOV:64" [.imm 0],
      .Lopn [.reg "RDI"] "MOV:64" [.imm 0],
      .Lopn [.reg "RBP"] "MOV:64" [.reg "RSI"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .imm 0],
      .Lcond (.reg "Z") 1073741829,
      .Llabel (.internal) 5,
      .Lopn [.reg "RSI"] "SHL:0:64" [.reg "RDI"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
      .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDX"],
      .Lopn [.reg "R9"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
      .Lopn [.reg "R10"] "MOV:64" [.imm 1],
      .Lopn [.reg "R10"] "SHR:1:64" [.reg "R8"],
      .Lopn [.reg "R11"] "MOV:64" [.imm 1],
      .Lopn [.reg "R11"] "SHR:1:64" [.reg "R9"],
      .Lopn [.reg "R12"] "MOV:64" [.reg "R10"],
      .Lopn [.reg "R12"] "ADD:64" [.reg "R12", .reg "R11"],
      .Lopn [.reg "R10"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "R10"] "AND:64" [.reg "R10", .reg "R9"],
      .Lopn [.reg "R11"] "MOV:64" [.imm 1],
      .Lopn [.reg "R13"] "MOV:64" [.reg "R10"],
      .Lopn [.reg "R13"] "AND:64" [.reg "R13", .reg "R11"],
      .Lopn [.reg "R10"] "MOV:64" [.reg "R12"],
      .Lopn [.reg "R10"] "ADD:64" [.reg "R10", .reg "R13"],
      .Lopn [.reg "R11"] "MOV:64" [.imm 63],
      .Lopn [.reg "R11"] "SHR:63:64" [.reg "R10"],
      .Lopn [.reg "R10"] "SHL:0:64" [.reg "R11"],
      .Lopn [.reg "R11"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "R11"] "ADD:64" [.reg "R11", .reg "R9"],
      .Lopn [.reg "R8"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "R9"] "MOV:64" [.reg "R11"],
      .Lopn [.reg "R9"] "AND:64" [.reg "R9", .reg "R8"],
      .Lopn [.reg "R8"] "SHL:0:64" [.reg "R9"],
      .Lopn [.reg "R9"] "MOV:64" [.imm 1],
      .Lopn [.reg "R9"] "SHR:1:64" [.reg "R8"],
      .Lopn [.reg "R11"] "MOV:64" [.imm 1],
      .Lopn [.reg "R11"] "SHR:1:64" [.reg "RAX"],
      .Lopn [.reg "R12"] "MOV:64" [.reg "R9"],
      .Lopn [.reg "R12"] "ADD:64" [.reg "R12", .reg "R11"],
      .Lopn [.reg "R9"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "R9"] "AND:64" [.reg "R9", .reg "RAX"],
      .Lopn [.reg "R11"] "MOV:64" [.imm 1],
      .Lopn [.reg "R13"] "MOV:64" [.reg "R9"],
      .Lopn [.reg "R13"] "AND:64" [.reg "R13", .reg "R11"],
      .Lopn [.reg "R9"] "MOV:64" [.reg "R12"],
      .Lopn [.reg "R9"] "ADD:64" [.reg "R9", .reg "R13"],
      .Lopn [.reg "R11"] "MOV:64" [.imm 63],
      .Lopn [.reg "R11"] "SHR:63:64" [.reg "R9"],
      .Lopn [.reg "R9"] "SHL:0:64" [.reg "R11"],
      .Lopn [.reg "R11"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "R11"] "ADD:64" [.reg "R11", .reg "RAX"],
      .Lopn [.reg "R8"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "R12"] "MOV:64" [.reg "R11"],
      .Lopn [.reg "R12"] "AND:64" [.reg "R12", .reg "R8"],
      .Lopn [.reg "R8"] "SHL:0:64" [.reg "R12"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
      .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "R8"],
      .Lopn [.reg "RSI"] "MOV:64" [.reg "R10"],
      .Lopn [.reg "RSI"] "ADD:64" [.reg "RSI", .reg "R9"],
      .Lopn [.reg "R8"] "SHL:0:64" [.reg "RSI"],
      .Lopn [.reg "RAX"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "RDI"] "ADD:64" [.reg "RDI", .imm 1],
      .Lopn [.reg "RBP"] "SUB:64" [.reg "RBP", .imm 1],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "RCX"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "RDX"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "RBX"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .imm 0],
      .Lcond (.reg "NZ") 5,
      .Llabel (.internal) 1073741829,
      .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"],
      .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"],
      .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"],
      .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"],
      .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"],
      .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem addScalarAccOfCanon_eq :
    (scalarAccOfCanon (ComL.toLfundef addCom mpnSeedImm) addCanonLit (fun _ => none) gmpAbiArgs
      [64, 64, 64, 64]).lfd_body = addPhysLit := by
  kernel_rfl

/-- **The function body of the linked `mpn_add_n_loop_owned`** is `addPhysLit`. -/
theorem addPhysAbi_eq : (ComL.toLfundefPhysAbiScalarAcc addCom (fun _ => none) mpnSeedImm
    gmpAbiArgs [64, 64, 64, 64]).lfd_body = addPhysLit := by
  rw [toLfundefPhysAbiScalarAcc_eq_ofCanon, addVirt_eq, addCanon_eq]
  exact addScalarAccOfCanon_eq

theorem addPhysLit_encodable : encodableLcmd addPhysLit = true := by kernel_rfl

theorem addPhysLit_bytes : encodeLfundefBytes addPhysLit = MpnAddSubShipped.addText := by
  kernel_rfl

/-- **The object bytes of `addLprogFront` are the linked object.** -/
theorem addObjBytes_eq : MpnLoopBytesEmit.objBytes (addLprogFront ()) = some MpnAddSubShipped.addObj := by
  rw [MpnLoopBytesEmit.objBytes, addLprogFront_eq, Option.bind_some, encodeLprogChecked]
  rw [ite_eq_left (by simp [ComL.toLprogPhysAbiScalarAcc, addPhysAbi_eq, addPhysLit_encodable])]
  rw [MpnAddSubShipped.addObj_eq, ← addPhysLit_bytes, ← addPhysAbi_eq]
  rfl

/-! ## 2. `mpn_sub_n_loop_owned` -/

/-- The runtime-trip loop node of `subRtProgOpt` over `subUpdate`. -/
noncomputable def subCom : ComL ΓouterCarry (mapTy (.sword 64)) :=
  ComL.forLoopNRt subUpdate (.there .here) .here
    (.cons (.there (.there (.there .here)))
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) .nil))) (.ret .here)

/-- **The linked program is the scalar-accumulator export of `subCom`.** -/
theorem subLprogFront_eq : subLprogFront () = some (ComL.toLprogPhysAbiScalarAcc subCom
    "mpn_sub_n_loop_owned" (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64]) := by
  unfold subLprogFront subRtProgOpt
  change Option.map _ (compileLoop (Γouter := ΓouterCarry) .plain (.runtime _) _ _ _ _ _) = _
  erw [← compileLoopCont_ret_here]
  simp only [compileLoopCont]
  unfold rolledForLoopNRtCont
  split
  next u hu =>
    have : u = subUpdate := Option.some.inj (hu.symm.trans subUpdate_eq)
    subst this; rfl
  next hu => exact absurd (hu.symm.trans subUpdate_eq) (by simp)

/-- The virtual body of `subCom` at the zero seed. -/
def subVirtLit : Lcmd := ([
      .Lopn [.reg "r5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lidx5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lctr5"] "MOV:64" [.reg "a3"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "Z") 1073741829,
      .Llabel (.internal) 5,
      .Lopn [.reg "L5_r5"] "SHL:0:64" [.reg "Lidx5"],
      .Lopn [.reg "L5_r6"] "LOADIDX" [.arrIdx "a1" "L5_r5" 8],
      .Lopn [.reg "L5_r7"] "LOADIDX" [.arrIdx "a2" "L5_r5" 8],
      .Lopn [.reg "L5_r8"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r9"] "XOR:64" [.reg "L5_r7", .reg "L5_r8"],
      .Lopn [.reg "L5_r10"] "SHL:0:64" [.reg "L5_r9"],
      .Lopn [.reg "L5_r11"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r12"] "XOR:64" [.reg "r5", .reg "L5_r11"],
      .Lopn [.reg "L5_r13"] "SHL:0:64" [.reg "L5_r12"],
      .Lopn [.reg "L5_r14"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r15"] "SHR:1:64" [.reg "L5_r6"],
      .Lopn [.reg "L5_r16"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r17"] "SHR:1:64" [.reg "L5_r10"],
      .Lopn [.reg "L5_r18"] "ADD:64" [.reg "L5_r15", .reg "L5_r17"],
      .Lopn [.reg "L5_r19"] "AND:64" [.reg "L5_r6", .reg "L5_r10"],
      .Lopn [.reg "L5_r20"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r21"] "AND:64" [.reg "L5_r19", .reg "L5_r20"],
      .Lopn [.reg "L5_r22"] "ADD:64" [.reg "L5_r18", .reg "L5_r21"],
      .Lopn [.reg "L5_r23"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r24"] "SHR:63:64" [.reg "L5_r22"],
      .Lopn [.reg "L5_r25"] "SHL:0:64" [.reg "L5_r24"],
      .Lopn [.reg "L5_r26"] "ADD:64" [.reg "L5_r6", .reg "L5_r10"],
      .Lopn [.reg "L5_r27"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r28"] "AND:64" [.reg "L5_r26", .reg "L5_r27"],
      .Lopn [.reg "L5_r29"] "SHL:0:64" [.reg "L5_r28"],
      .Lopn [.reg "L5_r30"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r31"] "SHR:1:64" [.reg "L5_r29"],
      .Lopn [.reg "L5_r32"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r33"] "SHR:1:64" [.reg "L5_r13"],
      .Lopn [.reg "L5_r34"] "ADD:64" [.reg "L5_r31", .reg "L5_r33"],
      .Lopn [.reg "L5_r35"] "AND:64" [.reg "L5_r29", .reg "L5_r13"],
      .Lopn [.reg "L5_r36"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r37"] "AND:64" [.reg "L5_r35", .reg "L5_r36"],
      .Lopn [.reg "L5_r38"] "ADD:64" [.reg "L5_r34", .reg "L5_r37"],
      .Lopn [.reg "L5_r39"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r40"] "SHR:63:64" [.reg "L5_r38"],
      .Lopn [.reg "L5_r41"] "SHL:0:64" [.reg "L5_r40"],
      .Lopn [.reg "L5_r42"] "ADD:64" [.reg "L5_r29", .reg "L5_r13"],
      .Lopn [.reg "L5_r43"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r44"] "AND:64" [.reg "L5_r42", .reg "L5_r43"],
      .Lopn [.reg "L5_r45"] "SHL:0:64" [.reg "L5_r44"],
      .Lopn [.reg "L5_r46"] "STOREIDX" [.arrIdx "a0" "L5_r5" 8, .reg "L5_r45"],
      .Lopn [.reg "L5_r47"] "ADD:64" [.reg "L5_r25", .reg "L5_r41"],
      .Lopn [.reg "L5_r48"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r49"] "XOR:64" [.reg "L5_r47", .reg "L5_r48"],
      .Lopn [.reg "L5_r50"] "SHL:0:64" [.reg "L5_r49"],
      .Lopn [.reg "r5"] "MOV:64" [.reg "L5_r50"],
      .Lopn [.reg "Lidx5"] "ADD:64" [.reg "Lidx5", .imm 1],
      .Lopn [.reg "Lctr5"] "SUB:64" [.reg "Lctr5", .imm 1],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a1"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a2"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a0"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "NZ") 5,
      .Llabel (.internal) 1073741829,
      .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem subVirt_eq : (ComL.toLfundef subCom mpnSeedImm).lfd_body = subVirtLit := by
  kernel_rfl

/-- One instruction of `arrChainAlias`: a memref store `dst := base[…]` maps `dst` to the
    resolved `base`, and every other instruction leaves the map unchanged. -/
def aliasStep (m : Std.HashMap String String) (i : Linstr) : Std.HashMap String String :=
  match i.li_i with
  | .Lopn [.reg dst] opn (.arrIdx base _ _ :: _) =>
      if isMemStore opn then m.insert dst (m.getD base base) else m
  | _ => m

/-- `arrChainAlias` is the left fold of `aliasStep` from the empty map. -/
theorem arrChainAlias_eq_foldl (body : Lcmd) :
    arrChainAlias body = body.foldl aliasStep {} := by
  unfold arrChainAlias
  generalize ({} : Std.HashMap String String) = m0
  induction body generalizing m0 with
  | nil => rfl
  | cons i is ih =>
    simp only [List.forIn_cons, List.foldl_cons, ← ih]
    unfold aliasStep
    split <;> grind

/-- The alias map of the store thread: the store result `L5_r46` resolves to `a0`. -/
theorem subChain_eq :
    arrChainAlias subVirtLit = (({} : Std.HashMap String String).insert "L5_r46" "a0") := by
  rw [arrChainAlias_eq_foldl]
  simp [subVirtLit, aliasStep, isMemStore, stripWidthTag_loadidx, stripWidthTag_storeidx]

/-- The canonicalised body. -/
def subCanonLit : Lcmd := ([
      .Lopn [.reg "r5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lidx5"] "MOV:64" [.imm 0],
      .Lopn [.reg "Lctr5"] "MOV:64" [.reg "a3"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "Z") 1073741829,
      .Llabel (.internal) 5,
      .Lopn [.reg "L5_r5"] "SHL:0:64" [.reg "Lidx5"],
      .Lopn [.reg "L5_r6"] "LOADIDX" [.arrIdx "a1" "L5_r5" 8],
      .Lopn [.reg "L5_r7"] "LOADIDX" [.arrIdx "a2" "L5_r5" 8],
      .Lopn [.reg "L5_r8"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r9"] "XOR:64" [.reg "L5_r7", .reg "L5_r8"],
      .Lopn [.reg "L5_r10"] "SHL:0:64" [.reg "L5_r9"],
      .Lopn [.reg "L5_r11"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r12"] "XOR:64" [.reg "r5", .reg "L5_r11"],
      .Lopn [.reg "L5_r13"] "SHL:0:64" [.reg "L5_r12"],
      .Lopn [.reg "L5_r14"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r15"] "SHR:1:64" [.reg "L5_r6"],
      .Lopn [.reg "L5_r16"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r17"] "SHR:1:64" [.reg "L5_r10"],
      .Lopn [.reg "L5_r18"] "ADD:64" [.reg "L5_r15", .reg "L5_r17"],
      .Lopn [.reg "L5_r19"] "AND:64" [.reg "L5_r6", .reg "L5_r10"],
      .Lopn [.reg "L5_r20"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r21"] "AND:64" [.reg "L5_r19", .reg "L5_r20"],
      .Lopn [.reg "L5_r22"] "ADD:64" [.reg "L5_r18", .reg "L5_r21"],
      .Lopn [.reg "L5_r23"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r24"] "SHR:63:64" [.reg "L5_r22"],
      .Lopn [.reg "L5_r25"] "SHL:0:64" [.reg "L5_r24"],
      .Lopn [.reg "L5_r26"] "ADD:64" [.reg "L5_r6", .reg "L5_r10"],
      .Lopn [.reg "L5_r27"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r28"] "AND:64" [.reg "L5_r26", .reg "L5_r27"],
      .Lopn [.reg "L5_r29"] "SHL:0:64" [.reg "L5_r28"],
      .Lopn [.reg "L5_r30"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r31"] "SHR:1:64" [.reg "L5_r29"],
      .Lopn [.reg "L5_r32"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r33"] "SHR:1:64" [.reg "L5_r13"],
      .Lopn [.reg "L5_r34"] "ADD:64" [.reg "L5_r31", .reg "L5_r33"],
      .Lopn [.reg "L5_r35"] "AND:64" [.reg "L5_r29", .reg "L5_r13"],
      .Lopn [.reg "L5_r36"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r37"] "AND:64" [.reg "L5_r35", .reg "L5_r36"],
      .Lopn [.reg "L5_r38"] "ADD:64" [.reg "L5_r34", .reg "L5_r37"],
      .Lopn [.reg "L5_r39"] "MOV:64" [.imm 63],
      .Lopn [.reg "L5_r40"] "SHR:63:64" [.reg "L5_r38"],
      .Lopn [.reg "L5_r41"] "SHL:0:64" [.reg "L5_r40"],
      .Lopn [.reg "L5_r42"] "ADD:64" [.reg "L5_r29", .reg "L5_r13"],
      .Lopn [.reg "L5_r43"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "L5_r44"] "AND:64" [.reg "L5_r42", .reg "L5_r43"],
      .Lopn [.reg "L5_r45"] "SHL:0:64" [.reg "L5_r44"],
      .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L5_r5" 8, .reg "L5_r45"],
      .Lopn [.reg "L5_r47"] "ADD:64" [.reg "L5_r25", .reg "L5_r41"],
      .Lopn [.reg "L5_r48"] "MOV:64" [.imm 1],
      .Lopn [.reg "L5_r49"] "XOR:64" [.reg "L5_r47", .reg "L5_r48"],
      .Lopn [.reg "L5_r50"] "SHL:0:64" [.reg "L5_r49"],
      .Lopn [.reg "r5"] "MOV:64" [.reg "L5_r50"],
      .Lopn [.reg "Lidx5"] "ADD:64" [.reg "Lidx5", .imm 1],
      .Lopn [.reg "Lctr5"] "SUB:64" [.reg "Lctr5", .imm 1],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a1"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a2"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .reg "a0"],
      .Lopn [.reg "Lctr5"] "CMP:64" [.reg "Lctr5", .imm 0],
      .Lcond (.reg "NZ") 5,
      .Llabel (.internal) 1073741829,
      .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem subCanon_eq : canonicalizeMemrefThread subVirtLit = subCanonLit := by
  unfold canonicalizeMemrefThread
  rw [subChain_eq]
  simp [Std.HashMap.isEmpty_insert, subVirtLit, subCanonLit, canonMemrefOperand,
    canonMemrefName, Std.HashMap.getD_insert]

/-- The physical body of the linked `mpn_sub_n_loop_owned`. -/
def subPhysLit : Lcmd := ([
      .Lopn [.reg "qsave.RDI"] "MOVQ" [.reg "RDI"],
      .Lopn [.reg "qsave.RSI"] "MOVQ" [.reg "RSI"],
      .Lopn [.reg "qsave.RBX"] "MOVQ" [.reg "RBX"],
      .Lopn [.reg "qsave.RBP"] "MOVQ" [.reg "RBP"],
      .Lopn [.reg "qsave.R12"] "MOVQ" [.reg "R12"],
      .Lopn [.reg "qsave.R13"] "MOVQ" [.reg "R13"],
      .Lopn [.reg "qsave.R14"] "MOVQ" [.reg "R14"],
      .Lopn [.reg "qsave.R15"] "MOVQ" [.reg "R15"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "RSI"],
      .Lopn [.reg "qsave.RDX"] "MOVQ" [.reg "RDX"],
      .Lopn [.reg "qsave.RCX"] "MOVQ" [.reg "RCX"],
      .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RDI"],
      .Lopn [.reg "RCX"] "MOVQ" [.reg "qsave.RSI"],
      .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.RDX"],
      .Lopn [.reg "k.0"] "MOVQ" [.reg "R15"],
      .Lopn [.reg "RSI"] "MOVQ" [.reg "qsave.RCX"],
      .Lopn [.reg "RAX"] "MOV:64" [.imm 0],
      .Lopn [.reg "RDI"] "MOV:64" [.imm 0],
      .Lopn [.reg "RBP"] "MOV:64" [.reg "RSI"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .imm 0],
      .Lcond (.reg "Z") 1073741829,
      .Llabel (.internal) 5,
      .Lopn [.reg "RSI"] "SHL:0:64" [.reg "RDI"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
      .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDX"],
      .Lopn [.reg "R9"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
      .Lopn [.reg "R10"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "R11"] "MOV:64" [.reg "R9"],
      .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "R10"],
      .Lopn [.reg "R9"] "SHL:0:64" [.reg "R11"],
      .Lopn [.reg "R10"] "MOV:64" [.imm 1],
      .Lopn [.reg "R11"] "MOV:64" [.reg "RAX"],
      .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "R10"],
      .Lopn [.reg "R10"] "SHL:0:64" [.reg "R11"],
      .Lopn [.reg "R11"] "MOV:64" [.imm 1],
      .Lopn [.reg "R11"] "SHR:1:64" [.reg "R8"],
      .Lopn [.reg "R12"] "MOV:64" [.imm 1],
      .Lopn [.reg "R12"] "SHR:1:64" [.reg "R9"],
      .Lopn [.reg "R13"] "MOV:64" [.reg "R11"],
      .Lopn [.reg "R13"] "ADD:64" [.reg "R13", .reg "R12"],
      .Lopn [.reg "R11"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "R11"] "AND:64" [.reg "R11", .reg "R9"],
      .Lopn [.reg "R12"] "MOV:64" [.imm 1],
      .Lopn [.reg "RDX"] "MOV:64" [.reg "R11"],
      .Lopn [.reg "RDX"] "AND:64" [.reg "RDX", .reg "R12"],
      .Lopn [.reg "R11"] "MOV:64" [.reg "R13"],
      .Lopn [.reg "R11"] "ADD:64" [.reg "R11", .reg "RDX"],
      .Lopn [.reg "RDX"] "MOV:64" [.imm 63],
      .Lopn [.reg "RDX"] "SHR:63:64" [.reg "R11"],
      .Lopn [.reg "R11"] "SHL:0:64" [.reg "RDX"],
      .Lopn [.reg "RDX"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "RDX"] "ADD:64" [.reg "RDX", .reg "R9"],
      .Lopn [.reg "R8"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "R9"] "MOV:64" [.reg "RDX"],
      .Lopn [.reg "R9"] "AND:64" [.reg "R9", .reg "R8"],
      .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R9"],
      .Lopn [.reg "R8"] "MOV:64" [.imm 1],
      .Lopn [.reg "R8"] "SHR:1:64" [.reg "RDX"],
      .Lopn [.reg "R9"] "MOV:64" [.imm 1],
      .Lopn [.reg "R9"] "SHR:1:64" [.reg "R10"],
      .Lopn [.reg "R12"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "R12"] "ADD:64" [.reg "R12", .reg "R9"],
      .Lopn [.reg "R8"] "MOV:64" [.reg "RDX"],
      .Lopn [.reg "R8"] "AND:64" [.reg "R8", .reg "R10"],
      .Lopn [.reg "R9"] "MOV:64" [.imm 1],
      .Lopn [.reg "R13"] "MOV:64" [.reg "R8"],
      .Lopn [.reg "R13"] "AND:64" [.reg "R13", .reg "R9"],
      .Lopn [.reg "R8"] "MOV:64" [.reg "R12"],
      .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .reg "R13"],
      .Lopn [.reg "R9"] "MOV:64" [.imm 63],
      .Lopn [.reg "R9"] "SHR:63:64" [.reg "R8"],
      .Lopn [.reg "R8"] "SHL:0:64" [.reg "R9"],
      .Lopn [.reg "R9"] "MOV:64" [.reg "RDX"],
      .Lopn [.reg "R9"] "ADD:64" [.reg "R9", .reg "R10"],
      .Lopn [.reg "RDX"] "MOV:64" [.imm 18446744073709551615],
      .Lopn [.reg "R10"] "MOV:64" [.reg "R9"],
      .Lopn [.reg "R10"] "AND:64" [.reg "R10", .reg "RDX"],
      .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R10"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
      .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "RDX"],
      .Lopn [.reg "RDX"] "MOV:64" [.reg "R11"],
      .Lopn [.reg "RDX"] "ADD:64" [.reg "RDX", .reg "R8"],
      .Lopn [.reg "RSI"] "MOV:64" [.imm 1],
      .Lopn [.reg "R8"] "MOV:64" [.reg "RDX"],
      .Lopn [.reg "R8"] "XOR:64" [.reg "R8", .reg "RSI"],
      .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R8"],
      .Lopn [.reg "RAX"] "MOV:64" [.reg "RDX"],
      .Lopn [.reg "RDI"] "ADD:64" [.reg "RDI", .imm 1],
      .Lopn [.reg "RBP"] "SUB:64" [.reg "RBP", .imm 1],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "RCX"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "k.0"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "RBX"],
      .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .imm 0],
      .Lcond (.reg "NZ") 5,
      .Llabel (.internal) 1073741829,
      .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"],
      .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"],
      .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"],
      .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"],
      .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"],
      .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"],
      .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem subScalarAccOfCanon_eq :
    (scalarAccOfCanon (ComL.toLfundef subCom mpnSeedImm) subCanonLit (fun _ => none) gmpAbiArgs
      [64, 64, 64, 64]).lfd_body = subPhysLit := by
  kernel_rfl

/-- **The function body of the linked `mpn_sub_n_loop_owned`** is `subPhysLit`. -/
theorem subPhysAbi_eq : (ComL.toLfundefPhysAbiScalarAcc subCom (fun _ => none) mpnSeedImm
    gmpAbiArgs [64, 64, 64, 64]).lfd_body = subPhysLit := by
  rw [toLfundefPhysAbiScalarAcc_eq_ofCanon, subVirt_eq, subCanon_eq]
  exact subScalarAccOfCanon_eq

theorem subPhysLit_encodable : encodableLcmd subPhysLit = true := by kernel_rfl

theorem subPhysLit_bytes : encodeLfundefBytes subPhysLit = MpnAddSubShipped.subText := by
  kernel_rfl

/-- **The object bytes of `subLprogFront` are the linked object.** -/
theorem subObjBytes_eq : MpnLoopBytesEmit.objBytes (subLprogFront ()) = some MpnAddSubShipped.subObj := by
  rw [MpnLoopBytesEmit.objBytes, subLprogFront_eq, Option.bind_some, encodeLprogChecked]
  rw [ite_eq_left (by simp [ComL.toLprogPhysAbiScalarAcc, subPhysAbi_eq, subPhysLit_encodable])]
  rw [MpnAddSubShipped.subObj_eq, ← subPhysLit_bytes, ← subPhysAbi_eq]
  rfl

/-! ## 4. The end theorems at the object list -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip (at')
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue (wordsOf calleeSavedL)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)

/-- **`mpn_add_n_loop_owned` from the object list.** The object bytes of the program
    `MpnLoopBytesEmit.kernels` maps to the symbol are the linked object `addObj`, the ELF
    wrapping of `addText`, which decodes to `addDec`; and from every System V entry state with
    the layout `ArgLayout 80` the machine halts on `addDec` with the sum in `rp` and the carry
    in `%rax` (`MpnAddSubBytesCorrect.mpn_add_n_correct`). -/
theorem mpn_add_n_linked_correct :
    MpnLoopBytesEmit.objBytes (addLprogFront ()) = some MpnAddSubShipped.addObj
    ∧ MpnAddSubShipped.addObj = ElfObject.buildElfObjectMulti
        [{ name := "mpn_add_n_loop_owned", text := MpnAddSubShipped.addText }]
    ∧ decodeLprog MpnAddSubShipped.addText = some MpnAddSubShipped.addDec
    ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
      MpnAddSubBytesCorrect.ArgLayout 80 (s0.regs "%rsp") (s0.regs "%rdi") (s0.regs "%rsi")
        (s0.regs "%rdx") n →
      ∃ s', Halts aMachine MpnAddSubShipped.addDec 0 s0 s'
        ∧ bignumVal ((List.range n).map (wordsOf s'.mem (s0.regs "%rdi")))
            + (s'.regs "%rax").toNat * (2 ^ 64) ^ n
          = bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi")))
            + bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rdx")))
        ∧ (s'.regs "%rax").toNat ≤ 1
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ MpnAddBytesValue.Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem
            s'.mem :=
  ⟨addObjBytes_eq, MpnAddSubBytesCorrect.mpn_add_n_correct⟩

/-- **`mpn_sub_n_loop_owned` from the object list**, as `mpn_add_n_linked_correct`. -/
theorem mpn_sub_n_linked_correct :
    MpnLoopBytesEmit.objBytes (subLprogFront ()) = some MpnAddSubShipped.subObj
    ∧ MpnAddSubShipped.subObj = ElfObject.buildElfObjectMulti
        [{ name := "mpn_sub_n_loop_owned", text := MpnAddSubShipped.subText }]
    ∧ decodeLprog MpnAddSubShipped.subText = some MpnAddSubShipped.subDec
    ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
      MpnAddSubBytesCorrect.ArgLayout 96 (s0.regs "%rsp") (s0.regs "%rdi") (s0.regs "%rsi")
        (s0.regs "%rdx") n →
      ∃ s', Halts aMachine MpnAddSubShipped.subDec 0 s0 s'
        ∧ bignumVal ((List.range n).map (wordsOf s'.mem (s0.regs "%rdi")))
            + bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rdx")))
          = bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi")))
            + (s'.regs "%rax").toNat * (2 ^ 64) ^ n
        ∧ (s'.regs "%rax").toNat ≤ 1
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ MpnSubBytesValue.Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") n s0.mem
            s'.mem :=
  ⟨subObjBytes_eq, MpnAddSubBytesCorrect.mpn_sub_n_correct⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubExportTerm
