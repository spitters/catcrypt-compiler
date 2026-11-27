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
public import CatCrypt.Tactic.KernelRfl
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRuntimeBytesEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan

@[expose] public section

set_option autoImplicit false

/-!
# The exporter terms of the shipped runtime-trip shift and compare kernels

`MpnRuntimeBytesEmit.kernels` maps the objects `mpn_shift_rt_owned` and `mpn_cmp_ct_owned` to
`MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt"` and
`MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct"`. As `MpnBinExportTerm` does for the bitwise
kernels, this module computes each program's function body as a literal `Lcmd`, the object
bytes and the decoded layout, with the kernel and rewriting only (no `native_decide`). The
programs are exports of the loop nodes over `MpnShiftFrontDenote.shiftUpdate` and
`MpnCmpFrontDenote.cmpUpdate`, the bodies the existing denotation theorems are about.

## Main results

* `shiftLprog_eq`, `shiftPhysAbi_eq`, `shiftObjBytes_eq`, `shiftPhysLit_decode`.
* `cmpLprog_eq`, `cmpPhysAbi_eq`, `cmpObjBytes_eq`, `cmpPhysLit_decode`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
  (compileLoop compileLoopCont compileLoopCont_ret_here)
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
  (physAbiOfCanon ofVirtCert_eq_physAbiOfCanon stripWidthTag_loadidx stripWidthTag_storeidx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)

/-! ## `mpn_shift_rt` -/

/-- The runtime-trip loop node of `MpnShiftFrontEmit.shiftRtLprogOpt` over `MpnShiftFrontDenote.shiftUpdate`. -/
def shiftCom : ComL MpnShiftFrontEmit.Gouter MpnShiftFrontEmit.AR :=
  ComL.forLoopNRt MpnShiftFrontDenote.shiftUpdate MpnShiftFrontEmit.shiftCount MpnShiftFrontEmit.shiftInit MpnShiftFrontEmit.shiftInvs (.ret .here)

/-- **The shipped program is the physical-ABI export of `shiftCom`.** -/
theorem shiftLprog_eq : MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt" = some (ComL.toLprogPhysAbi shiftCom "mpn_shift_rt"
    (argName 0) [argName 1] (fun _ => none) (fun _ => none)
    ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]) := by
  unfold MpnShiftFrontEmit.shiftRtLprogOpt MpnShiftFrontEmit.shiftRtProgOpt
  change Option.map _ (compileLoop (Γouter := MpnShiftFrontEmit.Gouter)
    (accCTy := .memref MpnShiftFrontEmit.NRS)
    (invCTys := [.memref MpnShiftFrontEmit.NUS, .sword 64]) .plain (.runtime _) _ _ _ _ _) = _
  erw [← compileLoopCont_ret_here]
  simp only [compileLoopCont]
  unfold rolledForLoopNRtCont
  split
  next u hu =>
    have : u = MpnShiftFrontDenote.shiftUpdate := Option.some.inj (hu.symm.trans MpnShiftFrontDenote.shiftUpdate_eq)
    subst this; rfl
  next hu => exact absurd (hu.symm.trans MpnShiftFrontDenote.shiftUpdate_eq) (by simp)

theorem shiftBaseNames :
    ComL.loopArgBaseNames 4 (fun _ => none) shiftCom 4 = some ("a0", ["a1"]) := by
  kernel_rfl

theorem shiftAccRegs : (ComL.loopAccRegs shiftCom 4).map regName = ["r4"] := by
  kernel_rfl

def shiftAliasLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a0" "Lidx4" 8],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8],
    .Lopn [.reg "L4_r6"] "MOV:64" [.imm 64],
    .Lopn [.reg "L4_r7"] "SUB:64" [.reg "L4_r6", .reg "a3"],
    .Lopn [.reg "L4_r8"] "SHL:0:64" [.reg "L4_r7"],
    .Lopn [.reg "L4_r9"] "SHL:64" [.reg "L4_r5", .reg "a3"],
    .Lopn [.reg "L4_r10"] "SHL:0:64" [.reg "L4_r9"],
    .Lopn [.reg "L4_r11"] "SHR:64" [.reg "L4_r5", .reg "L4_r8"],
    .Lopn [.reg "L4_r12"] "SHL:0:64" [.reg "L4_r11"],
    .Lopn [.reg "L4_r13"] "ADD:64" [.reg "L4_r10", .reg "L4_r4"],
    .Lopn [.reg "L4_r14"] "SHL:0:64" [.reg "L4_r13"],
    .Lopn [.reg "L4_r15"] "STOREIDX" [.arrIdx "a0" "Lidx4" 8, .reg "L4_r14"],
    .Lopn [.reg "L4_r16"] "MOV:64" [.imm 1],
    .Lopn [.reg "L4_r17"] "ADD:64" [.reg "Lidx4", .reg "L4_r16"],
    .Lopn [.reg "L4_r18"] "SHL:0:64" [.reg "L4_r17"],
    .Lopn [.reg "L4_r19"] "STOREIDX" [.arrIdx "L4_r15" "L4_r18" 8, .reg "L4_r12"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "L4_r19"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem shiftAlias_eq :
    aliasRegBody "r4" "a0" (ComL.toLfundef shiftCom (fun _ => none)).lfd_body = shiftAliasLit := by
  kernel_rfl

theorem shiftChain_eq :
    arrChainAlias shiftAliasLit = ((({} : Std.HashMap String String).insert "L4_r15" "a0").insert "L4_r19" "a0") := by
  simp [arrChainAlias, shiftAliasLit, isMemStore, stripWidthTag_loadidx, stripWidthTag_storeidx]

def shiftCanonLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a0" "Lidx4" 8],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8],
    .Lopn [.reg "L4_r6"] "MOV:64" [.imm 64],
    .Lopn [.reg "L4_r7"] "SUB:64" [.reg "L4_r6", .reg "a3"],
    .Lopn [.reg "L4_r8"] "SHL:0:64" [.reg "L4_r7"],
    .Lopn [.reg "L4_r9"] "SHL:64" [.reg "L4_r5", .reg "a3"],
    .Lopn [.reg "L4_r10"] "SHL:0:64" [.reg "L4_r9"],
    .Lopn [.reg "L4_r11"] "SHR:64" [.reg "L4_r5", .reg "L4_r8"],
    .Lopn [.reg "L4_r12"] "SHL:0:64" [.reg "L4_r11"],
    .Lopn [.reg "L4_r13"] "ADD:64" [.reg "L4_r10", .reg "L4_r4"],
    .Lopn [.reg "L4_r14"] "SHL:0:64" [.reg "L4_r13"],
    .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "Lidx4" 8, .reg "L4_r14"],
    .Lopn [.reg "L4_r16"] "MOV:64" [.imm 1],
    .Lopn [.reg "L4_r17"] "ADD:64" [.reg "Lidx4", .reg "L4_r16"],
    .Lopn [.reg "L4_r18"] "SHL:0:64" [.reg "L4_r17"],
    .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L4_r18" 8, .reg "L4_r12"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem shiftCanon_eq : canonicalizeMemrefThread shiftAliasLit = shiftCanonLit := by
  unfold canonicalizeMemrefThread
  rw [shiftChain_eq]
  simp [Std.HashMap.isEmpty_insert, shiftAliasLit, shiftCanonLit, canonMemrefOperand,
    canonMemrefName, Std.HashMap.getD_insert]

/-- The physical body of the shipped `mpn_shift_rt`. -/
def shiftPhysLit : Lcmd := ([
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
    .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
    .Lopn [.reg "RAX"] "MOV:64" [.imm 0],
    .Lopn [.reg "RDI"] "MOV:64" [.reg "RDX"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RDX"] "LOADIDX" [.arrIdx "R14" "RAX" 8],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
    .Lopn [.reg "RBP"] "LOADIDX" [.arrIdx "R14" "RAX" 8],
    .Lopn [.reg "R8"] "MOV:64" [.imm 64],
    .Lopn [.reg "R9"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "R9"] "SUB:64" [.reg "R9", .reg "RSI"],
    .Lopn [.reg "R8"] "SHL:0:64" [.reg "R9"],
    .Lopn [.reg "R9"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "R9"] "SHL:64" [.reg "R9", .reg "RSI"],
    .Lopn [.reg "R10"] "SHL:0:64" [.reg "R9"],
    .Lopn [.reg "R9"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "R9"] "SHR:64" [.reg "R9", .reg "R8"],
    .Lopn [.reg "RBP"] "SHL:0:64" [.reg "R9"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "R10"],
    .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .reg "RDX"],
    .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RAX" 8, .reg "RDX"],
    .Lopn [.reg "RDX"] "MOV:64" [.imm 1],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"],
    .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .reg "RDX"],
    .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RDX" 8, .reg "RBP"],
    .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
    .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1],
    .Lopn [.reg "RDI"] "SUB:64" [.reg "RDI", .imm 1],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RCX"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RSI"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"],
    .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"],
    .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"],
    .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"],
    .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"],
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem shiftPhysAbiOfCanon_eq :
    (physAbiOfCanon (ComL.toLfundef shiftCom (fun _ => none)) shiftCanonLit "a0" ["a1"]
      (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).1.lfd_body
      = shiftPhysLit := by
  kernel_rfl

/-- **The function body of the shipped `mpn_shift_rt`** is `shiftPhysLit`. -/
theorem shiftPhysAbi_eq : (ComL.toLfundefPhysAbi shiftCom (argName 0) [argName 1]
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).lfd_body
      = shiftPhysLit := by
  rw [ComL.toLfundefPhysAbi_eq_ofVirt]
  have h4 : (MpnShiftFrontEmit.Gouter).length = 4 := rfl
  simp only [h4, shiftBaseNames, shiftAccRegs]
  unfold lfundefPhysAbiOfVirt
  rw [ofVirtCert_eq_physAbiOfCanon]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [shiftAlias_eq, shiftCanon_eq]
  exact shiftPhysAbiOfCanon_eq

/-- **The object bytes of the linked `mpn_shift_rt`** are the ELF wrapping of the function bytes
    of `shiftPhysLit`. -/
theorem shiftObjBytes_eq {bs : List (BitVec 8)}
    (h : MpnRuntimeBytesEmit.objBytes (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt") = some bs) :
    bs = ElfObject.buildElfObjectMulti
      [{ name := "mpn_shift_rt", text := encodeLfundefBytes shiftPhysLit }] := by
  rw [MpnRuntimeBytesEmit.objBytes, shiftLprog_eq, Option.bind_some] at h
  rw [LprogBytesDecode.encodeLprogChecked_single rfl h, shiftPhysAbi_eq]

def shiftDecPre : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-64)
  , .storeMem "%rsp" 56 (.reg "%rdi")
  , .storeMem "%rsp" 48 (.reg "%rsi")
  , .storeMem "%rsp" 40 (.reg "%rbx")
  , .storeMem "%rsp" 32 (.reg "%rbp")
  , .storeMem "%rsp" 24 (.reg "%r12")
  , .storeMem "%rsp" 16 (.reg "%r13")
  , .storeMem "%rsp" 8 (.reg "%r14")
  , .storeMem "%rsp" 0 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx")
  , .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 56
  , .loadMem "%rcx" "%rsp" 48
  , .loadMem "%rsi" "%rsp" (-16)
  , .mov "%rbx" (.reg "%rbx")
  , .mov "%rax" (.imm 0)
  , .mov "%rdi" (.reg "%rdx") ]

def shiftDecLoopBody : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 56
  , .loadMemIdx "%rdx" "%r14" "%rax" 8
  , .loadMem "%r14" "%rsp" 48
  , .loadMemIdx "%rbp" "%r14" "%rax" 8
  , .mov "%r8" (.imm 64)
  , .mov "%r9" (.reg "%r8")
  , .sub "%r9" (.reg "%rsi")
  , .mov "%r8" (.reg "%r9")
  , .mov "%r9" (.reg "%rbp")
  , .shlx "%r9" "%r9" "%rsi"
  , .mov "%r10" (.reg "%r9")
  , .mov "%r9" (.reg "%rbp")
  , .shrx "%r9" "%r9" "%r8"
  , .mov "%rbp" (.reg "%r9")
  , .mov "%r8" (.reg "%r10")
  , .add "%r8" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r8")
  , .loadMem "%r14" "%rsp" 56
  , .storeMemIdx "%r14" "%rax" 8 (.reg "%rdx")
  , .mov "%rdx" (.imm 1)
  , .mov "%r8" (.reg "%rax")
  , .add "%r8" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r8")
  , .loadMem "%r14" "%rsp" 56
  , .storeMemIdx "%r14" "%rdx" 8 (.reg "%rbp")
  , .mov "%rbx" (.reg "%rbx")
  , .add "%rax" (.imm 1)
  , .sub "%rdi" (.imm 1)
  , .cmp "%rdi" (.reg "%rcx")
  , .cmp "%rdi" (.reg "%rsi") ]

def shiftDecLoop : XLoop 64 := { top := 4, ctr := "%rdi", body := shiftDecLoopBody }

def shiftDecPost : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 40
  , .loadMem "%rbp" "%rsp" 32
  , .loadMem "%r12" "%rsp" 24
  , .loadMem "%r13" "%rsp" 16
  , .loadMem "%r14" "%rsp" 8
  , .loadMem "%r15" "%rsp" 0
  , .lea "%rsp" "%rsp" "%rsp" 0 64 ]

/-- **The decoded shipped `mpn_shift_rt`.** -/
theorem shiftPhysLit_decode :
    decodeLprog (encodeLfundefBytes shiftPhysLit)
      = some (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) := by
  kernel_rfl

/-! ## `mpn_cmp_ct` -/

set_option maxRecDepth 20000

/-- The runtime-trip loop node of `MpnCmpFrontEmit.cmpRtLprogOpt` over `MpnCmpFrontDenote.cmpUpdate`. -/
def cmpCom : ComL MpnCmpFrontEmit.Gouter MpnCmpFrontEmit.AR :=
  ComL.forLoopNRt MpnCmpFrontDenote.cmpUpdate MpnCmpFrontEmit.cmpCount MpnCmpFrontEmit.cmpInit MpnCmpFrontEmit.cmpInvs (.ret .here)

/-- **The shipped program is the physical-ABI export of `cmpCom`.** -/
theorem cmpLprog_eq : MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct" = some (ComL.toLprogPhysAbi cmpCom "mpn_cmp_ct"
    (argName 0) [argName 1, argName 2] (fun _ => none) (fun _ => none)
    ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]) := by
  unfold MpnCmpFrontEmit.cmpRtLprogOpt MpnCmpFrontEmit.cmpRtProgOpt
  change Option.map _ (compileLoop (Γouter := MpnCmpFrontEmit.Gouter)
    (accCTy := .memref MpnCmpFrontEmit.NR)
    (invCTys := [.memref MpnCmpFrontEmit.NU, .memref MpnCmpFrontEmit.NU, .sword 64]) .plain (.runtime _) _ _ _ _ _) = _
  erw [← compileLoopCont_ret_here]
  simp only [compileLoopCont]
  unfold rolledForLoopNRtCont
  split
  next u hu =>
    have : u = MpnCmpFrontDenote.cmpUpdate := Option.some.inj (hu.symm.trans MpnCmpFrontDenote.cmpUpdate_eq)
    subst this; rfl
  next hu => exact absurd (hu.symm.trans MpnCmpFrontDenote.cmpUpdate_eq) (by simp)

theorem cmpBaseNames :
    ComL.loopArgBaseNames 4 (fun _ => none) cmpCom 4 = some ("a0", ["a1", "a2"]) := by
  kernel_rfl

theorem cmpAccRegs : (ComL.loopAccRegs cmpCom 4).map regName = ["r4"] := by
  kernel_rfl

def cmpAliasLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r5"] "MOV:64" [.imm 1],
    .Lopn [.reg "L4_r6"] "SUB:64" [.reg "a3", .reg "L4_r5"],
    .Lopn [.reg "L4_r7"] "SHL:0:64" [.reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "SUB:64" [.reg "L4_r7", .reg "Lidx4"],
    .Lopn [.reg "L4_r9"] "SHL:0:64" [.reg "L4_r8"],
    .Lopn [.reg "L4_r10"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r11"] "SHL:0:64" [.reg "L4_r10"],
    .Lopn [.reg "L4_r12"] "LOADIDX" [.arrIdx "a1" "L4_r9" 8],
    .Lopn [.reg "L4_r13"] "LOADIDX" [.arrIdx "a2" "L4_r9" 8],
    .Lopn [.reg "L4_r14"] "LOADIDX" [.arrIdx "a0" "L4_r11" 8],
    .Lopn [.reg "L4_r15"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r16"] "XOR:64" [.reg "L4_r12", .reg "L4_r15"],
    .Lopn [.reg "L4_r17"] "AND:64" [.reg "L4_r16", .reg "L4_r13"],
    .Lopn [.reg "L4_r18"] "SHL:0:64" [.reg "L4_r17"],
    .Lopn [.reg "L4_r19"] "XOR:64" [.reg "L4_r12", .reg "L4_r13"],
    .Lopn [.reg "L4_r20"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r21"] "XOR:64" [.reg "L4_r19", .reg "L4_r20"],
    .Lopn [.reg "L4_r22"] "SUB:64" [.reg "L4_r12", .reg "L4_r13"],
    .Lopn [.reg "L4_r23"] "AND:64" [.reg "L4_r21", .reg "L4_r22"],
    .Lopn [.reg "L4_r24"] "SHL:0:64" [.reg "L4_r23"],
    .Lopn [.reg "L4_r25"] "XOR:64" [.reg "L4_r18", .reg "L4_r24"],
    .Lopn [.reg "L4_r26"] "AND:64" [.reg "L4_r18", .reg "L4_r24"],
    .Lopn [.reg "L4_r27"] "XOR:64" [.reg "L4_r25", .reg "L4_r26"],
    .Lopn [.reg "L4_r28"] "MOV:64" [.imm 63],
    .Lopn [.reg "L4_r29"] "SHR:63:64" [.reg "L4_r27"],
    .Lopn [.reg "L4_r30"] "SHL:0:64" [.reg "L4_r29"],
    .Lopn [.reg "L4_r31"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r32"] "XOR:64" [.reg "L4_r13", .reg "L4_r31"],
    .Lopn [.reg "L4_r33"] "AND:64" [.reg "L4_r32", .reg "L4_r12"],
    .Lopn [.reg "L4_r34"] "SHL:0:64" [.reg "L4_r33"],
    .Lopn [.reg "L4_r35"] "XOR:64" [.reg "L4_r13", .reg "L4_r12"],
    .Lopn [.reg "L4_r36"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r37"] "XOR:64" [.reg "L4_r35", .reg "L4_r36"],
    .Lopn [.reg "L4_r38"] "SUB:64" [.reg "L4_r13", .reg "L4_r12"],
    .Lopn [.reg "L4_r39"] "AND:64" [.reg "L4_r37", .reg "L4_r38"],
    .Lopn [.reg "L4_r40"] "SHL:0:64" [.reg "L4_r39"],
    .Lopn [.reg "L4_r41"] "XOR:64" [.reg "L4_r34", .reg "L4_r40"],
    .Lopn [.reg "L4_r42"] "AND:64" [.reg "L4_r34", .reg "L4_r40"],
    .Lopn [.reg "L4_r43"] "XOR:64" [.reg "L4_r41", .reg "L4_r42"],
    .Lopn [.reg "L4_r44"] "MOV:64" [.imm 63],
    .Lopn [.reg "L4_r45"] "SHR:63:64" [.reg "L4_r43"],
    .Lopn [.reg "L4_r46"] "SHL:0:64" [.reg "L4_r45"],
    .Lopn [.reg "L4_r47"] "SUB:64" [.reg "L4_r46", .reg "L4_r30"],
    .Lopn [.reg "L4_r48"] "SHL:0:64" [.reg "L4_r47"],
    .Lopn [.reg "L4_r49"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r50"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r51"] "XOR:64" [.reg "L4_r49", .reg "L4_r50"],
    .Lopn [.reg "L4_r52"] "AND:64" [.reg "L4_r51", .reg "L4_r14"],
    .Lopn [.reg "L4_r53"] "SHL:0:64" [.reg "L4_r52"],
    .Lopn [.reg "L4_r54"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r55"] "XOR:64" [.reg "L4_r54", .reg "L4_r14"],
    .Lopn [.reg "L4_r56"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r57"] "XOR:64" [.reg "L4_r55", .reg "L4_r56"],
    .Lopn [.reg "L4_r58"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r59"] "SUB:64" [.reg "L4_r58", .reg "L4_r14"],
    .Lopn [.reg "L4_r60"] "AND:64" [.reg "L4_r57", .reg "L4_r59"],
    .Lopn [.reg "L4_r61"] "SHL:0:64" [.reg "L4_r60"],
    .Lopn [.reg "L4_r62"] "XOR:64" [.reg "L4_r53", .reg "L4_r61"],
    .Lopn [.reg "L4_r63"] "AND:64" [.reg "L4_r53", .reg "L4_r61"],
    .Lopn [.reg "L4_r64"] "XOR:64" [.reg "L4_r62", .reg "L4_r63"],
    .Lopn [.reg "L4_r65"] "MOV:64" [.imm 63],
    .Lopn [.reg "L4_r66"] "SHR:63:64" [.reg "L4_r64"],
    .Lopn [.reg "L4_r67"] "SHL:0:64" [.reg "L4_r66"],
    .Lopn [.reg "L4_r68"] "MOV:64" [.imm 1],
    .Lopn [.reg "L4_r69"] "SUB:64" [.reg "L4_r67", .reg "L4_r68"],
    .Lopn [.reg "L4_r70"] "SHL:0:64" [.reg "L4_r69"],
    .Lopn [.reg "L4_r71"] "XOR:64" [.reg "L4_r48", .reg "L4_r14"],
    .Lopn [.reg "L4_r72"] "SHL:0:64" [.reg "L4_r71"],
    .Lopn [.reg "L4_r73"] "AND:64" [.reg "L4_r70", .reg "L4_r72"],
    .Lopn [.reg "L4_r74"] "XOR:64" [.reg "L4_r14", .reg "L4_r73"],
    .Lopn [.reg "L4_r75"] "SHL:0:64" [.reg "L4_r74"],
    .Lopn [.reg "L4_r76"] "STOREIDX" [.arrIdx "a0" "L4_r11" 8, .reg "L4_r75"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "L4_r76"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem cmpAlias_eq :
    aliasRegBody "r4" "a0" (ComL.toLfundef cmpCom (fun _ => none)).lfd_body = cmpAliasLit := by
  kernel_rfl

theorem cmpChain_eq :
    arrChainAlias cmpAliasLit = (({} : Std.HashMap String String).insert "L4_r76" "a0") := by
  simp [arrChainAlias, cmpAliasLit, isMemStore, stripWidthTag_loadidx, stripWidthTag_storeidx]

def cmpCanonLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r5"] "MOV:64" [.imm 1],
    .Lopn [.reg "L4_r6"] "SUB:64" [.reg "a3", .reg "L4_r5"],
    .Lopn [.reg "L4_r7"] "SHL:0:64" [.reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "SUB:64" [.reg "L4_r7", .reg "Lidx4"],
    .Lopn [.reg "L4_r9"] "SHL:0:64" [.reg "L4_r8"],
    .Lopn [.reg "L4_r10"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r11"] "SHL:0:64" [.reg "L4_r10"],
    .Lopn [.reg "L4_r12"] "LOADIDX" [.arrIdx "a1" "L4_r9" 8],
    .Lopn [.reg "L4_r13"] "LOADIDX" [.arrIdx "a2" "L4_r9" 8],
    .Lopn [.reg "L4_r14"] "LOADIDX" [.arrIdx "a0" "L4_r11" 8],
    .Lopn [.reg "L4_r15"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r16"] "XOR:64" [.reg "L4_r12", .reg "L4_r15"],
    .Lopn [.reg "L4_r17"] "AND:64" [.reg "L4_r16", .reg "L4_r13"],
    .Lopn [.reg "L4_r18"] "SHL:0:64" [.reg "L4_r17"],
    .Lopn [.reg "L4_r19"] "XOR:64" [.reg "L4_r12", .reg "L4_r13"],
    .Lopn [.reg "L4_r20"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r21"] "XOR:64" [.reg "L4_r19", .reg "L4_r20"],
    .Lopn [.reg "L4_r22"] "SUB:64" [.reg "L4_r12", .reg "L4_r13"],
    .Lopn [.reg "L4_r23"] "AND:64" [.reg "L4_r21", .reg "L4_r22"],
    .Lopn [.reg "L4_r24"] "SHL:0:64" [.reg "L4_r23"],
    .Lopn [.reg "L4_r25"] "XOR:64" [.reg "L4_r18", .reg "L4_r24"],
    .Lopn [.reg "L4_r26"] "AND:64" [.reg "L4_r18", .reg "L4_r24"],
    .Lopn [.reg "L4_r27"] "XOR:64" [.reg "L4_r25", .reg "L4_r26"],
    .Lopn [.reg "L4_r28"] "MOV:64" [.imm 63],
    .Lopn [.reg "L4_r29"] "SHR:63:64" [.reg "L4_r27"],
    .Lopn [.reg "L4_r30"] "SHL:0:64" [.reg "L4_r29"],
    .Lopn [.reg "L4_r31"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r32"] "XOR:64" [.reg "L4_r13", .reg "L4_r31"],
    .Lopn [.reg "L4_r33"] "AND:64" [.reg "L4_r32", .reg "L4_r12"],
    .Lopn [.reg "L4_r34"] "SHL:0:64" [.reg "L4_r33"],
    .Lopn [.reg "L4_r35"] "XOR:64" [.reg "L4_r13", .reg "L4_r12"],
    .Lopn [.reg "L4_r36"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r37"] "XOR:64" [.reg "L4_r35", .reg "L4_r36"],
    .Lopn [.reg "L4_r38"] "SUB:64" [.reg "L4_r13", .reg "L4_r12"],
    .Lopn [.reg "L4_r39"] "AND:64" [.reg "L4_r37", .reg "L4_r38"],
    .Lopn [.reg "L4_r40"] "SHL:0:64" [.reg "L4_r39"],
    .Lopn [.reg "L4_r41"] "XOR:64" [.reg "L4_r34", .reg "L4_r40"],
    .Lopn [.reg "L4_r42"] "AND:64" [.reg "L4_r34", .reg "L4_r40"],
    .Lopn [.reg "L4_r43"] "XOR:64" [.reg "L4_r41", .reg "L4_r42"],
    .Lopn [.reg "L4_r44"] "MOV:64" [.imm 63],
    .Lopn [.reg "L4_r45"] "SHR:63:64" [.reg "L4_r43"],
    .Lopn [.reg "L4_r46"] "SHL:0:64" [.reg "L4_r45"],
    .Lopn [.reg "L4_r47"] "SUB:64" [.reg "L4_r46", .reg "L4_r30"],
    .Lopn [.reg "L4_r48"] "SHL:0:64" [.reg "L4_r47"],
    .Lopn [.reg "L4_r49"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r50"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r51"] "XOR:64" [.reg "L4_r49", .reg "L4_r50"],
    .Lopn [.reg "L4_r52"] "AND:64" [.reg "L4_r51", .reg "L4_r14"],
    .Lopn [.reg "L4_r53"] "SHL:0:64" [.reg "L4_r52"],
    .Lopn [.reg "L4_r54"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r55"] "XOR:64" [.reg "L4_r54", .reg "L4_r14"],
    .Lopn [.reg "L4_r56"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "L4_r57"] "XOR:64" [.reg "L4_r55", .reg "L4_r56"],
    .Lopn [.reg "L4_r58"] "MOV:64" [.imm 0],
    .Lopn [.reg "L4_r59"] "SUB:64" [.reg "L4_r58", .reg "L4_r14"],
    .Lopn [.reg "L4_r60"] "AND:64" [.reg "L4_r57", .reg "L4_r59"],
    .Lopn [.reg "L4_r61"] "SHL:0:64" [.reg "L4_r60"],
    .Lopn [.reg "L4_r62"] "XOR:64" [.reg "L4_r53", .reg "L4_r61"],
    .Lopn [.reg "L4_r63"] "AND:64" [.reg "L4_r53", .reg "L4_r61"],
    .Lopn [.reg "L4_r64"] "XOR:64" [.reg "L4_r62", .reg "L4_r63"],
    .Lopn [.reg "L4_r65"] "MOV:64" [.imm 63],
    .Lopn [.reg "L4_r66"] "SHR:63:64" [.reg "L4_r64"],
    .Lopn [.reg "L4_r67"] "SHL:0:64" [.reg "L4_r66"],
    .Lopn [.reg "L4_r68"] "MOV:64" [.imm 1],
    .Lopn [.reg "L4_r69"] "SUB:64" [.reg "L4_r67", .reg "L4_r68"],
    .Lopn [.reg "L4_r70"] "SHL:0:64" [.reg "L4_r69"],
    .Lopn [.reg "L4_r71"] "XOR:64" [.reg "L4_r48", .reg "L4_r14"],
    .Lopn [.reg "L4_r72"] "SHL:0:64" [.reg "L4_r71"],
    .Lopn [.reg "L4_r73"] "AND:64" [.reg "L4_r70", .reg "L4_r72"],
    .Lopn [.reg "L4_r74"] "XOR:64" [.reg "L4_r14", .reg "L4_r73"],
    .Lopn [.reg "L4_r75"] "SHL:0:64" [.reg "L4_r74"],
    .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L4_r11" 8, .reg "L4_r75"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem cmpCanon_eq : canonicalizeMemrefThread cmpAliasLit = cmpCanonLit := by
  unfold canonicalizeMemrefThread
  rw [cmpChain_eq]
  simp [Std.HashMap.isEmpty_insert, cmpAliasLit, cmpCanonLit, canonMemrefOperand,
    canonMemrefName, Std.HashMap.getD_insert]

/-- The physical body of the shipped `mpn_cmp_ct`. -/
def cmpPhysLit : Lcmd := ([
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
    .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.RSI"],
    .Lopn [.reg "k.1"] "MOVQ" [.reg "R15"],
    .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.RDX"],
    .Lopn [.reg "k.0"] "MOVQ" [.reg "R15"],
    .Lopn [.reg "RSI"] "MOVQ" [.reg "qsave.RCX"],
    .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
    .Lopn [.reg "RAX"] "MOV:64" [.imm 0],
    .Lopn [.reg "RDI"] "MOV:64" [.reg "RSI"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "RBP"] "MOV:64" [.imm 1],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RSI"],
    .Lopn [.reg "R8"] "SUB:64" [.reg "R8", .reg "RBP"],
    .Lopn [.reg "RBP"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "R8"] "SUB:64" [.reg "R8", .reg "RAX"],
    .Lopn [.reg "RBP"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R8"] "MOV:64" [.imm 0],
    .Lopn [.reg "R9"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
    .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RBP" 8],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDX"],
    .Lopn [.reg "R10"] "LOADIDX" [.arrIdx "R14" "RBP" 8],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RBP"] "LOADIDX" [.arrIdx "R14" "R9" 8],
    .Lopn [.reg "R11"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "R12"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "R12"] "XOR:64" [.reg "R12", .reg "R11"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R12"],
    .Lopn [.reg "R11"] "AND:64" [.reg "R11", .reg "R10"],
    .Lopn [.reg "R12"] "SHL:0:64" [.reg "R11"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "R10"],
    .Lopn [.reg "R13"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "RDX"] "MOV:64" [.reg "R11"],
    .Lopn [.reg "RDX"] "XOR:64" [.reg "RDX", .reg "R13"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "R11"] "SUB:64" [.reg "R11", .reg "R10"],
    .Lopn [.reg "R13"] "MOV:64" [.reg "RDX"],
    .Lopn [.reg "R13"] "AND:64" [.reg "R13", .reg "R11"],
    .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R13"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R12"],
    .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "RDX"],
    .Lopn [.reg "R13"] "MOV:64" [.reg "R12"],
    .Lopn [.reg "R13"] "AND:64" [.reg "R13", .reg "RDX"],
    .Lopn [.reg "RDX"] "MOV:64" [.reg "R11"],
    .Lopn [.reg "RDX"] "XOR:64" [.reg "RDX", .reg "R13"],
    .Lopn [.reg "R11"] "MOV:64" [.imm 63],
    .Lopn [.reg "R11"] "SHR:63:64" [.reg "RDX"],
    .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R11"],
    .Lopn [.reg "R11"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "R12"] "MOV:64" [.reg "R10"],
    .Lopn [.reg "R12"] "XOR:64" [.reg "R12", .reg "R11"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R12"],
    .Lopn [.reg "R11"] "AND:64" [.reg "R11", .reg "R8"],
    .Lopn [.reg "R12"] "SHL:0:64" [.reg "R11"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R10"],
    .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "R8"],
    .Lopn [.reg "R13"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "RCX"] "MOV:64" [.reg "R11"],
    .Lopn [.reg "RCX"] "XOR:64" [.reg "RCX", .reg "R13"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R10"],
    .Lopn [.reg "R11"] "SUB:64" [.reg "R11", .reg "R8"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RCX"],
    .Lopn [.reg "R8"] "AND:64" [.reg "R8", .reg "R11"],
    .Lopn [.reg "RCX"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "R12"],
    .Lopn [.reg "R8"] "XOR:64" [.reg "R8", .reg "RCX"],
    .Lopn [.reg "R10"] "MOV:64" [.reg "R12"],
    .Lopn [.reg "R10"] "AND:64" [.reg "R10", .reg "RCX"],
    .Lopn [.reg "RCX"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "RCX"] "XOR:64" [.reg "RCX", .reg "R10"],
    .Lopn [.reg "R8"] "MOV:64" [.imm 63],
    .Lopn [.reg "R8"] "SHR:63:64" [.reg "RCX"],
    .Lopn [.reg "RCX"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RCX"],
    .Lopn [.reg "R8"] "SUB:64" [.reg "R8", .reg "RDX"],
    .Lopn [.reg "RCX"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "RDX"] "MOV:64" [.imm 0],
    .Lopn [.reg "R8"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "R10"] "MOV:64" [.reg "RDX"],
    .Lopn [.reg "R10"] "XOR:64" [.reg "R10", .reg "R8"],
    .Lopn [.reg "RDX"] "MOV:64" [.reg "R10"],
    .Lopn [.reg "RDX"] "AND:64" [.reg "RDX", .reg "RBP"],
    .Lopn [.reg "R8"] "SHL:0:64" [.reg "RDX"],
    .Lopn [.reg "RDX"] "MOV:64" [.imm 0],
    .Lopn [.reg "R10"] "MOV:64" [.reg "RDX"],
    .Lopn [.reg "R10"] "XOR:64" [.reg "R10", .reg "RBP"],
    .Lopn [.reg "RDX"] "MOV:64" [.imm 18446744073709551615],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R10"],
    .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "RDX"],
    .Lopn [.reg "RDX"] "MOV:64" [.imm 0],
    .Lopn [.reg "R10"] "MOV:64" [.reg "RDX"],
    .Lopn [.reg "R10"] "SUB:64" [.reg "R10", .reg "RBP"],
    .Lopn [.reg "RDX"] "MOV:64" [.reg "R11"],
    .Lopn [.reg "RDX"] "AND:64" [.reg "RDX", .reg "R10"],
    .Lopn [.reg "R10"] "SHL:0:64" [.reg "RDX"],
    .Lopn [.reg "RDX"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "RDX"] "XOR:64" [.reg "RDX", .reg "R10"],
    .Lopn [.reg "R11"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "R11"] "AND:64" [.reg "R11", .reg "R10"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RDX"],
    .Lopn [.reg "R8"] "XOR:64" [.reg "R8", .reg "R11"],
    .Lopn [.reg "RDX"] "MOV:64" [.imm 63],
    .Lopn [.reg "RDX"] "SHR:63:64" [.reg "R8"],
    .Lopn [.reg "R8"] "SHL:0:64" [.reg "RDX"],
    .Lopn [.reg "RDX"] "MOV:64" [.imm 1],
    .Lopn [.reg "R10"] "MOV:64" [.reg "R8"],
    .Lopn [.reg "R10"] "SUB:64" [.reg "R10", .reg "RDX"],
    .Lopn [.reg "RDX"] "SHL:0:64" [.reg "R10"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RCX"],
    .Lopn [.reg "R8"] "XOR:64" [.reg "R8", .reg "RBP"],
    .Lopn [.reg "RCX"] "SHL:0:64" [.reg "R8"],
    .Lopn [.reg "R8"] "MOV:64" [.reg "RDX"],
    .Lopn [.reg "R8"] "AND:64" [.reg "R8", .reg "RCX"],
    .Lopn [.reg "RCX"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "RCX"] "XOR:64" [.reg "RCX", .reg "R8"],
    .Lopn [.reg "RDX"] "SHL:0:64" [.reg "RCX"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "R9" 8, .reg "RDX"],
    .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
    .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1],
    .Lopn [.reg "RDI"] "SUB:64" [.reg "RDI", .imm 1],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "k.1"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "k.0"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RSI"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"],
    .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"],
    .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"],
    .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"],
    .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"],
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem cmpPhysAbiOfCanon_eq :
    (physAbiOfCanon (ComL.toLfundef cmpCom (fun _ => none)) cmpCanonLit "a0" ["a1", "a2"]
      (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).1.lfd_body
      = cmpPhysLit := by
  kernel_rfl

/-- **The function body of the shipped `mpn_cmp_ct`** is `cmpPhysLit`. -/
theorem cmpPhysAbi_eq : (ComL.toLfundefPhysAbi cmpCom (argName 0) [argName 1, argName 2]
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).lfd_body
      = cmpPhysLit := by
  rw [ComL.toLfundefPhysAbi_eq_ofVirt]
  have h4 : (MpnCmpFrontEmit.Gouter).length = 4 := rfl
  simp only [h4, cmpBaseNames, cmpAccRegs]
  unfold lfundefPhysAbiOfVirt
  rw [ofVirtCert_eq_physAbiOfCanon]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [cmpAlias_eq, cmpCanon_eq]
  exact cmpPhysAbiOfCanon_eq

/-- **The object bytes of the linked `mpn_cmp_ct`** are the ELF wrapping of the function bytes
    of `cmpPhysLit`. -/
theorem cmpObjBytes_eq {bs : List (BitVec 8)}
    (h : MpnRuntimeBytesEmit.objBytes (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct") = some bs) :
    bs = ElfObject.buildElfObjectMulti
      [{ name := "mpn_cmp_ct", text := encodeLfundefBytes cmpPhysLit }] := by
  rw [MpnRuntimeBytesEmit.objBytes, cmpLprog_eq, Option.bind_some] at h
  rw [LprogBytesDecode.encodeLprogChecked_single rfl h, cmpPhysAbi_eq]

def cmpDecPre : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-80)
  , .storeMem "%rsp" 72 (.reg "%rdi")
  , .storeMem "%rsp" 64 (.reg "%rsi")
  , .storeMem "%rsp" 56 (.reg "%rbx")
  , .storeMem "%rsp" 48 (.reg "%rbp")
  , .storeMem "%rsp" 40 (.reg "%r12")
  , .storeMem "%rsp" 32 (.reg "%r13")
  , .storeMem "%rsp" 24 (.reg "%r14")
  , .storeMem "%rsp" 16 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx")
  , .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 72
  , .loadMem "%r15" "%rsp" 64
  , .storeMem "%rsp" 0 (.reg "%r15")
  , .loadMem "%r15" "%rsp" (-8)
  , .storeMem "%rsp" 8 (.reg "%r15")
  , .loadMem "%rsi" "%rsp" (-16)
  , .mov "%rbx" (.reg "%rbx")
  , .mov "%rax" (.imm 0)
  , .mov "%rdi" (.reg "%rsi") ]

def cmpDecLoopBody : List (JInstr 64) :=
  [ .mov "%rbp" (.imm 1)
  , .mov "%r8" (.reg "%rsi")
  , .sub "%r8" (.reg "%rbp")
  , .mov "%rbp" (.reg "%r8")
  , .mov "%r8" (.reg "%rbp")
  , .sub "%r8" (.reg "%rax")
  , .mov "%rbp" (.reg "%r8")
  , .mov "%r8" (.imm 0)
  , .mov "%r9" (.reg "%r8")
  , .loadMem "%r14" "%rsp" 64
  , .loadMemIdx "%r8" "%r14" "%rbp" 8
  , .loadMem "%r14" "%rsp" (-8)
  , .loadMemIdx "%r10" "%r14" "%rbp" 8
  , .loadMem "%r14" "%rsp" 72
  , .loadMemIdx "%rbp" "%r14" "%r9" 8
  , .mov "%r11" (.imm 18446744073709551615)
  , .mov "%r12" (.reg "%r8")
  , .xor_ "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r12")
  , .and_ "%r11" (.reg "%r10")
  , .mov "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r8")
  , .xor_ "%r11" (.reg "%r10")
  , .mov "%r13" (.imm 18446744073709551615)
  , .mov "%rdx" (.reg "%r11")
  , .xor_ "%rdx" (.reg "%r13")
  , .mov "%r11" (.reg "%r8")
  , .sub "%r11" (.reg "%r10")
  , .mov "%r13" (.reg "%rdx")
  , .and_ "%r13" (.reg "%r11")
  , .mov "%rdx" (.reg "%r13")
  , .mov "%r11" (.reg "%r12")
  , .xor_ "%r11" (.reg "%rdx")
  , .mov "%r13" (.reg "%r12")
  , .and_ "%r13" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r11")
  , .xor_ "%rdx" (.reg "%r13")
  , .mov "%r11" (.imm 63)
  , .mov "%r11" (.reg "%rdx")
  , .shr "%r11" (.imm 63)
  , .mov "%rdx" (.reg "%r11")
  , .mov "%r11" (.imm 18446744073709551615)
  , .mov "%r12" (.reg "%r10")
  , .xor_ "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r12")
  , .and_ "%r11" (.reg "%r8")
  , .mov "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r10")
  , .xor_ "%r11" (.reg "%r8")
  , .mov "%r13" (.imm 18446744073709551615)
  , .mov "%rcx" (.reg "%r11")
  , .xor_ "%rcx" (.reg "%r13")
  , .mov "%r11" (.reg "%r10")
  , .sub "%r11" (.reg "%r8")
  , .mov "%r8" (.reg "%rcx")
  , .and_ "%r8" (.reg "%r11")
  , .mov "%rcx" (.reg "%r8")
  , .mov "%r8" (.reg "%r12")
  , .xor_ "%r8" (.reg "%rcx")
  , .mov "%r10" (.reg "%r12")
  , .and_ "%r10" (.reg "%rcx")
  , .mov "%rcx" (.reg "%r8")
  , .xor_ "%rcx" (.reg "%r10")
  , .mov "%r8" (.imm 63)
  , .mov "%r8" (.reg "%rcx")
  , .shr "%r8" (.imm 63)
  , .mov "%rcx" (.reg "%r8")
  , .mov "%r8" (.reg "%rcx")
  , .sub "%r8" (.reg "%rdx")
  , .mov "%rcx" (.reg "%r8")
  , .mov "%rdx" (.imm 0)
  , .mov "%r8" (.imm 18446744073709551615)
  , .mov "%r10" (.reg "%rdx")
  , .xor_ "%r10" (.reg "%r8")
  , .mov "%rdx" (.reg "%r10")
  , .and_ "%rdx" (.reg "%rbp")
  , .mov "%r8" (.reg "%rdx")
  , .mov "%rdx" (.imm 0)
  , .mov "%r10" (.reg "%rdx")
  , .xor_ "%r10" (.reg "%rbp")
  , .mov "%rdx" (.imm 18446744073709551615)
  , .mov "%r11" (.reg "%r10")
  , .xor_ "%r11" (.reg "%rdx")
  , .mov "%rdx" (.imm 0)
  , .mov "%r10" (.reg "%rdx")
  , .sub "%r10" (.reg "%rbp")
  , .mov "%rdx" (.reg "%r11")
  , .and_ "%rdx" (.reg "%r10")
  , .mov "%r10" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r8")
  , .xor_ "%rdx" (.reg "%r10")
  , .mov "%r11" (.reg "%r8")
  , .and_ "%r11" (.reg "%r10")
  , .mov "%r8" (.reg "%rdx")
  , .xor_ "%r8" (.reg "%r11")
  , .mov "%rdx" (.imm 63)
  , .mov "%rdx" (.reg "%r8")
  , .shr "%rdx" (.imm 63)
  , .mov "%r8" (.reg "%rdx")
  , .mov "%rdx" (.imm 1)
  , .mov "%r10" (.reg "%r8")
  , .sub "%r10" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r10")
  , .mov "%r8" (.reg "%rcx")
  , .xor_ "%r8" (.reg "%rbp")
  , .mov "%rcx" (.reg "%r8")
  , .mov "%r8" (.reg "%rdx")
  , .and_ "%r8" (.reg "%rcx")
  , .mov "%rcx" (.reg "%rbp")
  , .xor_ "%rcx" (.reg "%r8")
  , .mov "%rdx" (.reg "%rcx")
  , .loadMem "%r14" "%rsp" 72
  , .storeMemIdx "%r14" "%r9" 8 (.reg "%rdx")
  , .mov "%rbx" (.reg "%rbx")
  , .add "%rax" (.imm 1)
  , .sub "%rdi" (.imm 1)
  , .cmpMem "%rdi" "%rsp" 0
  , .cmpMem "%rdi" "%rsp" 8
  , .cmp "%rdi" (.reg "%rsi") ]

def cmpDecLoop : XLoop 64 := { top := 4, ctr := "%rdi", body := cmpDecLoopBody }

def cmpDecPost : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 56
  , .loadMem "%rbp" "%rsp" 48
  , .loadMem "%r12" "%rsp" 40
  , .loadMem "%r13" "%rsp" 32
  , .loadMem "%r14" "%rsp" 24
  , .loadMem "%r15" "%rsp" 16
  , .lea "%rsp" "%rsp" "%rsp" 0 80 ]

/-- **The decoded shipped `mpn_cmp_ct`.** -/
theorem cmpPhysLit_decode :
    decodeLprog (encodeLfundefBytes cmpPhysLit)
      = some (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) := by
  kernel_rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
