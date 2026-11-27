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
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopBytesEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped

@[expose] public section

set_option autoImplicit false

/-!
# The exporter terms of the shipped bitwise kernels, without compiled evaluation

`MpnLoopBytesEmit.kernels` maps the linked symbols `mpn_and_n_loop_owned`,
`mpn_ior_n_loop_owned` and `mpn_xor_n_loop_owned` to `MpnLoopFrontEmit.andLprog ()`,
`iorLprog ()` and `xorLprog ()`. This module computes each program's one function body as a
literal `Lcmd` and the decoded layout of the bytes `encodeLfundefBytes` lays down for it, with
the kernel (`kernel_rfl`) and rewriting only; no `native_decide`.

## The route

* The front's `Option` is split at `JasminLsemExportCanonLogicShipped.binAndUpdate`, the body
  the canonical-node theorems are about, so the program is
  `ComL.toLprogPhysAbi andCom …` with `andCom` the `forLoopNRt` node over `binAndUpdate`
  (`andLprog_eq`).
* The exporter is `lfundefPhysAbiOfVirtCert` at the virtual export. The kernel evaluates every
  stage of it except `canonicalizeMemrefThread`, whose alias map is a `Std.HashMap String String`
  keyed through the opaque `String.hash`; that stage is computed by rewriting with the
  `Std.HashMap` lemmas (`andChain_eq`, `andCanon_eq`). The rest of the exporter, copied as
  `physAbiOfCanon` with the canonicalised body as an input (`ofVirtCert_eq_physAbiOfCanon`,
  by `rfl`), is evaluated by the kernel at the canonical literal (`andPhysAbiOfCanon_eq`).
* The kernel unfolds `String.startsWith`, `Array.range` and `kernelMergeSort` only with the
  `import all` lines of the header; without them those applications have no normal form in a
  `module`.

## Main results

* `andLprog_eq` — the shipped program is the physical-ABI export of `andCom`.
* `andPhysAbi_eq` — its function body is `andPhysLit`.
* `andLprog_funcs` — `andLprog ()` is one function `mpn_and_n_loop_owned` with body
  `andPhysLit`.
* `andObjBytes_eq` — the object bytes `MpnLoopBytesEmit.objBytes (andLprog ())` are the ELF
  wrapping of `encodeLfundefBytes andPhysLit`.
* `andPhysLit_decode` — those function bytes decode to
  `nodeLayout andDecPre andDecLoop andDecPost`.
* `iorLprog_eq`, `iorPhysAbi_eq`, `iorObjBytes_eq`, `iorPhysLit_decode` and the `xor`
  counterparts — the same four facts for `mpn_ior_n_loop_owned` and `mpn_xor_n_loop_owned`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped (binAndUpdate)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes encodeLprogChecked)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)

/-! ## 1. The exporter after canonicalisation -/

/-- `lfundefPhysAbiOfVirtCert` with the canonicalised body `canon` as an input in place of
    `canonicalizeMemrefThread (accRegs.foldl (fun b r => aliasRegBody r outArg' b)
    virt0.lfd_body)`; every other stage is the exporter's text. -/
def physAbiOfCanon (virt0 : Lfundef) (canon : Lcmd) (outArg' : String) (inArgs' : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (abi : IsaAbi := x86Abi)
    (posBind : Bool := false) (frameArrs : List (String × Nat × Nat) := [])
    (splitCfg : Lcmd → Option SplitCfg := fun _ => none) :
    Lfundef × List (String × String) :=
  let livePin : Lcmd :=
    if abiArgs.length ≥ 4 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  let body1 := livePin ++ canon
  let virt := { virt0 with lfd_body := body1 }
  let tbl := physTableOut virt.lfd_body [] (abi := abi) (split := splitCfg virt.lfd_body)
  let prologue := buildPrologue virt tbl (fun _ => none) ++ extraInputSaves abiArgs
  let argMat := buildArgPtrMaterialize virt tbl abiArgs (fun _ => none) abi
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := sibIdxOracle (fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm) virt.lfd_body
  let argAbi : List (String × String) := argBasePairs posBind outArg' inArgs' abiArgs
  let reloadPairs : List (String × String) :=
    faReloadPairs (fun A => physNameForBody virt.lfd_body tbl A abi) frameArrs ++
    argAbi.filterMap (fun (argNm, abiReg) =>
      match abiSlotOfExt abiReg with
      | some saveName =>
          some (physNameForBody virt.lfd_body tbl argNm abi, saveName)
      | none => none)
  let memrefBaseReload : String → Option String :=
    fun base => (reloadPairs.find? (fun p => p.1 == base)).map Prod.snd
  let callArgBaseReload : List (String × String) :=
    (abiArgs.zipIdx).filterMap (fun (abiReg, j) =>
      match abiSaveOfExt abiReg with
      | some saveName =>
          let phys := physNameForBody virt.lfd_body tbl (argName j) abi
          if isCallerSavedAllocGPR phys then some (phys, saveName) else none
      | none => none)
  let bodyWithReload := reloadArrImmBody memrefBaseReload
    ((match splitCfg virt.lfd_body with
      | some cfg => physBodySplit shiftImm' virt.lfd_body cfg memrefBaseReload abi
      | none => physBodyWithStores shiftImm' virt.lfd_body
          (fun _ => none) reloadScratch2 [] reloadScratch2 0 memrefBaseReload
          callArgBaseReload (abi := abi)).filter
      (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true))
  let bodyWithRestore := insertEpilogue bodyWithReload calleeSaveRestoreEpilogue
  ({ virt with
    lfd_body := prologue ++ argMat ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := [] }, allocCertOf virt.lfd_body (straightCallComposeTable virt.lfd_body tbl) abi)

/-- The exporter is `physAbiOfCanon` at its canonicalised body. -/
theorem ofVirtCert_eq_physAbiOfCanon (virt0 : Lfundef) (o : String) (ins accRegs : List String)
    (abiArgs : List String) (abiTyin : List Nat) :
    (lfundefPhysAbiOfVirtCert virt0 o ins accRegs (fun _ => none) abiArgs abiTyin).1
      = (physAbiOfCanon virt0 (canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r o b) virt0.lfd_body)) o ins
          (fun _ => none) abiArgs abiTyin).1 := rfl

/-! ## 2. The shipped program as an export of the canonical-node body -/

/-- The front compiles the shipped limb body to `binAndUpdate`. -/
theorem andFront_eq :
    frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody .SAnd)
      = some binAndUpdate := (Option.some_get _).symm

/-- The runtime-trip loop node of `andLprog` over `binAndUpdate`: count in slot `0`, the
    accumulator seeded from slot `3`, the invariants from slots `2` and `1`. -/
noncomputable def andCom : ComL ΓouterBin (mapTy (CryptoTy.memref N)) :=
  ComL.forLoopNRt binAndUpdate .here (.there (.there (.there .here)))
    (.cons (.there (.there .here)) (.cons (.there .here) .nil)) (.ret .here)

/-- **The shipped program is the physical-ABI export of `andCom`.** -/
theorem andLprog_eq : andLprog () = some (ComL.toLprogPhysAbi andCom "mpn_and_n_loop_owned"
    (argName 0) [argName 1, argName 2] (fun _ => none) (fun _ => none)
    ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]) := by
  unfold andLprog binLprog rolledForLoopNRtLprog rolledForLoopNRt rolledForLoopNRtCont
  split
  next u hu =>
    have : u = binAndUpdate := Option.some.inj (hu.symm.trans andFront_eq)
    subst this; rfl
  next hu => exact absurd (hu.symm.trans andFront_eq) (by simp)

/-! ## 3. The stages of the exporter at `andCom` -/

/-- The loop node's base names and accumulator. -/
theorem andBaseNames :
    ComL.loopArgBaseNames 4 (fun _ => none) andCom 4 = some ("a0", ["a1", "a2"]) := by
  kernel_rfl

theorem andAccRegs : (ComL.loopAccRegs andCom 4).map regName = ["r4"] := by
  kernel_rfl

/-- The virtual body with the accumulator `r4` aliased onto `a0`. -/
def andAliasLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "SHL:0:64" [.reg "Lidx4"],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8],
    .Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a2" "L4_r4" 8],
    .Lopn [.reg "L4_r7"] "AND:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "SHL:0:64" [.reg "L4_r7"],
    .Lopn [.reg "L4_r9"] "STOREIDX" [.arrIdx "a0" "L4_r4" 8, .reg "L4_r8"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "L4_r9"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem andAlias_eq :
    aliasRegBody "r4" "a0" (ComL.toLfundef andCom (fun _ => none)).lfd_body = andAliasLit := by
  kernel_rfl

theorem stripWidthTag_loadidx : stripWidthTag "LOADIDX" = "LOADIDX" := by kernel_rfl
theorem stripWidthTag_storeidx : stripWidthTag "STOREIDX" = "STOREIDX" := by kernel_rfl

/-- The alias map of the store thread: the store result `L4_r9` resolves to `a0`. -/
theorem andChain_eq :
    arrChainAlias andAliasLit = (({} : Std.HashMap String String).insert "L4_r9" "a0") := by
  simp [arrChainAlias, andAliasLit, isMemStore, stripWidthTag_loadidx, stripWidthTag_storeidx]

/-- The canonicalised body. -/
def andCanonLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "SHL:0:64" [.reg "Lidx4"],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8],
    .Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a2" "L4_r4" 8],
    .Lopn [.reg "L4_r7"] "AND:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "SHL:0:64" [.reg "L4_r7"],
    .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L4_r4" 8, .reg "L4_r8"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

/-- **The canonicalisation stage**, by rewriting through the alias map. -/
theorem andCanon_eq : canonicalizeMemrefThread andAliasLit = andCanonLit := by
  unfold canonicalizeMemrefThread
  rw [andChain_eq]
  simp [Std.HashMap.isEmpty_insert, andAliasLit, andCanonLit, canonMemrefOperand,
    canonMemrefName, Std.HashMap.getD_insert]

/-- The physical body of the shipped `mpn_and_n_loop_owned`: the callee-saved and argument
    saves, the argument moves and loop seeds, the zero-trip guard, the loop body with the
    base reloads through `R14`, the back-edge and the restores. -/
def andPhysLit : Lcmd := ([
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
    .Lopn [.reg "RDI"] "MOV:64" [.reg "RSI"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "RSI"] "SHL:0:64" [.reg "RAX"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
    .Lopn [.reg "RBP"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDX"],
    .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
    .Lopn [.reg "R9"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "R9"] "AND:64" [.reg "R9", .reg "R8"],
    .Lopn [.reg "RBP"] "SHL:0:64" [.reg "R9"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "RBP"],
    .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
    .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1],
    .Lopn [.reg "RDI"] "SUB:64" [.reg "RDI", .imm 1],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RCX"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RDX"],
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

/-- The exporter after canonicalisation, evaluated by the kernel. -/
theorem andPhysAbiOfCanon_eq :
    (physAbiOfCanon (ComL.toLfundef andCom (fun _ => none)) andCanonLit "a0" ["a1", "a2"]
      (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).1.lfd_body
      = andPhysLit := by
  kernel_rfl

/-- **The function body of the shipped `mpn_and_n_loop_owned`** is `andPhysLit`. -/
theorem andPhysAbi_eq : (ComL.toLfundefPhysAbi andCom (argName 0) [argName 1, argName 2]
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).lfd_body
      = andPhysLit := by
  rw [ComL.toLfundefPhysAbi_eq_ofVirt]
  have h4 : ΓouterBin.length = 4 := rfl
  simp only [h4, andBaseNames, andAccRegs]
  unfold lfundefPhysAbiOfVirt
  rw [ofVirtCert_eq_physAbiOfCanon]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [andAlias_eq, andCanon_eq]
  exact andPhysAbiOfCanon_eq

/-- **The shipped program is one function `mpn_and_n_loop_owned` with body `andPhysLit`.** -/
theorem andLprog_funcs :
    (andLprog ()).map (fun p => p.lp_funcs.map (fun q => (q.1, q.2.lfd_body)))
      = some [("mpn_and_n_loop_owned", andPhysLit)] := by
  rw [andLprog_eq, Option.map_some, ← andPhysAbi_eq]
  rfl

/-! ## 4. The object bytes and their decoding -/

/-- **The object bytes of the linked `mpn_and_n_loop_owned`** are the ELF wrapping of the
    function bytes of `andPhysLit`. -/
theorem andObjBytes_eq {bs : List (BitVec 8)}
    (h : MpnLoopBytesEmit.objBytes (andLprog ()) = some bs) :
    bs = ElfObject.buildElfObjectMulti
      [{ name := "mpn_and_n_loop_owned", text := encodeLfundefBytes andPhysLit }] := by
  rw [MpnLoopBytesEmit.objBytes, andLprog_eq, Option.bind_some] at h
  rw [LprogBytesDecode.encodeLprogChecked_single rfl h, andPhysAbi_eq]

/-- The decoded prologue: the frame `leaq`, the saves of the argument and callee-saved
    registers, the argument moves and the loop seeds, ending with the count in `%rdi`. -/
def andDecPre : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-64)
  , .storeMem "%rsp" 56 (.reg "%rdi"), .storeMem "%rsp" 48 (.reg "%rsi")
  , .storeMem "%rsp" 40 (.reg "%rbx"), .storeMem "%rsp" 32 (.reg "%rbp")
  , .storeMem "%rsp" 24 (.reg "%r12"), .storeMem "%rsp" 16 (.reg "%r13")
  , .storeMem "%rsp" 8 (.reg "%r14"), .storeMem "%rsp" 0 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx"), .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 56, .loadMem "%rcx" "%rsp" 48, .loadMem "%rsi" "%rsp" (-16)
  , .mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rsi") ]

/-- The decoded loop body: the index copy, the two limb loads through `%r14` reloaded from
    the frame, the conjunction, the store, the feedback copy, the index and counter updates
    and the two invariant touches. -/
def andDecLoopBody : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rax")
  , .loadMem "%r14" "%rsp" 48, .loadMemIdx "%rbp" "%r14" "%rsi" 8
  , .loadMem "%r14" "%rsp" (-8), .loadMemIdx "%r8" "%r14" "%rsi" 8
  , .mov "%r9" (.reg "%rbp"), .and_ "%r9" (.reg "%r8"), .mov "%rbp" (.reg "%r9")
  , .loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg "%rbp")
  , .mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rdi" (.imm 1)
  , .cmp "%rdi" (.reg "%rcx"), .cmp "%rdi" (.reg "%rdx") ]

/-- The decoded counted loop: counter `%rdi`, body `andDecLoopBody`. -/
def andDecLoop : XLoop 64 := { top := 4, ctr := "%rdi", body := andDecLoopBody }

/-- The decoded epilogue: the callee-saved restores and the closing `leaq`. -/
def andDecPost : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 40, .loadMem "%rbp" "%rsp" 32, .loadMem "%r12" "%rsp" 24
  , .loadMem "%r13" "%rsp" 16, .loadMem "%r14" "%rsp" 8, .loadMem "%r15" "%rsp" 0
  , .lea "%rsp" "%rsp" "%rsp" 0 64 ]

/-- **The decoded shipped `mpn_and_n_loop_owned`.** The function bytes of `andPhysLit`
    decode to the prologue `andDecPre`, the guarded counted loop `andDecLoop` and the
    epilogue `andDecPost` followed by `ret`. -/
theorem andPhysLit_decode :
    decodeLprog (encodeLfundefBytes andPhysLit)
      = some (nodeLayout andDecPre andDecLoop andDecPost) := by
  kernel_rfl

/-- **The decoded bytes of the linked object.** The function bytes of the body of the
    shipped program decode to the node layout. -/
theorem andLprog_decode :
    ∃ f : Lfundef, (andLprog ()).map (·.lp_funcs) = some [("mpn_and_n_loop_owned", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout andDecPre andDecLoop andDecPost) := by
  refine ⟨_, by rw [andLprog_eq]; rfl, ?_⟩
  rw [andPhysAbi_eq]
  exact andPhysLit_decode


/-! ## Ior: `mpn_ior_n_loop_owned` -/

/-- The limb operation of `mpn_ior_n_loop_owned`: `a OR b` as `(a XOR b) XOR (a AND b)`. -/
def iorOp : CatCrypt.Crypto.Jasmin.LowCT.SExpr → CatCrypt.Crypto.Jasmin.LowCT.SExpr →
    CatCrypt.Crypto.Jasmin.LowCT.SExpr := fun x y => .SXor (.SXor x y) (.SAnd x y)

theorem binIorFrontOk :
    (frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody iorOp)).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the limb body of
    `MpnLoopFrontEmit.iorLprog`. -/
noncomputable def binIorUpdate : Com jasminDialect (mapCtx ΓbodyBin)
    (mapTy (CryptoTy.memref N)) :=
  (frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody iorOp)).get binIorFrontOk

theorem iorFront_eq :
    frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody iorOp)
      = some binIorUpdate := (Option.some_get _).symm

/-- The runtime-trip loop node of `iorLprog` over `binIorUpdate`. -/
noncomputable def iorCom : ComL ΓouterBin (mapTy (CryptoTy.memref N)) :=
  ComL.forLoopNRt binIorUpdate .here (.there (.there (.there .here)))
    (.cons (.there (.there .here)) (.cons (.there .here) .nil)) (.ret .here)

/-- **The shipped program is the physical-ABI export of `iorCom`.** -/
theorem iorLprog_eq : iorLprog () = some (ComL.toLprogPhysAbi iorCom "mpn_ior_n_loop_owned"
    (argName 0) [argName 1, argName 2] (fun _ => none) (fun _ => none)
    ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]) := by
  unfold iorLprog binLprog rolledForLoopNRtLprog rolledForLoopNRt rolledForLoopNRtCont
  split
  next u hu =>
    have : u = binIorUpdate := Option.some.inj (hu.symm.trans iorFront_eq)
    subst this; rfl
  next hu => exact absurd (hu.symm.trans iorFront_eq) (by simp)

theorem iorBaseNames :
    ComL.loopArgBaseNames 4 (fun _ => none) iorCom 4 = some ("a0", ["a1", "a2"]) := by
  kernel_rfl

theorem iorAccRegs : (ComL.loopAccRegs iorCom 4).map regName = ["r4"] := by
  kernel_rfl

def iorAliasLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "SHL:0:64" [.reg "Lidx4"],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8],
    .Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a2" "L4_r4" 8],
    .Lopn [.reg "L4_r7"] "XOR:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "AND:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r9"] "XOR:64" [.reg "L4_r7", .reg "L4_r8"],
    .Lopn [.reg "L4_r10"] "SHL:0:64" [.reg "L4_r9"],
    .Lopn [.reg "L4_r11"] "STOREIDX" [.arrIdx "a0" "L4_r4" 8, .reg "L4_r10"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "L4_r11"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem iorAlias_eq :
    aliasRegBody "r4" "a0" (ComL.toLfundef iorCom (fun _ => none)).lfd_body = iorAliasLit := by
  kernel_rfl

theorem iorChain_eq :
    arrChainAlias iorAliasLit = (({} : Std.HashMap String String).insert "L4_r11" "a0") := by
  simp [arrChainAlias, iorAliasLit, isMemStore, stripWidthTag_loadidx, stripWidthTag_storeidx]

def iorCanonLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "SHL:0:64" [.reg "Lidx4"],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8],
    .Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a2" "L4_r4" 8],
    .Lopn [.reg "L4_r7"] "XOR:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "AND:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r9"] "XOR:64" [.reg "L4_r7", .reg "L4_r8"],
    .Lopn [.reg "L4_r10"] "SHL:0:64" [.reg "L4_r9"],
    .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L4_r4" 8, .reg "L4_r10"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem iorCanon_eq : canonicalizeMemrefThread iorAliasLit = iorCanonLit := by
  unfold canonicalizeMemrefThread
  rw [iorChain_eq]
  simp [Std.HashMap.isEmpty_insert, iorAliasLit, iorCanonLit, canonMemrefOperand,
    canonMemrefName, Std.HashMap.getD_insert]

/-- The physical body of the shipped `mpn_ior_n_loop_owned`. -/
def iorPhysLit : Lcmd := ([
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
    .Lopn [.reg "RDI"] "MOV:64" [.reg "RSI"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "RSI"] "SHL:0:64" [.reg "RAX"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
    .Lopn [.reg "RBP"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDX"],
    .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
    .Lopn [.reg "R9"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R8"],
    .Lopn [.reg "R10"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "R10"] "AND:64" [.reg "R10", .reg "R8"],
    .Lopn [.reg "RBP"] "MOV:64" [.reg "R9"],
    .Lopn [.reg "RBP"] "XOR:64" [.reg "RBP", .reg "R10"],
    .Lopn [.reg "R8"] "SHL:0:64" [.reg "RBP"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "R8"],
    .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
    .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1],
    .Lopn [.reg "RDI"] "SUB:64" [.reg "RDI", .imm 1],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RCX"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RDX"],
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

theorem iorPhysAbiOfCanon_eq :
    (physAbiOfCanon (ComL.toLfundef iorCom (fun _ => none)) iorCanonLit "a0" ["a1", "a2"]
      (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).1.lfd_body
      = iorPhysLit := by
  kernel_rfl

/-- **The function body of the shipped `mpn_ior_n_loop_owned`** is `iorPhysLit`. -/
theorem iorPhysAbi_eq : (ComL.toLfundefPhysAbi iorCom (argName 0) [argName 1, argName 2]
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).lfd_body
      = iorPhysLit := by
  rw [ComL.toLfundefPhysAbi_eq_ofVirt]
  have h4 : ΓouterBin.length = 4 := rfl
  simp only [h4, iorBaseNames, iorAccRegs]
  unfold lfundefPhysAbiOfVirt
  rw [ofVirtCert_eq_physAbiOfCanon]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [iorAlias_eq, iorCanon_eq]
  exact iorPhysAbiOfCanon_eq

/-- **The object bytes of the linked `mpn_ior_n_loop_owned`** are the ELF wrapping of the function
    bytes of `iorPhysLit`. -/
theorem iorObjBytes_eq {bs : List (BitVec 8)}
    (h : MpnLoopBytesEmit.objBytes (iorLprog ()) = some bs) :
    bs = ElfObject.buildElfObjectMulti
      [{ name := "mpn_ior_n_loop_owned", text := encodeLfundefBytes iorPhysLit }] := by
  rw [MpnLoopBytesEmit.objBytes, iorLprog_eq, Option.bind_some] at h
  rw [LprogBytesDecode.encodeLprogChecked_single rfl h, iorPhysAbi_eq]

def iorDecPre : List (JInstr 64) :=
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
  , .mov "%rdi" (.reg "%rsi") ]

def iorDecLoopBody : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rax")
  , .loadMem "%r14" "%rsp" 48
  , .loadMemIdx "%rbp" "%r14" "%rsi" 8
  , .loadMem "%r14" "%rsp" (-8)
  , .loadMemIdx "%r8" "%r14" "%rsi" 8
  , .mov "%r9" (.reg "%rbp")
  , .xor_ "%r9" (.reg "%r8")
  , .mov "%r10" (.reg "%rbp")
  , .and_ "%r10" (.reg "%r8")
  , .mov "%rbp" (.reg "%r9")
  , .xor_ "%rbp" (.reg "%r10")
  , .mov "%r8" (.reg "%rbp")
  , .loadMem "%r14" "%rsp" 56
  , .storeMemIdx "%r14" "%rsi" 8 (.reg "%r8")
  , .mov "%rbx" (.reg "%rbx")
  , .add "%rax" (.imm 1)
  , .sub "%rdi" (.imm 1)
  , .cmp "%rdi" (.reg "%rcx")
  , .cmp "%rdi" (.reg "%rdx") ]

def iorDecLoop : XLoop 64 := { top := 4, ctr := "%rdi", body := iorDecLoopBody }

def iorDecPost : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 40
  , .loadMem "%rbp" "%rsp" 32
  , .loadMem "%r12" "%rsp" 24
  , .loadMem "%r13" "%rsp" 16
  , .loadMem "%r14" "%rsp" 8
  , .loadMem "%r15" "%rsp" 0
  , .lea "%rsp" "%rsp" "%rsp" 0 64 ]

/-- **The decoded shipped `mpn_ior_n_loop_owned`.** -/
theorem iorPhysLit_decode :
    decodeLprog (encodeLfundefBytes iorPhysLit)
      = some (nodeLayout iorDecPre iorDecLoop iorDecPost) := by
  kernel_rfl

/-! ## Xor: `mpn_xor_n_loop_owned` -/

/-- The limb operation of `mpn_xor_n_loop_owned`: `a XOR b`. -/
def xorOp : CatCrypt.Crypto.Jasmin.LowCT.SExpr → CatCrypt.Crypto.Jasmin.LowCT.SExpr →
    CatCrypt.Crypto.Jasmin.LowCT.SExpr := .SXor

theorem binXorFrontOk :
    (frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody xorOp)).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the limb body of
    `MpnLoopFrontEmit.xorLprog`. -/
noncomputable def binXorUpdate : Com jasminDialect (mapCtx ΓbodyBin)
    (mapTy (CryptoTy.memref N)) :=
  (frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody xorOp)).get binXorFrontOk

theorem xorFront_eq :
    frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody xorOp)
      = some binXorUpdate := (Option.some_get _).symm

/-- The runtime-trip loop node of `xorLprog` over `binXorUpdate`. -/
noncomputable def xorCom : ComL ΓouterBin (mapTy (CryptoTy.memref N)) :=
  ComL.forLoopNRt binXorUpdate .here (.there (.there (.there .here)))
    (.cons (.there (.there .here)) (.cons (.there .here) .nil)) (.ret .here)

/-- **The shipped program is the physical-ABI export of `xorCom`.** -/
theorem xorLprog_eq : xorLprog () = some (ComL.toLprogPhysAbi xorCom "mpn_xor_n_loop_owned"
    (argName 0) [argName 1, argName 2] (fun _ => none) (fun _ => none)
    ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]) := by
  unfold xorLprog binLprog rolledForLoopNRtLprog rolledForLoopNRt rolledForLoopNRtCont
  split
  next u hu =>
    have : u = binXorUpdate := Option.some.inj (hu.symm.trans xorFront_eq)
    subst this; rfl
  next hu => exact absurd (hu.symm.trans xorFront_eq) (by simp)

theorem xorBaseNames :
    ComL.loopArgBaseNames 4 (fun _ => none) xorCom 4 = some ("a0", ["a1", "a2"]) := by
  kernel_rfl

theorem xorAccRegs : (ComL.loopAccRegs xorCom 4).map regName = ["r4"] := by
  kernel_rfl

def xorAliasLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "SHL:0:64" [.reg "Lidx4"],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8],
    .Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a2" "L4_r4" 8],
    .Lopn [.reg "L4_r7"] "XOR:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "SHL:0:64" [.reg "L4_r7"],
    .Lopn [.reg "L4_r9"] "STOREIDX" [.arrIdx "a0" "L4_r4" 8, .reg "L4_r8"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "L4_r9"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem xorAlias_eq :
    aliasRegBody "r4" "a0" (ComL.toLfundef xorCom (fun _ => none)).lfd_body = xorAliasLit := by
  kernel_rfl

theorem xorChain_eq :
    arrChainAlias xorAliasLit = (({} : Std.HashMap String String).insert "L4_r9" "a0") := by
  simp [arrChainAlias, xorAliasLit, isMemStore, stripWidthTag_loadidx, stripWidthTag_storeidx]

def xorCanonLit : Lcmd := ([
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0],
    .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "L4_r4"] "SHL:0:64" [.reg "Lidx4"],
    .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8],
    .Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a2" "L4_r4" 8],
    .Lopn [.reg "L4_r7"] "XOR:64" [.reg "L4_r5", .reg "L4_r6"],
    .Lopn [.reg "L4_r8"] "SHL:0:64" [.reg "L4_r7"],
    .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L4_r4" 8, .reg "L4_r8"],
    .Lopn [.reg "a0"] "MOV:64" [.reg "a0"],
    .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1],
    .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"],
    .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0],
    .Lcond (.reg "NZ") 4,
    .Llabel (.internal) 1073741828,
    .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

theorem xorCanon_eq : canonicalizeMemrefThread xorAliasLit = xorCanonLit := by
  unfold canonicalizeMemrefThread
  rw [xorChain_eq]
  simp [Std.HashMap.isEmpty_insert, xorAliasLit, xorCanonLit, canonMemrefOperand,
    canonMemrefName, Std.HashMap.getD_insert]

/-- The physical body of the shipped `mpn_xor_n_loop_owned`. -/
def xorPhysLit : Lcmd := ([
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
    .Lopn [.reg "RDI"] "MOV:64" [.reg "RSI"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .imm 0],
    .Lcond (.reg "Z") 1073741828,
    .Llabel (.internal) 4,
    .Lopn [.reg "RSI"] "SHL:0:64" [.reg "RAX"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
    .Lopn [.reg "RBP"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDX"],
    .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RSI" 8],
    .Lopn [.reg "R9"] "MOV:64" [.reg "RBP"],
    .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R8"],
    .Lopn [.reg "RBP"] "SHL:0:64" [.reg "R9"],
    .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
    .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "RBP"],
    .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
    .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1],
    .Lopn [.reg "RDI"] "SUB:64" [.reg "RDI", .imm 1],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RCX"],
    .Lopn [.reg "RDI"] "CMP:64" [.reg "RDI", .reg "RDX"],
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

theorem xorPhysAbiOfCanon_eq :
    (physAbiOfCanon (ComL.toLfundef xorCom (fun _ => none)) xorCanonLit "a0" ["a1", "a2"]
      (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).1.lfd_body
      = xorPhysLit := by
  kernel_rfl

/-- **The function body of the shipped `mpn_xor_n_loop_owned`** is `xorPhysLit`. -/
theorem xorPhysAbi_eq : (ComL.toLfundefPhysAbi xorCom (argName 0) [argName 1, argName 2]
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]).lfd_body
      = xorPhysLit := by
  rw [ComL.toLfundefPhysAbi_eq_ofVirt]
  have h4 : ΓouterBin.length = 4 := rfl
  simp only [h4, xorBaseNames, xorAccRegs]
  unfold lfundefPhysAbiOfVirt
  rw [ofVirtCert_eq_physAbiOfCanon]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [xorAlias_eq, xorCanon_eq]
  exact xorPhysAbiOfCanon_eq

/-- **The object bytes of the linked `mpn_xor_n_loop_owned`** are the ELF wrapping of the function
    bytes of `xorPhysLit`. -/
theorem xorObjBytes_eq {bs : List (BitVec 8)}
    (h : MpnLoopBytesEmit.objBytes (xorLprog ()) = some bs) :
    bs = ElfObject.buildElfObjectMulti
      [{ name := "mpn_xor_n_loop_owned", text := encodeLfundefBytes xorPhysLit }] := by
  rw [MpnLoopBytesEmit.objBytes, xorLprog_eq, Option.bind_some] at h
  rw [LprogBytesDecode.encodeLprogChecked_single rfl h, xorPhysAbi_eq]

def xorDecPre : List (JInstr 64) :=
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
  , .mov "%rdi" (.reg "%rsi") ]

def xorDecLoopBody : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rax")
  , .loadMem "%r14" "%rsp" 48
  , .loadMemIdx "%rbp" "%r14" "%rsi" 8
  , .loadMem "%r14" "%rsp" (-8)
  , .loadMemIdx "%r8" "%r14" "%rsi" 8
  , .mov "%r9" (.reg "%rbp")
  , .xor_ "%r9" (.reg "%r8")
  , .mov "%rbp" (.reg "%r9")
  , .loadMem "%r14" "%rsp" 56
  , .storeMemIdx "%r14" "%rsi" 8 (.reg "%rbp")
  , .mov "%rbx" (.reg "%rbx")
  , .add "%rax" (.imm 1)
  , .sub "%rdi" (.imm 1)
  , .cmp "%rdi" (.reg "%rcx")
  , .cmp "%rdi" (.reg "%rdx") ]

def xorDecLoop : XLoop 64 := { top := 4, ctr := "%rdi", body := xorDecLoopBody }

def xorDecPost : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 40
  , .loadMem "%rbp" "%rsp" 32
  , .loadMem "%r12" "%rsp" 24
  , .loadMem "%r13" "%rsp" 16
  , .loadMem "%r14" "%rsp" 8
  , .loadMem "%r15" "%rsp" 0
  , .lea "%rsp" "%rsp" "%rsp" 0 64 ]

/-- **The decoded shipped `mpn_xor_n_loop_owned`.** -/
theorem xorPhysLit_decode :
    decodeLprog (encodeLfundefBytes xorPhysLit)
      = some (nodeLayout xorDecPre xorDecLoop xorDecPost) := by
  kernel_rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
