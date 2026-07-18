/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
import CatCrypt.Crypto.SecureCompilation.AsconLinearGoldenPath
import CatCrypt.Crypto.SecureCompilation.AsconSboxGoldenPath
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.FieldModOpsGoldenPath
import CatCrypt.Crypto.SecureCompilation.FieldSubBorrowGoldenPath
import CatCrypt.Crypto.SecureCompilation.Sha512BitFuncsGoldenPath
import CatCrypt.Crypto.SecureCompilation.KeccakBitGoldenPath
import CatCrypt.Crypto.SecureCompilation.BranchlessSarGoldenPath
import CatCrypt.Crypto.SecureCompilation.BranchlessSelectGoldenPath
import CatCrypt.Crypto.SecureCompilation.VarShiftEmitGoldenPath

/-!
# `GoldenPathByteIdentityDemo` — re-homed `#eval` byte-identity certificates

The JInstr gather/byte-identity chain (`JInstrGatherExtended` →
`GatherImmForms` → `CompileComToElfJInstrFull6`) used to `#eval`-demo its
byte-match certificates on the real GoldenPath kernel `Com`s
(`asconSigma0Com`, `fieldMulLoCom`, …). That pulled the `*GoldenPath` modules
into the chain's import graph — a **cycle** the moment any GoldenPath kernel
wants to import the chain's re-point entry `compileComToElfJInstrFull6` for its
`_x86_elf` def.

This file breaks the cycle: it sits **above** both the chain
(`CompileComToElfJInstrFull6`, `GatherImmForms`) and the `*GoldenPath` kernel
modules, and carries **all** the moved `#eval` byte-match demos. The chain files
keep their kernel-independent `def`s / `theorem`s; only the kernel-`Com` `#eval`
certificates moved here. The `#eval`s below are the byte-match certificates (each
prints `true`), the same posture the chain modules recorded — interpreter
evidence on the real kernels, not part of any proof term.

No `sorry`, no axiom, no `native_decide`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GoldenPathByteIdentityDemo

open CatCrypt.Crypto.SecureCompilation.VIR (Com Ctxt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace (gatherJBlock3)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody (gatherJBlock4 lowerLinstrExtCov4L)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode (gatherJBlock5)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (matches6 pbody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (isMovq physAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
  (physBodyOf compileComToElfJInstrFull)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
  (compileComToElfJInstrFull6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
open CatCrypt.Crypto.SecureCompilation.AsconLinear (asconSigma0Com)
open CatCrypt.Crypto.SecureCompilation.AsconSbox (asconY0Com)
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath (fieldMulHiCom fieldMulLoCom)
open CatCrypt.Crypto.SecureCompilation.FieldModOps (condNegCom)
open CatCrypt.Crypto.SecureCompilation.FieldSubBorrow (fieldBorrowCom)
open CatCrypt.Crypto.SecureCompilation.Sha512BitFuncs (shaChCom)
open CatCrypt.Crypto.SecureCompilation.KeccakBit (keccakRho1Com keccakChiCom)
open CatCrypt.Crypto.SecureCompilation.BranchlessSar (sar1Com)
open CatCrypt.Crypto.SecureCompilation.BranchlessSelect (ctSelectCom)
open CatCrypt.Crypto.SecureCompilation.VarShiftEmit (boundedShrCom)

/-! ## 0. The kernel-`Com`-specific physical-body setup (moved from `PhysBodyGather`)

`physBody` / `aluCore` on `AsconLinear.asconSigma0Com` — the destructive
two-address physical body and its framing-free ALU core, the setup the gather
byte-compares below run on. -/

/-- The physical-ABI body of `asconSigma0Com` (prologue `MOVQ` spills + arg
    marshal, the ALU core, epilogue `MOVQ` restores, trailing `Lret`). -/
def physBody : List Linstr :=
  ((Com.toLprogPhysAbi asconSigma0Com "ascon_sigma0").lp_funcs.head?.map
    (fun p => p.2.lfd_body)).getD []

/-- The pure ALU core: the physical body with the `MOVQ` framing and the
    trailing `Lret` dropped. 12 instructions for `asconSigma0`. -/
def aluCore : List Linstr :=
  physBody.filter (fun i => !isLret i && !isMovq i)

/-! ## 1. `JInstrGatherExtended` — coverage on `asconSigma0Com` -/

#eval (comToFramedJLeaf2 asconSigma0Com "ascon_sigma0" asconAlloc asconArgs 0).isSome

#eval (CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstr.comToFramedJLeaf
  asconSigma0Com "ascon_sigma0" asconAlloc asconArgs 0).isSome

#eval (CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr.comBody
  asconSigma0Com "ascon_sigma0").bind gatherJBlock2

-- The exact exported body: 8 width-tagged `Lopn`s terminated by `Lret`.
#eval (CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr.comBody
  asconSigma0Com "ascon_sigma0").map (·.map (·.li_i))

/-! ## 2. `PhysBodyGather` — the non-in-place byte-compare on the physical ALU core -/

-- The whole physical body does NOT gather (the `MOVQ` framing is uncovered). `false`.
#eval (gatherJBlock2 physBody).isSome

-- Which physical-body instructions lower, and which don't.
#eval (physBody.filter (fun i => !isLret i)).map
  (fun i => match i.li_i with
            | .Lopn _ opn _ => (opn, (lowerLinstrExtCovL i).isSome)
            | _             => ("?", (lowerLinstrExtCovL i).isSome))

-- The ALU core DOES gather (the 12 width-tagged ops). `true`.
#eval (gatherJBlock2 aluCore).isSome

-- The non-in-place byte-compare on the physical ALU core. `false` (NO byte-match).
#eval encodeJBlock physAlloc ((gatherJBlock2 aluCore).getD []) == encodeLcmd aluCore

#eval (encodeJBlock physAlloc ((gatherJBlock2 aluCore).getD [])).length
#eval (encodeLcmd aluCore).length

/-! ## 3. `GatherInPlace` — the in-place byte-compare and the dropped-rotation finding -/

/-- Whether an ALU-core `Lopn` is a count-in-tag shift (`SHR/SHL:n:64`). -/
def isTagShift (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn _ opn _ => opn == "SHR:19:64" || opn == "SHL:45:64"
                       || opn == "SHR:28:64" || opn == "SHL:36:64"
  | _             => false

/-- The shift-free ALU core: the MOV/OR/XOR ops only. -/
def nonShiftCore : List Linstr := aluCore.filter (fun i => !isTagShift i)

-- The in-place gather still gathers the ALU core. `true`.
#eval (gatherJBlock3 aluCore).isSome

-- THE NON-SHIFT BYTE-MATCH: the gathered JInstr bytes of the shift-free MOV/OR/XOR
-- core equal `encodeLcmd` of the same core, byte-for-byte. `true`.
#eval encodeJBlock physAlloc ((gatherJBlock3 nonShiftCore).getD []) == encodeLcmd nonShiftCore

-- The dropped-rotation regression witness: `encodeLopn` of the first physical-body
-- shift now emits `[0x48,0xc1,0xe8,0x13]`, NOT `[]`.
#eval encodeLopn 0 0 (.Lopn [.reg "RAX"] "SHR:19:64" [.reg "RBX"])

-- No rotation is dropped: the count of zero-length Lopns in the ALU core is `0`.
#eval (aluCore.filter (fun i => (encodeLopn 0 64 i.li_i).length == 0)).length

/-! ## 4. `GatherFullBody` — whole-body gather + the framing-free compute-core match -/

/-- Whether an `Linstr` is a qsave callee-save reg↔mem spill/restore. -/
def isMovqSpill (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg d] "MOVQ" [.reg s] => d.startsWith "qsave." || s.startsWith "qsave."
  | _ => false

/-- The physical body with the qsave reg↔mem spills (and the trailing `Lret`) dropped. -/
def coreNoSpill : List Linstr :=
  physBody.filter (fun i => !isLret i && !isMovqSpill i)

-- The WHOLE physical body now gathers (the `MOVQ ↦ MOV:64` alias). `true`.
#eval (gatherJBlock4 physBody).isSome

-- THE COMPUTE-CORE BYTE-MATCH: gathered framed JInstr bytes vs the Lprog encoder
-- on the SAME physical ALU/shift core. `true`.
#eval (gatherJBlock4 aluCore).map (encodeJBlock physAlloc) == some (encodeLcmd aluCore)

-- The whole-body compare is still `false` — residual = the qsave reg↔mem spills.
#eval (gatherJBlock4 physBody).map (encodeJBlock physAlloc) == some (encodeLcmd physBody)

-- With ONLY the qsave reg↔mem spills removed, the gather byte-matches. `true`.
#eval (gatherJBlock4 coreNoSpill).map (encodeJBlock physAlloc) == some (encodeLcmd coreNoSpill)

/-! ## 5. `SpillSlotEncode` — the WHOLE physical-body byte-identity (the milestone) -/

-- The whole physical body gathers under the spill-aware lowering. `true`.
#eval (gatherJBlock5 physBody).isSome

-- THE WHOLE-BODY BYTE-MATCH: gathered JInstr bytes vs the Lprog encoder, on the
-- SAME real-kernel physical body — framing + qsave + ALU + shift. `true`.
#eval (gatherJBlock5 physBody).map (encodeJBlock physAlloc) == some (encodeLcmd physBody)

-- Same length, both sides. `111` / `111`.
#eval ((gatherJBlock5 physBody).map (encodeJBlock physAlloc)).map List.length
#eval (encodeLcmd physBody).length

/-! ## 6. `BlockBytesAgreeExtended` — the physical-body mnemonic printout -/

#eval (Com.toLprogPhysAbi asconSigma0Com "ascon_sigma0").lp_funcs.head?.map
  (fun nf => nf.2.lfd_body.map (·.li_i))

/-! ## 7. `CompileComToElfJInstrFull` — the whole-ELF byte-match + re-point demo -/

-- The full physical body gathers under the spill-aware lowering. `true`.
#eval (gatherJBlock5 (physBodyOf asconSigma0Com "ascon_sigma0")).isSome

-- THE WHOLE-ELF BYTE-MATCH: the full-body JInstr ELF entry vs `compileComToElf`,
-- on the real kernel `asconSigma0`. `true`.
#eval compileComToElfJInstrFull asconSigma0Com "ascon_sigma0"
        == compileComToElf asconSigma0Com "ascon_sigma0"

-- Same object size, both entries. `768` / `768`.
#eval (compileComToElfJInstrFull asconSigma0Com "ascon_sigma0").size
#eval (compileComToElf asconSigma0Com "ascon_sigma0").size

/-! ## 8. `GatherImmForms` — the per-kernel byte-match across all surveyed kernels -/

-- The 10 previously-blocked kernels: each prints `true`.
#eval matches6 (pbody asconY0Com "ascon_y0")          -- imm32-sign-ext MOV
#eval matches6 (pbody fieldMulHiCom "field_mul_hi")   -- nil MULXHI
#eval matches6 (pbody condNegCom "cond_neg")          -- all-ones MOV + shift-by-1
#eval matches6 (pbody fieldBorrowCom "field_borrow")
#eval matches6 (pbody shaChCom "sha_ch")
#eval matches6 (pbody keccakRho1Com "keccak_rho1")
#eval matches6 (pbody keccakChiCom "keccak_chi")
#eval matches6 (pbody sar1Com "sar1")                 -- shift-by-1
#eval matches6 (pbody ctSelectCom "ct_select")        -- all-ones MOV
#eval matches6 (pbody boundedShrCom "bounded_shr")

-- Already-matching kernels still match (no regression). `true`.
#eval matches6 (pbody asconSigma0Com "ascon_sigma0")
#eval matches6 (pbody fieldMulLoCom "field_mul_lo")

/-! ## 9. `CompileComToElfJInstrFull6` — the wired re-point entry byte-match -/

-- THE RE-POINT SMOKE CHECK: the byte-safe entry `compileComToElfJInstrFull6`
-- byte-matches `compileComToElf` on `asconSigma0` (the def the GoldenPath kernels'
-- `_x86_elf` defs re-point to). `true`.
#eval compileComToElfJInstrFull6 asconSigma0Com "ascon_sigma0"
        == compileComToElf asconSigma0Com "ascon_sigma0"

end CatCrypt.Crypto.SecureCompilation.X86Backend.GoldenPathByteIdentityDemo
