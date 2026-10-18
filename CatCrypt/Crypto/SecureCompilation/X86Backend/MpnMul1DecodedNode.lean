/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin

@[expose] public section

set_option autoImplicit false

/-!
# The `mpn_mul_1` loop node: its shape and its decoded bytes

`DecodedLsemLoop.decNode_halts` relates a flag-machine node
`seeds ++ guardedFlagLoopLinstrRM top endL ctr body` to the decoded layout
`nodeLayout pre l post`. This module supplies its structural hypotheses at the
front-compiled `mpn_mul_1` kernel.

## The flag-machine node

The export node `forLoopLcmdNRtRM` of the limb body `mul1Update` at depth `4`
(accumulator `regName 4`, seed `argName 0`, count `argName 2`, invariant bases
`argName 3` and `argName 1`), renamed by a node renaming `ρ` fixing the counter
`loopCtr 4`, is the three renamed seed moves `mul1Seeds ρ` followed by the guarded
loop over the renamed looped segment `mul1LoopBody ρ`, with top label `4` and skip
label `4 + 0x40000000`.

## The decoded physical body

`mul1PhysBody` is the body of the one function of
`MpnMul1FrontEmit.mul1RtLprogOpt "mpn_mul_1_rt"`: the output of
`ComL.toLprogPhysAbi` followed by `FuseMulHi.fuseMulHiLprog` in its
`saveRdx` mode, before `LprogOptPipeline.optimizeLprog`. `mul1PhysBody_eq` pins it
to the literal `mul1PhysBodyLit`. The function bytes `encodeLfundefBytes` lays down
for it decode to `nodeLayout mul1DecPre mul1DecLoop mul1DecPost`: the prologue
(frame `leaq`, the eight saves, the argument moves and the loop seeds), the
counted loop on `%rbp`, and the epilogue restores with the closing `leaq`.

## Main results

* `mul1Node_eq`: the renamed node is `mul1Seeds ρ ++ guardedFlagLoopLinstrRM 4
  (4 + 0x40000000) (loopCtr 4) (mul1LoopBody ρ)`.
* `mul1Seeds_isLopn`, `mul1LoopBody_isLopn`: seeds and looped segment are
  all-`Lopn`.
* `mul1Node_top`, `mul1Node_end`: the top label at `seeds.length + 2`, the skip
  label at `seeds.length + body.length + 5`.
* `mul1PhysBody_eq`: the exporter's physical body is `mul1PhysBodyLit`.
* `mul1PhysBody_decode`: `decodeLprog (encodeLfundefBytes mul1PhysBody)
  = some (nodeLayout mul1DecPre mul1DecLoop mul1DecPost)`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote (mul1Update)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (mul1RtLprogOpt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)

/-! ## 1. The flag-machine node -/

/-- A label search behind an all-`Lopn` prefix is the search in the rest, shifted by
    the prefix length. -/
theorem findLabelMem_append_of_isLopn (l : LLabel) (xs ys : List LinstrRM)
    (hx : ∀ i ∈ xs, IsLopn i) :
    findLabelMem l (xs ++ ys) = (findLabelMem l ys).map (· + xs.length) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_append, List.findIdx?_append]
  have hnone : (xs.map Prod.fst).findIdx? (JasminLsemLabeled.isLabel l) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    obtain ⟨d, o, s, hd⟩ := hx i hi
    rw [hd]
    rfl
  rw [hnone, List.length_map]
  simp

/-- The three seed moves of the `mpn_mul_1` node, renamed by `ρ`. -/
def mul1Seeds (ρ : String → String) : List LinstrRM :=
  (loopSeedsRM 4 (regName 4) (.reg (argName 0)) (.reg (argName 2))).map (renRM ρ)

/-- The looped segment of the `mpn_mul_1` node, renamed by `ρ`. -/
def mul1LoopBody (ρ : String → String) : List LinstrRM :=
  (forLoopBodyNRtRM 4 (regName 4) mul1Update [.reg (argName 3), .reg (argName 1)]
    (fun _ => none)).map (renRM ρ)

/-- **The renamed `mpn_mul_1` node.** Under a renaming `ρ` that fixes the counter
    `loopCtr 4`, the export node of the limb body is the renamed seeds followed by the
    guarded loop over the renamed looped segment, with top label `4` and skip label
    `4 + 0x40000000`. -/
theorem mul1Node_eq (ρ : String → String) (hctr : ρ (loopCtr 4) = loopCtr 4) :
    (forLoopLcmdNRtRM 4 (regName 4) (.reg (argName 0)) (.reg (argName 2)) mul1Update
        [.reg (argName 3), .reg (argName 1)] (fun _ => none)).map (renRM ρ)
      = mul1Seeds ρ ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) (loopCtr 4)
          (mul1LoopBody ρ) := by
  unfold forLoopLcmdNRtRM
  rw [List.map_append, guardedFlagLoopLinstrRM_map_renRM, hctr]
  rfl

theorem mul1Seeds_length (ρ : String → String) : (mul1Seeds ρ).length = 3 := rfl

/-- The renamed seeds are `Lopn`s. -/
theorem mul1Seeds_isLopn (ρ : String → String) : ∀ i ∈ mul1Seeds ρ, IsLopn i := by
  intro i hi
  simp only [mul1Seeds, loopSeedsRM, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

/-- The renamed looped segment is all-`Lopn`. -/
theorem mul1LoopBody_isLopn (ρ : String → String) : ∀ i ∈ mul1LoopBody ρ, IsLopn i := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨d, o, s, h⟩ := forLoopBodyNRtRM_isLopn _ _ _ _ _ j hj
  exact ⟨d.map (renOperand ρ), o, s.map (renOperand ρ), by
    show renLinstrR ρ j.1 = _
    rw [h]
    rfl⟩

/-- The top label `4` of the renamed node sits two instructions behind the seeds. -/
theorem mul1Node_top (ρ : String → String) :
    findLabelMem 4 (mul1Seeds ρ ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) (loopCtr 4)
        (mul1LoopBody ρ))
      = some ((mul1Seeds ρ).length + 2) := by
  rw [findLabelMem_append_of_isLopn _ _ _ (mul1Seeds_isLopn ρ), findLabelMem_guarded_top]
  simp [Nat.add_comm]

/-- The skip label `4 + 0x40000000` of the renamed node sits behind the guarded loop. -/
theorem mul1Node_end (ρ : String → String) :
    findLabelMem (4 + 0x40000000) (mul1Seeds ρ ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000)
        (loopCtr 4) (mul1LoopBody ρ))
      = some ((mul1Seeds ρ).length + (mul1LoopBody ρ).length + 5) := by
  rw [findLabelMem_append_of_isLopn _ _ _ (mul1Seeds_isLopn ρ),
    findLabelMem_guarded_endL _ _ _ _ (mul1LoopBody_isLopn ρ) (by decide)]
  simp only [Option.map_some, Option.some.injEq]
  omega

/-! ## 2. The physical body and its decoded bytes -/

/-- The body of the first function of the owned `mpn_mul_1` `Lprog`
    `mul1RtLprogOpt "mpn_mul_1_rt"`: the physical-ABI export followed by the `MULX`
    fusion in its `saveRdx` mode. -/
def mul1PhysBody : Lcmd :=
  (((mul1RtLprogOpt "mpn_mul_1_rt").bind (·.lp_funcs.head?)).map (·.2.lfd_body)).getD []

/-- The physical body of `mpn_mul_1` as a fixed instruction list: the qsave prologue,
    the argument moves and loop seeds, the guard, the loop body with the fused `MULX`
    bracketed by the save and restore of `RDX` through `R15`, the back-edge, the
    epilogue restores and `Lret`. -/
def mul1PhysBodyLit : Lcmd := ([
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
  .Lopn [.reg "RSI"] "MOVQ" [.reg "qsave.RDX"],
  .Lopn [.reg "RDI"] "MOVQ" [.reg "qsave.RCX"],
  .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
  .Lopn [.reg "RAX"] "MOV:64" [.imm 0],
  .Lopn [.reg "RBP"] "MOV:64" [.reg "RSI"],
  .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .imm 0],
  .Lcond (.reg "Z") 1073741828,
  .Llabel .internal 4,
  .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
  .Lopn [.reg "RSI"] "LOADIDX" [.arrIdx "R14" "RAX" 8],
  .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RSI"],
  .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "R14" "RAX" 8],
  .Lopn [.reg "R9"] "MOV:64" [.reg "R8"],
  .Lopn [.reg "R9"] "MUL:64" [.reg "R9", .reg "RDI"],
  .Lopn [.reg "R10"] "SHL:0:64" [.reg "R9"],
  .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"],
  .Lopn [.reg "RDX"] "MOV:64" [.reg "R8"],
  .Lopn [.reg "R9", .reg "R9"] "MULX" [.reg "RDI"],
  .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"],
  .Lopn [.reg "R8"] "SHL:0:64" [.reg "R9"],
  .Lopn [.reg "R9"] "MOV:64" [.reg "R10"],
  .Lopn [.reg "R9"] "ADD:64" [.reg "R9", .reg "RSI"],
  .Lopn [.reg "RSI"] "SHL:0:64" [.reg "R9"],
  .Lopn [.reg "R9"] "MOV:64" [.imm 18446744073709551615],
  .Lopn [.reg "R11"] "MOV:64" [.reg "RSI"],
  .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "R9"],
  .Lopn [.reg "R9"] "MOV:64" [.reg "R11"],
  .Lopn [.reg "R9"] "AND:64" [.reg "R9", .reg "R10"],
  .Lopn [.reg "R11"] "SHL:0:64" [.reg "R9"],
  .Lopn [.reg "R9"] "MOV:64" [.reg "RSI"],
  .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R10"],
  .Lopn [.reg "R12"] "MOV:64" [.imm 18446744073709551615],
  .Lopn [.reg "R13"] "MOV:64" [.reg "R9"],
  .Lopn [.reg "R13"] "XOR:64" [.reg "R13", .reg "R12"],
  .Lopn [.reg "R9"] "MOV:64" [.reg "RSI"],
  .Lopn [.reg "R9"] "SUB:64" [.reg "R9", .reg "R10"],
  .Lopn [.reg "R10"] "MOV:64" [.reg "R13"],
  .Lopn [.reg "R10"] "AND:64" [.reg "R10", .reg "R9"],
  .Lopn [.reg "R9"] "SHL:0:64" [.reg "R10"],
  .Lopn [.reg "R10"] "MOV:64" [.reg "R11"],
  .Lopn [.reg "R10"] "XOR:64" [.reg "R10", .reg "R9"],
  .Lopn [.reg "R12"] "MOV:64" [.reg "R11"],
  .Lopn [.reg "R12"] "AND:64" [.reg "R12", .reg "R9"],
  .Lopn [.reg "R9"] "MOV:64" [.reg "R10"],
  .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R12"],
  .Lopn [.reg "R10"] "MOV:64" [.imm 63],
  .Lopn [.reg "R10"] "SHR:63:64" [.reg "R9"],
  .Lopn [.reg "R9"] "SHL:0:64" [.reg "R10"],
  .Lopn [.reg "R10"] "MOV:64" [.reg "R8"],
  .Lopn [.reg "R10"] "ADD:64" [.reg "R10", .reg "R9"],
  .Lopn [.reg "R8"] "SHL:0:64" [.reg "R10"],
  .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
  .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RAX" 8, .reg "RSI"],
  .Lopn [.reg "RSI"] "MOV:64" [.imm 1],
  .Lopn [.reg "R9"] "MOV:64" [.reg "RAX"],
  .Lopn [.reg "R9"] "ADD:64" [.reg "R9", .reg "RSI"],
  .Lopn [.reg "RSI"] "SHL:0:64" [.reg "R9"],
  .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.RDI"],
  .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "RSI" 8, .reg "R8"],
  .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"],
  .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1],
  .Lopn [.reg "RBP"] "SUB:64" [.reg "RBP", .imm 1],
  .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "RDI"],
  .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .reg "RCX"],
  .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .imm 0],
  .Lcond (.reg "NZ") 4,
  .Llabel .internal 1073741828,
  .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"],
  .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"],
  .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"],
  .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"],
  .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"],
  .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"],
  .Lret ] : List LinstrR).map (fun i => ⟨0, i⟩)

/-- The exporter's physical body of `mpn_mul_1` is the pinned literal. The register
    allocation and the `MULX` fusion do not reduce in the kernel, so the equality is
    checked by compiled evaluation. -/
theorem mul1PhysBody_eq : mul1PhysBody = mul1PhysBodyLit := by
  native_decide

/-- The decoded prologue: the frame `leaq`, the saves of the argument and callee-saved
    registers, the argument moves and the loop seeds, ending with the count in `%rbp`. -/
def mul1DecPre : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-64)
  , .storeMem "%rsp" 56 (.reg "%rdi"), .storeMem "%rsp" 48 (.reg "%rsi")
  , .storeMem "%rsp" 40 (.reg "%rbx"), .storeMem "%rsp" 32 (.reg "%rbp")
  , .storeMem "%rsp" 24 (.reg "%r12"), .storeMem "%rsp" 16 (.reg "%r13")
  , .storeMem "%rsp" 8 (.reg "%r14"), .storeMem "%rsp" 0 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx"), .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 56, .loadMem "%rcx" "%rsp" 48
  , .loadMem "%rsi" "%rsp" (-8), .loadMem "%rdi" "%rsp" (-16)
  , .mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rbp" (.reg "%rsi") ]

/-- The decoded loop body: the two limb loads, the low product, the fused high product
    with `%rcx` saved at `-128(%rsp)`, the carry chain, the two stores, the index
    advance, the counter decrement and the two invariant touches. -/
def mul1DecLoopBody : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 56, .loadMemIdx "%rsi" "%r14" "%rax" 8
  , .loadMem "%r14" "%rsp" 48, .loadMemIdx "%r8" "%r14" "%rax" 8
  , .mov "%r9" (.reg "%r8"), .imul "%r9" (.reg "%rdi"), .mov "%r10" (.reg "%r9")
  , .mov "%r15" (.reg "%rdx"), .mov "%rdx" (.reg "%r8")
  , .storeMem "%rsp" (-128) (.reg "%rcx"), .mulx "%r9" "%rcx" (.reg "%rdx") (.reg "%rdi")
  , .loadMem "%rcx" "%rsp" (-128)
  , .mov "%rdx" (.reg "%r15"), .mov "%r8" (.reg "%r9"), .mov "%r9" (.reg "%r10")
  , .add "%r9" (.reg "%rsi"), .mov "%rsi" (.reg "%r9"), .mov "%r9" (.imm 18446744073709551615)
  , .mov "%r11" (.reg "%rsi"), .xor_ "%r11" (.reg "%r9"), .mov "%r9" (.reg "%r11")
  , .and_ "%r9" (.reg "%r10"), .mov "%r11" (.reg "%r9"), .mov "%r9" (.reg "%rsi")
  , .xor_ "%r9" (.reg "%r10"), .mov "%r12" (.imm 18446744073709551615), .mov "%r13" (.reg "%r9")
  , .xor_ "%r13" (.reg "%r12"), .mov "%r9" (.reg "%rsi"), .sub "%r9" (.reg "%r10")
  , .mov "%r10" (.reg "%r13"), .and_ "%r10" (.reg "%r9"), .mov "%r9" (.reg "%r10")
  , .mov "%r10" (.reg "%r11"), .xor_ "%r10" (.reg "%r9"), .mov "%r12" (.reg "%r11")
  , .and_ "%r12" (.reg "%r9"), .mov "%r9" (.reg "%r10"), .xor_ "%r9" (.reg "%r12")
  , .mov "%r10" (.imm 63), .mov "%r10" (.reg "%r9"), .shr "%r10" (.imm 63)
  , .mov "%r9" (.reg "%r10"), .mov "%r10" (.reg "%r8"), .add "%r10" (.reg "%r9")
  , .mov "%r8" (.reg "%r10"), .loadMem "%r14" "%rsp" 56
  , .storeMemIdx "%r14" "%rax" 8 (.reg "%rsi"), .mov "%rsi" (.imm 1)
  , .mov "%r9" (.reg "%rax"), .add "%r9" (.reg "%rsi"), .mov "%rsi" (.reg "%r9")
  , .loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg "%r8")
  , .mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rbp" (.imm 1)
  , .cmp "%rbp" (.reg "%rdi"), .cmp "%rbp" (.reg "%rcx") ]

/-- The decoded counted loop: counter `%rbp`, body `mul1DecLoopBody`. -/
def mul1DecLoop : XLoop 64 := { top := 4, ctr := "%rbp", body := mul1DecLoopBody }

/-- The decoded epilogue: the callee-saved restores and the closing `leaq`. -/
def mul1DecPost : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 40, .loadMem "%rbp" "%rsp" 32, .loadMem "%r12" "%rsp" 24
  , .loadMem "%r13" "%rsp" 16, .loadMem "%r14" "%rsp" 8, .loadMem "%r15" "%rsp" 0
  , .lea "%rsp" "%rsp" "%rsp" 0 64 ]

deriving instance DecidableEq for RInstr

/-- The function bytes of the pinned body decode to the node layout. -/
theorem mul1PhysBodyLit_decode :
    decodeLprog (encodeLfundefBytes mul1PhysBodyLit)
      = some (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) := by
  decide +kernel

/-- **The decoded `mpn_mul_1` node.** The function bytes `encodeLfundefBytes` lays down
    for the exporter's physical body decode to the prologue `mul1DecPre`, the guarded
    counted loop `mul1DecLoop` and the epilogue `mul1DecPost` followed by `ret`. -/
theorem mul1PhysBody_decode :
    decodeLprog (encodeLfundefBytes mul1PhysBody)
      = some (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) := by
  rw [mul1PhysBody_eq]
  exact mul1PhysBodyLit_decode

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode
