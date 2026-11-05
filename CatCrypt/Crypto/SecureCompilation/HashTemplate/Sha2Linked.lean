/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2LinkedData
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2LinkedData
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose

/-!
# The SHA-512 compression template as a region-compiled linked function

The SHA-512 compression template with one input array and an output array,
`sha2CompressBodyP sha512P`, compiled by the region back half `compileRegion` under the layout
`redLayout sha512Abi sha512Frame` (the output array `h` of 8 words at `%rdi`, the input array
`hm` of 24 words, the chaining words then the message words, at `%rsi`, the result the 8 words
at `%rdi`, and the stack words the frame of the code and the red zone below it), is the
template kernel `sha512Data`, whose linked function `sha512Kernel` has the meaning the
reference compression `sha2CompressRef sha512P`.

## Main definitions

* `sha512Abi` (module `Sha2LinkedData`): the layout at which the frame size of the code is
  read.
* `sha512Frame`, `sha512Pol`: the frame size of the code and its store policy.
* `sha512Ref`: the reference compression on source values.
* `sha512Data`: the data of the template kernel at a frame size.
* `sha512Kernel`: the linked function of the compiled template.

## Main statements

* `sha512CICheck_true`, `sha512_check`: the template compiles at the frame of its code, the
  layout passes the footprint check, the template the read-only check, and the decoded block
  the clobber check.
* `sha512Kernel_meets`: the code of the kernel meets the contract of its record.
* `sha512Kernel_linked`: the kernel is a linked kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.Hax (LinkedFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (isResRegion)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs)
open _root_.Hax (Value)

/-! ## 1. The layout -/

/-- The registers the code of the SHA-512 compression may change: every general-purpose
    register other than the stack register. -/
def sha512Clob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- **The frame size of the code of the SHA-512 compression**: `codeFrame` of the compiled
    template under `sha512Abi`. -/
def sha512Frame : Nat :=
  codeFrame sha512Abi (nfAbiNames "sha512_compress" sha512Abi)
    (NFProg.ofCom (sha2CompressBodyP sha512P))

/-- The store policy of the code of the SHA-512 compression: the red zone of `redZone` bytes,
    and the out window of the 64 bytes of the output array at `%rdi`. -/
def sha512Pol : StorePol := ⟨redZone, [("%rdi", 0, 64)]⟩

/-! ## 2. The meaning -/

/-- The input array of the compression splits into its chaining words and its message
    words. -/
theorem sha2InWords_split {w : Nat} (a : Fin 24 → BitVec w) :
    sha2InWords (fun i : Fin 8 => a ⟨i.1, by omega⟩) (fun j : Fin 16 => a ⟨8 + j.1, by omega⟩)
      = a := by
  funext i
  simp only [sha2InWords]
  split_ifs
  · rfl
  · congr 1
    ext
    simp
    omega

/-- **The reference compression on source values** of the parameters `h` and `hm`: the output
    array decoded as an array of 8 words, the input array as an array of 24 words, and the
    eight words of `sha2CompressRef sha512P` at the chaining words and the message words of
    the input array. -/
def sha512Ref (vals : List Value) : Option (Fin 8 → BitVec 64) :=
  match vals with
  | [hv, hmv] =>
      (dec (.arr 8 (.word 64)) hv).bind fun _ =>
      (dec (.arr 24 (.word 64)) hmv).map fun hm =>
        sha512P.sha2CompressRef (fun i => hm ⟨i.1, by omega⟩) (fun j => hm ⟨8 + j.1, by omega⟩)
  | _ => none

/-- The reference compression returns values only on arguments of the kinds of the
    layout. -/
theorem sha512_ref_kinds : ∀ vals r, sha512Ref vals = some r →
    vals.map valKind = sha512Abi.args.map (·.kind) := by
  intro vals r h
  unfold sha512Ref at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp h
    simp only [List.map_cons, List.map_nil, valKind_of_dec_arr hx, valKind_of_dec_arr hy]
    rfl
  · cases h

/-! ## 3. The valuation of the layout -/

/-- The valuation of the SHA-512 compression read off the entry state `sa`: the 24 words at
    `%rsi` and the 8 words at `%rdi`. -/
def sha512Val (sa : AState) : Ctxt.Valuation (sha2InCtxtP 64) :=
  .cons (wordsFn sa (sa.regs "%rsi") 24) (.cons (wordsFn sa (sa.regs "%rdi") 8) .nil)

theorem abiValOf_sha512 (sa : AState) : AbiValOf sha512Abi sa (sha512Val sa) where
  arg := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩
  arr := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- **The reference compression at the layout reading**: at the source values the layout
    reads off the entry state `sa`, the reference compression returns the value of the
    template at `sha512Val sa`. -/
theorem sha512_ref_read (sa : AState) :
    sha512Ref (sha512Abi.args.map (·.read sa)) =
      some ((sha2CompressBodyP sha512P).denote (sha512Val sa)) := by
  have hvals : sha512Abi.args.map (·.read sa) = [.array (wordsAt sa.mem (sa.regs "%rdi") 8),
      .array (wordsAt sa.mem (sa.regs "%rsi") 24)] :=
    rfl
  rw [hvals]
  simp only [sha512Ref, X86Backend.LinkedFnCallee.dec_arr_wordsAt, Option.bind_some]
  have h := sha2CompressBodyP_value sha512P
    (fun i : Fin 8 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
      (sa.regs "%rsi") i.1))
    (fun j : Fin 16 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
      (sa.regs "%rsi") (8 + j.1)))
    (wordsFn sa (sa.regs "%rdi") 8)
  have hw : sha2InWords (w := sha512P.w)
      (fun i : Fin 8 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
        (sa.regs "%rsi") i.1))
      (fun j : Fin 16 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
        (sa.regs "%rsi") (8 + j.1))) = wordsFn sa (sa.regs "%rsi") 24 :=
    sha2InWords_split (wordsFn sa (sa.regs "%rsi") 24)
  rw [hw] at h
  exact congrArg some h.symm

/-! ## 4. The template kernel -/

/-- **The data of the SHA-512 compression kernel** at the frame size `F`, under the layout
    `redLayout sha512Abi F`. -/
def sha512Data (F : Nat) (hF : F + redZone + 8 ≤ 2 ^ 64) : TemplateKernelData where
  name := "sha512_compress"
  params := [("h", .arr 8 (.word 64)), ("hm", .arr 24 (.word 64))]
  Γ := sha2InCtxtP 64
  nOut := 8
  body := sha2CompressBodyP sha512P
  layout := redLayout sha512Abi F
  clob := sha512Clob
  frame := F
  pol := sha512Pol
  outReg := "%rdi"
  ref := sha512Ref
  val := sha512Val
  events := sha2CompressBodyP_events sha512P JLeakParams.owned (fun _ => rfl)
  abiValOf_val sa := abiValOf_redLayout (abiValOf_sha512 sa)
  regArr := by decide
  ref_read := sha512_ref_read
  ref_kinds := sha512_ref_kinds
  kinds_eq := rfl
  arity := rfl
  args_nodup := (by decide : (sha512Abi.args.map (·.reg)).Nodup)
  pubWords := rfl
  result := rfl
  bounds := rfl
  regions_nodup := (by decide : sha512Abi.regions.Nodup)
  regions_ro :=
    (by decide : (sha512Abi.regions.filter fun p => !isResRegion sha512Abi p).length ≤ 1)
  frameHi := (by decide : sha512Abi.frameHi ≤ -8)
  out_region := (by decide : ("%rdi", 8) ∈ sha512Abi.regions)
  out_fit := by norm_num
  wins := by decide
  result_regs := (by decide : ∀ r ∈ resultRegs sha512Abi.result, r ∈ abiRegs sha512Abi)
  frame_fit := redLayout_frame_fit hF

/-- The check of the SHA-512 compression kernel at the frame size of its code: `frameCheck`
    of the template under `sha512Abi`, one evaluation of the back half. -/
def sha512CICheck : Bool :=
  frameCheck sha512Abi (nfAbiNames "sha512_compress" sha512Abi)
    (NFProg.ofCom (sha2CompressBodyP sha512P)) sha512Pol sha512Clob

set_option linter.style.native false in
/-- **The check of the compiled SHA-512 compression at the frame of its code**: the frame with
    the red zone fits, the back half succeeds at `redLayout sha512Abi sha512Frame`, the
    layout passes `layoutFootRoB`, the template passes the read-only check, and the decoded
    block passes `clobOkB` at `sha512Clob`. -/
theorem sha512CICheck_true : sha512CICheck = true := by
  native_decide

/-- The frame of the code of the SHA-512 compression fits with its red zone. -/
theorem sha512Frame_fit : sha512Frame + redZone + 8 ≤ 2 ^ 64 := by
  rw [sha512Frame]
  exact fit_of_frameCheck sha512CICheck_true

/-- The check of the SHA-512 compression kernel at a frame size `F` that is the frame of its
    code. -/
theorem sha512_check_at {F : Nat} (hF : F + redZone + 8 ≤ 2 ^ 64)
    (hc : F = codeFrame sha512Abi (nfAbiNames "sha512_compress" sha512Abi)
      (NFProg.ofCom (sha2CompressBodyP sha512P))) :
    (sha512Data F hF).check = true := by
  refine ProgKernelData.check_of_frameCheck (d := (sha512Data F hF).toProgKernelData)
    (σ := sha512Abi) rfl ?_ ?_
  · dsimp only [sha512Data, TemplateKernelData.toProgKernelData, TemplateKernelData.prog]
    exact hc
  · dsimp only [sha512Data, TemplateKernelData.toProgKernelData, TemplateKernelData.prog]
    exact sha512CICheck_true

/-- **The check of the SHA-512 compression kernel** at the frame of its code. -/
theorem sha512_check : (sha512Data sha512Frame sha512Frame_fit).check = true :=
  sha512_check_at sha512Frame_fit (by rw [sha512Frame])

/-- The parameters of the data of the SHA-512 compression kernel. -/
theorem sha512_ins : layoutIns sha512Abi = [("RDI", .words 8), ("RSI", .words 24)] := by
  native_decide

/-- The argument registers of the layout are the physical registers of its parameters. -/
theorem sha512_args : sha512Abi.args.map (fun a => (a.reg, a.kind)) =
    [("RDI", ArgKind.words 8), ("RSI", ArgKind.words 24)].map
      fun q => (X86Backend.DecodePrinted.phys q.1, q.2) := by
  decide

/-- **The linked function of the SHA-512 compression**: the region-compiled template under
    `redLayout sha512Abi sha512Frame`, with the meaning the reference compression, the frame
    size `sha512Frame` of the code and the store policy `sha512Pol`. -/
def sha512Kernel : LinkedFn := (sha512Data sha512Frame sha512Frame_fit).kernel sha512_check

/-- **The code of the SHA-512 compression meets the contract of its record.** -/
theorem sha512Kernel_meets : sha512Kernel.Meets :=
  TemplateKernelData.meets sha512_check

/-- **The SHA-512 compression is a linked kernel** of the out shape, with the destination at
    `%rdi`. -/
theorem sha512Kernel_linked : LinkedKernel sha512Kernel :=
  TemplateKernelData.linked (po := "RDI") sha512_check
    ((layoutIns_redLayout _ _).trans sha512_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans sha512_args)
    (by simp [sha512Data]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked
