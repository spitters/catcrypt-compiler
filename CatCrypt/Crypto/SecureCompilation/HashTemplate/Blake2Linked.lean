/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2LinkedData
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2LinkedData
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose

/-!
# The BLAKE2b compression template as a region-compiled linked function

The BLAKE2b compression template with one input array and an output array,
`blake2CompressBodyP blake2bP`, compiled by the region back half `compileRegion` under the
layout `redLayout blake2bKAbi blake2bKFrame` (the output array `h` of 8 words at `%rdi`, the
flag word `f0` at `%rsi`, the counter words `t1` at `%rdx` and `t0` at `%rcx`, the input array
`hm` of 24 words, the chaining words then the message words, at `%r8`, the result the 8 words
at `%rdi`, and the stack words the frame of the code and the red zone below it), is the
template kernel `blake2bKData`, whose linked function `blake2bKernel` has the meaning the
reference compression `blake2CompressRef blake2bP`.

## Main definitions

* `blake2bKAbi` (module `Blake2LinkedData`): the layout at which the frame size of the code
  is read.
* `blake2bKFrame`, `blake2bKPol`: the frame size of the code and its store policy.
* `blake2bKRef`: the reference compression on source values.
* `blake2bKData`: the data of the template kernel at a frame size.
* `blake2bKernel`: the linked function of the compiled template.

## Main statements

* `blake2bKCICheck_true`, `blake2bK_check`: the template compiles at the frame of its code,
  the layout passes the footprint check, the template the read-only check, and the decoded
  block the clobber check.
* `blake2bKernel_meets`: the code of the kernel meets the contract of its record.
* `blake2bKernel_linked`: the kernel is a linked kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked

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

/-- The registers the code of the BLAKE2b compression may change: every general-purpose
    register other than the stack register. -/
def blake2bKClob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- **The frame size of the code of the BLAKE2b compression**: `codeFrame` of the compiled
    template under `blake2bKAbi`. -/
def blake2bKFrame : Nat :=
  codeFrame blake2bKAbi (nfAbiNames "blake2b_compress" blake2bKAbi)
    (NFProg.ofCom (blake2CompressBodyP blake2bP))

/-- **The store policy of the BLAKE2b compression**: the red zone of `redZone` bytes, and the
    out window of the 8 words of the output array at the entry value of `%rdi`. -/
def blake2bKPol : StorePol := ⟨redZone, [("%rdi", 0, 64)]⟩

/-! ## 2. The meaning -/

/-- The input array of the compression splits into its chaining words and its message
    words. -/
theorem blake2InWords_split {w : Nat} (a : Fin 24 → BitVec w) :
    blake2InWords (fun i : Fin 8 => a ⟨i.1, by omega⟩) (fun j : Fin 16 => a ⟨8 + j.1, by omega⟩)
      = a := by
  funext i
  simp only [blake2InWords]
  split_ifs <;> exact congrArg a (Fin.ext (by grind))

/-- **The reference compression on source values** of the parameters `h`, `f0`, `t1`, `t0`
    and `hm`: the output array decoded as an array of 8 words, the input array as an array of
    24 words, the scalars as words, and the eight words of `blake2CompressRef blake2bP` at the
    chaining words and the message words of the input array. -/
def blake2bKRef (vals : List Value) : Option (Fin 8 → BitVec 64) :=
  match vals with
  | [hv, f0v, t1v, t0v, hmv] =>
      (dec (.arr 8 (.word 64)) hv).bind fun _ =>
      (dec (.arr 24 (.word 64)) hmv).bind fun hm =>
      (dec (.word 64) t0v).bind fun t0 =>
      (dec (.word 64) t1v).bind fun t1 =>
      (dec (.word 64) f0v).map fun f0 =>
        blake2bP.blake2CompressRef (fun i => hm ⟨i.1, by omega⟩)
          (fun j => hm ⟨8 + j.1, by omega⟩) t0 t1 f0
  | _ => none

/-- The reference compression returns values only on arguments of the kinds of the
    layout. -/
theorem blake2bK_ref_kinds : ∀ vals r, blake2bKRef vals = some r →
    vals.map valKind = blake2bKAbi.args.map (·.kind) := by
  intro vals r h
  rcases vals with _ | ⟨hv, _ | ⟨f0v, _ | ⟨t1v, _ | ⟨t0v, _ | ⟨hmv, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
    simp only [blake2bKRef, reduceCtorEq] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, h5⟩ := h
  obtain ⟨_, h6, -⟩ := Option.map_eq_some_iff.mp h5
  simp only [List.map_cons, List.map_nil, valKind_of_dec_arr h1, valKind_of_dec_arr h2,
    valKind_of_dec_word h3, valKind_of_dec_word h4, valKind_of_dec_word h6]
  rfl

/-! ## 3. The valuation of the layout -/

/-- The valuation of the BLAKE2b compression read off the entry state `sa`: the 24 words at
    `%r8`, the registers `%rcx`, `%rdx`, `%rsi`, and the 8 words at `%rdi`. -/
def blake2bKVal (sa : AState) : Ctxt.Valuation (blake2InCtxtP 64) :=
  .cons (wordsFn sa (sa.regs "%r8") 24) (.cons (sa.regs "%rcx") (.cons (sa.regs "%rdx")
    (.cons (sa.regs "%rsi") (.cons (wordsFn sa (sa.regs "%rdi") 8) .nil))))

theorem abiValOf_blake2bK (sa : AState) : AbiValOf blake2bKAbi sa (blake2bKVal sa) where
  arg := fun v => by
    rcases v with _ | _ | _ | _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | _ | _ | _ | ⟨⟨⟩⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl⟩
  arr := fun v => by
    rcases v with _ | _ | _ | _ | _ | ⟨⟨⟩⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- **The reference compression at the layout reading**: at the source values the layout
    reads off the entry state `sa`, the reference compression returns the value of the
    template at `blake2bKVal sa`. -/
theorem blake2bK_ref_read (sa : AState) :
    blake2bKRef (blake2bKAbi.args.map (·.read sa)) =
      some ((blake2CompressBodyP blake2bP).denote (blake2bKVal sa)) := by
  have hvals : blake2bKAbi.args.map (·.read sa) = [.array (wordsAt sa.mem (sa.regs "%rdi") 8),
      CatCrypt.Crypto.Hax.wordVal (sa.regs "%rsi"), CatCrypt.Crypto.Hax.wordVal (sa.regs "%rdx"),
      CatCrypt.Crypto.Hax.wordVal (sa.regs "%rcx"), .array (wordsAt sa.mem (sa.regs "%r8") 24)] :=
    rfl
  rw [hvals]
  simp only [blake2bKRef, X86Backend.LinkedFnCallee.dec_arr_wordsAt,
    CatCrypt.Crypto.Hax.dec_wordVal, Option.bind_some]
  have h := blake2CompressBodyP_value blake2bP
    (fun i : Fin 8 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
      (sa.regs "%r8") i.1))
    (fun j : Fin 16 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
      (sa.regs "%r8") (8 + j.1)))
    (sa.regs "%rcx") (sa.regs "%rdx") (sa.regs "%rsi") (wordsFn sa (sa.regs "%rdi") 8)
  have hw : blake2InWords (w := blake2bP.w)
      (fun i : Fin 8 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
        (sa.regs "%r8") i.1))
      (fun j : Fin 16 => Ascent.AddrMem.read64 sa.mem (X86Backend.ImageAddrSim.cellAt
        (sa.regs "%r8") (8 + j.1))) = wordsFn sa (sa.regs "%r8") 24 :=
    blake2InWords_split (wordsFn sa (sa.regs "%r8") 24)
  rw [hw] at h
  exact congrArg some h.symm

/-! ## 4. The template kernel -/

/-- **The data of the BLAKE2b compression kernel** at the frame size `F`, under the layout
    `redLayout blake2bKAbi F`. -/
def blake2bKData (F : Nat) (hF : F + redZone + 8 ≤ 2 ^ 64) : TemplateKernelData where
  name := "blake2b_compress"
  params := [("h", .arr 8 (.word 64)), ("f0", .word 64), ("t1", .word 64), ("t0", .word 64),
    ("hm", .arr 24 (.word 64))]
  Γ := blake2InCtxtP 64
  nOut := 8
  body := blake2CompressBodyP blake2bP
  layout := redLayout blake2bKAbi F
  clob := blake2bKClob
  frame := F
  pol := blake2bKPol
  outReg := "%rdi"
  ref := blake2bKRef
  val := blake2bKVal
  events := blake2CompressBodyP_events blake2bP JLeakParams.owned (fun _ => rfl)
  abiValOf_val sa := abiValOf_redLayout (abiValOf_blake2bK sa)
  regArr := by decide
  ref_read := blake2bK_ref_read
  ref_kinds := blake2bK_ref_kinds
  kinds_eq := rfl
  arity := rfl
  args_nodup := (by decide : (blake2bKAbi.args.map (·.reg)).Nodup)
  pubWords := rfl
  result := rfl
  bounds := rfl
  regions_nodup := (by decide : blake2bKAbi.regions.Nodup)
  regions_ro :=
    (by decide : (blake2bKAbi.regions.filter fun p => !isResRegion blake2bKAbi p).length ≤ 1)
  frameHi := (by decide : blake2bKAbi.frameHi ≤ -8)
  out_region := (by decide : ("%rdi", 8) ∈ blake2bKAbi.regions)
  out_fit := by norm_num
  wins := by decide
  result_regs := (by decide : ∀ r ∈ resultRegs blake2bKAbi.result, r ∈ abiRegs blake2bKAbi)
  frame_fit := redLayout_frame_fit hF

/-- The check of the BLAKE2b compression kernel at the frame size of its code: `frameCheck`
    of the template under `blake2bKAbi`, one evaluation of the back half. -/
def blake2bKCICheck : Bool :=
  frameCheck blake2bKAbi (nfAbiNames "blake2b_compress" blake2bKAbi)
    (NFProg.ofCom (blake2CompressBodyP blake2bP)) blake2bKPol blake2bKClob

set_option linter.style.native false in
/-- **The check of the compiled BLAKE2b compression at the frame of its code**: the frame with
    the red zone fits, the back half succeeds at `redLayout blake2bKAbi blake2bKFrame`, the
    layout passes `layoutFootRoB`, the template passes the read-only check, and the decoded
    block passes `clobOkB` at `blake2bKClob`. -/
theorem blake2bKCICheck_true : blake2bKCICheck = true := by
  native_decide

/-- The frame of the code of the BLAKE2b compression fits with its red zone. -/
theorem blake2bKFrame_fit : blake2bKFrame + redZone + 8 ≤ 2 ^ 64 := by
  rw [blake2bKFrame]
  exact fit_of_frameCheck blake2bKCICheck_true

/-- The check of the BLAKE2b compression kernel at a frame size `F` that is the frame of its
    code. -/
theorem blake2bK_check_at {F : Nat} (hF : F + redZone + 8 ≤ 2 ^ 64)
    (hc : F = codeFrame blake2bKAbi (nfAbiNames "blake2b_compress" blake2bKAbi)
      (NFProg.ofCom (blake2CompressBodyP blake2bP))) :
    (blake2bKData F hF).check = true := by
  refine ProgKernelData.check_of_frameCheck (d := (blake2bKData F hF).toProgKernelData)
    (σ := blake2bKAbi) rfl ?_ ?_
  · dsimp only [blake2bKData, TemplateKernelData.toProgKernelData, TemplateKernelData.prog]
    exact hc
  · dsimp only [blake2bKData, TemplateKernelData.toProgKernelData, TemplateKernelData.prog]
    exact blake2bKCICheck_true

/-- **The check of the BLAKE2b compression kernel** at the frame of its code. -/
theorem blake2bK_check : (blake2bKData blake2bKFrame blake2bKFrame_fit).check = true :=
  blake2bK_check_at blake2bKFrame_fit (by rw [blake2bKFrame])

/-- The parameters of the data of the BLAKE2b compression kernel. -/
theorem blake2bK_ins : layoutIns blake2bKAbi = [("RDI", .words 8), ("RSI", .scalar),
    ("RDX", .scalar), ("RCX", .scalar), ("R8", .words 24)] := by
  native_decide

/-- The argument registers of the layout are the physical registers of its parameters. -/
theorem blake2bK_args : blake2bKAbi.args.map (fun a => (a.reg, a.kind)) =
    [("RDI", ArgKind.words 8), ("RSI", ArgKind.scalar), ("RDX", ArgKind.scalar),
      ("RCX", ArgKind.scalar), ("R8", ArgKind.words 24)].map
      fun q => (X86Backend.DecodePrinted.phys q.1, q.2) := by
  decide

/-- **The linked function of the BLAKE2b compression**: the region-compiled template under
    `redLayout blake2bKAbi blake2bKFrame`, with the meaning the reference compression, the
    frame size `blake2bKFrame` of the code and the store policy `blake2bKPol`. -/
def blake2bKernel : LinkedFn :=
  (blake2bKData blake2bKFrame blake2bKFrame_fit).kernel blake2bK_check

/-- **The code of the BLAKE2b compression meets the contract of its record.** -/
theorem blake2bKernel_meets : blake2bKernel.Meets :=
  TemplateKernelData.meets blake2bK_check

/-- **The BLAKE2b compression is a linked kernel** of the out shape, with the destination at
    `%rdi`. -/
theorem blake2bKernel_linked : LinkedKernel blake2bKernel :=
  TemplateKernelData.linked (po := "RDI") blake2bK_check
    ((layoutIns_redLayout _ _).trans blake2bK_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans blake2bK_args)
    (by simp [blake2bKData]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked
