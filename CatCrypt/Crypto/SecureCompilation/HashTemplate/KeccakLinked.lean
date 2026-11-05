/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Keccak
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Keccak
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinkedData
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinkedData
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose

/-!
# The Keccak-f[1600] permutation as a region-compiled linked function

The Keccak-f[1600] template `keccakFBody`, read over the context of the two arrays of the
layout `keccakFAbi` (`keccakFLayoutBody`: the output array `dst` of 25 words at `%rdi`, the input
array `src` of 25 words at `%rsi`, the result the 25 words at `%rdi`), compiled by the region
back half `compileRegion`, is the template kernel `keccakFData`, whose linked function
`keccakFKernel` has the meaning the permutation `Primitives.Keccak.keccakF` on the 25 lanes of
the input array, the lane `(x, y)` at the index `5 * y + x`.

The frame size `keccakFFrame` of the code is read off the compiled code under `keccakFAbi`
(`codeFrame`), and the kernel has the layout `redLayout keccakFAbi keccakFFrame`, whose stack
words are the frame of the code and the red zone below it. The check `keccakFCICheck` (the
frame fits and the template check holds at it) is decided by evaluation.

## Main definitions

* `keccakFAbi` (module `KeccakLinkedData`): the layout of `keccak_f(dst, src)` at which the
  frame size of the code is read.
* `keccakFLayoutBody` (module `KeccakLinkedData`): the template over the context of the input
  and the output array.
* `keccakFRef`: the reference permutation on source values.
* `keccakFFrame`: the frame size of the compiled code.
* `keccakFData`: the data of the template kernel at a frame size.
* `keccakFKernel`: the linked function of the compiled template.

## Main statements

* `keccakFCICheck_true`, `keccakF_check`: the check of `keccakFData` at the frame of its code.
* `keccakFKernel_meets`: the code of the kernel meets the contract of its record.
* `keccakF_linked`: the kernel is a linked kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (isResRegion)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (leakFixed_rename)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.Hax (LinkedFn)
open _root_.Hax (Value)

/-! ## 1. The layout -/

/-- The registers the code of the permutation may change: every general-purpose register
    other than the stack register. -/
def keccakFClob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- The store policy of the code of the permutation: the red zone of `redZone` bytes, and the
    out window of the 200 bytes of the output array at `%rdi`. -/
def keccakFPol : StorePol := ⟨redZone, [("%rdi", 0, 200)]⟩

/-! ## 2. The meaning -/

/-- **The reference permutation on source values** of the parameters `dst` and `src`: both
    decoded as arrays of 25 words, and the lanes of `Primitives.Keccak.keccakF` of the lanes of
    the input array. -/
def keccakFRef (vals : List Value) : Option (Fin 25 → BitVec 64) :=
  match vals with
  | [dv, sv] =>
      (dec (.arr 25 (.word 64)) dv).bind fun _ =>
      (dec (.arr 25 (.word 64)) sv).map fun x =>
        keccakTToArr (Primitives.Keccak.keccakF (keccakTOfArr x))
  | _ => none

/-- The reference permutation returns values only on arguments of the kinds of the
    layout. -/
theorem keccakF_ref_kinds : ∀ vals r, keccakFRef vals = some r →
    vals.map valKind = keccakFAbi.args.map (·.kind) := by
  intro vals r h
  unfold keccakFRef at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp h
    simp only [List.map_cons, List.map_nil, valKind_of_dec_arr hx, valKind_of_dec_arr hy]
    rfl
  · cases h

/-! ## 3. The valuation of the layout -/

/-- The valuation of the permutation read off the entry state `sa`: the 25 words at `%rsi`
    and the 25 words at `%rdi`. -/
def keccakFVal (sa : AState) : Ctxt.Valuation keccakFCtxt :=
  .cons (wordsFn sa (sa.regs "%rsi") 25) (.cons (wordsFn sa (sa.regs "%rdi") 25) .nil)

/-- The layout reads `keccakFVal sa` off the entry state `sa`. -/
theorem abiValOf_keccakF (sa : AState) : AbiValOf keccakFAbi sa (keccakFVal sa) where
  arg := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩
  arr := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- **The reference permutation at the layout reading**: at the source values the layout
    reads off the entry state `sa`, the reference permutation returns the value of the
    template at `keccakFVal sa`. -/
theorem keccakF_ref_read (sa : AState) :
    keccakFRef (keccakFAbi.args.map (·.read sa)) =
      some (keccakFLayoutBody.denote (keccakFVal sa)) := by
  have hvals : keccakFAbi.args.map (·.read sa) = [.array (wordsAt sa.mem (sa.regs "%rdi") 25),
      .array (wordsAt sa.mem (sa.regs "%rsi") 25)] :=
    rfl
  have hcomap : (keccakFVal sa).comap keccakFHom = .cons (wordsFn sa (sa.regs "%rsi") 25) .nil :=
    by rfl
  rw [hvals, keccakFLayoutBody, Com.denote_rename, hcomap, keccakFBody_value]
  simp only [keccakFRef, X86Backend.LinkedFnCallee.dec_arr_wordsAt, Option.bind_some,
    Option.map_some]
  rfl

/-! ## 4. The template kernel -/

/-- **The data of the Keccak-f[1600] kernel** at the frame size `F`, under the layout
    `redLayout keccakFAbi F`. -/
def keccakFData (F : Nat) (hF : F + redZone + 8 ≤ 2 ^ 64) : TemplateKernelData where
  name := "keccak_f"
  params := [("dst", .arr 25 (.word 64)), ("src", .arr 25 (.word 64))]
  Γ := keccakFCtxt
  nOut := 25
  body := keccakFLayoutBody
  layout := redLayout keccakFAbi F
  clob := keccakFClob
  frame := F
  pol := keccakFPol
  outReg := "%rdi"
  ref := keccakFRef
  val := keccakFVal
  events := leakFixed_rename _ keccakFHom (keccakFBody_events JLeakParams.owned (fun _ => rfl))
  abiValOf_val sa := abiValOf_redLayout (abiValOf_keccakF sa)
  regArr := by decide
  ref_read := keccakF_ref_read
  ref_kinds := keccakF_ref_kinds
  kinds_eq := rfl
  arity := rfl
  args_nodup := (by decide : (keccakFAbi.args.map (·.reg)).Nodup)
  pubWords := rfl
  result := rfl
  bounds := rfl
  regions_nodup := (by decide : keccakFAbi.regions.Nodup)
  regions_ro :=
    (by decide : (keccakFAbi.regions.filter fun p => !isResRegion keccakFAbi p).length ≤ 1)
  frameHi := (by decide : keccakFAbi.frameHi ≤ -8)
  out_region := (by decide : ("%rdi", 25) ∈ keccakFAbi.regions)
  out_fit := by norm_num
  wins := by decide
  result_regs := (by decide : ∀ r ∈ resultRegs keccakFAbi.result, r ∈ abiRegs keccakFAbi)
  frame_fit := redLayout_frame_fit hF

/-! ## 5. The frame and the check -/

/-- **The frame size of the compiled permutation**: `codeFrame` of the compiled template under
    `keccakFAbi` at the symbol `keccak_f`. -/
def keccakFFrame : Nat :=
  codeFrame keccakFAbi (nfAbiNames "keccak_f" keccakFAbi) (NFProg.ofCom keccakFLayoutBody)

/-- The check of the Keccak-f[1600] kernel at the frame size of its code: `frameCheck` of the
    template under `keccakFAbi`, one evaluation of the back half. -/
def keccakFCICheck : Bool :=
  frameCheck keccakFAbi (nfAbiNames "keccak_f" keccakFAbi) (NFProg.ofCom keccakFLayoutBody)
    keccakFPol keccakFClob

set_option linter.style.native false in
/-- **The check of the compiled permutation at the frame of its code**: the frame with the red
    zone fits, the back half succeeds at `redLayout keccakFAbi keccakFFrame`, the layout
    passes `layoutFootRoB`, the template passes the read-only check, and the decoded block
    passes `clobOkB` at `keccakFClob`. -/
theorem keccakFCICheck_true : keccakFCICheck = true := by
  native_decide

/-- The frame of the compiled permutation fits with its red zone. -/
theorem keccakFFrame_fit : keccakFFrame + redZone + 8 ≤ 2 ^ 64 := by
  rw [keccakFFrame]
  exact fit_of_frameCheck keccakFCICheck_true

/-- The check of the Keccak-f[1600] kernel at a frame size `F` that is the frame of its
    code. -/
theorem keccakF_check_at {F : Nat} (hF : F + redZone + 8 ≤ 2 ^ 64)
    (hc : F = codeFrame keccakFAbi (nfAbiNames "keccak_f" keccakFAbi)
      (NFProg.ofCom keccakFLayoutBody)) :
    (keccakFData F hF).check = true := by
  refine ProgKernelData.check_of_frameCheck (d := (keccakFData F hF).toProgKernelData)
    (σ := keccakFAbi) rfl ?_ ?_
  · dsimp only [keccakFData, TemplateKernelData.toProgKernelData, TemplateKernelData.prog]
    exact hc
  · dsimp only [keccakFData, TemplateKernelData.toProgKernelData, TemplateKernelData.prog]
    exact keccakFCICheck_true

/-- **The check of the Keccak-f[1600] kernel** at the frame of its code. -/
theorem keccakF_check : (keccakFData keccakFFrame keccakFFrame_fit).check = true :=
  keccakF_check_at keccakFFrame_fit (by rw [keccakFFrame])

set_option linter.style.native false in
/-- The parameters of the layout: the output array of 25 words at `RDI` and the input array of
    25 words at `RSI`. -/
theorem keccakF_ins : layoutIns keccakFAbi = [("RDI", .words 25), ("RSI", .words 25)] := by
  native_decide

/-- The argument registers of the layout are the physical registers of its parameters. -/
theorem keccakF_args : keccakFAbi.args.map (fun a => (a.reg, a.kind)) =
    [("RDI", ArgKind.words 25), ("RSI", ArgKind.words 25)].map
      fun q => (X86Backend.DecodePrinted.phys q.1, q.2) := by
  decide

/-! ## 6. The linked function -/

/-- **The linked function of the Keccak-f[1600] permutation**: the region-compiled template
    under `redLayout keccakFAbi keccakFFrame`, with the meaning the reference permutation, the
    frame size `keccakFFrame` of the code and the store policy `keccakFPol`. -/
def keccakFKernel : LinkedFn :=
  (keccakFData keccakFFrame keccakFFrame_fit).kernel keccakF_check

/-- **The code of the Keccak-f[1600] permutation meets the contract of its record.** -/
theorem keccakFKernel_meets : keccakFKernel.Meets :=
  TemplateKernelData.meets keccakF_check

/-- **The Keccak-f[1600] permutation is a linked kernel** of the out shape, with the
    destination at `%rdi`. -/
theorem keccakF_linked : LinkedKernel keccakFKernel :=
  TemplateKernelData.linked (po := "RDI") keccakF_check
    ((layoutIns_redLayout _ _).trans keccakF_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans keccakF_args)
    (by simp [keccakFData]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.KeccakLinked
