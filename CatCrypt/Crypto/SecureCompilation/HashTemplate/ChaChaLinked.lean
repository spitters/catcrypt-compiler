/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.ChaCha
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.ChaCha
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.NarrowKernel
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.NarrowKernel

/-!
# The ChaCha20 block template as a narrow-width linked function

The ChaCha20 block program `chachaBlockBody`, over 32-bit words, compiled by the region back
half `compileRegion` under the u64-slot layout `redLayout chachaKAbi chachaKFrame`: the input
state `S` of 16 slots at `%rdi`, the output array `O` of 16 slots at `%rsi`, each slot a 64-bit
word holding a 32-bit word with zero high bits, and the result the 16 slots at `%rsi`. It is
the narrow-width template kernel `chachaKData`, whose linked function `chachaKernel` has the
meaning the reference block function `chachaBlock` on arguments whose words lie below
`2 ^ 32`, with the result words zero extended.

## Main definitions

* `chachaKAbi`, `chachaKFrame`, `chachaKPol`, `chachaKClob`: the layout at which the frame size
  of the code is read, the frame size, the store policy and the clobber set.
* `chachaKRef`: the reference block function on source values.
* `chachaKData`: the data of the narrow-width template kernel at a frame size.
* `chachaKernel`, `chachaKernelAbi`: the linked function of the compiled template, and its
  System V form.

## Main results

* `chachaKCICheck_true`, `chachaK_check`: the template compiles at the frame of its code and
  passes the footprint, read-only, level and clobber checks.
* `chachaKernel_meets`, `chachaKernel_linked`: the code of the kernel meets the contract of
  its record, and the kernel is a linked kernel.
* `chachaKernelAbi_meets`, `chachaKernelAbi_linked`: the same at the System V convention.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.ChaChaLinked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords (mapVal)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.Hax (LinkedFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (isResRegion)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs)
open CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked (lo32 setWidth_lo32)
open CatCrypt.Crypto.SecureCompilation.HashTemplate (chachaBlockBody chachaInCtxt
  chachaBlockBody_value)
open CatCrypt.Crypto.Jasmin.ChaCha20Block (chachaBlock)
open _root_.Hax (Value)

/-! ## 1. The layout -/

/-- **The u64-slot layout of the ChaCha20 block** at which the frame size of the code is read:
    the input state `s` (16 slots) at `%rdi`, the output array `o` (16 slots) at `%rsi`, the
    result the 16 slots at `%rsi`, and the stack words at the displacements from `-4096` to
    `-8`. -/
def chachaKAbi : AbiLayout :=
  AbiLayout.mk [⟨"o", "%rsi", .words 16⟩, ⟨"s", "%rdi", .words 16⟩] [] (.words "%rsi" 16) []
    (-4096) (-8) [] []

/-- The registers the code of the ChaCha20 block may change: every general-purpose register
    other than the stack register. -/
def chachaKClob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- **The frame size of the code of the ChaCha20 block**: `codeFrame` of the compiled program
    under `chachaKAbi`. -/
def chachaKFrame : Nat :=
  codeFrame chachaKAbi (nfAbiNames "chacha20_block" chachaKAbi)
    (NFProg.ofCom chachaBlockBody)

/-- **The store policy of the ChaCha20 block**: the red zone of `redZone` bytes, and the out
    window of the 16 slots of the output array at the entry value of `%rsi`. -/
def chachaKPol : StorePol := ⟨redZone, [("%rsi", 0, 128)]⟩

/-! ## 2. The meaning -/

/-- **The reference block function on source values** of the parameters `s` and `o`: both
    arrays decoded as arrays of 16 words; where every word lies below `2 ^ 32`, the sixteen
    words of `chachaBlock` at the low halves of the input state. -/
def chachaKRef (vals : List Value) : Option (Fin 16 → BitVec 32) :=
  match vals with
  | [ov, sv] =>
      (dec (.arr 16 (.word 64)) sv).bind fun s =>
      (dec (.arr 16 (.word 64)) ov).bind fun o =>
        if (∀ i, (s i).toNat < 2 ^ 32) ∧ (∀ i, (o i).toNat < 2 ^ 32) then
          some (chachaBlock (fun i => lo32 (s i)))
        else none
  | _ => none

/-- The reference block function returns values only on arguments of the kinds of the
    layout. -/
theorem chachaK_ref_kinds : ∀ vals r, chachaKRef vals = some r →
    vals.map valKind = chachaKAbi.args.map (·.kind) := by
  intro vals r h
  rcases vals with _ | ⟨ov, _ | ⟨sv, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [chachaKRef, reduceCtorEq] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, -⟩ := h
  simp only [List.map_cons, List.map_nil, valKind_of_dec_arr h1, valKind_of_dec_arr h2]
  rfl

/-! ## 3. The valuation of the layout -/

/-- The narrow valuation of the entry state `sa`: the low halves of the 16 slots at `%rdi` and
    of the 16 slots at `%rsi`. -/
def chachaKNVal (sa : AState) : Ctxt.Valuation chachaInCtxt :=
  .cons (fun i => lo32 (wordsFn sa (sa.regs "%rdi") 16 i))
    (.cons (fun i => lo32 (wordsFn sa (sa.regs "%rsi") 16 i)) .nil)

/-- **The reference block function at the layout reading**: where the reference function
    returns `r` at the source values the layout reads off the entry state `sa`, the layout
    reads the widening of the narrow valuation `chachaKNVal sa`, at which the program has the
    value `r`. -/
theorem chachaK_ref_read (sa : AState) (r : Fin 16 → BitVec 32)
    (h : chachaKRef (chachaKAbi.args.map (·.read sa)) = some r) :
    ∃ V : Ctxt.Valuation chachaInCtxt, AbiValOf chachaKAbi sa (mapVal V) ∧
      chachaBlockBody.denote V = r := by
  have hvals : chachaKAbi.args.map (·.read sa) = [.array (wordsAt sa.mem (sa.regs "%rsi") 16),
      .array (wordsAt sa.mem (sa.regs "%rdi") 16)] :=
    rfl
  rw [hvals] at h
  dsimp only [chachaKRef] at h
  rw [X86Backend.LinkedFnCallee.dec_arr_wordsAt, X86Backend.LinkedFnCallee.dec_arr_wordsAt,
    Option.bind_some, Option.bind_some] at h
  split at h
  · rename_i hr
    obtain ⟨h1, h2⟩ := hr
    obtain rfl := (Option.some.inj h).symm
    refine ⟨chachaKNVal sa, ?_, ?_⟩
    · exact
        { arg := fun v => by
            rcases v with _ | _ | ⟨⟨⟩⟩ <;> rfl
          reg := fun v => by
            rcases v with _ | _ | ⟨⟨⟩⟩
          arr := fun v => by
            rcases v with _ | _ | ⟨⟨⟩⟩
            · exact ⟨_, rfl, rfl, rfl, funext fun i => setWidth_lo32 (h1 i)⟩
            · exact ⟨_, rfl, rfl, rfl, funext fun i => setWidth_lo32 (h2 i)⟩ }
    · exact chachaBlockBody_value _ _
  · cases h

/-! ## 4. The template kernel -/

/-- **The data of the ChaCha20 block kernel** at the frame size `F`, under the layout
    `redLayout chachaKAbi F`. -/
def chachaKData (F : Nat) (hF : F + redZone + 8 ≤ 2 ^ 64) : NarrowTemplateKernelData where
  name := "chacha20_block"
  params := [("o", .arr 16 (.word 64)), ("s", .arr 16 (.word 64))]
  Γ := chachaInCtxt
  w := 32
  hw := rfl
  nOut := 16
  body := chachaBlockBody
  layout := redLayout chachaKAbi F
  clob := chachaKClob
  frame := F
  pol := chachaKPol
  outReg := "%rsi"
  ref := chachaKRef
  regArr := by decide
  ref_read sa r h := by
    obtain ⟨V, hV, hb⟩ := chachaK_ref_read sa r h
    exact ⟨V, abiValOf_redLayout hV, hb⟩
  ref_kinds := chachaK_ref_kinds
  kinds_eq := rfl
  arity := rfl
  args_nodup := (by decide : (chachaKAbi.args.map (·.reg)).Nodup)
  pubWords := rfl
  result := rfl
  bounds := rfl
  regions_nodup := (by decide : chachaKAbi.regions.Nodup)
  regions_ro :=
    (by decide : (chachaKAbi.regions.filter fun p => !isResRegion chachaKAbi p).length ≤ 1)
  frameHi := (by decide : chachaKAbi.frameHi ≤ -8)
  out_region := (by decide : ("%rsi", 16) ∈ chachaKAbi.regions)
  out_fit := by norm_num
  wins := by decide
  result_regs := (by decide : ∀ r ∈ resultRegs chachaKAbi.result, r ∈ abiRegs chachaKAbi)
  frame_fit := redLayout_frame_fit hF

/-- The check of the ChaCha20 block kernel at the frame size of its code:
    `narrowFrameCheck` of the program under `chachaKAbi`, one evaluation of the back half
    and the level check of the widened program. -/
def chachaKCICheck : Bool :=
  narrowFrameCheck chachaKAbi (nfAbiNames "chacha20_block" chachaKAbi)
    (NFProg.ofCom chachaBlockBody) chachaKPol chachaKClob

set_option linter.style.native false in
/-- **The check of the compiled ChaCha20 block at the frame of its code**: the frame with the
    red zone fits, the back half succeeds at `redLayout chachaKAbi chachaKFrame`, the layout
    passes `layoutFootRoB`, the widened program passes the read-only check and the level
    check, and the decoded block passes `clobOkB` at `chachaKClob`. -/
theorem chachaKCICheck_true : chachaKCICheck = true := by
  native_decide

/-- The frame of the code of the ChaCha20 block fits with its red zone. -/
theorem chachaKFrame_fit : chachaKFrame + redZone + 8 ≤ 2 ^ 64 := by
  rw [chachaKFrame]
  exact fit_of_narrowFrameCheck chachaKCICheck_true

/-- **The check of the ChaCha20 block kernel** at the frame of its code. -/
theorem chachaK_check : (chachaKData chachaKFrame chachaKFrame_fit).check = true := by
  refine NarrowProgKernelData.check_of_frameCheck
    (d := (chachaKData chachaKFrame chachaKFrame_fit).toNarrowProgKernelData)
    (σ := chachaKAbi)
    (by dsimp only [chachaKData, NarrowTemplateKernelData.toNarrowProgKernelData]) ?_ ?_
  · dsimp only [chachaKData, NarrowTemplateKernelData.toNarrowProgKernelData,
      NarrowTemplateKernelData.prog]
    rw [chachaKFrame]
  · dsimp only [chachaKData, NarrowTemplateKernelData.toNarrowProgKernelData,
      NarrowTemplateKernelData.prog]
    exact chachaKCICheck_true

set_option linter.style.native false in
/-- The parameters of the data of the ChaCha20 block kernel. -/
theorem chachaK_ins : layoutIns chachaKAbi = [("RSI", .words 16), ("RDI", .words 16)] := by
  native_decide

/-- The argument registers of the layout are the physical registers of its parameters. -/
theorem chachaK_args : chachaKAbi.args.map (fun a => (a.reg, a.kind)) =
    [("RSI", ArgKind.words 16), ("RDI", ArgKind.words 16)].map
      fun q => (X86Backend.DecodePrinted.phys q.1, q.2) := by
  decide

/-- **The linked function of the ChaCha20 block**: the region-compiled program under
    `redLayout chachaKAbi chachaKFrame`, with the meaning the reference block function on
    arguments below `2 ^ 32`, the frame size `chachaKFrame` of the code and the store policy
    `chachaKPol`. -/
def chachaKernel : LinkedFn :=
  (chachaKData chachaKFrame chachaKFrame_fit).kernel chachaK_check

/-- **The code of the ChaCha20 block meets the contract of its record.** -/
theorem chachaKernel_meets : chachaKernel.Meets :=
  NarrowTemplateKernelData.meets chachaK_check

/-- **The ChaCha20 block is a linked kernel** of the out shape, with the destination at
    `%rsi`. -/
theorem chachaKernel_linked : LinkedKernel chachaKernel :=
  NarrowTemplateKernelData.linked (po := "RSI") chachaK_check
    ((layoutIns_redLayout _ _).trans chachaK_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans chachaK_args)
    (by simp [chachaKData]) (by decide) rfl

/-- **The linked function of the ChaCha20 block at the System V convention**: the code of
    `chachaKernel` at the clobber set without the callee-saved registers. -/
def chachaKernelAbi : LinkedFn :=
  (chachaKData chachaKFrame chachaKFrame_fit).abiKernel chachaK_check

/-- **The code of the ChaCha20 block meets the contract at the System V convention.** -/
theorem chachaKernelAbi_meets : chachaKernelAbi.Meets :=
  NarrowTemplateKernelData.meets_abi chachaK_check

/-- **The ChaCha20 block at the System V convention is a linked kernel** of the out shape,
    with the destination at `%rsi`. -/
theorem chachaKernelAbi_linked : LinkedKernel chachaKernelAbi :=
  NarrowTemplateKernelData.linked_abi (po := "RSI") chachaK_check
    ((layoutIns_redLayout _ _).trans chachaK_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans chachaK_args)
    (by simp [chachaKData]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.ChaChaLinked
