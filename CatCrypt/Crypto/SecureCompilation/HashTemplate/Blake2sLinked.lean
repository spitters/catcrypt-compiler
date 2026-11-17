/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.NarrowKernel
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.NarrowKernel

/-!
# The BLAKE2s compression template as a narrow-width linked function

The BLAKE2s compression template `blake2CompressBodyP blake2sP`, over 32-bit words, compiled
by the region back half `compileRegion` under the u64-slot layout
`redLayout blake2sKAbi blake2sKFrame`: the output array `h` of 8 slots at `%rdi`, the flag
word `f0` at `%rsi`, the counter words `t1` at `%rdx` and `t0` at `%rcx`, the input array `hm`
of 24 slots, the chaining words then the message words, at `%r8`, each slot a 64-bit word
holding a 32-bit word with zero high bits, and the result the 8 slots at `%rdi`. It is the
narrow-width template kernel `blake2sKData`, whose linked function `blake2sKernel` has the
meaning the reference compression `blake2CompressRef blake2sP` on arguments whose words lie
below `2 ^ 32`, with the result words zero extended.

## Main definitions

* `blake2sKAbi`: the layout at which the frame size of the code is read.
* `blake2sKFrame`, `blake2sKPol`: the frame size of the code and its store policy.
* `blake2sKRef`: the reference compression on source values.
* `blake2sKData`: the data of the narrow-width template kernel at a frame size.
* `blake2sKernel`, `blake2sKernelAbi`: the linked function of the compiled template, and its
  System V form.

## Main statements

* `blake2sKCICheck_true`, `blake2sK_check`: the template compiles at the frame of its code and
  passes the footprint, read-only, level and clobber checks.
* `blake2sKernel_meets`, `blake2sKernel_linked`: the code of the kernel meets the contract of
  its record, and the kernel is a linked kernel.
* `blake2sKernelAbi_meets`, `blake2sKernelAbi_linked`: the same at the System V convention.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked

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
open CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2Linked (blake2InWords_split)
open _root_.Hax (Value)

/-! ## 1. The layout -/

/-- **The u64-slot layout of the BLAKE2s compression** at which the frame size of the code is
    read: the output array `h` (8 slots) at `%rdi`, the flag word `f0` at `%rsi`, the counter
    words `t1` at `%rdx` and `t0` at `%rcx`, the input array `hm` (24 slots) at `%r8`, the
    result the 8 slots at `%rdi`, and the stack words at the displacements from `-4096` to
    `-8`. -/
def blake2sKAbi : AbiLayout :=
  AbiLayout.mk [⟨"h", "%rdi", .words 8⟩, ⟨"f0", "%rsi", .scalar⟩, ⟨"t1", "%rdx", .scalar⟩,
    ⟨"t0", "%rcx", .scalar⟩, ⟨"hm", "%r8", .words 24⟩] [] (.words "%rdi" 8) []
    (-4096) (-8) [] []

/-- The registers the code of the BLAKE2s compression may change: every general-purpose
    register other than the stack register. -/
def blake2sKClob : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- **The frame size of the code of the BLAKE2s compression**: `codeFrame` of the compiled
    template under `blake2sKAbi`. -/
def blake2sKFrame : Nat :=
  codeFrame blake2sKAbi (nfAbiNames "blake2s_compress" blake2sKAbi)
    (NFProg.ofCom (blake2CompressBodyP blake2sP))

/-- **The store policy of the BLAKE2s compression**: the red zone of `redZone` bytes, and the
    out window of the 8 slots of the output array at the entry value of `%rdi`. -/
def blake2sKPol : StorePol := ⟨redZone, [("%rdi", 0, 64)]⟩

/-! ## 2. The meaning -/

/-- The low 32 bits of a 64-bit word. -/
def lo32 (x : BitVec 64) : BitVec 32 := x.setWidth 32

/-- A 64-bit word below `2 ^ 32` is the zero extension of its low 32 bits. -/
theorem setWidth_lo32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) : (lo32 x).setWidth 64 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.toNat_setWidth]
  omega

/-- **The reference compression on source values** of the parameters `h`, `f0`, `t1`, `t0` and
    `hm`: the output array decoded as an array of 8 words, the input array as an array of 24
    words, the scalars as words; where every word lies below `2 ^ 32`, the eight words of
    `blake2CompressRef blake2sP` at the low halves of the chaining words and the message words
    of the input array and of the scalars. -/
def blake2sKRef (vals : List Value) : Option (Fin 8 → BitVec 32) :=
  match vals with
  | [hv, f0v, t1v, t0v, hmv] =>
      (dec (.arr 8 (.word 64)) hv).bind fun hh =>
      (dec (.arr 24 (.word 64)) hmv).bind fun hm =>
      (dec (.word 64) t0v).bind fun t0 =>
      (dec (.word 64) t1v).bind fun t1 =>
      (dec (.word 64) f0v).bind fun f0 =>
        if (∀ i, (hh i).toNat < 2 ^ 32) ∧ (∀ i, (hm i).toNat < 2 ^ 32) ∧ t0.toNat < 2 ^ 32
            ∧ t1.toNat < 2 ^ 32 ∧ f0.toNat < 2 ^ 32 then
          some (blake2sP.blake2CompressRef (fun i => lo32 (hm ⟨i.1, by omega⟩))
            (fun j => lo32 (hm ⟨8 + j.1, by omega⟩)) (lo32 t0) (lo32 t1) (lo32 f0))
        else none
  | _ => none

/-- The reference compression returns values only on arguments of the kinds of the
    layout. -/
theorem blake2sK_ref_kinds : ∀ vals r, blake2sKRef vals = some r →
    vals.map valKind = blake2sKAbi.args.map (·.kind) := by
  intro vals r h
  rcases vals with _ | ⟨hv, _ | ⟨f0v, _ | ⟨t1v, _ | ⟨t0v, _ | ⟨hmv, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
    simp only [blake2sKRef, reduceCtorEq] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, _, h5, -⟩ := h
  simp only [List.map_cons, List.map_nil, valKind_of_dec_arr h1, valKind_of_dec_arr h2,
    valKind_of_dec_word h3, valKind_of_dec_word h4, valKind_of_dec_word h5]
  rfl

/-! ## 3. The valuation of the layout -/

/-- The narrow valuation of the entry state `sa`: the low halves of the 24 slots at `%r8`, of
    the registers `%rcx`, `%rdx`, `%rsi`, and of the 8 slots at `%rdi`. -/
def blake2sKNVal (sa : AState) : Ctxt.Valuation (blake2InCtxtP 32) :=
  .cons (fun i => lo32 (wordsFn sa (sa.regs "%r8") 24 i)) (.cons (lo32 (sa.regs "%rcx"))
    (.cons (lo32 (sa.regs "%rdx")) (.cons (lo32 (sa.regs "%rsi"))
      (.cons (fun i => lo32 (wordsFn sa (sa.regs "%rdi") 8 i)) .nil))))

/-- **The reference compression at the layout reading**: where the reference compression
    returns `r` at the source values the layout reads off the entry state `sa`, the layout
    reads the widening of the narrow valuation `blake2sKNVal sa`, at which the template has
    the value `r`. -/
theorem blake2sK_ref_read (sa : AState) (r : Fin 8 → BitVec 32)
    (h : blake2sKRef (blake2sKAbi.args.map (·.read sa)) = some r) :
    ∃ V : Ctxt.Valuation (blake2InCtxtP 32), AbiValOf blake2sKAbi sa (mapVal V) ∧
      (blake2CompressBodyP blake2sP).denote V = r := by
  have hvals : blake2sKAbi.args.map (·.read sa) = [.array (wordsAt sa.mem (sa.regs "%rdi") 8),
      CatCrypt.Crypto.Hax.wordVal (sa.regs "%rsi"), CatCrypt.Crypto.Hax.wordVal (sa.regs "%rdx"),
      CatCrypt.Crypto.Hax.wordVal (sa.regs "%rcx"), .array (wordsAt sa.mem (sa.regs "%r8") 24)] :=
    rfl
  rw [hvals] at h
  simp only [blake2sKRef, X86Backend.LinkedFnCallee.dec_arr_wordsAt,
    CatCrypt.Crypto.Hax.dec_wordVal, Option.bind_some] at h
  split at h
  · rename_i hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    obtain rfl := (Option.some.inj h).symm
    refine ⟨blake2sKNVal sa, ?_, ?_⟩
    · exact
        { arg := fun v => by
            rcases v with _ | _ | _ | _ | _ | ⟨⟨⟩⟩ <;> rfl
          reg := fun v => by
            rcases v with _ | _ | _ | _ | _ | ⟨⟨⟩⟩
            · exact ⟨_, rfl, rfl, rfl, setWidth_lo32 h3⟩
            · exact ⟨_, rfl, rfl, rfl, setWidth_lo32 h4⟩
            · exact ⟨_, rfl, rfl, rfl, setWidth_lo32 h5⟩
          arr := fun v => by
            rcases v with _ | _ | _ | _ | _ | ⟨⟨⟩⟩
            · exact ⟨_, rfl, rfl, rfl, funext fun i => setWidth_lo32 (h2 i)⟩
            · exact ⟨_, rfl, rfl, rfl, funext fun i => setWidth_lo32 (h1 i)⟩ }
    · have hv := blake2CompressBodyP_value blake2sP
        (fun i : Fin 8 => lo32 (wordsFn sa (sa.regs "%r8") 24 ⟨i.1, by omega⟩))
        (fun j : Fin 16 => lo32 (wordsFn sa (sa.regs "%r8") 24 ⟨8 + j.1, by omega⟩))
        (lo32 (sa.regs "%rcx")) (lo32 (sa.regs "%rdx")) (lo32 (sa.regs "%rsi"))
        (fun i => lo32 (wordsFn sa (sa.regs "%rdi") 8 i))
      rw [blake2InWords_split (w := blake2sP.w)
        (fun i => lo32 (wordsFn sa (sa.regs "%r8") 24 i))] at hv
      exact hv
  · cases h

/-! ## 4. The template kernel -/

/-- **The data of the BLAKE2s compression kernel** at the frame size `F`, under the layout
    `redLayout blake2sKAbi F`. -/
def blake2sKData (F : Nat) (hF : F + redZone + 8 ≤ 2 ^ 64) : NarrowTemplateKernelData where
  name := "blake2s_compress"
  params := [("h", .arr 8 (.word 64)), ("f0", .word 64), ("t1", .word 64), ("t0", .word 64),
    ("hm", .arr 24 (.word 64))]
  Γ := blake2InCtxtP 32
  w := 32
  hw := rfl
  nOut := 8
  body := blake2CompressBodyP blake2sP
  layout := redLayout blake2sKAbi F
  clob := blake2sKClob
  frame := F
  pol := blake2sKPol
  outReg := "%rdi"
  ref := blake2sKRef
  regArr := by decide
  ref_read sa r h := by
    obtain ⟨V, hV, hb⟩ := blake2sK_ref_read sa r h
    exact ⟨V, abiValOf_redLayout hV, hb⟩
  ref_kinds := blake2sK_ref_kinds
  kinds_eq := rfl
  arity := rfl
  args_nodup := (by decide : (blake2sKAbi.args.map (·.reg)).Nodup)
  pubWords := rfl
  result := rfl
  bounds := rfl
  regions_nodup := (by decide : blake2sKAbi.regions.Nodup)
  regions_ro :=
    (by decide : (blake2sKAbi.regions.filter fun p => !isResRegion blake2sKAbi p).length ≤ 1)
  frameHi := (by decide : blake2sKAbi.frameHi ≤ -8)
  out_region := (by decide : ("%rdi", 8) ∈ blake2sKAbi.regions)
  out_fit := by norm_num
  wins := by decide
  result_regs := (by decide : ∀ r ∈ resultRegs blake2sKAbi.result, r ∈ abiRegs blake2sKAbi)
  frame_fit := redLayout_frame_fit hF

/-- The check of the BLAKE2s compression kernel at the frame size of its code:
    `narrowFrameCheck` of the template under `blake2sKAbi`, one evaluation of the back half
    and the level check of the widened template. -/
def blake2sKCICheck : Bool :=
  narrowFrameCheck blake2sKAbi (nfAbiNames "blake2s_compress" blake2sKAbi)
    (NFProg.ofCom (blake2CompressBodyP blake2sP)) blake2sKPol blake2sKClob

set_option linter.style.native false in
/-- **The check of the compiled BLAKE2s compression at the frame of its code**: the frame with
    the red zone fits, the back half succeeds at `redLayout blake2sKAbi blake2sKFrame`, the
    layout passes `layoutFootRoB`, the widened template passes the read-only check and the
    level check, and the decoded block passes `clobOkB` at `blake2sKClob`. -/
theorem blake2sKCICheck_true : blake2sKCICheck = true := by
  native_decide

/-- The frame of the code of the BLAKE2s compression fits with its red zone. -/
theorem blake2sKFrame_fit : blake2sKFrame + redZone + 8 ≤ 2 ^ 64 := by
  rw [blake2sKFrame]
  exact fit_of_narrowFrameCheck blake2sKCICheck_true

/-- **The check of the BLAKE2s compression kernel** at the frame of its code. -/
theorem blake2sK_check : (blake2sKData blake2sKFrame blake2sKFrame_fit).check = true := by
  refine NarrowProgKernelData.check_of_frameCheck
    (d := (blake2sKData blake2sKFrame blake2sKFrame_fit).toNarrowProgKernelData)
    (σ := blake2sKAbi)
    (by dsimp only [blake2sKData, NarrowTemplateKernelData.toNarrowProgKernelData]) ?_ ?_
  · dsimp only [blake2sKData, NarrowTemplateKernelData.toNarrowProgKernelData,
      NarrowTemplateKernelData.prog]
    rw [blake2sKFrame]
    rfl
  · dsimp only [blake2sKData, NarrowTemplateKernelData.toNarrowProgKernelData,
      NarrowTemplateKernelData.prog]
    exact blake2sKCICheck_true

/-- The parameters of the data of the BLAKE2s compression kernel: those of the layout of the
    BLAKE2b compression, which has the same arguments. -/
theorem blake2sK_ins : layoutIns blake2sKAbi = [("RDI", .words 8), ("RSI", .scalar),
    ("RDX", .scalar), ("RCX", .scalar), ("R8", .words 24)] :=
  Blake2Linked.blake2bK_ins

/-- The argument registers of the layout are the physical registers of its parameters. -/
theorem blake2sK_args : blake2sKAbi.args.map (fun a => (a.reg, a.kind)) =
    [("RDI", ArgKind.words 8), ("RSI", ArgKind.scalar), ("RDX", ArgKind.scalar),
      ("RCX", ArgKind.scalar), ("R8", ArgKind.words 24)].map
      fun q => (X86Backend.DecodePrinted.phys q.1, q.2) := by
  decide

/-- **The linked function of the BLAKE2s compression**: the region-compiled template under
    `redLayout blake2sKAbi blake2sKFrame`, with the meaning the reference compression on
    arguments below `2 ^ 32`, the frame size `blake2sKFrame` of the code and the store policy
    `blake2sKPol`. -/
def blake2sKernel : LinkedFn :=
  (blake2sKData blake2sKFrame blake2sKFrame_fit).kernel blake2sK_check

/-- **The code of the BLAKE2s compression meets the contract of its record.** -/
theorem blake2sKernel_meets : blake2sKernel.Meets :=
  NarrowTemplateKernelData.meets blake2sK_check

/-- **The BLAKE2s compression is a linked kernel** of the out shape, with the destination at
    `%rdi`. -/
theorem blake2sKernel_linked : LinkedKernel blake2sKernel :=
  NarrowTemplateKernelData.linked (po := "RDI") blake2sK_check
    ((layoutIns_redLayout _ _).trans blake2sK_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans blake2sK_args)
    (by simp [blake2sKData]) (by decide) rfl

/-- **The linked function of the BLAKE2s compression at the System V convention**: the code of
    `blake2sKernel` at the clobber set without the callee-saved registers. -/
def blake2sKernelAbi : LinkedFn :=
  (blake2sKData blake2sKFrame blake2sKFrame_fit).abiKernel blake2sK_check

/-- **The code of the BLAKE2s compression meets the contract at the System V convention.** -/
theorem blake2sKernelAbi_meets : blake2sKernelAbi.Meets :=
  NarrowTemplateKernelData.meets_abi blake2sK_check

/-- **The BLAKE2s compression at the System V convention is a linked kernel** of the out
    shape, with the destination at `%rdi`. -/
theorem blake2sKernelAbi_linked : LinkedKernel blake2sKernelAbi :=
  NarrowTemplateKernelData.linked_abi (po := "RDI") blake2sK_check
    ((layoutIns_redLayout _ _).trans blake2sK_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans blake2sK_args)
    (by simp [blake2sKData]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked
