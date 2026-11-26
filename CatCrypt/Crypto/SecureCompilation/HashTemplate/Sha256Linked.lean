/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked
public meta import CatCrypt.Crypto.SecureCompilation.HashTemplate.NarrowKernel
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.NarrowKernel

/-!
# The SHA-256 compression template as a narrow-width linked function

The SHA-256 compression template `sha2CompressBodyP sha256P`, over 32-bit words, compiled by
the region back half `compileRegion` under the u64-slot layout
`redLayout sha256Abi sha256KFrame`: the output array `h` of 8 slots at `%rdi`, the input array
`hm` of 24 slots, the chaining words then the message words, at `%rsi`, each slot a 64-bit
word holding a 32-bit word with zero high bits, and the result the 8 slots at `%rdi`. It is
the narrow-width template kernel `sha256KData`, whose linked function `sha256Kernel` has the
meaning the reference compression `sha2CompressRef sha256P` on arguments whose words lie below
`2 ^ 32`, with the result words zero extended. The compression of SHA-224 is this template at
other initial hash values, which the kernel does not contain, so SHA-224 uses the same kernel.

## Main definitions

* `sha256KFrame`: the frame size of the code at the layout `sha256Abi`.
* `sha256KPol`, `sha256KClob` (module `Sha2LinkedData`): its store policy and clobber set.
* `sha256KRef`: the reference compression on source values.
* `sha256KData`: the data of the narrow-width template kernel at a frame size.
* `sha256Kernel`, `sha256KernelAbi`: the linked function of the compiled template, and its
  System V form.

## Main statements

* `sha256KCICheck_true`, `sha256K_check`: the template compiles at the frame of its code and
  passes the footprint, read-only, level and clobber checks.
* `sha256Kernel_meets`, `sha256Kernel_linked`: the code of the kernel meets the contract of
  its record, and the kernel is a linked kernel.
* `sha256KernelAbi_meets`, `sha256KernelAbi_linked`: the same at the System V convention.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha256Linked

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
open CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked (sha256Abi sha2InWords_split)
open CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2sLinked (lo32 setWidth_lo32)
open _root_.Hax (Value)

/-! ## 1. The layout -/

/-- **The frame size of the code of the SHA-256 compression**: `codeFrame` of the compiled
    template under `sha256Abi`. -/
def sha256KFrame : Nat :=
  codeFrame sha256Abi (nfAbiNames "sha256_compress" sha256Abi)
    (NFProg.ofCom (sha2CompressBodyP sha256P))

/-! ## 2. The meaning -/

/-- **The reference compression on source values** of the parameters `h` and `hm`: the output
    array decoded as an array of 8 words, the input array as an array of 24 words; where every
    word lies below `2 ^ 32`, the eight words of `sha2CompressRef sha256P` at the low halves
    of the chaining words and the message words of the input array. -/
def sha256KRef (vals : List Value) : Option (Fin 8 → BitVec 32) :=
  match vals with
  | [hv, hmv] =>
      (dec (.arr 8 (.word 64)) hv).bind fun hh =>
      (dec (.arr 24 (.word 64)) hmv).bind fun hm =>
        if (∀ i, (hh i).toNat < 2 ^ 32) ∧ (∀ i, (hm i).toNat < 2 ^ 32) then
          some (sha256P.sha2CompressRef (fun i => lo32 (hm ⟨i.1, by omega⟩))
            (fun j => lo32 (hm ⟨8 + j.1, by omega⟩)))
        else none
  | _ => none

/-- The reference compression returns values only on arguments of the kinds of the
    layout. -/
theorem sha256K_ref_kinds : ∀ vals r, sha256KRef vals = some r →
    vals.map valKind = sha256Abi.args.map (·.kind) := by
  intro vals r h
  rcases vals with _ | ⟨hv, _ | ⟨hmv, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [sha256KRef, reduceCtorEq] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, -⟩ := h
  simp only [List.map_cons, List.map_nil, valKind_of_dec_arr h1, valKind_of_dec_arr h2]
  rfl

/-! ## 3. The valuation of the layout -/

/-- The narrow valuation of the entry state `sa`: the low halves of the 24 slots at `%rsi` and
    of the 8 slots at `%rdi`. -/
def sha256KNVal (sa : AState) : Ctxt.Valuation (sha2InCtxtP 32) :=
  .cons (fun i => lo32 (wordsFn sa (sa.regs "%rsi") 24 i))
    (.cons (fun i => lo32 (wordsFn sa (sa.regs "%rdi") 8 i)) .nil)

/-- **The reference compression at the layout reading**: where the reference compression
    returns `r` at the source values the layout reads off the entry state `sa`, the layout
    reads the widening of the narrow valuation `sha256KNVal sa`, at which the template has
    the value `r`. -/
theorem sha256K_ref_read (sa : AState) (r : Fin 8 → BitVec 32)
    (h : sha256KRef (sha256Abi.args.map (·.read sa)) = some r) :
    ∃ V : Ctxt.Valuation (sha2InCtxtP 32), AbiValOf sha256Abi sa (mapVal V) ∧
      (sha2CompressBodyP sha256P).denote V = r := by
  have hvals : sha256Abi.args.map (·.read sa) = [.array (wordsAt sa.mem (sa.regs "%rdi") 8),
      .array (wordsAt sa.mem (sa.regs "%rsi") 24)] :=
    rfl
  rw [hvals] at h
  simp only [sha256KRef, X86Backend.LinkedFnCallee.dec_arr_wordsAt, Option.bind_some] at h
  split at h
  · rename_i hr
    obtain ⟨h1, h2⟩ := hr
    obtain rfl := (Option.some.inj h).symm
    refine ⟨sha256KNVal sa, ?_, ?_⟩
    · exact
        { arg := fun v => by
            rcases v with _ | _ | ⟨⟨⟩⟩ <;> rfl
          reg := fun v => by
            rcases v with _ | _ | ⟨⟨⟩⟩
          arr := fun v => by
            rcases v with _ | _ | ⟨⟨⟩⟩
            · exact ⟨_, rfl, rfl, rfl, funext fun i => setWidth_lo32 (h2 i)⟩
            · exact ⟨_, rfl, rfl, rfl, funext fun i => setWidth_lo32 (h1 i)⟩ }
    · have hv := sha2CompressBodyP_value sha256P
        (fun i : Fin 8 => lo32 (wordsFn sa (sa.regs "%rsi") 24 ⟨i.1, by omega⟩))
        (fun j : Fin 16 => lo32 (wordsFn sa (sa.regs "%rsi") 24 ⟨8 + j.1, by omega⟩))
        (fun i => lo32 (wordsFn sa (sa.regs "%rdi") 8 i))
      rw [sha2InWords_split (w := sha256P.w)
        (fun i => lo32 (wordsFn sa (sa.regs "%rsi") 24 i))] at hv
      exact hv
  · cases h

/-! ## 4. The template kernel -/

/-- **The data of the SHA-256 compression kernel** at the frame size `F`, under the layout
    `redLayout sha256Abi F`. -/
def sha256KData (F : Nat) (hF : F + redZone + 8 ≤ 2 ^ 64) : NarrowTemplateKernelData where
  name := "sha256_compress"
  params := [("h", .arr 8 (.word 64)), ("hm", .arr 24 (.word 64))]
  Γ := sha2InCtxtP 32
  w := 32
  hw := rfl
  nOut := 8
  body := sha2CompressBodyP sha256P
  layout := redLayout sha256Abi F
  clob := sha256KClob
  frame := F
  pol := sha256KPol
  outReg := "%rdi"
  ref := sha256KRef
  regArr := by decide
  ref_read sa r h := by
    obtain ⟨V, hV, hb⟩ := sha256K_ref_read sa r h
    exact ⟨V, abiValOf_redLayout hV, hb⟩
  ref_kinds := sha256K_ref_kinds
  kinds_eq := rfl
  arity := rfl
  args_nodup := (by decide : (sha256Abi.args.map (·.reg)).Nodup)
  pubWords := rfl
  result := rfl
  bounds := rfl
  regions_nodup := (by decide : sha256Abi.regions.Nodup)
  regions_ro :=
    (by decide : (sha256Abi.regions.filter fun p => !isResRegion sha256Abi p).length ≤ 1)
  frameHi := (by decide : sha256Abi.frameHi ≤ -8)
  out_region := (by decide : ("%rdi", 8) ∈ sha256Abi.regions)
  out_fit := by norm_num
  wins := by decide
  result_regs := (by decide : ∀ r ∈ resultRegs sha256Abi.result, r ∈ abiRegs sha256Abi)
  frame_fit := redLayout_frame_fit hF

/-- The check of the SHA-256 compression kernel at the frame size of its code:
    `narrowFrameCheck` of the template under `sha256Abi`, one evaluation of the back half
    and the level check of the widened template. -/
def sha256KCICheck : Bool :=
  narrowFrameCheck sha256Abi (nfAbiNames "sha256_compress" sha256Abi)
    (NFProg.ofCom (sha2CompressBodyP sha256P)) sha256KPol sha256KClob

set_option linter.style.native false in
/-- **The check of the compiled SHA-256 compression at the frame of its code**: the frame with
    the red zone fits, the back half succeeds at `redLayout sha256Abi sha256KFrame`, the
    layout passes `layoutFootRoB`, the widened template passes the read-only check and the
    level check, and the decoded block passes `clobOkB` at `sha256KClob`. -/
theorem sha256KCICheck_true : sha256KCICheck = true := by
  native_decide

/-- The frame of the code of the SHA-256 compression fits with its red zone. -/
theorem sha256KFrame_fit : sha256KFrame + redZone + 8 ≤ 2 ^ 64 := by
  rw [sha256KFrame]
  exact fit_of_narrowFrameCheck sha256KCICheck_true

/-- **The check of the SHA-256 compression kernel** at the frame of its code. -/
theorem sha256K_check : (sha256KData sha256KFrame sha256KFrame_fit).check = true := by
  refine NarrowProgKernelData.check_of_frameCheck
    (d := (sha256KData sha256KFrame sha256KFrame_fit).toNarrowProgKernelData)
    (σ := sha256Abi)
    (by dsimp only [sha256KData, NarrowTemplateKernelData.toNarrowProgKernelData]) ?_ ?_
  · dsimp only [sha256KData, NarrowTemplateKernelData.toNarrowProgKernelData,
      NarrowTemplateKernelData.prog]
    rw [sha256KFrame]
    rfl
  · dsimp only [sha256KData, NarrowTemplateKernelData.toNarrowProgKernelData,
      NarrowTemplateKernelData.prog]
    exact sha256KCICheck_true

set_option linter.style.native false in
/-- The parameters of the data of the SHA-256 compression kernel. -/
theorem sha256K_ins : layoutIns sha256Abi = [("RDI", .words 8), ("RSI", .words 24)] := by
  native_decide

/-- The argument registers of the layout are the physical registers of its parameters. -/
theorem sha256K_args : sha256Abi.args.map (fun a => (a.reg, a.kind)) =
    [("RDI", ArgKind.words 8), ("RSI", ArgKind.words 24)].map
      fun q => (X86Backend.DecodePrinted.phys q.1, q.2) := by
  decide

/-- **The linked function of the SHA-256 compression**: the region-compiled template under
    `redLayout sha256Abi sha256KFrame`, with the meaning the reference compression on
    arguments below `2 ^ 32`, the frame size `sha256KFrame` of the code and the store policy
    `sha256KPol`. -/
def sha256Kernel : LinkedFn :=
  (sha256KData sha256KFrame sha256KFrame_fit).kernel sha256K_check

/-- **The code of the SHA-256 compression meets the contract of its record.** -/
theorem sha256Kernel_meets : sha256Kernel.Meets :=
  NarrowTemplateKernelData.meets sha256K_check

/-- **The SHA-256 compression is a linked kernel** of the out shape, with the destination at
    `%rdi`. -/
theorem sha256Kernel_linked : LinkedKernel sha256Kernel :=
  NarrowTemplateKernelData.linked (po := "RDI") sha256K_check
    ((layoutIns_redLayout _ _).trans sha256K_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans sha256K_args)
    (by simp [sha256KData]) (by decide) rfl

/-- **The linked function of the SHA-256 compression at the System V convention**: the code of
    `sha256Kernel` at the clobber set without the callee-saved registers. -/
def sha256KernelAbi : LinkedFn :=
  (sha256KData sha256KFrame sha256KFrame_fit).abiKernel sha256K_check

/-- **The code of the SHA-256 compression meets the contract at the System V convention.** -/
theorem sha256KernelAbi_meets : sha256KernelAbi.Meets :=
  NarrowTemplateKernelData.meets_abi sha256K_check

/-- **The SHA-256 compression at the System V convention is a linked kernel** of the out
    shape, with the destination at `%rdi`. -/
theorem sha256KernelAbi_linked : LinkedKernel sha256KernelAbi :=
  NarrowTemplateKernelData.linked_abi (po := "RDI") sha256K_check
    ((layoutIns_redLayout _ _).trans sha256K_ins)
    ((congrArg (List.map _) (redLayout_args _ _)).trans sha256K_args)
    (by simp [sha256KData]) (by decide) rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha256Linked
