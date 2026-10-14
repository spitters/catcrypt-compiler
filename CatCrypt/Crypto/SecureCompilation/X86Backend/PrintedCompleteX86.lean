/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.IsaPrintedComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the x86 printed-class gate

The wide printed class of the x86 assembly simulation gates each instruction of a body by
`instrOKWB body P`, with the body parameters `P : Params` as context. Its register test
`gpOk` is the general-purpose register test of the x86 register file `x86Abi`, and the gate
is complete for the printed shapes of `IsaPrintedComplete`.

## Main results

* `gpOk_iff_isReg`: a name passes `gpOk` exactly when it is a register of `x86Abi` other
  than its stack pointer `RSP`.
* `x86_printedComplete`: `instrOKWB` is a complete printed-class gate over `x86Abi`.
* `instrOKWB_all_of_shapes`: the instruction conjunct of `printedAddrWB` holds of a body
  each of whose instructions before the last has a printed shape or passes `instrOKWB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteX86

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

/-- The stack pointer of the x86 register file is `RSP`. -/
theorem x86Abi_sp : x86Abi.sp = "RSP" := rfl

/-- **The x86 general-purpose name test is the register test of `x86Abi`**: a name passes
    `gpOk` exactly when it is a register of `x86Abi` other than the stack pointer. -/
theorem gpOk_iff_isReg (r : String) : gpOk r = true ↔ x86Abi.IsReg r ∧ r ≠ x86Abi.sp := by
  rw [x86Abi_sp]
  simp only [gpOk, gpList, IsaAbi.IsReg, gpRegNames, reloadScratch, reloadScratch2,
    List.contains_eq_mem, List.mem_cons, List.not_mem_nil, decide_eq_true_eq, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl) <;> decide
  · rintro ⟨(h | h | rfl), hne⟩
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · rcases h with rfl | rfl <;> decide
    · exact absurd rfl hne

/-- `gpOk` is the general-purpose register test `IsGp` of `x86Abi`. -/
theorem gpOk_iff_isGp (r : String) : gpOk r = true ↔ x86Abi.IsGp r := gpOk_iff_isReg r

/-- **The x86 printed-class gate is complete**: `instrOKWB` accepts the materialised
    comparison and the count-`0` shift over general-purpose registers of `x86Abi`, in every
    body and for all body parameters. -/
theorem x86_printedComplete : PrintedComplete x86Abi Params instrOKWB where
  setcc body P n R A B hR hA hB :=
    instrOKWB_sete body P n ((gpOk_iff_isGp R).2 hR) ((gpOk_iff_isGp A).2 hA)
      ((gpOk_iff_isGp B).2 hB)
  shl0 body P R hR := instrOKWB_shl0 body P ((gpOk_iff_isGp R).2 hR)

/-- **The instruction conjunct of `printedAddrWB` from the shapes**: it holds of a body each
    of whose instructions before the last has a printed shape over `x86Abi` or passes
    `instrOKWB`. -/
theorem instrOKWB_all_of_shapes {body : Lcmd}
    (h : ∀ i ∈ body.dropLast, PrintedShape x86Abi i.li_i
      ∨ instrOKWB body (Params.ofBody body) i.li_i = true) :
    body.dropLast.all (fun i => instrOKWB body (Params.ofBody body) i.li_i) = true :=
  x86_printedComplete.all_of_shapes Params.ofBody h

end CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteX86
