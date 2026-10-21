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
* `instrOKWB_zeroArr`, `instrOKWB_storeImm`: `instrOKWB` accepts the array zeroing
  `ZEROARR [], [B, #n, #64]` and the constant-index store `STOREIMM D, [B, V, #k]` through a
  general-purpose base register.
* `instrOKWB_all_of_arrShapes`: the instruction conjunct of `printedAddrWB` holds of a body
  each of whose instructions before the last has a printed shape, has a stack-array shape
  `ArrShape`, or passes `instrOKWB`.
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
    comparisons against a register and an immediate, the register-count shift and the
    count-`0` shift over general-purpose registers of `x86Abi`, in every body and for all body
    parameters. -/
theorem x86_printedComplete : PrintedComplete x86Abi Params instrOKWB where
  setcc body P n R A B hR hA hB :=
    instrOKWB_sete body P n ((gpOk_iff_isGp R).2 hR) ((gpOk_iff_isGp A).2 hA)
      ((gpOk_iff_isGp B).2 hB)
  setccImm body P n R A _v hR hA hv :=
    instrOKWB_seteImm body P n ((gpOk_iff_isGp R).2 hR) ((gpOk_iff_isGp A).2 hA) hv
  shiftReg body P l R A B hR hA hB :=
    instrOKWB_shrReg body P l ((gpOk_iff_isGp R).2 hR) ((gpOk_iff_isGp A).2 hA)
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

/-! ## The stack-array forms -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (stackDispOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (classifyA AArm)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)

/-- **The array zeroing through a base register is covered**: `instrOKWB` accepts
    `ZEROARR [], [B, #n, #64]` for every general-purpose register `B` of `x86Abi`, every count
    `0 < n` whose last word offset `8 (n - 1)` `stackDispOk` admits, every body and all body
    parameters. -/
theorem instrOKWB_zeroArr (body : Lcmd) (P : Params) {B : String} {n : Nat}
    (hB : x86Abi.IsGp B) (hn : 0 < n) (hk : stackDispOk (n - 1) = true) :
    instrOKWB body P (.Lopn [] "ZEROARR" [.reg B, .imm n, .imm 64]) = true := by
  have hB' := (gpOk_iff_isGp B).2 hB
  simp [instrOKWB, classifyK, movImmStruct?, classifyS, classifyC, classifyM, classifyI,
    classifyL, classifyV, classifyE, classifyX, classifyEI, classifyR, classifyA, AArm.ok, hB',
    hn, hk]

/-- **The constant-index store through a base register is covered**: `instrOKWB` accepts
    `STOREIMM D, [B, V, #k]` for all general-purpose registers `D`, `B`, `V` of `x86Abi`, every
    index `k` whose word offset `8 k` `stackDispOk` admits, every body and all body
    parameters. -/
theorem instrOKWB_storeImm (body : Lcmd) (P : Params) {D B V : String} {k : Nat}
    (hD : x86Abi.IsGp D) (hB : x86Abi.IsGp B) (hV : x86Abi.IsGp V)
    (hk : stackDispOk k = true) :
    instrOKWB body P (.Lopn [.reg D] "STOREIMM" [.reg B, .reg V, .imm k]) = true := by
  have hD' := (gpOk_iff_isGp D).2 hD
  have hB' := (gpOk_iff_isGp B).2 hB
  have hV' := (gpOk_iff_isGp V).2 hV
  simp [instrOKWB, classifyK, movImmStruct?, classifyS, classifyC, classifyM, classifyI,
    classifyL, classifyV, classifyE, classifyX, classifyEI, classifyR, classifyA, AArm.ok, hD',
    hB', hV', hk]

/-- **The stack-array shapes** over `x86Abi`: the array zeroing `ZEROARR [], [B, #n, #64]`
    with `0 < n` and the constant-index store `STOREIMM D, [B, V, #k]` over general-purpose
    registers, each with word offsets that `stackDispOk` admits. -/
def ArrShape (i : LinstrR) : Prop :=
  (∃ (B : String) (n : Nat), x86Abi.IsGp B ∧ 0 < n ∧ stackDispOk (n - 1) = true ∧
      i = .Lopn [] "ZEROARR" [.reg B, .imm n, .imm 64])
    ∨ ∃ (D B V : String) (k : Nat), x86Abi.IsGp D ∧ x86Abi.IsGp B ∧ x86Abi.IsGp V ∧
      stackDispOk k = true ∧ i = .Lopn [.reg D] "STOREIMM" [.reg B, .reg V, .imm k]

/-- `instrOKWB` accepts every instruction of a stack-array shape. -/
theorem instrOKWB_of_arrShape (body : Lcmd) (P : Params) {i : LinstrR} (h : ArrShape i) :
    instrOKWB body P i = true := by
  rcases h with ⟨B, n, hB, hn, hk, rfl⟩ | ⟨D, B, V, k, hD, hB, hV, hk, rfl⟩
  · exact instrOKWB_zeroArr body P hB hn hk
  · exact instrOKWB_storeImm body P hD hB hV hk

/-- **The instruction conjunct of `printedAddrWB` from the shapes and the stack-array
    shapes**: it holds of a body each of whose instructions before the last has a printed
    shape over `x86Abi`, has a stack-array shape, or passes `instrOKWB`. -/
theorem instrOKWB_all_of_arrShapes {body : Lcmd}
    (h : ∀ i ∈ body.dropLast, PrintedShape x86Abi i.li_i ∨ ArrShape i.li_i
      ∨ instrOKWB body (Params.ofBody body) i.li_i = true) :
    body.dropLast.all (fun i => instrOKWB body (Params.ofBody body) i.li_i) = true :=
  instrOKWB_all_of_shapes fun i hi => (h i hi).imp_right fun h' =>
    h'.elim (instrOKWB_of_arrShape body _) id

end CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteX86
