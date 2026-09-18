/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped

/-!
# Constant time of the shipped `ed25519_point_add`

This module extends `Ascent.Imported.ShippedCT` to the imported block of
`ed25519_point_add` (`Ed25519PointAddShipped.ed25519PointAddShippedBlock`, 4859
instructions in ten parts), in the same leakage model
(`X86Backend.MachineConstantTime.blockLeak`).

The block is call-free and has no indexed memory access: every instruction is
direct (`allDirect`), so the leakage trace is the same from any two states. Its
`cmovne`, `setc`, `test`, `bt` and `adcx` instructions emit no leakage event in
`instrLeak`, and `adcxMem` emits the event of its base register and displacement,
as every other direct memory access.

The address trace is checked part by part from the entry set `pub2` (`%rdi`,
`%rsi`, `%rsp`) with `check true`; each `pointAdd_strict_partNN` states the public
set after its part. The base registers of the block are `%rsp` and `%r14`, and
`%r14` is loaded, before each access through it, from the `%rsp` cell at offset
384 or 392 that the block fills with `%rsi` or `%rdi`.

## Main results

* `ed25519PointAdd_constant_time`: the leakage trace is the same from any two
  states.
* `ed25519PointAdd_addr`: the address trace is determined by `%rdi`, `%rsi`,
  `%rsp`.
* `shipped_kernels_constant_time_all`: `shipped_kernels_constant_time` together
  with `ed25519PointAdd_constant_time`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_append allDirect_constant_time)

section PointAdd
open Ed25519PointAddShipped

/-- Every instruction of `ed25519_point_add` is direct. -/
theorem pointAdd_allDirect : allDirect ed25519PointAddShippedBlock = true := by
  unfold ed25519PointAddShippedBlock
  simp only [allDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> decide +kernel

/-- `ed25519_point_add`: the leakage trace is the same from any two states. -/
theorem ed25519PointAdd_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ ed25519PointAddShippedBlock = blockLeak s₂ ed25519PointAddShippedBlock :=
  allDirect_constant_time _ pointAdd_allDirect s₁ s₂

/-! ### The address trace, part by part -/

theorem pointAdd_strict_part01 :
    check true pub2 ed25519PointAddShippedPart01 = true ∧
      run pub2 ed25519PointAddShippedPart01 =
        rspPub ["%r9", "%rbx", "%rsp"] [-128, 384, 392] := by decide +kernel
theorem pointAdd_strict_part02 :
    check true (rspPub ["%r9", "%rbx", "%rsp"] [-128, 384, 392])
        ed25519PointAddShippedPart02 = true ∧
      run (rspPub ["%r9", "%rbx", "%rsp"] [-128, 384, 392]) ed25519PointAddShippedPart02 =
        rspPub ["%rax", "%rsp"] [384, 392] := by decide +kernel
theorem pointAdd_strict_part03 :
    check true (rspPub ["%rax", "%rsp"] [384, 392]) ed25519PointAddShippedPart03 = true ∧
      run (rspPub ["%rax", "%rsp"] [384, 392]) ed25519PointAddShippedPart03 =
        rspPub ["%rcx", "%rbx", "%r14", "%r15", "%rsp"] [168, 384, 392] := by decide +kernel
theorem pointAdd_strict_part04 :
    check true (rspPub ["%rcx", "%rbx", "%r14", "%r15", "%rsp"] [168, 384, 392])
        ed25519PointAddShippedPart04 = true ∧
      run (rspPub ["%rcx", "%rbx", "%r14", "%r15", "%rsp"] [168, 384, 392])
          ed25519PointAddShippedPart04 =
        rspPub ["%rbp", "%rbx", "%rax", "%rsp"] [-128, 384, 392] := by decide +kernel
theorem pointAdd_strict_part05 :
    check true (rspPub ["%rbp", "%rbx", "%rax", "%rsp"] [-128, 384, 392])
        ed25519PointAddShippedPart05 = true ∧
      run (rspPub ["%rbp", "%rbx", "%rax", "%rsp"] [-128, 384, 392])
          ed25519PointAddShippedPart05 =
        rspPub ["%rcx", "%rbx", "%rsp"] [384, 392] := by decide +kernel
theorem pointAdd_strict_part06 :
    check true (rspPub ["%rcx", "%rbx", "%rsp"] [384, 392]) ed25519PointAddShippedPart06 = true ∧
      run (rspPub ["%rcx", "%rbx", "%rsp"] [384, 392]) ed25519PointAddShippedPart06 =
        rspPub ["%rbx", "%rsp"] [384, 392] := by decide +kernel
theorem pointAdd_strict_part07 :
    check true (rspPub ["%rbx", "%rsp"] [384, 392]) ed25519PointAddShippedPart07 = true ∧
      run (rspPub ["%rbx", "%rsp"] [384, 392]) ed25519PointAddShippedPart07 =
        rspPub ["%rsp"] [-128, 384, 392] := by decide +kernel
theorem pointAdd_strict_part08 :
    check true (rspPub ["%rsp"] [-128, 384, 392]) ed25519PointAddShippedPart08 = true ∧
      run (rspPub ["%rsp"] [-128, 384, 392]) ed25519PointAddShippedPart08 =
        rspPub ["%rax", "%rsp"] [384, 392] := by decide +kernel
theorem pointAdd_strict_part09 :
    check true (rspPub ["%rax", "%rsp"] [384, 392]) ed25519PointAddShippedPart09 = true ∧
      run (rspPub ["%rax", "%rsp"] [384, 392]) ed25519PointAddShippedPart09 =
        rspPub ["%r9", "%rax", "%rsp"] [-128, 384, 392] := by decide +kernel
theorem pointAdd_strict_part10 :
    check true (rspPub ["%r9", "%rax", "%rsp"] [-128, 384, 392])
      ed25519PointAddShippedPart10 = true := by decide +kernel

theorem pointAdd_check_strict : check true pub2 ed25519PointAddShippedBlock = true := by
  unfold ed25519PointAddShippedBlock
  simp only [List.append_assoc]
  exact check_append_of pointAdd_strict_part01 <| check_append_of pointAdd_strict_part02 <|
    check_append_of pointAdd_strict_part03 <| check_append_of pointAdd_strict_part04 <|
    check_append_of pointAdd_strict_part05 <| check_append_of pointAdd_strict_part06 <|
    check_append_of pointAdd_strict_part07 <| check_append_of pointAdd_strict_part08 <|
    check_append_of pointAdd_strict_part09 pointAdd_strict_part10

/-- `ed25519_point_add`: the address trace is determined by `%rdi`, `%rsi`, `%rsp`. -/
theorem ed25519PointAdd_addr (s₁ s₂ : JState 64) (hag : pub2.Agree s₁ s₂) :
    blockAddr s₁ ed25519PointAddShippedBlock = blockAddr s₂ ed25519PointAddShippedBlock :=
  check_addr pointAdd_check_strict hag

end PointAdd

/-- **The shipped kernels, point addition included, are constant time.** The
    twelve statements of `shipped_kernels_constant_time`, and the leakage trace of
    `ed25519_point_add` is the same from any two states. -/
theorem shipped_kernels_constant_time_all :
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519MulShipped.fe25519MulShippedBlock =
      blockLeak s₂ Fe25519MulShipped.fe25519MulShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519SqrShipped.fe25519SqrShippedBlock =
      blockLeak s₂ Fe25519SqrShipped.fe25519SqrShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519AddShipped.fe25519AddShippedBlock =
      blockLeak s₂ Fe25519AddShipped.fe25519AddShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Fe25519SubShipped.fe25519SubShippedBlock =
      blockLeak s₂ Fe25519SubShipped.fe25519SubShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519CombSelectShipped.ed25519CombSelectShippedBlock =
      blockLeak s₂ Ed25519CombSelectShipped.ed25519CombSelectShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519Join16Shipped.ed25519Join16ShippedBlock =
      blockLeak s₂ Ed25519Join16Shipped.ed25519Join16ShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519PackSignShipped.ed25519PackSignShippedBlock =
      blockLeak s₂ Ed25519PackSignShipped.ed25519PackSignShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519ScReduceShipped.ed25519ScReduceShippedBlock =
      blockLeak s₂ Ed25519ScReduceShipped.ed25519ScReduceShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519ScMuladdShipped.ed25519ScMuladdShippedBlock =
      blockLeak s₂ Ed25519ScMuladdShipped.ed25519ScMuladdShippedBlock) ∧
    (∀ C, LeafModel C → ∀ s₁ s₂, segsLeak C s₁ Ed25519MaddShipped.ed25519MaddShippedBlock =
      segsLeak C s₂ Ed25519MaddShipped.ed25519MaddShippedBlock) ∧
    (∀ C, LeafModel C → ∀ s₁ s₂, segsLeak C s₁ Ed25519InvertShipped.ed25519InvertShippedBlock =
      segsLeak C s₂ Ed25519InvertShipped.ed25519InvertShippedBlock) ∧
    (∀ C, ShippedModel C → ∀ s₁ s₂,
      segsLeak C s₁ Ed25519CompressShipped.ed25519CompressShippedBlock =
        segsLeak C s₂ Ed25519CompressShipped.ed25519CompressShippedBlock) ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ Ed25519PointAddShipped.ed25519PointAddShippedBlock =
      blockLeak s₂ Ed25519PointAddShipped.ed25519PointAddShippedBlock) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := shipped_kernels_constant_time
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ed25519PointAdd_constant_time⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
