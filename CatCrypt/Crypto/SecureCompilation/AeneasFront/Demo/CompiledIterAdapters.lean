/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryCT
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.ReifiedIterAdapters

/-!
# The compiler theorems of the Aeneas front at loops over iterator adapters

The three functions of `AeneasFront.Demo.TestIterAdapters` are loops over `enumerate` of a
range, `enumerate` of an array and `zip` of two arrays. `AeneasFront.Demo.ReifiedIterAdapters`
reads them as NF programs with counted loops, with the proofs by construction
`enumRangeSum_denote`, `enumArraySum_denote` and `zipArraySum_denote`. This module makes each
a source of the Aeneas entry (`AeSrc.ofFn`) and states the compiler theorem
`NFEntry.compileR_correct` at it, under a System V layout: the arrays of four words at `%rdi`
(and `%rsi`), the accumulator in the next argument register, the result in `%rax`.

## Main results

* `enumRangeSumSrc`, `enumArraySumSrc`, `zipArraySumSrc`: the sources.
* `enumRangeSum_compileR_correct`, `enumArraySum_compileR_correct`,
  `zipArraySum_compileR_correct`: the compiler theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open _root_.Hax (Value)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- The System V layout of `enum_range_sum`: the array of four words at `%rdi`, the
    accumulator in `%rsi`, the result in `%rax`. The parameters are listed from the last
    argument. -/
def enumRangeSumAbi : AbiLayout where
  args := [⟨"acc", "%rsi", .scalar⟩, ⟨"a", "%rdi", .words 4⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- **`enum_range_sum` as a source of the Aeneas entry**: the program and the certificate of
    the output of `reifyAeneas%` (`enumRangeSum`, `enumRangeSum_denote`). -/
def enumRangeSumSrc : AeSrc :=
  AeSrc.ofFn [.arr 4#usize (.u .U32 (by decide)), .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => iter_adapters.enum_range_sum a.1 a.2.1) enumRangeSum.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := enumRangeSum_denote a.1 a.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The compiler theorem at `enum_range_sum`.** It is `NFEntry.compileR_correct` at
    `aeneasEntry` and `enumRangeSumSrc`. -/
theorem enumRangeSum_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR enumRangeSumSrc enumRangeSumAbi "enum_range_sum" =
      some (P, bytes))
    (sa : AState) (hsep : enumRangeSumAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns enumRangeSumAbi enumRangeSumSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ enumRangeSumAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") enumRangeSumAbi.frameLo
            enumRangeSumAbi.frameHi) →
        (∀ p ∈ enumRangeSumAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct enumRangeSumSrc enumRangeSumAbi "enum_range_sum" P bytes hc
      sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

/-- The System V layout of `enum_array_sum` and `zip_array_sum`: the arrays of four words at
    `%rdi` and `%rsi`, the accumulator in `%rdx`, the result in `%rax`. The parameters are
    listed from the last argument. -/
def twoArraysAbi : AbiLayout where
  args := [⟨"acc", "%rdx", .scalar⟩, ⟨"b", "%rsi", .words 4⟩, ⟨"a", "%rdi", .words 4⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- **`enum_array_sum` as a source of the Aeneas entry**: the program and the certificate of
    the output of `reifyAeneas%` (`enumArraySum`, `enumArraySum_denote`). -/
def enumArraySumSrc : AeSrc :=
  AeSrc.ofFn [.arr 4#usize (.u .U32 (by decide)), .arr 4#usize (.u .U32 (by decide)),
      .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => iter_adapters.enum_array_sum a.1 a.2.1 a.2.2.1) enumArraySum.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := enumArraySum_denote a.1 a.2.1 a.2.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The compiler theorem at `enum_array_sum`.** It is `NFEntry.compileR_correct` at
    `aeneasEntry` and `enumArraySumSrc`. -/
theorem enumArraySum_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR enumArraySumSrc twoArraysAbi "enum_array_sum" = some (P, bytes))
    (sa : AState) (hsep : twoArraysAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns twoArraysAbi enumArraySumSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ twoArraysAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") twoArraysAbi.frameLo twoArraysAbi.frameHi) →
        (∀ p ∈ twoArraysAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct enumArraySumSrc twoArraysAbi "enum_array_sum" P bytes hc
      sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

/-- **`zip_array_sum` as a source of the Aeneas entry**: the program and the certificate of
    the output of `reifyAeneas%` (`zipArraySum`, `zipArraySum_denote`). -/
def zipArraySumSrc : AeSrc :=
  AeSrc.ofFn [.arr 4#usize (.u .U32 (by decide)), .arr 4#usize (.u .U32 (by decide)),
      .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => iter_adapters.zip_array_sum a.1 a.2.1 a.2.2.1) zipArraySum.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := zipArraySum_denote a.1 a.2.1 a.2.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The compiler theorem at `zip_array_sum`.** It is `NFEntry.compileR_correct` at
    `aeneasEntry` and `zipArraySumSrc`. -/
theorem zipArraySum_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR zipArraySumSrc twoArraysAbi "zip_array_sum" = some (P, bytes))
    (sa : AState) (hsep : twoArraysAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns twoArraysAbi zipArraySumSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ twoArraysAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") twoArraysAbi.frameLo twoArraysAbi.frameHi) →
        (∀ p ∈ twoArraysAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct zipArraySumSrc twoArraysAbi "zip_array_sum" P bytes hc
      sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
