/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryCT
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.ReifiedIterAdapters

/-!
# The compiler theorem of the Aeneas front at a loop over `step_by`

`iter_adapters.step_by_range_sum` of `AeneasFront.Demo.TestIterAdapters` is the loop
`for i in (0..8).step_by(2) { acc = acc + a[i] }`. `reifyAeneas%` reads it as an NF program
with a counted loop of `⌈8 / 2⌉` trips (`Reify.indexedForLoop` at `stepByRangeIter`), whose
step computes the item `j * 2` by the checked `usize` multiplication `Mul#size`
(`reifyE_mul` at `CheckedTy .Usize`). This module states the reading, makes the function a
source of the Aeneas entry and states the compiler theorem `NFEntry.compileR_correct` at it,
under a System V layout: the array of eight words at `%rdi`, the accumulator in `%rsi`, the
result in `%rax`.

## Main results

* `stepByRangeSum_denote`: the reading.
* `stepByRangeSumSrc`: the source.
* `stepByRangeSum_compileR_correct`: the compiler theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open _root_.Hax (Value)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- `iter_adapters.step_by_range_sum` read as an NF program. -/
def stepByRangeSum := reifyAeneas% iter_adapters.step_by_range_sum

/-- A value of `step_by_range_sum` is the denotation of its NF program. -/
theorem stepByRangeSum_denote (a : Aeneas.Std.Array U32 8#usize) (acc z : U32)
    (h : iter_adapters.step_by_range_sum a acc = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel stepByRangeSum.prog (vCons a (vCons acc vNil)) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (stepByRangeSum.sound a acc) h

/-- The System V layout of `step_by_range_sum`: the array of eight words at `%rdi`, the
    accumulator in `%rsi`, the result in `%rax`. The parameters are listed from the last
    argument. -/
def stepByRangeSumAbi : AbiLayout where
  args := [⟨"acc", "%rsi", .scalar⟩, ⟨"a", "%rdi", .words 8⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- **`step_by_range_sum` as a source of the Aeneas entry**: the program and the certificate
    of the output of `reifyAeneas%` (`stepByRangeSum`, `stepByRangeSum_denote`). -/
def stepByRangeSumSrc : AeSrc :=
  AeSrc.ofFn [.arr 8#usize (.u .U32 (by decide)), .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => iter_adapters.step_by_range_sum a.1 a.2.1) stepByRangeSum.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := stepByRangeSum_denote a.1 a.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The compiler theorem at `step_by_range_sum`.** It is `NFEntry.compileR_correct` at
    `aeneasEntry` and `stepByRangeSumSrc`. -/
theorem stepByRangeSum_compileR_correct (P : JasminLprogExport.Lprog)
    (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR stepByRangeSumSrc stepByRangeSumAbi "step_by_range_sum" =
      some (P, bytes))
    (sa : AState) (hsep : stepByRangeSumAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns stepByRangeSumAbi stepByRangeSumSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ stepByRangeSumAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") stepByRangeSumAbi.frameLo
            stepByRangeSumAbi.frameHi) →
        (∀ p ∈ stepByRangeSumAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct stepByRangeSumSrc stepByRangeSumAbi "step_by_range_sum" P
      bytes hc sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
