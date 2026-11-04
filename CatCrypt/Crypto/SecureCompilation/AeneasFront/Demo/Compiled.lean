/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryCT
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Reified

/-!
# The compiler theorems of the Aeneas front at `arrays.incr_array`

`arrays.incr_array` of the Aeneas test output (`AeneasFront.Demo.TestArrays`) reads the first
of two `u32` words of an array, adds one with the checked addition, and writes the sum back.
`reifyAeneas%` reads it as the NF program `Demo.incrArray` with the proof by construction
`Demo.incrArray_denote`. This module makes that output a source of the Aeneas entry and
states the correctness and the constant time of the bytes the compiler `NFEntry.compileR`
returns for it under the System V layout `incrAbi`: the array of two words at `%rdi`, the
result the two words at the entry `%rdi`.

* The source `incrArraySrc` takes the program and the certificate from the output of
  `reifyAeneas%`; the certificate is `Reify.toDenote` at the fuel the output gives.
* `incrArray_compileR_correct` is `NFEntry.compileR_correct` at `aeneasEntry` and the source;
  the entry carries no linked function and no declared procedure, so the default linked
  agreement holds.
* `incrArray_compileR_ct` is `aeneasEntry_compileR_ct` with the array secret: the level
  checker accepts the program (its index operands are literals), the layout check
  `pubLabelsB` accepts the secrecy record, the names of the layout are distinct; the
  sub-table hypothesis, the absence of declared `index`/`array_update` procedures and the
  termination hypothesis are discharged for every source by `aeneasEntry_compileR_ct`.

The bytes are written by the row `aeneas_incr_array` of `linked-kernel-emit`.

## Main results

* `incrArraySrc` — the source.
* `incrArray_compileR_correct` — the compiler theorem at the source.
* `incrArray_compileR_ct` — constant time of the bytes at the source.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open _root_.Hax (Value)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- The System V layout of `incr_array`: the array of two words at `%rdi`, the result the
    two words at the entry `%rdi`, the stack frame from `-256` to `-8`. -/
def incrAbi : AbiLayout where
  args := [⟨"x", "%rdi", .words 2⟩]
  consts := []
  result := .words "%rdi" 2
  bounds := []
  frameLo := -256
  frameHi := -8

/-- **`arrays.incr_array` as a source of the Aeneas entry**: the program and the certificate
    of the output of `reifyAeneas%` (`incrArray`, `incrArray_denote`). -/
def incrArraySrc : AeSrc where
  args := [.arr 2#usize (.u .U32 (by decide))]
  res := .arr 2#usize (.u .U32 (by decide))
  Γ := [AeVal.nty (Aeneas.Std.Array U32 2#usize)]
  t := AeVal.nty (Aeneas.Std.Array U32 2#usize)
  argVal a := vCons a.1 vNil
  resVal := AeVal.emb
  fn a := arrays.incr_array a.1
  prog := incrArray.prog
  cert a y h := by
    obtain ⟨N, hN⟩ := incrArray_denote a.1 y h
    exact ⟨N, hN N le_rfl⟩

/-- **The compiler theorem at `arrays.incr_array`.** For a result `(P, bytes)` of the
    compiler at the Aeneas entry on `incrArraySrc` under `incrAbi`: from every entry state
    satisfying `incrAbi.Regions`, every value `v` of a run of `arrays.incr_array` from it is
    matched by a halting run of the machine on the decoded bytes from which `incrAbi` reads
    back `v`, with the entry stack register and the entry bytes outside the stack words and
    the array. It is `NFEntry.compileR_correct` at `aeneasEntry`. -/
theorem incrArray_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR incrArraySrc incrAbi "incr_array" = some (P, bytes))
    (sa : AState) (hsep : incrAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns incrAbi incrArraySrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ incrAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") incrAbi.frameLo incrAbi.frameHi) →
        (∀ p ∈ incrAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct incrArraySrc incrAbi "incr_array" P bytes hc sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

/-- The secrecy record of `incr_array`: the array and the result are secret. -/
def incrSecrecy : _root_.Hax.FnSecrecy where
  fn := "incr_array"
  params := [("x", .secret)]
  ret := .secret

/-- **Constant time of the bytes at `arrays.incr_array`.** For a result `(P, bytes)` of the
    compiler at the Aeneas entry on `incrArraySrc` under `incrAbi`, every decoding of `bytes`
    is constant time under `ctRegime` between entry states satisfying `incrAbi.Regions`, agreeing on
    the public data of `incrAbi` (the stack register and the address of the array, not its
    words), from each of which `arrays.incr_array` has a run. It is `aeneasEntry_compileR_ct`
    with the level check of the program, the label check and the distinct names of the
    layout. -/
theorem incrArray_compileR_ct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR incrArraySrc incrAbi "incr_array" = some (P, bytes))
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    CT.ConstantTimeRel
      (fun s₁ s₂ => incrAbi.PubAgree s₁ s₂ ∧ incrAbi.Regions s₁ ∧ incrAbi.Regions s₂
        ∧ aeneasPre incrAbi incrArraySrc s₁ ∧ aeneasPre incrAbi incrArraySrc s₂
        ∧ (∃ v, aeneasRuns incrAbi incrArraySrc s₁ v)
        ∧ (([] : List CatCrypt.Crypto.Hax.LinkedFn) = []
          ∨ ∃ v, aeneasRuns incrAbi incrArraySrc s₂ v))
      (fun s t => ∃ s', X86Backend.DecodedCT.RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  aeneasEntry_compileR_ct incrSecrecy incrArraySrc incrAbi "incr_array" P bytes hc
    (fun q hq => by
      unfold aeneasToNF at hq
      split at hq
      · cases hq
        show (Dialects.NFLeak.NFProg.levelCheck' (nfLeakModelL []) incrArray.prog
          (CatCrypt.Crypto.Hax.ImpToNF.entryLabels
            (CatCrypt.Crypto.Hax.ImpToNF.paramLevelOf incrSecrecy) (abiEntry incrAbi))).isSome
          = true
        decide +kernel
      · cases hq)
    (by decide) (by decide) hd

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
