/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryCT
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Abort

/-!
# The compiler theorems of the Aeneas front at `joins.opt_add_1_or_panic`

`joins.opt_add_1_or_panic` of the Aeneas test output (`AeneasFront.Demo.TestJoins`) asserts its
Boolean argument `b` and returns `x + 1` for its `u32` argument `x`. `reifyAeneas%` reads it as
the NF program `Demo.optAdd` (`AeneasFront/Demo/Abort.lean`): the Boolean argument is the word
`boolW b` of the layout, its bit is bound first (`Reify.argBit`), and the assertion is the guard
`Reify.assert`. This module makes that output a source of the Aeneas entry and states the
correctness and the constant time of the bytes the compiler `NFEntry.compileR` returns for it
under the System V layout `optAddAbi`.

* The layout: `b` in `%rdi` as a scalar of the bound `1`, so that its register holds `0` or
  `1` and is public, `x` in `%rsi`, the result in `%rax`. The Boolean argument passes through
  the entry as `AeTy.bool`: its value map is the word `0` or `1` (`AeTy.val`), its layout entry
  the scalar of the bound `1`, its read-back the integer of the register (`AbiArg.read`), which
  the environment of a run holds as the encoding of the word.
* The source `optAddSrc` is `AeSrc.ofFn` at the codes `[.bool, .u .U32 _]` and `.u .U32 _`, with
  the program and the certificate of the output of `reifyAeneas%` (`optAdd_denote`).
* `optAdd_compileR_correct` is `NFEntry.compileR_correct` at `aeneasEntry` and the source.
* `optAdd_compileR_ct` is `aeneasEntry_compileR_ct` with `x` secret and `b` public: the level
  checker accepts the program, whose branch is on the bit of the public `b`.

The bytes are written by the row `aeneas_opt_add` of `linked-kernel-emit`.

## Main results

* `optAddAbi`, `optAddSrc` — the layout and the source.
* `optAdd_compileR_correct` — the compiler theorem at the source.
* `optAdd_compileR_ct` — constant time of the bytes at the source.
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

/-- The System V layout of `opt_add_1_or_panic`: the Boolean `b` in `%rdi`, a scalar of the
    bound `1`, the `u32` word `x` in `%rsi`, the result in `%rax`, the stack frame from `-256`
    to `-8`. The last parameter of the layout is the newest variable of the entry, so the
    parameters are listed from the last argument. -/
def optAddAbi : AbiLayout where
  args := [⟨"x", "%rsi", .scalar⟩, ⟨"b", "%rdi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := [("%rdi", 1)]
  frameLo := -256
  frameHi := -8

/-- **`joins.opt_add_1_or_panic` as a source of the Aeneas entry**: `AeSrc.ofFn` at its codes,
    with the program and the certificate of the output of `reifyAeneas%` (`optAdd`,
    `optAdd_denote`). -/
def optAddSrc : AeSrc :=
  AeSrc.ofFn [.bool, .u .U32 (by decide)] (.u .U32 (by decide))
    (fun a => joins.opt_add_1_or_panic a.1 a.2.1) optAdd.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := optAdd_denote a.1 a.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The compiler theorem at `joins.opt_add_1_or_panic`.** For a result `(P, bytes)` of the
    compiler at the Aeneas entry on `optAddSrc` under `optAddAbi`: from every entry state
    satisfying `optAddAbi.Regions`, every value `v` of a run of `joins.opt_add_1_or_panic` from
    it is matched by a halting run of the machine on the decoded bytes from which `optAddAbi`
    reads back `v` in `%rax`, with the entry stack register and the entry bytes outside the
    stack words. It is `NFEntry.compileR_correct` at `aeneasEntry`. -/
theorem optAdd_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR optAddSrc optAddAbi "opt_add_1_or_panic" = some (P, bytes))
    (sa : AState) (hsep : optAddAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns optAddAbi optAddSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ optAddAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") optAddAbi.frameLo optAddAbi.frameHi) →
        (∀ p ∈ optAddAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct optAddSrc optAddAbi "opt_add_1_or_panic" P bytes hc sa hsep v
      hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

/-- The secrecy record of `opt_add_1_or_panic`: the word and the result are secret, the
    Boolean is public. -/
def optAddSecrecy : _root_.Hax.FnSecrecy where
  fn := "opt_add_1_or_panic"
  params := [("x", .secret), ("b", .pub)]
  ret := .secret

/-- **Constant time of the bytes at `joins.opt_add_1_or_panic`.** For a result `(P, bytes)` of
    the compiler at the Aeneas entry on `optAddSrc` under `optAddAbi`, every decoding of
    `bytes` is constant time under `ctRegime` between entry states satisfying
    `optAddAbi.Regions`, agreeing on the public data of `optAddAbi` (the stack register and the
    register of `b`, not the word `x`), from each of which `joins.opt_add_1_or_panic` has a
    run. It is `aeneasEntry_compileR_ct` with the level check of the program, the label check
    and the distinct names of the layout. -/
theorem optAdd_compileR_ct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR optAddSrc optAddAbi "opt_add_1_or_panic" = some (P, bytes))
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    CT.ConstantTimeRel
      (fun s₁ s₂ => optAddAbi.PubAgree s₁ s₂ ∧ optAddAbi.Regions s₁ ∧ optAddAbi.Regions s₂
        ∧ aeneasPre optAddAbi optAddSrc s₁ ∧ aeneasPre optAddAbi optAddSrc s₂
        ∧ (∃ v, aeneasRuns optAddAbi optAddSrc s₁ v)
        ∧ (([] : List CatCrypt.Crypto.Hax.LinkedFn) = []
          ∨ ∃ v, aeneasRuns optAddAbi optAddSrc s₂ v))
      (fun s t => ∃ s', X86Backend.DecodedCT.RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  aeneasEntry_compileR_ct optAddSecrecy optAddSrc optAddAbi "opt_add_1_or_panic" P bytes hc
    (fun q hq => by
      unfold aeneasToNF at hq
      split at hq
      · cases hq
        show (Dialects.NFLeak.NFProg.levelCheck' (nfLeakModelL []) optAdd.prog
          (CatCrypt.Crypto.Hax.ImpToNF.entryLabels
            (CatCrypt.Crypto.Hax.ImpToNF.paramLevelOf optAddSecrecy) (abiEntry optAddAbi))).isSome
          = true
        decide +kernel
      · cases hq)
    (by decide) (by decide) hd

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
