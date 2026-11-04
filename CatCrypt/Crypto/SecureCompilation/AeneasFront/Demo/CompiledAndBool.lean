/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryCT
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestBitwise

/-!
# A Boolean result through the Aeneas entry: `bitwise.and_bool`

`bitwise.and_bool` of the Aeneas test output (`AeneasFront.Demo.TestBitwise`, copied unchanged
from Aeneas commit `b08bf81`) returns the conjunction `a && b` of its two Boolean arguments.
`reifyAeneas%` reads it at the result map `bitRes` of a Boolean result: each argument is the
word `boolW` of the layout, whose bit is bound first (`Reify.argBit`); the result `ok (a && b)`
is read by `Reify.okBit`, the prefix of the conjunction of the two bits (`readBitConn`) followed
by the bit-to-word step `bitWordP`, which selects the literal `1` or `0` by the bit with the
call `select` and returns the word. This module makes that output a source of the Aeneas entry
at the result code `AeTy.bool` and states the correctness and the constant time of the bytes
the compiler `NFEntry.compileR` returns for it under the System V layout `andBoolAbi`.

* The layout: `a` in `%rdi` and `b` in `%rsi`, each a scalar of the bound `1`, the result in
  `%rax`. The result is read back as the integer `0` or `1` of the conjunction
  (`andBool_result`, an instance of `aeneasRuns_bool`).
* `andBool_compileR_correct` is `NFEntry.compileR_correct` at `aeneasEntry` and the source.
* `andBool_compileR_ct` is `aeneasEntry_compileR_ct` with both arguments and the result secret:
  the program has no branch.

The bytes are written by the row `aeneas_and_bool` of `linked-kernel-emit`.

## Main results

* `andBool_denote` — a value of `bitwise.and_bool` is the denotation of its NF program.
* `andBoolAbi`, `andBoolSrc` — the layout and the source.
* `andBool_result` — the read-back of the result.
* `andBool_compileR_correct` — the compiler theorem at the source.
* `andBool_compileR_ct` — constant time of the bytes at the source.
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
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- `bitwise.and_bool` read as an NF program with a Boolean result. -/
def andBool := reifyAeneas% bitwise.and_bool

/-- A value of `bitwise.and_bool` is, as the word of the layout, the denotation of its NF
    program in the compiler's semantics. -/
theorem andBool_denote (a b z : Bool) (h : bitwise.and_bool a b = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel andBool.prog (wCons a (wCons b vNil)) =
      some (.cons (boolW z) .nil) :=
  ReifyG.toDenote (andBool.sound a b) h

/-- The System V layout of `and_bool`: `a` in `%rdi` and `b` in `%rsi`, each a scalar of the
    bound `1`, the result in `%rax`, the stack frame from `-256` to `-8`. The parameters are
    listed from the last argument. -/
def andBoolAbi : AbiLayout where
  args := [⟨"b", "%rsi", .scalar⟩, ⟨"a", "%rdi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := [("%rdi", 1), ("%rsi", 1)]
  frameLo := -256
  frameHi := -8

/-- **`bitwise.and_bool` as a source of the Aeneas entry**: `AeSrc.ofFn` at the argument codes
    `[.bool, .bool]` and the result code `.bool`, with the program and the certificate of the
    output of `reifyAeneas%` (`andBool`, `andBool_denote`). -/
def andBoolSrc : AeSrc :=
  AeSrc.ofFn [.bool, .bool] .bool (fun a => bitwise.and_bool a.1 a.2.1) andBool.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := andBool_denote a.1 a.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The read-back of the result**: a run of `bitwise.and_bool` from an entry state returns
    the integer `0` or `1` of the conjunction of its arguments. -/
theorem andBool_result (sa : AState) (v : Value) (h : aeneasRuns andBoolAbi andBoolSrc sa v) :
    ∃ a b : Bool, v = .int ((a && b).toNat : Int) := by
  obtain ⟨⟨a, b, u⟩, y, hy, hv⟩ := aeneasRuns_bool h
  have hy' : (RustM.ok (a && b) : RustM Bool) = .ok y := hy
  cases hy'
  exact ⟨a, b, hv⟩

/-- **The compiler theorem at `bitwise.and_bool`.** For a result `(P, bytes)` of the compiler
    at the Aeneas entry on `andBoolSrc` under `andBoolAbi`: from every entry state satisfying
    `andBoolAbi.Regions`, every value `v` of a run of `bitwise.and_bool` from it is matched by
    a halting run of the machine on the decoded bytes from which `andBoolAbi` reads back `v` in
    `%rax`, with the entry stack register and the entry bytes outside the stack words. It is
    `NFEntry.compileR_correct` at `aeneasEntry`. -/
theorem andBool_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR andBoolSrc andBoolAbi "and_bool" = some (P, bytes))
    (sa : AState) (hsep : andBoolAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns andBoolAbi andBoolSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ andBoolAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") andBoolAbi.frameLo andBoolAbi.frameHi) →
        (∀ p ∈ andBoolAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct andBoolSrc andBoolAbi "and_bool" P bytes hc sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

/-- The secrecy record of `and_bool`: both arguments and the result are secret. -/
def andBoolSecrecy : _root_.Hax.FnSecrecy where
  fn := "and_bool"
  params := [("b", .secret), ("a", .secret)]
  ret := .secret

/-- **Constant time of the bytes at `bitwise.and_bool`.** For a result `(P, bytes)` of the
    compiler at the Aeneas entry on `andBoolSrc` under `andBoolAbi`, every decoding of `bytes`
    is constant time under `ctRegime` between entry states satisfying `andBoolAbi.Regions`,
    agreeing on the public data of `andBoolAbi` (the stack register; both arguments are
    secret), from each of which `bitwise.and_bool` has a run. It is `aeneasEntry_compileR_ct`
    with the level check of the program, the label check and the distinct names of the
    layout. -/
theorem andBool_compileR_ct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR andBoolSrc andBoolAbi "and_bool" = some (P, bytes))
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    CT.ConstantTimeRel
      (fun s₁ s₂ => andBoolAbi.PubAgree s₁ s₂ ∧ andBoolAbi.Regions s₁ ∧ andBoolAbi.Regions s₂
        ∧ aeneasPre andBoolAbi andBoolSrc s₁ ∧ aeneasPre andBoolAbi andBoolSrc s₂
        ∧ (∃ v, aeneasRuns andBoolAbi andBoolSrc s₁ v)
        ∧ (([] : List CatCrypt.Crypto.Hax.LinkedFn) = []
          ∨ ∃ v, aeneasRuns andBoolAbi andBoolSrc s₂ v))
      (fun s t => ∃ s', X86Backend.DecodedCT.RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  aeneasEntry_compileR_ct andBoolSecrecy andBoolSrc andBoolAbi "and_bool" P bytes hc
    (fun q hq => by
      unfold aeneasToNF at hq
      split at hq
      · cases hq
        show (Dialects.NFLeak.NFProg.levelCheck' (nfLeakModelL []) andBool.prog
          (CatCrypt.Crypto.Hax.ImpToNF.entryLabels
            (CatCrypt.Crypto.Hax.ImpToNF.paramLevelOf andBoolSecrecy) (abiEntry andBoolAbi))).isSome
          = true
        decide +kernel
      · cases hq)
    (by decide) (by decide) hd

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
