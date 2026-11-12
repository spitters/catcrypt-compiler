/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryCT
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Signed
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestSigned

/-!
# The compiler theorem of the Aeneas front at signed scalars

The three functions of `AeneasFront.Demo.TestSigned` on `i32`, read by `reifyAeneas%` with the
signed instances of `AeneasFront.Signed`: a signed word is the word of its bit pattern, the
checked `+` and `-` are the calls `wrapping_add#32` and `wrapping_sub#32`, the literal `1#i32`
is bound as the literal of its pattern, and the branch on `x < y` binds the sign bit, the two
offset patterns and their unsigned comparison `Lt` (`Reify.iteBit` at `readBitSCmp`). Each
reading comes with the statement that a value of the function is, embedded, the denotation of
its program in `PDenP hax64WExit` from some fuel on. `signed.abs_diff` is then a source of the
Aeneas entry, at which the compiler theorem `NFEntry.compileR_correct` is stated under a
System V layout: `x` in `%rdi`, `y` in `%rsi`, the result in `%rax`.

## Main results

* `constAdd_denote`, `refIncr_denote`, `absDiff_denote`: the readings
* `absDiffSrc`: the source
* `absDiff_compileR_correct`: the compiler theorem
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

/-- `constants.add` read as an NF program. -/
def constAdd := reifyAeneas% constants.add

/-- A value of `constants.add` is the denotation of its NF program. -/
theorem constAdd_denote (a b z : I32) (h : constants.add a b = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel constAdd.prog (vCons a (vCons b vNil)) =
        some (.cons (embW (toU z)) .nil) :=
  Reify.toDenote (constAdd.sound a b) h

/-- `paper.ref_incr` read as an NF program. -/
def refIncr := reifyAeneas% paper.ref_incr

/-- A value of `paper.ref_incr` is the denotation of its NF program. -/
theorem refIncr_denote (x z : I32) (h : paper.ref_incr x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel refIncr.prog (vCons x vNil) = some (.cons (embW (toU z)) .nil) :=
  Reify.toDenote (refIncr.sound x) h

/-- `signed.abs_diff` read as an NF program. -/
def absDiff := reifyAeneas% signed.abs_diff

/-- A value of `signed.abs_diff` is the denotation of its NF program. -/
theorem absDiff_denote (x y z : I32) (h : signed.abs_diff x y = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel absDiff.prog (vCons x (vCons y vNil)) =
        some (.cons (embW (toU z)) .nil) :=
  Reify.toDenote (absDiff.sound x y) h

/-- The System V layout of `abs_diff`: `x` in `%rdi`, `y` in `%rsi`, the result in `%rax`.
    The parameters are listed from the last argument. -/
def absDiffAbi : AbiLayout where
  args := [⟨"y", "%rsi", .scalar⟩, ⟨"x", "%rdi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- **`abs_diff` as a source of the Aeneas entry**: the program and the certificate of the
    output of `reifyAeneas%` (`absDiff`, `absDiff_denote`). -/
def absDiffSrc : AeSrc :=
  AeSrc.ofFn [.i .I32 (by decide), .i .I32 (by decide)] (.i .I32 (by decide))
    (fun a => signed.abs_diff a.1 a.2.1) absDiff.prog
    (fun a y h => by
      obtain ⟨N, hN⟩ := absDiff_denote a.1 a.2.1 y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The compiler theorem at `abs_diff`.** It is `NFEntry.compileR_correct` at
    `aeneasEntry` and `absDiffSrc`. -/
theorem absDiff_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR absDiffSrc absDiffAbi "abs_diff" = some (P, bytes))
    (sa : AState) (hsep : absDiffAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns absDiffAbi absDiffSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ absDiffAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") absDiffAbi.frameLo absDiffAbi.frameHi) →
        (∀ p ∈ absDiffAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct absDiffSrc absDiffAbi "abs_diff" P bytes hc sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
