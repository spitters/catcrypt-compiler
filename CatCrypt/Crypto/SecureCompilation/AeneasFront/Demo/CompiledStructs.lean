/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryCT
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Structs
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestStructs

/-!
# The compiler theorem of the Aeneas front at structures of scalars

The three functions of `AeneasFront.Demo.TestStructs` on `constants.Pair U32 U32`, read by
`reifyAeneas%` with the structure instances of `AeneasFront.Structs`: a structure argument is
bound field by field, a projection `p.x` is the variable of its field, and a structure result
is the array of its field words, stored into the out-region `out` at the indices `0` and `1`
(`Reify.okStruct`). Each reading comes with the statement that a value of the function is the
denotation of its program in `PDenP hax64WExit` from some fuel on. `structs.incr_x` (a
structure argument and a structure result) is the source `AeSrc.ofStructFn` and `structs.sum`
(a structure argument and a scalar result) the source `AeSrc.ofFn` of `AeStruct.argFn`; at each
the compiler theorem `NFEntry.compileR_correct` is stated under a layout that passes the
fields in registers and, for `incr_x`, the out-region of two words at `%rdi`, read back after
the run.

## Main results

* `mkPair1_denote`, `incrX_denote`, `pairSum_denote`: the readings
* `incrXSrc`, `pairSumSrc`: the sources
* `incrX_compileR_correct`, `pairSum_compileR_correct`: the compiler theorems
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

/-- A pair of `u32` words is a structure of two `u32` fields. -/
instance : AeStruct (constants.Pair U32 U32) where
  fields := [.u .U32 (by decide), .u .U32 (by decide)]
  scalar := rfl
  toArgs s := (s.x, s.y, ())
  ofArgs a := ⟨a.1, a.2.1⟩
  ofArgs_toArgs _ := rfl
  toArgs_ofArgs _ := rfl

/-- `constants.mk_pair1` read as an NF program. -/
def mkPair1 := reifyAeneas% constants.mk_pair1

/-- A value of `constants.mk_pair1` is, as the array of its field words, the denotation of its
    NF program, at every out-region `out`. -/
theorem mkPair1_denote (out : Aeneas.Std.Array U64 (usz 2)) (x y : U32)
    (z : constants.Pair U32 U32) (h : constants.mk_pair1 x y = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel mkPair1.prog (vCons out (vCons x (vCons y vNil))) =
        some (.cons (embA (wordsArr (usz 2) [embW z.x, embW z.y]
          (usz_val_small (j := 2) (by decide)).symm)) .nil) :=
  ReifyG.toDenote (mkPair1.sound out x y) h

/-- `structs.incr_x` read as an NF program. -/
def incrX := reifyAeneas% structs.incr_x

/-- A value of `structs.incr_x` is, as the array of its field words, the denotation of its NF
    program at the fields of the argument, at every out-region `out`. -/
theorem incrX_denote (out : Aeneas.Std.Array U64 (usz 2)) (p z : constants.Pair U32 U32)
    (h : structs.incr_x p = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel incrX.prog (vCons out (vCons p.x (vCons p.y vNil))) =
        some (.cons (embA (wordsArr (usz 2) [embW z.x, embW z.y]
          (usz_val_small (j := 2) (by decide)).symm)) .nil) :=
  ReifyG.toDenote (incrX.sound out p) h

/-- `structs.sum` read as an NF program. -/
def pairSum := reifyAeneas% structs.sum

/-- A value of `structs.sum` is the denotation of its NF program at the fields of the
    argument. -/
theorem pairSum_denote (p : constants.Pair U32 U32) (z : U32) (h : structs.sum p = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel pairSum.prog (vCons p.x (vCons p.y vNil)) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (pairSum.sound p) h

/-- The layout of `incr_x`: the out-region of two words at `%rdi`, the fields `p.x` in `%rsi`
    and `p.y` in `%rdx`, the result the two words at the entry `%rdi`. The parameters are
    listed from the last. -/
def incrXAbi : AbiLayout where
  args := [⟨"p.y", "%rdx", .scalar⟩, ⟨"p.x", "%rsi", .scalar⟩, ⟨"out", "%rdi", .words 2⟩]
  consts := []
  result := .words "%rdi" 2
  bounds := []
  frameLo := -256
  frameHi := -8

/-- **`incr_x` as a source of the Aeneas entry**: `AeSrc.ofStructFn` at the program and the
    certificate of the output of `reifyAeneas%` (`incrX`, `incrX_denote`). -/
def incrXSrc : AeSrc :=
  AeSrc.ofStructFn (constants.Pair U32 U32) (constants.Pair U32 U32) [] (usz 2)
    (usz_val_small (j := 2) (by decide)) (fun p _ => structs.incr_x p) incrX.prog
    (fun a y h => by
      obtain ⟨o, x, x', ⟨⟩⟩ := a
      change (structs.incr_x ⟨x, x'⟩ >>= fun r => RustM.ok (AeStruct.toWords (usz 2) _ r)) =
        .ok y at h
      cases hf : structs.incr_x ⟨x, x'⟩ with
      | ok z =>
        rw [hf] at h
        cases h
        obtain ⟨N, hN⟩ := incrX_denote o ⟨x, x'⟩ z hf
        exact ⟨N, hN N le_rfl⟩
      | fail e => rw [hf] at h; cases h
      | div => rw [hf] at h; cases h)

/-- **The compiler theorem at `incr_x`**, a structure argument and a structure result. It is
    `NFEntry.compileR_correct` at `aeneasEntry` and `incrXSrc`. -/
theorem incrX_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR incrXSrc incrXAbi "incr_x" = some (P, bytes))
    (sa : AState) (hsep : incrXAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns incrXAbi incrXSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ incrXAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") incrXAbi.frameLo incrXAbi.frameHi) →
        (∀ p ∈ incrXAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct incrXSrc incrXAbi "incr_x" P bytes hc sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

/-- The layout of `sum`: the fields `p.x` in `%rdi` and `p.y` in `%rsi`, the result in `%rax`.
    The parameters are listed from the last. -/
def pairSumAbi : AbiLayout where
  args := [⟨"p.y", "%rsi", .scalar⟩, ⟨"p.x", "%rdi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- **`sum` as a source of the Aeneas entry**: `AeSrc.ofFn` at the field codes of the argument
    and the function `AeStruct.argFn`, with the program and the certificate of the output of
    `reifyAeneas%` (`pairSum`, `pairSum_denote`). -/
def pairSumSrc : AeSrc :=
  AeSrc.ofFn (AeStruct.fields (constants.Pair U32 U32) ++ []) (.u .U32 (by decide))
    (AeStruct.argFn fun p (_ : AeTy.Args []) => structs.sum p) pairSum.prog
    (fun a y h => by
      obtain ⟨x, x', ⟨⟩⟩ := a
      obtain ⟨N, hN⟩ := pairSum_denote ⟨x, x'⟩ y h
      exact ⟨N, hN N le_rfl⟩)

/-- **The compiler theorem at `sum`**, a structure argument and a scalar result. It is
    `NFEntry.compileR_correct` at `aeneasEntry` and `pairSumSrc`. -/
theorem pairSum_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR pairSumSrc pairSumAbi "sum" = some (P, bytes))
    (sa : AState) (hsep : pairSumAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns pairSumAbi pairSumSrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ pairSumAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") pairSumAbi.frameLo pairSumAbi.frameHi) →
        (∀ p ∈ pairSumAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x) := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
    aeneasEntry.compileR_correct pairSumSrc pairSumAbi "sum" P bytes hc sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
