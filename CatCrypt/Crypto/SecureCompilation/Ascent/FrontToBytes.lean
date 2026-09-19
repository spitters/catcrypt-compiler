/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.DialectToBytes
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom

/-!
# A front-compiled program, its bytes, and its value

`cryptoDialectToJasminCom` lowers a `Com catCryptDialect` to a
`Com jasminDialect`. `comToArithBlock` recognises the result, `lowerBlock` turns
it into machine instructions, and `encodeJBlock` encodes them. This module runs
that chain on a program the front produced.

## What is proved

* `frontCom_recognise` — the front's output for `srcCD` is the two-operation
  `ArithBlock` the recogniser returns.
* `frontBytes_decode` — the bytes of the lowered block decode back to it.
* `frontBytes_denote` — running the decoded block leaves the front's output
  program's denotation in `%rdx`.
* `sample_front_bytes` — the concrete value, `(7 + 35) * 7 = 294`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-! ## 1. The dialect source and the front's output -/

/-- The two-input dialect context. -/
abbrev SrcCtx : Ctx := [CryptoTy.sword 64, CryptoTy.sword 64]

/-- `let s1 = a + b in let s2 = s1 * a in ret s2`, built natively as a
    `Com catCryptDialect`. -/
def srcCD : Com catCryptDialect SrcCtx (.sword 64) :=
  .var
    { op := .bvAdd 64, retTy_eq := rfl,
      args := .cons .here (.cons (.there .here) .nil) }
    (.var
      { op := .bvMul 64, retTy_eq := rfl,
        args := .cons .here (.cons (.there .here) .nil) }
      (.ret .here))

/-- The front lowers `srcCD` to the two-operation Jasmin-dialect program
    `comBlock2`. -/
theorem srcCD_front : cryptoDialectToJasminCom srcCD = some comBlock2 := rfl

/-! ## 2. Recognition, lowering and bytes -/

/-- The recogniser returns `block2` for the front's output. -/
theorem frontCom_recognise : comToArithBlock comBlock2 = some block2 :=
  comBlock2_recognise

/-- The machine block, written as the chain it comes from: the front's output for
    `srcCD`, recognised, then lowered. -/
def frontBlock : List (JInstr 64) :=
  match cryptoDialectToJasminCom srcCD with
  | some jcom =>
      match comToArithBlock jcom with
      | some ab => lowerBlock ab nm2 g2
      | none => []
  | none => []

/-- The chain lands the same instructions the lowering of `block2` gives. -/
theorem frontBlock_eq : frontBlock = demoBlock := by
  rw [frontBlock, srcCD_front]
  simp only [frontCom_recognise]
  rfl

/-- The bytes of the front's block. -/
def frontBytes : List (BitVec 8) := encodeJBlock idAlloc frontBlock

/-- The bytes decode back to the block they encode. -/
theorem frontBytes_decode :
    decodeJStream frontBlock.length frontBytes = some frontBlock := by
  rw [frontBytes, frontBlock_eq]
  exact demo_bytes_decode

/-- Running the decoded block leaves the front's output program's denotation in
    `%rdx`, for every machine state corresponding to the valuation. -/
theorem frontBytes_denote (s : JState 64) (V : Ctxt.Valuation Δ2)
    (hinterp : JStateInterpG nm2 V s) :
    (runBlock s frontBlock).get "%rdx" = comBlock2.denote V := by
  rw [frontBlock_eq]
  exact demo_bytes_denote s V hinterp

/-! ## 3. The concrete value -/

/-- On the sample state the block leaves `(7 + 35) * 7 = 294` in `%rdx`. -/
theorem sample_front_bytes :
    (runBlock sampleS2 frontBlock).get "%rdx" = (294 : BitVec 64) := by
  rw [frontBlock_eq]
  exact sample_dialect_bytes

end CatCrypt.Crypto.SecureCompilation.Ascent
