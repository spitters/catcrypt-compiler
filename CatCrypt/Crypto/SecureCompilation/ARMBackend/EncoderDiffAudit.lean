/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

/-!
# Reserved-register byte-differential audit for the A64 encoder

This module is a scratch differential pin: it checks the Lean `encodeAInst`/
`encodeBInst` output, word-for-word, against the bytes `aarch64-linux-gnu-as`
**and** `llvm-mc-18 -triple=aarch64` both produce (they agree on every word),
for the **reserved-register stress alphabet** — every operand slot exercised
with `wzr`/`xzr` (register 31), the A64 analogue of x86's RBP/R13 SIB footgun.
The reference words are taken from `objdump -d` on the assembled stress file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.EncoderDiffAudit

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

/-- Little-endian byte list of a 32-bit reference word (objdump prints the word
    value; `.text` stores it LE). -/
def refLE (w : Nat) : List (BitVec 8) := wordLE w

/-- A stress allocation pinning the SSA names used below to `wN`/`xN`. -/
def A : GpAlloc :=
  [ ("w0","w0"),("w1","w1"),("w2","w2"),("w3","w3"),("w4","w4"),("w5","w5"),
    ("w6","w6"),("w7","w7"),("w8","w8"),("w9","w9"),("w18","w18"),("w19","w19"),
    ("zr","wzr"),
    ("x0","x0"),("x1","x1"),("x2","x2"),("x6","x6"),("x8","x8"),("x9","x9"),
    ("xzr","xzr") ]

-- W-form, ZR in the *source* slot: `add w0, wzr, w1` → gas/llvm word 0x0b0103e0
example : encodeAInst A (.add "w0" "zr" "w1") = refLE 0x0b0103e0 := by native_decide
-- W-form, ZR in the *dest* slot: `sub wzr, w2, w3` → 0x4b03005f
example : encodeAInst A (.sub "zr" "w2" "w3") = refLE 0x4b03005f := by native_decide

-- X-form bignum, ZR sources (the SP/XZR=31 footgun, ZR semantics required):
-- `add x0, xzr, x1` → 0x8b0103e0
example : encodeBInst A (.add "x0" "xzr" "x1") = refLE 0x8b0103e0 := by native_decide
-- `mul x0, xzr, x1` → 0x9b017fe0
example : encodeBInst A (.mul "x0" "xzr" "x1") = refLE 0x9b017fe0 := by native_decide
-- `umulh x0, xzr, x1` → 0x9bc17fe0
example : encodeBInst A (.umulh "x0" "xzr" "x1") = refLE 0x9bc17fe0 := by native_decide
-- `csel x0, xzr, x1, cc` → 0x9a8133e0
example : encodeBInst A (.csel "x0" "xzr" "x1" .cc) = refLE 0x9a8133e0 := by native_decide
-- `mov x0, xzr` (= ORR x0, xzr, xzr) → 0xaa1f03e0
example : encodeBInst A (.mov "x0" "xzr") = refLE 0xaa1f03e0 := by native_decide
-- `movz xzr, #0x1234` — ZR in the *dest* of a MOVZ → 0xd282469f
example : encodeBInst A (.movz "xzr" 0x1234) = refLE 0xd282469f := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.EncoderDiffAudit
