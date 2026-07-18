/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64

/-!
# Hardwired-zero (`x0`) byte-differential audit for the RV64 encoder

The RISC-V analogue of x86's reserved-SIB-base footgun is the hardwired-zero
register `x0`/`zero`, which reads as `0` and discards writes. This module pins
the Lean `RiscvEncoder.encodeWord` / `RiscvEncoder64.encodeWord64` output,
word-for-word, against the bytes `riscv64-linux-gnu-as -march=rv64g_zbb`
(non-compressed, matching the encoder's fixed-32-bit width) **and**
`llvm-mc-18 -triple=riscv64 -mattr=+m,+zbb` both produce (they agree on every
word), for the **`zero`-in-every-slot stress alphabet**. The reference words
come from `objdump -d -M no-aliases` on the assembled stress file.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.EncoderDiffAudit

open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64

-- 64-bit `RInst64` subset, `zero` (x0) in every operand slot:
-- `add zero, a0, a1` (x0 dest, write discarded) → 0x00b50033
example : encodeWord64 (.add "zero" "a0" "a1") = some 0x00b50033 := by native_decide
-- `add a0, zero, a1` (x0 source rs1) → 0x00b00533
example : encodeWord64 (.add "a0" "zero" "a1") = some 0x00b00533 := by native_decide
-- `add a0, a1, zero` (x0 source rs2) → 0x00058533
example : encodeWord64 (.add "a0" "a1" "zero") = some 0x00058533 := by native_decide
-- `sltu a3, zero, a1` → 0x00b036b3
example : encodeWord64 (.sltu "a3" "zero" "a1") = some 0x00b036b3 := by native_decide
-- `mul a0, zero, a1` → 0x02b00533
example : encodeWord64 (.mul "a0" "zero" "a1") = some 0x02b00533 := by native_decide
-- `sub a0, zero, a1` (the RV negate idiom) → 0x40b00533
example : encodeWord64 (.sub "a0" "zero" "a1") = some 0x40b00533 := by native_decide
-- `mv a0, zero` (= addi a0, zero, 0) → 0x00000513
example : encodeWord64 (.mv "a0" "zero") = some 0x00000513 := by native_decide
-- `mv zero, a0` (= addi zero, a0, 0, x0 dest) → 0x00050013
example : encodeWord64 (.mv "zero" "a0") = some 0x00050013 := by native_decide

-- 32-bit scalar `RInst` subset, the same `zero`-slot stress on the *W forms:
-- `addw a0, a0, a1` → 0x00b5053b
example : encodeWord (.addw "a0" "a0" "a1") = 0x00b5053b := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.EncoderDiffAudit
