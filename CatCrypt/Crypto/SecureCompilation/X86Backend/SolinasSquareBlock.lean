/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# The CryptOpt `fiat_curve25519_solinas_square` kernel as a `JInstr 64` block

`solinasSquareBlock` is the instruction list that
`NasmParse.parseNasm` produces from
`bench/cryptopt/fiat_curve25519_solinas_square.asm`: the 99 instructions of the
function body, without the final `ret`, which `parseNasm` accepts as the block
terminator. The kernel reads four 64-bit input limbs at `[rsi + 0]`, `[rsi + 8]`,
`[rsi + 16]`, `[rsi + 24]`, writes four output limbs at the same offsets of
`rdi`, and saves and restores `rbx`, `rbp`, `r12`–`r15` in the red zone below
`rsp`.

The list is a literal so that proofs can unfold it: the parser runs on file text,
which is not available to the kernel.

## Main results

* `solinasSquareBlock`: the kernel as a `List (JInstr 64)`.
* `solinasSquareBlock_length`: the block has 99 instructions.
* `solinasSeg1` … `solinasSeg4`, `solinasBody`, `solinasBody_eq_block`: the block in
  four segments, which concatenate to `solinasSquareBlock` by `rfl`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The body of `fiat_curve25519_solinas_square` as parsed by `parseNasm` from
    `bench/cryptopt/fiat_curve25519_solinas_square.asm`. -/
def solinasSquareBlock : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsi" 0,
    .mulxMem "%r10" "%rax" (.reg "%rdx") "%rsi" 8,
    .loadMem "%rdx" "%rsi" 0,
    .mulxMem "%rcx" "%r11" (.reg "%rdx") "%rsi" 16,
    .xor_ "%rdx" (.reg "%rdx"),
    .adox "%r11" (.reg "%r10"),
    .loadMem "%rdx" "%rsi" 0,
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%rdx"),
    .loadMem "%rdx" "%rsi" 24,
    .storeMem "%rsp" (-128) (.reg "%rbx"),
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 0,
    .loadMem "%rdx" "%rsi" 8,
    .storeMem "%rsp" (-120) (.reg "%rbp"),
    .storeMem "%rsp" (-112) (.reg "%r12"),
    .mulx "%r12" "%rbp" (.reg "%rdx") (.reg "%rdx"),
    .adox "%r10" (.reg "%rcx"),
    .loadMem "%rdx" "%rsi" 8,
    .storeMem "%rsp" (-104) (.reg "%r13"),
    .mulxMem "%r13" "%rcx" (.reg "%rdx") "%rsi" 16,
    .adcx "%rcx" (.reg "%r10"),
    .loadMem "%rdx" "%rsi" 8,
    .storeMem "%rsp" (-96) (.reg "%r14"),
    .mulxMem "%r14" "%r10" (.reg "%rdx") "%rsi" 24,
    .adox "%r10" (.reg "%rbx"),
    .adcx "%r13" (.reg "%r10"),
    .loadMem "%rdx" "%rsi" 16,
    .mulxMem "%r10" "%rbx" (.reg "%rdx") "%rsi" 24,
    .adox "%rbx" (.reg "%r14"),
    .mov "%rdx" (.imm 0),
    .mov "%r14" (.reg "%rdx"),
    .adcx "%r14" (.reg "%rbx"),
    .adox "%r10" (.reg "%rdx"),
    .mov "%rbx" (.imm 18446744073709551613),
    .inc "%rbx",
    .adox "%rax" (.reg "%rax"),
    .storeMem "%rsp" (-88) (.reg "%r15"),
    .mov "%r15" (.reg "%rdx"),
    .adcx "%r15" (.reg "%r10"),
    .adox "%r11" (.reg "%r11"),
    .adox "%rcx" (.reg "%rcx"),
    .adox "%r13" (.reg "%r13"),
    .adox "%r14" (.reg "%r14"),
    .setcc (.b) "%r10",
    .clc,
    .adcx "%r9" (.reg "%rax"),
    .adcx "%rbp" (.reg "%r11"),
    .adcx "%r12" (.reg "%rcx"),
    .loadMem "%rdx" "%rsi" 16,
    .mulx "%r11" "%rax" (.reg "%rdx") (.reg "%rdx"),
    .adcx "%rax" (.reg "%r13"),
    .adcx "%r11" (.reg "%r14"),
    .adox "%r15" (.reg "%r15"),
    .loadMem "%rdx" "%rsi" 24,
    .mulx "%r13" "%rcx" (.reg "%rdx") (.reg "%rdx"),
    .mov "%rdx" (.imm 38),
    .mulx "%rbx" "%r14" (.reg "%rdx") (.reg "%rax"),
    .adcx "%rcx" (.reg "%r15"),
    .movzx "%rax" 8 "%r10",
    .mov "%r15" (.imm 0),
    .adox "%rax" (.reg "%r15"),
    .movzx "%r15" 8 "%r10",
    .lea "%r15" "%r15" "%rax" 1 0,
    .adcx "%r15" (.reg "%r13"),
    .mulx "%r13" "%r10" (.reg "%rdx") (.reg "%r11"),
    .testN 8 "%rax" (.reg "%rax"),
    .adox "%r10" (.reg "%r9"),
    .mulx "%r11" "%r9" (.reg "%rdx") (.reg "%rcx"),
    .adox "%r9" (.reg "%rbp"),
    .mulx "%rcx" "%rbp" (.reg "%rdx") (.reg "%r15"),
    .adox "%rbp" (.reg "%r12"),
    .mov "%r12" (.imm 0),
    .adox "%rcx" (.reg "%r12"),
    .adcx "%r14" (.reg "%r8"),
    .adcx "%rbx" (.reg "%r10"),
    .adcx "%r13" (.reg "%r9"),
    .adcx "%r11" (.reg "%rbp"),
    .adc "%rcx" (.imm 0),
    .mulx "%rax" "%r8" (.reg "%rdx") (.reg "%rcx"),
    .xor_ "%rax" (.reg "%rax"),
    .adox "%r8" (.reg "%r14"),
    .mov "%r12" (.reg "%rax"),
    .adox "%r12" (.reg "%rbx"),
    .storeMem "%rdi" 8 (.reg "%r12"),
    .mov "%r15" (.reg "%rax"),
    .adox "%r15" (.reg "%r13"),
    .mov "%r10" (.reg "%rax"),
    .adox "%r10" (.reg "%r11"),
    .storeMem "%rdi" 24 (.reg "%r10"),
    .mov "%r9" (.reg "%rax"),
    .cmovcc (.o) "%r9" (.reg "%rdx"),
    .adcx "%r8" (.reg "%r9"),
    .storeMem "%rdi" 16 (.reg "%r15"),
    .storeMem "%rdi" 0 (.reg "%r8"),
    .loadMem "%rbx" "%rsp" (-128),
    .loadMem "%rbp" "%rsp" (-120),
    .loadMem "%r12" "%rsp" (-112),
    .loadMem "%r13" "%rsp" (-104),
    .loadMem "%r14" "%rsp" (-96),
    .loadMem "%r15" "%rsp" (-88) ]

/-- The block has 99 instructions, one per instruction line of the file other
    than the final `ret`. -/
theorem solinasSquareBlock_length : solinasSquareBlock.length = 99 := rfl


/-! ## The `solinas_square` body

The 99 instructions of the file in four segments, which the ascent of the kernel
(`Ascent/CorresX86Mem.lean`) closes one at a time:
the partial products and the first carry chains (lines 1–33), the doubling and the
reduction multiplies around `inc`, `setc`, `clc`, `movzx`, `lea` and `test`
(lines 34–65), the final reduction with `adc`, `cmovo` and the output stores
(lines 66–93), and the restores of the spilled registers (lines 94–99). -/

/-- Instructions 1–33 of `solinas_square`. -/
def solinasSeg1 : List (JInstr 64) :=
  [.loadMem "%rdx" "%rsi" 0,
   .mulxMem "%r10" "%rax" (.reg "%rdx") "%rsi" 8,
   .loadMem "%rdx" "%rsi" 0,
   .mulxMem "%rcx" "%r11" (.reg "%rdx") "%rsi" 16,
   .xor_ "%rdx" (.reg "%rdx"),
   .adox "%r11" (.reg "%r10"),
   .loadMem "%rdx" "%rsi" 0,
   .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%rdx"),
   .loadMem "%rdx" "%rsi" 24,
   .storeMem "%rsp" (-0x80) (.reg "%rbx"),
   .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 0,
   .loadMem "%rdx" "%rsi" 8,
   .storeMem "%rsp" (-0x78) (.reg "%rbp"),
   .storeMem "%rsp" (-0x70) (.reg "%r12"),
   .mulx "%r12" "%rbp" (.reg "%rdx") (.reg "%rdx"),
   .adox "%r10" (.reg "%rcx"),
   .loadMem "%rdx" "%rsi" 8,
   .storeMem "%rsp" (-0x68) (.reg "%r13"),
   .mulxMem "%r13" "%rcx" (.reg "%rdx") "%rsi" 16,
   .adcx "%rcx" (.reg "%r10"),
   .loadMem "%rdx" "%rsi" 8,
   .storeMem "%rsp" (-0x60) (.reg "%r14"),
   .mulxMem "%r14" "%r10" (.reg "%rdx") "%rsi" 24,
   .adox "%r10" (.reg "%rbx"),
   .adcx "%r13" (.reg "%r10"),
   .loadMem "%rdx" "%rsi" 16,
   .mulxMem "%r10" "%rbx" (.reg "%rdx") "%rsi" 24,
   .adox "%rbx" (.reg "%r14"),
   .mov "%rdx" (.imm 0),
   .mov "%r14" (.reg "%rdx"),
   .adcx "%r14" (.reg "%rbx"),
   .adox "%r10" (.reg "%rdx"),
   .mov "%rbx" (.imm 18446744073709551613)]

/-- Instructions 34–65 of `solinas_square`. -/
def solinasSeg2 : List (JInstr 64) :=
  [.inc "%rbx",
   .adox "%rax" (.reg "%rax"),
   .storeMem "%rsp" (-0x58) (.reg "%r15"),
   .mov "%r15" (.reg "%rdx"),
   .adcx "%r15" (.reg "%r10"),
   .adox "%r11" (.reg "%r11"),
   .adox "%rcx" (.reg "%rcx"),
   .adox "%r13" (.reg "%r13"),
   .adox "%r14" (.reg "%r14"),
   .setcc .b "%r10",
   .clc,
   .adcx "%r9" (.reg "%rax"),
   .adcx "%rbp" (.reg "%r11"),
   .adcx "%r12" (.reg "%rcx"),
   .loadMem "%rdx" "%rsi" 16,
   .mulx "%r11" "%rax" (.reg "%rdx") (.reg "%rdx"),
   .adcx "%rax" (.reg "%r13"),
   .adcx "%r11" (.reg "%r14"),
   .adox "%r15" (.reg "%r15"),
   .loadMem "%rdx" "%rsi" 24,
   .mulx "%r13" "%rcx" (.reg "%rdx") (.reg "%rdx"),
   .mov "%rdx" (.imm 38),
   .mulx "%rbx" "%r14" (.reg "%rdx") (.reg "%rax"),
   .adcx "%rcx" (.reg "%r15"),
   .movzx "%rax" 8 "%r10",
   .mov "%r15" (.imm 0),
   .adox "%rax" (.reg "%r15"),
   .movzx "%r15" 8 "%r10",
   .lea "%r15" "%r15" "%rax" 1 0,
   .adcx "%r15" (.reg "%r13"),
   .mulx "%r13" "%r10" (.reg "%rdx") (.reg "%r11"),
   .testN 8 "%rax" (.reg "%rax")]

/-- Instructions 66–93 of `solinas_square`. -/
def solinasSeg3 : List (JInstr 64) :=
  [.adox "%r10" (.reg "%r9"),
   .mulx "%r11" "%r9" (.reg "%rdx") (.reg "%rcx"),
   .adox "%r9" (.reg "%rbp"),
   .mulx "%rcx" "%rbp" (.reg "%rdx") (.reg "%r15"),
   .adox "%rbp" (.reg "%r12"),
   .mov "%r12" (.imm 0),
   .adox "%rcx" (.reg "%r12"),
   .adcx "%r14" (.reg "%r8"),
   .adcx "%rbx" (.reg "%r10"),
   .adcx "%r13" (.reg "%r9"),
   .adcx "%r11" (.reg "%rbp"),
   .adc "%rcx" (.imm 0),
   .mulx "%rax" "%r8" (.reg "%rdx") (.reg "%rcx"),
   .xor_ "%rax" (.reg "%rax"),
   .adox "%r8" (.reg "%r14"),
   .mov "%r12" (.reg "%rax"),
   .adox "%r12" (.reg "%rbx"),
   .storeMem "%rdi" 8 (.reg "%r12"),
   .mov "%r15" (.reg "%rax"),
   .adox "%r15" (.reg "%r13"),
   .mov "%r10" (.reg "%rax"),
   .adox "%r10" (.reg "%r11"),
   .storeMem "%rdi" 24 (.reg "%r10"),
   .mov "%r9" (.reg "%rax"),
   .cmovcc .o "%r9" (.reg "%rdx"),
   .adcx "%r8" (.reg "%r9"),
   .storeMem "%rdi" 16 (.reg "%r15"),
   .storeMem "%rdi" 0 (.reg "%r8")]

/-- Instructions 94–99 of `solinas_square`. -/
def solinasSeg4 : List (JInstr 64) :=
  [.loadMem "%rbx" "%rsp" (-0x80),
   .loadMem "%rbp" "%rsp" (-0x78),
   .loadMem "%r12" "%rsp" (-0x70),
   .loadMem "%r13" "%rsp" (-0x68),
   .loadMem "%r14" "%rsp" (-0x60),
   .loadMem "%r15" "%rsp" (-0x58)]

/-- The body of `solinas_square`, without the final `ret`. -/
def solinasBody : List (JInstr 64) := solinasSeg1 ++ solinasSeg2 ++ solinasSeg3 ++ solinasSeg4

/-- The four segments concatenate to the parsed kernel. -/
theorem solinasBody_eq_block : solinasBody = solinasSquareBlock := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock
