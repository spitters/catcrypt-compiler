/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# The CryptOpt `fiat_curve25519_carry_mul` kernel as a `JInstr 64` block

`carryMulBlock` is the instruction list that `NasmParse.parseNasm` produces from
`bench/cryptopt/fiat_curve25519_carry_mul.asm`: the 167 instructions of the function
body, without the final `ret`. The kernel multiplies two field elements of
`2^255 - 19` in radix `2^51`: it reads five input limbs at `[rsi + 8i]` and five at
`[rdx + 8i]` (through `rax` after `xchg rdx, rax`), stores the output pointer `rdi` at
`[rsp - 0x50]` after `sub rsp, 136`, and writes five output limbs through `r10`, the
register it reloads that pointer into. It saves and restores `rbx`, `rbp`, `r12`–`r15`
below `rsp`.

The list is a literal so that proofs can unfold it. `lake exe nasm-parse-kat`
(`NasmParseKat.lean`) checks that `parseNasm` of the file is this list.

## Main results

* `carryMulBlock`: the kernel as a `List (JInstr 64)`.
* `carryMulBlock_length`: the block has 167 instructions.
* `carryMulPre`, `carryMulMid1` … `carryMulMid5`, `carryMulLoadOut`, `carryMulTail`,
  `carryMulPost`, `carryMulBody_eq_block`: the block in segments, which concatenate to
  `carryMulBlock` by `rfl`. The segment boundaries are the instructions that write a
  register used as a memory base: `sub rsp` and `xchg rdx, rax` end `carryMulPre`,
  `mov r10, [rsp - 0x50]` is `carryMulLoadOut`, and `add rsp` is `carryMulPost`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The body of `fiat_curve25519_carry_mul` as parsed by `parseNasm` from
    `bench/cryptopt/fiat_curve25519_carry_mul.asm`. -/
def carryMulBlock : List (JInstr 64) :=
  [ .sub "%rsp" (.imm 136),
    .imulriMem "%rax" "%rdx" 24 19,
    .imulriMem "%r10" "%rdx" 16 19,
    .xchg "%rdx" "%rax",
    .mulxMem "%rcx" "%r11" (.reg "%rdx") "%rsi" 24,
    .mov "%r8" (.reg "%rdx"),
    .loadMem "%rdx" "%rsi" 0,
    .storeMem "%rsp" (-128) (.reg "%rbx"),
    .mulxMem "%rbx" "%r9" (.reg "%rdx") "%rax" 32,
    .loadMem "%rdx" "%rax" 8,
    .storeMem "%rsp" (-120) (.reg "%rbp"),
    .storeMem "%rsp" (-112) (.reg "%r12"),
    .mulxMem "%r12" "%rbp" (.reg "%rdx") "%rsi" 0,
    .loadMem "%rdx" "%rsi" 32,
    .storeMem "%rsp" (-104) (.reg "%r13"),
    .storeMem "%rsp" (-96) (.reg "%r14"),
    .mulx "%r14" "%r13" (.reg "%rdx") (.reg "%r8"),
    .loadMem "%rdx" "%rax" 24,
    .storeMem "%rsp" (-88) (.reg "%r15"),
    .storeMem "%rsp" (-80) (.reg "%rdi"),
    .mulxMem "%rdi" "%r15" (.reg "%rdx") "%rsi" 0,
    .imulriMem "%rdx" "%rax" 8 19,
    .storeMem "%rsp" (-72) (.reg "%rbx"),
    .storeMem "%rsp" (-64) (.reg "%r9"),
    .mulxMem "%r9" "%rbx" (.reg "%rdx") "%rsi" 32,
    .loadMem "%rdx" "%rsi" 24,
    .storeMem "%rsp" (-56) (.reg "%rdi"),
    .storeMem "%rsp" (-48) (.reg "%r15"),
    .mulx "%r15" "%rdi" (.reg "%rdx") (.reg "%r10"),
    .mov "%rdx" (.reg "%r10"),
    .storeMem "%rsp" (-40) (.reg "%r12"),
    .mulxMem "%r12" "%r10" (.reg "%rdx") "%rsi" 32,
    .imulriMem "%rdx" "%rax" 32 19,
    .add "%rbx" (.reg "%rdi"),
    .adcx "%r15" (.reg "%r9"),
    .add "%r10" (.reg "%r11"),
    .adcx "%rcx" (.reg "%r12"),
    .mulxMem "%r9" "%r11" (.reg "%rdx") "%rsi" 8,
    .mov "%rdi" (.reg "%rdx"),
    .loadMem "%rdx" "%rsi" 16,
    .storeMem "%rsp" (-32) (.reg "%rbp"),
    .mulx "%rbp" "%r12" (.reg "%rdx") (.reg "%r8"),
    .loadMem "%rdx" "%rax" 0,
    .storeMem "%rsp" (-24) (.reg "%r14"),
    .mulxMem "%r14" "%r8" (.reg "%rdx") "%rsi" 24,
    .mov "%rdx" (.reg "%rdi"),
    .storeMem "%rsp" (-16) (.reg "%r13"),
    .mulxMem "%r13" "%rdi" (.reg "%rdx") "%rsi" 32,
    .testN 8 "%rax" (.reg "%rax"),
    .adox "%rdi" (.reg "%r8"),
    .adox "%r14" (.reg "%r13"),
    .adcx "%rbx" (.reg "%r12"),
    .adcx "%rbp" (.reg "%r15"),
    .mulxMem "%r12" "%r15" (.reg "%rdx") "%rsi" 16,
    .xor_ "%r8" (.reg "%r8"),
    .adox "%r10" (.reg "%r15"),
    .adox "%r12" (.reg "%rcx"),
    .adcx "%rbx" (.reg "%r11"),
    .adcx "%r9" (.reg "%rbp"),
    .mov "%rcx" (.reg "%rdx"),
    .loadMem "%rdx" "%rax" 8,
    .mulxMem "%r13" "%r11" (.reg "%rdx") "%rsi" 16,
    .loadMem "%rdx" "%rsi" 32,
    .mulxMem "%r15" "%rbp" (.reg "%rdx") "%rax" 0,
    .mov "%rdx" (.reg "%rcx"),
    .mulxMem "%r8" "%rcx" (.reg "%rdx") "%rsi" 24,
    .xor_ "%rdx" (.reg "%rdx"),
    .adox "%rdi" (.reg "%r11"),
    .adox "%r13" (.reg "%r14"),
    .mov "%r14" (.reg "%rcx"),
    .adcxMem "%r14" "%rsp" (-16),
    .adcxMem "%r8" "%rsp" (-24),
    .loadMem "%rdx" "%rsi" 0,
    .mulxMem "%rcx" "%r11" (.reg "%rdx") "%rax" 0,
    .loadMem "%rdx" "%rax" 0,
    .storeMem "%rsp" (-8) (.reg "%r13"),
    .storeMem "%rsp" 0 (.reg "%rdi"),
    .mulxMem "%rdi" "%r13" (.reg "%rdx") "%rsi" 8,
    .xor_ "%rdx" (.reg "%rdx"),
    .adox "%rbx" (.reg "%r11"),
    .adox "%rcx" (.reg "%r9"),
    .adcx "%r10" (.reg "%r13"),
    .adcx "%rdi" (.reg "%r12"),
    .loadMem "%rdx" "%rsi" 16,
    .mulxMem "%r9" "%r12" (.reg "%rdx") "%rax" 16,
    .addMem "%r10" "%rsp" (-32),
    .adcxMem "%rdi" "%rsp" (-40),
    .mov "%rdx" (.reg "%rbx"),
    .shrd "%rdx" "%rcx" (.imm 51),
    .mov "%r11" (.imm 51),
    .bzhi "%r13" "%rbx" "%r11",
    .mov "%rbx" (.reg "%rdx"),
    .loadMem "%rdx" "%rax" 8,
    .mulxMem "%r11" "%rcx" (.reg "%rdx") "%rsi" 24,
    .adox "%rbp" (.reg "%rcx"),
    .adox "%r11" (.reg "%r15"),
    .add "%rbp" (.reg "%r12"),
    .adcx "%r9" (.reg "%r11"),
    .add "%r10" (.reg "%rbx"),
    .adc "%rdi" (.imm 0),
    .loadMem "%rdx" "%rsi" 8,
    .mulxMem "%r12" "%r15" (.reg "%rdx") "%rax" 8,
    .loadMem "%rdx" "%rax" 24,
    .mulxMem "%rcx" "%rbx" (.reg "%rdx") "%rsi" 8,
    .mov "%rdx" (.imm 51),
    .bzhi "%r11" "%r10" "%rdx",
    .shrd "%r10" "%rdi" (.imm 51),
    .add "%rbp" (.reg "%rbx"),
    .adcx "%rcx" (.reg "%r9"),
    .loadMem "%rdx" "%rax" 0,
    .mulxMem "%rdi" "%r9" (.reg "%rdx") "%rsi" 16,
    .xor_ "%rdx" (.reg "%rdx"),
    .adox "%r14" (.reg "%r9"),
    .adox "%rdi" (.reg "%r8"),
    .adcx "%r14" (.reg "%r15"),
    .adcx "%r12" (.reg "%rdi"),
    .loadMem "%rdx" "%rsi" 0,
    .mulxMem "%r15" "%r8" (.reg "%rdx") "%rax" 16,
    .add "%r14" (.reg "%r8"),
    .adcx "%r15" (.reg "%r12"),
    .add "%r14" (.reg "%r10"),
    .adc "%r15" (.imm 0),
    .mov "%rdx" (.reg "%r14"),
    .shrd "%rdx" "%r15" (.imm 51),
    .mov "%rbx" (.reg "%rdx"),
    .loadMem "%rdx" "%rax" 16,
    .mulxMem "%r9" "%r10" (.reg "%rdx") "%rsi" 8,
    .mov "%rdx" (.reg "%r10"),
    .addMem "%rdx" "%rsp" 0,
    .adcxMem "%r9" "%rsp" (-8),
    .mov "%rdi" (.imm 51),
    .bzhi "%r12" "%r14" "%rdi",
    .adoxMem "%rdx" "%rsp" (-48),
    .adoxMem "%r9" "%rsp" (-56),
    .add "%rdx" (.reg "%rbx"),
    .adc "%r9" (.imm 0),
    .xor_ "%r8" (.reg "%r8"),
    .adoxMem "%rbp" "%rsp" (-64),
    .adoxMem "%rcx" "%rsp" (-72),
    .bzhi "%r14" "%rdx" "%rdi",
    .shrd "%rdx" "%r9" (.imm 51),
    .add "%rbp" (.reg "%rdx"),
    .adc "%rcx" (.imm 0),
    .mov "%r15" (.reg "%rbp"),
    .shrd "%r15" "%rcx" (.imm 51),
    .imulri "%rbx" "%r15" 19,
    .loadMem "%r10" "%rsp" (-80),
    .storeMem "%r10" 24 (.reg "%r14"),
    .bzhi "%r9" "%rbp" "%rdi",
    .storeMem "%r10" 32 (.reg "%r9"),
    .lea "%r13" "%r13" "%rbx" 1 0,
    .bzhi "%r14" "%r13" "%rdi",
    .storeMem "%r10" 0 (.reg "%r14"),
    .shr "%r13" (.imm 51),
    .lea "%r13" "%r13" "%r11" 1 0,
    .bzhi "%r11" "%r13" "%rdi",
    .shr "%r13" (.imm 51),
    .lea "%r13" "%r13" "%r12" 1 0,
    .storeMem "%r10" 16 (.reg "%r13"),
    .storeMem "%r10" 8 (.reg "%r11"),
    .loadMem "%rbx" "%rsp" (-128),
    .loadMem "%rbp" "%rsp" (-120),
    .loadMem "%r12" "%rsp" (-112),
    .loadMem "%r13" "%rsp" (-104),
    .loadMem "%r14" "%rsp" (-96),
    .loadMem "%r15" "%rsp" (-88),
    .add "%rsp" (.imm 136) ]

set_option maxRecDepth 4000 in
/-- The block has 167 instructions, one per instruction line of the file other
    than the final `ret`. -/
theorem carryMulBlock_length : carryMulBlock.length = 167 := rfl

/-! ## The `carry_mul` body in segments -/

/-- Instructions 1–4: the frame allocation, the two multiplies by `19` read through
    `rdx`, and `xchg rdx, rax`. -/
def carryMulPre : List (JInstr 64) :=
  [.sub "%rsp" (.imm 136),
   .imulriMem "%rax" "%rdx" 24 19,
   .imulriMem "%r10" "%rdx" 16 19,
   .xchg "%rdx" "%rax"]

/-- Instructions 5–33 of `carry_mul`. -/
def carryMulMid1 : List (JInstr 64) :=
  [.mulxMem "%rcx" "%r11" (.reg "%rdx") "%rsi" 24,
   .mov "%r8" (.reg "%rdx"),
   .loadMem "%rdx" "%rsi" 0,
   .storeMem "%rsp" (-128) (.reg "%rbx"),
   .mulxMem "%rbx" "%r9" (.reg "%rdx") "%rax" 32,
   .loadMem "%rdx" "%rax" 8,
   .storeMem "%rsp" (-120) (.reg "%rbp"),
   .storeMem "%rsp" (-112) (.reg "%r12"),
   .mulxMem "%r12" "%rbp" (.reg "%rdx") "%rsi" 0,
   .loadMem "%rdx" "%rsi" 32,
   .storeMem "%rsp" (-104) (.reg "%r13"),
   .storeMem "%rsp" (-96) (.reg "%r14"),
   .mulx "%r14" "%r13" (.reg "%rdx") (.reg "%r8"),
   .loadMem "%rdx" "%rax" 24,
   .storeMem "%rsp" (-88) (.reg "%r15"),
   .storeMem "%rsp" (-80) (.reg "%rdi"),
   .mulxMem "%rdi" "%r15" (.reg "%rdx") "%rsi" 0,
   .imulriMem "%rdx" "%rax" 8 19,
   .storeMem "%rsp" (-72) (.reg "%rbx"),
   .storeMem "%rsp" (-64) (.reg "%r9"),
   .mulxMem "%r9" "%rbx" (.reg "%rdx") "%rsi" 32,
   .loadMem "%rdx" "%rsi" 24,
   .storeMem "%rsp" (-56) (.reg "%rdi"),
   .storeMem "%rsp" (-48) (.reg "%r15"),
   .mulx "%r15" "%rdi" (.reg "%rdx") (.reg "%r10"),
   .mov "%rdx" (.reg "%r10"),
   .storeMem "%rsp" (-40) (.reg "%r12"),
   .mulxMem "%r12" "%r10" (.reg "%rdx") "%rsi" 32,
   .imulriMem "%rdx" "%rax" 32 19]

/-- Instructions 34–63 of `carry_mul`. -/
def carryMulMid2 : List (JInstr 64) :=
  [.add "%rbx" (.reg "%rdi"),
   .adcx "%r15" (.reg "%r9"),
   .add "%r10" (.reg "%r11"),
   .adcx "%rcx" (.reg "%r12"),
   .mulxMem "%r9" "%r11" (.reg "%rdx") "%rsi" 8,
   .mov "%rdi" (.reg "%rdx"),
   .loadMem "%rdx" "%rsi" 16,
   .storeMem "%rsp" (-32) (.reg "%rbp"),
   .mulx "%rbp" "%r12" (.reg "%rdx") (.reg "%r8"),
   .loadMem "%rdx" "%rax" 0,
   .storeMem "%rsp" (-24) (.reg "%r14"),
   .mulxMem "%r14" "%r8" (.reg "%rdx") "%rsi" 24,
   .mov "%rdx" (.reg "%rdi"),
   .storeMem "%rsp" (-16) (.reg "%r13"),
   .mulxMem "%r13" "%rdi" (.reg "%rdx") "%rsi" 32,
   .testN 8 "%rax" (.reg "%rax"),
   .adox "%rdi" (.reg "%r8"),
   .adox "%r14" (.reg "%r13"),
   .adcx "%rbx" (.reg "%r12"),
   .adcx "%rbp" (.reg "%r15"),
   .mulxMem "%r12" "%r15" (.reg "%rdx") "%rsi" 16,
   .xor_ "%r8" (.reg "%r8"),
   .adox "%r10" (.reg "%r15"),
   .adox "%r12" (.reg "%rcx"),
   .adcx "%rbx" (.reg "%r11"),
   .adcx "%r9" (.reg "%rbp"),
   .mov "%rcx" (.reg "%rdx"),
   .loadMem "%rdx" "%rax" 8,
   .mulxMem "%r13" "%r11" (.reg "%rdx") "%rsi" 16,
   .loadMem "%rdx" "%rsi" 32]

/-- Instructions 64–92 of `carry_mul`. -/
def carryMulMid3 : List (JInstr 64) :=
  [.mulxMem "%r15" "%rbp" (.reg "%rdx") "%rax" 0,
   .mov "%rdx" (.reg "%rcx"),
   .mulxMem "%r8" "%rcx" (.reg "%rdx") "%rsi" 24,
   .xor_ "%rdx" (.reg "%rdx"),
   .adox "%rdi" (.reg "%r11"),
   .adox "%r13" (.reg "%r14"),
   .mov "%r14" (.reg "%rcx"),
   .adcxMem "%r14" "%rsp" (-16),
   .adcxMem "%r8" "%rsp" (-24),
   .loadMem "%rdx" "%rsi" 0,
   .mulxMem "%rcx" "%r11" (.reg "%rdx") "%rax" 0,
   .loadMem "%rdx" "%rax" 0,
   .storeMem "%rsp" (-8) (.reg "%r13"),
   .storeMem "%rsp" 0 (.reg "%rdi"),
   .mulxMem "%rdi" "%r13" (.reg "%rdx") "%rsi" 8,
   .xor_ "%rdx" (.reg "%rdx"),
   .adox "%rbx" (.reg "%r11"),
   .adox "%rcx" (.reg "%r9"),
   .adcx "%r10" (.reg "%r13"),
   .adcx "%rdi" (.reg "%r12"),
   .loadMem "%rdx" "%rsi" 16,
   .mulxMem "%r9" "%r12" (.reg "%rdx") "%rax" 16,
   .addMem "%r10" "%rsp" (-32),
   .adcxMem "%rdi" "%rsp" (-40),
   .mov "%rdx" (.reg "%rbx"),
   .shrd "%rdx" "%rcx" (.imm 51),
   .mov "%r11" (.imm 51),
   .bzhi "%r13" "%rbx" "%r11",
   .mov "%rbx" (.reg "%rdx")]

/-- Instructions 93–120 of `carry_mul`. -/
def carryMulMid4 : List (JInstr 64) :=
  [.loadMem "%rdx" "%rax" 8,
   .mulxMem "%r11" "%rcx" (.reg "%rdx") "%rsi" 24,
   .adox "%rbp" (.reg "%rcx"),
   .adox "%r11" (.reg "%r15"),
   .add "%rbp" (.reg "%r12"),
   .adcx "%r9" (.reg "%r11"),
   .add "%r10" (.reg "%rbx"),
   .adc "%rdi" (.imm 0),
   .loadMem "%rdx" "%rsi" 8,
   .mulxMem "%r12" "%r15" (.reg "%rdx") "%rax" 8,
   .loadMem "%rdx" "%rax" 24,
   .mulxMem "%rcx" "%rbx" (.reg "%rdx") "%rsi" 8,
   .mov "%rdx" (.imm 51),
   .bzhi "%r11" "%r10" "%rdx",
   .shrd "%r10" "%rdi" (.imm 51),
   .add "%rbp" (.reg "%rbx"),
   .adcx "%rcx" (.reg "%r9"),
   .loadMem "%rdx" "%rax" 0,
   .mulxMem "%rdi" "%r9" (.reg "%rdx") "%rsi" 16,
   .xor_ "%rdx" (.reg "%rdx"),
   .adox "%r14" (.reg "%r9"),
   .adox "%rdi" (.reg "%r8"),
   .adcx "%r14" (.reg "%r15"),
   .adcx "%r12" (.reg "%rdi"),
   .loadMem "%rdx" "%rsi" 0,
   .mulxMem "%r15" "%r8" (.reg "%rdx") "%rax" 16,
   .add "%r14" (.reg "%r8"),
   .adcx "%r15" (.reg "%r12")]

/-- Instructions 121–146 of `carry_mul`. -/
def carryMulMid5 : List (JInstr 64) :=
  [.add "%r14" (.reg "%r10"),
   .adc "%r15" (.imm 0),
   .mov "%rdx" (.reg "%r14"),
   .shrd "%rdx" "%r15" (.imm 51),
   .mov "%rbx" (.reg "%rdx"),
   .loadMem "%rdx" "%rax" 16,
   .mulxMem "%r9" "%r10" (.reg "%rdx") "%rsi" 8,
   .mov "%rdx" (.reg "%r10"),
   .addMem "%rdx" "%rsp" 0,
   .adcxMem "%r9" "%rsp" (-8),
   .mov "%rdi" (.imm 51),
   .bzhi "%r12" "%r14" "%rdi",
   .adoxMem "%rdx" "%rsp" (-48),
   .adoxMem "%r9" "%rsp" (-56),
   .add "%rdx" (.reg "%rbx"),
   .adc "%r9" (.imm 0),
   .xor_ "%r8" (.reg "%r8"),
   .adoxMem "%rbp" "%rsp" (-64),
   .adoxMem "%rcx" "%rsp" (-72),
   .bzhi "%r14" "%rdx" "%rdi",
   .shrd "%rdx" "%r9" (.imm 51),
   .add "%rbp" (.reg "%rdx"),
   .adc "%rcx" (.imm 0),
   .mov "%r15" (.reg "%rbp"),
   .shrd "%r15" "%rcx" (.imm 51),
   .imulri "%rbx" "%r15" 19]

/-- Instructions 5–146: the partial products, the column sums and the carry chain,
    reading memory through `rsi`, `rax` and `rsp` only. -/
def carryMulMid : List (JInstr 64) :=
  carryMulMid1 ++ carryMulMid2 ++ carryMulMid3 ++ carryMulMid4 ++ carryMulMid5

/-- Instruction 147: the output pointer reloaded into `r10`. -/
def carryMulLoadOut : List (JInstr 64) :=
  [.loadMem "%r10" "%rsp" (-80)]

/-- Instructions 148–166: the final carry, the output stores through `r10` and the
    restores of the saved registers. -/
def carryMulTail : List (JInstr 64) :=
  [.storeMem "%r10" 24 (.reg "%r14"),
   .bzhi "%r9" "%rbp" "%rdi",
   .storeMem "%r10" 32 (.reg "%r9"),
   .lea "%r13" "%r13" "%rbx" 1 0,
   .bzhi "%r14" "%r13" "%rdi",
   .storeMem "%r10" 0 (.reg "%r14"),
   .shr "%r13" (.imm 51),
   .lea "%r13" "%r13" "%r11" 1 0,
   .bzhi "%r11" "%r13" "%rdi",
   .shr "%r13" (.imm 51),
   .lea "%r13" "%r13" "%r12" 1 0,
   .storeMem "%r10" 16 (.reg "%r13"),
   .storeMem "%r10" 8 (.reg "%r11"),
   .loadMem "%rbx" "%rsp" (-128),
   .loadMem "%rbp" "%rsp" (-120),
   .loadMem "%r12" "%rsp" (-112),
   .loadMem "%r13" "%rsp" (-104),
   .loadMem "%r14" "%rsp" (-96),
   .loadMem "%r15" "%rsp" (-88)]

/-- Instruction 167: the frame release. -/
def carryMulPost : List (JInstr 64) :=
  [.add "%rsp" (.imm 136)]

set_option maxRecDepth 4000 in
/-- The segments concatenate to the parsed kernel. -/
theorem carryMulBody_eq_block :
    carryMulPre ++ carryMulMid ++ carryMulLoadOut ++ carryMulTail ++ carryMulPost =
      carryMulBlock := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock
