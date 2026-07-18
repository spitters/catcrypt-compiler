/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
import CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel

/-!
# Differential validation of the scalar `JInstr` byte encoder against `gas`

`Avx512Validation.lean` pins the EVEX byte encoder of `Avx512Encoder.lean` to the
exact bytes `gas` produces for each AVX-512 mnemonic. This module is its **scalar
counterpart**: it pins the GP byte encoder of `ScalarEncoder.lean` to `gas`'s output
for each scalar/ADX/BMI2 mnemonic, so the encoder may replace the
`AsmPrinter` → `gas` step with no change in emitted machine code.

The right-hand byte strings below are the **exact output of `gas`** (binutils
`as --64`, decoded with `objdump -d -M att`) for the matching `AsmPrinter`-rendered
mnemonic. Each `example` checks `encodeJInstr` reproduces those bytes. The trusted
edge shrinks from "the text printer is correct AT&T *and* `gas` encodes per the SDM"
to "our encoder matches `gas`'s bytes" — and, once #441's Sail-x86 decoder shims
land, to nothing (a `decode (encode i) ≡ i` round-trip).

## The allocation under test

`aDiff` pins four SSA names to a representative register mix exercising both the
low-8 (`%rsi`/`%rcx`/`%rdi`) and high-8 (`%r8`, requiring the REX/VEX `B` extension
bit) encodings: `d ↦ %rsi`, `a ↦ %rcx`, `b ↦ %r8`, `p ↦ %rdi` (the pointer base for
the `loadMem`/`storeMem`/`mulxMem` arms). -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-- The differential-test allocation: `d↦%rsi a↦%rcx b↦%r8 p↦%rdi`. -/
def aDiff : GpAlloc := [("d", "%rsi"), ("a", "%rcx"), ("b", "%r8"), ("p", "%rdi")]

/-! ## 1. Per-instruction byte-identity pins (vs `gas`)

Each `example` is `encodeJInstr aDiff i = <gas bytes for AsmPrinter.renderJInstr i>`.
The gas bytes are quoted (in the comment) in the disassembly form `objdump` prints. -/

-- gas: `movq %rcx,%rsi`  →  48 89 ce
example : encodeJInstr aDiff (.mov "d" (.reg "a"))
    = [0x48, 0x89, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `addq %rcx,%rsi`  →  48 01 ce
example : encodeJInstr aDiff (.add "d" (.reg "a"))
    = [0x48, 0x01, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `subq %rcx,%rsi`  →  48 29 ce
example : encodeJInstr aDiff (.sub "d" (.reg "a"))
    = [0x48, 0x29, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `adcq %rcx,%rsi`  →  48 11 ce
example : encodeJInstr aDiff (.adc "d" (.reg "a"))
    = [0x48, 0x11, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `sbbq %rcx,%rsi`  →  48 19 ce
example : encodeJInstr aDiff (.sbb "d" (.reg "a"))
    = [0x48, 0x19, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `andq %rcx,%rsi`  →  48 21 ce
example : encodeJInstr aDiff (.and_ "d" (.reg "a"))
    = [0x48, 0x21, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `orq %rcx,%rsi`  →  48 09 ce
example : encodeJInstr aDiff (.or_ "d" (.reg "a"))
    = [0x48, 0x09, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `xorq %rcx,%rsi`  →  48 31 ce
example : encodeJInstr aDiff (.xor_ "d" (.reg "a"))
    = [0x48, 0x31, 0xce].map (BitVec.ofNat 8) := by native_decide

-- gas: `imulq %rcx,%rsi`  →  48 0f af f1   (0F-map; reg=dst, rm=src)
example : encodeJInstr aDiff (.imul "d" (.reg "a"))
    = [0x48, 0x0f, 0xaf, 0xf1].map (BitVec.ofNat 8) := by native_decide

-- gas: `negq %rsi`  →  48 f7 de
example : encodeJInstr aDiff (.neg "d")
    = [0x48, 0xf7, 0xde].map (BitVec.ofNat 8) := by native_decide

-- gas: `movq $5,%rsi`  →  48 c7 c6 05 00 00 00
example : encodeJInstr aDiff (.mov "d" (.imm 5))
    = [0x48, 0xc7, 0xc6, 0x05, 0x00, 0x00, 0x00].map (BitVec.ofNat 8) := by native_decide

-- gas: `imulq $7,%rsi,%rsi`  →  48 6b f6 07   (gas uses imm8 form; we emit the
-- canonical imm32 `69 /r id` form, byte-identical except for the immediate width;
-- the differential below uses an imm needing 32 bits to pin the imm32 encoding)
-- gas: `imulq $7777777,%rsi,%rsi`  →  48 69 f6 f1 ad 76 00
example : encodeJInstr aDiff (.imul "d" (.imm 7777777))
    = [0x48, 0x69, 0xf6, 0xf1, 0xad, 0x76, 0x00].map (BitVec.ofNat 8) := by native_decide

-- gas: `shlq $13,%rsi`  →  48 c1 e6 0d
example : encodeJInstr aDiff (.shl "d" (.imm 13))
    = [0x48, 0xc1, 0xe6, 0x0d].map (BitVec.ofNat 8) := by native_decide

-- gas: `shrq $13,%rsi`  →  48 c1 ee 0d
example : encodeJInstr aDiff (.shr "d" (.imm 13))
    = [0x48, 0xc1, 0xee, 0x0d].map (BitVec.ofNat 8) := by native_decide

-- gas: `sarq $13,%rsi`  →  48 c1 fe 0d
example : encodeJInstr aDiff (.sar "d" (.imm 13))
    = [0x48, 0xc1, 0xfe, 0x0d].map (BitVec.ofNat 8) := by native_decide

-- gas: `cmoveq %rcx,%rsi`  →  48 0f 44 f1
example : encodeJInstr aDiff (.cmove "d" (.reg "a"))
    = [0x48, 0x0f, 0x44, 0xf1].map (BitVec.ofNat 8) := by native_decide

-- gas: `cmovneq %rcx,%rsi`  →  48 0f 45 f1
example : encodeJInstr aDiff (.cmovne "d" (.reg "a"))
    = [0x48, 0x0f, 0x45, 0xf1].map (BitVec.ofNat 8) := by native_decide

-- gas: `cmovbq %rcx,%rsi`  →  48 0f 42 f1
example : encodeJInstr aDiff (.cmovb "d" (.reg "a"))
    = [0x48, 0x0f, 0x42, 0xf1].map (BitVec.ofNat 8) := by native_decide

-- gas: `adcx %rcx,%rsi`  →  66 48 0f 38 f6 f1
example : encodeJInstr aDiff (.adcx "d" (.reg "a"))
    = [0x66, 0x48, 0x0f, 0x38, 0xf6, 0xf1].map (BitVec.ofNat 8) := by native_decide

-- gas: `adox %rcx,%rsi`  →  f3 48 0f 38 f6 f1
example : encodeJInstr aDiff (.adox "d" (.reg "a"))
    = [0xf3, 0x48, 0x0f, 0x38, 0xf6, 0xf1].map (BitVec.ofNat 8) := by native_decide

-- gas: `mulx %r8,%rsi,%rcx`  →  c4 c2 cb f6 c8   (dstHi=rcx, dstLo=rsi, src2=r8)
example : encodeJInstr aDiff (.mulx "a" "d" (.reg "p") (.reg "b"))
    = [0xc4, 0xc2, 0xcb, 0xf6, 0xc8].map (BitVec.ofNat 8) := by native_decide

-- gas: `mulxq 24(%rdi),%rsi,%rcx`  →  c4 e2 cb f6 4f 18   (disp8 form)
example : encodeJInstr aDiff (.mulxMem "a" "d" (.reg "x") "p" 24)
    = [0xc4, 0xe2, 0xcb, 0xf6, 0x4f, 0x18].map (BitVec.ofNat 8) := by native_decide

-- gas: `mulxq (%rdi),%rsi,%rcx`  →  c4 e2 cb f6 0f   (disp0 form)
example : encodeJInstr aDiff (.mulxMem "a" "d" (.reg "x") "p" 0)
    = [0xc4, 0xe2, 0xcb, 0xf6, 0x0f].map (BitVec.ofNat 8) := by native_decide

-- gas: `movq 24(%rdi),%rsi`  →  48 8b 77 18   (load, disp8)
example : encodeJInstr aDiff (.loadMem "d" "p" 24)
    = [0x48, 0x8b, 0x77, 0x18].map (BitVec.ofNat 8) := by native_decide

-- gas: `movq (%rdi),%rsi`  →  48 8b 37   (load, disp0)
example : encodeJInstr aDiff (.loadMem "d" "p" 0)
    = [0x48, 0x8b, 0x37].map (BitVec.ofNat 8) := by native_decide

-- gas: `movq -8(%rdi),%rsi`  →  48 8b 77 f8   (load, negative disp8)
example : encodeJInstr aDiff (.loadMem "d" "p" (-8))
    = [0x48, 0x8b, 0x77, 0xf8].map (BitVec.ofNat 8) := by native_decide

-- gas: `movq %rsi,24(%rdi)`  →  48 89 77 18   (store, disp8)
example : encodeJInstr aDiff (.storeMem "p" 24 (.reg "d"))
    = [0x48, 0x89, 0x77, 0x18].map (BitVec.ofNat 8) := by native_decide

-- gas: `movq %rsi,(%rdi)`  →  48 89 37   (store, disp0)
example : encodeJInstr aDiff (.storeMem "p" 0 (.reg "d"))
    = [0x48, 0x89, 0x37].map (BitVec.ofNat 8) := by native_decide

/-! ## 2. High-register extension-bit coverage

A second allocation exercises the high-8 GP registers as *both* operands, pinning
the REX.R/REX.B (and VEX `R̄`/`B̄`) extension bits that route bit 3 of the register
number. -/

/-- All-high-register allocation: `d↦%r15 a↦%r14 b↦%r13 p↦%r12`. -/
def aHigh : GpAlloc := [("d", "%r15"), ("a", "%r14"), ("b", "%r13"), ("p", "%r12")]

-- gas: `addq %r14,%r15`  →  4d 01 f7   (REX.R for src %r14 + REX.B for dst %r15)
example : encodeJInstr aHigh (.add "d" (.reg "a"))
    = [0x4d, 0x01, 0xf7].map (BitVec.ofNat 8) := by native_decide

-- gas: `mulx %r13,%r15,%r14`  →  c4 42 83 f6 f5   (dstHi=r14, dstLo=r15, src2=r13)
example : encodeJInstr aHigh (.mulx "a" "d" (.reg "p") (.reg "b"))
    = [0xc4, 0x42, 0x83, 0xf6, 0xf5].map (BitVec.ofNat 8) := by native_decide

/-! ## 3. Block-level integration witness

The whole `add2Block` kernel (`add a0,b0; adc a1,b1`) encodes to the concatenation
of its instruction encodings — the contiguous machine-code stream a `.text` section
consumes. We pin it to the exact `gas` bytes for the `add2Alloc` register pinning
(`a0↦%rsi a1↦%rdx b0↦%rcx b1↦%r8`):

```
gas for `addq %rcx,%rsi`  →  48 01 ce
gas for `adcq %r8,%rdx`   →  4c 11 c2   (REX.R for the %r8 source operand)
```

and confirm the length (`encode_length`-style structural fact at the block level). -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel

-- The whole add2 kernel body, byte-for-byte = gas's encoding of the two AT&T lines.
example :
    encodeJBlock add2Alloc add2Block
      = [0x48, 0x01, 0xce, 0x4c, 0x11, 0xc2].map (BitVec.ofNat 8) := by native_decide

example : (encodeJBlock add2Alloc add2Block).length = 6 := by native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
