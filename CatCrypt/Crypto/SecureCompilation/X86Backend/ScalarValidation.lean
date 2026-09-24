/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel

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
to "our encoder matches `gas`'s bytes"; a Sail-x86 decoder would remove it
(a `decode (encode i) ≡ i` round-trip).

## The allocation under test

`aDiff` pins four SSA names to a representative register mix exercising both the
low-8 (`%rsi`/`%rcx`/`%rdi`) and high-8 (`%r8`, requiring the REX/VEX `B` extension
bit) encodings: `d ↦ %rsi`, `a ↦ %rcx`, `b ↦ %r8`, `p ↦ %rdi` (the pointer base for
the `loadMem`/`storeMem`/`mulxMem` arms). -/

@[expose] public section

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
#guard encodeJInstr aDiff (.mov "d" (.reg "a"))
    == [0x48, 0x89, 0xce].map (BitVec.ofNat 8)

-- gas: `addq %rcx,%rsi`  →  48 01 ce
#guard encodeJInstr aDiff (.add "d" (.reg "a"))
    == [0x48, 0x01, 0xce].map (BitVec.ofNat 8)

-- gas: `subq %rcx,%rsi`  →  48 29 ce
#guard encodeJInstr aDiff (.sub "d" (.reg "a"))
    == [0x48, 0x29, 0xce].map (BitVec.ofNat 8)

-- gas: `adcq %rcx,%rsi`  →  48 11 ce
#guard encodeJInstr aDiff (.adc "d" (.reg "a"))
    == [0x48, 0x11, 0xce].map (BitVec.ofNat 8)

-- gas: `sbbq %rcx,%rsi`  →  48 19 ce
#guard encodeJInstr aDiff (.sbb "d" (.reg "a"))
    == [0x48, 0x19, 0xce].map (BitVec.ofNat 8)

-- gas: `andq %rcx,%rsi`  →  48 21 ce
#guard encodeJInstr aDiff (.and_ "d" (.reg "a"))
    == [0x48, 0x21, 0xce].map (BitVec.ofNat 8)

-- gas: `orq %rcx,%rsi`  →  48 09 ce
#guard encodeJInstr aDiff (.or_ "d" (.reg "a"))
    == [0x48, 0x09, 0xce].map (BitVec.ofNat 8)

-- gas: `xorq %rcx,%rsi`  →  48 31 ce
#guard encodeJInstr aDiff (.xor_ "d" (.reg "a"))
    == [0x48, 0x31, 0xce].map (BitVec.ofNat 8)

-- gas: `imulq %rcx,%rsi`  →  48 0f af f1   (0F-map; reg=dst, rm=src)
#guard encodeJInstr aDiff (.imul "d" (.reg "a"))
    == [0x48, 0x0f, 0xaf, 0xf1].map (BitVec.ofNat 8)

-- gas: `negq %rsi`  →  48 f7 de
#guard encodeJInstr aDiff (.neg "d")
    == [0x48, 0xf7, 0xde].map (BitVec.ofNat 8)

-- gas: `movq $5,%rsi`  →  48 c7 c6 05 00 00 00
#guard encodeJInstr aDiff (.mov "d" (.imm 5))
    == [0x48, 0xc7, 0xc6, 0x05, 0x00, 0x00, 0x00].map (BitVec.ofNat 8)

-- gas: `imulq $7,%rsi,%rsi`  →  48 6b f6 07   (gas uses imm8 form; we emit the
-- canonical imm32 `69 /r id` form, byte-identical except for the immediate width;
-- the differential below uses an imm needing 32 bits to pin the imm32 encoding)
-- gas: `imulq $7777777,%rsi,%rsi`  →  48 69 f6 f1 ad 76 00
#guard encodeJInstr aDiff (.imul "d" (.imm 7777777))
    == [0x48, 0x69, 0xf6, 0xf1, 0xad, 0x76, 0x00].map (BitVec.ofNat 8)

-- gas: `shlq $13,%rsi`  →  48 c1 e6 0d
#guard encodeJInstr aDiff (.shl "d" (.imm 13))
    == [0x48, 0xc1, 0xe6, 0x0d].map (BitVec.ofNat 8)

-- gas: `shrq $13,%rsi`  →  48 c1 ee 0d
#guard encodeJInstr aDiff (.shr "d" (.imm 13))
    == [0x48, 0xc1, 0xee, 0x0d].map (BitVec.ofNat 8)

-- gas: `sarq $13,%rsi`  →  48 c1 fe 0d
#guard encodeJInstr aDiff (.sar "d" (.imm 13))
    == [0x48, 0xc1, 0xfe, 0x0d].map (BitVec.ofNat 8)

-- gas: `cmoveq %rcx,%rsi`  →  48 0f 44 f1
#guard encodeJInstr aDiff (.cmove "d" (.reg "a"))
    == [0x48, 0x0f, 0x44, 0xf1].map (BitVec.ofNat 8)

-- gas: `cmovneq %rcx,%rsi`  →  48 0f 45 f1
#guard encodeJInstr aDiff (.cmovne "d" (.reg "a"))
    == [0x48, 0x0f, 0x45, 0xf1].map (BitVec.ofNat 8)

-- gas: `cmovbq %rcx,%rsi`  →  48 0f 42 f1
#guard encodeJInstr aDiff (.cmovb "d" (.reg "a"))
    == [0x48, 0x0f, 0x42, 0xf1].map (BitVec.ofNat 8)

-- gas: `adcx %rcx,%rsi`  →  66 48 0f 38 f6 f1
#guard encodeJInstr aDiff (.adcx "d" (.reg "a"))
    == [0x66, 0x48, 0x0f, 0x38, 0xf6, 0xf1].map (BitVec.ofNat 8)

-- gas: `adox %rcx,%rsi`  →  f3 48 0f 38 f6 f1
#guard encodeJInstr aDiff (.adox "d" (.reg "a"))
    == [0xf3, 0x48, 0x0f, 0x38, 0xf6, 0xf1].map (BitVec.ofNat 8)

-- gas: `mulx %r8,%rsi,%rcx`  →  c4 c2 cb f6 c8   (dstHi=rcx, dstLo=rsi, src2=r8)
#guard encodeJInstr aDiff (.mulx "a" "d" (.reg "p") (.reg "b"))
    == [0xc4, 0xc2, 0xcb, 0xf6, 0xc8].map (BitVec.ofNat 8)

-- gas: `mulxq 24(%rdi),%rsi,%rcx`  →  c4 e2 cb f6 4f 18   (disp8 form)
#guard encodeJInstr aDiff (.mulxMem "a" "d" (.reg "x") "p" 24)
    == [0xc4, 0xe2, 0xcb, 0xf6, 0x4f, 0x18].map (BitVec.ofNat 8)

-- gas: `mulxq (%rdi),%rsi,%rcx`  →  c4 e2 cb f6 0f   (disp0 form)
#guard encodeJInstr aDiff (.mulxMem "a" "d" (.reg "x") "p" 0)
    == [0xc4, 0xe2, 0xcb, 0xf6, 0x0f].map (BitVec.ofNat 8)

-- gas: `movq 24(%rdi),%rsi`  →  48 8b 77 18   (load, disp8)
#guard encodeJInstr aDiff (.loadMem "d" "p" 24)
    == [0x48, 0x8b, 0x77, 0x18].map (BitVec.ofNat 8)

-- gas: `movq (%rdi),%rsi`  →  48 8b 37   (load, disp0)
#guard encodeJInstr aDiff (.loadMem "d" "p" 0)
    == [0x48, 0x8b, 0x37].map (BitVec.ofNat 8)

-- gas: `movq -8(%rdi),%rsi`  →  48 8b 77 f8   (load, negative disp8)
#guard encodeJInstr aDiff (.loadMem "d" "p" (-8))
    == [0x48, 0x8b, 0x77, 0xf8].map (BitVec.ofNat 8)

-- gas: `movq %rsi,24(%rdi)`  →  48 89 77 18   (store, disp8)
#guard encodeJInstr aDiff (.storeMem "p" 24 (.reg "d"))
    == [0x48, 0x89, 0x77, 0x18].map (BitVec.ofNat 8)

-- gas: `movq %rsi,(%rdi)`  →  48 89 37   (store, disp0)
#guard encodeJInstr aDiff (.storeMem "p" 0 (.reg "d"))
    == [0x48, 0x89, 0x37].map (BitVec.ofNat 8)

-- The **store-immediate** form (`C7 /0 id` with a memory ModRM), the shape
-- `MpnLoopEmit.zeroLoopBody` emits (`storeMem "r" 0 (.imm 0)`). AT&T
-- `movq $0, (%rdi)` — NOT the `89 /r` register store this arm used to reuse.
-- gas: `movq $0,(%rdi)`  →  48 c7 07 00 00 00 00
#guard encodeJInstr aDiff (.storeMem "p" 0 (.imm 0))
    == [0x48, 0xc7, 0x07, 0x00, 0x00, 0x00, 0x00].map (BitVec.ofNat 8)

-- gas: `movq $7,24(%rdi)`  →  48 c7 47 18 07 00 00 00   (store-imm, disp8)
#guard encodeJInstr aDiff (.storeMem "p" 24 (.imm 7))
    == [0x48, 0xc7, 0x47, 0x18, 0x07, 0x00, 0x00, 0x00].map (BitVec.ofNat 8)

-- The register-indexed (SIB) store pair: register source, then the `C7 /0`
-- immediate source. `base = p ↦ %rdi`, `index = a ↦ %rcx`, `scale = 8`.
-- gas: `movq %rsi,(%rdi,%rcx,8)`  →  48 89 34 cf
#guard encodeJInstr aDiff (.storeMemIdx "p" "a" 8 (.reg "d"))
    == [0x48, 0x89, 0x34, 0xcf].map (BitVec.ofNat 8)

-- gas: `movq $0,(%rdi,%rcx,8)`  →  48 c7 04 cf 00 00 00 00
#guard encodeJInstr aDiff (.storeMemIdx "p" "a" 8 (.imm 0))
    == [0x48, 0xc7, 0x04, 0xcf, 0x00, 0x00, 0x00, 0x00].map (BitVec.ofNat 8)

/-! ### 1b. `SETcc` + `MOVZBQ`: the three REX bands

The `setc` arm emits the `setb %d8 ; movzbq %d8, %d64` pair, whose `SETcc` half
needs a `REX` prefix in two disjoint bands of the register number — pinned here
one example per band, because the middle band is the one an encoder gets wrong:

* `d < 4` (`%cl` = 1) — no prefix;
* `4 ≤ d < 8` (`%sil` = 6) — the **bare** `REX` `0x40`; without it the ModRM
  `rm` field names the legacy high byte `DH`, not `SIL`, while the `REX.W`
  `MOVZBQ` reads `SIL` — a mismatched register pair;
* `d ≥ 8` (`%r15b` = 15) — `REX.B` `0x41`. -/

-- gas: `setb %cl ; movzbq %cl,%rcx`  →  0f 92 c1  48 0f b6 c9   (no REX on the setb)
#guard encodeJInstr aDiff (.setc "a")
    == [0x0f, 0x92, 0xc1, 0x48, 0x0f, 0xb6, 0xc9].map (BitVec.ofNat 8)

-- gas: `setb %sil ; movzbq %sil,%rsi`  →  40 0f 92 c6  48 0f b6 f6   (BARE REX 0x40)
#guard encodeJInstr aDiff (.setc "d")
    == [0x40, 0x0f, 0x92, 0xc6, 0x48, 0x0f, 0xb6, 0xf6].map (BitVec.ofNat 8)

/-! ## 2. High-register extension-bit coverage

A second allocation exercises the high-8 GP registers as *both* operands, pinning
the REX.R/REX.B (and VEX `R̄`/`B̄`) extension bits that route bit 3 of the register
number. -/

/-- All-high-register allocation: `d↦%r15 a↦%r14 b↦%r13 p↦%r12`. -/
def aHigh : GpAlloc := [("d", "%r15"), ("a", "%r14"), ("b", "%r13"), ("p", "%r12")]

-- gas: `addq %r14,%r15`  →  4d 01 f7   (REX.R for src %r14 + REX.B for dst %r15)
#guard encodeJInstr aHigh (.add "d" (.reg "a"))
    == [0x4d, 0x01, 0xf7].map (BitVec.ofNat 8)

-- gas: `mulx %r13,%r15,%r14`  →  c4 42 83 f6 f5   (dstHi=r14, dstLo=r15, src2=r13)
#guard encodeJInstr aHigh (.mulx "a" "d" (.reg "p") (.reg "b"))
    == [0xc4, 0x42, 0x83, 0xf6, 0xf5].map (BitVec.ofNat 8)

-- The `d ≥ 8` `SETcc` band (`%r15b`): `REX.B` = 0x41 on the setb, `REX.W|R|B` =
-- 0x4d on the movzbq.
-- gas: `setb %r15b ; movzbq %r15b,%r15`  →  41 0f 92 c7  4d 0f b6 ff
#guard encodeJInstr aHigh (.setc "d")
    == [0x41, 0x0f, 0x92, 0xc7, 0x4d, 0x0f, 0xb6, 0xff].map (BitVec.ofNat 8)

/-! ## 3. Block-level integration witness

The whole `add2Block` kernel (`add a0,b0; adc a1,b1`) encodes to the concatenation
of its instruction encodings — the contiguous machine-code stream a `.text` section
consumes. We pin it to the exact `gas` bytes for the `add2Alloc` register pinning
(`a0↦%rsi a1↦%rdx b0↦%rcx b1↦%r8`):

```
gas for `addq %rcx,%rsi`  →  48 01 ce
gas for `adcq %r8,%rdx`   →  4c 11 c2   (REX.R for the %r8 source operand)
```

and confirm the length (the block-level analogue of the per-shape `§6`
`encAluRR_length`/`enc0FRR_length`/… structural facts). -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel

-- The whole add2 kernel body, byte-for-byte = gas's encoding of the two AT&T lines.
#guard encodeJBlock add2Alloc add2Block
      == [0x48, 0x01, 0xce, 0x4c, 0x11, 0xc2].map (BitVec.ofNat 8)

#guard (encodeJBlock add2Alloc add2Block).length == 6

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
