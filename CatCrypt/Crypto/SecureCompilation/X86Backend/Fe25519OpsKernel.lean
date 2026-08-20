/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# Curve25519 field-OP kernels `feAdd`/`feSub`/`feMul121666`/`feSqr`, lowered through the in-Lean x86 backend (#408)

`Fe25519MulKernel.lean` emits the Curve25519 **field-multiply** (4×4 schoolbook +
`2^255-19` Solinas reduce) through the owned x86 backend (MULX + dual ADCX/ADOX,
no jasminc), at s2n parity. The X25519 Montgomery ladder and the Ed25519
fixed-base scalar-multiply call the field-multiply alongside four more field
operations: addition, subtraction, multiply-by-`a24=121666`, and squaring. This
module emits those four through the SAME owned backend, so a real owned-backend
X25519 ladder is assembled entirely from owned-backend leaves rather than from a
fiat-crypto transliteration.

## The routines (all over `p25519 = 2^255 - 19`, 4-limb radix-2^64 saturated)

* `feAddBlock`  : `z := (x + y) mod p`, `x`,`y` assumed reduced (`< p`).
* `feSubBlock`  : `z := (x − y) mod p`, `x`,`y` assumed reduced.
* `feMul121666Block` : `z := (121666 · x) mod p` (the X25519 `a24` constant).
* `feSqrBlock`  : `z := (x²) mod p`.

The references are s2n-bignum's HOL-Light–verified
`x86_att/curve25519/bignum_{add,sub,cmul,sqr}_p25519.S`. `feAdd`/`feSub` follow
those line-for-line up to expressing s2n's `btr`/`cmovc` canonical select with
the supported `shr`/`neg`/`and`/`xor`/`sbb` sign-mask idiom (constant-time, no
secret-dependent branch). `feMul121666` is the `bignum_cmul_p25519` algorithm
with the multiplier fixed to `121666` and the `mulq`-by-19 step expressed with
`imul` (the `19·q` product is `< 2^24`, so its high word is `0` and a single low
multiply suffices). `feSqr` reuses the `feMulBlock` 4×4 schoolbook with the
multiplier read from `x[j]` (square = self-multiply) followed by the **same**
s2n fused-quotient-estimate reduce as `feMulBlock`.

## What is proved here

For each block `feXBlock`:

* `feXBlock_lowering_correct`: lowering to `Com (x86Dialect 64)` and denoting on
  the init state equals `runBlock` on the source block — the owned backend's
  straight-line lowering is denotation-preserving across the
  `loadMem`/`mulx(Mem)`/`add`/`adc`/`sub`/`sbb`/`adcx`/`adox`/`imul`/`shl`/`shr`/
  `neg`/`and`/`or`/`xor`/`cmovb`/`storeMem` mix (reusing `lowerBlock_denote_closed`).
* `feXAsmBody_length` / `feXAsm_shape`: the emitted AT&T body is one line per
  `JInstr` and contains the expected mnemonics.

The all-inputs value identity (`z = (x ⊙ y) mod p25519`) is the runtime KAT in
`bench/x25519_fieldops_compare/` against s2n-bignum's own
`bignum_{add,sub,cmul,sqr}_p25519` AND GMP (`mpz` (op) mod `p`), over corner +
random inputs — the standard gate for these word kernels (mirrors `feMulBlock`'s
KAT discipline; per REV-12 the per-input `native_decide` value pin is omitted).

## Trust story

Identical to `Fe25519MulKernel` / `BignumMontMulKernel` / `JasminModel` /
`X86Dialect` / `AsmPrinter`: the verified artifact is
`Com (x86Dialect 64) → runBlock → evalInstr`, the faithful transcription of
Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is the syntactic trust
boundary, and the System-V leaf prologue/epilogue is trusted ABI scaffolding
outside the verified body. No `sorry`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (blockLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_constant_time)

/-! ## 0. Initial machine states (reg-ptr ABI)

`feAdd`/`feSub` read two 4-limb buffers `x`,`y`; `feMul121666`/`feSqr` read one
buffer `x`. The input words live at `[x + 8·i]` / `[y + 8·i]`. -/

/-- Two-input init state: `x` buffer holds `x0..x3`, `y` buffer holds `y0..y3`. -/
def initState2 (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "x" then
        (if off = 0 then x0 else if off = 8 then x1
         else if off = 16 then x2 else if off = 24 then x3 else 0)
      else if base = "y" then
        (if off = 0 then y0 else if off = 8 then y1
         else if off = 16 then y2 else if off = 24 then y3 else 0)
      else 0 }

/-- Single-input init state: `x` buffer holds `x0..x3`. -/
def initState1 (x0 x1 x2 x3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "x" then
        (if off = 0 then x0 else if off = 8 then x1
         else if off = 16 then x2 else if off = 24 then x3 else 0)
      else 0 }

/-! ## 1. feAdd: `z := (x + y) mod p`, branchless canonical select

Mirrors s2n `bignum_add_p25519`: form `d = x + y`, `c = d + 19`; if `bit255(c)`
then the result is `c` with bit 255 cleared, else `d`. s2n's `btr`/`cmovc` select
is realised branchlessly: `m := 0 − bit63(c3)` (all-ones iff selecting `c`), then
`out := d XOR (m & (c XOR d))`. -/
def feAddBlock : List (JInstr 64) :=
  [ .loadMem "d0" "x" 0
  , .loadMem "lo" "y" 0,  .add "d0" (.reg "lo")
  , .loadMem "d1" "x" 8
  , .loadMem "lo" "y" 8,  .adc "d1" (.reg "lo")
  , .loadMem "d2" "x" 16
  , .loadMem "lo" "y" 16, .adc "d2" (.reg "lo")
  , .loadMem "d3" "x" 24
  , .loadMem "lo" "y" 24, .adc "d3" (.reg "lo")
  , .mov "c0" (.reg "d0"), .add "c0" (.imm 19)
  , .mov "c1" (.reg "d1"), .adc "c1" (.imm 0)
  , .mov "c2" (.reg "d2"), .adc "c2" (.imm 0)
  , .mov "c3" (.reg "d3"), .adc "c3" (.imm 0)
  , .mov "m" (.reg "c3"), .shr "m" (.imm 63)
  , .neg "m"
  , .mov "lo" (.imm 0x7fffffffffffffff), .and_ "c3" (.reg "lo")
  , .mov "lo" (.reg "c0"), .xor_ "lo" (.reg "d0"), .and_ "lo" (.reg "m"), .xor_ "d0" (.reg "lo")
  , .mov "lo" (.reg "c1"), .xor_ "lo" (.reg "d1"), .and_ "lo" (.reg "m"), .xor_ "d1" (.reg "lo")
  , .mov "lo" (.reg "c2"), .xor_ "lo" (.reg "d2"), .and_ "lo" (.reg "m"), .xor_ "d2" (.reg "lo")
  , .mov "lo" (.reg "c3"), .xor_ "lo" (.reg "d3"), .and_ "lo" (.reg "m"), .xor_ "d3" (.reg "lo")
  , .storeMem "z" 0 (.reg "d0")
  , .storeMem "z" 8 (.reg "d1")
  , .storeMem "z" 16 (.reg "d2")
  , .storeMem "z" 24 (.reg "d3") ]

theorem feAddBlock_length : feAddBlock.length = 45 := by native_decide

/-- **Lowering correctness on the add block.** -/
theorem feAddBlock_lowering_correct (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (lowerBlock (Γ := []) feAddBlock).denote
        (.cons (initState2 x0 x1 x2 x3 y0 y1 y2 y3) .nil)
      = runBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3) feAddBlock :=
  lowerBlock_denote_closed feAddBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3)

/-! ## 2. feSub: `z := (x − y) mod p`, branchless

Mirrors s2n `bignum_sub_p25519`: `d = x − y` (mod `2^256`, `CF` = borrow);
`c = (0 − CF) & 19` (the `19` to add back iff `x < y`); subtract `c` propagating
borrow; clear bit 255. -/
def feSubBlock : List (JInstr 64) :=
  [ .loadMem "d0" "x" 0
  , .loadMem "lo" "y" 0,  .sub "d0" (.reg "lo")
  , .loadMem "d1" "x" 8
  , .loadMem "lo" "y" 8,  .sbb "d1" (.reg "lo")
  , .loadMem "d2" "x" 16
  , .loadMem "lo" "y" 16, .sbb "d2" (.reg "lo")
  , .loadMem "d3" "x" 24
  , .loadMem "lo" "y" 24, .sbb "d3" (.reg "lo")
  , .mov "c" (.imm 0), .sbb "c" (.imm 0)
  , .and_ "c" (.imm 19)
  , .mov "zr" (.imm 0)
  , .sub "d0" (.reg "c")
  , .sbb "d1" (.reg "zr")
  , .sbb "d2" (.reg "zr")
  , .sbb "d3" (.reg "zr")
  , .mov "lo" (.imm 0x7fffffffffffffff), .and_ "d3" (.reg "lo")
  , .storeMem "z" 0 (.reg "d0")
  , .storeMem "z" 8 (.reg "d1")
  , .storeMem "z" 16 (.reg "d2")
  , .storeMem "z" 24 (.reg "d3") ]

theorem feSubBlock_length : feSubBlock.length = 26 := by native_decide

/-- **Lowering correctness on the sub block.** -/
theorem feSubBlock_lowering_correct (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (lowerBlock (Γ := []) feSubBlock).denote
        (.cons (initState2 x0 x1 x2 x3 y0 y1 y2 y3) .nil)
      = runBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3) feSubBlock :=
  lowerBlock_denote_closed feSubBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3)

/-! ## 3. feMul121666: `z := (121666 · x) mod p`

Mirrors s2n `bignum_cmul_p25519` with the multiplier fixed to `121666`: the
single-word multiply produces `[a;d3;d2;d1;d0] = c·x = 2^255·h + l`; estimate
`q = 2·a + bit63(d3) + 1`, set bit 63 of `d3` (s2n's `bts`), inject `19·q` (a
single `imul` since `19·q < 2^24`), add, then the `cmovb`-gated conditional
subtract and the bit-255 clear. -/
def feMul121666Block : List (JInstr 64) :=
  [ .mov "yd" (.imm 121666)
  , .mulxMem "d1" "d0" (.reg "yd") "x" 0
  , .mulxMem "d2" "a"  (.reg "yd") "x" 8
  , .add "d1" (.reg "a")
  , .mulxMem "d3" "a"  (.reg "yd") "x" 16
  , .adc "d2" (.reg "a")
  , .mulxMem "a"  "lo" (.reg "yd") "x" 24
  , .adc "d3" (.reg "lo")
  , .mov "zr" (.imm 0)
  , .adc "a" (.reg "zr")
  , .mov "h" (.reg "d3"), .shr "h" (.imm 63)
  , .shl "a" (.imm 1)
  , .add "a" (.reg "h")
  , .add "a" (.imm 1)
  , .imul "a" (.imm 19)
  , .mov "lo" (.imm 0x8000000000000000), .or_ "d3" (.reg "lo")
  , .add "d0" (.reg "a")
  , .adc "d1" (.reg "zr")
  , .adc "d2" (.reg "zr")
  , .adc "d3" (.reg "zr")
  , .mov "c" (.imm 19)
  , .cmovb "c" (.reg "zr")
  , .sub "d0" (.reg "c")
  , .sbb "d1" (.reg "zr")
  , .sbb "d2" (.reg "zr")
  , .sbb "d3" (.reg "zr")
  , .mov "lo" (.imm 0x7fffffffffffffff), .and_ "d3" (.reg "lo")
  , .storeMem "z" 0 (.reg "d0")
  , .storeMem "z" 8 (.reg "d1")
  , .storeMem "z" 16 (.reg "d2")
  , .storeMem "z" 24 (.reg "d3") ]

theorem feMul121666Block_length : feMul121666Block.length = 34 := by native_decide

/-- **Lowering correctness on the mul-by-121666 block.** -/
theorem feMul121666Block_lowering_correct (x0 x1 x2 x3 : BitVec 64) :
    (lowerBlock (Γ := []) feMul121666Block).denote
        (.cons (initState1 x0 x1 x2 x3) .nil)
      = runBlock (initState1 x0 x1 x2 x3) feMul121666Block :=
  lowerBlock_denote_closed feMul121666Block (initState1 x0 x1 x2 x3)

/-! ## 4. feSqr: `z := (x²) mod p`

The `feMulBlock` 4×4 schoolbook with the multiplier read from `x[j]`
(square = self-multiply), then the same s2n fused-quotient-estimate `2^255-19`
reduce. A few more multiplies than s2n's heterogeneous-doubling square, but the
same proven reduce — preferred here for certain correctness; a doubling-square
specialisation is named-remaining perf work. -/
def feSqrBlock : List (JInstr 64) :=
  [ .mov "zr" (.imm 0)
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "x" 0
  , .mulxMem "t1" "t0" (.reg "yd") "x" 0
  , .mulxMem "t2" "lo" (.reg "yd") "x" 8
  , .adcx "t1" (.reg "lo")
  , .mulxMem "t3" "lo" (.reg "yd") "x" 16
  , .adcx "t2" (.reg "lo")
  , .mulxMem "t4" "lo" (.reg "yd") "x" 24
  , .adcx "t3" (.reg "lo")
  , .adcx "t4" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "x" 8
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "t5" "lo" (.reg "yd") "x" 24
  , .adcx "t4" (.reg "lo")
  , .adox "t5" (.reg "zr")
  , .adcx "t5" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "x" 16
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "t6" "lo" (.reg "yd") "x" 24
  , .adcx "t5" (.reg "lo")
  , .adox "t6" (.reg "zr")
  , .adcx "t6" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "x" 24
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16
  , .adcx "t5" (.reg "lo"), .adox "t6" (.reg "hi")
  , .mulxMem "t7" "lo" (.reg "yd") "x" 24
  , .adcx "t6" (.reg "lo")
  , .adox "t7" (.reg "zr")
  , .adcx "t7" (.reg "zr")
    -- shared s2n fused-quotient-estimate 2^255-19 reduce (identical to feMulBlock)
  , .mov "yd" (.imm 38)
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .add "lo" (.reg "t3")
  , .adc "hi" (.reg "zr")
  , .mov "y" (.reg "lo")
  , .shr "y" (.imm 63)
  , .shl "hi" (.imm 1)
  , .add "hi" (.reg "y")
  , .add "hi" (.imm 1)
  , .mov "y" (.reg "hi")
  , .imul "hi" (.imm 19)
  , .xor_ "zr" (.reg "zr")
  , .adox "t0" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t4")
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t5")
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t6")
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .adc "t3" (.reg "lo")
  , .shl "y" (.imm 63)
  , .mov "lo" (.reg "t3")
  , .sub "lo" (.reg "y")
  , .shr "lo" (.imm 63)
  , .imul "lo" (.imm 19)
  , .sub "t0" (.reg "lo")
  , .sbb "t1" (.reg "zr")
  , .sbb "t2" (.reg "zr")
  , .sbb "t3" (.reg "zr")
  , .mov "hi" (.imm 0x7fffffffffffffff)
  , .and_ "t3" (.reg "hi")
  , .storeMem "z" 0 (.reg "t0")
  , .storeMem "z" 8 (.reg "t1")
  , .storeMem "z" 16 (.reg "t2")
  , .storeMem "z" 24 (.reg "t3") ]

theorem feSqrBlock_length : feSqrBlock.length = 95 := by native_decide

/-- **Lowering correctness on the square block.** -/
theorem feSqrBlock_lowering_correct (x0 x1 x2 x3 : BitVec 64) :
    (lowerBlock (Γ := []) feSqrBlock).denote
        (.cons (initState1 x0 x1 x2 x3) .nil)
      = runBlock (initState1 x0 x1 x2 x3) feSqrBlock :=
  lowerBlock_denote_closed feSqrBlock (initState1 x0 x1 x2 x3)

/-! ## 4a. Constant time: straight-line, all-direct addressing

Each of the four field-op bodies addresses memory only through a base register
and a compile-time-constant displacement, so its machine leakage trace is a
function of the program text alone
(`ConstantTimeCoverage.allDirect_constant_time`). The branchless canonical
selects in `feAdd`/`feSub` are mask arithmetic, not conditional jumps. -/

/-- The `feAdd` body uses only direct base+displacement addressing. -/
theorem feAddBlock_allDirect : allDirect feAddBlock = true := by
  decide

/-- **Constant time.** `feAdd` produces the same machine leakage trace from any
    two starting states. -/
theorem feAddBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ feAddBlock = blockLeak s₂ feAddBlock :=
  allDirect_constant_time feAddBlock feAddBlock_allDirect s₁ s₂

/-- The `feSub` body uses only direct base+displacement addressing. -/
theorem feSubBlock_allDirect : allDirect feSubBlock = true := by
  decide

/-- **Constant time.** `feSub` produces the same machine leakage trace from any
    two starting states. -/
theorem feSubBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ feSubBlock = blockLeak s₂ feSubBlock :=
  allDirect_constant_time feSubBlock feSubBlock_allDirect s₁ s₂

/-- The `feMul121666` body uses only direct base+displacement addressing. -/
theorem feMul121666Block_allDirect : allDirect feMul121666Block = true := by
  decide

/-- **Constant time.** `feMul121666` produces the same machine leakage trace from
    any two starting states. -/
theorem feMul121666Block_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ feMul121666Block = blockLeak s₂ feMul121666Block :=
  allDirect_constant_time feMul121666Block feMul121666Block_allDirect s₁ s₂

/-- The `feSqr` body uses only direct base+displacement addressing. -/
theorem feSqrBlock_allDirect : allDirect feSqrBlock = true := by
  decide

/-- **Constant time.** `feSqr` produces the same machine leakage trace from any
    two starting states. -/
theorem feSqrBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ feSqrBlock = blockLeak s₂ feSqrBlock :=
  allDirect_constant_time feSqrBlock feSqrBlock_allDirect s₁ s₂

/-! ## 5. AT&T assembly emission (in-Lean backend, no jasminc)

`feAdd`/`feSub` are two-input (`z`→`%rdi`, `x`→`%rsi`, `y`→`%rdx`, copied out of
`%rdx`). `feMul121666`/`feSqr` use `MULX`, so `yd`→`%rdx` and `zr`→`%rbp` are
pinned (mirroring `feMulBlock`). -/

def feAddPinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("y", "%rdx")]
def feSubPinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("y", "%rdx")]
def feMul121666Pinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("zr", "%rbp")]
def feSqrPinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("zr", "%rbp")]

def feAddAlloc : GpAlloc := allocGp feAddPinned feAddBlock
def feSubAlloc : GpAlloc := allocGp feSubPinned feSubBlock
def feMul121666Alloc : GpAlloc := allocGp feMul121666Pinned feMul121666Block
def feSqrAlloc : GpAlloc := allocGp feSqrPinned feSqrBlock

def feAddAsm : String :=
  renderLeafFn "fe25519_add_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tmovq %rdx, " ++ regOf feAddAlloc "y" ]
    (renderBlockBody feAddAlloc feAddBlock)
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

def feSubAsm : String :=
  renderLeafFn "fe25519_sub_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tmovq %rdx, " ++ regOf feSubAlloc "y" ]
    (renderBlockBody feSubAlloc feSubBlock)
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

def feMul121666Asm : String :=
  renderLeafFn "fe25519_mul121666_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15", "\tpushq %rbp" ]
    (renderBlockBody feMul121666Alloc feMul121666Block)
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

def feSqrAsm : String :=
  renderLeafFn "fe25519_sqr_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15", "\tpushq %rbp" ]
    (renderBlockBody feSqrAlloc feSqrBlock)
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

theorem feAddAsmBody_length : (renderBlockBody feAddAlloc feAddBlock).length = 45 := by native_decide
theorem feSubAsmBody_length : (renderBlockBody feSubAlloc feSubBlock).length = 26 := by native_decide
theorem feMul121666AsmBody_length :
    (renderBlockBody feMul121666Alloc feMul121666Block).length = 34 := by native_decide
theorem feSqrAsmBody_length : (renderBlockBody feSqrAlloc feSqrBlock).length = 95 := by native_decide

/-- No register-allocation overflow for any of the four blocks (every name maps
    to a distinct pool register; no silent `%rax` alias). -/
theorem feOps_alloc_no_overflow :
    allocOverflow feAddPinned feAddBlock = none
      ∧ allocOverflow feSubPinned feSubBlock = none
      ∧ allocOverflow feMul121666Pinned feMul121666Block = none
      ∧ allocOverflow feSqrPinned feSqrBlock = none := by native_decide

/- Shape checks: each emitted body contains the expected mnemonics. -/
#guard (BignumMontMulKernel.hasSub feAddAsm "addq") && (BignumMontMulKernel.hasSub feSubAsm "sbbq") && (BignumMontMulKernel.hasSub feMul121666Asm "$121666") && (BignumMontMulKernel.hasSub feSqrAsm "mulx")

/-- Emit driver: write the in-Lean-backend-emitted `.s` files for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_fieldops_compare/gen_com"
  IO.FS.writeFile "bench/x25519_fieldops_compare/gen_com/fe25519_add_x86_from_lean.s" feAddAsm
  IO.FS.writeFile "bench/x25519_fieldops_compare/gen_com/fe25519_sub_x86_from_lean.s" feSubAsm
  IO.FS.writeFile
    "bench/x25519_fieldops_compare/gen_com/fe25519_mul121666_x86_from_lean.s" feMul121666Asm
  IO.FS.writeFile "bench/x25519_fieldops_compare/gen_com/fe25519_sqr_x86_from_lean.s" feSqrAsm
  IO.println "wrote gen_com/fe25519_{add,sub,mul121666,sqr}_x86_from_lean.s (in-Lean x86 backend)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
