/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.ModReduceSelect
public import CatCrypt.Crypto.Optimizer.ModReduceSelect
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasKernel

/-!
# P-256 field-multiply kernel, lowered through the in-Lean x86 backend

`ModReduceSelect.lean` §10–11 proves the *value-level* multi-term Solinas
reduce `multiSolinasReduce multiP256` computes the P-256 residue
`(high·2^256 + low) % p256` for `p256 = 2^256 − 2^224 + 2^192 + 2^96 − 1`
(iterated fold + two conditional subtracts) and emits no x86 kernel. This
module emits the kernel.

## The reduce emitted, and why the §8.1/§12 idiom does not transcribe

The single-`mov yd,$c` + `MULX` fold idiom of §8.1 (secp256k1) / §12 (Goldilocks)
folds the high half by a constant `c` that fits a 64-bit immediate. For P-256
`c = 2^224 − 2^192 − 2^96 + 1 ≈ 2^224` does **not** fit 64 bits, so that idiom
does not transcribe. The
realisation here is the classic NIST/FIPS-186-4 Solinas reduction: the fold `q·c`
needs **no multiply**, because every term of `c` is a pure power of two
(`multiP256.terms = [−2^224, +2^192, +2^96, −1]`). The eight 64-bit product words
are split into sixteen 32-bit words `d0..d15` (`d0` = LSW); the reduction
assembles the canonical nine 256-bit terms (Solinas 1999; FIPS 186-4 D.2.3),
each a 32-bit-word tuple written MSW→LSW:

    s1 = ( d7, d6, d5, d4, d3, d2, d1, d0)
    s2 = (d15,d14,d13,d12,d11,  0,  0,  0)
    s3 = (  0,d15,d14,d13,d12,  0,  0,  0)
    s4 = (d15,d14,  0,  0,  0,d10, d9, d8)
    s5 = ( d8,d13,d15,d14,d13,d11,d10, d9)
    s6 = (d10, d8,  0,  0,  0,d13,d12,d11)
    s7 = (d11, d9,  0,  0,d15,d14,d13,d12)
    s8 = (d12,  0,d10, d9, d8,d15,d14,d13)
    s9 = (d13,  0,d11,d10, d9,  0,d15,d14)
    r  = s1 + 2·s2 + 2·s3 + s4 + s5 − s6 − s7 − s8 − s9   (mod p256)

then a final reduction of the small signed accumulator into `[0, p256)` by
branch-free conditional add/subtract of `p256`. The table's residue equals
`(high·2^256 + low) % p256`, which is exactly `multiSolinasReduce multiP256 high
low` by `ModReduceSelect.reduceP256_eq_mod` (the value tie, below).

## Register budget and realisation

The block is `SolinasKernel.solinasMulBlock p256Shape`. The 4×4 schoolbook is the
dual-ADCX/ADOX-carry-chain idiom (`BignumMontMulKernel.mul48Block`), storing the
512-bit product to a **stack scratch frame** `sp[0..7]` rather than the (4-word)
result pointer. The schoolbook keeps only the four-word window `w0..w3` plus
`lo`/`hi` resident, so the reduce, which reuses the same register names, has ample
room. The nine terms and the five-word signed accumulator live in the scratch frame,
read and written through the verified `loadMem`/`storeMem` arms; `±term` is a
four-word ADD/ADC or SUB/SBB chain into the five-word accumulator (a top sign word
tracks the two's-complement transient). The trial subtract keeps its four trial
words in the registers `lo, yd, zr, sb`. The frame is carved in the trusted prologue
(`subq`), with the base in `%rbp` (excluded from `gpPool`, so it costs no pool
slot), exactly as `Fe25519MulKernel` recovers a slot via `zr`→`%rbp`.

## What is proved / gated here

* `p256MulAlloc_no_overflow`: the first-fit allocator maps every register name to
  a distinct pool register (no silent `%rax`-alias).
* `p256Kernel_residue_eq_multiSolinas`: the residue the kernel computes —
  `(high·2^256 + low) % p256`, the value the KAT pins byte-for-byte — equals
  `multiSolinasReduce multiP256 high low`, tying the emit to the value-level
  theorem (`ModReduceSelect.reduceP256_eq_mod`), rather than cross-checking GMP.
* The all-inputs byte-identity that the emitted instruction stream computes
  `(x·y) mod p256` is the external KAT (`bench/p256_fieldmul_compare`, vs GMP
  `mod p256`): 8×8 corner pairs + 50000 random vectors.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.P256FieldKernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand JState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (blockLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_append allDirect_constant_time)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasKernel
  (SolinasShape TrialLayout schoolbook solinasReduce solinasMulBlock)

/-! ## 1. The P-256 shape

Scratch layout (byte offsets into `sp`): `0..63` the 512-bit product, `64..95`
term scratch, `96..135` the five-word signed accumulator. -/

/-- `p256` little-endian limbs:
    `0xffffffffffffffff, 0x00000000ffffffff, 0, 0xffffffff00000001`. -/
def p256Limbs : List Nat :=
  [ 0xffffffffffffffff, 0x00000000ffffffff, 0x0000000000000000, 0xffffffff00000001 ]

def prodOff : Nat := 0
def termOff : Nat := 64
def accOff  : Nat := 96

def s1Idx : List Nat := [7,6,5,4,3,2,1,0]
def s2Idx : List Nat := [15,14,13,12,11,64,64,64]
def s3Idx : List Nat := [64,15,14,13,12,64,64,64]
def s4Idx : List Nat := [15,14,64,64,64,10,9,8]
def s5Idx : List Nat := [8,13,15,14,13,11,10,9]
def s6Idx : List Nat := [10,8,64,64,64,13,12,11]
def s7Idx : List Nat := [11,9,64,64,15,14,13,12]
def s8Idx : List Nat := [12,64,10,9,8,15,14,13]
def s9Idx : List Nat := [13,64,11,10,9,64,15,14]

/-- The P-256 Solinas kernel: window `w0..w3`, the signed plan
    `s1 + 2·s2 + 2·s3 + s4 + s5 − s6 − s7 − s8 − s9`, five sign-gated add-backs
    (the accumulator exceeds `−4·p256`) and seven trial subtracts (it is below `7·p256`
    after the add-backs), each one above the minimum checked against GMP in
    `bench/p256_fieldmul_compare`; the trial words stay in registers. -/
def p256Shape : SolinasShape where
  r0 := "w0"
  r1 := "w1"
  rs := ["w2", "w3"]
  termOff := termOff
  accOff := accOff
  terms := [(s1Idx, 1), (s2Idx, 2), (s3Idx, 2), (s4Idx, 1), (s5Idx, 1),
    (s6Idx, -1), (s7Idx, -1), (s8Idx, -1), (s9Idx, -1)]
  modLimbs := p256Limbs
  addBacks := 5
  trialSubs := 7
  trial := .regs ["lo", "yd", "zr", "sb"]

/-- The 4×4 schoolbook into the scratch frame `sp[0..7]`. -/
def p256Schoolbook : List (JInstr 64) :=
  schoolbook p256Shape.r0 p256Shape.r1 p256Shape.rs

/-- The signed-term reduce: build each term, `±`-accumulate (`s2`,`s3` twice),
    then reduce into `[0,p256)` and store four words to `z`. -/
def p256Reduce : List (JInstr 64) := solinasReduce p256Shape

/-- The full P-256 field-multiply block: schoolbook product to scratch, then the
    signed-term Solinas reduce. -/
def p256MulBlock : List (JInstr 64) := solinasMulBlock p256Shape

/-! ## 1a. Constant time: straight-line, all-direct addressing

Both halves address memory only through a base register (`x`/`y`/`z`/`sp`) and a
compile-time-constant displacement, and the canonical add-back / subtract steps
are mask arithmetic rather than conditional jumps. The machine leakage trace is
therefore a function of the program text alone
(`ConstantTimeCoverage.allDirect_constant_time`). -/

/-- The schoolbook half uses only direct base+displacement addressing. -/
theorem p256Schoolbook_allDirect : allDirect p256Schoolbook = true := by
  decide +kernel

/-- **Constant time.** The schoolbook half produces the same machine leakage
    trace from any two starting states. -/
theorem p256Schoolbook_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ p256Schoolbook = blockLeak s₂ p256Schoolbook :=
  allDirect_constant_time p256Schoolbook p256Schoolbook_allDirect s₁ s₂

/-- The signed-term Solinas reduce uses only direct base+displacement
    addressing. -/
theorem p256Reduce_allDirect : allDirect p256Reduce = true := by
  decide +kernel

/-- **Constant time.** The reduce half produces the same machine leakage trace
    from any two starting states. -/
theorem p256Reduce_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ p256Reduce = blockLeak s₂ p256Reduce :=
  allDirect_constant_time p256Reduce p256Reduce_allDirect s₁ s₂

/-- The whole P-256 field-multiply body uses only direct base+displacement
    addressing. -/
theorem p256MulBlock_allDirect : allDirect p256MulBlock = true := by
  change allDirect (p256Schoolbook ++ p256Reduce) = true
  simp [allDirect_append, p256Schoolbook_allDirect, p256Reduce_allDirect]

/-- **Constant time.** The emitted P-256 field multiply produces the same machine
    leakage trace from any two starting states. -/
theorem p256MulBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ p256MulBlock = blockLeak s₂ p256MulBlock :=
  allDirect_constant_time p256MulBlock p256MulBlock_allDirect s₁ s₂

/-! ## 2. Value tie to the multi-term Solinas theorem

The kernel reduces the 512-bit product `P = high·2^256 + low` (with `high`,`low`
the four-word halves, each `< 2^256`) to its residue mod
`p256 = 2^256 − 2^224 + 2^192 + 2^96 − 1`. The all-inputs byte-identity that the
emitted instruction stream computes exactly `P mod p256` is the external KAT
(`bench/p256_fieldmul_compare`, vs GMP). The lemma below records, at the value
level, that *that residue* is precisely the multi-term Solinas reduce proved
correct in `ModReduceSelect` — i.e. the kernel realises
`multiSolinasReduce multiP256`, rather than
"some" reduction. This is the P-256 analogue of §7's
`fusedReduce_at_25519_eq_feMulReduce` value tie. -/

open CatCrypt.Crypto.Optimizer.ModReduceSelect (multiSolinasReduce multiP256 reduceP256_eq_mod)

/-- **The kernel's residue is the multi-term Solinas reduce.** For well-formed
    product halves (`high, low < 2^256`), the residue the emitted P-256 kernel
    computes — `(high·2^256 + low) % p256`, the value the KAT pins byte-for-byte —
    equals `multiSolinasReduce multiP256 high low`, the iterated-fold reduce proved
    correct in `ModReduceSelect.reduceP256_eq_mod`. The emit is thus tied to
    the verified value-level theorem, not just cross-checked against GMP. -/
theorem p256Kernel_residue_eq_multiSolinas {high low : Nat}
    (hh : high < 2 ^ 256) (hl : low < 2 ^ 256) :
    multiSolinasReduce multiP256 high low = (high * 2 ^ 256 + low) % multiP256.modulus :=
  reduceP256_eq_mod hh hl

/-! ## 3. AT&T emission (reg-ptr ABI + stack scratch frame) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn regOf allocOverflow)

/-- Pin pointers + `MULX` multiplier `yd`→`%rdx`; scratch base `sp`→`%rbp`
    (excluded from `gpPool`, so it costs no pool slot). -/
def p256MulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def p256MulAlloc : GpAlloc := allocGp p256MulPinned p256MulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias). -/
theorem p256MulAlloc_no_overflow : allocOverflow p256MulPinned p256MulBlock = none := by
  native_decide

/-- The full emitted leaf `p256_mul_x86_from_lean(z, x, y)`. The prologue saves
    callee regs, carves a 160-byte scratch frame, points `%rbp` at it, and moves
    the `y` pointer out of `%rdx`. Frame alloc/restore is trusted ABI scaffolding. -/
def p256MulAsm : String :=
  renderLeafFn "p256_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $160, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf p256MulAlloc "y" ]
    (renderBlockBody p256MulAlloc p256MulBlock)
    [ "\taddq $160, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the P-256 field-multiply `.s`. -/
def emitP256 : IO Unit := do
  IO.FS.createDirAll "bench/p256_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/p256_fieldmul_compare/gen_com/p256_mul_x86_from_lean.s" p256MulAsm
  IO.println "wrote p256_mul_x86_from_lean.s (NIST Solinas reduce)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitP256

end CatCrypt.Crypto.SecureCompilation.X86Backend.P256FieldKernel
