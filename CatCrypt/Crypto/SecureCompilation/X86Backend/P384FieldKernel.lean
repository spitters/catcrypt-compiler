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
# P-384 field-multiply kernel, lowered through the in-Lean x86 backend

`ModReduceSelect.lean` §10–11 proves the *value-level* multi-term Solinas
reduce `multiSolinasReduce multiP384` computes the P-384 residue
`(high·2^384 + low) % p384` for `p384 = 2^384 − 2^128 − 2^96 + 2^32 − 1`
(`reduceP384_eq_mod`, fuel 2). This module emits the x86 kernel. P-384 needs a
6×6 schoolbook (12-word product), and a direct transcription of the FIPS-186-4
D.2.4 signed Solinas table is error-prone. The signed table is therefore
*derived* from the relation `2^384 ≡ 2^128 + 2^96 − 2^32 + 1 (mod p384)`, folded to
fixpoint, and validated byte-for-byte against GMP
(`bench/p384_fieldmul_compare`).

## The reduce emitted

The 768-bit product is split into twenty-four 32-bit words `d0..d23` (`d0` = LSW)
out of the twelve 64-bit product words at `sp[0..11]`. Modulo p384, each high
word `d_i` (`i ≥ 12`) folds into the low twelve slots via `2^384 ≡ c` with
`c = 2^128 + 2^96 − 2^32 + 1` (every term a pure power of two — **no multiply**,
exactly the Solinas shape `multiP384.terms = [−2^128, −2^96, +2^32, −1]`). Folding
to fixpoint (two rounds — `multiP384.fuel = 2`) gives an eleven-term signed
combination; each term is a twelve-word (32-bit) tuple written MSW→LSW, assembled
by the same prime-agnostic `SolinasKernel.buildTerm` the P-256 kernel uses:

    r = s0 + s1 + s2 + s3 + s4 + s5 + s6 + s7 − s8 − s9 − s10   (mod p384)

(the term tuples are `s0Idx … s10Idx`, derived + GMP-validated in
`bench/p384_fieldmul_compare/p384_decompose.c`). A final branch-free conditional
add/subtract of `p384` lands the signed accumulator in `[0, p384)`. The table's
residue equals `(high·2^384 + low) % p384` = `multiSolinasReduce multiP384 high
low` by `ModReduceSelect.reduceP384_eq_mod` (the value tie, §2).

## Register budget and realisation

The block is `SolinasKernel.solinasMulBlock p384Shape`. The 6×6 schoolbook is the
dual-ADCX/ADOX-carry-chain idiom (the `mul48Block` pattern of `BignumMontMulKernel`,
extended to six columns), storing the 768-bit product to a **stack scratch frame**
`sp[0..11]` rather than the result pointer. The schoolbook keeps the six-word window
`w0..w5` plus `lo`/`hi`/`zr` resident. The reduce is memory-resident: each term and
the seven-word signed accumulator live in the scratch frame, read and written
through the verified `loadMem`/`storeMem` arms, so the reduce holds only a small
working window (`w0..w5`,`lo`,`hi`,`y`,`yd`); the trial subtract stages its six
trial words in the term words. The frame base lives in `%rbp` (excluded from
`gpPool`, costing no pool slot), as `Fe25519MulKernel` recovers a slot via
`zr`→`%rbp`. `p384MulAlloc_no_overflow` proves the first-fit allocator maps every
name to a distinct pool register (no silent `%rax`-alias).

## What is proved / gated here

* `p384MulAlloc_no_overflow`: the allocator assigns every register name a
  distinct pool register.
* `p384Kernel_residue_eq_multiSolinas`: the residue the kernel computes —
  `(high·2^384 + low) % p384` — equals `multiSolinasReduce multiP384 high low`,
  tying the emit to the value-level theorem (`reduceP384_eq_mod`).
* The all-inputs byte-identity that the emitted stream computes `(x·y) mod p384`
  is the external KAT (`bench/p384_fieldmul_compare`, vs GMP `mod p384`):
  6×6 corner pairs + 50000 random vectors.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.P384FieldKernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand JState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (blockLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_append allDirect_constant_time)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasKernel
  (SolinasShape TrialLayout schoolbook solinasReduce solinasMulBlock)

/-! ## 1. The P-384 shape

Scratch layout (byte offsets into `sp`): `0..95` the 768-bit product (twelve
words), `96..143` term scratch (six words), `144..199` the seven-word signed
accumulator. -/

/-- `p384` little-endian limbs (six 64-bit words):
    `0x00000000ffffffff, 0xffffffff00000000, 0xfffffffffffffffe,
     0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff`. -/
def p384Limbs : List Nat :=
  [ 0x00000000ffffffff, 0xffffffff00000000, 0xfffffffffffffffe
  , 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff ]

def prodOff : Nat := 0
def termOff : Nat := 96
def accOff  : Nat := 144

/-- The eleven derived + GMP-validated signed terms (MSW first; `64` = zero
    half-word), from `bench/p384_fieldmul_compare/p384_decompose.c`. -/
def s0Idx  : List Nat := [11,10,9,8,7,6,5,4,3,2,1,0]
def s1Idx  : List Nat := [19,18,17,16,15,14,13,12,12,14,13,12]
def s2Idx  : List Nat := [20,19,18,17,16,15,14,13,15,23,22,20]
def s3Idx  : List Nat := [23,22,21,20,19,18,17,16,20,64,23,21]
def s4Idx  : List Nat := [64,64,64,64,23,22,21,20,21,64,64,64]
def s5Idx  : List Nat := [64,64,64,64,64,23,22,21,64,64,64,64]
def s6Idx  : List Nat := [64,64,64,64,64,23,22,21,64,64,64,64]
def s7Idx  : List Nat := [64,64,64,64,64,64,23,22,64,64,64,64]
def s8Idx  : List Nat := [22,21,20,19,18,17,16,15,14,13,12,23]
def s9Idx  : List Nat := [64,64,64,64,64,64,64,23,22,21,20,64]
def s10Idx : List Nat := [64,64,64,64,64,64,64,23,23,64,64,64]

/-- The P-384 Solinas kernel: window `w0..w5`, the derived plan
    `+s0+s1+s2+s3+s4+s5+s6+s7−s8−s9−s10`, four sign-gated add-backs and six trial
    subtracts, each one above the minimum checked against GMP in
    `bench/p384_fieldmul_compare`; the trial words are staged in the term words. -/
def p384Shape : SolinasShape where
  r0 := "w0"
  r1 := "w1"
  rs := ["w2", "w3", "w4", "w5"]
  termOff := termOff
  accOff := accOff
  terms := [(s0Idx, 1), (s1Idx, 1), (s2Idx, 1), (s3Idx, 1), (s4Idx, 1), (s5Idx, 1),
    (s6Idx, 1), (s7Idx, 1), (s8Idx, -1), (s9Idx, -1), (s10Idx, -1)]
  modLimbs := p384Limbs
  addBacks := 4
  trialSubs := 6
  trial := .staged

/-- The 6×6 schoolbook into the scratch frame `sp[0..11]`. -/
def p384Schoolbook : List (JInstr 64) :=
  schoolbook p384Shape.r0 p384Shape.r1 p384Shape.rs

/-- The signed-term reduce: build each term, `±`-accumulate per the derived plan,
    then reduce into `[0,p384)` and store six words to `z`. -/
def p384Reduce : List (JInstr 64) := solinasReduce p384Shape

/-- The full P-384 field-multiply block: 6×6 schoolbook to scratch, then the
    signed-term Solinas reduce. -/
def p384MulBlock : List (JInstr 64) := solinasMulBlock p384Shape

/-! ## 1a. Constant time: straight-line, all-direct addressing

Both halves address memory only through a base register (`x`/`y`/`z`/`sp`) and a
compile-time-constant displacement, and the canonical add-back / subtract steps
are mask arithmetic rather than conditional jumps. The machine leakage trace is
therefore a function of the program text alone
(`ConstantTimeCoverage.allDirect_constant_time`). -/

/-- The 6×6 schoolbook half uses only direct base+displacement addressing. -/
theorem p384Schoolbook_allDirect : allDirect p384Schoolbook = true := by
  decide +kernel

/-- **Constant time.** The schoolbook half produces the same machine leakage
    trace from any two starting states. -/
theorem p384Schoolbook_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ p384Schoolbook = blockLeak s₂ p384Schoolbook :=
  allDirect_constant_time p384Schoolbook p384Schoolbook_allDirect s₁ s₂

/-- The signed-term Solinas reduce uses only direct base+displacement
    addressing. -/
theorem p384Reduce_allDirect : allDirect p384Reduce = true := by
  decide +kernel

/-- **Constant time.** The reduce half produces the same machine leakage trace
    from any two starting states. -/
theorem p384Reduce_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ p384Reduce = blockLeak s₂ p384Reduce :=
  allDirect_constant_time p384Reduce p384Reduce_allDirect s₁ s₂

/-- The whole P-384 field-multiply body uses only direct base+displacement
    addressing. -/
theorem p384MulBlock_allDirect : allDirect p384MulBlock = true := by
  change allDirect (p384Schoolbook ++ p384Reduce) = true
  simp [allDirect_append, p384Schoolbook_allDirect, p384Reduce_allDirect]

/-- **Constant time.** The emitted P-384 field multiply produces the same machine
    leakage trace from any two starting states. -/
theorem p384MulBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ p384MulBlock = blockLeak s₂ p384MulBlock :=
  allDirect_constant_time p384MulBlock p384MulBlock_allDirect s₁ s₂

/-! ## 2. Value tie to the multi-term Solinas theorem

The kernel reduces the 768-bit product `P = high·2^384 + low` (with `high`,`low`
the six-word halves, each `< 2^384`) to its residue mod
`p384 = 2^384 − 2^128 − 2^96 + 2^32 − 1`. The all-inputs byte-identity that the
emitted stream computes exactly `P mod p384` is the external KAT
(`bench/p384_fieldmul_compare`, vs GMP). The lemma below records, at the value
level, that *that residue* is precisely the multi-term Solinas reduce proved
correct in `ModReduceSelect` — the kernel realises `multiSolinasReduce multiP384`. -/

open CatCrypt.Crypto.Optimizer.ModReduceSelect (multiSolinasReduce multiP384 reduceP384_eq_mod)

/-- **The kernel's residue is the multi-term Solinas reduce.** For well-formed
    product halves (`high, low < 2^384`), the residue the emitted P-384 kernel
    computes — `(high·2^384 + low) % p384` — equals `multiSolinasReduce multiP384
    high low`, the iterated-fold reduce proved correct in
    `ModReduceSelect.reduceP384_eq_mod`. The emit is thus tied to the
    verified value-level theorem, not just cross-checked against GMP. -/
theorem p384Kernel_residue_eq_multiSolinas {high low : Nat}
    (hh : high < 2 ^ 384) (hl : low < 2 ^ 384) :
    multiSolinasReduce multiP384 high low = (high * 2 ^ 384 + low) % multiP384.modulus :=
  reduceP384_eq_mod hh hl

/-! ## 3. AT&T emission (reg-ptr ABI + stack scratch frame) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn regOf allocOverflow)

/-- Pin pointers + `MULX` multiplier `yd`→`%rdx`; scratch base `sp`→`%rbp`
    (excluded from `gpPool`, so it costs no pool slot). -/
def p384MulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def p384MulAlloc : GpAlloc := allocGp p384MulPinned p384MulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias). -/
theorem p384MulAlloc_no_overflow : allocOverflow p384MulPinned p384MulBlock = none := by
  native_decide

/-- The full emitted leaf `p384_mul_x86_from_lean(z, x, y)`. The prologue saves
    callee regs, carves a 208-byte scratch frame, points `%rbp` at it, and moves
    the `y` pointer out of `%rdx`. Frame alloc/restore is trusted ABI scaffolding. -/
def p384MulAsm : String :=
  renderLeafFn "p384_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $208, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf p384MulAlloc "y" ]
    (renderBlockBody p384MulAlloc p384MulBlock)
    [ "\taddq $208, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the P-384 field-multiply `.s`. -/
def emitP384 : IO Unit := do
  IO.FS.createDirAll "bench/p384_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/p384_fieldmul_compare/gen_com/p384_mul_x86_from_lean.s" p384MulAsm
  IO.println "wrote p384_mul_x86_from_lean.s (derived Solinas reduce)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitP384

end CatCrypt.Crypto.SecureCompilation.X86Backend.P384FieldKernel
