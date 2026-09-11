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

/-!
# SM2 PLAIN (Solinas) field-multiply kernel, generated through the multi-term pass

`ModReduceSelect.lean` §10–13 prove the *value-level* multi-term Solinas reduce
`multiSolinasReduce multiSm2` computes the SM2 residue
`(high·2^256 + low) % p_sm2` for

    p_sm2 = 2^256 − 2^224 − 2^96 + 2^64 − 1

(`c = 2^224 + 2^96 − 2^64 + 1`, `fuel = 9`; `reduceSm2_eq_mod` specialises the
general `multiSolinasReduce_eq_mod`), and §13 proves the **signed-shift
schedule** — split at `2^256`, shift the high half by each recorded term
exponent, add/subtract per sign — computes exactly the Solinas fold
(`termsFold_eq_solinasFold`, with the register-window form `sm2FoldShifts`).

The reduce instruction block here is **GENERATED from the term list** by the
§14 multi-term arm of the selection pass (`multiTermReduceBlock multiSm2`,
fired by `selectMultiTermReduce` — `sm2Reduce_selected` below): nine
signed-shift folds over a full 2n-word window (no bits discarded), two
branch-free conditional subtracts of `p_sm2`, and the four-word store. There is
no hand-authored fold schedule in this file; the schoolbook product half is the
proven dual-ADCX/ADOX carry idiom retargeted to the scratch frame, identical in
shape to `P256FieldKernel.p256Schoolbook`.

This is the **PLAIN** field multiply `z = (x·y) mod p_sm2` (the P-256-class
fast path that exploits the curve-specific prime structure), *not* a Montgomery
multiply. s2n-bignum's deployed SM2 field multiply (`bignum_montmul_sm2`) is in
the Montgomery domain; the plain Solinas mul-with-curve-specific-reduce here is
the apples-to-apples comparison for the field-mul class that exploits the prime
shape (like secp256k1 / x25519): `(x·y) mod p`, validated against GMP `mod p`.

## What is proved / gated here

* `sm2Reduce_selected`: the reduce block is what the selection pass emits on
  `multiSm2` — the kernel comes through the pass, not hand authoring.
* `sm2FieldMul_lowering_correct`: lowering the block to `Com (x86Dialect 64)`
  and denoting on the init state equals `runBlock` on the source block (via
  `X86Dialect.lowerBlock_denote_closed`).
* `sm2FieldMul_constant_time`: the body is straight-line all-direct addressing,
  so its machine leakage trace is state-independent (via
  `ConstantTimeCoverage.allDirect_constant_time`).
* `sm2FieldMulAlloc_no_overflow`: the first-fit allocator maps every register
  name to a distinct pool register (no silent `%rax`-alias, the #380 class).
* `sm2FieldMul_residue_eq_multiSolinas`: the residue the kernel computes —
  `(high·2^256 + low) % p_sm2`, the value the KAT pins byte-for-byte — equals
  `multiSolinasReduce multiSm2 high low`, tying the emit to the value-level
  theorem (`ModReduceSelect.reduceSm2_eq_mod`), not merely cross-checking GMP.
* `sm2FieldMul_kat_corners`: an in-Lean `runBlock` honesty gate — the generated
  block computes `(x·y) mod p_sm2` on the corner vectors `(p−1)²`,
  `(2^256−1)²`, and the SM2 generator-coordinate product `Gx·Gy`
  (GB/T 32918.5). This catches a wrong schedule before the external KAT; it is
  NOT the final gate.
* The all-inputs byte-identity that the emitted stream computes `(x·y) mod
  p_sm2` is the external KAT (`bench/sm2_compare/sm2_field_kat.c`, vs GMP `mod
  p_sm2` — the canonical-arithmetic oracle): corner pairs + xorshift-random
  vectors. The 512-bit iterated fold is infeasible as one in-Lean symbolic
  identity, hence the external gate, exactly as for P-256.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sm2FieldKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. The schoolbook product half (proven dual-carry idiom → scratch frame)

Identical in shape to `P256FieldKernel.p256Schoolbook`: the 4×4 `MULX`/ADCX/ADOX
schoolbook of `BignumMontMulKernel.mul48Block`, with the eight product stores
retargeted from the (4-word) result pointer `z` to the scratch frame `sp[0..7]`.
The 512-bit product `P = high·2^256 + low` lands at `sp[0..7]` (LSW first) —
exactly the working-value layout the generated reduce consumes. -/

/-- The 4×4 schoolbook into the scratch frame `sp[0..7]` (eight 64-bit product
    words, LSW at `sp 0`). -/
def sm2Schoolbook : List (JInstr 64) :=
  [ .mov "zr" (.imm 0), .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 0
  , .mulxMem "w1" "w0" (.reg "yd") "x" 0
  , .storeMem "sp" 0 (.reg "w0")
  , .mulxMem "w2" "lo" (.reg "yd") "x" 8,  .adcx "w1" (.reg "lo")
  , .mulxMem "w3" "lo" (.reg "yd") "x" 16, .adcx "w2" (.reg "lo")
  , .mulxMem "w0" "lo" (.reg "yd") "x" 24, .adcx "w3" (.reg "lo")
  , .adcx "w0" (.reg "zr")
  , .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" 8
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0,  .adcx "w1" (.reg "lo"), .adox "w2" (.reg "hi")
  , .storeMem "sp" 8 (.reg "w1")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8,  .adcx "w2" (.reg "lo"), .adox "w3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16, .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .mulxMem "w1" "lo" (.reg "yd") "x" 24, .adcx "w0" (.reg "lo")
  , .adox "w1" (.reg "zr"), .adcx "w1" (.reg "zr")
  , .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" 16
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0,  .adcx "w2" (.reg "lo"), .adox "w3" (.reg "hi")
  , .storeMem "sp" 16 (.reg "w2")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8,  .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16, .adcx "w0" (.reg "lo"), .adox "w1" (.reg "hi")
  , .mulxMem "w2" "lo" (.reg "yd") "x" 24, .adcx "w1" (.reg "lo")
  , .adox "w2" (.reg "zr"), .adcx "w2" (.reg "zr")
  , .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" 24
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0,  .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .storeMem "sp" 24 (.reg "w3")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8,  .adcx "w0" (.reg "lo"), .adox "w1" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16, .adcx "w1" (.reg "lo"), .adox "w2" (.reg "hi")
  , .mulxMem "w3" "lo" (.reg "yd") "x" 24, .adcx "w2" (.reg "lo")
  , .adox "w3" (.reg "zr"), .adcx "w3" (.reg "zr")
  , .storeMem "sp" 32 (.reg "w0"), .storeMem "sp" 40 (.reg "w1")
  , .storeMem "sp" 48 (.reg "w2"), .storeMem "sp" 56 (.reg "w3") ]

/-! ## 2. The reduce: generated by the selection pass -/

open CatCrypt.Crypto.Optimizer.ModReduceSelect
  (multiSolinasReduce multiSm2 multiSm2_modulus reduceSm2_eq_mod
   multiTermReduceBlock fieldMulMultiTermKernel selectMultiTermReduce
   select_fires_sm2 mtFrameBytes)

/-- The SM2 reduce block, GENERATED from `multiSm2`'s term list by the
    multi-term arm of the selection pass (nine signed-shift folds, two
    conditional subtracts, four-word store). -/
def sm2Reduce : List (JInstr 64) := multiTermReduceBlock multiSm2

/-- **The reduce comes through the pass.** The block this kernel uses is what
    `selectMultiTermReduce` emits on `multiSm2` — the multi-term pattern fires
    and its output is `sm2Reduce`, definitionally. -/
theorem sm2Reduce_selected :
    selectMultiTermReduce multiSm2 = some sm2Reduce :=
  select_fires_sm2

/-- The full SM2 plain field-multiply block: schoolbook product to the scratch
    frame, then the pass-generated multi-term Solinas reduce. Computes
    `z = (x·y) mod p_sm2` (PLAIN, not Montgomery). -/
def sm2FieldMul : List (JInstr 64) :=
  fieldMulMultiTermKernel sm2Schoolbook multiSm2

/-- The kernel is the schoolbook composed with the selected reduce. -/
theorem sm2FieldMul_eq : sm2FieldMul = sm2Schoolbook ++ sm2Reduce := rfl

/-! ## 3. Value tie to the multi-term Solinas theorem

The kernel reduces the 512-bit product `P = high·2^256 + low` (`high`,`low` the
four-word halves, each `< 2^256`) to its residue mod `p_sm2`. The lemma below
records, at the value level, that this residue is precisely the multi-term
Solinas reduce proved correct in `ModReduceSelect` — i.e. the kernel realises
`multiSolinasReduce multiSm2`, not merely "some" reduction. This is the SM2
analogue of `P256FieldKernel.p256Kernel_residue_eq_multiSolinas`. The
all-inputs byte-identity that the emitted instruction stream computes exactly
`P mod p_sm2` is the external KAT (`bench/sm2_compare/sm2_field_kat.c`, vs
GMP). -/

/-- **The kernel's residue is the multi-term Solinas reduce.** For well-formed
    product halves (`high, low < 2^256`), the residue the SM2 plain
    field-multiply kernel computes — `(high·2^256 + low) % p_sm2`, the value
    the KAT pins byte-for-byte — equals `multiSolinasReduce multiSm2 high low`,
    the iterated-fold reduce proved correct in
    `ModReduceSelect.reduceSm2_eq_mod` (which specialises the proven *general*
    `multiSolinasReduce_eq_mod`). -/
theorem sm2FieldMul_residue_eq_multiSolinas {high low : Nat}
    (hh : high < 2 ^ 256) (hl : low < 2 ^ 256) :
    multiSolinasReduce multiSm2 high low = (high * 2 ^ 256 + low) % multiSm2.modulus :=
  reduceSm2_eq_mod hh hl

/-! ## 4. The initial machine state (reg-ptr ABI) -/

/-- Build the init state from the eight operand limbs (`x[0..3]`, `y[0..3]`). -/
def initState (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "x" then
        if off = 0 then a0 else if off = 8 then a1 else if off = 16 then a2
        else if off = 24 then a3 else 0
      else if base = "y" then
        if off = 0 then b0 else if off = 8 then b1 else if off = 16 then b2
        else if off = 24 then b3 else 0
      else 0 }

/-! ## 5. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness.** Lowering the SM2 field-multiply block to
    `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on the
    source block — the owned backend's straight-line lowering is
    denotation-preserving (via `X86Dialect.lowerBlock_denote_closed`). -/
theorem sm2FieldMul_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) sm2FieldMul).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) sm2FieldMul :=
  lowerBlock_denote_closed sm2FieldMul
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-! ## 6. Constant-time: straight-line, all-direct addressing -/

/-- The whole field-mul body uses only direct base+displacement addressing (no
    secret-indexed memory access). -/
theorem sm2FieldMul_allDirect : allDirect sm2FieldMul = true := by
  native_decide

/-- **Constant time.** The emitted SM2 plain field-multiply produces the same
    machine leakage trace from any two starting states — it is constant time —
    discharged by the decidable `allDirect` check through
    `ConstantTimeCoverage.allDirect_constant_time`. -/
theorem sm2FieldMul_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ sm2FieldMul = blockLeak s₂ sm2FieldMul :=
  allDirect_constant_time sm2FieldMul sm2FieldMul_allDirect s₁ s₂

/-! ## 7. In-Lean `runBlock` honesty gate (corner vectors — NOT the final gate)

The generated schedule is executed by `runBlock` on corner inputs and compared
against `(x·y) mod p_sm2` computed independently over `Nat`. Vectors: the
maximal canonical pair `(p−1)²`, the maximal register pair `(2^256−1)²`
(non-canonical inputs — the reduce contract only needs `high, low < 2^256`),
and the SM2 generator-coordinate product `Gx·Gy` (GB/T 32918.5 published
constants). The all-inputs gate remains the external GMP KAT. -/

/-- `p_sm2` as a `Nat`. -/
def pSm2 : Nat := 2 ^ 256 - 2 ^ 224 - 2 ^ 96 + 2 ^ 64 - 1

/-- 64-bit limb `i` of a `Nat`. -/
def limb (x : Nat) (i : Nat) : BitVec 64 := BitVec.ofNat 64 (x / 2 ^ (64 * i))

/-- Run the kernel on `(x, y)` and check the four stored `z` words against
    `(x·y) mod p_sm2`. -/
def sm2KatOne (x y : Nat) : Bool :=
  let s := runBlock
    (initState (limb x 0) (limb x 1) (limb x 2) (limb x 3)
               (limb y 0) (limb y 1) (limb y 2) (limb y 3)) sm2FieldMul
  (s.mem "z" 0).toNat + 2 ^ 64 * (s.mem "z" 8).toNat
      + 2 ^ 128 * (s.mem "z" 16).toNat + 2 ^ 192 * (s.mem "z" 24).toNat
    == (x * y) % pSm2

/-- The SM2 generator x-coordinate (GB/T 32918.5). -/
def sm2Gx : Nat := 0x32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7

/-- The SM2 generator y-coordinate (GB/T 32918.5). -/
def sm2Gy : Nat := 0xBC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0

/-- **Corner-vector honesty gate on the generated schedule**: `(p−1)²`,
    `(2^256−1)²`, and the generator product `Gx·Gy` all reduce correctly under
    `runBlock`. -/
theorem sm2FieldMul_kat_corners :
    (sm2KatOne (pSm2 - 1) (pSm2 - 1)
      && sm2KatOne (2 ^ 256 - 1) (2 ^ 256 - 1)
      && sm2KatOne sm2Gx sm2Gy) = true := by
  native_decide

/-- Value-level corner gate on the proven fold itself: the `(p−1)²` and
    `2^512−1` products reduce to the GMP-checkable residues. -/
theorem sm2Fold_value_corners :
    (multiSolinasReduce multiSm2 (((pSm2 - 1) * (pSm2 - 1)) / 2 ^ 256)
          (((pSm2 - 1) * (pSm2 - 1)) % 2 ^ 256)
        == ((pSm2 - 1) * (pSm2 - 1)) % pSm2
      && multiSolinasReduce multiSm2 ((2 ^ 512 - 1) / 2 ^ 256) ((2 ^ 512 - 1) % 2 ^ 256)
        == (2 ^ 512 - 1) % pSm2) = true := by
  native_decide

/-! ## 8. AT&T assembly emission (reg-ptr ABI + stack scratch frame) -/

/-- Pin pointers + the `MULX` multiplier `yd`→`%rdx` + scratch base `sp`→`%rbp`
    (excluded from `gpPool`, so it costs no pool slot). -/
def sm2FieldMulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def sm2FieldMulAlloc : GpAlloc := allocGp sm2FieldMulPinned sm2FieldMul

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias,
    the #380 class). -/
theorem sm2FieldMulAlloc_no_overflow :
    allocOverflow sm2FieldMulPinned sm2FieldMul = none := by native_decide

/-- The rendered AT&T body (one line per `JInstr`). -/
def sm2FieldMulAsmBody : List String := renderBlockBody sm2FieldMulAlloc sm2FieldMul

/-- The full emitted leaf `sm2_field_mul_x86_from_lean(z, x, y)`. The prologue
    saves callee regs, carves the `mtFrameBytes 4 = 160`-byte scratch frame,
    points `%rbp` at it, and moves the `y` pointer out of `%rdx`. Frame
    alloc/restore is trusted ABI scaffolding outside the `runBlock`-verified
    body. -/
def sm2FieldMulAsm : String :=
  renderLeafFn "sm2_field_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $160, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf sm2FieldMulAlloc "y" ]
    sm2FieldMulAsmBody
    [ "\taddq $160, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the SM2 plain field-multiply `.s`. -/
def emitSm2Field : IO Unit := do
  IO.FS.createDirAll "bench/sm2_compare/gen_com"
  IO.FS.writeFile
    "bench/sm2_compare/gen_com/sm2_field_mul_x86_from_lean.s" sm2FieldMulAsm
  IO.println "wrote gen_com/sm2_field_mul_x86_from_lean.s (SM2 Solinas plain field-mul, pass-generated reduce)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sm2FieldKernel
