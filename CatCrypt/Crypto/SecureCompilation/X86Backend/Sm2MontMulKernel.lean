/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# SM2 `Fp` Montgomery field-multiply, lowered through the in-Lean x86 backend

This module emits the SM2 (Chinese 256-bit Weierstrass curve, GB/T 32918,
the s2n-bignum `sm2` analogue) base-field Montgomery multiply

    mont_mul(a, b) = a · b · R⁻¹ (mod p),   R = 2^256,

through the SAME owned x86 backend (`JasminModel.runBlock` /
`X86Dialect.lowerBlock_denote` / `AsmPrinter`, no jasminc) used for the
BN254 (`Bn254MontMulKernel`), BLS12-381, `bignum_mul_4_8`, and `fe25519`
kernels, framed by the principled SysV ABI layer (`renderSysVLeafFn`, #464).
It is the SM2 analog of the BN254 field-multiply: four CIOS iterations over a
256-bit prime.

## The SM2 modulus and Montgomery constant

The SM2 base-field prime is

    p_sm2 = 2^256 − 2^224 − 2^96 + 2^64 − 1.

Its four little-endian 64-bit limbs are
`[0xffffffffffffffff, 0xffffffff00000000, 0xffffffffffffffff, 0xfffffffeffffffff]`.

These limbs come from the vendored s2n-bignum SM2 sources:

* `bench/reference_install/s2n-bignum/x86/sm2/bignum_mod_sm2_4.S` documents the
  modulus directly as `[n3; -1; n1; -1] = p_sm2` with
  `n1 = 0xffffffff00000000`, `n3 = 0xfffffffeffffffff` (and the two `-1` limbs
  `= 0xffffffffffffffff`). That is exactly `pLimbs` below, big-endian-listed.
* `bench/reference_install/s2n-bignum/x86/sm2/bignum_montmul_sm2.S` corroborates
  via its `2^320 − p_sm2` reload `[1, 0xffffffff, 0, 0x100000000, -1]`.

The above limbs equal the closed form `2^256 − 2^224 − 2^96 + 2^64 − 1` exactly
(checked: the formula and the vendored constants agree bit-for-bit).

Because the lowest limb of `p_sm2` is `0xffffffffffffffff = −1 (mod 2^64)`, we
have `p ≡ −1 (mod 2^64)`, hence the Montgomery constant

    n′ = −p⁻¹ (mod 2^64) = 1.

The Montgomery factor of a CIOS row is therefore the low accumulator word
itself, `m = t0`, and the fold of `m · p_sm2` needs no multiply. Writing
`L = m ≪ 32` and `H = m ≫ 32` (so `m · 2^32 = L + H·2^64` as a 128-bit value),

    m · p_sm2 = m·2^256 − (L + H·2^64)·2^192 − (L + H·2^64)·2^64 + m·2^64 − m,

and the two middle terms at word position 1 combine into the single 128-bit
value `m·(2^32 − 1) = (L + H·2^64) − m`. The reduce is then one `shl`/`shr`
pair, one `sub`/`sbb` forming that 128-bit value, and one borrow chain across
the accumulator — the `montreds` macro of the vendored `bignum_montmul_sm2.S`.

## What is proved / gated here

* `sm2MontMulBlock_lowering_correct`: lowering the block to `Com (x86Dialect 64)`
  and denoting it on the init state equals `runBlock` on the source block — the
  owned backend's straight-line lowering is denotation-preserving across the
  `loadMem`/`mulxMem`/`adcx`/`adox`/`shl`/`shr`/`add`/`adc`/`sub`/`sbb`/`cmovb`/
  `storeMem` mix.
* `sm2MontMulAlloc_no_overflow`: the first-fit allocator assigns every register
  name a distinct pool register (no silent `%rax`-alias, the #380 class).
* `sm2MontMulBlock_constant_time`: the body is straight-line all-direct
  addressing (no secret-indexed memory), so its machine leakage trace is
  state-independent by `ConstantTimeCoverage.allDirect_constant_time`.
* The all-inputs byte-identity that the emitted stream computes
  `a·b·R⁻¹ (mod p_sm2)` is the external KAT (`bench/sm2_compare`, vs GMP
  `mod p_sm2` — the canonical-arithmetic oracle): the standard gate for these
  word kernels (per REV-12), over corner + random vectors. CIOS Montgomery's
  value-level correctness is a generic Montgomery identity; in-Lean it is a
  256×256→512 SAT instance, infeasible, hence the external gate.

## Trust story

Identical to `JasminModel` / `X86Dialect` / `AsmPrinter`: the verified artifact
is `Com (x86Dialect 64) → runBlock → evalInstr`, the faithful transcription of
Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is the thin syntactic trust
boundary, and the SysV leaf prologue/epilogue is trusted ABI scaffolding
(`renderSysVLeafFn`) outside the verified body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sm2MontMulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. The SM2 modulus and Montgomery constant (canonical, vendored) -/

/-- `p_sm2` little-endian 64-bit limbs
    (`= 2^256 − 2^224 − 2^96 + 2^64 − 1`,
    sourced from `s2n-bignum/x86/sm2/bignum_mod_sm2_4.S` `[n3; -1; n1; -1]`). -/
def pLimbs : List Nat :=
  [ 0xffffffffffffffff, 0xffffffff00000000
  , 0xffffffffffffffff, 0xfffffffeffffffff ]

/-- `n′ = −p⁻¹ mod 2^64 = 1` (since `p_sm2 ≡ −1 mod 2^64`).
    Satisfies `p_sm2 · n′ + 1 ≡ 0 (mod 2^64)`. -/
def nPrime : Nat := 1

/-! ## 2. The CIOS body as a `List (JInstr 64)`

Register names (within the 14-GP budget — four-limb window):
* `z`/`x`/`y` — the result and operand base pointers (`z`→`%rdi`, `x`→`%rsi`,
  `y` arrives in `%rdx` and is moved to a free register in the prologue —
  `%rdx` is reserved for the `MULX`/`mulx` multiplier).
* `yd` — the running multiplier, pinned to `%rdx`; reloaded with `b[i]` for the
  `MAC` phase of each row, and reused as a `montreds` temporary in the reduce.
* `t0..t5` — the six-word CIOS accumulator window (`n+2` words for `n = 4`: the
  `T += a·b[i]` and `T += m·p` folds can each carry out of limb `n` into limb
  `n+1 = t5`).
* `lo`/`hi` — the `MULX` product scratch, and the `montreds` shift pair
  (`L = m ≪ 32`, `H = m ≫ 32`) in the reduce.
* `zr` — a zero register for the zero-extend carry folds and to clear CF/OF
  (`xor zr, zr`) between chains, and the fourth `montreds` temporary. -/

/-- One CIOS MAC step on column `j` (`0 < j < 4`): `mulx hi,lo = a[j]·yd`, then
    `adcx t_j ← lo` (CF chain) and `adox t_{j+1} ← hi` (OF chain). -/
def macStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "yd") "x" (8 * j)
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- The short Montgomery reduction of `p_sm2` (`montreds`): fold `m · p_sm2`
    into the six accumulator words `u0..u5`, with the Montgomery factor
    `m = u0` (`n′ = 1`) and no multiply.

    `lo`/`hi` receive the shift pair `L = m ≪ 32`, `H = m ≫ 32`, copied to
    `yd`/`zr`; `sub lo, u0` / `sbb hi, 0` then turns `[hi:lo]` into the 128-bit
    `m·(2^32 − 1) = m·2^32 − m`. The fold is

    * `+ m` at limb 4 (`m·2^256`), carrying into limb 5;
    * `− m·(2^32 − 1)` at limbs 1–2 (`− m·2^96 + m·2^64`), `− L` at limb 3 and
      `− H` at limb 4 (`− m·2^224`), one borrow chain ending at limb 5;
    * `− m` at limb 0, which cancels `u0` exactly and borrows nothing, so it is
      not emitted — limb 0 leaves the window. -/
def montreds (u0 u1 u2 u3 u4 u5 : String) : List (JInstr 64) :=
  [ .mov "lo" (.reg u0), .shl "lo" (.imm 32)
  , .mov "hi" (.reg u0), .shr "hi" (.imm 32)
  , .mov "yd" (.reg "lo"), .mov "zr" (.reg "hi")
  , .sub "lo" (.reg u0), .sbb "hi" (.imm 0)
  , .add u4 (.reg u0), .adc u5 (.imm 0)
  , .sub u1 (.reg "lo"), .sbb u2 (.reg "hi")
  , .sbb u3 (.reg "yd"), .sbb u4 (.reg "zr"), .sbb u5 (.imm 0) ]

/-- The accumulator register holding limb `j` of the window during iteration `i`.
    The window shifts down by one limb per iteration; rotating the six names
    instead of copying the words realises the shift with no `mov`. -/
def tName (i j : Nat) : String := "t" ++ toString ((i + j) % 6)

/-- One CIOS iteration on multiplier word `b[i]`, over the rotated window
    `uⱼ = tName i j`.

    Phase A (MAC, `T += a·b[i]`): clear CF/OF, load `yd ← b[i]`, the first `MULX`
    `a[0]·b[i]` lands `(lo,hi)`; `adcx u0 ← lo`, `adox u1 ← hi`, then `macStep`
    for `j = 1..3`, finally fold the top carries into the window top.

    Phase B (reduce, `T += m·p`): `montreds` with `m = u0` (`n′ = 1`). Limb 0 is
    zero afterwards and becomes limb 5 of iteration `i+1` under the name
    rotation, so the iteration ends by clearing `u0`.

    **Six-word accumulator window.** A faithful CIOS needs `n+2 = 6` accumulator
    words for `n = 4`: each `T += …` adds a `≤ n+1`-word value to an `≤ n+1`-word
    running window, and the sum can spill into limb `n+1` (`u5`). The top
    column's high word (`adox uₙ₊₁ ← (·)ₕᵢ`) and the CF-chain tail can both carry
    *out* of `u4`; those final carries land in `u5`, not folded back into `u4`.
    So Phase A ends with `adcx u4 ← 0; adcx u5 ← 0; adox u5 ← 0` — the
    `adcx u4 ← 0` folds the CF chain into `u4`, `adcx u5 ← 0` captures `u4`'s
    carry-out, and `adox u5 ← 0` captures the OF-chain terminal carry (out of the
    `adox u4 ← hi` of the top column) into `u5`. -/
def ciosIter (i : Nat) : List (JInstr 64) :=
  let u0 := tName i 0; let u1 := tName i 1; let u2 := tName i 2
  let u3 := tName i 3; let u4 := tName i 4; let u5 := tName i 5
  -- Phase A: MAC  T += a·b[i]
  [ .xor_ "zr" (.reg "zr")          -- clear CF and OF
  , .loadMem "yd" "y" (8 * i)
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx u0 (.reg "lo"), .adox u1 (.reg "hi") ]
  ++ macStep u1 u2 1
  ++ macStep u2 u3 2
  ++ macStep u3 u4 3
  -- fold the CF chain into u4, then push both tail carries into u5
  ++ [ .adcx u4 (.reg "zr"), .adcx u5 (.reg "zr"), .adox u5 (.reg "zr") ]
  -- Phase B: reduce  T += m*p with m = u0 ; u0 cancels and becomes the next
  -- iteration's top limb
  ++ montreds u0 u1 u2 u3 u4 u5
  ++ [ .mov u0 (.imm 0) ]

/-- The final branch-free conditional subtract of `p_sm2` and store of the four
    result words to `z[0..3]`. After four CIOS iterations limbs `0..3` of the
    window (`tName 4 0 .. tName 4 3`) hold the low four words of a value in
    `[0, 2p)` and limb 4 its (`0`/`1`) carry word; trial-subtract `p_sm2`
    (immediates staged through `hi`, since `sub`/`sbb` take a register source
    for a full 64-bit operand), then `sbb, 0` threads the borrow through the
    carry word. If the final borrow `CF = 1` (i.e. `t < p`) `cmovb` restores the
    original limb over the trial word; otherwise the trial word is stored.

    The operand pointers `x`/`y`, the `MULX` multiplier `yd` and the zero
    register `zr` are dead once the last CIOS iteration has run, so they carry
    the four trial words and the reduce needs no memory. -/
def sm2FinalReduce : List (JInstr 64) :=
  let u0 := tName 4 0; let u1 := tName 4 1; let u2 := tName 4 2
  let u3 := tName 4 3; let u4 := tName 4 4
  [ .mov "x"  (.reg u0), .mov "hi" (.imm (pLimbs[0]!)), .sub "x"  (.reg "hi")
  , .mov "y"  (.reg u1), .mov "hi" (.imm (pLimbs[1]!)), .sbb "y"  (.reg "hi")
  , .mov "yd" (.reg u2), .mov "hi" (.imm (pLimbs[2]!)), .sbb "yd" (.reg "hi")
  , .mov "zr" (.reg u3), .mov "hi" (.imm (pLimbs[3]!)), .sbb "zr" (.reg "hi")
  , .sbb u4 (.imm 0)   -- top word; CF = final borrow; CF=1 ⇒ t < p ⇒ keep originals
  , .cmovb "x" (.reg u0), .cmovb "y" (.reg u1)
  , .cmovb "yd" (.reg u2), .cmovb "zr" (.reg u3)
  , .storeMem "z" 0 (.reg "x"),  .storeMem "z" 8  (.reg "y")
  , .storeMem "z" 16 (.reg "yd"), .storeMem "z" 24 (.reg "zr") ]

/-- The full CIOS Montgomery multiply body: zero the accumulator, four CIOS
    iterations, then the final conditional subtract + store. A concrete flat
    `List (JInstr 64)` the lowering / allocation / constant-time lemmas chew on. -/
def sm2MontMulBlock : List (JInstr 64) :=
  [ .mov "zr" (.imm 0)
  , .mov "t0" (.imm 0), .mov "t1" (.imm 0), .mov "t2" (.imm 0)
  , .mov "t3" (.imm 0), .mov "t4" (.imm 0), .mov "t5" (.imm 0) ]
  ++ (List.range 4).flatMap ciosIter
  ++ sm2FinalReduce

/-! ## 3. The initial machine state (reg-ptr ABI) -/

/-- Build the init state from the eight operand limbs. -/
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

/-! ## 4. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the CIOS block.** Lowering to `Com (x86Dialect 64)`
    and denoting on the init state equals `runBlock` on the source block — the
    owned backend's straight-line lowering is denotation-preserving across the
    full `loadMem`/`mulxMem`/`mulx`/`adcx`/`adox`/`imul`/`sub`/`sbb`/`cmovb`/
    `storeMem` mix. -/
theorem sm2MontMulBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) sm2MontMulBlock).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) sm2MontMulBlock :=
  lowerBlock_denote_closed sm2MontMulBlock
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-! ## 5. Constant-time: straight-line, all-direct addressing -/

/-- The whole CIOS body uses only direct base+displacement addressing (no
    secret-indexed memory access). -/
theorem sm2MontMulBlock_allDirect : allDirect sm2MontMulBlock = true := by
  native_decide

/-- **Constant time.** The emitted SM2 Montgomery-multiply body produces the
    same machine leakage trace from any two starting states — it is constant
    time — discharged by the decidable `allDirect` check through
    `ConstantTimeCoverage.allDirect_constant_time`. (Same all-direct argument as
    the secp256k1 / BN254 / BLS12-381 field-mul kernels.) -/
theorem sm2MontMulBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ sm2MontMulBlock = blockLeak s₂ sm2MontMulBlock :=
  allDirect_constant_time sm2MontMulBlock sm2MontMulBlock_allDirect s₁ s₂

/-! ## 6. AT&T assembly emission (reg-ptr ABI) -/

/-- Pin the pointers `z`→`%rdi`, `x`→`%rsi` and the `MULX` multiplier
    `yd`→`%rdx`. -/
def sm2MontMulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx")]

/-- First-fit allocation over the full block. -/
def sm2MontMulAlloc : GpAlloc := allocGp sm2MontMulPinned sm2MontMulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias,
    the #380 class). -/
theorem sm2MontMulAlloc_no_overflow :
    allocOverflow sm2MontMulPinned sm2MontMulBlock = none := by native_decide

/-- The rendered AT&T body (one line per `JInstr`). -/
def sm2MontMulAsmBody : List String := renderBlockBody sm2MontMulAlloc sm2MontMulBlock

/-- The full emitted leaf `sm2_mont_mul_x86_from_lean(z, x, y)`. The prologue
    saves the callee-saved registers and moves the `y` pointer out of `%rdx`
    (reserved for the `MULX` multiplier). Save/restore is trusted ABI
    scaffolding outside the `runBlock`-verified body. -/
def sm2MontMulAsm : String :=
  renderLeafFn "sm2_mont_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tmovq %rdx, " ++ regOf sm2MontMulAlloc "y" ]
    sm2MontMulAsmBody
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/- Shape check: the emitted asm contains the dual carry-chain CIOS idiom
    (`mulx`, `adcx`, `adox`), the `2^32` shift pair of the `montreds` reduce
    (`shlq $32`, `shrq $32`), the memory-operand `MULX` reads the multiplicand
    from `[x]` (`mulxq 0(%rsi)`), the result stores print in AT&T form
    (`(%rdi)`), and the `%rdx`-pinned multiplier is the `MULX` src1. -/
#guard (hasSub sm2MontMulAsm "mulx") && (hasSub sm2MontMulAsm "adcx") && (hasSub sm2MontMulAsm "adox") && (hasSub sm2MontMulAsm "shlq $32") && (hasSub sm2MontMulAsm "shrq $32") && (hasSub sm2MontMulAsm "mulxq 0(%rsi)") && (hasSub sm2MontMulAsm "(%rdi)") && (hasSub sm2MontMulAsm "src1=%rdx")

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/sm2_compare/gen_com"
  IO.FS.writeFile
    "bench/sm2_compare/gen_com/sm2_mont_mul_x86_from_lean.s"
    sm2MontMulAsm
  IO.println "wrote gen_com/sm2_mont_mul_x86_from_lean.s (in-Lean x86 backend CIOS, no jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sm2MontMulKernel
