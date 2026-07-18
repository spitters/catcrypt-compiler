/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

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

## The SM2 modulus + Montgomery constant (canonical, NOT fabricated)

The SM2 base-field prime is

    p_sm2 = 2^256 − 2^224 − 2^96 + 2^64 − 1.

Its four little-endian 64-bit limbs are
`[0xffffffffffffffff, 0xffffffff00000000, 0xffffffffffffffff, 0xfffffffeffffffff]`.

These limbs are **sourced from the vendored s2n-bignum SM2 sources**, not
fabricated:

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

This matches the vendored `bignum_montmul_sm2.S` `montreds` macro, whose short
Montgomery reduction takes the Montgomery factor `m = d0` (the `n′ = 1` step)
and folds `m · p_sm2` via the `2^32`-shift identity for this Solinas prime.

We use the standard generic CIOS Montgomery reduce (with `n′ = 1`) rather than
the prime-specific shift-and-subtract fast path: it is the same owned-backend
ADX idiom already verified for BN254/BLS12-381, and correctness is gated by the
external GMP KAT. The Solinas `2^32`-shift fast path (as in the vendored
`montreds`) is a follow-on perf optimization, not a correctness change.

## What is proved / gated here

* `sm2MontMulBlock_lowering_correct`: lowering the block to `Com (x86Dialect 64)`
  and denoting it on the init state equals `runBlock` on the source block — the
  owned backend's straight-line lowering is denotation-preserving across the
  `loadMem`/`mulxMem`/`mulx`/`adcx`/`adox`/`imul`/`sub`/`sbb`/`cmovb`/`storeMem`
  mix.
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
* `yd` — the running multiplier, pinned to `%rdx`; reloaded with `b[i]` (the
  `MAC` phase) then with the Montgomery factor `m = t0·n′ mod 2^64` (the reduce
  phase) per row.
* `t0..t5` — the six-word CIOS accumulator window (`n+2` words for `n = 4`: the
  `T += a·b[i]` and `T += m·p` adds can each carry out of limb `n` into limb
  `n+1 = t5`).
* `lo`/`hi` — the `MULX` product scratch (`hi` also stages the immediate `n′`
  and `p[j]` operands for the reduce).
* `zr` — a zero register, used for the zero-extend carry folds and to clear
  CF/OF (`xor zr, zr`) between chains. -/

/-- One CIOS MAC step on column `j` (`0 < j < 4`): `mulx hi,lo = a[j]·yd`, then
    `adcx t_j ← lo` (CF chain) and `adox t_{j+1} ← hi` (OF chain). -/
def macStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "yd") "x" (8 * j)
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS reduce step on column `j` (`0 < j < 4`): `mulx hi,lo = p[j]·m`
    (`yd` holds `m`), then the low word adds at limb `j` (`adcx t_j ← lo`, CF
    chain) and the high word at limb `j+1` (`adox t_{j+1} ← hi`, OF chain).
    `p[j]` is staged into `hi` first since `mulx` needs a register src2. -/
def redStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mov "hi" (.imm (pLimbs[j]!))
  , .mulx "hi" "lo" (.reg "yd") (.reg "hi")
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS iteration on multiplier word `b[i]`.

    Phase A (MAC, `T += a·b[i]`): clear CF/OF, load `yd ← b[i]`, the first `MULX`
    `a[0]·b[i]` lands `(lo,hi)`; `adcx t0 ← lo`, `adox t1 ← hi`, then `macStep`
    for `j = 1..3`, finally fold the top carries into the window top.

    Phase B (factor): `m = t0·n′ (mod 2^64)` computed straight into `yd`
    (=`%rdx`); since `n′ = 1` this is `m = t0`, computed by the generic `imul`
    sequence (`yd ← t0`, `yd ← yd·n′`) so the schedule is uniform with the other
    CIOS kernels.

    Phase C (reduce, `T += m·p`, then shift down): clear CF/OF; the first
    `mulx p[0]·m` adds into `t0` (`t0` becomes `≡ 0 (mod 2^64)` by the choice of
    `m`), `adox t1 ← hi`; then `redStep` for `j = 1..3`; the five-`mov` rotation
    `t0←t1, …, t4←t5, t5←0` shifts the window down.

    **Six-word accumulator window `t0..t5`.** A faithful CIOS needs `n+2 = 6`
    accumulator words for `n = 4`: each `T += …` adds a `≤ n+1`-word value to an
    `≤ n+1`-word running window, and the sum can spill into limb `n+1` (`t5`).
    The top column's high word (`adox tₙ₊₁ ← (·)ₕᵢ`) and the CF-chain tail can
    both carry *out* of `t4`; those final carries must land in `t5`, not be
    folded back into `t4`. So each phase ends with
    `adcx t4 ← 0; adcx t5 ← 0; adox t5 ← 0` — the `adcx t4 ← 0` folds the CF
    chain into `t4`, `adcx t5 ← 0` captures `t4`'s carry-out, and `adox t5 ← 0`
    captures the OF-chain terminal carry (out of the `adox t4 ← hi` of the top
    column) into `t5`. The window then rotates `t4 ← t5`. (An earlier 5-word
    window folded both tail carries back into `t4`; the limb-`n+1` carry was
    dropped, producing the small high/middle-limb KAT diffs.) -/
def ciosIter (i : Nat) : List (JInstr 64) :=
  -- Phase A: MAC  T += a·b[i]
  [ .xor_ "zr" (.reg "zr")          -- clear CF and OF
  , .loadMem "yd" "y" (8 * i)
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi") ]
  ++ macStep "t1" "t2" 1
  ++ macStep "t2" "t3" 2
  ++ macStep "t3" "t4" 3
  -- fold the CF chain into t4, then push both tail carries into t5
  ++ [ .adcx "t4" (.reg "zr"), .adcx "t5" (.reg "zr"), .adox "t5" (.reg "zr") ]
  -- Phase B: m = t0 * n' mod 2^64, computed straight into the multiplier yd
  ++ [ .mov "yd" (.reg "t0"), .mov "hi" (.imm nPrime), .imul "yd" (.reg "hi") ]
  -- Phase C: reduce  T += m*p ; t0 cancels; window shifts down
  ++ [ .xor_ "zr" (.reg "zr")
     , .mov "hi" (.imm (pLimbs[0]!))
     , .mulx "hi" "lo" (.reg "yd") (.reg "hi")
     , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi") ]
  ++ redStep "t1" "t2" 1
  ++ redStep "t2" "t3" 2
  ++ redStep "t3" "t4" 3
  -- fold the CF chain into t4, then push both tail carries into t5 (t5 already
  -- holds the Phase-A overflow; adcx/adox accumulate onto it)
  ++ [ .adcx "t4" (.reg "zr"), .adcx "t5" (.reg "zr"), .adox "t5" (.reg "zr")
     -- window shift: t0←t1, t1←t2, t2←t3, t3←t4, t4←t5, t5←0
     , .mov "t0" (.reg "t1"), .mov "t1" (.reg "t2"), .mov "t2" (.reg "t3")
     , .mov "t3" (.reg "t4"), .mov "t4" (.reg "t5"), .mov "t5" (.imm 0) ]

/-- The final branch-free conditional subtract of `p_sm2` and store of the four
    result words to `z[0..3]`. After four CIOS iterations the accumulator
    `t0..t3` holds the low four words of a value in `[0, 2p)` and `t4` its
    (`0`/`1`) carry word (the post-shift `t5`); trial-subtract `p_sm2`
    (immediates) staging each trial word in the stack scratch frame `sp[0..3]`,
    then `sbb t4, 0` threads the borrow through the carry word. If the final
    borrow `CF = 1` (i.e. `t < p`) `cmovb` keeps the original `tj`; else the
    trial word in scratch is kept. -/
def sm2FinalReduce : List (JInstr 64) :=
  [ .mov "lo" (.reg "t0"), .mov "hi" (.imm (pLimbs[0]!)), .sub "lo" (.reg "hi"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.reg "t1"), .mov "hi" (.imm (pLimbs[1]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.reg "t2"), .mov "hi" (.imm (pLimbs[2]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.reg "t3"), .mov "hi" (.imm (pLimbs[3]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 24 (.reg "lo")
  , .sbb "t4" (.imm 0)   -- top word; CF = final borrow; CF=1 ⇒ t < p ⇒ keep originals
  , .loadMem "hi" "sp" 0,  .cmovb "hi" (.reg "t0"), .storeMem "z" 0  (.reg "hi")
  , .loadMem "hi" "sp" 8,  .cmovb "hi" (.reg "t1"), .storeMem "z" 8  (.reg "hi")
  , .loadMem "hi" "sp" 16, .cmovb "hi" (.reg "t2"), .storeMem "z" 16 (.reg "hi")
  , .loadMem "hi" "sp" 24, .cmovb "hi" (.reg "t3"), .storeMem "z" 24 (.reg "hi") ]

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

/-! ## 6. AT&T assembly emission (reg-ptr ABI + small stack scratch frame) -/

/-- Pin pointers + the `MULX` multiplier `yd`→`%rdx` + scratch base `sp`→`%rbp`. -/
def sm2MontMulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def sm2MontMulAlloc : GpAlloc := allocGp sm2MontMulPinned sm2MontMulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias,
    the #380 class). -/
theorem sm2MontMulAlloc_no_overflow :
    allocOverflow sm2MontMulPinned sm2MontMulBlock = none := by native_decide

/-- The rendered AT&T body (one line per `JInstr`). -/
def sm2MontMulAsmBody : List String := renderBlockBody sm2MontMulAlloc sm2MontMulBlock

/-- The full emitted leaf `sm2_mont_mul_x86_from_lean(z, x, y)`. The prologue
    saves callee regs, carves a 32-byte scratch frame, points `%rbp` at it, and
    moves the `y` pointer out of `%rdx`. Frame alloc/restore is trusted ABI
    scaffolding outside the `runBlock`-verified body. -/
def sm2MontMulAsm : String :=
  renderLeafFn "sm2_mont_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $32, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf sm2MontMulAlloc "y" ]
    sm2MontMulAsmBody
    [ "\taddq $32, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- Shape check: the emitted asm contains the dual carry-chain CIOS idiom
    (`mulx`, `adcx`, `adox`, `imul` for the Montgomery factor), the
    memory-operand `MULX` reads the multiplicand from `[x]` (`mulxq 0(%rsi)`),
    the result stores print in AT&T form (`(%rdi)`), and the `%rdx`-pinned
    multiplier is the `MULX` src1. -/
theorem sm2MontMulAsm_shape :
    hasSub sm2MontMulAsm "mulx"
      ∧ hasSub sm2MontMulAsm "adcx"
      ∧ hasSub sm2MontMulAsm "adox"
      ∧ hasSub sm2MontMulAsm "imul"
      ∧ hasSub sm2MontMulAsm "mulxq 0(%rsi)"
      ∧ hasSub sm2MontMulAsm "(%rdi)"
      ∧ hasSub sm2MontMulAsm "src1=%rdx" := by native_decide

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/sm2_compare/gen_com"
  IO.FS.writeFile
    "bench/sm2_compare/gen_com/sm2_mont_mul_x86_from_lean.s"
    sm2MontMulAsm
  IO.println "wrote gen_com/sm2_mont_mul_x86_from_lean.s (in-Lean x86 backend CIOS, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sm2MontMulKernel
