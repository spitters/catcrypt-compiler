/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc

/-!
# BLS12-381 `Fp` Montgomery field-multiply, lowered through the in-Lean x86 backend (#490)

This module emits the BLS12-381 base-field (`p = 0x1a0111ea…aaab`, 381 bits,
six 64-bit limbs) Montgomery multiply

    mont_mul(a, b) = a · b · R⁻¹ (mod p),   R = 2^384,

through the SAME owned x86 backend (`JasminModel.runBlock` /
`X86Dialect.lowerBlock_denote` / `AsmPrinter`, no jasminc) used for the
`bignum_mul_4_8` / `fe25519` kernels, framed by the principled SysV ABI layer
(`renderSysVLeafFn`, #464). It is the field-multiply leg of the BLS-vs-blst
program (#487).

Unlike fe25519 (`2^255−19`, a Solinas prime with a cheap fold) and P-384 (a
Solinas prime with a signed multi-term reduce), the BLS12-381 base field is a
*generic* 381-bit prime with no special low-Hamming-weight structure, so the
canonical reduce is **CIOS Montgomery** — exactly what blst's `mulx_mont_384`
does. We emit the same ADX/BMI2 CIOS shape:

## The CIOS algorithm (six iterations, dual carry chains)

The accumulator `T = (t0..t6)` (seven 64-bit words) starts at zero. For each
multiplier word `b[i]` (`i = 0..5`):

1. **Multiply-accumulate** `T += a · b[i]`: six memory-operand `MULX` of
   `a[j]·b[i]`, the low halves flowing up the **CF** chain (`ADCX`), the high
   halves up the **OF** chain (`ADOX`) — the independent dual chains that make
   the ADX idiom fast (`x86_ADCX` routed to CF for `adcx`, to OF for `adox`).
2. **Montgomery factor** `m = t0 · n′ (mod 2^64)`, `n′ = −p⁻¹ mod 2^64 =
   0x89f3fffcfffcfffd` (blst's `BLS12_381_p0`). Computed with `imul` (the low
   word of the product); `imul` writes flags, so it is issued between the two
   carry-chain phases with CF/OF freshly cleared on each side.
3. **Reduce** `T += m · p`, which makes the low word `t0` zero by construction
   (`m ≡ −t0·p⁻¹`, so `t0 + m·p ≡ 0 (mod 2^64)`); the carry propagates up and
   the window shifts down by one word (`tj ← t(j+1)`), again via the dual
   ADCX/ADOX chains.

After six iterations `T = a·b·R⁻¹ + k·p` for some `k < p`, so a final
conditional subtract of `p` (branch-free, gated on the trial-subtract borrow)
lands the result in `[0, p)`. The six output words are stored to `z[0..5]`.

## The modulus + Montgomery constant

* `p` little-endian limbs and `n′` are taken verbatim from blst's own
  `src/consts.c` (`BLS12_381_P`, `BLS12_381_p0`); `p` agrees with
  `CatCrypt.Util.BLS12381` (`0x1a0111ea…aaab`).

## What is proved / gated here

* `blsMontMulBlock_lowering_correct`: lowering the block to `Com (x86Dialect 64)`
  and denoting it on the init state equals `runBlock` on the source block — the
  owned backend's straight-line lowering is denotation-preserving across the
  `loadMem`/`mulxMem`/`adcx`/`adox`/`imul`/`add`/`sbb`/`cmovb`/`storeMem` mix.
* `blsMontMulAlloc_no_overflow`: the first-fit allocator assigns every register
  name a distinct pool register (no silent `%rax`-alias, the #380 class).
* The all-inputs byte-identity that the emitted stream computes
  `a·b·R⁻¹ (mod p)` is the external KAT (`bench/bls12381_fieldmul_compare`, vs
  blst `blst_fp_mul` and GMP `mod p` — the canonical-arithmetic oracle): the
  standard gate for these word kernels (per REV-12), over corner + random
  vectors. CIOS Montgomery's value-level correctness is a generic Montgomery
  identity; in-Lean it is a 384×384→768 SAT instance, infeasible, hence the
  external gate.

## Trust story

Identical to `JasminModel` / `X86Dialect` / `AsmPrinter`: the verified artifact
is `Com (x86Dialect 64) → runBlock → evalInstr`, the faithful transcription of
Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is the thin syntactic trust
boundary, and the SysV leaf prologue/epilogue is trusted ABI scaffolding
(`renderSysVLeafFn`) outside the verified body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
open CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc (graphColorAlloc linearScanValueAlloc
  valueRanges graphColorSpillCount graphColor_spillReload_sound)

/-! ## 1. The BLS12-381 modulus and Montgomery constant (canonical) -/

/-- `p` little-endian 64-bit limbs (blst `BLS12_381_P`, `src/consts.c`).
    Assembles to `0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`
    = `CatCrypt.Util.BLS12381`. -/
def pLimbs : List Nat :=
  [ 0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624
  , 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a ]

/-- `n′ = −p⁻¹ mod 2^64` (blst `BLS12_381_p0`, `src/consts.c`). -/
def nPrime : Nat := 0x89f3fffcfffcfffd

/-! ## 2. The CIOS body as a `List (JInstr 64)`

Register names (within the 15-GP budget):
* `z`/`x`/`y` — the result and operand base pointers (`z`→`%rdi`, `x`→`%rsi`,
  `y` arrives in `%rdx` and is moved to a free register in the prologue —
  `%rdx` is reserved for the `MULX`/`mulx` multiplier).
* `yd` — the running multiplier, pinned to `%rdx` (the implicit `MULX` src1);
  reloaded with `b[i]` (the `MAC` phase) then with the Montgomery factor
  `m = t0·n′ mod 2^64` (the reduce phase) per row.
* `t0..t6` — the seven-word CIOS accumulator window.
* `lo`/`hi` — the `MULX` product scratch (`hi` also stages the immediate `n′`
  and `p[j]` operands for the reduce, since `mulx` needs a register src2).
* `zr` — a zero register, used for the zero-extend carry folds and to clear
  CF/OF (`xor zr, zr`) between chains. -/

/-- One CIOS MAC step on column `j` (`0 < j < 6`): `mulx hi,lo = a[j]·yd`, then
    `adcx t_j ← lo` (CF chain) and `adox t_{j+1} ← hi` (OF chain). `tlo`/`thi`
    are the two accumulator window registers at significance `j` and `j+1`. -/
def macStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "yd") "x" (8 * j)
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS reduce step on column `j` (`0 < j < 6`): `mulx hi,lo = p[j]·m`
    (`yd` holds `m`), then — same positional structure as the MAC step — the low
    word adds at limb `j` (`adcx t_j ← lo`, CF chain) and the high word at limb
    `j+1` (`adox t_{j+1} ← hi`, OF chain). `p[j]` is an immediate, but `mulx`
    needs a register/mem src2, so `p[j]` is staged into `hi` first. The window is
    shifted down by one *after* the whole reduce (`t0` has become `≡ 0`). -/
def redStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mov "hi" (.imm (pLimbs[j]!))
  , .mulx "hi" "lo" (.reg "yd") (.reg "hi")
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS iteration on multiplier word `b[i]`.

    Phase A (MAC, `T += a·b[i]`): clear CF/OF, load `yd ← b[i]`, the first `MULX`
    `a[0]·b[i]` lands `(lo,hi)`; `adcx t0 ← lo`, `adox t1 ← hi`, then `macStep`
    for `j = 1..5`, finally fold the top carry into `t6` (`adcx t6 ← zr`,
    `adox t6 ← zr` reconciles both chains).

    Phase B (factor): the Montgomery factor `m = t0·n′ (mod 2^64)` is computed
    straight into the multiplier `yd` (=`%rdx`) so phase C needs no extra
    register: `yd ← t0`, then `yd ← yd·n′` (a 2-operand `imul` low word, `n′`
    staged in `hi` because the full 64-bit constant does not fit a 3-operand
    `imul` immediate; `imul` clobbers flags so it sits between the cleared
    chains).

    Phase C (reduce, `T += m·p`, then shift down): clear CF/OF; the first
    `mulx p[0]·m` adds into `t0` (`adcx t0 ← lo` — `t0` becomes `≡ 0 (mod 2^64)`
    by the choice of `m`), `adox t1 ← hi`; then `redStep` for `j = 1..5`
    accumulates `p[j]·m`'s low at limb `j` and high at limb `j+1` (same positional
    structure as the MAC step). After the reduce `t0` is a spent carry source, so
    a six-`mov` rotation `t0←t1, …, t5←t6, t6←0` shifts the window down by one
    word, keeping the block a flat concrete list with fixed register names. -/
def ciosIter (i : Nat) : List (JInstr 64) :=
  -- Phase A: MAC  T += a·b[i]
  [ .xor_ "zr" (.reg "zr")          -- clear CF and OF
  , .loadMem "yd" "y" (8 * i)
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi") ]
  ++ macStep "t1" "t2" 1
  ++ macStep "t2" "t3" 2
  ++ macStep "t3" "t4" 3
  ++ macStep "t4" "t5" 4
  ++ macStep "t5" "t6" 5
  ++ [ .adcx "t6" (.reg "zr"), .adox "t6" (.reg "zr") ]
  -- Phase B: m = t0 * n' mod 2^64, computed straight into the multiplier yd
  -- (=%rdx) so phase C needs no separate `m` register. The 64-bit `n′` does not
  -- fit a 3-operand `imul` immediate, so it is staged into the `hi` scratch and
  -- folded by a 2-operand `imul` (low word).
  ++ [ .mov "yd" (.reg "t0"), .mov "hi" (.imm nPrime), .imul "yd" (.reg "hi") ]
  -- Phase C: reduce  T += m*p ; t0 cancels; window shifts down
  ++ [ .xor_ "zr" (.reg "zr")
     , .mov "hi" (.imm (pLimbs[0]!))
     , .mulx "hi" "lo" (.reg "yd") (.reg "hi")
     , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi") ]
  ++ redStep "t1" "t2" 1
  ++ redStep "t2" "t3" 2
  ++ redStep "t3" "t4" 3
  ++ redStep "t4" "t5" 4
  ++ redStep "t5" "t6" 5
  ++ [ .adcx "t6" (.reg "zr"), .adox "t6" (.reg "zr")
     -- window shift: t0←t1, t1←t2, …, t5←t6, t6←0
     , .mov "t0" (.reg "t1"), .mov "t1" (.reg "t2"), .mov "t2" (.reg "t3")
     , .mov "t3" (.reg "t4"), .mov "t4" (.reg "t5"), .mov "t5" (.reg "t6")
     , .mov "t6" (.imm 0) ]

/-- The final branch-free conditional subtract of `p` and store of the six
    result words to `z[0..5]`. After six CIOS iterations the accumulator
    `t0..t5` holds a value in `[0, 2p)`; trial-subtract `p` (immediates) staging
    each trial word in the stack scratch frame `sp[0..5]` (the `t6` high word
    participates in the borrow so a top-word carry-out is handled). If the final
    borrow `CF = 1` (i.e. `t < p`) `cmovb` keeps the original `tj`; else `CF = 0`
    (`t ≥ p`) the trial word in scratch is kept. The trial is staged to `sp`
    rather than a second register set so the kernel stays within the 14-GP pool
    (the accumulator `t0..t6` + `lo`/`hi`/`zr` scratch already fill the pool). -/
def blsFinalReduce : List (JInstr 64) :=
  -- trial = (t0..t5, t6) - (p, 0); stage each trial word in scratch sp[0..5].
  [ .mov "lo" (.reg "t0"), .mov "hi" (.imm (pLimbs[0]!)), .sub "lo" (.reg "hi"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.reg "t1"), .mov "hi" (.imm (pLimbs[1]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.reg "t2"), .mov "hi" (.imm (pLimbs[2]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.reg "t3"), .mov "hi" (.imm (pLimbs[3]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 24 (.reg "lo")
  , .mov "lo" (.reg "t4"), .mov "hi" (.imm (pLimbs[4]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 32 (.reg "lo")
  , .mov "lo" (.reg "t5"), .mov "hi" (.imm (pLimbs[5]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 40 (.reg "lo")
  , .sbb "t6" (.imm 0)   -- top word; CF = final borrow; CF=1 ⇒ t < p ⇒ keep originals
  -- select: load trial into hi, cmovb original (tj) over it when CF=1, store to z.
  , .loadMem "hi" "sp" 0,  .cmovb "hi" (.reg "t0"), .storeMem "z" 0  (.reg "hi")
  , .loadMem "hi" "sp" 8,  .cmovb "hi" (.reg "t1"), .storeMem "z" 8  (.reg "hi")
  , .loadMem "hi" "sp" 16, .cmovb "hi" (.reg "t2"), .storeMem "z" 16 (.reg "hi")
  , .loadMem "hi" "sp" 24, .cmovb "hi" (.reg "t3"), .storeMem "z" 24 (.reg "hi")
  , .loadMem "hi" "sp" 32, .cmovb "hi" (.reg "t4"), .storeMem "z" 32 (.reg "hi")
  , .loadMem "hi" "sp" 40, .cmovb "hi" (.reg "t5"), .storeMem "z" 40 (.reg "hi") ]

/-- The full CIOS Montgomery multiply body: zero the accumulator, six CIOS
    iterations, then the final conditional subtract + store. A concrete flat
    `List (JInstr 64)` the lowering / allocation lemmas chew on. -/
def blsMontMulBlock : List (JInstr 64) :=
  -- zero the accumulator t0..t6 and the zero register
  [ .mov "zr" (.imm 0)
  , .mov "t0" (.imm 0), .mov "t1" (.imm 0), .mov "t2" (.imm 0)
  , .mov "t3" (.imm 0), .mov "t4" (.imm 0), .mov "t5" (.imm 0), .mov "t6" (.imm 0) ]
  ++ (List.range 6).flatMap ciosIter
  ++ blsFinalReduce

/-! ## 3. The initial machine state (reg-ptr ABI)

`x`/`y`/`z` hold the buffer base addresses (modeled as register names). The
operand words live in memory at `[x + 8·i]`, `[y + 8·i]`; we seed `a0..a5`,
`b0..b5` at offsets `0,8,…,40`. -/

/-- Build the init state from the twelve operand limbs. -/
def initState (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "x" then
        if off = 0 then a0 else if off = 8 then a1 else if off = 16 then a2
        else if off = 24 then a3 else if off = 32 then a4 else if off = 40 then a5
        else 0
      else if base = "y" then
        if off = 0 then b0 else if off = 8 then b1 else if off = 16 then b2
        else if off = 24 then b3 else if off = 32 then b4 else if off = 40 then b5
        else 0
      else 0 }

/-! ## 4. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the CIOS block.** Lowering to `Com (x86Dialect 64)`
    and denoting on the init state equals `runBlock` on the source block — the
    owned backend's straight-line lowering is denotation-preserving across the
    full `loadMem`/`mulxMem`/`mulx`/`adcx`/`adox`/`imul`/`add`/`sbb`/`cmovb`/
    `storeMem` mix. -/
theorem blsMontMulBlock_lowering_correct
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : BitVec 64) :
    (lowerBlock (Γ := []) blsMontMulBlock).denote
        (.cons (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5) .nil)
      = runBlock (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5) blsMontMulBlock :=
  lowerBlock_denote_closed blsMontMulBlock
    (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5)

/-! ## 5. Constant time: straight-line, all-direct addressing

Every instruction of the CIOS body addresses memory through a base pointer and
a compile-time-constant displacement (`loadMem`/`storeMem`/`mulxMem`); the
final reduce is branch-free (`cmovb`), so no `loadMemIdx`/`storeMemIdx`
appears and the decidable `allDirect` check carries the block into
`ConstantTimeCoverage.allDirect_constant_time`. -/

/-- One CIOS MAC step uses only direct base+displacement addressing, for every
    column index. -/
theorem macStep_allDirect (tlo thi : String) (j : Nat) :
    allDirect (macStep tlo thi j) = true := rfl

/-- One CIOS reduce step uses only direct base+displacement addressing, for
    every column index. -/
theorem redStep_allDirect (tlo thi : String) (j : Nat) :
    allDirect (redStep tlo thi j) = true := rfl

/-- One CIOS iteration uses only direct base+displacement addressing, for every
    multiplier-word index. -/
theorem ciosIter_allDirect (i : Nat) : allDirect (ciosIter i) = true := rfl

/-- The final conditional subtract uses only direct base+displacement
    addressing. -/
theorem blsFinalReduce_allDirect : allDirect blsFinalReduce = true := rfl

/-- The whole CIOS Montgomery multiply body uses only direct base+displacement
    addressing (no secret-indexed memory access). Proved by splitting the body
    at its two concatenations and the iteration `flatMap`, so the cost is the
    per-piece checks rather than a reduction of the assembled block. -/
theorem blsMontMulBlock_allDirect : allDirect blsMontMulBlock = true := by
  simp only [blsMontMulBlock, allDirect, List.all_append, List.all_flatMap,
    Bool.and_eq_true]
  exact ⟨⟨rfl, List.all_eq_true.mpr fun i _ => ciosIter_allDirect i⟩,
    blsFinalReduce_allDirect⟩

/-- **Constant time.** The emitted BLS12-381 Montgomery multiply produces the
    same machine leakage trace from any two starting states: its observable
    control-flow + memory-address sequence is a function of the program text
    alone, so it carries no information about the operand limbs. -/
theorem blsMontMulBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ blsMontMulBlock = blockLeak s₂ blsMontMulBlock :=
  allDirect_constant_time blsMontMulBlock blsMontMulBlock_allDirect s₁ s₂

/-! ## 6. AT&T assembly emission (reg-ptr ABI + small stack scratch frame)

The kernel pins `z`→`%rdi`, `x`→`%rsi`, the running multiplier `yd`→`%rdx`
(the `MULX` implicit src1), and the scratch-frame base `sp`→`%rbp` (excluded
from `gpPool`, so it costs no pool slot — the same recovery `Fe25519MulKernel`
and `P384FieldKernel` use). The `y`-pointer argument arrives in `%rdx` and is
moved to a free register in the prologue. The 48-byte scratch frame holds the
final conditional-subtract trial words. The body is `runBlock`-verified; the
prologue/epilogue are trusted ABI scaffolding. -/

/-- Pin pointers + the `MULX` multiplier `yd`→`%rdx` + scratch base `sp`→`%rbp`. -/
def blsMontMulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def blsMontMulAlloc : GpAlloc := allocGp blsMontMulPinned blsMontMulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias,
    the #380 class). -/
theorem blsMontMulAlloc_no_overflow :
    allocOverflow blsMontMulPinned blsMontMulBlock = none := by native_decide

/-- The rendered AT&T body (one line per `JInstr`). -/
def blsMontMulAsmBody : List String := renderBlockBody blsMontMulAlloc blsMontMulBlock

/-- The full emitted leaf `bls12381_mont_mul_x86_from_lean(z, x, y)`. The
    prologue saves callee regs, carves a 64-byte scratch frame, points `%rbp`
    at it, and moves the `y` pointer out of `%rdx`. Frame alloc/restore is
    trusted ABI scaffolding outside the `runBlock`-verified body. -/
def blsMontMulAsm : String :=
  renderLeafFn "bls12381_mont_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $64, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf blsMontMulAlloc "y" ]
    blsMontMulAsmBody
    [ "\taddq $64, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/- Shape check: the emitted asm contains the dual carry-chain CIOS idiom
    (`mulx`, `adcx`, `adox`, `imul` for the Montgomery factor), the
    memory-operand `MULX` reads the multiplicand from `[x]` (`mulxq 0(%rsi)`),
    the result stores print in AT&T form (`(%rdi)`), and the `%rdx`-pinned
    multiplier is the `MULX` src1. -/
#guard (hasSub blsMontMulAsm "mulx") && (hasSub blsMontMulAsm "adcx") && (hasSub blsMontMulAsm "adox") && (hasSub blsMontMulAsm "imul") && (hasSub blsMontMulAsm "mulxq 0(%rsi)") && (hasSub blsMontMulAsm "(%rdi)") && (hasSub blsMontMulAsm "src1=%rdx")

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/bls12381_fieldmul_compare/gen_com/bls12381_mont_mul_x86_from_lean.s"
    blsMontMulAsm
  IO.println "wrote gen_com/bls12381_mont_mul_x86_from_lean.s (in-Lean x86 backend CIOS, no jasminc)"

/-! ## 7. Graph-coloring register allocation — the pairing-tower pressure case (gap #2)

The hand-authored CIOS body keeps `z`/`x`/`yd`/`sp` pinned and the seven-word accumulator
window `t0..t6` plus the `lo`/`hi`/`zr` scratch in registers. It has **11 distinct value
names whose PEAK SIMULTANEOUS liveness is 11** (all eleven are live together during the
carry-chain — verified by `blsMontMul_pressure_exceeds_pool`): this is the
register-pressure-bound BLS12-381 `Fp`-multiply leg of the pairing tower, the documented
#259/#474 regalloc wall. (Contrast BN254 — peak 9, fits — and the 4×4 schoolbook
`bignum_mul_4_8` — peak 8, fits — which are pure no-ops for any spiller.)

**Production fit vs the spilling-discipline win.** The shipped leaf (`blsMontMulAsm`,
first-fit `allocGp blsMontMulPinned`) does NOT reserve the two working registers, so its
pool is the full **11** non-pinned GP registers and it places all 11 peak-live names
*without spilling* — graph coloring is a no-op there. The interesting case is the
**spilling discipline** the verified `SpillingRegAlloc`/`GraphColoringRegAlloc` passes
impose: they reserve `%r14`/`%r15` as reload working registers (so a spill always has a
landing register), shrinking the pool to 8 and FORCING a 3-name spill on this 11-peak
body. On that forced-spill comparison the two allocators diverge:

`SpillingRegAlloc.linearScan`'s farthest-end eviction spills the **hot** `MULX` product
scratch `hi` (reloaded on every column of every row — its live range ends far, so the
farthest-end tie-break evicts it) alongside the window words `t4`/`t5`, producing **390**
spill-traffic instructions (196 reloads + 194 stores). `graphColorAlloc`'s use-density
spill cost instead keeps the hot `hi`/`lo` resident and spills only the **cold** window
words `t0`/`t4`/`t5` (each used few times before the window rotation overwrites it),
cutting the traffic to **165** (84 reloads + 81 stores) — **0.42×**. The output is a
drop-in `List (String × Slot)`, materialized by the same allocation-agnostic
`spillReloadBlock` and proved transparent by the same per-spill checker
(`graphColor_spillReload_sound`); only the spill *choice* differs.

**What the MCA gate does and does not show.** On the deterministic llvm-mca gate the gc leaf
has 587 instructions vs the linear-scan leaf's 812 (the 225-instruction reload-traffic
delta), and TotalCyc/iter drops 300.63 → 270.09 (**0.90×**) — gc shaves the reload
latency. But the throughput-bound `BlockRThroughput` is **229.8 for both (1.00×)**: this
leaf is bound by the dual-carry **MULX/ADCX/ADOX multiply ports**, not by the spill
traffic, so the extra reload `movq`s fill otherwise-idle load-port slots without raising
the port-pressure lower bound. The global allocator converts the register residual to
fewer instructions and lower latency-fill, but it does NOT move this kernel's throughput
ceiling — unlike the whole-program-live Keccak (RThru 0.67×) and the ALU-bound SHA round
(RThru 0.86×), where the spill traffic WAS on the binding port and gc drops RThru itself.
-/

/-- The graph-coloring spill base — the same `%rbp` stack frame the final-reduce scratch
    `sp` hangs off, but the gc spill cells are allocated from offset `48` upward
    (`gcFrameBase`), disjoint from the final-reduce trial words `sp[0..40]`, so a spilled
    value's cell never aliases a trial word. The base register `gcfp` is bound to `%rbp`
    in `gcResidentAlloc` (same physical frame pointer as `sp`). -/
def gcSpillBase : String := "gcfp"

/-- The byte offset the gc spill cells start at — above the 48-byte final-reduce scratch
    `sp[0..40]`, so the two regions are disjoint within the single `%rbp` frame. -/
def gcFrameBase : Int := 48

/-- The pins the graph-coloring allocator runs against. Beyond the four ABI/scratch pins
    `blsMontMulPinned` fixes, the read-only multiplier-source base `y` (which arrives in
    `%rdx`, moved out in the prologue, and is never written so the value allocator does
    not place it) is pinned to a free pool register `%rcx`, so the rendered body resolves
    its base operand. The remaining 8 pool registers carry the value names. -/
def blsMontMulGcPinned : GpAlloc := blsMontMulPinned ++ [("y", "%rcx")]

/-- **The graph-coloring spill/placement decisions** for the BLS CIOS body — the gap-#2
    global allocator over the same pool the linear scan uses. Drop-in
    `List (String × Slot)`. -/
def blsMontMulGcDecisions : List (String × Slot) :=
  graphColorAlloc blsMontMulGcPinned gcFrameBase blsMontMulBlock

/-- The (value-restricted) linear-scan decisions on the SAME names + pool, the baseline
    the graph-coloring win is measured against. -/
def blsMontMulLsDecisions : List (String × Slot) :=
  linearScanValueAlloc blsMontMulGcPinned gcFrameBase blsMontMulBlock

/-- The number of `valueRanges` simultaneously live at program point `idx` — the live
    set covering that point. The max over all points is the true peak register pressure
    (the chromatic-relevant quantity, ≥ which no spill-free allocation exists). -/
def liveAt (idx : Nat) : Nat :=
  ((valueRanges blsMontMulBlock).filter
    (fun lr => lr.defIdx ≤ idx ∧ idx ≤ lr.lastUse)).length

/-- The **peak simultaneous register pressure**: the max live-set size over all program
    points. For the BLS CIOS body this is 11 — all eleven value names are live together
    during the carry-chain. -/
def peakLive : Nat :=
  (List.range blsMontMulBlock.length).foldl (fun m i => max m (liveAt i)) 0

/-- **Peak simultaneous register pressure is 11** — all eleven value names of the CIOS
    body are live together at some program point (the carry-chain), so no spill-free
    allocation exists in fewer than 11 registers. This is the pairing-tower
    register-pressure wall (#259/#474): the shipped first-fit leaf fits because it uses
    the full 11-register GP allocation (no reserved working registers); the verified
    spilling discipline reserves `%r14`/`%r15` (→ 8-register pool) and so FORCES a 3-name
    spill, the case on which graph coloring beats linear scan. (Contrast BN254 peak 9,
    bignum_mul_4_8 peak 8 — both fit, pure no-ops.) -/
theorem blsMontMul_pressure_exceeds_pool :
    peakLive = 11 ∧ (allocPool blsMontMulGcPinned).length < peakLive := by
  native_decide

/-- **The spill SET differs**: graph coloring evicts the cold window words `t0`/`t4`/`t5`;
    the linear scan evicts the hot `MULX` scratch `hi` (farthest-ending) plus `t4`/`t5` —
    a different, cheaper-traffic assignment on the same body and pool. -/
theorem blsMontMul_gc_decisions_differ :
    blsMontMulGcDecisions ≠ blsMontMulLsDecisions := by native_decide

/-- **Graph coloring inserts strictly fewer spill reloads** than the linear scan on the
    BLS CIOS body, on the same names and pool. The farthest-end rule spills the hot
    `hi` scratch (reloaded on every column); use-density keeps it resident and spills the
    cold window words. (Concrete: graph-color 84 vs linear-scan 196 reloads.) -/
theorem blsMontMul_gc_fewer_reloads :
    reloadCount blsMontMulGcDecisions gcSpillBase blsMontMulBlock
      < reloadCount blsMontMulLsDecisions gcSpillBase blsMontMulBlock := by native_decide

/-- **Graph coloring's total spill traffic is strictly lower** (reloads + stores):
    graph-color 165 vs linear-scan 390, a `0.42×` ratio — the pairing-tower register
    residual this kernel converts to a recompile win. -/
theorem blsMontMul_gc_less_traffic :
    reloadCount blsMontMulGcDecisions gcSpillBase blsMontMulBlock
      + storeCount blsMontMulGcDecisions gcSpillBase blsMontMulBlock
    < reloadCount blsMontMulLsDecisions gcSpillBase blsMontMulBlock
      + storeCount blsMontMulLsDecisions gcSpillBase blsMontMulBlock := by native_decide

/-- **Graph-coloring spill soundness for the BLS Montgomery multiply.** The materialized
    block `spillReloadBlock blsMontMulGcDecisions gcSpillBase blsMontMulBlock` denotes the
    original CIOS body on the canonical run — each spilled name's store/use/reload
    sandwich is a no-op under the `SpillValid` invariant. This is the graph-coloring entry
    to the SAME allocation-agnostic checker the linear-scan path uses; the heuristic
    changed, the soundness did not. -/
theorem blsMontMulGc_spillReload_sound {sb : String} {off : Int} {r : String}
    {s : JState 64} (mid : List (JInstr 64)) (rest : List (JInstr 64))
    (hmid : SpillValid sb off r (runBlock (evalInstr s (.storeMem sb off (.reg r))) mid)) :
    runBlock s (.storeMem sb off (.reg r) :: (mid ++ .loadMem r sb off :: rest))
      = runBlock s (.storeMem sb off (.reg r) :: (mid ++ rest)) :=
  graphColor_spillReload_sound mid rest hmid

/-- The materialized graph-coloring block's length = original + reloads + stores
    (`spillReloadBlock_length`). -/
theorem blsMontMulGc_spilledLength :
    (spillReloadBlock blsMontMulGcDecisions gcSpillBase blsMontMulBlock).length
      = blsMontMulBlock.length
        + reloadCount blsMontMulGcDecisions gcSpillBase blsMontMulBlock
        + storeCount blsMontMulGcDecisions gcSpillBase blsMontMulBlock :=
  spillReloadBlock_length _ _ _

/-! ### Emit the graph-coloring-allocated BLS `Fp`-mul leaf for the MCA gate

The resident names are bound to their pool registers; the two cold spilled window words
get reload/store traffic against the `gcSpillBase` frame. The same `renderJInstrSpilled`
per-program-point realisation the SHA-256 / X25519 spilled emits use. -/

/-- The resident register allocation for the graph-coloring decisions: the pins plus each
    name graph coloring placed in a pool register. -/
def gcResidentAlloc : GpAlloc :=
  blsMontMulGcPinned ++ [(gcSpillBase, "%rbp")]
    ++ (blockNames blsMontMulBlock).filterMap (fun n =>
    match blsMontMulGcDecisions.lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The graph-coloring resident allocation never binds a non-pinned name to a reserved
    working register `%r14`/`%r15` (the reload scratch) — so a reload never clobbers a
    live resident value. -/
theorem gcResidentAlloc_avoids_working :
    gcResidentAlloc.all (fun p => p.2 != "%r14" && p.2 != "%r15") = true := by
  native_decide

/-- The graph-coloring spill slot for a name, if spilled (the pinned pointers/scratch
    base are never spilled — they are `valueRanges`-excluded read targets). -/
def gcSpilledMaterialised (n : String) : Option Int :=
  if n == "z" || n == "x" || n == "yd" || n == "sp" || n == "y" then none
  else spillSlotOf blsMontMulGcDecisions n

/-- The per-instruction `SpillView` under the graph-coloring allocation. -/
def gcViewOf (i : JInstr 64) : AsmPrinter.SpillView where
  resident := gcResidentAlloc
  frameBase := gcSpillBase
  spilledReads := (readNames i).filterMap (fun n =>
    (gcSpilledMaterialised n).map (fun off => (n, off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (gcSpilledMaterialised n).map (fun off => (n, off)))

/-- The graph-coloring-allocated BLS CIOS body, rendered line-by-line. -/
def gcBodyLines : List String :=
  blsMontMulBlock.flatMap (fun i => AsmPrinter.renderJInstrSpilled (gcViewOf i) i)

/-- **No `<UNALLOCATED>` sentinel under the graph-coloring allocation** — every name is
    placed (resident or spilled-and-reloaded). -/
theorem gcBodyLines_no_unallocated :
    (gcBodyLines.any (fun l => (l.splitOn "UNALLOCATED").length > 1)) = false := by
  native_decide

/-- The full graph-coloring-allocated BLS `Fp`-mul leaf. The prologue carves a 64-byte
    final-reduce scratch (`%rbp`) and a separate spill frame the spilled window words
    hang off; the body is the RA-materialised CIOS. -/
def gcMontMulAsm : String :=
  renderLeafFn "bls12381_mont_mul_gc_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $128, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf gcResidentAlloc "y" ]
    gcBodyLines
    [ "\taddq $128, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/- Shape check on the graph-coloring leaf: one labelled function carrying the CIOS
    arithmetic (`mulx`/`adcx`/`adox`/`imul`) and the (fewer) reload/store traffic. -/
#guard (hasSub gcMontMulAsm "bls12381_mont_mul_gc_x86_from_lean") && (hasSub gcMontMulAsm "adcx") && (hasSub gcMontMulAsm "adox")

/-! ### The linear-scan baseline leaf — the apples-to-apples MCA comparand

The same render path over the (value-restricted) linear-scan decisions, so the MCA gate
compares the two allocators on an identical body/pool — the only difference is which
names spill (and so how much reload traffic the rendered leaf carries). -/

/-- The resident register allocation for the linear-scan decisions (mirror of
    `gcResidentAlloc`). -/
def lsResidentAlloc : GpAlloc :=
  blsMontMulGcPinned ++ [(gcSpillBase, "%rbp")]
    ++ (blockNames blsMontMulBlock).filterMap (fun n =>
    match blsMontMulLsDecisions.lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The linear-scan spill slot for a name (mirror of `gcSpilledMaterialised`). -/
def lsSpilledMaterialised (n : String) : Option Int :=
  if n == "z" || n == "x" || n == "yd" || n == "sp" || n == "y" then none
  else spillSlotOf blsMontMulLsDecisions n

/-- The per-instruction `SpillView` under the linear-scan allocation. -/
def lsViewOf (i : JInstr 64) : AsmPrinter.SpillView where
  resident := lsResidentAlloc
  frameBase := gcSpillBase
  spilledReads := (readNames i).filterMap (fun n =>
    (lsSpilledMaterialised n).map (fun off => (n, off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (lsSpilledMaterialised n).map (fun off => (n, off)))

/-- The linear-scan-allocated BLS CIOS body, rendered line-by-line. -/
def lsBodyLines : List String :=
  blsMontMulBlock.flatMap (fun i => AsmPrinter.renderJInstrSpilled (lsViewOf i) i)

/-- **No `<UNALLOCATED>` sentinel under the linear-scan allocation** either. -/
theorem lsBodyLines_no_unallocated :
    (lsBodyLines.any (fun l => (l.splitOn "UNALLOCATED").length > 1)) = false := by
  native_decide

/-- **The graph-coloring body renders strictly fewer lines than the linear-scan body** —
    the emit-level form of the traffic win (fewer reloads ⇒ fewer rendered lines). -/
theorem gcBodyLines_shorter : gcBodyLines.length < lsBodyLines.length := by native_decide

/-- The full linear-scan-spilled BLS `Fp`-mul leaf (the MCA comparand). -/
def lsMontMulAsm : String :=
  renderLeafFn "bls12381_mont_mul_ls_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $128, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf lsResidentAlloc "y" ]
    lsBodyLines
    [ "\taddq $128, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write BOTH RA-spilled BLS `Fp`-mul leaves for the deterministic MCA gate
    (`bls12381_mont_mul_gc` = graph-coloring use-density spill, `bls12381_mont_mul_ls` =
    spill-blind linear-scan), plus the first-fit pool-resident leaf for the existing C
    KAT harness. The gc/ls leaves share the body and pool — only the spill choice differs,
    so the MCA RThru delta isolates the allocator. -/
def emitGcMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/bls12381_fieldmul_compare/gen_com/bls12381_mont_mul_x86_from_lean.s"
    blsMontMulAsm
  IO.FS.writeFile
    "bench/bls12381_fieldmul_compare/gen_com/bls12381_mont_mul_gc_x86_from_lean.s"
    gcMontMulAsm
  IO.FS.writeFile
    "bench/bls12381_fieldmul_compare/gen_com/bls12381_mont_mul_ls_x86_from_lean.s"
    lsMontMulAsm
  IO.println "wrote gen_com/bls12381_mont_mul_{,gc_,ls_}x86_from_lean.s (first-fit / graph-coloring / linear-scan BLS Fp-mul)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel
