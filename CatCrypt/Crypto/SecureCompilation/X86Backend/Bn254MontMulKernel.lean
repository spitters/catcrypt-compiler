/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# BN254 `Fp` Montgomery field-multiply, lowered through the in-Lean x86 backend

This module emits the BN254 (alt-bn128) base-field
(`p = 0x30644e72…fd47`, 254 bits, four 64-bit limbs) Montgomery multiply

    mont_mul(a, b) = a · b · R⁻¹ (mod p),   R = 2^256,

through the SAME owned x86 backend (`JasminModel.runBlock` /
`X86Dialect.lowerBlock_denote` / `AsmPrinter`, no jasminc) used for the
BLS12-381 (`Bls12381MontMulKernel`), `bignum_mul_4_8`, and `fe25519` kernels,
framed by the principled SysV ABI layer (`renderSysVLeafFn`, #464). It is the
BN254 analog of the BLS12-381 field-multiply (#490): four CIOS iterations
instead of six.

BN254 was the one production curve whose `Fp` multiply still **adopted** an
external fiat/bedrock2 Montgomery tower (per the #489 cross-curve audit,
`bench/CROSS_CURVE_AUDIT.md`) while the sibling curves emit their own ADX
field-mul. Own-emitting it makes the whole BN254 `G1` group law
(`Pairing/BN254GroupEmit.lean`) own-emitted end-to-end down to the field
multiply, subtract, and (already #488/#489) the divstep inverse.

Like BLS12-381, the BN254 base field is a *generic* 254-bit prime with no
special low-Hamming-weight structure, so the canonical reduce is **CIOS
Montgomery** with the ADX/BMI2 MULX + dual ADCX/ADOX carry-chain idiom.

## The CIOS algorithm (four iterations, dual carry chains)

The accumulator `T = (t0..t4)` (five 64-bit words) starts at zero. For each
multiplier word `b[i]` (`i = 0..3`):

1. **Multiply-accumulate** `T += a · b[i]`: four memory-operand `MULX` of
   `a[j]·b[i]`, the low halves flowing up the **CF** chain (`ADCX`), the high
   halves up the **OF** chain (`ADOX`) — the independent dual chains that make
   the ADX idiom fast.
2. **Montgomery factor** `m = t0 · n′ (mod 2^64)`, `n′ = −p⁻¹ mod 2^64 =
   0x87d20782e4866389` (arkworks/gnark `INV`). Computed with `imul` (the low
   word of the product); `imul` writes flags, so it is issued between the two
   carry-chain phases with CF/OF freshly cleared on each side.
3. **Reduce** `T += m · p`, which makes the low word `t0` zero by construction
   (`m ≡ −t0·p⁻¹`, so `t0 + m·p ≡ 0 (mod 2^64)`); the carry propagates up and
   the window shifts down by one word (`tj ← t(j+1)`), again via the dual
   ADCX/ADOX chains.

After four iterations `T = a·b·R⁻¹ + k·p` for some `k < p`, so a final
conditional subtract of `p` (branch-free, gated on the trial-subtract borrow)
lands the result in `[0, p)`. The four output words are stored to `z[0..3]`.

## The modulus + Montgomery constant (canonical sources)

* `p` little-endian limbs are the alt-bn128 base-field prime
  (`CatCrypt.Util.BN254Verified.BN254`,
  `21888242871839275222246405745257275088696311157297823662689037894645226208583`).
* `n′ = −p⁻¹ mod 2^64 = 0x87d20782e4866389` is the standard arkworks-bn254 /
  gnark Montgomery `INV` constant (`p · n′ + 1 ≡ 0 (mod 2^64)`).

## What is proved / gated here

* `bn254MontMulBlock_lowering_correct`: lowering the block to `Com (x86Dialect 64)`
  and denoting it on the init state equals `runBlock` on the source block — the
  owned backend's straight-line lowering is denotation-preserving across the
  `loadMem`/`mulxMem`/`adcx`/`adox`/`imul`/`add`/`sbb`/`cmovb`/`storeMem` mix.
* `bn254MontMulAlloc_no_overflow`: the first-fit allocator assigns every register
  name a distinct pool register (no silent `%rax`-alias, the #380 class).
* The all-inputs byte-identity that the emitted stream computes
  `a·b·R⁻¹ (mod p)` is the external KAT (`bench/bn254_fieldmul_compare`, vs GMP
  `mod p` — the canonical-arithmetic oracle; blst does NOT implement BN254): the
  standard gate for these word kernels (per REV-12), over corner + random
  vectors. CIOS Montgomery's value-level correctness is a generic Montgomery
  identity; in-Lean it is a 256×256→512 SAT instance, infeasible, hence the
  external gate.

## Trust story

Identical to `JasminModel` / `X86Dialect` / `AsmPrinter`: the verified artifact
is `Com (x86Dialect 64) → runBlock → evalInstr`, the faithful transcription of
Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is the thin syntactic trust
boundary, and the SysV leaf prologue/epilogue is trusted ABI scaffolding
(`renderSysVLeafFn`) outside the verified body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bn254MontMulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. The BN254 modulus and Montgomery constant (canonical) -/

/-- `p` little-endian 64-bit limbs (alt-bn128 base field
    `0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`,
    = `CatCrypt.Util.BN254Verified.BN254`). -/
def pLimbs : List Nat :=
  [ 0x3c208c16d87cfd47, 0x97816a916871ca8d
  , 0xb85045b68181585d, 0x30644e72e131a029 ]

/-- `n′ = −p⁻¹ mod 2^64` (arkworks-bn254 / gnark Montgomery `INV`).
    Satisfies `p · n′ + 1 ≡ 0 (mod 2^64)`. -/
def nPrime : Nat := 0x87d20782e4866389

/-! ## 2. The CIOS body as a `List (JInstr 64)`

Register names (within the 14-GP budget — fewer than BLS, four-limb window):
* `z`/`x`/`y` — the result and operand base pointers (`z`→`%rdi`, `x`→`%rsi`,
  `y` arrives in `%rdx` and is moved to a free register in the prologue —
  `%rdx` is reserved for the `MULX`/`mulx` multiplier).
* `yd` — the running multiplier, pinned to `%rdx` (the implicit `MULX` src1);
  reloaded with `b[i]` (the `MAC` phase) then with the Montgomery factor
  `m = t0·n′ mod 2^64` (the reduce phase) per row.
* `t0..t4` — the five-word CIOS accumulator window.
* `lo`/`hi` — the `MULX` product scratch (`hi` also stages the immediate `n′`
  and `p[j]` operands for the reduce, since `mulx` needs a register src2).
* `zr` — a zero register, used for the zero-extend carry folds and to clear
  CF/OF (`xor zr, zr`) between chains. -/

/-- One CIOS MAC step on column `j` (`0 < j < 4`): `mulx hi,lo = a[j]·yd`, then
    `adcx t_j ← lo` (CF chain) and `adox t_{j+1} ← hi` (OF chain). -/
def macStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "yd") "x" (8 * j)
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS reduce step on column `j` (`0 < j < 4`): `mulx hi,lo = p[j]·m`
    (`yd` holds `m`), then — same positional structure as the MAC step — the low
    word adds at limb `j` (`adcx t_j ← lo`, CF chain) and the high word at limb
    `j+1` (`adox t_{j+1} ← hi`, OF chain). `p[j]` is an immediate, but `mulx`
    needs a register/mem src2, so `p[j]` is staged into `hi` first. -/
def redStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mov "hi" (.imm (pLimbs[j]!))
  , .mulx "hi" "lo" (.reg "yd") (.reg "hi")
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS iteration on multiplier word `b[i]`.

    Phase A (MAC, `T += a·b[i]`): clear CF/OF, load `yd ← b[i]`, the first `MULX`
    `a[0]·b[i]` lands `(lo,hi)`; `adcx t0 ← lo`, `adox t1 ← hi`, then `macStep`
    for `j = 1..3`, finally fold the top carry into `t4` (`adcx t4 ← zr`,
    `adox t4 ← zr` reconciles both chains).

    Phase B (factor): `m = t0·n′ (mod 2^64)` computed straight into `yd`
    (=`%rdx`) so phase C needs no extra register: `yd ← t0`, then `yd ← yd·n′`
    (a 2-operand `imul` low word, `n′` staged in `hi`; `imul` clobbers flags so
    it sits between the cleared chains).

    Phase C (reduce, `T += m·p`, then shift down): clear CF/OF; the first
    `mulx p[0]·m` adds into `t0` (`adcx t0 ← lo` — `t0` becomes `≡ 0 (mod 2^64)`
    by the choice of `m`), `adox t1 ← hi`; then `redStep` for `j = 1..3`; the
    four-`mov` rotation `t0←t1, …, t3←t4, t4←0` shifts the window down. -/
def ciosIter (i : Nat) : List (JInstr 64) :=
  -- Phase A: MAC  T += a·b[i]
  [ .xor_ "zr" (.reg "zr")          -- clear CF and OF
  , .loadMem "yd" "y" (8 * i)
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi") ]
  ++ macStep "t1" "t2" 1
  ++ macStep "t2" "t3" 2
  ++ macStep "t3" "t4" 3
  ++ [ .adcx "t4" (.reg "zr"), .adox "t4" (.reg "zr") ]
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
  ++ [ .adcx "t4" (.reg "zr"), .adox "t4" (.reg "zr")
     -- window shift: t0←t1, t1←t2, t2←t3, t3←t4, t4←0
     , .mov "t0" (.reg "t1"), .mov "t1" (.reg "t2"), .mov "t2" (.reg "t3")
     , .mov "t3" (.reg "t4"), .mov "t4" (.imm 0) ]

/-- The final branch-free conditional subtract of `p` and store of the four
    result words to `z[0..3]`. After four CIOS iterations the accumulator
    `t0..t3` holds a value in `[0, 2p)`; trial-subtract `p` (immediates) staging
    each trial word in the stack scratch frame `sp[0..3]` (the `t4` high word
    participates in the borrow). If the final borrow `CF = 1` (i.e. `t < p`)
    `cmovb` keeps the original `tj`; else the trial word in scratch is kept. -/
def bn254FinalReduce : List (JInstr 64) :=
  -- trial = (t0..t3, t4) - (p, 0); stage each trial word in scratch sp[0..3].
  [ .mov "lo" (.reg "t0"), .mov "hi" (.imm (pLimbs[0]!)), .sub "lo" (.reg "hi"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.reg "t1"), .mov "hi" (.imm (pLimbs[1]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.reg "t2"), .mov "hi" (.imm (pLimbs[2]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.reg "t3"), .mov "hi" (.imm (pLimbs[3]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 24 (.reg "lo")
  , .sbb "t4" (.imm 0)   -- top word; CF = final borrow; CF=1 ⇒ t < p ⇒ keep originals
  -- select: load trial into hi, cmovb original (tj) over it when CF=1, store to z.
  , .loadMem "hi" "sp" 0,  .cmovb "hi" (.reg "t0"), .storeMem "z" 0  (.reg "hi")
  , .loadMem "hi" "sp" 8,  .cmovb "hi" (.reg "t1"), .storeMem "z" 8  (.reg "hi")
  , .loadMem "hi" "sp" 16, .cmovb "hi" (.reg "t2"), .storeMem "z" 16 (.reg "hi")
  , .loadMem "hi" "sp" 24, .cmovb "hi" (.reg "t3"), .storeMem "z" 24 (.reg "hi") ]

/-- The full CIOS Montgomery multiply body: zero the accumulator, four CIOS
    iterations, then the final conditional subtract + store. A concrete flat
    `List (JInstr 64)` the lowering / allocation lemmas chew on. -/
def bn254MontMulBlock : List (JInstr 64) :=
  -- zero the accumulator t0..t4 and the zero register
  [ .mov "zr" (.imm 0)
  , .mov "t0" (.imm 0), .mov "t1" (.imm 0), .mov "t2" (.imm 0)
  , .mov "t3" (.imm 0), .mov "t4" (.imm 0) ]
  ++ (List.range 4).flatMap ciosIter
  ++ bn254FinalReduce

/-! ## 3. The initial machine state (reg-ptr ABI)

`x`/`y`/`z` hold the buffer base addresses (modeled as register names). The
operand words live in memory at `[x + 8·i]`, `[y + 8·i]`; we seed `a0..a3`,
`b0..b3` at offsets `0,8,16,24`. -/

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
    full `loadMem`/`mulxMem`/`mulx`/`adcx`/`adox`/`imul`/`add`/`sbb`/`cmovb`/
    `storeMem` mix. -/
theorem bn254MontMulBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) bn254MontMulBlock).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) bn254MontMulBlock :=
  lowerBlock_denote_closed bn254MontMulBlock
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

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
theorem bn254FinalReduce_allDirect : allDirect bn254FinalReduce = true := rfl

/-- The whole CIOS Montgomery multiply body uses only direct base+displacement
    addressing (no secret-indexed memory access). Proved by splitting the body
    at its two concatenations and the iteration `flatMap`, so the cost is the
    per-piece checks rather than a reduction of the assembled block. -/
theorem bn254MontMulBlock_allDirect : allDirect bn254MontMulBlock = true := by
  simp only [bn254MontMulBlock, allDirect, List.all_append, List.all_flatMap,
    Bool.and_eq_true]
  exact ⟨⟨rfl, List.all_eq_true.mpr fun i _ => ciosIter_allDirect i⟩,
    bn254FinalReduce_allDirect⟩

/-- **Constant time.** The emitted BN254 Montgomery multiply produces the same
    machine leakage trace from any two starting states: its observable
    control-flow + memory-address sequence is a function of the program text
    alone, so it carries no information about the operand limbs. -/
theorem bn254MontMulBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ bn254MontMulBlock = blockLeak s₂ bn254MontMulBlock :=
  allDirect_constant_time bn254MontMulBlock bn254MontMulBlock_allDirect s₁ s₂

/-! ## 6. AT&T assembly emission (reg-ptr ABI + small stack scratch frame)

The kernel pins `z`→`%rdi`, `x`→`%rsi`, the running multiplier `yd`→`%rdx`
(the `MULX` implicit src1), and the scratch-frame base `sp`→`%rbp` (excluded
from `gpPool`). The `y`-pointer argument arrives in `%rdx` and is moved to a
free register in the prologue. The 32-byte scratch frame holds the final
conditional-subtract trial words. The body is `runBlock`-verified; the
prologue/epilogue are trusted ABI scaffolding. -/

/-- Pin pointers + the `MULX` multiplier `yd`→`%rdx` + scratch base `sp`→`%rbp`. -/
def bn254MontMulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def bn254MontMulAlloc : GpAlloc := allocGp bn254MontMulPinned bn254MontMulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias,
    the #380 class). -/
theorem bn254MontMulAlloc_no_overflow :
    allocOverflow bn254MontMulPinned bn254MontMulBlock = none := by native_decide

/-- The rendered AT&T body (one line per `JInstr`). -/
def bn254MontMulAsmBody : List String := renderBlockBody bn254MontMulAlloc bn254MontMulBlock

/-- The full emitted leaf `bn254_mont_mul_x86_from_lean(z, x, y)`. The prologue
    saves callee regs, carves a 32-byte scratch frame, points `%rbp` at it, and
    moves the `y` pointer out of `%rdx`. Frame alloc/restore is trusted ABI
    scaffolding outside the `runBlock`-verified body. -/
def bn254MontMulAsm : String :=
  renderLeafFn "bn254_mont_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $32, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf bn254MontMulAlloc "y" ]
    bn254MontMulAsmBody
    [ "\taddq $32, %rsp"
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
#guard (hasSub bn254MontMulAsm "mulx") && (hasSub bn254MontMulAsm "adcx") && (hasSub bn254MontMulAsm "adox") && (hasSub bn254MontMulAsm "imul") && (hasSub bn254MontMulAsm "mulxq 0(%rsi)") && (hasSub bn254MontMulAsm "(%rdi)") && (hasSub bn254MontMulAsm "src1=%rdx")

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bn254_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/bn254_fieldmul_compare/gen_com/bn254_mont_mul_x86_from_lean.s"
    bn254MontMulAsm
  IO.println "wrote gen_com/bn254_mont_mul_x86_from_lean.s (in-Lean x86 backend CIOS, no jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bn254MontMulKernel
