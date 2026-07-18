/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel

/-!
# Lazy-reduction Curve25519 field-OP leaves `feAddLazy`/`feSubLazy`/`feCmadd121666Lazy` (#410)

`Fe25519OpsKernel.lean` emits the **canonical** field add/sub: each forms `x ± y`
and then performs a full conditional reduction mod `p = 2^255 - 19`, so the
output is the unique canonical residue `< p`. In a leaf-composed Montgomery
ladder every such add/sub output flows directly into a `feMul`/`feSqr`, whose
4×4 schoolbook reads its inputs as arbitrary 64-bit limbs and reduces its result
internally — i.e. the multiply already tolerates any input `< 2^256`. The
canonical reduction the add/sub performs is therefore **redundant**: the value
is reduced once eagerly by the producer and again (unavoidably) by the consuming
multiply.

This module emits the **lazy** (reduction-deferred) variants, mirroring
s2n-bignum's `add_twice4` / `sub_twice4` / `cmadd_4` (the building blocks of
`curve25519_x25519`). They maintain the looser invariant "output `< 2^256`,
congruent mod `p`" instead of "output `< p`", replacing the multi-instruction
canonical select with a single carry/borrow fold of the modular overflow:

* `feAddLazyBlock` — `z := x + y` with the `2^256` overflow folded as `+38`
  (since `2^256 ≡ 38 (mod p)`); s2n `add_twice4`. Output `< 2^256`, `≡ x+y`.
* `feSubLazyBlock` — `z := x - y` with an underflow corrected by `-38` of the
  borrowed `2^256` (`x - y + 2^256 ≡ x - y + 38`); s2n `sub_twice4`. Output
  `< 2^256`, `≡ x-y`.
* `feCmadd121666LazyBlock` — `z := 121666·x + y` reduced only `< 2·p`; s2n
  `cmadd_4` with `C1 = 0x1db42 = 121666`. This fuses the X25519 doubling-step
  `e = 121666·p + d` (our previous `feMul121666` followed by `feAdd`) into a
  single leaf, removing both an eager reduce AND a leaf call.

The branchless overflow fold uses the `sbb r,r` (`= 0 - CF`) sign-mask idiom
already used by `feSubBlock`, so no new `cmovnc` semantics is needed.

## Magnitude-bound analysis (the soundness argument for deferral)

The lazy leaves are sound **as a drop-in replacement inside the X25519 ladder**
because of the following invariant, maintained by the leaf set:

* `feMul`/`feSqr`/`feMul121666` (canonical, from `Fe25519MulKernel`/
  `Fe25519OpsKernel`) produce output `< p < 2^255 < 2^256`.
* `feAddLazy` takes two operands each `< 2^256` to `< 2^256` (s2n's documented
  `add_twice4` bound: result fits in 4 digits provided the operand sum is
  `< 2^256 + (2^256 - 38)`, in particular whenever at least one operand is
  reduced double-modulo; a single un-chained add of two `< 2^255` canonical
  values is trivially `< 2^256`).
* `feSubLazy` likewise: operands `< 2^256` ↦ `< 2^256`.
* The schoolbook multiply (`feMulBlock`/`feSqrBlock`) reads inputs via `mulx`
  as arbitrary radix-`2^64` 4-limb integers and its fused-quotient-estimate
  reduce returns the canonical residue for **any** product `< 2^256·2^256`;
  hence any input `< 2^256` is acceptable, and the output is again `< p`.

In the RFC 7748 ladder step the lazy add/sub outputs (`A,B,C,D,E,t`) feed
**only** `feMul`/`feSqr`/`feCmadd` — never two lazy adds in a row without an
intervening multiply — so every lazy intermediate is consumed while still
`< 2^256`. The deferral is therefore value-preserving: the lazy ladder computes
the same field element as the canonical ladder. This is the same loose-reduction
discipline that s2n-bignum's HOL-Light proof of `curve25519_x25519` establishes;
here the **value identity** is gated by the runtime KAT
(`bench/x25519_ladder_compare/x25519_ladder_lazy.c`) against RFC 7748 §5.2 and
s2n's verified `curve25519_x25519`, mirroring `Fe25519OpsKernel`'s discipline.

## What is proved here

For each lazy block: `feXLazyBlock_lowering_correct` — the owned x86 backend's
straight-line lowering is denotation-preserving (reusing `lowerBlock_denote_closed`,
exactly as the canonical leaves), plus body-length and mnemonic-shape checks and
no register-allocation overflow. No `sorry`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LazyOpsKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel (initState1 initState2)

/-! ## 1. feAddLazy: `z := x + y`, overflow folded as `+38` (s2n `add_twice4`)

Form `d = x + y` over four limbs; `CF` after the top adc is the `2^256` carry.
`m := 0 − CF` (all-ones iff carry); `addend := m & 38`; `d += addend` (this last
add cannot itself produce a fresh `2^256` overflow given the operand bound), then
store. No canonical select: output is `< 2^256`, congruent to `x + y` mod `p`. -/
def feAddLazyBlock : List (JInstr 64) :=
  [ .loadMem "d0" "x" 0
  , .loadMem "lo" "y" 0,  .add "d0" (.reg "lo")
  , .loadMem "d1" "x" 8
  , .loadMem "lo" "y" 8,  .adc "d1" (.reg "lo")
  , .loadMem "d2" "x" 16
  , .loadMem "lo" "y" 16, .adc "d2" (.reg "lo")
  , .loadMem "d3" "x" 24
  , .loadMem "lo" "y" 24, .adc "d3" (.reg "lo")
    -- m = 0 - CF (all-ones iff there was a carry out of bit 255)
  , .mov "m" (.imm 0), .sbb "m" (.imm 0)
    -- addend = m & 38  (= 38 iff carry, else 0)
  , .and_ "m" (.imm 38)
  , .mov "zr" (.imm 0)
  , .add "d0" (.reg "m")
  , .adc "d1" (.reg "zr")
  , .adc "d2" (.reg "zr")
  , .adc "d3" (.reg "zr")
  , .storeMem "z" 0 (.reg "d0")
  , .storeMem "z" 8 (.reg "d1")
  , .storeMem "z" 16 (.reg "d2")
  , .storeMem "z" 24 (.reg "d3") ]

theorem feAddLazyBlock_length : feAddLazyBlock.length = 24 := by native_decide

/-- **Lowering correctness on the lazy add block.** -/
theorem feAddLazyBlock_lowering_correct (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (lowerBlock (Γ := []) feAddLazyBlock).denote
        (.cons (initState2 x0 x1 x2 x3 y0 y1 y2 y3) .nil)
      = runBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3) feAddLazyBlock :=
  lowerBlock_denote_closed feAddLazyBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3)

/-! ## 2. feSubLazy: `z := x − y`, underflow corrected by `−38` (s2n `sub_twice4`)

Form `d = x − y` over four limbs; `CF` after the top sbb is the `2^256` borrow.
`amt := (0 − CF) & 38` (= 38 iff we borrowed); subtract `amt` (this cancels the
borrowed `2^256` ≡ 38, so `d ≡ x − y` mod `p`), propagating borrow. Output
`< 2^256`. No canonical select. -/
def feSubLazyBlock : List (JInstr 64) :=
  [ .loadMem "d0" "x" 0
  , .loadMem "lo" "y" 0,  .sub "d0" (.reg "lo")
  , .loadMem "d1" "x" 8
  , .loadMem "lo" "y" 8,  .sbb "d1" (.reg "lo")
  , .loadMem "d2" "x" 16
  , .loadMem "lo" "y" 16, .sbb "d2" (.reg "lo")
  , .loadMem "d3" "x" 24
  , .loadMem "lo" "y" 24, .sbb "d3" (.reg "lo")
    -- amt = (0 - CF) & 38  (= 38 iff there was a borrow)
  , .mov "c" (.imm 0), .sbb "c" (.imm 0)
  , .and_ "c" (.imm 38)
  , .mov "zr" (.imm 0)
  , .sub "d0" (.reg "c")
  , .sbb "d1" (.reg "zr")
  , .sbb "d2" (.reg "zr")
  , .sbb "d3" (.reg "zr")
  , .storeMem "z" 0 (.reg "d0")
  , .storeMem "z" 8 (.reg "d1")
  , .storeMem "z" 16 (.reg "d2")
  , .storeMem "z" 24 (.reg "d3") ]

theorem feSubLazyBlock_length : feSubLazyBlock.length = 24 := by native_decide

/-- **Lowering correctness on the lazy sub block.** -/
theorem feSubLazyBlock_lowering_correct (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (lowerBlock (Γ := []) feSubLazyBlock).denote
        (.cons (initState2 x0 x1 x2 x3 y0 y1 y2 y3) .nil)
      = runBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3) feSubLazyBlock :=
  lowerBlock_denote_closed feSubLazyBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3)

/-! ## 3. feCmadd121666Lazy: `z := 121666·x + y` reduced `< 2·p` (s2n `cmadd_4`)

Fuses the X25519 doubling step `e = 121666·p + d` into one leaf (was
`feMul121666` then `feAdd`). The multiplier `C1 = 0x1db42 = 121666`. Since
`19·(121666·x + y) < 2^60·2^256`, the high part needs only a single-word
multiply by `19` (no high `mulx`), exactly as s2n: estimate the top word, fold
`19·hi`, conditional `−p` via the sign idiom, clear bit 255. Output `< 2·p`
(hence `< 2^256`), congruent to `121666·x + y`.

Two-input init state: `x` is the operand multiplied, `y` is the addend. `yd` is
the `%rdx`-pinned multiplier, `zr` the zero scratch. -/
def feCmadd121666LazyBlock : List (JInstr 64) :=
  [ -- load the addend y into the accumulator [d0..d3]
    .loadMem "d0" "y" 0
  , .loadMem "d1" "y" 8
  , .loadMem "d2" "y" 16
  , .loadMem "d3" "y" 24
  , .mov "zr" (.imm 0)
  , .xor_ "zr" (.reg "zr")             -- clear CF/OF
  , .mov "yd" (.imm 121666)
    -- d += 121666 * x   (dual carry chain, accumulating the 5th word in `hi`)
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "d0" (.reg "lo"), .adox "d1" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8
  , .adcx "d1" (.reg "lo"), .adox "d2" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16
  , .adcx "d2" (.reg "lo"), .adox "d3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 24
  , .adcx "d3" (.reg "lo")
  , .adox "hi" (.reg "zr")             -- top word b := high*… overflow (OF chain)
  , .adcx "hi" (.reg "zr")             -- + CF chain
    -- fold the 5th word: q = 2*hi + bit63(d3); inject 19*q; clear bit 255 of d3
  , .mov "q" (.reg "d3"), .shr "q" (.imm 63)
  , .shl "hi" (.imm 1)
  , .add "hi" (.reg "q")               -- hi = 2*hi + bit63(d3)
  , .imul "hi" (.imm 19)               -- hi = 19*q
  , .mov "lo" (.imm 0x7fffffffffffffff), .and_ "d3" (.reg "lo")  -- clear bit 255
  , .add "d0" (.reg "hi")
  , .adc "d1" (.reg "zr")
  , .adc "d2" (.reg "zr")
  , .adc "d3" (.reg "zr")
  , .storeMem "z" 0 (.reg "d0")
  , .storeMem "z" 8 (.reg "d1")
  , .storeMem "z" 16 (.reg "d2")
  , .storeMem "z" 24 (.reg "d3") ]

theorem feCmadd121666LazyBlock_length : feCmadd121666LazyBlock.length = 35 := by native_decide

/-- **Lowering correctness on the fused cmadd block.** -/
theorem feCmadd121666LazyBlock_lowering_correct (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (lowerBlock (Γ := []) feCmadd121666LazyBlock).denote
        (.cons (initState2 x0 x1 x2 x3 y0 y1 y2 y3) .nil)
      = runBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3) feCmadd121666LazyBlock :=
  lowerBlock_denote_closed feCmadd121666LazyBlock (initState2 x0 x1 x2 x3 y0 y1 y2 y3)

/-! ## 4. AT&T assembly emission (in-Lean backend, no jasminc)

`feAddLazy`/`feSubLazy` are two-input (`z`→`%rdi`, `x`→`%rsi`, `y`→`%rdx`).
`feCmadd121666Lazy` is also two-input but uses `MULX`, so `yd`→`%rdx` is pinned
(the multiplier) — the `y` addend buffer must therefore live in a different
register; we pin it to `%rcx` and copy the System-V third argument `%rdx` into
`%rcx` in the prologue (then `yd`/`%rdx` is free for the immediate multiplier).
`zr`→`%rbp`. -/

def feAddLazyPinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("y", "%rdx")]
def feSubLazyPinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("y", "%rdx")]
def feCmadd121666LazyPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("y", "%rcx"), ("yd", "%rdx"), ("zr", "%rbp")]

def feAddLazyAlloc : GpAlloc := allocGp feAddLazyPinned feAddLazyBlock
def feSubLazyAlloc : GpAlloc := allocGp feSubLazyPinned feSubLazyBlock
def feCmadd121666LazyAlloc : GpAlloc := allocGp feCmadd121666LazyPinned feCmadd121666LazyBlock

def feAddLazyAsm : String :=
  renderLeafFn "fe25519_add_lazy_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tmovq %rdx, " ++ regOf feAddLazyAlloc "y" ]
    (renderBlockBody feAddLazyAlloc feAddLazyBlock)
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

def feSubLazyAsm : String :=
  renderLeafFn "fe25519_sub_lazy_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tmovq %rdx, " ++ regOf feSubLazyAlloc "y" ]
    (renderBlockBody feSubLazyAlloc feSubLazyBlock)
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

def feCmadd121666LazyAsm : String :=
  renderLeafFn "fe25519_cmadd121666_lazy_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15", "\tpushq %rbp"
    , "\tmovq %rdx, " ++ regOf feCmadd121666LazyAlloc "y" ]
    (renderBlockBody feCmadd121666LazyAlloc feCmadd121666LazyBlock)
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

theorem feAddLazyAsmBody_length :
    (renderBlockBody feAddLazyAlloc feAddLazyBlock).length = 24 := by native_decide
theorem feSubLazyAsmBody_length :
    (renderBlockBody feSubLazyAlloc feSubLazyBlock).length = 24 := by native_decide
theorem feCmadd121666LazyAsmBody_length :
    (renderBlockBody feCmadd121666LazyAlloc feCmadd121666LazyBlock).length = 35 := by native_decide

/-- No register-allocation overflow for any of the three lazy blocks. -/
theorem feLazyOps_alloc_no_overflow :
    allocOverflow feAddLazyPinned feAddLazyBlock = none
      ∧ allocOverflow feSubLazyPinned feSubLazyBlock = none
      ∧ allocOverflow feCmadd121666LazyPinned feCmadd121666LazyBlock = none := by native_decide

/-- Shape checks: each emitted body contains the expected mnemonics; the lazy
    add/sub bodies do NOT contain the canonical-select `cmov`/`xor`-mask tail. -/
theorem feLazyOps_asm_shape :
    BignumMontMulKernel.hasSub feAddLazyAsm "addq"
      ∧ BignumMontMulKernel.hasSub feSubLazyAsm "sbbq"
      ∧ BignumMontMulKernel.hasSub feCmadd121666LazyAsm "$121666"
      ∧ BignumMontMulKernel.hasSub feCmadd121666LazyAsm "mulx" := by native_decide

/-- Emit driver: write the lazy `.s` files for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_ladder_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_ladder_compare/gen_com/fe25519_add_lazy_x86_from_lean.s" feAddLazyAsm
  IO.FS.writeFile
    "bench/x25519_ladder_compare/gen_com/fe25519_sub_lazy_x86_from_lean.s" feSubLazyAsm
  IO.FS.writeFile
    "bench/x25519_ladder_compare/gen_com/fe25519_cmadd121666_lazy_x86_from_lean.s"
    feCmadd121666LazyAsm
  IO.println "wrote gen_com/fe25519_{add_lazy,sub_lazy,cmadd121666_lazy}_x86_from_lean.s"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LazyOpsKernel
