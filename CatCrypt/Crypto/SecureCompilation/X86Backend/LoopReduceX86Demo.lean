/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopReduceDemo

/-!
# Array-reduction loop x86 emit — `v := v + a[i]` to `.s` (task #538, wall #2)

`LoopReduceDemo` pins the array-reduction `v := v + a[i]` value semantics and the
**abstract** array-loop control-flow tie (`arrSumLoop_loopRun_eq_ref`, over the
`execCom` evaluator via `JForProgIndexed.loopRunT_eq_denoteT`), and names the
**x86 register-pin splice for the memref load** as the residual:
`cforIdxToLprogAbiBodyZeroAcc` accepts only a two-slot `[acc, ctr]` counter-reading
body, with no array-base register and no per-iteration `MOV resReg, [base+idx*8]`
load.

This module **closes that splice**. `LprogControlFlow.cforIdxToLprogAbiBodyArr`
(added alongside the §5b counter-reading emitters) lowers the genuine three-slot
array-reduction body `arrSumBody nRC : Com [.reg 64, .reg 64, .stackArr 64 nRC]
(.reg 64)` over `(acc, idx, a)` to a callable owned `.s` function:

* the per-iteration `stackLoad a idx` (the memref load `a[idx]`) is lowered by the
  pre-existing `opToLinstrR`/`LprogAsmPrinter` SIB path to a register-indexed load
  `LOADIDX [.arrIdx aReg idxReg 8]`, rendered `mov (%aReg,%idxReg,8), %scratch`;
* the **array base** is passed in the SysV second arg `RSI` and pinned to the
  body's `a2`-arg register;
* the **index** ascends `0,1,…,n-1` (matching the abstract loop's ascending
  `idx = i`) in `idxReg`, `ADD idxReg, #1`'d each iteration, pinned to the body's
  `a1`-arg register;
* the **trip counter** `nReg` runs down `n,…,1` for the back-edge.

## What is landed here

1. **The array-reduction x86 emit** `arrSumAbiLcmd nRC` — `arrSumBody nRC` lowered
   through `cforIdxToLprogAbiBodyArr` at width 64, top label `0`, counter `R8`,
   index `R9`, base pointer `RSI`, trip count `100`. It is **rendered** to AT&T
   `.s` by `renderArrSumLoopS` (function name `loop_reduce_arrsum`) — NOT a
   hand-authored asm string; the memref load comes out of the body's `stackLoad`
   through the SIB lowering. `arrSumAbiLcmd_nonempty` witnesses the emit produced
   instructions (it ends with the `MOV RAX, resReg` return splice).

2. **The value semantics tie (abstract).** `arrSumLoop_denoteT_eq_ref` /
   `arrSumLoop_loopRun_eq_ref` (re-exported from `LoopReduceDemo`) certify, for
   **all** trip counts, that the array-reduction loop the emit realises computes
   the independent reference array sum `Σ_{j<n} a[j]` (`arrSumUpTo`). The emit and
   the abstract loop share the body `arrSumBody nRC` and the ascending-index fold.

## The honest residual (the Lprog-denotation value-tie is NOT carried to bytes)

There is **no `lsem` model** for the ABI-body emit — `cforIdxToLprogAbiBodyArr`
(like `cforIdxToLprogAbiBody{,ZeroAcc}`) is a control-flow + ABI emit outside the
straight-line fragments `ComLsemExportFaithful[MC]` cover, so its Com→`.s` tie is
the trusted physical-emit boundary, not a machine-semantics denotation of the
emitted `Lcmd`. The tie in §2 is over the
abstract `execCom` array-loop evaluator (`loopRunT`/`denoteT`); it is **not** a
proof that the rendered `.s` bytes compute the array sum. That last link — a
machine-semantics denotation of the spliced loop (the `MOV (%base,%idx,8)` SIB
load, the `ADD idxReg,#1` index-up, the `SUB nReg,#1`/`CMP`/`jne` back-edge) tied
to `cforIdxDenote`/`loopRunT` — is the same Lprog-denotation gap
`cforIdxToLprogAbiBodyZeroAcc` carries, and is closed at run time by the
C-harness byte-KAT (array → sum) the bench driver runs, not by an in-Lean kernel.

Relative to `LoopReduceDemo`, this file adds the array-base + scaled-indexed-load
**ABI-body emitter** `cforIdxToLprogAbiBodyArr` (the 3-slot `[acc, idx, ptr]`
body, the SIB `MOV (%base,%idx,8)` structure, the index-up / counter-down split)
and the proven **abstract** value-tie.

The two register-resolution bugs that kept the rendered `.s` from assembling are
**fixed**:

1. **SIB arg-register resolution (fixed).** The register-indexed (SIB) source
   `arrIdx base idx scale` is now threaded through the same physical-name map as
   every other body operand: `JasminLprogExport.LOperand.srcRegNames` tracks the
   SIB **base** (the array pointer) as a register-file source alongside the index,
   so the linear scan allocates it, and `remapOperand`'s new `.arrIdx` arm rewrites
   both `base` and `idx` to physical registers. The SIB now renders
   `(%ptrReg, %idxReg, 8)` with real registers instead of `(%<UNKNOWN:a0>, …)`.

2. **Accumulator/array arg-slot swap (fixed).** `tabCtxt accTy nRC =
   [accTy, .reg 64, .stackArr 64 nRC]` lists the accumulator at the **head** and
   the array at the **tail**; `comToLfundef`'s program-root (`Γ.reverse`) order
   therefore numbers them `a0 = array base`, `a1 = idx`, `a2 = accumulator` — the
   *reverse* of the De-Bruijn order. `cforIdxToLprogAbiBodyArr` had read `a0` as the
   accumulator and `a2` as the pointer, so the `XOR accReg, accReg` prologue zeroed
   `a0`'s register (the array base). The splice now reads the accumulator from `a2`
   and the array base from `a0`, so the XOR zeroes the genuine accumulator.

With these two fixes the SIB renders real registers and the prologue zeroes the
genuine accumulator, so the `.s` **assembles**. The value-semantics link to the
rendered bytes is still the same Lprog-denotation gap
`cforIdxToLprogAbiBody{,ZeroAcc}` carry (no `lsem` model for the ABI-body emit):
the §2 tie is over the abstract `execCom` array-loop evaluator
(`loopRunT`/`denoteT`), and the rendered `.s` is closed at run time by the
C-harness byte-KAT (array → sum) the bench driver runs, not by an in-Lean kernel.

The earlier register-aliasing residual is **also fixed**. The three loop-carried
roles (acc/idx/ptr) must occupy three *distinct* registers that survive the
back-edge, but `comToLfundefPhys` allocates the body as a single straight-line
copy: for a body whose arg uses are *disjoint* in that copy, the linear scan
reclaims and aliases the arg registers onto one slot, and the per-iteration arg
pins then clobber the accumulator. `arrSumBody` now opens with a **leading
liveness binder** (`regArith .add acc idx`, result discarded) that reads `acc`
and `idx` at the body's first instruction, so the accumulator's live range
overlaps the index and array-base uses and the linear scan keeps all three in
distinct registers across the back-edge. The binder is shadowed (never reaches
`.ret`), so the denotation is unchanged (`arrSumBody_denote` is still `rfl`).
This mirrors the §5b rejection-sampler body (`acc ^= ctr`, which reads both
loop-carried values in one binding and so was never aliased — which is why the
§5b byte-KATs already passed). The fix is local to `arrSumBody`; the global
linear scan is untouched, so the SIB-using kernels (Keccak/Poseidon2) are
unaffected.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoopReduceX86Demo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy jasminDialect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopReduceDemo
  (arrSumBody arrSumLoop arrSumUpTo arrSumLoop_denoteT_eq_ref arrSumLoop_loopRun_eq_ref)

/-! ## 1. The array-reduction x86 emit and rendered `.s` (driver-facing) -/

/-- The array-reduction loop `v := v + a[i]` lowered to a callable owned function
    body via the **three-slot** array ABI emitter `cforIdxToLprogAbiBodyArr`:
    `arrSumBody nRC` (over `(acc, idx, a)`) at width 64, top label `0`, counter
    register `R8`, ascending-index register `R9`, base-pointer register `RSI`
    (the SysV second arg), trip count `100`. The accumulator is zero-initialised
    in the prologue (`XOR accReg, accReg`); the per-iteration `stackLoad a idx`
    is lowered to the SIB load `LOADIDX [.arrIdx aReg R9 8]`. -/
def arrSumAbiLcmd (nRC : Nat) : VIR.JasminLprogExport.Lcmd :=
  cforIdxToLprogAbiBodyArr (nRC := nRC) 64 0 "R8" "R9" "RSI" 100 (arrSumBody nRC)

/-- The rendered AT&T `.s` text for the array-reduction loop, function name
    `loop_reduce_arrsum`. The driver writes this to `bench/loop_reduce/gen/`.
    The per-iteration `mov (%rsi,%r9,8), %scratch` SIB load is produced by the
    body's `stackLoad`, not hand-authored. The array length `nRC` only types the
    body; the emitted code is array-data-independent (the values are loaded at
    run time through `RSI`). -/
def renderArrSumLoopS (nRC : Nat) : String :=
  renderLfundef "loop_reduce_arrsum" (arrSumAbiLcmd nRC)

/-- The emitted body is non-empty (the lowering produced instructions): it ends
    with the `MOV RAX, resReg` return splice, so it is a `(_ :: _) ++ [_]`. -/
theorem arrSumAbiLcmd_nonempty (nRC : Nat) : arrSumAbiLcmd nRC ≠ [] := by
  simp only [arrSumAbiLcmd, cforIdxToLprogAbiBodyArr]
  exact List.append_ne_nil_of_right_ne_nil _ (by simp)

/-! ## 2. The value-semantics tie (abstract, re-exported)

The emit in §1 realises the array-reduction loop `arrSumLoop a n` whose value
semantics `LoopReduceDemo` certified against the independent reference array sum
`arrSumUpTo a n = Σ_{j<n} a[j]`, for **all** trip counts. We re-state the two ties
here so the x86 demo is self-contained: the abstract array-loop run/denotation the
emit realises equals the reference sum (the residual being the Lprog-denotation
gap — see the module docstring). -/

open CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed (loopRunT)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect (LeafSem LeafAgrees)

/-- **The value semantics the emit realises (denotation form).** The
    array-reduction loop `arrSumLoop a n`'s index-dependent denotation from
    `acc = 0` equals the independent reference array sum `Σ_{j<n} a[j]`
    (`arrSumUpTo a n`), for every trip count `n`. This is `LoopReduceDemo`'s
    `arrSumLoop_denoteT_eq_ref`; the §1 emit lowers exactly this loop's body
    (`arrSumBody`) and ascending-index fold. -/
theorem arrSumX86_denote_eq_ref {nRC : Nat} (a : Fin nRC → BitVec 64) (n : Nat) :
    (arrSumLoop a n).denoteT (0 : BitVec 64) = arrSumUpTo a n :=
  arrSumLoop_denoteT_eq_ref a n

/-- **The value semantics the emit realises (abstract run form).** Routed through
    the array-loop control-flow keystone, the abstract emitted array-reduction loop
    run from `acc = 0` equals the reference array sum `Σ_{j<n} a[j]`, under the
    single opaque-leaf hypothesis. This is `LoopReduceDemo`'s
    `arrSumLoop_loopRun_eq_ref`; it is over the abstract `execCom` evaluator, NOT
    the rendered `.s` bytes (the Lprog-denotation residual — see module docstring). -/
theorem arrSumX86_loopRun_eq_ref {nRC : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (a : Fin nRC → BitVec 64) (n : Nat) :
    loopRunT leafSem (arrSumLoop a n) (0 : BitVec 64) = arrSumUpTo a n :=
  arrSumLoop_loopRun_eq_ref hLeaf a n

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoopReduceX86Demo
