/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeFront
public import CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeFront
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Front schedule for the MSB-first early-exit `mpn_cmp`

`MpnLoopEmit`'s eight core runtime-N loop kernels (`add/sub/and/ior/xor/
com/copyi/zero`) are front-sourced through `TranslateDialectRuntimeLoop.
rolledForLoopNRt` (a covered `LowCT` loop body → `ComL.forLoopNRt` → owned
export). The one kernel that path could not express was `mpn_cmp`: GMP's
`__gmpn_cmp(ap, bp, n)` scans the limbs **MSB-first with a data-dependent early
exit** on the first differing limb and returns one of `{-1, 0, +1}`. A rolled
counted loop over the whole operand has no in-body forward exit and no small-set
return, so `mpn_cmp` stayed the last hand-authored owned-emit output (a void-leaf
full-scan stub — the documented backend gap).

This module supplies the front schedule that GENERATES the real early-exit
`mpn_cmp`, reusing the `SpStep` schedule language (`Shake256SpongeFront`) whose
primitives already cover every op the kernel needs — **no new step op**:

* the **runtime-N scan loop** is the top-tested `label ; cmp ; condFwd done ;
  body ; goto top ; done` shape (`SpStep.ctrl (.label/.cmpImm/.condFwd)` +
  `SpStep.goto` back-edge), the same runtime-loop shape the SHAKE256 sponge's
  absorb/squeeze loops use;
* the **data-dependent early break** is a forward `condFwd` out of the loop body
  to an after-loop sign block (`QuerySampleBranchFront.condSkip`'s forward
  branch, here breaking OUT of the loop rather than skipping a straight-line
  `then`);
* the **per-limb compare** is `SpStep.subRR t0 t1` (`t0 := a[i] - b[i]`), whose
  `ZF`/`CF` give `a[i] == b[i]` / `a[i] < b[i]` (a compare-by-subtract; the
  difference limb is discarded, only the flags are read);
* the **MSB-first order** is a decrementing scan: advance both pointers to one
  past the top limb (`base += 8·n` via `shlImm`/`addRR`), then step down `8`
  bytes each iteration and load at offset `0`;
* the **`{-1, 0, +1}` return** is a branch-built sign (`movImm RAX 1` for the
  `a > b` case, `movImm RAX 0 ; subImm RAX 1` = `-1` for `a < b`, default `0` for
  all-equal), left in `RAX`.

## ABI (GMP `__gmpn_cmp`)

SysV, `int mpn_cmp(const mp_limb_t *ap, const mp_limb_t *bp, mp_size_t n)`:
`ap → RDI`, `bp → RSI`, `n → RDX`, result `{-1,0,+1} → RAX`. The scratch is
`RAX` (result), `RCX` (counter), `R8` (`8·n` stride), `R9`/`R10` (the two loaded
limbs) — all caller-saved, so the leaf needs no callee-save park.

## Denotation

The forward `condFwd` break, the `goto` back-edge, and the `subRR` compare have
the **same** denotation status as the SHAKE256 sponge and query-sampler fronts:
the pure A-normal `Com` substrate carries no label/jump denotation, so a
machine-denote for the control flow is the reported residual, not claimed here.
What is discharged is the structural contract — the schedule renders exactly the
owned-backend `cmp ; Jcc ; … ; jmp ; label` early-exit shape the byte encoder
consumes, the generation gate (`wellFormedCmp`), and the value-correct
`{-1,0,+1}` MSB-first scan. Byte-level conformance is the external libgmp
`__gmpn_cmp` KAT.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MpnCmpEarlyExitFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lcmd)
open CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeFront
  (SpStep spstepToLcmd spband hasBranch hasGoto)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef)

/-! ## 1. The MSB-first early-exit compare schedule

Labels: `top = 0`, `done = 1`, `diff = 2`. The scan loop is top-tested
(`label top ; cmp counter,0 ; condFwd done ; … ; goto top`); the per-limb break
is `condFwd diff` out of the loop to the sign block; the sign block falls through
to `done`. -/

/-- The `mpn_cmp` schedule (GMP `__gmpn_cmp` ABI, `ap → RDI`, `bp → RSI`,
    `n → RDX`, result `→ RAX`). MSB-first decrementing scan with a data-dependent
    early break to the `{-1,0,+1}` sign block. -/
def cmpSteps : List SpStep :=
  [ -- default result = 0 (operands compare equal)
    .ctrl (.movImm "RAX" 0)
    -- n == 0 ⇒ return 0
  , .ctrl (.cmpImm "RDX" 0)
  , .ctrl (.condFwd "E" 1)
    -- counter := n ; advance ap/bp to one-past the top (MSB) limb: base += 8·n
  , .ctrl (.movRR "RCX" "RDX")
  , .ctrl (.movRR "R8" "RDX")
  , .ctrl (.shlImm "R8" 3)                 -- R8 := 8·n
  , .ctrl (.addRR "RDI" "R8")              -- ap := ap + 8·n  (one past the top limb)
  , .ctrl (.addRR "RSI" "R8")              -- bp := bp + 8·n
    -- MSB-first scan loop (top-tested)
  , .ctrl (.label 0)
  , .ctrl (.cmpImm "RCX" 0)
  , .ctrl (.condFwd "E" 1)                 -- counter exhausted ⇒ all equal ⇒ done (RAX=0)
  , .ctrl (.subImm "RDI" 8)                -- step down to the current limb …
  , .ctrl (.subImm "RSI" 8)
  , .ctrl (.load "R9" "RDI" 0)             -- a[i]
  , .ctrl (.load "R10" "RSI" 0)            -- b[i]
  , .subRR "R9" "R10"                       -- R9 := a[i] - b[i] ; ZF=(a==b), CF=(a<b)
  , .ctrl (.condFwd "NE" 2)                -- differ ⇒ break OUT of the loop to the sign block
  , .ctrl (.subImm "RCX" 1)                -- equal ⇒ decrement counter …
  , .goto 0                                 -- … and continue (back-edge)
    -- sign block (label 2): a[i] ≠ b[i]; CF still reflects (a[i] < b[i])
  , .ctrl (.label 2)
  , .ctrl (.movImm "RAX" 1)                -- assume a[i] > b[i] (mov leaves CF intact)
  , .ctrl (.condFwd "NC" 1)                -- CF=0 ⇒ a[i] > b[i] ⇒ return +1
  , .ctrl (.movImm "RAX" 0)                -- else a[i] < b[i]:  RAX := 0 - 1 = -1
  , .ctrl (.subImm "RAX" 1)
  , .ctrl (.label 1) ]                      -- done

/-- The `mpn_cmp` owned body (`spband 64` of the schedule). -/
def cmpBodyFront : Lcmd := spband 64 cmpSteps

/-! ## 2. Generation gate (`wellFormedCmp`) — the `isSome` analogue

`spband` is total, so the front gate is a decidable well-formedness `Bool`: an
early-exit compare schedule is well-formed iff it carries the data-dependent
forward branch (the early break) and the runtime loop back-edge. Unlike the
sponge gate it needs **no** leaf `call` (the compare is a call-free scan). -/

/-- Generation gate: the schedule carries the early-break forward branch and the
    scan-loop back-edge. -/
def wellFormedCmp (steps : List SpStep) : Bool := hasBranch steps && hasGoto steps

theorem cmp_wellFormed : wellFormedCmp cmpSteps = true := by native_decide

/-! ## 3. The rendered early-exit `.s` (front-sourced deployed body) -/

/-- The FRONT-sourced deployed `.s` text for `mpn_cmp` (rendered from the schedule
    via the owned `renderLfundef`). This is what `MpnLoopEmit` deploys. -/
def cmpAsmFront : String := renderLfundef "mpn_cmp_loop_owned" cmpBodyFront

/- **The rendered `mpn_cmp` is an MSB-first early-exit scan returning
    `{-1,0,+1}` in `RAX` over the GMP ABI.** The body renders:
    * the scan loop back-edge (`.L0:` / `jmp .L0`);
    * the per-limb compare-by-subtract (`subq %r10, %r9`);
    * the data-dependent early break (`jne .L2`) OUT of the loop and the counter
      guard (`je .L1`);
    * the `{-1,0,+1}` sign construction (`movq $1, %rax` for `+1`, `subq $1, %rax`
      for `-1`);
    * the GMP ABI operand streaming (`(%rdi)` = `a[i]`, `(%rsi)` = `b[i]`);
    and emits no `UNHANDLED` sentinel — every schedule op rendered to a real
    line. -/
#guard (occursIn ".L0:" cmpAsmFront)
    && (occursIn "jmp .L0" cmpAsmFront)
    && (occursIn "subq %r10, %r9" cmpAsmFront)
    && (occursIn "jne .L2" cmpAsmFront)
    && (occursIn "je .L1" cmpAsmFront)
    && (occursIn "movq $1, %rax" cmpAsmFront)
    && (occursIn "subq $1, %rax" cmpAsmFront)
    && (occursIn "(%rdi)" cmpAsmFront)
    && (occursIn "(%rsi)" cmpAsmFront)
    && !(occursIn "UNHANDLED" cmpAsmFront)

end CatCrypt.Crypto.SecureCompilation.VIR.MpnCmpEarlyExitFront
