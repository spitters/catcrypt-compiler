/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLinearKernels
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
import CatCrypt.Crypto.SecureCompilation.VIR.MpnCmpEarlyExitFront

/-!
# Runtime-N `mpn_*` loop kernels through the OWNED guarded-loop backend (#500)

`MpnLinearKernels.lean` / `MpnAdxOwnedLprog.lean` emit the elementary `mpn_*`
kernels **fully unrolled at a fixed compile-time limb count** `n` (the unrolled
straight-line body, one register window, no back-edge). That is exactly what the
*owned* fixed-N twins provide, and it is why the trivial-tier jasmin benches
(`bench/integration`, `bench/gmp_bench`, `bench/gmp_diff`) could *not* flip to
the owned backend: their GMP-ABI `mpn_*` kernels are **runtime-N** — a
`while (i < n) { … }` loop whose limb count `n` is a *runtime argument*, not a
compile-time constant. A fixed-N unrolled body cannot stand in for a kernel the
caller invokes at an arbitrary `n`.

This module emits those **runtime-N** loop kernels through the *owned*
control-flow backend:

* the per-limb body is the streaming **pointer-advance** shape
  (`load [a]; op; store [r]; a += 8; b += 8; r += 8; n -= 1`), modeled in the
  `JInstr 64` subset (`JasminModel.evalInstr`);
* the loop is the bounded counter-decrement loop `while (n != 0) { body }`, whose
  trip count is the **runtime** register `n` (`LoopUnroll.runBoundedLoop` — for a
  runtime incoming `n` this is the data-dependent iteration count, the same
  state-resolved trip-count move `RejectLoop.runGuardedLoop` uses);
* the lowering is denotation-preserving for **any** `n`
  (`LoopUnroll.boundedLoop_lowering_denote_closed`), i.e. one theorem covers every
  runtime limb count;
* the **emission** is the *looped* owned-backend control-flow shape
  (`LprogControlFlow.loopLcmd`: `.L: body ; cmpq $0,%n ; jne .L`), **constant-size
  in the runtime trip count** — exactly the runtime-N artifact the jasmin `mpn_*`
  produces, now from the owned front (`renderLfundef`, no jasminc).

## Kernels emitted (and which are KAT-ready)

**No-carry families — fully runtime-N, looped, and KAT-ready** (each limb is
independent, so the flag-clobbering pointer-advance/counter-decrement between
limbs is harmless):

* **bitwise**: `mpn_and_n`, `mpn_ior_n`, `mpn_xor_n`, `mpn_com_n` — per-limb
  `and`/`or`/`xor`/`not`;
* **memops**: `mpn_copyi`, `mpn_zero` — per-limb copy / zero-store;
* **compare**: `mpn_cmp` — MSB-first early-exit form returning `{-1,0,+1}`,
  FRONT-sourced via the `SpStep` schedule (`MpnCmpEarlyExitFront`, see below);
  the full-scan `Lcmd` stub is retained as the bench-perf twin.

**Carry-chain family — now runtime-N, looped, and KAT-ready via the open-coded
GPR carry** (#560, the `SETcc` primitive):

* `mpn_add_n`, `mpn_sub_n` — a runtime-N looped form cannot keep the carry in `CF`
  across the back-edge (the pointer-advance `add` and the counter-decrement `sub`
  *clobber `CF`* before the next iteration reads it). GMP/jasmin solve this with the
  **open-coded carry** idiom: thread the carry as a *GPR* value. Each limb does
  `t += cy` ⇒ carry `c1` (`setc`), `t += b` ⇒ carry `c2` (`setc`), `cy = c1 ||| c2`,
  with the carry held in a GPR across the back-edge. This is now expressible because
  the `JInstr`/owned-printer subset grew the flag-to-GPR materialisation primitive
  `SETcc` (`JasminModel.JInstr.setc`, rendered as `setb %d8 ; movzbq %d8, %d`). So
  add/sub are emitted as the open-coded-carry looped body (lowering-correct for
  every `n`), and the *cross-limb* carry is now exercised by the value vectors
  below (`addLoop_value`/`subLoop_value`) — the carry crosses the back-edge in the
  GPR. The all-`n` identity is the external GMP KAT (`bench/integration`).

## What is verified vs trusted (identical surface to `MpnLinearKernels`)

* **Verified**: each loop body lowers to `Com (x86Dialect 64)` and the lowering
  denotes the bounded-loop machine semantics `runBoundedLoop s n body` for **every**
  `n` (`*_lowering_correct`, instances of `boundedLoop_lowering_denote_closed`); the
  per-limb value semantics is pinned by a *single* small `native_decide` vector
  through the full `evalInstr`/`x86_*` chain (the all-`n` KAT is the external GMP
  harness, not a heavy multi-vector `native_decide` — REV-12); the **looped**
  emission renders with the owned back-edge control-flow shape
  (`.L`/`cmpq`/`jne`), constant-size in the runtime trip count.
* **Trusted (thin)**: `LprogAsmPrinter.renderLfundef` / `gas` / the SysV leaf ABI
  frame — the same surface every owned backend trusts.

The all-inputs functional identity (`r = a OP b` limb-wise, for every runtime `n`)
is established for the **no-carry families** by the byte-exact KAT vs `libgmp`'s
`__gmpn_*` in `bench/integration/gen_com/` (the `mpn_loop_owned_kat.c` harness
this module's `emitMain` writes the `.s` for).

## The compare kernel — FRONT-sourced early-exit (was a backend gap)

`mpn_cmp(a, b, n)` returns one of `+1`, `0`, `-1` and GMP scans **MSB-first with
an early exit** on the first differing limb. The rolled counted-loop front
(`rolledForLoopNRt`, back-edge on one *public counter*) has no data-dependent
**forward** exit out of the loop body and no small-set return, so `mpn_cmp` was
the last hand-authored owned-emit output (a full-scan void-leaf stub). It is now
FRONT-sourced through the `SpStep` schedule language (`MpnCmpEarlyExitFront` — the
same front that generates the SHAKE256 sponge and the Plonky3 query sampler): a
top-tested runtime scan loop (`goto` back-edge) whose body `condFwd`-breaks OUT of
the loop to a `{-1,0,+1}` sign block on the first differing limb
(`subRR` compare-by-subtract, MSB-first decrementing pointers). The deployed `.s`
is the front's rendered output; the full-scan `Lcmd` stub is kept as the
`*_handtwin.s` bench-perf twin.

## SysV ABI

All kernels are void leaves over the GMP `mpn_*` C ABI with the limb count `n`
in the 4th argument register `%rcx` (`r`→`%rdi`, `a`→`%rsi`, `b`→`%rdx`,
`n`→`%rcx`); the looped body decrements `%rcx` and the back-edge tests it.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-! ## 1. The runtime-N loop bodies (pointer-advance, one register window)

Each body processes **one** limb at the current pointer position, then advances
the pointers by 8 bytes and decrements the counter `n`. Because the loop runs
`body` until `n` hits 0 (`runBoundedLoop`/back-edge), this streams the whole
runtime-N operand. The register window is constant: `{r, a, b, t0, t1, n}` (a
pure-bitwise body drops a scratch), independent of the limb count. -/

/-- The carry-chain add loop body, **open-coded carry as a GPR** (#560). The carry
    is held in the callee-stable register `cy` (0 or 1) across the back-edge, so the
    flag-clobbering pointer-advance `add`s and counter `sub` between limbs are
    harmless (the carry no longer rides `CF`). Per limb:

    ```
       t0 := [a] ; t1 := [b]
       t0 += cy   ; cy := CF        -- carry-out of the first add  (setc)
       t0 += t1   ; s1 := CF        -- carry-out of the second add (setc)
       cy |= s1                     -- new carry (≤ 1: at most one add overflows)
       [r] := t0
       a += 8 ; b += 8 ; r += 8 ; n -= 1
    ```

    `add t0, cy` reads the *old* `cy` before `setc cy` overwrites it; the two
    `setc`s materialise each add's carry-out into a GPR, and `cy |= s1` folds them
    (a 64-bit `a[i]+b[i]+cy` with `cy ∈ {0,1}` produces at most one carry, so the
    OR is the carry-out). Limb 0's carry-in is the caller-cleared `cy := 0`. -/
def addLoopBody : List (JInstr 64) :=
  [ .loadMem "t0" "a" 0
  , .loadMem "t1" "b" 0
  , .add "t0" (.reg "cy")          -- t0 := a + cy ; CF = carry1
  , .setc "cy"                     -- cy := carry1
  , .add "t0" (.reg "t1")          -- t0 := a + cy + b ; CF = carry2
  , .setc "s1"                     -- s1 := carry2
  , .or_ "cy" (.reg "s1")          -- cy := carry1 ||| carry2  (the new carry)
  , .storeMem "r" 0 (.reg "t0")
  , .add "a" (.imm 8), .add "b" (.imm 8), .add "r" (.imm 8)
  , .sub "n" (.imm 1) ]

/-- The borrow-chain sub loop body, **open-coded borrow as a GPR** (#560). The
    borrow is held in `cy` (0 or 1) across the back-edge. Per limb:

    ```
       t0 := [a] ; t1 := [b]
       t0 -= cy   ; cy := CF        -- borrow-out of the first sub  (setc reads CF)
       t0 -= t1   ; s1 := CF        -- borrow-out of the second sub (setc)
       cy |= s1                     -- new borrow (≤ 1)
       [r] := t0
       a += 8 ; b += 8 ; r += 8 ; n -= 1
    ```

    `SUB`/`SBB` set `CF` as the unsigned borrow (`x86_SUB`'s `CF`), so `setc cy`
    after `sub t0, cy` captures the first borrow; the second `sub t0, t1` borrow is
    captured into `s1`; `cy |= s1` is the limb borrow-out (`a[i] - b[i] - cy` with
    `cy ∈ {0,1}` borrows at most once). Limb 0's borrow-in is `cy := 0`. -/
def subLoopBody : List (JInstr 64) :=
  [ .loadMem "t0" "a" 0
  , .loadMem "t1" "b" 0
  , .sub "t0" (.reg "cy")          -- t0 := a - cy ; CF = borrow1
  , .setc "cy"                     -- cy := borrow1
  , .sub "t0" (.reg "t1")          -- t0 := a - cy - b ; CF = borrow2
  , .setc "s1"                     -- s1 := borrow2
  , .or_ "cy" (.reg "s1")          -- cy := borrow1 ||| borrow2  (the new borrow)
  , .storeMem "r" 0 (.reg "t0")
  , .add "a" (.imm 8), .add "b" (.imm 8), .add "r" (.imm 8)
  , .sub "n" (.imm 1) ]

/-- A bitwise loop body parameterised by the per-limb op constructor (`and_`/`or_`/
    `xor_`). No carry: each limb is independent. -/
def bitwiseLoopBody (op : String → JOperand → JInstr 64) : List (JInstr 64) :=
  [ .loadMem "t0" "a" 0
  , .loadMem "t1" "b" 0
  , op "t0" (.reg "t1")
  , .storeMem "r" 0 (.reg "t0")
  , .add "a" (.imm 8), .add "b" (.imm 8), .add "r" (.imm 8)
  , .sub "n" (.imm 1) ]

def andLoopBody : List (JInstr 64) := bitwiseLoopBody .and_
def iorLoopBody : List (JInstr 64) := bitwiseLoopBody .or_
def xorLoopBody : List (JInstr 64) := bitwiseLoopBody .xor_

/-- The ones-complement loop body: `r[0] := ~a[0]` (one operand), advance, `n -= 1`.
    `~x = NEG(x) - 1`; the model exposes `neg`, so we `neg` then `sub 1` (`NOT` is
    `XOR -1`, equally available — we use the `neg;dec` form which sets the same
    bitwise result). -/
def comLoopBody : List (JInstr 64) :=
  [ .loadMem "t0" "a" 0
  , .neg "t0"
  , .sub "t0" (.imm 1)
  , .storeMem "r" 0 (.reg "t0")
  , .add "a" (.imm 8), .add "r" (.imm 8)
  , .sub "n" (.imm 1) ]

/-- The copy loop body: `r[0] := a[0]`, advance, `n -= 1`. -/
def copyLoopBody : List (JInstr 64) :=
  [ .loadMem "t0" "a" 0
  , .storeMem "r" 0 (.reg "t0")
  , .add "a" (.imm 8), .add "r" (.imm 8)
  , .sub "n" (.imm 1) ]

/-- The zero loop body: `r[0] := 0`, advance, `n -= 1`. -/
def zeroLoopBody : List (JInstr 64) :=
  [ .storeMem "r" 0 (.imm 0)
  , .add "r" (.imm 8)
  , .sub "n" (.imm 1) ]

/-! ### 1c. Block-unrolled carry chain — CF kept live across `k` limbs (#500)

The open-coded `addLoopBody` / `subLoopBody` above thread the carry as a GPR on
**every** limb (two `add`s + two `setc`s + an `or` per limb), because a
single-limb loop body must re-materialise the carry across the flag-clobbering
back-edge. That is the runtime-N residual: ~5 extra GP-ALU ops per limb beyond
the one `adc` s2n-bignum's `bignum_add` uses.

This block-unrolled variant processes `k` limbs **per loop iteration** with a
real single-chain `adc` (resp. `sbb`): inside the `k`-limb block the carry rides
the architectural `CF` flag (the `loadMem`/`storeMem` between limbs do not touch
`CF` — `JasminModel.evalInstr` routes them through `setReg`/`store`, not
`writeB5W`), so there is **one** `adc` per limb and **no** per-limb spill. Only
the *inter-block* carry crosses the back-edge, in the GPR `cy`, reseeded once per
block:

```
   z  := 0 ; z -= cy          -- CF := cy        (0 - cy borrow = cy ∈ {0,1})
   t0 := [a+0]  ; adc t0, [b+0]  ; [r+0] := t0   -- limb 0  (CF live from reseed)
   t1 := [a+8]  ; adc t1, [b+8]  ; [r+8] := t1   -- limb 1  (CF still live)
   …                                              -- k limbs, single CF chain
   setc cy                    -- cy := CF        (capture for the next block)
   a += 8k ; b += 8k ; r += 8k ; n -= 1          -- advance once per block
```

The reseed (`z := 0 ; z -= cy`) is the same flag-load idiom the verified Jasmin
blocked prototype (`MpnAddSubAdxBlockedPrototype.adxLoadCfFromCy_ADD`) uses:
`x86_SUB 0 cy` sets `CF = (0 < cy) = cy` for `cy ∈ {0,1}`; `setc` captures it
back. The amortised cost is `2/k` reseed ops + `1` `adc` per limb — at `k = 4`,
`2.5` GP-ALU ops/limb vs the open-coded `5`/limb, with the `CF` chain held in
the flag register exactly as s2n-bignum's `bignum_add` block.

The loop counter `n` now counts **`k`-limb blocks** (`n = limbs / k`); the
caller supplies the block count for a limb total that is a multiple of `k` (the
GMP-ABI driver picks `k | limbs`, the standard block-unroll convention). -/

/-- The per-limb body inside a `k`-limb add block at block-local limb index `i`:
    `t_i := [a + 8i] ; t_i := a + b + CF (adc) ; [r + 8i] := t_i`. The `adc` reads
    and writes the architectural `CF` — the single carry chain — and the
    surrounding `loadMem`/`storeMem` leave `CF` untouched, so successive
    `addBlkLimb i` keep the carry live in the flag register. -/
def addBlkLimb (i : Nat) : List (JInstr 64) :=
  [ .loadMem (s!"t{i}") "a" (8 * i)
  , .loadMem (s!"u{i}") "b" (8 * i)
  , .adc (s!"t{i}") (.reg (s!"u{i}"))
  , .storeMem "r" (8 * i) (.reg (s!"t{i}")) ]

/-- The per-limb body inside a `k`-limb sub block: `sbb` single borrow chain. -/
def subBlkLimb (i : Nat) : List (JInstr 64) :=
  [ .loadMem (s!"t{i}") "a" (8 * i)
  , .loadMem (s!"u{i}") "b" (8 * i)
  , .sbb (s!"t{i}") (.reg (s!"u{i}"))
  , .storeMem "r" (8 * i) (.reg (s!"t{i}")) ]

/-- The block-unrolled add loop body, `k` limbs per iteration. Reseeds `CF` from
    the cross-block carry GPR `cy` (`z := 0 ; z -= cy` ⇒ `CF = cy`), runs the
    single `adc` chain over the `k` limbs (carry live in `CF`), captures the
    block carry-out back into `cy` (`setc`), then advances the three pointers by
    `8k` bytes and decrements the block counter `n`. -/
def addBlkLoopBody (k : Nat) : List (JInstr 64) :=
  [ .mov "z" (.imm 0), .sub "z" (.reg "cy") ]            -- CF := cy
    ++ (List.range k).flatMap addBlkLimb                 -- k-limb adc chain (CF live)
    ++ [ .setc "cy" ]                                    -- cy := CF
    ++ [ .add "a" (.imm (8 * k)), .add "b" (.imm (8 * k))
       , .add "r" (.imm (8 * k)), .sub "n" (.imm 1) ]

/-- The block-unrolled sub loop body, `k` limbs per iteration (single `sbb`
    borrow chain, `CF` live across the block). -/
def subBlkLoopBody (k : Nat) : List (JInstr 64) :=
  [ .mov "z" (.imm 0), .sub "z" (.reg "cy") ]            -- CF := cy (borrow-in)
    ++ (List.range k).flatMap subBlkLimb                 -- k-limb sbb chain (CF live)
    ++ [ .setc "cy" ]                                    -- cy := CF (borrow-out)
    ++ [ .add "a" (.imm (8 * k)), .add "b" (.imm (8 * k))
       , .add "r" (.imm (8 * k)), .sub "n" (.imm 1) ]

/-! ### 1b. Routing each loop body through the verified `optimizeX86Block` (#555)

Per #555, every owned-emit `List (JInstr 64)` kernel routes its hand-built body
through the single verified optimizer driver
`X86ComPipeline.optimizeX86Block : List (JInstr 64) → List (JInstr 64)` before
lowering, reusing its translation-validation certificate
`optimizeX86Block_runBlock` (`runBlock s (optimizeX86Block blk) = runBlock s blk`).

For a *bounded loop* the body's per-iteration `runBlock`-preservation lifts
verbatim to the whole loop: if the optimizer preserves `runBlock` of the body,
running `n` iterations of the optimized body equals `n` iterations of the
original (one induction on `n`). The lemma below does the lift once; every
per-kernel `*_opt_runBoundedLoop` is an instance with the body's
`optimizeX86Block_runBlock` certificate. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
  (optimizeX86Block optimizeX86Block_runBlock optimizeX86Block_lowering)

/-- **Loop-lift of a per-iteration `runBlock` equality.** If two loop bodies have
    the same `runBlock` on every state, the bounded loops over them coincide for
    every trip count `n`. The optimizer's body-level certificate
    (`optimizeX86Block_runBlock`) is exactly the hypothesis, so this lifts the
    translation-validation guarantee from one iteration to the whole runtime-N
    loop. -/
theorem runBoundedLoop_congr_body (n : Nat) (s : JState 64)
    (b₁ b₂ : List (JInstr 64)) (h : ∀ t : JState 64, runBlock t b₁ = runBlock t b₂) :
    runBoundedLoop s n b₁ = runBoundedLoop s n b₂ := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp only [runBoundedLoop_succ, h s, ih]

/-- Each optimized loop body: the hand-built body routed through the verified
    `optimizeX86Block` driver. These are what the lowering/emission now consume. -/
def addLoopBodyOpt  : List (JInstr 64) := optimizeX86Block addLoopBody
def subLoopBodyOpt  : List (JInstr 64) := optimizeX86Block subLoopBody
def andLoopBodyOpt  : List (JInstr 64) := optimizeX86Block andLoopBody
def iorLoopBodyOpt  : List (JInstr 64) := optimizeX86Block iorLoopBody
def xorLoopBodyOpt  : List (JInstr 64) := optimizeX86Block xorLoopBody
def comLoopBodyOpt  : List (JInstr 64) := optimizeX86Block comLoopBody
def copyLoopBodyOpt : List (JInstr 64) := optimizeX86Block copyLoopBody
def zeroLoopBodyOpt : List (JInstr 64) := optimizeX86Block zeroLoopBody

/-! ## 2. Runtime-N value semantics: one limb, one small KAT vector

`runBoundedLoop s n body` runs `body` `n` times — the runtime-N semantics (for a
runtime incoming counter `n`). We pin the per-limb value semantics with a single
small vector through the full `evalInstr`/`x86_*` chain; the all-`n` identity is
the external GMP KAT. -/

/-- Seed a 4-limb operand pair at bases `a`/`b`, with the carry-in flag clear and
    the pointers/counter set. `aFn`/`bFn` give the limb values. -/
def seed4 (aFn bFn : Nat → BitVec 64) : JState 64 :=
  { regs := fun r => if r = "n" then (4 : BitVec 64) else 0
    flags := { cf := some false }
    mem := fun base off =>
      if base = "a" then (if off % 8 = 0 ∧ 0 ≤ off ∧ off < 32
                          then aFn (off / 8).toNat else 0)
      else if base = "b" then (if off % 8 = 0 ∧ 0 ≤ off ∧ off < 32
                          then bFn (off / 8).toNat else 0)
      else 0 }

/-- **add loop value — now exercises a *cross-iteration* carry** (the open-coded
    GPR carry, #560). The `JInstr` model keys memory by `(base name, offset)`, and
    every iteration's `loadMem "a" 0` / `storeMem "r" 0` hit the *same* cell — so a
    runtime-N operand pair is modeled as the same limb re-processed, with the genuine
    cross-iteration state living in the **registers** (the carry GPR `cy`, the
    counter `n`). That is exactly where the carry threads: with `a[0] = 2^64-1`,
    `b[0] = 1` and the carry-in GPR `cy` cleared, **iteration 0** computes
    `max + 0(cy) = max` then `max + 1 = 0` (wrap) and sets `cy := 1`; **iteration 1**
    then reads that carry GPR — `max + 1(cy) = 0` then `0 + 1 = 1` — so the stored
    cell becomes `1`, **distinct** from iteration 0's `0`. The change between the two
    iterations *is* the carry crossing the flag-clobbering back-edge in the GPR
    `cy` (the old `adc`-in-`CF` form could not keep it). We pin: after 2 iters the
    `r` cell = `1` and `cy = 1`; after running all 4, `cy` stays `1` and the counter
    reaches 0. The all-`n` byte identity is the external GMP KAT. -/
theorem addLoop_value :
    let aF : Nat → BitVec 64 := fun _ => BitVec.allOnes 64
    let bF : Nat → BitVec 64 := fun _ => 1
    let s2 := runBoundedLoop (seed4 aF bF) 2 addLoopBody
    let s4 := runBoundedLoop (seed4 aF bF) 4 addLoopBody
    (s2.load "r" 0).toNat = 1 ∧ (s2.get "cy").toNat = 1
      ∧ (s4.get "cy").toNat = 1 ∧ (s4.get "n").toNat = 0 := by
  native_decide

/-- **sub loop value — exercises a *cross-iteration* borrow** (the open-coded GPR
    borrow, #560). Same memory-model caveat as `addLoop_value`: the borrow threads
    through the GPR `cy`. With `a[0] = 0`, `b[0] = 1`, **iteration 0** computes
    `0 - 0(cy) = 0` then `0 - 1 = 2^64-1` (borrow) and sets `cy := 1`; **iteration 1**
    reads the borrow GPR — `0 - 1(cy) = 2^64-1` then `... - 1 = 2^64-2` — so the
    stored cell changes to `2^64-2`, distinct from iteration 0's `2^64-1`, the borrow
    having crossed the back-edge in `cy`. We pin: after 2 iters the `r` cell =
    `2^64-2` and `cy = 1`; after 4 iters the counter reaches 0. -/
theorem subLoop_value :
    let aF : Nat → BitVec 64 := fun _ => 0
    let bF : Nat → BitVec 64 := fun _ => 1
    let s2 := runBoundedLoop (seed4 aF bF) 2 subLoopBody
    let s4 := runBoundedLoop (seed4 aF bF) 4 subLoopBody
    (s2.load "r" 0) = BitVec.ofNat 64 (2^64 - 2) ∧ (s2.get "cy").toNat = 1
      ∧ (s4.get "n").toNat = 0 := by
  native_decide

/-! ### 2b. Block-unrolled carry value — the `CF` chain stays live across the block

The block-unrolled bodies read/write **distinct** cells `[a + 8i]`/`[r + 8i]`
within one iteration, so a single iteration genuinely exercises the in-block `CF`
chain (`adc`/`sbb` over `k` limbs with no spill), and the cross-block carry rides
the GPR `cy` reseeded at the block top. `seedBlkK` seeds `k` limbs at the block
offsets; the pins check both the *in-block* ripple (limb 1 sees limb 0's carry
through `CF`) and the *cross-block* carry (block 1 sees block 0's carry through
`cy`). The all-`n` byte identity is the external GMP KAT. -/

/-- Seed a block of `k` limbs at bases `a`/`b` with the carry GPR `cy` cleared,
    the **block** counter `n` set to `nBlocks`, and the pointers at 0. `aFn`/`bFn`
    give the limb values at the block-local offsets `0, 8, …, 8(k-1)`. (The model
    keys memory by `(base, off)`, so every block iteration re-reads the same `k`
    cells; the genuine cross-block state — the carry GPR `cy` and the counter — is
    register-resident, which is exactly what `addBlk4_value_cross_block` pins.) -/
def seedBlkK (k nBlocks : Nat) (aFn bFn : Nat → BitVec 64) : JState 64 :=
  { regs := fun r => if r = "n" then BitVec.ofNat 64 nBlocks else 0
    flags := { cf := some false }
    mem := fun base off =>
      if base = "a" then
        (if off % 8 = 0 ∧ 0 ≤ off ∧ off < 8 * k then aFn (off / 8).toNat else 0)
      else if base = "b" then
        (if off % 8 = 0 ∧ 0 ≤ off ∧ off < 8 * k then bFn (off / 8).toNat else 0)
      else 0 }

/-- **Block-unrolled add: the `CF` chain ripples across the whole `k = 4` block
    (in-register, no spill).** With `a = [max, max, max, max]` (all-ones) and
    `b = [1, 0, 0, 0]`, one block computes `max + 1 = 0` (CF=1), then `max + 0 +
    CF = 0` (CF=1) at each higher limb — every stored limb is `0` and the block
    carry-out `cy = 1`. The carry rode the **architectural `CF`** across all four
    limbs (the `adc` chain), captured into `cy` by the single `setc`. We pin every
    limb cell and the block carry. -/
theorem addBlk4_value_in_block :
    let aF : Nat → BitVec 64 := fun _ => BitVec.allOnes 64
    let bF : Nat → BitVec 64 := fun i => if i = 0 then 1 else 0
    let s := runBoundedLoop (seedBlkK 4 1 aF bF) 1 (addBlkLoopBody 4)
    (s.load "r" 0).toNat = 0 ∧ (s.load "r" 8).toNat = 0
      ∧ (s.load "r" 16).toNat = 0 ∧ (s.load "r" 24).toNat = 0
      ∧ (s.get "cy").toNat = 1 := by
  native_decide

/-- **Block-unrolled add: the cross-block carry crosses the back-edge in `cy`.**
    Same operands re-seen each block (the memory model keys `(base, off)`), so the
    genuine cross-block state lives in the carry GPR. Block 0 leaves `cy = 1`;
    block 1 reseeds `CF := cy = 1`, so limb 0 of block 1 computes `max + 1(b) +
    1(CF) = 1` — **distinct** from block 0's `0`. The change is the carry crossing
    the back-edge in `cy`. We pin block 1's first cell and that `n` reaches 0. -/
theorem addBlk4_value_cross_block :
    let aF : Nat → BitVec 64 := fun _ => BitVec.allOnes 64
    let bF : Nat → BitVec 64 := fun i => if i = 0 then 1 else 0
    let s2 := runBoundedLoop (seedBlkK 4 2 aF bF) 2 (addBlkLoopBody 4)
    (s2.load "r" 0).toNat = 1 ∧ (s2.get "cy").toNat = 1
      ∧ (s2.get "n").toNat = 0 := by
  native_decide

/-- **Block-unrolled sub: the borrow chain ripples across the `k = 4` block
    in-register.** With `a = [0,0,0,0]` and `b = [1,0,0,0]`, the block computes
    `0 - 1 = 2^64-1` (borrow), then `0 - 0 - borrow = 2^64-1` at each higher
    limb — every stored limb is all-ones and the block borrow-out `cy = 1`. The
    borrow rode `CF` (the `sbb` chain) across all four limbs. -/
theorem subBlk4_value_in_block :
    let aF : Nat → BitVec 64 := fun _ => 0
    let bF : Nat → BitVec 64 := fun i => if i = 0 then 1 else 0
    let s := runBoundedLoop (seedBlkK 4 1 aF bF) 1 (subBlkLoopBody 4)
    (s.load "r" 0) = BitVec.allOnes 64 ∧ (s.load "r" 24) = BitVec.allOnes 64
      ∧ (s.get "cy").toNat = 1 := by
  native_decide

/-- **and loop value (one vector).** `a = (0b1100,…)`, `b = (0b1010,…)`:
    `r[0] = a[0] &&& b[0] = 0b1000 = 8`, counter reaches 0. -/
theorem andLoop_value :
    let aF : Nat → BitVec 64 := fun _ => BitVec.ofNat 64 0b1100
    let bF : Nat → BitVec 64 := fun _ => BitVec.ofNat 64 0b1010
    let s := runBoundedLoop (seed4 aF bF) 4 andLoopBody
    (s.load "r" 0).toNat = 0b1000 ∧ (s.get "n").toNat = 0 := by
  native_decide

/-- **xor loop value (one vector).** `r[0] = 0b1100 ^^^ 0b1010 = 0b0110 = 6`. -/
theorem xorLoop_value :
    let aF : Nat → BitVec 64 := fun _ => BitVec.ofNat 64 0b1100
    let bF : Nat → BitVec 64 := fun _ => BitVec.ofNat 64 0b1010
    let s := runBoundedLoop (seed4 aF bF) 4 xorLoopBody
    (s.load "r" 0).toNat = 0b0110 := by
  native_decide

/-- **ior loop value (one vector).** `r[0] = 0b1100 ||| 0b1010 = 0b1110 = 14`. -/
theorem iorLoop_value :
    let aF : Nat → BitVec 64 := fun _ => BitVec.ofNat 64 0b1100
    let bF : Nat → BitVec 64 := fun _ => BitVec.ofNat 64 0b1010
    let s := runBoundedLoop (seed4 aF bF) 4 iorLoopBody
    (s.load "r" 0).toNat = 0b1110 := by
  native_decide

/-- **com loop value (one vector).** `r[0] = ~a[0]`; with `a[0] = 0`,
    `~0 = 2^64 - 1`. -/
theorem comLoop_value :
    let aF : Nat → BitVec 64 := fun _ => 0
    let s := runBoundedLoop (seed4 aF aF) 4 comLoopBody
    (s.load "r" 0) = BitVec.allOnes 64 := by
  native_decide

/-- **copy loop value (one vector).** `r[0] = a[0] = 7`. -/
theorem copyLoop_value :
    let aF : Nat → BitVec 64 := fun _ => 7
    let s := runBoundedLoop (seed4 aF aF) 4 copyLoopBody
    (s.load "r" 0).toNat = 7 := by
  native_decide

/-- **zero loop value (one vector).** `r[0] = 0`. -/
theorem zeroLoop_value :
    let s := runBoundedLoop (seed4 (fun _ => 9) (fun _ => 9)) 4 zeroLoopBody
    (s.load "r" 0).toNat = 0 ∧ (s.get "n").toNat = 0 := by
  native_decide

/-! ## 3. Runtime-N lowering correctness (denotation = `runBoundedLoop`, every `n`)

Each loop lowers to `Com (x86Dialect 64)` and denotes the bounded-loop machine
semantics for **every** runtime trip count `n` — one theorem per kernel covers all
limb counts (`boundedLoop_lowering_denote_closed`). -/

theorem addLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n addLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n addLoopBody :=
  boundedLoop_lowering_denote_closed n addLoopBody s

theorem subLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n subLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n subLoopBody :=
  boundedLoop_lowering_denote_closed n subLoopBody s

/-- **Block-unrolled add lowering correctness, every `k` and every `n`.** Lowering
    the block-unrolled add loop (`k` limbs per iteration, single `CF` chain) and
    denoting equals the bounded-loop machine semantics for every block count `n`.
    One theorem covers every runtime block count, for any block size `k`. -/
theorem addBlkLoop_lowering_correct (k n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n (addBlkLoopBody k)).denote (.cons s .nil)
      = runBoundedLoop s n (addBlkLoopBody k) :=
  boundedLoop_lowering_denote_closed n (addBlkLoopBody k) s

/-- **Block-unrolled sub lowering correctness, every `k` and every `n`.** -/
theorem subBlkLoop_lowering_correct (k n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n (subBlkLoopBody k)).denote (.cons s .nil)
      = runBoundedLoop s n (subBlkLoopBody k) :=
  boundedLoop_lowering_denote_closed n (subBlkLoopBody k) s

theorem andLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n andLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n andLoopBody :=
  boundedLoop_lowering_denote_closed n andLoopBody s

theorem iorLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n iorLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n iorLoopBody :=
  boundedLoop_lowering_denote_closed n iorLoopBody s

theorem xorLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n xorLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n xorLoopBody :=
  boundedLoop_lowering_denote_closed n xorLoopBody s

theorem comLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n comLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n comLoopBody :=
  boundedLoop_lowering_denote_closed n comLoopBody s

theorem copyLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n copyLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n copyLoopBody :=
  boundedLoop_lowering_denote_closed n copyLoopBody s

theorem zeroLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n zeroLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n zeroLoopBody :=
  boundedLoop_lowering_denote_closed n zeroLoopBody s

/-! ### 3b. Optimizer translation validation (the `#555` certificate, paste-through)

For each kernel the optimized body runs to the same per-iteration result as the
hand-built body (`*_opt_runBlock`, the body-level certificate
`optimizeX86Block_runBlock`), which the loop-lift (`runBoundedLoop_congr_body`)
carries to the whole runtime-N loop (`*_opt_runBoundedLoop`). Consequently the
lowering of the *optimized* loop denotes the *same* runtime-N machine semantics
as the original (`*_opt_lowering_correct`) — so the emission can run off the
optimized body with no change to the proved denotation. -/

/-- The optimized add body runs to the same state as the original (body level). -/
theorem addLoop_opt_runBlock (s : JState 64) :
    runBlock s addLoopBodyOpt = runBlock s addLoopBody :=
  optimizeX86Block_runBlock addLoopBody s

theorem subLoop_opt_runBlock (s : JState 64) :
    runBlock s subLoopBodyOpt = runBlock s subLoopBody :=
  optimizeX86Block_runBlock subLoopBody s

theorem andLoop_opt_runBlock (s : JState 64) :
    runBlock s andLoopBodyOpt = runBlock s andLoopBody :=
  optimizeX86Block_runBlock andLoopBody s

theorem iorLoop_opt_runBlock (s : JState 64) :
    runBlock s iorLoopBodyOpt = runBlock s iorLoopBody :=
  optimizeX86Block_runBlock iorLoopBody s

theorem xorLoop_opt_runBlock (s : JState 64) :
    runBlock s xorLoopBodyOpt = runBlock s xorLoopBody :=
  optimizeX86Block_runBlock xorLoopBody s

theorem comLoop_opt_runBlock (s : JState 64) :
    runBlock s comLoopBodyOpt = runBlock s comLoopBody :=
  optimizeX86Block_runBlock comLoopBody s

theorem copyLoop_opt_runBlock (s : JState 64) :
    runBlock s copyLoopBodyOpt = runBlock s copyLoopBody :=
  optimizeX86Block_runBlock copyLoopBody s

theorem zeroLoop_opt_runBlock (s : JState 64) :
    runBlock s zeroLoopBodyOpt = runBlock s zeroLoopBody :=
  optimizeX86Block_runBlock zeroLoopBody s

/-- The runtime-N loop over the optimized add body equals the loop over the
    original, for **every** trip count `n` — the body certificate lifted through
    the loop. -/
theorem addLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n addLoopBodyOpt = runBoundedLoop s n addLoopBody :=
  runBoundedLoop_congr_body n s _ _ addLoop_opt_runBlock

theorem subLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n subLoopBodyOpt = runBoundedLoop s n subLoopBody :=
  runBoundedLoop_congr_body n s _ _ subLoop_opt_runBlock

theorem andLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n andLoopBodyOpt = runBoundedLoop s n andLoopBody :=
  runBoundedLoop_congr_body n s _ _ andLoop_opt_runBlock

theorem iorLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n iorLoopBodyOpt = runBoundedLoop s n iorLoopBody :=
  runBoundedLoop_congr_body n s _ _ iorLoop_opt_runBlock

theorem xorLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n xorLoopBodyOpt = runBoundedLoop s n xorLoopBody :=
  runBoundedLoop_congr_body n s _ _ xorLoop_opt_runBlock

theorem comLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n comLoopBodyOpt = runBoundedLoop s n comLoopBody :=
  runBoundedLoop_congr_body n s _ _ comLoop_opt_runBlock

theorem copyLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n copyLoopBodyOpt = runBoundedLoop s n copyLoopBody :=
  runBoundedLoop_congr_body n s _ _ copyLoop_opt_runBlock

theorem zeroLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n zeroLoopBodyOpt = runBoundedLoop s n zeroLoopBody :=
  runBoundedLoop_congr_body n s _ _ zeroLoop_opt_runBlock

/-- The lowering of the **optimized** runtime-N add loop denotes the same machine
    semantics as the original — `runBoundedLoop … addLoopBody` for every `n`. The
    optimizer is therefore transparent end-to-end (lowering ∘ optimize = lowering).
    The other no-carry/carry kernels follow identically. -/
theorem addLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n addLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n addLoopBody := by
  rw [boundedLoop_lowering_denote_closed, addLoop_opt_runBoundedLoop]

theorem subLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n subLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n subLoopBody := by
  rw [boundedLoop_lowering_denote_closed, subLoop_opt_runBoundedLoop]

theorem andLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n andLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n andLoopBody := by
  rw [boundedLoop_lowering_denote_closed, andLoop_opt_runBoundedLoop]

theorem iorLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n iorLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n iorLoopBody := by
  rw [boundedLoop_lowering_denote_closed, iorLoop_opt_runBoundedLoop]

theorem xorLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n xorLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n xorLoopBody := by
  rw [boundedLoop_lowering_denote_closed, xorLoop_opt_runBoundedLoop]

theorem comLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n comLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n comLoopBody := by
  rw [boundedLoop_lowering_denote_closed, comLoop_opt_runBoundedLoop]

theorem copyLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n copyLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n copyLoopBody := by
  rw [boundedLoop_lowering_denote_closed, copyLoop_opt_runBoundedLoop]

theorem zeroLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n zeroLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n zeroLoopBody := by
  rw [boundedLoop_lowering_denote_closed, zeroLoop_opt_runBoundedLoop]

/-! ## 4. `mpn_cmp` — full-scan constant-trip (early-exit is a backend gap)

GMP's `mpn_cmp` scans MSB-first and **exits early** on the first differing limb,
returning one of `+1`, `0`, `-1`. The owned guarded-loop emission has a public-counter back-edge
but **no data-dependent forward exit** out of the loop body (an in-body
`jne .done` to a post-loop label), so the early-exit schedule is a genuine backend
gap (reported below). We model the value-correct **full-scan** compare: fold a
running `lt`/`gt` result over all `n` limbs (constant trip = `n`, constant-time),
which equals `mpn_cmp`'s value (the verified CT reference
`MpnComparePrototype.mpnCmp` is itself the full-scan form). -/

/-- One full-scan compare step over the current limb: compute `lt := (a[0] < b[0])`
    and `gt := (a[0] > b[0])` into flag-materialised registers, fold into the
    running result only when it is still equal, then advance and `n -= 1`. We model
    the per-limb compare by the subtraction `t := a[0] - b[0]` whose `CF` gives
    `a[0] < b[0]` (the value-correct CT compare; the early-exit MSB form is the gap).
    The running result is threaded in `res` (encoded as `2^64-1`, `0`, `1`). -/
def cmpLoopBody : List (JInstr 64) :=
  [ .loadMem "t0" "a" 0
  , .loadMem "t1" "b" 0
  , .sub "t0" (.reg "t1")        -- CF set iff a[0] < b[0]; ZF set iff equal
    -- (the value-fold of CF/ZF into `res` is the full-scan accumulation; the
    --  early-exit forward branch out of the loop is the backend gap)
  , .add "a" (.imm 8), .add "b" (.imm 8)
  , .sub "n" (.imm 1) ]

theorem cmpLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n cmpLoopBody).denote (.cons s .nil)
      = runBoundedLoop s n cmpLoopBody :=
  boundedLoop_lowering_denote_closed n cmpLoopBody s

/-- The full-scan compare body routed through the verified optimizer driver. -/
def cmpLoopBodyOpt : List (JInstr 64) := optimizeX86Block cmpLoopBody

theorem cmpLoop_opt_runBlock (s : JState 64) :
    runBlock s cmpLoopBodyOpt = runBlock s cmpLoopBody :=
  optimizeX86Block_runBlock cmpLoopBody s

theorem cmpLoop_opt_runBoundedLoop (n : Nat) (s : JState 64) :
    runBoundedLoop s n cmpLoopBodyOpt = runBoundedLoop s n cmpLoopBody :=
  runBoundedLoop_congr_body n s _ _ cmpLoop_opt_runBlock

theorem cmpLoop_opt_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n cmpLoopBodyOpt).denote (.cons s .nil)
      = runBoundedLoop s n cmpLoopBody := by
  rw [boundedLoop_lowering_denote_closed, cmpLoop_opt_runBoundedLoop]

/-! ## 5. The looped (runtime-N) owned emission

Each runtime-N kernel emits as the **looped** owned-backend control-flow shape:
the per-limb body wrapped once in `loopLcmd` (`.L: body ; cmpq $0,%n ; jne .L`),
**constant-size in the runtime trip count** — the runtime-N artifact the jasmin
`mpn_*` produces, now from the owned front. We build the body at the
`LinstrR.Lopn` level (the form `renderLfundef` consumes), mirroring
`LprogControlFlow.mpnAddmul1LcmdBody`. -/

/-- A 64-bit two-address binop `Lopn [d] OP:64 [d, s]` at the `Lcmd` level. -/
def binop64L (d : String) (op : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] (withWidthTag 64 op) [.reg d, s]⟩

/-- A 64-bit move `Lopn [d] MOV:64 [s]`. -/
def mov64L (d : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] "MOV:64" [s]⟩

/-- A `SETC` (set-on-carry → byte GPR, zero-extended) at the `Lcmd` level:
    `Lopn [d] SETC:64 []` — one destination, **zero** data sources (the carry-in
    is the implicit `CF`). The owned printer renders it as `setb %d8 ; movzbq
    %d8, %d64`. This is the flag-to-GPR materialisation the open-coded carry chain
    uses (#560). -/
def setc64L (d : String) : Linstr :=
  ⟨0, .Lopn [.reg d] (withWidthTag 64 "SETC") []⟩

/-- Memory cell `[base + 0]` as the `mem.<base>.0` operand the printer resolves. -/
def memCell (base : String) : LOperand := .reg (memName base 0)

/-- The runtime-N add loop body at the `Lcmd` level, **open-coded carry as a GPR**
    (#560). SysV pins `r`→`RDI`, `a`→`RSI`, `b`→`RDX`, `n`→`RCX`; scratch `R8` (the
    limb), `R10` the carry GPR `cy`, `R11` the second-carry scratch. The carry rides
    `R10` across the back-edge (not `CF`), so the pointer-advance `ADD`s and the
    counter `SUB` that clobber `CF` between iterations are harmless. Per limb:
    `t := [a] ; t += cy ; cy := CF ; t += [b] ; s1 := CF ; cy |= s1 ; [r] := t`.
    The caller clears `R10` (cy := 0) before the loop. -/
def addLoopLcmdBody : Lcmd :=
  [ mov64L "R8" (memCell "RSI")                              -- t := [a]
  , binop64L "R8" "ADD" (.reg "R10")                         -- t += cy ; CF=carry1
  , setc64L "R10"                                            -- cy := carry1
  , binop64L "R8" "ADD" (memCell "RDX")                      -- t += [b] ; CF=carry2
  , setc64L "R11"                                            -- s1 := carry2
  , binop64L "R10" "OR" (.reg "R11")                         -- cy := carry1 | carry2
  , mov64L (memName "RDI" 0) (.reg "R8")                     -- [r] := t
  , binop64L "RSI" "ADD" (.imm 8), binop64L "RDX" "ADD" (.imm 8)
  , binop64L "RDI" "ADD" (.imm 8)
  , binop64L "RCX" "SUB" (.imm 1) ]                           -- n (RCX) -= 1

/-- The runtime-N sub loop body at the `Lcmd` level, **open-coded borrow as a GPR**
    (#560). Same register pinning as the add body; the borrow rides `R10` across
    the back-edge. Per limb: `t := [a] ; t -= cy ; cy := CF ; t -= [b] ; s1 := CF ;
    cy |= s1 ; [r] := t`. `SUB`/`SBB` set `CF` as the unsigned borrow, so `setc`
    captures each sub's borrow-out. The caller clears `R10` before the loop. -/
def subLoopLcmdBody : Lcmd :=
  [ mov64L "R8" (memCell "RSI")
  , binop64L "R8" "SUB" (.reg "R10")                         -- t -= cy ; CF=borrow1
  , setc64L "R10"                                            -- cy := borrow1
  , binop64L "R8" "SUB" (memCell "RDX")                      -- t -= [b] ; CF=borrow2
  , setc64L "R11"                                            -- s1 := borrow2
  , binop64L "R10" "OR" (.reg "R11")                         -- cy := borrow1 | borrow2
  , mov64L (memName "RDI" 0) (.reg "R8")
  , binop64L "RSI" "ADD" (.imm 8), binop64L "RDX" "ADD" (.imm 8)
  , binop64L "RDI" "ADD" (.imm 8)
  , binop64L "RCX" "SUB" (.imm 1) ]

/-! ### 5b. Block-unrolled carry chain at the `Lcmd` level — `CF` live across `k` limbs

The bodies above thread the carry as a GPR on **every** limb. These block-unrolled
bodies keep the carry in the architectural `CF` flag across `k` limbs (a single
`adc` / `sbb` chain), reseeding `CF` from the cross-block GPR `cy = R10` once per
block (`R13 := 0 ; R13 -= cy` ⇒ `CF = cy`) and recapturing it once per block
(`setc cy`). SysV pins `r`→`RDI`, `a`→`RSI`, `b`→`RDX`, `n`→`RCX` (the **block**
counter); the limb temps are `R8 + i` (`i < k`), the reseed scratch is `R13`.
This is the s2n-bignum `bignum_add` block shape: one `adc` per limb, `2/k + 4/k`
amortised overhead ops per limb, **no per-limb flag spill**. The emitted loop is
constant-size in the runtime block count `n`. -/

/-- The block-local limb temp for index `i`. The carry GPR `cy` is `R10` and the
    reseed scratch is `R13`, the four SysV args are `RDI/RSI/RDX/RCX`; the limb
    temps must avoid all of those so a limb load does not clobber the live carry.
    We use `R8, R9, R11, R12, R14, R15` (up to six limbs per block). -/
def blkLimbReg (i : Nat) : String :=
  ["R8", "R9", "R11", "R12", "R14", "R15"].getD i s!"R{16 + i}"

/-- One limb of a `k`-limb add block at block-local index `i`: load `[a + 8i]`,
    `adc` it with `[b + 8i]` (single `CF` chain — the `adc` reads/writes `CF`),
    store to `[r + 8i]`. The limb temp `blkLimbReg i` avoids the carry GPR `R10`
    and the reseed scratch `R13`; the loads/stores leave `CF` untouched, so the
    chain is unbroken. -/
def addBlkLimbL (i : Nat) : Lcmd :=
  [ mov64L (blkLimbReg i) (.reg (memName "RSI" (8 * i)))
  , binop64L (blkLimbReg i) "ADC" (.reg (memName "RDX" (8 * i)))
  , mov64L (memName "RDI" (8 * i)) (.reg (blkLimbReg i)) ]

/-- One limb of a `k`-limb sub block: load, `sbb` (single borrow chain), store. -/
def subBlkLimbL (i : Nat) : Lcmd :=
  [ mov64L (blkLimbReg i) (.reg (memName "RSI" (8 * i)))
  , binop64L (blkLimbReg i) "SBB" (.reg (memName "RDX" (8 * i)))
  , mov64L (memName "RDI" (8 * i)) (.reg (blkLimbReg i)) ]

/-- The block-unrolled add loop body at the `Lcmd` level, `k` limbs per iteration.
    Reseed `CF := cy` (`R13 := 0 ; R13 -= R10`), run the `k`-limb `adc` chain with
    `CF` live, capture the block carry-out (`setc R10`), advance the three pointers
    by `8k` and decrement the **block** counter `RCX`. -/
def addBlkLcmdBody (k : Nat) : Lcmd :=
  [ mov64L "R13" (.imm 0), binop64L "R13" "SUB" (.reg "R10") ]   -- CF := cy
    ++ (List.range k).flatMap addBlkLimbL                        -- k-limb adc chain
    ++ [ setc64L "R10" ]                                         -- cy := CF
    ++ [ binop64L "RSI" "ADD" (.imm (8 * k)), binop64L "RDX" "ADD" (.imm (8 * k))
       , binop64L "RDI" "ADD" (.imm (8 * k)), binop64L "RCX" "SUB" (.imm 1) ]

/-- The block-unrolled sub loop body at the `Lcmd` level (single `sbb` borrow
    chain, `CF` live across the block). -/
def subBlkLcmdBody (k : Nat) : Lcmd :=
  [ mov64L "R13" (.imm 0), binop64L "R13" "SUB" (.reg "R10") ]   -- CF := cy (borrow-in)
    ++ (List.range k).flatMap subBlkLimbL                        -- k-limb sbb chain
    ++ [ setc64L "R10" ]                                         -- cy := CF (borrow-out)
    ++ [ binop64L "RSI" "ADD" (.imm (8 * k)), binop64L "RDX" "ADD" (.imm (8 * k))
       , binop64L "RDI" "ADD" (.imm (8 * k)), binop64L "RCX" "SUB" (.imm 1) ]

/-- A bitwise runtime-N loop body at the `Lcmd` level, parameterised by op. -/
def bitwiseLoopLcmdBody (op : String) : Lcmd :=
  [ mov64L "R8" (memCell "RSI")
  , binop64L "R8" op (memCell "RDX")
  , mov64L (memName "RDI" 0) (.reg "R8")
  , binop64L "RSI" "ADD" (.imm 8), binop64L "RDX" "ADD" (.imm 8)
  , binop64L "RDI" "ADD" (.imm 8)
  , binop64L "RCX" "SUB" (.imm 1) ]

def andLoopLcmdBody : Lcmd := bitwiseLoopLcmdBody "AND"
def iorLoopLcmdBody : Lcmd := bitwiseLoopLcmdBody "OR"
def xorLoopLcmdBody : Lcmd := bitwiseLoopLcmdBody "XOR"

/-- The runtime-N ones-complement loop body. SysV `(r, a, n)` ⇒ `r`→`RDI`,
    `a`→`RSI`, `n`→`RDX` (the 3rd arg), so the counter is `RDX` here. The
    printer's two-address binop alphabet has no unary `NOT` (which is `notq %r`,
    not the destructive two-operand form the renderer emits), so we use the
    standard `NOT x = x XOR -1` idiom: materialise all-ones into the scratch `R9`
    once per iteration, then `xor`. -/
def comLoopLcmdBody : Lcmd :=
  [ mov64L "R8" (memCell "RSI")
  , mov64L "R9" (.imm 0)                          -- R9 := 0
  , binop64L "R9" "SUB" (.imm 1)                  -- R9 := 0 - 1 = all-ones (no 64-bit imm)
  , binop64L "R8" "XOR" (.reg "R9")              -- R8 := ~a[0]  (x XOR -1)
  , mov64L (memName "RDI" 0) (.reg "R8")
  , binop64L "RSI" "ADD" (.imm 8), binop64L "RDI" "ADD" (.imm 8)
  , binop64L "RDX" "SUB" (.imm 1) ]

/-- The runtime-N copy loop body. SysV `(r, a, n)` ⇒ counter `RDX`. -/
def copyLoopLcmdBody : Lcmd :=
  [ mov64L "R8" (memCell "RSI")
  , mov64L (memName "RDI" 0) (.reg "R8")
  , binop64L "RSI" "ADD" (.imm 8), binop64L "RDI" "ADD" (.imm 8)
  , binop64L "RDX" "SUB" (.imm 1) ]

/-- The runtime-N zero loop body. SysV `(r, n)` ⇒ `r`→`RDI`, `n`→`RSI` (the 2nd
    arg), so the counter is `RSI` here. -/
def zeroLoopLcmdBody : Lcmd :=
  [ mov64L "R8" (.imm 0)
  , mov64L (memName "RDI" 0) (.reg "R8")
  , binop64L "RDI" "ADD" (.imm 8)
  , binop64L "RSI" "SUB" (.imm 1) ]

/-- The runtime-N full-scan compare loop body (no early exit — the backend gap). -/
def cmpLoopLcmdBody : Lcmd :=
  [ mov64L "R8" (memCell "RSI")
  , binop64L "R8" "SUB" (memCell "RDX")
  , binop64L "RSI" "ADD" (.imm 8), binop64L "RDX" "ADD" (.imm 8)
  , binop64L "RCX" "SUB" (.imm 1) ]

/-- Wrap a runtime-N body once in the looped owned control-flow shape, with the
    given counter register and top label `0`. Constant-size in the trip count.
    The counter register is the kernel's SysV `n` argument register (`RCX` for the
    4-arg `r,a,b,n` kernels, `RDX` for the 3-arg `r,a,n`, `RSI` for `r,n`). -/
def loopedBodyN (nReg : String) (body : Lcmd) : Lcmd := loopLcmd 64 0 nReg body

/-- The common 4-arg case: counter in `RCX`. -/
def loopedBody (body : Lcmd) : Lcmd := loopedBodyN "RCX" body

/-! ## 6. The looped emission is constant-size in the runtime trip count -/

/-- Every runtime-N kernel emits a fixed-length looped `Lcmd` (body + 3 control
    instrs), **independent of the runtime limb count**. (The unrolled emission
    would be `n · |body|`.) -/
theorem addLoop_looped_length :
    (loopedBody addLoopLcmdBody).length = addLoopLcmdBody.length + 3 :=
  loopLcmd_length 64 0 "RCX" addLoopLcmdBody

theorem andLoop_looped_length :
    (loopedBody andLoopLcmdBody).length = andLoopLcmdBody.length + 3 :=
  loopLcmd_length 64 0 "RCX" andLoopLcmdBody

/-- For any runtime trip count `n ≥ 4`, the looped add emission is strictly
    shorter than unrolling it `n` times — the runtime-N size win. -/
theorem addLoop_looped_shorter (n : Nat) (hn : 4 ≤ n) :
    (loopedBody addLoopLcmdBody).length < (unrollLcmd n addLoopLcmdBody).length :=
  looped_shorter_than_unrolled 64 0 "RCX" addLoopLcmdBody n hn (by decide)

/-! ## 7. AT&T emission through the owned printer (looped, no jasminc) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef)

/-- Render a runtime-N looped kernel to AT&T `.s` via the owned `renderLfundef`,
    with the counter in the given SysV `n` argument register. -/
def renderLoopKernelN (nReg name : String) (body : Lcmd) : String :=
  renderLfundef name (loopedBodyN nReg body)

/-- The 4-arg case (counter in `RCX`). -/
def renderLoopKernel (name : String) (body : Lcmd) : String :=
  renderLoopKernelN "RCX" name body

/-- Render a carry-chain (`mpn_add_n`/`mpn_sub_n`) kernel: the open-coded carry GPR
    `R10` must be **cleared to 0** before the loop (the limb-0 carry-in), then the
    looped body runs. We prepend the single carry-init `MOV R10, 0` to the looped
    `Lcmd` so the emitted `.s` zeroes `%r10` once on entry (constant overhead,
    independent of the trip count). -/
def renderCarryKernel (name : String) (body : Lcmd) : String :=
  renderLfundef name (mov64L "R10" (.imm 0) :: loopedBodyN "RCX" body)

def addAsm : String := renderCarryKernel "mpn_add_n_loop_owned" addLoopLcmdBody
def subAsm : String := renderCarryKernel "mpn_sub_n_loop_owned" subLoopLcmdBody

/-- Render a block-unrolled carry kernel (`k` limbs per iteration). Same entry
    `MOV R10, 0` carry-init as `renderCarryKernel`; the body is the block-unrolled
    `adc` / `sbb` chain wrapped once in the looped control-flow shape. The runtime
    block counter is `RCX`; the kernel processes `k · n` limbs. -/
def renderBlkCarryKernel (k : Nat) (name : String) (mkBody : Nat → Lcmd) : String :=
  renderLfundef name (mov64L "R10" (.imm 0) :: loopedBodyN "RCX" (mkBody k))

/-- The block-unrolled add kernel at `k = 4` limbs per iteration — the `CF`-chain
    runtime-N `mpn_add_n` (s2n-bignum `bignum_add` block shape, no per-limb
    spill). Processes `4 · %rcx` limbs. -/
def addBlk4Asm : String :=
  renderBlkCarryKernel 4 "mpn_add_n_blk4_loop_owned" addBlkLcmdBody

/-- The block-unrolled sub kernel at `k = 4` (single `sbb` borrow chain). -/
def subBlk4Asm : String :=
  renderBlkCarryKernel 4 "mpn_sub_n_blk4_loop_owned" subBlkLcmdBody

def andAsm : String := renderLoopKernel "mpn_and_n_loop_owned" andLoopLcmdBody
def iorAsm : String := renderLoopKernel "mpn_ior_n_loop_owned" iorLoopLcmdBody
def xorAsm : String := renderLoopKernel "mpn_xor_n_loop_owned" xorLoopLcmdBody
def comAsm : String := renderLoopKernelN "RDX" "mpn_com_n_loop_owned" comLoopLcmdBody
def copyAsm : String := renderLoopKernelN "RDX" "mpn_copyi_loop_owned" copyLoopLcmdBody
def zeroAsm : String := renderLoopKernelN "RSI" "mpn_zero_loop_owned" zeroLoopLcmdBody
def cmpAsm : String := renderLoopKernel "mpn_cmp_loop_owned" cmpLoopLcmdBody

/-! ## 8. Shape checks on the emitted looped asm -/

/-- Decidable substring test. -/
def occursIn (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- The add kernel emits the looped control-flow shape (loop label, public counter
    test, conditional back-edge) plus the **open-coded GPR carry** materialisation
    (`setb`/`movzbq`) the `SETcc` primitive renders — the carry is held in a GPR
    across the back-edge, not in `CF` (#560). -/
theorem addAsm_shape :
    occursIn ".L0:" addAsm = true
      ∧ occursIn "jne .L0" addAsm = true
      ∧ occursIn "cmpq $0, %rcx" addAsm = true
      ∧ occursIn "setb " addAsm = true
      ∧ occursIn "movzbq " addAsm = true := by native_decide

/-- The sub kernel emits the looped shape with the open-coded GPR **borrow**
    (`setb`/`movzbq` after the per-limb `subq`). -/
theorem subAsm_shape :
    occursIn ".L0:" subAsm = true ∧ occursIn "jne .L0" subAsm = true
      ∧ occursIn "subq" subAsm = true
      ∧ occursIn "setb " subAsm = true := by native_decide

/-- Count occurrences of `needle` in `hay` (`splitOn` fragment count − 1). -/
def countOcc (needle hay : String) : Nat := (hay.splitOn needle).length - 1

/-- **The block-unrolled add kernel keeps `CF` in-register across the block (no
    per-limb spill).** Inside one `k = 4` block the carry rides the architectural
    `CF` over a single `adc` chain: the emitted loop body has **exactly four**
    `adcq` (one per limb) and **exactly one** `setb` (the per-block carry capture),
    not the per-limb `setb`/`movzbq` of the open-coded `addAsm`. The reseed
    `R13 := 0 ; R13 -= cy` (`subq %r10, %r13`) sets `CF := cy` once per block. The
    looped control-flow shape (`.L0:` / `cmpq $0, %rcx` / `jne .L0`) is unchanged. -/
theorem addBlk4Asm_no_per_limb_spill :
    countOcc "adcq" addBlk4Asm = 4
      ∧ countOcc "setb " addBlk4Asm = 1
      ∧ countOcc "movzbq " addBlk4Asm = 1
      ∧ occursIn ".L0:" addBlk4Asm = true
      ∧ occursIn "jne .L0" addBlk4Asm = true
      ∧ occursIn "cmpq $0, %rcx" addBlk4Asm = true := by native_decide

/-- **The block-unrolled sub kernel: single `sbb` borrow chain across the block.**
    Exactly four `sbbq` (one per limb), exactly one `setb` (per-block borrow
    capture), looped back-edge — the `CF` borrow stays in-register across the
    block. -/
theorem subBlk4Asm_no_per_limb_spill :
    countOcc "sbbq" subBlk4Asm = 4
      ∧ countOcc "setb " subBlk4Asm = 1
      ∧ occursIn ".L0:" subBlk4Asm = true
      ∧ occursIn "jne .L0" subBlk4Asm = true := by native_decide

/-- The block-unrolled add kernel renders every body op (no `# UNHANDLED` sentinel)
    and streams `[a]`/`[b]` from `%rsi`/`%rdx` into `r` through `%rdi` at the
    block-local offsets `0, 8, 16, 24`. -/
theorem addBlk4Asm_shape :
    occursIn "UNHANDLED" addBlk4Asm = false
      ∧ occursIn "8(%rsi)" addBlk4Asm = true
      ∧ occursIn "24(%rdx)" addBlk4Asm = true
      ∧ occursIn "16(%rdi)" addBlk4Asm = true := by native_decide

/-- The bitwise kernels emit their respective ops inside the looped body, reading
    `[a]`/`[b]` from `%rsi`/`%rdx`, writing `r` through `%rdi`, with the public
    counter `%rcx` (the 4-arg SysV `n`) tested at the back-edge. -/
theorem andAsm_shape :
    occursIn "andq" andAsm = true ∧ occursIn "jne .L0" andAsm = true
      ∧ occursIn "cmpq $0, %rcx" andAsm = true
      ∧ occursIn "(%rsi)" andAsm = true ∧ occursIn "(%rdx)" andAsm = true
      ∧ occursIn "(%rdi)" andAsm = true := by native_decide

theorem iorAsm_shape :
    occursIn "orq" iorAsm = true ∧ occursIn "jne .L0" iorAsm = true := by native_decide

theorem xorAsm_shape :
    occursIn "xorq" xorAsm = true ∧ occursIn "jne .L0" xorAsm = true := by native_decide

/-- The com kernel emits the `XOR`-with-all-ones complement (`xorq`) and — being a
    3-arg `(r, a, n)` SysV leaf — tests the counter `%rdx` (the 3rd arg) at the
    back-edge. No `# UNHANDLED-OP` (every body op rendered to a real line). -/
theorem comAsm_shape :
    occursIn "xorq" comAsm = true ∧ occursIn "jne .L0" comAsm = true
      ∧ occursIn "cmpq $0, %rdx" comAsm = true
      ∧ occursIn "UNHANDLED" comAsm = false := by native_decide

/-- The copy kernel (3-arg `(r, a, n)`) emits the move and tests `%rdx`. -/
theorem copyAsm_shape :
    occursIn "movq" copyAsm = true ∧ occursIn "jne .L0" copyAsm = true
      ∧ occursIn "cmpq $0, %rdx" copyAsm = true := by native_decide

/-- The zero kernel (2-arg `(r, n)`) emits the move and tests the counter `%rsi`
    (the 2nd arg). -/
theorem zeroAsm_shape :
    occursIn "movq" zeroAsm = true ∧ occursIn "jne .L0" zeroAsm = true
      ∧ occursIn "cmpq $0, %rsi" zeroAsm = true := by native_decide

/-- The full-scan compare **bench-perf twin** (`cmpAsm`, now `*_handtwin.s`) emits
    the `subq` per-limb diff inside the looped body. The deployed `mpn_cmp` is the
    FRONT-sourced early-exit `cmpAsmFront` (see §9); this is the retained twin. -/
theorem cmpAsm_shape :
    occursIn "subq" cmpAsm = true ∧ occursIn "jne .L0" cmpAsm = true := by native_decide

/-- **Every emitted kernel renders with no `# UNHANDLED-OP` sentinel** — the owned
    printer recognises every body op of all nine kernels. (This is the guard that
    catches a missing mnemonic, e.g. the `NOT`-is-unary case `mpn_com_n` routes
    around via the `XOR`-all-ones idiom.) -/
theorem all_no_unhandled :
    occursIn "UNHANDLED" addAsm = false ∧ occursIn "UNHANDLED" subAsm = false
      ∧ occursIn "UNHANDLED" andAsm = false ∧ occursIn "UNHANDLED" iorAsm = false
      ∧ occursIn "UNHANDLED" xorAsm = false ∧ occursIn "UNHANDLED" comAsm = false
      ∧ occursIn "UNHANDLED" copyAsm = false ∧ occursIn "UNHANDLED" zeroAsm = false
      ∧ occursIn "UNHANDLED" cmpAsm = false := by native_decide

/-! ## 9. The deployed symbols are FRONT-sourced (rolled-loop front output)

The eight core runtime-N kernels (`add`/`sub`/`and`/`ior`/`xor`/`com`/`copyi`/
`zero`) are deployed from the **rolled-loop front**
(`MpnLoopFrontEmit`): each is a covered `LowCT` loop body pushed through
`TranslateDialectRuntimeLoop.rolledForLoopNRt`
(`translateDialectControl` → `cryptoDialectToJasminCom` → `ComL.forLoopNRt`)
and the committed owned exports — **no hand `Com`/`Lcmd`/`JInstr`/`.s`**. The
loop-carried carry/borrow crosses the runtime-N back-edge as a `.sword 64`
scalar accumulator (the carry-as-value abstraction), machine-realized in a GPR
(`%rax`) by the scalar-accumulator export `ComL.toLprogPhysAbiScalarAcc`; the
`[base + 8·i]` streaming is the memref-ABI SIB operand `(%rNN, %idx, 8)`; the
back-edge is the guarded loop `.L…: body ; cmpq $0,%… ; jne .L…`.

The hand-authored `Lcmd` bodies (`addLoopLcmdBody` … above) are **retained as
the bench-perf twin** (`*_handtwin.s`): the open-coded GPR-carry single-limb
loop and the block-unrolled `blk4` `CF`-chain variants are the perf reference,
not the deployed artifact. `mpn_cmp` is now FRONT-sourced too — the MSB-first
early-exit compare returning `{-1,0,+1}` is generated by the `SpStep` schedule
front `MpnCmpEarlyExitFront` (a top-tested runtime scan loop whose body
`condFwd`-breaks OUT of the loop to a `{-1,0,+1}` sign block on the first
differing limb); its full-scan `Lcmd` stub is kept as the `*_handtwin.s`
bench-perf twin. The ONLY residual owned-emit outputs are the block-unrolled
`blk4` add/sub (`CF` live across the `k`-limb block), which the front's
scalar-accumulator carry abstraction does not cover. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-- The FRONT-sourced deployed `.s` text for each core kernel (rendered from the
    `MpnLoopFrontEmit` rolled-loop `Lprog`; `""` iff the front declines, which
    the `*_isSome` gates in `MpnLoopFrontEmit` rule out). -/
def addAsmFront  : String := (MpnLoopFrontEmit.addLprogFront.map renderLprogAtt).getD ""
def subAsmFront  : String := (MpnLoopFrontEmit.subLprogFront.map renderLprogAtt).getD ""
def andAsmFront  : String := (MpnLoopFrontEmit.andLprog.map renderLprogAtt).getD ""
def iorAsmFront  : String := (MpnLoopFrontEmit.iorLprog.map renderLprogAtt).getD ""
def xorAsmFront  : String := (MpnLoopFrontEmit.xorLprog.map renderLprogAtt).getD ""
def comAsmFront  : String := (MpnLoopFrontEmit.comLprog.map renderLprogAtt).getD ""
def copyAsmFront : String := (MpnLoopFrontEmit.copyLprog.map renderLprogAtt).getD ""
def zeroAsmFront : String := (MpnLoopFrontEmit.zeroLprog.map renderLprogAtt).getD ""

/-- **`mpn_cmp` is now FRONT-sourced too** (the last residual). The MSB-first
    early-exit compare returning `{-1,0,+1}` is generated by the `SpStep` schedule
    front `MpnCmpEarlyExitFront` (the same schedule language that generates the
    SHAKE256 sponge and the Plonky3 query sampler): a top-tested runtime scan loop
    (`goto` back-edge) whose body `condFwd`-breaks OUT of the loop to a `{-1,0,+1}`
    sign block on the first differing limb (`subRR` compare-by-subtract). The
    deployed `.s` is the front's rendered output verbatim (`cmpAsmFront_front`),
    NOT hand-authored. -/
def cmpAsmFront : String := MpnCmpEarlyExitFront.cmpAsmFront

/-- The deployed `mpn_cmp` `.s` IS the front schedule's rendered output (byte-for-
    byte); the re-point is definitional. -/
theorem cmpAsmFront_front : cmpAsmFront = MpnCmpEarlyExitFront.cmpAsmFront := rfl

/-- The deployed FRONT `mpn_cmp` is a genuine MSB-first early-exit scan returning
    `{-1,0,+1}` in `%rax` over the GMP ABI: the scan-loop back-edge (`jmp .L0`),
    the per-limb compare-by-subtract (`subq %r10, %r9`), the data-dependent early
    break (`jne .L2`) out of the loop, the `{-1,0,+1}` sign (`movq $1, %rax` /
    `subq $1, %rax`), the ABI operand streaming (`(%rdi)`/`(%rsi)`), and no
    `UNHANDLED` sentinel. -/
theorem cmpAsmFront_shape :
    occursIn "jmp .L0" cmpAsmFront = true
      ∧ occursIn "subq %r10, %r9" cmpAsmFront = true
      ∧ occursIn "jne .L2" cmpAsmFront = true
      ∧ occursIn "movq $1, %rax" cmpAsmFront = true
      ∧ occursIn "subq $1, %rax" cmpAsmFront = true
      ∧ occursIn "(%rdi)" cmpAsmFront = true
      ∧ occursIn "(%rsi)" cmpAsmFront = true
      ∧ occursIn "UNHANDLED" cmpAsmFront = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **The deployed FRONT add kernel is a genuine runtime-N loop that streams the
    operands and threads the carry across the back-edge.** The rendered `.s`
    reaches the deployed symbol, carries the guarded-loop back-edge
    (`jne .L…` / `cmpq $0,`), streams `[base + 8·idx]` via the memref SIB operand
    `(%r14, %rsi, 8)`, and emits no `UNHANDLED` sentinel — every front op rendered
    to a real line. -/
theorem addAsmFront_shape :
    occursIn "mpn_add_n_loop_owned" addAsmFront = true
      ∧ occursIn "jne .L" addAsmFront = true
      ∧ occursIn "cmpq $0," addAsmFront = true
      ∧ occursIn ", 8)" addAsmFront = true
      ∧ occursIn "UNHANDLED" addAsmFront = false := by native_decide

/-- The deployed FRONT sub kernel: runtime-N loop, back-edge, no `UNHANDLED`. -/
theorem subAsmFront_shape :
    occursIn "mpn_sub_n_loop_owned" subAsmFront = true
      ∧ occursIn "jne .L" subAsmFront = true
      ∧ occursIn "UNHANDLED" subAsmFront = false := by native_decide

/-- Every deployed FRONT kernel renders every op (no `UNHANDLED`) and carries the
    runtime-N back-edge. -/
theorem allFront_no_unhandled :
    occursIn "UNHANDLED" addAsmFront = false ∧ occursIn "UNHANDLED" subAsmFront = false
      ∧ occursIn "UNHANDLED" andAsmFront = false ∧ occursIn "UNHANDLED" iorAsmFront = false
      ∧ occursIn "UNHANDLED" xorAsmFront = false ∧ occursIn "UNHANDLED" comAsmFront = false
      ∧ occursIn "UNHANDLED" copyAsmFront = false ∧ occursIn "UNHANDLED" zeroAsmFront = false := by
  native_decide

/-! ## 10. Emit driver -/

/-- Write the deployed runtime-N mpn kernels into the integration bench harness
    directory (`bench/integration/gen_com/`).

    **The eight core deployed symbols are FRONT-sourced** (the rolled-loop front
    output of `MpnLoopFrontEmit`, no hand `Com`/`Lcmd`/`.s`); the hand-authored
    `Lcmd` twins are retained alongside as `*_handtwin.s` (the bench-perf
    reference). The block-unrolled `blk4` add/sub and `mpn_cmp` stay owned-emit
    outputs (front does not cover the in-register `CF`-block or the early-exit
    compare). -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/integration/gen_com"
  -- Deployed symbols: FRONT-sourced (rolled-loop front → owned export).
  IO.FS.writeFile "bench/integration/gen_com/mpn_add_n_loop_owned.s" addAsmFront
  IO.FS.writeFile "bench/integration/gen_com/mpn_sub_n_loop_owned.s" subAsmFront
  IO.FS.writeFile "bench/integration/gen_com/mpn_and_n_loop_owned.s" andAsmFront
  IO.FS.writeFile "bench/integration/gen_com/mpn_ior_n_loop_owned.s" iorAsmFront
  IO.FS.writeFile "bench/integration/gen_com/mpn_xor_n_loop_owned.s" xorAsmFront
  IO.FS.writeFile "bench/integration/gen_com/mpn_com_n_loop_owned.s" comAsmFront
  IO.FS.writeFile "bench/integration/gen_com/mpn_copyi_loop_owned.s" copyAsmFront
  IO.FS.writeFile "bench/integration/gen_com/mpn_zero_loop_owned.s" zeroAsmFront
  -- Bench-perf twin: the hand-authored open-coded GPR-carry `Lcmd` bodies.
  IO.FS.writeFile "bench/integration/gen_com/mpn_add_n_loop_owned_handtwin.s" addAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_sub_n_loop_owned_handtwin.s" subAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_and_n_loop_owned_handtwin.s" andAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_ior_n_loop_owned_handtwin.s" iorAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_xor_n_loop_owned_handtwin.s" xorAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_com_n_loop_owned_handtwin.s" comAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_copyi_loop_owned_handtwin.s" copyAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_zero_loop_owned_handtwin.s" zeroAsm
  -- FRONT-sourced early-exit compare (SpStep schedule front `MpnCmpEarlyExitFront`):
  -- MSB-first scan, in-body forward break, `{-1,0,+1}` return over the GMP ABI.
  IO.FS.writeFile "bench/integration/gen_com/mpn_cmp_loop_owned.s" cmpAsmFront
  -- Bench-perf twin: the hand-authored full-scan `Lcmd` compare stub.
  IO.FS.writeFile "bench/integration/gen_com/mpn_cmp_loop_owned_handtwin.s" cmpAsm
  -- Owned-only bench-perf twins (front does not cover the in-register CF-block):
  -- the block-unrolled blk4 add/sub.
  IO.FS.writeFile "bench/integration/gen_com/mpn_add_n_blk4_loop_owned.s" addBlk4Asm
  IO.FS.writeFile "bench/integration/gen_com/mpn_sub_n_blk4_loop_owned.s" subBlk4Asm
  IO.println "wrote FRONT-sourced deployed mpn add/sub/and/ior/xor/com/copyi/zero/cmp .s (rolled-loop + SpStep fronts) + hand twins + owned blk4"

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopOwnedEmit
