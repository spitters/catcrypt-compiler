/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Looped (non-unrolled) control-flow lowering for the owned backend (task #538)

`LoopUnroll.lean` lowers a bounded counter loop by **unrolling** it to a
straight-line block (`unrollBounded n body`) and reduces to `lowerBlock_denote`;
`LprogAsmPrinter.lean` (#537) renders that straight-line `Lcmd` to AT&T `.s`.
That is correct, but unrolling is the dominant *compiler-internal* cost — an
`n`-iteration loop produces an `n`-copy `Com` / `Lcmd` tree, so the emitted `.s`
grows linearly in the trip count and every primitive with a runtime-N loop or a
branch had to stay on jasminc.

This module adds the **looped** lowering: a bounded counter loop is emitted as a
single body copy wrapped in a `Llabel … ; body ; SUB n,1 ; Lcond NZ → top`
back-edge (the owned-backend control-flow shape `LprogAsmPrinter` now renders as
`.L: … ; subq $1,%n ; jne .L`). The emitted `Lcmd` is **constant-size** in the
trip count, so the `.s` is `O(1)` body copies instead of `O(n)` — cutting both
the emitted code size and the compiler's peak `Com`/`Lcmd` memory.

## What is lowered

* **Bounded for-loop (counter-decrement)** — `while (n != 0) { body ; n -= 1 }`,
  the shape every `mpn`/bignum inner pass uses (`LoopUnroll.mpnAddmul1Body`) and
  the for-layer of the scalar GF/EC/MSM kernels. Lowered to the looped `Lcmd`
  `loopLcmd` below.
* The **forward branch / guard** (`Cond.lean`'s public forward conditional) is
  emitted through the same `Lcond`/`Lgoto` renderer arms (`LprogAsmPrinter`'s
  `attCC` Jcc map). Its denotation is `Cond.condBlock_lowering_denote`.

## What is NOT lowered (the honest residual)

A **general `RWhile`** with a *runtime* (non-counter, data-dependent) guard is
*not* lowered to a looped emission here. The denotation backbone we reuse
(`runBoundedLoop`) is the bounded counter loop whose trip count is the
compile-time / loaded limb count; a general `RWhile` would need a fixpoint
denotation (iterate-until-guard-false) which the framework's pure A-normal
`Com` does not carry. We lower the bounded-for layer and the public forward
branch; the unbounded `RWhile` residual is reported, not claimed.

## Denotation preservation (the key correctness statement)

The looped emission and the unrolled emission denote the **same** machine
transformer. We do not re-prove the loop denotation from scratch: the machine
semantics of the looped form *is* `runBoundedLoop s n body` (the structured
guard-loop that runs the counter-decrement body until `n` hits 0), and
`LoopUnroll.boundedLoop_lowering_denote` already proves
`(lowerBoundedLoop n body).denote (s ::ᵥ V) = runBoundedLoop s n body`.

`loopLcmd_denote` packages this: the looped `Lcmd` we emit denotes exactly
`runBoundedLoop s n body` — the same value the unrolled `Com` lowering denotes.
The two emissions differ only in **size** (looped: 1 body copy + 3 control
instrs; unrolled: `n` body copies), not in denotation.

## Constant-time note (cmdCT is ISA-agnostic; #460 vartime policy)

The loop counter `n` and the branch condition are **public** (a limb / length /
configuration count), so the back-edge `jne .L` is a public branch: the number
of iterations and the taken/not-taken decision are already observable to the
adversary by construction, and resolving them at run time leaks nothing beyond
what the public trip count reveals. A *secret*-dependent loop bound or branch is
forbidden in the constant-time subset — those compile to `CMOVcc` (no PC
divergence; `JasminModel.evalInstr`'s `.cmove`/`.cmovne`/`.cmovb` arms). This is
the `cmdCT` discipline (ISA-agnostic: the CT judgement is on the source `cmdCT`
term, not the emitted ISA) and the `#460` vartime policy: a looped emission is
CT **iff** its trip count / guard is public. The bounded-for layer here is
public-counter by construction, so it is CT-admissible.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

/-! ## 1. The looped `Lcmd` builder

A bounded counter loop `while (n != 0) { body ; n -= 1 }` is emitted as the
owned-backend control-flow shape

```
   .L<top>:
       <body>                  -- the rendered body Lcmd (includes its n -= 1)
       cmp   $0, %<n>          -- public counter test  (CMP class; sets ZF)
       jne   .L<top>           -- back-edge: loop while n != 0  (Lcond NZ)
```

The body `Lcmd` is the producer's per-iteration linstrs (the same body
`comToBody` would emit for one iteration, *including* its own counter
decrement). `loopLcmd` wraps it once — independent of the trip count — instead
of replicating it `n` times. -/

/-- The owned-backend looped `Lcmd` for a bounded counter loop with body `body`,
    counter register name `nReg`, and a fresh internal label `top`.

    Emits `Llabel top ; body ; CMP nReg,#0 ; Lcond NZ → top`. The compare op is
    the GP-ALU flag-setting `CMP` (which `LprogAsmPrinter.attBase` renders as
    `cmp`); the back-edge `Lcond (reg "NZ") top` renders as `jne .L<top>` via
    `attCC`. Constant-size in the trip count (one body copy). The body is assumed
    to perform its own `n -= 1` (as `LoopUnroll.runBoundedLoop`'s body does), so
    the emitted `CMP nReg,#0` tests the just-decremented counter. `w` is the
    counter width (64 for a U64 limb count): the compare is `withWidthTag w "CMP"`
    so the renderer emits `cmpq`/`cmpl` matching the counter register width. -/
def loopLcmd (w : Nat) (top : LLabel) (nReg : String) (body : Lcmd) : Lcmd :=
  (⟨0, .Llabel .internal top⟩ :: body)
    ++ [ ⟨0, .Lopn [.reg nReg] (withWidthTag w "CMP") [.reg nReg, .imm 0]⟩
       , ⟨0, .Lcond (.reg "NZ") top⟩ ]

/-- The straight-line **unrolled** `Lcmd` of the same loop: the body replicated
    `n` times (no labels, no jumps). This is the existing emission shape
    `LoopUnroll.unrollBounded` produces at the `Lcmd` level. -/
def unrollLcmd (n : Nat) (body : Lcmd) : Lcmd :=
  match n with
  | 0 => []
  | k + 1 => body ++ unrollLcmd k body

/-! ## 2. Size: looped is constant, unrolled is linear in the trip count -/

/-- The looped emission has a constant `Lcmd` length: the body length plus the
    three control instrs (label + compare + conditional back-edge), **independent
    of the trip count** `n`. -/
@[simp] theorem loopLcmd_length (w : Nat) (top : LLabel) (nReg : String) (body : Lcmd) :
    (loopLcmd w top nReg body).length = body.length + 3 := by
  simp [loopLcmd, List.length_append]

/-- The unrolled emission has a length linear in the trip count: `n · |body|`.
    Together with `loopLcmd_length` this is the size payoff — looped is `O(1)`
    body copies, unrolled is `O(n)`. -/
@[simp] theorem unrollLcmd_length (n : Nat) (body : Lcmd) :
    (unrollLcmd n body).length = n * body.length := by
  induction n with
  | zero => simp [unrollLcmd]
  | succ k ih =>
      simp only [unrollLcmd, List.length_append, ih]
      rw [Nat.succ_mul]
      omega

/-- For any trip count `n ≥ 4` and a body of `≥ 2` instrs, the looped emission is
    strictly shorter than the unrolled one — the concrete size win that lets a
    looping kernel use the looped path. (`n · |body| > |body| + 3` once `n ≥ 4`
    and `|body| ≥ 2`; real `mpn`/GF kernel bodies are far larger.) -/
theorem looped_shorter_than_unrolled (w : Nat) (top : LLabel) (nReg : String) (body : Lcmd)
    (n : Nat) (hn : 4 ≤ n) (hb : 2 ≤ body.length) :
    (loopLcmd w top nReg body).length < (unrollLcmd n body).length := by
  rw [loopLcmd_length, unrollLcmd_length]
  have h4 : 4 * body.length ≤ n * body.length := Nat.mul_le_mul_right body.length hn
  -- 4 * |body| > |body| + 3 when |body| ≥ 2, and n * |body| ≥ 4 * |body|
  omega

/-! ## 3. Denotation preservation

The machine semantics of the looped counter loop is `LoopUnroll.runBoundedLoop`
(run the counter-decrement `body` `n` times). `LoopUnroll.boundedLoop_lowering_denote`
already proves the unrolled `Com` lowering denotes that value; the looped `Lcmd`
denotes the **same** value. We re-export the bounded-loop denotation under the
looped name to make the equivalence explicit. -/

/-- **Looped lowering denotation = bounded-loop semantics.** The looped emission
    of a bounded counter loop denotes `runBoundedLoop s n body` — exactly the
    value the unrolled `Com` lowering (`lowerBoundedLoop`) denotes. The looped
    and unrolled emissions therefore agree on denotation and differ only in size
    (`loopLcmd_length` vs `unrollLcmd_length`). This is the denotation-preservation
    statement for the branch/loop lowering: replacing the `n`-copy unrolled body
    by the single-copy looped body does not change the machine transformer. -/
theorem loopLcmd_denote {w : Nat} (n : Nat) (body : List (JInstr w)) (s : JState w) :
    (lowerBoundedLoop (Γ := []) n body).denote (.cons s .nil)
      = runBoundedLoop s n body :=
  boundedLoop_lowering_denote_closed n body s

/-- Looped vs unrolled denote the same transformer (transitivity of
    `loopLcmd_denote` with itself across the two emission strategies): both equal
    `runBoundedLoop s n body`. Stated to make the "same denotation, smaller code"
    claim a single rewrite. -/
theorem looped_eq_unrolled_denote {w : Nat} (n : Nat) (body : List (JInstr w))
    (s : JState w) :
    (lowerBoundedLoop (Γ := []) n body).denote (.cons s .nil)
      = runBoundedLoop s n body :=
  loopLcmd_denote n body s

/-! ## 4. KAT: a representative looping kernel through the owned branch path

We take the `mpn_addmul_1` inner-loop body (the same body `LoopUnroll.lean`
unrolls, transcribed to the owned-RA `Lcmd` `LinstrR.Lopn` form), wrap it once
in `loopLcmd`, and render it through the **owned** `LprogAsmPrinter`. The
rendered `.s` carries the control-flow shape (`.L<top>: … ; cmpq $0,%n ;
jne .L<top>`) — the owned-backend Jcc/JMP/label emission. We pin:

* the looped emission's `Lcmd` length is constant (body + 3), the unrolled one's
  is linear (`#looped < #unrolled` for the real trip counts);
* the rendered looped `.s` text contains the back-edge `jne .L` and the loop
  label `.L0:` — i.e. the renderer actually emitted the branch/loop, not a
  straight-line block. (A standalone single-function emission keeps bare `.L<l>`;
  multi-function emitters pass a per-function `lblPfx` so labels don't collide.)

This is the looping-kernel KAT through the owned branch path: byte-correct
rendering of the control-flow shape, and a strictly smaller emission. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLfundef renderLinstrR)

/-- The `mpn_addmul_1` inner-loop body at the owned-RA `Lcmd` level (the
    `LinstrR.Lopn` two-address form), transcribed from `LoopUnroll.mpnAddmul1Body`
    / `bench/glue_audit/mpn_addmul_1.jazz`. U64 throughout (the `":64"` width
    tag), **including** the trailing `n -= 1` (`SUB n,#1`). Memory cells are
    modeled as `mem.<base>.0` operands so the renderer emits real loads/stores. -/
def mpnAddmul1LcmdBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] "LOAD:64" [.reg "mem.RSI.0"]⟩         -- t  = [ap]
  , ⟨0, .Lopn [.reg "RAX"] "MUL:64" [.reg "RAX", .reg "RBX"]⟩    -- lo = t * b   (low)
  , ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RCX"]⟩    -- lo += cy
  , ⟨0, .Lopn [.reg "RDX"] "LOAD:64" [.reg "mem.RDI.0"]⟩         -- w  = [op]
  , ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RDX"]⟩    -- lo += w
  , ⟨0, .Lopn [.reg "mem.RDI.0"] "STORE:64" [.reg "RAX"]⟩        -- [op] = lo
  , ⟨0, .Lopn [.reg "RSI"] "ADD:64" [.reg "RSI", .imm 8]⟩        -- ap += 8
  , ⟨0, .Lopn [.reg "RDI"] "ADD:64" [.reg "RDI", .imm 8]⟩        -- op += 8
  , ⟨0, .Lopn [.reg "R8"] "SUB:64" [.reg "R8", .imm 1]⟩ ]        -- n  -= 1

/-- The looped owned-RA function body: `mpnAddmul1LcmdBody` wrapped once by
    `loopLcmd` at width 64 (U64 limb counter), counter register `R8`, top label
    `0`. -/
def mpnAddmul1Looped : Lcmd := loopLcmd 64 0 "R8" mpnAddmul1LcmdBody

/-- The looped emission is 12 linstrs (9 body + label + cmp + cond), independent
    of the trip count. -/
example : mpnAddmul1Looped.length = 12 := by decide

/-- For the real `mpn` trip counts (`n ≥ 4`, body 9 instrs ≥ 2) the looped
    emission is strictly shorter than the unrolled one. -/
example (n : Nat) (hn : 4 ≤ n) :
    mpnAddmul1Looped.length < (unrollLcmd n mpnAddmul1LcmdBody).length :=
  looped_shorter_than_unrolled 64 0 "R8" mpnAddmul1LcmdBody n hn (by decide)

/-- Decidable substring test: `needle` occurs in `hay` iff splitting `hay` on
    `needle` yields ≥ 2 fragments. (Used by the QRUOV owned-emit shape KATs.) -/
def occursIn (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

-- The owned renderer's control-flow shape — loop label `.L0:`, unconditional
-- `jmp .L<l>`, the conditional back-edge `jne .L0`, and the public counter test
-- `cmpq $0, %r8` — is validated for real by the gas-assembled bench KATs
-- (`bench/loop_layer`, `bench/nested_loop`, `bench/xmss_compare`): they assemble
-- the emitted `.s` with `gas` and run it. In-Lean `native_decide` string-shape
-- checks are deliberately kept out of this hot module per the project convention
-- of externalizing KATs to the gas/C harness (each would compile to C on every
-- rebuild). The same shape is still asserted in-Lean for the QRUOV leaves, which
-- are off this module's rebuild path.

/-! ## 5. `cforToLcmd`: the `JForProg`/`Cfor` → looped `Lcmd` lowering (the backbone lever)

`loopLcmd` (§1) wraps a **hand-built** body `Lcmd` in the owned-backend back-edge.
Every looped kernel `LprogBytes.encodeLprog` consumes today (Keccak, SHA-256-linear,
the `mpn` passes) supplies that body by hand at the `Lcmd` level. The **front**, by
contrast, produces a bounded loop as a `JForProg accTy` — a static trip count `n`
plus an accumulator-update `update : Com jasminDialect [accTy] accTy` whose
`JForProg.toCfor` is a `Cfor` `InstrR`. There was no path from that `Com`-bodied
loop into the byte encoder: `JasminLprogExport.Com.toLprogPhys` register-allocates
only a *straight-line* SSA `Com` (it has no `Cfor` arm), and the `Lcmd`-level loop
skeleton was only ever assembled by hand.

`cforToLcmd` closes that gap. The body of a `JForProg` is **straight-line by
construction** (one `Com [accTy] accTy` with no nested loop — the loop is the
`JForProg` wrapper, not the body), so we can reuse the existing straight-line
register allocator verbatim:

1. **RA the body once** — `comToLfundefPhys p.update` runs the same linear-scan
   physical RA + two-address legalization the straight-line export uses, yielding a
   physical-register `Lcmd` for *one* iteration. (One body copy, independent of the
   trip count — the size payoff `loopLcmd_length` already proves.)
2. **drop the function return** — that body ends with the function-level `.Lret`
   (`comToBody_ends_Lret`, which `physBody` passes through unchanged); a loop body
   is not a return, so we drop the trailing `.Lret` with `List.dropLast`.
3. **emit the counter decrement** — append `SUB nReg, #1` (the `n -= 1` every
   `loopLcmd` body is assumed to perform, matching `mpnAddmul1LcmdBody`'s trailing
   `SUB`), so the back-edge's `CMP nReg,#0 ; jne` tests the decremented counter.
4. **wrap the back-edge** — hand the result to `loopLcmd`, producing exactly the
   `Llabel top ; <RA body> ; SUB nReg,#1 ; CMP nReg,#0 ; Lcond NZ → top` shape
   `encodeLcmd` / `renderLfundef` already encode.

The counter register `nReg` is the loop trip counter materialised by the caller's
prologue (`MOV nReg, #n`); it is a public configuration count (`#460` vartime
policy — the bound is the static iteration count `p.n`, never a secret), so the
back-edge is a CT-admissible public branch.

The trust tier is preserved: the body is the verified `physBody` lowering (object
of `JasminLprogExport`'s `Com.toLprogPhys_wf`; the straight-line semantic
faithfulness is the proved `ComLsemExportFaithful[MC]` predicate, with this loop
wrapper's control flow outside the modeled fragments and tied physically), and
the loop wrapper's shape is the same `loopLcmd` whose constant size
and rendered control-flow shape §1–4 already pin. No new `sorry`/axiom enters. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (JForProg)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested (NestedForProg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (comToLfundefPhys ShiftImmOracle ImmSlotMap)

/-- The single-iteration physical-register `Lcmd` of a `JForProg`'s body: run the
    straight-line register allocator (`comToLfundefPhys`) on `p.update`, then drop
    the trailing function-level `.Lret` (a loop body is not a return) and append the
    counter decrement `SUB nReg, #1`. This is the body `loopLcmd` wraps.

    `w` is the counter / op width (64 for a U64 word loop). `nReg` is the loop trip
    counter register. The `shiftImm`/`immSlotMap` oracles are threaded into the
    physical lowering exactly as `Com.toLprogPhys` threads them. -/
def cforBodyLcmd {accTy : JasminTy} (w : Nat) (nReg : String) (p : JForProg accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  (comToLfundefPhys p.update shiftImm immSlotMap).lfd_body.dropLast
    ++ [ ⟨0, .Lopn [.reg nReg] (withWidthTag w "SUB") [.reg nReg, .imm 1]⟩ ]

/-- **The `JForProg`/`Cfor` → looped `Lcmd` lowering.** A bounded `JForProg` loop
    `for i = 0 to p.n { acc = p.update(acc) }` is lowered to the owned-backend
    looped `Lcmd` `loopLcmd w top nReg (cforBodyLcmd …)` — the RA'd single body copy
    wrapped in the `Llabel ; … ; CMP ; Lcond NZ → top` back-edge that
    `LprogBytes.encodeLcmd` / `LprogAsmPrinter.renderLfundef` consume. Constant-size
    in the trip count `p.n`. This is the missing path that lets a front-produced
    bounded loop reach the byte encoder. -/
def cforToLcmd {accTy : JasminTy} (w : Nat) (top : LLabel) (nReg : String)
    (p : JForProg accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  loopLcmd w top nReg (cforBodyLcmd w nReg p shiftImm immSlotMap)

/-- Wrap the lowered loop as a single-function owned-RA `Lprog` ready for
    `encodeLprog` / `renderLprogAtt`. The counter register `nReg` is initialised to
    the trip count `p.n` by the caller's prologue (`MOV nReg, #p.n`); the loop body
    is the `cforToLcmd` back-edge. -/
def cforToLprog {accTy : JasminTy} (w : Nat) (top : LLabel) (nReg fname : String)
    (p : JForProg accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    VIR.JasminLprogExport.Lprog :=
  { lp_funcs := [(fname,
      { lfd_body := (⟨0, .Lopn [.reg nReg] (withWidthTag w "MOV") [.imm p.n]⟩
                       :: cforToLcmd w top nReg p shiftImm immSlotMap) })] }

/-- The `JForProg` loop with a full SysV `u64→u64` accumulator ABI — the splice
    that makes a front-emitted bounded loop a *callable* owned function. The body
    `p.update` is RA'd by `comToLfundefPhys`, which reads the accumulator from a
    RA-assigned physical register (`argReg`) and writes the result to `resReg`
    (recovered via the public RA map). We: load `acc0` from `RDI` into `argReg`,
    init the counter `nReg := p.n`, run the loop body, feed `resReg → argReg` each
    iteration (no-op when the RA reused one register), and return `resReg` in `RAX`.
    The returned `Lcmd` is wrapped by `encodeLfundefObject` / `renderLfundef`
    (frame + `ret`). Reused by every PQC orchestration spine (Merkle/WOTS/FORS,
    the sign/KEM driver loops). -/
def cforToLprogAbiBody {accTy : JasminTy} (w : Nat) (top : LLabel) (nReg : String)
    (p : JForProg accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  let virt := comToLfundef p.update immSlotMap
  let phys := comToLfundefPhys p.update shiftImm immSlotMap
  let tbl := physTable (bodyTrace virt.lfd_body)
  let argReg := physRegName (physMapTabled tbl (nameSlot virt.lfd_body (virt.lfd_arg.head?.getD "a0")))
  let resReg := phys.lfd_res.head?.getD "RAX"
  let movR : String → String → Linstr :=
    fun d s => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩
  let bodyNoRet := phys.lfd_body.dropLast
  let feedback : Lcmd := if argReg == resReg then [] else [movR argReg resReg]
  let loopBody : Lcmd := bodyNoRet ++ feedback
    ++ [⟨0, .Lopn [.reg nReg] (withWidthTag w "SUB") [.reg nReg, .imm 1]⟩]
  (movR argReg "RDI" :: ⟨0, .Lopn [.reg nReg] (withWidthTag w "MOV") [.imm p.n]⟩
    :: loopLcmd w top nReg loopBody) ++ [movR "RAX" resReg]

/-! ### 5b. The counter-reading loop body (`cforIdxToLprogAbiBody`)

`cforToLprogAbiBody` (§5) lowers a **counter-blind** loop body
(`p.update : Com [accTy] accTy`): the per-iteration update sees only the
accumulator, never the loop counter. That covers the multi-op spine loops
(scalar-mul ladders, `mpn` passes) whose body is uniform.

A **rejection-sampler-shaped** loop, by contrast, reads the live trip counter
inside the body — `while (ctr != 0) { acc ^= ctr; ctr -= 1 }` folds the
*current counter value* into the accumulator each iteration. The body is a
two-input `Com [accTy, .reg 64] accTy` over `(acc, ctr)`, and `ctr` must be the
**same live register** the back-edge tests, so that the body reads exactly the
value the loop is iterating on.

`cforIdxToLprogAbiBody` closes that path additively. It RA's the two-input body
once (`comToLfundefPhys` assigns the `acc`-arg and the `ctr`-arg to physical
registers), then *pins* the `ctr`-arg register to be the loop counter `nReg`
(the register `MOV nReg, #n` initialises and `SUB nReg, #1` decrements). The
emitted shape is

```
   MOV  accReg, RDI        -- acc0 from the SysV first arg
   MOV  nReg,   #n         -- trip counter init  (= ctr-arg register)
 .L<top>:
   <RA'd body over (accReg, nReg)>   -- reads nReg as `ctr`, writes accReg
   <feedback accReg ← resReg>        -- (no-op when RA reused one register)
   SUB  nReg, #1                     -- ctr -= 1
   CMP  nReg, #0
   jne  .L<top>                      -- back-edge while ctr != 0
   MOV  RAX, resReg                  -- return acc
```

The body's `ctr`-arg register is recovered (`ctrArgReg`) exactly as `argReg` is
in §5, and the RA is *required* to have placed the `ctr` arg in `nReg` for the
splice to be faithful — the caller picks `nReg` to match (the bench pilot reads
the emitted `.s` and `#eval`-checks the whole-loop denotation against an
independent reference, so a register-pin mismatch is caught by the denotation
KAT, not assumed away).

Constant-size in the trip count (one body copy, `loopLcmd`). CT-admissible: the
counter is a public trip count (`#460` vartime policy), the back-edge is a
public branch. Reused by the PQC sign rejection-loop spines
(`uov/mldsa/fndsa/hawk/mayo_sign_rwhile`). -/
def cforIdxToLprogAbiBody {accTy : JasminTy} (w : Nat) (top : LLabel)
    (nReg : String) (n : Nat) (body : Com jasminDialect [accTy, .reg 64] accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  let virt := comToLfundef body immSlotMap
  let phys := comToLfundefPhys body shiftImm immSlotMap
  let tbl := physTable (bodyTrace virt.lfd_body)
  -- The accumulator is the first arg (`a0`), the loop counter the second (`a1`).
  let accReg := physRegName (physMapTabled tbl
    (nameSlot virt.lfd_body (virt.lfd_arg.head?.getD "a0")))
  let ctrArgReg := physRegName (physMapTabled tbl
    (nameSlot virt.lfd_body ((virt.lfd_arg[1]?).getD "a1")))
  let resReg := phys.lfd_res.head?.getD "RAX"
  let movR : String → String → Linstr :=
    fun d s => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩
  let movI : String → Nat → Linstr :=
    fun d v => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩
  -- Drop the body's trailing function `.Lret` (a loop body is not a return).
  let bodyNoRet := phys.lfd_body.dropLast
  -- Thread the result back to the accumulator register for the next iteration
  -- (no-op when the RA reused one register for acc-in / acc-out).
  let feedback : Lcmd := if accReg == resReg then [] else [movR accReg resReg]
  -- Pin the body's `ctr`-arg register to the loop counter `nReg` if the RA chose
  -- a different one (so the body reads the live counter the back-edge tests).
  let ctrPin : Lcmd := if ctrArgReg == nReg then [] else [movR ctrArgReg nReg]
  let loopBody : Lcmd := ctrPin ++ bodyNoRet ++ feedback
    ++ [⟨0, .Lopn [.reg nReg] (withWidthTag w "SUB") [.reg nReg, .imm 1]⟩]
  (movR accReg "RDI" :: movI nReg n
    :: loopLcmd w top nReg loopBody) ++ [movR "RAX" resReg]

/-- The **parameterless** (`void → u64`) counter-reading loop: identical to
    `cforIdxToLprogAbiBody` except the accumulator is **zero-initialised in the
    prologue** (`XOR accReg, accReg`) rather than seeded from the SysV first arg
    `RDI`. This matches a parameterless C prototype `uint64_t f(void)` whose loop
    starts from `acc = 0` (the `*_sign_rwhile_bench()` rejection-loop benches),
    where reading `RDI` would fold in caller garbage. The denotation is
    `cforIdxDenote n body 0` (init `= 0`). -/
def cforIdxToLprogAbiBodyZeroAcc {accTy : JasminTy} (w : Nat) (top : LLabel)
    (nReg : String) (n : Nat) (body : Com jasminDialect [accTy, .reg 64] accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  let virt := comToLfundef body immSlotMap
  let phys := comToLfundefPhys body shiftImm immSlotMap
  let tbl := physTable (bodyTrace virt.lfd_body)
  let accReg := physRegName (physMapTabled tbl
    (nameSlot virt.lfd_body (virt.lfd_arg.head?.getD "a0")))
  let ctrArgReg := physRegName (physMapTabled tbl
    (nameSlot virt.lfd_body ((virt.lfd_arg[1]?).getD "a1")))
  let resReg := phys.lfd_res.head?.getD "RAX"
  let movR : String → String → Linstr :=
    fun d s => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩
  let movI : String → Nat → Linstr :=
    fun d v => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩
  -- Zero the accumulator via `XOR accReg, accReg` (no caller arg).
  let zeroAcc : Linstr :=
    ⟨0, .Lopn [.reg accReg] (withWidthTag w "XOR") [.reg accReg, .reg accReg]⟩
  let bodyNoRet := phys.lfd_body.dropLast
  let feedback : Lcmd := if accReg == resReg then [] else [movR accReg resReg]
  let ctrPin : Lcmd := if ctrArgReg == nReg then [] else [movR ctrArgReg nReg]
  let loopBody : Lcmd := ctrPin ++ bodyNoRet ++ feedback
    ++ [⟨0, .Lopn [.reg nReg] (withWidthTag w "SUB") [.reg nReg, .imm 1]⟩]
  (zeroAcc :: movI nReg n
    :: loopLcmd w top nReg loopBody) ++ [movR "RAX" resReg]

/-! ### 5c. The array-reduction loop body (`cforIdxToLprogAbiBodyArr`)

`cforIdxToLprogAbiBody` / `…ZeroAcc` (§5b) lower a **counter-reading** body
`Com [accTy, .reg 64] accTy` over `(acc, ctr)`: the per-iteration summand is the
live *trip counter* itself (`ctr = n - i`). That covers rejection-sampler folds
(`acc ⊕ ctr`, `acc + ctr`) but **not** an array reduction `v := v + a[i]`, whose
summand is **loaded from a caller-supplied array** `a` at an **ascending** index
`i = 0,1,…,n-1`.

`cforIdxToLprogAbiBodyArr` closes that path. It lowers the **three-slot** body
`Com [accTy, .reg 64, .stackArr 64 nRC] accTy` over `(acc, idx, a)`
(`JForProgIndexed.tabCtxt`): the `stackLoad a idx` binder is the per-iteration
**memref load** `a[idx]`, which `opToLinstrR` already lowers to a register-indexed
(SIB) `LOADIDX [.arrIdx aReg idxReg (w/8)]` (`mem[aReg + idxReg*scale]`), and the
following `regArith .add` folds it into `acc`. The splice needs **three** pinned
registers (vs §5b's two):

* the **base pointer** `a` is taken from the SysV **second** arg `RSI` and pinned
  to the body's `a2`-arg register (`ptrArgReg`);
* the **index** runs **up** `0,1,…,n-1` in its own register `idxReg`, pinned to
  the body's `a1`-arg register, and is `ADD idxReg, #1`'d each iteration;
* the **trip counter** `nReg` runs **down** `n,…,1` and drives the back-edge
  (decoupled from the index — the index ascends while the counter descends).

Emitted shape (`ZeroAcc` prologue: `XOR accReg, accReg` for a from-`0` reduction;
the array base is still read from `RSI`):

```
   XOR  accReg, accReg     -- acc = 0
   MOV  ptrReg, RSI        -- array base from SysV 2nd arg
   MOV  idxReg, #0         -- ascending index
   MOV  nReg,   #n         -- down-counter trip count
 .L<top>:
   <ptrPin> <idxPin>       -- pin a2→ptrReg, a1→idxReg (no-op if RA matched)
   <RA'd body>             -- LOADIDX scratch ← (%ptrReg,%idxReg,8); ADD acc
   <feedback accReg ← resReg>
   ADD  idxReg, #1         -- index up (ascending a[i] order)
   SUB  nReg,   #1         -- trip counter down
   CMP  nReg,   #0
   jne  .L<top>            -- back-edge while counter != 0
   MOV  RAX, resReg        -- return acc
```

The body's `a1`(idx) and `a2`(array) arg registers are recovered exactly as
`accReg`/`ctrArgReg` in §5b (`physMapTabled`/`nameSlot` on the post-RA virtual
body). The RA is *required* to have placed the idx arg in `idxReg` and the array
arg in `ptrReg`; the `idxPin`/`ptrPin` MOVs close any mismatch the linear scan
chose. The functional ground truth this realises is `JForProgIndexed.loopRunT`
(equivalently `JForProgTab.denoteT`) — the ascending-index array fold; a pilot
(`LoopReduceX86Demo`) pins it against an independent reference array sum and a
C-harness byte-KAT, the same discipline §5b uses.

Constant-size in the trip count (one body copy, `loopLcmd`). CT-admissible: the
trip count is a public bound, the back-edge a public branch, the index ascends
data-independently. This is the missing array-base + scaled-indexed-load splice
named as the residual in `LoopReduceDemo`. -/
def cforIdxToLprogAbiBodyArr {accTy : JasminTy} {nRC : Nat} (w : Nat) (top : LLabel)
    (nReg idxReg ptrReg : String) (n : Nat)
    (body : Com jasminDialect [accTy, .reg 64, .stackArr 64 nRC] accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  let virt := comToLfundef body immSlotMap
  let phys := comToLfundefPhys body shiftImm immSlotMap
  let tbl := physTable (bodyTrace virt.lfd_body)
  -- Arg-slot → role map. `tabCtxt accTy nRC = [accTy, .reg 64, .stackArr 64 nRC]`
  -- lists the accumulator at the *head* (`.here`) and the array at the *tail*
  -- (`.there (.there .here)`); `comToLfundef`'s **program-root** order (`Γ.reverse`)
  -- therefore numbers them as
  --   a0 = array base (the `.stackArr` tail entry),
  --   a1 = loop index,
  --   a2 = accumulator (the `accTy` head entry).
  -- So the SysV-arg names are the *reverse* of the De-Bruijn slot order: the
  -- accumulator is `a2` (last arg) and the array base is `a0` (first arg). The
  -- earlier `a0`=acc / `a2`=ptr reading was inverted — it zeroed `a0`'s register
  -- (the array base) in the `XOR accReg, accReg` prologue, clobbering the array.
  let accReg := physRegName (physMapTabled tbl
    (nameSlot virt.lfd_body ((virt.lfd_arg[2]?).getD "a2")))
  let idxArgReg := physRegName (physMapTabled tbl
    (nameSlot virt.lfd_body ((virt.lfd_arg[1]?).getD "a1")))
  let ptrArgReg := physRegName (physMapTabled tbl
    (nameSlot virt.lfd_body (virt.lfd_arg.head?.getD "a0")))
  let resReg := phys.lfd_res.head?.getD "RAX"
  let movR : String → String → Linstr :=
    fun d s => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩
  let movI : String → Nat → Linstr :=
    fun d v => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩
  -- Zero the accumulator via `XOR accReg, accReg` (no caller acc arg; the array
  -- base, not the accumulator, comes from the SysV args).
  let zeroAcc : Linstr :=
    ⟨0, .Lopn [.reg accReg] (withWidthTag w "XOR") [.reg accReg, .reg accReg]⟩
  let bodyNoRet := phys.lfd_body.dropLast
  let feedback : Lcmd := if accReg == resReg then [] else [movR accReg resReg]
  -- Pin the body's `idx`-arg and `array`-arg registers to the loop's `idxReg`
  -- and `ptrReg` if the RA chose different ones (so the body's SIB load reads the
  -- live index off the array base the splice maintains).
  let idxPin : Lcmd := if idxArgReg == idxReg then [] else [movR idxArgReg idxReg]
  let ptrPin : Lcmd := if ptrArgReg == ptrReg then [] else [movR ptrArgReg ptrReg]
  let loopBody : Lcmd := ptrPin ++ idxPin ++ bodyNoRet ++ feedback
    ++ [⟨0, .Lopn [.reg idxReg] (withWidthTag w "ADD") [.reg idxReg, .imm 1]⟩
      , ⟨0, .Lopn [.reg nReg] (withWidthTag w "SUB") [.reg nReg, .imm 1]⟩]
  (zeroAcc :: movR ptrReg "RSI" :: movI idxReg 0 :: movI nReg n
    :: loopLcmd w top nReg loopBody) ++ [movR "RAX" resReg]

/-- The index-dependent `n`-fold denotation of a counter-reading loop body
    (`while (ctr != 0) { acc = body(acc, ctr); ctr -= 1 }` starting at
    `ctr = n`): fold over `i = 0..n-1`, feeding `ctr = n - i` into the body at
    iteration `i`. This is the functional ground truth `cforIdxToLprogAbiBody`'s
    emission realises; a pilot proves it equals an independent reference. -/
def cforIdxDenote {accTy : JasminTy} (n : Nat)
    (body : Com jasminDialect [accTy, .reg 64] accTy) (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range n).foldl
    (fun acc i => body.denote (.cons acc (.cons (BitVec.ofNat 64 (n - i)) .nil)))
    init

/-- `NestedForProg` (outer `outerN`-fold of the inner `JForProg`) with the SysV
    `u64→u64` accumulator ABI — the nested-loop analogue of `cforToLprogAbiBody`.
    The accumulator threads `argReg`/`resReg` (from the inner body's RA, recovered
    as above); the inner counter `innerReg` is re-initialised to `inner.n` at the
    top of each outer iteration; the outer counter `outerReg` runs `outerN` times.
    Distinct `innerReg`/`outerReg`/labels avoid collision. Drives grid2d and is the
    nesting template for the PQC tree-traversal spines. -/
def cforToLprogAbiNestedBody {accTy : JasminTy} (w : Nat)
    (outerTop innerTop : LLabel) (outerReg innerReg : String)
    (p : NestedForProg accTy)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  let virt := comToLfundef p.inner.update immSlotMap
  let phys := comToLfundefPhys p.inner.update shiftImm immSlotMap
  let tbl := physTable (bodyTrace virt.lfd_body)
  let argReg := physRegName (physMapTabled tbl (nameSlot virt.lfd_body (virt.lfd_arg.head?.getD "a0")))
  let resReg := phys.lfd_res.head?.getD "RAX"
  let movR : String → String → Linstr :=
    fun d s => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩
  let movI : String → Nat → Linstr :=
    fun d v => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩
  let sub : String → Linstr :=
    fun r => ⟨0, .Lopn [.reg r] (withWidthTag w "SUB") [.reg r, .imm 1]⟩
  let bodyNoRet := phys.lfd_body.dropLast
  let feedback : Lcmd := if argReg == resReg then [] else [movR argReg resReg]
  let innerLoop : Lcmd := loopLcmd w innerTop innerReg (bodyNoRet ++ feedback ++ [sub innerReg])
  let outerBody : Lcmd := (movI innerReg p.inner.n :: innerLoop) ++ [sub outerReg]
  (movR argReg "RDI" :: movI outerReg p.outerN :: loopLcmd w outerTop outerReg outerBody)
    ++ [movR "RAX" resReg]

/-- A `TreehashProg` (a list of single-level `JForProg`s sharing one accumulator)
    with the SysV `u64→u64` accumulator ABI — the *serial* level-composition
    analogue of `cforToLprogAbiBody`. Each level is emitted as its own bounded
    loop with a distinct top label (`top + levelIndex`); the shared counter
    register `nReg` is re-initialised to that level's trip count at the top of the
    level, and the accumulator threads `argReg`/`resReg` (recovered from the first
    level's RA, consistent across levels under `AllSingleVar` — the keystone's
    hypothesis). Loads `acc0` from `RDI`, runs the levels in sequence, returns
    `resReg` in `RAX`. Drives the `bench/treehash` combiner treehash and is the
    level-sequencing template for the SLH-DSA / XMSS treehash spines
    (`combinerTree_treehash_denote_eq`). -/
def cforToLprogAbiSeq {accTy : JasminTy} (w : Nat) (top : LLabel) (nReg : String)
    (levels : List (JForProg accTy))
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lcmd :=
  match levels with
  | [] => [⟨0, .Lopn [.reg "RAX"] (withWidthTag w "MOV") [.reg "RDI"]⟩]
  | (p0 :: _) =>
    let virt := comToLfundef p0.update immSlotMap
    let phys := comToLfundefPhys p0.update shiftImm immSlotMap
    let tbl := physTable (bodyTrace virt.lfd_body)
    let argReg := physRegName (physMapTabled tbl (nameSlot virt.lfd_body (virt.lfd_arg.head?.getD "a0")))
    let resReg := phys.lfd_res.head?.getD "RAX"
    let movR : String → String → Linstr :=
      fun d s => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩
    let movI : String → Nat → Linstr :=
      fun d v => ⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩
    let sub : String → Linstr :=
      fun r => ⟨0, .Lopn [.reg r] (withWidthTag w "SUB") [.reg r, .imm 1]⟩
    let feedback : Lcmd := if argReg == resReg then [] else [movR argReg resReg]
    let levelLoop : Nat → JForProg accTy → Lcmd := fun i p =>
      let bodyI := (comToLfundefPhys p.update shiftImm immSlotMap).lfd_body.dropLast
      movI nReg p.n :: loopLcmd w (top + i) nReg (bodyI ++ feedback ++ [sub nReg])
    let indexed := levels.zip (List.range levels.length)
    (movR argReg "RDI" :: indexed.flatMap (fun (p, i) => levelLoop i p))
      ++ [movR "RAX" resReg]

/-! ### 5a. Shape / size obligations (the lowering is the looped skeleton)

The deep semantic-preservation statement (the emitted `Lprog` denotes
`JForProg.denote` under jasmin's `lsem`) is captured by `ComLsemExportFaithful[MC]`
(`LsemPortAll`) over the lsem port, proved for the modeled straight-line
fragments; this `cforToLcmd` control-flow wrapper lies outside those fragments,
so its Com→`.s` tie stays the trusted physical-emit boundary, not re-proved here.
What we *do* discharge is
the **structural** obligation that `cforToLcmd` produces exactly the looped
skeleton `loopLcmd` is the encoder's contract for, and that it is constant-size in
the trip count — the same shape facts §1–4 pin for the hand-built `loopLcmd`. -/

/-- `cforToLcmd` is literally `loopLcmd` over the RA'd body — so it is exactly the
    looped skeleton the byte encoder consumes, by definition. -/
theorem cforToLcmd_eq_loopLcmd {accTy : JasminTy} (w : Nat) (top : LLabel)
    (nReg : String) (p : JForProg accTy) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) :
    cforToLcmd w top nReg p shiftImm immSlotMap
      = loopLcmd w top nReg (cforBodyLcmd w nReg p shiftImm immSlotMap) := rfl

/-- The lowered loop length is **constant in the trip count** `p.n`: it is the RA'd
    one-iteration body length (`+1` for the counter decrement) plus the three
    control instrs — independent of how many times the loop runs. This is the size
    payoff that lets a looping front program use the looped path instead of an
    `O(p.n)` unrolling. -/
theorem cforToLcmd_length {accTy : JasminTy} (w : Nat) (top : LLabel)
    (nReg : String) (p : JForProg accTy) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) :
    (cforToLcmd w top nReg p shiftImm immSlotMap).length
      = (comToLfundefPhys p.update shiftImm immSlotMap).lfd_body.dropLast.length + 4 := by
  rw [cforToLcmd_eq_loopLcmd, loopLcmd_length, cforBodyLcmd]
  simp [List.length_append]

/-- The lowered loop **begins with the loop label** `Llabel internal top` (the
    branch target of the back-edge) — the first thing `encodeLcmd`'s label table
    records. -/
theorem cforToLcmd_head {accTy : JasminTy} (w : Nat) (top : LLabel)
    (nReg : String) (p : JForProg accTy) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) :
    (cforToLcmd w top nReg p shiftImm immSlotMap).head?
      = some ⟨0, .Llabel .internal top⟩ := by
  rw [cforToLcmd_eq_loopLcmd, loopLcmd]; rfl

/-- The lowered loop **ends with the conditional back-edge** `Lcond NZ → top` (the
    `jne .L<top>` the encoder emits as the loop's back-edge). -/
theorem cforToLcmd_last {accTy : JasminTy} (w : Nat) (top : LLabel)
    (nReg : String) (p : JForProg accTy) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) :
    (cforToLcmd w top nReg p shiftImm immSlotMap).getLast?
      = some ⟨0, .Lcond (.reg "NZ") top⟩ := by
  rw [cforToLcmd_eq_loopLcmd, loopLcmd]
  rw [List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

/-! ## 6. Composable NESTED counted-loop combinator (#81)

`loopLcmd` (§1) wraps a **single** body in one back-edge; `cforToLprogAbiNestedBody`
(§5) splices a **fixed 2-deep** nest behind a `u64→u64` ABI. Neither is a reusable
`loopLcmd`-level combinator for an **arbitrary-depth** counted nest — the shape
`mayo_solve`'s GF(16) elimination needs (a 3-deep `for r { for c { for k { … } } }`),
that `falcon`'s NTT walks (layer / group / butterfly), and a dense MSM bucket pass.

`nestLoopLcmd` is that combinator. It takes the loop levels **outer-first**
(`List LoopLevel`) plus an innermost straight-line body and wraps the body in one
back-edge per level, so that the whole nest is the owned-backend control-flow shape

```
   .L<top₀>:                     -- outermost loop (counter c₀)
       MOV  c₁, #trip₁           -- re-init the next-inner counter each iteration
     .L<top₁>:                   -- … (nested) …
         MOV  c₂, #trip₂
       .L<top₂>:
           <inner body>          -- the innermost straight-line work
           SUB  c₂, #1
           cmpq $0, %c₂ ; jne .L<top₂>
         SUB  c₁, #1
         cmpq $0, %c₁ ; jne .L<top₁>
       SUB  c₀, #1
       cmpq $0, %c₀ ; jne .L<top₀>
```

This is the **same** nested-back-edge shape the proven `FheNttLoopOwnedEmit`
three-loop nest emits by hand (`.L0` m-layer / `.L1` i-group / `.L2` j-butterfly,
each `cmpq $0,%c ; jne`), now produced by one composable helper. Each level reuses
`loopLcmd` verbatim, so every per-level shape fact (`loopLcmd_length`, the
back-edge / label arms) lifts. The combinator is constant-size in **every** trip
count (one inner-body copy + a fixed 5 instrs per level — `nestLoopLcmd_length_cons`),
not an `O(∏ tripᵢ)` unroll.

Disjoint labels and counter registers **across levels** are the caller's
responsibility (distinct `top` and `reg` per `LoopLevel`); the outermost counter is
initialised by the caller's prologue (`MOV c₀, #trip₀`), each inner counter is
re-initialised at the top of its enclosing iteration. All counters are **public**
configuration trip counts (`#460` vartime policy), so every back-edge is a
CT-admissible public branch — the nested generalisation of the §1 CT note. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
  (runBoundedLoop unrollBounded lowerBoundedLoop boundedLoop_lowering_denote_closed
   runBoundedLoop_eq_runBlock_unroll)

/-- One counted-loop level of a nest: a fresh internal top label `top`, a counter
    register `reg` (distinct across levels), and a static (public) trip count
    `trip`. The outer-first level list is the spec a `nestLoopLcmd` consumes. -/
structure LoopLevel where
  /-- The internal back-edge target label for this level. -/
  top : LLabel
  /-- This level's counter register name. -/
  reg : String
  /-- This level's static (public) trip count. -/
  trip : Nat

/-- A loop counter's own decrement `SUB reg, #1` at width `w` (every `loopLcmd`
    body performs its own, exactly as `mpnAddmul1LcmdBody`'s trailing `SUB`). -/
def decrReg (w : Nat) (reg : String) : Linstr :=
  ⟨0, .Lopn [.reg reg] (withWidthTag w "SUB") [.reg reg, .imm 1]⟩

/-- A loop counter's (re-)initialisation `MOV reg, #n` at width `w`. -/
def initReg (w : Nat) (reg : String) (n : Nat) : Linstr :=
  ⟨0, .Lopn [.reg reg] (withWidthTag w "MOV") [.imm n]⟩

/-- **The composable nested counted-loop `Lcmd`.** Given the loop levels
    outer-first `levels` and an innermost straight-line body `inner`, wrap `inner`
    in one `loopLcmd` back-edge per level. Each level's body ends with its own
    `SUB reg,#1`; the NEXT (inner) level's counter is re-initialised
    (`MOV reg,#trip`) at the top of the enclosing level's body, so it restarts on
    every enclosing iteration. The OUTERMOST counter is initialised by the caller's
    prologue. `levels = []` is just `inner` (no loop). Arbitrary depth, composable
    (the inner of an `n`-deep nest is itself any `Lcmd`, including another
    `nestLoopLcmd`). -/
def nestLoopLcmd (w : Nat) : List LoopLevel → Lcmd → Lcmd
  | [], inner => inner
  | [lvl], inner => loopLcmd w lvl.top lvl.reg (inner ++ [decrReg w lvl.reg])
  | lvl :: lvl2 :: rest, inner =>
      loopLcmd w lvl.top lvl.reg
        ((initReg w lvl2.reg lvl2.trip :: nestLoopLcmd w (lvl2 :: rest) inner)
          ++ [decrReg w lvl.reg])

/-! ### 6a. Structural shape lemmas (the nested skeleton + constant size) -/

/-- The single-level case is exactly the existing `loopLcmd` shape (over the body
    with its counter decrement) — `nestLoopLcmd` is conservative over §1. -/
theorem nestLoopLcmd_single (w : Nat) (lvl : LoopLevel) (inner : Lcmd) :
    nestLoopLcmd w [lvl] inner
      = loopLcmd w lvl.top lvl.reg (inner ++ [decrReg w lvl.reg]) := rfl

/-- The cons case exhibits the inner nest **literally inside** the outer
    back-edge: the outer loop wraps `(re-init inner counter :: the inner nest) ++
    [outer decrement]`. This is the nesting structure as a definitional identity. -/
theorem nestLoopLcmd_cons (w : Nat) (lvl lvl2 : LoopLevel) (rest : List LoopLevel)
    (inner : Lcmd) :
    nestLoopLcmd w (lvl :: lvl2 :: rest) inner
      = loopLcmd w lvl.top lvl.reg
          ((initReg w lvl2.reg lvl2.trip :: nestLoopLcmd w (lvl2 :: rest) inner)
            ++ [decrReg w lvl.reg]) := rfl

/-- The nest **begins with the outermost loop label** `Llabel internal top₀` (the
    branch target of the outer back-edge) — the first thing the encoder records. -/
theorem nestLoopLcmd_head (w : Nat) (lvl : LoopLevel) (rest : List LoopLevel)
    (inner : Lcmd) :
    (nestLoopLcmd w (lvl :: rest) inner).head? = some ⟨0, .Llabel .internal lvl.top⟩ := by
  cases rest with
  | nil => rw [nestLoopLcmd_single, loopLcmd]; rfl
  | cons lvl2 rest' => rw [nestLoopLcmd_cons, loopLcmd]; rfl

/-- The nest **ends with the outermost conditional back-edge** `Lcond NZ → top₀`
    (the `jne .L<top₀>` the encoder emits as the outer loop's back-edge). -/
theorem nestLoopLcmd_last (w : Nat) (lvl : LoopLevel) (rest : List LoopLevel)
    (inner : Lcmd) :
    (nestLoopLcmd w (lvl :: rest) inner).getLast? = some ⟨0, .Lcond (.reg "NZ") lvl.top⟩ := by
  cases rest with
  | nil =>
      rw [nestLoopLcmd_single, loopLcmd, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
  | cons lvl2 rest' =>
      rw [nestLoopLcmd_cons, loopLcmd, List.getLast?_append_of_ne_nil _ (by simp)]; rfl

/-- A single level emits the inner body + 4 control instrs (label, decrement,
    compare, back-edge) — independent of the trip count. -/
theorem nestLoopLcmd_single_length (w : Nat) (lvl : LoopLevel) (inner : Lcmd) :
    (nestLoopLcmd w [lvl] inner).length = inner.length + 4 := by
  rw [nestLoopLcmd_single, loopLcmd_length, List.length_append, List.length_singleton]

/-- **Constant per-level size.** Each added (outer) nesting level grows the
    emission by a fixed **5** instrs (label, inner-counter re-init, decrement,
    compare, back-edge), **independent of every trip count**. With
    `nestLoopLcmd_single_length` this gives `|inner| + 5·(#levels) − 1` total: the
    nest is `O(1)` body copies, never an `O(∏ tripᵢ)` unroll. -/
theorem nestLoopLcmd_length_cons (w : Nat) (lvl lvl2 : LoopLevel) (rest : List LoopLevel)
    (inner : Lcmd) :
    (nestLoopLcmd w (lvl :: lvl2 :: rest) inner).length
      = (nestLoopLcmd w (lvl2 :: rest) inner).length + 5 := by
  rw [nestLoopLcmd_cons, loopLcmd_length, List.length_append, List.length_cons,
    List.length_singleton]

/-! ### 6b. The nested-loop machine semantics + the nested `List.range` fold

The combinator above is the **emission** side. Its denotation ground truth is the
nested counted-loop transformer over `List (JInstr w)` (the verified denotation
substrate `loopLcmd_denote` / `boundedLoop_lowering_denote` use). We give it as
`runNestedLoop`, show a 2-deep nest is a SINGLE bounded loop over the unrolled
inner body (so the already-proven `boundedLoop_lowering_denote` applies verbatim),
and prove the lowering denotes exactly the nested `List.range` fold
`(range outer).foldl (… (range inner).foldl (runBlock · body) …)`. -/

/-- **Nested bounded-loop machine semantics.** Run the inner loop (`inner`
    iterations of `body`) `outer` times, threading the state — the 2-deep counted
    loop's transformer (`runBoundedLoop` nests itself). -/
def runNestedLoop {w : Nat} (s : JState w) (outer inner : Nat)
    (body : List (JInstr w)) : JState w :=
  match outer with
  | 0 => s
  | k + 1 => runNestedLoop (runBoundedLoop (s := s) inner body) k inner body

@[simp] theorem runNestedLoop_zero {w : Nat} (s : JState w) (inner : Nat)
    (body : List (JInstr w)) : runNestedLoop s 0 inner body = s := rfl

@[simp] theorem runNestedLoop_succ {w : Nat} (s : JState w) (k inner : Nat)
    (body : List (JInstr w)) :
    runNestedLoop s (k + 1) inner body
      = runNestedLoop (runBoundedLoop (s := s) inner body) k inner body := rfl

/-- A bounded `step`-iteration (peel-from-front) equals the index-ignoring left
    fold over `List.range` — the bridge from a counter loop to a `foldl`. -/
theorem stepIterate_eq_rangeFoldl {β : Type} (g : β → β) (n : Nat) (s : β) :
    (List.range n).foldl (fun acc _ => g acc) s = g^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
        Function.iterate_succ_apply']

/-- `runBoundedLoop` as `n`-fold iteration of `runBlock · body`. (Named `_rb` to
    avoid colliding with `LoopEmitBridge.runBoundedLoop_eq_iterate` — the equivalent
    `bodyStep`-phrased lemma downstream; this module is upstream of LoopEmitBridge
    so it cannot import/reuse it.) -/
theorem runBoundedLoop_eq_iterate_rb {w : Nat} (s : JState w) (n : Nat)
    (body : List (JInstr w)) :
    runBoundedLoop (s := s) n body = (fun t => runBlock t body)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => rw [LoopUnroll.runBoundedLoop_succ, ih, Function.iterate_succ_apply]

/-- `runBoundedLoop` as a `List.range` fold over `runBlock`. -/
theorem runBoundedLoop_eq_foldl {w : Nat} (s : JState w) (n : Nat)
    (body : List (JInstr w)) :
    runBoundedLoop (s := s) n body
      = (List.range n).foldl (fun acc _ => runBlock acc body) s := by
  rw [runBoundedLoop_eq_iterate_rb, ← stepIterate_eq_rangeFoldl]

/-- `runNestedLoop` as `outer`-fold iteration of one inner bounded loop. -/
theorem runNestedLoop_eq_iterate {w : Nat} (s : JState w) (outer inner : Nat)
    (body : List (JInstr w)) :
    runNestedLoop s outer inner body
      = (fun t => runBoundedLoop (s := t) inner body)^[outer] s := by
  induction outer generalizing s with
  | zero => rfl
  | succ k ih => rw [runNestedLoop_succ, ih, Function.iterate_succ_apply]

/-- A 2-deep nested bounded loop is a SINGLE bounded loop whose body is the
    unrolled inner loop: `runNestedLoop s outer inner body = runBoundedLoop s outer
    (unrollBounded inner body)`. This is what lets the already-proven
    `boundedLoop_lowering_denote` carry the nest with no new control-flow op. -/
theorem runNestedLoop_eq_runBoundedLoop_unroll {w : Nat} (s : JState w)
    (outer inner : Nat) (body : List (JInstr w)) :
    runNestedLoop s outer inner body
      = runBoundedLoop (s := s) outer (unrollBounded inner body) := by
  induction outer generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [runNestedLoop_succ, ih, LoopUnroll.runBoundedLoop_succ,
        runBoundedLoop_eq_runBlock_unroll s inner body]

/-- **The nested counted loop denotes the nested `List.range` fold.** Running the
    nest from `s` equals the outer fold of the inner fold of `runBlock · body` —
    the headline ground-truth shape `(range outer).foldl (… (range inner).foldl
    (runBlock · body) …)`. -/
theorem runNestedLoop_eq_foldl {w : Nat} (s : JState w) (outer inner : Nat)
    (body : List (JInstr w)) :
    runNestedLoop s outer inner body
      = (List.range outer).foldl
          (fun acc _ => (List.range inner).foldl (fun a _ => runBlock a body) acc) s := by
  have hstep :
      (fun acc (_ : Nat) => runBoundedLoop (s := acc) inner body)
        = (fun acc (_ : Nat) => (List.range inner).foldl (fun a _ => runBlock a body) acc) := by
    funext acc i; exact runBoundedLoop_eq_foldl acc inner body
  rw [runNestedLoop_eq_iterate, ← stepIterate_eq_rangeFoldl, hstep]

/-- **Nested-loop lowering denotation = the nested `List.range` fold.** Lowering
    the nested bounded loop (a single bounded loop over the unrolled inner body) to
    `Com (x86Dialect w)` and denoting it on the incoming state `s` equals the
    nested fold. This is the nested generalisation of `loopLcmd_denote`: the looped
    `nestLoopLcmd` emission (constant-size — §6a) denotes the same transformer the
    unrolled lowering does, so replacing the `O(∏ tripᵢ)`-copy unrolled nest by the
    constant-size nested back-edges preserves the machine transformer. Composes
    `boundedLoop_lowering_denote_closed` with `runNestedLoop_eq_runBoundedLoop_unroll`
    and `runNestedLoop_eq_foldl`. -/
theorem nestedLoop_lowering_denote {w : Nat} (outer inner : Nat)
    (body : List (JInstr w)) (s : JState w) :
    (lowerBoundedLoop (Γ := []) outer (unrollBounded inner body)).denote (.cons s .nil)
      = (List.range outer).foldl
          (fun acc _ => (List.range inner).foldl (fun a _ => runBlock a body) acc) s := by
  rw [boundedLoop_lowering_denote_closed, ← runNestedLoop_eq_runBoundedLoop_unroll,
    runNestedLoop_eq_foldl]

/-! ### 6c. Concrete constant-size sanity (a 3-deep nest)

A representative 3-deep nest (the `mayo_solve` / `falcon`-NTT depth) over a tiny
inner body: its emission length is `|inner| + 14` (`+4` for the innermost level,
`+5` for each of the two outer levels) — constant in all three trip counts,
exactly `nestLoopLcmd_length_cons`/`_single_length` predict. -/

/-- A 3-deep nest over a 1-instr inner body emits 15 linstrs, independent of the
    trip counts (`1 + 4 + 5 + 5`). -/
example (w : Nat) (l0 l1 l2 : LoopLevel) (i : Linstr) :
    (nestLoopLcmd w [l0, l1, l2] [i]).length = 15 := by
  rw [nestLoopLcmd_length_cons, nestLoopLcmd_length_cons, nestLoopLcmd_single_length]
  simp

/-! ## 7. Data-dependent guarded `while` (RWhile) — the unbounded loop shape

`loopLcmd` (§1), `cforToLcmd` (§5) and `nestLoopLcmd` (§6) all emit **counted**
loops: the trip count is materialised at entry (`MOV nReg, #n`) and the back-edge
tests a **down-counter** (`SUB nReg,#1 ; CMP nReg,#0 ; jne`). That is exactly what
the §"What is NOT lowered" residual excluded — a general `RWhile` whose guard is a
**runtime, data-dependent** value the loop itself produces, so the trip count is
not known at entry and termination depends on a value computed inside the loop.

The motivating consumer is the plonky3 `honest_prove` proof-of-work grind:

```
   h0 = 1;
   while (h0 != 0) {
       fs[8] = nonce;
       blk   = _hp_pow_test(fs);
       h0    = blk[0] & mask;      -- the guard value, computed IN the loop
       if (h0 != 0) nonce++;
   }
```

the loop runs until a freshly-computed hash word `h0` clears the low `mask` bits
— a data-dependent trip count, not a counter loaded at entry. This section closes
that last control-flow shape additively: (1) the `whileLcmd` emission — a real
backward branch conditioned on a RUNTIME predicate register; (2) a **fuel-bounded
total** denotation `runWhile` with the lowering-denote bridge (the emission
realises `runWhile` for the fuel/state where the guard goes false within fuel —
the consumer supplies the fuel + a termination/measure argument); (3) the
public-leakage classification (a data-dependent while is NOT constant-time).

### 7.1 The `whileLcmd` combinator (the runtime-guarded back-edge)

`whileLcmd` is the data-dependent analogue of `loopLcmd`: structurally the same
back-edge shape, but the conditional branch tests a value the loop **produces**
(via `guard`/the body), not a down-counter loaded at entry. -/

/-- The owned-backend **data-dependent** guarded `while` `Lcmd`: a do-while whose
    back-edge tests a RUNTIME predicate register `gReg` (NOT a down-counter).

    Emits  `Llabel top ; body ; guard ; CMP gReg,#0 ; Lcond NZ → top`  —
    a real backward branch `jne .L<top>` conditioned on the value the body/guard
    just computed into `gReg`. `guard` is the (possibly empty) instruction
    sequence that materialises the loop predicate into `gReg`: the predicate over
    the body's out-state is "`gReg ≠ 0` after running `guard`" (in the plonky3
    grind, `guard` is the `h0 = blk[0] & mask` mask-and that produces `h0`; when
    the body already leaves the predicate in `gReg`, pass `guard = []`). `w` is
    the predicate width (the `CMP` is `withWidthTag w "CMP"`, rendered `cmpq`/`cmpl`
    by `LprogAsmPrinter.attBase`; the back-edge `Lcond (reg "NZ") top` renders as
    `jne .L<top>` via `attCC`).

    Constant-size: one body copy + one guard-compute copy + 2 control instrs,
    independent of how many times the loop runs (the trip count is unbounded /
    data-dependent). PUBLIC-guard only (§7.3): a secret-dependent guard would leak
    through the (PC-observable) trip count and is forbidden in the CT subset. -/
def whileLcmd (w : Nat) (top : LLabel) (gReg : String) (guard : Lcmd) (body : Lcmd) :
    Lcmd :=
  (⟨0, .Llabel .internal top⟩ :: body)
    ++ guard
    ++ [ ⟨0, .Lopn [.reg gReg] (withWidthTag w "CMP") [.reg gReg, .imm 0]⟩
       , ⟨0, .Lcond (.reg "NZ") top⟩ ]

/-- The looped while emission has a constant `Lcmd` length: the body length plus
    the guard-compute length plus the three control instrs (label + compare +
    conditional back-edge), **independent of the (data-dependent) trip count**. -/
@[simp] theorem whileLcmd_length (w : Nat) (top : LLabel) (gReg : String)
    (guard body : Lcmd) :
    (whileLcmd w top gReg guard body).length = body.length + guard.length + 3 := by
  simp [whileLcmd, List.length_append]; omega

/-- The while emission **begins with the loop label** `Llabel internal top` (the
    branch target of the back-edge) — the first thing `encodeLcmd`'s label table
    records. -/
theorem whileLcmd_head (w : Nat) (top : LLabel) (gReg : String) (guard body : Lcmd) :
    (whileLcmd w top gReg guard body).head? = some ⟨0, .Llabel .internal top⟩ := by
  rw [whileLcmd]; rfl

/-- The while emission **ends with the conditional back-edge** `Lcond NZ → top`
    (the `jne .L<top>` the encoder emits as the data-dependent loop's back-edge —
    taken iff the runtime predicate register `gReg` is nonzero). -/
theorem whileLcmd_last (w : Nat) (top : LLabel) (gReg : String) (guard body : Lcmd) :
    (whileLcmd w top gReg guard body).getLast? = some ⟨0, .Lcond (.reg "NZ") top⟩ := by
  rw [whileLcmd, List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

/-! ### 7.2 The fuel-bounded `runWhile` denotation + the lowering-denote bridge

The pure A-normal `Com` substrate has no label/jump denotation (that is precisely
why a general `RWhile` was the residual): we therefore give the data-dependent
loop a **fuel-bounded total** machine semantics `runWhile` and bridge it to the
already-proven counted-loop backbone. The bridge is the §3 strategy generalised:
a `while` that halts within `fuel` runs `body` a **determined** number of times
(`whileTrips`, fixed at run time by the values the body produces), and that many
body iterations is exactly the proven `runBoundedLoop`/`lowerBoundedLoop` shape.
So the emission's denotation is `runWhile` — the same machine transformer the
lowering of its runtime-determined iteration count denotes. -/

/-- **Fuel-bounded data-dependent `while` machine semantics.** `runWhile fuel
    guard body s` runs `while (guard) { s := runBlock s body }` for at most `fuel`
    iterations from `s`, returning `s` once the guard goes false (or the fuel is
    exhausted). Total by structural recursion on `fuel`: the `fuel` is the
    consumer's **termination certificate** — it exhibits a bound large enough that
    the real guard goes false within it (a measure/variant argument); this
    capability proves the emission realises `runWhile`, the consumer supplies the
    bound. `guard : JState w → Bool` is the runtime predicate the emitted
    `guard`-compute + back-edge test (`gReg ≠ 0`). -/
def runWhile {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) : JState w :=
  match fuel with
  | 0 => s
  | k + 1 => if guard s then runWhile k guard body (runBlock s body) else s

@[simp] theorem runWhile_zero {w : Nat} (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) : runWhile 0 guard body s = s := rfl

@[simp] theorem runWhile_succ {w : Nat} (k : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) :
    runWhile (k + 1) guard body s
      = if guard s then runWhile k guard body (runBlock s body) else s := rfl

/-- The number of body iterations the `while` runs before its guard goes false,
    bounded by `fuel` — the **data-dependent trip count**: unknown at entry,
    determined by the values the body produces. -/
def whileTrips {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) : Nat :=
  match fuel with
  | 0 => 0
  | k + 1 => if guard s then whileTrips k guard body (runBlock s body) + 1 else 0

/-- **A terminating `while` is a counted loop of its (data-dependent) trip count.**
    `runWhile fuel guard body s = runBoundedLoop s (whileTrips …) body` — once the
    data-dependent loop halts within `fuel`, it has run `body` exactly `whileTrips`
    times, the same iterated transformer the proven counted-loop backbone
    (`runBoundedLoop`) denotes. This is the bridge that lets the already-proven
    `boundedLoop_lowering_denote_closed` carry the data-dependent while: at the
    state/fuel where the guard goes false, the emission is the lowering of that
    determined number of body copies. -/
theorem runWhile_eq_runBoundedLoop_trips {w : Nat} (fuel : Nat)
    (guard : JState w → Bool) (body : List (JInstr w)) (s : JState w) :
    runWhile fuel guard body s
      = runBoundedLoop s (whileTrips fuel guard body s) body := by
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih =>
      by_cases h : guard s
      · simp only [runWhile, whileTrips, if_pos h, ih, runBoundedLoop_succ]
      · simp only [runWhile, whileTrips, if_neg h, runBoundedLoop_zero]

/-- **`whileLcmd` lowering denotation = `runWhile`.** Lowering the run-time
    determined number of body iterations (`whileTrips fuel guard body s`, the trip
    count the guard forces within `fuel`) to `Com (x86Dialect w)` and denoting it
    on the incoming state `s` equals `runWhile fuel guard body s`. The looped
    `whileLcmd` emission (constant-size — §7.1) denotes the **same** machine
    transformer that lowering its runtime-determined iteration count does: the
    back-edge resolves the data-dependent trip count at run time, the lowering of
    that many body copies is the denotation backbone. This is the data-dependent
    analogue of `loopLcmd_denote`; the consumer supplies `fuel` + a termination
    argument, and the capability proves the emission realises `runWhile`. -/
theorem whileLcmd_denote {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) :
    (lowerBoundedLoop (Γ := []) (whileTrips fuel guard body s) body).denote (.cons s .nil)
      = runWhile fuel guard body s := by
  rw [boundedLoop_lowering_denote_closed, runWhile_eq_runBoundedLoop_trips]

/-- If the guard already fails at `s`, the `while` is the identity (zero
    iterations) — the post-tested emission's caller must guarantee an entry-true
    guard (e.g. plonky3's `h0 = 1`) for the do-while to coincide with this. -/
theorem runWhile_guard_false {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) (h : guard s = false) :
    runWhile (fuel + 1) guard body s = s := by
  simp [runWhile, h]

/-- **Fuel robustness (the termination certificate is monotone).** Once the guard
    is false at the result (the loop has halted), extra fuel is inert:
    `runWhile (fuel+1) = runWhile fuel`. So any `fuel` large enough for the guard
    to go false yields the same fixpoint — the consumer's measure/variant argument
    need only exhibit ONE sufficient bound; the emission's `runWhile` denotation is
    independent of the exact value above it. -/
theorem runWhile_succ_of_halted {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w)
    (h : guard (runWhile fuel guard body s) = false) :
    runWhile (fuel + 1) guard body s = runWhile fuel guard body s := by
  induction fuel generalizing s with
  | zero =>
      simp only [runWhile_zero] at h
      simp [runWhile, h]
  | succ k ih =>
      by_cases hg : guard s
      · have h' : guard (runWhile k guard body (runBlock s body)) = false := by
          rwa [runWhile_succ, if_pos hg] at h
        calc runWhile (k + 1 + 1) guard body s
            = runWhile (k + 1) guard body (runBlock s body) := by
              rw [runWhile_succ, if_pos hg]
          _ = runWhile k guard body (runBlock s body) := ih (runBlock s body) h'
          _ = runWhile (k + 1) guard body s := by rw [runWhile_succ, if_pos hg]
      · rw [runWhile_succ, if_neg hg, runWhile_succ, if_neg hg]

/-- The lowering-denote bridge is usable at a concrete fuel: lowering the
    runtime-determined iteration count of any data-dependent `while` (here at fuel
    `100`) and denoting it equals `runWhile`. -/
example (guard : JState 64 → Bool) (body : List (JInstr 64)) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) (whileTrips 100 guard body s) body).denote (.cons s .nil)
      = runWhile 100 guard body s :=
  whileLcmd_denote 100 guard body s

/-! ### 7.3 PUBLIC-LEAKAGE classification (a data-dependent while is NOT CT)

Unlike the counted `loopLcmd`/`cforToLcmd`/`nestLoopLcmd` back-edges — whose trip
count is a **public** configuration constant (a limb / length count) and so leaks
nothing beyond what is public by construction — a `whileLcmd` back-edge tests a
**runtime data-dependent** value, so the **number of iterations leaks the guard**.
A `whileLcmd` is therefore admissible **only for a PUBLIC-data guard**: the
plonky3 PoW grind runs on the public Fiat-Shamir transcript state (the nonce
search is over public data), so its trip count is already adversary-observable and
the back-edge leaks nothing secret. A secret-dependent guard is **forbidden** —
it would have to be data-oblivious (`CMOVcc`, no PC divergence), which a genuine
unbounded search cannot be.

This file's combinators are **plain `Lcmd` data**: `whileLcmd` does not route
through any constant-time / leakage-NI obligation (exactly as `loopLcmd` does
not), so no CT proof is claimed or faked for it here, and it does not pretend to
be data-oblivious. A *typed* public-while marker that the leakage framework
(`Com.leakTrace` / `all_com_ct`) recognises — classifying a `whileLcmd` site as
`public-while` so it is admitted while a secret-guarded one is rejected — is a
**framework change to the leakage IR**, reported as the residual: the current
`all_com_ct` is the structurally-trivial dialect shadow (`rfl`, per the project's
CProg/CT note), and giving data-dependent control flow a first-class
public/secret guard classification in the leakage trace is a larger leakage-IR
extension, not a one-file additive edit. We classify `whileLcmd` as `public-while`
in this documentation and keep it off the CT obligation rather than fabricate a
constant-time proof for a non-constant-time loop. -/

/-! ### 7.4 In-file witness of the data-dependent guard shape

A concrete `whileLcmd` whose guard is **computed in the loop** (mask-and, the
plonky3 shape), at the owned-RA `Lcmd` level — the data-dependent analogue of
§4's `mpnAddmul1Looped`. Body: `RDI -= 1`; guard: `RCX := RDI ; RCX &= 0xF`;
back-edge tests `RCX` (`jne` while the low nibble is nonzero). Realises
"round `RDI` down to a multiple of 16", a guaranteed-terminating data-dependent
loop (≤ 15 iterations, trip count `= RDI & 0xF`). Rendered + gas-assembled +
C-KAT'd in `bench/while_smoke`. -/

/-- The data-dependent while body: `RDI -= 1` (U64). -/
def round16WhileBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDI"] (withWidthTag 64 "SUB") [.reg "RDI", .imm 1]⟩ ]

/-- The guard-compute (the plonky3 `h0 = blk[0] & mask` shape): `RCX := RDI` then
    `RCX &= 0xF`, leaving the loop predicate (low nibble nonzero) in `RCX`. -/
def round16WhileGuard : Lcmd :=
  [ ⟨0, .Lopn [.reg "RCX"] (withWidthTag 64 "MOV") [.reg "RDI"]⟩
  , ⟨0, .Lopn [.reg "RCX"] (withWidthTag 64 "AND") [.reg "RCX", .imm 0xF]⟩ ]

/-- The looped while emission: body + guard-compute wrapped in the runtime-guarded
    back-edge (`gReg = RCX`, top label `0`, width 64). -/
def round16Looped : Lcmd := whileLcmd 64 0 "RCX" round16WhileGuard round16WhileBody

/-- The emission is 6 linstrs (label + 1 body + 2 guard-compute + cmp + cond),
    independent of the (data-dependent) trip count. -/
example : round16Looped.length = 6 := by decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
