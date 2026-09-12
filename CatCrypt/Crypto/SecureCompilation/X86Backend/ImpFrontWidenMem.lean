/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImpFrontWiden
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnifiedMem

/-!
# w6-mem — widening the source front over MEMORY ops via the public-index route

`ImpFrontWiden.lean` (w6) widened the source front over the all-`IsDirect`
fragment (scalar arith + branchless select + bounded literal loop), feeding the
w7 unified backend `lowerUProg`, and discharged the capstone's assumed middle as
the `LoweringCTPreserving` interface — whose conclusion is the
unconditional `CompilableCT b = allDirect b` (the trace is identical from *any*
two states).

Array load/store do **not** fit that interface.  They lower to the
register-INDEXED machine ops `loadMemIdx`/`storeMemIdx`, which are **not**
`IsDirect`: a load/store reads its index register's value, so its leakage trace
is identical only across states that **agree on the public index**.  Their
constant-time guarantee therefore has the *different*, weaker-and-more-general
`agreePub` shape that the w7-mem backend (`LowCTUnifiedMem.lean`) provides
uniformly via `lowerUMProg_constant_time` under the frame/data register
discipline `BlockFrameWF`.

This module widens the SOURCE front over memory.  It recognizes, in addition to
lifting the existing w6 arith/select shapes via `UMStmt.base`:

* an **array load** `assign dst (app "arr_load" [var arr, var idx])` — mapped to
  `UMStmt.memLoad { dst, arr, idx, scale := 8, dstTy := .TU64, arrTy := .TU64 }`
  (a `loadMemIdx`, index-register-addressed);
* an **array store** `app "arr_store" [var arr, var idx, var src]` — an `app` in
  statement position, since a store produces no destination register — mapped to
  `UMStmt.memStore { arr, idx, src, scale := 8, arrTy := .TU64, srcTy := .TU64 }`
  (a `storeMemIdx`).

and lowers the whole through the w7-mem unified backend (`lowerUMProg`).

## What is proved

* `impStmtToUM : ImpExpr → Option UMStmt` — recognize one supported statement:
  array load, array store, or any w6 arith/select shape lifted via `.base`.
* `impToUM : ImpExpr → Option UMProg` — the seq-chain translator (straight-line
  memory + lifted base statements).
* `impLowerUM : ImpExpr → Option (List (JInstr 64))` — post-composes
  `lowerUMProg idRho`.
* `LoweringMemCTPreserving` — the memory-CT-preservation interface, the
  `agreePub`-conditioned analogue of `LoweringCTPreserving`.
* `impLowerUM_MemCTPreserving` (**the headline**) — `LoweringMemCTPreserving pub
  impLowerUM` for every `pub`, directly from `lowerUMProg_constant_time`.
* a worked memory `example` (load–arith–store cell), shown to lower, satisfy
  `BlockFrameWF`, and obtain the `agreePub`-conditioned CT — the non-vacuity
  witness exercising the memLoad/memStore path.

## CT conclusion shape — why `agreePub`-conditioned, not full-state-independent

`LoweringCTPreserving` concludes `CompilableCT b` = `blockLeak s₁ b = blockLeak
s₂ b` for **any** `s₁ s₂`.  Value-indexed memory cannot satisfy that: a
`storeMemIdx`/`loadMemIdx` reads its index register, so its address leakage
depends on that register's value.  The honest, achievable guarantee is leakage
equality across states that **agree on the public registers** (frame
bases/indices/counters) — `agreePub pub s₁ s₂` — under the frame/data discipline
`BlockFrameWF pub b` (index registers public, computed-word destinations data).
That discipline is the necessary register-allocation contract for value-indexed
memory, recorded exactly as `LowCTUnifiedMem`/`LowCTMemCT` do; a real allocator
keeping bases/indices/counters in a frame and computed words in data registers
provides it.

## Scope notes

The translator keeps memory straight-line in this on-ramp: `impToUM` recognizes
a `seq`-chain of array load/store and lifted base statements.  Memory inside a
bounded loop is supported by the backend type (`UMStmt.forM` body may contain
memory statements) and the uniform CT covers it; threading the source `forLoop`
into `UMStmt.forM` is a clean extension that mirrors `ImpFrontWiden.impHeadToU`'s
loop case but to the memory loop constructor.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImpFrontWidenMem

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnifiedMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImpFrontWiden

/-! ## 1. Recognizing one supported statement (memory load/store or a lifted base)

A single supported statement, in priority order:

* **array load** `assign dst (app "arr_load" [var arr, var idx])` → a
  `UMStmt.memLoad` (stride 8, `TU64` element / array type);
* **array store** `app "arr_store" [var arr, var idx, var src]` → a
  `UMStmt.memStore` (an `app` in statement position — a store has no destination
  register);
* otherwise, any w6 arith/select shape recognized by `impStmtToU`, lifted with
  `UMStmt.base`. -/

/-- Recognize a single supported statement and produce its unified-with-memory
    statement.

    * `assign dst (app "arr_load" [var arr, var idx])` — an array load
      `UMStmt.memLoad`;
    * `app "arr_store" [var arr, var idx, var src]` — an array store
      `UMStmt.memStore`;
    * anything `impStmtToU` (w6) recognizes (arith / select) — lifted via
      `UMStmt.base`.

    Anything else returns `none`. -/
def impStmtToUM : ImpExpr → Option UMStmt
  | .assign dst (.app "arr_load" [.var arr, .var idx]) =>
      some (.memLoad { dst := dst, arr := arr, idx := idx, scale := 8,
                       dstTy := .TU64, arrTy := .TU64 })
  | .app "arr_store" [.var arr, .var idx, .var src] =>
      some (.memStore { arr := arr, idx := idx, src := src, scale := 8,
                        arrTy := .TU64, srcTy := .TU64 })
  | e => (impStmtToU e).map UMStmt.base

/-! ## 2. The widened-with-memory partial translator

A right-nested `seq` chain of supported statements, terminated by `unitVal`.
Each statement is an array load, an array store, or a w6 arith/select lifted via
`.base`.  (Memory-in-loops is a clean extension — see the module scope notes.) -/

/-- **The widened-with-memory partial translator.**  Recognize a `seq`-chain of
    supported statements (memory load/store + lifted base statements) and produce
    the corresponding `UMProg`; `none` for any unsupported constructor or shape.

    * `unitVal` — the empty block (`some []`);
    * `seq stmt rest` — a recognized head statement followed by a recognized tail;
    * a bare supported statement — a singleton block;
    * everything else — `none`. -/
def impToUM : ImpExpr → Option UMProg
  | .unitVal => some []
  | .seq e1 e2 =>
      match impStmtToUM e1, impToUM e2 with
      | some st, some rest => some (st :: rest)
      | _, _ => none
  | e => (impStmtToUM e).map (fun st => [st])

/-! ## 3. The concrete widened-with-memory lowering -/

/-- **The concrete widened-with-memory lowering.**  Translate the supported
    subset to a `UMProg`, then lower with `lowerUMProg` under the identity
    register map (`idRho`).  Matches the `ImpExpr → Option (List (JInstr 64))`
    type the capstone's `lower` expects.  `none` outside the translatable
    fragment. -/
def impLowerUM (e : ImpExpr) : Option (List (JInstr 64)) :=
  (impToUM e).map (fun p => lowerUMProg idRho p)

/-! ## 4. The memory-CT capstone: `LoweringMemCTPreserving`

`LoweringCTPreserving` demands full state-independence (`CompilableCT b` =
`blockLeak s₁ b = blockLeak s₂ b` for *any* `s₁ s₂`), which value-indexed memory
cannot satisfy.  The honest interface is the `agreePub`-conditioned one: under
the frame/data discipline `BlockFrameWF pub b`, leakage is equal across any two
states agreeing on the public registers.  We define that interface and prove the
lowering satisfies it directly from the backend's uniform CT theorem. -/

/-- **The memory-CT-preservation interface** — the `agreePub`-conditioned
    analogue of `SecureCompileChain.LoweringCTPreserving`.  A lowering is
    memory-CT-preserving for a public predicate `pub` when, on every `some`-output
    `b` that satisfies the frame/data discipline `BlockFrameWF pub b`, the
    machine leakage trace is identical from any two states that **agree on the
    public registers** (`agreePub pub`).

    This is the correct CT shape for value-indexed memory: leakage is a function
    of the public inputs (frame bases/indices/counters) alone, not unconditionally
    state-independent. -/
def LoweringMemCTPreserving (pub : PubPred)
    (lower : ImpExpr → Option (List (JInstr 64))) : Prop :=
  ∀ (e : ImpExpr) (b : List (JInstr 64)),
    lower e = some b → BlockFrameWF pub b →
    ∀ (s₁ s₂ : JState 64), agreePub pub s₁ s₂ → blockLeak s₁ b = blockLeak s₂ b

/-- **The discharge (headline).**  `impLowerUM` is memory-CT-preserving for
    **every** public predicate `pub`: any `some`-output `b` is `lowerUMProg idRho
    p` for some `p : UMProg`, and the backend's uniform CT theorem
    `lowerUMProg_constant_time` delivers leakage equality across `agreePub`-states
    under the supplied `BlockFrameWF`.

    This is the memory-fragment analogue of `ImpFrontWiden.impLowerU_CTPreserving`,
    in the `agreePub`-conditioned shape that value-indexed memory requires — not
    the unconditional full-state-independence of `LoweringCTPreserving`. -/
theorem impLowerUM_MemCTPreserving (pub : PubPred) :
    LoweringMemCTPreserving pub impLowerUM := by
  intro e b hlow hwf s₁ s₂ hag
  unfold impLowerUM at hlow
  cases hp : impToUM e with
  | none => simp [hp] at hlow
  | some p =>
      simp only [hp, Option.map_some, Option.some.injEq] at hlow
      subst hlow
      exact lowerUMProg_constant_time pub idRho p hwf s₁ s₂ hag

/-! ## 5. Worked memory instance (non-vacuity)

A concrete memory `ImpExpr`: load an array element, accumulate it, store it back
— a small bignum-cell analogue.  We show it lowers via the memLoad/memStore path,
exhibit a `pub` predicate, prove `BlockFrameWF`, and conclude the
`agreePub`-conditioned CT. -/

/-- A load–accumulate–store cell in the source language:

    ```
      ai := a[i]          -- assign ai (app "arr_load" [var a, var i])
      acc := acc + ai     -- assign acc (app "add" [var acc, var ai])
      r[i] := acc         -- app "arr_store" [var r, var i, var acc]
    ```

    chained by `seq` and terminated by `unitVal`.  Exercises BOTH memory shapes
    (load and store) plus a lifted base arith statement. -/
def demoMemCell : ImpExpr :=
  .seq (.assign "ai" (.app "arr_load" [.var "a", .var "i"]))
    (.seq (.assign "acc" (.app "add" [.var "acc", .var "ai"]))
      (.seq (.app "arr_store" [.var "r", .var "i", .var "acc"]) .unitVal))

/-- The corresponding unified-with-memory program (memLoad, base arith, memStore). -/
def demoMemProg : UMProg :=
  [ .memLoad { dst := "ai", arr := "a", idx := "i", scale := 8,
               dstTy := .TU64, arrTy := .TU64 }
  , .base (.arith { dst := "acc", a := "acc", op := .add, b := "ai" })
  , .memStore { arr := "r", idx := "i", src := "acc", scale := 8,
                arrTy := .TU64, srcTy := .TU64 } ]

/-- `impLowerUM` translates the cell via the memLoad/arith/memStore path. -/
theorem demoMemCell_lowers :
    impLowerUM demoMemCell = some (lowerUMProg idRho demoMemProg) := by
  simp [impLowerUM, impToUM, impStmtToUM, impStmtToU, demoMemCell, demoMemProg]

/-- The lowered cell. -/
def demoMemBlock : List (JInstr 64) := lowerUMProg idRho demoMemProg

/-- The public/secret split for the cell: array bases `a`, `r` and the index `i`
    are public (frame) registers; computed words `ai`, `acc` are data registers. -/
def demoPub : PubPred := fun r => r = "a" || r = "r" || r = "i"

/-- **The cell's lowering satisfies the frame/data discipline.**  Decided: the
    only index registers are `i` (public); the only destination registers are
    `ai`, `acc` (both data, non-public).  Mirrors
    `LowCTUnifiedMem.bignumKernel_frameWF`. -/
theorem demoMem_frameWF : BlockFrameWF demoPub demoMemBlock := by
  constructor
  · decide
  · decide

/-- **The worked memory instance (non-vacuity).**  The load–accumulate–store cell
    leaks nothing about its secret operands: any two states agreeing on the
    public frame registers (`a`, `r`, `i`) — but differing arbitrarily on the
    secret limb data — produce the same machine leakage trace.  Obtained from the
    discharged memory-CT capstone `impLowerUM_MemCTPreserving` applied to the
    concrete cell — this uses the memLoad/memStore path, not arith alone. -/
theorem demoMemCell_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub demoPub s₁ s₂) :
    blockLeak s₁ demoMemBlock = blockLeak s₂ demoMemBlock :=
  impLowerUM_MemCTPreserving demoPub demoMemCell demoMemBlock
    demoMemCell_lowers demoMem_frameWF s₁ s₂ hag

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImpFrontWidenMem
