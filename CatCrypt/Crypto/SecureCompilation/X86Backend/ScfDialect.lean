/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

/-!
# Structured-control-flow (`scf`) dialect over the owned x86 machine (#566)

A VIR `Dialect` whose ops are the MLIR-`scf`-style structured control constructs —
a bounded `for` and a two-arm `if` — over the owned x86 machine state `JState w`.
It is the structured-control-flow tier of the Com/VIR substrate: protocols that
today emit a fully-unrolled straight-line block (FAEST/ML-DSA/ML-KEM, every kernel
whose `.jazz` `inline for` unrolls) can instead carry the loop as a *single
first-class `scf.for` op* with an explicit trip count and body, and the verified
`scf → cf` lowering compiles it to the proven straight-line form.

## Region-free encoding

VIR's `Com`/`Expr` are deliberately region-free (`VIR.Core`: "no regions"). So an
`scf.for`'s body is **not** a nested `Com` region; it is an *op parameter* — the
`List (JInstr w)` loop body plus the compile-time trip count `n` — exactly as the
existing `LoopUnroll.runBoundedLoop` / `lowerBoundedLoop` machinery already models
it. The structured op is therefore a single-output, region-free dialect op whose
denotation is `runBoundedLoop`, and whose `scf → cf` lowering is `lowerBoundedLoop`
(unroll-then-lower), with denotation-preservation discharged by the already-proven
`LoopUnroll.boundedLoop_lowering_denote`. No new loop semantics are introduced;
this packages the proven machinery as a composable dialect op.

## Ops (`ScfOp`)

* `forN w n body`  — run `body : List (JInstr w)` exactly `n` times, threading the
                     machine state. Denotation `runBoundedLoop s n body`.
* `ifTE w t e`     — run `t` if the flag is set, else `e`. Denotation
                     `if c then runBlock s t else runBlock s e`.

## What is proved

* `scfFor_denote` / `scfIf_denote` — the op denotations are exactly the
  state-transformers above (definitional).
* `scfFor_lowering_denote` — **the `scf → cf` denotation-preservation**: the
  `scf.for` op denotes the same machine-state transformer as its lowered straight-line
  `cf` image `lowerBoundedLoop n body`. This is `boundedLoop_lowering_denote` lifted
  to the dialect op.
* Canonicalisation / fold lemmas: `scfFor_zero` (empty loop = identity),
  `scfFor_succ` (peel one iteration), `scfIf_true` / `scfIf_false` (constant-flag
  fold) — the denotation-level rewrites a `canonicalize`/`fold` pass applies.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ScfDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

/-! ## 1. Types -/

/-- The `scf` dialect's value-type alphabet: the owned x86 machine state at width
    `w`, and a boolean control flag. -/
inductive ScfTy where
  /-- The owned x86 machine state, `⟦·⟧ = JState w`. -/
  | mach (w : Nat)
  /-- A control flag, `⟦·⟧ = Bool`. -/
  | flag
  deriving DecidableEq

/-- Total denotation of `ScfTy`. -/
@[reducible] instance : TyDenote ScfTy where
  denote
    | .mach w => JState w
    | .flag => Bool

/-! ## 2. Op tags -/

/-- Structured-control-flow operations over the machine state. The loop / branch
    bodies are op parameters (region-free encoding, see module docstring). -/
inductive ScfOp where
  /-- Bounded `for`: run `body` exactly `n` times on the machine state. -/
  | forN (w : Nat) (n : Nat) (body : List (JInstr w))
  /-- Two-arm `if`: run `thenB` when the flag is set, else `elseB`. -/
  | ifTE (w : Nat) (thenB elseB : List (JInstr w))

/-- The `scf` dialect. -/
@[reducible] def scfDialect : Dialect :=
  { Op := ScfOp, Ty := ScfTy }

/-! ## 3. Op signatures -/

instance : DialectSignature scfDialect where
  sig op := match op with
    | .forN w _ _ => [.mach w]
    | .ifTE w _ _ => [.flag, .mach w]
  ret op := match op with
    | .forN w _ _ => .mach w
    | .ifTE w _ _ => .mach w

/-! ## 4. Op denotation -/

instance scfDenote : DialectDenote scfDialect where
  denote op := match op with
    | .forN _ n body => fun args =>
        let s : JState _ := args.head
        runBoundedLoop s n body
    | .ifTE _ thenB elseB => fun args =>
        let c : Bool := args.head
        let s : JState _ := args.tail.head
        if c then runBlock s thenB else runBlock s elseB

/-! ## 5. Single-op `Com` programs and their denotations -/

/-- The one-op `scf.for` program over `[mach w]`. -/
def scfForProg (w n : Nat) (body : List (JInstr w)) :
    Com scfDialect [.mach w] (.mach w) :=
  .var (.mk (.forN w n body) rfl (.cons .here .nil)) (.ret .here)

/-- The one-op `scf.if` program over `[flag, mach w]`. -/
def scfIfProg (w : Nat) (thenB elseB : List (JInstr w)) :
    Com scfDialect [.flag, .mach w] (.mach w) :=
  .var (.mk (.ifTE w thenB elseB) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **`scf.for` denotation.** On a state `s` the `scf.for` program denotes the
    bounded-loop machine semantics. -/
@[simp] theorem scfFor_denote (w n : Nat) (body : List (JInstr w)) (s : JState w) :
    (scfForProg w n body).denote (.cons s .nil) = runBoundedLoop s n body := rfl

/-- **`scf.if` denotation.** On a flag `c` and state `s`, the `scf.if` program
    denotes the conditional block run. -/
@[simp] theorem scfIf_denote (w : Nat) (thenB elseB : List (JInstr w))
    (c : Bool) (s : JState w) :
    (scfIfProg w thenB elseB).denote (.cons c (.cons s .nil))
      = (if c then runBlock s thenB else runBlock s elseB) := rfl

/-! ## 6. The `scf → cf` lowering and its denotation-preservation -/

/-- Lower an `scf.for` to its `cf`-level image: unroll `n` times and lower to the
    straight-line `Com (x86Dialect w)` block (`LoopUnroll.lowerBoundedLoop`). -/
def lowerScfFor (w n : Nat) (body : List (JInstr w)) :
    Com (x86Dialect w) [X86Ty.machine w] (X86Ty.machine w) :=
  lowerBoundedLoop (Γ := []) n body

/-- **`scf → cf` denotation-preservation.** The `scf.for` op denotes the same
    machine-state transformer as its lowered straight-line `cf` image. This is the
    structured-loop lowering correctness, lifted from `boundedLoop_lowering_denote`
    to the dialect op. -/
theorem scfFor_lowering_denote (w n : Nat) (body : List (JInstr w)) (s : JState w) :
    (scfForProg w n body).denote (.cons s .nil)
      = (lowerScfFor w n body).denote (.cons s .nil) := by
  rw [scfFor_denote, lowerScfFor, boundedLoop_lowering_denote_closed]

/-! ## 7. Canonicalisation / fold lemmas (the `canonicalize` / `fold` pass)

These are the denotation-level rewrites a structured-control-flow `canonicalize`
pass applies: an empty loop is the identity, a `succ` loop peels one body, and a
constant-flag `if` folds to one arm. Each is a `Com`-denotation equality, so the
pass is denotation-preserving by construction. -/

/-- **Empty-loop canonicalisation.** `scf.for 0` is the identity on the state. -/
@[simp] theorem scfFor_zero (w : Nat) (body : List (JInstr w)) (s : JState w) :
    (scfForProg w 0 body).denote (.cons s .nil) = s := by
  rw [scfFor_denote, runBoundedLoop_zero]

/-- **Loop peel.** `scf.for (n+1)` runs the body once then `scf.for n` from the
    resulting state — the unrolling rewrite. -/
theorem scfFor_succ (w n : Nat) (body : List (JInstr w)) (s : JState w) :
    (scfForProg w (n + 1) body).denote (.cons s .nil)
      = (scfForProg w n body).denote (.cons (runBlock s body) .nil) := by
  rw [scfFor_denote, scfFor_denote, runBoundedLoop_succ]

/-- **Constant-`true` fold.** `scf.if true t e` folds to running `t`. -/
@[simp] theorem scfIf_true (w : Nat) (thenB elseB : List (JInstr w)) (s : JState w) :
    (scfIfProg w thenB elseB).denote (.cons true (.cons s .nil))
      = runBlock s thenB := by
  rw [scfIf_denote]; simp

/-- **Constant-`false` fold.** `scf.if false t e` folds to running `e`. -/
@[simp] theorem scfIf_false (w : Nat) (thenB elseB : List (JInstr w)) (s : JState w) :
    (scfIfProg w thenB elseB).denote (.cons false (.cons s .nil))
      = runBlock s elseB := by
  rw [scfIf_denote]; simp

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScfDialect
