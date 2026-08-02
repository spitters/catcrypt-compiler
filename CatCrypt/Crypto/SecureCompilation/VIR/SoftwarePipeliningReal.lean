/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT

/-!
# A restructuring software-pipelining (loop-peel) pass for `Com` (real transform)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`SoftwarePipelining.lean` ships an *analysis-as-labelling* software pipeliner
whose `Com → Com` rewrite is the identity (`applySwp = fun p _ => p`), so its
preservation theorems are `rfl` and verify nothing about an actual loop
restructure. This file supplies what that one defers: a **structural**
loop-level transform that *restructures the loop* — peeling the first
iteration into a prologue and running a shortened steady-state loop — together
with a **non-`rfl`** denotation-preservation proof by the `List.foldl`
front-peel decomposition of the loop.

## Why software pipelining is a LOOP transform, not a `Com`-body transform

Software pipelining does **not** rewrite the straight-line loop body `update`.
The body is unchanged; what changes is the *iteration structure*: stages of
consecutive iterations overlap, and the loop grows a prologue (warm-up) and an
epilogue (cool-down) around a shortened steady-state kernel. The honest level
for this transform is therefore the **loop** (`JForProg` / the dialect-general
`loopDenote`), not the intrinsically-typed `Com` body. This mirrors
`LoopInvariantHoistReal.lean`, whose real transform also lives at the loop
level (it moves an invariant *out of* the loop) rather than at the `Com`-body
level.

## The transform: prologue peel = the degenerate 2-stage pipeline

The cleanest realizable software-pipeline restructure is the **prologue peel**:
the degenerate 2-stage modulo schedule where the first iteration is issued
on its own as the prologue and the remaining `n - 1` iterations run as the
steady state. Concretely, for `n = m + 1`:

```
acc := init; for _ in 0..(m+1) { acc := step(acc) }; ret acc          -- original
acc := step(init);                                  -- prologue (peeled iter 0)
for _ in 0..m { acc := step(acc) }; ret acc         -- shortened steady state
```

This is exactly the standard software-pipelining prologue/steady split with one
stage of overlap: the prologue runs the warm-up iteration, and the steady-state
loop runs one fewer time. It is a **real** restructure — the trip count drops
by one and a prologue iteration is emitted before the loop — not the identity.

The pass result is a `PipelinedLoop`: the precomputed prologue accumulator
(`prologueAcc`, the result of running the body once on `init`) plus the
shortened-loop body and steady trip count `m`. Its denotation runs the steady
loop from the prologue accumulator.

## The proof (not `rfl`)

The central lemma is

  `peelFirst_denote :
     (peelFirst (m+1) update init).denote = loopDenote (m+1) update init`

The two programs are structurally different (a prologue iteration emitted
before a shorter loop, vs. the full-length loop) and agree only by the
`List.foldl` front-peel law on `List.range (m+1)`:

  `(range (m+1)).foldl f init = (range m).foldl f (f init 0)`

(via `List.range_succ_eq_map` + `List.foldl_map`), where `f` ignores the index.
The proof is **not** `rfl`: it peels the first fold step off the loop and
re-associates the remaining `m` iterations as the steady state.

## CT preservation is honest, not `rfl`-vacuous

Loop peeling keeps the loop *body* `update` identical — the prologue runs the
same body once, the steady loop runs it `m` times. Since
`ctSafeJForProg p accL = ctSafeJasmin p.update (bodyLabelCtxt accL)` depends
**only on the body** (`JForProgCT.ctSafeJForProg_eq`), and the peel does not
touch the body, the steady-state `JForProg` is CT-safe iff the original is —
proved by `rfl` on the *body equality*, but stated about a different
(shorter) loop. The prologue is one straight-line execution of the same
CT-safe body, so it introduces no secret-dependent branch.

## What is general vs. scoped

* **General:** the loop model (`loopDenote`, shared with `LICMReal`), and the
  front-peel lemma (`loopDenote_peel`) are dialect-generic.
* **Scoped to the cleanest case:** `peelFirst` / `peelFirst_denote` peel a
  *single* leading iteration (the 1-stage-overlap prologue). Peeling `s`
  leading iterations (an `s`-stage prologue) iterates this lemma `s` times;
  the epilogue (cool-down) is the symmetric back-peel via `List.range_succ`
  + `List.foldl_append`. Both reuse the same `foldl` decomposition; the
  one-iteration peel carries the non-`rfl` proof cleanly.
-/

set_option autoImplicit false
-- Equation/lookup lemmas legitimately do not use every ambient typeclass
-- section variable; silence the section-variable linter rather than thread
-- per-theorem `omit` clauses.
set_option linter.unusedSectionVars false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SwpReal

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-! ## 1. The dialect-general bounded-loop denotation (mirrors `JForProg.denote`)

One iteration runs the body `update : Com d [accTy] accTy` on the singleton
valuation `[acc]`; the loop folds `n` iterations from `init`. This is the
ground-truth functional semantics that `JForProg.denote` (and `LICMReal`) also
use. -/

/-- One iteration: run the body on the singleton accumulator valuation. -/
def stepOf {accTy : d.Ty} (update : Com d [accTy] accTy) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  update.denote (.cons acc .nil)

/-- `n`-fold loop denotation: fold `step` `n` times from `init`. -/
def loopDenote {accTy : d.Ty} (n : Nat) (update : Com d [accTy] accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range n).foldl (fun acc _ => stepOf update acc) init

/-! ## 2. The front-peel lemma for the loop fold

Peeling the first iteration off an `(m+1)`-trip loop: run the body once, then
fold the remaining `m` iterations from the result. This is the `List.foldl`
front-peel on `List.range (m+1)`. -/

/-- **Loop front-peel (general).** An `(m+1)`-trip loop equals running the body
once and then an `m`-trip loop from the result. Proven by the `List.range`
front-peel (`range_succ_eq_map`) and `List.foldl_map` (the step ignores the
loop index). -/
theorem loopDenote_peel {accTy : d.Ty} (m : Nat)
    (update : Com d [accTy] accTy) (init : ⟦accTy⟧) :
    loopDenote (m + 1) update init = loopDenote m update (stepOf update init) := by
  unfold loopDenote
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

/-! ## 3. The pipelined program and the real transform

A `PipelinedLoop` carries the *precomputed prologue accumulator*
(`prologueAcc`, the body run once on the loop's initial value) and the steady
trip count plus body. Its denotation runs the steady-state loop from the
prologue accumulator — the first iteration has been peeled out as the
prologue. -/

/-- The pipelined program: a peeled-out prologue accumulator and the shortened
steady-state loop (`steadyN`-trip, same body). -/
structure PipelinedLoop (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    (accTy : d.Ty) where
  /-- Steady-state trip count (the original `n` minus the one peeled iteration). -/
  steadyN : Nat
  /-- The loop body (unchanged — software pipelining does not rewrite it). -/
  update : Com d [accTy] accTy
  /-- The prologue accumulator: the body run once on the loop's initial value.
      Materialised *before* the steady loop. -/
  prologueAcc : ⟦accTy⟧

/-- Pipelined-loop denotation: run the steady-state loop from the prologue
accumulator. The first iteration sits outside the loop — it lives in
`prologueAcc`. -/
def PipelinedLoop.denote {accTy : d.Ty} (p : PipelinedLoop d accTy) : ⟦accTy⟧ :=
  loopDenote p.steadyN p.update p.prologueAcc

/-- **The real software-pipelining transform (prologue peel).** Given a loop
with trip count `m + 1` and body `update`, peel the first iteration into the
prologue: precompute `stepOf update init` (the warm-up) and return a
`PipelinedLoop` whose steady-state loop runs `m` iterations of the same body
from that prologue accumulator.

This restructures the program — the trip count drops `m+1 ↝ m` and a
prologue iteration is emitted before the loop. It is **not** the identity: the
result is a different structure (`PipelinedLoop`) with a strictly shorter
steady-state loop. -/
def peelFirst {accTy : d.Ty} (m : Nat) (update : Com d [accTy] accTy)
    (init : ⟦accTy⟧) : PipelinedLoop d accTy where
  steadyN := m
  update := update
  prologueAcc := stepOf update init

/-! ## 4. Denotation preservation (NON-`rfl`)

The pipelined loop denotes exactly the original loop. The two programs are
structurally different (a prologue iteration before a shorter loop vs. the
full-length loop) and agree by the `List.foldl` front-peel. -/

/-- **Software-pipelining preservation (NON-`rfl`).** Peeling the first
iteration into the prologue and running the shortened steady-state loop
denotes the same function as the original `(m+1)`-trip loop.

The proof is not `rfl`: the original loop folds the body `m + 1`
times over `range (m+1)`, while the pipelined loop folds it `m` times from the
peeled prologue accumulator; equating them is the `List.foldl` front-peel
(`loopDenote_peel`). -/
theorem peelFirst_denote {accTy : d.Ty} (m : Nat)
    (update : Com d [accTy] accTy) (init : ⟦accTy⟧) :
    (peelFirst m update init).denote = loopDenote (m + 1) update init := by
  unfold PipelinedLoop.denote peelFirst
  rw [loopDenote_peel]

/-! ## 5. CT preservation (honest: the body is untouched)

Loop peeling keeps the loop *body* identical, so the steady-state loop is
CT-safe iff the original is. We state this over `JForProg` (the concrete loop
type carrying the CT predicate). The pipelined steady-state loop is the
`JForProg` `{ n := m, update := p.update }`, whose body is `p.update`, the same
body as the original — so `ctSafeJForProg` (which depends only on the body)
agrees. The prologue is one straight-line run of that same CT-safe body and
adds no branch. -/

/-- The steady-state `JForProg` of a prologue peel: trip count `m`, **same**
body as the original. -/
def steadyJForProg {accTy : JasminTy} (m : Nat)
    (p : JForProg accTy) : JForProg accTy :=
  { n := m, update := p.update }

/-- **CT preservation for the prologue peel (honest).** The steady-state loop
of a prologue peel is CT-safe iff the original loop is. This holds because the
peel does not touch the loop body, and `ctSafeJForProg` depends only on the
body (`ctSafeJForProg_eq`). It is not `rfl`-vacuous: it is stated about a
different (shorter) loop, and reduces to the body equality. -/
theorem steady_preserves_CT {accTy : JasminTy} (m : Nat)
    (p : JForProg accTy) (accL : SecretLevel) :
    ctSafeJForProg (steadyJForProg m p) accL = ctSafeJForProg p accL := by
  simp only [ctSafeJForProg_eq, steadyJForProg]

/-- **Robust CT preservation for the prologue peel.** A robustly CT-safe loop
stays robustly CT-safe after the peel — the steady-state loop has the same
body. -/
theorem steady_preserves_RobustlyCTSafe {accTy : JasminTy} (m : Nat)
    (p : JForProg accTy) (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg (steadyJForProg m p) := by
  intro accL
  rw [steady_preserves_CT]
  exact h accL

/-- **End-to-end: the prologue peel preserves the `JForProg` denotation.** For
`n = m + 1`, running the body once (prologue) then the `m`-trip steady-state
loop denotes the same accumulator as the original `JForProg`. This ties the
dialect-general lemma to the concrete `JForProg.denote`. -/
theorem peel_preserves_JForProg_denote {accTy : JasminTy} (m : Nat)
    (p : JForProg accTy) (hn : p.n = m + 1) (init : ⟦accTy⟧) :
    (steadyJForProg m p).denote (p.step init) = p.denote init := by
  -- `JForProg.denote` is a `foldl` over `range _.n`; the steady loop's count is
  -- `m`, the original's is `m + 1`. Peel the first iteration (`p.step init`)
  -- off the original's `range (m+1)` fold — the non-`rfl` content.
  unfold JForProg.denote JForProg.step steadyJForProg
  rw [hn, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

/-! ## 6. A concrete worked example (the first iteration really leaves the loop)

A self-contained one-type, two-op toy dialect over `Nat`, on which we exhibit a
loop, run `peelFirst`, and confirm the prologue accumulator is the first
iteration's result while the steady-state loop runs one fewer time — and the
two denote the same value. -/

namespace Demo

/-- A toy dialect: a single value type and an `incr` op (unary, adds 1). -/
inductive ToyOp where
  | incr
  deriving DecidableEq

def toyDialect : Dialect where
  Op := ToyOp
  Ty := Unit

instance : TyDenote toyDialect.Ty where
  denote _ := Nat

instance : DialectSignature toyDialect where
  sig | .incr => [()]
  ret _ := ()

instance : DialectDenote toyDialect where
  denote
    | .incr, .cons (a : Nat) .nil => a + 1

/-- A loop body that increments the accumulator by 1 each iteration:
`acc' = incr acc; ret acc'`. `update : Com toy [()] ()`. -/
def incrBody : Com toyDialect [()] () :=
  .var { op := .incr, retTy_eq := rfl, args := .cons .here .nil }
    (.ret .here)

/-- One iteration adds 1 to the accumulator. -/
example (acc : Nat) : stepOf incrBody acc = acc + 1 := rfl

/-- **The transform peels the first iteration.** The prologue
accumulator (from `init = 0`) is `1` — the first iteration's result now lives
*outside* the loop. -/
example : (peelFirst 4 incrBody (0 : Nat)).prologueAcc = (1 : Nat) := rfl

/-- The steady-state loop runs **one fewer** iteration: trip count `4`, not the
original `5`. -/
example : (peelFirst 4 incrBody (0 : Nat)).steadyN = 4 := rfl

/-- **Denotation preservation on this concrete loop (5 iterations from 0):** the
pipelined loop (prologue + 4-trip steady state) and the original 5-trip loop
agree. Both yield `0 + 5 = 5`. -/
example :
    (peelFirst 4 incrBody (0 : Nat)).denote = loopDenote 5 incrBody (0 : Nat) :=
  peelFirst_denote 4 incrBody (0 : Nat)

-- `#eval`: both loops denote `5` (= 5 increments) from `init = 0`.
#eval (peelFirst 4 incrBody (0 : Nat)).denote          -- 5
#eval loopDenote 5 incrBody (0 : Nat)                  -- 5
-- The prologue accumulator is the first iteration's result, `1`.
#eval (peelFirst 4 incrBody (0 : Nat)).prologueAcc     -- 1

end Demo

end CatCrypt.Crypto.SecureCompilation.VIR.SwpReal
