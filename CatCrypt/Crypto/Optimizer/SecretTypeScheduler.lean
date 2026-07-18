/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.SchedulerPass
import CatCrypt.Crypto.Optimizer.SecretType

/-!
# A third pass for the compositional-CT taint story: the ILP scheduler (#594)

`Optimizer/SecretType.lean` seeds *constant-time as a compositional typing
invariant*: a secret/public taint qualifier flows along the A-normal-form
let-chain of the typed `Com jasminDialect` substrate, and two structurally
different optimizer passes are shown to keep it well-formed —

* the local **peephole** rewrite *preserves* the per-binder taint exactly
  (`peepCom_wellTainted`), because it rewrites `binE bop a b ↦ binE bop' a b`
  over the *same* argument variables, and
* the bounded equality-saturation **egraph** engine *declassifies
  monotonically* (`saturateCom_comMaxTaint_le`), because its algebraic
  collapses only ever *drop* an input variable.

This file adds a **third, structurally-different pass**: the #525/#593
intra-block instruction **scheduler** (`Optimizer/SchedulerPass.lean`,
`scheduleBlock`). The scheduler is unlike both predecessors: it neither
rewrites an op (peephole) nor drops an argument (egraph). It only ever
performs **adjacent transpositions of two independent statements** — a pure
*reorder*. So it should preserve the taint summary not just monotonically but
**exactly** — the strongest of the three invariants.

## The representation gap and how we bridge it

`scheduleBlock` operates on a different substrate from `SecretType`'s
`Com jasminDialect`: it works on the `LowCT` block representation
`List BBStmt` (`RScalarSetExpr` / `RCall`), with a big-step `RustExec`
semantics and a `cmdCT`-based CT classification. `WellTainted` / `comMaxTaint`
live on `Com jasminDialect` with a De-Bruijn `Taint Γ`. The two do not share a
type.

We therefore define the taint summary **at the representation `scheduleBlock`
actually uses** — a named-variable taint environment `BBTaint := String →
SecretLevel` over `List BBStmt`, reusing `SecretType`'s `SecretLevel` lattice —
and prove the *exact* preservation there. Each statement's output taint is the
join of its read-variable taints (`stmtTaint`); a statement *updates* the
environment at its `writeVar` to that level (`stepTaint`), exactly mirroring how
`Com`'s let-chain threads `Taint Γ` by `exprTaint`. The block-level summary
`blockMaxTaint` is the running join of every statement's output taint down the
threaded environment — the `List BBStmt` analogue of `comMaxTaint`.

## What we prove

`scheduleBlock_blockMaxTaint_eq` : `blockMaxTaint T (scheduleBlock b) =
blockMaxTaint T b`. Because every reorder move is an adjacent independent swap,
and an `indep`-gated swap leaves the threaded environment and each statement's
read-taint **unchanged** (`stepTaint_comm`, the taint-level analogue of
`SchedulerPass`'s `bbSwap_exec_iff` state-commutation kernel), the running join
is invariant under the whole schedule. This is *exact* preservation — stronger
than the egraph's `⊑ₛ`-monotone declassification — as befits a pure reorder.

The kernel `stepTaint_comm` reuses `SchedulerPass`'s own dependence lemma
`indep_iff` (the three hazard-free conjuncts), so the taint invariant is gated
by *exactly* the independence predicate the scheduler certifies each swap with.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SecretTypeScheduler

open CatCrypt.Crypto.Optimizer.SchedulerPass
open CatCrypt.Crypto.Optimizer.SecretType

/-! ## 1. A named-variable taint environment over `List BBStmt`

`scheduleBlock`'s statements are over string-named variables (`BBStmt.writeVar :
String`, `BBStmt.readVars : List String`), not De Bruijn indices, so the taint
assignment is a total function `String → SecretLevel`. This is the `LowCT`
analogue of `SecretType.Taint Γ`. -/

/-- A taint assignment over named variables. -/
abbrev BBTaint := String → SecretLevel

/-- The taint of a statement's output: the join of its read variables' taints,
folded from `pub` (the join identity). The `LowCT` analogue of `exprTaint`. -/
def stmtTaint (T : BBTaint) (s : BBStmt) : SecretLevel :=
  s.readVars.foldr (fun x acc => T x ⊔ₛ acc) .pub

/-- Threading a statement through the environment: bind its `writeVar` to its
output taint. The `LowCT` analogue of `Taint.cons (exprTaint …)`. -/
def stepTaint (T : BBTaint) (s : BBStmt) : BBTaint :=
  fun y => if y = s.writeVar then stmtTaint T s else T y

/-- The overall secrecy level of a block: the running join of every statement's
output taint down the threaded environment. The `List BBStmt` analogue of
`comMaxTaint`. -/
def blockMaxTaint (T : BBTaint) : List BBStmt → SecretLevel
  | []      => .pub
  | s :: ss => stmtTaint T s ⊔ₛ blockMaxTaint (stepTaint T s) ss

/-! ## 2. `stmtTaint` depends only on the read variables

The taint of a statement's output is a function of the environment **only at
its read variables** — the data-flow analogue of `SExpr.eval_eq_of_agree`. Two
environments agreeing on `s.readVars` give the same `stmtTaint`. -/

/-- `stmtTaint` depends only on the environment at the statement's read
variables. -/
theorem stmtTaint_eq_of_agree (T1 T2 : BBTaint) (s : BBStmt)
    (h : ∀ y ∈ s.readVars, T1 y = T2 y) :
    stmtTaint T1 s = stmtTaint T2 s := by
  unfold stmtTaint
  suffices hgen : ∀ (l : List String), (∀ y ∈ l, T1 y = T2 y) →
      l.foldr (fun x acc => T1 x ⊔ₛ acc) .pub
    = l.foldr (fun x acc => T2 x ⊔ₛ acc) .pub from hgen s.readVars h
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hl
    simp only [List.foldr_cons]
    rw [hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]

/-- A write to a variable disjoint from `s`'s reads leaves `stmtTaint` unchanged
(WAR/RAW frame). -/
theorem stmtTaint_stepTaint_other (T : BBTaint) (s s' : BBStmt)
    (h : s'.writeVar ∉ s.readVars) :
    stmtTaint (stepTaint T s') s = stmtTaint T s := by
  apply stmtTaint_eq_of_agree
  intro y hy
  unfold stepTaint
  have : y ≠ s'.writeVar := fun hc => h (hc ▸ hy)
  simp [this]

/-! ## 3. The swap kernel: independent statements commute the threaded taint

The taint-level analogue of `SchedulerPass`'s state-commutation kernel
(`locatedUpdate_comm` / `rsSetScalar_comm` assembled into `bbSwap_exec_iff`).
For two `indep` statements, threading the environment through them in either
order yields the **same** environment, and each statement's read-taint is
unaffected by the other's write. We unpack independence with `SchedulerPass`'s
own `indep_iff`, so the taint invariant is gated by exactly the predicate the
scheduler certifies each swap with. -/

/-- **Threaded-taint commutation.** Two independent statements update the taint
environment to the *same* result in either order: distinct write targets (WAW)
commute, and neither reads what the other writes (WAR/RAW), so each statement's
output taint is computed from the same inputs regardless of order. -/
theorem stepTaint_comm (T : BBTaint) (s1 s2 : BBStmt) (h : indep s1 s2 = true) :
    stepTaint (stepTaint T s1) s2 = stepTaint (stepTaint T s2) s1 := by
  obtain ⟨hWAW, hRead2, hRead1⟩ := (indep_iff s1 s2).mp h
  -- s2's reads avoid s1's write, s1's reads avoid s2's write
  have h2 : s1.writeVar ∉ s2.readVars := fun hc => (hRead2 _ hc) rfl
  have h1 : s2.writeVar ∉ s1.readVars := fun hc => (hRead1 _ hc) rfl
  have e2 : stmtTaint (stepTaint T s1) s2 = stmtTaint T s2 :=
    stmtTaint_stepTaint_other T s2 s1 h2
  have e1 : stmtTaint (stepTaint T s2) s1 = stmtTaint T s1 :=
    stmtTaint_stepTaint_other T s1 s2 h1
  funext y
  -- Unfold only the outer `stepTaint` application, leaving the inner
  -- `stmtTaint (stepTaint …) …` subterms intact so `e1`/`e2` can rewrite them
  -- before any further unfolding collapses the `stepTaint` they mention.
  simp only [stepTaint]
  rw [e1, e2]
  by_cases hy2 : y = s2.writeVar <;> by_cases hy1 : y = s1.writeVar <;>
    simp_all

/-! ## 4. Swapping the first two statements preserves `blockMaxTaint`

With the kernel in hand, swapping an independent adjacent pair leaves the
running join invariant: the two output taints commute (`SecretLevel.join_comm`/
`join_assoc`), each is unchanged by the other's write (`e1`/`e2`), and the tail
is threaded through the identical environment (`stepTaint_comm`). -/

/-- Swapping the first two (independent) statements preserves the block taint
summary. The `blockMaxTaint` analogue of `block_swap_head`. -/
theorem blockMaxTaint_swap_head (T : BBTaint) (s1 s2 : BBStmt)
    (post : List BBStmt) (h : indep s1 s2 = true) :
    blockMaxTaint T (s1 :: s2 :: post) = blockMaxTaint T (s2 :: s1 :: post) := by
  obtain ⟨_, hRead2, hRead1⟩ := (indep_iff s1 s2).mp h
  have h2 : s1.writeVar ∉ s2.readVars := fun hc => (hRead2 _ hc) rfl
  have h1 : s2.writeVar ∉ s1.readVars := fun hc => (hRead1 _ hc) rfl
  have e2 : stmtTaint (stepTaint T s1) s2 = stmtTaint T s2 :=
    stmtTaint_stepTaint_other T s2 s1 h2
  have e1 : stmtTaint (stepTaint T s2) s1 = stmtTaint T s1 :=
    stmtTaint_stepTaint_other T s1 s2 h1
  simp only [blockMaxTaint]
  rw [e2, e1, stepTaint_comm T s1 s2 h]
  rw [← SecretLevel.join_assoc, ← SecretLevel.join_assoc,
    SecretLevel.join_comm (stmtTaint T s1) (stmtTaint T s2)]

/-! ## 5. One bubble pass preserves `blockMaxTaint`

`bubble` performs only `indep`-gated adjacent swaps, so it preserves the block
taint summary. Structural induction on the same `bubble.induct` principle
`SchedulerPass` uses for `bubble_exec_iff` / `bubble_cmdCT_eq`. -/

/-- **One bubble pass preserves the block taint summary.** -/
theorem bubble_blockMaxTaint_eq :
    ∀ (T : BBTaint) (b : List BBStmt),
      blockMaxTaint T (bubble b) = blockMaxTaint T b := by
  intro T b
  induction b using bubble.induct generalizing T with
  | case1 => simp only [bubble]
  | case2 s => simp only [bubble]
  | case3 s1 s2 rest hcond ih =>
    have hindep : indep s1 s2 = true := by
      have := hcond; simp only [Bool.and_eq_true] at this; exact this.1
    simp only [bubble, if_pos hcond]
    -- bubble (s1::s2::rest) = s2 :: bubble (s1::rest)
    show blockMaxTaint T (s2 :: bubble (s1 :: rest)) = _
    rw [show blockMaxTaint T (s2 :: bubble (s1 :: rest))
          = stmtTaint T s2 ⊔ₛ blockMaxTaint (stepTaint T s2) (bubble (s1 :: rest))
        from rfl, ih (stepTaint T s2)]
    -- now: stmtTaint T s2 ⊔ blockMaxTaint (stepTaint T s2) (s1::rest)
    --    = blockMaxTaint T (s1::s2::rest)
    have hswap := blockMaxTaint_swap_head T s1 s2 rest hindep
    simp only [blockMaxTaint] at hswap ⊢
    exact hswap.symm
  | case4 s1 s2 rest hcond ih =>
    simp only [bubble, if_neg hcond]
    -- bubble (s1::s2::rest) = s1 :: bubble (s2::rest)
    show blockMaxTaint T (s1 :: bubble (s2 :: rest)) = _
    simp only [blockMaxTaint]
    -- `ih` rewrites the recursive `bubble (s2 :: rest)` away; the resulting
    -- `blockMaxTaint (stepTaint T s1) (s2 :: rest)` then needs one cons-unfold
    -- to meet the already-expanded right-hand side.
    rw [ih (stepTaint T s1)]
    simp only [blockMaxTaint]

/-! ## 6. The headline: scheduling preserves the block taint summary *exactly*

`scheduleBlock = bubbleN length`, so iterating the bubble-pass invariance over
the fuel bound gives exact preservation. This is the third pass in the
compositional-CT story, and the strongest invariant of the three: the
peephole *preserves* per-binder taint, the egraph *declassifies monotonically*,
and the scheduler — a pure reorder — preserves the block taint summary *exactly*
(an equality, not an `⊑ₛ`). -/

/-- Iterating `bubble` preserves the block taint summary. -/
theorem bubbleN_blockMaxTaint_eq :
    ∀ (k : Nat) (T : BBTaint) (b : List BBStmt),
      blockMaxTaint T (bubbleN k b) = blockMaxTaint T b := by
  intro k
  induction k with
  | zero => intro T b; rfl
  | succ k ih =>
    intro T b
    simp only [bubbleN]
    rw [ih T (bubble b), bubble_blockMaxTaint_eq T b]

/-- **The scheduler preserves the block taint summary exactly.** For any taint
assignment `T`, `blockMaxTaint T (scheduleBlock b) = blockMaxTaint T b`. Every
reorder move is an adjacent independent swap, which leaves the threaded taint
environment and each statement's read-taint unchanged (`stepTaint_comm`), so the
running join — the program's overall secrecy level — is invariant. The third,
*reorder*, pass of the #594 compositional-CT story, and the only one that
preserves the summary *exactly*. -/
theorem scheduleBlock_blockMaxTaint_eq (T : BBTaint) (b : List BBStmt) :
    blockMaxTaint T (scheduleBlock b) = blockMaxTaint T b := by
  unfold scheduleBlock
  exact bubbleN_blockMaxTaint_eq b.length T b

/-! ## 7. Self-contained validation

A two-statement block over named variables: `y := a * b` then `z := c + d`,
read-sets `{a,b}` and `{c,d}`, write-sets `y` and `z` — fully independent, so
the scheduler may freely reorder them. With `a` marked `sec` (and everything
else `pub`), the first binder is `sec`, the second `pub`; the overall block
taint is `sec`, and is preserved under scheduling (no swap or any swap). -/

/-- Demo block: two independent statements `y := a * b`, `z := c + d`. -/
def demoBlock : List BBStmt :=
  [ .sset "y" (.SMul (.SVar "a") (.SVar "b")),
    .sset "z" (.SAdd (.SVar "c") (.SVar "d")) ]

/-- Taint assignment marking `a` secret, everything else public. -/
def demoBBTaint : BBTaint := fun x => if x = "a" then .sec else .pub

/-- The demo block's overall secrecy level is `sec` (the `y := a * b` binder
joins the secret `a`). -/
example : blockMaxTaint demoBBTaint demoBlock = .sec := by
  decide

/-- **Scheduling preserves the demo block's taint summary exactly.** Via
`scheduleBlock_blockMaxTaint_eq`. -/
example :
    blockMaxTaint demoBBTaint (scheduleBlock demoBlock)
      = blockMaxTaint demoBBTaint demoBlock :=
  scheduleBlock_blockMaxTaint_eq demoBBTaint demoBlock

/-- The two statements are independent, so swapping them is a legal scheduler
move that the taint kernel certifies neutral. -/
example :
    blockMaxTaint demoBBTaint
        [ .sset "z" (.SAdd (.SVar "c") (.SVar "d")),
          .sset "y" (.SMul (.SVar "a") (.SVar "b")) ]
      = blockMaxTaint demoBBTaint demoBlock :=
  (blockMaxTaint_swap_head demoBBTaint _ _ [] (by decide)).symm

end CatCrypt.Crypto.Optimizer.SecretTypeScheduler
