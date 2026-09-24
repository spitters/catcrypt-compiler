/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.MayoSolveCovered
public import CatCrypt.Crypto.SecureCompilation.VIR.MayoSolveCovered
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote

/-!
# MAYO-1 echelon phase with its data-dependent inner sweep OPENED as an `RWhileNz`

`MayoSolveCovered` descends the MAYO-1 GF(16) solve's top-level control — the four
static-count phases sequenced (`copy ; lastcol ; echelon ; backsub`) — but keeps
each phase's *inner* sweep **inside an opaque per-step leaf** (`mayo_solve_ef_step`
etc.), because those inner sweeps have runtime-computed trip counts (`RWhileNz`)
that the static-count `RFor`+`RSeq` covered fragment there does not express.

This module opens that leaf for the echelon phase, using that `IsCoveredSU`
closes `RFor` (`rFor`) over an ANY-`IsCoveredSU` body — including a body that is
itself a data-dependent `RWhileNz` sweep. The echelon phase is re-sourced as

```
RFor "pcol" AC (                     -- outer: static pivot-column pass (AC = 81)
  RScalarSet "row" m ;               --   reset the public row counter (m = 78)
  RWhileNz "row" (                   --   inner: data-dependent row sweep (down to 0)
    mayo_solve_ef_cell_step(A,P,P2)  --     GF(16) cell arithmetic — OPAQUE leaf
    row := row - 1))                 --     advance the public row counter
```

The **outer** `RFor` (static count) and the **inner** `RWhileNz` (data-dependent
count) are BOTH fully descended by the unified engine — the outer via the
env-threaded counted fold `loopRForDEnv`, the inner via the guard-driven do-while
`semScalarWhile`. Only the GF(16) cell arithmetic
(`mayo_solve_ef_cell_step`) stays an opaque `RCall` leaf, exactly as Keccak-f's
permutation stays opaque inside `keccakf1600`.

## Constant-time: the inner-sweep count is PUBLIC

Per `MayoSolveCovered`'s note, the inner sweep's trip count is *data-dependent but
public* — the row counter `row` is a public loop bound; the secret pivot row never
indexes or bounds anything, only feeds constant-time comparison masks (inside the
opaque cell step). So the `RWhileNz "row"` guard `guardNz "row"` reads a public
word: the descent is constant-time. The `row := row - 1` countdown is exactly the
`srcClean` `SSub` fragment the front covers (as in the DuplexChallenger absorb
loop).

## Contents

* `echelonLoopOpened` — the echelon phase with its inner sweep opened as an
  `RWhileNz` (not an opaque leaf).
* `echelonOpened_coveredU : IsCoveredSU echelonLoopOpened` — the structural
  coverage: `rFor` over an `RSeq` of a straight-line reset and an `rWhile` sweep.
  Unreachable from `MayoSolveCovered`'s `IsCoveredSCtlSeq`/`IsCoveredSCtl` (whose
  `RFor` body is straight-line only).
* `echelonOpenedCovered_denote` — **the deliverable**: the whole-program machine
  denote of the opened echelon phase, a direct instantiation of `transU_denote`.
  The control (outer `RFor` + inner `RWhileNz`) is fully descended; the GF(16) cell
  work is the separate opaque-leaf byte-KAT obligation.
* `echelonOpenedSmall_semU_terminates` / `echelonOpenedSmall_transU_isSome` —
  non-vacuity on a concrete small instance: the waist `semU` TERMINATES (the inner
  sweep counts a public `row` down to zero each pass) and the front `transU`
  SUCCEEDS, so the denote's `semU … = some env'` premise is satisfiable.

**0 sorries; no axioms beyond the front's existing set.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MayoSolveLeafOpenCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.VIR.MayoSolveCovered (bundleTy loc pM pAC)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located SExpr)

/-! ## 1. The opened echelon phase -/

/-- One echelon *cell* step for the current `(pcol, row)`: the constant-time GF(16)
    cell arithmetic (pivot search / invert / conditional write-back / eliminate),
    an OPAQUE `RCall` threading `A`. The secret pivot only feeds CT masks inside
    this leaf — it never bounds the sweep. -/
def efCellStep : LowCT :=
  .RCall "mayo_solve_ef_cell_step" (loc "A") [loc "A", loc "P", loc "P2"]

/-- The inner row-sweep counter decrement `row := row -ₛ 1` (saturating `SSub`).
    `srcClean` (so `IsCoveredS`); it drives the `guardNz "row"` do-while to
    terminate in `row` trips — a PUBLIC count. -/
def decRow : SExpr := .SSub (.SVar "row") (.SLit 1)

/-- One inner sweep iteration: the opaque GF(16) cell step, then advance the public
    row counter. Straight-line (`IsCoveredS`) — an `RSeq` of an opaque `RCall` and
    the `srcClean` countdown. -/
def efInnerSweepBody : LowCT :=
  .RSeq efCellStep (.RScalarSetExpr "row" decRow)

/-- **The inner sweep OPENED** — a data-dependent `RWhileNz` over the
    public row counter, not an opaque leaf. -/
def efInnerSweep : LowCT :=
  .RWhileNz "row" efInnerSweepBody

/-- One echelon phase body for pivot column `pcol`: reset the public row counter to
    `m`, then run the data-dependent inner sweep. -/
def echelonPhaseBody : LowCT :=
  .RSeq (.RScalarSet "row" pM) efInnerSweep

/-- **The echelon phase with its inner sweep opened.** The outer static-count pass
    over the pivot columns (`0..AC`) is an `RFor`; its body is an
    `RWhileNz`-containing phase, not an opaque leaf. -/
def echelonLoopOpened : LowCT :=
  .RFor "pcol" pAC echelonPhaseBody

/-! ## 2. Coverage — `IsCoveredSU`, reaching into the opened inner sweep -/

/-- The opaque cell step is straight-line covered. -/
theorem efCellStep_coveredS : IsCoveredS efCellStep :=
  .rCall "mayo_solve_ef_cell_step" (loc "A") [loc "A", loc "P", loc "P2"]

/-- `"row"` (length 3) is not a `__sx` fresh temp, so `SVar "row"` is `srcClean`. -/
theorem not_isTmp_row : ¬ isTmpName "row" := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [tmpName, String.length_append] at hlen
  have h2 : "__sx".length = 4 := rfl
  have h3 : "row".length = 3 := rfl
  omega

/-- The row countdown is in the covered `SExpr` fragment. -/
theorem decRow_srcClean : srcClean decRow :=
  ⟨not_isTmp_row, by simp only [srcClean]; norm_num⟩

/-- The inner sweep body is straight-line covered (opaque cell step `;` countdown). -/
theorem efInnerSweepBody_coveredS : IsCoveredS efInnerSweepBody :=
  .rSeq efCellStep_coveredS (.rScalarSetExpr "row" decRow decRow_srcClean)

/-- **The echelon phase body is unified-covered** (`IsCoveredSU`): the reset is an
    `ofCtl` straight-line leaf, the sweep is an `rWhile` over the covered inner
    body — sequenced by `rSeq`. This body is NOT `IsCoveredSCtl` (it contains an
    `RWhileNz`), so the phase is unreachable from `MayoSolveCovered`'s
    `IsCoveredSCtl`-`RFor` — it needs the `rFor`-over-`IsCoveredSU` closure. -/
theorem echelonPhaseBody_coveredU : IsCoveredSU echelonPhaseBody :=
  .rSeq (.ofCtl (.ofStraight (.rScalarSet "row" pM)) rfl)
    (.rWhile (.rSeq (.ofCtl (.ofStraight efCellStep_coveredS) rfl)
      (.ofCtl (.ofStraight (.rScalarSetExpr "row" decRow decRow_srcClean)) rfl)))

/-- **The opened echelon phase is unified-covered.** The `rFor` closure descends the
    static outer pass, and its body — the `RWhileNz`-containing phase — descends
    through the unified engine per trip. -/
theorem echelonOpened_coveredU : IsCoveredSU echelonLoopOpened :=
  .rFor echelonPhaseBody_coveredU

/-! ## 3. THE DELIVERABLE — the whole-program denote of the opened echelon phase -/

/-- **Whole-program machine denote of the opened MAYO-1 echelon phase.** For any
    context/valuation/env consistent triple on which the unified front descent
    `transU` fires and the unified waist `semU` terminates (the outer static pass
    unrolls, each inner sweep counts its public `row` down to zero within `fuel`),
    the descended dialect-`Com` prefix denotes exactly the phase's `semU`
    semantics. A direct instantiation of `transU_denote` at
    `echelonOpened_coveredU`: the outer `RFor` descends via the env-threaded
    counted fold `loopRForDEnv`, the inner `RWhileNz` via the guard-driven do-while
    — the CONTROL is fully descended. The GF(16) cell arithmetic
    (`mayo_solve_ef_cell_step`) is the opaque leaf whose correctness is the
    separate byte-KAT obligation. -/
theorem echelonOpenedCovered_denote (fuel : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env env' : SEnvScalar)
    (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : transU fuel vm env echelonLoopOpened = some o)
    (hsem : semU fuel echelonLoopOpened env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  transU_denote fuel echelonOpened_coveredU vm V env env' o hc htr hsem

/-! ## 4. Non-vacuity — a concrete small instance terminates and descends

The inner sweep's trip count is a PUBLIC `row` count, so a concrete run halts. A
small instance (`3` pivot columns, each resetting `row := 2`) is used so the
`native_decide` term stays small — the shape is identical to the `AC = 81`,
`m = 78` phase, only the counts differ. -/

/-- Small-instance echelon phase body: reset `row := 2`, then the opened sweep. -/
def echelonPhaseBodySmall : LowCT :=
  .RSeq (.RScalarSet "row" 2) efInnerSweep

/-- Small-instance opened echelon phase: `3` pivot columns. -/
def echelonLoopOpenedSmall : LowCT :=
  .RFor "pcol" 3 echelonPhaseBodySmall

/-- Concrete entry env with the public row counter bound (reset each pass). -/
def efEnv0 : SEnvScalar :=
  SEnvScalar.upd (fun _ => none) "row" (t := .sword 64) (0 : BitVec 64)

/-- Three-argument context for the opaque cell step's bundles `A`, `P`, `P2`. -/
def efArgCtx : Ctx :=
  [encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy]

/-- Name resolver binding `A`/`P`/`P2` to the three bundle arguments. -/
def efArgVM : VarMap efArgCtx where
  lookup := fun s =>
    if s = "A" then some ⟨encodeTy bundleTy, .here⟩
    else if s = "P" then some ⟨encodeTy bundleTy, .there .here⟩
    else if s = "P2" then some ⟨encodeTy bundleTy, .there (.there .here)⟩
    else none

/-- **Non-vacuity (semantics).** The unified waist TERMINATES on the concrete
    instance: each of the `3` outer passes resets `row := 2` and the inner sweep
    counts it down to `0` within `fuel = 20`. So the denote's `semU … = some env'`
    premise is satisfiable — the opened phase has a terminating run, not a vacuous
    hypothesis. -/
theorem echelonOpenedSmall_semU_terminates :
    (semU 20 echelonLoopOpenedSmall efEnv0).isSome = true := by native_decide

/-- **Non-vacuity (front).** The unified front descent SUCCEEDS on the concrete
    instance: the outer `RFor` env-threads its `3` passes, each inner `RWhileNz`
    unrolls to its `2`-trip public count, and every leaf (the opaque cell call, the
    reset, the countdown) front-compiles. -/
theorem echelonOpenedSmall_transU_isSome :
    (transU 20 efArgVM efEnv0 echelonLoopOpenedSmall).isSome = true := by native_decide

/-! ## 5. Axiom audit -/

#print axioms echelonOpened_coveredU
#print axioms echelonOpenedCovered_denote
#print axioms echelonOpenedSmall_semU_terminates
#print axioms echelonOpenedSmall_transU_isSome

end CatCrypt.Crypto.SecureCompilation.VIR.MayoSolveLeafOpenCovered
