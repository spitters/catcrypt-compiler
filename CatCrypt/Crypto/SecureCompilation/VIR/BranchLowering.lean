/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MultiPhaseBody

/-!
# A verified two-way branch over the emit `Phase` substrate: run = `ite` of arms

Every other control-flow lowering above the straight-line backend assumes a
**counted** or **straight-line** body: `LoopLowering.loopN` (counted loop =
`step^[n]`), `WholeFnLowering` (whole straight-line function), `MultiPhaseBody`
(a *fixed* left-to-right **sequence** of phases). The one structural shape none
of them provide is a **two-way branch**: a public condition selecting *which* of
two sub-bodies runs. `MultiPhaseBody`'s own scope note names this as the missing
piece — its phase list is fixed, "not chosen by a runtime predicate — that is
the `if`/branch layer".

This file is that layer, built — like `MultiPhaseBody` — at the **emit `Phase`**
level: a branch is a `MultiPhaseBody.Phase accTy` whose emitted `run` and
reference `sem` are the `if-then-else` of the two arms' `run`/`sem`, selected by
a **public** condition `cond : Bool`. Its soundness `run = sem` is proved by
case-splitting on `cond` and reusing **each arm's own** `sound` field — no new
proof obligation beyond the two arms' (the same `LeafAgrees` / `StraightLine`
edges carried throughout the emit theory).

## What this module adds

* `branchPhase cond thenPhase elsePhase` — a `Phase` whose `run`/`sem` are
  `if cond then thenPhase.{run,sem} else elsePhase.{run,sem}`. This is the
  branch **construct** + its **lowering** (as an emit-run self-map of the
  accumulator), in the same shape `MultiPhaseBody` lowers a sequence.
* `branchPhase_run_eq` — the **denote-correctness**: the emitted branch run
  equals the `ite` of the two branch *semantics*, selected by the public
  condition. This is the `if-then-else` of the two arms' denotations — the
  branch analogue of `loopN_lower_denote_iterate` (loop = `step^[n]`) and
  `phasesRun_eq` (sequence = left-fold). Discharged by `cases cond` + each arm's
  `sound`.
* `branchPhase_run_true` / `branchPhase_run_false` — the two taken-branch
  corollaries: when the public condition is `true` the run is the `then` arm's
  semantics; when `false`, the `else` arm's.
* A `branchPhase` interoperates with `MultiPhaseBody`: it **is** a `Phase`, so it
  drops into a `phasesRun` list as one element — a branch *inside* a sequence
  (`setup; if c then … else …; finalize`) is sound by `phasesRun_eq` for free.

## Public condition ⇒ CT preserved (honest framing)

The condition `cond : Bool` here is a **public** bit (a loop bound, a message
length, a protocol version, a Fiat-Shamir-public flag) — the case where
divergent control flow is fine because the branch *taken* is not secret. This is
the real-branch case, **distinct from** the branchless secret-select
(`SelectIdiom.selectW_eq_maskBlend` / the `BranchlessSelectGoldenPath`), where a
*secret*-dependent choice is compiled to a data-flow `CMOV`/mask-blend with no
control divergence. Because the condition is public, a two-way control-flow
branch on it preserves constant-time: the leakage (which arm runs) is a function
of public data only. We make this a *typing* discipline by taking `cond` as a
plain `Bool` parameter (a value the surrounding straight-line code computes from
public inputs), not a predicate of secret accumulator state. (Contrast
`DataDependentControlFlow.scfIf`, which branches on a *predicate of the state*
`σ → Bool` — that is the data- or transcript-dependent dispatch; here the bit
is supplied as a public parameter.)

## Honest gap: this is the `Phase`-level `ite` model, not a fused-CFG `Cif`

The branch is composed at the **meta / semantic (`Phase`) level**: `run` is
literally `if cond then thenPhase.run else elsePhase.run`, exactly as
`MultiPhaseBody.phasesRun` composes phase runs by `List.foldl` over a shared
accumulator value, and as `WholeProtocolBody` composes setup and loop. It is
**not** a single fused control-flow graph emitted as one Jasmin `Cif`
instruction (`JasminAST.InstrR.Cif`) with a real conditional-jump and a merge
block. The Jasmin AST *has* a `Cif` constructor (and a printer / CT analysis for
it), but the verified-emit *denotation* theory (`JForProgSemCorrect` covers only
`Cfor`; the typed `Com jasminDialect` emit framework is straight-line) has **no**
`Cif` `denote = ite` theorem tied to the `runProg`/`bodyStepRun` evaluator.
Proving that fused `Cif` lowering — the evaluator running one merged CFG whose
observable result is `ite` — is the remaining gap; this file supplies the
semantic `ite` law each arm of such a lowering must satisfy, and shows the public
condition keeps it CT.

0 sorries; the only carried hypotheses are each arm's (`LeafAgrees` and any
`StraightLine` witness), supplied once when the arm `Phase`s are built by the
`MultiPhaseBody` smart constructors.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BranchLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
open CatCrypt.Crypto.SecureCompilation.VIR.MultiPhaseBody

/-! ## 1. The two-way branch construct and its lowering

A branch is built from a **public** condition `cond : Bool` and two arm
`Phase`s over the same accumulator `accTy`. Its lowering is, like every other
phase lowering in `MultiPhaseBody`, a self-map of the accumulator: the emitted
`run` selects the arm by the public condition; the reference `sem` does the same
on the arms' semantics. -/

/-- **A two-way public-condition branch, as a verified `Phase`.**
    `branchPhase cond thenPhase elsePhase` is the phase whose emitted `run` is
    `if cond then thenPhase.run else elsePhase.run` and whose reference `sem` is
    `if cond then thenPhase.sem else elsePhase.sem` — the `if-then-else` of the
    two arms' emit runs / semantics, selected by the **public** bit `cond`. Its
    `sound` field is discharged by case-splitting on `cond` and reusing each
    arm's own `sound` — no new proof obligation. Because it is a `Phase`, it
    drops directly into a `MultiPhaseBody.phasesRun` sequence (a branch inside a
    `setup; if …; finalize` body). -/
def branchPhase {accTy : JasminTy} (cond : Bool)
    (thenPhase elsePhase : Phase accTy) : Phase accTy where
  run := fun init => if cond then thenPhase.run init else elsePhase.run init
  sem := fun init => if cond then thenPhase.sem init else elsePhase.sem init
  sound := by
    funext init
    cases cond with
    | true  =>
        simp only [if_true]
        exact congrFun thenPhase.sound init
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact congrFun elsePhase.sound init

/-! ## 2. Denote-correctness: emitted branch run = `ite` of the arms' semantics -/

/-- **Branch denote-correctness (the `ite` law).** The emitted branch run equals
    the `if-then-else` of the two arms' reference *semantics*, selected by the
    public condition: `run init = if cond then thenPhase.sem init else
    elsePhase.sem init`. This is the branch analogue of `loopN`'s
    `loop = step^[n]` and `MultiPhaseBody`'s `sequence = left-fold` — the
    structural denotation of a public two-way branch. Proved by unfolding
    `branchPhase.run` and rewriting each arm's `run` to its `sem` via that arm's
    `sound`. -/
theorem branchPhase_run_eq {accTy : JasminTy} (cond : Bool)
    (thenPhase elsePhase : Phase accTy) (init : ⟦accTy⟧) :
    (branchPhase cond thenPhase elsePhase).run init
      = if cond then thenPhase.sem init else elsePhase.sem init := by
  show (if cond then thenPhase.run init else elsePhase.run init)
      = if cond then thenPhase.sem init else elsePhase.sem init
  rw [thenPhase.sound, elsePhase.sound]

/-- **Taken-branch corollary (`true`).** When the public condition is `true`, the
    emitted branch run is exactly the `then` arm's semantics. -/
theorem branchPhase_run_true {accTy : JasminTy}
    (thenPhase elsePhase : Phase accTy) (init : ⟦accTy⟧) :
    (branchPhase true thenPhase elsePhase).run init = thenPhase.sem init := by
  rw [branchPhase_run_eq]; rfl

/-- **Taken-branch corollary (`false`).** When the public condition is `false`,
    the emitted branch run is exactly the `else` arm's semantics. -/
theorem branchPhase_run_false {accTy : JasminTy}
    (thenPhase elsePhase : Phase accTy) (init : ⟦accTy⟧) :
    (branchPhase false thenPhase elsePhase).run init = elsePhase.sem init := by
  rw [branchPhase_run_eq]; simp

/-- **A branch with identical arms is dead.** When both arms have the same
    semantics, the branch run equals that semantics irrespective of the public
    condition — the control divergence collapses (the CT-trivial case). -/
theorem branchPhase_run_const {accTy : JasminTy} (cond : Bool)
    (arm : Phase accTy) (init : ⟦accTy⟧) :
    (branchPhase cond arm arm).run init = arm.sem init := by
  rw [branchPhase_run_eq]; cases cond <;> simp

/-! ## 3. Worked example: `if c then acc := acc + acc else acc := acc ^^^ acc`

The two arms are straight-line blocks over the singleton accumulator context
`[reg 64]`, each a `straightPhase` (sound via
`WholeFnLowering.lowerComToProg_sem_eq'`):

* `then`: `acc := acc + acc` — the doubling block `MultiPhaseBody.setupBlock`
  (denotes `acc ↦ acc + acc`);
* `else`: `acc := acc ^^^ acc` — a `regArith xor` block (denotes `acc ↦ 0`).

The branch run is the `ite` of the two; we prove it equals the `then` semantics
for `c = true` and the `else` semantics for `c = false`, at concrete seeds. -/

/-- The `else` arm block over the singleton accumulator context `[reg 64]`:
    `acc := acc ^^^ acc` (one `regArith xor`, then return). Self-map `Com`
    `[reg 64] → reg 64`, the xor analogue of `MultiPhaseBody.setupBlock`. -/
def xorBlock : Com jasminDialect [JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .xor 64) rfl (.cons .here (.cons .here .nil)))
    (.ret .here)

/-- `xorBlock` is straight-line (its lone binder is a `regArith`). -/
theorem xorBlock_straightLine : StraightLine xorBlock := by
  refine ⟨fun w n h => ?_, trivial⟩
  exact absurd h (by simp)

/-- `xorBlock.denote ⟨acc⟩ = acc ^^^ acc` (which is `0`). -/
@[simp] theorem xorBlock_denote (acc : BitVec 64) :
    xorBlock.denote (.cons acc .nil) = acc ^^^ acc := rfl

/-- **The worked branch.** `if c then (acc := acc + acc) else (acc := acc ^^^ acc)`,
    both arms `straightPhase`s over `reg 64`, selected by the public bit `c`. -/
def doubleOrXor {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) (c : Bool) :
    Phase (.reg 64) :=
  branchPhase c
    (straightPhase hLeaf setupBlock setupBlock_straightLine)
    (straightPhase hLeaf xorBlock xorBlock_straightLine)

/-- **Worked example (`c = true` ⇒ then arm fires, concrete).** On seed
    `init = 5`, the public-`true` branch runs the `then` block `acc := acc + acc`,
    giving `5 + 5 = 10` byte-for-byte. Instance of `branchPhase_run_true`. -/
theorem doubleOrXor_true_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    (doubleOrXor hLeaf true).run (5 : BitVec 64) = (10 : BitVec 64) := by
  unfold doubleOrXor
  rw [branchPhase_run_true]
  show setupBlock.denote (.cons (5 : BitVec 64) .nil) = (10 : BitVec 64)
  rw [setupBlock_denote]; rfl

/-- **Worked example (`c = false` ⇒ else arm fires, concrete).** On seed
    `init = 5`, the public-`false` branch runs the `else` block
    `acc := acc ^^^ acc`, giving `5 ^^^ 5 = 0` byte-for-byte. Instance of
    `branchPhase_run_false`. -/
theorem doubleOrXor_false_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    (doubleOrXor hLeaf false).run (5 : BitVec 64) = (0 : BitVec 64) := by
  unfold doubleOrXor
  rw [branchPhase_run_false]
  show xorBlock.denote (.cons (5 : BitVec 64) .nil) = (0 : BitVec 64)
  rw [xorBlock_denote]; rfl

/-- **Worked example (the `ite` law, both arms, symbolic).** For any public bit
    `c` and seed `init`, the emitted branch run is exactly the `if-then-else` of
    the two arms' semantics: `acc + acc` when `c`, `acc ^^^ acc` when `¬c`. This
    is the branch denote-correctness specialised to the worked branch — the
    `ite` of the two branch denotations, selected by the public condition. -/
theorem doubleOrXor_run_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (c : Bool) (init : BitVec 64) :
    (doubleOrXor hLeaf c).run init
      = if c then init + init else init ^^^ init := by
  unfold doubleOrXor
  rw [branchPhase_run_eq]
  cases c <;> rfl

/-! ## 4. A branch *inside* a sequence: `setup; if c then … else …`

Because a `branchPhase` *is* a `Phase`, it drops into a `MultiPhaseBody.phasesRun`
list as one element with no extra work — a branch nested in a straight-line /
loop sequence is sound by `phasesRun_eq` for free. This is the payoff of building
the branch at the emit-`Phase` level. -/

/-- **A 2-phase body with a branch in the tail:** `setup (acc := acc + acc);
    if c then (acc := acc + acc) else (acc := acc ^^^ acc)`. The second phase is
    the `branchPhase`. -/
def setupThenBranch {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) (c : Bool) :
    List (Phase (.reg 64)) :=
  [ straightPhase hLeaf setupBlock setupBlock_straightLine,
    doubleOrXor hLeaf c ]

/-- The `branchPhase`'s `sem` on the worked branch (helper for the sequence
    example): `if c then acc + acc else acc ^^^ acc`. -/
theorem doubleOrXor_sem_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (c : Bool) (init : BitVec 64) :
    (doubleOrXor hLeaf c).sem init
      = if c then init + init else init ^^^ init := by
  unfold doubleOrXor branchPhase
  cases c <;> rfl

/-- **Worked example (branch inside a sequence, `ite` form).** The composed run
    of `setup; branch` equals `if c then (init+init)+(init+init) else
    (init+init) ^^^ (init+init)` — the setup doubles `init`, then the public
    branch either doubles again or xors-to-zero. Sound by `phasesRun_eq`
    (sequence) composed with `branchPhase_run_eq` (branch). -/
theorem setupThenBranch_run_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (c : Bool) (init : BitVec 64) :
    phasesRun (setupThenBranch hLeaf c) init
      = (if c then (init + init) + (init + init)
         else (init + init) ^^^ (init + init)) := by
  rw [phasesRun_eq]
  unfold setupThenBranch phasesSem
  simp only [List.foldl_cons, List.foldl_nil, straightPhase]
  rw [doubleOrXor_sem_eq]; rfl

/-- **Worked example (branch in a sequence, concrete, `c = true`).** Seed
    `init = 3`: setup doubles `3 → 6`, then the `true` branch doubles again
    `6 → 12`. -/
theorem setupThenBranch_true_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    phasesRun (setupThenBranch hLeaf true) (3 : BitVec 64) = (12 : BitVec 64) := by
  rw [setupThenBranch_run_eq]; rfl

/-- **Worked example (branch in a sequence, concrete, `c = false`).** Seed
    `init = 3`: setup doubles `3 → 6`, then the `false` branch xors `6 ^^^ 6 = 0`. -/
theorem setupThenBranch_false_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    phasesRun (setupThenBranch hLeaf false) (3 : BitVec 64) = (0 : BitVec 64) := by
  rw [setupThenBranch_run_eq]; rfl

end CatCrypt.Crypto.SecureCompilation.VIR.BranchLowering
