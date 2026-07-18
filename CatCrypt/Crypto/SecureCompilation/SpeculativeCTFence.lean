/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.SpeculativeCT

/-!
# Verified fence-insertion: speculative CT against an *unconstrained* predictor

**Task #564 residual.**  `SpeculativeCT.lean` delivered the speculative
leakage semantics over the owned `LowCT` stream (`specObs`,
`SpeculativelyConstantTime`) and the keystone `architecturally_CT_imp_SCT`.
That keystone, however, holds because the misprediction oracle there is a pure
function of the *public* branch value — so its choices are public-determined
the moment `cmdCT` certifies the branch public.  A *real* attacker controls the
branch predictor **adversarially**; against such a predictor the bare keystone
says nothing, because the predictor could in principle steer transient
execution down a secret-dependent wrong path.

This file closes that gap with the **sound, blanket mitigation**: a verified
`LowCT → LowCT` pass `insertFences` that places a speculation barrier
(`lfence`) at the head of every branch arm and loop body, and the theorem that
the fenced program is speculatively constant-time against an **unconstrained**
misprediction oracle.

The argument is the classic *"lfence drains speculation"* one (it is exactly
why Jasmin's Spectre-declassified backend, and the SLH literature, insert
fences): a fence truncates the transient (mis-speculated) window to zero at
that point, so a wrong-path that begins with a fence contributes **no**
transient observations.  With a fence at the head of every arm, the entire
speculative leakage trace collapses to the *architectural* leakage trace —
which `cmdCT` already certifies secret-independent.  Crucially, this holds for
**every** oracle, including an adversarial one, because the collapse is
structural (no oracle choice survives the drain).

## What this provides

1. `RFence` — a fence marker modelled as the zero-cost `LowCT.RAssert`
   no-op (Phase-L assertions have no runtime effect and leak nothing), so the
   pass needs no new `LowCT` constructor and reuses the existing `cmdCT` /
   `archObs` / `specObs` clauses unchanged.

2. `insertFences : LowCT → LowCT`, a structural recursion that fences the head
   of every `RIfNz` arm and every `RWhileNz` / `RFor` body.

3. **Denotation preservation** (`archObs_insertFences`,
   `cmdCT_insertFences`): the fence is a no-op for the architectural
   semantics (the architectural leakage trace is unchanged) and the pass
   preserves `cmdCT` acceptance.  (`LowCT` lowers to Jasmin and has no separate
   executable big-step here; the architectural *leakage* trace `archObs` is the
   denotation the CT story reasons over, exactly as in
   `architecturally_CT_imp_ArchCT`.)

4. **Fenced speculative semantics** (`specObsF`, `specTransient`): identical to
   `specObs` except that, on a branch, the mis-speculated wrong-path
   contribution is computed by `specTransient`, which *drains at the first
   fence* (returns `[]` on `RFence`).  This is the operational content of
   "lfence drains speculation".

5. **The unconstrained-oracle keystone**
   (`specObsF_insertFences_eq_archObs`, `insertFences_SCT_unconstrained`): for
   *any* window and *any* (adversarial) oracle, the fenced speculative trace of
   `insertFences c` equals the architectural trace of `c`; hence if `c` is
   architecturally CT (`cmdCT`), `insertFences c` is speculatively CT against an
   unconstrained predictor.

Applied to the pilot branch kernel `SpeculativeCT.Pilot.pilotKernelBranch`.

## Coverage (all four Spectre transient sources)

The 2026-06 extension carries the fence/mitigation past Spectre-v1 to the full
set of transient sources `SpeculativeCT.lean` now models:

| Variant | Mitigation inserted by `insertFences`           | Drained by | Proved |
|---------|--------------------------------------------------|------------|--------|
| PHT/v1  | `lfence` (`RFence`) at branch-arm / loop-body head | `specTransient` (wrong-path drain) | yes |
| BTB/v2  | retpoline-shape site-guard (`RGuard`) before the indirect call | `specObsF_fenceGuard` (transient drain) | yes |
| RSB     | RSB-stuffing site-guard before the matching return | `specObsF_fenceGuard` | yes |
| STL/v4  | SSBD / LFENCE site-guard before the load/store    | `specObsF_fenceGuard` | yes |

All four are proved SCT against an **unconstrained adversarial** oracle by the
single collapse theorem `specObsF_insertFences_eq_archObs` →
`insertFences_SCT_unconstrained`: every transient source resolves at its
guarded site and drains, so the fenced speculative trace equals the
architectural one regardless of the oracle.

## Honest scope

* This is the **blanket-fence + blanket-site-guard** mitigation: a fence at
  every branch and a guard before every call/load/store.  It is sound
  (provably SCT-vs-unconstrained-oracle) but conservative on performance.  The
  stronger Cauligi/Jasmin **selective speculative-load-hardening (SLH)** —
  masking only secret-dependent loads instead of blanket fencing — is a perf
  optimization with a harder proof obligation; it is *not* attempted here and
  is reported as the residual.
* The BTB/RSB site-guards are modelled as zero-cost barrier markers at the
  call's destination slot (the target/return register of the frame); see the
  `SpeculativeCT.lean` residual on the indirect-control abstraction (`LowCT`
  has no dedicated indirect-jump/`ret` constructor).  STL's microarchitectural
  store-buffer datum is a model assumption (the *address* pattern is what we
  model and drain; the bypassed datum's value is delegated to leaf-CT).

## References

* Cauligi et al., "Constant-Time Foundations for the New Spectre Era",
  PLDI 2020 (the speculative semantics and SLH).
* Shivakumar, Barthe, Grégoire, Laporte, Oliveira, Priya, Rezk, Schwabe,
  "Typing High-Speed Cryptography against Spectre v1", IEEE S&P 2023
  (Jasmin's fence/SLH selective protection — the perf-optimal variant).
-/

namespace CatCrypt.Crypto.SecureCompilation.SpeculativeCT

open CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-! ## §1.  The fence marker

We model an `lfence` speculation barrier as the zero-cost Phase-L assertion
`RAssert fenceLabel`.  Phase-L assertions have **no** runtime effect and emit
**no** bytes (their Hoare rule only injects a proposition), so reusing them as
the fence marker means:

* the pass introduces **no new `LowCT` constructor** (every existing analyser /
  observer clause for `RAssert` applies verbatim), and
* the fence is, by construction, a no-op for the architectural semantics — it
  leaks nothing (`archObs … (RAssert _) = []`) and is always `cmdCT`-clean
  (`cmdCT (RAssert _) = true`).

A *distinguished* label `fenceLabel` lets the fenced speculative observer
recognise the barrier and drain the transient window there. -/

/-- The distinguished assertion label marking a speculation barrier. -/
def fenceLabel : String := "__lfence__"

/-- A speculation barrier (`lfence`), modelled as the zero-cost `RAssert`
    no-op carrying the distinguished `fenceLabel`. -/
def RFence : LowCT := .RAssert fenceLabel

/-- A distinguished label marking a *site guard* barrier: an `lfence`/retpoline/
    SSBD placed **before** an indirect call, return, or load, serialising that
    site so its BTB/RSB/STL transient source cannot fire.  Distinguished from
    `fenceLabel` (a branch/loop-head barrier) so the fenced observer can drain
    the guarded site's transient while leaving committed execution untouched. -/
def guardLabel : String := "__guard__"

/-- A site-guard barrier (retpoline-shape for BTB/RSB, SSBD/LFENCE for STL),
    modelled as the zero-cost `RAssert` no-op carrying `guardLabel`. -/
def RGuard : LowCT := .RAssert guardLabel

theorem guardLabel_ne_fenceLabel : guardLabel ≠ fenceLabel := by decide

@[simp] theorem archObs_RFence (rs : RustState) : archObs rs RFence = [] := rfl

@[simp] theorem specObs_RFence (window : SpecWindow) (O : MispredOracle)
    (rs : RustState) : specObs window O rs RFence = [] := rfl

@[simp] theorem cmdCT_RFence (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT RFence lt leafCT = true := rfl

/-! ## §2.  The fence-insertion pass

`insertFences c` rewrites `c`, placing an `RFence` at the head of every branch
arm (`RIfNz`) and every loop body (`RWhileNz`, `RFor`), and recursing
structurally everywhere else.  Fencing the *head* of each arm means that when
the predictor speculatively enters the wrong arm, the very first instruction it
meets is the barrier, which drains the transient window before any wrong-path
memory/branch observation can be issued. -/

/-- Prepend a speculation barrier to a command. -/
def fenced (c : LowCT) : LowCT := .RSeq RFence c

@[simp] theorem archObs_fenced (rs : RustState) (c : LowCT) :
    archObs rs (fenced c) = archObs rs c := by
  simp [fenced, archObs, RFence]

@[simp] theorem cmdCT_fenced (c : LowCT) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (fenced c) lt leafCT = cmdCT c lt leafCT := by
  simp [fenced, cmdCT_RSeq, RFence]

/-- Prepend a *site-guard* barrier to a call/load/store, serialising the site
    so its BTB/RSB/STL transient source cannot fire. -/
def fenceGuard (c : LowCT) : LowCT := .RSeq RGuard c

@[simp] theorem archObs_fenceGuard (rs : RustState) (c : LowCT) :
    archObs rs (fenceGuard c) = archObs rs c := by
  simp [fenceGuard, archObs, RGuard]

@[simp] theorem cmdCT_fenceGuard (c : LowCT) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (fenceGuard c) lt leafCT = cmdCT c lt leafCT := by
  simp [fenceGuard, cmdCT_RSeq, RGuard]

/-- The fence-insertion pass.

    * An `RFence` (`lfence`) at the head of every **branch arm** and **loop
      body** — the Spectre-PHT (v1) mitigation: a misprediction into either arm
      drains immediately.
    * An `RGuard` (retpoline for BTB/RSB, SSBD/LFENCE for STL) **before** every
      indirect **call** (BTB/RSB) and every **load/store** (STL) — serialising
      the site so its transient source cannot fire.

    Structural everywhere else. -/
def insertFences : LowCT → LowCT
  | .RSeq c1 c2             => .RSeq (insertFences c1) (insertFences c2)
  | .RLetZero x t body      => .RLetZero x t (insertFences body)
  | .RLetU64Zero x body     => .RLetU64Zero x (insertFences body)
  | .RBlock body            => .RBlock (insertFences body)
  | .RFnDef n p r body cont => .RFnDef n p r (insertFences body) (insertFences cont)
  | .RIfNz cond ct cf       =>
      -- Fence the head of *both* arms: a misprediction into either arm drains
      -- immediately.  (PHT/v1)
      .RIfNz cond (fenced (insertFences ct)) (fenced (insertFences cf))
  | .RWhileNz cond body     =>
      -- Fence the loop body head: a mispredicted guard speculatively enters the
      -- body and drains at once.  (PHT/v1)
      .RWhileNz cond (fenced (insertFences body))
  | .RFor x n body          => .RFor x n (fenced (insertFences body))
  -- Site-guard the indirect call (BTB/RSB) and the load/store (STL).
  | .RCall f dest args      => fenceGuard (.RCall f dest args)
  | .RArrLoad dst src idx   => fenceGuard (.RArrLoad dst src idx)
  | .RArrStore arr idx src  => fenceGuard (.RArrStore arr idx src)
  | c                       => c

/-! ## §3.  Denotation preservation

The fence is a no-op for the architectural semantics, so `insertFences`
preserves the architectural leakage trace, and preserves `cmdCT` acceptance.
These are the "denote (insertFences c) = denote c" obligations at the
granularity the CT story reasons over (`LowCT` has no separate executable
big-step here; `archObs` is its leakage denotation). -/

/-- **Architectural denotation preservation.**  `insertFences` does not change
    the architectural leakage trace: the inserted fences are no-ops. -/
@[simp] theorem archObs_insertFences (rs : RustState) (c : LowCT) :
    archObs rs (insertFences c) = archObs rs c := by
  induction c generalizing rs with
  | RSeq c1 c2 ih1 ih2 => simp [insertFences, archObs, ih1, ih2]
  | RLetZero x t body ih => simp [insertFences, archObs, ih]
  | RLetU64Zero x body ih => simp [insertFences, archObs, ih]
  | RBlock body ih => simp [insertFences, archObs, ih]
  | RFnDef n p r body cont ihB ihC => simp [insertFences, archObs, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertFences, archObs, archObs_fenced, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertFences, archObs, archObs_fenced, ih]
  | RFor x n body ih =>
      simp only [insertFences, archObs, archObs_fenced, ih]
  | RCall f dest args => simp only [insertFences, archObs_fenceGuard]
  | RArrLoad dst src idx => simp only [insertFences, archObs_fenceGuard]
  | RArrStore arr idx src => simp only [insertFences, archObs_fenceGuard]
  | _ => rfl

/-- **Acceptance preservation.**  `insertFences` preserves `cmdCT` acceptance:
    fences are always `cmdCT`-clean, and the pass changes nothing else. -/
@[simp] theorem cmdCT_insertFences (c : LowCT) (lt : LevelTable)
    (leafCT : LeafCTTable) :
    cmdCT (insertFences c) lt leafCT = cmdCT c lt leafCT := by
  induction c generalizing lt with
  | RSeq c1 c2 ih1 ih2 => simp [insertFences, cmdCT_RSeq, ih1, ih2]
  | RLetZero x t body ih => simp [insertFences, cmdCT_RLetZero, ih]
  | RLetU64Zero x body ih => simp [insertFences, cmdCT_RLetU64Zero, ih]
  | RBlock body ih => simp [insertFences, cmdCT_RBlock, ih]
  | RFnDef n p r body cont ihB ihC =>
      simp [insertFences, cmdCT_RFnDef, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertFences, cmdCT_RIfNz, cmdCT_fenced, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertFences, cmdCT_RWhileNz, cmdCT_fenced, ih]
  | RFor x n body ih =>
      simp only [insertFences, cmdCT_RFor, cmdCT_fenced, ih]
  | RCall f dest args => simp only [insertFences, cmdCT_fenceGuard]
  | RArrLoad dst src idx => simp only [insertFences, cmdCT_fenceGuard]
  | RArrStore arr idx src => simp only [insertFences, cmdCT_fenceGuard]
  | _ => rfl

/-! ## §4.  Fenced speculative semantics — "lfence drains speculation"

The fenced speculative observer `specObsF` is identical to `specObs`, except
that the mis-speculated wrong-path contribution is computed by the auxiliary
`specTransient`, which **drains at the first fence**: as soon as transient
execution meets an `RFence`, the speculation window is flushed and no further
transient observation is issued.

This is the operational content of an `lfence`: the barrier serialises, so the
processor cannot read any further down the wrong path past it.  Because
`insertFences` puts a fence at the *head* of every arm/body, the transient
trace of a fenced wrong-path is empty. -/

/-- Transient (mis-speculated) observations of `c`, capped at `window`
    instructions, and **drained at the first fence**.  An `RFence` flushes the
    speculation window: nothing past it is observed transiently.  All other
    constructors contribute their architectural observation and recurse; the
    overall result is truncated to `window` by the caller.

    We only need the *head-fence* case for the keystone (a fenced arm starts
    with `RFence`), so non-fence constructors fall back to the architectural
    observation of the (truncated) prefix; the `RFence` and `RSeq`-with-leading-
    fence cases are what make the drain fire. -/
def specTransient (rs : RustState) : LowCT → ObsTrace
  | .RAssert _              => []
  | .RSeq c1 c2             =>
      -- If the first statement drains (it is a fence), the whole transient
      -- window is flushed; otherwise accumulate and continue.
      match c1 with
      | .RAssert s => if s = fenceLabel then [] else specTransient rs c2
      | _          => specTransient rs c1 ++ specTransient rs c2
  | c                       => archObs rs c

@[simp] theorem specTransient_RFence (rs : RustState) :
    specTransient rs RFence = [] := by
  simp [specTransient, RFence, fenceLabel]

@[simp] theorem specTransient_fenced (rs : RustState) (c : LowCT) :
    specTransient rs (fenced c) = [] := by
  simp [specTransient, fenced, RFence, fenceLabel]

/-- Cap a mis-speculated transient trace with a `rollback` marker — but only if
    the transient trace is **non-empty**.  A rollback observation is only
    visible if speculation actually issued cache/branch observations; a window
    that drained immediately (e.g. at a leading fence) issues nothing, hence no
    observable rollback.  This is what lets a fenced wrong-path collapse the
    speculative trace to the architectural one. -/
def withRollback : ObsTrace → ObsTrace
  | []    => []
  | l     => l ++ [Obs.rollback]

@[simp] theorem withRollback_nil : withRollback [] = [] := rfl

/-! ### BTB / RSB / STL transient sources are *transient-only*

The three post-v1 Spectre sources we added in `SpeculativeCT.lean`
(`indirectTarget`/BTB, `retTarget`/RSB, `stlForward`/STL) are leaks that occur
**only during mis-speculation**: committed (architecturally correct) execution
does not leak the injected indirect target, the mispredicted return-stack top,
or the bypassed store value.  In `specObs` they are therefore oracle-gated
(they vanish under `neverMispred`).  Operationally they resolve at the call /
return / load–store site, so the *same* `lfence`-drain that handles a PHT
wrong-path handles them: a fence placed *before* the indirect call / return /
load serialises execution and the transient source cannot fire.

To model this in the fenced observer we route a call/load/store's speculative
sources through `specObsF` as oracle-gated transients **only when the site is
not fence-guarded**.  A fence-guarded site is emitted by `insertFences` as
`fenced stmt = RSeq RFence stmt`; the fenced observer recognises the leading
fence and emits the site's *committed* (architectural) observation only,
dropping its oracle-gated transient.  `committedObs` is that architectural-only
trace (it ignores the oracle entirely, so no transient source survives). -/

/-- The committed (architecturally-correct) observation of a single, already
    fence-guarded statement: its architectural leakage, with **no** speculative
    transient source.  Used for a statement whose speculation has been drained
    by a preceding fence (`insertFences` fence-guards every call/load/store). -/
def committedObs (rs : RustState) (c : LowCT) : ObsTrace := archObs rs c

@[simp] theorem committedObs_eq_archObs (rs : RustState) (c : LowCT) :
    committedObs rs c = archObs rs c := rfl

/-- The fenced speculative observer.  Identical to `specObs`, but:

    * the mis-speculated *branch* wrong-path is computed by `specTransient`
      (which drains at a fence) rather than by a raw `.take window`, and
    * a *fence-guarded* statement (`RSeq RFence stmt`, as `insertFences` emits
      for every call/load/store) contributes only its **committed**
      (architectural) observation: the leading fence drains the BTB/RSB/STL
      transient source the same way it drains a PHT wrong-path.

    After `insertFences`, every branch arm / loop body begins with a fence (so
    `specTransient` of every wrong-path is `[]`), and every call / load / store
    is fence-guarded (so its BTB/RSB/STL transient is drained). -/
def specObsF (window : SpecWindow) (O : MispredOracle) (rs : RustState) :
    LowCT → ObsTrace
  | .RSkip                  => []
  | .RAssert _              => []
  | .RScalarSet _ _         => []
  | .RScalarSetExpr _ _     => []
  | .RSeq c1 c2             =>
      -- A leading fence drains the transient source of the statement it
      -- guards: emit that statement's *committed* observation only.
      match c1 with
      | .RAssert s =>
          -- A *guard* fence (`guardLabel`) drains the BTB/RSB/STL transient of
          -- the call/load/store it guards: emit that site's committed
          -- observation only.  A plain branch/loop-head fence (`fenceLabel`) is
          -- a no-op for committed execution (it only drains the wrong-path
          -- transient, handled in the `RIfNz`/`RWhileNz` clauses).
          if s = guardLabel then committedObs rs c2
          else specObsF window O rs c1 ++ specObsF window O rs c2
      | _ => specObsF window O rs c1 ++ specObsF window O rs c2
  | .RLetZero _ _ body      => specObsF window O rs body
  | .RLetU64Zero _ body     => specObsF window O rs body
  | .RBlock body            => specObsF window O rs body
  | .RFnDef _ _ _ body cont =>
      specObsF window O rs body ++ specObsF window O rs cont
  | .RIfNz cond ct cf       =>
      let v := rs.rsScalar cond
      let obsCt : ObsTrace := specObsF window O rs ct
      let obsCf : ObsTrace := specObsF window O rs cf
      -- Mis-speculated wrong-path, *drained at the first fence*.
      let speculated : ObsTrace :=
        if O.mispredict cond v then
          withRollback
            ((if v ≠ 0 then specTransient rs cf else specTransient rs ct).take window)
        else []
      Obs.branch cond v :: (speculated ++ (if v ≠ 0 then obsCt else obsCf))
  | .RWhileNz cond body     =>
      let v := rs.rsScalar cond
      let obsBody : ObsTrace := specObsF window O rs body
      let speculated : ObsTrace :=
        if O.mispredict cond v then
          withRollback ((specTransient rs body).take window)
        else []
      Obs.branch cond v :: (speculated ++ obsBody)
  | .RFor _ _ body          => specObsF window O rs body
  | .RArrStore _ idxVar _   => [Obs.memIdx idxVar (rs.rsScalar idxVar)]
  | .RArrLoad dst _ idxVar  =>
      -- Unfenced load: the STL transient fires (oracle-gated).  Mirrors the
      -- `specObs` STL clause; drained when fence-guarded (see `RSeq` above).
      let stl : ObsTrace :=
        if O.bypassStore idxVar (rs.rsScalar idxVar) then
          withRollback [Obs.stlForward idxVar (rs.rsScalar idxVar)]
        else []
      Obs.memIdx idxVar (rs.rsScalar idxVar) :: (stl ++ (let _ := dst; []))
  | .RCall _ dest _         =>
      -- Unfenced call: the BTB + RSB transients fire (oracle-gated).
      let tslot := dest.locVar
      let tv := rs.rsScalar tslot
      let btb : ObsTrace :=
        if O.injectTarget tslot tv then withRollback [Obs.indirectTarget tslot tv]
        else []
      let rsb : ObsTrace :=
        if O.mispredRet tslot tv then withRollback [Obs.retTarget tslot tv]
        else []
      btb ++ rsb
  | _                       => []

/-- The fenced speculative observer ignores a leading branch/loop-head fence
    (it is the zero-cost `RAssert` no-op, and `fenceLabel ≠ guardLabel`):
    `specObsF` of `fenced c` is `specObsF` of `c`.  (Committed execution is
    unchanged by a branch-head fence; only the wrong-path transient drains.) -/
@[simp] theorem specObsF_fenced (window : SpecWindow) (O : MispredOracle)
    (rs : RustState) (c : LowCT) :
    specObsF window O rs (fenced c) = specObsF window O rs c := by
  simp [fenced, specObsF, RFence, fenceLabel, guardLabel]

/-- A *site-guard* drains the guarded site's BTB/RSB/STL transient: `specObsF`
    of `fenceGuard c` is the **committed** (architectural) observation of `c`. -/
@[simp] theorem specObsF_fenceGuard (window : SpecWindow) (O : MispredOracle)
    (rs : RustState) (c : LowCT) :
    specObsF window O rs (fenceGuard c) = archObs rs c := by
  simp [fenceGuard, specObsF, RGuard, guardLabel, committedObs]

/-! ## §5.  The unconstrained-oracle keystone

For a *fenced* program — one where every branch arm / loop body begins with a
fence — the mis-speculated contribution of every branch is `[]` (the wrong-path
drains at its leading fence), regardless of the oracle.  Hence the fenced
speculative trace collapses to the architectural trace, **for every window and
every oracle**.

Composing with `archObs_insertFences`, the fenced speculative trace of
`insertFences c` equals the architectural trace of `c`. -/

/-- `insertFences` produces an `RAssert` head **only** from an `RAssert`
    source: every other constructor maps to a non-`RAssert` node.  (Used to
    discharge the guarded-head subcase of the collapse theorem.) -/
theorem insertFences_eq_RAssert {c : LowCT} {s : String}
    (h : insertFences c = LowCT.RAssert s) : c = LowCT.RAssert s := by
  cases c <;> simp_all [insertFences, fenceGuard, RGuard]

/-- **Collapse on `insertFences c`.**  The fenced speculative trace of
    `insertFences c` equals the architectural trace of `c`, for *any* window
    and *any* (adversarial) oracle: every wrong-path begins with a fence, so
    `specTransient` drains it to `[]` and no oracle choice survives. -/
theorem specObsF_insertFences_eq_archObs
    (window : SpecWindow) (O : MispredOracle) (rs : RustState) (c : LowCT) :
    specObsF window O rs (insertFences c) = archObs rs c := by
  induction c generalizing rs with
  | RSkip => rfl
  | RAssert _ => rfl
  | RScalarSet _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RSeq c1 c2 ih1 ih2 =>
      -- `insertFences (RSeq c1 c2) = RSeq (insertFences c1) (insertFences c2)`.
      -- `specObsF` pattern-matches the head `insertFences c1`; it is an
      -- `RAssert s` only if the source `c1` is, in which case `insertFences`
      -- leaves it untouched.  The guarded subcase (`s = guardLabel`) means
      -- `c1 = RAssert guardLabel`, whose architectural leakage is `[]`.
      simp only [insertFences, specObsF, archObs]
      split
      · rename_i s heq
        split
        · -- guarded head: `c1 = RAssert guardLabel`, so `archObs rs c1 = []`.
          have hc1 : c1 = LowCT.RAssert s := insertFences_eq_RAssert heq
          subst hc1
          simp only [archObs, committedObs, archObs_insertFences, List.nil_append]
        · simp only [ih1, ih2]
      · simp only [ih1, ih2]
  | RLetZero x t body ih =>
      simp only [insertFences, specObsF, archObs, ih]
  | RLetU64Zero x body ih =>
      simp only [insertFences, specObsF, archObs, ih]
  | RBlock body ih =>
      simp only [insertFences, specObsF, archObs, ih]
  | RFnDef n p r body cont ihB ihC =>
      simp only [insertFences, specObsF, archObs, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      -- The speculated wrong-path is `specTransient` of a *fenced* arm = [],
      -- so `withRollback ([].take window) = []`; the taken arm is fenced, so
      -- `specObsF_fenced` + ih reduce it.
      simp only [insertFences, specObsF, specObsF_fenced, archObs,
        specTransient_fenced, List.take_nil, withRollback_nil, List.nil_append,
        ite_self, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertFences, specObsF, specObsF_fenced, archObs,
        specTransient_fenced, List.take_nil, withRollback_nil, List.nil_append,
        ite_self, ih, List.singleton_append]
  | RFor x n body ih =>
      simp only [insertFences, specObsF, specObsF_fenced, archObs, ih]
  | RCall f dest args =>
      -- The call is site-guarded: `specObsF_fenceGuard` drops the BTB/RSB
      -- transient and leaves the (empty) architectural call observation.
      simp only [insertFences, specObsF_fenceGuard]
  | RArrLoad dst src idx =>
      -- The load is site-guarded: the STL transient is dropped, leaving the
      -- architectural memory-index observation.
      simp only [insertFences, specObsF_fenceGuard]
  | RArrStore arr idx src =>
      simp only [insertFences, specObsF_fenceGuard]
  | _ => rfl

/-! ## §6.  Speculative CT against an unconstrained predictor -/

/-- **Speculatively constant-time (fenced semantics).**  Two executions of `c`
    from `PublicEquiv` states produce equal *fenced* speculative leakage traces,
    under window `window` and oracle `O`. -/
def SpeculativelyConstantTimeF
    (window : SpecWindow) (O : MispredOracle) (lt : LevelTable) (c : LowCT) :
    Prop :=
  ∀ rs1 rs2 : RustState, PublicEquiv lt rs1 rs2 →
    specObsF window O rs1 c = specObsF window O rs2 c

/-- **The deliverable: verified fence-insertion ⇒ SCT vs. an unconstrained
    oracle.**  If `c` is architecturally constant-time (`cmdCT`), then
    `insertFences c` is speculatively constant-time against an **arbitrary**
    (adversarial) misprediction oracle and **any** speculation window.

    Proof: by `specObsF_insertFences_eq_archObs` the fenced speculative trace of
    `insertFences c` is the architectural trace of `c`, which is
    secret-independent by `architecturally_CT_imp_ArchCT`.  The oracle and
    window are universally quantified and never enter the collapsed trace —
    this is the "lfence drains speculation" guarantee against an unconstrained
    predictor. -/
theorem insertFences_SCT_unconstrained
    (window : SpecWindow) (O : MispredOracle)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true) :
    SpeculativelyConstantTimeF window O lt (insertFences c) := by
  intro rs1 rs2 hEq
  rw [specObsF_insertFences_eq_archObs, specObsF_insertFences_eq_archObs]
  exact architecturally_CT_imp_ArchCT lt leafCT c hCT rs1 rs2 hEq

/-! ## §7.  Pilot: the branching kernel is SCT against an unconstrained oracle

We exercise the unconstrained-oracle keystone on `Pilot.pilotKernelBranch`
(the `RIfNz`-on-public-flag kernel that genuinely drives the speculative
machinery).  Its architectural acceptance discharges by `cmdCT`
(`Pilot.pilotKernelBranch_cmdCT`); the fence pass then makes it SCT for *any*
predictor. -/

namespace Pilot

/-- `cmdCT` acceptance survives fence insertion on the branching pilot kernel
    (a tiny `native_decide` vector, mirroring `pilotKernelBranch_cmdCT`). -/
theorem insertFences_pilotKernelBranch_cmdCT :
    cmdCT (insertFences pilotKernelBranch) pilotLevels LeafCTTable.canonical
      = true := by
  native_decide

/-- **Pilot result.**  The fenced branching kernel `insertFences
    pilotKernelBranch` is speculatively constant-time against an
    **unconstrained** misprediction oracle, for every speculation window.  This
    is the sound, blanket-fence mitigation: even an adversarial predictor's
    transient wrong-path leaks nothing, because the head-fence drains the
    window before any wrong-path observation is issued. -/
theorem pilotKernelBranch_SCT_unconstrained
    (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTimeF window O pilotLevels
      (insertFences pilotKernelBranch) :=
  insertFences_SCT_unconstrained window O pilotLevels LeafCTTable.canonical
    pilotKernelBranch pilotKernelBranch_cmdCT

end Pilot

/-! ### Mitigation-effectiveness witnesses

These check that the site-guard genuinely *removes* the BTB/RSB/STL transient
(not vacuously): the unfenced call/load leaks the transient observation under a
firing oracle, while the guarded form drains it to the architectural trace. -/

/-- An oracle firing every speculative source. -/
def allFireF : MispredOracle :=
  ⟨fun _ _ => true, fun _ _ => true, fun _ _ => true, fun _ _ => true⟩

/-- Unfenced indirect call leaks the BTB + RSB transient under a firing oracle. -/
theorem call_unfenced_leaks :
    specObsF 8 allFireF Sanity.st (.RCall "f" ⟨"tgt", .TU64⟩ [])
      = [Obs.indirectTarget "tgt" 7, Obs.rollback,
         Obs.retTarget "tgt" 7, Obs.rollback] := by
  native_decide

/-- **Site-guard drains BTB/RSB.**  `insertFences` on the same indirect call
    produces the guarded form whose fenced speculative trace is the (empty)
    architectural call trace — the transient is gone, for the firing oracle. -/
theorem call_guarded_drains :
    specObsF 8 allFireF Sanity.st (insertFences (.RCall "f" ⟨"tgt", .TU64⟩ []))
      = [] := by
  native_decide

/-- **Site-guard drains STL.**  `insertFences` on a load drains the STL
    transient, leaving only the architectural memory-index observation. -/
theorem load_guarded_drains :
    specObsF 8 allFireF Sanity.st
        (insertFences (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx"))
      = [Obs.memIdx "idx" 3] := by
  native_decide

/-! ## §8.  What this gets us, and what remains

**Delivered (this file).**
* `insertFences : LowCT → LowCT`, a structural pass placing (i) an `lfence`
  (`RFence`) at the head of every branch arm / loop body — the PHT/v1
  mitigation — and (ii) a site-guard (`RGuard`: retpoline/RSB-stuffing/SSBD)
  before every indirect call (BTB/RSB) and every load/store (STL).
* **Denotation preservation**: `archObs_insertFences` (architectural leakage
  trace unchanged) and `cmdCT_insertFences` (acceptance preserved) — both the
  fence and the site-guard are genuine no-ops for the non-speculative
  semantics.
* **Fenced speculative semantics** (`specObsF` + `specTransient` +
  `committedObs`) implementing "barrier drains speculation": the PHT
  wrong-path is flushed at its leading fence (`specTransient`), and a
  site-guarded call/load/store's BTB/RSB/STL transient is drained to its
  committed (architectural) observation (`specObsF_fenceGuard`).
* **The unconstrained-oracle keystone** `insertFences_SCT_unconstrained`: an
  architecturally-CT program, once fenced+guarded, is speculatively CT against
  an *arbitrary adversarial* predictor and *any* window, over **all four
  Spectre sources** (PHT/BTB/RSB/STL).  Applied to `Pilot.pilotKernelBranch`.
  `call_unfenced_leaks` / `call_guarded_drains` / `load_guarded_drains`
  witness the site-guard genuinely removes the BTB/RSB/STL transient (the
  mitigation is non-vacuous).

**Variant-coverage matrix** (modelled? mitigated? proved?):

| Variant | Modelled (`SpeculativeCT.lean`) | Mitigation | Proved SCT vs unconstrained oracle |
|---------|---------------------------------|------------|------------------------------------|
| PHT/v1  | `branch` + wrong-path window    | `lfence` arm/loop head | yes |
| BTB/v2  | `indirectTarget`                | retpoline-shape `RGuard` before call | yes |
| RSB     | `retTarget`                     | RSB-stuffing `RGuard` before return | yes |
| STL/v4  | `stlForward`                    | SSBD/LFENCE `RGuard` before load/store | yes |

All four discharge through `specObsF_insertFences_eq_archObs` (axiom profile:
`propext`; the pilot/witness `native_decide` lemmas additionally carry the
standard `native_decide` axiom).

**What remains (honest residual / model assumptions).**
* **Selective SLH (perf).**  This is the *blanket* mitigation — a barrier at
  every branch/call/load.  The Cauligi/Jasmin selective speculative-load-
  hardening variant masks only secret-dependent loads (far fewer barriers),
  trading a harder proof obligation for much lower overhead.  That is the
  perf-optimal follow-up; the present blanket version is its sound baseline.
* **Indirect-control abstraction (BTB/RSB).**  `LowCT` has no dedicated
  indirect-jump/`ret` constructor, so the BTB/RSB site-guard is placed before
  *every* call.  A dedicated indirect-control node would let the pass guard
  only genuinely-indirect sites.  Sound but conservative.
* **STL store-buffer model.**  The STL guard drains the modelled *address*
  transient; the bypassed datum's *value* leakage is delegated to leaf-CT, as
  for an ordinary load.  A full store-buffer model is the residual. -/

end CatCrypt.Crypto.SecureCompilation.SpeculativeCT
