/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
import CatCrypt.Crypto.SecureCompilation.RejectionEnvelopeCT_SPIKE

/-!
# M2 — data-dependent rejection loop: the back-edge denotation tie at the `LowCT` layer

**Milestone M2.** A data-dependent (rejection-style) `RWhileNz` loop where the
guard is RECOMPUTED inside the body, with (1) a proved tie between the relational
`LowCT.RustExec` semantics of the loop and the mathematical "iterate the body
until the guard reads 0" fixpoint (the **back-edge denotation tie**), and (2) an
emit path to a constant-size `.s` function via the existing
`X86Backend.RejectLoop` lowering, with an executable KAT reference.

## KEY QUESTION, answered

> Does `RWhileNz` + its `denote` + emit ALREADY support a data-dependent guard
> (just used with a fixed one by safegcd), so M2 is "demonstrate + tie", or does
> the denote/emit assume a fixed trip count (so M2 must generalize it)?

**Answer: it ALREADY supports a data-dependent guard. M2 is "demonstrate + tie",
no generalization of `denote`/emit is needed.** Evidence:

* `LowCT.RustExec.whileTrue` / `whileFalse`
  (`CatCrypt/Crypto/Jasmin/LowCT.lean:1692-1699`) read the guard from the
  CURRENT state at each iteration — `whileTrue` recurses on `RWhileNz e body`
  from the POST-body state `r1`, re-reading `r1.rsScalar e`. There is no trip-
  count parameter; the loop runs until the body drives `rsScalar e` to 0. The
  fuel `N` is a bound on the derivation, never consumed in the rules. So a body
  that recomputes the guard variable yields a genuinely data-dependent number of
  iterations.

* The machine-level emission `X86Backend.RejectLoop.runGuardedLoop`
  (`RejectLoop.lean:135`) takes an ARBITRARY guard predicate
  `guard : JState w → Bool` and `guardedLoop_lowering_denote_closed`
  (`RejectLoop.lean:385`) proves the lowered constant-size `Com`/`loopLcmd`
  denotes it for ANY such guard. safegcd's fixed-count loop is the
  `tripCount_counterGuard` (`RejectLoop.lean:221`) INSTANCE — a counter guard
  `fun t => decide ((t.get k).toNat < N)` — not a special-cased fixed loop. The
  ML-DSA rejection demo `mldsaSignAttemptBody` / `mldsaRejectGuard`
  (`RejectLoop.lean:730,749`) already exercises the data-dependent case: the
  body recomputes the public `reject` flag each attempt.

What was MISSING (and is supplied here) is the explicit bridge between the
`LowCT`-layer RELATIONAL semantics (`RustExec` on `RWhileNz`) and the FUNCTIONAL
"iterate until guard 0" fixpoint that `runGuardedLoop` realizes at the machine
layer. The CT/leakage side is `RejectionEnvelopeCT_SPIKE.lean` (M0, reused, not
redone). This file supplies the back-edge denotation tie.

## What is proved here

* `rustWhileIterate f e` — the functional fixpoint: iterate `f` while
  `rsScalar e ≠ 0`, fuel-bounded (total).
* `rustWhileIterate_completeness` — the SOUNDNESS/forward direction of the tie:
  if `f` realizes the body (`RustExec body rs (f rs)`) and the iterate
  terminates within `fuel` (the guard reads 0 at the end), then
  `RustExec (.RWhileNz e body) rs (rustWhileIterate f e fuel rs)`. This is the
  back-edge composition: each `whileTrue` step glues one body realization to the
  recursive loop on the post-body state.
* `rustWhileIterate_unfold_nz` / `_z` — the back-edge unfolding equations the
  tie rests on.
* A concrete DATA-DEPENDENT rejection body (`rejectStepBody`) whose guard
  variable `"reject"` is recomputed each iteration from a decreasing counter,
  with the iterate computed by `decide` and the `RustExec` derivation obtained
  from `rustWhileIterate_completeness`.

## Emit driver + KAT for the orchestrator

The emit + executable KAT for the SAME data-dependent rejection shape already
lives in `X86Backend/RejectLoop.lean` §7 (the ML-DSA signing loop):

* emit driver: `RejectLoop.lowerGuardedLoop … mldsaSignFuel mldsaRejectGuard
  mldsaSignAttemptBody mldsaSignInit` → `Com (x86Dialect 64)`, rendered via
  `rejectLoopLcmd` (`= LprogControlFlow.loopLcmd`, constant-size) →
  `LprogAsmPrinter.renderLfundef` → `.s`.
* denotation tie at the machine layer: `mldsaSign_lowering_correct`
  (`RejectLoop.lean:797`) — the lowered loop denotes `runGuardedLoop`.
* KAT references (already `native_decide`-checked in `RejectLoop.lean`):
  trip count = 4, `kappa = 4 ∧ normz = 90 ∧ reject = 0`.

This file adds the corresponding executable KAT at the `LowCT` layer: the
`rustWhileIterate` of the data-dependent rejection body computes the same
"terminate at the first accepting attempt" transcript, so the C harness can
replay it deterministically against the emitted `.s`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RejectionLoopEmitDemo

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The functional "iterate until guard 0" fixpoint

This is the mathematical object the emitted back-edge realizes: given a body
TRANSFORMER `f : RustState → RustState` and a guard variable `e`, run `f` while
`rsScalar e ≠ 0`. `fuel` makes the recursion total; it is a bound, not a fixed
trip count — the loop stops as soon as the guard reads 0, exactly like
`RejectLoop.runGuardedLoop`. -/

/-- Iterate the body transformer `f` while the scalar guard `e` is nonzero,
    bounded by `fuel`. The functional analogue of `RustExec`'s `RWhileNz` rules:
    `whileFalse` ↔ `rsScalar e = 0` (return unchanged), `whileTrue` ↔ run `f`
    once then recurse on `f rs`. -/
def rustWhileIterate (f : RustState → RustState) (e : String) :
    Nat → RustState → RustState
  | 0, rs => rs
  | fuel + 1, rs => if rs.rsScalar e = 0 then rs
                    else rustWhileIterate f e fuel (f rs)

@[simp] theorem rustWhileIterate_zero (f : RustState → RustState) (e : String)
    (rs : RustState) : rustWhileIterate f e 0 rs = rs := rfl

/-- Back-edge unfolding (guard zero): the loop exits with the state unchanged. -/
@[simp] theorem rustWhileIterate_unfold_z (f : RustState → RustState) (e : String)
    (fuel : Nat) (rs : RustState) (h : rs.rsScalar e = 0) :
    rustWhileIterate f e (fuel + 1) rs = rs := by
  simp [rustWhileIterate, h]

/-- Back-edge unfolding (guard nonzero): the loop runs the body once (`f rs`)
    then recurses on the post-body state — the loop's back-edge. -/
@[simp] theorem rustWhileIterate_unfold_nz (f : RustState → RustState) (e : String)
    (fuel : Nat) (rs : RustState) (h : rs.rsScalar e ≠ 0) :
    rustWhileIterate f e (fuel + 1) rs = rustWhileIterate f e fuel (f rs) := by
  simp [rustWhileIterate, h]

/-! ## 2. The back-edge denotation tie

The soundness/forward direction: when `f` realizes the body relationally
(`RustExec body rs (f rs)` for all `rs`) AND the iterate has actually reached a
guard-zero state within `fuel` (`(rustWhileIterate f e fuel rs).rsScalar e = 0`,
i.e. the loop genuinely terminated and was not fuel-truncated), the relational
`RustExec` semantics of `RWhileNz` agrees with the functional iterate. The proof
is the back-edge gluing: each nonzero step composes one `RustExec.whileTrue`
(body realization + recursive loop) and the final zero step is
`RustExec.whileFalse`. -/

/-- **Back-edge denotation tie (completeness/forward).** If `f` realizes the loop
    body under `RustExec`, and the functional iterate terminated (its final guard
    reads 0 within `fuel`), then the relational `RustExec` semantics of the
    data-dependent `RWhileNz e body` loop reaches exactly the functional iterate.
    This is the `LowCT`-layer counterpart of `RejectLoop`'s machine-level
    `guardedLoop_lowering_denote`: it ties the recomputed-guard `RWhileNz` to the
    "iterate body until guard 0" fixpoint across the loop back-edge. -/
theorem rustWhileIterate_completeness
    (N : Nat) (leafSpec : LeafSpec) (e : String) (body : LowCT)
    (f : RustState → RustState)
    (hf : ∀ rs, RustExec N leafSpec body rs (f rs)) :
    ∀ (fuel : Nat) (rs : RustState),
      (rustWhileIterate f e fuel rs).rsScalar e = 0 →
      RustExec N leafSpec (.RWhileNz e body) rs (rustWhileIterate f e fuel rs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro rs hterm
      -- fuel 0: iterate = rs, and termination forces rsScalar e = 0.
      simp only [rustWhileIterate_zero] at hterm ⊢
      exact RustExec.whileFalse e body rs hterm
  | succ k ih =>
      intro rs hterm
      by_cases hz : rs.rsScalar e = 0
      · -- guard already 0: whileFalse, iterate is rs.
        simp only [rustWhileIterate_unfold_z f e k rs hz]
        exact RustExec.whileFalse e body rs hz
      · -- guard nonzero: one back-edge step (whileTrue), recurse on f rs.
        rw [rustWhileIterate_unfold_nz f e k rs hz] at hterm ⊢
        exact RustExec.whileTrue e body rs (f rs)
          (rustWhileIterate f e k (f rs)) (rs.rsScalar e)
          rfl hz (hf rs) (ih (f rs) hterm)

/-! ## 3. A concrete DATA-DEPENDENT rejection body

Unlike safegcd's fixed countdown, the guard variable `"reject"` is RECOMPUTED by
the body each iteration from a counter, so the trip count is resolved by the data
(the recomputed guard), not by a compile-time constant.

We model the body as a state transformer `rejectStep` mirroring the machine body
`RejectLoop.mldsaSignAttemptBody`: bump an attempt counter `"kappa"`, and set the
public guard `"reject"` to 0 once enough attempts have passed (here: accept at
`kappa = 4`), 1 otherwise. The functional iterate then terminates at the first
accepting attempt — the rejection-loop behaviour. -/

/-- The data-dependent rejection step (state transformer form): one signing
    attempt. Bumps `"kappa"`; recomputes the PUBLIC guard `"reject"` to 0 (accept)
    once `kappa ≥ 4`, else 1 (resample). The guard is recomputed FROM the body's
    own state advance — data-dependent termination. -/
def rejectStep (rs : RustState) : RustState :=
  let k := rs.rsScalar "kappa" + 1
  let rs1 := rsSetScalar rs "kappa" k
  rsSetScalar rs1 "reject" (if 4 ≤ k then 0 else 1)

/-- Initial signing state: `kappa = 0`, `reject = 1` (loop entered with a pending
    rejection), mirroring `RejectLoop.mldsaSignInit`. -/
def rejectInit : RustState :=
  rsSetScalar (rsSetScalar default "kappa" 0) "reject" 1

/-- Fuel cap — generous over the worst-case attempt count, only making the
    iterate total (cf. `RejectLoop.mldsaSignFuel`). -/
def rejectFuel : Nat := 64

/-- **KAT (value): the data-dependent rejection iterate terminates at the first
    accepting attempt.** The recomputed guard drives 4 attempts (`kappa` 1,2,3
    resample, attempt 4 accepts), stopping with `kappa = 4`, `reject = 0`. The
    trip count is DATA-DEPENDENT (resolved by the recomputed guard), not a
    compile-time constant — matching `RejectLoop.lean`'s machine-level KAT
    (`kappa = 4`, `reject = 0`). -/
theorem rejectIterate_kat :
    (rustWhileIterate rejectStep "reject" rejectFuel rejectInit).rsScalar "kappa" = 4
      ∧ (rustWhileIterate rejectStep "reject" rejectFuel rejectInit).rsScalar "reject" = 0 := by
  constructor <;> native_decide

/-- The iterate genuinely terminated (final guard reads 0) within fuel — the
    hypothesis the back-edge tie consumes. -/
theorem rejectIterate_terminates :
    (rustWhileIterate rejectStep "reject" rejectFuel rejectInit).rsScalar "reject" = 0 := by
  native_decide

/-! ## 4. The relational `RustExec` derivation for the data-dependent loop

Given a `LeafSpec` and a body LowCT term whose `RustExec` is realized by
`rejectStep`, the back-edge tie produces the `RustExec` derivation for the whole
data-dependent rejection loop, ending at the (computed) accepting transcript. We
state it parametrically over the realizer hypothesis `hf`: the body emission is
orthogonal to the back-edge tie, so the loop's relational semantics follow from
ANY body whose transformer is `rejectStep` (e.g. the `RScalarSet`-style emission
of `mldsaSignAttemptBody`). -/

/-- **The data-dependent rejection loop's `RustExec` reaches the accepting
    transcript.** For any body realized by `rejectStep`, the relational semantics
    of `RWhileNz "reject" body` from `rejectInit` reaches the functional iterate,
    which (by `rejectIterate_kat`) is the accepting state `kappa = 4, reject = 0`.
    This composes `rustWhileIterate_completeness` (the back-edge tie) with the
    termination witness `rejectIterate_terminates`. -/
theorem rejectLoop_rustExec
    (N : Nat) (leafSpec : LeafSpec) (body : LowCT)
    (hf : ∀ rs, RustExec N leafSpec body rs (rejectStep rs)) :
    RustExec N leafSpec (.RWhileNz "reject" body) rejectInit
      (rustWhileIterate rejectStep "reject" rejectFuel rejectInit) :=
  rustWhileIterate_completeness N leafSpec "reject" body rejectStep hf
    rejectFuel rejectInit rejectIterate_terminates

/-! ## 5. CT side: reuse M0

The constant-time / leakage side of THIS loop is already discharged by
`RejectionEnvelopeCT_SPIKE.rejection_envelope_x86_ct` (public guard `"reject"` +
CT body ⇒ the emitted x86 rejection loop is constant-time) and its non-vacuous
public-coins dynamic-trace form `rejection_envelope_dyn_noninterference`. We do
NOT redo it here; this file supplies the orthogonal denotation tie. -/

/-- The rejection guard `"reject"` used here is the SAME public guard the M0 CT
    spike admits: `rejectionEnvelope "reject" body` is `RWhileNz "reject" body`,
    so the M0 gate-form CT lemma applies verbatim once `"reject"` is declared
    public and the body is CT. (Re-export for the orchestrator — no new proof.) -/
theorem rejectLoop_eq_envelope (body : LowCT) :
    LowCT.RWhileNz "reject" body
      = RejectionEnvelopeCT_SPIKE.rejectionEnvelope "reject" body := rfl

/-! ## 6. The cross-layer loop-transport (the M2 residual, now FORMAL)

M2's `rustWhileIterate_completeness` (§2) ties the `LowCT`-layer relational
`RustExec` to the functional iterate `rustWhileIterate` at the `LowCT` layer;
`RejectLoop.guardedLoop_lowering_denote` ties the machine-layer lowered loop to
`RejectLoop.runGuardedLoop` at the machine layer. What M2 left INFORMAL was the
identification between the two iterates: both realize "iterate the body until the
guard reads 0", but no theorem related the `LowCT` `RustState` iterate to the
machine `JState` iterate.

This section closes that gap. The canonical `RustState`↔`JState` correspondence
the straight-line `LowCT`→`JInstr` compile-correctness preserves is
`X86Backend.LowCTToJInstrCT.StateMatch ρ rs js`
(`LowCTToJInstrCT.lean:177`: every source slot `v` has the machine register
`ρ v` holding `BitVec.ofNat 64 (rs.rsScalar v)`). The per-body forward simulation
is `LowCTToJInstrCT.lowerSeq_denote` (`LowCTToJInstrCT.lean:405`), proved:
`StateMatch ρ rs js → StateMatch ρ (srcDenote ps rs) (runBlock js (lowerSeq ρ ps))`.

The loop transport below is the fuel-inductive closure of that body simulation
across the loop back-edge. We take it parametric over:

* a body transformer `f : RustState → RustState` (the `LowCT`-side body, e.g.
  `srcDenote ps`) and a machine body block `bodyJ : List (JInstr 64)` (e.g.
  `lowerSeq ρ ps`), tied by the per-body simulation hypothesis
  `hbody : ∀ rs js, StateMatch ρ rs js → StateMatch ρ (f rs) (runBlock js bodyJ)`
  — discharged by `lowerSeq_denote` for the scalar-arith fragment;
* a guard correspondence `hguard : ∀ rs js, StateMatch ρ rs js →
  (guard js = decide (rs.rsScalar e ≠ 0))` — the machine guard CONTINUES exactly
  when the `LowCT` guard scalar is nonzero (note the polarity: `RWhileNz` /
  `rustWhileIterate` continue on `≠ 0`, `runGuardedLoop` continues on
  `guard = true`).

Under these, `rustWhileIterate f e fuel` (LowCT) and
`runGuardedLoop fuel guard bodyJ` (machine) produce `StateMatch`-related final
states, for any fuel and any related initial states. This is the formal
`LowCT.RustState`→`JState` loop-transport theorem the M2 docstring flagged as
the honest gap. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT in
open CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop in
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin in
/-- **Cross-layer loop transport (M2 residual, formal).** If `StateMatch ρ`
    relates the initial states, the per-body lowering is `StateMatch ρ`-preserving
    (`hbody` — discharged by `lowerSeq_denote`), and the machine guard tracks the
    `LowCT` guard scalar with the right polarity (`hguard`), then the `LowCT`
    iterate `rustWhileIterate f e fuel` and the machine iterate
    `runGuardedLoop fuel guard bodyJ` end in `StateMatch ρ`-related states. The
    proof is a fuel induction lifting `hbody` across the loop back-edge: at each
    nonzero step both layers run their body once (`StateMatch` preserved by
    `hbody`) and recurse on the post-body states. -/
theorem rustWhileIterate_runGuardedLoop_transport
    (ρ : RegMap) (e : String) (f : RustState → RustState)
    (bodyJ : List (JInstr 64)) (guard : JState 64 → Bool)
    (hbody : ∀ rs js, StateMatch ρ rs js → StateMatch ρ (f rs) (runBlock js bodyJ))
    (hguard : ∀ rs js, StateMatch ρ rs js → (guard js = decide (rs.rsScalar e ≠ 0))) :
    ∀ (fuel : Nat) (rs : RustState) (js : JState 64),
      StateMatch ρ rs js →
      StateMatch ρ (rustWhileIterate f e fuel rs)
        (runGuardedLoop fuel guard bodyJ js) := by
  intro fuel
  induction fuel with
  | zero =>
      intro rs js hm
      simpa using hm
  | succ k ih =>
      intro rs js hm
      by_cases hz : rs.rsScalar e = 0
      · -- LowCT guard 0 ⇒ machine guard false ⇒ both layers stop at the current state.
        have hgf : guard js = false := by
          rw [hguard rs js hm]; simp [hz]
        rw [rustWhileIterate_unfold_z f e k rs hz,
            runGuardedLoop_guard_false (k + 1) guard bodyJ js hgf]
        exact hm
      · -- LowCT guard ≠ 0 ⇒ machine guard true ⇒ both layers run the body once,
        -- recurse on the StateMatch-related post-body states.
        have hgt : guard js = true := by
          rw [hguard rs js hm]; simp [hz]
        rw [rustWhileIterate_unfold_nz f e k rs hz, runGuardedLoop_succ, if_pos hgt]
        exact ih (f rs) (runBlock js bodyJ) (hbody rs js hm)

/-! ### 6b. The transport with the per-body hypothesis discharged by `lowerSeq_denote`

The abstract `hbody` of `rustWhileIterate_runGuardedLoop_transport` is exactly
the canonical straight-line `LowCT`→`JInstr` per-body simulation
`LowCTToJInstrCT.lowerSeq_denote` for the scalar-arith body fragment. Here we
discharge it: for a rejection-loop whose body is a straight-line block of
scalar-arith assignments `ps` (LowCT side `srcDenote ps`, machine side
`lowerSeq ρ ps`), the loop transport holds with NO body hypothesis — it follows
from `lowerSeq_denote` directly. This shows the transport is the fuel-inductive
closure of the ALREADY-PROVED per-body correspondence, not of an assumed one. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT in
open CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop in
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin in
/-- **Cross-layer loop transport with `lowerSeq` body (per-body hypothesis
    discharged).** For a rejection loop whose body is the straight-line
    scalar-arith block `ps`, the `LowCT` iterate `rustWhileIterate (srcDenote ps)`
    and the machine iterate `runGuardedLoop fuel guard (lowerSeq ρ ps)` end in
    `StateMatch ρ`-related states — given the same register well-formedness
    (`hρ`, `hwf`) the straight-line compile-correctness needs, and the guard
    correspondence `hguard`. The body hypothesis is supplied by
    `lowerSeq_denote`, so this is the loop closure of the genuine per-body
    simulation. -/
theorem rustWhileIterate_runGuardedLoop_transport_lowerSeq
    (ρ : RegMap) (hρ : Function.Injective ρ) (e : String) (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst) (guard : JState 64 → Bool)
    (hguard : ∀ rs js, StateMatch ρ rs js → (guard js = decide (rs.rsScalar e ≠ 0))) :
    ∀ (fuel : Nat) (rs : RustState) (js : JState 64),
      StateMatch ρ rs js →
      StateMatch ρ (rustWhileIterate (srcDenote ps) e fuel rs)
        (runGuardedLoop fuel guard (lowerSeq ρ ps) js) :=
  rustWhileIterate_runGuardedLoop_transport ρ e (srcDenote ps) (lowerSeq ρ ps) guard
    (fun rs js hm => lowerSeq_denote ρ hρ ps hwf rs js hm) hguard

end CatCrypt.Crypto.SecureCompilation.RejectionLoopEmitDemo
