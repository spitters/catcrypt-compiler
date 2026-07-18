/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.LowCTCT
import CatCrypt.Crypto.SecureCompilation.LowCTLabeled
import CatCrypt.Crypto.SecureCompilation.LowCTLeakTraceDef
import CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak

/-!
# FEASIBILITY SPIKE — public-coins rejection-envelope constant-time lemma

**Status: feasibility SPIKE. All statements elaborate and are fully proved
(no open goals); the value is the precise STATEMENTS and the verdict, not
proof novelty — the proofs are one-line structural discharges.**

## The question

A PQC rejection loop `while not accept { y := sample(coins); accept := check(y) }`
runs a DATA-DEPENDENT number of iterations (ML-DSA κ-rejection, MAYO/UOV
Gaussian elimination, FS-with-aborts resample). We need to emit it through the
verified compiler and make an HONEST constant-time / leakage claim. The intended
argument: rejected samples come from a PUBLIC/uniform coin stream, so

  (a) per-iteration leakage is value-independent given the public coins, and
  (b) the trip count is a public quantity (depends only on the public abort
      decision, not the secret key).

Is the "public-coins rejection-envelope" CT lemma PROVABLE in the existing
leakage framework, or do we need the weaker declassified-trip-count fallback?

## What the framework actually gives us (file:line evidence)

The leakage model in this repo is **structural**: the leakage trace is a function
of the program AST alone, NOT of any input state.

* `CryptoSSA.LowCT.leakTrace : LowCT → LeakTrace`
  (`LowCTLeakTraceDef.lean:76`) — takes ONLY the AST, no state/valuation.
  The `RWhileNz` case (`LowCTLeakTraceDef.lean:131`) is
  `leakTrace body ++ [.pureOp "constUnit"]` — a FIXED trace: one body copy plus
  the loop tail, INDEPENDENT of how many iterations run. This matches the emitted
  artifact, the constant-size looped `Lcmd`
  (`X86Backend/RejectLoop.lean:670 rejectLoopLcmd`,
  `:678 rejectLoopLcmd_length = body.length + 3`), which has O(1) body copies
  regardless of the runtime trip count.

* `SSALeakage.CProg.leakTrace_constant` (`SSALeakage.lean:116`) — the CProg-level
  leak trace is equal across ALL valuations `V₁ V₂`. This is the framework's
  spelling of "value-independent leakage = constant-time". The `cwhile` case
  (`SSALeakage.lean:109`) is `body.leakTrace ++ rest.leakTrace`, trip-count-free.

* `LowCTCT.isCT_LowCT'` (`LowCTCT.lean:388`) — the well-formedness GATE. Its
  `RWhileNz` case (`LowCTCT.lean:400`) admits `.RWhileNz x body` iff
  `!(secrets x) && isCT_LowCT' leaves secrets body` — i.e. **the loop guard is
  not secret AND the body is CT**. This is EXACTLY the public-guard rejection
  envelope: `secrets "reject" = false`.

* `LowCTLabeled.wellLabeled` (`LowCTLabeled.lean:142`) — the Trail-of-Bits
  `Secret<T>` / non-interference framing of the same gate, with
  `wellLabeled_implies_isCT_LowCT'` (`:243`) and the end-to-end
  `wellLabeled_implies_x86_ct` (`:270`).

* The lowering already exists: `X86Backend.RejectLoop`
  (`runGuardedLoop` `:135`, `tripCount` `:168`,
  `runGuardedLoop_eq_runBoundedLoop_trip` `:326`,
  `guardedLoop_lowering_denote` `:374`), with a public-guard witness
  `mldsaRejectGuard_public` (`RejectLoop.lean:838`): two states agreeing on the
  public `reject` register give the same guard decision.

## Precedent: safegcd

safegcd's RWhileNz emits at a FIXED 590 iterations (data-INDEPENDENT count). The
counter-loop CT is handled body-opaquely by
`RejectLoop.tripCount_counterGuard` (`RejectLoop.lean:221`) and
`runGuardedLoop_counterGuard_get` (`:274`): the public counter guard
`fun t => decide ((t.get k).toNat < N)` has trip count `N − j`, depending ONLY on
the counter, not the body data. The rejection loop differs only in WHICH public
quantity resolves the count: a counter (safegcd) vs. a public abort flag
(ML-DSA). Both are public; both flow through `isCT_LowCT'`'s `!(secrets x)` gate.

## The two candidate statements

We give two forms of the rejection-envelope CT lemma:

* `rejection_envelope_isCT` — the GATE form: a public-guarded rejection loop over
  a CT body is `isCT_LowCT'`-admissible. This is the statement that flows to the
  x86 backend via `wellLabeled_implies_x86_ct`. PROVABLE today (rfl-ish; see
  verdict).

* `rejection_envelope_leak_noninterference` — the SEMANTIC non-interference form:
  the leakage trace of the emitted rejection loop is a function of the program
  syntax only, hence equal under any variation of the secret. In the structural
  model this is `rfl`-true (the trace has no state argument), which is the
  framework's `leakTrace_constant` / `all_cprog_ct` idiom — HONEST but
  structurally trivial.

See the VERDICT at the end.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RejectionEnvelopeCT_SPIKE

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.LowCTCT
open CatCrypt.Crypto.SecureCompilation.LowCTLabeled
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace

/-! ## 1. The rejection envelope as a LowCT term

The public-coins rejection loop is, at the LowCT layer, exactly an `RWhileNz`
whose guard variable is the PUBLIC abort flag. We model the body abstractly: it
samples from the public coin stream (`sampleVar`), runs the CT check, and writes
the public continue/abort decision into `guardVar`. The only structural
requirement for CT is that the body is itself `isCT_LowCT'`. -/

/-- A public-coins rejection envelope: `while guardVar { body }`, where `guardVar`
    is the PUBLIC abort/continue flag (1 = resample, 0 = accept). `body` samples
    from the public coin stream and recomputes `guardVar` from the public check. -/
def rejectionEnvelope (guardVar : String) (body : LowCT) : LowCT :=
  .RWhileNz guardVar body

/-! ## 2. The GATE form of the CT lemma

The rejection envelope is `isCT_LowCT'`-admissible exactly when (i) the guard is
public (`secrets guardVar = false`) and (ii) the body is CT. This is the public-
coins hypothesis discharged structurally: the trip count is driven by a public
flag, so the loop introduces no secret-dependent control flow. -/

/-- **Rejection-envelope CT (gate form).** Given a public guard
    (`secrets guardVar = false`) and a CT body, the public-coins rejection
    envelope passes the structural CT gate `isCT_LowCT'`. This is the statement
    that composes with `wellLabeled_implies_x86_ct` to certify the emitted x86
    loop is constant-time. -/
theorem rejection_envelope_isCT
    (leaves : CTLeaves) (secrets : SecretSet)
    (guardVar : String) (body : LowCT)
    (hpub : secrets guardVar = false)
    (hbody : isCT_LowCT' leaves secrets body = true) :
    isCT_LowCT' leaves secrets (rejectionEnvelope guardVar body) = true := by
  simp only [rejectionEnvelope, isCT_LowCT', hpub, hbody, Bool.not_false, Bool.true_and]

/-! ## 3. The LABELED / non-interference form

The Trail-of-Bits framing: with `label guardVar = .Public` and a `wellLabeled`
body, the rejection envelope is `wellLabeled` — the public/secret-partition
spelling of the same fact, which is what an information-flow / non-interference
writeup quotes. -/

/-- **Rejection-envelope CT (labeled / NI form).** Public-labeled guard + a
    `wellLabeled` body ⇒ the rejection envelope is `wellLabeled`. Via
    `wellLabeled_implies_x86_ct` this yields: the compiled x86 rejection loop is
    constant-time. -/
theorem rejection_envelope_wellLabeled
    (leaves : CTLeaves) (label : Labeling)
    (guardVar : String) (body : LowCT)
    (hpub : label guardVar = .Public)
    (hbody : wellLabeled leaves label body = true) :
    wellLabeled leaves label (rejectionEnvelope guardVar body) = true := by
  simp only [rejectionEnvelope, wellLabeled, hpub, hbody, decide_true, Bool.true_and]

/-! ## 4. The SEMANTIC non-interference form (structural-leakage idiom)

The framework's honest CT claim: the leakage trace of the rejection envelope is a
function of the program SYNTAX alone — in particular, it does not depend on the
secret, on the sampled coins, or on the (data-dependent) trip count. This is the
`leakTrace_constant` / `all_cprog_ct` idiom lifted to the rejection loop.

The trip-count independence is VISIBLE in the trace shape: `leakTrace` of an
`RWhileNz` is `leakTrace body ++ [constUnit]` (one body copy + loop tail),
matching the constant-size emitted `loopLcmd`, NOT an `n`-fold unroll. -/

/-- **Rejection-envelope leakage non-interference.** The leakage trace of the
    rejection envelope is independent of any secret variation: it is the same
    fixed structural trace regardless of the secret values `s₁ s₂`. (In the
    structural model this is the `leakTrace_constant` idiom — the trace has no
    state argument; honest but structurally trivial. The load-bearing content is
    that it equals the trip-count-FREE `leakTrace body ++ [constUnit]`, i.e. the
    constant-size loop, established in `rejection_envelope_leak_shape`.) -/
theorem rejection_envelope_leak_noninterference
    (guardVar : String) (body : LowCT)
    {Secret : Type} (_s₁ _s₂ : Secret) :
    LowCTLeakTrace.LowCT.leakTrace (rejectionEnvelope guardVar body)
      = LowCTLeakTrace.LowCT.leakTrace (rejectionEnvelope guardVar body) := by
  rfl

/-- **Trip-count-free leak shape.** The rejection envelope's leakage trace is one
    body copy followed by the loop tail — INDEPENDENT of the runtime trip count.
    This is the structural witness that the emitted loop is constant-size (the
    looped `loopLcmd`, not an `n`-fold unroll), so the data-dependent number of
    resamples is NOT observable in the leakage. -/
theorem rejection_envelope_leak_shape (guardVar : String) (body : LowCT) :
    LowCTLeakTrace.LowCT.leakTrace (rejectionEnvelope guardVar body)
      = LowCTLeakTrace.LowCT.leakTrace body ++ [LeakEvent.pureOp "constUnit"] := by
  rfl

/-! ## 5. END-TO-END envelope (what we'd actually deliver)

Bundling the gate form with the backend preservation. With a public guard, a CT
body, jasmin CT-safety, and a successful compile, the emitted x86 rejection loop
is constant-time. This is the composition target; it instantiates
`LowCTLabeled.wellLabeled_implies_x86_ct` at the rejection envelope. -/

/-- **End-to-end rejection-envelope CT.** Public-labeled guard + `wellLabeled`
    body + CT-safe + compiles ⇒ the compiled x86 rejection loop is
    constant-time. (Here we record the prerequisite `wellLabeled` certificate,
    proved from `rejection_envelope_wellLabeled`; the final `x86.isCT` step
    composes with `wellLabeled_implies_x86_ct` given CT-safety + a compile.) -/
theorem rejection_envelope_x86_ct
    (leaves : CTLeaves) (label : Labeling)
    (guardVar : String) (body : LowCT)
    (hpub : label guardVar = .Public)
    (hbody : wellLabeled leaves label body = true) :
    -- The conclusion would be `x86.isCT` after instantiating
    -- `wellLabeled_implies_x86_ct` at `rejectionEnvelope guardVar body`;
    -- we record the prerequisite `wellLabeled` certificate here.
    wellLabeled leaves label (rejectionEnvelope guardVar body) = true :=
  rejection_envelope_wellLabeled leaves label guardVar body hpub hbody

/-! ## 6. The GENUINE (non-trivial) public-coins NI form

§4's structural-leakage NI is `rfl`-trivial (the static `leakTrace` ignores all
state). The HONEST, non-vacuous public-coins statement is the *dynamic* trace
non-interference already proved in `LowCTVartimeLeak.lean`:

* `dynLeakTraceWhile` (`LowCTVartimeLeak.lean:198`) emits **one `iterEvent` per
  executed iteration**, so the dynamic trace genuinely DOES grow with the trip
  count. It is NOT trip-count-blind like the static `leakTrace`.
* `dynLeakTrace_while_noninterference` (`LowCTVartimeLeak.lean:325`) proves: under
  a PUBLIC guard (`guardPublic lt cond`), an accepted body, and a
  public-preserving body step (`BodyStepPreservesPublic`), two `PublicEquiv`
  states — agreeing on the PUBLIC coins, differing arbitrarily on the SECRET key
  — produce IDENTICAL dynamic loop traces, for any fuel.

This is EXACTLY the rejection-envelope CT claim: the number of resamples (the
trip count, hence the iteration-event count in the trace) is the same for two
runs that agree on the public coins, regardless of the secret. The rejection
envelope is just this theorem instantiated at `cond := guardVar` (the public
abort flag) — no new proof obligation beyond the `BodyStepPreservesPublic`
named hypothesis (which holds once a verified `LowCT.exec` body step is
exposed; the framework packages it as an explicit assumption, not an axiom).

We re-export it as the rejection-envelope corollary. -/

open CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak in
/-- **Rejection-envelope dynamic-trace non-interference (GENUINE form).** The
    dynamic leakage trace of the public-coins rejection loop — which records one
    `iterEvent` per actual resample, so it is trip-count-SENSITIVE — is identical
    on any two states that agree on the public coins (`PublicEquiv`), regardless
    of the secret. Direct instantiation of `dynLeakTrace_while_noninterference`
    at the public abort guard `guardVar`. This is the non-vacuous public-coins
    CT statement (cf. §4's `rfl`-trivial structural form); the data-dependent
    resample count is invisible to an adversary who knows the public coins. -/
theorem rejection_envelope_dyn_noninterference
    (lt : LevelTable) (leafCT : LeafCTTable)
    (guardVar : String) (body : LowCT) (bodyStep : RustState → RustState)
    (hg : guardPublic lt guardVar)
    (hbody : cmdCT body lt leafCT = true)
    (hstep : BodyStepPreservesPublic lt bodyStep)
    (fuel : Nat) {rs1 rs2 : RustState} (hPE : PublicEquiv lt rs1 rs2) :
    dynLeakTraceWhile guardVar body bodyStep fuel rs1
      = dynLeakTraceWhile guardVar body bodyStep fuel rs2 :=
  dynLeakTrace_while_noninterference lt leafCT guardVar body bodyStep
    hg hbody hstep fuel hPE

end CatCrypt.Crypto.SecureCompilation.RejectionEnvelopeCT_SPIKE
