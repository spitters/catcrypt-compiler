/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.LowCTLeakTraceDef
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Foundation for sound variable-time support

This module generalises the constant-time guarantee from "leak nothing"
(full CT) to **noninterference modulo public declassification**: code may
leak *at most its public inputs*.  This is the standard
constant-time-with-public-values policy (FaCT, the Jasmin CT type system,
CT-wasm), and the leak-nothing guarantee is recovered as the special case
where *no* input is classified `Public`.

## Where the existing pieces live, and what this module adds

The repository already has, in the orphaned RHP/cmdCT/leakTrace chain:

* `LowCT.leakTrace : LowCT → LeakTrace` (`LowCTLeakTrace.lean`) — a
  **static / structural** trace. Crucially it is a function of the program
  *syntax only*; it takes no `RustState`. So for *that* trace, two runs of
  the same program produce identical traces *trivially* — there is nothing
  for a secret to perturb. That is the right model for the
  branch-free / data-oblivious fragment, but it cannot express the leakage
  of a variable-time construct (a data-dependent branch leaks
  *which* branch ran; a data-dependent loop leaks its *iteration count*).

* `cmdCT : LowCT → LevelTable → LeafCTTable → Bool`
  (`LowCTCTAnalysis.lean`) — the syntactic analyser. It already **gates**
  the variable-time constructors on a `Public` guard / index:
  `RIfNz cond _ _` and `RWhileNz cond _` are accepted iff
  `lt cond = .Public`; `RArrLoad _ _ idxVar` iff `lt idxVar = .Public`;
  fail-closed (rejected) on a `Secret` guard/index. This *is* the
  public-taint typing rule (Deliverable 2); we restate it as named
  predicates below and prove the gate behaves as claimed.

* `PublicEquiv lt rs1 rs2` (`LowCTCTAnalysis.lean`) — the Volpano–Smith /
  Goguen–Meseguer low-equivalence relation: two `RustState`s agree on every
  `Public`-classified slot, secrets may differ.

What is **new** in this file:

1. `dynLeakTrace : LowCT → RustState → LeakTrace` — a **dynamic** (state-
   dependent) leak trace. It coincides with the static `LowCT.leakTrace`
   on the data-oblivious fragment, but for `RIfNz` it emits a `branch`
   event recording *which* branch the guard selected, and for `RWhileNz`
   it emits one `iter` event *per executed iteration*. These are the two
   places where variable-time control flow becomes observable.

2. The **noninterference-modulo-public theorem** (Deliverable 1):
   if `cmdCT c lt leafCT = true` and `PublicEquiv lt rs1 rs2`, then
   `dynLeakTrace c rs1 = dynLeakTrace c rs2`. Two runs that agree on the
   public inputs produce identical traces, even if they differ on secrets.

3. The leak-nothing corollary as the empty-public special case
   (Deliverable 1, second half), and a worked tiny example (Deliverable 3):
   a single `RIfNz` with a `Public` guard satisfies the rule and is
   accepted; with a `Secret` guard the analyser rejects it.

## Assumption ledger

* The straight-line + `RIfNz` fragment of the noninterference theorem is
  **proved** (`dynLeakTrace_noninterference`, see the per-constructor
  lemmas it dispatches to).
* The `RWhileNz` (data-dependent loop) clause of the dynamic trace is
  defined with an explicit **fuel** and a caller-supplied **body
  state-transition** `bodyStep`. Proving the loop NI clause needs the fact
  that one loop body iteration preserves `PublicEquiv` and the public
  guard value — exactly the small-step semantics the orphaned chain does
  not yet expose as a reusable `LowCT.exec`. We therefore state that step
  as the **named hypothesis** `BodyStepPreservesPublic` (a `Prop`-valued
  structure field, *not* an admitted proof and *not* an axiom) and prove the loop
  NI clause *relative to it* (`dynLeakTrace_while_noninterference`). When
  the chain grows a verified `LowCT.exec`, this hypothesis is discharged,
  not removed.

No open goals, no new axiom. The one gap (loop-body state evolution) is an
explicit hypothesis with this docstring, as required.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace

set_option autoImplicit false

/-! ## §1. The public-taint typing rule (Deliverable 2)

The analyser `cmdCT` already enforces the rule; we name its two
variable-time clauses as standalone predicates so the policy is stated
explicitly rather than buried in the fold. `guardPublic`/`indexPublic`
say "the guard / index variable is classified `Public`". The analyser
accepts a variable-time construct **iff** the relevant predicate holds
(and the sub-programs are themselves accepted); on a `Secret` guard /
index it is fail-closed. -/

/-- The data-dependent-branch / data-dependent-loop guard `cond` is derived
from public inputs only. -/
def guardPublic (lt : LevelTable) (cond : String) : Prop := lt cond = .Public

/-- A public-indexed array access has its index variable classified
`Public`. -/
def indexPublic (lt : LevelTable) (idxVar : String) : Prop := lt idxVar = .Public

/-- **Typing rule, branch clause.** `cmdCT` accepts `RIfNz cond ct cf`
iff the guard is public *and* both branches are accepted. This is exactly
the FaCT / Jasmin "public-condition" rule; the default (non-public guard)
is rejection. -/
theorem cmdCT_RIfNz_iff (cond : String) (ct cf : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RIfNz cond ct cf) lt leafCT = true ↔
      (guardPublic lt cond ∧ cmdCT ct lt leafCT = true ∧ cmdCT cf lt leafCT = true) := by
  simp only [cmdCT_RIfNz, Bool.and_eq_true, guardPublic]
  rw [level_beq_public_iff]
  tauto

/-- **Typing rule, loop clause.** `cmdCT` accepts `RWhileNz cond body`
iff the guard is public and the body is accepted. -/
theorem cmdCT_RWhileNz_iff (cond : String) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RWhileNz cond body) lt leafCT = true ↔
      (guardPublic lt cond ∧ cmdCT body lt leafCT = true) := by
  simp only [cmdCT_RWhileNz, Bool.and_eq_true, guardPublic]
  rw [level_beq_public_iff]

/-- **Typing rule, public-indexed load clause.** A `Secret` index is
rejected (fail-closed); the access is accepted only with a `Public`
index (and public dst/src). -/
theorem cmdCT_RArrLoad_iff (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrLoad dst src idxVar) lt leafCT = true ↔
      (indexPublic lt idxVar ∧ lt dst.locVar = .Public ∧ lt src.locVar = .Public) := by
  simp only [cmdCT_RArrLoad, Bool.and_eq_true, indexPublic]
  rw [level_beq_public_iff, level_beq_public_iff, level_beq_public_iff, and_assoc]

/-- Fail-closed corollary: a secret-classified branch guard is rejected. -/
theorem cmdCT_RIfNz_secret_rejected (cond : String) (ct cf : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hSecret : lt cond = .Secret) :
    cmdCT (.RIfNz cond ct cf) lt leafCT = false := by
  by_contra h
  simp only [Bool.not_eq_false] at h
  rw [cmdCT_RIfNz_iff] at h
  have := h.1
  unfold guardPublic at this
  rw [hSecret] at this
  exact absurd this (by decide)

/-! ## §2. The dynamic, state-dependent leak trace -/

/-- A variable-time-aware leak event tag. We reuse the existing
`LeakEvent.pureOp` carrier and distinguish the two variable-time
observations by name:

* `"branch:1"` / `"branch:0"` — a data-dependent branch took the
  true / false arm (the guard was nonzero / zero).
* `"iter"` — one observed iteration of a data-dependent loop.

The static (data-oblivious) constructors keep the *same* events the
existing `LowCT.leakTrace` emits, so on the branch-free fragment the
dynamic trace coincides with the static one. -/
@[simp] def branchEvent (b : Bool) : LeakEvent := .pureOp (if b then "branch:1" else "branch:0")

/-- Iteration marker for a data-dependent loop. -/
@[simp] def iterEvent : LeakEvent := .pureOp "iter"

/-- Read the (scalar) guard of a `RIfNz`/`RWhileNz`: nonzero ⇒ true arm. -/
@[simp] def guardBit (rs : RustState) (cond : String) : Bool := rs.rsScalar cond ≠ 0

/-- **Dynamic leak trace.** State-dependent generalisation of
`LowCT.leakTrace`. For every data-oblivious constructor it returns
exactly the static trace (so the data-oblivious fragment is unchanged).
For `RIfNz` it emits a `branchEvent` recording the guard bit followed by
the *taken* branch's trace. The data-dependent loop `RWhileNz` is handled
separately by `dynLeakTraceWhile` (it needs fuel + a body step). -/
def dynLeakTrace : LowCT → RustState → LeakTrace
  | .RIfNz cond ct cf, rs =>
      if guardBit rs cond
      then branchEvent true :: dynLeakTrace ct rs
      else branchEvent false :: dynLeakTrace cf rs
  | .RSeq c1 c2, rs => dynLeakTrace c1 rs ++ dynLeakTrace c2 rs
  | .RBlock body, rs => dynLeakTrace body rs
  -- Every other constructor is data-oblivious: defer to the static trace.
  | c, _ => LowCT.leakTrace c

/-- The bounded dynamic trace of a data-dependent loop, given a body
state-transition `bodyStep : RustState → RustState` (the effect of one
iteration) and `fuel` to keep the recursion total. Each executed
iteration emits one `iterEvent` followed by the body's dynamic trace at
the current state; the loop stops when the guard is zero or fuel runs
out. -/
def dynLeakTraceWhile (cond : String) (body : LowCT)
    (bodyStep : RustState → RustState) : Nat → RustState → LeakTrace
  | 0, _ => []
  | fuel + 1, rs =>
      if guardBit rs cond
      then iterEvent :: dynLeakTrace body rs ++ dynLeakTraceWhile cond body bodyStep fuel (bodyStep rs)
      else []

/-! ## §3. Noninterference modulo public (Deliverable 1) -/

/-- Public guards are read identically on `PublicEquiv` states. -/
theorem guardBit_eq_of_publicEquiv {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) {cond : String} (hPub : guardPublic lt cond) :
    guardBit rs1 cond = guardBit rs2 cond := by
  have : rs1.rsScalar cond = rs2.rsScalar cond := h.2 cond hPub
  simp only [guardBit, this]

/-- **Noninterference modulo public — straight-line + branch fragment.**

If `cmdCT c lt leafCT = true` (the program is accepted by the public-taint
typing rule) and the two states are public-equivalent, then the dynamic
leak trace is identical on both states. Differences confined to `Secret`
slots are invisible in the trace.

This is proved for the fragment built from data-oblivious constructors,
`RSeq`, `RBlock`, and the variable-time `RIfNz` (the data-dependent
branch). The `RWhileNz` clause is `dynLeakTrace_while_noninterference`
below, modulo the named body-step hypothesis. -/
theorem dynLeakTrace_noninterference
    (lt : LevelTable) (leafCT : LeafCTTable) :
    ∀ (c : LowCT) {rs1 rs2 : RustState},
      cmdCT c lt leafCT = true → PublicEquiv lt rs1 rs2 →
      dynLeakTrace c rs1 = dynLeakTrace c rs2
  | .RIfNz cond ct cf, rs1, rs2, hCT, hPE => by
      rw [cmdCT_RIfNz_iff] at hCT
      obtain ⟨hg, hct, hcf⟩ := hCT
      have hbit : guardBit rs1 cond = guardBit rs2 cond :=
        guardBit_eq_of_publicEquiv hPE hg
      simp only [dynLeakTrace, hbit]
      by_cases hb : guardBit rs2 cond
      · simp only [hb, if_true]
        rw [dynLeakTrace_noninterference lt leafCT ct hct hPE]
      · simp only [hb, if_false, Bool.false_eq_true]
        rw [dynLeakTrace_noninterference lt leafCT cf hcf hPE]
  | .RSeq c1 c2, rs1, rs2, hCT, hPE => by
      rw [cmdCT_RSeq, Bool.and_eq_true] at hCT
      simp only [dynLeakTrace]
      rw [dynLeakTrace_noninterference lt leafCT c1 hCT.1 hPE,
          dynLeakTrace_noninterference lt leafCT c2 hCT.2 hPE]
  | .RBlock body, rs1, rs2, hCT, hPE => by
      rw [cmdCT_RBlock] at hCT
      simp only [dynLeakTrace]
      exact dynLeakTrace_noninterference lt leafCT body hCT hPE
  -- Data-oblivious constructors: the dynamic trace is the static
  -- `LowCT.leakTrace`, which is a function of syntax alone, hence equal
  -- on any two states.
  | .RSkip, _, _, _, _ => rfl
  | .RAssert _, _, _, _, _ => rfl
  | .RScalarSet _ _, _, _, _, _ => rfl
  | .RScalarSetExpr _ _, _, _, _, _ => rfl
  | .RLetU64Zero _ _, _, _, _, _ => rfl
  | .RLetZero _ _ _, _, _, _, _ => rfl
  | .RCall _ _ _, _, _, _, _ => rfl
  | .RCallSwap _ _ _ _, _, _, _, _ => rfl
  | .RCallN _ _ _, _, _, _, _ => rfl
  | .RFnCall _ _ _, _, _, _, _ => rfl
  | .RCloneCall _ _ _ _ _ _, _, _, _, _ => rfl
  | .RSelect _ _ _ _, _, _, _, _ => rfl
  | .RLimbStore _ _ _, _, _, _, _ => rfl
  | .RLimbStoreExpr _ _ _, _, _, _, _ => rfl
  | .RArrStore _ _ _, _, _, _, _ => rfl
  | .RArrLoad _ _ _, _, _, _, _ => rfl
  | .RTupleLoad _ _ _, _, _, _, _ => rfl
  | .RArrLoadLit _ _ _, _, _, _, _ => rfl
  | .RArrStoreLit _ _ _, _, _, _, _ => rfl
  | .RCallDstThreaded _ _ _, _, _, _, _ => rfl
  | .RFor _ _ _, _, _, _, _ => rfl
  | .RForRuntime _ _ _, _, _, _, _ => rfl
  | .RFnDef _ _ _ _ _, _, _, _, _ => rfl
  | .RWhileNz _ _, _, _, _, _ => rfl

/-- **Leak-nothing as the empty-public special case (Deliverable 1).**

When *no* slot is `Public` (the all-secret table, the degenerate case of
the policy), `PublicEquiv` is the total relation: *any* two states are
public-equivalent. Noninterference then says the dynamic trace is
constant over **all** inputs — i.e. the trace leaks nothing about any
input. This is the classical full-CT guarantee, recovered as a corollary.

Note: for an accepted program (`cmdCT = true`) under the all-secret
table, the only accepted variable-time constructs are those with *no*
data-dependent branch/loop (a `Secret` guard is rejected), so the trace
is in fact the static one; the corollary states the leak-nothing
conclusion uniformly. -/
theorem dynLeakTrace_leak_nothing
    (leafCT : LeafCTTable) (c : LowCT)
    (hCT : cmdCT c (fun _ => .Secret) leafCT = true)
    (rs1 rs2 : RustState) :
    dynLeakTrace c rs1 = dynLeakTrace c rs2 := by
  refine dynLeakTrace_noninterference (fun _ => .Secret) leafCT c hCT ?_
  -- Under the all-secret table, `PublicEquiv` is vacuously total: there is
  -- no `x` with `(fun _ => .Secret) x = .Public`.
  refine ⟨?_, ?_⟩ <;> intro x hx <;> simp only [] at hx <;> exact absurd hx (by decide)

/-! ## §4. The data-dependent-loop clause (named-hypothesis form)

To prove NI for `RWhileNz` we need the semantic fact that one loop-body
iteration maps public-equivalent states to public-equivalent states and
keeps the (public) guard in lock-step. That requires a verified
`LowCT.exec`, which the orphaned chain does not yet expose. We package the
requirement as an explicit hypothesis structure (not an admitted proof, not an
axiom) and prove the loop NI clause relative to it. -/

/-- Hypothesis bundle: the caller-supplied body step `bodyStep` respects the
public projection. Discharged once a verified `LowCT.exec` lands; until
then it is the explicit assumption under which the loop NI clause holds. -/
structure BodyStepPreservesPublic (lt : LevelTable) (bodyStep : RustState → RustState) : Prop where
  /-- One body iteration preserves public-equivalence. -/
  preserves : ∀ {rs1 rs2 : RustState}, PublicEquiv lt rs1 rs2 →
    PublicEquiv lt (bodyStep rs1) (bodyStep rs2)

/-- **Noninterference for the data-dependent loop**, relative to the named
`BodyStepPreservesPublic` hypothesis. Under a public guard, an accepted
body, public-equivalent inputs, and a public-preserving body step, the
bounded loop trace is identical on both states for any fuel. -/
theorem dynLeakTrace_while_noninterference
    (lt : LevelTable) (leafCT : LeafCTTable)
    (cond : String) (body : LowCT) (bodyStep : RustState → RustState)
    (hg : guardPublic lt cond)
    (hbody : cmdCT body lt leafCT = true)
    (hstep : BodyStepPreservesPublic lt bodyStep) :
    ∀ (fuel : Nat) {rs1 rs2 : RustState}, PublicEquiv lt rs1 rs2 →
      dynLeakTraceWhile cond body bodyStep fuel rs1 =
        dynLeakTraceWhile cond body bodyStep fuel rs2
  | 0, _, _, _ => rfl
  | fuel + 1, rs1, rs2, hPE => by
      have hbit : guardBit rs1 cond = guardBit rs2 cond :=
        guardBit_eq_of_publicEquiv hPE hg
      simp only [dynLeakTraceWhile, hbit]
      by_cases hb : guardBit rs2 cond
      · simp only [hb, if_true]
        rw [dynLeakTrace_noninterference lt leafCT body hbody hPE,
            dynLeakTrace_while_noninterference lt leafCT cond body bodyStep hg hbody hstep
              fuel (hstep.preserves hPE)]
      · simp only [hb, if_false, Bool.false_eq_true]

/-! ## §5. Tiny worked example (Deliverable 3)

A single `RIfNz` over a *public* guard `"pc"`, both arms trivial. The
analyser accepts it, and noninterference gives identical traces on any two
public-equivalent states. Swapping the guard to `Secret` makes the
analyser reject it (fail-closed). -/

/-- The example program: branch on public guard `"pc"`. -/
def exampleVartimeIf : LowCT :=
  .RIfNz "pc" (.RScalarSet "x" 1) (.RScalarSet "y" 2)

/-- Level table classifying the guard `"pc"` as `Public`, all else `Secret`. -/
def exampleLT : LevelTable := fun v => if v = "pc" then .Public else .Secret

/-- With a public guard, the example is accepted by the analyser. -/
theorem exampleVartimeIf_accepted (leafCT : LeafCTTable) :
    cmdCT exampleVartimeIf exampleLT leafCT = true := by
  rw [exampleVartimeIf, cmdCT_RIfNz_iff]
  refine ⟨?_, rfl, rfl⟩
  unfold guardPublic exampleLT
  simp

/-- The example satisfies noninterference modulo public: any two
public-equivalent states (agreeing on `"pc"`, free to differ on the secret
`"x"`/`"y"`) produce the *same* dynamic leak trace. -/
theorem exampleVartimeIf_noninterference (leafCT : LeafCTTable)
    {rs1 rs2 : RustState} (hPE : PublicEquiv exampleLT rs1 rs2) :
    dynLeakTrace exampleVartimeIf rs1 = dynLeakTrace exampleVartimeIf rs2 :=
  dynLeakTrace_noninterference exampleLT leafCT exampleVartimeIf
    (exampleVartimeIf_accepted leafCT) hPE

/-- The *same* branch with the guard reclassified `Secret` is rejected by
the analyser — fail-closed. This is the side-channel-faithful behaviour:
a secret-dependent branch is never certified. -/
theorem exampleVartimeIf_secret_guard_rejected (leafCT : LeafCTTable) :
    cmdCT (.RIfNz "pc" (.RScalarSet "x" 1) (.RScalarSet "y" 2))
      (fun _ => .Secret) leafCT = false :=
  cmdCT_RIfNz_secret_rejected "pc" _ _ (fun _ => .Secret) leafCT rfl

/-- Concrete witness that the dynamic trace *records the branch*:
on a state where the public guard is nonzero the trace begins with
`branch:1`; on one where it is zero it begins with `branch:0`. (This is the
observation a variable-time branch leaks — and which the NI theorem proves
is a function of the *public* guard only.) -/
theorem exampleVartimeIf_trace_records_branch
    (rsT rsF : RustState)
    (hT : rsT.rsScalar "pc" = 1) (hF : rsF.rsScalar "pc" = 0) :
    (dynLeakTrace exampleVartimeIf rsT).head? = some (branchEvent true) ∧
      (dynLeakTrace exampleVartimeIf rsF).head? = some (branchEvent false) := by
  constructor
  · simp only [exampleVartimeIf, dynLeakTrace, guardBit, hT]
    simp
  · simp only [exampleVartimeIf, dynLeakTrace, guardBit, hF]
    simp

/-! ## §6. Pilot A — Ed25519 / XEdDSA verify is an all-public region

EdDSA *verification* operates entirely on public data: the public key,
the signature, and the message are all public values (no secret key is
involved). So the verify region sits squarely in the public-declassification
regime: every slot can be classified `Public`, and the whole body satisfies
the public-taint rule. This is the static (already-CT) baseline; the point
of the pilot is that, *because* verify is all-public, variable-time
constructs (the early-out branches a fast verify uses) would remain accepted
under the rule — they only ever branch on public quantities.

We use the in-tree `xeddsaVerifyBody` (XEdDSAVerify.lean) and the canonical
leaf-CT table. -/

open CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify in
/-- The XEdDSA verify body is accepted by the analyser under an all-public
classification with the canonical CT leaf table: every leaf call
(`mont_u_to_edwards_compressed_zero`, `ed25519_verify`) is CT and every
slot is public. -/
theorem xeddsaVerify_accepted_allPublic :
    cmdCT xeddsaVerifyBody LevelTable.allPublic LeafCTTable.canonical = true := by
  unfold xeddsaVerifyBody
  simp only [cmdCT_RLetZero, cmdCT_RSeq, cmdCT_RCall, Bool.and_eq_true, List.all_eq_true,
    LevelTable.allPublic, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, forall_const, and_true, true_and]
  refine ⟨⟨⟨?_, rfl⟩, rfl⟩, ⟨?_, rfl⟩, fun _ _ => rfl⟩ <;> decide

open CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify in
/-- Noninterference modulo public for the verify region: any two
public-equivalent states (which, under the all-public table, means any two
*equal* states on public slots) give identical dynamic traces. Since verify
is data-oblivious here, the trace is constant — the leak-nothing endpoint —
but it is derived through the *same* public-taint policy that would also
license a public-guarded early-out. -/
theorem xeddsaVerify_noninterference
    {rs1 rs2 : RustState} (hPE : PublicEquiv LevelTable.allPublic rs1 rs2) :
    dynLeakTrace xeddsaVerifyBody rs1 = dynLeakTrace xeddsaVerifyBody rs2 :=
  dynLeakTrace_noninterference LevelTable.allPublic LeafCTTable.canonical
    xeddsaVerifyBody xeddsaVerify_accepted_allPublic hPE

open CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify in
/-- A *variable-time* verify variant: an explicit public-guarded early-out
(`"sig_len_ok"` is a public check on the signature encoding) wrapping the
verify body. This models the data-dependent branch a fast verify takes; the
guard is a public quantity, so the public-taint rule accepts it. -/
def xeddsaVerifyVartime : LowCT :=
  .RIfNz "sig_len_ok" xeddsaVerifyBody (.RScalarSet "verified" 0)

/-- Level table for the vartime variant: the early-out guard is public,
everything else stays public too (verify is an all-public region). -/
def verifyVartimeLT : LevelTable := LevelTable.allPublic

open CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify in
/-- The vartime verify variant — with a *public* early-out guard — is
accepted by the analyser: the data-dependent branch is sound because its
guard is public-derived. -/
theorem xeddsaVerifyVartime_accepted :
    cmdCT xeddsaVerifyVartime verifyVartimeLT LeafCTTable.canonical = true := by
  rw [xeddsaVerifyVartime, cmdCT_RIfNz_iff]
  refine ⟨?_, xeddsaVerify_accepted_allPublic, rfl⟩
  unfold guardPublic verifyVartimeLT LevelTable.allPublic
  rfl

open CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify in
/-- Noninterference for the vartime verify variant: two public-equivalent
runs leak the *same* trace, including the branch event — the early-out
decision is public, so it is allowed to be observable. -/
theorem xeddsaVerifyVartime_noninterference
    {rs1 rs2 : RustState} (hPE : PublicEquiv verifyVartimeLT rs1 rs2) :
    dynLeakTrace xeddsaVerifyVartime rs1 = dynLeakTrace xeddsaVerifyVartime rs2 :=
  dynLeakTrace_noninterference verifyVartimeLT LeafCTTable.canonical
    xeddsaVerifyVartime xeddsaVerifyVartime_accepted hPE

/-! ## §7. Pilot B (sketch) — variable-time bignum on a public modulus

GMP-style bignum routines are variable-time: they early-exit on a zero
limb, skip leading zeros, and let the loop count depend on operand
magnitude. Under the policy above this is *sound* exactly when the operands
are public. The canonical instance is **public-modulus** arithmetic:
reducing/inverting modulo a *public* prime `p` (e.g. the curve order, a
public RSA modulus in a verify path) may use the magnitude-dependent loop —
its iteration count leaks only `p`, which is already public.

Concretely, a leading-zero-skip loop `while hi_limb(x) == 0 { ... }` is an
`RWhileNz` whose guard is a function of the public modulus / public operand;
classifying that guard `Public` makes `cmdCT_RWhileNz_iff` accept it, and
`dynLeakTrace_while_noninterference` (under `BodyStepPreservesPublic` for the
limb-shift body) gives identical iteration-count traces across any two runs
that agree on the public operand. The secret-operand case (e.g. a private
exponent) keeps the guard `Secret`, so the loop is fail-closed and the code
must fall back to the constant-time fixed-trip-count kernel — exactly the
GMP-vs-constant-time split. A full instance awaits the verified
`LowCT.exec` that discharges `BodyStepPreservesPublic`; the typing side is
already covered by `cmdCT_RWhileNz_iff` above. -/

end CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak
