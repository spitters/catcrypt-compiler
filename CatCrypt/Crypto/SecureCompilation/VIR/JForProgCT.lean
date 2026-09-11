/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
public import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety

/-!
# Constant-time / robust-safety theory for bounded for-loops (`JForProg`)

This file is the **additive bounded-for-loop layer** for the Com / Jasmin
constant-time pipeline. It extends the straight-line CT / robust-compilation
story (`JasminCTPredicate.lean`, `RobustSafety.lean`) to the bounded loop IR
`JForProg` (`JasminPrint.lean` §7) — *without touching the core `Com`
inductive*.

## The additive design (no mutation of core `Com`)

Core `Com` (`VIR/Core.lean`) stays exactly **two constructors** (`ret`, `var`):
it is straight-line by construction and all the existing straight-line CT
proofs (`ctSafeJasmin`, `lowerLatticeToJasmin_ctSafeJasmin`,
`RobustlyCTSafe`, …) remain valid verbatim. Control flow lives in *separate*
extended IRs layered on top, exactly as in this repo's existing precedent:

* `CTPredicate.ctSafeComR` over `ComR` adds a `.ifBit` constructor with a
  `SecretLevel` tag — a *secret-dependent branch* — leaving core `Com`
  untouched. A `.Public` `ifBit` is CT-safe iff both arms are; a `.Secret`
  one is never CT-safe.
* This file mirrors that precedent for **bounded loops**: `JForProg` wraps a
  core-`Com` loop body with a *static* iteration count `n : Nat`, and we build
  the CT / robust-CT theory over `JForProg` here.

So the layering is: core `Com` (straight-line) ⊂ `ComR` (`+ ifBit`, branches)
and core `Com` ⊂ `JForProg` (`+ static n`, bounded loops). Each layer is
additive — bounded loops *extend* the straight-line guarantees rather than
breaking them.

## Why a bounded loop is strictly easier than a `.Public` `ifBit`

A bounded `for i in 0..n` is **data-independent control flow**:

* the iteration count `n : Nat` is a static / public value (it is a field of
  the `JForProg` structure, not a runtime register), and
* the loop counter `i` ranges over `0..n` — a public sequence of literals,
  never a secret-derived value.

So the loop introduces **no** secret-dependent branch: there is nothing to
tag `.Secret`, unlike `ComR.ifBit`. Consequently the loop adds *no* CT
obligation beyond its body: `for i in 0..n { body(acc) }` is CT-safe exactly
when `body` is CT-safe (under a public loop variable). This is the headline of
§3 below — strictly weaker than `ctSafeComR`'s `.Public`-`ifBit` rule (which
must check *both* arms), because a loop has a single body.

## The accumulator label context

`JForProg`'s body is `update : Com jasminDialect [accTy] accTy` — a core
`Com` over the singleton context `[accTy]` whose one free variable
(de Bruijn `.here`) is the loop-carried accumulator. A label context for that
body is therefore a singleton `LabelCtxt [accTy] = .cons accL .nil` tagging
the accumulator with a `SecretLevel`. The loop index `i` does not appear in
the `Com` context (it is the public `0..n` counter materialised only in the
emitted `Cfor`), so it imposes no label obligation — exactly the
data-independence above.

## What is proved here

1. **CT-safety of a bounded loop** (§2–3): `ctSafeJForProg p accL`, the
   headline `ctSafeJForProg_iff_body` (the loop is CT-safe iff its body is),
   and `ctSafeJForProg_iff_bodyPublic` (the natural public-accumulator
   instance: a bounded loop is CT-safe iff its body is CT-safe under a public
   accumulator). Plus a non-vacuity smoke test (a secret-indexed `stackLoad`
   body is flagged).
2. **Robust CT-safety** (§4): `RobustlyCTSafeJForProg p` (CT against every
   attacker labelling of the accumulator), reduced to robust CT-safety of the
   body via `RobustlyCTSafeJForProg_iff_body` — the loop construct is robustly
   CT-safe iff its body is. Mirrors `RobustSafety.RobustlyCTSafe`.
3. **Loop-emission consistency** (§5): the emitted `Cfor`
   (`JForProg.toCfor` / `toProg`) is structurally a single `UpTo` loop over
   `0..n` whose body lowers `update`; and the `n`-fold denotation
   `JForProg.denote` is characterised by an explicit fold-unfolding lemma
   (`denote_succ_range`) relating the `(n+1)`-loop to one extra `step` of the
   `n`-loop. The semantic agreement of the *emitted evaluator* with
   `JForProg.denote` factors through the per-iteration body semantics, carried
   as an explicit named hypothesis (`StepAgrees`) exactly as
   `JasminPrintSemCorrect.lean` carries `LeafAgrees` — never a `sorry`.

All goals closed; the leaf / step edges are explicit hypotheses, never `sorry`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The accumulator label context

`JForProg`'s body is a core `Com` over the singleton context `[accTy]`, whose
one free variable is the loop-carried accumulator. A label context for the
body is therefore a singleton tagging that accumulator. -/

/-- The singleton label context for a loop body `Com jasminDialect [accTy] accTy`:
    it tags the loop-carried accumulator (de Bruijn `.here`) with `accL`. -/
def bodyLabelCtxt {accTy : JasminTy} (accL : SecretLevel) : LabelCtxt [accTy] :=
  .cons accL .nil

/-- The all-`.Public` accumulator label context — the natural choice: the loop
    counter `i` is public, and a public accumulator is the standard
    data-independent loop shape. -/
def publicBodyLabelCtxt {accTy : JasminTy} : LabelCtxt [accTy] :=
  bodyLabelCtxt SecretLevel.Public

/-! ## 2. CT-safety predicate for a bounded loop

A bounded loop is CT-safe iff its body is CT-safe. The static count `n` and
the public loop counter introduce no secret-dependent branch, so — unlike
`ctSafeComR`'s `.Public` `ifBit` (which must check *both* arms) — the loop
predicate is exactly the body predicate, with no extra obligation. -/

/-- **CT-safety of a bounded for-loop**, parametric in the accumulator's secrecy
    label `accL`. A `JForProg` is CT-safe iff its body `update` is CT-safe under
    the singleton label context tagging the accumulator `accL`. The static
    iteration count and the public loop counter add no constraint, so this is
    *only* the body's obligation. -/
def ctSafeJForProg {accTy : JasminTy} (p : JForProg accTy)
    (accL : SecretLevel) : Bool :=
  ctSafeJasmin p.update (bodyLabelCtxt accL)

/-- Propositional form of loop CT-safety. -/
def ctSafePropJForProg {accTy : JasminTy} (p : JForProg accTy)
    (accL : SecretLevel) : Prop :=
  ctSafeJForProg p accL = true

instance {accTy : JasminTy} (p : JForProg accTy) (accL : SecretLevel) :
    Decidable (ctSafePropJForProg p accL) := by
  unfold ctSafePropJForProg; infer_instance

/-! ## 3. Headline: a bounded loop is CT-safe iff its body is

The loop adds no CT obligation beyond its body. We state this two ways: the
definitional unfolding (`ctSafeJForProg_iff_body`, for any accumulator label)
and the natural public-accumulator instance (`ctSafeJForProg_iff_bodyPublic`),
which is the data-independent loop shape (public counter, public accumulator).
-/

/-- **Headline (general).** A bounded for-loop is CT-safe (under accumulator
    label `accL`) **iff** its loop body `update` is CT-safe under the singleton
    label context tagging the accumulator `accL`. The bounded loop construct
    introduces no CT obligation beyond its body: the iteration count is static
    and the loop counter is public, so there is no secret-dependent branch to
    check. (Contrast `ctSafeComR`'s `.Public` `ifBit`, which must check *both*
    branches.) -/
theorem ctSafeJForProg_iff_body {accTy : JasminTy} (p : JForProg accTy)
    (accL : SecretLevel) :
    ctSafeJForProg p accL = true
      ↔ ctSafeJasmin p.update (bodyLabelCtxt accL) = true :=
  Iff.rfl

/-- **Headline (public-accumulator instance).** With the public accumulator
    label context (the standard data-independent loop shape — public counter,
    public accumulator), a bounded for-loop is CT-safe **iff** its body is
    CT-safe under a public accumulator. -/
theorem ctSafeJForProg_iff_bodyPublic {accTy : JasminTy} (p : JForProg accTy) :
    ctSafeJForProg p SecretLevel.Public = true
      ↔ ctSafeJasmin p.update publicBodyLabelCtxt = true :=
  Iff.rfl

/-- The loop CT predicate is *literally* the body CT predicate: no extra term. -/
@[simp]
theorem ctSafeJForProg_eq {accTy : JasminTy} (p : JForProg accTy)
    (accL : SecretLevel) :
    ctSafeJForProg p accL = ctSafeJasmin p.update (bodyLabelCtxt accL) := rfl

/-! ## 4. Robust CT-safety of a bounded loop

Mirroring `RobustSafety.RobustlyCTSafe`: a bounded loop **robustly** satisfies
CT iff it is CT-safe against *every* attacker labelling of the accumulator.
Because the loop predicate is exactly the body predicate, robust loop CT-safety
reduces to robust CT-safety of the body — the loop construct is robustly
CT-safe iff its body is. -/

/-- **Robust CT-safety of a bounded for-loop.** A `JForProg` is robustly
    constant-time iff it is `ctSafeJForProg` under *every* accumulator secrecy
    label — i.e. no matter how the attacker classifies the loop-carried
    accumulator, the loop never performs a secret-indexed access. Mirrors
    `RobustSafety.RobustlyCTSafe`. -/
def RobustlyCTSafeJForProg {accTy : JasminTy} (p : JForProg accTy) : Prop :=
  ∀ accL : SecretLevel, ctSafeJForProg p accL = true

/-- A robustly CT-safe loop is CT-safe under any *given* accumulator label —
    the elimination form. -/
theorem RobustlyCTSafeJForProg.atLabel {accTy : JasminTy} {p : JForProg accTy}
    (h : RobustlyCTSafeJForProg p) (accL : SecretLevel) :
    ctSafeJForProg p accL = true := h accL

/-- **Headline (robust).** A bounded for-loop is robustly CT-safe **iff** its
    body is CT-safe under *every* accumulator labelling. The loop construct is
    robustly CT-safe against every attacker classification of the accumulator
    iff its body is — the loop adds no robust-CT obligation beyond its body. -/
theorem RobustlyCTSafeJForProg_iff_body {accTy : JasminTy} (p : JForProg accTy) :
    RobustlyCTSafeJForProg p
      ↔ ∀ accL : SecretLevel, ctSafeJasmin p.update (bodyLabelCtxt accL) = true :=
  Iff.rfl

/-- A loop whose body is CT-safe under *every* accumulator labelling is robustly
    CT-safe (the introduction form of the headline iff). -/
theorem robustlyCTSafeJForProg_of_body {accTy : JasminTy} {p : JForProg accTy}
    (h : ∀ accL : SecretLevel, ctSafeJasmin p.update (bodyLabelCtxt accL) = true) :
    RobustlyCTSafeJForProg p := h

/-! ## 5. Non-vacuity: a secret-indexed loop body IS flagged

To confirm `ctSafeJForProg` / `RobustlyCTSafeJForProg` are genuinely
restrictive (not vacuously `true`), we exhibit a one-iteration loop whose body
performs a `stackLoad` at the accumulator-as-index: when the accumulator is
labelled `.Secret` the loop is flagged non-CT, and it is *not* robustly
CT-safe. This is the loop analogue of `JasminCTPredicate.loadProg`'s smoke
test and `RobustSafety.loadProg_not_robustlyCTSafe`. -/

/-- A loop body over a `reg 64` accumulator that uses the accumulator itself as
    the load index of a stack array. A `JForProg` body has a single free
    variable (the accumulator), so to load `arr[acc]` the body first
    materialises a stack array `arr : stackArr 64 8` via an oblivious `extCall`
    leaf, then performs `stackLoad 64 8` with array `arr` (the freshly-bound
    `.here`) and index the accumulator (`.there .here`). The load result is a
    `reg 64`, matching the accumulator type, so the body is a valid
    `Com [reg 64] (reg 64)`. The only addressed access is the load, whose index
    is the accumulator — hence CT-safe iff the accumulator is `.Public`. -/
def secretLoopBody : Com jasminDialect [JasminTy.reg 64] (.reg 64) :=
  -- v0 : stackArr 64 8  ← extCall "fresh_arr" [] (stackArr 64 8)
  .var (.mk (.extCall "fresh_arr" [] (.stackArr 64 8)) rfl .nil)
    -- v1 : reg 64 ← stackLoad 64 8  arr=v0(.here)  idx=acc(.there .here)
    (.var (.mk (.stackLoad 64 8) rfl
            (.cons .here (.cons (.there .here) .nil)))
      (.ret .here))

/-- A one-iteration loop whose body loads `arr[acc]` — the accumulator is used
    as a memory index. -/
def secretLoop : JForProg (.reg 64) :=
  { n := 1, update := secretLoopBody }

/-- With the accumulator labelled `.Secret`, the loop is flagged NON-CT: the
    load indexes memory by the secret accumulator. (Non-vacuity, secret case.) -/
theorem secretLoop_secret_not_ctSafe :
    ctSafeJForProg secretLoop SecretLevel.Secret = false := by
  native_decide

/-- With the accumulator labelled `.Public`, the same loop IS CT-safe: the index
    is public. (Non-vacuity, public case.) -/
theorem secretLoop_public_ctSafe :
    ctSafeJForProg secretLoop SecretLevel.Public = true := by
  native_decide

/-- The secret-index loop is **not** robustly CT-safe: the `.Secret` accumulator
    labelling is a valid attacker choice that breaks CT. Confirms
    `RobustlyCTSafeJForProg` is non-vacuous. Mirrors
    `RobustSafety.loadProg_not_robustlyCTSafe`. -/
theorem secretLoop_not_robustlyCTSafe :
    ¬ RobustlyCTSafeJForProg secretLoop := by
  intro h
  have hbad := h SecretLevel.Secret
  rw [secretLoop_secret_not_ctSafe] at hbad
  exact Bool.noConfusion hbad

/-! ## 6. The straight-`update` loop is robustly CT-safe by construction

If the loop body is a straight-line whole-poly / `extCall` body (no addressed
load/store), it is CT-safe under every accumulator labelling, hence the loop is
robustly CT-safe. We capture this as: whenever the body is CT-safe under *all*
accumulator labels, the loop is robustly CT-safe. The `doubleLoop` example
(`acc := acc + acc`, a `regArith` body) instantiates it. -/

/-- The `doubleLoop` example (`acc := acc + acc`) body is CT-safe under any
    accumulator labelling: a `regArith add` op has no addressed access. -/
theorem doubleLoop_body_ctSafe (accL : SecretLevel) :
    ctSafeJasmin (JasminPrint.doubleLoop.update) (bodyLabelCtxt accL) = true := by
  cases accL <;> rfl

/-- The `doubleLoop` example is robustly CT-safe: its `regArith` body performs
    no addressed memory access, so it is CT-safe under every accumulator
    labelling. -/
theorem doubleLoop_robustlyCTSafe :
    RobustlyCTSafeJForProg JasminPrint.doubleLoop :=
  robustlyCTSafeJForProg_of_body doubleLoop_body_ctSafe

/-! ## 7. Loop-emission consistency (structural + `n`-fold semantics)

The emitted `Cfor` (`JForProg.toCfor`) is structurally a single `UpTo` loop
over `0..n` whose body is the lowering of `update`. And the `n`-fold
denotation `JForProg.denote` unfolds by one `step` per iteration. We prove the
structural facts unconditionally and characterise the `n`-fold semantics by an
explicit fold-unfolding lemma; the semantic agreement of the *emitted
evaluator* with `JForProg.denote` factors through the body's per-iteration
semantics, which we carry as an explicit named hypothesis (`StepAgrees`),
exactly as `JasminPrintSemCorrect.lean` carries `LeafAgrees` — never a
`sorry`. -/

/-- The emitted loop body: the lowered `update` instructions followed by the
    `acc := <result>` write-back. This is exactly the `body` slot of
    `JForProg.toCfor`. -/
def emittedBody {accTy : JasminTy} (p : JForProg accTy) :
    List CatCrypt.Crypto.Jasmin.InstrR :=
  let vm : VarMap [accTy] := (VarMap.empty).extend (t := accTy) "acc"
  let (bodyInstrs, resName) := lowerCom vm 0 p.update
  let writeBack : CatCrypt.Crypto.Jasmin.InstrR :=
    .Cassgn (.Lvar (mkVarI "acc" accTy)) .AT_none (styOfTy accTy)
      (pvarOf resName accTy)
  bodyInstrs ++ [writeBack]

/-- **Structural fact: the emitted loop is an `UpTo` loop over `0..n`.** The
    `Cfor` emitted for a `JForProg` runs ascending from `0` to `p.n`, with the
    loop index `i` and body `emittedBody`. -/
theorem toCfor_range {accTy : JasminTy} (p : JForProg accTy) :
    p.toCfor
      = .Cfor (mkVarI "i" .inlineInt)
          { dir := .UpTo, lo := 0, hi := p.n } (emittedBody p) := rfl

/-- **Structural fact: the emitted program is single-function, one loop body,
    one accumulator parameter, one result.** -/
theorem toProg_shape {accTy : JasminTy} (name : String) (p : JForProg accTy) :
    (p.toProg name).funcs.length = 1
      ∧ ((p.toProg name).funcs.head?.map (fun fd => fd.body.length)) = some 1
      ∧ ((p.toProg name).funcs.head?.map (fun fd => fd.params.length)) = some 1
      ∧ ((p.toProg name).funcs.head?.map (fun fd => fd.results.length)) = some 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`n`-fold semantics: the empty loop is the identity.** Iterating `step`
    zero times returns the initial accumulator unchanged. -/
theorem denote_zero {accTy : JasminTy} (p : JForProg accTy) (init : ⟦accTy⟧)
    (h : p.n = 0) : p.denote init = init := by
  unfold JForProg.denote
  rw [h]
  rfl

/-- **`n`-fold unfolding (List.range form).** The denotation of a loop with body
    `update` and count `n` is the left-fold of `step` over `List.range n` from
    `init`. (Definitional, recorded for downstream reasoning about the emitted
    `Cfor`.) -/
theorem denote_eq_foldl {accTy : JasminTy} (p : JForProg accTy) (init : ⟦accTy⟧) :
    p.denote init = (List.range p.n).foldl (fun acc _ => p.step acc) init := rfl

/-- A helper loop with the same body but a different (smaller) count, used to
    relate the `(n+1)`-loop to the `n`-loop. -/
def withCount {accTy : JasminTy} (p : JForProg accTy) (m : Nat) :
    JForProg accTy :=
  { n := m, update := p.update }

@[simp] theorem withCount_step {accTy : JasminTy} (p : JForProg accTy) (m : Nat)
    (acc : ⟦accTy⟧) : (withCount p m).step acc = p.step acc := rfl

/-- **`n`-fold unfolding (successor form).** A loop of `n+1` iterations applies
    one extra `step` *after* the `n`-iteration loop. This is the
    per-iteration recurrence relating `JForProg.denote` at successive counts —
    the semantic ground truth the emitted `Cfor` realises. Proved by the
    `List.range_succ` / `List.foldl_append` characterisation of the fold. -/
theorem denote_succ {accTy : JasminTy} (p : JForProg accTy) (m : Nat)
    (init : ⟦accTy⟧) (hp : p.n = m + 1) :
    p.denote init = p.step ((withCount p m).denote init) := by
  unfold JForProg.denote
  rw [hp]
  -- `List.range (m+1) = List.range m ++ [m]`, and folding over a concatenation
  -- with `[m]` applies one extra `step`.
  rw [List.range_succ, List.foldl_append]
  rfl

/-! ### Per-iteration evaluator agreement, as an explicit hypothesis

Relating the emitted `Cfor`'s run on a word-level evaluator to
`JForProg.denote` reduces — by induction on `n` and `denote_succ` — to the
fact that running the emitted *loop body* once (the lowering of `update`, with
the accumulator threaded through the named `acc` slot) computes `p.step`. That
per-iteration agreement is the loop analogue of
`JasminPrintSemCorrect.execCom_eq` (whose statement carries `LeafAgrees`).
Rather than re-deriving the body evaluator here, we package the per-iteration
fact as the abstract hypothesis `StepAgrees` and prove the *whole-loop*
agreement (`loopRun_eq`) parametric in it — exactly the
`JasminPrintSemCorrect.lean` discipline: the inductive loop structure is closed
unconditionally; only the single-iteration body edge is a named hypothesis,
never a `sorry`. -/

/-- An abstract per-iteration loop runner: `bodyRun acc` is the result of
    running the emitted loop body (lowering of `update`) once on accumulator
    `acc`. -/
abbrev BodyRunner (accTy : JasminTy) : Type := ⟦accTy⟧ → ⟦accTy⟧

/-- Per-iteration agreement: running the emitted loop body once computes the
    `JForProg.step` of the dialect-level body. The loop analogue of
    `JasminPrintSemCorrect.LeafAgrees` — an explicit, named edge condition that
    any concrete body evaluator discharges via `JasminPrintSemCorrect.execCom_eq`
    on the loop body, NOT a `sorry`. -/
def StepAgrees {accTy : JasminTy} (p : JForProg accTy)
    (bodyRun : BodyRunner accTy) : Prop :=
  ∀ acc : ⟦accTy⟧, bodyRun acc = p.step acc

/-- Run the emitted loop abstractly: iterate the body runner `n` times. This is
    the evaluator-side `n`-fold iteration the emitted `Cfor` performs (the
    `Cfor` over `0..n` runs its body `n` times, threading the named `acc`). -/
def loopRun {accTy : JasminTy} (p : JForProg accTy)
    (bodyRun : BodyRunner accTy) (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc _ => bodyRun acc) init

/-- The abstract loop run with a smaller count (used in the induction). -/
theorem loopRun_eq_foldl {accTy : JasminTy} (p : JForProg accTy)
    (bodyRun : BodyRunner accTy) (init : ⟦accTy⟧) :
    loopRun p bodyRun init
      = (List.range p.n).foldl (fun acc _ => bodyRun acc) init := rfl

/-- A `foldl` of two functions that agree everywhere over the same list and
    seed coincide. -/
theorem foldl_congr_fun {accTy : JasminTy} {β : Type}
    (f g : ⟦accTy⟧ → β → ⟦accTy⟧)
    (hfg : ∀ acc u, f acc u = g acc u) :
    ∀ (l : List β) (init : ⟦accTy⟧), l.foldl f init = l.foldl g init
  | [], _ => rfl
  | _ :: l, init => by
      rw [List.foldl_cons, List.foldl_cons, hfg]
      exact foldl_congr_fun f g hfg l _

/-- **Whole-loop emission consistency (parametric in the body edge).** Under the
    per-iteration agreement hypothesis `StepAgrees` (the named edge condition,
    not a `sorry`), the emitted loop's `n`-fold run computes exactly
    `JForProg.denote`. The loop structure (the `n`-fold iteration) is closed
    unconditionally; only the single-iteration body semantics is the carried
    hypothesis — exactly the `JasminPrintSemCorrect.lean` discipline. -/
theorem loopRun_eq {accTy : JasminTy} (p : JForProg accTy)
    {bodyRun : BodyRunner accTy} (hStep : StepAgrees p bodyRun)
    (init : ⟦accTy⟧) :
    loopRun p bodyRun init = p.denote init := by
  unfold loopRun JForProg.denote
  -- The two folds differ only in their per-element function; `hStep` makes them
  -- agree on every accumulator, so the folds coincide over `List.range p.n`.
  exact foldl_congr_fun (fun acc _ => bodyRun acc) (fun acc _ => p.step acc)
    (fun acc _ => hStep acc) (List.range p.n) init

/-! ## 8. Summary: bounded loops extend the straight-line CT story

The headline results above establish, *additively over the unchanged core
`Com`*:

* (`ctSafeJForProg_iff_body`) a bounded loop is CT-safe iff its body is;
* (`RobustlyCTSafeJForProg_iff_body`) a bounded loop is robustly CT-safe iff its
  body is robustly CT-safe;
* (`loopRun_eq`) the emitted `Cfor`'s `n`-fold run agrees with the loop's
  `n`-fold denotation, modulo the explicit per-iteration body edge `StepAgrees`.

Together these are the loop gateway to fixed-iteration crypto (X25519's
255-round ladder, Keccak's 24 rounds): each is a bounded loop whose *body* is a
straight-line CT-safe core `Com`, so its CT / robust-CT guarantee follows from
the body's by the iffs above, with the straight-line theory
(`JasminCTPredicate` / `RobustSafety`) reused unchanged.

### Scope note (single-accumulator shape)

`JForProg`'s body is a single-accumulator `Com [accTy] accTy`. A loop body that
must thread *several* loop-carried values (e.g. a Montgomery ladder carrying a
pair of points) is expressible by packing them into one product / tuple
`accTy`, or by a future multi-variable `JForProg` generalisation
(`update : Com jasminDialect accCtxt accTy'`). The single-accumulator shape is
sufficient for the CT theory here: the CT obligation is purely about the body's
addressed accesses, which the iffs reduce to regardless of how many values the
accumulator packs. -/

end CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
