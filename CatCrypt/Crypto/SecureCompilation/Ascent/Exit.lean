/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileTop
public import CatCrypt.Crypto.SecureCompilation.Ascent.PipelineWeld
public import HaxLean.Ascent.Exit

/-!
# Early exit as an exception phase

A kernel whose loop body contains `break`, `continue` or an early `return` reaches
the compiler through hax-lean's control-flow encoding: `functionalizeLoops` and
`cfIntoMonads` rewrite the exits into `controlFlow`-tagged values, and
`pipeline_full_correct` states that the pipeline's evaluator `denote'` agrees with
the reference `denote` up to `Outcome.encodeCF` (`earlyRet v ↦ val (controlFlow
true v)`). This module reads that encoding as the exception monad, the way
AutoCorres's exception phase reads a `return` inside a loop.

## A. The exception reading of the encoding

This part is re-exported from hax-lean's `HaxLean/Ascent/Exit.lean`. `cfExcept` reads a control-flow-tagged value as an `Except`: the `Break` tag is the
thrown value, anything else the normal result. `outcomeExceptCF` lifts it to the
pipeline's outcomes and `outcomeExceptRaw` reads the reference outcomes (`val` is
`pure`, `earlyRet` is `throw`). `pipeline_exceptProg` is the abstraction theorem:
when the reference run of a well-scoped program is the run of an abstract program
`prog : ExceptT Value Id Value`, so is the pipeline's encoded outcome. The user
reads `prog` as a `throw`/`pure` program; the flag lives only in the encoding.

## B. The loop rule with an exception phase

`whileE C fb` is the fuel-bounded do-while in the exception monad: run the body,
continue while the abstract guard `C` holds, and let a thrown exception end the
loop with that exception (AutoCorres's `whileLoopE`, in the do-while shape
`semScalarWhile` denotes by). `CorresE` is the correspondence of a body that may
throw, over a state relation on `Except ε A` whose `.error` case describes the
concrete state after the exit flag has been lowered. `whileExit_sim` is the
simulation of the guard-driven do-while by `whileE`, over any body semantics; its
side conditions are the body correspondence, the invariant, the agreement of the
concrete guard with `C` on normal states, and the concrete guard being false on
thrown states. `corres_while_exit` instantiates it at `semScalar` and
`corresU_while_exit` at the `semU` node `RWhileNz`.

## C. Leaves at the unified waist, and the early-return word weld

`corresU_condSet` is the guarded literal write `RIfNz name (RScalarSet nv v) RSkip`
under `semU`, the flag-lowering shape a compiled early exit takes.
`haxOutcomeWordCF_pipeline_earlyRet` and `haxOutcomeWordCF_pipeline_val` weld a
raw program's output word, returned early or normally, to the pipeline output
through `haxOutcomeWordCF`.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (sgraf812/ascent).
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## A. The exception reading of the control-flow encoding

The definitions and results of this part are in hax-lean's `HaxLean/Ascent/Exit.lean`
(namespace `Hax.Ascent`), re-exported here. -/

export _root_.Hax.Ascent (cfExcept cfExcept_break outcomeExceptCF outcomeExceptRaw
  outcomeExceptRaw_val outcomeExceptRaw_earlyRet outcomeExceptCF_encodeCF pipeline_exceptProg)

/-! ## B. The loop rule with an exception phase -/

variable {ε A : Type}

/-- The fuel-bounded do-while in the exception monad: run the body, then continue
    while the abstract guard `C` holds on the result; a thrown exception ends the
    loop with that exception. At fuel `0` the loop returns its argument; the rule
    below never reaches that case, since the concrete do-while returns `none` there. -/
def whileE (C : A → Bool) (fb : A → ExceptT ε Id A) : Nat → A → ExceptT ε Id A
  | 0, a => pure a
  | k + 1, a => do
      let a' ← fb a
      if C a' then whileE C fb k a' else pure a'

/-- One trip of `whileE` whose body returns normally. -/
theorem whileE_succ_ok (C : A → Bool) (fb : A → ExceptT ε Id A) (k : Nat) (a a' : A)
    (h : (fb a).run = .ok a') :
    (whileE C fb (k + 1) a).run = if C a' then (whileE C fb k a').run else .ok a' := by
  simp only [whileE, ExceptT.run_bind, h]
  show (if C a' = true then whileE C fb k a' else pure a').run = _
  split <;> rfl

/-- One trip of `whileE` whose body throws. -/
theorem whileE_succ_error (C : A → Bool) (fb : A → ExceptT ε Id A) (k : Nat) (a : A) (e : ε)
    (h : (fb a).run = .error e) :
    (whileE C fb (k + 1) a).run = .error e := by
  simp only [whileE, ExceptT.run_bind, h]
  rfl

/-- The correspondence of a body that may throw: from a concrete state related to
    the normal abstract state `a` satisfying `P`, with the abstract guard `C a`
    true, the body makes progress under `semScalar` to a state related to
    `(fb a).run` — a normal result or a thrown exception. -/
def CorresE (SR : SEnvScalar → Except ε A → Prop) (P : A → Prop) (C : A → Bool)
    (fb : A → ExceptT ε Id A) (c : LowCT) : Prop :=
  ∀ env a, SR env (.ok a) → P a → C a = true →
    ∃ env', semScalar c env = some env' ∧ SR env' (fb a).run

/-- `CorresE` at the unified waist `semU`. -/
def CorresUE (fuel : Nat) (SR : SEnvScalar → Except ε A → Prop) (P : A → Prop)
    (C : A → Bool) (fb : A → ExceptT ε Id A) (c : LowCT) : Prop :=
  ∀ env a, SR env (.ok a) → P a → C a = true →
    ∃ env', semU fuel c env = some env' ∧ SR env' (fb a).run

/-- **The exception-phase loop simulation, over any body semantics.** The
    guard-driven do-while `semScalarWhile semBody guard` from a state related to the
    normal abstract state `a` (with `P a` and `C a`) is simulated by `whileE C fb`:
    a terminating run lands related to `(whileE C fb fuel a).run`, and when that
    result is normal it satisfies `P` and exits with `C` false. Side conditions:

    * `hbody` — one trip of the body from a normal state with the guard true lands
      related to `(fb a).run`;
    * `hinv` — a normal body result preserves `P`;
    * `hC` — on normal states the concrete guard is the abstract guard;
    * `hE` — on thrown states the concrete guard is false. -/
theorem whileExit_sim (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool)
    (SR : SEnvScalar → Except ε A → Prop) (P : A → Prop) (C : A → Bool)
    (fb : A → ExceptT ε Id A)
    (hbody : ∀ env a, SR env (.ok a) → P a → C a = true →
      ∃ env', semBody env = some env' ∧ SR env' (fb a).run)
    (hinv : ∀ a a', P a → C a = true → (fb a).run = .ok a' → P a')
    (hC : ∀ env a, SR env (.ok a) → P a → guard env = C a)
    (hE : ∀ env e, SR env (.error e) → guard env = false) :
    ∀ (fuel : Nat) (env : SEnvScalar) (a : A) (env' : SEnvScalar),
      SR env (.ok a) → P a → C a = true →
      semScalarWhile semBody guard fuel env = some env' →
      SR env' (whileE C fb fuel a).run
        ∧ ∀ a', (whileE C fb fuel a).run = .ok a' → P a' ∧ C a' = false := by
  intro fuel
  induction fuel with
  | zero => intro env a env' _ _ _ hrun; simp [semScalarWhile] at hrun
  | succ k ih =>
      intro env a env' hSR hP hCa hrun
      simp only [semScalarWhile] at hrun
      obtain ⟨b, hb, hSRb⟩ := hbody env a hSR hP hCa
      simp only [hb] at hrun
      rcases hfb : (fb a).run with e | a'
      · rw [hfb] at hSRb
        rw [hE b e hSRb] at hrun
        simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hrun
        subst hrun
        rw [whileE_succ_error C fb k a e hfb]
        exact ⟨hSRb, fun a' h => nomatch h⟩
      · rw [hfb] at hSRb
        have hP' : P a' := hinv a a' hP hCa hfb
        rw [hC b a' hSRb hP'] at hrun
        rw [whileE_succ_ok C fb k a a' hfb]
        by_cases hc : C a' = true
        · rw [if_pos hc] at hrun ⊢
          exact ih b a' env' hSRb hP' hc hrun
        · rw [if_neg hc] at hrun ⊢
          obtain rfl := Option.some.inj hrun
          refine ⟨hSRb, fun a'' h => ?_⟩
          obtain rfl := Except.ok.inj h
          exact ⟨hP', Bool.eq_false_iff.mpr hc⟩

/-- **The exception-phase `while` rule** over `semScalar`: a `CorresE` body, run as
    the guard-driven do-while, is simulated by `whileE C fb`. -/
theorem corres_while_exit (SR : SEnvScalar → Except ε A → Prop) {P : A → Prop}
    {C : A → Bool} {fb : A → ExceptT ε Id A} {body : LowCT}
    (hbody : CorresE SR P C fb body)
    (hinv : ∀ a a', P a → C a = true → (fb a).run = .ok a' → P a')
    (guard : SEnvScalar → Bool)
    (hC : ∀ env a, SR env (.ok a) → P a → guard env = C a)
    (hE : ∀ env e, SR env (.error e) → guard env = false)
    (fuel : Nat) (env : SEnvScalar) (a : A) (env' : SEnvScalar)
    (hSR : SR env (.ok a)) (hP : P a) (hCa : C a = true)
    (hrun : semScalarWhile (fun e => semScalar body e) guard fuel env = some env') :
    SR env' (whileE C fb fuel a).run
      ∧ ∀ a', (whileE C fb fuel a).run = .ok a' → P a' ∧ C a' = false :=
  whileExit_sim (fun e => semScalar body e) guard SR P C fb hbody hinv hC hE
    fuel env a env' hSR hP hCa hrun

/-- **The exception-phase `while` rule at the `RWhileNz` node.** For the loop node
    `.RWhileNz name body` at the unified waist `semU`, with the node's guard
    `guardNz name` agreeing with the abstract guard on normal states and false on
    thrown states, a terminating run is simulated by `whileE C fb`. -/
theorem corresU_while_exit (SR : SEnvScalar → Except ε A → Prop) {fuel : Nat}
    {P : A → Prop} {C : A → Bool} {fb : A → ExceptT ε Id A} {name : String} {body : LowCT}
    (hbody : CorresUE fuel SR P C fb body)
    (hinv : ∀ a a', P a → C a = true → (fb a).run = .ok a' → P a')
    (hC : ∀ env a, SR env (.ok a) → P a → guardNz name env = C a)
    (hE : ∀ env e, SR env (.error e) → guardNz name env = false)
    (env : SEnvScalar) (a : A) (env' : SEnvScalar)
    (hSR : SR env (.ok a)) (hP : P a) (hCa : C a = true)
    (hrun : semU fuel (.RWhileNz name body) env = some env') :
    SR env' (whileE C fb fuel a).run
      ∧ ∀ a', (whileE C fb fuel a).run = .ok a' → P a' ∧ C a' = false := by
  rw [semU_rWhileNz] at hrun
  exact whileExit_sim (fun e => semU fuel body e) (guardNz name) SR P C fb hbody hinv hC hE
    fuel env a env' hSR hP hCa hrun

/-! ## C. Leaves at the unified waist, and the early-return word weld -/

/-- The guarded literal write `RIfNz name (RScalarSet nv v) RSkip` at the unified
    waist, over the word relation `SRwordBV`: when the word at `name` is nonzero the
    slot `nv` is set to `v`, otherwise the environment is unchanged. This is the
    flag-lowering shape of a compiled early exit. -/
theorem corresU_condSet (fuel : Nat) (name nv : String) (v : Nat) (hname : ¬ isTmpName name) :
    CorresU fuel SRwordBV (fun _ => True)
      (fun a s => if s = nv then (if a name = 0 then a s else BitVec.ofNat 64 v) else a s)
      (.RIfNz name (.RScalarSet nv v) .RSkip) := by
  intro env a hSR _
  have hg : envReadU64 env name = some (a name) := by
    simp only [envReadU64, hSR name hname]
  by_cases hz : a name = 0
  · refine ⟨env, ?_, ?_⟩
    · simp only [semU, Dialects.TranslateDialectScalar.semScalarCond, guardNz, hg,
        Option.getD_some, hz, ne_eq, not_true_eq_false, decide_false, cond_false]
    · intro s hs
      by_cases hsv : s = nv
      · simp only [if_pos hsv, if_pos hz]; exact hSR s hs
      · simp only [if_neg hsv]; exact hSR s hs
  · refine ⟨env.upd nv (t := .sword 64) (BitVec.ofNat 64 v), ?_, ?_⟩
    · simp only [semU, Dialects.TranslateDialectScalar.semScalarCond, guardNz, hg,
        Option.getD_some, ne_eq, hz, not_false_eq_true, decide_true, cond_true, semScalar]
    · intro s hs
      by_cases hsv : s = nv
      · subst hsv
        simp only [SEnvScalar.upd, if_true, if_neg hz]
      · simp only [SEnvScalar.upd, if_neg hsv]; exact hSR s hs

/-- **The early-return word weld.** For a well-scoped raw program at the standard
    builtin table, from a control-flow-free environment: if the reference run
    returns early with a value `v` carrying the word `w`, the pipeline output read
    through `haxOutcomeWordCF` is `w`. -/
theorem haxOutcomeWordCF_pipeline_earlyRet (e : Hax.ImpExpr) (hls : Hax.LoopScoped e)
    (hnq : Hax.NoQuestionMark e) (hncf : Hax.NoCFConstructors e) (fuel : Nat) (env : Hax.Env)
    (henv : Hax.Env.NoControlFlow env) (v : Hax.Value) (w : BitVec 64)
    (hRet : (Hax.denote Hax.defaultBuiltins fuel e env).1 = .earlyRet v)
    (hw : haxOutcomeWord (.val v) = some w) :
    haxOutcomeWordCF (Hax.denote' Hax.defaultBuiltins fuel (Hax.pipeline e) env).1 = some w := by
  rw [Hax.pipeline_full_correct Hax.defaultBuiltins Hax.Builtins.defaultBuiltins_deepNoControlFlow
    e hls hnq hncf fuel env henv]
  show haxOutcomeWordCF (Hax.Outcome.encodeCF (Hax.denote Hax.defaultBuiltins fuel e env).1) = some w
  rw [hRet, haxOutcomeWordCF_encodeCF_earlyRet]
  exact hw

/-- **The normal-return word weld.** The `val` counterpart of
    `haxOutcomeWordCF_pipeline_earlyRet`: a word the reference run returns normally
    is read from the pipeline output through `haxOutcomeWordCF`. -/
theorem haxOutcomeWordCF_pipeline_val (e : Hax.ImpExpr) (hls : Hax.LoopScoped e)
    (hnq : Hax.NoQuestionMark e) (hncf : Hax.NoCFConstructors e) (fuel : Nat) (env : Hax.Env)
    (henv : Hax.Env.NoControlFlow env) (w : BitVec 64)
    (hw : haxOutcomeWord (Hax.denote Hax.defaultBuiltins fuel e env).1 = some w) :
    haxOutcomeWordCF (Hax.denote' Hax.defaultBuiltins fuel (Hax.pipeline e) env).1 = some w := by
  rw [Hax.pipeline_full_correct Hax.defaultBuiltins Hax.Builtins.defaultBuiltins_deepNoControlFlow
    e hls hnq hncf fuel env henv]
  show haxOutcomeWordCF (Hax.Outcome.encodeCF (Hax.denote Hax.defaultBuiltins fuel e env).1) = some w
  exact haxOutcomeWordCF_encodeCF _ _ (haxOutcomeWordCF_of_haxOutcomeWord _ _ hw)

end CatCrypt.Crypto.SecureCompilation.Ascent
