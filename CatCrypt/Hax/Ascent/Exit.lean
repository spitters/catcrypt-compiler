/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.PipelineCF
public import CatCrypt.Hax.Ascent.Refines

/-!
# Early exit as an exception phase over the hax pipeline

`functionalizeLoops` and `cfIntoMonads` rewrite `break`, `continue` and an early
`return` into `controlFlow`-tagged values, and `pipeline_full_correct` states that the
pipeline's evaluator `denote'` agrees with the reference `denote` up to
`Outcome.encodeCF` (`earlyRet v ↦ val (controlFlow true v)`). This module reads that
encoding as the exception monad, the way AutoCorres's exception phase reads a `return`
inside a loop, and picks the weakest result monad for a hax source program.

## The exception reading of the encoding

`cfExcept` reads a control-flow-tagged value as an `Except`: the `Break` tag is the
thrown value, anything else the normal result. `outcomeExceptCF` lifts it to the
pipeline's outcomes and `outcomeExceptRaw` reads the reference outcomes (`val` is
`pure`, `earlyRet` is `throw`). `pipeline_exceptProg` is the abstraction theorem: when
the reference run of a well-scoped program is the run of an abstract program
`prog : ExceptT Value Id Value`, so is the pipeline's encoded outcome.

## Type strengthening of a hax source program

`tsHax bi fuel e` abstracts a raw program whose pipeline output `pipeline e` encodes
early exits as control-flow tags. The exception program is the exception reading of the
reference run, `haxExceptAbs`; its refinement of the pipeline's encoded outcome is
`haxExceptAbs_refines`. The pass picks the `Option` level when `checkNoEarlyExit e`
holds and the exception level otherwise. `denote_ne_earlyRet` proves that a program
passing the check never returns early, so on those programs the `Option` program is the
exception program (`tsHax_toExcept`). A fuel-bounded reference run fails on fuel
exhaustion and on ill-typed values, so the pass never picks the pure level.

## Main definitions and results

* `cfExcept`, `outcomeExceptCF`, `outcomeExceptRaw`, `pipeline_exceptProg`
* `NotEarlyRet`, `denote_notEarlyRet_mutual`, `denote_ne_earlyRet`
* `haxExceptAbs`, `haxPipelineSem`, `haxEntry`, `tsHaxLevel`, `tsHax`, `tsHax_sound`,
  `tsHax_toExcept`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## The exception reading of the control-flow encoding -/

/-- The exception reading of a control-flow-encoded value: the `Break` tag
    `controlFlow true w` is the thrown value `w`; any other value is the normal
    result. -/
def cfExcept : Hax.Value → Except Hax.Value Hax.Value
  | .controlFlow true w => .error w
  | v => .ok v

@[simp] theorem cfExcept_break (w : Hax.Value) :
    cfExcept (.controlFlow true w) = .error w := rfl

/-- The exception reading of a pipeline outcome: a `val` reads through `cfExcept`;
    any other outcome has no reading. -/
def outcomeExceptCF : Hax.Outcome → Option (Except Hax.Value Hax.Value)
  | .val v => some (cfExcept v)
  | _ => none

/-- The exception reading of a reference outcome: a `val` that is not
    control-flow-tagged is the normal result, an `earlyRet` is the thrown value, and
    every other outcome (a loop-scoped `broke`/`continued`, an error) has no
    reading. -/
def outcomeExceptRaw : Hax.Outcome → Option (Except Hax.Value Hax.Value)
  | .val v => if v.isControlFlow then none else some (.ok v)
  | .earlyRet v => some (.error v)
  | _ => none

/-- A normal reference outcome reads as `pure`. -/
theorem outcomeExceptRaw_val (v : Hax.Value) (hv : v.isControlFlow = false) :
    outcomeExceptRaw (.val v) = some (pure v : ExceptT Hax.Value Id Hax.Value).run := by
  simp [outcomeExceptRaw, hv]; rfl

/-- An early return reads as `throw`. -/
theorem outcomeExceptRaw_earlyRet (v : Hax.Value) :
    outcomeExceptRaw (.earlyRet v) = some (throw v : ExceptT Hax.Value Id Hax.Value).run := rfl

/-- The encoding commutes with the two readings: whenever the reference outcome has
    a reading, the encoded outcome has the same reading. -/
theorem outcomeExceptCF_encodeCF (o : Hax.Outcome) (r : Except Hax.Value Hax.Value)
    (h : outcomeExceptRaw o = some r) :
    outcomeExceptCF (Hax.Outcome.encodeCF o) = some r := by
  cases o with
  | val v =>
      cases v with
      | controlFlow b w => simp [outcomeExceptRaw] at h
      | _ => simp [outcomeExceptRaw] at h; subst h; rfl
  | earlyRet v => simp [outcomeExceptRaw] at h; subst h; rfl
  | broke v => simp [outcomeExceptRaw] at h
  | continued => simp [outcomeExceptRaw] at h
  | err msg => simp [outcomeExceptRaw] at h

/-- **The exception-phase abstraction.** For a well-scoped program `e` (loop-scoped,
    without `?`, without fold constructors) and a control-flow-free entry
    environment, if the reference run of `e` is the run of the abstract exception
    program `prog`, then the pipeline's encoded outcome, read through
    `outcomeExceptCF`, is the run of the same `prog`. -/
theorem pipeline_exceptProg (bi : Hax.Builtins) (hbi : Hax.Builtins.DeepNoControlFlow bi)
    (e : Hax.ImpExpr) (hls : Hax.LoopScoped e) (hnq : Hax.NoQuestionMark e)
    (hncf : Hax.NoCFConstructors e) (fuel : Nat) (env : Hax.Env)
    (henv : Hax.Env.NoControlFlow env) (prog : ExceptT Hax.Value Id Hax.Value)
    (h : outcomeExceptRaw (Hax.denote bi fuel e env).1 = some prog.run) :
    outcomeExceptCF (Hax.denote' bi fuel (Hax.pipeline e) env).1 = some prog.run := by
  rw [Hax.pipeline_full_correct bi hbi e hls hnq hncf fuel env henv]
  exact outcomeExceptCF_encodeCF _ _ h

/-! ## A hax source program never returning early -/

/-- The run does not end in an early return. -/
def NotEarlyRet (p : Hax.Outcome × Hax.Env) : Prop := ∀ v s, p ≠ (.earlyRet v, s)

set_option linter.unusedSimpArgs false in
/-- The reference evaluator and its helpers never end in an early return on a program
    passing `Hax.checkNoEarlyExit`, stated for the six functions of the mutual block. -/
theorem denote_notEarlyRet_mutual (bi : Hax.Builtins) :
    (∀ fuel e env, Hax.checkNoEarlyExit e = true → NotEarlyRet (Hax.denote bi fuel e env)) ∧
    (∀ fuel cond body env, (Hax.checkNoEarlyExit cond && Hax.checkNoEarlyExit body) = true →
      NotEarlyRet (Hax.denoteWhile bi fuel cond body env)) ∧
    (∀ fuel var lo hi body env, Hax.checkNoEarlyExit body = true →
      NotEarlyRet (Hax.denoteForLoopRev bi fuel var lo hi body env)) ∧
    (∀ fuel var lo hi body env, Hax.checkNoEarlyExit body = true →
      NotEarlyRet (Hax.denoteForLoop bi fuel var lo hi body env)) ∧
    (∀ fuel v arms env, Hax.checkNoEarlyExit.checkNoEarlyExitArms arms = true →
      NotEarlyRet (Hax.denoteMatchArms bi fuel v arms env)) ∧
    (∀ (_ : Nat) (_ : List Hax.ImpExpr), True) := by
  refine Hax.denote.mutual_induct
    (motive1 := fun fuel e => ∀ env, Hax.checkNoEarlyExit e = true →
      NotEarlyRet (Hax.denote bi fuel e env))
    (motive2 := fun fuel cond body => ∀ env,
      (Hax.checkNoEarlyExit cond && Hax.checkNoEarlyExit body) = true →
      NotEarlyRet (Hax.denoteWhile bi fuel cond body env))
    (motive3 := fun fuel var lo hi body => ∀ env, Hax.checkNoEarlyExit body = true →
      NotEarlyRet (Hax.denoteForLoopRev bi fuel var lo hi body env))
    (motive4 := fun fuel var lo hi body => ∀ env, Hax.checkNoEarlyExit body = true →
      NotEarlyRet (Hax.denoteForLoop bi fuel var lo hi body env))
    (motive5 := fun fuel v arms => ∀ env, Hax.checkNoEarlyExit.checkNoEarlyExitArms arms = true →
      NotEarlyRet (Hax.denoteMatchArms bi fuel v arms env))
    (motive6 := fun _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals try trivial
  all_goals
    rename_i h
    try simp only [Hax.checkNoEarlyExit, Hax.checkNoEarlyExit.checkNoEarlyExitArms,
      Bool.and_eq_true] at h
    unfold NotEarlyRet at *
    intro w s'
    first
      | (unfold Hax.denote) | (unfold Hax.denoteWhile) | (unfold Hax.denoteForLoop)
      | (unfold Hax.denoteForLoopRev) | (unfold Hax.denoteMatchArms)
    repeat' (first
      | (simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
          MonadStateOf.set, pure, StateT.pure, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet])
      | split)
  all_goals first
    | done
    | (simp_all; done)
    | (intro hc; simp only [Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; simp_all)
    | skip
  -- The four goals whose `match` is applied to the state, which `split` does not
  -- reach: the variable read, the builtin call, the projection, the match arm.
  · rename_i name env
    cases env name <;> simp [StateT.pure, pure]
  · rename_i f _ _ _ _ _ _ vals _
    cases bi f vals <;> simp [StateT.pure, pure]
  · rename_i i _ _ _ _ _ v _
    cases v.projIdx i <;> simp [StateT.pure, pure]
  · rename_i v pat _ _ ih2 ih1 env
    cases Hax.matchPat pat v env with
    | none => exact ih1 env h.2 w s'
    | some env' => exact ih2 env' h.1 w s'

/-- **A program without `return` or `?` never returns early.** On a program passing
    `Hax.checkNoEarlyExit`, the reference run never ends in `earlyRet`. -/
theorem denote_ne_earlyRet (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr) (env : Hax.Env)
    (h : Hax.checkNoEarlyExit e = true) (v : Hax.Value) (s : Hax.Env) :
    Hax.denote bi fuel e env ≠ (.earlyRet v, s) :=
  (denote_notEarlyRet_mutual bi).1 fuel e env h v s

/-! ## The pass on a hax source program -/

/-- The exception reading of the reference run of `e` from the entry environment: a
    normal value is `.ok`, an early return is `.error`, any other outcome has no
    reading. -/
def haxExceptAbs (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr) :
    Hax.Env → Option (Except Hax.Value Hax.Value) :=
  fun env => outcomeExceptRaw (Hax.denote bi fuel e env).1

/-- The pipeline's run of `e` from the entry environment, its outcome read through the
    control-flow encoding. -/
def haxPipelineSem (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr) :
    Hax.Env → Option (Except Hax.Value Hax.Value) :=
  fun env => outcomeExceptCF (Hax.denote' bi fuel (Hax.pipeline e) env).1

/-- The entry relation of a hax program: the same environment, free of control-flow
    values. -/
def haxEntry (c a : Hax.Env) : Prop := c = a ∧ Hax.Env.NoControlFlow a

/-- The exception program refines the pipeline's encoded run, for a well-scoped
    program under a builtin table that never produces a control-flow value. -/
theorem haxExceptAbs_refines (bi : Hax.Builtins) (hbi : Hax.Builtins.DeepNoControlFlow bi)
    (e : Hax.ImpExpr) (hls : Hax.LoopScoped e) (hnq : Hax.NoQuestionMark e)
    (hncf : Hax.NoCFConstructors e) (fuel : Nat) :
    RefinesO (haxPipelineSem bi fuel e) haxEntry (fun d r => d = r) (haxExceptAbs bi fuel e) := by
  rintro env _ r ⟨rfl, henv⟩ hr
  exact ⟨r, pipeline_exceptProg bi hbi e hls hnq hncf fuel env henv (ExceptT.mk r) hr, rfl⟩

/-- On a program passing `Hax.checkNoEarlyExit`, the exception program never throws. -/
theorem haxExceptAbs_noThrow (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr)
    (h : Hax.checkNoEarlyExit e = true) (env : Hax.Env) (err : Hax.Value) :
    haxExceptAbs bi fuel e env ≠ some (.error err) := by
  intro hc
  simp only [haxExceptAbs] at hc
  rcases hd : Hax.denote bi fuel e env with ⟨o, s⟩
  rw [hd] at hc
  cases o with
  | earlyRet v => exact denote_ne_earlyRet bi fuel e env h v s hd
  | val v =>
      simp only [outcomeExceptRaw] at hc
      split at hc <;> simp at hc
  | broke v => simp [outcomeExceptRaw] at hc
  | continued => simp [outcomeExceptRaw] at hc
  | err msg => simp [outcomeExceptRaw] at hc

/-- The level `tsHax` picks: `Option` on a program without `return` or `?`,
    exception otherwise. -/
def tsHaxLevel (e : Hax.ImpExpr) : MonadLevel :=
  if Hax.checkNoEarlyExit e then .option else .except

/-- The abstract program of a hax source at the weakest fitting level: the normal
    results of `haxExceptAbs` as an `Option` program on a program without `return` or
    `?`, `haxExceptAbs` itself otherwise. -/
def tsHax (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr) :
    AbsProg Hax.Value Hax.Env Hax.Value :=
  if Hax.checkNoEarlyExit e then .option (exceptOk (haxExceptAbs bi fuel e))
  else .except (haxExceptAbs bi fuel e)

theorem tsHax_level (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr) :
    (tsHax bi fuel e).level = tsHaxLevel e := by
  unfold tsHax tsHaxLevel
  split <;> rfl

/-- **Soundness of the pass on a hax source.** The abstract program `tsHax` refines
    the pipeline's encoded run at its own level. -/
theorem tsHax_sound (bi : Hax.Builtins) (hbi : Hax.Builtins.DeepNoControlFlow bi)
    (e : Hax.ImpExpr) (hls : Hax.LoopScoped e) (hnq : Hax.NoQuestionMark e)
    (hncf : Hax.NoCFConstructors e) (fuel : Nat) :
    (tsHax bi fuel e).Refines (haxPipelineSem bi fuel e) haxEntry (fun d r => d = r) := by
  have hx := haxExceptAbs_refines bi hbi e hls hnq hncf fuel
  unfold tsHax
  split
  · exact refinesO_exceptOk _ _ _ _ hx
  · exact hx

/-- **The `Option` choice loses nothing.** On a program passing
    `Hax.checkNoEarlyExit`, the exception image of the `Option` program is the
    exception program. -/
theorem tsHax_toExcept (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr)
    (h : Hax.checkNoEarlyExit e = true) :
    (tsHax bi fuel e).toExcept = haxExceptAbs bi fuel e := by
  unfold tsHax
  rw [if_pos h]
  funext env
  exact exceptOk_mapOk_of_noThrow _ (haxExceptAbs_noThrow bi fuel e h) env

end Hax.Ascent
