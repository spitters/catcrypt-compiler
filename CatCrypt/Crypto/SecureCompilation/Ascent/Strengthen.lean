/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Guards
public import CatCrypt.Crypto.SecureCompilation.Ascent.Exit

/-!
# Type strengthening: the weakest fitting result monad

The pass of this module picks, for a program the ascent abstracts, the lowest of the
three result monads of `Ascent/Phases.lean` (`MonadLevel`: pure, `Option`,
exception) in which the abstract program is stated, and produces the abstract
program at that level (`AbsProg`) with its refinement theorem. AutoCorres's
TypeStrengthen is the model: try pure, then option, then exception. The lifting
lemmas of `Phases.lean` (`AbsProg.refines_lift_iff`, `AbsProg.refines_iff_toExcept`)
turn a program stated at a lower level into the same correspondence one level up.

## A `LowCT` command

`tsLowCTL L fuel c` reads the guards of the total abstraction `ascendGL L fuel c` over
the array layout `L`, and `tsLowCT` is its instance at the empty layout:

* a guard with an `unsupported` node anywhere: no abstract program (`none`);
* every guard statically true (`Guard.trivialB`): the pure transformer;
* otherwise: the `Option` program `optGuard (guardsHold gs) f`, failing exactly when a
  guard fails on the store.

A guard is statically true when it is an `assert`, a `range` guard whose expression
cannot leave `u64` range on a word store (`rangeTrivialB`: variables, literals below
`2 ^ 64`, the bitwise and signed/widening nodes, and a right shift by a literal below
`64`), or a pull-back of a statically true guard. `tsLowCTL_sound` states the
correspondence at the unified waist `semU fuel c` over `SRwordL L`, and
`tsLowCTL_sound_scalar` at `semScalar` on a loop-free command; `tsLowCT_sound` and
`tsLowCT_sound_scalar` are the same over `SRwordNT`. `arrSelK_tsLowCTL` abstracts the
array kernel `arrSelK` of `Guards.lean` at the pure level. A `LowCT` command has
no exit construct, so the pass never picks the exception level for it; the
exception-level body relation of the loop rule of `Ascent/Exit.lean` is
`corresUE_iff_refinesO`.

## A hax source program

`tsHax bi fuel e` abstracts a raw hax-lean program whose pipeline output
`Hax.pipeline e` encodes early exits as control-flow tags. The exception program is
the exception reading of the reference run, `haxExceptAbs`; its refinement of the
pipeline's encoded outcome is `haxExceptAbs_refines` (`pipeline_exceptProg`). The
pass picks the `Option` level when `Hax.checkNoEarlyExit e` holds and the exception
level otherwise. `denote_ne_earlyRet` proves that a program passing the check never
returns early, so on those programs the `Option` program is the exception program
(`tsHax_toExcept`). A fuel-bounded reference run fails on fuel exhaustion and on
ill-typed values, so the pass never picks the pure level for a hax source.

## Main definitions and results

* `rangeTrivialB`, `Guard.trivialB`, `Guard.unsupportedB` — the static guard analysis
* `tsLevelLowCTL`, `tsLowCTL`, `tsLowCTL_sound`, `tsLowCTL_sound_scalar`,
  `tsLowCTL_isSome_iff`, and their empty-layout instances `tsLevelLowCT`, `tsLowCT`,
  `tsLowCT_sound`, `tsLowCT_sound_scalar`, `tsLowCT_isSome_iff`
* `denote_ne_earlyRet` — a program without `return` or `?` never returns early
* `haxExceptAbs`, `haxPipelineSem`, `tsHaxLevel`, `tsHax`, `tsHax_sound`, `tsHax_toExcept`
* `Kernel`, `Kernel.tsLevel` — the choice over both program kinds

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (sgraf812/ascent).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## Generic facts on the three levels -/

section Generic

variable {C D A B ε : Type}

/-- The output relation of the exception level induced by a relation on normal
    results: `.ok b` is related as `b`, a thrown value is related to nothing. -/
def liftOk (SR : D → B → Prop) : D → Except ε B → Prop
  | d, .ok b => SR d b
  | _, .error _ => False

/-- The normal results of a refining exception program refine at the `Option`
    level. -/
theorem refinesO_exceptOk (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → Except ε B → Prop) (f : A → Option (Except ε B))
    (h : RefinesO sem SRin SRout f) :
    RefinesO sem SRin (fun d b => SRout d (.ok b)) (exceptOk f) := by
  intro c a b hSR hf
  unfold exceptOk at hf
  rcases hfa : f a with _ | (e | b')
  · rw [hfa] at hf; exact absurd hf (by simp)
  · rw [hfa] at hf; exact absurd hf (by simp)
  · rw [hfa, Option.some.injEq] at hf
    subst hf
    exact h c a (.ok b') hSR hfa

end Generic

/-! ## The unified-waist relations as instances -/

/-- `CorresU` is `RefinesP` at the concrete semantics `semU fuel c`. -/
theorem corresU_iff_refinesP {AState : Type} (fuel : Nat) (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) :
    CorresU fuel SR P fa c ↔ RefinesP (fun env => semU fuel c env) SR SR P fa := Iff.rfl

/-- The exception-level body relation `CorresUE` of the loop rule is the `Option`
    refinement, at `semU fuel c`, of the body step guarded by `P a ∧ C a`. -/
theorem corresUE_iff_refinesO {ε A : Type} (fuel : Nat) (SR : SEnvScalar → Except ε A → Prop)
    (P : A → Prop) [DecidablePred P] (C : A → Bool) (fb : A → ExceptT ε Id A) (c : LowCT) :
    CorresUE fuel SR P C fb c ↔
      RefinesO (fun env => semU fuel c env) (fun env a => SR env (.ok a)) SR
        (optGuard (fun a => P a ∧ C a = true) (fun a => (fb a).run)) := by
  rw [← refinesP_iff_refinesO_guard]
  constructor
  · intro h env a hSR hPC
    exact h env a hSR hPC.1 hPC.2
  · intro h env a hSR hP hC
    exact h env a hSR ⟨hP, hC⟩

/-! ## Static guard analysis -/

/-- The expression cannot leave `u64` range on a store of `u64` values: variables,
    literals below `2 ^ 64`, the nodes whose range condition is only the range of
    their operands, and a right shift by a literal below `64`. -/
def rangeTrivialB : SExpr → Bool
  | .SVar _ => true
  | .SLit n => litOkB n
  | .SAnd a b | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b
  | .SMulHiS a b => rangeTrivialB a && rangeTrivialB b
  | .SShr a (.SLit k) => rangeTrivialB a && decide (k < 64)
  | .SLimb _ _ => true
  | _ => false

theorem rangeTrivialB_sound {σ : String → Nat} (hσ : ∀ x, σ x < 2 ^ 64) :
    ∀ e : SExpr, rangeTrivialB e = true → e.inRange σ
  | .SVar x, _ => hσ x
  | .SLit n, h => by simpa [rangeTrivialB, litOkB, SExpr.inRange] using h
  | .SAnd a b, h | .SXor a b, h | .SLt a b, h | .SAsr a b, h | .SMulS a b, h
  | .SMulHiU a b, h | .SMulHiS a b, h => by
      simp only [rangeTrivialB, Bool.and_eq_true] at h
      exact ⟨rangeTrivialB_sound hσ a h.1, rangeTrivialB_sound hσ b h.2⟩
  | .SShr a b, h => by
      cases b with
      | SLit k =>
          simp only [rangeTrivialB, Bool.and_eq_true, decide_eq_true_eq] at h
          refine ⟨rangeTrivialB_sound hσ a h.1, ?_, ?_⟩
          · show k < 2 ^ 64
            omega
          · exact h.2
      | _ => simp [rangeTrivialB] at h
  | .SLimb _ _, _ => trivial
  | .SAdd _ _, h | .SSub _ _, h | .SMul _ _, h | .SShl _ _, h => by simp [rangeTrivialB] at h

/-- Every value of the Nat view of a word store is below `2 ^ 64`. -/
theorem natStore_lt (a : AField) (x : String) : natStore a x < 2 ^ 64 := ZMod.val_lt (a x)

/-- The guard holds on every store: an `assert`, a `range` guard passing
    `rangeTrivialB`, or a pull-back of such a guard. -/
def Guard.trivialB : Guard → Bool
  | .range _ e => rangeTrivialB e
  | .loopHalts _ _ _ => false
  | .unsupported _ => false
  | .assert _ => true
  | .after _ g => g.trivialB
  | .whenNz _ g => g.trivialB
  | .everyTrip _ _ _ g => g.trivialB
  | .loopBody _ _ _ g => g.trivialB

/-- The guard contains an `unsupported` node. -/
def Guard.unsupportedB : Guard → Bool
  | .unsupported _ => true
  | .after _ g => g.unsupportedB
  | .whenNz _ g => g.unsupportedB
  | .everyTrip _ _ _ g => g.unsupportedB
  | .loopBody _ _ _ g => g.unsupportedB
  | _ => false

/-- A predicate true on every state holds at the entry of every trip. -/
theorem atrips_of_forall {A : Type} {Q : A → Prop} (hQ : ∀ a, Q a) (g : A → Bool)
    (fb : A → A) : ∀ (k : Nat) (a : A), atrips Q g fb k a
  | 0, _ => trivial
  | k + 1, a => ⟨hQ a, fun _ => atrips_of_forall hQ g fb k (fb a)⟩

theorem Guard.trivialB_sound : ∀ (g : Guard), g.trivialB = true → ∀ a, g.holds a
  | .range _ e, h, a => rangeTrivialB_sound (natStore_lt a) e h
  | .loopHalts _ _ _, h, _ => by simp [Guard.trivialB] at h
  | .unsupported _, h, _ => by simp [Guard.trivialB] at h
  | .assert _, _, _ => trivial
  | .after _ g, h, _ => Guard.trivialB_sound g h _
  | .whenNz _ g, h, a => fun _ => Guard.trivialB_sound g h a
  | .everyTrip _ _ _ g, h, _ => fun _ _ => Guard.trivialB_sound g h _
  | .loopBody _ _ _ g, h, _ => atrips_of_forall (Guard.trivialB_sound g h) _ _ _ _

/-! ## The pass on a `LowCT` command -/

/-- The level `tsLowCTL` picks over the layout `L`: none for an unsupported node, pure
    when every guard is statically true, `Option` otherwise. -/
def tsLevelLowCTL (L : ArrLayout) (fuel : Nat) (c : LowCT) : Option MonadLevel :=
  if (ascendGL L fuel c).1.any Guard.unsupportedB then none
  else if (ascendGL L fuel c).1.all Guard.trivialB then some .pure
  else some .option

/-- The level `tsLowCT` picks: `tsLevelLowCTL` at the empty layout. -/
abbrev tsLevelLowCT (fuel : Nat) (c : LowCT) : Option MonadLevel := tsLevelLowCTL [] fuel c

/-- The abstract program of a `LowCT` command over the layout `L` at the weakest fitting
    level: the transformer of `ascendGL L` as a pure function when its guards are
    statically true, as the `Option` program failing where a guard fails otherwise, and
    none when a guard contains an `unsupported` node. -/
def tsLowCTL {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT) :
    Option (AbsProg ε AField AField) :=
  if (ascendGL L fuel c).1.any Guard.unsupportedB then none
  else if (ascendGL L fuel c).1.all Guard.trivialB then some (.pure (ascendGL L fuel c).2)
  else some (.option (optGuard (guardsHold (ascendGL L fuel c).1) (ascendGL L fuel c).2))

/-- The abstract program of a `LowCT` command over `SRwordNT`: `tsLowCTL` at the empty
    layout. -/
abbrev tsLowCT {ε : Type} (fuel : Nat) (c : LowCT) : Option (AbsProg ε AField AField) :=
  tsLowCTL [] fuel c

theorem tsLowCTL_level {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT) :
    (tsLowCTL (ε := ε) L fuel c).map AbsProg.level = tsLevelLowCTL L fuel c := by
  unfold tsLowCTL tsLevelLowCTL
  split
  · rfl
  · split <;> rfl

theorem tsLowCT_level {ε : Type} (fuel : Nat) (c : LowCT) :
    (tsLowCT (ε := ε) fuel c).map AbsProg.level = tsLevelLowCT fuel c :=
  tsLowCTL_level [] fuel c

/-- **Soundness of the pass at the unified waist over a layout.** The abstract program
    `tsLowCTL L` returns refines `c` under `semU fuel` over `SRwordL L`, at its own
    level. -/
theorem tsLowCTL_sound {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT)
    {p : AbsProg ε AField AField} (h : tsLowCTL L fuel c = some p) :
    p.Refines (fun env => semU fuel c env) (SRwordL L) (liftOk (SRwordL L)) := by
  have hs := ascendGL_sound L fuel c
  unfold tsLowCTL at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i htriv
      obtain rfl := Option.some.inj h
      intro env a hSR _
      exact hs env a hSR (fun g hg => Guard.trivialB_sound g (List.all_eq_true.mp htriv g hg) a)
    · obtain rfl := Option.some.inj h
      exact (refinesP_iff_refinesO_guard (fun env => semU fuel c env) (SRwordL L) (SRwordL L)
        (guardsHold (ascendGL L fuel c).1) (ascendGL L fuel c).2).mp hs

/-- **Soundness of the pass at the unified waist.** The abstract program `tsLowCT`
    returns refines `c` under `semU fuel` over `SRwordNT`, at its own level. -/
theorem tsLowCT_sound {ε : Type} (fuel : Nat) (c : LowCT) {p : AbsProg ε AField AField}
    (h : tsLowCT fuel c = some p) :
    p.Refines (fun env => semU fuel c env) SRwordNT (liftOk SRwordNT) := by
  have hs := ascendG_sound fuel c
  unfold tsLowCT tsLowCTL at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i htriv
      obtain rfl := Option.some.inj h
      intro env a hSR _
      exact hs env a hSR (fun g hg => Guard.trivialB_sound g (List.all_eq_true.mp htriv g hg) a)
    · obtain rfl := Option.some.inj h
      exact (refinesP_iff_refinesO_guard (fun env => semU fuel c env) SRwordNT SRwordNT
        (guardsHold (ascendG fuel c).1) (ascendG fuel c).2).mp hs

/-- **Soundness of the pass at `semScalar` over a layout** on a loop-free command. -/
theorem tsLowCTL_sound_scalar {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT)
    (hlf : loopFree c = true) {p : AbsProg ε AField AField} (h : tsLowCTL L fuel c = some p) :
    p.Refines (fun env => semScalar c env) (SRwordL L) (liftOk (SRwordL L)) := by
  have hsem : (fun env => semU fuel c env) = (fun env => semScalar c env) :=
    funext (semU_eq_semScalar_of_loopFree fuel c hlf)
  have hs := tsLowCTL_sound L fuel c h
  rwa [hsem] at hs

/-- **Soundness of the pass at `semScalar`** on a loop-free command. -/
theorem tsLowCT_sound_scalar {ε : Type} (fuel : Nat) (c : LowCT) (hlf : loopFree c = true)
    {p : AbsProg ε AField AField} (h : tsLowCT fuel c = some p) :
    p.Refines (fun env => semScalar c env) SRwordNT (liftOk SRwordNT) := by
  have hsem : (fun env => semU fuel c env) = (fun env => semScalar c env) :=
    funext (semU_eq_semScalar_of_loopFree fuel c hlf)
  have hs := tsLowCT_sound fuel c h
  rwa [hsem] at hs

/-- The pass over a layout returns a program exactly when no guard contains an
    `unsupported` node. -/
theorem tsLowCTL_isSome_iff {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT) :
    (tsLowCTL (ε := ε) L fuel c).isSome = true ↔
      (ascendGL L fuel c).1.any Guard.unsupportedB = false := by
  unfold tsLowCTL
  split
  · rename_i hu; simp [hu]
  · rename_i hu
    simp only [Bool.not_eq_true] at hu
    simp only [hu, iff_true]
    split <;> rfl

/-- The pass returns a program exactly when no guard contains an `unsupported`
    node. -/
theorem tsLowCT_isSome_iff {ε : Type} (fuel : Nat) (c : LowCT) :
    (tsLowCT (ε := ε) fuel c).isSome = true ↔
      (ascendG fuel c).1.any Guard.unsupportedB = false :=
  tsLowCTL_isSome_iff [] fuel c

/-- The array kernel `arrSelK` is abstracted at the pure level over its layout: its one
    guard, the range condition of the mask select, is statically true. -/
theorem arrSelK_tsLowCTL {ε : Type} (fuel : Nat) :
    tsLowCTL (ε := ε) arrSelLayout fuel arrSelK = some (.pure arrSelKAbs) := rfl

/-- The pure program of `arrSelK` refines its `semScalar` run over `SRwordL arrSelLayout`. -/
theorem arrSelK_ts_refines {ε : Type} :
    (AbsProg.pure (ε := ε) arrSelKAbs).Refines (fun env => semScalar arrSelK env)
      (SRwordL arrSelLayout) (liftOk (SRwordL arrSelLayout)) :=
  tsLowCTL_sound_scalar arrSelLayout 0 arrSelK rfl (arrSelK_tsLowCTL 0)

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

/-! ## The choice over both program kinds -/

/-- A program the ascent abstracts: a `LowCT` command at a fuel, or a raw hax source
    under a builtin table and a fuel. -/
inductive Kernel where
  | lowct (fuel : Nat) (c : LowCT)
  | hax (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr)

/-- The level the pass picks for a kernel; `none` when the `LowCT` abstraction has an
    unsupported node. -/
def Kernel.tsLevel : Kernel → Option MonadLevel
  | .lowct fuel c => tsLevelLowCT fuel c
  | .hax _ _ e => some (tsHaxLevel e)

end CatCrypt.Crypto.SecureCompilation.Ascent
