/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ANormCore
public import HaxLean.Phase.InlineLocalClosures
public import CatCrypt.Crypto.Hax.DenoteKeeps

/-!
# `aNormalizeTotal` refines the control-flow semantics `denote'`

`aNormalizeTotal_denote'`: from one environment, every run of `denote' bi fuel e` whose
outcome is not an error is matched by a run of `denote' bi fuel (aNormalizeTotal e)` to the
same outcome, at the same fuel. The statement covers the whole of `ImpExpr` except
`match_`, including the loop and exit forms `whileFold`, `forFold`, `forFoldReturn`,
`cfBreak`, `cfContinue` and `cfBreakContinue`, under the Boolean source condition
`aNormTDenoteOk e`.

## The source condition

`ANormDOk ok e` holds when

* every name `e` reads or binds (variable, `letBind`, `assign`, loop counter) satisfies
  `ok`; `aNormTDenoteOk` takes for `ok` the names other than the fresh names
  `__anorm_j` the normaliser mints;
* `e` has no `match_`;
* a variable argument of a call or tuple is left unchanged by the arguments to its right
  (`argsOrderOk`): the normaliser binds every other argument before the call, so the
  variable is read after them;
* a loop bound the normaliser binds (`hoistsLo`, `hoistsBound`) satisfies `ANormDOk`, and a
  bound it keeps is in `frameOk ok ok`. The normaliser binds the lower bound before the
  upper one, and binds a variable lower bound whenever it binds the upper bound, so the
  order of evaluation of the two bounds is kept.

## The simulation

The target environment agrees with the source environment off the fresh names below the
bound `K` (`ARel`), and agrees with a fixed environment `g` on the fresh names below the
counter `k`, which the part of the target from counter `k` does not write. A binding of
a fresh name `__anorm_j` with `k ≤ j < K` keeps the relation (`ARel.extend_tmp`), and a
subterm normalised from a counter `k' ≥ k` simulates at `k` (`refE_widen`).

## Main definitions

* `varKept`, `argsOrderOk`, `ANormDOk` — the source condition
* `aNormTDenoteOk` — the condition on the input of `aNormalizeTotal`
* `ARel` — the relation between target and source environments

## Main results

* `letBindNorm_run`, `hoistBind_run` — floating the leading bindings of a right-hand side
  and binding a conditional right-hand side in each branch leave a run unchanged
* `aNormTArgs_denote'` — a run of the arguments of a call to values is matched by the run
  of the hoisted bindings, after which the arguments of the normal form evaluate to the
  same values
* `aNormTBody_denote'` — the hoisting pass refines `denote'`
* `bindTails_denote'` — tail binding refines `denote'`
* `aNormalizeTotal_denote'` — under `aNormTDenoteOk e`, every run of `denote' bi fuel e`
  whose outcome is not an error is matched by a run of `aNormalizeTotal e` from the same
  environment, at the same fuel, to the same outcome; `match_` is excluded
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat Value Env Outcome Builtins denote' denoteArgs'
  denoteForLoop' denoteForLoopOrig' denoteForLoopRev' denoteForLoopRevOrig')
open _root_.Hax.InlineLocalClosures
open _root_.Hax.ContinueFlag (var_run lit_run unitVal_run letBind_run seq_run ifThenElse_run
  app_run args_nil_run args_cons_run)

/-! ## §1  The source condition -/

/-- `e` leaves `x` unchanged when `a` is the variable `x`: `e` is in `frameOk` with every
    binder other than `x`. Any other `a` imposes no condition. -/
def varKept : ImpExpr → ImpExpr → Bool
  | .var x, e => frameOk (fun _ => true) (fun n => n != x) (fun _ => true) e
  | _, _ => true

/-- Every variable argument is left unchanged by the arguments to its right. -/
def argsOrderOk : List ImpExpr → Bool
  | [] => true
  | a :: as => as.all (varKept a) && argsOrderOk as

mutual

/-- The source condition of `aNormTBody_denote'`: every name read or bound satisfies
    `ok`, there is no `match_`, and the variable arguments of every call and tuple are left
    unchanged by the arguments to their right. A loop bound the normaliser binds
    (`hoistsLo`, `hoistsBound`) satisfies `ANormDOk ok`; a bound it keeps is in
    `frameOk ok ok`. -/
def ANormDOk (ok : String → Bool) : ImpExpr → Bool
  | .lit _ => true
  | .var n => ok n
  | .unitVal => true
  | .letBind n v b => ok n && ANormDOk ok v && ANormDOk ok b
  | .lam _ _ => true
  | .app _ args => argsOrderOk args && ANormDOkList ok args
  | .tuple es => argsOrderOk es && ANormDOkList ok es
  | .proj e _ => ANormDOk ok e
  | .ifThenElse c t e => ANormDOk ok c && ANormDOk ok t && ANormDOk ok e
  | .match_ _ _ => false
  | .seq a b => ANormDOk ok a && ANormDOk ok b
  | .borrow e => ANormDOk ok e
  | .deref e => ANormDOk ok e
  | .assign n r => ok n && ANormDOk ok r
  | .forLoop v lo hi b =>
    ok v && (if hoistsLo lo hi then ANormDOk ok lo else frameOk ok ok (fun _ => true) lo) &&
      (if hoistsBound hi then ANormDOk ok hi else frameOk ok ok (fun _ => true) hi) &&
      ANormDOk ok b
  | .forLoopRev v lo hi b =>
    ok v && (if hoistsLo lo hi then ANormDOk ok lo else frameOk ok ok (fun _ => true) lo) &&
      (if hoistsBound hi then ANormDOk ok hi else frameOk ok ok (fun _ => true) hi) &&
      ANormDOk ok b
  | .whileLoop c b => ANormDOk ok c && ANormDOk ok b
  | .break_ none => true
  | .break_ (some e) => ANormDOk ok e
  | .continue_ => true
  | .earlyReturn e => ANormDOk ok e
  | .questionMark e => ANormDOk ok e
  | .forFold v lo hi b =>
    ok v && (if hoistsLo lo hi then ANormDOk ok lo else frameOk ok ok (fun _ => true) lo) &&
      (if hoistsBound hi then ANormDOk ok hi else frameOk ok ok (fun _ => true) hi) &&
      ANormDOk ok b
  | .forFoldRev v lo hi b =>
    ok v && (if hoistsLo lo hi then ANormDOk ok lo else frameOk ok ok (fun _ => true) lo) &&
      (if hoistsBound hi then ANormDOk ok hi else frameOk ok ok (fun _ => true) hi) &&
      ANormDOk ok b
  | .whileFold c b => ANormDOk ok c && ANormDOk ok b
  | .forFoldReturn v lo hi b =>
    ok v && frameOk ok ok (fun _ => true) lo && frameOk ok ok (fun _ => true) hi &&
      ANormDOk ok b
  | .forFoldRevReturn v lo hi b =>
    ok v && frameOk ok ok (fun _ => true) lo && frameOk ok ok (fun _ => true) hi &&
      ANormDOk ok b
  | .whileFoldReturn c b => ANormDOk ok c && ANormDOk ok b
  | .cfBreak e => ANormDOk ok e
  | .cfContinue e => ANormDOk ok e
  | .cfBreakContinue e => ANormDOk ok e
  | .typeAscription e _ => ANormDOk ok e

/-- `ANormDOk` of every expression of a list. -/
def ANormDOkList (ok : String → Bool) : List ImpExpr → Bool
  | [] => true
  | e :: es => ANormDOk ok e && ANormDOkList ok es

end

theorem ANormDOkList_mem {ok : String → Bool} {es : List ImpExpr}
    (h : ANormDOkList ok es = true) : ∀ a ∈ es, ANormDOk ok a = true := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [ANormDOkList, Bool.and_eq_true] at h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact ih h.2 a ha

/-- The condition of `aNormalizeTotal_denote'`: the input of the hoisting pass satisfies
    `ANormDOk` with every name distinct from the fresh names `aNormalizeTotal e` mints. -/
def aNormTDenoteOk (e : ImpExpr) : Bool :=
  ANormDOk (fun n => (List.range (aNormalizeTotalCount e)).all (fun j => n != anormName j))
    (bindTails e)

/-! ## §2  Runs of bindings -/

section Runs

variable (bi : Builtins) (fuel : Nat)

theorem letBind_run_plain (n : String) (val body : ImpExpr) (env e1 : Env) (w : Value)
    (h : (denote' bi fuel val).run env = (.val w, e1)) (hw : w.isControlFlow = false) :
    (denote' bi fuel (.letBind n val body)).run env =
      (denote' bi fuel body).run (e1.extend n w) := by
  rw [letBind_run, h]
  cases w <;> first | rfl | simp [_root_.Hax.Value.isControlFlow] at hw

theorem prependBindings_append (bs cs : List (String × ImpExpr)) (body : ImpExpr) :
    prependBindings (bs ++ cs) body = prependBindings bs (prependBindings cs body) := by
  simp [prependBindings, List.foldr_append]

/-- Floating the leading bindings of `x` outwards: for a context `F` that runs as
    `let n = c; B` on every `c`, the bindings of `x` followed by `F` applied to its core run
    as `let n = x; B`. -/
theorem floatCtx_run (n : String) (B : ImpExpr) (F : ImpExpr → ImpExpr)
    (hF : ∀ c env, (denote' bi fuel (F c)).run env = (denote' bi fuel (.letBind n c B)).run env) :
    ∀ (x : ImpExpr) (env : Env),
      (denote' bi fuel (prependBindings (splitLetBinds x).1 (F (splitLetBinds x).2))).run env =
        (denote' bi fuel (.letBind n x B)).run env := by
  intro x
  induction x using ImpExpr.ind
  case letBind a v t _ iht =>
    intro env
    rw [splitLetBinds_letBind, prependBindings_cons, letBind_run, letBind_run, letBind_run]
    rcases (denote' bi fuel v).run env with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w
      case controlFlow b w => rfl
      all_goals (dsimp only; rw [iht, letBind_run])
    all_goals rfl
  all_goals intro env; exact hF _ env

/-- `bindRhs` runs as `letBind`. -/
theorem bindRhs'_run (x : String) (r body : ImpExpr) (env : Env) :
    (denote' bi fuel (bindRhs x r body)).run env =
      (denote' bi fuel (.letBind x r body)).run env := by
  cases r
  case ifThenElse c t e =>
    have hfl : ∀ (s : ImpExpr) (env' : Env),
        (denote' bi fuel (floatLet x s .unitVal)).run env' =
          (denote' bi fuel (.letBind x s .unitVal)).run env' :=
      fun s env' => floatCtx_run bi fuel x .unitVal (fun c => .letBind x c .unitVal)
        (fun _ _ => rfl) s env'
    simp only [bindRhs]
    rw [seq_run, ifThenElse_run, letBind_run, ifThenElse_run]
    rcases (denote' bi fuel c).run env with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w
      case bool b =>
        cases b <;>
        · dsimp only
          rw [hfl, letBind_run]
          rcases (denote' bi fuel _).run e1 with ⟨o2, e2⟩
          rcases o2 with w2 | _ | _ | _ | _
          · cases w2 <;> first | rfl | (dsimp only; rw [unitVal_run])
          all_goals rfl
      all_goals rfl
    all_goals rfl
  all_goals rfl

/-- The normal form of `let n = x; B`: the leading bindings of `x` floated outwards and its
    core bound by `bindRhs`, runs as `let n = x; B`. -/
theorem letBindNorm_run (n : String) (x B : ImpExpr) (env : Env) :
    (denote' bi fuel (prependBindings (splitLetBinds x).1
      (bindRhs n (splitLetBinds x).2 B))).run env =
        (denote' bi fuel (.letBind n x B)).run env :=
  floatCtx_run bi fuel n B (fun c => bindRhs n c B) (fun c env => bindRhs'_run bi fuel n c B env)
    x env

/-- The bindings `hoistAt x j` followed by `C` run as `let __anorm_j = x; C`. -/
theorem hoistBind_run (x C : ImpExpr) (j : Nat) (env : Env) :
    (denote' bi fuel (prependBindings (hoistAt x j).1 C)).run env =
      (denote' bi fuel (.letBind (anormName j) x C)).run env := by
  simp only [hoistAt]
  rw [prependBindings_append]
  exact floatCtx_run bi fuel (anormName j) C (fun c => prependBindings [(anormName j, c)] C)
    (fun _ _ => rfl) x env

theorem args_cons_some {a : ImpExpr} {as : List ImpExpr} {env s : Env} {vals : List Value}
    (h : (denoteArgs' bi fuel (a :: as)).run env = (some vals, s)) :
    ∃ w m rv, (denote' bi fuel a).run env = (.val w, m) ∧ w.isControlFlow = false ∧
      (denoteArgs' bi fuel as).run m = (some rv, s) ∧ vals = w :: rv := by
  rw [args_cons_run] at h
  rcases ha : (denote' bi fuel a).run env with ⟨o, m⟩
  rw [ha] at h
  rcases o with w | _ | _ | _ | _
  · cases w
    case controlFlow => cases h
    all_goals
      dsimp only at h
      rcases hr : (denoteArgs' bi fuel as).run m with ⟨or, s'⟩
      rw [hr] at h
      rcases or with _ | rv
      · cases h
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        simp only [Option.map_some, Option.some.injEq] at h1
        exact ⟨_, m, rv, rfl, rfl, by rw [hr, ← h2], h1.symm⟩
  all_goals cases h

theorem args_cons_of {a : ImpExpr} {as : List ImpExpr} {env m s : Env} {w : Value}
    {rv : List Value} (h1 : (denote' bi fuel a).run env = (.val w, m))
    (hw : w.isControlFlow = false) (h2 : (denoteArgs' bi fuel as).run m = (some rv, s)) :
    (denoteArgs' bi fuel (a :: as)).run env = (some (w :: rv), s) := by
  rw [args_cons_run, h1]
  cases w <;> first | (dsimp only; rw [h2]; rfl) | (simp [_root_.Hax.Value.isControlFlow] at hw)

end Runs

/-! ## §3  The relation between target and source environments -/

/-- The target environment `e₁` agrees with the source environment `e₂` off the first `K`
    fresh names, and with `g` on the fresh names below `k`. -/
def ARel (K k : Nat) (g e₁ e₂ : Env) : Prop :=
  EnvEqOff (AnormBelow K) e₂ e₁ ∧ ∀ j, j < k → e₁ (anormName j) = g (anormName j)

theorem anormName_below {K j : Nat} (h : j < K) : AnormBelow K (anormName j) := ⟨j, h, rfl⟩

theorem ARel.extend {K k : Nat} {g e₁ e₂ : Env} (h : ARel K k g e₁ e₂) (hk : k ≤ K)
    {n : String} (hn : ¬ AnormBelow K n) (w : Value) :
    ARel K k g (e₁.extend n w) (e₂.extend n w) := by
  refine ⟨h.1.extend n w, fun j hj => ?_⟩
  have hne : anormName j ≠ n := fun h' => hn (h' ▸ anormName_below (by omega))
  rw [Env.extend_other _ _ _ _ hne]
  exact h.2 j hj

theorem ARel.extend_tmp {K k : Nat} {g e₁ e₂ : Env} (h : ARel K k g e₁ e₂) {j : Nat}
    (hkj : k ≤ j) (hjK : j < K) (w : Value) : ARel K k g (e₁.extend (anormName j) w) e₂ := by
  refine ⟨h.1.extend_right (anormName_below hjK) w, fun i hi => ?_⟩
  have hne : anormName i ≠ anormName j := fun h' => by have := anormName_inj h'; omega
  rw [Env.extend_other _ _ _ _ hne]
  exact h.2 i hi

theorem ARel.read {K k : Nat} {g e₁ e₂ : Env} (h : ARel K k g e₁ e₂) {x : String}
    (hx : ¬ AnormBelow K x) : e₁ x = e₂ x := (h.1 x hx).symm

/-- A simulation from counter `k'` is a simulation from every counter `k ≤ k'`. -/
theorem refE_widen {K k k' : Nat} (hk : k ≤ k') {t s : StateM Env Outcome}
    (h : ∀ g, RefE (ARel K k' g) t s) : ∀ g, RefE (ARel K k g) t s := by
  intro g e₁ e₂ hR o s₂ hr hnb
  obtain ⟨s₁, h1, hEq, hLow⟩ := h e₁ e₁ e₂ ⟨hR.1, fun _ _ => rfl⟩ o s₂ hr hnb
  exact ⟨s₁, h1, hEq, fun j hj => (hLow j (by omega)).trans (hR.2 j hj)⟩

theorem RefR.congr_tgt {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop}
    {t₁ t₂ s : StateM Env α} (h : RefR P Q bad t₂ s) (he : ∀ env, t₁.run env = t₂.run env) :
    RefR P Q bad t₁ s := by
  intro e₁ e₂ hP o s₂ hr hb
  obtain ⟨s₁, h1, hQ⟩ := h e₁ e₂ hP o s₂ hr hb
  exact ⟨s₁, (he e₁).trans h1, hQ⟩

section Frame

variable (bi : Builtins)

/-- An expression in `frameOk ok ok` refines itself under `ARel`. -/
theorem refE_frameOk {ok : String → Bool} {K k : Nat}
    (hok : ∀ n, ok n = true → ¬ AnormBelow K n) (hkK : k ≤ K) (e : ImpExpr)
    (h : frameOk ok ok (fun _ => true) e = true) (g : Env) (fuel : Nat) :
    RefE (ARel K k g) (denote' bi fuel e) (denote' bi fuel e) := by
  have := denote'_frame (R := ARel K k g) (bi₁ := bi) (bi₂ := bi) id ok ok (fun _ => true)
    (fun e₁ e₂ x hR hx => hR.read (hok x hx))
    (fun e₁ e₂ n w hR hn => hR.extend hkK (hok n hn) w) (fun _ _ => rfl) e h fuel
  rwa [renameReads_id e (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e h)]
    at this

theorem denoteArgs'_keeps {x : String} (fuel : Nat) (as : List ImpExpr)
    (h : as.all (varKept (.var x)) = true) :
    ∀ env vals s, (denoteArgs' bi fuel as).run env = (some vals, s) → s x = env x := by
  induction as with
  | nil =>
    intro env vals s hr
    rw [args_nil_run] at hr
    cases hr; rfl
  | cons a as ih =>
    intro env vals s hr
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨w, m, rv, h1, _, h2, _⟩ := args_cons_some bi fuel hr
    rw [ih h.2 m rv s h2]
    exact denote'_keeps bi a h.1 fuel env h1 (by rintro ⟨_, h'⟩; cases h')

end Frame

/-! ## §4  Counted loops after the lower bound -/

section Tail

variable (bi : Builtins) (fuel : Nat) (var : String) (body : ImpExpr)

/-- The run of `forLoop var lo hi body` after `lo` evaluates to the value `vlo` and `hi` to
    the outcome `rhi`. -/
def forTailOrig (vlo : Value) (rhi : Outcome) : StateM Env Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoopOrig' bi fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoopOrig' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoopOrig' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) => denoteForLoopOrig' bi fuel var lo_val hi_val body
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The run of `forFold var lo hi body` after `lo` evaluates to the value `vlo` and `hi` to
    the outcome `rhi`. -/
def forTailFold (vlo : Value) (rhi : Outcome) : StateM Env Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoop' bi fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoop' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoop' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) => denoteForLoop' bi fuel var lo_val hi_val body
  | _, .val (.controlFlow _ _) => pure rhi
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

theorem forLoop_run_lo (lo hi : ImpExpr) (env e1 : Env) (vlo : Value)
    (h : (denote' bi fuel lo).run env = (.val vlo, e1)) (hv : vlo.isControlFlow = false) :
    (denote' bi fuel (.forLoop var lo hi body)).run env =
      ((denote' bi fuel hi) >>= forTailOrig bi fuel var body vlo).run e1 := by
  simp only [denote']
  rw [run_bind, h]
  cases vlo <;> first | rfl | simp [_root_.Hax.Value.isControlFlow] at hv

theorem forFold_run_lo (lo hi : ImpExpr) (env e1 : Env) (vlo : Value)
    (h : (denote' bi fuel lo).run env = (.val vlo, e1)) (hv : vlo.isControlFlow = false) :
    (denote' bi fuel (.forFold var lo hi body)).run env =
      ((denote' bi fuel hi) >>= forTailFold bi fuel var body vlo).run e1 := by
  simp only [denote']
  rw [run_bind, h]
  cases vlo <;> first | rfl | simp [_root_.Hax.Value.isControlFlow] at hv

/-- The run of `forLoopRev var lo hi body` after `lo` evaluates to the value `vlo` and `hi`
    to the outcome `rhi`. -/
def forTailRevOrig (vlo : Value) (rhi : Outcome) : StateM Env Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoopRevOrig' bi fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoopRevOrig' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoopRevOrig' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) =>
      denoteForLoopRevOrig' bi fuel var lo_val hi_val body
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The run of `forFoldRev var lo hi body` after `lo` evaluates to the value `vlo` and `hi`
    to the outcome `rhi`. -/
def forTailFoldRev (vlo : Value) (rhi : Outcome) : StateM Env Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoopRev' bi fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoopRev' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoopRev' bi fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) => denoteForLoopRev' bi fuel var lo_val hi_val body
  | _, .val (.controlFlow _ _) => pure rhi
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The run of a counted loop after its lower bound evaluates to the outcome `rlo`: a
    control-flow value or a non-value is the result, and a plain value `vlo` is followed by
    the run of `hi` and the tail `T vlo`. -/
def anfLoopTail (hi : ImpExpr) (T : Value → Outcome → StateM Env Outcome) (rlo : Outcome) :
    StateM Env Outcome :=
  match rlo with
  | .val w => if w.isControlFlow then pure (.val w) else (denote' bi fuel hi) >>= T w
  | other => pure other

theorem forLoop_run_tail (lo hi : ImpExpr) (env : Env) :
    (denote' bi fuel (.forLoop var lo hi body)).run env =
      ((denote' bi fuel lo) >>= anfLoopTail bi fuel hi (forTailOrig bi fuel var body)).run env := by
  simp only [denote']
  rw [run_bind, run_bind]
  rcases (denote' bi fuel lo).run env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

theorem forLoopRev_run_tail (lo hi : ImpExpr) (env : Env) :
    (denote' bi fuel (.forLoopRev var lo hi body)).run env =
      ((denote' bi fuel lo) >>= anfLoopTail bi fuel hi (forTailRevOrig bi fuel var body)).run
        env := by
  simp only [denote']
  rw [run_bind, run_bind]
  rcases (denote' bi fuel lo).run env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

theorem forFold_run_tail (lo hi : ImpExpr) (env : Env) :
    (denote' bi fuel (.forFold var lo hi body)).run env =
      ((denote' bi fuel lo) >>= anfLoopTail bi fuel hi (forTailFold bi fuel var body)).run env := by
  simp only [denote']
  rw [run_bind, run_bind]
  rcases (denote' bi fuel lo).run env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

theorem forFoldRev_run_tail (lo hi : ImpExpr) (env : Env) :
    (denote' bi fuel (.forFoldRev var lo hi body)).run env =
      ((denote' bi fuel lo) >>= anfLoopTail bi fuel hi (forTailFoldRev bi fuel var body)).run
        env := by
  simp only [denote']
  rw [run_bind, run_bind]
  rcases (denote' bi fuel lo).run env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

/-- The run of `ifThenElse c t e` after `c` evaluates to the outcome `rc`. -/
def iteTail (t e : ImpExpr) (rc : Outcome) : StateM Env Outcome :=
  match rc with
  | .val (.controlFlow k v) => pure (.val (.controlFlow k v))
  | .val (.bool true) => denote' bi fuel t
  | .val (.bool false) => denote' bi fuel e
  | .val _ => pure (.err "if condition not a bool")
  | other => pure other

theorem ifThenElse_run_tail (c t e : ImpExpr) (env : Env) :
    (denote' bi fuel (.ifThenElse c t e)).run env =
      ((denote' bi fuel c) >>= iteTail bi fuel t e).run env := by
  rw [ifThenElse_run, run_bind]
  rcases (denote' bi fuel c).run env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w
    case bool b => cases b <;> rfl
    all_goals rfl
  all_goals rfl

end Tail

section TailRel

variable {bi : Builtins} {R : Env → Env → Prop}

theorem RefR.congr_src {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop}
    {t s₁ s₂ : StateM Env α} (h : RefR P Q bad t s₂) (he : ∀ env, s₁.run env = s₂.run env) :
    RefR P Q bad t s₁ := by
  intro e₁ e₂ hP o s hr hb
  exact h e₁ e₂ hP o s ((he e₂).symm.trans hr) hb

theorem forTailOrig_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefE R (denote' bi fuel b₁) (denote' bi fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefE R (forTailOrig bi fuel var b₁ vlo rhi) (forTailOrig bi fuel var b₂ vlo rhi) := by
  have hL := forLoopOrig'_rel (bi₁ := bi) (bi₂ := bi) hv h fuel
  unfold forTailOrig
  split <;> first | exact hL _ _ | exact RefR.pure _

theorem forTailFold_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefE R (denote' bi fuel b₁) (denote' bi fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefE R (forTailFold bi fuel var b₁ vlo rhi) (forTailFold bi fuel var b₂ vlo rhi) := by
  have hL := forLoop'_rel (bi₁ := bi) (bi₂ := bi) hv h fuel
  unfold forTailFold
  split <;> first | exact hL _ _ | exact RefR.pure _

theorem forTailRevOrig_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefE R (denote' bi fuel b₁) (denote' bi fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefE R (forTailRevOrig bi fuel var b₁ vlo rhi) (forTailRevOrig bi fuel var b₂ vlo rhi) := by
  have hL := forLoopRevOrig'_rel (bi₁ := bi) (bi₂ := bi) hv h fuel
  unfold forTailRevOrig
  split <;> first | exact hL _ _ | exact RefR.pure _

theorem forTailFoldRev_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefE R (denote' bi fuel b₁) (denote' bi fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefE R (forTailFoldRev bi fuel var b₁ vlo rhi) (forTailFoldRev bi fuel var b₂ vlo rhi) := by
  have hL := forLoopRev'_rel (bi₁ := bi) (bi₂ := bi) hv h fuel
  unfold forTailFoldRev
  split <;> first | exact hL _ _ | exact RefR.pure _

theorem anfLoopTail_rel {hi : ImpExpr} {T₁ T₂ : Value → Outcome → StateM Env Outcome} (fuel : Nat)
    (hhi : RefE R (denote' bi fuel hi) (denote' bi fuel hi))
    (hT : ∀ vlo rhi, RefE R (T₁ vlo rhi) (T₂ vlo rhi))
    (hoth : ∀ vlo o m, (∀ w, o ≠ .val w) → (T₂ vlo o).run m = (o, m)) (rlo : Outcome) :
    RefE R (anfLoopTail bi fuel hi T₁ rlo) (anfLoopTail bi fuel hi T₂ rlo) := by
  unfold anfLoopTail
  split
  · split
    · exact RefR.pure _
    · refine RefR.bind hhi (fun a _ => hT _ a) (fun a ha s => ?_)
      obtain ⟨m, rfl⟩ := ha
      rw [hoth _ _ s (fun w h' => by cases h')]
      exact ⟨m, rfl⟩
  · exact RefR.pure _

/-- **Binding a subterm to a fresh name, with the bound value in the relation.** Let the
    source run `hi` and continue with `Ts`, and the target bind `tmp` to `hi'` and run `C`.
    If `hi'` refines `hi`, binding `tmp` to `w` takes `R` to `Rw w`, `C` refines `Ts` on the
    plain value `w` from `Rw w` back to `R`, and `Ts` passes on control-flow values and
    non-values, then `let tmp = hi'; C` refines the source. -/
theorem letBind_hoist_cont {tmp : String} {hi hi' C : ImpExpr}
    {Ts : Outcome → StateM Env Outcome} {fuel : Nat} {Rw : Value → Env → Env → Prop}
    (hext : ∀ e₁ e₂ w, R e₁ e₂ → Rw w (e₁.extend tmp w) e₂)
    (hhi : RefE R (denote' bi fuel hi') (denote' bi fuel hi))
    (hT : ∀ w, w.isControlFlow = false → RefR (Rw w) R IsErr (denote' bi fuel C) (Ts (.val w)))
    (hcf : ∀ w m o s, w.isControlFlow = true → (Ts (.val w)).run m = (o, s) → ¬ IsErr o →
      o = .val w ∧ s = m)
    (hother : ∀ o m, (∀ w, o ≠ .val w) → (Ts o).run m = (o, m)) :
    RefE R (denote' bi fuel (.letBind tmp hi' C)) ((denote' bi fuel hi) >>= Ts) := by
  intro e₁ e₂ hR o s₂ hr hnb
  rw [run_bind] at hr
  rcases hs : (denote' bi fuel hi).run e₂ with ⟨oh, m₂⟩
  rw [hs] at hr
  have hnv : ∀ o', (∀ w, o' ≠ .val w) → (Ts o').run m₂ = (o, s₂) → o' = o ∧ m₂ = s₂ :=
    fun o' h' hr' => by rw [hother o' m₂ h'] at hr'; exact Prod.mk.inj hr'
  have hoh : ¬ IsErr oh := by
    rintro ⟨m, rfl⟩
    obtain ⟨rfl, _⟩ := hnv _ (fun w h' => by cases h') hr
    exact hnb ⟨m, rfl⟩
  obtain ⟨m₁, ht, hRm⟩ := hhi e₁ e₂ hR oh m₂ hs hoh
  rcases oh with w | m | w | _ | w
  · cases hwc : w.isControlFlow
    · rw [letBind_run_plain bi fuel _ _ _ _ _ _ ht hwc]
      exact hT w hwc _ _ (hext _ _ w hRm) o s₂ hr hnb
    · obtain ⟨rfl, rfl⟩ := hcf w m₂ o s₂ hwc hr hnb
      cases w <;> simp [_root_.Hax.Value.isControlFlow] at hwc
      exact ⟨m₁, by rw [letBind_run, ht], hRm⟩
  all_goals
    obtain ⟨rfl, rfl⟩ := hnv _ (fun w h' => by cases h') hr
    exact ⟨m₁, by rw [letBind_run, ht], hRm⟩

theorem iteTail_rel {t₁ t₂ e₁ e₂ : ImpExpr} (fuel : Nat)
    (ht : RefE R (denote' bi fuel t₁) (denote' bi fuel t₂))
    (he : RefE R (denote' bi fuel e₁) (denote' bi fuel e₂)) (rc : Outcome) :
    RefE R (iteTail bi fuel t₁ e₁ rc) (iteTail bi fuel t₂ e₂ rc) := by
  unfold iteTail
  split <;> first | exact ht | exact he | exact RefR.pure _

/-- **Binding a subterm to a fresh name.** Let the source run `hi` and continue with `Ts`,
    and the target bind `tmp` to `hi'` and run `C`, which continues as `Tt` on the value of
    `tmp`. If `hi'` refines `hi`, binding `tmp` alone in the target keeps `R`, `Tt` refines
    `Ts` on plain values, and `Ts` passes on control-flow values and non-values, then
    `let tmp = hi'; C` refines the source. -/
theorem letBind_hoist_rel {tmp : String} {hi hi' C : ImpExpr}
    {Ts Tt : Outcome → StateM Env Outcome} {fuel : Nat}
    (hext : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend tmp w) e₂)
    (hhi : RefE R (denote' bi fuel hi') (denote' bi fuel hi))
    (hC : ∀ e w, e tmp = some w → w.isControlFlow = false →
      (denote' bi fuel C).run e = (Tt (.val w)).run e)
    (hT : ∀ w, w.isControlFlow = false → RefE R (Tt (.val w)) (Ts (.val w)))
    (hcf : ∀ w m o s, w.isControlFlow = true → (Ts (.val w)).run m = (o, s) → ¬ IsErr o →
      o = .val w ∧ s = m)
    (hother : ∀ o m, (∀ w, o ≠ .val w) → (Ts o).run m = (o, m)) :
    RefE R (denote' bi fuel (.letBind tmp hi' C)) ((denote' bi fuel hi) >>= Ts) :=
  letBind_hoist_cont (Rw := fun w e₁ e₂ => R e₁ e₂ ∧ e₁ tmp = some w)
    (fun e₁ e₂ w h => ⟨hext e₁ e₂ w h, Env.extend_same _ _ _⟩) hhi
    (fun w hw e₁ e₂ hR o s hr hnb => by
      rw [hC e₁ w hR.2 hw]
      exact hT w hw e₁ e₂ hR.1 o s hr hnb)
    hcf hother

variable (bi) (fuel : Nat)

theorem forTailOrig_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome) (m : Env)
    (h : ∀ w, o ≠ .val w) : (forTailOrig bi fuel var b vlo o).run m = (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

theorem forTailOrig_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env) (o : Outcome)
    (s : Env) (hw : w.isControlFlow = true) (hr : (forTailOrig bi fuel var b vlo (.val w)).run m = (o, s))
    (ho : ¬ IsErr o) : o = .val w ∧ s = m := by
  cases w <;> simp [_root_.Hax.Value.isControlFlow] at hw
  cases vlo <;> (simp only [forTailOrig] at hr; exact absurd ⟨_, (Prod.mk.inj hr).1.symm⟩ ho)

theorem forTailFold_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome) (m : Env)
    (h : ∀ w, o ≠ .val w) : (forTailFold bi fuel var b vlo o).run m = (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

theorem forTailFold_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env) (o : Outcome)
    (s : Env) (hw : w.isControlFlow = true) (hr : (forTailFold bi fuel var b vlo (.val w)).run m = (o, s))
    (_ho : ¬ IsErr o) : o = .val w ∧ s = m := by
  cases w <;> simp [_root_.Hax.Value.isControlFlow] at hw
  cases vlo <;> (simp only [forTailFold] at hr; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr; exact ⟨rfl, rfl⟩)

theorem forTailRevOrig_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome)
    (m : Env) (h : ∀ w, o ≠ .val w) : (forTailRevOrig bi fuel var b vlo o).run m = (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

theorem forTailRevOrig_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env) (o : Outcome)
    (s : Env) (hw : w.isControlFlow = true)
    (hr : (forTailRevOrig bi fuel var b vlo (.val w)).run m = (o, s))
    (ho : ¬ IsErr o) : o = .val w ∧ s = m := by
  cases w <;> simp [_root_.Hax.Value.isControlFlow] at hw
  cases vlo <;> (simp only [forTailRevOrig] at hr; exact absurd ⟨_, (Prod.mk.inj hr).1.symm⟩ ho)

theorem forTailFoldRev_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome)
    (m : Env) (h : ∀ w, o ≠ .val w) : (forTailFoldRev bi fuel var b vlo o).run m = (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

theorem forTailFoldRev_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env) (o : Outcome)
    (s : Env) (hw : w.isControlFlow = true)
    (hr : (forTailFoldRev bi fuel var b vlo (.val w)).run m = (o, s))
    (_ho : ¬ IsErr o) : o = .val w ∧ s = m := by
  cases w <;> simp [_root_.Hax.Value.isControlFlow] at hw
  cases vlo <;>
    (simp only [forTailFoldRev] at hr; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr; exact ⟨rfl, rfl⟩)

theorem iteTail_other (t e : ImpExpr) (o : Outcome) (m : Env) (h : ∀ w, o ≠ .val w) :
    (iteTail bi fuel t e o).run m = (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => rfl

theorem iteTail_cf (t e : ImpExpr) (w : Value) (m : Env) (o : Outcome) (s : Env)
    (hw : w.isControlFlow = true) (hr : (iteTail bi fuel t e (.val w)).run m = (o, s))
    (_ho : ¬ IsErr o) : o = .val w ∧ s = m := by
  cases w <;> simp [_root_.Hax.Value.isControlFlow] at hw
  simp only [iteTail] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  exact ⟨rfl, rfl⟩

end TailRel

/-! ## §5  The simulation -/

/-- The simulation of `e` by its hoisted form: for every counter `k` whose normal form mints
    fresh names below `K`, the normal form refines `e` under `ARel K k g`, for every `g` and
    fuel. -/
def ANormDSim (bi : Builtins) (K : Nat) (e : ImpExpr) : Prop :=
  ∀ k, (aNormTBody e k).2 ≤ K → ∀ (g : Env) (fuel : Nat),
    RefE (ARel K k g) (denote' bi fuel (aNormTBody e k).1) (denote' bi fuel e)

section Sim

variable (bi : Builtins) {ok : String → Bool} {K : Nat}
  (hok : ∀ n, ok n = true → ¬ AnormBelow K n)

theorem ANormDSim.at {e : ImpExpr} (h : ANormDSim bi K e) {k k' : Nat} (hk : k ≤ k')
    (hK : (aNormTBody e k').2 ≤ K) (g : Env) (fuel : Nat) :
    RefE (ARel K k g) (denote' bi fuel (aNormTBody e k').1) (denote' bi fuel e) :=
  refE_widen hk (fun g => h k' hK g fuel) g

include hok in
/-- **The hoisted arguments.** A run of the arguments to values is matched by the run of
    the hoisted bindings, after which the argument list of the normal form evaluates to the
    same values. -/
theorem aNormTArgs_denote' (args : List ImpExpr) (ih : ∀ a ∈ args, ANormDSim bi K a)
    (hOrd : argsOrderOk args = true) (hA : ∀ a ∈ args, ANormDOk ok a = true) :
    ∀ k, (aNormTArgs args k).2.2 ≤ K → ∀ (g : Env) (fuel : Nat) (e₁ e₂ s₂ : Env)
      (vals : List Value), ARel K k g e₁ e₂ →
      (denoteArgs' bi fuel args).run e₂ = (some vals, s₂) →
      ∃ s₁, ARel K k g s₁ s₂ ∧
        (∀ B, (denote' bi fuel (prependBindings (aNormTArgs args k).1 B)).run e₁ =
          (denote' bi fuel B).run s₁) ∧
        (denoteArgs' bi fuel (aNormTArgs args k).2.1).run s₁ = (some vals, s₁) := by
  induction args with
  | nil =>
    intro k _ g fuel e₁ e₂ s₂ vals hR hr
    rw [args_nil_run] at hr
    cases hr
    exact ⟨e₁, hR, fun B => rfl, args_nil_run bi fuel e₁⟩
  | cons a rest ihr =>
    intro k hK g fuel e₁ e₂ s₂ vals hR hr
    simp only [argsOrderOk, Bool.and_eq_true] at hOrd
    have ihr' := ihr (fun b hb => ih b (List.mem_cons_of_mem _ hb)) hOrd.2
      (fun b hb => hA b (List.mem_cons_of_mem _ hb))
    obtain ⟨w, m₂, rv, h1, hw, h2, rfl⟩ := args_cons_some bi fuel hr
    by_cases hv : isVar a = true
    · obtain ⟨x, rfl⟩ := isVar_eq_true hv
      simp only [aNormTArgs, hv, ite_true] at hK ⊢
      rw [var_run] at h1
      have hx : e₂ x = some w ∧ m₂ = e₂ := by
        cases hex : e₂ x with
        | none => rw [hex] at h1; cases h1
        | some u => rw [hex] at h1; cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hx, rfl⟩ := hx
      obtain ⟨s₁, hR', hB, hD⟩ := ihr' k hK g fuel e₁ m₂ s₂ rv hR h2
      have hkeep := denoteArgs'_keeps bi fuel rest hOrd.1 m₂ rv s₂ h2
      have hxok : ¬ AnormBelow K x := hok x (by simpa [ANormDOk] using hA _ List.mem_cons_self)
      refine ⟨s₁, hR', fun B => by simpa using hB B, ?_⟩
      refine args_cons_of bi fuel ?_ hw hD
      rw [var_run, hR'.read hxok, hkeep, hx]
    · have hvf : isVar a = false := by simpa using hv
      rcases hr1 : aNormTBody a k with ⟨r1, r2⟩
      simp only [aNormTArgs, hvf, hr1, Bool.false_eq_true, ite_false] at hK ⊢
      have hr2K : r2 + 1 ≤ K :=
        Nat.le_trans (aNormTArgs_le_of rest (fun b _ => aNormTBody_le b) (r2 + 1)) hK
      have hkr : k ≤ r2 := by have := aNormTBody_le a k; rw [hr1] at this; exact this
      have iha := ih a List.mem_cons_self k (by rw [hr1]; omega) g fuel
      rw [hr1] at iha
      obtain ⟨m₁, ht1, hRm⟩ := iha e₁ e₂ hR _ m₂ h1 (by rintro ⟨_, h'⟩; cases h')
      have hR0 : ARel K (r2 + 1) (m₁.extend (anormName r2) w) (m₁.extend (anormName r2) w) m₂ :=
        ⟨hRm.1.extend_right (anormName_below (by omega)) w, fun _ _ => rfl⟩
      obtain ⟨s₁, hR', hB, hD⟩ := ihr' (r2 + 1) hK _ fuel _ m₂ s₂ rv hR0 h2
      have hs₁ : s₁ (anormName r2) = some w := by
        rw [hR'.2 r2 (Nat.lt_succ_self _), Env.extend_same]
      refine ⟨s₁, ⟨hR'.1, fun j hj => ?_⟩, fun B => ?_, ?_⟩
      · have hne : anormName j ≠ anormName r2 := fun h' => by
          have := anormName_inj h'; omega
        rw [hR'.2 j (by omega), Env.extend_other _ _ _ _ hne]
        exact hRm.2 j hj
      · rw [prependBindings_append, hoistBind_run, letBind_run_plain bi fuel _ _ _ _ _ _ ht1 hw]
        exact hB B
      · refine args_cons_of bi fuel ?_ hw hD
        simp only [hoistAt]
        rw [var_run, hs₁]

/-- A loop bound condition of `ANormDOk` gives the simulation of a bound the normaliser
    binds and keeps the `frameOk` condition of a bound it keeps. -/
theorem ite_bound_sim {c a d : Bool} {P : Prop} (ih : a = true → P)
    (h : (if c = true then a else d) = true) : if c = true then P else d = true := by
  cases c
  · simpa using h
  · simpa using ih (by simpa using h)

include hok in
/-- **The hoisting pass on a counted loop refines the loop.** For a loop constructor `mk`
    that runs its lower bound, then `anfLoopTail` with the tail `T`, a counter in `ok`, a
    lower bound simulated by its hoisted form when `hoistsLo` holds and in `frameOk ok ok`
    otherwise, the same for the upper bound under `hoistsBound`, and a simulated body, the
    form `loopNorm` refines the loop. -/
theorem loopNorm_denote' (mk : String → ImpExpr → ImpExpr → ImpExpr → ImpExpr)
    (T : Nat → String → ImpExpr → Value → Outcome → StateM Env Outcome)
    (hrun : ∀ fuel v lo hi b env, (denote' bi fuel (mk v lo hi b)).run env =
      ((denote' bi fuel lo) >>= anfLoopTail bi fuel hi (T fuel v b)).run env)
    (hcf : ∀ fuel v b vlo w m o s, w.isControlFlow = true →
      (T fuel v b vlo (.val w)).run m = (o, s) → ¬ IsErr o → o = .val w ∧ s = m)
    (hoth : ∀ fuel v b vlo o m, (∀ w, o ≠ .val w) → (T fuel v b vlo o).run m = (o, m))
    (hrel : ∀ {R : Env → Env → Prop} (v : String) (b₁ b₂ : ImpExpr),
      (∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w)) →
      (∀ fuel, RefE R (denote' bi fuel b₁) (denote' bi fuel b₂)) →
      ∀ fuel vlo rhi, RefE R (T fuel v b₁ vlo rhi) (T fuel v b₂ vlo rhi))
    (v : String) (lo hi b : ImpExpr) (hv : ok v = true)
    (hl : if hoistsLo lo hi = true then ANormDSim bi K lo
      else frameOk ok ok (fun _ => true) lo = true)
    (hh : if hoistsBound hi = true then ANormDSim bi K hi
      else frameOk ok ok (fun _ => true) hi = true)
    (hb : ANormDSim bi K b) :
    ∀ k, (loopNorm mk v lo hi b k).2 ≤ K → ∀ (g : Env) (fuel : Nat),
      RefE (ARel K k g) (denote' bi fuel (loopNorm mk v lo hi b k).1)
        (denote' bi fuel (mk v lo hi b)) := by
  intro k hK g fuel
  have hvx : ∀ {k' : Nat} {g' : Env}, k' ≤ K → ∀ e₁ e₂ w, ARel K k' g' e₁ e₂ →
      ARel K k' g' (e₁.extend v w) (e₂.extend v w) :=
    fun hkK e₁ e₂ w h => h.extend hkK (hok v hv) w
  have hbody : ∀ {k' k'' : Nat} (g' : Env), k' ≤ k'' → (aNormTBody b k'').2 ≤ K →
      ∀ fuel, RefE (ARel K k' g') (denote' bi fuel (aNormTBody b k'').1) (denote' bi fuel b) :=
    fun g' hk hK' fuel => ANormDSim.at bi hb hk hK' g' fuel
  have hcfL : ∀ w m o s, w.isControlFlow = true →
      (anfLoopTail bi fuel hi (T fuel v b) (.val w)).run m = (o, s) → ¬ IsErr o →
      o = .val w ∧ s = m := fun w m o s hw hr _ => by
    simp only [anfLoopTail, hw, ite_true] at hr
    have := Prod.mk.inj (hr : ((Outcome.val w, m) : Outcome × Env) = (o, s))
    exact ⟨this.1.symm, this.2.symm⟩
  have hothL : ∀ o m, (∀ w, o ≠ .val w) → (anfLoopTail bi fuel hi (T fuel v b) o).run m = (o, m) :=
    fun o m ho => by
      cases o with
      | val w => exact absurd rfl (ho w)
      | _ => rfl
  by_cases hlo : hoistsLo lo hi = true
  · rw [ite_eq_left hlo] at hl
    rcases hr1 : aNormTBody lo k with ⟨r1, r2⟩
    have hkr : k ≤ r2 := by have := aNormTBody_le lo k; rw [hr1] at this; exact this
    refine RefR.congr_src ?_ (hrun fuel v lo hi b)
    by_cases hhb : hoistsBound hi = true
    · rw [ite_eq_left hhb] at hh
      rcases hq : aNormTBody hi (r2 + 1) with ⟨q1, q2⟩
      have hrq : r2 + 1 ≤ q2 := by
        have := aNormTBody_le hi (r2 + 1); rw [hq] at this; exact this
      simp only [loopNorm, hlo, hhb, hr1, hq, ite_true] at hK ⊢
      have hqb := aNormTBody_le b (q2 + 1)
      have hlr := hl k (by rw [hr1]; omega) g fuel
      rw [hr1] at hlr
      refine RefR.congr_tgt ?_ (fun env => (congrArg (fun x => (denote' bi fuel x).run env)
        (prependBindings_append _ _ _)).trans (hoistBind_run bi fuel r1 _ r2 env))
      refine letBind_hoist_cont (Rw := fun w e₁ e₂ => ARel K k g e₁ e₂ ∧
          e₁ (anormName r2) = some w)
        (fun e₁ e₂ w h => ⟨h.extend_tmp hkr (by omega) w, Env.extend_same _ _ _⟩) hlr ?_
        hcfL hothL
      intro w hw e₁ e₂ ⟨hR, hs⟩ o s₂ hr hnb
      simp only [anfLoopTail, hw, Bool.false_eq_true, ite_false] at hr
      have hhq := hh (r2 + 1) (by rw [hq]; omega) e₁ fuel
      rw [hq] at hhq
      have key := letBind_hoist_cont (R := ARel K (r2 + 1) e₁) (tmp := anormName q2)
        (C := mk v (hoistAt r1 r2).2 (hoistAt q1 q2).2 (aNormTBody b (q2 + 1)).1)
        (Rw := fun w2 e e' => ARel K (r2 + 1) e₁ e e' ∧ e (anormName q2) = some w2)
        (fun e e' w2 h => ⟨h.extend_tmp hrq (by omega) w2, Env.extend_same _ _ _⟩) hhq
        (fun w2 hw2 e e' hP o' s' hr' hnb' => by
          obtain ⟨hR', ht⟩ := hP
          have hse : e (anormName r2) = some w := by
            rw [hR'.2 r2 (Nat.lt_succ_self _)]; exact hs
          have heq : (denote' bi fuel (mk v (hoistAt r1 r2).2 (hoistAt q1 q2).2
              (aNormTBody b (q2 + 1)).1)).run e =
              (T fuel v (aNormTBody b (q2 + 1)).1 w (.val w2)).run e := by
            simp only [hoistAt]
            rw [hrun, run_bind, var_run, hse]
            simp only [anfLoopTail, hw, Bool.false_eq_true, ite_false]
            rw [run_bind, var_run, ht]
          rw [heq]
          exact hrel v _ b (hvx (by omega)) (hbody e₁ (by omega) hK) fuel w (.val w2)
            e e' hR' o' s' hr' hnb')
        (hcf fuel v b w) (hoth fuel v b w)
      obtain ⟨s₁, h1, hR1⟩ := key e₁ e₂ ⟨hR.1, fun _ _ => rfl⟩ o s₂ hr hnb
      refine ⟨s₁, ?_, hR1.1, fun j hj => (hR1.2 j (by omega)).trans (hR.2 j hj)⟩
      rw [← h1]
      exact hoistBind_run bi fuel q1 _ q2 e₁
    · rw [ite_eq_right hhb] at hh
      have hhf : hoistsBound hi = false := by simpa using hhb
      simp only [loopNorm, hlo, hhf, hr1, ite_true, Bool.false_eq_true, ite_false,
        List.append_nil] at hK ⊢
      have hrb := aNormTBody_le b (r2 + 1)
      have hlr := hl k (by rw [hr1]; omega) g fuel
      rw [hr1] at hlr
      refine RefR.congr_tgt ?_ (hoistBind_run bi fuel r1 _ r2)
      refine letBind_hoist_rel (Tt := anfLoopTail bi fuel hi (T fuel v (aNormTBody b (r2 + 1)).1))
        (fun e₁ e₂ w h => h.extend_tmp hkr (by omega) w) hlr ?_ ?_ hcfL hothL
      · intro env w hw _
        simp only [hoistAt]
        rw [hrun, run_bind, var_run, hw]
      · intro w _
        exact anfLoopTail_rel fuel (refE_frameOk bi hok (by omega) hi hh g fuel)
          (fun vlo rhi => hrel v _ b (hvx (by omega)) (hbody g (by omega) hK) fuel vlo rhi)
          (hoth fuel v b) _
  · rw [ite_eq_right hlo] at hl
    have hlf : hoistsLo lo hi = false := by simpa using hlo
    by_cases hhb : hoistsBound hi = true
    · rw [ite_eq_left hhb] at hh
      obtain ⟨l, rfl⟩ : ∃ l, lo = .lit l := by
        cases lo <;> simp_all [hoistsLo]
      rcases hq : aNormTBody hi k with ⟨q1, q2⟩
      have hkq : k ≤ q2 := by have := aNormTBody_le hi k; rw [hq] at this; exact this
      simp only [loopNorm, hlf, hhb, hq, ite_true, Bool.false_eq_true, ite_false,
        List.nil_append] at hK ⊢
      have hqb := aNormTBody_le b (q2 + 1)
      have hhq := hh k (by rw [hq]; omega) g fuel
      rw [hq] at hhq
      have hl0 := _root_.Hax.Value.ofLit_not_isControlFlow l
      refine RefR.congr_tgt ?_ (hoistBind_run bi fuel q1 _ q2)
      refine RefR.congr_src
        (s₂ := (denote' bi fuel hi) >>= T fuel v b (_root_.Hax.Value.ofLit l)) ?_
        (fun env => (hrun fuel v _ hi b env).trans (by
          rw [run_bind, lit_run]
          simp only [anfLoopTail, hl0, Bool.false_eq_true, ite_false]))
      refine letBind_hoist_rel (Tt := T fuel v (aNormTBody b (q2 + 1)).1 (_root_.Hax.Value.ofLit l))
        (fun e₁ e₂ w h => h.extend_tmp hkq (by omega) w) hhq ?_ ?_
        (hcf fuel v b _) (hoth fuel v b _)
      · intro env w hw _
        simp only [hoistAt]
        rw [hrun, run_bind, lit_run]
        simp only [anfLoopTail, hl0, Bool.false_eq_true, ite_false]
        rw [run_bind, var_run, hw]
      · intro w _
        exact hrel v _ b (hvx (k' := k) (by omega)) (hbody g (by omega) hK) fuel _ _
    · rw [ite_eq_right hhb] at hh
      have hhf : hoistsBound hi = false := by simpa using hhb
      simp only [loopNorm, hlf, hhf, Bool.false_eq_true, ite_false, List.append_nil,
        prependBindings_nil] at hK ⊢
      have hkb := aNormTBody_le b k
      refine RefR.congr_tgt ?_ (hrun fuel v lo hi _)
      refine RefR.congr_src ?_ (hrun fuel v lo hi b)
      refine RefR.bind (refE_frameOk bi hok (by omega) lo hl g fuel) (fun o _ => ?_)
        (fun a ha s => ?_)
      · exact anfLoopTail_rel fuel (refE_frameOk bi hok (by omega) hi hh g fuel)
          (fun vlo rhi => hrel v _ b (hvx (by omega)) (hbody g (Nat.le_refl _) hK) fuel vlo rhi)
          (hoth fuel v b) o
      · obtain ⟨m, rfl⟩ := ha
        exact ⟨m, rfl⟩

include hok in
/-- **The hoisting pass refines `denote'`.** For a program satisfying `ANormDOk ok`, with
    no admissible name among the first `K` fresh names, the hoisted form from every counter
    `k` refines the program under `ARel K k g`. -/
theorem aNormTBody_denote' (e : ImpExpr) : ANormDOk ok e = true → ANormDSim bi K e := by
  have fr : ∀ {k : Nat}, k ≤ K → ∀ x, frameOk ok ok (fun _ => true) x = true →
      ∀ (g : Env) (fuel : Nat), RefE (ARel K k g) (denote' bi fuel x) (denote' bi fuel x) :=
    fun hkK x hx g fuel => refE_frameOk bi hok hkK x hx g fuel
  have ext : ∀ {k : Nat} {g : Env}, k ≤ K → ∀ n, ok n = true → ∀ e₁ e₂ w,
      ARel K k g e₁ e₂ → ARel K k g (e₁.extend n w) (e₂.extend n w) :=
    fun hkK n hn e₁ e₂ w h => h.extend hkK (hok n hn) w
  induction e using ImpExpr.ind with
  | lit l =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact fr hK _ rfl g fuel
  | unitVal =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact fr hK _ rfl g fuel
  | continue_ =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact fr hK _ rfl g fuel
  | break_none =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact fr hK _ rfl g fuel
  | var n =>
    intro hD k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact fr hK _ (by simpa [ANormDOk, frameOk] using hD) g fuel
  | lam ps b _ =>
    intro _ k _ g fuel
    exact RefR.of_bad fun _ => by simp only [denote']; exact ⟨_, rfl⟩
  | match_ => intro hD; simp [ANormDOk] at hD
  | typeAscription e ty ih =>
    intro hD k hK g fuel
    simp only [ANormDOk] at hD
    simp only [aNormTBody] at hK ⊢
    exact RefR.congr_src (ih hD k hK g fuel) (fun env => by simp only [denote'])
  | proj e _ ih | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih =>
    intro hD k hK g fuel
    simp only [ANormDOk] at hD
    simp only [aNormTBody] at hK ⊢
    have h := ANormDSim.at bi (ih hD) (k := k) (k' := k) (Nat.le_refl _) hK g
    simp only [denote']
    rel_step
  | assign n r ih =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkr := aNormTBody_le r k
    have h := ANormDSim.at bi (ih hD.2) (k := k) (k' := k) (Nat.le_refl _) hK g
    have hn := ext (k := k) (g := g) (by omega) n hD.1
    simp only [denote']
    rel_step
  | seq a b iha ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hka := aNormTBody_le a k
    have hab := aNormTBody_le b (aNormTBody a k).2
    have h1 := ANormDSim.at bi (iha hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSim.at bi (ihb hD.2) hka hK g
    simp only [denote']
    rel_step
  | whileLoop c b ihc ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkc := aNormTBody_le c k
    have hcb := aNormTBody_le b (aNormTBody c k).2
    have h1 := ANormDSim.at bi (ihc hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSim.at bi (ihb hD.2) hkc hK g
    simp only [denote']
    exact whileOrig'_rel h1 h2 fuel
  | whileFold c b ihc ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkc := aNormTBody_le c k
    have hcb := aNormTBody_le b (aNormTBody c k).2
    have h1 := ANormDSim.at bi (ihc hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSim.at bi (ihb hD.2) hkc hK g
    simp only [denote']
    exact while'_rel h1 h2 fuel
  | whileFoldReturn c b ihc ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkc := aNormTBody_le c k
    have hcb := aNormTBody_le b (aNormTBody c k).2
    have h1 := ANormDSim.at bi (ihc hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSim.at bi (ihb hD.2) hkc hK g
    simp only [denote']
    exact while'Return_rel h1 h2 fuel
  | letBind n v b ihv ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkv := aNormTBody_le v k
    have hvb := aNormTBody_le b (aNormTBody v k).2
    have hv := ANormDSim.at bi (ihv hD.1.2) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have hb := ANormDSim.at bi (ihb hD.2) hkv hK g
    have hn := ext (k := k) (g := g) (by omega) n hD.1.1
    refine RefR.congr_tgt ?_ (letBindNorm_run bi fuel n _ _)
    simp only [denote']
    rel_step
  | app f args ih =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    intro e₁ e₂ hR o s₂ hr hnb
    rw [app_run] at hr
    rcases hd : (denoteArgs' bi fuel args).run e₂ with ⟨ov, m⟩
    rw [hd] at hr
    rcases ov with _ | vals
    · exact absurd ⟨_, (Prod.mk.inj hr).1.symm⟩ hnb
    obtain ⟨s₁, hR', hB, hD'⟩ := aNormTArgs_denote' bi hok args
      (fun a ha => ih a ha (ANormDOkList_mem hD.2 a ha)) hD.1 (ANormDOkList_mem hD.2) k hK g
      fuel e₁ e₂ m vals hR hd
    have ht := hB (.app f (aNormTArgs args k).2.1)
    rw [app_run, hD'] at ht
    dsimp only at hr ht
    rcases hf : bi f vals with _ | v <;> simp only [hf] at hr ht <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr <;> exact ⟨s₁, ht, hR'⟩
  | tuple es ih =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    intro e₁ e₂ hR o s₂ hr hnb
    rw [tuple_run] at hr
    rcases hd : (denoteArgs' bi fuel es).run e₂ with ⟨ov, m⟩
    rw [hd] at hr
    rcases ov with _ | vals
    · exact absurd ⟨_, (Prod.mk.inj hr).1.symm⟩ hnb
    obtain ⟨s₁, hR', hB, hD'⟩ := aNormTArgs_denote' bi hok es
      (fun a ha => ih a ha (ANormDOkList_mem hD.2 a ha)) hD.1 (ANormDOkList_mem hD.2) k hK g
      fuel e₁ e₂ m vals hR hd
    have ht := hB (.tuple (aNormTArgs es k).2.1)
    rw [tuple_run, hD'] at ht
    dsimp only at hr ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    exact ⟨s₁, ht, hR'⟩
  | ifThenElse c t e ihc iht ihe =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    by_cases hv : isVar c = true
    · obtain ⟨x, rfl⟩ := isVar_eq_true hv
      simp only [aNormTBody, hv, ite_true, prependBindings_nil] at hK ⊢
      have hkt := aNormTBody_le t k
      have hte := aNormTBody_le e (aNormTBody t k).2
      have h1 := fr (k := k) (by omega) (.var x) (by simpa [ANormDOk, frameOk] using hD.1.1) g
      have h2 := ANormDSim.at bi (iht hD.1.2) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
      have h3 := ANormDSim.at bi (ihe hD.2) hkt hK g
      refine RefR.congr_tgt ?_ (ifThenElse_run_tail bi fuel _ _ _)
      refine RefR.congr_src ?_ (ifThenElse_run_tail bi fuel _ _ _)
      exact RefR.bind (badα := IsErr) (h1 fuel)
        (fun o _ => iteTail_rel fuel (h2 fuel) (h3 fuel) o)
        (fun a ha s => by obtain ⟨m, rfl⟩ := ha; exact ⟨m, rfl⟩)
    · have hvf : isVar c = false := by simpa using hv
      rcases hr1 : aNormTBody c k with ⟨r1, r2⟩
      simp only [aNormTBody, hvf, hr1, Bool.false_eq_true, ite_false] at hK ⊢
      have hkr : k ≤ r2 := by have := aNormTBody_le c k; rw [hr1] at this; exact this
      have hrt := aNormTBody_le t (r2 + 1)
      have hte := aNormTBody_le e (aNormTBody t (r2 + 1)).2
      have hc := ihc hD.1.1 k (by rw [hr1]; omega) g fuel
      rw [hr1] at hc
      have h2 := ANormDSim.at bi (iht hD.1.2) (k := k) (k' := r2 + 1) (by omega) (by omega) g
        fuel
      have h3 := ANormDSim.at bi (ihe hD.2) (k := k) (by omega) hK g fuel
      refine RefR.congr_tgt ?_ (hoistBind_run bi fuel r1 _ r2)
      refine RefR.congr_src ?_ (ifThenElse_run_tail bi fuel c t e)
      refine letBind_hoist_rel (Tt := iteTail bi fuel (aNormTBody t (r2 + 1)).1
          (aNormTBody e (aNormTBody t (r2 + 1)).2).1)
        (fun e₁ e₂ w h => h.extend_tmp hkr (by omega) w) hc ?_ ?_ (iteTail_cf bi fuel t e)
        (iteTail_other bi fuel t e)
      · intro env w hw _
        simp only [hoistAt]
        rw [ifThenElse_run_tail, run_bind, var_run, hw]
      · intro w _
        exact iteTail_rel fuel h2 h3 _
  | forLoop v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forLoop_loopNorm] at hK ⊢
    exact loopNorm_denote' bi hok .forLoop (fun fuel v b => forTailOrig bi fuel v b)
      (fun fuel v lo hi b env => forLoop_run_tail bi fuel v b lo hi env)
      (fun fuel v b => forTailOrig_cf bi fuel v b) (fun fuel v b => forTailOrig_other bi fuel v b)
      (fun _ _ _ hv h fuel => forTailOrig_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forFold v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forFold_loopNorm] at hK ⊢
    exact loopNorm_denote' bi hok .forFold (fun fuel v b => forTailFold bi fuel v b)
      (fun fuel v lo hi b env => forFold_run_tail bi fuel v b lo hi env)
      (fun fuel v b => forTailFold_cf bi fuel v b) (fun fuel v b => forTailFold_other bi fuel v b)
      (fun _ _ _ hv h fuel => forTailFold_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forLoopRev_loopNorm] at hK ⊢
    exact loopNorm_denote' bi hok .forLoopRev (fun fuel v b => forTailRevOrig bi fuel v b)
      (fun fuel v lo hi b env => forLoopRev_run_tail bi fuel v b lo hi env)
      (fun fuel v b => forTailRevOrig_cf bi fuel v b)
      (fun fuel v b => forTailRevOrig_other bi fuel v b)
      (fun _ _ _ hv h fuel => forTailRevOrig_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forFoldRev_loopNorm] at hK ⊢
    exact loopNorm_denote' bi hok .forFoldRev (fun fuel v b => forTailFoldRev bi fuel v b)
      (fun fuel v lo hi b env => forFoldRev_run_tail bi fuel v b lo hi env)
      (fun fuel v b => forTailFoldRev_cf bi fuel v b)
      (fun fuel v b => forTailFoldRev_other bi fuel v b)
      (fun _ _ _ hv h fuel => forTailFoldRev_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forFoldReturn v lo hi b _ _ ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkb := aNormTBody_le b k
    have hl := fr (k := k) (by omega) lo hD.1.1.2 g
    have hhi := fr (k := k) (by omega) hi hD.1.2 g
    have hb := ANormDSim.at bi (ihb hD.2) (k := k) (k' := k) (Nat.le_refl _) hK g
    have hvx := ext (k := k) (g := g) (by omega) v hD.1.1.1
    have := forLoop'Return_rel (bi₁ := bi) (bi₂ := bi) hvx hb
    simp only [denote']
    rel_step
  | forFoldRevReturn v lo hi b _ _ ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkb := aNormTBody_le b k
    have hl := fr (k := k) (by omega) lo hD.1.1.2 g
    have hhi := fr (k := k) (by omega) hi hD.1.2 g
    have hb := ANormDSim.at bi (ihb hD.2) (k := k) (k' := k) (Nat.le_refl _) hK g
    have hvx := ext (k := k) (g := g) (by omega) v hD.1.1.1
    have := forLoopRev'Return_rel (bi₁ := bi) (bi₂ := bi) hvx hb
    simp only [denote']
    rel_step

end Sim

/-! ## §6  Tail binding and the composed pass -/

section Tails

variable (bi : Builtins) (fuel : Nat)

theorem bindTail_denote' (e : ImpExpr) (env : Env) (o : Outcome) (s : Env)
    (h : (denote' bi fuel e).run env = (o, s)) :
    ∃ s', (denote' bi fuel
      (if isTailBindable e then .letBind retName e (.var retName) else e)).run env = (o, s') := by
  split
  · rw [letBind_run, h]
    rcases o with w | _ | _ | _ | _
    · cases w
      case controlFlow b u => exact ⟨s, rfl⟩
      all_goals exact ⟨_, by dsimp only; rw [var_run, Env.extend_same]⟩
    all_goals exact ⟨s, rfl⟩
  · exact ⟨s, h⟩

/-- **Tail binding preserves every run** of `denote'`, up to the final environment. -/
theorem bindTails_denote' (e : ImpExpr) :
    ∀ (env : Env) (o : Outcome) (s : Env), (denote' bi fuel e).run env = (o, s) →
      ∃ s', (denote' bi fuel (bindTails e)).run env = (o, s') := by
  induction e using ImpExpr.ind
  case letBind n v b _ ihb =>
    intro env o s h
    simp only [bindTails]
    rw [letBind_run] at h ⊢
    rcases hs : (denote' bi fuel v).run env with ⟨o1, e1⟩
    rw [hs] at h
    rcases o1 with w | _ | _ | _ | _
    · cases w
      case controlFlow => exact ⟨s, h⟩
      all_goals exact ihb _ _ _ h
    all_goals exact ⟨s, h⟩
  case seq a b _ ihb =>
    intro env o s h
    simp only [bindTails]
    rw [seq_run] at h ⊢
    rcases hs : (denote' bi fuel a).run env with ⟨o1, e1⟩
    rw [hs] at h
    rcases o1 with w | _ | _ | _ | _
    · cases w
      case controlFlow => exact ⟨s, h⟩
      all_goals exact ihb _ _ _ h
    all_goals exact ⟨s, h⟩
  case ifThenElse c t e _ iht ihe =>
    intro env o s h
    simp only [bindTails]
    rw [ifThenElse_run] at h ⊢
    rcases hs : (denote' bi fuel c).run env with ⟨o1, e1⟩
    rw [hs] at h
    rcases o1 with w | _ | _ | _ | _
    · cases w
      case bool b => cases b; exact ihe _ _ _ h; exact iht _ _ _ h
      all_goals exact ⟨s, h⟩
    all_goals exact ⟨s, h⟩
  all_goals
    intro env o s h
    exact bindTail_denote' bi fuel _ env o s h

/-- **`aNormalizeTotal` refines `denote'`.** Under `aNormTDenoteOk e`, every run of
    `denote' bi fuel e` from `env` whose outcome is not an error is matched by a run of
    `denote' bi fuel (aNormalizeTotal e)` from `env` to the same outcome. -/
theorem aNormalizeTotal_denote' (e : ImpExpr) (h : aNormTDenoteOk e = true) (env : Env)
    (o : Outcome) (s : Env) (hr : (denote' bi fuel e).run env = (o, s)) (ho : ¬ IsErr o) :
    ∃ s', (denote' bi fuel (aNormalizeTotal e)).run env = (o, s') := by
  obtain ⟨s₁, h₁⟩ := bindTails_denote' bi fuel e env o s hr
  have hok : ∀ n, (fun n => (List.range (aNormalizeTotalCount e)).all
      (fun j => n != anormName j)) n = true → ¬ AnormBelow (aNormalizeTotalCount e) n := by
    rintro n hn ⟨j, hj, rfl⟩
    simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hn
    exact hn j hj rfl
  obtain ⟨s', h', _⟩ := aNormTBody_denote' bi hok (bindTails e) h 0 (Nat.le_refl _) env fuel env env
    ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ o s₁ h₁ ho
  exact ⟨s', h'⟩

end Tails

/-- From `env`, every run of `e` to a value is matched, at some fuel, by a run of
    `aNormalizeTotal e` to the same outcome. -/
def AnfSoundAt (bi : Builtins) (e : ImpExpr) (env : Env) : Prop :=
  ∀ fuel o env', (denote' bi fuel e).run env = (o, env') → (∃ v, o = .val v) →
    ∃ fuel' env'', (denote' bi fuel' (aNormalizeTotal e)).run env = (o, env'')

/-- A body that `aNormalizeTotal` leaves unchanged satisfies `AnfSoundAt`. -/
theorem anfSoundAt_of_eq (bi : Builtins) (e : ImpExpr) (env : Env)
    (h : aNormalizeTotal e = e) : AnfSoundAt bi e env := by
  intro fuel o env' hr _
  exact ⟨fuel, env', by rw [h]; exact hr⟩

/-- A body satisfying `aNormTDenoteOk` satisfies `AnfSoundAt` at every environment, at the
    same fuel. -/
theorem anfSoundAt_of_aNormTDenoteOk (bi : Builtins) (e : ImpExpr) (env : Env)
    (h : aNormTDenoteOk e = true) : AnfSoundAt bi e env := by
  intro fuel o env' hr hv
  obtain ⟨s, hs⟩ := aNormalizeTotal_denote' bi fuel e h env o env' hr
    (by rintro ⟨m, rfl⟩; obtain ⟨v, hv⟩ := hv; cases hv)
  exact ⟨fuel, s, hs⟩

end CatCrypt.Crypto.Hax
