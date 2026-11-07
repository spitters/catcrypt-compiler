/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds
public import HaxLean.DenoteTotal
public import HaxLean.Phase.InlineLocalClosures
public import CatCrypt.Crypto.Hax.Hax64Table

@[expose] public section

set_option autoImplicit false

/-!
# A derived bound loses no source run

`DeriveBounds.deriveBounds` bounds a scalar parameter `p` by a cap read off the body: the trip
count of a counted loop `for i in lo..p` whose every trip reaches an access `a[i + c]` of an
array variable of known length, or an access `a[p]` on the statement spine. This module proves
that the bound holds at every valuation at which the body denotes a value: if `p` exceeded a
cap, the run would reach an access at an index at or beyond the length of its array, which the
source semantics makes a panic (`err`).

The proof holds for every builtin table with four properties (`SiteTable`): no call returns a
control-flow value, `index` and `array_update` fail at an index at or beyond the length, and
the checked additions of `checkedAdd` add exactly.

## Main definitions

* `SiteTable` — the properties of the table the proof uses.
* `LensIn` — a table of array lengths holds in an environment.

## Main results

* `cfFree_run` — a node with `cfFree` returns no control-flow value and changes the
  environment only at the names it binds (`writes`).
* `strictCaps_fail` — a trip at a counter at or beyond a cap of its body returns no value.
* `capsOf_fail` — a run past a cap of `p` along the spine returns no value that is not a
  control-flow value.
* `le_of_mem_capsOf` — at every run to a value, `p` is at most each of its caps.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds

open _root_.Hax (TExpr TExprKind ImpExpr ImpLit ImpType Value Env Builtins Outcome denote'
  denoteArgs' denoteForLoop')

/-- **The properties of a builtin table the bound derivation uses**: no call returns a
    control-flow value, `index` and `array_update` fail at an index at or beyond the length
    of the array, and a checked addition (`checkedAdd`) on two integers that returns a value
    returns their sum. -/
structure SiteTable (bi : Builtins) : Prop where
  /-- No call returns a control-flow value. -/
  noCF : ∀ f vs r, bi f vs = some r → r.isControlFlow = false
  /-- `index` fails at or beyond the length. -/
  index_oob : ∀ (vs : List Value) (k : Int), (vs.length : Int) ≤ k →
    bi "index" [.array vs, .int k] = none
  /-- `array_update` fails at or beyond the length. -/
  update_oob : ∀ (vs : List Value) (k : Int) (w : Value), (vs.length : Int) ≤ k →
    bi "array_update" [.array vs, .int k, w] = none
  /-- A checked addition adds. -/
  add : ∀ (f : String) (a c : Int) (r : Value), checkedAdd f = true →
    bi f [.int a, .int c] = some r → r = .int (a + c)

/-- No name of the environment holds a control-flow value. -/
def NoCFEnv (env : Env) : Prop := ∀ y w, env y = some w → w.isControlFlow = false

/-- **The table of lengths `K` holds in `env`**: each name of `K` holds an array of its
    length. -/
def LensIn (K : List (String × Nat)) (env : Env) : Prop :=
  ∀ x L, List.lookup x K = some L → ∃ vs, env x = some (.array vs) ∧ vs.length = L

/-- An outcome that is a value is no control-flow value. -/
def Good (r : Outcome) : Prop := ∀ w, r = .val w → w.isControlFlow = false

/-! ## Tables of lengths -/

theorem lookup_dropW {K : List (String × Nat)} {ws : List String} {x : String} {L : Nat}
    (h : List.lookup x (dropW K ws) = some L) :
    List.lookup x K = some L ∧ ws.contains x = false := by
  induction K with
  | nil => simp [dropW] at h
  | cons q K ih =>
      obtain ⟨y, l⟩ := q
      by_cases hy : y ∈ ws
      · replace h : List.lookup x (dropW K ws) = some L := by
          simpa [dropW, List.filter_cons, hy] using h
        obtain ⟨h1, h2⟩ := ih h
        have hxy : x ≠ y := by
          rintro rfl
          simp [hy] at h2
        refine ⟨?_, h2⟩
        have hb : (x == y) = false := by simpa using hxy
        simp only [List.lookup, hb, h1]
      · replace h : List.lookup x ((y, l) :: dropW K ws) = some L := by
          simpa [dropW, List.filter_cons, hy] using h
        by_cases hxy : x = y
        · subst hxy
          simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h ⊢
          exact ⟨h, by simpa using hy⟩
        · have hb : (x == y) = false := by simpa using hxy
          simp only [List.lookup, hb] at h ⊢
          exact ih h

/-- Lengths not among the names `ws` survive a step that changes only names among `ws`. -/
theorem LensIn.dropW {K : List (String × Nat)} {env env' : Env} {ws : List String}
    (h : LensIn K env) (hf : ∀ x, ws.contains x = false → env' x = env x) :
    LensIn (DeriveBounds.dropW K ws) env' := by
  intro x L hx
  obtain ⟨h1, h2⟩ := lookup_dropW hx
  rw [hf x h2]
  exact h x L h1

theorem NoCFEnv.extend {env : Env} (h : NoCFEnv env) (x : String) {w : Value}
    (hw : w.isControlFlow = false) : NoCFEnv (Env.extend env x w) := by
  intro y u hy
  simp only [Env.extend] at hy
  split at hy
  · cases hy
    exact hw
  · exact h y u hy

theorem extend_apply_of_ne {env : Env} {x y : String} {w : Value} (h : y ≠ x) :
    Env.extend env x w y = env y := by
  simp [Env.extend, h]

theorem extend_apply_self {env : Env} {x : String} {w : Value} :
    Env.extend env x w x = some w := by
  simp [Env.extend]

/-! ## One-step evaluation -/

theorem denoteArgs'_cons_unfold (bi : Builtins) (fuel : Nat) (e : ImpExpr) (es : List ImpExpr)
    (env : Env) :
    denoteArgs' bi fuel (e :: es) env =
      match denote' bi fuel e env with
      | (.val (.controlFlow _ _), env') => (none, env')
      | (.val w, env') =>
          ((denoteArgs' bi fuel es env').1.map (w :: ·), (denoteArgs' bi fuel es env').2)
      | (_, env') => (none, env') := by
  conv => lhs; unfold denoteArgs'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel e env = q
  obtain ⟨r, env'⟩ := q
  cases r <;> try rfl
  rename_i w; cases w <;> rfl

theorem denoteArgs'_cons_of_val' {bi : Builtins} {fuel : Nat} {e : ImpExpr}
    {es : List ImpExpr} {env env1 : Env} {w : Value}
    (he : denote' bi fuel e env = (.val w, env1)) (hw : w.isControlFlow = false) :
    denoteArgs' bi fuel (e :: es) env =
      ((denoteArgs' bi fuel es env1).1.map (w :: ·), (denoteArgs' bi fuel es env1).2) := by
  rw [denoteArgs'_cons_unfold, he]
  cases w <;> first | rfl | simp [Value.isControlFlow] at hw

theorem denoteArgs'_cons_of_nonval {bi : Builtins} {fuel : Nat} {e : ImpExpr}
    {es : List ImpExpr} {env env1 : Env} {r : Outcome}
    (he : denote' bi fuel e env = (r, env1)) (hr : ∀ w, r = .val w → w.isControlFlow = true) :
    denoteArgs' bi fuel (e :: es) env = (none, env1) := by
  rw [denoteArgs'_cons_unfold, he]
  cases r with
  | val w =>
      have := hr w rfl
      cases w <;> first | rfl | simp [Value.isControlFlow] at this
  | _ => rfl

theorem denote'_app_unfold (bi : Builtins) (fuel : Nat) (f : String) (args : List ImpExpr)
    (env : Env) :
    denote' bi fuel (.app f args) env =
      ((match (denoteArgs' bi fuel args env).1 with
        | some vals =>
            match bi f vals with
            | some v => Outcome.val v
            | none => Outcome.err s!"unknown function or bad args: {f}"
        | none => Outcome.err "non-value in function arguments"),
        (denoteArgs' bi fuel args env).2) := by
  conv => lhs; unfold denote'
  unfold _root_.Hax.denoteApp'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denoteArgs' bi fuel args env = q
  obtain ⟨r, env'⟩ := q
  cases r with
  | none => rfl
  | some vals => rcases hb : bi f vals with _ | v <;> simp [hb] <;> rfl

theorem denote'_tuple_run (bi : Builtins) (fuel : Nat) (es : List ImpExpr) (env : Env) :
    denote' bi fuel (.tuple es) env =
      ((match (denoteArgs' bi fuel es env).1 with
        | some vals => Outcome.val (.tuple vals)
        | none => Outcome.err "non-value in tuple elements"),
        (denoteArgs' bi fuel es env).2) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denoteArgs' bi fuel es env = q
  obtain ⟨r, env'⟩ := q
  cases r <;> rfl

theorem denote'_letBind_of_nonval {bi : Builtins} {fuel : Nat} {x : String} {v b : ImpExpr}
    {env env1 : Env} {r : Outcome} (hv : denote' bi fuel v env = (r, env1))
    (hr : ∀ w, r = .val w → w.isControlFlow = true) :
    denote' bi fuel (.letBind x v b) env = (r, env1) := by
  rw [_root_.Hax.denote'_letBind_run, hv]
  cases r with
  | val w =>
      have := hr w rfl
      cases w <;> first | rfl | simp [Value.isControlFlow] at this
  | _ => rfl

theorem denote'_seq_of_nonval {bi : Builtins} {fuel : Nat} {a b : ImpExpr}
    {env env1 : Env} {r : Outcome} (ha : denote' bi fuel a env = (r, env1))
    (hr : ∀ w, r = .val w → w.isControlFlow = true) :
    denote' bi fuel (.seq a b) env = (r, env1) := by
  rw [_root_.Hax.denote'_seq_run, ha]
  cases r with
  | val w =>
      have := hr w rfl
      cases w <;> first | rfl | simp [Value.isControlFlow] at this
  | _ => rfl

/-- The outcome of a conditional whose condition returns no value that is not a control-flow
    value is the outcome of its condition. -/
theorem denote'_ite_of_nonval {bi : Builtins} {fuel : Nat} {c t e : ImpExpr}
    {env env1 : Env} {r : Outcome} (hc : denote' bi fuel c env = (r, env1))
    (hr : ∀ w, r = .val w → w.isControlFlow = true) :
    denote' bi fuel (.ifThenElse c t e) env = (r, env1) := by
  rw [_root_.Hax.denote'_ifThenElse_run, hc]
  cases r with
  | val w =>
      have := hr w rfl
      cases w <;> first | rfl | simp [Value.isControlFlow] at this
  | _ => rfl

/-- A conditional whose condition returns a value that is not a control-flow value returns
    an error or the outcome of one of its arms from the environment after the condition. -/
theorem denote'_ite_of_val {bi : Builtins} {fuel : Nat} {c t e : ImpExpr}
    {env env1 : Env} {w : Value} (hc : denote' bi fuel c env = (.val w, env1))
    (hw : w.isControlFlow = false) :
    denote' bi fuel (.ifThenElse c t e) env = denote' bi fuel t env1 ∨
      denote' bi fuel (.ifThenElse c t e) env = denote' bi fuel e env1 ∨
      denote' bi fuel (.ifThenElse c t e) env = (.err "if condition not a bool", env1) := by
  rw [_root_.Hax.denote'_ifThenElse_run, hc]
  cases w with
  | bool b => cases b <;> simp
  | controlFlow => simp [Value.isControlFlow] at hw
  | _ => simp

theorem denote'_forFold_of_lo {bi : Builtins} {fuel : Nat} {x : String}
    {lo hi body : ImpExpr} {env env1 : Env} {r : Outcome}
    (hlo : denote' bi fuel lo env = (r, env1)) (hr : ∀ w, r = .val w → w.isControlFlow = true) :
    denote' bi fuel (.forFold x lo hi body) env = (r, env1) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rw [hlo]
  cases r with
  | val w =>
      have := hr w rfl
      cases w <;> first | rfl | simp [Value.isControlFlow] at this
  | _ => rfl

/-- A counted loop whose lower bound returns a value that is not a control-flow value runs
    its loop at the integer bounds, or returns an error or the outcome of the upper bound,
    from the environment after the upper bound. -/
theorem denote'_forFold_of_hi {bi : Builtins} {fuel : Nat} {x : String}
    {lo hi body : ImpExpr} {env env1 env2 : Env} {vlo : Value} {r : Outcome}
    (hlo : denote' bi fuel lo env = (.val vlo, env1)) (hcf : vlo.isControlFlow = false)
    (hhi : denote' bi fuel hi env1 = (r, env2)) :
    (∃ l h, denote' bi fuel (.forFold x lo hi body) env =
        denoteForLoop' bi fuel x l h body env2) ∨
      (∃ s, denote' bi fuel (.forFold x lo hi body) env = (.err s, env2)) ∨
      denote' bi fuel (.forFold x lo hi body) env = (r, env2) := by
  unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rw [hlo]
  cases vlo with
  | controlFlow => simp [Value.isControlFlow] at hcf
  | int l =>
      dsimp only [StateT.bind]
      rw [hhi]
      cases r with
      | val vh =>
          cases vh
          case int => exact .inl ⟨_, _, rfl⟩
          case uint => exact .inl ⟨_, _, rfl⟩
          case controlFlow => exact .inr (.inr rfl)
          all_goals exact .inr (.inl ⟨_, rfl⟩)
      | _ => exact .inr (.inr rfl)
  | uint w l =>
      dsimp only [StateT.bind]
      rw [hhi]
      cases r with
      | val vh =>
          cases vh
          case int => exact .inl ⟨_, _, rfl⟩
          case uint => exact .inl ⟨_, _, rfl⟩
          case controlFlow => exact .inr (.inr rfl)
          all_goals exact .inr (.inl ⟨_, rfl⟩)
      | _ => exact .inr (.inr rfl)
  | _ =>
      dsimp only [StateT.bind]
      rw [hhi]
      cases r with
      | val vh =>
          cases vh
          case controlFlow => exact .inr (.inr rfl)
          all_goals exact .inr (.inl ⟨_, rfl⟩)
      | _ => exact .inr (.inr rfl)

theorem denoteForLoop'_stop (bi : Builtins) (fuel : Nat) (x : String) {lo hi : Int}
    (body : ImpExpr) (env : Env) (h : lo ≥ hi) :
    denoteForLoop' bi fuel x lo hi body env = (.val .unit, env) := by
  rw [denoteForLoop', ite_eq_left h]
  rfl

theorem denoteForLoop'_zero (bi : Builtins) (x : String) {lo hi : Int}
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    denoteForLoop' bi 0 x lo hi body env = (.err "out of fuel", env) := by
  rw [denoteForLoop', ite_eq_right (by omega), ite_eq_left rfl]
  rfl

theorem denoteForLoop'_of_val {bi : Builtins} {fuel : Nat} {x : String} {lo hi : Int}
    {body : ImpExpr} {env env1 : Env} {w : Value} (h : lo < hi) (hf : fuel ≠ 0)
    (hb : denote' bi fuel body (Env.extend env x (.int lo)) = (.val w, env1))
    (hw : w.isControlFlow = false) :
    denoteForLoop' bi fuel x lo hi body env =
      denoteForLoop' bi (fuel - 1) x (lo + 1) hi body env1 := by
  rw [denoteForLoop', ite_eq_right (by omega), ite_eq_right hf]
  dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
  rw [hb]
  cases w <;> first | rfl | simp [Value.isControlFlow] at hw

theorem denoteForLoop'_of_nonval {bi : Builtins} {fuel : Nat} {x : String} {lo hi : Int}
    {body : ImpExpr} {env env1 : Env} {r : Outcome} (h : lo < hi) (hf : fuel ≠ 0)
    (hb : denote' bi fuel body (Env.extend env x (.int lo)) = (r, env1))
    (hr : ∀ w, r ≠ .val w) :
    denoteForLoop' bi fuel x lo hi body env = (r, env1) := by
  rw [denoteForLoop', ite_eq_right (by omega), ite_eq_right hf]
  dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
  rw [hb]
  cases r with
  | val w => exact absurd rfl (hr w)
  | _ => rfl

/-! ## Nodes that leave no trip early -/

theorem ofLit_noCF (l : ImpLit) : (Value.ofLit l).isControlFlow = false := by
  cases l <;> rfl

theorem contains_append_false {l₁ l₂ : List String} {y : String}
    (h : (l₁ ++ l₂).contains y = false) : l₁.contains y = false ∧ l₂.contains y = false := by
  simp only [List.contains_append, Bool.or_eq_false_iff] at h
  exact h

theorem contains_cons_false {x y : String} {l : List String} (h : (x :: l).contains y = false) :
    y ≠ x ∧ l.contains y = false := by
  simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  exact h

/-- A counted loop whose body returns no control-flow value and changes the environment only
    at the names `ws` returns no control-flow value and changes the environment only at `ws`
    and its counter. -/
theorem denoteForLoop'_good_frame {bi : Builtins} {x : String} {body : ImpExpr} {ws : List String}
    (hb : ∀ fuel env, NoCFEnv env → Good (denote' bi fuel body env).1 ∧
      NoCFEnv (denote' bi fuel body env).2 ∧
      ∀ y, ws.contains y = false → (denote' bi fuel body env).2 y = env y) :
    ∀ (fuel : Nat) (lo hi : Int) (env : Env), NoCFEnv env →
      Good (denoteForLoop' bi fuel x lo hi body env).1 ∧
      NoCFEnv (denoteForLoop' bi fuel x lo hi body env).2 ∧
      ∀ y, ws.contains y = false → y ≠ x →
        (denoteForLoop' bi fuel x lo hi body env).2 y = env y := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi env henv
      by_cases h : lo ≥ hi
      · rw [denoteForLoop'_stop _ _ _ _ _ h]
        exact ⟨(fun w hw => by cases hw; rfl), henv, fun _ _ _ => rfl⟩
      · rw [denoteForLoop'_zero _ _ _ _ (by omega)]
        exact ⟨(fun w hw => by cases hw), henv, fun _ _ _ => rfl⟩
  | succ n ih =>
      intro lo hi env henv
      by_cases h : lo ≥ hi
      · rw [denoteForLoop'_stop _ _ _ _ _ h]
        exact ⟨(fun w hw => by cases hw; rfl), henv, fun _ _ _ => rfl⟩
      · have h1 : NoCFEnv (Env.extend env x (.int lo)) := henv.extend x rfl
        obtain ⟨g1, n1, f1⟩ := hb (n + 1) _ h1
        rcases hr : denote' bi (n + 1) body (Env.extend env x (.int lo)) with ⟨r, env1⟩
        rw [hr] at g1 n1 f1
        dsimp only at g1 n1 f1
        cases r with
        | val w =>
            rw [denoteForLoop'_of_val (by omega) (by omega) hr (g1 w rfl), Nat.add_sub_cancel]
            obtain ⟨g2, n2, f2⟩ := ih (lo + 1) hi env1 n1
            refine ⟨g2, n2, fun y hy hyx => ?_⟩
            rw [f2 y hy hyx, f1 y hy, extend_apply_of_ne hyx]
        | _ =>
            rw [denoteForLoop'_of_nonval (by omega) (by omega) hr (fun w hw => by cases hw)]
            exact ⟨(fun w hw => by cases hw), n1,
              fun y hy hyx => by dsimp only; rw [f1 y hy, extend_apply_of_ne hyx]⟩

mutual

/-- **A node with `cfFree` returns no control-flow value**, keeps the environment free of
    control-flow values, and changes it only at the names it binds (`writes`). -/
theorem cfFree_run {bi : Builtins} (hbi : SiteTable bi) :
    ∀ (e : TExpr), cfFree e = true → ∀ (fuel : Nat) (env : Env), NoCFEnv env →
      Good (denote' bi fuel e.erase env).1 ∧ NoCFEnv (denote' bi fuel e.erase env).2 ∧
        ∀ y, (writes e).contains y = false → (denote' bi fuel e.erase env).2 y = env y
  | .mk (.lit l) _, _, fuel, env, henv => by
      simp only [TExpr.erase, _root_.Hax.denote'_lit_run]
      exact ⟨(fun w hw => by cases hw; exact ofLit_noCF l), henv, fun _ _ => trivial⟩
  | .mk (.var x) _, _, fuel, env, henv => by
      simp only [TExpr.erase, _root_.Hax.denote'_var_run]
      rcases hx : env x with _ | u
      · exact ⟨(fun w hw => by cases hw), henv, fun _ _ => rfl⟩
      · exact ⟨(fun w hw => by cases hw; exact henv x u hx), henv, fun _ _ => rfl⟩
  | .mk .unitVal _, _, fuel, env, henv => by
      simp only [TExpr.erase, _root_.Hax.denote'_unitVal_run]
      exact ⟨(fun w hw => by cases hw; rfl), henv, fun _ _ => trivial⟩
  | .mk (.app f args) _, h, fuel, env, henv => by
      have ha : cfFreeList args = true := by simpa [cfFree] using h
      obtain ⟨n1, f1⟩ := cfFreeList_run hbi args ha fuel env henv
      simp only [TExpr.erase, TExpr.eraseList_eq, denote'_app_unfold]
      refine ⟨?_, n1, fun y hy => f1 y (by simpa [writes] using hy)⟩
      intro w hw
      revert hw
      rcases (denoteArgs' bi fuel (args.map TExpr.erase) env).1 with _ | vals
      · intro hw; cases hw
      · rcases hb : bi f vals with _ | v
        · simp only [hb]; intro hw; cases hw
        · simp only [hb]; intro hw; cases hw; exact hbi.noCF _ _ _ hb
  | .mk (.tuple es) _, h, fuel, env, henv => by
      have ha : cfFreeList es = true := by simpa [cfFree] using h
      obtain ⟨n1, f1⟩ := cfFreeList_run hbi es ha fuel env henv
      simp only [TExpr.erase, TExpr.eraseList_eq, denote'_tuple_run]
      refine ⟨?_, n1, fun y hy => f1 y (by simpa [writes] using hy)⟩
      intro w hw
      revert hw
      rcases (denoteArgs' bi fuel (es.map TExpr.erase) env).1 with _ | vals
      · intro hw; cases hw
      · intro hw; cases hw; rfl
  | .mk (.letBind x v c) _, h, fuel, env, henv => by
      obtain ⟨hv, hc⟩ : cfFree v = true ∧ cfFree c = true := by simpa [cfFree] using h
      simp only [TExpr.erase]
      obtain ⟨g1, n1, f1⟩ := cfFree_run hbi v hv fuel env henv
      rcases hr : denote' bi fuel v.erase env with ⟨r1, env1⟩
      rw [hr] at g1 n1 f1
      dsimp only at g1 n1 f1
      cases r1 with
      | val w =>
          have hw := g1 w rfl
          rw [_root_.Hax.Total.denote'_letBind_of_val hr hw]
          obtain ⟨g2, n2, f2⟩ := cfFree_run hbi c hc fuel (Env.extend env1 x w) (n1.extend x hw)
          refine ⟨g2, n2, fun y hy => ?_⟩
          obtain ⟨hyx, hy⟩ := contains_cons_false (by simpa only [writes] using hy)
          obtain ⟨hy1, hy2⟩ := contains_append_false hy
          rw [f2 y hy2, extend_apply_of_ne hyx, f1 y hy1]
      | _ =>
          rw [denote'_letBind_of_nonval hr (fun w hw => by cases hw)]
          refine ⟨(fun w hw => by cases hw), n1, fun y hy => ?_⟩
          obtain ⟨-, hy⟩ := contains_cons_false (by simpa only [writes] using hy)
          exact f1 y (contains_append_false hy).1
  | .mk (.seq a b) _, h, fuel, env, henv => by
      obtain ⟨ha, hb⟩ : cfFree a = true ∧ cfFree b = true := by simpa [cfFree] using h
      simp only [TExpr.erase]
      obtain ⟨g1, n1, f1⟩ := cfFree_run hbi a ha fuel env henv
      rcases hr : denote' bi fuel a.erase env with ⟨r1, env1⟩
      rw [hr] at g1 n1 f1
      dsimp only at g1 n1 f1
      cases r1 with
      | val w =>
          rw [_root_.Hax.Total.denote'_seq_of_val hr (g1 w rfl)]
          obtain ⟨g2, n2, f2⟩ := cfFree_run hbi b hb fuel env1 n1
          refine ⟨g2, n2, fun y hy => ?_⟩
          obtain ⟨hy1, hy2⟩ := contains_append_false (by simpa only [writes] using hy)
          rw [f2 y hy2, f1 y hy1]
      | _ =>
          rw [denote'_seq_of_nonval hr (fun w hw => by cases hw)]
          exact ⟨(fun w hw => by cases hw), n1,
            fun y hy => f1 y (contains_append_false (by simpa only [writes] using hy)).1⟩
  | .mk (.ifThenElse c a b) _, h, fuel, env, henv => by
      obtain ⟨⟨hc, ha⟩, hb⟩ : (cfFree c = true ∧ cfFree a = true) ∧ cfFree b = true := by
        simpa [cfFree] using h
      simp only [TExpr.erase]
      obtain ⟨g1, n1, f1⟩ := cfFree_run hbi c hc fuel env henv
      rcases hr : denote' bi fuel c.erase env with ⟨r1, env1⟩
      rw [hr] at g1 n1 f1
      dsimp only at g1 n1 f1
      have hw' : ∀ y, (writes (.mk (.ifThenElse c a b) ‹_›)).contains y = false →
          (writes c).contains y = false ∧ (writes a).contains y = false ∧
            (writes b).contains y = false := by
        intro y hy
        obtain ⟨h1, h2⟩ := contains_append_false (by simpa only [writes] using hy)
        exact ⟨h1, contains_append_false h2⟩
      cases r1 with
      | val w =>
          rcases denote'_ite_of_val (t := a.erase) (e := b.erase) hr (g1 w rfl) with hi | hi | hi
          · rw [hi]
            obtain ⟨g2, n2, f2⟩ := cfFree_run hbi a ha fuel env1 n1
            refine ⟨g2, n2, fun y hy => ?_⟩
            obtain ⟨h1, h2, -⟩ := hw' y hy
            rw [f2 y h2, f1 y h1]
          · rw [hi]
            obtain ⟨g2, n2, f2⟩ := cfFree_run hbi b hb fuel env1 n1
            refine ⟨g2, n2, fun y hy => ?_⟩
            obtain ⟨h1, -, h3⟩ := hw' y hy
            rw [f2 y h3, f1 y h1]
          · rw [hi]
            exact ⟨(fun w hw => by cases hw), n1, fun y hy => f1 y (hw' y hy).1⟩
      | _ =>
          rw [denote'_ite_of_nonval hr (fun w hw => by cases hw)]
          exact ⟨(fun w hw => by cases hw), n1, fun y hy => f1 y (hw' y hy).1⟩
  | .mk (.forFold i lo hi b) _, h, fuel, env, henv => by
      obtain ⟨⟨hlo, hhi⟩, hb⟩ : (cfFree lo = true ∧ cfFree hi = true) ∧ cfFree b = true := by
        simpa [cfFree] using h
      simp only [TExpr.erase]
      have hw' : ∀ y, (writes (.mk (.forFold i lo hi b) ‹_›)).contains y = false →
          y ≠ i ∧ (writes lo).contains y = false ∧ (writes hi).contains y = false ∧
            (writes b).contains y = false := by
        intro y hy
        obtain ⟨hyi, hy⟩ := contains_cons_false (by simpa only [writes] using hy)
        obtain ⟨h1, h2⟩ := contains_append_false hy
        exact ⟨hyi, h1, contains_append_false h2⟩
      obtain ⟨g1, n1, f1⟩ := cfFree_run hbi lo hlo fuel env henv
      rcases hr : denote' bi fuel lo.erase env with ⟨r1, env1⟩
      rw [hr] at g1 n1 f1
      dsimp only at g1 n1 f1
      cases r1 with
      | val w =>
          obtain ⟨g2, n2, f2⟩ := cfFree_run hbi hi hhi fuel env1 n1
          rcases hr2 : denote' bi fuel hi.erase env1 with ⟨r2, env2⟩
          rw [hr2] at g2 n2 f2
          dsimp only at g2 n2 f2
          rcases denote'_forFold_of_hi (x := i) (body := b.erase) hr (g1 w rfl) hr2 with
            ⟨l, u, hl⟩ | ⟨s, hs⟩ | hs
          · rw [hl]
            obtain ⟨g3, n3, f3⟩ := denoteForLoop'_good_frame (x := i) (body := b.erase)
              (fun fuel' env' h' => cfFree_run hbi b hb fuel' env' h') fuel l u env2 n2
            refine ⟨g3, n3, fun y hy => ?_⟩
            obtain ⟨hyi, h1, h2, h3⟩ := hw' y hy
            rw [f3 y h3 hyi, f2 y h2, f1 y h1]
          · rw [hs]
            refine ⟨(fun w hw => by cases hw), n2, fun y hy => ?_⟩
            obtain ⟨-, h1, h2, -⟩ := hw' y hy
            dsimp only; rw [f2 y h2, f1 y h1]
          · rw [hs]
            refine ⟨g2, n2, fun y hy => ?_⟩
            obtain ⟨-, h1, h2, -⟩ := hw' y hy
            dsimp only; rw [f2 y h2, f1 y h1]
      | _ =>
          rw [denote'_forFold_of_lo hr (fun w hw => by cases hw)]
          exact ⟨(fun w hw => by cases hw), n1, fun y hy => f1 y (hw' y hy).2.1⟩
  | .mk (.ann e) _, h, fuel, env, henv => by
      have he : cfFree e = true := by simpa [cfFree] using h
      simp only [TExpr.erase]
      obtain ⟨g1, n1, f1⟩ := cfFree_run hbi e he fuel env henv
      exact ⟨g1, n1, fun y hy => f1 y (by simpa only [writes] using hy)⟩
  | .mk (.lam _ _) _, h, _, _, _ | .mk (.proj _ _) _, h, _, _, _
  | .mk (.match_ _ _) _, h, _, _, _ | .mk (.borrow _) _, h, _, _, _
  | .mk (.deref _) _, h, _, _, _ | .mk (.assign _ _) _, h, _, _, _
  | .mk (.forLoop _ _ _ _) _, h, _, _, _ | .mk (.forLoopRev _ _ _ _) _, h, _, _, _
  | .mk (.whileLoop _ _) _, h, _, _, _ | .mk (.break_ _) _, h, _, _, _
  | .mk .continue_ _, h, _, _, _ | .mk (.earlyReturn _) _, h, _, _, _
  | .mk (.questionMark _) _, h, _, _, _ | .mk (.forFoldRev _ _ _ _) _, h, _, _, _
  | .mk (.whileFold _ _) _, h, _, _, _ | .mk (.forFoldReturn _ _ _ _) _, h, _, _, _
  | .mk (.forFoldRevReturn _ _ _ _) _, h, _, _, _ | .mk (.whileFoldReturn _ _) _, h, _, _, _
  | .mk (.cfBreak _) _, h, _, _, _ | .mk (.cfContinue _) _, h, _, _, _
  | .mk (.cfBreakContinue _) _, h, _, _, _ => by simp [cfFree] at h

/-- `cfFree_run` along an argument list. -/
theorem cfFreeList_run {bi : Builtins} (hbi : SiteTable bi) :
    ∀ (es : List TExpr), cfFreeList es = true → ∀ (fuel : Nat) (env : Env), NoCFEnv env →
      NoCFEnv (denoteArgs' bi fuel (es.map TExpr.erase) env).2 ∧
        ∀ y, (writesList es).contains y = false →
          (denoteArgs' bi fuel (es.map TExpr.erase) env).2 y = env y
  | [], _, fuel, env, henv => by
      rw [List.map_nil, _root_.Hax.Total.denoteArgs'_nil_run]
      exact ⟨henv, fun _ _ => rfl⟩
  | e :: es, h, fuel, env, henv => by
      obtain ⟨he, hes⟩ : cfFree e = true ∧ cfFreeList es = true := by simpa [cfFreeList] using h
      obtain ⟨g1, n1, f1⟩ := cfFree_run hbi e he fuel env henv
      rw [List.map_cons]
      rcases hr : denote' bi fuel e.erase env with ⟨r1, env1⟩
      rw [hr] at g1 n1 f1
      dsimp only at g1 n1 f1
      cases r1 with
      | val w =>
          rw [denoteArgs'_cons_of_val' hr (g1 w rfl)]
          obtain ⟨n2, f2⟩ := cfFreeList_run hbi es hes fuel env1 n1
          refine ⟨n2, fun y hy => ?_⟩
          obtain ⟨h1, h2⟩ := contains_append_false (by simpa only [writesList] using hy)
          rw [f2 y h2, f1 y h1]
      | _ =>
          rw [denoteArgs'_cons_of_nonval hr (fun w hw => by cases hw)]
          exact ⟨n1, fun y hy =>
            f1 y (contains_append_false (by simpa only [writesList] using hy)).1⟩

end

/-! ## Accesses out of range -/

theorem and3 {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem not_true_eq {b : Bool} (h : (!b) = true) : b = false := by
  simpa using h

theorem denote'_var_of {bi : Builtins} {fuel : Nat} {env : Env} {x : String} {u : Value}
    (h : env x = some u) : denote' bi fuel (.var x) env = (.val u, env) := by
  rw [_root_.Hax.denote'_var_run, h]

theorem varNodeName?_erase {a : TExpr} {x : String} (h : varNodeName? a = some x) :
    a.erase = .var x := by
  obtain ⟨k, t⟩ := a
  cases k <;> simp only [varNodeName?, reduceCtorEq, Option.some.injEq] at h
  subst h
  rfl

theorem denoteArgs'_cons_inv {bi : Builtins} {fuel : Nat} {e : ImpExpr} {es : List ImpExpr}
    {env : Env} {vals : List Value} (h : (denoteArgs' bi fuel (e :: es) env).1 = some vals) :
    ∃ w ws, vals = w :: ws ∧ (denote' bi fuel e env).1 = .val w ∧
      (denoteArgs' bi fuel es (denote' bi fuel e env).2).1 = some ws := by
  rw [denoteArgs'_cons_unfold] at h
  rcases hr : denote' bi fuel e env with ⟨r, env1⟩
  rw [hr] at h
  cases r with
  | val w =>
      cases w with
      | controlFlow => cases h
      | _ =>
          obtain ⟨ws, h1, h2⟩ := Option.map_eq_some_iff.mp h
          exact ⟨_, ws, h2.symm, rfl, h1⟩
  | _ => cases h

theorem denoteArgs'_nil_inv {bi : Builtins} {fuel : Nat} {env : Env} {vals : List Value}
    (h : (denoteArgs' bi fuel [] env).1 = some vals) : vals = [] := by
  rw [_root_.Hax.Total.denoteArgs'_nil_run] at h
  exact (Option.some.inj h).symm

theorem app_val_inv {bi : Builtins} {fuel : Nat} {f : String} {args : List ImpExpr}
    {env : Env} {w : Value} (h : (denote' bi fuel (.app f args) env).1 = .val w) :
    ∃ vals, (denoteArgs' bi fuel args env).1 = some vals ∧ bi f vals = some w := by
  rw [denote'_app_unfold] at h
  revert h
  rcases ho : (denoteArgs' bi fuel args env).1 with _ | vals
  · intro h; cases h
  · rcases hb : bi f vals with _ | v
    · simp only [hb]; intro h; cases h
    · simp only [hb]; intro h; cases h; exact ⟨vals, rfl, hb⟩

/-- The value of an index at offset `c` from the counter `i` is the counter plus `c`. -/
theorem ctrOff_val {bi : Builtins} (hbi : SiteTable bi) {i : String} {ix : TExpr} {c : Nat}
    (h : ctrOff? i ix = some c) {env : Env} {k : Int} (hi : env i = some (.int k))
    {fuel : Nat} {w : Value} (hw : (denote' bi fuel ix.erase env).1 = .val w) :
    w = .int (k + c) := by
  unfold ctrOff? at h
  split at h
  · split at h
    · rename_i hx
      cases h
      have hx' := beq_iff_eq.mp hx
      subst hx'
      simp only [TExpr.erase, denote'_var_of hi] at hw
      cases hw
      simp
    · cases h
  · split at h
    · rename_i hc
      cases h
      obtain ⟨hx, hf, hc0⟩ := and3 hc
      have hx' := beq_iff_eq.mp hx
      subst hx'
      have hc0' := of_decide_eq_true hc0
      simp only [TExpr.erase, TExpr.eraseList_eq, List.map_cons, List.map_nil] at hw
      obtain ⟨vals, hv, hb⟩ := app_val_inv hw
      obtain ⟨w1, ws, rfl, h1, h2⟩ := denoteArgs'_cons_inv hv
      rw [denote'_var_of hi] at h1 h2
      cases h1
      obtain ⟨w2, ws', rfl, h3, h4⟩ := denoteArgs'_cons_inv h2
      rw [_root_.Hax.denote'_lit_run] at h3 h4
      cases h3
      cases denoteArgs'_nil_inv h4
      rw [hbi.add _ _ _ w hf hb]
      simp only [Value.int.injEq]
      omega
    · cases h
  · cases h

/-- **An access out of range returns no value**: an access of an array variable holding
    `vs` at an index operand whose value, if any, is an integer at or beyond the length of
    `vs`. -/
theorem access_fail {bi : Builtins} (hbi : SiteTable bi) {e a ix : TExpr} {x : String}
    {env : Env} {vs : List Value} {fuel : Nat}
    (he : access? e = some (a, ix)) (ha : varNodeName? a = some x) (hx : env x = some (.array vs))
    (hix : ∀ w, (denote' bi fuel ix.erase env).1 = .val w →
      ∃ k : Int, w = .int k ∧ (vs.length : Int) ≤ k) :
    ∀ w, (denote' bi fuel e.erase env).1 ≠ .val w := by
  intro w hw
  have hae := varNodeName?_erase ha
  unfold access? at he
  split at he
  · cases he
    simp only [TExpr.erase, TExpr.eraseList_eq, List.map_cons, List.map_nil, hae] at hw
    obtain ⟨vals, hv, hb⟩ := app_val_inv hw
    obtain ⟨w1, ws, rfl, h1, h2⟩ := denoteArgs'_cons_inv hv
    rw [denote'_var_of hx] at h1 h2
    cases h1
    obtain ⟨w2, ws', rfl, h3, h4⟩ := denoteArgs'_cons_inv h2
    cases denoteArgs'_nil_inv h4
    obtain ⟨k, rfl, hk⟩ := hix w2 h3
    rw [hbi.index_oob vs k hk] at hb
    cases hb
  · cases he
    simp only [TExpr.erase, TExpr.eraseList_eq, List.map_cons, List.map_nil, hae] at hw
    obtain ⟨vals, hv, hb⟩ := app_val_inv hw
    obtain ⟨w1, ws, rfl, h1, h2⟩ := denoteArgs'_cons_inv hv
    rw [denote'_var_of hx] at h1 h2
    cases h1
    obtain ⟨w2, ws', rfl, h3, h4⟩ := denoteArgs'_cons_inv h2
    obtain ⟨w3, ws'', rfl, -, h5⟩ := denoteArgs'_cons_inv h4
    cases denoteArgs'_nil_inv h5
    obtain ⟨k, rfl, hk⟩ := hix w2 h3
    rw [hbi.update_oob vs k w3 hk] at hb
    cases hb
  · cases he

/-- **An access at a cap of the counter fails**: where the counter `i` holds `k` at least
    the cap of the access, the access returns no value. -/
theorem site_fail {bi : Builtins} (hbi : SiteTable bi) {K : List (String × Nat)} {i : String}
    {e : TExpr} {c : Nat} (h : siteCap? K i e = some c) {env : Env} (hK : LensIn K env)
    {k : Int} (hi : env i = some (.int k)) (hck : (c : Int) ≤ k) (fuel : Nat) :
    ∀ w, (denote' bi fuel e.erase env).1 ≠ .val w := by
  unfold siteCap? at h
  rcases hacc : access? e with _ | ⟨a, ix⟩
  · rw [hacc] at h; cases h
  rw [hacc] at h
  rcases hx : varNodeName? a with _ | x
  · simp [hx] at h
  rcases hL : List.lookup x K with _ | L
  · simp [hx, hL] at h
  rcases hoff : ctrOff? i ix with _ | off
  · simp [hx, hoff] at h
  simp only [hx, hL, hoff, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨vs, hvs, hlen⟩ := hK x L hL
  refine access_fail hbi hacc hx hvs (fun w hw => ⟨k + off, ctrOff_val hbi hoff hi hw, ?_⟩)
  omega

mutual

/-- **A trip at a counter at or beyond a cap of its body returns no value**: where the
    counter `i` holds `k`, the lengths `K` hold and no name holds a control-flow value, a node
    with a cap at most `k` (`strictCaps`) returns no value. -/
theorem strictCaps_fail {bi : Builtins} (hbi : SiteTable bi) {i : String} {k : Int} :
    ∀ (e : TExpr) (K : List (String × Nat)) (fuel : Nat) (env : Env), LensIn K env →
      NoCFEnv env → env i = some (.int k) → ∀ c ∈ strictCaps K i e, (c : Int) ≤ k →
        ∀ w, (denote' bi fuel e.erase env).1 ≠ .val w
  | .mk (.app f args) t, K, fuel, env, hK, henv, hi, c, hc, hck => by
      simp only [strictCaps, List.mem_append, Option.mem_toList] at hc
      rcases hc with hc | hc
      · exact site_fail hbi hc hK hi hck fuel
      · have h1 := strictCapsList_fail hbi args K fuel env hK henv hi c hc hck
        intro w hw
        simp only [TExpr.erase, TExpr.eraseList_eq, denote'_app_unfold, h1] at hw
        cases hw
  | .mk (.tuple es) t, K, fuel, env, hK, henv, hi, c, hc, hck => by
      simp only [strictCaps] at hc
      have h1 := strictCapsList_fail hbi es K fuel env hK henv hi c hc hck
      intro w hw
      simp only [TExpr.erase, TExpr.eraseList_eq, denote'_tuple_run, h1] at hw
      cases hw
  | .mk (.letBind x v c') t, K, fuel, env, hK, henv, hi, c, hc, hck => by
      simp only [strictCaps, List.mem_append] at hc
      simp only [TExpr.erase]
      rcases hc with hc | hc
      · have h1 := strictCaps_fail hbi v K fuel env hK henv hi c hc hck
        rcases hr : denote' bi fuel v.erase env with ⟨r1, env1⟩
        rw [hr] at h1
        rw [denote'_letBind_of_nonval hr (fun w hw => absurd hw (h1 w))]
        exact h1
      · split at hc
        · rename_i hcond
          obtain ⟨hv, hxi, hwi⟩ := and3 hcond
          have hxi' : x ≠ i := by simpa using hxi
          have hwi' := not_true_eq hwi
          obtain ⟨g1, n1, f1⟩ := cfFree_run hbi v hv fuel env henv
          rcases hr : denote' bi fuel v.erase env with ⟨r1, env1⟩
          rw [hr] at g1 n1 f1
          dsimp only at g1 n1 f1
          cases r1 with
          | val w1 =>
              rw [_root_.Hax.Total.denote'_letBind_of_val hr (g1 w1 rfl)]
              refine strictCaps_fail hbi c' _ fuel _ (hK.dropW fun y hy => ?_)
                (n1.extend x (g1 w1 rfl)) ?_ c hc hck
              · obtain ⟨hyx, hy⟩ := contains_cons_false hy
                rw [extend_apply_of_ne hyx, f1 y hy]
              · rw [extend_apply_of_ne (Ne.symm hxi'), f1 i hwi', hi]
          | _ =>
              rw [denote'_letBind_of_nonval hr (fun w hw => by cases hw)]
              intro w hw
              cases hw
        · simp at hc
  | .mk (.seq a b) t, K, fuel, env, hK, henv, hi, c, hc, hck => by
      simp only [strictCaps, List.mem_append] at hc
      simp only [TExpr.erase]
      rcases hc with hc | hc
      · have h1 := strictCaps_fail hbi a K fuel env hK henv hi c hc hck
        rcases hr : denote' bi fuel a.erase env with ⟨r1, env1⟩
        rw [hr] at h1
        rw [denote'_seq_of_nonval hr (fun w hw => absurd hw (h1 w))]
        exact h1
      · split at hc
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨ha, hwi⟩ := hcond
          have hwi' := not_true_eq hwi
          obtain ⟨g1, n1, f1⟩ := cfFree_run hbi a ha fuel env henv
          rcases hr : denote' bi fuel a.erase env with ⟨r1, env1⟩
          rw [hr] at g1 n1 f1
          dsimp only at g1 n1 f1
          cases r1 with
          | val w1 =>
              rw [_root_.Hax.Total.denote'_seq_of_val hr (g1 w1 rfl)]
              refine strictCaps_fail hbi b _ fuel _ (hK.dropW fun y hy => f1 y hy) n1 ?_ c hc hck
              rw [f1 i hwi', hi]
          | _ =>
              rw [denote'_seq_of_nonval hr (fun w hw => by cases hw)]
              intro w hw
              cases hw
        · simp at hc
  | .mk (.ifThenElse c' _ _) t, K, fuel, env, hK, henv, hi, c, hc, hck => by
      simp only [strictCaps] at hc
      simp only [TExpr.erase]
      have h1 := strictCaps_fail hbi c' K fuel env hK henv hi c hc hck
      rcases hr : denote' bi fuel c'.erase env with ⟨r1, env1⟩
      rw [hr] at h1
      rw [denote'_ite_of_nonval hr (fun w hw => absurd hw (h1 w))]
      exact h1
  | .mk (.ann e) t, K, fuel, env, hK, henv, hi, c, hc, hck => by
      simp only [strictCaps] at hc
      simp only [TExpr.erase]
      exact strictCaps_fail hbi e K fuel env hK henv hi c hc hck
  | .mk (.lit _) _, _, _, _, _, _, _, c, hc, _ | .mk (.var _) _, _, _, _, _, _, _, c, hc, _
  | .mk .unitVal _, _, _, _, _, _, _, c, hc, _ | .mk (.lam _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.proj _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.match_ _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.borrow _) _, _, _, _, _, _, _, c, hc, _ | .mk (.deref _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.assign _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.forLoop _ _ _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.forLoopRev _ _ _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.whileLoop _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.break_ _) _, _, _, _, _, _, _, c, hc, _ | .mk .continue_ _, _, _, _, _, _, _, c, hc, _
  | .mk (.earlyReturn _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.questionMark _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.forFold _ _ _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.forFoldRev _ _ _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.whileFold _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.forFoldReturn _ _ _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.forFoldRevReturn _ _ _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.whileFoldReturn _ _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.cfBreak _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.cfContinue _) _, _, _, _, _, _, _, c, hc, _
  | .mk (.cfBreakContinue _) _, _, _, _, _, _, _, c, hc, _ => by simp [strictCaps] at hc

/-- `strictCaps_fail` along an argument list: the list returns no values. -/
theorem strictCapsList_fail {bi : Builtins} (hbi : SiteTable bi) {i : String} {k : Int} :
    ∀ (es : List TExpr) (K : List (String × Nat)) (fuel : Nat) (env : Env), LensIn K env →
      NoCFEnv env → env i = some (.int k) → ∀ c ∈ strictCapsList K i es, (c : Int) ≤ k →
        (denoteArgs' bi fuel (es.map TExpr.erase) env).1 = none
  | [], _, _, _, _, _, _, c, hc, _ => by simp [strictCapsList] at hc
  | e :: es, K, fuel, env, hK, henv, hi, c, hc, hck => by
      simp only [strictCapsList, List.mem_append] at hc
      rw [List.map_cons]
      rcases hc with hc | hc
      · have h1 := strictCaps_fail hbi e K fuel env hK henv hi c hc hck
        rcases hr : denote' bi fuel e.erase env with ⟨r1, env1⟩
        rw [hr] at h1
        rw [denoteArgs'_cons_of_nonval hr (fun w hw => absurd hw (h1 w))]
      · split at hc
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨he, hwi⟩ := hcond
          have hwi' := not_true_eq hwi
          obtain ⟨g1, n1, f1⟩ := cfFree_run hbi e he fuel env henv
          rcases hr : denote' bi fuel e.erase env with ⟨r1, env1⟩
          rw [hr] at g1 n1 f1
          dsimp only at g1 n1 f1
          cases r1 with
          | val w1 =>
              rw [denoteArgs'_cons_of_val' hr (g1 w1 rfl)]
              have h2 := strictCapsList_fail hbi es _ fuel env1 (hK.dropW fun y hy => f1 y hy) n1
                (by rw [f1 i hwi', hi]) c hc hck
              simp [h2]
          | _ => rw [denoteArgs'_cons_of_nonval hr (fun w hw => by cases hw)]
        · simp at hc

end

/-! ## Counted loops over a parameter -/

theorem LensIn.mono {K : List (String × Nat)} {env env' : Env} (h : LensIn K env)
    (hf : ∀ x L, List.lookup x K = some L → env' x = env x) : LensIn K env' := by
  intro x L hx
  rw [hf x L hx]
  exact h x L hx

/-- **A loop that runs to a trip at or beyond a cap of its body returns no value**: from the
    trip `j` the trip `kk = j + t` below the upper bound `h` is reached, at which the body,
    whose counter holds `kk` at least its cap, returns no value. -/
theorem loop_fail {bi : Builtins} (hbi : SiteTable bi) {K : List (String × Nat)} {i : String}
    {b : TExpr} (hb : cfFree b = true) {cap : Nat}
    (hcap : cap ∈ strictCaps (dropW K (i :: writes b)) i b) {kk h : Int}
    (hk : (cap : Int) ≤ kk) (hkh : kk < h) :
    ∀ (t : Nat) (j : Int) (fuel : Nat) (env : Env), j + t = kk →
      LensIn (dropW K (i :: writes b)) env → NoCFEnv env →
        ∀ w, (denoteForLoop' bi fuel i j h b.erase env).1 ≠ .val w := by
  have hext : ∀ (env : Env) (j : Int), LensIn (dropW K (i :: writes b)) env →
      LensIn (dropW K (i :: writes b)) (Env.extend env i (.int j)) := by
    intro env j hK
    refine hK.mono fun y L hy => ?_
    obtain ⟨-, hc⟩ := lookup_dropW hy
    exact extend_apply_of_ne (contains_cons_false hc).1
  intro t
  induction t with
  | zero =>
      intro j fuel env hj hK henv w hw
      cases fuel with
      | zero =>
          rw [denoteForLoop'_zero _ _ _ _ (by omega)] at hw
          cases hw
      | succ m =>
          have h1 := strictCaps_fail hbi b _ (m + 1) _ (hext env j hK) (henv.extend i rfl)
            extend_apply_self cap hcap (by omega)
          rcases hr : denote' bi (m + 1) b.erase (Env.extend env i (.int j)) with ⟨r, env2⟩
          rw [hr] at h1
          rw [denoteForLoop'_of_nonval (by omega) (by omega) hr h1] at hw
          exact h1 w hw
  | succ t ih =>
      intro j fuel env hj hK henv w hw
      cases fuel with
      | zero =>
          rw [denoteForLoop'_zero _ _ _ _ (by omega)] at hw
          cases hw
      | succ m =>
          obtain ⟨g1, n1, f1⟩ := cfFree_run hbi b hb (m + 1) _ (henv.extend i (w := .int j) rfl)
          rcases hr : denote' bi (m + 1) b.erase (Env.extend env i (.int j)) with ⟨r, env2⟩
          rw [hr] at g1 n1 f1
          dsimp only at g1 n1 f1
          cases r with
          | val w1 =>
              rw [denoteForLoop'_of_val (by omega) (by omega) hr (g1 w1 rfl),
                Nat.add_sub_cancel] at hw
              refine ih (j + 1) m env2 (by omega) (hK.mono fun y L hy => ?_) n1 w hw
              obtain ⟨-, hc⟩ := lookup_dropW hy
              obtain ⟨hyi, hyw⟩ := contains_cons_false hc
              rw [f1 y hyw, extend_apply_of_ne hyi]
          | _ =>
              rw [denoteForLoop'_of_nonval (by omega) (by omega) hr (fun w h => by cases h)] at hw
              cases hw

/-- **A loop over the parameter `p` past a cap of its body returns no value.** -/
theorem loopHead_fail {bi : Builtins} (hbi : SiteTable bi) {K : List (String × Nat)}
    {p : String} {n : Int} {i q : String} {lo : Int} {t1 t2 t : ImpType} {b : TExpr}
    (hq : (q == p) = true) (hlo : decide (0 ≤ lo) = true) (hb : cfFree b = true) {cap : Nat}
    (hcap : cap ∈ strictCaps (dropW K (i :: writes b)) i b) {fuel : Nat} {env : Env}
    (hK : LensIn K env) (henv : NoCFEnv env) (hp : env p = some (.int n))
    (hcn : ((max lo.toNat cap : Nat) : Int) < n) :
    ∀ w, (denote' bi fuel
      (TExpr.mk (.forFold i (.mk (.lit (.int lo)) t1) (.mk (.var q) t2) b) t).erase env).1 ≠
        .val w := by
  have hq' := beq_iff_eq.mp hq
  subst hq'
  have hlo' := of_decide_eq_true hlo
  simp only [TExpr.erase]
  rw [_root_.Hax.Total.denote'_forFold_of_bounds (_root_.Hax.denote'_lit_run _ _ _ _) rfl
    (denote'_var_of hp) rfl]
  have hmax : ((max lo.toNat cap : Nat) : Int) = max lo (cap : Int) := by omega
  rw [hmax] at hcn
  exact loop_fail hbi hb hcap (le_max_right _ _) hcn (max lo (cap : Int) - lo).toNat lo fuel env
    (by omega) (hK.dropW fun _ _ => rfl) henv

/-! ## The heads of the spine -/

theorem access?_erase {e a ix : TExpr} (h : access? e = some (a, ix)) :
    ∃ f args, e.erase = .app f args := by
  unfold access? at h
  split at h
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · cases h

/-- A head with a cap is a counted loop or a call. -/
theorem headCaps_shape {K : List (String × Nat)} {p : String} {e : TExpr} {c : Nat}
    (hc : c ∈ headCaps K p e) :
    (∃ i lo hi b, e.erase = .forFold i lo hi b) ∨ ∃ f args, e.erase = .app f args := by
  unfold headCaps at hc
  split at hc
  · exact .inl ⟨_, _, _, _, rfl⟩
  · split at hc
    · rename_i hacc
      exact .inr (access?_erase hacc)
    · simp at hc

theorem headCaps_not_lam {K : List (String × Nat)} {p : String} {e : TExpr} {c : Nat}
    (hc : c ∈ headCaps K p e) : ∀ ps b, e.erase ≠ .lam ps b := by
  intro ps b he
  rcases headCaps_shape hc with ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] at he <;> cases he

/-- **A head of the spine past a cap of `p` returns no value.** -/
theorem headCaps_fail {bi : Builtins} (hbi : SiteTable bi) {K : List (String × Nat)}
    {p : String} {n : Int} {e : TExpr} {fuel : Nat} {env : Env} (hK : LensIn K env)
    (henv : NoCFEnv env) (hp : env p = some (.int n)) {c : Nat} (hc : c ∈ headCaps K p e)
    (hcn : (c : Int) < n) : ∀ w, (denote' bi fuel e.erase env).1 ≠ .val w := by
  unfold headCaps at hc
  split at hc
  · split at hc
    · rename_i hcond
      obtain ⟨hq, hlo, hb⟩ := and3 hcond
      obtain ⟨cap, hcap, rfl⟩ := List.mem_map.mp hc
      exact loopHead_fail hbi hq hlo hb hcap hK henv hp hcn
    · simp at hc
  · split at hc
    · next a q tq hacc =>
      split at hc
      · rename_i hq
        have hq' := beq_iff_eq.mp hq
        subst hq'
        rcases hx : varNodeName? a with _ | x
        · simp [hx] at hc
        rcases hL : List.lookup x K with _ | L
        · simp [hx, hL] at hc
        simp only [hx, hL, Option.bind_some, Option.map_some, Option.toList_some,
          List.mem_singleton] at hc
        subst hc
        obtain ⟨vs, hvs, hlen⟩ := hK x L hL
        refine access_fail hbi hacc hx hvs (fun w hw => ⟨n, ?_, ?_⟩)
        · simp only [TExpr.erase, denote'_var_of hp] at hw
          cases hw
          rfl
        · omega
      · simp at hc
    · simp at hc

/-! ## The spine -/

theorem cfFree_not_lam : ∀ (v : TExpr), cfFree v = true → ∀ ps b, v.erase ≠ .lam ps b
  | .mk k t, h => by
      cases k
      case ann e =>
        simp only [cfFree] at h
        simp only [TExpr.erase]
        exact cfFree_not_lam e h
      case lam => simp [cfFree] at h
      all_goals
        intro ps b he
        first
          | simp [TExpr.erase] at he
          | (rename_i o; cases o <;> simp [TExpr.erase] at he)

theorem selfBind_erase {x : String} {v : TExpr} (h : selfBind x v = true) : v.erase = .var x := by
  obtain ⟨k, t⟩ := v
  cases k <;> simp only [selfBind, Bool.false_eq_true] at h
  rw [beq_iff_eq] at h
  subst h
  rfl

theorem var_run_inv {bi : Builtins} {fuel : Nat} {x : String} {env env1 : Env} {w : Value}
    (h : denote' bi fuel (.var x) env = (.val w, env1)) : env x = some w ∧ env1 = env := by
  rw [_root_.Hax.denote'_var_run] at h
  rcases hx : env x with _ | u <;> rw [hx] at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

theorem denoteSpine_letBind_eq {bi : Builtins} {fuel : Nat} {x : String} {v c : ImpExpr}
    (hnl : ∀ ps b, v ≠ .lam ps b) (env : Env) :
    _root_.Hax.InlineLocalClosures.denoteSpine bi fuel (.letBind x v c) env =
      match denote' bi fuel v env with
      | (.val (.controlFlow ib w), env') => (.val (.controlFlow ib w), env')
      | (.val w, env') =>
          _root_.Hax.InlineLocalClosures.denoteSpine bi fuel c (Env.extend env' x w)
      | (other, env') => (other, env') := by
  cases v
  case lam ps b => exact absurd rfl (hnl ps b)
  all_goals
    simp only [_root_.Hax.InlineLocalClosures.denoteSpine]
    dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
    generalize denote' bi fuel _ env = q
    obtain ⟨r, env'⟩ := q
    cases r <;> try rfl
    rename_i w; cases w <;> rfl

theorem denoteSpine_seq_eq {bi : Builtins} {fuel : Nat} {a b : ImpExpr} (env : Env) :
    _root_.Hax.InlineLocalClosures.denoteSpine bi fuel (.seq a b) env =
      match denote' bi fuel a env with
      | (.val (.controlFlow ib w), env') => (.val (.controlFlow ib w), env')
      | (.val _, env') => _root_.Hax.InlineLocalClosures.denoteSpine bi fuel b env'
      | (other, env') => (other, env') := by
  simp only [_root_.Hax.InlineLocalClosures.denoteSpine]
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel a env = q
  obtain ⟨r, env'⟩ := q
  cases r <;> try rfl
  rename_i w; cases w <;> rfl

theorem denoteSpine_of_head {bi : Builtins} {fuel : Nat} {K : List (String × Nat)} {p : String}
    {e : TExpr} {c : Nat} (hc : c ∈ headCaps K p e) (env : Env) :
    _root_.Hax.InlineLocalClosures.denoteSpine bi fuel e.erase env =
      denote' bi fuel e.erase env := by
  rcases headCaps_shape hc with ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;>
    simp only [_root_.Hax.InlineLocalClosures.denoteSpine]

/-- **A run past a cap of `p` along the spine returns no value that is not a control-flow
    value.** -/
theorem capsOf_fail {bi : Builtins} (hbi : SiteTable bi) {p : String} {n : Int} :
    ∀ (s : Nat) (te : TExpr), sizeOf te ≤ s → ∀ (K : List (String × Nat)) (fuel : Nat)
      (env : Env), LensIn K env → NoCFEnv env → env p = some (.int n) →
        ∀ c ∈ capsOf K p te, (c : Int) < n → ∀ w,
          (_root_.Hax.InlineLocalClosures.denoteSpine bi fuel te.erase env).1 = .val w →
            w.isControlFlow = true := by
  intro s
  induction s with
  | zero =>
      intro te hs
      obtain ⟨k, t⟩ := te
      simp at hs
  | succ s ih =>
      intro te hs K fuel env hK henv hp c hc hcn w hw
      unfold capsOf at hc
      split at hc
      · next x v c' t =>
        have hs' : sizeOf c' ≤ s := by simp at hs; omega
        simp only [List.mem_append] at hc
        simp only [TExpr.erase] at hw
        rcases hc with hc | hc
        · have hnl := headCaps_not_lam hc
          have h1 := headCaps_fail hbi hK henv hp hc hcn (fuel := fuel)
          rw [denoteSpine_letBind_eq hnl] at hw
          rcases hr : denote' bi fuel v.erase env with ⟨r1, env1⟩
          rw [hr] at h1 hw
          cases r1 with
          | val w1 => exact absurd rfl (h1 w1)
          | _ => cases hw
        · split at hc
          · rename_i hcond
            obtain ⟨hv, hxp, hwp⟩ := and3 hcond
            have hwp' := not_true_eq hwp
            have hnl := cfFree_not_lam v hv
            obtain ⟨g1, n1, f1⟩ := cfFree_run hbi v hv fuel env henv
            rw [denoteSpine_letBind_eq hnl] at hw
            rcases hr : denote' bi fuel v.erase env with ⟨r1, env1⟩
            rw [hr] at g1 n1 f1 hw
            dsimp only at g1 n1 f1
            cases r1 with
            | val w1 =>
                have hw1 := g1 w1 rfl
                have hw' : (_root_.Hax.InlineLocalClosures.denoteSpine bi fuel c'.erase
                    (Env.extend env1 x w1)).1 = .val w := by
                  revert hw
                  cases w1 <;> first | exact id | simp [Value.isControlFlow] at hw1
                have key : LensIn (bindK K x v) (Env.extend env1 x w1) ∧
                    Env.extend env1 x w1 p = some (.int n) := by
                  unfold bindK
                  split
                  · rename_i hsb
                    rw [selfBind_erase hsb] at hr
                    obtain ⟨hxw, he1⟩ := var_run_inv hr
                    rw [he1]
                    have hsame : ∀ y, Env.extend env x w1 y = env y := by
                      intro y
                      by_cases hyx : y = x
                      · subst hyx
                        rw [extend_apply_self, hxw]
                      · exact extend_apply_of_ne hyx
                    exact ⟨hK.mono fun y _ _ => hsame y, by rw [hsame, hp]⟩
                  · rename_i hsb
                    have hxp' : x ≠ p := by
                      simp only [Bool.or_eq_true] at hxp
                      rcases hxp with h | h
                      · simpa using h
                      · exact absurd h hsb
                    refine ⟨hK.dropW fun y hy => ?_, ?_⟩
                    · obtain ⟨hyx, hy⟩ := contains_cons_false hy
                      rw [extend_apply_of_ne hyx, f1 y hy]
                    · rw [extend_apply_of_ne (Ne.symm hxp'), f1 p hwp', hp]
                exact ih c' hs' _ fuel _ key.1 (n1.extend x hw1) key.2 c hc hcn w hw'
            | _ => cases hw
          · simp at hc
      · next a b t =>
        have hs' : sizeOf b ≤ s := by simp at hs; omega
        simp only [List.mem_append] at hc
        simp only [TExpr.erase] at hw
        rw [denoteSpine_seq_eq] at hw
        rcases hc with hc | hc
        · have h1 := headCaps_fail hbi hK henv hp hc hcn (fuel := fuel)
          rcases hr : denote' bi fuel a.erase env with ⟨r1, env1⟩
          rw [hr] at h1 hw
          cases r1 with
          | val w1 => exact absurd rfl (h1 w1)
          | _ => cases hw
        · split at hc
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            obtain ⟨ha, hwp⟩ := hcond
            have hwp' := not_true_eq hwp
            obtain ⟨g1, n1, f1⟩ := cfFree_run hbi a ha fuel env henv
            rcases hr : denote' bi fuel a.erase env with ⟨r1, env1⟩
            rw [hr] at g1 n1 f1 hw
            dsimp only at g1 n1 f1
            cases r1 with
            | val w1 =>
                have hw1 := g1 w1 rfl
                have hw' : (_root_.Hax.InlineLocalClosures.denoteSpine bi fuel b.erase
                    env1).1 = .val w := by
                  revert hw
                  cases w1 <;> first | exact id | simp [Value.isControlFlow] at hw1
                exact ih b hs' _ fuel env1 (hK.dropW fun y hy => f1 y hy) n1
                  (by rw [f1 p hwp', hp]) c hc hcn w hw'
            | _ => cases hw
          · simp at hc
      · rw [denoteSpine_of_head hc] at hw
        exact absurd hw (headCaps_fail hbi hK henv hp hc hcn w)

/-- **A cap of `p` along the spine holds at every run to a value**: where the lengths `K` hold,
    no name holds a control-flow value and `p` holds the integer `n`, a run of the spine
    reading of the body to a value that is not a control-flow value has `n` at most every cap
    of `p` (`capsOf`). -/
theorem le_of_mem_capsOf {bi : Builtins} (hbi : SiteTable bi) {K : List (String × Nat)}
    {p : String} {te : TExpr} {fuel : Nat} {env env' : Env} {v : Value} {n : Int}
    (hK : LensIn K env) (henv : NoCFEnv env) (hp : env p = some (.int n))
    (hrun : (_root_.Hax.InlineLocalClosures.denoteSpine bi fuel te.erase).run env =
      (.val v, env'))
    (hv : v.isControlFlow = false) : ∀ c ∈ capsOf K p te, n ≤ c := by
  intro c hc
  by_contra hlt
  have h1 : (_root_.Hax.InlineLocalClosures.denoteSpine bi fuel te.erase env).1 = .val v :=
    congrArg Prod.fst hrun
  have := capsOf_fail hbi (sizeOf te) te le_rfl K fuel env hK henv hp c hc (by omega) v h1
  rw [hv] at this
  cases this

/-! ## The derived bounds of a layout -/

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

theorem lookup_arrLens {args : List AbiArg} {x : String} {L : Nat}
    (h : List.lookup x (arrLens args) = some L) : ∃ a ∈ args, a.name = x ∧ a.kind = .words L := by
  induction args with
  | nil => simp [arrLens] at h
  | cons a args ih =>
      cases hk : a.kind with
      | scalar =>
          have h' : List.lookup x (arrLens args) = some L := by simpa [arrLens, hk] using h
          obtain ⟨b, hb, h1, h2⟩ := ih h'
          exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩
      | words m =>
          have h' : List.lookup x ((a.name, m) :: arrLens args) = some L := by
            simpa [arrLens, hk] using h
          by_cases hx : x = a.name
          · subst hx
            simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h'
            subst h'
            exact ⟨a, List.mem_cons_self, rfl, hk⟩
          · have hb : (x == a.name) = false := by simpa using hx
            simp only [List.lookup, hb] at h'
            obtain ⟨b, hb, h1, h2⟩ := ih h'
            exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩

/-- **The derived bounds lose no source run**: where `σ` reads the environment `env` off the
    entry state `sa` (`AbiLayout.EnvOf`) and no constant of `σ` is a control-flow value, a run
    of the spine reading of the body `te` from `env` to a value that is not a control-flow
    value, at a table with `SiteTable`, has each register a derived bound of `te` names at most
    its bound. -/
theorem deriveBounds_hold {bi : Builtins} (hbi : SiteTable bi) {σ : AbiLayout} {sa : AState}
    {env : Env} (hσ : σ.EnvOf sa env) (hcs : ∀ c ∈ σ.consts, c.2.isControlFlow = false)
    {te : TExpr} {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (_root_.Hax.InlineLocalClosures.denoteSpine bi fuel te.erase).run env =
      (.val v, env'))
    (hv : v.isControlFlow = false) :
    ∀ b ∈ deriveBounds σ.args te, (sa.regs b.1).toNat ≤ b.2 := by
  obtain ⟨hargs, hconsts, hnames⟩ := hσ
  have hK : LensIn (arrLens σ.args) env := by
    intro x L hx
    obtain ⟨a, ha, rfl, hk⟩ := lookup_arrLens hx
    refine ⟨wordsAt sa.mem (sa.regs a.reg) L, ?_, by simp [wordsAt]⟩
    rw [hargs a ha]
    simp [AbiArg.read, hk]
  have henv : NoCFEnv env := by
    intro y w hy
    have hm := hnames y (by rw [hy]; rfl)
    simp only [AbiLayout.envNames, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
    · rw [hargs a ha] at hy
      cases hy
      unfold AbiArg.read
      cases a.kind <;> rfl
    · rw [hconsts c hc] at hy
      cases hy
      exact hcs c hc
  intro b hb
  obtain ⟨a, ha, hk, hr, hm⟩ := mem_deriveBounds hb
  have hp : env a.name = some (.int ((sa.regs a.reg).toNat : Int)) := by
    rw [hargs a ha]
    simp [AbiArg.read, hk]
  have := le_of_mem_capsOf hbi hK henv hp hrun hv b.2 (minCap_mem hm)
  rw [← hr]
  omega

/-! ## The table `hax64WExit` -/

open CatCrypt.Crypto.Hax (hax64WExit hax64Exit hax64WideHead)

theorem widthArrayOps_repeat_noCF {vals : List Value} {r : Value}
    (h : _root_.Hax.widthArrayOps "repeat" vals = some r) : r.isControlFlow = false := by
  rcases vals with _ | ⟨v, _ | ⟨n, _ | ⟨_, _⟩⟩⟩
  all_goals try (simp [_root_.Hax.widthArrayOps] at h; done)
  cases n <;> simp [_root_.Hax.widthArrayOps] at h
  all_goals (obtain ⟨-, rfl⟩ := h; rfl)

theorem hax64WExit_noCF {f : String} {vals : List Value} {r : Value}
    (h : hax64WExit f vals = some r) : r.isControlFlow = false := by
  by_cases hs : f = "select"
  · subst hs
    obtain ⟨k, x, y, -, hx, hy, rfl⟩ := CatCrypt.Crypto.Hax.hax64WExit_select_some h
    cases k <;> simpa
  by_cases hw : hax64WideHead f
  · rw [CatCrypt.Crypto.Hax.hax64WExit_wide hw] at h
    obtain ⟨-, ys, rfl⟩ := CatCrypt.Crypto.Hax.hax64Builtins_wideHead hw h
    rfl
  by_cases hl : f = "array_lit"
  · subst hl
    unfold hax64WExit at h
    simp only [ite_true] at h
    split_ifs at h
    cases h
    rfl
  by_cases hp : f = "repeat"
  · subst hp
    unfold hax64WExit at h
    simp only [show ("repeat" : String) ≠ "array_lit" by decide, ite_false, ite_true] at h
    split_ifs at h
    rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_repeat _)] at h
    exact widthArrayOps_repeat_noCF h
  by_cases he : f = "eq#arr" ∨ f = "ne#arr"
  · unfold hax64WExit at h
    simp only [hl, hp, he, ↓reduceIte] at h
    split_ifs at h with ha
    unfold CatCrypt.Crypto.Hax.hax64EqArrAdmit at ha
    split at ha
    · simp only [Bool.and_eq_true] at ha
      rcases he with rfl | rfl
      · rw [_root_.Hax.hax64Builtins_eqArr_words ha.1 ha.2] at h
        cases h
        rfl
      · rw [_root_.Hax.hax64Builtins_neArr_words ha.1 ha.2] at h
        cases h
        rfl
    · cases ha
  · rw [not_or] at he
    rw [CatCrypt.Crypto.Hax.hax64WExit_of_ne hl hp he.1 he.2 hw hs] at h
    exact (CatCrypt.Crypto.Hax.hax64Exit_some h).2.1

theorem hax64WExit_index_oob (vs : List Value) (k : Int) (hk : (vs.length : Int) ≤ k) :
    hax64WExit "index" [.array vs, .int k] = none := by
  rw [CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
  unfold hax64Exit
  rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_index _ vs),
    _root_.Hax.widthArrayOps_index_int, ite_eq_left (by omega),
    List.getElem?_eq_none (by omega)]
  rfl

theorem hax64WExit_update_oob (vs : List Value) (k : Int) (w : Value)
    (hk : (vs.length : Int) ≤ k) : hax64WExit "array_update" [.array vs, .int k, w] = none := by
  rw [CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
  unfold hax64Exit
  rw [_root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_array_update _ vs w),
    _root_.Hax.widthArrayOps_array_update_int]
  have : (decide (0 ≤ k) && decide (k.toNat < vs.length)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
    right
    omega
  rw [this]
  rfl

theorem hax64WExit_add {f : String} {a c : Int} {r : Value} (hf : checkedAdd f = true)
    (h : hax64WExit f [.int a, .int c] = some r) : r = .int (a + c) := by
  simp only [checkedAdd, Bool.or_eq_true, beq_iff_eq] at hf
  have hb : _root_.Hax.hax64Builtins f [.int a, .int c] = some r := by
    rcases hf with (rfl | rfl) | rfl <;>
      exact CatCrypt.Crypto.Hax.hax64Exit_sub
        (by rwa [CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide)
          (by decide)] at h)
  have hw : _root_.Hax.hax64WordOps f [.int a, .int c] = _root_.Hax.uintAddOp 64 a c := by
    rcases hf with (rfl | rfl) | rfl
    · rw [← _root_.Hax.hax64WordOps_add64_eq_Add]
      rfl
    · rfl
    · rfl
  have hn : _root_.Hax.widthArrayOps f [.int a, .int c] = none := by
    rcases hf with (rfl | rfl) | rfl <;> rfl
  unfold _root_.Hax.hax64Builtins at hb
  rw [hw, hn] at hb
  unfold _root_.Hax.uintAddOp at hb
  split_ifs at hb
  · cases hb
    rfl
  · cases hb

/-- **`hax64WExit` has the properties the derivation uses.** -/
theorem siteTable_hax64WExit : SiteTable hax64WExit where
  noCF _ _ _ h := hax64WExit_noCF h
  index_oob := hax64WExit_index_oob
  update_oob := hax64WExit_update_oob
  add _ _ _ _ hf h := hax64WExit_add hf h

end CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds
