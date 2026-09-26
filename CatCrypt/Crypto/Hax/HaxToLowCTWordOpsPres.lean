/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTWordOpsLoop

/-!
# The multiply-high fusion and A-normalisation of `mpn_mul_1` in `denote'`

`mul1_hax_eq_compiled` (`HaxToLowCTWordOpsLoop`) identifies the value of the
fused, A-normalised `mpn_mul_1` program `mul1ProgHax` in `denote'` with the output
of the compiled loop. This module transfers that statement to the extracted
program `mul1ProgSrc`, in which the multiply-high idiom is the call chain
`mulHiChain` and the call arguments are nested calls.

The transfer is a backward simulation (`RunBack`): every run of the target to a
value is matched by a run of the source to the same value, in environments that
agree off the fresh names the A-normaliser mints (`EnvAgreeExcept`). A binding
whose right-hand side is flat in the target is matched with a binding whose
right-hand side is a call tree in the source when the two have the same call-tree
value (`treeVal`); a binding of a fresh name exists in the target alone. The
call-tree value of `mulHiChain a b` is that of `mulhi#64(a, b)` when `a` and `b`
hold words below `2^64` (`treeVal_mulHiChain`); on other operands the two differ,
so the fusion preserves `denote'` only under that range condition, which the trip
of `mpn_mul_1` discharges from `WordBuiltins.index` on the cells of `up` and from
the word `v`.

## Main definitions

* `treeVal`, `treeVals` — the value of a call tree over variables and literals.
* `isAtom`, `isFlatRhs` — atoms and flat right-hand sides.
* `EnvAgreeExcept F` — agreement of two environments off the names `F`.
* `RunBack` — backward simulation of a target run by a source run.
* `mul1BodySrc`, `mul1ProgSrc` — the extracted `mpn_mul_1` body and program.
* `mul1FreshNames`, `mul1Fresh` — the fresh names of `mul1BodyHax`.

## Main results

* `treeVal_run` — a call tree with a value runs in `denote'` to that value.
* `flat_inv`, `letBind_inv`, `seq_inv` — inversion of runs to values.
* `RunBack.letBind`, `RunBack.fresh`, `RunBack.seq`, `RunBack.var`,
  `RunBack.unitVal` — the simulation rules.
* `treeVal_mulHiChain`, `denote'_mulHiChain`, `denote'_letBind_fuseMulHiRhs` — the
  multiply-high idiom on two words and its fused form have the same value.
* `mul1_src_trip_back` — one trip of `mul1BodyHax` is simulated by one trip of
  `mul1BodySrc`.
* `mul1_src_loop` — the loop over `mul1BodySrc` ends in an environment that agrees
  with `mul1Trips` off the fresh names.
* `mul1_src_eq_compiled` — the statement of `mul1_hax_eq_compiled` for
  `mul1ProgSrc`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.WordOpsSim

open _root_.Hax (ImpExpr ImpLit Value Env Builtins Outcome denote' denoteArgs')
open CatCrypt.Crypto.Jasmin.LowCT (sexprMulHiU)

/-! ### Call trees -/

mutual

/-- The value of a call tree (a variable, a literal, or a call of call trees) in
    `env`, when every node evaluates to a value that is no control-flow value;
    `none` on every other expression. -/
def treeVal (bi : Builtins) (env : Env) : ImpExpr → Option Value
  | .var x => (env x).filter (fun v => !v.isControlFlow)
  | .lit l => some (Value.ofLit l)
  | .app f args => ((treeVals bi env args).bind (bi f)).filter (fun v => !v.isControlFlow)
  | _ => none

/-- The values of a list of call trees. -/
def treeVals (bi : Builtins) (env : Env) : List ImpExpr → Option (List Value)
  | [] => some []
  | a :: as => (treeVal bi env a).bind fun v => (treeVals bi env as).map (v :: ·)

end

/-- A variable or a literal. -/
def isAtom : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | _ => false

/-- A variable, a literal, or a call whose arguments are variables and literals. -/
def isFlatRhs : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | .app _ args => args.all isAtom
  | _ => false

theorem ofLit_isControlFlow (l : ImpLit) : (Value.ofLit l).isControlFlow = false := by
  cases l <;> rfl

theorem treeVal_eq_some {bi : Builtins} {env : Env} {e : ImpExpr} {v : Value}
    (h : treeVal bi env e = some v) :
    v.isControlFlow = false ∧
      ((∃ x, e = .var x ∧ env x = some v) ∨ (∃ l, e = .lit l ∧ v = Value.ofLit l) ∨
        (∃ f args vs, e = .app f args ∧ treeVals bi env args = some vs ∧ bi f vs = some v)) := by
  cases e with
  | var x =>
    simp only [treeVal, Option.filter_eq_some_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact ⟨h.2, Or.inl ⟨x, rfl, h.1⟩⟩
  | lit l =>
    simp only [treeVal, Option.some.injEq] at h
    subst h
    exact ⟨ofLit_isControlFlow l, Or.inr (Or.inl ⟨l, rfl, rfl⟩)⟩
  | app f args =>
    simp only [treeVal, Option.filter_eq_some_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
      Option.bind_eq_some_iff] at h
    obtain ⟨⟨vs, hvs, hb⟩, hc⟩ := h
    exact ⟨hc, Or.inr (Or.inr ⟨f, args, vs, rfl, hvs, hb⟩)⟩
  | _ => simp [treeVal] at h

theorem treeVal_isControlFlow {bi : Builtins} {env : Env} {e : ImpExpr} {v : Value}
    (h : treeVal bi env e = some v) : v.isControlFlow = false :=
  (treeVal_eq_some h).1

/-- A call tree with a value runs in `denote'` to that value and leaves the
    environment unchanged. -/
theorem treeVal_run_aux (bi : Builtins) (fuel : Nat) :
    ∀ (n : Nat) (e : ImpExpr) (env : Env) (v : Value), sizeOf e < n →
      treeVal bi env e = some v → denote' bi fuel e env = (.val v, env)
  | 0, _, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, e, env, v, hs, h => by
    obtain ⟨-, ⟨x, rfl, hx⟩ | ⟨l, rfl, rfl⟩ | ⟨f, args, vs, rfl, hargs, hb⟩⟩ := treeVal_eq_some h
    · exact _root_.Hax.Ascent.denote'_var bi fuel hx
    · exact _root_.Hax.Ascent.denote'_lit bi fuel l env
    · refine _root_.Hax.Ascent.denote'_app bi fuel ?_ hb
      have key : ∀ (as : List ImpExpr) (ws : List Value), (∀ a ∈ as, sizeOf a < n) →
          treeVals bi env as = some ws → denoteArgs' bi fuel as env = (some ws, env) := by
        intro as
        induction as with
        | nil =>
          intro ws _ hw
          simp only [treeVals, Option.some.injEq] at hw
          subst hw
          exact _root_.Hax.Ascent.denoteArgs'_nil bi fuel env
        | cons a as ih =>
          intro ws hsz hw
          simp only [treeVals, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hw
          obtain ⟨w, hw₁, ws', hws', rfl⟩ := hw
          exact _root_.Hax.Ascent.denoteArgs'_cons bi fuel
            (treeVal_run_aux bi fuel n a env w (hsz a (by simp)) hw₁) (treeVal_isControlFlow hw₁)
            (ih ws' (fun b hb => hsz b (by simp [hb])) hws')
      refine key args vs (fun a ha => ?_) hargs
      have := List.sizeOf_lt_of_mem ha
      simp only [ImpExpr.app.sizeOf_spec] at hs
      omega

theorem treeVal_run {bi : Builtins} (fuel : Nat) {e : ImpExpr} {env : Env} {v : Value}
    (h : treeVal bi env e = some v) : denote' bi fuel e env = (.val v, env) :=
  treeVal_run_aux bi fuel _ e env v (Nat.lt_succ_self _) h

/-! ### Inverting runs -/

section Inversion

variable {bi : Builtins} {fuel : Nat}

theorem denote'_letBind_eq (x : String) (r k : ImpExpr) (env : Env) :
    denote' bi fuel (.letBind x r k) env =
      match denote' bi fuel r env with
      | (.val (.controlFlow b v), e1) => (.val (.controlFlow b v), e1)
      | (.val v, e1) => denote' bi fuel k (e1.extend x v)
      | (o, e1) => (o, e1) := by
  simp only [denote', bind, StateT.bind, pure, modify, modifyGet, MonadStateOf.modifyGet]
  rcases (denote' bi fuel r) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem denote'_seq_eq (a b : ImpExpr) (env : Env) :
    denote' bi fuel (.seq a b) env =
      match denote' bi fuel a env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val _, e1) => denote' bi fuel b e1
      | (o, e1) => (o, e1) := by
  simp only [denote', bind, StateT.bind, pure]
  rcases (denote' bi fuel a) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem denote'_app_eq (f : String) (args : List ImpExpr) (env : Env) :
    denote' bi fuel (.app f args) env =
      match denoteArgs' bi fuel args env with
      | (some vals, e1) =>
          match bi f vals with
          | some v => (.val v, e1)
          | none => (.err s!"unknown function or bad args: {f}", e1)
      | (none, e1) => (.err "non-value in function arguments", e1) := by
  simp only [denote', _root_.Hax.denoteApp', bind, StateT.bind, pure]
  rcases (denoteArgs' bi fuel args) env with ⟨o, e1⟩
  rcases o with _ | vals
  · rfl
  · cases h : bi f vals <;> simp only [h] <;> rfl

theorem denoteArgs'_cons_eq (e : ImpExpr) (es : List ImpExpr) (env : Env) :
    denoteArgs' bi fuel (e :: es) env =
      match denote' bi fuel e env with
      | (.val (.controlFlow _ _), e1) => (none, e1)
      | (.val v, e1) =>
          ((denoteArgs' bi fuel es e1).1.map (v :: ·), (denoteArgs' bi fuel es e1).2)
      | (_, e1) => (none, e1) := by
  simp only [denoteArgs', bind, StateT.bind, pure]
  rcases (denote' bi fuel e) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem denote'_var_eq (x : String) (env : Env) :
    denote' bi fuel (.var x) env =
      match env x with
      | some v => (.val v, env)
      | none => (.err s!"undefined variable: {x}", env) := by
  simp only [denote']
  cases h : env x <;>
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, h]

/-- A run of an atom to a value that is no control-flow value leaves the
    environment unchanged and is the atom's call-tree value. -/
theorem atom_inv {a : ImpExpr} (ha : isAtom a = true) {env s : Env} {w : Value}
    (h : denote' bi fuel a env = (.val w, s)) (hw : w.isControlFlow = false) :
    s = env ∧ treeVal bi env a = some w := by
  cases a with
  | var x =>
    rw [denote'_var_eq] at h
    cases hx : env x with
    | none => rw [hx] at h; cases h
    | some v =>
      rw [hx] at h
      cases h
      exact ⟨rfl, by simp [treeVal, hx, hw]⟩
  | lit l =>
    rw [_root_.Hax.Ascent.denote'_lit] at h
    cases h
    exact ⟨rfl, rfl⟩
  | _ => simp [isAtom] at ha

theorem atoms_inv : ∀ (as : List ImpExpr), as.all isAtom = true → ∀ {env s : Env}
    {vs : List Value}, denoteArgs' bi fuel as env = (some vs, s) →
      s = env ∧ treeVals bi env as = some vs
  | [], _, env, s, vs, h => by
    rw [_root_.Hax.Ascent.denoteArgs'_nil] at h
    cases h
    exact ⟨rfl, rfl⟩
  | a :: as, hall, env, s, vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [denoteArgs'_cons_eq] at h
    rcases ha : denote' bi fuel a env with ⟨o, s₁⟩
    rw [ha] at h
    rcases o with w | _ | _ | _ | _
    · cases hw : w.isControlFlow
      · have h' : ((denoteArgs' bi fuel as s₁).1.map (w :: ·), (denoteArgs' bi fuel as s₁).2) =
            (some vs, s) := by
          cases w <;> first | exact h | simp at hw
        obtain ⟨hs₁, ht⟩ := atom_inv hall.1 ha hw
        rw [hs₁] at h'
        rcases hr : denoteArgs' bi fuel as env with ⟨r, s'⟩
        rw [hr] at h'
        rcases r with _ | ws
        · cases h'
        · simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          obtain ⟨rfl, hts⟩ := atoms_inv as hall.2 hr
          exact ⟨rfl, by simp [treeVals, ht, hts]⟩
      · cases w <;> simp at hw
        cases h
    all_goals cases h

/-- A run of a flat right-hand side to a value that is no control-flow value
    leaves the environment unchanged and is its call-tree value. -/
theorem flat_inv {r : ImpExpr} (hr : isFlatRhs r = true) {env s : Env} {w : Value}
    (h : denote' bi fuel r env = (.val w, s)) (hw : w.isControlFlow = false) :
    s = env ∧ treeVal bi env r = some w := by
  cases r with
  | var x => exact atom_inv rfl h hw
  | lit l => exact atom_inv rfl h hw
  | app f args =>
    rw [denote'_app_eq] at h
    rcases hA : denoteArgs' bi fuel args env with ⟨o, s₁⟩
    rw [hA] at h
    rcases o with _ | vals
    · cases h
    · dsimp only at h
      cases hb : bi f vals with
      | none => rw [hb] at h; cases h
      | some v =>
        rw [hb] at h
        cases h
        obtain ⟨rfl, hts⟩ := atoms_inv args hr hA
        exact ⟨rfl, by simp [treeVal, hts, hb, hw]⟩
  | _ => simp [isFlatRhs] at hr

theorem letBind_inv {x : String} {r k : ImpExpr} {env env' : Env} {o : Value}
    (h : denote' bi fuel (.letBind x r k) env = (.val o, env')) (ho : o.isControlFlow = false) :
    ∃ w s, denote' bi fuel r env = (.val w, s) ∧ w.isControlFlow = false ∧
      denote' bi fuel k (s.extend x w) = (.val o, env') := by
  rw [denote'_letBind_eq] at h
  rcases hr : denote' bi fuel r env with ⟨o₁, s⟩
  rw [hr] at h
  rcases o₁ with w | _ | _ | _ | _
  · cases w with
    | controlFlow b p => cases h; simp at ho
    | _ => exact ⟨_, s, rfl, rfl, h⟩
  all_goals cases h

theorem seq_inv {a b : ImpExpr} {env env' : Env} {o : Value}
    (h : denote' bi fuel (.seq a b) env = (.val o, env')) (ho : o.isControlFlow = false) :
    ∃ w s, denote' bi fuel a env = (.val w, s) ∧ w.isControlFlow = false ∧
      denote' bi fuel b s = (.val o, env') := by
  rw [denote'_seq_eq] at h
  rcases hr : denote' bi fuel a env with ⟨o₁, s⟩
  rw [hr] at h
  rcases o₁ with w | _ | _ | _ | _
  · cases w with
    | controlFlow k p => cases h; simp at ho
    | _ => exact ⟨_, s, rfl, rfl, h⟩
  all_goals cases h

end Inversion

/-! ### Backward simulation up to fresh names -/

/-- Two environments agree on every name outside `F`. -/
def EnvAgreeExcept (F : String → Prop) (env₁ env₂ : Env) : Prop :=
  ∀ y, ¬ F y → env₁ y = env₂ y

theorem EnvAgreeExcept.extend {F : String → Prop} {env₁ env₂ : Env}
    (h : EnvAgreeExcept F env₁ env₂) (x : String) (v : Value) :
    EnvAgreeExcept F (env₁.extend x v) (env₂.extend x v) := by
  intro y hy
  simp only [Env.extend]
  split
  · rfl
  · exact h y hy

theorem EnvAgreeExcept.extend_right {F : String → Prop} {env₁ env₂ : Env}
    (h : EnvAgreeExcept F env₁ env₂) {z : String} (hz : F z) (v : Value) :
    EnvAgreeExcept F env₁ (env₂.extend z v) := by
  intro y hy
  have hyz : y ≠ z := fun e => hy (e ▸ hz)
  rw [extend_ne _ hyz]
  exact h y hy

/-- **Backward simulation.** Every run of `e₂` from `env₂` to a value that is no
    control-flow value is matched by a run of `e₁` from `env₁` to the same value,
    with `Q` holding of the two final environments. -/
def RunBack (bi : Builtins) (fuel : Nat) (e₁ : ImpExpr) (env₁ : Env) (e₂ : ImpExpr) (env₂ : Env)
    (Q : Env → Env → Prop) : Prop :=
  ∀ v env₂', denote' bi fuel e₂ env₂ = (.val v, env₂') → v.isControlFlow = false →
    ∃ env₁', denote' bi fuel e₁ env₁ = (.val v, env₁') ∧ Q env₁' env₂'

section RunBack

variable {bi : Builtins} {fuel : Nat}

/-- A binding of the same name on both sides, the source right-hand side a call
    tree with the value of the target's flat right-hand side. -/
theorem RunBack.letBind {x : String} {r₁ r₂ k₁ k₂ : ImpExpr} {env₁ env₂ : Env}
    {Q : Env → Env → Prop} (hr₂ : isFlatRhs r₂ = true)
    (hT : treeVal bi env₁ r₁ = treeVal bi env₂ r₂)
    (hk : ∀ w, treeVal bi env₂ r₂ = some w →
      RunBack bi fuel k₁ (env₁.extend x w) k₂ (env₂.extend x w) Q) :
    RunBack bi fuel (.letBind x r₁ k₁) env₁ (.letBind x r₂ k₂) env₂ Q := by
  intro v env₂' h hv
  obtain ⟨w, s, hr, hw, hk₂⟩ := letBind_inv h hv
  obtain ⟨rfl, ht⟩ := flat_inv hr₂ hr hw
  obtain ⟨env₁', h₁, hQ⟩ := hk w ht v env₂' hk₂ hv
  refine ⟨env₁', ?_, hQ⟩
  rw [_root_.Hax.Ascent.denote'_letBind bi fuel (treeVal_run fuel (hT.trans ht)) hw]
  exact h₁

/-- A binding of the target alone. -/
theorem RunBack.fresh {z : String} {e₁ r₂ k₂ : ImpExpr} {env₁ env₂ : Env}
    {Q : Env → Env → Prop} (hr₂ : isFlatRhs r₂ = true)
    (hk : ∀ w, treeVal bi env₂ r₂ = some w → RunBack bi fuel e₁ env₁ k₂ (env₂.extend z w) Q) :
    RunBack bi fuel e₁ env₁ (.letBind z r₂ k₂) env₂ Q := by
  intro v env₂' h hv
  obtain ⟨w, s, hr, hw, hk₂⟩ := letBind_inv h hv
  obtain ⟨rfl, ht⟩ := flat_inv hr₂ hr hw
  exact hk w ht v env₂' hk₂ hv

theorem RunBack.seq {a₁ a₂ b₁ b₂ : ImpExpr} {env₁ env₂ : Env} {Q : Env → Env → Prop}
    (ha : RunBack bi fuel a₁ env₁ a₂ env₂ (fun s₁ s₂ => RunBack bi fuel b₁ s₁ b₂ s₂ Q)) :
    RunBack bi fuel (.seq a₁ b₁) env₁ (.seq a₂ b₂) env₂ Q := by
  intro v env₂' h hv
  obtain ⟨w, s, hs, hw, hb⟩ := seq_inv h hv
  obtain ⟨s₁, h₁, hB⟩ := ha w s hs hw
  obtain ⟨env₁', h₂, hQ⟩ := hB v env₂' hb hv
  exact ⟨env₁', by rw [_root_.Hax.Ascent.denote'_seq bi fuel h₁ hw]; exact h₂, hQ⟩

theorem RunBack.var {y : String} {env₁ env₂ : Env} {Q : Env → Env → Prop}
    (hy : env₁ y = env₂ y) (hQ : Q env₁ env₂) :
    RunBack bi fuel (.var y) env₁ (.var y) env₂ Q := by
  intro v env₂' h hv
  obtain ⟨rfl, ht⟩ := atom_inv rfl h hv
  obtain ⟨-, ⟨x, hx, hxv⟩ | ⟨l, hl, -⟩ | ⟨f, args, vs, he, -⟩⟩ := treeVal_eq_some ht
  · cases hx
    exact ⟨env₁, _root_.Hax.Ascent.denote'_var bi fuel (hy.trans hxv), hQ⟩
  · cases hl
  · cases he

theorem RunBack.unitVal {env₁ env₂ : Env} {Q : Env → Env → Prop} (hQ : Q env₁ env₂) :
    RunBack bi fuel .unitVal env₁ .unitVal env₂ Q := by
  intro v env₂' h _
  rw [_root_.Hax.Ascent.denote'_unitVal] at h
  cases h
  exact ⟨env₁, _root_.Hax.Ascent.denote'_unitVal bi fuel env₁, hQ⟩

end RunBack

/-! ### Values of call trees -/

section TreeValues

variable {bi : Builtins}

theorem treeVal_var_congr {env₁ env₂ : Env} {y : String} (h : env₁ y = env₂ y) :
    treeVal bi env₁ (.var y) = treeVal bi env₂ (.var y) := by
  simp only [treeVal, h]

theorem treeVal_lit_congr (env₁ env₂ : Env) (l : ImpLit) :
    treeVal bi env₁ (.lit l) = treeVal bi env₂ (.lit l) := rfl

theorem treeVal_var_of {env : Env} {y : String} {w : Value} (h : env y = some w)
    (hw : w.isControlFlow = false) : treeVal bi env (.var y) = some w := by
  simp [treeVal, h, hw]

theorem treeVal_app_congr {env₁ env₂ : Env} (f : String) {as bs : List ImpExpr}
    (h : treeVals bi env₁ as = treeVals bi env₂ bs) :
    treeVal bi env₁ (.app f as) = treeVal bi env₂ (.app f bs) := by
  simp only [treeVal, h]

theorem treeVals_nil_congr (env₁ env₂ : Env) : treeVals bi env₁ [] = treeVals bi env₂ [] := rfl

theorem treeVals_cons_congr {env₁ env₂ : Env} {a b : ImpExpr} {as bs : List ImpExpr}
    (h : treeVal bi env₁ a = treeVal bi env₂ b) (hs : treeVals bi env₁ as = treeVals bi env₂ bs) :
    treeVals bi env₁ (a :: as) = treeVals bi env₂ (b :: bs) := by
  simp only [treeVals, h, hs]

/-- Under `MulHiBuiltins`, the multiply-high idiom on two variables holding words
    below `2^64` has the call-tree value of `mulhi#64` on them. -/
theorem treeVal_mulHiChain (hbi : MulHiBuiltins bi) {env : Env} {a b : String} {n m : Nat}
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (ha : env a = some (.int n))
    (hb : env b = some (.int m)) :
    treeVal bi env (mulHiChain (.var a) (.var b)) =
      treeVal bi env (.app mulHiCallName [.var a, .var b]) := by
  have hnm : n * m < 2 ^ 128 := by
    have h := Nat.mul_lt_mul'' hn hm
    rwa [← Nat.pow_add] at h
  have hhi : (n * m) >>> 64 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hnm)
  have hI : ∀ z : Int, (some (Value.int z)).filter (fun v => !v.isControlFlow) =
      some (Value.int z) := fun _ => rfl
  simp only [mulHiChain, treeVal, treeVals, ha, hb, hI, Option.bind, Option.map_some,
    Value.ofLit, hbi.cast128 n hn, hbi.cast128 m hm, hbi.mul n m hn hm, hbi.shr128 _ hnm,
    hbi.cast64 _ hhi, hbi.mulhi n m hn hm, sexprMulHiU_of_lt hn hm]

/-- The variables among a list of expressions. -/
def atomVars : List ImpExpr → List String
  | [] => []
  | .var y :: as => y :: atomVars as
  | _ :: as => atomVars as

/-- The variables a flat right-hand side reads. -/
def flatVars : ImpExpr → List String
  | .var y => [y]
  | .app _ args => atomVars args
  | _ => []

theorem treeVals_atoms_congr {F : String → Prop} {env₁ env₂ : Env}
    (h : EnvAgreeExcept F env₁ env₂) :
    ∀ (as : List ImpExpr), as.all isAtom = true → (∀ y ∈ atomVars as, ¬ F y) →
      treeVals bi env₁ as = treeVals bi env₂ as
  | [], _, _ => rfl
  | a :: as, ha, hF => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    cases a with
    | var y =>
      simp only [atomVars, List.mem_cons, forall_eq_or_imp] at hF
      exact treeVals_cons_congr (treeVal_var_congr (h y hF.1))
        (treeVals_atoms_congr h as ha.2 hF.2)
    | lit l => exact treeVals_cons_congr rfl (treeVals_atoms_congr h as ha.2 hF)
    | _ => simp [isAtom] at ha

/-- A flat right-hand side reading no name of `F` has the same value in two
    environments that agree off `F`. -/
theorem treeVal_flat_congr {F : String → Prop} {env₁ env₂ : Env}
    (h : EnvAgreeExcept F env₁ env₂) (e : ImpExpr) (he : isFlatRhs e = true)
    (hF : ∀ y ∈ flatVars e, ¬ F y) : treeVal bi env₁ e = treeVal bi env₂ e := by
  cases e with
  | var y => exact treeVal_var_congr (h y (hF y (by simp [flatVars])))
  | lit l => rfl
  | app f args => exact treeVal_app_congr f (treeVals_atoms_congr h args he hF)
  | _ => simp [isFlatRhs] at he

theorem treeVal_app_vars2 {env : Env} {f a b : String} {va vb : Value}
    (ha : env a = some va) (hb : env b = some vb) (hva : va.isControlFlow = false)
    (hvb : vb.isControlFlow = false) :
    treeVal bi env (.app f [.var a, .var b]) = (bi f [va, vb]).filter (fun v => !v.isControlFlow) := by
  have hf : ∀ {w : Value}, w.isControlFlow = false →
      (some w).filter (fun v => !v.isControlFlow) = some w := fun hw => by
    simp [Option.filter, hw]
  simp only [treeVal, treeVals, ha, hb, hf hva, hf hvb, Option.bind, Option.map_some]

/-- Under `MulHiBuiltins`, the multiply-high idiom on two variables holding words
    below `2^64` runs in `denote'` as the call `mulhi#64` on them. -/
theorem denote'_mulHiChain (hbi : MulHiBuiltins bi) (fuel : Nat) {env : Env} {a b : String}
    {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (ha : env a = some (.int n))
    (hb : env b = some (.int m)) :
    denote' bi fuel (mulHiChain (.var a) (.var b)) env =
      denote' bi fuel (.app mulHiCallName [.var a, .var b]) env := by
  have h2 : treeVal bi env (.app mulHiCallName [.var a, .var b]) =
      some (.int (sexprMulHiU n m)) := by
    rw [treeVal_app_vars2 ha hb rfl rfl, hbi.mulhi n m hn hm]
    rfl
  rw [treeVal_run fuel h2, treeVal_run fuel ((treeVal_mulHiChain hbi hn hm ha hb).trans h2)]

/-- **`fuseMulHiIdiom` on a binding it rewrites.** Under `MulHiBuiltins`, the
    binding `let x = mulHiChain a b; k` of the multiply-high idiom on two variables
    holding words below `2^64` runs in `denote'` as its fused form
    `let x = fuseMulHiRhs (mulHiChain a b); k`. -/
theorem denote'_letBind_fuseMulHiRhs (hbi : MulHiBuiltins bi) (fuel : Nat) {env : Env}
    (x : String) (k : ImpExpr) {a b : String} {n m : Nat} (hn : n < 2 ^ 64)
    (hm : m < 2 ^ 64) (ha : env a = some (.int n)) (hb : env b = some (.int m)) :
    denote' bi fuel (.letBind x (fuseMulHiRhs (mulHiChain (.var a) (.var b))) k) env =
      denote' bi fuel (.letBind x (mulHiChain (.var a) (.var b)) k) env := by
  have h2 : treeVal bi env (.app mulHiCallName [.var a, .var b]) =
      some (.int (sexprMulHiU n m)) := by
    rw [treeVal_app_vars2 ha hb rfl rfl, hbi.mulhi n m hn hm]
    rfl
  show denote' bi fuel (.letBind x (.app mulHiCallName [.var a, .var b]) k) env = _
  rw [_root_.Hax.Ascent.denote'_letBind bi fuel (treeVal_run fuel h2) rfl,
    _root_.Hax.Ascent.denote'_letBind bi fuel
      (treeVal_run fuel ((treeVal_mulHiChain hbi hn hm ha hb).trans h2)) rfl]

end TreeValues

/-! ### The extracted `mpn_mul_1` -/

/-- The loop body of the extracted `mpn_mul_1`: the multiply-high idiom unfused
    and the call arguments not A-normalised. -/
def mul1BodySrc : ImpExpr :=
  .letBind "cy" (.app "index" [.var "rp", .var "i"])
  (.letBind "t" (.app "index" [.var "up", .var "i"])
  (.letBind "lo" (.app "wrapping_mul#64" [.var "t", .var "v"])
  (.letBind "hi" (mulHiChain (.var "t") (.var "v"))
  (.letBind "s" (.app "wrapping_add#64" [.var "lo", .var "cy"])
  (.letBind "cq" (.app "BitAnd#64" [.app "BitXor#64" [.var "s", .var "ONES"], .var "lo"])
  (.letBind "cr" (.app "BitAnd#64" [.app "BitXor#64" [.app "BitXor#64" [.var "s", .var "lo"],
      .var "ONES"], .app "wrapping_sub#64" [.var "s", .var "lo"]])
  (.letBind "c" (.app "Shr#64" [.app "BitXor#64" [.app "BitXor#64" [.var "cq", .var "cr"],
      .app "BitAnd#64" [.var "cq", .var "cr"]], .lit (.int 63)])
  (.letBind "cyo" (.app "wrapping_add#64" [.var "hi", .var "c"])
  (.seq (.seq (.letBind "rp" (.app "array_update" [.var "rp", .var "i", .var "s"]) (.var "rp"))
      .unitVal)
    (.seq (.seq (.letBind "rp" (.app "array_update" [.var "rp",
        .app "Add" [.var "i", .lit (.int 1)], .var "cyo"]) (.var "rp")) .unitVal) .unitVal))))))))))

/-- The extracted `mpn_mul_1`: the argument rebindings, the loop over
    `mul1BodySrc`, and the return of `rp` with the carry `rp[n]`. -/
def mul1ProgSrc : ImpExpr :=
  .letBind "rp" (.var "rp") (.letBind "up" (.var "up") (.letBind "n" (.var "n")
    (.letBind "v" (.var "v") (.letBind "rp" (.var "rp")
      (.seq (.forFold "i" (.lit (.int 0)) (.var "n") mul1BodySrc)
        (.letBind "carry" (.app "index" [.var "rp", .var "n"])
          (.tuple [.var "rp", .var "carry"])))))))

/-- The fresh names of `mul1BodyHax`. -/
def mul1FreshNames : List String :=
  ["__anorm_0", "__anorm_1", "__anorm_2", "__anorm_3", "__anorm_4", "__anorm_5", "__anorm_6",
   "__anorm_7", "__anorm_8", "__anorm_9"]

/-- A fresh name of `mul1BodyHax`. -/
abbrev mul1Fresh (y : String) : Prop := y ∈ mul1FreshNames

/-- **One trip, source against target.** From environments that agree off the
    fresh names, with the target holding at `up` a list whose cell `j` is the word
    `c`, at `i` the index `j`, and at `v` a word: every run of the target body
    `mul1BodyHax` to a value is matched by a run of the source body `mul1BodySrc` to
    the same value, in environments that agree off the fresh names. -/
theorem mul1_src_trip_back {bi : Builtins} (hbi : MulHiBuiltins bi) (fuel : Nat) {E₁ E₂ : Env}
    (hA : EnvAgreeExcept mul1Fresh E₁ E₂) {vs : List Value} {j c m : Nat}
    (hup : E₂ "up" = some (.array vs)) (hi : E₂ "i" = some (.int j))
    (hidx : bi "index" [.array vs, .int j] = some (.int c)) (hc : c < 2 ^ 64)
    (hv : E₂ "v" = some (.int m)) (hm : m < 2 ^ 64) :
    RunBack bi fuel mul1BodySrc E₁ mul1BodyHax E₂ (EnvAgreeExcept mul1Fresh) := by
  simp only [mul1BodySrc, mul1BodyHax, bindsHax, mul1Pre, mul1St1, mul1St2, WBind.hax]
  refine RunBack.letBind rfl (treeVal_flat_congr hA _ rfl (by decide)) fun wcy _ => ?_
  have hA1 := hA.extend "cy" wcy
  refine RunBack.letBind rfl (treeVal_flat_congr hA1 _ rfl (by decide)) fun wt hwt => ?_
  have hA2 := hA1.extend "t" wt
  have hwt' : wt = .int c := by
    rw [treeVal_app_vars2 (by rw [extend_ne _ (by decide), hup]) (by rw [extend_ne _ (by decide), hi])
      rfl rfl, hidx] at hwt
    exact (Option.some.inj hwt).symm
  subst hwt'
  refine RunBack.letBind rfl (treeVal_flat_congr hA2 _ rfl (by decide)) fun wlo _ => ?_
  have hA3 := hA2.extend "lo" wlo
  refine RunBack.letBind rfl ?_ fun whi _ => ?_
  · have ht : ((((E₁.extend "cy" wcy).extend "t" (.int c)).extend "lo" wlo) "t") =
        some (.int c) := by rw [extend_ne _ (by decide), extend_self]
    have hv' : ((((E₁.extend "cy" wcy).extend "t" (.int c)).extend "lo" wlo) "v") =
        some (.int m) := by
      rw [extend_ne _ (by decide), extend_ne _ (by decide), extend_ne _ (by decide),
        hA "v" (by decide), hv]
    rw [treeVal_mulHiChain hbi hc hm ht hv']
    exact treeVal_flat_congr hA3 _ rfl (by decide)
  have hA4 := hA3.extend "hi" whi
  refine RunBack.letBind rfl (treeVal_flat_congr hA4 _ rfl (by decide)) fun ws _ => ?_
  have hA5 := hA4.extend "s" ws
  -- `cq`
  refine RunBack.fresh rfl fun w0 hw0 => ?_
  have hA5' := hA5.extend_right (z := "__anorm_0") (by decide) w0
  refine RunBack.letBind rfl ?_ fun wcq _ => ?_
  · refine treeVal_app_congr _ (treeVals_cons_congr ?_ (treeVals_cons_congr
      (treeVal_var_congr (hA5' "lo" (by decide))) (treeVals_nil_congr _ _)))
    rw [treeVal_var_of (extend_self _) (treeVal_isControlFlow hw0), ← hw0]
    exact treeVal_flat_congr hA5 _ rfl (by decide)
  have hA6 := hA5'.extend "cq" wcq
  -- `cr`
  refine RunBack.fresh rfl fun w1 hw1 => ?_
  refine RunBack.fresh rfl fun w2 hw2 => ?_
  refine RunBack.fresh rfl fun w3 hw3 => ?_
  have hB1 := hA6.extend_right (z := "__anorm_1") (by decide) w1
  have hB2 := hB1.extend_right (z := "__anorm_2") (by decide) w2
  have hB3 := hB2.extend_right (z := "__anorm_3") (by decide) w3
  refine RunBack.letBind rfl ?_ fun wcr _ => ?_
  · refine treeVal_app_congr _ (treeVals_cons_congr ?_ (treeVals_cons_congr ?_
      (treeVals_nil_congr _ _)))
    · rw [treeVal_var_of (by rw [extend_ne _ (by decide), extend_self])
        (treeVal_isControlFlow hw2), ← hw2]
      refine treeVal_app_congr _ (treeVals_cons_congr ?_ (treeVals_cons_congr
        (treeVal_var_congr (hB1 "ONES" (by decide))) (treeVals_nil_congr _ _)))
      rw [treeVal_var_of (extend_self _) (treeVal_isControlFlow hw1), ← hw1]
      exact treeVal_flat_congr hA6 _ rfl (by decide)
    · rw [treeVal_var_of (extend_self _) (treeVal_isControlFlow hw3), ← hw3]
      exact treeVal_flat_congr hB2 _ rfl (by decide)
  have hA7 := hB3.extend "cr" wcr
  -- `c`
  refine RunBack.fresh rfl fun w4 hw4 => ?_
  refine RunBack.fresh rfl fun w5 hw5 => ?_
  refine RunBack.fresh rfl fun w6 hw6 => ?_
  refine RunBack.fresh rfl fun w7 hw7 => ?_
  have hC4 := hA7.extend_right (z := "__anorm_4") (by decide) w4
  have hC5 := hC4.extend_right (z := "__anorm_5") (by decide) w5
  have hC6 := hC5.extend_right (z := "__anorm_6") (by decide) w6
  have hC7 := hC6.extend_right (z := "__anorm_7") (by decide) w7
  refine RunBack.letBind rfl ?_ fun wc _ => ?_
  · refine treeVal_app_congr _ (treeVals_cons_congr ?_ (treeVals_cons_congr ?_
      (treeVals_nil_congr _ _)))
    · rw [treeVal_var_of (by rw [extend_ne _ (by decide), extend_self])
        (treeVal_isControlFlow hw6), ← hw6]
      refine treeVal_app_congr _ (treeVals_cons_congr ?_ (treeVals_cons_congr ?_
        (treeVals_nil_congr _ _)))
      · rw [treeVal_var_of (by rw [extend_ne _ (by decide), extend_self])
          (treeVal_isControlFlow hw4), ← hw4]
        exact treeVal_flat_congr hA7 _ rfl (by decide)
      · rw [treeVal_var_of (extend_self _) (treeVal_isControlFlow hw5), ← hw5]
        exact treeVal_flat_congr hC4 _ rfl (by decide)
    · rw [treeVal_var_of (extend_self _) (treeVal_isControlFlow hw7), ← hw7]
      rfl
  have hA8 := hC7.extend "c" wc
  refine RunBack.letBind rfl (treeVal_flat_congr hA8 _ rfl (by decide)) fun wcyo _ => ?_
  have hA9 := hA8.extend "cyo" wcyo
  -- the store of `s`
  refine RunBack.seq (RunBack.seq (RunBack.letBind rfl (treeVal_flat_congr hA9 _ rfl (by decide))
    fun wrp _ => RunBack.var ((hA9.extend "rp" wrp) "rp" (by decide)) (RunBack.unitVal ?_)))
  -- the store of `cyo`
  refine RunBack.seq (RunBack.seq (RunBack.fresh rfl fun w8 hw8 => RunBack.fresh rfl
    fun w9 hw9 => ?_))
  have hD8 := (hA9.extend "rp" wrp).extend_right (z := "__anorm_8") (by decide) w8
  have hD9 := hD8.extend_right (z := "__anorm_9") (by decide) w9
  refine RunBack.letBind rfl ?_ fun wrp2 _ => RunBack.var ((hD9.extend "rp" wrp2) "rp" (by decide))
    (RunBack.unitVal (RunBack.unitVal (hD9.extend "rp" wrp2)))
  refine treeVal_app_congr _ (treeVals_cons_congr (treeVal_var_congr (hD9 "rp" (by decide)))
    (treeVals_cons_congr ?_ (treeVals_cons_congr (treeVal_var_congr (hD9 "cyo" (by decide)))
      (treeVals_nil_congr _ _))))
  rw [treeVal_var_of (extend_self _) (treeVal_isControlFlow hw9), ← hw9]
  refine treeVal_app_congr _ (treeVals_cons_congr (treeVal_var_congr (hD8 "i" (by decide)))
    (treeVals_cons_congr ?_ (treeVals_nil_congr _ _)))
  rw [treeVal_var_of (extend_self _) (treeVal_isControlFlow hw8), ← hw8]
  rfl

/-- `n` trips leave `up`, `v`, `ONES` and `n` unchanged. -/
theorem mul1Trips_frame (R : Nat) (env : Env) {y : String}
    (hy : y = "up" ∨ y = "v" ∨ y = "ONES" ∨ y = "n") : ∀ n, mul1Trips R env n y = env y
  | 0 => rfl
  | n + 1 => by
    show mul1Next R ((mul1Trips R env n).extend "i" (.int n)) y = _
    rw [mul1Next_frame R _ hy, extend_ne _ (by rcases hy with rfl | rfl | rfl | rfl <;> decide),
      mul1Trips_frame R env hy n]

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (SEnvScalar)

/-- **The loop of the extracted `mpn_mul_1`.** Under the hypotheses of
    `mul1_loop_sim`, with `up` holding the first `U` cells of a memref, from a
    source environment that agrees with `env` off the fresh names: the loop
    `forFold i 0 n` over `mul1BodySrc` returns `()` at every fuel `≥ N`, in an
    environment that agrees with `mul1Trips R env N` off the fresh names. -/
theorem mul1_src_loop {bi : Builtins} (hbi : WordBuiltins bi) (hmh : MulHiBuiltins bi)
    {R U N L : Nat} (hR : N + 1 ≤ R) (hU : N ≤ U) (h64 : N + 1 < 2 ^ 64) {env : Env}
    {σ : SEnvScalar} (h : EnvRelW env σ ["v", "ONES", "n"] [("rp", R), ("up", U)])
    (hn : natOf env "n" = N) (up : Fin L → BitVec 64)
    (hup : env "up" = some (.array (intCells up U))) {env₁ : Env}
    (hA : EnvAgreeExcept mul1Fresh env₁ env) :
    ∃ E, (∀ fuel, N ≤ fuel →
        denote' bi fuel (.forFold "i" (.lit (.int 0)) (.var "n") mul1BodySrc) env₁ =
          (.val .unit, E)) ∧
      EnvAgreeExcept mul1Fresh E (mul1Trips R env N) := by
  have hnE : env "n" = some (.int N) := by
    rw [← hn]; exact ((h.word "n" (by simp)).natOf_eq).2.1
  obtain ⟨m, hm, hvE, -⟩ := h.word "v" (by simp)
  obtain ⟨E, σN, hL, -, hC⟩ := forFold_sim (bi := bi) mul1BodySrc (mul1BodyLow R) "i" "n" N
    (fun j e s => EnvAgreeExcept mul1Fresh e (mul1Trips R env j) ∧
      EnvRelW (mul1Trips R env j) s ["v", "ONES", "n"] [("rp", R), ("up", U)])
    (fun j hj e s ⟨he, hrel⟩ => by
      obtain ⟨σ', h1, h2, h3⟩ := mul1_trip hbi (j := j) (by omega) (by omega) (by omega) hrel
      have hback := mul1_src_trip_back hmh 0 (he.extend "i" (.int j)) (vs := intCells up U)
        (j := j) (c := (memGetDyn up j).toNat) (m := m)
        (by rw [extend_ne _ (by decide), mul1Trips_frame R env (by simp) j, hup]) (extend_self _)
        (hbi.index _ _ _ (intCells_getElem? up (by omega))) (BitVec.isLt _)
        (by rw [extend_ne _ (by decide), mul1Trips_frame R env (by simp) j, hvE]) hm
      obtain ⟨E', hE', hAg⟩ := hback _ _ (h1 0) rfl
      refine ⟨E', σ', fun fuel => ?_, h2, hAg, h3⟩
      rw [_root_.Hax.Ascent.denote'_fuel_mono_of_fuelFree bi (fuel := 0) rfl]
      exact hE') env₁ σ ⟨hA, h⟩ (by rw [hA "n" (by decide), hnE])
  exact ⟨E, hL, hC.1⟩

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (mul1RtProgOpt mul1Count mul1Init Gouter NR NU ones mul1Fold)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote (mul1RtProg_fold upVar vVar)
open CatCrypt.Crypto.SecureCompilation.VIR (Ctxt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (ComL)

/-- **The extracted `mpn_mul_1` and the compiled loop return the same words.** The
    statement of `mul1_hax_eq_compiled` for the source program `mul1ProgSrc`, under
    `WordBuiltins` and `MulHiBuiltins`. -/
theorem mul1_src_eq_compiled {bi : Builtins} (hbi : WordBuiltins bi) (hmh : MulHiBuiltins bi)
    (V : Ctxt.Valuation Gouter) {R U : Nat} (hR9 : R ≤ NR) (hU8 : U ≤ NU)
    (hNR : (mul1Count.lookup V).toNat + 1 ≤ R) (hNU : (mul1Count.lookup V).toNat ≤ U)
    {env : Env} (hup : env "up" = some (.array (intCells (upVar.lookup V) U)))
    (hrp : env "rp" = some (.array (intCells (mul1Init.lookup V) R)))
    (hv : env "v" = some (.int (vVar.lookup V).toNat)) (hO : env "ONES" = some (.int ones))
    (hn : env "n" = some (.int (mul1Count.lookup V).toNat)) :
    ∃ out, mul1RtProgOpt.map (fun c => ComL.denote c V) = some out ∧
      ∀ fuel, (mul1Count.lookup V).toNat ≤ fuel →
        (denote' bi fuel mul1ProgSrc env).1 =
          .val (.tuple [.array (intCells out R),
            .int (memGetDyn out (mul1Count.lookup V).toNat).toNat]) := by
  refine ⟨_, mul1RtProg_fold V, fun fuel hf => ?_⟩
  have hR64 : R < 2 ^ 64 := by
    have : NR = 9 := rfl
    omega
  obtain ⟨hvr, hvf⟩ := mul1Trips_val R U (upVar.lookup V) (vVar.lookup V) (mul1Init.lookup V)
    env hR9 hU8 hup hrp hv hO _ hNR hNU
  have hrel := mul1Sigma_rel R U (upVar.lookup V) (vVar.lookup V) (mul1Init.lookup V)
    (N := (mul1Count.lookup V).toNat) (by omega) hup hrp hv hO hn
  obtain ⟨E, hloop, hE⟩ := mul1_src_loop hbi hmh hNR hNU (by omega) hrel (by simp [natOf, hn])
    (upVar.lookup V) hup (fun _ _ => rfl)
  have hvrE := (hE "rp" (by decide)).trans hvr
  have hnN : E "n" = some (.int (mul1Count.lookup V).toNat) := by
    rw [hE "n" (by decide), hvf "n" (by simp), hn]
  have hcell := intCells_getElem? (mul1Fold (upVar.lookup V) (vVar.lookup V)
    (mul1Count.lookup V).toNat (mul1Init.lookup V)) (k := R) (j := (mul1Count.lookup V).toNat)
    (by omega)
  rw [mul1ProgSrc,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hrp) rfl,
    extend_of_eq hrp,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hup) rfl,
    extend_of_eq hup,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hn) rfl,
    extend_of_eq hn,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hv) rfl,
    extend_of_eq hv,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hrp) rfl,
    extend_of_eq hrp,
    _root_.Hax.Ascent.denote'_seq bi fuel (hloop fuel hf) rfl,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_app bi fuel
      (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hvrE) rfl
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hnN) rfl
          (_root_.Hax.Ascent.denoteArgs'_nil bi fuel _)))
      (hbi.index _ _ _ hcell)) rfl,
    _root_.Hax.Ascent.denote'_tuple bi fuel
      (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
        (_root_.Hax.Ascent.denote'_var bi fuel (by rw [extend_ne _ (by decide)]; exact hvrE)) rfl
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
          (_root_.Hax.Ascent.denote'_var bi fuel (extend_self _)) rfl
          (_root_.Hax.Ascent.denoteArgs'_nil bi fuel _)))]

end CatCrypt.Crypto.Hax.WordOpsSim
