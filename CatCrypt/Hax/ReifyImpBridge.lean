/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ReifyImp
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramFor
public import HaxLean.Phase.FunctionalizeLoopsCF

/-!
# The semantics bridge for `reifyImp%` literals

The ascent judgment `FnCorres` of `CatCrypt.Hax.ReifyImp` is stated over the
control-flow-aware semantics `denote'`; the read-back check `haxReadAgrees_sound` is
stated over `evalImp`, the value projection of the reference semantics `denote`, of the
program `forToLoop e`. On the fragment `reifyImp%` emits the two semantics coincide and
`forToLoop` is the identity, provided that the builtins and the environment carry no
control-flow value.

## Main definitions

* `ReifyFrag` — the fragment of `reifyImp%`: literals, variables, `let`, calls, tuples,
  projections and conditionals
* `Good` — a run whose exit environment and value carry no control-flow value

## Main results

* `forToLoop_eq_self` — `forToLoop e = e` on the fragment
* `denote'_eq_denote` — on the fragment, `denote'` and `denote` have the same run from a
  control-flow-free environment under control-flow-free builtins
* `fnCorres_evalImp` — a `FnCorres` statement of a fragment literal gives the `evalImp` run
  of `forToLoop e`
* `edwardsAdd_evalImp` — `evalImp` of `forToLoop edwardsAddImp` returns the encoding of
  `edwardsAddLean`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.ReifyImp

open _root_.Hax _root_.Hax.Ascent
open CatCrypt.Crypto.Hax (forToLoop forToLoopArgs evalImp)

/-! ## The fragment -/

/-- The fragment of `reifyImp%`: literals, variables, `let`, calls, tuples, projections and
    conditionals. -/
inductive ReifyFrag : ImpExpr → Prop where
  | lit {l} : ReifyFrag (.lit l)
  | var {n} : ReifyFrag (.var n)
  | letBind {n v b} : ReifyFrag v → ReifyFrag b → ReifyFrag (.letBind n v b)
  | app {f args} : (∀ a ∈ args, ReifyFrag a) → ReifyFrag (.app f args)
  | tuple {es} : (∀ a ∈ es, ReifyFrag a) → ReifyFrag (.tuple es)
  | proj {e i} : ReifyFrag e → ReifyFrag (.proj e i)
  | ifThenElse {c t e} : ReifyFrag c → ReifyFrag t → ReifyFrag e →
      ReifyFrag (.ifThenElse c t e)

/-! ## `forToLoop` is the identity on the fragment -/

/-- `forToLoopArgs` is the identity on a list on whose elements `forToLoop` is. -/
theorem forToLoopArgs_eq_self (args : List ImpExpr)
    (h : ∀ a ∈ args, forToLoop a = a) : forToLoopArgs args = args := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    simp only [forToLoopArgs, h a (.head _), ih fun b hb => h b (.tail _ hb)]

/-- `forToLoop` is the identity on the fragment. -/
theorem forToLoop_eq_self {e : ImpExpr} (h : ReifyFrag e) : forToLoop e = e := by
  induction h with
  | lit => rfl
  | var => rfl
  | letBind _ _ ihv ihb => simp only [forToLoop, ihv, ihb]
  | app _ ih => simp only [forToLoop, forToLoopArgs_eq_self _ ih]
  | tuple _ ih => simp only [forToLoop, forToLoopArgs_eq_self _ ih]
  | proj _ ih => simp only [forToLoop, ih]
  | ifThenElse _ _ _ ihc iht ihe => simp only [forToLoop, ihc, iht, ihe]

/-! ## `denote'` and `denote` coincide on the fragment -/

/-- A run whose exit environment carries no control-flow value and whose value, when it
    returns one, carries none. -/
def Good (r : Outcome × Env) : Prop :=
  r.2.NoControlFlow ∧ ∀ v, r.1 = .val v → v.deepNoControlFlow = true

/-- A run of an argument list whose exit environment carries no control-flow value and
    whose values, when it returns them, carry none. -/
def GoodArgs (r : Option (List Value) × Env) : Prop :=
  r.2.NoControlFlow ∧ ∀ vs, r.1 = some vs → ∀ v ∈ vs, v.deepNoControlFlow = true

variable {bi : Builtins} {fuel : Nat}

/-- The two semantics coincide on an argument list whose elements they coincide on. -/
theorem denoteArgs'_eq_denoteArgs (args : List ImpExpr)
    (ih : ∀ a ∈ args, ∀ env : Env, env.NoControlFlow →
      denote' bi fuel a env = denote bi fuel a env ∧ Good (denote bi fuel a env))
    (env : Env) (henv : env.NoControlFlow) :
    denoteArgs' bi fuel args env = denoteArgs bi fuel args env ∧
      GoodArgs (denoteArgs bi fuel args env) := by
  induction args generalizing env with
  | nil =>
    refine ⟨by rw [denoteArgs', denoteArgs], ?_⟩
    rw [denoteArgs]; exact ⟨henv, fun vs h v hv => by cases h; cases hv⟩
  | cons a as iha =>
    obtain ⟨h1, g1⟩ := ih a (.head _) env henv
    have ihas := iha (fun b hb => ih b (.tail _ hb))
    rw [denoteArgs', denoteArgs]
    simp only [bind, StateT.bind, h1]
    rcases hr : denote bi fuel a env with ⟨o, env1⟩
    rw [hr] at g1
    obtain ⟨genv1, gv⟩ := g1
    cases o with
    | val w =>
      have hw := gv w rfl
      obtain ⟨h2, genv2, gvs⟩ := ihas env1 genv1
      refine ⟨?_, ?_⟩
      · dsimp only
        cases w <;> first
          | (simp [Value.deepNoControlFlow] at hw; done)
          | simp only [StateT.bind, h2]
      · dsimp only [StateT.bind]
        rcases hr2 : denoteArgs bi fuel as env1 with ⟨ro, env2⟩
        rw [hr2] at genv2 gvs
        refine ⟨genv2, ?_⟩
        rintro vs hvs v hv
        cases ro with
        | none => cases hvs
        | some rs =>
          have hvs' : some (w :: rs) = some vs := hvs
          cases hvs'
          rcases hv with _ | ⟨_, hv⟩
          · exact hw
          · exact gvs rs rfl v hv
    | _ => exact ⟨rfl, genv1, fun vs h => by cases h⟩

/-- **The two semantics coincide on the fragment.** From an environment carrying no
    control-flow value, under builtins that produce none from arguments carrying none, the
    run of `denote'` on a fragment expression is the run of `denote`, at every fuel, and
    that run carries no control-flow value. -/
theorem denote'_eq_denote_good (hbi : bi.DeepNoControlFlow) {e : ImpExpr} (h : ReifyFrag e)
    (env : Env) (henv : env.NoControlFlow) :
    denote' bi fuel e env = denote bi fuel e env ∧ Good (denote bi fuel e env) := by
  induction h generalizing env with
  | lit =>
    refine ⟨by rw [denote', denote], ?_⟩
    rw [denote]
    exact ⟨henv, fun v h => Outcome.val.inj h ▸ Value.ofLit_deepNoControlFlow _⟩
  | @var n =>
    refine ⟨by rw [denote', denote]; rfl, ?_⟩
    rw [denote]
    dsimp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure]
    rcases hn : env n with _ | w
    · exact ⟨henv, fun v h => by cases h⟩
    · exact ⟨henv, fun v h => Outcome.val.inj h ▸ henv n w hn⟩
  | @letBind n v b _ _ ihv ihb =>
    obtain ⟨h1, g1⟩ := ihv env henv
    rw [denote', denote]
    simp only [bind, StateT.bind, h1]
    rcases hr : denote bi fuel v env with ⟨o, env1⟩
    rw [hr] at g1
    obtain ⟨genv1, gv⟩ := g1
    cases o with
    | val w =>
      have hw := gv w rfl
      have henv2 : (env1.extend n w).NoControlFlow := genv1.extend hw
      obtain ⟨h2, g2⟩ := ihb _ henv2
      refine ⟨?_, ?_⟩
      · dsimp only
        cases w <;> first
          | (simp [Value.deepNoControlFlow] at hw; done)
          | exact h2
      · exact g2
    | _ => exact ⟨rfl, genv1, fun vs h => by cases h⟩
  | @app f args _ ih =>
    obtain ⟨h1, genv1, gvs⟩ := denoteArgs'_eq_denoteArgs args ih env henv
    rw [denote', denoteApp', denote]
    simp only [bind, StateT.bind, h1]
    rcases hr : denoteArgs bi fuel args env with ⟨ro, env1⟩
    rw [hr] at genv1 gvs
    refine ⟨rfl, ?_⟩
    cases ro with
    | none => exact ⟨genv1, fun v h => by cases h⟩
    | some vals =>
      dsimp only
      rcases hb : bi f vals with _ | w
      · exact ⟨genv1, fun v h => by cases h⟩
      · exact ⟨genv1, fun v h => Outcome.val.inj h ▸ hbi f vals w hb (gvs vals rfl)⟩
  | @tuple es _ ih =>
    obtain ⟨h1, genv1, gvs⟩ := denoteArgs'_eq_denoteArgs es ih env henv
    rw [denote', denote]
    simp only [bind, StateT.bind, h1]
    rcases hr : denoteArgs bi fuel es env with ⟨ro, env1⟩
    rw [hr] at genv1 gvs
    refine ⟨rfl, ?_⟩
    cases ro with
    | none => exact ⟨genv1, fun v h => by cases h⟩
    | some vals =>
      exact ⟨genv1, fun v h => Outcome.val.inj h ▸
        deepNoControlFlowList_of_forall vals (gvs vals rfl)⟩
  | @proj e i _ ih =>
    obtain ⟨h1, g1⟩ := ih env henv
    rw [denote', denote]
    simp only [bind, StateT.bind, h1]
    rcases hr : denote bi fuel e env with ⟨o, env1⟩
    rw [hr] at g1
    obtain ⟨genv1, gv⟩ := g1
    cases o with
    | val w =>
      have hw := gv w rfl
      refine ⟨?_, ?_⟩
      · dsimp only
        cases w <;> first
          | (simp [Value.deepNoControlFlow] at hw; done)
          | rfl
      · dsimp only
        rcases hp : w.projIdx i with _ | wi
        · exact ⟨genv1, fun v h => by cases h⟩
        · exact ⟨genv1, fun v h => Outcome.val.inj h ▸ Value.deepNoControlFlow_projIdx hw hp⟩
    | _ => exact ⟨rfl, genv1, fun vs h => by cases h⟩
  | @ifThenElse c t e _ _ _ ihc iht ihe =>
    obtain ⟨h1, g1⟩ := ihc env henv
    rw [denote', denote]
    simp only [bind, StateT.bind, h1]
    rcases hr : denote bi fuel c env with ⟨o, env1⟩
    rw [hr] at g1
    obtain ⟨genv1, gv⟩ := g1
    cases o with
    | val w =>
      have hw := gv w rfl
      cases w with
      | bool b =>
        cases b
        · exact ihe env1 genv1
        · exact iht env1 genv1
      | controlFlow => simp [Value.deepNoControlFlow] at hw
      | _ => exact ⟨rfl, genv1, fun vs h => by cases h⟩
    | _ => exact ⟨rfl, genv1, fun vs h => by cases h⟩

/-- On the fragment, from an environment carrying no control-flow value, under builtins that
    produce none from arguments carrying none, `denote'` and `denote` have the same run at
    every fuel. -/
theorem denote'_eq_denote (hbi : bi.DeepNoControlFlow) {e : ImpExpr} (h : ReifyFrag e)
    (env : Env) (henv : env.NoControlFlow) :
    denote' bi fuel e env = denote bi fuel e env :=
  (denote'_eq_denote_good hbi h env henv).1

/-- On the fragment, a value returned by the run of `denote'` is the value `evalImp` returns
    on `forToLoop e`. -/
theorem evalImp_of_denote' (hbi : bi.DeepNoControlFlow) {e : ImpExpr} (h : ReifyFrag e)
    {env : Env} (henv : env.NoControlFlow) {v : Value}
    (hv : (denote' bi fuel e env).1 = .val v) :
    ∃ env', evalImp bi fuel (forToLoop e) env = some (v, env') := by
  rw [denote'_eq_denote hbi h env henv] at hv
  refine ⟨(denote bi fuel e env).2, ?_⟩
  rw [forToLoop_eq_self h, evalImp, StateT.run]
  rcases hr : denote bi fuel e env with ⟨o, env'⟩
  rw [hr] at hv
  cases hv
  rfl

/-- **The ascent judgment gives the `evalImp` run.** A `FnCorres` statement of a fragment
    literal `e` from entry environments carrying no control-flow value, under builtins that
    produce none from arguments carrying none, gives, from some fuel on, the `evalImp` run of
    `forToLoop e` returning `enc (f a)`. This is the form `haxReadAgrees_sound` rewrites. -/
theorem fnCorres_evalImp {A β : Type} [HaxEnc β] (hbi : bi.DeepNoControlFlow) {e : ImpExpr}
    (h : ReifyFrag e) {entry : A → Env} {G : A → Prop} {f : A → β}
    (hentry : ∀ a, G a → (entry a).NoControlFlow) (hc : FnCorres bi e entry G f)
    (a : A) (hG : G a) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      ∃ env', evalImp bi fuel (forToLoop e) (entry a) = some (enc (f a), env') := by
  obtain ⟨fuel₀, hrun⟩ := hc a hG
  exact ⟨fuel₀, fun fuel hf => evalImp_of_denote' hbi h (hentry a hG) (hrun fuel hf)⟩

/-! ## The pilot through `evalImp` -/

section Pilot

variable {α : Type} [HaxEnc α] [HaxEnc.Inj α]

/-- The value of a leaf of a function returning `β` is an encoding of a value of `β`. -/
theorem liftFn_eq_enc {A B : Type} [HaxArgs A] [HaxEnc B] {g : A → B} {vs : List Value}
    {v : Value} (h : liftFn g vs = some v) : ∃ b : B, v = enc b := by
  unfold liftFn at h
  split at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · cases h

/-- The table `edBi` produces no control-flow value when the encoding of `α` carries none. -/
theorem edBi_deepNoControlFlow (hα : ∀ x : α, (enc x).deepNoControlFlow = true)
    (mul add sub : α → α → α) (double neg : α → α) (d : α) :
    (edBi mul add sub double neg d).DeepNoControlFlow := by
  intro f args v h _
  simp only [edBi, Table.toBuiltins, Table.over, List.lookup] at h
  split at h
  · rename_i g hg
    repeat' split at hg
    all_goals first
      | (cases hg; obtain ⟨b, rfl⟩ := liftFn_eq_enc h; exact hα b)
      | cases hg
  · cases h

/-- The pilot literal lies in the fragment. -/
theorem edwardsAddImp_reifyFrag : ReifyFrag edwardsAddImp := by
  unfold edwardsAddImp
  repeat' first
    | constructor
    | simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]

variable [HaxEnc.Plain α]

/-- **The pilot through `evalImp`.** From the environment binding `p` and `q`, when the
    encoding of `α` carries no control-flow value, the `evalImp` run of
    `forToLoop edwardsAddImp` under `edBi` returns the encoding of `edwardsAddLean`, from
    some fuel on. -/
theorem edwardsAdd_evalImp (hα : ∀ x : α, (enc x).deepNoControlFlow = true)
    (mul add sub : α → α → α) (double neg : α → α) (d : α) (p q : α × α × α × α) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → ∃ env',
      evalImp (edBi mul add sub double neg d) fuel (forToLoop edwardsAddImp)
          (bindParams [("p", enc p), ("q", enc q)]) =
        some (enc (edwardsAddLean mul add sub double d p q), env') := by
  have hp : ∀ r : α × α × α × α, (enc r).deepNoControlFlow = true := fun r => by
    obtain ⟨x, y, z, t⟩ := r
    simp [HaxTupleEnc.encList, Value.deepNoControlFlow, hα]
  exact fnCorres_evalImp (A := (α × α × α × α) × (α × α × α × α) × Unit)
    (f := fun a => edwardsAddLean mul add sub double d a.1 a.2.1)
    (edBi_deepNoControlFlow hα mul add sub double neg d) edwardsAddImp_reifyFrag
    (fun a _ => ((Env.NoControlFlow.empty.extend (hp a.2.1)).extend (hp a.1)))
    (edwardsAdd_fnCorres mul add sub double neg d) (p, q, ()) trivial

end Pilot

end CatCrypt.Hax.ReifyImp

end
