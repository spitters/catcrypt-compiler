/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main_Full
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_AnfShaped_Full
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_While

/-!
# Program-level simulation for `haxToLowCT`

`haxToLowCT_simulates_full` (`HaxToLowCTSim_Main_Full.lean`) takes its call-side
conditions universally quantified over every name, state and argument list.
§1 shows that each of those five hypotheses is unsatisfiable on its own, so the
theorem, and every consumer that threads them through, is a conditional whose
premise is `False`.

This module restates the simulation with side conditions that are decided on the
source program:

* `simScope S Γ e` is a syntactic scope checker.  `Γ` records the names known to
  be tower-bound in the entry state, with their `TowerType`; `S` is the set of
  scalar-binding names.  The checker threads `Γ` through the program (each
  tower-typed `let` extends it), requires every leaf-call argument to be a
  tower-bound variable of the callee's type, every scalar `let`/`assign` name to
  be in `S`, every tower-binding name to be outside `S`, and every alias
  `let n = s` to satisfy `n = s`.  It returns the scope at the exit.
* `ScopeBound rs Γ` and `NamesFresh rs S` are the state-level preconditions on
  the entry state: the names of `Γ` are tower-bound at their recorded type, and
  the names of `S` have no tower binding.
* `ProgSim` is the simulation predicate under these conditions; its conclusion
  re-establishes `ScopeBound` at the exit scope and `NamesFresh`, which is what
  the `seq` and `whileLoop` arms need to continue.

The arms covered: `var`, `unitVal`, `seq`, `tuple` of variables, scalar-literal
`letBind`/`assign`, leaf-call `letBind`/`assign`, alias `letBind` (with `n = s`),
tuple-component `letBind`, `ifThenElse` on a variable, `whileLoop` on a variable
(from the body's induction hypothesis and `RustExec.whileTrue`/`whileFalse`).
The `array_update` and `index` call arms are the two fields of `ProgramSimArms`,
each dischargeable by vacuity of the builtin (`ProgramSimArms_of_vacuity`).
The `match_` arm and every constructor `haxToLowCT` rejects are outside the
checker (`simScope` returns `none`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote denoteWhile denoteArgs defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  The universal call-side hypotheses are unsatisfiable

Each hypothesis of `haxToLowCT_simulates_full` that is quantified over every
name, state or argument list has a counterexample. -/

/-- The empty tower state, with all scalars zero. -/
def rsEmpty : RustState := { rsTower := fun _ => none, rsScalar := fun _ => 0 }

/-- `∀ name rs, TowerFresh rs name` fails at a state with one tower binding. -/
theorem hScalarFresh_all_unsat :
    ¬ (∀ (name : String) (rs : RustState), TowerFresh rs name) := by
  intro h
  have hx := h "x" (rsSetTower rsEmpty "x" ⟨.TFp, default⟩)
  unfold TowerFresh at hx
  rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same] at hx
  cases hx

/-- `hDestBoundAll` fails at the empty tower state. -/
theorem hDestBoundAll_unsat :
    ¬ (∀ (f name : String) (rs : RustState),
         ∃ oldDestV : RustVal (towerOfCallName f),
           locatedLookup rs { locVar := name, locSrc := towerOfCallName f }
             = some oldDestV) := by
  intro h
  obtain ⟨_, hv⟩ := h "fp_add" "x" rsEmpty
  simp [locatedLookup, rsEmpty] at hv

/-- `hArgsEnvAll` fails at an argument list containing a literal. -/
theorem hArgsEnvAll_unsat :
    ¬ (∀ (_f : String) (args : List ImpExpr) (env : Env),
         ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w) := by
  intro h
  obtain ⟨n, hn, _⟩ := h "f" [.unitVal] (fun _ => none) .unitVal (List.mem_singleton.mpr rfl)
  cases hn

/-- `hArgsBoundAll` fails at the empty tower state with one variable argument. -/
theorem hArgsBoundAll_unsat :
    ¬ (∀ (f : String) (args : List ImpExpr) (rs : RustState) args',
         haxArgsToLocated (towerOfCallName f) args = some args' →
         ArgsTowerBound rs args') := by
  intro h
  have hb := h "fp_add" [.var "x"] rsEmpty
    [{ locVar := "x", locSrc := towerOfCallName "fp_add" }]
    (by simp [haxArgsToLocated, haxArgToLocated])
  obtain ⟨_, hv⟩ := hb _ (List.mem_singleton.mpr rfl)
  simp [rsEmpty] at hv

/-- `hArgsFreshAll` fails when the destination name is also an argument. -/
theorem hArgsFreshAll_unsat :
    ¬ (∀ (f : String) (args : List ImpExpr) (name : String) args',
         haxArgsToLocated (towerOfCallName f) args = some args' →
         ∀ a ∈ args', a.locVar ≠ name) := by
  intro h
  exact h "fp_add" [.var "x"] "x" [{ locVar := "x", locSrc := towerOfCallName "fp_add" }]
    (by simp [haxArgsToLocated, haxArgToLocated]) _ (List.mem_singleton.mpr rfl) rfl

/-- The conjunction of the universal freshness, destination-bound and
    argument-environment hypotheses of `haxToLowCT_simulates_full` is
    unsatisfiable. -/
theorem sim_universal_hyps_unsat :
    ¬ ((∀ (name : String) (rs : RustState), TowerFresh rs name)
       ∧ (∀ (f name : String) (rs : RustState),
            ∃ oldDestV : RustVal (towerOfCallName f),
              locatedLookup rs { locVar := name, locSrc := towerOfCallName f }
                = some oldDestV)
       ∧ (∀ (_f : String) (args : List ImpExpr) (env : Env),
            ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)) :=
  fun h => hScalarFresh_all_unsat h.1

/-! ## §2  The syntactic scope checker -/

/-- Names known to be tower-bound, with their `TowerType`. -/
abbrev TowerScope := List (String × TowerType)

/-- The names of `Γ` are tower-bound in `rs` at their recorded type. -/
def ScopeBound (rs : RustState) (Γ : TowerScope) : Prop :=
  ∀ n dt, List.lookup n Γ = some dt → ∃ val, rs.rsTower n = some ⟨dt, val⟩

/-- The names of `S` have no tower binding in `rs`. -/
def NamesFresh (rs : RustState) (S : List String) : Prop :=
  ∀ n ∈ S, rs.rsTower n = none

/-- Binding `name` at `dt` is compatible with `Γ`: `name` is either absent from
    `Γ` or recorded at the same type. -/
def scopeCompat (Γ : TowerScope) (name : String) (dt : TowerType) : Bool :=
  match List.lookup name Γ with
  | none => true
  | some dt' => decide (dt' = dt)

/-- Every argument is a variable recorded in `Γ` at type `dt`. -/
def argsInScope (Γ : TowerScope) (dt : TowerType) : List ImpExpr → Bool
  | [] => true
  | .var n :: as => decide (List.lookup n Γ = some dt) && argsInScope Γ dt as
  | _ :: _ => false

/-- Every argument is a variable distinct from `name`. -/
def argsAvoid (name : String) : List ImpExpr → Bool
  | [] => true
  | .var n :: as => decide (n ≠ name) && argsAvoid name as
  | _ :: _ => false

/-- The scope checker.  `S` is the set of scalar-binding names, `Γ` the entry
    scope; the result is the exit scope, or `none` when the program is outside
    the checked fragment. -/
def simScope (S : List String) (Γ : TowerScope) : ImpExpr → Option TowerScope
  | .letBind name (.app f args) body =>
      if f = "array_update" then
        if args.all isVar then simScope S Γ body else none
      else if f = "index" then
        if args.all isVar && scopeCompat Γ name .TFp && !S.contains name then
          simScope S ((name, .TFp) :: Γ) body
        else none
      else
        let dt := towerOfCallName f
        if argsInScope Γ dt args && argsAvoid name args && scopeCompat Γ name dt
            && !S.contains name then
          simScope S ((name, dt) :: Γ) body
        else none
  | .letBind name (.lit _) body =>
      if S.contains name then simScope S Γ body else none
  | .letBind name (.var src) body =>
      if name = src then simScope S Γ body else none
  | .letBind name (.proj (.var t) _) body =>
      if decide (List.lookup t Γ = some .TFp) && decide (t ≠ name)
          && scopeCompat Γ name .TFp && !S.contains name then
        simScope S ((name, .TFp) :: Γ) body
      else none
  | .var _ => some Γ
  | .unitVal => some Γ
  | .seq a b =>
      match simScope S Γ a with
      | some Γ₁ => simScope S Γ₁ b
      | none => none
  | .ifThenElse (.var _) t e =>
      match simScope S Γ t, simScope S Γ e with
      | some _, some _ => some Γ
      | _, _ => none
  | .whileLoop (.var _) body =>
      match simScope S Γ body with
      | some _ => some Γ
      | none => none
  | .assign name (.lit _) => if S.contains name then some Γ else none
  | .assign name (.app f args) =>
      let dt := towerOfCallName f
      if argsInScope Γ dt args && decide (List.lookup name Γ = some dt)
          && !S.contains name then some Γ else none
  | .tuple es => if es.all isVar then some Γ else none
  | _ => none

/-- The scalar-binding names of a program: the names of its literal
    `letBind`s and `assign`s. -/
def scalarNames : ImpExpr → List String
  | .letBind name (.lit _) body => name :: scalarNames body
  | .letBind _ _ body => scalarNames body
  | .seq a b => scalarNames a ++ scalarNames b
  | .ifThenElse _ t e => scalarNames t ++ scalarNames e
  | .whileLoop _ body => scalarNames body
  | .assign name (.lit _) => [name]
  | _ => []

/-- The decidable well-formedness predicate: the checker accepts `e` from the
    entry scope `Γ` with `scalarNames e` as the scalar-name set. -/
def SimWellFormed (Γ : TowerScope) (e : ImpExpr) : Bool :=
  (simScope (scalarNames e) Γ e).isSome

/-! ## §3  Syntactic lemmas on the checker -/

theorem lookup_cons_of_scopeCompat (Γ : TowerScope) (name : String) (dt : TowerType)
    (hC : scopeCompat Γ name dt = true) (m : String) (dt' : TowerType)
    (h : List.lookup m Γ = some dt') :
    List.lookup m ((name, dt) :: Γ) = some dt' := by
  by_cases hm : m = name
  · subst hm
    unfold scopeCompat at hC
    rw [h] at hC
    simp only [decide_eq_true_eq] at hC
    subst hC
    simp [List.lookup]
  · have hb : (m == name) = false := beq_eq_false_iff_ne.mpr hm
    simp [List.lookup, hb, h]

theorem lookup_cons_self (Γ : TowerScope) (name : String) (dt : TowerType) :
    List.lookup name ((name, dt) :: Γ) = some dt := by
  simp [List.lookup]

theorem lookup_cons_other (Γ : TowerScope) (name : String) (dt : TowerType)
    (m : String) (hm : m ≠ name) :
    List.lookup m ((name, dt) :: Γ) = List.lookup m Γ := by
  have hb : (m == name) = false := beq_eq_false_iff_ne.mpr hm
  simp [List.lookup, hb]

/-- The exit scope of the checker extends the entry scope. -/
theorem simScope_lookup_mono (S : List String) (e : ImpExpr) :
    ∀ (Γ Γ' : TowerScope), simScope S Γ e = some Γ' →
      ∀ m dt, List.lookup m Γ = some dt → List.lookup m Γ' = some dt := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro Γ Γ' h m dt hm
    cases val with
    | app f args =>
      simp only [simScope] at h
      by_cases hArr : f = "array_update"
      · rw [if_pos hArr] at h
        by_cases hAll : args.all isVar = true
        · rw [if_pos hAll] at h
          exact ihBody Γ Γ' h m dt hm
        · rw [if_neg hAll] at h; cases h
      · rw [if_neg hArr] at h
        by_cases hIdx : f = "index"
        · rw [if_pos hIdx] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            exact ihBody _ Γ' h m dt
              (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
          · cases h
        · rw [if_neg hIdx] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            exact ihBody _ Γ' h m dt
              (lookup_cons_of_scopeCompat Γ name (towerOfCallName f) hc.1.2 m dt hm)
          · cases h
    | lit l =>
      simp only [simScope] at h
      split at h
      · exact ihBody Γ Γ' h m dt hm
      · cases h
    | var src =>
      simp only [simScope] at h
      split at h
      · exact ihBody Γ Γ' h m dt hm
      · cases h
    | proj pe i =>
      cases pe with
      | var t =>
        simp only [simScope] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      | _ => simp [simScope] at h
    | _ => simp [simScope] at h
  | var _ => intro Γ Γ' h m dt hm; simp only [simScope, Option.some.injEq] at h; subst h; exact hm
  | unitVal => intro Γ Γ' h m dt hm; simp only [simScope, Option.some.injEq] at h; subst h; exact hm
  | seq a b iha ihb =>
    intro Γ Γ' h m dt hm
    simp only [simScope] at h
    rcases hA : simScope S Γ a with _ | Γ₁
    · rw [hA] at h; cases h
    · rw [hA] at h
      exact ihb Γ₁ Γ' h m dt (iha Γ Γ₁ hA m dt hm)
  | ifThenElse c t e _ _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScope] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | _ => simp [simScope] at h
  | whileLoop c body _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScope] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | _ => simp [simScope] at h
  | assign name rhs _ =>
    intro Γ Γ' h m dt hm
    cases rhs with
    | lit _ =>
      simp only [simScope] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | app f args =>
      simp only [simScope] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | _ => simp [simScope] at h
  | tuple es _ =>
    intro Γ Γ' h m dt hm
    simp only [simScope] at h
    split at h
    · rw [Option.some.injEq] at h; subst h; exact hm
    · cases h
  | _ => intro Γ Γ' h; simp [simScope] at h

/-- `ScopeBound` transfers along scope extension. -/
theorem ScopeBound_of_lookup_mono (rs : RustState) (Γ Γ' : TowerScope)
    (hMono : ∀ m dt, List.lookup m Γ = some dt → List.lookup m Γ' = some dt)
    (h : ScopeBound rs Γ') : ScopeBound rs Γ :=
  fun n dt hn => h n dt (hMono n dt hn)

theorem argsInScope_allVars (Γ : TowerScope) (dt : TowerType) :
    ∀ (args : List ImpExpr), argsInScope Γ dt args = true →
      ∀ a ∈ args, ∃ n, a = .var n
  | [], _, a, ha => by simp at ha
  | .var n :: as, h, a, ha => by
      simp only [argsInScope, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨n, rfl⟩
      · exact argsInScope_allVars Γ dt as h.2 a ha
  | .lit _ :: _, h, _, _ => by simp [argsInScope] at h
  | .letBind _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .lam _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .app _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .tuple _ :: _, h, _, _ => by simp [argsInScope] at h
  | .proj _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .ifThenElse _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .match_ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .unitVal :: _, h, _, _ => by simp [argsInScope] at h
  | .seq _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .borrow _ :: _, h, _, _ => by simp [argsInScope] at h
  | .deref _ :: _, h, _, _ => by simp [argsInScope] at h
  | .assign _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .forLoop _ _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .forLoopRev _ _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .whileLoop _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .break_ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .continue_ :: _, h, _, _ => by simp [argsInScope] at h
  | .earlyReturn _ :: _, h, _, _ => by simp [argsInScope] at h
  | .questionMark _ :: _, h, _, _ => by simp [argsInScope] at h
  | .forFold _ _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .forFoldRev _ _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .whileFold _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .forFoldReturn _ _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .forFoldRevReturn _ _ _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .whileFoldReturn _ _ :: _, h, _, _ => by simp [argsInScope] at h
  | .cfBreak _ :: _, h, _, _ => by simp [argsInScope] at h
  | .cfContinue _ :: _, h, _, _ => by simp [argsInScope] at h
  | .cfBreakContinue _ :: _, h, _, _ => by simp [argsInScope] at h

/-- Arguments in scope are tower-bound in a `ScopeBound` state. -/
theorem argsInScope_bound (Γ : TowerScope) (dt : TowerType) (rs : RustState)
    (hSB : ScopeBound rs Γ) :
    ∀ (args : List ImpExpr) (args' : List Located),
      argsInScope Γ dt args = true →
      haxArgsToLocated dt args = some args' →
      ArgsTowerBound rs args' := by
  intro args
  induction args with
  | nil =>
    intro args' _ hL
    simp only [haxArgsToLocated, Option.some.injEq] at hL
    subst hL
    intro a ha; simp at ha
  | cons a as ih =>
    intro args' hIn hL
    obtain ⟨n, rfl⟩ := argsInScope_allVars Γ dt (a :: as) hIn a (List.mem_cons_self ..)
    simp only [argsInScope, Bool.and_eq_true, decide_eq_true_eq] at hIn
    simp only [haxArgsToLocated, haxArgToLocated] at hL
    rcases hR : haxArgsToLocated dt as with _ | rest
    · rw [hR] at hL; cases hL
    · rw [hR] at hL
      simp only [Option.some.injEq] at hL
      subst hL
      intro b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · obtain ⟨val, hval⟩ := hSB n dt hIn.1
        exact ⟨val, hval⟩
      · exact ih rest hIn.2 hR b hb

/-- Arguments avoiding `name` translate to located arguments distinct from `name`. -/
theorem argsAvoid_fresh (name : String) (dt : TowerType) :
    ∀ (args : List ImpExpr) (args' : List Located),
      argsAvoid name args = true →
      haxArgsToLocated dt args = some args' →
      ∀ a ∈ args', a.locVar ≠ name := by
  intro args
  induction args with
  | nil =>
    intro args' _ hL
    simp only [haxArgsToLocated, Option.some.injEq] at hL
    subst hL
    intro a ha; simp at ha
  | cons a as ih =>
    intro args' hAv hL
    cases a with
    | var n =>
      simp only [argsAvoid, Bool.and_eq_true, decide_eq_true_eq] at hAv
      simp only [haxArgsToLocated, haxArgToLocated] at hL
      rcases hR : haxArgsToLocated dt as with _ | rest
      · rw [hR] at hL; cases hL
      · rw [hR] at hL
        simp only [Option.some.injEq] at hL
        subst hL
        intro b hb
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hAv.1
        · exact ih rest hAv.2 hR b hb
    | _ => simp [argsAvoid] at hAv

/-! ## §4  Source-side lemmas -/

/-- Unfold equation for `.app`. -/
theorem denote_app_run_eq (bi : Builtins) (fuel : Nat) (f : String)
    (args : List ImpExpr) (env : Env) :
    (denote bi fuel (.app f args)).run env =
      (match (denoteArgs bi fuel args).run env with
       | (some vals, env_a) =>
           (match bi f vals with
            | some v => (Outcome.val v, env_a)
            | none => (Outcome.err s!"unknown function or bad args: {f}", env_a))
       | (none, env_a) => (Outcome.err "non-value in function arguments", env_a)) := by
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  rw [show (denoteArgs bi fuel args) env = (denoteArgs bi fuel args).run env from rfl]
  rcases (denoteArgs bi fuel args).run env with ⟨mvals, env_a⟩
  cases mvals with
  | none => rfl
  | some vs =>
    dsimp only
    cases bi f vs <;> rfl

/-- A successful `denoteArgs` over variables resolves every variable in `env`. -/
theorem denoteArgs_vars_defined (bi : Builtins) (fuel : Nat) (env : Env) :
    ∀ (args : List ImpExpr) (vals : List Value) (env₂ : Env),
      (∀ a ∈ args, ∃ n, a = .var n) →
      (denoteArgs bi fuel args).run env = (some vals, env₂) →
      ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w := by
  intro args
  induction args with
  | nil => intro _ _ _ _ a ha; simp at ha
  | cons a as ih =>
    intro vals env₂ hVars h
    obtain ⟨n, rfl⟩ := hVars a (List.mem_cons_self ..)
    rw [denoteArgs_cons_run_eq, denote_var_run_eq] at h
    cases hen : env n with
    | none => simp only [hen] at h; cases h
    | some w =>
      simp only [hen] at h
      rcases hR : (denoteArgs bi fuel as).run env with ⟨rest, env_b⟩
      rw [hR] at h
      cases rest with
      | none => exact absurd (Prod.mk.inj h).1 (by simp)
      | some vs =>
        intro b hb
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact ⟨n, rfl, w, hen⟩
        · exact ih vs env_b (fun a' ha' => hVars a' (List.mem_cons_of_mem _ ha')) hR b hb

/-- A successful evaluation of `letBind name (.app f args) body` with variable
    arguments resolves every argument variable in `env`. -/
theorem evalImp_letBind_app_argsDefined (bi : Builtins) (fuel : Nat)
    (name f : String) (args : List ImpExpr) (body : ImpExpr) (env : Env)
    (v : Value) (env' : Env)
    (hVars : ∀ a ∈ args, ∃ n, a = .var n)
    (h : evalImp bi fuel (.letBind name (.app f args) body) env = some (v, env')) :
    ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w := by
  unfold evalImp at h
  rw [denote_letBind_run_eq, denote_app_run_eq] at h
  rcases hDA : (denoteArgs bi fuel args).run env with ⟨mvals, env_a⟩
  rw [hDA] at h
  cases mvals with
  | none => simp at h
  | some vals => exact denoteArgs_vars_defined bi fuel env args vals env_a hVars hDA

/-- A successful evaluation of `assign name (.app f args)` with variable
    arguments resolves every argument variable in `env`. -/
theorem evalImp_assign_app_argsDefined (bi : Builtins) (fuel : Nat)
    (name f : String) (args : List ImpExpr) (env : Env)
    (v : Value) (env' : Env)
    (hVars : ∀ a ∈ args, ∃ n, a = .var n)
    (h : evalImp bi fuel (.assign name (.app f args)) env = some (v, env')) :
    ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w := by
  unfold evalImp at h
  rw [denote_assign_run_eq, denote_app_run_eq] at h
  rcases hDA : (denoteArgs bi fuel args).run env with ⟨mvals, env_a⟩
  rw [hDA] at h
  cases mvals with
  | none => simp at h
  | some vals => exact denoteArgs_vars_defined bi fuel env args vals env_a hVars hDA

/-- Inverse for the alias `letBind name (.var src) body`. -/
theorem evalImp_letBind_var_inv (bi : Builtins) (fuel : Nat)
    (name src : String) (body : ImpExpr) (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.letBind name (.var src) body) env = some (v, env')) :
    ∃ w, env src = some w ∧
      evalImp bi fuel body (env.extend name w) = some (v, env') := by
  unfold evalImp at h ⊢
  rw [denote_letBind_run_eq, denote_var_run_eq] at h
  cases hen : env src with
  | none => simp only [hen] at h; cases h
  | some w =>
    simp only [hen] at h
    exact ⟨w, rfl, h⟩

/-- Extending an environment at a name with the value it already holds is the
    identity. -/
theorem Env.extend_self (env : Env) (name : String) (w : Value)
    (h : env name = some w) : env.extend name w = env := by
  funext x
  by_cases hx : x = name
  · subst hx; simp [CatCrypt.Hax.Env.extend, h]
  · simp [CatCrypt.Hax.Env.extend, hx]

/-- Step inverse for `whileLoop (.var cond) body` at successor fuel, under the
    outcome dichotomy of the body at the entry environment. -/
theorem evalImp_whileLoop_var_step_inv
    (bi : Builtins) (n : Nat) (cond : String) (body : ImpExpr)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi (n+1) (.whileLoop (.var cond) body) env = some (v, env'))
    (hBody : (∃ vB env_b, (denote bi (n+1) body).run env = (.val vB, env_b))
           ∨ (∃ msg env_b, (denote bi (n+1) body).run env = (.err msg, env_b))) :
    (env cond = some (.bool false) ∧ v = .unit ∧ env' = env)
  ∨ (∃ vB env_mid, env cond = some (.bool true) ∧
       evalImp bi (n+1) body env = some (vB, env_mid) ∧
       evalImp bi n (.whileLoop (.var cond) body) env_mid = some (v, env')) := by
  unfold evalImp at h
  rw [denote_whileLoop_run_eq, denoteWhile_succ_run, denote_var_run_eq] at h
  cases hen : env cond with
  | none => simp only [hen] at h; cases h
  | some w =>
    simp only [hen] at h
    cases w with
    | bool b =>
      cases b with
      | false =>
        left
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨rfl, h.1.symm, h.2.symm⟩
      | true =>
        right
        dsimp only at h
        rcases hBody with ⟨vB, env_b, hB⟩ | ⟨msg, env_b, hB⟩
        · rw [hB] at h
          dsimp only at h
          refine ⟨vB, env_b, rfl, ?_, ?_⟩
          · unfold evalImp; rw [hB]
          · unfold evalImp; rw [denote_whileLoop_run_eq]; exact h
        · rw [hB] at h; cases h
    | int _ => cases h
    | unit => cases h
    | tuple _ => cases h
    | option _ => cases h
    | result _ _ => cases h
    | controlFlow _ _ => cases h

/-- The body of a translated loop evaluates to a value or an error. -/
theorem denote_val_or_err_of_haxToLowCT (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (c : LowCT) (hHax : haxToLowCT e = some c) (env : Env) :
    (∃ v env', (denote bi fuel e).run env = (.val v, env'))
  ∨ (∃ msg env', (denote bi fuel e).run env = (.err msg, env')) :=
  AnfShaped_outcome_val_or_err bi fuel e env
    ((haxToLowCT_isSome_iff_anf e).mp (by rw [hHax]; rfl))

/-! ## §5  State-level lemmas -/

theorem mem_of_contains (S : List String) (n : String) (h : S.contains n = true) : n ∈ S := by
  simpa using h

theorem not_mem_of_not_contains (S : List String) (n : String) (h : (!S.contains n) = true) :
    n ∉ S := by
  simpa using h

/-- A tower binding at the recorded type is a successful `locatedLookup`. -/
theorem locatedLookup_of_rsTower (rs : RustState) (n : String) (dt : TowerType)
    (val : RustVal dt) (h : rs.rsTower n = some ⟨dt, val⟩) :
    locatedLookup rs { locVar := n, locSrc := dt } = some val := by
  unfold CatCrypt.Crypto.Jasmin.LowCT.locatedLookup
  simp [h]

theorem ScopeBound_rsSetTower_cons (rs : RustState) (Γ : TowerScope) (name : String)
    (dt : TowerType) (val : RustVal dt) (hC : scopeCompat Γ name dt = true)
    (h : ScopeBound rs Γ) :
    ScopeBound (rsSetTower rs name ⟨dt, val⟩) ((name, dt) :: Γ) := by
  intro m dt' hm
  by_cases hmn : m = name
  · subst hmn
    rw [lookup_cons_self] at hm
    rw [Option.some.injEq] at hm
    subst hm
    exact ⟨val, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same rs m ⟨_, val⟩⟩
  · rw [lookup_cons_other Γ name dt m hmn] at hm
    obtain ⟨w, hw⟩ := h m dt' hm
    refine ⟨w, ?_⟩
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs name m _ (Ne.symm hmn)]
    exact hw

theorem ScopeBound_rsSetTower_same (rs : RustState) (Γ : TowerScope) (name : String)
    (dt : TowerType) (val : RustVal dt) (hLk : List.lookup name Γ = some dt)
    (h : ScopeBound rs Γ) :
    ScopeBound (rsSetTower rs name ⟨dt, val⟩) Γ := by
  intro m dt' hm
  by_cases hmn : m = name
  · subst hmn
    rw [hLk, Option.some.injEq] at hm
    subst hm
    exact ⟨val, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same rs m ⟨_, val⟩⟩
  · obtain ⟨w, hw⟩ := h m dt' hm
    refine ⟨w, ?_⟩
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs name m _ (Ne.symm hmn)]
    exact hw

theorem NamesFresh_rsSetTower (rs : RustState) (S : List String) (name : String)
    (v : Σ t : TowerType, RustVal t) (hN : name ∉ S) (h : NamesFresh rs S) :
    NamesFresh (rsSetTower rs name v) S := by
  intro m hm
  have hne : m ≠ name := fun e => hN (e ▸ hm)
  rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs name m v (Ne.symm hne)]
  exact h m hm

/-! ## §6  The program-level simulation predicate -/

/-- Simulation of `e` under the checker's side conditions.  The conclusion
    re-establishes `ScopeBound` at the exit scope and `NamesFresh`. -/
def ProgSim (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S : List String) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (Γ Γ' : TowerScope) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    simScope S Γ e = some Γ' →
    ScopeBound rs Γ → NamesFresh rs S →
    haxToLowCT e = some c →
    evalImp bi fuel e env = some (v, env') →
    envAgreesRustFull bridge env rs →
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRustFull bridge env' rs' ∧
      ScopeBound rs' Γ' ∧ NamesFresh rs' S

/-- Bridge-level preconditions of the tuple-component arm: the tuple-load
    oracle is bridge-aligned with `Value.projIdx`, and every component of a
    bridged tuple is tower-typed. -/
structure ProjPreconds (bridge : ValueTowerBridge) (leafSpec : LeafSpec) : Prop where
  tupleAgrees : ∀ (name : String) (i : Nat) (vTup vi : Value) (srcV : RustVal .TFp),
    bridge .TFp vTup srcV → vTup.projIdx i = some vi →
    bridge .TFp vi
      (leafSpec.tupleLoad { locVar := name, locSrc := .TFp } (default : RustVal .TFp)
        ⟨.TFp, srcV⟩ i)
  compScalar : ∀ (vTup vi : Value) (srcV : RustVal .TFp) (i : Nat),
    bridge .TFp vTup srcV → vTup.projIdx i = some vi → valueToScalar vi = none

/-- The two call arms carried as hypotheses: the array-store and array-load
    calls, each as the inductive step from the body's simulation. -/
structure ProgramSimArms (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat)
    (leafSpec : LeafSpec) (S : List String) : Prop where
  arrayUpdate : ∀ (name : String) (args : List ImpExpr) (body : ImpExpr),
    ProgSim bridge bi N leafSpec S body →
    ProgSim bridge bi N leafSpec S (.letBind name (.app "array_update" args) body)
  index : ∀ (name : String) (args : List ImpExpr) (body : ImpExpr),
    ProgSim bridge bi N leafSpec S body →
    ProgSim bridge bi N leafSpec S (.letBind name (.app "index" args) body)

/-- The array-store arm holds when the builtin table does not implement
    `array_update`. -/
theorem progSim_arrayUpdate_of_vacuity (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat)
    (leafSpec : LeafSpec) (S : List String)
    (hArr : ∀ vals, bi "array_update" vals = none)
    (name : String) (args : List ImpExpr) (body : ImpExpr)
    (_ : ProgSim bridge bi N leafSpec S body) :
    ProgSim bridge bi N leafSpec S (.letBind name (.app "array_update" args) body) := by
  intro fuel Γ Γ' c env env' rs v _ _ _ _ hEval _
  exact absurd hEval (fun h =>
    evalImp_letBind_app_vacuous bi fuel name "array_update" args body env v env' hArr h)

/-- The array-load arm holds when the builtin table does not implement `index`. -/
theorem progSim_index_of_vacuity (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat)
    (leafSpec : LeafSpec) (S : List String)
    (hIdx : ∀ vals, bi "index" vals = none)
    (name : String) (args : List ImpExpr) (body : ImpExpr)
    (_ : ProgSim bridge bi N leafSpec S body) :
    ProgSim bridge bi N leafSpec S (.letBind name (.app "index" args) body) := by
  intro fuel Γ Γ' c env env' rs v _ _ _ _ hEval _
  exact absurd hEval (fun h =>
    evalImp_letBind_app_vacuous bi fuel name "index" args body env v env' hIdx h)

/-- Both hypothesis arms hold when the builtin table implements neither
    `array_update` nor `index`. -/
theorem ProgramSimArms_of_vacuity (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat)
    (leafSpec : LeafSpec) (S : List String)
    (hArr : ∀ vals, bi "array_update" vals = none)
    (hIdx : ∀ vals, bi "index" vals = none) :
    ProgramSimArms bridge bi N leafSpec S where
  arrayUpdate := progSim_arrayUpdate_of_vacuity bridge bi N leafSpec S hArr
  index := progSim_index_of_vacuity bridge bi N leafSpec S hIdx

/-! ## §7  Per-arm lemmas -/

section Arms

variable (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (S : List String)

/-- Every expression the checker rejects simulates trivially. -/
theorem progSim_of_simScope_none (e : ImpExpr) (h : ∀ Γ, simScope S Γ e = none) :
    ProgSim bridge bi N leafSpec S e := by
  intro fuel Γ Γ' c env env' rs v hScope
  rw [h Γ] at hScope
  cases hScope

theorem progSim_var (name : String) : ProgSim bridge bi N leafSpec S (.var name) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_var_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_var_inv bi fuel name env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSim_unitVal : ProgSim bridge bi N leafSpec S .unitVal := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_unitVal_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_unitVal_inv bi fuel env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSim_tuple (es : List ImpExpr) : ProgSim bridge bi N leafSpec S (.tuple es) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hAll
    rw [Option.some.injEq] at hScope
    subst hScope
    rw [haxToLowCT_tuple_of_vars es hAll] at hHax
    cases hHax
    have henv := evalImp_tuple_vars_inv bi fuel es env v env' hAll hEval
    subst henv
    exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩
  · cases hScope

theorem progSim_seq (a b : ImpExpr)
    (iha : ProgSim bridge bi N leafSpec S a) (ihb : ProgSim bridge bi N leafSpec S b) :
    ProgSim bridge bi N leafSpec S (.seq a b) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  rcases hA : simScope S Γ a with _ | Γ₁
  · rw [hA] at hScope; cases hScope
  rw [hA] at hScope
  obtain ⟨aC, bC, hAtrans, hBtrans, hC⟩ := haxToLowCT_seq_some a b c hHax
  subst hC
  obtain ⟨vA, env_mid, hAeval, hBeval⟩ := evalImp_seq_inv bi fuel a b env v env' hEval
  obtain ⟨rs_mid, hAexec, hAgreeMid, hSBmid, hSFmid⟩ :=
    iha fuel Γ Γ₁ aC env env_mid rs vA hA hSB hSF hAtrans hAeval hAgree
  obtain ⟨rs', hBexec, hAgree', hSB', hSF'⟩ :=
    ihb fuel Γ₁ Γ' bC env_mid env' rs_mid v hScope hSBmid hSFmid hBtrans hBeval hAgreeMid
  exact ⟨rs', rustExec_RSeq_chain N leafSpec aC bC rs rs_mid rs' hAexec hBexec,
         hAgree', hSB', hSF'⟩

theorem progSim_ifThenElse (cond : String) (t e : ImpExpr)
    (iht : ProgSim bridge bi N leafSpec S t) (ihe : ProgSim bridge bi N leafSpec S e) :
    ProgSim bridge bi N leafSpec S (.ifThenElse (.var cond) t e) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  rcases hT : simScope S Γ t with _ | Γt
  · rw [hT] at hScope; cases hScope
  rcases hE : simScope S Γ e with _ | Γe
  · rw [hT, hE] at hScope; cases hScope
  rw [hT, hE] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ := haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  rcases evalImp_ifThenElse_var_inv bi fuel cond t e env v env' hEval with
    ⟨hCond, hTeval⟩ | ⟨hCond, hEeval⟩
  · obtain ⟨rs', hTexec, hAgree', hSB', hSF'⟩ :=
      iht fuel Γ Γt tC env env' rs v hT hSB hSF hTtrans hTeval hAgree
    have hScalar : rs.rsScalar cond = 1 :=
      envAgreesRust_bool_to_scalar env rs cond true hAgree.1 hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_true N leafSpec cond tC eC rs rs' 1 hScalar
      (by decide) hTexec, hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γt (simScope_lookup_mono S t Γ Γt hT) hSB'
  · obtain ⟨rs', hEexec, hAgree', hSB', hSF'⟩ :=
      ihe fuel Γ Γe eC env env' rs v hE hSB hSF hEtrans hEeval hAgree
    have hScalar : rs.rsScalar cond = 0 :=
      envAgreesRust_bool_to_scalar env rs cond false hAgree.1 hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_false N leafSpec cond tC eC rs rs' hScalar hEexec,
      hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γe (simScope_lookup_mono S e Γ Γe hE) hSB'

/-- The loop arm: the body's simulation, at every fuel, gives the loop's by
    induction on fuel, through `RustExec.whileTrue` / `whileFalse`. -/
theorem progSim_whileLoop (cond : String) (body : ImpExpr)
    (ihBody : ProgSim bridge bi N leafSpec S body) :
    ProgSim bridge bi N leafSpec S (.whileLoop (.var cond) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  rcases hB : simScope S Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bC, hBtrans, hC⟩ := haxToLowCT_whileLoop_var_some cond body c hHax
  subst hC
  have hMono := simScope_lookup_mono S body Γ Γb hB
  induction fuel generalizing env env' rs v with
  | zero =>
    exact absurd hEval (fun h => evalImp_whileLoop_var_fuel_zero_inv bi cond body env v env' h)
  | succ n IH =>
    rcases evalImp_whileLoop_var_step_inv bi n cond body env v env' hEval
        (denote_val_or_err_of_haxToLowCT bi (n+1) body bC hBtrans env) with
      ⟨hCondF, hv, henv⟩ | ⟨vB, env_mid, hCondT, hBodyEval, hLoopRec⟩
    · subst hv
      subst henv
      have hScalar : rs.rsScalar cond = 0 :=
        envAgreesRust_bool_to_scalar _ rs cond false hAgree.1 hCondF
      exact ⟨rs, RustExec.whileFalse cond bC rs hScalar, hAgree, hSB, hSF⟩
    · have hScalar : rs.rsScalar cond = 1 :=
        envAgreesRust_bool_to_scalar env rs cond true hAgree.1 hCondT
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid⟩ :=
        ihBody (n+1) Γ Γb bC env env_mid rs vB hB hSB hSF hBtrans hBodyEval hAgree
      have hSBmid' : ScopeBound rs_mid Γ := ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid
      obtain ⟨rs', hLoopExec, hAgree', hSB', hSF'⟩ :=
        IH env_mid env' rs_mid v hSBmid' hSFmid hLoopRec hAgreeMid
      exact ⟨rs', RustExec.whileTrue cond bC rs rs_mid rs' 1 hScalar (by decide)
               hBodyExec hLoopExec, hAgree', hSB', hSF'⟩

theorem progSim_letBind_lit (name : String) (l : ImpLit) (body : ImpExpr)
    (ihBody : ProgSim bridge bi N leafSpec S body) :
    ProgSim bridge bi N leafSpec S (.letBind name (.lit l) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hIn
    obtain ⟨bodyC, n, hBodyTrans, hDecode, hC⟩ :=
      haxToLowCT_letBind_lit_some name l body c hHax
    subst hC
    have hBodyEval := evalImp_letBind_lit_inv bi fuel name l body env v env' hEval
    have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
    have hAgreeExt : envAgreesRustFull bridge (env.extend name (Value.ofLit l))
                      (rsSetScalar rs name n) :=
      envAgreesRustFull_extend_scalar_fresh bridge env rs name
        (Value.ofLit l) n hFresh hDecode hAgree
    obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
      ihBody fuel Γ Γ' bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name n) v
        hScope hSB hSF hBodyTrans hBodyEval hAgreeExt
    exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name n bodyC rs rs' hBodyExec,
           hAgree', hSB', hSF'⟩
  · cases hScope

theorem progSim_letBind_var (name src : String) (body : ImpExpr)
    (ihBody : ProgSim bridge bi N leafSpec S body) :
    ProgSim bridge bi N leafSpec S (.letBind name (.var src) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hEq
    subst hEq
    have hHax' : haxToLowCT body = some c := by
      simp only [haxToLowCT] at hHax
      exact hHax
    obtain ⟨w, hw, hBodyEval⟩ := evalImp_letBind_var_inv bi fuel _ _ body env v env' hEval
    rw [Env.extend_self env _ w hw] at hBodyEval
    exact ihBody fuel Γ Γ' c env env' rs v hScope hSB hSF hHax' hBodyEval hAgree
  · cases hScope

theorem progSim_letBind_app (name f : String) (args : List ImpExpr) (body : ImpExpr)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hf_arr : f ≠ "array_update") (hf_idx : f ≠ "index")
    (ihBody : ProgSim bridge bi N leafSpec S body) :
    ProgSim bridge bi N leafSpec S (.letBind name (.app f args) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope, if_neg hf_arr, if_neg hf_idx] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hArgsIn, hAvoid⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
      haxToLowCT_letBind_app_some name f args body c hf_arr hf_idx hHax
    subst hC
    have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f args body env v env'
      (argsInScope_allVars Γ _ args hArgsIn) hEval
    obtain ⟨vals, vRes, _, hBi, hBodyEval⟩ :=
      evalImp_letBind_app_vars_inv bi fuel name f args body env v env' hArgsEnv hEval
    have hAB : ArgsTowerBound rs args' := argsInScope_bound Γ _ rs hSB args args' hArgsIn hArgsT
    have hAF : ∀ a ∈ args', a.locVar ≠ name := argsAvoid_fresh name _ args args' hAvoid hArgsT
    have hDecode : valueToScalar vRes = none := hPre.leafScalar f vals vRes hBi
    set dt := towerOfCallName f with hdt_def
    set dest : Located := { locVar := name, locSrc := dt } with hdest_def
    set rs_init := rsSetTower rs name ⟨dt, default⟩ with hrs_init_def
    have hABinit : ArgsTowerBound rs_init args' :=
      ArgsTowerBound_preserved_extend rs args' name ⟨dt, default⟩ hAF hAB
    have hLookup : locatedLookup rs_init dest = some default := locatedLookup_letZero rs name dt
    set argList := args'.filterMap (fun a => rs_init.rsTower a.locVar) with hargList_def
    set newVal := leafSpec.call f dt (args'.map (·.locDst)) default argList with hnewVal_def
    set rs_mid := locatedUpdate rs_init dest newVal with hrs_mid_def
    have hCallArgs : ∀ a ∈ args', ∃ vv, rs_init.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
      hABinit
    have hCall : RustExec N leafSpec (.RCall f dest args') rs_init rs_mid :=
      RustExec.call (N := N) (leafSpec := leafSpec)
        f dest args' rs_init default argList hLookup rfl hCallArgs
    have hBridgeAgr : bridge dt vRes newVal := by
      have hL := hPre.allLeavesAgree f rs_init name args' vals vRes hBi hCallArgs
      have hOld : (locatedLookup rs_init { locVar := name, locSrc := dt }).getD default
                  = (default : RustVal dt) := by
        rw [hLookup]; rfl
      rw [hOld] at hL
      exact hL
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨dt, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨dt, default⟩) name ⟨dt, newVal⟩
           = rsSetTower rs name ⟨dt, newVal⟩
      exact rsSetTower_collapse rs name ⟨dt, default⟩ ⟨dt, newVal⟩
    have hAgreeMid : envAgreesRustFull bridge (env.extend name vRes) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustFull_extend_tower bridge env rs name vRes dt newVal
              hAgree hBridgeAgr hDecode
    have hSBmid : ScopeBound rs_mid ((name, dt) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name dt newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, dt) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
        hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name dt _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hCall hBodyExec
  · cases hScope

theorem progSim_letBind_proj (name t : String) (i : Nat) (body : ImpExpr)
    (hProj : ProjPreconds bridge leafSpec)
    (ihBody : ProgSim bridge bi N leafSpec S body) :
    ProgSim bridge bi N leafSpec S (.letBind name (.proj (.var t) i) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hLk, hNe⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_proj_some name t i body c hHax
    subst hC
    obtain ⟨vTup, vi, hEnvT, hProjI, hBodyEval⟩ :=
      evalImp_letBind_proj_inv bi fuel name t i body env v env' hEval
    obtain ⟨srcV, hRawT⟩ := hSB t .TFp hLk
    have hSrcLook : locatedLookup rs { locVar := t, locSrc := .TFp } = some srcV :=
      locatedLookup_of_rsTower rs t .TFp srcV hRawT
    set dst : Located := { locVar := name, locSrc := .TFp } with hdst
    set src : Located := { locVar := t, locSrc := .TFp } with hsrc
    set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
    have hDstLook : locatedLookup rs_init dst = some default :=
      locatedLookup_letZero rs name .TFp
    have hSrcLook' : locatedLookup rs_init src = some srcV := by
      rw [hrs_init,
          CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
            rs name ⟨.TFp, default⟩ src (Ne.symm hNe)]
      exact hSrcLook
    set newVal := leafSpec.tupleLoad dst default ⟨src.locDst, srcV⟩ i with hnewVal
    set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
    have hLoad : RustExec N leafSpec (.RTupleLoad dst src i) rs_init rs_mid :=
      RustExec.tupleLoad dst src i rs_init default srcV hDstLook hSrcLook'
    have hTupBridge : bridge .TFp vTup srcV := hAgree.2 t vTup hEnvT .TFp srcV hRawT
    have hCompBridge : bridge .TFp vi newVal :=
      hProj.tupleAgrees name i vTup vi srcV hTupBridge hProjI
    have hDecode : valueToScalar vi = none := hProj.compScalar vTup vi srcV i hTupBridge hProjI
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
          = rsSetTower rs name ⟨.TFp, newVal⟩
      exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
    have hAgreeMid : envAgreesRustFull bridge (env.extend name vi) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustFull_extend_tower bridge env rs name vi .TFp newVal
              hAgree hCompBridge hDecode
    have hSBmid : ScopeBound rs_mid ((name, .TFp) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vi) env' rs_mid v
        hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name .TFp _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hLoad hBodyExec
  · cases hScope

/-- The image of a scalar-literal assignment is an `RScalarSet` at that name. -/
theorem haxToLowCT_assign_lit_shape (name : String) (l : ImpLit) (c : LowCT)
    (h : haxToLowCT (.assign name (.lit l)) = some c) :
    ∃ m, c = .RScalarSet name m := by
  cases l with
  | uintLit w n =>
    rw [haxToLowCT_assign_lit_uintLit_some] at h
    exact ⟨n, ((Option.some.injEq _ _).mp h).symm⟩
  | bool b =>
    rw [haxToLowCT_assign_lit_bool_some] at h
    exact ⟨if b then 1 else 0, ((Option.some.injEq _ _).mp h).symm⟩
  | int n =>
    by_cases hn : 0 ≤ n
    · rw [haxToLowCT_assign_lit_int_some_of_nonneg name n hn] at h
      exact ⟨n.toNat, ((Option.some.injEq _ _).mp h).symm⟩
    · simp [haxToLowCT, hn] at h
  | unit => simp [haxToLowCT] at h
  | sintLit _ _ => simp [haxToLowCT] at h

theorem progSim_assign_lit (name : String) (l : ImpLit) :
    ProgSim bridge bi N leafSpec S (.assign name (.lit l)) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hIn
    rw [Option.some.injEq] at hScope
    subst hScope
    have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
    have key : HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
        (.assign name (.lit l)) c env env' rs v := by
      cases l with
      | uintLit w n =>
        exact simulates_assign_lit_uintLit_full bridge bi fuel N leafSpec
          name w n c env env' rs v hFresh
      | bool b =>
        exact simulates_assign_lit_bool_full bridge bi fuel N leafSpec
          name b c env env' rs v hFresh
      | int n =>
        by_cases hn : 0 ≤ n
        · exact simulates_assign_lit_int_full bridge bi fuel N leafSpec
            name n hn c env env' rs v hFresh
        · intro hHax' _ _; simp [haxToLowCT, hn] at hHax'
      | unit => intro hHax' _ _; simp [haxToLowCT] at hHax'
      | sintLit _ _ => intro hHax' _ _; simp [haxToLowCT] at hHax'
    obtain ⟨rs', hExec, hAgree'⟩ := key hHax hEval hAgree
    obtain ⟨m, hC⟩ := haxToLowCT_assign_lit_shape name l c hHax
    subst hC
    have hRs : rs' = rsSetScalar rs name m := by
      cases hExec
      rfl
    subst hRs
    exact ⟨_, hExec, hAgree', hSB, hSF⟩
  · cases hScope

theorem progSim_assign_app (name f : String) (args : List ImpExpr)
    (hPre : FullSimPreconds bi leafSpec bridge) :
    ProgSim bridge bi N leafSpec S (.assign name (.app f args)) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScope] at hScope
  split at hScope
  · rename_i hc
    rw [Option.some.injEq] at hScope
    subst hScope
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hArgsIn, hLk⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', hArgsT, hC⟩ := haxToLowCT_assign_app_some name f args c hHax
    have hArgsEnv := evalImp_assign_app_argsDefined bi fuel name f args env v env'
      (argsInScope_allVars Γ _ args hArgsIn) hEval
    have hAB : ArgsTowerBound rs args' := argsInScope_bound Γ _ rs hSB args args' hArgsIn hArgsT
    obtain ⟨oldV, hOld⟩ := hSB name (towerOfCallName f) hLk
    have hDestBound : ∃ oldDestV : RustVal (towerOfCallName f),
        locatedLookup rs { locVar := name, locSrc := towerOfCallName f } = some oldDestV :=
      ⟨oldV, locatedLookup_of_rsTower rs name _ oldV hOld⟩
    obtain ⟨rs', hExec, hAgree'⟩ :=
      haxToLowCT_simulates_assign_app_full bridge bi fuel N leafSpec name f args c env env' rs v
        (hPre.allLeavesAgree f) hArgsEnv
        (fun args'' h => by rw [hArgsT] at h; cases h; exact hAB)
        hDestBound (hPre.leafScalar f) hHax hEval hAgree
    subst hC
    have hRs : ∃ w, rs' = rsSetTower rs name ⟨towerOfCallName f, w⟩ := by
      cases hExec
      exact ⟨_, rfl⟩
    obtain ⟨w, hRs⟩ := hRs
    subst hRs
    exact ⟨_, hExec, hAgree', ScopeBound_rsSetTower_same rs Γ name _ w hLk hSB,
           NamesFresh_rsSetTower rs S name _ hNotMem hSF⟩
  · cases hScope

end Arms

/-! ## §8  The program-level theorem -/

/-- **Program-level simulation.**  Every source program the checker accepts
    simulates, with the call-side conditions decided on the program and the
    two state-level preconditions stated on the entry state. -/
theorem haxToLowCT_simulates_program
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S : List String)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (hArms : ProgramSimArms bridge bi N leafSpec S)
    (e : ImpExpr) : ProgSim bridge bi N leafSpec S e := by
  induction e using ImpExpr.ind with
  | var name => exact progSim_var bridge bi N leafSpec S name
  | unitVal => exact progSim_unitVal bridge bi N leafSpec S
  | seq a b iha ihb => exact progSim_seq bridge bi N leafSpec S a b iha ihb
  | tuple es _ => exact progSim_tuple bridge bi N leafSpec S es
  | letBind name val body _ ihBody =>
    cases val with
    | lit l => exact progSim_letBind_lit bridge bi N leafSpec S name l body ihBody
    | app f args =>
      by_cases hf_arr : f = "array_update"
      · subst hf_arr
        exact hArms.arrayUpdate name args body ihBody
      by_cases hf_idx : f = "index"
      · subst hf_idx
        exact hArms.index name args body ihBody
      exact progSim_letBind_app bridge bi N leafSpec S name f args body hPre hf_arr hf_idx ihBody
    | var src => exact progSim_letBind_var bridge bi N leafSpec S name src body ihBody
    | proj pe i =>
      cases pe with
      | var t => exact progSim_letBind_proj bridge bi N leafSpec S name t i body hProj ihBody
      | _ => exact progSim_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
    | _ => exact progSim_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | ifThenElse cond t e _ iht ihe =>
    cases cond with
    | var v_cond => exact progSim_ifThenElse bridge bi N leafSpec S v_cond t e iht ihe
    | _ => exact progSim_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | whileLoop cond body _ ihBody =>
    cases cond with
    | var v_cond => exact progSim_whileLoop bridge bi N leafSpec S v_cond body ihBody
    | _ => exact progSim_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | assign name rhs _ =>
    cases rhs with
    | lit l => exact progSim_assign_lit bridge bi N leafSpec S name l
    | app f args => exact progSim_assign_app bridge bi N leafSpec S name f args hPre
    | _ => exact progSim_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])
  | _ => exact progSim_of_simScope_none bridge bi N leafSpec S _ (fun Γ => by simp [simScope])

/-- The program-level simulation in the shape of `HaxToLowCTSimulatesFull`: a
    well-formed program, an entry state bound on `Γ` and fresh on the program's
    scalar names, and the bridge-level preconditions. -/
theorem haxToLowCT_simulates_wellFormed
    (bridge : ValueTowerBridge) (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (Γ : TowerScope)
    (hWF : SimWellFormed Γ e = true)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (hArms : ProgramSimArms bridge bi N leafSpec (scalarNames e))
    (rs : RustState) (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs (scalarNames e)) :
    ∀ (c : LowCT) (env env' : Env) (v : Value),
      HaxToLowCTSimulatesFull bridge bi fuel N leafSpec e c env env' rs v := by
  intro c env env' v hHax hEval hAgree
  unfold SimWellFormed at hWF
  rcases hS : simScope (scalarNames e) Γ e with _ | Γ'
  · rw [hS] at hWF; simp at hWF
  obtain ⟨rs', hExec, hAgree', _, _⟩ :=
    haxToLowCT_simulates_program bridge bi N leafSpec (scalarNames e) hPre hProj hArms e
      fuel Γ Γ' c env env' rs v hS hSB hSF hHax hEval hAgree
  exact ⟨rs', hExec, hAgree'⟩

end CatCrypt.Crypto.Hax
