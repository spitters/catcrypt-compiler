/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine

/-!
# Inlining a pure closure at the level of call trees

A pure expression (`isPure`) changes no variable, but a call in it is an event of the call tree:
its reading from an environment is a tree of outcomes, independent of the fuel, whose leaves carry
that environment (`atEnv`). Instantiating the parameters of a pure body by arguments that read as
leaves keeps that tree (`subst_runT`). A call of the closure on arguments without calls under the
closure table at a tree table therefore reads as the instantiated body (`callT_ref`), and
`inlineCalls` relates the call trees of a continuation (`denoteT_inlineCalls`).

## Main definitions

* `atEnv`: a tree of results with the leaves paired with one environment.
* `SubstT`: the readings of a body and of its instantiation are one tree of outcomes.
* `AgreeR`: equal environments agreeing with the environment of the binding on the captures.

## Main results

* `subst_runT`: instantiation of a pure body keeps its tree of outcomes.
* `callT_ref`: a call of the closure reads as the instantiated body.
* `denoteT_inlineCalls`: the call trees of a continuation and of its rewriting are related.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine

open _root_.Hax
open _root_.Hax.InlineLocalClosures
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run
  denoteT_lit_run denoteT_var_run denoteT_var_run_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue (lift_bind_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)

variable {E : EventSig} {h₁ : ∀ e : E.Event, E.Resp e}

/-! ## Trees at an environment -/

/-- A tree of results with every leaf paired with the environment `env`. -/
def atEnv {α : Type} (t : CallTree E α) (env : Env) : CallTree E (α × Env) :=
  t.bind fun a => .ret (a, env)

/-- A continuation whose readings are trees at their environment, the same tree from every
    environment, sends a tree at an environment to a tree at that environment. -/
theorem bind_indep {α β : Type} (K : α → TM E β)
    (hK : ∀ a, ∃ u : CallTree E β, ∀ env, K a env = atEnv u env) :
    ∃ G : α → CallTree E β, ∀ (t : CallTree E α) (env : Env),
      (atEnv t env).bind (fun p => K p.1 p.2) = atEnv (t.bind G) env := by
  choose G hG using hK
  refine ⟨G, fun t env => ?_⟩
  simp only [atEnv, bind_assoc]
  congr 1
  funext a
  exact hG a env

/-- A computation reading as one tree at every environment, followed by such a continuation. -/
theorem indep_bind {α β : Type} (m : TM E α) (t : CallTree E α)
    (hm : ∀ env, m env = atEnv t env) (K : α → TM E β)
    (hK : ∀ a, ∃ u : CallTree E β, ∀ env, K a env = atEnv u env) :
    ∃ u : CallTree E β, ∀ env, (m >>= K) env = atEnv u env := by
  obtain ⟨G, hG⟩ := bind_indep K hK
  exact ⟨t.bind G, fun env => by rw [tm_bind_run, hm, hG]⟩

/-- The continuation of a call reads as one tree at every environment. -/
theorem appK_indep (bt : TreeTable E) (g : String) (ov : Option (List Value)) :
    ∃ u : CallTree E Outcome, ∀ env,
      (match ov with
        | some vals => do
          let r ← StateT.lift (bt g vals)
          match r with
          | some v => pure (Outcome.val v)
          | none => pure (.err s!"unknown function or bad args: {g}")
        | none => pure (.err "non-value in function arguments") : TM E Outcome) env =
        atEnv u env := by
  rcases ov with _ | vals
  · exact ⟨.ret _, fun _ => rfl⟩
  · exact indep_bind _ (bt g vals) (fun _ => rfl) _ fun r => by
      rcases r with _ | v
      · exact ⟨.ret _, fun _ => rfl⟩
      · exact ⟨.ret _, fun _ => rfl⟩

/-! ## Instantiation of a pure body -/

/-- The reading of `b` from `ρ'` and the reading of its instantiation from `σ` are one tree of
    outcomes, at every fuel, with the leaves at the respective environments. -/
def SubstT (bt : TreeTable E) (ps : List String) (args : List ImpExpr) (σ ρ' : Env)
    (b : ImpExpr) : Prop :=
  ∃ t : CallTree E Outcome, (∀ fuel, denoteT bt fuel b ρ' = atEnv t ρ') ∧
    ∀ fuel, denoteT bt fuel (subst ps args b) σ = atEnv t σ

/-- The argument readings of instantiated arguments. -/
theorem substArgsT (bt : TreeTable E) (ps : List String) (args : List ImpExpr) (σ ρ' : Env)
    (es : List ImpExpr) (ih : ∀ a, a ∈ es → SubstT bt ps args σ ρ' a) :
    ∃ t : CallTree E (Option (List Value)), (∀ fuel, denoteArgsT bt fuel es ρ' = atEnv t ρ') ∧
      ∀ fuel, denoteArgsT bt fuel (es.map (subst ps args)) σ = atEnv t σ := by
  induction es with
  | nil => exact ⟨.ret (some []), fun fuel => argsT_nil_run bt fuel ρ',
      fun fuel => argsT_nil_run bt fuel σ⟩
  | cons e es ihes =>
    obtain ⟨te, he1, he2⟩ := ih e List.mem_cons_self
    obtain ⟨tr, hr1, hr2⟩ := ihes fun a ha => ih a (List.mem_cons_of_mem e ha)
    have key : ∀ (x : ImpExpr) (xs : List ImpExpr) (env : Env),
        (∀ fuel, denoteT bt fuel x env = atEnv te env) →
        (∀ fuel, denoteArgsT bt fuel xs env = atEnv tr env) →
        ∀ fuel, denoteArgsT bt fuel (x :: xs) env = atEnv (te.bind fun o =>
          match o with
          | .val (.controlFlow _ _) => .ret none
          | .val v => tr.bind fun q => .ret (q.map (v :: ·))
          | _ => .ret none) env := by
      intro x xs env hx hxs fuel
      rw [argsT_cons_run, hx]
      simp only [atEnv, bind_assoc]
      congr 1
      funext o
      rcases o with v | _ | _ | _ | _
      · cases v <;> first
          | rfl
          | (simp only [CallTree.bind]; rw [hxs]; simp only [atEnv, bind_assoc]; rfl)
      all_goals rfl
    exact ⟨_, key e es ρ' he1 hr1, by simpa only [List.map_cons] using key _ _ σ he2 hr2⟩

/-- Two readings that are one tree at their environments, followed by one continuation whose
    readings are trees at their environment, are one tree at their environments. -/
theorem substT_bind {α : Type} {ρ' σ : Env} {K : α → TM E Outcome} (t : CallTree E α)
    (m₁ m₂ : Nat → TM E α) (n₁ n₂ : Nat → TM E Outcome)
    (h1 : ∀ fuel, m₁ fuel ρ' = atEnv t ρ') (h2 : ∀ fuel, m₂ fuel σ = atEnv t σ)
    (hn₁ : ∀ fuel, n₁ fuel = m₁ fuel >>= K) (hn₂ : ∀ fuel, n₂ fuel = m₂ fuel >>= K)
    (hK : ∀ a, ∃ u : CallTree E Outcome, ∀ env, K a env = atEnv u env) :
    ∃ u : CallTree E Outcome, (∀ fuel, n₁ fuel ρ' = atEnv u ρ') ∧
      ∀ fuel, n₂ fuel σ = atEnv u σ := by
  obtain ⟨G, hG⟩ := bind_indep K hK
  exact ⟨t.bind G, fun fuel => by rw [hn₁, tm_bind_run, h1, hG],
    fun fuel => by rw [hn₂, tm_bind_run, h2, hG]⟩

/-- **Instantiation of a pure body.** When every variable of `b` reads in `ρ'` the leaf that its
    instantiation reads in `σ`, the readings of `b` from `ρ'` and of its instantiation from `σ`
    are one tree of outcomes. -/
theorem subst_runT (bt : TreeTable E) (ps : List String) (args : List ImpExpr) (σ ρ' : Env)
    (b : ImpExpr) (hb : isPure b = true)
    (hvar : ∀ x, x ∈ pureVars b → ∃ o, (∀ fuel, denoteT bt fuel (.var x) ρ' = .ret (o, ρ')) ∧
      ∀ fuel, denoteT bt fuel ((argFor ps args x).getD (.var x)) σ = .ret (o, σ)) :
    SubstT bt ps args σ ρ' b := by
  induction b using ImpExpr.ind with
  | var x =>
    obtain ⟨o, h1, h2⟩ := hvar x (by simp [pureVars])
    exact ⟨.ret o, h1, fun fuel => by simp only [subst]; exact h2 fuel⟩
  | lit l =>
    exact ⟨.ret _, fun fuel => denoteT_lit_run bt fuel l ρ',
      fun fuel => by simp only [subst]; exact denoteT_lit_run bt fuel l σ⟩
  | unitVal =>
    exact ⟨.ret (.val .unit), fun fuel => by rw [denoteT]; rfl,
      fun fuel => by simp only [subst]; rw [denoteT]; rfl⟩
  | app g es ih =>
    simp only [isPure, allPure_eq, List.all_eq_true] at hb
    simp only [pureVars, pureVars.varsList_eq, List.mem_flatMap] at hvar
    obtain ⟨ta, ha1, ha2⟩ := substArgsT bt ps args σ ρ' es
      (fun a ha => ih a ha (hb a ha) (fun x hx => hvar x ⟨a, ha, hx⟩))
    refine substT_bind ta (fun fuel => denoteArgsT bt fuel es)
      (fun fuel => denoteArgsT bt fuel (es.map (subst ps args)))
      (fun fuel => denoteT bt fuel (.app g es))
      (fun fuel => denoteT bt fuel (subst ps args (.app g es)))
      ha1 ha2 (fun fuel => by rw [denoteT, denoteAppT])
      (fun fuel => by simp only [subst, subst.substList_eq]; rw [denoteT, denoteAppT]) ?_
    intro ov
    exact appK_indep bt g ov
  | tuple es ih =>
    simp only [isPure, allPure_eq, List.all_eq_true] at hb
    simp only [pureVars, pureVars.varsList_eq, List.mem_flatMap] at hvar
    obtain ⟨ta, ha1, ha2⟩ := substArgsT bt ps args σ ρ' es
      (fun a ha => ih a ha (hb a ha) (fun x hx => hvar x ⟨a, ha, hx⟩))
    refine substT_bind ta (fun fuel => denoteArgsT bt fuel es)
      (fun fuel => denoteArgsT bt fuel (es.map (subst ps args)))
      (fun fuel => denoteT bt fuel (.tuple es))
      (fun fuel => denoteT bt fuel (subst ps args (.tuple es)))
      ha1 ha2 (fun fuel => by rw [denoteT])
      (fun fuel => by simp only [subst, subst.substList_eq]; rw [denoteT]) ?_
    intro ov
    rcases ov with _ | vals
    · exact ⟨.ret _, fun _ => rfl⟩
    · exact ⟨.ret _, fun _ => rfl⟩
  | proj e i ih =>
    simp only [isPure] at hb
    simp only [pureVars] at hvar
    obtain ⟨te, he1, he2⟩ := ih hb hvar
    refine substT_bind te (fun fuel => denoteT bt fuel e)
      (fun fuel => denoteT bt fuel (subst ps args e))
      (fun fuel => denoteT bt fuel (.proj e i))
      (fun fuel => denoteT bt fuel (subst ps args (.proj e i)))
      he1 he2 (fun fuel => by rw [denoteT])
      (fun fuel => by simp only [subst]; rw [denoteT]) ?_
    intro o
    rcases o with v | _ | _ | _ | _
    · refine ⟨.ret (match v with
        | .controlFlow k w => .val (.controlFlow k w)
        | v =>
          match v.projIdx i with
          | some vi => .val vi
          | none => .err s!"projection index {i} out of range"), fun env => ?_⟩
      cases v <;> try rfl
      all_goals (simp only; split <;> (rename_i h; simp only [atEnv, CallTree.bind, h]; rfl))
    all_goals exact ⟨.ret _, fun _ => rfl⟩
  | _ => simp [isPure] at hb

/-- A variable read through the arguments: a parameter reads the value of its argument, and any
    other variable reads in `σ` the leaf it reads in `ρ`. -/
theorem argForT_run (bt : TreeTable E) (σ ρ : Env) (x : String) :
    ∀ (ps : List String) (targs : List ImpExpr) (vals : List Value),
      (∀ av, av ∈ targs.zip vals → ∀ fuel, denoteT bt fuel av.1 σ = .ret (.val av.2, σ)) →
      targs.length = ps.length → vals.length = ps.length → (x ∉ ps → σ x = ρ x) →
      ∃ o, (∀ fuel, denoteT bt fuel (.var x) (bindAll ρ ps vals) =
          .ret (o, bindAll ρ ps vals)) ∧
        ∀ fuel, denoteT bt fuel ((argFor ps targs x).getD (.var x)) σ = .ret (o, σ)
  | [], targs, vals, _, _, _, hx => by
    have hσ := hx List.not_mem_nil
    have hb : bindAll ρ [] vals = ρ := by cases vals <;> rfl
    have ha : argFor [] targs x = none := by cases targs <;> rfl
    exact ⟨_, fun fuel => by rw [hb, denoteT_var_eq],
      fun fuel => by rw [ha, Option.getD_none, denoteT_var_eq, hσ]⟩
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, hl, _ => by simp at hl
  | p :: ps, a :: as, v :: vs, h2, hl, hl', hx => by
    by_cases hxp : x = p
    · subst hxp
      have ha : argFor (x :: ps) (a :: as) x = some a := by simp [argFor]
      refine ⟨.val v, fun fuel => ?_, fun fuel => ?_⟩
      · simp only [bindAll]
        exact denoteT_var_run _ _ _ _ _ (Env.extend_same _ _ _)
      · rw [ha, Option.getD_some]
        exact h2 (a, v) (by simp) fuel
    · obtain ⟨o, h1, h3⟩ := argForT_run bt σ ρ x ps as vs (fun av h => h2 av (by simp [h]))
        (by simpa using hl) (by simpa using hl') (fun h => hx (by simp [hxp, h]))
      have ha : argFor (p :: ps) (a :: as) x = argFor ps as x := by simp [argFor, hxp]
      refine ⟨o, fun fuel => ?_, fun fuel => ?_⟩
      · have h1' := h1 fuel
        rw [denoteT_var_eq] at h1' ⊢
        simp only [CallTree.ret.injEq, Prod.mk.injEq] at h1'
        simp only [bindAll, Env.extend_other _ _ _ _ hxp, h1'.1]
      · rw [ha]; exact h3 fuel

/-! ## A call of the closure -/

/-- The relation along the continuation of a pure closure: equal environments agreeing with `ρ`
    on `K`. -/
def AgreeR (K : List String) (ρ : Env) (e₁ e₂ : Env) : Prop := e₁ = e₂ ∧ Agree K ρ e₂

/-- Extending both environments at a name off `K` keeps `AgreeR K ρ`. -/
theorem AgreeR.ext {K : List String} {ρ : Env} {n : String} (hn : n ∉ K) :
    ∀ e₁ e₂ w, AgreeR K ρ e₁ e₂ → AgreeR K ρ (e₁.extend n w) (e₂.extend n w) :=
  fun _ _ w h => ⟨h.1 ▸ rfl, Agree.extend h.2 hn w⟩

/-- **A call of the closure.** From equal environments agreeing with `ρ` on the captures, a call
    of `f` on arguments without calls under the closure table reads as the body instantiated at
    the arguments, a leaf that is not a value being a failed leaf. -/
theorem callT_ref (bt : TreeTable E) (fuel₀ : Nat) (f : String) (ps : List String)
    (body : ImpExpr) (ρ : Env) (hbody : isPure body = true) (args : List ImpExpr)
    (hnc : ∀ a, a ∈ args → noCalls a = true) (hlen : args.length = ps.length) (fuel : Nat) :
    RelT h₁ (AgreeR (captures ps body) ρ) (AgreeR (captures ps body) ρ) IsErr
      (denoteT bt fuel (subst ps args body))
      (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel (.app f args)) := by
  rintro e₁ e₂ ⟨rfl, hA⟩
  obtain ⟨ov, hov⟩ := noCallsArgs_aux e₁ args (fun a ha => noCalls_runT a (hnc a ha) e₁)
  rw [denoteT, denoteAppT, tm_bind_run, hov]
  rcases ov with _ | vals
  · exact .fail ⟨_, rfl⟩
  obtain ⟨-, hvlen, hz⟩ := noCallsArgs_vals bt fuel e₁ args vals e₁ hnc (hov bt fuel)
  have hvl : vals.length = ps.length := hvlen.trans hlen
  obtain ⟨t, h1, h2⟩ := subst_runT bt ps args e₁ (bindAll ρ ps vals) body hbody
    (fun x hx => argForT_run bt e₁ ρ x ps args vals (fun av hav fuel => hz av hav bt fuel) hlen
      hvl (fun hxp => hA x (by simp only [captures, List.mem_filter]; simp [hx, hxp])))
  rw [h2 fuel]
  dsimp only [CallTree.bind]
  rw [lift_bind_run]
  simp only [closureTableT, ite_true, hvl, h1 fuel₀, atEnv, bind_assoc]
  refine NFCallTreeAnfPick.ruttS_bind_same t fun o => ?_
  rcases o with w | _ | _ | _ | _
  · exact .ret ⟨rfl, rfl, hA⟩
  all_goals exact .fail ⟨_, rfl⟩

/-- One tree performed on both sides, followed by related continuations. -/
theorem RelT.bind_lift {α β : Type} {P Q : Env → Env → Prop} {bad : β → Prop}
    (t : CallTree E α) {k₁ k₂ : α → TM E β} (hk : ∀ a, RelT h₁ P Q bad (k₁ a) (k₂ a)) :
    RelT h₁ P Q bad (StateT.lift t >>= k₁) (StateT.lift t >>= k₂) := by
  intro e₁ e₂ hp
  rw [lift_bind_run, lift_bind_run]
  exact NFCallTreeAnfPick.ruttS_bind_same t fun a => hk a e₁ e₂ hp

/-- A call of `f` whose argument count differs from the parameter count reads as an error leaf
    under the closure table. -/
theorem callT_arity_err (bt : TreeTable E) (fuel₀ : Nat) (f : String) (ps : List String)
    (body : ImpExpr) (ρ : Env) (args : List ImpExpr) (hnc : ∀ a, a ∈ args → noCalls a = true)
    (hlen : args.length ≠ ps.length) (fuel : Nat) (env : Env) :
    ∃ a s, denoteT (closureTableT bt fuel₀ f ps body ρ) fuel (.app f args) env = .ret (a, s) ∧
      IsErr a := by
  obtain ⟨ov, hov⟩ := noCallsArgs_aux env args (fun a ha => noCalls_runT a (hnc a ha) env)
  rw [denoteT, denoteAppT, tm_bind_run, hov]
  rcases ov with _ | vals
  · exact ⟨_, _, rfl, _, rfl⟩
  obtain ⟨-, hvlen, -⟩ := noCallsArgs_vals bt fuel env args vals env hnc (hov bt fuel)
  have hvl : vals.length ≠ ps.length := hvlen ▸ hlen
  dsimp only [CallTree.bind]
  rw [lift_bind_run]
  simp only [closureTableT, ite_true, hvl, ite_false]
  exact ⟨_, _, rfl, _, rfl⟩

/-- The match readings over related arm bodies, from equal environments agreeing with `ρ` on
    `K`, for patterns binding no variable of `K`. -/
theorem armsT_ref {K : List String} {ρ : Env} {bt₁ bt₂ : TreeTable E} (g : ImpExpr → ImpExpr)
    (arms : List (ImpPat × ImpExpr))
    (hK : ∀ pa, pa ∈ arms → ∀ x, x ∈ patVars pa.1 → K.contains x = false)
    (ih : ∀ pa, pa ∈ arms → ∀ fuel,
      RelT h₁ (AgreeR K ρ) (AgreeR K ρ) IsErr (denoteT bt₁ fuel (g pa.2)) (denoteT bt₂ fuel pa.2))
    (fuel : Nat) (v : Value) :
    RelT h₁ (AgreeR K ρ) (AgreeR K ρ) IsErr
      (denoteMatchArmsT bt₁ fuel v (arms.map fun (p, e) => (p, g e)))
      (denoteMatchArmsT bt₂ fuel v arms) := by
  induction arms with
  | nil => simp only [List.map_nil, denoteMatchArmsT]; exact RelT.pure _
  | cons pa rest iha =>
    obtain ⟨p, e⟩ := pa
    simp only [List.map_cons, denoteMatchArmsT]
    refine RelT.get fun e₁ e₂ he => ?_
    obtain ⟨rfl, hA⟩ := he
    split
    · rename_i env' hm
      refine RelT.set ⟨rfl, fun x hx => ?_⟩ (fun _ => ih (p, e) List.mem_cons_self fuel)
      rw [matchPat_frame x p v e₁ env' hm (fun hxp => by
        have := hK (p, e) List.mem_cons_self x hxp
        simp [hx] at this)]
      exact hA x hx
    · exact iha (fun pa hpa => hK pa (List.mem_cons_of_mem _ hpa))
        (fun pa hpa => ih pa (List.mem_cons_of_mem _ hpa))

/-- **Inlining the calls of a pure closure.** For a pure body and a continuation `e` whose calls
    of `f` pass arguments without calls and which binds no captured variable, the call tree of
    `e` read with the closure table of `f` defined in `ρ` is related to the call tree of
    `inlineCalls f ps body e` read with `bt`, from equal environments agreeing with `ρ` on the
    captures: a leaf that is an error is a failed leaf, and every other leaf is matched by an
    equal leaf. -/
theorem denoteT_inlineCalls (bt : TreeTable E) (fuel₀ : Nat) (f : String) (ps : List String)
    (body : ImpExpr) (ρ : Env) (hbody : isPure body = true) (e : ImpExpr) :
    noBind (captures ps body) e = true → argsFree f e = true → ∀ fuel,
      RelT h₁ (AgreeR (captures ps body) ρ) (AgreeR (captures ps body) ρ) IsErr
        (denoteT bt fuel (inlineCalls f ps body e))
        (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel e) := by
  induction e using ImpExpr.ind with
  | app g args ih =>
    intro hK hc fuel
    simp only [noBind, noBind.noBindList_eq, List.all_eq_true] at hK
    simp only [argsFree, argsFree.argsFreeList_eq, Bool.and_eq_true, Bool.or_eq_true,
      bne_iff_ne, ne_eq, List.all_eq_true] at hc
    have ih' := fun a ha => ih a ha (hK a ha) (hc.2 a ha)
    by_cases hgf : g = f
    · subst hgf
      have hp : ∀ a, a ∈ args → noCalls a = true := by
        simpa [noCalls.allNo_eq] using hc.1
      by_cases hl : args.length = ps.length
      · have hmap : args.map (inlineCalls g ps body) = args :=
          (List.map_congr_left fun a ha => inlineCalls_noCalls g ps body a (hp a ha)).trans
            (by simp)
        simp only [inlineCalls, hl, and_self, ite_true, inlineCalls.mapExpr_eq, hmap]
        exact callT_ref bt fuel₀ g ps body ρ hbody args hp hl fuel
      · exact RelT.of_bad (callT_arity_err bt fuel₀ g ps body ρ args hp hl fuel)
    · simp only [inlineCalls, hgf, false_and, ite_false, inlineCalls.mapExpr_eq, denoteT]
      unfold denoteAppT
      refine RelT.bind (badα := fun o => o = none) (argsT_rel _ args fuel fun a ha => ih' a ha fuel)
        (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, _, rfl, _, rfl⟩)
      simp only [closureTableT, hgf, ite_false]
      split
      · exact RelT.bind_lift _ fun r => by split <;> exact RelT.pure _
      · exact absurd rfl hr
  | tuple es ih =>
    intro hK hc fuel
    simp only [noBind, noBind.noBindList_eq, List.all_eq_true] at hK
    simp only [argsFree, argsFree.argsFreeList_eq, List.all_eq_true] at hc
    have ih' := fun a ha => ih a ha (hK a ha) (hc a ha)
    simp only [inlineCalls, inlineCalls.mapExpr_eq, denoteT]
    refine RelT.bind (badα := fun o => o = none) (argsT_rel _ es fuel fun a ha => ih' a ha fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, _, rfl, _, rfl⟩)
    split <;> exact RelT.pure _
  | match_ scrut arms ihs iha =>
    intro hK hc fuel
    simp only [noBind, noBind.noBindArms_eq, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at hK
    simp only [argsFree, argsFree.argsFreeArms_eq, Bool.and_eq_true, List.all_eq_true] at hc
    have hs := ihs hK.1 hc.1
    have ha := armsT_ref (bt₁ := bt) (bt₂ := closureTableT bt fuel₀ f ps body ρ)
      (inlineCalls f ps body) arms
      (fun pa hpa x hx => by
        have := (hK.2 pa hpa).1 x hx
        simpa using this)
      (fun pa hpa => iha pa hpa (hK.2 pa hpa).2 (hc.2 pa hpa))
    simp only [inlineCalls, inlineCalls.mapArms_eq, denoteT]
    relt_step
  | lam qs b ihb =>
    intro _ _ fuel
    exact RelT.of_bad fun _ => by rw [denoteT]; exact ⟨_, _, rfl, _, rfl⟩
  | forLoop v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopOrigT_rel (bt₁ := bt) (AgreeR.ext (by simpa using hK.1.1.1)) (ihb hK.2 hc.2)
    simp only [inlineCalls, denoteT]
    relt_step
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopRevOrigT_rel (bt₁ := bt) (AgreeR.ext (by simpa using hK.1.1.1)) (ihb hK.2 hc.2)
    simp only [inlineCalls, denoteT]
    relt_step
  | forFold v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopT_rel (bt₁ := bt) (AgreeR.ext (by simpa using hK.1.1.1)) (ihb hK.2 hc.2)
    simp only [inlineCalls, denoteT]
    relt_step
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopRevT_rel (bt₁ := bt) (AgreeR.ext (by simpa using hK.1.1.1)) (ihb hK.2 hc.2)
    simp only [inlineCalls, denoteT]
    relt_step
  | forFoldReturn v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopReturnT_rel (bt₁ := bt) (AgreeR.ext (by simpa using hK.1.1.1)) (ihb hK.2 hc.2)
    simp only [inlineCalls, denoteT]
    relt_step
  | forFoldRevReturn v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopRevReturnT_rel (bt₁ := bt) (AgreeR.ext (by simpa using hK.1.1.1)) (ihb hK.2 hc.2)
    simp only [inlineCalls, denoteT]
    relt_step
  | whileLoop c b ihc ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true] at hK hc
    simp only [inlineCalls, denoteT]
    exact whileOrigT_rel (ihc hK.1 hc.1) (ihb hK.2 hc.2) fuel
  | whileFold c b ihc ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true] at hK hc
    simp only [inlineCalls, denoteT]
    exact whileT_rel (ihc hK.1 hc.1) (ihb hK.2 hc.2) fuel
  | whileFoldReturn c b ihc ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true] at hK hc
    simp only [inlineCalls, denoteT]
    exact whileReturnT_rel (ihc hK.1 hc.1) (ihb hK.2 hc.2) fuel
  | letBind n v b ihv ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hn := AgreeR.ext (ρ := ρ) (by simpa using hK.1.1 : n ∉ captures ps body)
    have hv := ihv hK.1.2 hc.1
    have hb := ihb hK.2 hc.2
    simp only [inlineCalls, denoteT]
    relt_step
  | assign n rhs ih =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hn := AgreeR.ext (ρ := ρ) (by simpa using hK.1 : n ∉ captures ps body)
    have hr := ih hK.2 hc
    simp only [inlineCalls, denoteT]
    relt_step
  | seq a b iha ihb =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true] at hK hc
    have ha := iha hK.1 hc.1
    have hb := ihb hK.2 hc.2
    simp only [inlineCalls, denoteT]
    relt_step
  | ifThenElse c t e ihc iht ihe =>
    intro hK hc fuel
    simp only [noBind, argsFree, Bool.and_eq_true] at hK hc
    have h1 := ihc hK.1.1 hc.1.1
    have h2 := iht hK.1.2 hc.1.2
    have h3 := ihe hK.2 hc.2
    simp only [inlineCalls, denoteT]
    relt_step
  | proj e _ ih | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih
  | typeAscription e _ ih =>
    intro hK hc fuel
    simp only [noBind, argsFree] at hK hc
    have h := ih hK hc
    simp only [inlineCalls, denoteT]
    relt_step
  | var x =>
    intro _ _ fuel
    rintro e₁ e₂ ⟨rfl, hA⟩
    simp only [inlineCalls]
    rw [denoteT_var_eq, denoteT_var_eq]
    exact .ret ⟨rfl, rfl, hA⟩
  | _ =>
    intro _ _ fuel
    simp only [inlineCalls, denoteT]
    relt_step


end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine
