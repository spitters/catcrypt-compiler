/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_AnfShaped

/-!
# H3 Blocker 2 finishing: combined `AnfShaped_outcome_val_or_err` theorem

Builds on the per-constructor helpers in `HaxToLowCTSim_AnfShaped.lean`
to close the full syntactic-to-semantic implication.  Unblocks the
`hBodyAlwaysVal` helper hypothesis used in
`HaxToLowCTSim_While.lean`'s `haxToLowCT_simulates_whileLoop_var`.

## Main exports

* `denoteWhile_zero`, `denoteWhile_succ_run` — unfold equations for
  `denoteWhile`, separated by fuel: the zero-fuel case returns the
  out-of-fuel error; the successor case exposes one iteration as a
  pair-match (analogous to `denote_letBind_run_eq` in the companion
  `_AnfShaped.lean` file).  The successor form keeps the recursive
  `denoteWhile bi fuel _ _` call opaque so it can be discharged by an
  induction hypothesis.
* `denote_whileLoop_run_eq`, `denote_match_run_eq` — unfold equations
  for the remaining compound constructors needed by the main proof.
* `denoteWhile_outcome_val_or_err` — outcome dichotomy for `denoteWhile`
  by strong induction on fuel, taking the body's dichotomy as a
  parameter.
* `denoteMatchArms_tuple2_outcome`, `AnfShaped_match_outcome` —
  outcome dichotomy for the 2-tuple-destructure match pattern that
  `AnfShaped` admits.
* `AnfShaped_outcome_val_or_err` — the combined dichotomy: every
  `AnfShaped` expression evaluates to `.val _` or `.err _` (never
  `.broke`, `.continued`, or `.earlyRet`).
* `hBodyAlwaysVal_of_AnfShaped` — derives the specific shape required
  by the whileLoop simulation lemma.
* `denoteForLoop_ge_run`, `denoteForLoop_zero_run`, `denoteForLoop_succ_run`,
  `denote_forLoop_lit_run` — unfold equations for counted loops.
* `denoteForLoop_val_or_err`, `denote_forLoop_val_or_err` — outcome dichotomy
  for counted loops.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType ImpPat Value Env Outcome Builtins
                   denote denoteWhile denoteMatchArms denoteForLoop denoteForLoopRev denoteArgs)

/-! ## §1  Unfold equation for `denoteWhile`

The recursive `denoteWhile` body — `if fuel = 0 then err else
do cond; match …` — does not reduce automatically under `simp only`
because the nested `match` patterns block reduction.  This unfold
lemma exposes the structure as a clean pair-match analogous to
`denote_letBind_run_eq`, allowing structural reasoning later. -/

/-- Unfold equation for `denoteWhile` at zero fuel. -/
theorem denoteWhile_zero (bi : Builtins) (cond body : ImpExpr) (env : Env) :
    (denoteWhile bi 0 cond body).run env = (Outcome.err "out of fuel", env) := by
  show (denoteWhile bi 0 cond body).run env = _
  unfold denoteWhile
  simp [StateT.run, pure, Pure.pure, StateT.pure]

/-- Unfold equation for `denoteWhile` at successor fuel: one iteration unfolded.

The recursive `denoteWhile` call in the body branch is kept opaque (via the
unapplied `StateT` value), allowing this lemma to be used in inductive
arguments where the recursive call is dispatched to the IH. -/
theorem denoteWhile_succ_run (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) (env : Env) :
    (denoteWhile bi (fuel + 1) cond body).run env =
      (match (denote bi (fuel + 1) cond).run env with
       | (.val (.bool true), env_a) =>
           (match (denote bi (fuel + 1) body).run env_a with
            | (.val _, env_b) => (denoteWhile bi fuel cond body).run env_b
            | (.continued, env_b) => (denoteWhile bi fuel cond body).run env_b
            | (.broke v, env_b) => (.val v, env_b)
            | (other, env_b) => (other, env_b))
       | (.val (.bool false), env_a) => (.val .unit, env_a)
       | (.val _, env_a) => (.err "while condition not a bool", env_a)
       | (other, env_a) => (other, env_a)) := by
  have hWhile : denoteWhile bi (fuel + 1) cond body = (do
      let rc ← denote bi (fuel + 1) cond
      match rc with
      | .val (.bool true) => do
          let rb ← denote bi (fuel + 1) body
          match rb with
          | .val _ | .continued =>
              denoteWhile bi fuel cond body
          | .broke v => pure (.val v)
          | other => pure other
      | .val (.bool false) => pure (.val .unit)
      | .val _ => pure (.err "while condition not a bool")
      | other => pure other) := by
    conv_lhs => unfold denoteWhile
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rfl
  show (denoteWhile bi (fuel + 1) cond body).run env = _
  rw [hWhile]
  simp only [StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  cases denote bi (fuel + 1) cond env with
  | mk a s =>
    rcases a with v | v | v | _ | msg
    · -- val v: case on whether v is bool
      rcases v with b | _ | _ | _ | _ | _ | _
      · -- bool b
        rcases b
        · rfl
        · -- true: peel off StateT.bind on body
          show StateT.bind (denote bi (fuel + 1) body) _ s = _
          simp only [StateT.bind]
          cases denote bi (fuel + 1) body s with
          | mk a2 s2 =>
            cases a2 <;> rfl
      all_goals rfl
    all_goals rfl

/-- Unfold equation for `.whileLoop`. -/
theorem denote_whileLoop_run_eq (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) (env : Env) :
    (denote bi fuel (.whileLoop cond body)).run env =
      (denoteWhile bi fuel cond body).run env := by
  show (denote bi fuel (.whileLoop cond body)).run env = _
  unfold denote
  rfl

/-- Unfold equation for `.match_`. -/
theorem denote_match_run_eq (bi : Builtins) (fuel : Nat)
    (scrut : ImpExpr) (arms : List (ImpPat × ImpExpr)) (env : Env) :
    (denote bi fuel (.match_ scrut arms)).run env =
      (match (denote bi fuel scrut).run env with
       | (.val v, env_a) => (denoteMatchArms bi fuel v arms).run env_a
       | (other, env_a) => (other, env_a)) := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  cases denote bi fuel scrut env with
  | mk a s => cases a <;> rfl

/-! ## §2  `denoteWhile` outcome dichotomy

A `denoteWhile` invocation on an AnfShaped body produces `.val` or `.err`
(never `.broke`/`.continued`/`.earlyRet`), provided that the body itself
satisfies the dichotomy at every fuel.  This is the bridge to the
whileLoop arm of the main structural induction. -/

/-- If `body` satisfies the outcome dichotomy at every fuel level (its
    direct or weakened form being captured by `hBody`), and `cond` does
    too, then so does `denoteWhile bi fuel cond body`. -/
theorem denoteWhile_outcome_val_or_err (bi : Builtins) (cond body : ImpExpr)
    (hCond : ∀ fuel env,
        (∃ v env', (denote bi fuel cond).run env = (.val v, env'))
      ∨ (∃ msg env', (denote bi fuel cond).run env = (.err msg, env')))
    (hBody : ∀ fuel env,
        (∃ v env', (denote bi fuel body).run env = (.val v, env'))
      ∨ (∃ msg env', (denote bi fuel body).run env = (.err msg, env')))
    (fuel : Nat) (env : Env) :
      (∃ v env', (denoteWhile bi fuel cond body).run env = (.val v, env'))
    ∨ (∃ msg env', (denoteWhile bi fuel cond body).run env = (.err msg, env')) := by
  induction fuel using Nat.strong_induction_on generalizing env with
  | _ fuel ih =>
    match fuel with
    | 0 =>
      right
      refine ⟨"out of fuel", env, ?_⟩
      exact denoteWhile_zero bi cond body env
    | n + 1 =>
      rw [denoteWhile_succ_run]
      rcases hCond (n + 1) env with ⟨vc, env_a, hc⟩ | ⟨msg, env_a, hc⟩
      · rw [hc]
        -- Case on whether vc is .bool true / .bool false / something else
        match vc with
        | .bool true =>
          simp only
          -- iterate body
          rcases hBody (n + 1) env_a with ⟨vb, env_b, hb⟩ | ⟨msg, env_b, hb⟩
          · rw [hb]
            -- recurse on while with fuel n
            exact ih n (Nat.lt_succ_self n) env_b
          · rw [hb]
            right; exact ⟨msg, env_b, rfl⟩
        | .bool false =>
          left; exact ⟨.unit, env_a, rfl⟩
        | .int _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .unit =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .tuple _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .option _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .result _ _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .controlFlow _ _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .uint _ _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .sint _ _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
        | .array _ =>
          right; exact ⟨"while condition not a bool", env_a, rfl⟩
      · rw [hc]
        right; exact ⟨msg, env_a, rfl⟩

/-! ## §3  `denoteMatchArms` outcome dichotomy for AnfShaped 2-tuple pattern -/

open _root_.Hax (matchPat) in
/-- The denotation of `denoteMatchArms` on the single-arm 2-tuple destructure
    pattern admitted by `AnfShaped`.  Either the body fires (after binding the
    two variables) or the no-matching-pattern error is returned. -/
theorem denoteMatchArms_tuple2_outcome (bi : Builtins) (fuel : Nat)
    (v : Value) (n1 n2 : String) (body : ImpExpr) (env : Env)
    (hBody : ∀ env',
        (∃ vb env'', (denote bi fuel body).run env' = (.val vb, env''))
      ∨ (∃ msg env'', (denote bi fuel body).run env' = (.err msg, env''))) :
      (∃ vb env',
          (denoteMatchArms bi fuel v
              [(.tuplePat [.varPat n1, .varPat n2], body)]).run env
            = (.val vb, env'))
    ∨ (∃ msg env',
          (denoteMatchArms bi fuel v
              [(.tuplePat [.varPat n1, .varPat n2], body)]).run env
            = (.err msg, env')) := by
  -- Unfold the match-arm machinery for the single 2-tuple arm.
  cases hMatch : matchPat (.tuplePat [.varPat n1, .varPat n2]) v env with
  | none =>
    -- pattern doesn't bind; cascade to empty arms which give .err.
    right
    refine ⟨"no matching pattern", env, ?_⟩
    show (denoteMatchArms bi fuel v _).run env = _
    unfold denoteMatchArms
    simp only [StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
               MonadStateOf.get, StateT.get,
               pure, Pure.pure, hMatch]
    -- Now goal: denoteMatchArms bi fuel v [] env = (.err _, env)
    show denoteMatchArms bi fuel v [] env = _
    unfold denoteMatchArms
    rfl
  | some env' =>
    -- pattern binds; run body in extended env'.
    rcases hBody env' with ⟨vb, env'', hb⟩ | ⟨msg, env'', hb⟩
    · left
      refine ⟨vb, env'', ?_⟩
      show (denoteMatchArms bi fuel v _).run env = _
      unfold denoteMatchArms
      simp only [StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
                 MonadStateOf.get, StateT.get, set, MonadStateOf.set,
                 StateT.set, pure, Pure.pure, hMatch]
      exact hb
    · right
      refine ⟨msg, env'', ?_⟩
      show (denoteMatchArms bi fuel v _).run env = _
      unfold denoteMatchArms
      simp only [StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
                 MonadStateOf.get, StateT.get, set, MonadStateOf.set,
                 StateT.set, pure, Pure.pure, hMatch]
      exact hb

/-! ## §3b  `denoteMatchArms` on the AnfShaped 2-arm pattern, full helper -/

/-- For the specific AnfShaped match pattern (one tuple-of-vars arm), the
    composed denotation produces `.val` or `.err`. This is the form we use
    in the main induction's `match_` arm. -/
theorem AnfShaped_match_outcome
    (bi : Builtins) (fuel : Nat) (f : String) (args : List ImpExpr)
    (n1 n2 : String) (body : ImpExpr) (env : Env)
    (hbody_dichotomy : ∀ env',
        (∃ vb env'', (denote bi fuel body).run env' = (.val vb, env''))
      ∨ (∃ msg env'', (denote bi fuel body).run env' = (.err msg, env''))) :
      (∃ v env',
          (denote bi fuel (.match_ (.app f args)
            [(.tuplePat [.varPat n1, .varPat n2], body)])).run env
          = (.val v, env'))
    ∨ (∃ msg env',
          (denote bi fuel (.match_ (.app f args)
            [(.tuplePat [.varPat n1, .varPat n2], body)])).run env
          = (.err msg, env')) := by
  rw [denote_match_run_eq]
  rcases denote_app_outcome bi fuel f args env with
      ⟨vapp, env_a, ha⟩ | ⟨msg, env_a, ha⟩
  · rw [ha]; simp only
    exact denoteMatchArms_tuple2_outcome bi fuel vapp n1 n2 body env_a hbody_dichotomy
  · rw [ha]; right; exact ⟨msg, env_a, rfl⟩

/-! ## §4  Main combined dichotomy

`AnfShaped` programs never produce `.broke`, `.continued`, or `.earlyRet`
under `denote`; only `.val _` or `.err _`. -/

open _root_.Hax (Value.ofLit) in
/-- Combined outcome dichotomy for `AnfShaped` expressions. -/
theorem AnfShaped_outcome_val_or_err
    (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env)
    (h : AnfShaped e = true) :
      (∃ v env', (denote bi fuel e).run env = (.val v, env'))
    ∨ (∃ msg env', (denote bi fuel e).run env = (.err msg, env')) := by
  induction e using ImpExpr.ind generalizing fuel env with
  | lit v =>
    -- Bare `.lit` at toplevel is rejected by AnfShaped (only allowed inside
    -- letBind / assign positions).
    cases v <;> (unfold AnfShaped at h; simp at h)
  | var n =>
    exact denote_var_outcome bi fuel n env
  | letBind n val body _ihval ihbody =>
    rw [denote_letBind_run_eq]
    -- Productive shapes admitted by AnfShaped:
    -- (.lit (.uintLit _ _)), (.lit (.int n)) with n ≥ 0, or (.app f args).
    cases val with
    | lit l =>
      cases l with
      | int k =>
        have hbody_anf : AnfShaped body = true := by
          unfold AnfShaped at h
          by_cases hk : k ≥ 0
          · simp [hk] at h; exact h
          · simp [hk] at h
        rw [denote_lit_eq bi fuel (.int k) env]
        exact ihbody fuel (env.extend n (Value.ofLit (.int k))) hbody_anf
      | uintLit w m =>
        have hbody_anf : AnfShaped body = true := by
          unfold AnfShaped at h; exact h
        rw [denote_lit_eq bi fuel (.uintLit w m) env]
        exact ihbody fuel (env.extend n (Value.ofLit (.uintLit w m))) hbody_anf
      | bool b =>
        have hbody_anf : AnfShaped body = true := by
          unfold AnfShaped at h; exact h
        rw [denote_lit_eq bi fuel (.bool b) env]
        exact ihbody fuel (env.extend n (Value.ofLit (.bool b))) hbody_anf
      | unit | sintLit _ _ =>
        unfold AnfShaped at h; simp at h
    | app f args =>
      have hbody_anf : AnfShaped body = true := by
        unfold AnfShaped at h; simp at h; exact h.2
      rcases denote_app_outcome bi fuel f args env with
          ⟨vapp, env_a, ha⟩ | ⟨msg, env_a, ha⟩
      · rw [ha]; exact ihbody fuel (env_a.extend n vapp) hbody_anf
      · rw [ha]; right; exact ⟨msg, env_a, rfl⟩
    | var src =>
      -- Parameter-alias `let _ = .var src; body`: AnfShaped recurses into body.
      have hbody_anf : AnfShaped body = true := by
        unfold AnfShaped at h; exact h
      rcases denote_var_outcome bi fuel src env with
          ⟨vsrc, env_a, hv⟩ | ⟨msg, env_a, hv⟩
      · rw [hv]; exact ihbody fuel (env_a.extend n vsrc) hbody_anf
      · rw [hv]; right; exact ⟨msg, env_a, rfl⟩
    | proj pe i =>
      -- Tuple-component read `let _ = (.var t).i; body`: the rhs
      -- denotation is a pure env lookup + projection (val or err),
      -- then the body's dichotomy applies in the extended env.
      cases pe with
      | var t =>
        have hbody_anf : AnfShaped body = true := by
          unfold AnfShaped at h; exact h
        cases hEnvT : env t with
        | none =>
          rw [denote_proj_var_run_err_of_env_none bi fuel t i env hEnvT]
          right; exact ⟨_, env, rfl⟩
        | some vTup =>
          cases hProj : vTup.projIdx i with
          | none =>
            rw [denote_proj_var_run_err_of_proj_none bi fuel t i env vTup
                  hEnvT hProj]
            right; exact ⟨_, env, rfl⟩
          | some vi =>
            rw [denote_proj_var_run_some bi fuel t i env vTup vi hEnvT hProj]
            exact ihbody fuel (env.extend n vi) hbody_anf
      | _ => unfold AnfShaped at h; simp at h
    | _ => unfold AnfShaped at h; simp at h
  | app f args _ihs =>
    exact denote_app_outcome bi fuel f args env
  | lam _ _ _ih => unfold AnfShaped at h; simp at h
  | tuple elems _ihs =>
    -- The tuple denotation is a total match on `denoteArgs`: it yields
    -- `.val (.tuple vals)` on success and the non-value error otherwise,
    -- so the dichotomy holds for every tuple (AnfShaped restricts to
    -- all-`var` components, but the dichotomy needs no restriction).
    rw [denote_tuple_run_eq]
    cases hDA : (denoteArgs bi fuel elems).run env with
    | mk mvals env_a =>
      cases mvals with
      | some vals => left; exact ⟨.tuple vals, env_a, rfl⟩
      | none => right; exact ⟨"non-value in tuple elements", env_a, rfl⟩
  | proj _ _ _ih => unfold AnfShaped at h; simp at h
  | ifThenElse c t e _ihc iht ihe =>
    cases c with
    | var name =>
      rw [denote_ifThenElse_run_eq]
      have ht_anf : AnfShaped t = true := by
        unfold AnfShaped at h; simp at h; exact h.1
      have he_anf : AnfShaped e = true := by
        unfold AnfShaped at h; simp at h; exact h.2
      rcases denote_var_outcome bi fuel name env with ⟨vc, env_a, hc⟩ | ⟨msg, env_a, hc⟩
      · rw [hc]
        match vc with
        | .bool true => simp only; exact iht fuel env_a ht_anf
        | .bool false => simp only; exact ihe fuel env_a he_anf
        | .int _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .unit => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .tuple _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .option _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .result _ _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .controlFlow _ _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .uint _ _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .sint _ _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
        | .array _ => right; exact ⟨"if condition not a bool", env_a, rfl⟩
      · rw [hc]
        right; exact ⟨msg, env_a, rfl⟩
    | _ => unfold AnfShaped at h; simp at h
  | match_ scrut arms _ihscrut iharms =>
    -- AnfShaped admits exactly:
    --   scrut = .app f args,
    --   arms = [(.tuplePat [.varPat n1, .varPat n2], body)],
    --   args.all isVar, AnfShaped body.
    -- All other shapes fall through to the catch-all `_ => false`.
    cases scrut
    case' app f args =>
      cases arms
      case' cons hd tl =>
        obtain ⟨pat, body⟩ := hd
        cases tl
        case' nil =>
          cases pat
          case' tuplePat pats =>
            cases pats
            case' cons p1 ps1 =>
              cases p1
              case' varPat n1 =>
                cases ps1
                case' cons p2 ps2 =>
                  cases p2
                  case' varPat n2 =>
                    cases ps2
                    case' nil =>
                      have hbody_anf : AnfShaped body = true := by
                        unfold AnfShaped at h; simp at h; exact h.2
                      have hbody_dichotomy : ∀ env',
                          (∃ vb env'', (denote bi fuel body).run env' = (.val vb, env''))
                        ∨ (∃ msg env'', (denote bi fuel body).run env' = (.err msg, env'')) :=
                        fun env' =>
                          iharms ⟨.tuplePat [.varPat n1, .varPat n2], body⟩
                            (by simp) fuel env' hbody_anf
                      exact AnfShaped_match_outcome bi fuel f args n1 n2 body env hbody_dichotomy
    all_goals (unfold AnfShaped at h; simp at h)
  | unitVal =>
    left; refine ⟨.unit, env, ?_⟩
    exact denote_unitVal_eq bi fuel env
  | seq e1 e2 ih1 ih2 =>
    rw [denote_seq_run_eq]
    have h1 : AnfShaped e1 = true := by
      unfold AnfShaped at h; simp at h; exact h.1
    have h2 : AnfShaped e2 = true := by
      unfold AnfShaped at h; simp at h; exact h.2
    rcases ih1 fuel env h1 with ⟨v1, env_a, hv1⟩ | ⟨msg, env_a, hv1⟩
    · rw [hv1]; exact ih2 fuel env_a h2
    · rw [hv1]; right; exact ⟨msg, env_a, rfl⟩
  | borrow _ _ih => unfold AnfShaped at h; simp at h
  | deref _ _ih => unfold AnfShaped at h; simp at h
  | assign n rhs _ihrhs =>
    rw [denote_assign_run_eq]
    cases rhs with
    | lit l =>
      cases l with
      | int k =>
        rw [denote_lit_eq bi fuel (.int k) env]
        left; exact ⟨.unit, env.extend n (Value.ofLit (.int k)), rfl⟩
      | uintLit w m =>
        rw [denote_lit_eq bi fuel (.uintLit w m) env]
        left; exact ⟨.unit, env.extend n (Value.ofLit (.uintLit w m)), rfl⟩
      | bool b =>
        rw [denote_lit_eq bi fuel (.bool b) env]
        left; exact ⟨.unit, env.extend n (Value.ofLit (.bool b)), rfl⟩
      | unit | sintLit _ _ =>
        unfold AnfShaped at h; simp at h
    | app f args =>
      rcases denote_app_outcome bi fuel f args env with
          ⟨v, env_a, hv⟩ | ⟨msg, env_a, hv⟩
      · rw [hv]
        left; exact ⟨.unit, env_a.extend n v, rfl⟩
      · rw [hv]; right; exact ⟨msg, env_a, rfl⟩
    | _ => unfold AnfShaped at h; simp at h
  | forLoop _ _ _ _ _ _ _ => unfold AnfShaped at h; simp at h
  | forLoopRev _ _ _ _ _ _ _ => unfold AnfShaped at h; simp at h
  | whileLoop c body _ihc ihbody =>
    cases c with
    | var name =>
      rw [denote_whileLoop_run_eq]
      have hbody_anf : AnfShaped body = true := by
        unfold AnfShaped at h; exact h
      refine denoteWhile_outcome_val_or_err bi (.var name) body
        (fun f e => denote_var_outcome bi f name e)
        (fun f e => ihbody f e hbody_anf) fuel env
    | _ => unfold AnfShaped at h; simp at h
  | break_none => unfold AnfShaped at h; simp at h
  | break_some _ _ih => unfold AnfShaped at h; simp at h
  | continue_ => unfold AnfShaped at h; simp at h
  | earlyReturn _ _ih => unfold AnfShaped at h; simp at h
  | questionMark _ _ih => unfold AnfShaped at h; simp at h
  | forFold _ lo hi body _ _ ihbody =>
      -- `AnfShaped` admits the literal- and convertible-runtime-bounded
      -- `.forFold` shapes (zero- and offset-start).  Independently of the
      -- shape, `.forFold` is a post-phase constructor whose ImpExpr
      -- `denote` returns `pure (.err _)` (see `HaxLean/Semantics.lean`),
      -- so the outcome dichotomy is discharged uniformly on the err side —
      -- no case split on `lo`/`hi` is needed.
      right
      refine ⟨"forFold in pre-pipeline expression", env, ?_⟩
      unfold denote; rfl
  | typeAscription e _ ih =>
    unfold AnfShaped at h
    rcases ih fuel env h with ⟨v, env', hv⟩ | ⟨msg, env', hm⟩
    · exact Or.inl ⟨v, env', by unfold denote; exact hv⟩
    · exact Or.inr ⟨msg, env', by unfold denote; exact hm⟩
  | forFoldRev _ _ _ _ _ _ _ =>
      -- A post-phase constructor: `denote` returns `pure (.err _)` whatever
      -- the shape.
      right
      refine ⟨"forFoldRev in pre-pipeline expression", env, ?_⟩
      unfold denote; rfl
  | whileFold _ _ _ _ =>
      right
      refine ⟨"whileFold in pre-pipeline expression", env, ?_⟩
      unfold denote; rfl
  | forFoldReturn _ _ _ _ _ _ _ => unfold AnfShaped at h; simp at h
  | forFoldRevReturn _ _ _ _ _ _ _ => unfold AnfShaped at h; simp at h
  | whileFoldReturn _ _ _ _ => unfold AnfShaped at h; simp at h
  | cfBreak _ _ih => unfold AnfShaped at h; simp at h
  | cfContinue _ _ih => unfold AnfShaped at h; simp at h
  | cfBreakContinue _ _ih => unfold AnfShaped at h; simp at h

/-! ## §5  The whileLoop body-always-val helper

The specific shape required by the whileLoop simulation: if a body is
AnfShaped (so by §4 only produces `.val`/`.err`) and the simulation
context rules out the `.err` branch (via `hNoErr`), then every
evaluation lands on `.val`. -/

/-- If `body` is AnfShaped and provably never errors in this context, then
    every `denote bi f body` from any env produces a `.val` outcome. -/
theorem hBodyAlwaysVal_of_AnfShaped
    (bi : Builtins) (body : ImpExpr) (h : AnfShaped body = true)
    (hNoErr : ∀ f env msg env', (denote bi f body).run env ≠ (.err msg, env')) :
    ∀ f env_a, ∃ vB env_b, (denote bi f body).run env_a = (.val vB, env_b) := by
  intro f env_a
  rcases AnfShaped_outcome_val_or_err bi f body env_a h with
      ⟨v, env', hv⟩ | ⟨msg, env', he⟩
  · exact ⟨v, env', hv⟩
  · exact absurd he (hNoErr f env_a msg env')

/-! ## §6  Counted loops

Unfold equations for `denoteForLoop` separated by the bound test and the fuel,
and the outcome dichotomy for `denoteForLoop` and `.forLoop`. -/

/-- A counted loop whose start is not below its bound runs no trip. -/
theorem denoteForLoop_ge_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : hi ≤ lo) :
    (denoteForLoop bi fuel v lo hi body).run env = (.val .unit, env) := by
  show (denoteForLoop bi fuel v lo hi body).run env = _
  unfold denoteForLoop
  simp [h, StateT.run, pure, Pure.pure, StateT.pure]

/-- A counted loop with a trip left fails at zero fuel. -/
theorem denoteForLoop_zero_run (bi : Builtins) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    (denoteForLoop bi 0 v lo hi body).run env = (.err "out of fuel", env) := by
  show (denoteForLoop bi 0 v lo hi body).run env = _
  unfold denoteForLoop
  simp [show ¬ hi ≤ lo by omega, StateT.run, pure, Pure.pure, StateT.pure]

/-- One trip of a counted loop at successor fuel: the body runs at the same fuel
    with the counter bound to the start, and the loop continues from the next
    start at the predecessor fuel. -/
theorem denoteForLoop_succ_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    (denoteForLoop bi (fuel + 1) v lo hi body).run env =
      (match (denote bi (fuel + 1) body).run (env.extend v (.int lo)) with
       | (.val _, env_b) => (denoteForLoop bi fuel v (lo + 1) hi body).run env_b
       | (.continued, env_b) => (denoteForLoop bi fuel v (lo + 1) hi body).run env_b
       | (.broke w, env_b) => (.val w, env_b)
       | (other, env_b) => (other, env_b)) := by
  have hFor : denoteForLoop bi (fuel + 1) v lo hi body = (do
      modify (Env.extend · v (.int lo))
      let rb ← denote bi (fuel + 1) body
      match rb with
      | .val _ | .continued => denoteForLoop bi fuel v (lo + 1) hi body
      | .broke w => pure (.val w)
      | other => pure other) := by
    conv_lhs => unfold denoteForLoop
    simp only [show ¬ lo ≥ hi by omega, if_false, Nat.succ_ne_zero, Nat.add_sub_cancel]
    rfl
  show (denoteForLoop bi (fuel + 1) v lo hi body).run env = _
  rw [hFor]
  simp only [StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet]
  cases denote bi (fuel + 1) body (env.extend v (.int lo)) with
  | mk a s => cases a <;> rfl

/-- Unfold equation for `.forLoop` with integer literal bounds. -/
theorem denote_forLoop_lit_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) :
    (denote bi fuel (.forLoop v (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (denoteForLoop bi fuel v lo hi body).run env := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure,
    Value.ofLit]

/-- A counted loop whose body runs to a value or an error at every fuel runs to
    a value or an error. -/
theorem denoteForLoop_val_or_err (bi : Builtins) (v : String) (body : ImpExpr)
    (hBody : ∀ fuel env,
        (∃ w env', (denote bi fuel body).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel body).run env = (.err msg, env'))) :
    ∀ (fuel : Nat) (lo hi : Int) (env : Env),
        (∃ w env', (denoteForLoop bi fuel v lo hi body).run env = (.val w, env'))
      ∨ (∃ msg env', (denoteForLoop bi fuel v lo hi body).run env = (.err msg, env')) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env
    by_cases h : hi ≤ lo
    · exact Or.inl ⟨_, _, denoteForLoop_ge_run bi 0 v lo hi body env h⟩
    · exact Or.inr ⟨_, _, denoteForLoop_zero_run bi v lo hi body env (by omega)⟩
  | succ m ih =>
    intro lo hi env
    by_cases h : hi ≤ lo
    · exact Or.inl ⟨_, _, denoteForLoop_ge_run bi _ v lo hi body env h⟩
    rw [denoteForLoop_succ_run bi m v lo hi body env (by omega)]
    rcases hBody (m + 1) (env.extend v (.int lo)) with ⟨w, e1, hb⟩ | ⟨msg, e1, hb⟩
    · rw [hb]; exact ih (lo + 1) hi e1
    · rw [hb]; exact Or.inr ⟨msg, e1, rfl⟩

/-- `.forLoop` whose bounds and body run to a value or an error runs to a value
    or an error. -/
theorem denote_forLoop_val_or_err (bi : Builtins) (fuel : Nat) (v : String)
    (lo hi body : ImpExpr) (env : Env)
    (hlo : ∀ env,
        (∃ w env', (denote bi fuel lo).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel lo).run env = (.err msg, env')))
    (hhi : ∀ env,
        (∃ w env', (denote bi fuel hi).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel hi).run env = (.err msg, env')))
    (hBody : ∀ fuel env,
        (∃ w env', (denote bi fuel body).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel body).run env = (.err msg, env'))) :
    (∃ w env', (denote bi fuel (.forLoop v lo hi body)).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel (.forLoop v lo hi body)).run env = (.err msg, env')) := by
  have hL := denoteForLoop_val_or_err bi v body hBody fuel
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  rcases hlo env with ⟨a, e1, ha⟩ | ⟨m, e1, ha⟩ <;> simp only [StateT.run] at ha <;>
    simp only [ha]
  · simp only [StateT.bind]
    rcases hhi e1 with ⟨b, e2, hb⟩ | ⟨m', e2, hb⟩ <;> simp only [StateT.run] at hb <;>
      simp only [hb]
    · cases a <;> cases b <;>
        first | exact Or.inr ⟨_, _, rfl⟩ | exact Or.inl ⟨_, _, rfl⟩ | exact hL _ _ _
    · cases a <;> exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩

/-! ## §7  Reverse counted loops

Unfold equations for `denoteForLoopRev` separated by the bound test and the
fuel, the unfold equation of `.forLoop` at a variable bound, and the outcome
dichotomy for `denoteForLoopRev` and `.forLoopRev`. -/

/-- A reverse counted loop whose start is not below its bound runs no trip. -/
theorem denoteForLoopRev_ge_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : hi ≤ lo) :
    (denoteForLoopRev bi fuel v lo hi body).run env = (.val .unit, env) := by
  show (denoteForLoopRev bi fuel v lo hi body).run env = _
  unfold denoteForLoopRev
  simp [h, StateT.run, pure, Pure.pure, StateT.pure]

/-- A reverse counted loop with a trip left fails at zero fuel. -/
theorem denoteForLoopRev_zero_run (bi : Builtins) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    (denoteForLoopRev bi 0 v lo hi body).run env = (.err "out of fuel", env) := by
  show (denoteForLoopRev bi 0 v lo hi body).run env = _
  unfold denoteForLoopRev
  simp [show ¬ hi ≤ lo by omega, StateT.run, pure, Pure.pure, StateT.pure]

/-- One trip of a reverse counted loop at successor fuel: the body runs at the
    same fuel with the counter bound to the bound less one, and the loop
    continues with that bound at the predecessor fuel. -/
theorem denoteForLoopRev_succ_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    (denoteForLoopRev bi (fuel + 1) v lo hi body).run env =
      (match (denote bi (fuel + 1) body).run (env.extend v (.int (hi - 1))) with
       | (.val _, env_b) => (denoteForLoopRev bi fuel v lo (hi - 1) body).run env_b
       | (.continued, env_b) => (denoteForLoopRev bi fuel v lo (hi - 1) body).run env_b
       | (.broke w, env_b) => (.val w, env_b)
       | (other, env_b) => (other, env_b)) := by
  have hFor : denoteForLoopRev bi (fuel + 1) v lo hi body = (do
      modify (Env.extend · v (.int (hi - 1)))
      let rb ← denote bi (fuel + 1) body
      match rb with
      | .val _ | .continued => denoteForLoopRev bi fuel v lo (hi - 1) body
      | .broke w => pure (.val w)
      | other => pure other) := by
    conv_lhs => unfold denoteForLoopRev
    simp only [show ¬ lo ≥ hi by omega, if_false, Nat.succ_ne_zero, Nat.add_sub_cancel]
    rfl
  show (denoteForLoopRev bi (fuel + 1) v lo hi body).run env = _
  rw [hFor]
  simp only [StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet]
  cases denote bi (fuel + 1) body (env.extend v (.int (hi - 1))) with
  | mk a s => cases a <;> rfl

/-- Unfold equation for `.forLoopRev` with integer literal bounds. -/
theorem denote_forLoopRev_lit_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) :
    (denote bi fuel (.forLoopRev v (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (denoteForLoopRev bi fuel v lo hi body).run env := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure,
    Value.ofLit]

/-- Unfold equation for `.forLoop` from an integer literal to a variable bound
    holding an integer. -/
theorem denote_forLoop_lit_var_run (bi : Builtins) (fuel : Nat) (v : String) (lo : Int)
    (n : String) (k : Int) (body : ImpExpr) (env : Env) (hk : env n = some (.int k)) :
    (denote bi fuel (.forLoop v (.lit (.int lo)) (.var n) body)).run env =
      (denoteForLoop bi fuel v lo k body).run env := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure,
    Value.ofLit, get, getThe, MonadStateOf.get, StateT.get, hk]

/-- Unfold equation for `.forLoop` from an integer literal to a variable bound
    holding the unsigned word `m`: the loop runs up to the integer `m`. -/
theorem denote_forLoop_lit_var_uint_run (bi : Builtins) (fuel : Nat) (v : String) (lo : Int)
    (n : String) (wd : _root_.Hax.IntWidth) (m : Nat) (body : ImpExpr) (env : Env)
    (hm : env n = some (.uint wd m)) :
    (denote bi fuel (.forLoop v (.lit (.int lo)) (.var n) body)).run env =
      (denoteForLoop bi fuel v lo m body).run env := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure,
    Value.ofLit, get, getThe, MonadStateOf.get, StateT.get, hm]

/-- A reverse counted loop whose body runs to a value or an error at every fuel
    runs to a value or an error. -/
theorem denoteForLoopRev_val_or_err (bi : Builtins) (v : String) (body : ImpExpr)
    (hBody : ∀ fuel env,
        (∃ w env', (denote bi fuel body).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel body).run env = (.err msg, env'))) :
    ∀ (fuel : Nat) (lo hi : Int) (env : Env),
        (∃ w env', (denoteForLoopRev bi fuel v lo hi body).run env = (.val w, env'))
      ∨ (∃ msg env', (denoteForLoopRev bi fuel v lo hi body).run env = (.err msg, env')) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env
    by_cases h : hi ≤ lo
    · exact Or.inl ⟨_, _, denoteForLoopRev_ge_run bi 0 v lo hi body env h⟩
    · exact Or.inr ⟨_, _, denoteForLoopRev_zero_run bi v lo hi body env (by omega)⟩
  | succ m ih =>
    intro lo hi env
    by_cases h : hi ≤ lo
    · exact Or.inl ⟨_, _, denoteForLoopRev_ge_run bi _ v lo hi body env h⟩
    rw [denoteForLoopRev_succ_run bi m v lo hi body env (by omega)]
    rcases hBody (m + 1) (env.extend v (.int (hi - 1))) with ⟨w, e1, hb⟩ | ⟨msg, e1, hb⟩
    · rw [hb]; exact ih lo (hi - 1) e1
    · rw [hb]; exact Or.inr ⟨msg, e1, rfl⟩

/-- `.forLoopRev` whose bounds and body run to a value or an error runs to a
    value or an error. -/
theorem denote_forLoopRev_val_or_err (bi : Builtins) (fuel : Nat) (v : String)
    (lo hi body : ImpExpr) (env : Env)
    (hlo : ∀ env,
        (∃ w env', (denote bi fuel lo).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel lo).run env = (.err msg, env')))
    (hhi : ∀ env,
        (∃ w env', (denote bi fuel hi).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel hi).run env = (.err msg, env')))
    (hBody : ∀ fuel env,
        (∃ w env', (denote bi fuel body).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel body).run env = (.err msg, env'))) :
    (∃ w env', (denote bi fuel (.forLoopRev v lo hi body)).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel (.forLoopRev v lo hi body)).run env = (.err msg, env')) := by
  have hL := denoteForLoopRev_val_or_err bi v body hBody fuel
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  rcases hlo env with ⟨a, e1, ha⟩ | ⟨m, e1, ha⟩ <;> simp only [StateT.run] at ha <;>
    simp only [ha]
  · simp only [StateT.bind]
    rcases hhi e1 with ⟨b, e2, hb⟩ | ⟨m', e2, hb⟩ <;> simp only [StateT.run] at hb <;>
      simp only [hb]
    · cases a <;> cases b <;>
        first | exact Or.inr ⟨_, _, rfl⟩ | exact Or.inl ⟨_, _, rfl⟩ | exact hL _ _ _
    · cases a <;> exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩

end CatCrypt.Crypto.Hax
