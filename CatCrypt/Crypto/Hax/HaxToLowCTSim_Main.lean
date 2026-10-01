/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Agreement
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_AssignMatch
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Call
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_If
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_While

/-!
# Assembly of the Hax → LowCT simulation theorem

Wires together the per-case lemmas from `HaxToLowCTSim_*.lean` into
the main theorem.  Dispatches via `ImpExpr.ind` (the custom induction
principle for nested-inductive `ImpExpr` in hax-lean's
`HaxLean/AST.lean`).

## Architecture

The proof is a structural induction on `ImpExpr` via `ImpExpr.ind`.
Each constructor case dispatches to its per-file lemma:

| Constructor | Closure | Source file |
|---|---|---|
| `var _` | `haxToLowCT_simulates_var` | `HaxToLowCTSimulates.lean` |
| `unitVal` | `haxToLowCT_simulates_unitVal` | `HaxToLowCTSimulates.lean` |
| `seq a b` | `haxToLowCT_simulates_seq` | `HaxToLowCTSimulates.lean` |
| `letBind _ (lit _) _` | `haxToLowCT_simulates_letBind_lit` | `HaxToLowCTSim_Agreement.lean` |
| `letBind _ (app _ _) _` | **DEFERRED** (tower-typed) | parametric hyp `Hyp_letBindApp` |
| `letBind _ (proj (var _) _) _` | parametric hyp `Hyp_letBindProj` | closure in `Main_Full` |
| `letBind _ (var _) _` | `haxToLowCT_simulates_letBind_var` | this file |
| `letBind _ _ _` (other) | contradiction | inline `simp [haxToLowCT]` |
| `assign _ (lit (uintLit ..))` | `haxToLowCT_simulates_assign_lit_uintLit` | `HaxToLowCTSim_AssignMatch.lean` |
| `assign _ (lit (int n))`, n≥0 | `haxToLowCT_simulates_assign_lit_int` | `HaxToLowCTSim_AssignMatch.lean` |
| `assign _ (lit (bool _))` | `haxToLowCT_simulates_assign_lit_bool` | `HaxToLowCTSim_AssignMatch.lean` |
| `tuple es` (all `var`s → `RSkip`) | `haxToLowCT_simulates_tuple` | `HaxToLowCTSimulates.lean` |
| `assign _ (app _ _)` | **DEFERRED** (tower-typed) | parametric hyp `Hyp_assignApp` |
| `assign _ _` (other) | contradiction | inline |
| `ifThenElse (var _) _ _` | `haxToLowCT_simulates_ifThenElse_var` | `HaxToLowCTSim_If.lean` |
| `ifThenElse _ _ _` (other) | contradiction | inline |
| `whileLoop (var _) _` | `haxToLowCT_simulates_whileLoop_var` | `HaxToLowCTSim_While.lean` |
| `whileLoop _ _` (other) | contradiction | inline |
| `match_ (app _ _) [(tuplePat [varPat _, varPat _], _)]` | **DEFERRED** (tower-typed) | parametric hyp `Hyp_matchTuple` |
| `match_ _ _` (other) | contradiction | inline |
| All other rejected arms | `haxToLowCT_simulates_*` | `HaxToLowCTSimulates.lean` |

## Parametric form vs full theorem

`haxToLowCT_simulates_param` is the parametric main theorem, taking
the deferred-case hypotheses (`Hyp_letBindApp`, `Hyp_assignApp`,
`Hyp_match`, `Hyp_whileLoop`, `Hyp_letBindProj`) as inputs; it contains
the full dispatch, with the variable binding closed by
`haxToLowCT_simulates_letBind_var`.  This module states no
unconditional form: discharging the hypotheses needs tower-typed
`envAgreesRust` and `LeafCallAgrees` instances, which
`HaxToLowCTSim_Main_Full.lean` and the `HaxToLowCTSim_Quarta*` modules
develop.

## Why the tower-typed cases are hypotheses

The deferred cases share a root cause: `RustExec.call` updates the
*tower* slot via `locatedUpdate`, not the *scalar* slot.  The
`envAgreesRust` predicate covers only scalar bindings.

Discharging the `Hyp_*` parameters takes three steps:

* Extend `envAgreesRust` to cover tower bindings (a byte-layout
  transport in the style of `bindingOK`).
* Add `valueToTowerVal : Value → (dt : TowerType) → Option (RustVal dt)`.
* Provide per-leaf `LeafCallAgrees` instances grounded in the
  extracted leaf-call semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Deferred-case hypotheses

These three hypotheses parameterise the main theorem over the arms
that need tower-typed agreement. -/

/-- Hypothesis: `letBind name (app f args) body` simulates.  Its
    discharge needs tower-typed agreement and per-leaf
    `LeafCallAgrees` instances. -/
abbrev Hyp_letBindApp
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (f : String) (args : List ImpExpr) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.letBind name (.app f args) body) c env env' rs v

/-- Hypothesis: `assign name (app f args)` simulates.  Its discharge
    needs the same tower-typed agreement. -/
abbrev Hyp_assignApp
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (f : String) (args : List ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.assign name (.app f args)) c env env' rs v

/-- Hypothesis: `match_` 2-tuple destructure of an `app` simulates.
    Its discharge needs the tuple-destructure lowering and tower-typed
    agreement. -/
abbrev Hyp_matchTuple
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (f : String) (args : List ImpExpr) (n1 n2 : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.match_ (.app f args) [(.tuplePat [.varPat n1, .varPat n2], body)])
      c env env' rs v

/-! ## §2  Outline of the dispatch

An outline of the dispatch via `ImpExpr.ind`, over the three hypotheses
of §1.  It is not elaborated; the proved theorem in §4 follows this
structure, with `Hyp_match`, `Hyp_whileLoop` and `Hyp_letBindProj` in
place of `Hyp_matchTuple`.

```
theorem haxToLowCT_simulates_param
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hLetBindApp : Hyp_letBindApp bi fuel N leafSpec)
    (hAssignApp : Hyp_assignApp bi fuel N leafSpec)
    (hMatchTuple : Hyp_matchTuple bi fuel N leafSpec)
    (e : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec e c env env' rs v := by
  induction e using ImpExpr.ind generalizing c env env' rs v with
  | lit l         => exact haxToLowCT_simulates_lit bi fuel N leafSpec l c env env' rs v
  | var name      => exact haxToLowCT_simulates_var bi fuel N leafSpec name c env env' rs v
  | letBind name val body ihVal ihBody =>
      cases val with
      | lit l         => exact haxToLowCT_simulates_letBind_lit bi fuel N leafSpec name l body c env env' rs v ihBody
      | app f args _  => exact hLetBindApp name f args body c env env' rs v ihBody
      | _             => -- contradiction: haxToLowCT returns none for other RHS shapes
                          intro h _ _; simp [haxToLowCT] at h
  | app f args _  => exact haxToLowCT_simulates_app bi fuel N leafSpec f args c env env' rs v
  | tuple elems _ => exact haxToLowCT_simulates_tuple bi fuel N leafSpec elems c env env' rs v
  | proj e i _    => exact haxToLowCT_simulates_proj bi fuel N leafSpec e i c env env' rs v
  | ifThenElse cond t e ihC ihT ihE =>
      cases cond with
      | var v_cond  => exact haxToLowCT_simulates_ifThenElse_var bi fuel N leafSpec v_cond t e c env env' rs v ihT ihE
      | _           => intro h _ _; simp [haxToLowCT] at h
  | match_ scrut arms ihScrut ihArms =>
      cases scrut with
      | app f args  => match arms with
                       | [(.tuplePat [.varPat n1, .varPat n2], body)] =>
                           exact hMatchTuple f args n1 n2 body c env env' rs v (ihArms _ (List.Mem.head _))
                       | _ => intro h _ _; simp [haxToLowCT] at h
      | _           => intro h _ _; simp [haxToLowCT] at h
  | unitVal       => exact haxToLowCT_simulates_unitVal bi fuel N leafSpec c env env' rs v
  | seq e1 e2 ih1 ih2 => exact haxToLowCT_simulates_seq bi fuel N leafSpec e1 e2 c env env' rs v ih1 ih2
  | borrow e _    => exact haxToLowCT_simulates_borrow bi fuel N leafSpec e c env env' rs v
  | deref e _     => exact haxToLowCT_simulates_deref bi fuel N leafSpec e c env env' rs v
  | assign name rhs _ =>
      cases rhs with
      | lit l         => cases l with
                         | uintLit w n => exact haxToLowCT_simulates_assign_lit_uintLit bi fuel N leafSpec name w n c env env' rs v
                         | bool b      => exact haxToLowCT_simulates_assign_lit_bool bi fuel N leafSpec name b c env env' rs v
                         | int n       => -- n≥0 case; for n<0, haxToLowCT returns none
                                          if hn : 0 ≤ n then
                                            exact haxToLowCT_simulates_assign_lit_int bi fuel N leafSpec name n hn c env env' rs v
                                          else
                                            intro h _ _; simp [haxToLowCT, hn] at h
                         | _           => intro h _ _; simp [haxToLowCT] at h
      | app f args _  => exact hAssignApp name f args c env env' rs v
      | _             => intro h _ _; simp [haxToLowCT] at h
  | forLoop v lo hi body _ _ _ =>
      exact haxToLowCT_simulates_forLoop bi fuel N leafSpec v lo hi body c env env' rs v
  | forLoopRev v lo hi body _ _ _ =>
      exact haxToLowCT_simulates_forLoopRev bi fuel N leafSpec v lo hi body c env env' rs v
  | whileLoop cond body ihC ihBody =>
      cases cond with
      | var v_cond  => exact haxToLowCT_simulates_whileLoop_var bi fuel N leafSpec v_cond body c env env' rs v ihBody
      | _           => intro h _ _; simp [haxToLowCT] at h
  | break_none    => exact haxToLowCT_simulates_break bi fuel N leafSpec none c env env' rs v
  | break_some e _ => exact haxToLowCT_simulates_break bi fuel N leafSpec (some e) c env env' rs v
  | continue_     => exact haxToLowCT_simulates_continue bi fuel N leafSpec c env env' rs v
  | earlyReturn e _ => exact haxToLowCT_simulates_earlyReturn bi fuel N leafSpec e c env env' rs v
  | questionMark e _ => exact haxToLowCT_simulates_questionMark bi fuel N leafSpec e c env env' rs v
  | forFold v lo hi body _ _ _ =>
      exact haxToLowCT_simulates_forFold bi fuel N leafSpec v lo hi body c env env' rs v
  | forFoldRev v lo hi body _ _ _ =>
      exact haxToLowCT_simulates_forFoldRev bi fuel N leafSpec v lo hi body c env env' rs v
  | whileFold cond body _ _ =>
      exact haxToLowCT_simulates_whileFold bi fuel N leafSpec cond body c env env' rs v
  | forFoldReturn v lo hi body _ _ _ =>
      exact haxToLowCT_simulates_forFoldReturn bi fuel N leafSpec v lo hi body c env env' rs v
  | forFoldRevReturn v lo hi body _ _ _ =>
      exact haxToLowCT_simulates_forFoldRevReturn bi fuel N leafSpec v lo hi body c env env' rs v
  | whileFoldReturn cond body _ _ =>
      exact haxToLowCT_simulates_whileFoldReturn bi fuel N leafSpec cond body c env env' rs v
  | cfBreak e _ => exact haxToLowCT_simulates_cfBreak bi fuel N leafSpec e c env env' rs v
  | cfContinue e _ => exact haxToLowCT_simulates_cfContinue bi fuel N leafSpec e c env env' rs v
  | cfBreakContinue e _ => exact haxToLowCT_simulates_cfBreakContinue bi fuel N leafSpec e c env env' rs v
```

The elaborated proof differs from this outline in:
* The exact constructor-argument count of `ImpExpr.ind`'s cases (each
  recursive sub-term provides one IH argument).
* The `cases l with | int n => if hn : 0 ≤ n` shape, which the proof
  handles with a `by_cases hn : 0 ≤ n`.
* The `match arms with | ...` inside the `match_` case — only the
  specific 2-tuple shape is accepted; all other shapes contradict.
-/

/-! ## §3  Hypothesis: whileLoop simulation

`haxToLowCT_simulates_whileLoop_var` closes under two
extra hypotheses (`ihBody` fuel-quantified + `hBodyAlwaysVal`).
Discharging those in the dispatcher requires either:
* strengthening the induction motive to be fuel-polymorphic (impacts
  every other case), or
* a separate `AnfShaped → outcome ∈ {.val, .err}` lemma to derive
  `hBodyAlwaysVal` syntactically.

For the parametric dispatcher, we treat the whileLoop closure as a
hypothesis. -/

abbrev Hyp_whileLoop
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (cond : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.whileLoop (.var cond) body) c env env' rs v

/-- Hypothesis: `match_` with any scrutinee/arms simulates.  The broad
    form simplifies the dispatcher; internally, all but the
    tuple-destructure shape contradict via `haxToLowCT` returning
    `none`.  A discharge case-splits on the scrutinee and arm
    shapes. -/
abbrev Hyp_match
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (scrut : ImpExpr) (arms : List (Hax.ImpPat × ImpExpr))
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihScrut : ∀ c' env_a env_b rs_a v_a,
                  HaxToLowCTSimulates bi fuel N leafSpec scrut c' env_a env_b rs_a v_a)
    (_ihArms : ∀ pa ∈ arms,
                  ∀ c' env_a env_b rs_a v_a,
                    HaxToLowCTSimulates bi fuel N leafSpec pa.2 c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec (.match_ scrut arms) c env env' rs v

/-- The simulation statement for `letBind name (.var src) body`, closed by
    `haxToLowCT_simulates_letBind_var`.  The source extends `env` with
    `name ↦ env src`; the lowering is the body's lowering when `name = src`
    and the scalar copy of `src` into `name` otherwise. -/
abbrev Hyp_letBindVarAlias
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name src : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.letBind name (.var src) body) c env env' rs v

/-- Extending the source env at `name` with the value `w` of `src`, and
    setting the scalar slot `name` to the scalar slot `src`, preserves
    scalar agreement. -/
theorem envAgreesRust_extend_copy (env : Env) (rs : RustState) (name src : String)
    (w : Value) (hAgree : envAgreesRust env rs) (hsrc : env src = some w) :
    envAgreesRust (Env.extend env name w) (rsSetScalar rs name (rs.rsScalar src)) := by
  intro m v hv n hn
  by_cases hm : m = name
  · subst hm
    rw [Env.extend_same] at hv
    cases hv
    simpa [rsSetScalar] using hAgree src w hsrc n hn
  · rw [Env.extend_other env name w m hm] at hv
    simpa [rsSetScalar, hm] using hAgree m v hv n hn

/-- **Simulation of a variable binding.**  `letBind name (.var src) body`
    simulates for every `name` and `src`: the self-alias by the body's
    simulation, and `name ≠ src` by the scalar copy of `src` into `name`. -/
theorem haxToLowCT_simulates_letBind_var
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) :
    Hyp_letBindVarAlias bi fuel N leafSpec := by
  intro name src body c env env' rs v ihBody hHax hEval hAgree
  unfold evalImp at hEval
  rw [denote_letBind_run_eq', denote_var_run_eq] at hEval
  cases hsrc : env src with
  | none => simp only [hsrc] at hEval; cases hEval
  | some w =>
    simp only [hsrc] at hEval
    by_cases h : name = src
    · subst h
      rw [haxToLowCT_letBind_var_self] at hHax
      have hself : env.extend name w = env := by
        funext y
        by_cases hy : y = name
        · subst hy; rw [Env.extend_same, hsrc]
        · rw [Env.extend_other env name w y hy]
      rw [hself] at hEval
      exact ihBody c env env' rs v hHax hEval hAgree
    · rw [haxToLowCT_letBind_var_ne name src body h] at hHax
      cases hb : haxToLowCT body with
      | none => simp [hb] at hHax
      | some bodyC =>
        simp only [hb, Option.map_some, Option.some.injEq] at hHax
        subst hHax
        obtain ⟨rs', hExec, hAgree'⟩ := ihBody bodyC (env.extend name w) env'
          (rsSetScalar rs name (rs.rsScalar src)) v hb hEval
          (envAgreesRust_extend_copy env rs name src w hAgree hsrc)
        refine ⟨rs', ?_, hAgree'⟩
        refine RustExec.letU64Zero name _ rs rs' ?_
        refine RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr name _ _) ?_
        have hsv : (CatCrypt.Crypto.Jasmin.LowCT.SExpr.SVar src).evalState
            (rsSetScalar rs name 0) = rs.rsScalar src := by
          simp [CatCrypt.Crypto.Jasmin.LowCT.SExpr.evalState, rsSetScalar, Ne.symm h]
        rw [hsv, rsSetScalar_collapse]
        exact hExec

/-- Hypothesis: `letBind name ((.var t).i) body` (tuple-component read)
    simulates.  The translator lowers this shape to
    `RLetZero name _ (RSeq (RTupleLoad ..) ..)`, whose result lands in a
    *tower* slot — outside the scalar-only agreement this predicate
    threads.  The closure (component value related through the
    `leafSpec.tupleLoad` oracle) is
    `haxToLowCT_simulates_letBind_proj_full` in
    `HaxToLowCTSim_Main_Full.lean`. -/
abbrev Hyp_letBindProj
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name t : String) (i : Nat) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.letBind name (.proj (.var t) i) body) c env env' rs v

/-! ## §4  Parametric main theorem

The main theorem, modulo the five `Hyp_*` hypotheses for deferred
cases.  All other cases (var, unitVal, seq, letBind lit, letBind var,
assign lit (uintLit / int n≥0), ifThenElse var, whileLoop (handled
by hypothesis), all 22 unreachable arms) are closed. -/

theorem haxToLowCT_simulates_param
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hLetBindApp : Hyp_letBindApp bi fuel N leafSpec)
    (hAssignApp : Hyp_assignApp bi fuel N leafSpec)
    (hMatch : Hyp_match bi fuel N leafSpec)
    (hWhileLoop : Hyp_whileLoop bi fuel N leafSpec)
    (hLetBindProj : Hyp_letBindProj bi fuel N leafSpec)
    (e : ImpExpr) :
    ∀ (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
      HaxToLowCTSimulates bi fuel N leafSpec e c env env' rs v := by
  induction e using ImpExpr.ind with
  -- ─── Trivial / unreachable arms ──────────────────────────────────
  | lit l => intro c env env' rs v
             exact haxToLowCT_simulates_lit bi fuel N leafSpec l c env env' rs v
  | tuple elems _ => intro c env env' rs v
                     exact haxToLowCT_simulates_tuple bi fuel N leafSpec elems c env env' rs v
  | proj e i _ => intro c env env' rs v
                  exact haxToLowCT_simulates_proj bi fuel N leafSpec e i c env env' rs v
  | borrow e _ => intro c env env' rs v
                  exact haxToLowCT_simulates_borrow bi fuel N leafSpec e c env env' rs v
  | deref e _ => intro c env env' rs v
                 exact haxToLowCT_simulates_deref bi fuel N leafSpec e c env env' rs v
  | continue_ => intro c env env' rs v
                 exact haxToLowCT_simulates_continue bi fuel N leafSpec c env env' rs v
  | break_none => intro c env env' rs v
                  exact haxToLowCT_simulates_break bi fuel N leafSpec none c env env' rs v
  | break_some e _ => intro c env env' rs v
                      exact haxToLowCT_simulates_break bi fuel N leafSpec (some e) c env env' rs v
  | earlyReturn e _ => intro c env env' rs v
                       exact haxToLowCT_simulates_earlyReturn bi fuel N leafSpec e c env env' rs v
  | questionMark e _ => intro c env env' rs v
                        exact haxToLowCT_simulates_questionMark bi fuel N leafSpec e c env env' rs v
  | forLoop v_l lo hi body _ _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_forLoop bi fuel N leafSpec v_l lo hi body c env env' rs v
  | forLoopRev v_l lo hi body _ _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_forLoopRev bi fuel N leafSpec v_l lo hi body c env env' rs v
  | forFold v_l lo hi body _ _ _ =>
      -- `denote` gives the post-phase loop constructors no meaning; the
      -- simulation over `forToLoop` is `haxToLowCT_simulates_forFold`
      -- (`HaxToLowCTSim_ProgramLoops`).
      intro c env env' rs v _ hEval _
      rw [evalImp_forFold_eq_none] at hEval
      contradiction
  | forFoldRev v_l lo hi body _ _ _ =>
      intro c env env' rs v _ hEval _
      rw [evalImp_forFoldRev_eq_none] at hEval
      contradiction
  | whileFold cond body _ _ =>
      intro c env env' rs v _ hEval _
      rw [evalImp_whileFold_eq_none] at hEval
      contradiction
  | forFoldReturn v_l lo hi body _ _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_forFoldReturn bi fuel N leafSpec v_l lo hi body c env env' rs v
  | forFoldRevReturn v_l lo hi body _ _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_forFoldRevReturn bi fuel N leafSpec v_l lo hi body c env env' rs v
  | typeAscription e ty ih =>
      intro c env env' rs v
      unfold HaxToLowCTSimulates
      intro hc he hagr
      rw [haxToLowCT_typeAscription_eq] at hc
      rw [evalImp_typeAscription] at he
      exact ih c env env' rs v hc he hagr
  | whileFoldReturn cond body _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_whileFoldReturn bi fuel N leafSpec cond body c env env' rs v
  | cfBreak e _ => intro c env env' rs v
                   exact haxToLowCT_simulates_cfBreak bi fuel N leafSpec e c env env' rs v
  | cfContinue e _ => intro c env env' rs v
                      exact haxToLowCT_simulates_cfContinue bi fuel N leafSpec e c env env' rs v
  | cfBreakContinue e _ => intro c env env' rs v
                           exact haxToLowCT_simulates_cfBreakContinue bi fuel N leafSpec e c env env' rs v
  -- ─── `app` at top (rejected, but no _simulates_app instance — inline) ─
  | app f args _ => intro c env env' rs v hHax _ _; simp [haxToLowCT] at hHax
  -- ─── `lam` (first-class closure, rejected — lowers to none) ───────────
  | lam _ _ _ => intro c env env' rs v hHax _ _; simp [haxToLowCT] at hHax
  -- ─── Productive arms ──────────────────────────────────────────────
  | var name => intro c env env' rs v
                exact haxToLowCT_simulates_var bi fuel N leafSpec name c env env' rs v
  | unitVal => intro c env env' rs v
               exact haxToLowCT_simulates_unitVal bi fuel N leafSpec c env env' rs v
  | seq e1 e2 ih1 ih2 =>
      intro c env env' rs v
      exact haxToLowCT_simulates_seq bi fuel N leafSpec e1 e2 c env env' rs v ih1 ih2
  | letBind name val body _ ihBody =>
      intro c env env' rs v
      cases val with
      | lit l => exact haxToLowCT_simulates_letBind_lit bi fuel N leafSpec name l body c env env' rs v ihBody
      | app f args => exact hLetBindApp name f args body c env env' rs v ihBody
      | var src =>
          exact haxToLowCT_simulates_letBind_var bi fuel N leafSpec
            name src body c env env' rs v ihBody
      | proj pe i =>
          -- Tuple-component read `let name = tup.i; body`: productive
          -- only for a `var` base; delegated to `hLetBindProj` (the
          -- component lands in a tower slot — see the Full-predicate
          -- closure).  Non-`var` bases stay untranslated.
          cases pe with
          | var t => exact hLetBindProj name t i body c env env' rs v ihBody
          | _ => intro hHax _ _; simp [haxToLowCT] at hHax
      | _ => intro hHax _ _; simp [haxToLowCT] at hHax
  | ifThenElse cond t e _ ihT ihE =>
      intro c env env' rs v
      cases cond with
      | var v_cond => exact haxToLowCT_simulates_ifThenElse_var bi fuel N leafSpec v_cond t e c env env' rs v ihT ihE
      | _ => intro hHax _ _; simp [haxToLowCT] at hHax
  | match_ scrut arms ihScrut ihArms =>
      intro c env env' rs v
      exact hMatch scrut arms c env env' rs v ihScrut ihArms
  | whileLoop cond body _ ihBody =>
      intro c env env' rs v
      cases cond with
      | var v_cond => exact hWhileLoop v_cond body c env env' rs v ihBody
      | _ => intro hHax _ _; simp [haxToLowCT] at hHax
  | assign name rhs _ =>
      intro c env env' rs v
      cases rhs with
      | lit l =>
          cases l with
          | uintLit w n => exact haxToLowCT_simulates_assign_lit_uintLit bi fuel N leafSpec name w n c env env' rs v
          | bool b => exact haxToLowCT_simulates_assign_lit_bool bi fuel N leafSpec name b c env env' rs v
          | int n =>
              by_cases hn : 0 ≤ n
              · exact haxToLowCT_simulates_assign_lit_int bi fuel N leafSpec name n hn c env env' rs v
              · intro hHax _ _; simp [haxToLowCT, hn] at hHax
          | _ => intro hHax _ _; simp [haxToLowCT] at hHax
      | app f args => exact hAssignApp name f args c env env' rs v
      | _ => intro hHax _ _; simp [haxToLowCT] at hHax

end CatCrypt.Crypto.Hax
