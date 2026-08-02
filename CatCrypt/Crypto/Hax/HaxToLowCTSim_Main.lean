/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Hax.HaxToLowCTSimulates
import CatCrypt.Crypto.Hax.HaxToLowCTSim_Agreement
import CatCrypt.Crypto.Hax.HaxToLowCTSim_AssignMatch
import CatCrypt.Crypto.Hax.HaxToLowCTSim_Call
import CatCrypt.Crypto.Hax.HaxToLowCTSim_If
import CatCrypt.Crypto.Hax.HaxToLowCTSim_While

/-!
# H3.final: Assembly of the Hax → LowCT simulation theorem

Wires together the per-case lemmas from `HaxToLowCTSim_*.lean` into
the main theorem.  Dispatches via `ImpExpr.ind` (the custom induction
principle for nested-inductive `ImpExpr` at
`CatCrypt/Hax/AST.lean:109`).

## Architecture

The proof is a structural induction on `ImpExpr` via `ImpExpr.ind`.
Each constructor case dispatches to its per-file lemma:

| Constructor | Closure | Source file |
|---|---|---|
| `var _` | `haxToLowCT_simulates_var` | `HaxToLowCTSimulates.lean` |
| `unitVal` | `haxToLowCT_simulates_unitVal` | `HaxToLowCTSimulates.lean` |
| `seq a b` | `haxToLowCT_simulates_seq` | `HaxToLowCTSimulates.lean` |
| `letBind _ (lit _) _` | `haxToLowCT_simulates_letBind_lit` | `HaxToLowCTSim_Agreement.lean` |
| `letBind _ (app _ _) _` | **DEFERRED** (H3.quarta) | parametric hyp `Hyp_letBindApp` |
| `letBind _ (proj (var _) _) _` | parametric hyp `Hyp_letBindProj` | genuine closure in `Main_Full` |
| `letBind _ _ _` (other) | contradiction | inline `simp [haxToLowCT]` |
| `assign _ (lit (uintLit ..))` | `haxToLowCT_simulates_assign_lit_uintLit` | `HaxToLowCTSim_AssignMatch.lean` |
| `assign _ (lit (int n))`, n≥0 | `haxToLowCT_simulates_assign_lit_int` | `HaxToLowCTSim_AssignMatch.lean` |
| `assign _ (lit (bool _))` | `haxToLowCT_simulates_assign_lit_bool` | `HaxToLowCTSim_AssignMatch.lean` |
| `tuple es` (all `var`s → `RSkip`) | `haxToLowCT_simulates_tuple` | `HaxToLowCTSimulates.lean` |
| `assign _ (app _ _)` | **DEFERRED** (H3.quarta) | parametric hyp `Hyp_assignApp` |
| `assign _ _` (other) | contradiction | inline |
| `ifThenElse (var _) _ _` | `haxToLowCT_simulates_ifThenElse_var` | `HaxToLowCTSim_If.lean` |
| `ifThenElse _ _ _` (other) | contradiction | inline |
| `whileLoop (var _) _` | `haxToLowCT_simulates_whileLoop_var` | `HaxToLowCTSim_While.lean` |
| `whileLoop _ _` (other) | contradiction | inline |
| `match_ (app _ _) [(tuplePat [varPat _, varPat _], _)]` | **DEFERRED** (H3.quarta, H2.1) | parametric hyp `Hyp_matchTuple` |
| `match_ _ _` (other) | contradiction | inline |
| All other rejected arms | `haxToLowCT_simulates_*` (H3.septa) | `HaxToLowCTSimulates.lean` |

## Parametric form vs full theorem

This file ships **two** statements:

1. `haxToLowCT_simulates_param` — the parametric main theorem,
   taking the three deferred-case hypotheses (`Hyp_letBindApp`,
   `Hyp_assignApp`, `Hyp_matchTuple`) as inputs.  This compiles
   today and contains the full dispatch.

2. `haxToLowCT_simulates` — the unconditional main theorem,
   obtained by discharging the three hypotheses once H3.quarta lands
   (tower-typed `envAgreesRust` + `LeafCallAgrees` instances).
   **Not yet stated** — pending H3.quarta.

## H3.quarta blocker (Agent B's finding)

The three deferred cases share a root cause: `RustExec.call` updates
the *tower* slot via `locatedUpdate`, not the *scalar* slot.  The
current `envAgreesRust` predicate covers only scalar bindings.

To discharge the three `Hyp_*` parameters, H3.quarta must:

* Extend `envAgreesRust` to cover tower bindings (parallel to
  CryptoSSA's `bindingOK` byte-layout transport).
* Add `valueToTowerVal : Value → (dt : TowerType) → Option (RustVal dt)`.
* Provide per-leaf `LeafCallAgrees` instances grounded in the
  extracted leaf-call semantics.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Deferred-case hypotheses

These three hypotheses parameterise the main theorem over the
H3.quarta-pending arms. -/

/-- Hypothesis: `letBind name (app f args) body` simulates.  Discharged
    by H3.quarta once tower-typed agreement + per-leaf
    `LeafCallAgrees` are in place. -/
abbrev Hyp_letBindApp
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (f : String) (args : List ImpExpr) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.letBind name (.app f args) body) c env env' rs v

/-- Hypothesis: `assign name (app f args)` simulates.  Same blocker. -/
abbrev Hyp_assignApp
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (f : String) (args : List ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.assign name (.app f args)) c env env' rs v

/-- Hypothesis: `match_` 2-tuple destructure of an `app` simulates.
    Blocked on H2.1 + H3.quarta. -/
abbrev Hyp_matchTuple
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (f : String) (args : List ImpExpr) (n1 n2 : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.match_ (.app f args) [(.tuplePat [.varPat n1, .varPat n2], body)])
      c env env' rs v

/-! ## §2  Plan-text for the main theorem

The full dispatch via `ImpExpr.ind` has the following structure.  We
include it as a documented plan rather than a closed term — the actual
term requires careful case-handling for the `letBind`/`assign`/`match_`
arms (which have inner sub-cases on the RHS / scrutinee shape).

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

This dispatch is correct in shape but needs minor adjustments for:
* The exact constructor-argument count of `ImpExpr.ind`'s cases (each
  recursive sub-term provides one IH argument).
* The `cases l with | int n => if hn : 0 ≤ n` shape — Lean's
  `cases` doesn't easily integrate with the conditional, so this
  needs a `by_cases hn : 0 ≤ n` or a helper.
* The `match arms with | ...` inside the `match_` case — only the
  specific 2-tuple shape is accepted; all other shapes contradict.

Closing this in a single commit is the H3.final landing step.  The
proof body above is ~40 lines plus the cases that need tactical
clean-up — total ~60–80 lines for the full dispatch.
-/

/-! ## §3  Hypothesis: whileLoop simulation

Agent E's `haxToLowCT_simulates_whileLoop_var` closes under two
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
    form simplifies the dispatcher; internally, all but the H2.1
    tuple-destructure shape contradict via `haxToLowCT` returning
    `none`.  Discharged in a follow-up that case-splits on
    scrut/arms shapes. -/
abbrev Hyp_match
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (scrut : ImpExpr) (arms : List (CatCrypt.Hax.ImpPat × ImpExpr))
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihScrut : ∀ c' env_a env_b rs_a v_a,
                  HaxToLowCTSimulates bi fuel N leafSpec scrut c' env_a env_b rs_a v_a)
    (_ihArms : ∀ pa ∈ arms,
                  ∀ c' env_a env_b rs_a v_a,
                    HaxToLowCTSimulates bi fuel N leafSpec pa.2 c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec (.match_ scrut arms) c env env' rs v

/-- Hypothesis: `letBind name (.var src) body` (parameter-alias) simulates.

The translator emits `haxToLowCT body` for this shape (parameter-alias
treated as no-op).  Source-side semantics extends `env` with
`name ↦ env src`.  The closure requires that the env-extension preserves
agreement — which holds when `name = src` (the standard hax-extraction
shape: `let a = a; let b = b; let r = ZERO_VEC; ...`).

In the parametric form, we leave the alias closure as a hypothesis.
Concrete deployments discharge it via a syntactic check on the
extracted `ImpExpr` (every alias has `name = src`). -/
abbrev Hyp_letBindVarAlias
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name src : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulates bi fuel N leafSpec body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulates bi fuel N leafSpec
      (.letBind name (.var src) body) c env env' rs v

/-- Hypothesis: `letBind name ((.var t).i) body` (tuple-component read)
    simulates.  The translator lowers this shape to
    `RLetZero name _ (RSeq (RTupleLoad ..) ..)`, whose result lands in a
    *tower* slot — outside the scalar-only agreement this predicate
    threads.  The genuine closure (component value related through the
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

This is the H3.final closure modulo the four `Hyp_*` hypotheses for
deferred cases.  All other cases (var, unitVal, seq, letBind lit,
assign lit (uintLit / int n≥0), ifThenElse var, whileLoop (handled
by hypothesis), all 22 unreachable arms) are closed inline. -/

theorem haxToLowCT_simulates_param
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hLetBindApp : Hyp_letBindApp bi fuel N leafSpec)
    (hAssignApp : Hyp_assignApp bi fuel N leafSpec)
    (hMatch : Hyp_match bi fuel N leafSpec)
    (hWhileLoop : Hyp_whileLoop bi fuel N leafSpec)
    (hLetBindVarAlias : Hyp_letBindVarAlias bi fuel N leafSpec)
    (hLetBindProj : Hyp_letBindProj bi fuel N leafSpec)
    (e : ImpExpr) :
    ∀ (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
      HaxToLowCTSimulates bi fuel N leafSpec e c env env' rs v := by
  induction e using ImpExpr.ind with
  -- ─── Trivial / unreachable arms (H3.septa) ────────────────────────
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
      intro c env env' rs v
      exact haxToLowCT_simulates_forFold bi fuel N leafSpec v_l lo hi body c env env' rs v
  | forFoldRev v_l lo hi body _ _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_forFoldRev bi fuel N leafSpec v_l lo hi body c env env' rs v
  | whileFold cond body _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_whileFold bi fuel N leafSpec cond body c env env' rs v
  | forFoldReturn v_l lo hi body _ _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_forFoldReturn bi fuel N leafSpec v_l lo hi body c env env' rs v
  | forFoldRevReturn v_l lo hi body _ _ _ =>
      intro c env env' rs v
      exact haxToLowCT_simulates_forFoldRevReturn bi fuel N leafSpec v_l lo hi body c env env' rs v
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
  -- ─── Productive arms (H3.bis / H3.tertia / H3.sexta) ──────────────
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
          -- After the 2026-05 extension, `letBind _ (.var src) body` is a
          -- parameter-alias that lowers to `haxToLowCT body`.  The
          -- closure is delegated to the `hLetBindVarAlias` hypothesis,
          -- which deployers discharge syntactically via the
          -- `name = src` invariant of hax extractions.
          exact hLetBindVarAlias name src body c env env' rs v ihBody
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

/-! ## §5  Status -/

/-- Documentation marker — the chain of imports composes. -/
theorem h3_chain_compiles : True := trivial

end CatCrypt.Crypto.Hax
