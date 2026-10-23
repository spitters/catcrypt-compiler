/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

import all Init.Data.Repr
public import CatCrypt.Crypto.Hax.HaxToLowCT
public import CatCrypt.Crypto.Hax.HaxCallNames
public import CatCrypt.Crypto.Hax.ImpEval
public import HaxLean.Semantics
public import HaxLean.Value
public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# Hax → LowCT Semantic Simulation

States the semantic-preservation theorem for
`haxToLowCT : ImpExpr → Option LowCT` and proves its structural cases.

`HaxToLowCT.lean` provides the syntactic side (representability
biconditionals).  This module adds the **dynamics**: when `haxToLowCT
e = some c`, the LowCT `c` denotes the same thing as the source
ImpExpr `e`.

## Position in the chain

```
   cargo hax json
        ↓ (haxpipeT trusted renderer)
   ImpExpr     —— denote (StateM Env Outcome) ——
        ↓ haxToLowCT                                ← BRIDGED HERE
   LowCT     —— RustExec (relational) ——
        ↓ rustExecSimulatesDialect
   catCryptDialect / Jasmin
```

## Case split

| Cases | Module |
|---|---|
| `var`, `unitVal`, `seq`, rejected arms | this module |
| lit-let, scalar assign | `HaxToLowCTSim_Agreement`, `HaxToLowCTSim_AssignMatch` |
| leaf calls (u64, TFp, TFp2, TFp25519, TBytes) | `HaxToLowCTSim_Call`, `HaxToLowCTSim_Quarta*` |
| `ifThenElse`, `whileLoop` | `HaxToLowCTSim_If`, `HaxToLowCTSim_While` |
| assembly | `HaxToLowCTSim_Main` |

## Structural-recursion note

`ImpExpr` is a **nested inductive** type (it contains `List ImpExpr`
in the `tuple` and `app` arms, and `List (ImpPat × ImpExpr)` in
`match_`).  Lean's `induction` tactic does not produce induction
hypotheses for nested-inductive sub-terms in nested positions.

The simulation proofs use the custom induction principle
`ImpExpr.ind` (hax-lean `HaxLean/AST.lean`) under
`induction ... using`.

## Contents

* §1 Agreement predicate
* §2 Source-side `evalImp` (defined in `ImpEval`)
* §3 Main theorem statement (as `def` returning `Prop`)
* §4 Demo lemmas validating the predicate setup
* §5 Unreachable arms
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote denoteArgs defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Environment/state agreement predicate

This predicate covers scalar bindings only.  Tower-typed agreement
(content-bearing, byte-layout transport in the style of `bindingOK`)
is `envAgreesRustFull` in `HaxToLowCTSim_Quarta.lean`. -/

/-- Agreement on a single name.  If the Hax env has a value that
    decodes to a scalar, the RustState's scalar binding agrees. -/
def nameAgreesScalar (env : Env) (rs : RustState) (name : String) : Prop :=
  ∀ v, env name = some v →
    ∀ n, valueToScalar v = some n →
      rs.rsScalar name = n

/-- Top-level agreement: scalar-only.  `envAgreesRustFull` in
    `HaxToLowCTSim_Quarta.lean` covers tower and byte bindings. -/
def envAgreesRust (env : Env) (rs : RustState) : Prop :=
  ∀ name, nameAgreesScalar env rs name

/-! ## §2  Source-side evaluation

The value projection `evalImp` of `denote` and its unfold lemmas
(`evalImp_unitVal`, `evalImp_var_some`, `evalImp_var_inv`,
`evalImp_unitVal_inv`, `denote_typeAscription`, `evalImp_typeAscription`,
`evalImp_letBind_lit_inv`) are in `CatCrypt.Crypto.Hax.ImpEval`, which this
module re-exports. -/

/-- The standard simp set for unfolding StateM operations on `denote`. -/
abbrev stateMUnfolds : List Lean.Name := [] -- documentation only

/-- `haxToLowCT` erases a type ascription. -/
theorem haxToLowCT_typeAscription_eq (e : ImpExpr) (ty : String) :
    haxToLowCT (.typeAscription e ty) = haxToLowCT e := by
  simp [haxToLowCT]

/-! ## §3  Main simulation theorem (statement) -/

/--
**Hax → LowCT simulation conclusion**.

The shape of the per-case obligations: given a successful translation
and a successful source-side evaluation, there exists a LowCT
post-state satisfying the agreement predicate.

This is packaged as a `def` (rather than `theorem`) so the file
builds without requiring a proof body; the proof obligation is
satisfied by `haxToLowCT_simulates` once closed. -/
def HaxToLowCTSimulates
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value) : Prop :=
  haxToLowCT e = some c →
  evalImp bi fuel e env = some (v, env') →
  envAgreesRust env rs →
  ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRust env' rs'

/-!
### Planned full statement

```
theorem haxToLowCT_simulates
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec e c env env' rs v
```

Per-clause proof obligations (one per arm of `haxToLowCT` that
returns `some _`):

| Source pattern | Target LowCT |
|---|---|
| `var _` | `RSkip` |
| `unitVal` | `RSkip` |
| `seq a b` | `RSeq aC bC` |
| `letBind _ (lit (uintLit _ _)) body` | `RLetU64Zero + RSeq (RScalarSet ..) bodyC` |
| `letBind _ (lit (int n)) body`, `n ≥ 0` | same |
| `letBind _ (app f args) body` | `RLetZero _ (RSeq (RCall ..) bodyC)` |
| `assign _ (lit (int n))`, `n ≥ 0` | `RScalarSet _ n.toNat` |
| `assign _ (lit (uintLit _ n))` | `RScalarSet _ n` |
| `assign _ (app f args)` | `RCall f _ args'` |
| `ifThenElse (var v) t e` | `RIfNz v tC eC` |
| `whileLoop (var v) body` | `RWhileNz v bodyC` |
| `match_ (app f args) [(tuplePat ..)]` | `RLetZero + RLetZero + RCallSwap` |

All other arms of `haxToLowCT` return `none`, so the hypothesis
`haxToLowCT e = some c` is `False`; these cases discharge
by contradiction (§5).
-/

/-! ## §4  Demo lemmas validating the predicate setup

These check that the predicate machinery composes — i.e. that the
per-case obligations are stateable as instances of
`HaxToLowCTSimulates`. -/

/-! ### §4.1  `var _` case is stateable

For any `e = .var name`, `haxToLowCT e = some .RSkip`.  The
simulation obligation specialises cleanly. -/

theorem haxToLowCT_var_some (name : String) :
    haxToLowCT (.var name) = some .RSkip := by
  simp [haxToLowCT]

/-! ### §4.2  `unitVal` case is stateable -/

theorem haxToLowCT_unitVal_some :
    haxToLowCT .unitVal = some .RSkip := by
  simp [haxToLowCT]

/-! ### §4.3  `RSkip` simulation: structural lemma

For the `var` and `unitVal` cases, `c = .RSkip` and the LowCT
execution is the identity.  Agreement is preserved by reflexivity.
This is the per-case proof for `var` and `unitVal` once the source-
side env-preservation lemma is in place. -/

theorem rustExec_RSkip_refl
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    RustExec N leafSpec .RSkip rs rs :=
  RustExec.skip rs

/-! ### §4.4  `RSeq` simulation: structural lemma

For the `seq` case, the LowCT execution chains via `RustExec.seq`.
The per-case proof composes two IH results. -/

theorem rustExec_RSeq_chain
    (N : Nat) (leafSpec : LeafSpec) (c1 c2 : LowCT)
    (rs r1 rs' : RustState)
    (h1 : RustExec N leafSpec c1 rs r1)
    (h2 : RustExec N leafSpec c2 r1 rs') :
    RustExec N leafSpec (.RSeq c1 c2) rs rs' :=
  RustExec.seq c1 c2 rs r1 rs' h1 h2

/-! ### §4.5  `RLetU64Zero` + `RScalarSet` simulation: lit-let lemma

For the `letBind _ (lit _) body` case, the LowCT execution sets a
scalar to zero (allocation), then to the literal value, then runs
the body.  This lemma packages the first two steps. -/

/-- Helper: setting the same scalar twice collapses to the second value. -/
theorem rsSetScalar_collapse (rs : RustState) (name : String) (m n : Nat) :
    rsSetScalar (rsSetScalar rs name m) name n = rsSetScalar rs name n := by
  rcases rs with ⟨t, s⟩
  simp only [rsSetScalar]
  congr 1
  funext y
  by_cases hy : y = name <;> simp [hy]

theorem rustExec_RLetU64Zero_ScalarSet
    (N : Nat) (leafSpec : LeafSpec) (name : String) (n : Nat)
    (body : LowCT) (rs rs' : RustState)
    (hBody : RustExec N leafSpec body (rsSetScalar rs name n) rs') :
    RustExec N leafSpec
      (.RLetU64Zero name (.RSeq (.RScalarSet name n) body)) rs rs' := by
  refine RustExec.letU64Zero name _ rs rs' ?_
  refine RustExec.seq _ _ _ _ _ ?_ hBody
  rw [← rsSetScalar_collapse rs name 0 n]
  exact RustExec.scalarSet (N := N) (leafSpec := leafSpec)
          name n (rsSetScalar rs name 0)

/-! ### §4.6  `RIfNz` simulation: control-flow dispatcher

For the `ifThenElse (var v) t e` case, the LowCT reads the scalar
`v` and dispatches.  This lemma packages the dispatch given an IH
on the chosen branch. -/

theorem rustExec_RIfNz_dispatch_true
    (N : Nat) (leafSpec : LeafSpec) (cond : String) (ct cf : LowCT)
    (rs rs' : RustState) (n : Nat) (hCond : rs.rsScalar cond = n) (hNz : n ≠ 0)
    (hThen : RustExec N leafSpec ct rs rs') :
    RustExec N leafSpec (.RIfNz cond ct cf) rs rs' :=
  RustExec.ifTrue cond ct cf rs rs' n hCond hNz hThen

/-! ### §4.7  var and unitVal simulation instances

These are two productive (non-contradiction) cases of the main
theorem.  Both reduce to `RSkip` on the LowCT side, with
env / rs both unchanged. -/

theorem haxToLowCT_simulates_var
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.var name) c env env' rs v := by
  intro hHax hEval hAgree
  rw [haxToLowCT_var_some] at hHax
  cases hHax  -- c = .RSkip
  obtain ⟨_hLookup, henv⟩ := evalImp_var_inv bi fuel name env v env' hEval
  refine ⟨rs, RustExec.skip rs, ?_⟩
  rw [henv]
  exact hAgree

theorem haxToLowCT_simulates_unitVal
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec .unitVal c env env' rs v := by
  intro hHax hEval hAgree
  rw [haxToLowCT_unitVal_some] at hHax
  cases hHax  -- c = .RSkip
  obtain ⟨_hv, henv⟩ := evalImp_unitVal_inv bi fuel env v env' hEval
  refine ⟨rs, RustExec.skip rs, ?_⟩
  rw [henv]
  exact hAgree

theorem rustExec_RIfNz_dispatch_false
    (N : Nat) (leafSpec : LeafSpec) (cond : String) (ct cf : LowCT)
    (rs rs' : RustState) (hCond : rs.rsScalar cond = 0)
    (hElse : RustExec N leafSpec cf rs rs') :
    RustExec N leafSpec (.RIfNz cond ct cf) rs rs' :=
  RustExec.ifFalse cond ct cf rs rs' hCond hElse

/-! ## §5  Unreachable arms — closure template

Every `ImpExpr` constructor whose `haxToLowCT` arm returns `none`
contributes a vacuously-true per-case obligation: the hypothesis
`haxToLowCT e = some c` is `False`.  These are the
"closure-by-contradiction" cases.

The template (one per constructor) is:

```
theorem haxToLowCT_simulates_<ctor> ... :
    HaxToLowCTSimulates ... :=
  fun h _ _ => by simp [haxToLowCT] at h
```

§5.5 instantiates it for each rejected constructor. -/

/-! ### §5.1  Sample: `lit` at tail position is unreachable -/

theorem haxToLowCT_lit_top_eq_none (l : ImpLit) :
    haxToLowCT (.lit l) = none := by
  cases l <;> simp [haxToLowCT]

/-! ### §5.2  `tuple`: aggregate tuple tail

An all-`var` tuple tail translates to `RSkip` (each named component
already lives in its slot — same justification as the trailing `var _`
arm); a tuple with a non-`var` component is unreachable. -/

theorem haxToLowCT_tuple_of_vars (elems : List ImpExpr)
    (h : elems.all isVar = true) :
    haxToLowCT (.tuple elems) = some .RSkip := by
  simp [haxToLowCT, h]

theorem haxToLowCT_tuple_eq_none_of_not_all_vars (elems : List ImpExpr)
    (h : ¬ elems.all isVar = true) :
    haxToLowCT (.tuple elems) = none := by
  simp [haxToLowCT, h]

/-! #### Source-side helpers for the tuple tail

`denote` on an all-`var` tuple leaves the env unchanged (each component
read is effect-free), so the `RSkip` target trivially preserves
agreement.  The unfold equations `denote_var_run_eq` and
`denoteArgs_cons_run_eq` are in `Hax.ImpEval`. -/

/-- `denoteArgs` on an all-`var` list leaves the env unchanged. -/
theorem denoteArgs_vars_run_env (bi : Builtins) (fuel : Nat)
    (es : List ImpExpr) :
    es.all isVar = true → ∀ env : Env,
      ∃ o, (denoteArgs bi fuel es).run env = (o, env) := by
  induction es with
  | nil =>
    intro _ env
    refine ⟨some [], ?_⟩
    have hEq : denoteArgs bi fuel ([] : List ImpExpr) = pure (some []) := by
      conv_lhs => unfold denoteArgs
    rw [hEq]
    rfl
  | cons e es ih =>
    intro h env
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hHead, hTail⟩ := h
    cases e <;> simp [isVar] at hHead
    rename_i n
    rw [denoteArgs_cons_run_eq, denote_var_run_eq]
    cases hen : env n with
    | none => exact ⟨none, rfl⟩
    | some v =>
      obtain ⟨o, ho⟩ := ih hTail env
      refine ⟨o.map (v :: ·), ?_⟩
      show (match (denoteArgs bi fuel es).run env with
            | (rest, env_b) => (rest.map (v :: ·), env_b)) =
            (o.map (v :: ·), env)
      rw [ho]

/-- Unfold equation for `.tuple`. -/
theorem denote_tuple_run_eq (bi : Builtins) (fuel : Nat)
    (elems : List ImpExpr) (env : Env) :
    (denote bi fuel (.tuple elems)).run env =
      (match (denoteArgs bi fuel elems).run env with
       | (some vals, env_a) => (.val (.tuple vals), env_a)
       | (none, env_a) => (.err "non-value in tuple elements", env_a)) := by
  show (denote bi fuel (.tuple elems)).run env = _
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  cases denoteArgs bi fuel elems env with
  | mk mvals s => cases mvals <;> rfl

/-- Inverse: a successful `evalImp` on an all-`var` tuple leaves the env
    unchanged. -/
theorem evalImp_tuple_vars_inv (bi : Builtins) (fuel : Nat)
    (elems : List ImpExpr) (env : Env) (v : Value) (env' : Env)
    (hAll : elems.all isVar = true)
    (h : evalImp bi fuel (.tuple elems) env = some (v, env')) :
    env' = env := by
  obtain ⟨o, ho⟩ := denoteArgs_vars_run_env bi fuel elems hAll env
  unfold evalImp at h
  rw [denote_tuple_run_eq, ho] at h
  cases o with
  | some vals =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | none => simp at h

/-! ### §5.2b  Source-side helpers for the letBind-proj arm

`let name = (.var t).i; body` is the tuple-component destructuring
shape (K-PKE keygen's `(ek, dk)` pair).  These lemmas expose the rhs
denotation and invert a successful `evalImp` on the whole binding. -/

/-- `.proj (.var t) i` on a bound tuple with an in-range index runs to
    the component value; env unchanged. -/
theorem denote_proj_var_run_some (bi : Builtins) (fuel : Nat)
    (t : String) (i : Nat) (env : Env) (vTup vi : Value)
    (hEnv : env t = some vTup) (hProj : vTup.projIdx i = some vi) :
    (denote bi fuel (.proj (.var t) i)).run env = (.val vi, env) := by
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
             MonadStateOf.get, StateT.get, pure, Pure.pure, StateT.pure,
             hEnv, hProj]

/-- `.proj (.var t) i` with `t` unbound runs to the undefined-variable
    error; env unchanged. -/
theorem denote_proj_var_run_err_of_env_none (bi : Builtins) (fuel : Nat)
    (t : String) (i : Nat) (env : Env)
    (hEnv : env t = none) :
    (denote bi fuel (.proj (.var t) i)).run env =
      (.err s!"undefined variable: {t}", env) := by
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
             MonadStateOf.get, StateT.get, pure, Pure.pure, StateT.pure, hEnv]

/-- `.proj (.var t) i` with an out-of-range (or non-tuple) projection
    runs to the projection error; env unchanged. -/
theorem denote_proj_var_run_err_of_proj_none (bi : Builtins) (fuel : Nat)
    (t : String) (i : Nat) (env : Env) (vTup : Value)
    (hEnv : env t = some vTup) (hProj : vTup.projIdx i = none) :
    (denote bi fuel (.proj (.var t) i)).run env =
      (.err s!"projection index {i} out of range", env) := by
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
             MonadStateOf.get, StateT.get, pure, Pure.pure, StateT.pure,
             hEnv, hProj]

/-- Local copy of the `.letBind` unfold equation (the canonical
    `denote_letBind_run_eq` lives downstream in
    `HaxToLowCTSim_AnfShaped.lean`, which imports this file). -/
theorem denote_letBind_run_eq' (bi : Builtins) (fuel : Nat) (n : String)
    (val body : ImpExpr) (env : Env) :
    (denote bi fuel (.letBind n val body)).run env =
      (match (denote bi fuel val).run env with
       | (.val v, env_a) => (denote bi fuel body).run (env_a.extend n v)
       | (other, env_a) => (other, env_a)) := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure,
        modify, modifyGet, MonadStateOf.modifyGet]
  cases denote bi fuel val env with
  | mk a s => cases a <;> rfl

/-- Inverse: a successful `evalImp` on `let name = (.var t).i; body`
    yields the tuple value at `t`, its `i`-th component, and the body
    evaluation in the env extended with the component. -/
theorem evalImp_letBind_proj_inv (bi : Builtins) (fuel : Nat)
    (name t : String) (i : Nat) (body : ImpExpr)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.letBind name (.proj (.var t) i) body) env
           = some (v, env')) :
    ∃ vTup vi, env t = some vTup ∧ vTup.projIdx i = some vi ∧
      evalImp bi fuel body (env.extend name vi) = some (v, env') := by
  unfold evalImp at h ⊢
  rw [denote_letBind_run_eq' bi fuel name _ body env] at h
  cases hEnvT : env t with
  | none =>
    rw [denote_proj_var_run_err_of_env_none bi fuel t i env hEnvT] at h
    simp at h
  | some vTup =>
    cases hProj : vTup.projIdx i with
    | none =>
      rw [denote_proj_var_run_err_of_proj_none bi fuel t i env vTup
            hEnvT hProj] at h
      simp at h
    | some vi =>
      rw [denote_proj_var_run_some bi fuel t i env vTup vi hEnvT hProj] at h
      exact ⟨vTup, vi, rfl, hProj, h⟩

/-! ### §5.3  Sample: `borrow` is unreachable -/

theorem haxToLowCT_borrow_eq_none (e : ImpExpr) :
    haxToLowCT (.borrow e) = none := by
  simp [haxToLowCT]

/-! ### §5.4  Sample: control-flow constructors are unreachable -/

theorem haxToLowCT_break_eq_none (m : Option ImpExpr) :
    haxToLowCT (.break_ m) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_continue_eq_none :
    haxToLowCT .continue_ = none := by
  simp [haxToLowCT]

theorem haxToLowCT_earlyReturn_eq_none (e : ImpExpr) :
    haxToLowCT (.earlyReturn e) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_questionMark_eq_none (e : ImpExpr) :
    haxToLowCT (.questionMark e) = none := by
  simp [haxToLowCT]

/-- `.proj` at *tail* position has no destination slot and stays
    untranslated.  The productive proj shape is `letBind`-bound —
    `let name = (.var t).i; body` lowers via the letBind-proj arm to
    `RTupleLoad` (see `denote_proj_var_run_some` /
    `evalImp_letBind_proj_inv` below for its source-side inverses). -/
theorem haxToLowCT_proj_eq_none (e : ImpExpr) (i : Nat) :
    haxToLowCT (.proj e i) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_deref_eq_none (e : ImpExpr) :
    haxToLowCT (.deref e) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_forLoop_eq_none
    (v : String) (lo hi body : ImpExpr) :
    haxToLowCT (.forLoop v lo hi body) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_forLoopRev_eq_none
    (v : String) (lo hi body : ImpExpr) :
    haxToLowCT (.forLoopRev v lo hi body) = none := by
  simp [haxToLowCT]

set_option maxHeartbeats 800000 in
/-- For-fold with a non-convertible-bound shape returns `none`.

    The literal-bounded forms (zero- or offset-start over `RFor`) and
    the convertible runtime-bound forms (`RForRuntime`, including the
    offset-start variant) all translate; every one of them requires
    `impBoundToSExpr hi` to succeed (a nonneg literal `hi` converts),
    so `h_not_runtime` excludes them all.  This lemma covers only the
    residual non-convertible cases.  Callers operating on arbitrary
    `lo`, `hi` need the case-split helper
    `haxToLowCT_simulates_forFold` below. -/
theorem haxToLowCT_forFold_eq_none
    (v : String) (lo hi body : ImpExpr)
    (h_not_lit : ¬ ∃ n : Int, lo = .lit (.int 0) ∧ hi = .lit (.int n) ∧ n ≥ 0)
    (h_not_uint : ¬ ∃ (w : Hax.IntWidth) (n : Nat),
        lo = .lit (.int 0) ∧ hi = .lit (.uintLit w n))
    -- The runtime-bound arm fires when
    -- `lo = .lit (.int 0)` and `impBoundToSExpr hi` succeeds; exclude it.
    (h_not_runtime : impBoundToSExpr hi = none) :
    haxToLowCT (.forFold v lo hi body) = none := by
  unfold haxToLowCT
  -- Eliminate the two productive literal-bounded sub-cases via the guards.
  cases lo with
  | lit l0 =>
    cases l0 with
    | int n0 =>
      by_cases hn0 : n0 = 0
      · subst hn0
        cases hi with
        | lit l1 =>
          cases l1 with
          | int n =>
            by_cases hn : n ≥ 0
            · exact absurd ⟨n, rfl, rfl, hn⟩ h_not_lit
            · simp [hn]
          | uintLit w n => exact absurd ⟨w, n, rfl, rfl⟩ h_not_uint
          | _ => simp [h_not_runtime]
        | _ => simp [h_not_runtime]
      -- `n0 ≠ 0`: the offset-start arms require a convertible bound
      -- (`impLitNat hi` on the literal side implies `impBoundToSExpr hi`
      -- succeeds), so `h_not_runtime` rules every productive case out.
      · cases hi with
        | lit l1 =>
          cases l1 with
          | int m =>
            by_cases hm : m ≥ 0
            · simp [impBoundToSExpr, hm] at h_not_runtime
            · cases hl : impLitNat (.int n0) <;> simp_all [impLitNat]
          | uintLit _ _ => simp [impBoundToSExpr] at h_not_runtime
          | sintLit _ m =>
            by_cases hm : m ≥ 0
            · simp [impBoundToSExpr, hm] at h_not_runtime
            · cases hl : impLitNat (.int n0) <;> simp_all [impLitNat]
          | bool _ => cases hl : impLitNat (.int n0) <;> simp_all [impLitNat]
          | unit => cases hl : impLitNat (.int n0) <;> simp_all [impLitNat]
        | _ => cases hl : impLitNat (.int n0) <;> simp_all
    | uintLit w n =>
      cases hi with
      | lit l1 =>
        cases l1 with
        | int m =>
          by_cases hm : m ≥ 0
          · simp [impBoundToSExpr, hm] at h_not_runtime
          · simp [impLitNat, hm]
        | uintLit _ _ => simp [impBoundToSExpr] at h_not_runtime
        | sintLit _ m =>
          by_cases hm : m ≥ 0
          · simp [impBoundToSExpr, hm] at h_not_runtime
          · simp [impLitNat, hm]
        | bool _ => simp [impLitNat]
        | unit => simp [impLitNat]
      | _ => simp [impLitNat, h_not_runtime]
    | sintLit w n =>
      cases hi with
      | lit l1 =>
        cases l1 with
        | int m =>
          by_cases hm : m ≥ 0
          · simp [impBoundToSExpr, hm] at h_not_runtime
          · cases hl : impLitNat (.sintLit w n) <;> simp_all [impLitNat]
        | uintLit _ _ => simp [impBoundToSExpr] at h_not_runtime
        | sintLit _ m =>
          by_cases hm : m ≥ 0
          · simp [impBoundToSExpr, hm] at h_not_runtime
          · cases hl : impLitNat (.sintLit w n) <;> simp_all [impLitNat]
        | bool _ => cases hl : impLitNat (.sintLit w n) <;> simp_all [impLitNat]
        | unit => cases hl : impLitNat (.sintLit w n) <;> simp_all [impLitNat]
      | _ => cases hl : impLitNat (.sintLit w n) <;> simp_all
    | bool b =>
      cases hi with
      | lit l1 => simp [impLitNat]
      | _ => simp [impLitNat, h_not_runtime]
    | unit =>
      cases hi with
      | lit l1 => simp [impLitNat]
      | _ => simp [impLitNat, h_not_runtime]
  | _ => rfl

/-- `haxToLowCT` rejects a `forFoldRev` whose bounds are not both literals. -/
theorem haxToLowCT_forFoldRev_eq_none (v : String) (lo hi body : ImpExpr)
    (h : ¬ ∃ l1 l2 : Hax.ImpLit, lo = .lit l1 ∧ hi = .lit l2) :
    haxToLowCT (.forFoldRev v lo hi body) = none := by
  cases lo with
  | lit l1 =>
    cases hi with
    | lit l2 => exact absurd ⟨l1, l2, rfl, rfl⟩ h
    | _ => simp [haxToLowCT]
  | _ => simp [haxToLowCT]

/-- `haxToLowCT` rejects a `whileFold` whose guard is not a variable. -/
theorem haxToLowCT_whileFold_eq_none (cond body : ImpExpr) (h : ∀ v, cond ≠ .var v) :
    haxToLowCT (.whileFold cond body) = none := by
  cases cond with
  | var v => exact absurd rfl (h v)
  | _ => simp [haxToLowCT]

theorem haxToLowCT_forFoldReturn_eq_none
    (v : String) (lo hi body : ImpExpr) :
    haxToLowCT (.forFoldReturn v lo hi body) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_forFoldRevReturn_eq_none
    (v : String) (lo hi body : ImpExpr) :
    haxToLowCT (.forFoldRevReturn v lo hi body) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_whileFoldReturn_eq_none
    (cond body : ImpExpr) :
    haxToLowCT (.whileFoldReturn cond body) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_cfBreak_eq_none (e : ImpExpr) :
    haxToLowCT (.cfBreak e) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_cfContinue_eq_none (e : ImpExpr) :
    haxToLowCT (.cfContinue e) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_cfBreakContinue_eq_none (e : ImpExpr) :
    haxToLowCT (.cfBreakContinue e) = none := by
  simp [haxToLowCT]

/-! ## §5.5  Unreachable-arm simulation instances

Each of these is a `HaxToLowCTSimulates` instance whose closure
follows from the corresponding `haxToLowCT_*_eq_none` lemma —
the translation hypothesis collapses to `none = some c`, which is
`False`.

These cover every `ImpExpr` constructor for which `haxToLowCT`
returns `none`.  Once the structural cases close, these instances
plug directly into the dispatcher. -/

theorem haxToLowCT_simulates_lit
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (l : ImpLit) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.lit l) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_lit_top_eq_none] at h
  contradiction

/-- `tuple` simulation.  The productive shape is the all-`var` tuple
    tail: it lowers to `RSkip`, the source-side evaluation leaves the
    env unchanged (`evalImp_tuple_vars_inv`), so `rs' = rs` closes
    agreement.  Non-`var` tuples contradict the translation
    hypothesis. -/
theorem haxToLowCT_simulates_tuple
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (elems : List ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.tuple elems) c env env' rs v := by
  intro hHax hEval hAgree
  by_cases hAll : elems.all isVar = true
  · rw [haxToLowCT_tuple_of_vars elems hAll] at hHax
    cases hHax
    have henv := evalImp_tuple_vars_inv bi fuel elems env v env' hAll hEval
    subst henv
    exact ⟨rs, RustExec.skip rs, hAgree⟩
  · rw [haxToLowCT_tuple_eq_none_of_not_all_vars elems hAll] at hHax
    contradiction

theorem haxToLowCT_simulates_borrow
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.borrow e) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_borrow_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_break
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (m : Option ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.break_ m) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_break_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_continue
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec .continue_ c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_continue_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_earlyReturn
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.earlyReturn e) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_earlyReturn_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_questionMark
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.questionMark e) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_questionMark_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_proj
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (i : Nat) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.proj e i) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_proj_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_deref
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.deref e) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_deref_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_forLoop
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (var : String) (lo hi body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.forLoop var lo hi body) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_forLoop_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_forLoopRev
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (var : String) (lo hi body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.forLoopRev var lo hi body) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_forLoopRev_eq_none] at h
  contradiction

/-- Source-side: `.forFold` is a post-phase constructor whose `denote`
    always yields `Outcome.err`, so `evalImp` returns `none`.

    This closes the literal-bounded forFold simulation cases:
    although the translator produces `some (.RFor ..)` for the two
    literal shapes, the source-side evaluation hypothesis is vacuous, and
    the simulation conclusion follows by `False.elim`. -/
theorem evalImp_forFold_eq_none (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi body : ImpExpr) (env : Env) :
    evalImp bi fuel (.forFold var lo hi body) env = none := by
  unfold evalImp denote
  simp only [pure, Pure.pure, StateT.pure, StateT.run]

/-- `denote` gives `forFoldRev` no meaning, so `evalImp` returns `none`. -/
theorem evalImp_forFoldRev_eq_none (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi body : ImpExpr) (env : Env) :
    evalImp bi fuel (.forFoldRev var lo hi body) env = none := by
  unfold evalImp denote
  simp only [pure, Pure.pure, StateT.pure, StateT.run]

/-- `denote` gives `whileFold` no meaning, so `evalImp` returns `none`. -/
theorem evalImp_whileFold_eq_none (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) (env : Env) :
    evalImp bi fuel (.whileFold cond body) env = none := by
  unfold evalImp denote
  simp only [pure, Pure.pure, StateT.pure, StateT.run]

theorem haxToLowCT_simulates_forFoldReturn
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (var : String) (lo hi body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.forFoldReturn var lo hi body) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_forFoldReturn_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_forFoldRevReturn
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (var : String) (lo hi body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.forFoldRevReturn var lo hi body) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_forFoldRevReturn_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_whileFoldReturn
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (cond body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.whileFoldReturn cond body) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_whileFoldReturn_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_cfBreak
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.cfBreak e) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_cfBreak_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_cfContinue
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.cfContinue e) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_cfContinue_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_cfBreakContinue
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.cfBreakContinue e) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_cfBreakContinue_eq_none] at h
  contradiction

/-! ## §6  Summary

* §1 Agreement predicate (scalar-only)
* §2 `evalImp` (in `ImpEval`)
* §3 Main theorem statement as `def HaxToLowCTSimulates`
* §4 Per-case LowCT-side structural lemmas:
  * `rustExec_RSkip_refl` (var / unitVal)
  * `rustExec_RSeq_chain` (seq)
  * `rustExec_RLetU64Zero_ScalarSet` (lit-let; uses `rsSetScalar_collapse`)
  * `rustExec_RIfNz_dispatch_{true,false}` (if dispatcher)
* §5 + §5.5: per-constructor
  `haxToLowCT_*_eq_none` lemmas + `haxToLowCT_simulates_*` instances
  covering every ImpExpr constructor that `haxToLowCT` rejects (`lit`,
  `proj`, `borrow`, `deref`, `forLoop`/`forLoopRev`,
  `forFold`/`forFoldRev`, `forFoldReturn`/`forFoldRevReturn`,
  `whileFold`/`whileFoldReturn`, `break_`, `continue_`, `earlyReturn`,
  `questionMark`, `cfBreak`/`cfContinue`/`cfBreakContinue`).
* `tuple` closes productively: the all-`var` tuple tail lowers to
  `RSkip` with env and state unchanged (`haxToLowCT_simulates_tuple`
  via `evalImp_tuple_vars_inv`); non-`var` tuples contradict.
* `var`, `unitVal`: `haxToLowCT_simulates_{var,unitVal}` via
  `evalImp_{var,unitVal}_inv`, by induction with `ImpExpr.ind`
  (hax-lean `HaxLean/AST.lean`).
* `seq`: `haxToLowCT_simulates_seq` via `evalImp_seq_inv` and
  `haxToLowCT_seq_some`, threading sub-IHs through
  `rustExec_RSeq_chain`.
* `letBind lit`: the source-side inverse `evalImp_letBind_lit_inv` (in `ImpEval`);
  the simulation instance, which also uses
  `envAgreesRust_extend_scalar`, is in `HaxToLowCTSim_Agreement.lean`.
* The remaining productive cases are in the `HaxToLowCTSim_*` modules
  listed in the header.
-/

/-! ## §7  Source-side decomposition: `seq` -/

/-- Inverse: if `evalImp` on `.seq a b` succeeds, then `a` produces some
    value `vA` with mid-env `env_mid`, and `b` then produces `v` from
    `env_mid` ending at `env'`. -/
theorem evalImp_seq_inv (bi : Builtins) (fuel : Nat) (a b : ImpExpr)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.seq a b) env = some (v, env')) :
    ∃ vA env_mid, evalImp bi fuel a env = some (vA, env_mid) ∧
                  evalImp bi fuel b env_mid = some (v, env') := by
  unfold evalImp at h ⊢
  -- Unfold the .seq case of denote
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure] at h
  -- Case-split on what `denote bi fuel a env` returns
  cases hA : denote bi fuel a env with
  | mk oA emA =>
    rw [hA] at h
    -- Now case-split on the outcome oA
    cases oA with
    | val vA =>
      refine ⟨vA, emA, ?_, ?_⟩
      · show (match denote bi fuel a env with
                | (Outcome.val v, env') => some (v, env')
                | _ => none) = some (vA, emA)
        rw [hA]
      · show (match (denote bi fuel b).run emA with
                | (Outcome.val v, env') => some (v, env')
                | _ => none) = some (v, env')
        exact h
    | earlyRet w => simp [StateT.pure] at h
    | broke w => simp [StateT.pure] at h
    | continued => simp [StateT.pure] at h
    | err msg => simp [StateT.pure] at h

/-! ## §8  `seq` simulation -/

/-- `haxToLowCT` reduces on `.seq a b` to `some c` iff both
    sub-translations succeed and `c` is their `.RSeq`. -/
theorem haxToLowCT_seq_some (a b : ImpExpr) (c : LowCT)
    (h : haxToLowCT (.seq a b) = some c) :
    ∃ aC bC, haxToLowCT a = some aC ∧ haxToLowCT b = some bC ∧
              c = .RSeq aC bC := by
  unfold haxToLowCT at h
  cases hA : haxToLowCT a with
  | none => rw [hA] at h; simp at h
  | some aC =>
    cases hB : haxToLowCT b with
    | none => rw [hA, hB] at h; simp at h
    | some bC =>
      rw [hA, hB] at h
      simp at h
      exact ⟨aC, bC, rfl, rfl, h.symm⟩

/-- `seq` simulation: combine IH on `a` and `b`. -/
theorem haxToLowCT_simulates_seq
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (a b : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value)
    (iha : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulates bi fuel N leafSpec a c' env_a env_b rs_a v_a)
    (ihb : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulates bi fuel N leafSpec b c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulates bi fuel N leafSpec (.seq a b) c env env' rs v := by
  intro hHax hEval hAgree
  -- Unpack the syntactic translation
  obtain ⟨aC, bC, hAtrans, hBtrans, hC⟩ := haxToLowCT_seq_some a b c hHax
  subst hC
  -- Unpack the source-side evaluation via the seq inverse
  obtain ⟨vA, env_mid, hAeval, hBeval⟩ :=
    evalImp_seq_inv bi fuel a b env v env' hEval
  -- Apply IH on `a` to get rs_mid
  obtain ⟨rs_mid, hAexec, hAgreeMid⟩ :=
    iha aC env env_mid rs vA hAtrans hAeval hAgree
  -- Apply IH on `b` to get rs'
  obtain ⟨rs', hBexec, hAgree'⟩ :=
    ihb bC env_mid env' rs_mid v hBtrans hBeval hAgreeMid
  -- Combine via RSeq
  exact ⟨rs', rustExec_RSeq_chain N leafSpec aC bC rs rs_mid rs' hAexec hBexec,
         hAgree'⟩

end CatCrypt.Crypto.Hax
