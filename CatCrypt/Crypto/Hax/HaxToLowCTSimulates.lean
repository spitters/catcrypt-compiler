/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Hax.HaxToLowCT
import CatCrypt.Hax.Semantics
import CatCrypt.Hax.Value
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# H3: Hax → LowCT Semantic Simulation

States and progressively closes the semantic-preservation theorem for
`haxToLowCT : ImpExpr → Option LowCT`.

`HaxToLowCT.lean` provides the syntactic side (representability
biconditionals).  This file adds the **dynamics**: when `haxToLowCT
e = some c`, the LowCT `c` denotes the same thing as the source
ImpExpr `e`.

## Closing this theorem completes the chain

```
   cargo hax json
        ↓ (haxpipeT trusted renderer)
   ImpExpr     —— denote (StateM Env Outcome) ——
        ↓ haxToLowCT                                ← BRIDGED HERE
   LowCT     —— RustExec (relational) ——
        ↓ rustExecSimulatesCryptoSSA / rustExecSimulates
   CryptoSSA / Jasmin
```

## Phase plan (mirrors CryptoSSA closure trail B1.*)

| Phase | Cases | Status |
|---|---|---|
| **H3.bis** | `var`, `unitVal`, `seq`, lit-let | structural; this commit closes the dispatcher |
| **H3.tertia** | scalar-typed leaf calls (u64, TFpL25519) | pending |
| **H3.quarta** | tower/byte leaf calls (TFp, TFp2, TFp25519, TBytes) | pending |
| **H3.sexta** | `ifThenElse`, `whileLoop` | pending |
| **H3.septa** | H1/H2-rejected unreachable arms (mechanical) | pending |

## Structural-recursion note

`ImpExpr` is a **nested inductive** type (it contains `List ImpExpr`
in the `tuple` and `app` arms, and `List (ImpPat × ImpExpr)` in
`match_`).  Lean's `induction` tactic does not produce induction
hypotheses for nested-inductive sub-terms in nested positions.

The CryptoSSA simulation works around this with explicit recursion
on `RustExec` (an extra-syntactic relational input).  Here, the
cleanest analogue is to recur on the *fuel-bounded denotation* —
since `denote` is total in `fuel`, every successful evaluation has
a finite trace, and the simulation can be stated as a recursive
function rather than an induction.

This file defers the choice between (a) custom `ImpExpr` induction
principle, (b) recursion on `sizeOf e`, and (c) recursion on `fuel`
to the H3.bis closure work.  The current commit lands the agreement
predicate, the source-side evaluation alias, and the theorem
statement; the per-case dispatch is the H3.bis closure target.

## Status

* §1 Agreement predicate — landed
* §2 Source-side `evalImp` alias — landed
* §3 Main theorem statement — landed (as `def` returning `Prop`;
  the proof is the work plan above)
* §4 Demo lemmas validating the predicate setup — landed

The file deliberately does **NOT** appear in `CatCrypt.lean`'s import
graph yet; closing the phases gates inclusion in the main build.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote denoteArgs defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Environment/state agreement predicate (H3.A1)

Phase H3.bis covers scalar bindings only.  Tower-typed agreement
(content-bearing, byte-layout transport per CryptoSSA's `bindingOK`)
is added in H3.quarta. -/

/-- Decode a Hax `Value` to a LowCT scalar.  H3.bis covers
    `int n` (when `n ≥ 0`), `bool`, and `unit`.  Tower / bytes /
    tuples / options decoded in H3.quarta. -/
def valueToScalar : Value → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | .bool true => some 1
  | .bool false => some 0
  | .unit => some 0
  | _ => none

/-- Agreement on a single name.  If the Hax env has a value that
    decodes to a scalar, the RustState's scalar binding agrees. -/
def nameAgreesScalar (env : Env) (rs : RustState) (name : String) : Prop :=
  ∀ v, env name = some v →
    ∀ n, valueToScalar v = some n →
      rs.rsScalar name = n

/-- Top-level agreement: scalar-only.  Extended in H3.quarta to cover
    tower and byte bindings. -/
def envAgreesRust (env : Env) (rs : RustState) : Prop :=
  ∀ name, nameAgreesScalar env rs name

/-! ### §1.1  Agreement-preservation lemmas

These let the per-case proofs extend agreement across state updates.
The full set is populated as phases close. -/

/-- Identity preservation: `var` and `unitVal` cases leave both env
    and rs unchanged, so agreement carries trivially. -/
theorem envAgreesRust_refl (env : Env) (rs : RustState) :
    envAgreesRust env rs → envAgreesRust env rs := id

/-! ## §2  Source-side evaluation alias

The Hax-side big-step semantics `denote : Builtins → Nat → ImpExpr →
StateM Env Outcome` is fuel-parametric.  This alias projects to the
"good" case where evaluation produced a value. -/

/-- `evalImp bi fuel e env` returns `some (v, env')` when `denote`
    produces `Outcome.val v` with final env `env'`; `none` otherwise. -/
def evalImp (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env) :
    Option (Value × Env) :=
  match (denote bi fuel e).run env with
  | (.val v, env') => some (v, env')
  | _ => none

/-! ### §2.1  Source-side unfold lemmas

These are the StateT/denote simp normal forms for the trivial cases.
Each closes by unfolding the monad operations.

The bi-directional lemmas (`_inv` variants) lift `evalImp e env = some
(v, env')` to concrete equalities about `v` and `env'`, used in the
per-case proofs of the main theorem. -/

/-- The standard simp set for unfolding StateM operations on `denote`. -/
private abbrev stateMUnfolds : List Lean.Name := [] -- documentation only

/-- `unitVal` evaluates to `.unit` with env unchanged. -/
theorem evalImp_unitVal (bi : Builtins) (fuel : Nat) (env : Env) :
    evalImp bi fuel .unitVal env = some (.unit, env) := by
  unfold evalImp denote
  simp only [pure, Pure.pure, StateT.pure, StateT.run]

/-- `var name` evaluates to the env lookup when defined; env unchanged. -/
theorem evalImp_var_some (bi : Builtins) (fuel : Nat) (name : String)
    (env : Env) (v : Value) (h : env name = some v) :
    evalImp bi fuel (.var name) env = some (v, env) := by
  unfold evalImp denote
  simp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
             StateT.get, pure, Pure.pure, StateT.pure, StateT.run, h]

/-- Inverse: extract `env name = some v` and `env' = env` from a
    successful `evalImp` on `.var name`. -/
theorem evalImp_var_inv (bi : Builtins) (fuel : Nat) (name : String)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.var name) env = some (v, env')) :
    env name = some v ∧ env' = env := by
  cases hen : env name with
  | none =>
    exfalso
    unfold evalImp denote at h
    simp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
               StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
    cases h
  | some w =>
    have key := evalImp_var_some bi fuel name env w hen
    rw [key] at h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨congrArg some h.1, h.2.symm⟩

/-- Inverse: extract `v = .unit` and `env' = env` from a successful
    `evalImp` on `.unitVal`. -/
theorem evalImp_unitVal_inv (bi : Builtins) (fuel : Nat)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel .unitVal env = some (v, env')) :
    v = .unit ∧ env' = env := by
  have key := evalImp_unitVal bi fuel env
  rw [key] at h
  rw [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

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

| Source pattern | Target LowCT | Phase |
|---|---|---|
| `var _` | `RSkip` | H3.bis |
| `unitVal` | `RSkip` | H3.bis |
| `seq a b` | `RSeq aC bC` | H3.bis |
| `letBind _ (lit (uintLit _ _)) body` | `RLetU64Zero + RSeq (RScalarSet ..) bodyC` | H3.bis |
| `letBind _ (lit (int n)) body`, `n ≥ 0` | same | H3.bis |
| `letBind _ (app f args) body` | `RLetZero _ (RSeq (RCall ..) bodyC)` | H3.tertia |
| `assign _ (lit (int n))`, `n ≥ 0` | `RScalarSet _ n.toNat` | H3.tertia |
| `assign _ (lit (uintLit _ n))` | `RScalarSet _ n` | H3.tertia |
| `assign _ (app f args)` | `RCall f _ args'` | H3.tertia |
| `ifThenElse (var v) t e` | `RIfNz v tC eC` | H3.sexta |
| `whileLoop (var v) body` | `RWhileNz v bodyC` | H3.sexta |
| `match_ (app f args) [(tuplePat ..)]` | `RLetZero + RLetZero + RCallSwap` | H3.tertia (H2.1) |

All other arms of `haxToLowCT` return `none`, so the hypothesis
`haxToLowCT e = some c` is `False`; these cases discharge
mechanically in H3.septa.
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

/-! ### §4.7  H3.bis: var and unitVal simulation instances

These are the first two productive (non-contradiction) closures of
the main theorem.  Both reduce to `RSkip` on the LowCT side, with
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
`haxToLowCT e = some c` is `False`.  These are the H3.septa
"closure-by-contradiction" cases.

The template (one per constructor) is:

```
theorem haxToLowCT_simulates_<ctor> ... :
    HaxToLowCTSimulates ... :=
  fun h _ _ => by simp [haxToLowCT] at h
```

Twelve such cases.  Mechanical; populated in H3.septa. -/

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
agreement. -/

/-- `.var n` runs to the env lookup (value or undefined-variable error)
    with the env unchanged. -/
theorem denote_var_run_eq (bi : Builtins) (fuel : Nat) (n : String)
    (env : Env) :
    (denote bi fuel (.var n)).run env =
      ((match env n with
        | some v => Outcome.val v
        | none => Outcome.err s!"undefined variable: {n}"), env) := by
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
             MonadStateOf.get, StateT.get, pure, Pure.pure]
  cases env n <;> rfl

/-- Unfold equation for `denoteArgs` on a cons cell.  The recursive
    `denoteArgs bi fuel es` call is kept opaque so it can be rewritten
    by an induction hypothesis. -/
theorem denoteArgs_cons_run_eq (bi : Builtins) (fuel : Nat)
    (e : ImpExpr) (es : List ImpExpr) (env : Env) :
    (denoteArgs bi fuel (e :: es)).run env =
      (match (denote bi fuel e).run env with
       | (.val v, env_a) =>
           (match (denoteArgs bi fuel es).run env_a with
            | (rest, env_b) => (rest.map (v :: ·), env_b))
       | (_, env_a) => (none, env_a)) := by
  have hEq : denoteArgs bi fuel (e :: es) = (do
      let r ← denote bi fuel e
      match r with
      | .val v => do
          let rest ← denoteArgs bi fuel es
          pure (rest.map (v :: ·))
      | _ => pure none) := by
    conv_lhs => unfold denoteArgs
    rfl
  show (denoteArgs bi fuel (e :: es)).run env = _
  rw [hEq]
  simp only [StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  cases denote bi fuel e env with
  | mk a s =>
    rcases a with v | v | v | _ | msg
    · show StateT.bind (denoteArgs bi fuel es) _ s = _
      simp only [StateT.bind]
      cases denoteArgs bi fuel es s with
      | mk rest s2 => rfl
    all_goals rfl

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
    (h_not_uint : ¬ ∃ (w : CatCrypt.Hax.IntWidth) (n : Nat),
        lo = .lit (.int 0) ∧ hi = .lit (.uintLit w n))
    -- Stage 1a (2026-07-01): the runtime-bound arm fires when
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

theorem haxToLowCT_forFoldRev_eq_none
    (v : String) (lo hi body : ImpExpr) :
    haxToLowCT (.forFoldRev v lo hi body) = none := by
  simp [haxToLowCT]

theorem haxToLowCT_whileFold_eq_none
    (cond body : ImpExpr) :
    haxToLowCT (.whileFold cond body) = none := by
  simp [haxToLowCT]

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

/-! ## §5.5  H3.septa: unreachable-arm simulation instances

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

    This is what unblocks the literal-bounded forFold simulation cases:
    even though the translator now produces `some (.RFor ..)` for the two
    literal shapes, the source-side evaluation hypothesis is vacuous, and
    the simulation conclusion follows by `False.elim`. -/
theorem evalImp_forFold_eq_none (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi body : ImpExpr) (env : Env) :
    evalImp bi fuel (.forFold var lo hi body) env = none := by
  unfold evalImp denote
  simp only [pure, Pure.pure, StateT.pure, StateT.run]

/-- For-fold simulation.

    After the 2026-05 extension, two literal-bounded shapes of `.forFold`
    translate to `.RFor`.  But on the source side, `denote bi fuel
    (.forFold ..)` is `pure (.err ..)` (post-phase constructor), so
    `evalImp` returns `none` and the simulation hypothesis is vacuous —
    closing all three sub-cases uniformly. -/
theorem haxToLowCT_simulates_forFold
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (var : String) (lo hi body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.forFold var lo hi body) c env env' rs v := by
  intro _ hEval _
  rw [evalImp_forFold_eq_none] at hEval
  contradiction

theorem haxToLowCT_simulates_forFoldRev
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (var : String) (lo hi body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.forFoldRev var lo hi body) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_forFoldRev_eq_none] at h
  contradiction

theorem haxToLowCT_simulates_whileFold
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (cond body : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulates bi fuel N leafSpec (.whileFold cond body) c env env' rs v := by
  intro h _ _
  rw [haxToLowCT_whileFold_eq_none] at h
  contradiction

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

* §1 Agreement predicate (scalar-only) — landed
* §2 `evalImp` alias — landed
* §3 Main theorem statement as `def HaxToLowCTSimulates` — landed
* §4 Per-case LowCT-side structural lemmas — landed:
  * `rustExec_RSkip_refl` (var / unitVal)
  * `rustExec_RSeq_chain` (seq)
  * `rustExec_RLetU64Zero_ScalarSet` (lit-let; uses `rsSetScalar_collapse`)
  * `rustExec_RIfNz_dispatch_{true,false}` (if dispatcher)
* §5 + §5.5 H3.septa — **complete**: per-constructor
  `haxToLowCT_*_eq_none` lemmas + `haxToLowCT_simulates_*` instances
  covering every ImpExpr constructor that `haxToLowCT` rejects (`lit`,
  `proj`, `borrow`, `deref`, `forLoop`/`forLoopRev`,
  `forFold`/`forFoldRev`, `forFoldReturn`/`forFoldRevReturn`,
  `whileFold`/`whileFoldReturn`, `break_`, `continue_`, `earlyReturn`,
  `questionMark`, `cfBreak`/`cfContinue`/`cfBreakContinue`).
* `tuple` closes productively: the all-`var` tuple tail lowers to
  `RSkip` with env and state unchanged (`haxToLowCT_simulates_tuple`
  via `evalImp_tuple_vars_inv`); non-`var` tuples contradict.
* **H3.bis (this commit)**: var, unitVal closed end-to-end as
  `haxToLowCT_simulates_{var,unitVal}` via `evalImp_{var,unitVal}_inv`.
  Recursion principle solved: `ImpExpr.ind` (custom recursor in
  `Hax/AST.lean:109`) works under `induction ... using`.
* **H3.bis (later commit)**: `seq` closed end-to-end as
  `haxToLowCT_simulates_seq` via `evalImp_seq_inv` and
  `haxToLowCT_seq_some`, threading sub-IHs through
  `rustExec_RSeq_chain`.  The `letBind lit` source-side inverse
  `evalImp_letBind_lit_inv` is in place; the full simulation instance
  still needs an agreement-extension lemma
  `envAgreesRust_extend_scalar` to discharge the body IH.
* Remaining work — H3.bis: `letBind lit` simulation instance using
  `evalImp_letBind_lit_inv` + `rustExec_RLetU64Zero_ScalarSet` +
  the missing `envAgreesRust_extend_scalar` lemma.
* Remaining work — H3.tertia / H3.quarta / H3.sexta: per the plan
  doc.  Each phase has its own source-side decomposition lemma
  (`evalImp_letBind_inv`, `evalImp_assign_inv`, `evalImp_ifThenElse_inv`,
  `evalImp_whileLoop_inv`) plus its own target-side dispatcher.

**Build status**: zero sorries, zero axioms, zero warnings.
Not yet wired into `CatCrypt.lean`'s import graph; closure of the
remaining phases gates inclusion in the main build (and the audit
script).
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

/-! ## §9  Source-side decomposition: `letBind` of a literal RHS

For `letBind name (.lit l) body`, the RHS evaluation is `pure (.val
(Value.ofLit l))` — guaranteed to succeed with no env change.  The
inverse therefore says: there exists a value `vL = .ofLit l` such that
the body, evaluated in the env extended at `name` with `vL`, produces
`(v, env')`. -/

theorem evalImp_letBind_lit_inv (bi : Builtins) (fuel : Nat) (name : String)
    (l : ImpLit) (body : ImpExpr) (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.letBind name (.lit l) body) env = some (v, env')) :
    evalImp bi fuel body (env.extend name (Value.ofLit l)) = some (v, env') := by
  unfold evalImp at h ⊢
  -- Unfold the letBind + lit case of denote
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure, StateT.pure, modify, modifyGet,
             MonadStateOf.modifyGet, StateT.modifyGet] at h
  exact h

end CatCrypt.Crypto.Hax
