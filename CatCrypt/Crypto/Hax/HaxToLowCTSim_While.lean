/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates

/-!
# whileLoop simulation case

Handles `.whileLoop (.var cond) body` arm of `haxToLowCT`,
which produces `RWhileNz cond bodyC` on the LowCT side.

The Hax-side `denote` uses an auxiliary `denoteWhile bi fuel cond
body` (declared `mutual` with `denote`).  The LowCT-side uses
`RustExec.whileTrue` (recursive iteration) / `whileFalse` (exit).

The recursion correspondence: Hax `fuel` decrements per loop iteration;
LowCT `N` is a fuel parameter on the relation (interpreted as max
iterations).  The simulation must align these.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote denoteWhile defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Syntactic unpacker for the `whileLoop (.var cond) body` arm -/

/-- `haxToLowCT` reduces on `.whileLoop (.var cond) body` to `some c`
    iff the body sub-translation succeeds and `c = .RWhileNz cond bC`. -/
theorem haxToLowCT_whileLoop_var_some
    (cond : String) (body : ImpExpr) (c : LowCT)
    (h : haxToLowCT (.whileLoop (.var cond) body) = some c) :
    ∃ bC, haxToLowCT body = some bC ∧ c = .RWhileNz cond bC := by
  unfold haxToLowCT at h
  cases hB : haxToLowCT body with
  | none => rw [hB] at h; simp at h
  | some bC =>
    rw [hB] at h
    simp at h
    exact ⟨bC, rfl, h.symm⟩

/-! ## §2  Source-side: the fuel-zero whileLoop case is degenerate

`denoteWhile bi 0 cond body = pure (.err "out of fuel")` — at fuel = 0
the loop helper immediately returns an error outcome, so `evalImp` on
`.whileLoop _ _` returns `none`.  Therefore any hypothesis claiming a
successful evaluation at fuel = 0 is `False`. -/

theorem evalImp_whileLoop_var_fuel_zero_inv
    (bi : Builtins) (cond : String) (body : ImpExpr)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi 0 (.whileLoop (.var cond) body) env = some (v, env')) :
    False := by
  -- Unfold `evalImp`, then the `.whileLoop` arm of `denote`,
  -- then `denoteWhile` at fuel = 0.
  unfold evalImp at h
  simp only [denote] at h
  unfold denoteWhile at h
  simp only [pure, Pure.pure, StateT.run] at h
  cases h

/-! ## §3  Agreement bridge: `bool` value ⇒ scalar 0/1

When the agreement predicate holds and `env cond = some (.bool b)`,
the LowCT scalar slot `cond` is `1` (b = true) or `0` (b = false). -/

theorem envAgreesRust_bool_to_scalar
    (env : Env) (rs : RustState) (cond : String) (b : Bool)
    (hAgree : envAgreesRust env rs) (hEnv : env cond = some (.bool b)) :
    rs.rsScalar cond = if b then 1 else 0 := by
  have := hAgree cond (.bool b) hEnv
  cases b with
  | true  =>
    simpa using this 1 (by simp [valueToScalar])
  | false =>
    simpa using this 0 (by simp [valueToScalar])

/-! ## §4  Source-side step inverse (false-arm only)

A weaker partial inverse: if `evalImp` succeeds on `.whileLoop (.var
cond)` and `env cond = some (.bool false)`, the result is the trivial
exit `(.unit, env)`.

This is enough to discharge the *exit* arm of the inductive step
in §5 below; the *iterate* arm requires the full multi-way step
inverse described in the TODO. -/

theorem evalImp_whileLoop_var_false_exit
    (bi : Builtins) (n : Nat) (cond : String) (body : ImpExpr)
    (env : Env) (v : Value) (env' : Env)
    (hEnv : env cond = some (.bool false))
    (h : evalImp bi (n+1) (.whileLoop (.var cond) body) env
           = some (v, env')) :
    v = .unit ∧ env' = env := by
  unfold evalImp at h
  simp only [denote] at h
  unfold denoteWhile at h
  simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
             StateT.bind, denote, get, getThe, MonadStateOf.get,
             StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hEnv] at h
  rw [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-! ## §5  Source-side step inverse (true-arm, .val body outcome)

If `evalImp` succeeds on `.whileLoop (.var cond)` with `env cond = some
(.bool true)` and the body's `denote` outcome is `.val vB` at some
mid-env `env_mid`, then the loop result equals the result of recursing
on `evalImp ... n` from `env_mid`.

This handles the "normal" iterate case.  The `.continued` / `.broke v`
arms of the body are not covered by this lemma — they require a more
general form, deferred to the TODO. -/

theorem evalImp_whileLoop_var_true_iterate
    (bi : Builtins) (n : Nat) (cond : String) (body : ImpExpr)
    (env : Env) (v : Value) (env' : Env) (vB : Value) (env_mid : Env)
    (hEnv : env cond = some (.bool true))
    (hBody : denote bi (n+1) body env = (.val vB, env_mid))
    (h : evalImp bi (n+1) (.whileLoop (.var cond) body) env
           = some (v, env')) :
    evalImp bi n (.whileLoop (.var cond) body) env_mid = some (v, env') := by
  unfold evalImp at h ⊢
  simp only [denote] at h
  unfold denoteWhile at h
  simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
             StateT.bind, denote, get, getThe, MonadStateOf.get,
             StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hEnv,
             hBody] at h
  -- Now `h` has `denoteWhile bi n (.var cond) body` applied to `env_mid`.
  -- Bridge the dispatch: `denote bi n (.whileLoop ..) = denoteWhile bi n ..`
  simp only [denote]
  exact h

/-! ## §6  Combined source-side step inverse

Combines the exit and (.val-arm) iterate lemmas, plus the fuel-zero
exclusion, into a single dichotomy.  This is the form consumed by
the inductive step of the main simulation.

The cases `.continued` / `.broke` in the body outcome are *excluded*
— for the source programs `haxToLowCT` accepts (`AnfShaped`
bodies), control-flow constructors inside the loop body would have
been rejected by H1/H2, so this restriction does not lose generality.
Closing the case where they fire formally requires a syntactic
absence-of-break lemma (TODO §7). -/

/-- If a `whileLoop` evaluation succeeds, either we exited immediately
    (cond false) or we ran one iteration (body returned a value) and
    recursed at decremented fuel.  Excludes `.continued` / `.broke v`
    body outcomes — see comment above. -/
theorem evalImp_whileLoop_var_step_inv_valArm
    (bi : Builtins) (n : Nat) (cond : String) (body : ImpExpr)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi (n+1) (.whileLoop (.var cond) body) env
           = some (v, env'))
    (hBodyShape : ∀ env_a, ∃ vB env_b, denote bi (n+1) body env_a = (.val vB, env_b)) :
    (env cond = some (.bool false) ∧ v = .unit ∧ env' = env)
  ∨ (∃ vB env_mid, env cond = some (.bool true) ∧
       denote bi (n+1) body env = (.val vB, env_mid) ∧
       evalImp bi n (.whileLoop (.var cond) body) env_mid
         = some (v, env')) := by
  -- We split on `env cond` to determine which arm fires.
  cases hen : env cond with
  | none =>
    -- `denote` returns `.err`, so `evalImp` is `none`, contradiction.
    exfalso
    unfold evalImp at h
    simp only [denote] at h
    unfold denoteWhile at h
    simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
               StateT.bind, denote, get, getThe, MonadStateOf.get,
               StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
    cases h
  | some w =>
    cases w with
    | int _ =>
      exfalso
      unfold evalImp at h
      simp only [denote] at h
      unfold denoteWhile at h
      simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
                 StateT.bind, denote, get, getThe, MonadStateOf.get,
                 StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
      cases h
    | bool b =>
      cases b with
      | false =>
        left
        obtain ⟨hv, henv⟩ :=
          evalImp_whileLoop_var_false_exit bi n cond body env v env' hen h
        exact ⟨rfl, hv, henv⟩
      | true =>
        right
        obtain ⟨vB, env_mid, hBody⟩ := hBodyShape env
        refine ⟨vB, env_mid, rfl, hBody, ?_⟩
        exact evalImp_whileLoop_var_true_iterate bi n cond body env v env'
          vB env_mid hen hBody h
    | uint _ _ | sint _ _ | array _ =>
      exfalso
      unfold evalImp at h
      simp only [denote] at h
      unfold denoteWhile at h
      simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
                 StateT.bind, denote, get, getThe, MonadStateOf.get,
                 StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
      cases h
    | unit =>
      exfalso
      unfold evalImp at h
      simp only [denote] at h
      unfold denoteWhile at h
      simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
                 StateT.bind, denote, get, getThe, MonadStateOf.get,
                 StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
      cases h
    | tuple _ =>
      exfalso
      unfold evalImp at h
      simp only [denote] at h
      unfold denoteWhile at h
      simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
                 StateT.bind, denote, get, getThe, MonadStateOf.get,
                 StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
      cases h
    | option _ =>
      exfalso
      unfold evalImp at h
      simp only [denote] at h
      unfold denoteWhile at h
      simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
                 StateT.bind, denote, get, getThe, MonadStateOf.get,
                 StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
      cases h
    | result _ _ =>
      exfalso
      unfold evalImp at h
      simp only [denote] at h
      unfold denoteWhile at h
      simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
                 StateT.bind, denote, get, getThe, MonadStateOf.get,
                 StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
      cases h
    | controlFlow _ _ =>
      exfalso
      unfold evalImp at h
      simp only [denote] at h
      unfold denoteWhile at h
      simp only [Nat.add_one_ne_zero, if_false, bind, Bind.bind,
                 StateT.bind, denote, get, getThe, MonadStateOf.get,
                 StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
      cases h

/-! ## §7  Main simulation: `whileLoop (.var cond) body`

The main theorem closes the whileLoop case under an extra
hypothesis `hBodyAlwaysVal`: at every reachable env, the body's `denote`
outcome is `.val _` (no `.broke` / `.continued` / `.earlyRet` / `.err`).

This restriction is consistent with the syntactic shape `haxToLowCT`
accepts: `AnfShaped` bodies (cf. `HaxToLowCT.lean` §3.4) cannot
contain `break_` / `continue_` / `earlyReturn` constructors, so for
*well-shaped* source programs the body always falls through with a
value.  Removing the `hBodyAlwaysVal` hypothesis requires a
syntactic-absence-of-control-flow lemma (TODO §8 below). -/

/-- Main simulation for the `whileLoop` case.

    The `ihBody` / `hBodyAlwaysVal` hypotheses are quantified over fuel
    so they can be applied at each iteration of the loop. -/
theorem haxToLowCT_simulates_whileLoop_var
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (cond : String) (body : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (ihBody : ∀ f c' env_a env_b rs_a v_a,
                HaxToLowCTSimulates bi f N leafSpec body c' env_a env_b rs_a v_a)
    (hBodyAlwaysVal : ∀ f env_a,
        ∃ vB env_b, denote bi f body env_a = (.val vB, env_b)) :
    HaxToLowCTSimulates bi fuel N leafSpec
      (.whileLoop (.var cond) body) c env env' rs v := by
  intro hHax hEval hAgree
  -- Unpack the syntactic translation.
  obtain ⟨bC, hBtrans, hC⟩ :=
    haxToLowCT_whileLoop_var_some cond body c hHax
  subst hC
  -- Induct on fuel.
  induction fuel generalizing env env' rs v with
  | zero =>
    -- Fuel 0: hypothesis is False.
    exact absurd hEval
      (fun h => evalImp_whileLoop_var_fuel_zero_inv bi cond body env v env' h)
  | succ n IH =>
    -- Case-split via the combined step inverse.
    rcases evalImp_whileLoop_var_step_inv_valArm bi n cond body env v env'
      hEval (hBodyAlwaysVal (n+1)) with
      ⟨hCondF, hv, henv⟩ | ⟨vB, env_mid, hCondT, hBody, hLoopRec⟩
    · -- Exit case: cond false, no body runs, rs unchanged.
      subst hv; subst henv
      have hScalar : rs.rsScalar cond = 0 := by
        have := envAgreesRust_bool_to_scalar env' rs cond false hAgree hCondF
        simpa using this
      exact ⟨rs, RustExec.whileFalse cond bC rs hScalar, hAgree⟩
    · -- Iterate case: cond true, body runs, then recurse.
      have hScalar : rs.rsScalar cond = 1 := by
        have := envAgreesRust_bool_to_scalar env rs cond true hAgree hCondT
        simpa using this
      -- 1. Apply ihBody to get rs_mid.
      have hEvalBody : evalImp bi (n+1) body env = some (vB, env_mid) := by
        unfold evalImp
        rw [show (denote bi (n+1) body).run env = denote bi (n+1) body env from rfl, hBody]
      obtain ⟨rs_mid, hBodyExec, hAgreeMid⟩ :=
        ihBody (n+1) bC env env_mid rs vB hBtrans hEvalBody hAgree
      -- 2. Apply the outer IH (induction hypothesis) on the smaller fuel.
      obtain ⟨rs', hLoopExec, hAgree'⟩ :=
        IH env_mid env' rs_mid v hLoopRec hAgreeMid
      -- 3. Combine via RustExec.whileTrue.
      refine ⟨rs', RustExec.whileTrue cond bC rs rs_mid rs' 1 hScalar
              (by decide) hBodyExec hLoopExec, hAgree'⟩

/-! ## §8  Remaining work: removing the body-shape hypotheses

The main theorem `haxToLowCT_simulates_whileLoop_var` is closed,
but under two extra hypotheses:

1. **`ihBody` quantified over fuel**: a body simulation IH at every
   fuel.  In the dispatcher (a future top-level induction over `ImpExpr`
   that calls this lemma), this is automatic — the dispatcher's outer
   IH on `body` gives a polymorphic-in-fuel version.

2. **`hBodyAlwaysVal`**: the body's `denote` outcome is always `.val _`
   (never `.broke` / `.continued` / `.earlyRet` / `.err`).

The second hypothesis follows from a syntactic property of the source
program: if `body` does **not** contain `break_`, `continue_`,
`earlyReturn`, or `questionMark` constructors anywhere (which is true
of `AnfShaped` bodies accepted by `haxToLowCT`, cf. §3.4 of
`HaxToLowCT.lean`), then `denote`'s body outcome is restricted to
`.val _` and `.err _`.  Combined with the assumption that the loop
itself succeeded (so no errors propagated), the body outcome is `.val _`.

### Closure path

A future commit can replace `hBodyAlwaysVal` by a syntactic lemma:

```
theorem AnfShaped_denote_val_or_err
    (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env)
    (h : AnfShaped e) :
    (∃ v env', denote bi fuel e env = (.val v, env'))
  ∨ (∃ msg env', denote bi fuel e env = (.err msg, env'))
```

plus a forward-propagation lemma showing that an `.err` body outcome
yields an `.err` loop outcome (so the loop-success hypothesis rules
it out).  Together, these eliminate `hBodyAlwaysVal`.
-/

end CatCrypt.Crypto.Hax
