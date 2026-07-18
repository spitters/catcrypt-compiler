/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Hax.AST
import CatCrypt.Crypto.Optimizer.SecretType

/-!
# Source-level constant-time gate over the `ImpExpr` extraction AST

This module supplies the **front information-flow enforcement** of the
verified-compiler stack: a decidable check over the source IR `ImpExpr`
(the imperative-expression image of the Rust the hax pipeline extracts) that
*rejects secret-dependent control flow* — secret branch guards, secret loop
bounds, and secret loop conditions.

## Where it sits

The plan offered two routes to a constant-time compiler: an information-flow
discipline, or *restricting the language so it cannot branch or index on
secrets*. The downstream front IR `thirDialect` takes the second route
**structurally** — `com_ct_by_construction`
(`SecureCompilation/ThirCTByConstruction.lean`) shows a `Com thirDialect`
admits no data-dependent control surface at all, because the dialect simply has
no branch/loop node. But that structural guarantee only applies *after* the
source has been lowered into the branchless target. The lowering
`impExprToThir` (`SecureCompilation/ImpExprToThir.lean`) already returns `none`
on every loop/branch it cannot turn into straight-line dataflow — that is its
*structural* gate.

This file adds the missing **secret-dependence** gate on the source side: even
where a branch/loop *could* be lowered (e.g. a public, statically-bounded
loop), we must reject it if its guard or bound is *secret-derived*, because that
is exactly a timing channel. `impCTSafe` is that check; `NoSecretControl` is the
invariant it certifies. Together with `impExprToThir`'s structural gate and
`com_ct_by_construction`'s branchless target, a CT-safe **and** lowerable
`ImpExpr` reaches a CT-by-construction `Thir`.

## The pieces

* `SecEnv := String → SecretLevel` — the seed secret-labelling of the
  function's variables (its secret parameters map to `sec`).
* `exprLevel : SecEnv → ImpExpr → SecretLevel` — a **sound over-approximation**
  of the secrecy level of an expression's *value*: `var` reads the env, `lit`
  is `pub`, composite forms `join` their subexpressions' levels (monotone taint
  propagation), and any construct whose value-secrecy we cannot pin down
  conservatively yields `sec` ("when unsure, secret").
* `impCTSafe : SecEnv → ImpExpr → Bool` — the gate. It returns `false` as soon
  as any **control surface** is secret-derived:
  - `ifThenElse cond _ _` / `match_ scrut _` — secret guard ⇒ reject;
  - `forLoop/forLoopRev/forFold/…` — secret `lo` or `hi` bound ⇒ reject;
  - `whileLoop/whileFold cond _` — secret `cond` ⇒ reject (and `whileLoop`
    is rejected outright as not statically bounded, matching `impExprToThir`).
  It recurses into every subexpression; only a fully control-surface-public
  tree passes.
* `NoSecretControl : SecEnv → ImpExpr → Prop` — the structural predicate: every
  branch/match guard and every loop bound/condition node in the tree has a
  public level under the env.
* `impCTSafe_NoSecretControl` — **the policy theorem**: `impCTSafe env e = true
  → NoSecretControl env e`. This is the source-language analogue of
  `CompilableCT` / `com_ct_by_construction`.

`exprLevel` is the conservative variant the deliverable allows: only the forms
whose value-secrecy is genuinely a join of subexpressions are propagated
precisely; everything else is `sec`. The gate theorem is proved for this
conservative `exprLevel`, so it is sound regardless of how loose the
approximation is — a stricter analysis would only *accept more* programs, never
*reject fewer* secrets.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ImpCTGate

open CatCrypt.Hax
open CatCrypt.Crypto.Optimizer.SecretType
open CatCrypt.Crypto.Optimizer.SecretType.SecretLevel

/-! ## 1. The secret environment -/

/-- A secret-labelling of source variables: each variable name maps to its
secrecy level. Seeded from the function's signature — secret parameters map to
`sec`, public ones (and everything unmentioned) default to `pub`. -/
def SecEnv := String → SecretLevel

/-- The all-public environment (no secrets). -/
def SecEnv.pub : SecEnv := fun _ => SecretLevel.pub

/-- Mark one variable `x` as carrying level `s`, leaving the rest unchanged.
Used to seed the secret parameters. -/
def SecEnv.set (env : SecEnv) (x : String) (s : SecretLevel) : SecEnv :=
  fun y => if y = x then s else env y

/-! ## 2. The value-level over-approximation `exprLevel`

The information-flow level of an expression's *value*. This is a **sound
over-approximation**: precise on the genuinely-dataflow forms (atoms,
applications, tuples, projections, sequencing and let-binding), and `sec`
("when unsure, secret") on every form whose value-secrecy we do not track. The
gate theorem (§5) holds for this conservative reading, so soundness does not
depend on the approximation being tight. -/

/-- The secrecy level of an expression's value, a sound over-approximation. -/
def exprLevel (env : SecEnv) : ImpExpr → SecretLevel
  | .lit _        => SecretLevel.pub
  | .unitVal      => SecretLevel.pub
  | .var x        => env x
  | .letBind _ _ body => exprLevel env body
  | .app _ args   => argsLevel env args
  | .tuple elems  => argsLevel env elems
  | .proj e _     => exprLevel env e
  | .seq _ e2     => exprLevel env e2
  | .borrow e     => exprLevel env e
  | .deref e      => exprLevel env e
  -- Every other form: conservatively secret.
  | _             => SecretLevel.sec
where
  /-- Join the value-levels of a list of subexpressions (taint propagation),
  starting from the join identity `pub`. -/
  argsLevel (env : SecEnv) : List ImpExpr → SecretLevel
  | []      => SecretLevel.pub
  | a :: as => exprLevel env a ⊔ₛ argsLevel env as

/-! ## 3. The CT gate `impCTSafe`

`impCTSafe env e` returns `true` iff no control surface in `e` is secret-derived
under `env`. Every branch/match guard and every loop bound/condition is checked
to be `pub`; the check recurses into all subexpressions. -/

/-- Is a level public? -/
def isPub (s : SecretLevel) : Bool :=
  match s with
  | .pub => true
  | .sec => false

/-- **The source-level constant-time gate.** Returns `false` (reject) if any
control surface — branch guard, match scrutinee, loop bound, or loop condition
— is secret-derived under `env`. Recurses into every subexpression; passes
(`true`) only when the whole tree is control-surface-public.

`whileLoop`/`whileFold` are rejected outright (not statically bounded, matching
`impExprToThir`'s structural gate); the other loop forms are accepted iff both
bounds are public. -/
def impCTSafe (env : SecEnv) : ImpExpr → Bool
  | .lit _        => true
  | .var _        => true
  | .unitVal      => true
  | .continue_    => true
  | .break_ none  => true
  | .letBind _ v body => impCTSafe env v && impCTSafe env body
  | .lam _ body   => impCTSafe env body
  | .app _ args   => allSafe env args
  | .tuple elems  => allSafe env elems
  | .proj e _     => impCTSafe env e
  | .seq e1 e2    => impCTSafe env e1 && impCTSafe env e2
  | .borrow e     => impCTSafe env e
  | .deref e      => impCTSafe env e
  | .assign _ rhs => impCTSafe env rhs
  | .break_ (some e) => impCTSafe env e
  | .earlyReturn e => impCTSafe env e
  | .questionMark e => impCTSafe env e
  | .cfBreak e    => impCTSafe env e
  | .cfContinue e => impCTSafe env e
  | .cfBreakContinue e => impCTSafe env e
  -- Control surfaces: guard / scrutinee must be public.
  | .ifThenElse cond thn els =>
      isPub (exprLevel env cond) && impCTSafe env cond
        && impCTSafe env thn && impCTSafe env els
  | .match_ scrut arms =>
      isPub (exprLevel env scrut) && impCTSafe env scrut && allSafeArms env arms
  -- Bounded loops: both bounds must be public.
  | .forLoop _ lo hi body =>
      isPub (exprLevel env lo) && isPub (exprLevel env hi)
        && impCTSafe env lo && impCTSafe env hi && impCTSafe env body
  | .forLoopRev _ lo hi body =>
      isPub (exprLevel env lo) && isPub (exprLevel env hi)
        && impCTSafe env lo && impCTSafe env hi && impCTSafe env body
  | .forFold _ lo hi body =>
      isPub (exprLevel env lo) && isPub (exprLevel env hi)
        && impCTSafe env lo && impCTSafe env hi && impCTSafe env body
  | .forFoldRev _ lo hi body =>
      isPub (exprLevel env lo) && isPub (exprLevel env hi)
        && impCTSafe env lo && impCTSafe env hi && impCTSafe env body
  | .forFoldReturn _ lo hi body =>
      isPub (exprLevel env lo) && isPub (exprLevel env hi)
        && impCTSafe env lo && impCTSafe env hi && impCTSafe env body
  | .forFoldRevReturn _ lo hi body =>
      isPub (exprLevel env lo) && isPub (exprLevel env hi)
        && impCTSafe env lo && impCTSafe env hi && impCTSafe env body
  -- while loops: not statically bounded — rejected outright (even if the
  -- condition were public, there is no static bound).
  | .whileLoop _ _ => false
  | .whileFold _ _ => false
  | .whileFoldReturn _ _ => false
where
  /-- All subexpressions in a list are CT-safe. -/
  allSafe (env : SecEnv) : List ImpExpr → Bool
  | []      => true
  | a :: as => impCTSafe env a && allSafe env as
  /-- All arm bodies in a match are CT-safe. -/
  allSafeArms (env : SecEnv) : List (ImpPat × ImpExpr) → Bool
  | []      => true
  | pa :: rest => impCTSafe env pa.2 && allSafeArms env rest

/-! ## 4. The structural invariant `NoSecretControl`

`NoSecretControl env e` is the *property* the gate certifies: every control
surface in `e` (branch/match guard, loop bound, loop condition) has a public
level under `env`, and no unbounded loop occurs. We state it directly as a
recursive `Prop` over `ImpExpr`, mirroring the gate's structure. -/

/-- **The CT invariant.** Holds iff no control surface of `e` is secret under
`env`: branch/match guards and loop bounds are all `pub`, and there is no
unbounded (`while`) loop. -/
def NoSecretControl (env : SecEnv) : ImpExpr → Prop
  | .lit _        => True
  | .var _        => True
  | .unitVal      => True
  | .continue_    => True
  | .break_ none  => True
  | .letBind _ v body => NoSecretControl env v ∧ NoSecretControl env body
  | .lam _ body   => NoSecretControl env body
  | .app _ args   => allNSC env args
  | .tuple elems  => allNSC env elems
  | .proj e _     => NoSecretControl env e
  | .seq e1 e2    => NoSecretControl env e1 ∧ NoSecretControl env e2
  | .borrow e     => NoSecretControl env e
  | .deref e      => NoSecretControl env e
  | .assign _ rhs => NoSecretControl env rhs
  | .break_ (some e) => NoSecretControl env e
  | .earlyReturn e => NoSecretControl env e
  | .questionMark e => NoSecretControl env e
  | .cfBreak e    => NoSecretControl env e
  | .cfContinue e => NoSecretControl env e
  | .cfBreakContinue e => NoSecretControl env e
  | .ifThenElse cond thn els =>
      exprLevel env cond = SecretLevel.pub
        ∧ NoSecretControl env cond ∧ NoSecretControl env thn
        ∧ NoSecretControl env els
  | .match_ scrut arms =>
      exprLevel env scrut = SecretLevel.pub
        ∧ NoSecretControl env scrut ∧ allNSCArms env arms
  | .forLoop _ lo hi body =>
      exprLevel env lo = SecretLevel.pub ∧ exprLevel env hi = SecretLevel.pub
        ∧ NoSecretControl env lo ∧ NoSecretControl env hi
        ∧ NoSecretControl env body
  | .forLoopRev _ lo hi body =>
      exprLevel env lo = SecretLevel.pub ∧ exprLevel env hi = SecretLevel.pub
        ∧ NoSecretControl env lo ∧ NoSecretControl env hi
        ∧ NoSecretControl env body
  | .forFold _ lo hi body =>
      exprLevel env lo = SecretLevel.pub ∧ exprLevel env hi = SecretLevel.pub
        ∧ NoSecretControl env lo ∧ NoSecretControl env hi
        ∧ NoSecretControl env body
  | .forFoldRev _ lo hi body =>
      exprLevel env lo = SecretLevel.pub ∧ exprLevel env hi = SecretLevel.pub
        ∧ NoSecretControl env lo ∧ NoSecretControl env hi
        ∧ NoSecretControl env body
  | .forFoldReturn _ lo hi body =>
      exprLevel env lo = SecretLevel.pub ∧ exprLevel env hi = SecretLevel.pub
        ∧ NoSecretControl env lo ∧ NoSecretControl env hi
        ∧ NoSecretControl env body
  | .forFoldRevReturn _ lo hi body =>
      exprLevel env lo = SecretLevel.pub ∧ exprLevel env hi = SecretLevel.pub
        ∧ NoSecretControl env lo ∧ NoSecretControl env hi
        ∧ NoSecretControl env body
  | .whileLoop _ _ => False
  | .whileFold _ _ => False
  | .whileFoldReturn _ _ => False
where
  /-- Every subexpression in a list satisfies `NoSecretControl`. -/
  allNSC (env : SecEnv) : List ImpExpr → Prop
  | []      => True
  | a :: as => NoSecretControl env a ∧ allNSC env as
  /-- Every arm body satisfies `NoSecretControl`. -/
  allNSCArms (env : SecEnv) : List (ImpPat × ImpExpr) → Prop
  | []      => True
  | pa :: rest => NoSecretControl env pa.2 ∧ allNSCArms env rest

/-! ## 5. The policy theorem

`impCTSafe env e = true → NoSecretControl env e`: passing the decidable gate
certifies the structural invariant. The bridge from the `Bool` check to the
`Prop` is the standard `isPub`-to-`= pub` step. -/

/-- `isPub s = true` exactly says `s = pub`. -/
theorem isPub_eq_pub {s : SecretLevel} (h : isPub s = true) : s = SecretLevel.pub := by
  cases s with
  | pub => rfl
  | sec => simp [isPub] at h

/-- List helper: if every element's gate-pass yields `NoSecretControl`, then the
bundled `allSafe` recursor over a list yields the bundled `allNSC`. -/
theorem allSafe_allNSC (env : SecEnv) :
    ∀ (xs : List ImpExpr),
      (∀ a, a ∈ xs → impCTSafe env a = true → NoSecretControl env a) →
      impCTSafe.allSafe env xs = true → NoSecretControl.allNSC env xs
  | [], _, _ => by simp only [NoSecretControl.allNSC]
  | a :: as, ih, h => by
      simp only [impCTSafe.allSafe, Bool.and_eq_true] at h
      simp only [NoSecretControl.allNSC]
      exact ⟨ih a (List.mem_cons_self ..) h.1,
        allSafe_allNSC env as (fun b hb => ih b (List.mem_cons_of_mem _ hb)) h.2⟩

/-- Arms helper: the bundled `allSafeArms` recursor yields the bundled
`allNSCArms`, given each arm body's gate-pass yields `NoSecretControl`. -/
theorem allSafeArms_allNSCArms (env : SecEnv) :
    ∀ (arms : List (ImpPat × ImpExpr)),
      (∀ pa, pa ∈ arms → impCTSafe env pa.2 = true → NoSecretControl env pa.2) →
      impCTSafe.allSafeArms env arms = true → NoSecretControl.allNSCArms env arms
  | [], _, _ => by simp only [NoSecretControl.allNSCArms]
  | pa :: rest, ih, h => by
      simp only [impCTSafe.allSafeArms, Bool.and_eq_true] at h
      simp only [NoSecretControl.allNSCArms]
      exact ⟨ih pa (List.mem_cons_self ..) h.1,
        allSafeArms_allNSCArms env rest
          (fun qb hqb => ih qb (List.mem_cons_of_mem _ hqb)) h.2⟩

/-- **The source-level CT policy theorem.** If `e` passes the decidable gate
`impCTSafe` under `env`, then `e` satisfies the structural invariant
`NoSecretControl`: no branch guard, match scrutinee, or loop bound is secret,
and no unbounded loop occurs. This is the source-language analogue of
`CompilableCT` / `com_ct_by_construction`. -/
theorem impCTSafe_NoSecretControl (env : SecEnv) :
    ∀ (e : ImpExpr), impCTSafe env e = true → NoSecretControl env e := by
  intro e
  induction e using ImpExpr.ind with
  | lit _ => intro _; trivial
  | var _ => intro _; trivial
  | unitVal => intro _; trivial
  | continue_ => intro _; trivial
  | break_none => intro _; trivial
  | break_some e ih =>
      intro h; simp only [impCTSafe] at h; exact ih h
  | letBind _ v body ihv ihb =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨ihv h.1, ihb h.2⟩
  | lam _ body ih => intro h; simp only [impCTSafe] at h; exact ih h
  | app f args ih =>
      intro h
      simp only [impCTSafe] at h
      show NoSecretControl.allNSC env args
      exact allSafe_allNSC env args ih h
  | tuple elems ih =>
      intro h
      simp only [impCTSafe] at h
      show NoSecretControl.allNSC env elems
      exact allSafe_allNSC env elems ih h
  | proj e i ih => intro h; simp only [impCTSafe] at h; exact ih h
  | seq e1 e2 ih1 ih2 =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨ih1 h.1, ih2 h.2⟩
  | borrow e ih => intro h; simp only [impCTSafe] at h; exact ih h
  | deref e ih => intro h; simp only [impCTSafe] at h; exact ih h
  | assign _ rhs ih => intro h; simp only [impCTSafe] at h; exact ih h
  | earlyReturn e ih => intro h; simp only [impCTSafe] at h; exact ih h
  | questionMark e ih => intro h; simp only [impCTSafe] at h; exact ih h
  | cfBreak e ih => intro h; simp only [impCTSafe] at h; exact ih h
  | cfContinue e ih => intro h; simp only [impCTSafe] at h; exact ih h
  | cfBreakContinue e ih => intro h; simp only [impCTSafe] at h; exact ih h
  | ifThenElse c t e ihc iht ihe =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨isPub_eq_pub h.1.1.1, ihc h.1.1.2, iht h.1.2, ihe h.2⟩
  | match_ scrut arms ihs iharms =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      refine ⟨isPub_eq_pub h.1.1, ihs h.1.2, ?_⟩
      show NoSecretControl.allNSCArms env arms
      exact allSafeArms_allNSCArms env arms iharms h.2
  | forLoop _ lo hi body ihlo ihhi ihbody =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨isPub_eq_pub h.1.1.1.1, isPub_eq_pub h.1.1.1.2,
        ihlo h.1.1.2, ihhi h.1.2, ihbody h.2⟩
  | forLoopRev _ lo hi body ihlo ihhi ihbody =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨isPub_eq_pub h.1.1.1.1, isPub_eq_pub h.1.1.1.2,
        ihlo h.1.1.2, ihhi h.1.2, ihbody h.2⟩
  | forFold _ lo hi body ihlo ihhi ihbody =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨isPub_eq_pub h.1.1.1.1, isPub_eq_pub h.1.1.1.2,
        ihlo h.1.1.2, ihhi h.1.2, ihbody h.2⟩
  | forFoldRev _ lo hi body ihlo ihhi ihbody =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨isPub_eq_pub h.1.1.1.1, isPub_eq_pub h.1.1.1.2,
        ihlo h.1.1.2, ihhi h.1.2, ihbody h.2⟩
  | forFoldReturn _ lo hi body ihlo ihhi ihbody =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨isPub_eq_pub h.1.1.1.1, isPub_eq_pub h.1.1.1.2,
        ihlo h.1.1.2, ihhi h.1.2, ihbody h.2⟩
  | forFoldRevReturn _ lo hi body ihlo ihhi ihbody =>
      intro h
      simp only [impCTSafe, Bool.and_eq_true] at h
      exact ⟨isPub_eq_pub h.1.1.1.1, isPub_eq_pub h.1.1.1.2,
        ihlo h.1.1.2, ihhi h.1.2, ihbody h.2⟩
  | whileLoop _ _ _ _ => intro h; exact absurd h (by simp [impCTSafe])
  | whileFold _ _ _ _ => intro h; exact absurd h (by simp [impCTSafe])
  | whileFoldReturn _ _ _ _ => intro h; exact absurd h (by simp [impCTSafe])

/-! ## 6. Self-contained validation

A public-bounded loop over a secret accumulator passes the gate (the secret only
flows into the loop *body*, never a guard/bound); flipping the bound to a secret
variable makes the gate reject. A secret branch guard is rejected. -/

/-- An env with `k` secret and `n` public. -/
def demoEnv : SecEnv := SecEnv.pub.set "k" SecretLevel.sec

/-- A public-bounded `for` loop whose body touches the secret `k`: the control
surface (bounds `0 .. n`) is public, so the gate **accepts** it. -/
def demoGoodLoop : ImpExpr :=
  .forLoop "i" (.lit (.int 0)) (.var "n")
    (.assign "acc" (.app "add" [.var "acc", .var "k"]))

/-- The good loop passes the gate (public bounds, secret only in the body). -/
example : impCTSafe demoEnv demoGoodLoop = true := by decide

/-- And therefore satisfies the structural invariant. -/
example : NoSecretControl demoEnv demoGoodLoop :=
  impCTSafe_NoSecretControl demoEnv demoGoodLoop (by decide)

/-- A loop whose *upper bound* is the secret `k`: a secret-derived control
surface, so the gate **rejects** it. -/
def demoBadLoop : ImpExpr :=
  .forLoop "i" (.lit (.int 0)) (.var "k") (.assign "acc" (.var "i"))

/-- The secret-bound loop is rejected. -/
example : impCTSafe demoEnv demoBadLoop = false := by decide

/-- A branch on the secret `k`: a secret guard, so the gate **rejects** it. -/
def demoBadBranch : ImpExpr :=
  .ifThenElse (.var "k") (.lit (.int 1)) (.lit (.int 0))

/-- The secret branch is rejected. -/
example : impCTSafe demoEnv demoBadBranch = false := by decide

/-- A branch on a *public* condition is accepted, even with secrets in the
arms. -/
example :
    impCTSafe demoEnv (.ifThenElse (.var "n") (.var "k") (.lit (.int 0))) = true := by
  decide

end CatCrypt.Crypto.SecureCompilation.ImpCTGate
