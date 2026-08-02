/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import Std.Tactic.BVDecide

/-!
# A rewriting strength-reduction pass for `Com` (real transform)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`StrengthReduce.lean` ships an *analysis-as-labelling* strength reducer whose
`Com → Com` rewrite is the identity (`applyStrengthReduce = fun p _ => p`), so
its preservation theorems are `rfl` and verify nothing about an actual
rewrite. This file supplies what that one avoids: a **structural**
`Com → Com` transform that *rewrites* an `Expr` to a cheaper but
denotationally-equal one, together with a **non-`rfl`** denotation-preservation
proof by induction over the `Com`.

## The transform

The canonical strength reduction is `mul x (const 2) ↝ add x x`: a multiply by
the constant `2` is replaced by a self-add, which on every common ISA is the
cheaper instruction (an `add`/`lea` instead of a general `mul`). Unlike DCE
this is **not** a binding removal — the context is unchanged, there is no de
Bruijn renumbering. It is an `Expr → Expr` rewrite threaded through the `Com`:

```
let y = mul x (const 2)   ↝   let y = add x x
<body>                          <body>
```

The result type of the binding (`t`), the context (`Γ`), and the body are all
untouched; only the bound `Expr` changes. So the transform is a structural map
over the `Com` that replaces, at each `.var`, the bound expression with its
strength-reduced form.

## The proof (not `rfl`)

`Com.var e body` denotes `body.denote (V.extend (e.denote V))`. So rewriting
`e ↝ e'` preserves the whole-program denotation **iff** `e'.denote V = e.denote V`
for every valuation `V`. The lemma

  `srExpr_denote`:  `(srExpr e).denote V = e.denote V`

is the op-equivalence: for the `mul x (const 2)` site it reduces
to the **arithmetic fact** `a * 2 = a + a` over the dialect's value type
(`BitVec`/`Nat`), discharged by `bv_decide` / `ring` / `omega` — **not** by
`rfl`, because `mul`'s denotation (`a * 2`) and `add`'s denotation (`a + a`)
are syntactically distinct terms that agree only by an algebraic law.

`srCom_denote` then threads `srExpr_denote` through the whole `Com` by
induction on the `.var` spine. It is **not** `rfl`: the program changes (a
different op is bound), and the two `Com`s denote equal values only via the
op-equivalence lemma, applied at every binding.

## What is general vs. scoped

* **General:** `srCom` / `srCom_denote` are parametric in a per-`Expr` rewrite
  `rw` together with its denotation-equivalence proof `rw_sound`; the induction
  over the `Com` spine is dialect-agnostic.
* **Concrete:** the worked dialect (`ArithDialect`, ops `const n`, `add`, `mul2`)
  exhibits the real `mul2 x ↝ add x x` rewrite whose soundness
  (`mul2_to_add_sound`) is the non-`rfl` arithmetic identity `2 * a = a + a`.
-/

set_option autoImplicit false
-- Equation/lookup lemmas legitimately do not use every ambient typeclass
-- section variable; silence the section-variable linter rather than thread
-- per-theorem `omit` clauses.
set_option linter.unusedSectionVars false

namespace CatCrypt.Crypto.SecureCompilation.VIR.StrengthReduceReal

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 0. A structural length measure on `Com`

`srCom` / `srCom_denote` map over a `Com`; the context index is fixed here (the
rewrite preserves the context), but to keep the recursion robust under
well-founded fallback we reuse the same plainly-structural length measure as
`DeadCodeElimReal.lean`. -/

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d]

/-- Number of `.var` bindings in a `Com` (a structural `Nat` measure). -/
def comLen {Γ₀ : Ctxt d} {τ₀ : d.Ty} : Com d Γ₀ τ₀ → Nat
  | .ret _      => 0
  | .var _ body => comLen body + 1

/-! ## 1. The generic, denotation-sound `Expr` rewrite carrier

A strength-reduction rewrite is a context/type-preserving map on expressions
`rw : Expr d Γ t → Expr d Γ t`. It is **sound** when it never changes an
expression's denotation. We package the rewrite and its soundness obligation
and prove the `Com`-level preservation once and for all. -/

variable [DialectDenote d]

/-- Map a sound per-`Expr` rewrite over a whole `Com`, rewriting the expression
bound at every `.var`. The context and result type are preserved at every
node, so no re-typing is needed. -/
def srCom (rw : {Γ : Ctxt d} → {t : d.Ty} → Expr d Γ t → Expr d Γ t) :
    {Γ : Ctxt d} → {τ : d.Ty} → Com d Γ τ → Com d Γ τ
  | _, _, .ret v       => .ret v
  | _, _, .var e body  => .var (rw e) (srCom rw body)
  termination_by _ _ c => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-- Equation lemma: `srCom` on a `ret`. -/
@[simp] theorem srCom_ret
    (rw : {Γ : Ctxt d} → {t : d.Ty} → Expr d Γ t → Expr d Γ t)
    {Γ : Ctxt d} {τ : d.Ty} (v : Ctxt.Var Γ τ) :
    srCom rw (Com.ret v) = Com.ret v := by
  rw [srCom]

/-- Equation lemma: `srCom` on a `var`. -/
@[simp] theorem srCom_var
    (rw : {Γ : Ctxt d} → {t : d.Ty} → Expr d Γ t → Expr d Γ t)
    {Γ : Ctxt d} {t τ : d.Ty} (e : Expr d Γ t) (body : Com d (t :: Γ) τ) :
    srCom rw (Com.var e body) = Com.var (rw e) (srCom rw body) := by
  rw [srCom]

/-! ## 2. Denotation preservation (NON-`rfl`)

Given that the rewrite is denotation-sound on every expression, mapping it over
the `Com` preserves the whole-program denotation. The proof is a structural
induction on the `.var` spine: at each binding the bound value is unchanged
(by `rw_sound`), so the extended valuation handed to the body is the same, and
the induction hypothesis closes the body. It is **not** `rfl` because the
program structure changes (a different op is bound) and the two sides agree
only through `rw_sound`. -/

/-- **Denotation preservation for `srCom`.** If `rw` never changes any
expression's denotation, then `srCom rw` never changes the program's
denotation. -/
theorem srCom_denote
    (rw : {Γ : Ctxt d} → {t : d.Ty} → Expr d Γ t → Expr d Γ t)
    (rw_sound : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
      (V : Ctxt.Valuation Γ), (rw e).denote V = e.denote V) :
    {Γ : Ctxt d} → {τ : d.Ty} → (c : Com d Γ τ) → (V : Ctxt.Valuation Γ) →
    (srCom rw c).denote V = c.denote V
  | _, _, .ret v, V => by
      rw [srCom_ret]
  | _, _, .var e body, V => by
      rw [srCom_var, Com.denote, Com.denote]
      -- The bound value is unchanged by the sound rewrite, so the body sees
      -- the same extended valuation; recurse on the body.
      rw [rw_sound e V]
      exact srCom_denote rw rw_sound body (V.extend (e.denote V))
  termination_by _ _ c _ => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-! ## 3. A concrete arithmetic dialect with a real `mul2 ↝ add x x` rewrite

A self-contained dialect over `BitVec 32` with a nullary `const n`, a binary
`add`, and a unary `mul2` (multiply-by-two). The strength reduction rewrites
`mul2 x ↝ add x x`; its soundness is the non-`rfl` arithmetic identity
`2 * a = a + a` over `BitVec 32`. -/

namespace Arith

/-- A toy arithmetic dialect: a single 32-bit value type, a `const`, a binary
`add`, and a unary `mul2` (multiply-by-two). -/
inductive ArithOp where
  | const (n : BitVec 32)
  | add
  | mul2
  deriving DecidableEq

/-- The dialect: a single value type (`Unit`-tagged) and `ArithOp` operations. -/
def arithDialect : Dialect where
  Op := ArithOp
  Ty := Unit

instance : TyDenote arithDialect.Ty where
  denote _ := BitVec 32

instance : DialectSignature arithDialect where
  sig | .const _ => [] | .add => [(), ()] | .mul2 => [()]
  ret _ := ()

instance : DialectDenote arithDialect where
  denote
    | .const n, _                                => n
    | .add,     .cons (a : BitVec 32) (.cons (b : BitVec 32) .nil) => a + b
    | .mul2,    .cons (a : BitVec 32) .nil       => 2 * a

/-! ### The op-equivalence (NON-`rfl`)

`2 * a = a + a` over `BitVec 32`. This is the algebraic identity carrying the
rewrite: `mul2`'s denotation is `2 * a`, the rewritten `add x x` denotes
`a + a`, and they agree only by this `BitVec` fact — NOT `rfl`. Closed by
`bv_decide` (the `BitVec` decision procedure), which discharges it over the
core `BitVec` operations without pulling in Mathlib's ring layer. -/

/-- The strength-reduction op identity over `BitVec 32`: doubling equals
self-addition. Closed by `bv_decide` (the decision procedure for `BitVec`),
**not** `rfl`. -/
theorem two_mul_eq_add_self (a : BitVec 32) : 2 * a = a + a := by
  bv_decide

/-! ### The concrete `Expr → Expr` rewrite

`srExpr` inspects the bound expression: a `mul2` whose single argument is the
variable `x` is rewritten to an `add` of `x` with itself. Every other
expression is returned unchanged. -/

/-- The strength-reduction `Expr` rewrite: `mul2 x ↝ add x x`. Other
expressions pass through unchanged. -/
def srExpr {Γ : Ctxt arithDialect} {t : arithDialect.Ty}
    (e : Expr arithDialect Γ t) : Expr arithDialect Γ t :=
  match e with
  | { op := .mul2, retTy_eq := hr, args := .cons x .nil } =>
      { op := .add, retTy_eq := hr, args := .cons x (.cons x .nil) }
  | e => e

/-- **The strength-reduction rewrite is denotation-sound (NON-`rfl`).** For
every expression `e`, `srExpr e` denotes the same value as `e`. On the
`mul2 x` site this reduces to the arithmetic identity `2 * a = a + a`
(`two_mul_eq_add_self`); on every other expression `srExpr` is the identity. -/
theorem srExpr_sound {Γ : Ctxt arithDialect} {t : arithDialect.Ty}
    (e : Expr arithDialect Γ t) (V : Ctxt.Valuation Γ) :
    (srExpr e).denote V = e.denote V := by
  rcases e with ⟨op, hr, args⟩
  cases op with
  | const n =>
      rfl
  | add =>
      rfl
  | mul2 =>
      -- `args : HVector _ [()]` = `.cons x .nil`.
      match args with
      | .cons x .nil =>
          -- LHS: `add x x` denotes `x + x`; RHS: `mul2 x` denotes `2 * x`.
          -- The two agree only via `2 * a = a + a` — NOT `rfl`.
          dsimp only [srExpr, Expr.denote, Expr.lookupArgs]
          exact (two_mul_eq_add_self (Ctxt.Var.lookup x V)).symm

/-! ### The user-facing strength reducer on `Com` and its preservation

`strengthReduce` runs `srExpr` at every binding. `strengthReduce_denote`
is the whole-program preservation theorem — a corollary of the generic
`srCom_denote` instantiated at `srExpr` with `srExpr_sound`. -/

/-- **Apply strength reduction to a whole program.** Rewrites `mul2 x ↝ add x x`
at every `.var` binding. -/
def strengthReduce {Γ : Ctxt arithDialect} {τ : arithDialect.Ty}
    (c : Com arithDialect Γ τ) : Com arithDialect Γ τ :=
  srCom (fun e => srExpr e) c

/-- **Denotation preservation for `strengthReduce` (NON-`rfl`).** The
strength-reduced program denotes the same function as the original. This is
**not** `rfl`: at every `mul2` site the bound expression changes
(`mul2 x ↝ add x x`), and the two programs denote equal values only through
the `BitVec` identity `2 * a = a + a` (`two_mul_eq_add_self`), threaded over
the whole `Com` by `srCom_denote`. -/
theorem strengthReduce_denote {Γ : Ctxt arithDialect} {τ : arithDialect.Ty}
    (c : Com arithDialect Γ τ) (V : Ctxt.Valuation Γ) :
    (strengthReduce c).denote V = c.denote V := by
  unfold strengthReduce
  exact srCom_denote (fun e => srExpr e) (fun e V => srExpr_sound e V) c V

/-! ### A concrete worked example (the transform really rewrites a binding)

A closed program `let y = mul2 x; ret y` (with `x` an input). Strength
reduction rewrites it to `let y = add x x; ret y`. The bound op
changes (`mul2 → add`), yet the denotation is preserved: both compute `2 * x`. -/

/-- A program over context `[()]` (one input `x`): bind `mul2 x`, return it. -/
def doubleProg : Com arithDialect [()] () :=
  .var { op := .mul2, retTy_eq := rfl, args := .cons .here .nil }
    (.ret .here)

/-- The strength-reduced program binds `add x x` instead of `mul2 x`: the bound
op differs. -/
theorem strengthReduce_doubleProg :
    strengthReduce doubleProg
      = .var { op := ArithOp.add, retTy_eq := rfl,
               args := .cons .here (.cons .here .nil) } (.ret .here) := by
  unfold strengthReduce doubleProg
  rw [srCom_var, srCom_ret]
  rfl

/-- The two programs are **not** syntactically equal — strength reduction did
real work (the bound op changed `mul2 → add`). -/
example : strengthReduce doubleProg ≠ doubleProg := by
  rw [strengthReduce_doubleProg, doubleProg]
  intro h
  rw [Com.var.injEq] at h
  have he := eq_of_heq h.2.1
  exact ArithOp.noConfusion (congrArg Expr.op he)

/-- Denotation preservation on the concrete program: both denote `2 * x` for
any input `x` (the rewritten one as `x + x`). -/
example (x : BitVec 32) :
    (strengthReduce doubleProg).denote (.cons x .nil)
      = doubleProg.denote (.cons x .nil) :=
  strengthReduce_denote doubleProg (.cons x .nil)

-- `#eval`: input `x = 5`. Original `mul2 5 = 10`; rewritten `add 5 5 = 10`.
#eval doubleProg.denote (.cons (5 : BitVec 32) .nil)                 -- 10
#eval (strengthReduce doubleProg).denote (.cons (5 : BitVec 32) .nil) -- 10

end Arith

end CatCrypt.Crypto.SecureCompilation.VIR.StrengthReduceReal
