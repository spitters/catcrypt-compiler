/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# An eliminating common-subexpression-elimination pass for `Com` (real transform)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`CommonSubexprElim.lean` ships an *analysis-as-labelling* CSE whose `Com → Com`
rewrite is the identity (`applyCse = fun p _ => p`), so its preservation
theorems are `rfl` and verify nothing about an actual elimination. This file
supplies what that one defers: a **structural** `Com → Com` transform that
*removes* a redundant let-binding and *redirects its uses to the
earlier, equal binding*, together with a **non-`rfl`** denotation-preservation
proof by induction over the `Com`.

This mirrors `DeadCodeElimReal.lean` (the proven template that did the same for
dead-code elimination): there the dropped binding was *dead* (never read here);
here the dropped binding is *redundant* (it recomputes a value already bound by
the immediately preceding binding), and instead of forbidding uses of the
dropped slot we **rewrite** them onto the canonical earlier slot.

## The transform

Consider two **adjacent** bindings computing the *same* expression:

```
let v0 = e        -- e : Expr d Γ t,           binds v0 : t
let v1 = e'       -- e' : Expr d (t :: Γ) t,   binds v1 : t
<body>            -- body : Com d (t :: t :: Γ) s
```

The inner binding `v1 = e'` is **redundant** exactly when `e'`, evaluated in the
extended context `t :: Γ`, denotes the same value as `v0`. The syntactic
sufficient condition (single-static-assignment, so a `Ctxt.Var` names one fixed
value) is: `e'` is `e` with every argument variable shifted up by one (`.there`)
— i.e. `e'` reads exactly the same originating slots as `e`, now one binder
deeper. Then `e'.denote (V.extend (e.denote V)) = e.denote V`, so `v1` always
equals `v0`.

CSE then **drops** the redundant binding and **redirects** every use of `v1`
(the dropped slot, de Bruijn `.here` in `t :: t :: Γ`) onto `v0` (the earlier
equal slot). The body is re-typed from `t :: t :: Γ` down to `t :: Γ`:

* a use of `v1` (`.here`)          ↝ `v0` (`.here` after the slot is dropped);
* a use of `v0` (`.there .here`)   ↝ `v0` (`.here`);
* a use of an earlier slot         ↝ shifted down by one.

So `.here` and `.there .here` **merge** onto the single canonical slot — this is
the CSE deduplication, and it is *not* the identity: the context shrinks and two
distinct de Bruijn variables collapse to one.

## The proof (not `rfl`)

The central lemma is

  `cseHead_denote`:
    `(cseHead e' body h_eq).denote (V.extend w) = (Com.var e' body).denote (V.extend w)`

where `w = e.denote V` is the canonical value. The transformed (smaller) program
at `V.extend w` denotes the same function as the original at `V.extend w`,
because the dropped binding `v1` *always equals* `v0 = w` (the equal-expression
hypothesis), so redirecting `v1`'s uses to `v0` changes nothing observable. The
proof is a structural induction on `body` (peeling each `.var`), threaded through
the matching substitution laws on `Var` / `HVector` / `Expr`. It is **not**
`rfl`: the transform changes the program's context and structure, and the two
sides denote at *different* valuations (`V.extend w` over `t :: Γ` vs.
`(V.extend w).extend w` over `t :: t :: Γ`) that agree only because the two
merged slots hold the same value `w`.

## What is general vs. scoped

* **General:** the substitution (`substVar`, `substHV`, `substExpr`, `cseSubst`)
  and the lookup/denotation laws (`substVar_lookup`, `cseSubst_denote`) work at
  an arbitrary de Bruijn position `|Δ|`, for any dialect, merging the slot at
  depth `|Δ|` onto the slot at depth `|Δ| + 1`.
* **Scoped to the cleanest case:** `cseHead` / `cseHead_denote` specialise to
  `Δ = []` — eliminating the *innermost-of-two-adjacent* redundant `.var` and
  redirecting its uses to the immediately preceding equal binding. The
  user-facing `cseAdjacent` runs on `.var e (.var e' body)`, checks the
  equal-expression hypothesis, and returns the smaller `.var e
  (cseHead e' body …)` with the preservation theorem `cseAdjacent_denote`.
-/

set_option autoImplicit false
-- Several equation/lookup lemmas legitimately do not use every ambient
-- typeclass section variable (`TyDenote`/`DialectSignature`); silence the
-- section-variable linter rather than thread per-theorem `omit` clauses.
set_option linter.unusedSectionVars false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CSEReal

open CatCrypt.Crypto.SecureCompilation.VIR

variable {d : Dialect} [TyDenote d.Ty]

/-! ## 0. A structural length measure on `Com`

`cseSubst` / `cseSubst_denote` recurse on a `Com` whose *index* (the context)
changes at each step, so Lean cannot infer structural recursion and falls back
to well-founded recursion. We supply an explicit, plainly-structural length
measure and use it as the `termination_by` measure (cf. `DeadCodeElimReal`). -/

/-- Number of `.var` bindings in a `Com` (a structural `Nat` measure). -/
def comLen [DialectSignature d] {Γ₀ : Ctxt d} {τ₀ : d.Ty} : Com d Γ₀ τ₀ → Nat
  | .ret _      => 0
  | .var _ body => comLen body + 1

/-! ## 1. Variable substitution merging the dropped slot onto the earlier one

We work with a context split as `Δ ++ t :: t :: Γ`; the slot to drop is the
*first* `t` (the redundant binding `v1`), at depth `|Δ|`. Its uses are
redirected onto the *second* `t` (the canonical binding `v0`), at depth
`|Δ| + 1`. A variable `Var (Δ ++ t :: t :: Γ) s`:

* points *into* `Δ` (depth `< |Δ|`)             → survives unchanged;
* points *at* the dropped slot (depth `= |Δ|`)  → redirected to the canonical
  slot, which after dropping sits at depth `|Δ|`;
* points *at* the canonical slot (depth `= |Δ| + 1`) → shifts down to depth
  `|Δ|` (the slot above it is gone);
* points *past* both (depth `> |Δ| + 1`)        → shifts down by one.

`substVar` produces the re-typed variable over the shrunk context
`Δ ++ t :: Γ`. -/

/-- Substitute a variable across the dropped slot at depth `|Δ|`, redirecting
that slot onto the canonical slot at depth `|Δ| + 1`. -/
def substVar : {Δ : Ctxt d} → {t : d.Ty} → {Γ : Ctxt d} → {s : d.Ty} →
    Ctxt.Var (Δ ++ t :: t :: Γ) s → Ctxt.Var (Δ ++ t :: Γ) s
  -- Δ = []: the head two slots are the redundant/canonical pair.
  | [],     _, _, _, .here          => .here            -- v1 ↝ v0
  | [],     _, _, _, .there v        => v                -- v0 and deeper shift down
  -- Δ = _ :: _: descend, keeping the head slot.
  | _ :: _, _, _, _, .here          => .here
  | _ :: _, t, Γ, _, .there v        =>
      .there (substVar (Δ := _) (t := t) (Γ := Γ) v)

/-! ## 2. Substitution lifted over `HVector` of variables, `Expr`, `Com` -/

/-- Substitute every variable in an `HVector`. -/
def substHV {Δ : Ctxt d} {t : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var (Δ ++ t :: t :: Γ) ty) tys →
    HVector (fun ty => Ctxt.Var (Δ ++ t :: Γ) ty) tys
  | [],     .nil        => .nil
  | _ :: _, .cons v rest => .cons (substVar v) (substHV rest)

variable [DialectSignature d]

/-- Substitute an `Expr`'s argument variables. -/
def substExpr {Δ : Ctxt d} {t : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (Δ ++ t :: t :: Γ) s) : Expr d (Δ ++ t :: Γ) s :=
  { op := e.op, retTy_eq := e.retTy_eq, args := substHV e.args }

/-- Substitute a whole `Com`, merging the dropped slot onto the canonical one.
The recursion grows the prefix `Δ` by each freshly bound type as it descends
under a `.var`. -/
def cseSubst : {Δ : Ctxt d} → {t : d.Ty} → {Γ : Ctxt d} → {τ : d.Ty} →
    Com d (Δ ++ t :: t :: Γ) τ → Com d (Δ ++ t :: Γ) τ
  | _,  _, _, _, .ret v         => .ret (substVar v)
  | Δ, t, Γ, _, .var (t := s) e body =>
      .var (substExpr e)
           (cseSubst (Δ := s :: Δ) (t := t) (Γ := Γ) body)
  termination_by _ _ _ _ c => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-- Equation lemma: `cseSubst` on a `ret`. -/
@[simp] theorem cseSubst_ret {Δ : Ctxt d} {t : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (v : Ctxt.Var (Δ ++ t :: t :: Γ) τ) :
    cseSubst (Com.ret v) = Com.ret (substVar v) := by
  rw [cseSubst]

/-- Equation lemma: `cseSubst` on a `var`. -/
@[simp] theorem cseSubst_var {Δ : Ctxt d} {t : d.Ty} {Γ : Ctxt d}
    {s τ : d.Ty} (e : Expr d (Δ ++ t :: t :: Γ) s)
    (body : Com d (s :: (Δ ++ t :: t :: Γ)) τ) :
    cseSubst (Com.var e body) =
      Com.var (substExpr e) (cseSubst (Δ := s :: Δ) (t := t) (Γ := Γ) body) := by
  rw [cseSubst]

/-! ## 3. The "merged valuation": the canonical value sits in both slots

To state preservation we need, for a valuation `V : Valuation (Δ ++ Γ)` and the
canonical value `w : ⟦t⟧`, two valuations:

* `single V w : Valuation (Δ ++ t :: Γ)` — the **shrunk** valuation, with `w`
  at the single surviving slot;
* `double V w : Valuation (Δ ++ t :: t :: Γ)` — the **original** valuation, with
  `w` at *both* the redundant and the canonical slots (because the redundant
  binding always recomputes `w`).

The preservation law says: the substituted program at `single V w` denotes
exactly what the original denotes at `double V w`. The two valuations differ
only at the dropped slot, where the original holds `w` — the same `w` the
substitution redirects to. -/

/-- The shrunk valuation: drop the redundant slot, keep `w` at the canonical. -/
def single : {Δ : Ctxt d} → {t : d.Ty} → {Γ : Ctxt d} →
    Ctxt.Valuation (Δ ++ Γ) → ⟦t⟧ → Ctxt.Valuation (Δ ++ t :: Γ)
  | [],     _, _, V,         w => .cons w V
  | _ :: _, _, _, .cons v V, w => .cons v (single V w)

/-- The original valuation: `w` at *both* the redundant and canonical slots. -/
def double : {Δ : Ctxt d} → {t : d.Ty} → {Γ : Ctxt d} →
    Ctxt.Valuation (Δ ++ Γ) → ⟦t⟧ → Ctxt.Valuation (Δ ++ t :: t :: Γ)
  | [],     _, _, V,         w => .cons w (.cons w V)
  | _ :: _, _, _, .cons v V, w => .cons v (double V w)

/-! ## 4. The substitution laws (lookups agree)

The inductive lemmas: looking up a substituted variable in `single V w`
equals looking up the original variable in `double V w`. Both the redundant slot
and the canonical slot hold `w` in `double`, so merging them is sound. -/

/-- **Variable law.** A substituted variable looks up the same value in
`single V w` (via its substitution) as the original does in `double V w`. -/
theorem substVar_lookup :
    {Δ : Ctxt d} → {t : d.Ty} → {Γ : Ctxt d} → {s : d.Ty} →
    (v : Ctxt.Var (Δ ++ t :: t :: Γ) s) →
    (V : Ctxt.Valuation (Δ ++ Γ)) → (w : ⟦t⟧) →
    (substVar v).lookup (single V w) = v.lookup (double V w)
  | [],     _, _, _, .here,    V, w => by
      rw [substVar]; rfl
  | [],     _, _, _, .there v, V, w => by
      rw [substVar]
      -- `v : Var (t :: Γ) s`; LHS = v.lookup (single V w) = v.lookup (.cons w V);
      -- RHS = (Var.there v).lookup (.cons w (.cons w V)) = v.lookup (.cons w V).
      rfl
  | _ :: _, _, _, _, .here,    .cons _ _, _ => by
      rw [substVar]; rfl
  | _ :: _, t, Γ, _, .there v, .cons u V, w => by
      rw [substVar, single, double]
      show (substVar v).lookup (single V w) = v.lookup (double V w)
      exact substVar_lookup (Δ := _) (t := t) (Γ := Γ) v V w

/-- **HVector law.** Resolving a substituted `HVector` against `single V w`
yields the same heterogeneous vector as the original against `double V w`. -/
theorem substHV_lookupArgs {Δ : Ctxt d} {t : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} →
    (vs : HVector (fun ty => Ctxt.Var (Δ ++ t :: t :: Γ) ty) tys) →
    (V : Ctxt.Valuation (Δ ++ Γ)) → (w : ⟦t⟧) →
    Expr.lookupArgs (substHV vs) (single V w) = Expr.lookupArgs vs (double V w)
  | [],     .nil,         _, _ => by simp [substHV, Expr.lookupArgs]
  | _ :: _, .cons v rest, V, w => by
      simp only [substHV, Expr.lookupArgs]
      rw [substVar_lookup v V w, substHV_lookupArgs rest V w]

variable [DialectDenote d]

/-- **Expr law.** A substituted `Expr` denotes the same value at `single V w`
as the original at `double V w`. -/
theorem substExpr_denote {Δ : Ctxt d} {t : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (Δ ++ t :: t :: Γ) s)
    (V : Ctxt.Valuation (Δ ++ Γ)) (w : ⟦t⟧) :
    (substExpr e).denote (single V w) = e.denote (double V w) := by
  unfold substExpr Expr.denote
  simp only []
  rw [substHV_lookupArgs e.args V w]

/-! ## 5. Denotation preservation of the substitution (NON-`rfl`)

The substituted program at `single V w` denotes the same function as the
original at `double V w`. The two valuations differ at the dropped slot (where
the original holds the canonical value `w`), so merging the slot onto the
canonical one is observationally invisible. Structural induction on `Com`. -/

/-- **Substitution preservation, general position.** -/
theorem cseSubst_denote :
    {Δ : Ctxt d} → {t : d.Ty} → {Γ : Ctxt d} → {τ : d.Ty} →
    (c : Com d (Δ ++ t :: t :: Γ) τ) →
    (V : Ctxt.Valuation (Δ ++ Γ)) → (w : ⟦t⟧) →
    (cseSubst c).denote (single V w) = c.denote (double V w)
  | _,  _, _, _, .ret v, V, w => by
      show (cseSubst (Com.ret v)).denote (single V w) = (Com.ret v).denote (double V w)
      rw [cseSubst_ret]
      show (substVar v).lookup (single V w) = (Com.ret v).denote (double V w)
      rw [Com.denote]
      exact substVar_lookup v V w
  | Δ, t, Γ, _, .var (t := s) e body, V, w => by
      rw [cseSubst_var]
      show (cseSubst (Δ := s :: Δ) (t := t) (Γ := Γ) body).denote
              ((single V w).extend ((substExpr e).denote (single V w)))
            = (Com.var e body).denote (double V w)
      rw [Com.denote]
      rw [substExpr_denote e V w]
      -- Recurse under the binding. The prefix grows to `s :: Δ`, where
      -- `single (V.extend u) w = (single V w).extend u` and
      -- `double (V.extend u) w = (double V w).extend u` definitionally.
      have IH := cseSubst_denote (Δ := s :: Δ) (t := t) (Γ := Γ) body
                   (V.extend (e.denote (double V w))) w
      exact IH
  termination_by _ _ _ _ c _ _ => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-! ## 6. Scoped, user-facing case: eliminating the INNERMOST of two adjacent
       redundant bindings

The cleanest instance: `Δ = []`. The redundant binding `v1 = e'` sits directly
above the canonical `v0 = e`; `cseHead` drops `v1` and redirects its uses to
`v0`, given a proof that `e'` recomputes `v0`'s value. -/

/-- **Redundancy hypothesis.** The inner expression `e'`, evaluated in the
context `t :: Γ` extended by the canonical value `w := e.denote V`, recomputes
exactly `w`. This is what makes the inner binding redundant. (The syntactic
sufficient condition — `e'` is `e` shifted by one `.there` — implies this; we
take the semantic form so the law is maximally general.) -/
abbrev RedundantHead {t : d.Ty} {Γ : Ctxt d}
    (e : Expr d Γ t) (e' : Expr d (t :: Γ) t) : Prop :=
  ∀ V : Ctxt.Valuation Γ, e'.denote (V.extend (e.denote V)) = e.denote V

/-- **Eliminate the redundant inner binding.** Given the body of two adjacent
bindings (context `t :: t :: Γ`), drop the redundant slot and redirect its uses
to the canonical slot, re-typing the body under `t :: Γ`. This changes
the context `t :: t :: Γ ↝ t :: Γ` and merges two de Bruijn variables. -/
def cseHead {t : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (body : Com d (t :: t :: Γ) τ) : Com d (t :: Γ) τ :=
  cseSubst (Δ := []) (t := t) (Γ := Γ) body

/-- **Innermost preservation (NON-`rfl`).** When the inner expression `e'` is
redundant (recomputes the canonical value `w := e.denote V`), the rewritten
program `Com.var e (cseHead body)` denotes the same function as the original
`Com.var e (Com.var e' body)`. -/
theorem cseHead_denote {t : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (e : Expr d Γ t) (e' : Expr d (t :: Γ) t)
    (body : Com d (t :: t :: Γ) τ) (hred : RedundantHead e e')
    (V : Ctxt.Valuation Γ) :
    (Com.var e (cseHead body)).denote V
      = (Com.var e (Com.var e' body)).denote V := by
  -- Unfold both outer bindings; the inner binding extends with
  -- `e'.denote (V.extend (e.denote V))`, which by redundancy equals `e.denote V`,
  -- so both slots hold the canonical value.
  rw [Com.denote, Com.denote, Com.denote, hred V]
  unfold cseHead
  -- `single (Δ := []) V w = V.extend w`; `double (Δ := []) V w = (V.extend w).extend w`.
  have := cseSubst_denote (Δ := []) (t := t) (Γ := Γ) body V (e.denote V)
  simpa [single, double, Ctxt.Valuation.extend] using this

/-! ## 7. End-to-end: run on `.var e (.var e' body)`

`cseAdjacent` takes the full two-binding program plus the redundancy proof and
returns the smaller `.var e (cseHead body)` — one fewer binding.
`cseAdjacent_denote` is the user-facing preservation theorem. -/

/-- Eliminate the redundant inner binding of an adjacent pair `e; e'`, given a
proof `e'` is redundant. Returns the smaller program over the same context. -/
def cseAdjacent {t : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (e : Expr d Γ t) (e' : Expr d (t :: Γ) t)
    (body : Com d (t :: t :: Γ) τ) (_hred : RedundantHead e e') :
    Com d Γ τ :=
  Com.var e (cseHead body)

/-- **End-to-end CSE preservation (NON-`rfl`).** `cseAdjacent` preserves
denotation: dropping the redundant inner binding and redirecting its uses to the
canonical binding leaves the meaning unchanged. -/
theorem cseAdjacent_denote {t : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (e : Expr d Γ t) (e' : Expr d (t :: Γ) t)
    (body : Com d (t :: t :: Γ) τ) (hred : RedundantHead e e')
    (V : Ctxt.Valuation Γ) :
    (cseAdjacent e e' body hred).denote V
      = (Com.var e (Com.var e' body)).denote V := by
  unfold cseAdjacent
  exact cseHead_denote e e' body hred V

/-! ## 8. A concrete worked example (the transform really removes a binding)

A self-contained one-type, two-op toy dialect over `Nat`, on which we exhibit a
program with a redundant inner binding (`v1 = dbl v0`-style recompute
where the syntactic shift makes `e'` recompute `v0`), run `cseAdjacent`, and
check (via `comLen`) that the result has **one fewer** binding — the elimination
is real, not the identity. We also confirm the denotation agrees. -/

namespace Demo

/-- A toy dialect: a single value type, a `const` op (nullary) and an `id`
op (unary, returns its argument). -/
inductive ToyOp where
  | const (n : Nat)
  | idOp
  deriving DecidableEq

def toyDialect : Dialect where
  Op := ToyOp
  Ty := Unit

instance : TyDenote toyDialect.Ty where
  denote _ := Nat

instance : DialectSignature toyDialect where
  sig | .const _ => [] | .idOp => [()]
  ret _ := ()

instance : DialectDenote toyDialect where
  denote
    | .const n, _                  => n
    | .idOp,    .cons (a : Nat) .nil => a

/-- The canonical expression `e = const 7` (over `Γ = []`, no args). -/
def e0 : Expr toyDialect [] () :=
  { op := .const 7, retTy_eq := rfl, args := .nil }

/-- The redundant expression `e' = const 7` (over `() :: []`). Same op, no args,
so it recomputes the same value as `e0` regardless of context. -/
def e1 : Expr toyDialect [()] () :=
  { op := .const 7, retTy_eq := rfl, args := .nil }

/-- `e1` is redundant: it always recomputes `e0`'s value (both are `const 7`). -/
theorem e1_redundant : CSEReal.RedundantHead e0 e1 := by
  intro V
  rfl

/-- The body of the adjacent pair: returns `v1` (the redundant binding,
`.here`). After CSE, this use of `v1` is redirected to `v0`. -/
def adjBody : Com toyDialect [(), ()] () :=
  .ret .here

/-- The full two-binding program:
```
let v0 = const 7   -- e0
let v1 = const 7   -- e1 (redundant)
ret v1
```
-/
def fullProg : Com toyDialect [] () :=
  .var e0 (.var e1 adjBody)

/-- The full program has **two** bindings. -/
example : comLen fullProg = 2 := rfl

/-- After CSE, **one** binding remains: the binder count drops `2 → 1`. -/
example :
    comLen (CSEReal.cseAdjacent e0 e1 adjBody e1_redundant) = 1 := by native_decide

/-- The substitution merges `v1`'s use onto `v0`: `cseHead adjBody`
returns `.ret v0` over the smaller context `() :: []`. -/
example : CSEReal.cseHead adjBody = Com.ret .here := by
  unfold CSEReal.cseHead adjBody
  rw [CSEReal.cseSubst.eq_def]
  rfl

/-- CSE preserves `fullProg`'s denotation: dropping the redundant `v1` and
returning `v0` instead leaves the meaning unchanged (`7`). -/
example (V : Ctxt.Valuation (d := toyDialect) []) :
    (CSEReal.cseAdjacent e0 e1 adjBody e1_redundant).denote V
      = fullProg.denote V :=
  CSEReal.cseAdjacent_denote e0 e1 adjBody e1_redundant V

-- `#eval`: both the eliminated and original program denote `7`.
#eval (CSEReal.cseAdjacent e0 e1 adjBody e1_redundant).denote .nil  -- 7
#eval fullProg.denote .nil                                          -- 7

end Demo

end CatCrypt.Crypto.SecureCompilation.VIR.CSEReal
