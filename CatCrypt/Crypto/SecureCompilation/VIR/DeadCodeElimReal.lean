/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# An eliminating dead-code-elimination pass for `Com` (real transform)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`DeadCodeElim.lean` ships an *analysis-as-labelling* DCE whose `Com → Com`
rewrite is the identity (`applyDce = fun p _ => p`), so its preservation
theorems are `rfl` and verify nothing about an actual elimination. This file
supplies what that one avoids: a **structural** `Com → Com` transform that
*removes* a dead let-binding, together with a **non-`rfl`**
denotation-preservation proof by induction over the `Com` and the de Bruijn
strengthening it forces.

## The transform

A let-binding `Com.var e body : Com d Γ τ` introduces a fresh variable of type
`t'` into the context: `body : Com d (t' :: Γ) τ`. The binding is **dead** when
`body` never reads that fresh variable — i.e. `body` never uses the de Bruijn
variable `Ctxt.Var.here`. In that case the binding can be dropped and `body`
re-typed under the *smaller* context `Γ`, with every `Ctxt.Var` index that
pointed *past* the dead slot shifted down by one.

`Core.lean`'s `Com` is dialect-agnostic and intrinsically typed, so the
strengthening is the real content. We do it at an **arbitrary** position
(not only the outermost binding) by splitting the context as
`Δ ++ t' :: Γ`: the dead slot sits at de Bruijn depth `|Δ|`. This generality
is exactly what lets the proof recurse under a `.var` (where the prefix `Δ`
grows by one).

## The proof (not `rfl`)

The central lemma is

  `removeDeadHead_denote`:
    `(removeDeadHead body h).denote V = body.denote (V.insertAt x)`

for *any* value `x` of the dropped slot's type — the dead value is irrelevant
precisely because `body` never reads it. The proof is a structural induction
on `Com` (peeling each `.var`), threaded through the matching strengthening
laws on `Var` / `HVector` / `Expr`. It is **not** `rfl`: the transform changes
the program's context and structure, and the two sides denote at *different*
valuations (`V` vs. `V.insertAt x`) that agree only because of the
liveness hypothesis.

## What is general vs. scoped

* **General:** the strengthening (`strengthenVar`, `strengthenHV`,
  `strengthenExpr`, `removeDead`) and the denotation law
  (`removeDead_denote`) work at an arbitrary de Bruijn position `|Δ|`, for any
  dialect, on a binding proven dead.
* **Scoped to the cleanest case:** `removeDeadHead` / `removeDeadHead_denote`
  specialise to `Δ = []` — dropping the *outermost* dead `.var`. The
  user-facing `dceOutermost` runs the deadness check and, when it succeeds,
  returns the smaller program with the preservation theorem
  `dceOutermost_denote`.
-/

@[expose] public section

set_option autoImplicit false
-- Several equation/lookup lemmas legitimately do not use every ambient
-- typeclass section variable (`TyDenote`/`DialectSignature`); silence the
-- section-variable linter rather than thread per-theorem `omit` clauses.
set_option linter.unusedSectionVars false

namespace CatCrypt.Crypto.SecureCompilation.VIR.DCEReal

open CatCrypt.Crypto.SecureCompilation.VIR

variable {d : Dialect} [TyDenote d.Ty]

/-! ## 0. A structural length measure on `Com`

`usesSlotCom` / `removeDead` / `removeDead_denote` recurse on a `Com` whose
*index* (the context) changes at each step, so Lean cannot infer structural
recursion and falls back to well-founded recursion. The dependently-typed
`sizeOf` confuses `omega` (it sees the two `sizeOf body` occurrences as distinct
atoms). We sidestep this with an explicit, plainly-structural length measure
(`Γ` is a variable here, so this *is* structural) and use it as the
`termination_by` measure. -/

/-- Number of `.var` bindings in a `Com` (a structural `Nat` measure). -/
def comLen [DialectSignature d] {Γ₀ : Ctxt d} {τ₀ : d.Ty} : Com d Γ₀ τ₀ → Nat
  | .ret _      => 0
  | .var _ body => comLen body + 1

/-! ## 1. Variable strengthening across a removed slot

We work with a context split as `Δ ++ t' :: Γ`; the slot to remove is the
`t'` at depth `|Δ|`. A variable `Var (Δ ++ t' :: Γ) s` either points *into*
`Δ` (depth `< |Δ|`, survives unchanged), *at* the dead slot (depth `= |Δ|`,
which the deadness hypothesis forbids), or *past* it (depth `> |Δ|`, shifts
down by one). `usesSlot` is the Boolean "this var is the dead slot", and
`strengthenVar` produces the re-typed variable when it is not. -/

/-- Does this variable point exactly at the removed slot (depth `|Δ|`)? -/
def usesSlotVar : {Δ : Ctxt d} → {t' : d.Ty} → {Γ : Ctxt d} → {s : d.Ty} →
    Ctxt.Var (Δ ++ t' :: Γ) s → Bool
  | [],      _,  _, _, .here     => true
  | [],      _,  _, _, .there _  => false
  | _ :: _,  _,  _, _, .here     => false
  | _ :: _,  t', Γ, _, .there v  => usesSlotVar (Δ := _) (t' := t') (Γ := Γ) v

/-- Strengthen a variable that does **not** point at the removed slot, dropping
the `t'` at depth `|Δ|` from its context. -/
def strengthenVar : {Δ : Ctxt d} → {t' : d.Ty} → {Γ : Ctxt d} → {s : d.Ty} →
    (v : Ctxt.Var (Δ ++ t' :: Γ) s) → usesSlotVar v = false → Ctxt.Var (Δ ++ Γ) s
  | [],      _,  _, _, .here,    h => by simp [usesSlotVar] at h
  | [],      _,  _, _, .there v, _ => v
  | _ :: _,  _,  _, _, .here,    _ => .here
  | _ :: _,  t', Γ, _, .there v, h =>
      .there (strengthenVar (Δ := _) (t' := t') (Γ := Γ) v h)

/-! ## 2. Strengthening lifted over `HVector` of variables, `Expr`, `Com` -/

/-- A whole `HVector` of variables is slot-free when every entry is. -/
def usesSlotHV {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var (Δ ++ t' :: Γ) ty) tys → Bool
  | [],     .nil        => false
  | _ :: _, .cons v rest => usesSlotVar v || usesSlotHV rest

/-- Strengthen a slot-free `HVector` of variables. -/
def strengthenHV {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → (vs : HVector (fun ty => Ctxt.Var (Δ ++ t' :: Γ) ty) tys) →
    usesSlotHV vs = false → HVector (fun ty => Ctxt.Var (Δ ++ Γ) ty) tys
  | [],     .nil,         _ => .nil
  | _ :: _, .cons v rest, h =>
      .cons (strengthenVar v (by
              have := h; simp only [usesSlotHV, Bool.or_eq_false_iff] at this; exact this.1))
            (strengthenHV rest (by
              have := h; simp only [usesSlotHV, Bool.or_eq_false_iff] at this; exact this.2))

variable [DialectSignature d]

/-- An `Expr` is slot-free when its argument `HVector` is. -/
def usesSlotExpr {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (Δ ++ t' :: Γ) s) : Bool :=
  usesSlotHV e.args

/-- Strengthen a slot-free `Expr`. -/
def strengthenExpr {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (Δ ++ t' :: Γ) s) (h : usesSlotExpr e = false) :
    Expr d (Δ ++ Γ) s :=
  { op := e.op, retTy_eq := e.retTy_eq, args := strengthenHV e.args h }

/-- A `Com` is slot-free when every `Expr` it binds and its final `ret` are.
The recursion grows the prefix `Δ` by the freshly bound type as it descends
under each `.var`. -/
def usesSlotCom : {Δ : Ctxt d} → {t' : d.Ty} → {Γ : Ctxt d} → {τ : d.Ty} →
    Com d (Δ ++ t' :: Γ) τ → Bool
  | _,  _, _, _, .ret v         => usesSlotVar v
  | Δ, t', Γ, _, .var (t := s) e body =>
      usesSlotExpr e ||
        usesSlotCom (Δ := s :: Δ) (t' := t') (Γ := Γ) body
  termination_by _ _ _ _ c => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-- Equation lemma: `usesSlotCom` on a `ret`. -/
@[simp] theorem usesSlotCom_ret {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (v : Ctxt.Var (Δ ++ t' :: Γ) τ) :
    usesSlotCom (Com.ret v) = usesSlotVar v := by
  rw [usesSlotCom]

/-- Equation lemma: `usesSlotCom` on a `var`. -/
@[simp] theorem usesSlotCom_var {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d}
    {s τ : d.Ty} (e : Expr d (Δ ++ t' :: Γ) s)
    (body : Com d (s :: (Δ ++ t' :: Γ)) τ) :
    usesSlotCom (Com.var e body) =
      (usesSlotExpr e || usesSlotCom (Δ := s :: Δ) (t' := t') (Γ := Γ) body) := by
  rw [usesSlotCom]

/-- **The real eliminating transform.** Remove the dead slot at depth `|Δ|`
from a slot-free `Com`, producing a smaller (re-typed) program. -/
def removeDead : {Δ : Ctxt d} → {t' : d.Ty} → {Γ : Ctxt d} → {τ : d.Ty} →
    (c : Com d (Δ ++ t' :: Γ) τ) → usesSlotCom c = false → Com d (Δ ++ Γ) τ
  | _,  _, _, _, .ret v, h => .ret (strengthenVar v (by rwa [usesSlotCom_ret] at h))
  | Δ, t', Γ, _, .var (t := s) e body, h =>
      .var (strengthenExpr e (by
              rw [usesSlotCom_var, Bool.or_eq_false_iff] at h; exact h.1))
           (removeDead (Δ := s :: Δ) (t' := t') (Γ := Γ) body (by
              rw [usesSlotCom_var, Bool.or_eq_false_iff] at h; exact h.2))
  termination_by _ _ _ _ c _ => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-! ## 3. Inserting the dropped value back into a valuation

To state preservation we need, for a valuation `V : Valuation (Δ ++ Γ)` and an
arbitrary value `x : ⟦t'⟧`, the valuation `V.insertAt x : Valuation
(Δ ++ t' :: Γ)` that puts `x` back at the removed slot. This is the inverse
operation to deleting the slot; the preservation law says the strengthened
program at `V` and the original at `V.insertAt x` agree. -/

/-- Insert a value `x` of the dropped type back at depth `|Δ|`. -/
def insertAt : {Δ : Ctxt d} → {t' : d.Ty} → {Γ : Ctxt d} →
    Ctxt.Valuation (Δ ++ Γ) → ⟦t'⟧ → Ctxt.Valuation (Δ ++ t' :: Γ)
  | [],     _, _, V,          x => .cons x V
  | _ :: _, _, _, .cons v V,  x => .cons v (insertAt V x)

/-! ## 4. The strengthening laws (lookups agree)

These are the inductive lemmas: looking up a strengthened variable in
`V` equals looking up the original variable in `V.insertAt x`. The dead slot
is the only place where the two valuations differ, and a slot-free variable
never lands there. -/

/-- **Variable law.** A slot-free variable looks up the same value in `V` (via
its strengthening) as the original does in `V.insertAt x`. -/
theorem strengthenVar_lookup :
    {Δ : Ctxt d} → {t' : d.Ty} → {Γ : Ctxt d} → {s : d.Ty} →
    (v : Ctxt.Var (Δ ++ t' :: Γ) s) → (h : usesSlotVar v = false) →
    (V : Ctxt.Valuation (Δ ++ Γ)) → (x : ⟦t'⟧) →
    (strengthenVar v h).lookup V = v.lookup (insertAt V x)
  | [],      _,  _, _, .here,    h, _,        _ => by simp [usesSlotVar] at h
  | [],      _,  _, _, .there v, _, V,        x => by
      rw [strengthenVar]; rfl
  | _ :: _,  _,  _, _, .here,    _, .cons _ _, _ => by
      rw [strengthenVar]; rfl
  | _ :: _,  t', Γ, _, .there v, h, .cons w V, x => by
      rw [strengthenVar, insertAt]
      show (strengthenVar v h).lookup V = v.lookup (insertAt V x)
      exact strengthenVar_lookup (Δ := _) (t' := t') (Γ := Γ) v h V x

/-- **HVector law.** Resolving a strengthened slot-free `HVector` against `V`
yields the same heterogeneous vector as the original against `V.insertAt x`. -/
theorem strengthenHV_lookupArgs {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} →
    (vs : HVector (fun ty => Ctxt.Var (Δ ++ t' :: Γ) ty) tys) →
    (h : usesSlotHV vs = false) →
    (V : Ctxt.Valuation (Δ ++ Γ)) → (x : ⟦t'⟧) →
    Expr.lookupArgs (strengthenHV vs h) V = Expr.lookupArgs vs (insertAt V x)
  | [],     .nil,         _, _, _ => by simp [strengthenHV, Expr.lookupArgs]
  | _ :: _, .cons v rest, h, V, x => by
      simp only [strengthenHV, Expr.lookupArgs]
      have h1 : usesSlotVar v = false := by
        simp only [usesSlotHV, Bool.or_eq_false_iff] at h; exact h.1
      have h2 : usesSlotHV rest = false := by
        simp only [usesSlotHV, Bool.or_eq_false_iff] at h; exact h.2
      rw [strengthenVar_lookup v h1 V x, strengthenHV_lookupArgs rest h2 V x]

variable [DialectDenote d]

/-- **Expr law.** A slot-free `Expr` denotes the same value at `V` (after
strengthening) as the original at `V.insertAt x`. -/
theorem strengthenExpr_denote {Δ : Ctxt d} {t' : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (Δ ++ t' :: Γ) s) (h : usesSlotExpr e = false)
    (V : Ctxt.Valuation (Δ ++ Γ)) (x : ⟦t'⟧) :
    (strengthenExpr e h).denote V = e.denote (insertAt V x) := by
  unfold strengthenExpr Expr.denote
  simp only []
  rw [strengthenHV_lookupArgs e.args h V x]

/-! ## 5. Denotation preservation (NON-`rfl`)

The transform changes the program (smaller context, fewer/strengthened
bindings), and the two sides denote at *different* valuations (`V` vs.
`V.insertAt x`). They agree only because the dropped binding is never read.
The proof is a structural induction on `Com`, using the `Expr` law at each
binding and the recursion under `.var` (where the prefix grows and the inserted
value commutes through `extend`). -/

/-- **Denotation preservation, general position.** For a slot-free `Com c` and
*any* value `x` of the dropped type, the strengthened program at `V` denotes
exactly what the original denotes at `V` with `x` inserted at the dead slot. -/
theorem removeDead_denote :
    {Δ : Ctxt d} → {t' : d.Ty} → {Γ : Ctxt d} → {τ : d.Ty} →
    (c : Com d (Δ ++ t' :: Γ) τ) → (h : usesSlotCom c = false) →
    (V : Ctxt.Valuation (Δ ++ Γ)) → (x : ⟦t'⟧) →
    (removeDead c h).denote V = c.denote (insertAt V x)
  | _,  _, _, _, .ret v, h, V, x => by
      have hv : usesSlotVar v = false := by rwa [usesSlotCom_ret] at h
      show (removeDead (Com.ret v) h).denote V = (Com.ret v).denote (insertAt V x)
      rw [removeDead]
      show (Ctxt.Var.lookup (strengthenVar v hv) V) = (Com.ret v).denote (insertAt V x)
      rw [Com.denote]
      exact strengthenVar_lookup v hv V x
  | Δ, t', Γ, _, .var (t := s) e body, h, V, x => by
      have he : usesSlotExpr e = false := by
        rw [usesSlotCom_var, Bool.or_eq_false_iff] at h; exact h.1
      have hb : usesSlotCom (Δ := s :: Δ) body = false := by
        rw [usesSlotCom_var, Bool.or_eq_false_iff] at h; exact h.2
      -- Unfold one step of the transform and the denotation.
      rw [removeDead]
      show (removeDead (Δ := s :: Δ) (t' := t') (Γ := Γ) body hb).denote
              (V.extend ((strengthenExpr e he).denote V))
            = (Com.var e body).denote (insertAt V x)
      rw [Com.denote]
      -- The bound value agrees up to the inserted `x`.
      rw [strengthenExpr_denote e he V x]
      -- Recurse under the binding. The prefix grows to `s :: Δ`, where
      -- `insertAt (V.extend w) x = (insertAt V x).extend w` definitionally.
      have IH := removeDead_denote (Δ := s :: Δ) (t' := t') (Γ := Γ) body hb
                   (V.extend (e.denote (insertAt V x))) x
      rw [IH]
      rfl
  termination_by _ _ _ _ c _ _ _ => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-! ## 6. Scoped, user-facing case: dropping the OUTERMOST dead binding

The cleanest instance: `Δ = []`. Here the dead slot is the head variable
`.here` introduced by the outermost `.var`, and `removeDeadHead` drops it. -/

/-- Does the body of an outermost binding read its freshly bound variable? -/
abbrev bodyUsesHead {t' : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (body : Com d (t' :: Γ) τ) : Bool :=
  usesSlotCom (Δ := []) body

/-- **Remove the outermost dead `.var`.** Given a body that provably does not
read its head variable, drop the binding and re-type the body under the smaller
context `Γ`. This changes the context `t' :: Γ ↝ Γ`. -/
def removeDeadHead {t' : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (body : Com d (t' :: Γ) τ) (h : bodyUsesHead body = false) : Com d Γ τ :=
  removeDead (Δ := []) (t' := t') (Γ := Γ) body h

/-- **Outermost preservation (NON-`rfl`).** The strengthened body denotes, at
`V`, exactly what the original body denotes at `V` extended by an *arbitrary*
value `x` for the dropped head slot — the head value is irrelevant because the
body never reads it. -/
theorem removeDeadHead_denote {t' : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (body : Com d (t' :: Γ) τ) (h : bodyUsesHead body = false)
    (V : Ctxt.Valuation Γ) (x : ⟦t'⟧) :
    (removeDeadHead body h).denote V = body.denote (V.extend x) := by
  unfold removeDeadHead
  have := removeDead_denote (Δ := []) (t' := t') (Γ := Γ) body h V x
  simpa [insertAt, Ctxt.Valuation.extend] using this

/-! ## 7. End-to-end: run the deadness check, then eliminate

`dceOutermost` is total: it inspects the outermost binding and, when its head
variable is provably dead, returns the smaller program; otherwise it
leaves the program unchanged. The preservation theorem covers the eliminating
branch — the branch the identity DCE never reaches. -/

/-- Run DCE on the outermost binding if it is dead; otherwise return the program
unchanged (re-wrapped at the same type). The first projection records whether an
elimination actually happened. -/
def dceOutermost {t' : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (c : Com d (t' :: Γ) τ) : Bool × Σ' Γ', Com d Γ' τ :=
  if h : bodyUsesHead c = false then
    (true, ⟨Γ, removeDeadHead c h⟩)
  else
    (false, ⟨t' :: Γ, c⟩)

/-- When `dceOutermost` fires (the head is dead), its output is the eliminated
program and denotes the same function as the input under any inserted head
value. This is the user-facing wrapper around `removeDeadHead_denote`. -/
theorem dceOutermost_eliminates_denote {t' : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (c : Com d (t' :: Γ) τ) (h : bodyUsesHead c = false)
    (V : Ctxt.Valuation Γ) (x : ⟦t'⟧) :
    (removeDeadHead c h).denote V = c.denote (V.extend x) :=
  removeDeadHead_denote c h V x

/-! ## 8. A concrete worked example (the transform really removes a binding)

A self-contained one-type, two-op toy dialect over `Nat`, on which we exhibit a
program with a dead outermost binding, run `removeDeadHead`, and check
(via `comLen`) that the result has **one fewer** binding — the elimination is
real, not the identity. We also confirm the denotation agrees for an arbitrary
dead value. -/

namespace Demo

/-- A toy dialect: a single value type, a `const` op (nullary) and a `dbl`
op (unary, doubles its argument). -/
inductive ToyOp where
  | const (n : Nat)
  | dbl
  deriving DecidableEq

def toyDialect : Dialect where
  Op := ToyOp
  Ty := Unit

instance : TyDenote toyDialect.Ty where
  denote _ := Nat

instance : DialectSignature toyDialect where
  sig | .const _ => [] | .dbl => [()]
  ret _ := ()

instance : DialectDenote toyDialect where
  denote
    | .const n, _                  => n
    | .dbl,     .cons (a : Nat) .nil => a + a

/-- The **body** of a binding whose head variable (`dead`, the freshly bound
value at de Bruijn `0`) is never read:

```
-- context here is `dead :: []`, i.e. one live slot for the dead value
let live = const 7      -- ignores `dead`
ret live                -- returns `const 7`, not `dead`
```

`deadBody : Com toy [()] ()`: the head `()` is the to-be-removed dead slot. The
body binds `const 7` (no args) and returns it, never touching `dead`. So
`removeDeadHead` can drop the dead slot and re-type the body under `[]`. -/
def deadBody : Com toyDialect [()] () :=
  .var { op := .const 7, retTy_eq := rfl, args := .nil }
    (.ret .here)

/-- The body has one binding (`const 7`). -/
example : comLen deadBody = 1 := rfl

/-- The head variable (the dead slot) is unused, so the check passes. -/
example : bodyUsesHead deadBody = false := by native_decide

/-- **The transform changes the program:** `removeDeadHead` re-types
`deadBody : Com toy [()] ()` to a program over the *smaller* context `[]` — the
dead slot is gone. (The binding count is unchanged here because the dropped slot
was an input slot, not one of `deadBody`'s own `.var`s; the *context* shrinks
from `[()]` to `[]`, which is the elimination.) -/
example :
    comLen (removeDeadHead deadBody (by native_decide)) = 1 := by native_decide

/-- Denotation preservation on this concrete program: the eliminated program
(now closed, over context `[]`) agrees with the original under *any* value `x`
for the dropped slot — the slot is never read. -/
example (h : bodyUsesHead deadBody = false) (x : Nat) :
    (removeDeadHead deadBody h).denote .nil
      = deadBody.denote (HVector.cons x .nil) :=
  removeDeadHead_denote deadBody h .nil x

/-- The full picture: a complete closed program whose **outermost** binding is
dead. `let dead = const 42; <deadBody>` — the `const 42` result is never read by
`deadBody`. DCE rewrites `.var e body ↝ removeDeadHead body h`, dropping the
binding. -/
def fullProg : Com toyDialect [] () :=
  .var { op := .const 42, retTy_eq := rfl, args := .nil } deadBody

/-- The full program has **two** bindings (`const 42`, `const 7`). -/
example : comLen fullProg = 2 := rfl

/-- After eliminating the dead outermost binding, **one** binding remains: the
binder count drops `2 → 1`, and the result denotes the same value. -/
example : comLen (removeDeadHead deadBody (by native_decide)) = 1 := by native_decide

/-- DCE preserves `fullProg`'s denotation: dropping `const 42` (the dead head
binding) leaves the meaning unchanged. -/
example : (removeDeadHead deadBody (by native_decide)).denote .nil
            = fullProg.denote .nil :=
  removeDeadHead_denote deadBody (by native_decide) .nil
    (Expr.denote { op := .const 42, retTy_eq := rfl, args := .nil } .nil)

-- `#eval`: the eliminated closed program denotes `7` (the `const`), independent
-- of the dropped slot. The original at dead-slot value `5` denotes the same `7`.
#eval (removeDeadHead deadBody (by native_decide)).denote .nil  -- 7
#eval deadBody.denote (HVector.cons (5 : Nat) .nil)             -- 7
#eval fullProg.denote .nil                                      -- 7

end Demo

end CatCrypt.Crypto.SecureCompilation.VIR.DCEReal
