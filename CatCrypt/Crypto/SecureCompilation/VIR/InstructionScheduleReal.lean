/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# A genuine instruction-scheduling pass for `Com` (real transform)

`InstructionSchedule.lean` ships an *analysis-as-labelling* scheduler whose
`Com → Com` rewrite is the identity (`applySchedule = fun p _ => p`), so its
preservation theorems are `rfl` and verify nothing about an actual reorder.
This file supplies what that one defers: a **structural** `Com → Com` transform
that genuinely *reorders two adjacent independent bindings*, together with a
**non-`rfl`** denotation-preservation proof by induction over the `Com`.

This mirrors `DeadCodeElimReal.lean` and `CommonSubexprElimReal.lean` (the
proven templates): there the transform dropped / merged a binding via a de
Bruijn strengthening / substitution; here the transform **swaps** two adjacent
binders via a de Bruijn 2-slot swap.

## The transform

Consider two **adjacent** bindings whose second is **independent** of the first:

```
let v1 = e1       -- e1 : Expr d Γ t1,           binds v1 : t1
let v2 = e2       -- e2 : Expr d (t1 :: Γ) t2,   binds v2 : t2
<body>            -- body : Com d (t2 :: t1 :: Γ) τ
```

`v2 = e2` is **independent of `v1`** exactly when `e2` never reads `v1` — i.e.
`e2` never uses the de Bruijn variable `.here` of `t1 :: Γ`. Then `e2` can be
re-typed under the smaller context `Γ` (strengthening away the unused `t1`
slot), giving `e2' : Expr d Γ t2`. Now `e2'` can be emitted **first**:

```
let v2 = e2'      -- e2' : Expr d Γ t2,           binds v2 : t2
let v1 = e1'      -- e1' : Expr d (t2 :: Γ) t1,   binds v1 : t1  (e1, shifted)
<body'>           -- body' : Com d (t1 :: t2 :: Γ) τ  (body, top-2 slots swapped)
```

* `e1'` is `e1` with every argument variable shifted up by one `.there` (it now
  reads its originating slots one binder deeper, since `v2` was inserted below).
* `body'` is `body` with the top two slots **swapped** — every use of `v2`
  (`.here` in `t2 :: t1 :: Γ`) becomes `v2` at its new depth, every use of `v1`
  (`.there .here`) becomes `v1` at its new depth, deeper uses unchanged.

This is a genuine reorder: the two binders change places, and the body's de
Bruijn indices are renumbered through a 2-slot swap. It is **not** the identity.

## The proof (genuinely not `rfl`)

The keystone is

  `swapBody_denote`:
    `(swapCom body).denote (swap V) = body.denote V`

where `swap V` exchanges the values at the top two slots. The transformed body
sees a valuation with the two slots swapped — matching its swapped indices — so
it computes the same final result. The proof is a structural induction on
`body` (peeling each `.var`), threaded through the matching swap laws on
`Var` / `HVector` / `Expr`. It is **not** `rfl`: the transform changes the
program's context shape and the two sides denote at *different* valuations
(`V` vs. the slot-swapped `swap V`) that agree only because each renumbered
variable lands on the slot now holding its old value.

## What is general vs. scoped

* **General:** the swap (`swapVar`, `swapHV`, `swapExpr`, `swapCom`) and the
  lookup/denotation laws (`swapVar_lookup`, `swapCom_denote`) work at an
  arbitrary de Bruijn position `|Δ|`, for any dialect, exchanging the slots at
  depths `|Δ|` and `|Δ| + 1`.
* **Scoped to the cleanest case:** `scheduleSwap` / `scheduleSwap_denote`
  specialise to `Δ = []` and bundle the independence-strengthening of `e2`. The
  user-facing `scheduleSwap` runs on `.var e1 (.var e2 body)`, checks the
  independence hypothesis (`e2` does not read `v1`), and returns the genuinely
  reordered `.var e2' (.var e1' body')` with the preservation theorem
  `scheduleSwap_denote`.
-/

set_option autoImplicit false
-- Several equation/lookup lemmas legitimately do not use every ambient
-- typeclass section variable (`TyDenote`/`DialectSignature`); silence the
-- section-variable linter rather than thread per-theorem `omit` clauses.
set_option linter.unusedSectionVars false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ScheduleReal

open CatCrypt.Crypto.SecureCompilation.VIR

variable {d : Dialect} [TyDenote d.Ty]

/-! ## 0. A structural length measure on `Com`

`swapCom` / `swapCom_denote` recurse on a `Com` whose *index* (the context)
changes at each step, so Lean cannot infer structural recursion and falls back
to well-founded recursion. We supply an explicit, plainly-structural length
measure and use it as the `termination_by` measure (cf. `DeadCodeElimReal`,
`CommonSubexprElimReal`). -/

/-- Number of `.var` bindings in a `Com` (a structural `Nat` measure). -/
def comLen [DialectSignature d] {Γ₀ : Ctxt d} {τ₀ : d.Ty} : Com d Γ₀ τ₀ → Nat
  | .ret _      => 0
  | .var _ body => comLen body + 1

/-! ## 1. The 2-slot variable swap

We work with a context split as `Δ ++ t2 :: t1 :: Γ`; the two slots to swap
are the `t2` at depth `|Δ|` and the `t1` at depth `|Δ| + 1`. A variable
`Var (Δ ++ t2 :: t1 :: Γ) s`:

* points *into* `Δ` (depth `< |Δ|`)            → survives unchanged;
* points *at* the top slot (depth `= |Δ|`)     → moves to depth `|Δ| + 1`;
* points *at* the next slot (depth `= |Δ| + 1`)→ moves to depth `|Δ|`;
* points *past* both (depth `> |Δ| + 1`)       → survives unchanged.

`swapVar` produces the re-typed variable over the swapped context
`Δ ++ t1 :: t2 :: Γ`. -/

/-- Swap the two slots at depths `|Δ|` and `|Δ| + 1` for a variable. -/
def swapVar : {Δ : Ctxt d} → {t1 t2 : d.Ty} → {Γ : Ctxt d} → {s : d.Ty} →
    Ctxt.Var (Δ ++ t2 :: t1 :: Γ) s → Ctxt.Var (Δ ++ t1 :: t2 :: Γ) s
  -- Δ = []: the head two slots are exactly the pair to swap.
  | [],     _,  _,  _, _, .here          => .there .here   -- top slot ↝ second
  | [],     _,  _,  _, _, .there .here   => .here          -- second slot ↝ top
  | [],     _,  _,  _, _, .there (.there v) => .there (.there v)  -- deeper, unchanged
  -- Δ = _ :: _: descend, keeping the head slot.
  | _ :: _, _,  _,  _, _, .here          => .here
  | _ :: _, t1, t2, Γ, _, .there v        =>
      .there (swapVar (Δ := _) (t1 := t1) (t2 := t2) (Γ := Γ) v)

/-! ## 2. The swap lifted over `HVector` of variables, `Expr`, `Com` -/

/-- Swap every variable in an `HVector`. -/
def swapHV {Δ : Ctxt d} {t1 t2 : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var (Δ ++ t2 :: t1 :: Γ) ty) tys →
    HVector (fun ty => Ctxt.Var (Δ ++ t1 :: t2 :: Γ) ty) tys
  | [],     .nil        => .nil
  | _ :: _, .cons v rest => .cons (swapVar v) (swapHV rest)

variable [DialectSignature d]

/-- Swap an `Expr`'s argument variables. -/
def swapExpr {Δ : Ctxt d} {t1 t2 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (Δ ++ t2 :: t1 :: Γ) s) : Expr d (Δ ++ t1 :: t2 :: Γ) s :=
  { op := e.op, retTy_eq := e.retTy_eq, args := swapHV e.args }

/-- Swap a whole `Com`, exchanging the two slots at depths `|Δ|` and `|Δ| + 1`.
The recursion grows the prefix `Δ` by each freshly bound type as it descends
under a `.var`. -/
def swapCom : {Δ : Ctxt d} → {t1 t2 : d.Ty} → {Γ : Ctxt d} → {τ : d.Ty} →
    Com d (Δ ++ t2 :: t1 :: Γ) τ → Com d (Δ ++ t1 :: t2 :: Γ) τ
  | _,  _,  _,  _, _, .ret v         => .ret (swapVar v)
  | Δ, t1, t2, Γ, _, .var (t := s) e body =>
      .var (swapExpr e)
           (swapCom (Δ := s :: Δ) (t1 := t1) (t2 := t2) (Γ := Γ) body)
  termination_by _ _ _ _ _ c => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-- Equation lemma: `swapCom` on a `ret`. -/
@[simp] theorem swapCom_ret {Δ : Ctxt d} {t1 t2 : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (v : Ctxt.Var (Δ ++ t2 :: t1 :: Γ) τ) :
    swapCom (Com.ret v) = Com.ret (swapVar v) := by
  rw [swapCom]

/-- Equation lemma: `swapCom` on a `var`. -/
@[simp] theorem swapCom_var {Δ : Ctxt d} {t1 t2 : d.Ty} {Γ : Ctxt d}
    {s τ : d.Ty} (e : Expr d (Δ ++ t2 :: t1 :: Γ) s)
    (body : Com d (s :: (Δ ++ t2 :: t1 :: Γ)) τ) :
    swapCom (Com.var e body) =
      Com.var (swapExpr e)
        (swapCom (Δ := s :: Δ) (t1 := t1) (t2 := t2) (Γ := Γ) body) := by
  rw [swapCom]

/-! ## 3. The "swapped valuation"

To state preservation we need, for the original valuation
`W : Valuation (Δ ++ t2 :: t1 :: Γ)`, the swapped valuation
`swapVal W : Valuation (Δ ++ t1 :: t2 :: Γ)` that exchanges the two top values.
The preservation law says the swapped program at `swapVal W` denotes exactly
what the original denotes at `W`: each renumbered variable lands on the slot
now holding its old value. -/

/-- The swapped valuation: exchange the values at depths `|Δ|` and `|Δ| + 1`. -/
def swapVal : {Δ : Ctxt d} → {t1 t2 : d.Ty} → {Γ : Ctxt d} →
    Ctxt.Valuation (Δ ++ t2 :: t1 :: Γ) → Ctxt.Valuation (Δ ++ t1 :: t2 :: Γ)
  | [],     _,  _,  _, .cons a (.cons b V) => .cons b (.cons a V)
  | _ :: _, t1, t2, Γ, .cons v V => .cons v (swapVal (Δ := _) (t1 := t1) (t2 := t2) (Γ := Γ) V)

/-! ## 4. The swap laws (lookups agree)

The genuine inductive lemmas: looking up a swapped variable in `swapVal W`
equals looking up the original variable in `W`. The two top slots hold each
other's values in `swapVal W`, so the index swap is exactly compensated. -/

/-- **Variable law.** A swapped variable looks up the same value in `swapVal W`
(via its swap) as the original does in `W`. -/
theorem swapVar_lookup :
    {Δ : Ctxt d} → {t1 t2 : d.Ty} → {Γ : Ctxt d} → {s : d.Ty} →
    (v : Ctxt.Var (Δ ++ t2 :: t1 :: Γ) s) →
    (W : Ctxt.Valuation (Δ ++ t2 :: t1 :: Γ)) →
    (swapVar v).lookup (swapVal W) = v.lookup W
  | [],     _,  _,  _, _, .here,             .cons a (.cons b V) => by
      rw [swapVar, swapVal]; rfl
  | [],     _,  _,  _, _, .there .here,      .cons a (.cons b V) => by
      rw [swapVar, swapVal]; rfl
  | [],     _,  _,  _, _, .there (.there v), .cons a (.cons b V) => by
      rw [swapVar, swapVal]; rfl
  | _ :: _, _,  _,  _, _, .here,             .cons u W => by
      rw [swapVar, swapVal]; rfl
  | _ :: _, t1, t2, Γ, _, .there v,          .cons u W => by
      rw [swapVar, swapVal]
      show (swapVar v).lookup (swapVal W) = v.lookup W
      exact swapVar_lookup (Δ := _) (t1 := t1) (t2 := t2) (Γ := Γ) v W

/-- **HVector law.** Resolving a swapped `HVector` against `swapVal W` yields the
same heterogeneous vector as the original against `W`. -/
theorem swapHV_lookupArgs {Δ : Ctxt d} {t1 t2 : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} →
    (vs : HVector (fun ty => Ctxt.Var (Δ ++ t2 :: t1 :: Γ) ty) tys) →
    (W : Ctxt.Valuation (Δ ++ t2 :: t1 :: Γ)) →
    Expr.lookupArgs (swapHV vs) (swapVal W) = Expr.lookupArgs vs W
  | [],     .nil,         _ => by simp [swapHV, Expr.lookupArgs]
  | _ :: _, .cons v rest, W => by
      simp only [swapHV, Expr.lookupArgs]
      rw [swapVar_lookup v W, swapHV_lookupArgs rest W]

variable [DialectDenote d]

/-- **Expr law.** A swapped `Expr` denotes the same value at `swapVal W` as the
original at `W`. -/
theorem swapExpr_denote {Δ : Ctxt d} {t1 t2 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (Δ ++ t2 :: t1 :: Γ) s)
    (W : Ctxt.Valuation (Δ ++ t2 :: t1 :: Γ)) :
    (swapExpr e).denote (swapVal W) = e.denote W := by
  unfold swapExpr Expr.denote
  simp only []
  rw [swapHV_lookupArgs e.args W]

/-! ## 5. The keystone: denotation preservation of the swap (NON-`rfl`)

The swapped program at `swapVal W` denotes the same function as the original at
`W`. The two valuations exchange the two top slots, and the body's swapped
indices land back on those values. Structural induction on `Com`. -/

/-- **Swap preservation, general position.** -/
theorem swapCom_denote :
    {Δ : Ctxt d} → {t1 t2 : d.Ty} → {Γ : Ctxt d} → {τ : d.Ty} →
    (c : Com d (Δ ++ t2 :: t1 :: Γ) τ) →
    (W : Ctxt.Valuation (Δ ++ t2 :: t1 :: Γ)) →
    (swapCom c).denote (swapVal W) = c.denote W
  | _,  _,  _,  _, _, .ret v, W => by
      show (swapCom (Com.ret v)).denote (swapVal W) = (Com.ret v).denote W
      rw [swapCom_ret]
      show (swapVar v).lookup (swapVal W) = (Com.ret v).denote W
      rw [Com.denote]
      exact swapVar_lookup v W
  | Δ, t1, t2, Γ, _, .var (t := s) e body, W => by
      rw [swapCom_var]
      show (swapCom (Δ := s :: Δ) (t1 := t1) (t2 := t2) (Γ := Γ) body).denote
              ((swapVal W).extend ((swapExpr e).denote (swapVal W)))
            = (Com.var e body).denote W
      rw [Com.denote]
      rw [swapExpr_denote e W]
      -- Recurse under the binding. The prefix grows to `s :: Δ`, where
      -- `swapVal (W.extend u) = (swapVal W).extend u` definitionally.
      have IH := swapCom_denote (Δ := s :: Δ) (t1 := t1) (t2 := t2) (Γ := Γ) body
                   (W.extend (e.denote W))
      exact IH
  termination_by _ _ _ _ _ c _ => comLen c
  decreasing_by all_goals (simp_wf; simp [comLen])

/-! ## 6. Strengthening the independent second expression

For the scoped user-facing reorder we must move `e2 : Expr d (t1 :: Γ) t2`
down to `e2' : Expr d Γ t2`, which is well-typed exactly when `e2` does not
read the head slot `v1`. We reuse the same head-slot machinery as
`DeadCodeElimReal`, specialised here to the outermost slot (`Δ = []`). -/

/-- Does this variable point at the outermost slot (`.here`)? -/
def usesHeadVar {t1 : d.Ty} {Γ : Ctxt d} {s : d.Ty} :
    Ctxt.Var (t1 :: Γ) s → Bool
  | .here     => true
  | .there _  => false

/-- Strengthen a variable that does **not** point at the head slot. -/
def strengthenHeadVar {t1 : d.Ty} {Γ : Ctxt d} {s : d.Ty} :
    (v : Ctxt.Var (t1 :: Γ) s) → usesHeadVar v = false → Ctxt.Var Γ s
  | .here,    h => by simp [usesHeadVar] at h
  | .there v, _ => v

/-- A whole `HVector` of variables is head-free when every entry is. -/
def usesHeadHV {t1 : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var (t1 :: Γ) ty) tys → Bool
  | [],     .nil        => false
  | _ :: _, .cons v rest => usesHeadVar v || usesHeadHV rest

/-- Strengthen a head-free `HVector`. -/
def strengthenHeadHV {t1 : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → (vs : HVector (fun ty => Ctxt.Var (t1 :: Γ) ty) tys) →
    usesHeadHV vs = false → HVector (fun ty => Ctxt.Var Γ ty) tys
  | [],     .nil,         _ => .nil
  | _ :: _, .cons v rest, h =>
      .cons (strengthenHeadVar v (by
              have := h; simp only [usesHeadHV, Bool.or_eq_false_iff] at this; exact this.1))
            (strengthenHeadHV rest (by
              have := h; simp only [usesHeadHV, Bool.or_eq_false_iff] at this; exact this.2))

/-- An `Expr` is head-free when its argument `HVector` is. -/
def usesHeadExpr {t1 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (t1 :: Γ) s) : Bool :=
  usesHeadHV e.args

/-- Strengthen a head-free `Expr` from `t1 :: Γ` down to `Γ`. -/
def strengthenHeadExpr {t1 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (t1 :: Γ) s) (h : usesHeadExpr e = false) : Expr d Γ s :=
  { op := e.op, retTy_eq := e.retTy_eq, args := strengthenHeadHV e.args h }

/-! ## 7. Strengthening laws (lookups agree)

Looking up a head-strengthened variable in `V` equals looking up the original
in `V.extend x` for *any* head value `x` — a head-free variable never lands on
the head slot. -/

/-- **Variable law.** -/
theorem strengthenHeadVar_lookup {t1 : d.Ty} {Γ : Ctxt d} {s : d.Ty} :
    (v : Ctxt.Var (t1 :: Γ) s) → (h : usesHeadVar v = false) →
    (V : Ctxt.Valuation Γ) → (x : ⟦t1⟧) →
    (strengthenHeadVar v h).lookup V = v.lookup (V.extend x)
  | .here,    h, _, _ => by simp [usesHeadVar] at h
  | .there v, _, V, x => by rw [strengthenHeadVar]; rfl

/-- **HVector law.** -/
theorem strengthenHeadHV_lookupArgs {t1 : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} →
    (vs : HVector (fun ty => Ctxt.Var (t1 :: Γ) ty) tys) →
    (h : usesHeadHV vs = false) →
    (V : Ctxt.Valuation Γ) → (x : ⟦t1⟧) →
    Expr.lookupArgs (strengthenHeadHV vs h) V = Expr.lookupArgs vs (V.extend x)
  | [],     .nil,         _, _, _ => by simp [strengthenHeadHV, Expr.lookupArgs]
  | _ :: _, .cons v rest, h, V, x => by
      simp only [strengthenHeadHV, Expr.lookupArgs]
      have h1 : usesHeadVar v = false := by
        simp only [usesHeadHV, Bool.or_eq_false_iff] at h; exact h.1
      have h2 : usesHeadHV rest = false := by
        simp only [usesHeadHV, Bool.or_eq_false_iff] at h; exact h.2
      rw [strengthenHeadVar_lookup v h1 V x, strengthenHeadHV_lookupArgs rest h2 V x]

/-- **Expr law.** A head-free `Expr` denotes the same value at `V` (after
strengthening) as the original at `V.extend x`, for any head value `x`. -/
theorem strengthenHeadExpr_denote {t1 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d (t1 :: Γ) s) (h : usesHeadExpr e = false)
    (V : Ctxt.Valuation Γ) (x : ⟦t1⟧) :
    (strengthenHeadExpr e h).denote V = e.denote (V.extend x) := by
  unfold strengthenHeadExpr Expr.denote
  simp only []
  rw [strengthenHeadHV_lookupArgs e.args h V x]

/-! ## 8. Shifting the first expression up by one slot

`e1 : Expr d Γ t1` must become `e1' : Expr d (t2 :: Γ) t1` once `v2` is inserted
below it. This is the standard weakening: shift every argument variable up by
one `.there`. -/

/-- Weaken a variable by one slot at the head. -/
def weakenHeadVar {t2 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (v : Ctxt.Var Γ s) : Ctxt.Var (t2 :: Γ) s := .there v

/-- Weaken an `HVector` of variables by one head slot. -/
def weakenHeadHV {t2 : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (t2 :: Γ) ty) tys
  | [],     .nil        => .nil
  | _ :: _, .cons v rest => .cons (weakenHeadVar v) (weakenHeadHV rest)

/-- Weaken an `Expr` by one head slot. -/
def weakenHeadExpr {t2 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d Γ s) : Expr d (t2 :: Γ) s :=
  { op := e.op, retTy_eq := e.retTy_eq, args := weakenHeadHV e.args }

/-- **HVector weakening law.** A weakened `HVector` looked up in `V.extend u`
equals the original in `V`. -/
theorem weakenHeadHV_lookupArgs {t2 : d.Ty} {Γ : Ctxt d} :
    {tys : List d.Ty} → (vs : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (V : Ctxt.Valuation Γ) → (u : ⟦t2⟧) →
    Expr.lookupArgs (weakenHeadHV (t2 := t2) vs) (V.extend u) = Expr.lookupArgs vs V
  | [],     .nil,         _, _ => by simp [weakenHeadHV, Expr.lookupArgs]
  | _ :: _, .cons v rest, V, u => by
      simp only [weakenHeadHV, Expr.lookupArgs, weakenHeadVar]
      rw [weakenHeadHV_lookupArgs rest V u]
      rfl

/-- **Expr weakening law.** A weakened `Expr` denotes at `V.extend u` exactly
what the original denotes at `V`. -/
theorem weakenHeadExpr_denote {t2 : d.Ty} {Γ : Ctxt d} {s : d.Ty}
    (e : Expr d Γ s) (V : Ctxt.Valuation Γ) (u : ⟦t2⟧) :
    (weakenHeadExpr (t2 := t2) e).denote (V.extend u) = e.denote V := by
  unfold weakenHeadExpr Expr.denote
  simp only []
  rw [weakenHeadHV_lookupArgs e.args V u]

/-! ## 9. Scoped, user-facing case: swapping two adjacent independent bindings

`Δ = []`. Given `.var e1 (.var e2 body)` where `e2` is independent of `v1`
(`usesHeadExpr e2 = false`), produce the reordered
`.var e2' (.var e1' body')` and prove it denotes the same function. -/

/-- **Reorder two adjacent independent bindings.** Given
`.var e1 (.var e2 body)` over `Γ` with `e2` independent of the first binding
(`usesHeadExpr e2 = false`), emit `e2` first (strengthened to `Γ`), then `e1`
(weakened over the new slot), then the body with its top two slots swapped. -/
def scheduleSwap {t1 t2 : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (e1 : Expr d Γ t1) (e2 : Expr d (t1 :: Γ) t2)
    (body : Com d (t2 :: t1 :: Γ) τ) (h : usesHeadExpr e2 = false) :
    Com d Γ τ :=
  Com.var (strengthenHeadExpr e2 h)
    (Com.var (weakenHeadExpr (t2 := t2) e1)
      (swapCom (Δ := []) (t1 := t1) (t2 := t2) (Γ := Γ) body))

/-- **Reorder preservation (NON-`rfl`).** When `e2` is independent of `v1`
(`usesHeadExpr e2 = false`), the reordered program `scheduleSwap e1 e2 body h`
denotes the same function as the original `Com.var e1 (Com.var e2 body)`. -/
theorem scheduleSwap_denote {t1 t2 : d.Ty} {Γ : Ctxt d} {τ : d.Ty}
    (e1 : Expr d Γ t1) (e2 : Expr d (t1 :: Γ) t2)
    (body : Com d (t2 :: t1 :: Γ) τ) (h : usesHeadExpr e2 = false)
    (V : Ctxt.Valuation Γ) :
    (scheduleSwap e1 e2 body h).denote V
      = (Com.var e1 (Com.var e2 body)).denote V := by
  -- Original: extend by `v1 := e1.denote V`, then `v2 := e2.denote (V.extend v1)`,
  -- then `body.denote ((V.extend v1).extend v2)`.
  -- Reordered: extend by `v2' := e2'.denote V`, then `v1' := e1'.denote (V.extend v2')`,
  -- then `(swapCom body).denote ((V.extend v2').extend v1')`.
  unfold scheduleSwap
  rw [Com.denote, Com.denote, Com.denote, Com.denote]
  -- Let `v1 = e1.denote V`, `v2 = e2.denote (V.extend v1)`.
  -- `e2'.denote V = e2.denote (V.extend v1)` (strengthen, any head value v1).
  rw [strengthenHeadExpr_denote e2 h V (e1.denote V)]
  -- `e1'.denote (V.extend v2) = e1.denote V` (weaken).
  rw [weakenHeadExpr_denote e1 V (e2.denote (V.extend (e1.denote V)))]
  -- Now the bodies: the reordered side is
  --   (swapCom body).denote ((V.extend v2).extend v1)
  -- which by the swap keystone (Δ = []) equals
  --   body.denote ((V.extend v1).extend v2) = original body side.
  have hswap := swapCom_denote (Δ := []) (t1 := t1) (t2 := t2) (Γ := Γ) body
                  ((V.extend (e1.denote V)).extend (e2.denote (V.extend (e1.denote V))))
  -- `swapVal (Δ := []) ((V.extend v1).extend v2) = (V.extend v2).extend v1`.
  simpa [swapVal, Ctxt.Valuation.extend] using hswap

/-! ## 10. A concrete worked example (the transform really reorders two binders)

A self-contained one-type, two-op toy dialect over `Nat`, on which we exhibit a
program with two adjacent independent bindings, run `scheduleSwap`, and confirm
the two binders swapped places (the emitted program is *not* the input) while
the denotation is preserved. -/

namespace Demo

/-- A toy dialect: a single value type, a `const` op (nullary) and an `addHead`
op (unary, adds 1 to its argument — used to make the two binders distinct). -/
inductive ToyOp where
  | const (n : Nat)
  | incr
  deriving DecidableEq

def toyDialect : Dialect where
  Op := ToyOp
  Ty := Unit

instance : TyDenote toyDialect.Ty where
  denote _ := Nat

instance : DialectSignature toyDialect where
  sig | .const _ => [] | .incr => [()]
  ret _ := ()

instance : DialectDenote toyDialect where
  denote
    | .const n, _                  => n
    | .incr,    .cons (a : Nat) .nil => a + 1

/-- `e1 = const 10` over `Γ = []` (binds `v1`). -/
def e1 : Expr toyDialect [] () :=
  { op := .const 10, retTy_eq := rfl, args := .nil }

/-- `e2 = const 20` over `() :: []` (binds `v2`). It reads no variables, so it
is independent of `v1`. -/
def e2 : Expr toyDialect [()] () :=
  { op := .const 20, retTy_eq := rfl, args := .nil }

/-- `e2` is independent of `v1` (it has no arguments at all). -/
example : ScheduleReal.usesHeadExpr e2 = false := by native_decide

/-- The body returns `v1` (`.there .here` in `() :: () :: []` — the second slot).
After the swap, this use is renumbered to track `v1`'s new position. -/
def body : Com toyDialect [(), ()] () :=
  .ret (.there .here)

/-- The original program:
```
let v1 = const 10   -- e1
let v2 = const 20   -- e2 (independent of v1)
ret v1
```
-/
def origProg : Com toyDialect [] () :=
  .var e1 (.var e2 body)

/-- The reordered program emits `e2` (= `const 20`) first, then `e1`. The
*outermost expression genuinely changes* from `const 10` to `const 20`: the two
binders swapped places. This is a real reorder, not the identity. -/
example :
    ScheduleReal.scheduleSwap e1 e2 body (by native_decide)
      = Com.var
          { op := ToyOp.const 20, retTy_eq := rfl, args := .nil }
          (Com.var { op := ToyOp.const 10, retTy_eq := rfl, args := .nil }
            (Com.ret .here)) := by
  unfold ScheduleReal.scheduleSwap e1 e2 body
  rw [ScheduleReal.swapCom.eq_def]
  rfl

/-- The reorder preserves denotation: returning `v1` (= `10`) is unchanged by
emitting `v2` first. -/
example (V : Ctxt.Valuation (d := toyDialect) []) :
    (ScheduleReal.scheduleSwap e1 e2 body (by native_decide)).denote V
      = origProg.denote V :=
  ScheduleReal.scheduleSwap_denote e1 e2 body (by native_decide) V

-- `#eval`: both the reordered and original program denote `10` (the value of
-- `v1`), confirming the swap is observationally invisible.
#eval (ScheduleReal.scheduleSwap e1 e2 body (by native_decide)).denote .nil  -- 10
#eval origProg.denote .nil                                                   -- 10

end Demo

end CatCrypt.Crypto.SecureCompilation.VIR.ScheduleReal
