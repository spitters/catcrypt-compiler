/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph
public import CatCrypt.Crypto.SecureCompilation.VIR.ComVarDepth

/-!
# Verified dead-let elimination for `Com` — a denotation-preserving rewrite

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A **structural `Com → Com` dead-binding-elimination pass** over the typed VIR
framework. It is the `Com`-level rewrite that the analysis-only
`SecureCompilation/VIR/DeadCodeElim.lean` left as the documented residual: that
file decides *which* binders are dead but applies the identity transform at the
`Com` level (deadness is consumed downstream as a labelling). Here the rewrite
actually deletes a dead let-binding and re-checks the result type, with a real
denotation-preservation proof (an induction over the let-chain, **not** `rfl`).

## The De Bruijn obstruction and our sound scope

`Com d Γ t` is intrinsically typed: a binder introduces a fresh type at the head
of the context, and every variable below it is a `Ctxt.Var` De Bruijn index.
Removing an *interior* binding changes the intrinsic type of the body — every
subsequent `.there` index would need to shift, and binders nested below the
dead one would have to be exchanged past it (a full context-permutation /
reindexing layer).

We take the sound scope that needs **no interior reindex**: a **trailing dead
binding** — a binder `.var e body` whose `body`, after recursively eliminating
its own trailing dead bindings, is a bare `.ret v` that does *not* read the
binder (`v ≠ .here`). Such a binder feeds a value into a return that ignores it,
so it can be dropped, leaving `.ret v'` where `v'` is `v` with its outermost
index strengthened (the only reindex required, and it is total because `v` is
not `.here`). Running the pass bottom-up peels off *all* trailing dead bindings
in one traversal — e.g.

    let a = …        let a = …
    let b = …    ↦   ret a            (b, c dead: they feed a ret that returns a)
    let c = …
    ret a

Every `jasminDialect` op is pure (effect-free), so deleting a dead binding never
drops an observable effect: denotation is preserved exactly.

## Contents

* `dropVar` — strengthen a variable out of an extended context, defined only on
  non-`.here` indices (`Option`-valued; `none` exactly on `.here`).
* `dropVar_lookup` — the strengthening is lookup-invariant under `extend`.
* `comDCE` — the bottom-up trailing-dead-binding elimination, generic over any
  `Dialect`.
* `comDCE_denote` — **denotation preservation** (`(comDCE c).denote V = c.denote V`),
  by induction over the let-chain. **Not `rfl`.**
* `dceLive` — elimination of every dead binding, interior ones included, in time
  linear in the size of the program: a liveness scan over binding levels and a
  rebuild through a `Thinning`. `dceLive_denote` — denotation preservation.
* `comDCE_cost_le`, `comDCE_ctSafe` — `jasminDialect` corollaries: the pass is
  cost-non-increasing and CT-preserving (the dialect is branch-free).
* Self-contained validation: a program with a dead trailing binder is
  shrunk by the pass while its denotation is preserved.

All goals closed. Axiom set: `propext`, `Quot.sound`,
`Classical.choice` (the standard Lean/Mathlib trio inherited via `Egraph`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComDCE

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open Ctxt (Var)

/-! ## 1. Variable strengthening

Dropping a binder removes the head type `t` from the context. A variable
`Var (t :: Γ) s` strengthens to `Var Γ s` exactly when it is not the dropped
binder itself (i.e. not `.here`). `dropVar` is total into `Option`, returning
`none` precisely on `.here`. -/

/-- Strengthen a variable out of the extended context `t :: Γ`. Returns `none`
exactly when the variable *is* the head binder (`.here`); otherwise peels one
`.there`. -/
def dropVar {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t s : d.Ty} :
    Var (t :: Γ) s → Option (Var Γ s)
  | .here    => none
  | .there v => some v

/-- **Lookup invariance of `dropVar`.** When `dropVar v = some v'`, the value
read for `v` under an extended valuation `V.extend x` is exactly the value read
for the strengthened `v'` under `V` — the dropped binding `x` is never observed.
This is the variable-level core of denotation preservation. -/
theorem dropVar_lookup {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    {Γ : Ctxt d} {t s : d.Ty}
    (v : Var (t :: Γ) s) (v' : Var Γ s) (h : dropVar v = some v')
    (V : Ctxt.Valuation Γ) (x : ⟦t⟧) :
    v.lookup (V.extend x) = v'.lookup V := by
  cases v with
  | here    => simp [dropVar] at h
  | there w => simp [dropVar] at h; subst h; rfl

/-! ## 2. The dead-let-elimination pass

`comDCE` is a single bottom-up traversal. At a binder `.var e body` it first
eliminates the trailing dead bindings of `body`; if the residual body is a bare
`.ret v` that does not read this binder (`dropVar v = some v'`), the binder is
dead and is dropped, collapsing to `.ret v'`. Otherwise the binder is kept (the
body still reads it, or the body is not a bare return). Iterating the recursion
removes a whole trailing run of dead bindings in one pass. -/

/-- **Dead-let elimination.** Bottom-up removal of trailing dead bindings: a
binder whose (already-cleaned) body is a `.ret` ignoring it is deleted, with the
returned variable strengthened. Generic over any `Dialect` — every operation in
the VIR `Expr` model is a pure function, so deleting a dead binding cannot drop
an effect. -/
def comDCE {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty} :
    Com d Γ t → Com d Γ t
  | .ret v => .ret v
  | .var e body =>
      match comDCE body with
      | .ret v =>
          match dropVar v with
          | some v' => .ret v'          -- binder is dead: drop it
          | none    => .var e (.ret v)  -- the binder *is* the returned value: keep
      | body' => .var e body'           -- body still has binders: keep this one

/-! ## 3. Denotation preservation (not `rfl`) -/

/-- **Denotation preservation for `comDCE`.** The cleaned program denotes the
same function as the input: `(comDCE c).denote V = c.denote V`, for every
valuation `V`. Proved by induction over the `Com` let-chain — the dead-binder
case discharges via `dropVar_lookup` (the dropped binding is never read).
**Not `rfl`.** -/
theorem comDCE_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ : Ctxt d} {t : d.Ty} :
    ∀ (c : Com d Γ t) (V : Ctxt.Valuation Γ), (comDCE c).denote V = c.denote V
  | .ret _, _ => rfl
  | .var e body, V => by
      have ih := comDCE_denote body (V.extend (e.denote V))
      show (comDCE (.var e body)).denote V = body.denote (V.extend (e.denote V))
      rw [← ih]
      simp only [comDCE]
      cases hb : comDCE body with
      | ret v =>
          simp only []
          split
          · next v' hv =>
              simp only [Com.denote]
              exact (dropVar_lookup v v' hv V (e.denote V)).symm
          · next hv => simp only [Com.denote]
      | var e2 body2 => simp only [Com.denote]

/-! ## 4. Elimination of every dead binding by liveness

`dceLive c` deletes every binding of `c` whose value does not reach the return, interior
ones included, in time linear in the size of `c`:

1. `bindingUses` records, in one forward traversal, the levels of the arguments of each
   binding (the level of a variable is its position counted from the bottom of the
   context, `n - 1 - varDepth v` in a context of length `n`);
2. `liveLevels` marks the live levels in one backward scan of that array: the returned
   level, and the argument levels of every live binding;
3. `dceGo` rebuilds the program in one forward traversal, dropping the unmarked
   bindings and carrying a `Thinning` from the old context to the new one, through which
   each surviving variable is re-indexed.

The marks are not trusted: `dceGo` returns `none` when a kept binding reads a dropped
one, and `dceLive` then returns its input. `dceGo_denote` holds for any marks. -/

/-- An order-preserving embedding of `Δ` into `Γ`: `Γ` with some of the bindings above
    a common base dropped. -/
inductive Thinning {d : Dialect} : Ctxt d → Ctxt d → Type _ where
  /-- The identity on the base. -/
  | refl (Γ : Ctxt d) : Thinning Γ Γ
  /-- A binding kept in both contexts. -/
  | keep {Δ Γ : Ctxt d} (t : d.Ty) : Thinning Δ Γ → Thinning (t :: Δ) (t :: Γ)
  /-- A binding of `Γ` absent from `Δ`. -/
  | drop {Δ Γ : Ctxt d} (t : d.Ty) : Thinning Δ Γ → Thinning Δ (t :: Γ)

namespace Thinning

/-- The variable of `Δ` a variable of `Γ` corresponds to, or `none` for a dropped
    binding. -/
def get {d : Dialect} : {Δ Γ : Ctxt d} → {t : d.Ty} → Thinning Δ Γ → Var Γ t →
    Option (Var Δ t)
  | _, _, _, .refl _, v => some v
  | _, _, _, .keep _ _, .here => some .here
  | _, _, _, .keep _ θ, .there v => (θ.get v).map .there
  | _, _, _, .drop _ _, .here => none
  | _, _, _, .drop _ θ, .there v => θ.get v

/-- The restriction of a valuation of `Γ` to `Δ`. -/
def pull {d : Dialect} [TyDenote d.Ty] : {Δ Γ : Ctxt d} → Thinning Δ Γ →
    Ctxt.Valuation Γ → Ctxt.Valuation Δ
  | _, _, .refl _, V => V
  | _, _, .keep _ θ, .cons x V => .cons x (θ.pull V)
  | _, _, .drop _ θ, .cons _ V => θ.pull V

theorem get_lookup {d : Dialect} [TyDenote d.Ty] : ∀ {Δ Γ : Ctxt d} {t : d.Ty}
    (θ : Thinning Δ Γ) (v : Var Γ t) (v' : Var Δ t), θ.get v = some v' →
    ∀ V : Ctxt.Valuation Γ, v'.lookup (θ.pull V) = v.lookup V
  | _, _, _, .refl _, v, v', h, V => by
      simp only [get, Option.some.injEq] at h; subst h; rfl
  | _, _, _, .keep _ _, .here, v', h, .cons _ _ => by
      simp only [get, Option.some.injEq] at h; subst h; rfl
  | _, _, _, .keep _ θ, .there v, v', h, .cons _ V => by
      simp only [get, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact get_lookup θ v w hw V
  | _, _, _, .drop _ _, .here, v', h, _ => by simp [get] at h
  | _, _, _, .drop _ θ, .there v, v', h, .cons _ V => get_lookup θ v v' h V

/-- The re-indexed argument vector, or `none` when an argument is dropped. -/
def getArgs {d : Dialect} {Δ Γ : Ctxt d} (θ : Thinning Δ Γ) : {tys : List d.Ty} →
    HVector (fun ty => Var Γ ty) tys → Option (HVector (fun ty => Var Δ ty) tys)
  | [], .nil => some .nil
  | _ :: _, .cons v rest =>
      match θ.get v, θ.getArgs rest with
      | some v', some r => some (.cons v' r)
      | _, _ => none

theorem getArgs_lookup {d : Dialect} [TyDenote d.Ty] {Δ Γ : Ctxt d} (θ : Thinning Δ Γ)
    (V : Ctxt.Valuation Γ) : ∀ {tys : List d.Ty} (as : HVector (fun ty => Var Γ ty) tys)
    (as' : HVector (fun ty => Var Δ ty) tys), θ.getArgs as = some as' →
    Expr.lookupArgs as' (θ.pull V) = Expr.lookupArgs as V
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons v rest, as', h => by
      simp only [getArgs] at h
      split at h
      · rename_i v' r hv hr
        simp only [Option.some.injEq] at h
        subst h
        simp only [Expr.lookupArgs]
        rw [get_lookup θ v v' hv V, getArgs_lookup θ V rest r hr]
      · cases h

/-- The re-indexed expression, or `none` when an argument is dropped. -/
def getExpr {d : Dialect} [DialectSignature d] {Δ Γ : Ctxt d} {t : d.Ty}
    (θ : Thinning Δ Γ) (e : Expr d Γ t) : Option (Expr d Δ t) :=
  (θ.getArgs e.args).map fun args => ⟨e.op, e.retTy_eq, args⟩

theorem getExpr_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d]
    {Δ Γ : Ctxt d} {t : d.Ty} (θ : Thinning Δ Γ) (e : Expr d Γ t) (e' : Expr d Δ t)
    (h : θ.getExpr e = some e') (V : Ctxt.Valuation Γ) :
    e'.denote (θ.pull V) = e.denote V := by
  simp only [getExpr, Option.map_eq_some_iff] at h
  obtain ⟨args, hargs, rfl⟩ := h
  simp only [Expr.denote]
  rw [getArgs_lookup θ V e.args args hargs]

end Thinning

/-- The levels of the variables `args` in a context of length `n`, prepended to `acc`. -/
def argLevels {d : Dialect} {Γ : Ctxt d} (n : Nat) : {tys : List d.Ty} →
    HVector (fun ty => Var Γ ty) tys → List Nat → List Nat
  | [], .nil, acc => acc
  | _ :: _, .cons v rest, acc => argLevels n rest ((n - 1 - varDepth v) :: acc)

/-- The argument levels of each binding of `c`, in binding order, pushed onto `acc`, and
    the level of the returned variable; `n` is the length of the context of `c`. -/
def bindingUses {d : Dialect} [DialectSignature d] : {Γ : Ctxt d} → {t : d.Ty} → Nat →
    Com d Γ t → Array (List Nat) → Array (List Nat) × Nat
  | _, _, n, .ret v, acc => (acc, n - 1 - varDepth v)
  | _, _, n, .var e body, acc => bindingUses (n + 1) body (acc.push (argLevels n e.args []))

/-- The live levels of a program over a context of length `n0` whose bindings read the
    levels `uses` and which returns level `r`: entry `ℓ` is `true` when level `ℓ` is `r`
    or is read by a binding at a live level. One backward scan. -/
def liveLevels (n0 : Nat) (uses : Array (List Nat)) (r : Nat) : Array Bool := Id.run do
  let mut live := (Array.replicate (n0 + uses.size) false).setIfInBounds r true
  for j in [0:uses.size] do
    let i := uses.size - 1 - j
    if live.getD (n0 + i) false then
      for a in uses.getD i [] do
        live := live.setIfInBounds a true
  return live

/-- The rebuild: the binding at level `n` is kept when `live` marks it (or has no entry
    for it) and dropped otherwise; `θ` re-indexes the variables of the kept program.
    `none` when a kept binding or the return reads a dropped binding. -/
def dceGo {d : Dialect} [DialectSignature d] (live : Array Bool) :
    {Δ Γ : Ctxt d} → {t : d.Ty} → Nat → Thinning Δ Γ → Com d Γ t → Option (Com d Δ t)
  | _, _, _, _, θ, .ret v => (θ.get v).map .ret
  | _, _, _, n, θ, .var (t := u) e body =>
      if live.getD n true then
        match θ.getExpr e, dceGo live (n + 1) (.keep u θ) body with
        | some e', some b => some (.var e' b)
        | _, _ => none
      else dceGo live (n + 1) (.drop u θ) body

/-- **Soundness of the rebuild**, for any marks: a rebuilt program denotes, on the
    restricted valuation, what the input denotes. -/
theorem dceGo_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d]
    (live : Array Bool) : ∀ {Δ Γ : Ctxt d} {t : d.Ty} (n : Nat) (θ : Thinning Δ Γ)
    (c : Com d Γ t) (c' : Com d Δ t), dceGo live n θ c = some c' →
    ∀ V : Ctxt.Valuation Γ, c'.denote (θ.pull V) = c.denote V
  | _, _, _, _, θ, .ret v, c', h, V => by
      simp only [dceGo, Option.map_eq_some_iff] at h
      obtain ⟨v', hv, rfl⟩ := h
      exact θ.get_lookup v v' hv V
  | _, _, _, n, θ, .var (t := u) e body, c', h, V => by
      simp only [dceGo] at h
      split at h
      · split at h
        · rename_i e' b he hb
          simp only [Option.some.injEq] at h
          subst h
          simp only [Com.denote]
          rw [θ.getExpr_denote e e' he V]
          exact dceGo_denote live (n + 1) (.keep u θ) body b hb (V.extend (e.denote V))
        · cases h
      · exact dceGo_denote live (n + 1) (.drop u θ) body c' h (V.extend (e.denote V))

/-- **Dead-binding elimination by liveness.** Every binding whose value does not reach
    the return is deleted; linear in the size of `c`. -/
def dceLive {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) : Com d Γ t :=
  let n0 := Γ.length
  let ur := bindingUses n0 c #[]
  match dceGo (liveLevels n0 ur.1 ur.2) n0 (.refl Γ) c with
  | some c' => c'
  | none => c

/-- **Denotation preservation for `dceLive`.** -/
theorem dceLive_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d]
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ) :
    (dceLive c).denote V = c.denote V := by
  unfold dceLive
  dsimp only
  split
  · rename_i c' h
    exact dceGo_denote _ _ (.refl Γ) c c' h V
  · rfl

/-! ## 5. `jasminDialect` corollaries: cost and constant-time

The headline preservation theorem is dialect-generic. For the concrete
`jasminDialect` (the linear-jasmin emit target) we additionally show the pass is
cost-non-increasing (it only ever deletes binders) and constant-time-preserving
(the dialect is branch-free, so every `Com` is CT-safe before and after). -/

/-- **The pass is cost-non-increasing on `jasminDialect`.** `comDCE` only deletes
binders, so the let-chain cost never rises. -/
theorem comDCE_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ c : Com jasminDialect Γ t, comCost (comDCE c) ≤ comCost c
  | .ret _ => Nat.le_refl _
  | .var e body => by
      have ih := comDCE_cost_le body
      show comCost (comDCE (.var e body)) ≤ comCost (.var e body)
      simp only [comDCE]
      cases hb : comDCE body with
      | ret v =>
          rw [hb] at ih
          simp only []
          split
          · simp only [comCost]; omega
          · simp only [comCost]; omega
      | var e2 body2 =>
          rw [hb] at ih
          simp only [comCost] at ih ⊢
          omega

/-- **The pass preserves constant-time safety on `jasminDialect`.** The dialect
has no conditional op, so every `Com` — input or output — is CT-safe. -/
theorem comDCE_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) :
    ctSafeComJ (comDCE c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (comDCE c), ctSafeComJ_true c]

/-! ## 6. Self-contained validation

A `Com jasminDialect [reg 32] (reg 32)` with a **dead trailing
binding**:

    let v0 = x + x      -- live: it is what we return
    let v1 = x + x      -- dead: never read; feeds a ret that returns v0
    ret v0

The pass deletes `v1` and re-points the return at the strengthened `v0`. We
check that (a) the pass actually shrinks the program (one binder removed),
(b) the denotation is preserved, and (c) cost is non-increasing and CT is
preserved. -/

/-- A `reg 32` binary `regArith` helper for the demo. -/
def binR32 {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 32)) : Expr jasminDialect Γ (.reg 32) :=
  { op := .regArith op 32, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The demo program: `v0 = x + x; v1 = x + x; ret v0`. The binder `v1` is dead
— the `ret` returns `v0` (which is `.there .here` after `v1` is bound), never
`v1` (`.here`). -/
def demoDeadTrailing : Com jasminDialect [.reg 32] (.reg 32) :=
  -- v0 = x + x.  Context becomes [v0, x]; `x` is `.there .here`, `v0` is `.here`.
  .var (binR32 .add .here .here)
    -- v1 = x + x.  Context becomes [v1, v0, x]; `x` is `.there (.there .here)`.
    (.var (binR32 .add (.there .here) (.there .here))
      -- ret v0.  `v0` is `.there .here` here (skipping the dead `v1`).
      (.ret (.there .here)))

/-- **The pass deletes the dead `v1` binder**, collapsing to `v0 = x + x; ret v0`
with the return strengthened to `.here`. A concrete `rfl`-checkable shrink. -/
example : comDCE demoDeadTrailing =
    Com.var (binR32 .add .here .here) (.ret .here) := rfl

/-- **Strictly fewer binders after the pass** (the dead binder is gone): the
input has cost `2`, the output cost `1`. -/
example : comCost (comDCE demoDeadTrailing) < comCost demoDeadTrailing := by decide

/-- **Denotation preserved** for the demo, via the general theorem. Both map
`x` to `x + x`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comDCE demoDeadTrailing).denote V = demoDeadTrailing.denote V :=
  comDCE_denote demoDeadTrailing V

/-- Concretely, on `x = 21`, both denote `42`. -/
example : demoDeadTrailing.denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

example :
    (comDCE demoDeadTrailing).denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

/-- **Cost non-increasing** on the demo. -/
example : comCost (comDCE demoDeadTrailing) ≤ comCost demoDeadTrailing :=
  comDCE_cost_le demoDeadTrailing

/-- **CT preserved** on the demo. -/
example : ctSafeComJ (comDCE demoDeadTrailing) = ctSafeComJ demoDeadTrailing :=
  comDCE_ctSafe demoDeadTrailing

/-- A program with **no** dead trailing binder is left unchanged: the binder *is*
the returned value, so it is kept. -/
def demoLive : Com jasminDialect [.reg 32] (.reg 32) :=
  .var (binR32 .add .here .here) (.ret .here)

example : comDCE demoLive = demoLive := rfl

end CatCrypt.Crypto.Optimizer.ComDCE
