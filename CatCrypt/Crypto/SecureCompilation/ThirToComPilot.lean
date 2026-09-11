/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# Pilot: a verified THIR → `Com` lowering ("Aeneas-for-compilation", #568)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

This module is a **design + pilot** for a *direct* lowering from a minimal
subset of Rust's Typed-HIR (THIR — the typed AST that hax/charon expose) into
CatCrypt's intrinsically-typed SSA IR `Com` (`VIR/Core.lean`), with a
**denotation-preservation lemma proved (no `sorry`)** on the pilot fragment and
concrete pilot functions.

## Why this is distinct from the existing `haxpipeT` path

CatCrypt already has a hax-extraction pipeline (`CatCrypt/Hax/*`):

  THIR  --hax-->  `ImpExpr` (untyped, String-named, fuel-bounded big-step,
                   `Outcome`-effectful;  `Hax/AST.lean`, `Hax/Semantics.lean`)
        --phases-->  `RawCode`  (a Lean term)

That path targets the **extraction-to-Lean** problem: turn Rust into a Lean
*term* whose abstract security can be proved. It does **not** target `Com`, the
SSA IR the **compilation/codegen** backend consumes (X86/ARM/RISC-V/Jasmin/MLIR
via `VIR/*`). There is currently no lowering from the THIR/`ImpExpr` world into
`Com`.

#568 asks for the *compilation* counterpart: a direct THIR → `Com` front, in
the style of Aeneas (which lowers Rust's typed MIR/THIR directly into a pure
functional model). This file pilots that lowering on a monomorphic ANF fragment
and ties the two denotations.

## What the pilot covers

* A minimal THIR-subset datatype `Thir` over `u64`, in **A-normal form** (the
  shape charon/THIR produce after let-normalisation):
  - `Atom` operands are `lit` or a named `var`;
  - statements are `let_` of a `Rhs` (an atom, or `add`/`mul` of two atoms),
    ending in a returned atom (`ret`);
  - plus a *bounded* fold `forUp` whose iteration count is a compile-time
    literal (the LowCT-expressible monomorphic bound).
* A small big-step THIR denotation `Thir.denote` / `Atom.denote` / `Rhs.denote`
  into `Option UInt64` over a `String → Option UInt64` environment (partial,
  mirroring the untyped, possibly-unbound-name `ImpExpr` semantics).
* A target dialect `pilot` for `Com` with one type `u64` and ops
  `const`/`add`/`mul`, plus its `DialectSignature`/`DialectDenote`.
* A scope-directed lowering `thirToCom` (name → de-Bruijn `Var`) on the ANF
  fragment; `forUp` is lowered by compile-time unrolling into nested `let_`s, so
  it routes through the same straight-line lowering.
* The denotation-preservation theorem `thirToCom_denote`, proved by structural
  induction with a compatibility invariant `Agree` between the THIR name
  environment and the `Com` de-Bruijn `Valuation`. Concrete pilot functions
  (`pilotAddMul`, `pilotForSum`) instantiate it and evaluate by `decide`.

## Scope (pilot vs a general front)

The pilot is **not** a general THIR front. A general front additionally needs:

* **Generics + monomorphization**: THIR is generic; charon/hax monomorphize.
  The pilot is fixed at `u64`. A real front needs type-driven `Dialect`
  selection keyed on the monomorphized instance.
* **The full expr grammar**: tuples/structs/enums, `match`, references/`deref`,
  trait/method dispatch, slices/indexing — none here. The pilot covers
  `let`/`var`/arith/bounded-`for`, the slice with a `Com` home.
* **Runtime-`N` loops**: the pilot bounds loops by a *compile-time literal*
  (unrolling). `Com` itself is loop-free (straight-line ANF); real bounded loops
  live downstream in the Jasmin/`JForProg` layer (`VIR/JForProg*.lean`), so a
  general front would lower THIR `for` there rather than unroll.
* **Effects/partiality/overflow**: `ImpExpr`'s `Outcome`
  (early-return/break/continue) and Rust overflow checks are not modelled; the
  pilot is pure `Option` with wrapping `u64`.
* **Mutation/borrows**: handled upstream by `dropReferences`/`localMutation`.

## Relation to `haxpipeT`: complement, not replacement

This is a **complement**: `haxpipeT` is the *extraction* front (→ Lean term for
security proofs); this pilots the *compilation* front (→ `Com` for codegen). A
production version would consume `haxpipeT`'s post-phase `ImpExpr` (already
de-sugared of references/mutation/loops-as-folds) and lower the surviving
*core* constructors into `Com` — reusing the existing typed phases as the THIR
normaliser and adding only the final `ImpExpr_core → Com` leg. `Thir` here is a
faithful ANF subset of those surviving core constructors so the wiring is a
refinement, not a rewrite.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirToComPilot

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## §1  The minimal THIR subset (ANF) -/

/-- A THIR operand: a `u64` literal or a named variable reference.
    (THIR after let-normalisation has atomic operands.) -/
inductive Atom where
  | lit (n : UInt64)
  | var (name : String)
  deriving Repr, DecidableEq

/-- The right-hand side of a `let`: an atom, or a binary op on two atoms. -/
inductive Rhs where
  | atom (a : Atom)
  | add (a b : Atom)
  | mul (a b : Atom)
  deriving Repr

/-- A THIR statement sequence in A-normal form over `u64`.

* `ret a` — return atom `a`.
* `let_ x r body` — `let x = r in body` (THIR `Expr::Let` / block binding).
* `forUp acc init n body` — `let mut acc = init; for _ in 0..n { acc = body }`,
  with `n` a compile-time literal, `body : Rhs` the per-iteration accumulator
  update (an ANF assignment that may read `acc`), and the loop value the final
  `acc`. A `Rhs` body (single ANF assignment) is the common accumulator-loop
  shape and keeps `forUp` unrollable into nested `let_`s. -/
inductive Thir where
  | ret (a : Atom)
  | let_ (name : String) (r : Rhs) (body : Thir)
  | forUp (acc : String) (init : Atom) (n : Nat) (body : Rhs)
  deriving Repr

/-- A THIR name environment: partial map name → `u64` (mirrors `Hax.Env`). -/
abbrev TEnv := String → Option UInt64

/-- Empty environment. -/
def TEnv.empty : TEnv := fun _ => none

/-- Extend an environment. -/
def TEnv.set (ρ : TEnv) (x : String) (v : UInt64) : TEnv :=
  fun y => if y = x then some v else ρ y

/-! ## §2  Big-step THIR denotation -/

/-- Denotation of an atom. -/
def Atom.denote : Atom → TEnv → Option UInt64
  | .lit n, _ => some n
  | .var x, ρ => ρ x

/-- Denotation of a `let`-RHS. -/
def Rhs.denote : Rhs → TEnv → Option UInt64
  | .atom a, ρ => a.denote ρ
  | .add a b, ρ => (a.denote ρ).bind fun av => (b.denote ρ).map (av + ·)
  | .mul a b, ρ => (a.denote ρ).bind fun av => (b.denote ρ).map (av * ·)

/-- Iterate the loop body `n` times, threading the accumulator through `acc`. -/
def forIter (acc : String) (body : Rhs) :
    Nat → UInt64 → TEnv → Option UInt64
  | 0,     a, _ => some a
  | k + 1, a, ρ => (body.denote (ρ.set acc a)).bind
                      fun a' => forIter acc body k a' ρ

/-- Big-step denotation of a THIR statement, partial via `Option`. -/
def Thir.denote : Thir → TEnv → Option UInt64
  | .ret a, ρ => a.denote ρ
  | .let_ x r body, ρ => (r.denote ρ).bind fun rv => body.denote (ρ.set x rv)
  | .forUp acc init n body, ρ =>
      (init.denote ρ).bind fun i0 => forIter acc body n i0 ρ

/-! ## §3  The target `Com` dialect -/

/-- The pilot dialect's value-type alphabet: a single `u64` type. -/
inductive PilotTy where
  | u64
  deriving DecidableEq, Repr

/-- The pilot dialect's operations. -/
inductive PilotOp where
  | const (n : UInt64)
  | add
  | mul
  deriving Repr

@[reducible] instance : TyDenote PilotTy where
  denote
    | .u64 => UInt64

@[reducible] def pilot : Dialect := { Op := PilotOp, Ty := PilotTy }

instance : DialectSignature pilot where
  sig
    | .const _ => []
    | .add => [.u64, .u64]
    | .mul => [.u64, .u64]
  ret
    | .const _ => .u64
    | .add => .u64
    | .mul => .u64

instance : DialectDenote pilot where
  denote
    | .const n, .nil => n
    | .add, .cons (a : UInt64) (.cons (b : UInt64) .nil) => a + b
    | .mul, .cons (a : UInt64) (.cons (b : UInt64) .nil) => a * b

/-! ## §4  Compile-time scope and the lowering -/

/-- A compile-time scope: bound names, newest first. -/
abbrev Scope := List String

/-- The `Com` typing context induced by a scope: one `.u64` per name. -/
def scopeCtxt : Scope → Ctxt pilot
  | [] => []
  | _ :: σ => .u64 :: scopeCtxt σ

/-- Resolve a name to a de-Bruijn variable in the induced context, if bound.
    Returns the *newest* matching binding. -/
def scopeVar : (σ : Scope) → String → Option (Ctxt.Var (scopeCtxt σ) .u64)
  | [],      _ => none
  | y :: σ', x =>
      if x = y then
        some .here
      else
        (scopeVar σ' x).map (·.there)

/-- Lower a `Rhs` to a single `Com` expression that returns the RHS's value,
    against a scope.

    To keep the lowering total and the round-trip proof a clean structural
    induction, binary-op operands must be **variables in scope** (the ANF charon
    produces after let-normalisation: every literal is first `let`-bound). A
    literal `Rhs` (`atom (lit n)`) becomes a `const`; a variable `Rhs`
    (`atom (var x)`) re-binds via `add x (const 0)` is avoided — instead a bare
    variable atom is returned directly. -/
def lowerRhs (σ : Scope) : Rhs → Option (Com pilot (scopeCtxt σ) .u64)
  | .atom (.lit n) => some (.var (Expr.mk (.const n) rfl .nil) (.ret .here))
  | .atom (.var x) => (scopeVar σ x).map (.ret ·)
  | .add (.var a) (.var b) =>
      match scopeVar σ a, scopeVar σ b with
      | some va, some vb =>
          some (.var (Expr.mk .add rfl (.cons va (.cons vb .nil))) (.ret .here))
      | _, _ => none
  | .mul (.var a) (.var b) =>
      match scopeVar σ a, scopeVar σ b with
      | some va, some vb =>
          some (.var (Expr.mk .mul rfl (.cons va (.cons vb .nil))) (.ret .here))
      | _, _ => none
  -- Non-ANF operands (a literal inside a binary op) are rejected; the front
  -- normalises these to a leading `let` before this layer (see `forUp` and the
  -- module docstring). The pilot fns exercise the supported shapes.
  | .add _ _ => none
  | .mul _ _ => none

/-! ### §4.1  The single `Expr` a `let`-RHS binds

A `let x = r in body` lowers to `Com.var e bc`, where `e` is the single `Expr`
that produces `r`'s value at the head of the context, and `bc` is the lowering
of `body` in the extended scope. `rhsExpr` extracts that head `Expr`. (For the
supported ANF shapes, `lowerRhs σ r` is exactly `Com.var (rhsExpr σ r) (ret
here)`; the `let` lowering reuses the `Expr` directly rather than the wrapped
`Com`.) -/

/-- The single `Expr` underlying a supported `Rhs` lowering, if any. Returns the
    op-expression that `lowerRhs` would bind at the head. -/
def rhsExpr (σ : Scope) : Rhs → Option (Expr pilot (scopeCtxt σ) .u64)
  | .atom (.lit n) => some (Expr.mk (.const n) rfl .nil)
  | .atom (.var _) => none      -- a bare variable is not an `Expr`; see note
  | .add (.var a) (.var b) =>
      match scopeVar σ a, scopeVar σ b with
      | some va, some vb => some (Expr.mk .add rfl (.cons va (.cons vb .nil)))
      | _, _ => none
  | .mul (.var a) (.var b) =>
      match scopeVar σ a, scopeVar σ b with
      | some va, some vb => some (Expr.mk .mul rfl (.cons va (.cons vb .nil)))
      | _, _ => none
  | .add _ _ => none
  | .mul _ _ => none

/-! ### §4.2  Compile-time unrolling of the bounded loop

`forUp acc init n body` unrolls to
`let acc = init in (let acc = body in)^n  ret (var acc)`. -/

/-- Append `n` copies of `let acc = body` ending in `ret (var acc)`. -/
def unrollBody (acc : String) (body : Rhs) : Nat → Thir
  | 0     => .ret (.var acc)
  | k + 1 => .let_ acc body (unrollBody acc body k)

/-- Unroll a bounded loop into the nested-`let` straight-line fragment. -/
def Thir.unrollFor (acc : String) (init : Atom) (n : Nat) (body : Rhs) : Thir :=
  .let_ acc (.atom init) (unrollBody acc body n)

/-- A termination measure dominating the unrolling step: `forUp` (measure
    `2 + n + measure body`, but `body : Rhs` so it contributes `0`) strictly
    exceeds its unrolling `let acc = init in (let acc = body)^n ret acc`
    (measure `1 + n`). -/
def thirMeasure : Thir → Nat
  | .ret _ => 0
  | .let_ _ _ body => 1 + thirMeasure body
  | .forUp _ _ n _ => 2 + n

/-- `unrollBody` has measure exactly `n`. -/
theorem thirMeasure_unrollBody (acc : String) (body : Rhs) (n : Nat) :
    thirMeasure (unrollBody acc body n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [unrollBody, thirMeasure, ih]; omega

/-- `unrollFor` has measure `1 + n`, strictly below `forUp`'s `2 + n`. -/
theorem thirMeasure_unrollFor (acc : String) (init : Atom) (n : Nat)
    (body : Rhs) :
    thirMeasure (Thir.unrollFor acc init n body) = 1 + n := by
  simp [Thir.unrollFor, thirMeasure, thirMeasure_unrollBody]

/-- Lower a THIR statement to `Com` against a scope.

* `ret a` → `lowerRhs σ (.atom a)`.
* `let_ x r body` → bind `r`'s `Expr` at the head, then lower `body` in the
  extended scope `x :: σ`. A bare-variable RHS (`r = atom (var y)`) is handled
  by binding an identity `const`-free copy — modelled here by requiring `r` to
  have an `Expr` (so `let x = y` is *not* in the pilot's input shape; charon
  emits `let x = y + 0`-style copies or inlines the alias, so this is a faithful
  restriction). The pilot fns only `let`-bind op-RHSs and literals.
* `forUp acc init n body` → compile-time **unrolling** into nested `let_`s, then
  lower the result. -/
def thirToCom (σ : Scope) : Thir → Option (Com pilot (scopeCtxt σ) .u64)
  | .ret a => lowerRhs σ (.atom a)
  | .let_ x r body =>
      match rhsExpr σ r, thirToCom (x :: σ) body with
      | some e, some bc => some (.var e bc)
      | _, _ => none
  | .forUp acc init n body =>
      thirToCom σ (Thir.unrollFor acc init n body)
  termination_by t => thirMeasure t
  decreasing_by
    · simp [thirMeasure]
    · simp [thirMeasure, thirMeasure_unrollFor]

/-! ## §5  Denotation preservation -/

/-- Compatibility between a THIR name environment `ρ` and a `Com` de-Bruijn
    valuation `V` over a scope `σ`: every name resolvable to a de-Bruijn
    variable carries the same value. -/
def Agree (σ : Scope) (ρ : TEnv) (V : Ctxt.Valuation (scopeCtxt σ)) : Prop :=
  ∀ (x : String) (v : Ctxt.Var (scopeCtxt σ) .u64),
    scopeVar σ x = some v → ρ x = some (v.lookup V)

/-- Extending both environments with the same binding preserves `Agree`. -/
theorem Agree.extend {σ : Scope} {ρ : TEnv} {V : Ctxt.Valuation (scopeCtxt σ)}
    (h : Agree σ ρ V) (x : String) (w : UInt64) :
    Agree (x :: σ) (ρ.set x w)
      ((V.extend w : Ctxt.Valuation (PilotTy.u64 :: scopeCtxt σ))) := by
  intro y v hy
  simp only [scopeVar] at hy
  by_cases hxy : y = x
  · subst hxy
    rw [if_pos rfl] at hy
    cases hy
    show (ρ.set y w) y = some (Ctxt.Var.here.lookup (V.extend w))
    simp only [TEnv.set, Ctxt.Valuation.extend]
    rfl
  · rw [if_neg hxy] at hy
    rcases hv : scopeVar σ y with _ | v0
    · rw [hv] at hy; simp at hy
    · rw [hv] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy
      simp only [TEnv.set, if_neg hxy]
      have := h y v0 hv
      rw [this]
      rfl

/-- Atom preservation: a variable atom resolvable in scope denotes to the
    looked-up value; a literal denotes to itself. -/
theorem lowerRhs_atom_denote {σ : Scope} {ρ : TEnv}
    {V : Ctxt.Valuation (scopeCtxt σ)} (h : Agree σ ρ V) (a : Atom)
    {c : Com pilot (scopeCtxt σ) .u64} (hc : lowerRhs σ (.atom a) = some c) :
    a.denote ρ = some (c.denote V) := by
  cases a with
  | lit n =>
      simp only [lowerRhs, Option.some.injEq] at hc
      subst hc
      simp only [Atom.denote, Com.denote, Expr.denote, DialectDenote.denote,
        Expr.lookupArgs, Ctxt.Valuation.extend]
      rfl
  | var x =>
      simp only [lowerRhs] at hc
      rcases hv : scopeVar σ x with _ | v
      · rw [hv] at hc; simp at hc
      · rw [hv] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        subst hc
        simp only [Atom.denote, Com.denote]
        exact h x v hv

/-- A scoped variable denotes to its valuation lookup under `Agree`. -/
theorem scopeVar_denote {σ : Scope} {ρ : TEnv}
    {V : Ctxt.Valuation (scopeCtxt σ)} (h : Agree σ ρ V) {x : String}
    {v : Ctxt.Var (scopeCtxt σ) .u64} (hv : scopeVar σ x = some v) :
    ρ x = some (v.lookup V) := h x v hv

/-- `rhsExpr` preservation: the single `Expr` produced for a `Rhs` denotes to
    the same value as the THIR `Rhs`. -/
theorem rhsExpr_denote {σ : Scope} {ρ : TEnv}
    {V : Ctxt.Valuation (scopeCtxt σ)} (h : Agree σ ρ V) (r : Rhs)
    {e : Expr pilot (scopeCtxt σ) .u64} (he : rhsExpr σ r = some e) :
    r.denote ρ = some (e.denote V) := by
  cases r with
  | atom a =>
      cases a with
      | lit n =>
          simp only [rhsExpr, Option.some.injEq] at he
          subst he
          simp only [Rhs.denote, Atom.denote, Expr.denote, DialectDenote.denote]
          rfl
      | var x => simp [rhsExpr] at he
  | add a b =>
      cases a with
      | lit _ => cases b <;> simp [rhsExpr] at he
      | var xa =>
        cases b with
        | lit _ => simp [rhsExpr] at he
        | var xb =>
            simp only [rhsExpr] at he
            rcases hva : scopeVar σ xa with _ | va <;> rw [hva] at he
            · simp at he
            rcases hvb : scopeVar σ xb with _ | vb <;> rw [hvb] at he
            · simp at he
            · simp only [Option.some.injEq] at he
              subst he
              simp only [Rhs.denote, Atom.denote, Expr.denote,
                DialectDenote.denote]
              rw [scopeVar_denote h hva, scopeVar_denote h hvb]
              rfl
  | mul a b =>
      cases a with
      | lit _ => cases b <;> simp [rhsExpr] at he
      | var xa =>
        cases b with
        | lit _ => simp [rhsExpr] at he
        | var xb =>
            simp only [rhsExpr] at he
            rcases hva : scopeVar σ xa with _ | va <;> rw [hva] at he
            · simp at he
            rcases hvb : scopeVar σ xb with _ | vb <;> rw [hvb] at he
            · simp at he
            · simp only [Option.some.injEq] at he
              subst he
              simp only [Rhs.denote, Atom.denote, Expr.denote,
                DialectDenote.denote]
              rw [scopeVar_denote h hva, scopeVar_denote h hvb]
              rfl

/-- Setting the same name twice keeps the last write. -/
theorem TEnv.set_set (ρ : TEnv) (x : String) (a b : UInt64) :
    (ρ.set x a).set x b = ρ.set x b := by
  funext y; simp only [TEnv.set]; by_cases h : y = x <;> simp [h]

/-- The unrolled loop body denotes exactly like the `forIter` iteration. -/
theorem unrollBody_denote (acc : String) (body : Rhs) (n : Nat) (a : UInt64)
    (ρ : TEnv) :
    (unrollBody acc body n).denote (ρ.set acc a) = forIter acc body n a ρ := by
  induction n generalizing a with
  | zero => simp [unrollBody, Thir.denote, Atom.denote, forIter, TEnv.set]
  | succ k ih =>
      simp only [unrollBody, Thir.denote, forIter, TEnv.set_set]
      cases hb : body.denote (ρ.set acc a) with
      | none => simp
      | some a' => simp only [Option.bind_some]; rw [ih]

/-- Unrolling preserves the loop's denotation. -/
theorem unrollFor_denote (acc : String) (init : Atom) (n : Nat) (body : Rhs)
    (ρ : TEnv) :
    (Thir.unrollFor acc init n body).denote ρ
      = (Thir.forUp acc init n body).denote ρ := by
  simp only [Thir.unrollFor, Thir.denote, Rhs.denote]
  cases hi : init.denote ρ with
  | none => simp
  | some i0 => simp only [Option.bind_some]; rw [unrollBody_denote]

/-- Main preservation theorem: when `Agree σ ρ V` holds and the lowering
    succeeds, the THIR denotation equals the lowered `Com`'s denotation.

    Proved by induction following `thirToCom`'s own recursion (so the bounded
    loop is handled through its unrolling). No `sorry`. -/
theorem thirToCom_denote (σ : Scope) (t : Thir) (ρ : TEnv)
    (V : Ctxt.Valuation (scopeCtxt σ)) (c : Com pilot (scopeCtxt σ) .u64)
    (hAg : Agree σ ρ V) (hc : thirToCom σ t = some c) :
    t.denote ρ = some (c.denote V) := by
  -- Strong induction on the unrolling measure, so the bounded loop reduces to
  -- its (measure-smaller) unrolled straight-line form.
  induction hmeas : thirMeasure t using Nat.strongRecOn
    generalizing σ ρ V c t with
  | ind m ih =>
    cases t with
    | ret a =>
        -- `ret a`
        simp only [thirToCom] at hc
        have := lowerRhs_atom_denote hAg a hc
        simpa [Thir.denote, Atom.denote, Rhs.denote] using this
    | let_ x r body =>
        -- `let_ x r body`
        simp only [thirToCom] at hc
        rcases he : rhsExpr σ r with _ | e <;> rw [he] at hc
        · simp at hc
        rcases hbc : thirToCom (x :: σ) body with _ | bc <;> rw [hbc] at hc
        · simp at hc
        · simp only [Option.some.injEq] at hc
          subst hc
          simp only [Thir.denote, Com.denote]
          rw [rhsExpr_denote hAg r he, Option.bind_some]
          have hExt : Agree (x :: σ) (ρ.set x (e.denote V))
              (V.extend (e.denote V)) := hAg.extend x (e.denote V)
          exact ih (thirMeasure body) (by subst hmeas; simp [thirMeasure])
            (x :: σ) body (ρ.set x (e.denote V)) (V.extend (e.denote V)) bc
            hExt hbc rfl
    | forUp acc init n body =>
        -- `forUp acc init n body` → handled via unrolling (measure-smaller)
        simp only [thirToCom] at hc
        rw [← unrollFor_denote]
        have hlt : thirMeasure (Thir.unrollFor acc init n body) < m := by
          subst hmeas; rw [thirMeasure_unrollFor]; simp [thirMeasure]
        exact ih (thirMeasure (Thir.unrollFor acc init n body)) hlt
          σ (Thir.unrollFor acc init n body) ρ V c hAg hc rfl

/-! ## §6  Pilot functions

Two concrete monomorphic THIR functions, lowered into `Com` and checked. The
empty scope `[]` matches the empty `Com` context, so the `Agree` hypothesis is
vacuous and `thirToCom_denote` specialises to an unconditional equality of
closed denotations. -/

/-- `Agree` over the empty scope is trivially true. -/
theorem Agree.nil (ρ : TEnv) : Agree [] ρ HVector.nil := by
  intro x v hv; simp only [scopeVar] at hv; nomatch hv

/-! ### Pilot 1: straight-line `let x = 6 in let y = 7 in x * y`

THIR:
```rust
fn f() -> u64 { let x = 6u64; let y = 7u64; x * y }
```
-/

/-- Pilot fn 1: `let x = 6; let y = 7; let z = x * y; z`. The product is bound
    via a third `let` so the result is an atom, matching the ANF charon
    produces. -/
def pilotMul : Thir :=
  .let_ "x" (.atom (.lit 6))
    (.let_ "y" (.atom (.lit 7))
      (.let_ "z" (.mul (.var "x") (.var "y"))
        (.ret (.var "z"))))

/-- The lowering of `pilotMul` succeeds. -/
theorem pilotMul_lowers :
    (thirToCom [] pilotMul).isSome := by
  simp [pilotMul, thirToCom, rhsExpr, lowerRhs, scopeVar]

/-- End-to-end check: the THIR denotation of `pilotMul` equals its lowered
    `Com`'s denotation (both `6 * 7 = 42`). -/
theorem pilotMul_denote (c : Com pilot (scopeCtxt []) .u64)
    (hc : thirToCom [] pilotMul = some c) :
    pilotMul.denote TEnv.empty = some (c.denote HVector.nil) :=
  thirToCom_denote [] pilotMul TEnv.empty HVector.nil c (Agree.nil _) hc

/-- The THIR side evaluates to `42`. -/
example : pilotMul.denote TEnv.empty = some (42 : UInt64) := by
  simp only [pilotMul, Thir.denote, Rhs.denote, Atom.denote, TEnv.empty,
    TEnv.set, Option.bind_some]
  decide

/-! ### Pilot 2: bounded loop `acc := 1; for _ in 0..3 { acc := acc + acc }`

THIR:
```rust
fn g() -> u64 { let mut acc = 1u64; for _ in 0..3 { acc = acc + acc; } acc }
```
denotes to `1 * 2^3 = 8`. -/

/-- Pilot fn 2: a bounded accumulator loop (`acc` doubles 3 times). -/
def pilotForSum : Thir :=
  .forUp "acc" (.lit 1) 3 (.add (.var "acc") (.var "acc"))

/-- The lowering of `pilotForSum` succeeds (the loop is unrolled). -/
theorem pilotForSum_lowers : (thirToCom [] pilotForSum).isSome := by
  simp [pilotForSum, thirToCom, Thir.unrollFor, unrollBody, rhsExpr, lowerRhs,
    scopeVar]

/-- End-to-end check: the THIR denotation of `pilotForSum` equals its lowered
    (unrolled) `Com`'s denotation. -/
theorem pilotForSum_denote (c : Com pilot (scopeCtxt []) .u64)
    (hc : thirToCom [] pilotForSum = some c) :
    pilotForSum.denote TEnv.empty = some (c.denote HVector.nil) :=
  thirToCom_denote [] pilotForSum TEnv.empty HVector.nil c (Agree.nil _) hc

/-- The THIR side evaluates to `8` (`1` doubled three times). -/
example : pilotForSum.denote TEnv.empty = some (8 : UInt64) := by
  simp only [pilotForSum, Thir.denote, forIter, Rhs.denote, Atom.denote,
    TEnv.empty, TEnv.set, Option.bind_some]
  decide

end CatCrypt.Crypto.SecureCompilation.ThirToComPilot
