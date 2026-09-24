/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace

/-!
# Value-carrying leak trace for `catCryptDialect`

The native dialect leak trace `Com.leakTrace`
(`CryptoDialectLeakTrace.lean`) is **valuation-free**: it recurses over the ANF
`Com.ret`/`Com.var` skeleton and takes no input. Consequently
`Com.all_com_ct` (`CryptoDialectLeakTraceNative.lean`) holds by `rfl` — it
carries *no* data-dependent-leakage content, because the trace is literally the
same `List LeakEvent` for every input.

The constant-time / robust-hyperproperty (RHP) framework, however, is about the
**input-independence** of leakage: a program is constant-time precisely when its
observable trace does *not* depend on the secret input. To even *state* that
non-trivially one needs a trace that *can* depend on the input — i.e. a trace
that threads the runtime valuation through the program's evaluation and may emit
value-dependent observations. A valuation-free trace makes CT vacuous (always
true by `rfl`); a value-carrying trace makes CT a proof obligation.

This module provides the substrate for the RHP / CT-leakage framework on the
dialect `Com`. It defines such a value-carrying trace and proves the property
the trivial shadow *cannot* have: the trace distinguishes inputs.

## What is defined / proved

* `valTag` — a total serialization `(t : CryptoTy) → t.denote → String` of a
  runtime value, used as the value-dependent payload of a leak event. On
  `bit`/`sword`/`pair`/`sum` it serializes the value; on `memref` it
  returns a constant tag (the dialect's memref addresses are static `Fin n`
  indices, so the memory axis is constant-time by construction — see the
  `CryptoDialectLeakTrace` docstring).
* `Com.leakTraceV` — the **value-carrying** dialect leak trace. Unlike
  `Com.leakTrace`, it takes a `Ctxt.Valuation Γ` (the same input valuation that
  `Com.denote` threads) and, at each `Com.var e body`, emits an event
  `pureOp (opName ++ "=" ++ valTag (e.denote V))` whose payload is the runtime
  value of the bound expression. It reuses the `LeakEvent`/`LeakTrace` types of
  `CryptoDialectLeakTrace`.
* `Com.leakTraceV_value_dependent` — the **key non-triviality lemma**: there is
  a concrete `Com catCryptDialect` and two input valuations `V₁ ≠ V₂` with
  `Com.leakTraceV V₁ c ≠ Com.leakTraceV V₂ c`. This is exactly the property the
  valuation-free `Com.leakTrace` (and hence the `rfl`-shadow `Com.all_com_ct`)
  *cannot* have: the value-carrying trace observes the input.
* `Com.isConstantTimeV` — the constant-time predicate over the *value-carrying*
  trace: the trace agrees on any two inputs that agree on the public part of the
  context. This is **not** `rfl` (it is a real ∀-quantified equality of
  value-dependent traces), in contrast to `Com.all_com_ct`.
* `Com.isConstantTimeV_const` — `isConstantTimeV` is inhabited but meaningful: a
  program whose only bound op is a constant (`bvConst`) is constant-time, proved
  by showing the per-step value tag does not depend on the secret input.

The statistical-distance and pipeline RHP results (`LowCTRHP`, the full
pipeline RHP) over this trace are outside the scope of this module.

**0 axioms**; all goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTraceValued

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace

/-! ## 1. Value serialization (the value-dependent leak payload) -/

/-- Total serialization of a runtime dialect value to a `String`, used as the
    value-dependent payload of a leak event.

    On `bit`/`sword` the value is serialized (so the payload
    tracks the runtime value); on `pair`/`sum` it recurses; on `memref` it
    returns a constant tag, because the dialect's memref addresses are static
    `Fin n` indices (the memory axis is constant-time by construction — see the
    `CryptoDialectLeakTrace` module docstring). It is precisely the
    `bit`/`sword` cases that make `leakTraceV` value-dependent. -/
def valTag : (t : CryptoTy) → t.denote → String
  | .bit, b => if b then "1" else "0"
  | .unit, _ => "()"
  | .pair a b, v => "(" ++ valTag a v.1 ++ "," ++ valTag b v.2 ++ ")"
  | .sum a b, v =>
      match v with
      | .inl x => "L" ++ valTag a x
      | .inr y => "R" ++ valTag b y
  | .sword _, w => toString w.toNat
  | .memref _, _ => "mem"
  | .memrefW _ _, _ => "mem"

/-! ## 2. The value-carrying leak trace -/

/-- **Value-carrying dialect leak trace.** Recurses over the ANF
    `Com.ret`/`Com.var` structure exactly like `Com.denote`, threading the input
    `Ctxt.Valuation Γ`. At each `Com.var e body`, it computes the runtime value
    `v := e.denote V` of the bound expression and emits an event
    `pureOp (opName "=" valTag v)` whose payload depends on that value, then
    continues with `V` extended by `v`.

    Unlike the valuation-free `Com.leakTrace`, this trace threads the input and
    so *can* (and, for value-dependent ops, *does*) distinguish inputs — the
    substrate a non-vacuous CT / RHP statement requires. -/
def Com.leakTraceV {Γ : Ctx} {t : CryptoTy} :
    Com catCryptDialect Γ t →
      Ctxt.Valuation (d := catCryptDialect) Γ → LeakTrace
  | .ret _, _ => []
  | .var e body, V =>
      let v := e.denote V
      let baseName := match Expr.leakEvent e with
        | .pureOp n => n
        | .sampleOp => "sample"
      .pureOp (baseName ++ "=" ++ valTag _ v) :: Com.leakTraceV body (V.extend v)

/-! ## 3. Non-triviality: the value-carrying trace distinguishes inputs -/

/-- The witnessing one-binding program: a single context entry `bit` returned
    after `let _ := not(secret)`. Concretely, it binds the negation of the
    head (secret) bit and returns the original secret. The bound op is the
    pure `not`, whose value flips with the input, so `leakTraceV` emits a
    value-dependent event. -/
def witnessProg : Com catCryptDialect [CryptoTy.bit] CryptoTy.bit :=
  .var
    { op := .not
      retTy_eq := rfl
      args := .cons Ctxt.Var.here .nil }
    (.ret (Ctxt.Var.there Ctxt.Var.here))

/-- Input valuation assigning `false` to the single secret bit. -/
def valFalse : Ctxt.Valuation (d := catCryptDialect) [CryptoTy.bit] :=
  .cons false .nil

/-- Input valuation assigning `true` to the single secret bit. -/
def valTrue : Ctxt.Valuation (d := catCryptDialect) [CryptoTy.bit] :=
  .cons true .nil

/-- **Key non-triviality lemma.** The value-carrying trace depends on
    the input: on the concrete program `witnessProg`, the two input valuations
    `valFalse` and `valTrue` produce *different* traces.

    This is exactly the property the valuation-free `Com.leakTrace` — and hence
    the `rfl`-shadow `Com.all_com_ct` — *cannot* have. There, `leakTrace c` is a
    fixed list independent of any input, so no two inputs can ever be
    distinguished. Here, `leakTraceV` threads the value through `Expr.denote`,
    so the leaked payload `not=1` vs `not=0` separates the two inputs. -/
theorem Com.leakTraceV_value_dependent :
    Com.leakTraceV witnessProg valFalse ≠ Com.leakTraceV witnessProg valTrue := by
  decide

/-! ## 4. A non-trivial (not `rfl`) constant-time predicate over the valued trace -/

/-- **Value-carrying constant-time predicate.** A dialect program with a leading
    secret entry is constant-time when its *value-carrying* leak trace agrees on
    any two inputs that share the public part of the context (here: the tail
    `V`), regardless of the secret head value.

    Crucially this is **not** `rfl`: `leakTraceV` is value-dependent, so the
    equality `leakTraceV (s₁ :: V) = leakTraceV (s₂ :: V)` is a proof
    obligation about the program, in contrast to the trivial
    `Com.all_com_ct`, whose body is `rfl` because its trace ignores all
    inputs. -/
def Com.isConstantTimeV {secret : CryptoTy} {Γ : Ctx} {t : CryptoTy}
    (c : Com catCryptDialect (secret :: Γ) t) : Prop :=
  ∀ (s₁ s₂ : secret.denote) (V : Ctxt.Valuation (d := catCryptDialect) Γ),
    Com.leakTraceV c (V.extend s₁) = Com.leakTraceV c (V.extend s₂)

/-- A constant program (bind a `bvConst`, then return it) over a leading secret
    `bit`. Its single bound op is `bvConst 8 0`, whose value is the literal `0`
    independent of any input. -/
def constProg : Com catCryptDialect [CryptoTy.bit] (CryptoTy.sword 8) :=
  .var
    { op := .bvConst 8 0
      retTy_eq := rfl
      args := .nil }
    (.ret Ctxt.Var.here)

/-- **`isConstantTimeV` is inhabited but meaningful.** The constant program
    `constProg` is constant-time under the value-carrying trace: its only bound
    op is `bvConst 8 0`, whose denotation is the fixed value `0` regardless of
    the secret input, so the emitted value tag `bvConst=0` is the same for every
    input and the two traces coincide.

    Unlike `Com.all_com_ct`, this does **not** hold by `rfl` for an arbitrary
    program — it holds *because* the bound expression is input-independent, which
    is precisely the content the value-carrying trace forces one to verify. -/
theorem Com.isConstantTimeV_const : Com.isConstantTimeV constProg := by
  unfold Com.isConstantTimeV
  intro s₁ s₂ V
  cases V
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTraceValued
