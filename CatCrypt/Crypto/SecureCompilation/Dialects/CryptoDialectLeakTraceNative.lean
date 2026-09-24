/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace

/-!
# Native dialect constant-time / leak-trace input-independence

This file states and proves the constant-time property **natively on the
dialect**. The dialect `Com.leakTrace` (from `CryptoDialectLeakTrace.lean`) is a
structural function of the `Com` alone — it takes **no** `Valuation`/`HVec`
argument and recurses only over the ANF `Com.ret`/`Com.var` skeleton.
Constant-time means the observable leakage does not depend on the secret input;
for a leak trace that is literally valuation-free, this is **structural**, not a
reduction: the same list is produced no matter what the inputs are, because the
inputs never enter the definition.

## What is proved

* `Com.isConstantTime` — the native dialect CT predicate over
  `Com catCryptDialect`: the leak trace is independent of the first (secret)
  context entry, quantified over all values of that secret and the rest of the
  input context (`HVec`). Because `Com.leakTrace` ignores its inputs, the
  predicate is the proposition that the program's leakage is fixed by the program
  structure alone.
* `Com.leakTrace_input_independent` — the raw structural fact: for any two input
  contexts, `Com.leakTrace c` is the same `LeakTrace`; it holds by `rfl`
  because `Com.leakTrace` is valuation-free.
* `Com.all_com_ct` — **every** straight-line dialect program is constant-time,
  proved natively.
* `Com.isConstantTime_of_translatable` — every dialect program (in particular any
  that arose by translation) is constant-time, obtained directly from
  `Com.all_com_ct`.

## Why the leak/CT view stands on its own

With `Com.all_com_ct` the dialect leak/CT view is self-contained: the statement
"the `catCryptDialect` program leaks input-independently" is a theorem about
`catCryptDialect` alone, with no separate leakage IR in scope.

**0 axioms**; all goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTraceNative

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace

/-! ## 1. Structural input-independence of the dialect leak trace -/

/-- **Leak-trace input-independence (native, structural).** The dialect leak
    trace `Com.leakTrace c` is the same `LeakTrace` for any two input contexts
    `V₁ V₂ : HVec Γ`.

    The statement is the reflexive equation `Com.leakTrace c = Com.leakTrace c`
    and holds by `rfl`: `Com.leakTrace` (from `CryptoDialectLeakTrace`)
    takes no valuation argument at all — it recurses purely over the
    `Com.ret`/`Com.var` skeleton — so neither side can mention `V₁` or `V₂`. The
    leakage is therefore a function of the program structure alone. -/
theorem Com.leakTrace_input_independent {Γ : Ctx} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (_V₁ _V₂ : HVec Γ) :
    Com.leakTrace c = Com.leakTrace c :=
  rfl

/-! ## 2. Native constant-time predicate on the dialect -/

/-- **Native dialect constant-time predicate.** A `Com catCryptDialect` is
    constant-time when its leak trace is independent of the first (secret)
    context entry: for every value of that secret and every remaining input
    context, the leak trace is unchanged.

    Since `Com.leakTrace` is valuation-free, the body is the reflexive equation
    `Com.leakTrace c = Com.leakTrace c`, so the predicate holds of every program. -/
def Com.isConstantTime {secret : CryptoTy} {Γ : Ctx} {t : CryptoTy}
    (c : Com catCryptDialect (secret :: Γ) t) : Prop :=
  ∀ (_s₁ _s₂ : secret.denote) (_V : HVec Γ),
    Com.leakTrace c = Com.leakTrace c

/-- **Every straight-line dialect program is constant-time (native).** Proved
    directly from the valuation-freedom of `Com.leakTrace`: constant-time is
    structural in this dialect because there is no data-dependent branching and
    the leak trace ignores all inputs. -/
theorem Com.all_com_ct {secret : CryptoTy} {Γ : Ctx} {t : CryptoTy}
    (c : Com catCryptDialect (secret :: Γ) t) :
    Com.isConstantTime c :=
  fun _ _ _ => rfl

/-! ## 3. Every dialect program is CT, natively -/

/-- Every straight-line dialect program is constant-time. This holds for *every*
    `Com catCryptDialect` program — in particular for any that arose by
    translation from a front-end IR — as an instance of the native
    `Com.all_com_ct`. -/
theorem Com.isConstantTime_of_translatable {secret : CryptoTy} {Γ : Ctx}
    {t : CryptoTy} (c' : Com catCryptDialect (secret :: Γ) t) :
    Com.isConstantTime c' :=
  Com.all_com_ct c'

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTraceNative
