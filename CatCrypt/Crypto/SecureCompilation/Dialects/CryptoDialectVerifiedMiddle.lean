/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring

/-!
# Contexts and linked leakage traces on `Com catCryptDialect`

A *context* at the dialect level is another `Com catCryptDialect Γ t` (the same
syntactic class as the source), and the linked leakage trace of a source plugged
into a context is the list-monoid concatenation of their `Com.leakTrace`s.
`Com.leakTrace` reads no valuation, so this trace is not constant-time evidence.

## Main definitions

* `DialectCtx`: the contexts at the dialect level.
* `linkedLeakTraceCom`: the leakage trace of a program linked with a context.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectVerifiedMiddle

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace

/-- A context at the dialect level is itself a `Com catCryptDialect Γ t`. -/
abbrev DialectCtx (Γ : Ctx) (t : CryptoTy) : Type := Com catCryptDialect Γ t

/-- Linked leakage trace of a source program plugged into a context: the source's
    leakage events followed by the context's (list-monoid linking). -/
def linkedLeakTraceCom {Γ : Ctx} {t : CryptoTy}
    (source : Com catCryptDialect Γ t) (ctx : DialectCtx Γ t) : LeakTrace :=
  Com.leakTrace source ++ Com.leakTrace ctx

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectVerifiedMiddle
