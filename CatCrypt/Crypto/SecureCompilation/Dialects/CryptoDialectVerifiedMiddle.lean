/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring

/-!
# Verified-middle leakage RHP on `Com catCryptDialect`

The dialect analogue of `RHPVerifiedMiddle.RHP_leakage_verified_middle`. A
*context* at the dialect level is another `Com catCryptDialect Γ t` (the same
syntactic class as the source), and the linked leakage trace of a source plugged
into a context is the list-monoid concatenation of their `Com.leakTrace`s.

`RHP_leakage_verified_middle_dialect` is the symmetric-adversary RHP on the
verified middle: for every source and target context there is a source context
(namely the target context — the back-translation is the identity at the dialect
level, both contexts inhabiting `Com catCryptDialect Γ t`) whose linked leakage
trace agrees. The statement is reflexive; the asymmetric-adversary version
(target contexts observing more than source contexts) is outside its scope.
Stated over `Com.leakTrace`.
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

/-- **Verified-middle leakage RHP on `catCryptDialect`.** For every source program
    and dialect-level target context there is a source context whose linked
    leakage trace agrees; the witness is the target context itself (identity
    back-translation, both contexts in `Com catCryptDialect Γ t`). The dialect
    analogue of `RHPVerifiedMiddle.RHP_leakage_verified_middle`, reflexive, over
    `Com.leakTrace`. -/
theorem RHP_leakage_verified_middle_dialect {Γ : Ctx} {t : CryptoTy}
    (sourceProg : Com catCryptDialect Γ t) (targetCtx : DialectCtx Γ t) :
    ∃ sourceCtx : DialectCtx Γ t,
      linkedLeakTraceCom sourceProg sourceCtx = linkedLeakTraceCom sourceProg targetCtx :=
  ⟨targetCtx, rfl⟩

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectVerifiedMiddle
