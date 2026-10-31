/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain

@[expose] public section

set_option autoImplicit false

/-!
# Semantics and the route wrapper of the route chains

The pieces of a `PassChain.Chain` that every route of the hax compiler shares: the
semantics `comSemOf` of straight-line programs of a dialect (inputs are valuations, outputs
values, every run succeeds), the semantics `routeSem` of route programs, and the last step
of every route chain, the route wrapper `RouteProg.straight` (`straightStep`) with its
certificate `straightCert`.

The declarations live in the namespace `Haxc.FieldChain`, beside the chains of the field
route (`FieldRoute`).

## Main definitions

* `comSemOf`, `routeSem`: the semantics of straight-line programs and of route programs.
* `straightStep`, `straightCert`: the route wrapper as a chain step and its certificate.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg)

/-- The semantics of straight-line programs of `d` over `Γ` of type `t`: inputs are
    valuations of `Γ`, outputs values of `t`, and every run succeeds with the
    denotation. -/
def comSemOf (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    (Γ : Ctxt d) (t : d.Ty) : Sem (Com d Γ t) where
  In := Valuation Γ
  Out := ⟦t⟧
  den c V := some (c.denote V)

/-- The semantics of route programs over `Γ` of type `t`: every run succeeds with
    `RouteProg.denote`. -/
def routeSem (Γ : Ctxt jasminDialect) (t : JasminTy) : Sem (RouteProg Γ t) where
  In := Valuation Γ
  Out := ⟦t⟧
  den p V := some (p.denote V)

/-- The route wrapper `RouteProg.straight` as a chain step. -/
def straightStep (Γ : Ctxt jasminDialect) (t : JasminTy) :
    Step (Com jasminDialect Γ t) (RouteProg Γ t) :=
  ⟨"straight", fun c => some (.straight c)⟩

/-- The certificate of the route wrapper: the transport at the identity. -/
def straightCert (Γ : Ctxt jasminDialect) (t : JasminTy) :
    StepCert (straightStep Γ t).run (comSemOf jasminDialect Γ t) (routeSem Γ t) :=
  StepCert.ofTransport _ _ id id fun c q V hf => by
    cases hf
    exact congrArg some (RouteProg.denote_straight c V)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain
