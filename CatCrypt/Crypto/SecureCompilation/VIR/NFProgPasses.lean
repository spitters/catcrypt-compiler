/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgDCE
public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF

/-!
# The passes on structured programs as certified chain steps

This module instantiates the chains of passes of `VIR/PassChain.lean` at structured
programs. The program type of a step is `NFProg d Γ ts`, so the dialect, the context and
the result types are indices of the type. The semantics `nfSem fuel d Γ ts` has the
valuations of `Γ` as inputs, the result tuples of `ts` as outputs, and `NFProg.denote` at
the fuel `fuel` as denotation; the fuel is a parameter of the semantics, so the steps are
free of it. A lowering along a partial block lowering `P` is a step from
`NFProg d Γ ts` to `NFProg d' (P.mapCtx Γ) (ts.map P.mapTy)`: the target context and
result types are computed from the source by the maps of `P`, so a chain step after it is
stated at those indices and adjacency holds by unfolding.

## Main definitions

* `NFProgPasses.nfSem`: the semantics of structured programs at a fuel;
  `NFProgPasses.nfSemE`: the same at an explicit call environment.
* `NFProgPasses.mapStep`, `NFProgPasses.dceStep`, `NFProgPasses.aegraphStep`,
  `NFProgPasses.lowerSelectsStep`: the lowering along a partial block lowering,
  dead-code elimination, the e-graph stage and the select lowering as chain steps.
* `PassChain.StepCert.ofMap?`: the certificate of the lowering along a partial block
  lowering, with the graph of the valuation transport as input relation and the graph
  of the transport of result tuples as output relation; `PassChain.StepCert.ofMapAt?`:
  the same between the semantics at two call environments.
* `NFProgPasses.dceCert`, `NFProgPasses.aegraphCert`, `NFProgPasses.lowerSelectsCert`:
  the certificates of the three endo-passes, at equal inputs and outputs.

## Main results

The certificates are built from `NFProg.map?_denote_call`, `NFProg.map?_denoteAt`,
`NFProg.denote_dce`,
`aegraphOptNF_denote` and `NFProg.denote_lowerSelects` with the generic constructors
`PassChain.StepCert.ofTransport`, `PassChain.StepCert.ofRefines` and
`PassChain.StepCert.ofDenoteEq`; their preservation statement through a chain is
`PassChain.Cert.sound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Valuation)
open BlockLoweringExtend (transArgs)
open Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_denote)
open Optimizer.Rewrite.AegraphGeneric (RuleSet)

namespace NFProgPasses

/-! ## 1. The semantics and the endo-passes -/

/-- The semantics of structured programs over `d` at the context `Γ` and the result
    types `ts`, at the fuel `fuel`: inputs are valuations of `Γ`, outputs are result
    tuples, and the denotation is `NFProg.denote fuel`. -/
def nfSem (fuel : Nat) (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] [CallDenote d] (Γ : Ctxt d)
    (ts : List d.Ty) : PassChain.Sem (NFProg d Γ ts) where
  In := Valuation Γ
  Out := Valuation ts
  den p V := p.denote fuel V

/-- The semantics of structured programs over `d` at the context `Γ` and the result
    types `ts`, at the call environment `E` and the fuel `fuel`: the denotation is
    `NFProg.denoteAt E fuel`. -/
def nfSemE {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] [DialectDenoteM d Option] (E : CallEnv d) (fuel : Nat) (Γ : Ctxt d)
    (ts : List d.Ty) : PassChain.Sem (NFProg d Γ ts) where
  In := Valuation Γ
  Out := Valuation ts
  den p V := p.denoteAt E fuel V

section Endo

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- Dead-code elimination as a chain step. -/
def dceStep (Γ : Ctxt d) (ts : List d.Ty) : PassChain.Step (NFProg d Γ ts) (NFProg d Γ ts) :=
  ⟨"dce", fun p => some (NFProg.dce p)⟩

/-- The certificate of dead-code elimination: the eliminated program keeps every
    successful run, from `NFProg.denote_dce`. -/
def dceCert [DialectDenoteM d Option] [CallDenote d] (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.StepCert (dceStep Γ ts).run (nfSem fuel d Γ ts) (nfSem fuel d Γ ts) :=
  PassChain.StepCert.ofRefines _ fun p q _ _ hf hd => by
    cases hf
    exact NFProg.denote_dce p hd

/-- The select lowering as a chain step. -/
def lowerSelectsStep [DialectDenoteM d Option] [HasSelect d] (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.Step (NFProg d Γ ts) (NFProg d Γ ts) :=
  ⟨"lowerSelects", fun p => some (NFProg.lowerSelects p)⟩

/-- The certificate of the select lowering: the lowered program has the denotation of
    its input, from `NFProg.denote_lowerSelects`. -/
def lowerSelectsCert [DialectDenoteM d Option] [HasSelect d] [CallDenote d] (fuel : Nat) (Γ : Ctxt d)
    (ts : List d.Ty) :
    PassChain.StepCert (lowerSelectsStep Γ ts).run (nfSem fuel d Γ ts) (nfSem fuel d Γ ts) :=
  PassChain.StepCert.ofDenoteEq _ fun p q hf => by
    cases hf
    funext V
    exact NFProg.denote_lowerSelects fuel p V

variable [DecidableEq d.Ty] [DialectDenote d] [DecidableEq d.Op]

/-- The e-graph pass `aegraphOptNF` at the rule set `R` as a chain step. -/
def aegraphStep (R : RuleSet d) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.Step (NFProg d Γ ts) (NFProg d Γ ts) :=
  ⟨"aegraph", fun p => some (aegraphOptNF R p)⟩

/-- The certificate of the e-graph stage: the optimised program has the denotation of
    its input, from `aegraphOptNF_denote`. -/
def aegraphCert [CallDenote d] (R : RuleSet d) (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.StepCert (aegraphStep R Γ ts).run (nfSem fuel d Γ ts) (nfSem fuel d Γ ts) :=
  PassChain.StepCert.ofDenoteEq _ fun p q hf => by
    cases hf
    exact aegraphOptNF_denote R p fuel

end Endo

/-! ## 2. The lowering along a partial block lowering -/

section Map

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- The lowering of structured programs along the partial block lowering `P`, at the
    identity renaming, as a chain step from `NFProg d Γ ts` to
    `NFProg d' (P.mapCtx Γ) (ts.map P.mapTy)`. -/
def mapStep (P : PartialBlockLowering d d') (hT : P.RegionTypes) (Γ : Ctxt d)
    (ts : List d.Ty) :
    PassChain.Step (NFProg d Γ ts) (NFProg d' (P.mapCtx Γ) (ts.map P.mapTy)) :=
  ⟨"map?", fun p => NFProg.map? P hT p (fun v => v)⟩

end Map

end NFProgPasses

section MapCert

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
  [DialectDenote d] [DialectDenote d']

open NFProgPasses in
/-- **The certificate of the lowering along a partial block lowering, at call
    environments.** Under the variable leaf, the block leaf on every expression `P`
    accepts, the binding-threading leaf, `RegionTransports`, and the agreement `hCall` of
    the call environments `E` and `E'` along the transport at every call, the step
    `mapStep P hT Γ ts` is certified from the semantics at `E` to the semantics at `E'`, at
    every fuel, with the graph of `mapVal` as input relation and the graph of the transport
    of result tuples as output relation, from `NFProg.map?_denoteAt`. -/
def PassChain.StepCert.ofMapAt? (P : PartialBlockLowering d d') (hT : P.RegionTypes)
    (transTy : P.TransTy) (mapVal : P.MapVal) (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denote (mapVal V) = transTy (e.denote V))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (E : CallEnv d) (E' : CallEnv d')
    (hCall : E.Transports E' (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x)
      (fun _ _ _ => True))
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.StepCert (mapStep P hT Γ ts).run (nfSemE E fuel Γ ts)
      (nfSemE E' fuel (P.mapCtx Γ) (ts.map P.mapTy)) :=
  PassChain.StepCert.ofTransport _ _ mapVal (transArgs P.mapTy transTy) fun p q V hf =>
    NFProg.map?_denoteAt P transTy mapVal hT (fun _ => True) hVar
      (fun e _ blk hb V => hBlk e blk hb V) hExt hR E E' fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) (hCall.mono fun _ _ _ _ => trivial)
      _ V (mapVal V) (FieldDialectBlockDescent.pullV_id _) q hf

variable [CallDenote d] [CallDenote d']

open NFProgPasses in
/-- **The certificate of the lowering along a partial block lowering.** Under the
    variable leaf, the block leaf on every expression `P` accepts, the binding-threading
    leaf, `RegionTransports`, and the agreement `hCall` of the call environments of `d` and
    `d'` along the transport at every call, the step `mapStep P hT Γ ts` is certified at
    every fuel with the graph of `mapVal` as input relation and the graph of the transport
    of result tuples as output relation, from `NFProg.map?_denote_call`. The default proof
    of `hCall` is `CallEnv.transports_empty`, which closes it where both dialects denote
    calls in the empty environment. -/
def PassChain.StepCert.ofMap? (P : PartialBlockLowering d d') (hT : P.RegionTypes)
    (transTy : P.TransTy) (mapVal : P.MapVal) (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denote (mapVal V) = transTy (e.denote V))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty)
    (hCall : (CallDenote.env (d := d)).Transports (CallDenote.env (d := d'))
      (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x) (fun _ _ _ => True) := by
      exact CallEnv.transports_empty _ _ _) :
    PassChain.StepCert (mapStep P hT Γ ts).run (nfSem fuel d Γ ts)
      (nfSem fuel d' (P.mapCtx Γ) (ts.map P.mapTy)) :=
  PassChain.StepCert.ofTransport _ _ mapVal (transArgs P.mapTy transTy) fun p q V hf =>
    NFProg.map?_denote_call P transTy mapVal hT (fun _ => True) hVar
      (fun e _ blk hb V => hBlk e blk hb V) hExt hR fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) (hCall.mono fun _ _ _ _ => trivial)
      _ V (mapVal V) (FieldDialectBlockDescent.pullV_id _) q hf

end MapCert

end CatCrypt.Crypto.SecureCompilation.VIR
