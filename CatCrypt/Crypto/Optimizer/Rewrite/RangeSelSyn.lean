/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn
public meta import CatCrypt.Crypto.Optimizer.Rewrite.RangeSelNF
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeSelNF

/-!
# The range-conditioned selections at the synthesised annotation and from entry environments

The pass `RangeSelNF.rangeSel` takes the annotation `RangeNFLoop.CarriedAnn` of the range
stage. This file states it at the annotation `RangeAnnSyn.synAnn` the synthesiser computes,
and from an abstract environment of the inputs. Its target dialect `SelDialect.jasminSel`
has no lowering, so no chain of the compiler runs it.

`entrySel A a p` is the traversal `RangeSelNF.selGo` from the abstract environment `A` of
the inputs. Its denotation theorem holds at every valuation `V` with `EnvOK A V`. The
certificate `inputSelCert` has the input relation `V = W ∧ EnvOK A V` and equality of
results as output relation.

## Main results

* `synSel_denote`: `rangeSel` at `synAnn p` denotes what `p` denotes.
* `synSelStep`, `synSelCert`: the chain step of the pass at `synAnn`, with its certificate.
* `entrySel`: the pass from an abstract environment of the inputs.
* `entrySel_denote`: under `EnvOK A V` the output denotes at `V` what the input denotes at
  `V`.
* `entrySel_leakRun`: under `EnvOK A V` and a leakage model whose `regArith` operations are
  quiet, the leakage run of `entrySel A a p` at `V` is that of `p`.
* `entrySel_topEnv`: at `topEnv` the entry form is `rangeSel`.
* `inputSelStep`, `inputSelCert`: the chain step of the entry form, with a certificate
  whose input relation is `V = W ∧ EnvOK A V`.
* On `RangeNFLoop.lazyAddLoop`, `rangeSel` at the synthesised annotation binds one unsigned
  minimum, as under `RangeNFLoop.lazyAddAnn`; on `RangeAnnSyn.plainAddLoop` it binds none
  from the full lane range and one from `RangeAnnSyn.plainAddEnv` (`#kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop
open CatCrypt.Crypto.Optimizer.Rewrite.RangeSelNF
open CatCrypt.Crypto.SecureCompilation.VIR.SelDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-! ## 1. The pass at the synthesised annotation -/

/-- `rangeSel` at the synthesised annotation denotes what its input denotes. -/
theorem synSel_denote {Γ : JCtxt} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (fuel : Nat) (V : Ctxt.Valuation Γ) :
    (rangeSel (synAnn p) p).denote fuel V = p.denote fuel V :=
  rangeSel_denote (synAnn p) p fuel V

open NFProgPasses (nfSem)

/-- The pass `rangeSel` at the synthesised annotation, as a chain step. -/
def synSelStep (Γ : JCtxt) (ts : List JasminTy) :
    PassChain.Step (NFProg jasminDialect Γ ts) (NFProg jasminSel Γ ts) :=
  selStep Γ ts synAnn

/-- The certificate of `synSelStep`: at the same valuation the output has the denotation of
    its input. -/
def synSelCert (fuel : Nat) (Γ : JCtxt) (ts : List JasminTy) :
    PassChain.StepCert (synSelStep Γ ts).run (nfSem fuel jasminDialect Γ ts)
      (nfSem fuel jasminSel Γ ts) :=
  selCert fuel Γ ts synAnn

/-! ## 2. The pass from an abstract environment of the inputs -/

/-- The range-conditioned selections from the abstract environment `A` of the inputs. -/
def entrySel {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) : NFProg jasminSel Γ ts :=
  selGo A [] Γ.length a (VarMap.same Γ) p

/-- **Denotation of the selections from an entry environment.** At a valuation of which
    `A` holds, `entrySel A a p`, read in `jasminSel`, denotes what `p` denotes, at every
    fuel and for every annotation. -/
theorem entrySel_denote {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) (fuel : Nat) (V : Ctxt.Valuation Γ) (hA : EnvOK A V) :
    (entrySel A a p).denote fuel V = p.denote fuel V :=
  selGo_denote fuel A [] Γ.length a (VarMap.same Γ) p V V rfl hA (fun _ h => nomatch h)
    (VarMap.OK.same V)

/-- **Leakage run of the selections from an entry environment.** Under a leakage model `L`
    whose `regArith` operations are quiet, at a valuation of which `A` holds,
    `entrySel A a p` runs under `jasminSelLeak L` to the results and the events of the run
    of `p` under `L`. -/
theorem entrySel_leakRun {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat) {Γ : JCtxt}
    {ts : List JasminTy} (A : AEnv Γ) (a : CarriedAnn) (p : NFProg jasminDialect Γ ts)
    (V : Ctxt.Valuation Γ) (hA : EnvOK A V) :
    NFProg.leakRun (jasminSelLeak L) fuel (entrySel A a p) V = NFProg.leakRun L fuel p V :=
  selGo_leakRun hq fuel A [] Γ.length a (VarMap.same Γ) p V V rfl hA (fun _ h => nomatch h)
    (VarMap.OK.same V)

/-- At the full lane range of every input the entry form is `rangeSel`. -/
theorem entrySel_topEnv {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) : entrySel (topEnv Γ) a p = rangeSel a p :=
  rfl

/-- The pass `entrySel A` as a chain step, at the annotation `syn p` computed from the
    input `p`. -/
def inputSelStep {Γ : JCtxt} (ts : List JasminTy) (A : AEnv Γ)
    (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.Step (NFProg jasminDialect Γ ts) (NFProg jasminSel Γ ts) :=
  ⟨"range-sel-entry", fun p => some (entrySel A (syn p) p)⟩

/-- The certificate of `inputSelStep`. The input relation is equality of the two
    valuations together with `EnvOK A` of the valuation; the output relation is equality.
    A successful run of the input at a valuation of which `A` holds is a run of the output,
    read in `jasminSel`, with the same result. -/
def inputSelCert (fuel : Nat) {Γ : JCtxt} (ts : List JasminTy) (A : AEnv Γ)
    (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.StepCert (inputSelStep ts A syn).run (nfSem fuel jasminDialect Γ ts)
      (nfSem fuel jasminSel Γ ts) where
  relIn V W := V = W ∧ EnvOK A V
  relOut := Eq
  sound := by
    intro p q V W o hf hVW hd
    obtain ⟨rfl, hA⟩ := hVW
    cases hf
    exact ⟨o, (entrySel_denote A (syn p) p fuel V hA).trans hd, rfl⟩

/-! ## 3. Instances -/

/- Under the synthesised annotation `rangeSel` binds one unsigned minimum on
   `lazyAddLoop`, as under `lazyAddAnn`. The budget covers the start of the evaluator at
   the first check of the file. -/
set_option kat.ms 3000 in
#kat bindCount isUmin (rangeSel (synAnn lazyAddLoop) lazyAddLoop) == 1

/- From the full lane range no unsigned minimum is bound on `plainAddLoop`. -/
#kat bindCount isUmin (rangeSel (synAnn plainAddLoop) plainAddLoop) == 0

/- From `plainAddEnv` one unsigned minimum is bound. -/
#kat bindCount isUmin
  (entrySel plainAddEnv (entryAnn plainAddEnv plainAddLoop) plainAddLoop) == 1

end CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn
