/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.EcRoute
public import CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphField
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphFieldGood
public import CatCrypt.Crypto.Optimizer.Rewrite.GvnMulti
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain
public import CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs

@[expose] public section

set_option autoImplicit false

/-!
# The field route as a chain of passes

The field route of `FieldRoute` at the field e-graph, as a `PassChain.Chain` with its
certificate. For a rule set `R` over `fieldDialect`, a coverage decision `good` and a limb
lowering `low` to word arrays, `limbChain R Γ t good low` is the limb chain
`FieldRoute`'s `limbChainVia` at the e-graph step; it has four steps:

1. `comAegraphStep R`: the acyclic e-graph `aegraphOptOf R` on `Com fieldDialect`;
2. `limbStep good low`: the limb lowering to `Com jasminDialect` over word arrays, which
   refuses a program that `good` rejects;
3. `Step.id`: the jasmin-level step, the identity, since `compileField` applies no
   optimisation at that level;
4. `straightStep`: the route wrapper `RouteProg.straight`.

The semantics are `comSemOf` for straight-line programs (inputs are valuations, outputs
values, every run succeeds) and `routeSem` for route programs (`RouteChain`). The
certificate `limbChainCert` is `limbChainViaCert` at the e-graph step: one step
certificate per step, `StepCert.ofDenoteEq` for the e-graph, `limbCert` for the lowering,
whose input relation `limbIn` relates a valuation to the word arrays holding the limbs of
its values and whose output relation reads the limbs of the output array, `StepCert.id`,
and `StepCert.ofTransport` at the identity for the wrapper (`straightCert`).

At the Montgomery record `P` the chain `fieldChainOf R P` runs to
`compileField P (aegraphOptOf R c)`, and at the Solinas record `S` the chain
`fieldChainSOf R S` runs to `compileFieldS S (aegraphOptOf R c)`. The templates
`montTemplateOf R P` and `solinasTemplateOf R S` route by these chains, so
`FieldTemplate.route_abi_denote` holds for them. At the field rule set
`AegraphField.fieldRules` the chains are `fieldChain P` and `fieldChainS S`, and the
templates `montTemplateC P` and `solinasTemplateC S`.

The lane chain `lanesChain N pure` is `NttRoute`'s `lanesChainVia` at the value numbering
`gvnMR pure` on `MultiReturnCom jasminDialect`, at the semantics `mrSem`, then the lane
lowering `lanesCom` and the route wrapper.

The tower chain `towerChain P N` takes a `towerDialect` program to a route program over
arrays of `N` words: the identity, the lowering `TowerToLimbs.towerCom P N` guarded by
`towerGoodB P N` (`towerStep`), the identity at the jasmin level and the route wrapper. Its
certificate `towerChainCert` carries the input relation `towerIn`, under which each input
array holds the Montgomery limbs of the coordinates of its value.

## Main definitions

* `comAegraphStep`, `comAegraphCert`: the e-graph pass on `Com` as a step and its
  certificate.
* `limbChain`, `limbChainCert`: the chain and its certificate.
* `fieldChainOf`, `fieldChainSOf`: the chain at a Montgomery and at a Solinas record.
* `montTemplateOf`, `solinasTemplateOf`: the templates routed by the chains.
* `fieldChain`, `fieldChainCert`, `fieldChainS`, `montTemplateC`, `solinasTemplateC`: the
  chains, the certificate and the templates at `fieldRules`.
* `gvnStep`, `gvnCert`, `lanesChain`, `lanesChainCert`: the lane chain and its
  certificate.
* `towerStep`, `towerCert`, `towerChain`, `towerChainCert`: the tower chain and its
  certificate.

## Main results

* `limbChain_run`, `limbChain_denote`: the run of the chain, and the output limbs of a
  program it produces, from `Cert.sound`.
* `fieldChainOf_run`, `fieldChainOf_denote`: the chain runs to `compileField` of the
  e-graph output, and the output array of its program holds the encoding of the value of
  the source program (the statement of `compileField_denote`).
* `fieldChainSOf_run`, `fieldChainSOf_denote`: the same at a Solinas record.
* `fieldChain_run`, `fieldChain_denote`, `fieldChainS_run`,
  `montTemplateC_route_abi_denote`: the same at `fieldRules`, with
  `compileField P (aegraphOptField c)` as the run.
* `lanesChain_run`, `lanesChain_denote`: the lane chain runs to the lane lowering of the
  numbered program, and the words of its output array are the results of the lane program
  at the input words.
* `towerChain_run`, `towerChain_denote`: the tower chain runs to the wrapped lowering of an
  accepted program, and the output array of its program holds the Montgomery limbs of the
  coordinates of the value of the source program.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams enc)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## 1. The e-graph step on `Com` -/

section Generic

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

variable [DecidableEq d.Ty] [DecidableEq d.Op]

/-- The e-graph pass `aegraphOptOf` at the rule set `R` on `Com d Γ t` as a chain step. -/
def comAegraphStep (R : RuleSet d) (Γ : Ctxt d) (t : d.Ty) : Step (Com d Γ t) (Com d Γ t) :=
  ⟨"aegraph", fun c => some (aegraphOptOf R c)⟩

/-- The certificate of the e-graph step: the optimised program has the denotation of its
    input, from `aegraphOptOf_denote`. -/
def comAegraphCert (R : RuleSet d) (Γ : Ctxt d) (t : d.Ty) :
    StepCert (comAegraphStep R Γ t).run (comSemOf d Γ t) (comSemOf d Γ t) :=
  StepCert.ofDenoteEq _ fun c q hf => by
    cases hf
    funext V
    show some _ = some _
    rw [aegraphOptOf_denote]

end Generic

/-! ## 2. The chain and its certificate -/

section Chain

variable {n : Nat}

/-- The e-graph step has the denotation of its input. -/
theorem comAegraphStep_denote (R : RuleSet fieldDialect) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c q : Com fieldDialect Γ t) (hf : (comAegraphStep R Γ t).run c = some q) :
    q.denote = c.denote := by
  cases hf
  exact aegraphOptOf_denote R c

/-- **The limb chain**: the limb chain `limbChainVia` at the e-graph step at the rule set
    `R`, with the limb lowering `low` guarded by `good`, the identity at the jasmin level
    and the route wrapper. -/
def limbChain (R : RuleSet fieldDialect) (Γ : Ctxt fieldDialect) (t : FieldTy)
    (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n)) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  limbChainVia (comAegraphStep R Γ t) good low

/-- **The certificate of the limb chain**: one step certificate per step. -/
def limbChainCert (R : RuleSet fieldDialect) (Γ : Ctxt fieldDialect) (t : FieldTy)
    (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n))
    (enc : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t))
    (h : ∀ c, good c = true → ∀ (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
      (o : Fin n → BitVec 64), arrFlat A = flatVal (fun {t} x => enc (t := t) x) V →
      arrLimbs ((low c).denote (hvAppend A (.cons o .nil))) n 0 = enc (c.denote V)) :
    Cert (limbChain R Γ t good low) (comSemOf fieldDialect Γ t)
      (routeSem (LimbCtx n Γ) (arrTy n)) :=
  limbChainViaCert (comAegraphStep R Γ t) (comAegraphStep_denote R) good low enc h

/-- The limb chain runs to the wrapped lowering of the e-graph output when `good` accepts
    it, and refuses otherwise. -/
theorem limbChain_run (R : RuleSet fieldDialect) (Γ : Ctxt fieldDialect) (t : FieldTy)
    (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n))
    (c : Com fieldDialect Γ t) :
    (limbChain R Γ t good low).run c =
      if good (aegraphOptOf R c) then some (.straight (low (aegraphOptOf R c))) else none := by
  simp only [limbChain, limbChainVia, Chain.run, comAegraphStep, limbStep, Option.bind_some]
  split <;> rfl

/-- **The output limbs of a program of the limb chain**, from `Cert.sound` of
    `limbChainCert`: for input arrays holding the limbs of the values of `V`, the output
    array holds the limbs of the value of the source program. -/
theorem limbChain_denote (R : RuleSet fieldDialect) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n))
    (enc : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t))
    (h : ∀ c, good c = true → ∀ (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
      (o : Fin n → BitVec 64), arrFlat A = flatVal (fun {t} x => enc (t := t) x) V →
      arrLimbs ((low c).denote (hvAppend A (.cons o .nil))) n 0 = enc (c.denote V))
    {c : Com fieldDialect Γ t} {rp : RouteProg (LimbCtx n Γ) (arrTy n)}
    (hrun : (limbChain R Γ t good low).run c = some rp) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => enc (t := t) x) V) :
    arrLimbs (rp.denote (hvAppend A (.cons o .nil))) n 0 = enc (c.denote V) :=
  limbChainVia_denote (comAegraphStep R Γ t) (comAegraphStep_denote R) good low enc h hrun
    V A o hA

end Chain

/-! ## 3. The chain at a Montgomery record -/

section Mont

variable {n : Nat} (R : RuleSet fieldDialect) (P : LimbParams n)

/-- **The field chain at the Montgomery record `P`**: the limb chain at `GoodVB P` and
    `fieldCom P`. -/
def fieldChainOf (Γ : Ctxt fieldDialect) (t : FieldTy) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  limbChain R Γ t (GoodVB P) (fieldCom P)

/-- The field chain runs to `compileField P` of the e-graph output. -/
theorem fieldChainOf_run {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    (fieldChainOf R P Γ t).run c = compileField P (aegraphOptOf R c) := by
  rw [fieldChainOf, limbChain_run, compileField_eq]

/-- **The output array of a program of the field chain**: the statement of
    `compileField_denote` for the chain. -/
theorem fieldChainOf_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    {c : Com fieldDialect Γ t} {p : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}
    (h : (fieldChainOf R P Γ t).run c = some p) (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
    (o : Fin n → BitVec 64) (hA : arrFlat A = flatVal (fun {t} x => encL P (t := t) x) V) :
    arrLimbs (p.denote (hvAppend A (.cons o .nil))) n 0 = encL P (c.denote V) :=
  limbChain_denote R _ _ (fun {t} x => encL P (t := t) x)
    (fun c hc => fieldCom_denote P hn c (GoodVB_sound P c hc)) h V A o hA

/-- **The Montgomery template routed by the field chain** at the rule set `R`. -/
def montTemplateOf (hn : n < 2 ^ 64) : FieldTemplate n :=
  { montTemplate P hn with
    route := fun {Γ t} c => (fieldChainOf R P Γ t).run c
    route_denote := fun h => fieldChainOf_denote R P hn h }

end Mont

/-! ## 4. The chain at a Solinas record -/

section Solinas

variable {n : Nat} (R : RuleSet fieldDialect) (S : SolinasParams n)

/-- **The field chain at the Solinas record `S`**: the limb chain at `GoodLB S` and the
    Solinas blocks `lowerOpL S`. -/
def fieldChainSOf (Γ : Ctxt fieldDialect) (t : FieldTy) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  limbChain R Γ t (FieldToJasminLimbsSolinas.GoodLB S)
    (fieldComOf (FieldToJasminLimbsSolinas.lowerOpL S))

/-- The Solinas field chain runs to `compileFieldS S` of the e-graph output. -/
theorem fieldChainSOf_run {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    (fieldChainSOf R S Γ t).run c = compileFieldS S (aegraphOptOf R c) := by
  rw [fieldChainSOf, limbChain_run, compileFieldS_eq]

/-- **The output array of a program of the Solinas field chain**: the statement of
    `compileFieldS_denote` for the chain. -/
theorem fieldChainSOf_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    {c : Com fieldDialect Γ t} {p : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}
    (h : (fieldChainSOf R S Γ t).run c = some p) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => FieldToJasminLimbsSolinas.encL S (t := t) x) V) :
    arrLimbs (p.denote (hvAppend A (.cons o .nil))) n 0
      = FieldToJasminLimbsSolinas.encL S (c.denote V) :=
  limbChain_denote R _ _ (fun {t} x => FieldToJasminLimbsSolinas.encL S (t := t) x)
    (fun c hc => fieldComOf_denote (FieldToJasminLimbsSolinas.lowerOpL S)
      (fun {t} x => FieldToJasminLimbsSolinas.encL S (t := t) x)
      (FieldToJasminLimbsSolinas.GoodL S) (FieldToJasminLimbsSolinas.blockSquareL S) hn c
      (FieldToJasminLimbsSolinas.GoodLB_sound S c hc)) h V A o hA

/-- **The Solinas template routed by the Solinas field chain** at the rule set `R`. -/
def solinasTemplateOf (hn : n < 2 ^ 64) : FieldTemplate n :=
  { solinasTemplate S hn with
    route := fun {Γ t} c => (fieldChainSOf R S Γ t).run c
    route_denote := fun h => fieldChainSOf_denote R S hn h }

end Solinas

/-! ## 5. The chains at the field rule set -/

section FieldRules

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphField (fieldRules aegraphOptField)

variable {n : Nat}

/-- **The field chain** at the Montgomery record `P`: the field e-graph `fieldRules`, the
    limb lowering `fieldCom P` guarded by `GoodVB P`, the identity at the jasmin level and
    the route wrapper. -/
def fieldChain (P : LimbParams n) (Γ : Ctxt fieldDialect) (t : FieldTy) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  fieldChainOf fieldRules P Γ t

/-- The certificate of the field chain. -/
def fieldChainCert (P : LimbParams n) (hn : n < 2 ^ 64) (Γ : Ctxt fieldDialect) (t : FieldTy) :
    Cert (fieldChain P Γ t) (comSemOf fieldDialect Γ t) (routeSem (LimbCtx n Γ) (arrTy n)) :=
  limbChainCert fieldRules Γ t (GoodVB P) (fieldCom P) (fun {t} x => encL P (t := t) x)
    (fun c hc => fieldCom_denote P hn c (GoodVB_sound P c hc))

theorem fieldChain_run (P : LimbParams n) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) :
    (fieldChain P Γ t).run c = compileField P (aegraphOptField c) :=
  fieldChainOf_run fieldRules P c

/-- **The output array of a program of the field chain**: the statement of
    `compileField_denote`. -/
theorem fieldChain_denote (P : LimbParams n) (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect}
    {t : FieldTy} {c : Com fieldDialect Γ t} {p : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}
    (h : (fieldChain P Γ t).run c = some p) (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
    (o : Fin n → BitVec 64) (hA : arrFlat A = flatVal (fun {t} x => encL P (t := t) x) V) :
    arrLimbs (p.denote (hvAppend A (.cons o .nil))) n 0 = encL P (c.denote V) :=
  fieldChainOf_denote fieldRules P hn h V A o hA

/-- **The Montgomery template routed by the field chain.** -/
def montTemplateC (P : LimbParams n) (hn : n < 2 ^ 64) : FieldTemplate n :=
  montTemplateOf fieldRules P hn

/-- **The Solinas field chain** at the Solinas record `S`, with the field e-graph. -/
def fieldChainS (S : SolinasParams n) (Γ : Ctxt fieldDialect) (t : FieldTy) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  fieldChainSOf fieldRules S Γ t

theorem fieldChainS_run (S : SolinasParams n) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) :
    (fieldChainS S Γ t).run c = compileFieldS S (aegraphOptField c) :=
  fieldChainSOf_run fieldRules S c

/-- **The Solinas template routed by the Solinas field chain.** -/
def solinasTemplateC (S : SolinasParams n) (hn : n < 2 ^ 64) : FieldTemplate n :=
  solinasTemplateOf fieldRules S hn

/-- **The output limbs of a program of the Montgomery template routed by the field chain
    at a machine state**: `FieldTemplate.route_abi_denote` at `montTemplateC`. -/
theorem montTemplateC_route_abi_denote (P : LimbParams n) (hn : n < 2 ^ 64)
    {Γ : Ctxt fieldDialect} {c : Com fieldDialect Γ (.fp P.p)}
    {rp : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}
    (h : (fieldChain P Γ (.fp P.p)).run c = some rp) (sa : AState) (V : Valuation Γ)
    (hV : arrFlat (opVals n sa Γ) = flatVal (fun {t} x => encL P (t := t) x) V) :
    arrLimbs (rp.denote (abiValN n sa Γ)) n 0 = enc P (c.denote V) :=
  (montTemplateC P hn).route_abi_denote (c := c) h sa V hV

end FieldRules

/-! ## 6. The lane route as a chain -/

section Lanes

open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute (lanesCtx lanesCom)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)

section Gvn

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [DecidableEq d.Ty] [DecidableEq d.Op]

/-- The value numbering `gvnMR pure` of a multi-return program as a chain step. -/
def gvnStep (pure : d.Op → Bool) (Γ : Ctxt d) (ts : List d.Ty) :
    Step (MultiReturnCom d Γ ts) (MultiReturnCom d Γ ts) :=
  ⟨"gvn", fun m => some (gvnMR pure m)⟩

/-- The certificate of the value numbering: the numbered program has the denotation of
    its input, from `gvnMR_denote`. -/
def gvnCert (pure : d.Op → Bool) (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (gvnStep pure Γ ts).run (mrSem d Γ ts) (mrSem d Γ ts) :=
  StepCert.ofDenoteEq _ fun m q hf => by
    cases hf
    funext V
    exact congrArg some (gvnMR_denote pure m V)

end Gvn

/-- The value numbering has the denotation of its input, from `gvnMR_denote`. -/
theorem gvnStep_denote {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] [DecidableEq d.Ty] [DecidableEq d.Op] (pure : d.Op → Bool)
    {Γ : Ctxt d} {ts : List d.Ty} (m q : MultiReturnCom d Γ ts)
    (hf : (gvnStep pure Γ ts).run m = some q) : q.denote = m.denote := by
  cases hf
  funext V
  exact gvnMR_denote pure m V

variable {N : Nat}

/-- **The lane chain**: the lane chain `lanesChainVia` at the value numbering
    `gvnMR pure`, with the lane lowering and the route wrapper. -/
def lanesChain (N : Nat) (pure : jasminDialect.Op → Bool) :
    Chain (MultiReturnCom jasminDialect (Rn N) (Rn N)) (RouteProg (lanesCtx N) (arrTy N)) :=
  lanesChainVia (gvnStep pure _ _)

/-- The certificate of the lane chain. -/
def lanesChainCert (hN : N < 2 ^ 64) (pure : jasminDialect.Op → Bool) :
    Cert (lanesChain N pure) (mrSem jasminDialect (Rn N) (Rn N))
      (routeSem (lanesCtx N) (arrTy N)) :=
  lanesChainViaCert hN (gvnStep pure _ _) (gvnStep_denote pure)

theorem lanesChain_run (pure : jasminDialect.Op → Bool)
    (m : MultiReturnCom jasminDialect (Rn N) (Rn N)) :
    (lanesChain N pure).run m = some (.straight (lanesCom (gvnMR pure m))) :=
  rfl

/-- **The output words of a program of the lane chain**, from `Cert.sound`: the words of
    the output array are the results of the lane program at the input words. -/
theorem lanesChain_denote (hN : N < 2 ^ 64) (pure : jasminDialect.Op → Bool)
    {m : MultiReturnCom jasminDialect (Rn N) (Rn N)} {rp : RouteProg (lanesCtx N) (arrTy N)}
    (hrun : (lanesChain N pure).run m = some rp) (a o : Fin N → BitVec 64) :
    arrLimbs (rp.denote (.cons a (.cons o .nil))) N 0 = m.denote (arrLimbs a N 0) :=
  lanesChainVia_denote hN (gvnStep pure _ _) (gvnStep_denote pure) hrun a o

end Lanes

/-! ## 7. The tower chain -/

section Tower

open CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect (towerDialect TowerTy towerMapTys)
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs

variable {n : Nat} (P : LimbParams n) (N : Nat)

/-- The context of a lowered tower program over `Γ`: an array of `N` words for each source
    variable, then the output array. -/
abbrev TowerCtx (N : Nat) (Γ : Ctxt towerDialect) : Ctxt jasminDialect :=
  tArrCtx N Γ ++ [arrTy N]

/-- The lowering of tower programs to word arrays as a chain step: `towerCom P N` on the
    programs that `towerGoodB P N` accepts, and a refusal otherwise. -/
def towerStep (Γ : Ctxt towerDialect) (t : TowerTy) :
    Step (Com towerDialect Γ t) (Com jasminDialect (TowerCtx N Γ) (arrTy N)) :=
  ⟨"towerLimbs", fun c => if towerGoodB P N c then some (towerCom P N c) else none⟩

/-- The input relation of the tower lowering: the input arrays hold the Montgomery limbs of
    the coordinates of the values of `V`, and the output array is arbitrary. -/
def towerIn {Γ : Ctxt towerDialect} (V : Valuation Γ) (W : Valuation (TowerCtx N Γ)) : Prop :=
  ∃ (A : Valuation (tArrCtx N Γ)) (o : Fin N → BitVec 64),
    @Eq (Valuation (TowerCtx N Γ)) W (hvAppend A (.cons o .nil)) ∧
      tArrFlat n A = flatVal (towerLimbEnc P) V

/-- The certificate of the tower lowering, from `towerCom_denoteB`: the input relation is
    `towerIn`, and the output relation says that the output array holds the Montgomery limbs
    of the coordinates of the source value. -/
def towerCert (Γ : Ctxt towerDialect) (t : TowerTy) :
    StepCert (towerStep P N Γ t).run (comSemOf towerDialect Γ t)
      (comSemOf jasminDialect (TowerCtx N Γ) (arrTy N)) where
  relIn := towerIn P N
  relOut x y := arrCoords n y (towerMapTys t) 0 = towerLimbEnc P x
  sound := by
    intro c q V W o hf hVW hd
    obtain ⟨A, o', rfl, hA⟩ := hVW
    simp only [towerStep] at hf
    split at hf
    · rename_i hc
      cases hf
      cases hd
      exact ⟨_, rfl, towerCom_denoteB P N c hc V A o' hA⟩
    · cases hf

/-- **The tower chain** at the Montgomery record `P` over arrays of `N` words: the identity
    at the tower level, the lowering `towerCom P N` guarded by `towerGoodB P N`, the identity
    at the jasmin level and the route wrapper. -/
def towerChain (Γ : Ctxt towerDialect) (t : TowerTy) :
    Chain (Com towerDialect Γ t) (RouteProg (TowerCtx N Γ) (arrTy N)) :=
  .cons (Step.id _) <| .cons (towerStep P N Γ t) <| .cons (Step.id _) <|
    .cons (straightStep _ _) <| .nil _

/-- **The certificate of the tower chain**: one step certificate per step. -/
def towerChainCert (Γ : Ctxt towerDialect) (t : TowerTy) :
    Cert (towerChain P N Γ t) (comSemOf towerDialect Γ t)
      (routeSem (TowerCtx N Γ) (arrTy N)) :=
  .cons (StepCert.id _) <| .cons (towerCert P N Γ t) <| .cons (StepCert.id _) <|
    .cons (straightCert _ _) <| .nil _

/-- The tower chain runs to the wrapped lowering `towerCom P N c` when `towerGoodB P N`
    accepts `c`, and refuses otherwise. -/
theorem towerChain_run {Γ : Ctxt towerDialect} {t : TowerTy} (c : Com towerDialect Γ t) :
    (towerChain P N Γ t).run c =
      if towerGoodB P N c then some (.straight (towerCom P N c)) else none := by
  simp only [towerChain, Chain.run, Step.id, towerStep, Option.bind_some]
  split <;> rfl

/-- **The output coordinates of a program of the tower chain**, from `Cert.sound` of
    `towerChainCert`: for input arrays holding the Montgomery limbs of the coordinates of the
    values of `V`, the output array holds the Montgomery limbs of the coordinates of the value
    of the source program. -/
theorem towerChain_denote {Γ : Ctxt towerDialect} {t : TowerTy} {c : Com towerDialect Γ t}
    {rp : RouteProg (TowerCtx N Γ) (arrTy N)} (hrun : (towerChain P N Γ t).run c = some rp)
    (V : Valuation Γ) (A : Valuation (tArrCtx N Γ)) (o : Fin N → BitVec 64)
    (hA : tArrFlat n A = flatVal (towerLimbEnc P) V) :
    arrCoords n (rp.denote (hvAppend A (.cons o .nil))) (towerMapTys t) 0
      = towerLimbEnc P (c.denote V) := by
  obtain ⟨o', ho', x, hx, y, hy, z, hz, w, hw, hwo⟩ :=
    (towerChainCert P N Γ t).sound (V := V) (W := hvAppend A (.cons o .nil))
      (o := c.denote V) hrun ⟨V, rfl, _, ⟨A, o, rfl, hA⟩, _, rfl, _, rfl, rfl⟩ rfl
  cases ho'
  cases hx
  cases hz
  cases hw
  cases hwo
  exact hy

end Tower

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain
