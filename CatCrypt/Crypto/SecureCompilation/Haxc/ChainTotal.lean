/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCall

/-!
# Total steps and domain-complete chains

A step `s : Step P Q` is complete on `D : P → Prop` into `E : Q → Prop`
(`Step.CompleteOn s D E`) when every input satisfying `D` runs to an output satisfying `E`.
A chain is complete on `D` into `E` (`Chain.CompleteOn`) in the same sense, and a chain
built by `Chain.cons` from complete steps whose domains meet is complete
(`Chain.completeOn_cons`); a complete chain runs to `some` on its domain
(`Chain.run_isSome`). A step that never refuses is `Step.total n f`, the step `some ∘ f`;
it is complete from `D` into `E` whenever `f` maps `D` into `E` (`Step.completeOn_total`).

The steps `dceStep`, `aegraphStep`, `NFMontify.montifyStep`, `lowerSelectsStep` and
`rangeNFStep` are total steps (`dceStep_eq_total` and its siblings); each is complete on
`True`, and on every predicate the pass maps into itself (`*_preserves_Dom`).

The first step of `extChain`, tuple flattening `flatSameStep`, is complete on the programs
it runs into a domain, into that domain (`flatSameStep_completeOn`). The domains of the
stages of `extChainCore`, the steps of `extChain` after flattening, before the translation
`nfToCatExt` are the Boolean
predicates `extDom0B t` (the input of the check `outTyStep`), `extDom1B t` (the input of
`dceStep`) and `extDom2B t` (the input of the translation), each the result-type check
`outTyB t`; `extPre_completeOn` states that the two first steps of `extChainCore` run every
program in `extDom0B t` to its dead-code-eliminated form, which lies in `extDom2B t`.

## Main definitions

* `Step.total`: the step `some ∘ f` of a function `f`.
* `Step.CompleteOn`, `Chain.CompleteOn`: every input in the domain runs to an output in the
  codomain.
* `Chain.runTotal`: the run of a complete chain as a total function on its domain.
* `extDom0B`, `extDom1B`, `extDom2B`: the domains of the stages of `extChainCore` before the
  translation.

## Main results

* `Chain.completeOn_cons`, `Chain.completeOn_append`: composition of complete steps and chains.
* `Chain.run_isSome`: a complete chain runs to `some` on its domain.
* `Chain.run_eq_some_runTotal`: the partial run is the total run on the domain.
* `dceStep_preserves_Dom` and its siblings: the passes that never refuse are complete on every
  predicate they preserve.
* `flatSameStep_completeOn`: tuple flattening is complete on the programs it runs into a
  domain.
* `extPre_completeOn`, `extPre_run`: the prefix of `extChainCore` is complete on `extDom0B`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-! ## Total steps and completeness -/

/-- The step that never refuses: it runs `f`. -/
def Step.total {P Q : Type} (name : String) (f : P → Q) : Step P Q := ⟨name, some ∘ f⟩

@[simp] theorem Step.total_run {P Q : Type} (name : String) (f : P → Q) (p : P) :
    (Step.total name f).run p = some (f p) := rfl

/-- A step is complete on `D` into `E` when every input in `D` runs to an output in `E`. -/
def Step.CompleteOn {P Q : Type} (s : Step P Q) (D : P → Prop) (E : Q → Prop) : Prop :=
  ∀ p, D p → ∃ q, s.run p = some q ∧ E q

/-- A total step is complete from `D` into `E` when its function maps `D` into `E`. -/
theorem Step.completeOn_total {P Q : Type} (name : String) (f : P → Q) {D : P → Prop}
    {E : Q → Prop} (h : ∀ p, D p → E (f p)) : (Step.total name f).CompleteOn D E :=
  fun p hp => ⟨f p, rfl, h p hp⟩

/-- A step complete on `D` runs every input in `D` to `some`. -/
theorem Step.CompleteOn.run_isSome {P Q : Type} {s : Step P Q} {D : P → Prop} {E : Q → Prop}
    (hs : s.CompleteOn D E) {p : P} (hp : D p) : (s.run p).isSome = true := by
  obtain ⟨q, hq, -⟩ := hs p hp
  simp [hq]

/-- A chain is complete on `D` into `E` when every input in `D` runs to an output in `E`. -/
def Chain.CompleteOn {P Q : Type} (c : Chain P Q) (D : P → Prop) (E : Q → Prop) : Prop :=
  ∀ p, D p → ∃ q, c.run p = some q ∧ E q

/-- The empty chain is complete on `D` into `D`. -/
theorem Chain.completeOn_nil {P : Type} (D : P → Prop) : (Chain.nil P).CompleteOn D D :=
  fun p hp => ⟨p, rfl, hp⟩

/-- A step complete on `D` into `E` followed by a chain complete on `E` into `F` is a chain
    complete on `D` into `F`. -/
theorem Chain.completeOn_cons {P Q R : Type} {s : Step P Q} {c : Chain Q R} {D : P → Prop}
    {E : Q → Prop} {F : R → Prop} (hs : s.CompleteOn D E) (hc : c.CompleteOn E F) :
    (Chain.cons s c).CompleteOn D F := by
  intro p hp
  obtain ⟨q, hq, hE⟩ := hs p hp
  obtain ⟨r, hr, hF⟩ := hc q hE
  exact ⟨r, by simp only [Chain.run, hq, Option.bind_some, hr], hF⟩

/-- Appending a chain complete on `E` into `F` to a chain complete on `D` into `E` gives a
    chain complete on `D` into `F`. -/
theorem Chain.completeOn_append {P Q R : Type} {c : Chain P Q} {d : Chain Q R}
    {D : P → Prop} {E : Q → Prop} {F : R → Prop} (hc : c.CompleteOn D E)
    (hd : d.CompleteOn E F) : (c.append d).CompleteOn D F := by
  intro p hp
  obtain ⟨q, hq, hE⟩ := hc p hp
  obtain ⟨r, hr, hF⟩ := hd q hE
  exact ⟨r, by rw [Chain.run_append, hq, Option.bind_some, hr], hF⟩

/-- **A chain complete on `D` runs every input in `D` to `some`.** -/
theorem Chain.run_isSome {P Q : Type} {c : Chain P Q} {D : P → Prop} {E : Q → Prop}
    (hc : c.CompleteOn D E) {p : P} (hp : D p) : (c.run p).isSome = true := by
  obtain ⟨q, hq, -⟩ := hc p hp
  simp [hq]

/-- The output of a chain complete on `D` at an input in `D`, without the option. -/
def Chain.runTotal {P Q : Type} {c : Chain P Q} {D : P → Prop} {E : Q → Prop}
    (hc : c.CompleteOn D E) (p : {p : P // D p}) : Q :=
  (c.run p.1).get (Chain.run_isSome hc p.2)

theorem Chain.run_eq_some_runTotal {P Q : Type} {c : Chain P Q} {D : P → Prop}
    {E : Q → Prop} (hc : c.CompleteOn D E) (p : {p : P // D p}) :
    c.run p.1 = some (Chain.runTotal hc p) := by
  simp [Chain.runTotal]

end CatCrypt.Crypto.SecureCompilation.VIR.PassChain

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF (rangeNF rangeNFStep)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF)

/-! ## The passes that never refuse -/

section Endo

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

theorem dceStep_eq_total (Γ : Ctxt d) (ts : List d.Ty) :
    dceStep Γ ts = Step.total "dce" (NFProg.dce (Γ := Γ) (ts := ts)) := rfl

theorem dceStep_isSome (Γ : Ctxt d) (ts : List d.Ty) (p : NFProg d Γ ts) :
    ((dceStep Γ ts).run p).isSome = true := rfl

/-- Dead-code elimination is complete on every predicate it preserves. -/
theorem dceStep_preserves_Dom {Γ : Ctxt d} {ts : List d.Ty} (D : NFProg d Γ ts → Prop)
    (h : ∀ p, D p → D (NFProg.dce p)) : (dceStep Γ ts).CompleteOn D D :=
  fun p hp => ⟨_, rfl, h p hp⟩

theorem lowerSelectsStep_eq_total [DialectDenoteM d Option] [HasSelect d] (Γ : Ctxt d)
    (ts : List d.Ty) :
    lowerSelectsStep Γ ts =
      Step.total "lowerSelects" (NFProg.lowerSelects (Γ := Γ) (ts := ts)) := rfl

theorem lowerSelectsStep_isSome [DialectDenoteM d Option] [HasSelect d] (Γ : Ctxt d)
    (ts : List d.Ty) (p : NFProg d Γ ts) : ((lowerSelectsStep Γ ts).run p).isSome = true :=
  rfl

/-- The select lowering is complete on every predicate it preserves. -/
theorem lowerSelectsStep_preserves_Dom [DialectDenoteM d Option] [HasSelect d] {Γ : Ctxt d}
    {ts : List d.Ty} (D : NFProg d Γ ts → Prop) (h : ∀ p, D p → D (NFProg.lowerSelects p)) :
    (lowerSelectsStep Γ ts).CompleteOn D D :=
  fun p hp => ⟨_, rfl, h p hp⟩

variable [DecidableEq d.Ty] [DialectDenote d] [DecidableEq d.Op]

theorem aegraphStep_eq_total (R : Optimizer.Rewrite.AegraphGeneric.RuleSet d) (Γ : Ctxt d)
    (ts : List d.Ty) :
    aegraphStep R Γ ts = Step.total "aegraph" (aegraphOptNF R (Γ := Γ) (ts := ts)) := rfl

theorem aegraphStep_isSome (R : Optimizer.Rewrite.AegraphGeneric.RuleSet d) (Γ : Ctxt d)
    (ts : List d.Ty) (p : NFProg d Γ ts) : ((aegraphStep R Γ ts).run p).isSome = true := rfl

/-- The e-graph pass is complete on every predicate it preserves. -/
theorem aegraphStep_preserves_Dom (R : Optimizer.Rewrite.AegraphGeneric.RuleSet d) {Γ : Ctxt d}
    {ts : List d.Ty} (D : NFProg d Γ ts → Prop) (h : ∀ p, D p → D (aegraphOptNF R p)) :
    (aegraphStep R Γ ts).CompleteOn D D :=
  fun p hp => ⟨_, rfl, h p hp⟩

end Endo

theorem montifyStep_eq_total (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    NFMontify.montifyStep Γ ts =
      Step.total "montify" (NFMontify.montifyPass (Γ := Γ) (ts := ts)) := rfl

theorem montifyStep_isSome (Γ : Ctxt jasminDialect) (ts : List JasminTy)
    (p : NFProg jasminDialect Γ ts) : ((NFMontify.montifyStep Γ ts).run p).isSome = true := rfl

/-- The montify pass is complete on every predicate it preserves. -/
theorem montifyStep_preserves_Dom {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (D : NFProg jasminDialect Γ ts → Prop) (h : ∀ p, D p → D (NFMontify.montifyPass p)) :
    (NFMontify.montifyStep Γ ts).CompleteOn D D :=
  fun p hp => ⟨_, rfl, h p hp⟩

theorem rangeNFStep_eq_total (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    rangeNFStep Γ ts = Step.total "range" (rangeNF (Γ := Γ) (ts := ts)) := rfl

theorem rangeNFStep_isSome (Γ : Ctxt jasminDialect) (ts : List JasminTy) (p : NFProg jasminDialect Γ ts) :
    ((rangeNFStep Γ ts).run p).isSome = true := rfl

/-- The range stage is complete on every predicate it preserves. -/
theorem rangeNFStep_preserves_Dom {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (D : NFProg jasminDialect Γ ts → Prop) (h : ∀ p, D p → D (rangeNF p)) :
    (rangeNFStep Γ ts).CompleteOn D D :=
  fun p hp => ⟨_, rfl, h p hp⟩

/-! ## The domains of `extChain` before the translation -/

/-- **Tuple flattening is complete on the programs it runs into `E`, into `E`.** -/
theorem flatSameStep_completeOn (Γ : Ctxt nfDialect) (ts : List NfTy)
    (E : NFProg nfDialect Γ ts → Prop) :
    (flatSameStep Γ ts).CompleteOn (fun p => ∃ q, (flatSameStep Γ ts).run p = some q ∧ E q) E :=
  fun _ hp => hp

/-- The domain of the input of `extChainCore`, the input of the check `outTyStep`. -/
def extDom0B {Γ : Ctxt nfDialect} (t : NfTy) (_p : NFProg nfDialect Γ [t]) : Bool := outTyB t

/-- The domain of the input of `dceStep` in `extChainCore`. -/
def extDom1B {Γ : Ctxt nfDialect} (t : NfTy) (_p : NFProg nfDialect Γ [t]) : Bool := outTyB t

/-- The domain of the input of the translation `extCallStep` in `extChainCore`. -/
def extDom2B {Γ : Ctxt nfDialect} (t : NfTy) (_p : NFProg nfDialect Γ [t]) : Bool := outTyB t

theorem extDom0B_iff {Γ : Ctxt nfDialect} (t : NfTy) (p : NFProg nfDialect Γ [t]) :
    extDom0B t p = true ↔ outTyB t = true := Iff.rfl

theorem extDom1B_iff {Γ : Ctxt nfDialect} (t : NfTy) (p : NFProg nfDialect Γ [t]) :
    extDom1B t p = true ↔ outTyB t = true := Iff.rfl

theorem extDom2B_iff {Γ : Ctxt nfDialect} (t : NfTy) (p : NFProg nfDialect Γ [t]) :
    extDom2B t p = true ↔ outTyB t = true := Iff.rfl

/-- The check of the result type is complete on its domain and keeps the program. -/
theorem outTyStep_completeOn (Γ : Ctxt nfDialect) (t : NfTy) :
    (outTyStep Γ t).CompleteOn (fun p => extDom0B t p = true)
      (fun q => extDom1B t q = true) := by
  intro p hp
  refine ⟨p, ?_, hp⟩
  simp only [outTyStep, show outTyB t = true from hp, ite_true]

/-- Dead-code elimination keeps the domain before the translation. -/
theorem dceStep_preserves_extDom (Γ : Ctxt nfDialect) (t : NfTy) :
    (dceStep Γ [t]).CompleteOn (fun p => extDom1B t p = true)
      (fun q => extDom2B t q = true) :=
  fun _ hp => ⟨_, rfl, hp⟩

/-- **The two steps of `extChainCore` before the translation run every program in `extDom0B t`
    to its dead-code-eliminated form, which lies in `extDom2B t`.** -/
theorem extPre_completeOn (Γ : Ctxt nfDialect) (t : NfTy) :
    (Chain.cons (outTyStep Γ t) (.cons (dceStep Γ [t]) (.nil _))).CompleteOn
      (fun p => extDom0B t p = true) (fun q => extDom2B t q = true) :=
  Chain.completeOn_cons (outTyStep_completeOn Γ t)
    (Chain.completeOn_cons (dceStep_preserves_extDom Γ t) (Chain.completeOn_nil _))

theorem extPre_run {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t])
    (hp : extDom0B t p = true) :
    (Chain.cons (outTyStep Γ t) (.cons (dceStep Γ [t]) (.nil _))).run p =
      some (NFProg.dce p) := by
  simp only [Chain.run, outTyStep, show outTyB t = true from hp, ite_true, Option.bind_some,
    dceStep]

end CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal
