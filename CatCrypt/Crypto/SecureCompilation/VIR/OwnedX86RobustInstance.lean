/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
public import CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo

/-!
# The owned x86 backend as a proved `JasminIRToX86` instance

The capstone `RobustCompilationPipeline.robustCompilation_source_to_x86` consumes
a `JasminVerifiedCompiler` record whose value-refinement field abstracts jasmin's
external Coq compiler `compile_prog_to_asmP`. This file instantiates the minimal
`JasminIRToX86` residual with CatCrypt's **own** verified x86 backend
(`ScalarLinX86Demo.x86Target` / `comToRegProg` / `regToX86`), so that — on the
fragment the owned backend covers — the jasmin-IR → x86 value edge is a *proved*
fact rather than a carried hypothesis.

## The observable and the record fields

* `ownedX86Obs := BitVec 64` — the value in the result register.
* `ownedObsOf` decodes a jasmin-IR meaning to that observable (identity on
  `reg 64`, `0` on the other type slots the owned scalar backend does not target).
* `ownedX86Behaviour leafSem com V := ownedObsOf (runProg leafSem com V)` — the
  x86 observable read off the owned jasmin-IR evaluator meaning. The record field
  `semRefine` then holds by definition.

## Where the owned machine content lives

`ownedX86_machine_realizes` is the substantive theorem: on the owned scalar
`reg 64` fragment (`ComOK`, `AllReg64`, shift amounts in range), the **actual x86
machine run** of the owned-emitted block equals `ownedX86Behaviour`. Its proof is
exactly the `com_x86_e2e` composition (`regToX86_denote ∘ comToReg_faithful`)
bridged to the evaluator by `lowerComToProg_sem_eq` (`runProg = Com.denote`). This
is what distinguishes the owned route from a carried external edge: the machine
that realizes the record's behaviour is exhibited and proved, not assumed.

## Scope boundary (constant-time and the capstone)

* `ownedX86CTSafe` is `True`: the `x86Target` ISA subset (`X86Backend.Model`) has
  no memory operands and no branches, so every emitted block is constant-time by
  construction. The owned *leakage-trace* constant-time theorem
  (`X86Backend.CorrectAndRobust.ownedCompile_secure_and_CT`, `blockLeak`) is stated
  over a different x86 machine (`X86Backend.Jasmin`, `JInstr`/`runBlock`) and a
  different source (`List ArithSrc`), so it does not plug into this `Com jasminDialect`
  value route; the `True` predicate records the by-construction fact for the
  `x86Target` model.
* The capstone quantifies over `lowerLatticeToJasmin c`, whose binders are all
  `extCall` (opaque leaves) — the owned scalar backend compiles `regArith`/`mulhi`/
  shift/const, never `extCall`. So the owned machine-realization fragment is
  disjoint from the capstone's programs: `ownedRobustCompilation_source_to_x86`
  below discharges the capstone's `jvc` hypothesis with this owned instance, but on
  the capstone's `extCall` programs the discharged `semRefine` is the definitional
  decode, not the owned machine — the machine's teeth are on the scalar fragment
  (`ownedX86_machine_realizes`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.OwnedX86RobustInstance

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
open CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo

/-! ## 1. The observable and its decode -/

/-- The owned x86 observable: the 64-bit value in the result register. -/
abbrev ownedX86Obs : Type := BitVec 64

/-- Decode a jasmin-IR meaning `⟦t⟧` to the owned x86 observable: identity on the
    `reg 64` result the owned scalar backend targets, `0` on the other type slots
    (which the owned backend never returns). -/
def ownedObsOf : {t : JasminTy} → ⟦t⟧ → ownedX86Obs
  | .reg 64, v => v
  | _, _ => 0

/-- On a `reg 64` meaning, the decode is the identity. -/
@[simp] theorem ownedObsOf_reg64 (v : BitVec 64) : ownedObsOf (t := .reg 64) v = v := rfl

/-! ## 2. The record's behaviour and CT fields -/

/-- The owned x86 behaviour: decode the owned jasmin-IR evaluator meaning
    (`runProg`) to the observable. This is exactly the record's value-refinement
    shape, so `semRefine` is definitional. -/
def ownedX86Behaviour (leafSem : LeafSem) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) : ownedX86Obs :=
  ownedObsOf (runProg leafSem com V)

/-- The owned x86 CT predicate. The `x86Target` model (`X86Backend.Model`) has no
    memory operands and no branches, so every emitted scalar block is constant-time
    by construction; the predicate records this as `True`. -/
def ownedX86CTSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (_com : Com jasminDialect Γ t) : Prop := True

/-! ## 3. The owned machine realizes the behaviour on the scalar fragment

`ComOK` implies `StraightLine`, so `lowerComToProg_sem_eq` gives `runProg = denote`
on the fragment; `com_x86_e2e` gives the owned x86 machine run `= denote`. Together:
the owned x86 machine computes `ownedX86Behaviour`. -/

/-- Every supported straight-line `Com` is `StraightLine` (no binder is the
    aliasing `stackStore`): each `ComOK` binder op is `SupportedOp`, none of whose
    shapes is `stackStore`. -/
theorem comOK_straightLine {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (.reg 64)} (h : ComOK com) : StraightLine com := by
  induction h with
  | ret v => trivial
  | @var Γ e body hsupp hbody ih =>
      refine ⟨?_, ih⟩
      intro w n hop
      rcases hsupp with ⟨bop, he, _⟩ | he | ⟨k, he | he⟩ | ⟨k, he⟩ <;>
        · rw [he] at hop; exact JasminOp.noConfusion hop

/-- The owned x86 machine observable: run the owned-emitted block from the initial
    state seeded by `V`, read the result register. Total over every `Com`
    (`comToRegProg` emits nothing for ops it does not cover). -/
def ownedX86MachineObs {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) : ownedX86Obs :=
  ((x86Target.runOps ⟨envOf Γ.length V, {}⟩
      (x86Target.compile (comToRegProg com Γ.length))).regs) (comRetName com Γ.length)

/-- **The owned x86 machine realizes the record's behaviour, on the scalar
    `reg 64` fragment.** For a supported straight-line `Com` over an all-`reg 64`
    context whose emitted shift amounts are in range, the actual x86 machine run of
    the owned-emitted block equals `ownedX86Behaviour`. The proof is the
    `com_x86_e2e` composition (`regToX86_denote ∘ comToReg_faithful`) bridged to the
    evaluator by `lowerComToProg_sem_eq`. This exhibits the jasmin-IR → x86 value
    edge for the owned route as a proved fact. -/
theorem ownedX86_machine_realizes {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ)
    (hPinj : ∀ (t t' : jasminDialect.Ty) (v : Ctxt.Var Γ t)
                (v' : Ctxt.Var Γ t'), (paramsAndMap Γ).2 t v = (paramsAndMap Γ).2 t' v' →
                (∃ h : t = t', h ▸ v = v'))
    (hsh : ∀ stmt ∈ comToRegProg com Γ.length, ShiftAmtOK stmt)
    (V : Ctxt.Valuation Γ) :
    ownedX86MachineObs com V = ownedX86Behaviour leafSem com V := by
  have hmach : ownedX86MachineObs com V = Com.denote com V :=
    com_x86_e2e hok hΓ V ⟨envOf Γ.length V, {}⟩ rfl hsh
  have heval : runProg leafSem com V = Com.denote com V :=
    lowerComToProg_sem_eq hLeaf hInj com (comOK_straightLine hok) hPinj V
  rw [hmach, ownedX86Behaviour, heval, ownedObsOf_reg64]

/-! ## 4. The proved `JasminIRToX86` instance -/

/-- **The owned x86 backend as a proved `JasminIRToX86` residual.** `semRefine` holds
    by definition (`ownedX86Behaviour` is the decode of the evaluator meaning);
    `ctPreserve` is discharged by the by-construction constant-time of the
    `x86Target` ISA subset. Unlike the carried jasmin edge, the value refinement is
    grounded by `ownedX86_machine_realizes`: the owned x86 machine computes this
    behaviour on the scalar `reg 64` fragment. -/
def ownedJasminIRToX86 (leafSem : LeafSem) :
    JasminIRToX86 leafSem ownedX86Obs (ownedX86Behaviour leafSem) ownedX86CTSafe where
  obsOf := ownedObsOf
  semRefine := fun _ _ => rfl
  ctPreserve := fun _ _ => trivial

/-- The legacy `JasminVerifiedCompiler` record, built from the owned residual for
    free (`ofIRToX86` derives the redundant `psemFaithful` field). -/
def ownedJasminVerifiedCompiler (leafSem : LeafSem) :
    JasminVerifiedCompiler leafSem ownedX86Obs (ownedX86Behaviour leafSem) ownedX86CTSafe :=
  JasminVerifiedCompiler.ofIRToX86 (ownedJasminIRToX86 leafSem)

/-! ## 5. Capstone application: `jvc` discharged for the owned route

The capstone `robustCompilation_source_to_x86` is applied with the owned instance,
so the `jvc` hypothesis is discharged rather than a free parameter. The conclusion holds; its
value conjunct on the capstone's `extCall` programs is the definitional decode
(`ownedX86Behaviour`), not the owned machine — the owned machine's guarantee is on
the disjoint scalar fragment (`ownedX86_machine_realizes`). -/

/-- **Robust compilation source → x86 with the owned `JasminVerifiedCompiler`
    discharged.** Specialization of `robustCompilation_source_to_x86` to the owned
    instance: for every source lattice program, the owned x86 observable of the
    emitted-and-compiled program is the decode of the transported source
    denotation, and it is x86-CT-safe. The compiler-edge hypothesis is constructed,
    not assumed. -/
theorem ownedRobustCompilation_source_to_x86
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (c : Com latticeDialect Γ t)
    (hPinj : ∀ (s s' : jasminDialect.Ty)
                (v : Ctxt.Var (Γ.map tau) s)
                (v' : Ctxt.Var (Γ.map tau) s'),
                (paramsAndMap (Γ.map tau)).2 s v
                  = (paramsAndMap (Γ.map tau)).2 s' v' →
                (∃ h : s = s', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    ownedX86Behaviour leafSem (lowerLatticeToJasmin c) (mapVal V)
        = ownedObsOf (transTy (c.denote V))
      ∧ ownedX86CTSafe (lowerLatticeToJasmin c) :=
  robustCompilation_source_to_x86 hLeaf hInj (ownedJasminVerifiedCompiler leafSem) c hPinj V

end CatCrypt.Crypto.SecureCompilation.VIR.OwnedX86RobustInstance
