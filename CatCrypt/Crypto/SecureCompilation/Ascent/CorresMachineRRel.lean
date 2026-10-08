/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresJRRel
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresGeneric
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscv
public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileTop
public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardsLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.Exit
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsa
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresDescentX86
public import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemFieldLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
public import HaxAscent.Ascent.CorresRRel

@[expose] public section
set_option autoImplicit false

/-!
# The machine correspondences as relational refinements `RRelPT`

Each machine correspondence of `Ascent/` states: from a machine state related by a
state relation `SR` to an abstract state `a` with `P a`, a run of the machine ends
in a state related to `fa a`. This module states every one of them as the relational
refinement `RRelPT` of `CatCryptCore/Refinement/RRel.lean` between the abstract
program `optProg (optGuard P fun a => ((), fa a))` of a guarded update and a predicate
transformer of the machine, in the form of `rrelPT_optProg_wpRel_iff`
(`CatCryptCore/Refinement/Programs.lean`).

* `wpRel T` is the weakest precondition of a step relation `T` with the `Unit` value:
  some `T`-successor satisfies the postcondition. A partial function
  `step : σ → Option σ` has the step relation `step s = some s'`, so its failure `none`
  has weakest precondition `False`; a total function `run` has the relation
  `s' = run s`.
* `wpRelP T` is the weakest liberal precondition: every `T`-successor satisfies the
  postcondition.
* `GuardedRRelPT SR P fa wc` is `RRelPT` at the assertion map `AssnRel.ofStateRel SR`,
  between the guarded update with its exception postcondition fixed to false and the
  machine transformer `wc`.

The judgments with distinct entry and exit relations (`CorresMPost`, `CorresH`) are
`CorresM` over the abstract state space `A ⊕ A` with the relation `entryExitRel`; the
judgments with an exceptional abstract result (`CorresE`, `CorresUE`) are `CorresM`
over the abstract state space `Except ε A`.

`GuardedRRelPT`, the total, partial and deterministic total shapes
(`corresRel_iff_rrelPT`, `corresRelP_iff_rrelPT`, `corresFun_iff_rrelPT`) and
`guardedRRelPT_trans` are in `CatCryptCore/Refinement/Programs.lean`; `corresM_iff_rrelPT`
and `corresM_trans_of_rrelPT` are in `HaxAscent/Calculus/CorresMCore.lean`.

## Main results

* the instances of `corresM_iff_rrelPT`: `corres_semScalar_iff_rrelPT`,
  `corresR_iff_rrelPT`, `corresU_iff_rrelPT`, `corresL_iff_rrelPT`,
  `corresUL_iff_rrelPT`, `corresE_iff_rrelPT`, `corresUE_iff_rrelPT`,
  `corresIsa_iff_rrelPT`, `corresIsaRun_iff_rrelPT`, `corresMPost_iff_rrelPT`,
  `corresH_iff_rrelPT`, `corresA_iff_rrelPT`; `corresWhile_iff_rrelPT` for the partial
  loop judgment.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Refinement
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

open _root_.Hax.Ascent (optGuard)

/-! ## The machine judgments as instances

`GuardedRRelPT`, `corresRel_iff_rrelPT`, `corresRelP_iff_rrelPT` and
`corresFun_iff_rrelPT` are in `CatCryptCore/Refinement/Programs.lean`;
`corresM_iff_rrelPT` and `corresM_trans_of_rrelPT` are in `HaxAscent/Calculus/CorresMCore.lean`. -/

section Instances

variable {AState : Type}

/-- `Corres SR P fa c` over `semScalar` is `GuardedRRelPT` at the step relation of
    `semScalar c`. -/
theorem corres_semScalar_iff_rrelPT (SR : SEnvScalar → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : LowCT) :
    Corres SR P fa c ↔ GuardedRRelPT SR P fa (wpRel fun e (_ : Unit) e' => semScalar c e = some e') :=
  corresM_iff_rrelPT semScalar SR P fa c

/-- `CorresR SR P fa c` over `runRBlock64` is `GuardedRRelPT` at the graph of the run. -/
theorem corresR_iff_rrelPT (SR : RISCVBackend.RState64 → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : List RISCVBackend.RInst64) :
    CorresR SR P fa c ↔
      GuardedRRelPT SR P fa (wpRel fun s (_ : Unit) s' => s' = RISCVBackend.runRBlock64 s c) :=
  corresFun_iff_rrelPT SR P fa _

/-- `CorresU fuel SR P fa c` is `GuardedRRelPT` at the step relation of `semU fuel c`. -/
theorem corresU_iff_rrelPT (fuel : Nat) (SR : SEnvScalar → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : LowCT) :
    CorresU fuel SR P fa c ↔
      GuardedRRelPT SR P fa (wpRel fun e (_ : Unit) e' => semU fuel c e = some e') :=
  corresM_iff_rrelPT (semU fuel) SR P fa c

/-- `CorresL ls SR P fa c` is `GuardedRRelPT` at the step relation of `semScalarL ls c`. -/
theorem corresL_iff_rrelPT (ls : VIR.CatCryptLeafOracle.SemLeafSpec) (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) :
    CorresL ls SR P fa c ↔
      GuardedRRelPT SR P fa (wpRel fun e (_ : Unit) e' => Dialects.LeafOracleScalar.semScalarL ls c e = some e') :=
  corresRel_iff_rrelPT SR P fa _

/-- `CorresUL ls fuel SR P fa c` is `GuardedRRelPT` at the step relation of
    `semUL ls fuel c`. -/
theorem corresUL_iff_rrelPT (ls : VIR.CatCryptLeafOracle.SemLeafSpec) (fuel : Nat)
    (SR : SEnvScalar → AState → Prop) (P : AState → Prop) (fa : AState → AState) (c : LowCT) :
    CorresUL ls fuel SR P fa c ↔
      GuardedRRelPT SR P fa (wpRel fun e (_ : Unit) e' => Dialects.LeafOracleScalar.semUL ls fuel c e = some e') :=
  corresRel_iff_rrelPT SR P fa _

/-- `CorresIsa isa P SR Pre fa fuel` is `GuardedRRelPT` at the step relation of the run
    of `P` under `isa` with `fuel` steps. -/
theorem corresIsa_iff_rrelPT (isa : VIR.LprogIsa.Isa) (P : VIR.JasminLsemMemLoop.LprogM)
    (SR : VIR.JasminLsemMemFlagGuard.LstateMF → AState → Prop) (Pre : AState → Prop)
    (fa : AState → AState) (fuel : Nat) :
    CorresIsa isa P SR Pre fa fuel ↔
      GuardedRRelPT SR Pre fa (wpRel fun m (_ : Unit) m' => isa.lsemFuelMemF P fuel m = some m') :=
  corresM_iff_rrelPT (isa.lsemFuelMemF P) SR Pre fa fuel

/-- `CorresIsaRun isa P SR Pre fa` is `GuardedRRelPT` at the step relation "the run of
    `P` under `isa` halts in `m'` at some fuel". -/
theorem corresIsaRun_iff_rrelPT (isa : VIR.LprogIsa.Isa) (P : VIR.JasminLsemMemLoop.LprogM)
    (SR : VIR.JasminLsemMemFlagGuard.LstateMF → AState → Prop) (Pre : AState → Prop)
    (fa : AState → AState) :
    CorresIsaRun isa P SR Pre fa ↔
      GuardedRRelPT SR Pre fa
        (wpRel fun m (_ : Unit) m' => ∃ fuel, isa.lsemFuelMemF P fuel m = some m') :=
  Iff.trans ⟨fun h m a hs hP => let ⟨n, m', hr, h'⟩ := h m a hs hP; ⟨m', ⟨n, hr⟩, h'⟩,
    fun h m a hs hP => let ⟨m', ⟨n, hr⟩, h'⟩ := h m a hs hP; ⟨n, m', hr, h'⟩⟩
    (corresRel_iff_rrelPT SR Pre fa _)

/-- `Footprint.CorresA SR P fa c` over `runBlockA` is `GuardedRRelPT` at the graph of
    the run. -/
theorem corresA_iff_rrelPT {α : Type} (SR : AddrMem.AState → α → Prop) (P : α → Prop)
    (fa : α → α) (c : List (JInstr 64)) :
    Footprint.CorresA SR P fa c ↔
      GuardedRRelPT SR P fa (wpRel fun s (_ : Unit) s' => s' = AddrMem.runBlockA s c) :=
  corresFun_iff_rrelPT SR P fa _

/-- `CorresWhile SR P fb body` is, for every trip count `k`, `GuardedRRelPT` at the
    abstract iterate `kfold fb k` and the weakest liberal precondition of the `k`-fold
    body run. -/
theorem corresWhile_iff_rrelPT (SR : SEnvScalar → AState → Prop) (P : AState → Prop)
    (fb : AState → AState) (body : LowCT) :
    CorresWhile SR P fb body ↔ ∀ k, GuardedRRelPT SR P (kfold fb k)
      (wpRelP fun e (_ : Unit) e' => semWhileIter (fun e => semScalar body e) k e = some e') :=
  Iff.trans ⟨fun h k s a hs hP s' hr => h s a k s' hs hP hr,
    fun h s a k s' hs hP hr => h k s a hs hP s' hr⟩
    (forall_congr' fun k => corresRelP_iff_rrelPT SR P (kfold fb k) _)

end Instances

/-! ## Entry and exit relations -/

section EntryExit

variable {A : Type}

/-- The precondition on `A ⊕ A` of a judgment with entry and exit relations: `P` at an
    entry state `.inl a`, false at an exit state. -/
def entryPre (P : A → Prop) : A ⊕ A → Prop
  | .inl a => P a
  | .inr _ => False

/-- The abstract step on `A ⊕ A` of a judgment with entry and exit relations: an entry
    state `.inl a` goes to the exit state `.inr (fa a)`. -/
def entryStep (fa : A → A) : A ⊕ A → A ⊕ A
  | .inl a => .inr (fa a)
  | .inr a => .inr a

/-- `CorresMPost step SRin SRout P fa c` is `CorresM` over `A ⊕ A` with the relation
    `entryExitRel SRin SRout`. -/
theorem corresMPost_iff_corresM {M C : Type} (step : C → M → Option M)
    (SRin SRout : M → A → Prop) (P : A → Prop) (fa : A → A) (c : C) :
    CorresMPost step SRin SRout P fa c ↔
      CorresM step (entryExitRel SRin SRout) (entryPre P) (entryStep fa) c := by
  constructor
  · intro h m x hs hP
    cases x with
    | inl a => exact h m a hs hP
    | inr _ => exact hP.elim
  · intro h m a hs hP
    exact h m (.inl a) hs hP

/-- `CorresMPost step SRin SRout P fa c` is `GuardedRRelPT` over `A ⊕ A` at the relation
    `entryExitRel SRin SRout` and the step relation of `step c`. -/
theorem corresMPost_iff_rrelPT {M C : Type} (step : C → M → Option M)
    (SRin SRout : M → A → Prop) (P : A → Prop) (fa : A → A) (c : C) :
    CorresMPost step SRin SRout P fa c ↔
      GuardedRRelPT (entryExitRel SRin SRout) (entryPre P) (entryStep fa)
        (wpRel fun m (_ : Unit) m' => step c m = some m') :=
  (corresMPost_iff_corresM step SRin SRout P fa c).trans (corresM_iff_rrelPT _ _ _ _ _)

/-- `CorresH SRi SRo P fa c` over `semScalar` is `GuardedRRelPT` over `A ⊕ A` at the
    relation `entryExitRel SRi SRo`. -/
theorem corresH_iff_rrelPT (SRi SRo : SEnvScalar → A → Prop) (P : A → Prop) (fa : A → A)
    (c : LowCT) :
    CorresH SRi SRo P fa c ↔
      GuardedRRelPT (entryExitRel SRi SRo) (entryPre P) (entryStep fa)
        (wpRel fun e (_ : Unit) e' => semScalar c e = some e') :=
  corresMPost_iff_rrelPT semScalar SRi SRo P fa c

end EntryExit

/-! ## Exceptional abstract results -/

section Exc

variable {ε A : Type}

/-- The precondition on `Except ε A` of `CorresE`: `P` and the guard `C` at a normal
    state, false at an exception. -/
def exceptPre (P : A → Prop) (C : A → Bool) : Except ε A → Prop
  | .ok a => P a ∧ C a = true
  | .error _ => False

/-- The abstract step on `Except ε A` of `CorresE`: the body `fb` at a normal state,
    the identity at an exception. -/
def exceptStep (fb : A → ExceptT ε Id A) : Except ε A → Except ε A
  | .ok a => (fb a).run
  | .error e => .error e

/-- `CorresE SR P C fb c` is `Corres` over `Except ε A` at `exceptPre P C` and
    `exceptStep fb`. -/
theorem corresE_iff_corres (SR : SEnvScalar → Except ε A → Prop) (P : A → Prop)
    (C : A → Bool) (fb : A → ExceptT ε Id A) (c : LowCT) :
    CorresE SR P C fb c ↔ Corres SR (exceptPre P C) (exceptStep fb) c := by
  constructor
  · intro h env x hs hP
    cases x with
    | ok a => exact h env a hs hP.1 hP.2
    | error _ => exact hP.elim
  · intro h env a hs hP hC
    exact h env (.ok a) hs ⟨hP, hC⟩

/-- `CorresE SR P C fb c` is `GuardedRRelPT` over `Except ε A` at the step relation of
    `semScalar c`. -/
theorem corresE_iff_rrelPT (SR : SEnvScalar → Except ε A → Prop) (P : A → Prop)
    (C : A → Bool) (fb : A → ExceptT ε Id A) (c : LowCT) :
    CorresE SR P C fb c ↔ GuardedRRelPT SR (exceptPre P C) (exceptStep fb)
      (wpRel fun e (_ : Unit) e' => semScalar c e = some e') :=
  (corresE_iff_corres SR P C fb c).trans (corres_semScalar_iff_rrelPT _ _ _ _)

/-- `CorresUE fuel SR P C fb c` is `CorresU fuel` over `Except ε A` at `exceptPre P C`
    and `exceptStep fb`. -/
theorem corresUE_iff_corresU (fuel : Nat) (SR : SEnvScalar → Except ε A → Prop)
    (P : A → Prop) (C : A → Bool) (fb : A → ExceptT ε Id A) (c : LowCT) :
    CorresUE fuel SR P C fb c ↔ CorresU fuel SR (exceptPre P C) (exceptStep fb) c := by
  constructor
  · intro h env x hs hP
    cases x with
    | ok a => exact h env a hs hP.1 hP.2
    | error _ => exact hP.elim
  · intro h env a hs hP hC
    exact h env (.ok a) hs ⟨hP, hC⟩

/-- `CorresUE fuel SR P C fb c` is `GuardedRRelPT` over `Except ε A` at the step
    relation of `semU fuel c`. -/
theorem corresUE_iff_rrelPT (fuel : Nat) (SR : SEnvScalar → Except ε A → Prop)
    (P : A → Prop) (C : A → Bool) (fb : A → ExceptT ε Id A) (c : LowCT) :
    CorresUE fuel SR P C fb c ↔ GuardedRRelPT SR (exceptPre P C) (exceptStep fb)
      (wpRel fun e (_ : Unit) e' => semU fuel c e = some e') :=
  (corresUE_iff_corresU fuel SR P C fb c).trans (corresU_iff_rrelPT _ _ _ _ _)

end Exc

end CatCrypt.Crypto.SecureCompilation.Ascent

end
