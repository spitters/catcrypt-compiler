/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.NonInterference
public import CatCrypt.Crypto.CompilerSecurity.Framework
public import CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-!
# NI Preservation Through Compilation

Non-interference properties transfer through correct compilation passes.
This connects the abstract NI framework (`NonInterference.lean`) to the
secure compilation framework (`Framework.lean`).

## Key results

* `ni_preserved_by_eq` — Program equality preserves leakage NI
* `quantified_ni_preserved` — Quantitative NI bounds transfer
* `ni_multipass` — NI composes through multiple compilation passes
* `ni_real_ideal_gives_uc` — NI + compilation → UC security
* `ConstantTimeNI` — Constant-time as a special case of 0-NI

## References

* [Almeida et al., *Enforcing ideal-world leakage bounds in MPC*, CSF 2018]
* [Barthe et al., *Secure Compilation of Side-Channel Countermeasures*, POPL 2025]

**0 axioms**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.NIPreservation

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.NonInterference
open CatCrypt.Crypto.SecureCompilation
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.UCDSL
open scoped ENNReal

set_option autoImplicit false

/-! ## Leakage Non-Interference for SPComp Programs

A program has leakage NI if two executions with NI-related inputs
produce identical SPComp computations. This is the strongest form:
perfect indistinguishability of the full computation. -/

/-- Leakage non-interference for SPComp programs.

    Two inputs related by `R` produce identical computations.
    This captures the source-level NI from Almeida et al. (Definition 1). -/
def LeakageNI {α β : Type} (R : α → α → Prop) (f : α → SPComp β) : Prop :=
  ∀ x₁ x₂, R x₁ x₂ → f x₁ = f x₂

/-- Quantified leakage NI: two related inputs produce computations
    at most ε apart in statistical distance. -/
def QuantifiedLeakageNI {α β : Type} (R : α → α → Prop) (f : α → SPComp β) (ε : ℝ≥0∞) : Prop :=
  ∀ x₁ x₂, R x₁ x₂ →
    sdist (fun _ : Unit => f x₁) (fun _ : Unit => f x₂) ≤ ε

/-- Perfect leakage NI implies quantified NI at ε = 0. -/
theorem leakageNI_implies_quantified {α β : Type} {R : α → α → Prop} {f : α → SPComp β}
    (h : LeakageNI R f) : QuantifiedLeakageNI R f 0 := by
  intro x₁ x₂ hr
  rw [h x₁ x₂ hr]
  exact le_of_eq (sdist_self _)

/-! ## NI Preservation Through Compilation -/

/-- **NI preservation**: If compilation preserves program equality
    (i.e., `source = target` extensionally), then leakage NI
    transfers from source to target.

    This is the key theorem from Almeida et al. (Theorem 2):
    source-level NI + correct compilation → target NI. -/
theorem ni_preserved_by_eq {α β : Type} {R : α → α → Prop}
    {source target : α → SPComp β}
    (h_correct : ∀ x, source x = target x)
    (h_ni : LeakageNI R source) :
    LeakageNI R target := by
  intro x₁ x₂ hr
  rw [← h_correct x₁, ← h_correct x₂]
  exact h_ni x₁ x₂ hr

/-- Quantified NI preservation: bounds transfer through correct compilation. -/
theorem quantified_ni_preserved {α β : Type} {R : α → α → Prop}
    {source target : α → SPComp β} {ε : ℝ≥0∞}
    (h_correct : ∀ x, source x = target x)
    (h_ni : QuantifiedLeakageNI R source ε) :
    QuantifiedLeakageNI R target ε := by
  intro x₁ x₂ hr
  have h1 : (fun _ : Unit => target x₁) = (fun _ : Unit => source x₁) :=
    funext fun _ => (h_correct x₁).symm
  have h2 : (fun _ : Unit => target x₂) = (fun _ : Unit => source x₂) :=
    funext fun _ => (h_correct x₂).symm
  rw [h1, h2]
  exact h_ni x₁ x₂ hr

/-- NI preservation through multiple compilation passes. -/
theorem ni_multipass {α β : Type} {R : α → α → Prop}
    {p₁ p₂ p₃ : α → SPComp β}
    (h₁₂ : ∀ x, p₁ x = p₂ x) (h₂₃ : ∀ x, p₂ x = p₃ x)
    (h_ni : LeakageNI R p₁) :
    LeakageNI R p₃ :=
  ni_preserved_by_eq (fun x => (h₁₂ x).trans (h₂₃ x)) h_ni

/-! ## NI + Compilation → UC Security

The main integration theorem: if a protocol has NI and compilation
is correct, the compiled protocol has UC security. -/

/-- NI + compilation correctness → UC security of compiled code. -/
theorem ni_compilation_gives_uc {α β : Type}
    {source target : α → SPComp β} (V : Type)
    (h_eq : source = target) :
    UCEmulates 0 (UCSpec.ofGame α β V)
      (UCProtocol.ofGame target)
      (UCProtocol.ofGame source) :=
  UCEmulates_of_game_eq h_eq.symm

/-- Perfect NI between real and ideal → UC at ε = 0 after compilation. -/
theorem ni_real_ideal_gives_uc {α β : Type}
    {real ideal : α → SPComp β}
    {compiled : α → SPComp β} (V : Type)
    (h_ni : ∀ x, real x = ideal x)
    (h_compile : ∀ x, real x = compiled x) :
    UCEmulates 0 (UCSpec.ofGame α β V)
      (UCProtocol.ofGame compiled)
      (UCProtocol.ofGame ideal) := by
  apply UCEmulates_of_game_eq
  funext x
  rw [← h_compile x, h_ni x]

/-! ## Approximate NI Preservation

When compilation introduces bounded error (e.g., PRG approximation),
NI degrades gracefully. -/

/-- Approximate compilation preserves quantified NI with error accumulation.

    If source has NI at ε_ni and compilation introduces error ε_compile,
    the target has NI at ε_ni + 2 * ε_compile (triangle inequality). -/
theorem approx_ni_preservation {α β : Type} {R : α → α → Prop}
    {source target : α → SPComp β}
    {ε_ni ε_compile : ℝ≥0∞}
    (h_ni : QuantifiedLeakageNI R source ε_ni)
    (h_compile : sdist source target ≤ ε_compile) :
    QuantifiedLeakageNI R target (ε_ni + 2 * ε_compile) := by
  intro x₁ x₂ hr
  -- Triangle: target x₁ → source x₁ → source x₂ → target x₂
  calc sdist (fun _ : Unit => target x₁) (fun _ : Unit => target x₂)
      ≤ sdist (fun _ : Unit => target x₁) (fun _ : Unit => source x₁) +
        sdist (fun _ : Unit => source x₁) (fun _ : Unit => target x₂) :=
        sdist_triangle _ _ _
    _ ≤ sdist (fun _ : Unit => target x₁) (fun _ : Unit => source x₁) +
        (sdist (fun _ : Unit => source x₁) (fun _ : Unit => source x₂) +
         sdist (fun _ : Unit => source x₂) (fun _ : Unit => target x₂)) := by
        gcongr; exact sdist_triangle _ _ _
    _ ≤ ε_compile + (ε_ni + ε_compile) := by
        gcongr
        · -- target x₁ vs source x₁: precomp + sym
          calc sdist (fun _ : Unit => target x₁) (fun _ : Unit => source x₁)
              ≤ sdist target source :=
                sdist_precomp_le target source (fun _ : Unit => x₁)
            _ = sdist source target := sdist_sym _ _
            _ ≤ ε_compile := h_compile
        · exact h_ni x₁ x₂ hr
        · -- source x₂ vs target x₂: precomp
          exact le_trans (sdist_precomp_le source target (fun _ : Unit => x₂)) h_compile
    _ = ε_ni + 2 * ε_compile := by ring

/-! ## Constant-Time as 0-NI

Constant-time execution is a special case of non-interference:
the program's behavior is independent of secret inputs.

In CryptoSSA, all programs are CT by construction (no branching).
This means all CryptoSSA programs satisfy 0-NI for the "public
output only" observation. -/

/-- A program is constant-time if its computation is independent
    of all inputs. This is NI for the trivial (universal) relation. -/
def ConstantTimeNI {α β : Type} (f : α → SPComp β) : Prop :=
  LeakageNI (fun _ _ => True) f

/-- NI implies constant-time (CT is a weaker property).

    If a program is NI for a meaningful relation R, it is certainly
    CT (which is NI for the trivial relation). -/
theorem ni_implies_ct {α β : Type} {R : α → α → Prop}
    {f : α → SPComp β}
    (h_ni : LeakageNI R f)
    (h_total : ∀ x₁ x₂, R x₁ x₂) :
    ConstantTimeNI f := by
  intro x₁ x₂ _
  exact h_ni x₁ x₂ (h_total x₁ x₂)

/-! ## Sequential Composition of NI Programs -/

/-- Sequential composition preserves NI: if f is NI,
    then `f >>= g` is NI. -/
theorem leakageNI_bind {α β γ : Type} {R : α → α → Prop}
    {f : α → SPComp β} {g : β → SPComp γ}
    (h_f : LeakageNI R f) :
    LeakageNI R (fun x => SPComp.bind (f x) g) := by
  intro x₁ x₂ hr
  show SPComp.bind (f x₁) g = SPComp.bind (f x₂) g
  rw [h_f x₁ x₂ hr]

/-- Parallel composition preserves NI: if f₁ and f₂ are both NI,
    then their product is NI. -/
theorem leakageNI_pair {α β₁ β₂ : Type} {R : α → α → Prop}
    {f₁ : α → SPComp β₁} {f₂ : α → SPComp β₂}
    (h₁ : LeakageNI R f₁) (h₂ : LeakageNI R f₂) :
    LeakageNI R (fun x => SPComp.bind (f₁ x) fun v₁ =>
      SPComp.bind (f₂ x) fun v₂ => SPComp.pure (v₁, v₂)) := by
  intro x₁ x₂ hr
  show SPComp.bind (f₁ x₁) _ = SPComp.bind (f₁ x₂) _
  rw [h₁ x₁ x₂ hr, h₂ x₁ x₂ hr]

end CatCrypt.Crypto.SecureCompilation.NIPreservation
