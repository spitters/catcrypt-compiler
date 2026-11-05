/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.ZXCalculus

@[expose] public section

set_option autoImplicit false

/-!
# ZX Calculus Optimizer

Verified optimization passes for ZX diagrams. Each pass is a structure bundling
a diagram transformation with a correctness proof (the optimized diagram is
equivalent to the original). Passes compose, and the main `optimize` function
chains identity removal, spider fusion, phase cancellation, Hadamard
cancellation, and Pauli simplification.

## Main definitions

* `Pass m n` — a verified optimization pass on ZX diagrams
* `composePass` — sequential composition of two passes
* `removeIdentities` — remove Z(1,1,0) and X(1,1,0) identity spiders
* `fuseSpiders` — merge adjacent same-colour spiders (1,1 specialization)
* `cancelPhases` — cancel opposing phases (alpha + (-alpha) = 0)
* `cancelHadamards` — remove adjacent Hadamard pairs (H . H = I)
* `simplifyPaulis` — simplify X^2 = I and Z^2 = I
* `optimize` — compose all passes into a single optimization

## References

* van de Wetering — *ZX-calculus for the working quantum computer scientist*, 2020
* Kissinger, van de Wetering — *Reducing the number of non-Clifford gates
  in quantum circuits*, Physical Review A, 2020
-/

open scoped Matrix ComplexOrder

namespace CatCrypt.Quantum.ZXCalculus

namespace ZXDiagram

/-! ## Optimization Pass Infrastructure -/

/-- A verified optimization pass: a diagram transformation together with
    a proof that the output is ZX-equivalent to the input. -/
structure Pass (m n : ℕ) where
  /-- The transformation applied to diagrams. -/
  apply : ZXDiagram m n → ZXDiagram m n
  /-- Correctness: the optimized diagram is equivalent to the original. -/
  correct : ∀ d, apply d ≃zx d

/-- The identity pass that does nothing. -/
def idPass (m n : ℕ) : Pass m n where
  apply := id
  correct := fun d => equiv_refl d

/-- Compose two passes sequentially: first apply `p₁`, then `p₂`.
    Correctness follows from transitivity of equivalence. -/
def composePass {m n : ℕ} (p₁ p₂ : Pass m n) : Pass m n where
  apply := p₂.apply ∘ p₁.apply
  correct := fun d =>
    equiv_trans (p₂.correct (p₁.apply d)) (p₁.correct d)

/-! ## Transformation Functions

Note on pattern matching: `ZXDiagram m n` is an indexed inductive type.
Matching on `compose (n := 1) d₁ (.zSpider 1 1 α)` works because it binds
`α : ℝ` as a variable. Matching on a literal `0 : ℝ` inside `compose`
triggers a dependent elimination failure (the kernel cannot solve
`Real.zero = α`), so we match on `α` and use `if α = 0` instead. -/

/-- Remove identity spiders from a single-qubit composition.
    Checks the right component first, then the left. -/
noncomputable def removeId_apply (d : ZXDiagram 1 1) : ZXDiagram 1 1 :=
  match d with
  | .compose (n := 1) d₁ (.zSpider 1 1 α) =>
      if α = 0 then d₁ else .compose d₁ (.zSpider 1 1 α)
  | .compose (n := 1) d₁ (.xSpider 1 1 α) =>
      if α = 0 then d₁ else .compose d₁ (.xSpider 1 1 α)
  | .compose (n := 1) (.zSpider 1 1 α) d₂ =>
      if α = 0 then d₂ else .compose (.zSpider 1 1 α) d₂
  | .compose (n := 1) (.xSpider 1 1 α) d₂ =>
      if α = 0 then d₂ else .compose (.xSpider 1 1 α) d₂
  | d => d

/-- Fuse adjacent same-colour single-qubit spiders. -/
noncomputable def fuse_apply (d : ZXDiagram 1 1) : ZXDiagram 1 1 :=
  match d with
  | .compose (n := 1) (.zSpider 1 1 α) (.zSpider 1 1 β) => .zSpider 1 1 (α + β)
  | .compose (n := 1) (.xSpider 1 1 α) (.xSpider 1 1 β) => .xSpider 1 1 (α + β)
  | d => d

/-- Cancel opposing phases in single-qubit Z-spider compositions. -/
noncomputable def cancelPhase_apply (d : ZXDiagram 1 1) : ZXDiagram 1 1 :=
  match d with
  | .compose (n := 1) (.zSpider 1 1 α) (.zSpider 1 1 β) =>
      if α + β = 0 then .zSpider 1 1 0
      else .compose (.zSpider 1 1 α) (.zSpider 1 1 β)
  | d => d

/-- Cancel Hadamard pairs: H . H = wire. -/
noncomputable def cancelH_apply (d : ZXDiagram 1 1) : ZXDiagram 1 1 :=
  match d with
  | .compose (n := 1)
      (.compose (n := 1) (.zSpider 1 1 a₁)
        (.compose (n := 1) (.xSpider 1 1 b₁) (.zSpider 1 1 c₁)))
      (.compose (n := 1) (.zSpider 1 1 a₂)
        (.compose (n := 1) (.xSpider 1 1 b₂) (.zSpider 1 1 c₂))) =>
        if a₁ = Real.pi / 2 && b₁ = Real.pi / 2 && c₁ = Real.pi / 2 &&
           a₂ = Real.pi / 2 && b₂ = Real.pi / 2 && c₂ = Real.pi / 2
        then .wire
        else .compose
          (.compose (.zSpider 1 1 a₁) (.compose (.xSpider 1 1 b₁) (.zSpider 1 1 c₁)))
          (.compose (.zSpider 1 1 a₂) (.compose (.xSpider 1 1 b₂) (.zSpider 1 1 c₂)))
  | d => d

/-- Simplify Pauli squared: X^2 = I, Z^2 = I. -/
noncomputable def simplifyPauli_apply (d : ZXDiagram 1 1) : ZXDiagram 1 1 :=
  match d with
  | .compose (n := 1) (.xSpider 1 1 α) (.xSpider 1 1 β) =>
      if α = Real.pi && β = Real.pi then .wire
      else .compose (.xSpider 1 1 α) (.xSpider 1 1 β)
  | .compose (n := 1) (.zSpider 1 1 α) (.zSpider 1 1 β) =>
      if α = Real.pi && β = Real.pi then .wire
      else .compose (.zSpider 1 1 α) (.zSpider 1 1 β)
  | d => d

/-! ## Correctness Proofs

The correctness proofs for the passes depend on the ZX rewrite rules
proved in `ZXCalculus.lean` (spider_fusion, z_identity, x_identity,
hadamard_sq, pauliXGate_sq, pauliZGate_sq). The proof structure is:

1. Unfold the transformation function
2. For each pattern match arm, apply the corresponding ZX rewrite rule
3. For unchanged arms, apply `equiv_refl` -/

/-- If d₂ has the same denotation as wire, then compose d₁ d₂ ≡zx d₁. -/
private theorem compose_strictEquiv_wire_right (d₁ : ZXDiagram 1 1) {d₂ : ZXDiagram 1 1}
    (h : d₂ ≡zx .wire) : (.compose d₁ d₂ : ZXDiagram 1 1) ≡zx d₁ := by
  show denote (.compose d₁ d₂) = denote d₁
  simp [denote, strictEquiv] at h
  simp [denote, h]

/-- If d₁ has the same denotation as wire, then compose d₁ d₂ ≡zx d₂. -/
private theorem compose_strictEquiv_wire_left {d₁ : ZXDiagram 1 1} (d₂ : ZXDiagram 1 1)
    (h : d₁ ≡zx .wire) : (.compose d₁ d₂ : ZXDiagram 1 1) ≡zx d₂ := by
  show denote (.compose d₁ d₂) = denote d₂
  simp [denote, strictEquiv] at h
  simp [denote, h]

/-- Identity removal is correct: follows from z_identity and x_identity. -/
theorem removeId_correct (d : ZXDiagram 1 1) :
    removeId_apply d ≃zx d := by
  unfold removeId_apply
  split
  · rename_i d₁ α
    split_ifs with h
    · subst h
      exact strictEquiv_implies_equiv
        (strictEquiv_symm (compose_strictEquiv_wire_right d₁ z_identity))
    · exact equiv_refl _
  · rename_i d₁ α
    split_ifs with h
    · subst h
      exact strictEquiv_implies_equiv
        (strictEquiv_symm (compose_strictEquiv_wire_right d₁ x_identity))
    · exact equiv_refl _
  · rename_i α d₂ _ _
    split_ifs with h
    · subst h
      exact strictEquiv_implies_equiv
        (strictEquiv_symm (compose_strictEquiv_wire_left d₂ z_identity))
    · exact equiv_refl _
  · rename_i α d₂ _ _
    split_ifs with h
    · subst h
      exact strictEquiv_implies_equiv
        (strictEquiv_symm (compose_strictEquiv_wire_left d₂ x_identity))
    · exact equiv_refl _
  · exact equiv_refl _

/-- Spider fusion is correct: follows from spider_fusion and x_spider_fusion. -/
theorem fuse_correct (d : ZXDiagram 1 1) :
    fuse_apply d ≃zx d := by
  unfold fuse_apply
  split
  · rename_i α β
    exact strictEquiv_implies_equiv (strictEquiv_symm (spider_fusion α β 1 1 1 one_pos))
  · rename_i α β
    exact strictEquiv_implies_equiv (strictEquiv_symm (x_spider_fusion α β 1 1 1 one_pos))
  · exact equiv_refl _

/-- Phase cancellation is correct: follows from spider_fusion
    with alpha + beta = 0. -/
theorem cancelPhase_correct (d : ZXDiagram 1 1) :
    cancelPhase_apply d ≃zx d := by
  unfold cancelPhase_apply
  split
  · rename_i α β
    split_ifs with h
    · have hfuse := spider_fusion α β 1 1 1 one_pos
      rw [h] at hfuse
      exact strictEquiv_implies_equiv (strictEquiv_symm hfuse)
    · exact equiv_refl _
  · exact equiv_refl _

/-- Hadamard cancellation is correct: follows from hadamard_sq. -/
theorem cancelH_correct (d : ZXDiagram 1 1) :
    cancelH_apply d ≃zx d := by
  unfold cancelH_apply
  split
  · rename_i a₁ b₁ c₁ a₂ b₂ c₂
    split_ifs with h
    · simp [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
      exact equiv_symm hadamard_sq
    · exact equiv_refl _
  · exact equiv_refl _

/-- Pauli simplification is correct: follows from pauliXGate_sq
    and pauliZGate_sq. -/
theorem simplifyPauli_correct (d : ZXDiagram 1 1) :
    simplifyPauli_apply d ≃zx d := by
  unfold simplifyPauli_apply
  split
  · rename_i α β
    split_ifs with h
    · simp [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact equiv_symm (strictEquiv_implies_equiv pauliXGate_sq)
    · exact equiv_refl _
  · rename_i α β _
    split_ifs with h
    · simp [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact equiv_symm (strictEquiv_implies_equiv pauliZGate_sq)
    · exact equiv_refl _
  · exact equiv_refl _

/-! ## Concrete Optimization Passes -/

/-- **Identity removal**: Remove Z(1,1,0) and X(1,1,0) identity spiders
    from single-qubit compositions. -/
noncomputable def removeIdentities : Pass 1 1 :=
  ⟨removeId_apply, removeId_correct⟩

/-- **Spider fusion** (1-qubit specialization): Merge adjacent same-colour
    spiders by adding phases.

    `Z(1,1,alpha) ⊚ Z(1,1,beta)` --> `Z(1,1,alpha+beta)`
    `X(1,1,alpha) ⊚ X(1,1,beta)` --> `X(1,1,alpha+beta)` -/
noncomputable def fuseSpiders : Pass 1 1 :=
  ⟨fuse_apply, fuse_correct⟩

/-- **Phase cancellation**: Cancel opposing phases for single-qubit Z-spiders.

    `Z(1,1,alpha) ⊚ Z(1,1,beta)` --> `Z(1,1,0)` when `alpha + beta = 0`. -/
noncomputable def cancelPhases : Pass 1 1 :=
  ⟨cancelPhase_apply, cancelPhase_correct⟩

/-- **Hadamard cancellation**: Remove adjacent Hadamard pairs (H . H = I). -/
noncomputable def cancelHadamards : Pass 1 1 :=
  ⟨cancelH_apply, cancelH_correct⟩

/-- **Pauli simplification**: Simplify X^2 = I and Z^2 = I. -/
noncomputable def simplifyPaulis : Pass 1 1 :=
  ⟨simplifyPauli_apply, simplifyPauli_correct⟩

/-! ## Combined Optimizer -/

/-- Compose all single-qubit optimization passes into one:
    identity removal, then spider fusion, then Pauli simplification,
    then phase cancellation, then Hadamard cancellation. -/
noncomputable def allPasses : Pass 1 1 :=
  composePass removeIdentities
    (composePass fuseSpiders
      (composePass simplifyPaulis
        (composePass cancelPhases cancelHadamards)))

/-- Main optimization entry point for single-qubit diagrams.
    Applies all verified optimization passes. -/
noncomputable def optimize (d : ZXDiagram 1 1) : ZXDiagram 1 1 :=
  allPasses.apply d

/-- Main correctness theorem: the optimized diagram is ZX-equivalent
    to the original. -/
theorem optimize_correct (d : ZXDiagram 1 1) : optimize d ≃zx d :=
  allPasses.correct d

/-! ## Spider Count Reduction -/

/-- Identity removal does not increase spider count. -/
theorem removeIdentities_spiderCount_le (d : ZXDiagram 1 1) :
    (removeIdentities.apply d).spiderCount ≤ d.spiderCount := by
  show (removeId_apply d).spiderCount ≤ d.spiderCount
  unfold removeId_apply
  split <;> (try split) <;> simp_all [spiderCount]

/-- Spider fusion does not increase spider count. -/
theorem fuseSpiders_spiderCount_le (d : ZXDiagram 1 1) :
    (fuseSpiders.apply d).spiderCount ≤ d.spiderCount := by
  show (fuse_apply d).spiderCount ≤ d.spiderCount
  unfold fuse_apply
  split <;> simp_all [spiderCount]

/-- Phase cancellation does not increase spider count. -/
private theorem cancelPhases_spiderCount_le (d : ZXDiagram 1 1) :
    (cancelPhases.apply d).spiderCount ≤ d.spiderCount := by
  show (cancelPhase_apply d).spiderCount ≤ d.spiderCount
  unfold cancelPhase_apply
  split <;> (try split) <;> simp_all [spiderCount]

/-- Hadamard cancellation does not increase spider count. -/
private theorem cancelHadamards_spiderCount_le (d : ZXDiagram 1 1) :
    (cancelHadamards.apply d).spiderCount ≤ d.spiderCount := by
  show (cancelH_apply d).spiderCount ≤ d.spiderCount
  unfold cancelH_apply
  split <;> (try split) <;> simp_all [spiderCount]

/-- Pauli simplification does not increase spider count. -/
private theorem simplifyPaulis_spiderCount_le (d : ZXDiagram 1 1) :
    (simplifyPaulis.apply d).spiderCount ≤ d.spiderCount := by
  show (simplifyPauli_apply d).spiderCount ≤ d.spiderCount
  unfold simplifyPauli_apply
  split <;> (try split) <;> simp_all [spiderCount]

/-- The overall optimization does not increase spider count.
    Chains through individual spider-count lemmas for each pass. -/
theorem optimize_spiderCount_le (d : ZXDiagram 1 1) :
    (optimize d).spiderCount ≤ d.spiderCount := by
  unfold optimize allPasses composePass
  simp only [Function.comp]
  exact (cancelHadamards_spiderCount_le _).trans <|
    (cancelPhases_spiderCount_le _).trans <|
      (simplifyPaulis_spiderCount_le _).trans <|
        (fuseSpiders_spiderCount_le _).trans (removeIdentities_spiderCount_le _)

/-! ## Circuit Round-Trip (Placeholder) -/

-- Future integration: Circuit n -> ZXDiagram n n -> optimize -> ZXDiagram n n -> Circuit n
-- Requires CircuitToZX and ZXToCircuit extraction, not yet available.

end ZXDiagram

end CatCrypt.Quantum.ZXCalculus
