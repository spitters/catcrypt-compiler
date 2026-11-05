/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.GateBall
public import CatCrypt.Quantum.Synthesis.KAKPassSmall

/-!
# Approximate correctness of the resynthesis passes, with a verified distance checker

The exact theorems `KAKPassSmall.listMatrix_kakEmit` and `ZYZPass.listMatrix_zyzEmit` assume
that each replaced block's template has exactly the block's matrix up to a phase
(`FitSound`, `ZFitSound`). Fitted angles are rounded, so that holds only approximately. This
module replaces the hypothesis by a checked bound in the `ℓ²` operator norm.

Errors of unitary factors add up (`norm_mul_sub_smul_le`): for unitary `A₁` and `B₂` and
`|c₂| = 1`, `‖A₁ A₂ - c₁ c₂ B₁ B₂‖ ≤ ‖A₁ - c₁ B₁‖ + ‖A₂ - c₂ B₂‖`. Over a concatenation of
segments the phases add and the bounds add (`norm_listMatrix_flatMap_sub_le`).

A fit is *checked* (`KFitChecked`, `ZFitChecked`) when, for every replaced block, the payload
carries a phase `φ` and a bound `ε` such that the checker of `GateBall` returns at most `ε` on
the block, its template and `φ`. Under that hypothesis the gates emitted by the pass are
within the sum of the `ε` of the input, up to the phase `Φ = Σ φ`. The wrappers
`checkedFit` and `checkedZFit` turn any fit into a checked one: they keep a proposal only when
the checker accepts it with a bound below a threshold, and record phase and bound in the
payload; the passes themselves are unchanged.

## Main definitions

* `KFitChecked`, `ZFitChecked` — the per-block hypothesis, decided by the checkers.
* `checkedFit`, `checkedZFit` — the fit wrappers that run the checker on each proposal.

## Main results

* `norm_mul_sub_smul_le` — the approximate composition of unitary factors.
* `norm_listMatrix_flatMap_sub_le` — the approximate composition over a concatenation.
* `listMatrix_kakEmit_approx`, `listMatrix_zyzEmit_approx` — the approximate pass theorems
  under the checked hypothesis.
* `listMatrix_kakEmit_checkedFit`, `listMatrix_zyzEmit_checkedZFit` — the same for the
  wrapped fits, with no hypothesis.
-/

@[expose] public section

set_option autoImplicit false

open Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Synthesis.KAK CatCrypt.Quantum.Synthesis.KAKPass
open CatCrypt.Quantum.Synthesis.KAKPassSmall CatCrypt.Quantum.Synthesis.ZYZPass
open CatCrypt.Quantum.QFT (listMatrix listMatrix_append)
open scoped Matrix.Norms.L2Operator

namespace CatCrypt.Quantum.Synthesis.IntervalArith

variable {n : ℕ}

/-! ## Composition of approximations -/

/-- **Approximate composition.** For unitary `A₁`, `B₂` and `‖c₂‖ = 1`, the error of a product
is at most the sum of the errors of the factors. -/
theorem norm_mul_sub_smul_le {m : Type*} [Fintype m] [DecidableEq m]
    {A₁ A₂ B₁ B₂ : Matrix m m ℂ} (hA₁ : A₁ ∈ Matrix.unitaryGroup m ℂ)
    (hB₂ : B₂ ∈ Matrix.unitaryGroup m ℂ) (c₁ c₂ : ℂ) (hc₂ : ‖c₂‖ = 1) :
    ‖A₁ * A₂ - (c₁ * c₂) • (B₁ * B₂)‖ ≤ ‖A₁ - c₁ • B₁‖ + ‖A₂ - c₂ • B₂‖ := by
  have h : A₁ * A₂ - (c₁ * c₂) • (B₁ * B₂) =
      A₁ * (A₂ - c₂ • B₂) + (A₁ - c₁ • B₁) * (c₂ • B₂) := by
    rw [mul_comm c₁ c₂, ← smul_smul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [CStarRing.norm_mem_unitary_mul _ hA₁, Matrix.mul_smul, norm_smul, hc₂, one_mul,
    CStarRing.norm_mul_mem_unitary _ hB₂, add_comm]

/-- The matrix of a gate list is unitary. -/
theorem listMatrix_mem_unitaryGroup (l : List (Gate n)) :
    listMatrix l ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  (Optimization.RoutingPerm.circuitUnitary (Circuit.ofList l)).2

/-- A gate list is within `0` of itself at the phase `0`. -/
theorem norm_listMatrix_sub_self_le (l : List (Gate n)) :
    ‖listMatrix l - exp (I * ((0 : ℝ) : ℂ)) • listMatrix l‖ ≤ 0 := by
  simp

/-- **Approximate composition over a concatenation.** If each segment `F x` is within `ε x`
of `G x` up to the phase `φ x`, the concatenation of the `F x` is within `Σ ε x` of the
concatenation of the `G x` up to the phase `Σ φ x`. -/
theorem norm_listMatrix_flatMap_sub_le {α : Type*} (L : List α) (F G : α → List (Gate n))
    (φ ε : α → ℝ)
    (h : ∀ x ∈ L, ‖listMatrix (F x) - exp (I * (φ x : ℂ)) • listMatrix (G x)‖ ≤ ε x) :
    ‖listMatrix (L.flatMap F) - exp (I * (((L.map φ).sum : ℝ) : ℂ)) •
      listMatrix (L.flatMap G)‖ ≤ (L.map ε).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [List.flatMap_cons, List.flatMap_cons, listMatrix_append, listMatrix_append,
      List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    have he : exp (I * (((φ x + (L.map φ).sum : ℝ)) : ℂ)) =
        exp (I * (((L.map φ).sum : ℝ) : ℂ)) * exp (I * (φ x : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [he]
    refine (norm_mul_sub_smul_le (listMatrix_mem_unitaryGroup _) (listMatrix_mem_unitaryGroup _)
      _ _ (Complex.norm_exp_I_mul_ofReal _)).trans ?_
    linarith

/-! ## The KAK pass -/

variable {β : Type}

/-- The checked hypothesis of the KAK pass, for payload readings `ph` (phase) and `ep`
(bound): on every block of `l` where `fit` proposes a template with fewer CNOTs, the checker
`checkPair` bounds the distance of the block from its template at the phase `ph b` by at
most `ep b`. -/
def KFitChecked (fit : BlockFit n β) (ph : β → PiLin) (ep : β → ℚ) (l : List (Gate n)) :
    Prop :=
  ∀ i j gs k θ b, Block.pair i j gs ∈ collectBlocks l → fit i j gs = some (k, θ, b) →
    k.val < cnotCount gs → ∃ e, checkPair i j gs (tmplGatesQ k i j θ) (ph b) = some e ∧ e ≤ ep b

/-- **Approximate correctness of the exact KAK pass.** Under `KFitChecked fit ph ep l`, the
gates of `kakEmit fit l` are within `Σ ep b` of `l` in the `ℓ²` operator norm, up to the
global phase `Σ ph b`, both sums over the payloads `b` of the replaced blocks. -/
theorem listMatrix_kakEmit_approx (fit : BlockFit n β) (ph : β → PiLin) (ep : β → ℚ)
    (l : List (Gate n)) (hfit : KFitChecked fit ph ep l) :
    ‖listMatrix (kakEmit fit l).1 -
        exp (I * ((((kakEmit fit l).2.map fun b => PiLin.toReal (ph b)).sum : ℝ) : ℂ)) •
          listMatrix l‖ ≤ ((kakEmit fit l).2.map fun b => (ep b : ℝ)).sum := by
  have h2 : (kakEmit fit l).2 = (collectBlocks l).flatMap fun b => (blockEmit fit b).2 := by
    simp [kakEmit, List.flatMap_map]
  have hsum : ∀ {γ δ : Type} (L : List γ) (P : γ → List δ) (f : δ → ℝ),
      ((L.flatMap P).map f).sum = (L.map fun x => ((P x).map f).sum).sum := fun L P f => by
    rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]; rfl
  rw [← listMatrix_collectBlocks l, kakEmit_fst, h2, hsum, hsum]
  refine norm_listMatrix_flatMap_sub_le _ _ _ _ _ fun b hb => ?_
  cases b with
  | gate g => simp [blockEmit, Block.gates]
  | pair i j gs =>
    rcases h : fit i j gs with _ | ⟨k, θ, p⟩
    · simp [blockEmit, h, Block.gates]
    · by_cases hk : k.val < cnotCount gs
      · simp only [blockEmit, h, hk, ite_true, Block.gates, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
        obtain ⟨e, he, hle⟩ := hfit i j gs k θ p hb h hk
        exact (norm_sub_le_checkPair he).trans (by exact_mod_cast hle)
      · simp [blockEmit, h, hk, Block.gates]

/-- The KAK fit wrapped by the checker: a proposal `(k, θ, b)` of `fit` on a block `gs` is
kept when `checkPair` on `gs`, the template `tmplGatesQ k i j θ` and the phase `phase b`
returns a bound `e ≤ bound`, with the payload `(b, phase b, e)`; otherwise the block is
kept. -/
def checkedFit (fit : BlockFit n β) (phase : β → PiLin) (bound : ℚ) :
    BlockFit n (β × PiLin × ℚ) := fun i j gs =>
  match fit i j gs with
  | some (k, θ, b) =>
    match checkPair i j gs (tmplGatesQ k i j θ) (phase b) with
    | some e => if e ≤ bound then some (k, θ, (b, phase b, e)) else none
    | none => none
  | none => none

/-- The wrapped KAK fit satisfies the checked hypothesis with the recorded phases and
bounds. -/
theorem kFitChecked_checkedFit (fit : BlockFit n β) (phase : β → PiLin) (bound : ℚ)
    (l : List (Gate n)) :
    KFitChecked (checkedFit fit phase bound) (fun b => b.2.1) (fun b => b.2.2) l := by
  intro i j gs k θ b _ hf _
  simp only [checkedFit] at hf
  split at hf
  · next k' θ' b' _ =>
    split at hf
    · next e he =>
      split at hf
      · simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        exact ⟨e, he, le_rfl⟩
      · exact absurd hf (by simp)
    · exact absurd hf (by simp)
  · exact absurd hf (by simp)

/-- **The checked KAK pass.** For every fit, the gates of `kakEmit (checkedFit fit phase bound)
l` are within the sum of the recorded bounds of `l`, up to the sum of the recorded phases. -/
theorem listMatrix_kakEmit_checkedFit (fit : BlockFit n β) (phase : β → PiLin) (bound : ℚ)
    (l : List (Gate n)) :
    ‖listMatrix (kakEmit (checkedFit fit phase bound) l).1 -
        exp (I * ((((kakEmit (checkedFit fit phase bound) l).2.map
          fun b => PiLin.toReal b.2.1).sum : ℝ) : ℂ)) • listMatrix l‖ ≤
      ((kakEmit (checkedFit fit phase bound) l).2.map fun b => (b.2.2 : ℝ)).sum :=
  listMatrix_kakEmit_approx _ _ _ l (kFitChecked_checkedFit fit phase bound l)

/-! ## The ZYZ pass -/

/-- The checked hypothesis of the run pass: on every run `gs` on `q` at position `i` of
`collectRuns l` where `fit` proposes an axis `a` and angles `θ`, the checker `checkRun` bounds
the distance of the run from its template `runTemplate a q θ` at the phase `ph b` by at
most `ep b`. -/
def ZFitChecked (fit : ZFit n β) (ph : β → PiLin) (ep : β → ℚ) (l : List (Gate n)) : Prop :=
  ∀ i q gs a θ b, (collectRuns l)[i]? = some (Seg.run q gs) → fit i q gs = some (a, θ, b) →
    ∃ e, checkRun q gs (runTemplate a q θ) (ph b) = some e ∧ e ≤ ep b

/-- **Approximate correctness of the ZYZ pass.** Under `ZFitChecked fit ph ep l`, the gates of
`zyzEmit fit l` are within `Σ ep b` of `l` in the `ℓ²` operator norm, up to the global phase
`Σ ph b`, both sums over the payloads `b` of the replaced runs. -/
theorem listMatrix_zyzEmit_approx (fit : ZFit n β) (ph : β → PiLin) (ep : β → ℚ)
    (l : List (Gate n)) (hfit : ZFitChecked fit ph ep l) :
    ‖listMatrix (zyzEmit fit l).1 -
        exp (I * ((((zyzEmit fit l).2.map fun b => PiLin.toReal (ph b)).sum : ℝ) : ℂ)) •
          listMatrix l‖ ≤ ((zyzEmit fit l).2.map fun b => (ep b : ℝ)).sum := by
  have h2 : (zyzEmit fit l).2 =
      (collectRuns l).zipIdx.flatMap fun si => (segEmit fit si.2 si.1).2 := by
    simp [zyzEmit, List.flatMap_map]
  have h0 : (collectRuns l).zipIdx.flatMap (fun si => Seg.gates si.1) =
      (collectRuns l).flatMap Seg.gates := by
    rw [← List.flatMap_map (f := Prod.fst) (g := Seg.gates), List.zipIdx_map_fst]
  have hsum : ∀ {γ δ : Type} (L : List γ) (P : γ → List δ) (f : δ → ℝ),
      ((L.flatMap P).map f).sum = (L.map fun x => ((P x).map f).sum).sum := fun L P f => by
    rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]; rfl
  rw [← listMatrix_collectRuns l, ← h0, zyzEmit_fst, h2, hsum, hsum]
  refine norm_listMatrix_flatMap_sub_le _ _ _ _ _ fun si hsi => ?_
  obtain ⟨s, i⟩ := si
  have hi : (collectRuns l)[i]? = some s := by grind [List.mem_zipIdx']
  cases s with
  | gate g => simp [segEmit, Seg.gates]
  | run q gs =>
    rcases h : fit i q gs with _ | ⟨a, θ, p⟩
    · simp [segEmit, h, Seg.gates]
    · simp only [segEmit, h, Seg.gates, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      obtain ⟨e, he, hle⟩ := hfit i q gs a θ p hi h
      exact (norm_sub_le_checkRun he).trans (by exact_mod_cast hle)

/-- The run fit wrapped by the checker: a proposal `(a, θ, b)` of `fit` on a run `gs` is kept
when `checkRun` on `gs`, the template `runTemplate a q θ` and the phase `phase b` returns a
bound `e ≤ bound`, with the payload `(b, phase b, e)`; otherwise the run is kept. -/
def checkedZFit (fit : ZFit n β) (phase : β → PiLin) (bound : ℚ) :
    ZFit n (β × PiLin × ℚ) := fun i q gs =>
  match fit i q gs with
  | some (a, θ, b) =>
    match checkRun q gs (runTemplate a q θ) (phase b) with
    | some e => if e ≤ bound then some (a, θ, (b, phase b, e)) else none
    | none => none
  | none => none

/-- The wrapped run fit satisfies the checked hypothesis with the recorded phases and
bounds. -/
theorem zFitChecked_checkedZFit (fit : ZFit n β) (phase : β → PiLin) (bound : ℚ)
    (l : List (Gate n)) :
    ZFitChecked (checkedZFit fit phase bound) (fun b => b.2.1) (fun b => b.2.2) l := by
  intro i q gs a θ b _ hf
  simp only [checkedZFit] at hf
  split at hf
  · next a' θ' b' _ =>
    split at hf
    · next e he =>
      split at hf
      · simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        exact ⟨e, he, le_rfl⟩
      · exact absurd hf (by simp)
    · exact absurd hf (by simp)
  · exact absurd hf (by simp)

/-- **The checked ZYZ pass.** For every fit, the gates of `zyzEmit (checkedZFit fit phase
bound) l` are within the sum of the recorded bounds of `l`, up to the sum of the recorded
phases. -/
theorem listMatrix_zyzEmit_checkedZFit (fit : ZFit n β) (phase : β → PiLin) (bound : ℚ)
    (l : List (Gate n)) :
    ‖listMatrix (zyzEmit (checkedZFit fit phase bound) l).1 -
        exp (I * ((((zyzEmit (checkedZFit fit phase bound) l).2.map
          fun b => PiLin.toReal b.2.1).sum : ℝ) : ℂ)) • listMatrix l‖ ≤
      ((zyzEmit (checkedZFit fit phase bound) l).2.map fun b => (b.2.2 : ℝ)).sum :=
  listMatrix_zyzEmit_approx _ _ _ l (zFitChecked_checkedZFit fit phase bound l)

end CatCrypt.Quantum.Synthesis.IntervalArith
