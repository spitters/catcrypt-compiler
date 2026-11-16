/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.HTWord

/-!
# The checked replacement of one-qubit gates by words over `H`, `T`, `T†`

The pass `skReplaceChecked gen bound` replaces every one-qubit gate `g` other than `H`, `T`,
`T†` on qubit `q` by a word proposed by an untrusted generator `gen`, placed at `q`. A
proposal `(w, φ)` is accepted when `w` is over `H`, `T`, `T†` and the ball checker `checkRun`
certifies `‖listMatrix (atQubit q w) - e^{iφ} • listMatrix [g]‖ ≤ e` with `e ≤ bound`; a gate
without an accepted proposal is kept, with phase `0` and bound `0`. The pass returns the
concatenated gates, the sum of the phases and the sum of the certified bounds. Its correctness
theorem has no hypothesis on the generator. The checker `gate1BW` encloses no real-angle `Rz`,
so such a gate is always kept; angle snapping (`AngleSnap.snapQ`) moves it to `RzQ` first.

## Main definitions

* `WordGen` — an untrusted generator of words and phases.
* `checkGate` — the certified replacement of one gate, `none` when refused.
* `skGateChecked` — the replacement of one gate, the gate itself when refused.
* `skReplaceChecked` — the checked pass.

## Main statements

* `norm_skGateChecked_sub_le` — the per-gate bound.
* `listMatrix_skReplaceChecked` — **correctness of the checked pass**: up to the global phase
  `e^{iφ}`, the output is within the sum `e` of the certified bounds, and every replaceable
  gate left in the output is a gate of the input.
* `bound_skReplaceChecked_le` — for `0 ≤ bound`, `e` is at most the number of replaceable
  gates times `bound`.
-/

@[expose] public section

set_option autoImplicit false

open Complex
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil)
open CatCrypt.Quantum.Synthesis.ZYZPass (oneQ?)
open CatCrypt.Quantum.Synthesis.IntervalArith (checkRun norm_sub_le_checkRun
  norm_listMatrix_flatMap_sub_le)
open scoped Matrix.Norms.L2Operator

namespace CatCrypt.Quantum.Synthesis.SK

variable {n : ℕ}

/-- An untrusted generator: for a one-qubit gate on qubit `0`, a proposed word and phase. -/
abbrev WordGen := Gate 1 → Option (List (Gate 1) × PiLin)

/-- One gate, certified: a replaceable gate `g` on `q` with a proposal `(w, φ)` of `gen` gives
`(atQubit q w, φ, e)` when `w` is over `H`, `T`, `T†` and `checkRun q [g] (atQubit q w) φ`
returns `e ≤ bound`; `none` otherwise. -/
def checkGate (gen : WordGen) (bound : ℚ) (g : Gate n) : Option (List (Gate n) × PiLin × ℚ) :=
  match isRot g, oneQ? g with
  | true, some q =>
    match gen (QFT.mapGate (fun _ => (0 : Fin 1)) g) with
    | some (w, φ) =>
      if w.all isHT then
        match checkRun q [g] (atQubit q w) φ with
        | some e => if e ≤ bound then some (atQubit q w, φ, e) else none
        | none => none
      else none
    | none => none
  | _, _ => none

/-- One gate: the certified replacement of `checkGate`, or the gate itself with phase `0` and
bound `0`. -/
def skGateChecked (gen : WordGen) (bound : ℚ) (g : Gate n) : List (Gate n) × PiLin × ℚ :=
  (checkGate gen bound g).getD ([g], 0, 0)

/-- The checked pass: the concatenated replacements, the sum of the phases and the sum of the
certified bounds. -/
def skReplaceChecked (gen : WordGen) (bound : ℚ) (L : List (Gate n)) :
    List (Gate n) × PiLin × ℚ :=
  let rs := L.map (skGateChecked gen bound)
  (rs.flatMap Prod.fst, (rs.map fun r => r.2.1).sum, (rs.map fun r => r.2.2).sum)

/-- What `checkGate` certifies: the gate is replaceable, the word is over `H`, `T`, `T†`, the
distance is at most the bound, and the bound is at most `bound`. -/
theorem checkGate_spec {gen : WordGen} {bound : ℚ} {g : Gate n}
    {r : List (Gate n) × PiLin × ℚ} (h : checkGate gen bound g = some r) :
    isRot g = true ∧ (∀ g' ∈ r.1, isHT g' = true) ∧
      ‖listMatrix r.1 - exp (I * (PiLin.toReal r.2.1 : ℂ)) • listMatrix [g]‖ ≤ (r.2.2 : ℝ) ∧
      r.2.2 ≤ bound := by
  unfold checkGate at h
  split at h
  · next q hr hq =>
    split at h
    · next w φ hgen =>
      split at h
      · next hw =>
        split at h
        · next e he =>
          split at h
          · next hle =>
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨hr, isHT_atQubit (by simpa using hw), norm_sub_le_checkRun he, hle⟩
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The per-gate bound of the checked replacement. -/
theorem norm_skGateChecked_sub_le (gen : WordGen) (bound : ℚ) (g : Gate n) :
    ‖listMatrix (skGateChecked gen bound g).1 -
        exp (I * (PiLin.toReal (skGateChecked gen bound g).2.1 : ℂ)) • listMatrix [g]‖ ≤
      ((skGateChecked gen bound g).2.2 : ℝ) := by
  unfold skGateChecked
  rcases hc : checkGate gen bound g with _ | r
  · simp
  · exact (checkGate_spec hc).2.2.1

/-- A replaceable gate in the replacement of `g` is `g` itself. -/
theorem eq_of_mem_skGateChecked {gen : WordGen} {bound : ℚ} {g g' : Gate n}
    (h : g' ∈ (skGateChecked gen bound g).1) (hr : isRot g' = true) : g' = g := by
  unfold skGateChecked at h
  rcases hc : checkGate gen bound g with _ | r <;> rw [hc] at h
  · simpa using h
  · simp [isRot_eq_false_of_isHT ((checkGate_spec hc).2.1 g' h)] at hr

/-- For `0 ≤ bound`, the bound of one gate is `bound` at most if it is replaceable and `0`
otherwise. -/
theorem skGateChecked_bound_le {gen : WordGen} {bound : ℚ} (hb : 0 ≤ bound) (g : Gate n) :
    (skGateChecked gen bound g).2.2 ≤ if isRot g then bound else 0 := by
  unfold skGateChecked
  rcases hc : checkGate gen bound g with _ | r
  · split_ifs <;> simp [hb]
  · obtain ⟨hr, -, -, hle⟩ := checkGate_spec hc
    simpa [hr] using hle

/-- `PiLin.toReal` of a sum is the sum of the `PiLin.toReal`. -/
theorem toReal_list_sum (l : List PiLin) : PiLin.toReal l.sum = (l.map PiLin.toReal).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]

/-- **Correctness of the checked pass**, with no hypothesis on the generator. Up to the global
phase `e^{iφ}`, the output is within the sum `e` of the certified bounds; every replaceable
gate of the output is a gate of the input, one whose proposal was refused. -/
theorem listMatrix_skReplaceChecked {gen : WordGen} {bound : ℚ} {L out : List (Gate n)}
    {φ : PiLin} {e : ℚ} (h : skReplaceChecked gen bound L = (out, φ, e)) :
    (∀ g ∈ out, isRot g = true → g ∈ L) ∧
      ‖listMatrix out - exp (I * (PiLin.toReal φ : ℂ)) • listMatrix L‖ ≤ (e : ℝ) := by
  simp only [skReplaceChecked, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨fun g hg hr => ?_, ?_⟩
  · rw [List.flatMap_map] at hg
    obtain ⟨g₀, hg₀, hg⟩ := List.mem_flatMap.mp hg
    rw [eq_of_mem_skGateChecked hg hr]
    exact hg₀
  · have h := norm_listMatrix_flatMap_sub_le L (fun g => (skGateChecked gen bound g).1)
      (fun g => [g]) (fun g => PiLin.toReal (skGateChecked gen bound g).2.1)
      (fun g => ((skGateChecked gen bound g).2.2 : ℝ))
      (fun g _ => norm_skGateChecked_sub_le gen bound g)
    simpa [List.flatMap_map, toReal_list_sum, List.map_map, Rat.cast_list_sum,
      Function.comp_def] using h

/-- For `0 ≤ bound`, the sum of the certified bounds is at most the number of replaceable
gates times `bound`. -/
theorem bound_skReplaceChecked_le {gen : WordGen} {bound : ℚ} (hb : 0 ≤ bound)
    {L out : List (Gate n)} {φ : PiLin} {e : ℚ}
    (h : skReplaceChecked gen bound L = (out, φ, e)) :
    (e : ℝ) ≤ (L.countP isRot : ℝ) * bound := by
  simp only [skReplaceChecked, Prod.mk.injEq] at h
  obtain ⟨-, -, rfl⟩ := h
  have key : ∀ l : List (Gate n),
      ((l.map (skGateChecked gen bound)).map fun r => r.2.2).sum ≤
        (l.countP isRot : ℚ) * bound := by
    intro l
    induction l with
    | nil => simp
    | cons g l ih =>
      have h1 := skGateChecked_bound_le (gen := gen) hb g
      simp only [List.map_cons, List.sum_cons, List.countP_cons]
      split_ifs at h1 with hr <;> simp only [hr] <;> push_cast <;> linarith
  exact_mod_cast key L

end CatCrypt.Quantum.Synthesis.SK
