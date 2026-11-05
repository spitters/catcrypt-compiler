/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.EGraphRuleSound

/-!
# Real-semantics soundness of the Level-4 rule-rewriting optimizer

`EGraphRuleSound.lean` establishes the per-rule soundness
`rewriteFixpointRules_soundU : ∀ r ∈ allCircuitRules n, SoundU r`: whenever a rewrite
rule fires on a gate list `gs` returning `(m, repl)`, the matched window
`gs.take m` and the replacement `repl` have the same unitary-channel denotation
(`udL (gs.take m) = udL repl`).

This file lifts that per-rule fact through the saturation engine
(`tryRules → applyRulesOnceAux → applyRulesOnce → saturateCircuit`) to the full
optimizer `rewriteFixpointOptimize`, proving it preserves the real
`unitaryDenote` semantics:

* `rewriteFixpointOptimize_unitaryCorrect : UnitaryCorrectQ rewriteFixpointOptimize`
* `rewriteFixpointOptimize_unitaryDenote : unitaryDenote (rewriteFixpointOptimize c) = unitaryDenote c`

## Implementation reminder

`rewriteFixpointOptimize` is a **list-rewrite-to-fixpoint** (option (a)): flatten
`c` to a gate list via `circuitToList`, run `saturateCircuit` — a fuel-bounded
iteration of `applyRulesOnce`, itself a fuel-bounded left-to-right scan that
splices a fired window `gs.take m ↦ repl` and continues — then rebuild via
`Circuit.ofList`.  There is no e-class / union-find data structure, so the proof
is the list-rewrite invariant: each scan preserves `udL` of the running list,
lifted by the append-homomorphism `unitaryDenote_ofList_append`.

## Main results

* `tryRules_soundU` — when the first firing rule of a rule list rewrites a window, the
  window and its replacement have the same `udL` denotation.
* `applyRulesOnce_udL` — one left-to-right rewriting scan preserves `udL`.
* `saturateCircuit_udL` — the fuel-bounded iteration of the scan preserves `udL`.
* `rewriteFixpointOptimize_unitaryDenote` — `rewriteFixpointOptimize` preserves
  `unitaryDenote`.
* `rewriteFixpointOptimize_unitaryCorrect` — `UnitaryCorrectQ rewriteFixpointOptimize`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.TemplateMatching
open CatCrypt.Quantum.Optimization.UnitarySound
open CatCrypt.Quantum.Optimization.EGraphRuleSound

namespace CatCrypt.Quantum.Optimization.RewriteFixpoint

variable {n : ℕ}

/-! ## `udL` append congruence

`udL gs = unitaryDenote (Circuit.ofList gs)` is homomorphic over append
(`unitaryDenote_ofList_append`).  These two lemmas let us replace a window by a
`udL`-equal one inside any left/right context. -/

/-- Replacing a list by a `udL`-equal one in a *right* context preserves `udL`. -/
theorem udL_congr_right {ys ys' : List (Gate n)} (h : udL ys = udL ys')
    (zs : List (Gate n)) : udL (ys ++ zs) = udL (ys' ++ zs) := by
  simp only [udL, unitaryDenote_ofList_append] at *
  rw [h]

/-- Replacing a list by a `udL`-equal one in a *left* context preserves `udL`. -/
theorem udL_congr_left {ys ys' : List (Gate n)} (h : udL ys = udL ys')
    (xs : List (Gate n)) : udL (xs ++ ys) = udL (xs ++ ys') := by
  simp only [udL, unitaryDenote_ofList_append] at *
  rw [h]

/-- Replacing a window by a `udL`-equal one inside both contexts preserves `udL`. -/
theorem udL_congr_window {ys ys' : List (Gate n)} (h : udL ys = udL ys')
    (xs zs : List (Gate n)) : udL (xs ++ ys ++ zs) = udL (xs ++ ys' ++ zs) := by
  rw [List.append_assoc, List.append_assoc]
  exact udL_congr_left (udL_congr_right h zs) xs

/-! ## The saturation engine preserves `udL`

The invariant is: a single scan / loop iteration preserves `udL` of the running
gate list. -/

/-- A `tryRules` hit is sound: the fired window equals its replacement.

`tryRules` returns the result of the first rule whose `apply` succeeds, so the
hit is a hit of some rule in `rules`, and that rule is `SoundU`. -/
theorem tryRules_soundU
    (rules : List (CircuitRule n)) (hsound : ∀ r ∈ rules, SoundU r)
    (gates : List (Gate n)) (m : ℕ) (repl : List (Gate n))
    (h : tryRules rules gates = some (m, repl)) :
    udL (gates.take m) = udL repl := by
  induction rules with
  | nil => simp [tryRules] at h
  | cons r rs ih =>
    simp only [tryRules] at h
    split at h
    next heq =>
      have happ : r.apply gates = some (m, repl) := by
        simp only [Option.some.injEq] at h; rw [← h]; exact heq
      exact hsound r (by simp) gates m repl happ
    next =>
      exact ih (fun r' hr' => hsound r' (by simp [hr'])) h

/-- One scan step preserves `udL` of `pfx.reverse ++ suffix`. -/
theorem applyRulesOnceAux_udL
    (rules : List (CircuitRule n)) (hsound : ∀ r ∈ rules, SoundU r)
    (pfx suffix : List (Gate n)) (changed : Bool) (fuel : Nat) :
    udL (applyRulesOnceAux rules pfx suffix changed fuel).1 =
      udL (pfx.reverse ++ suffix) := by
  induction fuel generalizing pfx suffix changed with
  | zero => simp [applyRulesOnceAux]
  | succ fuel' ih =>
    unfold applyRulesOnceAux
    match suffix with
    | [] => simp
    | g :: rest =>
      simp only
      split
      next ml replacement heq =>
        -- a rule fired: `tryRules rules (g::rest) = some (ml, replacement)`.
        -- It is one of `rules`, so by `SoundU`:
        --   `udL ((g::rest).take ml) = udL replacement`.
        rw [ih]
        -- goal: udL (pfx.reverse ++ (replacement ++ (g::rest).drop ml))
        --     = udL (pfx.reverse ++ (g :: rest))
        have hwin : udL ((g :: rest).take ml) = udL replacement :=
          tryRules_soundU rules hsound (g :: rest) ml replacement heq
        have hsplit : (g :: rest) = (g :: rest).take ml ++ (g :: rest).drop ml :=
          (List.take_append_drop ml (g :: rest)).symm
        calc
          udL (pfx.reverse ++ (replacement ++ (g :: rest).drop ml))
              = udL (pfx.reverse ++ replacement ++ (g :: rest).drop ml) := by
                rw [List.append_assoc]
          _ = udL (pfx.reverse ++ (g :: rest).take ml ++ (g :: rest).drop ml) :=
                udL_congr_window hwin.symm pfx.reverse ((g :: rest).drop ml)
          _ = udL (pfx.reverse ++ ((g :: rest).take ml ++ (g :: rest).drop ml)) := by
                rw [List.append_assoc]
          _ = udL (pfx.reverse ++ (g :: rest)) := by rw [← hsplit]
      next =>
        rw [ih]
        -- goal: udL ((g::pfx).reverse ++ rest) = udL (pfx.reverse ++ (g :: rest))
        simp [List.reverse_cons]

/-- One full scan preserves `udL`. -/
theorem applyRulesOnce_udL
    (rules : List (CircuitRule n)) (hsound : ∀ r ∈ rules, SoundU r)
    (gates : List (Gate n)) :
    udL (applyRulesOnce rules gates).1 = udL gates := by
  simp only [applyRulesOnce]
  rw [applyRulesOnceAux_udL rules hsound [] gates false]
  simp

/-- The full saturation loop preserves `udL`. -/
theorem saturateCircuit_udL
    (rules : List (CircuitRule n)) (hsound : ∀ r ∈ rules, SoundU r)
    (fuel : Nat) (gates : List (Gate n)) :
    udL (saturateCircuit rules fuel gates) = udL gates := by
  induction fuel generalizing gates with
  | zero => simp [saturateCircuit]
  | succ fuel' ih =>
    simp only [saturateCircuit]
    split
    · rw [ih, applyRulesOnce_udL rules hsound gates]
    · exact applyRulesOnce_udL rules hsound gates

/-! ## The optimizer preserves `unitaryDenote` -/

/-- **Real-semantics correctness of the Level-4 rule-rewriting optimizer.**
`rewriteFixpointOptimize` preserves the unitary-channel denotation
`unitaryDenote` (ρ ↦ UρU†). -/
theorem rewriteFixpointOptimize_unitaryDenote (c : Circuit n) :
    unitaryDenote (rewriteFixpointOptimize c) = unitaryDenote c := by
  simp only [rewriteFixpointOptimize]
  -- `rewriteFixpointOptimize c = Circuit.ofList (saturateCircuit … (circuitToList c))`.
  -- `unitaryDenote (Circuit.ofList gs) = udL gs` by definition of `udL`.
  show udL (saturateCircuit (allCircuitRules n) 100 (TemplateMatching.circuitToList c))
      = unitaryDenote c
  rw [saturateCircuit_udL (allCircuitRules n) (rewriteFixpointRules_soundU) 100
        (TemplateMatching.circuitToList c)]
  show unitaryDenote (Circuit.ofList (TemplateMatching.circuitToList c)) = unitaryDenote c
  exact unitaryDenote_circuitToList c

/-- The Level-4 rule-rewriting optimizer is unitary-correct (`UnitaryCorrectQ`). -/
theorem rewriteFixpointOptimize_unitaryCorrect :
    UnitaryCorrectQ (rewriteFixpointOptimize : Circuit n → Circuit n) := by
  intro c
  exact (rewriteFixpointOptimize_unitaryDenote c).symm

end CatCrypt.Quantum.Optimization.RewriteFixpoint

namespace CatCrypt.Quantum.Optimization.EGraphCircuit

@[deprecated RewriteFixpoint.rewriteFixpointOptimize_unitaryDenote (since := "2026-10-10")]
alias eGraphCircuitOptimize_unitaryDenote :=
  RewriteFixpoint.rewriteFixpointOptimize_unitaryDenote

@[deprecated RewriteFixpoint.rewriteFixpointOptimize_unitaryCorrect (since := "2026-10-10")]
alias eGraphCircuitOptimize_unitaryCorrect :=
  RewriteFixpoint.rewriteFixpointOptimize_unitaryCorrect

end CatCrypt.Quantum.Optimization.EGraphCircuit
