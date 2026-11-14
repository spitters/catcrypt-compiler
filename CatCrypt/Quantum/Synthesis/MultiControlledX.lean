/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.AndLadder
public import CatCrypt.Quantum.Synthesis.KAKPass

/-!
# Multi-controlled `X` with a linear number of `CNOT`s

The `X` gate on a target `t` controlled on `k ≥ 1` qubits `c :: cs`, with `k - 1` clean
ancillae `as`, is the AND ladder of relative-phase Toffolis (`AndLadder.andLadder`; Maslov,
*Advantages of using relative-phase Toffoli gates with an application to multiple control
Toffoli optimization*, Phys. Rev. A 93, 2016) computing the conjunction of the controls into
the last ancilla, one `CNOT` from that ancilla to `t`, and the inverse ladder. Each rung of
the ladder is a relative-phase Toffoli with three `CNOT`s, so the circuit has
`6 (k - 1) + 1` `CNOT`s and `18 (k - 1) + 1` gates, against the exponential count of the
ancilla-free `ControlledGates.mctrlGates`. On clean ancillae its matrix is `X_t` controlled
on every control, and every ancilla is returned to `|0⟩`.

## Main definitions

* `mcxGates c cs as t` — the multi-controlled `X` on the controls `c :: cs` with the ancillae
  `as`.

## Main results

* `listMatrix_mcxGates` — on clean ancillae the matrix is `X_t` controlled on `c :: cs`.
* `mcxGates_restores` — every ancilla is returned to `|0⟩`.
* `cnotCount_mcxGates` — exactly `6 · |as| + 1` `CNOT`s, that is `6 (k - 1) + 1` for `k`
  controls.
* `length_mcxGates` — exactly `18 · |as| + 1` gates.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.AndAncilla
open CatCrypt.Quantum.AndLadder
open CatCrypt.Quantum.Synthesis.KAKPass (isCNOT cnotCount)
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append invGate
  invGates)

namespace CatCrypt.Quantum.Synthesis.MultiControlledX

variable {n : ℕ}

/-- The `X` gate on `t` controlled on `c :: cs`, with the clean ancillae `as`
(`|as| = |cs|`): the AND ladder, a `CNOT` from its last ancilla to `t`, the inverse ladder. -/
def mcxGates (c : Fin n) (cs as : List (Fin n)) (t : Fin n) : List (Gate n) :=
  ancillaCtrlGates (andLadder c cs as) (ladderTarget c as) [Gate.X t]

/-- **Multi-controlled `X`.** For distinct controls, ancillae and target, on clean ancillae the
matrix of `mcxGates c cs as t` is `X_t` controlled on every qubit of `c :: cs`. -/
theorem listMatrix_mcxGates {c t : Fin n} {cs as : List (Fin n)} (hlen : cs.length = as.length)
    (hnd : (c :: cs ++ as).Nodup) (ht : t ∉ c :: cs ++ as) :
    listMatrix (mcxGates c cs as t) * cleanProj as
      = mctrlMatrix (c :: cs) (embedGate1 n t pauliX) * cleanProj as := by
  have hU : ∀ g ∈ [Gate.X t], ∀ q ∈ c :: cs ++ as, Avoids q g := by
    intro g hg q hq
    rw [List.mem_singleton] at hg
    subst hg
    exact fun h => ht (h ▸ hq)
  have h := listMatrix_ladderCtrl hlen hnd hU
  rwa [listMatrix_cons, listMatrix_nil, one_mul] at h

/-- **The ancillae are restored.** -/
theorem mcxGates_restores {c t q : Fin n} {cs as : List (Fin n)} (hlen : cs.length = as.length)
    (hnd : (c :: cs ++ as).Nodup) (ht : t ∉ c :: cs ++ as) (hq : q ∈ as) :
    embedGate1 n q proj1 * listMatrix (mcxGates c cs as t) * cleanProj as = 0 := by
  have hU : ∀ g ∈ [Gate.X t], ∀ q ∈ c :: cs ++ as, Avoids q g := by
    intro g hg q hq
    rw [List.mem_singleton] at hg
    subst hg
    exact fun h => ht (h ▸ hq)
  exact ladderCtrl_restores hlen hnd hU hq

theorem isCNOT_invGate (g : Gate n) : isCNOT (invGate g) = isCNOT g := by
  cases g <;> rfl

theorem cnotCount_invGates (l : List (Gate n)) : cnotCount (invGates l) = cnotCount l := by
  simp only [cnotCount, invGates, List.countP_reverse, List.countP_map]
  exact List.countP_congr fun g _ => by simp [Function.comp, isCNOT_invGate]

theorem cnotCount_append (l₁ l₂ : List (Gate n)) :
    cnotCount (l₁ ++ l₂) = cnotCount l₁ + cnotCount l₂ :=
  List.countP_append

/-- Each rung of the ladder has three `CNOT`s. -/
theorem cnotCount_andLadder : ∀ (c : Fin n) (cs as : List (Fin n)), cs.length = as.length →
    cnotCount (andLadder c cs as) = 3 * as.length
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => absurd h (by simp)
  | _, _ :: _, [], h => absurd h (by simp)
  | c, c₁ :: cs, a :: as, h => by
    have e : andLadder c (c₁ :: cs) (a :: as) = rtofGates c c₁ a ++ andLadder a cs as := rfl
    rw [e, cnotCount_append, cnotCount_andLadder a cs as (by simpa using h)]
    simp [rtofGates, cnotCount, isCNOT, List.countP_cons]
    ring

/-- **Linear `CNOT` count.** The multi-controlled `X` on `k = |cs| + 1` controls has
`6 (k - 1) + 1` `CNOT`s. -/
theorem cnotCount_mcxGates (c : Fin n) {cs as : List (Fin n)} (h : cs.length = as.length)
    (t : Fin n) : cnotCount (mcxGates c cs as t) = 6 * as.length + 1 := by
  simp only [mcxGates, ancillaCtrlGates, cnotCount_append, cnotCount_invGates,
    cnotCount_andLadder c cs as h]
  simp [ctrlList, ctrlGates, cnotCount, isCNOT]
  ring

/-- The multi-controlled `X` on `k = |cs| + 1` controls has `18 (k - 1) + 1` gates. -/
theorem length_mcxGates (c : Fin n) {cs as : List (Fin n)} (h : cs.length = as.length)
    (t : Fin n) : (mcxGates c cs as t).length = 18 * as.length + 1 := by
  simp only [mcxGates, ancillaCtrlGates, List.length_append, QFT.length_invGates,
    length_andLadder c cs as h]
  simp [ctrlList, ctrlGates]
  ring

end CatCrypt.Quantum.Synthesis.MultiControlledX
