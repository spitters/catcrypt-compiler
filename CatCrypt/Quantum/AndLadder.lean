/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.AndAncilla

/-!
# The AND ladder of relative-phase Toffolis

A multi-controlled operation on the controls `c₀, …, c_{k-1}` (`k ≥ 2`) with the clean
ancillae `a₀, …, a_{k-2}`: the AND ladder computes `a₀ = c₀ ∧ c₁` and
`a_i = a_{i-1} ∧ c_{i+1}` by relative-phase Toffolis (`AndAncilla.rtofGates`, three `CNOT`s
and four `T` gates each), the block is controlled on the last ancilla, and the inverse ladder
uncomputes every ancilla. The phases of the relative-phase Toffolis cancel between the ladder
and its inverse. The construction has `9 (k - 1)` gates in each ladder, `3 (k - 1)` of them
`CNOT`s, against the exponential growth of the ancilla-free `mctrlGates`.

The proof is an induction over the controls: each rung is the conjugation theorem
(`predAncilla_conj_ctrlMatrix`) with the previous ancilla and the next control as the two
controls of a relative-phase Toffoli, applied to the multi-controlled matrix of the rest of
the ladder.

## Main definitions

* `cleanProj as` — the projector onto the states where every ancilla of `as` reads `0`.
* `andLadder c cs as` — the AND ladder on the controls `c :: cs` and the ancillae `as`.
* `ladderTarget c as` — the last ancilla, which holds the AND.

## Main results

* `predAncilla_conj_ctrlMatrix` — the conjugation theorem for an arbitrary matrix controlled
  on the ancilla.
* `rtofGates_conj_ctrlMatrix` — one rung: conjugating by a relative-phase Toffoli adds two
  controls.
* `listMatrix_ladderCtrl` — on clean ancillae, `ancillaCtrlGates (andLadder c cs as)
  (ladderTarget c as) U` is `U` multi-controlled on `c :: cs`.
* `ladderCtrl_restores` — every ancilla is returned to `|0⟩`.
* `length_andLadder`, `length_ladderCtrl_le` — the construction is linear in the number of
  controls.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.AndAncilla
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append invGates
  listMatrix_invGates length_invGates)

noncomputable section

namespace CatCrypt.Quantum.AndLadder

variable {n : ℕ}

/-! ## Clean ancillae -/

/-- The projector onto the basis states where every qubit of `as` reads `0`: the clean
    ancillae `as`. -/
def cleanProj (as : List (Fin n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (as.map fun a => embedGate1 n a proj0).prod

/-- With no ancilla the clean-ancilla projector is the identity. -/
theorem cleanProj_nil : cleanProj ([] : List (Fin n)) = 1 := by
  simp [cleanProj]

/-- The clean-ancilla projector of `a :: as` is `|0⟩⟨0|_a` times that of `as`. -/
theorem cleanProj_cons (a : Fin n) (as : List (Fin n)) :
    cleanProj (a :: as) = embedGate1 n a proj0 * cleanProj as := by
  simp [cleanProj]

/-- The clean-ancilla projector is a phase on its qubits. -/
theorem phaseOn_cleanProj : ∀ as : List (Fin n), PhaseOn as (cleanProj as)
  | [] => by rw [cleanProj_nil]; exact phaseOn_one _
  | a :: as => by
    rw [cleanProj_cons]
    exact (phaseOn_embedGate1 List.mem_cons_self isDiagonal_proj0).mul
      ((phaseOn_cleanProj as).mono (List.subset_cons_self a as))

/-- `|1⟩⟨1|` on a clean ancilla annihilates the clean-ancilla projector. -/
theorem proj1_mul_cleanProj {q : Fin n} :
    ∀ {as : List (Fin n)}, q ∈ as → embedGate1 n q proj1 * cleanProj as = 0
  | [], h => absurd h List.not_mem_nil
  | b :: as, h => by
    rw [cleanProj_cons, ← mul_assoc]
    by_cases hqb : q = b
    · subst hqb
      rw [embedGate1_mul, proj1_mul_proj0, embedGate1_map_zero, zero_mul]
    · have hq : q ∈ as := (List.mem_cons.mp h).resolve_left hqb
      rw [commOn_embedGate1 (Ne.symm hqb) proj0 proj1, mul_assoc, proj1_mul_cleanProj hq,
        mul_zero]

/-! ## Commutation with controlled matrices -/

/-- A difference of matrices commuting with the operators on `c` commutes with them. -/
theorem CommOn.sub {c : Fin n} {M N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn c M) (hN : CommOn c N) : CommOn c (M - N) := fun G => by
  rw [mul_sub, sub_mul, hM G, hN G]

/-- A matrix controlled on `c` commutes with the operators on a qubit `q ≠ c` it commutes
    with. -/
theorem commOn_ctrlMatrix {q c : Fin n} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hqc : c ≠ q) (hM : CommOn q M) : CommOn q (ctrlMatrix c M) :=
  CommOn.add (commOn_embedGate1 hqc proj0) ((commOn_embedGate1 hqc proj1).mul hM)

/-- A multi-controlled matrix commutes with the operators on a qubit outside its controls. -/
theorem commOn_mctrlMatrix {q : Fin n} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : CommOn q M) : ∀ {cs : List (Fin n)}, q ∉ cs → CommOn q (mctrlMatrix cs M)
  | [], _ => hM
  | c :: cs, h => by
    rw [List.mem_cons, not_or] at h
    exact commOn_ctrlMatrix (Ne.symm h.1) (commOn_mctrlMatrix hM h.2)

/-! ## The conjugation theorem for a controlled matrix -/

/-- **Conjugation theorem for a controlled matrix.** `V` writes the predicate `Π` of `cs`
    into the clean ancilla `a` up to a phase `D` on `a :: cs`. For a matrix `B` commuting with
    the operators on `a`, with `Π` and with `D`, conjugating `B` controlled on `a` by `V` gives
    `1 + Π (B - 1)` on ancilla `|0⟩`. -/
theorem predAncilla_conj_ctrlMatrix {cs : List (Fin n)} {a : Fin n}
    {P D B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {V : List (Gate n)}
    (ha : a ∉ cs) (hP : IsPred cs P) (hD : PhaseOn (a :: cs) D)
    (hV : listMatrix V * embedGate1 n a proj0
      = D * (1 + P * (embedGate1 n a pauliX - 1)) * embedGate1 n a proj0)
    (hB : CommOn a B) (hPB : Commute P B) (hDB : Commute D B) :
    (listMatrix V)ᴴ * ctrlMatrix a B * listMatrix V * embedGate1 n a proj0
      = (1 + P * (B - 1)) * embedGate1 n a proj0 := by
  have hP₁ : PhaseOn [a] (embedGate1 n a proj1) :=
    phaseOn_embedGate1 List.mem_cons_self isDiagonal_proj1
  have hP₀ : PhaseOn [a] (embedGate1 n a proj0) :=
    phaseOn_embedGate1 List.mem_cons_self isDiagonal_proj0
  have hPX : Commute P (embedGate1 n a pauliX) :=
    hP.1.commute_of_keepsBits (keepsBits_embedGate1 (by rintro q hq rfl; exact ha hq) _)
  have hDW : Commute D (ctrlMatrix a B) := by
    rw [ctrlMatrix_eq_one_add]
    exact (Commute.one_right D).add_right
      ((hD.commute hP₁).mul_right (hDB.sub_right (Commute.one_right D)))
  have h10 : embedGate1 n a proj1 * embedGate1 n a proj0 = 0 := by
    rw [embedGate1_mul, proj1_mul_proj0, embedGate1_map_zero]
  have h1X0 : embedGate1 n a proj1 * embedGate1 n a pauliX * embedGate1 n a proj0
      = embedGate1 n a pauliX * embedGate1 n a proj0 := by
    rw [embedGate1_mul, embedGate1_mul, embedGate1_mul, proj1_pauliX_proj0]
  exact conj_ring (listMatrix_conjTranspose_mul V) (ctrlMatrix_eq_one_add a _) hDW hV hPX
    (hPB.sub_right (Commute.one_right P)) (hP.1.commute hP₀) (hP.1.commute hP₁)
    ((CommOn.commute hB proj0).sub_left (Commute.one_left _))
    ((CommOn.commute hB proj1).sub_left (Commute.one_left _))
    ((CommOn.commute hB pauliX).sub_left (Commute.one_left _)) hP.2 h10 h1X0

/-- **One rung of the ladder.** Conjugating `B` controlled on `a` by the relative-phase
    Toffoli on `c₁`, `c₂`, `a` gives `B` controlled on `c₁` and `c₂`, on ancilla `|0⟩`. -/
theorem rtofGates_conj_ctrlMatrix {c₁ c₂ a : Fin n} {B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ a) (h2a : c₂ ≠ a) (hB₁ : CommOn c₁ B) (hB₂ : CommOn c₂ B)
    (hBa : CommOn a B) :
    (listMatrix (rtofGates c₁ c₂ a))ᴴ * ctrlMatrix a B * listMatrix (rtofGates c₁ c₂ a)
        * embedGate1 n a proj0
      = ctrlMatrix c₁ (ctrlMatrix c₂ B) * embedGate1 n a proj0 := by
  have k : ∀ q : Fin n, CommOn q B → ∀ G, Commute (embedGate1 n q G) B := fun _ h G => h G
  have ha : a ∉ [c₁, c₂] := by simp [Ne.symm h1a, Ne.symm h2a]
  have htof : listMatrix (toffoliGates c₁ c₂ a) = 1 + ([c₁, c₂].map fun c =>
      embedGate1 n c proj1).prod * (embedGate1 n a pauliX - 1) := by
    rw [listMatrix_toffoliGates h12 h1a h2a, embedGate2_cnot h2a, ← mctrlMatrix_eq]
    rfl
  have hD : PhaseOn (a :: [c₁, c₂]) (rtofPhase c₁ c₂ a) :=
    (phaseOn_rtofPhase c₁ c₂ a).mono (by simp [List.subset_def])
  have hPB : Commute (([c₁, c₂].map fun c => embedGate1 n c proj1).prod) B := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (k _ hB₁ proj1).mul_left (k _ hB₂ proj1)
  have hDB : Commute (rtofPhase c₁ c₂ a) B := by
    simp only [rtofPhase, ctrlMatrix, branchMatrix]
    exact (k _ hB₁ proj0).add_left ((k _ hB₁ proj1).mul_left
      (((k _ hB₂ proj0).mul_left (k _ hBa _)).add_left ((k _ hB₂ proj1).mul_left (k _ hBa _))))
  rw [predAncilla_conj_ctrlMatrix ha (isPred_prod_proj1 _) hD
    (by rw [listMatrix_rtofGates h12 h1a h2a, htof]) hBa hPB hDB, ← mctrlMatrix_eq]
  rfl

/-! ## The ladder -/

/-- **AND ladder.** For controls `c :: c₁ :: … ` and clean ancillae `a₀ :: a₁ :: …`, the
    relative-phase Toffolis computing `a₀ = c ∧ c₁`, `a₁ = a₀ ∧ c₂`, …: each rung is
    `rtofGates` with the previous ancilla and the next control as its two controls. -/
def andLadder (c : Fin n) : List (Fin n) → List (Fin n) → List (Gate n)
  | c₁ :: cs, a :: as => rtofGates c c₁ a ++ andLadder a cs as
  | _, _ => []

/-- The qubit holding the AND of the ladder: the last ancilla, or the control `c` when there
    is no ancilla. -/
def ladderTarget (c : Fin n) (as : List (Fin n)) : Fin n :=
  (c :: as).getLast (List.cons_ne_nil c as)

/-- The target of a ladder with first ancilla `a` is the target of the rest of the ladder. -/
theorem ladderTarget_cons (c a : Fin n) (as : List (Fin n)) :
    ladderTarget c (a :: as) = ladderTarget a as :=
  List.getLast_cons (List.cons_ne_nil a as)

/-- The gates of a relative-phase Toffoli avoid every qubit other than its three. -/
theorem avoids_rtofGates {c₁ c₂ a q : Fin n} (h1 : c₁ ≠ q) (h2 : c₂ ≠ q) (ha : a ≠ q) :
    ∀ g ∈ rtofGates c₁ c₂ a, Avoids q g := by
  intro g hg
  simp only [rtofGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Avoids, h1, h2, ha]

/-- Conjugating the ancilla construction by a prefix of its compute step. -/
theorem listMatrix_ancillaCtrlGates_append (V₁ V₂ : List (Gate n)) (a : Fin n)
    (U : List (Gate n)) :
    listMatrix (ancillaCtrlGates (V₁ ++ V₂) a U)
      = (listMatrix V₁)ᴴ * listMatrix (ancillaCtrlGates V₂ a U) * listMatrix V₁ := by
  simp only [ancillaCtrlGates, listMatrix_append, listMatrix_invGates, Matrix.conjTranspose_mul,
    mul_assoc]

/-- **The AND ladder controls the block on every control.** On clean ancillae `as`, computing
    the AND of the controls `c :: cs` into the last ancilla by the ladder, controlling the block
    `U` on it and uncomputing is `U` controlled on every qubit of `c :: cs`. -/
theorem listMatrix_ladderCtrl {U : List (Gate n)} :
    ∀ {c : Fin n} {cs as : List (Fin n)}, cs.length = as.length → (c :: cs ++ as).Nodup →
      (∀ g ∈ U, ∀ q ∈ c :: cs ++ as, Avoids q g) →
      listMatrix (ancillaCtrlGates (andLadder c cs as) (ladderTarget c as) U) * cleanProj as
        = mctrlMatrix (c :: cs) (listMatrix U) * cleanProj as
  | c, [], [], _, _, hU => by
    have e : andLadder c [] [] = [] := rfl
    rw [e, ladderTarget, List.getLast_singleton, ancillaCtrlGates, listMatrix_append,
      listMatrix_append, listMatrix_invGates, listMatrix_nil,
      listMatrix_ctrlList fun g hg => hU g hg c List.mem_cons_self]
    simp [mctrlMatrix]
  | _, [], _ :: _, hlen, _, _ => absurd hlen (by simp)
  | _, _ :: _, [], hlen, _, _ => absurd hlen (by simp)
  | c, c₁ :: cs, a :: as, hlen, hnd, hU => by
    have hlen' : cs.length = as.length := by simpa using hlen
    have hnd' : (a :: cs ++ as).Nodup := List.perm_middle.nodup_iff.mp hnd.of_cons.of_cons
    have hU' : ∀ g ∈ U, ∀ q ∈ a :: cs ++ as, Avoids q g := fun g hg q hq =>
      hU g hg q (by simp only [List.mem_cons, List.mem_append] at hq ⊢; tauto)
    have IH := listMatrix_ladderCtrl hlen' hnd' hU'
    have hc1 : c ≠ c₁ := by grind
    have hca : c ≠ a := by grind
    have h1a : c₁ ≠ a := by grind
    have hnc : ∀ q ∈ as, c ≠ q ∧ c₁ ≠ q ∧ a ≠ q := by grind
    have hB : ∀ q ∈ [c, c₁, a], CommOn q (mctrlMatrix cs (listMatrix U)) := by
      intro q hq
      exact commOn_mctrlMatrix (commOn_listMatrix fun g hg => hU g hg q (by grind)) (by grind)
    have hRQ : Commute (listMatrix (rtofGates c c₁ a)) (cleanProj as) :=
      (commute_of_phaseOn (phaseOn_cleanProj as) fun g hg q hq =>
        avoids_rtofGates (hnc q hq).1 (hnc q hq).2.1 (hnc q hq).2.2 g hg).symm
    have hPQ : Commute (embedGate1 n a proj0) (cleanProj as) :=
      (phaseOn_embedGate1 (S := [a]) List.mem_cons_self isDiagonal_proj0).commute
        (phaseOn_cleanProj as)
    have e1 : listMatrix (rtofGates c c₁ a) * (embedGate1 n a proj0 * cleanProj as)
        = cleanProj as * (listMatrix (rtofGates c c₁ a) * embedGate1 n a proj0) := by
      rw [hPQ.eq, ← mul_assoc, hRQ.eq, mul_assoc]
    have e : andLadder c (c₁ :: cs) (a :: as) = rtofGates c c₁ a ++ andLadder a cs as := rfl
    rw [e, ladderTarget_cons, listMatrix_ancillaCtrlGates_append, cleanProj_cons]
    calc _ = (listMatrix (rtofGates c c₁ a))ᴴ * ((listMatrix (ancillaCtrlGates
            (andLadder a cs as) (ladderTarget a as) U) * cleanProj as)
            * (listMatrix (rtofGates c c₁ a) * embedGate1 n a proj0)) := by
          rw [mul_assoc _ (listMatrix (rtofGates c c₁ a)), e1]
          simp only [mul_assoc]
      _ = (listMatrix (rtofGates c c₁ a))ᴴ * ((mctrlMatrix (a :: cs) (listMatrix U)
            * cleanProj as) * (listMatrix (rtofGates c c₁ a) * embedGate1 n a proj0)) := by
          rw [IH]
      _ = (listMatrix (rtofGates c c₁ a))ᴴ * mctrlMatrix (a :: cs) (listMatrix U)
            * listMatrix (rtofGates c c₁ a) * embedGate1 n a proj0 * cleanProj as := by
          rw [mul_assoc (mctrlMatrix (a :: cs) (listMatrix U)), ← e1]
          simp only [mul_assoc]
      _ = ctrlMatrix c (ctrlMatrix c₁ (mctrlMatrix cs (listMatrix U)))
            * embedGate1 n a proj0 * cleanProj as := by
          rw [mctrlMatrix, rtofGates_conj_ctrlMatrix hc1 hca h1a (hB c (by simp))
            (hB c₁ (by simp)) (hB a (by simp))]
      _ = _ := by rw [mul_assoc]; rfl

/-- **The ladder returns every ancilla to `|0⟩`.** -/
theorem ladderCtrl_restores {U : List (Gate n)} {c q : Fin n} {cs as : List (Fin n)}
    (hlen : cs.length = as.length) (hnd : (c :: cs ++ as).Nodup)
    (hU : ∀ g ∈ U, ∀ q ∈ c :: cs ++ as, Avoids q g) (hq : q ∈ as) :
    embedGate1 n q proj1 * listMatrix (ancillaCtrlGates (andLadder c cs as) (ladderTarget c as) U)
      * cleanProj as = 0 := by
  have hM : CommOn q (mctrlMatrix (c :: cs) (listMatrix U)) :=
    commOn_mctrlMatrix (commOn_listMatrix fun g hg => hU g hg q (by grind)) (by grind)
  rw [mul_assoc, listMatrix_ladderCtrl hlen hnd hU, ← mul_assoc, hM proj1, mul_assoc,
    proj1_mul_cleanProj hq, mul_zero]

/-- The ladder has nine gates per ancilla. -/
theorem length_andLadder : ∀ (c : Fin n) (cs as : List (Fin n)), cs.length = as.length →
    (andLadder c cs as).length = 9 * as.length
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => absurd h (by simp)
  | _, _ :: _, [], h => absurd h (by simp)
  | c, c₁ :: cs, a :: as, h => by
    have e : andLadder c (c₁ :: cs) (a :: as) = rtofGates c c₁ a ++ andLadder a cs as := rfl
    rw [e, List.length_append, length_andLadder a cs as (by simpa using h)]
    simp [rtofGates]
    ring

/-- The ladder construction is linear in the number of controls: eighteen gates per ancilla
    plus nineteen per gate of the block. -/
theorem length_ladderCtrl_le (c : Fin n) {cs as : List (Fin n)} (h : cs.length = as.length)
    (U : List (Gate n)) :
    (ancillaCtrlGates (andLadder c cs as) (ladderTarget c as) U).length
      ≤ 18 * as.length + 19 * U.length := by
  have := length_ancillaCtrlGates (andLadder c cs as) (ladderTarget c as) U
  rw [length_andLadder c cs as h] at this
  omega

end CatCrypt.Quantum.AndLadder
