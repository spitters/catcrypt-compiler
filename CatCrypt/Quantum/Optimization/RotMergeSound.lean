/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.RotationMerging
public import CatCrypt.Quantum.Optimization.FusionSound
public import CatCrypt.Quantum.Optimization.CommuteSound
public import CatCrypt.Quantum.Optimization.UnitarySound
public import CatCrypt.Quantum.Optimization.MixedCommute
public import CatCrypt.Quantum.Optimization.ControlCommute
public import CatCrypt.Quantum.Optimization.CommuteMergeSound

/-!
# Real-semantics soundness of VOQC-style rotation merging

`RotationMerging.rotationMergingPass` is the pass that most directly mirrors
VOQC's Coq-verified rotation merging: it flattens the circuit, normalizes the
`Rz`-family gates (`T`, `Tdg`, `S`, `Z`) into explicit `Rz`, then repeatedly
finds an `Rz(α)` separated from a later `Rz(β)` on the **same** qubit by a run
of gates that all *commute* with `Rz`, slides the rotations together, and fuses
them via `Rz(α); Rz(β) = Rz(α + β)`.

The pass is stated against the unitary-channel semantics
`GateUnitarity.unitaryDenote` (ρ ↦ UρU†).

## Proof architecture

* `CommuteMergeSound.gateEmbedding_rz_comm` — at the matrix level, the embedding of
  any gate `g` that `gateCommutes` with `Rz q` commutes with the embedding of `Rz q θ`.
* `rzCommutesU` / `unitaryDenote_cons_swapRz` — lift the matrix commutation to a
  head-swap of any gate list under `unitaryDenote`.
* `unitaryDenote_mergeRz` — fuse two same-qubit `Rz`'s at the head of a list,
  which is `CommuteMergeSound.unitaryDenote_merge_rz` (`Rz θ₁; Rz θ₂ = Rz(θ₁+θ₂)`).
* `normalizeToRz_denoteU` / `normalizeList_unitaryDenote` — normalization
  (`T = Rz(π/4)`, …) preserves `unitaryDenote` (exact matrix equalities).
* `findMergePartner_slide` — the run of gates between the head `Rz` and its merge
  partner all commute, so the head `Rz q θ₁` slides to the partner at position
  `k`, fuses, and the partner is removed — at the list-denotation level.
* `mergeRotations_unitaryDenote` / `rotationMergingPass_unitaryCorrect` — the
  fuel recursion and the flatten/normalize/merge/rebuild wrapper preserve
  `unitaryDenote`; i.e. `UnitaryCorrectQ`.

## Main results

* `unitaryDenote_cons_swapRz` — a gate that commutes with `Rz q` swaps with `Rz q θ` at
  the head of a gate list under `unitaryDenote`.
* `unitaryDenote_mergeRz` — `Rz q α; Rz q β` at the head of a gate list has the
  denotation of `Rz q (α + β)`.
* `normalizeList_unitaryDenote` — rewriting `T`, `Tdg`, `S`, `Z` into `Rz` preserves the
  list denotation.
* `mergeStep_correctU` — fusing a head `Rz` with its merge partner and deleting the
  partner preserves the list denotation.
* `mergeRotations_unitaryDenote` — the fuel-bounded merge recursion preserves
  `unitaryDenote`.
* `rotationMergingPass_unitaryCorrect` — `rotationMergingPass` is `UnitaryCorrectQ`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.CommuteSound
open CatCrypt.Quantum.Optimization.FusionSound
open CatCrypt.Quantum.Optimization.RotationMerging
open CatCrypt.Quantum.Optimization.CommutationRules
open CatCrypt.Quantum.Optimization.CommuteMergeSound (gateEmbedding_rz_comm)

noncomputable section

namespace CatCrypt.Quantum.Optimization.RotMergeSound

variable {n : ℕ}

/-! ## Lifting matrix commutation to the list denotation -/

/-- The matrix commutation lifts to the unitary-group level. -/
theorem gateEmbedding_unitaryGroup_rz_comm {q : Fin n} {g : Gate n} (θ : ℝ)
    (h : gateCommutes (Gate.Rz q (0 : ℝ)) g = true) :
    gateEmbedding_unitaryGroup g * gateEmbedding_unitaryGroup (Gate.Rz q θ)
      = gateEmbedding_unitaryGroup (Gate.Rz q θ) * gateEmbedding_unitaryGroup g := by
  apply Subtype.ext
  show gateEmbedding g * gateEmbedding (Gate.Rz q θ)
    = gateEmbedding (Gate.Rz q θ) * gateEmbedding g
  exact (gateEmbedding_rz_comm θ h).symm

/-- `Rz q θ` commutes with `g` under `unitaryDenote` at the head of a gate list,
whenever `gateCommutes (Rz q 0) g = true`. -/
theorem unitaryDenote_cons_swapRz {q : Fin n} {g : Gate n} (θ : ℝ)
    (h : gateCommutes (Gate.Rz q (0 : ℝ)) g = true) (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (Gate.Rz q θ :: g :: gs))
      = unitaryDenote (Circuit.ofList (g :: Gate.Rz q θ :: gs)) :=
  MatrixSound.unitaryDenote_eq_of_circuitUnitary_eq
    (MatrixSound.circuitUnitary_ofList_swap (gateEmbedding_rz_comm θ h).symm gs)

/-- Fuse two same-qubit `Rz`'s at the head of a gate list
(`CommuteMergeSound.unitaryDenote_merge_rz`). -/
theorem unitaryDenote_mergeRz (q : Fin n) (α β : ℝ) (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (Gate.Rz q α :: Gate.Rz q β :: gs))
      = unitaryDenote (Circuit.ofList (Gate.Rz q (α + β) :: gs)) :=
  CommuteMergeSound.unitaryDenote_merge_rz q α β gs

/-! ## Normalization preserves `unitaryDenote` -/

/-- `T = Rz(π/4)`, `Tdg = Rz(-π/4)`, `S = Rz(π/2)`, `Z = Rz(π)` are *exact*
matrix equalities rather than equalities up to global phase: both sides are
`diag(1, e^{i·})`. Hence normalization preserves the gate channel
`denoteGateU`. -/
theorem normalizeToRz_denoteU (g : Gate n) :
    denoteGateU (normalizeToRz g) = denoteGateU g := by
  cases g with
  | T i =>
    change denoteGateU (Gate.Rz i (PiLin.toReal (1 / 4))) = denoteGateU (Gate.T i)
    rw [show PiLin.toReal (1 / 4) = Real.pi / 4 by
      simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.toReal_ofPi]
      push_cast; ring]
    unfold denoteGateU; apply congrArg; apply Subtype.ext
    show embedGate1 n i (rzGate (Real.pi / 4)) = embedGate1 n i Programs.Qubit.tGate
    rw [rzGate_eq_diagB, tGate_eq_diagB]
  | Tdg i =>
    change denoteGateU (Gate.Rz i (PiLin.toReal (-(1 / 4)))) = denoteGateU (Gate.Tdg i)
    rw [show PiLin.toReal (-(1 / 4)) = -(Real.pi / 4) by
      simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.neg_ofPi,
        PiLin.toReal_ofPi]
      push_cast; ring]
    unfold denoteGateU; congr 1; apply Subtype.ext
    show embedGate1 n i (rzGate (-(Real.pi / 4))) = embedGate1 n i tDaggerGate
    rw [rzGate_eq_diagB, tDaggerGate_eq_diagB]
    congr 2
    push_cast; ring_nf
  | S i =>
    change denoteGateU (Gate.Rz i (PiLin.toReal (1 / 2))) = denoteGateU (Gate.S i)
    rw [show PiLin.toReal (1 / 2) = Real.pi / 2 by
      simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.toReal_ofPi]
      push_cast; ring]
    unfold denoteGateU; congr 1; apply Subtype.ext
    show embedGate1 n i (rzGate (Real.pi / 2)) = embedGate1 n i Programs.Qubit.phaseS
    rw [rzGate_eq_diagB, phaseS_eq_diagB]
    congr 2
    rw [mul_comm, Complex.exp_mul_I]; push_cast
    rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]; simp
  | Z i =>
    change denoteGateU (Gate.Rz i (PiLin.toReal 1)) = denoteGateU (Gate.Z i)
    rw [show PiLin.toReal 1 = Real.pi by simp]
    unfold denoteGateU; congr 1; apply Subtype.ext
    show embedGate1 n i (rzGate Real.pi) = embedGate1 n i Programs.Qubit.pauliZ
    rw [rzGate_eq_diagB, pauliZ_eq_diagB]
    congr 2
    rw [mul_comm, Complex.exp_mul_I]
    rw [Complex.cos_pi, Complex.sin_pi]; simp
  | H i => rfl
  | X i => rfl
  | Y i => rfl
  | Rz i θ => rfl
  | RzQ i a => rfl
  | CNOT i j => rfl
  | CZ i j => rfl

/-- Normalization preserves the list denotation. -/
theorem normalizeList_unitaryDenote (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (normalizeList gs))
      = unitaryDenote (Circuit.ofList gs) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    show QComp.qbind (denoteGateU (normalizeToRz g))
          (fun _ => unitaryDenote (Circuit.ofList (normalizeList gs)))
       = QComp.qbind (denoteGateU g)
          (fun _ => unitaryDenote (Circuit.ofList gs))
    rw [normalizeToRz_denoteU, ih]

/-! ## Index bookkeeping for `findMergePartner` -/

/-- `findMergePartner` returns an index relative to its `idx` argument; shifting
the start offset shifts the result by the same amount. -/
theorem findMergePartner_shift (q : Fin n) :
    ∀ (rest : List (Gate n)) (idx : ℕ),
      findMergePartner rest q idx = (findMergePartner rest q 0).map (· + idx) := by
  intro rest
  induction rest with
  | nil => intro idx; simp [findMergePartner]
  | cons g gs ih =>
    intro idx
    simp only [findMergePartner]
    cases rzAngle? g with
    | some qθ =>
      obtain ⟨q', _⟩ := qθ
      by_cases hqq : q = q'
      · simp [hqq]
      · by_cases hcomm : gateCommutes (Gate.Rz q 0) g = true
        · simp only [hqq, decide_false, Bool.false_eq_true, ite_false, hcomm, ite_true]
          rw [ih (idx + 1), ih (0 + 1)]
          cases findMergePartner gs q 0 with
          | none => rfl
          | some m => simp only [Option.map_some]; congr 1; omega
        · simp [hqq, hcomm]
    | none =>
      by_cases hcomm : gateCommutes (Gate.Rz q 0) g = true
      · simp only [hcomm, ite_true]
        rw [ih (idx + 1), ih (0 + 1)]
        cases findMergePartner gs q 0 with
        | none => rfl
        | some m => simp only [Option.map_some]; congr 1; omega
      · simp [hcomm]

/-- The partner returned by `findMergePartner rest q` is always an `Rz`-family
gate on qubit `q` (that is the loop's only exit-with-`some` condition). -/
theorem findMergePartner_partner_qubit (q : Fin n) :
    ∀ (rest : List (Gate n)) (idx k : ℕ) (partner : Gate n) (qp : Fin n) (θ : RzAngle),
      findMergePartner rest q idx = some k →
      List.getAt? rest (k - idx) = some partner →
      rzAngle? partner = some (qp, θ) →
      qp = q := by
  intro rest
  induction rest with
  | nil => intro idx k partner qp θ hfind _ _; simp [findMergePartner] at hfind
  | cons g gs ih =>
    intro idx k partner qp θ hfind hget hpart
    simp only [findMergePartner] at hfind
    cases hrz : rzAngle? g with
    | some qθ =>
      obtain ⟨q', φ⟩ := qθ
      rw [hrz] at hfind; simp only [] at hfind
      by_cases hqq : q = q'
      · rw [ite_eq_left (decide_eq_true hqq)] at hfind
        simp only [Option.some.injEq] at hfind
        subst hfind
        simp only [Nat.sub_self, List.getAt?, Option.some.injEq] at hget
        subst hget
        rw [hrz] at hpart
        simp only [Option.some.injEq, Prod.mk.injEq] at hpart
        exact hpart.1.symm.trans hqq.symm
      · rw [ite_eq_right (by simp [hqq])] at hfind
        by_cases hcomm : gateCommutes (Gate.Rz q 0) g = true
        · rw [ite_eq_left hcomm] at hfind
          have hkle : idx + 1 ≤ k := by
            have hsh := hfind
            rw [findMergePartner_shift q gs (idx + 1)] at hsh
            rcases hm : findMergePartner gs q 0 with _ | m
            · rw [hm] at hsh; simp at hsh
            · rw [hm] at hsh
              simp only [Option.map_some, Option.some.injEq] at hsh; omega
          have hget' : List.getAt? gs (k - (idx + 1)) = some partner := by
            have hkeq : k - idx = (k - (idx + 1)) + 1 := by omega
            rw [hkeq] at hget
            simpa only [List.getAt?] using hget
          exact ih (idx + 1) k partner qp θ hfind hget' hpart
        · rw [ite_eq_right hcomm] at hfind; simp at hfind
    | none =>
      rw [hrz] at hfind; simp only [] at hfind
      by_cases hcomm : gateCommutes (Gate.Rz q 0) g = true
      · rw [ite_eq_left hcomm] at hfind
        have hkle : idx + 1 ≤ k := by
          have hsh := hfind
          rw [findMergePartner_shift q gs (idx + 1)] at hsh
          rcases hm : findMergePartner gs q 0 with _ | m
          · rw [hm] at hsh; simp at hsh
          · rw [hm] at hsh
            simp only [Option.map_some, Option.some.injEq] at hsh; omega
        have hget' : List.getAt? gs (k - (idx + 1)) = some partner := by
          have hkeq : k - idx = (k - (idx + 1)) + 1 := by omega
          rw [hkeq] at hget
          simpa only [List.getAt?] using hget
        exact ih (idx + 1) k partner qp θ hfind hget' hpart
      · rw [ite_eq_right hcomm] at hfind; simp at hfind

/-! ## The single merge step -/

/-- A gate recognised by `rzAngle?` denotes the same channel as the explicit
`Rz` gate by the real value of its angle (`T = Rz(π/4)`, …). -/
theorem rzAngle?_denoteU {g : Gate n} {q : Fin n} {θ : RzAngle}
    (h : rzAngle? g = some (q, θ)) :
    denoteGateU g = denoteGateU (Gate.Rz q θ.toReal) := by
  cases g with
  | Rz i α =>
    simp only [rzAngle?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | RzQ i a =>
    simp only [rzAngle?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | T i =>
    simp only [rzAngle?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact (normalizeToRz_denoteU (Gate.T i)).symm
  | Tdg i =>
    simp only [rzAngle?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact (normalizeToRz_denoteU (Gate.Tdg i)).symm
  | S i =>
    simp only [rzAngle?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact (normalizeToRz_denoteU (Gate.S i)).symm
  | Z i =>
    simp only [rzAngle?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact (normalizeToRz_denoteU (Gate.Z i)).symm
  | H i => simp [rzAngle?] at h
  | X i => simp [rzAngle?] at h
  | Y i => simp [rzAngle?] at h
  | CNOT i j => simp [rzAngle?] at h
  | CZ i j => simp [rzAngle?] at h

/-- The rotation `θ.gate q` denotes `Rz q θ.toReal`. -/
theorem RzAngle.gate_denoteU (q : Fin n) (θ : RzAngle) :
    denoteGateU (θ.gate q) = denoteGateU (Gate.Rz q θ.toReal) := by
  cases θ <;> rfl

/-- A sum computed by `RzAngle.add?` has the sum of the real values. -/
theorem RzAngle.toReal_of_add? {θ₁ θ₂ θ : RzAngle} (h : θ₁.add? θ₂ = some θ) :
    θ.toReal = θ₁.toReal + θ₂.toReal := by
  cases θ₁ <;> cases θ₂ <;> simp only [RzAngle.add?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h
  · rfl
  · simp only [RzAngle.toReal, PiLin.toReal_add]

/-- Replace a `gateCommutes`-certified head gate `g` (between an `Rz q θ` and the
rest) with anything of the same denotation, sliding the `Rz` rightward. More
usefully: at the head, `Rz q θ :: g :: tl` and `g :: Rz q θ :: tl` agree under
`unitaryDenote` when `gateCommutes (Rz q 0) g`. -/
theorem cons_rz_commute {q : Fin n} (θ : ℝ) {g : Gate n}
    (hc : gateCommutes (Gate.Rz q (0 : ℝ)) g = true) (tl : List (Gate n)) :
    unitaryDenote (Circuit.ofList (Gate.Rz q θ :: g :: tl))
      = unitaryDenote (Circuit.ofList (g :: Gate.Rz q θ :: tl)) :=
  unitaryDenote_cons_swapRz θ hc tl

/-- The deeper-partner slide step, factored out of `mergeStep_correctU`'s
induction.  Here `g` is a gate that commutes with `Rz q` and the partner lives
inside `gs` at the shifted index `findMergePartner gs q 1 = some k`.  Using the
index-shift lemma, `k = k' + 1` with `findMergePartner gs q 0 = some k'`; we then
slide `Rz q θ₁` past `g`, merge inside `gs` via the induction hypothesis `ih`,
and slide the fused `Rz q (θ₁+θ₂)` back. -/
theorem mergeStep_slide {g : Gate n} {gs : List (Gate n)} {q : Fin n} {θ₁ : ℝ}
    {k : ℕ} {partner : Gate n} {θ₂ : RzAngle}
    (ih : ∀ (q : Fin n) (θ₁ : ℝ) (k : ℕ) (partner : Gate n) (θ₂ : RzAngle),
      findMergePartner gs q = some k → List.getAt? gs k = some partner →
      rzAngle? partner = some (q, θ₂) →
      unitaryDenote (Circuit.ofList (Gate.Rz q (θ₁ + θ₂.toReal) :: List.removeAt' gs k))
        = unitaryDenote (Circuit.ofList (Gate.Rz q θ₁ :: gs)))
    (hcomm : gateCommutes (Gate.Rz q (0 : ℝ)) g = true)
    (hfind : findMergePartner gs q 1 = some k)
    (hget : List.getAt? (g :: gs) k = some partner)
    (hpart : rzAngle? partner = some (q, θ₂)) :
    unitaryDenote (Circuit.ofList (Gate.Rz q (θ₁ + θ₂.toReal) :: List.removeAt' (g :: gs) k))
      = unitaryDenote (Circuit.ofList (Gate.Rz q θ₁ :: g :: gs)) := by
  -- k = k' + 1 with findMergePartner gs q 0 = some k'.
  rw [findMergePartner_shift q gs 1] at hfind
  cases hk : findMergePartner gs q 0 with
  | none => rw [hk] at hfind; simp at hfind
  | some k' =>
    rw [hk] at hfind
    simp only [Option.map_some, Option.some.injEq] at hfind
    subst hfind
    -- getAt?/removeAt' on `g :: gs` at `k' + 1` peel off `g`.
    have hget' : List.getAt? gs k' = some partner := by
      rw [show k' + 1 = k' + 1 from rfl] at hget
      simpa only [List.getAt?, Nat.add_eq, Nat.succ_eq_add_one] using hget
    have hrm : List.removeAt' (g :: gs) (k' + 1) = g :: List.removeAt' gs k' := by
      simp only [List.removeAt']
    rw [hrm]
    -- Slide `Rz q (θ₁+θ₂)` past `g`, merge inside `gs`, slide `Rz q θ₁` past `g`.
    have hslide₁ :
        unitaryDenote (Circuit.ofList (Gate.Rz q (θ₁ + θ₂.toReal) :: g :: List.removeAt' gs k'))
          = unitaryDenote
              (Circuit.ofList (g :: Gate.Rz q (θ₁ + θ₂.toReal) :: List.removeAt' gs k')) :=
      cons_rz_commute (θ₁ + θ₂.toReal) hcomm _
    have hmergeInner :
        unitaryDenote (Circuit.ofList (Gate.Rz q (θ₁ + θ₂.toReal) :: List.removeAt' gs k'))
          = unitaryDenote (Circuit.ofList (Gate.Rz q θ₁ :: gs)) :=
      ih q θ₁ k' partner θ₂ hk hget' hpart
    have hslide₂ :
        unitaryDenote (Circuit.ofList (g :: Gate.Rz q θ₁ :: gs))
          = unitaryDenote (Circuit.ofList (Gate.Rz q θ₁ :: g :: gs)) :=
      (cons_rz_commute θ₁ hcomm gs).symm
    -- Prepending `g` is a `qbind` on the left, preserved by congruence.
    have hcong :
        unitaryDenote (Circuit.ofList (g :: Gate.Rz q (θ₁ + θ₂.toReal) :: List.removeAt' gs k'))
          = unitaryDenote (Circuit.ofList (g :: Gate.Rz q θ₁ :: gs)) := by
      show QComp.qbind (denoteGateU g)
            (fun _ => unitaryDenote
              (Circuit.ofList (Gate.Rz q (θ₁ + θ₂.toReal) :: List.removeAt' gs k')))
         = QComp.qbind (denoteGateU g)
            (fun _ => unitaryDenote (Circuit.ofList (Gate.Rz q θ₁ :: gs)))
      rw [hmergeInner]
    rw [hslide₁, hcong, hslide₂]

/-- **The single merge step.** When `findMergePartner rest q = some k` finds a
later `Rz` on qubit `q` (at position `k`, reachable through gates all certified
to commute with `Rz q`), and that partner reads `(q, θ₂)`, sliding `Rz q θ₁`
down to position `k` and fusing it with the partner — i.e. replacing the head
pair with `Rz q (θ₁ + θ₂.toReal)` and deleting the partner — preserves the list
denotation. -/
theorem mergeStep_correctU :
    ∀ (rest : List (Gate n)) (q : Fin n) (θ₁ : ℝ) (k : ℕ) (partner : Gate n) (θ₂ : RzAngle),
      findMergePartner rest q = some k →
      List.getAt? rest k = some partner →
      rzAngle? partner = some (q, θ₂) →
      unitaryDenote (Circuit.ofList (Gate.Rz q (θ₁ + θ₂.toReal) :: List.removeAt' rest k))
        = unitaryDenote (Circuit.ofList (Gate.Rz q θ₁ :: rest)) := by
  intro rest
  induction rest with
  | nil => intro q θ₁ k partner θ₂ hfind _ _; simp [findMergePartner] at hfind
  | cons g gs ih =>
    intro q θ₁ k partner θ₂ hfind hget hpart
    rw [show findMergePartner (g :: gs) q
          = (match rzAngle? g with
             | some (q', _) =>
               if decide (q = q') then some 0
               else if gateCommutes (Gate.Rz q 0) g then findMergePartner gs q 1 else none
             | none =>
               if gateCommutes (Gate.Rz q 0) g then findMergePartner gs q 1 else none)
          from rfl] at hfind
    cases hrz : rzAngle? g with
    | some qθ =>
      obtain ⟨q', φ⟩ := qθ
      rw [hrz] at hfind
      simp only [] at hfind
      by_cases hqq : q = q'
      · -- partner is the immediate head `g`; k = 0, fuse directly.
        rw [ite_eq_left (decide_eq_true hqq)] at hfind
        simp only [Option.some.injEq] at hfind
        subst hfind
        simp only [List.getAt?, Option.some.injEq] at hget
        subst hget
        simp only [List.removeAt']
        have hgθ : denoteGateU g = denoteGateU (Gate.Rz q θ₂.toReal) := rzAngle?_denoteU hpart
        rw [show Circuit.ofList (Gate.Rz q θ₁ :: g :: gs)
              = Circuit.gate (Gate.Rz q θ₁) (Circuit.gate g (Circuit.ofList gs)) from rfl,
          show unitaryDenote (Circuit.gate (Gate.Rz q θ₁) (Circuit.gate g (Circuit.ofList gs)))
              = QComp.qbind (denoteGateU (Gate.Rz q θ₁))
                  (fun _ => QComp.qbind (denoteGateU g)
                    (fun _ => unitaryDenote (Circuit.ofList gs))) from rfl,
          hgθ]
        exact (unitaryDenote_mergeRz q θ₁ θ₂.toReal gs).symm
      · -- partner is deeper; slide `Rz q θ₁` past `g`, recurse on `gs`.
        rw [ite_eq_right (by simp [hqq])] at hfind
        by_cases hcomm : gateCommutes (Gate.Rz q 0) g = true
        · rw [ite_eq_left hcomm] at hfind
          exact mergeStep_slide ih hcomm hfind hget hpart
        · rw [ite_eq_right hcomm] at hfind; exact absurd hfind (by simp)
    | none =>
      rw [hrz] at hfind
      simp only [] at hfind
      by_cases hcomm : gateCommutes (Gate.Rz q 0) g = true
      · rw [ite_eq_left hcomm] at hfind
        exact mergeStep_slide ih hcomm hfind hget hpart
      · rw [ite_eq_right hcomm] at hfind; exact absurd hfind (by simp)

/-! ## The fuel recursion and the full pass -/

/-- The fuel-bounded merge recursion preserves `unitaryDenote`. -/
theorem mergeRotations_unitaryDenote :
    ∀ (gs : List (Gate n)) (fuel : ℕ),
      unitaryDenote (Circuit.ofList (mergeRotations gs fuel))
        = unitaryDenote (Circuit.ofList gs) := by
  intro gs fuel
  induction fuel generalizing gs with
  | zero => rfl
  | succ fuel' ih =>
    cases gs with
    | nil => rfl
    | cons g rest =>
      rw [show mergeRotations (g :: rest) (fuel' + 1)
            = (match rzAngle? g with
               | some (q, θ₁) =>
                 match findMergePartner rest q with
                 | some k =>
                   match List.getAt? rest k with
                   | some partner =>
                     match rzAngle? partner with
                     | some (_, θ₂) =>
                       match θ₁.add? θ₂ with
                       | some θ => θ.gate q :: mergeRotations (List.removeAt' rest k) fuel'
                       | none => g :: mergeRotations rest fuel'
                     | none => g :: mergeRotations rest fuel'
                   | none => g :: mergeRotations rest fuel'
                 | none => g :: mergeRotations rest fuel'
               | none => g :: mergeRotations rest fuel')
            from rfl]
      cases hrz : rzAngle? g with
      | none => simp only []; exact UnitarySound.unitaryDenote_cons_congr g (ih rest)
      | some qθ =>
        obtain ⟨q, θ₁⟩ := qθ
        simp only []
        cases hfind : findMergePartner rest q with
        | none => exact UnitarySound.unitaryDenote_cons_congr g (ih rest)
        | some k =>
          simp only []
          cases hgetk : List.getAt? rest k with
          | none => exact UnitarySound.unitaryDenote_cons_congr g (ih rest)
          | some partner =>
            simp only []
            cases hpz : rzAngle? partner with
            | none => exact UnitarySound.unitaryDenote_cons_congr g (ih rest)
            | some pθ =>
              obtain ⟨qp, θ₂⟩ := pθ
              simp only []
              cases hadd : θ₁.add? θ₂ with
              | none => exact UnitarySound.unitaryDenote_cons_congr g (ih rest)
              | some θ =>
              simp only []
              -- The partner found by `findMergePartner` at the match index is on
              -- qubit `q` (that is the exit condition `decide (q = q')`).
              have hqp : qp = q :=
                findMergePartner_partner_qubit q rest 0 k partner qp θ₂
                  hfind (by simpa using hgetk) hpz
              subst qp
              -- Replace `g` (the head Rz) with its explicit `Rz q θ₁` channel.
              have hgθ : denoteGateU g = denoteGateU (Gate.Rz q θ₁.toReal) :=
                rzAngle?_denoteU hrz
              -- The merged gate denotes the rotation by the sum of the angles.
              have hθ : denoteGateU (θ.gate q)
                  = denoteGateU (Gate.Rz q (θ₁.toReal + θ₂.toReal)) := by
                rw [RzAngle.gate_denoteU, RzAngle.toReal_of_add? hadd]
              -- Recurse on the shortened list, then apply the single merge step.
              calc unitaryDenote (Circuit.ofList
                      (θ.gate q :: mergeRotations (List.removeAt' rest k) fuel'))
                  = unitaryDenote (Circuit.ofList
                      (θ.gate q :: List.removeAt' rest k)) :=
                    UnitarySound.unitaryDenote_cons_congr _ (ih (List.removeAt' rest k))
                _ = unitaryDenote (Circuit.ofList
                      (Gate.Rz q (θ₁.toReal + θ₂.toReal) :: List.removeAt' rest k)) := by
                    change QComp.qbind (denoteGateU (θ.gate q))
                          (fun _ => unitaryDenote (Circuit.ofList (List.removeAt' rest k)))
                       = QComp.qbind (denoteGateU (Gate.Rz q (θ₁.toReal + θ₂.toReal)))
                          (fun _ => unitaryDenote (Circuit.ofList (List.removeAt' rest k)))
                    rw [hθ]
                _ = unitaryDenote (Circuit.ofList (Gate.Rz q θ₁.toReal :: rest)) :=
                    mergeStep_correctU rest q θ₁.toReal k partner θ₂ hfind hgetk hpz
                _ = unitaryDenote (Circuit.ofList (g :: rest)) := by
                    change QComp.qbind (denoteGateU (Gate.Rz q θ₁.toReal))
                          (fun _ => unitaryDenote (Circuit.ofList rest))
                       = QComp.qbind (denoteGateU g)
                          (fun _ => unitaryDenote (Circuit.ofList rest))
                    rw [hgθ]

/-- **The VOQC-style rotation merging pass preserves the unitary
semantics.**  `rotationMergingPass` flattens, normalizes the `Rz`-family,
merges compatible rotations, and rebuilds; the resulting circuit has the same
`unitaryDenote` (ρ ↦ UρU†) as the input. -/
theorem rotationMergingPass_unitaryDenote (c : Circuit n) :
    unitaryDenote (rotationMergingPass c) = unitaryDenote c := by
  show unitaryDenote (Circuit.ofList (mergeRotations (normalizeList (circuitToList c)))) = _
  rw [mergeRotations_unitaryDenote, normalizeList_unitaryDenote,
    UnitarySound.unitaryDenote_circuitToList]

/-- The rotation merging pass is `UnitaryCorrectQ`: it preserves the real
unitary-channel denotation. -/
theorem rotationMergingPass_unitaryCorrect :
    UnitaryCorrectQ (rotationMergingPass : Circuit n → Circuit n) :=
  fun c => (rotationMergingPass_unitaryDenote c).symm

end CatCrypt.Quantum.Optimization.RotMergeSound
