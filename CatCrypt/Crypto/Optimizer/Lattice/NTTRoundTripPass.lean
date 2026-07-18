/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

/-!
# Verified radix-2 NTT/INTT *stage* round-trip

The per-lane twiddle cancellation (`ctButterfly_inverse_cancel`) of
`NTTButterflyPass` is the arithmetic core; a number-theoretic transform fires it
across a whole *stage* — a list of independent radix-2 lanes processed in
parallel. This module lifts the per-lane identity to the list/stage level over a
generic commutative ring `R`, so it specialises to every NTT-bearing protocol
(ML-KEM `q = 3329`, ML-DSA `q = 8380417`, Plonky3 BabyBear, …) with no concrete
modulus or root of unity fixed.

A single forward (Cooley–Tukey, decimation-in-time) stage applies `ctButterfly`
to each `(ω, a, b)` lane; the matching inverse (Gentleman–Sande,
decimation-in-frequency) stage applies `gsButterfly` carrying the *inverse*
twiddle `ωinv` per lane. The round-trip result:

* `ctStageRT` / `gsStageRT` — the forward and inverse stages over a lane list
  that carries both `ω` and `ωinv` per lane;
* `gsStageRT_ctStageRT` — the whole-stage round trip: under the per-lane unit
  hypothesis `ω · ωinv = 1`, a forward stage followed by the inverse stage is the
  pointwise scaling `(a, b) ↦ (2·a, 2·b)`, i.e. the un-normalised identity. The
  twiddle cancels lane-by-lane purely from the unit hypotheses — no concrete root
  of unity is used.

The per-lane work is already discharged upstream by
`ctButterfly_inverse_cancel`; this module supplies the `List`/stage induction.
Everything is closed by a `List.map` induction plus the per-lane lemma.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTRoundTripPass

open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

variable {R : Type*} [CommRing R]

/-! ## Lane data

A round-trip lane carries the forward twiddle `ω`, its inverse `ωinv`, and the
low/high data pair `(a, b)`. We use the tuple shape `(ω, ωinv, a, b)`. -/

/-- The forward (Cooley–Tukey) twiddle of a round-trip lane `(ω, ωinv, a, b)`. -/
@[reducible] def laneTwiddle (lane : R × R × R × R) : R := lane.1

/-- The inverse (Gentleman–Sande) twiddle of a round-trip lane `(ω, ωinv, a, b)`. -/
@[reducible] def laneInvTwiddle (lane : R × R × R × R) : R := lane.2.1

/-- The low/high data pair `(a, b)` of a round-trip lane `(ω, ωinv, a, b)`. -/
@[reducible] def laneData (lane : R × R × R × R) : R × R := (lane.2.2.1, lane.2.2.2)

/-! ## Stages over a lane list -/

/-- One forward Cooley–Tukey radix-2 stage over a round-trip lane list: apply
`ctButterfly` to each lane's forward twiddle and data, discarding the inverse
twiddle (which the inverse stage will consume). -/
def ctStageRT (lanes : List (R × R × R × R)) : List (R × R) :=
  lanes.map (fun lane => ctButterfly lane.1 lane.2.2.1 lane.2.2.2)

/-- One inverse Gentleman–Sande radix-2 stage over a round-trip lane list, paired
with the forward-stage output: apply `gsButterfly` with each lane's *inverse*
twiddle `ωinv` to the corresponding `(sum, diff)` output of the forward stage. -/
def gsStageRT (lanes : List (R × R × R × R)) (mids : List (R × R)) : List (R × R) :=
  (lanes.zip mids).map (fun p => gsButterfly p.1.2.1 p.2.1 p.2.2)

@[simp] theorem ctStageRT_nil : ctStageRT ([] : List (R × R × R × R)) = [] := rfl

@[simp] theorem ctStageRT_cons (lane : R × R × R × R) (ls : List (R × R × R × R)) :
    ctStageRT (lane :: ls) =
      ctButterfly lane.1 lane.2.2.1 lane.2.2.2 :: ctStageRT ls := rfl

@[simp] theorem ctStageRT_length (lanes : List (R × R × R × R)) :
    (ctStageRT lanes).length = lanes.length := by
  simp [ctStageRT]

@[simp] theorem gsStageRT_nil_left (mids : List (R × R)) :
    gsStageRT ([] : List (R × R × R × R)) mids = [] := by
  simp [gsStageRT]

@[simp] theorem gsStageRT_cons
    (lane : R × R × R × R) (ls : List (R × R × R × R))
    (m : R × R) (ms : List (R × R)) :
    gsStageRT (lane :: ls) (m :: ms) =
      gsButterfly lane.2.1 m.1 m.2 :: gsStageRT ls ms := rfl

/-! ## Whole-stage round trip -/

/-- The full forward-then-inverse stage round trip on a single lane list: feeding
the forward stage's output straight into the inverse stage cancels every twiddle
(under the per-lane unit law `ω · ωinv = 1`) and leaves the un-normalised scaling
`(a, b) ↦ (2·a, 2·b)`. The hypothesis is supplied lane-by-lane via a
`List.Forall` predicate on the lanes; the proof is a `List.map` induction whose
inductive step is exactly `ctButterfly_inverse_cancel`. -/
theorem gsStageRT_ctStageRT (lanes : List (R × R × R × R))
    (h : ∀ lane ∈ lanes, lane.1 * lane.2.1 = 1) :
    gsStageRT lanes (ctStageRT lanes)
      = lanes.map (fun lane => (2 * lane.2.2.1, 2 * lane.2.2.2)) := by
  induction lanes with
  | nil => simp
  | cons lane ls ih =>
    have hlane : lane.1 * lane.2.1 = 1 := h lane (List.mem_cons_self ..)
    have hrest : ∀ l ∈ ls, l.1 * l.2.1 = 1 := fun l hl =>
      h l (List.mem_cons_of_mem _ hl)
    rw [ctStageRT_cons, gsStageRT_cons, ih hrest, List.map_cons]
    refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
    exact ctButterfly_inverse_cancel lane.1 lane.2.1 lane.2.2.1 lane.2.2.2 hlane

/-! ## Worked example: a 2-lane stage

A concrete two-lane round trip. With twiddles `ω₀, ω₁` (inverses `ω₀⁻¹, ω₁⁻¹`)
and data `(a₀, b₀), (a₁, b₁)`, the forward+inverse stage produces the pointwise
doubled data. The unit hypotheses are the only inputs; no root of unity is
fixed. -/
example (ω₀ ω₀inv a₀ b₀ ω₁ ω₁inv a₁ b₁ : R)
    (h₀ : ω₀ * ω₀inv = 1) (h₁ : ω₁ * ω₁inv = 1) :
    let lanes : List (R × R × R × R) :=
      [(ω₀, ω₀inv, a₀, b₀), (ω₁, ω₁inv, a₁, b₁)]
    gsStageRT lanes (ctStageRT lanes)
      = [(2 * a₀, 2 * b₀), (2 * a₁, 2 * b₁)] := by
  apply gsStageRT_ctStageRT
  intro lane hlane
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlane
  rcases hlane with rfl | rfl
  · exact h₀
  · exact h₁

end CatCrypt.Crypto.Optimizer.Lattice.NTTRoundTripPass
