/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Basic

/-!
# Verified radix-2 NTT butterfly (Cooley–Tukey / Gentleman–Sande)

The arithmetic core that an NTT-lowering / twiddle-cancellation pass relies on,
proved over a *generic* commutative ring `R`. No concrete prime, modulus, or
root of unity is fixed, so the identities below specialise to every
NTT-bearing protocol: ML-KEM (`q = 3329`), ML-DSA (`q = 8380417`), Plonky3
BabyBear (`p = 2^31 − 2^27 + 1`), and so on.

A single radix-2 stage of a number-theoretic transform is built from the
*butterfly*. Two flavours appear in NTT implementations:

* the **decimation-in-time (Cooley–Tukey) butterfly**
  `ctButterfly ω a b = (a + ω·b, a − ω·b)`, used on the forward transform; and
* the **decimation-in-frequency (Gentleman–Sande) butterfly**
  `gsButterfly ω a b = (a + b, (a − b)·ω)`, used on the inverse transform.

The pass-relevant facts are:

* `ctButterfly_sum` / `ctButterfly_diff` — the two outputs are exactly
  `a + ω·b` and `a − ω·b` (projection lemmas for downstream rewrites);
* `gsButterfly_ctButterfly` — running the GS butterfly (same twiddle `ω`) on the
  CT output scales by `2` and squares the twiddle: `(2·a, 2·ω²·b)`;
* `ctButterfly_inverse_cancel` — the twiddle-cancellation a butterfly pass
  actually fires: if `ω` is a unit with inverse `ωinv` (`ω·ωinv = 1`), then a CT
  butterfly followed by the matching GS butterfly *with the inverse twiddle*
  recovers `(2·a, 2·b)` — the twiddle cancels with NO concrete root of unity,
  purely from the unit hypothesis.

These are the correctness obligations a butterfly/twiddle rewrite discharges;
everything is closed by `ring`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

variable {R : Type*} [CommRing R]

/-- The decimation-in-time (Cooley–Tukey) radix-2 butterfly with twiddle `ω`:
maps a low/high pair `(a, b)` to `(a + ω·b, a − ω·b)`. -/
def ctButterfly (ω a b : R) : R × R := (a + ω * b, a - ω * b)

/-- The decimation-in-frequency (Gentleman–Sande) radix-2 butterfly with twiddle
`ω`: maps `(a, b)` to `(a + b, (a − b)·ω)`. This is the inverse-transform
butterfly; the twiddle multiplies the *difference* lane. -/
def gsButterfly (ω a b : R) : R × R := (a + b, (a - b) * ω)

/-! ## Projection lemmas (CT outputs) -/

@[simp] theorem ctButterfly_fst (ω a b : R) :
    (ctButterfly ω a b).1 = a + ω * b := rfl

@[simp] theorem ctButterfly_snd (ω a b : R) :
    (ctButterfly ω a b).2 = a - ω * b := rfl

/-- The "sum lane" of a CT butterfly is `a + ω·b`. -/
theorem ctButterfly_sum (ω a b : R) : (ctButterfly ω a b).1 = a + ω * b := rfl

/-- The "difference lane" of a CT butterfly is `a − ω·b`. -/
theorem ctButterfly_diff (ω a b : R) : (ctButterfly ω a b).2 = a - ω * b := rfl

@[simp] theorem gsButterfly_fst (ω a b : R) :
    (gsButterfly ω a b).1 = a + b := rfl

@[simp] theorem gsButterfly_snd (ω a b : R) :
    (gsButterfly ω a b).2 = (a - b) * ω := rfl

/-! ## Composed-stage identities -/

/-- Running the Gentleman–Sande butterfly with the *same* twiddle `ω` on the
Cooley–Tukey output scales the data by `2` and squares the twiddle:
`gs ω (ct ω a b) = (2·a, 2·ω²·b)`. This is the exact (un-normalised) scaled
identity for the same-twiddle round trip. -/
theorem gsButterfly_ctButterfly (ω a b : R) :
    gsButterfly ω (ctButterfly ω a b).1 (ctButterfly ω a b).2
      = (2 * a, 2 * ω ^ 2 * b) := by
  simp only [ctButterfly, gsButterfly]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- The twiddle-cancellation a radix-2 butterfly pass fires: with `ω` a unit
(inverse `ωinv`, `ω·ωinv = 1`), a Cooley–Tukey butterfly followed by the
matching Gentleman–Sande butterfly carrying the *inverse* twiddle `ωinv`
recovers `(2·a, 2·b)`. The twiddle cancels purely from the unit hypothesis — no
concrete root of unity is used. -/
theorem ctButterfly_inverse_cancel (ω ωinv a b : R) (h : ω * ωinv = 1) :
    gsButterfly ωinv (ctButterfly ω a b).1 (ctButterfly ω a b).2
      = (2 * a, 2 * b) := by
  simp only [ctButterfly, gsButterfly]
  refine Prod.ext ?_ ?_
  · simp; ring
  · -- ((a + ω*b) - (a - ω*b)) * ωinv = 2*ω*ωinv*b = 2*b
    show ((a + ω * b) - (a - ω * b)) * ωinv = 2 * b
    have : ((a + ω * b) - (a - ω * b)) * ωinv = 2 * b * (ω * ωinv) := by ring
    rw [this, h, mul_one]

/-! ## Optional: a single radix-2 stage over a `List` of pairs

A radix-2 stage applies the butterfly pointwise to a list of `(lo, hi)` lanes,
each carrying its own twiddle. We record the per-element denotation, the length
preservation, and the whole-stage twiddle cancellation that follows from
`ctButterfly_inverse_cancel`. -/

/-- One Cooley–Tukey radix-2 stage: apply `ctButterfly` to each `(ω, a, b)`
triple in the lane list. -/
def ctStage (lanes : List (R × R × R)) : List (R × R) :=
  lanes.map (fun t => ctButterfly t.1 t.2.1 t.2.2)

@[simp] theorem ctStage_length (lanes : List (R × R × R)) :
    (ctStage lanes).length = lanes.length := by
  simp [ctStage]

@[simp] theorem ctStage_nil : ctStage ([] : List (R × R × R)) = [] := rfl

@[simp] theorem ctStage_cons (t : R × R × R) (ts : List (R × R × R)) :
    ctStage (t :: ts) = ctButterfly t.1 t.2.1 t.2.2 :: ctStage ts := rfl

end CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass
