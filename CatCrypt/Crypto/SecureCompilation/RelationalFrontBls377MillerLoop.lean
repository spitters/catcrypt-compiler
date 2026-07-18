/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377MillerLine
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377G2Scalar

/-!
# The `bls12_377` Miller-loop ACCUMULATION over the `Fp12` tower

`RelationalFrontBls377MillerLine` built the per-step pairing *line function*
value (`lineTangent` / `lineChord` valued in `Fp12_377`, embedded by `ofBase`),
the per-step Miller doubling update `millerStep f ℓ = f²·ℓ`, and the structural
sanity checks (the line vanishes at its anchor; `millerStep 1 ℓ = ℓ`).
`RelationalFrontBls377G2Scalar` developed the **double-and-add** schedule over a
bit list (`binaryLadder`, `bitsToNat`, the Horner / append recurrences) as a
left fold.

This module assembles the two into the **Miller loop**: the
doubling-and-add *accumulation* the optimal-Ate pairing runs over the loop
parameter's bit list.  At each step the loop squares-and-multiplies the running
`Fp12_377` value by the current tangent line (the doubling step
`f ← millerStep f ℓ_dbl = f²·ℓ_dbl`) and, when the loop-parameter bit is set,
multiplies in the current chord line (the addition step `f ← f · ℓ_add`).  The
point progression of the accumulator is modelled abstractly: rather than
re-deriving each step's anchor point, we fold over a list whose entries carry
the bit together with that step's two `Fp12_377` line values — exactly the
values the line functions of `RelationalFrontBls377MillerLine` produce.

## What this module defines and proves

* `MillerEntry` — one loop step's data: the loop-parameter `bit`, the doubling
  (tangent) line value `dbl`, and the addition (chord) line value `add`, all in
  `Fp12_377`.
* `millerStepEntry ξ₂ ξ₆ f e` — the per-step accumulator update:
  `f ← (f²·e.dbl)` then, iff `e.bit`, `· e.add`.  Built from
  `RelationalFrontBls377MillerLine.millerStep`.
* `millerLoop ξ₂ ξ₆ es` — the Miller loop as a left fold of `millerStepEntry`
  over the entry list `es`, seeded at the unit accumulator `1 : Fp12_377`.
* Structural / algebraic recurrences, all over the `Fp12_377` `CommRing`:
  - `millerLoop_nil` — the empty loop is `1`;
  - `millerLoop_append` — the loop over `es ++ fs` folds `fs` onto the loop over
    `es` (the fold recurrence), and its specialization
    `millerLoop_append_one` for one appended step;
  - `millerStepEntry_bit_false` / `_true` — the per-step update splits into the
    pure doubling step and the doubling-then-add step;
  - `millerLoop_trivialLines` — the loop over all-trivial (unit) line values is
    `1` (the homomorphism-flavoured degeneration: with every line `= 1` the
    accumulation collapses to the identity, independent of the bits);
  - `millerLoop_singleton` — a one-step loop is exactly `millerStepEntry 1`.

## Honesty boundary

This assembles the Miller-loop **computation** — the doubling-and-add line
accumulation over the `Fp12_377` tower — and proves its structural fold
recurrences and the all-trivial-line degeneration.  It does **not** prove
**pairing correctness**: that `millerLoop` followed by the final exponentiation
realizes a *bilinear, non-degenerate* pairing is the Weil/Tate divisor theory,
which Mathlib has no formalization of (no `WeilPairing` over a general curve),
exactly as `RelationalFrontBls377MillerLine` and the `AUCurvesPort` /
`PairingAxioms` layer defer it.  Nothing here claims the accumulated
`Fp12_377` value is the pairing; we deliver the well-defined accumulation and
its algebraic recurrences only.

0 sorries; no custom axioms.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. One loop step's data

A Miller-loop step over the loop-parameter bit `bit` carries two `Fp12_377` line
values: the tangent (doubling) line `dbl` always multiplied in via the
square-and-multiply, and the chord (addition) line `add` multiplied in only when
`bit` is set.  These are exactly the values `lineTangent` / `lineChord` produce
at the step's accumulator point; the point progression is modelled abstractly by
taking the line values as the data. -/

/-- **One Miller-loop step's data**: the loop-parameter `bit`, the doubling
    (tangent) line value `dbl`, and the addition (chord) line value `add`, all in
    `Fp12_377`.  The accumulator's point progression is abstracted into these
    precomputed line values. -/
structure MillerEntry where
  /-- The loop-parameter bit at this step: when `true`, the addition (chord) step
      runs in addition to the doubling step. -/
  bit : Bool
  /-- The tangent (doubling-step) line value at this step, in `Fp12_377`. -/
  dbl : Fp12_377
  /-- The chord (addition-step) line value at this step, in `Fp12_377`. -/
  add : Fp12_377

/-! ## 2. The per-step accumulator update

The square-and-multiply doubling step `f ← millerStep f e.dbl = f²·e.dbl`,
followed (iff `e.bit`) by the addition step `· e.add`. -/

/-- **The Miller per-step accumulator update.**  Run the doubling step
    `f ← millerStep f e.dbl = f²·e.dbl`, then — iff the loop-parameter bit
    `e.bit` is set — the addition step `f ← f · e.add`.  Over the `Fp12_377`
    `CommRing` at tower nonresidues `ξ₂, ξ₆`. -/
def millerStepEntry (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377)
    (e : MillerEntry) : Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  let f' := millerStep ξ₂ ξ₆ f e.dbl
  if e.bit then f' * e.add else f'

/-- **The doubling-only step** (`bit = false`): the per-step update is exactly the
    Miller doubling step `f ← f²·e.dbl`. -/
theorem millerStepEntry_bit_false (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377)
    (d a : Fp12_377) :
    millerStepEntry ξ₂ ξ₆ f ⟨false, d, a⟩ = millerStep ξ₂ ξ₆ f d := by
  simp [millerStepEntry]

/-- **The doubling-then-add step** (`bit = true`): the per-step update is the
    doubling step followed by multiplying in the chord line,
    `(f²·d) · a`. -/
theorem millerStepEntry_bit_true (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377)
    (d a : Fp12_377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    millerStepEntry ξ₂ ξ₆ f ⟨true, d, a⟩ = millerStep ξ₂ ξ₆ f d * a := by
  simp [millerStepEntry]

/-! ## 3. The Miller loop as a left fold

`millerLoop ξ₂ ξ₆ es` folds `millerStepEntry` over the entry list `es`, seeded at
the unit accumulator `1`.  This is the doubling-and-add accumulation; its
recurrences are definitional on the fold (mirroring `binaryLadder` of
`RelationalFrontBls377G2Scalar`). -/

/-- **The Miller loop.**  Fold the per-step accumulator update `millerStepEntry`
    over the entry list `es`, starting from the unit accumulator `1 : Fp12_377`.
    Each entry runs its doubling step and, iff its bit is set, its addition step —
    the standard MSB-first square-and-multiply Miller accumulation over the
    `Fp12_377` tower at nonresidues `ξ₂, ξ₆`. -/
def millerLoop (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (es : List MillerEntry) : Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  es.foldl (millerStepEntry ξ₂ ξ₆) 1

/-- **The empty Miller loop is the unit accumulator `1`.** -/
@[simp] theorem millerLoop_nil (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) :
    millerLoop ξ₂ ξ₆ [] = 1 := rfl

/-- **The Miller-loop fold recurrence over `++`.**  The loop over `es ++ fs`
    continues the loop over `es` by folding `fs` onto its accumulated value:
    `millerLoop (es ++ fs) = fs.foldl millerStepEntry (millerLoop es)`. -/
theorem millerLoop_append (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (es fs : List MillerEntry) :
    millerLoop ξ₂ ξ₆ (es ++ fs)
      = fs.foldl (millerStepEntry ξ₂ ξ₆) (millerLoop ξ₂ ξ₆ es) := by
  simp only [millerLoop, List.foldl_append]

/-- **The Miller-loop append-one recurrence.**  Appending one step `e` runs its
    per-step update on the loop's running value:
    `millerLoop (es ++ [e]) = millerStepEntry (millerLoop es) e`. -/
theorem millerLoop_append_one (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (es : List MillerEntry) (e : MillerEntry) :
    millerLoop ξ₂ ξ₆ (es ++ [e])
      = millerStepEntry ξ₂ ξ₆ (millerLoop ξ₂ ξ₆ es) e := by
  simp only [millerLoop, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **A one-step Miller loop** is exactly the per-step update on the unit
    accumulator: `millerLoop [e] = millerStepEntry 1 e`. -/
theorem millerLoop_singleton (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (e : MillerEntry) :
    millerLoop ξ₂ ξ₆ [e] = millerStepEntry ξ₂ ξ₆ 1 e := rfl

/-! ## 4. The all-trivial-line degeneration

With every line value `= 1`, each doubling step is `f ← f²` and each addition
step is `f ← f · 1 = f`; starting from `1`, the accumulator stays `1` for the
whole loop, independent of the bits.  This is the homomorphism-flavoured
structural fact: trivial input lines accumulate to the trivial pairing value. -/

/-- **The per-step update fixes `1` on trivial lines.**  When both line values are
    `1`, the step maps the unit accumulator to itself: `millerStepEntry 1 ⟨b,1,1⟩
    = 1` for either bit.  (`1²·1 = 1`, and the optional `· 1` is the identity.) -/
theorem millerStepEntry_one_trivial (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (b : Bool) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    millerStepEntry ξ₂ ξ₆ 1 ⟨b, 1, 1⟩ = 1 := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  have hstep : millerStep ξ₂ ξ₆ (1 : Fp12_377) 1 = 1 := by
    rw [millerStep_one_left]
  cases b with
  | false => rw [millerStepEntry_bit_false, hstep]
  | true => rw [millerStepEntry_bit_true, hstep, mul_one]

/-- **The Miller loop over all-trivial lines is `1`.**  If every entry's two line
    values are the unit `1` (only the bits may vary), the accumulation collapses
    to the trivial pairing value `1`, for any bit pattern.  This is the
    degeneration that holds without any pairing-correctness input: trivial lines
    contribute nothing. -/
theorem millerLoop_trivialLines (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (bs : List Bool) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    millerLoop ξ₂ ξ₆ (bs.map (fun b => (⟨b, 1, 1⟩ : MillerEntry))) = 1 := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs b ih =>
    rw [List.map_append, List.map_cons, List.map_nil, millerLoop_append_one, ih,
      millerStepEntry_one_trivial]

/-! ## 5. A worked example

A concrete two-step loop at tower nonresidues `ξ₂ = 5`, `ξ₆ = 2 + 3u` (the same
witnesses the `MillerLine` worked examples use), with trivial lines, exercising
`millerLoop_trivialLines`. -/

/-- **Worked example — a two-step trivial-line loop is `1`.**  A concrete
    instance of `millerLoop_trivialLines` over the bit list `[true, false]`. -/
theorem example_millerLoop_trivial :
    letI := Fp12_377.commRing 5 ⟨2, 3⟩
    millerLoop 5 ⟨2, 3⟩
        ([true, false].map (fun b => (⟨b, 1, 1⟩ : MillerEntry))) = 1 :=
  millerLoop_trivialLines 5 ⟨2, 3⟩ [true, false]

end CatCrypt.Crypto.SecureCompilation.RelationalFront
