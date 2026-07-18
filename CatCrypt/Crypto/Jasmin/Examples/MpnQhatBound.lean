/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

set_option autoImplicit false

/-!
# The q̂ (q-hat) estimate and its at-most-2 correction — Knuth Theorem B

**Phase 3, the load-bearing NEW obligation for the Knuth Algorithm D division
kernel** (the multi-precision divide-and-conquer `mpn_divrem` / `mpn_tdiv_qr`).
The Euclidean *output* contract is already pinned down and proved in
`MpnDivRemSpec.lean` (`mpnDivRem_spec`); every other Knuth-D phase reuses the
already-verified `Mpn*Prototype` carry/borrow/limb-walk plumbing
(`submul_1`, `mpnAddN`) and the per-digit remainder-window invariant is the
radix-`2^64` lift of `longDivBits_spec`.

The single genuinely-new proof obligation — the one with *no* analogue in the
add/sub/mul plumbing — is the **correctness of the per-digit quotient estimate
`q̂` and its at-most-2 correction** (`mpn.cpp` `div_n` lines 244–249, WhyMP's
`wmpn_tdiv_qr`, s2n-bignum `bignum_divmod`).  The classical statement is
**Knuth TAOCP Vol. 2, §4.3.1, Theorem B**.

## Statement (base `b`, normalized divisor)

We divide a number by an `n`-limb divisor `v` that is **normalized**: its top
limb `v1 = v_{n-1}` satisfies `v1 ≥ b/2`.  At each quotient digit, with the
top-two divisor limbs `v1, v2` and a dividend window whose top-three limbs are
`u2, u1, u0`, write `U = u2·b + u1` (the top two limbs of the window).  The
estimate Knuth forms (using *only* the top divisor limb) is

> `q̂ = min(b-1, ⌊U / v1⌋)`.

Let `q = ⌊W / V⌋` be the *true* quotient digit, where `W` is the full dividend
window and `V = toNat v` the full divisor.  The loop invariant guarantees
`W < b·V` (the running remainder window stays `< V`), so `q ≤ b-1`.

This file proves, axiom-clean over `Nat`:

1. **`q ≤ q̂`** — the estimate never undershoots
   (`qhat_ge_q` / `qhat_ge_q_min`): from `v1 ≥ b/2` (normalization).
2. **`q̂ ≤ q + 2`** — it overshoots by at most 2
   (`qhat_le_q_add_two`): from `v1 ≥ b/2`.
3. **2-term refinement `q̂ ≤ q + 1`** — if the two-limb correction test
   `q̂·v2 ≤ r̂·b + u0` (with `r̂ = U - q̂·v1` the estimated remainder) *passes*,
   then `q̂ ≤ q + 1` (`qhat_le_q_add_one_of_test`).  The remaining off-by-one
   `q̂ = q+1` is fixed by the already-verified `mpnAddN` add-back step.

These are pure number-theory inequalities; the workhorses are `Nat.div_add_mod`
(the division identity `W = q·V + W%V`), `Nat.le_div_iff_mul_le`,
`Nat.lt_div_iff_mul_lt`, and `omega`/`nlinarith` after the division facts are
introduced.  This is the classic hard part of verified division (cf. WhyMP,
Knuth); we keep the statements faithful to Knuth's reduced top-limb form.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnQhatBound

/-! ## §1  The abstract Knuth-B configuration

We bundle the quantities that appear in Knuth's Theorem B into a configuration
of plain `Nat`s, with the hypotheses that hold at every quotient-digit step of
a normalized Knuth-D divide.  Working over abstract `Nat` (rather than a fixed
`b = 2^64`) keeps the number theory honest and reusable; the limb instantiation
`b := 2^64`, `v1 := v[n-1].toNat`, etc., is immediate.

Knuth reduces Theorem B to the *top two limbs* of the window and the *top one or
two limbs* of the divisor.  The connection between the full window/divisor
(`W`, `V`) and their top parts (`U`, `v1`) is captured by two scaling
relations: writing `M = b^(n-1)` for the place value of the top divisor limb,

* `v1 · M ≤ V`            — `v1` is the leading limb of `V` (so `V`'s top
                            digit is `v1`), hence `V ≥ v1·M`;
* `W < (U + 1) · M`       — `U` are the top two limbs of `W`, so the window is
                            strictly below `(U+1)·M` (the next value of the top
                            two-limb prefix).

These two are exactly what Knuth's proof uses; everything else is the floor
identity for `q` and `q̂`. -/

/-- A configuration of quantities at one quotient-digit step of normalized
    Knuth Algorithm D.  All fields are `Nat`; `b` is the limb base (`= 2^64`).

    * `b`  : the base, `b ≥ 2` (in fact `b = 2^64`).
    * `V`  : the full divisor `toNat v`, with leading limb `v1`.
    * `v1` : the top divisor limb `v_{n-1}` (the divisor is *normalized*:
             `v1 ≥ b/2`).
    * `M`  : the place value `b^(n-1)` of the top divisor limb (`M ≥ 1`).
    * `W`  : the full dividend window value.
    * `U`  : the top two limbs of the window, `U = u2·b + u1`.

    The carried hypotheses are the ones that hold at every step of a normalized
    divide; see the field docstrings. -/
structure KnuthBStep where
  /-- The limb base.  In the kernel `b = 2^64`. -/
  b  : Nat
  /-- The full divisor `toNat v`. -/
  V  : Nat
  /-- The top divisor limb `v_{n-1}`. -/
  v1 : Nat
  /-- The place value `b^(n-1)` of the top divisor limb. -/
  M  : Nat
  /-- The full dividend window. -/
  W  : Nat
  /-- The top two limbs of the window, `U = u2·b + u1`. -/
  U  : Nat
  /-- `b ≥ 2`. -/
  hb : 2 ≤ b
  /-- `M ≥ 1` (it is `b^(n-1)`). -/
  hM : 1 ≤ M
  /-- **Normalization**: the top divisor limb is `≥ b/2`. -/
  hnorm : b ≤ 2 * v1
  /-- `v1 < b`: the top limb is a base-`b` digit. -/
  hv1b : v1 < b
  /-- `v1 > 0`: nonzero leading limb (`v1 ≥ b/2 ≥ 1`). -/
  hv1 : 0 < v1
  /-- `V ≥ v1·M`: `v1` is the leading limb of `V`. -/
  hVlow : v1 * M ≤ V
  /-- `V < (v1+1)·M`: `v1` is *exactly* the leading limb of `V`
      (the rest of `V` is `< M`). -/
  hVhigh : V < (v1 + 1) * M
  /-- `W < (U+1)·M`: `U` are the top two limbs of the window. -/
  hWhigh : W < (U + 1) * M
  /-- `U·M ≤ W`: the top two limbs are a lower bound of the window. -/
  hWlow : U * M ≤ W
  /-- The loop invariant: the window is `< b·V` (running remainder `< V`),
      so the true quotient digit is a base-`b` digit. -/
  hWb : W < b * V

namespace KnuthBStep

variable (s : KnuthBStep)

/-- The **true** quotient digit `q = ⌊W / V⌋`. -/
def q : Nat := s.W / s.V

/-- The Knuth estimate from the top limbs: `qraw = ⌊U / v1⌋`. -/
def qraw : Nat := s.U / s.v1

/-- The **q̂ estimate**: `q̂ = min(b-1, ⌊U / v1⌋)`. -/
def qhat : Nat := min (s.b - 1) s.qraw

/-- `V > 0`: the divisor is positive (since `v1 ≥ b/2 ≥ 1` and `V ≥ v1·M`). -/
theorem V_pos : 0 < s.V := by
  have := s.hVlow
  have := s.hv1
  have := s.hM
  nlinarith [s.hVlow, s.hv1, s.hM]

/-- The true quotient digit is a base-`b` digit: `q ≤ b-1` (i.e. `q < b`).
    From the loop invariant `W < b·V`. -/
theorem q_lt_b : s.q < s.b := by
  unfold q
  rw [Nat.div_lt_iff_lt_mul s.V_pos]
  exact s.hWb

/-! ## §2  Basic floor facts for `q`, `qraw`, `qhat` -/

/-- `q·V ≤ W`: the true quotient times divisor is below the window
    (`Nat.div_mul_le_self`). -/
theorem q_mul_V_le : s.q * s.V ≤ s.W := Nat.div_mul_le_self s.W s.V

/-- `W < (q+1)·V`: the window is below the next multiple of the divisor.
    From `W = V·q + W%V` and `W%V < V`. -/
theorem W_lt_q_succ_mul_V : s.W < (s.q + 1) * s.V := by
  have hdm : s.V * (s.W / s.V) + s.W % s.V = s.W := Nat.div_add_mod s.W s.V
  have hmod : s.W % s.V < s.V := Nat.mod_lt _ s.V_pos
  show s.W < (s.W / s.V + 1) * s.V
  nlinarith [hdm, hmod]

/-- `qraw·v1 ≤ U` (`Nat.div_mul_le_self`). -/
theorem qraw_mul_v1_le : s.qraw * s.v1 ≤ s.U := Nat.div_mul_le_self s.U s.v1

/-- `q̂ ≤ qraw = ⌊U/v1⌋`. -/
theorem qhat_le_qraw : s.qhat ≤ s.qraw := min_le_right _ _

/-- `q̂ ≤ b-1`. -/
theorem qhat_le_b_pred : s.qhat ≤ s.b - 1 := min_le_left _ _

/-- The estimate satisfies `q̂·v1 ≤ U` (the defining floor inequality). -/
theorem qhat_mul_v1_le : s.qhat * s.v1 ≤ s.U :=
  le_trans (Nat.mul_le_mul_right _ s.qhat_le_qraw) s.qraw_mul_v1_le

/-! ## §3  Theorem B, claim (1): `q ≤ q̂` (the estimate never undershoots)

`q ≤ qraw` reduces (via `Nat.le_div_iff_mul_le`) to `q·v1 ≤ U`, which follows
from `q·v1·M ≤ q·V ≤ W < (U+1)·M` (using `v1·M ≤ V`, `W < (U+1)·M`) and `M ≥ 1`.
Since also `q ≤ b-1`, we get `q ≤ min(b-1, qraw) = q̂`. -/

/-- `q · v1 ≤ U`: the true digit times the top divisor limb is below the top
    two window limbs.  From `q·v1·M ≤ q·V ≤ W < (U+1)·M` and `M ≥ 1`. -/
theorem q_mul_v1_le_U : s.q * s.v1 ≤ s.U := by
  -- q·v1·M ≤ q·V ≤ W < (U+1)·M, then cancel M.
  have hqV : s.q * s.V ≤ s.W := s.q_mul_V_le
  have hWhigh : s.W < (s.U + 1) * s.M := s.hWhigh
  have hVlow : s.v1 * s.M ≤ s.V := s.hVlow
  have hM : 1 ≤ s.M := s.hM
  -- q·(v1·M) ≤ q·V
  have h1 : s.q * (s.v1 * s.M) ≤ s.q * s.V := Nat.mul_le_mul_left _ hVlow
  -- so q·v1·M < (U+1)·M
  have h2 : s.q * s.v1 * s.M < (s.U + 1) * s.M := by nlinarith [h1, hqV, hWhigh]
  -- cancel M
  have h3 : s.q * s.v1 < s.U + 1 := Nat.lt_of_mul_lt_mul_right h2
  omega

/-- **Knuth Theorem B, claim (1): `q ≤ qraw`** (the raw floor estimate never
    undershoots).  Equivalent to `q·v1 ≤ U`. -/
theorem q_le_qraw : s.q ≤ s.qraw := by
  rw [qraw, Nat.le_div_iff_mul_le s.hv1]
  exact s.q_mul_v1_le_U

/-- **Knuth Theorem B, claim (1): `q ≤ q̂`** — the estimate `q̂ = min(b-1, ⌊U/v1⌋)`
    never undershoots the true quotient digit.  Combines `q ≤ qraw` with the
    base-`b` digit bound `q ≤ b-1`. -/
theorem qhat_ge_q : s.q ≤ s.qhat := by
  rw [qhat, le_min_iff]
  refine ⟨?_, s.q_le_qraw⟩
  have := s.q_lt_b
  omega

/-! ## §4  Theorem B, claim (2): `q̂ ≤ q + 2` (overshoots by at most 2)

This is where **normalization** (`v1 ≥ b/2`) is essential.  Knuth's integer
argument:

* `q̂·v1·M ≤ U·M ≤ W`            (from `q̂·v1 ≤ U` and `U·M ≤ W`);
* `W < (q+1)·V < (q+1)·(v1+1)·M` (from `W < (q+1)·V` and `V < (v1+1)·M`);

so `q̂·v1·M < (q+1)·(v1+1)·M`; cancelling `M` gives
`q̂·v1 < (q+1)·(v1+1) = (q+1)·v1 + (q+1)`, i.e. `(q̂ - q - 1)·v1 < q+1`.
Now `q+1 ≤ b ≤ 2·v1` (digit bound + normalization), so if `q̂ ≥ q+3` then
`(q̂-q-1)·v1 ≥ 2·v1 ≥ q+1`, a contradiction.  Hence `q̂ ≤ q+2`. -/

/-- The pre-cancellation inequality `q̂·v1·M < (q+1)·(v1+1)·M`. -/
theorem qhat_chain : s.qhat * s.v1 * s.M < (s.q + 1) * (s.v1 + 1) * s.M := by
  -- q̂·v1·M ≤ U·M ≤ W
  have hA : s.qhat * s.v1 ≤ s.U := s.qhat_mul_v1_le
  have hUM : s.U * s.M ≤ s.W := s.hWlow
  have hlo : s.qhat * s.v1 * s.M ≤ s.W := by nlinarith [hA, hUM, s.hM]
  -- W < (q+1)·V < (q+1)·(v1+1)·M
  have hWq : s.W < (s.q + 1) * s.V := s.W_lt_q_succ_mul_V
  have hVh : s.V < (s.v1 + 1) * s.M := s.hVhigh
  have hhi : (s.q + 1) * s.V < (s.q + 1) * ((s.v1 + 1) * s.M) := by
    have := Nat.succ_pos s.q
    nlinarith [hVh, this]
  nlinarith [hlo, hWq, hhi]

/-- The cancelled inequality `q̂·v1 < (q+1)·(v1+1)`. -/
theorem qhat_lt_expand : s.qhat * s.v1 < (s.q + 1) * (s.v1 + 1) :=
  Nat.lt_of_mul_lt_mul_right s.qhat_chain

/-- **Knuth Theorem B, claim (2): `q̂ ≤ q + 2`** — the estimate overshoots by at
    most 2.  Requires normalization (`v1 ≥ b/2`).  Proof: from
    `q̂·v1 < (q+1)·(v1+1)` and `q+1 ≤ b ≤ 2·v1`, a `q̂ ≥ q+3` would force
    `(q̂-q-1)·v1 ≥ 2·v1 ≥ q+1`, contradicting the expanded bound. -/
theorem qhat_le_q_add_two : s.qhat ≤ s.q + 2 := by
  by_contra h
  rw [Nat.not_le] at h   -- h : q + 2 < q̂, i.e. q + 3 ≤ q̂
  have hexp : s.qhat * s.v1 < (s.q + 1) * (s.v1 + 1) := s.qhat_lt_expand
  -- q + 1 ≤ b  (q < b)
  have hqb : s.q + 1 ≤ s.b := s.q_lt_b
  -- b ≤ 2·v1  (normalization)
  have hnorm : s.b ≤ 2 * s.v1 := s.hnorm
  -- (q̂ - q - 1) ≥ 2  and  (q̂-q-1)·v1 ≤ q̂·v1 - (q+1)·v1 ... use nlinarith directly.
  nlinarith [hexp, hqb, hnorm, h, s.hv1]

end KnuthBStep

/-! ## §5  Theorem B, claim (3): the two-term refinement `q̂ ≤ q + 1`

Knuth's correction test uses the *second* divisor limb `v2 = v_{n-2}` and the
*third* window limb `u0`.  Write the estimated remainder
`r̂ = U - q̂·v1 = u2·b + u1 - q̂·v1` (well-defined as `q̂·v1 ≤ U`); the test is

> `q̂·v2 ≤ r̂·b + u0`.

When the test **passes** (Knuth's loop does *not* decrement), the estimate
overshoots by at most 1:  `q̂ ≤ q + 1`.

The refinement bundles the second-limb data on top of a `KnuthBStep`:

* `v2`  : the second divisor limb `v_{n-2}`, `v2 < b`;
* `u0`  : the third window limb;
* `Wh`  : the top-three-limb window value `Ŵ = u2·b² + u1·b + u0`;
* `V2`  : the top-two divisor limbs `V2 = v1·b + v2`;
* `M2`  : the place value `b^(n-2)` of the second divisor limb;

with the consistency relations (`U·b + u0 = Ŵ`, `V2·M2 ≤ V < (V2+1)·M2`,
`Ŵ·M2 ≤ W < (Ŵ+1)·M2`).  The decisive bound is `V2 ≥ v1·b ≥ b ≥ q+1`, so a
single `(q̂-q-1)·V2 < q+1 ≤ V2` step pins `q̂ ≤ q+1`. -/

/-- The two-term refinement configuration on top of a Knuth-B step. -/
structure KnuthBRefine extends KnuthBStep where
  /-- The second divisor limb `v_{n-2}`. -/
  v2 : Nat
  /-- The third window limb. -/
  u0 : Nat
  /-- The top-three-limb window `Ŵ = u2·b² + u1·b + u0`. -/
  Wh : Nat
  /-- The top-two divisor limbs `V2 = v1·b + v2`. -/
  V2 : Nat
  /-- The place value `b^(n-2)` of the second divisor limb. -/
  M2 : Nat
  /-- `M2 ≥ 1`. -/
  hM2 : 1 ≤ M2
  /-- `v2 < b`: it is a base-`b` digit. -/
  hv2b : v2 < b
  /-- `V2 = v1·b + v2` is the top-two-limb prefix value. -/
  hV2 : V2 = v1 * b + v2
  /-- `U·b + u0 = Ŵ`: the three-limb window extends the two-limb top `U`. -/
  hWh : U * b + u0 = Wh
  /-- `V2·M2 ≤ V`: `V2` is the leading two-limb prefix of `V`. -/
  hV2low : V2 * M2 ≤ V
  /-- `V < (V2+1)·M2`: the rest of `V` is `< M2`. -/
  hV2high : V < (V2 + 1) * M2
  /-- `Ŵ·M2 ≤ W`: `Ŵ` is the leading three-limb prefix of `W`. -/
  hWhlow : Wh * M2 ≤ W
  /-- `W < (Ŵ+1)·M2`: the rest of `W` is `< M2`. -/
  hWhhigh : W < (Wh + 1) * M2

namespace KnuthBRefine

variable (s : KnuthBRefine)

/-- The estimated remainder `r̂ = U - q̂·v1` (well-defined: `q̂·v1 ≤ U`). -/
def rhat : Nat := s.U - s.toKnuthBStep.qhat * s.v1

/-- `q̂·v1 + r̂ = U`: the estimated remainder reconstructs `U`. -/
theorem qhat_v1_add_rhat : s.toKnuthBStep.qhat * s.v1 + s.rhat = s.U := by
  unfold rhat
  have := s.toKnuthBStep.qhat_mul_v1_le
  omega

/-- **The test ⟹ `q̂·V2 ≤ Ŵ`.**  If `q̂·v2 ≤ r̂·b + u0`, then
    `q̂·(v1·b+v2) = q̂·v1·b + q̂·v2 ≤ q̂·v1·b + r̂·b + u0 = U·b + u0 = Ŵ`. -/
theorem qhat_mul_V2_le_Wh (htest : s.toKnuthBStep.qhat * s.v2 ≤ s.rhat * s.b + s.u0) :
    s.toKnuthBStep.qhat * s.V2 ≤ s.Wh := by
  have hrec : s.toKnuthBStep.qhat * s.v1 + s.rhat = s.U := s.qhat_v1_add_rhat
  have hWh : s.U * s.b + s.u0 = s.Wh := s.hWh
  rw [s.hV2]
  -- q̂·(v1·b + v2) = q̂·v1·b + q̂·v2
  --              ≤ q̂·v1·b + r̂·b + u0
  --              = (q̂·v1 + r̂)·b + u0 = U·b + u0 = Ŵ
  nlinarith [htest, hrec, hWh]

/-- The two-limb divisor prefix dominates the base: `V2 ≥ b`.
    From `V2 = v1·b + v2` and `v1 ≥ 1`. -/
theorem V2_ge_b : s.b ≤ s.V2 := by
  have hv1 : 0 < s.toKnuthBStep.v1 := s.toKnuthBStep.hv1
  rw [s.hV2]
  nlinarith [hv1, s.toKnuthBStep.hb]

/-- **Knuth Theorem B, claim (3): `q̂ ≤ q + 1`** when the two-term correction
    test passes.

    Proof: the test gives `q̂·V2 ≤ Ŵ`.  Multiplying by `M2` and chaining,
    `q̂·V2·M2 ≤ Ŵ·M2 ≤ W < (q+1)·V < (q+1)·(V2+1)·M2`, so (cancel `M2`)
    `q̂·V2 < (q+1)·(V2+1) = (q+1)·V2 + (q+1)`, i.e. `(q̂-q-1)·V2 < q+1`.
    Since `V2 ≥ b ≥ q+1`, a `q̂ ≥ q+2` would force `(q̂-q-1)·V2 ≥ V2 ≥ q+1`,
    a contradiction.  Hence `q̂ ≤ q+1`. -/
theorem qhat_le_q_add_one_of_test
    (htest : s.toKnuthBStep.qhat * s.v2 ≤ s.rhat * s.b + s.u0) :
    s.toKnuthBStep.qhat ≤ s.toKnuthBStep.q + 1 := by
  -- Abbreviations.
  set qh := s.toKnuthBStep.qhat with hqh
  set q  := s.toKnuthBStep.q with hq
  -- Test ⟹ q̂·V2 ≤ Ŵ.
  have hqV2 : qh * s.V2 ≤ s.Wh := s.qhat_mul_V2_le_Wh htest
  -- Scale by M2:  q̂·V2·M2 ≤ Ŵ·M2 ≤ W.
  have hWhlow : s.Wh * s.M2 ≤ s.W := s.hWhlow
  have hlo : qh * s.V2 * s.M2 ≤ s.W := by nlinarith [hqV2, hWhlow, s.hM2]
  -- W < (q+1)·V < (q+1)·(V2+1)·M2.
  have hWq : s.W < (q + 1) * s.V := s.toKnuthBStep.W_lt_q_succ_mul_V
  have hVh : s.V < (s.V2 + 1) * s.M2 := s.hV2high
  have hhi : (q + 1) * s.V < (q + 1) * ((s.V2 + 1) * s.M2) := by
    nlinarith [hVh, Nat.succ_pos q]
  have hchain : qh * s.V2 * s.M2 < (q + 1) * (s.V2 + 1) * s.M2 := by
    nlinarith [hlo, hWq, hhi]
  -- Cancel M2.
  have hcancel : qh * s.V2 < (q + 1) * (s.V2 + 1) := Nat.lt_of_mul_lt_mul_right hchain
  -- V2 ≥ b ≥ q+1.
  have hV2b : s.b ≤ s.V2 := s.V2_ge_b
  have hqb : q + 1 ≤ s.b := s.toKnuthBStep.q_lt_b
  -- Conclude q̂ ≤ q+1.
  by_contra h
  rw [Nat.not_le] at h   -- h : q + 1 < qh, i.e. q + 2 ≤ qh
  nlinarith [hcancel, hV2b, hqb, h]

end KnuthBRefine

/-! ## §6  Non-vacuity: a concrete inhabited configuration

The lemmas above would be vacuous if `KnuthBStep` / `KnuthBRefine` had
contradictory hypotheses.  Here is a concrete satisfying instance (base
`b = 10`, two-limb divisor `V = 50` normalized with `v1 = 5`, window
`W = 340`), witnessing that the hypothesis bundle is jointly satisfiable.
There `q = ⌊340/50⌋ = 6`, `qraw = ⌊34/5⌋ = 6`, `q̂ = min(9,6) = 6`, so
`q ≤ q̂ ≤ q+2` and the test holds with `q̂ ≤ q+1` — all consistent. -/

/-- A concrete satisfying `KnuthBStep` (base 10, `V = 50`, `W = 340`). -/
def exStep : KnuthBStep where
  b := 10; V := 50; v1 := 5; M := 10; W := 340; U := 34
  hb := by norm_num
  hM := by norm_num
  hnorm := by norm_num
  hv1b := by norm_num
  hv1 := by norm_num
  hVlow := by norm_num
  hVhigh := by norm_num
  hWhigh := by norm_num
  hWlow := by norm_num
  hWb := by norm_num

example : exStep.q = 6 := by native_decide
example : exStep.qraw = 6 := by native_decide
example : exStep.qhat = 6 := by native_decide
-- The three claims, instantiated and checked on the witness.
example : exStep.q ≤ exStep.qhat := exStep.qhat_ge_q
example : exStep.qhat ≤ exStep.q + 2 := exStep.qhat_le_q_add_two

/-- A concrete satisfying `KnuthBRefine` extending `exStep`
    (`v2 = 0`, `u0 = 0`, `Ŵ = 340`, `V2 = 50`, `M2 = 1`). -/
def exRefine : KnuthBRefine where
  toKnuthBStep := exStep
  v2 := 0; u0 := 0; Wh := 340; V2 := 50; M2 := 1
  hM2 := by norm_num
  hv2b := by norm_num [exStep]
  hV2 := by norm_num [exStep]
  hWh := by norm_num [exStep]
  hV2low := by norm_num [exStep]
  hV2high := by norm_num [exStep]
  hWhlow := by norm_num [exStep]
  hWhhigh := by norm_num [exStep]

example : exRefine.rhat = 4 := by native_decide
-- The correction test passes on the witness, and the refinement gives q̂ ≤ q+1.
example :
    exRefine.toKnuthBStep.qhat ≤ exRefine.toKnuthBStep.q + 1 :=
  exRefine.qhat_le_q_add_one_of_test (by native_decide)

end CatCrypt.Crypto.Jasmin.Examples.MpnQhatBound
