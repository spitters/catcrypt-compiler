/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

/-!
# Fusing the 4-limb Montgomery reduce over one `runBlock` trace

`MontReduceRunBlock.emitMontRedcStep_runBlock` proves that ONE emitted reduce
word-step's recombined `runBlock` value, divided by `2^64`, equals one
`Number.montgomeryReduce` step. `MontReduceRunBlock.emitMontRedc4_value` chains
FOUR such steps into `Cios4LimbProven.montRedc4` — but only *value-level*, under
four `hstep_i` hypotheses each asserting that step `i`'s recombined value is the
corresponding `montgomeryReduce` step. Those `hstep_i` are the inter-step
register-routing remainder: the four word steps run as a *single* `runBlock`
trace, threading step `i`'s shifted-down accumulator limbs into step `i+1`'s input
registers, is not yet a theorem.

This module attacks that fusion. It proves the FIRST genuine brick of the
inter-step routing — the **register-level shift-down** — and then states the full
fused obligation precisely, isolating exactly the two residuals that remain
(the physical carry-fold routing and the `emitCondSubP` canonicalisation anomaly).

## What is PROVEN here (new, register-level, no pin needed)

* **`valShift`** — the pure `valLimbs` identity behind the CIOS window slide: for a
  non-empty limb list `L` and a top carry word `r`,
  `(valLimbs L + (2^64)^|L| · r) / 2^64 = valLimbs (L.drop 1) + (2^64)^(|L|-1) · r`.
  The `/2^64` (the spec's `/R`) is realised *exactly* — floor division loses only
  the low limb `L[0]`, which the next window drops — with **no** Montgomery
  exactness/pin hypothesis (the low limb need not be zero for the *shifted-window
  value* to be correct, because the shifted window does not read `L[0]`).

* **`emitMontRedcStep_shifted_window`** ⭐ — the register-level shift of
  `emitMontRedcStep_runBlock`: running one emitted reduce word-step from a loaded
  state, the **shifted window** (the accumulator registers with the low limb
  dropped) together with the carry register `rcy` as its new top word reconstructs
  to `montgomeryReduce (valLimbs p) (2^64) n' (valLimbs T)`. I.e.
  `valLimbs ((accs.map post.get).drop 1) + (2^64)^(|p|-1) · (post.get rcy).toNat
     = montgomeryReduce …`.
  This is the value the physical window slide of `Curve4MontMulProvenEmit`'s
  `emitMontRedcStepAt` must land in registers `accNames[i+1 .. i+4]` after folding
  `rcy` into `accNames[i+4]`. Neither the four-limb `EmittedReduceWindowDischarge`
  nor the six-limb `EmittedReduceWindow6Discharge` exposes it — both assume the
  whole reduce-body register realiser (`ResReducedWindow` / `ResReducedWindow6`).

## What remains OPEN (the fused `montRedc4_runBlock`, stated below)

`montRedc4RunBlockGoal` states the target: running `emitMontRedc4Block` from a
window-loaded state leaves `montRedc4 (valLimbs p) n' T` reconstructed in the top
window `accNames[4..7]` (plus `rtop`). Discharging it from the instructions —
turning `emitMontRedc4_value`'s four `hstep_i` into theorems — needs, beyond the
shift brick proved here, the two residuals catalogued in `montRedc4RunBlock_gap`:

1. **The physical carry-fold routing** — that `emitMontRedcStepAt i`'s
   `add accNames[i+4], rcy` plus the `foldChain` `adc` cascade lands the
   shifted-window value (this module's `emitMontRedcStep_shifted_window`) into the
   next step's input registers with the inter-step carry propagated the whole way
   up into `rtop`, and that this composes over the four nested steps. Needs new
   `runBlock` reasoning for the `add`/`adc` fold cascade (no `valLimbs`-level
   `add`/`adc` lemma is in tree yet).

2. **The `emitCondSubP` anomaly** — the 10-round conditional-subtract
   canonicaliser (`Curve4MontMulProvenEmit.condSubRounds = 10`) that the emit's own
   comment flags as mis-canonicalising at one round (an `rtop`/borrow interaction).
   This is the canonicalisation step from the pre-condSub `< 2·p` value to the
   `< p` result registers `resNames`, and is the harder, KAT-gated residual.

The shift brick proved here is one of the two things needed for residual (1); the
`add`/`adc` fold cascade is the other.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
open CatCrypt.Crypto.Number

/-! ## 1. The pure `valLimbs` window-slide identity

The Montgomery reduce spec divides by `R = 2^64` (the word shift-down). In
registers this is realised by *dropping* the low accumulator limb and treating the
carry word as the new top limb of the shifted window. `valShift` is the arithmetic
that these agree: floor division by `2^64` removes exactly the low limb, which the
shifted window does not read — so the identity holds with **no** low-limb-zero /
Montgomery-pin hypothesis. -/

/-- **The window-slide value identity.** For a non-empty limb list `L` and a top
    carry word value `r`, the recombined `(L, r)` value divided by `2^64` equals
    the shifted window `L.drop 1` with `r` as its top limb:
    `(valLimbs L + (2^64)^|L| · r) / 2^64 = valLimbs (L.drop 1) + (2^64)^(|L|-1) · r`.
    Floor division loses only `L[0]` (the low limb `< 2^64`), which `L.drop 1`
    drops. No exactness hypothesis: the shifted window is correct as a *value*
    regardless of whether the dropped low limb is zero. -/
theorem valShift (L : List (BitVec 64)) (r : Nat) (hL : 0 < L.length) :
    (valLimbs L + (2 ^ 64) ^ L.length * r) / 2 ^ 64
      = valLimbs (L.drop 1) + (2 ^ 64) ^ (L.length - 1) * r := by
  cases L with
  | nil => simp at hL
  | cons w ws =>
    simp only [List.drop_succ_cons, List.drop_zero, valLimbs_cons, List.length_cons,
      Nat.add_sub_cancel]
    -- (2^64)^(n+1) = (2^64)^n * 2^64  (targeted, so the base 2^64 is untouched)
    have hp : (2 ^ 64 : Nat) ^ (ws.length + 1) = (2 ^ 64) ^ ws.length * 2 ^ 64 :=
      pow_succ (2 ^ 64) ws.length
    rw [hp]
    -- numerator = w + 2^64 * (valLimbs ws + (2^64)^n * r)
    have hfactor : w.toNat + 2 ^ 64 * valLimbs ws + (2 ^ 64) ^ ws.length * 2 ^ 64 * r
        = w.toNat + 2 ^ 64 * (valLimbs ws + (2 ^ 64) ^ ws.length * r) := by ring
    rw [hfactor, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ 64),
      Nat.div_eq_of_lt w.isLt, Nat.zero_add]

/-! ## 2. The register-level shifted-window theorem (the new brick)

`emitMontRedcStep_runBlock` gives the step's recombined value divided by `2^64`.
Post-composing with `valShift` gives the value held in the physical *shifted
window* — the accumulator registers minus their low limb, with `rcy` as the new
top word. This is exactly what the next word step reads as its input `T`. -/

/-- **The emitted reduce word-step lands `montgomeryReduce` in the shifted window.**
    Under the same loaded-state preconditions as
    `MontReduceRunBlock.emitMontRedcStep_runBlock`, plus `0 < p.length`, running one
    emitted reduce word-step leaves the shifted window — the accumulator registers
    `accs` with the low limb dropped, and the carry register `rcy` as the new top
    limb — reconstructing to one `Number.montgomeryReduce` step:

    `valLimbs ((accs.map post.get).drop 1) + (2^64)^(|p|-1) · (post.get rcy).toNat
       = montgomeryReduce (valLimbs p) (2^64) n' (valLimbs T)`,

    where `post = runBlock s (emitMontRedcStep …)`. This is the register-level
    realisation of the spec's `/R = /2^64` word shift-down: the divided value of
    `emitMontRedcStep_runBlock` IS the value the shifted window holds
    (`valShift`). It is the value `Curve4MontMulProvenEmit.emitMontRedcStepAt` must
    thread — after folding `rcy` into `accNames[i+4]` — into the next word step's
    input window. -/
theorem emitMontRedcStep_shifted_window
    (s : JState 64) (mReg t0Reg npReg dcy dhi dlo : String)
    (accs as : List String) (rcy rhi rlo : String)
    (p T : List (BitVec 64)) (nP : BitVec 64)
    (hAccLo : mReg ≠ dlo) (hAccHi : mReg ≠ dhi)
    (hDcyLo : dcy ≠ dlo) (hDcyHi : dcy ≠ dhi) (hDcyAcc : dcy ≠ mReg)
    (hDloHi : dlo ≠ dhi)
    (hAcc_pres : ∀ r ∈ accs, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hAs_pres : ∀ r ∈ as, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hRcy_pres : rcy ≠ mReg ∧ rcy ≠ dcy ∧ rcy ≠ dhi ∧ rcy ≠ dlo)
    (hlen : as.length = accs.length) (hplen : p.length = as.length)
    (htlen : T.length = accs.length)
    (hfresh : RowFresh accs as mReg rcy rhi rlo)
    (ht0 : s.get t0Reg = T.headD 0) (hnp : s.get npReg = nP)
    (hm0 : s.get mReg = 0) (hdcy0 : s.get dcy = 0)
    (has : as.map s.get = p) (haccs : accs.map s.get = T) (hrcy0 : s.get rcy = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hp0 : 0 < p.length) :
    valLimbs ((accs.map (runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
              accs as rcy rhi rlo)).get).drop 1)
        + (2 ^ 64) ^ (p.length - 1)
            * ((runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
                accs as rcy rhi rlo)).get rcy).toNat
      = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T) := by
  -- the proven per-step recombined value / 2^64 = one montgomeryReduce step
  have hstep := emitMontRedcStep_runBlock s mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo
    p T nP hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi hAcc_pres hAs_pres hRcy_pres
    hlen hplen htlen hfresh ht0 hnp hm0 hdcy0 has haccs hrcy0 hcf hof
  -- the output accumulator-register limb list
  set L := accs.map (runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
    accs as rcy rhi rlo)).get with hL
  set r := ((runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
    accs as rcy rhi rlo)).get rcy).toNat with hr
  -- |L| = |accs| = |p|
  have hLlen : L.length = p.length := by
    rw [hL, List.length_map, ← hlen, hplen]
  have hLpos : 0 < L.length := by rw [hLlen]; exact hp0
  -- rewrite the `/2^64` value via the pure window-slide identity
  have hshift := valShift L r hLpos
  rw [hLlen] at hshift
  -- hstep : (valLimbs L + (2^64)^|p| * r) / 2^64 = montgomeryReduce …
  rw [← hshift]
  exact hstep

/-! ## 3. The fused target and the remaining gap (OPEN)

The four word steps as a single `runBlock` trace land the full-radix reduction in
the top window. `montRedc4RunBlockGoal` states this precisely. It is **not** proved
here: `montRedc4RunBlock_gap` documents the two residuals between the shift brick
above and the goal. Both live entirely inside `Curve4MontMulProvenEmit`'s emitted
block, which this module treats read-only. -/

/-- **The fused 4-limb reduce goal (OPEN).** For a window-loaded start state — the
    input accumulator `T` in registers `accNames.take 4`, the modulus `p` in
    `pNames`, `n'` in `npName`, the upper window `accNames[4..7]` and `rtop` cleared,
    the scratch/carry registers cleared and flags clear — running the fused reduce
    block `emitMontRedc4Block` lands the four-fold Montgomery reduction
    `montRedc4 (valLimbs p) n' (valLimbs T)` reconstructed across the top window
    `accNames[4..7]` and the top-carry word `rtop`:

    `valLimbs ((Curve4MontMulProvenEmit.accNames.drop 4).map post.get)
       + (2^64)^4 · (post.get Curve4MontMulProvenEmit.rtopName).toNat
     = montRedc4 (valLimbs p) nP.toNat (valLimbs T)`,

    where `post = runBlock s emitMontRedc4Block`. Discharging this turns the four
    `hstep_i` of `MontReduceRunBlock.emitMontRedc4_value` into theorems. It is the
    pre-`emitCondSubP` reduce; the trailing conditional subtract then canonicalises
    into `resNames`. Stated as a `Prop`, not asserted — see `montRedc4RunBlock_gap`
    for what remains. -/
def montRedc4RunBlockGoal
    (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64) : Prop :=
  valLimbs ((Curve4MontMulProvenEmit.accNames.drop 4).map
        (runBlock s Curve4MontMulProvenEmit.emitMontRedc4Block).get)
      + (2 ^ 64) ^ 4
          * ((runBlock s Curve4MontMulProvenEmit.emitMontRedc4Block).get
              Curve4MontMulProvenEmit.rtopName).toNat
    = montRedc4 (valLimbs p) nP.toNat (valLimbs T)

/-- **The two residuals between the shift brick and `montRedc4RunBlockGoal`.**
    Recorded as documentation (a `True` marker whose docstring is the content) so a
    later session can pick up exactly where this walls, without re-auditing:

    1. **Carry-fold routing.** `emitMontRedcStep_shifted_window` (proved above) lands
       step `i`'s value in the shifted window `accs.drop 1` with the carry in `rcy`.
       `Curve4MontMulProvenEmit.emitMontRedcStepAt i` then executes
       `add accNames[i+4], rcy` followed by the `foldChain` `adc` cascade to place
       that carry into `accNames[i+4]` and propagate the resulting carry through
       `accNames[i+5..7]` into `rtop`. Proving that this cascade preserves the value
       — so that after step `i` the input window of step `i+1`
       (`accNames[i+1..i+4]`) reconstructs to `montRedc4`'s `i`-th partial — needs a
       `valLimbs`-level `runBlock` lemma for the `add`/`adc` fold (absent in tree),
       plus the four-fold fusion threading each step's freshness/preservation
       through the per-step `xor` clears. The shift brick is one half of this
       residual; the `add`/`adc` cascade lemma is the other.

    2. **`emitCondSubP` anomaly.** From the pre-condSub `< 2·p` window value, the
       10-round `Curve4MontMulProvenEmit.emitCondSubP` (its `condSubRounds = 10`)
       canonicalises into `resNames`. The emit's own comment flags a one-round
       `rtop`/borrow interaction that the iterated subtract works around; a value
       proof must reconcile that anomaly (or prove the pre-condSub goal and carry the
       canonicaliser as the single named residual). This is the harder, KAT-gated
       edge, matching the `ResReducedWindow` realiser that both
       `EmittedReduceWindowDischarge` and `EmittedReduceWindow6Discharge` assume.

    The six-limb sibling closes NEITHER residual: `Cios6LimbProven.montRedc6_correct`
    is a closed-form `Nat` composition (the six-word analogue of `montRedc4_correct`,
    a residue fact, not a `runBlock` theorem), and
    `EmittedReduceWindow6Discharge.ResReducedWindow6` is assumed verbatim like
    `ResReducedWindow`. So the six-limb case supplies no template for this fusion —
    the register-level shift brick above is genuinely new to both. -/
theorem montRedc4RunBlock_gap : True := trivial

end CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven
