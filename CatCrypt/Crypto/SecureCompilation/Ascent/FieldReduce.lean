/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
import CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven
import CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedcCarryFold
import CatCrypt.Crypto.Number.MontgomeryReduction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The modular-reduction value leaf for the ascent field vertical

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`)._

The field capstones (`CapstoneField.feSub_word_to_field`, `EcMultiLimbCapstone.feSub4_capstone`)
reach an *integer* value — a multi-precision difference `X − Y − b_in`, or a product over `ℤ`.
Matching a `ZMod p` field element then needs one more step: a **modular reduction** that maps
the wide integer down to the canonical residue. This module supplies that step as a pure value
leaf, with its correctness: the reduction computes the intended residue.

## The reduction: Montgomery (`montRedc`)

`montRedc p R pInv T = (T + m·p)/R` with `m = (T·pInv) mod R`, where `R` is the Montgomery
radix, `p` the modulus, and `pInv ≡ −p⁻¹ (mod R)` the precomputed constant (the standing
Montgomery relation `R ∣ (p·pInv + 1)`). Montgomery is chosen over Barrett/Solinas here because
its correctness is a **modular-congruence identity** provable by ring reasoning over `ℤ`/`ZMod`,
rather than a family of range inequalities.

The content is threefold:

* `montRedc_dvd` / `montRedc_mul_R` — the division is **exact**: `R ∣ (T + m·p)`, so
  `montRedc · R = T + m·p` over `ℤ`. This is the fact that makes Montgomery a reduction at all.
* `montRedc_spec` — the reduction output **is the intended residue**:
  `(montRedc p R pInv T : ZMod p) = (T : ZMod p) · (R : ZMod p)⁻¹`, i.e. it divides out the
  radix `R` modulo `p`. The unit-ness of `(R : ZMod p)` is *derived* from the Montgomery
  relation, not assumed separately.
* `montRedc_lt` / `montRedcNormalized_mem_Ico` — the standard Montgomery **range** property: for
  `0 ≤ T < R·p` the pre-normalized output lies in `[0, 2p)`, so a single conditional subtract
  (`montRedcNormalized`) lands it in the canonical range `[0, p)` without changing its residue.

## Connecting to the capstones

* `montRedcOfLimbs` / `montRedcOfLimbs_spec` — feed a little-endian limb list through the
  capstones' own recomposition `limbVal` (base `2^64`), matching how `feSub4_capstone` presents
  its value.
* `montRedc_of_diff` — the direct interface to the field-subtract capstones: the reduction of the
  difference `X − Y` denotes `((X : ZMod p) − (Y : ZMod p)) · (R : ZMod p)⁻¹`.

## The emitted reduce word-step as a `CorresJ`

`corresJ_montRedcStep` wraps one emitted Montgomery reduce word-step
(`X86Backend.MontReduceRunBlock.emitMontRedcStep`) as a `CorresJ` forward simulation over
`runBlock`. Its abstract state is two-phase: the `input` phase is the pristine loaded state (the
accumulator limbs `T` in registers, the modulus `p` and constant `n'` loaded, scratch and flags
cleared); the `output` phase is the shifted window (the accumulator with its low limb dropped and
the carry register as new top word). The abstract transition `faMontRedc` maps the input value to
`Number.montgomeryReduce (valLimbs p) (2^64) n' ⟦T⟧` recomposed across the output window, so the
`CorresJ` conclusion is the register-level shifted-window realisation
(`emitMontRedcStep_shifted_window`).

`montgomeryReduce_residue` gives that reduce target its residue: `Number.montgomeryReduce N R n' T`,
cast to `ZMod N`, equals `T · R⁻¹` — routed through the numeric bridge
`montgomeryReduce_natCast_eq_montRedc` (the `Nat` reduce cast to `ℤ` is the `ℤ` `montRedc`) and
`montRedc_spec`. Composing the two, `montRedcStep_runBlock_residue` reads the emitted step's
shifted-window `runBlock` value directly as the `ZMod (valLimbs p)` residue `⟦T⟧ · (2^64)⁻¹`.

The multi-word fusion — four word-steps as a single `runBlock` trace with the inter-step register
routing — is the residual recorded in `X86Backend.MontRedc4RunBlockProven.montRedc4RunBlock_gap`;
the two-phase state here refines one word-step and does not compose with itself across that routing.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven

/-! ## The Montgomery reduction function and its exactness -/

/-- Montgomery reduction (pre-conditional-subtract form). Given the modulus `p`, the Montgomery
radix `R`, the precomputed `pInv` satisfying `R ∣ (p·pInv + 1)` (i.e. `pInv ≡ −p⁻¹ mod R`), and
an input `T`, `montRedc` computes `(T + m·p)/R` where `m = (T·pInv) mod R`. Under the Montgomery
relation the numerator is divisible by `R`, so this is exact division. -/
def montRedc (p R pInv T : ℤ) : ℤ :=
  (T + ((T * pInv) % R) * p) / R

/-- **Exactness of the Montgomery division.** Under the Montgomery relation `R ∣ (p·pInv + 1)`,
the numerator `T + m·p` (with `m = (T·pInv) mod R`) is divisible by `R`. The witness is
`T·s − (T·pInv/R)·p` where `p·pInv + 1 = R·s`; the identity closes by `linear_combination`. -/
theorem montRedc_dvd (p R pInv T : ℤ) (hpInv : R ∣ (p * pInv + 1)) :
    R ∣ (T + ((T * pInv) % R) * p) := by
  obtain ⟨s, hs⟩ := hpInv
  refine ⟨T * s - (T * pInv / R) * p, ?_⟩
  have hemod : (T * pInv) % R = T * pInv - R * (T * pInv / R) := by
    rw [Int.emod_def]
  rw [hemod]
  linear_combination T * hs

/-- The exact-division rewrite: `montRedc p R pInv T · R = T + m·p`. -/
theorem montRedc_mul_R (p R pInv T : ℤ) (hpInv : R ∣ (p * pInv + 1)) :
    montRedc p R pInv T * R = T + ((T * pInv) % R) * p := by
  rw [montRedc]
  exact Int.ediv_mul_cancel (montRedc_dvd p R pInv T hpInv)

/-! ## The residue specification -/

/-- **Montgomery reduction computes the intended residue.** For a modulus `n` and a radix `R`
satisfying the Montgomery relation `R ∣ (n·pInv + 1)`, the reduction output equals `T · R⁻¹` in
`ZMod n`. The unit-ness of `(R : ZMod n)` is derived from the relation itself: the witness `s` of
`n·pInv + 1 = R·s` gives `R · s = 1` in `ZMod n`, so `R` is invertible mod `n` (no primality
needed — only coprimality of `R` and `n`, which the relation supplies). -/
theorem montRedc_spec (n : ℕ) (R pInv T : ℤ)
    (hpInv : R ∣ ((n : ℤ) * pInv + 1)) :
    ((montRedc (n : ℤ) R pInv T : ℤ) : ZMod n)
      = (T : ZMod n) * ((R : ZMod n))⁻¹ := by
  obtain ⟨s, hs⟩ := hpInv
  -- `(R : ZMod n)` is a unit, with inverse `s`, straight from the Montgomery relation.
  have hRunit : (R : ZMod n) * (s : ZMod n) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod n) hs
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_one, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, zero_add] at h
    exact h.symm
  have hunit : IsUnit (R : ZMod n) :=
    ⟨⟨(R : ZMod n), (s : ZMod n), hRunit, by rw [mul_comm]; exact hRunit⟩, rfl⟩
  -- The `ZMod`-native cancellation, matching the `ZMod.instInv` in the goal.
  have hRinv : (R : ZMod n) * ((R : ZMod n))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
  -- The exact-division identity, cast into `ZMod n`; the `m·n` term vanishes.
  have hmul : montRedc (n : ℤ) R pInv T * R = T + ((T * pInv) % R) * (n : ℤ) :=
    montRedc_mul_R (n : ℤ) R pInv T ⟨s, hs⟩
  have hcast : ((montRedc (n : ℤ) R pInv T : ℤ) : ZMod n) * (R : ZMod n) = (T : ZMod n) := by
    have h := congrArg (Int.cast : ℤ → ZMod n) hmul
    rw [Int.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, add_zero] at h
    exact h
  rw [← hcast, mul_assoc, hRinv, mul_one]

/-! ## The Montgomery range property and the conditional-subtract normalization -/

/-- **Montgomery range bound.** For `0 ≤ T < R·p` (the standing precondition of a Montgomery
multiply, `T < R·p` because the incoming product is `< p·p ≤ R·p`), the pre-normalized reduction
lies in `[0, 2p)`. The upper bound uses `0 ≤ m < R`. -/
theorem montRedc_lt (p R pInv T : ℤ) (hR : 0 < R) (hp : 0 < p)
    (hTR : T < R * p) :
    montRedc p R pInv T < 2 * p := by
  have hm0 : 0 ≤ (T * pInv) % R := Int.emod_nonneg _ (by exact ne_of_gt hR)
  have hmR : (T * pInv) % R < R := Int.emod_lt_of_pos _ hR
  have hnum : T + ((T * pInv) % R) * p < 2 * p * R := by
    have h1 : ((T * pInv) % R) * p ≤ (R - 1) * p := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hp)
      omega
    nlinarith [hp, hR, hTR]
  rw [montRedc, Int.ediv_lt_iff_lt_mul hR]
  linarith [hnum]

/-- The pre-normalized reduction is non-negative for a non-negative input (with `0 ≤ p`). -/
theorem montRedc_nonneg (p R pInv T : ℤ) (hR : 0 < R) (hp : 0 ≤ p) (hT0 : 0 ≤ T) :
    0 ≤ montRedc p R pInv T := by
  have hm0 : 0 ≤ (T * pInv) % R := Int.emod_nonneg _ (ne_of_gt hR)
  rw [montRedc]
  apply Int.ediv_nonneg _ (le_of_lt hR)
  have : 0 ≤ ((T * pInv) % R) * p := mul_nonneg hm0 hp
  linarith

/-- The canonical-range Montgomery reduction: one conditional subtract normalizes the
pre-reduction output into `[0, p)`. -/
def montRedcNormalized (p R pInv T : ℤ) : ℤ :=
  if p ≤ montRedc p R pInv T then montRedc p R pInv T - p else montRedc p R pInv T

/-- **The conditional subtract preserves the residue.** `montRedcNormalized` has the same
`ZMod n` value as `montRedc`, hence equals `T · R⁻¹` — subtracting the modulus `p = n` is `0`
in `ZMod n`. -/
theorem montRedcNormalized_spec (n : ℕ) (R pInv T : ℤ)
    (hpInv : R ∣ ((n : ℤ) * pInv + 1)) :
    ((montRedcNormalized (n : ℤ) R pInv T : ℤ) : ZMod n)
      = (T : ZMod n) * ((R : ZMod n))⁻¹ := by
  rw [montRedcNormalized]
  split
  · rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, sub_zero]
    exact montRedc_spec n R pInv T hpInv
  · exact montRedc_spec n R pInv T hpInv

/-- **Canonical range of the normalized reduction.** Under the Montgomery precondition
`0 ≤ T < R·p` (and `0 < p`), the normalized output lies in `[0, p)`. The lower bound in the
subtracting branch uses `p ≤ montRedc`; the upper bound uses `montRedc < 2p`. -/
theorem montRedcNormalized_mem_Ico (p R pInv T : ℤ) (hR : 0 < R) (hp : 0 < p)
    (hT0 : 0 ≤ T) (hTR : T < R * p) :
    0 ≤ montRedcNormalized p R pInv T ∧ montRedcNormalized p R pInv T < p := by
  have hlt := montRedc_lt p R pInv T hR hp hTR
  have hge := montRedc_nonneg p R pInv T hR (le_of_lt hp) hT0
  rw [montRedcNormalized]
  split <;> constructor <;> omega

/-! ## Connection to the capstones' limb representation -/

/-- The Montgomery reduction of a little-endian base-`2^64` limb list, recomposed through the
capstones' own `limbVal`. This is the shape `EcMultiLimbCapstone.feSub4_capstone` presents its
value in. -/
def montRedcOfLimbs (n : ℕ) (R pInv : ℤ) (Ts : List (BitVec 64)) : ℤ :=
  montRedc (n : ℤ) R pInv (limbVal Ts)

/-- **Limb-list residue spec.** The reduction of a limb list denotes the recomposed value
`⟦Ts⟧` divided by the radix in `ZMod n`. -/
theorem montRedcOfLimbs_spec (n : ℕ) (R pInv : ℤ)
    (Ts : List (BitVec 64)) (hpInv : R ∣ ((n : ℤ) * pInv + 1)) :
    ((montRedcOfLimbs n R pInv Ts : ℤ) : ZMod n)
      = ((limbVal Ts : ℕ) : ZMod n) * ((R : ZMod n))⁻¹ := by
  rw [montRedcOfLimbs, montRedc_spec n R pInv (limbVal Ts) hpInv, Int.cast_natCast]

/-- **The field-subtract interface.** The reduction of the difference `X − Y` that the field-sub
capstones reach denotes `((X : ZMod n) − (Y : ZMod n)) · R⁻¹` — the canonical `ZMod n` residue of
the Montgomery-domain difference. This is the value obligation the eventual `Corres`-wrapped
reduction leaf must agree with. -/
theorem montRedc_of_diff (n : ℕ) (R pInv X Y : ℤ)
    (hpInv : R ∣ ((n : ℤ) * pInv + 1)) :
    ((montRedc (n : ℤ) R pInv (X - Y) : ℤ) : ZMod n)
      = ((X : ZMod n) - (Y : ZMod n)) * ((R : ZMod n))⁻¹ := by
  rw [montRedc_spec n R pInv (X - Y) hpInv, Int.cast_sub]

/-! ## The `runBlock`-emitted Montgomery reduce word-step and its residue

The `runBlock` reduce (`X86Backend.MontReduceRunBlock.emitMontRedcStep`) computes over `Nat` via
`Number.montgomeryReduce`. `montgomeryReduce_natCast_eq_montRedc` identifies its `ℤ` cast with the
`ℤ` `montRedc` above, so `montRedc_spec` transfers to the emitted reduce; `corresJ_montRedcStep`
wraps one emitted word-step as a `CorresJ`, and `montRedcStep_runBlock_residue` reads its output as
the `ZMod` residue. -/

/-- The `Nat` Montgomery reduce `Number.montgomeryReduce`, cast to `ℤ`, is the `ℤ` `montRedc` on the
cast arguments: both compute `(T + ((T·n')%R)·N)/R`, and the nonnegative `Nat` floor division casts
to the `ℤ` `ediv`. -/
theorem montgomeryReduce_natCast_eq_montRedc (N R nP T : ℕ) :
    ((Number.montgomeryReduce N R nP T : ℕ) : ℤ)
      = montRedc (N : ℤ) (R : ℤ) (nP : ℤ) (T : ℤ) := by
  unfold Number.montgomeryReduce montRedc
  push_cast
  rfl

/-- **The `runBlock` reduce target computes the residue.** For a modulus `N` and radix `R`
satisfying the Montgomery relation `R ∣ (N·n' + 1)`, `Number.montgomeryReduce N R n' T` — the `Nat`
reduce the emitted word-step realises — equals `T · R⁻¹` in `ZMod N`. Routed through the cast
bridge `montgomeryReduce_natCast_eq_montRedc` and `montRedc_spec`. -/
theorem montgomeryReduce_residue (N R nP T : ℕ)
    (hpInv : (R : ℤ) ∣ ((N : ℤ) * (nP : ℤ) + 1)) :
    ((Number.montgomeryReduce N R nP T : ℕ) : ZMod N)
      = (T : ZMod N) * ((R : ZMod N))⁻¹ := by
  have hbridge := montgomeryReduce_natCast_eq_montRedc N R nP T
  have hspec := montRedc_spec N (R : ℤ) (nP : ℤ) (T : ℤ) hpInv
  have hcast : ((Number.montgomeryReduce N R nP T : ℕ) : ZMod N)
      = ((montRedc (N : ℤ) (R : ℤ) (nP : ℤ) (T : ℤ) : ℤ) : ZMod N) := by
    rw [← hbridge]; push_cast; rfl
  rw [hcast, hspec]; push_cast; rfl

/-- The two phases of the reduce word-step abstract state: the pristine loaded input, and the
shifted-window output the step produces. -/
inductive MontRedcPhase where
  | input
  | output
deriving DecidableEq

/-- The abstract state of the reduce word-step `CorresJ`: a phase tag, the register window
currently holding the value (little-endian), and the value it recomposes to. -/
structure AMontRedc where
  /-- Input or output phase. -/
  phase : MontRedcPhase
  /-- The value window (little-endian register names). -/
  win : List String
  /-- The recomposed value held in `win`. -/
  val : Nat

/-- The pristine loaded-input predicate on a `JState`: the accumulator's low limb `T₀` in `t0Reg`,
`n'` in `npReg`, the digit accumulator `mReg` and both carries `dcy`, `rcy` cleared, the modulus
limbs `p` in `as`, the accumulator limbs `T` in `accs`, and both flags clear. -/
def InputLoad (t0Reg npReg mReg dcy rcy : String) (accs as : List String)
    (p T : List (BitVec 64)) (nP : BitVec 64) (st : JState 64) : Prop :=
  st.get t0Reg = T.headD 0 ∧ st.get npReg = nP ∧ st.get mReg = 0 ∧ st.get dcy = 0 ∧
    as.map st.get = p ∧ accs.map st.get = T ∧ st.get rcy = 0 ∧
    st.flagB (·.cf) = false ∧ st.flagB (·.of) = false

/-- The state relation of the reduce word-step `CorresJ`: the value window `a.win` recomposes (via
`valLimbs`) to `a.val`, and in the `input` phase the window is `accs` and the state is loaded
(`InputLoad`). In the `output` phase only the value-window recomposition is asserted — the emitted
step does not pin the scratch registers or flags. -/
def SRmontRedc (t0Reg npReg mReg dcy rcy : String) (accs as : List String)
    (p T : List (BitVec 64)) (nP : BitVec 64) (st : JState 64) (a : AMontRedc) : Prop :=
  valLimbs (a.win.map st.get) = a.val ∧
    (a.phase = MontRedcPhase.input →
      a.win = accs ∧ InputLoad t0Reg npReg mReg dcy rcy accs as p T nP st)

/-- The abstract transition of the reduce word-step: to the `output` phase, the shifted window
`accs.drop 1 ++ [rcy]`, holding `Number.montgomeryReduce (valLimbs p) (2^64) n' a.val`. -/
def faMontRedc (rcy : String) (accs : List String)
    (p : List (BitVec 64)) (nP : BitVec 64) (a : AMontRedc) : AMontRedc :=
  { phase := MontRedcPhase.output,
    win := accs.drop 1 ++ [rcy],
    val := Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat a.val }

/-- **The emitted reduce word-step as a `CorresJ`.** Running one emitted Montgomery reduce
word-step (`emitMontRedcStep`) under `runBlock` refines the abstract transition `faMontRedc` through
`SRmontRedc`: from a pristine loaded input state (the `input` phase) the shifted output window
recomposes to `Number.montgomeryReduce (valLimbs p) (2^64) n' ⟦T⟧`. The value conclusion is the
register-level shift `emitMontRedcStep_shifted_window`; the `output`-phase image discharges the
relation's loaded-input arm vacuously. -/
theorem corresJ_montRedcStep
    (mReg t0Reg npReg dcy dhi dlo : String) (accs as : List String)
    (rcy rhi rlo : String) (p T : List (BitVec 64)) (nP : BitVec 64)
    (hAccLo : mReg ≠ dlo) (hAccHi : mReg ≠ dhi)
    (hDcyLo : dcy ≠ dlo) (hDcyHi : dcy ≠ dhi) (hDcyAcc : dcy ≠ mReg)
    (hDloHi : dlo ≠ dhi)
    (hAcc_pres : ∀ r ∈ accs, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hAs_pres : ∀ r ∈ as, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hRcy_pres : rcy ≠ mReg ∧ rcy ≠ dcy ∧ rcy ≠ dhi ∧ rcy ≠ dlo)
    (hlen : as.length = accs.length) (hplen : p.length = as.length)
    (htlen : T.length = accs.length)
    (hfresh : RowFresh accs as mReg rcy rhi rlo)
    (hp0 : 0 < p.length) :
    CorresJ (SRmontRedc t0Reg npReg mReg dcy rcy accs as p T nP)
      (fun a => a.phase = MontRedcPhase.input)
      (faMontRedc rcy accs p nP)
      (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo) := by
  intro st a hSR hP
  obtain ⟨hval, hin⟩ := hSR
  obtain ⟨hwin, hload⟩ := hin hP
  obtain ⟨ht0, hnp, hm0, hdcy0, has, haccs, hrcy0, hcf, hof⟩ := hload
  have haval : a.val = valLimbs T := by rw [← hval, hwin, haccs]
  set post := runBlock st (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
    accs as rcy rhi rlo) with hpost
  have hshift := emitMontRedcStep_shifted_window st mReg t0Reg npReg dcy dhi dlo
    accs as rcy rhi rlo p T nP hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi
    hAcc_pres hAs_pres hRcy_pres hlen hplen htlen hfresh ht0 hnp hm0 hdcy0
    has haccs hrcy0 hcf hof hp0
  rw [← hpost] at hshift
  refine ⟨?_, ?_⟩
  · show valLimbs ((faMontRedc rcy accs p nP a).win.map post.get)
      = (faMontRedc rcy accs p nP a).val
    simp only [faMontRedc]
    rw [haval]
    have hacclen : accs.length = p.length := by rw [← hlen, ← hplen]
    rw [List.map_append, valLimbs_append, List.map_drop]
    simp only [List.length_drop, List.length_map, List.map_cons, List.map_nil,
      valLimbs_cons, valLimbs_nil, mul_zero, add_zero]
    rw [hacclen]
    exact hshift
  · intro h
    simp only [faMontRedc] at h
    exact absurd h (by decide)

/-- **The emitted reduce word-step's `runBlock` value as a `ZMod` residue.** Under the Montgomery
relation `2^64 ∣ (⟦p⟧·n' + 1)`, the shifted-window value of one emitted reduce word-step — read out
of `runBlock` — cast to `ZMod (valLimbs p)`, equals `⟦T⟧ · (2^64)⁻¹`. Combines
`emitMontRedcStep_shifted_window` (the machine value) with `montgomeryReduce_residue` (the residue
of the reduce target). -/
theorem montRedcStep_runBlock_residue
    (st : JState 64) (mReg t0Reg npReg dcy dhi dlo : String) (accs as : List String)
    (rcy rhi rlo : String) (p T : List (BitVec 64)) (nP : BitVec 64)
    (hAccLo : mReg ≠ dlo) (hAccHi : mReg ≠ dhi)
    (hDcyLo : dcy ≠ dlo) (hDcyHi : dcy ≠ dhi) (hDcyAcc : dcy ≠ mReg)
    (hDloHi : dlo ≠ dhi)
    (hAcc_pres : ∀ r ∈ accs, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hAs_pres : ∀ r ∈ as, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hRcy_pres : rcy ≠ mReg ∧ rcy ≠ dcy ∧ rcy ≠ dhi ∧ rcy ≠ dlo)
    (hlen : as.length = accs.length) (hplen : p.length = as.length)
    (htlen : T.length = accs.length)
    (hfresh : RowFresh accs as mReg rcy rhi rlo)
    (ht0 : st.get t0Reg = T.headD 0) (hnp : st.get npReg = nP)
    (hm0 : st.get mReg = 0) (hdcy0 : st.get dcy = 0)
    (has : as.map st.get = p) (haccs : accs.map st.get = T) (hrcy0 : st.get rcy = 0)
    (hcf : st.flagB (·.cf) = false) (hof : st.flagB (·.of) = false)
    (hp0 : 0 < p.length)
    (hMont : ((2 ^ 64 : ℕ) : ℤ) ∣ ((valLimbs p : ℤ) * (nP.toNat : ℤ) + 1)) :
    ((valLimbs ((accs.map (runBlock st (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
              accs as rcy rhi rlo)).get).drop 1)
        + (2 ^ 64) ^ (p.length - 1)
            * ((runBlock st (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
                accs as rcy rhi rlo)).get rcy).toNat : ℕ) : ZMod (valLimbs p))
      = (valLimbs T : ZMod (valLimbs p)) * (((2 ^ 64 : ℕ)) : ZMod (valLimbs p))⁻¹ := by
  have hshift := emitMontRedcStep_shifted_window st mReg t0Reg npReg dcy dhi dlo
    accs as rcy rhi rlo p T nP hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi
    hAcc_pres hAs_pres hRcy_pres hlen hplen htlen hfresh ht0 hnp hm0 hdcy0
    has haccs hrcy0 hcf hof hp0
  rw [hshift]
  exact montgomeryReduce_residue (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T) hMont

/-! ## The fused four-word reduce's residue and its block `CorresJ`

`montRedc4_residue` gives the full-radix reduction `Cios4LimbProven.montRedc4` — the
four chained word-steps — its `ZMod` residue `⟦T⟧ · (2^256)⁻¹`, the four-word analogue
of `montRedc_spec`. `corresJ_montRedc4Block` wraps the whole emitted reduce block
`Curve4MontMulProvenEmit.emitMontRedc4Block` as a `CorresJ` whose abstract transition
lands `montRedc4` reconstructed across the top window `accNames[4..7]` and `rtop`; its
routing hypothesis is exactly `MontRedc4RunBlockProven.montRedc4RunBlockGoal`, the
residual recorded in `montRedc4RunBlock_gap`. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven in
/-- **The fused four-word reduction computes the residue.** For a modulus `N`, the
Montgomery constant `nP` with `(N·nP) mod 2^64 = 2^64 − 1`, and input `T < 2^64·N`,
the four-fold reduction `montRedc4 N nP T` — four chained `montgomeryReduce` word-steps,
a reduction at radix `2^256` — cast to `ZMod N`, equals `T · (2^256)⁻¹`. The unit-ness of
`(2^256 : ZMod N)` is derived from the Montgomery relation (`2^64` is a unit, so is its
fourth power); the congruence `montRedc4 N nP T · 2^256 ≡ T (mod N)` is
`Cios4LimbProven.montRedc4_correct`. The four-word analogue of `montRedc_spec`. -/
theorem montRedc4_residue (N nP T : ℕ) (hN : 0 < N)
    (hnp64 : (N * nP) % 2 ^ 64 = 2 ^ 64 - 1)
    (hT : T < 2 ^ 64 * N) :
    ((montRedc4 N nP T : ℕ) : ZMod N)
      = (T : ZMod N) * (((2 ^ 256 : ℕ)) : ZMod N)⁻¹ := by
  -- `2^64` is a unit in `ZMod N`, from the Montgomery relation `2^64 ∣ (N·nP + 1)`.
  have h0 : (N * nP + 1) % 2 ^ 64 = 0 := by
    rw [Nat.add_mod, hnp64, Nat.mod_eq_of_lt (by norm_num : (1 : ℕ) < 2 ^ 64),
      Nat.sub_add_cancel (by norm_num : (1 : ℕ) ≤ 2 ^ 64), Nat.mod_self]
  obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero h0
  have hunit64 : IsUnit (((2 ^ 64 : ℕ)) : ZMod N) := by
    have hcast : ((N * nP + 1 : ℕ) : ZMod N) = ((2 ^ 64 * u : ℕ) : ZMod N) := by rw [hu]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self, zero_mul, zero_add,
      Nat.cast_mul] at hcast
    exact ⟨⟨_, (u : ZMod N), hcast.symm, by rw [mul_comm]; exact hcast.symm⟩, rfl⟩
  -- hence so is `2^256 = (2^64)^4`.
  have hpow : (((2 ^ 256 : ℕ)) : ZMod N) = (((2 ^ 64 : ℕ)) : ZMod N) ^ 4 := by
    push_cast; ring
  have hunit256 : IsUnit (((2 ^ 256 : ℕ)) : ZMod N) := by rw [hpow]; exact hunit64.pow 4
  have hRinv : (((2 ^ 256 : ℕ)) : ZMod N) * (((2 ^ 256 : ℕ)) : ZMod N)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit256
  -- the exact congruence `montRedc4 · 2^256 ≡ T (mod N)`, cast into `ZMod N`.
  obtain ⟨_, hcong⟩ := montRedc4_correct N nP T hN hnp64 hT
  have hmul : ((montRedc4 N nP T : ℕ) : ZMod N) * (((2 ^ 256 : ℕ)) : ZMod N)
      = (T : ZMod N) := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcong
    rwa [Nat.cast_mul] at h
  calc ((montRedc4 N nP T : ℕ) : ZMod N)
      = ((montRedc4 N nP T : ℕ) : ZMod N)
          * ((((2 ^ 256 : ℕ)) : ZMod N) * (((2 ^ 256 : ℕ)) : ZMod N)⁻¹) := by
        rw [hRinv, mul_one]
    _ = (((montRedc4 N nP T : ℕ) : ZMod N) * (((2 ^ 256 : ℕ)) : ZMod N))
          * (((2 ^ 256 : ℕ)) : ZMod N)⁻¹ := by ring
    _ = (T : ZMod N) * (((2 ^ 256 : ℕ)) : ZMod N)⁻¹ := by rw [hmul]

/-! ## The per-step running value of one fused reduce word-step

`montRedcStep_fold_running_value` glues the three proven value bricks over a single
`runBlock` of one fused reduce word-step — the three entry `xor` clears, the emitted
reduce word-step, and the carry-fold cascade. It is the register-level realisation of
one `montgomeryReduce` word-step acting on the *whole* running value (the low window
`accs` and the higher words held in `D`, including the top-carry word). The pieces:

* `MontRedc4RunBlockProven.xorClears3` — the three `xor` clears re-establish
  `m = dcy = rcy = 0`, `CF = OF = 0`, preserving the step's inputs;
* `MontRedc4RunBlockProven.emitMontRedcStep_shifted_window` — the shift: the emitted
  step lands `montgomeryReduce (valLimbs p) (2^64) n' (valLimbs T)` in the shifted
  window `accs.drop 1` with the carry in `rcy`;
* `MontRedcCarryFold.foldCascade_value` — the `add`/`adc` cascade folds `rcy` into the
  higher-word registers `D`;
* `MontRedc4RunBlockProven.montgomeryReduce_window_split` — the higher words ride
  through one reduce step down-shifted by one word.

The step's inputs survive the clears (`ht0m`…`hacc_clr`), and the higher-word registers
`D` survive both the clears and the step (`hDpres`), so their old value re-enters the
`montgomeryReduce` argument via the window split. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedcCarryFold in
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA in
open CatCrypt.Crypto.Number in
/-- **One fused reduce word-step advances the running value by one `montgomeryReduce`
step.** For a four-limb window `accs` holding `T`, the modulus limbs `p` in `as`, `n'`
in `npReg`, and the higher running words (with the top-carry word) held in registers
`D` (value `Higher`), running the three entry `xor` clears, the emitted reduce word-step,
and the carry-fold cascade `foldCascade D rcy` leaves the new running window
`accs.drop 1 ++ D` (with the final `CF` weighted at the top) reconstructing to
`montgomeryReduce (valLimbs p) (2^64) n' (valLimbs T + (2^64)^4 · valLimbs Higher)`. -/
theorem montRedcStep_fold_running_value
    (s : JState 64) (mReg t0Reg npReg dcy dhi dlo : String)
    (accs as : List String) (rcy rhi rlo : String) (D : List String)
    (p T Higher : List (BitVec 64)) (nP : BitVec 64)
    (hAccLo : mReg ≠ dlo) (hAccHi : mReg ≠ dhi)
    (hDcyLo : dcy ≠ dlo) (hDcyHi : dcy ≠ dhi) (hDcyAcc : dcy ≠ mReg)
    (hDloHi : dlo ≠ dhi)
    (hAcc_pres : ∀ r ∈ accs, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hAs_pres : ∀ r ∈ as, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hRcy_pres : rcy ≠ mReg ∧ rcy ≠ dcy ∧ rcy ≠ dhi ∧ rcy ≠ dlo)
    (hfresh : RowFresh accs as mReg rcy rhi rlo)
    (hlen : as.length = accs.length) (hplen4 : p.length = 4) (haccs4 : accs.length = 4)
    (htlen : T.length = accs.length)
    (ht0m : t0Reg ≠ mReg) (ht0d : t0Reg ≠ dcy) (ht0r : t0Reg ≠ rcy)
    (hnpm : npReg ≠ mReg) (hnpd : npReg ≠ dcy) (hnpr : npReg ≠ rcy)
    (has_clr : ∀ r ∈ as, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ rcy)
    (hacc_clr : ∀ r ∈ accs, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ rcy)
    (ht0 : s.get t0Reg = T.headD 0) (hnp : s.get npReg = nP)
    (has : as.map s.get = p) (haccs : accs.map s.get = T)
    (hDlen : D.length = Higher.length) (hDnd : D.Nodup) (hHpos : 0 < Higher.length)
    (hDrcy : ∀ d ∈ D, rcy ≠ d)
    (hDacc : ∀ d ∈ D, ∀ q ∈ accs, d ≠ q)
    (hDpres : ∀ d ∈ D, d ≠ mReg ∧ d ≠ dcy ∧ d ≠ rcy ∧ d ≠ dhi ∧ d ≠ dlo
      ∧ d ≠ rhi ∧ d ≠ rlo)
    (hDmap : D.map s.get = Higher) :
    valLimbs ((accs.drop 1 ++ D).map (runBlock s
        ([JInstr.xor_ mReg (.reg mReg), JInstr.xor_ dcy (.reg dcy),
            JInstr.xor_ rcy (.reg rcy)]
          ++ emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo
          ++ foldCascade D rcy)).get)
      + (2 ^ 64) ^ (accs.length - 1 + D.length)
          * (if (runBlock s
              ([JInstr.xor_ mReg (.reg mReg), JInstr.xor_ dcy (.reg dcy),
                  JInstr.xor_ rcy (.reg rcy)]
                ++ emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo
                ++ foldCascade D rcy)).flagB (·.cf) then 1 else 0)
    = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
        (valLimbs T + (2 ^ 64) ^ 4 * valLimbs Higher) := by
  -- a general fold-cascade preservation fact for registers outside `D`
  have foldpres : ∀ (Dl : List String) (r : String) (t : JState 64),
      (∀ d ∈ Dl, r ≠ d) → (runBlock t (foldCascade Dl rcy)).get r = t.get r := by
    intro Dl
    cases Dl with
    | nil => intro r t _; simp [foldCascade]
    | cons d0 tl =>
      intro r t hr
      rw [foldCascade, runBlock_cons,
        adcImm0Chain_preserves tl r _ (fun q hq => hr q (List.mem_cons_of_mem _ hq)),
        emit_add_other _ d0 rcy r (hr d0 List.mem_cons_self)]
  -- split the run block into the three clears, the step, and the fold
  rw [runBlock_append, runBlock_append]
  set s1 := runBlock s [JInstr.xor_ mReg (.reg mReg), JInstr.xor_ dcy (.reg dcy),
    JInstr.xor_ rcy (.reg rcy)] with hs1def
  set s2 := runBlock s1 (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo)
    with hs2def
  set post := runBlock s2 (foldCascade D rcy) with hpostdef
  -- the three entry clears
  have hxc := xorClears3 s mReg dcy rcy hDcyAcc.symm hRcy_pres.1.symm hRcy_pres.2.1.symm
  rw [← hs1def] at hxc
  obtain ⟨hm0', hdcy0', hrcy0', hcf', hof', hpres'⟩ := hxc
  -- the step's inputs survive the clears
  have ht0' : s1.get t0Reg = T.headD 0 := by rw [hpres' t0Reg ht0m ht0d ht0r, ht0]
  have hnp' : s1.get npReg = nP := by rw [hpres' npReg hnpm hnpd hnpr, hnp]
  have has' : as.map s1.get = p := by
    rw [← has]; apply List.map_congr_left; intro r hr
    obtain ⟨h1, h2, h3⟩ := has_clr r hr; exact hpres' r h1 h2 h3
  have haccs' : accs.map s1.get = T := by
    rw [← haccs]; apply List.map_congr_left; intro r hr
    obtain ⟨h1, h2, h3⟩ := hacc_clr r hr; exact hpres' r h1 h2 h3
  have hDmap1 : D.map s1.get = Higher := by
    rw [← hDmap]; apply List.map_congr_left; intro d hd
    obtain ⟨hm, hdc, hrc, _, _, _, _⟩ := hDpres d hd; exact hpres' d hm hdc hrc
  -- derived length facts
  have hplen : p.length = as.length := by rw [hplen4, hlen, haccs4]
  have hp0 : 0 < p.length := by rw [hplen4]; norm_num
  -- the shift brick on the post-clears state
  have hshift := emitMontRedcStep_shifted_window s1 mReg t0Reg npReg dcy dhi dlo accs as rcy
    rhi rlo p T nP hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi hAcc_pres hAs_pres hRcy_pres
    hlen hplen htlen hfresh ht0' hnp' hm0' hdcy0' has' haccs' hrcy0' hcf' hof' hp0
  rw [← hs2def] at hshift
  -- the step ends with CF = 0
  have hstepcf := emitMontRedcStep_cf s1 mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo
    p T nP hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi hAcc_pres hAs_pres hRcy_pres
    hlen hplen htlen hfresh ht0' hnp' hm0' hdcy0' has' haccs' hrcy0' hcf' hof'
  rw [← hs2def] at hstepcf
  -- `D` survives the step, so it still holds `Higher` at the fold's entry
  have hDmap2 : D.map s2.get = Higher := by
    rw [← hDmap1]; apply List.map_congr_left; intro d hd
    obtain ⟨hm, hdc, hrc, hdh, hdl, hrh, hrl⟩ := hDpres d hd
    rw [hs2def]
    exact emitMontRedcStep_preserves s1 mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo
      d (hDacc d hd) hm hdc hdh hdl hrc hrh hrl
  -- the carry-fold cascade value
  have hfoldv := foldCascade_value D rcy Higher s2 hDlen hDnd hDrcy hDmap2 hstepcf hHpos
  rw [← hpostdef] at hfoldv
  -- `accs.drop 1` survives the fold
  have haccdrop : (accs.drop 1).map post.get = (accs.drop 1).map s2.get := by
    apply List.map_congr_left; intro r hr
    have hrmem : r ∈ accs := List.mem_of_mem_drop hr
    rw [hpostdef]; exact foldpres D r s2 (fun d hd => (hDacc d hd r hrmem).symm)
  -- concrete exponents
  have he3a : accs.length - 1 = 3 := by rw [haccs4]
  have he3p : p.length - 1 = 3 := by rw [hplen4]
  rw [he3p] at hshift
  rw [← List.map_drop] at hshift
  -- assemble the window value
  have key1 : valLimbs ((accs.drop 1 ++ D).map post.get)
      = valLimbs ((accs.drop 1).map s2.get) + (2 ^ 64) ^ 3 * valLimbs (D.map post.get) := by
    rw [List.map_append, valLimbs_append, List.length_map, List.length_drop, he3a, haccdrop]
  -- the higher-word ride-through split
  have hsplit := montgomeryReduce_window_split (valLimbs p) nP.toNat (valLimbs T)
    (valLimbs Higher)
  -- name the atoms
  set x := valLimbs ((accs.drop 1).map s2.get) with hxdef
  set y := valLimbs (D.map post.get) with hydef
  set cfb := (if post.flagB (·.cf) then (1 : Nat) else 0) with hcfbdef
  set r0 := (s2.get rcy).toNat with hr0def
  set h0 := valLimbs Higher with hh0def
  -- combine
  rw [he3a, hsplit, key1, ← hshift]
  have hkey : (2 ^ 64 : Nat) ^ (3 + D.length) = (2 ^ 64) ^ 3 * (2 ^ 64) ^ D.length :=
    pow_add (2 ^ 64) 3 D.length
  calc x + (2 ^ 64) ^ 3 * y + (2 ^ 64) ^ (3 + D.length) * cfb
      = x + ((2 ^ 64) ^ 3 * y + (2 ^ 64) ^ 3 * ((2 ^ 64) ^ D.length * cfb)) := by
        rw [hkey]; ring
    _ = x + (2 ^ 64) ^ 3 * (y + (2 ^ 64) ^ D.length * cfb) := by ring
    _ = x + (2 ^ 64) ^ 3 * (h0 + r0) := by rw [hfoldv]
    _ = x + (2 ^ 64) ^ 3 * r0 + (2 ^ 64) ^ 3 * h0 := by ring

/-! ## Zeroing the inter-step carry from the Montgomery range bound

One fused reduce word-step (`montRedcStep_fold_running_value`) reconstructs the new
running window plus a final carry bit weighted at the top. To chain the four steps
into `montRedc4`, that carry must be zero. `montRedcStep_chain` proves it from the
Montgomery range bound: the step's output value `montgomeryReduce … W < 2·⟦p⟧ < 2^256`
fits in the window, while the carry sits at weight `(2^64)^(3+|D|) ≥ 2^320`, so it is
forced to zero. The window value then equals the reduced value exactly, and the same
`< 2·⟦p⟧` bound feeds the next step's precondition. -/

/-- The little-endian limb value is bounded by the radix power of its length. -/
theorem valLimbs_lt_pow (l : List (BitVec 64)) : valLimbs l < (2 ^ 64) ^ l.length := by
  induction l with
  | nil => simp
  | cons w ws ih =>
    have hw : w.toNat < 2 ^ 64 := w.isLt
    have hstep : valLimbs ws + 1 ≤ (2 ^ 64) ^ ws.length := by omega
    calc valLimbs (w :: ws) = w.toNat + 2 ^ 64 * valLimbs ws := rfl
      _ < 2 ^ 64 + 2 ^ 64 * valLimbs ws := by omega
      _ = 2 ^ 64 * (valLimbs ws + 1) := by ring
      _ ≤ 2 ^ 64 * (2 ^ 64) ^ ws.length := by apply Nat.mul_le_mul_left; exact hstep
      _ = (2 ^ 64) ^ (w :: ws).length := by rw [List.length_cons, pow_succ]; ring

/-- **Carry elimination.** A window value `a < Wt` plus a single top carry `cfbit ≤ 1`
weighted at `Wt` equals a target `MR`; if `MR` is strictly below the same weight `Wt`
(here via `MR < twop ≤ Wt`), the carry must be zero and the window value is exactly
`MR`. -/
theorem carry_elim (a Wt cfbit MR twop : Nat)
    (hfold : a + Wt * cfbit = MR) (_ha : a < Wt) (hcf : cfbit ≤ 1)
    (hMR : MR < twop) (hbw : twop ≤ Wt) : a = MR ∧ cfbit = 0 := by
  interval_cases cfbit <;> omega

/-- **The fused reduce word-step, chainable form.** Given the value output of one fused
reduce word-step — the running window `accs.drop 1 ++ D` plus the final carry bit
reconstructing to `montgomeryReduce ⟦p⟧ (2^64) nP W` (`hfold`, from
`montRedcStep_fold_running_value`) — under the Montgomery side conditions and
`W < 2^64·⟦p⟧`, the carry is forced to zero: the window reconstructs to the reduced
value exactly, and that value is `< 2·⟦p⟧` (feeding the next step). Requires `|accs| = 4`,
`|p| = 4`, and `2 ≤ |D|` (the window weight `(2^64)^(3+|D|) ≥ 2^320` exceeds `2·⟦p⟧`). -/
theorem montRedcStep_chain (accs D : List String) (post : JState 64)
    (p : List (BitVec 64)) (nP : BitVec 64) (W : Nat)
    (haccs4 : accs.length = 4) (hp4 : p.length = 4) (hDge2 : 2 ≤ D.length)
    (hfold : valLimbs ((accs.drop 1 ++ D).map post.get)
          + (2 ^ 64) ^ (accs.length - 1 + D.length)
              * (if post.flagB (·.cf) then 1 else 0)
        = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W)
    (hN : 0 < valLimbs p)
    (hnp64 : (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1)
    (hWbound : W < 2 ^ 64 * valLimbs p) :
    valLimbs ((accs.drop 1 ++ D).map post.get)
        = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W
      ∧ Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W < 2 * valLimbs p := by
  have hcf1 : (if post.flagB (·.cf) then (1 : Nat) else 0) ≤ 1 := by split <;> omega
  set MR := Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W with hMRdef
  have hMRlt : MR < 2 * valLimbs p :=
    (Number.montgomeryReduce_correct (valLimbs p) (2 ^ 64) nP.toNat W hN
      (by positivity) hnp64 hWbound).1
  -- the window length equals the carry-weight exponent
  set k := accs.length - 1 + D.length with hkdef
  have hwinlen : (accs.drop 1 ++ D).length = k := by
    rw [List.length_append, List.length_drop, hkdef]
  have ha : valLimbs ((accs.drop 1 ++ D).map post.get) < (2 ^ 64) ^ k := by
    have := valLimbs_lt_pow ((accs.drop 1 ++ D).map post.get)
    rwa [List.length_map, hwinlen] at this
  -- the carry weight exceeds 2·⟦p⟧
  have hpk : (2 ^ 64 : Nat) ^ 4 ≤ (2 ^ 64) ^ k := by
    apply Nat.pow_le_pow_right (by norm_num); omega
  have hplt : valLimbs p < (2 ^ 64) ^ 4 := by
    have := valLimbs_lt_pow p; rwa [hp4] at this
  have h5 : (2 ^ 64 : Nat) ^ 5 ≤ (2 ^ 64) ^ k := by
    apply Nat.pow_le_pow_right (by norm_num); omega
  have hbw : 2 * valLimbs p ≤ (2 ^ 64) ^ k := by
    have h45 : (2 : Nat) * (2 ^ 64) ^ 4 ≤ (2 ^ 64) ^ 5 := by
      rw [pow_succ]; nlinarith [pow_pos (show 0 < 2 ^ 64 by norm_num) 4]
    omega
  have hcarry := carry_elim (valLimbs ((accs.drop 1 ++ D).map post.get))
    ((2 ^ 64) ^ k) (if post.flagB (·.cf) then 1 else 0) MR (2 * valLimbs p)
    hfold ha hcf1 hMRlt hbw
  exact ⟨hcarry.1, hMRlt⟩

/-! ## Composing the four fused word-steps into `montRedc4RunBlockGoal`

`emitMontRedc4Block` is `emitMontRedcStepAt 0 ++ … ++ emitMontRedcStepAt 3`, each
`emitMontRedcStepAt i` being the three entry `xor` clears, the emitted reduce word-step,
the `add`/`adc` carry fold — exactly the `foldCascade`-form fused step of
`montRedcStep_fold_running_value`. At window offset `i` the low window is
`(accNames.drop i).take 4` and the higher words are `accNames.drop (i+4) ++ [rtop]`.
`stepAt_advance` advances one step's running value; `montRedc4RunBlock_proven` chains
the four, threading the modulus/`n'` registers through (`stepAt_keeps`) and the
`< 2·⟦p⟧` bound forward, to discharge `montRedc4RunBlockGoal`. -/

section MontRedc4Fusion

open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedcCarryFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven

/-- **The fused word-step preserves registers outside its footprint.** A register `r`
distinct from the digit/carry/scratch registers, from every accumulator register `accs`,
and from every higher-word register `D` is unchanged by the whole fused step (the three
entry `xor` clears, the emitted reduce word-step, and the carry-fold cascade). -/
theorem fusedStep_pres (mReg t0Reg npReg dcy dhi dlo : String) (accs as : List String)
    (rcy rhi rlo : String) (D : List String) (s : JState 64) (r : String)
    (hmd : mReg ≠ dcy) (hmr : mReg ≠ rcy) (hdr : dcy ≠ rcy)
    (hm : r ≠ mReg) (hdcy : r ≠ dcy) (hrcy : r ≠ rcy)
    (hacc : ∀ q ∈ accs, r ≠ q)
    (hdhi : r ≠ dhi) (hdlo : r ≠ dlo) (hrhi : r ≠ rhi) (hrlo : r ≠ rlo)
    (hD : ∀ d ∈ D, r ≠ d) :
    (runBlock s ([JInstr.xor_ mReg (.reg mReg), JInstr.xor_ dcy (.reg dcy),
        JInstr.xor_ rcy (.reg rcy)]
        ++ emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo
        ++ foldCascade D rcy)).get r = s.get r := by
  rw [runBlock_append, runBlock_append]
  have foldpres : ∀ (t : JState 64), (runBlock t (foldCascade D rcy)).get r = t.get r := by
    intro t
    cases D with
    | nil => simp [foldCascade]
    | cons d0 tl =>
      rw [foldCascade, runBlock_cons,
        adcImm0Chain_preserves tl r _ (fun q hq => hD q (List.mem_cons_of_mem _ hq)),
        emit_add_other _ d0 rcy r (hD d0 List.mem_cons_self)]
  rw [foldpres]
  rw [emitMontRedcStep_preserves _ mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo r
      hacc hm hdcy hdhi hdlo hrcy hrhi hrlo]
  have hxc := xorClears3 s mReg dcy rcy hmd hmr hdr
  exact hxc.2.2.2.2.2 r hm hdcy hrcy

/-- The fused word-step `emitMontRedcStepAt i` (for `i ≤ 3`) in its explicit `foldCascade`
form: the three entry `xor` clears, the emitted reduce word-step over the window
`(accNames.drop i).take 4` and modulus `pNames`, and the carry-fold cascade over the higher
words `accNames.drop (i+4) ++ [rtop]`. -/
theorem emitMontRedcStepAt_fused (i : Nat) (hi3 : i ≤ 3) :
    emitMontRedcStepAt i
      = [JInstr.xor_ mName (.reg mName), JInstr.xor_ dcyName (.reg dcyName),
          JInstr.xor_ rcyName (.reg rcyName)]
        ++ emitMontRedcStep mName (((accNames.drop i).take 4).headD default) npName
            dcyName hiName loName ((accNames.drop i).take 4) pNames rcyName hiName loName
        ++ foldCascade (accNames.drop (i + 4) ++ [rtopName]) rcyName := by
  interval_cases i <;> rfl

/-- The fused reduce word-step `emitMontRedcStepAt i` (for `i ≤ 3`) preserves the modulus
registers `pNames` and the Montgomery-constant register `npName`: they are disjoint from
its footprint. -/
theorem stepAt_keeps (s : JState 64) (i : Nat) (hi3 : i ≤ 3) :
    pNames.map (runBlock s (emitMontRedcStepAt i)).get = pNames.map s.get
      ∧ (runBlock s (emitMontRedcStepAt i)).get npName = s.get npName := by
  rw [emitMontRedcStepAt_fused i hi3]
  interval_cases i <;>
    refine ⟨List.map_congr_left (fun r hr => ?_), ?_⟩ <;>
    (apply fusedStep_pres <;> first | (fin_cases hr <;> decide) | decide)

/-- **One fused word-step advances the running value by one `montgomeryReduce` step.** At
window offset `i` (`i ≤ 3`), with the modulus in `pNames` and `n'` in `npName`, running
`emitMontRedcStepAt i` reconstructs the new running window `win.drop 1 ++ D` to
`montgomeryReduce ⟦p⟧ (2^64) n' (⟦win⟧ + 2^256·⟦D⟧)`, and (from the Montgomery range bound)
that value is `< 2·⟦p⟧` — feeding the next step. The inter-step carry is zeroed by
`montRedcStep_chain`. -/
theorem stepAt_advance (s : JState 64) (i : Nat) (p : List (BitVec 64)) (nP : BitVec 64)
    (win D : List String)
    (hwin : win = (accNames.drop i).take 4) (hD : D = accNames.drop (i + 4) ++ [rtopName])
    (hp4 : p.length = 4) (hN : 0 < valLimbs p)
    (hnp64 : (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1)
    (hi3 : i ≤ 3)
    (hpN : pNames.map s.get = p) (hnpv : s.get npName = nP)
    (hWbound : valLimbs (win.map s.get) + (2 ^ 64) ^ 4 * valLimbs (D.map s.get)
        < 2 ^ 64 * valLimbs p) :
    valLimbs ((win.drop 1 ++ D).map (runBlock s (emitMontRedcStepAt i)).get)
        = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
            (valLimbs (win.map s.get) + (2 ^ 64) ^ 4 * valLimbs (D.map s.get))
      ∧ Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
            (valLimbs (win.map s.get) + (2 ^ 64) ^ 4 * valLimbs (D.map s.get))
        < 2 * valLimbs p := by
  subst hwin hD
  rw [emitMontRedcStepAt_fused i hi3]
  interval_cases i <;>
  · refine montRedcStep_chain _ _ _ p nP _
      (by decide) hp4 (by decide) ?_ hN hnp64 hWbound
    exact montRedcStep_fold_running_value s mName _ npName
      dcyName hiName loName _ pNames rcyName hiName loName _ p _ _ nP
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide)
      (by decide) hp4 (by decide) (by simp)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by rfl) hnpv hpN rfl
      (by simp) (by decide) (by simp) (by decide) (by decide) (by decide) rfl

/-- **The fused four-word reduce lands `montRedc4` in the top window.** From a window-loaded
start state (`MontRedc4Load`) meeting the Montgomery side conditions, running the fused
reduce block `emitMontRedc4Block` reconstructs the top window `accNames[4..7]` together with
`rtop` to `montRedc4 ⟦p⟧ n' ⟦T⟧`. The four `emitMontRedcStepAt` steps chain via
`stepAt_advance`, `stepAt_keeps` threading `pNames`/`npName`, and the Montgomery range bound
carried forward so each partial is `< 2·⟦p⟧ < 2^256` and every inter-step carry is zero.
This discharges `MontRedc4RunBlockProven.montRedc4RunBlockGoal`. -/
theorem montRedc4RunBlock_proven (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64)
    (hp4 : p.length = 4) (_hT4 : T.length = 4) (hN : 0 < valLimbs p)
    (hnp64 : (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1)
    (hTbound : valLimbs T < 2 ^ 64 * valLimbs p)
    (hload : MontRedc4Load s p T nP) :
    valLimbs ((accNames.drop 4).map (runBlock s emitMontRedc4Block).get)
      + (2 ^ 64) ^ 4 * ((runBlock s emitMontRedc4Block).get rtopName).toNat
    = montRedc4 (valLimbs p) nP.toNat (valLimbs T) := by
  obtain ⟨hlo, hhi, hpN, hnpv⟩ := hload
  have h2p : 2 * valLimbs p ≤ 2 ^ 64 * valLimbs p := by
    gcongr
    norm_num
  set s1 := runBlock s (emitMontRedcStepAt 0) with hs1
  set s2 := runBlock s1 (emitMontRedcStepAt 1) with hs2
  set s3 := runBlock s2 (emitMontRedcStepAt 2) with hs3
  set s4 := runBlock s3 (emitMontRedcStepAt 3) with hs4
  have k0 := stepAt_keeps s 0 (by norm_num); rw [← hs1] at k0
  have k1 := stepAt_keeps s1 1 (by norm_num); rw [← hs2] at k1
  have k2 := stepAt_keeps s2 2 (by norm_num); rw [← hs3] at k2
  have hpN1 : pNames.map s1.get = p := by rw [k0.1, hpN]
  have hnpv1 : s1.get npName = nP := by rw [k0.2, hnpv]
  have hpN2 : pNames.map s2.get = p := by rw [k1.1, hpN1]
  have hnpv2 : s2.get npName = nP := by rw [k1.2, hnpv1]
  have hpN3 : pNames.map s3.get = p := by rw [k2.1, hpN2]
  have hnpv3 : s3.get npName = nP := by rw [k2.2, hnpv2]
  have ha0 : valLimbs (((accNames.drop 0).take 4).map s.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (0 + 4) ++ [rtopName]).map s.get)
      = valLimbs T := by
    rw [show (accNames.drop 0).take 4 = accNames.take 4 from by decide, hlo,
        show (accNames.drop (0 + 4) ++ [rtopName]) = accNames.drop 4 ++ [rtopName] from rfl,
        hhi, valLimbs_replicate_zero, Nat.mul_zero, Nat.add_zero]
  have hc0 := stepAt_advance s 0 p nP ((accNames.drop 0).take 4)
    (accNames.drop (0 + 4) ++ [rtopName]) rfl rfl hp4 hN hnp64 (by norm_num) hpN hnpv
    (by rw [ha0]; exact hTbound)
  rw [← hs1] at hc0
  have ha1 : valLimbs (((accNames.drop 1).take 4).map s1.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (((accNames.drop 0).take 4).map s.get)
            + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (0 + 4) ++ [rtopName]).map s.get)) := by
    have e1 : valLimbs (((accNames.drop 1).take 4 ++ (accNames.drop (1 + 4) ++ [rtopName])).map s1.get)
        = valLimbs (((accNames.drop 1).take 4).map s1.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 1).take 4).length = 4 from by decide]
    rw [← e1,
      show (accNames.drop 1).take 4 ++ (accNames.drop (1 + 4) ++ [rtopName])
        = ((accNames.drop 0).take 4).drop 1 ++ (accNames.drop (0 + 4) ++ [rtopName]) from by decide,
      hc0.1]
  have hc1 := stepAt_advance s1 1 p nP ((accNames.drop 1).take 4)
    (accNames.drop (1 + 4) ++ [rtopName]) rfl rfl hp4 hN hnp64 (by norm_num) hpN1 hnpv1
    (by rw [ha1]; exact lt_of_lt_of_le hc0.2 h2p)
  rw [← hs2] at hc1
  have ha2 : valLimbs (((accNames.drop 2).take 4).map s2.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (((accNames.drop 1).take 4).map s1.get)
            + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get)) := by
    have e2 : valLimbs (((accNames.drop 2).take 4 ++ (accNames.drop (2 + 4) ++ [rtopName])).map s2.get)
        = valLimbs (((accNames.drop 2).take 4).map s2.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 2).take 4).length = 4 from by decide]
    rw [← e2,
      show (accNames.drop 2).take 4 ++ (accNames.drop (2 + 4) ++ [rtopName])
        = ((accNames.drop 1).take 4).drop 1 ++ (accNames.drop (1 + 4) ++ [rtopName]) from by decide,
      hc1.1]
  have hc2 := stepAt_advance s2 2 p nP ((accNames.drop 2).take 4)
    (accNames.drop (2 + 4) ++ [rtopName]) rfl rfl hp4 hN hnp64 (by norm_num) hpN2 hnpv2
    (by rw [ha2]; exact lt_of_lt_of_le hc1.2 h2p)
  rw [← hs3] at hc2
  have ha3 : valLimbs (((accNames.drop 3).take 4).map s3.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (3 + 4) ++ [rtopName]).map s3.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (((accNames.drop 2).take 4).map s2.get)
            + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get)) := by
    have e3 : valLimbs (((accNames.drop 3).take 4 ++ (accNames.drop (3 + 4) ++ [rtopName])).map s3.get)
        = valLimbs (((accNames.drop 3).take 4).map s3.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (3 + 4) ++ [rtopName]).map s3.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 3).take 4).length = 4 from by decide]
    rw [← e3,
      show (accNames.drop 3).take 4 ++ (accNames.drop (3 + 4) ++ [rtopName])
        = ((accNames.drop 2).take 4).drop 1 ++ (accNames.drop (2 + 4) ++ [rtopName]) from by decide,
      hc2.1]
  have hc3 := stepAt_advance s3 3 p nP ((accNames.drop 3).take 4)
    (accNames.drop (3 + 4) ++ [rtopName]) rfl rfl hp4 hN hnp64 (by norm_num) hpN3 hnpv3
    (by rw [ha3]; exact lt_of_lt_of_le hc2.2 h2p)
  rw [← hs4] at hc3
  have hpost : runBlock s emitMontRedc4Block = s4 := by
    rw [emitMontRedc4Block, runBlock_append, runBlock_append, runBlock_append,
        ← hs1, ← hs2, ← hs3, ← hs4]
  rw [hpost]
  have hfin : valLimbs ((accNames.drop 4).map s4.get) + (2 ^ 64) ^ 4 * (s4.get rtopName).toNat
      = valLimbs ((accNames.drop 4 ++ [rtopName]).map s4.get) := by
    rw [List.map_append, valLimbs_append, List.length_map,
        show (accNames.drop 4).length = 4 from by decide]
    simp
  rw [hfin,
    show accNames.drop 4 ++ [rtopName]
      = ((accNames.drop 3).take 4).drop 1 ++ (accNames.drop (3 + 4) ++ [rtopName]) from by decide,
    hc3.1, ha3, ha2, ha1, ha0]
  simp only [montRedc4]

/-- The strengthened `MontRedc4RunBlockProven.montRedc4RunBlockGoal` holds for every state:
its antecedents (`MontRedc4Load` plus the Montgomery side conditions) are exactly the
preconditions `montRedc4RunBlock_proven` consumes. -/
theorem montRedc4RunBlockGoal_holds (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64) :
    montRedc4RunBlockGoal s p T nP :=
  fun hp4 hT4 hN hnp64 hTbound hload =>
    montRedc4RunBlock_proven s p T nP hp4 hT4 hN hnp64 hTbound hload

end MontRedc4Fusion

/-- The state relation of the fused reduce-block `CorresJ`: the value window `a.win`
recomposes (via `valLimbs`) to `a.val`, and in the `input` phase the window is the low
four accumulator registers `accNames.take 4` holding the input limbs `T`, the modulus in
`pNames`, `nP` in `npName`, and the upper window with `rtop` cleared (`MontRedc4Load`). -/
def SRmontRedc4 (p T : List (BitVec 64)) (nP : BitVec 64)
    (st : JState 64) (a : AMontRedc) : Prop :=
  valLimbs (a.win.map st.get) = a.val ∧
    (a.phase = MontRedcPhase.input →
      a.win = X86Backend.Curve4MontMulProvenEmit.accNames.take 4 ∧
      X86Backend.MontRedc4RunBlockProven.MontRedc4Load st p T nP)

/-- The abstract transition of the fused reduce block: to the `output` phase, the top
window `accNames[4..7] ++ [rtop]`, holding `Cios4LimbProven.montRedc4 (valLimbs p) n'
a.val` — the full-radix reduction of the input value. -/
def faMontRedc4 (p : List (BitVec 64)) (nP : BitVec 64) (a : AMontRedc) : AMontRedc :=
  { phase := MontRedcPhase.output,
    win := X86Backend.Curve4MontMulProvenEmit.accNames.drop 4
      ++ [X86Backend.Curve4MontMulProvenEmit.rtopName],
    val := X86Backend.Cios4LimbProven.montRedc4 (valLimbs p) nP.toNat a.val }

open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven in
/-- **The emitted fused reduce block as a `CorresJ`.**
Running the four chained emitted word-steps `Curve4MontMulProvenEmit.emitMontRedc4Block`
under `runBlock` refines the abstract transition `faMontRedc4` through `SRmontRedc4`:
from a window-loaded input state (the `input` phase, `MontRedc4Load`: the low four
registers holding `T`, the modulus in `pNames`, `nP` in `npName`, the upper window and
`rtop` cleared) satisfying the Montgomery side conditions, the top window `accNames[4..7]`
together with `rtop` recomposes to `montRedc4 (valLimbs p) n' ⟦T⟧`.

The value conclusion is discharged by `montRedc4RunBlock_proven`, the block-level
composition of the four fused word-steps; `montRedc4_residue` reads the output value as the
`ZMod (valLimbs p)` residue `⟦T⟧ · (2^256)⁻¹`. -/
theorem corresJ_montRedc4Block (p T : List (BitVec 64)) (nP : BitVec 64)
    (hp4 : p.length = 4) (hT4 : T.length = 4) (hN : 0 < valLimbs p)
    (hnp64 : (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1)
    (hTbound : valLimbs T < 2 ^ 64 * valLimbs p) :
    CorresJ (SRmontRedc4 p T nP)
      (fun a => a.phase = MontRedcPhase.input)
      (faMontRedc4 p nP)
      X86Backend.Curve4MontMulProvenEmit.emitMontRedc4Block := by
  intro st a hSR hP
  obtain ⟨hval, hin⟩ := hSR
  obtain ⟨hwin, hload⟩ := hin hP
  have haval : a.val = valLimbs T := by rw [← hval, hwin, hload.1]
  have hg := montRedc4RunBlock_proven st p T nP hp4 hT4 hN hnp64 hTbound hload
  set post := runBlock st X86Backend.Curve4MontMulProvenEmit.emitMontRedc4Block with hpost
  refine ⟨?_, ?_⟩
  · show valLimbs ((faMontRedc4 p nP a).win.map post.get) = (faMontRedc4 p nP a).val
    simp only [faMontRedc4]
    rw [haval, List.map_append]
    rw [valLimbs_append]
    simp only [List.length_map, List.map_cons, List.map_nil, valLimbs_cons, valLimbs_nil,
      mul_zero, add_zero]
    have hlen4 : (X86Backend.Curve4MontMulProvenEmit.accNames.drop 4).length = 4 := by
      rfl
    rw [hlen4]
    exact hg
  · intro h
    simp only [faMontRedc4] at h
    exact absurd h (by decide)

end CatCrypt.Crypto.SecureCompilation.Ascent
