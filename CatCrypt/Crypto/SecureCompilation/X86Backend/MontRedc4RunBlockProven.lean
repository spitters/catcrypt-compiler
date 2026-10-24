/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

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

This module attacks that fusion. It proves the first brick of the
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

## The fused target

`montRedc4RunBlockGoal` states the target: running `emitMontRedc4Block` from a
window-loaded state leaves `montRedc4 (valLimbs p) n' T` reconstructed in the top
window `accNames[4..7]` (plus `rtop`). The shift brick proved here, the carry-fold
cascade `MontRedcCarryFold.foldCascade_value` and `Ascent.montRedc4RunBlock_proven`
discharge it. §4 states the step from this pre-`emitCondSubP` window to the
canonical result registers `resNames`, which no theorem in this module covers.
-/

@[expose] public section

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

/-- An emitted reduce word-step writes only the accumulator registers `accs`, the
    digit register `mReg`, the digit carry `dcy`, the row carry `rcy`, and the
    scratch registers `dhi`/`dlo`/`rhi`/`rlo`: any register distinct from all of
    these is preserved across the whole step. -/
theorem emitMontRedcStep_preserves
    (s : JState 64) (mReg t0Reg npReg dcy dhi dlo : String)
    (accs as : List String) (rcy rhi rlo r : String)
    (hacc : ∀ q ∈ accs, r ≠ q) (hm : r ≠ mReg) (hdcy : r ≠ dcy)
    (hdhi : r ≠ dhi) (hdlo : r ≠ dlo) (hrcy : r ≠ rcy) (hrhi : r ≠ rhi)
    (hrlo : r ≠ rlo) :
    (runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo)).get r
      = s.get r := by
  rw [emitMontRedcStep, runBlock_append,
    emitRowBlock_preserves accs as mReg rcy rhi rlo r
      (runBlock s (emitMontDigit mReg t0Reg npReg dcy dhi dlo)) hacc hrcy hrhi hrlo,
    emitMontDigit,
    emitColumnReset_preserves s mReg t0Reg npReg dcy dhi dlo r hm hdcy hdhi hdlo]

/-- **An emitted reduce word-step ends with `CF = 0`.** Under the same loaded-state
    preconditions as `MontReduceRunBlock.emitMontRedcStep_runBlock`, running one
    emitted reduce word-step leaves the carry flag cleared: the accumulate row
    (`emitRowBlock`, the step's last block) resets `CF` (`emitRowBlock_runBlock_value`).
    This is the entry precondition the following carry-fold cascade reads. -/
theorem emitMontRedcStep_cf
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
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    (runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi
        rlo)).flagB (·.cf) = false := by
  set s1 := runBlock s (emitMontDigit mReg t0Reg npReg dcy dhi dlo) with hs1
  have hdig : s1.get mReg = montDigit T nP := by
    rw [hs1]
    exact emitMontDigit_runBlock s mReg t0Reg npReg dcy dhi dlo T nP
      hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi ht0 hnp hm0 hdcy0 hcf hof
  have hpres : ∀ r : String, r ≠ mReg → r ≠ dcy → r ≠ dhi → r ≠ dlo →
      s1.get r = s.get r := by
    intro r h1 h2 h3 h4
    rw [hs1, emitMontDigit]
    exact emitColumnReset_preserves s mReg t0Reg npReg dcy dhi dlo r h1 h2 h3 h4
  have haccs1 : accs.map s1.get = T := by
    rw [← haccs]; apply List.map_congr_left; intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hAcc_pres r hr
    exact hpres r h1 h2 h3 h4
  have has1 : as.map s1.get = p := by
    rw [← has]; apply List.map_congr_left; intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hAs_pres r hr
    exact hpres r h1 h2 h3 h4
  have hrcy1 : s1.get rcy = 0 := by
    obtain ⟨h1, h2, h3, h4⟩ := hRcy_pres
    rw [hpres rcy h1 h2 h3 h4, hrcy0]
  have hflags : s1.flagB (·.cf) = false ∧ s1.flagB (·.of) = false := by
    have h := emitColumnReset_value s mReg t0Reg npReg dcy dhi dlo (T.headD 0) nP 0 0
      hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi ht0 hnp hm0 hdcy0 hcf hof
    rw [hs1, emitMontDigit]; exact ⟨h.2.2.1, h.2.2.2⟩
  have hrun : runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo)
      = runBlock s1 (emitRowBlock accs as mReg rcy rhi rlo) := by
    rw [emitMontRedcStep, runBlock_append, ← hs1]
  rw [hrun]
  exact (emitRowBlock_runBlock_value accs as p T (montDigit T nP) mReg rcy rhi rlo s1 0
    hlen hplen htlen hfresh has1 haccs1 hdig hrcy1 hflags.1 hflags.2).2.2.1

/-- **The three self-`xor` entry clears.** Running `xor a,a; xor b,b; xor c,c`
    (with `a`, `b`, `c` pairwise distinct) zeroes `a`, `b`, `c`, resets `CF`/`OF`
    (the last `xor` clears both), and preserves every other register. This is the
    entry-precondition re-establishment before an emitted reduce word-step
    (`m = dcy = rcy = 0`, `CF = OF = 0`). -/
theorem xorClears3 (s : JState 64) (a b c : String)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (runBlock s [JInstr.xor_ a (.reg a), JInstr.xor_ b (.reg b),
        JInstr.xor_ c (.reg c)]).get a = 0
      ∧ (runBlock s [JInstr.xor_ a (.reg a), JInstr.xor_ b (.reg b),
          JInstr.xor_ c (.reg c)]).get b = 0
      ∧ (runBlock s [JInstr.xor_ a (.reg a), JInstr.xor_ b (.reg b),
          JInstr.xor_ c (.reg c)]).get c = 0
      ∧ (runBlock s [JInstr.xor_ a (.reg a), JInstr.xor_ b (.reg b),
          JInstr.xor_ c (.reg c)]).flagB (·.cf) = false
      ∧ (runBlock s [JInstr.xor_ a (.reg a), JInstr.xor_ b (.reg b),
          JInstr.xor_ c (.reg c)]).flagB (·.of) = false
      ∧ (∀ r, r ≠ a → r ≠ b → r ≠ c →
          (runBlock s [JInstr.xor_ a (.reg a), JInstr.xor_ b (.reg b),
              JInstr.xor_ c (.reg c)]).get r = s.get r) := by
  have hself : ∀ (t : JState 64) (x : String),
      (evalInstr t (JInstr.xor_ x (.reg x))).get x = 0 := by
    intro t x
    rw [get_xor]
    simp [JOperand.eval, x86_XOR, rflags_of_bwop, BitVec.xor_self]
  have hother : ∀ (t : JState 64) (x r : String), r ≠ x →
      (evalInstr t (JInstr.xor_ x (.reg x))).get r = t.get r := by
    intro t x r hr; rw [get_xor, ite_eq_right hr]
  simp only [runBlock_cons, runBlock_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hother _ c a hac, hother _ b a hab, hself]
  · rw [hother _ c b hbc, hself]
  · rw [hself]
  · simp only [JState.flagB, cf_xor, Option.getD_some]
  · simp only [JState.flagB, of_xor, Option.getD_some]
  · intro r hra hrb hrc
    rw [hother _ c r hrc, hother _ b r hrb, hother _ a r hra]

/-! ## 2b. The Montgomery-reduce window-split arithmetic bridge

One `montgomeryReduce` word-step reads its Montgomery digit `m = (T·n') mod R` only
from the low `R`-residue of its input, and its `/R` shift-down carries any higher
part through unchanged. `montgomeryReduce_add_high` states this: adding `R·b` to the
input adds exactly `b` to the output. `montgomeryReduce_window_split` is its
four-word instance, the "higher product words ride through untouched" fact, the piece that lets the shift
brick (`emitMontRedcStep_shifted_window`) and the carry-fold cascade
(`MontRedcCarryFold.foldCascade_value`) act on the low window word while the higher
running words pass through. -/

/-- **The higher part rides through the reduce step.** Adding `R·b` to the input of one
    `montgomeryReduce` word-step adds exactly `b` to the output:
    `montgomeryReduce N R n' (a + R·b) = montgomeryReduce N R n' a + b`.
    The Montgomery digit `m = (·n') mod R` reads only the low `R`-residue, so it is
    unchanged by the `R·b` term; the `/R` shift-down then splits the `R·b` off as `b`.
    No Montgomery-relation hypothesis is needed — the identity is a pure floor-division
    fact about the reduce shape `(T + m·N)/R`. -/
theorem montgomeryReduce_add_high (N R Nprime a b : Nat) (hR : 0 < R) :
    montgomeryReduce N R Nprime (a + R * b)
      = montgomeryReduce N R Nprime a + b := by
  unfold montgomeryReduce
  set m := (a * Nprime) % R with hm
  have hmeq : ((a + R * b) * Nprime) % R = m := by
    rw [hm, Nat.add_mul, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  rw [hmeq, show (a + R * b) + m * N = (a + m * N) + R * b by ring,
    Nat.add_mul_div_left _ _ hR]

/-- **The four-word window split of one reduce step.** For a low window value `lo`
    (four words, `< (2^64)^4`) and a higher part `hi`, one `montgomeryReduce` word-step
    at radix `2^64` on `lo + (2^64)^4·hi` equals the windowed reduce plus `(2^64)^3·hi`:
    `montgomeryReduce N (2^64) n' (lo + (2^64)^4·hi)
       = montgomeryReduce N (2^64) n' lo + (2^64)^3·hi`.
    The `Nat` arithmetic bridge of the composition in §4 of `MontRedcCarryFold`:
    the `/R = /2^64` shift-down drops the low window word and demotes the four-word
    weight `(2^64)^4·hi` to `(2^64)^3·hi`, so the higher running words `accNames[i+4..7]`
    and `rtop` ride through one reduce step untouched (down-shifted by one word). -/
theorem montgomeryReduce_window_split (N n' lo hi : Nat) :
    montgomeryReduce N (2 ^ 64) n' (lo + (2 ^ 64) ^ 4 * hi)
      = montgomeryReduce N (2 ^ 64) n' lo + (2 ^ 64) ^ 3 * hi := by
  have hsplit : (2 ^ 64 : Nat) ^ 4 * hi = 2 ^ 64 * ((2 ^ 64) ^ 3 * hi) := by ring
  rw [hsplit, montgomeryReduce_add_high N (2 ^ 64) n' lo ((2 ^ 64) ^ 3 * hi)
    (by positivity)]

/-! ## 3. The fused target

The four word steps as a single `runBlock` trace land the full-radix reduction in
the top window. `montRedc4RunBlockGoal` states this precisely, carrying the
window-load precondition `MontRedc4Load` and the Montgomery side conditions in its
antecedent. It is discharged (from these preconditions) by
`Ascent.montRedc4RunBlock_proven`, which composes the four fused word-steps and
folds the Montgomery range bound to zero out the inter-step carries. -/

/-- The window-loaded input state for the fused 4-limb reduce: the low four
    accumulator registers `accNames.take 4` hold the input limbs `T`, the upper
    window `accNames[4..7]` together with the top-carry `rtop` are cleared, the
    modulus limbs `p` are in `pNames`, and the Montgomery constant `nP` is in
    `npName`. -/
def MontRedc4Load (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64) : Prop :=
  (Curve4MontMulProvenEmit.accNames.take 4).map s.get = T ∧
    ((Curve4MontMulProvenEmit.accNames.drop 4)
        ++ [Curve4MontMulProvenEmit.rtopName]).map s.get = List.replicate 5 0 ∧
    Curve4MontMulProvenEmit.pNames.map s.get = p ∧
    s.get Curve4MontMulProvenEmit.npName = nP

/-- **The fused 4-limb reduce goal.** For a window-loaded start state
    (`MontRedc4Load`: the input accumulator `T` in registers `accNames.take 4`, the
    modulus `p` in `pNames`, `nP` in `npName`, the upper window `accNames[4..7]` and
    `rtop` cleared) satisfying the Montgomery side conditions (`p` and `T` are four
    limbs, `0 < ⟦p⟧`, the constant relation `(⟦p⟧·nP) mod 2^64 = 2^64 − 1`, and the
    input bound `⟦T⟧ < 2^64·⟦p⟧`), running the fused reduce block `emitMontRedc4Block`
    lands the four-fold Montgomery reduction `montRedc4 ⟦p⟧ nP ⟦T⟧` reconstructed
    across the top window `accNames[4..7]` and the top-carry word `rtop`:

    `valLimbs ((accNames.drop 4).map post.get)
       + (2^64)^4 · (post.get rtopName).toNat
     = montRedc4 (valLimbs p) nP.toNat (valLimbs T)`,

    where `post = runBlock s emitMontRedc4Block`. It is the pre-`emitCondSubP`
    reduce; the trailing conditional subtract then canonicalises into `resNames`.
    Proved by `Ascent.montRedc4RunBlock_proven`. -/
def montRedc4RunBlockGoal
    (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64) : Prop :=
  p.length = 4 → T.length = 4 → 0 < valLimbs p →
  (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1 →
  valLimbs T < 2 ^ 64 * valLimbs p →
  MontRedc4Load s p T nP →
  valLimbs ((Curve4MontMulProvenEmit.accNames.drop 4).map
        (runBlock s Curve4MontMulProvenEmit.emitMontRedc4Block).get)
      + (2 ^ 64) ^ 4
          * ((runBlock s Curve4MontMulProvenEmit.emitMontRedc4Block).get
              Curve4MontMulProvenEmit.rtopName).toNat
    = montRedc4 (valLimbs p) nP.toNat (valLimbs T)

/-! ## 4. From `montRedc4RunBlockGoal` to the canonical result

1. **Carry-fold routing.** `emitMontRedcStep_shifted_window` lands step `i`'s value
   in the shifted window `accs.drop 1` with the carry in `rcy`;
   `MontRedcCarryFold.foldCascade_value` folds that carry through
   `accNames[i+4..7]` into `rtop`; `Ascent.montRedcStep_fold_running_value` glues the
   two over one fused word-step; and `Ascent.montRedc4RunBlock_proven` composes the
   four fused steps, folding the Montgomery range bound
   (`Number.montgomeryReduce_correct`, each partial `< 2·p < 2^256`) to zero out the
   inter-step carries and discharge `montRedc4RunBlockGoal`.

2. **`emitCondSubP`.** `montRedc4RunBlockGoal` is the pre-`emitCondSubP` reduce
   (value `< 2·p`, reconstructed across `accNames[4..7]` and `rtop`). From there the
   10-round `Curve4MontMulProvenEmit.emitCondSubP` (`condSubRounds = 10`)
   canonicalises into `resNames`. The emit's own comment flags a one-round
   `rtop`/borrow interaction that the iterated subtract works around. No theorem in
   this module states the value of the canonicaliser: running `emitCondSubP` from a
   window holding `v < 2·p` leaves `v mod p` in `resNames`. That statement is the
   `ResReducedWindow` realiser that `EmittedReduceWindowDischarge` and
   `EmittedReduceWindow6Discharge` assume. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven
