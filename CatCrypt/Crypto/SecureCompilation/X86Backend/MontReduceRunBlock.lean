/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock

/-!
# The emitted Montgomery REDUCE word-step over `runBlock`

`SchoolbookRunBlock.lean` ties one emitted schoolbook *row* `t += x·c` over the
faithful `runBlock` semantics to the abstract `Cios4LimbProven.addmul1`
(`emitRowBlock_runBlock_value`). The Montgomery reduction's per-word step is
structurally the same row, plus a digit and a shift:

* form the Montgomery digit `m = T₀·n' mod 2^64` (a `mulx`-low / `macLo` on the
  accumulator's low limb), the abstract `Cios4LimbProven.montDigit`;
* add `m·p` into the accumulator (one `emitRowBlock` row, `= addmul1 p m T 0`);
* shift the accumulator down one word (the spec's `/R = /2^64`, exact because the
  low limb cancels).

`Cios4LimbProven.ciosWord_eq` already proves that this triple equals one
`Number.montgomeryReduce (valLimbs p) (2^64) n' (valLimbs T)` (the
per-word REDC), via `mulScalar`/`addLimbs`. This file realises the *accumulate*
half over `runBlock` of an emitted `List (JInstr 64)`, reusing
`emitRowBlock_runBlock_value` (the row `= addmul1`) for the `m·p` accumulate, and
ties the recombined `runBlock` value of the emitted reduce-step to the abstract
`montgomeryReduce` step. Four such steps chain — via the proven
`Number.montgomeryReduce_comp` in `Cios4LimbProven.montRedc4_correct` — into the
full-radix `R = 2^256` reduction `montRedc4`.

## What is PROVEN (`runBlock(emitted) = montgomeryReduce`)

* **`emitMontDigit` / `emitMontDigit_runBlock`** — the Montgomery digit `m`
  emitted as one `emitColumnReset` over `T₀·n'` with cleared accumulator and
  carry: its `acc` register, read out of `runBlock`, equals
  `Cios4LimbProven.montDigit T n'`.

* **`emitMontRedcStep` / `emitMontRedcStep_runBlock`** ⭐ — one emitted reduce
  word-step over `runBlock`: the digit emit followed by the `m·p` accumulate row
  (`emitRowBlock`). Its recombined `runBlock` value (result limbs in `accs`, carry
  word in `cy`, divided by `2^64` for the shift) equals
  `Number.montgomeryReduce (valLimbs p) (2^64) n' (valLimbs T)` — one
  Montgomery reduction word-step, the accumulate produced by an emitted
  instruction list under faithful `runBlock` semantics. The accumulate row is
  `emitRowBlock_runBlock_value` (= `addmul1`); the numerator-to-`montgomeryReduce`
  reasoning is shared with `Cios4LimbProven.ciosWord_eq`.

* **`emitMontRedc4_value`** — four per-word steps, each the proven emitted
  step-value (`emitMontRedcStep_runBlock`), chain into `montRedc4 (valLimbs p) n'`
  via `Cios4LimbProven.montRedc4_correct`'s `montgomeryReduce_comp` composition:
  `< 2·p` and `· 2^256 ≡ T (mod p)`. Each word's input value is the previous
  word's emitted-step `runBlock` value.

## What is NOT covered (the named remainder)

`emitMontRedcStep_runBlock` ties ONE word-step's recombined `runBlock` value to
one `montgomeryReduce` step. `emitMontRedc4_value` chains four such values into
`montRedc4`. The four steps as a *single* `runBlock` trace — routing the
shifted-down accumulator limbs of step `i` into step `i+1`'s input registers
across one fused emitted block, with the inter-step register renaming — is
outside this module (the same multi-block register-routing the schoolbook's
`SchoolbookRunBlock` names for its inter-row combine). It does not change the
value spec: each step's value IS a `runBlock`-of-emitted reduction step.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
open CatCrypt.Crypto.Number

/-! ## 1. The emitted Montgomery digit `m = T₀·n' mod 2^64`

The Montgomery factor word `m = (T₀·n') mod 2^64` is one `mulx`-low / `macLo` on
the accumulator's low limb `T₀`. Emitted, it is one `emitColumnReset` with the
accumulator and carry cleared on entry: `emitColumnReset mReg t0Reg npReg cy hi
lo` reads `T₀` from `t0Reg`, `n'` from `npReg`, writes `macLo T₀ n' 0 0 =
montDigit T n'` into `mReg`. -/

/-- One emitted Montgomery-digit step: a single flag-resetting MAC column over
    `T₀·n'` with the accumulator register `mReg` and carry register `cy` cleared
    on entry, leaving `mReg = macLo T₀ n' 0 0 = montDigit T n'`. -/
def emitMontDigit (mReg t0Reg npReg cy hi lo : String) : List (JInstr 64) :=
  emitColumnReset mReg t0Reg npReg cy hi lo

/-- **The emitted digit register holds the abstract Montgomery digit.** Entered
    with both flags cleared, the accumulator register `mReg` and the carry `cy`
    holding `0`, the multiplier limbs `t0Reg = T₀` (the accumulator's low limb)
    and `npReg = n'`, running `emitMontDigit` leaves `mReg = montDigit T n'` over
    `runBlock`. This is `emitColumnReset_value` with `add = cin = 0`
    (`macLo T₀ n' 0 0 = montDigit T n'`). -/
theorem emitMontDigit_runBlock (s : JState 64) (mReg t0Reg npReg cy hi lo : String)
    (T : List (BitVec 64)) (nP : BitVec 64)
    (hAccLo : mReg ≠ lo) (hAccHi : mReg ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ mReg)
    (hLoHi : lo ≠ hi)
    (ht0 : s.get t0Reg = T.headD 0) (hnp : s.get npReg = nP)
    (hm0 : s.get mReg = 0) (hcy0 : s.get cy = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    (runBlock s (emitMontDigit mReg t0Reg npReg cy hi lo)).get mReg = montDigit T nP := by
  have h := (emitColumnReset_value s mReg t0Reg npReg cy hi lo (T.headD 0) nP 0 0
    hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi ht0 hnp hm0 hcy0 hcf hof).1
  rw [emitMontDigit]; rw [h]; rfl

/-! ## 2. The emitted reduce word-step over `runBlock`

`emitMontRedcStep` emits the per-word reduce: the digit emit (`emitMontDigit`),
then the `m·p` accumulate row (`emitRowBlock` over the modulus limbs `p`, the
digit `m` in `mReg`, the carry threaded through `rcy`). The recombined `runBlock`
value of the accumulate row (result limbs in `accs`, carry word in `rcy`),
divided by `2^64` for the shift-down, equals one `montgomeryReduce` step. -/

/-- One emitted Montgomery reduce word-step: form the digit `m` in `mReg`, then
    accumulate `T += m·p` as one emitted schoolbook row (`emitRowBlock` over the
    modulus-limb registers `as`, the accumulator registers `accs`, the digit
    `mReg` as the scalar, carry `rcy`). The shift-down is read off the output
    registers (the `/2^64`). -/
def emitMontRedcStep (mReg t0Reg npReg dcy dhi dlo : String)
    (accs as : List String) (rcy rhi rlo : String) : List (JInstr 64) :=
  emitMontDigit mReg t0Reg npReg dcy dhi dlo
    ++ emitRowBlock accs as mReg rcy rhi rlo

/-- **The emitted reduce word-step's recombined `runBlock` value = one Montgomery
    reduction step.** The accumulate row (`emitRowBlock`) leaves the result limbs
    in `accs` and the carry word in `rcy`; their little-endian recombination is
    `valLimbs T + valLimbs p · m` (= `addmul1`, via `emitRowBlock_runBlock_value`
    and `addmul1_reconstruct`), and dividing by `2^64` (the shift-down) yields
    `Number.montgomeryReduce (valLimbs p) (2^64) n' (valLimbs T)` — one
    per-word REDC, the accumulate produced by an emitted `List (JInstr 64)` under
    `runBlock`.

    Here `s1` is the post-digit state (digit `m = montDigit T n'` in `mReg`); the
    accumulator registers `accs` still hold `T`, `rcy` holds `0`, flags clear,
    and the modulus limbs `p` are in `as`. The numerator-to-`montgomeryReduce`
    reasoning is shared with `Cios4LimbProven.ciosWord_eq`. -/
theorem emitMontRedcStep_value
    (s1 : JState 64) (mReg rcy rhi rlo : String) (accs as : List String)
    (p T : List (BitVec 64)) (nP : BitVec 64)
    (hlen : as.length = accs.length) (hplen : p.length = as.length)
    (htlen : T.length = accs.length)
    (hfresh : RowFresh accs as mReg rcy rhi rlo)
    (has : as.map s1.get = p) (haccs : accs.map s1.get = T)
    (hmReg : s1.get mReg = montDigit T nP) (hrcy : s1.get rcy = 0)
    (hcf : s1.flagB (·.cf) = false) (hof : s1.flagB (·.of) = false) :
    (valLimbs (accs.map (runBlock s1 (emitRowBlock accs as mReg rcy rhi rlo)).get)
        + (2 ^ 64) ^ p.length
            * ((runBlock s1 (emitRowBlock accs as mReg rcy rhi rlo)).get rcy).toNat)
        / 2 ^ 64
      = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T) := by
  -- the accumulate row over runBlock = addmul1 p (montDigit T nP) T 0, recombined to T + p·m
  have hrow := emitRowBlock_valLimbs accs as p T (montDigit T nP) mReg rcy rhi rlo s1 0
    hlen hplen htlen hfresh has haccs hmReg hrcy hcf hof
  -- numerator = valLimbs (T.take |p|) + valLimbs p · m + 0
  rw [hrow]
  -- T.take |p| = T  (|p| = |as| = |accs| = |T|)
  have hpT : p.length = T.length := by rw [hplen, hlen, htlen]
  have htake : T.take p.length = T := by
    apply List.take_of_length_le; omega
  rw [htake, show (BitVec.toNat 0) = 0 from rfl, Nat.add_zero]
  -- m = montDigit T nP, so m.toNat = (valLimbs T · nP) mod 2^64
  -- montgomeryReduce N R nP T = (T + N · ((T·nP) mod R)) / R; here R = 2^64
  rw [montDigit_eq]
  simp only [montgomeryReduce]
  rw [Nat.mul_comm (valLimbs p)]

/-! ## 3. The full reduce word-step over one `runBlock` (digit + accumulate)

`emitMontRedcStep_runBlock` runs the whole emitted reduce step — the digit emit
then the `m·p` accumulate row — over a single `runBlock`. The digit block writes
only `{mReg, dcy, dhi, dlo}`, so the accumulator registers `accs` (holding `T`),
the modulus-limb registers `as` (holding `p`), and the accumulate carry `rcy`
survive into the post-digit state, at which `emitMontRedcStep_value` applies. The
recombined output value, divided by `2^64`, is one `montgomeryReduce` step. -/

/-- **The whole emitted reduce word-step over one `runBlock` = one Montgomery
    reduction step.** Running `emitMontRedcStep` from a state with both flags
    clear, the digit accumulator `mReg` and both carries (`dcy`, `rcy`) cleared,
    the low limb `t0Reg = T₀`, the constant `npReg = n'`, the accumulator
    registers `accs` holding `T`, and the modulus-limb registers `as` holding
    `p`, the recombined output value (result limbs in `accs`, carry in `rcy`)
    divided by `2^64` equals `Number.montgomeryReduce (valLimbs p) (2^64) n'
    (valLimbs T)`. The digit is `emitMontDigit_runBlock`; the accumulate is
    `emitMontRedcStep_value` on the post-digit state (registers preserved by
    `emitColumnReset_preserves`). -/
theorem emitMontRedcStep_runBlock
    (s : JState 64) (mReg t0Reg npReg dcy dhi dlo : String)
    (accs as : List String) (rcy rhi rlo : String)
    (p T : List (BitVec 64)) (nP : BitVec 64)
    -- digit-column register freshness
    (hAccLo : mReg ≠ dlo) (hAccHi : mReg ≠ dhi)
    (hDcyLo : dcy ≠ dlo) (hDcyHi : dcy ≠ dhi) (hDcyAcc : dcy ≠ mReg)
    (hDloHi : dlo ≠ dhi)
    -- the accumulate row preserves into the post-digit state: accs/as/rcy survive
    -- the digit block (which writes only {mReg, dcy, dhi, dlo})
    (hAcc_pres : ∀ r ∈ accs, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hAs_pres : ∀ r ∈ as, r ≠ mReg ∧ r ≠ dcy ∧ r ≠ dhi ∧ r ≠ dlo)
    (hRcy_pres : rcy ≠ mReg ∧ rcy ≠ dcy ∧ rcy ≠ dhi ∧ rcy ≠ dlo)
    -- accumulate-row freshness
    (hlen : as.length = accs.length) (hplen : p.length = as.length)
    (htlen : T.length = accs.length)
    (hfresh : RowFresh accs as mReg rcy rhi rlo)
    -- digit reads the low limb T₀ and the constant n'; T = head limb of accs read
    (ht0 : s.get t0Reg = T.headD 0) (hnp : s.get npReg = nP)
    (hm0 : s.get mReg = 0) (hdcy0 : s.get dcy = 0)
    -- input register contents and clear flags
    (has : as.map s.get = p) (haccs : accs.map s.get = T) (hrcy0 : s.get rcy = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    (valLimbs (accs.map (runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
            accs as rcy rhi rlo)).get)
        + (2 ^ 64) ^ p.length
            * ((runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo
                accs as rcy rhi rlo)).get rcy).toNat)
        / 2 ^ 64
      = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T) := by
  -- the post-digit state
  set s1 := runBlock s (emitMontDigit mReg t0Reg npReg dcy dhi dlo) with hs1
  -- the digit register holds montDigit T nP
  have hdig : s1.get mReg = montDigit T nP := by
    rw [hs1]
    exact emitMontDigit_runBlock s mReg t0Reg npReg dcy dhi dlo T nP
      hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi ht0 hnp hm0 hdcy0 hcf hof
  -- the digit block (one emitColumnReset) writes only {mReg, dcy, dhi, dlo};
  -- accs, as, rcy are preserved
  have hpres : ∀ r : String, r ≠ mReg → r ≠ dcy → r ≠ dhi → r ≠ dlo →
      s1.get r = s.get r := by
    intro r h1 h2 h3 h4
    rw [hs1, emitMontDigit]
    exact emitColumnReset_preserves s mReg t0Reg npReg dcy dhi dlo r h1 h2 h3 h4
  -- accs still hold T
  have haccs1 : accs.map s1.get = T := by
    rw [← haccs]; apply List.map_congr_left; intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hAcc_pres r hr
    exact hpres r h1 h2 h3 h4
  -- as still hold p
  have has1 : as.map s1.get = p := by
    rw [← has]; apply List.map_congr_left; intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hAs_pres r hr
    exact hpres r h1 h2 h3 h4
  -- rcy still 0
  have hrcy1 : s1.get rcy = 0 := by
    obtain ⟨h1, h2, h3, h4⟩ := hRcy_pres
    rw [hpres rcy h1 h2 h3 h4, hrcy0]
  -- the digit block resets both flags (emitColumnReset_value's flags-out)
  have hflags : s1.flagB (·.cf) = false ∧ s1.flagB (·.of) = false := by
    have h := emitColumnReset_value s mReg t0Reg npReg dcy dhi dlo (T.headD 0) nP 0 0
      hAccLo hAccHi hDcyLo hDcyHi hDcyAcc hDloHi ht0 hnp hm0 hdcy0 hcf hof
    rw [hs1, emitMontDigit]; exact ⟨h.2.2.1, h.2.2.2⟩
  -- the whole block = digit ++ accumulate; runBlock factors through s1
  have hrun : runBlock s (emitMontRedcStep mReg t0Reg npReg dcy dhi dlo accs as rcy rhi rlo)
      = runBlock s1 (emitRowBlock accs as mReg rcy rhi rlo) := by
    rw [emitMontRedcStep, runBlock_append, ← hs1]
  rw [hrun]
  exact emitMontRedcStep_value s1 mReg rcy rhi rlo accs as p T nP
    hlen hplen htlen hfresh has1 haccs1 hdig hrcy1 hflags.1 hflags.2

/-! ## 4. Four word steps chain into the full-radix Montgomery reduction

Each emitted reduce word-step's recombined `runBlock` value is one
`Number.montgomeryReduce (valLimbs p) (2^64) n'` step (`emitMontRedcStep_value`).
Feeding word `i`'s output value as word `i+1`'s input, four steps compose — via
`Number.montgomeryReduce_comp` inside `Cios4LimbProven.montRedc4_correct` — into
the full-radix `R = 2^256` reduction `montRedc4`. This is the value-level chain;
the four steps as a *single* fused `runBlock` trace (inter-step register routing)
is the named remainder. -/

/-- **Four emitted reduce word-step values = the full Montgomery reduction.** Let
    `step T` be the recombined `runBlock` value of one emitted reduce word-step on
    accumulator value `T` (each a `montgomeryReduce (valLimbs p) (2^64) n'` step by
    `emitMontRedcStep_value`). Chaining four such steps lands `montRedc4 (valLimbs
    p) n' T`, which (by `Cios4LimbProven.montRedc4_correct`) is `< 2·p` and
    `· 2^256 ≡ T (mod p)`. The hypotheses `hstep₁..₄` say each step's
    `runBlock`-recombined value is the corresponding `montgomeryReduce` step (the
    instances of `emitMontRedcStep_value` along the chain). -/
theorem emitMontRedc4_value
    (p : List (BitVec 64)) (nP : BitVec 64) (T : Nat)
    (w1 w2 w3 w4 : Nat)
    (hstep1 : w1 = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat T)
    (hstep2 : w2 = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat w1)
    (hstep3 : w3 = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat w2)
    (hstep4 : w4 = montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat w3)
    (hN : 0 < valLimbs p)
    (hnp64 : (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1)
    (hT : T < 2 ^ 64 * valLimbs p) :
    w4 = montRedc4 (valLimbs p) nP.toNat T ∧
    w4 < 2 * valLimbs p ∧ w4 * 2 ^ 256 ≡ T [MOD valLimbs p] := by
  -- the four-fold chain IS montRedc4 by definition
  have hw4 : w4 = montRedc4 (valLimbs p) nP.toNat T := by
    rw [hstep4, hstep3, hstep2, hstep1]; rfl
  obtain ⟨hrange, hcong⟩ := montRedc4_correct (valLimbs p) nP.toNat T hN hnp64 hT
  exact ⟨hw4, hw4 ▸ hrange, hw4 ▸ hcong⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
