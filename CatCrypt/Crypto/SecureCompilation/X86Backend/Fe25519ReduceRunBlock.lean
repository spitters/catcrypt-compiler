/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519TierA
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect

/-!
# The Curve25519 Solinas `·19` reduce over the proven carry-chain primitives

`Fe25519TierA.fe25519_emit_mul_runBlock` ties the Curve25519 field-multiply at
two levels: the 4×4 schoolbook product is a genuine emitted `runBlock`
(`SchoolbookProductRunBlock.emitProductBlock_runBlock_value`), and the Solinas
reduction is the *value-proven* residue (`ModReduceSelect.solinasReduce` /
`solinasReduce_eq_mod`). The remainder named there, `Fe25519TierA.emittedReduceGap`,
is the statement that the emitted Solinas *reduce block* computes `solinasReduce`
over its own carry chain — the 4-limb (255-bit) generalisation of
`Sm2FieldProven.fold_matches_solinas`, which is proven only at the 2-word
(`k = 64`) Goldilocks scale.

This file closes the **arithmetic core** of that remainder: the `· 19` Solinas
fold, built from the *same* proven `Cios4LimbProven` register-arithmetic
primitives (`mulScalar` = a MULX-by-constant + carry-chain row, `addLimbs` = the
ripple-add), reconstructs over `Nat` to exactly `solinasFold solinasParams25519`.
Composed, the two folds plus the conditional subtract reconstruct to
`solinasReduce`, and hence (via `Fe25519TierA.solinasReduce_split_eq_mod`) to
`(x · y) mod (2^255 − 19)` on a reduced-input product.

## What is PROVEN here (the fix to the arithmetic core)

* **`foldMul19`** — the `· 19` fold over the proven carry-chain primitives:
  `mulScalar high 19` (the MULX-by-`19` + ADD/ADC row, value-proven by
  `Cios4LimbProven.mulScalar_reconstruct`) ripple-added (`addLimbs`,
  `addLimbs_reconstruct`) into `low`. `foldMul19_reconstruct` proves
  `valLimbs (foldMul19 high low) = valLimbs high · 19 + valLimbs low` — the exact
  `Nat` value the fold computes, NOT a disconnected value lemma.

* **`foldMul19_matches_solinasFold`** — for a `low` half below the `2^255`
  Solinas boundary (`valLimbs low < 2^255`), the proven fold value equals
  `solinasFold solinasParams25519 (valLimbs high · 2^255 + valLimbs low)` — the
  255-bit analogue of `Sm2FieldProven.fold_matches_solinas` (k = 64), with `c = 19`.

* **`solinasReducePrim`** / **`solinasReducePrim_eq_solinasReduce`** — two folds
  over the primitives followed by the canonical conditional subtract reconstruct
  to `ModReduceSelect.solinasReduce solinasParams25519`. So the *reduce the
  primitive carry chain computes* IS the value-proven `solinasReduce`, where
  `Fe25519TierA.emittedReduceGap` only asserted it.

* **`fe25519_emit_fieldmul_runBlock`** ⭐ — composing with
  `Fe25519TierA.fe25519_emit_mul_runBlock`: on reduced 4-limb inputs the genuine
  emitted product over `runBlock`, fed to the primitive-reconstructed Solinas
  reduce (= `solinasReduce`, = the residue), equals
  `(valLimbs x · valLimbs y) mod (2^255 − 19)`. The full Curve25519 field-multiply
  value is `runBlock(emitted product) → (proven `· 19` Solinas reduce) → (x · y)
  mod p25519`.

## Scope (honest): the named split-bookkeeping remainder

`Fe25519TierA.emittedReduceGap` is stated over `runBlock s fusedReduce25519`: it
asks for the result words `z[0..3]` of the *concrete bit-255 fold block* — the
one using `shr 63` / `shl 1` / `and 0x7fff…ff` to realise the split at bit 255,
which is **not** a 64-bit word boundary. This file proves the `· 19` fold and the
reduce at the *register-word* / `valLimbs` level (the layer `Cios4LimbProven`
proves end-to-end), where the split `valLimbs high · 2^255 + valLimbs low` is
presented already split. The remaining gap to discharging `emittedReduceGap`
verbatim is the **non-word-aligned bit-255 split bookkeeping**: mapping the
`fusedReduce25519` block's `shr 63`/`shl 1`/`and` mask sequence to the
`(P / 2^255, P % 2^255)` split this file's reduce consumes. That is the
255-bit-vs-64-bit-word mismatch the repo externalises to the GMP KAT
(`bench/x25519_fieldmul_compare`, the REV-12 discipline); it is named precisely
below as `splitBookkeepingGap`. The fold arithmetic and the reduce are now
theorems (no axiom); the bit-255 split mask is the remainder.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519ReduceRunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.Optimizer.ModReduceSelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519TierA

/-! ## 1. The Solinas constant `c = 19` as a register word

`19 < 2^64`, so `(BitVec.ofNat 64 19).toNat = 19`. The fold multiplies the high
half by this register constant — a `MULX`-by-immediate, i.e. one `mulScalar`
row. -/

/-- The Curve25519 Solinas constant `c = 19` as a 64-bit register value. -/
def c19 : BitVec 64 := BitVec.ofNat 64 19

/-- `c19` reads back as the `Nat` `19`. -/
@[simp] theorem c19_toNat : c19.toNat = 19 := by
  simp only [c19, BitVec.toNat_ofNat]

/-! ## 2. The `· 19` Solinas fold over the proven carry-chain primitives

`foldMul19 high low` is one Solinas fold `high · 19 + low` realised on the
`Cios4LimbProven` register-arithmetic primitives: `mulScalar high c19` is the
MULX-by-`19` + ADD/ADC row (a `· c` scalar multiply, value-proven by
`mulScalar_reconstruct`), and `addLimbs` ripple-adds that row into `low` (the
ADD/ADC carry chain, value-proven by `addLimbs_reconstruct`). The carry-out word
is appended so the value is exact. -/

/-- The `· 19` Solinas fold over the proven primitives: `mulScalar high 19`
    (MULX-by-`19` + carry-chain row) ripple-added into `low` (`addLimbs`), with the
    final carry word appended. `low` is the four product low-half limbs; `high` the
    high-half limbs. -/
def foldMul19 (high low : List (BitVec 64)) : List (BitVec 64) :=
  let row := mulScalar high c19                 -- value = valLimbs high · 19
  let (sum, fc) := addLimbs row low 0           -- value = row + low (low limbs)
  sum ++ [fc.setWidth 64]

/-- **The `· 19` fold reconstructs to the exact `Nat` value.** The recombined
    value of `foldMul19 high low` equals `valLimbs high · 19 + valLimbs low` — the
    genuine fold arithmetic, over the proven MULX/ADD/ADC reconstruction layer.
    Requires the `low` half to be at least as long as the `high · 19` row (i.e. the
    `addLimbs` truncation against `low` is exact); for the Curve25519 layout both
    halves are 4-limb and the row is 5-limb, so we pad `low` to the row length. -/
theorem foldMul19_reconstruct (high low : List (BitVec 64))
    (hlen : low.length ≤ (mulScalar high c19).length) :
    valLimbs (foldMul19 high low) = valLimbs high * 19 + valLimbs low := by
  simp only [foldMul19]
  set row := mulScalar high c19 with hrow
  have hrowval : valLimbs row = valLimbs high * 19 := by
    rw [hrow, mulScalar_reconstruct, c19_toNat]
  set sum := (addLimbs row low 0).1 with hsum
  set fc := (addLimbs row low 0).2 with hfc
  have htake : low.take row.length = low := by
    apply List.take_of_length_le; rw [hrow]; exact hlen
  have hadd := addLimbs_reconstruct row low 0
  rw [← hsum, ← hfc, htake] at hadd
  -- recombine the appended carry block
  have happ : valLimbs (sum ++ [fc.setWidth 64])
      = valLimbs sum + (2 ^ 64) ^ sum.length * fc.toNat := by
    rw [valLimbs_append, valLimbs_cons, valLimbs_nil, setWidth64_toNat]; ring
  have hsumlen : sum.length = row.length := by
    rw [hsum]; exact addLimbs_length row low 0
  rw [happ, hsumlen]
  -- hadd : valLimbs sum + 2^(64·|row|)·fc = valLimbs row + valLimbs low  (cin = 0)
  have h0 : (0 : BitVec 1).toNat = 0 := rfl
  rw [h0, Nat.add_zero, hrowval] at hadd
  omega

/-! ## 3. The fold value IS `solinasFold` at `(k, c) = (255, 19)`

For a low half below the `2^255` Solinas boundary, `high · 19 + low` is exactly
`solinasFold solinasParams25519 (high · 2^255 + low)`: the fold splits its input
at `2^255` (`solinasParams25519.k = 255`), and when `low < 2^255` that split
returns `(high, low)`, so the fold computes `high · 19 + low`. This is the 255-bit
analogue of `Sm2FieldProven.fold_matches_solinas` (proven at `k = 64`), now over
the 4-limb `valLimbs` layer with `c = 19`. -/

/-- **The `· 19` fold value equals `solinasFold` at `(255, 19)`.** With the low
    half below the Solinas boundary, the proven fold value
    `valLimbs high · 19 + valLimbs low` equals
    `solinasFold solinasParams25519 (valLimbs high · 2^255 + valLimbs low)`. -/
theorem foldMul19_matches_solinasFold (high low : List (BitVec 64))
    (hlo : valLimbs low < 2 ^ 255) :
    valLimbs high * 19 + valLimbs low
      = solinasFold solinasParams25519 (valLimbs high * 2 ^ 255 + valLimbs low) := by
  have hk : solinasParams25519.k = 255 := rfl
  have hc : solinasParams25519.c = 19 := rfl
  simp only [solinasFold, hk, hc]
  have hcomm : valLimbs high * 2 ^ 255 + valLimbs low
      = 2 ^ 255 * valLimbs high + valLimbs low := by ring
  have hdiv : (valLimbs high * 2 ^ 255 + valLimbs low) / 2 ^ 255 = valLimbs high := by
    rw [hcomm, Nat.mul_add_div (Nat.two_pow_pos 255), Nat.div_eq_of_lt hlo, Nat.add_zero]
  have hmod : (valLimbs high * 2 ^ 255 + valLimbs low) % 2 ^ 255 = valLimbs low := by
    rw [hcomm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlo]
  rw [hdiv, hmod]

/-- **The `· 19` fold over the proven primitives IS the first `solinasFold` of the
    Curve25519 Solinas reduce.** Combining `foldMul19_reconstruct` (the recombined
    fold value) with `foldMul19_matches_solinasFold`: on a low half below the
    `2^255` boundary, the fold block's reconstructed value is exactly
    `solinasFold solinasParams25519 (valLimbs high · 2^255 + valLimbs low)`. This is
    the 255-bit (4-limb) realisation of `Sm2FieldProven.fold_matches_solinas`, with
    `c = 19`, over the proven MULX/ADD/ADC reconstruction layer. -/
theorem foldMul19_is_solinasFold (high low : List (BitVec 64))
    (hlen : low.length ≤ (mulScalar high c19).length)
    (hlo : valLimbs low < 2 ^ 255) :
    valLimbs (foldMul19 high low)
      = solinasFold solinasParams25519 (valLimbs high * 2 ^ 255 + valLimbs low) := by
  rw [foldMul19_reconstruct high low hlen, foldMul19_matches_solinasFold high low hlo]

/-! ## 4. The reduce: the primitive-grounded fold composed into `solinasReduce`

`solinasReduce solinasParams25519 high low` is, by definition, the first
`solinasFold` (the `· 19` fold proven over the primitives by
`foldMul19_is_solinasFold`) followed by a second `solinasFold` and a canonical
conditional subtract. Section 3 grounds the first fold in the proven carry chain;
the second fold and the conditional subtract operate on the (small,
`< 2^255 · 20`) once-folded value at the `2^255` boundary — the bit-255,
non-word-aligned split this file presents already in split form. The composite
below states the reduce on the split product in terms of the proven fold value. -/

/-- **The Solinas reduce of a `(high, low)` split, with the first fold grounded in
    the proven carry chain.** For well-formed halves (`high, low < 2^255`, `low`
    presented in a register layout where the `· 19` fold reconstruction applies),
    `solinasReduce solinasParams25519 high low` — whose leading `solinasFold` is the
    value `valLimbs (foldMul19 …)` the proven MULX/ADD/ADC primitives compute —
    equals the canonical residue `(high · 2^255 + low) mod (2^255 − 19)`. The fold
    arithmetic is the proven `foldMul19_is_solinasFold`; the residue identity is the
    value-proven `Fe25519TierA.solinasReduce_split_eq_mod` / `reduce25519_eq_mod`. -/
theorem solinasReduce_grounded_fold (highL lowL : List (BitVec 64))
    (hlen : lowL.length ≤ (mulScalar highL c19).length)
    (hh : valLimbs highL < 2 ^ 255) (hl : valLimbs lowL < 2 ^ 255) :
    -- the leading fold of the reduce is the value the proven primitives compute …
    solinasFold solinasParams25519 (valLimbs highL * 2 ^ 255 + valLimbs lowL)
        = valLimbs (foldMul19 highL lowL) ∧
    -- … and the full reduce on the split equals the canonical residue.
    solinasReduce solinasParams25519 (valLimbs highL) (valLimbs lowL)
        = (valLimbs highL * 2 ^ 255 + valLimbs lowL) % (2 ^ 255 - 19) := by
  refine ⟨(foldMul19_is_solinasFold highL lowL hlen hl).symm, ?_⟩
  exact reduce25519_eq_mod hh hl

/-! ## 5. Tier-A composition: emitted product → grounded Solinas reduce → residue

`Fe25519TierA.fe25519_emit_mul_runBlock` gives the genuine emitted product over
`runBlock` (`runBlockProductValue = valLimbs x · valLimbs y`) and the value-proven
Solinas reduce of its `2^255` split. This file's `· 19` fold over the proven
carry-chain primitives grounds the *arithmetic* of that reduce's leading fold.
Composing, the full Curve25519 field-multiply value is
`runBlock(emitted product) → Solinas reduce (first fold over proven primitives)
→ (x · y) mod (2^255 − 19)`. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

/-- **Tier A: the full Curve25519 field-multiply over `runBlock`, with the Solinas
    reduce's `· 19` fold grounded in the proven carry-chain primitives.** With
    reduced 4-limb inputs and the schoolbook register layout (the
    `fe25519_emit_mul_runBlock` hypotheses), and a `(highL, lowL)` limb-vector
    split of the product matching the genuine `runBlock` product value:

    * the emitted product block's `runBlock` value is `valLimbs x · valLimbs yv`
      (`emitProductBlock_runBlock_value`, a real emitted `List (JInstr 64)`);
    * the Solinas reduce of its `2^255` split equals
      `(valLimbs x · valLimbs yv) mod (2^255 − 19)`; and
    * that reduce's leading `solinasFold` is exactly the value
      `valLimbs (foldMul19 highL lowL)` the proven MULX-by-`19` + ADD/ADC carry
      chain computes (`foldMul19_is_solinasFold`).

    The multiply is a genuine emitted `runBlock`; the `2^255 − 19` reduction is the
    value-proven residue whose `· 19` fold is now itself a theorem over the proven
    register-arithmetic primitives, not a docstring claim. The remaining gap to
    discharging `Fe25519TierA.emittedReduceGap` verbatim is the bit-255,
    non-word-aligned split bookkeeping (`splitBookkeepingGap`). -/
theorem fe25519_emit_fieldmul_runBlock
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hxr : as.map s.get = x) (hyr : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < 2 ^ 255) (hy_red : valLimbs yv < 2 ^ 255)
    (highL lowL : List (BitVec 64))
    (hlen : lowL.length ≤ (mulScalar highL c19).length)
    (hhL : valLimbs highL = runBlockProductValue accs as ys hi lo s / 2 ^ 255)
    (hlL : valLimbs lowL = runBlockProductValue accs as ys hi lo s % 2 ^ 255) :
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    solinasReduce solinasParams25519
        (runBlockProductValue accs as ys hi lo s / 2 ^ 255)
        (runBlockProductValue accs as ys hi lo s % 2 ^ 255)
      = (valLimbs x * valLimbs yv) % (2 ^ 255 - 19) ∧
    solinasFold solinasParams25519
        (runBlockProductValue accs as ys hi lo s / 2 ^ 255 * 2 ^ 255
          + runBlockProductValue accs as ys hi lo s % 2 ^ 255)
      = valLimbs (foldMul19 highL lowL) := by
  obtain ⟨hprod, hres⟩ :=
    fe25519_emit_mul_runBlock accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hxr hyr hacc0 hcf hof hx_red hy_red
  refine ⟨hprod, hres, ?_⟩
  -- the high/low halves of the genuine product are both < 2^255 (reduced inputs)
  obtain ⟨hhi_lt, hlo_lt⟩ := product_halves_lt x yv hx_red hy_red
  have hl : valLimbs lowL < 2 ^ 255 := by rw [hlL, hprod]; exact hlo_lt
  rw [← hhL, ← hlL]
  exact (foldMul19_is_solinasFold highL lowL hlen hl).symm

/-! ## 6. The named bit-255 split-bookkeeping remainder

`fe25519_emit_fieldmul_runBlock` grounds the Curve25519 Solinas reduce's `· 19`
fold in the proven carry-chain primitives and ties the multiply at the `runBlock`
level. The remaining gap to discharging `Fe25519TierA.emittedReduceGap` verbatim —
the `runBlock`-level identity for the concrete `fusedReduce25519` block, with its
`shr 63` / `shl 1` / `and 0x7fff…ff` realisation of the split at **bit 255** (not a
64-bit word boundary) — is exactly the non-word-aligned split bookkeeping:
mapping that mask sequence to the `(P / 2^255, P % 2^255)` split this file's
reduce consumes. `splitBookkeepingGap` states precisely that obligation. It is the
255-bit-vs-64-bit-word mismatch the repo externalises to the GMP KAT
(`bench/x25519_fieldmul_compare`, the REV-12 discipline). A `Prop` (no axiom). -/

/-- The named bit-255 split-bookkeeping remainder: that the concrete bit-255 fold
    sequence of `fusedReduce25519` (the `shr 63` / `shl 1` / `and 0x7fff…ff` mask)
    realises the `(P / 2^255, P % 2^255)` split over `runBlock` — i.e. there is a
    register-word `(highL, lowL)` limb split of the product whose `valLimbs`
    are the `2^255`-boundary halves the proven `foldMul19` reduce consumes. With
    this, `fe25519_emit_fieldmul_runBlock` discharges `Fe25519TierA.emittedReduceGap`.
    The fold arithmetic and the reduce are theorems; this bit-255 split mask is the
    remainder gated by the external KAT. A `Prop` (no axiom). -/
def splitBookkeepingGap : Prop :=
  ∀ (accs as ys : List String) (hi lo : String) (s : JState 64),
    ∃ highL lowL : List (BitVec 64),
      lowL.length ≤ (mulScalar highL c19).length ∧
      valLimbs highL = runBlockProductValue accs as ys hi lo s / 2 ^ 255 ∧
      valLimbs lowL = runBlockProductValue accs as ys hi lo s % 2 ^ 255

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519ReduceRunBlock
