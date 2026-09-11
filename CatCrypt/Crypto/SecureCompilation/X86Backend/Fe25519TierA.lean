/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
public meta import CatCrypt.Crypto.Optimizer.ModReduceSelect
public import CatCrypt.Crypto.Optimizer.ModReduceSelect

/-!
# Tier-A Curve25519 field-multiply over `runBlock` (Solinas `2^255 − 19`)

The 4-limb curve mont-mul kernels are Tier A via the Montgomery radix
(`Curve4LimbTierA`, `sm2_emit_montmul_runBlock_full`). The Curve25519
field-multiply is the last 4-limb *multiply* whose reduction is **Solinas**
(`2^255 − 19`), not Montgomery: `fe25519_mul(z, x, y) = (x · y) mod (2^255 − 19)`
with the high half folded back via `· 19` rather than a Montgomery `n' = 1`
reduction. This file makes it Tier A by the same recipe — the genuine emitted
product over `runBlock` composed with the proven reduction — but with the
Solinas residue (`ModReduceSelect.solinasReduce`/`solinasReduce_eq_mod`) as the
reduction spec.

## The two proven pieces and their composition

* **Product (genuine emit over `runBlock`).**
  `SchoolbookProductRunBlock.emitProductBlock_runBlock_value` proves the emitted
  4×4 schoolbook product block's `runBlock` value, read out of the accumulator
  file, is exactly `valLimbs x · valLimbs y` (axiom-clean, a real emitted
  `List (JInstr 64)`).

* **Reduce (value-proven Solinas residue).**
  `ModReduceSelect.reduce25519_eq_mod` proves, for any `high, low < 2^255`,
  `solinasReduce solinasParams25519 high low = (high·2^255 + low) % (2^255 − 19)`
  — the two-fold-then-conditional-subtract Solinas reduce computes the canonical
  residue at `(k, c) = (255, 19)`.

* **Composition (this file).** The full product `P = valLimbs x · valLimbs y`
  splits at the `2^255` Solinas boundary as `P = high·2^255 + low` with
  `high = P / 2^255`, `low = P % 2^255`. For 4-limb inputs both halves are
  `< 2^255` (`P < 2^510`), so `reduce25519_eq_mod` applies and the Solinas reduce
  of the split equals `P % (2^255 − 19)`. `fe25519_emit_mul_runBlock` chains this
  with `emitProductBlock_runBlock_value`:

      solinasReduce solinasParams25519
        (runBlockProductValue accs as ys hi lo s / 2^255)
        (runBlockProductValue accs as ys hi lo s % 2^255)
        = (valLimbs x · valLimbs y) % (2^255 − 19).

  The multiply is a genuine emitted `runBlock`; the Solinas reduction is the
  value-proven residue. This is Tier A for the Curve25519 field-multiply value:
  `runBlock(emitted product) → Solinas-reduce → (x·y) mod (2^255 − 19)`.

## Scope (honest): the named emitted-reduce remainder

The reduction here is tied at the **value** level (`solinasReduce …`), fed the
genuine `runBlock` product. What is *not* tied in-file is the emitted Solinas
*reduce block* (`ModReduceSelect.fusedReduce25519`, the `· 38`/`· 19` MULX/ADD
carry chain over the four words `t4..t7 → t0..t3` with the bit-255 fold) matching
`solinasReduce` over its own `runBlock`. That `runBlock(fusedReduce25519) =
solinasReduce` identity is the 255-bit, non-64-bit-aligned fold whose 4-limb
carry-chain reconstruction is the obligation `Sm2FieldProven` discharges only at
the 2-word (`k = 64`) Goldilocks scale and which the repo externalises to the GMP
KAT (`bench/x25519_fieldmul_compare`) at 256-bit (the REV-12 discipline). It is
named precisely below as `Fe25519TierA.emittedReduceGap` (a `Prop` statement, no
axiom) so the remainder is explicit. The product is fully Tier A;
the reduce is value-proven; the emitted-reduce-over-`runBlock` block is the
remainder.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519TierA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.Optimizer.ModReduceSelect

/-! ## 1. The Curve25519 modulus `p25519 = 2^255 − 19`

Pinned by `native_decide` to the genuine prime. `solinasParams25519.modulus`
(from `ModReduceSelect`) is `2^255 − 19` by definition; we re-export the value
and the canonical little-endian 4-limb representation. -/

/-- The canonical little-endian 4-limb representation of `p25519 = 2^255 − 19`:
    `[2^64 − 19, 2^64 − 1, 2^64 − 1, 2^63 − 1]`. -/
def p25519Limbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 (2 ^ 64 - 19)
  , BitVec.ofNat 64 (2 ^ 64 - 1)
  , BitVec.ofNat 64 (2 ^ 64 - 1)
  , BitVec.ofNat 64 (2 ^ 63 - 1) ]

/-- The 4-limb representation recombines to the genuine prime `2^255 − 19`,
    which is `solinasParams25519.modulus`. Pinned by `native_decide`. -/
theorem p25519Limbs_value :
    valLimbs p25519Limbs = solinasParams25519.modulus := by
  native_decide

/-- The Solinas modulus at `(k, c) = (255, 19)` is `2^255 − 19`. -/
theorem p25519_modulus_eq : solinasParams25519.modulus = 2 ^ 255 - 19 := by
  native_decide

/-! ## 2. Reduced-input products split below the Solinas boundary

The single-fold `solinasReduce` is exact only when the high half is `< 2^255`
(`SolinasOK.high_lt`). For *reduced* field elements (`valLimbs x, valLimbs yv <
2^255`, the canonical inputs to a field multiply) the product `P < 2^510`, so
`P / 2^255 < 2^255` and `P % 2^255 < 2^255` — both halves are well-formed and
`reduce25519_eq_mod` applies. (This is the standard reduced-input hypothesis the
Montgomery Tier-A headlines also carry: `valLimbs x < p`, `valLimbs yv < p`.) -/

/-- For reduced inputs (`valLimbs x, valLimbs yv < 2^255`), the full product
    `P = valLimbs x · valLimbs yv < 2^510`, so its high half `P / 2^255 < 2^255`
    and low half `P % 2^255 < 2^255` — the well-formedness `reduce25519_eq_mod`
    requires. -/
theorem product_halves_lt (x yv : List (BitVec 64))
    (hx : valLimbs x < 2 ^ 255) (hy : valLimbs yv < 2 ^ 255) :
    valLimbs x * valLimbs yv / 2 ^ 255 < 2 ^ 255 ∧
    valLimbs x * valLimbs yv % 2 ^ 255 < 2 ^ 255 := by
  have hP : valLimbs x * valLimbs yv < 2 ^ 255 * 2 ^ 255 := Nat.mul_lt_mul'' hx hy
  refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos 255)⟩
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 255)]
  rwa [Nat.mul_comm (2 ^ 255) (2 ^ 255)]

/-! ## 3. The reduce-of-split equals the residue, and recombines the split

The Solinas reduce fed the radix-`2^255` split of any `P < 2^510` computes
`P mod (2^255 − 19)`: the split recombines (`high·2^255 + low = P`), and
`reduce25519_eq_mod` gives the residue. -/

/-- For any `P < 2^510`, the Solinas reduce of its radix-`2^255` split computes
    `P mod (2^255 − 19)`. The split recombines to `P` (Euclidean division), and
    both halves are `< 2^255` (so `reduce25519_eq_mod` applies). -/
theorem solinasReduce_split_eq_mod (P : Nat) (hP : P < 2 ^ 255 * 2 ^ 255) :
    solinasReduce solinasParams25519 (P / 2 ^ 255) (P % 2 ^ 255)
      = P % (2 ^ 255 - 19) := by
  have hhi : P / 2 ^ 255 < 2 ^ 255 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 255)]
    rwa [Nat.mul_comm (2 ^ 255) (2 ^ 255)] at hP
  have hlo : P % 2 ^ 255 < 2 ^ 255 := Nat.mod_lt _ (Nat.two_pow_pos 255)
  have hrecon : P / 2 ^ 255 * 2 ^ 255 + P % 2 ^ 255 = P := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod P (2 ^ 255)
  rw [reduce25519_eq_mod hhi hlo, hrecon]

/-! ## 4. Tier A for the Curve25519 field-multiply over `runBlock`

The emitted product over `runBlock` (`emitProductBlock_runBlock_value`,
axiom-clean), reduced by the value-proven Solinas reduce, equals
`(valLimbs x · valLimbs y) mod (2^255 − 19)`. This is Tier A for the Curve25519
field-multiply value: a genuine emitted `runBlock` multiply composed with the
proven `2^255 − 19` residue. -/

/-- **Tier A: Curve25519 field-multiply over `runBlock`.** With reduced 4-limb
    inputs (`valLimbs x, valLimbs y < 2^255`), a cleared accumulator file, the
    `ProdFresh` register layout, matching lengths, enough accumulator words, and
    both carry flags clear:

    * the emitted product block's `runBlock` value is exactly
      `valLimbs x · valLimbs y` (`emitProductBlock_runBlock_value`, a real emitted
      `List (JInstr 64)`); and
    * the value-proven Solinas reduce (`solinasReduce solinasParams25519`) of that
      genuine `runBlock` product value, split at the `2^255` Solinas boundary,
      equals `(valLimbs x · valLimbs y) mod (2^255 − 19)`.

    The multiply is a genuine emitted `runBlock`; the `2^255 − 19` reduction is the
    value-proven residue (`solinasReduce_eq_mod`). This is
    `runBlock(emitted product) → Solinas-reduce → fe25519_mul spec` — Tier A for
    the Curve25519 field-multiply value. The emitted Solinas *reduce block* over
    its own `runBlock` is the named remainder (`emittedReduceGap`). -/
theorem fe25519_emit_mul_runBlock
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hxr : as.map s.get = x) (hyr : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < 2 ^ 255) (hy_red : valLimbs yv < 2 ^ 255) :
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    solinasReduce solinasParams25519
        (runBlockProductValue accs as ys hi lo s / 2 ^ 255)
        (runBlockProductValue accs as ys hi lo s % 2 ^ 255)
      = (valLimbs x * valLimbs yv) % (2 ^ 255 - 19) := by
  have hprod : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hxr hyr hacc0 hcf hof
  refine ⟨hprod, ?_⟩
  rw [hprod]
  exact solinasReduce_split_eq_mod (valLimbs x * valLimbs yv)
    (Nat.mul_lt_mul'' hx_red hy_red)

/-! ## 5. The named emitted-reduce remainder (honest partial Tier A)

`fe25519_emit_mul_runBlock` ties the multiply at the `runBlock` level and the
Solinas reduction at the value level. The remaining gap to a *fully* emitted
Tier-A kernel is that the emitted Solinas reduce block
(`ModReduceSelect.fusedReduce25519`, the `· 38`/`· 19` MULX/ADD carry chain over
the four high words with the bit-255 fold and conditional subtract) computes
`solinasReduce solinasParams25519` over its own `runBlock`. `emittedReduceGap`
states exactly that obligation. It is the 255-bit, non-64-bit-aligned fold whose
4-limb carry-chain reconstruction `Sm2FieldProven` discharges only at the 2-word
(`k = 64`) Goldilocks scale (`fold_matches_solinas`, `condsub_word`) and which the
repo externalises to the GMP / s2n KAT at 256-bit (`bench/x25519_fieldmul_compare`,
the REV-12 discipline). Stated as a `Prop` (no axiom); proving it is
the 4-limb generalisation of `Sm2FieldProven`'s 2-word fold reconstruction. -/

/-- Read four 64-bit words little-endian as a `Nat`. -/
def limbVal4 (a0 a1 a2 a3 : BitVec 64) : Nat :=
  a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat

/-- The named emitted-reduce remainder: that the emitted Solinas reduce block
    `fusedReduce25519`, run over `runBlock` on a state whose product high/low
    words are register-resident in `t4..t7`/`t0..t3`, produces in its result words
    `z[0..3]` the little-endian value `solinasReduce solinasParams25519 high low`,
    for product halves `high = P / 2^255`, `low = P % 2^255`. This is the 4-limb
    (255-bit) generalisation of `Sm2FieldProven.fold_matches_solinas` +
    `condsub_word` (proven there at the 2-word Goldilocks scale); the 256-bit
    instance is gated by the external KAT. A `Prop` (no axiom). -/
def emittedReduceGap : Prop :=
  ∀ (s : JState 64) (P : Nat), P < 2 ^ 255 * 2 ^ 255 →
    -- the product low half t0..t3 and high half t4..t7 encode `P`
    (P % 2 ^ 255 = limbVal4 (s.get "t0") (s.get "t1") (s.get "t2") (s.get "t3")) →
    (P / 2 ^ 255 = limbVal4 (s.get "t4") (s.get "t5") (s.get "t6") (s.get "t7")) →
    let sf := runBlock s fusedReduce25519
    limbVal4 (sf.load "z" 0) (sf.load "z" 8) (sf.load "z" 16) (sf.load "z" 24)
      = solinasReduce solinasParams25519 (P / 2 ^ 255) (P % 2 ^ 255)

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519TierA
