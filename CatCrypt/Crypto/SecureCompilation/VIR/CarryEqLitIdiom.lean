/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

set_option autoImplicit false

/-!
# C6 instruction-selection bridges: carry and equality-literal idioms

This module proves two `BitVec` bridge lemmas that document why the
compile-from-hax front-end needs no special reg-1-result ALU dialect ops for
the carry-add data word and the equality-literal test.  Both are C6
instruction-selection targets: the front emits the homogeneous two-`add` or
XOR/OR/shift idiom, and C6 maps it to the efficient x86 instruction.

## Lemma 1 — `addCarryWord` = two homogeneous adds

`JasminDialect.addCarryWord a b cin` is the data word of a carry-chain add.
Its definition `a + b + BitVec.ofNat w cin.toNat` is already the explicit
left-associative two-`add` form, so the front needs no special `addCarryLo`
op: two `regArith .add` ops suffice.  (`addCarryLo` is the C6 target that
collapses the pair to a single `ADCX`/`ADOX`.)

## Lemma 2 — `isEqLitIdiom` = the if-equal result

The `thir_eqlit` leaf implements the tag test `a == ofNat w k` via the
constant-time branchless idiom

```
x  = a ^ k
x1 = 0 - x    -- twos-complement negate
x  = x | x1   -- MSB = 1 iff x ≠ 0
x  = x >> (w-1)  -- isolate the "non-zero" bit into the LSB position
x  = 1 - x    -- invert: 1 ↔ a = k
```

`isEqLitIdiom_eq` proves this is semantically equal to `if a = ofNat w k then 1#w else 0#w`.
The proof is achieved at **general `w`** using `BitVec` equational lemmas
(`BitVec.xor_eq_zero_iff`, `BitVec.msb_neg`, `BitVec.msb_or`, `BitVec.msb_intMin`)
together with a pointwise shift characterization (`getLsbD`-based).

The `thEqLit` denotation in `ThirDialect` is the opaque leaf `jasminExtSem`;
`isEqLitIdiom_eq` is the in-Lean value-correctness certificate that the
concrete bitwise body implements the spec.  The leaf's full KAT discharge
(against the reference implementation) is an external obligation.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open JasminDialect

/-! ## 1. `addCarryWord` = two homogeneous adds -/

/-- **Carry-add data word = two homogeneous adds** (C6 bridge, `addCarryLo`).
    `addCarryWord a b cin` is definitionally `a + b + BitVec.ofNat w cin.toNat`,
    which is the explicit left-to-right two-`regArith .add` form.  The front
    therefore emits just two homogeneous add ops for the data word of a
    carry-chain step — no special-purpose `addCarryLo` dialect op is needed in
    the front.  `addCarryLo` is the C6 instruction-selection target that
    collapses the pair to a single `ADCX`/`ADOX`. -/
theorem addCarryWord_eq_twoAdds {w : Nat} (a b : BitVec w) (cin : BitVec 1) :
    addCarryWord a b cin = (a + b) + BitVec.ofNat w cin.toNat := by
  simp [addCarryWord]

/-! ## 2. `isEqLitIdiom` and its general-`w` correctness proof -/

/-- The branchless equality-literal idiom used by the `thir_eqlit` leaf:
    ```
    x  = a ^^^ ofNat w k        -- a XOR k
    x1 = 0#w - x                -- twos-complement negate
    x  = x ||| x1               -- MSB = 1 iff x ≠ 0 (OR-with-negate test)
    x  = x >>> (w - 1)          -- logical right-shift to isolate MSB → {0,1}
    x  = 1#w - x                -- invert: 1 ↔ x was 0 ↔ a = k
    ```
    Result type is `BitVec w`; the `thEqLit` leaf appends a width-1 truncation
    (`reg 1`) to yield the 1-bit tag-test result.  `isEqLitIdiom_eq` proves
    the idiom equals `if a = ofNat w k then 1#w else 0#w` for all `w`. -/
def isEqLitIdiom {w : Nat} (a : BitVec w) (k : Nat) : BitVec w :=
  let x := a ^^^ BitVec.ofNat w k
  1#w - (((x ||| (0#w - x)) >>> (w - 1)))

/-! ### Auxiliary lemmas for the general-`w` proof -/

/-- **Shift-by-(w-1) extracts the MSB** (general `w ≥ 1`): `v >>> (w-1)` equals
    `1#w` when `v.msb = true` and `0#w` otherwise.  Proved by a bitwise
    extension argument: `getLsbD j` of the shifted value equals `getLsbD (w-1)`
    of `v` when `j = 0` (the only in-range bit), and `false` for `j ≥ 1`
    (out-of-range, `BitVec.getLsbD_of_ge`). -/
private theorem ushiftRight_wm1_eq_msb {w : Nat} (hw : 0 < w) (v : BitVec w) :
    v >>> (w - 1) = if v.msb then 1#w else 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  rw [BitVec.getLsbD_ushiftRight]
  by_cases hmsb : v.msb
  · simp only [hmsb, ↓reduceIte, BitVec.getLsbD_one, hw, decide_true, Bool.true_and]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [Nat.add_zero, decide_true]
      rwa [← BitVec.msb_eq_getLsbD_last]
    · simp only [show (decide (i = 0)) = false from by simp [hi0]]
      exact BitVec.getLsbD_of_ge v _ (by omega)
  · simp only [Bool.not_eq_true] at hmsb
    simp only [hmsb, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_zero]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [Nat.add_zero]
      rw [← BitVec.msb_eq_getLsbD_last]; simp [hmsb]
    · exact BitVec.getLsbD_of_ge v _ (by omega)

/-- **MSB of `x ||| (-x)` = is-nonzero flag** (general `w ≥ 1`): `(x ||| -x).msb`
    is `true` iff `x ≠ 0#w`.

    Proof sketch: `msb_or` gives `x.msb || (-x).msb`.  If `x.msb = true`,
    done.  If `x.msb = false` and `x ≠ 0`, then `x.toNat ∈ [1, 2^(w-1)-1]`,
    so `-x = 2^w - x.toNat ∈ [2^(w-1)+1, 2^w-1]`, hence `(-x).msb = true`.
    Formally: `msb_neg` gives `(-x).msb = (x ≠ 0 ∧ x ≠ intMin w) ^^^ x.msb`;
    when `x.msb = false` and `x ≠ 0`, `x ≠ intMin w` follows because
    `intMin w` has `msb = true` (`BitVec.msb_intMin`). -/
private theorem msb_or_neg {w : Nat} (hw : 0 < w) (x : BitVec w) :
    (x ||| -x).msb = decide (x ≠ 0#w) := by
  rw [BitVec.msb_or, BitVec.msb_neg]
  by_cases hxz : x = 0#w
  · subst hxz; simp [BitVec.msb_zero]
  · simp only [ne_eq, hxz, not_false_eq_true, decide_true]
    by_cases hmsb : x.msb = true
    · simp [hmsb]
    · simp only [Bool.not_eq_true] at hmsb
      simp only [hmsb, Bool.false_or, Bool.xor_false]
      rw [Bool.and_eq_true]
      exact ⟨bne_iff_ne.mpr hxz, by
        rw [bne_iff_ne]
        intro heq
        have : (BitVec.intMin w).msb = true := by
          rw [BitVec.msb_intMin]; simp [hw]
        rw [← heq, hmsb] at this
        exact absurd this (by decide)⟩

/-- **OR-with-negate shift** (sub-lemma): for any `x : BitVec w`,
    `(x ||| (0#w - x)) >>> (w-1) = if x = 0#w then 0#w else 1#w`.

    This is the core of `isEqLitIdiom_eq`: the shift extracts the MSB of
    `x ||| (-x)`, which is the "is-nonzero" bit.  For `w = 0` every `BitVec 0`
    is `0#0`; for `w ≥ 1` use `ushiftRight_wm1_eq_msb` and `msb_or_neg`. -/
private theorem or_neg_ushiftRight_wm1 {w : Nat} (x : BitVec w) :
    (x ||| (0#w - x)) >>> (w - 1) = if x = 0#w then 0#w else 1#w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hx0 : x = 0#0 := BitVec.eq_of_toNat_eq (by
        simp [Nat.lt_one_iff.mp x.isLt])
    subst hx0; simp
  · rw [BitVec.zero_sub, ushiftRight_wm1_eq_msb hw, msb_or_neg hw]
    by_cases hxz : x = 0#w <;> simp [hxz]

/-! ### Main theorem -/

/-- **Equality-literal idiom correctness** (general `w`, C6 bridge, `thEqLit`).
    `isEqLitIdiom a k = if a = BitVec.ofNat w k then 1#w else 0#w`.

    The front emits the five-op XOR/OR/negate/shift/subtract idiom for the
    `thir_eqlit` leaf.  This theorem says it computes the same value as the
    spec `if a = k then 1 else 0`.  The key steps:

    1. `a = ofNat w k ↔ a ^^^ ofNat w k = 0#w`  (`BitVec.xor_eq_zero_iff`).
    2. `(x ||| (0 - x)) >>> (w-1) = if x = 0 then 0 else 1`
       (`or_neg_ushiftRight_wm1`, the MSB of `x | -x` is the is-nonzero bit).
    3. `1 - (if x=0 then 0 else 1) = if x=0 then 1 else 0` (`simp`).

    **Proof coverage**: general `w` (including `w = 0`, handled separately). -/
theorem isEqLitIdiom_eq {w : Nat} (a : BitVec w) (k : Nat) :
    isEqLitIdiom a k = (if a = BitVec.ofNat w k then 1#w else 0#w) := by
  unfold isEqLitIdiom
  dsimp only []
  have ha_eq_iff : a ^^^ BitVec.ofNat w k = 0#w ↔ a = BitVec.ofNat w k :=
    BitVec.xor_eq_zero_iff
  rw [or_neg_ushiftRight_wm1 (a ^^^ BitVec.ofNat w k)]
  by_cases hxz : a ^^^ BitVec.ofNat w k = 0#w
  · rw [if_pos hxz, if_pos (ha_eq_iff.mp hxz)]; simp
  · rw [if_neg hxz, if_neg (fun h => hxz (ha_eq_iff.mpr h))]; simp

end CatCrypt.Crypto.SecureCompilation.VIR
