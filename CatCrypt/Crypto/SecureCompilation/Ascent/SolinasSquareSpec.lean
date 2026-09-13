/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel

/-!
# The field specification of fiat-crypto's `curve25519_solinas` square

fiat-crypto's `SolinasReduction` pipeline (`PushButtonSynthesis/SolinasReduction.v`,
`square_correct`) proves, for `m = 2^255 - 19` over four saturated 64-bit limbs,
the predicate `sqr_correct` of `COperationSpecifications.v`: for every input whose
limbs are bounded by `saturated_bounds` (each limb in `[0, 2^64)`),

* `eval (sqr x) mod m = (eval x * eval x) mod m`, and
* the output limbs are bounded by `saturated_bounds`.

The output is not required to be below `m`. Over `BitVec 64` limbs the two limb
bounds hold by construction, so the specification is the congruence alone.
CryptOpt's `fiat_curve25519_solinas_square` (`SolinasSquareBlock`) is an
implementation of this function.

The limb value and the modulus are those of `Fe25519MulKernel`: `eval4` reads a
limb vector through `Fe25519MulKernel.limbsNat` and `curve25519P` is
`Fe25519MulKernel.p25519`.

## Main results

* `eval4`, `curve25519P`: the little-endian value of four limbs and `2^255 - 19`.
* `SolinasSquareSpec inp out`: `eval4 out ≡ eval4 inp ^ 2 (mod 2^255 - 19)`.
* `limbsOfNat`, `eval4_limbsOfNat`: the four base-`2^64` digits of a number below
  `2^256`, and their value.
* `solinasSquareRef`, `solinasSquareRef_spec`: a reference square (the canonical
  residue split into limbs) meets the specification.
* `not_solinasSquareSpec_two_five`: the specification rejects `5` as the square
  of `2`.
* `solinasSquareSpec_noncanonical`: the specification accepts the non-canonical
  output `4 + p` for the input `2`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.SolinasSquare

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (limbsNat p25519)

/-- The little-endian value `l 0 + 2^64 l 1 + 2^128 l 2 + 2^192 l 3` of four
    64-bit limbs. -/
abbrev eval4 (l : Fin 4 → BitVec 64) : Nat :=
  limbsNat (l 0) (l 1) (l 2) (l 3)

/-- The Curve25519 field modulus `2^255 - 19`. -/
abbrev curve25519P : Nat := p25519

/-- fiat-crypto's `sqr_correct` for `curve25519_solinas` square over 64-bit limbs:
    the output value is congruent to the square of the input value modulo
    `2^255 - 19`. -/
def SolinasSquareSpec (inp out : Fin 4 → BitVec 64) : Prop :=
  eval4 out % curve25519P = (eval4 inp * eval4 inp) % curve25519P

/-- The four base-`2^64` digits of `v`, least significant first. -/
def limbsOfNat (v : Nat) : Fin 4 → BitVec 64 :=
  fun i => BitVec.ofNat 64 (v / 2 ^ (64 * i.val))

/-- The digits of a number below `2^256` have that number as their value. -/
theorem eval4_limbsOfNat (v : Nat) (hv : v < 2 ^ 256) : eval4 (limbsOfNat v) = v := by
  simp only [eval4, limbsNat, limbsOfNat, BitVec.toNat_ofNat, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  have h3 : ((3 : Fin 4) : Nat) = 3 := rfl
  rw [h3]
  omega

/-- The modulus is below `2^256`. -/
theorem curve25519P_lt : curve25519P < 2 ^ 256 := by
  simp only [curve25519P, p25519]; omega

/-- The modulus is positive. -/
theorem curve25519P_pos : 0 < curve25519P := by
  simp only [curve25519P, p25519]; omega

/-- The reference square: the canonical residue of `eval4 inp ^ 2` modulo
    `2^255 - 19`, split into four limbs. -/
def solinasSquareRef (inp : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 :=
  limbsOfNat ((eval4 inp * eval4 inp) % curve25519P)

/-- The value of the reference square is the canonical residue. -/
theorem eval4_solinasSquareRef (inp : Fin 4 → BitVec 64) :
    eval4 (solinasSquareRef inp) = (eval4 inp * eval4 inp) % curve25519P :=
  eval4_limbsOfNat _ (lt_trans (Nat.mod_lt _ curve25519P_pos) curve25519P_lt)

/-- The reference square meets the specification. -/
theorem solinasSquareRef_spec (inp : Fin 4 → BitVec 64) :
    SolinasSquareSpec inp (solinasSquareRef inp) := by
  unfold SolinasSquareSpec
  rw [eval4_solinasSquareRef, Nat.mod_mod]

/-- The specification rejects `5` as the square of `2`. -/
theorem not_solinasSquareSpec_two_five :
    ¬ SolinasSquareSpec (limbsOfNat 2) (limbsOfNat 5) := by
  unfold SolinasSquareSpec
  rw [eval4_limbsOfNat 2 (by omega), eval4_limbsOfNat 5 (by omega)]
  simp only [curve25519P, p25519]
  omega

/-- The specification accepts the output `4 + (2^255 - 19)` for the input `2`: it
    constrains the output value modulo `2^255 - 19` only. -/
theorem solinasSquareSpec_noncanonical :
    SolinasSquareSpec (limbsOfNat 2) (limbsOfNat (4 + curve25519P)) := by
  unfold SolinasSquareSpec
  rw [eval4_limbsOfNat 2 (by omega),
    eval4_limbsOfNat _ (by simp only [curve25519P, p25519]; omega)]
  simp only [curve25519P, p25519]
  omega

end CatCrypt.Crypto.SecureCompilation.Ascent.SolinasSquare
