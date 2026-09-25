/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.Poseidon2.Width16
public meta import CatCrypt.Crypto.Hash.Poseidon2.Width16
public import CatCryptCore.Tactics.KatGuard

/-!
# Poseidon2 over KoalaBear (width 16)

The width-16 Poseidon2 parameters of Plonky3 over KoalaBear, `p = 2³¹ − 2²⁴ + 1`:
S-box `x ↦ x³`, 4 + 4 external rounds, 20 internal rounds.

## Provenance

The constants are those of `p3-koala-bear` 0.5.4 (`src/poseidon2.rs`, source
commit `da6ca12c71912ec213d3c5af68b14509d2099bc3` of Plonky3), passed there to
`KoalaBear::new_array` as canonical residues:

* `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`, `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`:
  4 + 4 rounds × 16 lanes;
* `KOALABEAR_POSEIDON2_RC_16_INTERNAL`: 20 constants;
* the internal diagonal `V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2⁸, 1/8, 1/2²⁴,
  -1/2⁸, -1/8, -1/16, -1/2²⁴]` of `KoalaBearInternalLayerParameters`.

The known-answer check is `test_default_koalabear_poseidon2_width_16` of the same
file.

## Main definitions

* `params`: the `Width16.Params` record.
* `permute`: the KoalaBear Poseidon2 permutation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Poseidon2.KoalaBear

open CatCrypt.Crypto.Hash.Poseidon2.Width16 (Params permuteNat)

/-- The KoalaBear prime `2³¹ − 2²⁴ + 1`. -/
abbrev P : Nat := 2130706433

/-- `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL` followed by
    `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`. -/
def rcExternalTable : Array (Array Nat) := #[
  #[0x7ee56a48, 0x11367045, 0x12e41941, 0x7ebbc12b, 0x1970b7d5, 0x662b60e8, 0x3e4990c6,
    0x679f91f5, 0x350813bb, 0x00874ad4, 0x28a0081a, 0x18fa5872, 0x5f25b071, 0x5e5d5998,
    0x5e6fd3e7, 0x5b2e2660],
  #[0x6f1837bf, 0x3fe6182b, 0x1edd7ac5, 0x57470d00, 0x43d486d5, 0x1982c70f, 0x0ea53af9,
    0x61d6165b, 0x51639c00, 0x2dec352c, 0x2950e531, 0x2d2cb947, 0x08256cef, 0x1a0109f6,
    0x1f51faf3, 0x5cef1c62],
  #[0x3d65e50e, 0x33d91626, 0x133d5a1e, 0x0ff49b0d, 0x38900cd1, 0x2c22cc3f, 0x28852bb2,
    0x06c65a02, 0x7b2cf7bc, 0x68016e1a, 0x15e16bc0, 0x5248149a, 0x6dd212a0, 0x18d6830a,
    0x5001be82, 0x64dac34e],
  #[0x5902b287, 0x426583a0, 0x0c921632, 0x3fe028a5, 0x245f8e49, 0x43bb297e, 0x7873dbd9,
    0x3cc987df, 0x286bb4ce, 0x640a8dcd, 0x512a8e36, 0x03a4cf55, 0x481837a2, 0x03d6da84,
    0x73726ac7, 0x760e7fdf],
  #[0x43e7dc24, 0x259a5d61, 0x27e85a3b, 0x1b9133fa, 0x343e5628, 0x485cd4c2, 0x16e269f5,
    0x165b60c6, 0x25f683d9, 0x124f81f9, 0x174331f9, 0x77344dc5, 0x5a821dba, 0x5fc4177f,
    0x54153bf5, 0x5e3f1194],
  #[0x3bdbf191, 0x088c84a3, 0x68256c9b, 0x3c90bbc6, 0x6846166a, 0x03f4238d, 0x463335fb,
    0x5e3d3551, 0x6e59ae6f, 0x32d06cc0, 0x596293f3, 0x6c87edb2, 0x08fc60b5, 0x34bcca80,
    0x24f007f3, 0x62731c6f],
  #[0x1e1db6c6, 0x0ca409bb, 0x585c1e78, 0x56e94edc, 0x16d22734, 0x18e11467, 0x7b2c3730,
    0x770075e4, 0x35d1b18c, 0x22be3db5, 0x4fb1fbb7, 0x477cb3ed, 0x7d5311c6, 0x5b62ae7d,
    0x559c5fa8, 0x77f15048],
  #[0x3211570b, 0x490fef6a, 0x77ec311f, 0x2247171b, 0x4e0ac711, 0x2edf69c9, 0x3b5a8850,
    0x65809421, 0x5619b4aa, 0x362019a7, 0x6bf9d4ed, 0x5b413dff, 0x617e181e, 0x5e7ab57b,
    0x33ad7833, 0x3466c7ca]]

/-- The external round constants: row `r`, entry `i` of `rcExternalTable`. -/
def rcExternal (r : Fin 8) (i : Fin 16) : ZMod P :=
  ((rcExternalTable.getD r.val #[]).getD i.val 0 : Nat)

/-- `KOALABEAR_POSEIDON2_RC_16_INTERNAL`. -/
def rcInternalTable : Array Nat := #[
  0x54dfeb5d, 0x7d40afd6, 0x722cb316, 0x106a4573, 0x45a7ccdb, 0x44061375, 0x154077a5,
  0x45744faa, 0x4eb5e5ee, 0x3794e83f, 0x47c7093c, 0x5694903c, 0x69cb6299, 0x373df84c,
  0x46a0df58, 0x46b8758a, 0x3241ebcb, 0x0b09d233, 0x1af42357, 0x1e66cec2]

/-- The internal round constants: entry `r` of `rcInternalTable`. -/
def rcInternal (r : Fin 20) : ZMod P := (rcInternalTable.getD r.val 0 : Nat)

/-- The internal diagonal `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2⁸, 1/8, 1/2²⁴,
    -1/2⁸, -1/8, -1/16, -1/2²⁴]`. -/
def diag : Fin 16 → ZMod P := ![
  -2, 1, 2, (2 : ZMod P)⁻¹, 3, 4, -(2 : ZMod P)⁻¹, -3, -4, (2 ^ 8 : ZMod P)⁻¹,
  (8 : ZMod P)⁻¹, (2 ^ 24 : ZMod P)⁻¹, -(2 ^ 8 : ZMod P)⁻¹, -(8 : ZMod P)⁻¹,
  -(16 : ZMod P)⁻¹, -(2 ^ 24 : ZMod P)⁻¹]

/-- The KoalaBear width-16 Poseidon2 parameters. -/
def params : Params where
  p := P
  sboxDeg := 3
  halfFullRounds := 4
  partialRounds := 20
  rcExternal := rcExternal
  rcInternal := rcInternal
  diag := diag

/-- **The KoalaBear Poseidon2 permutation.** -/
abbrev permute : (Fin 16 → ZMod P) → Fin 16 → ZMod P := Width16.permute params

/-- The input of `test_default_koalabear_poseidon2_width_16`. -/
def katInput : List Nat :=
  [894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
   120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
   1783754913]

/-- The expected output of `test_default_koalabear_poseidon2_width_16`. -/
def katExpected : List Nat :=
  [1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110, 1391183747,
   351743874, 1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461,
   748270449, 651545025]

/-! ## Known-answer check

The Plonky3 test vector, a static check on the constants and on the order of the
layers; by `Width16.permuteNat_eq` it is a statement about `permute`. -/

#kat permuteNat params katInput == katExpected

end CatCrypt.Crypto.Hash.Poseidon2.KoalaBear
