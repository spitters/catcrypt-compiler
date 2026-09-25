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
# Poseidon2 over Mersenne-31 (width 16)

The width-16 Poseidon2 parameters of Plonky3 over `p = 2³¹ − 1`: S-box `x ↦ x⁵`,
4 + 4 external rounds, 14 internal rounds.

## Provenance

The constants are those of `p3-mersenne-31` 0.5.4 (`src/poseidon2.rs`, source
commit `da6ca12c71912ec213d3c5af68b14509d2099bc3` of Plonky3):

* `MERSENNE31_POSEIDON2_RC_16_EXTERNAL_INITIAL`, `MERSENNE31_POSEIDON2_RC_16_EXTERNAL_FINAL`:
  4 + 4 rounds × 16 lanes;
* `MERSENNE31_POSEIDON2_RC_16_INTERNAL`: 14 constants;
* the internal diagonal `V = [-2] ++ [2^s | s ∈ POSEIDON2_INTERNAL_MATRIX_DIAG_16_SHIFTS]`,
  with shifts `[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16]`.

The known-answer check is `test_default_mersenne31_poseidon2_width_16` of the same
file, the permutation of `[0, 1, …, 15]`.

## Main definitions

* `params`: the `Width16.Params` record.
* `permute`: the Mersenne-31 Poseidon2 permutation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Poseidon2.Mersenne31

open CatCrypt.Crypto.Hash.Poseidon2.Width16 (Params permuteNat)

/-- The Mersenne prime `2³¹ − 1`. -/
abbrev P : Nat := 2147483647

/-- `MERSENNE31_POSEIDON2_RC_16_EXTERNAL_INITIAL` followed by
    `MERSENNE31_POSEIDON2_RC_16_EXTERNAL_FINAL`. -/
def rcExternalTable : Array (Array Nat) := #[
  #[0x768bab52, 0x70e0ab7d, 0x3d266c8a, 0x6da42045, 0x600fef22, 0x41dace6b, 0x64f9bdd4,
    0x5d42d4fe, 0x76b1516d, 0x6fc9a717, 0x70ac4fb6, 0x00194ef6, 0x22b644e2, 0x1f7916d5,
    0x47581be2, 0x2710a123],
  #[0x6284e867, 0x018d3afe, 0x5df99ef3, 0x4c1e467b, 0x566f6abc, 0x2994e427, 0x538a6d42,
    0x5d7bf2cf, 0x7fda2dab, 0x0fd854c4, 0x46922fca, 0x3d7763a1, 0x19fd05ca, 0x0a4bbb43,
    0x15075851, 0x3d903d76],
  #[0x2d290ff7, 0x40809fa0, 0x59dac6ec, 0x127927a2, 0x6bbf0ea0, 0x0294140f, 0x24742976,
    0x6e84c081, 0x22484f4a, 0x354cae59, 0x0453ffe1, 0x3f47a3cc, 0x0088204e, 0x6066e109,
    0x3b7c4b80, 0x6b55665d],
  #[0x3bc4b897, 0x735bf378, 0x508daf42, 0x1884fc2b, 0x7214f24c, 0x7498be0a, 0x1a60e640,
    0x3303f928, 0x29b46376, 0x5c96bb68, 0x65d097a5, 0x1d358e9f, 0x4a9a9017, 0x4724cf76,
    0x347af70f, 0x1e77e59a],
  #[0x57090613, 0x1fa42108, 0x17bbef50, 0x1ff7e11c, 0x047b24ca, 0x4e140275, 0x4fa086f5,
    0x079b309c, 0x1159bd47, 0x6d37e4e5, 0x075d8dce, 0x12121ca0, 0x7f6a7c40, 0x68e182ba,
    0x5493201b, 0x0444a80e],
  #[0x0064f4c6, 0x6467abe6, 0x66975762, 0x2af68f9b, 0x345b33be, 0x1b70d47f, 0x053db717,
    0x381189cb, 0x43b915f8, 0x20df3694, 0x0f459d26, 0x77a0e97b, 0x2f73e739, 0x1876c2f9,
    0x65a0e29a, 0x4cabefbe],
  #[0x5abd1268, 0x4d34a760, 0x12771799, 0x69a0c9ac, 0x39091e55, 0x7f611cd0, 0x3af055da,
    0x7ac0bbdf, 0x6e0f3a24, 0x41e3b6f7, 0x49b3756d, 0x568bc538, 0x20c079d8, 0x1701c72c,
    0x7670dc6c, 0x5a439035],
  #[0x7c93e00e, 0x561fbb4d, 0x1178907b, 0x02737406, 0x32fb24f1, 0x6323b60a, 0x6ab12418,
    0x42c99cea, 0x155a0b97, 0x53d1c6aa, 0x2bd20347, 0x279b3d73, 0x4f5f3c70, 0x0245af6c,
    0x238359d3, 0x49966a59]]

/-- The external round constants: row `r`, entry `i` of `rcExternalTable`. -/
def rcExternal (r : Fin 8) (i : Fin 16) : ZMod P :=
  ((rcExternalTable.getD r.val #[]).getD i.val 0 : Nat)

/-- `MERSENNE31_POSEIDON2_RC_16_INTERNAL`. -/
def rcInternalTable : Array Nat := #[
  0x7f7ec4bf, 0x0421926f, 0x5198e669, 0x34db3148, 0x4368bafd, 0x66685c7f, 0x78d3249a,
  0x60187881, 0x76dad67a, 0x0690b437, 0x1ea95311, 0x40e5369a, 0x38f103fc, 0x1d226a21]

/-- The internal round constants: entry `r` of `rcInternalTable`. -/
def rcInternal (r : Fin 14) : ZMod P := (rcInternalTable.getD r.val 0 : Nat)

/-- `POSEIDON2_INTERNAL_MATRIX_DIAG_16_SHIFTS`. -/
def diagShifts : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16]

/-- The internal diagonal: `-2`, then `2 ^ s` for the shifts `s` of `diagShifts`. -/
def diag (i : Fin 16) : ZMod P :=
  if i.val = 0 then -2 else ((2 ^ diagShifts.getD (i.val - 1) 0 : Nat) : ZMod P)

/-- The Mersenne-31 width-16 Poseidon2 parameters. -/
def params : Params where
  p := P
  sboxDeg := 5
  halfFullRounds := 4
  partialRounds := 14
  rcExternal := rcExternal
  rcInternal := rcInternal
  diag := diag

/-- **The Mersenne-31 Poseidon2 permutation.** -/
abbrev permute : (Fin 16 → ZMod P) → Fin 16 → ZMod P := Width16.permute params

/-- The input of `test_default_mersenne31_poseidon2_width_16`. -/
def katInput : List Nat := List.range 16

/-- The expected output of `test_default_mersenne31_poseidon2_width_16`. -/
def katExpected : List Nat :=
  [0x0b2c803a, 0x5b1ee4d1, 0x49c6b1e3, 0x2cdc280c, 0x310a60c8, 0x530a729e, 0x4e61bcb4,
   0x2e84d3c3, 0x58709c08, 0x7e82ac42, 0x2162bcef, 0x6d153ab6, 0x742cf0e3, 0x2f21632d,
   0x61adce1e, 0x1973d6f1]

/-! ## Known-answer check

The Plonky3 test vector, a static check on the constants and on the order of the
layers; by `Width16.permuteNat_eq` it is a statement about `permute`. -/

#kat permuteNat params katInput == katExpected

end CatCrypt.Crypto.Hash.Poseidon2.Mersenne31
