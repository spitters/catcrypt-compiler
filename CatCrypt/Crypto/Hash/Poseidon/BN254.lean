/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.Poseidon.Grain
public meta import CatCrypt.Crypto.Hash.Poseidon.Grain
public import CatCrypt.Crypto.Hash.Poseidon.Permutation
public meta import CatCrypt.Crypto.Hash.Poseidon.Permutation
public import CatCryptCore.Tactics.KatGuard

/-!
# Poseidon over the BN254 scalar field, circomlib parameters

The width-3 Poseidon permutation of circomlib and Semaphore over the scalar field
`ZMod r` of BN254 (alt_bn128), `r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`:
S-box `x ↦ x⁵`, 8 full and 57 partial rounds. `hash2 a b` is circomlib
`poseidon([a, b])`, lane `0` of the permutation of `(0, a, b)`.

## Provenance of the constants

The round constants and the MDS matrix are not transcribed: they are
`Grain.constants r 254 3 8 57`, the output of the Grain LFSR procedure of the
Poseidon reference `generate_parameters_grain.sage` (field type `1`, S-box type `0`,
field size 254, width 3, 8 full and 57 partial rounds), from which circomlib's
`poseidon_constants.js` was generated. The MDS matrix is the Cauchy matrix
`M i j = (xᵢ + yⱼ)⁻¹` on the six points drawn after the round constants.

The static checks below compare this derivation with circomlib: the first round
constant is entry `C[1][0]` of `poseidon_constants.js` in `iden3/circomlibjs`
(commit `fe43791f413959cbfcb485b8d27bafac5b9a473d`), and `hash2 1 2` is the circomlib
test vector `poseidon([1, 2]) = 0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a`.

## Main definitions

* `r`: the BN254 scalar-field modulus.
* `grain3`, `mds3`, `params3`: the constants and the parameter record.
* `permute3`, `hash2`: the permutation and the 2-to-1 hash.
* `hash2Nat`: `hash2` through `permuteVec`, on canonical representatives.

## Main results

* `hash2Nat_eq`: `hash2Nat` is the value of `hash2`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Poseidon.BN254

open CatCrypt.Crypto.Hash.Poseidon

/-- The order `r` of the BN254 (alt_bn128) group, the scalar field of the curve. -/
abbrev r : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The Grain constants of width 3: 8 full and 57 partial rounds over the 254-bit
    field `ZMod r`. -/
def grain3 : List Nat × List Nat := Grain.constants r 254 3 8 57

/-- The width-3 Cauchy matrix `M i j = (xᵢ + yⱼ)⁻¹`, row-major. -/
def mds3 : List (ZMod r) :=
  (List.range 9).map fun n =>
    ((grain3.2.getD (n / 3) 0 : ZMod r) + (grain3.2.getD (3 + n % 3) 0 : ZMod r))⁻¹

/-- The width-3 circomlib parameters: `x ↦ x⁵`, 8 full and 57 partial rounds, and the
    round constants and Cauchy matrix of `grain3`. -/
def params3 : Params r 3 where
  fullRounds := 8
  partialRounds := 57
  alpha := 5
  rc k i := (grain3.1.getD (3 * k + i.val) 0 : ZMod r)
  mds i j := mds3.getD (3 * i.val + j.val) 0

/-- The width-3 permutation. -/
abbrev permute3 : (Fin 3 → ZMod r) → Fin 3 → ZMod r := permute params3

/-- **circomlib `poseidon([a, b])`**: lane `0` of the permutation of `(0, a, b)`. -/
def hash2 (a b : ZMod r) : ZMod r := permute3 ![0, a, b] 0

/-- `hash2` through `permuteVec`, on canonical representatives. -/
def hash2Nat (a b : Nat) : Nat :=
  (permuteVec params3 (Vector.ofFn ![0, (a : ZMod r), (b : ZMod r)]))[(0 : Fin 3)].val

/-! ## Static checks

The first check pins `Grain.block` to sixteen single steps of `Grain.step` on the
first 200 blocks of the width-3 stream. The second pins the Cauchy points (the six
values are distinct and no sum `xᵢ + yⱼ` vanishes, so the reference procedure keeps
its first matrix), the first round constant to `C[1][0]` of circomlib
`poseidon_constants.js`, and, by `hash2Nat_eq`, `hash2 1 2` to the circomlib test
vector. -/

#kat Grain.blockAgrees 200 (Grain.init 1 0 254 3 8 57)

#kat grain3.1.length == 195 && grain3.2.length == 6 && (grain3.2.map (· % r)).Nodup &&
  ((List.range 9).all fun n =>
    (grain3.2.getD (n / 3) 0 + grain3.2.getD (3 + n % 3) 0) % r != 0) &&
  grain3.1.head? == some 0x0ee9a592ba9a9518d05986d656f40c2114c4993c11bb29938d21d47304cd8e6e &&
  hash2Nat 1 2 == 0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a

theorem hash2Nat_eq (a b : Nat) : hash2Nat a b = (hash2 a b).val := by
  rw [hash2Nat, permuteVec_get, hash2]
  congr 2
  funext j
  simp

end CatCrypt.Crypto.Hash.Poseidon.BN254
