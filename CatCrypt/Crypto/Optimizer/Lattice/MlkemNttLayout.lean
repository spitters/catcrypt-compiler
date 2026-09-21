/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec

/-!
# A 16 × 16 storage layout on `Fin 256`, and the 256-point DFT at `ω = 17`
  over `ZMod 3329` in bit-reversed order

This file has two parts.

1. The storage layout permutation `mlkemNttStorageLayout : Equiv.Perm (Fin 256)`,
   the vector-major / lane-minor map `(v, l) ↦ 16·v + l` for a 256-coefficient
   polynomial held as 16 vectors of 16 lanes, where slot `v` (`0 … 15`) holds 16
   consecutive coefficients and lane `l` (`0 … 15`) of slot `v` is the
   coefficient at linear position `16·v + l`.  It is `finProdFinEquiv`
   repackaged and acts as the identity on the linear index.
2. `mlkemNttKernelSpec`, defined as the iterative decimation-in-time transform
   `nttIter 8 17` over `ZMod 3329`, i.e. the full 256-point DFT at `ω = 17` with
   output in bit-reversed order, together with theorems relating it to the
   definitional `dft 256 17` through the transform-order permutation
   `bitrevPerm 8` from the proved iterative-transform specification.

## What `mlkemNttKernelSpec` is not

`nttIter 8 17` is a full 256-point DFT of `Z_3329[X]/(X^256 − 1)`.  It is not
FIPS 203's ML-KEM transform: ML-KEM's NTT is the incomplete 7-layer transform
of `Z_3329[X]/(X^256 + 1)` into 128 quadratic residues, and no full negacyclic
diagonalisation exists at this modulus because `3328 = 2^8 · 13` gives
`ZMod 3329` no element of order 512 (`ConcreteNttInstances.lean`, "ML-KEM is
cyclic here, not negacyclic").  A kernel that agrees with
`PQCLEAN_MLKEM768_CLEAN_ntt` computes the FIPS 203 transform, so its value is
not `mlkemNttKernelSpec`.  The owned ML-KEM NTT that passes the NIST KAT is a
separate artifact and is not described by this file.

## The two index permutations

* The I/O storage layout: how the 256 coefficient words sit in 16 vectors.  A
  kernel that loads and stores the polynomial linearly (slot/lane position
  `16·v + l` holds coefficient `16·v + l`) exposes `finProdFinEquiv` as its
  storage-to-linear map, i.e. linear order.  `mlkemNttStorageLayout` records
  this map and `mlkemNttStorageLayout_apply` proves it is the identity on the
  linear index.

* The transform-order permutation: a decimation-in-time transform leaves its
  output in bit-reversed frequency order.  This is `bitrevPerm 8`, and the
  whole-transform theorems route it through `nttIter_eq_nttRec_comp_bitrev`.

## What is proved

`mlkemNttKernelSpec x k = nttIter 8 17 x k` by definition.  The theorem

`mlkemNttKernelSpec_eq_dft_bitrev :`
`    mlkemNttKernelSpec x k = dft 256 ω (fun j ↦ x (bitrevPerm 8 j)) k`

relates the layer-fold, position by position over all 256 outputs, to the
definitional length-256 `dft` of the bit-reversed input, from
`nttIter_eq_nttRec_comp_bitrev` and `nttRec_eq_dft`.  The companion
`mlkemNttKernelSpec_bitrev_eq_dft` is the natural-input form: the transform of
the bit-reversed input is `dft` in natural index order.
`mlkemNttKernelSpec_storage_eq_dft_bitrev` composes with the storage layout,
which contributes nothing beyond the linear order.

## Scope

The file is at the specification level, over the in-Lean `dft`/`nttIter`
definitions.  No theorem here relates `mlkemNttKernelSpec` to the machine bytes
or the denotation of any emitted kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.MlkemNttLayout

open CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
open CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass

/-! ## 1. The storage layout permutation -/

/-- The 16-vector storage layout as a permutation of the 256 linear coefficient
indices, through the vector-major / lane-minor bijection
`Fin 16 × Fin 16 ≃ Fin 256`, `(v, l) ↦ 16·v + l`. `finProdFinEquiv` gives
`(v, l) ↦ l + 16·v`, the linear index of slot `v`, lane `l`. -/
def mlkemNttStorageLayout : Equiv.Perm (Fin 256) :=
  -- `finProdFinEquiv : Fin 16 × Fin 16 ≃ Fin (16*16)`; compose with its inverse
  -- to land back on `Fin 256` (= `Fin (16*16)` definitionally), i.e. read the
  -- (slot, lane) coordinates off a linear index and re-pack them linearly.
  -- This is the identity permutation written through the slot/lane coordinates.
  (finProdFinEquiv.symm.trans finProdFinEquiv :
    Fin (16 * 16) ≃ Fin (16 * 16))

/-- The linear index of slot `v`, lane `l` is `16·v + l`. This is the storage
layout's defining equation, read off `finProdFinEquiv`. -/
theorem mlkemNttStorageLayout_coord (v l : Fin 16) :
    (finProdFinEquiv (v, l) : Fin (16 * 16)).val = l.val + 16 * v.val := by
  rw [finProdFinEquiv_apply_val]

/-- The storage layout is the identity on linear indices: reading off
(slot, lane) coordinates and re-packing them recovers the same linear
position. -/
@[simp] theorem mlkemNttStorageLayout_apply (i : Fin 256) :
    mlkemNttStorageLayout i = i := by
  simp [mlkemNttStorageLayout]

/-- `mlkemNttStorageLayout` is a bijection: it is an `Equiv.Perm` by
construction, and concretely the identity permutation. -/
theorem mlkemNttStorageLayout_bijective :
    Function.Bijective mlkemNttStorageLayout :=
  mlkemNttStorageLayout.bijective

/-! ## 2. The 256-point DFT at `ω = 17` in bit-reversed output order -/

/-- The root `ω = 17 : ZMod 3329`, a primitive 256-th root of unity
(`ConcreteNttRoots.isPrimitiveRoot_17_256`). -/
abbrev mlkemOmega : ZMod 3329 := 17

/-- The iterative decimation-in-time transform `nttIter 8 17` over `ZMod 3329`
at natural-order input `x` and output position `k`: the full 256-point DFT at
`ω = 17` with output in bit-reversed order (8 butterfly layers).
It is a transform of `Z_3329[X]/(X^256 − 1)` and is not FIPS 203's 7-layer
ML-KEM transform of `X^256 + 1` (module docstring). -/
def mlkemNttKernelSpec (x : Fin (2 ^ 8) → ZMod 3329) (k : Fin (2 ^ 8)) :
    ZMod 3329 :=
  nttIter 8 mlkemOmega x k

/-- Bit-reversed-input form: `mlkemNttKernelSpec` on the bit-reversed input
equals the definitional length-256 `dft` of the natural-order input.  This is
`nttIter_comp_bitrev_eq_dft` at `n = 8`, `ω = 17`, given `ω ^ 256 = 1`, at
every output position `k`. -/
theorem mlkemNttKernelSpec_bitrev_eq_dft (x : Fin (2 ^ 8) → ZMod 3329)
    (hω : mlkemOmega ^ (2 ^ 8) = 1) (k : Fin (2 ^ 8)) :
    mlkemNttKernelSpec (fun j => x ((bitrevPerm 8) j)) k
      = dft (2 ^ 8) mlkemOmega x k := by
  unfold mlkemNttKernelSpec
  exact nttIter_comp_bitrev_eq_dft 8 mlkemOmega hω x k

/-- Natural-input form: `mlkemNttKernelSpec` on natural-order input equals the
length-256 `dft` of the bit-reversed input, i.e. the decimation-in-time
transform leaves its output in bit-reversed frequency order.  Permutation
algebra over `nttIter_eq_nttRec_comp_bitrev` and `nttRec_eq_dft`; the
bit-reversal `bitrevPerm 8` is the transform-order permutation. -/
theorem mlkemNttKernelSpec_eq_dft_bitrev (x : Fin (2 ^ 8) → ZMod 3329)
    (hω : mlkemOmega ^ (2 ^ 8) = 1) (k : Fin (2 ^ 8)) :
    mlkemNttKernelSpec x k
      = dft (2 ^ 8) mlkemOmega (fun j => x ((bitrevPerm 8) j)) k := by
  unfold mlkemNttKernelSpec
  rw [nttIter_eq_nttRec_comp_bitrev 8 mlkemOmega x k,
    NTTRecursiveFull.nttRec_eq_dft 8 mlkemOmega hω]

/-- The natural-input form through the (identity) storage layout: applying the
storage layout to the output index does not change the value, so the transform
at storage position `k` is the `dft` of the bit-reversed input at the same
index.  The I/O storage permutation contributes nothing beyond the linear order;
the only non-identity index permutation is `bitrevPerm 8`. -/
theorem mlkemNttKernelSpec_storage_eq_dft_bitrev (x : Fin (2 ^ 8) → ZMod 3329)
    (hω : mlkemOmega ^ (2 ^ 8) = 1) (k : Fin 256) :
    mlkemNttKernelSpec x (mlkemNttStorageLayout k)
      = dft (2 ^ 8) mlkemOmega (fun j => x ((bitrevPerm 8) j)) k := by
  rw [mlkemNttStorageLayout_apply]
  exact mlkemNttKernelSpec_eq_dft_bitrev x hω k

end CatCrypt.Crypto.Optimizer.Lattice.MlkemNttLayout
