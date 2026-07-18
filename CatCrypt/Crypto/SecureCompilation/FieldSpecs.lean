/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
import Mathlib

/-!
# High-level field specifications (P256, P384, Poly1305, BabyBear)

The `ZMod p` specs the compiled field arithmetic targets, for the standard primes
the missing-spec list names. The multi-limb kernels (`MultiLimbKernel`) compute the
exact integer products/sums against `bignumVal`; these definitions fix the
mathematical field each kernel reduces into. A field operation is correct when its
output limb-value equals the `ZMod p` field result (the `*_zmod` lemmas already do
this for BabyBear; the larger primes reduce the multi-limb product mod `p`).
-/

namespace CatCrypt.Crypto.SecureCompilation.FieldSpecs

/-- The NIST P-256 prime `2^256 - 2^224 + 2^192 + 2^96 - 1`. -/
def p256 : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The NIST P-384 prime `2^384 - 2^128 - 2^96 + 2^32 - 1`. -/
def p384 : Nat := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

/-- The Poly1305 prime `2^130 - 5`. -/
def poly1305P : Nat := 2 ^ 130 - 5

/-- BabyBear `2^31 - 2^27 + 1` (plonky3's field). -/
def babyBear : Nat := 2013265921

/-- **The field spec for a prime `p`**: arithmetic in `ZMod p`. The compiled
    multi-limb kernel realises `a * b` as an integer (`MultiLimbKernel.mulBignum_val`);
    the field result is its `ZMod p` reduction. -/
def fieldMul (p : Nat) (a b : ZMod p) : ZMod p := a * b
def fieldAdd (p : Nat) (a b : ZMod p) : ZMod p := a + b

/-- The spec is exactly `ZMod p` multiplication — the reduction of the integer
    product, the value the multi-limb multiply kernel produces. -/
theorem fieldMul_val (p : Nat) [NeZero p] (a b : Nat) :
    (fieldMul p (a : ZMod p) (b : ZMod p)).val = (a * b) % p := by
  rw [fieldMul, ← Nat.cast_mul, ZMod.val_natCast]

theorem fieldAdd_val (p : Nat) [NeZero p] (a b : Nat) :
    (fieldAdd p (a : ZMod p) (b : ZMod p)).val = (a + b) % p := by
  rw [fieldAdd, ← Nat.cast_add, ZMod.val_natCast]

/-! ## Poly1305 MAC spec (the Horner polynomial fold over `ZMod (2^130-5)`)

The Poly1305 message-authentication core: evaluate the message polynomial at the key
`r` by Horner's rule over the prime field, `acc ← (acc + block)·r`. (The final
`+ s mod 2^128` is the trusted output-encoding layer.) Each step is exactly the
field add+mul the compiled kernels realise. -/

/-- The Poly1305 polynomial-evaluation MAC over `ZMod (2^130-5)`. -/
def poly1305Mac (r : ZMod poly1305P) (blocks : List (ZMod poly1305P)) : ZMod poly1305P :=
  blocks.foldl (fun acc m => (acc + m) * r) 0

/-- One Horner step is a field add followed by a field multiply — the operations the
    kernels compute, so the MAC is a fold of verified field ops. -/
theorem poly1305Mac_step (r acc m : ZMod poly1305P) :
    poly1305Mac r [m] = fieldMul poly1305P (fieldAdd poly1305P 0 m) r := by
  simp [poly1305Mac, fieldMul, fieldAdd]

/-! ## plonky3 / FRI: the NTT butterfly spec over `ZMod p`

The radix-2 NTT butterfly `(a, b) ↦ (a + ω·b, a − ω·b)` is the inner operation of
the number-theoretic transform plonky3's FRI low-degree test runs over the BabyBear
field — built from one field multiply and a field add/subtract, the verified kernels.
This fixes the butterfly spec; routing the full transform/FRI is the prover layer. -/

/-- The radix-2 decimation NTT butterfly over `ZMod p` (twiddle `ω`). -/
def nttButterfly (p : Nat) (ω a b : ZMod p) : ZMod p × ZMod p := (a + ω * b, a - ω * b)

/-- The butterfly decomposes into the verified field operations: a multiply `ω·b`,
    then a field add and a field subtract. -/
theorem nttButterfly_eq (p : Nat) (ω a b : ZMod p) :
    nttButterfly p ω a b = (fieldAdd p a (fieldMul p ω b), a - fieldMul p ω b) := by
  simp [nttButterfly, fieldAdd, fieldMul]

/-! ## FRI: the folding step

FRI's low-degree test folds a polynomial split into even/odd parts by a random
challenge `β`: `f'(y) = f_even(y) + β·f_odd(y)`, halving the degree each round. The
fold is a field multiply-add — the verified `fieldMul`/`fieldAdd` kernels. Applied
across a domain it is the per-point FRI fold; iterated it is the low-degree test. -/

/-- One FRI fold: the random linear combination of the even/odd decimations. -/
def friFold (p : Nat) (β fEven fOdd : ZMod p) : ZMod p := fEven + β * fOdd

/-- The fold is exactly a field multiply (`β·fOdd`) followed by a field add — the
    operations the compiled kernels realise. -/
theorem friFold_eq (p : Nat) (β fEven fOdd : ZMod p) :
    friFold p β fEven fOdd = fieldAdd p fEven (fieldMul p β fOdd) := by
  simp [friFold, fieldAdd, fieldMul]

/-- A whole FRI round folds a list of even/odd pairs pointwise — a `map` of the
    per-point fold, i.e. of verified field multiply-adds. -/
def friRound (p : Nat) (β : ZMod p) (pairs : List (ZMod p × ZMod p)) : List (ZMod p) :=
  pairs.map (fun q => friFold p β q.1 q.2)

/-! ## Poseidon: the hash underlying plonky3's Merkle commitment

plonky3 commits via Merkle trees over the Poseidon2 hash. Poseidon's nonlinear layer
is the S-box `x ↦ x^5` over the field, and its linear layer is an MDS matrix-vector
product — both pure field arithmetic. The S-box is `(x²)²·x`, three field multiplies;
the linear layer is field multiply-adds. So the entire prover compute stack (NTT, FRI,
Merkle/Poseidon) reduces to the verified field operations. -/

/-- The Poseidon S-box `x ↦ x^5`, the nonlinear layer of plonky3's hash. -/
def poseidonSbox (p : Nat) (x : ZMod p) : ZMod p := x ^ 5

/-- The S-box is three field multiplies: `(x·x)·(x·x)·x`. -/
theorem poseidonSbox_eq (p : Nat) (x : ZMod p) :
    poseidonSbox p x = fieldMul p (fieldMul p (fieldMul p x x) (fieldMul p x x)) x := by
  simp only [poseidonSbox, fieldMul]; ring

/-- A Poseidon MDS linear-layer cell: `Σ mᵢ · vᵢ`, a chain of field multiply-adds. -/
def mdsCell (p : Nat) (row vec : List (ZMod p)) : ZMod p :=
  (List.zipWith (· * ·) row vec).foldl (· + ·) 0

/-! ## Multi-limb field multiply: the product reduced mod `p` IS the field product

For *any* prime `p` (P256, P384, …), the multi-limb integer product
(`MultiLimbKernel.mulBignum_val`) reduced mod `p` equals the `ZMod p` field product
of the operands' values. This is the value-correctness of multi-limb field
multiplication; the `mod p` reduction itself is a multi-limb Barrett/Montgomery
*implementation* over the same verified add/sub/mul kernels. -/

open MultiLimbKernel in
/-- The multi-limb product reduced mod `p` is the `ZMod p` field product — for any
    prime, the larger NIST primes included. -/
theorem mulBignum_zmod (p : Nat) [NeZero p] (as bs : List (BitVec 64)) :
    bignumVal (mulBignum as bs) % p
      = (((bignumVal as : ZMod p)) * ((bignumVal bs : ZMod p))).val := by
  rw [mulBignum_val, ← Nat.cast_mul, ZMod.val_natCast]

open MultiLimbKernel in
/-- And the multi-limb sum reduced mod `p` is the `ZMod p` field sum. -/
theorem addLimbs_zmod (p : Nat) [NeZero p] (as bs : List (BitVec 64))
    (hlen : as.length = bs.length) :
    bignumVal (addLimbs as bs 0) % p
      = (((bignumVal as : ZMod p)) + ((bignumVal bs : ZMod p))).val := by
  rw [addLimbs_val as bs 0 (by decide) hlen]
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  rw [h0, Nat.add_zero, ← Nat.cast_add, ZMod.val_natCast]

open MultiLimbKernel in
/-- **The reduction kernel produces the field element.** For an `n`-limb value below
    `2·p` (the post-addition / post-Barrett range), the multi-limb conditional
    subtract outputs exactly the limbs of the `ZMod (bignumVal p)` element of the
    input value — the kernel-to-field tie for the reduction layer. -/
theorem condSubLimbs_zmod (x p : List (BitVec 64)) [NeZero (bignumVal p)]
    (hlen : x.length = p.length) (hx : bignumVal x < 2 * bignumVal p) :
    bignumVal (condSubLimbs x p) = ((bignumVal x : ZMod (bignumVal p))).val := by
  rw [condSubLimbs_val x p hlen hx, ZMod.val_natCast]

open MultiLimbKernel in
/-- **The full Barrett reduction produces the field element.** For a `W`-limb value
    `x` and `W`-limb prime `p` with reciprocal `mu`, the Barrett reduction outputs the
    limbs of `x`'s `ZMod (bignumVal p)` element. Composed with `mulBignum_val` (the
    schoolbook product) this is multi-limb field multiplication: the product of two
    operands, Barrett-reduced, is their field product — for any prime. -/
theorem barrettReduce_zmod (x p mu : List (BitVec 64)) (W : Nat) (hW : 0 < W)
    [NeZero (bignumVal p)] (hxl : x.length = W) (hpl : p.length = W) (hmul : mu.length = W)
    (hmuval : bignumVal mu = (2 ^ 64) ^ W / bignumVal p) :
    bignumVal (barrettReduce x p mu W) = ((bignumVal x : ZMod (bignumVal p))).val := by
  rw [barrettReduce_val x p mu W hW hxl hpl hmul (NeZero.pos _) hmuval, ZMod.val_natCast]

end CatCrypt.Crypto.SecureCompilation.FieldSpecs
