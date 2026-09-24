/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public meta import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public meta import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public meta import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Mul
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Mul
public import Mathlib.Data.ZMod.Basic

/-!
# The `bls12_381` BASE-field ADD + MUL, realized relationally over a 6×64-bit carrier

`RelationalFrontBls377Add` / `RelationalFrontBls377Mul` realize the `bls12_377`
base-field **ADD** and **MUL** relationally at `k = 6` limbs: the abstract `ZMod q`
operation, serialized by the 6-limb encoding `encMLK q 6`, equals the emitted 6-limb
reducing kernel (`mlAddModK` with the `condSubLimbs` reduce; `mlMulMod` with the
Barrett reduce of the product), read through `bignumVal`. Those modules supply
the carrier-parametric scaffolding — `splitLimbsK`, `encMLK`, `mlAddModK`, `mlMulMod`,
`KLimbPrime`, `KLimbPrimeMul`, the commuting squares `encMLK_add_commutes` /
`encMLK_mul_commutes`, and the transfer lemmas — instantiated there at the 377-bit
Zexe/Aleo prime.

This module instantiates **exactly the same `k = 6` scaffolding** at the
`bls12_381` (IETF / Ethereum-2 pairing curve) **base-field** prime

```
   p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
```

(381-bit, 6×64-bit limbs). `bls12_381`'s base field is also a 6-limb prime, so the
structure is *identical* to `bls12_377`: only the prime literal and its limb vector
change. We reuse `splitLimbsK` / `encMLK` / `mlAddModK` / `mlMulMod` / `KLimbPrime` /
`KLimbPrimeMul` verbatim, and obtain both `bls12_381` base-field commuting squares.

## What is demonstrated (sorry-free)

* `bls381Q` — the 381-bit `bls12_381` base-field prime as a `Nat`.
* `bls381Limbs` — its 6×64-bit little-endian limb vector; `bignumVal_bls381Limbs`
  proves it reads back to `bls381Q` (the transcription check, by `norm_num`).
* `bls381KLimbPrime` (`k = 6`) — the three side conditions discharge axiom-cleanly:
  `q ≠ 0` and `2q ≤ (2^64)^6` (= `2^384`; `p` is 381-bit so `2p < 2^384`) by `norm_num`
  (pure-`Nat`, no `decide`); `bignumVal bls381Limbs = q` by `bignumVal_bls381Limbs`.
* `bls381_add_commutes` — the `bls12_381` base-field **ADD** commuting square, with the
  6-limb conditional-subtract reduce.
* `bls381Mu = ⌊(2^64)^12 / q⌋` — the product-width (`2k = 12`, `m = 768`) Barrett
  reciprocal, *defined as its side-condition value* (no `2^768` literal to `norm_num`);
  `bls381KLimbPrimeMul` and `bls381_mul_commutes` — the `bls12_381` base-field **MUL**
  commuting square, with the 12-limb Barrett reduce of the product.
* `EndoOpRealization`s for both ops, and a worked wrapping example per op.

The prime source: the repo's `Crypto/Util/BLS12381Verified.lean` declares `BLS12381`
as a `Nat` modulus but as a single decimal `abbrev`, not a 6×64-bit limb vector with a
`KLimbPrime` datum; `bls381Q` is defined here directly (mirroring how `bls377Q` is
defined in `RelationalFrontBls377Add`) so the limb transcription check `bignumVal
bls381Limbs = bls381Q` is local and self-contained.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The `bls12_381` base-field prime, `k = 6` -/

/-- The `bls12_381` base-field prime `p` (381-bit), the standard
    `0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`. -/
def bls381Q : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The `bls12_381` base-field prime as a 6×64-bit little-endian limb vector
    (`limb0` = low). `p = Σ bls381Limbsᵢ · 2^(64·i)`. -/
def bls381Limbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0xb9feffffffffaaab,
    BitVec.ofNat 64 0x1eabfffeb153ffff,
    BitVec.ofNat 64 0x6730d2a0f6b0f624,
    BitVec.ofNat 64 0x64774b84f38512bf,
    BitVec.ofNat 64 0x4b1ba7b6434bacd7,
    BitVec.ofNat 64 0x1a0111ea397fe69a ]

/-- `bls381Limbs` reads back to `bls381Q` — the 6-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). This is the limb-transcription check. -/
theorem bignumVal_bls381Limbs : bignumVal bls381Limbs = bls381Q := by
  simp only [bls381Limbs, bls381Q, bignumVal, BitVec.toNat_ofNat]; norm_num

/-- **The `bls12_381` base-field prime as a `KLimbPrime` (`k = 6`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^6 = 2^384` by `norm_num`
    (pure-`Nat`; `p` is 381-bit so `2p < 2^382 < 2^384`); `bignumVal bls381Limbs = q` by
    `bignumVal_bls381Limbs`. -/
def bls381KLimbPrime : KLimbPrime where
  k        := 6
  q        := bls381Q
  nz       := ⟨by unfold bls381Q; norm_num⟩
  ql       := bls381Limbs
  ql_len   := rfl
  ql_val   := bignumVal_bls381Limbs
  two_q_le := by unfold bls381Q; norm_num

/-- `NeZero bls381Q` from the `KLimbPrime` datum (the projection instance does not fire
    on the bare literal). Needed for the value-carrier `EndoOpRealization`s. -/
instance : NeZero bls381Q := bls381KLimbPrime.nz

/-! ## 2. The `bls12_381` base-field ADD commuting square -/

/-- **The `bls12_381` base-field ADD commuting square.** The abstract `bls12_381`
    base-field addition `a + b` (in `ZMod q` for the 381-bit prime `q = bls381Q`),
    serialized by the 6-limb encoding `encMLK q 6`, equals the emitted 6×64-bit reducing
    kernel `mlAddModK` on the serialized operands, read through `bignumVal` — with the
    6-limb conditional-subtract modular reduce. The `bls12_381` sibling of
    `bls377_add_commutes`. -/
theorem bls381_add_commutes (a b : ZMod bls381Q) :
    (a + b).val
      = bignumVal (mlAddModK bls381Limbs (encMLK bls381Q 6 a) (encMLK bls381Q 6 b)) :=
  encMLK_add_commutes bls381KLimbPrime a b

/-- **The `EndoOpRealization` for the `bls12_381` base-field ADD.** `op = (· + ·)` on
    `ZMod bls381Q`; `bop = fun x y => (x + y) % bls381Q` on the value carrier `ℕ`;
    `enc = ZMod.val` (injective). The commuting square is `ZMod.val_add`. -/
def bls381AddRealization :
    EndoOpRealization (fun a b : ZMod bls381Q => a + b) (fun x y : Nat => (x + y) % bls381Q) :=
  addModRealizationK bls381Q

/-- **Worked wrapping ADD example.** In the `bls12_381` base field, `(q - 1) + 5` wraps to
    `4` (the maximal residue plus `5` exceeds `q` by `4`). The abstract field equation
    `(-1) + 5 = 4 + 0` in `ZMod q` transfers (through `mlAddK_spec_transfers`) to the
    emitted 6-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized
    operands — the wrapping case the 6-limb conditional-subtract reduce must get right. -/
theorem bls381_add_wrap_example :
    bignumVal (mlAddModK bls381Limbs
        (encMLK bls381Q 6 (-1)) (encMLK bls381Q 6 5))
      = bignumVal (mlAddModK bls381Limbs
          (encMLK bls381Q 6 4) (encMLK bls381Q 6 0)) :=
  (mlAddK_spec_transfers bls381KLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod bls381Q) + 5 = 4; ring_nf)

/-! ## 3. The `bls12_381` base-field MUL commuting square

The product-width Barrett reciprocal at `2k = 12` limbs (`m = 64·12 = 768`):
`bls381Mu = ⌊(2^64)^12 / q⌋`, defined *as its side-condition value* (no `2^768`
literal), re-limbed to 12×64-bit limbs by `splitLimbsK 12`. -/

/-- The `bls12_381` Barrett reciprocal at product width `2·6 = 12` limbs
    (`m = 64·12 = 768`): `⌊(2^64)^12 / q⌋ = ⌊2^768 / q⌋`. Defined *as the side-condition
    value itself*, so `muTwo_val` is definitional — no `2^768` literal needs `norm_num`
    evaluation. The re-limbing round-trip needs only `⌊N/q⌋ < N < (2^64)^12`. -/
def bls381Mu : Nat := (2 ^ 64) ^ 12 / bls381Q

/-- `bls381Mu` re-limbed to a 12×64-bit little-endian vector. -/
def bls381MuLimbs : List (BitVec 64) := splitLimbsK 12 bls381Mu

/-- `bls381Mu < (2^64)^12`: the Barrett quotient `⌊N/q⌋ < N` (`Nat.div_lt_self`, with
    `0 < N` and `1 < q`). -/
theorem bls381Mu_lt : bls381Mu < (2 ^ 64) ^ 12 := by
  unfold bls381Mu
  refine Nat.div_lt_self (by positivity) ?_
  unfold bls381Q; norm_num

/-- **The `bls12_381` base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 6`).** Reuses `bls381KLimbPrime`; the new data are the 12-limb
    reciprocal `bls381MuLimbs` and the reciprocal-correctness side condition
    `bignumVal bls381MuLimbs = (2^64)^12 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    (the reciprocal is defined *as* that value). -/
def bls381KLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := bls381KLimbPrime
  muTwo     := bls381MuLimbs
  muTwo_len := by
    show (splitLimbsK 12 bls381Mu).length = 2 * bls381KLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 12 bls381Mu) = (2 ^ 64) ^ (2 * bls381KLimbPrime.k) / bls381KLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 12 bls381Mu bls381Mu_lt]
    show bls381Mu = (2 ^ 64) ^ (2 * 6) / bls381Q
    rfl
  k_pos := by decide

/-- **The `bls12_381` base-field MUL commuting square.** The abstract `bls12_381`
    base-field multiply `a * b` (in `ZMod q` for the 381-bit prime `q = bls381Q`),
    serialized by the 6-limb encoding `encMLK q 6`, equals the emitted 12-limb
    Barrett-reducing kernel `mlMulMod` on the serialized operands, read through
    `bignumVal` — with the multi-limb Barrett modular reduce of the product. The
    `bls12_381` sibling of `bls377_mul_commutes`, completing the `bls12_381` field-op set. -/
theorem bls381_mul_commutes (a b : ZMod bls381Q) :
    (a * b).val
      = bignumVal (mlMulMod 6 bls381MuLimbs bls381Limbs (encMLK bls381Q 6 a) (encMLK bls381Q 6 b)) :=
  encMLK_mul_commutes bls381KLimbPrimeMul a b

/-- **The `EndoOpRealization` for the `bls12_381` base-field MUL.** `op = (· * ·)` on
    `ZMod bls381Q`; `bop = fun x y => (x * y) % bls381Q` on the value carrier `ℕ`;
    `enc = ZMod.val` (injective). The MUL sibling of `bls381AddRealization`. -/
def bls381MulRealization :
    EndoOpRealization (fun a b : ZMod bls381Q => a * b) (fun x y : Nat => (x * y) % bls381Q) :=
  mulModRealizationK bls381Q

/-- **Worked wrapping MUL example.** In the `bls12_381` base field, `(-1) * 2 = -2` (the
    maximal residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1`
    in `ZMod q` transfers (through `mlMulK_spec_transfers`) to the emitted 12-limb
    `mlMulMod` kernel agreeing (through `bignumVal`) on the serialized operands — the
    wrapping case the multi-limb Barrett reduce must get right. -/
theorem bls381_mul_wrap_example :
    bignumVal (mlMulMod 6 bls381MuLimbs bls381Limbs
        (encMLK bls381Q 6 (-1)) (encMLK bls381Q 6 2))
      = bignumVal (mlMulMod 6 bls381MuLimbs bls381Limbs
          (encMLK bls381Q 6 (-2)) (encMLK bls381Q 6 1)) :=
  (mlMulK_spec_transfers bls381KLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod bls381Q) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
