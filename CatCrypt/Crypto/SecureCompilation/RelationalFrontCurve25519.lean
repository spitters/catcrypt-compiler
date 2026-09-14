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
# The Curve25519 base field ADD and MUL, realized relationally over a 4×64-bit carrier

`RelationalFrontBls377Add` realizes a base-field **ADD** relationally over a `k`-limb
carrier; `RelationalFrontBls377Mul` adds the **MUL** (Barrett of the product). Both
factor through the *carrier-parametric* multi-limb machinery in those modules —
`KLimbPrime`/`encMLK`/`splitLimbsK`/`mlAddModK`/`encMLK_add_commutes` (ADD) and
`KLimbPrimeMul`/`mlMulMod`/`encMLK_mul_commutes` (MUL) are stated at arbitrary `k` and
reuse the proved `MultiLimbKernel` value laws verbatim. `RelationalFrontSecp256k1` is the
closest sibling: another 256-bit-class prime over the same machinery.

This module instantiates that machinery at the **Curve25519 base field** — the prime of
X25519 / Ed25519:
`p = 2^255 − 19
   = 0x7FFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFED`
(64 hex digits / 256-bit field width; top nibble `7`).

## The limb count: `k = 4`

`KLimbPrime` requires the ADD no-overflow bound `2q ≤ (2^64)^k`. The Curve25519 prime is
a 255-bit value, so `2q = 2·(2^255 − 19) = 2^256 − 38 ≤ 2^256 = (2^64)^4`, and the bound
holds at `k = 4` (field `two_q_le` of `c25519KLimbPrime`, closed by `norm_num`). This
module uses the saturated 4×64-bit layout with top limb `0x7FFFFFFFFFFFFFFF`. For
comparison, the secp256k1 prime is a full 256-bit value, `2q > (2^64)^4`, and
`RelationalFrontSecp256k1` uses `k = 5`. The product width for MUL is `2k = 8` limbs.

## Proved statements

* **ADD:** the `ZMod q` field addition `a + b`, serialized by the 4-limb encoding
  `encMLK q 4`, equals the 4-limb reducing kernel `mlAddModK` (carry-extended limb
  addition followed by the `condSubLimbs` conditional-subtract reduce) on the serialized
  operands, read through `bignumVal`. This is `c25519_add_commutes`.
* **MUL:** the `ZMod q` field multiplication `a * b`, serialized by the same encoding,
  equals the 8-limb (`2k = 8`) Barrett-reducing kernel `mlMulMod` on the serialized
  operands, read through `bignumVal` (`mu = ⌊(2^64)^8 / q⌋`, defined as its
  side-condition value so no `2^512` literal is evaluated). This is
  `c25519_mul_commutes`.
* The three `Nat` side conditions (`q ≠ 0`, `2q ≤ (2^64)^4`, `bignumVal c25519Limbs = q`)
  are closed by `norm_num`/`simp` on the 255-bit literal (no `native_decide`); the Barrett
  reciprocal side conditions are closed by `Nat.div_lt_self` and the generic re-limbing
  round-trip, without evaluating the quotient digits.

`mlAddModK` and `mlMulMod` are Lean functions on limb lists. Subtraction and inversion
in this field are not stated in this module.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The Curve25519 base-field prime and its 4×64-bit limb vector

The Curve25519 base prime:
`p = 2^255 − 19
   = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED
   = 57896044618658097711785492504343953926634992332820282019728792003956564819949`.
A 255-bit prime, so the low three 64-bit limbs are `0xFFFFFFFFFFFFFFFF` except the low
limb `0xFFFFFFFFFFFFFFED`, and the top limb is `0x7FFFFFFFFFFFFFFF` (high bit clear). It
is laid out over the saturated `k = 4` limbs; the ADD no-overflow bound
`2q ≤ (2^64)^4` holds because `2q = 2^256 − 38 ≤ 2^256` (see the module header). -/

/-- The Curve25519 base-field prime `q` (`= 2^255 − 19`, 255-bit). -/
def curve25519Q : Nat :=
  0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED

/-- `Fe25519P` — the Curve25519 base field as a residue ring. -/
abbrev Fe25519P : Type := ZMod curve25519Q

/-- The Curve25519 base-field prime as a 4×64-bit little-endian limb vector
    (`limb0` = low, `limb3 = 0x7FFFFFFFFFFFFFFF`). Matches the saturated 4×u64 LE wire
    format (`q = Σ c25519Limbsᵢ · 2^(64·i)`). -/
def c25519Limbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0xFFFFFFFFFFFFFFED,
    BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF,
    BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF,
    BitVec.ofNat 64 0x7FFFFFFFFFFFFFFF ]

/-- `c25519Limbs` reads back to `curve25519Q` — the 4-limb vector represents the prime.
    Proved by `simp only [bignumVal, BitVec.toNat_ofNat]` and `norm_num` (no
    `native_decide`). -/
theorem bignumVal_c25519Limbs : bignumVal c25519Limbs = curve25519Q := by
  simp only [c25519Limbs, curve25519Q, bignumVal, BitVec.toNat_ofNat]; norm_num

/-! ## 2. The Curve25519 base-field prime as a `KLimbPrime` (`k = 4`) — the ADD datum -/

/-- **The Curve25519 base-field prime as a `KLimbPrime` (`k = 4`).** All three side
    conditions are closed without `native_decide`: `q ≠ 0` and `2q ≤ (2^64)^4` by `norm_num`
    (pure-`Nat`); `bignumVal c25519Limbs = q` by `bignumVal_c25519Limbs`. The `k = 4`
    layout holds `2q ≤ (2^64)^4` because `2q = 2^256 − 38 ≤ 2^256` — the 255-bit prime
    sits just under the 4-limb ceiling (unlike secp256k1, whose full-256-bit prime needs
    `k = 5`). -/
def c25519KLimbPrime : KLimbPrime where
  k        := 4
  q        := curve25519Q
  nz       := ⟨by unfold curve25519Q; norm_num⟩
  ql       := c25519Limbs
  ql_len   := rfl
  ql_val   := bignumVal_c25519Limbs
  two_q_le := by unfold curve25519Q; norm_num

/-- **The Curve25519 base-field ADD commuting square.** The abstract Curve25519
    base-field addition `a + b` (in `ZMod q` for the 255-bit prime
    `q = curve25519Q`), serialized by the 4-limb encoding `encMLK q 4`, equals the
    4×64-bit reducing kernel `mlAddModK` on the serialized operands, read through
    `bignumVal`; `mlAddModK` ends with the 4-limb conditional-subtract modular reduce.
    The Curve25519 counterpart of `secp_add_commutes`. -/
theorem c25519_add_commutes (a b : ZMod curve25519Q) :
    (a + b).val
      = bignumVal (mlAddModK c25519Limbs (encMLK curve25519Q 4 a) (encMLK curve25519Q 4 b)) :=
  encMLK_add_commutes c25519KLimbPrime a b

/-! ## 3. A worked example: a Curve25519 base-field add whose sum WRAPS

Two Curve25519 base-field elements whose abstract sum exceeds `q` — so the 4-limb
conditional-subtract reduce *fires*. Take `a = q - 1 = -1` (the maximal residue) and
`b = 5`: in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the kernel must
reduce. The abstract field equation `(-1) + 5 = 4 + 0` transfers (through
`mlAddK_spec_transfers`) to the 4-limb kernel agreeing on the serialized
operands. -/

/-- **Worked wrapping example.** In the Curve25519 base field, `(-1) + 5` wraps to `4`.
    The abstract field equation `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the
    4-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized operands
    — the wrapping case the 4-limb conditional-subtract reduce must get right. -/
theorem c25519_add_wrap_example :
    bignumVal (mlAddModK c25519Limbs
        (encMLK curve25519Q 4 (-1)) (encMLK curve25519Q 4 5))
      = bignumVal (mlAddModK c25519Limbs
          (encMLK curve25519Q 4 4) (encMLK curve25519Q 4 0)) :=
  (mlAddK_spec_transfers c25519KLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod curve25519Q) + 5 = 4; ring_nf)

/-! ## 4. The Curve25519 base-field MUL: the product-width Barrett reciprocal (`2k = 8`)

The Barrett reciprocal at the product width `2k = 8` (so the kernel's Barrett shift
`m = 64·8 = 512`): `c25519Mu = ⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`, a ~257-bit `Nat`. Defined
*as the side-condition value itself*, so `muTwo_val` is definitional — no `2^512` literal
needs `norm_num` evaluation. -/

/-- `NeZero curve25519Q` from the `KLimbPrime` datum (the projection instance does not
    fire on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero curve25519Q := c25519KLimbPrime.nz

/-- The Curve25519 Barrett reciprocal at product width `2·4 = 8` limbs
    (`m = 64·8 = 512`): `⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`. Defined *as the side-condition
    value itself* (`(2^64)^8 / curve25519Q`), so `muTwo_val` is definitional — no `2^512`
    literal needs `norm_num` evaluation. The re-limbing round-trip needs only
    `⌊N / q⌋ < (2^64)^8` (`Nat.div_lt_self`), never the digits of the quotient. -/
def c25519Mu : Nat := (2 ^ 64) ^ 8 / curve25519Q

/-- `c25519Mu` re-limbed to an 8×64-bit little-endian vector. -/
def c25519MuLimbs : List (BitVec 64) := splitLimbsK 8 c25519Mu

/-- `c25519Mu < (2^64)^8`: the Barrett quotient `⌊N/q⌋ < N` for `0 < N`, `1 < q`
    (`Nat.div_lt_self`). The `1 < q` side condition closes by `norm_num` on the
    255-bit prime literal. -/
theorem c25519Mu_lt : c25519Mu < (2 ^ 64) ^ 8 := by
  unfold c25519Mu
  refine Nat.div_lt_self (by positivity) ?_
  unfold curve25519Q; norm_num

/-- **The Curve25519 base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 4`).** Reuses `c25519KLimbPrime`; the new data are the 8-limb
    reciprocal `c25519MuLimbs` and its reciprocal-correctness side condition
    `bignumVal c25519MuLimbs = (2^64)^8 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `c25519Mu_lt` (no `2^512` literal evaluation). -/
def c25519KLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := c25519KLimbPrime
  muTwo     := c25519MuLimbs
  muTwo_len := by
    show (splitLimbsK 8 c25519Mu).length = 2 * c25519KLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 8 c25519Mu) = (2 ^ 64) ^ (2 * c25519KLimbPrime.k) / c25519KLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 8 c25519Mu c25519Mu_lt]
    show c25519Mu = (2 ^ 64) ^ (2 * 4) / curve25519Q
    rfl
  k_pos := by decide

/-- **The Curve25519 base-field MUL commuting square.** The abstract Curve25519
    base-field multiply `a * b` (in `ZMod q` for the 255-bit prime
    `q = curve25519Q`), serialized by the 4-limb encoding `encMLK q 4`, equals the
    8-limb Barrett-reducing kernel `mlMulMod` on the serialized operands, read through
    `bignumVal`; `mlMulMod` applies the multi-limb Barrett modular reduce to the product.
    The Curve25519 counterpart of `secp_mul_commutes`. -/
theorem c25519_mul_commutes (a b : ZMod curve25519Q) :
    (a * b).val
      = bignumVal (mlMulMod 4 c25519MuLimbs c25519Limbs
          (encMLK curve25519Q 4 a) (encMLK curve25519Q 4 b)) :=
  encMLK_mul_commutes c25519KLimbPrimeMul a b

/-! ## 5. The `EndoOpRealization`s for the Curve25519 ADD and MUL

`addModRealizationK curve25519Q` / `mulModRealizationK curve25519Q` tie the abstract
`ZMod q` ops to the value-carrier `bop`s `(· + ·) % q` / `(· * ·) % q`; the whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) from `ReprTransferExpr` applies to
them. -/

/-- **The `EndoOpRealization` for the Curve25519 base-field ADD.** `op = (· + ·)` on
    `ZMod curve25519Q`; `bop = fun x y => (x + y) % curve25519Q`; `enc = ZMod.val`. -/
def c25519AddRealization :
    EndoOpRealization (fun a b : ZMod curve25519Q => a + b)
      (fun x y : Nat => (x + y) % curve25519Q) :=
  addModRealizationK curve25519Q

/-- **The `EndoOpRealization` for the Curve25519 base-field MUL.** `op = (· * ·)` on
    `ZMod curve25519Q`; `bop = fun x y => (x * y) % curve25519Q`; `enc = ZMod.val`. -/
def c25519MulRealization :
    EndoOpRealization (fun a b : ZMod curve25519Q => a * b)
      (fun x y : Nat => (x * y) % curve25519Q) :=
  mulModRealizationK curve25519Q

/-! ## 6. A worked example: a Curve25519 base-field product whose reduce FIRES

Two Curve25519 base-field elements whose abstract product exceeds `q`, so the 8-limb
Barrett reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in
`ZMod q`, `(-1) * 2 = -2 = q - 2`, which equals `(-2) * 1` — the abstract field equation
`(-1) * 2 = (-2) * 1` transfers (through `mlMulK_spec_transfers`) to the 8-limb
MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the Curve25519 base field, `(-1) * 2 = -2` (the maximal
    residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1` in
    `ZMod q` transfers to the 8-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem c25519_mul_wrap_example :
    bignumVal (mlMulMod 4 c25519MuLimbs c25519Limbs
        (encMLK curve25519Q 4 (-1)) (encMLK curve25519Q 4 2))
      = bignumVal (mlMulMod 4 c25519MuLimbs c25519Limbs
          (encMLK curve25519Q 4 (-2)) (encMLK curve25519Q 4 1)) :=
  (mlMulK_spec_transfers c25519KLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod curve25519Q) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
