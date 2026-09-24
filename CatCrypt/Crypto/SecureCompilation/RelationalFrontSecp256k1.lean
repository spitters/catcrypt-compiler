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
# The secp256k1 base field ADD and MUL, realized relationally over a 5×64-bit carrier

`RelationalFrontBls377Add` realizes a base-field **ADD** relationally over a `k`-limb
carrier; `RelationalFrontBls377Mul` adds the **MUL** (Barrett of the product). Both
factor through the *carrier-parametric* multi-limb machinery in those modules —
`KLimbPrime`/`encMLK`/`splitLimbsK`/`mlAddModK`/`encMLK_add_commutes` (ADD) and
`KLimbPrimeMul`/`mlMulMod`/`encMLK_mul_commutes` (MUL) are stated at arbitrary `k` and
reuse the proved `MultiLimbKernel` value laws verbatim. `RelationalFrontPallas` is the
closest sibling: another 256-bit-class prime over the same machinery.

This module instantiates that machinery at the **secp256k1 base field** — the prime of
Bitcoin / Ethereum ECDSA and Schnorr (BIP-340):
`p = 2^256 − 2^32 − 977
   = 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2F`.

## The limb-count subtlety: `k = 5`, not `k = 4`

secp256k1's prime is a *full* 256-bit value (`p ≈ 2^256`), so `2p ≈ 2^257`. The
multi-limb ADD's no-overflow side condition `2q ≤ (2^64)^k` therefore **fails at
`k = 4`** (`(2^64)^4 = 2^256 < 2p`) — unlike Pallas/BLS-377, whose primes sit well
below their limb ceiling. We use **`k = 5`** 64-bit limbs (carrier `2^320`): the top
limb is `0`, and `2p ≤ 2^320` holds with room to spare. The product width for MUL is
then `2k = 10` limbs.

## secp256k1 instance scope

* **ADD (fully proved):** the abstract `ZMod q` field add `a + b`, serialized by the
  5-limb encoding `encMLK q 5`, equals the emitted 5-limb reducing kernel `mlAddModK`
  on the serialized operands (with the `condSubLimbs` reduce), read through
  `bignumVal`. This is `secp_add_commutes`.
* **MUL (fully proved):** the abstract `ZMod q` field multiply `a * b`, serialized by the
  same encoding, equals the emitted 10-limb (`2k = 10`) Barrett-reducing kernel
  `mlMulMod` on the serialized operands — with the multi-limb Barrett reduce of
  the product (`mu = ⌊(2^64)^10 / q⌋`, defined *as its side-condition value* so no
  `2^640` literal is evaluated). This is `secp_mul_commutes`.
* The three Nat side conditions (`q ≠ 0`, `2q ≤ (2^64)^5`, `bignumVal secpLimbs = q`)
  discharge by `norm_num`/`simp` on the 256-bit literal (no `native_decide`); the
  Barrett reciprocal-width side conditions discharge by `Nat.div_lt_self` + the generic
  re-limbing round-trip, never evaluating the quotient digits.

With ADD + MUL both realized over the 5-limb carrier, the secp256k1 base-field op set is
complete for the inversion-free EC group law (Jacobian add/double are straight-line
`+`/`·`; field inversion is the separate safegcd leaf in `Vale/SafegcdSecp256k1.lean`,
not a relational front).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The secp256k1 base-field prime and its 5×64-bit limb vector

The secp256k1 base prime:
`p = 2^256 − 2^32 − 977
   = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
   = 115792089237316195423570985008687907853269984665640564039457584007908834671663`.
A full 256-bit prime, so the low four 64-bit limbs are `0xFFFFFFFFFFFFFFFF` except the
low limb `0xFFFFFFFEFFFFFC2F`, and we lay it out over **`k = 5`** limbs (the top limb is
`0`) so that the ADD no-overflow bound `2q ≤ (2^64)^5` holds (see the module header). -/

/-- The secp256k1 base-field prime `q` (`= 2^256 − 2^32 − 977`, 256-bit). -/
def secpQ : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- `FpSecp` — the secp256k1 base field as a residue ring. -/
abbrev FpSecp : Type := ZMod secpQ

/-- The secp256k1 base-field prime as a 5×64-bit little-endian limb vector
    (`limb0` = low, `limb4 = 0`). Matches the saturated 4×u64 LE wire format
    zero-extended to 5 limbs (`q = Σ secpLimbsᵢ · 2^(64·i)`). -/
def secpLimbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0xFFFFFFFEFFFFFC2F,
    BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF,
    BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF,
    BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF,
    BitVec.ofNat 64 0x0000000000000000 ]

/-- `secpLimbs` reads back to `secpQ` — the 5-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). -/
theorem bignumVal_secpLimbs : bignumVal secpLimbs = secpQ := by
  simp only [secpLimbs, secpQ, bignumVal, BitVec.toNat_ofNat]; norm_num

/-! ## 2. The secp256k1 base-field prime as a `KLimbPrime` (`k = 5`) — the ADD datum -/

/-- **The secp256k1 base-field prime as a `KLimbPrime` (`k = 5`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^5` by `norm_num`
    (pure-`Nat`); `bignumVal secpLimbs = q` by `bignumVal_secpLimbs`. The `k = 5`
    layout (top limb `0`) is what makes `2q ≤ (2^64)^5` hold (`2q ≈ 2^257 ≤ 2^320`);
    `k = 4` would fail it. -/
def secpKLimbPrime : KLimbPrime where
  k        := 5
  q        := secpQ
  nz       := ⟨by unfold secpQ; norm_num⟩
  ql       := secpLimbs
  ql_len   := rfl
  ql_val   := bignumVal_secpLimbs
  two_q_le := by unfold secpQ; norm_num

/-- **The secp256k1 base-field ADD commuting square.** The abstract secp256k1 base-field
    addition `a + b` (in `ZMod q` for the 256-bit prime `q = secpQ`), serialized
    by the 5-limb encoding `encMLK q 5`, equals the emitted 5×64-bit reducing kernel
    `mlAddModK` on the serialized operands, read through `bignumVal` — with the
    5-limb conditional-subtract modular reduce. The secp256k1 sibling of
    `pallas_add_commutes`. -/
theorem secp_add_commutes (a b : ZMod secpQ) :
    (a + b).val
      = bignumVal (mlAddModK secpLimbs (encMLK secpQ 5 a) (encMLK secpQ 5 b)) :=
  encMLK_add_commutes secpKLimbPrime a b

/-! ## 3. A worked example: a secp256k1 base-field add whose sum WRAPS

Two secp256k1 base-field elements whose abstract sum exceeds `q` — so the 5-limb
conditional-subtract reduce *fires*. Take `a = q - 1 = -1` (the maximal residue) and
`b = 5`: in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the emitted kernel must
reduce. The abstract field equation `(-1) + 5 = 4 + 0` transfers (through
`mlAddK_spec_transfers`) to the emitted 5-limb kernel agreeing on the serialized
operands. -/

/-- **Worked wrapping example.** In the secp256k1 base field, `(-1) + 5` wraps to `4`.
    The abstract field equation `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the emitted
    5-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized operands
    — the wrapping case the 5-limb conditional-subtract reduce must get right. -/
theorem secp_add_wrap_example :
    bignumVal (mlAddModK secpLimbs
        (encMLK secpQ 5 (-1)) (encMLK secpQ 5 5))
      = bignumVal (mlAddModK secpLimbs
          (encMLK secpQ 5 4) (encMLK secpQ 5 0)) :=
  (mlAddK_spec_transfers secpKLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod secpQ) + 5 = 4; ring_nf)

/-! ## 4. The secp256k1 base-field MUL: the product-width Barrett reciprocal (`2k = 10`)

The Barrett reciprocal at the product width `2k = 10` (so the kernel's Barrett shift
`m = 64·10 = 640`): `secpMu = ⌊(2^64)^10 / q⌋ = ⌊2^640 / q⌋`, a ~385-bit `Nat`. Defined
*as the side-condition value itself*, so `muTwo_val` is definitional — no `2^640`
literal needs `norm_num` evaluation. -/

/-- `NeZero secpQ` from the `KLimbPrime` datum (the projection instance does not fire
    on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero secpQ := secpKLimbPrime.nz

/-- The secp256k1 Barrett reciprocal at product width `2·5 = 10` limbs
    (`m = 64·10 = 640`): `⌊(2^64)^10 / q⌋ = ⌊2^640 / q⌋`. Defined *as the side-condition
    value itself* (`(2^64)^10 / secpQ`), so `muTwo_val` is definitional — no `2^640`
    literal needs `norm_num` evaluation. The re-limbing round-trip needs only
    `⌊N / q⌋ < (2^64)^10` (`Nat.div_lt_self`), never the digits of the quotient. -/
def secpMu : Nat := (2 ^ 64) ^ 10 / secpQ

/-- `secpMu` re-limbed to a 10×64-bit little-endian vector. -/
def secpMuLimbs : List (BitVec 64) := splitLimbsK 10 secpMu

/-- `secpMu < (2^64)^10`: the Barrett quotient `⌊N/q⌋ < N` for `0 < N`, `1 < q`
    (`Nat.div_lt_self`). The `1 < q` side condition closes by `norm_num` on the
    256-bit prime literal. -/
theorem secpMu_lt : secpMu < (2 ^ 64) ^ 10 := by
  unfold secpMu
  refine Nat.div_lt_self (by positivity) ?_
  unfold secpQ; norm_num

/-- **The secp256k1 base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 5`).** Reuses `secpKLimbPrime`; the new data are the 10-limb
    reciprocal `secpMuLimbs` and its reciprocal-correctness side condition
    `bignumVal secpMuLimbs = (2^64)^10 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `secpMu_lt` (no `2^640` literal evaluation). -/
def secpKLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := secpKLimbPrime
  muTwo     := secpMuLimbs
  muTwo_len := by
    show (splitLimbsK 10 secpMu).length = 2 * secpKLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 10 secpMu) = (2 ^ 64) ^ (2 * secpKLimbPrime.k) / secpKLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 10 secpMu secpMu_lt]
    show secpMu = (2 ^ 64) ^ (2 * 5) / secpQ
    rfl
  k_pos := by decide

/-- **The secp256k1 base-field MUL commuting square.** The abstract secp256k1 base-field
    multiply `a * b` (in `ZMod q` for the 256-bit prime `q = secpQ`), serialized
    by the 5-limb encoding `encMLK q 5`, equals the emitted 10-limb Barrett-reducing
    kernel `mlMulMod` on the serialized operands, read through `bignumVal` — with the
    multi-limb Barrett modular reduce of the product. The secp256k1 sibling of
    `pallas_mul_commutes`, completing the secp256k1 field-op set. -/
theorem secp_mul_commutes (a b : ZMod secpQ) :
    (a * b).val
      = bignumVal (mlMulMod 5 secpMuLimbs secpLimbs (encMLK secpQ 5 a) (encMLK secpQ 5 b)) :=
  encMLK_mul_commutes secpKLimbPrimeMul a b

/-! ## 5. The `EndoOpRealization`s for the secp256k1 ADD and MUL

`addModRealizationK secpQ` / `mulModRealizationK secpQ` tie the abstract `ZMod q`
ops to the value-carrier `bop`s `(· + ·) % q` / `(· * ·) % q`; the whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) is inherited from `ReprTransferExpr`
for free. -/

/-- **The `EndoOpRealization` for the secp256k1 base-field ADD.** `op = (· + ·)` on
    `ZMod secpQ`; `bop = fun x y => (x + y) % secpQ`; `enc = ZMod.val`. -/
def secpAddRealization :
    EndoOpRealization (fun a b : ZMod secpQ => a + b) (fun x y : Nat => (x + y) % secpQ) :=
  addModRealizationK secpQ

/-- **The `EndoOpRealization` for the secp256k1 base-field MUL.** `op = (· * ·)` on
    `ZMod secpQ`; `bop = fun x y => (x * y) % secpQ`; `enc = ZMod.val`. -/
def secpMulRealization :
    EndoOpRealization (fun a b : ZMod secpQ => a * b) (fun x y : Nat => (x * y) % secpQ) :=
  mulModRealizationK secpQ

/-! ## 6. A worked example: a secp256k1 base-field product whose reduce FIRES

Two secp256k1 base-field elements whose abstract product exceeds `q`, so the 10-limb
Barrett reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in
`ZMod q`, `(-1) * 2 = -2 = q - 2`, which equals `(-2) * 1` — the abstract field equation
`(-1) * 2 = (-2) * 1` transfers (through `mlMulK_spec_transfers`) to the emitted 10-limb
MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the secp256k1 base field, `(-1) * 2 = -2` (the maximal
    residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1` in
    `ZMod q` transfers to the emitted 10-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem secp_mul_wrap_example :
    bignumVal (mlMulMod 5 secpMuLimbs secpLimbs
        (encMLK secpQ 5 (-1)) (encMLK secpQ 5 2))
      = bignumVal (mlMulMod 5 secpMuLimbs secpLimbs
          (encMLK secpQ 5 (-2)) (encMLK secpQ 5 1)) :=
  (mlMulK_spec_transfers secpKLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod secpQ) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
