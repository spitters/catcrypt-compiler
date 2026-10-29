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
public import CatCryptCore.Tactics.GrindChar

/-!
# The NIST P-256 base field ADD and MUL, realized relationally over a 5×64-bit carrier

`RelationalFrontBls377Add` realizes a base-field **ADD** relationally over a `k`-limb
carrier; `RelationalFrontBls377Mul` adds the **MUL** (Barrett of the product). Both
factor through the *carrier-parametric* multi-limb machinery in those modules —
`KLimbPrime`/`encMLK`/`splitLimbsK`/`mlAddModK`/`encMLK_add_commutes` (ADD) and
`KLimbPrimeMul`/`mlMulMod`/`encMLK_mul_commutes` (MUL) are stated at arbitrary `k` and
reuse the proved `MultiLimbKernel` value laws verbatim. `RelationalFrontSecp256k1` is the
closest sibling: another full 256-bit prime over the same machinery.

This module instantiates that machinery at the **NIST P-256 (secp256r1) base field** —
the prime of NIST ECDSA / ECDH over P-256:
`p = 2^256 − 2^224 + 2^192 + 2^96 − 1
   = 0xFFFFFFFF_00000001_00000000_00000000_00000000_FFFFFFFF_FFFFFFFF_FFFFFFFF`.

## The limb-count subtlety: `k = 5`, not `k = 4`

P-256's prime is a *full* 256-bit value (`p ≈ 2^256`), so `2p ≈ 2^257`. The
multi-limb ADD's no-overflow side condition `2q ≤ (2^64)^k` therefore **fails at
`k = 4`** (`(2^64)^4 = 2^256 < 2p`) — just like secp256k1. We use **`k = 5`** 64-bit
limbs (carrier `2^320`): the top limb is `0`, and `2p ≤ 2^320` holds with room to
spare. The product width for MUL is then `2k = 10` limbs.

## P-256 instance scope

* **ADD (fully proved):** the abstract `ZMod q` field add `a + b`, serialized by the
  5-limb encoding `encMLK q 5`, equals the emitted 5-limb reducing kernel `mlAddModK`
  on the serialized operands (with the `condSubLimbs` reduce), read through
  `bignumVal`. This is `p256_add_commutes`.
* **MUL (fully proved):** the abstract `ZMod q` field multiply `a * b`, serialized by the
  same encoding, equals the emitted 10-limb (`2k = 10`) Barrett-reducing kernel
  `mlMulMod` on the serialized operands — with the multi-limb Barrett reduce of
  the product (`mu = ⌊(2^64)^10 / q⌋`, defined *as its side-condition value* so no
  `2^640` literal is evaluated). This is `p256_mul_commutes`.
* The three Nat side conditions (`q ≠ 0`, `2q ≤ (2^64)^5`, `bignumVal p256Limbs = q`)
  discharge by `norm_num`/`simp` on the 256-bit literal (no `native_decide`); the
  Barrett reciprocal-width side conditions discharge by `Nat.div_lt_self` + the generic
  re-limbing round-trip, never evaluating the quotient digits.

With ADD + MUL both realized over the 5-limb carrier, the P-256 base-field op set is
complete for the inversion-free EC group law (Jacobian add/double are straight-line
`+`/`·`; field inversion is the separate safegcd leaf in `Vale/SafegcdP256.lean`,
not a relational front).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The P-256 base-field prime and its 5×64-bit limb vector

The NIST P-256 base prime:
`p = 2^256 − 2^224 + 2^192 + 2^96 − 1
   = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
   = 115792089210356248762697446949407573530086143415290314195533631308867097853951`.
A full 256-bit prime, laid out over **`k = 5`** limbs (the top limb is `0`) so that the
ADD no-overflow bound `2q ≤ (2^64)^5` holds (see the module header). The four low 64-bit
LE limbs are, from the hex 64-bit words `FFFFFFFF00000001 | 0000000000000000 |
00000000FFFFFFFF | FFFFFFFFFFFFFFFF` (high→low): `limb0 = FFFFFFFFFFFFFFFF`,
`limb1 = 00000000FFFFFFFF`, `limb2 = 0000000000000000`, `limb3 = FFFFFFFF00000001`. -/

/-- The NIST P-256 base-field prime `q` (`= 2^256 − 2^224 + 2^192 + 2^96 − 1`, 256-bit). -/
def p256Q : Nat :=
  0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

/-- `FpP256R` — the NIST P-256 base field as a residue ring. -/
abbrev FpP256R : Type := ZMod p256Q

-- grind reduces mod p in FpP256R: a literal characteristic (grind_char_numeral).
grind_char_numeral FpP256R

/-- The P-256 base-field prime as a 5×64-bit little-endian limb vector
    (`limb0` = low, `limb4 = 0`). Matches the saturated 4×u64 LE wire format
    zero-extended to 5 limbs (`q = Σ p256Limbsᵢ · 2^(64·i)`). -/
def p256Limbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF,
    BitVec.ofNat 64 0x00000000FFFFFFFF,
    BitVec.ofNat 64 0x0000000000000000,
    BitVec.ofNat 64 0xFFFFFFFF00000001,
    BitVec.ofNat 64 0x0000000000000000 ]

/-- `p256Limbs` reads back to `p256Q` — the 5-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). -/
theorem bignumVal_p256Limbs : bignumVal p256Limbs = p256Q := by
  simp only [p256Limbs, p256Q, bignumVal, BitVec.toNat_ofNat]; norm_num

/-! ## 2. The P-256 base-field prime as a `KLimbPrime` (`k = 5`) — the ADD datum -/

/-- **The P-256 base-field prime as a `KLimbPrime` (`k = 5`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^5` by `norm_num`
    (pure-`Nat`); `bignumVal p256Limbs = q` by `bignumVal_p256Limbs`. The `k = 5`
    layout (top limb `0`) is what makes `2q ≤ (2^64)^5` hold (`2q ≈ 2^257 ≤ 2^320`);
    `k = 4` would fail it. -/
def p256KLimbPrime : KLimbPrime where
  k        := 5
  q        := p256Q
  nz       := ⟨by unfold p256Q; norm_num⟩
  ql       := p256Limbs
  ql_len   := rfl
  ql_val   := bignumVal_p256Limbs
  two_q_le := by unfold p256Q; norm_num

/-- **The P-256 base-field ADD commuting square.** The abstract P-256 base-field
    addition `a + b` (in `ZMod q` for the 256-bit prime `q = p256Q`), serialized
    by the 5-limb encoding `encMLK q 5`, equals the emitted 5×64-bit reducing kernel
    `mlAddModK` on the serialized operands, read through `bignumVal` — with the
    5-limb conditional-subtract modular reduce. The P-256 sibling of
    `secp_add_commutes`. -/
theorem p256_add_commutes (a b : ZMod p256Q) :
    (a + b).val
      = bignumVal (mlAddModK p256Limbs (encMLK p256Q 5 a) (encMLK p256Q 5 b)) :=
  encMLK_add_commutes p256KLimbPrime a b

/-! ## 3. A worked example: a P-256 base-field add whose sum WRAPS

Two P-256 base-field elements whose abstract sum exceeds `q` — so the 5-limb
conditional-subtract reduce *fires*. Take `a = q - 1 = -1` (the maximal residue) and
`b = 5`: in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the emitted kernel must
reduce. The abstract field equation `(-1) + 5 = 4 + 0` transfers (through
`mlAddK_spec_transfers`) to the emitted 5-limb kernel agreeing on the serialized
operands. -/

/-- **Worked wrapping example.** In the P-256 base field, `(-1) + 5` wraps to `4`.
    The abstract field equation `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the emitted
    5-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized operands
    — the wrapping case the 5-limb conditional-subtract reduce must get right. -/
theorem p256_add_wrap_example :
    bignumVal (mlAddModK p256Limbs
        (encMLK p256Q 5 (-1)) (encMLK p256Q 5 5))
      = bignumVal (mlAddModK p256Limbs
          (encMLK p256Q 5 4) (encMLK p256Q 5 0)) :=
  (mlAddK_spec_transfers p256KLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod p256Q) + 5 = 4; ring_nf)

/-! ## 4. The P-256 base-field MUL: the product-width Barrett reciprocal (`2k = 10`)

The Barrett reciprocal at the product width `2k = 10` (so the kernel's Barrett shift
`m = 64·10 = 640`): `p256Mu = ⌊(2^64)^10 / q⌋ = ⌊2^640 / q⌋`, a ~385-bit `Nat`. Defined
*as the side-condition value itself*, so `muTwo_val` is definitional — no `2^640`
literal needs `norm_num` evaluation. -/

/-- `NeZero p256Q` from the `KLimbPrime` datum (the projection instance does not fire
    on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero p256Q := p256KLimbPrime.nz

/-- The P-256 Barrett reciprocal at product width `2·5 = 10` limbs
    (`m = 64·10 = 640`): `⌊(2^64)^10 / q⌋ = ⌊2^640 / q⌋`. Defined *as the side-condition
    value itself* (`(2^64)^10 / p256Q`), so `muTwo_val` is definitional — no `2^640`
    literal needs `norm_num` evaluation. The re-limbing round-trip needs only
    `⌊N / q⌋ < (2^64)^10` (`Nat.div_lt_self`), never the digits of the quotient. -/
def p256Mu : Nat := (2 ^ 64) ^ 10 / p256Q

/-- `p256Mu` re-limbed to a 10×64-bit little-endian vector. -/
def p256MuLimbs : List (BitVec 64) := splitLimbsK 10 p256Mu

/-- `p256Mu < (2^64)^10`: the Barrett quotient `⌊N/q⌋ < N` for `0 < N`, `1 < q`
    (`Nat.div_lt_self`). The `1 < q` side condition closes by `norm_num` on the
    256-bit prime literal. -/
theorem p256Mu_lt : p256Mu < (2 ^ 64) ^ 10 := by
  unfold p256Mu
  refine Nat.div_lt_self (by positivity) ?_
  unfold p256Q; norm_num

/-- **The P-256 base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 5`).** Reuses `p256KLimbPrime`; the new data are the 10-limb
    reciprocal `p256MuLimbs` and its reciprocal-correctness side condition
    `bignumVal p256MuLimbs = (2^64)^10 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `p256Mu_lt` (no `2^640` literal evaluation). -/
def p256KLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := p256KLimbPrime
  muTwo     := p256MuLimbs
  muTwo_len := by
    show (splitLimbsK 10 p256Mu).length = 2 * p256KLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 10 p256Mu) = (2 ^ 64) ^ (2 * p256KLimbPrime.k) / p256KLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 10 p256Mu p256Mu_lt]
    show p256Mu = (2 ^ 64) ^ (2 * 5) / p256Q
    rfl
  k_pos := by decide

/-- **The P-256 base-field MUL commuting square.** The abstract P-256 base-field
    multiply `a * b` (in `ZMod q` for the 256-bit prime `q = p256Q`), serialized
    by the 5-limb encoding `encMLK q 5`, equals the emitted 10-limb Barrett-reducing
    kernel `mlMulMod` on the serialized operands, read through `bignumVal` — with the
    multi-limb Barrett modular reduce of the product. The P-256 sibling of
    `secp_mul_commutes`, completing the P-256 field-op set. -/
theorem p256_mul_commutes (a b : ZMod p256Q) :
    (a * b).val
      = bignumVal (mlMulMod 5 p256MuLimbs p256Limbs (encMLK p256Q 5 a) (encMLK p256Q 5 b)) :=
  encMLK_mul_commutes p256KLimbPrimeMul a b

/-! ## 5. The `EndoOpRealization`s for the P-256 ADD and MUL

`addModRealizationK p256Q` / `mulModRealizationK p256Q` tie the abstract `ZMod q`
ops to the value-carrier `bop`s `(· + ·) % q` / `(· * ·) % q`; the whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) is inherited from `ReprTransferExpr`
for free. -/

/-- **The `EndoOpRealization` for the P-256 base-field ADD.** `op = (· + ·)` on
    `ZMod p256Q`; `bop = fun x y => (x + y) % p256Q`; `enc = ZMod.val`. -/
def p256AddRealization :
    EndoOpRealization (fun a b : ZMod p256Q => a + b) (fun x y : Nat => (x + y) % p256Q) :=
  addModRealizationK p256Q

/-- **The `EndoOpRealization` for the P-256 base-field MUL.** `op = (· * ·)` on
    `ZMod p256Q`; `bop = fun x y => (x * y) % p256Q`; `enc = ZMod.val`. -/
def p256MulRealization :
    EndoOpRealization (fun a b : ZMod p256Q => a * b) (fun x y : Nat => (x * y) % p256Q) :=
  mulModRealizationK p256Q

/-! ## 6. A worked example: a P-256 base-field product whose reduce FIRES

Two P-256 base-field elements whose abstract product exceeds `q`, so the 10-limb
Barrett reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in
`ZMod q`, `(-1) * 2 = -2 = q - 2`, which equals `(-2) * 1` — the abstract field equation
`(-1) * 2 = (-2) * 1` transfers (through `mlMulK_spec_transfers`) to the emitted 10-limb
MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the P-256 base field, `(-1) * 2 = -2` (the maximal
    residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1` in
    `ZMod q` transfers to the emitted 10-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem p256_mul_wrap_example :
    bignumVal (mlMulMod 5 p256MuLimbs p256Limbs
        (encMLK p256Q 5 (-1)) (encMLK p256Q 5 2))
      = bignumVal (mlMulMod 5 p256MuLimbs p256Limbs
          (encMLK p256Q 5 (-2)) (encMLK p256Q 5 1)) :=
  (mlMulK_spec_transfers p256KLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod p256Q) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
