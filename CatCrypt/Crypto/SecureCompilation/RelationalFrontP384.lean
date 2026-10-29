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
# The NIST P-384 base field ADD and MUL, realized relationally over a 7×64-bit carrier

`RelationalFrontBls377Add` realizes a base-field **ADD** relationally over a `k`-limb
carrier; `RelationalFrontBls377Mul` adds the **MUL** (Barrett of the product). Both
factor through the *carrier-parametric* multi-limb machinery in those modules —
`KLimbPrime`/`encMLK`/`splitLimbsK`/`mlAddModK`/`encMLK_add_commutes` (ADD) and
`KLimbPrimeMul`/`mlMulMod`/`encMLK_mul_commutes` (MUL) are stated at arbitrary `k` and
reuse the proved `MultiLimbKernel` value laws verbatim. `RelationalFrontP256` is the
closest sibling: another full-width NIST base-field prime over the same machinery, one
limb wider (`k = 5`).

This module instantiates that machinery at the **NIST P-384 (secp384r1) base field** —
the prime of NIST ECDSA / ECDH over P-384:
`p = 2^384 − 2^128 − 2^96 + 2^32 − 1`,
i.e.
`p = 0xFFFFFFFF…FFFFFFFE_FFFFFFFF_00000000_00000000_FFFFFFFF` (a full 384-bit prime).

## The limb-count subtlety: `k = 7`, not `k = 6`

P-384's prime is a *full* 384-bit value (`p ≈ 2^384`), so `2p ≈ 2^385`. The multi-limb
ADD's no-overflow side condition `2q ≤ (2^64)^k` therefore **fails at `k = 6`**
(`(2^64)^6 = 2^384 < 2p`, where `two_q_le` reduces to `False` under `norm_num`) — the
same full-width boundary secp256k1 and P-256 hit at `k = 4`. We use **`k = 7`** 64-bit
limbs (carrier `2^448`): the top limb is `0`, and `2p ≤ 2^448` holds with room to spare.
The product width for MUL is then `2k = 14` limbs (Barrett shift `m = 64·14 = 896`).

## P-384 instance scope

* **ADD (fully proved):** the abstract `ZMod q` field add `a + b`, serialized by the
  7-limb encoding `encMLK q 7`, equals the emitted 7-limb reducing kernel `mlAddModK`
  on the serialized operands (with the `condSubLimbs` reduce), read through
  `bignumVal`. This is `p384_add_commutes`.
* **MUL (fully proved):** the abstract `ZMod q` field multiply `a * b`, serialized by the
  same encoding, equals the emitted 14-limb (`2k = 14`) Barrett-reducing kernel
  `mlMulMod` on the serialized operands — with the multi-limb Barrett reduce of
  the product (`mu = ⌊(2^64)^14 / q⌋`, defined *as its side-condition value* so no
  `2^896` literal is evaluated). This is `p384_mul_commutes`.
* The three Nat side conditions (`q ≠ 0`, `2q ≤ (2^64)^7`, `bignumVal p384Limbs = q`)
  discharge by `norm_num`/`simp` on the 384-bit literal (no `native_decide`); the
  Barrett reciprocal-width side conditions discharge by `Nat.div_lt_self` + the generic
  re-limbing round-trip, never evaluating the quotient digits.

With ADD + MUL both realized over the 7-limb carrier, the P-384 base-field op set is
complete for the inversion-free EC group law (Jacobian add/double are straight-line
`+`/`·`; field inversion is the separate safegcd leaf in `Vale/SafegcdP384.lean`, not a
relational front). The 6×64-limb modulus vector matches the repo's emit-side
`X86Backend.P384FieldKernel.p384Limbs` (this front zero-extends to 7 limbs).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The P-384 base-field prime and its 7×64-bit limb vector

The NIST P-384 base prime:
`p = 2^384 − 2^128 − 2^96 + 2^32 − 1
   = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
       FFFFFFFF0000000000000000FFFFFFFF`.
A full 384-bit prime, laid out over **`k = 7`** limbs (the top limb is `0`) so that the
ADD no-overflow bound `2q ≤ (2^64)^7` holds (see the module header). The six low 64-bit
LE limbs match `X86Backend.P384FieldKernel.p384Limbs`:
`limb0 = 0x00000000FFFFFFFF`, `limb1 = 0xFFFFFFFF00000000`, `limb2 = 0xFFFFFFFFFFFFFFFE`,
`limb3 = limb4 = limb5 = 0xFFFFFFFFFFFFFFFF`, with `limb6 = 0` the carrier head. -/

/-- The NIST P-384 base-field prime `q` (`= 2^384 − 2^128 − 2^96 + 2^32 − 1`, 384-bit). -/
def p384Q : Nat :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff

/-- `FpP384R` — the NIST P-384 base field as a residue ring. -/
abbrev FpP384R : Type := ZMod p384Q

-- grind reduces mod p in FpP384R: a literal characteristic (grind_char_numeral).
grind_char_numeral FpP384R

/-- The P-384 base-field prime as a 7×64-bit little-endian limb vector
    (`limb0` = low, `limb6 = 0`). The six low limbs match the saturated 6×u64 LE wire
    format (`X86Backend.P384FieldKernel.p384Limbs`), zero-extended to 7 limbs
    (`q = Σ p384Limbsᵢ · 2^(64·i)`). -/
def p384Limbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0x00000000ffffffff,
    BitVec.ofNat 64 0xffffffff00000000,
    BitVec.ofNat 64 0xfffffffffffffffe,
    BitVec.ofNat 64 0xffffffffffffffff,
    BitVec.ofNat 64 0xffffffffffffffff,
    BitVec.ofNat 64 0xffffffffffffffff,
    BitVec.ofNat 64 0x0000000000000000 ]

/-- `p384Limbs` reads back to `p384Q` — the 7-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). -/
theorem bignumVal_p384Limbs : bignumVal p384Limbs = p384Q := by
  simp only [p384Limbs, p384Q, bignumVal, BitVec.toNat_ofNat]; norm_num

/-! ## 2. The P-384 base-field prime as a `KLimbPrime` (`k = 7`) — the ADD datum -/

/-- **The P-384 base-field prime as a `KLimbPrime` (`k = 7`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^7` by `norm_num`
    (pure-`Nat`); `bignumVal p384Limbs = q` by `bignumVal_p384Limbs`. The `k = 7`
    layout (top limb `0`) is what makes `2q ≤ (2^64)^7` hold (`2q ≈ 2^385 ≤ 2^448`);
    `k = 6` would fail it (`(2^64)^6 = 2^384 < 2q`, `norm_num` reducing `two_q_le` to
    `False`). -/
def p384KLimbPrime : KLimbPrime where
  k        := 7
  q        := p384Q
  nz       := ⟨by unfold p384Q; norm_num⟩
  ql       := p384Limbs
  ql_len   := rfl
  ql_val   := bignumVal_p384Limbs
  two_q_le := by unfold p384Q; norm_num

/-- **The P-384 base-field ADD commuting square.** The abstract P-384 base-field
    addition `a + b` (in `ZMod q` for the 384-bit prime `q = p384Q`), serialized
    by the 7-limb encoding `encMLK q 7`, equals the emitted 7×64-bit reducing kernel
    `mlAddModK` on the serialized operands, read through `bignumVal` — with the
    7-limb conditional-subtract modular reduce. The P-384 sibling of
    `p256_add_commutes`. -/
theorem p384_add_commutes (a b : ZMod p384Q) :
    (a + b).val
      = bignumVal (mlAddModK p384Limbs (encMLK p384Q 7 a) (encMLK p384Q 7 b)) :=
  encMLK_add_commutes p384KLimbPrime a b

/-! ## 3. A worked example: a P-384 base-field add whose sum WRAPS

Two P-384 base-field elements whose abstract sum exceeds `q` — so the 7-limb
conditional-subtract reduce *fires*. Take `a = q - 1 = -1` (the maximal residue) and
`b = 5`: in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the emitted kernel must
reduce. The abstract field equation `(-1) + 5 = 4 + 0` transfers (through
`mlAddK_spec_transfers`) to the emitted 7-limb kernel agreeing on the serialized
operands. -/

/-- **Worked wrapping example.** In the P-384 base field, `(-1) + 5` wraps to `4`.
    The abstract field equation `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the emitted
    7-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized operands
    — the wrapping case the 7-limb conditional-subtract reduce must get right. -/
theorem p384_add_wrap_example :
    bignumVal (mlAddModK p384Limbs
        (encMLK p384Q 7 (-1)) (encMLK p384Q 7 5))
      = bignumVal (mlAddModK p384Limbs
          (encMLK p384Q 7 4) (encMLK p384Q 7 0)) :=
  (mlAddK_spec_transfers p384KLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod p384Q) + 5 = 4; ring_nf)

/-! ## 4. The P-384 base-field MUL: the product-width Barrett reciprocal (`2k = 14`)

The Barrett reciprocal at the product width `2k = 14` (so the kernel's Barrett shift
`m = 64·14 = 896`): `p384Mu = ⌊(2^64)^14 / q⌋ = ⌊2^896 / q⌋`, a ~513-bit `Nat`. Defined
*as the side-condition value itself*, so `muTwo_val` is definitional — no `2^896`
literal needs `norm_num` evaluation. -/

/-- `NeZero p384Q` from the `KLimbPrime` datum (the projection instance does not fire
    on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero p384Q := p384KLimbPrime.nz

/-- The P-384 Barrett reciprocal at product width `2·7 = 14` limbs
    (`m = 64·14 = 896`): `⌊(2^64)^14 / q⌋ = ⌊2^896 / q⌋`. Defined *as the side-condition
    value itself* (`(2^64)^14 / p384Q`), so `muTwo_val` is definitional — no `2^896`
    literal needs `norm_num` evaluation. The re-limbing round-trip needs only
    `⌊N / q⌋ < (2^64)^14` (`Nat.div_lt_self`), never the digits of the quotient. -/
def p384Mu : Nat := (2 ^ 64) ^ 14 / p384Q

/-- `p384Mu` re-limbed to a 14×64-bit little-endian vector. -/
def p384MuLimbs : List (BitVec 64) := splitLimbsK 14 p384Mu

/-- `p384Mu < (2^64)^14`: the Barrett quotient `⌊N/q⌋ < N` for `0 < N`, `1 < q`
    (`Nat.div_lt_self`). The `1 < q` side condition closes by `norm_num` on the
    384-bit prime literal. -/
theorem p384Mu_lt : p384Mu < (2 ^ 64) ^ 14 := by
  unfold p384Mu
  refine Nat.div_lt_self (by positivity) ?_
  unfold p384Q; norm_num

/-- **The P-384 base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 7`).** Reuses `p384KLimbPrime`; the new data are the 14-limb
    reciprocal `p384MuLimbs` and its reciprocal-correctness side condition
    `bignumVal p384MuLimbs = (2^64)^14 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `p384Mu_lt` (no `2^896` literal evaluation). -/
def p384KLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := p384KLimbPrime
  muTwo     := p384MuLimbs
  muTwo_len := by
    show (splitLimbsK 14 p384Mu).length = 2 * p384KLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 14 p384Mu) = (2 ^ 64) ^ (2 * p384KLimbPrime.k) / p384KLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 14 p384Mu p384Mu_lt]
    show p384Mu = (2 ^ 64) ^ (2 * 7) / p384Q
    rfl
  k_pos := by decide

/-- **The P-384 base-field MUL commuting square.** The abstract P-384 base-field
    multiply `a * b` (in `ZMod q` for the 384-bit prime `q = p384Q`), serialized
    by the 7-limb encoding `encMLK q 7`, equals the emitted 14-limb Barrett-reducing
    kernel `mlMulMod` on the serialized operands, read through `bignumVal` — with the
    multi-limb Barrett modular reduce of the product. The P-384 sibling of
    `p256_mul_commutes`, completing the P-384 field-op set. -/
theorem p384_mul_commutes (a b : ZMod p384Q) :
    (a * b).val
      = bignumVal (mlMulMod 7 p384MuLimbs p384Limbs (encMLK p384Q 7 a) (encMLK p384Q 7 b)) :=
  encMLK_mul_commutes p384KLimbPrimeMul a b

/-! ## 5. The `EndoOpRealization`s for the P-384 ADD and MUL

`addModRealizationK p384Q` / `mulModRealizationK p384Q` tie the abstract `ZMod q`
ops to the value-carrier `bop`s `(· + ·) % q` / `(· * ·) % q`; the whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) is inherited from `ReprTransferExpr`
for free. -/

/-- **The `EndoOpRealization` for the P-384 base-field ADD.** `op = (· + ·)` on
    `ZMod p384Q`; `bop = fun x y => (x + y) % p384Q`; `enc = ZMod.val`. -/
def p384AddRealization :
    EndoOpRealization (fun a b : ZMod p384Q => a + b) (fun x y : Nat => (x + y) % p384Q) :=
  addModRealizationK p384Q

/-- **The `EndoOpRealization` for the P-384 base-field MUL.** `op = (· * ·)` on
    `ZMod p384Q`; `bop = fun x y => (x * y) % p384Q`; `enc = ZMod.val`. -/
def p384MulRealization :
    EndoOpRealization (fun a b : ZMod p384Q => a * b) (fun x y : Nat => (x * y) % p384Q) :=
  mulModRealizationK p384Q

/-! ## 6. A worked example: a P-384 base-field product whose reduce FIRES

Two P-384 base-field elements whose abstract product exceeds `q`, so the 14-limb
Barrett reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in
`ZMod q`, `(-1) * 2 = -2 = q - 2`, which equals `(-2) * 1` — the abstract field equation
`(-1) * 2 = (-2) * 1` transfers (through `mlMulK_spec_transfers`) to the emitted 14-limb
MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the P-384 base field, `(-1) * 2 = -2` (the maximal
    residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1` in
    `ZMod q` transfers to the emitted 14-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem p384_mul_wrap_example :
    bignumVal (mlMulMod 7 p384MuLimbs p384Limbs
        (encMLK p384Q 7 (-1)) (encMLK p384Q 7 2))
      = bignumVal (mlMulMod 7 p384MuLimbs p384Limbs
          (encMLK p384Q 7 (-2)) (encMLK p384Q 7 1)) :=
  (mlMulK_spec_transfers p384KLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod p384Q) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
