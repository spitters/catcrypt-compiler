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
# The BN254 base field ADD and MUL, realized relationally over a 4×64-bit carrier

`RelationalFrontBls377Add` realizes the `bls12_377` base-field **ADD** relationally
over a 6×64-bit carrier; `RelationalFrontBls377Mul` adds the **MUL** (Barrett of the
product). Both factor through the *carrier-parametric* multi-limb machinery in those
modules — `KLimbPrime`/`encMLK`/`splitLimbsK`/`mlAddModK`/`encMLK_add_commutes` (ADD)
and `KLimbPrimeMul`/`mlMulMod`/`encMLK_mul_commutes` (MUL) are stated at arbitrary
`k` and reuse the proved `MultiLimbKernel` value laws verbatim.

This module instantiates that machinery at the **BN254 base field** — a 254-bit prime
laid out in **`k = 4`** 64-bit limbs. BN254 (alt_bn128 / Barreto–Naehrig at 254 bits)
is the pairing-friendly curve of Ethereum's precompiles (EIP-196/197), Groth16/PLONK
verifiers, and Tornado-style ZK rollups. The repo's `Vale/BN254.lean` declares the
field leaves as *opaque axioms* (`BN254Fp`/`BN254Fp2`/`BN254Fp12`), not as a `Nat`
modulus, so they supply no `Nat` literal for the relational front; `bn254Q` is
defined here directly (the canonical BN254 base prime).

## BN254 instance scope

* **ADD (sorry-free):** the abstract `ZMod q` field add `a + b`, serialized by the
  4-limb encoding `encMLK q 4`, equals the emitted 4-limb reducing kernel `mlAddModK`
  on the serialized operands (with the `condSubLimbs` reduce) — read through
  `bignumVal`. This is `bn254_add_commutes`.
* **MUL (sorry-free):** the abstract `ZMod q` field multiply `a * b`, serialized by the
  same encoding, equals the emitted 8-limb (`2k = 8`) Barrett-reducing kernel `mlMulMod`
  on the serialized operands — with the multi-limb Barrett reduce of the
  product (`mu = ⌊(2^64)^8 / q⌋`, defined *as its side-condition value* so no `2^512`
  literal is evaluated). This is `bn254_mul_commutes`.
* The three Nat side conditions (`q ≠ 0`, `2q ≤ (2^64)^4`, `bignumVal bn254Limbs = q`)
  discharge by `norm_num`/`simp` on the 254-bit literal (no `native_decide`); since BN254
  is 254-bit, `2q < 2^256 = (2^64)^4`, so `k = 4` suffices. The Barrett reciprocal-width
  side conditions discharge by `Nat.div_lt_self` + the generic re-limbing round-trip,
  never evaluating the quotient digits.

With ADD + MUL both realized over the 4-limb carrier, the BN254 base-field op set is
complete for the inversion-free EC group law (Jacobian add/double are straight-line
`+`/`·`; field inversion is the separate safegcd leaf in `Vale/SafegcdBN254.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The BN254 base-field prime and its 4×64-bit limb vector

The BN254 base prime:
`p = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`
  `= 21888242871839275222246405745257275088696311157297823662689037894645226208583`.
254-bit, so `2p < 2^256 = (2^64)^4` and `k = 4` 64-bit limbs suffice. -/

/-- The BN254 base-field prime `q` (254-bit). -/
def bn254Q : Nat :=
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

/-- `FpBN254R` — the BN254 base field as a residue ring. -/
abbrev FpBN254R : Type := ZMod bn254Q

/-- The BN254 base-field prime as a 4×64-bit little-endian limb vector
    (`limb0` = low). `q = Σ bn254Limbsᵢ · 2^(64·i)`. -/
def bn254Limbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0x3c208c16d87cfd47,
    BitVec.ofNat 64 0x97816a916871ca8d,
    BitVec.ofNat 64 0xb85045b68181585d,
    BitVec.ofNat 64 0x30644e72e131a029 ]

/-- `bn254Limbs` reads back to `bn254Q` — the 4-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). -/
theorem bignumVal_bn254Limbs : bignumVal bn254Limbs = bn254Q := by
  simp only [bn254Limbs, bn254Q, bignumVal, BitVec.toNat_ofNat]; norm_num

/-! ## 2. The BN254 base-field prime as a `KLimbPrime` (`k = 4`) — the ADD datum -/

/-- **The BN254 base-field prime as a `KLimbPrime` (`k = 4`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^4` by `norm_num`
    (pure-`Nat`); `bignumVal bn254Limbs = q` by `bignumVal_bn254Limbs`. -/
def bn254KLimbPrime : KLimbPrime where
  k        := 4
  q        := bn254Q
  nz       := ⟨by unfold bn254Q; norm_num⟩
  ql       := bn254Limbs
  ql_len   := rfl
  ql_val   := bignumVal_bn254Limbs
  two_q_le := by unfold bn254Q; norm_num

/-- **The BN254 base-field ADD commuting square.** The abstract BN254 base-field
    addition `a + b` (in `ZMod q` for the 254-bit prime `q = bn254Q`),
    serialized by the 4-limb encoding `encMLK q 4`, equals the emitted 4×64-bit reducing
    kernel `mlAddModK` on the serialized operands, read through `bignumVal` — with the
    4-limb conditional-subtract modular reduce. The BN254 sibling of
    `bls377_add_commutes`. -/
theorem bn254_add_commutes (a b : ZMod bn254Q) :
    (a + b).val
      = bignumVal (mlAddModK bn254Limbs (encMLK bn254Q 4 a) (encMLK bn254Q 4 b)) :=
  encMLK_add_commutes bn254KLimbPrime a b

/-! ## 3. A worked example: a BN254 base-field add whose sum WRAPS

Two BN254 base-field elements whose abstract sum exceeds `q` — so the 4-limb
conditional-subtract reduce *fires*. Take `a = q - 1 = -1` (the maximal residue) and
`b = 5`: in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the emitted kernel must
reduce. The abstract field equation `(-1) + 5 = 4 + 0` transfers (through
`mlAddK_spec_transfers`) to the emitted 4-limb kernel agreeing on the serialized
operands. -/

/-- **Worked wrapping example.** In the BN254 base field, `(-1) + 5` wraps to `4`. The
    abstract field equation `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the emitted
    4-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized operands
    — the wrapping case the 4-limb conditional-subtract reduce must get right. -/
theorem bn254_add_wrap_example :
    bignumVal (mlAddModK bn254Limbs
        (encMLK bn254Q 4 (-1)) (encMLK bn254Q 4 5))
      = bignumVal (mlAddModK bn254Limbs
          (encMLK bn254Q 4 4) (encMLK bn254Q 4 0)) :=
  (mlAddK_spec_transfers bn254KLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod bn254Q) + 5 = 4; ring_nf)

/-! ## 4. The BN254 base-field MUL: the product-width Barrett reciprocal (`2k = 8`)

The Barrett reciprocal at the product width `2k = 8` (so the kernel's Barrett shift
`m = 64·8 = 512`): `bn254Mu = ⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`, a ~258-bit `Nat`. Defined
*as the side-condition value itself*, so `muTwo_val` is definitional — no `2^512`
literal needs `norm_num` evaluation. -/

/-- `NeZero bn254Q` from the `KLimbPrime` datum (the projection instance does not fire
    on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero bn254Q := bn254KLimbPrime.nz

/-- The BN254 Barrett reciprocal at product width `2·4 = 8` limbs (`m = 64·8 = 512`):
    `⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`. Defined *as the side-condition value itself*
    (`(2^64)^8 / bn254Q`), so `muTwo_val` is definitional — no `2^512` literal needs
    `norm_num` evaluation. The re-limbing round-trip needs only `⌊N / q⌋ < (2^64)^8`
    (`Nat.div_lt_self`), never the digits of the quotient. -/
def bn254Mu : Nat := (2 ^ 64) ^ 8 / bn254Q

/-- `bn254Mu` re-limbed to an 8×64-bit little-endian vector. -/
def bn254MuLimbs : List (BitVec 64) := splitLimbsK 8 bn254Mu

/-- `bn254Mu < (2^64)^8`: the Barrett quotient `⌊N/q⌋ < N` for `0 < N`, `1 < q`
    (`Nat.div_lt_self`). The `1 < q` side condition closes by `norm_num` on the
    254-bit prime literal. -/
theorem bn254Mu_lt : bn254Mu < (2 ^ 64) ^ 8 := by
  unfold bn254Mu
  refine Nat.div_lt_self (by positivity) ?_
  unfold bn254Q; norm_num

/-- **The BN254 base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 4`).** Reuses `bn254KLimbPrime`; the new data are the 8-limb
    reciprocal `bn254MuLimbs` and its reciprocal-correctness side condition
    `bignumVal bn254MuLimbs = (2^64)^8 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `bn254Mu_lt` (no `2^512` literal evaluation). -/
def bn254KLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := bn254KLimbPrime
  muTwo     := bn254MuLimbs
  muTwo_len := by
    show (splitLimbsK 8 bn254Mu).length = 2 * bn254KLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 8 bn254Mu) = (2 ^ 64) ^ (2 * bn254KLimbPrime.k) / bn254KLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 8 bn254Mu bn254Mu_lt]
    show bn254Mu = (2 ^ 64) ^ (2 * 4) / bn254Q
    rfl
  k_pos := by decide

/-- **The BN254 base-field MUL commuting square.** The abstract BN254 base-field
    multiply `a * b` (in `ZMod q` for the 254-bit prime `q = bn254Q`),
    serialized by the 4-limb encoding `encMLK q 4`, equals the emitted 8-limb
    Barrett-reducing kernel `mlMulMod` on the serialized operands, read through
    `bignumVal` — with the multi-limb Barrett modular reduce of the product. The
    BN254 sibling of `bls377_mul_commutes`, completing the BN254 field-op set. -/
theorem bn254_mul_commutes (a b : ZMod bn254Q) :
    (a * b).val
      = bignumVal (mlMulMod 4 bn254MuLimbs bn254Limbs (encMLK bn254Q 4 a) (encMLK bn254Q 4 b)) :=
  encMLK_mul_commutes bn254KLimbPrimeMul a b

/-! ## 5. The `EndoOpRealization`s for the BN254 ADD and MUL

`addModRealizationK bn254Q` / `mulModRealizationK bn254Q` tie the abstract `ZMod q`
ops to the value-carrier `bop`s `(· + ·) % q` / `(· * ·) % q`; the whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) is inherited from `ReprTransferExpr`
for free. -/

/-- **The `EndoOpRealization` for the BN254 base-field ADD.** `op = (· + ·)` on
    `ZMod bn254Q`; `bop = fun x y => (x + y) % bn254Q`; `enc = ZMod.val`. -/
def bn254AddRealization :
    EndoOpRealization (fun a b : ZMod bn254Q => a + b) (fun x y : Nat => (x + y) % bn254Q) :=
  addModRealizationK bn254Q

/-- **The `EndoOpRealization` for the BN254 base-field MUL.** `op = (· * ·)` on
    `ZMod bn254Q`; `bop = fun x y => (x * y) % bn254Q`; `enc = ZMod.val`. -/
def bn254MulRealization :
    EndoOpRealization (fun a b : ZMod bn254Q => a * b) (fun x y : Nat => (x * y) % bn254Q) :=
  mulModRealizationK bn254Q

/-! ## 6. A worked example: a BN254 base-field product whose reduce FIRES

Two BN254 base-field elements whose abstract product exceeds `q`, so the 8-limb Barrett
reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in `ZMod q`,
`(-1) * 2 = -2 = q - 2`, which equals `(-2) * 1` — the abstract field equation
`(-1) * 2 = (-2) * 1` transfers (through `mlMulK_spec_transfers`) to the emitted 8-limb
MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the BN254 base field, `(-1) * 2 = -2` (the maximal
    residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1` in
    `ZMod q` transfers to the emitted 8-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem bn254_mul_wrap_example :
    bignumVal (mlMulMod 4 bn254MuLimbs bn254Limbs
        (encMLK bn254Q 4 (-1)) (encMLK bn254Q 4 2))
      = bignumVal (mlMulMod 4 bn254MuLimbs bn254Limbs
          (encMLK bn254Q 4 (-2)) (encMLK bn254Q 4 1)) :=
  (mlMulK_spec_transfers bn254KLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod bn254Q) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
