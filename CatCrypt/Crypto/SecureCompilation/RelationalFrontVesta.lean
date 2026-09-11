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
# The Vesta base field ADD and MUL, realized relationally over a 4×64-bit carrier

`RelationalFrontPallas` realizes the **Pallas** base field (one half of the Pasta
cycle) relationally over a 4×64-bit carrier. This module is its **Vesta** sibling,
completing the Pasta cycle: Pallas and Vesta are a pair of primes each of which is
the other's scalar field. The Pallas *base* prime is the Vesta *scalar* prime, and
the **Vesta base prime** (realized here) is the **Pallas scalar prime**.

Both factor through the *carrier-parametric* multi-limb machinery in
`RelationalFrontBls377Add` / `RelationalFrontBls377Mul` —
`KLimbPrime`/`encMLK`/`splitLimbsK`/`mlAddModK`/`encMLK_add_commutes` (ADD) and
`KLimbPrimeMul`/`mlMulMod`/`encMLK_mul_commutes` (MUL) are stated at arbitrary `k`
and reuse the proved `MultiLimbKernel` value laws verbatim.

This module instantiates that machinery at the **Vesta base field** — a 255-bit
prime laid out in **`k = 4`** 64-bit limbs (`q ≈ 2²⁵⁴ < 2²⁵⁵`, so `2q < 2²⁵⁶ =
(2⁶⁴)⁴` and `k = 4` suffices). Vesta is one half of the Pasta cycle (Pallas / Vesta)
used by Halo2 (Zcash Orchard), Mina (kimchi), and Aleo's SnarkVM for IPA-based
SNARKs with no trusted setup. The repo's `Vale/Vesta.lean` declares the field leaves
as *opaque axioms* (the AUCurves Bernstein–Yang safegcd inversion leaf), not as a
`Nat` modulus, so there was no reusable `Nat` literal; `vestaQ` is defined here
directly (the canonical Pasta Vesta base prime). Its four little-endian limbs are the
same word values as `PastaBignumTierA.vestaLimbs` (the AUCurves `vesta_modulus`).

## Vesta instance scope (HONEST)

* **ADD (sorry-free):** the abstract `ZMod q` field add `a + b`, serialized by the
  4-limb encoding `encMLK q 4`, equals the emitted 4-limb reducing kernel `mlAddModK`
  on the serialized operands (with the genuine `condSubLimbs` reduce) — read through
  `bignumVal`. This is `vesta_add_commutes`.
* **MUL (sorry-free):** the abstract `ZMod q` field multiply `a * b`, serialized by
  the same encoding, equals the emitted 8-limb (`2k = 8`) Barrett-reducing kernel
  `mlMulMod` on the serialized operands — with the genuine multi-limb Barrett reduce
  of the product (`mu = ⌊(2^64)^8 / q⌋`, defined *as its side-condition value* so no
  `2^512` literal is evaluated). This is `vesta_mul_commutes`.
* The three Nat side conditions (`q ≠ 0`, `2q ≤ (2^64)^4`, `bignumVal vestaLimbs = q`)
  discharge by `norm_num`/`simp` on the 255-bit literal (no `native_decide`); the
  Barrett reciprocal-width side conditions discharge by `Nat.div_lt_self` + the generic
  re-limbing round-trip, never evaluating the quotient digits.

With ADD + MUL realized over the 4-limb carrier for both Pallas and Vesta, the Pasta
**cycle** base-field op set is complete for the inversion-free EC group law (Jacobian
add/double are straight-line `+`/`·`; field inversion is the separate AUCurves safegcd
leaf in `Vale/Vesta.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The Vesta base-field prime and its 4×64-bit limb vector

The Pasta Vesta base prime (FIPS-style display):
`q = 2^254 + 45560315531506369815346746415080538113`
  `= 0x40000000_00000000_00000000_00000000_224698fc_0994a8dd_8c46eb21_00000001`
  `= 28948022309329048855892746252171976963363056481941647379679742748393362948097`.
This is the **base** field of Vesta (and the **scalar** field of Pallas — the Pasta
cycle property). 255-bit, so `k = 4` 64-bit limbs. -/

/-- The Vesta base-field prime `q` (255-bit). -/
def vestaQ : Nat :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- `FpVesta` — the Vesta base field as a residue ring. -/
abbrev FpVesta : Type := ZMod vestaQ

/-- The Vesta base-field prime as a 4×64-bit little-endian limb vector
    (`limb0` = low). Matches the AUCurves saturated 4×u64 LE wire format for Vesta
    `Fp` elements (`q = Σ vestaLimbsᵢ · 2^(64·i)`); identical word values to
    `PastaBignumTierA.vestaLimbs`. -/
def vestaLimbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0x8c46eb2100000001,
    BitVec.ofNat 64 0x224698fc0994a8dd,
    BitVec.ofNat 64 0x0000000000000000,
    BitVec.ofNat 64 0x4000000000000000 ]

/-- `vestaLimbs` reads back to `vestaQ` — the 4-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). -/
theorem bignumVal_vestaLimbs : bignumVal vestaLimbs = vestaQ := by
  simp only [vestaLimbs, vestaQ, bignumVal, BitVec.toNat_ofNat]; norm_num

/-! ## 2. The Vesta base-field prime as a `KLimbPrime` (`k = 4`) — the ADD datum -/

/-- **The Vesta base-field prime as a `KLimbPrime` (`k = 4`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^4` by `norm_num`
    (pure-`Nat`); `bignumVal vestaLimbs = q` by `bignumVal_vestaLimbs`. -/
def vestaKLimbPrime : KLimbPrime where
  k        := 4
  q        := vestaQ
  nz       := ⟨by unfold vestaQ; norm_num⟩
  ql       := vestaLimbs
  ql_len   := rfl
  ql_val   := bignumVal_vestaLimbs
  two_q_le := by unfold vestaQ; norm_num

/-- **The Vesta base-field ADD commuting square.** The abstract Vesta base-field
    addition `a + b` (in `ZMod q` for the genuine 255-bit prime `q = vestaQ`),
    serialized by the 4-limb encoding `encMLK q 4`, equals the emitted 4×64-bit reducing
    kernel `mlAddModK` on the serialized operands, read through `bignumVal` — with the
    genuine 4-limb conditional-subtract modular reduce. The Vesta sibling of
    `pallas_add_commutes`. -/
theorem vesta_add_commutes (a b : ZMod vestaQ) :
    (a + b).val
      = bignumVal (mlAddModK vestaLimbs (encMLK vestaQ 4 a) (encMLK vestaQ 4 b)) :=
  encMLK_add_commutes vestaKLimbPrime a b

/-! ## 3. A worked example: a Vesta base-field add whose sum WRAPS

Two Vesta base-field elements whose abstract sum exceeds `q` — so the 4-limb
conditional-subtract reduce *fires*. Take `a = q - 1 = -1` (the maximal residue) and
`b = 5`: in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the emitted kernel must
reduce. The abstract field equation `(-1) + 5 = 4 + 0` transfers (through
`mlAddK_spec_transfers`) to the emitted 4-limb kernel agreeing on the serialized
operands. -/

/-- **Worked wrapping example.** In the Vesta base field, `(-1) + 5` wraps to `4`. The
    abstract field equation `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the emitted
    4-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized operands
    — the wrapping case the 4-limb conditional-subtract reduce must get right. -/
theorem vesta_add_wrap_example :
    bignumVal (mlAddModK vestaLimbs
        (encMLK vestaQ 4 (-1)) (encMLK vestaQ 4 5))
      = bignumVal (mlAddModK vestaLimbs
          (encMLK vestaQ 4 4) (encMLK vestaQ 4 0)) :=
  (mlAddK_spec_transfers vestaKLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod vestaQ) + 5 = 4; ring_nf)

/-! ## 4. The Vesta base-field MUL: the product-width Barrett reciprocal (`2k = 8`)

The Barrett reciprocal at the product width `2k = 8` (so the kernel's Barrett shift
`m = 64·8 = 512`): `vestaMu = ⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`, a ~257-bit `Nat`. Defined
*as the side-condition value itself*, so `muTwo_val` is definitional — no `2^512`
literal needs `norm_num` evaluation. -/

/-- `NeZero vestaQ` from the `KLimbPrime` datum (the projection instance does not fire
    on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero vestaQ := vestaKLimbPrime.nz

/-- The Vesta Barrett reciprocal at product width `2·4 = 8` limbs (`m = 64·8 = 512`):
    `⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`. Defined *as the side-condition value itself*
    (`(2^64)^8 / vestaQ`), so `muTwo_val` is definitional — no `2^512` literal needs
    `norm_num` evaluation. The re-limbing round-trip needs only `⌊N / q⌋ < (2^64)^8`
    (`Nat.div_lt_self`), never the digits of the quotient. -/
def vestaMu : Nat := (2 ^ 64) ^ 8 / vestaQ

/-- `vestaMu` re-limbed to an 8×64-bit little-endian vector. -/
def vestaMuLimbs : List (BitVec 64) := splitLimbsK 8 vestaMu

/-- `vestaMu < (2^64)^8`: the Barrett quotient `⌊N/q⌋ < N` for `0 < N`, `1 < q`
    (`Nat.div_lt_self`). The `1 < q` side condition closes by `norm_num` on the
    255-bit prime literal. -/
theorem vestaMu_lt : vestaMu < (2 ^ 64) ^ 8 := by
  unfold vestaMu
  refine Nat.div_lt_self (by positivity) ?_
  unfold vestaQ; norm_num

/-- **The Vesta base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 4`).** Reuses `vestaKLimbPrime`; the new data are the 8-limb
    reciprocal `vestaMuLimbs` and its reciprocal-correctness side condition
    `bignumVal vestaMuLimbs = (2^64)^8 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `vestaMu_lt` (no `2^512` literal evaluation). -/
def vestaKLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := vestaKLimbPrime
  muTwo     := vestaMuLimbs
  muTwo_len := by
    show (splitLimbsK 8 vestaMu).length = 2 * vestaKLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 8 vestaMu) = (2 ^ 64) ^ (2 * vestaKLimbPrime.k) / vestaKLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 8 vestaMu vestaMu_lt]
    show vestaMu = (2 ^ 64) ^ (2 * 4) / vestaQ
    rfl
  k_pos := by decide

/-- **The Vesta base-field MUL commuting square.** The abstract Vesta base-field
    multiply `a * b` (in `ZMod q` for the genuine 255-bit prime `q = vestaQ`),
    serialized by the 4-limb encoding `encMLK q 4`, equals the emitted 8-limb
    Barrett-reducing kernel `mlMulMod` on the serialized operands, read through
    `bignumVal` — with the genuine multi-limb Barrett modular reduce of the product. The
    Vesta sibling of `pallas_mul_commutes`, completing the Pasta-cycle field-op set. -/
theorem vesta_mul_commutes (a b : ZMod vestaQ) :
    (a * b).val
      = bignumVal (mlMulMod 4 vestaMuLimbs vestaLimbs (encMLK vestaQ 4 a) (encMLK vestaQ 4 b)) :=
  encMLK_mul_commutes vestaKLimbPrimeMul a b

/-! ## 5. The `EndoOpRealization`s for the Vesta ADD and MUL

`addModRealizationK vestaQ` / `mulModRealizationK vestaQ` tie the abstract `ZMod q`
ops to the value-carrier `bop`s `(· + ·) % q` / `(· * ·) % q`; the whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) is inherited from `ReprTransferExpr`
for free. -/

/-- **The `EndoOpRealization` for the Vesta base-field ADD.** `op = (· + ·)` on
    `ZMod vestaQ`; `bop = fun x y => (x + y) % vestaQ`; `enc = ZMod.val`. -/
def vestaAddRealization :
    EndoOpRealization (fun a b : ZMod vestaQ => a + b) (fun x y : Nat => (x + y) % vestaQ) :=
  addModRealizationK vestaQ

/-- **The `EndoOpRealization` for the Vesta base-field MUL.** `op = (· * ·)` on
    `ZMod vestaQ`; `bop = fun x y => (x * y) % vestaQ`; `enc = ZMod.val`. -/
def vestaMulRealization :
    EndoOpRealization (fun a b : ZMod vestaQ => a * b) (fun x y : Nat => (x * y) % vestaQ) :=
  mulModRealizationK vestaQ

/-! ## 6. A worked example: a Vesta base-field product whose reduce FIRES

Two Vesta base-field elements whose abstract product exceeds `q`, so the 8-limb Barrett
reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in `ZMod q`,
`(-1) * 2 = -2 = q - 2`, which equals `(-2) * 1` — the abstract field equation
`(-1) * 2 = (-2) * 1` transfers (through `mlMulK_spec_transfers`) to the emitted 8-limb
MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the Vesta base field, `(-1) * 2 = -2` (the maximal
    residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1` in
    `ZMod q` transfers to the emitted 8-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem vesta_mul_wrap_example :
    bignumVal (mlMulMod 4 vestaMuLimbs vestaLimbs
        (encMLK vestaQ 4 (-1)) (encMLK vestaQ 4 2))
      = bignumVal (mlMulMod 4 vestaMuLimbs vestaLimbs
          (encMLK vestaQ 4 (-2)) (encMLK vestaQ 4 1)) :=
  (mlMulK_spec_transfers vestaKLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod vestaQ) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
