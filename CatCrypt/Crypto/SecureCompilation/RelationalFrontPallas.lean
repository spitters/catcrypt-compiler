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
# The Pallas base field ADD and MUL, realized relationally over a 4×64-bit carrier

`RelationalFrontBls377Add` realizes the `bls12_377` base-field **ADD** relationally
over a 6×64-bit carrier; `RelationalFrontBls377Mul` adds the **MUL** (Barrett of the
product). Both factor through the *carrier-parametric* multi-limb machinery in those
modules — `KLimbPrime`/`encMLK`/`splitLimbsK`/`mlAddModK`/`encMLK_add_commutes` (ADD)
and `KLimbPrimeMul`/`mlMulMod`/`encMLK_mul_commutes` (MUL) are stated at arbitrary
`k` and reuse the proved `MultiLimbKernel` value laws verbatim.

This module instantiates that machinery at the **Pallas base field** — a 255-bit prime
laid out in **`k = 4`** 64-bit limbs. Pallas is one half of the Pasta cycle
(Pallas / Vesta) used by Halo2 (Zcash Orchard), Mina (kimchi), and Aleo's SnarkVM for
IPA-based SNARKs with no trusted setup. The repo's `Vale/Pallas.lean` declares the
field leaves as *opaque axioms* (the AUCurves Bernstein–Yang safegcd inversion leaf),
not as a `Nat` modulus, so there is no reusable `Nat` literal; `pallasQ` is defined
here directly (the canonical Pasta Pallas base prime).

## Pallas instance scope

* **ADD (fully proved):** the abstract `ZMod q` field add `a + b`, serialized by the
  4-limb encoding `encMLK q 4`, equals the emitted 4-limb reducing kernel `mlAddModK`
  on the serialized operands (with the `condSubLimbs` reduce) — read through
  `bignumVal`. This is `pallas_add_commutes`.
* **MUL (fully proved):** the abstract `ZMod q` field multiply `a * b`, serialized by the
  same encoding, equals the emitted 8-limb (`2k = 8`) Barrett-reducing kernel `mlMulMod`
  on the serialized operands — with the multi-limb Barrett reduce of the
  product (`mu = ⌊(2^64)^8 / q⌋`, defined *as its side-condition value* so no `2^512`
  literal is evaluated). This is `pallas_mul_commutes`.
* The three Nat side conditions (`q ≠ 0`, `2q ≤ (2^64)^4`, `bignumVal pallasLimbs = q`)
  discharge by `norm_num`/`simp` on the 255-bit literal (no `native_decide`); the
  Barrett reciprocal-width side conditions discharge by `Nat.div_lt_self` + the generic
  re-limbing round-trip, never evaluating the quotient digits.

With ADD + MUL both realized over the 4-limb carrier, the Pallas base-field op set is
complete for the inversion-free EC group law (Jacobian add/double are straight-line
`+`/`·`; field inversion is the separate AUCurves safegcd leaf in `Vale/Pallas.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. The Pallas base-field prime and its 4×64-bit limb vector

The Pasta Pallas base prime (FIPS-style display):
`p = 2^254 + 45560315531419706090280762371685220353`
  `= 0x40000000_00000000_00000000_00000000_224698fc_094cf91b_992d30ed_00000001`
  `= 28948022309329048855892746252171976963363056481941560715954676764349967630337`.
This is the **base** field of Pallas (and the **scalar** field of Vesta — the Pasta
cycle property). 255-bit, so `k = 4` 64-bit limbs. -/

/-- The Pallas base-field prime `q` (255-bit). -/
def pallasQ : Nat :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- `FpPallas` — the Pallas base field as a residue ring. -/
abbrev FpPallas : Type := ZMod pallasQ

-- grind reduces mod p in FpPallas: a literal characteristic (grind_char_numeral).
grind_char_numeral FpPallas

/-- The Pallas base-field prime as a 4×64-bit little-endian limb vector
    (`limb0` = low). Matches the AUCurves saturated 4×u64 LE wire format for Pallas
    `Fp` elements (`q = Σ pallasLimbsᵢ · 2^(64·i)`). -/
def pallasLimbs : List (BitVec 64) :=
  [ BitVec.ofNat 64 0x992d30ed00000001,
    BitVec.ofNat 64 0x224698fc094cf91b,
    BitVec.ofNat 64 0x0000000000000000,
    BitVec.ofNat 64 0x4000000000000000 ]

/-- `pallasLimbs` reads back to `pallasQ` — the 4-limb vector represents the prime.
    Closed axiom-cleanly by `simp [bignumVal, BitVec.toNat_ofNat] + norm_num` (no
    `native_decide`). -/
theorem bignumVal_pallasLimbs : bignumVal pallasLimbs = pallasQ := by
  simp only [pallasLimbs, pallasQ, bignumVal, BitVec.toNat_ofNat]; norm_num

/-! ## 2. The Pallas base-field prime as a `KLimbPrime` (`k = 4`) — the ADD datum -/

/-- **The Pallas base-field prime as a `KLimbPrime` (`k = 4`).** All three side
    conditions discharge axiom-cleanly: `q ≠ 0` and `2q ≤ (2^64)^4` by `norm_num`
    (pure-`Nat`); `bignumVal pallasLimbs = q` by `bignumVal_pallasLimbs`. -/
def pallasKLimbPrime : KLimbPrime where
  k        := 4
  q        := pallasQ
  nz       := ⟨by unfold pallasQ; norm_num⟩
  ql       := pallasLimbs
  ql_len   := rfl
  ql_val   := bignumVal_pallasLimbs
  two_q_le := by unfold pallasQ; norm_num

/-- **The Pallas base-field ADD commuting square.** The abstract Pallas base-field
    addition `a + b` (in `ZMod q` for the 255-bit prime `q = pallasQ`),
    serialized by the 4-limb encoding `encMLK q 4`, equals the emitted 4×64-bit reducing
    kernel `mlAddModK` on the serialized operands, read through `bignumVal` — with the
    4-limb conditional-subtract modular reduce. The Pallas sibling of
    `bls377_add_commutes`. -/
theorem pallas_add_commutes (a b : ZMod pallasQ) :
    (a + b).val
      = bignumVal (mlAddModK pallasLimbs (encMLK pallasQ 4 a) (encMLK pallasQ 4 b)) :=
  encMLK_add_commutes pallasKLimbPrime a b

/-! ## 3. A worked example: a Pallas base-field add whose sum WRAPS

Two Pallas base-field elements whose abstract sum exceeds `q` — so the 4-limb
conditional-subtract reduce *fires*. Take `a = q - 1 = -1` (the maximal residue) and
`b = 5`: in `ZMod q`, `a + b = q - 1 + 5 = q + 4 ≡ 4`, which the emitted kernel must
reduce. The abstract field equation `(-1) + 5 = 4 + 0` transfers (through
`mlAddK_spec_transfers`) to the emitted 4-limb kernel agreeing on the serialized
operands. -/

/-- **Worked wrapping example.** In the Pallas base field, `(-1) + 5` wraps to `4`. The
    abstract field equation `(-1) + 5 = 4 + 0` in `ZMod q` transfers to the emitted
    4-limb `mlAddModK` kernel agreeing (through `bignumVal`) on the serialized operands
    — the wrapping case the 4-limb conditional-subtract reduce must get right. -/
theorem pallas_add_wrap_example :
    bignumVal (mlAddModK pallasLimbs
        (encMLK pallasQ 4 (-1)) (encMLK pallasQ 4 5))
      = bignumVal (mlAddModK pallasLimbs
          (encMLK pallasQ 4 4) (encMLK pallasQ 4 0)) :=
  (mlAddK_spec_transfers pallasKLimbPrime (-1) 4 5 0).mp
    (by show (-1 : ZMod pallasQ) + 5 = 4; ring_nf)

/-! ## 4. The Pallas base-field MUL: the product-width Barrett reciprocal (`2k = 8`)

The Barrett reciprocal at the product width `2k = 8` (so the kernel's Barrett shift
`m = 64·8 = 512`): `pallasMu = ⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`, a ~257-bit `Nat`. Defined
*as the side-condition value itself*, so `muTwo_val` is definitional — no `2^512`
literal needs `norm_num` evaluation. -/

/-- `NeZero pallasQ` from the `KLimbPrime` datum (the projection instance does not fire
    on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero pallasQ := pallasKLimbPrime.nz

/-- The Pallas Barrett reciprocal at product width `2·4 = 8` limbs (`m = 64·8 = 512`):
    `⌊(2^64)^8 / q⌋ = ⌊2^512 / q⌋`. Defined *as the side-condition value itself*
    (`(2^64)^8 / pallasQ`), so `muTwo_val` is definitional — no `2^512` literal needs
    `norm_num` evaluation. The re-limbing round-trip needs only `⌊N / q⌋ < (2^64)^8`
    (`Nat.div_lt_self`), never the digits of the quotient. -/
def pallasMu : Nat := (2 ^ 64) ^ 8 / pallasQ

/-- `pallasMu` re-limbed to an 8×64-bit little-endian vector. -/
def pallasMuLimbs : List (BitVec 64) := splitLimbsK 8 pallasMu

/-- `pallasMu < (2^64)^8`: the Barrett quotient `⌊N/q⌋ < N` for `0 < N`, `1 < q`
    (`Nat.div_lt_self`). The `1 < q` side condition closes by `norm_num` on the
    255-bit prime literal. -/
theorem pallasMu_lt : pallasMu < (2 ^ 64) ^ 8 := by
  unfold pallasMu
  refine Nat.div_lt_self (by positivity) ?_
  unfold pallasQ; norm_num

/-- **The Pallas base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 4`).** Reuses `pallasKLimbPrime`; the new data are the 8-limb
    reciprocal `pallasMuLimbs` and its reciprocal-correctness side condition
    `bignumVal pallasMuLimbs = (2^64)^8 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `pallasMu_lt` (no `2^512` literal evaluation). -/
def pallasKLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := pallasKLimbPrime
  muTwo     := pallasMuLimbs
  muTwo_len := by
    show (splitLimbsK 8 pallasMu).length = 2 * pallasKLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 8 pallasMu) = (2 ^ 64) ^ (2 * pallasKLimbPrime.k) / pallasKLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 8 pallasMu pallasMu_lt]
    show pallasMu = (2 ^ 64) ^ (2 * 4) / pallasQ
    rfl
  k_pos := by decide

/-- **The Pallas base-field MUL commuting square.** The abstract Pallas base-field
    multiply `a * b` (in `ZMod q` for the 255-bit prime `q = pallasQ`),
    serialized by the 4-limb encoding `encMLK q 4`, equals the emitted 8-limb
    Barrett-reducing kernel `mlMulMod` on the serialized operands, read through
    `bignumVal` — with the multi-limb Barrett modular reduce of the product. The
    Pallas sibling of `bls377_mul_commutes`, completing the Pallas field-op set. -/
theorem pallas_mul_commutes (a b : ZMod pallasQ) :
    (a * b).val
      = bignumVal (mlMulMod 4 pallasMuLimbs pallasLimbs (encMLK pallasQ 4 a) (encMLK pallasQ 4 b)) :=
  encMLK_mul_commutes pallasKLimbPrimeMul a b

/-! ## 5. The `EndoOpRealization`s for the Pallas ADD and MUL

`addModRealizationK pallasQ` / `mulModRealizationK pallasQ` tie the abstract `ZMod q`
ops to the value-carrier `bop`s `(· + ·) % q` / `(· * ·) % q`; the whole-term
abstraction theorem (`OpExpr.expr_eq_transfer`) is inherited from `ReprTransferExpr`
for free. -/

/-- **The `EndoOpRealization` for the Pallas base-field ADD.** `op = (· + ·)` on
    `ZMod pallasQ`; `bop = fun x y => (x + y) % pallasQ`; `enc = ZMod.val`. -/
def pallasAddRealization :
    EndoOpRealization (fun a b : ZMod pallasQ => a + b) (fun x y : Nat => (x + y) % pallasQ) :=
  addModRealizationK pallasQ

/-- **The `EndoOpRealization` for the Pallas base-field MUL.** `op = (· * ·)` on
    `ZMod pallasQ`; `bop = fun x y => (x * y) % pallasQ`; `enc = ZMod.val`. -/
def pallasMulRealization :
    EndoOpRealization (fun a b : ZMod pallasQ => a * b) (fun x y : Nat => (x * y) % pallasQ) :=
  mulModRealizationK pallasQ

/-! ## 6. A worked example: a Pallas base-field product whose reduce FIRES

Two Pallas base-field elements whose abstract product exceeds `q`, so the 8-limb Barrett
reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in `ZMod q`,
`(-1) * 2 = -2 = q - 2`, which equals `(-2) * 1` — the abstract field equation
`(-1) * 2 = (-2) * 1` transfers (through `mlMulK_spec_transfers`) to the emitted 8-limb
MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the Pallas base field, `(-1) * 2 = -2` (the maximal
    residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1` in
    `ZMod q` transfers to the emitted 8-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem pallas_mul_wrap_example :
    bignumVal (mlMulMod 4 pallasMuLimbs pallasLimbs
        (encMLK pallasQ 4 (-1)) (encMLK pallasQ 4 2))
      = bignumVal (mlMulMod 4 pallasMuLimbs pallasLimbs
          (encMLK pallasQ 4 (-2)) (encMLK pallasQ 4 1)) :=
  (mlMulK_spec_transfers pallasKLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod pallasQ) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
