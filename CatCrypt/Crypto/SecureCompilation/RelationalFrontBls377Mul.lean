/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFront
import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
import Mathlib.Data.ZMod.Basic

/-!
# The `bls12_377` base-field MULTIPLICATION, realized relationally over a 6×64-bit carrier

`RelationalFrontBls377Add` realizes the `bls12_377` base-field **ADD** relationally:
the abstract `ZMod q` add `a + b`, serialized by the 6-limb encoding `encMLK q 6`,
equals the emitted 6-limb reducing kernel `mlAddModK` (with the genuine
`condSubLimbs` reduce). Its docstring flags the remaining op: the multi-limb
**MUL** modular reduce — Barrett *of the product* at the `ZMod` value level — as the
larger piece for the full `bls12_377` EC group law.

This module **closes that piece**. It composes the two already-proved multi-limb
kernels from `MultiLimbKernel`:

* `mulBignum_val` — the *exact integer product*
  `bignumVal (mulBignum x y) = bignumVal x * bignumVal y` (unconditional);
* `barrettReduce_val` — the *Barrett field reduction*
  `bignumVal (barrettReduce x p mu W) = bignumVal x % bignumVal p`, for a `W`-limb
  input `x` and `W`-limb prime `p`, under the precondition that `mu` is the
  precomputed reciprocal `⌊(2^64)^W / bignumVal p⌋`.

into a `ZMod q` MUL commuting square at the genuine 377-bit `bls12_377` base-field
prime `q`, reusing `bls377Q`/`bls377Limbs`/`encMLK`/`splitLimbsK`/`KLimbPrime`
from `RelationalFrontBls377Add`.

## The reduce-width subtlety (why `W = 2k`)

`barrettReduce` reduces a `W`-limb input mod a `W`-limb prime. A product of two
`k`-limb operands is a `2k`-limb value (`x·y < q² < ((2^64)^k)² = (2^64)^(2k)`), so
the reduce runs at **`W = 2k`** limbs: the modulus `p` is the `k`-limb prime
*re-limbed to `2k`* (zero-extended), and `mu = ⌊(2^64)^(2k) / q⌋`. (The kernel pins
the Barrett shift `m` to the limb granularity `m = 64·W = 64·2k = 768` for
`bls12_377`, ≥ the textbook `2·377 = 754`; both are valid Barrett reciprocals — the
quotient-error bound `barrett_bound` holds for any `m` with `x < 2^m`.)

`mlMulMod` re-limbs the (variable-length) `mulBignum` product faithfully to exactly
`2k` limbs via `splitLimbsK (2k)` (`= the value's low 2k limbs`, faithful since the
product `< (2^64)^(2k)`), so the `barrettReduce` length precondition `x.length = W`
is met by construction.

## Honest scope

* **Demonstrated (sorry-free):** the generic `k`-limb `mlMulMod` and its value
  correctness `mlMulMod_val` (composing `mulBignum_val` + `barrettReduce_val`,
  discharging the reduce's input-bound from `x,y < q ⇒ x·y < q²`); the `ZMod q` MUL
  commuting square `encMLK_mul_commutes` (via `mlMulMod_val` + `ZMod.val_mul`); the
  `bls12_377` instance at the genuine 377-bit prime `q = bls377Q`, with the Barrett
  reciprocal `bls377Mu = ⌊2^768 / q⌋` computed as a `Nat` literal and discharged
  axiom-cleanly (`norm_num` on the `Nat.div`); a `RealizedKernel` / `EndoOpRealization`
  for the MUL; and a worked example.
* With **ADD** (`RelationalFrontBls377Add`) + **MUL** (here) both realized over the
  6-limb carrier, the `bls12_377` base-field op set is complete for the inversion-free
  EC group law (Jacobian add/double are straight-line `+`/`·`; field inversion is the
  separate piece, computed by an addition chain over the same MUL).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. Zero-extension: re-limbing the `k`-limb modulus to `2k` limbs -/

/-- A list of zero limbs has `bignumVal` zero. -/
theorem bignumVal_replicate_zero : ∀ n : Nat, bignumVal (List.replicate n (0 : BitVec 64)) = 0
  | 0 => by simp [bignumVal]
  | n + 1 => by
      have ih := bignumVal_replicate_zero n
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      simp only [List.replicate_succ, bignumVal, ih, h0, mul_zero, add_zero]

/-- Appending zero limbs leaves `bignumVal` unchanged: the high limbs contribute
    `0 · 2^(64·i)`. -/
theorem bignumVal_append_zeros : ∀ (l : List (BitVec 64)) (n : Nat),
    bignumVal (l ++ List.replicate n 0) = bignumVal l
  | [], n => by rw [List.nil_append, bignumVal_replicate_zero]; rfl
  | a :: as, n => by
      have ih := bignumVal_append_zeros as n
      simp only [List.cons_append, bignumVal, ih]

@[simp] theorem length_append_zeros (l : List (BitVec 64)) (n : Nat) :
    (l ++ List.replicate n 0).length = l.length + n := by
  simp [List.length_append]

/-! ## 2. The generic `k`-limb modular multiply `mlMulMod` and its value correctness -/

/-- **Multi-limb modular multiply.** Compute the `2k`-limb integer product
    (`mulBignum`, faithfully re-limbed to exactly `2k` limbs via `splitLimbsK`), then
    Barrett-reduce it mod the (zero-extended-to-`2k`-limb) prime `pl` using the
    precomputed reciprocal `mu = ⌊(2^64)^(2k) / bignumVal pl⌋`. The MUL analogue of
    `mlAddModK` (`addLimbs` + `condSubLimbs` ↦ `mulBignum` + `barrettReduce`). -/
def mlMulMod (k : Nat) (mu pl x y : List (BitVec 64)) : List (BitVec 64) :=
  barrettReduce
    (splitLimbsK (2 * k) (bignumVal (mulBignum x y)))
    (pl ++ List.replicate k 0)
    mu (2 * k)

/-- **`mlMulMod` value correctness.** For `k`-limb operands `x, y` strictly below the
    `k`-limb modulus `pl` (with `0 < bignumVal pl`), the emitted composite computes
    `(bignumVal x · bignumVal y) % bignumVal pl`. Composes `mulBignum_val` (exact
    integer product) and `barrettReduce_val` (Barrett field reduce); the reduce's
    input bound `x·y < (2^64)^(2k)` is discharged from `x, y < pl < (2^64)^k`. -/
theorem mlMulMod_val (k : Nat) (mu pl x y : List (BitVec 64)) (hk : 0 < k)
    (hxl : x.length = k) (hyl : y.length = k) (hpl : pl.length = k)
    (hmul : mu.length = 2 * k)
    (hppos : 0 < bignumVal pl)
    (hmuval : bignumVal mu = (2 ^ 64) ^ (2 * k) / bignumVal pl)
    (_hx : bignumVal x < bignumVal pl) (_hy : bignumVal y < bignumVal pl) :
    bignumVal (mlMulMod k mu pl x y) = (bignumVal x * bignumVal y) % bignumVal pl := by
  -- the zero-extended modulus: same value, length 2k
  set P := bignumVal pl with hP
  have hpl2_len : (pl ++ List.replicate k 0).length = 2 * k := by
    rw [length_append_zeros, hpl]; omega
  have hpl2_val : bignumVal (pl ++ List.replicate k 0) = P := by
    rw [bignumVal_append_zeros, hP]
  -- the product, re-limbed to exactly 2k limbs (faithful: product < (2^64)^(2k))
  have hplt : P < (2 ^ 64) ^ k := by
    have := bignumVal_lt pl; rw [hpl] at this; rw [hP]; exact this
  have hxlt : bignumVal x < (2 ^ 64) ^ k := by
    have := bignumVal_lt x; rw [hxl] at this; exact this
  have hylt : bignumVal y < (2 ^ 64) ^ k := by
    have := bignumVal_lt y; rw [hyl] at this; exact this
  have hpow2 : ((2 : ℕ) ^ 64) ^ (2 * k) = (2 ^ 64) ^ k * (2 ^ 64) ^ k := by
    rw [two_mul, pow_add]
  have hprodlt : bignumVal x * bignumVal y < (2 ^ 64) ^ (2 * k) := by
    rw [hpow2]; exact Nat.mul_lt_mul_of_lt_of_le hxlt (le_of_lt hylt) (by positivity)
  have hsplit_val :
      bignumVal (splitLimbsK (2 * k) (bignumVal (mulBignum x y))) = bignumVal x * bignumVal y := by
    rw [bignumVal_splitLimbsK_of_lt, mulBignum_val]
    rw [mulBignum_val]; exact hprodlt
  have hsplit_len : (splitLimbsK (2 * k) (bignumVal (mulBignum x y))).length = 2 * k :=
    splitLimbsK_length _ _
  -- apply Barrett reduce at width 2k
  unfold mlMulMod
  rw [barrettReduce_val
        (splitLimbsK (2 * k) (bignumVal (mulBignum x y)))
        (pl ++ List.replicate k 0) mu (2 * k)
        (by omega) hsplit_len hpl2_len hmul
        (by rw [hpl2_val]; exact hppos)
        (by rw [hpl2_val, hmuval])]
  rw [hsplit_val, hpl2_val]

/-! ## 3. The `EndoOpRealization` for `ZMod q` MUL over the multi-limb value carrier

Carrier = represented value `ℕ` (read by `bignumVal`); `enc = ZMod.val`,
`bop x y = (x * y) % q`. The single-op commuting square is `ZMod.val_mul`. The MUL
sibling of `addModRealizationK`. -/

/-- **The `EndoOpRealization` for `F_q` MUL via the canonical representative**, over the
    multi-limb value carrier `ℕ`. `op = (· * ·)`; `bop = fun x y => (x * y) % q`;
    `enc = ZMod.val`. The commuting square is `ZMod.val_mul`. -/
def mulModRealizationK (q : Nat) [NeZero q] :
    EndoOpRealization (fun a b : ZMod q => a * b) (fun x y : Nat => (x * y) % q) where
  enc := ZMod.val
  enc_inj := ZMod.val_injective q
  commutes := fun a b => by rw [ZMod.val_mul]

/-! ## 4. The `k`-limb MUL IR seam and commuting square -/

/-- A `k`-limb prime equipped with its precomputed Barrett reciprocal `muTwo` at the
    *product width* `2k` — the datum the multi-limb MUL needs on top of `KLimbPrime`. -/
structure KLimbPrimeMul extends KLimbPrime where
  /-- The Barrett reciprocal `⌊(2^64)^(2k) / q⌋` as a `2k`-limb vector. -/
  muTwo : List (BitVec 64)
  /-- `muTwo` has exactly `2k` limbs. -/
  muTwo_len : muTwo.length = 2 * k
  /-- `muTwo` reads back to the Barrett reciprocal at product width. -/
  muTwo_val : bignumVal muTwo = (2 ^ 64) ^ (2 * k) / q
  /-- The limb count is positive. -/
  k_pos : 0 < k

/-- **The multi-limb MUL IR seam at `k` limbs.** The emitted `mlMulMod` kernel, run on
    the encoded operands and read through `bignumVal`, computes the realization's `bop`
    value `(a.val * b.val) % q`. Reuses `mlMulMod_val` and `bignumVal_encMLK`. -/
theorem mlMul_seamK (Q : KLimbPrimeMul) (a b : ZMod Q.q) :
    bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b))
      = (a.val * b.val) % Q.q := by
  have hqk := Q.q_lt
  have hppos : 0 < bignumVal Q.ql := by rw [Q.ql_val]; exact Nat.pos_of_ne_zero (NeZero.ne Q.q)
  have hva : a.val < Q.q := ZMod.val_lt a
  have hvb : b.val < Q.q := ZMod.val_lt b
  have hea : bignumVal (encMLK Q.q Q.k a) = a.val := bignumVal_encMLK Q.q Q.k hqk a
  have heb : bignumVal (encMLK Q.q Q.k b) = b.val := bignumVal_encMLK Q.q Q.k hqk b
  rw [mlMulMod_val Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)
      Q.k_pos (encMLK_length _ _ _) (encMLK_length _ _ _) Q.ql_len Q.muTwo_len
      hppos
      (by rw [Q.ql_val]; exact Q.muTwo_val)
      (by rw [hea, Q.ql_val]; exact hva) (by rw [heb, Q.ql_val]; exact hvb)]
  rw [hea, heb, Q.ql_val]

/-- **The `k`-limb `F_q` MUL commuting square.** The abstract field multiply `a * b`
    (in `F_q`), serialized by the injective-not-surjective `k`-limb encoding `encMLK`,
    equals the emitted multi-limb Barrett-reducing kernel `mlMulMod` on the serialized
    operands, read through `bignumVal` — with the genuine multi-limb Barrett reduce. The
    MUL sibling of `encMLK_add_commutes`. -/
theorem encMLK_mul_commutes (Q : KLimbPrimeMul) (a b : ZMod Q.q) :
    (a * b).val = bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b)) := by
  rw [mlMul_seamK Q, ZMod.val_mul]

/-- **The `k`-limb MUL transfer demonstration.** An abstract `F_q` equation
    `a * b = a' * b'` transfers to an equation between the emitted multi-limb kernel's
    `bignumVal`-read value — through the injective-not-onto `encMLK`. -/
theorem mlMulK_spec_transfers (Q : KLimbPrimeMul) (a a' b b' : ZMod Q.q) :
    a * b = a' * b' ↔
      bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k b))
        = bignumVal (mlMulMod Q.k Q.muTwo Q.ql (encMLK Q.q Q.k a') (encMLK Q.q Q.k b')) := by
  rw [← encMLK_mul_commutes Q, ← encMLK_mul_commutes Q]
  exact ⟨fun h => by rw [h], fun h => (mulModRealizationK Q.q).enc_inj h⟩

/-! ## 5. The `bls12_377` instance: the genuine 377-bit base-field prime, `k = 6`

The Barrett reciprocal at the product width `2k = 12` (so `m = 768`):
`bls377Mu = ⌊2^768 / bls377Q⌋`, a ~391-bit `Nat`, computed as a literal and
re-limbed to 12×64-bit limbs by `splitLimbsK 12`. -/

/-- `NeZero bls377Q` from the `KLimbPrime` datum (the projection instance does not
    fire on the bare literal). Needed for the value-carrier `EndoOpRealization`. -/
instance : NeZero bls377Q := bls377KLimbPrime.nz

/-- The `bls12_377` Barrett reciprocal at product width `2·6 = 12` limbs
    (`m = 64·12 = 768`): `⌊(2^64)^12 / q⌋ = ⌊2^768 / q⌋`. Defined *as the side-condition
    value itself* (`(2^64)^12 / bls377Q`), so `muTwo_val` is definitional — no
    `2^768` literal needs `norm_num` evaluation (the exponentiation threshold blocks
    that). The re-limbing round-trip needs only `⌊N / q⌋ ≤ N < (2^64)^12` (`Nat.div_le_self`,
    `Nat.lt_pow_self`), never the digits of the quotient. -/
def bls377Mu : Nat := (2 ^ 64) ^ 12 / bls377Q

/-- `bls377Mu` re-limbed to a 12×64-bit little-endian vector. -/
def bls377MuLimbs : List (BitVec 64) := splitLimbsK 12 bls377Mu

/-- `(2^64)^12 = 2^768` as a `Nat` identity (limb granularity = textbook Barrett shift
    `m = 768`). Stated via `pow_mul` to avoid evaluating either literal. -/
theorem pow64_12_eq : ((2 : ℕ) ^ 64) ^ 12 = 2 ^ 768 := by rw [← pow_mul]

/-- `bls377Mu < (2^64)^12`: the Barrett quotient `⌊N/q⌋ ≤ N`, and `N = (2^64)^12 ≥ 1`
    is below its successor; more directly `N/q < N` needs `q ≥ 2`, but `⌊N/q⌋ ≤ N` and
    `N < (2^64)^12 + 1` suffices via `Nat.div_le_self`. We use the sharper
    `Nat.div_lt_self` (`0 < N`, `1 < q`). -/
theorem bls377Mu_lt : bls377Mu < (2 ^ 64) ^ 12 := by
  unfold bls377Mu
  refine Nat.div_lt_self (by positivity) ?_
  unfold bls377Q; norm_num

/-- **The `bls12_377` base-field prime with its product-width Barrett reciprocal as a
    `KLimbPrimeMul` (`k = 6`).** Reuses `bls377KLimbPrime`; the new data are the
    12-limb reciprocal `bls377MuLimbs` and the reciprocal-correctness side condition
    `bignumVal bls377MuLimbs = (2^64)^12 / q`, discharged by `bignumVal_splitLimbsK_of_lt`
    + `norm_num` (the `2^768` floor-division literal). -/
def bls377KLimbPrimeMul : KLimbPrimeMul where
  toKLimbPrime := bls377KLimbPrime
  muTwo     := bls377MuLimbs
  muTwo_len := by
    show (splitLimbsK 12 bls377Mu).length = 2 * bls377KLimbPrime.k
    rw [splitLimbsK_length]; rfl
  muTwo_val := by
    show bignumVal (splitLimbsK 12 bls377Mu) = (2 ^ 64) ^ (2 * bls377KLimbPrime.k) / bls377KLimbPrime.q
    rw [bignumVal_splitLimbsK_of_lt 12 bls377Mu bls377Mu_lt]
    show bls377Mu = (2 ^ 64) ^ (2 * 6) / bls377Q
    rfl
  k_pos := by decide

/-- **The `bls12_377` base-field MUL commuting square — the user's target field.** The
    abstract `bls12_377` base-field multiply `a * b` (in `ZMod q` for the genuine 377-bit
    prime `q = bls377Q`), serialized by the 6-limb encoding `encMLK q 6`, equals the
    emitted 12-limb Barrett-reducing kernel `mlMulMod` on the serialized operands, read
    through `bignumVal` — with the genuine multi-limb Barrett modular reduce of the
    product. The MUL sibling of `bls377_add_commutes`, completing the `bls12_377`
    field-op set. -/
theorem bls377_mul_commutes (a b : ZMod bls377Q) :
    (a * b).val
      = bignumVal (mlMulMod 6 bls377MuLimbs bls377Limbs (encMLK bls377Q 6 a) (encMLK bls377Q 6 b)) :=
  encMLK_mul_commutes bls377KLimbPrimeMul a b

/-! ## 6. The `RealizedKernel`/`EndoOpRealization` for the `bls12_377` MUL

`mulModRealizationK bls377Q` is the `EndoOpRealization` tying the abstract `ZMod q`
multiply to the value-carrier `bop = (· * ·) % q`; the whole-term abstraction theorem
(`OpExpr.expr_eq_transfer`) is inherited from `ReprTransferExpr` for free. -/

/-- **The `EndoOpRealization` for the `bls12_377` base-field MUL.** `op = (· * ·)` on
    `ZMod bls377Q`; `bop = fun x y => (x * y) % bls377Q` on the value carrier `ℕ`;
    `enc = ZMod.val` (injective). The MUL sibling of `addModRealizationK bls377Q`. -/
def bls377MulRealization :
    EndoOpRealization (fun a b : ZMod bls377Q => a * b) (fun x y : Nat => (x * y) % bls377Q) :=
  mulModRealizationK bls377Q

/-! ## 7. A worked example: a `bls12_377` base-field product whose reduce FIRES

Two `bls12_377` base-field elements whose abstract product exceeds `q`, so the 12-limb
Barrett reduce must wrap. Take `a = -1 = q - 1` (the maximal residue) and `b = 2`: in
`ZMod q`, `(-1) * 2 = -2 = q - 2 ≡ q - 2`, which equals `(q-2) * 1` — the abstract field
equation `(-1) * 2 = (q-2) * 1` transfers (through `mlMulK_spec_transfers`) to the
emitted 12-limb MUL-reduce kernel agreeing on the serialized operands. -/

/-- **Worked product example.** In the `bls12_377` base field, `(-1) * 2 = -2` (the
    maximal residue times `2`, reduced). The abstract field equation `(-1) * 2 = (-2) * 1`
    in `ZMod q` transfers to the emitted 12-limb `mlMulMod` kernel agreeing (through
    `bignumVal`) on the serialized operands — the wrapping case the multi-limb Barrett
    reduce must get right. -/
theorem bls377_mul_wrap_example :
    bignumVal (mlMulMod 6 bls377MuLimbs bls377Limbs
        (encMLK bls377Q 6 (-1)) (encMLK bls377Q 6 2))
      = bignumVal (mlMulMod 6 bls377MuLimbs bls377Limbs
          (encMLK bls377Q 6 (-2)) (encMLK bls377Q 6 1)) :=
  (mlMulK_spec_transfers bls377KLimbPrimeMul (-1) (-2) 2 1).mp
    (by show (-1 : ZMod bls377Q) * 2 = (-2) * 1; ring)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
