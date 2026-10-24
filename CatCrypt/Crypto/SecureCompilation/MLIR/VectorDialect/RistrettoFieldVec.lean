/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public meta import CatCrypt.Crypto.Util.X25519Verified
public import CatCrypt.Crypto.Util.X25519Verified

/-!
# SIMD Ristretto / Curve25519 4-way packed field through the VectorDialect

dalek's `FieldElement2625x4` packs **four** Curve25519 field elements as
`10 × 26/25`-bit limbs across AVX2 lanes, so a point operation runs its four
coordinate multiplies in parallel (`VPMULUDQ` 32×32→64 over fixed lanes,
`VPADD`/`VPSRL` for the in-lane carry/reduce). This module models that layout
next to the scalar `5×51` field.

The lattice 4-way NTT (`MldsaNtt4WayVec`) packs field coefficients into AVX2 lanes
using `LaneMap.laneMap_eq_scalarMap` and the dialect `mul`/`add`/`shiftR` lowering
lemmas. This module follows the same pattern on the curve25519 field, with the
radix `10×26/25` and an x19 Solinas reduce (`2^255 ≡ 19`) in place of the NTT's
Montgomery reduce.

## What is proved here

Limbs are modelled as unbounded integers (`Fin 10 → ℤ`), decoded into
`Fp25519 = ZMod (2^255 − 19)`; lane overflow of the 32/64-bit lane words is not
modelled for the limb arithmetic.

* `two_pow_high` — `(2 : Fp25519)^(255 + e) = 19 · 2^e`, so a term at bit
  position `255 + e` folds to `19 · 2^e`.
* `eval2625_reduce19` — the fold `reduce19`, which adds `19 · limb` of the nine
  high limbs (10..18) of a nineteen-limb product to the low limbs, preserves the
  `Fp25519` value.
* `evalN_prod19` / `prodEval_eq_mul` — the nineteen-limb schoolbook product
  `prod19` (limb `k` is `Σ_{i+j=k} c_ij·a_i·b_j`, with `c_ij = 2` when `i` and `j`
  are both odd, since `weight i + weight j = weight (i+j) + 1` then) decodes to
  `eval2625 a * eval2625 b`.
* `mul2625_decode` / `sqr2625_decode` / `mul2625x4_decode` — the multiply
  `mul2625 a b = reduce19 (prod19 a b)` decodes to the field product.
* `pow2625_decode` / `inv2625_decode` — square-and-multiply exponentiation built
  from `mul2625` decodes to the field power, and `inv2625 a = pow2625 a (p − 2)`
  decodes to the field inverse (Fermat).

## Lane-parallel structure

The four field elements ride the four AVX2 lanes; applying any per-lane field op
in parallel equals running it on each lane sequentially — `laneMap_eq_scalarMap`
at `α = the 10-limb field element`, `L = 4` (`field4way_lane_map`).

## Edwards point arithmetic

`edwardsAdd2625_decode` shows that the affine twisted-Edwards point-add built from
`mul2625` / `add2625` / `sub2625` / `inv2625` and the limb constant `one2625`
decodes to `ed25519AffineAdd` over `Fp25519`, for a limb vector `dL` that decodes
to `ed25519D`. The double (`edwardsDouble2625_decode`) is `P + P`.

## Lane words

§6 gives the dialect ops at the `VPMULUDQ` lane shape: four `BitVec 64` lanes,
with `lmuludq` the product of the low 32 bits of each operand, exact in 64 bits
(`lmuludq_toNat`), and `VPADDQ` / `VPSRLQ` as lane add and shift. No theorem
connects these lane words to the integer limbs of §§1–5.

## Constant-time

`PackedFieldOp` names lane intrinsics, including the data-dependent forms
`jccLane` (a conditional branch on a lane value) and `gatherLane` (a memory load
indexed by a lane value). `PackedFieldOp.dataIndep` is `false` exactly on those
two. `ct_data_indep` states that the op list `mulReduceOps` contains neither. The
op list is not derived from `mul2625` or from emitted code, and no leakage
semantics is given for the ops.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.RistrettoFieldVec

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
open CatCrypt.Util

/-! ## 1. The `10 × 26/25`-bit radix layout

A `2625` field element is ten limbs. Limb `i` carries weight `2^(weight i)`
where the weights alternate `+26, +25, +26, …` starting at `0`:
`0, 26, 51, 77, 102, 128, 153, 179, 204, 230`. The closed form is
`weight i = (51 * i + 1) / 2` (Nat division), i.e. `⌈25.5 · i⌉`. A field-element
*product* spans nineteen limbs (degree `0..18`); limb `10 + k` lands at weight
`weight k + 255`, which the x19 Solinas wrap folds back. -/

/-- Weight (bit position) of limb `i` in the `2625` radix: `0,26,51,77,…,230`. -/
def weight (i : Nat) : Nat := (51 * i + 1) / 2

/-- Limb `10 + k` of a product lands `255` bits above limb `k`. -/
theorem weight_high (k : Nat) : weight (10 + k) = weight k + 255 := by
  unfold weight
  omega

/-- The weights are additive up to one bit: `weight i + weight j` is
    `weight (i + j) + 1` when `i` and `j` are both odd, and `weight (i + j)`
    otherwise. -/
theorem weight_add (i j : Nat) :
    weight i + weight j = weight (i + j) + (if i % 2 = 1 ∧ j % 2 = 1 then 1 else 0) := by
  unfold weight
  split_ifs with h <;> omega

/-- A `2625` field element: ten integer limbs (radix `26/25`). We carry limbs as
    `ℤ` (signed-limb friendly, as dalek's `i32`/`i64` lanes are) and decode into
    `Fp25519` via the weighted sum. -/
abbrev Limbs10 : Type := Fin 10 → ℤ

/-- A product / unreduced element: nineteen limbs (degrees `0..18`). -/
abbrev Limbs19 : Type := Fin 19 → ℤ

/-- Decode `n` limbs `l` with the `2625` weights into `Fp25519`:
    `Σ_{i<n} l i · 2^(weight i)`. -/
def evalN (n : Nat) (l : Fin n → ℤ) : Fp25519 :=
  ∑ i : Fin n, (l i : Fp25519) * (2 : Fp25519) ^ weight i

/-- Decode a ten-limb element. -/
def eval2625 (l : Limbs10) : Fp25519 := evalN 10 l

/-! ## 2. The x19 Solinas wrap

In `Fp25519 = ZMod (2^255 − 19)` we have `(2 : Fp25519) ^ 255 = 19`, because
`2^255 − 19 ≡ 0`. Hence a limb at weight `255 + e` reduces to `19 · 2^e` times
its value. -/

/-- **The `2^255 = 19` identity in `Fp25519`.** -/
theorem two_pow_255 : (2 : Fp25519) ^ 255 = 19 := by
  have hp : ((2 ^ 255 - 19 : Nat) : Fp25519) = 0 := ZMod.natCast_self P25519
  have h19le : 19 ≤ 2 ^ 255 := by norm_num
  rw [Nat.cast_sub h19le, Nat.cast_pow] at hp
  have : (2 : Fp25519) ^ 255 = ((19 : Nat) : Fp25519) := sub_eq_zero.mp hp
  rw [this]; norm_num

/-- **The wrap identity at an arbitrary offset.** A limb value `v` at weight
    `255 + e` decodes to `19 · v · 2^e` — i.e. `2^(255+e) = 19 · 2^e`. -/
theorem two_pow_high (e : Nat) : (2 : Fp25519) ^ (255 + e) = 19 * (2 : Fp25519) ^ e := by
  rw [pow_add, two_pow_255]

/-! ## 3. Folding the high limbs of a product into the low ten

A nineteen-limb product `p` splits into low ten (degrees `0..9`) and high nine
(degrees `10..18`). The reduce produces ten limbs
`reduce19 p i = p_low i + 19 · p_high i` where `p_high i = p (10 + i)` for
`i < 9` and `0` for `i = 9`. -/

/-- The reduced ten limbs of a nineteen-limb product: low limb plus `19×` the
    high limb that wraps onto it. Degrees `10..18` wrap onto degrees `0..8`. -/
def reduce19 (p : Limbs19) : Limbs10 := fun i =>
  if h : (i : Nat) < 9 then
    p ⟨i, by have := i.isLt; omega⟩ + 19 * p ⟨10 + i, by omega⟩
  else
    p ⟨i, by have := i.isLt; omega⟩

/-- **The x19 fold preserves the field value.**
    Decoding the reduced ten limbs equals decoding all nineteen limbs — the high
    nine limbs, weighted `2^(255 + weight k)`, fold onto the low limbs as
    `19 · 2^(weight k)` by `two_pow_high`. The limbs are integers; the statement
    says nothing about limb bounds. -/
theorem eval2625_reduce19 (p : Limbs19) :
    eval2625 (reduce19 p) = evalN 19 p := by
  unfold eval2625 evalN reduce19
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.val_succ, Fin.val_zero]
  simp only [show weight 0 = 0 by decide, show weight 1 = 26 by decide,
    show weight 2 = 51 by decide, show weight 3 = 77 by decide,
    show weight 4 = 102 by decide, show weight 5 = 128 by decide,
    show weight 6 = 153 by decide, show weight 7 = 179 by decide,
    show weight 8 = 204 by decide, show weight 9 = 230 by decide,
    show weight 10 = 255 by decide, show weight 11 = 281 by decide,
    show weight 12 = 306 by decide, show weight 13 = 332 by decide,
    show weight 14 = 357 by decide, show weight 15 = 383 by decide,
    show weight 16 = 408 by decide, show weight 17 = 434 by decide,
    show weight 18 = 459 by decide]
  push_cast
  rw [show (2 : Fp25519) ^ 255 = 19 from two_pow_255,
      show (2 : Fp25519) ^ 281 = 19 * 2 ^ 26 by rw [show 281 = 255 + 26 from rfl, two_pow_high],
      show (2 : Fp25519) ^ 306 = 19 * 2 ^ 51 by rw [show 306 = 255 + 51 from rfl, two_pow_high],
      show (2 : Fp25519) ^ 332 = 19 * 2 ^ 77 by rw [show 332 = 255 + 77 from rfl, two_pow_high],
      show (2 : Fp25519) ^ 357 = 19 * 2 ^ 102 by rw [show 357 = 255 + 102 from rfl, two_pow_high],
      show (2 : Fp25519) ^ 383 = 19 * 2 ^ 128 by rw [show 383 = 255 + 128 from rfl, two_pow_high],
      show (2 : Fp25519) ^ 408 = 19 * 2 ^ 153 by rw [show 408 = 255 + 153 from rfl, two_pow_high],
      show (2 : Fp25519) ^ 434 = 19 * 2 ^ 179 by rw [show 434 = 255 + 179 from rfl, two_pow_high],
      show (2 : Fp25519) ^ 459 = 19 * 2 ^ 204 by rw [show 459 = 255 + 204 from rfl, two_pow_high]]
  ring

/-! ## 4. The schoolbook multiply and the reduce

The `VPMULUDQ`s form, for each limb-index pair `(i, j)`, the lane product
`a_i · b_j`, which lands at bit position `weight i + weight j`. The unreduced
product decode is the double sum `prodEval`. Grouping by degree `k = i + j`, the
product at bit position `weight i + weight j = weight k + 1` (both odd) is the
limb `2·a_i·b_j` at weight `weight k`, which gives the nineteen-limb product
`prod19`. The multiply `mul2625` is `reduce19 ∘ prod19`. -/

/-- The unreduced product decode: `Σ_{i,j} a_i b_j · 2^(weight i + weight j)`. -/
def prodEval (a b : Limbs10) : Fp25519 :=
  ∑ i : Fin 10, ∑ j : Fin 10,
    ((a i * b j : ℤ) : Fp25519) * (2 : Fp25519) ^ (weight i + weight j)

/-- **The unreduced product decode is the field product** (`Finset.sum_mul_sum`). -/
theorem prodEval_eq_mul (a b : Limbs10) :
    prodEval a b = eval2625 a * eval2625 b := by
  unfold prodEval eval2625 evalN
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  push_cast
  rw [pow_add]
  ring

/-- The coefficient of `a_i·b_j` in limb `i + j` of the product: `2` when `i` and
    `j` are both odd, `1` otherwise. -/
def prodCoeff (i j : Nat) : ℤ := if i % 2 = 1 ∧ j % 2 = 1 then 2 else 1

/-- The nineteen-limb schoolbook product: limb `k` is
    `Σ_{i+j=k} prodCoeff i j · a_i · b_j`. -/
def prod19 (a b : Limbs10) : Limbs19 := fun k =>
  ∑ i : Fin 10, ∑ j : Fin 10, if (i : Nat) + j = k then prodCoeff i j * a i * b j else 0

/-- The schoolbook product limbs decode to the unreduced product decode. -/
theorem evalN_prod19 (a b : Limbs10) : evalN 19 (prod19 a b) = prodEval a b := by
  unfold evalN prod19 prodEval
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hk : (i : Nat) + j < 19 := by omega
  rw [Finset.sum_eq_single ⟨(i : Nat) + j, hk⟩]
  · simp only [ite_true]
    push_cast
    rw [weight_add i j, prodCoeff]
    split_ifs <;> push_cast <;> ring
  · intro k _ hk'
    rw [ite_eq_right (fun h => hk' (Fin.ext h.symm)), Int.cast_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The packed field multiply: the schoolbook product `prod19` folded by
    `reduce19`. -/
def mul2625 (a b : Limbs10) : Limbs10 := reduce19 (prod19 a b)

/-- **Decode of the packed multiply.** `mul2625 a b` decodes to
    `eval2625 a * eval2625 b`. -/
theorem mul2625_decode (a b : Limbs10) :
    eval2625 (mul2625 a b) = eval2625 a * eval2625 b := by
  rw [mul2625, eval2625_reduce19, evalN_prod19, prodEval_eq_mul]

/-- The squaring specialization: `eval (a²) = (eval a)²`. -/
theorem sqr2625_decode (a : Limbs10) :
    eval2625 (mul2625 a a) = eval2625 a ^ 2 := by
  rw [mul2625_decode, sq]

/-- The limb vector of `1`: limb 0 is `1`, the others `0`. -/
def one2625 : Limbs10 := fun i => if (i : Nat) = 0 then 1 else 0

theorem one2625_decode : eval2625 one2625 = 1 := by
  unfold eval2625 evalN one2625
  simp [weight]

/-- Square-and-multiply exponentiation over the packed field:
    `pow2625 a n = (pow2625 a (n/2))² · a^(n mod 2)`. -/
def pow2625 (a : Limbs10) (n : Nat) : Limbs10 :=
  if h : n = 0 then one2625
  else
    let hp := pow2625 a (n / 2)
    let sq := mul2625 hp hp
    if n % 2 = 1 then mul2625 sq a else sq
termination_by n
decreasing_by omega

/-- `pow2625 a n` decodes to `(eval2625 a)^n`. -/
theorem pow2625_decode (a : Limbs10) (n : Nat) : eval2625 (pow2625 a n) = eval2625 a ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [pow2625]
    split_ifs with h0 h1
    · subst h0; simp [one2625_decode]
    · simp only [mul2625_decode, ih (n / 2) (by omega)]
      rw [← pow_add, ← pow_succ]
      congr 1; omega
    · simp only [mul2625_decode, ih (n / 2) (by omega)]
      rw [← pow_add]
      congr 1; omega

/-- The packed field inverse `a^(p − 2)`. -/
def inv2625 (a : Limbs10) : Limbs10 := pow2625 a (P25519 - 2)

/-- `inv2625 a` decodes to `(eval2625 a)⁻¹` (with `0⁻¹ = 0`). -/
theorem inv2625_decode (a : Limbs10) : eval2625 (inv2625 a) = (eval2625 a)⁻¹ := by
  rw [inv2625, pow2625_decode]
  have := Fact.mk p25519_prime
  generalize eval2625 a = x
  have hp2 : P25519 - 2 ≠ 0 := by unfold P25519; norm_num
  by_cases hx : x = 0
  · subst hx; rw [zero_pow hp2, inv_zero]
  · refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ, show P25519 - 2 + 1 = P25519 - 1 by unfold P25519; norm_num]
    exact ZMod.pow_card_sub_one_eq_one hx

/-! ## 5. Lane-parallel structure: four field elements, one op

The `2625x4` layout runs the same field op on each of the four AVX2 lanes. By
`laneMap_eq_scalarMap` at `α = Limbs10`, `L = 4`, applying any per-lane field
function in parallel equals running it sequentially per lane. -/

/-- A `2625x4` packed value: four ten-limb field elements (one per AVX2 lane). -/
abbrev Fe2625x4 : Type := Fin 4 → Limbs10

/-- **The Ristretto 4-way lane-map equality** (`laneMap_eq_scalarMap` at
    `α = Limbs10`, `L = 4`). -/
theorem field4way_lane_map (f : Limbs10 → Limbs10) (v : Fe2625x4) :
    laneMap f v = (fun i => f (v i)) :=
  laneMap_eq_scalarMap f v

/-- The 4-way packed multiply: lane-wise `mul2625` of two packed values. -/
def mul2625x4 (a b : Fe2625x4) : Fe2625x4 := fun i => mul2625 (a i) (b i)

/-- **The 4-way packed multiply decodes lane-wise to the field product.** -/
theorem mul2625x4_decode (a b : Fe2625x4) (i : Fin 4) :
    eval2625 (mul2625x4 a b i) = eval2625 (a i) * eval2625 (b i) :=
  mul2625_decode (a i) (b i)

/-! ## 6. The packed lane ops as dialect `mul` / `add` / `shiftR`

`VPMULUDQ`, `VPADDQ` and `VPSRLQ` act on four `BitVec 64` lanes of a `__m256i`.
`VPMULUDQ` multiplies the low 32 bits of each operand lane into a 64-bit lane
result, which is exact (`lmuludq_toNat`). The theorems below state the dialect
denotation and lowering of these ops at that shape. -/

/-- The number of `u64` lanes in a `__m256i`. -/
abbrev limbLaneN : Nat := 4

/-- The `BitVec 64` lane add (`VPADDQ`). -/
abbrev ladd (x y : BitVec 64) : BitVec 64 := x + y

/-- The `VPMULUDQ` lane multiply: the product of the low 32 bits of each operand,
    as a 64-bit word. -/
def lmuludq (x y : BitVec 64) : BitVec 64 :=
  (x.truncate 32).zeroExtend 64 * (y.truncate 32).zeroExtend 64

/-- The `VPMULUDQ` lane product is the exact product of the operands' low 32 bits. -/
theorem lmuludq_toNat (x y : BitVec 64) :
    (lmuludq x y).toNat = (x.toNat % 2 ^ 32) * (y.toNat % 2 ^ 32) := by
  unfold lmuludq
  rw [BitVec.toNat_mul]
  simp only [BitVec.toNat_setWidth]
  have h1 : x.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have h2 : y.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have h3 : (x.toNat % 2 ^ 32) * (y.toNat % 2 ^ 32) < 2 ^ 64 := by
    calc _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt (by omega : x.toNat % 2 ^ 32 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : y.toNat % 2 ^ 32 < 2 ^ 64), Nat.mod_eq_of_lt h3]

/-- The `BitVec 64` lane logical shift-right (`VPSRLQ`, the carry shift). -/
abbrev lshr (x : BitVec 64) (m : Nat) : BitVec 64 := x >>> m

/-- The packed limb-add denotes the dialect `add` op pointwise (`VPADDQ`). -/
theorem limbAdd_denote (v w : VectorTy (BitVec 64) limbLaneN) :
    denoteVectorOp (.add ladd v w : VectorOp (BitVec 64) limbLaneN)
      = .vec (fun i => v i + w i) := rfl

/-- The `VPMULUDQ` lane multiply denotes the dialect `mul` op pointwise. -/
theorem limbMul_denote (v w : VectorTy (BitVec 64) limbLaneN) :
    denoteVectorOp (.mul lmuludq v w : VectorOp (BitVec 64) limbLaneN)
      = .vec (fun i => lmuludq (v i) (w i)) := rfl

/-- The carry right-shift denotes the dialect `shiftR` op (`VPSRLQ`). -/
theorem limbShr_denote (m : Nat) (v : VectorTy (BitVec 64) limbLaneN) :
    denoteVectorOp (.shiftR lshr m v : VectorOp (BitVec 64) limbLaneN)
      = .vec (fun i => v i >>> m) := rfl

/-- The three lane ops lower to per-lane scalar expansions with the stated
    denotation: `lower_add_correct`, `lower_mul_correct` and
    `lower_shiftR_correct` instantiated at four `BitVec 64` lanes. -/
theorem ristretto_ops_lower_correct (v w : VectorTy (BitVec 64) limbLaneN) (m : Nat) :
    (lower (0 : BitVec 64) (.add ladd v w)).map (·.denote)
        = some (VectorTy.map₂ ladd v w)
      ∧ (lower (0 : BitVec 64) (.mul lmuludq v w)).map (·.denote)
        = some (VectorTy.map₂ lmuludq v w)
      ∧ (lower (0 : BitVec 64) (.shiftR lshr m v)).map (·.denote)
        = some (VectorTy.map₁imm lshr m v) :=
  ⟨ lower_add_correct (0 : BitVec 64) ladd v w
  , lower_mul_correct (0 : BitVec 64) lmuludq v w
  , lower_shiftR_correct (0 : BitVec 64) lshr m v ⟩

/-! ## 7. Vectorized Edwards point-add over the packed field

The affine complete addition law (RFC 8032 §5.1, `a = −1`) over the packed field,
decoding each coordinate through `eval2625`. It equals `ed25519AffineAdd` over
`Fp25519`. -/

/-- Limb-wise add of two ten-limb elements (`VPADD`); decodes additively. -/
def add2625 (a b : Limbs10) : Limbs10 := fun i => a i + b i

/-- Limb-wise subtract (`VPSUB`); decodes by `eval(a) − eval(b)`. -/
def sub2625 (a b : Limbs10) : Limbs10 := fun i => a i - b i

/-- The limb-wise add decodes to the field sum. -/
theorem add2625_decode (a b : Limbs10) :
    eval2625 (add2625 a b) = eval2625 a + eval2625 b := by
  unfold eval2625 evalN add2625
  rw [← Finset.sum_add_distrib]
  congr 1; funext i; push_cast; ring

/-- The limb-wise subtract decodes to the field difference. -/
theorem sub2625_decode (a b : Limbs10) :
    eval2625 (sub2625 a b) = eval2625 a - eval2625 b := by
  unfold eval2625 evalN sub2625
  rw [← Finset.sum_sub_distrib]
  congr 1; funext i; push_cast; ring

/-- An on-lane packed affine point: the `x` and `y` coordinates as ten-limb
    packed field elements. -/
structure Point2625 where
  /-- Affine `x`-coordinate limbs. -/
  x : Limbs10
  /-- Affine `y`-coordinate limbs. -/
  y : Limbs10

/-- Decode a packed point to the abstract `Ed25519Point`. -/
def Point2625.toAlg (P : Point2625) : Ed25519Point :=
  { x := eval2625 P.x, y := eval2625 P.y }

/-- The vectorized affine point-add over the packed field, built from `mul2625`,
    `add2625`, `sub2625`, `inv2625` and `one2625`; `dL` is the limb vector of the
    curve constant `d`. -/
def edwardsAdd2625 (dL : Limbs10) (P Q : Point2625) : Point2625 :=
  let m := mul2625
  let t  := m (m (m (m dL P.x) Q.x) P.y) Q.y
  let xn := add2625 (m P.x Q.y) (m P.y Q.x)
  let yn := add2625 (m P.y Q.y) (m P.x Q.x)
  let rx := m xn (inv2625 (add2625 one2625 t))
  let ry := m yn (inv2625 (sub2625 one2625 t))
  { x := rx, y := ry }

/-- **The vectorized packed Edwards point-add decodes to `ed25519AffineAdd`**,
    for a limb vector `dL` decoding to `ed25519D`. -/
theorem edwardsAdd2625_decode (dL : Limbs10) (hd : eval2625 dL = ed25519D)
    (P Q : Point2625) :
    (edwardsAdd2625 dL P Q).toAlg = ed25519AffineAdd P.toAlg Q.toAlg := by
  unfold edwardsAdd2625 Point2625.toAlg ed25519AffineAdd
    ed25519AffineRx ed25519AffineRy ed25519AddXNum ed25519AddYNum ed25519AddT
  refine Ed25519Point.mk.injEq .. ▸ ⟨?_, ?_⟩ <;>
    simp only [mul2625_decode, add2625_decode, sub2625_decode, inv2625_decode,
      one2625_decode, hd]

/-- The vectorized point-double is the unified addition at `P = Q`. -/
def edwardsDouble2625 (dL : Limbs10) (P : Point2625) : Point2625 :=
  edwardsAdd2625 dL P P

/-- **The vectorized packed point-double decodes to `ed25519Double`.** -/
theorem edwardsDouble2625_decode (dL : Limbs10) (hd : eval2625 dL = ed25519D)
    (P : Point2625) :
    (edwardsDouble2625 dL P).toAlg = ed25519Double P.toAlg := by
  unfold edwardsDouble2625 ed25519Double
  exact edwardsAdd2625_decode dL hd P P

/-! ## 8. The packed field op alphabet and data independence

`PackedFieldOp` names lane intrinsics. Five are data-independent lane ops; two
are data-dependent: a conditional branch on a lane value and a memory load
indexed by a lane value. `dataIndep` is `false` exactly on the data-dependent
forms. -/

/-- The packed field op alphabet. -/
inductive PackedFieldOp where
  /-- `VPMULUDQ` — 32×32→64 lane product. -/
  | vpmuludq
  /-- `VPADD` — lane add. -/
  | vpadd
  /-- `VPSUB` — lane subtract. -/
  | vpsub
  /-- `VPSRL` — lane logical shift-right (carry/reduce). -/
  | vpsrl
  /-- `VPAND` — lane mask (limb mask in the reduce). -/
  | vpand
  /-- A conditional branch on a lane value (`VPTEST` + `Jcc`). -/
  | jccLane
  /-- A memory load indexed by a lane value (`VPGATHER`). -/
  | gatherLane
  deriving DecidableEq, Repr

/-- `op.dataIndep` is `false` for the ops whose control flow or memory address
    depends on a lane value (`jccLane`, `gatherLane`), and `true` otherwise. -/
def PackedFieldOp.dataIndep : PackedFieldOp → Bool
  | .jccLane => false
  | .gatherLane => false
  | _ => true

/-- A conditional branch on a lane value is not data-independent. -/
theorem jccLane_not_dataIndep : PackedFieldOp.jccLane.dataIndep = false := rfl

/-- A lane-indexed memory load is not data-independent. -/
theorem gatherLane_not_dataIndep : PackedFieldOp.gatherLane.dataIndep = false := rfl

/-- A fixed list of lane-intrinsic names for one packed field multiply + x19
    reduce. The list is not derived from `mul2625` or from emitted code. -/
def mulReduceOps : List PackedFieldOp :=
  [.vpmuludq, .vpmuludq, .vpmuludq, .vpmuludq, .vpmuludq,  -- the convolution products
   .vpadd, .vpadd, .vpadd, .vpadd,                          -- accumulate degrees
   .vpsrl, .vpand, .vpadd,                                  -- carry/reduce
   .vpmuludq, .vpadd]                                       -- x19 fold

/-- `mulReduceOps` contains no data-dependent branch and no lane-indexed load:
    every op in it has `dataIndep = true`. -/
theorem ct_data_indep : ∀ op ∈ mulReduceOps, op.dataIndep = true := by decide

/-! ## 9. Summary

* `eval2625_reduce19` — the integer-limb x19 fold preserves the `Fp25519` value.
* `evalN_prod19`, `prodEval_eq_mul` — the schoolbook product decodes to the field
  product.
* `mul2625_decode` / `sqr2625_decode` / `mul2625x4_decode` — `reduce19 ∘ prod19`
  decodes to the field product.
* `pow2625_decode` / `inv2625_decode` — exponentiation and Fermat inverse.
* `field4way_lane_map` — lane-wise application equals `laneMap`.
* `lmuludq_toNat`, `ristretto_ops_lower_correct` — the `VPMULUDQ` lane product is
  exact; dialect lowering of add / `VPMULUDQ` / shift at four `BitVec 64` lanes.
* `edwardsAdd2625_decode` / `edwardsDouble2625_decode` — the point add/double
  decode to `ed25519AffineAdd` / `ed25519Double` given the decode of `dL`.
* `ct_data_indep` — `mulReduceOps` has no data-dependent op.
-/

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.RistrettoFieldVec
