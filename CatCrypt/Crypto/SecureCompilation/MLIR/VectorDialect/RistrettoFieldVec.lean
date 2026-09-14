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
# SIMD Ristretto / Curve25519 4-way packed field through the VectorDialect (task #461)

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
modelled.

* `two_pow_high` — `(2 : Fp25519)^(255 + e) = 19 · 2^e`, so a term at bit
  position `255 + e` folds to `19 · 2^e`.
* `eval2625_reduce19` — the concrete fold `reduce19`, which adds `19 · limb`
  of the nine high limbs (10..18) of a nineteen-limb product to the low limbs,
  preserves the `Fp25519` value.
* `prodEval_eq_mul` — the unreduced double-sum product decode equals
  `eval2625 a * eval2625 b`.
* `mul2625_decode` / `sqr2625_decode` / `mul2625x4_decode` — for any reduction
  `red` satisfying the hypothesis `ReducesTo red` (its limbs decode to the
  unreduced product value), `mul2625 red` decodes to the field product. No
  theorem here shows that a concrete limb-level reduce satisfies `ReducesTo`;
  in particular `reduce19` is not connected to it.

## Lane-parallel structure (reuse, structural)

The four field elements ride the four AVX2 lanes; applying any per-lane field op
in parallel equals running it on each lane sequentially — `laneMap_eq_scalarMap`
at `α = the 10-limb field element`, `L = 4` (`field4way_lane_map`). This is the
same structural step the ChaCha / Keccak / NTT 4-way emits use.

## Edwards point arithmetic

`edwardsAdd2625_decode` shows that the affine twisted-Edwards point-add built from
`mul2625` / `add2625` / `sub2625` decodes to `ed25519AffineAdd` over `Fp25519`,
under the hypotheses `ReducesTo red`, decodes of the constants `1` and `d`, and a
packed inverse `inv` that decodes to the field inverse. The double
(`edwardsDouble2625_decode`) is `P + P`, reusing the add.

## Scope

* **In Lean**: the statements listed above, the lane-map equality
  `field4way_lane_map`, and the dialect-op lowering equalities
  `ristretto_ops_lower_correct` at the `2625x4` lane shape (`BitVec 32` lanes).
  Primality of `p` comes from the theorem `p25519_prime`.
* **Not in Lean**: the emitted limb shuffle, value checks of emitted code on
  concrete vectors, and timing; none of these are part of this package.

## Constant-time

The intended packed field uses `VPMULUDQ` / `VPADD` / `VPSRL` / `VPAND` over
fixed lanes, with no data-dependent branch or memory index, and a branch-free
masked select for the final canonical subtract. No theorem in this module states
a constant-time property: `ct_data_indep` holds by definition, because
`PackedFieldOp.dataIndep` returns `true` for every op.
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

/-! ## 2. The x19 Solinas wrap — the algebraic heart of the radix change

In `Fp25519 = ZMod (2^255 − 19)` we have `(2 : Fp25519) ^ 255 = 19`, because
`2^255 − 19 ≡ 0`. Hence a limb at weight `255 + e` reduces to `19 · 2^e` times
its value — the wrap the in-lane reduce performs. -/

/-- **The `2^255 = 19` identity in `Fp25519`.** This is what makes the `2^255−19`
    Solinas reduction a field identity: the top wrap multiplies by `19`. -/
theorem two_pow_255 : (2 : Fp25519) ^ 255 = 19 := by
  -- `P25519 = 2^255 - 19` (definitionally), and `(P25519 : Fp) = 0`.
  have hp : ((2 ^ 255 - 19 : Nat) : Fp25519) = 0 := ZMod.natCast_self P25519
  have h19le : 19 ≤ 2 ^ 255 := by norm_num
  rw [Nat.cast_sub h19le, Nat.cast_pow] at hp
  -- `hp : (2 : Fp)^255 - ((19 : Nat) : Fp) = 0`.
  have : (2 : Fp25519) ^ 255 = ((19 : Nat) : Fp25519) := sub_eq_zero.mp hp
  rw [this]; norm_num

/-- **The wrap identity at an arbitrary offset.** A limb value `v` at weight
    `255 + e` decodes to `19 · v · 2^e` — i.e. `2^(255+e) = 19 · 2^e`. -/
theorem two_pow_high (e : Nat) : (2 : Fp25519) ^ (255 + e) = 19 * (2 : Fp25519) ^ e := by
  rw [pow_add, two_pow_255]

/-! ## 3. Folding the high limbs of a product into the low ten

A nineteen-limb product `p` splits into low ten (`fun i => p i`, degrees `0..9`)
and high nine (degrees `10..18`). The reduce produces ten limbs
`reduce19 p i = p_low i + 19 · p_high i` where `p_high i = p (10 + i)` for
`i < 9` and `0` for `i = 9`. We prove the decode is preserved. -/

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
  -- Expand both `Fin`-sums (fixed small sizes) via `Fin.sum_univ_succ`.
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  -- Resolve the `if (i:Nat) < 9` decisions and the `Fin.val`/cast plumbing.
  norm_num [Fin.val_succ, Fin.val_zero]
  -- Replace every weight by its literal; rewrite the high weights via the wrap.
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

/-! ## 4. The packed schoolbook multiply (bit-position double sum)

The packed `VPMULUDQ`s form, for each limb-index pair `(i, j)`, the lane product
`a_i · b_j`; in the field this lands at bit position `weight i + weight j`. The
*unreduced product decode* is therefore the double sum
`Σ_{i,j} a_i b_j · 2^(weight i + weight j)`, which equals the field product
`eval a · eval b` directly by `Finset.sum_mul_sum` (no false per-degree weight
additivity is assumed — each lane product carries its own bit position). The
reduce then folds every bit position `≥ 255` by the `2^255 = 19` wrap.

We define `mul2625` abstractly via a reduction `red` that receives the
bit-position decode `prodEval` itself, and prove its decode from the product
identity and the hypothesis `ReducesTo red`. The concrete limb shuffle of the
emitted reduce is not defined in this module. -/

/-- The unreduced product decode: `Σ_{i,j} a_i b_j · 2^(weight i + weight j)`.
    This is the true bit-position-correct decode of the packed `VPMULUDQ`
    products — NOT a per-degree convolution at a single weight (the `26/25`
    radix is not index-additive). -/
def prodEval (a b : Limbs10) : Fp25519 :=
  ∑ i : Fin 10, ∑ j : Fin 10,
    ((a i * b j : ℤ) : Fp25519) * (2 : Fp25519) ^ (weight i + weight j)

/-- **The unreduced product decode IS the field product.** Direct from
    `Finset.sum_mul_sum`: the weighted decode is polynomial evaluation at `2`,
    so the product of the two decodes is the double sum with each lane product
    `a_i b_j` at bit position `weight i + weight j`. No false weight additivity. -/
theorem prodEval_eq_mul (a b : Limbs10) :
    prodEval a b = eval2625 a * eval2625 b := by
  unfold prodEval eval2625 evalN
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  push_cast
  rw [pow_add]
  ring

/-- A reduction realizer: `red prodEval a b` is ten limbs whose decode equals the
    unreduced decode `prodEval a b`. Because `red` receives the field-valued
    function `prodEval`, the property can be met without any limb arithmetic;
    no theorem here shows that a limb-level Solinas fold satisfies it. -/
def ReducesTo (red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10) : Prop :=
  ∀ a b, eval2625 (red prodEval a b) = prodEval a b

/-- The packed field multiply, parametric in the reduction `red` applied to the
    bit-position product decode. -/
def mul2625 (red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10)
    (a b : Limbs10) : Limbs10 := red prodEval a b

/-- **Decode of the packed multiply.** For any `red` with `ReducesTo red`,
    `mul2625 red a b` decodes to `eval2625 a * eval2625 b`. The proof rewrites
    with the hypothesis `ReducesTo red` and then `prodEval_eq_mul`; the
    reduction's value preservation is assumed, not proved. -/
theorem mul2625_decode
    {red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10}
    (hred : ReducesTo red) (a b : Limbs10) :
    eval2625 (mul2625 red a b) = eval2625 a * eval2625 b := by
  unfold mul2625
  rw [hred a b, prodEval_eq_mul]

/-- The squaring specialization: `eval (a²) = (eval a)²`. -/
theorem sqr2625_decode
    {red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10}
    (hred : ReducesTo red) (a : Limbs10) :
    eval2625 (mul2625 red a a) = eval2625 a ^ 2 := by
  rw [mul2625_decode hred, sq]

/-! ## 5. Lane-parallel structure: four field elements, one op (reuse)

The `2625x4` layout runs the SAME field op on each of the four AVX2 lanes. By
`laneMap_eq_scalarMap` at `α = Limbs10`, `L = 4`, applying any per-lane field
function in parallel equals running it sequentially per lane — the structural
step every 4-way SIMD emit uses (ChaCha, Keccak, NTT). -/

/-- A `2625x4` packed value: four ten-limb field elements (one per AVX2 lane). -/
abbrev Fe2625x4 : Type := Fin 4 → Limbs10

/-- **The Ristretto 4-way lane-map equality** (corollary of
    `laneMap_eq_scalarMap`). For any per-lane field function
    `f : Limbs10 → Limbs10`, applying it to each of the four packed lanes in
    parallel equals running it sequentially per lane. The packed field op's
    denotation-preservation theorem instantiates this at `f` = the packed
    mul/sqr/reduce. -/
theorem field4way_lane_map (f : Limbs10 → Limbs10) (v : Fe2625x4) :
    laneMap f v = (fun i => f (v i)) :=
  laneMap_eq_scalarMap f v

/-- The 4-way packed multiply: lane-wise `mul2625` of two packed values
    against a shared multiplier vector (the inter-point batching flavor — four
    independent field multiplies in the four lanes). -/
def mul2625x4 (red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10)
    (a b : Fe2625x4) : Fe2625x4 := fun i => mul2625 red (a i) (b i)

/-- **The 4-way packed multiply decodes lane-wise to the field product.** Each
    of the four lanes independently realizes `mul2625_decode`. This is the
    denotation-preservation for the inter-point (four-buckets-in-lanes) flavor
    that composes with the #452 Straus MSM. -/
theorem mul2625x4_decode
    {red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10}
    (hred : ReducesTo red) (a b : Fe2625x4) (i : Fin 4) :
    eval2625 (mul2625x4 red a b i) = eval2625 (a i) * eval2625 (b i) := by
  unfold mul2625x4
  exact mul2625_decode hred (a i) (b i)

/-! ## 6. The packed field ops as dialect `mul` / `add` / `shiftR`

The limb adds (`VPADD`), the lane multiply and the carry/reduce shifts (`VPSRL`)
are the dialect `add` / `mul` / `shiftR` ops at `BitVec 32` lanes, 8 lanes per
`__m256i`. The theorems below state the dialect denotation and lowering of these
ops at that shape. The lane multiply `lmul` is the wrapping 32-bit product; the
64-bit result of `VPMULUDQ` is not modelled, and no theorem connects these
`BitVec 32` lanes to the integer limbs of §§1–5. -/

/-- The `2625` lane element on the AVX2 wire: a `BitVec 32` limb. -/
abbrev limbLaneN : Nat := 8

/-- The `BitVec 32` lane add (`VPADDD`). -/
abbrev ladd (x y : BitVec 32) : BitVec 32 := x + y
/-- The `BitVec 32` lane multiply: the low 32 bits of the product (the 64-bit
    `VPMULUDQ` result is not modelled). -/
abbrev lmul (x y : BitVec 32) : BitVec 32 := x * y
/-- The `BitVec 32` lane logical shift-right (`VPSRLD` — the carry/reduce shift). -/
abbrev lshr (x : BitVec 32) (m : Nat) : BitVec 32 := x >>> m

/-- The packed limb-add denotes the dialect `add` op pointwise (`VPADDD`). -/
theorem limbAdd_denote (v w : VectorTy (BitVec 32) limbLaneN) :
    denoteVectorOp (.add ladd v w : VectorOp (BitVec 32) limbLaneN)
      = .vec (fun i => v i + w i) := rfl

/-- The 32-bit lane multiply denotes the dialect `mul` op pointwise. -/
theorem limbMul_denote (v w : VectorTy (BitVec 32) limbLaneN) :
    denoteVectorOp (.mul lmul v w : VectorOp (BitVec 32) limbLaneN)
      = .vec (fun i => v i * w i) := rfl

/-- The in-lane carry/reduce right-shift denotes the dialect `shiftR` op
    (`VPSRLD` — the `>>> 26` / `>>> 25` of the carry propagation). -/
theorem limbShr_denote (m : Nat) (v : VectorTy (BitVec 32) limbLaneN) :
    denoteVectorOp (.shiftR lshr m v : VectorOp (BitVec 32) limbLaneN)
      = .vec (fun i => v i >>> m) := rfl

/-- The three limb ops lower to per-lane scalar expansions with the stated
    denotation at the `2625x4` lane shape: `lower_add_correct`,
    `lower_mul_correct` and `lower_shiftR_correct` instantiated at `BitVec 32`,
    8 lanes. -/
theorem ristretto_ops_lower_correct (v w : VectorTy (BitVec 32) limbLaneN) (m : Nat) :
    (lower (0 : BitVec 32) (.add ladd v w)).map (·.denote)
        = some (VectorTy.map₂ ladd v w)
      ∧ (lower (0 : BitVec 32) (.mul lmul v w)).map (·.denote)
        = some (VectorTy.map₂ lmul v w)
      ∧ (lower (0 : BitVec 32) (.shiftR lshr m v)).map (·.denote)
        = some (VectorTy.map₁imm lshr m v) :=
  ⟨ lower_add_correct (0 : BitVec 32) ladd v w
  , lower_mul_correct (0 : BitVec 32) lmul v w
  , lower_shiftR_correct (0 : BitVec 32) lshr m v ⟩

/-! ## 7. Vectorized Edwards point-add over the packed field

dalek's vectorized Hisil–Wong–Carter–Dawson formula maps the four coordinate
operations of one extended-twisted-Edwards point onto the four AVX2 lanes. We
model the *affine* complete addition law (RFC 8032 §5.1, `a = −1`) over the
packed field, decoding each coordinate through `eval2625`, and show it equals
`ed25519AffineAdd` over `Fp25519` — the intra-point 4-lane flavor (four coords
of one point, which speeds a single scalar-mult / MSM term and Ed25519 verify).

Every coordinate multiply is `mul2625 red` (decoded under `ReducesTo red`); the
adds / subtracts are the limb-wise `add` op decoded by linearity of `evalN`. -/

/-- Limb-wise add of two ten-limb elements (`VPADD`); decodes additively. -/
def add2625 (a b : Limbs10) : Limbs10 := fun i => a i + b i

/-- Limb-wise subtract (`VPSUB`); decodes by `eval(a) − eval(b)`. -/
def sub2625 (a b : Limbs10) : Limbs10 := fun i => a i - b i

/-- The limb-wise add decodes to the field sum (linearity of the weighted
    decode). -/
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
    packed field elements (the intra-point layout has these in lanes). -/
structure Point2625 where
  /-- Affine `x`-coordinate limbs. -/
  x : Limbs10
  /-- Affine `y`-coordinate limbs. -/
  y : Limbs10

/-- Decode a packed point to the abstract `Ed25519Point`. -/
def Point2625.toAlg (P : Point2625) : Ed25519Point :=
  { x := eval2625 P.x, y := eval2625 P.y }

/-- The vectorized affine point-add over the packed field. Each coordinate
    numerator / the common product `t` / the two `1 ± t` factors are built from
    `mul2625` / `add2625` / `sub2625`; the two field inverses of the `1 ± t`
    denominators use a parameter `inv`, whose decode to the field inverse is a
    hypothesis of `edwardsAdd2625_decode`. -/
def edwardsAdd2625 (red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10)
    (inv : Limbs10 → Limbs10) (oneL dL : Limbs10) (P Q : Point2625) :
    Point2625 :=
  let m := mul2625 red
  let t  := m (m (m (m dL P.x) Q.x) P.y) Q.y
  let xn := add2625 (m P.x Q.y) (m P.y Q.x)
  let yn := add2625 (m P.y Q.y) (m P.x Q.x)
  let rx := m xn (inv (add2625 oneL t))
  let ry := m yn (inv (sub2625 oneL t))
  { x := rx, y := ry }

/-- **The vectorized packed Edwards point-add decodes to `ed25519AffineAdd`.**

    Using `mul2625_decode`, `add2625_decode` and `sub2625_decode`, the point-add
    decodes coordinate-wise to the twisted-Edwards addition over `Fp25519`. The
    hypotheses are `ReducesTo red`, the decodes of the constants `oneL`/`dL`, and
    `hinv : ∀ a, eval2625 (inv a) = (eval2625 a)⁻¹`. -/
theorem edwardsAdd2625_decode
    {red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10}
    (hred : ReducesTo red) (inv : Limbs10 → Limbs10) (oneL dL : Limbs10)
    (hone : eval2625 oneL = 1) (hd : eval2625 dL = ed25519D)
    (hinv : ∀ a, eval2625 (inv a) = (eval2625 a)⁻¹)
    (P Q : Point2625) :
    (edwardsAdd2625 red inv oneL dL P Q).toAlg
      = ed25519AffineAdd P.toAlg Q.toAlg := by
  unfold edwardsAdd2625 Point2625.toAlg ed25519AffineAdd
    ed25519AffineRx ed25519AffineRy ed25519AddXNum ed25519AddYNum ed25519AddT
  refine Ed25519Point.mk.injEq .. ▸ ⟨?_, ?_⟩ <;>
    simp only [mul2625_decode hred, add2625_decode, sub2625_decode, hinv, hone, hd]

/-- The vectorized point-DOUBLE is the unified addition at `P = Q` (twisted
    Edwards is complete; `[2]P = P + P`), reusing `edwardsAdd2625`. -/
def edwardsDouble2625 (red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10)
    (inv : Limbs10 → Limbs10) (oneL dL : Limbs10) (P : Point2625) :
    Point2625 := edwardsAdd2625 red inv oneL dL P P

/-- **The vectorized packed point-double decodes to `ed25519Double`.** -/
theorem edwardsDouble2625_decode
    {red : (Limbs10 → Limbs10 → Fp25519) → Limbs10 → Limbs10 → Limbs10}
    (hred : ReducesTo red) (inv : Limbs10 → Limbs10) (oneL dL : Limbs10)
    (hone : eval2625 oneL = 1) (hd : eval2625 dL = ed25519D)
    (hinv : ∀ a, eval2625 (inv a) = (eval2625 a)⁻¹)
    (P : Point2625) :
    (edwardsDouble2625 red inv oneL dL P).toAlg = ed25519Double P.toAlg := by
  unfold edwardsDouble2625 ed25519Double
  exact edwardsAdd2625_decode hred inv oneL dL hone hd hinv P P

/-! ## 8. The packed field op alphabet

The intended packed field ops are lane-parallel intrinsics
(`VPMULUDQ`/`VPADD`/`VPSUB`/`VPSRL`/`VPAND`) over fixed lane indices. This section
records the op alphabet and an op list. It has no semantics for the ops and no
leakage model, so it states no constant-time property. -/

/-- The packed field op alphabet (names of lane intrinsics). -/
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
  deriving DecidableEq, Repr

/-- A Boolean label on ops, defined as the constant function `true`. It is not
    derived from any semantics of the op. -/
def PackedFieldOp.dataIndep : PackedFieldOp → Bool := fun _ => true

/-- A fixed list of lane-intrinsic names for one packed field multiply + x19
    reduce. The list is not connected to `mul2625` or to any emitted code. -/
def mulReduceOps : List PackedFieldOp :=
  [.vpmuludq, .vpmuludq, .vpmuludq, .vpmuludq, .vpmuludq,  -- the convolution products
   .vpadd, .vpadd, .vpadd, .vpadd,                          -- accumulate degrees
   .vpsrl, .vpand, .vpadd,                                  -- carry/reduce
   .vpmuludq, .vpadd]                                       -- x19 fold

/-- Every op in `mulReduceOps` has `dataIndep = true`. The statement holds for any
    list, since `PackedFieldOp.dataIndep` is constantly `true`; it carries no
    constant-time content. -/
theorem ct_data_indep : ∀ op ∈ mulReduceOps, op.dataIndep = true := by
  intro op _; rfl

/-! ## 9. Summary

* `eval2625_reduce19` — the integer-limb x19 fold preserves the `Fp25519` value.
* `prodEval_eq_mul` — the double-sum product decode is the field product.
* `mul2625_decode` / `sqr2625_decode` / `mul2625x4_decode` — the parametric packed
  multiply decodes to the field product under the hypothesis `ReducesTo red`.
* `field4way_lane_map` — lane-wise application equals `laneMap`
  (`laneMap_eq_scalarMap`).
* `ristretto_ops_lower_correct` — dialect lowering of add / 32-bit mul / shift at
  `BitVec 32`, 8 lanes.
* `edwardsAdd2625_decode` / `edwardsDouble2625_decode` — the point add/double
  decode to `ed25519AffineAdd` / `ed25519Double` under `ReducesTo red`, the
  constant decodes and the inverse hypothesis.
* `ct_data_indep` — holds by definition of `dataIndep`; no constant-time content.
-/

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.RistrettoFieldVec
