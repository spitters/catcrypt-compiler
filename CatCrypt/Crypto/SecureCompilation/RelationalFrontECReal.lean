/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontEC
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBN254

/-!
# The EC doubling-slope numerator `E = 3·A` over a 256-bit curve prime

`RelationalFrontEC` realizes the `a = 0` Jacobian doubling-slope numerator
`E = 3·A` over `ZMod 251` with a single-word `BitVec 64` carrier. This module
carries the same relational structure — an injective, not-onto encoding, the
commuting square, and the transfer corollary — over a **4×64-bit limb carrier** at
the BN254 base-field prime.

## The carrier and the curve

The abstract field is `ZMod bn254Q` for the 254-bit BN254 base prime
(`RelationalFrontBN254`), laid out over `k = 4` 64-bit limbs. BN254 is
`y² = x³ + 3`, i.e. `a = 0`, so the tangent slope
(`EllipticCurveDialect.ECParams.tangentSlope`) is `(3·x² + 0)·(2y)⁻¹` and its
inversion-free numerator is exactly `E = 3·A` with `A = x²`.

`2·bn254Q < (2^64)^4`, which is what lets the modular add's no-overflow side
condition hold at four limbs; a full 256-bit prime (secp256k1) needs `k = 5` for
the same kernel (`RelationalFrontSecp256k1`, §"The limb-count subtlety").

## The realized operation

* **Field**: `ZMod bn254Q`, serialized by `encMLK bn254Q 4` — the canonical
  representative split into four little-endian limbs, injective
  (`encMLK_injective`) and not onto (`bn254_encMLK_not_surjective`).
* **EC sub-step**: `A ↦ 3·A`, the `a = 0` Jacobian doubling-slope numerator.
* **Kernel**: `mlTripleModK`, the composition of two `mlAddModK` steps — each a
  carry-extended `addLimbs` followed by the `condSubLimbs` modular reduce. Two
  reduces are needed because `3·A` can be up to `3·(q−1)`. This mirrors the
  GF(251) `tripleMod251SSA` schedule (field double + condsub, field add +
  condsub) at four limbs.

## The multiply's `ZMod`-level commuting square

`RelationalFrontEC` records that the multiply's `ZMod`-level square was not
available for its GF(251) golden-path kernel. At multi-limb width it is
`RelationalFrontBN254.bn254_mul_commutes` — the abstract `ZMod bn254Q` product,
serialized by the same encoding, read off the emitted 8-limb Barrett-reducing
kernel. `bn254_tripleOfSquare_commutes` composes it with the tripling square to
give the whole inversion-free numerator `E = 3·X²` as one commuting square.

## The record

`RealizedUnaryKernel` carries a `Com jasminDialect [.reg 64] (.reg 64)`, a
single-word program, so it does not instantiate at four limbs.
`RealizedLimbUnaryKernel` is its multi-limb counterpart: the same
`EndoUnaryRealization` tie over a limb-vector carrier, with the single-word
`Com`-denotation seam replaced by the limb-width obligation on the kernel. The
`EndoUnaryRealization` structure itself is reused verbatim — it is parametric in
the carrier.

## Main results

* `splitLimbsK_bignumVal`: limb normal form, lifting a value-level kernel law to
  an equality of limb vectors.
* `mlTripleModK`, `encMLK_triple_commutes`: the tripling kernel and its
  `KLimbPrime`-generic commuting square.
* `bn254_triple_commutes`, `bn254_triple_spec_transfers`: the square and the
  transfer corollary at the BN254 base field.
* `bn254_tripleOfSquare_commutes`: the composite `E = 3·X²` with both squares.
* `bn254_encMLK_not_surjective`: the encoding is injective, not onto.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-! ## 0. Limb normal form and kernel widths

A `k`-limb vector is the `splitLimbsK` normal form of its own `bignumVal`, so two
`k`-limb vectors with equal `bignumVal` are equal. This is what promotes the
value-level kernel correctness of `RelationalFrontBls377Add` to an equality of
limb vectors, which is the shape the `EndoUnaryRealization` commuting square
takes over a limb carrier. -/

/-- **Limb normal form.** A limb vector is the `splitLimbsK` split of its own
    `bignumVal` at its own length. -/
theorem splitLimbsK_bignumVal :
    ∀ l : List (BitVec 64), splitLimbsK l.length (bignumVal l) = l
  | [] => rfl
  | w :: ws => by
      have hw : w.toNat < 2 ^ 64 := w.isLt
      have hmod : (w.toNat + 2 ^ 64 * bignumVal ws) % 2 ^ 64 = w.toNat := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]
      have hdiv : (w.toNat + 2 ^ 64 * bignumVal ws) / 2 ^ 64 = bignumVal ws := by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hw, Nat.zero_add]
      have hw' : BitVec.ofNat 64 w.toNat = w := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
      simp only [bignumVal, List.length_cons, splitLimbsK, hmod, hdiv, hw', splitLimbsK_bignumVal ws]

/-- Two limb vectors of the same length with the same `bignumVal` are equal. -/
theorem bignumVal_inj_of_length_eq (u v : List (BitVec 64))
    (hlen : u.length = v.length) (hval : bignumVal u = bignumVal v) : u = v := by
  rw [← splitLimbsK_bignumVal u, ← splitLimbsK_bignumVal v, hlen, hval]

/-- The branchless per-limb select preserves the operand length. -/
theorem selLimbs_length (m : BitVec 64) :
    ∀ a b : List (BitVec 64), a.length = b.length →
      (selLimbs m a b).length = a.length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [selLimbs, List.length_cons]
      rw [selLimbs_length m xs ys (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The multi-limb conditional subtract preserves the operand length. -/
theorem condSubLimbs_length (x p : List (BitVec 64)) (hlen : x.length = p.length) :
    (condSubLimbs x p).length = x.length := by
  have hnl : x.length = (notLimbs p).length := by
    simp only [notLimbs, List.length_map]; exact hlen
  have hdlen : (subLimbs x p).length = x.length + 1 := by
    simpa [subLimbs] using addLimbs_length x (notLimbs p) 1 hnl
  have hdrop : ((subLimbs x p).dropLast).length = x.length := by
    rw [List.length_dropLast, hdlen]; omega
  simp only [condSubLimbs]
  rw [selLimbs_length _ _ _ (by rw [hdrop]), hdrop]

/-- The `k`-limb modular add returns a `k`-limb vector. -/
theorem mlAddModK_length (k : Nat) (pl x y : List (BitVec 64))
    (hxl : x.length = k) (hyl : y.length = k) (hpl : pl.length = k) :
    (mlAddModK pl x y).length = k := by
  have hxy : x.length = y.length := by rw [hxl, hyl]
  have hlen1 : (addLimbs x y 0).length = k + 1 := by
    rw [addLimbs_length x y 0 hxy, hxl]
  have hdrop : ((addLimbs x y 0).dropLast).length = k := by
    rw [List.length_dropLast, hlen1]; omega
  simp only [mlAddModK]
  rw [condSubLimbs_length _ _ (by rw [hdrop, hpl]), hdrop]

/-! ## 1. The transfer corollary at the level of the realization

`RealizedUnaryKernel.spec_eq_transfers_to_emit` uses only the three
`EndoUnaryRealization` fields, so the same statement holds for any carrier. -/

/-- **The relational-front transfer corollary.** An abstract source equation
    `op a = op a'` holds exactly when the carrier operator agrees on the encoded
    operands. The carrier-generic form of
    `RealizedUnaryKernel.spec_eq_transfers_to_emit`. -/
theorem EndoUnaryRealization.spec_eq_transfers {A α : Type} {op : A → A} {bop : α → α}
    (R : EndoUnaryRealization op bop) (a a' : A) :
    op a = op a' ↔ bop (R.enc a) = bop (R.enc a') := by
  rw [← R.commutes, ← R.commutes]
  exact ⟨fun h => by rw [h], fun h => R.enc_inj h⟩

/-! ## 2. The `k`-limb tripling kernel

`mlTripleModK` is two `mlAddModK` steps: the field double `x + x`, then `+ x`.
Each step carries its own `condSubLimbs` reduce, which is what `3·A ≤ 3·(q−1)`
needs. -/

/-- The `k`-limb modular tripling kernel: the modular double `x + x` followed by a
    modular add of `x`, each an `addLimbs`/`condSubLimbs` step against the modulus
    limb vector `pl`. -/
def mlTripleModK (pl x : List (BitVec 64)) : List (BitVec 64) :=
  mlAddModK pl (mlAddModK pl x x) x

/-- The `k`-limb tripling kernel returns a `k`-limb vector. -/
theorem mlTripleModK_length (k : Nat) (pl x : List (BitVec 64))
    (hxl : x.length = k) (hpl : pl.length = k) :
    (mlTripleModK pl x).length = k := by
  have hinner : (mlAddModK pl x x).length = k := mlAddModK_length k pl x x hxl hxl hpl
  exact mlAddModK_length k pl _ x hinner hxl hpl

/-- **The multi-limb IR seam for the tripling kernel.** Run on the encoded
    operand and read through `bignumVal`, the two-step kernel computes the
    canonical representative of `3·a`. -/
theorem mlTriple_seamK (Q : KLimbPrime) (a : ZMod Q.q) :
    bignumVal (mlTripleModK Q.ql (encMLK Q.q Q.k a)) = (3 * a).val := by
  have hqk := Q.q_lt
  have hea : bignumVal (encMLK Q.q Q.k a) = a.val := bignumVal_encMLK Q.q Q.k hqk a
  have hva : a.val < Q.q := ZMod.val_lt a
  have hinner : bignumVal (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k a))
      = (a + a).val := (mlAdd_seamK Q a a).trans (ZMod.val_add a a).symm
  have hinnerlen : (mlAddModK Q.ql (encMLK Q.q Q.k a) (encMLK Q.q Q.k a)).length = Q.k :=
    mlAddModK_length Q.k Q.ql _ _ (encMLK_length _ _ _) (encMLK_length _ _ _) Q.ql_len
  simp only [mlTripleModK]
  rw [mlAddModK_val Q.k Q.ql _ _ hinnerlen (encMLK_length _ _ _) Q.ql_len
      (by rw [Q.ql_val]; exact Q.two_q_le)
      (by rw [hinner, Q.ql_val]; exact ZMod.val_lt _)
      (by rw [hea, Q.ql_val]; exact hva)]
  rw [hinner, hea, Q.ql_val, ← ZMod.val_add]
  congr 1
  ring

/-- **The `k`-limb tripling commuting square.** The abstract `3·a` in `ZMod q`,
    serialized by the injective-not-onto `k`-limb encoding `encMLK`, is the
    emitted two-step reducing kernel applied to the serialized operand — an
    equality of limb vectors, via `bignumVal_inj_of_length_eq`. -/
theorem encMLK_triple_commutes (Q : KLimbPrime) (a : ZMod Q.q) :
    encMLK Q.q Q.k (3 * a) = mlTripleModK Q.ql (encMLK Q.q Q.k a) := by
  refine bignumVal_inj_of_length_eq _ _ ?_ ?_
  · rw [encMLK_length, mlTripleModK_length Q.k Q.ql _ (encMLK_length _ _ _) Q.ql_len]
  · rw [bignumVal_encMLK Q.q Q.k Q.q_lt, mlTriple_seamK Q]

/-! ## 3. The multi-limb realized unary kernel -/

/-- A relationally-emitted unary kernel over a multi-limb carrier: an abstract
    unary field operation, its limb-vector realization, and the width obligation
    that the kernel maps `k`-limb vectors to `k`-limb vectors. The limb-carrier
    counterpart of `RealizedUnaryKernel`, whose `com`/`com_denotes_bop` fields are
    fixed at a single-word `Com`. -/
structure RealizedLimbUnaryKernel {A : Type} (op : A → A) where
  /-- The number of 64-bit limbs in the carrier. -/
  k : Nat
  /-- The limb-vector operator the abstract `op` is realized by. -/
  bop : List (BitVec 64) → List (BitVec 64)
  /-- The relational tie (encoding + injectivity + commuting square). -/
  realization : EndoUnaryRealization op bop
  /-- The kernel maps `k`-limb vectors to `k`-limb vectors. -/
  bop_length : ∀ l : List (BitVec 64), l.length = k → (bop l).length = k

namespace RealizedLimbUnaryKernel
variable {A : Type} {op : A → A}

/-- **The transfer-to-emit corollary over a multi-limb carrier.** An abstract
    source equation transfers to an equation between the emitted multi-limb
    kernel's outputs on the serialized operands. -/
theorem spec_eq_transfers_to_emit (R : RealizedLimbUnaryKernel op) (a a' : A) :
    op a = op a' ↔ R.bop (R.realization.enc a) = R.bop (R.realization.enc a') :=
  R.realization.spec_eq_transfers a a'

end RealizedLimbUnaryKernel

/-- **The `k`-limb realization of the EC doubling-slope numerator.** `op = (3 · ·)`
    on `ZMod q`; `bop = mlTripleModK Q.ql` on the `k`-limb carrier;
    `enc = encMLK Q.q Q.k` (injective, not onto). -/
def tripleRealizationK (Q : KLimbPrime) :
    EndoUnaryRealization (fun a : ZMod Q.q => 3 * a) (mlTripleModK Q.ql) where
  enc := encMLK Q.q Q.k
  enc_inj := encMLK_injective Q.q Q.k Q.q_lt
  commutes := encMLK_triple_commutes Q

/-- **The `k`-limb realized kernel for the EC doubling-slope numerator.** -/
def tripleLimbKernelK (Q : KLimbPrime) :
    RealizedLimbUnaryKernel (fun a : ZMod Q.q => 3 * a) where
  k := Q.k
  bop := mlTripleModK Q.ql
  realization := tripleRealizationK Q
  bop_length := fun l hl => mlTripleModK_length Q.k Q.ql l hl Q.ql_len

/-- **The `k`-limb transfer demonstration.** An abstract `ZMod q` doubling-slope
    numerator equation `3·a = 3·a'` holds exactly when the emitted multi-limb
    kernel agrees on the serialized operands. -/
theorem mlTripleK_spec_transfers (Q : KLimbPrime) (a a' : ZMod Q.q) :
    3 * a = 3 * a' ↔
      mlTripleModK Q.ql (encMLK Q.q Q.k a) = mlTripleModK Q.ql (encMLK Q.q Q.k a') :=
  (tripleRealizationK Q).spec_eq_transfers a a'

/-! ## 4. The BN254 instance: the doubling-slope numerator at a 256-bit curve prime -/

/-- **The BN254 tripling seam.** The two-step 4-limb reducing kernel, run on the
    serialized coordinate, computes the canonical representative of `3·A`. -/
theorem bn254_triple_seam (A : ZMod bn254Q) :
    bignumVal (mlTripleModK bn254Limbs (encMLK bn254Q 4 A)) = (3 * A).val :=
  mlTriple_seamK bn254KLimbPrime A

/-- **The BN254 doubling-slope-numerator commuting square.** The abstract
    `a = 0` Jacobian doubling-slope numerator `E = 3·A` in the BN254 base field,
    serialized by the injective-not-onto 4-limb encoding `encMLK bn254Q 4`, is the
    emitted two-step 4-limb reducing kernel on the serialized coordinate. The
    multi-limb sibling of `tripleMod251_commutes`. -/
theorem bn254_triple_commutes (A : ZMod bn254Q) :
    encMLK bn254Q 4 (3 * A) = mlTripleModK bn254Limbs (encMLK bn254Q 4 A) :=
  encMLK_triple_commutes bn254KLimbPrime A

/-- **The `EndoUnaryRealization` for the BN254 doubling-slope numerator.** -/
def bn254TripleRealization :
    EndoUnaryRealization (fun A : ZMod bn254Q => 3 * A) (mlTripleModK bn254Limbs) :=
  tripleRealizationK bn254KLimbPrime

/-- **The BN254 realized kernel for the doubling-slope numerator.** The 4-limb
    sibling of `tripleMod251RealizedKernel`. -/
def bn254TripleLimbKernel :
    RealizedLimbUnaryKernel (fun A : ZMod bn254Q => 3 * A) :=
  tripleLimbKernelK bn254KLimbPrime

/-- **The BN254 transfer demonstration.** Two Jacobian points whose
    `X`-coordinates give the same doubling-slope numerator `3·A = 3·A'` in the
    BN254 base field exactly when the emitted 4-limb kernel agrees on the
    serialized coordinates. `spec_eq_transfers_to_emit` at a 256-bit curve
    prime. -/
theorem bn254_triple_spec_transfers (A A' : ZMod bn254Q) :
    3 * A = 3 * A' ↔
      mlTripleModK bn254Limbs (encMLK bn254Q 4 A)
        = mlTripleModK bn254Limbs (encMLK bn254Q 4 A') :=
  bn254TripleLimbKernel.spec_eq_transfers_to_emit A A'

/-- **The encoding is not onto.** The modulus limb vector `bn254Limbs` has
    `bignumVal` equal to `bn254Q`, while every encoded residue has `bignumVal`
    below `bn254Q`, so `bn254Limbs` is outside the range of `encMLK bn254Q 4`. -/
theorem bn254_encMLK_not_surjective :
    ¬ Function.Surjective (encMLK bn254Q 4) := by
  intro hsurj
  obtain ⟨A, hA⟩ := hsurj bn254Limbs
  have hval : bignumVal (encMLK bn254Q 4 A) = A.val :=
    bignumVal_encMLK bn254Q 4 bn254KLimbPrime.q_lt A
  rw [hA, bignumVal_bn254Limbs] at hval
  have := ZMod.val_lt A
  omega

/-- **A wrapping instance.** For the maximal residue `A = −1` both reduction steps
    of the kernel fire (`3·(q−1) = 3q−3`), and the kernel's `bignumVal` is the
    canonical representative of `−3`. -/
theorem bn254_triple_wrap_example :
    bignumVal (mlTripleModK bn254Limbs (encMLK bn254Q 4 (-1)))
      = (-3 : ZMod bn254Q).val := by
  rw [bn254_triple_seam (-1)]
  congr 1

/-! ## 5. The abstract group-law step the kernel realizes

BN254 is `y² = x³ + 3`, an `a = 0` short-Weierstrass curve, so
`EllipticCurveDialect.ECParams.tangentSlope` has numerator `3·x² + 0 = 3·A` with
`A = x²`. -/

/-- BN254 as an `ECParams` over its base field: `y² = x³ + 3`, i.e. `a = 0`. -/
def bn254Curve : ECParams bn254Q := ⟨0, 3⟩

/-- **The realized kernel is the `a = 0` tangent-slope numerator.** For BN254 the
    tangent slope is `(3·X² + a)·(2Y)⁻¹` with `a = 0`, so its numerator is the
    unary op `A ↦ 3·A` at `A = X·X` that the realized kernel computes. -/
theorem bn254_tangentSlope_numerator_isTriple (X Y : ZMod bn254Q) :
    bn254Curve.tangentSlope X Y
      = (fun A : ZMod bn254Q => 3 * A) (X * X) * (2 * Y)⁻¹ := by
  simp only [ECParams.tangentSlope, bn254Curve, add_zero]

/-! ## 6. The composite numerator `E = 3·X²`

The multiply's `ZMod`-level commuting square at this width is
`bn254_mul_commutes` (the emitted 8-limb Barrett-reducing kernel). Composing it
with the tripling square gives the whole inversion-free doubling-slope numerator
as one commuting square between the abstract field and emitted multi-limb
kernels. -/

/-- **The composite doubling-slope numerator `E = 3·X²`.** The abstract BN254
    numerator, serialized by `encMLK bn254Q 4`, is the emitted 4-limb tripling
    kernel applied to the emitted 8-limb Barrett-reducing squaring kernel's output
    (re-limbed to the 4-limb operand width). Both commuting squares are
    `ZMod`-level: `bn254_mul_commutes` for the square, `bn254_triple_commutes` for
    the tripling. -/
theorem bn254_tripleOfSquare_commutes (X : ZMod bn254Q) :
    encMLK bn254Q 4 (3 * (X * X))
      = mlTripleModK bn254Limbs
          (splitLimbsK 4
            (bignumVal (mlMulMod 4 bn254MuLimbs bn254Limbs
              (encMLK bn254Q 4 X) (encMLK bn254Q 4 X)))) := by
  rw [← bn254_mul_commutes]
  exact bn254_triple_commutes (X * X)

/-- **The composite transfer demonstration.** Two `X`-coordinates give the same
    `a = 0` doubling-slope numerator `3·X² = 3·X'²` exactly when the emitted
    tripling kernel agrees on the emitted squaring kernel's re-limbed outputs. -/
theorem bn254_tripleOfSquare_spec_transfers (X X' : ZMod bn254Q) :
    3 * (X * X) = 3 * (X' * X') ↔
      mlTripleModK bn254Limbs
          (splitLimbsK 4 (bignumVal (mlMulMod 4 bn254MuLimbs bn254Limbs
            (encMLK bn254Q 4 X) (encMLK bn254Q 4 X))))
        = mlTripleModK bn254Limbs
          (splitLimbsK 4 (bignumVal (mlMulMod 4 bn254MuLimbs bn254Limbs
            (encMLK bn254Q 4 X') (encMLK bn254Q 4 X')))) := by
  rw [← bn254_mul_commutes, ← bn254_mul_commutes]
  exact bn254_triple_spec_transfers (X * X) (X' * X')

end CatCrypt.Crypto.SecureCompilation.RelationalFront
