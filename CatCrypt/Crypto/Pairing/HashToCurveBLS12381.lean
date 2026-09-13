/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.BLS12381Verified
public import CatCrypt.Crypto.Pairing.IsogenyPolyIdentity
public import Transfer.Examples.ZModPowMod
public meta import CatCrypt.Crypto.Util.BLS12381Verified
public meta import Transfer.Examples.ZModPowMod

/-!
# RFC 9380 hash-to-curve for BLS12-381 G1 — Lean port of the AUCurves Rocq spec

Lean 4 port of the AUCurves Rocq formalization
`AUCurves/src/Spec/HashToCurve*.v` (BLS12-381 G1, suite
`BLS12381G1_XMD:SHA-256_SSWU_RO_`). It ports:

* the **Simplified SWU** map `map_to_curve_simple_swu` (RFC 9380 §6.6.2) onto
  the isogenous curve `E' : y² = x³ + A'·x + B'`;
* the **11-isogeny** `iso_map : E' → E` (RFC 9380 Appendix E.2, projective form
  handling kernel points);
* `map_to_curve_g1 = iso_map ∘ swu`;
* affine `point_add` / `scalar_mul` on `E : y² = x³ + 4`, and
  **`clear_cofactor`** (RFC 9380 §8.8.1, `h_eff = 0xd201000000010001`);
* the full `hash_to_curve` / `encode_to_curve` pipeline (RFC 9380 §3).

Field: `FpBLS = ZMod p` (`CatCrypt.Util.BLS12381Verified`), a Mathlib `Field`
(primality of the 381-bit `p` is the theorem `bls12381_prime` there).

## Rocq correspondence

| Lean (this file) | Rocq (`Spec/HashToCurve*.v`) |
|---|---|
| `sgn0`, `isSquare`, `fpSqrt`, `curveRhs` | `HashToCurve.v` helpers |
| `mapToCurveSimpleSWU` | `map_to_curve_simple_swu` |
| `hornerEval`, `hornerEvalMonic`, `isoMap` | `horner_eval`, `iso_map` |
| `mapToCurveG1` | `map_to_curve_g1` |
| `pointAdd`, `scalarMul`, `clearCofactor` | `point_add`, `scalar_mul`, `clear_cofactor` |
| `hashToCurve`, `encodeToCurve` | `hash_to_curve`, `encode_to_curve` |
| `onCurveE`, `onCurveEprime` | `on_curve_E`, `on_curve_Eprime` |
| `swuMapsToEprime` | `swu_maps_to_Eprime_proof` (`HashToCurveSWUProof.v`) |
| `isoMapsEprimeToE` | `iso_map_on_curve` (`HashToCurveIsogenyProof.v`) |
| `mapProducesCurvePoints` | `map_produces_curve_points_proof` (`HashToCurveProof.v`) |
| `clearCofactorPreserves` | `clear_cofactor_preserves` (`HashToCurveClosureProof.v`) |
| `swuGxRatio` | `swu_gx_ratio` (`HashToCurveSWUProof.v`) |

## Scope

1. **On-curve, NOT prime-order-subgroup.** `mapProducesCurvePoints` and
   `clearCofactorPreserves` prove the output lies on the affine curve
   `E : y² = x³ + 4`. They do **not** prove membership in the prime-order
   subgroup `G1` of order `r`. Cofactor clearing (`clearCofactor`) is what
   *lands* points in the subgroup, but proving `[h_eff]P ∈ G1` requires the
   group-order / torsion structure — a follow-on, exactly as in the Rocq
   development (which likewise proves only on-curve closure).

2. **The hash is abstract.** `hashToField` (the SHA-256 XMD `expand_message`
   plus field reduction, RFC 9380 §5) is an **opaque input**: the pipeline is
   verified as a function of its output field elements `u₀, u₁`. The
   Rocq side imports `hash_to_field` from `Crypto.Spec.SHA256_axiom` likewise.

## Proof status

All theorems are proved without `sorry`. The symbolic parts mirror the Rocq
`field`/`fsatz`/`ring` proofs: `swuGxRatio` (the `gx₂ = t³·gx₁` field identity),
the constant-nonzero lemmas, `swuZ_nonsquare` (`Z = 11` is a nonresidue, by
`norm_num` on `jacobiSym 11 p` and `ZMod.euler_criterion`), `fpSqrt_correct`,
`swuMapsToEprime` (`swuGxRatio`, `swuZ_nonsquare`, multiplicativity of the Euler
symbol, `fpSqrt_correct`, and the edge lemma below), `pointAddPreserves` /
`scalarMulPreserves` / `clearCofactorPreserves`, and `mapProducesCurvePoints` as
the composition of `swuMapsToEprime` and `isoMapsEprimeToE`.

Two steps are computations over the 381-bit field, which Rocq discharges by
`vm_compute`/`native_compute`:
* `edge_case_gx1_is_square` (the `tv1 = 0` Legendre check that
  `curveRhs A' B' (B'·(Z·A')⁻¹)` is a square, a property of the concrete
  `(A', B', Z)` triple) evaluates one modular exponentiation over `Nat` by
  `native_decide`, so `swuMapsToEprime` and its consumers depend on
  `Lean.ofReduceBool`;
* `isogenyPolyIdentity` (used by `isoMapsEprimeToE`) is proved in
  `IsogenyPolyIdentity` by a bounded reflective coefficient check.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.HashToCurveBLS12381

open CatCrypt.Util (FpBLS BLS12381)

/-! ## §0  Field helpers -/

/-- A nonzero `Nat` below the BLS12-381 prime is nonzero in `FpBLS`
    (mirrors `HashToCurveFieldSetup.v`'s `vm_compute`-based nonzero lemmas). -/
theorem fp_nz (n : ℕ) (h0 : 0 < n) (hlt : n < BLS12381) : (n : FpBLS) ≠ 0 := by
  intro hz
  have hdvd : (BLS12381 : ℕ) ∣ n := (CharP.cast_eq_zero_iff FpBLS BLS12381 n).mp hz
  have := Nat.le_of_dvd h0 hdvd
  omega

/-! ## §1  RFC 9380 field-map helpers (`HashToCurve.v`)

`inv0` (the field inverse with `inv0 0 = 0`) is Mathlib's `⁻¹` on a field
(`inv_zero : (0 : FpBLS)⁻¹ = 0`), so no separate `inv0` is needed. -/

/-- `sgn0(x)` for GF(p), m = 1: the parity of the canonical representative
    (RFC 9380 §4.1). -/
def sgn0 (x : FpBLS) : ℕ := (ZMod.val x) % 2

/-- The Euler-criterion exponent `(p-1)/2`. -/
def legendreExp : ℕ := (BLS12381 - 1) / 2

/-- The square-root exponent `(p+1)/4` (valid since `p ≡ 3 mod 4`). -/
def sqrtExp : ℕ := (BLS12381 + 1) / 4

/-- `isSquare x`: quadratic-residuosity test via the Euler criterion
    `x^((p-1)/2) = 1`, with `0` counted as a square. -/
def isSquare (x : FpBLS) : Bool :=
  if x ^ legendreExp = 1 then true else if x = 0 then true else false

/-- Square root via `x^((p+1)/4)` (correct for `p ≡ 3 mod 4`). -/
def fpSqrt (x : FpBLS) : FpBLS := x ^ sqrtExp

/-- Curve RHS `x³ + a·x + b`. -/
def curveRhs (a b x : FpBLS) : FpBLS := x ^ 3 + a * x + b

/-! ## §2  Simplified SWU map (RFC 9380 §6.6.2) -/

/-- The Simplified SWU map for `y² = x³ + a·x + b` with SWU constant `z`
    (a nonsquare). Faithful transcription of `map_to_curve_simple_swu`. -/
def mapToCurveSimpleSWU (a b z u : FpBLS) : FpBLS × FpBLS :=
  let u2 := u ^ 2
  let u4 := u2 ^ 2
  let z2 := z ^ 2
  -- Step 1: tv1 = inv0(Z²·u⁴ + Z·u²)
  let tv1 := (z2 * u4 + z * u2)⁻¹
  -- Step 2: x1 = (-B/A)·(1 + tv1)
  let negBoverA := (-b) * a⁻¹
  let x1normal := negBoverA * (1 + tv1)
  -- Step 3: edge case tv1 = 0 ⇒ x1 = B/(Z·A)
  let x1 := if tv1 = 0 then b * (z * a)⁻¹ else x1normal
  -- Step 4: gx1
  let gx1 := curveRhs a b x1
  -- Step 5: x2 = Z·u²·x1
  let x2 := z * u2 * x1
  -- Step 6: gx2
  let gx2 := curveRhs a b x2
  -- Steps 7-8: pick the branch whose gx is a QR
  let xy := if isSquare gx1 then (x1, fpSqrt gx1) else (x2, fpSqrt gx2)
  let x := xy.1
  let y := xy.2
  -- Step 9: sign fix
  let yFinal := if sgn0 u = sgn0 y then y else -y
  (x, yFinal)

/-! ## §3–4  Isogeny map data + polynomial identity

The isogenous-curve constants (`isoA`, `isoB`, `swuZ`, `bls12B`), the four
rational-map coefficient lists (`isoXnum`/`isoXden`/`isoYnum`/`isoYden`), the
Horner evaluators (`hornerEval`/`hornerEvalMonic`), and the degree-63
`isogenyPolyIdentity` are imported from `IsogenyCoeffs` / `IsogenyPolyIdentity`
(RFC 9380 §8.8.1 / Appendix E.2). The identity is proved there by the bounded
reflective coefficient check, so it is verified on a light import closure. -/

/-- The 11-isogeny `φ : E'(x',y') → E`. Projective form: returns `(0,2) ∈ E`
    at kernel points (`xden·yden = 0`), the affine image otherwise. -/
def isoMap (pt : FpBLS × FpBLS) : FpBLS × FpBLS :=
  let x' := pt.1
  let y' := pt.2
  let xn := hornerEval isoXnum x'
  let xd := hornerEvalMonic isoXden x'
  let yn := hornerEval isoYnum x'
  let yd := hornerEvalMonic isoYden x'
  let z := xd * yd
  if z = 0 then (0, (2 : FpBLS))
  else (xn * yd * z⁻¹, y' * yn * xd * z⁻¹)

/-- Full `map_to_curve` for G1: SWU on `E'` then the isogeny to `E`. -/
def mapToCurveG1 (u : FpBLS) : FpBLS × FpBLS :=
  isoMap (mapToCurveSimpleSWU isoA isoB swuZ u)

/-! ## §5  Affine group law on E : y² = x³ + 4 -/

/-- An affine point: `some (x,y)` or the point at infinity `none`. -/
abbrev AffinePoint := Option (FpBLS × FpBLS)

/-- The point at infinity. -/
def pointAtInfinity : AffinePoint := none

/-- Affine point addition on `E : y² = x³ + 4` (`a = 0`). Faithful to
    `point_add`. -/
def pointAdd (P Q : AffinePoint) : AffinePoint :=
  match P, Q with
  | none, _ => Q
  | _, none => P
  | some (x1, y1), some (x2, y2) =>
    if x1 = x2 then
      if y1 = -y2 then pointAtInfinity
      else
        let lam := 3 * x1 ^ 2 * (2 * y1)⁻¹
        let x3 := lam ^ 2 - x1 - x2
        let y3 := lam * (x1 - x3) - y1
        some (x3, y3)
    else
      let lam := (y2 - y1) * (x2 - x1)⁻¹
      let x3 := lam ^ 2 - x1 - x2
      let y3 := lam * (x1 - x3) - y1
      some (x3, y3)

/-- Scalar multiplication `[n]P` (repeated addition). -/
def scalarMul : ℕ → AffinePoint → AffinePoint
  | 0, _ => pointAtInfinity
  | n + 1, P => pointAdd P (scalarMul n P)

/-! ## §6  Cofactor clearing (RFC 9380 §8.8.1) -/

/-- The effective cofactor `h_eff = 0xd201000000010001` for BLS12-381 G1. -/
def hEff : ℕ := 0xd201000000010001

/-- Cofactor clearing `[h_eff]P`. -/
def clearCofactor (P : AffinePoint) : AffinePoint := scalarMul hEff P

/-! ## §7  hash_to_curve pipeline (RFC 9380 §3)

`hashToField` (SHA-256 XMD `expand_message` + field reduction, RFC 9380 §5) is
an **opaque input** — see module caveat (2). -/

/-- Domain separation tag for `BLS12381G1_XMD:SHA-256_SSWU_RO_`. As in the Rocq
    spec, users supply their own DST; `[]` is the placeholder. -/
def dstG1 : List UInt8 := []

/-- RFC 9380 §5 `hash_to_field` — the SHA-256/XMD hash + field reduction.
    Opaque: the pipeline below is verified as a function of its output. -/
opaque hashToField : List UInt8 → List UInt8 → ℕ → List FpBLS

/-- `hash_to_curve` (RFC 9380 §3, uniform / RO variant). -/
def hashToCurve (msg dst : List UInt8) : AffinePoint :=
  match hashToField msg dst 2 with
  | [u0, u1] =>
    let Q0 := mapToCurveG1 u0
    let Q1 := mapToCurveG1 u1
    clearCofactor (pointAdd (some Q0) (some Q1))
  | _ => pointAtInfinity

/-- `encode_to_curve` (RFC 9380 §3, nonuniform variant). -/
def encodeToCurve (msg dst : List UInt8) : AffinePoint :=
  match hashToField msg dst 1 with
  | [u0] => clearCofactor (some (mapToCurveG1 u0))
  | _ => pointAtInfinity

/-! ## §8  On-curve predicates and the key correctness statements -/

/-- `(x,y)` is on the target curve `E : y² = x³ + 4`. -/
def onCurveE (pt : FpBLS × FpBLS) : Prop :=
  pt.2 ^ 2 = pt.1 ^ 3 + bls12B

/-- `(x,y)` is on the isogenous curve `E' : y² = x³ + A'·x + B'`. -/
def onCurveEprime (pt : FpBLS × FpBLS) : Prop :=
  pt.2 ^ 2 = pt.1 ^ 3 + isoA * pt.1 + isoB

/-- `on_curve` lifted to `AffinePoint` (`None` = infinity is vacuously on-curve). -/
def onCurveEopt : AffinePoint → Prop
  | none => True
  | some pt => onCurveE pt

/-! ### §8.1  Constant-nonzero lemmas (Rocq `HashToCurveFieldSetup.v`) -/

/-- `A'` is nonzero. -/
theorem isoA_nonzero : isoA ≠ 0 := by
  unfold isoA
  exact fp_nz _ (by norm_num) (by norm_num [BLS12381])

/-- `B'` is nonzero. -/
theorem isoB_nonzero : isoB ≠ 0 := by
  unfold isoB
  exact fp_nz _ (by norm_num) (by norm_num [BLS12381])

/-- `Z = 11` is nonzero. -/
theorem swuZ_nonzero : swuZ ≠ 0 := by
  unfold swuZ
  exact fp_nz _ (by norm_num) (by norm_num [BLS12381])

/-- `Z = 11` is a quadratic **non**-residue mod `p`.

    Where the Rocq proof uses `vm_compute` of `11^((p-1)/2) mod p`, this replays
    the Jacobi-symbol reciprocity algorithm (`norm_num` evaluates
    `jacobiSym 11 p = -1` in `O(log p)`), turns it into `¬ IsSquare (11 : FpBLS)`
    via `ZMod.nonsquare_iff_jacobiSym_eq_neg_one`, and closes `isSquare` through
    `ZMod.euler_criterion` (`11 ≠ 0`, so `IsSquare ↔ 11^(p/2) = 1`). -/
theorem swuZ_nonsquare : isSquare swuZ = false := by
  have hj : jacobiSym 11 BLS12381 = -1 := by norm_num
  have hns : ¬ IsSquare (swuZ : FpBLS) := by
    have h := (ZMod.nonsquare_iff_jacobiSym_eq_neg_one (a := 11) (p := BLS12381)).mp hj
    simpa [swuZ] using h
  have hne0 : (swuZ : FpBLS) ≠ 0 := swuZ_nonzero
  have heuler := ZMod.euler_criterion BLS12381 (a := swuZ) hne0
  have hpow : swuZ ^ (BLS12381 / 2) ≠ 1 := fun h => hns (heuler.mpr h)
  have hexp : legendreExp = BLS12381 / 2 := by norm_num [legendreExp, BLS12381]
  unfold isSquare
  rw [hexp, if_neg hpow, if_neg hne0]

/-! ### §8.2  Square-root correctness (Rocq `HashToCurveSWUProof.v`) -/

/-- If `isSquare x = true` then `(fpSqrt x)² = x`.

    Ports `fp_sqrt_correct_F`. Since `p ≡ 3 mod 4`, `2·sqrtExp = legendreExp + 1`
    (a concrete `Nat` identity discharged by `norm_num`), so
    `(x^sqrtExp)² = x^legendreExp · x`. The `isSquare x = true` hypothesis
    unfolds to `x^legendreExp = 1 ∨ x = 0`; the first branch gives `1 · x = x`,
    the second gives `0 = x`. No Euler criterion is needed — the QR test lives
    entirely in `isSquare`. -/
theorem fpSqrt_correct (x : FpBLS) (h : isSquare x = true) : (fpSqrt x) ^ 2 = x := by
  unfold fpSqrt
  rw [← pow_mul]
  have hexp : sqrtExp * 2 = legendreExp + 1 := by
    norm_num [sqrtExp, legendreExp, BLS12381]
  rw [hexp, pow_succ]
  unfold isSquare at h
  by_cases hx : x ^ legendreExp = 1
  · rw [hx, one_mul]
  · simp only [hx, if_false] at h
    by_cases hx0 : x = 0
    · rw [hx0]; simp
    · simp [hx0] at h

/-! ### §8.3  SWU key identity `gx₂ = t³·gx₁` (Rocq `swu_gx_ratio`) — PROVED -/

/-- **The key SWU identity, `gx₂ = t³·gx₁`** where `t = z·u²` and `S = t²+t`.
    Faithful port of `swu_gx_ratio` (Rocq uses the same `t`, `S := sqr t + t`),
    proved by `field_simp; ring` (the Lean analogue of the Rocq `field` proof).
    This is what forces the Legendre dichotomy
    (`Legendre(gx₂) = -Legendre(gx₁)` when `z` is a nonsquare). -/
theorem swuGxRatio (a b t : FpBLS) (ha : a ≠ 0) (hS : t ^ 2 + t ≠ 0) :
    curveRhs a b (t * ((-b) * a⁻¹ * (1 + (t ^ 2 + t)⁻¹)))
      = t ^ 3 * curveRhs a b ((-b) * a⁻¹ * (1 + (t ^ 2 + t)⁻¹)) := by
  have ht : t ≠ 0 := fun h => hS (by rw [h]; ring)
  have ht1 : t + 1 ≠ 0 := fun h => hS (by have : t = -1 := by linear_combination h
                                          rw [this]; ring)
  unfold curveRhs
  field_simp [ha, ht, ht1]
  ring

/-! ### §8.3b  Euler-symbol helpers for the QR dichotomy -/

/-- `2·((p-1)/2) = p-1`. -/
private theorem two_mul_legendreExp : 2 * legendreExp = BLS12381 - 1 := by
  norm_num [legendreExp, BLS12381]

/-- `legendreExp = p/2`. -/
private theorem legendreExp_eq : legendreExp = BLS12381 / 2 := by
  norm_num [legendreExp, BLS12381]

/-- For `x ≠ 0`, `(x^((p-1)/2))² = 1` (Fermat). -/
private theorem sq_pow_legendreExp (x : FpBLS) (hx : x ≠ 0) :
    (x ^ legendreExp) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm legendreExp 2, two_mul_legendreExp]
  exact ZMod.pow_card_sub_one_eq_one hx

/-- For `x ≠ 0`, the Euler symbol `x^((p-1)/2)` is `±1`. -/
private theorem pow_legendreExp_eq_one_or (x : FpBLS) (hx : x ≠ 0) :
    x ^ legendreExp = 1 ∨ x ^ legendreExp = -1 := by
  have h := sq_pow_legendreExp x hx
  rw [pow_two] at h
  exact mul_self_eq_one_iff.mp h

/-- `isSquare x = false` gives Euler symbol `-1`. -/
private theorem pow_legendreExp_of_isSquare_false (x : FpBLS)
    (h : isSquare x = false) : x ^ legendreExp = -1 := by
  unfold isSquare at h
  by_cases h1 : x ^ legendreExp = 1
  · rw [if_pos h1] at h; simp at h
  · rw [if_neg h1] at h
    by_cases h0 : x = 0
    · rw [if_pos h0] at h; simp at h
    · rcases pow_legendreExp_eq_one_or x h0 with he | he
      · exact absurd he h1
      · exact he

/-- `x^((p-1)/2) = 1` gives `isSquare x = true`. -/
private theorem isSquare_of_pow_legendreExp (x : FpBLS)
    (h : x ^ legendreExp = 1) : isSquare x = true := by
  unfold isSquare
  rw [if_pos h]

/-- `Z = 11` has Euler symbol `-1`. -/
private theorem swuZ_pow_legendreExp : swuZ ^ legendreExp = -1 :=
  pow_legendreExp_of_isSquare_false swuZ swuZ_nonsquare

/-- **The `tv1 = 0` edge value is a square** (the single computational residue).

    In the edge case the map sets `x₁ = B'·(Z·A')⁻¹`, and the RFC guarantees
    `gx₁ = curveRhs A' B' x₁` is a QR — this is the property that makes `Z = 11`
    an *admissible* SWU constant for the specific isogenous curve `E'`. Unlike the
    non-edge dichotomy (which is algebraic: `swuGxRatio` + `Z` nonsquare +
    quadratic-character multiplicativity), this fact is **not** derivable "by
    construction": it is a property of the concrete `(A', B', Z)` triple, and the
    reference Rocq proof discharges the corresponding
    `edge_case_gx1_is_square` in `HashToCurveSWUCompute.v` by `native_compute;
    reflexivity` (a Legendre-symbol evaluation on the concrete field element
    `gx₁ = curveRhs A' B' (B'·(Z·A')⁻¹)`).

    The proof computes the natural-number representative `gn` of `gx₁` through
    `invMod`, checks `powMod gn legendreExp p = 1` by `native_decide`, and
    transports both to `FpBLS` with `invMod_cast` and `powMod_cast`. -/
private theorem edge_case_gx1_is_square :
    isSquare (curveRhs isoA isoB (isoB * (swuZ * isoA)⁻¹)) = true := by
  set aAn : ℕ := 0x144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d
  set aBn : ℕ := 0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0
  set ivn : ℕ := Transfer.ZModPowMod.invMod (11 * aAn) BLS12381 with hivn
  set x1n : ℕ := aBn * ivn with hx1n
  set gn  : ℕ := x1n ^ 3 + aAn * x1n + aBn with hgnn
  have hne : (11 * aAn) % BLS12381 ≠ 0 := by decide
  have hgn : Transfer.ZModPowMod.powMod gn legendreExp BLS12381 = 1 := by native_decide
  have hA : isoA = (aAn : FpBLS) := rfl
  have hB : isoB = (aBn : FpBLS) := rfl
  have hmul : swuZ * isoA = ((11 * aAn : ℕ) : FpBLS) := by
    rw [hA]; simp only [swuZ]; push_cast; ring
  have hinv : (swuZ * isoA)⁻¹ = ((ivn : ℕ) : FpBLS) := by
    rw [hmul, hivn, Transfer.ZModPowMod.invMod_cast BLS12381 (11 * aAn) hne]
  have hbridge : curveRhs isoA isoB (isoB * (swuZ * isoA)⁻¹) = (gn : FpBLS) := by
    rw [curveRhs, hinv, hA, hB, hgnn, hx1n]
    push_cast; ring
  rw [hbridge]
  have hsq : (gn : FpBLS) ^ legendreExp = 1 := by
    rw [← Transfer.ZModPowMod.powMod_cast gn legendreExp BLS12381, hgn, Nat.cast_one]
  unfold isSquare
  rw [if_pos hsq]

/-! ### §8.4  SWU lands on E' (Rocq `swu_maps_to_Eprime_proof`) -/

/-- **The SWU map lands on `E'`.**

    The assembly is **algebraic and complete** (mirroring `HashToCurveSWUProof.v`):
    (i) `swuGxRatio` — the `gx₂ = (Z·u²)³·gx₁` field identity (proved); (ii) the
    QR-dichotomy that at least one of `gx₁, gx₂` is a square, obtained from
    `swuZ_nonsquare` (proved) via quadratic-character multiplicativity of the Euler
    symbol — in the non-edge branch `Legendre(gx₂) = Legendre(Z·u²)·Legendre(gx₁) =
    -Legendre(gx₁)`, so `gx₁` a nonsquare forces `gx₂` a square; and (iii)
    `fpSqrt_correct` (proved), giving `y² = g(x)` for whichever branch is chosen.

    The `tv1 = 0` branch uses `edge_case_gx1_is_square`, the concrete Legendre
    check on the `(A', B', Z)` triple, proved by `native_decide`; this is the
    theorem's only dependence on `Lean.ofReduceBool`. The proof body itself
    evaluates no numeral: the map's output is related to named intermediates by
    rewriting each intermediate into the definition's `let`-form body and closing
    with `exact rfl`, without zeta-expanding the body. -/
theorem swuMapsToEprime (u : FpBLS) :
    onCurveEprime (mapToCurveSimpleSWU isoA isoB swuZ u) := by
  obtain ⟨tv1, htv1⟩ : ∃ t : FpBLS, t = (swuZ ^ 2 * (u ^ 2) ^ 2 + swuZ * u ^ 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨x1, hx1⟩ : ∃ x : FpBLS,
      x = if tv1 = 0 then isoB * (swuZ * isoA)⁻¹ else -isoB * isoA⁻¹ * (1 + tv1) := ⟨_, rfl⟩
  obtain ⟨gx1, hgx1⟩ : ∃ g : FpBLS, g = curveRhs isoA isoB x1 := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ x : FpBLS, x = swuZ * u ^ 2 * x1 := ⟨_, rfl⟩
  obtain ⟨gx2, hgx2⟩ : ∃ g : FpBLS, g = curveRhs isoA isoB x2 := ⟨_, rfl⟩
  obtain ⟨xy, hxy⟩ : ∃ p : FpBLS × FpBLS,
      p = if isSquare gx1 then (x1, fpSqrt gx1) else (x2, fpSqrt gx2) := ⟨_, rfl⟩
  -- the map's output in terms of the named intermediates; the equation is closed
  -- by `exact rfl` against the `let`-form body, which is never zeta-expanded
  have hmap : mapToCurveSimpleSWU isoA isoB swuZ u
      = (xy.1, if sgn0 u = sgn0 xy.2 then xy.2 else -xy.2) := by
    rw [hxy, hgx2, hx2, hgx1, hx1, htv1]
    exact rfl
  rw [onCurveEprime, hmap]
  -- the sign fix does not change `y²`
  have hy2 : (if sgn0 u = sgn0 xy.2 then xy.2 else -xy.2) ^ 2 = xy.2 ^ 2 := by
    split_ifs <;> ring
  rw [hy2]
  by_cases hgs : isSquare gx1 = true
  · -- `gx₁` is a square: take the `x₁` branch, `y² = gx₁`
    rw [hxy, if_pos hgs]
    dsimp only
    rw [fpSqrt_correct gx1 hgs, hgx1]
    simp only [curveRhs]
  · -- `gx₁` is a nonsquare: the `x₂` branch, and `gx₂` is a square by the dichotomy
    have hgsf : isSquare gx1 = false := by
      cases h : isSquare gx1 with
      | false => rfl
      | true => exact absurd h hgs
    have hgs2 : isSquare gx2 = true := by
      by_cases htv0 : tv1 = 0
      · -- edge case is impossible here: the edge `gx₁` is a square
        exfalso
        have hsq1 : isSquare gx1 = true := by
          rw [hgx1, hx1, if_pos htv0]; exact edge_case_gx1_is_square
        rw [hsq1] at hgsf; simp at hgsf
      · -- non-edge: `gx₂ = (Z·u²)³·gx₁`, and the Euler symbols multiply to `+1`
        have hu0 : u ≠ 0 := by
          intro h; apply htv0; rw [htv1, h]; simp
        have hins : swuZ ^ 2 * (u ^ 2) ^ 2 + swuZ * u ^ 2
            = (swuZ * u ^ 2) ^ 2 + swuZ * u ^ 2 := by ring
        have hSne : swuZ ^ 2 * (u ^ 2) ^ 2 + swuZ * u ^ 2 ≠ 0 := by
          intro h; apply htv0; rw [htv1, h]; exact inv_zero
        have hSne' : (swuZ * u ^ 2) ^ 2 + swuZ * u ^ 2 ≠ 0 := by rw [← hins]; exact hSne
        have htv1b : tv1 = ((swuZ * u ^ 2) ^ 2 + swuZ * u ^ 2)⁻¹ := by rw [htv1, hins]
        have hx1v : x1 = -isoB * isoA⁻¹ * (1 + ((swuZ * u ^ 2) ^ 2 + swuZ * u ^ 2)⁻¹) := by
          rw [hx1, if_neg htv0, htv1b]
        have hgx2v : gx2 = (swuZ * u ^ 2) ^ 3 * gx1 := by
          have key := swuGxRatio isoA isoB (swuZ * u ^ 2) isoA_nonzero hSne'
          rw [hgx2, hx2, hgx1, hx1v]
          exact key
        have htleg : (swuZ * u ^ 2) ^ legendreExp = -1 := by
          rw [mul_pow, swuZ_pow_legendreExp, pow_right_comm, sq_pow_legendreExp u hu0, mul_one]
        have hg2leg : gx2 ^ legendreExp = 1 := by
          rw [hgx2v, mul_pow, pow_right_comm, htleg,
            pow_legendreExp_of_isSquare_false gx1 hgsf]
          ring
        exact isSquare_of_pow_legendreExp gx2 hg2leg
    rw [hxy, if_neg hgs]
    dsimp only
    rw [fpSqrt_correct gx2 hgs2, hgx2]
    simp only [curveRhs]

/-! ### §8.5  The isogeny maps E' → E (Rocq `iso_map_on_curve`) -/

-- `isogenyPolyIdentity` (the RFC E.2 degree-63 polynomial identity
-- `curve(x')·ynum²·xden³ = xnum³·yden² + 4·xden³·yden²`) is proved in
-- `IsogenyPolyIdentity` by the bounded reflective coefficient check.

/-- The generic-branch algebra over opaque atoms: no concrete Horner
    coefficient is in scope, so `field_simp`/`linear_combination` face nine
    variables and coefficient `1`/`B` monomials — cost independent of the
    381-bit constants. `hident` is the cleared-denominator isogeny identity. -/
private theorem isoMap_generic_aux
    (x' y' xn xd yn yd a b B : FpBLS)
    (hxd0 : xd ≠ 0) (hyd0 : yd ≠ 0)
    (hcurve : y' ^ 2 = x' ^ 3 + a * x' + b)
    (hident : (x' ^ 3 + a * x' + b) * yn ^ 2 * xd ^ 3
              = xn ^ 3 * yd ^ 2 + B * xd ^ 3 * yd ^ 2) :
    (y' * yn * xd * (xd * yd)⁻¹) ^ 2 = (xn * yd * (xd * yd)⁻¹) ^ 3 + B := by
  have hz0 : xd * yd ≠ 0 := mul_ne_zero hxd0 hyd0
  field_simp
  linear_combination hident + (yn ^ 2 * xd ^ 3) * hcurve

/-- **The isogeny maps every `E'` point to an `E` point.** Ports
    `iso_map_on_curve`. The kernel case (`z = 0 ⇒ (0,2) ∈ E`) is closed by
    `norm_num`; the generic case discharges `isoMap_generic_aux` on the four
    Horner terms plus `isogenyPolyIdentity` — the concrete coefficients never
    reach `field_simp`, so the cost is independent of the coefficient magnitudes. -/
theorem isoMapsEprimeToE (pt : FpBLS × FpBLS) (h : onCurveEprime pt) :
    onCurveE (isoMap pt) := by
  obtain ⟨x', y'⟩ := pt
  unfold onCurveEprime at h
  simp only at h
  unfold onCurveE isoMap
  simp only
  by_cases hzero : hornerEvalMonic isoXden x' * hornerEvalMonic isoYden x' = 0
  · -- kernel case: image is (0, 2), and 2² = 0³ + 4
    rw [if_pos hzero]; norm_num [bls12B]
  · rw [if_neg hzero]
    have hxd0 : hornerEvalMonic isoXden x' ≠ 0 := fun h0 => hzero (by rw [h0, zero_mul])
    have hyd0 : hornerEvalMonic isoYden x' ≠ 0 := fun h0 => hzero (by rw [h0, mul_zero])
    exact isoMap_generic_aux x' y'
      (hornerEval isoXnum x') (hornerEvalMonic isoXden x')
      (hornerEval isoYnum x') (hornerEvalMonic isoYden x')
      isoA isoB bls12B hxd0 hyd0 h (isogenyPolyIdentity x')

/-! ### §8.6  Full map produces curve points (Rocq `map_produces_curve_points`) -/

/-- **The full G1 map produces points on `E`.** Proved as the composition
    `isoMapsEprimeToE ∘ swuMapsToEprime`. Mirrors
    `map_produces_curve_points_proof`. -/
theorem mapProducesCurvePoints (u : FpBLS) : onCurveE (mapToCurveG1 u) := by
  unfold mapToCurveG1
  exact isoMapsEprimeToE _ (swuMapsToEprime u)

/-! ## §9  Cofactor clearing preserves on-curve (Rocq `HashToCurveClosureProof.v`) — PROVED -/

/-- **`pointAdd` preserves on-curve membership.** Ports `point_add_preserves`;
    both branches close by `field_simp; ring` (the Lean analogue of Rocq's
    `Field.fsatz`), using `y² = x³ + 4` for the inputs. -/
theorem pointAddPreserves (P Q : AffinePoint)
    (hP : onCurveEopt P) (hQ : onCurveEopt Q) : onCurveEopt (pointAdd P Q) := by
  match P, Q with
  | none, _ => simpa [pointAdd] using hQ
  | some _, none => simpa [pointAdd] using hP
  | some (x1, y1), some (x2, y2) =>
    simp only [onCurveEopt, onCurveE, bls12B] at hP hQ ⊢
    by_cases hx : x1 = x2
    · by_cases hy : y1 = -y2
      · simp [pointAdd, pointAtInfinity, hx, hy]
      · simp only [pointAdd]
        rw [if_pos hx, if_neg hy]
        subst hx
        dsimp only
        have hy1 : y1 ≠ 0 := by
          intro h0
          apply hy
          have hyy : y2 ^ 2 = y1 ^ 2 := by rw [hQ, hP]
          rw [h0] at hyy
          have hy2 : y2 ^ 2 = 0 := by rw [hyy]; ring
          have : y2 = 0 := by
            simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy2
          rw [h0, this]; ring
        have h2 : (2 : FpBLS) ≠ 0 := fp_nz 2 (by norm_num) (by norm_num [BLS12381])
        field_simp
        linear_combination (64 * y1 ^ 6) * hP
    · simp only [pointAdd, if_neg hx]
      have hxx : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      field_simp
      linear_combination (-x1 ^ 6 + 3 * x1 ^ 5 * x2 - 9 * x1 ^ 3 * x2 ^ 3 + x1 ^ 3 * y1 ^ 2
          - 2 * x1 ^ 3 * y1 * y2 + 4 * x1 ^ 3 + 12 * x1 ^ 2 * x2 ^ 4 - 3 * x1 ^ 2 * x2 * y1 ^ 2
          + 6 * x1 ^ 2 * x2 * y1 * y2 - 12 * x1 ^ 2 * x2 - 6 * x1 * x2 ^ 5 + 3 * x1 * x2 ^ 2 * y1 ^ 2
          - 6 * x1 * x2 ^ 2 * y1 * y2 + 12 * x1 * x2 ^ 2 + x2 ^ 6 - x2 ^ 3 * y1 ^ 2
          + 2 * x2 ^ 3 * y1 * y2 - 4 * x2 ^ 3) * hP
        + (x1 ^ 6 - 6 * x1 ^ 5 * x2 + 12 * x1 ^ 4 * x2 ^ 2 - 9 * x1 ^ 3 * x2 ^ 3
          + 2 * x1 ^ 3 * y1 * y2 - x1 ^ 3 * y2 ^ 2 - 4 * x1 ^ 3 - 6 * x1 ^ 2 * x2 * y1 * y2
          + 3 * x1 ^ 2 * x2 * y2 ^ 2 + 12 * x1 ^ 2 * x2 + 3 * x1 * x2 ^ 5 + 6 * x1 * x2 ^ 2 * y1 * y2
          - 3 * x1 * x2 ^ 2 * y2 ^ 2 - 12 * x1 * x2 ^ 2 - x2 ^ 6 - 2 * x2 ^ 3 * y1 * y2
          + x2 ^ 3 * y2 ^ 2 + 4 * x2 ^ 3) * hQ

/-- **`scalarMul` preserves on-curve.** Induction on `n`. -/
theorem scalarMulPreserves (n : ℕ) (P : AffinePoint)
    (hP : onCurveEopt P) : onCurveEopt (scalarMul n P) := by
  induction n with
  | zero => exact True.intro
  | succ n ih => exact pointAddPreserves P (scalarMul n P) hP ih

/-- **Cofactor clearing preserves on-curve.** Ports `clear_cofactor_preserves`.
    Fully proved (up to `pointAddPreserves`). -/
theorem clearCofactorPreserves (P : AffinePoint)
    (hP : onCurveEopt P) : onCurveEopt (clearCofactor P) :=
  scalarMulPreserves hEff P hP

end CatCrypt.Crypto.Pairing.HashToCurveBLS12381
