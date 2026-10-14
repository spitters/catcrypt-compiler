/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneReadback
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Poseidon2 external MDS on the unified cross-lane SIMD path

The Poseidon2 width-16 external MDS (`mds16`) has two cross-lane steps — the
per-4-block circulant `M4 = circ(2,3,1,1)` and the column-sum — that route data
across the 8×u64 lanes of a ZMM register. The per-lane `zmmPackQ` fragment
(`vpaddq`/`vpmullq`/… over `reg 512`) cannot express them: `zmmPackQ`'s output
lane `i` depends only on input lane `i`.

The unified path carries the cross-lane family as the `extCall` leaf with a
compile-time-constant control `σ : Fin 8 → Fin 8` — the same mechanism ChaCha's
`vpshufb` rotate uses (`CrossLaneSimdEmit`). The leaf's data effect on an 8-lane
qword bundle is `vshuffle σ` (`CrossLaneReadback`), output lane `i` reading input
lane `σ i`; the emitted instruction's byte-identity to its reference is the
leaf's KAT (Tier-B, external bench), the same discipline as the ChaCha `vpshufb`
leaf, rather than an in-tree Lean encoder claim.

This module re-expresses `M4` and the column-sum on that surviving path:

* the within-block rotate `P` and the block-swap `P₄` are the fixed controls
  `rotσ` / `rot4σ`, applied by `vshuffle` (the `vpermq`-constant-control leaf);
* the scale-and-sum is per-lane add, the image of `zmmPackQ .add` under the lane
  bridge `zmmPackQ_lane`;
* `m4_vec_eq_scalar` / `colsum_vec_eq_scalar` prove the vectorised block equals
  the scalar `mds16` loop, over the wrapping `BitVec 64` add the ZMM ops compute.

The lane bundle `Zmm8 = Fin 8 → BitVec 64` is the `zmmLane` view of a `reg 512`;
`zmmPackQ_lane` / `zmmOfLanes_zmmLane'` connect the bundle statements to the
`BitVec 512` denotation the emitter produces.

The MDS is a linear map, so the per-lane BabyBear `csub` reduce commutes with it
and is applied after the linear mix, unchanged from the field-arithmetic
half-kernels.

## Main results

* `permP` / `permRot4` — the within-block rotate and block-swap as `vshuffle`
  cross-lane leaves.
* `m4_vec_eq_scalar` — the vectorised `M4 = 2I+3P+P²+P³` equals the scalar
  `circ(2,3,1,1)` block loop.
* `colsum_vec_eq_scalar` — the rotate-by-4 column sum equals the scalar `mds16`
  column sum.
* `linCombLane_m4_eq_scalar` — the generic `Σ cₖ·Pᵏx` schedule at `M4` equals the
  scalar circulant.
* `m4Zmm_lanes` — the `BitVec 512` lift: the M4 block from `zmmPackQ .add` + the
  `zmmPerm rotσ` leaf reads, lane for lane, as `m4Lane (lanesOf x)`, connecting the
  bundle proofs to the emitted denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2MdsPermUnified

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneReadback
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect (VectorTy)

/-! ## 0. The 8×u64 lane bundle and the `BitVec 512` lane bridge -/

/-- An 8×u64 ZMM register as a lane bundle: `Fin 8 → BitVec 64`, the `zmmLane`
    view of a `reg 512`. -/
abbrev Zmm8 : Type := VectorTy (BitVec 64) 8

/-- Reading lane `k` of an assembled bundle recovers the lane value. -/
theorem zmmOfLanes_zmmLane' (f : Fin 8 → BitVec 64) (k : Fin 8) :
    zmmLane (zmmOfLanes f) k = f k := by
  fin_cases k <;>
    (unfold zmmLane zmmOfLanes
     norm_num [Fin.val_ofNat, BitVec.extractLsb'_append_eq_of_le,
       BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_right,
       BitVec.extractLsb'_append_eq_left]) <;>
    rfl

/-- Lane `k` of `zmmPackQ bop a b` is the scalar `bop` of the two lanes: the
    per-lane meaning of `vpaddq`/`vpsubq`/… on the `BitVec 512` denotation. -/
theorem zmmPackQ_lane (bop : JasminBinOp) (a b : BitVec 512) (k : Fin 8) :
    zmmLane (zmmPackQ bop a b) k = bop.applyLane (zmmLane a k) (zmmLane b k) := by
  unfold zmmPackQ
  rw [zmmOfLanes_zmmLane']

/-! ## 1. The two cross-lane controls: within-block rotate and block-swap -/

/-- The within-block rotate-by-1 control `[1,2,3,0, 5,6,7,4]`: output lane `j`
    reads input lane `4·(j/4) + (j+1)%4` (rotate by one inside each 4-block).
    The fixed, public `vpermq` control realising `P`. -/
def rotσ : Fin 8 → Fin 8 := fun j =>
  ⟨4 * (j.val / 4) + (j.val + 1) % 4, by
    have h1 : (j.val + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    have h2 : j.val < 8 := j.isLt
    have h3 : j.val / 4 ≤ 1 := by omega
    omega⟩

/-- The block-swap control `[4,5,6,7, 0,1,2,3]`: output lane `j` reads input lane
    `(j+4)%8` (swap the two 4-blocks of a ZMM — a cross-256 move). The fixed
    `vpermq` control realising the column-sum's `P₄`. -/
def rot4σ : Fin 8 → Fin 8 := fun j =>
  ⟨(j.val + 4) % 8, Nat.mod_lt _ (by decide)⟩

/-- The within-block cyclic rotation `P` as the constant-control cross-lane leaf
    (`vshuffle rotσ` = the `vpermq`-with-immediate data effect). -/
def permP (a : Zmm8) : Zmm8 := vshuffle rotσ a

/-- `permP` is exactly the within-block rotate-by-1. -/
theorem permP_apply (a : Zmm8) (j : Fin 8) :
    permP a j = a ⟨4 * (j.val / 4) + (j.val + 1) % 4, by
      have h1 : (j.val + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
      have h2 : j.val < 8 := j.isLt
      have h3 : j.val / 4 ≤ 1 := by omega
      omega⟩ := rfl

/-- The block-swap `P₄` as the constant-control cross-lane leaf. -/
def permRot4 (a : Zmm8) : Zmm8 := vshuffle rot4σ a

/-- `permRot4` is exactly the rotate-by-4 (block swap). -/
theorem permRot4_apply (a : Zmm8) (j : Fin 8) :
    permRot4 a j = a ⟨(j.val + 4) % 8, Nat.mod_lt _ (by decide)⟩ := rfl

/-! ## 2. The vectorised `M4` and its equality to the scalar `circ(2,3,1,1)` -/

/-- The lane function the vectorised `M4` block computes: `2·x + 3·(Px) + P²x +
    P³x` per lane, over wrapping 64-bit add (the `vpaddq` semantics). The `P`
    powers are cross-lane leaves; the scale-and-sum is per-lane add. -/
def m4Lane (x : Zmm8) : Zmm8 :=
  let p1 := permP x
  let p2 := permP p1
  let p3 := permP p2
  fun j => (x j + x j) + (p1 j + p1 j + p1 j) + p2 j + p3 j

/-- The scalar `mds16` block circulant `circ(2,3,1,1)`, lane-indexed on the
    8-lane register (each 4-block independently). -/
def m4ScalarLane (x : Zmm8) : Zmm8 := fun j =>
  let b := 4 * (j.val / 4)
  let r1 := x ⟨b + (j.val + 1) % 4, by
    have : (j.val + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    have : j.val < 8 := j.isLt
    have : j.val / 4 ≤ 1 := by omega
    omega⟩
  let r2 := x ⟨b + (j.val + 2) % 4, by
    have : (j.val + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
    have : j.val < 8 := j.isLt
    have : j.val / 4 ≤ 1 := by omega
    omega⟩
  let r3 := x ⟨b + (j.val + 3) % 4, by
    have : (j.val + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
    have : j.val < 8 := j.isLt
    have : j.val / 4 ≤ 1 := by omega
    omega⟩
  (x j + x j) + (r1 + r1 + r1) + r2 + r3

/-- **The vectorised `M4` equals the scalar `circ(2,3,1,1)` block map.** Lane for
    lane, the cross-lane-permute-and-add `m4Lane` is the scalar `mds16` block
    circulant, over the same wrapping `BitVec 64` add the `vpaddq`/`vpermq` ops
    compute. The algebraic correctness of the cross-lane MDS wiring. -/
theorem m4_vec_eq_scalar (x : Zmm8) : m4Lane x = m4ScalarLane x := by
  funext j
  simp only [m4Lane, m4ScalarLane, permP, vshuffle_apply, rotσ]
  fin_cases j <;> rfl

/-! ## 3. The column-sum and its equality to the scalar `mds16` column-sum

The 16-lane state is two 8-lane ZMMs, `lo = s[0..7]` and `hi = s[8..15]` (the
`M4` outputs). The column-sum broadcasts `Σ_{4 blocks} m4[·][k]` back to all 16
lanes, realised per ZMM by a block-swap `P₄` and per-lane adds. -/

/-- The column total at lane `j`: blocks-0+1 (`lo + P₄lo`) plus blocks-2+3
    (`hi + P₄hi`) — the sum of all four blocks at position `j%4`. -/
def csumLane (lo hi : Zmm8) : Zmm8 := fun j =>
  (lo j + permRot4 lo j) + (hi j + permRot4 hi j)

/-- The low ZMM of the full external MDS: `m4[j] + colsum`. -/
def oloLane (lo hi : Zmm8) : Zmm8 := fun j => lo j + csumLane lo hi j

/-- The high ZMM of the full external MDS: `m4[j] + colsum`. -/
def ohiLane (lo hi : Zmm8) : Zmm8 := fun j => hi j + csumLane lo hi j

/-- The scalar `mds16` column-sum reference on the low ZMM. -/
def mds16ScalarLo (lo hi : Zmm8) : Zmm8 := fun j =>
  lo j + ((lo j + lo ⟨(j.val + 4) % 8, Nat.mod_lt _ (by decide)⟩)
            + (hi j + hi ⟨(j.val + 4) % 8, Nat.mod_lt _ (by decide)⟩))

/-- The scalar `mds16` column-sum reference on the high ZMM. -/
def mds16ScalarHi (lo hi : Zmm8) : Zmm8 := fun j =>
  hi j + ((lo j + lo ⟨(j.val + 4) % 8, Nat.mod_lt _ (by decide)⟩)
            + (hi j + hi ⟨(j.val + 4) % 8, Nat.mod_lt _ (by decide)⟩))

/-- **The vectorised column-sum equals the scalar `mds16` column-sum.** -/
theorem colsum_vec_eq_scalar (lo hi : Zmm8) :
    oloLane lo hi = mds16ScalarLo lo hi ∧ ohiLane lo hi = mds16ScalarHi lo hi := by
  constructor <;>
    · funext j
      simp only [oloLane, ohiLane, csumLane, mds16ScalarLo, mds16ScalarHi,
        permRot4, vshuffle_apply, rot4σ]

/-! ## 4. The generic `linCombEmit` spec: `Σ cₖ·Pᵏ x` as the M4 instance

The M4 schedule is the pass output of a generic linear-combination-of-permute-
powers spec, of which `M4 = 2·P⁰ + 3·P¹ + P² + P³` is one instance. The pass
form emits each power `Pᵏ` as a cross-lane leaf and the accumulation as per-lane
adds; here we carry the *spec* and its equality to the scalar circulant. -/

/-- `P` iterated `k` times (`P = vshuffle rotσ`). -/
def permIter : Nat → Zmm8 → Zmm8
  | 0,     x => x
  | (k+1), x => vshuffle rotσ (permIter k x)

/-- Expand `terms` (coefficient, power) to a flat list of powers, each `k`
    repeated `c` times (`c·Pᵏ` = `c` copies of `Pᵏ`). -/
def expand (terms : List (Nat × Nat)) : List Nat :=
  terms.flatMap (fun ck => List.replicate ck.1 ck.2)

/-- The lane function the linear combination computes (wrapping `BitVec 64` add). -/
def linCombLane (terms : List (Nat × Nat)) (x : Zmm8) : Zmm8 :=
  fun j => (expand terms).foldl (fun s k => s + permIter k x j) 0

/-- The `circ(2,3,1,1)` coefficient/power terms: `2·P⁰ + 3·P¹ + 1·P² + 1·P³`. -/
def m4Terms : List (Nat × Nat) := [(2, 0), (3, 1), (1, 2), (1, 3)]

/-- **The linear-combination spec at `m4Terms` is the vectorised `M4` block.** The
    generic `Σ cₖ·Pᵏ x` fold, instantiated at the M4 coefficients, expands to
    `2x + 3(Px) + P²x + P³x` per lane — the schedule a pass emits as permute
    leaves plus per-lane adds. -/
theorem linCombLane_m4_eq_m4Lane (x : Zmm8) :
    linCombLane m4Terms x = m4Lane x := by
  funext j
  have he : expand m4Terms = [0, 0, 1, 1, 1, 2, 3] := rfl
  simp only [linCombLane, he, List.foldl_cons, List.foldl_nil, m4Lane, permP,
    permIter]
  ring

/-- **The linear-combination spec at `m4Terms` computes the scalar `circ(2,3,1,1)`.**
    Chaining `linCombLane_m4_eq_m4Lane` with `m4_vec_eq_scalar`: the pass-generated
    schedule equals the scalar `mds16` block circulant, carried by these
    equalities rather than hand matching. -/
theorem linCombLane_m4_eq_scalar (x : Zmm8) :
    linCombLane m4Terms x = m4ScalarLane x :=
  (linCombLane_m4_eq_m4Lane x).trans (m4_vec_eq_scalar x)

/-! ## 5. The `BitVec 512` lift: the bundle statements on the emitted denotation

The `M4` block over `BitVec 512` uses `zmmPackQ .add` for each per-lane add and
the cross-lane leaf (`vpermq` control `rotσ`) for each `P`. Reading lane `k`
(`zmmPackQ_lane`) reduces every add to its scalar lane op, so the `BitVec 512`
block's lane function is `m4Lane` of the input's lane bundle — and hence, by
`m4_vec_eq_scalar`, the scalar circulant. -/

/-- The input `reg 512` viewed as its 8-lane bundle. -/
def lanesOf (a : BitVec 512) : Zmm8 := fun k => zmmLane a k

/-- The cross-lane leaf on `BitVec 512`: reassemble the `vshuffle σ` of the lane
    bundle. This is the `BitVec 512` denotation of the `vpermq`-constant-control
    `extCall` leaf (byte-identity is the leaf's external KAT, Tier-B). -/
def zmmPerm (σ : Fin 8 → Fin 8) (a : BitVec 512) : BitVec 512 :=
  zmmOfLanes (vshuffle σ (lanesOf a))

/-- Lane `k` of `zmmPerm σ a` reads lane `σ k` of `a` — the cross-lane law on the
    `BitVec 512` denotation. -/
theorem zmmPerm_lane (σ : Fin 8 → Fin 8) (a : BitVec 512) (k : Fin 8) :
    zmmLane (zmmPerm σ a) k = zmmLane a (σ k) := by
  unfold zmmPerm
  rw [zmmOfLanes_zmmLane']
  rfl

/-- **The `BitVec 512` `M4` block's lane bundle is the vectorised `m4Lane`.** The
    block `2x + 3(Px) + P²x + P³x` built from `zmmPackQ .add` and the `zmmPerm
    rotσ` cross-lane leaf reads, lane for lane, as `m4Lane (lanesOf x)`. Combined
    with `m4_vec_eq_scalar` this is the emitted-denotation correctness of the
    cross-lane MDS block. -/
theorem m4Zmm_lanes (x : BitVec 512) :
    let p1 := zmmPerm rotσ x
    let p2 := zmmPerm rotσ p1
    let p3 := zmmPerm rotσ p2
    (fun k => zmmLane
      (zmmPackQ .add
        (zmmPackQ .add
          (zmmPackQ .add (zmmPackQ .add x x)
            (zmmPackQ .add (zmmPackQ .add p1 p1) p1))
          p2)
        p3) k)
      = m4Lane (lanesOf x) := by
  funext k
  simp only [zmmPackQ_lane, JasminBinOp.applyLane, m4Lane, permP, lanesOf,
    zmmPerm_lane, vshuffle_apply]
