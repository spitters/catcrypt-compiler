/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-!
# Poseidon2 lane bundles through the structured VectorDialect (pure reuse)

The Poseidon2 BabyBear permutation, when lane-bundled across a 4-slot `__m256i`
packed-u64 tile (`VIR/Poseidon2SimdReduce`), uses two lane-parallel phases:

* the **linear layer** / round-constant add — pointwise `VectorOp.add`
  (`#VPADD_4u64`);
* the **S-box** `x ↦ x^5` — a chain of pointwise `VectorOp.mul`
  (`x² → x⁴ → x⁴·x = x⁵`);
* the **field reduce** (Barrett fold) inside `fmul` — pointwise `VectorOp.shiftR`
  (`#VPSRL_4u64`) + `VectorOp.add` (`#VPADD_4u64`) + a lane-spread scalar
  multiply (`* BBC`, no native AVX2 packed-u64-by-scalar, so it stays scalar).

This is **pure reuse** of the dialect alphabet (`add`/`mul`/`shiftR`) — no new
op needed. This file pins the Poseidon2 lane-bundle meaning against the dialect
ops and grounds its denotation in the proven `LaneMap.poseidon2_sbox_lane_map`
theorem. All reused ops lower with proven denotation preservation
(`lower_add_correct`, `lower_mul`-shape, `lower_shiftR_correct`).

The existing Poseidon2 emit (`VIR/Poseidon2Emit` / `Poseidon2SimdReduce`) is
left **untouched**; the reuse demonstrated here is at the DENOTATION level (the
dialect ops denote the same per-lane operations the direct emit realizes).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap (poseidon2_sbox_lane_map poseidon2SBoxStub)

/-! ## 1. Poseidon2 lane shape: a 4-slot `__m256i` packed-u64 tile.

The BabyBear coefficient is a `u64` lane (`< 2^31` canonical, `< 2^62`
unreduced product); 4 lanes fit one `__m256i`. -/

/-- The Poseidon2 SIMD lane count (4 × u64 per `__m256i`). -/
abbrev poseidon2LaneN : Nat := 4

/-- The 64-bit lane multiply (`fmul`'s un-reduced product, before the Barrett
    fold). -/
abbrev pmul (x y : BitVec 64) : BitVec 64 := x * y
/-- The 64-bit lane add (`#VPADD_4u64` — RC-add / linear layer / fold combine). -/
abbrev padd (x y : BitVec 64) : BitVec 64 := x + y
/-- The 64-bit lane shift-right (`#VPSRL_4u64` — the Barrett fold's `>>> 31`). -/
abbrev pshr (x : BitVec 64) (m : Nat) : BitVec 64 := x >>> m

/-! ## 2. The linear layer / RC-add as the dialect `add` op (reuse) -/

/-- The dialect `add` op carrying `padd` denotes the per-lane add — the
    abstract classifier of the `#VPADD_4u64` linear-layer / RC-add /
    fold-combine ops. -/
theorem add_denote (v w : VectorTy (BitVec 64) poseidon2LaneN) :
    denoteVectorOp (.add padd v w : VectorOp (BitVec 64) poseidon2LaneN)
      = .vec (fun i => v i + w i) := rfl

/-! ## 3. The S-box `x^5` as a dialect `mul` chain (reuse)

`x^5 = ((x·x)·(x·x))·x`. Each `·` is a pointwise `VectorOp.mul`. We pin the
chain's per-lane denotation and ground it in the proven S-box lane-map theorem. -/

/-- The dialect `mul` op carrying `pmul` denotes the per-lane multiply. -/
theorem mul_denote (v w : VectorTy (BitVec 64) poseidon2LaneN) :
    denoteVectorOp (.mul pmul v w : VectorOp (BitVec 64) poseidon2LaneN)
      = .vec (fun i => v i * w i) := rfl

/-- The lane-wise `x^5` S-box, written as the `mul`-chain `x²·x²·x` the dialect
    realizes, equals the scalar per-lane `x·x·x·x·x`. Grounded in the proven
    `poseidon2_sbox_lane_map` theorem (per-slot independence). -/
theorem sbox_denotation_preserves (state : VectorTy (BitVec 64) poseidon2LaneN) :
    poseidon2SBoxStub state =
      (fun i => let x := state i; x * x * x * x * x) :=
  poseidon2_sbox_lane_map state

/-- The S-box `x^5` expressed as a dialect `mul`-chain denotes lane-wise to
    `x⁵`. We assemble `x² = mul x x`, `x⁴ = mul x² x²`, `x⁵ = mul x⁴ x`, all
    pointwise. -/
theorem sbox_via_dialect_mul_chain (v : VectorTy (BitVec 64) poseidon2LaneN) :
    (VectorTy.map₂ pmul
        (VectorTy.map₂ pmul (VectorTy.map₂ pmul v v) (VectorTy.map₂ pmul v v)) v)
      = (fun i => (v i * v i) * (v i * v i) * v i) := by
  funext i
  rfl

/-! ## 4. The Barrett fold as `shiftR` + `add` (reuse)

The fold step `hi = x >>> 31; lo = x & MM; x = hi·BBC + lo` reuses the dialect
`shiftR` (the `>>> 31`) and `add` (the final combine). The `& MM` mask and the
`· BBC` scalar multiply are lane-local scalar ops (the lane-spread). -/

/-- The dialect `shiftR` op carrying `pshr` denotes the per-lane Barrett-fold
    right shift — the `#VPSRL_4u64` of the fold step. -/
theorem fold_shr_denote (m : Nat) (v : VectorTy (BitVec 64) poseidon2LaneN) :
    denoteVectorOp (.shiftR pshr m v : VectorOp (BitVec 64) poseidon2LaneN)
      = .vec (fun i => v i >>> m) := rfl

/-! ## 5. The reused ops lower with proven preservation -/

/-- The Poseidon2 lane-bundle ops (`add` for the linear layer / RC-add / fold
    combine, `mul` for the S-box chain, `shiftR` for the fold shift) all lower
    to proven per-lane scalar expansions (the dialect lowering theorems at the
    Poseidon2 lane instance). -/
theorem poseidon2_ops_lower_correct (v w : VectorTy (BitVec 64) poseidon2LaneN) (m : Nat) :
    (lower (0 : BitVec 64) (.add padd v w)).map (·.denote)
        = some (VectorTy.map₂ padd v w)
      ∧ (lower (0 : BitVec 64) (.mul pmul v w)).map (·.denote)
        = some (VectorTy.map₂ pmul v w)
      ∧ (lower (0 : BitVec 64) (.shiftR pshr m v)).map (·.denote)
        = some (VectorTy.map₁imm pshr m v) := by
  exact ⟨ lower_add_correct (0 : BitVec 64) padd v w
        , lower_mul_correct (0 : BitVec 64) pmul v w
        , lower_shiftR_correct (0 : BitVec 64) pshr m v ⟩

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec
