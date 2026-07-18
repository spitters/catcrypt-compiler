/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-!
# Keccak `ρ` step through the structured VectorDialect (task #275, pure reuse)

The Keccak `ρ` (rho) step rotates each of the 25 lanes by a per-lane constant
offset: `lane i ↦ (x <<< rotConst i) ||| (x >>> (64 - rotConst i))`. This is
**pure reuse** of the dialect alphabet — no new op needed:

* the per-lane left shift is `VectorOp.shiftL` carrying `(· <<< ·)`;
* the per-lane right shift is `VectorOp.shiftR` carrying `(· >>> ·)`;
* the `|||` combine is the generic binary `VectorOp.add` carrying `(· ||| ·)`.

The per-lane *varying* rotate offset (`rotConst i` differs per lane) is exactly
the `LaneMap.laneMapIdx` shape (a lane-INDEXED map). This file pins the Keccak
`ρ` lane meaning against the dialect shift/or ops and grounds its denotation in
the proven `LaneMap.keccak_rho_lane_map` keystone. All three ops lower with
proven denotation preservation (`lower_shiftL_correct`, `lower_shiftR_correct`,
`lower_add_correct`).

The existing Keccak emit (`VIR/KeccakEmit`) builds the `ρ`-step through the
typed `Com` IR (`emitRhoPiLane` / `emitRotL`), not via `List String`
rendering, so the natural reuse demonstrated here is at the DENOTATION level
(the dialect shift/or ops denote the same per-lane rotate the direct emit
realizes), not a byte-identity render proof. The Keccak emit module is left
**untouched**.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.KeccakRhoVec

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap (keccak_rho_lane_map keccakRotStub laneMapIdx laneMapIdx_eq_scalar)

/-! ## 1. Keccak lane shape: 25 lanes of `BitVec 64`. -/

/-- The Keccak state lane count (5×5 lanes). -/
abbrev keccakLaneN : Nat := 25

/-- The 64-bit lane shift-left op (`#VPSLLQ`-shape, here per-lane scalar). -/
abbrev keccakShl (x : BitVec 64) (m : Nat) : BitVec 64 := x <<< m
/-- The 64-bit lane shift-right op (`#VPSRLQ`-shape). -/
abbrev keccakShr (x : BitVec 64) (m : Nat) : BitVec 64 := x >>> m
/-- The 64-bit lane bitwise-or (`#VPOR`-shape). -/
abbrev keccakOr (x y : BitVec 64) : BitVec 64 := x ||| y

/-! ## 2. One `ρ`-rotate lane expressed via the dialect shift/or ops

For a fixed rotate amount `n`, the rotate-left on a 64-bit lane is
`(x <<< n) ||| (x >>> (64 - n))` — the dialect `add`-carrying-or of the two
shift halves. -/

/-- The per-lane rotate-left at a fixed amount `n`, expressed through the
    dialect shift/or ops, equals the direct `BitVec` rotate. -/
theorem rho_lane_via_dialect (v : VectorTy (BitVec 64) keccakLaneN) (n : Nat) :
    denoteVectorOp (.add keccakOr
        (VectorTy.map₁imm keccakShl n v)
        (VectorTy.map₁imm keccakShr (64 - n) v) : VectorOp (BitVec 64) keccakLaneN)
      = .vec (fun i => (v i <<< n) ||| (v i >>> (64 - n))) := rfl

/-! ## 3. The full `ρ` step (per-lane VARYING offset) via `laneMapIdx`

The 25 lanes each rotate by a different `rotConst i`. That lane-indexed map is
`LaneMap.laneMapIdx`, and the proven `keccak_rho_lane_map` keystone says the
packed (SIMD) form equals the scalar per-lane sequential form. -/

/-- **The Keccak `ρ` lane-indexed rotate equals its scalar per-lane form.** The
    dialect shift/or alphabet realizes each lane's rotate (`rho_lane_via_dialect`
    at the per-lane amount `rotConst i`); the lane-varying offset table is the
    `laneMapIdx` shape closed by the proven keystone. -/
theorem rho_denotation_preserves (rotConst : Fin keccakLaneN → Nat)
    (state : VectorTy (BitVec 64) keccakLaneN) :
    keccakRotStub rotConst state =
      (fun i => (state i) <<< (rotConst i) ||| (state i) >>> (64 - rotConst i)) :=
  keccak_rho_lane_map rotConst state

/-! ## 4. The reused ops lower with proven preservation -/

/-- The `ρ`-step shift/or ops all lower to proven per-lane scalar expansions
    (the dialect keystones `lower_shiftL_correct` / `lower_shiftR_correct` /
    `lower_add_correct` at the Keccak lane instance). -/
theorem rho_ops_lower_correct (v : VectorTy (BitVec 64) keccakLaneN) (n : Nat) :
    (lower (0 : BitVec 64) (.shiftL keccakShl n v)).map (·.denote)
        = some (VectorTy.map₁imm keccakShl n v)
      ∧ (lower (0 : BitVec 64) (.shiftR keccakShr (64 - n) v)).map (·.denote)
        = some (VectorTy.map₁imm keccakShr (64 - n) v)
      ∧ (lower (0 : BitVec 64) (.add keccakOr
            (VectorTy.map₁imm keccakShl n v) (VectorTy.map₁imm keccakShr (64 - n) v))).map (·.denote)
        = some (VectorTy.map₂ keccakOr
            (VectorTy.map₁imm keccakShl n v) (VectorTy.map₁imm keccakShr (64 - n) v)) :=
  ⟨ lower_shiftL_correct (0 : BitVec 64) keccakShl n v
  , lower_shiftR_correct (0 : BitVec 64) keccakShr (64 - n) v
  , lower_add_correct (0 : BitVec 64) keccakOr _ _ ⟩

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.KeccakRhoVec
