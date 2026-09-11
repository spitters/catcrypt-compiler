/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types

/-!
# Step 4: the data-parallel lane carrier and the vector carrier coincide

The cleanest factoring routes vectorization, SIMD, and SIMT through ONE
data-parallel carrier. This file records that the `TileBackend`'s `Tile n w`
(the SIMT/GPU lane model, `bench/gpu_compare`) and the MLIR `VectorTy` (the CPU
SIMD lane model used by NEON / AVX-512 / RVV) are the *same* carrier
`Fin n → BitVec w`, and that the elementwise lane op IS the vector `map₂`. So
"vectorize", "pack into a SIMD register", and "fan out over GPU threads" are
three lowerings of one IR, not three carriers.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.TileVectorUnify

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel (Tile)
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect (VectorTy)

/-- **The lane carriers coincide.** The SIMT/GPU `Tile n w` and the CPU-SIMD
    `VectorTy (BitVec w) n` are definitionally the same `Fin n → BitVec w`. -/
theorem tile_eq_vectorTy (n w : Nat) : Tile n w = VectorTy (BitVec w) n := rfl

/-- **The elementwise lane op is the vector map.** Per-lane wrapping add over a
    `Tile`/`VectorTy` is exactly `VectorTy.map₂ (· + ·)` — the same datum whether
    you read it as a packed SIMD add, an RVV `vadd`, or a per-thread GPU add. -/
theorem lane_add_eq_map₂ {n w : Nat} (a b : Tile n w) :
    (fun i => a i + b i) = VectorTy.map₂ (· + ·) a b := rfl

/-- The same for multiply (the load-bearing field-lane op). -/
theorem lane_mul_eq_map₂ {n w : Nat} (a b : Tile n w) :
    (fun i => a i * b i) = VectorTy.map₂ (· * ·) a b := rfl

end CatCrypt.Crypto.SecureCompilation.TileBackend.TileVectorUnify
