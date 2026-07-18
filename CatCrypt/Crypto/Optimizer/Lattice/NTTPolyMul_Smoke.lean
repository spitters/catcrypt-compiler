/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul

/-!
# Pass 3.1 — NTT poly-mul rewrite smoke tests

Stage E: smoke-test that the `nttPolyMul` rewrite from
`CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul` produces the expected
syntactic outputs on concrete `LowCT` terms.  These are *purely
syntactic* checks (no semantics, no `LeafSpec`); they pin down the
shape of the rewriter as the consumer-facing contract.

Covers:
* ML-KEM specialisation rewriting `"poly_mul"` and `"polymul"` to
  `"ntt_poly_mul_3329_256"`.
* ML-DSA specialisation rewriting to `"ntt_poly_mul_8380417_256"`.
* Non-poly-mul names left untouched.
* Composite `RSeq` only touches the poly-mul leaf.
* Coverage for `RCallSwap` and `RCloneCall` branches.
* Name-generation `nttPolyMulName` round-trip.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul.Smoke

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul

/-! ## §1  Concrete `Located` / `TowerType` fixtures -/

/-- ML-KEM polynomial type: `TPolyMod 3329 256`. -/
private def aPolyTy : TowerType := .TPolyMod 3329 256

/-- A destination slot of polynomial type. -/
private def dstL : Located := ⟨"out", aPolyTy⟩

/-- First argument slot. -/
private def arg1 : Located := ⟨"a", aPolyTy⟩

/-- Second argument slot. -/
private def arg2 : Located := ⟨"b", aPolyTy⟩

/-- An auxiliary destination slot for the `RCallSwap` test. -/
private def dst2L : Located := ⟨"out2", aPolyTy⟩

/-- Old-destination location for the `RCloneCall` test. -/
private def odL : Located := ⟨"old", aPolyTy⟩

/-! ## §2  ML-KEM rewrites (q = 3329, n = 256) -/

/-- **(1)** `nttPolyMulMlkem` rewrites `RCall "poly_mul"` to
    `RCall "ntt_poly_mul_3329_256"`. -/
example :
    nttPolyMulMlkem (.RCall "poly_mul" dstL [arg1, arg2]) =
      .RCall "ntt_poly_mul_3329_256" dstL [arg1, arg2] := by
  rfl

/-- **(2)** `nttPolyMulMlkem` also rewrites the alternate spelling
    `"polymul"`. -/
example :
    nttPolyMulMlkem (.RCall "polymul" dstL [arg1, arg2]) =
      .RCall "ntt_poly_mul_3329_256" dstL [arg1, arg2] := by
  rfl

/-! ## §3  ML-DSA rewrites (q = 8380417, n = 256) -/

/-- **(3)** `nttPolyMulMldsa` rewrites `RCall "poly_mul"` to the
    ML-DSA leaf name `"ntt_poly_mul_8380417_256"`. -/
example :
    nttPolyMulMldsa (.RCall "poly_mul" dstL [arg1, arg2]) =
      .RCall "ntt_poly_mul_8380417_256" dstL [arg1, arg2] := by
  rfl

/-! ## §4  Non-poly-mul names are untouched -/

/-- **(4)** A call to an unrelated leaf (here `"other_name"`) is left
    structurally identical by the rewrite. -/
example :
    nttPolyMulMlkem (.RCall "other_name" dstL [arg1, arg2]) =
      .RCall "other_name" dstL [arg1, arg2] := by
  rfl

/-! ## §5  Composite `RSeq` — only the poly-mul leaf is rewritten -/

/-- **(5)** In an `RSeq` containing `poly_mul` followed by `poly_add`,
    only the `poly_mul` site is rewritten; `poly_add` is preserved. -/
example :
    nttPolyMulMlkem
        (.RSeq (.RCall "poly_mul" dstL [arg1, arg2])
               (.RCall "poly_add" dstL [arg1, arg2])) =
      .RSeq (.RCall "ntt_poly_mul_3329_256" dstL [arg1, arg2])
            (.RCall "poly_add" dstL [arg1, arg2]) := by
  rfl

/-! ## §6  `RCallSwap` branch coverage -/

/-- **(6)** `RCallSwap "poly_mul" d1 d2 args` is rewritten in place,
    exercising the `RCallSwap` arm of `nttPolyMul`. -/
example :
    nttPolyMulMlkem (.RCallSwap "poly_mul" dstL dst2L [arg1, arg2]) =
      .RCallSwap "ntt_poly_mul_3329_256" dstL dst2L [arg1, arg2] := by
  rfl

/-! ## §7  `RCloneCall` branch coverage -/

/-- **(7)** `RCloneCall cv ct od "poly_mul" dest args` rewrites only
    the inner leaf name, exercising the `RCloneCall` arm of
    `nttPolyMul`. -/
example :
    nttPolyMulMlkem
        (.RCloneCall "clone_var" aPolyTy odL "poly_mul" dstL [arg1, arg2]) =
      .RCloneCall "clone_var" aPolyTy odL "ntt_poly_mul_3329_256" dstL
        [arg1, arg2] := by
  rfl

/-! ## §8  Name generator -/

/-- **(8)** The generated leaf name for ML-KEM parameters is exactly
    `"ntt_poly_mul_3329_256"`. -/
example : nttPolyMulName 3329 256 = "ntt_poly_mul_3329_256" := by
  rfl

end CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul.Smoke
