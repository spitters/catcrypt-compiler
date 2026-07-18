/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# FAEST gf_dot_vec reflect surface — GF(2^128) PCLMUL Karatsuba dot through the verified front

This file is the FAEST-QuickSilver-VOLE SIMD-extension analogue of
`UovReflect.lean`: it adds a FAEST-gf_dot-specific opaque leaf and a
`LowCTPattern` registration so that a pure-Lean GF(2^128) dot-product
kernel can be lifted through the verified compiler chain
`LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## FAEST gf_dot_vec kernel

FAEST (Faster post-quantum signatures from VOLE-in-the-Head, Round 1
selected, NIST PQC Additional Signatures) uses GF(2^128) as the
arithmetic substrate for its QuickSilver / VOLE-in-the-Head check. The
hot kernel is a vector dot product over GF(2^128):

```
  out = Σ_{i=0}^{L-1} a_i · b_i    in GF(2^128)
```

where each `a_i`, `b_i` is a 128-bit element and `Σ` is XOR (the GF(2)
sum). The PCLMUL-Karatsuba implementation computes each `a_i · b_i` via
three `#PCLMULQDQ_128` invocations (Karatsuba's three half-products),
folds the half-products, accumulates into a 256-bit running sum, then
reduces modulo the FAEST GF(2^128) polynomial at the end.

We model the entire `gf_dot_vec` kernel as one opaque leaf. The
operands are vectors of 128-bit elements — we narrow to L = 8 (the
most-cited bench shape from `bench/faest_glue/`) so the operand types
are `TBytes 128` (8 × 16 bytes = 128 bytes = `memref 16`).

## Reflection→front gap (same as `UovReflect` / `FalconReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`. We follow the
established pattern.

## References

* FAEST v2.0 spec — §3.4 (QuickSilver check + GF(2^128) arithmetic)
* Karatsuba, "Multiplication of Multi-digit Numbers on Automata"
  (1962) — three-half-product multiplication
* Intel SDM Vol. 2 — `PCLMULQDQ` (carry-less multiply over GF(2))
* `bench/faest_glue/gf_dot_vec_emit.lean` — legacy Tier C string-
  templated emit (superseded by this leaf-shim pattern)
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling SIMD-leaf reference
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque FAEST gf_dot surface types

The vector operands are L = 8 × 16-byte GF(2^128) elements = 128 bytes
each. We encode as `.TBytes 128` (`memref 16`). The dot-product result
is a single GF(2^128) element = 16 bytes = `.TBytes 16` (`memref 2`). -/

/-- A length-8 vector of GF(2^128) elements (FAEST's standard inner-loop
    width). 128 bytes total. Opaque; the leaf `faest_gf_dot_vec` runs
    the PCLMUL-Karatsuba dot product. -/
axiom FaestGfVec8 : Type
/-- Axiomatic inhabitant. -/ axiom FaestGfVec8.default : FaestGfVec8
noncomputable instance : Inhabited FaestGfVec8 := ⟨FaestGfVec8.default⟩

/-- A single GF(2^128) element (the dot-product result). 16 bytes. -/
axiom FaestGf128 : Type
/-- Axiomatic inhabitant. -/ axiom FaestGf128.default : FaestGf128
noncomputable instance : Inhabited FaestGf128 := ⟨FaestGf128.default⟩

/-! ## 2. FAEST gf_dot leaves (axioms = opaque jasmin function symbols) -/

/-- The length-8 GF(2^128) dot product:
    `out = Σ_{i=0}^{7} a_i · b_i` in GF(2^128) (XOR-accumulated).
    Implemented by the jasmin shim issuing 8 × 3 = 24 `#PCLMULQDQ_128`
    invocations (Karatsuba's three half-products per pair), plus XOR
    folding and one final GF(2^128) reduction. -/
axiom faest_gf_dot_vec : FaestGfVec8 → FaestGfVec8 → FaestGf128

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `faest_gf_dot_vec` → leaf `faest_gf_dot_vec_l8`.
    The tower-type field carries the dest type (the GF(2^128) result),
    not the arg type (the L=8 vector). The args are `.TBytes 128`. -/
@[rust_cmd_pattern]
def faestGfDotVecPattern : LowCTPattern where
  name      := "faest_gf_dot_vec_l8"
  fnHead    := ``faest_gf_dot_vec
  arity     := 2
  towerType := .TBytes 16   -- single GF(2^128) result

/-! ## 4. FAEST gf_dot tower-type abbreviations -/

/-- Tower type of an L=8 GF(2^128) vector (`memref 16`). -/
def faestGfVec8TowerType : TowerType := .TBytes 128
/-- Tower type of a single GF(2^128) element (`memref 2`). -/
def faestGf128TowerType : TowerType := .TBytes 16

private def loc (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean FAEST gf_dot_vec kernel — the spec -/

/-- One length-8 GF(2^128) dot product. -/
noncomputable def faestGfDotVecLean (a b : FaestGfVec8) : FaestGf128 :=
  faest_gf_dot_vec a b

/-! ## 6. Hand-built `LowCT` body (the front-end input) -/

/-- The `LowCT` body for `faestGfDotVecLean`. Shape:
    `RSeq RSkip (RCall "faest_gf_dot_vec_l8" __result [a, b])`. -/
def faestGfDotVecBody : LowCT :=
  let a_l      := loc "a"        faestGfVec8TowerType
  let b_l      := loc "b"        faestGfVec8TowerType
  let result_l := loc "__result" faestGf128TowerType
  .RSeq .RSkip
    (.RCall "faest_gf_dot_vec_l8" result_l [a_l, b_l])

/-- `ReifiedFunc` bundle for the FAEST gf_dot_vec kernel. -/
def faestGfDotVecReified : ReifiedFunc :=
  { args    := [("a", faestGfVec8TowerType), ("b", faestGfVec8TowerType)]
    body    := faestGfDotVecBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval faestGfDotVecReified.args.map Prod.fst              -- [a, b]
#eval faestGfDotVecReified.args.length                    -- 2
#eval faestGfDotVecReified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
