/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# GHASH-VPCLMUL reflect surface — carry-less multiply leaf through the verified front

This file is the SIMD-extension analogue of `UovReflect.lean`: it adds a
GHASH-specific opaque leaf and a `LowCTPattern` registration so that a
pure-Lean GHASH inner kernel can be lifted through the verified compiler
chain `LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## GHASH inner equation

GHASH (NIST SP 800-38D §6.4) is the universal hash powering AES-GCM. The
inner kernel is one polynomial multiply over `GF(2^128)` defined by the
field polynomial `x^128 + x^7 + x^2 + x + 1`. The hot path is:

```
  Y_{i+1} = (Y_i ⊕ X_i) · H mod p(x)
```

The multiply step decomposes into one 128×128 carry-less multiply
producing a 256-bit intermediate, then one Montgomery-style reduction
back to 128 bits. The VPCLMULQDQ extension fuses the four 64×64
schoolbook half-products into two YMM-lane intrinsic calls, which is
the headline AES-GCM throughput win.

We model the fused 128×128 carry-less multiply (the half-product +
Karatsuba assembly + reduction) as one opaque leaf
`vpclmul_qdq_carryless_mul`. The verified front sees only the leaf name
and the tower-type signature; the SIMD intrinsic semantics
(per-`imm8`-half polynomial multiply) is pinned by the existing
`VPClmulEmit.vpclmulqdq_eq_polyMul` lane identity.

## Reflection→front gap (same as `UovReflect` / `FalconReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`, not the dynamic
`LowCTPattern` registry, so `reifyLowCT% ghashKernelLean` would error.
We follow the established pattern: define the pure-Lean function for
documentation, register each leaf in the `LowCTPattern` registry via
`@[rust_cmd_pattern]`, then **hand-build the `LowCT`** the reifier
*would* produce. Downstream (`translate → cryptoDialectToJasminCom →
emitAbiOrchRegPtr`) is the unmodified verified front.

## LowCT-expressivity gap (documented)

`#VPCLMULQDQ_128 / _256` is a packed-lane SIMD intrinsic, not an
arithmetic leaf in the sense `LowCT` already supports. We do **not**
extend `LowCT` itself: the leaf is registered like any other opaque
leaf, with the jasmin shim (`bench/aesgcm_compare/include/ghash_vpclmul_leaves.jinc`)
issuing the `#VPCLMULQDQ_128` intrinsic + the Karatsuba assembly +
reduction. The verified front sees only the opaque leaf name and the
TBytes signature; the per-lane intrinsic semantics is pinned by
`VPClmulEmit.vpclmulqdq_eq_polyMul`. The underlying hardware-leaf trust
assumption — that `PCLMULQDQ` computes the carry-less GF(2)[x] product —
is **factored and discharged** in
`CatCrypt.Crypto.SecureCompilation.X86Backend.HardwareISAAxioms`
(`HardwareISA.pclmul`, tier `sailAnchored`): owned `polyMul64` equals the
Sail-x86 `clmul64_spec` on GHASH-style known-answer vectors
(`HardwareISA.pclmul_discharge`).

## References

* NIST SP 800-38D §6.4 — GHASH definition + field polynomial
* Intel SDM Vol. 2 — `VPCLMULQDQ` (EVEX promotion of `PCLMULQDQ`)
* `CatCrypt/Crypto/SecureCompilation/VIR/VPClmulEmit.lean` — per-lane
  intrinsic semantics + `vpclmulqdq_eq_polyMul` bridge
* `bench/ghash_vpclmul_compare/ghash_vpclmul_emit.lean` — legacy Tier C
  string-templated emit (superseded by this leaf-shim pattern)
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling SIMD-leaf reference
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque GHASH surface types

GHASH operates on 16-byte (128-bit) blocks: the running tag `Y`, the
hash subkey `H`, and the input block `X` all share this shape. We
encode one block as `.TBytes 16` (`memref 2`, two `u64` limbs). -/

/-- A single 128-bit GHASH block (running tag, hash subkey, or input
    block). Opaque; concrete leaves implement the GF(2^128) field
    multiply via VPCLMULQDQ. -/
axiom GhashBlock : Type
/-- Axiomatic inhabitant. -/ axiom GhashBlock.default : GhashBlock
noncomputable instance : Inhabited GhashBlock := ⟨GhashBlock.default⟩

/-! ## 2. GHASH leaves (axioms = opaque jasmin function symbols) -/

/-- The fused 128×128 carry-less multiply over GF(2^128) with the AES-GCM
    field polynomial `x^128 + x^7 + x^2 + x + 1`. Implemented by the
    jasmin shim issuing four `#PCLMULQDQ_128`s (or two
    `#VPCLMULQDQ_256`s) plus the Karatsuba assembly and Montgomery-style
    reduction. The pure-Lean semantics is the GF(2^128) multiply itself;
    the SIMD intrinsic structure is documented in `VPClmulEmit`. -/
axiom vpclmul_qdq_carryless_mul : GhashBlock → GhashBlock → GhashBlock

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `vpclmul_qdq_carryless_mul` → leaf `ghash_vpclmul_mul128`. -/
@[rust_cmd_pattern]
def ghashVpclmulMul128Pattern : LowCTPattern where
  name      := "ghash_vpclmul_mul128"
  fnHead    := ``vpclmul_qdq_carryless_mul
  arity     := 2
  towerType := .TBytes 16   -- 128-bit block

/-! ## 4. GHASH tower-type abbreviations -/

/-- Tower type of a 128-bit GHASH block (`memref 2`). -/
def ghashBlockTowerType : TowerType := .TBytes 16

def locGhashVpclmul (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean GHASH inner kernel — the spec

Documentation only; the reifier doesn't consult this at lift time
(see "Reflection→front gap" above). The hand-built `LowCT` body
below mirrors this single leaf call one-for-one. -/

/-- GHASH inner kernel: one GF(2^128) multiply of the accumulator by the
    hash subkey. Repeated invocations build the full GHASH polynomial
    evaluation. -/
noncomputable def ghashKernelLean (y h : GhashBlock) : GhashBlock :=
  vpclmul_qdq_carryless_mul y h

/-! ## 6. Hand-built `LowCT` body (the front-end input) -/

/-- The `LowCT` body the reifier *would* produce for `ghashKernelLean`.
    Shape: `RSeq RSkip (RCall "ghash_vpclmul_mul128" __result [y, h])`. -/
def ghashKernelBody : LowCT :=
  let y_l      := locGhashVpclmul "y"        ghashBlockTowerType
  let h_l      := locGhashVpclmul "h"        ghashBlockTowerType
  let result_l := locGhashVpclmul "__result" ghashBlockTowerType
  .RSeq .RSkip
    (.RCall "ghash_vpclmul_mul128" result_l [y_l, h_l])

/-- `ReifiedFunc` bundle for the GHASH inner kernel. The bench driver
    consumes `.body` / `.retName` exactly as it would a `reifyLowCT%`
    output. -/
def ghashKernelReified : ReifiedFunc :=
  { args    := [("y", ghashBlockTowerType), ("h", ghashBlockTowerType)]
    body    := ghashKernelBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval ghashKernelReified.args.map Prod.fst              -- [y, h]
#eval ghashKernelReified.args.length                    -- 2
#eval ghashKernelReified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
