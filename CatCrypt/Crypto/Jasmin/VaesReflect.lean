/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# VAES reflect surface — 2-way VAESENC / VAESDEC leaves through the verified front

This file is the AES-NI/VAES SIMD-extension analogue of `UovReflect.lean`:
it adds VAES-specific opaque leaves and `LowCTPattern` registrations so
that a pure-Lean 2-way AES round can be lifted through the verified
compiler chain `LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## VAES inner equation

`#VAESENC` (Intel SDM Vol. 2) is the EVEX-promotion of legacy AES-NI's
`#AESENC`: a single mnemonic runs one AES encryption round
(SubBytes ∘ ShiftRows ∘ MixColumns ∘ AddRoundKey) on each 128-bit lane
of an `ymm` (2-way) or `zmm` (4-way) register. Per-lane semantics is
the canonical AES round; no cross-lane mixing. The 2-way YMM variant is
the most-cited bench shape (it pairs naturally with VPCLMULQDQ for
AES-GCM and saves one MOVDQA per round vs. 2× `#AESENC`).

We model the 2-way fused VAESENC / VAESDEC at YMM width as opaque
leaves:

* `vaesenc_2way(state, rk) = (#VAESENC state rk)` lanewise over the two
  128-bit halves of state and rk — one EVEX-encoded VAESENC.

* `vaesdec_2way(state, rk) = (#VAESDEC state rk)` lanewise — same shape
  for the decryption round.

The 2-way packed shape (`TBytes 32`, two `u128` lanes ⇒ `memref 4`) is
the canonical ABI for VAES kernels (the Intel optimization guide's
"VAES + VPCLMULQDQ AES-GCM" reference body uses exactly this shape).

## Reflection→front gap (same as `UovReflect` / `FalconReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`, not the dynamic
`LowCTPattern` registry, so `reifyLowCT% vaesencLean` would error.
We follow the established pattern: define the pure-Lean function for
documentation, register each leaf via `@[rust_cmd_pattern]`, then
**hand-build the `LowCT`** the reifier *would* produce. Downstream
(`translate → cprogToJasminCom → emitAbiOrchRegPtr`) is the unmodified
verified front.

## LowCT-expressivity gap (documented)

`#VAESENC_256 / _512` are packed-lane SIMD intrinsics, not arithmetic
leaves in the sense `LowCT` already supports. We do **not** extend
`LowCT` itself: the leaves are registered like any other opaque leaf,
with the jasmin shim (`bench/aesgcm_compare/include/vaes_leaves.jinc`)
issuing the `#VAESENC_256` / `#VAESDEC_256` intrinsic at YMM width.
The verified front sees only the opaque leaf name and the TBytes
signature. The per-lane *semantics* — each 128-bit lane is one AES round
— is the hardware-leaf trust assumption, **factored and discharged** in
`CatCrypt.Crypto.SecureCompilation.X86Backend.HardwareISAAxioms`
(`HardwareISA.vaes`, tier `sailAnchored`): the per-lane round equals the
AES-NI round, pinned to the Sail-x86 `aesenc_spec`/`aesenclast_spec` on
the FIPS-197 known-answer block (`HardwareISA.aesNi_discharge`); the only
VAES-specific difference (the VEX/EVEX encoding) is byte-validated in
`X86Backend.CryptoExtValidation`.

## References

* Intel SDM Vol. 2 — `VAESENC`, `VAESDEC` (EVEX-encoded AES round)
* Intel Optimization Manual §13.5 — "VAES and VPCLMULQDQ AES-GCM"
  reference code (2-way YMM variant)
* NIST FIPS-197 §5.1 — AES round structure
* `bench/aesgcm_compare/aesgcm_vaes_emit.lean` — legacy Tier C string-
  templated emit (superseded by this leaf-shim pattern)
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling SIMD-leaf reference
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque VAES surface types

VAES at 2-way YMM operates on 256-bit packed registers: two 128-bit AES
states (or two round keys) per call. We encode one packed YMM operand
as `.TBytes 32` (`memref 4`, four `u64` limbs). -/

/-- A 2-way VAES packed operand: two 128-bit AES states (or two 128-bit
    round keys) packed into one YMM register. Opaque; concrete leaves
    implement the EVEX-encoded `#VAESENC_256` / `#VAESDEC_256`. -/
axiom Vaes2Block : Type
/-- Axiomatic inhabitant. -/ axiom Vaes2Block.default : Vaes2Block
noncomputable instance : Inhabited Vaes2Block := ⟨Vaes2Block.default⟩

/-! ## 2. VAES leaves (axioms = opaque jasmin function symbols) -/

/-- The 2-way VAES encryption round: `(state, rk) ↦ #VAESENC_256 state rk`
    lanewise over the two 128-bit halves of state and rk. Per-lane
    semantics is one AES encryption round (SubBytes ∘ ShiftRows ∘
    MixColumns ∘ AddRoundKey). Implemented by the jasmin shim issuing
    one `#VAESENC_256`. -/
axiom vaesenc_2way : Vaes2Block → Vaes2Block → Vaes2Block

/-- The 2-way VAES decryption round: `(state, rk) ↦ #VAESDEC_256 state rk`
    lanewise. Per-lane semantics is one AES decryption round
    (InvShiftRows ∘ InvSubBytes ∘ InvMixColumns ∘ AddRoundKey). -/
axiom vaesdec_2way : Vaes2Block → Vaes2Block → Vaes2Block

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `vaesenc_2way` → leaf `vaesenc_2way_256`. -/
@[rust_cmd_pattern]
def vaesEnc2WayPattern : LowCTPattern where
  name      := "vaesenc_2way_256"
  fnHead    := ``vaesenc_2way
  arity     := 2
  towerType := .TBytes 32   -- 2 × 128-bit packed lanes

/-- Register `vaesdec_2way` → leaf `vaesdec_2way_256`. -/
@[rust_cmd_pattern]
def vaesDec2WayPattern : LowCTPattern where
  name      := "vaesdec_2way_256"
  fnHead    := ``vaesdec_2way
  arity     := 2
  towerType := .TBytes 32   -- 2 × 128-bit packed lanes

/-! ## 4. VAES tower-type abbreviations -/

/-- Tower type of a 2-way VAES packed operand (`memref 4`). -/
def vaes2BlockTowerType : TowerType := .TBytes 32

private def loc (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean VAES kernels — the specs -/

/-- One 2-way VAES encryption round on packed state with packed round key. -/
noncomputable def vaesEnc2WayLean (state rk : Vaes2Block) : Vaes2Block :=
  vaesenc_2way state rk

/-- One 2-way VAES decryption round on packed state with packed round key. -/
noncomputable def vaesDec2WayLean (state rk : Vaes2Block) : Vaes2Block :=
  vaesdec_2way state rk

/-! ## 6. Hand-built `LowCT` bodies (the front-end input) -/

/-- The `LowCT` body for `vaesEnc2WayLean`. Shape:
    `RSeq RSkip (RCall "vaesenc_2way_256" __result [state, rk])`. -/
def vaesEnc2WayBody : LowCT :=
  let state_l  := loc "state"    vaes2BlockTowerType
  let rk_l     := loc "rk"       vaes2BlockTowerType
  let result_l := loc "__result" vaes2BlockTowerType
  .RSeq .RSkip
    (.RCall "vaesenc_2way_256" result_l [state_l, rk_l])

/-- `ReifiedFunc` bundle for the 2-way VAES encryption round. -/
def vaesEnc2WayReified : ReifiedFunc :=
  { args    := [("state", vaes2BlockTowerType), ("rk", vaes2BlockTowerType)]
    body    := vaesEnc2WayBody
    retName := "__result" }

/-- The `LowCT` body for `vaesDec2WayLean`. Shape:
    `RSeq RSkip (RCall "vaesdec_2way_256" __result [state, rk])`. -/
def vaesDec2WayBody : LowCT :=
  let state_l  := loc "state"    vaes2BlockTowerType
  let rk_l     := loc "rk"       vaes2BlockTowerType
  let result_l := loc "__result" vaes2BlockTowerType
  .RSeq .RSkip
    (.RCall "vaesdec_2way_256" result_l [state_l, rk_l])

/-- `ReifiedFunc` bundle for the 2-way VAES decryption round. -/
def vaesDec2WayReified : ReifiedFunc :=
  { args    := [("state", vaes2BlockTowerType), ("rk", vaes2BlockTowerType)]
    body    := vaesDec2WayBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval vaesEnc2WayReified.args.map Prod.fst              -- [state, rk]
#eval vaesEnc2WayReified.args.length                    -- 2
#eval vaesEnc2WayReified.retName                        -- __result
#eval vaesDec2WayReified.args.map Prod.fst              -- [state, rk]

end CatCrypt.Crypto.Jasmin.LowCTReflect
