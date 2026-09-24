/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# AES-bitslice reflect surface — 32-block-wide AES round through the verified front

This file is the bitsliced-AES SIMD-extension analogue of
`UovReflect.lean`: it adds AES-bitslice-specific opaque leaves and
`LowCTPattern` registrations so that a pure-Lean 32-block-wide AES
round can be lifted through the verified compiler chain
`LowCT → catCryptDialect → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## AES-bitslice equation

The constant-time AES-bitslice technique (Käsper-Schwabe 2009, Knebl
2017) treats each AES state bit as one slot of an SIMD register, then
runs 32 AES blocks in parallel by processing one bit-position at a time
across all 32 blocks. Per-round semantics:

* `SubBytes` — one bit-sliced S-box via 113 boolean ops per S-box
  (Boyar-Peralta circuit), parallel across all 32 blocks.
* `ShiftRows` — register-level permutation (32-way: each register holds
  the i-th bit of state byte k for all 32 blocks).
* `MixColumns` — XOR-tree across the 32 packed-state registers.
* `AddRoundKey` — packed XOR with the round-key bit-slice.

The 32-block-wide AES round is the kernel; the bench measures throughput
(bytes/cycle for 32×16 = 512 bytes per round).

We model the entire 32-block AES round as one opaque leaf
`aes_bitslice_round32`. Input: packed 32-block state (32 × 16 bytes =
512 bytes = `TBytes 512`); packed round key (also `TBytes 512`). Output:
packed 32-block state. The verified front sees only the opaque leaf
name and the TBytes signature; the bitsliced-round semantics is pinned
by the existing AES bitslice KAT (NIST FIPS-197 round-by-round
intermediate values).

## Reflection→front gap (same as `UovReflect` / `FalconReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`. We follow the
established pattern.

## References

* Käsper-Schwabe, "Faster and Timing-Attack Resistant AES-GCM" (CHES 2009)
* Boyar-Peralta, "A New Combinational Logic Minimization Technique"
  (WEA 2010) — 113-op S-box
* NIST FIPS-197 §5 — AES round
* `bench/aes_compare/aes_bitslice_emit.lean` — the string-templated
  emit of the same round
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling SIMD-leaf reference
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque AES-bitslice surface types

AES-bitslice at 32-way operates on 32 × 16 = 512-byte packed states
(one state byte k holds the (k-th) bit of all 128 AES state bits across
all 32 blocks). We encode as `.TBytes 512` (`memref 64`). -/

/-- A 32-block-wide packed AES state (or round key): 32 × 16 = 512
    bytes. Opaque; the leaf `aes_bitslice_round32` runs the canonical
    bitsliced AES round. -/
axiom AesBitslice32 : Type
/-- Axiomatic inhabitant. -/ axiom AesBitslice32.default : AesBitslice32
noncomputable instance : Inhabited AesBitslice32 := ⟨AesBitslice32.default⟩

/-! ## 2. AES-bitslice leaves (axioms = opaque jasmin function symbols) -/

/-- The 32-block-wide bitsliced AES encryption round:
    `(state, rk) ↦ AddRoundKey(MixColumns(ShiftRows(SubBytes state)), rk)`
    in bitsliced form, running 32 AES blocks in parallel.
    Implemented by the jasmin shim issuing the Boyar-Peralta S-box +
    ShiftRows permutation + MixColumns XOR-tree + AddRoundKey. -/
axiom aes_bitslice_round32 : AesBitslice32 → AesBitslice32 → AesBitslice32

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `aes_bitslice_round32` → leaf `aes_bitslice_round32`. -/
@[rust_cmd_pattern]
def aesBitsliceRound32Pattern : LowCTPattern where
  name      := "aes_bitslice_round32"
  fnHead    := ``aes_bitslice_round32
  arity     := 2
  towerType := .TBytes 512   -- 32 × 16-byte packed state

/-! ## 4. AES-bitslice tower-type abbreviation -/

/-- Tower type of a 32-block packed AES state (`memref 64`). -/
def aesBitslice32TowerType : TowerType := .TBytes 512

def locAesBitslice (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean AES-bitslice kernel — the spec -/

/-- One 32-block-wide bitsliced AES round on packed state with packed
    round key. -/
noncomputable def aesBitsliceRound32Lean (state rk : AesBitslice32) : AesBitslice32 :=
  aes_bitslice_round32 state rk

/-! ## 6. Hand-built `LowCT` body (the front-end input) -/

/-- The `LowCT` body for `aesBitsliceRound32Lean`. Shape:
    `RSeq RSkip (RCall "aes_bitslice_round32" __result [state, rk])`. -/
def aesBitsliceRound32Body : LowCT :=
  let state_l  := locAesBitslice "state"    aesBitslice32TowerType
  let rk_l     := locAesBitslice "rk"       aesBitslice32TowerType
  let result_l := locAesBitslice "__result" aesBitslice32TowerType
  .RSeq .RSkip
    (.RCall "aes_bitslice_round32" result_l [state_l, rk_l])

/-- `ReifiedFunc` bundle for the 32-block-wide bitsliced AES round. -/
def aesBitsliceRound32Reified : ReifiedFunc :=
  { args    := [("state", aesBitslice32TowerType),
                ("rk",    aesBitslice32TowerType)]
    body    := aesBitsliceRound32Body
    retName := "__result" }

/-! ## 7. Inspection -/

#eval aesBitsliceRound32Reified.args.map Prod.fst              -- [state, rk]
#eval aesBitsliceRound32Reified.args.length                    -- 2
#eval aesBitsliceRound32Reified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
