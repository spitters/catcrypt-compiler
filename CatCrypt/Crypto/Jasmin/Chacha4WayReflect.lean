/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# ChaCha 4-way (XMM-resident) reflect surface — through the verified front

This file is the ChaCha-AVX SIMD-extension analogue of `UovReflect.lean`:
it adds a ChaCha-4way-specific opaque leaf and a `LowCTPattern`
registration so that a pure-Lean ChaCha20 4-way block kernel can be
lifted through the verified compiler chain `LowCT → catCryptDialect → Com →
jasmin`, **without** editing `LowCTReflect.lean`'s `knownOps` table.

## ChaCha 4-way kernel

The ChaCha20 4-way XMM-resident block kernel processes four ChaCha20
blocks in parallel using the SSE2/SSSE3 SIMD lanes. Each block has 16
32-bit state words `s[0..16]`; four parallel blocks pack into 16 XMM
registers (one per state-word index, four lanes per register). The
kernel runs the canonical 20-round (10 double-round) ChaCha20 schedule
on the packed state with `#VPSHUFB_128` / `#VPSLLD_128` / `#VPADD_4u32`,
then XORs the keystream output with the plaintext.

We model this entire 4-block kernel as one opaque leaf
`chacha_4way_xmm_block`. The input is the packed 4-block state (4 × 64
bytes = 256 bytes = `TBytes 256`); the output is the packed 4-block
keystream (also `TBytes 256`). The verified front sees only the opaque
leaf name and the TBytes signature; the per-round semantics is RFC 8439
§2.3 and pinned by the existing single-block ChaCha emit
(`bench/chacha_compare/chacha_emit.lean`).

## Reflection→front gap (same as `UovReflect` / `FalconReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`. We follow the
established pattern: define the pure-Lean function for documentation,
register the leaf via `@[rust_cmd_pattern]`, then **hand-build the
`LowCT`** the reifier *would* produce.

## LowCT-expressivity gap (documented)

ChaCha's XMM-resident permutation runs 320 SIMD ops (20 rounds × 4
quarter-rounds × 4 sub-ops per QR) per block; the entire schedule is a
straight-line invocation of `#VPADD_4u32` / `#VPXOR_128` /
`#VPSHUFB_128`. Wrapping the entire kernel as one opaque leaf preserves
the perf because the leaf body is straight-line (no per-call orchestration
cost — the verified front emits ~2 register movs for the wrapper). The
string-templated XMM-resident emit
(`bench/chacha_compare/chacha_4way_xmm_emit.lean`) has the same byte-level
shape; this reflect surface lifts it through the verified front.

## References

* RFC 8439 §2.3 — ChaCha20 block / quarter-round / double-round
* `bench/chacha_compare/chacha_emit.lean` — sibling single-block
  Com (verified emit on hand-built Com)
* `bench/chacha_compare/chacha_4way_xmm_emit.lean` —
  string-templated 4-way emit
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling SIMD-leaf reference
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque ChaCha-4way surface types

ChaCha 4-way XMM-resident operates on a 4 × 16 × 32-bit packed state
(four parallel ChaCha20 blocks). The full 256-byte packed state encodes
as `.TBytes 256` (`memref 32`, 32 × `u64` limbs). -/

opaque Chacha4WayState.Impl : NonemptyType.{0}
/-- A packed 4-way ChaCha20 state: four parallel 64-byte ChaCha blocks
    packed into 16 XMM registers (lane k of register i holds state word
    i of block k). 256 bytes total. Opaque; the leaf
    `chacha_4way_xmm_block` runs the canonical 20-round schedule. -/
def Chacha4WayState : Type := Chacha4WayState.Impl.type
instance : Nonempty Chacha4WayState := Chacha4WayState.Impl.property
/-- Axiomatic inhabitant. -/ axiom Chacha4WayState.default : Chacha4WayState
noncomputable instance : Inhabited Chacha4WayState := ⟨Chacha4WayState.default⟩

/-! ## 2. ChaCha-4way leaves (opaque constants = jasmin function symbols) -/

/-- The 4-way ChaCha20 block kernel: run 20 rounds (10 double-rounds) on
    the packed 4-block state, return the packed 4-block keystream
    (= initial state + final state, per RFC 8439 §2.3). Implemented by
    the jasmin shim issuing 320 SIMD ops (the canonical XMM-resident
    body, see `bench/chacha_compare/chacha_4way_xmm_emit.lean` for the
    explicit op sequence). -/
noncomputable opaque chacha_4way_xmm_block : Chacha4WayState → Chacha4WayState

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `chacha_4way_xmm_block` → leaf `chacha_4way_xmm_block`. -/
@[rust_cmd_pattern]
def chacha4WayXmmBlockPattern : LowCTPattern where
  name      := "chacha_4way_xmm_block"
  fnHead    := ``chacha_4way_xmm_block
  arity     := 1
  towerType := .TBytes 256

/-! ## 4. ChaCha-4way tower-type abbreviation -/

/-- Tower type of a packed 4-way ChaCha state (`memref 32`). -/
def chacha4WayStateTowerType : TowerType := .TBytes 256

def locChacha4Way (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean ChaCha-4way kernel — the spec -/

/-- One 4-way ChaCha20 block: 20 rounds + final-state add over the
    packed 4-block state. -/
noncomputable def chacha4WayXmmBlockLean (s : Chacha4WayState) : Chacha4WayState :=
  chacha_4way_xmm_block s

/-! ## 6. Hand-built `LowCT` body (the front-end input) -/

/-- The `LowCT` body for `chacha4WayXmmBlockLean`. Shape:
    `RSeq RSkip (RCall "chacha_4way_xmm_block" __result [s])`. -/
def chacha4WayXmmBlockBody : LowCT :=
  let s_l      := locChacha4Way "s"        chacha4WayStateTowerType
  let result_l := locChacha4Way "__result" chacha4WayStateTowerType
  .RSeq .RSkip
    (.RCall "chacha_4way_xmm_block" result_l [s_l])

/-- `ReifiedFunc` bundle for the 4-way ChaCha20 XMM block kernel. -/
def chacha4WayXmmBlockReified : ReifiedFunc :=
  { args    := [("s", chacha4WayStateTowerType)]
    body    := chacha4WayXmmBlockBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval chacha4WayXmmBlockReified.args.map Prod.fst              -- [s]
#eval chacha4WayXmmBlockReified.args.length                    -- 1
#eval chacha4WayXmmBlockReified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
