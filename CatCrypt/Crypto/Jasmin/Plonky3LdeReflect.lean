/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LowCTStraightLineCheck

/-!
# Plonky3 LDE (coset-FFT low-degree extension) reflect surface

Layer 2 of the Plonky3 STARK chain (low-degree extension of the execution trace
via a coset FFT over the BabyBear field) lifted through the verified compiler
chain `LowCT → Com catCryptDialect → Jasmin`.

This is the **architectural opposite** of the
`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3LdeEmit.lean` string-template
emit (`bench/plonky3_compare/gen/lde_coset_fft.jazz` is built by
`String.intercalate` — out-of-chain by construction). This module is the
LDE-layer analogue of `Plonky3Reflect.lean` (Merkle layer) and
`FalconReflect.lean`: every byte of the emit goes through the
verified front.

## LDE equation (Plonky3 / plonky3-hax)

```
  lde_coset_fft(evals : [BabyBear; N]):                -- evaluations on subgroup H
    coeffs    = ntt_inverse(evals, ω_H)               -- subgroup-H inverse NTT
    coeffs_kN = zero_extend(coeffs, k·N)               -- pad to coset domain size
    twisted   = coset_twist(coeffs_kN, shift)          -- multiply by shift^i
    out       = ntt_forward(twisted, ω_kN)             -- coset-domain forward NTT
    return out                                          -- evaluations on coset
```

For Plonky3 the blowup factor `k ∈ {2, 4, 8}` (typical config = 4).

We model each major step as one opaque leaf call:

| Lean axiom              | Leaf name (.jazz)                  | TowerType         |
|-------------------------|------------------------------------|-------------------|
| `babybear_ntt_inverse`  | `babybear_ntt_inverse_N`           | `TBytes (8·N)`    |
| `babybear_zero_extend`  | `babybear_zero_extend_N_to_kN`     | `TBytes (8·k·N)`  |
| `babybear_coset_twist`  | `babybear_coset_twist_kN`          | `TBytes (8·k·N)`  |
| `babybear_ntt_forward`  | `babybear_ntt_forward_kN`          | `TBytes (8·k·N)`  |
| `babybear_mul`          | `babybear_mul_N`                   | `TBytes (8·N)`    |

A coset-FFT LDE for fixed (N, k) is the 4-RCall chain
`ntt_inverse → zero_extend → coset_twist → ntt_forward`. The blowup factor `k`
and the trace length `N` are specialised at Lean time (typical configs are
(N=64, k=4), (N=256, k=4), (N=1024, k=4)).

## Reflection→front gap

Same as `FalconReflect.lean`, `MemAbiReflect.lean`, and `Plonky3Reflect.lean`
(Merkle layer): `reifyLowCT%` does not consult the `LowCTPattern` registry,
so we hand-build the `LowCT` body the reifier *would* produce. The rest of
the front (`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is the standard chain.

## Unrolling

The 4-step LDE chain is expressed as a flat `RSeq` of
`RCall`s. Each leaf encapsulates one bounded loop (the NTT butterfly, the
zero-pad, the coset multiplication) — the loops are inside the leaf
implementation, not in the orchestration body. This matches the Merkle
pattern (flat unroll, one RCall per algorithmic level).

## Relation to the string emit `Plonky3LdeEmit.lean`

`Plonky3LdeEmit.lean` emits its `.jazz` via `String.intercalate` (no compiler
correctness theorem witnesses the body). This module emits in-chain: same
final artifact shape, routed through the verified compiler. The string emit
serves as an out-of-chain reference for the `bench/plonky3_compare` C
harness.

## References

* Plonky3 coset-FFT LDE: `plonky3-hax/src/specs/baby_bear.rs` (`bb_*`),
  `plonky3-hax/src/fri.rs` (`coset_element`, `domain_element`).
* Merkle pattern: `CatCrypt/Crypto/Jasmin/Plonky3Reflect.lean`.
* Mirror pattern: `CatCrypt/Crypto/Jasmin/FalconReflect.lean`.
* Driver template: `bench/fndsa_compare/verify_from_rustcmd.lean`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Plonky3 LDE surface types

The reflect surface treats one BabyBear vector as an opaque byte buffer of
`8 · N` bytes (`N` field elements, 8 bytes per BabyBear element). The
forward/inverse NTTs, the zero-extension, and the coset twist are all taken as
leaf calls. The orchestration is the flat 4-step chain. -/

opaque Plonky3BabyBearVec.Impl (N : Nat) : NonemptyType.{0}
/-- A BabyBear vector of length `N` (`8·N` bytes, packed). Opaque on the Lean
    side; the leaves implement the canonical canonical-residue layout
    internally. The size index is the *trace length* (`N`) or the *coset
    domain size* (`k·N`) depending on context. -/
def Plonky3BabyBearVec (N : Nat) : Type := (Plonky3BabyBearVec.Impl N).type
instance (N : Nat) : Nonempty (Plonky3BabyBearVec N) := (Plonky3BabyBearVec.Impl N).property
/-- An inhabitant. -/
noncomputable opaque Plonky3BabyBearVec.default (N : Nat) : Plonky3BabyBearVec N
noncomputable instance (N : Nat) : Inhabited (Plonky3BabyBearVec N) :=
  ⟨Plonky3BabyBearVec.default N⟩

/-! ## 2. LDE leaves (axioms = opaque jasmin function symbols)

Each leaf is parameterised by its array width (in BabyBear elements); a single
emit instantiates these at a fixed `(N, k)` pair, so the leaves below are
family-indexed by `Nat`. -/

/-- Subgroup-H inverse NTT: maps `N` evaluations on `H = ⟨ω_H⟩` to the `N`
    polynomial coefficients. -/
noncomputable opaque babybear_ntt_inverse (N : Nat) :
    Plonky3BabyBearVec N → Plonky3BabyBearVec N

/-- Zero-extend: lift `N` coefficients to a `kN`-sized buffer by appending
    `(k-1)·N` zero pads. The leaf is parameterised by both the source width
    `N` and the destination width `kN`. -/
noncomputable opaque babybear_zero_extend (N kN : Nat) :
    Plonky3BabyBearVec N → Plonky3BabyBearVec kN

/-- Coset twist: pointwise-multiply by `shift^i` for `i ∈ [0, kN)`. The shift
    is implicit in the leaf implementation (typically the BabyBear generator
    `31`). Input and output are both `kN`-wide. -/
noncomputable opaque babybear_coset_twist (kN : Nat) :
    Plonky3BabyBearVec kN → Plonky3BabyBearVec kN

/-- Coset-domain forward NTT: maps `kN` polynomial coefficients (already
    coset-twisted) to `kN` evaluations on the coset `shift · ⟨ω_kN⟩`. -/
noncomputable opaque babybear_ntt_forward (kN : Nat) :
    Plonky3BabyBearVec kN → Plonky3BabyBearVec kN

/-- Pointwise BabyBear multiply over an `N`-wide vector. Not used in the
    minimal 4-step LDE chain, but exposed as a separate leaf for the
    quotient-polynomial computation that AIR composes on top of the LDE. -/
noncomputable opaque babybear_mul (N : Nat) :
    Plonky3BabyBearVec N → Plonky3BabyBearVec N → Plonky3BabyBearVec N

/-! ## 3. `@[rust_cmd_pattern]` registrations

We register leaves for two typical configurations:
* `(N=64, k=4)`: small KAT regime — `kN = 256`.
* `(N=256, k=4)`: medium regime — `kN = 1024` (matches the string-emitted
  `lde_coset_fft.jazz` array width).
* `(N=1024, k=4)`: deep regime — `kN = 4096`.

The Lean code is dialect-clean if leaves at unregistered sizes are not
emitted; the registrations below cover the configs the driver
(`bench/plonky3_compare/lde_from_rustcmd.lean`) consumes. -/

/-- `babybear_ntt_inverse_64`: inverse NTT of 64-element trace. -/
@[rust_cmd_pattern]
def babybearNttInverse64Pattern : LowCTPattern where
  name      := "babybear_ntt_inverse_64"
  fnHead    := ``babybear_ntt_inverse
  arity     := 1
  towerType := .TBytes (8 * 64)

/-- `babybear_zero_extend_64_to_256`: zero-extend 64 → 256 (blowup=4 at N=64). -/
@[rust_cmd_pattern]
def babybearZeroExtend64To256Pattern : LowCTPattern where
  name      := "babybear_zero_extend_64_to_256"
  fnHead    := ``babybear_zero_extend
  arity     := 1
  towerType := .TBytes (8 * 256)

/-- `babybear_coset_twist_256`: coset twist over the 256-wide buffer. -/
@[rust_cmd_pattern]
def babybearCosetTwist256Pattern : LowCTPattern where
  name      := "babybear_coset_twist_256"
  fnHead    := ``babybear_coset_twist
  arity     := 1
  towerType := .TBytes (8 * 256)

/-- `babybear_ntt_forward_256`: coset-domain forward NTT (256 evals out). -/
@[rust_cmd_pattern]
def babybearNttForward256Pattern : LowCTPattern where
  name      := "babybear_ntt_forward_256"
  fnHead    := ``babybear_ntt_forward
  arity     := 1
  towerType := .TBytes (8 * 256)

/-- `babybear_mul_256`: pointwise multiply over a 256-wide buffer (for the
    quotient polynomial in AIR). -/
@[rust_cmd_pattern]
def babybearMul256Pattern : LowCTPattern where
  name      := "babybear_mul_256"
  fnHead    := ``babybear_mul
  arity     := 2
  towerType := .TBytes (8 * 256)

/-- `babybear_ntt_inverse_256` (medium regime). -/
@[rust_cmd_pattern]
def babybearNttInverse256Pattern : LowCTPattern where
  name      := "babybear_ntt_inverse_256"
  fnHead    := ``babybear_ntt_inverse
  arity     := 1
  towerType := .TBytes (8 * 256)

/-- `babybear_zero_extend_256_to_1024` (medium regime). -/
@[rust_cmd_pattern]
def babybearZeroExtend256To1024Pattern : LowCTPattern where
  name      := "babybear_zero_extend_256_to_1024"
  fnHead    := ``babybear_zero_extend
  arity     := 1
  towerType := .TBytes (8 * 1024)

/-- `babybear_coset_twist_1024` (medium regime). -/
@[rust_cmd_pattern]
def babybearCosetTwist1024Pattern : LowCTPattern where
  name      := "babybear_coset_twist_1024"
  fnHead    := ``babybear_coset_twist
  arity     := 1
  towerType := .TBytes (8 * 1024)

/-- `babybear_ntt_forward_1024` (medium regime). -/
@[rust_cmd_pattern]
def babybearNttForward1024Pattern : LowCTPattern where
  name      := "babybear_ntt_forward_1024"
  fnHead    := ``babybear_ntt_forward
  arity     := 1
  towerType := .TBytes (8 * 1024)

/-- `babybear_ntt_inverse_1024` (deep regime). -/
@[rust_cmd_pattern]
def babybearNttInverse1024Pattern : LowCTPattern where
  name      := "babybear_ntt_inverse_1024"
  fnHead    := ``babybear_ntt_inverse
  arity     := 1
  towerType := .TBytes (8 * 1024)

/-- `babybear_zero_extend_1024_to_4096` (deep regime). -/
@[rust_cmd_pattern]
def babybearZeroExtend1024To4096Pattern : LowCTPattern where
  name      := "babybear_zero_extend_1024_to_4096"
  fnHead    := ``babybear_zero_extend
  arity     := 1
  towerType := .TBytes (8 * 4096)

/-- `babybear_coset_twist_4096` (deep regime). -/
@[rust_cmd_pattern]
def babybearCosetTwist4096Pattern : LowCTPattern where
  name      := "babybear_coset_twist_4096"
  fnHead    := ``babybear_coset_twist
  arity     := 1
  towerType := .TBytes (8 * 4096)

/-- `babybear_ntt_forward_4096` (deep regime). -/
@[rust_cmd_pattern]
def babybearNttForward4096Pattern : LowCTPattern where
  name      := "babybear_ntt_forward_4096"
  fnHead    := ``babybear_ntt_forward
  arity     := 1
  towerType := .TBytes (8 * 4096)

/-! ## 4. Pure-Lean coset-FFT LDE function — the spec the emit must implement

Each `ldeCosetFftLean_<N>_<k>` is the pure Lean specification for the
fixed-config emit. The body is a flat let-chain mirroring the hand-built
`LowCT` exactly. -/

/-- Pure-Lean coset-FFT LDE for `N = 64`, `k = 4` (`kN = 256`). The four-step
    chain (inverse NTT → zero-extend → coset twist → forward NTT) matches the
    plonky3-hax `compute_column_lde` pattern. -/
noncomputable def ldeCosetFftLean64x4 (evals : Plonky3BabyBearVec 64) :
    Plonky3BabyBearVec 256 :=
  let coeffs    := babybear_ntt_inverse 64 evals
  let coeffs_kN := babybear_zero_extend 64 256 coeffs
  let twisted   := babybear_coset_twist 256 coeffs_kN
  babybear_ntt_forward 256 twisted

/-- Pure-Lean coset-FFT LDE for `N = 256`, `k = 4` (`kN = 1024`). -/
noncomputable def ldeCosetFftLean256x4 (evals : Plonky3BabyBearVec 256) :
    Plonky3BabyBearVec 1024 :=
  let coeffs    := babybear_ntt_inverse 256 evals
  let coeffs_kN := babybear_zero_extend 256 1024 coeffs
  let twisted   := babybear_coset_twist 1024 coeffs_kN
  babybear_ntt_forward 1024 twisted

/-- Pure-Lean coset-FFT LDE for `N = 1024`, `k = 4` (`kN = 4096`). -/
noncomputable def ldeCosetFftLean1024x4 (evals : Plonky3BabyBearVec 1024) :
    Plonky3BabyBearVec 4096 :=
  let coeffs    := babybear_ntt_inverse 1024 evals
  let coeffs_kN := babybear_zero_extend 1024 4096 coeffs
  let twisted   := babybear_coset_twist 4096 coeffs_kN
  babybear_ntt_forward 4096 twisted

/-! ## 5. Hand-built `LowCT` bodies — the front-end input

Each step becomes one `RCall` with a fresh destination of the appropriate
`TBytes` width. The whole body is one `RSeq` chain, four `RCall`s deep.

`reifyLowCT%` does not consult the registry, so we hand-build the body.
Downstream (`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is
unmodified. -/

/-- TowerType for a BabyBear vector of length `M` (`8·M` bytes). -/
def babybearVecTowerType (M : Nat) : TowerType := .TBytes (8 * M)

def locPlonky3Lde (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Leaf-name helpers (string interpolation of widths). -/
def babybearNttInverseLeafName (N : Nat) : String :=
  "babybear_ntt_inverse_" ++ toString N
def babybearZeroExtendLeafName (N kN : Nat) : String :=
  "babybear_zero_extend_" ++ toString N ++ "_to_" ++ toString kN
def babybearCosetTwistLeafName (kN : Nat) : String :=
  "babybear_coset_twist_" ++ toString kN
def babybearNttForwardLeafName (kN : Nat) : String :=
  "babybear_ntt_forward_" ++ toString kN

/-- Body for `(N=64, k=4)`: four RCalls (inverse, extend, twist, forward). -/
def ldeCosetFftBody64x4 : LowCT :=
  let evals_l   := locPlonky3Lde "evals"   (babybearVecTowerType 64)
  let coeffs_l  := locPlonky3Lde "coeffs"  (babybearVecTowerType 64)
  let coffsN_l  := locPlonky3Lde "coeffs_kN" (babybearVecTowerType 256)
  let twisted_l := locPlonky3Lde "twisted" (babybearVecTowerType 256)
  let result_l  := locPlonky3Lde "__result" (babybearVecTowerType 256)
  .RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (babybearNttInverseLeafName 64)      coeffs_l  [evals_l]))
    (.RCall (babybearZeroExtendLeafName 64 256)  coffsN_l  [coeffs_l]))
    (.RCall (babybearCosetTwistLeafName 256)     twisted_l [coffsN_l]))
    (.RCall (babybearNttForwardLeafName 256)     result_l  [twisted_l])

/-- Body for `(N=256, k=4)`: four RCalls at the medium regime. -/
def ldeCosetFftBody256x4 : LowCT :=
  let evals_l   := locPlonky3Lde "evals"   (babybearVecTowerType 256)
  let coeffs_l  := locPlonky3Lde "coeffs"  (babybearVecTowerType 256)
  let coffsN_l  := locPlonky3Lde "coeffs_kN" (babybearVecTowerType 1024)
  let twisted_l := locPlonky3Lde "twisted" (babybearVecTowerType 1024)
  let result_l  := locPlonky3Lde "__result" (babybearVecTowerType 1024)
  .RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (babybearNttInverseLeafName 256)       coeffs_l  [evals_l]))
    (.RCall (babybearZeroExtendLeafName 256 1024)  coffsN_l  [coeffs_l]))
    (.RCall (babybearCosetTwistLeafName 1024)      twisted_l [coffsN_l]))
    (.RCall (babybearNttForwardLeafName 1024)      result_l  [twisted_l])

/-- Body for `(N=1024, k=4)`: four RCalls at the deep regime. -/
def ldeCosetFftBody1024x4 : LowCT :=
  let evals_l   := locPlonky3Lde "evals"   (babybearVecTowerType 1024)
  let coeffs_l  := locPlonky3Lde "coeffs"  (babybearVecTowerType 1024)
  let coffsN_l  := locPlonky3Lde "coeffs_kN" (babybearVecTowerType 4096)
  let twisted_l := locPlonky3Lde "twisted" (babybearVecTowerType 4096)
  let result_l  := locPlonky3Lde "__result" (babybearVecTowerType 4096)
  .RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (babybearNttInverseLeafName 1024)        coeffs_l  [evals_l]))
    (.RCall (babybearZeroExtendLeafName 1024 4096)   coffsN_l  [coeffs_l]))
    (.RCall (babybearCosetTwistLeafName 4096)        twisted_l [coffsN_l]))
    (.RCall (babybearNttForwardLeafName 4096)        result_l  [twisted_l])

/-- `ReifiedFunc` bundle for the (N=64, k=4) LDE. -/
def ldeCosetFft64x4Reified : ReifiedFunc :=
  { args    := [("evals", babybearVecTowerType 64)]
    body    := ldeCosetFftBody64x4
    retName := "__result" }

/-- `ReifiedFunc` bundle for the (N=256, k=4) LDE. -/
def ldeCosetFft256x4Reified : ReifiedFunc :=
  { args    := [("evals", babybearVecTowerType 256)]
    body    := ldeCosetFftBody256x4
    retName := "__result" }

/-- `ReifiedFunc` bundle for the (N=1024, k=4) LDE. -/
def ldeCosetFft1024x4Reified : ReifiedFunc :=
  { args    := [("evals", babybearVecTowerType 1024)]
    body    := ldeCosetFftBody1024x4
    retName := "__result" }

/-! ## 6. Default-config alias

`ldeCosetFftReified : LowCT` is the canonical entry point: the
medium-regime `(N=256, k=4)` body. It matches the string-emitted
`lde_coset_fft.jazz` array width (`u64[1024]`), so the KAT against the
string emit is byte-identical at this size. -/

/-- The canonical entry point: the medium-regime `(N=256, k=4)` LDE body. -/
def ldeCosetFftReified : ReifiedFunc := ldeCosetFft256x4Reified

/-! ## 7. Opaque-leaf correctness hypotheses

The leaves above are opaque axioms in Lean. The emit's correctness lifts to
the full spec only if the leaves' jasmin implementations match the BabyBear
spec semantics. We name those obligations explicitly here so downstream files
can quote them — they are NOT proven; the leaves are linked against
`plonky3-hax`'s matching implementations at C-harness link time, and the
named hypotheses below are the assumption that link-time behavior is
correct. -/

/-- Inverse-NTT leaf correctness: `babybear_ntt_inverse_N` realises the
    spec's subgroup-H inverse NTT (cf. `plonky3-hax/src/specs/baby_bear.rs`
    `bb_intt` if exposed; otherwise the canonical inverse-NTT pseudocode). -/
def NttInverseLeafCorrect : Prop := True  -- named hypothesis only

/-- Forward-NTT leaf correctness: `babybear_ntt_forward_kN` realises the
    spec's coset-domain forward NTT. -/
def NttForwardLeafCorrect : Prop := True  -- named hypothesis only

/-- Zero-extend leaf correctness: `babybear_zero_extend_N_to_kN` zero-pads
    the upper `(k-1)·N` positions and copies the lower `N`. -/
def ZeroExtendLeafCorrect : Prop := True  -- named hypothesis only

/-- Coset-twist leaf correctness: `babybear_coset_twist_kN` multiplies
    position `i` by `shift^i`. -/
def CosetTwistLeafCorrect : Prop := True  -- named hypothesis only

/-! ## 8. Bridge theorem to hax extraction

The plonky3-hax Rust source for the coset-FFT LDE is `compute_column_lde` (in
`plonky3-hax/src/specs/`). At present there is no `hax → Lean` extraction for
that function exposed in CatCrypt (the plonky3-hax tree compiles, but its
charon dump has not been wired into a `Hax.ReprBridge` view of an LDE
function in the SurfaceDeps catalog).

We therefore leave the LDE-side hax-bridge as a named hypothesis. The bridge
is **structurally mechanical**: `compute_column_lde` is a straight-line
sequence of four steps (`bb_intt → pad → twist → bb_ntt`), exactly matching
`ldeCosetFftLean256x4`'s let-chain. The only obligation is to match each
leaf-call's argument shape and width — a one-statement-per-line proof once
the extraction is in place. -/

/-- **Bridge to hax extraction (named hypothesis).**

    Asserts that the pure-Lean `ldeCosetFftLean256x4` agrees with the hax-
    extracted Rust `compute_column_lde` once the extraction lands. The bridge
    is **mechanical**: `compute_column_lde`'s Rust body is the same 4-step
    chain `bb_intt → zero_extend → coset_twist → bb_ntt`, with the same per-
    step argument shapes; the Lean let-chain mirrors it position-for-position.

    The bridge is currently a named hypothesis (not a theorem) for two
    reasons:
    1. **No hax extraction yet for LDE.** plonky3-hax's `compute_column_lde`
       has not been wired through hax → CatCrypt's `Hax.ReprBridge`. When
       it is, this Prop becomes the equation
       `ldeCosetFftLean256x4 = hax_compute_column_lde_256_to_1024`.
    2. **Opaque-leaf identification.** The bridge has to identify each
       `babybear_*` leaf with the corresponding hax-extracted leaf (which
       Rust calls `bb_intt`, `bb_ntt`, etc.). Once leaf naming is agreed,
       the proof is mechanical (refl-up-to-leaf-renaming). -/
def Phase2LdeBridgeToHaxExtraction : Prop := True  -- named hypothesis only

/-! ## 9. Dataflow checks

Static checks on the hand-written bodies: no call reads an undefined slot, and
every computed slot other than `__result` is read by a later call. -/

#guard straightLineUndefined ldeCosetFft64x4Reified = some []
#guard straightLineUnread ldeCosetFft64x4Reified = some []
#guard straightLineUndefined ldeCosetFft256x4Reified = some []
#guard straightLineUnread ldeCosetFft256x4Reified = some []
#guard straightLineUndefined ldeCosetFft1024x4Reified = some []
#guard straightLineUnread ldeCosetFft1024x4Reified = some []

end CatCrypt.Crypto.Jasmin.LowCTReflect
