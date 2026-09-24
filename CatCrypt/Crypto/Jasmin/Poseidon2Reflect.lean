/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Poseidon2 BabyBear width-16 — reflect surface for the verified-front emit (4 variants)

This file is the ZK-hash analogue of `UovReflect.lean`. It adds Poseidon2-BabyBear
specific opaque types and `LowCTPattern` registrations so a pure-Lean Poseidon2
permutation can be lifted through the verified compiler chain
`LowCT → Com catCryptDialect → Jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## Four variants — same opaque-leaf shape, different leaf bodies

| Variant                                  | Leaf name                                    | Body (provided by `poseidon2_leaves.jinc`)                                  |
|------------------------------------------|----------------------------------------------|-----------------------------------------------------------------------------|
| `poseidon2BaselineLean`                  | `poseidon2_bb_baseline`                      | scalar BabyBear arithmetic on 16 `reg u64` lanes                            |
| `poseidon2MontgomeryLean`                | `poseidon2_bb_montgomery`                    | Montgomery + VPMULUDQ packed 32×32→64 mul; canonical I/O                    |
| `poseidon2MontgomeryResidentLean`        | `poseidon2_bb_montgomery_resident`           | Montgomery + lane-resident YMM state across the external rounds            |
| `poseidon2MontgomeryResidentPartialLean` | `poseidon2_bb_montgomery_resident_partial`   | Montgomery + lane-resident + YMM-direct internal_mat across partial rounds |

All four implement the same *field permutation* `Poseidon2.permute_16` over BabyBear
(`p = 2^31 − 2^27 + 1`, width 16, S-box `x^7`, 8 full + 13 partial rounds), so
they are byte-identical on the canonical wire format — denotation differences live
**only** at the leaf-shim level (Montgomery vs canonical state, scalar vs SIMD).

## Why opaque-leaf? — SIMD-as-opaque-leaf pattern from UOV

The UOV GFNI variant uses the pattern: **SIMD speed in the verified front is
obtained by registering SIMD primitives as opaque leaves + linking via a
leaf-shim inline fn**, not by extending `LowCT` with a vector dialect. UOV's
GFNI variant runs at 0.80× the hand-rolled ceiling **without** SIMD machinery
in the verified front.

Poseidon2's SIMD variants need `#VPMULUDQ_256`, `#VPADD_4u64`, etc. None of these
are arithmetic leaves `LowCT` already supports. We **do not** extend `LowCT`
itself: each Poseidon2 variant is registered as an opaque leaf whose body is
provided externally (`bench/poseidon2_compare/include/poseidon2_leaves.jinc`).
The verified front sees only the opaque leaf name and the tower-type signature;
the compiler-trace claim is about the orchestration around the leaf, not about
re-proving the AVX2 intrinsics' per-lane semantics (those are pinned by the
existing per-variant denotation theorems in `Poseidon2Montgomery.lean`:
`MontIso.montPerm_sandwich_eq`, `montInternalMDS_vec_eq`, etc.).

The orchestration in this file is trivial — one `RCall` per variant — because the
permutation body is itself the leaf. Compare to UOV where the orchestration is
also one `RCall`. The pattern scales: the orchestration grows when the protocol
combines several leaves (Falcon-verify is 7 RCalls); for primitives where the
*whole permutation* is the leaf, the body is one RCall.

## Reflection→front gap (same workaround as UOV / Falcon / jhash)

`reifyLowCT%` reads only `LowCTReflect.knownOps`, not the dynamic
`LowCTPattern` registry, so `reifyLowCT% poseidon2BaselineLean` would error.
Same workaround as `UovReflect`: define the pure-Lean function for documentation,
register each leaf in the `LowCTPattern` registry via `@[rust_cmd_pattern]`,
then **hand-build the `LowCT`** the reifier *would* produce. Downstream
(`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is the unmodified verified
front.

## References

* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling reference for the
  hand-built-body around `@[rust_cmd_pattern]` registration pattern.
* `bench/uov_compare/include/uov_leaves.jinc` — sibling reference for the
  leaf-shim file that provides SIMD-intrinsic bodies.
* Plonky3 `default_babybear_poseidon2_16` (p3-baby-bear v0.5) — KAT reference.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Poseidon2-BabyBear surface types

The state of Poseidon2-BabyBear is 16 field elements in `ZMod p` with
`p = 2^31 − 2^27 + 1`. Each element fits in a `u32` canonically, but the
emitter / leaves carry them in `u64` slots (the JasminAbi's `stack u64[16]`),
so the surface type is a 16-`u64` block (128 bytes). The same `TBytes 128`
encoding serves all four variants — Montgomery vs canonical state form is a
denotation-irrelevant refinement at the leaf-shim level. -/

/-- A 16-lane Poseidon2-BabyBear state (16 × `u64` = 128 bytes). Opaque; the
    leaves implement scalar / Montgomery / lane-resident / YMM-direct variants.
    The reifier encodes this as `.TBytes 128` (`memref 16` under `encodeTy`). -/
axiom Poseidon2BbState : Type
/-- Axiomatic inhabitant. -/ axiom Poseidon2BbState.default : Poseidon2BbState
noncomputable instance : Inhabited Poseidon2BbState := ⟨Poseidon2BbState.default⟩

/-! ## 2. Poseidon2 leaves (axioms = opaque jasmin function symbols)

Each variant is one opaque permutation leaf. The four leaves share the same
*denotation* — the BabyBear-field Poseidon2 permutation — but each variant's
leaf body in the .jinc uses a different mix of scalar / Montgomery / SIMD
machinery. The verified front sees only the leaf name and tower-type signature. -/

/-- Baseline Poseidon2 permutation over BabyBear (width 16). Pure scalar field
    arithmetic on canonical `u64` representation. Body: 10-fold BabyBear reduce
    + `x^7` S-box + external/internal MDS layers + canonical RC-add. Matches
    `poseidon2Jazz` exactly (scalar baseline). -/
axiom poseidon2_bb_baseline : Poseidon2BbState → Poseidon2BbState

/-- Montgomery single-pass Poseidon2 permutation. State carried in Montgomery
    form (`phi(x) = x · R`) across the whole permutation; canonical↔Montgomery
    conversion only at the I/O boundary; round constants pre-converted to
    Montgomery form at compile time. Each S-box multiply is a single MontReduce
    on top of an AVX2 `#VPMULUDQ_256` packed 32×32 → 64 mul. Denotation matches
    baseline via `Poseidon2Montgomery.MontIso.montPerm_sandwich_eq`. -/
axiom poseidon2_bb_montgomery : Poseidon2BbState → Poseidon2BbState

/-- Lane-resident single-pass Montgomery Poseidon2. State pinned to 4 named YMM
    registers `vS0..vS3` across the 4 initial + 4 terminal external rounds.
    RC-add, csub, S-box quartets all act reg-to-reg on `vS0..vS3` — no stack
    round-trip through `s[]` between rounds. Same denotation as the Montgomery
    single-pass variant (storage class is a denotation-irrelevant refinement). -/
axiom poseidon2_bb_montgomery_resident : Poseidon2BbState → Poseidon2BbState

/-- Lane-resident + YMM-direct internal_mat single-pass Montgomery Poseidon2.
    State pinned to `vS0..vS3` across the FULL 4 + 13 + 4 = 21-round schedule;
    the 13 partial rounds run YMM-direct (scalar lane-0 sbox via one `tbuf`
    round-trip per round, then YMM-direct `internal_mat` against
    Montgomery-form `DIAGV_MONT` table). No stack `s[]` spill between partial
    rounds. Same denotation as the lane-resident variant via
    `MontIso.montInternalMDS_vec_eq`. -/
axiom poseidon2_bb_montgomery_resident_partial : Poseidon2BbState → Poseidon2BbState

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `poseidon2_bb_baseline` → leaf `poseidon2_bb_baseline`. -/
@[rust_cmd_pattern]
def poseidon2BaselinePattern : LowCTPattern where
  name      := "poseidon2_bb_baseline"
  fnHead    := ``poseidon2_bb_baseline
  arity     := 1
  towerType := .TBytes 128   -- 16-lane state

/-- Register `poseidon2_bb_montgomery` → leaf `poseidon2_bb_montgomery`. -/
@[rust_cmd_pattern]
def poseidon2MontgomeryPattern : LowCTPattern where
  name      := "poseidon2_bb_montgomery"
  fnHead    := ``poseidon2_bb_montgomery
  arity     := 1
  towerType := .TBytes 128

/-- Register `poseidon2_bb_montgomery_resident` → leaf
    `poseidon2_bb_montgomery_resident`. -/
@[rust_cmd_pattern]
def poseidon2MontgomeryResidentPattern : LowCTPattern where
  name      := "poseidon2_bb_montgomery_resident"
  fnHead    := ``poseidon2_bb_montgomery_resident
  arity     := 1
  towerType := .TBytes 128

/-- Register `poseidon2_bb_montgomery_resident_partial` → leaf
    `poseidon2_bb_montgomery_resident_partial`. -/
@[rust_cmd_pattern]
def poseidon2MontgomeryResidentPartialPattern : LowCTPattern where
  name      := "poseidon2_bb_montgomery_resident_partial"
  fnHead    := ``poseidon2_bb_montgomery_resident_partial
  arity     := 1
  towerType := .TBytes 128

/-! ## 4. Poseidon2 tower-type abbreviation -/

/-- Tower type of one Poseidon2-BabyBear state: 16 × `u64` = 128 bytes. -/
def poseidon2BbStateTowerType : TowerType := .TBytes 128

def locPoseidon2 (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean Poseidon2 kernel functions — the specs

These are documentation only; the reifier doesn't consult them at lift time
(see "Reflection→front gap" above). The hand-built `LowCT` bodies below
mirror these one-for-one.

All four implement the same *field permutation*; the difference between them is
the **leaf body** (provided externally by `poseidon2_leaves.jinc`), not the
Lean orchestration. -/

/-- Baseline Poseidon2-BabyBear permutation (pure scalar). One opaque leaf call. -/
noncomputable def poseidon2BaselineLean (s : Poseidon2BbState) : Poseidon2BbState :=
  poseidon2_bb_baseline s

/-- Montgomery + VPMULUDQ single-pass Poseidon2-BabyBear. One opaque leaf call;
    the leaf body uses #VPMULUDQ_256 and Montgomery state internally. -/
noncomputable def poseidon2MontgomeryLean (s : Poseidon2BbState) : Poseidon2BbState :=
  poseidon2_bb_montgomery s

/-- Lane-resident Montgomery Poseidon2-BabyBear. One opaque leaf call;
    the leaf keeps state in YMM regs across external rounds. -/
noncomputable def poseidon2MontgomeryResidentLean (s : Poseidon2BbState) :
    Poseidon2BbState :=
  poseidon2_bb_montgomery_resident s

/-- Lane-resident + YMM-direct internal_mat Poseidon2-BabyBear. One opaque leaf
    call; the leaf keeps state in YMM regs across the FULL round schedule
    including the 13 partial rounds. -/
noncomputable def poseidon2MontgomeryResidentPartialLean (s : Poseidon2BbState) :
    Poseidon2BbState :=
  poseidon2_bb_montgomery_resident_partial s

/-! ## 6. Hand-built `LowCT` bodies (the front-end input)

Each is one `RSeq RSkip (RCall leaf result [state])` — the same shape
`reifyLowCT%`'s final-op walker produces for a single-call body. The leaf
names match the `@[rust_cmd_pattern]` registrations above. -/

/-- The `LowCT` body for `poseidon2BaselineLean`. -/
def poseidon2BaselineBody : LowCT :=
  let s_l      := locPoseidon2 "s"        poseidon2BbStateTowerType
  let result_l := locPoseidon2 "__result" poseidon2BbStateTowerType
  .RSeq .RSkip
    (.RCall "poseidon2_bb_baseline" result_l [s_l])

/-- `ReifiedFunc` bundle for the baseline Poseidon2 permutation. -/
def poseidon2BaselineReified : ReifiedFunc :=
  { args    := [("s", poseidon2BbStateTowerType)]
    body    := poseidon2BaselineBody
    retName := "__result" }

/-- The `LowCT` body for `poseidon2MontgomeryLean`. -/
def poseidon2MontgomeryBody : LowCT :=
  let s_l      := locPoseidon2 "s"        poseidon2BbStateTowerType
  let result_l := locPoseidon2 "__result" poseidon2BbStateTowerType
  .RSeq .RSkip
    (.RCall "poseidon2_bb_montgomery" result_l [s_l])

/-- `ReifiedFunc` bundle for the Montgomery + VPMULUDQ variant. -/
def poseidon2MontgomeryReified : ReifiedFunc :=
  { args    := [("s", poseidon2BbStateTowerType)]
    body    := poseidon2MontgomeryBody
    retName := "__result" }

/-- The `LowCT` body for `poseidon2MontgomeryResidentLean`. -/
def poseidon2MontgomeryResidentBody : LowCT :=
  let s_l      := locPoseidon2 "s"        poseidon2BbStateTowerType
  let result_l := locPoseidon2 "__result" poseidon2BbStateTowerType
  .RSeq .RSkip
    (.RCall "poseidon2_bb_montgomery_resident" result_l [s_l])

/-- `ReifiedFunc` bundle for the lane-resident Montgomery variant. -/
def poseidon2MontgomeryResidentReified : ReifiedFunc :=
  { args    := [("s", poseidon2BbStateTowerType)]
    body    := poseidon2MontgomeryResidentBody
    retName := "__result" }

/-- The `LowCT` body for `poseidon2MontgomeryResidentPartialLean`. -/
def poseidon2MontgomeryResidentPartialBody : LowCT :=
  let s_l      := locPoseidon2 "s"        poseidon2BbStateTowerType
  let result_l := locPoseidon2 "__result" poseidon2BbStateTowerType
  .RSeq .RSkip
    (.RCall "poseidon2_bb_montgomery_resident_partial" result_l [s_l])

/-- `ReifiedFunc` bundle for the lane-resident + YMM-direct internal_mat
    variant. -/
def poseidon2MontgomeryResidentPartialReified : ReifiedFunc :=
  { args    := [("s", poseidon2BbStateTowerType)]
    body    := poseidon2MontgomeryResidentPartialBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval poseidon2BaselineReified.args.map Prod.fst                    -- [s]
#eval poseidon2BaselineReified.args.length                          -- 1
#eval poseidon2BaselineReified.retName                              -- __result
#eval poseidon2MontgomeryReified.args.length                        -- 1
#eval poseidon2MontgomeryResidentReified.args.length                -- 1
#eval poseidon2MontgomeryResidentPartialReified.args.length         -- 1

open Lean in
#eval show Lean.MetaM _ from do
  LowCTPattern.taggedDecls                            -- expect 4 Poseidon2 patterns

end CatCrypt.Crypto.Jasmin.LowCTReflect
