/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Plonky3 AIR reflect surface — Tier A migration of the AIR layer

Layer 4 of the Plonky3 STARK chain (#154): the AIR (Algebraic Intermediate
Representation) transition-constraint evaluator over a precomputed execution
trace. This file is the architectural analogue of `Plonky3Reflect.lean`
(Merkle, Wave 1): every byte of the new AIR emit goes through the verified
front `LowCT → CryptoSSA → Com → jasmin`.

## AIR equation (this surface)

Trace width = 3 (`[x, y, z]`); the transition constraints per pair of
consecutive rows `(cur, next)` are:

```
  c_0 = next.x - cur.z                     -- "next.x = z" (shift)
  c_1 = next.z - (next.x + next.y)         -- "next.z = next.x + next.y"
```

The AIR holds at the trace iff every `c_i` evaluates to `0` at every adjacent
pair. The per-row transition body reads two rows, computes the two
constraints, and accumulates the `ok` flag. The sweep over rows is a
**lane-parallel MAP** (one independent transition per lane).

| Lean axiom                          | Leaf name (.jazz)                  | TowerType         |
|-------------------------------------|------------------------------------|-------------------|
| `plonky3_air_transition_W_H`        | `plonky3_air_transition_W_H`       | `TBytes 8`        |

The opaque leaf evaluates the transition at one row pair; the orchestration
(the per-row sweep) is what the verified front emits. The leaf is parameterised
by the trace width `W` and the height `H` (the runtime `i` bound is part of the
leaf's contract, not the orchestration — the orchestration just chains one
RCall per step bucket).

For Tier-A KAT identity with the legacy Tier-C `air.jazz` body, we provide a
single-call shape: one `air_transition` call that returns the OK flag (a
`TBytes 8` u64-sized buffer). Multi-step variants statically unroll into a
chain of identical RCall sites.

## Reflection→front gap

Same as `FalconReflect.lean` / `Plonky3Reflect.lean`: `reifyLowCT%` does not
consult the `LowCTPattern` registry, so we hand-build the body the reifier
*would* produce. Downstream (`translate → cryptoDialectToJasminCom →
emitAbiOrchRegPtr`) is unchanged.

## Relation to legacy Tier C `Plonky3AirEmit.lean`

The legacy file builds its `.jazz` via inline regArith templating; this file
replaces that pattern with an in-chain emit anchored on an opaque
`plonky3_air_transition` leaf so the orchestration is verified end-to-end.
The leaf's field-arithmetic body is the legacy file's responsibility (linked
in via `air_eval_fib.jinc` / equivalent); the cross-layer composition is now
verified.

## References

* Plonky3 AIR transition: `plonky3-hax/src/air.rs`
* Mirror pattern: `CatCrypt/Crypto/Jasmin/Plonky3Reflect.lean` (Wave 1 Merkle)
* Driver template: `bench/plonky3_compare/merkle_from_rustcmd.lean`
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Plonky3 AIR surface types

The reflect surface treats the trace as an opaque buffer of
`W * H * 8` bytes (one u64 BabyBear cell per slot), and the per-step
transition output as a single u64 OK byte (we use `TBytes 8`). The
field-arithmetic body lives in the leaf; the orchestration is what we
verify here. -/

/-- An opaque Plonky3 trace buffer of `W` columns × `H` rows of BabyBear
    field elements (8 bytes each). Opaque on the Lean side; the leaf
    `plonky3_air_transition_W_H` consumes a width-`W * H * 8`-byte buffer. -/
axiom Plonky3Trace (W H : Nat) : Type
/-- Axiomatic inhabitant. -/
axiom Plonky3Trace.default (W H : Nat) : Plonky3Trace W H
noncomputable instance (W H : Nat) : Inhabited (Plonky3Trace W H) :=
  ⟨Plonky3Trace.default W H⟩

/-- The OK flag bundle returned by one AIR transition sweep — opaque 8-byte
    blob holding the accumulated u64 OK status. -/
axiom Plonky3AirOk : Type
/-- Axiomatic inhabitant. -/
axiom Plonky3AirOk.default : Plonky3AirOk
noncomputable instance : Inhabited Plonky3AirOk := ⟨Plonky3AirOk.default⟩

/-! ## 2. AIR leaves (axioms = opaque jasmin function symbols)

`plonky3_air_transition_W_H` consumes the trace buffer (containing W columns,
H rows) and returns the accumulated OK flag (= 1 iff every transition holds).
Parameterised by `(W, H)`. -/

/-- One AIR transition sweep over a precomputed trace. Returns the OK flag
    accumulated over all `H - 1` transitions. Implementation is per-row
    field arithmetic per the AIR constraints (3-column variant:
    `next.x = cur.z` and `next.z = next.x + next.y`). -/
axiom plonky3_air_transition (W H : Nat) :
    Plonky3Trace W H → Plonky3AirOk

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `plonky3_air_transition` for the demonstrator width=3, height=8. -/
@[rust_cmd_pattern]
def plonky3AirTransition3x8Pattern : LowCTPattern where
  name      := "plonky3_air_transition_3_8"
  fnHead    := ``plonky3_air_transition
  arity     := 1
  towerType := .TBytes 8

/-! ## 4. Pure-Lean AIR transition function

The pure-Lean specification: a single opaque leaf call wrapped in a
`let`-chain mirroring the hand-built `LowCT` exactly. -/

/-- Pure-Lean AIR transition sweep for trace width=3, height=8. -/
noncomputable def airTransitionLean3x8 (trace : Plonky3Trace 3 8) : Plonky3AirOk :=
  let ok := plonky3_air_transition 3 8 trace
  ok

/-- Pure-Lean AIR transition sweep for trace width=3, height=16. -/
noncomputable def airTransitionLean3x16 (trace : Plonky3Trace 3 16) : Plonky3AirOk :=
  let ok := plonky3_air_transition 3 16 trace
  ok

/-! ## 5. Hand-built `LowCT` body — the front-end input

`reifyLowCT%` does not consult the registry, so we hand-build the body.
Downstream (`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is unmodified. -/

/-- TowerType for the AIR trace buffer of width `W`, height `H`
    (8 bytes per BabyBear cell). -/
def plonky3TraceTowerType (W H : Nat) : TowerType := .TBytes (8 * W * H)

/-- TowerType for the OK flag bundle (u64 wrapper). -/
def plonky3AirOkTowerType : TowerType := .TBytes 8

private def loc (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Per-(W,H) AIR transition leaf name: `plonky3_air_transition_W_H`. -/
def plonky3AirTransitionLeafName (W H : Nat) : String :=
  "plonky3_air_transition_" ++ toString W ++ "_" ++ toString H

/-- Body for width=3, height=8: one transition call. -/
def airTransitionBody3x8 : LowCT :=
  let trace_l  := loc "trace" (plonky3TraceTowerType 3 8)
  let result_l := loc "__result" plonky3AirOkTowerType
  .RSeq .RSkip
    (.RCall (plonky3AirTransitionLeafName 3 8) result_l [trace_l])

/-- Body for width=3, height=16: one transition call (different leaf
    instantiation). -/
def airTransitionBody3x16 : LowCT :=
  let trace_l  := loc "trace" (plonky3TraceTowerType 3 16)
  let result_l := loc "__result" plonky3AirOkTowerType
  .RSeq .RSkip
    (.RCall (plonky3AirTransitionLeafName 3 16) result_l [trace_l])

/-- `ReifiedFunc` bundle for width=3, height=8 (mirrors what `reifyLowCT%`
    would produce for `airTransitionLean3x8`). -/
def airTransitionReified3x8 : ReifiedFunc :=
  { args    := [("trace", plonky3TraceTowerType 3 8)]
    body    := airTransitionBody3x8
    retName := "__result" }

/-- `ReifiedFunc` bundle for width=3, height=16. -/
def airTransitionReified3x16 : ReifiedFunc :=
  { args    := [("trace", plonky3TraceTowerType 3 16)]
    body    := airTransitionBody3x16
    retName := "__result" }

/-- Canonical default name used in the bench docstring: `airTransitionReified`
    aliases the height-8 demonstrator. -/
def airTransitionReified : ReifiedFunc := airTransitionReified3x8

/-! ## 6. Inspection -/

#eval airTransitionReified3x8.args.map Prod.fst              -- [trace]
#eval airTransitionReified3x16.args.length                   -- 1
#eval airTransitionReified.retName                           -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
