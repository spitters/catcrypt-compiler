/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# X25519 reflect surface — Montgomery-ladder iteration via the verified front

This file is the **Curve25519 / RFC 7748 analogue** of `Secp256k1Reflect.lean`:
it adds X25519-specific opaque surface types (`X25519LadderState`) and a
`@[rust_cmd_pattern]` registration so that a pure-Lean Montgomery-ladder
iteration can be lifted through the verified compiler chain
`LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## The ladder iteration leaf

The 255-step X25519 Montgomery ladder factors as 255 invocations of the
**single ladder-step kernel** `x25519_ladder_iter`. RFC 7748 §5
specifies the per-step body (the `cswap` + the X- and Z-coordinate
double/add formulas over the prime field `2²⁵⁵ − 19`). Each step reads
the carried 24-word accumulator bundle `[x2 | z2 | x3 | z3 | scalar | base]`
and produces the next accumulator. The full ladder is therefore
`acc ↦ x25519_ladder_iter(acc)` iterated 255 times — the same shape as
`bench/x25519_ladder/x25519_ladder_emit.lean`'s `x25519Ladder.toCfor`,
which already emits the verified for-loop wrapper.

The leaf body (`include/x25519_leaves.jinc`) wraps **formosa-25519**'s
ref4 Montgomery-ladder iteration over the 24-word bundle (the same step
the existing `bench/x25519_ladder/x25519_ladder_iter.jinc` uses); the
verified front sees only the opaque leaf name and the 24-u64-limb tower
type.

| Lean axiom              | Leaf name (.jazz)      | TowerType    |
|------------------------|------------------------|--------------|
| `x25519_ladder_iter`    | `x25519_ladder_iter`   | `TBytes 192` |

192 bytes = 24 × 8 bytes = one bundle.

## NO HAX BRIDGE — bridge is to RFC 7748 §5 spec only

The rustcmd's `x25519` builds on opaque `fe_*` leaves; no hax extraction exists
to bridge against. The bridge target is the hand-written Lean spec used by
`bench/x25519_ladder/x25519_ladder_emit.lean`, not hax output.

There is no `x25519-hax/` Rust source. The L3 bridge for x25519 is to
the RFC 7748 §5.2 byte-vector test vectors (KAT-only); the named
hypothesis `X25519LeanSpecCorrect` in the driver records the trust edge
(the leaf body computes one RFC 7748 ladder step).

## Reflection→front gap (same as UOV / secp256k1 / P-256)

`reifyLowCT%` doesn't consult the `LowCTPattern` registry, so
`reifyLowCT% x25519LadderStepLean` would error. We register the leaf
via `@[rust_cmd_pattern]`, then hand-build the `LowCT` body the
reifier *would* produce.

## References

* RFC 7748: Elliptic Curves for Security, §5 (X25519, the Montgomery
  ladder); §5.2 (KAT vectors)
* `bench/x25519_ladder/x25519_ladder_iter.jinc` — formosa-25519 ref4
  ladder-step body that the leaf delegates to
* `bench/x25519_ladder/x25519_ladder_emit.lean` — the verified-loop-layer
  emit driver (the loop wrapper around this Reflect surface's iteration)
* `CatCrypt/Crypto/SecureCompilation/VIR/X25519Ladder.lean` —
  `x25519Ladder.toCfor` / `x25519Ladder_loop_denote_eq`
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque X25519 surface types

The X25519 ladder carries a 24-word `u64` accumulator bundle:
`[x2 (4) | z2 (4) | x3 (4) | z3 (4) | scalar (4) | base (4)]`. We surface
this as one opaque type `X25519LadderState` of `TBytes 192` (24 × 8 = 192
bytes). -/

/-- A Curve25519 ladder accumulator bundle: the 24-u64-word state
    `[x2 | z2 | x3 | z3 | scalar | base]`. Opaque on the Lean side; the
    leaf `x25519_ladder_iter` reads and writes one full bundle per step.
    The reifier encodes this as `TBytes 192` (memref 24 u64-limbs). -/
axiom X25519LadderState : Type
/-- Axiomatic inhabitant. -/ axiom X25519LadderState.default : X25519LadderState
noncomputable instance : Inhabited X25519LadderState := ⟨X25519LadderState.default⟩

/-! ## 2. X25519 leaves (axioms = opaque jasmin function symbols)

The single leaf is the per-iteration body of the Montgomery ladder. -/

/-- One iteration of the X25519 Montgomery ladder. Reads the current
    bundle, performs the `cswap` based on the current scalar bit, executes
    the X- and Z-coordinate double/add formulas over the prime field
    `2²⁵⁵ − 19`, and writes the next bundle. Opaque here — the jasmin
    body wraps formosa-25519's ref4 ladder-step over the 24-word bundle.
    The 255-fold iteration of this leaf is the full X25519 scalarmult. -/
axiom x25519_ladder_iter : X25519LadderState → X25519LadderState

/-! ## 3. `@[rust_cmd_pattern]` registration -/

/-- Register `x25519_ladder_iter` → leaf `x25519_ladder_iter`. -/
@[rust_cmd_pattern]
def x25519LadderIterPattern : LowCTPattern where
  name      := "x25519_ladder_iter"
  fnHead    := ``x25519_ladder_iter
  arity     := 1
  towerType := .TBytes 192   -- 24 × 8-byte limbs of the ladder bundle

/-! ## 4. X25519 tower-type abbreviation -/

/-- Tower type of the 24-u64-word ladder bundle. -/
def x25519LadderStateTowerType : TowerType := .TBytes 192

def locX25519 (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean X25519 kernel function — the spec -/

/-- One step of the Montgomery ladder: `acc' = x25519_ladder_iter(acc)`.
    The full X25519 ladder is this leaf iterated 255 times — the shape
    emitted by `bench/x25519_ladder/x25519_ladder_emit.lean`'s verified
    loop wrapper, and the shape this Reflect surface mirrors per
    iteration. -/
noncomputable def x25519LadderStepLean (acc : X25519LadderState) : X25519LadderState :=
  x25519_ladder_iter acc

/-! ## 6. Hand-built `LowCT` body (the front-end input)

Since `reifyLowCT%` does not consult the `LowCTPattern` registry, we
hand-build the body the reifier *would* produce for `x25519LadderStepLean`.
Shape: one `RSeq RSkip (RCall …)`. -/

/-- The `LowCT` body for `x25519LadderStepLean`:

    ```
    __result := x25519_ladder_iter(acc)
    ```

    A single `RCall` ending the chain. -/
def x25519LadderStepBody : LowCT :=
  let acc_l    := locX25519 "acc"      x25519LadderStateTowerType
  let result_l := locX25519 "__result" x25519LadderStateTowerType
  .RSeq .RSkip
    (.RCall "x25519_ladder_iter" result_l [acc_l])

/-- `ReifiedFunc` bundle for the ladder-step kernel. -/
def x25519LadderStepReified : ReifiedFunc :=
  { args    := [("acc", x25519LadderStateTowerType)]
    body    := x25519LadderStepBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval x25519LadderStepReified.args.map Prod.fst              -- [acc]
#eval x25519LadderStepReified.args.length                    -- 1
#eval x25519LadderStepReified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
