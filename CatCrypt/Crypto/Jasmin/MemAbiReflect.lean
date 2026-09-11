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
# Memory-pointer ABI reflect surface: the ML-KEM FO "J" hash

This file registers a single new reifier op, `mlk_jhash_mem`, for the
ML-KEM-768 Fujisaki–Okamoto implicit-rejection hash

  `J(z, ct) = SHAKE256(z ‖ ct, 32)`

with `z` the 32-byte rejection seed (`sk[2368:2400]`) and `ct` the 1088-byte
ciphertext (`MLKEM_INDCPA_CIPHERTEXTBYTES`). It is the surface for the
formosa avx2 leaf `_shake256_1120_32(reg u64 out in0 in1)`, an
**all-`reg u64`** standard-pointer-convention leaf (each buffer is a raw
caller-memory address, not a typed jasmin array). That leaf shape is exactly
what `JasminAbiEmit.emitAbiOrchMem` (the THIRD, memory-pointer ABI emit mode)
targets.

## Registration (no edit to `LowCTReflect.knownOps`)

The op is registered through the **`@[rust_cmd_pattern]` attribute** from this
separate file. `LowCTPattern.snapshot` / `LowCTPattern.taggedDecls` see the
entry, so no edit to `LowCTReflect.lean` is needed.

The `LowCTPattern` carries a single `towerType` used for the **destination**
(`.TBytes 32` → 32-byte output). The argument *types* are taken from the caller's
`VarMap` at `translate` time (`resolveLocatedArgs` looks each arg up by name), NOT
from the pattern's `towerType` — so the two inputs may differ in size
(`z` = `.TBytes 32`, `ct` = `.TBytes 1088`) even though the pattern only stores
one tower type. This is what lets a single registry entry describe the
heterogeneous `(out:32, z:32, ct:1088)` leaf.

## Reflection→front gap (documented)

`reifyLowCT%`'s walker (`LowCTReflect.reifyChain`) consults **only** the
in-file `knownOps` table via `matchOp?`; it does **not** call `matchPattern?`,
so the `@[rust_cmd_pattern]` registry is *not* yet wired into the reifier. A
`reifyLowCT% jhashLean` therefore errors with "final expression is neither a
bound var nor a known fp_* op". Wiring the registry fallback into `reifyChain`
requires editing `LowCTReflect.lean` (frozen for this task — another agent
owns it).

We therefore build the **same `LowCT` body the reifier *would* produce** by
hand (`jhashBody` below: one `RCall "jhash_mem"` ending the chain, retName
`__result`) and drive it through the **rest of the verified front unchanged**
(`translate` → `extractedFrontProg` → `cryptoDialectToJasminCom` →
`emitAbiOrchMem`). Only the `reifyLowCT%` macro is bypassed; the downstream
front (the part `decaps_full_kat.lean` and friends exercise) is identical.

## Pure-Lean surface

```lean
noncomputable def jhashLean (z : MlSeed) (ct : MlCipher) : MlMsg :=
  mlk_jhash_mem z ct
```

The reifier maps `MlSeed ↦ .TBytes 32`, `MlCipher ↦ .TBytes 1088` (via
`leanTypeToTowerType`), so the reflected arg context is `[.TBytes 32, .TBytes
1088]` and the result is `.TBytes 32`. `encodeTy` then gives `memref 4`
(32 bytes), `memref 136` (1088 bytes), `memref 4` (32 bytes); the u64 front
sends each `memref n` to `stackArr 64 n`; `emitAbiOrchMem` renders **every**
`stackArr` as a raw `reg u64` caller-memory pointer — the all-`reg u64` shape of
the formosa leaf.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The opaque op

`mlk_jhash_mem z ct = SHAKE256(z ‖ ct, 32)`. Homogeneous-shaped to the reifier's
let-chain walker: a binary leaf over byte buffers ending the chain. We reuse the
existing `MlSeed` (`.TBytes 32`) and `MlCipher` (`.TBytes 1088`) surface types,
and return `MlMsg` (`.TBytes 32`) for the 32-byte digest. -/

/-- ML-KEM FO implicit-rejection "J" hash: `Kbar = SHAKE256(z ‖ ct, 32)` where
    `z` is the 32-byte rejection seed and `ct` the 1088-byte ciphertext. Lowered
    to the all-`reg u64` formosa leaf `_shake256_1120_32` via the memory-pointer
    ABI emit mode. -/
axiom mlk_jhash_mem : MlSeed → MlCipher → MlMsg

/-! ## 2. `@[rust_cmd_pattern]` registration

Leaf-call name `jhash_mem` (a thin shim in `include/jhash_mem_shim.jinc` that
wraps the void formosa `_shake256_1120_32(out, in0, in1)` and returns `out`,
adapting it to the emit mode's `out = leaf(out, …)` return convention). Arity 2
(the two inputs `z`, `ct`); `towerType := .TBytes 32` sets only the 32-byte
destination — the arg sizes come from the caller's `VarMap`. -/

/-- Register `mlk_jhash_mem` in the dynamic reifier registry. The emitted leaf
    call is `jhash_mem` (the return-style shim around `_shake256_1120_32`). -/
@[rust_cmd_pattern]
def mlkJhashMemPattern : CatCrypt.Crypto.Jasmin.LowCTReflect.LowCTPattern where
  name      := "jhash_mem"
  fnHead    := ``mlk_jhash_mem
  arity     := 2
  towerType := .TBytes 32

/-! ## 3. Pure-Lean function + reified form -/

/-- The ML-KEM FO "J" hash authored as a **pure Lean function** over the opaque
    byte-buffer surface: one leaf call `mlk_jhash_mem z ct`. This is the value
    `reifyLowCT%` would reflect (and `jhashBody` is the `LowCT` it would
    produce); see the §"Reflection→front gap" note. -/
noncomputable def jhashLean (z : MlSeed) (ct : MlCipher) : MlMsg :=
  mlk_jhash_mem z ct

/-- The byte-buffer tower type of the rejection seed `z` (32 bytes). -/
def zTowerType : TowerType := .TBytes 32
/-- The byte-buffer tower type of the ciphertext `ct` (1088 bytes). -/
def ctTowerType : TowerType := .TBytes 1088

/-- The `LowCT` body the reifier *would* produce for `jhashLean` (built by
    hand because the `@[rust_cmd_pattern]` registry is not wired into
    `reifyChain` — see the module docstring). Exactly the `reifyChain`
    final-op shape: `RSeq RSkip (RCall "jhash_mem" __result [z, ct])`, with the
    leaf name `"jhash_mem"` and dest tower type `.TBytes 32` taken from the
    registered `mlkJhashMemPattern`. -/
def jhashBody : LowCT :=
  .RSeq .RSkip
    (.RCall "jhash_mem"
      { locVar := "__result", locSrc := mlkJhashMemPattern.towerType }
      [ { locVar := "z",  locSrc := zTowerType }
      , { locVar := "ct", locSrc := ctTowerType } ])

/-- The reified-func bundle, assembled by hand from `jhashBody` (same fields
    `reifyLowCT%` would emit: arg list with tower types, the body, and the
    return name `__result`). The `bench/mlkem_compare` driver consumes
    `.body` / `.retName` exactly as it would a `reifyLowCT%` output. -/
def jhashReified : ReifiedFunc :=
  { args    := [("z", zTowerType), ("ct", ctTowerType)]
    body    := jhashBody
    retName := "__result" }

-- Inspect the reified form at elaboration time.
#eval jhashReified.args.map Prod.fst              -- [z, ct]
#eval jhashReified.args.map (fun p => repr p.2)   -- [TBytes 32, TBytes 1088]
#eval jhashReified.retName                        -- __result
open Lean in
#eval show Lean.MetaM _ from do  -- the @[rust_cmd_pattern] entry is registered
  LowCTPattern.taggedDecls  -- expect #[…mlkJhashMemPattern]

end CatCrypt.Crypto.Jasmin.LowCTReflect
