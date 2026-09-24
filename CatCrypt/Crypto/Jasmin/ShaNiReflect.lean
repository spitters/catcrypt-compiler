/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Intel SHA-NI reflect surface — SHA-256 round/msg leaves through the verified front

This file is the SHA-256 hardware-extension analogue of `UovReflect.lean`:
it adds Intel SHA-NI specific opaque leaves and `LowCTPattern`
registrations so that a pure-Lean SHA-256 compression round can be
lifted through the verified compiler chain `LowCT → Com catCryptDialect →
Jasmin`, **without** editing `LowCTReflect.lean`'s `knownOps` table.

## SHA-256 compression with SHA-NI

Intel SHA-NI (Intel SDM Vol. 2) provides three SHA-256-specific
intrinsics:

* `#SHA256RNDS2` — two SHA-256 rounds at a time. Operands: previous
  state half `(c d g h)`, current state half `(a b e f)`, and a 128-bit
  `w + k` block (two 32-bit `Wi + Ki` words). Output: updated state half.

* `#SHA256MSG1` — message schedule helper 1: given `w[i-16..i-13]` +
  `w[i-12..i-9]`, output `w[i-16..i-13] + σ0(w[i-15..i-12])`.

* `#SHA256MSG2` — message schedule helper 2: given the running state +
  the most-recent four `w` words, output the next four `w` words via
  `σ1(w[i-2..i+1]) + ...`.

Together the three intrinsics implement one SHA-256 compression block at
~3-4× the cost of pure scalar/AVX2 — the headline win HACL\* AES-GCM and
OpenSSL SHA-256 both build on.

We model each intrinsic as one opaque leaf at `TBytes 16` (128-bit
packed `xmm`-resident state half / message-schedule quad):

| Lean name             | Leaf name (.jazz)             | TowerType   |
|-----------------------|-------------------------------|-------------|
| `shani_sha256_rnds2`  | `shani_sha256_rnds2`          | `TBytes 16` |
| `shani_sha256_msg1`   | `shani_sha256_msg1`           | `TBytes 16` |
| `shani_sha256_msg2`   | `shani_sha256_msg2`           | `TBytes 16` |

The verified front sees only the opaque leaf names and the TBytes
signatures. The per-intrinsic *semantics* — that each leaf computes its
documented SHA-256 function — is the hardware-leaf trust assumption,
**factored and discharged** in
`CatCrypt.Crypto.SecureCompilation.X86Backend.HardwareISAAxioms`
(`HardwareISA.shaNi`, tier `fipsClosed`): the owned SHA-NI model
(`ShaNiEmit.sha256rnds2_lane` / `sha256msg1_lane` / `sha256msg2_lane`)
denotes *definitionally* (`rfl`) to the FIPS-180-4 SHA-256 round and
message-schedule body — see `HardwareISA.shaNi_discharge`. This is the
strongest validation tier (pinned to the cryptographic standard itself),
so these leaves are anchored to the standard in addition to SDM prose and
KATs.

## Reflection→front gap (same as `UovReflect` / `FalconReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`. We follow the
established pattern: define the pure-Lean functions for documentation,
register each leaf via `@[rust_cmd_pattern]`, then **hand-build the
`LowCT`** the reifier *would* produce.

## References

* Intel SDM Vol. 2 — `SHA256RNDS2`, `SHA256MSG1`, `SHA256MSG2`
* NIST FIPS-180-4 §6.2 — SHA-256 compression function
* `bench/sha2_compare/sha2_emit.lean` — sibling emit
  (single-block SHA-256 compression Com, hand-built, verified emit)
* `bench/hmac_shani_compare/hmac_shani_emit.lean` — string-templated
  emit outside the verified chain
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling SIMD-leaf reference
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque SHA-NI surface types

All SHA-NI intrinsics operate on 128-bit packed XMM operands. We encode
each as `.TBytes 16` (`memref 2`). -/

opaque ShaNiBlock.Impl : NonemptyType.{0}
/-- A 128-bit packed XMM operand: either a SHA-256 state half
    (`a b e f` or `c d g h`) or a message-schedule quad (four `Wi`
    words). Opaque; concrete leaves implement the SHA-NI intrinsics. -/
def ShaNiBlock : Type := ShaNiBlock.Impl.type
instance : Nonempty ShaNiBlock := ShaNiBlock.Impl.property
/-- Axiomatic inhabitant. -/ axiom ShaNiBlock.default : ShaNiBlock
noncomputable instance : Inhabited ShaNiBlock := ⟨ShaNiBlock.default⟩

/-! ## 2. SHA-NI leaves (opaque constants = jasmin function symbols) -/

/-- `#SHA256RNDS2`: two SHA-256 compression rounds. Inputs: previous
    state half (`c d g h`), current state half (`a b e f`), and the
    packed `W + K` quad for these two rounds. Output: the next pair of
    state-half updates. -/
noncomputable opaque shani_sha256_rnds2 : ShaNiBlock → ShaNiBlock → ShaNiBlock → ShaNiBlock

/-- `#SHA256MSG1`: message schedule helper 1. -/
noncomputable opaque shani_sha256_msg1 : ShaNiBlock → ShaNiBlock → ShaNiBlock

/-- `#SHA256MSG2`: message schedule helper 2. -/
noncomputable opaque shani_sha256_msg2 : ShaNiBlock → ShaNiBlock → ShaNiBlock

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `shani_sha256_rnds2` → leaf `shani_sha256_rnds2`. -/
@[rust_cmd_pattern]
def shaNiSha256Rnds2Pattern : LowCTPattern where
  name      := "shani_sha256_rnds2"
  fnHead    := ``shani_sha256_rnds2
  arity     := 3
  towerType := .TBytes 16

/-- Register `shani_sha256_msg1` → leaf `shani_sha256_msg1`. -/
@[rust_cmd_pattern]
def shaNiSha256Msg1Pattern : LowCTPattern where
  name      := "shani_sha256_msg1"
  fnHead    := ``shani_sha256_msg1
  arity     := 2
  towerType := .TBytes 16

/-- Register `shani_sha256_msg2` → leaf `shani_sha256_msg2`. -/
@[rust_cmd_pattern]
def shaNiSha256Msg2Pattern : LowCTPattern where
  name      := "shani_sha256_msg2"
  fnHead    := ``shani_sha256_msg2
  arity     := 2
  towerType := .TBytes 16

/-! ## 4. SHA-NI tower-type abbreviations -/

/-- Tower type of a 128-bit SHA-NI XMM operand (`memref 2`). -/
def shaNiBlockTowerType : TowerType := .TBytes 16

def locShaNi (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean SHA-NI kernels — the specs -/

/-- One `#SHA256RNDS2` call (two SHA-256 rounds). -/
noncomputable def shaNiRnds2Lean (prev cur wk : ShaNiBlock) : ShaNiBlock :=
  shani_sha256_rnds2 prev cur wk

/-- One `#SHA256MSG1` call. -/
noncomputable def shaNiMsg1Lean (a b : ShaNiBlock) : ShaNiBlock :=
  shani_sha256_msg1 a b

/-- One `#SHA256MSG2` call. -/
noncomputable def shaNiMsg2Lean (a b : ShaNiBlock) : ShaNiBlock :=
  shani_sha256_msg2 a b

/-! ## 6. Hand-built `LowCT` bodies (the front-end input) -/

/-- The `LowCT` body for `shaNiRnds2Lean`. Shape:
    `RSeq RSkip (RCall "shani_sha256_rnds2" __result [prev, cur, wk])`. -/
def shaNiRnds2Body : LowCT :=
  let prev_l   := locShaNi "prev"     shaNiBlockTowerType
  let cur_l    := locShaNi "cur"      shaNiBlockTowerType
  let wk_l     := locShaNi "wk"       shaNiBlockTowerType
  let result_l := locShaNi "__result" shaNiBlockTowerType
  .RSeq .RSkip
    (.RCall "shani_sha256_rnds2" result_l [prev_l, cur_l, wk_l])

def shaNiRnds2Reified : ReifiedFunc :=
  { args    := [("prev", shaNiBlockTowerType),
                ("cur",  shaNiBlockTowerType),
                ("wk",   shaNiBlockTowerType)]
    body    := shaNiRnds2Body
    retName := "__result" }

/-- The `LowCT` body for `shaNiMsg1Lean`. -/
def shaNiMsg1Body : LowCT :=
  let a_l      := locShaNi "a"        shaNiBlockTowerType
  let b_l      := locShaNi "b"        shaNiBlockTowerType
  let result_l := locShaNi "__result" shaNiBlockTowerType
  .RSeq .RSkip
    (.RCall "shani_sha256_msg1" result_l [a_l, b_l])

def shaNiMsg1Reified : ReifiedFunc :=
  { args    := [("a", shaNiBlockTowerType), ("b", shaNiBlockTowerType)]
    body    := shaNiMsg1Body
    retName := "__result" }

/-- The `LowCT` body for `shaNiMsg2Lean`. -/
def shaNiMsg2Body : LowCT :=
  let a_l      := locShaNi "a"        shaNiBlockTowerType
  let b_l      := locShaNi "b"        shaNiBlockTowerType
  let result_l := locShaNi "__result" shaNiBlockTowerType
  .RSeq .RSkip
    (.RCall "shani_sha256_msg2" result_l [a_l, b_l])

def shaNiMsg2Reified : ReifiedFunc :=
  { args    := [("a", shaNiBlockTowerType), ("b", shaNiBlockTowerType)]
    body    := shaNiMsg2Body
    retName := "__result" }

/-! ## 7. Inspection -/

#eval shaNiRnds2Reified.args.map Prod.fst              -- [prev, cur, wk]
#eval shaNiRnds2Reified.args.length                    -- 3
#eval shaNiMsg1Reified.args.length                     -- 2
#eval shaNiMsg2Reified.args.length                     -- 2

end CatCrypt.Crypto.Jasmin.LowCTReflect
