/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTDSL
public import CatCrypt.Crypto.Jasmin.LowCTDSL

/-!
# SHA-512 compression function in the LowCT DSL (structural demo)

80 rounds of SHA-512, authored in the DSL and unrolled at elaboration.
The **structure** — message schedule + 80 round applications — fits in
~15 lines of Lean. The emitted `LowCT` has ~240 `extCall` nodes
(80 rounds + 64 schedule steps + setup) fully unrolled.

## What this demonstrates

- The "write loops, get straight-line output" pattern scales to 80
  rounds just as readily as X25519's 255.
- Per-round work (`Ch`, `Maj`, `Σ₀`, `Σ₁`, round constants K[t]) is
  pushed into `sha512_round` and `sha512_sched` leaves. The C
  implementations of those leaves are tiny — each is 5–10 lines of
  standard SHA-512 reference code.

## What this is NOT

- Not a semantic SHA-512 implementation. LowCT's scalar ops are
  limited (no native u64 XOR/rotate), so bit-manipulation is
  encapsulated inside the leaves. If you want a SHA-512 that is
  "fully through the verified pipeline" (no external bit-op leaves),
  extend `LowCT` with u64-bitop constructors or compile to MLIR's
  `arith` dialect directly.
- Not wired to a real state encoding yet. SHA-512's 8×u64 state is
  represented here as a single `TFp2` memref (96 bytes, enough for
  8 limbs with room to spare). A dedicated `TowerType.TShaState`
  variant (byteSize 64) is the clean future form.

The reference choice: **use libjade's SHA-512 as a single `extCall`
leaf** for Ed25519 interop (1 leaf, 1 block-size boundary, trust the
Jasmin proof). This file demonstrates the *alternative* — author
SHA-512 at the LowCT level — in case you want the whole thing
through the catCryptDialect→VIR→MLIR pipeline.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Examples.SHA512CompressDSL

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTDSL
open CatCrypt.Crypto.Jasmin.LowCTDSL.Rcm
open TowerType

/-! ## 1. SHA-512 compression — full 80-round unrolled

Convention:
- `H` : current hash state (8×u64, packed into a TFp2 memref).
- `M` : 16-word message block (packed into TFp2).
- `W_i` (i ∈ 0..79): expanded schedule words, one TU64 per slot.
- Round constants `K_t` and per-round σ/Σ bit-manip live inside the
  `sha512_round`/`sha512_sched` leaves (so they stay off the Lean
  source surface).

The schedule recurrence is `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`
for `t ∈ 16..79`; `W[0..15]` are copied from the block. -/
def sha512Compress : LowCT := rustcmd| do
  rc_let "H" TFp2    -- state (8 × u64 packed)
  rc_let "M" TFp2    -- message block (16 × u64 packed)
  -- Schedule words W[0..15] are the block; W[16..79] are derived.
  for i in List.range 16 do
    rc_call "sha512_sched_copy"
      (loc s!"W_{i}" TFp)  -- one-word container
      [loc "M" TFp2]
  for t in List.range (80 - 16) do
    let i := t + 16
    rc_call "sha512_sched_step"
      (loc s!"W_{i}" TFp)
      [loc s!"W_{i-2}" TFp, loc s!"W_{i-7}" TFp,
       loc s!"W_{i-15}" TFp, loc s!"W_{i-16}" TFp]
  -- 80 round applications. Each reads H + W[t], updates H in place.
  for t in List.range 80 do
    rc_call "sha512_round"
      (loc "H" TFp2)
      [loc s!"W_{t}" TFp]
  -- Fold result back into H (SHA-512 adds the input state to the
  -- round-updated state).
  rc_call "sha512_finalize_add"
    (loc "H" TFp2)
    [loc "H" TFp2]

/-- 80-round unroll produces a straight-line `LowCT` with:
      16 (copy) + 64 (sched) + 80 (round) + 1 (finalize) = 161 calls,
    each wrapped in an `RSeq`, plus the `rc_let` prelude (2 entries)
    and the final `RSkip`. Verifying with `rcSize` would exercise
    `native_decide` past its default recursion limit at this scale —
    we just confirm elaboration goes through. -/
example : sha512Compress ≠ .RSkip := by
  intro h
  -- `sha512Compress` starts with an `RLetZero`; if it were `RSkip` the
  -- constructors would clash. `nomatch` decides by reducing the WHNF.
  cases h

/-! ## 2. Why this reads cleanly

Compare — the same 80-round compress authored by hand:

```lean
-- Without DSL: 161 nested `.RSeq (.RCall …) _` blocks,
-- copy-pasted for each round. ~240 LoC.
def sha512_handwritten : LowCT :=
  .RLetZero "H" .TFp2 (.RLetZero "M" .TFp2 (
    .RSeq (.RCall "sha512_sched_copy" ⟨"W_0", .TFp, .TFp⟩ [⟨"M", .TFp2, .TFp2⟩])
      (.RSeq (.RCall "sha512_sched_copy" ⟨"W_1", .TFp, .TFp⟩ [⟨"M", .TFp2, .TFp2⟩])
        (.RSeq ... repeated 159 more times ...))))
```

The DSL version is ~15 lines. The compiled AST is the same. -/

end CatCrypt.Crypto.Jasmin.Examples.SHA512CompressDSL
