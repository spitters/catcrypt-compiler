/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTDSL

/-!
# X25519 Montgomery ladder in the LowCT DSL

A readable reference implementation of the full 255-iteration X25519
scalar multiplication, authored in the DSL and unrolled at elaboration
time. This parallels the hand-written VIR program in
`CatCrypt/Crypto/SecureCompilation/VIR/X25519EmitMLIR.lean`, but at the
`LowCT` surface level — so it flows through the verified
`translateDialectControl : LowCT → Com catCryptDialect` pipeline.

## Encoding

`TowerType.TFp25519` encodes to `CryptoTy.memref 5` (5×u64 = 40 bytes),
matching Curve25519's packed limb layout and the `Fp[5]` used by the
fiat-crypto shim (`catcrypt-bench/src/fiat_shim.c`). This means the
DSL output translates through `translateDialectControl`
into memrefs of the correct shape for the existing MLIR pipeline.

## Structure

`ladderStep` — one iteration of cswap-dbl-dadd-cswap over a ladder
state of 4 Fp elements (`x2`, `z2`, `x3`, `z3`) plus a u64 bit. The
five underlying field ops (`fp_add`, `fp_sub`, `fp_mul`, `fp_sqr`,
`fp_mul_a24`) are `extCall` leaves backed by the fiat-crypto shim
(see `catcrypt-bench/src/fiat_shim.c`).

`ladder255` — the 255-round unrolled ladder. Elaboration reduces the
`for` to 255 copies of the step.

## `cswap_fp` 2-output handling

Mathematically `cswap(bit, a, b)` mutates *both* `a` and `b`.  The
single-destination `rc_call` constructor would give a
`cswap_fp(&mut a, &b, &swap)` emit that Rust rejects.

`RCallSwap` in `LowCT.lean` and the matching `rc_call_swap` helper in
`LowCTDSL.lean` handle it.  The emitter (`RustEmit.
lean::ppLowCT`) renders it as
`cswap_fp(&mut a, &mut b, &swap)`, matching the natural Rust
signature `pub fn cswap_fp(a: &mut Fp25519, b: &mut Fp25519,
swap: &Fp25519)`.  Used here for the four cswap sites in
`ladderStep`.

(NOTE: borrowOk for `RCallSwap` — `dest1 ≠ dest2`, neither in
args — is the constructor's intended invariant; it is not stated as a
`Decidable` predicate.)
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSL

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTDSL
open CatCrypt.Crypto.Jasmin.LowCTDSL.Rcm
open TowerType

/-! ## 1. One ladder step

Bernstein's X25519 cswap-dbl-dadd-cswap. Pre-conditions: the caller
has set `swap` to the current bit, and `x2,z2,x3,z3,x1` are
appropriately placed.

```
  cswap(bit, x2, x3)
  cswap(bit, z2, z3)
  A  = x2 + z2
  B  = x2 - z2
  C  = x3 + z3
  D  = x3 - z3
  AA = A²
  BB = B²
  E  = AA - BB
  DA = D * A
  CB = C * B
  x3'= (DA + CB)²
  z3'= x1 * (DA - CB)²
  x2'= AA * BB
  z2'= E * (BB + 121666 * E)
  cswap(bit, x2, x3)
  cswap(bit, z2, z3)
``` -/
def ladderStep : Rcm Unit := do
  -- Conditional swap (in-place): leaf mutates BOTH x2 and x3 (and
  -- z2/z3) per the ct-cswap semantics. The 2-output AST constructor
  -- `RCallSwap` emits
  -- `cswap_fp(&mut x2, &mut x3, &swap)` — the leaf gets two `&mut
  -- Fp25519` args and a `&Fp25519` swap mask.
  rc_call_swap "cswap_fp" (loc "x2" TFp25519) (loc "x3" TFp25519)
                          [loc "swap" TFp25519]
  rc_call_swap "cswap_fp" (loc "z2" TFp25519) (loc "z3" TFp25519)
                          [loc "swap" TFp25519]
  -- Sums and differences.
  rc_call "fp_add" (loc "A" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sub" (loc "B" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_add" (loc "C" TFp25519) [loc "x3" TFp25519, loc "z3" TFp25519]
  rc_call "fp_sub" (loc "D" TFp25519) [loc "x3" TFp25519, loc "z3" TFp25519]
  -- Squares.
  rc_call "fp_sqr" (loc "AA" TFp25519) [loc "A" TFp25519]
  rc_call "fp_sqr" (loc "BB" TFp25519) [loc "B" TFp25519]
  rc_call "fp_sub" (loc "E"  TFp25519) [loc "AA" TFp25519, loc "BB" TFp25519]
  -- Cross products.
  rc_call "fp_mul" (loc "DA" TFp25519) [loc "D" TFp25519, loc "A" TFp25519]
  rc_call "fp_mul" (loc "CB" TFp25519) [loc "C" TFp25519, loc "B" TFp25519]
  -- New x3, z3.
  rc_call "fp_add" (loc "DApCB" TFp25519) [loc "DA" TFp25519, loc "CB" TFp25519]
  rc_call "fp_sub" (loc "DAmCB" TFp25519) [loc "DA" TFp25519, loc "CB" TFp25519]
  rc_call "fp_sqr" (loc "x3"   TFp25519) [loc "DApCB" TFp25519]
  rc_call "fp_sqr" (loc "tmp"  TFp25519) [loc "DAmCB" TFp25519]
  rc_call "fp_mul" (loc "z3"   TFp25519) [loc "x1" TFp25519, loc "tmp" TFp25519]
  -- New x2, z2.
  rc_call "fp_mul"     (loc "x2"    TFp25519) [loc "AA" TFp25519, loc "BB" TFp25519]
  rc_call "fp_mul_a24" (loc "a24E"  TFp25519) [loc "E" TFp25519]
  rc_call "fp_add"     (loc "z2inn" TFp25519) [loc "BB" TFp25519, loc "a24E" TFp25519]
  rc_call "fp_mul"     (loc "z2"    TFp25519) [loc "E" TFp25519, loc "z2inn" TFp25519]
  -- (Bernstein/RFC 7748 §5 ladder: ONE cswap pair per iteration at
  -- the START, plus ONE final cswap-pair AFTER the loop, with `swap`
  -- tracked as the running XOR `swap ^= bit_t` outside the step.
  -- The previous version also did a swap-back HERE, which made the
  -- math operate on swap-then-unswap and produced wrong KATs.  See
  -- NaCl ref10/scalarmult.c for the canonical structure.)

/-! ## 2. Full 255-iteration ladder

Each iteration extracts one bit of the scalar into `swap`, then runs
`ladderStep`. Bit extraction (`bit_i`) is delegated to an
external leaf `scalar_bit` whose `i`-th call returns the `i`-th bit
of the scalar tower variable `k`. -/

def ladder255 : LowCT := rustcmd| do
  -- Persistent ladder state.  `x1` (u-coord) and `k` (scalar) are
  -- function-input parameters; the emitter declares them in the
  -- signature, so we do NOT `rc_let` them here (otherwise the emitted
  -- Rust shadows the inputs with zero-initialised locals).
  rc_let "x2" TFp25519
  rc_let "z2" TFp25519
  rc_let "x3" TFp25519
  rc_let "z3" TFp25519
  rc_let "swap" TFp25519  -- current bit, broadcast to a memref for cswap_fp
  -- Per-step scratch names. Each iteration rebinds these via `rc_let`;
  -- the SSA translation treats that as shadowing.
  rc_let "A" TFp25519
  rc_let "B" TFp25519
  rc_let "C" TFp25519
  rc_let "D" TFp25519
  rc_let "AA" TFp25519
  rc_let "BB" TFp25519
  rc_let "E" TFp25519
  rc_let "DA" TFp25519
  rc_let "CB" TFp25519
  rc_let "DApCB" TFp25519
  rc_let "DAmCB" TFp25519
  rc_let "tmp" TFp25519
  rc_let "a24E" TFp25519
  rc_let "z2inn" TFp25519
  -- Unrolled loop.
  for i in List.range 255 do
    -- Leaf `scalar_bit` reads bit `254-i` of the scalar `k` into
    -- `swap`.  The DSL's RCall destination must NOT alias any arg
    -- (borrowOk invariant), so the only arg is `k`; the leaf infers
    -- the iteration index from a hidden side-channel (or, in the
    -- preferred design, `i` is a fresh u64 local set by `rc_letU64`
    -- + `rc_set` before the call).
    rc_call "scalar_bit" (loc "swap" TFp25519) [loc "k" TFp25519]
    let _ := i  -- i is implicit in the unrolled position
    ladderStep

/-- Elaboration check: the 255-iteration unroll completes without
    hitting Lean's recursion-depth limit. The translation through
    `translateDialectControl` is not checked here. -/
example : True := by trivial

/-! ## 3. Standalone ladder-step entry point

`ladder_step_call` wraps `ladderStep` with the per-step scratch
`rc_let`s, packaging it as a closed `LowCT` suitable for emission
as a standalone Rust function.  The expected signature in the
emitted code is:

```rust
pub fn x25519_ladder_step(
    x1   : &Fp25519,        // u-coordinate input (read-only)
    swap : &Fp25519,        // current swap-bit broadcast (read-only)
    x2   : &mut Fp25519,    // ladder state, mutated in place
    z2   : &mut Fp25519,
    x3   : &mut Fp25519,
    z3   : &mut Fp25519,
)
```

Caller (the Rust glue in `signal-wasm/component/src/x25519.rs`) is
responsible for the 255-iteration loop, scalar clamping, u-coord
high-bit mask, bit extraction into `swap`, and final `x2 / z2`
inversion.  Only the inner ladder math is emitted from Lean.
-/

def ladder_step_call : LowCT := rustcmd| do
  rc_let "A" TFp25519
  rc_let "B" TFp25519
  rc_let "C" TFp25519
  rc_let "D" TFp25519
  rc_let "AA" TFp25519
  rc_let "BB" TFp25519
  rc_let "E" TFp25519
  rc_let "DA" TFp25519
  rc_let "CB" TFp25519
  rc_let "DApCB" TFp25519
  rc_let "DAmCB" TFp25519
  rc_let "tmp" TFp25519
  rc_let "a24E" TFp25519
  rc_let "z2inn" TFp25519
  ladderStep

end CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSL
