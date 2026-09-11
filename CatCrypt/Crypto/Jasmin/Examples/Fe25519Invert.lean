/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# fe25519_invert authored as a Lean `LowCT` AST.

This is Phase 2 of the "extend the IR" plan: take a hand-coded Rust
function from `curve25519-jasmin-rs/src/mont_to_edwards.rs` and
re-express it as a verified `LowCT` so that the emitted Rust is
covered by the `JasminToRustEmitSimulates.ppFunDecl_simulates`
discipline (one named axiom `RustcExec_correct`, per-constructor
printer reflexivity).

The function computes `out := a^(p-2) mod p`, `p = 2^255 - 19`, via the
standard 254-square + 11-multiplication addition chain (Bernstein /
dalek / libjade-equivalent recipe).

Leaves used (declared external; the call sites correspond to the
existing `fe25519_mul` / `fe25519_sqr` shim in
`curve25519-jasmin-rs/src/ed25519_rustcmd/fe25519_portable.rs` and
`fe25519_limbs.rs`):
  - `fe25519_mul : (out a b : TFp25519) → unit`
  - `fe25519_sqr : (out a   : TFp25519) → unit`

These are RCall sites: each writes to `dest`, reads from `args`.
The borrow checker (`borrowOk`) requires `dest ∉ args`; we satisfy
this by using a scratch `tmp` slot for the "repeated squaring"
inner loop and copying back to the named accumulator each iteration.

-/
module

public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.RustEmit


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1.  Helpers -/

/-- A `TFp25519` slot. -/
def fp (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TFp25519 }

/-- `RCall "fe25519_sqr" (fp dst) [fp src]`: `dst := src^2`. -/
def sqr (dst src : String) : LowCT :=
  LowCT.RCall "fe25519_sqr" (fp dst) [fp src]

/-- `RCall "fe25519_mul" (fp dst) [fp a, fp b]`: `dst := a · b`. -/
def mul (dst a b : String) : LowCT :=
  LowCT.RCall "fe25519_mul" (fp dst) [fp a, fp b]

/-- `n` squarings of `acc` (in place), via the bounded for-loop.

    Uses a separate scratch `scratch` slot to avoid the alias
    `fe25519_sqr(&mut tmp, &tmp)` which the borrow checker rejects.
    Body each iteration:
        scratch := acc^2
        acc     := scratch          (verified copy leaf)
    After `n` iterations, `acc` holds the n-th iterated square. -/
def sqrN (n : Nat) (acc scratch : String) : LowCT :=
  LowCT.RFor "_i" n
    (LowCT.RSeq
      (sqr scratch acc)
      (LowCT.RCall "fe25519_copy" (fp acc) [fp scratch]))

/-- Sequence two commands. -/
def seq2 (c1 c2 : LowCT) : LowCT := LowCT.RSeq c1 c2

/-- Sequence a list of commands left-to-right.  Empty list → `RSkip`. -/
def seqN : List LowCT → LowCT
  | []      => LowCT.RSkip
  | [c]     => c
  | c :: cs => LowCT.RSeq c (seqN cs)

/-! ## §2.  fe25519_invert body

The classical chain (matches dalek's `Fe51::invert`):

      z2     = a^2                                  -- 1 sqr
      t      = z2^4                                 -- 2 sqr
      z9     = t · a                                -- 1 mul
      z11    = z9 · z2                              -- 1 mul
      t      = z11^2                                -- 1 sqr
      z2_5_0 = t · z9                               -- 1 mul     [a^31]
      t      = z2_5_0^32                            -- 5 sqr
      z2_10_0= t · z2_5_0                           -- 1 mul     [a^(2^10-1)]
      t      = z2_10_0^1024                         -- 10 sqr
      z2_20_0= t · z2_10_0                          -- 1 mul     [a^(2^20-1)]
      t      = z2_20_0^(2^20)                       -- 20 sqr
      z2_40_0= t · z2_20_0                          -- 1 mul     [a^(2^40-1)]
      t      = z2_40_0^(2^10)                       -- 10 sqr
      z2_50_0= t · z2_10_0                          -- 1 mul     [a^(2^50-1)]
      t      = z2_50_0^(2^50)                       -- 50 sqr
      z2_100_0=t · z2_50_0                          -- 1 mul     [a^(2^100-1)]
      t      = z2_100_0^(2^100)                     -- 100 sqr
      t2     = t · z2_100_0                         -- 1 mul     [a^(2^200-1)]
      t      = t2^(2^50)                            -- 50 sqr
      t3     = t · z2_50_0                          -- 1 mul     [a^(2^250-1)]
      t      = t3^32                                -- 5 sqr
      out    = t · z11                              -- 1 mul     [a^(p-2)]

Total: 1+2+1+5+10+20+10+50+100+50+5 = 254 squarings, 11 multiplies. -/

def fe25519InvertBody : LowCT :=
  seqN
    [ -- slot declarations: tmp + 11 named intermediates
      LowCT.RLetZero "tmp"      TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "scratch"  TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z2"       TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z9"       TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z11"      TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z2_5_0"   TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z2_10_0"  TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z2_20_0"  TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z2_40_0"  TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z2_50_0"  TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "z2_100_0" TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "t2"       TowerType.TFp25519 LowCT.RSkip,
      LowCT.RLetZero "t3"       TowerType.TFp25519 LowCT.RSkip,
      -- z2 = a^2
      sqr "z2" "a",
      -- tmp = z2^4 = a^8  (two squarings, ping-pong via scratch)
      sqr "tmp" "z2",
      sqr "scratch" "tmp",
      LowCT.RCall "fe25519_copy" (fp "tmp") [fp "scratch"],
      -- z9 = tmp · a    -- after this tmp holds a^8
      mul "z9" "tmp" "a",
      -- z11 = z9 · z2
      mul "z11" "z9" "z2",
      -- tmp = z11^2
      sqr "tmp" "z11",
      -- z2_5_0 = tmp · z9
      mul "z2_5_0" "tmp" "z9",
      -- tmp = z2_5_0^32   (5 squarings)
      sqr "tmp" "z2_5_0",
      sqrN 4 "tmp" "scratch",
      -- z2_10_0 = tmp · z2_5_0
      mul "z2_10_0" "tmp" "z2_5_0",
      -- tmp = z2_10_0^1024  (10 squarings)
      sqr "tmp" "z2_10_0",
      sqrN 9 "tmp" "scratch",
      -- z2_20_0 = tmp · z2_10_0
      mul "z2_20_0" "tmp" "z2_10_0",
      -- tmp = z2_20_0^(2^20)  (20 squarings)
      sqr "tmp" "z2_20_0",
      sqrN 19 "tmp" "scratch",
      -- z2_40_0 = tmp · z2_20_0
      mul "z2_40_0" "tmp" "z2_20_0",
      -- tmp = z2_40_0^(2^10)  (10 squarings)
      sqr "tmp" "z2_40_0",
      sqrN 9 "tmp" "scratch",
      -- z2_50_0 = tmp · z2_10_0
      mul "z2_50_0" "tmp" "z2_10_0",
      -- tmp = z2_50_0^(2^50)  (50 squarings)
      sqr "tmp" "z2_50_0",
      sqrN 49 "tmp" "scratch",
      -- z2_100_0 = tmp · z2_50_0
      mul "z2_100_0" "tmp" "z2_50_0",
      -- tmp = z2_100_0^(2^100)  (100 squarings)
      sqr "tmp" "z2_100_0",
      sqrN 99 "tmp" "scratch",
      -- t2 = tmp · z2_100_0
      mul "t2" "tmp" "z2_100_0",
      -- tmp = t2^(2^50)  (50 squarings)
      sqr "tmp" "t2",
      sqrN 49 "tmp" "scratch",
      -- t3 = tmp · z2_50_0
      mul "t3" "tmp" "z2_50_0",
      -- tmp = t3^32  (5 squarings)
      sqr "tmp" "t3",
      sqrN 4 "tmp" "scratch",
      -- out = tmp · z11
      mul "out" "tmp" "z11" ]

/-! ## §3.  Function envelope + emitter -/

/-- Input parameter: `a : &[u8; 40]` (the 40-byte canonical TFp25519 slot). -/
def params : List Located := [ fp "a" ]
/-- Output parameter: `out : &mut [u8; 40]`. -/
def results : List Located := [ fp "out" ]

/-- The Rust source string for `fe25519_invert`. -/
def emitFe25519Invert : String :=
  ppRustFunction "fe25519_invert" params results fe25519InvertBody

/-- IO driver: write the emitted source to `/tmp/fe25519_invert.rs`. -/
def runEmit : IO Unit := do
  let outPath := "/tmp/fe25519_invert.rs"
  IO.FS.writeFile outPath emitFe25519Invert
  IO.println s!"wrote {outPath}"
  IO.println s!"({(emitFe25519Invert.length)} bytes)"

end CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert
