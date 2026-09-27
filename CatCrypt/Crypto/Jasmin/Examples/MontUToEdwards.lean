/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# `mont_u_to_edwards_compressed` (happy-path core) as a Lean `LowCT` AST.

Source: `curve25519-jasmin-rs/src/mont_to_edwards.rs::mont_u_to_edwards_compressed`.

The full function performs

```
y = (u - 1) * (u + 1)^(-1) mod p
output = encode_y(y) with bit 255 = sign_bit
return None if u + 1 == 0
```

The IR does NOT expose byte-level bit-twiddling for the sign-bit OR, nor
a clean Option-typed return for the rejection.  We therefore factor:

  * The AST below covers the FIELD-ARITHMETIC happy path: given an input
    `u : TFp25519`, produce both `y_out : TFp25519` and `den_out : TFp25519`.
  * The Rust shim does the `[u8; 32]` <-> `Fp25519` boundary, the zero
    check on `den_out` (rejection), and the sign-bit OR on `y_out`'s
    encoded bytes.

This split matches the spec note "If neither fits cleanly, factor the
conditional out to the Rust shim and have the AST cover only the happy
path."

## Leaves used

  * `fe25519_sub_then_carry  (out a b)`  — `out := carry(a - b)`, tight.
  * `fe25519_add_then_carry  (out a b)`  — `out := carry(a + b)`, tight.
  * `fe25519_mul             (out a b)`  — `out := a · b`,         tight.
  * `fe25519_invert          (out a)`    — `out := a^(p-2)`.

Each is realised in the consumer Rust module as a thin wrapper over
fiat-crypto's `carry_sub` / `carry_add` / `carry_mul` and the
Lean-emitted `fe25519_invert` (composes cleanly: AST calls AST).

## Constants

`ONE : TFp25519` (the field element 1) is built inline via
`RLetZero` (zero-filled) + `RLimbStore one 0 1` (write 1 to limb 0).
The fiat-crypto tight representation uses radix-2^51 with all limbs
< 2^51, so the literal `(1, 0, 0, 0, 0)` is a valid tight value
representing the integer 1.
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTExec
public import CatCrypt.Crypto.Jasmin.RustEmit


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards

open CatCrypt.Crypto.Jasmin.LowCT

/-- A `TFp25519` slot at the given variable name. -/
def fp (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TFp25519 }

/-! ## §1.  Body -/

/--
Body of the happy-path core.  Reads input `u : TFp25519`; writes
`y_out : TFp25519` and `den_out : TFp25519`.

Steps:
  1. Build the constant `1 : TFp25519` in a local `one` slot.
  2. `num     := carry(u - 1)`
  3. `den     := carry(u + 1)`              (local intermediate)
  4. `inv_den := den^(p-2)`                 -- via Lean-emitted `fe25519_invert`
  5. `y_out   := num * inv_den`
  6. `den_out := den`                       -- copy local `den` to output
                                            -- (exposed so the shim can detect
                                            -- the rejection case u + 1 == 0)

Notes:
  * `den` is a LOCAL TFp25519 (not the output `den_out`).  This avoids
    re-reading the output `den_out` as an immutable arg to `fe25519_invert`,
    which the emitter's `rustLocRef` would render as `&den_out`
    (= `&&mut Fp25519`) — not the `&Fp25519` the leaf expects.  Passing
    the local `&den` works under standard reborrow rules.
  * The final `fe25519_copy` leaf populates `den_out` from `den`.
-/
def montUToEdwardsBody : LowCT :=
  -- §1.1 Locals: one (constant 1), num, den (intermediate), inv_den.
  LowCT.RLetZero "one"     TowerType.TFp25519 $
  LowCT.RLetZero "num"     TowerType.TFp25519 $
  LowCT.RLetZero "den"     TowerType.TFp25519 $
  LowCT.RLetZero "inv_den" TowerType.TFp25519 $
    -- §1.2  Initialise `one` to the field element 1 via a leaf call.
    --       (Cannot use `RLimbStore` directly: the emitter renders it as
    --       `one.limbs[0] = 1u64`, but fiat-crypto's tight type is a tuple
    --       struct `Fp25519(pub [u64; 5])` with no `limbs` named field.
    --       Consumer-side shim provides `fe25519_set_one` as a 1-line
    --       wrapper writing `out.0[0] = 1; out.0[1..4] = 0`.)
    LowCT.RSeq (LowCT.RCall "fe25519_set_one" (fp "one") []) $
    -- §1.3  num := carry(u - 1)
    LowCT.RSeq (LowCT.RCall "fe25519_sub_then_carry" (fp "num")
                                [fp "u", fp "one"]) $
    -- §1.4  den := carry(u + 1)
    LowCT.RSeq (LowCT.RCall "fe25519_add_then_carry" (fp "den")
                                [fp "u", fp "one"]) $
    -- §1.5  inv_den := den^(p-2)  (via Lean-emitted fe25519_invert)
    LowCT.RSeq (LowCT.RCall "fe25519_invert" (fp "inv_den")
                                [fp "den"]) $
    -- §1.6  y_out := num · inv_den
    LowCT.RSeq (LowCT.RCall "fe25519_mul" (fp "y_out")
                                [fp "num", fp "inv_den"]) $
    -- §1.7  den_out := den   (expose denominator to the shim)
    LowCT.RCall "fe25519_copy" (fp "den_out") [fp "den"]

/-! ## §2.  Function envelope + emitter -/

/-- Input: `u : &Fp25519`. -/
def params : List Located := [ fp "u" ]
/-- Outputs: `y_out : &mut Fp25519`, `den_out : &mut Fp25519`. -/
def results : List Located := [ fp "y_out", fp "den_out" ]

/-- The Rust source string for `mont_u_to_edwards_field`. -/
def emitMontUToEdwards : String :=
  ppRustFunction "mont_u_to_edwards_field" params results montUToEdwardsBody

/-- IO driver: write the emitted source to `/tmp/mont_u_to_edwards_field.rs`. -/
def runEmit : IO Unit := do
  let outPath := "/tmp/mont_u_to_edwards_field.rs"
  IO.FS.writeFile outPath emitMontUToEdwards
  IO.println s!"wrote {outPath}"
  IO.println s!"({emitMontUToEdwards.length} bytes)"
  IO.println "---"
  IO.println emitMontUToEdwards

end CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards
