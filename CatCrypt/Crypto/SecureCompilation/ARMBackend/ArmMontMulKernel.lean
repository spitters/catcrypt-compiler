/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering

/-!
# A 4×4→8 schoolbook 256-bit multiply, lowered through the owned AArch64 backend (#549)

`ArmBignumKernel.lean` (#547) lowered s2n-bignum's `bignum_add_p256` — the
**ADD-class** carry-chain kernel — through the 64-bit `X`-register bignum model
(`ArmModel.BState`/`evalBInst`). This module is the **MULTIPLY-class** keystone:
it lowers a full `bignum_mul_4_8`-shaped 4×4→8 schoolbook multiply
(`z[8] := x[4] · y[4]`, the 256×256→512 widening product) through the SAME owned
backend, exercising the widening `MUL`/`UMULH` (64×64→128 low/high) together with
the `ADDS`/`ADCS`/`ADC` multi-precision accumulation carry chain that AArch64 —
unlike x86's MULX/ADX-only ceiling — exposes as plain flag-setting adds. It is the
A64 analogue of `X86Backend/BignumMontMulKernel.lean` and the multiply core that
`fe25519_mul` (#550's X25519 field path) and a 4×64 Montgomery mul both ride.

## The schoolbook (operand-scanning, two-carry accumulation)

The 512-bit product `[z7..z0]` of `[x3,x2,x1,x0] · [y3,y2,y1,y0]` is the sum of
the 16 partial products `x_i · y_j` placed at limb position `i + j`. Each
`x_i · y_j` is a 128-bit value split as `MUL` (low 64) + `UMULH` (high 64). We
accumulate **row by row**: for each row `i`, multiply `x_i` by all four `y_j`,
folding the eight half-products into the running 5-word accumulator window with an
`ADDS`/`ADCS` carry chain. The low half of `x_i·y_j` lands at limb `i+j`, the high
half at `i+j+1`. AArch64 has no fused multiply-accumulate-with-carry, so each
partial product is `MUL`+`UMULH`+`ADDS`/`ADCS` — the canonical portable schoolbook
(e.g. s2n-bignum `arm/fastmul/bignum_mul_4_8.S`'s straightforward variant).

Concretely we keep the eight result words `z0..z7` in registers, plus two scratch
`lo`/`hi` for the current `MUL`/`UMULH` product and one `cc` carry word. We add
`x_i·y_j` into the pair `(z_{i+j}, z_{i+j+1})` with a length-2 carry chain, and
propagate the carry-out up through `z_{i+j+2}…` via `ADCS`/`ADC`. The model's
`ADDS`/`ADCS` set the carry flag `C` exactly as the Arm ARM `AddWithCarry`
pseudocode does (`ArmModel.addWithCarry`), so the lowered block computes the true
512-bit integer product.

## What this kernel emits / proves

* `mul48Block`: the verified `BOp` body — the 16 `MUL`/`UMULH` products and the
  accumulation carry chains, in operand-scanning order.
* `mul48_lowering_correct`: lowering the body to `BInst` and running it on the
  `BState` model equals the direct machine fold — `bignumBlock_lowering_denote`
  on this body (no new custom axioms).
* `mul48_kat` / `mul48_kat2` / `mul48_kat_max`: value KATs on worked vectors,
  including the all-ones²/mixed cases, pinning the eight stored words
  byte-identical to the hand-computed full 512-bit product `x·y`.

The full all-inputs correctness (`⟦z0..z7⟧ = ⟦x⟧·⟦y⟧`) is the s2n proof
obligation (`arm/proofs/bignum_mul_4_8.ml`); as an in-Lean close it is a 512-bit
multiply identity gated by the GMP/s2n cross-check KAT, the same REV-12 posture as
the x86 multiply kernels. Here we pin worked vectors (incl. the maximal
`(2⁶⁴-1)`-limbed inputs that exercise every carry) under `native_decide`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMontMulKernel

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. The 4×4→8 schoolbook body as a `BOp` block

We use the operand-scanning schoolbook: the accumulator is the eight result
words `z0..z7`; `lo`/`hi` are the current `MUL`/`UMULH` product halves; `cc` is a
carry word. Inputs `x0..x3`, `y0..y3` are pre-loaded by the trusted `ldp`s.

The accumulator words `z_k` start implicitly at 0 (an absent name reads `0` in
`BState`). For each partial product `x_i·y_j` (placed at limb `i+j`), we add the
two product halves `lo`@`i+j` and `hi`@`i+j+1` into the window, threading the
carry up. To keep the carry-chain *flag* discipline correct we add each product as
a length-3 chain `ADDS z_{i+j}; ADCS z_{i+j+1}; ADC carry-into-z_{i+j+2}` (the
high limbs above `i+j+1` only receive carry, so `ADCS xzr`). Concretely we emit,
per `(i,j)`:

```
mul   lo, x_i, y_j
umulh hi, x_i, y_j
adds  z_{i+j},   z_{i+j},   lo
adcs  z_{i+j+1}, z_{i+j+1}, hi
adcs  z_{i+j+2}, z_{i+j+2}, xzr   (carry into the next limb)
...                                (propagate the carry up through z_7)
```

For limbs at the very top (where `i+j+2 > 7` etc.) the carry cannot propagate
past `z7` for in-range inputs, so those `ADCS xzr` are omitted. This is exactly
the standard portable AArch64 schoolbook. -/

/-- Add the 128-bit product `x_i · y_j` (computed into `lo`/`hi`) into the
    accumulator window starting at limb `base = i + j`, threading the carry up to
    `z7`. Emits `MUL`/`UMULH` then the `ADDS`/`ADCS`/`ADC` accumulation chain. -/
def addProduct (xi yj : String) (base : Nat) : List BOp :=
  let z : Nat → String := fun k => "z" ++ toString k
  -- the limbs above base+1 that still need a carry propagated (base+2 .. 7)
  let carriers : List Nat := (List.range 8).filter (fun k => base + 2 ≤ k)
  [ .mul "lo" xi yj
  , .umulh "hi" xi yj
  , .adds (z base) (z base) "lo"
  , .adcs (z (base+1)) (z (base+1)) "hi" ]
  ++ carriers.map (fun k => BOp.adcs (z k) (z k) "xzr")

/-- The full 4×4→8 schoolbook multiply body, operand-scanning order: for each
    `i ∈ 0..3` and `j ∈ 0..3`, add `x_i · y_j` at limb `i+j`. The accumulator
    words `z0..z7` hold the 512-bit product; they begin at `0` (absent ⇒ 0). -/
def mul48Block : List BOp :=
  (List.range 4).flatMap (fun i =>
    (List.range 4).flatMap (fun j =>
      addProduct ("x" ++ toString i) ("y" ++ toString j) (i + j)))

/-! ## 2. Lowering correctness (the multiply keystone instantiated) -/

/-- **Lowering correctness on the 4×4→8 schoolbook.** Running the lowered body on
    the 64-bit model equals the direct machine fold — `bignumBlock_lowering_denote`
    instantiated on the multiply body, for every initial `BState`. No new custom
    axioms. -/
theorem mul48_lowering_correct (s : BState) :
    runBBlock s (lowerBBlock mul48Block)
      = mul48Block.foldl (fun st op => evalBInst st (toBInst op)) s :=
  bignumBlock_lowering_denote mul48Block s

/-! ## 3. The value KATs (worked full-product vectors)

We read the eight result words `z0..z7` little-endian and compare to the
hand-computed 512-bit product `⟦x⟧ · ⟦y⟧`. The inputs begin in `x0..x3`/`y0..y3`;
the `z_k` start at 0. -/

/-- Build a `BState` with `x = [x0,x1,x2,x3]`, `y = [y0,y1,y2,y3]` (little-endian
    limbs) and all `z_k = 0`. -/
def mkState (x0 x1 x2 x3 y0 y1 y2 y3 : X64) : BState :=
  { cf := false
  , regs := fun r =>
      match r with
      | "x0" => x0 | "x1" => x1 | "x2" => x2 | "x3" => x3
      | "y0" => y0 | "y1" => y1 | "y2" => y2 | "y3" => y3
      | _ => 0 }

/-- The 512-bit product read back from `z0..z7` little-endian after running the
    lowered schoolbook. -/
def runProductNat (st : BState) : Nat :=
  let s := runBBlock st (lowerBBlock mul48Block)
  (List.range 8).foldr (fun k acc => acc * 2 ^ 64 + (s.get ("z" ++ toString k)).toNat) 0

/-- The little-endian `Nat` value of a 4-limb input. -/
def limbsNat (a0 a1 a2 a3 : X64) : Nat :=
  a0.toNat + a1.toNat * 2 ^ 64 + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192

/-- **`bignum_mul_4_8` KAT (small).** `x = 0x...cdef…`, `y = 0x...3210…`: the eight
    stored words read little-endian equal the full integer product `x·y`. -/
theorem mul48_kat :
    runProductNat (mkState
      0x0123456789abcdef 0x1111111122222222 0x0000000000000003 0x0000000000000000
      0xfedcba9876543210 0x0000000000000005 0x00000000000000ff 0x0000000000000000)
      = limbsNat 0x0123456789abcdef 0x1111111122222222 0x0000000000000003 0
        * limbsNat 0xfedcba9876543210 0x0000000000000005 0x00000000000000ff 0 := by
  native_decide

/-- **`bignum_mul_4_8` KAT (full 4-limb).** Both operands use all four limbs;
    the product is the full 512-bit value. -/
theorem mul48_kat2 :
    runProductNat (mkState
      0xdeadbeefcafebabe 0x0123456789abcdef 0xfedcba9876543210 0x1122334455667788
      0x8877665544332211 0x0f0f0f0f0f0f0f0f 0xa5a5a5a5a5a5a5a5 0x5a5a5a5a5a5a5a5a)
      = limbsNat 0xdeadbeefcafebabe 0x0123456789abcdef 0xfedcba9876543210 0x1122334455667788
        * limbsNat 0x8877665544332211 0x0f0f0f0f0f0f0f0f 0xa5a5a5a5a5a5a5a5 0x5a5a5a5a5a5a5a5a := by
  native_decide

/-- **`bignum_mul_4_8` KAT (maximal carry).** `x = y = 2²⁵⁶ - 1` (all limbs
    `0xff…ff`): the product is `(2²⁵⁶-1)² = 2⁵¹² - 2²⁵⁷ + 1`, exercising every
    carry in the accumulation chain. The eight stored words match it exactly. -/
theorem mul48_kat_max :
    runProductNat (mkState
      0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff
      0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff)
      = (2 ^ 256 - 1) * (2 ^ 256 - 1) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMontMulKernel
