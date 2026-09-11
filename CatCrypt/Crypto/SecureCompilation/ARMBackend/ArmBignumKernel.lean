/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering

/-!
# s2n-bignum's `bignum_add_p256`, lowered through the owned AArch64 backend (#547)

`ArmLowering.lean` (sub #533) lowered the ChaCha quarter-round through the 32-bit
`W`-register GP-ALU subset. This module is the **bignum/field hot-path** keystone:
it lowers s2n-bignum's `bignum_add_p256` — `z := (x + y) mod p_256` for two
reduced 256-bit inputs — through the 64-bit `X`-register bignum model
(`ArmModel.BState`/`evalBInst`, #547), exercising the full carry-chain +
conditional-subtract-reduce instruction mix: `ADDS`/`ADCS`/`ADC` (the carry
chain), `SUBS`/`SBCS` (the trial subtraction of `p_256`), `MOVZ`/`MOVK` (the
64-bit reduction constants), and `CSEL` (the constant-time select). It is the A64
analogue of `X86Backend/BignumMontMulKernel.lean`.

## The routine (s2n-bignum `arm/p256/bignum_add_p256.S`)

```
ldp d0,d1,[x] ; ldp n0,n1,[y]
adds d0,d0,n0 ; adcs d1,d1,n1
ldp d2,d3,[x,#16] ; ldp n2,n3,[y,#16]
adcs d2,d2,n2 ; adcs d3,d3,n3 ; adc c,xzr,xzr   -- [c;d3;d2;d1;d0] = x+y
subs n0,d0,#0xffffffffffffffff
mov  n1,#0x00000000ffffffff ; sbcs n1,d1,n1
sbcs n2,d2,xzr
mov  n3,#0xffffffff00000001 ; sbcs n3,d3,n3
sbcs c,c,xzr                                    -- [c;n3;n2;n1;n0] = (x+y) - p_256
csel d0,d0,n0,cc ; csel d1,d1,n1,cc
csel d2,d2,n2,cc ; csel d3,d3,n3,cc             -- select (x+y) iff no final borrow
stp  d0,d1,[z] ; stp d2,d3,[z,#16]
```

The `ldp`/`stp` are the memory traffic at the function boundary (trusted ABI
scaffolding, exactly the x86 leaf-prologue posture and the 32-bit `LDR`/`STR`
posture); the **verified straight-line body** is the register-to-register chain
between them. We model the inputs `x`/`y` as the eight `X` registers `d0..d3`,
`n0..n3` pre-loaded by the (trusted) `ldp`s, run the verified body, and read the
four result limbs `d0..d3` back (the registers the `stp`s write).

## What this kernel emits / proves

* `addp256Block`: the verified `BOp` body — the carry chain + trial subtraction +
  `csel`, the s2n register sequence line-for-line (`#0xffffffffffffffff` is
  realised as `~~~ 0` = `SUBS Xd, Xn, XZR` after a `MVN`; we encode the literal
  by a `movz/movk`-built constant register `cst0` to keep the body a pure
  register machine — see `subsImm`).
* `addp256_lowering_correct`: lowering the body to `BInst` and running it on the
  `BState` model equals the direct machine fold — `bignumBlock_lowering_denote`
  on the `bignum_add_p256` body (no new custom axioms).
* `addp256_kat`: the value KAT on a worked test vector — two reduced inputs whose
  sum overflows `p_256`, so the conditional-subtract reduce fires (selects the
  subtracted limbs), pinned byte-identical to the hand-computed `(x+y) mod p_256`.

The full all-inputs correctness (`⟦d0..d3⟧ = (⟦x⟧ + ⟦y⟧) mod p_256`) is the s2n
proof obligation (`arm/proofs/bignum_add_p256.ml`); as an in-Lean close it is a
256-bit modular-arithmetic identity gated by the GMP/s2n cross-check KAT, the same
posture as the x86 bignum kernels (REV-12). Here we pin the worked vector that
exercises the reduce branch.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmBignumKernel

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. The verified `bignum_add_p256` body as a `BOp` block

The p256 modulus limbs (little-endian 64-bit): `p_256 = 2²⁵⁶ - 2²²⁴ + 2¹⁹² +
2⁹⁶ - 1`, i.e.
`[0xffffffffffffffff, 0x00000000ffffffff, 0x0000000000000000, 0xffffffff00000001]`.
The s2n trial subtraction subtracts these four limbs (with `xzr` for the all-zero
limb `p2`). We materialise the two non-trivial constant limbs in scratch registers
`p0`/`p1`/`p3` via `MOVZ`/`MOVK` (the body is then a pure register machine; the
`p0 = 0xffffffffffffffff` limb is built as `movz #0xffff; movk … ×3`). -/

/-- Build the all-ones limb `0xffffffffffffffff` into `r`: `movz #0xffff` then
    three `movk`s at lanes 1,2,3 — the verified-front realisation of the `#-1`
    immediate s2n encodes inline. -/
def buildAllOnes (r : String) : List BOp :=
  [ .movz r 0xffff, .movk r 0xffff 1, .movk r 0xffff 2, .movk r 0xffff 3 ]

/-- Build `0x00000000ffffffff` into `r` (`p_256` limb 1): `movz #0xffff; movk
    #0xffff @lane1`. -/
def buildP1 (r : String) : List BOp :=
  [ .movz r 0xffff, .movk r 0xffff 1 ]

/-- Build `0xffffffff00000001` into `r` (`p_256` limb 3): `movz #1; movk #0xffff
    @lane2; movk #0xffff @lane3`. -/
def buildP3 (r : String) : List BOp :=
  [ .movz r 0x0001, .movk r 0xffff 2, .movk r 0xffff 3 ]

/-- The verified straight-line body of `bignum_add_p256` (register-to-register).
    Inputs: `d0..d3` (x limbs) and `n0..n3` (y limbs) pre-loaded by the trusted
    `ldp`s; output: `d0..d3` (read back by the trusted `stp`s). `c` is the top
    carry word; `p0`/`p1`/`p3` are the materialised `p_256` constant limbs. -/
def addp256Block : List BOp :=
  -- [c;d3;d2;d1;d0] := x + y   (carry chain)
  [ .adds "d0" "d0" "n0"
  , .adcs "d1" "d1" "n1"
  , .adcs "d2" "d2" "n2"
  , .adcs "d3" "d3" "n3"
  , .adc  "c"  "xzr" "xzr" ]
  -- materialise the p_256 constant limbs
  ++ buildAllOnes "p0" ++ buildP1 "p1" ++ buildP3 "p3" ++
  -- [c;n3;n2;n1;n0] := [c;d3;d2;d1;d0] - p_256   (trial subtraction)
  [ .subs "n0" "d0" "p0"
  , .sbcs "n1" "d1" "p1"
  , .sbcs "n2" "d2" "xzr"
  , .sbcs "n3" "d3" "p3"
  , .sbcs "c"  "c"  "xzr"
  -- select (x+y) iff the subtraction borrowed (cc: C=0 ⇒ x+y < p_256)
  , .csel "d0" "d0" "n0" .cc
  , .csel "d1" "d1" "n1" .cc
  , .csel "d2" "d2" "n2" .cc
  , .csel "d3" "d3" "n3" .cc ]

/-! ## 2. Lowering correctness (the bignum keystone instantiated) -/

/-- **Lowering correctness on `bignum_add_p256`.** Running the lowered body on the
    64-bit model equals the direct machine fold — `bignumBlock_lowering_denote`
    instantiated on the `bignum_add_p256` body, for every initial `BState`. -/
theorem addp256_lowering_correct (s : BState) :
    runBBlock s (lowerBBlock addp256Block)
      = addp256Block.foldl (fun st op => evalBInst st (toBInst op)) s :=
  bignumBlock_lowering_denote addp256Block s

/-! ## 3. The value KAT (the worked reduce-branch vector)

Test vector chosen so that `x + y ≥ p_256` (the reduce fires). Take
`x = p_256 - 1` and `y = 2`; then `x + y = p_256 + 1 ≡ 1 (mod p_256)`, so the
result must be the limb vector `[1,0,0,0]` — and it comes from the *subtracted*
branch (`n` limbs), proving the `CSEL`/`SUBS`/`SBCS` reduce path is exercised. -/

/-- `p_256 - 1` little-endian limbs: `p_256 = [ffff…ff, 0000…ffff, 0, ffffffff00000001]`,
    so `p_256 - 1 = [ffff…fe, 0000…ffff, 0, ffffffff00000001]`. -/
def kat_x : BState :=
  { cf := false
  , regs := fun r =>
      match r with
      | "d0" => 0xfffffffffffffffe | "d1" => 0x00000000ffffffff
      | "d2" => 0x0000000000000000 | "d3" => 0xffffffff00000001
      -- y = 2
      | "n0" => 0x0000000000000002 | "n1" => 0
      | "n2" => 0 | "n3" => 0
      | _ => 0 }

/-- The lowered-and-run `bignum_add_p256` on the KAT vector. -/
def katRun : BState := runBBlock kat_x (lowerBBlock addp256Block)

/-- **`bignum_add_p256` KAT.** `x = p_256 - 1`, `y = 2` ⇒ `(x+y) mod p_256 = 1`,
    i.e. result limbs `[1,0,0,0]`. The reduce branch fires (the result is the
    subtracted `n` limbs selected by `CSEL`), byte-identical to the hand-computed
    modular sum. -/
theorem addp256_kat :
    (katRun.get "d0" = 0x0000000000000001) ∧ (katRun.get "d1" = 0) ∧
    (katRun.get "d2" = 0) ∧ (katRun.get "d3" = 0) := by
  native_decide

/-- A second KAT: no overflow (`x + y < p_256` ⇒ no reduce). `x = 3`, `y = 4`
    ⇒ result `[7,0,0,0]`, selected from the *un*-subtracted `d` limbs. -/
def kat2_x : BState :=
  { cf := false
  , regs := fun r =>
      match r with
      | "d0" => 3 | "n0" => 4 | _ => 0 }

/-- KAT for the non-reduce branch: `3 + 4 = 7 < p_256`. -/
theorem addp256_kat_noreduce :
    let s := runBBlock kat2_x (lowerBBlock addp256Block)
    (s.get "d0" = 7) ∧ (s.get "d1" = 0) ∧ (s.get "d2" = 0) ∧ (s.get "d3" = 0) := by
  native_decide

/-! ## 4. A standalone `MUL`/`UMULH` widening-product witness

The carry-chain kernel above does not multiply; this pins the 64×64→128 widening
product the bignum *multiply* kernels (the next-round target) ride. The two halves
of `a * b` are `MUL` (low) and `UMULH` (high), recombined as one 128-bit value. -/

/-- The `MUL`/`UMULH` widening product of two registers `a`, `b` into `(lo, hi)`. -/
def mulWideBlock : List BOp :=
  [ .mul "lo" "a" "b", .umulh "hi" "a" "b" ]

/-- **Widening-product KAT.** `a = 0x0123456789abcdef`, `b = 0xfedcba9876543210`;
    the 128-bit product `a*b` splits into `lo = UMULH-low`, `hi = UMULH-high`,
    recombined byte-identical to the full integer product. -/
theorem mulwide_kat :
    let s := runBBlock
      { cf := false, regs := fun r =>
          match r with
          | "a" => 0x0123456789abcdef | "b" => 0xfedcba9876543210 | _ => 0 }
      (lowerBBlock mulWideBlock)
    (s.get "hi").toNat * 2 ^ 64 + (s.get "lo").toNat
      = 0x0123456789abcdef * 0xfedcba9876543210 := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmBignumKernel
