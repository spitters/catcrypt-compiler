/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64

/-!
# s2n-bignum's `bignum_mul_4_8` (4×4 schoolbook), lowered through the owned RV64 backend

`RiscvBignumKernel.lean` lowers s2n-bignum's *add*-class `bignum_add_p256`
through the 64-bit RV64 model, riding the SLTU-synthesized carry chain. This
module is the **multiply**-class sibling: it lowers the SAME kernel the x86
`X86Backend/BignumMontMulKernel.lean` reference emits — `bignum_mul_4_8`, the full
256×256→512 schoolbook product `z[8] = x[4] · y[4]` — but through the **RISC-V
RV64** M-extension (`MUL`/`MULHU`) plus the SLTU `addc`/`addcc` carry macros. It
is a cross-ISA comparison and the field-multiply prerequisite for X25519.

## The key architectural difference: no MULX, no ADX, no carry flag

The x86 reference rides the **MULX + dual ADCX/ADOX** idiom: one 64×64→128 product
(`mulx`, touching no flag) feeds two independent carry chains (low halves up the
CF chain via `adcx`, high halves up the OF chain via `adox`), so the out-of-order
core runs both adders in parallel. **RV64 has none of this.** The base+M ISA gives
only:

* `MUL`/`MULHU` — the low / high 64 bits of the 64×64 product, as **two separate
  instructions** (no fused 128-bit destination, no `%rdx`-implicit src);
* `ADD`/`SUB`/`SLTU` — no carry flag, so every add-with-carry is the SLTU macro
  (`add ; sltu ; add ; sltu ; or`, 5 insns), exactly as in `RiscvBignumKernel`.

So the multiply is a pure **operand-scanning schoolbook**: for each multiplier
limb `x[i]`, each `MUL`/`MULHU` pair `(lo, hi) = x[i]·y[j]` is accumulated into the
running column window with the SLTU `addc` chain. There is no dual-chain
parallelism — RV64 cannot express it — so the instruction count is the
no-ADX cost (documented in §"instruction-count cost" below).

## The routine

`bignum_mul_4_8(z, x, y)`: `z[8] := x[4] · y[4]`, full 512-bit product, no
reduction. Operand-scanning: 16 `MUL`+`MULHU` product pairs (32 multiply insns),
each low/high half folded into the eight-word accumulator `acc0..acc7` by the
SLTU carry chain.

## What this kernel emits / proves

* `mul48Block64`: the verified `ROp64` body — the 16 product pairs + SLTU carry
  accumulation into `acc0..acc7`.
* `mul48_lowering_correct64`: lowering the body and running it on `RState64`
  equals the direct fold (`riscvBlock64_lowering_denote` instantiated), no new
  custom axioms.
* `mul48_kat64*`: value KATs on worked vectors — the eight accumulator words read
  little-endian equal the full integer product `x·y`, byte-identical to the x86
  reference / GMP.

The full all-inputs correctness is the s2n proof obligation; as an in-Lean close
it is a 256×256→512 schoolbook identity gated by the qemu-riscv64 KAT, the same
posture as the x86/ARM kernels.

## The no-ADX instruction-count cost (vs x86/ARM)

| ISA   | product op            | add-with-carry           | 4×4 machine insns |
|-------|-----------------------|--------------------------|-------------------|
| x86   | `mulx` (1, 128-bit)   | `adcx`/`adox` (1, dual)  | 63 (s2n exact)    |
| ARM   | `mul`+`umulh` (2)     | `adds`/`adcs` (1, flag)  | ~50               |
| RV64  | `mul`+`mulhu` (2)     | SLTU `addc` macro (5)    | 800 (this body)   |

The measured cost: this RV64 body lowers to **800** machine `RInst64`
(`mul48Block64_lowered_length`), against x86's **63** for the identical
`bignum_mul_4_8` (`X86Backend.BignumMontMulKernel.mul48Block`). RV64 pays the
no-ADX tax twice over:

* **two instructions per product** (`mul`+`mulhu`) — like ARM, but with no fused
  128-bit destination like x86's single `mulx`;
* **five instructions per add-with-carry** (the SLTU `addc` macro
  `add ; sltu ; add ; sltu ; or`) — there is no carry flag, unlike *both* x86 and
  ARM.

This kernel also uses the **maximally portable** operand-scanning ripple (each
product's low/high half ripples a carry all the way to `acc7`), which is simpler
to verify but instruction-heavier than a column-summed schedule; a
column-scheduled RV64 multiply would shrink the ripples but stay far above x86's
ADX count. The 800-vs-63 ratio is the price of the missing ADX/flag register (and
the conservative ripple), not a backend inefficiency.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMontMulKernel

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. The verified `bignum_mul_4_8` body as an `ROp64` block

Operand-scanning schoolbook. Inputs: `u0..u3` (x limbs), `v0..v3` (y limbs);
output: the eight accumulator words `acc0..acc7` (read back little-endian as the
512-bit product). Scratch: `lo__`/`hi__` (the `MUL`/`MULHU` halves), `cra`/`crb`
(the two alternating SLTU ripple-carry words), `tt__` (the `addc`/`addcc` macro
scratch).

(The x limbs are named `u*`, NOT `x0..x3`, because `x0` is the RV64 hard-wired
zero-register alias — `RState64.get "x0"` always reads `0`.)

We accumulate column-major into `acc0..acc7`. For each multiplier limb `u[i]`
(`i = 0..3`) and each `v[j]` (`j = 0..3`):

* `lo__ := MUL u[i] v[j]`, `hi__ := MULHU u[i] v[j]`;
* fold `lo__` into `acc[i+j]` and `hi__` into `acc[i+j+1]`, propagating the carry
  up through the higher accumulator words with the SLTU `addc` macro.

`acc0..acc7` start at 0 (the trusted prologue zeroes them). The two registers
`cra`/`crb` alternate the running ripple carry; `tt__` is the `addc`/`addcc`
scratch. -/

/-- Add a 64-bit `src` into accumulator word `acc[k]`, propagating the carry up
    through `acc[k+1..7]` via the SLTU `addcc`/`addc` macros. `cyIn` names the
    incoming carry register (already 0/1), `cyOut` the produced carry, `t` the
    scratch. We model the propagation explicitly: `acc[k] += src` (carry `c`), then
    `acc[k+1] += c`, `acc[k+2] += (that carry)`, … up to `acc7`. -/
def accAt (k : Nat) : String := "acc" ++ toString k

/-- Fold one product half `src` into the accumulator starting at column `k`,
    rippling the carry up to `acc7`. Produces the carry chain via `addcc` (head)
    then `addc` links — each adds the running carry into the next accumulator
    word. The carry registers are named `cyK`/`cyK1`/… per column so they stay
    distinct (alias-free). -/
def foldInto (k : Nat) (src : String) : List ROp64 :=
  -- acc[k] := acc[k] + src, carry → the running carry register. At any point in a
  -- ripple only ONE carry is live (each link consumes the previous carry and
  -- produces the next), so we alternate just two names `cra`/`crb` — the
  -- producer of step `d` writes the register the consumer of step `d+1` reads.
  -- This keeps the scratch register-pressure bounded (24 distinct names total)
  -- so the leaf fits the 25-GP RV64 pool. The names `cra`/`crb`/`tt__` do NOT
  -- collide with the `addc`/`addcc` macro's *internal* scratch `c1__`/`c2__`/
  -- `sum__` (RiscvLowering64.toRInst64).
  let carry := fun (d : Nat) => if d % 2 == 0 then "cra" else "crb"
  -- head: carry index 0 (produces `cra`)
  .addcc (accAt k) (carry 0) (accAt k) src ::
  -- ripple link d (d = 0 .. 6-k): reads carry d (cin), produces carry d+1.
  (List.range (7 - k)).map (fun d =>
    let col := k + 1 + d
    .addc (accAt col) (carry (d+1)) (accAt col) "zero" (carry d) "tt__")

/-- The product pair `x[i]·y[j]` folded into the accumulator: `lo` at column
    `i+j`, `hi` at column `i+j+1`. -/
def macAt (i j : Nat) (xi yj : String) : List ROp64 :=
  [ .mul "lo__" xi yj, .mulhu "hi__" xi yj ] ++
  foldInto (i + j) "lo__" ++
  foldInto (i + j + 1) "hi__"

/-- The verified straight-line body of `bignum_mul_4_8` on RV64 (operand-scanning
    schoolbook, SLTU-synthesized carry accumulation). Inputs `u0..u3` (x limbs),
    `v0..v3` (y limbs) pre-loaded by the trusted loads; output `acc0..acc7` (read
    back by the trusted stores). The eight accumulator words are pre-zeroed by the
    trusted prologue. (The x limbs are named `u*`, NOT `x0..x3`, because `x0` is
    the RV64 hard-wired zero register alias — `RState64.get "x0"` reads `0`.) -/
def mul48Block64 : List ROp64 :=
  (List.flatten <|
    (List.range 4).flatMap (fun i =>
      (List.range 4).map (fun j =>
        macAt i j ("u" ++ toString i) ("v" ++ toString j))))

/-! ## 2. Lowering correctness (the bignum block-lowering theorem instantiated) -/

/-- **Lowering correctness on `bignum_mul_4_8` (RV64).** Running the lowered body
    on the 64-bit model equals the direct fold — `riscvBlock64_lowering_denote`
    instantiated on the `bignum_mul_4_8` body, for every initial `RState64`. -/
theorem mul48_lowering_correct64 (s : RState64) :
    runRBlock64 s (lowerRBlock64 mul48Block64)
      = mul48Block64.foldl (fun st op => runRBlock64 st (toRInst64 op)) s :=
  riscvBlock64_lowering_denote mul48Block64 s

/-! ## 3. The value KATs (the eight accumulator words = the full product)

Read the eight accumulator words little-endian as a 512-bit integer and compare
against the true integer product `x·y`. These are the in-Lean witnesses that the
operand-scanning carry accumulation matches the schoolbook math; the all-inputs
identity is gated by the qemu-riscv64 KAT. -/

/-- The 512-bit little-endian value of the eight accumulator words in a state. -/
def outProduct (s : RState64) : Nat :=
  (List.range 8).foldl (fun acc k =>
    acc + (s.get (accAt k)).toNat * 2 ^ (64 * k)) 0

/-- The little-endian 256-bit value of four input limbs. -/
def fromLimbs (a0 a1 a2 a3 : Nat) : Nat :=
  a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192

/-- Build an init state with x limbs `u0..u3`, y limbs `v0..v3` seeded and `acc*`
    zero. (x limbs are `u*` to avoid the `x0` zero-register alias.) -/
def mkMulState (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) : RState64 :=
  { regs := fun r => match r with
      | "u0" => BitVec.ofNat 64 x0 | "u1" => BitVec.ofNat 64 x1
      | "u2" => BitVec.ofNat 64 x2 | "u3" => BitVec.ofNat 64 x3
      | "v0" => BitVec.ofNat 64 y0 | "v1" => BitVec.ofNat 64 y1
      | "v2" => BitVec.ofNat 64 y2 | "v3" => BitVec.ofNat 64 y3
      | _ => 0 }

/-- **`bignum_mul_4_8` KAT #1 (small).** `x = 3`, `y = 5` ⇒ product `15`, in
    `acc0` with all higher words zero. -/
theorem mul48_kat_small64 :
    let s := runRBlock64 (mkMulState 3 0 0 0 5 0 0 0) (lowerRBlock64 mul48Block64)
    outProduct s = 15 := by native_decide

/-- **`bignum_mul_4_8` KAT #2 (single-limb carry).** `x = 2⁶⁴-1`, `y = 2⁶⁴-1` ⇒
    `(2⁶⁴-1)² = 2¹²⁸ - 2⁶⁵ + 1`, exercising `MUL`+`MULHU` and the carry into
    `acc1`. -/
theorem mul48_kat_sq64 :
    let s := runRBlock64
      (mkMulState 0xffffffffffffffff 0 0 0 0xffffffffffffffff 0 0 0)
      (lowerRBlock64 mul48Block64)
    outProduct s = (2^64 - 1) * (2^64 - 1) := by native_decide

/-- **`bignum_mul_4_8` KAT #3 (full 4×4, all limbs).** A worked 256×256 vector;
    the eight accumulator words read little-endian equal the full integer
    product. Exercises every one of the 16 partial products and the full carry
    ripple to `acc7`. -/
theorem mul48_kat_full64 :
    let x0 := 0x0123456789abcdef; let x1 := 0xfedcba9876543210
    let x2 := 0x0f1e2d3c4b5a6978; let x3 := 0x8796a5b4c3d2e1f0
    let y0 := 0x1111111111111111; let y1 := 0x2222222222222222
    let y2 := 0x3333333333333333; let y3 := 0x4444444444444444
    let s := runRBlock64 (mkMulState x0 x1 x2 x3 y0 y1 y2 y3)
      (lowerRBlock64 mul48Block64)
    outProduct s = fromLimbs x0 x1 x2 x3 * fromLimbs y0 y1 y2 y3 := by
  native_decide

/-- **All-ones full product KAT.** `x = y = 2²⁵⁶-1` ⇒ `(2²⁵⁶-1)²`, the maximal
    carry-ripple vector (every accumulator word saturated, carries propagate the
    whole way to `acc7`). -/
theorem mul48_kat_allones64 :
    let m := 0xffffffffffffffff
    let s := runRBlock64 (mkMulState m m m m m m m m) (lowerRBlock64 mul48Block64)
    outProduct s = (2^256 - 1) * (2^256 - 1) := by native_decide

/-! ## 4. The no-ADX instruction-count cost (the cross-ISA datum) -/

/-- The lowered RV64 body instruction count — the no-ADX cost. The x86
    reference (`X86Backend.BignumMontMulKernel.mul48Block`) is 63 instructions
    riding MULX + dual ADCX/ADOX; this RV64 body is materially larger (two insns
    per product, no fused 128-bit dest; five insns per add-with-carry, no flag). -/
theorem mul48Block64_lowered_length :
    (lowerRBlock64 mul48Block64).length = 800 := by native_decide

/-- The source `ROp64` op count (before SLTU macro expansion). -/
theorem mul48Block64_length : mul48Block64.length = 176 := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMontMulKernel
