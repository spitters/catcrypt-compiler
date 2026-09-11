/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64

/-!
# s2n-bignum's `bignum_add_p256`, lowered through the owned RV64 backend (#549)

`ArmBignumKernel.lean` (#547) lowered s2n-bignum's `bignum_add_p256` —
`z := (x + y) mod p_256` for two reduced 256-bit inputs — through the AArch64
64-bit `X`-register bignum model, riding the flag-based carry chain
(`ADDS`/`ADCS`/`SUBS`/`SBCS`/`CSEL`). This module lowers the **same kernel**
through the **RISC-V RV64** 64-bit model — the cross-ISA comparison the task
asks for — but RV64 has **no carry flag and no conditional select**, so the
carry chain is **SLTU-synthesized** and the reduce is a **branch-free mask
select** (`RiscvModel64`/`RiscvLowering64` headers explain the architectural
reason). It is the RISC-V sibling of `ArmBignumKernel.addp256Block` and
`X86Backend/BignumMontMulKernel.lean`.

## The routine, and the honest RISC-V instruction-count cost

The same s2n `bignum_add_p256` body, but the A64 single-instruction carry ops
become RV64 SLTU macros:

* the 4-limb carry chain `ADDS ; ADCS×3 ; ADC` (5 A64 instructions) becomes
  `addcc` (2 insns) + `addc`×3 (5 insns each) + a final carry already in a
  register — the top carry word is the last `addc`'s `cout`;
* the trial subtraction `SUBS ; SBCS×4` (5 A64 instructions) becomes `subbb`
  (2 insns) + `subb`×4 (5 insns each);
* the 4× `CSEL` reduce becomes 4× `csub` mask select (5 insns each).

So the body that is **23 A64 instructions** lowers to **~60 RV64 instructions** —
the documented price of the missing flag register and `CSEL`, not a backend
inefficiency. (s2n-bignum ships a dedicated `x86`/`arm` `bignum_add_p256`; there
is no RISC-V s2n-bignum, which is exactly why the synthesis cost is the
interesting datum.)

## What this kernel emits / proves

* `addp256Block64`: the verified `ROp64` body — the SLTU carry chain + SLTU
  trial subtraction + mask-select reduce.
* `addp256_lowering_correct64`: lowering the body and running it on `RState64`
  equals the direct fold (`riscvBlock64_lowering_denote` instantiated), no new
  custom axioms.
* `addp256_kat64` / `addp256_kat_noreduce64`: value KATs on worked vectors that
  exercise the reduce and no-reduce branches, byte-identical to `(x+y) mod p_256`.

The full all-inputs correctness is the s2n proof obligation; as an in-Lean close
it is a 256-bit modular-arithmetic identity gated by the qemu-riscv64 KAT, the
same posture as the ARM/x86 kernels.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBignumKernel

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. The verified `bignum_add_p256` body as an `ROp64` block

The p256 modulus limbs (little-endian 64-bit):
`p_256 = [0xffffffffffffffff, 0x00000000ffffffff, 0x0000000000000000,
0xffffffff00000001]`. RV64 materialises each constant limb with the `li`
pseudo-op. Inputs: `d0..d3` (x limbs), `n0..n3` (y limbs); output: `d0..d3`. The
carry words `cy1..cy3` and the top carry `cy`; the trial-sub limbs land in
`m0..m3` with borrow words `bo1..bo3` and top borrow `bo`. -/

/-- The verified straight-line body of `bignum_add_p256` on RV64 (register-to-
    register, SLTU-synthesized). Inputs `d0..d3` (x), `n0..n3` (y) pre-loaded by
    the trusted loads; output `d0..d3` (read back by the trusted stores). -/
def addp256Block64 : List ROp64 :=
  -- [cy;d3;d2;d1;d0] := x + y   (SLTU-synthesized carry chain)
  [ .addcc "d0" "cy1" "d0" "n0"                  -- d0 := x0+y0, cy1 := carry
  , .addc  "d1" "cy2" "d1" "n1" "cy1" "tt"       -- d1 := x1+y1+cy1, cy2 := carry
  , .addc  "d2" "cy3" "d2" "n2" "cy2" "tt"
  , .addc  "d3" "cy"  "d3" "n3" "cy3" "tt"       -- cy := top carry word
  -- materialise the p_256 constant limbs (li pseudo-ops)
  , .li "p0" 0xffffffffffffffff
  , .li "p1" 0x00000000ffffffff
  , .li "p3" 0xffffffff00000001
  -- [bo;m3;m2;m1;m0] := [cy;d3;d2;d1;d0] - p_256   (SLTU-synthesized trial sub)
  , .subbb "m0" "bo1" "d0" "p0"                  -- m0 := d0-p0, bo1 := borrow
  , .subb  "m1" "bo2" "d1" "p1" "bo1" "tt"       -- m1 := d1-p1-bo1
  , .subb  "m2" "bo3" "d2" "zero" "bo2" "tt"     -- p2 = 0, subtract zero
  , .subb  "m3" "bo4" "d3" "p3" "bo3" "tt"
  , .subb  "boF" "bo" "cy" "zero" "bo4" "tt"     -- final borrow: cy - 0 - bo4
  -- select the subtracted limbs iff there was NO final borrow (cond := ¬bo).
  -- bo = 1 ⇔ (x+y) < p_256 ⇒ keep d; bo = 0 ⇔ (x+y) ≥ p_256 ⇒ take m.
  -- cond := 1 - bo  (bo is 0/1), i.e. cond := bo XOR 1.
  , .li "one" 1
  , .xor "cond" "bo" "one"                       -- cond := ¬bo  (1 if no borrow)
  , .csub "d0" "m0" "d0" "cond" "mask" "tt"
  , .csub "d1" "m1" "d1" "cond" "mask" "tt"
  , .csub "d2" "m2" "d2" "cond" "mask" "tt"
  , .csub "d3" "m3" "d3" "cond" "mask" "tt" ]

/-! ## 2. Lowering correctness (the bignum keystone instantiated) -/

/-- **Lowering correctness on `bignum_add_p256` (RV64).** Running the lowered body
    on the 64-bit model equals the direct fold — `riscvBlock64_lowering_denote`
    instantiated on the `bignum_add_p256` body, for every initial `RState64`. -/
theorem addp256_lowering_correct64 (s : RState64) :
    runRBlock64 s (lowerRBlock64 addp256Block64)
      = addp256Block64.foldl (fun st op => runRBlock64 st (toRInst64 op)) s :=
  riscvBlock64_lowering_denote addp256Block64 s

/-! ## 3. The value KATs (the worked reduce / no-reduce vectors)

`x = p_256 - 1`, `y = 2` ⇒ `(x+y) mod p_256 = 1`, from the *subtracted* branch
(the reduce fires). `x = 3`, `y = 4` ⇒ `7`, from the un-subtracted branch. -/

/-- `x = p_256 - 1` little-endian limbs; `y = 2`. -/
def kat_x : RState64 :=
  { regs := fun r =>
      match r with
      | "d0" => 0xfffffffffffffffe | "d1" => 0x00000000ffffffff
      | "d2" => 0x0000000000000000 | "d3" => 0xffffffff00000001
      | "n0" => 0x0000000000000002 | "n1" => 0
      | "n2" => 0 | "n3" => 0
      | _ => 0 }

/-- The lowered-and-run `bignum_add_p256` on the reduce vector. -/
def katRun : RState64 := runRBlock64 kat_x (lowerRBlock64 addp256Block64)

/-- **`bignum_add_p256` KAT (reduce branch).** `x = p_256 - 1`, `y = 2` ⇒
    `(x+y) mod p_256 = 1`, i.e. result limbs `[1,0,0,0]` — selected from the
    SLTU-subtracted `m` limbs by the mask-select reduce. -/
theorem addp256_kat64 :
    (katRun.get "d0" = 0x0000000000000001) ∧ (katRun.get "d1" = 0) ∧
    (katRun.get "d2" = 0) ∧ (katRun.get "d3" = 0) := by native_decide

/-- A second KAT: no overflow. `x = 3`, `y = 4` ⇒ `7`, from the un-subtracted
    limbs (the mask-select picks `orig`). -/
def kat2_x : RState64 :=
  { regs := fun r => match r with | "d0" => 3 | "n0" => 4 | _ => 0 }

/-- KAT for the non-reduce branch: `3 + 4 = 7 < p_256`. -/
theorem addp256_kat_noreduce64 :
    let s := runRBlock64 kat2_x (lowerRBlock64 addp256Block64)
    (s.get "d0" = 7) ∧ (s.get "d1" = 0) ∧ (s.get "d2" = 0) ∧ (s.get "d3" = 0) := by
  native_decide

/-- A third KAT: `x = p_256 - 1`, `y = p_256 - 1` ⇒ `2·(p_256-1) mod p_256 =
    p_256 - 2`, the reduce fires and the high limbs are non-trivial — exercises
    the full carry chain through all four limbs and the mask select on every
    limb. `p_256 - 2 = [0xfffffffffffffffd, 0x00000000ffffffff, 0,
    0xffffffff00000001]`. -/
def kat3_x : RState64 :=
  { regs := fun r =>
      match r with
      | "d0" => 0xfffffffffffffffe | "d1" => 0x00000000ffffffff
      | "d2" => 0x0000000000000000 | "d3" => 0xffffffff00000001
      | "n0" => 0xfffffffffffffffe | "n1" => 0x00000000ffffffff
      | "n2" => 0x0000000000000000 | "n3" => 0xffffffff00000001
      | _ => 0 }

/-- KAT for the all-limbs reduce: `(p_256-1)+(p_256-1) ≡ p_256-2`. -/
theorem addp256_kat_full64 :
    let s := runRBlock64 kat3_x (lowerRBlock64 addp256Block64)
    (s.get "d0" = 0xfffffffffffffffd) ∧ (s.get "d1" = 0x00000000ffffffff) ∧
    (s.get "d2" = 0) ∧ (s.get "d3" = 0xffffffff00000001) := by native_decide

/-! ## 4. A standalone `MUL`/`MULHU` widening-product witness

The carry kernel above does not multiply; this pins the 64×64→128 widening
product the bignum *multiply* kernels (the next-round target) ride. -/

/-- The `MUL`/`MULHU` widening product of `a`, `b` into `(lo, hi)`. -/
def mulWideBlock64 : List ROp64 :=
  [ .mul "lo" "a" "b", .mulhu "hi" "a" "b" ]

/-- **Widening-product KAT.** `a = 0x0123456789abcdef`, `b = 0xfedcba9876543210`;
    the 128-bit product splits into `lo = MUL`, `hi = MULHU`, recombined
    byte-identical to the full integer product. -/
theorem mulwide_kat64 :
    let s := runRBlock64
      { regs := fun r => match r with
          | "a" => 0x0123456789abcdef | "b" => 0xfedcba9876543210 | _ => 0 }
      (lowerRBlock64 mulWideBlock64)
    (s.get "hi").toNat * 2 ^ 64 + (s.get "lo").toNat
      = 0x0123456789abcdef * 0xfedcba9876543210 := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBignumKernel
