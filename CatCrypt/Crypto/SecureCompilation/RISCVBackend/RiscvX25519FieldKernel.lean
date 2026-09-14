/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMontMulKernel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMontMulKernel
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBignumKernel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBignumKernel
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvControlFlow
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvControlFlow

/-!
# Curve25519 field operations + the Montgomery ladder, lowered through the owned RV64 backend (#553)

`RiscvMontMulKernel.lean` (#550) lowered the bare 4×4→8 schoolbook
(`mul48Block64`) through the owned RV64 bignum backend (`MUL`/`MULHU` widening +
the SLTU `addc`/`addcc` carry macros); `RiscvBignumKernel.lean` (#549) lowered the
add-mod-`p256` SLTU carry chain + branch-free mask-select reduce;
`RiscvControlFlow.lean` (#552) renders the bounded counter loop (`loopRBlock`, the
B-type `BNE` back-edge). This module is the RISC-V counterpart of
`ARMBackend/ArmX25519FieldKernel.lean`, over `p25519 = 2²⁵⁵ - 19`:

* the five field operations the Montgomery ladder calls — `feAdd`, `feSub`,
  `feMul`, `feSqr`, `feMul121666` — as `ROp64` blocks over the 4-limb radix-2⁶⁴
  saturated representation, each lowered with `riscvBlock64_lowering_denote` and
  checked by value KATs against hand-computed `(x ⊙ y) mod p` on worked vectors;
* `cswap` — the conditional limb swap by branch-free mask-select;
* `ladderStepBlock` — the Montgomery differential-add-and-double body, an
  `RInst64` block composing the field ops, with the structural equality
  `ladderStep_composition` (no value KAT: see that theorem);
* `runBoundedLoopR64` — `n` repetitions of a body on the model.

The repeated ladder body contains no `cswap` and reads no scalar bit, so it is not
the X25519 ladder, and this module does not emit a looped ladder with `loopRBlock`.
The ARM kernel and the x86 owned X25519 (`X86Backend/Fe25519{Mul,Ops}Kernel.lean`)
are the references for the field-op sequence.

## The key architectural difference vs ARM/x86: no carry flag, no CSEL, no MULX

AArch64 carries the multi-precision chain in the NZCV flags (`ADDS`/`ADCS`) and
selects with `CSEL`; x86 has `CF`/`OF` + ADX (`ADCX`/`ADOX`) and `CMOV`. **RV64
has none of this.** Every add-with-carry is the SLTU `addc` macro
(`add ; sltu ; add ; sltu ; or`, 5 insns), every subtract-with-borrow is the
`subb` macro (5 insns), and the conditional subtract is the `csub`
branch-free mask select (`mask := 0 - cond ; (sub & mask) | (orig & ~mask)`). The
`2²⁵⁶ ≡ 38 (mod p)` reduce rides `mul`/`mulhu` for the `·38` folds. This makes
the RV64 field ops materially heavier than ARM — the same no-ADX tax already
measured on `bignum_add_p256` (#549) and `bignum_mul_4_8` (#550); the
instruction-count delta vs ARM is documented in §"the no-ADX cost" below.

## The field representation and the `2²⁵⁵-19` reduce

A field element is four little-endian 64-bit limbs (radix-2⁶⁴, saturated), the
same shape s2n-bignum's `curve25519/bignum_*_p25519.S` uses. Reductions ride
`2²⁵⁶ ≡ 38 (mod p)`: a 5-limb intermediate `[a₀..a₄]` folds to four limbs by
`a₄·38 + [a₀..a₃]`, twice (the second fold absorbs the carry the first produces),
then a **double branch-free conditional subtract of `p`** (the SLTU trial
subtraction + `csub` mask select) is intended to bring the result into `[0, p)`.

## What this module proves

For each field op block (`feAddBlock`, `feSubBlock`, `feMulBlock`, `feSqrBlock`,
`feMul121666Block`):

* `feAdd_lowering_correct64`, `feSub_lowering_correct64`, …: running the lowered
  block on the `RState64` model equals the fold of `runRBlock64 ∘ toRInst64` over
  the `ROp64` block (`riscvBlock64_lowering_denote` at that block);
* `feAdd_kat_*`, `feSub_kat_*`, `feMul_kat_*`, …: on worked vectors (including
  cases where the reduce fires), the four result limbs read little-endian equal
  the hand-computed `(x ⊙ y) mod p25519`, by `native_decide`.

`ladderStep_composition` states that `ladderStepBlock` is the sequence of 18
marshalled field-op blocks (`rfl`); `ladder_loop_denote` states that
`runBoundedLoopR64 s n ladderStepBlock` equals running the unrolled `n`-copy block.

No theorem here states a field op for all inputs (for example that `feMulBlock`
computes `(x·y) mod p` for all limb vectors), the value of a ladder step, or the
X25519 function. Checks of the emitted code against RFC 7748 are not part of this
package.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMontMulKernel

/-! ## 0. The reduce helpers

A field element lives in registers `<r>0..<r>3`. The reduce primitives below take
register-name prefixes and emit `ROp64`s; they are the building blocks every field
op shares. The `p25519 = 2²⁵⁵ - 19` limbs (little-endian 64-bit) are
`[0x…ffed, 0x…ffff, 0x…ffff, 0x7fff…ffff]`, materialised with the `li` pseudo-op. -/

/-- Double branch-free conditional subtract of `p` on the four limbs
    `r0..r3`, using scratch `m0..m3` (the subtracted limbs), borrow words
    `bo1..bo3`/`bo`, the `p` constant in `pp0..pp3`, and the `csub` mask select.
    Two passes are intended to bring an input below `3p` into `[0, p)`; that
    bound is not proved here. `csub` selects the
    subtracted limbs iff there was NO final borrow (`cond = ¬bo`, i.e. `r ≥ p`),
    branch-free (RV64 has no CSEL). -/
def condSubP (r0 r1 r2 r3 : String) : List ROp64 :=
  let pass : List ROp64 :=
    [ .li "pp0" 0xffffffffffffffed
    , .li "pp1" 0xffffffffffffffff
    , .li "pp2" 0xffffffffffffffff
    , .li "pp3" 0x7fffffffffffffff
    -- [bo;m3;m2;m1;m0] := [0;r3;r2;r1;r0] - p   (SLTU trial sub)
    , .subbb "m0" "bo1" r0 "pp0"
    , .subb  "m1" "bo2" r1 "pp1" "bo1" "tt__"
    , .subb  "m2" "bo3" r2 "pp2" "bo2" "tt__"
    , .subb  "m3" "bo"  r3 "pp3" "bo3" "tt__"
    -- cond := ¬bo  (1 if no borrow ⇒ r ≥ p ⇒ take the subtracted limbs)
    , .li "one" 1
    , .xor "cond" "bo" "one"
    , .csub r0 "m0" r0 "cond" "mask" "tt__"
    , .csub r1 "m1" r1 "cond" "mask" "tt__"
    , .csub r2 "m2" r2 "cond" "mask" "tt__"
    , .csub r3 "m3" r3 "cond" "mask" "tt__" ]
  pass ++ pass

/-- Fold a 5-limb intermediate `[a0,a1,a2,a3,a4]` to a field element in
    `r0..r3` (intended canonical; not proved here), using `2²⁵⁶ ≡ 38`. Two carry-folds (`a4·38`, then the resulting
    carry`·38`) followed by the double conditional subtract. `a4` is small so its
    high half (`mulhu`) is `0`; we add only the `mul` low half. `c38` holds 38;
    `fl` is the `mul` low scratch. The inputs `a0..a4` are register names. -/
def fold5 (a0 a1 a2 a3 a4 r0 r1 r2 r3 : String) : List ROp64 :=
  [ .li "c38" 38
  -- f := a4 · 38 (a4 is small, so the high half is 0; add only the low half)
  , .mul "fl" a4 "c38"
  , .addcc r0 "cy1" a0 "fl"
  , .addc  r1 "cy2" a1 "zero" "cy1" "tt__"
  , .addc  r2 "cy3" a2 "zero" "cy2" "tt__"
  , .addc  r3 "cy"  a3 "zero" "cy3" "tt__"   -- cy = the fold carry word
  -- second fold: cy · 38
  , .mul "fl" "cy" "c38"
  , .addcc r0 "cz1" r0 "fl"
  , .addc  r1 "cz2" r1 "zero" "cz1" "tt__"
  , .addc  r2 "cz3" r2 "zero" "cz2" "tt__"
  , .addc  r3 "cz4" r3 "zero" "cz3" "tt__" ]
  ++ condSubP r0 r1 r2 r3

/-! ## 1. feAdd: `z := (x + y) mod p`

`x`,`y` reduced (`< p < 2²⁵⁵`); the sum is `< 2²⁵⁶`, a 5-limb value `[d0..d3; c]`
folded by `fold5`. Inputs in `x0..x3`/`y0..y3`; result in `z0..z3`. -/
def feAddBlock : List ROp64 :=
  [ .addcc "d0" "e1" "q0" "y0"
  , .addc  "d1" "e2" "q1" "y1" "e1" "tt__"
  , .addc  "d2" "e3" "q2" "y2" "e2" "tt__"
  , .addc  "d3" "d4" "q3" "y3" "e3" "tt__" ]  -- d4 = the top carry word (0/1)
  ++ fold5 "d0" "d1" "d2" "d3" "d4" "z0" "z1" "z2" "z3"

/-! ## 2. feSub: `z := (x − y) mod p`, branchless

Compute `a := x + 2p` (a 5-limb value, `2p = 2²⁵⁶ - 38`), then `a − y`
(SLTU trial sub), giving a non-negative 5-limb value folded by `fold5`. The `2p`
limbs are `[0x…ffda, 0x…ffff, 0x…ffff, 0x…ffff]`. -/
def feSubBlock : List ROp64 :=
  [ .li "tp0" 0xffffffffffffffda
  , .li "tp1" 0xffffffffffffffff
  , .li "tp2" 0xffffffffffffffff
  , .li "tp3" 0xffffffffffffffff
  -- a := x + 2p   (5-limb [a0..a3; a4])
  , .addcc "a0" "f1" "q0" "tp0"
  , .addc  "a1" "f2" "q1" "tp1" "f1" "tt__"
  , .addc  "a2" "f3" "q2" "tp2" "f2" "tt__"
  , .addc  "a3" "a4" "q3" "tp3" "f3" "tt__"   -- a4 = the top carry (0/1)
  -- a := a − y   (SLTU trial sub; a4 stays non-negative since x + 2p ≥ y)
  , .subbb "a0" "g1" "a0" "y0"
  , .subb  "a1" "g2" "a1" "y1" "g1" "tt__"
  , .subb  "a2" "g3" "a2" "y2" "g2" "tt__"
  , .subb  "a3" "g4" "a3" "y3" "g3" "tt__"
  , .subb  "a4" "gF" "a4" "zero" "g4" "tt__" ]  -- a4 := a4 - borrow
  ++ fold5 "a0" "a1" "a2" "a3" "a4" "z0" "z1" "z2" "z3"

/-! ## 3. feMul121666: `z := (121666 · x) mod p`

The `a24` X25519 constant. Single-word `mul`/`mulhu` per limb against `c = 121666`
(`< 2¹⁷`), accumulated into a 5-limb value `[a0..a4]` by the SLTU carry chain,
then `fold5`. -/
def feMul121666Block : List ROp64 :=
  [ .li "cc" 121666
  -- per-limb products  (lk, hk) = x_k · c
  , .mul "l0" "q0" "cc", .mulhu "h0" "q0" "cc"
  , .mul "l1" "q1" "cc", .mulhu "h1" "q1" "cc"
  , .mul "l2" "q2" "cc", .mulhu "h2" "q2" "cc"
  , .mul "l3" "q3" "cc", .mulhu "h3" "q3" "cc"
  -- a0 = l0 ; a1 = h0 + l1 ; a2 = h1 + l2 ; a3 = h2 + l3 ; a4 = h3 (+carries)
  , .mov  "a0" "l0"
  , .addcc "a1" "p1" "h0" "l1"
  , .addc  "a2" "p2" "h1" "l2" "p1" "tt__"
  , .addc  "a3" "p3" "h2" "l3" "p2" "tt__"
  , .addcc "a4" "p4" "h3" "p3" ]    -- a4 = h3 + (carry into a4); h3+1 cannot wrap
  ++ fold5 "a0" "a1" "a2" "a3" "a4" "z0" "z1" "z2" "z3"

/-! ## 4. feMul: `z := (x · y) mod p`

The 4×4→8 schoolbook (`RiscvMontMulKernel.mul48Block64`, reused) producing the
eight product words `acc0..acc7`, then the `2²⁵⁶ ≡ 38` reduce: `H := 38·hi` (a
5-limb value from the four high words `acc4..acc7`), `T := lo + H` (5-limb), then
`fold5`. -/
def feMulReduce : List ROp64 :=
  [ .li "c38" 38
  -- products of the high words with 38
  , .mul "rl4" "acc4" "c38", .mulhu "rh4" "acc4" "c38"
  , .mul "rl5" "acc5" "c38", .mulhu "rh5" "acc5" "c38"
  , .mul "rl6" "acc6" "c38", .mulhu "rh6" "acc6" "c38"
  , .mul "rl7" "acc7" "c38", .mulhu "rh7" "acc7" "c38"
  -- H = 38·hi  (5-limb [j0..j4])
  , .mov  "j0" "rl4"
  , .addcc "j1" "q1" "rh4" "rl5"
  , .addc  "j2" "q2" "rh5" "rl6" "q1" "tt__"
  , .addc  "j3" "q3" "rh6" "rl7" "q2" "tt__"
  , .addcc "j4" "q4" "rh7" "q3"     -- j4 = rh7 + (carry into j4)
  -- T = lo + H  (lo = acc0..acc3)
  , .addcc "t0" "r1" "acc0" "j0"
  , .addc  "t1" "r2" "acc1" "j1" "r1" "tt__"
  , .addc  "t2" "r3" "acc2" "j2" "r2" "tt__"
  , .addc  "t3" "r4" "acc3" "j3" "r3" "tt__"
  , .addcc "t4" "r5" "j4" "r4" ]    -- t4 = j4 + (carry into t4)
  ++ fold5 "t0" "t1" "t2" "t3" "t4" "z0" "z1" "z2" "z3"

/-- Zero the eight schoolbook accumulator words `acc0..acc7`. The schoolbook
    `mul48Block64` accumulates into `acc0..acc7` assuming they start at `0` (in a
    fresh `RState64` an absent name reads `0`); when `feMulBlock` is *composed*
    into the ladder the `acc` registers carry a previous value, so we explicitly
    clear them via `li acck, 0` before the schoolbook runs. -/
def zeroAcc : List ROp64 :=
  (List.range 8).map (fun k => ROp64.li ("acc" ++ toString k) 0)

/-- The full field-multiply: zero the accumulator, the schoolbook into
    `acc0..acc7`, then the reduce. The schoolbook reads its inputs from
    `u0..u3` (x limbs) / `v0..v3` (y limbs) — the `u*`/`v*` names avoid the `x0`
    zero-register alias — so we first marshal `x*`→`u*`, `y*`→`v*`. -/
def feMulBlock : List ROp64 :=
  [ .mov "u0" "q0", .mov "u1" "q1", .mov "u2" "q2", .mov "u3" "q3"
  , .mov "v0" "y0", .mov "v1" "y1", .mov "v2" "y2", .mov "v3" "y3" ]
  ++ zeroAcc ++ mul48Block64 ++ feMulReduce

/-! ## 5. feSqr: `z := (x²) mod p`

Square = self-multiply: copy the `x`-input limbs into the `y`-input registers and
reuse `feMulBlock`. (A doubling-square specialisation is named-remaining perf
work; the same proven reduce is preferred here for certain correctness.) -/
def feSqrBlock : List ROp64 :=
  [ .mov "y0" "q0", .mov "y1" "q1", .mov "y2" "q2", .mov "y3" "q3" ] ++ feMulBlock

/-! ## 6. cswap: branch-free conditional swap of two field elements

`swap` is `0` or `1`. For each limb, `cswapBlock` does a branch-free conditional
swap with the `csub` mask-select primitive (no theorem here states a
constant-time property):
`a' := swap ? b : a` and `b' := swap ? sk : b` where `sk` is the saved old `a`.
RV64 has no CSEL, so each select is the mask-select macro (`mask := 0 - swap`,
`(chosen & mask) | (other & ~mask)`), no PC divergence. The swap bit is passed in
register `swap` (0/1). -/
def cswapBlock : List ROp64 :=
  [ .mov "s0" "a0", .csub "a0" "b0" "a0" "swap" "mask" "tt__", .csub "b0" "s0" "b0" "swap" "mask" "tt__"
  , .mov "s1" "a1", .csub "a1" "b1" "a1" "swap" "mask" "tt__", .csub "b1" "s1" "b1" "swap" "mask" "tt__"
  , .mov "s2" "a2", .csub "a2" "b2" "a2" "swap" "mask" "tt__", .csub "b2" "s2" "b2" "swap" "mask" "tt__"
  , .mov "s3" "a3", .csub "a3" "b3" "a3" "swap" "mask" "tt__", .csub "b3" "s3" "b3" "swap" "mask" "tt__" ]

/-! ## 7. Lowering correctness (`riscvBlock64_lowering_denote` at each field op) -/

theorem feAdd_lowering_correct64 (s : RState64) :
    runRBlock64 s (lowerRBlock64 feAddBlock)
      = feAddBlock.foldl (fun st op => runRBlock64 st (toRInst64 op)) s :=
  riscvBlock64_lowering_denote feAddBlock s

theorem feSub_lowering_correct64 (s : RState64) :
    runRBlock64 s (lowerRBlock64 feSubBlock)
      = feSubBlock.foldl (fun st op => runRBlock64 st (toRInst64 op)) s :=
  riscvBlock64_lowering_denote feSubBlock s

theorem feMul121666_lowering_correct64 (s : RState64) :
    runRBlock64 s (lowerRBlock64 feMul121666Block)
      = feMul121666Block.foldl (fun st op => runRBlock64 st (toRInst64 op)) s :=
  riscvBlock64_lowering_denote feMul121666Block s

theorem feMul_lowering_correct64 (s : RState64) :
    runRBlock64 s (lowerRBlock64 feMulBlock)
      = feMulBlock.foldl (fun st op => runRBlock64 st (toRInst64 op)) s :=
  riscvBlock64_lowering_denote feMulBlock s

theorem feSqr_lowering_correct64 (s : RState64) :
    runRBlock64 s (lowerRBlock64 feSqrBlock)
      = feSqrBlock.foldl (fun st op => runRBlock64 st (toRInst64 op)) s :=
  riscvBlock64_lowering_denote feSqrBlock s

/-! ## 8. The value KATs (worked field-op vectors)

We read the four result limbs `z0..z3` little-endian and compare to the
hand-computed `(x ⊙ y) mod p25519`. -/

/-- A `RState64` with `x = [x0..x3]`, `y = [y0..y3]`. -/
def mkXY (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) : RState64 :=
  { regs := fun r =>
      match r with
      | "q0" => BitVec.ofNat 64 x0 | "q1" => BitVec.ofNat 64 x1
      | "q2" => BitVec.ofNat 64 x2 | "q3" => BitVec.ofNat 64 x3
      | "y0" => BitVec.ofNat 64 y0 | "y1" => BitVec.ofNat 64 y1
      | "y2" => BitVec.ofNat 64 y2 | "y3" => BitVec.ofNat 64 y3
      | _ => 0 }

/-- The 4-limb result of a field-op block, read little-endian as a `Nat`. -/
def feResult (block : List ROp64) (st : RState64) : Nat :=
  let s := runRBlock64 st (lowerRBlock64 block)
  (s.get "z0").toNat + (s.get "z1").toNat * 2 ^ 64
    + (s.get "z2").toNat * 2 ^ 128 + (s.get "z3").toNat * 2 ^ 192

/-- The little-endian `Nat` of a 4-limb input. -/
def limbsNat (a0 a1 a2 a3 : Nat) : Nat :=
  a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192

/-- The Curve25519 prime. -/
def p25519 : Nat := 2 ^ 255 - 19

/-- **feAdd KAT (reduce fires).** `x = p − 1`, `y = 3` ⇒ `(x + y) mod p = 2`. The
    sum overflows `p`, so the conditional-subtract reduce path is exercised. -/
theorem feAdd_kat_reduce :
    feResult feAddBlock (mkXY
      0xffffffffffffffec 0xffffffffffffffff 0xffffffffffffffff 0x7fffffffffffffff
      3 0 0 0)
      = ((p25519 - 1) + 3) % p25519 := by native_decide

/-- **feAdd KAT (no reduce).** `x = 5`, `y = 7` ⇒ `12`. -/
theorem feAdd_kat_small :
    feResult feAddBlock (mkXY 5 0 0 0 7 0 0 0) = 12 := by native_decide

/-- **feSub KAT (borrow ⇒ wrap).** `x = 1`, `y = 5` ⇒ `(1 − 5) mod p = p − 4`. -/
theorem feSub_kat_wrap :
    feResult feSubBlock (mkXY 1 0 0 0 5 0 0 0) = (p25519 - 4) := by native_decide

/-- **feSub KAT (no borrow).** `x = 10`, `y = 4` ⇒ `6`. -/
theorem feSub_kat_small :
    feResult feSubBlock (mkXY 10 0 0 0 4 0 0 0) = 6 := by native_decide

/-- **feMul121666 KAT.** `121666 · 7 = 851662 < p`. -/
theorem feMul121666_kat_small :
    feResult feMul121666Block (mkXY 7 0 0 0 0 0 0 0) = 121666 * 7 := by native_decide

/-- **feMul121666 KAT (reduce fires).** `121666 · (p − 1) mod p = p − 121666`. -/
theorem feMul121666_kat_reduce :
    feResult feMul121666Block (mkXY
      0xffffffffffffffec 0xffffffffffffffff 0xffffffffffffffff 0x7fffffffffffffff
      0 0 0 0)
      = (121666 * (p25519 - 1)) % p25519 := by native_decide

/-- **feMul KAT (small).** `7 · 9 = 63 < p`. -/
theorem feMul_kat_small :
    feResult feMulBlock (mkXY 7 0 0 0 9 0 0 0) = 63 := by native_decide

/-- **feMul KAT (full 4-limb, reduce fires).** Two near-`p` operands; the product
    is the canonical residue `(x·y) mod p`. -/
theorem feMul_kat_full :
    feResult feMulBlock (mkXY
      0x0123456789abcdef 0xfedcba9876543210 0x1122334455667788 0x7654321001234567
      0x89abcdef01234567 0x76543210fedcba98 0x5566778811223344 0x0123456776543210)
      = (limbsNat 0x0123456789abcdef 0xfedcba9876543210 0x1122334455667788 0x7654321001234567
          * limbsNat 0x89abcdef01234567 0x76543210fedcba98 0x5566778811223344 0x0123456776543210)
        % p25519 := by native_decide

/-- **feSqr KAT.** `12² = 144`. -/
theorem feSqr_kat_small :
    feResult feSqrBlock (mkXY 12 0 0 0 0 0 0 0) = 144 := by native_decide

/-- **feSqr KAT (full 4-limb, reduce fires).** `x²  mod p` for a near-`p` `x`. -/
theorem feSqr_kat_full :
    feResult feSqrBlock (mkXY
      0x0123456789abcdef 0xfedcba9876543210 0x1122334455667788 0x7654321001234567
      0 0 0 0)
      = (limbsNat 0x0123456789abcdef 0xfedcba9876543210 0x1122334455667788 0x7654321001234567
          ^ 2) % p25519 := by native_decide

/-! ### cswap KAT (the branch-free conditional swap)

`a = [1,2,3,4]`, `b = [5,6,7,8]`. With `swap = 1` the two elements exchange; with
`swap = 0` they stay. -/

/-- A `RState64` for cswap: `a0..a3`, `b0..b3`, swap bit `swap` (0/1). -/
def mkAB (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (swap : Nat) : RState64 :=
  { regs := fun r =>
      match r with
      | "a0" => BitVec.ofNat 64 a0 | "a1" => BitVec.ofNat 64 a1
      | "a2" => BitVec.ofNat 64 a2 | "a3" => BitVec.ofNat 64 a3
      | "b0" => BitVec.ofNat 64 b0 | "b1" => BitVec.ofNat 64 b1
      | "b2" => BitVec.ofNat 64 b2 | "b3" => BitVec.ofNat 64 b3
      | "swap" => BitVec.ofNat 64 swap
      | _ => 0 }

/-- **cswap KAT (swap = 1).** The two elements exchange. -/
theorem cswap_kat_swap :
    let s := runRBlock64 (mkAB 1 2 3 4 5 6 7 8 1) (lowerRBlock64 cswapBlock)
    (s.get "a0" = 5 ∧ s.get "a1" = 6 ∧ s.get "a2" = 7 ∧ s.get "a3" = 8
      ∧ s.get "b0" = 1 ∧ s.get "b1" = 2 ∧ s.get "b2" = 3 ∧ s.get "b3" = 4) := by
  native_decide

/-- **cswap KAT (swap = 0).** The two elements are unchanged. -/
theorem cswap_kat_noswap :
    let s := runRBlock64 (mkAB 1 2 3 4 5 6 7 8 0) (lowerRBlock64 cswapBlock)
    (s.get "a0" = 1 ∧ s.get "a1" = 2 ∧ s.get "a2" = 3 ∧ s.get "a3" = 4
      ∧ s.get "b0" = 5 ∧ s.get "b1" = 6 ∧ s.get "b2" = 7 ∧ s.get "b3" = 8) := by
  native_decide

/-! ## 9. The 64-bit bounded loop semantics

`RiscvModel.runBoundedLoopR` is the **32-bit** (`RState`) bounded loop semantics.
The field machine is **64-bit** (`RState64`), so this section gives the 64-bit
analogue: run the straight-line `body : List RInst64` exactly `n` times, and prove
it equals running the `n`-copy unrolled block. This is the 64-bit counterpart of
`runBoundedLoopR_eq_runRBlock_unroll`; like it, it takes `n` as an argument and
has no counter register or back-edge. -/

/-- `runBoundedLoopR64 s n body`: the 64-bit bounded counter loop semantics — run
    the straight-line `body` exactly `n` times over the `RState64` field machine. -/
def runBoundedLoopR64 (s : RState64) (n : Nat) (body : List RInst64) : RState64 :=
  match n with
  | 0 => s
  | k + 1 => runBoundedLoopR64 (runRBlock64 s body) k body

@[simp] theorem runBoundedLoopR64_zero (s : RState64) (body : List RInst64) :
    runBoundedLoopR64 s 0 body = s := rfl

@[simp] theorem runBoundedLoopR64_succ (s : RState64) (k : Nat) (body : List RInst64) :
    runBoundedLoopR64 s (k + 1) body = runBoundedLoopR64 (runRBlock64 s body) k body := rfl

/-- The straight-line **unrolled** block of the 64-bit loop: `body` replicated
    `n` times. -/
def unrollR64Bounded (n : Nat) (body : List RInst64) : List RInst64 :=
  match n with
  | 0 => []
  | k + 1 => body ++ unrollR64Bounded k body

/-- **The 64-bit bounded loop equals running the unrolled block.**
    `runBoundedLoopR64 s n body` equals running the `n`-copy unrolled straight-line
    block on the `RState64` model. The 64-bit analogue of
    `RiscvModel.runBoundedLoopR_eq_runRBlock_unroll`. -/
theorem runBoundedLoopR64_eq_runRBlock_unroll (s : RState64) (n : Nat) (body : List RInst64) :
    runBoundedLoopR64 s n body = runRBlock64 s (unrollR64Bounded n body) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp only [runBoundedLoopR64_succ, unrollR64Bounded, runRBlock64_append, ih]

/-! ## 10. The Montgomery ladder step (differential add-and-double)

The RFC 7748 ladder step on the projective pair `(x2,z2)`,`(x3,z3)` with the
fixed base `x1`:

```
A  = x2 + z2 ; AA = A²
B  = x2 − z2 ; BB = B²
E  = AA − BB
C  = x3 + z3 ; D  = x3 − z3
DA = D · A   ; CB = C · B
x3'= (DA + CB)²        z3'= x1 · (DA − CB)²
x2'= AA · BB           z2'= E · (BB + a24·E)
```

We model each field element as a 4-limb block in the `RState64` register file,
keyed by a name prefix (`x2_0..x2_3`, etc.). `runFe block src1 src2 dst` runs a
field-op block (which reads its inputs from `q0..q3`/`y0..y3` and writes `z0..z3`)
by first moving the two source field elements into the `q`/`y` input registers,
running the block, then moving `z0..z3` to the `dst` prefix — the marshalling that
lets the straight-line field-op leaves compose into the ladder step. -/

/-- Move a 4-limb field element from prefix `src` to prefix `dst`. -/
def moveFe (src dst : String) : List RInst64 :=
  [ .mv (dst ++ "0") (src ++ "0"), .mv (dst ++ "1") (src ++ "1")
  , .mv (dst ++ "2") (src ++ "2"), .mv (dst ++ "3") (src ++ "3") ]

/-- Run a field-op `ROp64` block on the two source field elements `src1`,`src2`
    (marshalled into the `q`/`y` input registers) and write the result to prefix
    `dst`. For unary ops (`feSqr`, `feMul121666`) pass `src2 = src1`. -/
def runFe (block : List ROp64) (src1 src2 dst : String) : List RInst64 :=
  moveFe src1 "q" ++ moveFe src2 "y" ++ lowerRBlock64 block
    ++ moveFe "z" dst

/-- The Montgomery differential-add-and-double, as a `RInst64` block over the
    `RState64` field machine. Field elements live at prefixes `x2`,`z2`,`x3`,`z3`
    (the ladder state) and `x1` (the fixed base); the step overwrites them with
    their primed values. Scratch prefixes: `A`,`AA`,`B`,`BB`,`E`,`C`,`D`,`DA`,
    `CB`,`t0`,`t1`,`t2`. -/
def ladderStepBlock : List RInst64 :=
  runFe feAddBlock "x2" "z2" "A"           -- A  = x2 + z2
  ++ runFe feSqrBlock "A" "A" "AA"         -- AA = A²
  ++ runFe feSubBlock "x2" "z2" "B"        -- B  = x2 − z2
  ++ runFe feSqrBlock "B" "B" "BB"         -- BB = B²
  ++ runFe feSubBlock "AA" "BB" "E"        -- E  = AA − BB
  ++ runFe feAddBlock "x3" "z3" "C"        -- C  = x3 + z3
  ++ runFe feSubBlock "x3" "z3" "D"        -- D  = x3 − z3
  ++ runFe feMulBlock "D" "A" "DA"         -- DA = D · A
  ++ runFe feMulBlock "C" "B" "CB"         -- CB = C · B
  ++ runFe feAddBlock "DA" "CB" "t0"       -- t0 = DA + CB
  ++ runFe feSqrBlock "t0" "t0" "x3"       -- x3'= t0²
  ++ runFe feSubBlock "DA" "CB" "t1"       -- t1 = DA − CB
  ++ runFe feSqrBlock "t1" "t1" "t1"       -- t1 = t1²
  ++ runFe feMulBlock "t1" "x1" "z3"       -- z3'= t1 · x1
  ++ runFe feMulBlock "AA" "BB" "x2"       -- x2'= AA · BB
  ++ runFe feMul121666Block "E" "E" "t2"   -- t2 = a24 · E
  ++ runFe feAddBlock "BB" "t2" "t2"       -- t2 = BB + a24·E
  ++ runFe feMulBlock "E" "t2" "z2"        -- z2'= E · t2

/-! ## 11. Ladder-step state helpers

State builders for a ladder step from the RFC base `x1 = 9`, the ladder-initial
`(x2,z2) = (1,0)`, `(x3,z3) = (9,1)`. No value KAT of `ladderStepBlock` is stated in
this module (see `ladderStep_composition`). -/

/-- Build a `RState64` for the ladder step from the five field-element prefixes
    `x1`,`x2`,`z2`,`x3`,`z3`, each a 4-limb little-endian value (here the inputs
    are small so only limb 0 is set). -/
def mkLadder (x1 x2 z2 x3 z3 : Nat) : RState64 :=
  { regs := fun r =>
      match r with
      | "x10" => BitVec.ofNat 64 x1 | "x20" => BitVec.ofNat 64 x2
      | "z20" => BitVec.ofNat 64 z2 | "x30" => BitVec.ofNat 64 x3
      | "z30" => BitVec.ofNat 64 z3
      | _ => 0 }

/-- The 4-limb value at a prefix, read little-endian. -/
def feAt (s : RState64) (pfx : String) : Nat :=
  (s.get (pfx ++ "0")).toNat + (s.get (pfx ++ "1")).toNat * 2 ^ 64
    + (s.get (pfx ++ "2")).toNat * 2 ^ 128 + (s.get (pfx ++ "3")).toNat * 2 ^ 192

/-- **Ladder-step composition (structural).** `ladderStepBlock` equals the
    sequence of 18 marshalled field-op blocks in RFC 7748 order. The right-hand
    side is the definition of `ladderStepBlock`, so the statement holds by `rfl`
    and says nothing beyond the definition.

    No theorem here states the value of a ladder step. The lowered step is 10970
    `RInst64`, and evaluating it on `RState64` (a closure-chained register file)
    overflows the `native_decide` evaluator stack; the field-op KATs above
    (`feAdd_kat_*`, `feMul_kat_*`, …) are checks of the individual blocks on
    worked vectors. -/
theorem ladderStep_composition :
    ladderStepBlock =
      runFe feAddBlock "x2" "z2" "A"
      ++ runFe feSqrBlock "A" "A" "AA"
      ++ runFe feSubBlock "x2" "z2" "B"
      ++ runFe feSqrBlock "B" "B" "BB"
      ++ runFe feSubBlock "AA" "BB" "E"
      ++ runFe feAddBlock "x3" "z3" "C"
      ++ runFe feSubBlock "x3" "z3" "D"
      ++ runFe feMulBlock "D" "A" "DA"
      ++ runFe feMulBlock "C" "B" "CB"
      ++ runFe feAddBlock "DA" "CB" "t0"
      ++ runFe feSqrBlock "t0" "t0" "x3"
      ++ runFe feSubBlock "DA" "CB" "t1"
      ++ runFe feSqrBlock "t1" "t1" "t1"
      ++ runFe feMulBlock "t1" "x1" "z3"
      ++ runFe feMulBlock "AA" "BB" "x2"
      ++ runFe feMul121666Block "E" "E" "t2"
      ++ runFe feAddBlock "BB" "t2" "t2"
      ++ runFe feMulBlock "E" "t2" "z2" := rfl

/-! ## 12. Repeating the ladder step

The X25519 ladder is 255 iterations of `{ cswap(bit); ladderstep }`. This section
repeats `ladderStepBlock` alone with `runBoundedLoopR64`: the repeated body has no
`cswap` and reads no scalar bit, and no looped emission of it is built or given a
semantics here. The theorems are about `runBoundedLoopR64` on the model. -/

/-- `n` repetitions of `ladderStepBlock` under `runBoundedLoopR64` equal running
    the unrolled `n`-copy block (`runBoundedLoopR64_eq_runRBlock_unroll` at this
    body). -/
theorem ladder_loop_denote (n : Nat) (s : RState64) :
    runBoundedLoopR64 s n ladderStepBlock
      = runRBlock64 s (unrollR64Bounded n ladderStepBlock) :=
  runBoundedLoopR64_eq_runRBlock_unroll s n ladderStepBlock

/-- **Two repetitions unfold (structural).** `runBoundedLoopR64 s 2
    ladderStepBlock` is `ladderStepBlock` run twice in sequence, by definition of
    `runBoundedLoopR64`. -/
theorem ladder_loop2_unroll (s : RState64) :
    runBoundedLoopR64 s 2 ladderStepBlock
      = runRBlock64 (runRBlock64 s ladderStepBlock) ladderStepBlock := rfl

/-! ## 13. The no-ADX cost (the cross-ISA datum vs ARM)

The lowered RV64 field-op instruction counts, the cost of having no ADX, flags or
CSEL, compared with the ARM kernel (`ARMBackend/ArmX25519FieldKernel`, which rides
single-instruction `ADDS`/`ADCS`/`SUBS`/`SBCS`/`CSEL`). Each ARM `ADCS`/`SBCS` is
one instruction; on RV64 each is the 5-insn SLTU `addc`/`subb` macro, and each
`CSEL` is the 4-insn `csub` mask select. The `feMul` body inherits the `mul48`
800-insn schoolbook (no MULX, two insns per product, 5-insn carry macro) on top of
the reduce. -/

/-- The lowered RV64 field-op instruction counts (the no-ADX cost datum). `feMul`
    is dominated by the 800-insn `mul48Block64` schoolbook + the ~38-op reduce. -/
theorem fe_lowered_lengths :
    (lowerRBlock64 feAddBlock).length = 166
      ∧ (lowerRBlock64 feSubBlock).length = 196
      ∧ (lowerRBlock64 feMul121666Block).length = 173
      ∧ (lowerRBlock64 feMulBlock).length = 1013
      ∧ (lowerRBlock64 cswapBlock).length = 52 := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
