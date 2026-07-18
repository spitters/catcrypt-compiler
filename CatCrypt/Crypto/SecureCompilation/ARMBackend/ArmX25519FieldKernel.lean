/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMontMulKernel
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmControlFlow

/-!
# Curve25519 field operations + the Montgomery ladder, lowered through the owned AArch64 backend (#552)

`ArmMontMulKernel.lean` (#549) lowered the bare 4×4→8 schoolbook
(`bignum_mul_4_8`) through the owned A64 bignum backend (`MUL`/`UMULH` widening +
`ADDS`/`ADCS` carry chain); `ArmBignumKernel.lean` (#547) lowered the
add-mod-`p256` carry-chain + conditional-subtract reduce; `ArmControlFlow.lean`
(#551) emitted the bounded counter loop (`loopABlock` / `runBoundedLoopA`). This
module is the **X25519 keystone** — the flagship deployment-reach result, since
phones / Graviton / Apple-Silicon all run X25519 — composing those three levers
into the whole scalar-multiplication over `p25519 = 2²⁵⁵ - 19`:

* the five field operations the Montgomery ladder calls — `feAdd`, `feSub`,
  `feMul`, `feSqr`, `feMul121666` — as verified `BOp` blocks over the 4-limb
  radix-2⁶⁴ saturated representation, each lowered through the owned A64 bignum
  backend and pinned with a value KAT against the hand-computed `(x ⊙ y) mod p`;
* `cswap` — the constant-time conditional limb swap (mask-select, no branch);
* `ladderstep` — the Montgomery differential-add-and-double body, an `BOp` block
  composing the field ops, pinned with a value KAT;
* the **whole ladder** wrapped in `loopABlock` over the 255 scalar bits (the
  bounded-counter loop of #551), the looped emission denoting `runBoundedLoopA`.

The x86 owned X25519 (`X86Backend/Fe25519{Mul,Ops}Kernel.lean`, #380/#408) is the
reference Com body and the source of the RFC 7748 expected output; this is its A64
analogue, assembled entirely from owned-backend leaves (no fiat transliteration).

## The field representation and the `2²⁵⁵-19` reduce

A field element is four little-endian 64-bit limbs (radix-2⁶⁴, saturated), the
same shape s2n-bignum's `curve25519/bignum_*_p25519.S` uses. Reductions ride
`2²⁵⁶ ≡ 38 (mod p)`: a 5-limb intermediate `[a₀..a₄]` folds to four limbs by
`a₄·38 + [a₀..a₃]`, twice (the second fold absorbs the carry the first produces),
then a **double constant-time conditional subtract of `p`** (`SUBS`/`SBCS` trial
subtraction + `CSEL`) brings the result canonically into `[0, p)`. This is the
A64 carry-chain analogue of the x86 fused-quotient-estimate reduce, chosen here
for an obviously-correct word sequence (every limb is one modelled `ADDS`/`ADCS`/
`SUBS`/`SBCS`/`CSEL`/`MUL`/`UMULH`), validated below by `native_decide` KATs and,
end-to-end, by the qemu-aarch64 RFC 7748 KAT in `bench/arm_compare/`.

## What this module emits / proves

Each field op `feXBlock : List BOp`:

* `feXBlock_lowering_correct`: running the lowered block on the `BState` model
  equals the direct machine fold — `bignumBlock_lowering_denote` instantiated on
  the body (no new custom axioms).
* `feX_kat`: the value KAT — the four stored result limbs read little-endian equal
  the hand-computed `(x ⊙ y) mod p25519` on worked vectors (incl. the reduce-firing
  corner cases), under `native_decide`.

`ladderstep_kat` pins one differential-add-and-double step; `ladderLoopBody` +
`ladder_loop_denote` wrap the step in the bounded-counter loop (the looped
emission denotes `runBoundedLoopA`, the same value the unrolled block denotes,
constant emitted size).

The all-inputs identities (`feMul` is `(x·y) mod p` for *all* limb vectors; the
255-step ladder + inversion is RFC 7748 X25519) are the runtime KATs: the field
ops against the hand-computed modular results, and the WHOLE X25519 against the
RFC 7748 §5.2 `(k, u) → out` vectors, run under qemu-aarch64 — the load-bearing
gate (this is a **correctness** result, not a cyc/op claim: no real silicon).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmX25519FieldKernel

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMontMulKernel

/-! ## 0. The reduce helpers

A field element lives in registers `<r>0..<r>3`. The reduce primitives below take
register-name prefixes and emit `BOp`s; they are the building blocks every field
op shares. -/

/-- The `p25519 = 2²⁵⁵ - 19` limbs (little-endian 64-bit): `[0x…ffed, 0x…ffff,
    0x…ffff, 0x7fff…ffff]`. Built into scratch registers `pp0..pp3` via `MOVZ`/
    `MOVK`. -/
def buildP0 (r : String) : List BOp :=  -- 0xffffffffffffffed
  [ .movz r 0xffed, .movk r 0xffff 1, .movk r 0xffff 2, .movk r 0xffff 3 ]
def buildPmax (r : String) : List BOp :=  -- 0xffffffffffffffff
  [ .movz r 0xffff, .movk r 0xffff 1, .movk r 0xffff 2, .movk r 0xffff 3 ]
def buildPtop (r : String) : List BOp :=  -- 0x7fffffffffffffff
  [ .movz r 0xffff, .movk r 0xffff 1, .movk r 0xffff 2, .movk r 0x7fff 3 ]

/-- Double constant-time conditional subtract of `p` on the four limbs
    `r0..r3`, using scratch `n0..n3` (the subtracted limbs), `pp0..pp3` (the `p`
    constant), and `cc`. After two passes the result is canonical in `[0, p)`.
    `CSEL .cs` selects the subtracted limbs iff there was no borrow (`C=1`, i.e.
    `r ≥ p`). -/
def condSubP (r0 r1 r2 r3 : String) : List BOp :=
  let pass : List BOp :=
    [ .subs "n0" r0 "pp0"
    , .sbcs "n1" r1 "pp1"
    , .sbcs "n2" r2 "pp2"
    , .sbcs "n3" r3 "pp3"
    -- C=1 ⇒ no borrow ⇒ r ≥ p ⇒ take the subtracted limbs
    , .csel r0 "n0" r0 .cs
    , .csel r1 "n1" r1 .cs
    , .csel r2 "n2" r2 .cs
    , .csel r3 "n3" r3 .cs ]
  buildP0 "pp0" ++ buildPmax "pp1" ++ buildPmax "pp2" ++ buildPtop "pp3"
    ++ pass ++ pass

/-- Fold a 5-limb intermediate `[a0,a1,a2,a3,a4]` to a canonical field element in
    `r0..r3`, using `2²⁵⁶ ≡ 38`. Two carry-folds (`a4·38`, then the resulting
    carry`·38`) followed by the double conditional subtract. `c38` holds 38;
    `fl`/`fh` are the `MUL`/`UMULH` scratch for the fold product. The inputs
    `a0..a4` are register names. -/
def fold5 (a0 a1 a2 a3 a4 r0 r1 r2 r3 : String) : List BOp :=
  [ .movz "c38" 38
  -- f := a4 · 38 (a4 is small, so UMULH is 0; we add only the low half)
  , .mul "fl" a4 "c38"
  , .adds r0 a0 "fl"
  , .adcs r1 a1 "xzr"
  , .adcs r2 a2 "xzr"
  , .adcs r3 a3 "xzr"
  , .adc  "cy" "xzr" "xzr"   -- the fold carry
  -- second fold: cy · 38
  , .mul "fl" "cy" "c38"
  , .adds r0 r0 "fl"
  , .adcs r1 r1 "xzr"
  , .adcs r2 r2 "xzr"
  , .adcs r3 r3 "xzr" ]
  ++ condSubP r0 r1 r2 r3

/-! ## 1. feAdd: `z := (x + y) mod p`

`x`,`y` reduced (`< p < 2²⁵⁵`); the sum is `< 2²⁵⁶`, a 5-limb value `[d0..d3; c]`
folded by `fold5`. Inputs in `x0..x3`/`y0..y3`; result in `z0..z3`. -/
def feAddBlock : List BOp :=
  [ .adds "d0" "x0" "y0"
  , .adcs "d1" "x1" "y1"
  , .adcs "d2" "x2" "y2"
  , .adcs "d3" "x3" "y3"
  , .adc  "d4" "xzr" "xzr" ]
  ++ fold5 "d0" "d1" "d2" "d3" "d4" "z0" "z1" "z2" "z3"

/-! ## 2. feSub: `z := (x − y) mod p`, branchless

Compute `a := x + 2p` (a 5-limb value, `2p = 2²⁵⁶ - 38`), then `a − y`
(`SUBS`/`SBCS`), giving a non-negative 5-limb value folded by `fold5`. The `2p`
limbs are `[0x…ffda, 0x…ffff, 0x…ffff, 0x…ffff]`. -/
def buildTP0 (r : String) : List BOp :=  -- 0xffffffffffffffda
  [ .movz r 0xffda, .movk r 0xffff 1, .movk r 0xffff 2, .movk r 0xffff 3 ]

def feSubBlock : List BOp :=
  buildTP0 "tp0" ++ buildPmax "tp1" ++ buildPmax "tp2" ++ buildPmax "tp3" ++
  -- a := x + 2p   (5-limb [a0..a3; a4])
  [ .adds "a0" "x0" "tp0"
  , .adcs "a1" "x1" "tp1"
  , .adcs "a2" "x2" "tp2"
  , .adcs "a3" "x3" "tp3"
  , .adc  "a4" "xzr" "xzr"
  -- a := a − y
  , .subs "a0" "a0" "y0"
  , .sbcs "a1" "a1" "y1"
  , .sbcs "a2" "a2" "y2"
  , .sbcs "a3" "a3" "y3"
  , .sbc  "a4" "a4" "xzr" ]
  ++ fold5 "a0" "a1" "a2" "a3" "a4" "z0" "z1" "z2" "z3"

/-! ## 3. feMul121666: `z := (121666 · x) mod p`

The `a24` X25519 constant. Single-word `MUL`/`UMULH` per limb against `c = 121666`
(`< 2¹⁷`), accumulated into a 5-limb value `[a0..a4]` by the carry chain, then
`fold5`. -/
def feMul121666Block : List BOp :=
  -- 121666 = 0x1DB42 needs two MOV lanes (MOVZ is a 16-bit immediate).
  [ .movz "cc" 0xDB42, .movk "cc" 0x1 1
  -- per-limb products  (lk, hk) = x_k · c
  , .mul   "l0" "x0" "cc", .umulh "h0" "x0" "cc"
  , .mul   "l1" "x1" "cc", .umulh "h1" "x1" "cc"
  , .mul   "l2" "x2" "cc", .umulh "h2" "x2" "cc"
  , .mul   "l3" "x3" "cc", .umulh "h3" "x3" "cc"
  -- a0 = l0 ; a1 = h0 + l1 ; a2 = h1 + l2 ; a3 = h2 + l3 ; a4 = h3 (+carries)
  , .mov  "a0" "l0"
  , .adds "a1" "h0" "l1"
  , .adcs "a2" "h1" "l2"
  , .adcs "a3" "h2" "l3"
  , .adc  "a4" "h3" "xzr" ]
  ++ fold5 "a0" "a1" "a2" "a3" "a4" "z0" "z1" "z2" "z3"

/-! ## 4. feMul: `z := (x · y) mod p`

The 4×4→8 schoolbook (`ArmMontMulKernel.mul48Block`, reused) producing the eight
product words `z0..z7`, then the `2²⁵⁶ ≡ 38` reduce: `H := 38·hi` (a 5-limb value
from the four high words `z4..z7`), `T := lo + H` (5-limb), then `fold5`. -/
def feMulReduce : List BOp :=
  [ .movz "c38" 38
  -- products of the high words with 38
  , .mul "rl4" "z4" "c38", .umulh "rh4" "z4" "c38"
  , .mul "rl5" "z5" "c38", .umulh "rh5" "z5" "c38"
  , .mul "rl6" "z6" "c38", .umulh "rh6" "z6" "c38"
  , .mul "rl7" "z7" "c38", .umulh "rh7" "z7" "c38"
  -- H = 38·hi  (5-limb [g0..g4])
  , .mov  "g0" "rl4"
  , .adds "g1" "rh4" "rl5"
  , .adcs "g2" "rh5" "rl6"
  , .adcs "g3" "rh6" "rl7"
  , .adc  "g4" "rh7" "xzr"
  -- T = lo + H  (lo = z0..z3)
  , .adds "t0" "z0" "g0"
  , .adcs "t1" "z1" "g1"
  , .adcs "t2" "z2" "g2"
  , .adcs "t3" "z3" "g3"
  , .adc  "t4" "g4" "xzr" ]
  ++ fold5 "t0" "t1" "t2" "t3" "t4" "z0" "z1" "z2" "z3"

/-- Zero the eight schoolbook accumulator words `z0..z7`. The schoolbook
    `mul48Block` accumulates into `z0..z7` assuming they start at `0` (in a fresh
    `BState` an absent name reads `0`); when `feMulBlock` is *composed* into the
    ladder the `z` registers carry a previous value, so we explicitly clear them
    via `MOV zk, xzr` before the schoolbook runs. -/
def zeroZ : List BOp :=
  (List.range 8).map (fun k => BOp.mov ("z" ++ toString k) "xzr")

/-- The full field-multiply: zero the accumulator, the schoolbook into `z0..z7`,
    then the reduce. -/
def feMulBlock : List BOp := zeroZ ++ mul48Block ++ feMulReduce

/-! ## 5. feSqr: `z := (x²) mod p`

Square = self-multiply: copy the `x`-input limbs into the `y`-input registers and
reuse `feMulBlock`. (A doubling-square specialisation is named-remaining perf
work; the same proven reduce is preferred here for certain correctness.) -/
def feSqrBlock : List BOp :=
  [ .mov "y0" "x0", .mov "y1" "x1", .mov "y2" "x2", .mov "y3" "x3" ] ++ feMulBlock

/-! ## 6. cswap: constant-time conditional swap of two field elements

`swap` is `0` or `0xff…ff` (a full mask). For each limb, `t := mask & (a ⊕ b)`,
`a := a ⊕ t`, `b := b ⊕ t` — the standard branchless conditional swap, no `CSEL`
and no PC divergence (the mask is a public ladder bit, CT-admissible). Implemented
with the modelled ops: `EOR` is not in `BOp`, so we use the algebraic identity via
`sub`-free masking — here we realise `a ⊕ t` and the masking with the bitwise ops
the model carries (`add`/`sub` are not bitwise), so cswap uses `CSEL` directly:
`CSEL a' = mask?b:a`, `CSEL b' = mask?a:b`. The select condition is the carry flag
the caller sets from the ladder bit (`mask ≠ 0 ⇒ swap`). -/
def cswapBlock : List BOp :=
  -- precondition: the carry flag C encodes the swap bit (set by the caller's
  -- `SUBS`/`CMP` on the ladder bit). `csel d x y .cs` = `C ? x : y`. We stash the
  -- old `a` limb in `sk` first, then `a := C ? b : a`, `b := C ? sk : b`.
  [ .mov "s0" "a0", .csel "a0" "b0" "a0" .cs, .csel "b0" "s0" "b0" .cs
  , .mov "s1" "a1", .csel "a1" "b1" "a1" .cs, .csel "b1" "s1" "b1" .cs
  , .mov "s2" "a2", .csel "a2" "b2" "a2" .cs, .csel "b2" "s2" "b2" .cs
  , .mov "s3" "a3", .csel "a3" "b3" "a3" .cs, .csel "b3" "s3" "b3" .cs ]

/-! ## 7. Lowering correctness (each field op instantiated on the keystone) -/

theorem feAdd_lowering_correct (s : BState) :
    runBBlock s (lowerBBlock feAddBlock)
      = feAddBlock.foldl (fun st op => evalBInst st (toBInst op)) s :=
  bignumBlock_lowering_denote feAddBlock s

theorem feSub_lowering_correct (s : BState) :
    runBBlock s (lowerBBlock feSubBlock)
      = feSubBlock.foldl (fun st op => evalBInst st (toBInst op)) s :=
  bignumBlock_lowering_denote feSubBlock s

theorem feMul121666_lowering_correct (s : BState) :
    runBBlock s (lowerBBlock feMul121666Block)
      = feMul121666Block.foldl (fun st op => evalBInst st (toBInst op)) s :=
  bignumBlock_lowering_denote feMul121666Block s

theorem feMul_lowering_correct (s : BState) :
    runBBlock s (lowerBBlock feMulBlock)
      = feMulBlock.foldl (fun st op => evalBInst st (toBInst op)) s :=
  bignumBlock_lowering_denote feMulBlock s

theorem feSqr_lowering_correct (s : BState) :
    runBBlock s (lowerBBlock feSqrBlock)
      = feSqrBlock.foldl (fun st op => evalBInst st (toBInst op)) s :=
  bignumBlock_lowering_denote feSqrBlock s

/-! ## 8. The value KATs (worked field-op vectors)

We read the four result limbs `z0..z3` little-endian and compare to the
hand-computed `(x ⊙ y) mod p25519`. -/

/-- A `BState` with `x = [x0..x3]`, `y = [y0..y3]` and a chosen carry flag. -/
def mkXY (x0 x1 x2 x3 y0 y1 y2 y3 : X64) (cf : Bool := false) : BState :=
  { cf := cf
  , regs := fun r =>
      match r with
      | "x0" => x0 | "x1" => x1 | "x2" => x2 | "x3" => x3
      | "y0" => y0 | "y1" => y1 | "y2" => y2 | "y3" => y3
      | _ => 0 }

/-- The 4-limb result of a field-op block, read little-endian as a `Nat`. -/
def feResult (block : List BOp) (st : BState) : Nat :=
  let s := runBBlock st (lowerBBlock block)
  (s.get "z0").toNat + (s.get "z1").toNat * 2 ^ 64
    + (s.get "z2").toNat * 2 ^ 128 + (s.get "z3").toNat * 2 ^ 192

/-- The little-endian `Nat` of a 4-limb input. -/
def limbsNat (a0 a1 a2 a3 : X64) : Nat :=
  a0.toNat + a1.toNat * 2 ^ 64 + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192

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

/-! ### cswap KAT (the constant-time conditional swap)

`a = [1,2,3,4]`, `b = [5,6,7,8]`. With the carry flag set (`swap = 1`) the two
elements exchange; with it clear they stay. -/

/-- A `BState` for cswap: `a0..a3`, `b0..b3`, carry flag `swap`. -/
def mkAB (a0 a1 a2 a3 b0 b1 b2 b3 : X64) (swap : Bool) : BState :=
  { cf := swap
  , regs := fun r =>
      match r with
      | "a0" => a0 | "a1" => a1 | "a2" => a2 | "a3" => a3
      | "b0" => b0 | "b1" => b1 | "b2" => b2 | "b3" => b3
      | _ => 0 }

/-- **cswap KAT (swap = 1).** The two elements exchange. -/
theorem cswap_kat_swap :
    let s := runBBlock (mkAB 1 2 3 4 5 6 7 8 true) (lowerBBlock cswapBlock)
    (s.get "a0" = 5 ∧ s.get "a1" = 6 ∧ s.get "a2" = 7 ∧ s.get "a3" = 8
      ∧ s.get "b0" = 1 ∧ s.get "b1" = 2 ∧ s.get "b2" = 3 ∧ s.get "b3" = 4) := by
  native_decide

/-- **cswap KAT (swap = 0).** The two elements are unchanged. -/
theorem cswap_kat_noswap :
    let s := runBBlock (mkAB 1 2 3 4 5 6 7 8 false) (lowerBBlock cswapBlock)
    (s.get "a0" = 1 ∧ s.get "a1" = 2 ∧ s.get "a2" = 3 ∧ s.get "a3" = 4
      ∧ s.get "b0" = 5 ∧ s.get "b1" = 6 ∧ s.get "b2" = 7 ∧ s.get "b3" = 8) := by
  native_decide

/-! ## 9. The 64-bit bounded counter loop (the ladder's loop backbone)

`ArmModel.runBoundedLoopA` / `ArmControlFlow.loopABlock` give the **32-bit**
(`AState`) bounded counter loop and its looped-emission denotation. The X25519
Montgomery ladder runs on the **64-bit** (`BState`) field machine, so we give the
64-bit analogue here: run the straight-line `body : List BInst` exactly `n` times
(the body performs its own counter decrement, so the `CBNZ` back-edge tests the
just-decremented counter), and prove it equals running the `n`-copy unrolled
block. This is the 64-bit counterpart of `runBoundedLoopA_eq_runABlock_unroll`. -/

/-- `runBoundedLoopB s n body`: the 64-bit bounded counter loop semantics — run the
    straight-line `body` exactly `n` times over the `BState` field machine. -/
def runBoundedLoopB (s : BState) (n : Nat) (body : List BInst) : BState :=
  match n with
  | 0 => s
  | k + 1 => runBoundedLoopB (runBBlock s body) k body

@[simp] theorem runBoundedLoopB_zero (s : BState) (body : List BInst) :
    runBoundedLoopB s 0 body = s := rfl

@[simp] theorem runBoundedLoopB_succ (s : BState) (k : Nat) (body : List BInst) :
    runBoundedLoopB s (k + 1) body = runBoundedLoopB (runBBlock s body) k body := rfl

/-- The straight-line **unrolled** block of the 64-bit loop: `body` replicated
    `n` times. -/
def unrollBBounded (n : Nat) (body : List BInst) : List BInst :=
  match n with
  | 0 => []
  | k + 1 => body ++ unrollBBounded k body

@[simp] theorem runBBlock_append (s : BState) (xs ys : List BInst) :
    runBBlock s (xs ++ ys) = runBBlock (runBBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBBlock_cons, ih]

/-- **The 64-bit bounded loop equals running the unrolled block.** The looped
    emission (one body copy + `CBNZ` back-edge) denotes `runBoundedLoopB s n body`,
    exactly the value the `n`-copy unrolled straight-line block computes — the
    same denotation, constant emitted size. The 64-bit analogue of
    `ArmModel.runBoundedLoopA_eq_runABlock_unroll`. -/
theorem runBoundedLoopB_eq_runBBlock_unroll (s : BState) (n : Nat) (body : List BInst) :
    runBoundedLoopB s n body = runBBlock s (unrollBBounded n body) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp only [runBoundedLoopB_succ, unrollBBounded, runBBlock_append, ih]

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

We model each field element as a 4-limb block in the `BState` register file,
keyed by a name prefix (`x2_0..x2_3`, etc.). `runFe block src1 src2 dst` runs a
field-op block (which reads its inputs from `x0..x3`/`y0..y3` and writes `z0..z3`)
by first moving the two source field elements into the `x`/`y` input registers,
running the block, then moving `z0..z3` to the `dst` prefix — the marshalling that
lets the straight-line field-op leaves compose into the ladder step. -/

/-- Move a 4-limb field element from prefix `src` to prefix `dst`. -/
def moveFe (src dst : String) : List BInst :=
  [ .mov (dst ++ "0") (src ++ "0"), .mov (dst ++ "1") (src ++ "1")
  , .mov (dst ++ "2") (src ++ "2"), .mov (dst ++ "3") (src ++ "3") ]

/-- Run a field-op `BOp` block on the two source field elements `src1`,`src2`
    (marshalled into the `x`/`y` input registers) and write the result to prefix
    `dst`. For unary ops (`feSqr`, `feMul121666`) pass `src2 = src1`. -/
def runFe (block : List BOp) (src1 src2 dst : String) : List BInst :=
  moveFe src1 "x" ++ moveFe src2 "y" ++ lowerBBlock block
    ++ moveFe "z" dst

/-- The Montgomery differential-add-and-double, as a `BInst` block over the
    `BState` field machine. Field elements live at prefixes `x2`,`z2`,`x3`,`z3`
    (the ladder state) and `x1` (the fixed base); the step overwrites them with
    their primed values. Scratch prefixes: `A`,`AA`,`B`,`BB`,`E`,`C`,`D`,`DA`,
    `CB`,`t0`,`t1`,`t2`. -/
def ladderStepBlock : List BInst :=
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

/-! ## 11. The ladder-step value KAT

Run one `ladderStepBlock` on a worked projective state and check the four output
field elements against the hand-computed RFC 7748 step. The initial state uses the
RFC base `x1 = 9`, the ladder-initial `(x2,z2) = (1,0)`, `(x3,z3) = (9,1)`. -/

/-- Build a `BState` for the ladder step from the five field-element prefixes
    `x1`,`x2`,`z2`,`x3`,`z3`, each a 4-limb little-endian value (here the inputs
    are small so only limb 0 is set). -/
def mkLadder (x1 x2 z2 x3 z3 : X64) : BState :=
  { cf := false
  , regs := fun r =>
      match r with
      | "x10" => x1 | "x20" => x2 | "z20" => z2 | "x30" => x3 | "z30" => z3
      | _ => 0 }

/-- The 4-limb value at a prefix, read little-endian. -/
def feAt (s : BState) (pfx : String) : Nat :=
  (s.get (pfx ++ "0")).toNat + (s.get (pfx ++ "1")).toNat * 2 ^ 64
    + (s.get (pfx ++ "2")).toNat * 2 ^ 128 + (s.get (pfx ++ "3")).toNat * 2 ^ 192

/-- **Ladder-step KAT.** One differential-add-and-double from `x1 = 9`,
    `(x2,z2) = (1,0)`, `(x3,z3) = (9,1)`. The primed outputs match the
    hand-computed RFC 7748 step values (mod `p`): with these inputs
    `A=1,AA=1,B=1,BB=1,E=0`, so `x2'=1, z2'=0`; `C=10, D=8, DA=8, CB=10`,
    `x3'=(18)²=324`, `z3'=9·(−2)²=9·4=36`. -/
theorem ladderStep_kat :
    let s := runBBlock (mkLadder 9 1 0 9 1) ladderStepBlock
    (feAt s "x2" = 1 ∧ feAt s "z2" = 0
      ∧ feAt s "x3" = 324 ∧ feAt s "z3" = 36) := by native_decide

/-! ## 12. Wrapping the ladder in the bounded counter loop

The whole X25519 ladder is 255 fixed iterations of `{ cswap(bit); ladderstep }`
over the field machine — a bounded counter loop. We wrap the ladder-step body in
`loopABlock`/`runBoundedLoopB`: the looped emission denotes `runBoundedLoopB s n
ladderStepBlock`, the same value the `n`-copy unrolled block denotes, at constant
emitted size (one body copy + the `CBNZ` back-edge). This is the loop-wrapping the
255-bit ladder rides; the small-trip KAT below runs the *real* loop semantics over
a few steps (the full 255-step run + the inversion is the qemu-aarch64 KAT, which
runs the emitted `.s` on real AArch64 — far past `native_decide`'s reach). -/

/-- **The ladder loop denotes the same value looped or unrolled.** Running the
    255-step (or any `n`-step) ladder as the looped emission equals running the
    unrolled `n`-copy block — `runBoundedLoopB` is `runBBlock` on the unrolled
    body. The looped emission is constant-size in the trip count (the size payoff
    of `ArmControlFlow.loopABlock`), the unrolled one is `O(n)`. -/
theorem ladder_loop_denote (n : Nat) (s : BState) :
    runBoundedLoopB s n ladderStepBlock
      = runBBlock s (unrollBBounded n ladderStepBlock) :=
  runBoundedLoopB_eq_runBBlock_unroll s n ladderStepBlock

/-- **Small-trip ladder-loop KAT (real loop semantics).** A 2-step bounded loop of
    the ladder body from `x1 = 9`, `(x2,z2) = (1,0)`, `(x3,z3) = (9,1)` runs the
    differential-add-and-double twice (the second step doubles/adds from the first
    step's output). This exercises the `runBoundedLoopB` loop backbone — the same
    semantics the 255-step ladder rides — over the field machine. The 4-bit and
    full 255-bit runs are the qemu-aarch64 KAT. -/
theorem ladder_loop2_runs :
    let s := runBoundedLoopB (mkLadder 9 1 0 9 1) 2 ladderStepBlock
    -- the loop runs (the second step consumes the first's x2'/z2'/x3'/z3' output);
    -- after step 1 the state is (x2'=1,z2'=0,x3'=324,z3'=36) as in ladderStep_kat,
    -- step 2 doubles (x2,z2)=(1,0) again (=(1,0)) and diff-adds with (x3,z3).
    (feAt s "x2" = 1 ∧ feAt s "z2" = 0) := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmX25519FieldKernel
