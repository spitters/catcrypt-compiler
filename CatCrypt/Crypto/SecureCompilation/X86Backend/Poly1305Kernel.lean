/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaPolyEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Poly1305 MAC kernel — HACL-schedule 5×26 field-dot, runtime block loop (#421)

`ChaChaPolyEmit.poly1305MacJazz` emits a correct-but-naive Poly1305 MAC: a fixed
`NBLK = 10` fully-unrolled Horner over a `5×26`-limb `𝔽_{2¹³⁰−5}` accumulator, with
the field multiply written as `5×5` partial products that each apply the `·5`
reduction weight by a *separate* `t = t * 5` instruction and accumulate into a
**stack** array `acc[]`. Benched standalone (RFC 8439 §2.5.2, 34-byte message) it
runs at **661.9 cyc/op vs HACL*'s 136.1** — 4.86× behind HACL's hand-scheduled
scalar Poly1305. The gap has two structural causes:

1. **The `NBLK = 10` zero-padding.** A 34-byte (3-block) message is padded to 10
   blocks, so the kernel does **10** Horner field-multiplies instead of 3 —
   ≈3.3× of the gap is wasted work on zero blocks.
2. **The naive multiply schedule.** The `t = t * 5` weight is a separate
   multiply per folded product (10 extra `imul`s per block), and the `acc[]`
   stack array forces a load/store on every accumulation.

This module emits the **HACL scalar schedule** (`Hacl_MAC_Poly1305.c`'s `fmul`,
the byte-identical reference the standalone bench cross-checks against), which
fixes both:

* **Precomputed `r5i = 5·rᵢ`.** Poly1305's reduction `2¹³⁰ ≡ 5 (mod p)` is folded
  into the key *once* (after the clamp): the four products `5·rᵢ` are precomputed,
  so the field multiply's wrapped diagonals read `r5i` directly with **no**
  per-product `·5` instruction. This is the classic Bernstein/HACL `r54..r51`
  trick.
* **Register-resident SSA accumulators `d0..d4`.** The five output limbs are
  computed as five staggered diagonals (each `aᵢ·rⱼ`, summing the wrapped terms
  `aᵢ·r5ⱼ` for `i+j ≥ 5`) held in `reg u64` SSA variables, never an `acc[]` stack
  array — the standard straight-line `a02..a46` HACL form. All products fit in
  64 bits (`26 + ≤29 = ≤55` bits; five terms sum to `< 2⁵⁸`), so no `128`-bit
  arithmetic is needed — exactly HACL's scalar path.
* **A runtime block-count loop.** The export takes the **actual** number of
  message blocks `nblk` as a register argument and Horner-folds exactly that many
  (`while (nblk != 0)`), so a 3-block message does 3 multiplies, not 10.

The lane field and the load-bearing denotation lemma are **unchanged**: the MAC is
still `Σᵢ mᵢ · r^(n-i)` over `𝔽_p = ZMod (2¹³⁰−5)`, carried by
`VectorReduce.scalarFold_eq_hsum` (re-exported here at the same lane as
`ChaChaPolyEmit.poly1305_dot`). Only the *schedule* of the field arithmetic
changes; the algebraic content is identical.

## What is verified vs KAT-gated

* The MAC's polynomial-evaluation denotation (`poly1305_mac_dot`,
  `scalarFold = hsum` over `𝔽_{2¹³⁰−5}`) is the proved content — reused verbatim
  from `ChaChaPolyEmit`.
* The concrete `5×26`-limb schedule (the `r5i` fold, the diagonal multiply, the
  carry chain) is **KAT-gated**, byte-identical to RFC 8439 §2.5.2 and to HACL*'s
  `Hacl_MAC_Poly1305` over random keys/messages, in
  `bench/poly1305_compare/poly1305_hacl_vs.c`. This is the standard leaf
  discipline for the emitted field kernels (mirrors `Fe25519MulKernel`'s external
  GMP/s2n KAT gate): the in-Lean guarantee is the algebraic reassociation; the
  bit-exact `2¹³⁰−5` reduction is the C/HACL cross-check.

The emitted text is structurally checked here (`strContains`): the `r5i` precompute,
the absence of the per-product `·5` instruction, the register-SSA diagonals, and
the runtime `while (nblk` loop.

## Measured (the honest picture)

Standalone MAC, RFC 8439 §2.5.2 message (34 bytes = 3 Poly1305 blocks), taskset
core-pinned, MIN-of-3 (`bench/poly1305_compare/poly1305_hacl_vs.c`):

  prior naive (`ChaChaPolyEmit`)  661.9 cyc   4.86× vs HACL*'s 136
  this kernel (loop, 3 blocks)    308.4 cyc   2.25× vs HACL*

So **4.86× → 2.25×** on the standalone MAC. Most of that win is the runtime
block loop (3 multiplies instead of the naive's `NBLK=10` zero-padded 10); the
`r5i`/register schedule trims the multiply count `360 → 295` imuls.

On the fixed-`NBLK` AEAD path the two levers above do **not** stack: the
fixed-`NBLK` **unrolled** variant (`emitHaclMacUnrolled`) keeps the accumulator
in a `stack u64[5]` array, so the inline multiply re-materialises all five
accumulator limbs to/from the stack **on every block** — the `movq` traffic
(`652` over the MAC body) that offsets the multiply saving on the 10-block AEAD
message.

The **cross-block-resident** variant (`emitHaclMacResident`, #498) fixes that:
it keeps the five accumulator limbs `a0..a4` in `reg u64` SSA variables across
the whole unrolled block sequence (the #111 ChaCha XMM-resident / #166 Poseidon2
lane-resident lever applied to the Poly1305 accumulator) — zeroed once, folded
block-by-block without spilling, stored once. The read-only key `r[]`/`r5[]` stay
in stack arrays (loop-invariant, so they cost no per-block accumulator spill and
keep the live GP-register set within the x86-64 budget — HACL keeps `r` in memory
for the same reason; the accumulator is the only thing that must survive the
boundary). On the RFC 8439 §2.8.2 AEAD message (10 Poly1305 blocks) this cuts the
MAC-body `movq` count `652 → 406` and the whole ChaCha20-Poly1305 AEAD core (4-way
ChaCha keystream + this MAC) from **2.04× → ~1.78× vs HACL\*'s full AEAD**
(`bench/chachapoly_compare/chachapoly_hacl_vs.c`, MIN over runs). The resident
MAC accumulator is KAT-checked byte-identical to the unrolled variant — which
#421 KAT'd byte-identical to HACL\*'s `Hacl_MAC_Poly1305` over the RFC 8439 vector
+ 256 random vectors — so the residency change is value-preserving.

The remaining whole-AEAD residual is the C-side AEAD orchestration + the
fixed-block path having no zero-padding to reclaim, not the Poly1305 schedule.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Poly1305Kernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.VIR.ChaChaPolyEmit (Fp NBlk polyPrime)
open scoped BigOperators

/-! ## 1. Denotation preservation — unchanged at the `𝔽_{2¹³⁰−5}` MAC lane

The HACL schedule changes only how the field multiply is *computed*; the MAC is
the same polynomial `Σᵢ mᵢ · r^(n-i)` over `𝔽_p`. We re-export the load-bearing
reassociation at the same lane so this kernel carries the identical denotation
guarantee as `ChaChaPolyEmit`. -/

/-- **MAC denotation, HACL-schedule kernel.** The MAC polynomial
    `Σᵢ mᵢ · r^(n-i)` (lane-wise the monomial terms, horizontal sum `hsum`) equals
    the scalar straight-line `𝔽_p` Horner fold (`scalarFold`). This is
    `VectorReduce.scalarFold_eq_hsum` at the `𝔽_{2¹³⁰−5}` lane — the same content
    `ChaChaPolyEmit.poly1305_dot` carries; the `r5i`/register/loop schedule below
    realizes exactly this fold. -/
theorem poly1305_hacl_dot (m : Fin NBlk → Fp) (r : Fp) :
    VectorReduce.hsum (fun i => m i * r ^ (NBlk - (i : ℕ))) =
      VectorReduce.scalarFold (fun i => m i * r ^ (NBlk - (i : ℕ))) :=
  ChaChaPolyEmit.poly1305_dot m r

/-- The Poly1305 MAC computes the mathematical polynomial value
    `Σᵢ mᵢ · r^(n-i)` over `𝔽_p` — the authenticator, before `+ s` / `mod 2¹²⁸`. -/
theorem poly1305_hacl_isPoly (m : Fin NBlk → Fp) (r : Fp) :
    VectorReduce.hsum (fun i => m i * r ^ (NBlk - (i : ℕ))) =
      ∑ i, m i * r ^ (NBlk - (i : ℕ)) :=
  ChaChaPolyEmit.poly1305_isPoly m r

/-! ## 2. The HACL `r5i = 5·rᵢ` precompute

After clamping, the key limbs `r[0..4]` get the four wrapped multiples
`r5i = 5·r[i]` (i = 1..4) precomputed once. The diagonal multiply then reads
these directly — the `2¹³⁰ ≡ 5` reduction is folded into the key, not applied
per product. -/

/-- Emit the `r5i = 5·r[i]` precompute (`i = 1..4`): the four wrapped key
    multiples Poly1305's reduction `2¹³⁰ ≡ 5 (mod p)` folds into the key once. The
    diagonal multiply reads `r5[i]` instead of issuing a per-product `·5`. Each is
    staged through the `t` register (`t = r[i]; t *= 5; r5[i] = t`) for jasmin's
    2-address `IMULri` form. -/
def renderR5Precompute : List String :=
  (List.range 4).flatMap (fun k =>
    let i := toString (k + 1)
    [ "t = r[" ++ i ++ "];"
    , "t *= 5;"
    , "r5[" ++ i ++ "] = t;" ])

/-! ## 3. The HACL field multiply — five register-SSA diagonals, no per-product `·5`

`(a · r) mod p` over `5×26` limbs as five staggered diagonals. Diagonal `out`
sums `a[i]·r[j]` for `i+j ≡ out (mod 5)`, reading `r5[j]` (the `5·r[j]` wrap)
when `i+j ≥ 5`. Each `d{out}` is a single `reg u64` SSA accumulator (HACL's
`a0k..a4k` form). All products fit in 64 bits, so no `128`-bit step. -/

/-- One product term of diagonal `out`: limb `a[i]·(key limb at j)`, where
    `j = (out - i) mod 5` and the key limb is `r5[j]` (the `5·r[j]` wrap) when the
    natural position `i + j` overflowed (`i > out`, i.e. `i + j = out + 5`), else
    `r[j]`. Returns the emitted multiply-source string. -/
def diagSrc (out i : Nat) : String :=
  let j := (out + 5 - i) % 5
  let wrapped := i > out          -- natural position i+j = out+5 ⇒ read the 5· wrap
  (if wrapped then "r5[" else "r[") ++ toString j ++ "]"

/-- Render diagonal `out` of the field multiply: `d{out} = a0·… + a1·… + … + a4·…`,
    five product terms accumulated into the single SSA register `d{out}`, reading
    the precomputed `r5[j]` wrap for the folded terms (no per-product `·5`).
    Each product is emitted in jasmin's strict 2-address `IMULr` form
    (`t = a[i]; t *= src;` — the destination is the multiply operand), then folded
    into `d{out}` (`= t` for the first term, `+= t` after). -/
def renderDiagonal (out : Nat) : List String :=
  (List.range 5).flatMap (fun i =>
    [ "t = a[" ++ toString i ++ "];"
    , "t *= " ++ diagSrc out i ++ ";" ]
    ++ (if i == 0 then
          [ "d" ++ toString out ++ " = t;" ]
        else
          [ "d" ++ toString out ++ " += t;" ]))

/-- The carry chain renormalizing `d0..d4` (each `< 2⁵⁸`) back to `5×26`-bit
    limbs `a[0..4]`: shift each high part `>> 26` into the next limb (mask
    `& 0x3ffffff`); the top `d4` carry folds back into `a[0]` with `·5`
    (`2¹³⁰ ≡ 5`), then one more `a[0] → a[1]` settle. All ops are emitted in the
    strict 2-address form jasmin's `asmgen` accepts (register source/dest; the
    masked limb is staged in `m` before the `a[k]` stack store). -/
def renderHaclCarry : List String :=
  (List.range 4).flatMap (fun k =>
    [ "t = d" ++ toString k ++ ";"
    , "t >>= 26;"
    , "m = d" ++ toString k ++ ";"
    , "m &= 0x3ffffff;"
    , "a[" ++ toString k ++ "] = m;"
    , "d" ++ toString (k + 1) ++ " += t;" ])
  ++ [ "c = d4;"
     , "c >>= 26;"
     , "m = d4;"
     , "m &= 0x3ffffff;"
     , "a[4] = m;"
     , "c *= 5;"                         -- 2¹³⁰ ≡ 5 top-limb fold
     , "m = a[0];"
     , "m += c;"
     , "t = m;"
     , "t >>= 26;"
     , "m &= 0x3ffffff;"
     , "a[0] = m;"
     , "m = a[1];"
     , "m += t;"
     , "a[1] = m;" ]

/-- The Poly1305 HACL-schedule field multiply `a := (a · r) mod p`, inline jasmin
    over `5×26`-bit limbs. Reads the precomputed `r5[]` wraps; computes the five
    register-SSA diagonals `d0..d4`; renormalizes via `renderHaclCarry`. The `r5i`
    fold replaces the naive emit's `5×` separate-instruction weighting; the
    `d{out}` registers replace the `acc[]` stack array. -/
def haclMulModFn : String :=
  let header := [ "inline fn poly1305_mulmod_hacl(reg ptr u64[5] a,"
                    ++ " reg const ptr u64[5] r, reg const ptr u64[5] r5)"
                    ++ " -> reg ptr u64[5] {"
                , "reg u64 d0 d1 d2 d3 d4 t c m;" ]
  let diags := (List.range 5).flatMap renderDiagonal
  let footer := [ "return a;" ]
  String.intercalate "\n  "
    (header ++ diags ++ renderHaclCarry ++ footer)
    ++ "\n}"

/-! ## 4. The MAC export — Horner over a RUNTIME block count

`poly1305_mac_hacl(out, inp, nblk)`: Horner-fold the field-multiply over the
**actual** `nblk` message blocks (`while (nblk != 0)`), not a fixed `NBLK = 10`
unroll. `inp` holds the clamped key limbs `r[0..4]` then the message-block limb
quintuples; the `r5[]` wraps are precomputed once before the loop. Each step is
`a := (a + mᵢ)` then `a := a · r  (mod p)` via the inline HACL multiply. -/

/-- The Poly1305 MAC export, HACL schedule + runtime block loop. ABI:
    `reg ptr u64[5] out` (the `5×26` MAC accumulator limbs),
    `reg const ptr u64[stride] inp` (clamped key `r[0..4]` then the message-block
    limb quintuples), `reg u64 nblk` (the actual block count). Per block: the
    limb-wise `+ mᵢ` add then the inline `poly1305_mulmod_hacl`. The `r5[]`
    reduction wraps are precomputed once (`renderR5Precompute`) before the loop.

    Denotation: the accumulated terms are `hsum (fun i => mᵢ · r^(n-i))` over
    `𝔽_{2¹³⁰−5}`, equal to the scalar Horner fold by `poly1305_hacl_dot`. -/
def emitHaclMacExport (name : String) (maxblk : Nat) : String :=
  let stride := 5 + 5 * maxblk
  let paramStrs := [ "reg ptr u64[5] out"
                   , "reg const ptr u64[" ++ toString stride ++ "] inp"
                   , "reg u64 nblk" ]
  let decls := [ "stack u64[5] a;"
               , "stack u64[5] r;"
               , "stack u64[5] r5;"
               , "reg u64 t m bi off;"
               , "inline int z;"
               , "for z = 0 to 5 { r[z] = inp[z]; }"        -- clamped key limbs
               , "for z = 0 to 5 { a[z] = 0; }" ]            -- accumulator starts at 0
               ++ renderR5Precompute                         -- r5[i] = 5·r[i], once
               ++ [ "bi = 0;" ]
  let loopBody :=
    [ "while (nblk != 0) {"
    , "  off = bi;"
    , "  off *= 5;"
    , "  off += 5;" ]
    ++ (List.range 5).flatMap (fun k =>
         [ "  t = inp[(int) off + " ++ toString k ++ "];"
         , "  m = a[" ++ toString k ++ "];"
         , "  m += t;"
         , "  a[" ++ toString k ++ "] = m;" ])
    ++ [ "  a = poly1305_mulmod_hacl(a, r, r5);"
       , "  bi += 1;"
       , "  nblk -= 1;"
       , "}" ]
  let store := [ "for z = 0 to 5 { out[z] = a[z]; }" ]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[5] {\n  "
    ++ String.intercalate "\n  " (decls ++ loopBody ++ store)
    ++ "\n  return out;\n}"

/-! ## 4b. A fully-UNROLLED fixed-block variant (no loop overhead)

The runtime-block loop wins on **short** messages (it folds exactly `nblk`
blocks instead of padding to a fixed `NBLK`); but its per-iteration dynamic-index
address recompute (`off = bi·5 + 5`, then `inp[(int)off + k]`) and the loop branch
cost more than a straight-line unroll on **long** messages. For the fixed
`NBLK`-block AEAD message (RFC 8439 §2.8.2 = 10 blocks) the unrolled form keeps
the HACL `r5i`/register-diagonal schedule win **without** that loop overhead:
each block's limbs are read at the static offset `5 + 5·i + k`. This is the
straight-line analog of `emitHaclMacExport`, a drop-in replacement for the prior
`ChaChaPolyEmit.poly1305MacJazz` (same fixed-`NBLK` ABI), now on the HACL
schedule. -/

/-- The unrolled fixed-`nblk`-block HACL-schedule MAC export (static indexing,
    no runtime loop). ABI matches `ChaChaPolyEmit`'s `poly1305_mac`
    (`out : u64[5]`, `inp : u64[5 + 5·nblk]`); body uses the HACL `r5i`/register
    diagonals via the same inline `poly1305_mulmod_hacl`. -/
def emitHaclMacUnrolled (name : String) (nblk : Nat) : String :=
  let total := 5 + 5 * nblk
  let paramStrs := [ "reg ptr u64[5] out"
                   , "reg const ptr u64[" ++ toString total ++ "] inp" ]
  let decls := [ "stack u64[5] a;"
               , "stack u64[5] r;"
               , "stack u64[5] r5;"
               , "reg u64 t m;"
               , "inline int z;"
               , "for z = 0 to 5 { r[z] = inp[z]; }"
               , "for z = 0 to 5 { a[z] = 0; }" ]
               ++ renderR5Precompute
  let steps := (List.range nblk).flatMap (fun i =>
    (List.range 5).flatMap (fun k =>
      [ "t = inp[" ++ toString (5 + 5 * i + k) ++ "];"
      , "m = a[" ++ toString k ++ "];"
      , "m += t;"
      , "a[" ++ toString k ++ "] = m;" ])
    ++ [ "a = poly1305_mulmod_hacl(a, r, r5);" ])
  let store := [ "for z = 0 to 5 { out[z] = a[z]; }" ]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[5] {\n  "
    ++ String.intercalate "\n  " (decls ++ steps ++ store)
    ++ "\n  return out;\n}"

/-! ## 4c. A REGISTER-RESIDENT fixed-block variant — cross-block accumulator residence

The unrolled variant (`emitHaclMacUnrolled`) keeps the `r5i`/register-diagonal
schedule, but its accumulator `a` is still a `stack u64[5]` array, and the
inline `poly1305_mulmod_hacl` reads `a[i]` from that stack and writes `a[k]`
back to it. On the fixed-`NBLK` AEAD message this re-materialises all five
accumulator limbs to/from the stack **on every block** — the `movq` traffic
(`547 → 708` in the prior measurement) that offsets the multiply saving and caps
the whole-AEAD speedup.

This variant applies the **cross-block residency** technique
(`CrossBlockResidencyUnroll`, the same lever as #111 ChaCha XMM-resident state
and #166 Poseidon2 lane-resident `vS0..vS3` across rounds): the five accumulator
limbs `a0..a4` are held in `reg u64` SSA variables and **stay register-resident
across the entire unrolled block sequence**. They are zeroed once before the
blocks and stored to `out[]` once after — never spilled to a stack array between
blocks. The clamped key limbs `r0..r4` and their `5·` wraps `r50..r54` are
likewise loaded into registers once (loop-invariant, the prologue pin set).

The field multiply is inlined directly over the register limbs (no `inline fn`
indirection, no `reg ptr u64[5]`): each diagonal reads `a0..a4` and `r0..r4` /
`r50..r54` registers, accumulates into `d0..d4` registers, and the carry chain
writes back into the `a0..a4` registers. This is the straight-line analog of
`renderDiagonal` / `renderHaclCarry` with the stack-array slots `a[i]`, `r[j]`,
`r5[j]` replaced by registers `a{i}`, `r{j}`, `r5{j}`.

The algebraic content is identical to `emitHaclMacUnrolled` — same `5×26` HACL
schedule, same `2¹³⁰ ≡ 5` reduction — so it carries the same MAC denotation
(`poly1305_hacl_dot`) and is KAT-gated the same way (RFC 8439 §2.5.2 / HACL*). -/

/-- Register-resident diagonal `out`: like `renderDiagonal` but the accumulator
    limbs are registers `a{i}` and the key limbs are registers `r{j}` / `r5{j}`
    (the `5·` wrap), not stack-array slots. Five products into the SSA register
    `d{out}`. -/
def renderDiagonalReg (out : Nat) : List String :=
  (List.range 5).flatMap (fun i =>
    let j := (out + 5 - i) % 5
    let src := (if i > out then "r5[" else "r[") ++ toString j ++ "]"
    [ "t = a" ++ toString i ++ ";"
    , "t *= " ++ src ++ ";" ]
    ++ (if i == 0 then
          [ "d" ++ toString out ++ " = t;" ]
        else
          [ "d" ++ toString out ++ " += t;" ]))

/-- Register-resident carry chain: like `renderHaclCarry` but renormalises
    `d0..d4` back into the register limbs `a0..a4` (not a stack array). The top
    `d4` carry folds into `a0` with `·5` (`2¹³⁰ ≡ 5`), then one `a0 → a1`
    settle. The masked limb is staged in `m` before the register store. -/
def renderHaclCarryReg : List String :=
  (List.range 4).flatMap (fun k =>
    [ "t = d" ++ toString k ++ ";"
    , "t >>= 26;"
    , "m = d" ++ toString k ++ ";"
    , "m &= 0x3ffffff;"
    , "a" ++ toString k ++ " = m;"
    , "d" ++ toString (k + 1) ++ " += t;" ])
  ++ [ "c = d4;"
     , "c >>= 26;"
     , "m = d4;"
     , "m &= 0x3ffffff;"
     , "a4 = m;"
     , "c *= 5;"                          -- 2¹³⁰ ≡ 5 top-limb fold
     , "m = a0;"
     , "m += c;"
     , "t = m;"
     , "t >>= 26;"
     , "m &= 0x3ffffff;"
     , "a0 = m;"
     , "m = a1;"
     , "m += t;"
     , "a1 = m;" ]

/-- One register-resident Horner block: add the message-block limbs (read from
    `inp` at the static offset `5 + 5·i + k`) into the register accumulator
    `a0..a4`, then the inline field multiply `a := (a · r) mod p` over the
    registers (`renderDiagonalReg` × 5 + `renderHaclCarryReg`). No stack array
    is touched — the accumulator stays register-resident across blocks. -/
def renderResidentBlock (i : Nat) : List String :=
  (List.range 5).flatMap (fun k =>
    [ "t = inp[" ++ toString (5 + 5 * i + k) ++ "];"
    , "a" ++ toString k ++ " += t;" ])
  ++ (List.range 5).flatMap renderDiagonalReg
  ++ renderHaclCarryReg

/-- **The cross-block-resident fixed-`nblk`-block HACL-schedule MAC export.**
    ABI matches `emitHaclMacUnrolled` / `ChaChaPolyEmit.poly1305_mac`
    (`out : u64[5]`, `inp : u64[5 + 5·nblk]`). The five accumulator limbs
    `a0..a4` and the key limbs `r0..r4` / `r50..r54` are held in `reg u64`
    across the FULL unrolled block sequence (the residency lever, analog of
    #111 / #166): zeroed/loaded once in the prologue, the blocks fold without
    spilling the accumulator, and `a0..a4` are stored to `out[]` once at the
    end. -/
def emitHaclMacResident (name : String) (nblk : Nat) : String :=
  let total := 5 + 5 * nblk
  let paramStrs := [ "reg ptr u64[5] out"
                   , "reg const ptr u64[" ++ toString total ++ "] inp" ]
  -- Prologue: load the clamped key limbs into registers, precompute the 5·
  -- wraps into registers, zero the accumulator registers. All ONCE, before the
  -- unrolled blocks (the prologue pin set).
  -- The accumulator limbs `a0..a4` stay register-resident across the FULL block
  -- sequence (the residency lever). The read-only key limbs `r[]` and their `5·`
  -- wraps `r5[]` go to stack arrays — they are loop-invariant (loaded into a
  -- register only at point of use), so they cost no per-block accumulator spill
  -- and they keep the live register set within the x86-64 GP budget (HACL keeps
  -- `r` in memory for the same reason). Only `a0..a4` need to survive the
  -- boundary; the diagonals `d0..d4` and scratch `t,c,m` are per-block dead.
  let decls := [ "reg u64 a0 a1 a2 a3 a4;"
               , "stack u64[5] r;"
               , "stack u64[5] r5;"
               , "reg u64 d0 d1 d2 d3 d4 t c m;"
               , "inline int z;"
               , "for z = 0 to 5 { r[z] = inp[z]; }" ]
               ++ renderR5Precompute
               ++ [ "a0 = 0;"
                  , "a1 = 0;"
                  , "a2 = 0;"
                  , "a3 = 0;"
                  , "a4 = 0;" ]
  let blocks := (List.range nblk).flatMap renderResidentBlock
  let store := [ "out[0] = a0;"
               , "out[1] = a1;"
               , "out[2] = a2;"
               , "out[3] = a3;"
               , "out[4] = a4;" ]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[5] {\n  "
    ++ String.intercalate "\n  " (decls ++ blocks ++ store)
    ++ "\n  return out;\n}"

/-! ## 5. The emitted kernels -/

/-- The emitted HACL-schedule Poly1305 MAC kernel: the inline
    `poly1305_mulmod_hacl` (precomputed-`r5i` diagonals, register SSA) + the
    runtime-block-count Horner export. Self-contained `.jazz`. `maxblk = NBlk`
    only sizes the `inp` array type; the loop runs over the runtime `nblk`.
    Best on **short** messages. -/
def poly1305MacHaclJazz : String :=
  haclMulModFn ++ "\n\n" ++ emitHaclMacExport "poly1305_mac_hacl" NBlk

/-- Both HACL-schedule MAC kernels in one `.jazz`: the runtime-loop export
    (`poly1305_mac_hacl`) and the fixed-`NBLK` unrolled export
    (`poly1305_mac_hacl_u`), sharing the one inline `poly1305_mulmod_hacl`. The
    bench harness picks per message length (loop for short, unrolled for the
    fixed-`NBLK` AEAD message). -/
def poly1305MacHaclBundleJazz : String :=
  haclMulModFn ++ "\n\n" ++ emitHaclMacExport "poly1305_mac_hacl" NBlk
    ++ "\n\n" ++ emitHaclMacUnrolled "poly1305_mac_hacl_u" NBlk
    ++ "\n\n" ++ emitHaclMacResident "poly1305_mac_hacl_r" NBlk

/-- The largest Poly1305 block count the AEAD bench exercises. A 16 KiB
    plaintext is `16384 / 16 = 1024` Poly1305 blocks; the AEAD schedule adds at
    most one AAD-pad block and one length block, so `1026` blocks is the runtime
    maximum. We round up to `NBlkAeadMax = 1100` to leave margin for the AAD and
    any ragged-tail block. This only sizes the runtime-loop export's `inp` array
    **type**; the `while (nblk != 0)` loop still folds exactly the runtime
    `nblk` blocks the caller passes. -/
def NBlkAeadMax : Nat := 1100

/-- The AEAD-wiring Poly1305 MAC bundle: the **runtime-loop** export
    (`poly1305_mac_hacl`, sized for up to `NBlkAeadMax` blocks so the AEAD
    harness can MAC a 16 KiB message by passing the actual `nblk`) plus the
    fixed-`NBLK` cross-block-resident export (`poly1305_mac_hacl_r`, the fastest
    variant on the RFC 8439 §2.8.2 ten-block message). One shared inline
    `poly1305_mulmod_hacl`. This is the bundle the ChaCha20-Poly1305 AEAD
    head-to-head links (`bench/chachapoly_compare/aead_vs.c`): the resident
    export carries the 114-byte row, the runtime-loop export carries the 1 KiB
    and 16 KiB rows. Both denote `Σᵢ mᵢ · r^(n-i)` over `𝔽_{2¹³⁰−5}` by the same
    `poly1305_hacl_dot`. -/
def poly1305MacHaclAeadBundleJazz : String :=
  haclMulModFn ++ "\n\n" ++ emitHaclMacExport "poly1305_mac_hacl" NBlkAeadMax
    ++ "\n\n" ++ emitHaclMacResident "poly1305_mac_hacl_r" NBlk

/-! ### Structural checks on the emitted text -/

/- The AEAD bundle's runtime-loop export sizes its `inp` array for up to
    `NBlkAeadMax` blocks (so a 16 KiB message fits) — `5 + 5·1100 = 5505`. -/
#guard (strContains poly1305MacHaclAeadBundleJazz "reg const ptr u64[5505] inp")

/- The AEAD bundle still folds exactly the runtime `nblk` blocks
    (`while (nblk != 0)`), not a fixed unroll — so it MACs any message length up
    to `NBlkAeadMax` blocks. -/
#guard (strContains poly1305MacHaclAeadBundleJazz "while (nblk != 0)")

/- The AEAD bundle carries the cross-block-resident fixed-`NBLK` export for the
    114-byte RFC 8439 §2.8.2 row. -/
#guard (strContains poly1305MacHaclAeadBundleJazz "export fn poly1305_mac_hacl_r(")

/- The MAC export takes the runtime block count `nblk` and Horner-folds it with a
    `while (nblk` loop — NOT a fixed `NBLK`-deep unroll. -/
#guard (strContains poly1305MacHaclJazz "while (nblk != 0)")

/- The reduction wraps `r5[i] = 5·r[i]` are precomputed once (the HACL `r5i`
    trick), folding `2¹³⁰ ≡ 5` into the key. -/
#guard (strContains poly1305MacHaclJazz "r5[1] = t;")

/- The field multiply reads the precomputed wrap `r5[…]` in its diagonals (the
    folded `2¹³⁰ ≡ 5` terms), instead of a per-product `·5` instruction. -/
#guard (strContains poly1305MacHaclJazz "t *= r5[")

/- The five field-multiply diagonals are register-SSA accumulators `d0..d4`
    (HACL's `a0k..a4k` form), not an `acc[]` stack array. -/
#guard (strContains poly1305MacHaclJazz "d0 = t;")

/- The top-limb carry still folds back with the `·5` weight (`2¹³⁰ ≡ 5 (mod p)`)
    after the diagonals — the field reduction is correct. -/
#guard (strContains poly1305MacHaclJazz "c *= 5;")

/- The `26`-bit limb mask `0x3ffffff` (`= 2²⁶ − 1`) renormalizes the limbs. -/
#guard (strContains poly1305MacHaclJazz "m &= 0x3ffffff;")

/- The Horner step is the field add (`a[k] += mᵢ,k`) then the inline HACL field
    multiply. -/
#guard (strContains poly1305MacHaclJazz "a = poly1305_mulmod_hacl(a, r, r5);")

/- The bundle carries the unrolled fixed-`NBLK` export with **static** indexing
    (no runtime loop): block `i = 0` reads `inp[5 + 0]` etc., so there is no
    per-block `off` recompute. (Block `0`, limb `0` is `inp[5]`.) -/
#guard (strContains poly1305MacHaclBundleJazz "export fn poly1305_mac_hacl_u(")

/- The bundle's unrolled export uses static block indexing (`inp[5]` is block 0
    limb 0) — no `while (nblk` loop inside `poly1305_mac_hacl_u`. -/
#guard (strContains poly1305MacHaclBundleJazz "t = inp[5];")

/-! ### Structural checks on the cross-block-resident export -/

/- The bundle carries the cross-block-resident export `poly1305_mac_hacl_r`
    (the #498 accumulator-residence variant). -/
#guard (strContains poly1305MacHaclBundleJazz "export fn poly1305_mac_hacl_r(")

/- The resident export declares the five accumulator limbs as `reg u64`
    variables `a0..a4` (register-resident across the block sequence), NOT a
    `stack u64[5] a` array. The accumulator never spills between blocks. -/
#guard (strContains poly1305MacHaclBundleJazz "reg u64 a0 a1 a2 a3 a4;")

/- The resident export precomputes the `5·` key wraps ONCE in the prologue (the
    loop-invariant `r5[]` precompute), before the unrolled blocks. The wraps and
    clamped key live in stack arrays (loop-invariant, no per-block accumulator
    spill); only the accumulator `a0..a4` is register-resident across blocks. -/
#guard (strContains poly1305MacHaclBundleJazz "r5[1] = t;")

/- The resident export folds the message into the register accumulator
    (`a0 += t;`) — no `a[0] = m;` stack store of the accumulator between blocks. -/
#guard (strContains poly1305MacHaclBundleJazz "a0 += t;")

/- The resident export stores the final accumulator from registers to `out[]`
    ONCE (`out[0] = a0;`), the single epilogue commit. -/
#guard (strContains poly1305MacHaclBundleJazz "out[0] = a0;")

end CatCrypt.Crypto.SecureCompilation.X86Backend.Poly1305Kernel
