/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel

/-!
# BLS12-381 pairing tower, squaring layer + cyclotomic squaring, owned x86 (#602/#219)

**Variant: RELIC-transcribed (tests-only correctness).**

**STRING-TEMPLATED — not verified-compiler output:** the emitted
`bls12381_*_x86_from_lean.s` is assembled as literal asm-line text
(`framedDriver`/`renderLeafFn` join `movq`/`leaq`/`call` string literals), with
no `Com`/`Lprog` IR and no verified printer, so no theorem relates the emitted
bytes to a source; the byte-identity to RELIC below is the only corroboration.

This owned x86 emit is
hand-transcribed from the RELIC pairing reference and gated **byte-identical to
RELIC**. RELIC is unverified C, so that byte-identity is a **test**, not a
correctness proof. The verified-correctness BLS variant — owned emit whose
denotation is tied to the **AUCurves** Rocq-proved pairing via the rocqlean
axiom bridge — is a **separate** artifact, kept distinct from this one so the
RELIC-transcribed and AUCurves-generated variants can be compared.

Continued **one layer up** from the committed `Fp6`/`Fp12` multiply
(`Bls12381Fp6Fp12MulKernel`, commit e8006039): the **squarings** of the pairing
tower, which the final exponentiation and the Miller-loop `f`-accumulation drive
hardest.

Emitted owned drivers (no jasminc), composing the committed leaves:

* `bls12381_fp2_dbl`        — `Fp2` doubling (`z = x + x`), two `Fp` adds.
* `bls12381_fp6_dbl`        — `Fp6` doubling, three `Fp2` adds.
* `bls12381_fp12_sqr`       — `Fp12` Karatsuba square (RELIC `fp12_sqr_basic`):
  `2 Fp6`-muls + 2 `fp6_mul_art` + `Fp6` add/sub/dbl.  No `Fp` halving.
* `bls12381_fp12_sqr_cyc`   — **cyclotomic** `Fp12` square (RELIC
  `fp12_sqr_cyc_basic`, Granger–Scott): the final-exp hot loop, built from
  `Fp2` sqr / mul-by-ξ / add / sub / dbl only.  No `Fp6`-mul, no `Fp` halving.

## Why these layers, and why basic == lazyr for the KAT

The BLS12-381 RELIC builds (`build`, `build-bls381-asm`) set `FPX_RDC = LAZYR`,
so `fp12_sqr` / `fp12_sqr_cyc` dispatch to the lazy-reduced variants. Lazy
reduction changes only **when** a modular reduction is applied, never the
**field-element value** computed. The owned drivers below realise the *basic*
schedules (the published Chung–Hasan / Granger–Scott formulas); the bench KAT
bridges every `Fp` component through canonical GMP `mpz` (the same
reduction-agnostic oracle the committed `fp6_mul`/`fp12_mul` KAT already uses),
so owned (basic) and RELIC (lazyr) must both equal the canonical product. This
is exactly the byte-identical-via-canonical-bridge gate the committed mul layer
passed.

## Real `Fp`-mul call counts (the tower call graph)

* `fp12_sqr`     = 2 `Fp6`-muls = **108 `Fp`-muls** (= 2 × 54), the
  RELIC `fp12_sqr_basic` Karatsuba graph (not a 0–1-mul stub).
* `fp12_sqr_cyc` = 9 `Fp2`-squarings = **27 `Fp`-muls** (each `Fp2`-sqr = 3
  `Fp`-muls); cyclotomic squaring is *much* cheaper than a generic `Fp12`
  square — that is the whole point of compressing into the cyclotomic subgroup
  for the final exponentiation.

## Scope: the remaining gap to a fully-owned `pp_map`

This module lands the **squaring** layer of the tower. The two remaining layers
to a fully-owned `pp_map` are documented but **not** emitted here:

* the **sparse line multiply** `fp12_mul_dxs` — RELIC's body branches on the
  twist type (`ep2_curve_is_twist()`, D-type vs M-type) and on `EP_ADD`
  (`PROJC`/`JACOB`/`BASIC`), so a byte-identical KAT requires reproducing the
  exact sparse line-coordinate layout the Miller loop feeds it under the *same*
  curve config the linked RELIC was built with (the two installed BLS12-381
  builds even disagree: `gmp` uses `EP_ADD=PROJC`, `asm` uses `JACOB`);
* the **Miller loop** driver (`pp_mil_k12`) — `G2` point doubling/addition with
  line evaluation over the BLS `x = -0xd201000000010000` NAF, accumulating into
  `f`. This needs the full `Fp2` `G2` group law (projective doubling/addition
  formulas) on top of the field tower, plus the final exponentiation
  (`pp_exp_k12`: easy part `(p^6-1)(p^2+1)` via Frobenius `p`-power maps +
  inverse, hard part as a cyclotomic/NAF addition chain over `fp12_sqr_cyc`).

The squaring layer emitted here is the field-arithmetic prerequisite both of
those layers consume; the precise remaining gap is **`G2` arithmetic +
Frobenius + the curve-config-locked sparse mul**, not more tower field ops.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Pairing

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel

/-! ## 0. Owned-leaf symbol names (committed/emitted lower-tier kernels) -/

/-- Committed `Fp2` mul driver. -/
def fp2MulSym : String := "bls12381_fp2_mul_x86_from_lean"
/-- Committed `Fp2` sqr driver (`Bls12381Fp2MulKernel.fp2SqrAsm`). -/
def fp2SqrSym : String := "bls12381_fp2_sqr_x86_from_lean"
/-- Emitted `Fp2` add (committed in the Fp6/Fp12 module). -/
def fp2AddSym : String := "bls12381_fp2_add_x86_from_lean"
/-- Emitted `Fp2` sub. -/
def fp2SubSym : String := "bls12381_fp2_sub_x86_from_lean"
/-- Emitted `Fp2` mul-by-ξ=(1+u). -/
def fp2NorSym : String := "bls12381_fp2_mul_nor_x86_from_lean"
/-- Emitted `Fp2` doubling (this module). -/
def fp2DblSym : String := "bls12381_fp2_dbl_x86_from_lean"
/-- Committed `Fp6` mul driver. -/
def fp6MulSym : String := "bls12381_fp6_mul_x86_from_lean"
/-- Committed `Fp6` mul-by-`v` (`fp6_mul_art`). -/
def fp6ArtSym : String := "bls12381_fp6_mul_art_x86_from_lean"
/-- Committed `Fp6` add driver. -/
def fp6AddSym : String := "bls12381_fp6_add_x86_from_lean"
/-- Committed `Fp6` sub driver. -/
def fp6SubSym : String := "bls12381_fp6_sub_x86_from_lean"
/-- Emitted `Fp6` doubling (this module). -/
def fp6DblSym : String := "bls12381_fp6_dbl_x86_from_lean"

/-! ## 1. `Fp2` / `Fp6` doubling leaves (`z = x + x`)

`Fp2` doubling is two `Fp` adds; `Fp6` doubling is three `Fp2` adds. Frame `8`
keeps `%rsp ≡ 0 mod 16` at the inner calls. The two source pointers passed to
each add are *the same* base (`x = x + x`), so doubling is alias-safe by
construction. -/

/-- `bls12381_fp2_dbl_x86_from_lean(z, x)` = `x + x` over `Fp2`. -/
def fp2DblAsm : String :=
  framedDriver fp2DblSym 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( callTri fpAddSym "%rbx" 0     "%r12" 0     "%r12" 0
    ++ callTri fpAddSym "%rbx" imOff "%r12" imOff "%r12" imOff )

/-- `bls12381_fp6_dbl_x86_from_lean(z, x)` = `x + x` over `Fp6`. -/
def fp6DblAsm : String :=
  framedDriver fp6DblSym 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( callTri fp2AddSym "%rbx" c0 "%r12" c0 "%r12" c0
    ++ callTri fp2AddSym "%rbx" c1 "%r12" c1 "%r12" c1
    ++ callTri fp2AddSym "%rbx" c2 "%r12" c2 "%r12" c2 )

/-! ## 2. `Fp12` Karatsuba square (RELIC `fp12_sqr_basic`)

`Fp12 = Fp6[w]/(w² − v)`; for `x = a₀ + a₁·w`:

    t0 = a₀ + a₁ ; t1 = v·a₁ (fp6_mul_art) ; t1 = a₀ + t1
    t0 = t0·t1 ; r1 = a₀·a₁ ; r0 = t0 − r1 ; t1 = v·r1 (fp6_mul_art) ; r0 = r0 − t1
    r1 = 2·r1 ; z.c₀ = r0 ; z.c₁ = r1

3 `Fp6`-muls (= 162 `Fp`-muls) + 2 `fp6_mul_art` + `Fp6` add/sub/dbl. Output is
computed into scratch `Fp6` felems `r0,r1` then copied to `z`, so `z` may alias
`x`. Scratch: `t0,t1,r0,r1` (288 bytes each) + a zeroed `Fp6` felem `zr` for the
alias-safe copy-out. 5 felems = `1440`; `+8 ⇒ 1448 ≡ 8 mod 16`. -/

def ST0 : Int := 0
def ST1 : Int := 288
def SR0 : Int := 576
def SR1 : Int := 864
def SZR : Int := 1152

/-- `bls12381_fp12_sqr_x86_from_lean(z, x)` over `Fp12 = Fp6[w]/(w²−v)`.
    Composes the committed `Fp6` mul + `fp6_mul_art` + `Fp6` add/sub/dbl; matches
    RELIC `fp12_sqr_basic`. -/
def fp12SqrAsm : String :=
  framedDriver "bls12381_fp12_sqr_x86_from_lean" 1448
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( -- zr = a₀ − a₀  (zeroed Fp6 felem, three Fp2 = six Fp subs)
      callTri fpSubSym "%rbp" (SZR+c0)         "%r12" (w0+c0)         "%r12" (w0+c0)
    ++ callTri fpSubSym "%rbp" (SZR+c0+imOff)  "%r12" (w0+c0+imOff)   "%r12" (w0+c0+imOff)
    ++ callTri fpSubSym "%rbp" (SZR+c1)         "%r12" (w0+c1)         "%r12" (w0+c1)
    ++ callTri fpSubSym "%rbp" (SZR+c1+imOff)  "%r12" (w0+c1+imOff)   "%r12" (w0+c1+imOff)
    ++ callTri fpSubSym "%rbp" (SZR+c2)         "%r12" (w0+c2)         "%r12" (w0+c2)
    ++ callTri fpSubSym "%rbp" (SZR+c2+imOff)  "%r12" (w0+c2+imOff)   "%r12" (w0+c2+imOff)
      -- t0 = a₀ + a₁
    ++ callTri fp6AddSym "%rbp" ST0 "%r12" w0 "%r12" w1
      -- t1 = v·a₁ ; t1 = a₀ + t1
    ++ callBin fp6ArtSym "%rbp" ST1 "%r12" w1
    ++ callTri fp6AddSym "%rbp" ST1 "%r12" w0 "%rbp" ST1
      -- t0 = (a₀+a₁)·(a₀ + v·a₁)
    ++ callTri fp6MulSym "%rbp" ST0 "%rbp" ST0 "%rbp" ST1
      -- r1 = a₀·a₁
    ++ callTri fp6MulSym "%rbp" SR1 "%r12" w0 "%r12" w1
      -- r0 = t0 − r1
    ++ callTri fp6SubSym "%rbp" SR0 "%rbp" ST0 "%rbp" SR1
      -- t1 = v·r1 ; r0 = r0 − t1
    ++ callBin fp6ArtSym "%rbp" ST1 "%rbp" SR1
    ++ callTri fp6SubSym "%rbp" SR0 "%rbp" SR0 "%rbp" ST1
      -- r1 = 2·r1
    ++ callBin fp6DblSym "%rbp" SR1 "%rbp" SR1
      -- copy r0 → z.c₀, r1 → z.c₁  (Fp6 add against zero, alias-safe)
    ++ callTri fp6AddSym "%rbx" w0 "%rbp" SR0 "%rbp" SZR
    ++ callTri fp6AddSym "%rbx" w1 "%rbp" SR1 "%rbp" SZR )

/-! ## 3. `Fp12` cyclotomic square (RELIC `fp12_sqr_cyc_basic`, Granger–Scott)

The hot loop of the final exponentiation. RELIC indexes the `Fp12` element as
`a[i][j]` (`i ∈ {0,1}` the `w`-coordinate, `j ∈ {0,1,2}` the `v`-coordinate),
each an `Fp2`. In the owned byte layout `a[i][j]` sits at offset
`i·288 + j·96` (`w_i + c_j`). The schedule (transcribed verbatim from
`fp12_sqr_cyc_basic`, `Fp2` temporaries `t0..t6`):

    t2 = a00² ; t3 = a11² ; t1 = a00 + a11
    t0 = ξ·t3 ; t0 = t0 + t2
    t1 = t1² ; t1 = t1 − t2 ; t1 = t1 − t3
    c00 = t0 − a00 ; c00 = 2·c00 ; c00 = t0 + c00
    c11 = t1 + a11 ; c11 = 2·c11 ; c11 = t1 + c11
    t0 = a01² ; t1 = a12² ; t5 = a01 + a12 ; t2 = t5²
    t3 = t0 + t1 ; t5 = t2 − t3
    t6 = a10 + a02 ; t3 = t6² ; t2 = a10²
    t6 = ξ·t5 ; t5 = t6 + a10 ; t5 = 2·t5 ; c10 = t5 + t6
    t4 = ξ·t1 ; t5 = t0 + t4 ; t6 = t5 − a02
    t1 = a02² ; t6 = 2·t6 ; c02 = t6 + t5
    t4 = ξ·t1 ; t5 = t2 + t4 ; t6 = t5 − a01 ; t6 = 2·t6 ; c01 = t6 + t5
    t0 = t2 + t1 ; t5 = t3 − t0 ; t6 = t5 + a12 ; t6 = 2·t6 ; c12 = t5 + t6

9 `Fp2`-squarings (= 27 `Fp`-muls) + `Fp2` mul-by-ξ / add / sub / dbl. The six
output `Fp2` coordinates are written into scratch slots first and copied to `z`
last, so `z` may alias `x`. The committed `fp2_sqr` leaf requires `z ≠ x` (it
stages `a+b` into `z.re` before reading `x`), so the lone in-place RELIC
`fp2_sqr(t1,t1)` is routed through a dedicated scratch slot `US`. Scratch: 7
`Fp2` temporaries (`t0..t6`) + 6 result slots + a zeroed `Fp2` for the copy-out
+ the `US` square scratch = 15 `Fp2` felems = `1440`; `+8 ⇒ 1448`. -/

def U0 : Int := 0
def U1 : Int := 96
def U2 : Int := 192
def U3 : Int := 288
def U4 : Int := 384
def U5 : Int := 480
def U6 : Int := 576
def Q00 : Int := 672
def Q11 : Int := 768
def Q10 : Int := 864
def Q02 : Int := 960
def Q01 : Int := 1056
def Q12 : Int := 1152
def QZ  : Int := 1248   -- zeroed Fp2 for copy-out
def US  : Int := 1344   -- scratch for the in-place `fp2_sqr` (non-aliasing leaf)

/-- Byte offset of `a[i][j]` (an `Fp2`) in an owned `Fp12` felem. -/
def aij (i j : Int) : Int := i * 288 + j * 96

/-- `bls12381_fp12_sqr_cyc_x86_from_lean(z, x)` over the cyclotomic subgroup of
    `Fp12*`. Composes the committed `Fp2` sqr / mul-by-ξ / add / sub + the `Fp2`
    dbl emitted here; matches RELIC `fp12_sqr_cyc_basic` (Granger–Scott). Inputs
    must lie in the cyclotomic subgroup (the contract under which RELIC invokes
    this in `pp_exp_k12`). -/
def fp12SqrCycAsm : String :=
  framedDriver "bls12381_fp12_sqr_cyc_x86_from_lean" 1448
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( -- QZ = a00 − a00 (zeroed Fp2)
      callTri fpSubSym "%rbp" QZ          "%r12" (aij 0 0)         "%r12" (aij 0 0)
    ++ callTri fpSubSym "%rbp" (QZ+imOff)  "%r12" (aij 0 0 + imOff) "%r12" (aij 0 0 + imOff)
      -- t2 = a00² ; t3 = a11² ; t1 = a00 + a11
    ++ callBin fp2SqrSym "%rbp" U2 "%r12" (aij 0 0)
    ++ callBin fp2SqrSym "%rbp" U3 "%r12" (aij 1 1)
    ++ callTri fp2AddSym "%rbp" U1 "%r12" (aij 0 0) "%r12" (aij 1 1)
      -- t0 = ξ·t3 ; t0 = t0 + t2
    ++ callBin fp2NorSym "%rbp" U0 "%rbp" U3
    ++ callTri fp2AddSym "%rbp" U0 "%rbp" U0 "%rbp" U2
      -- t1 = t1² ; t1 = t1 − t2 ; t1 = t1 − t3
      -- (fp2_sqr requires z ≠ x: square into US, then read US)
    ++ callBin fp2SqrSym "%rbp" US "%rbp" U1
    ++ callTri fp2SubSym "%rbp" U1 "%rbp" US "%rbp" U2
    ++ callTri fp2SubSym "%rbp" U1 "%rbp" U1 "%rbp" U3
      -- c00 = t0 − a00 ; c00 = 2·c00 ; c00 = t0 + c00
    ++ callTri fp2SubSym "%rbp" Q00 "%rbp" U0 "%r12" (aij 0 0)
    ++ callBin fp2DblSym "%rbp" Q00 "%rbp" Q00
    ++ callTri fp2AddSym "%rbp" Q00 "%rbp" U0 "%rbp" Q00
      -- c11 = t1 + a11 ; c11 = 2·c11 ; c11 = t1 + c11
    ++ callTri fp2AddSym "%rbp" Q11 "%rbp" U1 "%r12" (aij 1 1)
    ++ callBin fp2DblSym "%rbp" Q11 "%rbp" Q11
    ++ callTri fp2AddSym "%rbp" Q11 "%rbp" U1 "%rbp" Q11
      -- t0 = a01² ; t1 = a12² ; t5 = a01 + a12 ; t2 = t5²
    ++ callBin fp2SqrSym "%rbp" U0 "%r12" (aij 0 1)
    ++ callBin fp2SqrSym "%rbp" U1 "%r12" (aij 1 2)
    ++ callTri fp2AddSym "%rbp" U5 "%r12" (aij 0 1) "%r12" (aij 1 2)
    ++ callBin fp2SqrSym "%rbp" U2 "%rbp" U5
      -- t3 = t0 + t1 ; t5 = t2 − t3
    ++ callTri fp2AddSym "%rbp" U3 "%rbp" U0 "%rbp" U1
    ++ callTri fp2SubSym "%rbp" U5 "%rbp" U2 "%rbp" U3
      -- t6 = a10 + a02 ; t3 = t6² ; t2 = a10²
    ++ callTri fp2AddSym "%rbp" U6 "%r12" (aij 1 0) "%r12" (aij 0 2)
    ++ callBin fp2SqrSym "%rbp" U3 "%rbp" U6
    ++ callBin fp2SqrSym "%rbp" U2 "%r12" (aij 1 0)
      -- t6 = ξ·t5 ; t5 = t6 + a10 ; t5 = 2·t5 ; c10 = t5 + t6
    ++ callBin fp2NorSym "%rbp" U6 "%rbp" U5
    ++ callTri fp2AddSym "%rbp" U5 "%rbp" U6 "%r12" (aij 1 0)
    ++ callBin fp2DblSym "%rbp" U5 "%rbp" U5
    ++ callTri fp2AddSym "%rbp" Q10 "%rbp" U5 "%rbp" U6
      -- t4 = ξ·t1 ; t5 = t0 + t4 ; t6 = t5 − a02
    ++ callBin fp2NorSym "%rbp" U4 "%rbp" U1
    ++ callTri fp2AddSym "%rbp" U5 "%rbp" U0 "%rbp" U4
    ++ callTri fp2SubSym "%rbp" U6 "%rbp" U5 "%r12" (aij 0 2)
      -- t1 = a02² ; t6 = 2·t6 ; c02 = t6 + t5
    ++ callBin fp2SqrSym "%rbp" U1 "%r12" (aij 0 2)
    ++ callBin fp2DblSym "%rbp" U6 "%rbp" U6
    ++ callTri fp2AddSym "%rbp" Q02 "%rbp" U6 "%rbp" U5
      -- t4 = ξ·t1 ; t5 = t2 + t4 ; t6 = t5 − a01 ; t6 = 2·t6 ; c01 = t6 + t5
    ++ callBin fp2NorSym "%rbp" U4 "%rbp" U1
    ++ callTri fp2AddSym "%rbp" U5 "%rbp" U2 "%rbp" U4
    ++ callTri fp2SubSym "%rbp" U6 "%rbp" U5 "%r12" (aij 0 1)
    ++ callBin fp2DblSym "%rbp" U6 "%rbp" U6
    ++ callTri fp2AddSym "%rbp" Q01 "%rbp" U6 "%rbp" U5
      -- t0 = t2 + t1 ; t5 = t3 − t0 ; t6 = t5 + a12 ; t6 = 2·t6 ; c12 = t5 + t6
    ++ callTri fp2AddSym "%rbp" U0 "%rbp" U2 "%rbp" U1
    ++ callTri fp2SubSym "%rbp" U5 "%rbp" U3 "%rbp" U0
    ++ callTri fp2AddSym "%rbp" U6 "%rbp" U5 "%r12" (aij 1 2)
    ++ callBin fp2DblSym "%rbp" U6 "%rbp" U6
    ++ callTri fp2AddSym "%rbp" Q12 "%rbp" U5 "%rbp" U6
      -- copy the six result Fp2 slots → z (Fp2 add against zero, alias-safe)
    ++ callTri fp2AddSym "%rbx" (aij 0 0) "%rbp" Q00 "%rbp" QZ
    ++ callTri fp2AddSym "%rbx" (aij 0 1) "%rbp" Q01 "%rbp" QZ
    ++ callTri fp2AddSym "%rbx" (aij 0 2) "%rbp" Q02 "%rbp" QZ
    ++ callTri fp2AddSym "%rbx" (aij 1 0) "%rbp" Q10 "%rbp" QZ
    ++ callTri fp2AddSym "%rbx" (aij 1 1) "%rbp" Q11 "%rbp" QZ
    ++ callTri fp2AddSym "%rbx" (aij 1 2) "%rbp" Q12 "%rbp" QZ )

/-! ## 4. In-Lean value pin (faithful leaf-call model vs Granger–Scott reference, #602/#219)

`native_decide`/`lean_diagnostic` can witness the *shape* of the emitted asm but
not its computed *value*; a wrong scratch slot or a leaf-aliasing violation in
the schedule elaborates clean yet computes the wrong field element (exactly the
class of bug the external GMP/RELIC KAT caught). To surface such bugs in-Lean we
re-run the **same call schedule** `fp12SqrCycAsm` emits — at the granularity of
the committed `Fp`/`Fp2` leaves, with their exact staged byte-level write order
— over a tiny prime field `𝔽ₚ`, and pin the result against the Granger–Scott
cyclotomic-square formula evaluated directly on the `Fp2` coordinates.

Crucially the model reproduces the committed `bls12381_fp2_sqr` leaf's *staged*
semantics (`z.re ← a+b` is written **before** `x` is read again), so it requires
`z ≠ x`: an in-place `fp2_sqr(t,t)` corrupts `x`. That is the precise hazard the
`US` scratch slot in `fp12SqrCycAsm` avoids; the pin would fail if the in-place
form were restored. `mont_mul` is modelled as `𝔽ₚ`-multiplication (the
Montgomery factor is a field automorphism that cancels in a value-equality
check). Memory is an `Array Int` keyed by *word slot* (one cell per `Fp`
coordinate; an `Fp2` at base `b` is `re = b`, `im = b+1`) — abstract slot ids,
not byte addresses (the byte offsets `U*/Q*/US/aij` are checked separately by
the shape theorems and cross-validated against the C harness layout). The array
form keeps `native_decide` cheap (no nested-closure tower). -/

namespace CycModel

/-- Small prime for the in-Lean value pin. -/
def pp : Int := 1000003
/-- Reduce into `[0, pp)`. -/
def md (x : Int) : Int := ((x % pp) + pp) % pp

/-- Model memory: word slot → `𝔽_pp` residue (one cell per `Fp`). -/
abbrev Mem := Array Int
def NCELL : Nat := 200
def rd (m : Mem) (o : Nat) : Int := m.getD o 0
def wr (m : Mem) (o : Nat) (v : Int) : Mem := m.set! o (md v)
def fpAddM (m : Mem) (z x y : Nat) : Mem := wr m z (rd m x + rd m y)
def fpSubM (m : Mem) (z x y : Nat) : Mem := wr m z (rd m x - rd m y)
def fpMulM (m : Mem) (z x y : Nat) : Mem := wr m z (rd m x * rd m y)

/-- `Fp2` at word-slot base `b`: `re = b`, `im = b + 1`. -/
def fp2AddM (m : Mem) (z x y : Nat) : Mem := fpAddM (fpAddM m z x y) (z+1) (x+1) (y+1)
def fp2SubM (m : Mem) (z x y : Nat) : Mem := fpSubM (fpSubM m z x y) (z+1) (x+1) (y+1)
def fp2DblM (m : Mem) (z x : Nat) : Mem := fpAddM (fpAddM m z x x) (z+1) (x+1) (x+1)
/-- `fp2_mul_nor` ξ=(1+u): `z.im ← x.re+x.im` then `z.re ← x.re−x.im` (driver order). -/
def fp2NorM (m : Mem) (z x : Nat) : Mem := fpSubM (fpAddM m (z+1) x (x+1)) z x (x+1)
/-- Leaf-private scratch of `bls12381_fp2_sqr` (own frame; distinct slots). -/
def SV1 : Nat := 180
def SV2 : Nat := 182
/-- Faithful `bls12381_fp2_sqr` staged semantics: `z.re ← a+b` written before the
    second read of `x`, so **requires `z ≠ x`**. -/
def fp2SqrM (m : Mem) (z x : Nat) : Mem :=
  let m := fpAddM m z x (x+1)
  let m := fpSubM m SV1 x (x+1)
  let m := fpMulM m z z SV1
  let m := fpMulM m SV2 x (x+1)
  fpAddM m (z+1) SV2 SV2

/-- Scratch `Fp2` slot bases mirroring the driver's `U*/Q*/US` (step 2 cells). -/
def mU0:Nat:=12
def mU1:Nat:=14
def mU2:Nat:=16
def mU3:Nat:=18
def mU4:Nat:=20
def mU5:Nat:=22
def mU6:Nat:=24
def mQ00:Nat:=26
def mQ11:Nat:=28
def mQ10:Nat:=30
def mQ02:Nat:=32
def mQ01:Nat:=34
def mQ12:Nat:=36
def mUS:Nat:=38
/-- Input `a[i][j]` word-slot base. -/
def mA (i j : Nat) : Nat := 2*(3*i+j)

/-- Run the exact `fp12SqrCycAsm` schedule (model slots = driver slots). When
    `inPlace = true`, the lone `fp2_sqr(t1,t1)` is left in place (the original
    broken form) so the pin can witness the bug; `false` uses the `US` scratch. -/
def runCyc (inPlace : Bool) (m0 : Mem) : Mem := Id.run do
  let mut m := m0
  m := fp2SqrM m mU2 (mA 0 0); m := fp2SqrM m mU3 (mA 1 1); m := fp2AddM m mU1 (mA 0 0) (mA 1 1)
  m := fp2NorM m mU0 mU3; m := fp2AddM m mU0 mU0 mU2
  let sqrDst := if inPlace then mU1 else mUS
  m := fp2SqrM m sqrDst mU1
  m := fp2SubM m mU1 sqrDst mU2
  m := fp2SubM m mU1 mU1 mU3
  m := fp2SubM m mQ00 mU0 (mA 0 0); m := fp2DblM m mQ00 mQ00; m := fp2AddM m mQ00 mU0 mQ00
  m := fp2AddM m mQ11 mU1 (mA 1 1); m := fp2DblM m mQ11 mQ11; m := fp2AddM m mQ11 mU1 mQ11
  m := fp2SqrM m mU0 (mA 0 1); m := fp2SqrM m mU1 (mA 1 2); m := fp2AddM m mU5 (mA 0 1) (mA 1 2); m := fp2SqrM m mU2 mU5
  m := fp2AddM m mU3 mU0 mU1; m := fp2SubM m mU5 mU2 mU3
  m := fp2AddM m mU6 (mA 1 0) (mA 0 2); m := fp2SqrM m mU3 mU6; m := fp2SqrM m mU2 (mA 1 0)
  m := fp2NorM m mU6 mU5; m := fp2AddM m mU5 mU6 (mA 1 0); m := fp2DblM m mU5 mU5; m := fp2AddM m mQ10 mU5 mU6
  m := fp2NorM m mU4 mU1; m := fp2AddM m mU5 mU0 mU4; m := fp2SubM m mU6 mU5 (mA 0 2)
  m := fp2SqrM m mU1 (mA 0 2); m := fp2DblM m mU6 mU6; m := fp2AddM m mQ02 mU6 mU5
  m := fp2NorM m mU4 mU1; m := fp2AddM m mU5 mU2 mU4; m := fp2SubM m mU6 mU5 (mA 0 1); m := fp2DblM m mU6 mU6; m := fp2AddM m mQ01 mU6 mU5
  m := fp2AddM m mU0 mU2 mU1; m := fp2SubM m mU5 mU3 mU0; m := fp2AddM m mU6 mU5 (mA 1 2); m := fp2DblM m mU6 mU6; m := fp2AddM m mQ12 mU5 mU6
  return m

/-- Granger–Scott reference, evaluated directly on `Fp2 = 𝔽ₚ[u]/(u²+1)` coords. -/
abbrev F2 := Int × Int
def a2 (x y : F2) : F2 := (md (x.1+y.1), md (x.2+y.2))
def s2' (x y : F2) : F2 := (md (x.1-y.1), md (x.2-y.2))
def m2 (x y : F2) : F2 := (md (x.1*y.1 - x.2*y.2), md (x.1*y.2 + x.2*y.1))
def sq2 (x : F2) : F2 := m2 x x
def nor2 (x : F2) : F2 := (md (x.1 - x.2), md (x.1 + x.2))
def d2 (x : F2) : F2 := a2 x x
def gsRef (a00 a01 a02 a10 a11 a12 : F2) : F2 × F2 × F2 × F2 × F2 × F2 :=
  let t2 := sq2 a00; let t3 := sq2 a11; let t1 := a2 a00 a11
  let t0 := a2 (nor2 t3) t2; let t1b := s2' (s2' (sq2 t1) t2) t3
  let c00 := (let c := s2' t0 a00; a2 t0 (d2 c)); let c11 := (let c := a2 t1b a11; a2 t1b (d2 c))
  let s0 := sq2 a01; let s1 := sq2 a12; let s5b := s2' (sq2 (a2 a01 a12)) (a2 s0 s1)
  let r3 := sq2 (a2 a10 a02); let r2 := sq2 a10
  let n6 := nor2 s5b; let c10 := a2 (d2 (a2 n6 a10)) n6
  let w5 := a2 s0 (nor2 s1); let c02 := a2 (d2 (s2' w5 a02)) w5
  let q1 := sq2 a02; let w5b := a2 r2 (nor2 q1); let c01 := a2 (d2 (s2' w5b a01)) w5b
  let z5 := s2' r3 (a2 r2 q1); let c12 := a2 z5 (d2 (a2 z5 a12))
  (c00, c01, c02, c10, c11, c12)

/-- A concrete test element (six `Fp2` coords with small, distinct entries). -/
def mkMem : Mem := Id.run do
  let mut m : Mem := Array.replicate NCELL 0
  let vals : List (Nat × Int) :=
    [ (mA 0 0, 3), (mA 0 0 + 1, 5), (mA 0 1, 7), (mA 0 1 + 1, 11)
    , (mA 0 2, 13), (mA 0 2 + 1, 17), (mA 1 0, 19), (mA 1 0 + 1, 23)
    , (mA 1 1, 29), (mA 1 1 + 1, 31), (mA 1 2, 37), (mA 1 2 + 1, 41) ]
  for (o, v) in vals do m := m.set! o v
  return m
def coordM (m : Mem) (o : Nat) : F2 := (rd m o, rd m (o+1))
def refVal := gsRef (3,5) (7,11) (13,17) (19,23) (29,31) (37,41)

/-- The schedule's six result slots match the GS reference (`inPlace` selects the
    fixed `US`-scratch form when `false`, the broken in-place form when `true`). -/
def cycMatches (inPlace : Bool) : Bool :=
  let m := runCyc inPlace mkMem
  (coordM m mQ00 == refVal.1) && (coordM m mQ01 == refVal.2.1) && (coordM m mQ02 == refVal.2.2.1)
   && (coordM m mQ10 == refVal.2.2.2.1) && (coordM m mQ11 == refVal.2.2.2.2.1)
   && (coordM m mQ12 == refVal.2.2.2.2.2)

end CycModel

/-- **Value pin**: the cyclotomic-square schedule that `fp12SqrCycAsm` emits
    computes the Granger–Scott square on a concrete `Fp12` element, and the
    in-place-`fp2_sqr` variant does **not** (witnessing both the bug and its
    fix, since `bls12381_fp2_sqr` requires `z ≠ x`). -/
theorem fp12SqrCyc_value_pin :
    CycModel.cycMatches false = true ∧ CycModel.cycMatches true = false := by
  native_decide

/-! ## 5. Shape checks (real tower call graph, not a stub) -/

/-- **The owned `Fp12` square carries two real `Fp6`-multiply calls** (= 108
    `Fp`-muls), the RELIC `fp12_sqr_basic` Karatsuba graph (`t0·t1` and
    `a₀·a₁`), plus two `fp6_mul_art` (mul-by-`v`) and the `Fp6` add/sub/dbl. -/
theorem fp12SqrAsm_two_real_fp6muls :
    countSub fp12SqrAsm "callq bls12381_fp6_mul_x86_from_lean" = 2
      ∧ countSub fp12SqrAsm "callq bls12381_fp6_mul_art_x86_from_lean" = 2
      ∧ hasSub fp12SqrAsm "callq bls12381_fp6_dbl_x86_from_lean"
      ∧ hasSub fp12SqrAsm "callq bls12381_fp6_add_x86_from_lean"
      ∧ hasSub fp12SqrAsm "callq bls12381_fp6_sub_x86_from_lean" := by native_decide

/-- **The owned cyclotomic `Fp12` square carries nine real `Fp2`-squarings**
    (= 27 `Fp`-muls) — the Granger–Scott `fp12_sqr_cyc_basic` graph,
    cheaper than a generic `Fp12` square (which would need 3 `Fp6`-muls) — plus
    the `Fp2` mul-by-ξ / add / sub / dbl. No `Fp6`-mul appears. -/
theorem fp12SqrCycAsm_nine_real_fp2sqrs :
    countSub fp12SqrCycAsm "callq bls12381_fp2_sqr_x86_from_lean" = 9
      ∧ countSub fp12SqrCycAsm "callq bls12381_fp6_mul_x86_from_lean" = 0
      ∧ hasSub fp12SqrCycAsm "callq bls12381_fp2_mul_nor_x86_from_lean"
      ∧ hasSub fp12SqrCycAsm "callq bls12381_fp2_dbl_x86_from_lean" := by native_decide

/-- The `Fp6` doubling leaf is three `Fp2` adds; the `Fp2` doubling leaf is two
    `Fp` adds (`z = x + x`). -/
theorem dbl_shapes :
    countSub fp6DblAsm "callq bls12381_fp2_add_x86_from_lean" = 3
      ∧ countSub fp2DblAsm "callq bls12381_fp_add_x86_from_lean" = 2 := by native_decide

/-! ## 6. Emit driver -/

/-- Emit the owned `Fp2`/`Fp6` doubling leaves + `Fp12` square + cyclotomic
    `Fp12` square `.s` for the bench harness. The committed lower-tier leaves are
    referenced read-only by the harness and are **not** re-emitted here. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_pairing_compare/gen_com"
  let g := "bench/bls12381_pairing_compare/gen_com/"
  IO.FS.writeFile (g ++ "bls12381_fp2_dbl_x86_from_lean.s")      fp2DblAsm
  IO.FS.writeFile (g ++ "bls12381_fp6_dbl_x86_from_lean.s")      fp6DblAsm
  IO.FS.writeFile (g ++ "bls12381_fp12_sqr_x86_from_lean.s")     fp12SqrAsm
  IO.FS.writeFile (g ++ "bls12381_fp12_sqr_cyc_x86_from_lean.s") fp12SqrCycAsm
  IO.println "wrote gen_com/bls12381_fp2_dbl + fp6_dbl + fp12_sqr + fp12_sqr_cyc .s (owned x86 backend, pairing-tower squaring layer over the committed Fp6/Fp12 mul)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Pairing
