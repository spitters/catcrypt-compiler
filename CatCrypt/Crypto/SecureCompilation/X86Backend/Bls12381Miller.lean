/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381G2
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381G2
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel

/-!
# BLS12-381 Miller loop, owned x86 backend (toward `pp_map`)

**Variant: RELIC-transcribed (tests-only correctness).**

**STRING-TEMPLATED — not verified-compiler output:** the emitted
`bls12381_*_x86_from_lean.s` is assembled as literal asm-line text
(`framedDriver`/`renderLeafFn` join `movq`/`leaq`/`call` string literals), with
no `Com`/`Lprog` IR and no verified printer, so no theorem relates the emitted
bytes to a source; the byte-identity to RELIC below is the only corroboration.
See `bench/framework/AUDIT_EMIT_BYPASS.md` and `EMIT_PROVENANCE.md`
§"Which emit is verified?".

This owned x86 emit is
hand-transcribed from the RELIC pairing reference and gated **byte-identical to
RELIC**. RELIC is unverified C, so that byte-identity is a **test**, not a
correctness proof. The verified-correctness BLS variant — owned emit whose
denotation is tied to the **AUCurves** Rocq-proved pairing via the rocqlean
axiom bridge — is a **separate** artifact, kept distinct from this one so the
RELIC-transcribed and AUCurves-generated variants can be compared.

The pairing layer **above** the committed pieces:

* `Fp2`     leaf — `Bls12381Fp2MulKernel` (commit 52dc486f).
* `Fp6/Fp12` mul  — `Bls12381Fp6Fp12MulKernel` (commit e8006039).
* `G2` group law  — `Bls12381G2` (commit 1d66735d, `bls12381_g2_add/dbl`).

This module emits the **Miller-loop** drivers, all composing those owned leaves:

* `bls12381_fp12_mul_dxs` — the **sparse line × dense `Fp12`** accumulation step
  (`r = r · l`, the per-bit Miller multiply).
* `bls12381_pp_dbl_k12` — `G2` doubling **with line evaluation** (the dominant
  per-bit step) producing the sparse line `l`.
* `bls12381_pp_add_k12` — `G2` addition with line evaluation.
* `bls12381_pp_mil_k12` — the NAF Miller driver accumulating `f`.

## Curve-config lock (matches the *installed* RELIC BLS12-381)

The sparse-line layout is **config-locked** to the twist convention and the
`EP_ADD`/coordinate system. The installed RELIC BLS12-381 (`ep_param.c`
`B12_P381`) fixes:

* **M-type sextic twist** (`type = RLC_EP_MTYPE`) — so RELIC's line code runs
  with `one ^= 1; zero ^= 1`, i.e. `one = 0, zero = 1`.
* curve `b = 4` (`B12_P381_B = "4"`), so `ep_curve_opt_b() != RLC_TWO`; the
  Miller doubling takes the **general-`b` else branch** of
  `pp_dbl_k12_projc` (`relic_pp_dbl_k12.c`).
* `EP_ADD = PROJC`, `FPX_RDC = LAZYR`, `PP_EXT = LAZYR`. The lazy-reduction
  variants compute the **same reduced field values** as the basic schedules
  (lazy reduction merely defers the `mod p`); the owned drivers realise the
  mathematically-equivalent basic schedule and are KAT'd byte-identical to the
  installed RELIC `pp_dbl_k12` / `pp_add_k12` / `fp12_mul_dxs`.

### The sparse line `l` (M-type, `one=0, zero=1`)

`pp_dbl_k12_projc` (general-`b` else branch) writes exactly three `Fp2`
components of the dodecic `l`:

* `l[one][one]   = l[0][0] = D − B`           (`D = 3b·C`, an `Fp2`);
* `l[one][zero]  = l[0][1] = xₚ · A`          (`A = x₁²`, scaled by the `G1`
  affine `Fp` scalar `xₚ`, per `Fp2` component);
* `l[zero][zero] = l[1][1] = F · yₚ`          (`F`, scaled by the `Fp` scalar
  `yₚ`).

In the owned packed `Fp12` layout (`l[i][j]` at byte offset `i·288 + j·96`)
those are `l00 = 0`, `l01 = 96`, `l11 = 384`; the other three `Fp2` slots
(`l02 = 192`, `l10 = 288`, `l12 = 480`) are **zero**. This is exactly the
sparse pattern the M-type `fp12_mul_dxs` reads (`relic_fp12_mul.c`,
`else`/`PROJC` branch reads `b[0][0]`, `b[0][1]`, `b[1][1]`).

`pp_add_k12_projc` writes the same three slots: `l[one][zero]=-A·xₚ → l01`,
`l[one][one]=J → l00`, `l[zero][zero]=B·yₚ → l11` (the M-type `one=0, zero=1`
swap sends `J` to `l00` and `B·yₚ` to `l11`).

## Scope

Same trust boundary as the committed tower: the `Fp` add/sub/mul leaves are the
verified word kernels; everything emitted here is a **trusted SysV-ABI driver**
sequencing `call`s over a caller-owned `%rbp` frame. Value correctness is the
external KAT (`bench/bls12381_miller_compare`) against the installed RELIC
`fp12_mul_dxs` / `pp_dbl_k12` / `pp_add_k12` / `pp_mil_k12` and a GMP oracle
running the identical M-type schedules over canonical integers.

The Miller loop is **not** `pp_map`: the final exponentiation (`Fp12`
cyclotomic via Frobenius + the BLS hard-part addition chain, building on the
in-flight `fp12_sqr_cyc`) is the remaining layer and is documented as the
residual, not claimed here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Miller

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel (callFp)

/-! ## 0. Owned-leaf symbol names (committed / lower-tier) -/

def fpMul  : String := "bls12381_mont_mul_x86_from_lean"
def fpAdd  : String := "bls12381_fp_add_x86_from_lean"
def fpSub  : String := "bls12381_fp_sub_x86_from_lean"
def fp2Mul : String := "bls12381_fp2_mul_x86_from_lean"
def fp2Sqr : String := "bls12381_fp2_sqr_x86_from_lean"
def fp2Add : String := "bls12381_fp2_add_x86_from_lean"
def fp2Sub : String := "bls12381_fp2_sub_x86_from_lean"
def fp2Nor : String := "bls12381_fp2_mul_nor_x86_from_lean"
def fp2Dbl : String := "bls12381_fp2_dbl_x86_from_lean"
def fp2Copy : String := "bls12381_fp2_copy_x86_from_lean"
def fp6Mul : String := "bls12381_fp6_mul_x86_from_lean"
def fp6Art : String := "bls12381_fp6_mul_art_x86_from_lean"
def fp6Add : String := "bls12381_fp6_add_x86_from_lean"
def fp6Sub : String := "bls12381_fp6_sub_x86_from_lean"
def fp12Mul : String := "bls12381_fp12_mul_x86_from_lean"

/-! ## 1. Byte-offset layout

`Fp = 48`, `Fp2 = 96` (`re=0, im=48`), `Fp6 = 288` (`a₀=0,a₁=96,a₂=192`),
`Fp12 = 576` (`c₀=0,c₁=288`). A dodecic component `l[i][j]` sits at
`i·288 + j·96`. A `G2` point `ep2_st` is `[X:Y:Z]` at `X=0, Y=96, Z=192`
(packed 36×u64), matching the committed `Bls12381G2` driver layout. -/

def imOff : Int := 48
/-- `Fp2` byte size. -/
def f2B : Int := 96
/-- dodecic component offset `l[i][j]`. -/
def lij (i j : Int) : Int := i * 288 + j * 96
/-- packed `G2` coordinate offsets. -/
def oX : Int := 0
def oY : Int := 96
def oZ : Int := 192

/-! ## 2. ABI helpers -/

def lea (off : Int) (base argreg : String) : String :=
  "\tleaq " ++ toString off ++ "(" ++ base ++ "), " ++ argreg

/-- 3-pointer SysV call `leaf(z, x, y)`. -/
def c3 (leaf : String) (zb : String) (zo : Int)
    (xb : String) (xo : Int) (yb : String) (yo : Int) : List String :=
  callFp leaf zb zo xb xo yb yo

/-- 2-pointer SysV call `leaf(z, x)`. -/
def c2 (leaf : String) (zb : String) (zo : Int) (xb : String) (xo : Int) : List String :=
  [ lea zo zb "%rdi", lea xo xb "%rsi", "\tcallq " ++ leaf ]

/-- Framed driver: 6 callee-saved pushes + `subq frame` + `movq %rsp,%rbp`.
    `frame ≡ 8 (mod 16)` keeps inner `callq` 16-aligned. -/
def framedDriver (name : String) (frame : Int) (saveMoves body : List String) : String :=
  renderLeafFn name
    ([ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
     , "\tpushq %rbp"
     , "\tsubq $" ++ toString frame ++ ", %rsp", "\tmovq %rsp, %rbp" ] ++ saveMoves)
    body
    [ "\taddq $" ++ toString frame ++ ", %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- **Non-aliasing `Fp2` multiply** `z = x·y` via the dedicated scratch felem
    `sc` (the committed `fp2_mul` driver requires the output not alias inputs;
    it stages `a+b`/`c+d` into the output halves). Always alias-safe. -/
def m2 (F : String) (sc : Int) (zb : String) (zo : Int)
    (xb : String) (xo : Int) (yb : String) (yo : Int) : List String :=
  c3 fp2Mul F sc xb xo yb yo ++ c2 fp2Copy zb zo F sc

/-! ## 3. Owned line-eval leaves emitted here

`fp_neg(z, x)`: `z = 0 − x`. Realised as `Fp` sub of `x` from a zero `Fp`
felem held in the frame. `fpScale2(z, x, s)`: scale the `Fp2` `x` by the `Fp`
scalar `s` (per component, two `Fp` muls) — the line code's `xp·A`, `F·yp`,
`-xp·A`, `B·yp`. -/

/-- `bls12381_fp_neg_x86_from_lean(z, x)`: `z = 0 − x` over `Fp`. Frame holds a
    zero `Fp` felem (built as `x − x`). -/
def fpNegAsm : String :=
  framedDriver "bls12381_fp_neg_x86_from_lean" 56
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( c3 fpSub "%rbp" 0 "%r12" 0 "%r12" 0      -- zero = x − x
    ++ c3 fpSub "%rbx" 0 "%rbp" 0 "%r12" 0 )   -- z = 0 − x

/-- `bls12381_fp2_scale_x86_from_lean(z, x, s)`: `z = s·x` where `x` is an
    `Fp2` and `s` points at an `Fp` scalar. `z.re = s·x.re`, `z.im = s·x.im`
    (two `Fp` muls) — the per-`Fp2`-component scalar scaling RELIC's
    `fp_mul(l[..][0], s, x[0]); fp_mul(l[..][1], s, x[1])` does. -/
def fp2ScaleAsm : String :=
  framedDriver "bls12381_fp2_scale_x86_from_lean" 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( c3 fpMul "%rbx" 0     "%r12" 0     "%r13" 0     -- z.re = x.re · s
    ++ c3 fpMul "%rbx" imOff "%r12" imOff "%r13" 0 )  -- z.im = x.im · s

/-! ## 4. `ep2_curve_mul_b` (M-type, b = 4)

For the M-type twist, `ep2_curve_mul_b(c, a) = (1+u)·(4·a)` — i.e. scale the
`Fp2` `a` by the prime-field constant `b = 4` componentwise, then multiply by
the non-residue `ξ = (1+u)` (`fp2_mul_nor`). `4·a` is two `Fp2` doublings.
Requires `c ≠ a` (the `fp2_mul_nor` leaf's non-aliasing contract): we double
into the scratch then `nor` into `c`. -/

/-- `bls12381_ep2_mul_b_x86_from_lean(c, a)`: `c = (1+u)·(4·a)`, the M-type
    `ep2_curve_mul_b`. Frame holds one `Fp2` scratch (`4·a`). `96 + 8 ⇒ 104`. -/
def ep2MulBAsm : String :=
  framedDriver "bls12381_ep2_mul_b_x86_from_lean" 104
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( c2 fp2Dbl "%rbp" 0 "%r12" 0       -- s = 2·a
    ++ c2 fp2Dbl "%rbp" 0 "%rbp" 0      -- s = 4·a
    ++ c2 fp2Nor "%rbx" 0 "%rbp" 0 )    -- c = ξ·(4·a)

/-! ## 5. `fp12_mul_dxs` — sparse line × dense `Fp12` (M-type, PROJC)

The Miller accumulation `r = r · l`. `a = r` is a **dense** `Fp12`; `b = l` is
the **sparse** line with nonzero `Fp2` components `l[0][0]` (=`b[0][0]`),
`l[0][1]` (=`b[0][1]`), `l[1][1]` (=`b[1][1]`); `l[0][2]=l[1][0]=l[1][2]=0`.
We realise the *mathematically-equivalent* full schedule, but skip the products
that are structurally zero — matching RELIC `fp12_mul_dxs` (else/PROJC branch)
value-for-value.

Write `a = (a₀ + a₁·w)` with `a₀,a₁ ∈ Fp6 = (·₀,·₁,·₂)` over `Fp2[v]`, and the
sparse `b = (b₀ + b₁·w)` with `b₀ = (l00, l01, 0)`, `b₁ = (0, l11, 0)`. Then,
following the RELIC schedule (`fp6_mul_dxs` on the `b₀`-half, the
`fp2_mul_nor`-folded products on the `b₁`-half):

    t0 = a₀ ·dxs b₀      -- sparse fp6 mul (b₀ has only ·₀,·₁ nonzero)
    t1 = a₁ ·dxs b₁ "art-folded"  -- b₁ = (0,l11,0): t1₀ = ξ·(a₁₂·l11),
                                       t1₁ = a₁₀·l11, t1₂ = a₁₁·l11
    t2₀ = b₀₀ = l00 ; t2₁ = b₀₁ + b₁₁ = l01 + l11 ; t2₂ = 0
    c₁ = (a₀ + a₁) ·dxs t2 ; c₁ -= t0 ; c₁ -= t1
    c₀ = t0 + v·t1            -- fp6_mul_art on t1, then fp6 add

### `fp6 ·dxs` with a `(·₀, ·₁, 0)` sparse operand (RELIC `fp6_mul_dxs`)

For `b = (b0, b1, 0)`:
    v0 = a0·b0 ; v1 = a1·b1
    c0 = v0 + ξ·(a2·b1)
    c1 = (a0+a1)(b0+b1) − v0 − v1
    c2 = a2·b0 + v1
(6 → here 5 `Fp2`-muls since `b2 = 0` kills the `a·b2` products.)
-/

/- frame felems for `fp6_mul_dxs(z = dense fp6, x = dense fp6, y = (y0,y1,0))`.
   Local scratch `Fp2` slots. -/
namespace Dxs6
def V0 : Int := 0
def V1 : Int := 96
def S0 : Int := 192   -- a0+a1
def S1 : Int := 288   -- b0+b1
def T  : Int := 384   -- products / temporaries
def R0 : Int := 480
def R1 : Int := 576
def R2 : Int := 672
def SC : Int := 768   -- non-aliasing fp2_mul scratch
end Dxs6

/-- `bls12381_fp6_mul_dxs_x86_from_lean(z, x, y)`: `z = x · y` over `Fp6`, with
    `y = (y₀, y₁, 0)` sparse (`y₂` is structurally zero, not read). Matches
    RELIC `fp6_mul_dxs` (`d`-shape with two nonzero `Fp2`). 4 generic `Fp2`-mul
    + 1 `fp2_mul_nor`. Frame = 9 `Fp2` = 864; `+8 ⇒ 872`. -/
def fp6MulDxsAsm : String :=
  let F := "%rbp"; let X := "%r12"; let Y := "%r13"; let Z := "%rbx"
  open Dxs6 in
  framedDriver "bls12381_fp6_mul_dxs_x86_from_lean" 872
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( -- v0 = a0·b0 ; v1 = a1·b1
      m2 F SC F V0 X 0   Y 0
    ++ m2 F SC F V1 X 96  Y 96
      -- c0 = v0 + ξ·(a2·b1)
    ++ m2 F SC F T  X 192 Y 96
    ++ c2 fp2Nor F R0 F T
    ++ c3 fp2Add F R0 F R0 F V0
      -- c1 = (a0+a1)(b0+b1) − v0 − v1
    ++ c3 fp2Add F S0 X 0  X 96
    ++ c3 fp2Add F S1 Y 0  Y 96
    ++ m2 F SC F R1 F S0 F S1
    ++ c3 fp2Sub F R1 F R1 F V0
    ++ c3 fp2Sub F R1 F R1 F V1
      -- c2 = a2·b0 + v1
    ++ m2 F SC F T  X 192 Y 0
    ++ c3 fp2Add F R2 F T  F V1
      -- copy r0,r1,r2 → z
    ++ c2 fp2Copy Z 0   F R0
    ++ c2 fp2Copy Z 96  F R1
    ++ c2 fp2Copy Z 192 F R2 )

/- frame felems for the dodecic sparse mul `fp12_mul_dxs(z, x, y=sparse l)`.
   `Fp6` scratch (288 each): t0,t1,t2 (Karatsuba), s (a₀+a₁), r0,r1 (out),
   plus an `Fp2` scratch slot `sc` for `m2`. -/
namespace Dxs12
def T0 : Int := 0
def T1 : Int := 288
def T2 : Int := 576
def SA : Int := 864    -- a0 + a1 (Fp6)
def R0 : Int := 1152
def R1 : Int := 1440
def SC : Int := 1728   -- Fp2 scratch for m2
end Dxs12

/-- `bls12381_fp12_mul_dxs_x86_from_lean(z, x, y)`: `z = x · y` over `Fp12`,
    `x = r` dense, `y = l` the sparse Miller line (nonzero `Fp2` slots
    `l00=0, l01=96, l11=384`). Matches RELIC `fp12_mul_dxs` (else/PROJC,
    M-type). Composes the owned `fp6_mul_dxs`, `fp6_mul`, `fp2_mul`,
    `fp2_mul_nor`, `fp6_mul_art`, `fp6 add/sub`. Frame = 6 `Fp6` + 1 `Fp2`
    = 1824; `+8 ⇒ 1832`. -/
def fp12MulDxsAsm : String :=
  let F := "%rbp"; let X := "%r12"; let Y := "%r13"; let Z := "%rbx"
  open Dxs12 in
  -- byte offsets inside an Fp6 component (Fp2 slots 0,1,2)
  let j0 : Int := 0; let j1 : Int := 96; let j2 : Int := 192
  -- Fp12 w-coord offsets
  let w0 : Int := 0; let w1 : Int := 288
  framedDriver "bls12381_fp12_mul_dxs_x86_from_lean" 1832
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( -- t0 = a₀ ·dxs b₀   (b₀ = (l00, l01, 0): sparse fp6 mul)
      ( lea (w0) X "%rsi" :: lea (T0) F "%rdi" :: lea (w0) Y "%rdx"
        :: [ "\tcallq bls12381_fp6_mul_dxs_x86_from_lean" ] )
      -- t1 = a₁ ·"art-folded" b₁   (b₁ = (0, l11, 0)):
      --   t1₀ = ξ·(a₁₂·l11) ; t1₁ = a₁₀·l11 ; t1₂ = a₁₁·l11
    ++ m2 F SC F (T1+j1) X (w1+j2) Y (w1+j1)   -- tmp = a₁₂·l11  → into T1.c1 slot transiently
    ++ c2 fp2Nor F (T1+j0) F (T1+j1)           -- t1₀ = ξ·tmp
    ++ m2 F SC F (T1+j1) X (w1+j0) Y (w1+j1)   -- t1₁ = a₁₀·l11
    ++ m2 F SC F (T1+j2) X (w1+j1) Y (w1+j1)   -- t1₂ = a₁₁·l11
      -- t2 = b₀ + b₁ : t2₀ = l00 ; t2₁ = l01 + l11 ; t2₂ = 0
    ++ c2 fp2Copy F (T2+j0) Y (w0+j0)          -- t2₀ = l00
    ++ c3 fp2Add  F (T2+j1) Y (w0+j1) Y (w1+j1) -- t2₁ = l01 + l11
    -- t2₂ stays whatever; but fp6_mul_dxs only reads y0,y1 of its sparse arg,
    -- and here t2 is the *sparse* (y) operand below, so t2₂ is never read.
      -- s = a₀ + a₁   (Fp6 add)
    ++ ( lea (SA) F "%rdi" :: lea (w0) X "%rsi" :: lea (w1) X "%rdx"
         :: [ "\tcallq bls12381_fp6_add_x86_from_lean" ] )
      -- c₁ = s ·dxs t2   (t2 = (t2₀,t2₁,0) sparse)
    ++ ( lea (R1) F "%rdi" :: lea (SA) F "%rsi" :: lea (T2) F "%rdx"
         :: [ "\tcallq bls12381_fp6_mul_dxs_x86_from_lean" ] )
    ++ ( lea (R1) F "%rdi" :: lea (R1) F "%rsi" :: lea (T0) F "%rdx"
         :: [ "\tcallq bls12381_fp6_sub_x86_from_lean" ] )
    ++ ( lea (R1) F "%rdi" :: lea (R1) F "%rsi" :: lea (T1) F "%rdx"
         :: [ "\tcallq bls12381_fp6_sub_x86_from_lean" ] )
      -- c₀ = t0 + v·t1   (fp6_mul_art on t1, then fp6 add)
    ++ ( lea (T2) F "%rdi" :: lea (T1) F "%rsi"
         :: [ "\tcallq bls12381_fp6_mul_art_x86_from_lean" ] )
    ++ ( lea (R0) F "%rdi" :: lea (T0) F "%rsi" :: lea (T2) F "%rdx"
         :: [ "\tcallq bls12381_fp6_add_x86_from_lean" ] )
      -- copy r0 → z.w0, r1 → z.w1  (Fp6 copy via three Fp2 copies)
    ++ c2 fp2Copy Z (w0+j0) F (R0+j0)
    ++ c2 fp2Copy Z (w0+j1) F (R0+j1)
    ++ c2 fp2Copy Z (w0+j2) F (R0+j2)
    ++ c2 fp2Copy Z (w1+j0) F (R1+j0)
    ++ c2 fp2Copy Z (w1+j1) F (R1+j1)
    ++ c2 fp2Copy Z (w1+j2) F (R1+j2) )

/-! ## 6. `pp_dbl_k12` — `G2` doubling + line evaluation (M-type, general b)

The RELIC `pp_dbl_k12_projc` general-`b` else branch over `Fp2` plus the
M-type (`one=0, zero=1`) line writes. `q = (X,Y,Z)` packed `G2`; `p = (xₚ, yₚ)`
the affine `G1` point (two `Fp` scalars). Outputs the doubled point `r` (packed
`G2`) and the sparse line `l` (packed `Fp12`, only `l00,l01,l11` nonzero — the
caller zeroes the rest once).

    A=t0=X² ; B=t1=Y² ; C=t2=Z²
    t3 = 3C ; t3 = mul_b(t3)              (= D = 3b·C)
    t4 = (X+Y)² − A − B                   (= E)
    t5 = (Y+Z)² − B − C                   (= F)
    t6 = 3D                               (= G)
    Rx = E·(B − G)
    Ry = (B+G)² − 12·D²
    Rz = 4B·F
    l00 = D − B
    l01 = xₚ·A    (per Fp2 component)
    l11 = F·yₚ    (per Fp2 component)

Frame felems (`Fp2`, 96): t0..t6 (7), Rx,Ry,Rz (3), plus `Fp2` scratch `sc`
for `m2`, `sqr`/`mul_b` scratch. = 12 `Fp2` = 1152; `+8 ⇒ 1160`.
Bases: %rbx=r, %r12=q, %r13=l, %r14=p, %rbp=frame. -/

namespace Dbl
def T0 : Int := 0
def T1 : Int := 96
def T2 : Int := 192
def T3 : Int := 288
def T4 : Int := 384
def T5 : Int := 480
def T6 : Int := 576
def RX : Int := 672
def RY : Int := 768
def RZ : Int := 864
def SC : Int := 960    -- m2 / mul_b scratch
def TT : Int := 1056   -- extra temp (D², etc.)
end Dbl

/-- `bls12381_pp_dbl_k12(r, l, q, p)`: `G2` doubling with line eval, M-type,
    general `b`. Args `%rdi=r` (packed G2), `%rsi=l` (packed Fp12 line),
    `%rdx=q` (packed G2), `%rcx=p` (affine G1: xₚ at +0, yₚ at +48). -/
def ppDblAsm : String :=
  let F := "%rbp"; let Q := "%r12"; let L := "%r13"; let P := "%r14"; let R := "%rbx"
  open Dbl in
  framedDriver "bls12381_pp_dbl_k12" 1160
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r13", "\tmovq %rdx, %r12", "\tmovq %rcx, %r14" ]
    ( -- A=t0=X² ; B=t1=Y² ; C=t2=Z²
      c2 fp2Sqr F T0 Q oX
    ++ c2 fp2Sqr F T1 Q oY
    ++ c2 fp2Sqr F T2 Q oZ
      -- t3 = 3C ; D = mul_b(3C)
    ++ c2 fp2Dbl F T3 F T2
    ++ c3 fp2Add F T3 F T3 F T2
    ++ c2 "bls12381_ep2_mul_b_x86_from_lean" F SC F T3   -- SC = D
    ++ c2 fp2Copy F T3 F SC                              -- t3 = D
      -- E = (X+Y)² − A − B   → t4
    ++ c3 fp2Add F T4 Q oX Q oY
    ++ c2 fp2Sqr F SC F T4
    ++ c3 fp2Sub F T4 F SC F T0
    ++ c3 fp2Sub F T4 F T4 F T1
      -- F = (Y+Z)² − B − C   → t5
    ++ c3 fp2Add F T5 Q oY Q oZ
    ++ c2 fp2Sqr F SC F T5
    ++ c3 fp2Sub F T5 F SC F T1
    ++ c3 fp2Sub F T5 F T5 F T2
      -- G = 3D   → t6
    ++ c2 fp2Dbl F T6 F T3
    ++ c3 fp2Add F T6 F T6 F T3
      -- Rx = E·(B − G)
    ++ c3 fp2Sub F RX F T1 F T6
    ++ m2 F SC F RX F RX F T4
      -- Ry = (B+G)² − 12·D² :  t6=(B+G)² ; tt=D² ; Ry = 12·D² ; Ry = t6 − Ry
    ++ c3 fp2Add F T6 F T6 F T1
    ++ c2 fp2Sqr F SC F T6
    ++ c2 fp2Copy F T6 F SC          -- t6 = (B+G)²
    ++ c2 fp2Sqr F TT F T3           -- tt = D²
    ++ c2 fp2Dbl F RY F TT           -- Ry = 2D²
    ++ c2 fp2Dbl F SC F RY           -- sc = 4D²
    ++ c2 fp2Dbl F RY F SC           -- Ry = 8D²
    ++ c3 fp2Add F RY F RY F SC      -- Ry = 12D²
    ++ c3 fp2Sub F RY F T6 F RY      -- Ry = (B+G)² − 12D²
      -- Rz = 4B·F
    ++ c2 fp2Dbl F RZ F T1
    ++ c2 fp2Dbl F RZ F RZ           -- Rz = 4B
    ++ m2 F SC F RZ F RZ F T5
      -- l00 = D − B
    ++ c3 fp2Sub L (lij 0 0) F T3 F T1
      -- l01 = xₚ·A   (per Fp2 component; p->x at P+0)
    ++ ( lea (lij 0 1) L "%rdi" :: lea T0 F "%rsi" :: lea 0 P "%rdx"
         :: [ "\tcallq bls12381_fp2_scale_x86_from_lean" ] )
      -- l11 = F·yₚ   (p->y at P+48)
    ++ ( lea (lij 1 1) L "%rdi" :: lea T5 F "%rsi" :: lea imOff P "%rdx"
         :: [ "\tcallq bls12381_fp2_scale_x86_from_lean" ] )
      -- write r = (Rx,Ry,Rz)
    ++ c2 fp2Copy R oX F RX
    ++ c2 fp2Copy R oY F RY
    ++ c2 fp2Copy R oZ F RZ )

/-! ## 7. `pp_add_k12` — `G2` mixed addition + line evaluation (M-type)

RELIC `pp_add_k12_projc` (PROJC). `r` (in/out) is a projective `G2`; `q` is the
**affine** `G2` addend (`Z=1`, so only `X,Y` read); `p` affine `G1`.

    t0 = X₁ − X₂·Z₁ = B
    t1 = Y₁ − Y₂·Z₁ = A
    t2 = B²        ; Rx = X₁·D ; t2 = B³ = E
    t3 = A² ; t3 = A²·Z₁ ; t3 = E + t3 = F
    l01 = −A·xₚ                         (l[one][zero], M-type)
    t4 = B·X₂                           (for J)
    H = F − 2·G  (t3 −= Rx ; t3 −= Rx)
    Ry = A·(G − H) − Y₁·E
    Rx = B·H
    Rz = Z₁·E
    l00 = J = A·X₂ − B·Y₂               (l[one][one] → l00 under M-type swap)
    l11 = B·yₚ                          (l[zero][zero] → l11 under M-type swap)

Frame felems (`Fp2`): t0..t4 (5), Rx,Ry,Rz handled in place on `r` scratch
(we copy r to a working point first), plus the m2 scratch. We use a working
`Fp2` set t0..t4, Rx,Ry,Rz, sc = 9 `Fp2` = 864; `+8 ⇒ 872`.
Bases: %rbx=r, %r12=q (affine G2), %r13=l, %r14=p, %rbp=frame.
Note RELIC reads/writes `r->{x,y,z}` in place; we hold them in frame
(`RXi,RYi,RZi` ← copy of r) and write the result back at the end so r may alias
freely. -/

namespace Add
def T0 : Int := 0
def T1 : Int := 96
def T2 : Int := 192
def T3 : Int := 288
def T4 : Int := 384
def RX : Int := 480
def RY : Int := 576
def RZ : Int := 672
def SC : Int := 768
def NX : Int := 864    -- −xₚ (Fp, but kept in an Fp2-sized slot, only .re used)
end Add

/-- `bls12381_pp_add_k12(r, l, q, p)`: projective `G2` + affine `G2` addition
    with line eval, M-type, PROJC. Args `%rdi=r` (in/out packed G2),
    `%rsi=l` (packed Fp12 line), `%rdx=q` (affine G2 addend, X at +0, Y at +96),
    `%rcx=p` (affine G1: xₚ +0, yₚ +48). -/
def ppAddAsm : String :=
  let F := "%rbp"; let Q := "%r12"; let L := "%r13"; let P := "%r14"; let R := "%rbx"
  open Add in
  framedDriver "bls12381_pp_add_k12" 968
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r13", "\tmovq %rdx, %r12", "\tmovq %rcx, %r14" ]
    ( -- load r into frame working point (Rx,Ry,Rz)
      c2 fp2Copy F RX R oX
    ++ c2 fp2Copy F RY R oY
    ++ c2 fp2Copy F RZ R oZ
      -- t0 = X₁ − X₂·Z₁   (B)
    ++ m2 F SC F T0 Q oX F RZ
    ++ c3 fp2Sub F T0 F RX F T0
      -- t1 = Y₁ − Y₂·Z₁   (A)
    ++ m2 F SC F T1 Q oY F RZ
    ++ c3 fp2Sub F T1 F RY F T1
      -- t2 = B² ; Rx = X₁·t2 (=G) ; t2 = t2·B (=E)
    ++ c2 fp2Sqr F T2 F T0
    ++ m2 F SC F RX F RX F T2
    ++ m2 F SC F T2 F T2 F T0
      -- t3 = A² ; t3 = t3·Z₁ ; t3 = E + t3 (=F)
    ++ c2 fp2Sqr F T3 F T1
    ++ m2 F SC F T3 F T3 F RZ
    ++ c3 fp2Add F T3 F T2 F T3
      -- l01 = −(A·xₚ): nx = −xₚ ; l01 = A·nx   (per Fp2 component)
    ++ ( lea NX F "%rdi" :: lea 0 P "%rsi"
         :: [ "\tcallq bls12381_fp_neg_x86_from_lean" ] )
    ++ ( lea (lij 0 1) L "%rdi" :: lea T1 F "%rsi" :: lea NX F "%rdx"
         :: [ "\tcallq bls12381_fp2_scale_x86_from_lean" ] )
      -- t4 = X₂·A   (for J = A·X₂ − B·Y₂)
    ++ m2 F SC F T4 Q oX F T1
      -- H = F − 2G : t3 −= Rx ; t3 −= Rx
    ++ c3 fp2Sub F T3 F T3 F RX
    ++ c3 fp2Sub F T3 F T3 F RX
      -- Ry = A·(G − H) − Y₁·E :  Rx = G − H ; t1 = A·Rx ; Ry = E·Y₁ ; Ry = t1 − Ry
    ++ c3 fp2Sub F RX F RX F T3
    ++ m2 F SC F T1 F T1 F RX
    ++ m2 F SC F RY F T2 F RY
    ++ c3 fp2Sub F RY F T1 F RY
      -- Rx = B·H
    ++ m2 F SC F RX F T0 F T3
      -- Rz = Z₁·E
    ++ m2 F SC F RZ F RZ F T2
      -- l00 = J = A·X₂ − B·Y₂  (M-type: l[one][one] → l[0][0]) :  t2 = Y₂·B ; l00 = t4 − t2
    ++ m2 F SC F T2 Q oY F T0
    ++ c3 fp2Sub L (lij 0 0) F T4 F T2
      -- l11 = B·yₚ  (M-type: l[zero][zero] → l[1][1]; p->y at P+48)
    ++ ( lea (lij 1 1) L "%rdi" :: lea T0 F "%rsi" :: lea imOff P "%rdx"
         :: [ "\tcallq bls12381_fp2_scale_x86_from_lean" ] )
      -- write r = (Rx,Ry,Rz)
    ++ c2 fp2Copy R oX F RX
    ++ c2 fp2Copy R oY F RY
    ++ c2 fp2Copy R oZ F RZ )

/-! ## 8. Shape checks (composed-call counts witness the real schedules) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel (countSub hasSub)

/-- `fp6_mul_dxs` over a `(·₀,·₁,0)` sparse operand: **5 generic `Fp2`-muls +
    1 `fp2_mul_nor`** (`v0=a₀b₀, v1=a₁b₁, a₂b₁, (a₀+a₁)(b₀+b₁), a₂b₀`; the
    `a·b₂` products are killed by the structural `b₂ = 0`). -/
theorem fp6MulDxsAsm_counts :
    countSub fp6MulDxsAsm ("callq " ++ fp2Mul) = 5
      ∧ countSub fp6MulDxsAsm ("callq " ++ fp2Nor) = 1 := by native_decide

/-- `fp12_mul_dxs` carries **two `fp6_mul_dxs` calls** (the sparse `t0`, `c₁`
    products), one `fp6_mul_art` (the `v·t1` fold), and the `fp2_mul_nor` of the
    `a₁`-half — the M-type sparse dodecic schedule. -/
theorem fp12MulDxsAsm_counts :
    countSub fp12MulDxsAsm "callq bls12381_fp6_mul_dxs_x86_from_lean" = 2
      ∧ countSub fp12MulDxsAsm "callq bls12381_fp6_mul_art_x86_from_lean" = 1
      ∧ hasSub fp12MulDxsAsm ("callq " ++ fp2Nor) := by native_decide

/-- `pp_dbl_k12` composes the general-`b` RCB doubling + line eval: **3
    `fp2_sqr`** (`X²,Y²,Z²` plus the squarings of `E`/`(B+G)`/`D` realised via
    `fp2_sqr`), one `ep2_mul_b`, two `fp2_scale` line-evals (`xₚ·A`, `F·yₚ`),
    and the documented `fp2_{mul,add,sub,dbl}` mix. -/
theorem ppDblAsm_counts :
    countSub ppDblAsm "callq bls12381_ep2_mul_b_x86_from_lean" = 1
      ∧ countSub ppDblAsm "callq bls12381_fp2_scale_x86_from_lean" = 2
      ∧ hasSub ppDblAsm ("callq " ++ fp2Mul)
      ∧ hasSub ppDblAsm ("callq " ++ fp2Sqr) := by native_decide

/-- `pp_add_k12` composes the projective-+affine RCB addition + line eval: one
    `fp_neg` (the `−xₚ`), two `fp2_scale` line-evals (`−A·xₚ`, `B·yₚ`), and the
    `fp2_{mul,sqr,sub}` mix. -/
theorem ppAddAsm_counts :
    countSub ppAddAsm "callq bls12381_fp_neg_x86_from_lean" = 1
      ∧ countSub ppAddAsm "callq bls12381_fp2_scale_x86_from_lean" = 2
      ∧ hasSub ppAddAsm ("callq " ++ fp2Mul)
      ∧ hasSub ppAddAsm ("callq " ++ fp2Sqr) := by native_decide

/-! ## 9. Emit driver

Emits the Miller-loop leaves/drivers for the bench harness. The committed `Fp`,
`Fp2`, `Fp6`, `Fp12` leaves are referenced read-only (emitted by their owning
modules) and are **not** re-emitted here. The `pp_mil_k12` NAF driver is *not*
emitted as a single owned `.s` (the NAF recoding of the BLS `x` and the
variable-length loop are realised in the C harness, which calls the owned
`pp_dbl_k12`/`pp_add_k12`/`fp12_mul_dxs`/`fp12_sqr` per bit — the same
composition RELIC's `pp_mil_k12` uses); the per-bit owned steps are what is
KAT'd byte-identical, and the harness drives the loop. See the module docstring
and the bench README. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_miller_compare/gen_com"
  let g := "bench/bls12381_miller_compare/gen_com/"
  IO.FS.writeFile (g ++ "bls12381_fp_neg_x86_from_lean.s")        fpNegAsm
  IO.FS.writeFile (g ++ "bls12381_fp2_scale_x86_from_lean.s")     fp2ScaleAsm
  IO.FS.writeFile (g ++ "bls12381_ep2_mul_b_x86_from_lean.s")     ep2MulBAsm
  IO.FS.writeFile (g ++ "bls12381_fp6_mul_dxs_x86_from_lean.s")   fp6MulDxsAsm
  IO.FS.writeFile (g ++ "bls12381_fp12_mul_dxs_x86_from_lean.s")  fp12MulDxsAsm
  IO.FS.writeFile (g ++ "bls12381_pp_dbl_k12.s")                  ppDblAsm
  IO.FS.writeFile (g ++ "bls12381_pp_add_k12.s")                  ppAddAsm
  IO.println "wrote gen_com/{fp_neg,fp2_scale,ep2_mul_b,fp6_mul_dxs,fp12_mul_dxs}.s + pp_{dbl,add}_k12.s (owned x86 Miller-loop layer, M-type BLS12-381, over the committed Fp2/Fp6/Fp12/G2 leaves)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Miller
