/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel

/-!
# BLS12-381 `Fp6` + `Fp12` (GT-field) multiply, owned x86 (#602/#219)

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

The BLS12-381 pairing tower, continued **two layers up** from the committed
`Fp2` leaf (`Bls12381Fp2MulKernel`, commit 52dc486f, `bls12381_fp2_mul/sqr`):

* `Fp6 = Fp2[v]/(v³ − ξ)`, `ξ = (1 + u)`  — the sextic extension. An element is
  `a₀ + a₁·v + a₂·v²` with `aᵢ ∈ Fp2`.
* `Fp12 = Fp6[w]/(w² − v)` — the dodecic extension, the BLS12-381 target group
  `GT`'s field. An element is `c₀ + c₁·w` with `cⱼ ∈ Fp6`.

Both layers are emitted as **owned drivers** that compose the committed owned
`Fp2` leaf (`bls12381_fp2_mul_x86_from_lean`, 3 real `Fp`-muls each) plus the
owned `Fp2` add / sub / mul-by-ξ (the non-residue `E`) and the owned `Fp6`
mul-by-`v` (`fp6_mul_art`) helpers emitted **here**. No jasminc: the deep tower
nesting (`Fp6`→`Fp2`→`Fp`, `Fp12`→`Fp6`→`Fp2`→`Fp`) is the exact place jasminc's
register allocator (#241) wall bit hardest on the pairing wrappers; the owned
**caller-owned frame-spilling** discipline (save bases in callee-saved
registers, hold every cross-`Fp2`/`Fp6` live value as a stack felem, recompute
operand pointers with `leaq` before each `call`) clears it.

## Non-residue conventions (must match RELIC byte-for-byte)

The KAT gate is **byte-identical to RELIC** `fp6_mul` / `fp12_mul`. RELIC fixes
(BLS12-381, `p ≡ 3 mod 8`, `qnr = 1`, `relic_fp2_mul.c::fp2_mul_nor_basic`
case 3):

    ξ·(c₀ + c₁·u) = (c₀ − c₁) + (c₀ + c₁)·u            -- `fp2_mul_nor`, mul-by-(1+u)

and the `Fp6` mul-by-`v` (`relic_fp6_mul.c::fp6_mul_art`):

    v·(a₀ + a₁·v + a₂·v²) = ξ·a₂ + a₀·v + a₁·v²        -- the v²·v = v³ = ξ wrap

The `Fp6` multiply schedule below is **exactly** RELIC's `fp6_mul_basic`
(6 `Fp2`-muls + 2 `fp2_mul_nor` + the Karatsuba `Fp2` add/subs); the `Fp12`
multiply is **exactly** RELIC's `fp12_mul_basic` (3 `Fp6`-muls + one
`fp6_mul_art` + the Karatsuba `Fp6` add/subs).

## Real `Fp`-mul call counts

* one `Fp2` mul  = 3 `Fp`-muls;
* one `Fp6` mul  = 6 `Fp2`-muls = **18 `Fp`-muls**;
* one `Fp12` mul = 3 `Fp6`-muls = **54 `Fp`-muls**.

The shape theorems below witness 6 `callq …fp2_mul…` in the `Fp6` driver and
3 `callq …fp6_mul…` in the `Fp12` driver — the tower call graph, not a
0–1-multiply stub.

## What is verified vs trusted (scope)

Identical status to the committed `Fp2` module: the `Fp` add/sub bodies are
`runBlock`-verified leaves (in the committed module); the `Fp2`/`Fp6`/`Fp12`
**drivers** are sequences of `call`s over a caller-owned `%rsp`-moving stack
frame — **trusted SysV ABI scaffolding** outside the verified field bodies, the
same standard as the committed `Fp2` driver and `renderLeafFn` prologue/epilogue
elsewhere. Value-level correctness — that the emitted drivers compute the
`Fp6`/`Fp12` product — is the **external KAT** (`bench/bls12381_fp6_compare`, vs
RELIC `fp6_mul`/`fp12_mul` and GMP over the same canonical prime, per `Fp2`/`Fp6`
component), the standard gate for these word kernels (per REV-12).

This is the **GT-field arithmetic** (`Fp6`/`Fp12` mul) of the pairing tower —
**not** `pp_map`. The Miller loop (line evaluations + the `f`-accumulation over
the BLS `x`-NAF) and the final exponentiation remain the documented follow-on
layers to a fully-owned pairing.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 0. Owned-leaf symbol names (the committed/emitted lower-tier kernels) -/

/-- The committed owned `Fp` add leaf (`Bls12381Fp2MulKernel.fpAddAsm`). -/
def fpAddSym : String := "bls12381_fp_add_x86_from_lean"
/-- The committed owned `Fp` sub leaf. -/
def fpSubSym : String := "bls12381_fp_sub_x86_from_lean"
/-- The committed owned `Fp2` Karatsuba mul driver (`bls12381_fp2_mul…`). -/
def fp2MulSym : String := "bls12381_fp2_mul_x86_from_lean"

/-- The `Fp2` add leaf emitted here (componentwise `Fp` add). -/
def fp2AddSym : String := "bls12381_fp2_add_x86_from_lean"
/-- The `Fp2` sub leaf emitted here (componentwise `Fp` sub). -/
def fp2SubSym : String := "bls12381_fp2_sub_x86_from_lean"
/-- The `Fp2` mul-by-ξ=(1+u) leaf emitted here (`fp2_mul_nor`). -/
def fp2NorSym : String := "bls12381_fp2_mul_nor_x86_from_lean"
/-- The `Fp6` mul-by-`v` leaf emitted here (`fp6_mul_art`). -/
def fp6ArtSym : String := "bls12381_fp6_mul_art_x86_from_lean"

/-! ## 1. Byte-offset layout of the tower felems

`Fp`  felem = 6×u64 = **48 bytes**.
`Fp2` felem = 2 `Fp` (re, im) = **96 bytes**; `re` at `+0`, `im` at `+48`.
`Fp6` felem = 3 `Fp2` (a₀,a₁,a₂) = **288 bytes**; `a₀` at `+0`, `a₁` at `+96`,
`a₂` at `+192`.
`Fp12` felem = 2 `Fp6` (c₀,c₁) = **576 bytes**; `c₀` at `+0`, `c₁` at `+288`.

The owned buffers are contiguous in this layout (the bench harness controls the
owned layout and bridges to RELIC per-`Fp` component through canonical mpz, so
no shared raw encoding is assumed). -/

/-- byte size of an `Fp` felem. -/
def fpBytes : Int := 48
/-- byte size of an `Fp2` felem. -/
def fp2Bytes : Int := 96
/-- byte size of an `Fp6` felem. -/
def fp6Bytes : Int := 288
/-- `Fp2.im` byte offset within an `Fp2` felem. -/
def imOff : Int := 48
/-- `Fp6` coordinate byte offsets (`a₀,a₁,a₂`). -/
def c0 : Int := 0
def c1 : Int := 96
def c2 : Int := 192
/-- `Fp12` coordinate byte offsets (`c₀,c₁`). -/
def w0 : Int := 0
def w1 : Int := 288

/-! ## 2. The SysV-ABI call helper (caller-owned frame-spilling)

`callTri leaf zb zoff xb xoff yb yoff` emits a 3-pointer SysV call
`leaf(z = zoff(zb), x = xoff(xb), y = yoff(yb))`, forming each pointer with
`leaq off(%base), %argreg`. `%rdi/%rsi/%rdx` are the first three SysV integer
args; the live bases (`z`/`x`/`y`) are held across the calls in callee-saved
registers (`%rbx`/`%r12`/`%r13`) and the scratch felems in the `%rbp` frame —
this is the owned frame-spilling discipline that clears the jasminc #241 wall on
the deep tower nesting. -/

/-- Emit `leaq off(%base), %argreg`. -/
def lea (off : Int) (base argreg : String) : String :=
  "\tleaq " ++ toString off ++ "(" ++ base ++ "), " ++ argreg

/-- A 3-pointer SysV call into an owned leaf. -/
def callTri (leaf : String) (zb : String) (zoff : Int)
    (xb : String) (xoff : Int) (yb : String) (yoff : Int) : List String :=
  [ lea zoff zb "%rdi", lea xoff xb "%rsi", lea yoff yb "%rdx", "\tcallq " ++ leaf ]

/-- A 2-pointer SysV call into an owned leaf (`leaf(z, x)`), for the unary
    helpers `fp2_mul_nor` and `fp6_mul_art`. -/
def callBin (leaf : String) (zb : String) (zoff : Int)
    (xb : String) (xoff : Int) : List String :=
  [ lea zoff zb "%rdi", lea xoff xb "%rsi", "\tcallq " ++ leaf ]

/-- Standard 6-push prologue + `subq $frame` + `movq %rsp,%rbp` framed leaf.
    `frame` must be `≡ 8 (mod 16)` so each inner `callq` lands `%rsp ≡ 0 mod 16`
    (entry `%rsp ≡ 8 mod 16`; six 8-byte pushes preserve `≡ 8 mod 16`). The
    saved arg bases are moved into callee-saved registers in `saveMoves`. -/
def framedDriver (name : String) (frame : Int) (saveMoves : List String)
    (body : List String) : String :=
  renderLeafFn name
    ([ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
     , "\tpushq %rbp"
     , "\tsubq $" ++ toString frame ++ ", %rsp", "\tmovq %rsp, %rbp" ] ++ saveMoves)
    body
    [ "\taddq $" ++ toString frame ++ ", %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-! ## 3. `Fp2` add / sub / mul-by-ξ leaves (compose the verified `Fp` leaves)

`Fp2` add / sub are componentwise `Fp` add / sub: `z.re = x.re ± y.re`,
`z.im = x.im ± y.im` — two `Fp` calls each. The frame is empty (no scratch
felem); only the three bases are saved. Frame `8` keeps `%rsp ≡ 0 mod 16` at the
inner `Fp` calls. -/

/-- `bls12381_fp2_add_x86_from_lean(z, x, y)` = componentwise `Fp` add. -/
def fp2AddAsm : String :=
  framedDriver fp2AddSym 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( callTri fpAddSym "%rbx" 0     "%r12" 0     "%r13" 0       -- z.re = x.re + y.re
    ++ callTri fpAddSym "%rbx" imOff "%r12" imOff "%r13" imOff ) -- z.im = x.im + y.im

/-- `bls12381_fp2_sub_x86_from_lean(z, x, y)` = componentwise `Fp` sub. -/
def fp2SubAsm : String :=
  framedDriver fp2SubSym 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( callTri fpSubSym "%rbx" 0     "%r12" 0     "%r13" 0
    ++ callTri fpSubSym "%rbx" imOff "%r12" imOff "%r13" imOff )

/-- `bls12381_fp2_mul_nor_x86_from_lean(z, x)` = mul by ξ=(1+u): for
    `x = c₀ + c₁·u`, `ξ·x = (c₀ − c₁) + (c₀ + c₁)·u`. Matches RELIC
    `fp2_mul_nor_basic` case 3 (`p ≡ 3 mod 8`, `qnr = 1`). Requires `z ≠ x`
    (the non-aliasing contract RELIC's `fp2_mul_nor` is invoked under here):
    `z.im` is computed from `x.re,x.im` and `z.re` from the same, into the
    distinct `z`. -/
def fp2NorAsm : String :=
  framedDriver fp2NorSym 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( callTri fpAddSym "%rbx" imOff "%r12" 0     "%r12" imOff   -- z.im = x.re + x.im
    ++ callTri fpSubSym "%rbx" 0     "%r12" 0     "%r12" imOff ) -- z.re = x.re − x.im

/-! ## 3b. `Fp2` inverse `fp2_inv` (the pairing-final-exp tower base, #fp12-inv)

`x = a + b·u`, `x⁻¹ = (a − b·u)/(a²+b²)`.  The base-field inverse is the AUCurves
Bernstein–Yang safegcd leaf `bls12_invert_divstep_sat` — but it operates on
**canonical** `Fp` (6×u64 LE), while this tower is in **Montgomery** form.  We
bracket the inverse with the two standard Montgomery conversions, both supplied
via `cptr → [one(48) ‖ R²(48)]` (the harness builds them from the prime, exactly
as `fp12_frb` passes its `γ` constants):

* `from_mont(y') = mont_mul(y', one)`  (`y·R·1·R⁻¹ = y`, canonical);
* `to_mont(y)   = mont_mul(y,  R²)`    (`y·R²·R⁻¹ = y·R`, Montgomery).

So `INVM = to_mont(invLeaf(from_mont(norm')))` is `norm⁻¹` in Montgomery form,
and `z.re = a·INVM`, `z.im = −(b·INVM)` (both Montgomery).  Every read of `x`
precedes the writes to `z`, so `z` may alias `x`. -/

/-- The committed owned `Fp` Montgomery-mul leaf (`bls12381_mont_mul…`, #490). -/
def fpMulSym : String := "bls12381_mont_mul_x86_from_lean"
/-- The AUCurves Bernstein–Yang safegcd base-field inverse leaf (canonical
    6×u64 in/out) — the same leaf `BLS12381GroupEmit` wires for affine inverses. -/
def fpInvSym : String := "bls12_invert_divstep_sat"
/-- Emitted `Fp2` inverse driver symbol. -/
def fp2InvSym : String := "bls12381_fp2_inv_x86_from_lean"

/-- `bls12381_fp2_inv_x86_from_lean(z, x, cptr)` = `x⁻¹` over `Fp2`, Montgomery
    form (alias-safe, `cptr → [one ‖ R²]`).  Scratch felems: `T0/norm@0`, `T1@48`,
    `NC@96`, `INV@144`, `INVM@192`, `T2@240`, `ZERO@288`. -/
def fp2InvAsm : String :=
  framedDriver fp2InvSym 344
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( -- T0 = a²,  T1 = b²   (Montgomery)
      callTri fpMulSym "%rbp" 0   "%r12" 0     "%r12" 0
    ++ callTri fpMulSym "%rbp" 48  "%r12" imOff "%r12" imOff
      -- T0 = norm' = a² + b²
    ++ callTri fpAddSym "%rbp" 0   "%rbp" 0     "%rbp" 48
      -- NC = from_mont(norm') = mont_mul(norm', one)   (canonical norm)
    ++ callTri fpMulSym "%rbp" 96  "%rbp" 0     "%r13" 0
      -- INV = invLeaf(NC)   (canonical inverse)
    ++ callBin fpInvSym "%rbp" 144 "%rbp" 96
      -- INVM = to_mont(INV) = mont_mul(INV, R²)   (Montgomery norm⁻¹)
    ++ callTri fpMulSym "%rbp" 192 "%rbp" 144 "%r13" 48
      -- T2 = b·INVM   (read x.im before writing z)
    ++ callTri fpMulSym "%rbp" 240 "%r12" imOff "%rbp" 192
      -- ZERO = x.re − x.re   (read x.re before writing z)
    ++ callTri fpSubSym "%rbp" 288 "%r12" 0     "%r12" 0
      -- z.re = a·INVM
    ++ callTri fpMulSym "%rbx" 0     "%r12" 0   "%rbp" 192
      -- z.im = 0 − T2 = −(b·INVM)
    ++ callTri fpSubSym "%rbx" imOff "%rbp" 288 "%rbp" 240 )

/-! ## 3c. `Fp6` inverse `fp6_inv` (cubic extension, composes `fp2_inv`).

`Fp6 = Fp2[v]/(v³ − ξ)`.  RELIC `fp6_inv_basic`: for `x = a₀ + a₁v + a₂v²`,
`A = a₀² − ξ·a₁a₂`, `B = ξ·a₂² − a₀a₁`, `C = a₁² − a₀a₂`, norm
`N = a₀A + ξ·a₂B + ξ·a₁C ∈ Fp2`, and `x⁻¹ = (A·N⁻¹) + (B·N⁻¹)v + (C·N⁻¹)v²`.
The single `Fp2` inverse `N⁻¹` is the committed `fp2_inv` (so `cptr` threads
through).  `fp2_mul_nor` requires `z ≠ x`, so every `ξ·` writes a fresh felem.
Scratch (6 `Fp2`): `v0/v1/v2@0/96/192` (`A/B/C`), `t0/t1/t2@288/384/480`. -/
def fp6InvSym : String := "bls12381_fp6_inv_x86_from_lean"
/-- The committed owned `Fp2` square leaf. -/
def fp2SqrSym : String := "bls12381_fp2_sqr_x86_from_lean"

/-- `bls12381_fp6_inv_x86_from_lean(z, x, cptr)` = `x⁻¹` over `Fp6` (Montgomery,
    alias-safe, `cptr → [one ‖ R²]` forwarded to the inner `fp2_inv`). -/
def fp6InvAsm : String :=
  framedDriver fp6InvSym 584
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( -- A = a₀² − ξ(a₁a₂)
      callBin fp2SqrSym "%rbp" 288 "%r12" c0
    ++ callTri fp2MulSym "%rbp" 384 "%r12" c1 "%r12" c2
    ++ callBin fp2NorSym "%rbp" 480 "%rbp" 384
    ++ callTri fp2SubSym "%rbp" 0   "%rbp" 288 "%rbp" 480
      -- B = ξ·a₂² − a₀a₁
    ++ callBin fp2SqrSym "%rbp" 288 "%r12" c2
    ++ callBin fp2NorSym "%rbp" 384 "%rbp" 288
    ++ callTri fp2MulSym "%rbp" 288 "%r12" c0 "%r12" c1
    ++ callTri fp2SubSym "%rbp" 96  "%rbp" 384 "%rbp" 288
      -- C = a₁² − a₀a₂
    ++ callBin fp2SqrSym "%rbp" 288 "%r12" c1
    ++ callTri fp2MulSym "%rbp" 384 "%r12" c0 "%r12" c2
    ++ callTri fp2SubSym "%rbp" 192 "%rbp" 288 "%rbp" 384
      -- N = a₀A + ξ·a₂B + ξ·a₁C
    ++ callTri fp2MulSym "%rbp" 288 "%r12" c0 "%rbp" 0
    ++ callTri fp2MulSym "%rbp" 384 "%r12" c2 "%rbp" 96
    ++ callBin fp2NorSym "%rbp" 480 "%rbp" 384
    ++ callTri fp2AddSym "%rbp" 288 "%rbp" 288 "%rbp" 480
    ++ callTri fp2MulSym "%rbp" 384 "%r12" c1 "%rbp" 192
    ++ callBin fp2NorSym "%rbp" 480 "%rbp" 384
    ++ callTri fp2AddSym "%rbp" 288 "%rbp" 288 "%rbp" 480
      -- t1 = N⁻¹  (inner fp2_inv, cptr = %r13)
    ++ callTri fp2InvSym "%rbp" 384 "%rbp" 288 "%r13" 0
      -- z = (A,B,C)·N⁻¹
    ++ callTri fp2MulSym "%rbx" c0 "%rbp" 0   "%rbp" 384
    ++ callTri fp2MulSym "%rbx" c1 "%rbp" 96  "%rbp" 384
    ++ callTri fp2MulSym "%rbx" c2 "%rbp" 192 "%rbp" 384 )

/-! ## 3d. `Fp6` sub + `Fp12` inverse `fp12_inv` (quadratic ext, composes `fp6_inv`).

`fp6_sub` is componentwise `Fp2` sub (3 coordinates).  `Fp12 = Fp6[w]/(w² − v)`:
for `x = c₀ + c₁w`, `x⁻¹ = (c₀ − c₁w)/(c₀² − v·c₁²)`.  With `t = c₀² − v·c₁²`
(`v·` is `fp6_mul_art`), `t⁻¹` the committed `fp6_inv`, the result is
`(c₀·t⁻¹) − (c₁·t⁻¹)·w`.  Scratch (7 `Fp6`): `t0@0 t1@288 t1art@576 t@864
tinv@1152 c1t@1440 ZERO6@1728`; `cptr` threads to the inner `fp6_inv`. -/
/-- Symbols for the `Fp6` sub / mul leaves (bodies `fp6SubAsm` / `fp6MulAsm`
    defined below) + the `Fp12` inverse driver. -/
def fp6SubSym : String := "bls12381_fp6_sub_x86_from_lean"
def fp6MulSym : String := "bls12381_fp6_mul_x86_from_lean"
def fp12InvSym : String := "bls12381_fp12_inv_x86_from_lean"

/-- `bls12381_fp12_inv_x86_from_lean(z, x, cptr)` = `x⁻¹` over `Fp12` (Montgomery,
    alias-safe, `cptr → [one ‖ R²]` forwarded down to the inner `fp2_inv`). -/
def fp12InvAsm : String :=
  framedDriver fp12InvSym 2024
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( -- t0 = c₀², t1 = c₁²
      callTri fp6MulSym "%rbp" 0    "%r12" w0 "%r12" w0
    ++ callTri fp6MulSym "%rbp" 288  "%r12" w1 "%r12" w1
      -- t1art = v·c₁²
    ++ callBin fp6ArtSym "%rbp" 576  "%rbp" 288
      -- t = c₀² − v·c₁²
    ++ callTri fp6SubSym "%rbp" 864  "%rbp" 0   "%rbp" 576
      -- tinv = t⁻¹  (inner fp6_inv, cptr = %r13)
    ++ callTri fp6InvSym "%rbp" 1152 "%rbp" 864 "%r13" 0
      -- ZERO6 = c₀ − c₀  (read c₀ before writing z)
    ++ callTri fp6SubSym "%rbp" 1728 "%r12" w0 "%r12" w0
      -- c1t = c₁·tinv
    ++ callTri fp6MulSym "%rbp" 1440 "%r12" w1 "%rbp" 1152
      -- z.w₀ = c₀·tinv
    ++ callTri fp6MulSym "%rbx" w0   "%r12" w0 "%rbp" 1152
      -- z.w₁ = 0 − c₁·tinv
    ++ callTri fp6SubSym "%rbx" w1   "%rbp" 1728 "%rbp" 1440 )

/-! ## 3e. Final-exp easy part `fp12_conv_cyc` (`f ↦ f^{(p⁶−1)(p²+1)}`).

This is the composition the BLS12-381 final exponentiation was missing once
`fp12_inv` landed.  `f^{p⁶−1} = conj(f)·f⁻¹` (where `conj = fp12_inv_cyc`, the
`(c₀,−c₁)` map = `f^{p⁶}` for general `f`), giving a cyclotomic element `g`; then
`g^{p²+1} = frb²(g)·g` (two single-step `fp12_frb` applications = the `p²` power).
ABI `(z, f, cptr, gptr)`: `cptr=[one‖R²]` for `fp12_inv`, `gptr=[γ₁…γ₅]` for the
Frobenius.  Scratch (5 `Fp12`): `conj@0 inv@576 g@1152 g2@1728 g3@2304`. -/
def fp12ConvCycSym : String := "bls12381_fp12_conv_cyc_x86_from_lean"
def fp12InvCycSym : String := "bls12381_fp12_inv_cyc_x86_from_lean"
def fp12FrbSym : String := "bls12381_fp12_frb_x86_from_lean"
def fp12MulSym : String := "bls12381_fp12_mul_x86_from_lean"

/-- `bls12381_fp12_conv_cyc_x86_from_lean(z, f, cptr, gptr)` = `f^{(p⁶−1)(p²+1)}`,
    the final-exp easy part, composing the committed `fp12_{inv_cyc,inv,mul,frb}`
    leaves (`gptr` = the five `Fp2` Frobenius constants, owned Montgomery). -/
def fp12ConvCycAsm : String :=
  framedDriver fp12ConvCycSym 2888
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13", "\tmovq %rcx, %r14" ]
    ( -- conj = f^{p⁶} = (c₀, −c₁)
      callBin fp12InvCycSym "%rbp" 0    "%r12" 0
      -- inv = f⁻¹
    ++ callTri fp12InvSym "%rbp" 576  "%r12" 0    "%r13" 0
      -- g = conj·inv = f^{p⁶−1}  (cyclotomic)
    ++ callTri fp12MulSym "%rbp" 1152 "%rbp" 0    "%rbp" 576
      -- g2 = frb(g), g3 = frb(g2) = g^{p²}
    ++ callTri fp12FrbSym "%rbp" 1728 "%rbp" 1152 "%r14" 0
    ++ callTri fp12FrbSym "%rbp" 2304 "%rbp" 1728 "%r14" 0
      -- z = g^{p²}·g = g^{p²+1}
    ++ callTri fp12MulSym "%rbx" 0    "%rbp" 2304 "%rbp" 1152 )

/-! ## 4. The `Fp6` mul-by-`v` leaf (`fp6_mul_art`)

`v·(a₀ + a₁·v + a₂·v²) = ξ·a₂ + a₀·v + a₁·v²`, i.e. the output coordinates are
`(ξ·a₂, a₀, a₁)`. The `a₀→c₁`, `a₁→c₂` moves are `Fp2` copies (two `Fp` copies
each, here a copy is `Fp` add of the value to a zero — but cheaper to copy
limbs); to stay leaf-free we route the copies through the verified `Fp` add
against a zero felem held in the frame. The `ξ·a₂` is the `fp2_mul_nor` leaf.

`fp6_mul_art` is invoked by `fp12_mul` with `z ≠ x` would alias (RELIC uses a
temp `t0 = a[0]` precisely because the rotation overwrites). We require `z ≠ x`
and compute into the scratch frame felems, then copy out, so the rotation is
alias-safe regardless. Frame = 3 `Fp2` scratch felems (r0,r1,r2) + a zero felem.
`288 + 96 = 384`; `+8 ⇒ 392 ≡ 8 mod 16`. -/

/-- scratch `Fp2` rotation slots in the `fp6_mul_art` frame. -/
def artR0 : Int := 0
def artR1 : Int := 96
def artR2 : Int := 192
/-- a zeroed `Fp2` felem, for routing copies through the verified `Fp` add. -/
def artZero : Int := 288

/-- `bls12381_fp6_mul_art_x86_from_lean(z, x)` = `v·x` over `Fp6`.
    Output `(ξ·a₂, a₀, a₁)`. The zero felem is materialised with `Fp` sub of a
    value from itself (`y − y = 0`) into the frame, then each copy is `Fp` add
    against it. Requires `z ≠ x`. -/
def fp6ArtAsm : String :=
  framedDriver fp6ArtSym 392
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( -- zero felem: artZero = x.a0 − x.a0  (re and im halves)
      callTri fpSubSym "%rbp" artZero          "%r12" 0           "%r12" 0
    ++ callTri fpSubSym "%rbp" (artZero+imOff)  "%r12" imOff       "%r12" imOff
      -- r0 = ξ·a₂  (into scratch, alias-safe)
    ++ callBin fp2NorSym "%rbp" artR0 "%r12" c2
      -- r1 = a₀ + 0 ; r2 = a₁ + 0  (Fp2 copies via verified Fp add)
    ++ callTri fpAddSym "%rbp" artR1          "%r12" c0          "%rbp" artZero
    ++ callTri fpAddSym "%rbp" (artR1+imOff)  "%r12" (c0+imOff)  "%rbp" (artZero+imOff)
    ++ callTri fpAddSym "%rbp" artR2          "%r12" c1          "%rbp" artZero
    ++ callTri fpAddSym "%rbp" (artR2+imOff)  "%r12" (c1+imOff)  "%rbp" (artZero+imOff)
      -- copy r0,r1,r2 → z.c0,z.c1,z.c2  (via Fp add against the zero felem)
    ++ callTri fpAddSym "%rbx" c0          "%rbp" artR0          "%rbp" artZero
    ++ callTri fpAddSym "%rbx" (c0+imOff)  "%rbp" (artR0+imOff)  "%rbp" (artZero+imOff)
    ++ callTri fpAddSym "%rbx" c1          "%rbp" artR1          "%rbp" artZero
    ++ callTri fpAddSym "%rbx" (c1+imOff)  "%rbp" (artR1+imOff)  "%rbp" (artZero+imOff)
    ++ callTri fpAddSym "%rbx" c2          "%rbp" artR2          "%rbp" artZero
    ++ callTri fpAddSym "%rbx" (c2+imOff)  "%rbp" (artR2+imOff)  "%rbp" (artZero+imOff) )

/-! ## 5. The `Fp6` multiply driver (exactly RELIC `fp6_mul_basic`)

Schedule (`v0,v1,v2,t0,t1,t2` scratch `Fp2` felems; output `r0,r1,r2` scratch
then copied to `z`, so aliasing of `z` with `x`/`y` is harmless):

    v0 = a₀·b₀ ; v1 = a₁·b₁ ; v2 = a₂·b₂
    -- c₀ = v0 + ξ·((a₁+a₂)(b₁+b₂) − v1 − v2)
    t0 = a₁+a₂ ; t1 = b₁+b₂ ; t2 = t0·t1 ; t2 = t2−v1 ; t2 = t2−v2 ; t0 = ξ·t2 ; r0 = t0+v0
    -- c₁ = (a₀+a₁)(b₀+b₁) − v0 − v1 + ξ·v2
    t0 = a₀+a₁ ; t1 = b₀+b₁ ; r1 = t0·t1 ; r1 = r1−v0 ; r1 = r1−v1 ; t0 = ξ·v2 ; r1 = r1+t0
    -- c₂ = (a₀+a₂)(b₀+b₂) − v0 + v1 − v2
    t0 = a₀+a₂ ; t1 = b₀+b₂ ; r2 = t0·t1 ; r2 = r2−v0 ; r2 = r2+v1 ; r2 = r2−v2
    z.c₀ = r0 ; z.c₁ = r1 ; z.c₂ = r2

6 `Fp2`-muls (= 18 `Fp`-muls) + 2 `fp2_mul_nor` + Karatsuba `Fp2` add/subs.
Scratch frame: 9 `Fp2` felems (v0,v1,v2,t0,t1,t2,r0,r1,r2) = `864` bytes;
`+8 ⇒ 872 ≡ 8 mod 16`. The copy-out of r0..r2 is an `Fp2` add against the v2
slot reused as zero — simpler: store r0..r2 directly as the targets of the final
ops, and use `fp2_add` of the result to a zero. To avoid an extra zero felem we
instead make r0,r1,r2 the *direct* output halves of the last op writing each
coordinate. We keep r-slots and emit a trailing `fp2_add`(z, r, zero); the zero
felem is the 10th slot. -/

def V0 : Int := 0
def V1 : Int := 96
def V2 : Int := 192
def T0 : Int := 288
def T1 : Int := 384
def T2 : Int := 480
def R0 : Int := 576
def R1 : Int := 672
def R2 : Int := 768
def ZER : Int := 864   -- zero felem for the copy-out

/-- `bls12381_fp6_mul_x86_from_lean(z, x, y)` over `Fp6 = Fp2[v]/(v³−ξ)`.
    Composes the committed `Fp2` mul + the `Fp2` add/sub/mul-by-ξ leaves; matches
    RELIC `fp6_mul_basic`. Frame = 10 `Fp2` felems = `960` bytes; `+8 ⇒ 968`. -/
def fp6MulAsm : String :=
  framedDriver "bls12381_fp6_mul_x86_from_lean" 968
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( -- zero felem ZER = a₀ − a₀
      callTri fpSubSym "%rbp" ZER          "%r12" 0           "%r12" 0
    ++ callTri fpSubSym "%rbp" (ZER+imOff)  "%r12" imOff       "%r12" imOff
      -- v0,v1,v2
    ++ callTri fp2MulSym "%rbp" V0 "%r12" c0 "%r13" c0
    ++ callTri fp2MulSym "%rbp" V1 "%r12" c1 "%r13" c1
    ++ callTri fp2MulSym "%rbp" V2 "%r12" c2 "%r13" c2
      -- c₀ = v0 + ξ·((a₁+a₂)(b₁+b₂) − v1 − v2)
    ++ callTri fp2AddSym "%rbp" T0 "%r12" c1 "%r12" c2
    ++ callTri fp2AddSym "%rbp" T1 "%r13" c1 "%r13" c2
    ++ callTri fp2MulSym "%rbp" T2 "%rbp" T0 "%rbp" T1
    ++ callTri fp2SubSym "%rbp" T2 "%rbp" T2 "%rbp" V1
    ++ callTri fp2SubSym "%rbp" T2 "%rbp" T2 "%rbp" V2
    ++ callBin fp2NorSym "%rbp" T0 "%rbp" T2
    ++ callTri fp2AddSym "%rbp" R0 "%rbp" T0 "%rbp" V0
      -- c₁ = (a₀+a₁)(b₀+b₁) − v0 − v1 + ξ·v2
    ++ callTri fp2AddSym "%rbp" T0 "%r12" c0 "%r12" c1
    ++ callTri fp2AddSym "%rbp" T1 "%r13" c0 "%r13" c1
    ++ callTri fp2MulSym "%rbp" R1 "%rbp" T0 "%rbp" T1
    ++ callTri fp2SubSym "%rbp" R1 "%rbp" R1 "%rbp" V0
    ++ callTri fp2SubSym "%rbp" R1 "%rbp" R1 "%rbp" V1
    ++ callBin fp2NorSym "%rbp" T0 "%rbp" V2
    ++ callTri fp2AddSym "%rbp" R1 "%rbp" R1 "%rbp" T0
      -- c₂ = (a₀+a₂)(b₀+b₂) − v0 + v1 − v2
    ++ callTri fp2AddSym "%rbp" T0 "%r12" c0 "%r12" c2
    ++ callTri fp2AddSym "%rbp" T1 "%r13" c0 "%r13" c2
    ++ callTri fp2MulSym "%rbp" R2 "%rbp" T0 "%rbp" T1
    ++ callTri fp2SubSym "%rbp" R2 "%rbp" R2 "%rbp" V0
    ++ callTri fp2AddSym "%rbp" R2 "%rbp" R2 "%rbp" V1
    ++ callTri fp2SubSym "%rbp" R2 "%rbp" R2 "%rbp" V2
      -- copy r0,r1,r2 → z (Fp2 add against zero), alias-safe
    ++ callTri fp2AddSym "%rbx" c0 "%rbp" R0 "%rbp" ZER
    ++ callTri fp2AddSym "%rbx" c1 "%rbp" R1 "%rbp" ZER
    ++ callTri fp2AddSym "%rbx" c2 "%rbp" R2 "%rbp" ZER )

/-! ## 6. `Fp6` add / sub leaves (componentwise `Fp2`, for the `Fp12` Karatsuba) -/

/-- `bls12381_fp6_add_x86_from_lean(z, x, y)` = three `Fp2` adds. -/
def fp6AddAsm : String :=
  framedDriver "bls12381_fp6_add_x86_from_lean" 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( callTri fp2AddSym "%rbx" c0 "%r12" c0 "%r13" c0
    ++ callTri fp2AddSym "%rbx" c1 "%r12" c1 "%r13" c1
    ++ callTri fp2AddSym "%rbx" c2 "%r12" c2 "%r13" c2 )

/-- `bls12381_fp6_sub_x86_from_lean(z, x, y)` = three `Fp2` subs. -/
def fp6SubAsm : String :=
  framedDriver "bls12381_fp6_sub_x86_from_lean" 8
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( callTri fp2SubSym "%rbx" c0 "%r12" c0 "%r13" c0
    ++ callTri fp2SubSym "%rbx" c1 "%r12" c1 "%r13" c1
    ++ callTri fp2SubSym "%rbx" c2 "%r12" c2 "%r13" c2 )

/-! ## 7. The `Fp12` multiply driver (exactly RELIC `fp12_mul_basic`)

`Fp12 = Fp6[w]/(w² − v)`; for `x = a₀ + a₁·w`, `y = b₀ + b₁·w`:

    t0 = a₀·b₀ ; t1 = a₁·b₁ ; t2 = b₀+b₁
    c₁ = a₀+a₁ ; c₁ = c₁·t2 ; c₁ = c₁−t0 ; c₁ = c₁−t1
    t1 = v·t1   (fp6_mul_art) ; c₀ = t0 + t1

3 `Fp6`-muls (= 54 `Fp`-muls) + one `fp6_mul_art` + Karatsuba `Fp6` add/subs.
Scratch `Fp6` felems (288 bytes each): `t0,t1,t2` (Karatsuba temporaries),
`r0,r1` (result coordinates, computed into scratch so the output may alias `x`
or `y`), and `zr` (a zeroed `Fp6` felem for the copy-out via `fp6_add`). 6 felems
= `1728` bytes; `+8 ⇒ 1736 ≡ 8 mod 16`. -/

def FT0 : Int := 0
def FT1 : Int := 288
def FT2 : Int := 576
def FR0 : Int := 864
def FR1 : Int := 1152
def FZR : Int := 1440   -- zeroed Fp6 felem for the copy-out

/-- `bls12381_fp12_mul_x86_from_lean(z, x, y)` over `Fp12 = Fp6[w]/(w²−v)`.
    Composes the owned `Fp6` mul + `Fp6` add/sub + `fp6_mul_art`; matches RELIC
    `fp12_mul_basic`. The two output coordinates are computed into scratch `Fp6`
    felems `r0,r1` and copied to `z` last, so `z` may alias `x`/`y`. Frame = 6
    `Fp6` felems = `1728`; `+8 ⇒ 1736`. -/
def fp12MulAsm : String :=
  framedDriver "bls12381_fp12_mul_x86_from_lean" 1736
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( -- zr = a₀ − a₀  (zeroed Fp6 felem, three Fp2 = six Fp subs)
      callTri fpSubSym "%rbp" (FZR+c0)         "%r12" (w0+c0)         "%r12" (w0+c0)
    ++ callTri fpSubSym "%rbp" (FZR+c0+imOff)  "%r12" (w0+c0+imOff)   "%r12" (w0+c0+imOff)
    ++ callTri fpSubSym "%rbp" (FZR+c1)         "%r12" (w0+c1)         "%r12" (w0+c1)
    ++ callTri fpSubSym "%rbp" (FZR+c1+imOff)  "%r12" (w0+c1+imOff)   "%r12" (w0+c1+imOff)
    ++ callTri fpSubSym "%rbp" (FZR+c2)         "%r12" (w0+c2)         "%r12" (w0+c2)
    ++ callTri fpSubSym "%rbp" (FZR+c2+imOff)  "%r12" (w0+c2+imOff)   "%r12" (w0+c2+imOff)
      -- t0 = a₀·b₀ ; t1 = a₁·b₁
    ++ callTri "bls12381_fp6_mul_x86_from_lean" "%rbp" FT0 "%r12" w0 "%r13" w0
    ++ callTri "bls12381_fp6_mul_x86_from_lean" "%rbp" FT1 "%r12" w1 "%r13" w1
      -- t2 = b₀+b₁ ; r1 = a₀+a₁ ; r1 = r1·t2 ; r1 -= t0 ; r1 -= t1   (= c₁)
    ++ callTri "bls12381_fp6_add_x86_from_lean" "%rbp" FT2 "%r13" w0 "%r13" w1
    ++ callTri "bls12381_fp6_add_x86_from_lean" "%rbp" FR1 "%r12" w0 "%r12" w1
    ++ callTri "bls12381_fp6_mul_x86_from_lean" "%rbp" FR1 "%rbp" FR1 "%rbp" FT2
    ++ callTri "bls12381_fp6_sub_x86_from_lean" "%rbp" FR1 "%rbp" FR1 "%rbp" FT0
    ++ callTri "bls12381_fp6_sub_x86_from_lean" "%rbp" FR1 "%rbp" FR1 "%rbp" FT1
      -- t2 = v·t1 (fp6_mul_art, alias-safe leaf) ; r0 = t0 + t2   (= c₀)
    ++ callBin fp6ArtSym "%rbp" FT2 "%rbp" FT1
    ++ callTri "bls12381_fp6_add_x86_from_lean" "%rbp" FR0 "%rbp" FT0 "%rbp" FT2
      -- copy r0 → z.c₀, r1 → z.c₁  (Fp6 add against the zero felem, alias-safe)
    ++ callTri "bls12381_fp6_add_x86_from_lean" "%rbx" w0 "%rbp" FR0 "%rbp" FZR
    ++ callTri "bls12381_fp6_add_x86_from_lean" "%rbx" w1 "%rbp" FR1 "%rbp" FZR )

/-! ## 8. Shape checks (real tower call graph, not a stub)

Substring / count helpers reused from the committed `Fp2` module's idiom. -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- Count occurrences of `needle` in `hay` (one hit per start index). -/
def countSub (hay needle : String) : Nat :=
  (List.range (hay.length + 1)).foldl
    (fun acc i =>
      if needle == String.ofList (hay.toList.drop i |>.take needle.length)
      then acc + 1 else acc) 0

/-- **The owned `Fp6` mul carries six real `Fp2`-multiply calls** (= 18 `Fp`-muls),
    the RELIC `fp6_mul_basic` call graph, plus two `fp2_mul_nor` (ξ) calls
    and the Karatsuba `Fp2` add/subs — not the 0–1-multiply stub the RELIC bench
    previously flagged. -/
theorem fp6MulAsm_six_real_fp2muls :
    countSub fp6MulAsm "callq bls12381_fp2_mul_x86_from_lean" = 6
      ∧ countSub fp6MulAsm "callq bls12381_fp2_mul_nor_x86_from_lean" = 2
      ∧ hasSub fp6MulAsm "callq bls12381_fp2_add_x86_from_lean"
      ∧ hasSub fp6MulAsm "callq bls12381_fp2_sub_x86_from_lean" := by native_decide

/-- **The owned `Fp12` mul carries three real `Fp6`-multiply calls** (= 54
    `Fp`-muls), the RELIC `fp12_mul_basic` call graph, plus one
    `fp6_mul_art` (mul-by-`v`) and the Karatsuba `Fp6` add/subs. -/
theorem fp12MulAsm_three_real_fp6muls :
    countSub fp12MulAsm "callq bls12381_fp6_mul_x86_from_lean" = 3
      ∧ countSub fp12MulAsm "callq bls12381_fp6_mul_art_x86_from_lean" = 1
      ∧ hasSub fp12MulAsm "callq bls12381_fp6_add_x86_from_lean"
      ∧ hasSub fp12MulAsm "callq bls12381_fp6_sub_x86_from_lean" := by native_decide

/-- The `Fp2` mul-by-ξ leaf is the `(1+u)` non-residue (one `Fp` add for the imag
    half `c₀+c₁`, one `Fp` sub for the real half `c₀−c₁`), matching RELIC
    `fp2_mul_nor_basic` case 3. -/
theorem fp2NorAsm_shape :
    countSub fp2NorAsm "callq bls12381_fp_add_x86_from_lean" = 1
      ∧ countSub fp2NorAsm "callq bls12381_fp_sub_x86_from_lean" = 1 := by native_decide

/-- The `Fp6` mul-by-`v` leaf carries the single ξ·a₂ non-residue call (the
    `v²·v = ξ` wrap). -/
theorem fp6ArtAsm_shape :
    countSub fp6ArtAsm "callq bls12381_fp2_mul_nor_x86_from_lean" = 1 := by native_decide

/-! ## 9. Emit driver -/

/-- Emit the owned `Fp2` add/sub/mul-by-ξ + `Fp6` mul-art/add/sub/mul + `Fp12` mul
    `.s` for the bench harness. The committed `Fp` mul/add/sub leaves and the
    committed `Fp2` mul driver are referenced read-only by the harness and are
    **not** re-emitted here. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_fp6_compare/gen_com"
  let g := "bench/bls12381_fp6_compare/gen_com/"
  IO.FS.writeFile (g ++ "bls12381_fp2_add_x86_from_lean.s")     fp2AddAsm
  IO.FS.writeFile (g ++ "bls12381_fp2_sub_x86_from_lean.s")     fp2SubAsm
  IO.FS.writeFile (g ++ "bls12381_fp2_mul_nor_x86_from_lean.s") fp2NorAsm
  IO.FS.writeFile (g ++ "bls12381_fp6_mul_art_x86_from_lean.s") fp6ArtAsm
  IO.FS.writeFile (g ++ "bls12381_fp6_add_x86_from_lean.s")     fp6AddAsm
  IO.FS.writeFile (g ++ "bls12381_fp6_sub_x86_from_lean.s")     fp6SubAsm
  IO.FS.writeFile (g ++ "bls12381_fp6_mul_x86_from_lean.s")     fp6MulAsm
  IO.FS.writeFile (g ++ "bls12381_fp12_mul_x86_from_lean.s")    fp12MulAsm
  IO.println "wrote gen_com/bls12381_fp2_{add,sub,mul_nor} + fp6_{mul_art,add,sub,mul} + fp12_mul .s (owned x86 backend, Fp6/Fp12 GT-field arithmetic over the committed Fp2 leaf)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel
