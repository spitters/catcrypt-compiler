/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel

/-!
# BLS12-381 G2 (E'/Fp2) projective group law, owned x86 backend (Miller prerequisite)

**TEST/BENCH-ONLY — STRING-TEMPLATED, not verified-compiler output.** The
emitted `bench/bls12381_g2_compare/gen_com/bls12381_g2_{add,dbl}.s` and
`bls12381_fp2_{add,sub,dbl,copy}_x86_from_lean.s` are assembled as text
(`renderLeafFn` wrapping hand-written prologue / `callFp`/`c2`/`c3`/`mul3` body
line lists / epilogue joined with `++`), with no single verified-printer descent
for the whole file. The `native_decide` shape checks are `countSub`/`hasSub`
substring assertions. The composed `Fp` add/sub leaves are `runBlock`-verified
in `Bls12381Fp2MulKernel` and the `Fp` mul is the #490 CIOS kernel (block
model); the `Fp2`/`G2` drivers here are hand-written SysV call-frame
scaffolding. It is a bench/interop reference. The verified emit path is the
FRONT-SOURCED descent; see `bench/framework/AUDIT_EMIT_BYPASS.md` and
`EMIT_PROVENANCE.md` §"Which emit is verified?".

**Variant: RELIC-transcribed (tests-only correctness).** This owned x86 emit is
hand-transcribed from the RELIC pairing reference and gated **byte-identical to
RELIC**. RELIC is unverified C, so that byte-identity is a **test**, not a
correctness proof. The verified-correctness BLS variant — owned emit whose
denotation is tied to the **AUCurves** Rocq-proved pairing via the rocqlean
axiom bridge — is a **separate** artifact, kept distinct from this one so the
RELIC-transcribed and AUCurves-generated variants can be compared.

`G2` is the order-`r` subgroup of the **sextic twist** `E'/Fp2`:
`y² = x³ + b'` with `b' = 4(1 + u)` (the twist constant RELIC loads for
BLS12-381). A point is three `Fp2` coordinates `(X, Y, Z)` in *homogeneous
projective* form — each `Fp2` is the contiguous 12×u64 `[re, im]` Montgomery
layout of `Bls12381Fp2MulKernel`. The Miller loop walks the BLS `x`-NAF doing a
`G2` doubling per bit and a `G2` addition per nonzero digit (plus a line eval),
so the `G2` group law is the first Miller-loop prerequisite and is
*independently* KAT-able against RELIC `ep2_add_projc` / `ep2_dbl_projc`.

This module emits `bls12381_g2_add` and `bls12381_g2_dbl` as **owned drivers**
that *compose* the committed owned `Fp2` leaves (`Bls12381Fp2MulKernel`):

* `bls12381_fp2_mul_x86_from_lean` (#602, Karatsuba, 3 real `Fp`-muls);
* `bls12381_fp2_sqr_x86_from_lean` (#602, complex squaring, 2 real `Fp`-muls);
* the `Fp` add/sub leaves it emits (`bls12381_fp_add/sub_x86_from_lean`);

and the `Fp2` add / sub / dbl / copy drivers emitted *here* (each `Fp2` add/sub
is two `Fp` add/sub on the `re`/`im` halves; `Fp2` dbl is `Fp2` add of a value
to itself; `Fp2` copy is a 12×u64 move). Multiply-by-`b'` is realised as an
`Fp2` multiply by the runtime `b'` constant (the caller passes RELIC's loaded
`ep2_b`), so the emitted code is byte-identical to RELIC's `ep2_curve_mul_b`
whatever twist constant the linked RELIC build actually loaded — no hardcoded
`b'`.

## The formulas (Renes–Costello–Batina, `a = 0` branch)

RELIC's `ep2_{add,dbl}_projc` for BLS12-381 take the `opt_a == RLC_ZERO`
branch of the complete RCB formulas (`src/tmpl/relic_ep_{add,dbl}_tmpl.h`,
eprint 2015/1060). We replicate that **exact instruction schedule** over the
owned `Fp2` leaves.

### `g2_add` (12 `fp2_mul` + 2 `fp2_mul`-by-`b'` + 19 `fp2_{add,sub,dbl}`)

    t0 = X1·X2          t1 = Y1·Y2          t2 = Z1·Z2
    t3 = X1+Y1          t4 = X2+Y2          t3 = t3·t4
    t4 = t0+t1          t3 = t3−t4
    t4 = Y1+Z1          t5 = Y2+Z2          t4 = t4·t5
    t5 = t1+t2          t4 = t4−t5
    Ry = X2+Z2          Rx = X1+Z1          Rx = Rx·Ry
    Ry = t0+t2          Ry = Rx−Ry
    Rx = 2·t0           t0 = t0+Rx
    t5 = 2·t2           t2 = t2+t5          t2 = b'·t2
    Rz = t1+t2          t1 = t1−t2
    t5 = 2·Ry           Ry = Ry+t5          Ry = b'·Ry
    Rx = t4·Ry          t2 = t3·t1          Rx = t2−Rx
    Ry = t0·Ry          t1 = t1·Rz          Ry = t1+Ry
    t0 = t0·t3          Rz = Rz·t4          Rz = Rz+t0

### `g2_dbl` (6 `fp2_mul` + 2 `fp2_sqr` + 1 `fp2_mul`-by-`b'` + 9 `fp2_{add,sub,dbl}`)

The non-BASIC (`Z ≠ 1`) RCB doubling for `a = 0` (`Z1 = p->z`):

    t0 = Y²             t3 = X·Y
    t1 = Y·Z            t2 = Z²
    t5 = 2·t2           t5 = t5+t2          t2 = b'·t5     (= 3b'·Z²)
    Rz = 2·t0           Rz = 2·Rz           Rz = 2·Rz      (= 8·Y²)
    Rx = t2·Rz          Ry = t0+t2
    Rz = t1·Rz
    t1 = 2·t2           t2 = t1+t2          t0 = t0−t2     (= Y² − 9b'Z²)
    Ry = t0·Ry          Ry = Rx+Ry
    Rx = t0·t3          Rx = 2·Rx

`fp2_sqr` covers `t0 = Y²` and `t2 = Z²`. The by-`b'` step is `fp2_mul` by the
runtime `b'` operand.

## Scope

This is the `G2` group-law **leaf** toward the Miller loop. The bodies of the
`Fp` add/sub leaves are `runBlock`-verified (`Bls12381Fp2MulKernel`); the `Fp`
mul is the committed #490 CIOS kernel. The `Fp2`/`G2` **drivers** are trusted
SysV call-frame scaffolding over those leaves (same status as the committed
`Fp2` mul/sqr drivers — a driver makes `call`s, so it is not a leaf). Value
correctness is the external KAT (`bench/bls12381_g2_compare`) against RELIC
`ep2_add_projc` / `ep2_dbl_projc` and a GMP canonical RCB oracle.

The remaining Miller-loop layers are still gapped and *not* claimed here:
the **line-function evaluation** (sparse `Fp12`), the **`x`-NAF driver**, and
the **final exponentiation** (`Fp12` cyclotomic). This module delivers only the
`G2` doubling + addition that the Miller loop iterates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381G2

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel (callFp)

/-! ## 1. Names of the composed owned leaves -/

def fp2Mul : String := "bls12381_fp2_mul_x86_from_lean"
def fp2Sqr : String := "bls12381_fp2_sqr_x86_from_lean"
def fpAdd  : String := "bls12381_fp_add_x86_from_lean"
def fpSub  : String := "bls12381_fp_sub_x86_from_lean"
def fp2Add  : String := "bls12381_fp2_add_x86_from_lean"
def fp2Sub  : String := "bls12381_fp2_sub_x86_from_lean"
def fp2Dbl  : String := "bls12381_fp2_dbl_x86_from_lean"
def fp2Copy : String := "bls12381_fp2_copy_x86_from_lean"

/-! ## 2. `Fp2` add / sub / dbl / copy drivers (componentwise over `re`/`im`)

An `Fp2 = a + b·u` is the 12×u64 `[re(6), im(6)]` layout: `re` at byte offset
`0`, `im` at byte offset `48`. `Fp2` add/sub are *componentwise* `Fp` add/sub;
`Fp2` dbl is `Fp2` add of a value to itself; `Fp2` copy is a 12×u64 move. -/

/-- `bls12381_fp2_add_x86_from_lean(z, x, y)`: `z = x + y`. -/
def fp2AddAsm : String :=
  renderLeafFn fp2Add
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"
    , "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( callFp fpAdd "%rbx" 0  "%r12" 0  "%r13" 0
    ++ callFp fpAdd "%rbx" 48 "%r12" 48 "%r13" 48 )
    [ "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- `bls12381_fp2_sub_x86_from_lean(z, x, y)`: `z = x − y`. -/
def fp2SubAsm : String :=
  renderLeafFn fp2Sub
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"
    , "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13" ]
    ( callFp fpSub "%rbx" 0  "%r12" 0  "%r13" 0
    ++ callFp fpSub "%rbx" 48 "%r12" 48 "%r13" 48 )
    [ "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- `bls12381_fp2_dbl_x86_from_lean(z, x)`: `z = x + x`. -/
def fp2DblAsm : String :=
  renderLeafFn fp2Dbl
    [ "\tpushq %rbx", "\tpushq %r12"
    , "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12" ]
    ( callFp fpAdd "%rbx" 0  "%r12" 0  "%r12" 0
    ++ callFp fpAdd "%rbx" 48 "%r12" 48 "%r12" 48 )
    [ "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- `bls12381_fp2_copy_x86_from_lean(z, x)`: 12×u64 move (`z := x`). A leaf, so
    no callee-saved spills are needed; `%rax`/`%rcx` are scratch. -/
def fp2CopyAsm : String :=
  let mov (o : Nat) : List String :=
    [ "\tmovq " ++ toString o ++ "(%rsi), %rax", "\tmovq %rax, " ++ toString o ++ "(%rdi)" ]
  renderLeafFn fp2Copy []
    ((List.range 12).flatMap (fun i => mov (8 * i)))
    [ "\tret" ]

/-! ## 3. The `G2` add / dbl drivers (RCB `a = 0` schedule over `Fp2` leaves)

The drivers carry a stack frame holding the RCB temporaries as `Fp2` felems
(96 bytes each) plus the three working result coordinates `Rx,Ry,Rz`; the
output is assembled in scratch and copied to `r` last (robust against
output/input aliasing). Point bases live in callee-saved registers across the
`call`s; each `Fp2` operand pointer is recomputed with `leaq base+off`.

Coordinate byte offsets within an `ep2_st` (`{X:Fp2, Y:Fp2, Z:Fp2, coord}`):
`X = 0`, `Y = 96`, `Z = 192`. `b'` is its own pointer argument so multiply-by-`b'`
is a plain `fp2_mul`. -/

def oX : Int := 0
def oY : Int := 96
def oZ : Int := 192

def fT0 : Int := 0
def fT1 : Int := 96
def fT2 : Int := 192
def fT3 : Int := 288
def fT4 : Int := 384
def fT5 : Int := 480
def fRx : Int := 576
def fRy : Int := 672
def fRz : Int := 768
/-- A dedicated scratch felem for the *non-aliasing* multiply (`mul3`). -/
def fS  : Int := 864

/-- `call leaf(z, x, y)` over three `Fp2` (base,offset) operands. -/
def c3 (leaf zb : String) (zo : Int) (xb : String) (xo : Int) (yb : String) (yo : Int) : List String :=
  callFp leaf zb zo xb xo yb yo

/-- `call leaf(z, x)` (two-operand: `fp2_sqr` / `fp2_dbl` / `fp2_copy`). -/
def c2 (leaf zb : String) (zo : Int) (xb : String) (xo : Int) : List String :=
  [ "\tleaq " ++ toString zo ++ "(" ++ zb ++ "), %rdi"
  , "\tleaq " ++ toString xo ++ "(" ++ xb ++ "), %rsi"
  , "\tcallq " ++ leaf ]

/-- **Non-aliasing `Fp2` multiply** into a (base,offset) destination. The
    committed `fp2_mul` driver requires the output not alias either input (it
    stages `a+b`/`c+d` into the output halves before the third Karatsuba mul).
    The RCB schedules below freely reuse a temporary as both an operand and the
    product (`t3 = t3·t4`, `t2 = b'·t2`, …), so we always compute the product
    into the dedicated frame scratch `fS` and copy it to `z` — unconditionally
    alias-safe at the cost of one 12×u64 copy per multiply. -/
def mul3 (F : String) (zb : String) (zo : Int) (xb : String) (xo : Int) (yb : String) (yo : Int) : List String :=
  c3 fp2Mul F fS xb xo yb yo ++ c2 fp2Copy zb zo F fS

/-- `bls12381_g2_add(r, p, q, b')`: projective `G2` addition, RCB `a = 0`.

    Args `%rdi=r`, `%rsi=p`, `%rdx=q`, `%rcx=b'` (`Fp2` twist constant). Saved
    bases `%rbx=r`, `%r12=p`, `%r13=q`, `%r14=b'`; frame `%rbp`. -/
def g2AddAsm : String :=
  let P := "%r12"; let Q := "%r13"; let B := "%r14"; let F := "%rbp"; let R := "%rbx"
  renderLeafFn "bls12381_g2_add"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $976, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r13", "\tmovq %rcx, %r14" ]
    ( mul3 F F fT0 P oX Q oX
    ++ mul3 F F fT1 P oY Q oY
    ++ mul3 F F fT2 P oZ Q oZ
    ++ c3 fp2Add F fT3 P oX P oY
    ++ c3 fp2Add F fT4 Q oX Q oY
    ++ mul3 F F fT3 F fT3 F fT4
    ++ c3 fp2Add F fT4 F fT0 F fT1
    ++ c3 fp2Sub F fT3 F fT3 F fT4
    ++ c3 fp2Add F fT4 P oY P oZ
    ++ c3 fp2Add F fT5 Q oY Q oZ
    ++ mul3 F F fT4 F fT4 F fT5
    ++ c3 fp2Add F fT5 F fT1 F fT2
    ++ c3 fp2Sub F fT4 F fT4 F fT5
    ++ c3 fp2Add F fRy Q oX Q oZ
    ++ c3 fp2Add F fRx P oX P oZ
    ++ mul3 F F fRx F fRx F fRy
    ++ c3 fp2Add F fRy F fT0 F fT2
    ++ c3 fp2Sub F fRy F fRx F fRy
    ++ c2 fp2Dbl F fRx F fT0
    ++ c3 fp2Add F fT0 F fT0 F fRx
    ++ c2 fp2Dbl F fT5 F fT2
    ++ c3 fp2Add F fT2 F fT2 F fT5
    ++ mul3 F F fT2 B 0    F fT2
    ++ c3 fp2Add F fRz F fT1 F fT2
    ++ c3 fp2Sub F fT1 F fT1 F fT2
    ++ c2 fp2Dbl F fT5 F fRy
    ++ c3 fp2Add F fRy F fRy F fT5
    ++ mul3 F F fRy B 0    F fRy
    ++ mul3 F F fRx F fT4 F fRy
    ++ mul3 F F fT2 F fT3 F fT1
    ++ c3 fp2Sub F fRx F fT2 F fRx
    ++ mul3 F F fRy F fT0 F fRy
    ++ mul3 F F fT1 F fT1 F fRz
    ++ c3 fp2Add F fRy F fT1 F fRy
    ++ mul3 F F fT0 F fT0 F fT3
    ++ mul3 F F fRz F fRz F fT4
    ++ c3 fp2Add F fRz F fRz F fT0
    -- copy Rx,Ry,Rz -> r.X,r.Y,r.Z
    ++ c2 fp2Copy R oX F fRx
    ++ c2 fp2Copy R oY F fRy
    ++ c2 fp2Copy R oZ F fRz )
    [ "\taddq $976, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- `bls12381_g2_dbl(r, p, b')`: projective `G2` doubling, RCB `a = 0`,
    non-BASIC (`Z ≠ 1`).

    Args `%rdi=r`, `%rsi=p`, `%rdx=b'`. Saved bases `%rbx=r`, `%r12=p`,
    `%r14=b'`; frame `%rbp`. -/
def g2DblAsm : String :=
  let P := "%r12"; let B := "%r14"; let F := "%rbp"; let R := "%rbx"
  renderLeafFn "bls12381_g2_dbl"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $976, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r14" ]
    ( -- t0 = Y² ; t3 = X·Y ; t1 = Y·Z ; t2 = Z²
      c2 fp2Sqr F fT0 P oY
    ++ mul3 F F fT3 P oX P oY
    ++ mul3 F F fT1 P oY P oZ
    ++ c2 fp2Sqr F fT2 P oZ
      -- t5 = 2·t2 ; t5 = t5+t2 ; t2 = b'·t5   (= 3b'·Z²)
    ++ c2 fp2Dbl F fT5 F fT2
    ++ c3 fp2Add F fT5 F fT5 F fT2
    ++ mul3 F F fT2 B 0    F fT5
      -- Rz = 2·t0 ; Rz = 2·Rz ; Rz = 2·Rz     (= 8·Y²)
    ++ c2 fp2Dbl F fRz F fT0
    ++ c2 fp2Dbl F fRz F fRz
    ++ c2 fp2Dbl F fRz F fRz
      -- Rx = t2·Rz ; Ry = t0+t2 ; Rz = t1·Rz
    ++ mul3 F F fRx F fT2 F fRz
    ++ c3 fp2Add F fRy F fT0 F fT2
    ++ mul3 F F fRz F fT1 F fRz
      -- t1 = 2·t2 ; t2 = t1+t2 ; t0 = t0−t2   (= Y² − 9b'Z²)
    ++ c2 fp2Dbl F fT1 F fT2
    ++ c3 fp2Add F fT2 F fT1 F fT2
    ++ c3 fp2Sub F fT0 F fT0 F fT2
      -- Ry = t0·Ry ; Ry = Rx+Ry
    ++ mul3 F F fRy F fT0 F fRy
    ++ c3 fp2Add F fRy F fRx F fRy
      -- Rx = t0·t3 ; Rx = 2·Rx
    ++ mul3 F F fRx F fT0 F fT3
    ++ c2 fp2Dbl F fRx F fRx
      -- copy Rx,Ry,Rz -> r.X,r.Y,r.Z
    ++ c2 fp2Copy R oX F fRx
    ++ c2 fp2Copy R oY F fRy
    ++ c2 fp2Copy R oZ F fRz )
    [ "\taddq $976, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-! ## 4. Shape checks (the composed `Fp2`-op call counts) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel (countSub hasSub)

/-- `g2_add` composes the RCB `a=0` schedule: **14 `fp2_mul` calls** (12 generic
    products + 2 by-`b'`), no `fp2_sqr`, and the documented `fp2_{add,sub,dbl}`
    mix. Each multiply is staged through the non-aliasing scratch (`mul3`),
    contributing one `fp2_copy`; with the three final output-coordinate writes
    that is `14 + 3 = 17` `fp2_copy` calls. -/
theorem g2AddAsm_op_counts :
    countSub g2AddAsm ("callq " ++ fp2Mul) = 14
      ∧ countSub g2AddAsm ("callq " ++ fp2Sqr) = 0
      ∧ countSub g2AddAsm ("callq " ++ fp2Copy) = 17
      ∧ hasSub g2AddAsm ("callq " ++ fp2Add)
      ∧ hasSub g2AddAsm ("callq " ++ fp2Sub)
      ∧ hasSub g2AddAsm ("callq " ++ fp2Dbl) := by native_decide

/-- `g2_dbl` composes the RCB `a=0` doubling: **6 `fp2_mul` + 2 `fp2_sqr`**
    (`Y²`, `Z²`) plus one by-`b'` (also a `fp2_mul`, so 7 `fp2_mul` total), the
    `fp2_{add,sub,dbl}` mix, and `7 + 3 = 10` `fp2_copy` calls (one per `mul3`
    plus three final output-coordinate writes). -/
theorem g2DblAsm_op_counts :
    countSub g2DblAsm ("callq " ++ fp2Mul) = 7
      ∧ countSub g2DblAsm ("callq " ++ fp2Sqr) = 2
      ∧ countSub g2DblAsm ("callq " ++ fp2Copy) = 10
      ∧ hasSub g2DblAsm ("callq " ++ fp2Add)
      ∧ hasSub g2DblAsm ("callq " ++ fp2Sub)
      ∧ hasSub g2DblAsm ("callq " ++ fp2Dbl) := by native_decide

/-! ## 5. Emit driver -/

/-- Emit the owned `Fp2` add/sub/dbl/copy drivers and the `G2` add/dbl drivers
    for the bench harness. The committed `Fp` mul/add/sub and `Fp2` mul/sqr
    leaves are referenced read-only (emitted by `Bls12381Fp2MulKernel` and #490). -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_g2_compare/gen_com"
  IO.FS.writeFile "bench/bls12381_g2_compare/gen_com/bls12381_fp2_add_x86_from_lean.s"  fp2AddAsm
  IO.FS.writeFile "bench/bls12381_g2_compare/gen_com/bls12381_fp2_sub_x86_from_lean.s"  fp2SubAsm
  IO.FS.writeFile "bench/bls12381_g2_compare/gen_com/bls12381_fp2_dbl_x86_from_lean.s"  fp2DblAsm
  IO.FS.writeFile "bench/bls12381_g2_compare/gen_com/bls12381_fp2_copy_x86_from_lean.s" fp2CopyAsm
  IO.FS.writeFile "bench/bls12381_g2_compare/gen_com/bls12381_g2_add.s"                 g2AddAsm
  IO.FS.writeFile "bench/bls12381_g2_compare/gen_com/bls12381_g2_dbl.s"                 g2DblAsm
  IO.println "wrote gen_com/bls12381_fp2_{add,sub,dbl,copy}_x86_from_lean.s + bls12381_g2_{add,dbl}.s (owned x86 backend, G2 group law over verified Fp2 leaves)"

/-! ## Artifact generation at elaboration

The renders are written while this module elaborates, so `lake` produces them
from this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381G2
