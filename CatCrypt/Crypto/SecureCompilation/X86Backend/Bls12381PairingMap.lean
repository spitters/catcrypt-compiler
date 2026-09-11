/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381FinalExp
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381FinalExp

/-!
# BLS12-381 owned `Fp` inverse + the full owned `pp_map` (#602 / #219)

**Variant: RELIC-transcribed (tests-only correctness).**

**STRING-TEMPLATED — not verified-compiler output:** the emitted
`bls12381_*_x86_from_lean.s` is assembled as literal asm-line text
(`framedDriver`/`renderLeafFn` join `movq`/`leaq`/`call` string literals), with
no `Com`/`Lprog` IR and no verified printer, so no theorem relates the emitted
bytes to a source; the byte-identity to RELIC below is the only corroboration.
See `bench/framework/AUDIT_EMIT_BYPASS.md` and `EMIT_PROVENANCE.md`
§"Which emit is verified?".

This owned `pp_map`
emit is hand-transcribed from the RELIC pairing reference and gated
**byte-identical to RELIC** (`pp_map_oatep`). RELIC is unverified C, so that
byte-identity is a **test**, not a correctness proof. The verified-correctness
BLS variant — owned emit whose denotation is tied to the **AUCurves** Rocq-proved
pairing via the rocqlean axiom bridge — is a **separate** artifact, kept distinct
from this one so the RELIC-transcribed and AUCurves-generated variants can be
compared.

The **last missing leaf** of the fully-owned BLS12-381 optimal-ate pairing
`pp_map = Miller-loop ∘ final-exp`: the constant-time `Fp` inverse.

The committed pieces (all owned, all KAT'd byte-identical to RELIC):

* `Fp`/`Fp2`/`Fp6`/`Fp12` add/sub/mul (`Bls12381Fp2MulKernel`,
  `Bls12381Fp6Fp12MulKernel`, commits 52dc486f / e8006039),
* `fp12_sqr_cyc` (commit 3c6fdd2a),
* the Miller-loop layer `pp_dbl_k12`/`pp_add_k12`/`fp12_mul_dxs`
  (`Bls12381Miller`),
* the final-exp Frobenius + cyclotomic conjugation `fp12_frb`/`fp12_inv_cyc`
  and the hard-part addition chain (`Bls12381FinalExp`),
* the AUCurves verified-CT Bernstein-Yang divstep `Fp` inverse leaf
  `bls12_invert_divstep_sat` (committed safegcd path, emitted through the
  verified front in `bench/bls12381_safegcd_compare/bls12381_safegcd_emit.lean`).

The one thing that did **not** yet exist was an owned `Fp` inverse over the
*Montgomery* felem layout the tower uses, which the final-exp **easy part**
`fp12_conv_cyc` (`f ↦ f^{(p⁶−1)(p²+1)}`) needs through
`fp12_inv → fp6_inv → fp2_inv → fp_inv`.

## The owned `Fp` inverse `fp_inv`

The divstep leaf computes a **plain** (non-Montgomery) modular inverse on
canonical `6×u64` little-endian input: `divstep(w) = w⁻¹ mod p`.  The owned
tower felem stores the Montgomery representative `A = a·R mod p`
(`R = 2³⁸⁴`).  Feeding the Montgomery limbs to the leaf gives

    divstep(A) = (a·R)⁻¹ = a⁻¹·R⁻¹  (mod p),

and the owned Montgomery multiply `mont_mul(x,y) = x·y·R⁻¹ mod p`.  Multiplying
by the constant `R³ mod p` corrects the representation back to Montgomery form:

    mont_mul(divstep(A), R³) = a⁻¹·R⁻¹ · R³ · R⁻¹ = a⁻¹·R,

which is exactly the Montgomery representative of `a⁻¹`.  So

    bls12381_fp_inv_x86_from_lean(z, x, r3):
        bls12_invert_divstep_sat(scratch, x)        # canonical (aR)⁻¹
        bls12381_mont_mul_x86_from_lean(z, scratch, r3)   # · R³  → a⁻¹R

The `R³ mod p` constant is **passed as a data pointer** (the harness computes it
from the curve prime via canonical GMP), so the driver is curve-config-agnostic
and byte-identical by construction — it bakes no constant table into the `.s`.
`z` may alias `x`: the divstep result lands in the `%rbp` scratch felem before
the Montgomery multiply reads `x`-free.

## The tower inverse and the easy part (composed over owned leaves)

`fp2_inv`, `fp6_inv`, `fp12_inv` are the standard norm-down formulas (RELIC
`relic_fpx_inv.c`), and the easy part `fp12_conv_cyc` is

    t = fp12_inv(a);  c = fp12_inv_cyc(a);  c = c·t;          # a^{p⁶−1}
    t = fp12_frb(c, 2);  c = c·t                              # c^{p²+1}

— composed over `{fp_inv, fp_mul, fp2_mul, fp2_mul_nor, fp6_mul, fp6_mul_art,
fp12_mul, fp12_inv_cyc, fp12_frb}`, all owned.  Following the committed hard-part
pattern (`o_pp_exp_hard`), the multi-level tower-inverse schedule is sequenced in
the bench harness at the granularity of the owned leaves, and each layer is
KAT'd byte-identical to RELIC (`fp_inv`, `fp2_inv`, `fp6_inv`, `fp12_inv`,
`fp12_conv_cyc`, `pp_exp_k12`) and a GMP oracle.

## Full owned `pp_map`

With the easy part owned, the **full** `pp_exp` (easy ∘ hard) runs owned, and

    pp_map(P, Q) = pp_exp( [x<0] inv_cyc( pp_mil(P, Q) ) )

composes the (committed, KAT'd) owned Miller loop with the now-complete owned
final exponentiation.  The bench gate KATs the owned `pp_map(P,Q)` byte-identical
to RELIC `pp_map_oatep` over random `G1 × G2` — the fully-owned BLS12-381 pairing.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381PairingMap

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel

/-! ## 0. Owned-leaf symbol names -/

/-- The AUCurves verified-CT Bernstein-Yang divstep `Fp` inverse leaf
    (committed safegcd path). Plain (non-Montgomery) inverse on canonical
    `6×u64` LE limbs. Signature `bls12_invert_divstep_sat(out, x)`. -/
def divstepSym : String := "bls12_invert_divstep_sat"
/-- The committed owned Montgomery multiply leaf (`mont_mul(z,x,y)=xyR⁻¹`). -/
def montMulSym : String := "bls12381_mont_mul_x86_from_lean"
/-- The owned `Fp` inverse driver emitted here. -/
def fpInvSym : String := "bls12381_fp_inv_x86_from_lean"

/-! ## 1. The owned `Fp` inverse driver

`bls12381_fp_inv_x86_from_lean(z, x, r3)`:

1. `bls12_invert_divstep_sat(scratch, x)` — canonical inverse of the Montgomery
   limbs `x = a·R`, i.e. `scratch = (a·R)⁻¹ = a⁻¹·R⁻¹ mod p`.
2. `bls12381_mont_mul_x86_from_lean(z, scratch, r3)` — `z = scratch·R³·R⁻¹ =
   a⁻¹·R`, the Montgomery representative of `a⁻¹`.

`r3` (= `R³ mod p`, 6×u64) is held in `%r14`; the scratch felem in the `%rbp`
frame (one `Fp` = 48 bytes; `48 + 8 = 56 ≡ 8 mod 16`). `z`/`x` held in
`%rbx`/`%r12`. The divstep result is materialised in scratch before the
Montgomery multiply, so `z` may alias `x`. -/

/-- byte offset of the scratch `Fp` felem (the canonical inverse). -/
def IS : Int := 0

/-- `bls12381_fp_inv_x86_from_lean(z, x, r3)` = Montgomery `Fp` inverse via the
    divstep leaf + an `R³` Montgomery correction. -/
def fpInvAsm : String :=
  framedDriver fpInvSym 56
    [ "\tmovq %rdi, %rbx", "\tmovq %rsi, %r12", "\tmovq %rdx, %r14" ]
    ( -- scratch = divstep(x) = (aR)⁻¹    (2-pointer leaf: out=rdi, x=rsi)
      [ lea IS "%rbp" "%rdi", lea 0 "%r12" "%rsi", "\tcallq " ++ divstepSym ]
      -- z = mont_mul(scratch, r3) = a⁻¹R
    ++ callTri montMulSym "%rbx" 0 "%rbp" IS "%r14" 0 )

/-! ## 2. Shape checks (real leaf call graph, not a stub) -/

/-- The owned `fp_inv` calls the divstep leaf exactly once and the Montgomery
    multiply exactly once — the `divstep`-then-`·R³` correction. -/
theorem fpInvAsm_calls :
    countSub fpInvAsm ("callq " ++ divstepSym) = 1
      ∧ countSub fpInvAsm ("callq " ++ montMulSym) = 1 := by native_decide

/-- The driver exports under its owned symbol and forms three reg-ptr arguments
    (the `%r14` correction-constant base is loaded in the prologue). -/
theorem fpInvAsm_export :
    hasSub fpInvAsm (".globl " ++ fpInvSym)
      ∧ hasSub fpInvAsm "movq %rdx, %r14" := by native_decide

/-! ## 3. In-Lean value pin (Montgomery-correction model vs reference)

We re-run the driver's two-step schedule abstractly over a tiny prime field
`𝔽ₚ` with a chosen "R" to surface the representation correction: feeding the
Montgomery representative `aR` to a plain inverse yields `(aR)⁻¹`, and the
`mont_mul(·, R³)` step recovers `a⁻¹R`. This pins the *representation algebra*
of the driver (the class of bug where the wrong `R`-power constant is used);
the field-element value correctness vs RELIC is the external KAT. -/

namespace InvModel

/-- A small prime for the model (representation algebra only). -/
def pp : Int := 1000003
def md (x : Int) : Int := ((x % pp) + pp) % pp
/-- model "R" (any unit mod pp); 2¹⁰ here. -/
def Rm : Int := 1024

/-- modular inverse via Fermat (pp prime). -/
def inv (x : Int) : Int := Id.run do
  let mut r := 1
  let mut b := md x
  let mut e := pp - 2
  while e > 0 do
    if e % 2 == 1 then r := md (r * b)
    b := md (b * b)
    e := e / 2
  return r

/-- Montgomery multiply on residues: `x·y·R⁻¹`. -/
def mont (x y : Int) : Int := md (md (x * y) * inv Rm)

/-- The driver's schedule: `mont(divstep(aR), R³)` where `divstep = plain inv`. -/
def fpInvModel (aR : Int) : Int := mont (inv aR) (md (Rm * Rm * Rm))

/-- Reference: the Montgomery representative of `a⁻¹` is `a⁻¹·R`. -/
def fpInvRef (a : Int) : Int := md (inv a * Rm)

/-- Over a sweep of `a`, the driver schedule on `aR` equals `a⁻¹R`. -/
def matchesAll : Bool :=
  (List.range 50).all (fun n =>
    let a := md (Int.ofNat n + 2)        -- nonzero residues
    fpInvModel (md (a * Rm)) == fpInvRef a)

end InvModel

/-- **Value pin (`fp_inv` Montgomery correction)**: feeding the Montgomery
    representative `a·R` to the plain divstep inverse and correcting by
    `mont(·, R³)` yields `a⁻¹·R`, the Montgomery representative of `a⁻¹`, for a
    sweep of nonzero residues. -/
theorem fpInv_value_pin : InvModel.matchesAll = true := by native_decide

/-! ## 4. Emit driver -/

/-- Emit the owned `Fp` inverse `.s` for the `pp_map` bench harness. The
    committed lower-tier leaves (divstep, mont_mul, the `Fp`/`Fp2`/`Fp6`/`Fp12`
    tower) are referenced read-only and not re-emitted. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_ppmap_compare/gen_com"
  let g := "bench/bls12381_ppmap_compare/gen_com/"
  IO.FS.writeFile (g ++ "bls12381_fp_inv_x86_from_lean.s") fpInvAsm
  IO.println "wrote gen_com/bls12381_fp_inv_x86_from_lean.s (owned Fp inverse: AUCurves divstep leaf + R^3 Montgomery correction over the committed mont_mul)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381PairingMap
