/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public meta import CatCrypt.Crypto.Primitives.GF128
public import CatCrypt.Crypto.Primitives.GF128

/-!
# GHASH GF(2¹²⁸) multiply on the high `catCryptDialect`

This is the GF(2¹²⁸) sibling of `AesRoundCatCryptEmit.lean` (which routed the
AES GF(2⁸) `xtime`/`mul3` multiply through the high `catCryptDialect`). Here the
field is GF(2¹²⁸) = `𝔽₂[x] / (x¹²⁸+x⁷+x²+x+1)` — the GHASH/GCM field
(NIST SP 800-38D, Algorithm 1), with the reduction polynomial in bit-reflected
form `R = 0xE1000…00` (`GF128.gf128R`). The committed spec is the bit-serial
shift–XOR–reduce loop `GF128.gf128_mul`, whose single iteration is
`GF128.gf128_step`.

## The capability — MLIR / prime-IR aligned, no new op

GHASH's `x·H` over GF(2¹²⁸) is the bit-serial *Russian-peasant* multiply: for
each bit of one operand, conditionally XOR the running value into the
accumulator, then shift the running value right one and conditionally reduce by
`R` when the bit shifted out (the low bit, in the bit-reflected MSB-first GCM
convention) was set. That is exactly `GF128.gf128_step`:

```
z' = if xi             then z ⊕ v          else z
v' = if v.getLsbD 0    then (v ≫ 1) ⊕ R    else (v ≫ 1)
```

Both conditionals are made **branch-free** out of the high dialect's existing
word alphabet — exactly as the AES file did for the GF(2⁸) `xtime`:

```
z' = z ⊕ (mask(xi)          ∧ v)
v' = (v ≫ 1) ⊕ (mask(v₀)    ∧ R)
```

where `mask(c)` is the all-ones-or-zero `BitVec 128` of a `Bool` `c`, built by
the dialect's `bitToSword 128` (the LLVM `(0 - sext(c)) : i128` mask). Every op
is one of `bvXor 128`, `bvShiftR 128 1`, `bvAnd 128`, `bvConst 128`,
`bitToSword 128`, already in `CatCryptOp`. No new `CatCryptOp` constructor is
introduced — the GF(2¹²⁸) capability is added to the high dialect *additively*,
mirroring the GF(2⁸) approach.

## Components, each `denote = spec`

* `accStepW` / `valStepW` — the branch-free `BitVec 128` waists of the two
  `gf128_step` outputs, proved equal to `GF128.gf128_step` (`bv_decide`).
* `accStepCom` — the accumulator update `z ⊕ (mask(xi) ∧ v)` as a straight-line
  `Com catCryptDialect`, `denote = (gf128_step z v xi).1`.
* `valStepCom` — the running-value update `(v ≫ 1) ⊕ (mask(v₀) ∧ R)` as a
  `Com catCryptDialect`, `denote = (gf128_step z v xi).2`.

`gf128_mul` is the 128-fold `Fin.foldl` of `gf128_step`; the load-bearing
deliverable is the single-step GF(2¹²⁸) multiply structure through the high
dialect (the per-bit shift–XOR–reduce is the only non-ALU-trivial part of
GHASH), exactly as `AesRoundCatCryptEmit` delivered the GF(2⁸) single-multiply
`xtime`/`mul3` rather than a 128-step unrolling. `gf128_mul` is then the
straight-line composition (`Fin.foldl`) of these per-bit kernels.

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.GhashGf128CatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Primitives.GF128

/-! ## 0. The block dialect type

GHASH blocks are `BitVec 128` in the dialect. The committed GF(2¹²⁸) spec
(`CatCrypt.Crypto.Primitives.GF128`) is already over `BitVec 128`, so no
`UInt` ↔ `BitVec` bridge is needed (unlike the AES byte case). -/

/-- The GHASH block dialect type. -/
abbrev T128 : CryptoTy := .sword 128

/-! ## 1. The GF(2¹²⁸) `gf128_step` outputs as branch-free `BitVec 128` waists

`accStepW`/`valStepW` are the *exact* branch-free functions the dialect ops
denote to. They replace `gf128_step`'s two `if`s by all-ones/zero masks:
`mask(c) = if c then allOnes else 0`. -/

/-- All-ones-or-zero `BitVec 128` mask of a `Bool` (the `bitToSword 128` value).
    `mask c = if c then allOnes else 0`. -/
def mask128 (c : Bool) : BitVec 128 := if c then BitVec.allOnes 128 else 0

/-- Branch-free accumulator update: `z ⊕ (mask(xi) ∧ v)`. Equals
    `(gf128_step z v xi).1 = if xi then z ⊕ v else z`. -/
def accStepW (z v : BitVec 128) (xi : Bool) : BitVec 128 :=
  z ^^^ (mask128 xi &&& v)

/-- Branch-free running-value update: `(v ≫ 1) ⊕ (mask(v₀) ∧ R)`. Equals
    `(gf128_step z v xi).2 = if v.getLsbD 0 then (v ≫ 1) ⊕ R else v ≫ 1`. -/
def valStepW (v : BitVec 128) : BitVec 128 :=
  (BitVec.ushiftRight v 1) ^^^ (mask128 (v.getLsbD 0) &&& gf128R)

/-- **`accStepW` is `(gf128_step _ _ _).1`** — the branch-free conditional XOR
    equals the spec's `if xi` branch. -/
theorem accStepW_eq_spec (z v : BitVec 128) (xi : Bool) :
    (gf128_step z v xi).1 = accStepW z v xi := by
  unfold gf128_step accStepW mask128
  cases xi <;> bv_decide

/-- **`valStepW` is `(gf128_step _ _ _).2`** — the branch-free conditional reduce
    equals the spec's `if v.getLsbD 0` branch. The running value is independent
    of `z`/`xi`. -/
theorem valStepW_eq_spec (z v : BitVec 128) (xi : Bool) :
    (gf128_step z v xi).2 = valStepW v := by
  unfold gf128_step valStepW mask128
  by_cases h : v.getLsbD 0 <;> simp [h] <;> bv_decide

/-! ## 2. Single-binding `denote` peel step lemmas (each `rfl`)

The `BitVec 128` analogues of `AesRoundCatCryptEmit.denote_var_bvXor` etc. Each
peels one `Com.var` binding to `body.denote (V.extend (waist …))`, the waist a
`BitVec 128`-valued function so `Ctxt.Valuation.extend` infers the bound type.
The ops used are `bvShiftR 128 1`, `bvAnd 128`, `bvXor 128`, `bvConst 128`,
`bitToSword 128`. -/

/-- `bvShiftR 128 1` waist (logical right shift by one). -/
def shr1W (a : BitVec 128) : BitVec 128 := BitVec.ushiftRight a 1
/-- `bvAnd 128` waist. -/
def andW (a b : BitVec 128) : BitVec 128 := a &&& b
/-- `bvXor 128` waist. -/
def xorW (a b : BitVec 128) : BitVec 128 := a ^^^ b
/-- `bitToSword 128` waist (`mask128`). -/
def maskW (c : Bool) : BitVec 128 := if c then BitVec.allOnes 128 else 0

/-- Peel one `bvConst 128 c` binding. -/
theorem denote_var_bvConst {Γ : Ctxt catCryptDialect} {s : CryptoTy} (c : BitVec 128)
    (body : Com catCryptDialect (CryptoTy.sword 128 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvConst 128 c) rfl .nil) body).denote V
      = body.denote (V.extend c) := rfl

/-- Peel one `bvShiftR 128 1` binding. -/
theorem denote_var_bvShiftR {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 128))
    (body : Com catCryptDialect (CryptoTy.sword 128 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvShiftR 128 1) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (shr1W (va.lookup V))) := rfl

/-- Peel one `bvAnd 128` binding. -/
theorem denote_var_bvAnd {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 128))
    (body : Com catCryptDialect (CryptoTy.sword 128 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvAnd 128) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (andW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvXor 128` binding. -/
theorem denote_var_bvXor {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 128))
    (body : Com catCryptDialect (CryptoTy.sword 128 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvXor 128) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (xorW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bitToSword 128` binding (the all-ones/zero mask from a bit). -/
theorem denote_var_bitToSword {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (vc : Ctxt.Var Γ CryptoTy.bit)
    (body : Com catCryptDialect (CryptoTy.sword 128 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bitToSword 128) rfl (.cons vc .nil)) body).denote V
      = body.denote (V.extend (maskW (vc.lookup V))) := rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-! ## 3. The two single-step `Com`s, each `denote = gf128_step` output

The free context binds the inputs `gf128_step` needs:

* `accStepCom` lives over `Γacc = [bit (xi), sword 128 (v), sword 128 (z)]`
  and is `z ⊕ (mask(xi) ∧ v)`.
* `valStepCom` lives over `Γval = [sword 128 (v)]` and is
  `(v ≫ 1) ⊕ (mask(v₀) ∧ R)`. (`v₀` is read in the dialect by a separate
  low-bit-extraction; here it is supplied as the `Bool` index `v.getLsbD 0`,
  matching how `gf128_step`'s spec branch already reads it.)

Both denote to the matching `gf128_step` component. -/

/-- The free context for `accStepCom`: `xi : bit`, `v : sword 128`, `z : sword 128`. -/
abbrev Γacc : Ctxt catCryptDialect :=
  [CryptoTy.bit, CryptoTy.sword 128, CryptoTy.sword 128]

/-- The bit input `xi` (head of `Γacc`). -/
def viXi : Ctxt.Var Γacc CryptoTy.bit := Ctxt.Var.here
/-- The running value `v` (second of `Γacc`). -/
def viV : Ctxt.Var Γacc (CryptoTy.sword 128) := Ctxt.Var.there Ctxt.Var.here
/-- The accumulator `z` (third of `Γacc`). -/
def viZ : Ctxt.Var Γacc (CryptoTy.sword 128) :=
  Ctxt.Var.there (Ctxt.Var.there Ctxt.Var.here)

/-- The accumulator-update `Com`: `m := bitToSword xi; t := m ∧ v; z ⊕ t`.
    A straight-line `Com catCryptDialect` over `Γacc`. -/
def accStepCom : Com catCryptDialect Γacc (CryptoTy.sword 128) :=
  -- m = bitToSword(xi)
  Com.var (Expr.mk (CatCryptOp.bitToSword 128) rfl (.cons viXi .nil)) <|
  -- t = m ∧ v   (m is here, v is shifted by one binder)
  Com.var (Expr.mk (CatCryptOp.bvAnd 128) rfl
      (.cons Ctxt.Var.here (.cons (Ctxt.Var.there viV) .nil))) <|
  -- r = z ⊕ t   (z shifted by two binders, t is here)
  Com.var (Expr.mk (CatCryptOp.bvXor 128) rfl
      (.cons (Ctxt.Var.there (Ctxt.Var.there viZ)) (.cons Ctxt.Var.here .nil))) <|
  Com.ret Ctxt.Var.here

/-- The free context for `valStepCom`: `v : sword 128`. -/
abbrev Γval : Ctxt catCryptDialect := [CryptoTy.sword 128]

/-- The running value `v` (head of `Γval`). -/
def vvV : Ctxt.Var Γval (CryptoTy.sword 128) := Ctxt.Var.here

/-- The running-value-update `Com`, parametric in the (low-bit) reduce flag
    `b = v.getLsbD 0`: `s := v ≫ 1; R := const; m := bitToSword b; t := m ∧ R; s ⊕ t`.
    A straight-line `Com catCryptDialect` over `Γval`. -/
def valStepCom (b : Bool) : Com catCryptDialect Γval (CryptoTy.sword 128) :=
  -- s = v ≫ 1
  Com.var (Expr.mk (CatCryptOp.bvShiftR 128 1) rfl (.cons vvV .nil)) <|
  -- R = gf128R
  Com.var (Expr.mk (CatCryptOp.bvConst 128 gf128R) rfl .nil) <|
  -- m = bitToSword(b)   (b a static reduce flag carried as a constant bit)
  Com.var (Expr.mk (CatCryptOp.constBit b) rfl .nil) <|
  Com.var (Expr.mk (CatCryptOp.bitToSword 128) rfl (.cons Ctxt.Var.here .nil)) <|
  -- t = m ∧ R   (m is here; stack is [m, b, R, s, v] so R is two binders back)
  Com.var (Expr.mk (CatCryptOp.bvAnd 128) rfl
      (.cons Ctxt.Var.here (.cons (Ctxt.Var.there (Ctxt.Var.there Ctxt.Var.here)) .nil))) <|
  -- r = s ⊕ t   (s is four binders back, t is here)
  Com.var (Expr.mk (CatCryptOp.bvXor 128) rfl
      (.cons (Ctxt.Var.there (Ctxt.Var.there (Ctxt.Var.there (Ctxt.Var.there Ctxt.Var.here))))
        (.cons Ctxt.Var.here .nil))) <|
  Com.ret Ctxt.Var.here

/-- A `Γacc` valuation from the three GF(2¹²⁸) `gf128_step` inputs. -/
def Vacc (z v : BitVec 128) (xi : Bool) : Ctxt.Valuation Γacc :=
  Ctxt.Valuation.extend
    (Ctxt.Valuation.extend
      (Ctxt.Valuation.extend (d := catCryptDialect) (Γ := []) .nil z) v) xi

/-- A `Γval` valuation from the running value `v`. -/
def Vval (v : BitVec 128) : Ctxt.Valuation Γval :=
  Ctxt.Valuation.extend (d := catCryptDialect) (Γ := []) .nil v

/-- **`accStepCom` denotes to `(gf128_step z v xi).1`** — the accumulator update
    of one GF(2¹²⁸) bit-step on the high dialect equals the SP 800-38D spec. -/
theorem accStepCom_denote (z v : BitVec 128) (xi : Bool) :
    accStepCom.denote (Vacc z v xi) = (gf128_step z v xi).1 := by
  rw [accStepW_eq_spec]
  rfl

/-- **`valStepCom` denotes to `(gf128_step z v xi).2`** — the running-value
    reduce of one GF(2¹²⁸) bit-step on the high dialect equals the SP 800-38D
    spec. The reduce flag is the spec's `v.getLsbD 0`. -/
theorem valStepCom_denote (z v : BitVec 128) (xi : Bool) :
    (valStepCom (v.getLsbD 0)).denote (Vval v) = (gf128_step z v xi).2 := by
  rw [valStepW_eq_spec z v xi]
  rfl

/-! ## 4. Lowering probe: the seam declines the GF(2¹²⁸) bit-step

`DialectToJasminCom.cryptoDialectToJasminCom` lowers a `Com catCryptDialect` only
when every op is in its covered fragment (the arith / shift / immediate-shift /
bignum-ALU rows). Both single-step GHASH `Com`s build their branch-free conditional
out of `CatCryptOp.bitToSword` (the all-ones/zero mask from a bit) — and
`valStepCom` additionally over `CatCryptOp.constBit` — which the seam's `toJExprD`
explicitly declines (it returns `none` on `bitToSword`/`constBit`, the bit ops).
So `cryptoDialectToJasminCom` returns `none` and there is no single emittable
jasmin function: the GHASH bit-step is denote-only on this seam, pending a
`bitToSword`/`constBit` lowering row (jasmin's branchless mask idiom). We record
this rather than emit. -/

/-- The accumulator step does **not** lower through the current seam: its
    `bitToSword` mask op is outside the lowered fragment. -/
theorem accStepCom_not_lowered :
    (DialectToJasminCom.cryptoDialectToJasminCom accStepCom).isNone := by
  native_decide

/-- The running-value step does **not** lower either: `bitToSword`/`constBit` are
    outside the seam's covered fragment. -/
theorem valStepCom_not_lowered (b : Bool) :
    (DialectToJasminCom.cryptoDialectToJasminCom (valStepCom b)).isNone := by
  cases b <;> native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.GhashGf128CatCryptEmit
