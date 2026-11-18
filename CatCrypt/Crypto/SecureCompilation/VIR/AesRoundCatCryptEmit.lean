/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.Primitives.AES128
public import Std.Tactic.BVDecide

/-!
# Byte-level building blocks for the AES round on `catCryptDialect`

Reference functions and `denote` lemmas on bytes (`BitVec 8`, the dialect type `.sword 8`)
for straight-line `Com catCryptDialect` programs of the AES round (FIPS-197 §5.1). The module
defines no program.

The multiplications by `x` and by `x + 1` in GF(2⁸) = `𝔽₂[x] / (x⁸ + x⁴ + x³ + x + 1)`, the
coefficients of MixColumns, are written in the dialect's word operations without a branch:

```
xtime b  =  (b ≪ 1) ⊕ ((0 - ((b ≫ 7) ∧ 1)) ∧ 0x1b)
mul3  b  =  xtime b ⊕ b
```

## Main definitions

* `T8`: the byte type of the dialect.
* `xtimeW`, `mul3W`: the branch-free multiplications by `x` and by `x + 1` on `BitVec 8`.
* `shlW`, `shrW`, `andW`, `subW`, `xorW`: the denotations of the byte operations `bvShiftL`,
  `bvShiftR`, `bvAnd`, `bvSub` and `bvXor` of `catCryptDialect`.

## Main results

* `xtimeW_eq_spec`, `mul3W_eq_spec`: `xtimeW` and `mul3W` are `AES128.xtime` and `AES128.mul3`
  along `UInt8.toBitVec`.
* `shlW_of_lt`, `shrW_of_lt`: below the width, the shift denotations are the plain shifts.
* `denote_var_bvConst`, `denote_var_bvShiftL`, `denote_var_bvShiftR`, `denote_var_bvAnd`,
  `denote_var_bvSub`, `denote_var_bvXor`: the denotation of a program whose first binding is
  one byte operation.
* `lookup_here_extend`, `lookup_there_extend`: variable lookup in an extended valuation.

The bitsliced round, SubBytes included, is the template `HashTemplate.AesBitslice` on
`jasminDialect`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.AesRoundCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Primitives

/-! ## 0. The byte dialect type and UInt8 ↔ BitVec correspondence

AES bytes are `BitVec 8` in the dialect. The FIPS-197 spec
(`CatCrypt.Crypto.Primitives.AES128`) is over `UInt8`; `UInt8.toBitVec` is the
bridge (it commutes with `<<<`, `>>>`, `&&&`, `^^^`, literals). -/

/-- The byte dialect type. -/
abbrev T8 : CryptoTy := .sword 8

/-! ## 1. The GF(2⁸) generators as branch-free `BitVec 8` reference functions

These are the *exact* waist functions the dialect ops denote to. `xtimeW` is the
branch-free Rijndael `×x`: shift left by one, then conditionally XOR the reduction
modulus `0x1b` (the low byte of `0x11b`) when the high bit was set. The
conditional reduce is `((0 - (b₇)) ∧ 0x1b)` — an all-ones-or-zero mask AND the
modulus — which is the standard CT-safe GF(2⁸) doubling and is exactly what the
dialect's `bvShiftR`/`bvAnd`/`bvSub`/`bvConst`/`bvShiftL`/`bvXor` chain produces. -/

/-- Branch-free GF(2⁸) `×x` (xtime): `(b ≪ 1) ⊕ (mask(b₇) ∧ 0x1b)`. -/
def xtimeW (b : BitVec 8) : BitVec 8 :=
  (b <<< (1 : Nat)) ^^^ (((0 : BitVec 8) - ((b >>> (7 : Nat)) &&& 1)) &&& 0x1b)

/-- GF(2⁸) `×3`: `xtime b ⊕ b`. -/
def mul3W (b : BitVec 8) : BitVec 8 := xtimeW b ^^^ b

/-- **`xtimeW` is the FIPS-197 `AES128.xtime`** (lifted along `UInt8.toBitVec`).
    The branch-free conditional reduce equals the spec's `if b &&& 0x80 ≠ 0`
    branch — discharged by `bv_decide` after unfolding the spec and the byte test. -/
theorem xtimeW_eq_spec (b : BitVec 8) : (AES128.xtime ⟨b⟩).toBitVec = xtimeW b := by
  unfold AES128.xtime xtimeW
  simp only [bne]
  bv_decide

/-- **`mul3W` is the FIPS-197 `AES128.mul3`.** -/
theorem mul3W_eq_spec (b : BitVec 8) : (AES128.mul3 ⟨b⟩).toBitVec = mul3W b := by
  unfold AES128.mul3 mul3W
  rw [← xtimeW_eq_spec]
  rfl

/-! ## 2. Single-binding `denote` peel step lemmas (each `rfl`)

The byte-dialect analogues of `Chacha20QRCatCryptEmit.denote_var_bvAdd` etc. Each
peels one `Com.var` binding to `body.denote (V.extend (waist …))`, the waist a
`BitVec 8`-valued function so `Ctxt.Valuation.extend` infers the bound type. The
ops used are `bvShiftL`, `bvShiftR`, `bvAnd`, `bvSub`, `bvXor`, `bvConst`. -/

/-- `bvShiftL 8 k` waist: the dialect denotation, shifting by `shiftMask 8 k`. -/
def shlW (k : Nat) (a : BitVec 8) : BitVec 8 := a <<< shiftMask 8 k
/-- `bvShiftR 8 k` waist (logical right shift by `shiftMask 8 k`). -/
def shrW (k : Nat) (a : BitVec 8) : BitVec 8 := BitVec.ushiftRight a (shiftMask 8 k)

/-- At a count below `8` the `bvShiftL 8 k` waist is the plain left shift. -/
theorem shlW_of_lt {k : Nat} (hk : k < 8) (a : BitVec 8) : shlW k a = a <<< k := by
  rw [shlW, shiftMask_of_lt hk]

/-- At a count below `8` the `bvShiftR 8 k` waist is the plain logical right shift. -/
theorem shrW_of_lt {k : Nat} (hk : k < 8) (a : BitVec 8) :
    shrW k a = BitVec.ushiftRight a k := by
  rw [shrW, shiftMask_of_lt hk]
/-- `bvAnd 8` waist. -/
def andW (a b : BitVec 8) : BitVec 8 := a &&& b
/-- `bvSub 8` waist. -/
def subW (a b : BitVec 8) : BitVec 8 := a - b
/-- `bvXor 8` waist. -/
def xorW (a b : BitVec 8) : BitVec 8 := a ^^^ b

/-- Peel one `bvConst 8 c` binding. -/
theorem denote_var_bvConst {Γ : Ctxt catCryptDialect} {s : CryptoTy} (c : BitVec 8)
    (body : Com catCryptDialect (CryptoTy.sword 8 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvConst 8 c) rfl .nil) body).denote V
      = body.denote (V.extend c) := rfl

/-- Peel one `bvShiftL 8 k` binding. -/
theorem denote_var_bvShiftL {Γ : Ctxt catCryptDialect} {k : Nat} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 8))
    (body : Com catCryptDialect (CryptoTy.sword 8 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvShiftL 8 k) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (shlW k (va.lookup V))) := rfl

/-- Peel one `bvShiftR 8 k` binding. -/
theorem denote_var_bvShiftR {Γ : Ctxt catCryptDialect} {k : Nat} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 8))
    (body : Com catCryptDialect (CryptoTy.sword 8 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvShiftR 8 k) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (shrW k (va.lookup V))) := rfl

/-- Peel one `bvAnd 8` binding. -/
theorem denote_var_bvAnd {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 8))
    (body : Com catCryptDialect (CryptoTy.sword 8 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvAnd 8) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (andW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvSub 8` binding. -/
theorem denote_var_bvSub {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 8))
    (body : Com catCryptDialect (CryptoTy.sword 8 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvSub 8) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (subW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvXor 8` binding. -/
theorem denote_var_bvXor {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 8))
    (body : Com catCryptDialect (CryptoTy.sword 8 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvXor 8) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (xorW (va.lookup V) (vb.lookup V))) := rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.AesRoundCatCryptEmit
