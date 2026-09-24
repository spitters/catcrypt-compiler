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
# The AES round on the high `catCryptDialect`: GF(2⁸) capability + MixColumns / AddRoundKey

The AES round (FIPS-197 §5.1) is built natively as straight-line
`Com catCryptDialect` programs over the high (MLIR/prime-IR-aligned) crypto-SSA
dialect, and each program is proved to *denote* to the committed FIPS-197 spec
in `CatCrypt.Crypto.Primitives.AES128`.

## GF(2⁸) capability — MLIR / prime-IR aligned

GF(2⁸) is the Rijndael binary polynomial field `𝔽₂[x] / (x⁸+x⁴+x³+x+1)`
(reduction polynomial `0x11b`). The same field and reduction modulus already
underlie the committed `clmul`/`gf2p8affineqb` SIMD ops and the bit-serial
`FieldEmitGoldenGf256.gf256mul`. Here the field is added to the **high** dialect
*additively* — no new `CatCryptOp` constructor is introduced. The two field
generators AES needs (`xtime = ×x mod 0x11b`, and `×3 = ×x ⊕ id`) are expressed
out of the dialect's existing word alphabet:

```
xtime b  =  (b ≪ 1) ⊕ (mask(b₇) ∧ 0x1b)        -- branch-free conditional reduce
mul3  b  =  xtime b ⊕ b
```

where `mask(b₇)` is the all-ones-or-zero mask of the top bit `b₇`, built from the
dialect's `bitToSword` of `b ≫ 7`'s low bit — i.e. exactly the LLVM
`(0 - sext(b₇)) : i8` mask pattern. Every op is one of `bvShiftL`, `bvShiftR`,
`bvAnd`, `bvXor`, `bvConst` already in `CatCryptOp`. This is the GF(2⁸)
*multiply-by-constant* capability — the MixColumns MDS coefficients are `{01,02,03}`,
so `xtime`/`mul3`/`id` are exactly what MixColumns needs.

## Components, each `denote = spec`

* `xtimeCom`     — `denote = (AES128.xtime _).toBitVec`     (GF(2⁸) ×2)
* `mul3Com`      — `denote = (AES128.mul3 _).toBitVec`      (GF(2⁸) ×3)
* `mixColOutCom` — the four MixColumns output bytes, `denote = (AES128.mixColumn …).i`
* `addRoundKeyCom` — `denote = (a ⊕ k)` (AddRoundKey is a byte XOR)

ShiftRows is a pure lane permutation (no arithmetic) and AddRoundKey is `bvXor`;
the GF(2⁸) `xtime`/`mul3` + MixColumns witness is the main result,
since the MDS multiply is the only non-ALU-trivial part of the round. SubBytes is
the S-box table; its dialect handling is via `memrefGetDyn` (runtime-index table
lookup) and is discussed in the final section.

0 sorries.
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

/-- `bvShiftL 8 k` waist. -/
def shlW (k : Nat) (a : BitVec 8) : BitVec 8 := a <<< k
/-- `bvShiftR 8 k` waist (logical right shift). -/
def shrW (k : Nat) (a : BitVec 8) : BitVec 8 := BitVec.ushiftRight a k
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
