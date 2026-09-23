/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptOpInfo
public import CatCrypt.Crypto.SecureCompilation.VIR.Grind

/-!
# VIR-level masking-preservation predicate

A static predicate `maskingSafeCom` that captures: *every op in this
program is linear over an XOR-share masking* — i.e., if each input
variable is replaced by `v ⊕ r` for a fresh share `r`, every
intermediate result is similarly masked.

This is the IR-level analogue of the ITree-level `MaskingPass.lean`,
lifted to operate on `Com catCryptDialect`. Bridges to `MaskingPass`
through the existing `Com.denote → SPComp` chain.

## Scope

Each op falls into one of three classes:

* **Linear** — `xor`, `bvXor`, `not`, `bvNot`, `constBit`, `bvConst`,
  `inl`, `inr`, `mkPair`, `fst`, `snd`. Trivially share-commuting.
* **Non-linear but in-place** — `and`, `or`, `eqBit`, `bvAnd`, `bvOr`,
  `bvAdd`, `bvSub`, `bvMul`, `bvEq`. These cannot be applied
  directly under a sharing without re-randomization; flagged as
  unsafe under the simplest policy.
* **Memory / control** — `memref*`, `ite`, `extCall`. Conservatively
  unsafe.

Track 3c-v2 (deferred): a strengthened predicate that distinguishes
"first-order masking-safe" from "second-order masking-safe" and
accepts `and`/`mul` when paired with an explicit re-randomization
(`refreshMask`) op.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

namespace CatCryptDialect

/-! ## 1. Per-op linearity predicate -/

/-- Is this op linear over XOR-sharing under the conservative first-order
    policy? -/
def CatCryptOp.maskingLinear : CatCryptOp → Bool
  -- Constants: trivially linear (additive identity preserved).
  | .constBit _ | .constUnit | .bvConst _ _ => true
  -- Bitwise linear ops.
  | .xor | .not | .bvXor _ | .bvNot _ => true
  -- Pair/sum constructors and destructors: linear (no mixing).
  | .mkPair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _ => true
  -- Equality: not linear (squares the bit).
  | .eqBit | .bvEq _ => false
  -- AND/OR: non-linear over GF(2).
  | .and | .or | .bvAnd _ | .bvOr _ => false
  -- BitVec arithmetic over Z/2^n is non-linear over GF(2)-sharing.
  | .bvAdd _ | .bvSub _ | .bvMul _ => false
  -- Shifts by constant amounts are linear.
  | .bvShiftL _ _ | .bvShiftR _ _ => true
  -- Rotates and arithmetic right shift by a compile-time immediate are bit
  -- permutations / linear bit copies, hence GF(2)-linear (like the logical shifts).
  | .bvRor _ _ | .bvRol _ _ | .bvShiftRA _ _ => true
  -- Variable-amount shifts: the shift count is a *second* data operand, so the
  -- result is not linear in that operand — conservatively unsafe.
  | .bvShiftLV _ | .bvShiftRV _ => false
  -- `andn` = `(~a) & b` contains an AND: non-linear over GF(2)-sharing.
  | .andn _ => false
  -- `bitToSword n`: sign-extension of a bit is GF(2)-linear
  -- (`extend(c1 ⊕ c2) = extend(c1) ⊕ extend(c2)`).
  | .bitToSword _ => true
  -- ite / memrefs / extCall: conservatively unsafe.
  | .ite _ | .memrefZero _ | .memrefSet _ _ | .memrefGet _ _
  | .memrefSetDyn _ | .memrefGetDyn _ | .memrefGetDyn128 _
  | .memrefWSetDyn _ _ | .memrefWGetDyn _ _
  | .extCall _ _ _ => false
  -- Carry-arithmetic + sampling: non-linear over GF(2)-sharing / not maskable.
  | .bvAdd64 _ | .bvAdc _ | .sampleBit | .sampleBv _ => false
  -- Bignum word-splits (high-multiply + carry-chain words): carry / multiply
  -- arithmetic, non-linear over GF(2)-sharing (like `bvMul`/`bvAdd64`).
  | .bvMulHi _ | .bvAddCarryLo _ | .bvAddCarryHi _ => false
  -- 128-bit SIMD. Pure permutations / immediate byte-shifts / baked constants are
  -- GF(2)-linear; the general `vsimd` bundle (AES S-box, GF-multiply, packed
  -- add/and/or, data-dependent shuffle) and the SHA-NI / key-schedule ops mix in
  -- non-linear steps, so they are conservatively unsafe.
  | .vpshufdC _ | .vpsrldqC _ | .vpslldqC _ | .vconst128 _ => true
  | .vsimd _ | .vaeskeygenC _
  | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2 => false

@[grind =]
theorem CatCryptOp.maskingLinear_xor :
    CatCryptOp.maskingLinear .xor = true := rfl

@[grind =]
theorem CatCryptOp.maskingLinear_bvXor (w : Nat) :
    CatCryptOp.maskingLinear (.bvXor w) = true := rfl

@[grind =]
theorem CatCryptOp.maskingLinear_and :
    CatCryptOp.maskingLinear .and = false := rfl

@[grind =]
theorem CatCryptOp.maskingLinear_bvAnd (w : Nat) :
    CatCryptOp.maskingLinear (.bvAnd w) = false := rfl

@[grind =]
theorem CatCryptOp.maskingLinear_bvMul (w : Nat) :
    CatCryptOp.maskingLinear (.bvMul w) = false := rfl

end CatCryptDialect

open CatCryptDialect

/-! ## 2. Per-expression and per-program predicate -/

/-- An `Expr` is masking-linear iff its op is. -/
def maskingLinearExpr {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) : Bool :=
  e.op.maskingLinear

@[grind =]
theorem maskingLinearExpr_op {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) : maskingLinearExpr e = e.op.maskingLinear := rfl

/-- A `Com` is masking-safe iff every let-bound expression is masking-linear. -/
def maskingSafeCom {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    Com catCryptDialect Γ t → Bool
  | .ret _ => true
  | .var e body => maskingLinearExpr e && maskingSafeCom body

@[grind =]
theorem maskingSafeCom_ret {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (v : Ctxt.Var Γ t) : maskingSafeCom (Com.ret v) = true := rfl

@[grind =]
theorem maskingSafeCom_var {Γ : Ctxt catCryptDialect} {t s : CryptoTy}
    (e : Expr catCryptDialect Γ t) (body : Com catCryptDialect (t :: Γ) s) :
    maskingSafeCom (Com.var e body) =
      (maskingLinearExpr e && maskingSafeCom body) := rfl

/-! ## 3. Decidability + Prop bridge -/

def maskingSafePropCom {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) : Prop :=
  maskingSafeCom c = true

instance {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) : Decidable (maskingSafePropCom c) := by
  unfold maskingSafePropCom; infer_instance

/-! ## 4. Smoke test: pure-XOR chain is masking-safe -/

example {Γ : Ctxt catCryptDialect} (v : Ctxt.Var Γ .bit) :
    maskingSafeCom (Com.var (d := catCryptDialect) (Γ := Γ) (t := .bit) (s := .bit)
      { op := .xor, retTy_eq := rfl,
        args := .cons v (.cons v .nil) }
      (.ret .here)) = true := by
  grind

/-! ## 5. Smoke test: `and` is NOT masking-safe -/

example {Γ : Ctxt catCryptDialect} (v : Ctxt.Var Γ .bit) :
    maskingSafeCom (Com.var (d := catCryptDialect) (Γ := Γ) (t := .bit) (s := .bit)
      { op := .and, retTy_eq := rfl,
        args := .cons v (.cons v .nil) }
      (.ret .here)) = false := by
  grind

end CatCrypt.Crypto.SecureCompilation.VIR
