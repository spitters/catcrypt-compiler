/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# #606 fan-out: the verified compiler emits a GF(524287) Mersenne-fold multiply

This module extends the **C4** step of the verified-compiler plan to another
**prime-field** primitive: the `GF(524287)` base-field multiply.
`524287 = 2¹⁹ − 1` is a **Mersenne** prime, so `2¹⁹ ≡ 1 (mod 524287)`: multiply
is integer `a·b` followed by a `2¹⁹ ≡ 1` double-fold and a branch-free
conditional subtract — the same Mersenne reduce shape as the GF(127) (= 2⁷−1),
GF(8191) (= 2¹³−1), GF(131071) (= 2¹⁷−1) and Mersenne-31 (= 2³¹−1) fan-outs,
here at the 19-bit Mersenne modulus, completing the small-Mersenne ladder.

## GF(524287) multiply (Mersenne fold), `w = 64`

With `a, b ∈ [0, 524286]` the product `a·b ≤ 524286² < 2³⁸` fits the low word,
and `2¹⁹ ≡ 1 (mod 524287)` folds the high bits:

```
   p := a*b                                   -- p < 2³⁸
   p := (p & 524287) + (p >> 19)              -- 1st fold
   p := (p & 524287) + (p >> 19)              -- 2nd fold
   t := p - 524287 ; m := t >> 63 ; p := (0 - m) & 524287 + t   -- branch-free csub
```

All steps are `&`/`>>`/`+`/`-`/`*` over GPRs — the SHA-256/Keccak/BLAKE2/GF(8191)
recognizers (`wrapping_mul`/`shift_right`/`BitAnd`/`wrapping_add`/`wrapping_sub`
with literal counts) already accept them, so **no change to the verified front is
required**.

## Method (mirrors `CompileFromHaxGf8191.gf8191Mul_compiles`)

`gf524287MulSrc` is the let-normalized `ImpExpr`; `gf524287MulFold` is the
explicit closed Mersenne-fold **emit form** the source denotes to; the
`_compiles` theorem routes the FOLD-FORM source-spec through the C3 per-primitive
obligation `compileFromHax_meets_spec`. The abstract `(a*b) % 524287` tie
(`gf524287MulFold_eq_mod`) is proved via `Nat` arithmetic on `toNat`: even with
the product bounded `< 2³⁸`, the full 64-bit double-fold + csub bitblast
SAT-times-out under `bv_decide`, so the residue is established structurally
(Euclidean fold split + one branch-free csub case-split) — the same route the
Mersenne-31 seam takes.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The GF(524287) Mersenne multiply source — `w = 64`, parameters `["a","b"]` -/

/-- The GF(524287) multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`). Integer multiply,
    Mersenne `2¹⁹ ≡ 1` double-fold, then a branch-free conditional subtract of
    `524287` using the `0 − (t >> 63)` mask. Returns the residue register `r`. -/
def gf524287MulSrc : ImpExpr :=
  .letBind "cP" (.lit (.int 524287))
   (.letBind "c0" (.lit (.int 0))
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   (.letBind "lo0" (.app "BitAnd" [.var "p", .var "cP"])
    (.letBind "hi0" (.app "shift_right" [.var "p", .lit (.int 19)])
     (.letBind "p1" (.app "wrapping_add" [.var "lo0", .var "hi0"])
      (.letBind "lo1" (.app "BitAnd" [.var "p1", .var "cP"])
       (.letBind "hi1" (.app "shift_right" [.var "p1", .lit (.int 19)])
        (.letBind "p2" (.app "wrapping_add" [.var "lo1", .var "hi1"])
         (.letBind "t" (.app "wrapping_sub" [.var "p2", .var "cP"])
          (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
           (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
            (.letBind "mm" (.app "BitAnd" [.var "nm", .var "cP"])
             (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
              (.var "r"))))))))))))))

/-- The explicit closed Mersenne-fold **emit form** the source denotes to, at
    `w = 64`. `gf524287MulFold_eq_mod` ties it to abstract `(a*b) % 524287` on
    `a, b < 524287`. -/
def gf524287MulFold (a b : BitVec 64) : BitVec 64 :=
  let p  := a * b
  let p1 := (p &&& 524287) + (p >>> (19 : Nat))
  let p2 := (p1 &&& 524287) + (p1 >>> (19 : Nat))
  let t  := p2 - 524287
  let m  := t >>> (63 : Nat)
  let mm := (0 - m) &&& 524287
  mm + t

/-- The GF(524287) source denotes to the Mersenne-fold emit form. -/
theorem gf524287MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I gf524287MulSrc (fun _ => none)
      = some (gf524287MulFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the GF(524287) multiply. -/
theorem gf524287Mul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf524287MulSrc).isSome := by
  native_decide

/-- **GF(524287) Mersenne multiply emitted by the verified compiler (fold
    form).** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] gf524287MulSrc = some c`, and `c`'s `BitVec 64`
    denotation (under `![a, b]`) is the closed Mersenne-fold emit form. A #606
    fan-out to the Mersenne prime field `GF(2¹⁹−1)`, reusing the existing
    recognizers with no front change. The abstract `(a*b) % 524287` tie is
    `gf524287MulFold_eq_mod`. -/
theorem gf524287Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf524287MulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = gf524287MulFold a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf524287MulSrc).get
    gf524287Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf524287MulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      gf524287MulSrc (fun _ => none) = some (gf524287MulFold a b) := by
    have h := gf524287MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] gf524287MulSrc _ hc hspec

/-! ## The abstract `(a*b) % 524287` tie (the prime-field mod-reduce identity) -/

/-- **GF(524287) Mersenne fold = `(a*b) mod 524287`** on `a, b < 524287`. Ties
    the emitted closed fold form to abstract modular multiply. The product
    `a·b ≤ 524286² < 2³⁸` never wraps the `BitVec 64`, so the two `2¹⁹ ≡ 1` folds
    and the single conditional subtract land the residue exactly in `[0, 524286]`.

    Proved via `Nat` arithmetic on `toNat`: even with the product bounded
    `< 2³⁸`, the full 64-bit double-fold + csub bitblast SAT-times-out under
    `bv_decide`, so the residue is established structurally (Euclidean fold
    split + one branch-free csub case-split), the same route as the Mersenne-31
    seam. `2¹⁹ ≡ 1`, `524288 = 2¹⁹`. -/
theorem gf524287MulFold_eq_mod (a b : BitVec 64)
    (ha : a < 524287#64) (hb : b < 524287#64) :
    gf524287MulFold a b = (a * b) % 524287#64 := by
  have ham : a.toNat < 524287 := by bv_omega
  have hbm : b.toNat < 524287 := by bv_omega
  have hPmul : (a * b).toNat = a.toNat * b.toNat := by
    have hlt : a.toNat * b.toNat < 2 ^ 64 := by
      have hle : a.toNat * b.toNat ≤ 524286 * 524286 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt hlt
  have hPlt : a.toNat * b.toNat < 2 ^ 38 := by
    have hle : a.toNat * b.toNat ≤ 524286 * 524286 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hmask : ∀ n : Nat, n &&& 524287 = n % 524288 := by
    intro n; rw [show (524287 : Nat) = 2 ^ 19 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hlit : BitVec.toNat (524287 : BitVec 64) = 524287 := rfl
  have hlit0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
  apply BitVec.eq_of_toNat_eq
  unfold gf524287MulFold
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_sub, BitVec.toNat_umod, BitVec.toNat_mul,
    Nat.shiftRight_eq_div_pow, hlit, hlit0, hmask]
  rw [show (524287#64 : BitVec 64).toNat = 524287 from rfl]
  set P := a.toNat * b.toNat with hP
  clear_value P
  clear hP hPmul ham hbm ha hb hmask hlit hlit0
  have hP64 : P % 2 ^ 64 = P := Nat.mod_eq_of_lt (by omega)
  rw [hP64]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 524288 ∧ P = q * 524288 + r :=
    ⟨P / 524288, P % 524288, Nat.mod_lt _ (by norm_num), by omega⟩
  have hq : q < 524288 := by omega
  have hf1 : (q * 524288 + r) % 524288 + (q * 524288 + r) / 2 ^ 19 = r + q := by
    rw [show (2 ^ 19 : Nat) = 524288 from rfl]; omega
  rw [hf1]
  have hf1lt : r + q < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hf1lt]
  set f2 := (r + q) % 524288 + (r + q) / 2 ^ 19 with hf2
  have hf2lt : f2 < 2 ^ 64 := by
    rw [hf2, show (2 ^ 19 : Nat) = 524288 from rfl]; omega
  rw [Nat.mod_eq_of_lt hf2lt]
  have hf2le : f2 ≤ 524288 := by
    rw [hf2, show (2 ^ 19 : Nat) = 524288 from rfl]; omega
  clear_value f2
  have hcong : f2 % 524287 = (q * 524288 + r) % 524287 := by
    rw [hf2, show (2 ^ 19 : Nat) = 524288 from rfl]; omega
  rw [← hcong]
  rcases Nat.lt_or_ge f2 524287 with hlt | hge
  · have ht : (2 ^ 64 - 524287 + f2) % 2 ^ 64 = 2 ^ 64 - 524287 + f2 := by
      apply Nat.mod_eq_of_lt; omega
    rw [ht]
    have hm : (2 ^ 64 - 524287 + f2) / 2 ^ 63 = 1 := by
      rw [Nat.div_eq_of_lt_le] <;> omega
    rw [hm]; omega
  · have ht : (2 ^ 64 - 524287 + f2) % 2 ^ 64 = f2 - 524287 := by
      have : 2 ^ 64 - 524287 + f2 = 2 ^ 64 + (f2 - 524287) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [ht]
    have hm : (f2 - 524287) / 2 ^ 63 = 0 := by
      apply Nat.div_eq_of_lt; omega
    rw [hm]; omega

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287
