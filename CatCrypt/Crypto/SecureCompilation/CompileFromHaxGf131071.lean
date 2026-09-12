/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import CatCrypt.Crypto.SecureCompilation.BitVecNatBridge
public import CatCrypt.Crypto.SecureCompilation.BitVecNatBridge

/-!
# #606 fan-out: the verified compiler emits a GF(131071) Mersenne-fold multiply

This module extends the **C4** step of the verified-compiler plan to the
**prime-field** primitive `GF(131071)`. `131071 = 2¹⁷ - 1` is a **Mersenne**
prime, so `2¹⁷ ≡ 1 (mod 131071)`: multiply is integer `a·b` followed by a
`2¹⁷ ≡ 1` double-fold and a branch-free conditional subtract — the same Mersenne
reduce shape as GF(127) (= 2⁷-1) and GF(8191) (= 2¹³-1), here at the 17-bit
Mersenne modulus.

## GF(131071) multiply (Mersenne fold), `w = 64`

With `a, b ∈ [0, 131070]` the product `a·b ≤ 131070² ≈ 1.7·10¹⁰ < 2³⁵` fits in
the low word, and `2¹⁷ ≡ 1 (mod 131071)` folds the high bits:

```
   p := a*b                                    -- p < 2³⁵
   p := (p & 131071) + (p >> 17)               -- 1st fold
   p := (p & 131071) + (p >> 17)               -- 2nd fold
   t := p - 131071 ; m := t >> 63 ; p := (0 - m) & 131071 + t   -- branch-free csub
```

The conditional subtract is data-independent. All steps are `&`/`>>`/`+`/`-`/`*`
over GPRs — the existing SHA-256/Keccak/BLAKE2 recognizers accept them, so **no
change to the verified front is required**.

## Method (mirrors `CompileFromHaxGf8191.gf8191Mul_compiles`)

`gf131071MulSrc` is the let-normalized `ImpExpr`; `gf131071MulFold` is the closed
Mersenne-fold **emit form** the source denotes to; `_compiles` routes the
FOLD-FORM source-spec (a `rfl`) through `compileFromHax_meets_spec`. The abstract
`(a*b) % 131071` tie is `gf131071MulFold_eq_mod` over `a, b < 131071`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf131071

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The GF(131071) Mersenne multiply source — `w = 64`, params `["a","b"]` -/

/-- The GF(131071) multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]`. Integer multiply, Mersenne `2¹⁷ ≡ 1` double-fold,
    then a branch-free conditional subtract of `131071`. -/
def gf131071MulSrc : ImpExpr :=
  .letBind "c131071" (.lit (.int 131071))
   (.letBind "c0" (.lit (.int 0))
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   (.letBind "lo0" (.app "BitAnd" [.var "p", .var "c131071"])
    (.letBind "hi0" (.app "shift_right" [.var "p", .lit (.int 17)])
     (.letBind "p1" (.app "wrapping_add" [.var "lo0", .var "hi0"])
      (.letBind "lo1" (.app "BitAnd" [.var "p1", .var "c131071"])
       (.letBind "hi1" (.app "shift_right" [.var "p1", .lit (.int 17)])
        (.letBind "p2" (.app "wrapping_add" [.var "lo1", .var "hi1"])
         (.letBind "t" (.app "wrapping_sub" [.var "p2", .var "c131071"])
          (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
           (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
            (.letBind "mm" (.app "BitAnd" [.var "nm", .var "c131071"])
             (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
              (.var "r"))))))))))))))

/-- The explicit closed Mersenne-fold **emit form** the source denotes to. -/
def gf131071MulFold (a b : BitVec 64) : BitVec 64 :=
  let p  := a * b
  let p1 := (p &&& 131071) + (p >>> (17 : Nat))
  let p2 := (p1 &&& 131071) + (p1 >>> (17 : Nat))
  let t  := p2 - 131071
  let m  := t >>> (63 : Nat)
  let mm := (0 - m) &&& 131071
  mm + t

/-- The GF(131071) source denotes to the Mersenne-fold emit form. -/
theorem gf131071MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I gf131071MulSrc (fun _ => none)
      = some (gf131071MulFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the GF(131071) multiply. -/
theorem gf131071Mul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf131071MulSrc).isSome := by
  native_decide

/-- **GF(131071) Mersenne multiply emitted by the verified compiler (fold
    form).** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] gf131071MulSrc = some c`, and `c`'s `BitVec 64`
    denotation (under `![a, b]`) is the closed Mersenne-fold emit form. A #606
    fan-out to the Mersenne prime field `GF(2¹⁷-1)`. The abstract `(a*b) % 131071`
    tie is `gf131071MulFold_eq_mod`. -/
theorem gf131071Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf131071MulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = gf131071MulFold a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf131071MulSrc).get
    gf131071Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf131071MulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      gf131071MulSrc (fun _ => none) = some (gf131071MulFold a b) := by
    have h := gf131071MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] gf131071MulSrc _ hc hspec

/-! ## The abstract `(a*b) % 131071` tie (the prime-field mod-reduce identity) -/

/-- The `Nat`-domain image of the GF(131071) Mersenne fold: the exact `toNat`
    semantics of each `BitVec 64` step (`W = 2⁶⁴`; `&&& 131071` is `% 131072`, the
    branch-free csub is the two's-complement `W - 131071 + p2` / sign-bit mask).
    `gf131071FoldNat_eq_mod` is the standalone `Nat` payload; the `BitVec`-plumbing
    push is `bitvec_binop_eq_of_nat_bridge`'s `hf` obligation. -/
def gf131071FoldNat (m n : Nat) : Nat :=
  let W := 18446744073709551616
  let p  := m * n % W
  let p1 := (p % 131072 + p / 131072) % W
  let p2 := (p1 % 131072 + p1 / 131072) % W
  let t  := (W - 131071 + p2) % W
  let mm := (W - t / 9223372036854775808 + 0) % W % 131072
  (mm + t) % W

/-- The pure-`Nat` GF(131071) reduce payload: the fold-as-`Nat` equals
    `(m*n) % 131071` on the residue domain `m, n < 131071` (the reduction
    `e ≡ r1 ≡ r2 (mod 131071)` is linear because `2¹⁷ = 131071 + 1`). Factored out
    of the `BitVec` plumbing via `bitvec_binop_eq_of_nat_bridge`. -/
theorem gf131071FoldNat_eq_mod (m n : Nat) (hm : m < 131071) (hn : n < 131071) :
    gf131071FoldNat m n = m * n % 131071 := by
  have hmn : m * n ≤ 131070 * 131070 := Nat.mul_le_mul (by omega) (by omega)
  simp only [gf131071FoldNat]
  set e := m * n with he
  rw [Nat.mod_eq_of_lt (show e < 18446744073709551616 by omega)]
  set r1 := e % 131072 + e / 131072 with hr1
  rw [Nat.mod_eq_of_lt (show r1 < 18446744073709551616 by omega)]
  set r2 := r1 % 131072 + r1 / 131072 with hr2
  rw [Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
  rcases Nat.lt_or_ge r2 131071 with hr2c | hr2c
  · rw [Nat.mod_eq_of_lt (show 18446744073709551616 - 131071 + r2 < 18446744073709551616 by omega)]
    rw [show (18446744073709551616 - 131071 + r2) / 9223372036854775808 = 1 by omega]
    rw [show (18446744073709551616 - 1 + 0) % 18446744073709551616 % 131072 = 131071 by norm_num]
    rw [show 131071 + (18446744073709551616 - 131071 + r2) = 18446744073709551616 + r2 by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
    omega
  · rw [show (18446744073709551616 - 131071 + r2) % 18446744073709551616 = r2 - 131071 by omega]
    rw [show (r2 - 131071) / 9223372036854775808 = 0 by omega]
    omega

/-- **GF(131071) Mersenne fold = `(a*b) mod 131071`** on `a, b < 131071`. Ties
    the emitted closed fold form to abstract modular multiply. The `Nat` reduce is
    factored into `gf131071FoldNat_eq_mod`; `bitvec_binop_eq_of_nat_bridge` does
    the plumbing. -/
theorem gf131071MulFold_eq_mod (a b : BitVec 64)
    (ha : a < 131071#64) (hb : b < 131071#64) :
    gf131071MulFold a b = (a * b) % 131071#64 := by
  have hA : a.toNat < 131071 := by have := BitVec.lt_def.mp ha; simpa using this
  have hB : b.toNat < 131071 := by have := BitVec.lt_def.mp hb; simpa using this
  apply bitvec_binop_eq_of_nat_bridge a b gf131071MulFold (fun a b => (a * b) % 131071#64)
    gf131071FoldNat (fun m n => m * n % 131071) 131071 hA hB
  · intro u v _ _
    have hm : ∀ x : Nat, x &&& 131071 = x % 131072 :=
      fun x => Nat.and_two_pow_sub_one_eq_mod x 17
    simp only [gf131071MulFold, gf131071FoldNat, BitVec.toNat_add, BitVec.toNat_and,
      BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.reduceToNat,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, hm]
  · intro u v hu hv
    have huv : u.toNat * v.toNat < 18446744073709551616 := by
      have : u.toNat * v.toNat ≤ 131070 * 131070 := Nat.mul_le_mul (by omega) (by omega); omega
    simp only [BitVec.toNat_umod, BitVec.toNat_mul, BitVec.reduceToNat]
    rw [Nat.mod_eq_of_lt huv]
  · exact gf131071FoldNat_eq_mod

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf131071
