/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax
import CatCrypt.Crypto.SecureCompilation.BitVecNatBridge

/-!
# #606 fan-out: the verified compiler emits a GF(8191) Mersenne-fold multiply

This module extends the **C4** step of the verified-compiler plan to another
**prime-field** primitive: the `GF(8191)` base-field multiply. `8191 = 2¹³ - 1`
is a **Mersenne** prime, so `2¹³ ≡ 1 (mod 8191)`: multiply is integer `a·b`
followed by a `2¹³ ≡ 1` double-fold and a branch-free conditional subtract —
the same Mersenne reduce shape as the GF(127) (= 2⁷-1) fan-out, here at the
13-bit Mersenne modulus.

## GF(8191) multiply (Mersenne fold), `w = 64`

With `a, b ∈ [0, 8190]` the product `a·b ≤ 8190² = 67076100 < 2²⁷` fits in the
low word, and `2¹³ ≡ 1 (mod 8191)` folds the high bits:

```
   p := a*b                                   -- p ≤ 67076100 < 2²⁷
   p := (p & 8191) + (p >> 13)                -- 1st fold: p ≤ 8190 + 2¹⁴
   p := (p & 8191) + (p >> 13)                -- 2nd fold: p ≤ 8190 + 1
   t := p - 8191 ; m := t >> 63 ; p := (0 - m) & 8191 + t   -- branch-free csub
```

The conditional subtract is data-independent (a `0 − (t >> 63)` mask, not a
`Jcc`). All steps are `&`/`>>`/`+`/`-`/`*` over GPRs — the SHA-256/Keccak/BLAKE2
recognizers (`wrapping_mul`/`shr`/`BitAnd`/`wrapping_add`/`wrapping_sub` with
literal counts) already accept them, so **no change to the verified front is
required**; this is the same Mersenne prime-field (mod-reduce) fan-out shape as
the GF(127) multiply, here for the Mersenne prime `8191 = 2¹³ - 1`.

## Method (mirrors `CompileFromHaxGf127.gf127Mul_compiles`)

`gf8191MulSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `gf8191MulFold` is the explicit closed Mersenne-fold
**emit form** the source denotes to; the `_compiles` theorem routes the
FOLD-FORM source-spec (`gf8191MulSrc_denoteScalar`, a `rfl`) through the C3
per-primitive obligation `compileFromHax_meets_spec`. The emitted jasmin `Com`
is *computed by the verified compiler* and proven equal to the Mersenne-fold
form. The abstract `(a*b) % 8191` tie is stated and proved separately
(`gf8191MulFold_eq_mod`) over the constrained domain `a, b < 8191`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf8191

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The GF(8191) Mersenne multiply source — `w = 64`, parameters `["a","b"]` -/

/-- The GF(8191) multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`). Integer multiply,
    Mersenne `2¹³ ≡ 1` double-fold, then a branch-free conditional subtract of
    `8191` using the `0 − (t >> 63)` mask. Returns the residue register `r`. -/
def gf8191MulSrc : ImpExpr :=
  .letBind "c8191" (.lit (.int 8191))
   (.letBind "c0" (.lit (.int 0))
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   (.letBind "lo0" (.app "BitAnd" [.var "p", .var "c8191"])
    (.letBind "hi0" (.app "shift_right" [.var "p", .lit (.int 13)])
     (.letBind "p1" (.app "wrapping_add" [.var "lo0", .var "hi0"])
      (.letBind "lo1" (.app "BitAnd" [.var "p1", .var "c8191"])
       (.letBind "hi1" (.app "shift_right" [.var "p1", .lit (.int 13)])
        (.letBind "p2" (.app "wrapping_add" [.var "lo1", .var "hi1"])
         (.letBind "t" (.app "wrapping_sub" [.var "p2", .var "c8191"])
          (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
           (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
            (.letBind "mm" (.app "BitAnd" [.var "nm", .var "c8191"])
             (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
              (.var "r"))))))))))))))

/-- The explicit closed Mersenne-fold **emit form** the source denotes to, at
    `w = 64`. This is the exact step-by-step computation `gf8191MulSrc` performs;
    `gf8191MulFold_eq_mod` ties it to abstract `(a*b) % 8191` on `a, b < 8191`. -/
def gf8191MulFold (a b : BitVec 64) : BitVec 64 :=
  let p  := a * b
  let p1 := (p &&& 8191) + (p >>> (13 : Nat))
  let p2 := (p1 &&& 8191) + (p1 >>> (13 : Nat))
  let t  := p2 - 8191
  let m  := t >>> (63 : Nat)
  let mm := (0 - m) &&& 8191
  mm + t

/-- The GF(8191) source denotes (under `denoteScalar`, parameters `["a","b"]`)
    to the Mersenne-fold emit form `gf8191MulFold`, reading `a = inpGet I 0`,
    `b = inpGet I 1`. -/
theorem gf8191MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I gf8191MulSrc (fun _ => none)
      = some (gf8191MulFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the GF(8191) multiply. -/
theorem gf8191Mul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf8191MulSrc).isSome := by
  native_decide

/-- **GF(8191) Mersenne multiply emitted by the verified compiler (fold form).**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] gf8191MulSrc = some c`, and for every `(a, b)`,
    `c`'s `BitVec 64` denotation (under `![a, b]`) is the closed Mersenne-fold
    emit form `gf8191MulFold`. Routed through `compileFromHax_meets_spec`. A
    #606 fan-out to the Mersenne prime field `GF(2¹³-1)`, reusing the
    SHA-256/Keccak/BLAKE2 `wrapping_mul`/`shr`/`BitAnd`/`add`/`sub` recognizers
    with no front change. The abstract `(a*b) % 8191` tie is
    `gf8191MulFold_eq_mod`. -/
theorem gf8191Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf8191MulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = gf8191MulFold a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf8191MulSrc).get
    gf8191Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf8191MulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      gf8191MulSrc (fun _ => none) = some (gf8191MulFold a b) := by
    have h := gf8191MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] gf8191MulSrc _ hc hspec

/-! ## The abstract `(a*b) % 8191` tie (the prime-field mod-reduce identity) -/

/-- The `Nat`-domain image of the GF(8191) Mersenne fold: the exact `toNat`
    semantics of each `BitVec 64` step (`W = 2⁶⁴`; `&&& 8191` is `% 8192`, the
    branch-free csub is the two's-complement `W - 8191 + p2` / sign-bit mask).
    `gf8191FoldNat_eq_mod` is the standalone `Nat` payload; the `BitVec`-plumbing
    push is `bitvec_binop_eq_of_nat_bridge`'s `hf` obligation. -/
def gf8191FoldNat (m n : Nat) : Nat :=
  let W := 18446744073709551616
  let p  := m * n % W
  let p1 := (p % 8192 + p / 8192) % W
  let p2 := (p1 % 8192 + p1 / 8192) % W
  let t  := (W - 8191 + p2) % W
  let mm := (W - t / 9223372036854775808 + 0) % W % 8192
  (mm + t) % W

/-- The pure-`Nat` GF(8191) reduce payload: the fold-as-`Nat` equals `(m*n) % 8191`
    on the residue domain `m, n < 8191`. Factored out of the `BitVec` plumbing via
    `bitvec_binop_eq_of_nat_bridge`. -/
theorem gf8191FoldNat_eq_mod (m n : Nat) (hm : m < 8191) (hn : n < 8191) :
    gf8191FoldNat m n = m * n % 8191 := by
  have hmn : m * n ≤ 8190 * 8190 := Nat.mul_le_mul (by omega) (by omega)
  simp only [gf8191FoldNat]
  set e := m * n with he
  rw [Nat.mod_eq_of_lt (show e < 18446744073709551616 by omega)]
  set r1 := e % 8192 + e / 8192 with hr1
  rw [Nat.mod_eq_of_lt (show r1 < 18446744073709551616 by omega)]
  set r2 := r1 % 8192 + r1 / 8192 with hr2
  rw [Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
  rcases Nat.lt_or_ge r2 8191 with hr2c | hr2c
  · rw [Nat.mod_eq_of_lt (show 18446744073709551616 - 8191 + r2 < 18446744073709551616 by omega)]
    rw [show (18446744073709551616 - 8191 + r2) / 9223372036854775808 = 1 by omega]
    rw [show (18446744073709551616 - 1 + 0) % 18446744073709551616 % 8192 = 8191 by norm_num]
    rw [show 8191 + (18446744073709551616 - 8191 + r2) = 18446744073709551616 + r2 by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
    omega
  · rw [show (18446744073709551616 - 8191 + r2) % 18446744073709551616 = r2 - 8191 by omega]
    rw [show (r2 - 8191) / 9223372036854775808 = 0 by omega]
    omega

/-- **GF(8191) Mersenne fold = `(a*b) mod 8191`** on the residue domain
    `a, b < 8191`. Ties the emitted closed fold form `gf8191MulFold` (the
    `_compiles` deliverable) to abstract modular multiply. The `Nat` reduce is
    factored into `gf8191FoldNat_eq_mod`; `bitvec_binop_eq_of_nat_bridge` does the
    plumbing. -/
theorem gf8191MulFold_eq_mod (a b : BitVec 64)
    (ha : a < 8191#64) (hb : b < 8191#64) :
    gf8191MulFold a b = (a * b) % 8191#64 := by
  have hA : a.toNat < 8191 := by have := BitVec.lt_def.mp ha; simpa using this
  have hB : b.toNat < 8191 := by have := BitVec.lt_def.mp hb; simpa using this
  apply bitvec_binop_eq_of_nat_bridge a b gf8191MulFold (fun a b => (a * b) % 8191#64)
    gf8191FoldNat (fun m n => m * n % 8191) 8191 hA hB
  · intro u v _ _
    have hm : ∀ x : Nat, x &&& 8191 = x % 8192 := fun x => Nat.and_two_pow_sub_one_eq_mod x 13
    simp only [gf8191MulFold, gf8191FoldNat, BitVec.toNat_add, BitVec.toNat_and,
      BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.reduceToNat,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, hm]
  · intro u v hu hv
    have huv : u.toNat * v.toNat < 18446744073709551616 := by
      have : u.toNat * v.toNat ≤ 8190 * 8190 := Nat.mul_le_mul (by omega) (by omega); omega
    simp only [BitVec.toNat_umod, BitVec.toNat_mul, BitVec.reduceToNat]
    rw [Nat.mod_eq_of_lt huv]
  · exact gf8191FoldNat_eq_mod

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf8191
