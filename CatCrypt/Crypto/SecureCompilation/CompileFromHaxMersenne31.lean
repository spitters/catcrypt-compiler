/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import CatCrypt.Crypto.SecureCompilation.BitVecNatBridge
public import CatCrypt.Crypto.SecureCompilation.BitVecNatBridge

/-!
# #606 fan-out: the verified compiler emits the Mersenne-31 field multiply

This module extends the **C4** step of the verified-compiler plan to the
**Mersenne-31** base-field multiply, the prime `p = 2³¹ − 1 = 2147483647`.
This is the base field of CircleSTARK / Plonky3-Mersenne31. `2³¹ ≡ 1 (mod p)`,
so multiply is integer `a·b` followed by a `2³¹ ≡ 1` double-fold and a single
branch-free conditional subtract — the same Mersenne reduce shape as the
GF(127) (= 2⁷−1), GF(8191) (= 2¹³−1) and GF(131071) (= 2¹⁷−1) fan-outs, here
at the 31-bit Mersenne modulus.

## Mersenne-31 multiply (Mersenne fold), `w = 64`

With `a, b ∈ [0, p)` the product `a·b ≤ (2³¹−2)² < 2⁶²` fits a `u64`, and
`2³¹ ≡ 1 (mod p)` folds the high bits:

```
   x  := a*b                                    -- x ≤ (2³¹−2)² < 2⁶²
   x  := (x & M) + (x >> 31)                    -- 1st fold: x < 2³²  (M = 2³¹−1)
   x  := (x & M) + (x >> 31)                    -- 2nd fold: x ≤ 2³¹
   t := x - p ; m := t >> 63 ; r := (0 - m) & p + t   -- branch-free csub of p
```

The conditional subtract is data-independent (a `0 − (t >> 63)` mask, not a
`Jcc`). All steps are `&`/`>>`/`+`/`-`/`*` over GPRs — the SHA-256/Keccak/
BLAKE2/GF(8191) recognizers (`wrapping_mul`/`shift_right`/`BitAnd`/
`wrapping_add`/`wrapping_sub` with literal counts) already accept them, so
**no change to the verified front is required**.

## Method (mirrors `CompileFromHaxGf8191.gf8191Mul_compiles`)

`m31MulSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `m31MulFold` is the explicit closed Mersenne-fold
**emit form** the source denotes to; the `_compiles` theorem routes the
FOLD-FORM source-spec (`m31MulSrc_denoteScalar`, a `rfl`) through the C3
per-primitive obligation `compileFromHax_meets_spec`. The emitted jasmin `Com`
is *computed by the verified compiler* and proven equal to the Mersenne-fold
form.

The abstract `(a·b) % p` tie `m31MulFold_eq_mod` is, **unlike** the narrower
GF(8191)/GF(131071) Mersenne fields, **not** discharged by `bv_decide`: at
`p = 2³¹` the product reaches `2⁶²` and the 64-bit double-fold blows the SAT
solver up (the #117 Barrett-seam timeout). Instead it is closed via
`toNat` **`Nat`-arithmetic** (`m31_toNat_mul` plus the two-fold residue
computation), the same structured-`Nat` route the BabyBear `bbMul_correct`
seam uses — no bitblast at `2³¹`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The Mersenne-31 multiply source — `w = 64`, parameters `["a","b"]` -/

/-- The Mersenne-31 multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`). Integer multiply,
    Mersenne `2³¹ ≡ 1` double-fold, then a branch-free conditional subtract of
    `p = 2³¹−1` using the `0 − (t >> 63)` mask. Returns the residue register `r`. -/
def m31MulSrc : ImpExpr :=
  .letBind "cP" (.lit (.int 2147483647))
   (.letBind "c0" (.lit (.int 0))
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   (.letBind "lo0" (.app "BitAnd" [.var "p", .var "cP"])
    (.letBind "hi0" (.app "shift_right" [.var "p", .lit (.int 31)])
     (.letBind "p1" (.app "wrapping_add" [.var "lo0", .var "hi0"])
      (.letBind "lo1" (.app "BitAnd" [.var "p1", .var "cP"])
       (.letBind "hi1" (.app "shift_right" [.var "p1", .lit (.int 31)])
        (.letBind "p2" (.app "wrapping_add" [.var "lo1", .var "hi1"])
         (.letBind "t" (.app "wrapping_sub" [.var "p2", .var "cP"])
          (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
           (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
            (.letBind "mm" (.app "BitAnd" [.var "nm", .var "cP"])
             (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
              (.var "r"))))))))))))))

/-- The explicit closed Mersenne-fold **emit form** the source denotes to, at
    `w = 64`. This is the exact step-by-step computation `m31MulSrc` performs;
    `m31MulFold_eq_mod` ties it to abstract `(a·b) % p` on `a, b < p`. -/
def m31MulFold (a b : BitVec 64) : BitVec 64 :=
  let p  := a * b
  let p1 := (p &&& 2147483647) + (p >>> (31 : Nat))
  let p2 := (p1 &&& 2147483647) + (p1 >>> (31 : Nat))
  let t  := p2 - 2147483647
  let m  := t >>> (63 : Nat)
  let mm := (0 - m) &&& 2147483647
  mm + t

/-- The Mersenne-31 source denotes (under `denoteScalar`, parameters `["a","b"]`)
    to the Mersenne-fold emit form `m31MulFold`, reading `a = inpGet I 0`,
    `b = inpGet I 1`. -/
theorem m31MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I m31MulSrc (fun _ => none)
      = some (m31MulFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the Mersenne-31 multiply. -/
theorem m31Mul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31MulSrc).isSome := by
  native_decide

/-- **Mersenne-31 multiply emitted by the verified compiler (fold form).**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] m31MulSrc = some c`, and for every `(a, b)`,
    `c`'s `BitVec 64` denotation (under `![a, b]`) is the closed Mersenne-fold
    emit form `m31MulFold`. Routed through `compileFromHax_meets_spec`. A #606
    fan-out to the Mersenne prime field `GF(2³¹−1)` (CircleSTARK / Plonky3-M31),
    reusing the SHA-256/Keccak/BLAKE2/GF(8191) recognizers with no front change.
    The abstract `(a·b) % p` tie is `m31MulFold_eq_mod`. -/
theorem m31Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31MulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = m31MulFold a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31MulSrc).get
    m31Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31MulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      m31MulSrc (fun _ => none) = some (m31MulFold a b) := by
    have h := m31MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] m31MulSrc _ hc hspec

/-! ## The abstract `(a·b) % p` tie (the #117 Barrett seam at `2³¹`)

`bv_decide` SAT-times-out on the 64-bit Mersenne double-fold at `p = 2³¹`
(the product reaches `2⁶²`).  We close the tie by **`Nat` arithmetic on
`toNat`** instead: the product never wraps, each fold and the single csub
are exact on `Nat`, and the composite lands `(a·b) % p`. -/

/-- On the residue domain `a, b < p = 2³¹−1`, the `BitVec 64` product is the
    integer product: it never wraps `2⁶⁴` (`a·b ≤ (2³¹−2)² < 2⁶²`). -/
theorem m31_toNat_mul (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h1 : a.toNat < 2147483647 := by bv_omega
  have h2 : b.toNat < 2147483647 := by bv_omega
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have hle : a.toNat * b.toNat ≤ 2147483646 * 2147483646 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

/-- The `Nat`-domain image of the Mersenne-31 fold: the exact `toNat` semantics of
    each `BitVec 64` step (`&&& (2³¹−1)` is `% 2³¹`; the branch-free csub is the
    two's-complement `2⁶⁴ − p + p2` / sign-bit mask). `m31FoldNat_eq_mod` is the
    standalone `Nat` payload; the `BitVec`-plumbing push is
    `bitvec_binop_eq_of_nat_bridge`'s `hf` obligation. -/
def m31FoldNat (m n : Nat) : Nat :=
  let p  := m * n % 2 ^ 64
  let p1 := (p % 2147483648 + p / 2 ^ 31) % 2 ^ 64
  let p2 := (p1 % 2147483648 + p1 / 2 ^ 31) % 2 ^ 64
  let t  := (2 ^ 64 - 2147483647 + p2) % 2 ^ 64
  let mm := (2 ^ 64 - t / 2 ^ 63 + 0) % 2 ^ 64 % 2147483648
  (mm + t) % 2 ^ 64

/-- The pure-`Nat` Mersenne-31 reduce payload: the fold-as-`Nat` equals `(m·n) % p`
    (`p = 2147483647 = 2³¹ − 1`) on the residue domain `m, n < p`.

    Proved via `Nat` arithmetic (no `bv_decide` bitblast — the #117 Barrett seam
    SAT-times-out at `2³¹`). The product `P = m·n < 2⁶²` never wraps; `2³¹ ≡ 1`, so
    the first fold gives `P mod 2³¹ + P / 2³¹ ≡ P` with value `< 2³²`, the second
    fold drops the value to `≤ 2³¹` while preserving the residue, and the single
    branch-free csub of `p` lands the result in `[0, p)`. Factored out of the
    `BitVec` plumbing via `bitvec_binop_eq_of_nat_bridge`. -/
theorem m31FoldNat_eq_mod (m n : Nat) (hm : m < 2147483647) (hn : n < 2147483647) :
    m31FoldNat m n = m * n % 2147483647 := by
  have hPlt : m * n < 2 ^ 62 := by
    have hle : m * n ≤ 2147483646 * 2147483646 := Nat.mul_le_mul (by omega) (by omega)
    omega
  simp only [m31FoldNat]
  set P := m * n with hP
  clear_value P
  clear hP hm hn
  have hP64 : P % 2 ^ 64 = P := Nat.mod_eq_of_lt (by omega)
  rw [hP64]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2147483648 ∧ P = q * 2147483648 + r :=
    ⟨P / 2147483648, P % 2147483648, Nat.mod_lt _ (by norm_num), by omega⟩
  have hq : q < 2147483648 := by omega
  have hf1 : (q * 2147483648 + r) % 2147483648 + (q * 2147483648 + r) / 2 ^ 31 = r + q := by
    rw [show (2 ^ 31 : Nat) = 2147483648 from rfl]
    omega
  rw [hf1]
  have hf1lt : r + q < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hf1lt]
  set f2 := (r + q) % 2147483648 + (r + q) / 2 ^ 31 with hf2
  have hf2lt : f2 < 2 ^ 64 := by
    rw [hf2, show (2 ^ 31 : Nat) = 2147483648 from rfl]; omega
  rw [Nat.mod_eq_of_lt hf2lt]
  have hf2le : f2 ≤ 2147483648 := by
    rw [hf2, show (2 ^ 31 : Nat) = 2147483648 from rfl]; omega
  clear_value f2
  have hcong : f2 % 2147483647 = (q * 2147483648 + r) % 2147483647 := by
    rw [hf2, show (2 ^ 31 : Nat) = 2147483648 from rfl]
    omega
  rw [← hcong]
  rcases Nat.lt_or_ge f2 2147483647 with hlt | hge
  · have ht : (2 ^ 64 - 2147483647 + f2) % 2 ^ 64 = 2 ^ 64 - 2147483647 + f2 := by
      apply Nat.mod_eq_of_lt; omega
    rw [ht]
    have hmm : (2 ^ 64 - 2147483647 + f2) / 2 ^ 63 = 1 := by
      rw [Nat.div_eq_of_lt_le] <;> omega
    rw [hmm]
    omega
  · have ht : (2 ^ 64 - 2147483647 + f2) % 2 ^ 64 = f2 - 2147483647 := by
      have : 2 ^ 64 - 2147483647 + f2 = 2 ^ 64 + (f2 - 2147483647) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [ht]
    have hmm : (f2 - 2147483647) / 2 ^ 63 = 0 := by
      apply Nat.div_eq_of_lt; omega
    rw [hmm]
    omega

/-- **Mersenne-31 fold = `(a·b) mod p`** on the residue domain `a, b < p`
    (`p = 2147483647 = 2³¹ − 1`). Ties the emitted closed fold form `m31MulFold`
    (the `_compiles` deliverable) to abstract modular multiply. The `Nat` reduce is
    factored into `m31FoldNat_eq_mod`; `bitvec_binop_eq_of_nat_bridge` does the
    plumbing (no `bv_decide` bitblast — the #117 Barrett seam SAT-times-out at
    `2³¹`). -/
theorem m31MulFold_eq_mod (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    m31MulFold a b = (a * b) % 2147483647#64 := by
  have hA : a.toNat < 2147483647 := by have := BitVec.lt_def.mp ha; simpa using this
  have hB : b.toNat < 2147483647 := by have := BitVec.lt_def.mp hb; simpa using this
  apply bitvec_binop_eq_of_nat_bridge a b m31MulFold (fun a b => (a * b) % 2147483647#64)
    m31FoldNat (fun m n => m * n % 2147483647) 2147483647 hA hB
  · intro u v _ _
    have hmask : ∀ k : Nat, k &&& 2147483647 = k % 2147483648 := by
      intro k; rw [show (2147483647 : Nat) = 2 ^ 31 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    have hlit : BitVec.toNat (2147483647 : BitVec 64) = 2147483647 := rfl
    have hlit0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
    simp only [m31MulFold, m31FoldNat, BitVec.toNat_add, BitVec.toNat_and,
      BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul,
      Nat.shiftRight_eq_div_pow, hlit, hlit0, hmask]
  · intro u v hu hv
    have huv : u.toNat * v.toNat < 2 ^ 64 := by
      have : u.toNat * v.toNat ≤ 2147483646 * 2147483646 := Nat.mul_le_mul (by omega) (by omega)
      omega
    simp only [BitVec.toNat_umod, BitVec.toNat_mul]
    rw [show (2147483647#64 : BitVec 64).toNat = 2147483647 from rfl]
    rw [Nat.mod_eq_of_lt huv]
  · exact m31FoldNat_eq_mod

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31
