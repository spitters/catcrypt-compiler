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
# C4 fan-out: the verified compiler emits a GF(127) Mersenne-fold multiply

This module extends the **C4** step of the verified-compiler plan to the
**prime-field** primitive shared by **QR-UOV** and **CROSS**: the `GF(127)`
base-field multiply. `127 = 2⁷ - 1` is a **Mersenne** prime, so `2⁷ ≡ 1
(mod 127)`: multiply is integer `a·b` followed by a `128 ≡ 1` double-fold and a
branch-free conditional subtract — exactly the reduce CatCrypt's owned QR-UOV
(`QRUOV/VerifyEmit.lean`) and CROSS (`CROSS/SyndromeEmit.lean`) kernels
render through the GP-ALU alphabet.

## GF(127) multiply (Mersenne fold), `w = 64`

With `a, b ∈ [0, 126]` the product `a·b ≤ 126² = 15876 < 2¹⁴` fits in the low
word, and `128 ≡ 1 (mod 127)` folds the high bits:

```
   p := a*b                                  -- p ≤ 15876
   p := (p & 127) + (p >> 7)                 -- 1st fold: p ≤ 124 + 127 = 251
   p := (p & 127) + (p >> 7)                 -- 2nd fold: p ≤ 1 + 127   = 128
   t := p - 127 ; m := t >> 63 ; p := (0 - m) & 127 + t   -- branch-free csub
```

The conditional subtract is data-independent (a `0 − (t >> 7-shift)` mask, not a
`Jcc`). All steps are `&`/`>>`/`+`/`-`/`*` over GPRs — the SHA-256/Keccak/BLAKE2
recognizers (`wrapping_mul`/`shr`/`BitAnd`/`wrapping_add`/`wrapping_sub` with
literal counts) already accept them, so **no change to the verified front is
required**; this is the same prime-field (mod-reduce) fan-out shape as the SDitH
GF(251) Solinas multiply, here for the Mersenne prime `127`.

## The `>> 63` mask works at `w = 64`

`t := p - 127` is computed in `BitVec 64` (two's complement). After two folds
`p ∈ [0, 128]`:
* if `p ≥ 127` (i.e. `p ∈ {127, 128}`), `t = p - 127 ∈ {0, 1}`, top bit `0`,
  `m = t >> 63 = 0`, mask `0 - 0 = 0`, `0 & 127 = 0`, result `0 + t = p - 127`;
* if `p < 127`, `t = p - 127 (mod 2⁶⁴)` has bit 63 set, `m = t >> 63 = 1`,
  mask `0 - 1 = all-ones`, `allOnes & 127 = 127`, result `127 + t = p`.

So the conditional subtract lands the residue in `[0, 126]`.

## Method (mirrors `CompileFromHaxSdithGf251.gf251Mul_compiles`)

`gf127MulSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `gf127MulFold` is the explicit closed Mersenne-fold
**emit form** the source denotes to; the `_compiles` theorem routes the FOLD-FORM
source-spec (`gf127MulSrc_denoteScalar`, a `rfl`) through the C3 per-primitive
obligation `compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by
the verified compiler* and proven equal to the Mersenne-fold form.

The abstract `(a*b) % 127` tie is stated and proved **separately**
(`gf127MulFold_eq_mod`) over the constrained domain `a, b < 127`, the
mod-reduce arithmetic identity (the prime-field analogue of the `#117` Barrett
seam, here phrased in pure `BitVec` so `bv_decide` bitblasts the fold).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf127

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The GF(127) Mersenne multiply source — `w = 64`, parameters `["a","b"]` -/

/-- The GF(127) multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`). Integer multiply,
    Mersenne `128 ≡ 1` double-fold, then a branch-free conditional subtract of
    `127` using the `0 − (t >> 63)` mask. Returns the residue register `r`. -/
def gf127MulSrc : ImpExpr :=
  -- pre-bind the fold constants (binary-ALU literal operands must be `let`-bound
  -- under the front's ANF discipline; only `shr` counts may stay literal)
  .letBind "c127" (.lit (.int 127))
   (.letBind "c0" (.lit (.int 0))
  -- p := a * b
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   -- 1st fold: p := (p & 127) + (p >> 7)
   (.letBind "lo0" (.app "BitAnd" [.var "p", .var "c127"])
    (.letBind "hi0" (.app "shift_right" [.var "p", .lit (.int 7)])
     (.letBind "p1" (.app "wrapping_add" [.var "lo0", .var "hi0"])
      -- 2nd fold: p1 := (p1 & 127) + (p1 >> 7)
      (.letBind "lo1" (.app "BitAnd" [.var "p1", .var "c127"])
       (.letBind "hi1" (.app "shift_right" [.var "p1", .lit (.int 7)])
        (.letBind "p2" (.app "wrapping_add" [.var "lo1", .var "hi1"])
         -- branch-free conditional subtract of 127
         (.letBind "t" (.app "wrapping_sub" [.var "p2", .var "c127"])
          (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
           (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
            (.letBind "mm" (.app "BitAnd" [.var "nm", .var "c127"])
             (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
              (.var "r"))))))))))))))

/-- The explicit closed Mersenne-fold **emit form** the source denotes to, at
    `w = 64`. Stated as a plain `def` so the emitted form is explicit and
    auditable. This is the exact step-by-step computation `gf127MulSrc` performs;
    `gf127MulFold_eq_mod` ties it to abstract `(a*b) % 127` on `a, b < 127`. -/
def gf127MulFold (a b : BitVec 64) : BitVec 64 :=
  let p  := a * b
  let p1 := (p &&& 127) + (p >>> (7 : Nat))
  let p2 := (p1 &&& 127) + (p1 >>> (7 : Nat))
  let t  := p2 - 127
  let m  := t >>> (63 : Nat)
  let mm := (0 - m) &&& 127
  mm + t

/-- The GF(127) source denotes (under `denoteScalar`, parameters `["a","b"]`) to
    the Mersenne-fold emit form `gf127MulFold`, reading `a = inpGet I 0`,
    `b = inpGet I 1`. The closed let-normalized body reduces definitionally:
    `wrapping_mul` is `*`, `shift_right n` is `>>> n`, `BitAnd` is `&&&`,
    `wrapping_add`/`wrapping_sub` are `+`/`-`. -/
theorem gf127MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I gf127MulSrc (fun _ => none)
      = some (gf127MulFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the GF(127) multiply (`w = 64`,
    two parameters). -/
theorem gf127Mul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf127MulSrc).isSome := by
  native_decide

/-- **GF(127) Mersenne multiply emitted by the verified compiler (fold form).**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] gf127MulSrc = some c`, and for every `(a, b)`, `c`'s
    `BitVec 64` denotation (under the input valuation `![a, b]`) is exactly the
    closed Mersenne-fold emit form `gf127MulFold`. Routed through the C3
    per-primitive obligation `compileFromHax_meets_spec`. This is a C4 fan-out to
    the **prime-field** core shared by **QR-UOV** and **CROSS** (GF(127) = 2⁷-1
    Mersenne reduce), reusing the SHA-256/Keccak/BLAKE2
    `wrapping_mul`/`shr`/`BitAnd`/`add`/`sub` recognizers with no front change.
    The abstract `(a*b) % 127` tie is `gf127MulFold_eq_mod`. -/
theorem gf127Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf127MulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = gf127MulFold a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf127MulSrc).get
    gf127Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf127MulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      gf127MulSrc (fun _ => none) = some (gf127MulFold a b) := by
    have h := gf127MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] gf127MulSrc _ hc hspec

/-! ## The abstract `(a*b) % 127` tie (the prime-field mod-reduce identity)

The Mersenne-fold emit form `gf127MulFold` equals abstract `(a*b) % 127` over the
constrained QR-UOV / CROSS domain `a, b < 127` (every base-field residue). This
is the prime-field reduce identity — proved by pushing everything to
`toNat` and discharging the resulting bounded `Nat` arithmetic with `omega`, so
no bit-blasting is needed. -/

/-- The `Nat`-domain image of the GF(127) Mersenne fold: the exact `toNat`
    semantics of each `BitVec 64` step (`W = 2⁶⁴`; `&&& 127` is `% 128`, the
    branch-free csub is the two's-complement `W - 127 + p2` / sign-bit mask).
    `gf127FoldNat_eq_mod` is the standalone `Nat` payload; the `BitVec`-plumbing
    push is `bitvec_binop_eq_of_nat_bridge`'s `hf` obligation. -/
def gf127FoldNat (m n : Nat) : Nat :=
  let W := 18446744073709551616
  let p  := m * n % W
  let p1 := (p % 128 + p / 128) % W
  let p2 := (p1 % 128 + p1 / 128) % W
  let t  := (W - 127 + p2) % W
  let mm := (W - t / 9223372036854775808 + 0) % W % 128
  (mm + t) % W

/-- The pure-`Nat` GF(127) reduce payload: the fold-as-`Nat` equals `(m*n) % 127`
    on the residue domain `m, n < 127` (the two `128 ≡ 1` folds and the single
    branch-free csub land the residue in `[0,126]`). Factored out of the `BitVec`
    plumbing via `bitvec_binop_eq_of_nat_bridge`. -/
theorem gf127FoldNat_eq_mod (m n : Nat) (hm : m < 127) (hn : n < 127) :
    gf127FoldNat m n = m * n % 127 := by
  have hmn : m * n ≤ 126 * 126 := Nat.mul_le_mul (by omega) (by omega)
  simp only [gf127FoldNat]
  set e := m * n with he
  rw [Nat.mod_eq_of_lt (show e < 18446744073709551616 by omega)]
  set r1 := e % 128 + e / 128 with hr1
  rw [Nat.mod_eq_of_lt (show r1 < 18446744073709551616 by omega)]
  set r2 := r1 % 128 + r1 / 128 with hr2
  rw [Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
  rcases Nat.lt_or_ge r2 127 with hr2c | hr2c
  · rw [Nat.mod_eq_of_lt (show 18446744073709551616 - 127 + r2 < 18446744073709551616 by omega)]
    rw [show (18446744073709551616 - 127 + r2) / 9223372036854775808 = 1 by omega]
    rw [show (18446744073709551616 - 1 + 0) % 18446744073709551616 % 128 = 127 by norm_num]
    rw [show 127 + (18446744073709551616 - 127 + r2) = 18446744073709551616 + r2 by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
    omega
  · rw [show (18446744073709551616 - 127 + r2) % 18446744073709551616 = r2 - 127 by omega]
    rw [show (r2 - 127) / 9223372036854775808 = 0 by omega]
    omega

/-- **GF(127) Mersenne fold = `(a*b) mod 127`** on the residue domain `a, b < 127`.
    Ties the emitted closed fold form `gf127MulFold` (the `_compiles` deliverable)
    to abstract modular multiply. The product `a·b ≤ 126² = 15876 < 2¹⁴` never
    wraps the `BitVec 64`, so the two `128 ≡ 1` folds and the single conditional
    subtract land the residue exactly in `[0,126]`. The `Nat` reduce is factored
    into `gf127FoldNat_eq_mod`; `bitvec_binop_eq_of_nat_bridge` does the plumbing. -/
theorem gf127MulFold_eq_mod (a b : BitVec 64)
    (ha : a < 127#64) (hb : b < 127#64) :
    gf127MulFold a b = (a * b) % 127#64 := by
  have hA : a.toNat < 127 := by have := BitVec.lt_def.mp ha; simpa using this
  have hB : b.toNat < 127 := by have := BitVec.lt_def.mp hb; simpa using this
  apply bitvec_binop_eq_of_nat_bridge a b gf127MulFold (fun a b => (a * b) % 127#64)
    gf127FoldNat (fun m n => m * n % 127) 127 hA hB
  · intro u v _ _
    have hm : ∀ x : Nat, x &&& 127 = x % 128 := fun x => Nat.and_two_pow_sub_one_eq_mod x 7
    simp only [gf127MulFold, gf127FoldNat, BitVec.toNat_add, BitVec.toNat_and,
      BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.reduceToNat,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, hm]
  · intro u v hu hv
    have huv : u.toNat * v.toNat < 18446744073709551616 := by
      have : u.toNat * v.toNat ≤ 126 * 126 := Nat.mul_le_mul (by omega) (by omega); omega
    simp only [BitVec.toNat_umod, BitVec.toNat_mul, BitVec.reduceToNat]
    rw [Nat.mod_eq_of_lt huv]
  · exact gf127FoldNat_eq_mod

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf127
