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
# C4 fan-out: the verified compiler emits an SDitH GF(251) prime-field multiply

This module extends the **C4** step of the verified-compiler plan to a
**prime-field** primitive: SDitH's `GF(251)` base-field multiply. Unlike the
binary `GF(2^k)` fan-outs (BLAKE2 ARX, Keccak χ, SHA-256 leaves), GF(251) is the
**Solinas / pseudo-Mersenne** prime `251 = 2⁸ - 5`, so `256 ≡ 5 (mod 251)`:
multiply is integer `a·b` followed by a `256 ≡ 5` double-fold and a branch-free
conditional subtract — exactly the reduce CatCrypt's owned SDitH kernel
(`SDitH/VerifyEmit.lean`) renders through the GP-ALU alphabet.

## GF(251) multiply (Solinas fold), `w = 64`

With `a, b ∈ [0, 250]` the product `a·b ≤ 250² = 62500 < 2¹⁶` fits in the low
word, and `256 ≡ 5 (mod 251)` folds the high byte:

```
   p := a*b                                      -- p ≤ 62500
   p := (p >> 8)*5 + (p & 255)                   -- 1st fold: p ≤ 244*5+255 = 1475
   p := (p >> 8)*5 + (p & 255)                   -- 2nd fold: p ≤ 5*5+255   = 280
   t := p - 251 ; m := t >> 63 ; p := (0 - m) & 251 + t   -- branch-free csub
```

The conditional subtract is data-independent (a `0 − (t >> 63)` mask, not a
`Jcc`). All steps are `*`/`>>`/`&`/`+`/`-` over GPRs — the SHA-256/Keccak/BLAKE2
recognizers (`wrapping_mul`/`shr`/`BitAnd`/`wrapping_add`/`wrapping_sub` with
literal counts) already accept them, so **no change to the verified front is
required**; this is the first **prime-field** (mod-reduce) fan-out point.

## The `>> 63` mask works at `w = 64`

`t := p - 251` is computed in `BitVec 64` (two's complement). After two folds
`p ∈ [0, 280]`:
* if `p ≥ 251` (i.e. `p ∈ [251, 280]`), `t = p - 251 ∈ [0, 29]`, top bit `0`,
  `m = t >> 63 = 0`, mask `0 - 0 = 0`, `0 & 251 = 0`, result `0 + t = p - 251`;
* if `p < 251`, `t = p - 251 (mod 2⁶⁴)` has bit 63 set, `m = t >> 63 = 1`,
  mask `0 - 1 = all-ones`, `allOnes & 251 = 251`, result `251 + t = p`.

So the conditional subtract lands the residue in `[0, 250]`.

## Method (mirrors `CompileFromHaxBlake2.blake2G_compiles`)

`gf251MulSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `gf251MulFold` is the explicit closed Solinas-fold
**emit form** the source denotes to; the `_compiles` theorem routes the FOLD-FORM
source-spec (`gf251MulSrc_denoteScalar`, a `rfl`) through the C3 per-primitive
obligation `compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by
the verified compiler* and proven equal to the Solinas-fold form.

The abstract `(a*b) % 251` tie is stated and proved **separately**
(`gf251MulFold_eq_mod`) over the constrained domain `a, b < 251`, the
mod-reduce arithmetic identity (the hard part — the prime-field analogue of the
`#117` Barrett seam).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSdithGf251

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The GF(251) Solinas multiply source — `w = 64`, parameters `["a","b"]` -/

/-- The GF(251) multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`). Integer multiply,
    Solinas `256 ≡ 5` double-fold, then a branch-free conditional subtract of
    `251` using the `0 − (t >> 63)` mask. Returns the residue register `r`. -/
def gf251MulSrc : ImpExpr :=
  -- pre-bind the fold constants (binary-ALU literal operands must be `let`-bound
  -- under the front's ANF discipline; only `shr` counts may stay literal)
  .letBind "c5" (.lit (.int 5))
   (.letBind "c255" (.lit (.int 255))
    (.letBind "c251" (.lit (.int 251))
     (.letBind "c0" (.lit (.int 0))
  -- p := a * b
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   -- 1st fold: p := (p >> 8)*5 + (p & 255)
   (.letBind "hi0" (.app "shift_right" [.var "p", .lit (.int 8)])
    (.letBind "him0" (.app "wrapping_mul" [.var "hi0", .var "c5"])
     (.letBind "lo0" (.app "BitAnd" [.var "p", .var "c255"])
      (.letBind "p1" (.app "wrapping_add" [.var "him0", .var "lo0"])
       -- 2nd fold: p1 := (p1 >> 8)*5 + (p1 & 255)
       (.letBind "hi1" (.app "shift_right" [.var "p1", .lit (.int 8)])
        (.letBind "him1" (.app "wrapping_mul" [.var "hi1", .var "c5"])
         (.letBind "lo1" (.app "BitAnd" [.var "p1", .var "c255"])
          (.letBind "p2" (.app "wrapping_add" [.var "him1", .var "lo1"])
           -- branch-free conditional subtract of 251
           (.letBind "t" (.app "wrapping_sub" [.var "p2", .var "c251"])
            (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
             (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
              (.letBind "mm" (.app "BitAnd" [.var "nm", .var "c251"])
               (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
                (.var "r"))))))))))))))))))

/-- The explicit closed Solinas-fold **emit form** the source denotes to, at
    `w = 64`. Stated as a plain `def` so the emitted form is explicit and
    auditable. This is the exact step-by-step computation `gf251MulSrc` performs;
    `gf251MulFold_eq_mod` ties it to abstract `(a*b) % 251` on `a, b < 251`. -/
def gf251MulFold (a b : BitVec 64) : BitVec 64 :=
  let p  := a * b
  let p1 := (p >>> (8 : Nat)) * 5 + (p &&& 255)
  let p2 := (p1 >>> (8 : Nat)) * 5 + (p1 &&& 255)
  let t  := p2 - 251
  let m  := t >>> (63 : Nat)
  let mm := (0 - m) &&& 251
  mm + t

/-- The GF(251) source denotes (under `denoteScalar`, parameters `["a","b"]`) to
    the Solinas-fold emit form `gf251MulFold`, reading `a = inpGet I 0`,
    `b = inpGet I 1`. The closed let-normalized body reduces definitionally:
    `wrapping_mul` is `*`, `shift_right n` is `>>> n`, `BitAnd` is `&&&`,
    `wrapping_add`/`wrapping_sub` are `+`/`-`. -/
theorem gf251MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I gf251MulSrc (fun _ => none)
      = some (gf251MulFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the GF(251) multiply (`w = 64`,
    two parameters). -/
theorem gf251Mul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf251MulSrc).isSome := by
  native_decide

/-- **SDitH GF(251) multiply emitted by the verified compiler (Solinas-fold
    form).** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] gf251MulSrc = some c`, and for every `(a, b)`, `c`'s
    `BitVec 64` denotation (under the input valuation `![a, b]`) is exactly the
    closed Solinas-fold emit form `gf251MulFold`. Routed through the C3
    per-primitive obligation `compileFromHax_meets_spec`. This is a C4 fan-out to
    a **prime-field** primitive (GF(251) = 2⁸-5 Solinas reduce), reusing the
    SHA-256/Keccak/BLAKE2 `wrapping_mul`/`shr`/`BitAnd`/`add`/`sub` recognizers
    with no front change. The abstract `(a*b) % 251` tie is `gf251MulFold_eq_mod`. -/
theorem gf251Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf251MulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = gf251MulFold a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf251MulSrc).get
    gf251Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] gf251MulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      gf251MulSrc (fun _ => none) = some (gf251MulFold a b) := by
    have h := gf251MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] gf251MulSrc _ hc hspec

/-! ## The abstract `(a*b) % 251` tie (the prime-field mod-reduce identity)

The Solinas-fold emit form `gf251MulFold` equals abstract `(a*b) % 251` over the
constrained SDitH domain `a, b < 251` (every base-field residue). This is the
prime-field reduce identity: a Barrett-style modular-reduction fact over
the constrained SDitH domain. -/

/-- The `Nat`-domain image of the GF(251) Solinas fold: the exact `toNat`
    semantics of each `BitVec 64` step (`W = 2⁶⁴`; the fold `&&& 255` is `% 256`,
    the branch-free csub keeps the non-power-of-two mask `&&& 251` as a `Nat`
    bitwise-and). `gf251FoldNat_eq_mod` is the standalone `Nat` payload; the
    `BitVec`-plumbing push is `bitvec_binop_eq_of_nat_bridge`'s `hf` obligation. -/
def gf251FoldNat (m n : Nat) : Nat :=
  let W := 18446744073709551616
  let p  := m * n % W
  let p1 := (p / 256 * 5 % W + p % 256) % W
  let p2 := (p1 / 256 * 5 % W + p1 % 256) % W
  let t  := (W - 251 + p2) % W
  let mm := (W - t / 9223372036854775808 + 0) % W &&& 251
  (mm + t) % W

/-- The pure-`Nat` GF(251) Solinas reduce payload: the fold-as-`Nat` equals
    `(m*n) % 251` on the residue domain `m, n < 251`. The two `256 ≡ 5 (mod 251)`
    folds each drop a multiple of 251, so `r2 ≡ m·n (mod 251)`, and the single
    branch-free csub lands the residue in `[0,250]`. Factored out of the `BitVec`
    plumbing via `bitvec_binop_eq_of_nat_bridge`. -/
theorem gf251FoldNat_eq_mod (m n : Nat) (hm : m < 251) (hn : n < 251) :
    gf251FoldNat m n = m * n % 251 := by
  have hmn : m * n ≤ 250 * 250 := Nat.mul_le_mul (by omega) (by omega)
  simp only [gf251FoldNat]
  set e := m * n with he
  rw [Nat.mod_eq_of_lt (show e < 18446744073709551616 by omega)]
  rw [Nat.mod_eq_of_lt (show e / 256 * 5 < 18446744073709551616 by omega)]
  set r1 := e / 256 * 5 + e % 256 with hr1
  rw [Nat.mod_eq_of_lt (show r1 < 18446744073709551616 by omega)]
  rw [Nat.mod_eq_of_lt (show r1 / 256 * 5 < 18446744073709551616 by omega)]
  set r2 := r1 / 256 * 5 + r1 % 256 with hr2
  rw [Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
  have h1 : r1 + 251 * (e / 256) = e := by rw [hr1]; omega
  have h2 : r2 + 251 * (r1 / 256) = r1 := by rw [hr2]; omega
  have hr2u : r2 ≤ 280 := by rw [hr2, hr1]; omega
  rcases Nat.lt_or_ge r2 251 with hr2c | hr2c
  · have hin : (18446744073709551616 - 251 + r2) % 18446744073709551616
        = 18446744073709551616 - 251 + r2 := Nat.mod_eq_of_lt (by omega)
    rw [hin]
    have hdiv : (18446744073709551616 - 251 + r2) / 9223372036854775808 = 1 := by omega
    rw [hdiv]
    have hmask251 : (18446744073709551616 - 1) &&& 251 = 251 := by
      rw [Nat.and_comm]; simp
    have hmaskval : (18446744073709551616 - 1 + 0) % 18446744073709551616
        = 18446744073709551616 - 1 := by omega
    rw [hmaskval, hmask251]
    have hsum : 251 + (18446744073709551616 - 251 + r2) = 18446744073709551616 + r2 := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (show r2 < 18446744073709551616 by omega)]
    omega
  · have hin : (18446744073709551616 - 251 + r2) % 18446744073709551616 = r2 - 251 := by omega
    rw [hin]
    have hdiv : (r2 - 251) / 9223372036854775808 = 0 := by omega
    rw [hdiv]
    have hmaskval : (18446744073709551616 - 0 + 0) % 18446744073709551616 = 0 := by omega
    rw [hmaskval, Nat.zero_and, Nat.zero_add,
      Nat.mod_eq_of_lt (show r2 - 251 < 18446744073709551616 by omega)]
    omega

/-- **GF(251) Solinas fold = `(a*b) mod 251`** on the residue domain `a, b < 251`.
    Ties the emitted closed fold form `gf251MulFold` (the `_compiles` deliverable)
    to abstract modular multiply. The product `a·b ≤ 250² = 62500 < 2¹⁶` never
    wraps the `BitVec 64`, so the two `256 ≡ 5` folds and the single conditional
    subtract land the residue exactly in `[0,250]`. The `Nat` reduce is factored
    into `gf251FoldNat_eq_mod`; `bitvec_binop_eq_of_nat_bridge` does the plumbing. -/
theorem gf251MulFold_eq_mod (a b : BitVec 64)
    (ha : a < 251#64) (hb : b < 251#64) :
    gf251MulFold a b = (a * b) % 251#64 := by
  have hA : a.toNat < 251 := by have := BitVec.lt_def.mp ha; simpa using this
  have hB : b.toNat < 251 := by have := BitVec.lt_def.mp hb; simpa using this
  apply bitvec_binop_eq_of_nat_bridge a b gf251MulFold (fun a b => (a * b) % 251#64)
    gf251FoldNat (fun m n => m * n % 251) 251 hA hB
  · intro u v _ _
    have hm255 : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
    simp only [gf251MulFold, gf251FoldNat, BitVec.toNat_add, BitVec.toNat_and,
      BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.reduceToNat,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, hm255]
  · intro u v hu hv
    have huv : u.toNat * v.toNat < 18446744073709551616 := by
      have : u.toNat * v.toNat ≤ 250 * 250 := Nat.mul_le_mul (by omega) (by omega); omega
    simp only [BitVec.toNat_umod, BitVec.toNat_mul, BitVec.reduceToNat]
    rw [Nat.mod_eq_of_lt huv]
  · exact gf251FoldNat_eq_mod

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSdithGf251
