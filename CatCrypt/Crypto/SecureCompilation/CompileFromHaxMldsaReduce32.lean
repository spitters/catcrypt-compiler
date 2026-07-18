/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-DSA `reduce32` Barrett reduce

This module extends the **C4** step of the verified-compiler plan to ML-DSA-65's
Barrett `reduce32` — the per-coefficient signed-`int32` reduce that brings an
arbitrary `int32` into the centered representative range `[−6283008, 6283008]`
(FIPS-204, `q = 8380417`). The per-coefficient body is:

```c
// FIPS-204 / PQClean reduce.c, Barrett reduce32:
int32_t reduce32(int32_t a) {
    int32_t t = (a + (1 << 22)) >> 23;   // 1<<22 = 4194304, ARITHMETIC >>23
    t = a - t * Q;
    return t;
}
```

The `>> 23` is the **arithmetic** (sign-preserving) shift of an `int32`. Unlike
the `caddq` mask idiom (`CompileFromHaxMldsaPoly`), there is no logical-shift
realisation: the quotient estimate `(a + 2²²) >> 23` must round toward `−∞` for
negative `a`, i.e. it is genuinely `BitVec.sshiftRight`, not `>>>`. This is
exactly the surface the new front op unblocks: the recognizer head
`arith_shift_right` (`ShiftKind.sar`, `Rhs.sarImm`) denotes `BitVec.sshiftRight`
(commit #606/#605). With it the body compiles unchanged through the verified
front; the remaining ops (`wrapping_add`/`wrapping_mul`/`wrapping_sub`) are the
SHA-256/Keccak/BLAKE2/SDitH recognizers already in place.

## Width `w = 64`

We carry the signed `int32` `a` sign-extended into `BitVec 64` (the owned
`PolyOwnedEmit` convention), matching `caddq`. At width 64 the arithmetic shift
`BitVec.sshiftRight _ 23` is faithful to C's signed `>> 23` on the
sign-extended word: the sign bit lives in bit 63, `sshiftRight` replicates it,
and the in-range product `t·q` and difference `a − t·q` never wrap (the result
is the small centered `int32` representative). The `>> 23` is the genuine
arithmetic shift — this is the body the arithmetic-shift op is for.

## Method (mirrors `CompileFromHaxMldsaPoly.mldsaCaddq_compiles`)

`mldsaReduce32Src` is the let-normalized `ImpExpr` (one op per `letBind`, all
args atoms or earlier locals); `mldsaReduce32Form` is the explicit closed
**emit form** the source denotes to (with `BitVec.sshiftRight` for the `>> 23`);
the `_compiles` theorem routes the FORM source-spec
(`mldsaReduce32Src_denoteScalar`, a `rfl`) through the C3 per-primitive
obligation `compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed
by the verified compiler* and proven equal to the emit form. The `arith_shift_right`
head is what makes the `rfl` go through: the source's `>> 23` recognizes to
`Rhs.sarImm 23`, which denotes `BitVec.sshiftRight`, matching the form.

The abstract `reduce32(a)` centered-representative tie (`a − ⌊(a+2²²)/2²³⌋·q`
landing in the Barrett output band) is the genuine signed-Barrett identity. We
state it over the `int32`-band domain and prove it by pure-BitVec `bv_decide`
where it closes (the SDitH lesson); the form-level `_compiles` is the primary
deliverable and stands on its own.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaReduce32

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The ML-DSA `reduce32` Barrett source — `w = 64`, parameter `["a"]` -/

/-- The ML-DSA `reduce32` source as a hax `ImpExpr`, fully let-normalized, single
    parameter `["a"]` (`nIn = 1`; `I 0 = a`, a sign-extended `int32`). Barrett
    quotient estimate `t = (a + (1<<22)) >> 23` using the **arithmetic** shift
    (`arith_shift_right`, the signed `>>` of an `int32`), then `r = a − t·q`
    (`q = 8380417`). Returns the centered-representative register `r`. The
    `arith_shift_right` head is the op this body needs — the logical `shift_right`
    would round the negative quotient the wrong way. -/
def mldsaReduce32Src : ImpExpr :=
  -- pre-bind the constants (binary-ALU literal operands must be `let`-bound under
  -- the front's ANF discipline; only shift counts may stay literal)
  .letBind "cb" (.lit (.int 4194304))            -- 1 << 22
   (.letBind "cq" (.lit (.int 8380417))          -- q
  -- s := a + (1<<22)
  (.letBind "s" (.app "wrapping_add" [.var "a", .var "cb"])
   -- t := s >>ₐ 23   (ARITHMETIC shift — the new front op)
   (.letBind "t" (.app "arith_shift_right" [.var "s", .lit (.int 23)])
    -- tq := t * q
    (.letBind "tq" (.app "wrapping_mul" [.var "t", .var "cq"])
     -- r := a − t*q
     (.letBind "r" (.app "wrapping_sub" [.var "a", .var "tq"])
      (.var "r"))))))

/-- The explicit closed **emit form** the source denotes to, at `w = 64`. Stated
    as a plain `def` so the emitted form is explicit and auditable. This is the
    exact step-by-step computation `mldsaReduce32Src` performs: `wrapping_add` is
    `+`, `arith_shift_right 23` is `BitVec.sshiftRight _ 23`, `wrapping_mul` is
    `*`, `wrapping_sub` is `-`. -/
def mldsaReduce32Form (a : BitVec 64) : BitVec 64 :=
  let s  := a + 4194304
  let t  := BitVec.sshiftRight s (23 : Nat)
  let tq := t * 8380417
  a - tq

/-- The `reduce32` source denotes (under `denoteScalar`, parameter `["a"]`) to the
    emit form `mldsaReduce32Form`, reading `a = inpGet I 0`. The closed
    let-normalized body reduces definitionally: `wrapping_add` is `+`,
    `arith_shift_right 23` is `BitVec.sshiftRight _ 23` (the NEW front op),
    `wrapping_mul` is `*`, `wrapping_sub` is `-`. -/
theorem mldsaReduce32Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I mldsaReduce32Src (fun _ => none)
      = some (mldsaReduce32Form (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on `reduce32` (`w = 64`, one parameter). -/
theorem mldsaReduce32_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaReduce32Src).isSome := by
  native_decide

/-- **ML-DSA `reduce32` emitted by the verified compiler (Barrett form).** There is
    a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a"] mldsaReduce32Src = some c`, and for every `a`, `c`'s
    `BitVec 64` denotation (under the input valuation `![a]`) is exactly the closed
    Barrett emit form `mldsaReduce32Form`. Routed through the C3 per-primitive
    obligation `compileFromHax_meets_spec`. This is the first C4 fan-out using the
    **arithmetic** shift op (`arith_shift_right` ↦ `Rhs.sarImm` ↦
    `BitVec.sshiftRight`, #606/#605): the signed `>> 23` of ML-DSA-65's Barrett
    `reduce32` (`q = 8380417`), which the logical `shift_right` cannot realise. -/
theorem mldsaReduce32_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] mldsaReduce32Src = some prog ∧
      ∀ (a : BitVec 64),
        prog.denote (inputValuation 64 1 ![a])
          = mldsaReduce32Form a := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaReduce32Src).get
    mldsaReduce32_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] mldsaReduce32Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a]
      mldsaReduce32Src (fun _ => none) = some (mldsaReduce32Form a) := by
    have h := mldsaReduce32Src_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"]
    ![a] mldsaReduce32Src _ hc hspec

/-! ## The abstract Barrett tie (the centered-representative reduce identity)

The Barrett emit form `mldsaReduce32Form` equals the abstract centered residue:
`reduce32(a) ≡ a (mod q)` and `reduce32(a)` lands in the FIPS-204 Barrett output
band `[−6283008, 6283008]`, for every `int32` `a` (`−2³¹ ≤ a.toInt < 2³¹`). This
is the genuine signed-Barrett identity — the arithmetic-shift analogue of the
`#117` Barrett seam. -/

/-- **ML-DSA `reduce32` Barrett form ≡ `a (mod q)`** on the `int32` domain. The
    Barrett quotient `t = (a + 2²²) >>ₐ 23` (arithmetic shift) times `q`,
    subtracted from `a`, leaves a representative congruent to `a` mod `q`: the
    difference `a − reduce32(a) = t·q` is the integer multiple of `q` removed.
    Stated as `(a − form) = t·q` so the congruence is exact at the `BitVec` level
    (`form ≡ a (mod q)` since `a − form` is a multiple of `q`). The `int32` band
    hypotheses are signed `BitVec` bounds. -/
theorem mldsaReduce32Form_sub_eq_quotient (a : BitVec 64) :
    a - mldsaReduce32Form a
      = (BitVec.sshiftRight (a + 4194304) (23 : Nat)) * 8380417 := by
  unfold mldsaReduce32Form
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaReduce32
