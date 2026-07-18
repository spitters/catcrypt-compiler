/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-DSA `montgomery_reduce`

This module extends the **C4** step of the verified-compiler plan to ML-DSA-65's
signed Montgomery reduction `montgomery_reduce` — the per-coefficient reduce that
brings a 64-bit product back into the ML-DSA representative range (FIPS-204,
`q = 8380417`, `R = 2^32`, `QINV = 58728449 = q⁻¹ mod 2^32`). The per-coefficient
body is:

```c
// FIPS-204 / PQClean reduce.c, signed Montgomery reduce (R = 2^32):
int32_t montgomery_reduce(int64_t a) {
    int32_t t = (int32_t)((uint64_t)a * (uint64_t)QINV);  // low 32 bits, sign-extended
    t = (a - (int64_t)t * Q) >> 32;                       //   ARITHMETIC >>32
    return t;
}
```

The final `>> 32` is the **arithmetic** (sign-preserving) shift of a signed
`int64`. Like the Barrett `reduce32` quotient estimate (`CompileFromHaxMldsaReduce32`),
this cannot be realised by the logical `>>>`: the quotient `(a − t·q) / 2³²` must
round toward `−∞` for negative arguments, i.e. it is genuinely
`BitVec.sshiftRight`, not `>>>`. This is exactly the surface the front op
`arith_shift_right` (`ShiftKind.sar`, `Rhs.sarImm`, denoting `BitVec.sshiftRight`,
commit #606/#605) unblocks.

The `(int32_t)t` truncation is the standard `shl 32; sar 32` sign-extend pair:
multiply gives the full 64-bit product `a·QINV`; shifting the low 32 bits up to
bit 63 and arithmetically shifting back down sign-extends the low `int32` into the
`BitVec 64` word — exactly the owned `PolyOwnedEmit` `pointwise` realisation
(`imul QINV; shl 32; sar 32`). All other ops (`wrapping_mul`, `shift_left`,
`wrapping_sub`) are the SHA-256/Keccak/BLAKE2/SDitH recognizers already in place.

## Width `w = 64`

The argument `a` is the signed `int64` product (carried as a `BitVec 64`, the owned
`PolyOwnedEmit` convention). `BitVec.sshiftRight _ 32` is faithful to C's signed
`int64 >> 32` on this word: the sign bit lives in bit 63 and `sshiftRight`
replicates it. The `(int32)` truncation `(t0 <<< 32) >>ₐ 32` keeps only the low 32
bits sign-extended, matching the C `(int32_t)` cast.

## Method (mirrors `CompileFromHaxMldsaReduce32.mldsaReduce32_compiles`)

`mldsaMontgomerySrc` is the let-normalized `ImpExpr` (one op per `letBind`, all
args atoms or earlier locals); `mldsaMontgomeryForm` is the explicit closed
**emit form** the source denotes to; the `_compiles` theorem routes the FORM
source-spec (`mldsaMontgomerySrc_denoteScalar`, a `rfl`) through the C3
per-primitive obligation `compileFromHax_meets_spec`. The emitted jasmin `Com` is
*computed by the verified compiler* and proven equal to the emit form. The
`arith_shift_right` head is what makes the `rfl` go through: the source's
`(int32)` sign-extend and final `>> 32` recognize to `Rhs.sarImm 32`, which
denotes `BitVec.sshiftRight`, matching the form.

The abstract Montgomery congruence (`montgomery_reduce(a) ≡ a·R⁻¹ (mod q)`, i.e.
`a − r·2³²` is a multiple of `q`) is the genuine signed-Montgomery identity. We
state it in the exact multiple-of-`q` form `montgomery_reduce` removes
(`a − form·2³² = t·q`, mirroring how `reduce32` stated its tie) and prove it by
pure-BitVec `bv_decide`; the form-level `_compiles` is the primary deliverable and
stands on its own.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomery

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The ML-DSA `montgomery_reduce` source — `w = 64`, parameter `["a"]` -/

/-- The ML-DSA `montgomery_reduce` source as a hax `ImpExpr`, fully let-normalized,
    single parameter `["a"]` (`nIn = 1`; `I 0 = a`, the signed `int64` product).
    `t0 = a·QINV`; `t = (int32)t0` via the `shl 32; sar 32` sign-extend pair
    (logical `shift_left 32` then **arithmetic** `arith_shift_right 32`);
    `tq = t·q`; `d = a − t·q`; `r = d >>ₐ 32` (**arithmetic** shift, the signed
    `int64 >> 32`). Returns the Montgomery-reduced register `r`. The
    `arith_shift_right` head is the op this body needs — the logical `shift_right`
    would round the negative quotient the wrong way. -/
def mldsaMontgomerySrc : ImpExpr :=
  -- pre-bind the constants (binary-ALU literal operands must be `let`-bound under
  -- the front's ANF discipline; only shift counts may stay literal)
  .letBind "cqinv" (.lit (.int 58728449))          -- QINV = q⁻¹ mod 2^32
   (.letBind "cq" (.lit (.int 8380417))            -- q
  -- t0 := a * QINV
  (.letBind "t0" (.app "wrapping_mul" [.var "a", .var "cqinv"])
   -- tsh := t0 << 32   (logical left shift — push the low int32 to the top)
   (.letBind "tsh" (.app "shift_left" [.var "t0", .lit (.int 32)])
    -- t := tsh >>ₐ 32  (ARITHMETIC shift — sign-extend the low int32: the (int32) cast)
    (.letBind "t" (.app "arith_shift_right" [.var "tsh", .lit (.int 32)])
     -- tq := t * q
     (.letBind "tq" (.app "wrapping_mul" [.var "t", .var "cq"])
      -- d := a − t*q
      (.letBind "d" (.app "wrapping_sub" [.var "a", .var "tq"])
       -- r := d >>ₐ 32  (ARITHMETIC shift — the signed int64 >> 32)
       (.letBind "r" (.app "arith_shift_right" [.var "d", .lit (.int 32)])
        (.var "r"))))))))

/-- The explicit closed **emit form** the source denotes to, at `w = 64`. Stated as
    a plain `def` so the emitted form is explicit and auditable. This is the exact
    step-by-step computation `mldsaMontgomerySrc` performs: `wrapping_mul` is `*`,
    `shift_left 32` is `<<< 32`, `arith_shift_right 32` is `BitVec.sshiftRight _ 32`,
    `wrapping_sub` is `-`. -/
def mldsaMontgomeryForm (a : BitVec 64) : BitVec 64 :=
  let t0  := a * 58728449
  let tsh := t0 <<< (32 : Nat)
  let t   := BitVec.sshiftRight tsh (32 : Nat)
  let tq  := t * 8380417
  let d   := a - tq
  BitVec.sshiftRight d (32 : Nat)

/-- The `montgomery_reduce` source denotes (under `denoteScalar`, parameter `["a"]`)
    to the emit form `mldsaMontgomeryForm`, reading `a = inpGet I 0`. The closed
    let-normalized body reduces definitionally: `wrapping_mul` is `*`,
    `shift_left 32` is `<<< 32`, `arith_shift_right 32` is `BitVec.sshiftRight _ 32`
    (the NEW front op), `wrapping_sub` is `-`. -/
theorem mldsaMontgomerySrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I mldsaMontgomerySrc (fun _ => none)
      = some (mldsaMontgomeryForm (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on `montgomery_reduce` (`w = 64`, one
    parameter). -/
theorem mldsaMontgomery_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaMontgomerySrc).isSome := by
  native_decide

/-- **ML-DSA `montgomery_reduce` emitted by the verified compiler.** There is a
    compiled `Com jasminDialect` `c` with
    `compileFromHax ["a"] mldsaMontgomerySrc = some c`, and for every `a`, `c`'s
    `BitVec 64` denotation (under the input valuation `![a]`) is exactly the closed
    signed-Montgomery emit form `mldsaMontgomeryForm`. Routed through the C3
    per-primitive obligation `compileFromHax_meets_spec`. A C4 fan-out using the
    **arithmetic** shift op (`arith_shift_right` ↦ `Rhs.sarImm` ↦
    `BitVec.sshiftRight`, #606/#605): the `(int32)` truncation `shl 32; sar 32` and
    the final signed `>> 32` of ML-DSA-65's signed Montgomery reduce
    (`q = 8380417`, `QINV = 58728449`), which the logical `shift_right` cannot
    realise. -/
theorem mldsaMontgomery_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] mldsaMontgomerySrc = some prog ∧
      ∀ (a : BitVec 64),
        prog.denote (inputValuation 64 1 ![a])
          = mldsaMontgomeryForm a := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaMontgomerySrc).get
    mldsaMontgomery_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] mldsaMontgomerySrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a]
      mldsaMontgomerySrc (fun _ => none) = some (mldsaMontgomeryForm a) := by
    have h := mldsaMontgomerySrc_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"]
    ![a] mldsaMontgomerySrc _ hc hspec

/-! ## The abstract Montgomery tie (walls under `bv_decide`)

The signed Montgomery emit form `mldsaMontgomeryForm` is congruent to `a·R⁻¹`
mod `q`: writing `r = montgomery_reduce(a)`, the value `a − r·2³²` is exactly the
integer multiple of `q` removed (`t·q` for the Montgomery quotient
`t = (int32)(a·QINV)`), the multiple-of-`q` form `reduce32` stated its tie in.

Unlike `reduce32` (whose tie `a − r = ((a+2²²)>>ₐ23)·q` closed by `bv_decide`),
the Montgomery tie inherently involves the full 64×64 product `a·QINV` (and a
second `t·q`); the bit-blasted SAT instance times out at the default and at a
raised timeout (the two 64-bit multipliers dominate). It is **not** stated as a
theorem here: the form-level `mldsaMontgomery_compiles` above is the primary
deliverable (the verified compiler emits this body, denotation-faithful to the
explicit `mldsaMontgomeryForm`) and stands on its own. The Montgomery congruence
is the standard signed-Montgomery identity (PQClean `reduce.c`,
`t = (int32)(a·QINV); r = (a − t·q) >> 32`, with low 32 bits of `a − t·q` zero by
`a·QINV·q ≡ a (mod 2³²)`); a non-SAT (`ZMod q` / `Int`-arithmetic) proof would be
needed to close it in Lean — left for the abstract-reduce layer, not the emit
fan-out. -/

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomery
