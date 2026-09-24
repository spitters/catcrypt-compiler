/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-DSA `make_hint` hint bit

This module extends the **C4** step of the verified-compiler plan to ML-DSA-65's
FIPS-204 §7.4 `MakeHint` — the per-coefficient 1-bit hint predicate. It is the
sibling of the Barrett `reduce32` / `decompose` low-part leaves
(`CompileFromHaxMldsaReduce32`, `CompileFromHaxMldsaDecomposeFull`); like them it
hinges on the front op `arith_shift_right` (`ShiftKind.sar`, `Rhs.sarImm`,
denoting `BitVec.sshiftRight`), here used as the **signed
sign-mask** primitive that realises the comparisons branchlessly.

`make_hint` returns the FIPS-204 hint bit (PQClean `ml-dsa-65/clean/rounding.c`):

```c
unsigned int make_hint(int32_t a0, int32_t a1) {
    if (a0 > GAMMA2 || a0 < -GAMMA2 || (a0 == -GAMMA2 && a1 != 0))
        return 1;
    return 0;
}
```

i.e. `1` iff the low part `a0` overflows the `±γ2` window, with the
`a0 == −γ2 ∧ a1 ≠ 0` tie-break (`γ2 = (q−1)/32 = 261888` for ML-DSA-65).

## Branchless realisation (the signed-compare sign masks)

Each clause is a signed comparison; the **arithmetic** `>> 63` of a sign-extended
`int32` is the all-ones/all-zeros sign mask, so the whole predicate is a
straight-line sign-mask OR — no data-dependent branch (the owned
`HintEmit.makeHintBody`, transcribed). The negation `0 − x` is the front's
`wrapping_sub` from a `0` literal (there is no `neg` head in the front's subset;
`0 − x` denotes identically):

* `m1 = sar63(γ2 − a0)` — all-ones iff `a0 > γ2`.
* `m2 = sar63(a0 + γ2)` — all-ones iff `a0 < −γ2` (i.e. `a0 + γ2 < 0`).
* clause 3 `(a0 = −γ2) ∧ (a1 ≠ 0)` as a 1-bit conjunction (the final `& 1`
  keeps only the low bit, so each clause is reduced to a bit):
  * `z = a0 + γ2`; `nzZ = sar63(z | (0 − z))` is `0` iff `z = 0` else all-ones,
    so `eqBit = (nzZ + 1) & 1` is `1` iff `z = 0`, i.e. `a0 = −γ2`.
  * `nzA1bit = sar63(a1 | (0 − a1)) & 1` is `1` iff `a1 ≠ 0`.
  * `m3 = eqBit & nzA1bit`.
* `hint = ((m1 | m2) & 1) | m3`.

## Width `w = 64`, two parameters `["a0", "a1"]`

Both inputs are signed `int32` carried sign-extended in `BitVec 64` (the owned
`HintEmit` convention). The sign bit lives in bit 63, so `BitVec.sshiftRight
_ 63` is the all-ones/all-zeros sign mask — exactly the owned `sar 63`. `nIn = 2`:
`a0 = inp 0`, `a1 = inp 1`.

## Method (mirrors `CompileFromHaxMldsaReduce32.mldsaReduce32_compiles`)

`mldsaMakeHintSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `mldsaMakeHintForm` is the explicit closed **emit form**
the source denotes to; the `_compiles` theorem routes the FORM source-spec
(`mldsaMakeHintSrc_denoteScalar`, a `rfl`) through the C3 per-primitive obligation
`compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by the verified
compiler* and proven equal to the emit form.

The abstract tie (`mldsaMakeHintForm = the FIPS-204 hint predicate`) is — unlike
the Barrett/Montgomery multiply-chain walls — a pure **comparison** of the two
sign-extended `int32` operands, so it closes by pure-BitVec `bv_decide`
(`mldsaMakeHintForm_eq_pred`, over the `int32`-band domain). The per-coefficient
value-correctness against PQClean over the whole buffer is KAT-pinned in
`HintEmit` (`make_hint_*`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaHint

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The ML-DSA `make_hint` source — `w = 64`, parameters `["a0", "a1"]` -/

/-- The ML-DSA `make_hint` source as a hax `ImpExpr`, fully let-normalized, two
    parameters `["a0", "a1"]` (`nIn = 2`; `a0 = inp 0`, `a1 = inp 1`, both signed
    `int32` sign-extended). Branchless three-clause sign-mask OR using the
    **arithmetic** shift `arith_shift_right 63` (the signed sign mask) and
    `wrapping_sub` from a pre-bound `0` literal for the negations (the front has no
    `neg` head; `0 − x` denotes identically). Constants `γ2 = 261888` and `0`/`1`
    are pre-bound as locals under the front's ANF discipline. Returns the hint bit
    `0/1` in the low bit. -/
def mldsaMakeHintSrc : ImpExpr :=
  -- pre-bind the constants (binary-ALU literal operands must be `let`-bound under
  -- the front's ANF discipline; only shift counts may stay literal)
  .letBind "cg2"  (.lit (.int 261888))                 -- γ2 = (q−1)/32
   (.letBind "c0" (.lit (.int 0))                       -- zero (for the negations)
   (.letBind "c1" (.lit (.int 1))                       -- one (eqBit / mask)
  -- m1 = sar63(γ2 − a0)   ⇒ all-ones iff a0 > γ2
  (.letBind "g2ma0" (.app "wrapping_sub" [.var "cg2", .var "a0"])
   (.letBind "m1"    (.app "arith_shift_right" [.var "g2ma0", .lit (.int 63)])
   -- m2 = sar63(a0 + γ2)  ⇒ all-ones iff a0 < −γ2
   (.letBind "z"     (.app "wrapping_add" [.var "a0", .var "cg2"])
    (.letBind "m2"   (.app "arith_shift_right" [.var "z", .lit (.int 63)])
     -- eqBit = ((sar63(z | (0 − z))) + 1) & 1   ⇒ 1 iff z = 0 (a0 = −γ2)
     (.letBind "nz"  (.app "wrapping_sub" [.var "c0", .var "z"])
      (.letBind "ze" (.app "BitOr" [.var "z", .var "nz"])
       (.letBind "zs" (.app "arith_shift_right" [.var "ze", .lit (.int 63)])
        (.letBind "ze1" (.app "wrapping_add" [.var "zs", .var "c1"])
         (.letBind "eqBit" (.app "BitAnd" [.var "ze1", .var "c1"])
          -- nzA1bit = sar63(a1 | (0 − a1)) & 1   ⇒ 1 iff a1 ≠ 0
          (.letBind "na1" (.app "wrapping_sub" [.var "c0", .var "a1"])
           (.letBind "a1e" (.app "BitOr" [.var "a1", .var "na1"])
            (.letBind "a1s" (.app "arith_shift_right" [.var "a1e", .lit (.int 63)])
             (.letBind "nzA1" (.app "BitAnd" [.var "a1s", .var "c1"])
              -- m3 = eqBit & nzA1bit
              (.letBind "m3" (.app "BitAnd" [.var "eqBit", .var "nzA1"])
               -- hint = ((m1 | m2) & 1) | m3
               (.letBind "mor" (.app "BitOr" [.var "m1", .var "m2"])
                (.letBind "mor1" (.app "BitAnd" [.var "mor", .var "c1"])
                 (.letBind "h" (.app "BitOr" [.var "mor1", .var "m3"])
                  (.var "h"))))))))))))))))))))

/-- The explicit closed **emit form** the `make_hint` source denotes to, at
    `w = 64`. Stated as a plain `def` so the emitted form is explicit and
    auditable. This is the exact step-by-step computation `mldsaMakeHintSrc`
    performs: `wrapping_sub` is `-`, `wrapping_add` is `+`, `BitOr` is `|||`,
    `BitAnd` is `&&&`, `arith_shift_right 63` is `BitVec.sshiftRight _ 63`. -/
def mldsaMakeHintForm (a0 a1 : BitVec 64) : BitVec 64 :=
  let m1    := BitVec.sshiftRight (261888 - a0) (63 : Nat)
  let z     := a0 + 261888
  let m2    := BitVec.sshiftRight z (63 : Nat)
  let nz    := 0 - z
  let zs    := BitVec.sshiftRight (z ||| nz) (63 : Nat)
  let eqBit := (zs + 1) &&& 1
  let na1   := 0 - a1
  let a1s   := BitVec.sshiftRight (a1 ||| na1) (63 : Nat)
  let nzA1  := a1s &&& 1
  let m3    := eqBit &&& nzA1
  ((m1 ||| m2) &&& 1) ||| m3

/-- The `make_hint` source denotes (under `denoteScalar`, parameters
    `["a0", "a1"]`) to the emit form `mldsaMakeHintForm`, reading
    `a0 = inpGet I 0`, `a1 = inpGet I 1`. The closed let-normalized body reduces
    definitionally: `wrapping_sub` is `-`, `wrapping_add` is `+`, `BitOr` is `|||`,
    `BitAnd` is `&&&`, `arith_shift_right 63` is `BitVec.sshiftRight _ 63` (the NEW
    front op). -/
theorem mldsaMakeHintSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a0", "a1"] I mldsaMakeHintSrc (fun _ => none)
      = some (mldsaMakeHintForm (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on `make_hint` (`w = 64`, two
    parameters). -/
theorem mldsaMakeHint_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaMakeHintSrc).isSome := by
  native_decide

/-- **ML-DSA `make_hint` emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with
    `compileFromHax ["a0","a1"] mldsaMakeHintSrc = some c`, and for every signed
    `(a0, a1)`, `c`'s `BitVec 64` denotation (under the input valuation `![a0,a1]`)
    is exactly the closed `make_hint` emit form `mldsaMakeHintForm`. Routed through
    the C3 per-primitive obligation `compileFromHax_meets_spec`. A C4 fan-out using
    the **arithmetic** shift op (`arith_shift_right` ↦ `Rhs.sarImm` ↦
    `BitVec.sshiftRight`) as the signed-compare sign-mask primitive:
    the branchless FIPS-204 §7.4 hint predicate of ML-DSA-65 (`γ2 = 261888`). -/
theorem mldsaMakeHint_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaMakeHintSrc = some prog ∧
      ∀ (a0 a1 : BitVec 64),
        prog.denote (inputValuation 64 2 ![a0, a1])
          = mldsaMakeHintForm a0 a1 := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaMakeHintSrc).get
    mldsaMakeHint_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaMakeHintSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a0 a1
  have hspec : ImpExpr.denoteScalar ["a0", "a1"] ![a0, a1]
      mldsaMakeHintSrc (fun _ => none) = some (mldsaMakeHintForm a0 a1) := by
    have h := mldsaMakeHintSrc_denoteScalar (nIn := 2) ![a0, a1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a0", "a1"]
    ![a0, a1] mldsaMakeHintSrc _ hc hspec

/-! ## The abstract hint-predicate tie (the comparison the sign masks realise)

Unlike the Barrett/Montgomery multiply-chain ties (which wall `bv_decide`), the
`make_hint` form is a pure **signed comparison** of the two sign-extended `int32`
operands — no multiply chain — so the bit-blasted SAT instance is in `bv_decide`'s
reach. We prove the emit form equals the FIPS-204 hint predicate exactly, over the
`int32`-band domain (signed `BitVec 64` bounds), via pure-BitVec `bv_decide`. -/

/-- **ML-DSA `make_hint` form = the FIPS-204 hint predicate.** For signed `int32`
    operands `a0, a1` (held in the `int32` band of `BitVec 64`), the branchless
    sign-mask form yields exactly `1` iff `a0 > γ2 ∨ a0 < −γ2 ∨ (a0 = −γ2 ∧
    a1 ≠ 0)` (the FIPS-204 §7.4 hint bit), else `0`. The comparison closes by
    pure-BitVec `bv_decide` (it is a comparison, not a multiply chain). The
    `int32`-band hypotheses are signed `BitVec` bounds: `a0, a1 ∈ [−2³¹, 2³¹)`. -/
theorem mldsaMakeHintForm_eq_pred (a0 a1 : BitVec 64)
    (ha0lo : (-2147483648 : BitVec 64).sle a0) (ha0hi : a0.sle 2147483647)
    (ha1lo : (-2147483648 : BitVec 64).sle a1) (ha1hi : a1.sle 2147483647) :
    mldsaMakeHintForm a0 a1
      = (if (261888 : BitVec 64).slt a0 ∨ a0.slt (-261888)
            ∨ (a0 = (-261888 : BitVec 64) ∧ a1 ≠ 0) then 1 else 0) := by
  unfold mldsaMakeHintForm
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaHint
