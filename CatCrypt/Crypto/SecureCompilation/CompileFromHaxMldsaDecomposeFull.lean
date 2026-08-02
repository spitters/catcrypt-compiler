/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-DSA `decompose` low part `a0`

This module extends the **C4** step of the verified-compiler plan to ML-DSA-65's
FIPS-204 §7.4 `Decompose` (`q = 8380417`, `γ2 = (q−1)/32 = 261888`,
`α = 2·γ2 = 523776`, `(q−1)/2 = 4190208`). It is the sibling of the
`reduce32`/`montgomery_reduce` Barrett/Montgomery leaves
(`CompileFromHaxMldsaReduce32`, `CompileFromHaxMldsaMontgomery`); like them it
hinges on the new front op `arith_shift_right` (`ShiftKind.sar`, `Rhs.sarImm`,
denoting `BitVec.sshiftRight`, commit #606/#605).

`decompose` splits a standard representative `a ∈ [0, q)` into `(a1, a0)` with
`a ≡ a1·α + a0 (mod q)`, `a0` centered. The PQClean body (verbatim from
`ml-dsa-65/clean/rounding.c`, transcribed in `DecomposeEmit`):

```c
int32_t decompose(int32_t *a0, int32_t a) {
    int32_t a1;
    a1  = (a + 127) >> 7;                   // logical (a ≥ 0): ⌊a/α⌋ pre-scale
    a1  = (a1 * 1025 + (1 << 21)) >> 22;    // Barrett reciprocal-multiply ⌊a/α⌋
    a1 &= 15;                               // mask to 0..15 (16 folds to 0)
    *a0  = a - a1 * 2 * GAMMA2;             // a − a1·α
    *a0 -= (((Q - 1) / 2 - *a0) >> 31) & Q; // branchless boundary fix-up (signed >>)
    return a1;
}
```

The single output derived here is the **low part `a0`** — the branch that
needs the arithmetic shift. The boundary fix-up
`*a0 −= (((q−1)/2 − *a0) >> 31) & q` is the branchless two's-complement trick:
`mid = (q−1)/2 − a0` is a signed `int32`; its **arithmetic** `>> 31` is the
all-ones sign mask (`−1`) when `mid < 0`, else `0`; `& q` then subtracts `q`
exactly on the boundary range. The logical `>>>` cannot realise this — the mask
must be sign-replicated, not zero-filled. This is exactly the
`arith_shift_right` surface (`DecomposeEmit`'s owned `sar` instruction).

## Width `w = 64`

Following the owned `DecomposeEmit` convention, all values are carried in
`BitVec 64`. The two `⌊a/α⌋` shifts (`>> 7`, `>> 22`) act on **non-negative**
values, so they are the logical `shift_right` (`>>>`); the boundary `mid` is held
sign-extended (it fits the signed `int32` range, `mid ∈ [−3928321, 4190208]`), so
its 32-bit `>> 31` sign mask is reproduced **exactly** by the 64-bit
`BitVec.sshiftRight mid 63` (the owned `sar 63`): both yield `0` (non-negative
`mid`) or all-ones (negative `mid`). This is the same realisation `DecomposeEmit`
uses (`sar "m" (.imm 63)`).

## Method (mirrors `CompileFromHaxMldsaReduce32.mldsaReduce32_compiles`)

`mldsaDecomposeA0Src` is the let-normalized `ImpExpr` (one op per `letBind`, all
args atoms or earlier locals); `mldsaDecomposeA0Form` is the explicit closed
**emit form** the source denotes to; the `_compiles` theorem routes the FORM
source-spec (`mldsaDecomposeA0Src_denoteScalar`, a `rfl`) through the C3
per-primitive obligation `compileFromHax_meets_spec`. The emitted jasmin `Com`
is *computed by the verified compiler* and proven equal to the emit form. The
`arith_shift_right` head is what makes the `rfl` go through: the source's signed
`>> 63` recognizes to `Rhs.sarImm 63`, which denotes `BitVec.sshiftRight`,
matching the form.

The abstract `decompose` splitting tie (`a ≡ a1·α + a0 (mod q)` with `a0`
centered) inherently involves the full Barrett `⌊a/α⌋` reciprocal-multiply
(`a1*1025` is a 32×11-bit product, `a1*α` a 4×20-bit product) chained with the
boundary fix-up; like the Montgomery 64×64 tie, the bit-blasted SAT instance is
out of `bv_decide`'s reach at the default and raised timeout. It is **not**
stated as a theorem here: the form-level `mldsaDecomposeA0_compiles` is the
primary deliverable (the verified compiler emits this body, denotation-faithful
to the explicit `mldsaDecomposeA0Form`) and stands on its own. The per-coefficient
value-correctness against PQClean (including the boundary fix-up coefficient) is
KAT-pinned in `DecomposeEmit` (`decompose_a0_coeff{0,17,4}`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecomposeFull

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The ML-DSA `decompose` low-part `a0` source — `w = 64`, parameter `["a"]` -/

/-- The ML-DSA `decompose` low-part `a0` source as a hax `ImpExpr`, fully
    let-normalized, single parameter `["a"]` (`nIn = 1`; `I 0 = a`, the standard
    representative in `[0, q)`). Computes the Barrett high part `a1`
    (`(a+127)>>7`, `(a1·1025+2²¹)>>22`, `&15` — all **logical** shifts on
    non-negative values), then `a0 = a − a1·α`, then the branchless boundary
    fix-up `a0 −= ((( q−1)/2 − a0) >>ₐ 63) & q` using the **arithmetic** shift
    (`arith_shift_right`, the signed `>>`; the logical shift would zero-fill the
    mask the wrong way). Constants pre-bound as locals under the front's ANF
    discipline. Returns the (boundary-corrected, two's-complement) low part. -/
def mldsaDecomposeA0Src : ImpExpr :=
  -- pre-bind the constants (binary-ALU literal operands must be `let`-bound under
  -- the front's ANF discipline; only shift counts may stay literal)
  .letBind "c127"   (.lit (.int 127))                  -- a-prescale add
   (.letBind "crec" (.lit (.int 1025))                 -- Barrett reciprocal
   (.letBind "cr21" (.lit (.int 2097152))              -- 2^21 rounding constant
   (.letBind "c15"  (.lit (.int 15))                   -- high-bits mask
   (.letBind "calp" (.lit (.int 523776))               -- α = 2·γ2
   (.letBind "cqh"  (.lit (.int 4190208))              -- (q−1)/2
   (.letBind "cq"   (.lit (.int 8380417))              -- q
  -- a1 = (a + 127) >> 7
  (.letBind "p"   (.app "wrapping_add" [.var "a", .var "c127"])
   (.letBind "a1h" (.app "shift_right" [.var "p", .lit (.int 7)])
   -- a1 = (a1*1025 + 2^21) >> 22
   (.letBind "m1"  (.app "wrapping_mul" [.var "a1h", .var "crec"])
    (.letBind "m1r" (.app "wrapping_add" [.var "m1", .var "cr21"])
     (.letBind "a1m" (.app "shift_right" [.var "m1r", .lit (.int 22)])
      -- a1 &= 15
      (.letBind "a1" (.app "BitAnd" [.var "a1m", .var "c15"])
       -- ta = a1 * α
       (.letBind "ta" (.app "wrapping_mul" [.var "a1", .var "calp"])
        -- a0 = a − a1·α
        (.letBind "a0" (.app "wrapping_sub" [.var "a", .var "ta"])
         -- mid = (q−1)/2 − a0
         (.letBind "mid" (.app "wrapping_sub" [.var "cqh", .var "a0"])
          -- msk = mid >>ₐ 63   (ARITHMETIC shift — the signed >> sign mask)
          (.letBind "msk" (.app "arith_shift_right" [.var "mid", .lit (.int 63)])
           -- mskq = msk & q
           (.letBind "mskq" (.app "BitAnd" [.var "msk", .var "cq"])
            -- a0f = a0 − (sign-mask & q)
            (.letBind "a0f" (.app "wrapping_sub" [.var "a0", .var "mskq"])
             (.var "a0f")))))))))))))))))))

/-- The explicit closed **emit form** the `a0` source denotes to, at `w = 64`.
    Stated as a plain `def` so the emitted form is explicit and auditable. This is
    the exact step-by-step computation `mldsaDecomposeA0Src` performs:
    `wrapping_add` is `+`, `shift_right` is `>>>`, `wrapping_mul` is `*`, `BitAnd`
    is `&&&`, `wrapping_sub` is `-`, `arith_shift_right 63` is
    `BitVec.sshiftRight _ 63`. -/
def mldsaDecomposeA0Form (a : BitVec 64) : BitVec 64 :=
  let a1h  := (a + 127) >>> (7 : Nat)
  let a1m  := (a1h * 1025 + 2097152) >>> (22 : Nat)
  let a1   := a1m &&& 15
  let a0   := a - a1 * 523776
  let mid  := 4190208 - a0
  let msk  := BitVec.sshiftRight mid (63 : Nat)
  a0 - (msk &&& 8380417)

/-- The `decompose` low-part source denotes (under `denoteScalar`, parameter
    `["a"]`) to the emit form `mldsaDecomposeA0Form`, reading `a = inpGet I 0`.
    The closed let-normalized body reduces definitionally: `wrapping_add` is `+`,
    `shift_right` is `>>>`, `wrapping_mul` is `*`, `BitAnd` is `&&&`,
    `wrapping_sub` is `-`, `arith_shift_right 63` is `BitVec.sshiftRight _ 63`
    (the NEW front op). -/
theorem mldsaDecomposeA0Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I mldsaDecomposeA0Src (fun _ => none)
      = some (mldsaDecomposeA0Form (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on `decompose`'s `a0` low part
    (`w = 64`, one parameter). -/
theorem mldsaDecomposeA0_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaDecomposeA0Src).isSome := by
  native_decide

/-- **ML-DSA `decompose` low part `a0` emitted by the verified compiler.** There
    is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a"] mldsaDecomposeA0Src = some c`, and for every `a`, `c`'s
    `BitVec 64` denotation (under the input valuation `![a]`) is exactly the
    closed `decompose` low-part emit form `mldsaDecomposeA0Form`. Routed through
    the C3 per-primitive obligation `compileFromHax_meets_spec`. A C4 fan-out
    using the **arithmetic** shift op (`arith_shift_right` ↦ `Rhs.sarImm` ↦
    `BitVec.sshiftRight`, #606/#605): the branchless boundary fix-up
    `a0 −= (((q−1)/2 − a0) >>ₐ 63) & q` of ML-DSA-65's `decompose`
    (`q = 8380417`, `α = 523776`), whose signed `>>` the logical `shift_right`
    cannot realise. -/
theorem mldsaDecomposeA0_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] mldsaDecomposeA0Src = some prog ∧
      ∀ (a : BitVec 64),
        prog.denote (inputValuation 64 1 ![a])
          = mldsaDecomposeA0Form a := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaDecomposeA0Src).get
    mldsaDecomposeA0_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] mldsaDecomposeA0Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a]
      mldsaDecomposeA0Src (fun _ => none) = some (mldsaDecomposeA0Form a) := by
    have h := mldsaDecomposeA0Src_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"]
    ![a] mldsaDecomposeA0Src _ hc hspec

/-! ## The branchless boundary fix-up identity (the part the arithmetic shift owns)

The structural identity that makes the boundary fix-up a *branchless* select: the
arithmetic-shift sign mask `msk = mid >>ₐ 63` is the two's-complement all-ones /
all-zeros word, and `msk & q` is therefore exactly `q` when `mid < 0` (the
boundary range) and `0` otherwise. This is the purpose of the
`arith_shift_right` op — it is what removes the data-dependent boundary branch.

This is stated and proved at the pure-BitVec level (the mask-select fact only,
isolated from the Barrett high-part multiply chain that walls `bv_decide`). The
full `decompose` splitting tie (`a ≡ a1·α + a0 (mod q)`, `a0` centered) inherently
chains the `a1*1025` / `a1*α` products and is out of `bv_decide`'s reach (the
Montgomery wall); it is KAT-pinned against PQClean in
`DecomposeEmit.decompose_a0_coeff{0,17,4}` (including the boundary-firing
coefficient), not restated here. -/

/-- **The arithmetic-shift sign mask is the branchless select.** For any signed
    word `mid : BitVec 64`, the arithmetic `>> 63` mask `&`-ed with `q` is exactly
    `q` (when `mid`'s sign bit is set, i.e. `mid` negative as a signed int) or `0`
    (otherwise) — the value the `decompose` boundary fix-up subtracts. This is the
    bit-level reason the `sar 63 & q` idiom is branchless, isolated from the
    Barrett high-part chain. Proved by pure-BitVec `bv_decide`. -/
theorem decomposeA0_signMask_select (mid : BitVec 64) :
    (BitVec.sshiftRight mid (63 : Nat)) &&& (8380417 : BitVec 64)
      = if mid.msb then (8380417 : BitVec 64) else 0 := by
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecomposeFull
