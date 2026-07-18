/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax
import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit

/-!
# C4 fan-out: the verified compiler emits the Plonky3 BabyBear field multiply

This module extends the **C4** step of the verified-compiler plan to the
**Plonky3 BabyBear** base-field multiply `bbMul a b = (a·b) mod p`, the prime
`p = 2³¹ − 2²⁷ + 1 = 2013265921` (`0x78000001`). Unlike the pseudo-Mersenne
`GF(251)` Solinas fold (`CompileFromHaxSdithGf251`), BabyBear is reduced by the
**ten-fold shift-add** chain `bbReduce` that CatCrypt's owned Poseidon2 / NTT
kernels (`VIR/Poseidon2Emit.lean`) render through the GP-ALU alphabet — there is
**no** modular-`%` op in the dialect.

## BabyBear multiply (ten-fold shift-add reduce), `w = 64`

With `a, b ∈ [0, p)` the product `a·b < p² < 2⁶²` fits a `u64`. The reduction is:

```
   x  := a*b                                            -- x < 2⁶²
   x  := (x >> 31)*C + (x & M)   × 10                   -- fold: C = 2²⁷−1, M = 2³¹−1
   x  := csub(x) ; x := csub(x)                         -- two branch-free csubs of p
```

Each fold step `x ↦ (x >> 31)·C + (x & M)` uses `256·… ≡ …`-style folding via
`2³¹ ≡ C (mod p)`; ten of them bring any `x < 2⁶²` below `2p`, and two
branch-free conditional subtracts (`(x − p) + (p & (0 − ((x − p) >> 63)))`)
land the residue in `[0, p)`.

All steps are `*`/`>>`/`&`/`+`/`-` over GPRs — the SHA-256/Keccak/BLAKE2/GF(251)
recognizers (`wrapping_mul`/`shift_right`/`BitAnd`/`wrapping_add`/`wrapping_sub`
with literal shift counts) already accept them, so **no change to the verified
front is required**.

## Method (mirrors `CompileFromHaxSdithGf251.gf251Mul_compiles`)

`bbMulSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args atoms
or earlier locals); `bbMulReduceForm` is the explicit closed reduce **emit form**
the source denotes to — chosen to be *definitionally* `Poseidon2Emit.bbMul`
(the ten-fold + two-csub chain). The `_compiles` theorem routes the FOLD-FORM
source-spec (`bbMulSrc_denoteScalar`, a `rfl`) through the C3 per-primitive
obligation `compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by
the verified compiler* and proven equal to the reduce form.

The abstract `(a*b) % p` tie is `bbMulReduceForm_eq_mod` over the domain
`a, b < p`. This is the **#117 Barrett seam** — historically `bv_decide`-timed
out at `p = 2³¹`. We do **not** re-derive it by `bv_decide`: the seam is already
closed structurally by `Poseidon2Emit.bbMul_correct` (folds bound + residue +
two exact csubs, via structured `Nat` arithmetic), and `bbMulReduceForm` is
definitionally `bbMul`, so the tie is `bbMul_correct` verbatim.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPlonky3Bb

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit (bbP bbC bbM bbFold bbCsub bbReduce bbMul bbMul_correct)

/-! ## The BabyBear multiply source — `w = 64`, parameters `["a","b"]` -/

/-- One fold step `x ↦ (x >> 31)*C + (x & M)`, as a let-extending `ImpExpr`
    continuation builder. `out` names the result local; `inp` is the input
    local; `cC`, `cM` are the pre-bound fold constants. -/
def foldStep (out inp cC cM : String) (cont : ImpExpr) : ImpExpr :=
  .letBind (out ++ "_hi") (.app "shift_right" [.var inp, .lit (.int 31)])
   (.letBind (out ++ "_him") (.app "wrapping_mul" [.var (out ++ "_hi"), .var cC])
    (.letBind (out ++ "_lo") (.app "BitAnd" [.var inp, .var cM])
     (.letBind out (.app "wrapping_add" [.var (out ++ "_him"), .var (out ++ "_lo")])
      cont)))

/-- One branch-free conditional subtract of `p`, `r ↦ (r − p) + (p & (0 − ((r − p) >> 63)))`,
    as a let-extending continuation. `out` names the result; `inp` the input;
    `cP` is the pre-bound prime, `cZ` the pre-bound zero. -/
def csubStep (out inp cP cZ : String) (cont : ImpExpr) : ImpExpr :=
  .letBind (out ++ "_t") (.app "wrapping_sub" [.var inp, .var cP])
   (.letBind (out ++ "_m") (.app "shift_right" [.var (out ++ "_t"), .lit (.int 63)])
    (.letBind (out ++ "_nm") (.app "wrapping_sub" [.var cZ, .var (out ++ "_m")])
     (.letBind (out ++ "_mm") (.app "BitAnd" [.var cP, .var (out ++ "_nm")])
      (.letBind out (.app "wrapping_add" [.var (out ++ "_t"), .var (out ++ "_mm")])
       cont))))

/-- The BabyBear multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`). Integer multiply,
    ten `(x >> 31)*C + (x & M)` folds, then two branch-free conditional subtracts
    of `p`, using the `0 − (t >> 63)` mask. Returns the residue register. -/
def bbMulSrc : ImpExpr :=
  -- pre-bind reduce constants as locals (binary-ALU literal operands must be
  -- `let`-bound under the front's ANF discipline; only `shift_right` counts may
  -- stay literal)
  .letBind "cC" (.lit (.int 134217727))        -- C = 2²⁷ − 1
   (.letBind "cM" (.lit (.int 2147483647))      -- M = 2³¹ − 1
    (.letBind "cP" (.lit (.int 2013265921))     -- p = 2³¹ − 2²⁷ + 1
     (.letBind "cZ" (.lit (.int 0))
  -- x := a * b
  (.letBind "x0" (.app "wrapping_mul" [.var "a", .var "b"])
  -- ten folds
  (foldStep "x1" "x0" "cC" "cM"
   (foldStep "x2" "x1" "cC" "cM"
    (foldStep "x3" "x2" "cC" "cM"
     (foldStep "x4" "x3" "cC" "cM"
      (foldStep "x5" "x4" "cC" "cM"
       (foldStep "x6" "x5" "cC" "cM"
        (foldStep "x7" "x6" "cC" "cM"
         (foldStep "x8" "x7" "cC" "cM"
          (foldStep "x9" "x8" "cC" "cM"
           (foldStep "x10" "x9" "cC" "cM"
  -- two csubs
  (csubStep "c1" "x10" "cP" "cZ"
   (csubStep "r" "c1" "cP" "cZ"
    (.var "r")))))))))))))))))

/-- The explicit closed reduce **emit form** the source denotes to, at `w = 64`.
    Definitionally `Poseidon2Emit.bbMul` (ten folds + two csubs of the product),
    written here as a transparent `def` so the emitted form is auditable and the
    `_compiles` `rfl` against `denoteScalar` goes through. -/
def bbMulReduceForm (a b : BitVec 64) : BitVec 64 := bbMul a b

/-- The BabyBear source denotes (under `denoteScalar`, parameters `["a","b"]`) to
    the reduce emit form `bbMulReduceForm`, reading `a = inpGet I 0`,
    `b = inpGet I 1`. The closed let-normalized body reduces definitionally:
    `wrapping_mul` is `*`, `shift_right n` is `>>> n`, `BitAnd` is `&&&`,
    `wrapping_add`/`wrapping_sub` are `+`/`-`. -/
theorem bbMulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I bbMulSrc (fun _ => none)
      = some (bbMulReduceForm (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the BabyBear multiply (`w = 64`,
    two parameters). -/
theorem bbMul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] bbMulSrc).isSome := by
  native_decide

/-- **Plonky3 BabyBear multiply emitted by the verified compiler (ten-fold reduce
    form).** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] bbMulSrc = some c`, and for every `(a, b)`, `c`'s
    `BitVec 64` denotation (under the input valuation `![a, b]`) is exactly the
    closed reduce emit form `bbMulReduceForm` (definitionally `bbReduce (a*b)`).
    Routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.
    This is a C4 fan-out to the **Plonky3 BabyBear** prime field
    (`p = 2³¹ − 2²⁷ + 1`), reusing the SHA-256/Keccak/BLAKE2/GF(251)
    `wrapping_mul`/`shift_right`/`BitAnd`/`add`/`sub` recognizers with no front
    change. The abstract `(a*b) % p` tie is `bbMulReduceForm_eq_mod`. -/
theorem bbMul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] bbMulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = bbMulReduceForm a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] bbMulSrc).get
    bbMul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] bbMulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      bbMulSrc (fun _ => none) = some (bbMulReduceForm a b) := by
    have h := bbMulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] bbMulSrc _ hc hspec

/-! ## The abstract `(a*b) % p` tie (the #117 Barrett seam)

The reduce emit form `bbMulReduceForm` equals abstract `(a*b) % p` over the
BabyBear residue domain `a, b < p`. This is the **#117 Barrett seam** that
historically timed out under `bv_decide` at `p = 2³¹`. We do not bitblast it:
`bbMulReduceForm` is definitionally `Poseidon2Emit.bbMul`, whose mod-`p`
correctness `bbMul_correct` is already proved **structurally** (the product fits
below `2⁶²`; ten folds preserve the residue and shrink the high part below `2p`;
two exact branch-free csubs land it in `[0, p)`), so the tie reuses that lemma
verbatim. -/

/-- **BabyBear reduce form = `(a*b) mod p`** on the residue domain `a, b < p`
    (`p = 2013265921 = 2³¹ − 2²⁷ + 1`). Ties the emitted closed reduce form
    `bbMulReduceForm` (the `_compiles` deliverable) to abstract modular multiply.
    This is the #117 Barrett seam: it reuses the structurally-proved
    `Poseidon2Emit.bbMul_correct` (no `bv_decide` bitblast at `2³¹`). -/
theorem bbMulReduceForm_eq_mod (a b : BitVec 64)
    (ha : a < bbP) (hb : b < bbP) :
    bbMulReduceForm a b = (a * b) % bbP :=
  bbMul_correct a b ha hb

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPlonky3Bb
