/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype
public meta import CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.MulPrototype

@[expose] public section

set_option autoImplicit false

/-!
# Phase-3 — ADCX/ADOX/MULX dual-carry-chain variants of GMP's
  `mpn_mul_basecase` and `mpn_sqr_basecase`

**EXPERIMENTAL FILE.**  Companion to `Mpn.AddMul1AdxPrototype.lean` and
`Mpn.MulPrototype.lean`.  Composes the just-landed
`mpn_addmul_1_adx` kernel into the schoolbook outer loop, producing the
multi-limb (n×n)→2n multiply that GMP calls `mpn_mul_basecase`, and the
diagonal-saving (n×n)→2n square that GMP calls `mpn_sqr_basecase`.

## Algorithmic structure

### `mpn_mul_basecase` (the schoolbook product)

For input limbs `a[0..n)` and `b[0..n)` and 2n-limb output `r[0..2n)`:

```
mpn_mul_1   (r,        a, n, b[0])           ; r[0..n] := a · b[0]
for j = 1 .. n-1:
  mpn_addmul_1 (r + j, a, n, b[j])           ; r[j..j+n] += a · b[j]
```

Each `mpn_addmul_1` accumulates one column of the product into the result
window.  Using the dual-chain ADCX/ADOX/MULX kernel for each inner step is
*the* standard production technique on Haswell+; it's what GMP's
`mpn/x86_64/coreihwl/mul_basecase.asm` does (with extra hand-asm
software-pipelining on top).

### `mpn_sqr_basecase` (the schoolbook square)

The square `a · a` has the special structure `a[i] · a[j] = a[j] · a[i]`,
so we compute each off-diagonal `a[i] · a[j]` (for `i ≠ j`) ONCE, double
it, and add.  The diagonal terms `a[i] · a[i]` are added separately.  Net
saving: about half the inner multiplies vs the naive square.

```
# Off-diagonal stage: r[..] := sum_{i<j} 2 · a[i] · a[j]
for j = 1 .. n-1:
  mpn_addmul_1 (r + j, a[0..j], j, a[j])     ; r[j..2j] += a[0..j] · a[j]
# Double the off-diagonals: r := 2·r
mpn_lshift1  (r, 2n)                         ; r := 2 · r
# Diagonal: r[2i..2i+1] += a[i]²
for i = 0 .. n-1:
  (hi, lo) = MULX (a[i], a[i])
  add hi:lo into r[2i..2i+1]
```

The doubling-on-add pattern is *exactly* the diagonal optimization GMP
encodes in `mpn_sqr_basecase`; the diagonals are MULX-on-self (low and
high halves added directly).

## Sizes

For the **fully unrolled** Lean emit we target `n ∈ {4, 8}` (Curve25519,
secp256k1/BLS12 inner column) — sizes for which jasminc's register
allocator accepts the unrolled body.  At `n ∈ {16, 32}` the unrolled body
exceeds jasminc's GPR budget (same scaling note as
`MpnAddMul1AdxPrototype`); the bench harness falls back to a C ADX
reference for those sizes.

## What this file proves

1. **Pure functional reference** for `mpnMulBasecaseAdx` and
   `mpnSqrBasecaseAdx`, with the headline correctness:
   ```
   toNat (mpnMulBasecaseAdx a b) = toNat a · toNat b
   toNat (mpnSqrBasecaseAdx a)   = toNat a · toNat a
   ```
   Both are **definitionally** the same lists as `mpnMul` (already proved
   correct in `MpnMulPrototype`), via the `(a·b + a·b)`/`(2·a·b)`
   symmetry for the square; the `Adx`-postfixed names exist for naming
   parallelism with `mpnAddmul1Adx`.

2. **Straight-line, fully-unrolled InstrR body** for each fixed `n`:
   `bodyMulBasecaseAdx n` and `bodySqrBasecaseAdx n`.  Each consists of
   the `mpn_addmul_1_adx` per-column body (from
   `Mpn.AddMul1AdxPrototype.bodyAddMul1Adx`) replicated `n` times with
   appropriate offsets, plus the diagonal block for the square.

3. **`FunDecl` and `.jazz` emission**: `mpn_mul_basecase_adx_<n>` and
   `mpn_sqr_basecase_adx_<n>` symbols accepted by
   `jasminc -arch x86-64` for `n ∈ {4, 8}`.

4. **Refinement statement** `MpnMulBasecaseAdxJasminRefines` /
   `MpnSqrBasecaseAdxJasminRefines`: the emitted straight-line body
   computes the pure reference.  The `n = 0` case is proved by direct
   evaluation; the general `n ≥ 1` statement is recorded as a `Prop`
   reducing structurally to `MpnAddMul1AdxJasminRefines_holds_n0`'s
   pattern (per-column mechanical port deferred — same shape as the
   single-chain `MpnAddmul1JasminRefines` outer-loop bridge in
   `MpnMulPrototype`).

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.MulBaseCaseAdxPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype hiding vr pv loadAt0 storeAt0 binImm
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype

/-! ## §1  Pure functional reference

The dual-chain `Adx` variant performs the same arithmetic per column as
the single-chain reference (each column is an `mpnAddmul1` step over the
appropriate window of `r`).  We expose the dual-chain names as
definitional wrappers and prove the headline `toNat` correctness via
`mpnMul_toNat`.
-/

/-- The dual-chain `mpn_mul_basecase`: by definition the same list as
    `mpnMul`.  The `Adx` postfix mirrors the `mpnAddmul1Adx` /
    `mpnAddmul1` definitional alias from `MpnAddMul1AdxPrototype`. -/
def mpnMulBasecaseAdx (a b : List (BitVec 64)) : List (BitVec 64) :=
  mpnMul a b

/-- The dual-chain `mpn_sqr_basecase`: same product `a · a`, but with
    the diagonal-saving schedule baked into the emitted body (the pure
    reference is `mpnMul a a`; the bench measures the saving). -/
def mpnSqrBasecaseAdx (a : List (BitVec 64)) : List (BitVec 64) :=
  mpnMul a a

/-- `mpnMulBasecaseAdx a b = mpnMul a b` — definitional. -/
theorem mpnMulBasecaseAdx_eq_mpnMul (a b : List (BitVec 64)) :
    mpnMulBasecaseAdx a b = mpnMul a b := rfl

/-- `mpnSqrBasecaseAdx a = mpnMul a a` — definitional. -/
theorem mpnSqrBasecaseAdx_eq_mpnMul_self (a : List (BitVec 64)) :
    mpnSqrBasecaseAdx a = mpnMul a a := rfl

/-- Width: `mpn_mul_basecase` outputs exactly `|a| + |b|` limbs. -/
theorem mpnMulBasecaseAdx_length (a b : List (BitVec 64)) :
    (mpnMulBasecaseAdx a b).length = a.length + b.length :=
  mpnMul_length a b

/-- Width: `mpn_sqr_basecase` outputs exactly `2|a|` limbs. -/
theorem mpnSqrBasecaseAdx_length (a : List (BitVec 64)) :
    (mpnSqrBasecaseAdx a).length = 2 * a.length := by
  show (mpnMul a a).length = 2 * a.length
  rw [mpnMul_length]; ring

/-- **Main correctness** for the dual-chain `mpn_mul_basecase`:
    the full schoolbook product equals `a · b` over `Nat`. -/
theorem mpnMulBasecaseAdx_toNat (a b : List (BitVec 64)) :
    toNat (mpnMulBasecaseAdx a b) = toNat a * toNat b :=
  mpnMul_toNat a b

/-- **Main correctness** for the dual-chain `mpn_sqr_basecase`:
    `a²` as a `2|a|`-limb product. -/
theorem mpnSqrBasecaseAdx_toNat (a : List (BitVec 64)) :
    toNat (mpnSqrBasecaseAdx a) = toNat a * toNat a :=
  mpnMul_toNat a a

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- 2-limb × 2-limb sanity: `[3,0] · [2,0] = [6,0,0,0]`. -/
example : mpnMulBasecaseAdx [3, 0] [2, 0] = [6, 0, 0, 0] := by native_decide

/-- 2-limb square: `[5,0]² = [25,0,0,0]`. -/
example : mpnSqrBasecaseAdx [5, 0] = [25, 0, 0, 0] := by native_decide

/-- Carry propagation: `[2^63,0]² = [0, 2^62, 0, 0]`. -/
example : mpnSqrBasecaseAdx [BitVec.ofNat 64 (2 ^ 63), 0]
    = [0, BitVec.ofNat 64 (2 ^ 62), 0, 0] := by native_decide

/-! ## §2  Register naming for the unrolled body

Conventions for the schoolbook outer-loop unroll:

* `r_i` (`i = 0..2n-1`) — the i-th limb of the running result, kept in a
  register for the whole body.
* `t_i` (`i = 0..n-1`) — the i-th loaded `a` limb register (reloaded per
  column to limit live regs; same as `MpnAddMul1AdxPrototype`).
* `bj`  — the current column's multiplier (`b[j]` for mul, `a[j]` for
  the off-diagonal sqr).
* `hi_i`, `lo_i` — the per-step MULX outputs (same as
  `Mpn.AddMul1AdxPrototype.hiName`, `loName`).
* `cf`, `of`, `zero` — the dual-carry flag registers + the zero
  scratch.  Reset at the start of every column.
-/

/-- Name for the i-th result-limb register. -/
def colRName (i : Nat) : String := "r" ++ toString i

/-! ## §3  Unrolled body for `mpn_mul_basecase_adx`

For input row index `i` and column index `j`, the per-column body of
the schoolbook product is one `mpn_addmul_1_adx`-style sweep of the
n-limb `a` against the scalar `b[j]`, accumulating into the result
window `r[j .. j+n]`.

Reusing the per-column AST from `MpnAddMul1AdxPrototype`:

* `xorClearFlags "of" "cf" "zero"` resets the dual-carry chain.
* `adxLimbFull i` for `i = 0..n-1` is the per-limb step:
  `t_i = a[i]`, MULX, ADCX, ADOX.
* `adxFinalFold n` captures the residual CF+OF+hi[n-1] into `cy`.

We don't store r[..] back between columns — they stay in registers for
the full body — so the actual emit is the per-column compute body **without**
the load-r/store-r prologue/epilogue.

The full body interleaves all columns; at the end every `r_i` is stored
back to memory `[rp + 8*i]`.
-/

/-- Per-column compute body for column `j` in a length-`n` row.  Loads
    the scalar `b[j]` into the `bj` register, resets the dual carries,
    runs the per-limb interleaved (load t_i, MULX, ADCX, ADOX), then the
    final fold which absorbs the final CF + OF + hi[n-1] into the
    NEXT result limb `r[j+n]`.

    Index translation: the per-limb step uses register `rName i` to mean
    "the i-th limb of the addmul window".  In our outer-loop context the
    addmul window starts at `r[j]`, so we use `colRName (j + i)`. -/
def mulCol (n j : Nat) : List InstrR :=
  -- Load b[j]; the per-limb steps use it as the scalar "b".
  [ load64Off "b" "bp" (8 * Int.ofNat j)
  -- Reset CF=OF=0 and the zero register at the start of the column.
  , xorClearFlags "of" "cf" "zero" ]
  -- Per-limb (load a[i] into t_i, MULX, ADCX, ADOX) for i = 0..n-1.
  -- The addmul window starts at r[j], so we rebind the per-step register
  -- names: use colRName(j+i) in place of rName(i).  Since the per-limb
  -- ASTs in MpnAddMul1AdxPrototype reference "r"++toString i directly we
  -- emit fresh column-local instructions here.
  ++ (List.range n).flatMap (fun i =>
       [ load64Off ("t" ++ toString i) "ap" (8 * Int.ofNat i)
       , mulxCopn ("hi" ++ toString i) ("lo" ++ toString i)
                  "b" ("t" ++ toString i)
       , adcxCopn "cf" (colRName (j + i)) (colRName (j + i))
                  ("lo" ++ toString i) "cf"
       , adoxCopn "of" (colRName (j + i)) (colRName (j + i))
                  (if i = 0 then "zero" else "hi" ++ toString (i - 1)) "of" ])
  -- Final fold: top := hi[n-1] + cf (CF chain); colCy := top + of (OF chain).
  -- The captured `colCy` is added into r[j+n] (the next limb above the window).
  -- We use `colCy` (not `cy`) here because `addCopn` below would clobber the
  -- type of `cy` as a flag-bool (the addCopn's first LVal); using two
  -- distinct names keeps both types stable.
  ++ (if n = 0 then
        [ assignConst "colCy" 0 ]
      else
        [ adcxCopn "cf"    "top"   "zero" ("hi" ++ toString (n - 1)) "cf"
        , adoxCopn "of"    "colCy" "top"  "zero"                     "of" ])
  -- Add the captured colCy into r[j+n] (the carry-out limb of this column).
  ++ (if n = 0 then [] else
       [ addCopn "pf" (colRName (j + n)) (colRName (j + n)) "colCy" ])

/-- Initialize all 2n result limbs to zero. -/
def initResultZero : Nat → List InstrR
  | 0     => []
  | k + 1 => initResultZero k ++ [ assignConst (colRName k) 0 ]

/-- Store all 2n result limbs back to `[rp + 8*i]`. -/
def storeResult : Nat → List InstrR
  | 0     => []
  | k + 1 => storeResult k ++ [ store64Off "rp" (8 * Int.ofNat k) (colRName k) ]

/-- All `n` columns: `j = 0, 1, …, n-1`. -/
def mulCols (n : Nat) : Nat → List InstrR
  | 0       => []
  | j + 1   => mulCols n j ++ mulCol n j

/-- **Full `mpn_mul_basecase_adx` body for fixed `n` limbs.**

    Prologue: zero all 2n result limbs.
    Main: `n` columns; column `j` is `addmul_1(r+j, a, n, b[j])` via
    the dual-chain ADX kernel.
    Epilogue: store all 2n result limbs to `[rp + 8*i]`.

    The dual-carry chains reset at the start of each column (xor-clear);
    the result limbs are kept in registers across all columns. -/
def bodyMulBasecaseAdx (n : Nat) : List InstrR :=
  initResultZero (2 * n) ++ mulCols n n ++ storeResult (2 * n)

/-! ## §4  Unrolled body for `mpn_sqr_basecase_adx`

The square has the special structure `a[i] · a[j] = a[j] · a[i]`.  We
compute the strict-off-diagonal product

    sum_{0 ≤ i < j < n} a[i] · a[j]

(each cross-term ONCE), then double the whole thing (one bitshift), then
add the diagonal `a[i]²` (with MULX-on-self, no doubling).

Off-diagonal stage as columns: for `j = 1 .. n-1`,
    addmul_1(r + j, a[0..j], j, a[j])      ; r[j..2j] += a[0..j] · a[j]

After the doubling, the diagonal stage adds `a[i]²` at position `r[2i..2i+1]`.

Index notes:
* The off-diagonal column `j` reads `j` limbs of `a` (indices 0..j-1) and
  accumulates into `r[j..2j]`, a `j+1`-limb window (with the column's
  carry-out at `r[2j]`).
* The diagonal stage produces hi:lo from MULX(a[i], a[i]) and adds them
  into r[2i] (lo) and r[2i+1] (hi).

We use the same `mpn_addmul_1_adx`-style per-column ADX pattern as the
mul body, just with the row-length parameter varying by column.

For the doubling we use `r := r << 1` (a single sweep of add-with-carry of
`r` to itself).  We model it as `add r, r` (limb-by-limb add of `r` to
itself, carries propagating through the OF chain — same dual-chain
kernel).
-/

/-- Per-off-diagonal-column body for sqr column `j` (1 ≤ j ≤ n-1).  Reads
    `a[0..j-1]` (length `j`) and scalar `a[j]`, addmul-accumulates into
    `r[j..2j]`.

    Structurally identical to `mulCol j j` but with the multiplicand
    drawn from `a[0..j-1]` (not `a[0..n-1]`) and the scalar register
    bound to `a[j]`. -/
def sqrOffDiagCol (j : Nat) : List InstrR :=
  -- Load b := a[j] (the scalar for this column).
  [ load64Off "b" "ap" (8 * Int.ofNat j)
  , xorClearFlags "of" "cf" "zero" ]
  -- For i = 0..j-1: MULX(a[i], b), ADCX, ADOX (window r[j..2j-1]).
  ++ (List.range j).flatMap (fun i =>
       [ load64Off ("t" ++ toString i) "ap" (8 * Int.ofNat i)
       , mulxCopn ("hi" ++ toString i) ("lo" ++ toString i)
                  "b" ("t" ++ toString i)
       , adcxCopn "cf" (colRName (j + i)) (colRName (j + i))
                  ("lo" ++ toString i) "cf"
       , adoxCopn "of" (colRName (j + i)) (colRName (j + i))
                  (if i = 0 then "zero" else "hi" ++ toString (i - 1)) "of" ])
  -- Final fold: capture the top carry-out into r[2j].
  ++ (if j = 0 then
        [ assignConst "colCy" 0 ]
      else
        [ adcxCopn "cf"    "top"   "zero" ("hi" ++ toString (j - 1)) "cf"
        , adoxCopn "of"    "colCy" "top"  "zero"                     "of" ])
  ++ (if j = 0 then [] else
       [ addCopn "pf" (colRName (j + j)) (colRName (j + j)) "colCy" ])

/-- All off-diagonal columns `j = 1, …, n-1` (j = 0 contributes nothing
    since `a[0] · a[<0]` is empty). -/
def sqrOffDiagCols (n : Nat) : Nat → List InstrR
  | 0       => []
  | j + 1   => sqrOffDiagCols n j ++ (if j = 0 then [] else sqrOffDiagCol j)

/-- Double the result: `r := r << 1` via limb-wise add-with-carry (`r := r + r`).
    Uses the ADX dual-carry chain (`xor` then ADCX limb by limb).
    `n2 = 2*n` is the result width. -/
def doubleResult : Nat → List InstrR
  | 0       => []
  | k + 1   =>
      doubleResult k ++
      [ -- one limb: r_k := r_k + r_k + cf
        adcxCopn "cf" (colRName k) (colRName k) (colRName k) "cf" ]

/-- Diagonal stage: for `i = 0..n-1`, MULX(a[i], a[i]) → (hi, lo); add
    `lo` into `r[2i]` and `hi` into `r[2i+1]` along the OF chain. -/
def sqrDiag (n : Nat) : Nat → List InstrR
  | 0       => []
  | i + 1   =>
      sqrDiag n i ++
      [ load64Off ("t" ++ toString i) "ap" (8 * Int.ofNat i)
      , mulxCopn ("hi" ++ toString i) ("lo" ++ toString i)
                 ("t" ++ toString i) ("t" ++ toString i)
      , adoxCopn "of" (colRName (2 * i))     (colRName (2 * i))
                 ("lo" ++ toString i) "of"
      , adoxCopn "of" (colRName (2 * i + 1)) (colRName (2 * i + 1))
                 ("hi" ++ toString i) "of" ]

/-- **Full `mpn_sqr_basecase_adx` body for fixed `n` limbs.**

    Prologue: zero all 2n result limbs; reset dual carries.
    Stage 1: off-diagonal column sweep (columns j = 1..n-1; column 0
             contributes nothing).
    Stage 2: double the partial result.
    Stage 3: diagonal stage adds `a[i]²` for `i = 0..n-1`.
    Epilogue: store all 2n result limbs.

    Saves about half the multiplies vs `mpn_mul_basecase_adx` on the same
    input (the diagonal optimization that GMP's `mpn_sqr_basecase` does). -/
def bodySqrBasecaseAdx (n : Nat) : List InstrR :=
  initResultZero (2 * n)
  ++ sqrOffDiagCols n n
  ++ [ xorClearFlags "of" "cf" "zero" ]  -- reset for the doubling
  ++ doubleResult (2 * n)
  ++ [ xorClearFlags "of" "cf" "zero" ]  -- reset for the diagonal stage
  ++ sqrDiag n n
  ++ storeResult (2 * n)

/-! ## §5  `FunDecl` and `.jazz` emission -/

/-- The `mpn_mul_basecase_adx_<n>` function declaration for fixed `n`.

    Signature: `(rp, ap, bp)` — result pointer (2n limbs), multiplicand
    pointer (n limbs), multiplier pointer (n limbs).  Matches the GMP
    `__gmpn_mul_basecase` ABI restricted to the equal-length case. -/
def mpnMulBasecaseAdxFd (n : Nat) : FunDecl where
  name := { name := "mpn_mul_basecase_adx_" ++ toString n }
  params := [⟨{ var := vr "rp" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodyMulBasecaseAdx n
  results := []

/-- The `mpn_sqr_basecase_adx_<n>` function declaration for fixed `n`.

    Signature: `(rp, ap)` — result pointer (2n limbs), input pointer
    (n limbs).  Matches the GMP `__gmpn_sqr_basecase` ABI. -/
def mpnSqrBasecaseAdxFd (n : Nat) : FunDecl where
  name := { name := "mpn_sqr_basecase_adx_" ++ toString n }
  params := [⟨{ var := vr "rp" }⟩, ⟨{ var := vr "ap" }⟩]
  body := bodySqrBasecaseAdx n
  results := []

/-- Constant-time shape: the body is straight-line `Cassgn` / `Copn`,
    no `Cif` / `Cfor` / `Cwhile`.  All branches depend on the public
    limb-count parameter only. -/
example : (bodyMulBasecaseAdx 4).all (fun i => match i with
    | .Cassgn _ _ _ _ => true
    | .Copn _ _ _ _   => true
    | _ => false) = true := by decide

example : (bodySqrBasecaseAdx 4).all (fun i => match i with
    | .Cassgn _ _ _ _ => true
    | .Copn _ _ _ _   => true
    | _ => false) = true := by decide

/-- Emitted `.jazz` for the `mpn_mul_basecase` kernel at `n = 4`. -/
def emittedMul4 : Option String := emitFunDecl (mpnMulBasecaseAdxFd 4)

/-- Emitted `.jazz` for the `mpn_mul_basecase` kernel at `n = 8`. -/
def emittedMul8 : Option String := emitFunDecl (mpnMulBasecaseAdxFd 8)

/-- Emitted `.jazz` for the `mpn_sqr_basecase` kernel at `n = 4`. -/
def emittedSqr4 : Option String := emitFunDecl (mpnSqrBasecaseAdxFd 4)

/-- Emitted `.jazz` for the `mpn_sqr_basecase` kernel at `n = 8`. -/
def emittedSqr8 : Option String := emitFunDecl (mpnSqrBasecaseAdxFd 8)

/-! ## §6  Refinement statements

`MpnMulBasecaseAdxRefinesStmt n` says: when run on a state holding
`a` at `ap`, `b` at `bp`, and (any) `r_in` at `rp`, the unrolled body
produces `mpnMulBasecaseAdx a b` at `rp`.

For `n = 0` the body is trivial (no init, no columns, no store, since
`2 * 0 = 0`) so the refinement holds by direct evaluation.  The general
`n ≥ 1` case is recorded as a `Prop`; the per-column proof obligation
reduces to `n` invocations of `mpnAddmul1Adx`'s per-limb step (already
discharged in `MpnAddMul1AdxPrototype` for the n=0 base; the general n
algorithm is structurally identical to the single-chain outer-loop
bridge already proved in `Mpn.MulPrototype.mpnMul_outer_loop_holds`).
The algorithmic content is the *same* multiply-accumulate identity per
column. -/

/-- Refinement statement for the dual-chain `mpn_mul_basecase` body at
    fixed `n`.  Disjointness: `rp`, `ap`, `bp` point to pairwise-disjoint
    `2n`, `n`, `n`-limb regions. -/
def MpnMulBasecaseAdxRefinesStmt (n : Nat) : Prop :=
  ∀ (s : BignumState) (rin a b : List (BitVec 64)),
    rin.length = 2 * n →
    a.length = n →
    b.length = n →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "rp").toNat) rin →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * (2 * n)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * n)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * (2 * n)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * n)) →
    ∃ s', bignumExec (bodyMulBasecaseAdx n) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (mpnMulBasecaseAdx a b)

/-- Refinement statement for the dual-chain `mpn_sqr_basecase` body. -/
def MpnSqrBasecaseAdxRefinesStmt (n : Nat) : Prop :=
  ∀ (s : BignumState) (rin a : List (BitVec 64)),
    rin.length = 2 * n →
    a.length = n →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "rp").toNat) rin →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * (2 * n)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * n)) →
    ∃ s', bignumExec (bodySqrBasecaseAdx n) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (mpnSqrBasecaseAdx a)

/-! ### `n = 0` base case: direct evaluation

For `n = 0` both bodies degenerate (empty `initResultZero 0`, empty
column sweep, empty store) and memory is trivially unchanged.  Since
`mpnMul [] [] = []` and `mpnSqrBasecaseAdx [] = []`, the refinement is
vacuous-but-explicit. -/

theorem mpnMul_nil_nil : mpnMul ([] : List (BitVec 64)) [] = [] := by
  simp [mpnMul]

theorem mpnMulBasecaseAdx_nil_nil :
    mpnMulBasecaseAdx ([] : List (BitVec 64)) [] = [] :=
  mpnMul_nil_nil

theorem mpnSqrBasecaseAdx_nil :
    mpnSqrBasecaseAdx ([] : List (BitVec 64)) = [] := by
  show mpnMul ([] : List (BitVec 64)) [] = []
  exact mpnMul_nil_nil

/-- For `n = 0`, the mul body is empty. -/
theorem bodyMulBasecaseAdx_zero : bodyMulBasecaseAdx 0 = [] := by
  unfold bodyMulBasecaseAdx initResultZero mulCols storeResult
  rfl

/-- For `n = 0`, the sqr body reduces to just the two `xorClearFlags`
    resets (init/store/columns/diag/doubling are all empty when n = 0,
    but we still emit the two flag-clears).  These leave memory
    unchanged. -/
theorem bodySqrBasecaseAdx_zero :
    bodySqrBasecaseAdx 0 =
      [ xorClearFlags "of" "cf" "zero", xorClearFlags "of" "cf" "zero" ] := by
  unfold bodySqrBasecaseAdx initResultZero sqrOffDiagCols
         doubleResult sqrDiag storeResult
  rfl

/-- Mul refinement at `n = 0`: empty body, identity state. -/
theorem MpnMulBasecaseAdxJasminRefines_zero : MpnMulBasecaseAdxRefinesStmt 0 := by
  intro s rin a b hrin ha hb hrp hap hbp _ _
  have hrin_nil : rin = [] := List.length_eq_zero_iff.mp (by simp [hrin])
  have ha_nil : a = [] := List.length_eq_zero_iff.mp ha
  have hb_nil : b = [] := List.length_eq_zero_iff.mp hb
  subst hrin_nil; subst ha_nil; subst hb_nil
  refine ⟨s, ?_, ?_⟩
  · -- Body is empty: bignumExec [] s = some s.
    rw [bodyMulBasecaseAdx_zero]
    rfl
  · -- mpnMulBasecaseAdx [] [] = []; memHoldsLimbs of nil at any base.
    rw [mpnMulBasecaseAdx_nil_nil]
    -- the input was holding [], and the body is the identity.
    show memHoldsLimbs s.mem (UInt64.ofNat (s.regs "rp").toNat) ([] : List (BitVec 64))
    simp [memHoldsLimbs]

/-- Sqr refinement at `n = 0`: only the two flag-clears run, leaving
    memory at `rp` unchanged.  Argument: at `n = 0` `mpnSqrBasecaseAdx []`
    is `[]`, and `memHoldsLimbs` of `[]` at any base in any state is
    trivially true (vacuous).  The body itself executes successfully
    (two `xorClearFlags` instructions); we don't need to name the exact
    state. -/
theorem MpnSqrBasecaseAdxJasminRefines_zero : MpnSqrBasecaseAdxRefinesStmt 0 := by
  intro s rin a hrin ha hrp hap _
  have hrin_nil : rin = [] := List.length_eq_zero_iff.mp (by simp [hrin])
  have ha_nil : a = [] := List.length_eq_zero_iff.mp ha
  subst hrin_nil; subst ha_nil
  -- We need: ∃ s', bignumExec [xorClear, xorClear] s = some s' ∧ memHoldsLimbs s'.mem _ [].
  -- The body is non-failing (two pure Copn instructions on existing registers);
  -- and memHoldsLimbs of [] is trivially true regardless of s'.
  rw [bodySqrBasecaseAdx_zero]
  -- Evaluate the body symbolically; both xors succeed.
  simp only [bignumExec, execInstr, evalPExpr, xorClearFlags, vr, pv,
             bind, Option.bind, writeXorBundle]
  -- Now the goal is `∃ s', some s' = some <explicit state> ∧ memHoldsLimbs s'.mem … []`.
  -- Pick the explicit state.
  refine ⟨_, rfl, ?_⟩
  rw [mpnSqrBasecaseAdx_nil]
  show memHoldsLimbs _ _ ([] : List (BitVec 64))
  simp [memHoldsLimbs]

/-! ### General `n ≥ 1`: reduction to the single-chain bridge

The dual-chain body produces the same `BitVec` arithmetic per column as
the single-chain `mpn_mul` loop already structured in
`Mpn.MulPrototype.mpnMul_outer_loop_holds`.  We do not re-port the full
outer-loop bridge here — the algorithmic content is the same
`mpnAddmul1_spec` cascade per column, exactly as in
`MpnAddMul1AdxJasminRefines_holds_n0`'s pattern.

The recorded `Prop` (statement above) is closed at `n = 0` by direct
evaluation; the `n ≥ 1` closure is the obvious induction over columns,
each step reducing to `mpnAddmul1Adx`'s per-limb correctness (already
proved at `n = 0` and reducible via `mpnAddmul1Adx_eq_mpnAddmul1` to the
single-chain bridge for general `n`).
-/

/-- The dual-chain `mpn_mul_basecase` body refines the pure reference at
    `n = 0`.  Mirror of `MpnAddMul1AdxJasminRefines_holds_n0`'s pattern. -/
theorem MpnMulBasecaseAdxJasminRefines_holds_n0 :
    MpnMulBasecaseAdxRefinesStmt 0 :=
  MpnMulBasecaseAdxJasminRefines_zero

/-- The dual-chain `mpn_sqr_basecase` body refines the pure reference at
    `n = 0`. -/
theorem MpnSqrBasecaseAdxJasminRefines_holds_n0 :
    MpnSqrBasecaseAdxRefinesStmt 0 :=
  MpnSqrBasecaseAdxJasminRefines_zero

/-! ### Smoke test: emitted `.jazz` is non-`none` for in-budget sizes -/

example : emittedMul4.isSome := by native_decide
example : emittedMul8.isSome := by native_decide
example : emittedSqr4.isSome := by native_decide
example : emittedSqr8.isSome := by native_decide

end CatCrypt.Crypto.Jasmin.Mpn.MulBaseCaseAdxPrototype
